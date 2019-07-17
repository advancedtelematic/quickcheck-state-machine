{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Bookstore
  ( Bug(..)
  , prop_bookstore
  , cleanup
  , setup
  )
  where

import Control.Concurrent
         (threadDelay)
import Control.Monad.Reader
         (ReaderT, ask, runReaderT)
import Database.PostgreSQL.Simple as PS
         (ConnectInfo, Connection, Query,
         close, connect, connectDatabase, connectHost,
         connectPassword, connectPort, connectUser,
         defaultConnectInfo, execute, execute_, query)
import Database.PostgreSQL.Simple.FromRow
         (FromRow (fromRow), field )
import Database.PostgreSQL.Simple.Errors
         (ConstraintViolation (..), catchViolation)
import Data.Int
         (Int64)
import Data.List
         (dropWhileEnd, group, inits, isInfixOf, sort, tails)
import Data.Kind
         (Type)
import Data.Maybe
         (fromJust)
import GHC.Generics
         (Generic, Generic1)
import Network.Socket as Sock
         (AddrInfoFlag(AI_NUMERICSERV, AI_NUMERICHOST),
         Socket, SocketType(Stream), addrAddress, addrFamily,
         addrFlags, addrProtocol, addrSocketType, close,
         connect, defaultHints, getAddrInfo, socket)
import Prelude
import System.Process
         (callProcess, readProcess)
import Test.QuickCheck
         (Arbitrary (arbitrary), Gen, Property,
         arbitraryPrintableChar, choose, elements, frequency,
         ioProperty, listOf, oneof, shrink, suchThat,
         vectorOf, (===))
import Test.QuickCheck.Monadic
         (monadic)
import UnliftIO
         (IOException, bracket, catch, liftIO, onException,
         throwIO)

import           Test.StateMachine
import qualified Test.StateMachine.Types.Rank2 as Rank2
import           Test.StateMachine.Z
                   (codomain, domain)

-- Based on Bookstore case study from:
-- https://propertesting.com/book_case_study_stateful_properties_with_a_bookstore.html

-- System under test: Parametrized SQL statements

data Book = Book {
    isbn   :: String
  , title  :: String
  , author :: String
  , owned  :: Int
  , avail  :: Int
  } deriving (Eq, Show, Generic)

instance ToExpr Book where

instance FromRow Book where
  fromRow = Book <$> field <*> field <*> field <*> field <*> field

handleViolations
  :: (Connection -> IO a)
  -> Connection
  -> IO (Maybe a)
handleViolations fn cn = catchViolation catcher (Just <$> fn cn)
  where
    catcher _ (UniqueViolation _) = return Nothing
    catcher e _ = throwIO e

setupTable :: Connection -> IO (Maybe Int64)
setupTable = handleViolations $ \cn ->
  execute_ cn "CREATE TABLE books (\
              \ isbn varchar(20) PRIMARY KEY,\
              \ title varchar(256) NOT NULL,\
              \ author varchar(256) NOT NULL,\
              \ owned smallint DEFAULT 0,\
              \ available smallint DEFAULT 0\
              \ )"

teardown :: Connection -> IO (Maybe Int64)
teardown = handleViolations $ \cn -> execute_ cn "DROP TABLE books"

addBook
  :: String -> String -> String
  -> Connection
  -> IO (Maybe Int64)
addBook isbn_ title_ auth = handleViolations $ \cn ->
  execute cn templ (isbn_, title_, auth)
    where templ = "INSERT INTO books (isbn, title, author, owned, available)\
                  \ VALUES ( ?, ?, ?, 0, 0 )"

update :: Query -> String -> Connection -> IO Int64
update prepStmt param cn = execute cn prepStmt [param]

addCopy :: String -> Connection -> IO (Maybe Int64)
addCopy isbn_ = handleViolations $ update templ isbn_
  where templ = "UPDATE books SET\
                \ owned = owned + 1,\
                \ available = available + 1\
                \ WHERE isbn = ?"

borrowCopy :: String -> Connection -> IO (Maybe Int64)
borrowCopy isbn_ = handleViolations (update templ isbn_)
  where templ = "UPDATE books SET available = available - 1 \
                \ WHERE isbn = ? AND available > 0"

returnCopy :: Bug -> String -> Connection -> IO (Maybe Int64)
returnCopy bug isbn_ = handleViolations (update templ isbn_)
  where
    templ = if bug == Bug
      then "UPDATE books SET available = available + 1 WHERE isbn = ?;"
      else "UPDATE books SET available = available + 1\
           \ WHERE isbn = ? AND available < owned;"

select :: Query -> String -> Connection -> IO [Book]
select prepStmt param cn = query cn prepStmt [param]

findByAuthor, findByTitle
  :: Bug -> String -> Connection -> IO (Maybe [Book])
findByAuthor bug s = case bug of
  Injection -> handleViolations (select templ $ "%"++s++"%")
  _          -> handleViolations (select templ $ "%"++(sanitize s)++"%")
  where templ = "SELECT * FROM books WHERE author LIKE ?"

findByTitle bug s = case bug of
  Injection -> handleViolations (select templ $ "%"++s++"%")
  _          -> handleViolations (select templ $ "%"++(sanitize s)++"%")
  where templ = "SELECT * FROM books WHERE title LIKE ?"

findByIsbn :: String -> Connection -> IO (Maybe [Book])
findByIsbn s = handleViolations $ select "SELECT * FROM books WHERE isbn = ?" s

-- XXX
sanitize :: String -> String
sanitize = concatMap (\c -> if c `elem` ['_', '%', '\\'] then '\\':[c] else [c])

withConnection :: ConnectInfo -> (Connection -> IO a) -> IO a
withConnection connInfo = bracket (PS.connect connInfo) PS.close

-- Modeling

newtype Model r = Model [(Isbn, Book)]
  deriving (Generic, Show)

instance ToExpr (Model Concrete) where

initModel :: Model v
initModel = Model []

newtype Isbn = Isbn { getString :: String } deriving (Eq, Show)

instance ToExpr Isbn where
  toExpr = toExpr . show

instance Arbitrary Isbn where
  arbitrary = oneof [isbn10, isbn13]
    where
      isbn10 = do
        gr <- isbnGroup
        t  <- pubTitle (9 - length gr)
        c  <- elements ('X':['0'..'9'])
        return $ Isbn (gr ++ "-" ++ t ++ "-" ++ [c])
      isbn13 = do
        code <- elements ["978", "979"]
        Isbn x <- isbn10
        return $ Isbn (code ++ "-" ++ x)

isbnGroup :: Gen String
isbnGroup = elements $ show <$> concat [
    [0..5] :: [Integer]
  , [7]
  , [80..94]
  , [600..621]
  , [950..989]
  , [9926..9989]
  , [99901..99976]
  ]

pubTitle :: Int -> Gen String
pubTitle size = do
  i  <- choose (1, size - 1)
  v1 <- vectorOf i $ choose ('0', '9')
  v2 <- vectorOf (size - i) $ choose ('0', '9')
  return $ v1 ++ "-" ++ v2

data Tag
  = New
  | Exist
  | Invalid
  | Avail
  | Unavail
  | Taken
  | Full
  deriving (Eq, Show)

data Command (r :: Type -> Type)
  = NewBook      Tag Isbn String String
  | AddCopy      Tag Isbn
  | Borrow       Tag Isbn
  | Return       Tag Isbn
  | FindByAuthor Tag String
  | FindByTitle  Tag String
  | FindByIsbn   Tag Isbn
  deriving (Show, Generic1)

instance Rank2.Foldable    Command where
instance Rank2.Functor     Command where
instance Rank2.Traversable Command where

data Response (r :: Type -> Type)
  = Rows [Book]
  | Updated
  | Inserted
  | NotFound
  | UniqueError
  | OtherError
  deriving (Eq, Show, Generic1)

instance Rank2.Foldable Response where

generator :: Model Symbolic -> Maybe (Gen (Command Symbolic))
generator (Model m) = Just $ oneof $ [
    NewBook      New     <$> newIsbn <*> stringGen <*> stringGen
  , AddCopy      Invalid <$> newIsbn
  , Borrow       Invalid <$> newIsbn
  , Return       Invalid <$> newIsbn
  , FindByIsbn   Invalid <$> newIsbn
  , FindByTitle  Invalid <$> searchStringGen
  , FindByAuthor Invalid <$> searchStringGen
  ] ++ if null m then [] else [
    NewBook      Exist   <$> existIsbn <*> stringGen <*> stringGen
  , AddCopy      Exist   <$> existIsbn
  , Borrow       Avail   <$> existIsbn
  , Borrow       Unavail <$> existIsbn
  , Return       Taken   <$> existIsbn
  , Return       Full    <$> existIsbn
  , FindByIsbn   Exist   <$> existIsbn
  , FindByTitle  Exist   <$> genTitle
  , FindByAuthor Exist   <$> genAuthor
  ]
  where
    newIsbn = arbitrary `suchThat` \x -> not $ elem x (domain m)
    existIsbn = elements $ domain m
    genTitle  = elements $ (title  <$> codomain m) >>= infixes
    genAuthor = elements $ (author <$> codomain m) >>= infixes

stringGen :: Gen String
stringGen = listOf arbitraryPrintableChar

searchStringGen :: Gen String
searchStringGen = listOf $ frequency [ (7, arbitraryPrintableChar)
                                     , (3, elements ['_', '%']) ]

infixes :: Ord a => [a] -> [[a]]
infixes l = map head . group . sort $ inits l >>= tails

-- How to shrink Commands

shrinker :: Model Symbolic -> Command Symbolic -> [Command Symbolic]
shrinker _ (NewBook tag key x y) = [ NewBook tag key x y' | y' <- shrink y ] ++
                                   [ NewBook tag key x' y | x' <- shrink x ]
shrinker _ (FindByAuthor tag a)  = [ FindByAuthor tag a' | a' <- shrink a ]
shrinker _ (FindByTitle  tag t)  = [ FindByTitle  tag t' | t' <- shrink t ]
shrinker _ _ = []



-- Pre-requisites and invariants

preconditions :: Model Symbolic -> Command Symbolic -> Logic
preconditions (Model m) cmd = case cmd of
  AddCopy    Invalid key   -> Not $ hasKey key
  Borrow     Invalid key   -> Not $ hasKey key
  Return     Invalid key   -> Not $ hasKey key
  FindByIsbn Invalid key   -> Not $ hasKey key
  NewBook    New   key _ _ -> Not $ hasKey key
  NewBook    Exist key _ _ -> hasKey key
  AddCopy    Exist key     -> hasKey key
  FindByIsbn Exist key     -> hasKey key
  Borrow     Avail   key -> keyPred key (\b -> avail b .> 0)
  Borrow     Unavail key -> keyPred key (\b -> avail b .== 0)
  Return     Taken   key -> keyPred key (\b -> owned b .> avail b)
  Return     Full    key -> keyPred key (\b -> owned b .== avail b)
  FindByAuthor Invalid x -> Not $ Exists values (Boolean . isInfixOf x . author)
  FindByTitle Invalid x  -> Not $ Exists values (Boolean . isInfixOf x . title)
  FindByTitle Exist x -> Exists values (Boolean . isInfixOf x . title)
  _ -> Top
  where
    values = codomain m
    hasKey key = key `member` (domain m)
    keyPred key p = maybe Bot p (lookup key m)

postconditions :: Model Concrete -> Command Concrete -> Response Concrete -> Logic
postconditions (Model m) cmd resp = case cmd of
  NewBook    Exist _ _ _ -> resp .== UniqueError
  NewBook    New   _ _ _ -> resp .== Inserted
  AddCopy      Invalid _ -> resp .== NotFound
  Return       Invalid _ -> resp .== NotFound
  Borrow       Invalid _ -> resp .== NotFound
  Return       Full    _ -> resp .== NotFound
  Borrow       Unavail _ -> resp .== NotFound
  Borrow       Avail   _ -> resp .== Updated
  AddCopy      Exist   _ -> resp .== Updated
  Return       Taken   _ -> resp .== Updated
  FindByIsbn   Invalid _ -> resp .== Rows []
  FindByAuthor Invalid _ -> resp .== Rows []
  FindByTitle  Invalid _ -> resp .== Rows []
  FindByIsbn Exist key -> case lookup key m of
    Just x -> Rows [x] .== resp
    _ -> error "Should not happen"
  FindByAuthor Exist x -> case resp of
    Rows rs -> Forall rs (Boolean . isInfixOf x . author) .&&
               Forall rs (\b -> Just b .== lookup (Isbn $ isbn b) m)
    _ -> Bot .// "findByAuthor returned " ++ (show resp)
  FindByTitle Exist x -> case resp of
    Rows rs -> Forall rs (Boolean . isInfixOf x . title) .&&
               Forall rs (\b -> Just b .== lookup (Isbn $ isbn b) m)
    _ -> Bot .// "findByTitle returned " ++ (show resp)
  _ -> Bot

-- Transitions of the state machine that models SUT

transitions :: Model r -> Command r -> Response r -> Model r
transitions (Model m) cmd _ = Model $ case cmd of
  NewBook New key t a -> (key, Book (getString key) t a 0 0):m
  AddCopy Exist key -> map (applyForKey key $ incOwned . incAvail) m
  Borrow  Avail key -> map (applyForKey key decAvail) m
  Return  Taken key -> map (applyForKey key incAvail) m
  _ -> m
  where
    applyForKey key fn (k, v) = (k, if k == key then fn v else v)
    incOwned row = row { owned = 1 + owned row }
    incAvail row = row { avail = 1 + avail row }
    decAvail row = row { avail = (avail row) - 1 }

-- Semantics

data Bug = Bug | NoBug | Injection deriving Eq

semantics :: Bug -> Command Concrete -> ReaderT ConnectInfo IO (Response Concrete)
semantics bug cmd = do
  connInfo <- ask
  liftIO $ withConnection connInfo $ \cn -> case cmd of
    NewBook _ (Isbn key) t a  -> toResp insertRes <$> addBook key t a cn
    AddCopy _ (Isbn key)      -> toResp updateRes <$> addCopy key cn
    Borrow  _ (Isbn key)      -> toResp updateRes <$> borrowCopy key cn
    Return  _ (Isbn key)      -> toResp updateRes <$> returnCopy bug key cn
    FindByAuthor _ x          -> toResp Rows <$> findByAuthor bug x cn
    FindByTitle  _ x          -> toResp Rows <$> findByTitle bug x cn
    FindByIsbn   _ (Isbn key) -> toResp Rows <$> findByIsbn key cn
  where toResp = maybe UniqueError
        updateRes 0 = NotFound
        updateRes 1 = Updated
        updateRes _ = OtherError
        insertRes 1 = Inserted
        insertRes _ = OtherError

-- Mock is currently not used by the library

mock :: Model Symbolic -> Command Symbolic -> GenSym (Response Symbolic)
mock (Model m) cmd = return $ case cmd of
  NewBook New _ _ _ -> Inserted
  NewBook Exist _ _ _ -> UniqueError
  AddCopy Invalid _ -> NotFound
  AddCopy Exist _ -> Updated
  Borrow  Invalid _ -> NotFound
  Borrow  Avail _ -> Updated
  Borrow  Unavail _ -> NotFound
  Return  Invalid _ -> NotFound
  Return  Taken _ -> Updated
  Return  Full _ -> NotFound
  FindByTitle Exist x -> Rows $ filter (isInfixOf x . title) (codomain m)
  FindByAuthor Exist x -> Rows $ filter (isInfixOf x . author) (codomain m)
  FindByIsbn Exist key -> Rows [fromJust (lookup key m)]
  FindByTitle Invalid _ -> Rows []
  FindByIsbn Invalid _ -> Rows []
  FindByAuthor Invalid _ -> Rows []
  _ -> error $ (show cmd) ++ " should not happen"

-- Property

sm :: Bug -> StateMachine Model Command (ReaderT ConnectInfo IO) Response
sm bug = StateMachine initModel transitions preconditions postconditions
  Nothing generator shrinker (semantics bug) mock

runner :: IO String -> ReaderT ConnectInfo IO Property -> IO Property
runner io p = do
  dbIp <- io
  let connInfo = defaultConnectInfo {
    connectUser     = "postgres"
  , connectPassword = "mysecretpassword"
  , connectDatabase = "postgres"
  , connectPort     = 5432
  , connectHost     = dbIp
  }
  bracket (withConnection connInfo setupTable)
          (const (withConnection connInfo teardown))
          (const (runReaderT p connInfo))

prop_bookstore :: Bug -> IO String -> Property
prop_bookstore bug io =
  forAllCommands sm' Nothing $ \cmds -> monadic (ioProperty . runner io) $ do
    (hist, _, res) <- runCommands sm' cmds

    prettyCommands sm' hist $ res === Ok
  where
    sm' = sm bug

-- Setup PostgreSQL db in Docker

setup :: IO (String, String)
setup = do
  pid <- trim <$> readProcess "docker"
    [ "run"
    , "-d"
    , "-e", "POSTGRES_PASSWORD=mysecretpassword"
    , "postgres:10.2"
    ] ""
  ip <- trim <$> readProcess "docker"
    [ "inspect"
    , pid
    , "--format"
    , "'{{range .NetworkSettings.Networks}}{{.IPAddress}}{{end}}'"
    ] ""
  healthyDb pid ip `onException` callProcess "docker" [ "rm", "-f", "-v", pid ]
  return (pid, ip)
  where
    trim :: String -> String
    trim = dropWhileEnd isGarbage . dropWhile isGarbage
      where
        isGarbage = flip elem ['\'', '\n']

    healthyDb :: String -> String -> IO ()
    healthyDb pid ip = do
      sock <- go 10
      Sock.close sock
      where
        go :: Int -> IO Socket
        go 0 = error "healthyDb: db isn't healthy"
        go n = do
          let hints = defaultHints
                { addrFlags      = [AI_NUMERICHOST , AI_NUMERICSERV]
                , addrSocketType = Stream
                }
          addr : _ <- getAddrInfo (Just hints) (Just ip) (Just "5432")
          sock <- socket (addrFamily addr) (addrSocketType addr) (addrProtocol addr)
          (Sock.connect sock (addrAddress addr) >>
            readProcess "docker"
              [ "exec"
              , "-u", "postgres"
              , pid
              , "psql", "-U", "postgres", "-d", "postgres", "-c", "SELECT 1 + 1"
              ] "" >> return sock)
            `catch` (\(_ :: IOException) -> do
                        threadDelay 1000000
                        go (n - 1))

cleanup :: (String, String) -> IO ()
cleanup (pid, _) = callProcess "docker" [ "rm", "-f", "-v", pid ]
