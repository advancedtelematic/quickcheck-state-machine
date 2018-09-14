module Main (main) where

import           Brick
import           Data.Text
                   (Text)
import           Data.Text.Zipper
import qualified Graphics.Vty       as V
import           Prelude
import           System.Environment
                   (getArgs)

------------------------------------------------------------------------

main :: IO ()
main = do
  [fp] <- getArgs
  ts   <- read <$> readFile fp
  _finalState <- defaultMain app (initState ts)
  return ()

type State = TextZipper Text

data Name = Viewport1
  deriving (Eq, Ord, Show)

initState :: [Text] -> State
initState ts = textZipper ts Nothing

app :: App State () Name
app = App
  { appDraw         = ui
  , appChooseCursor = neverShowCursor
  , appHandleEvent  = handleEvent
  , appStartEvent   = return
  , appAttrMap      = const (attrMap V.defAttr [])
  }

ui :: State -> [Widget Name]
ui s = [viewport Viewport1 Vertical (txt (currentLine s))]

handleEvent :: State -> BrickEvent Name () -> EventM Name (Next State)
handleEvent s (VtyEvent (V.EvKey (V.KChar 'j') [])) = continue (moveDown s)
handleEvent s (VtyEvent (V.EvKey (V.KChar 'k') [])) = continue (moveUp s)
handleEvent s (VtyEvent (V.EvKey (V.KChar ' ') [])) = do
  vScrollPage (viewportScroll Viewport1) Down
  continue s
handleEvent s (VtyEvent (V.EvKey (V.KChar 'u') [])) = do
  vScrollPage (viewportScroll Viewport1) Up
  continue s
handleEvent s (VtyEvent (V.EvKey (V.KChar 'g') [])) = do
  vScrollToBeginning (viewportScroll Viewport1)
  continue s
handleEvent s (VtyEvent (V.EvKey (V.KChar 'G') [])) = do
  vScrollToEnd (viewportScroll Viewport1)
  continue s
handleEvent s (VtyEvent (V.EvKey (V.KChar 'q') [])) = halt s
handleEvent s _                                     = continue s
