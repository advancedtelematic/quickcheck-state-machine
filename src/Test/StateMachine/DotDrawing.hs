{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE RecordWildCards     #-}

module Test.StateMachine.DotDrawing
  ( GraphOptions (..)
  , Rose (..)
  , printDotGraph
  ) where

import           Control.Monad
import           Data.GraphViz.Attributes.Complete
import           Data.GraphViz.Commands
import           Data.GraphViz.Types.Canonical
import           Data.List (uncons)
import           Data.List.Split
import           Data.Map hiding (null)
import           Data.Maybe
import           Data.Text.Lazy (pack)
import           Prelude
import           Test.StateMachine.Types.History

data GraphOptions = GraphOptions {
      filePath       :: FilePath       --  Where to store the graph
                                       --  (note: file extensions are not checked)
    , graphvizOutput :: GraphvizOutput --  output formats (like Jpeg, Png ..)
}

data Rose a = Rose a (Map Pid a)
    deriving(Functor, Show)

printDotGraph :: GraphOptions -> Rose [String] -> IO ()
printDotGraph GraphOptions{..} (Rose pref sfx) = do
    let

        -- create barrier nodes

        nThreads = size sfx
        barrierRecord = (\n -> PortName (PN {portName = pack $ show n})) <$> [1..nThreads]
        barrierNode = DotNode {
                        nodeID = "barrier"
                        , nodeAttributes =
                            [Shape Record,FixedSize SetNodeSize,Width 4.0,
                                Height 0.0,
                                Label (RecordLabel barrierRecord)]
                        }

        -- create preffix

        prefixWithResp = zip [1..] $ byTwoUnsafe "prefix" pref
        prefixNodes = toDotNode "prefix" <$> prefixWithResp
        prefixEdges = connectNodes prefixNodes

        -- create suffixes

        nodesAndEdges = flip Prelude.map (toList sfx) $ \(pid, str) ->
            let p = unPid pid
                s = zip [1..] $ byTwoUnsafe (show p) str
                n = toDotNode (show p) <$> s
                e = connectNodes n
            in (p, n, e)
        nodes = concatMap (\(_,n,_) -> n) nodesAndEdges
        edges = concatMap (\(_,_,e) -> e) nodesAndEdges
        firstOfEachPid = (\(p, n, _) -> (p, fmap fst $ uncons n)) <$> nodesAndEdges

        -- create barrier edges

        edgesFromBarrier = concat $ (\(p, mn) -> case mn of
                            Nothing -> []
                            Just n -> [DotEdge {
                                      fromNode = nodeID barrierNode
                                    , toNode = nodeID n
                                    , edgeAttributes = [TailPort (LabelledPort (PN {portName = pack $ show p}) Nothing)]
                                    }]) <$> firstOfEachPid
        prefixToBarrier = case prefixNodes of
            [] -> []
            _  -> [DotEdge {
                        fromNode = nodeID (last prefixNodes)
                    , toNode = nodeID barrierNode
                    , edgeAttributes = [] -- [HeadPort (LabelledPort (PN {portName = "1"}) Nothing)]]
                    }]

        -- create dot graph

        dotStmts = DotStmts {
                    attrStmts = [NodeAttrs {attrs = [Shape BoxShape,Width 4.0]}]
                    , subGraphs = [] -- do we want to put commands with same pid on the same group?
                    , nodeStmts = barrierNode : (prefixNodes ++ nodes)
                    , edgeStmts = prefixToBarrier ++ prefixEdges ++ edges ++ edgesFromBarrier
                    }

        dg = DotGraph {
            strictGraph = False
            , directedGraph = True
            , graphID = Just (Str $ pack "G")
            , graphStatements = dotStmts
        }

    void $ runGraphviz dg graphvizOutput filePath

toDotNode :: String -> (Int, (String,String)) -> DotNode String
toDotNode nodeIdGroup (n, (invocation, resp)) =
    DotNode {
          nodeID = (nodeIdGroup ++ "-" ++ show n)
        , nodeAttributes = [Label $ StrLabel $ pack $
                (newLinesAfter "\\l" 60 invocation)
                ++ "\\n"
                ++ (newLinesAfter "\\r" 60 resp)]
    }

byTwoUnsafe :: String -> [a] -> [(a,a)]
byTwoUnsafe str ls = fromMaybe (error $ "couldn't split " ++ if null str then " " else str ++ " in pairs") $ byTwo ls

byTwo :: [a] -> Maybe [(a,a)]
byTwo = go []
  where
    go acc [] = Just $ reverse acc
    go _acc [_] = Nothing
    go acc (a: b : rest) = go ((a,b) : acc) rest

connectNodes :: [DotNode a] -> [DotEdge a]
connectNodes = go []
  where
    go acc [] = reverse acc
    go acc [_] = reverse acc
    go acc (a:b:rest) = go (DotEdge (nodeID a) (nodeID b) [] : acc) (b:rest)

newLinesAfter :: String -> Int -> String -> String
newLinesAfter esc n str = concat (fmap (\s -> s ++ esc) (chunksOf n str))
