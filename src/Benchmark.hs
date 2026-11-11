{-# LANGUAGE BangPatterns #-}

module Benchmark
  ( runBenchmarks
  , runEdgeSweepBenchmarks
  , runTopologySweepBenchmarks,
  validateTopologyGraphs
  , GraphKind(..)
  , GraphConfig(..)
  , EdgeConfig(..)
  , SnapshotGraph(..)
  , SnapshotStats(..)
  , generateGraph
  , generateEdgeGraph
  , defaultConfigs
  ) where

import Control.DeepSeq (NFData(..))
import Criterion.Main
import IntInterpreter
  ( prepareSnapshotBenchmark
  )
import Data.List (intercalate)
import Control.Monad (forM_, unless)

--------------------------------------------------------------------------------
-- Graph descriptions
--------------------------------------------------------------------------------

-- | The topology of the graph to be generated.
data GraphKind
  = Chain
  | Star
  | Tree
  | SharedDAG
  | DenseDAG
  deriving (Show, Eq, Ord, Enum, Bounded)

-- | Parameters used by a graph generator.
--
-- depth:
--   Number of edges along the longest root-to-leaf path.
--
-- branching:
--   Number of branches or nodes per layer, depending on graph kind.
data GraphConfig = GraphConfig
  { graphKind  :: !GraphKind
  , depth      :: !Int
  , branching  :: !Int
  } deriving (Show, Eq, Ord)

-- | A graph represented by integer node identifiers and directed edges.
--
-- Nodes are numbered from 0 to nodeCount - 1.
-- Node 0 is always the root.
data SnapshotGraph = SnapshotGraph
  { nodeCount :: !Int
  , rootNode  :: !Int
  , edges     :: ![(Int, Int)]
  } deriving (Show, Eq)

-- | Statistics returned by one snapshot execution.
data SnapshotStats = SnapshotStats
  { visitedCells    :: !Int
  , allocatedCells  :: !Int
  , allocatedEnvs   :: !Int
  } deriving (Show, Eq)

instance NFData SnapshotStats where
  rnf (SnapshotStats a b c) =
    rnf a `seq` rnf b `seq` rnf c

data EdgeConfig = EdgeConfig
  { edgeVertices :: !Int
  , edgeCount    :: !Int
  } deriving (Show, Eq, Ord)

data Topology
  = Uniform
  | Hub
  | Convergent
  | Dispersed
  deriving (Show, Eq, Ord, Enum, Bounded)

--------------------------------------------------------------------------------
-- Graph generation
--------------------------------------------------------------------------------

generateTopologyGraph
  :: Topology
  -> EdgeConfig
  -> Either String SnapshotGraph
generateTopologyGraph topology config
  | v < 2 =
      Left "At least two vertices are required"

  | e < v - 1 =
      Left "Edge count must be at least V - 1"

  | e > maxEdges =
      Left "Too many edges for a simple DAG"

  | length candidates < extraCount =
      Left "Requested edge count exceeds topology capacity"

  | otherwise =
      Right SnapshotGraph
        { nodeCount = v
        , rootNode = 0
        , edges = backbone <> take extraCount candidates
        }
  where
    v = edgeVertices config
    e = edgeCount config

    maxEdges = v * (v - 1) `div` 2

    extraCount = e - (v - 1)

    backbone =
      [(i, i + 1) | i <- [0 .. v - 2]]

    -- All possible non-backbone forward edges.
    allCandidates =
      [ (i, i + distance)
      | distance <- [2 .. v - 1]
      , i <- [0 .. v - distance - 1]
      ]

    -- Rotate a list without changing its elements.
    rotate :: Int -> [a] -> [a]
    rotate _ [] = []
    rotate n xs =
      let k = n `mod` length xs
      in drop k xs <> take k xs

    -- Uniformly distribute outgoing edges across source vertices.
    uniformCandidates =
      concat
        [ let sources = [0 .. v - distance - 1]
          in
            [ (i, i + distance)
            | i <- rotate distance sources
            ]
        | distance <- [2 .. v - 1]
        ]

    -- Concentrate outgoing edges in the first quarter of vertices.
    hubCount = max 1 (v `div` 4)

    hubCandidates =
      [ (i, j)
      | i <- [0 .. hubCount - 1]
      , j <- [i + 2 .. v - 1]
      ]

    -- Concentrate incoming edges in the final quarter of vertices.
    targetStart = v - hubCount

    convergentCandidates =
      [ (i, j)
      | j <- [targetStart .. v - 1]
      , i <- [0 .. j - 2]
      ]

    -- Prefer long-distance edges, spreading their sources
    -- across the available range at each distance.
    dispersedCandidates =
      concat
        [ let sources = [0 .. v - distance - 1]
          in
            [ (i, i + distance)
            | i <- rotate distance sources
            ]
        | distance <- reverse [2 .. v - 1]
        ]

    candidates =
      case topology of
        Uniform    -> uniformCandidates
        Hub        -> hubCandidates
        Convergent -> convergentCandidates
        Dispersed  -> dispersedCandidates

topologyConfigs :: [EdgeConfig]
topologyConfigs =
  -- [ EdgeConfig 1000 e
  -- | e <- [999, 1998, 4995, 9990, 19980, 49950, 99900, 199800]
  -- ]
  -- <>
  -- [ EdgeConfig 2000 e
  -- | e <- [1999, 3998, 9995, 19990, 39980, 99950, 199900, 39980]
  -- ]
  [ EdgeConfig 1000 e | e <- [999, 1998, 4995] ]

topologies :: [Topology]
topologies =
  [Uniform, Hub, Convergent, Dispersed]

runTopologySweepBenchmarks :: IO ()
runTopologySweepBenchmarks =
  defaultMain
    [ bgroup ("V=" <> show v)
        [ bgroup ("E=" <> show e)
            [ env (prepareGraph graph) $
                \(PreparedSnapshot action) ->
                  bench (show topology) $
                    nfIO action
            | topology <- topologies
            , Right graph <-
                [generateTopologyGraph topology config]
            ]
        | config@(EdgeConfig vertices e) <- topologyConfigs
        , vertices == v
        ]
    | v <- [1000, 2000]
    ]

validateTopologyGraphs :: IO ()
validateTopologyGraphs =
  forM_ topologyConfigs $ \config ->
    forM_ topologies $ \topology ->
      case generateTopologyGraph topology config of
        Left err -> putStrLn $ show topology <> ": " <> err
        Right graph -> do
          let actualV = nodeCount graph
              actualE = length (edges graph)
          unless (actualV == edgeVertices config && actualE == edgeCount config) $
            ioError $ userError $ "Invalid graph: " <> show (topology, config)

-- | Generate a graph from its configuration.
--
-- The first argument must be non-negative.
-- The branching factor must be positive.
generateGraph :: GraphConfig -> Either String SnapshotGraph
generateGraph config
  | depth config < 0 =
      Left "Graph depth must be non-negative"

  | branching config < 1 =
      Left "Graph branching factor must be positive"

  | otherwise =
      case graphKind config of
        Chain    -> Right (generateChain (depth config))
        Star     -> Right (generateStar (depth config) (branching config))
        Tree     -> Right (generateTree (depth config) (branching config))
        SharedDAG -> Right (generateSharedDAG (depth config) (branching config))
        DenseDAG -> Right (generateDenseDAG (depth config) (branching config))

generateEdgeGraph :: EdgeConfig -> Either String SnapshotGraph
generateEdgeGraph config
  | v < 1 =
      Left "Vertex count must be positive"

  | e < v - 1 =
      Left "Edge count is too small: graph would be disconnected"

  | e > maxEdges =
      Left "Edge count exceeds the maximum for a simple DAG"

  | otherwise =
      Right SnapshotGraph
        { nodeCount = v
        , rootNode = 0
        , edges = backbone <> extraEdges
        }
  where
    v = edgeVertices config
    e = edgeCount config

    -- Maximum number of edges in a simple DAG.
    maxEdges = v * (v - 1) `div` 2

    -- A chain guarantees reachability of every vertex.
    backbone =
      [(i, i + 1) | i <- [0 .. v - 2]]

    -- Additional forward edges. The chain edges are excluded.
    candidates =
      [ (i, j)
      | i <- [0 .. v - 1]
      , j <- [i + 2 .. v - 1]
      ]

    extraEdges =
      take (e - (v - 1)) candidates

edgeConfigs :: [EdgeConfig]
edgeConfigs =
  -- V = 1000
  [ EdgeConfig 1000 e
  | e <- [999, 1998, 4995, 9990, 19980, 49950, 99900, 199800]
  ]
  <>
  -- V = 2000
  [ EdgeConfig 2000 e
  | e <- [1999, 3998, 9995, 19990, 39980, 99950, 199900, 399800]
  ]

runEdgeSweepBenchmarks :: IO ()
runEdgeSweepBenchmarks =
  defaultMain
    [ bgroup ("V=" <> show v)
        [ env (prepareGraph graph) $ \(PreparedSnapshot action) ->
            bench ("E=" <> show e) $
              nfIO action
        | EdgeConfig vertices e <- edgeConfigs
        , vertices == v
        , Right graph <- [generateEdgeGraph (EdgeConfig vertices e)]
        ]
    | v <- [1000, 2000]
    ]

--------------------------------------------------------------------------------
-- Chain
--------------------------------------------------------------------------------

-- 0 -> 1 -> 2 -> ... -> depth
--
-- Number of vertices: depth + 1
-- Number of edges:    depth

generateChain :: Int -> SnapshotGraph
generateChain d =
  SnapshotGraph
    { nodeCount = d + 1
    , rootNode = 0
    , edges = [(i, i + 1) | i <- [0 .. d - 1]]
    }

--------------------------------------------------------------------------------
-- Star
--------------------------------------------------------------------------------

-- The root has 'branching' independent arms.
-- Each arm is a chain of length 'depth'.
--
-- For example, depth = 2, branching = 3:
--
--       0
--     / | \
--    1  3  5
--    |  |  |
--    2  4  6
--
-- Number of vertices: 1 + depth * branching
-- Number of edges:    depth * branching

generateStar :: Int -> Int -> SnapshotGraph
generateStar d b =
  let
    armNode arm level =
      1 + arm * d + (level - 1)

    firstEdges =
      [(0, armNode arm 1) | d > 0, arm <- [0 .. b - 1]]

    innerEdges =
      [ (armNode arm level, armNode arm (level + 1))
      | arm <- [0 .. b - 1]
      , level <- [1 .. d - 1]
      ]

  in
    SnapshotGraph
      { nodeCount = 1 + d * b
      , rootNode = 0
      , edges = firstEdges <> innerEdges
      }

--------------------------------------------------------------------------------
-- Tree
--------------------------------------------------------------------------------

-- A full b-ary tree of depth d.
--
-- Each node has exactly b children, except nodes at the final level.
--
-- Number of vertices:
--   1 + b + b^2 + ... + b^d
--
-- Number of edges:
--   nodeCount - 1

generateTree :: Int -> Int -> SnapshotGraph
generateTree d b =
  let
    widths =
      take (d + 1) (iterate (* b) 1)

    offsets =
      scanl (+) 0 widths

    totalNodes =
      sum widths

    levelEdges level =
      let
        parentOffset = offsets !! level
        childOffset = offsets !! (level + 1)
        parentWidth = widths !! level
      in
        [ (parentOffset + parent, childOffset + parent * b + child)
        | parent <- [0 .. parentWidth - 1]
        , child <- [0 .. b - 1]
        ]

    allEdges =
      concat
        [ levelEdges level
        | level <- [0 .. d - 1]
        ]

  in
    SnapshotGraph
      { nodeCount = totalNodes
      , rootNode = 0
      , edges = allEdges
      }

--------------------------------------------------------------------------------
-- Shared DAG
--------------------------------------------------------------------------------

-- The graph has a root and several layers.
--
-- The root points to every node in the first layer.
-- Every node in a layer points to two nodes in the next layer:
--   * the node with the same index;
--   * the next node, wrapping around at the end.
--
-- Multiple parents can therefore reference the same node.
--
-- For branching >= 2, this creates shared subgraphs.
--
-- Number of vertices: 1 + depth * branching
-- Number of edges:    branching + 2 * branching * (depth - 1)
--                     when depth > 0

generateSharedDAG :: Int -> Int -> SnapshotGraph
generateSharedDAG d b =
  let
    layerNode level index =
      1 + (level - 1) * b + index

    rootEdges =
      [(0, layerNode 1 i) | d > 0, i <- [0 .. b - 1]]

    layerEdges =
      [ (layerNode level i, layerNode (level + 1) target)
      | level <- [1 .. d - 1]
      , i <- [0 .. b - 1]
      , target <- [i, (i + 1) `mod` b]
      ]

  in
    SnapshotGraph
      { nodeCount = 1 + d * b
      , rootNode = 0
      , edges = rootEdges <> layerEdges
      }

--------------------------------------------------------------------------------
-- Dense DAG
--------------------------------------------------------------------------------

-- The graph has a root and several layers.
--
-- The root points to every node in the first layer.
-- Every node in one layer points to every node in the next layer.
--
-- This increases the number of edges much faster than the number
-- of vertices.
--
-- Number of vertices: 1 + depth * branching
-- Number of edges:    branching + (depth - 1) * branching^2

generateDenseDAG :: Int -> Int -> SnapshotGraph
generateDenseDAG d b =
  let
    layerNode level index =
      1 + (level - 1) * b + index

    rootEdges =
      [(0, layerNode 1 i) | d > 0, i <- [0 .. b - 1]]

    layerEdges =
      [ (layerNode level i, layerNode (level + 1) j)
      | level <- [1 .. d - 1]
      , i <- [0 .. b - 1]
      , j <- [0 .. b - 1]
      ]

  in
    SnapshotGraph
      { nodeCount = 1 + d * b
      , rootNode = 0
      , edges = rootEdges <> layerEdges
      }

--------------------------------------------------------------------------------
-- Criterion setup
--------------------------------------------------------------------------------

-- | A prepared benchmark action.
--
-- Criterion requires an NFData environment. The action itself is intentionally
-- not executed or forced during setup.
newtype PreparedSnapshot = PreparedSnapshot
  { runPreparedSnapshot :: IO SnapshotStats
  }

instance NFData PreparedSnapshot where
  rnf (PreparedSnapshot _) = ()

-- | Prepare the interpreter state outside the measured region.
--
-- The Interpreter adapter must:
--   1. Build the graph in a fresh heap.
--   2. Save the initial interpreter state.
--   3. Return an action that runs snapshotEnv against a fresh copy
--      of that initial state on every invocation.
prepareGraph :: SnapshotGraph -> IO PreparedSnapshot
prepareGraph graph = do
  action <- prepareSnapshotBenchmark
    (rootNode graph)
    (edges graph)

  pure $ PreparedSnapshot $ do
    (visited, allocated, envs) <- action
    pure $ SnapshotStats visited allocated envs

--------------------------------------------------------------------------------
-- Benchmark configurations
--------------------------------------------------------------------------------

defaultConfigs :: [GraphConfig]
defaultConfigs =
  -- Chains: vary depth while keeping branching irrelevant.
  [ GraphConfig Chain d 1
  | d <- [100, 500, 1000, 2000, 4000]
  ]
  <>
  -- Stars: vary width and depth.
  [ GraphConfig Star d b
  | (d, b) <- [(1, 100), (1, 500), (1, 1000), (4, 250), (8, 250)]
  ]
  <>
  -- Trees: vary branching and depth.
  [ GraphConfig Tree d b
  | (d, b) <- [(4, 2), (6, 2), (8, 2), (4, 3), (5, 3)]
  ]
  <>
  -- Shared DAGs: many paths converge on common nodes.
  [ GraphConfig SharedDAG d b
  | (d, b) <- [(10, 10), (50, 10), (100, 10), (50, 50), (100, 50)]
  ]
  <>
  -- Dense DAGs: increase edge count while keeping vertex count moderate.
  [ GraphConfig DenseDAG d b
  | (d, b) <- [(10, 5), (10, 10), (20, 10), (20, 20)]
  ]

--------------------------------------------------------------------------------
-- Benchmark names
--------------------------------------------------------------------------------

configName :: GraphConfig -> String
configName config =
  intercalate "/"
    [ show (graphKind config)
    , "depth=" <> show (depth config)
    , "branching=" <> show (branching config)
    ]
--------------------------------------------------------------------------------
-- Benchmark runner
--------------------------------------------------------------------------------

runBenchmarks :: IO ()
runBenchmarks =
  defaultMain [
    bgroup (show kind) [
      env (prepareGraph graph) $ \(PreparedSnapshot action) -> bench (configName config) $ nfIO action
      | config <- defaultConfigs,
      graphKind config == kind,
      Right graph <- [generateGraph config]
    ]
    | kind <- [minBound .. maxBound]
  ]
