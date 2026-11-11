-- | Compatibility shim.  The implementation lives in 'IntInterpreter';
-- this module only re-exports it so that old imports keep working.
module Interpreter (interpret, prepareSnapshotBenchmark) where

import IntInterpreter (interpret, prepareSnapshotBenchmark)
