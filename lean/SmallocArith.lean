-- Root of the Aeneas-extracted code.
-- The extracted files (Types.lean and Funs.lean) live in the SmallocArith/
-- subdirectory and are produced by running Aeneas on the LLBC output of Charon
-- (see ../smalloc-arith/). Funs.lean additionally imports the hand-written
-- FunsExternal.lean, which models the std intrinsics Aeneas cannot translate
-- (here, usize::ilog2).
import SmallocArith.Types
import SmallocArith.Funs
