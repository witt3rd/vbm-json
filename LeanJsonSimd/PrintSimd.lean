import LeanJson.PrintTape
import VbmSimd.Shims
/-! # `LeanJsonSimd.PrintSimd`: the tape printer with the word load of vbm-simd (the code of `vbm_json_print_tape`)

`LeanJson.printTapeG` (`LeanJson/PrintTape.lean`) is the printer, generic in the load of a tape word and in the writer of a scalar or string node. Here it is run with `ldwS`: the word is one `ld64` (a single 8-byte load, `VbmSimd.ld64`)
when the word is inside the tape and the tape is below 4 GiB (`size / 65536 < 65536`: a literal of 2^32 would be a big number to the compiler) (so that the byte offset is exact on 32 bits), the reference `ldw` otherwise. `ldwS_eq` (`LeanJsonProofs/PrintSimd.lean`): `ldwS = ldw`, so `printTapeS_eq`: `printTapeS = printTape`,
and everything proved of `printTape` (`printTape_encode`) holds of the export. -/
namespace LeanJson
open VbmSimd

/-- `ldw`, by one load. -/
@[inline] def ldwS (a : ByteArray) (i : Nat) : UInt64 :=
  if 8 * i + 8 ≤ a.size ∧ a.size / 65536 < 65536 then ld64 a (8 * i).toUSize else ldw a i

/-- The compact JSON of the tape `(w, x)` (`printTape`), the words read by `ld64`. -/
def printTapeS (w x : ByteArray) : Option ByteArray := printTapeG ldwS pleaf w x

/-- The export `vbm_json_lean_print_tape` (called by `vbm_json_print_tape` in `abi/vbm_json.c`): the JSON bytes, or no bytes for a refused tape (printed JSON is never empty). -/
@[export vbm_json_lean_print_tape]
def printTapeExport (w x : ByteArray) : ByteArray := (printTapeS w x).getD ByteArray.empty

end LeanJson
