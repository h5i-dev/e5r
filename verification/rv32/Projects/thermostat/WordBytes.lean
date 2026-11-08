import Projects.thermostat.StoreBytes
namespace E5R.Thermostat.WordBytes
open E5R E5R.Thermostat

def bytes (w : Word) : List (BitVec 8) := [byteOf w 0,byteOf w 1,byteOf w 2,byteOf w 3]

theorem store (ram : Word → BitVec 8) (p w : Word) (i : Fin 4) :
    ramWrite ram p w .w (p+BitVec.ofNat 32 i.val) = (bytes w)[i.val]'(by change i.val<4;exact i.isLt) := by
  have hi := i.isLt
  have hc : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 := by omega
  rcases hc with h|h|h|h <;>
    simp [bytes,h,ramWrite,ramPut,BitVec.add_right_inj,BitVec.self_eq_add_right]

theorem span {B} (ram : Word → BitVec 8) (p w : Word) (hm : Memory.Block B p 4) :
    Bytes.Span B (ramWrite ram p w .w) p (bytes w) := Bytes.of_block B _ p _ hm (by change 4<2^32;decide) (store ram p w)
end E5R.Thermostat.WordBytes
