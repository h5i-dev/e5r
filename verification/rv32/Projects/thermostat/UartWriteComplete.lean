import Projects.thermostat.UartWriteEmpty
import Projects.thermostat.UartWriteMemory
namespace E5R.Thermostat.UartWriteComplete
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (obj src len : Word) :=
  UartWriteReturn.memory (UartWriteRemaining.memory (UartWriteTail.memory ram obj src len) obj (src+len) 0#32) obj

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (obj src len : Word)
    (hp : c.pc=0x8000080a#32) (h10 : c.get 10=obj) (h11 : c.get 11=len)
    (hm : Memory.Block B obj 41) (ha : obj.toNat%4=0)
    (h20 : ramRead ram (obj+20#32) .w=len) (h16 : ramRead ram (obj+16#32) .w=src) :
    ∃ d, Quiet.Steps B img 14 ⟨c,ram⟩ ⟨d,memory ram obj src len⟩ ∧ d.pc=c.get 1 &&& ~~~1 ∧
      (∀ r : Reg, r≠11 → r≠12 → r≠14 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,ta,pa,a12,_,a11,ar,ac⟩ := UartWriteTail.contract B c ram obj src len h10 h11 hm ha h20 h16 hp
  have a10 := (ar 10 (by decide) (by decide) (by decide)).trans h10
  obtain ⟨b,tb,pb,br,bc⟩ := UartWriteRemaining.contract B a (UartWriteTail.memory ram obj src len) obj (src+len) 0#32 a10 a11 a12 hm ha pa
  obtain ⟨u,tu,pu,ur,uc⟩ := UartWriteEmpty.contract B b _ ((br 12).trans a12) pb
  have u10 := (ur 10).trans ((br 10).trans a10)
  obtain ⟨d,td,pd,_,dr,dc⟩ := UartWriteReturn.contract B u _ obj pu u10 hm
  have u1 : u.get 1=c.get 1 := (ur 1).trans ((br 1).trans (ar 1 (by decide) (by decide) (by decide)))
  refine ⟨d,((ta.trans tb).trans tu).trans td,by rw [pd,u1],?_,dc.trans (uc.trans (bc.trans ac))⟩
  intro reg h11 h12 h14
  exact (dr reg h11).trans ((ur reg).trans ((br reg).trans (ar reg h12 h14 h11)))

theorem source (ram : Word → BitVec 8) (obj src len : Word) : ramRead (memory ram obj src len) (obj+16#32) .w=src+len := by
  unfold memory UartWriteReturn.memory
  rw [StoreWords.read_other _ _ _ _ .b (StoreWords.offsets obj 16 4 40 1 (by decide) (by decide) (Or.inl (by decide)))]
  exact UartWriteMemory.remaining_src _ obj _ _

theorem length (ram : Word → BitVec 8) (obj src len : Word) : ramRead (memory ram obj src len) (obj+20#32) .w=0#32 := by
  unfold memory UartWriteReturn.memory
  rw [StoreWords.read_other _ _ _ _ .b (StoreWords.offsets obj 20 4 40 1 (by decide) (by decide) (Or.inl (by decide)))]
  exact UartWriteMemory.remaining_len _ obj _ _

theorem complete (ram : Word → BitVec 8) (obj src len : Word) : memory ram obj src len (obj+40#32)=1#8 :=
  UartWriteReturn.complete _ obj

theorem frame (ram : Word → BitVec 8) (obj src len x : Word) (hx : ∀ i : Fin 41, x≠obj+BitVec.ofNat 32 i.val) : memory ram obj src len x=ram x :=
  (UartWriteMemory.returned_frame _ obj x hx).trans ((UartWriteMemory.remaining_frame _ obj _ _ x hx).trans (UartWriteMemory.tail_frame ram obj src len x hx))
end E5R.Thermostat.UartWriteComplete
