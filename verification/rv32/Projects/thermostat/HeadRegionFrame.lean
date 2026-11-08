import Projects.thermostat.ViewFrame
namespace E5R.Thermostat.HeadRegionFrame
open E5R E5R.Thermostat

theorem trans {before mid after : Word → BitVec 8} {p : Word} {n : Nat}
    (first : ViewFrame.Region before mid p n) (second : ViewFrame.Region mid after p n) :
    ViewFrame.Region before after p n := fun i => (second i).trans (first i)

theorem sub {before after : Word → BitVec 8} {p : Word} {n : Nat}
    (h : ViewFrame.Region before after p n) (off len : Nat) (bound : off+len≤n) :
    ViewFrame.Region before after (p+BitVec.ofNat 32 off) len := by
  intro i
  have value := h ⟨off+i.val,by have hi := i.isLt;omega⟩
  simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using value

theorem offset {before after : Word → BitVec 8} {sp : Word} {base n : Nat}
    (h : ViewFrame.Region before after (sp+BitVec.ofNat 32 base) n)
    (off len : Nat) (lower : base≤off) (upper : off+len≤base+n) :
    ViewFrame.Region before after (sp+BitVec.ofNat 32 off) len := by
  have value := sub h (off-base) len (by omega)
  have address : (sp+BitVec.ofNat 32 base)+BitVec.ofNat 32 (off-base)=sp+BitVec.ofNat 32 off := by
    rw [BitVec.add_assoc,←BitVec.ofNat_add,show base+(off-base)=off by omega]
  rw [address] at value
  exact value
end E5R.Thermostat.HeadRegionFrame
