import Projects.thermostat.InitRoutes
import Projects.thermostat.ViewFrame
set_option autoImplicit false
namespace E5R.Thermostat.MainRouterTable
open E5R E5R.Thermostat

/-- The immutable sixty route bytes needed at main dispatch. The unrelated
    initial RX-capacity scratch word is intentionally not part of this view. -/
def At (ram : Word → BitVec 8) : Prop :=
  ∀ i : Fin 5,
    ramRead ram (0x80ffebd8#32+BitVec.ofNat 32 (8*i.val)) .w =
      (match i.val with | 0 => 0x80005b9c#32 | 1 => 0x80005b97#32 | 2 => 0x80005b92#32 | 3 => 0x80005b89#32 | _ => 0x80005b83#32) ∧
    ramRead ram (0x80ffebdc#32+BitVec.ofNat 32 (8*i.val)) .w =
      (match i.val with | 0 => 10#32 | 1 => 5#32 | 2 => 5#32 | 3 => 9#32 | _ => 6#32) ∧
    ram (0x80ffec00#32+BitVec.ofNat 32 (4*i.val)) =
      (match i.val with | 0 => 0#8 | 1 => 3#8 | 2 => 2#8 | _ => 3#8)

theorem initialized {ram : Word → BitVec 8} (layout : InitRoutes.Layout ram) : At ram := layout.1

theorem preserve {before after : Word → BitVec 8} (h : At before)
    (frame : ViewFrame.Region before after 0x80ffebd8#32 60) : At after := by
  intro i
  have small := i.isLt
  have words := h i
  refine ⟨(ViewFrame.word frame (8*i.val) (by omega)).trans words.1,?_,?_⟩
  · have stored := ViewFrame.word frame (4+8*i.val) (by omega)
    have addr : 0x80ffebd8#32+BitVec.ofNat 32 (4+8*i.val)=0x80ffebdc#32+BitVec.ofNat 32 (8*i.val) := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
    rw [addr] at stored
    exact stored.trans words.2.1
  · have stored := frame ⟨40+4*i.val,by omega⟩
    have addr : 0x80ffebd8#32+BitVec.ofNat 32 (40+4*i.val)=0x80ffec00#32+BitVec.ofNat 32 (4*i.val) := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
    rw [addr] at stored
    exact stored.trans words.2.2
end E5R.Thermostat.MainRouterTable
