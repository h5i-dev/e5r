import Projects.thermostat.FormatStr
import Projects.thermostat.CursorLayoutFrame
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.FormatInput
open E5R E5R.Thermostat

/-- Actual default Formatter fields and disjoint Cursor/source/output/stack
    allocations. No Formatter or Cursor behavior is assumed in the layout. -/
structure Data (B : Board) (ram : Word → BitVec 8) (sp fmt obj src dst flags : Word)
    (cap pos : Nat) (xs : List (BitVec 8)) : Prop where
  stack : Memory.Block B sp 64
  aligned : sp.toNat%4 = 0
  object : Memory.Block B fmt 12
  objectAligned : fmt.toNat%4 = 0
  writer : ramRead ram fmt .w = obj
  vtable : ramRead ram (fmt+4#32) .w = 0x80005c04#32
  flagsWord : ramRead ram (fmt+8#32) .w = flags
  defaultFlags : flags &&& 0x18000000#32 = 0#32
  formatterStack : WordRegions.Disjoint fmt 12 sp 64
  layout : CursorInput.Layout B ram (sp+32#32) obj src dst cap pos xs
  objectStack : WordRegions.Disjoint obj 12 sp 64
  sourceStack : WordRegions.Disjoint src xs.length sp 64
  outputStack : WordRegions.Disjoint dst cap sp 64

structure Pre (B : Board) (c : Core) (ram : Word → BitVec 8) (sp fmt obj src dst flags : Word)
    (cap pos : Nat) (xs : List (BitVec 8)) : Prop where
  pc : c.pc = 0x80004790#32
  spReg : c.get 2 = sp+64#32
  formatterReg : c.get 10 = fmt
  sourceReg : c.get 11 = src
  lengthReg : c.get 12 = BitVec.ofNat 32 xs.length
  stack : Memory.Block B sp 64
  aligned : sp.toNat%4 = 0
  object : Memory.Block B fmt 12
  objectAligned : fmt.toNat%4 = 0
  writer : ramRead ram fmt .w = obj
  vtable : ramRead ram (fmt+4#32) .w = 0x80005c04#32
  flagsWord : ramRead ram (fmt+8#32) .w = flags
  defaultFlags : flags &&& 0x18000000#32 = 0#32
  formatterStack : WordRegions.Disjoint fmt 12 sp 64
  layout : CursorInput.Layout B ram (sp+32#32) obj src dst cap pos xs
  objectStack : WordRegions.Disjoint obj 12 sp 64
  sourceStack : WordRegions.Disjoint src xs.length sp 64
  outputStack : WordRegions.Disjoint dst cap sp 64

theorem establishes {B c ram sp fmt obj src dst flags cap pos xs}
    (h : Pre B c ram sp fmt obj src dst flags cap pos xs) (hrom : B.inRam 0x80005c10#32 4 = false) :
    ∃ a, DetSteps B img 37 ⟨c,ram⟩ ⟨a,FormatStrSave.memory ram sp c⟩ ∧ FormatStr.Ready c a obj ∧
      CursorInput.Pre B a (FormatStrSave.memory ram sp c) (sp+32#32) obj src dst cap pos xs := by
  obtain ⟨a,ta,ha⟩ := FormatStr.contract B c ram sp fmt obj flags h.pc h.spReg h.formatterReg h.stack h.aligned
    h.object h.objectAligned h.writer h.vtable h.flagsWord h.defaultFlags h.formatterStack hrom
  have ho : ViewFrame.Region ram (FormatStrSave.memory ram sp c) obj 12 :=
    fun i => FormatStrSave.frame ram sp c _ (h.objectStack i)
  have hs : ViewFrame.Region ram (FormatStrSave.memory ram sp c) src xs.length :=
    fun i => FormatStrSave.frame ram sp c _ (h.sourceStack i)
  have hl := CursorLayoutFrame.frame h.layout ho hs
  refine ⟨a,ta,ha,ha.pc,?_,ha.writer,ha.source.trans h.sourceReg,ha.length.trans h.lengthReg,
    hl.stack,hl.stackAligned,hl.object,hl.objectAligned,hl.capacity,hl.position,hl.pointerWord,hl.capacityWord,hl.positionWord,
    hl.source,hl.short,hl.output,hl.nowrap,hl.objectStack,hl.sourceStack,hl.outputStack,hl.sourceOutput,hl.objectOutput⟩
  rw [ha.sp,h.spReg,BitVec.add_assoc];rfl
theorem to_pre {B c ram sp fmt obj src dst flags cap pos xs}
    (h : Data B ram sp fmt obj src dst flags cap pos xs)
    (hp : c.pc = 0x80004790#32) (hsp : c.get 2 = sp+64#32) (h10 : c.get 10 = fmt)
    (h11 : c.get 11 = src) (h12 : c.get 12 = BitVec.ofNat 32 xs.length) :
    Pre B c ram sp fmt obj src dst flags cap pos xs := by
  exact ⟨hp,hsp,h10,h11,h12,h.stack,h.aligned,h.object,h.objectAligned,h.writer,h.vtable,h.flagsWord,h.defaultFlags,
    h.formatterStack,h.layout,h.objectStack,h.sourceStack,h.outputStack⟩
end E5R.Thermostat.FormatInput
