import Projects.thermostat.MainChunkReceiveMemory
import Projects.thermostat.ChunkBufferView
namespace E5R.Thermostat.MainChunkRefillFrame
open E5R E5R.Thermostat
open MainChunkReceiveMemory

def memory (ram : Word → BitVec 8) (sp filled read datum io : Word) :=
  MainChunkReceiveTail.memory (MainChunkReceiveSetup.memory ram sp filled io) sp filled read datum

theorem region (ram : Word → BitVec 8) (sp filled read datum io : Word) (off len : Nat)
    (hf : filled.toNat<2048) (hb : off+len≤4294967296)
    (hr : off+len≤132+filled.toNat ∨ 132+filled.toNat+1≤off)
    (hd : off+len≤3664 ∨ 3677≤off) (hc : off+len≤3288 ∨ 3292≤off) :
    ViewFrame.Region ram (memory ram sp filled read datum io) (sp+BitVec.ofNat 32 off) len := by
  intro i
  exact (tail_region _ sp filled read datum off len hf hb hr (by omega) hc i).trans
    (setup_region ram sp filled io off len hb hd i)

theorem word (ram : Word → BitVec 8) (sp filled read datum io : Word) (off : Nat)
    (hf : filled.toNat<2048) (hb : off+4≤4294967296) (hr : 2180≤off)
    (hd : off+4≤3664 ∨ 3677≤off) (hc : off+4≤3288 ∨ 3292≤off) :
    ramRead (memory ram sp filled read datum io) (sp+BitVec.ofNat 32 off) .w=
      ramRead ram (sp+BitVec.ofNat 32 off) .w := by
  simpa only [BitVec.add_zero] using ViewFrame.word
    (region ram sp filled read datum io off 4 hf hb (by omega) hd hc) 0 (by decide)

theorem layout {ram sp filled read datum io} (hf : filled.toNat<2048) (h : MainChunkLayout.At ram sp) :
    MainChunkLayout.At (memory ram sp filled read datum io) sp := by
  exact ⟨(word ram sp filled read datum io 3312 hf (by decide) (by decide) (by decide) (by decide)).trans h.rx,
    (word ram sp filled read datum io 3316 hf (by decide) (by decide) (by decide) (by decide)).trans h.capacity,
    (word ram sp filled read datum io 3636 hf (by decide) (by decide) (by decide) (by decide)).trans h.limits,
    (word ram sp filled read datum io 3284 hf (by decide) (by decide) (by decide) (by decide)).trans h.maxBody,
    (word ram sp filled read datum io 3640 hf (by decide) (by decide) (by decide) (by decide)).trans h.filledPtr⟩

theorem state {ram sp filled read datum io s} (hf : filled.toNat<2048) (hs : ChunkLayout.At ram (sp+3680#32) s) :
    ChunkLayout.At (memory ram sp filled read datum io) (sp+3680#32) s :=
  ChunkStateFrame.preserve hs (region ram sp filled read datum io 3680 25 hf
    (by decide) (by omega) (by decide) (by decide))

theorem filled (ram : Word → BitVec 8) (sp filled read datum io : Word) :
    ramRead (memory ram sp filled read datum io) (sp+3288#32) .w=filled+1#32 :=
  tail_filled _ _ _ _ _

theorem stored (ram : Word → BitVec 8) (sp filled read datum io : Word) (hf : filled.toNat<2048) :
    memory ram sp filled read datum io ((sp+132#32)+filled)=byteOf datum 0 :=
  tail_stored _ _ _ _ _ hf

theorem rx_before (ram : Word → BitVec 8) (sp filled read datum io : Word) (hf : filled.toNat<2048) :
    ViewFrame.Region ram (memory ram sp filled read datum io) (sp+132#32) filled.toNat :=
  region ram sp filled read datum io 132 filled.toNat hf (by omega) (by omega) (by omega) (by omega)

theorem body {ram sp filled read datum io start body} (hf : filled.toNat<2048)
    (hb : ChunkBufferView.Body ram sp start body) (he : start+body.length≤filled.toNat) :
    ChunkBufferView.Body (memory ram sp filled read datum io) sp start body := by
  intro i
  rw [ChunkBufferView.address,rx_before ram sp filled read datum io hf ⟨start+i.val,by have := i.isLt;omega⟩]
  simpa only [ChunkBufferView.address] using hb i

theorem app (ram : Word → BitVec 8) (filled read datum io : Word) (s : Spec.Snapshot)
    (hf : filled.toNat<2048) (hs : AppState.At ram s) :
    AppState.At (memory ram 0x80ffeb90#32 filled read datum io) s := by
  apply AppState.preserve ram _ s hs
  have r := region ram 0x80ffeb90#32 filled read datum io 44 25 hf
    (by decide) (by omega) (by decide) (by decide)
  have base : 0x80ffeb90#32+44#32=0x80ffebbc#32 := by decide +kernel
  simpa only [ViewFrame.Region,base] using r

end E5R.Thermostat.MainChunkRefillFrame
