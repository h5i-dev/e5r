import Projects.thermostat.UartPlatform
import Projects.thermostat.AppendEffect
namespace E5R.Thermostat.FormatSpace
open E5R E5R.Thermostat

/-- The live Cursor and scratch allocations shared by the real format loop.
    Source values and the argument table are additional framed objects. -/
structure Space (ram : Word → BitVec 8) (p obj dst : Word) (cap pos : Nat) : Prop where
  arena : Memory.Block UartPlatform.board p 224
  aligned : p.toNat%4 = 0
  object : Memory.Block UartPlatform.board obj 12
  objectAligned : obj.toNat%4 = 0
  capacity : cap < 2^32
  position : pos ≤ cap
  pointerWord : ramRead ram obj .w = dst
  capacityWord : ramRead ram (obj+4#32) .w = BitVec.ofNat 32 cap
  positionWord : ramRead ram (obj+8#32) .w = BitVec.ofNat 32 pos
  output : Memory.Block UartPlatform.board dst cap
  nowrap : dst.toNat+cap < 2^32
  objectArena : WordRegions.Disjoint obj 12 p 224
  outputArena : WordRegions.Disjoint dst cap p 224
  objectOutput : WordRegions.Disjoint obj 12 dst cap

theorem after_append {ram r p obj dst cap pos xs} (h : Space ram p obj dst cap pos)
    (he : AppendEffect.Effect UartPlatform.board ram r p obj dst 224 cap pos xs)
    (hf : pos+xs.length ≤ cap) : Space r p obj dst cap (pos+xs.length) := by
  exact ⟨h.arena,h.aligned,h.object,h.objectAligned,h.capacity,hf,he.pointer,he.capacity,
    by simpa only [Cursor.nextPosition,ite_eq_left hf] using he.position,
    h.output,h.nowrap,h.objectArena,h.outputArena,h.objectOutput⟩
end E5R.Thermostat.FormatSpace
