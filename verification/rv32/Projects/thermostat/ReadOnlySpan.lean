import Projects.thermostat.ReadOnlyByte
namespace E5R.Thermostat.ReadBytes
open E5R

theorem Span.readonly {B img before after a xs} (h : Span B img before a xs)
    (ho : ∀ i : Fin xs.length, B.inRam (a+BitVec.ofNat 32 i.val) 1=false) : Span B img after a xs :=
  ⟨h.length,h.nowrap,fun i => (h.bytes i).readonly (ho i)⟩
end E5R.Thermostat.ReadBytes
