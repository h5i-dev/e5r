import Projects.thermostat.HttpRequestSpec
import Projects.thermostat.HeaderSpec
namespace E5R.Thermostat.HttpRequestBytes
open E5R E5R.Thermostat
open HttpRequestSpec

def bytes (input : List (BitVec 8)) := input.map BitVec.toNat
def parse (input : List (BitVec 8)) (maxHead maxBody : Nat) := parseHead (bytes input) maxHead maxBody

def entry (f : Field) : HeaderSpec.Entry := ⟨f.ns,f.ne,f.vs,f.ve⟩

/-- The Nat specification is used only on actual byte values. -/
theorem bounded (input : List (BitVec 8)) : ∀ b∈bytes input, b<256 := by
  intro b hb
  obtain ⟨v,_,hv⟩ := List.mem_map.mp hb
  rw [←hv];exact v.isLt

/-- Padding after the read limit has no semantic effect. This is a pure
    specification property, separate from the actual ELF access proof. -/
theorem window_take (input : List Nat) (limit : Nat) : window input limit=window (input.take limit) limit := by
  funext i
  unfold window
  split
  · rename_i hi
    simp [List.getD_eq_getElem?_getD,List.getElem?_take,hi]
  · rfl

theorem reads (input input' : List (BitVec 8)) (maxHead maxBody : Nat)
    (h : maxHead≤input.length) (h' : maxHead≤input'.length) (same : input.take maxHead=input'.take maxHead) :
    parse input maxHead maxBody=parse input' maxHead maxBody := by
  have hn : readLimit (bytes input).length maxHead=maxHead := by simp [readLimit,bytes,h]
  have hn' : readLimit (bytes input').length maxHead=maxHead := by simp [readLimit,bytes,h']
  have ht : (bytes input).take maxHead=(bytes input').take maxHead := by simp only [bytes,←List.map_take];rw [same]
  have hw : window (bytes input) maxHead=window (bytes input') maxHead := by rw [window_take,ht,←window_take]
  have lim : readLimit input.length maxHead=maxHead := by simp [readLimit,h]
  have lim' : readLimit input'.length maxHead=maxHead := by simp [readLimit,h']
  simp only [bytes] at hw
  unfold parse parseHead
  simp only [bytes,List.length_map]
  rw [lim,lim',hw]
  simp only [decide_eq_true h,decide_eq_true h']
end E5R.Thermostat.HttpRequestBytes
