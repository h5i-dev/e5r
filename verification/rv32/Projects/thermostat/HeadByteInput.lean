import Projects.thermostat.HttpRequestBytes
import Projects.thermostat.Bytes
import Projects.thermostat.HeadLineScanSpec
import Projects.thermostat.HeadEarlyPath
namespace E5R.Thermostat.HeadByteInput
open E5R E5R.Thermostat HttpRequestSpec

def term (input : List (BitVec 8)) : Nat :=
  let n := min input.length 1024
  let g := window (HttpRequestBytes.bytes input) n
  lineTerm g (lineEnd g 0 n) n

theorem read_limit (input : List (BitVec 8)) :
    readLimit (HttpRequestBytes.bytes input).length 1024=min input.length 1024 := by
  by_cases full : 1024≤input.length
  · simp only [readLimit,HttpRequestBytes.bytes,List.length_map,full,ite_true,Nat.min_eq_right full]
  · have short : input.length≤1024 := by omega
    simp only [readLimit,HttpRequestBytes.bytes,List.length_map,full,ite_false,Nat.min_eq_left short]

theorem agree {ram buf input} (h : Bytes.At ram buf input) :
    ∀ k, k<min input.length 1024 → HeadLineScanSpec.bytes ram buf k=window (HttpRequestBytes.bytes input) (min input.length 1024) k := by
  intro k hk
  have bound : k<input.length := Nat.lt_of_lt_of_le hk (Nat.min_le_left _ _)
  have hb := h ⟨k,bound⟩
  change ram (buf+BitVec.ofNat 32 k)=input[k] at hb
  unfold HeadLineScanSpec.bytes window
  rw [hb]
  simp only [hk,ite_true,HttpRequestBytes.bytes,List.getD_eq_getElem?_getD,List.getElem?_map,
    List.getElem?_eq_getElem bound,Option.map_some,Option.getD_some]

theorem classification (input : List (BitVec 8)) (early : term input=1 ∨ term input=2) :
    HttpRequestBytes.parse input 1024 1024=HeadEarlyFinish.out (HeadEarlyPath.kind input.length (term input)) := by
  unfold HttpRequestBytes.parse parseHead
  rw [read_limit]
  have length : (HttpRequestBytes.bytes input).length=input.length := by simp only [HttpRequestBytes.bytes,List.length_map]
  rw [length]
  dsimp only
  rcases early with one|two
  · have one' := one
    dsimp only [term] at one'
    rw [one']
    simp only [ite_true]
    by_cases full : 1024≤input.length
    all_goals simp only [HeadEarlyPath.kind,one,full,decide_true,decide_false,Bool.false_eq_true,ite_true,ite_false,HeadEarlyFinish.out]
  · have two' := two
    dsimp only [term] at two'
    rw [two']
    simp only [show ¬(2=1) by decide,ite_false,ite_true]
    simp only [HeadEarlyPath.kind,two,show ¬(2=1) by decide,ite_false,HeadEarlyFinish.out]
end E5R.Thermostat.HeadByteInput
