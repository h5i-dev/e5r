import Projects.thermostat.MainTempSuccessReset
import Projects.thermostat.MainInitWitness
import Projects.thermostat.Blocking
import Projects.thermostat.MainChunkStreamingWitness
import Projects.thermostat.UartWriteWitness
set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 5000000
namespace E5R.Thermostat.MainTempSuccessWitness
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
abbrev B := UartPlatform.board
def header (close : Bool) : List (BitVec 8) := if close then [80,79,83,84,32,47,116,101,109,112,63,113,32,72,84,84,80,47,49,46,49,13,10,72,111,115,116,58,120,13,10,67,111,110,116,101,110,116,45,76,101,110,103,116,104,58,51,13,10,65,117,116,104,111,114,105,122,97,116,105,111,110,58,66,101,97,114,101,114,32,100,101,118,45,107,101,121,13,10,67,111,110,110,101,99,116,105,111,110,58,99,108,111,115,101,13,10,13,10] else [80,79,83,84,32,47,116,101,109,112,63,113,32,72,84,84,80,47,49,46,49,13,10,72,111,115,116,58,120,13,10,67,111,110,116,101,110,116,45,76,101,110,103,116,104,58,51,13,10,65,117,116,104,111,114,105,122,97,116,105,111,110,58,66,101,97,114,101,114,32,100,101,118,45,107,101,121,13,10,13,10]
def body : List (BitVec 8) := [52,48,48]
def expected (close : Bool) : Head :=
  if close then ⟨(0,4),(5,12),1,[⟨23,27,28,29⟩,⟨31,45,46,47⟩,⟨49,62,63,77⟩,⟨79,89,90,95⟩],99,.length 3⟩
  else ⟨(0,4),(5,12),1,[⟨23,27,28,29⟩,⟨31,45,46,47⟩,⟨49,62,63,77⟩],81,.length 3⟩
def wire (close : Bool) (k : Nat) : BitVec 8 := (header close++body)[k]?.getD 0#8

theorem consumed_false : consume (wire false) (header false).length []=⟨(header false).length,header false,.done (expected false)⟩ := by
  have run80 : consume (wire false) 1 ((header false).take 80)=⟨1,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 80++[wire false ((header false).take 80).length]=(header false).take 81 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 81) 1024 1024=.done (expected false) := by decide +kernel
    rw [consume,nextByte,parsed]
    congr 1
  have run79 : consume (wire false) 2 ((header false).take 79)=⟨2,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 79++[wire false ((header false).take 79).length]=(header false).take 80 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 80) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run80]
  have run78 : consume (wire false) 3 ((header false).take 78)=⟨3,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 78++[wire false ((header false).take 78).length]=(header false).take 79 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 79) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run79]
  have run77 : consume (wire false) 4 ((header false).take 77)=⟨4,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 77++[wire false ((header false).take 77).length]=(header false).take 78 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 78) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run78]
  have run76 : consume (wire false) 5 ((header false).take 76)=⟨5,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 76++[wire false ((header false).take 76).length]=(header false).take 77 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 77) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run77]
  have run75 : consume (wire false) 6 ((header false).take 75)=⟨6,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 75++[wire false ((header false).take 75).length]=(header false).take 76 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 76) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run76]
  have run74 : consume (wire false) 7 ((header false).take 74)=⟨7,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 74++[wire false ((header false).take 74).length]=(header false).take 75 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 75) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run75]
  have run73 : consume (wire false) 8 ((header false).take 73)=⟨8,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 73++[wire false ((header false).take 73).length]=(header false).take 74 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 74) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run74]
  have run72 : consume (wire false) 9 ((header false).take 72)=⟨9,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 72++[wire false ((header false).take 72).length]=(header false).take 73 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 73) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run73]
  have run71 : consume (wire false) 10 ((header false).take 71)=⟨10,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 71++[wire false ((header false).take 71).length]=(header false).take 72 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 72) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run72]
  have run70 : consume (wire false) 11 ((header false).take 70)=⟨11,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 70++[wire false ((header false).take 70).length]=(header false).take 71 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 71) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run71]
  have run69 : consume (wire false) 12 ((header false).take 69)=⟨12,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 69++[wire false ((header false).take 69).length]=(header false).take 70 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 70) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run70]
  have run68 : consume (wire false) 13 ((header false).take 68)=⟨13,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 68++[wire false ((header false).take 68).length]=(header false).take 69 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 69) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run69]
  have run67 : consume (wire false) 14 ((header false).take 67)=⟨14,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 67++[wire false ((header false).take 67).length]=(header false).take 68 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 68) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run68]
  have run66 : consume (wire false) 15 ((header false).take 66)=⟨15,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 66++[wire false ((header false).take 66).length]=(header false).take 67 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 67) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run67]
  have run65 : consume (wire false) 16 ((header false).take 65)=⟨16,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 65++[wire false ((header false).take 65).length]=(header false).take 66 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 66) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run66]
  have run64 : consume (wire false) 17 ((header false).take 64)=⟨17,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 64++[wire false ((header false).take 64).length]=(header false).take 65 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 65) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run65]
  have run63 : consume (wire false) 18 ((header false).take 63)=⟨18,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 63++[wire false ((header false).take 63).length]=(header false).take 64 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 64) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run64]
  have run62 : consume (wire false) 19 ((header false).take 62)=⟨19,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 62++[wire false ((header false).take 62).length]=(header false).take 63 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 63) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run63]
  have run61 : consume (wire false) 20 ((header false).take 61)=⟨20,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 61++[wire false ((header false).take 61).length]=(header false).take 62 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 62) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run62]
  have run60 : consume (wire false) 21 ((header false).take 60)=⟨21,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 60++[wire false ((header false).take 60).length]=(header false).take 61 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 61) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run61]
  have run59 : consume (wire false) 22 ((header false).take 59)=⟨22,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 59++[wire false ((header false).take 59).length]=(header false).take 60 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 60) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run60]
  have run58 : consume (wire false) 23 ((header false).take 58)=⟨23,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 58++[wire false ((header false).take 58).length]=(header false).take 59 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 59) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run59]
  have run57 : consume (wire false) 24 ((header false).take 57)=⟨24,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 57++[wire false ((header false).take 57).length]=(header false).take 58 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 58) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run58]
  have run56 : consume (wire false) 25 ((header false).take 56)=⟨25,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 56++[wire false ((header false).take 56).length]=(header false).take 57 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 57) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run57]
  have run55 : consume (wire false) 26 ((header false).take 55)=⟨26,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 55++[wire false ((header false).take 55).length]=(header false).take 56 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 56) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run56]
  have run54 : consume (wire false) 27 ((header false).take 54)=⟨27,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 54++[wire false ((header false).take 54).length]=(header false).take 55 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 55) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run55]
  have run53 : consume (wire false) 28 ((header false).take 53)=⟨28,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 53++[wire false ((header false).take 53).length]=(header false).take 54 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 54) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run54]
  have run52 : consume (wire false) 29 ((header false).take 52)=⟨29,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 52++[wire false ((header false).take 52).length]=(header false).take 53 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 53) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run53]
  have run51 : consume (wire false) 30 ((header false).take 51)=⟨30,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 51++[wire false ((header false).take 51).length]=(header false).take 52 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 52) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run52]
  have run50 : consume (wire false) 31 ((header false).take 50)=⟨31,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 50++[wire false ((header false).take 50).length]=(header false).take 51 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 51) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run51]
  have run49 : consume (wire false) 32 ((header false).take 49)=⟨32,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 49++[wire false ((header false).take 49).length]=(header false).take 50 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 50) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run50]
  have run48 : consume (wire false) 33 ((header false).take 48)=⟨33,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 48++[wire false ((header false).take 48).length]=(header false).take 49 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 49) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run49]
  have run47 : consume (wire false) 34 ((header false).take 47)=⟨34,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 47++[wire false ((header false).take 47).length]=(header false).take 48 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 48) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run48]
  have run46 : consume (wire false) 35 ((header false).take 46)=⟨35,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 46++[wire false ((header false).take 46).length]=(header false).take 47 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 47) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run47]
  have run45 : consume (wire false) 36 ((header false).take 45)=⟨36,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 45++[wire false ((header false).take 45).length]=(header false).take 46 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 46) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run46]
  have run44 : consume (wire false) 37 ((header false).take 44)=⟨37,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 44++[wire false ((header false).take 44).length]=(header false).take 45 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 45) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run45]
  have run43 : consume (wire false) 38 ((header false).take 43)=⟨38,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 43++[wire false ((header false).take 43).length]=(header false).take 44 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 44) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run44]
  have run42 : consume (wire false) 39 ((header false).take 42)=⟨39,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 42++[wire false ((header false).take 42).length]=(header false).take 43 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 43) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run43]
  have run41 : consume (wire false) 40 ((header false).take 41)=⟨40,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 41++[wire false ((header false).take 41).length]=(header false).take 42 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 42) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run42]
  have run40 : consume (wire false) 41 ((header false).take 40)=⟨41,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 40++[wire false ((header false).take 40).length]=(header false).take 41 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 41) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run41]
  have run39 : consume (wire false) 42 ((header false).take 39)=⟨42,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 39++[wire false ((header false).take 39).length]=(header false).take 40 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 40) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run40]
  have run38 : consume (wire false) 43 ((header false).take 38)=⟨43,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 38++[wire false ((header false).take 38).length]=(header false).take 39 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 39) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run39]
  have run37 : consume (wire false) 44 ((header false).take 37)=⟨44,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 37++[wire false ((header false).take 37).length]=(header false).take 38 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 38) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run38]
  have run36 : consume (wire false) 45 ((header false).take 36)=⟨45,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 36++[wire false ((header false).take 36).length]=(header false).take 37 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 37) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run37]
  have run35 : consume (wire false) 46 ((header false).take 35)=⟨46,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 35++[wire false ((header false).take 35).length]=(header false).take 36 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 36) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run36]
  have run34 : consume (wire false) 47 ((header false).take 34)=⟨47,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 34++[wire false ((header false).take 34).length]=(header false).take 35 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 35) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run35]
  have run33 : consume (wire false) 48 ((header false).take 33)=⟨48,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 33++[wire false ((header false).take 33).length]=(header false).take 34 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 34) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run34]
  have run32 : consume (wire false) 49 ((header false).take 32)=⟨49,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 32++[wire false ((header false).take 32).length]=(header false).take 33 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 33) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run33]
  have run31 : consume (wire false) 50 ((header false).take 31)=⟨50,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 31++[wire false ((header false).take 31).length]=(header false).take 32 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 32) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run32]
  have run30 : consume (wire false) 51 ((header false).take 30)=⟨51,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 30++[wire false ((header false).take 30).length]=(header false).take 31 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 31) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run31]
  have run29 : consume (wire false) 52 ((header false).take 29)=⟨52,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 29++[wire false ((header false).take 29).length]=(header false).take 30 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 30) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run30]
  have run28 : consume (wire false) 53 ((header false).take 28)=⟨53,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 28++[wire false ((header false).take 28).length]=(header false).take 29 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 29) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run29]
  have run27 : consume (wire false) 54 ((header false).take 27)=⟨54,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 27++[wire false ((header false).take 27).length]=(header false).take 28 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 28) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run28]
  have run26 : consume (wire false) 55 ((header false).take 26)=⟨55,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 26++[wire false ((header false).take 26).length]=(header false).take 27 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 27) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run27]
  have run25 : consume (wire false) 56 ((header false).take 25)=⟨56,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 25++[wire false ((header false).take 25).length]=(header false).take 26 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 26) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run26]
  have run24 : consume (wire false) 57 ((header false).take 24)=⟨57,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 24++[wire false ((header false).take 24).length]=(header false).take 25 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 25) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run25]
  have run23 : consume (wire false) 58 ((header false).take 23)=⟨58,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 23++[wire false ((header false).take 23).length]=(header false).take 24 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 24) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run24]
  have run22 : consume (wire false) 59 ((header false).take 22)=⟨59,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 22++[wire false ((header false).take 22).length]=(header false).take 23 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 23) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run23]
  have run21 : consume (wire false) 60 ((header false).take 21)=⟨60,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 21++[wire false ((header false).take 21).length]=(header false).take 22 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 22) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run22]
  have run20 : consume (wire false) 61 ((header false).take 20)=⟨61,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 20++[wire false ((header false).take 20).length]=(header false).take 21 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 21) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run21]
  have run19 : consume (wire false) 62 ((header false).take 19)=⟨62,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 19++[wire false ((header false).take 19).length]=(header false).take 20 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 20) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run20]
  have run18 : consume (wire false) 63 ((header false).take 18)=⟨63,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 18++[wire false ((header false).take 18).length]=(header false).take 19 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 19) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run19]
  have run17 : consume (wire false) 64 ((header false).take 17)=⟨64,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 17++[wire false ((header false).take 17).length]=(header false).take 18 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 18) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run18]
  have run16 : consume (wire false) 65 ((header false).take 16)=⟨65,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 16++[wire false ((header false).take 16).length]=(header false).take 17 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 17) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run17]
  have run15 : consume (wire false) 66 ((header false).take 15)=⟨66,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 15++[wire false ((header false).take 15).length]=(header false).take 16 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 16) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run16]
  have run14 : consume (wire false) 67 ((header false).take 14)=⟨67,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 14++[wire false ((header false).take 14).length]=(header false).take 15 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 15) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run15]
  have run13 : consume (wire false) 68 ((header false).take 13)=⟨68,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 13++[wire false ((header false).take 13).length]=(header false).take 14 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 14) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run14]
  have run12 : consume (wire false) 69 ((header false).take 12)=⟨69,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 12++[wire false ((header false).take 12).length]=(header false).take 13 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 13) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run13]
  have run11 : consume (wire false) 70 ((header false).take 11)=⟨70,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 11++[wire false ((header false).take 11).length]=(header false).take 12 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 12) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run12]
  have run10 : consume (wire false) 71 ((header false).take 10)=⟨71,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 10++[wire false ((header false).take 10).length]=(header false).take 11 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 11) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run11]
  have run9 : consume (wire false) 72 ((header false).take 9)=⟨72,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 9++[wire false ((header false).take 9).length]=(header false).take 10 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 10) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run10]
  have run8 : consume (wire false) 73 ((header false).take 8)=⟨73,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 8++[wire false ((header false).take 8).length]=(header false).take 9 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 9) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run9]
  have run7 : consume (wire false) 74 ((header false).take 7)=⟨74,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 7++[wire false ((header false).take 7).length]=(header false).take 8 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 8) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run8]
  have run6 : consume (wire false) 75 ((header false).take 6)=⟨75,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 6++[wire false ((header false).take 6).length]=(header false).take 7 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 7) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run7]
  have run5 : consume (wire false) 76 ((header false).take 5)=⟨76,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 5++[wire false ((header false).take 5).length]=(header false).take 6 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 6) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run6]
  have run4 : consume (wire false) 77 ((header false).take 4)=⟨77,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 4++[wire false ((header false).take 4).length]=(header false).take 5 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 5) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run5]
  have run3 : consume (wire false) 78 ((header false).take 3)=⟨78,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 3++[wire false ((header false).take 3).length]=(header false).take 4 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 4) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run4]
  have run2 : consume (wire false) 79 ((header false).take 2)=⟨79,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 2++[wire false ((header false).take 2).length]=(header false).take 3 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 3) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run3]
  have run1 : consume (wire false) 80 ((header false).take 1)=⟨80,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 1++[wire false ((header false).take 1).length]=(header false).take 2 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 2) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run2]
  have run0 : consume (wire false) 81 ((header false).take 0)=⟨81,header false,.done (expected false)⟩ := by
    have nextByte : (header false).take 0++[wire false ((header false).take 0).length]=(header false).take 1 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 1) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run1]
  exact run0

theorem consumed_true : consume (wire true) (header true).length []=⟨(header true).length,header true,.done (expected true)⟩ := by
  have run98 : consume (wire true) 1 ((header true).take 98)=⟨1,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 98++[wire true ((header true).take 98).length]=(header true).take 99 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 99) 1024 1024=.done (expected true) := by decide +kernel
    rw [consume,nextByte,parsed]
    congr 1
  have run97 : consume (wire true) 2 ((header true).take 97)=⟨2,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 97++[wire true ((header true).take 97).length]=(header true).take 98 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 98) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run98]
  have run96 : consume (wire true) 3 ((header true).take 96)=⟨3,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 96++[wire true ((header true).take 96).length]=(header true).take 97 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 97) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run97]
  have run95 : consume (wire true) 4 ((header true).take 95)=⟨4,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 95++[wire true ((header true).take 95).length]=(header true).take 96 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 96) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run96]
  have run94 : consume (wire true) 5 ((header true).take 94)=⟨5,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 94++[wire true ((header true).take 94).length]=(header true).take 95 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 95) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run95]
  have run93 : consume (wire true) 6 ((header true).take 93)=⟨6,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 93++[wire true ((header true).take 93).length]=(header true).take 94 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 94) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run94]
  have run92 : consume (wire true) 7 ((header true).take 92)=⟨7,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 92++[wire true ((header true).take 92).length]=(header true).take 93 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 93) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run93]
  have run91 : consume (wire true) 8 ((header true).take 91)=⟨8,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 91++[wire true ((header true).take 91).length]=(header true).take 92 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 92) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run92]
  have run90 : consume (wire true) 9 ((header true).take 90)=⟨9,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 90++[wire true ((header true).take 90).length]=(header true).take 91 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 91) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run91]
  have run89 : consume (wire true) 10 ((header true).take 89)=⟨10,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 89++[wire true ((header true).take 89).length]=(header true).take 90 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 90) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run90]
  have run88 : consume (wire true) 11 ((header true).take 88)=⟨11,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 88++[wire true ((header true).take 88).length]=(header true).take 89 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 89) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run89]
  have run87 : consume (wire true) 12 ((header true).take 87)=⟨12,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 87++[wire true ((header true).take 87).length]=(header true).take 88 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 88) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run88]
  have run86 : consume (wire true) 13 ((header true).take 86)=⟨13,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 86++[wire true ((header true).take 86).length]=(header true).take 87 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 87) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run87]
  have run85 : consume (wire true) 14 ((header true).take 85)=⟨14,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 85++[wire true ((header true).take 85).length]=(header true).take 86 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 86) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run86]
  have run84 : consume (wire true) 15 ((header true).take 84)=⟨15,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 84++[wire true ((header true).take 84).length]=(header true).take 85 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 85) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run85]
  have run83 : consume (wire true) 16 ((header true).take 83)=⟨16,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 83++[wire true ((header true).take 83).length]=(header true).take 84 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 84) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run84]
  have run82 : consume (wire true) 17 ((header true).take 82)=⟨17,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 82++[wire true ((header true).take 82).length]=(header true).take 83 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 83) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run83]
  have run81 : consume (wire true) 18 ((header true).take 81)=⟨18,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 81++[wire true ((header true).take 81).length]=(header true).take 82 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 82) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run82]
  have run80 : consume (wire true) 19 ((header true).take 80)=⟨19,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 80++[wire true ((header true).take 80).length]=(header true).take 81 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 81) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run81]
  have run79 : consume (wire true) 20 ((header true).take 79)=⟨20,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 79++[wire true ((header true).take 79).length]=(header true).take 80 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 80) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run80]
  have run78 : consume (wire true) 21 ((header true).take 78)=⟨21,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 78++[wire true ((header true).take 78).length]=(header true).take 79 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 79) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run79]
  have run77 : consume (wire true) 22 ((header true).take 77)=⟨22,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 77++[wire true ((header true).take 77).length]=(header true).take 78 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 78) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run78]
  have run76 : consume (wire true) 23 ((header true).take 76)=⟨23,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 76++[wire true ((header true).take 76).length]=(header true).take 77 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 77) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run77]
  have run75 : consume (wire true) 24 ((header true).take 75)=⟨24,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 75++[wire true ((header true).take 75).length]=(header true).take 76 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 76) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run76]
  have run74 : consume (wire true) 25 ((header true).take 74)=⟨25,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 74++[wire true ((header true).take 74).length]=(header true).take 75 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 75) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run75]
  have run73 : consume (wire true) 26 ((header true).take 73)=⟨26,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 73++[wire true ((header true).take 73).length]=(header true).take 74 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 74) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run74]
  have run72 : consume (wire true) 27 ((header true).take 72)=⟨27,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 72++[wire true ((header true).take 72).length]=(header true).take 73 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 73) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run73]
  have run71 : consume (wire true) 28 ((header true).take 71)=⟨28,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 71++[wire true ((header true).take 71).length]=(header true).take 72 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 72) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run72]
  have run70 : consume (wire true) 29 ((header true).take 70)=⟨29,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 70++[wire true ((header true).take 70).length]=(header true).take 71 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 71) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run71]
  have run69 : consume (wire true) 30 ((header true).take 69)=⟨30,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 69++[wire true ((header true).take 69).length]=(header true).take 70 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 70) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run70]
  have run68 : consume (wire true) 31 ((header true).take 68)=⟨31,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 68++[wire true ((header true).take 68).length]=(header true).take 69 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 69) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run69]
  have run67 : consume (wire true) 32 ((header true).take 67)=⟨32,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 67++[wire true ((header true).take 67).length]=(header true).take 68 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 68) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run68]
  have run66 : consume (wire true) 33 ((header true).take 66)=⟨33,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 66++[wire true ((header true).take 66).length]=(header true).take 67 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 67) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run67]
  have run65 : consume (wire true) 34 ((header true).take 65)=⟨34,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 65++[wire true ((header true).take 65).length]=(header true).take 66 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 66) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run66]
  have run64 : consume (wire true) 35 ((header true).take 64)=⟨35,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 64++[wire true ((header true).take 64).length]=(header true).take 65 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 65) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run65]
  have run63 : consume (wire true) 36 ((header true).take 63)=⟨36,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 63++[wire true ((header true).take 63).length]=(header true).take 64 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 64) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run64]
  have run62 : consume (wire true) 37 ((header true).take 62)=⟨37,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 62++[wire true ((header true).take 62).length]=(header true).take 63 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 63) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run63]
  have run61 : consume (wire true) 38 ((header true).take 61)=⟨38,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 61++[wire true ((header true).take 61).length]=(header true).take 62 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 62) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run62]
  have run60 : consume (wire true) 39 ((header true).take 60)=⟨39,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 60++[wire true ((header true).take 60).length]=(header true).take 61 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 61) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run61]
  have run59 : consume (wire true) 40 ((header true).take 59)=⟨40,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 59++[wire true ((header true).take 59).length]=(header true).take 60 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 60) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run60]
  have run58 : consume (wire true) 41 ((header true).take 58)=⟨41,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 58++[wire true ((header true).take 58).length]=(header true).take 59 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 59) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run59]
  have run57 : consume (wire true) 42 ((header true).take 57)=⟨42,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 57++[wire true ((header true).take 57).length]=(header true).take 58 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 58) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run58]
  have run56 : consume (wire true) 43 ((header true).take 56)=⟨43,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 56++[wire true ((header true).take 56).length]=(header true).take 57 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 57) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run57]
  have run55 : consume (wire true) 44 ((header true).take 55)=⟨44,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 55++[wire true ((header true).take 55).length]=(header true).take 56 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 56) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run56]
  have run54 : consume (wire true) 45 ((header true).take 54)=⟨45,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 54++[wire true ((header true).take 54).length]=(header true).take 55 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 55) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run55]
  have run53 : consume (wire true) 46 ((header true).take 53)=⟨46,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 53++[wire true ((header true).take 53).length]=(header true).take 54 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 54) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run54]
  have run52 : consume (wire true) 47 ((header true).take 52)=⟨47,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 52++[wire true ((header true).take 52).length]=(header true).take 53 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 53) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run53]
  have run51 : consume (wire true) 48 ((header true).take 51)=⟨48,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 51++[wire true ((header true).take 51).length]=(header true).take 52 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 52) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run52]
  have run50 : consume (wire true) 49 ((header true).take 50)=⟨49,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 50++[wire true ((header true).take 50).length]=(header true).take 51 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 51) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run51]
  have run49 : consume (wire true) 50 ((header true).take 49)=⟨50,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 49++[wire true ((header true).take 49).length]=(header true).take 50 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 50) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run50]
  have run48 : consume (wire true) 51 ((header true).take 48)=⟨51,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 48++[wire true ((header true).take 48).length]=(header true).take 49 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 49) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run49]
  have run47 : consume (wire true) 52 ((header true).take 47)=⟨52,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 47++[wire true ((header true).take 47).length]=(header true).take 48 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 48) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run48]
  have run46 : consume (wire true) 53 ((header true).take 46)=⟨53,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 46++[wire true ((header true).take 46).length]=(header true).take 47 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 47) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run47]
  have run45 : consume (wire true) 54 ((header true).take 45)=⟨54,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 45++[wire true ((header true).take 45).length]=(header true).take 46 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 46) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run46]
  have run44 : consume (wire true) 55 ((header true).take 44)=⟨55,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 44++[wire true ((header true).take 44).length]=(header true).take 45 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 45) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run45]
  have run43 : consume (wire true) 56 ((header true).take 43)=⟨56,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 43++[wire true ((header true).take 43).length]=(header true).take 44 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 44) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run44]
  have run42 : consume (wire true) 57 ((header true).take 42)=⟨57,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 42++[wire true ((header true).take 42).length]=(header true).take 43 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 43) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run43]
  have run41 : consume (wire true) 58 ((header true).take 41)=⟨58,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 41++[wire true ((header true).take 41).length]=(header true).take 42 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 42) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run42]
  have run40 : consume (wire true) 59 ((header true).take 40)=⟨59,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 40++[wire true ((header true).take 40).length]=(header true).take 41 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 41) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run41]
  have run39 : consume (wire true) 60 ((header true).take 39)=⟨60,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 39++[wire true ((header true).take 39).length]=(header true).take 40 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 40) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run40]
  have run38 : consume (wire true) 61 ((header true).take 38)=⟨61,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 38++[wire true ((header true).take 38).length]=(header true).take 39 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 39) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run39]
  have run37 : consume (wire true) 62 ((header true).take 37)=⟨62,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 37++[wire true ((header true).take 37).length]=(header true).take 38 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 38) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run38]
  have run36 : consume (wire true) 63 ((header true).take 36)=⟨63,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 36++[wire true ((header true).take 36).length]=(header true).take 37 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 37) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run37]
  have run35 : consume (wire true) 64 ((header true).take 35)=⟨64,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 35++[wire true ((header true).take 35).length]=(header true).take 36 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 36) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run36]
  have run34 : consume (wire true) 65 ((header true).take 34)=⟨65,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 34++[wire true ((header true).take 34).length]=(header true).take 35 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 35) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run35]
  have run33 : consume (wire true) 66 ((header true).take 33)=⟨66,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 33++[wire true ((header true).take 33).length]=(header true).take 34 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 34) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run34]
  have run32 : consume (wire true) 67 ((header true).take 32)=⟨67,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 32++[wire true ((header true).take 32).length]=(header true).take 33 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 33) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run33]
  have run31 : consume (wire true) 68 ((header true).take 31)=⟨68,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 31++[wire true ((header true).take 31).length]=(header true).take 32 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 32) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run32]
  have run30 : consume (wire true) 69 ((header true).take 30)=⟨69,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 30++[wire true ((header true).take 30).length]=(header true).take 31 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 31) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run31]
  have run29 : consume (wire true) 70 ((header true).take 29)=⟨70,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 29++[wire true ((header true).take 29).length]=(header true).take 30 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 30) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run30]
  have run28 : consume (wire true) 71 ((header true).take 28)=⟨71,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 28++[wire true ((header true).take 28).length]=(header true).take 29 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 29) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run29]
  have run27 : consume (wire true) 72 ((header true).take 27)=⟨72,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 27++[wire true ((header true).take 27).length]=(header true).take 28 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 28) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run28]
  have run26 : consume (wire true) 73 ((header true).take 26)=⟨73,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 26++[wire true ((header true).take 26).length]=(header true).take 27 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 27) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run27]
  have run25 : consume (wire true) 74 ((header true).take 25)=⟨74,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 25++[wire true ((header true).take 25).length]=(header true).take 26 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 26) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run26]
  have run24 : consume (wire true) 75 ((header true).take 24)=⟨75,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 24++[wire true ((header true).take 24).length]=(header true).take 25 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 25) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run25]
  have run23 : consume (wire true) 76 ((header true).take 23)=⟨76,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 23++[wire true ((header true).take 23).length]=(header true).take 24 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 24) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run24]
  have run22 : consume (wire true) 77 ((header true).take 22)=⟨77,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 22++[wire true ((header true).take 22).length]=(header true).take 23 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 23) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run23]
  have run21 : consume (wire true) 78 ((header true).take 21)=⟨78,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 21++[wire true ((header true).take 21).length]=(header true).take 22 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 22) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run22]
  have run20 : consume (wire true) 79 ((header true).take 20)=⟨79,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 20++[wire true ((header true).take 20).length]=(header true).take 21 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 21) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run21]
  have run19 : consume (wire true) 80 ((header true).take 19)=⟨80,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 19++[wire true ((header true).take 19).length]=(header true).take 20 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 20) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run20]
  have run18 : consume (wire true) 81 ((header true).take 18)=⟨81,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 18++[wire true ((header true).take 18).length]=(header true).take 19 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 19) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run19]
  have run17 : consume (wire true) 82 ((header true).take 17)=⟨82,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 17++[wire true ((header true).take 17).length]=(header true).take 18 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 18) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run18]
  have run16 : consume (wire true) 83 ((header true).take 16)=⟨83,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 16++[wire true ((header true).take 16).length]=(header true).take 17 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 17) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run17]
  have run15 : consume (wire true) 84 ((header true).take 15)=⟨84,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 15++[wire true ((header true).take 15).length]=(header true).take 16 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 16) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run16]
  have run14 : consume (wire true) 85 ((header true).take 14)=⟨85,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 14++[wire true ((header true).take 14).length]=(header true).take 15 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 15) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run15]
  have run13 : consume (wire true) 86 ((header true).take 13)=⟨86,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 13++[wire true ((header true).take 13).length]=(header true).take 14 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 14) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run14]
  have run12 : consume (wire true) 87 ((header true).take 12)=⟨87,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 12++[wire true ((header true).take 12).length]=(header true).take 13 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 13) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run13]
  have run11 : consume (wire true) 88 ((header true).take 11)=⟨88,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 11++[wire true ((header true).take 11).length]=(header true).take 12 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 12) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run12]
  have run10 : consume (wire true) 89 ((header true).take 10)=⟨89,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 10++[wire true ((header true).take 10).length]=(header true).take 11 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 11) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run11]
  have run9 : consume (wire true) 90 ((header true).take 9)=⟨90,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 9++[wire true ((header true).take 9).length]=(header true).take 10 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 10) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run10]
  have run8 : consume (wire true) 91 ((header true).take 8)=⟨91,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 8++[wire true ((header true).take 8).length]=(header true).take 9 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 9) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run9]
  have run7 : consume (wire true) 92 ((header true).take 7)=⟨92,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 7++[wire true ((header true).take 7).length]=(header true).take 8 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 8) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run8]
  have run6 : consume (wire true) 93 ((header true).take 6)=⟨93,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 6++[wire true ((header true).take 6).length]=(header true).take 7 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 7) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run7]
  have run5 : consume (wire true) 94 ((header true).take 5)=⟨94,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 5++[wire true ((header true).take 5).length]=(header true).take 6 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 6) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run6]
  have run4 : consume (wire true) 95 ((header true).take 4)=⟨95,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 4++[wire true ((header true).take 4).length]=(header true).take 5 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 5) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run5]
  have run3 : consume (wire true) 96 ((header true).take 3)=⟨96,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 3++[wire true ((header true).take 3).length]=(header true).take 4 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 4) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run4]
  have run2 : consume (wire true) 97 ((header true).take 2)=⟨97,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 2++[wire true ((header true).take 2).length]=(header true).take 3 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 3) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run3]
  have run1 : consume (wire true) 98 ((header true).take 1)=⟨98,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 1++[wire true ((header true).take 1).length]=(header true).take 2 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 2) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run2]
  have run0 : consume (wire true) 99 ((header true).take 0)=⟨99,header true,.done (expected true)⟩ := by
    have nextByte : (header true).take 0++[wire true ((header true).take 0).length]=(header true).take 1 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 1) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run1]
  exact run0

theorem consumed (close : Bool) : consume (wire close) (header close).length []=⟨(header close).length,header close,.done (expected close)⟩ := by
  cases close
  · exact consumed_false
  · exact consumed_true

def plan (close : Bool) : ChunkReceivePlan.Plan :=
  ⟨fun _ => [0#32,2#32],fun _ => 129#32,fun k => BitVec.ofNat 32 (wire close k).toNat⟩
theorem valid (close : Bool) (first count : Nat) : ChunkReceivePlan.Valid (plan close) (wire close) first count := by
  intro k hk he
  refine ⟨?_,(by change MainChunkPoll.mask 129#32≠0#32;decide +kernel),MainChunkStreamingWitness.byte_roundtrip (wire close k)⟩
  intro status hs
  change status∈[0#32,2#32] at hs
  have casesStatus : status=0#32 ∨ status=2#32 := by simpa using hs
  rcases casesStatus with zero|two <;> subst status <;> decide +kernel

def state : Spec.Snapshot := { Spec.initial with temp := 400#16 }
def result : Spec.Success := ⟨some state,state⟩
def headerSlots (close : Bool) := List.replicate
  (ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot result.reply).length close).length UartWriteWitness.slot1
def bodySlots := List.replicate (ReplyJson.snapshot result.reply).length UartWriteWitness.slot1

theorem delivered (close : Bool) : MainTempSuccessReset.received (wire close) (header close).length (expected close) 3=header close++body := by
  unfold MainTempSuccessReset.received
  rw [consumed close]
  cases close <;> decide +kernel

theorem facts : ∀ close : Bool, (header close).length≤2048 ∧ (expected close).framing=.length 3 ∧
    MainRequestSpans.path (header close++body) (expected close)=WireSpec.ascii "/temp" ∧
    MainMethodSpec.decode (MainMethodBytes.token (header close++body) (expected close).method.2)=.post ∧
    AuthSpec.authorized (HeaderSpec.lookup (MainRequestSpans.raw (header close++body) (expected close) 3) (WireSpec.ascii "authorization") (MainRequestInputs.entries (expected close))) (WireSpec.ascii "dev-key")=true ∧
    WireSpec.decode (WireSpec.ascii "/temp") (MainRequestSpans.body (header close++body) (expected close) 3) none=.ok (.reportTemp 400#16) ∧
    MainCloseSpec.mustClose (expected close).minor 1 (MainRequestSpans.raw (header close++body) (expected close) 3) (MainRequestInputs.entries (expected close))=close := by decide +kernel

/-- Both real keep/close completions update persisted temperature200->400 and
    emit its exact HTTP+JSON bytes from a real POST request with a query. -/
theorem execution (close : Bool) : ∃ n d after reads,
    Observed.Steps B img n ⟨MainInitWitness.core,MainInitWitness.ram⟩ ⟨d,after⟩ reads
      (UartTxLoop.events (ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot state).length close)++UartTxLoop.events (ReplyJson.snapshot state)) ∧
    Observed.input reads=header close++body ∧ d.pc=(if close then 0x80000978#32 else 0x800017be#32) ∧ d.mie_=false ∧
    AppState.At after state ∧ Engine.InvariantAt after 0x80ffebbc#32 := by
  have fs := facts close
  have accepted : (consume (wire close) (header close).length []).result=.done (expected close) := by rw [consumed close]
  obtain ⟨n,d,after,selected,limit,trace,bytes,selection,pc,sp,fp,masked,app,inv⟩ := MainTempSuccessReset.contract
    MainInitWitness.core MainInitWitness.ram (wire close) (plan close) (header close).length (expected close) 3 (plan close)
    rfl (Or.inr rfl) rfl Blocking.stack_available fs.1 (valid close _ _) accepted fs.2.1 (valid close _ _)
    (by rw [delivered];exact fs.2.2.1) (by rw [delivered];exact fs.2.2.2.1) (.reportTemp 400#16) result
    (by rw [delivered];exact fs.2.2.2.2.1) (by rw [delivered];exact fs.2.2.2.2.2.1) rfl
    headerSlots bodySlots (fun _ => List.length_replicate) List.length_replicate
  rw [delivered] at bytes selection
  have selectedClose : selected=close := selection.trans fs.2.2.2.2.2.2
  rw [selectedClose] at trace bytes pc
  exact ⟨n,d,after,_,trace,bytes,pc,masked,app,inv⟩
end E5R.Thermostat.MainTempSuccessWitness
