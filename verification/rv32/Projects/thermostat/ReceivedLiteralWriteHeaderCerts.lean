import Projects.thermostat.ReceivedLiteralWriteData
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.ReceivedLiteralWriteWitness
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec

theorem header_setpoint : consume (wire .setpoint) (headBytes .setpoint).length []=⟨(headBytes .setpoint).length,headBytes .setpoint,.done (head .setpoint)⟩ := by
  have run93 : consume (wire .setpoint) 1 ((headBytes .setpoint).take 93)=⟨1,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 93++[wire .setpoint ((headBytes .setpoint).take 93).length]=(headBytes .setpoint).take 94 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 94) 1024 1024=.done (head .setpoint) := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    congr 1
  have run92 : consume (wire .setpoint) 2 ((headBytes .setpoint).take 92)=⟨2,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 92++[wire .setpoint ((headBytes .setpoint).take 92).length]=(headBytes .setpoint).take 93 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 93) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run93]
  have run91 : consume (wire .setpoint) 3 ((headBytes .setpoint).take 91)=⟨3,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 91++[wire .setpoint ((headBytes .setpoint).take 91).length]=(headBytes .setpoint).take 92 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 92) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run92]
  have run90 : consume (wire .setpoint) 4 ((headBytes .setpoint).take 90)=⟨4,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 90++[wire .setpoint ((headBytes .setpoint).take 90).length]=(headBytes .setpoint).take 91 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 91) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run91]
  have run89 : consume (wire .setpoint) 5 ((headBytes .setpoint).take 89)=⟨5,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 89++[wire .setpoint ((headBytes .setpoint).take 89).length]=(headBytes .setpoint).take 90 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 90) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run90]
  have run88 : consume (wire .setpoint) 6 ((headBytes .setpoint).take 88)=⟨6,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 88++[wire .setpoint ((headBytes .setpoint).take 88).length]=(headBytes .setpoint).take 89 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 89) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run89]
  have run87 : consume (wire .setpoint) 7 ((headBytes .setpoint).take 87)=⟨7,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 87++[wire .setpoint ((headBytes .setpoint).take 87).length]=(headBytes .setpoint).take 88 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 88) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run88]
  have run86 : consume (wire .setpoint) 8 ((headBytes .setpoint).take 86)=⟨8,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 86++[wire .setpoint ((headBytes .setpoint).take 86).length]=(headBytes .setpoint).take 87 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 87) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run87]
  have run85 : consume (wire .setpoint) 9 ((headBytes .setpoint).take 85)=⟨9,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 85++[wire .setpoint ((headBytes .setpoint).take 85).length]=(headBytes .setpoint).take 86 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 86) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run86]
  have run84 : consume (wire .setpoint) 10 ((headBytes .setpoint).take 84)=⟨10,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 84++[wire .setpoint ((headBytes .setpoint).take 84).length]=(headBytes .setpoint).take 85 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 85) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run85]
  have run83 : consume (wire .setpoint) 11 ((headBytes .setpoint).take 83)=⟨11,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 83++[wire .setpoint ((headBytes .setpoint).take 83).length]=(headBytes .setpoint).take 84 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 84) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run84]
  have run82 : consume (wire .setpoint) 12 ((headBytes .setpoint).take 82)=⟨12,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 82++[wire .setpoint ((headBytes .setpoint).take 82).length]=(headBytes .setpoint).take 83 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 83) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run83]
  have run81 : consume (wire .setpoint) 13 ((headBytes .setpoint).take 81)=⟨13,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 81++[wire .setpoint ((headBytes .setpoint).take 81).length]=(headBytes .setpoint).take 82 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 82) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run82]
  have run80 : consume (wire .setpoint) 14 ((headBytes .setpoint).take 80)=⟨14,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 80++[wire .setpoint ((headBytes .setpoint).take 80).length]=(headBytes .setpoint).take 81 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 81) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run81]
  have run79 : consume (wire .setpoint) 15 ((headBytes .setpoint).take 79)=⟨15,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 79++[wire .setpoint ((headBytes .setpoint).take 79).length]=(headBytes .setpoint).take 80 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 80) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run80]
  have run78 : consume (wire .setpoint) 16 ((headBytes .setpoint).take 78)=⟨16,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 78++[wire .setpoint ((headBytes .setpoint).take 78).length]=(headBytes .setpoint).take 79 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 79) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run79]
  have run77 : consume (wire .setpoint) 17 ((headBytes .setpoint).take 77)=⟨17,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 77++[wire .setpoint ((headBytes .setpoint).take 77).length]=(headBytes .setpoint).take 78 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 78) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run78]
  have run76 : consume (wire .setpoint) 18 ((headBytes .setpoint).take 76)=⟨18,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 76++[wire .setpoint ((headBytes .setpoint).take 76).length]=(headBytes .setpoint).take 77 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 77) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run77]
  have run75 : consume (wire .setpoint) 19 ((headBytes .setpoint).take 75)=⟨19,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 75++[wire .setpoint ((headBytes .setpoint).take 75).length]=(headBytes .setpoint).take 76 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 76) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run76]
  have run74 : consume (wire .setpoint) 20 ((headBytes .setpoint).take 74)=⟨20,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 74++[wire .setpoint ((headBytes .setpoint).take 74).length]=(headBytes .setpoint).take 75 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 75) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run75]
  have run73 : consume (wire .setpoint) 21 ((headBytes .setpoint).take 73)=⟨21,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 73++[wire .setpoint ((headBytes .setpoint).take 73).length]=(headBytes .setpoint).take 74 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 74) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run74]
  have run72 : consume (wire .setpoint) 22 ((headBytes .setpoint).take 72)=⟨22,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 72++[wire .setpoint ((headBytes .setpoint).take 72).length]=(headBytes .setpoint).take 73 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 73) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run73]
  have run71 : consume (wire .setpoint) 23 ((headBytes .setpoint).take 71)=⟨23,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 71++[wire .setpoint ((headBytes .setpoint).take 71).length]=(headBytes .setpoint).take 72 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 72) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run72]
  have run70 : consume (wire .setpoint) 24 ((headBytes .setpoint).take 70)=⟨24,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 70++[wire .setpoint ((headBytes .setpoint).take 70).length]=(headBytes .setpoint).take 71 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 71) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run71]
  have run69 : consume (wire .setpoint) 25 ((headBytes .setpoint).take 69)=⟨25,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 69++[wire .setpoint ((headBytes .setpoint).take 69).length]=(headBytes .setpoint).take 70 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 70) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run70]
  have run68 : consume (wire .setpoint) 26 ((headBytes .setpoint).take 68)=⟨26,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 68++[wire .setpoint ((headBytes .setpoint).take 68).length]=(headBytes .setpoint).take 69 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 69) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run69]
  have run67 : consume (wire .setpoint) 27 ((headBytes .setpoint).take 67)=⟨27,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 67++[wire .setpoint ((headBytes .setpoint).take 67).length]=(headBytes .setpoint).take 68 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 68) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run68]
  have run66 : consume (wire .setpoint) 28 ((headBytes .setpoint).take 66)=⟨28,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 66++[wire .setpoint ((headBytes .setpoint).take 66).length]=(headBytes .setpoint).take 67 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 67) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run67]
  have run65 : consume (wire .setpoint) 29 ((headBytes .setpoint).take 65)=⟨29,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 65++[wire .setpoint ((headBytes .setpoint).take 65).length]=(headBytes .setpoint).take 66 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 66) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run66]
  have run64 : consume (wire .setpoint) 30 ((headBytes .setpoint).take 64)=⟨30,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 64++[wire .setpoint ((headBytes .setpoint).take 64).length]=(headBytes .setpoint).take 65 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 65) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run65]
  have run63 : consume (wire .setpoint) 31 ((headBytes .setpoint).take 63)=⟨31,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 63++[wire .setpoint ((headBytes .setpoint).take 63).length]=(headBytes .setpoint).take 64 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 64) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run64]
  have run62 : consume (wire .setpoint) 32 ((headBytes .setpoint).take 62)=⟨32,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 62++[wire .setpoint ((headBytes .setpoint).take 62).length]=(headBytes .setpoint).take 63 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 63) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run63]
  have run61 : consume (wire .setpoint) 33 ((headBytes .setpoint).take 61)=⟨33,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 61++[wire .setpoint ((headBytes .setpoint).take 61).length]=(headBytes .setpoint).take 62 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 62) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run62]
  have run60 : consume (wire .setpoint) 34 ((headBytes .setpoint).take 60)=⟨34,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 60++[wire .setpoint ((headBytes .setpoint).take 60).length]=(headBytes .setpoint).take 61 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 61) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run61]
  have run59 : consume (wire .setpoint) 35 ((headBytes .setpoint).take 59)=⟨35,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 59++[wire .setpoint ((headBytes .setpoint).take 59).length]=(headBytes .setpoint).take 60 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 60) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run60]
  have run58 : consume (wire .setpoint) 36 ((headBytes .setpoint).take 58)=⟨36,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 58++[wire .setpoint ((headBytes .setpoint).take 58).length]=(headBytes .setpoint).take 59 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 59) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run59]
  have run57 : consume (wire .setpoint) 37 ((headBytes .setpoint).take 57)=⟨37,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 57++[wire .setpoint ((headBytes .setpoint).take 57).length]=(headBytes .setpoint).take 58 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 58) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run58]
  have run56 : consume (wire .setpoint) 38 ((headBytes .setpoint).take 56)=⟨38,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 56++[wire .setpoint ((headBytes .setpoint).take 56).length]=(headBytes .setpoint).take 57 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 57) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run57]
  have run55 : consume (wire .setpoint) 39 ((headBytes .setpoint).take 55)=⟨39,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 55++[wire .setpoint ((headBytes .setpoint).take 55).length]=(headBytes .setpoint).take 56 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 56) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run56]
  have run54 : consume (wire .setpoint) 40 ((headBytes .setpoint).take 54)=⟨40,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 54++[wire .setpoint ((headBytes .setpoint).take 54).length]=(headBytes .setpoint).take 55 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 55) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run55]
  have run53 : consume (wire .setpoint) 41 ((headBytes .setpoint).take 53)=⟨41,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 53++[wire .setpoint ((headBytes .setpoint).take 53).length]=(headBytes .setpoint).take 54 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 54) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run54]
  have run52 : consume (wire .setpoint) 42 ((headBytes .setpoint).take 52)=⟨42,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 52++[wire .setpoint ((headBytes .setpoint).take 52).length]=(headBytes .setpoint).take 53 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 53) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run53]
  have run51 : consume (wire .setpoint) 43 ((headBytes .setpoint).take 51)=⟨43,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 51++[wire .setpoint ((headBytes .setpoint).take 51).length]=(headBytes .setpoint).take 52 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 52) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run52]
  have run50 : consume (wire .setpoint) 44 ((headBytes .setpoint).take 50)=⟨44,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 50++[wire .setpoint ((headBytes .setpoint).take 50).length]=(headBytes .setpoint).take 51 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 51) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run51]
  have run49 : consume (wire .setpoint) 45 ((headBytes .setpoint).take 49)=⟨45,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 49++[wire .setpoint ((headBytes .setpoint).take 49).length]=(headBytes .setpoint).take 50 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 50) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run50]
  have run48 : consume (wire .setpoint) 46 ((headBytes .setpoint).take 48)=⟨46,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 48++[wire .setpoint ((headBytes .setpoint).take 48).length]=(headBytes .setpoint).take 49 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 49) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run49]
  have run47 : consume (wire .setpoint) 47 ((headBytes .setpoint).take 47)=⟨47,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 47++[wire .setpoint ((headBytes .setpoint).take 47).length]=(headBytes .setpoint).take 48 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 48) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run48]
  have run46 : consume (wire .setpoint) 48 ((headBytes .setpoint).take 46)=⟨48,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 46++[wire .setpoint ((headBytes .setpoint).take 46).length]=(headBytes .setpoint).take 47 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 47) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run47]
  have run45 : consume (wire .setpoint) 49 ((headBytes .setpoint).take 45)=⟨49,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 45++[wire .setpoint ((headBytes .setpoint).take 45).length]=(headBytes .setpoint).take 46 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 46) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run46]
  have run44 : consume (wire .setpoint) 50 ((headBytes .setpoint).take 44)=⟨50,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 44++[wire .setpoint ((headBytes .setpoint).take 44).length]=(headBytes .setpoint).take 45 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 45) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run45]
  have run43 : consume (wire .setpoint) 51 ((headBytes .setpoint).take 43)=⟨51,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 43++[wire .setpoint ((headBytes .setpoint).take 43).length]=(headBytes .setpoint).take 44 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 44) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run44]
  have run42 : consume (wire .setpoint) 52 ((headBytes .setpoint).take 42)=⟨52,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 42++[wire .setpoint ((headBytes .setpoint).take 42).length]=(headBytes .setpoint).take 43 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 43) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run43]
  have run41 : consume (wire .setpoint) 53 ((headBytes .setpoint).take 41)=⟨53,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 41++[wire .setpoint ((headBytes .setpoint).take 41).length]=(headBytes .setpoint).take 42 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 42) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run42]
  have run40 : consume (wire .setpoint) 54 ((headBytes .setpoint).take 40)=⟨54,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 40++[wire .setpoint ((headBytes .setpoint).take 40).length]=(headBytes .setpoint).take 41 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 41) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run41]
  have run39 : consume (wire .setpoint) 55 ((headBytes .setpoint).take 39)=⟨55,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 39++[wire .setpoint ((headBytes .setpoint).take 39).length]=(headBytes .setpoint).take 40 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 40) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run40]
  have run38 : consume (wire .setpoint) 56 ((headBytes .setpoint).take 38)=⟨56,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 38++[wire .setpoint ((headBytes .setpoint).take 38).length]=(headBytes .setpoint).take 39 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 39) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run39]
  have run37 : consume (wire .setpoint) 57 ((headBytes .setpoint).take 37)=⟨57,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 37++[wire .setpoint ((headBytes .setpoint).take 37).length]=(headBytes .setpoint).take 38 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 38) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run38]
  have run36 : consume (wire .setpoint) 58 ((headBytes .setpoint).take 36)=⟨58,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 36++[wire .setpoint ((headBytes .setpoint).take 36).length]=(headBytes .setpoint).take 37 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 37) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run37]
  have run35 : consume (wire .setpoint) 59 ((headBytes .setpoint).take 35)=⟨59,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 35++[wire .setpoint ((headBytes .setpoint).take 35).length]=(headBytes .setpoint).take 36 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 36) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run36]
  have run34 : consume (wire .setpoint) 60 ((headBytes .setpoint).take 34)=⟨60,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 34++[wire .setpoint ((headBytes .setpoint).take 34).length]=(headBytes .setpoint).take 35 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 35) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run35]
  have run33 : consume (wire .setpoint) 61 ((headBytes .setpoint).take 33)=⟨61,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 33++[wire .setpoint ((headBytes .setpoint).take 33).length]=(headBytes .setpoint).take 34 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 34) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run34]
  have run32 : consume (wire .setpoint) 62 ((headBytes .setpoint).take 32)=⟨62,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 32++[wire .setpoint ((headBytes .setpoint).take 32).length]=(headBytes .setpoint).take 33 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 33) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run33]
  have run31 : consume (wire .setpoint) 63 ((headBytes .setpoint).take 31)=⟨63,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 31++[wire .setpoint ((headBytes .setpoint).take 31).length]=(headBytes .setpoint).take 32 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 32) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run32]
  have run30 : consume (wire .setpoint) 64 ((headBytes .setpoint).take 30)=⟨64,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 30++[wire .setpoint ((headBytes .setpoint).take 30).length]=(headBytes .setpoint).take 31 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 31) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run31]
  have run29 : consume (wire .setpoint) 65 ((headBytes .setpoint).take 29)=⟨65,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 29++[wire .setpoint ((headBytes .setpoint).take 29).length]=(headBytes .setpoint).take 30 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 30) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run30]
  have run28 : consume (wire .setpoint) 66 ((headBytes .setpoint).take 28)=⟨66,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 28++[wire .setpoint ((headBytes .setpoint).take 28).length]=(headBytes .setpoint).take 29 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 29) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run29]
  have run27 : consume (wire .setpoint) 67 ((headBytes .setpoint).take 27)=⟨67,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 27++[wire .setpoint ((headBytes .setpoint).take 27).length]=(headBytes .setpoint).take 28 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 28) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run28]
  have run26 : consume (wire .setpoint) 68 ((headBytes .setpoint).take 26)=⟨68,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 26++[wire .setpoint ((headBytes .setpoint).take 26).length]=(headBytes .setpoint).take 27 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 27) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run27]
  have run25 : consume (wire .setpoint) 69 ((headBytes .setpoint).take 25)=⟨69,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 25++[wire .setpoint ((headBytes .setpoint).take 25).length]=(headBytes .setpoint).take 26 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 26) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run26]
  have run24 : consume (wire .setpoint) 70 ((headBytes .setpoint).take 24)=⟨70,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 24++[wire .setpoint ((headBytes .setpoint).take 24).length]=(headBytes .setpoint).take 25 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 25) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run25]
  have run23 : consume (wire .setpoint) 71 ((headBytes .setpoint).take 23)=⟨71,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 23++[wire .setpoint ((headBytes .setpoint).take 23).length]=(headBytes .setpoint).take 24 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 24) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run24]
  have run22 : consume (wire .setpoint) 72 ((headBytes .setpoint).take 22)=⟨72,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 22++[wire .setpoint ((headBytes .setpoint).take 22).length]=(headBytes .setpoint).take 23 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 23) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run23]
  have run21 : consume (wire .setpoint) 73 ((headBytes .setpoint).take 21)=⟨73,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 21++[wire .setpoint ((headBytes .setpoint).take 21).length]=(headBytes .setpoint).take 22 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 22) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run22]
  have run20 : consume (wire .setpoint) 74 ((headBytes .setpoint).take 20)=⟨74,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 20++[wire .setpoint ((headBytes .setpoint).take 20).length]=(headBytes .setpoint).take 21 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 21) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run21]
  have run19 : consume (wire .setpoint) 75 ((headBytes .setpoint).take 19)=⟨75,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 19++[wire .setpoint ((headBytes .setpoint).take 19).length]=(headBytes .setpoint).take 20 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 20) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run20]
  have run18 : consume (wire .setpoint) 76 ((headBytes .setpoint).take 18)=⟨76,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 18++[wire .setpoint ((headBytes .setpoint).take 18).length]=(headBytes .setpoint).take 19 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 19) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run19]
  have run17 : consume (wire .setpoint) 77 ((headBytes .setpoint).take 17)=⟨77,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 17++[wire .setpoint ((headBytes .setpoint).take 17).length]=(headBytes .setpoint).take 18 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 18) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run18]
  have run16 : consume (wire .setpoint) 78 ((headBytes .setpoint).take 16)=⟨78,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 16++[wire .setpoint ((headBytes .setpoint).take 16).length]=(headBytes .setpoint).take 17 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 17) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run17]
  have run15 : consume (wire .setpoint) 79 ((headBytes .setpoint).take 15)=⟨79,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 15++[wire .setpoint ((headBytes .setpoint).take 15).length]=(headBytes .setpoint).take 16 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 16) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run16]
  have run14 : consume (wire .setpoint) 80 ((headBytes .setpoint).take 14)=⟨80,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 14++[wire .setpoint ((headBytes .setpoint).take 14).length]=(headBytes .setpoint).take 15 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 15) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run15]
  have run13 : consume (wire .setpoint) 81 ((headBytes .setpoint).take 13)=⟨81,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 13++[wire .setpoint ((headBytes .setpoint).take 13).length]=(headBytes .setpoint).take 14 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 14) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run14]
  have run12 : consume (wire .setpoint) 82 ((headBytes .setpoint).take 12)=⟨82,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 12++[wire .setpoint ((headBytes .setpoint).take 12).length]=(headBytes .setpoint).take 13 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 13) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run13]
  have run11 : consume (wire .setpoint) 83 ((headBytes .setpoint).take 11)=⟨83,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 11++[wire .setpoint ((headBytes .setpoint).take 11).length]=(headBytes .setpoint).take 12 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 12) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run12]
  have run10 : consume (wire .setpoint) 84 ((headBytes .setpoint).take 10)=⟨84,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 10++[wire .setpoint ((headBytes .setpoint).take 10).length]=(headBytes .setpoint).take 11 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 11) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run11]
  have run9 : consume (wire .setpoint) 85 ((headBytes .setpoint).take 9)=⟨85,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 9++[wire .setpoint ((headBytes .setpoint).take 9).length]=(headBytes .setpoint).take 10 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 10) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run10]
  have run8 : consume (wire .setpoint) 86 ((headBytes .setpoint).take 8)=⟨86,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 8++[wire .setpoint ((headBytes .setpoint).take 8).length]=(headBytes .setpoint).take 9 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 9) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run9]
  have run7 : consume (wire .setpoint) 87 ((headBytes .setpoint).take 7)=⟨87,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 7++[wire .setpoint ((headBytes .setpoint).take 7).length]=(headBytes .setpoint).take 8 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 8) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run8]
  have run6 : consume (wire .setpoint) 88 ((headBytes .setpoint).take 6)=⟨88,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 6++[wire .setpoint ((headBytes .setpoint).take 6).length]=(headBytes .setpoint).take 7 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 7) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run7]
  have run5 : consume (wire .setpoint) 89 ((headBytes .setpoint).take 5)=⟨89,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 5++[wire .setpoint ((headBytes .setpoint).take 5).length]=(headBytes .setpoint).take 6 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 6) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run6]
  have run4 : consume (wire .setpoint) 90 ((headBytes .setpoint).take 4)=⟨90,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 4++[wire .setpoint ((headBytes .setpoint).take 4).length]=(headBytes .setpoint).take 5 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 5) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run5]
  have run3 : consume (wire .setpoint) 91 ((headBytes .setpoint).take 3)=⟨91,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 3++[wire .setpoint ((headBytes .setpoint).take 3).length]=(headBytes .setpoint).take 4 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 4) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run4]
  have run2 : consume (wire .setpoint) 92 ((headBytes .setpoint).take 2)=⟨92,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 2++[wire .setpoint ((headBytes .setpoint).take 2).length]=(headBytes .setpoint).take 3 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 3) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run3]
  have run1 : consume (wire .setpoint) 93 ((headBytes .setpoint).take 1)=⟨93,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 1++[wire .setpoint ((headBytes .setpoint).take 1).length]=(headBytes .setpoint).take 2 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 2) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run2]
  have run0 : consume (wire .setpoint) 94 ((headBytes .setpoint).take 0)=⟨94,headBytes .setpoint,.done (head .setpoint)⟩ := by
    have nextByte : (headBytes .setpoint).take 0++[wire .setpoint ((headBytes .setpoint).take 0).length]=(headBytes .setpoint).take 1 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .setpoint).take 1) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run1]
  exact run0

theorem header_temp : consume (wire .temp) (headBytes .temp).length []=⟨(headBytes .temp).length,headBytes .temp,.done (head .temp)⟩ := by
  have run90 : consume (wire .temp) 1 ((headBytes .temp).take 90)=⟨1,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 90++[wire .temp ((headBytes .temp).take 90).length]=(headBytes .temp).take 91 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 91) 1024 1024=.done (head .temp) := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    congr 1
  have run89 : consume (wire .temp) 2 ((headBytes .temp).take 89)=⟨2,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 89++[wire .temp ((headBytes .temp).take 89).length]=(headBytes .temp).take 90 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 90) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run90]
  have run88 : consume (wire .temp) 3 ((headBytes .temp).take 88)=⟨3,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 88++[wire .temp ((headBytes .temp).take 88).length]=(headBytes .temp).take 89 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 89) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run89]
  have run87 : consume (wire .temp) 4 ((headBytes .temp).take 87)=⟨4,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 87++[wire .temp ((headBytes .temp).take 87).length]=(headBytes .temp).take 88 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 88) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run88]
  have run86 : consume (wire .temp) 5 ((headBytes .temp).take 86)=⟨5,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 86++[wire .temp ((headBytes .temp).take 86).length]=(headBytes .temp).take 87 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 87) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run87]
  have run85 : consume (wire .temp) 6 ((headBytes .temp).take 85)=⟨6,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 85++[wire .temp ((headBytes .temp).take 85).length]=(headBytes .temp).take 86 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 86) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run86]
  have run84 : consume (wire .temp) 7 ((headBytes .temp).take 84)=⟨7,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 84++[wire .temp ((headBytes .temp).take 84).length]=(headBytes .temp).take 85 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 85) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run85]
  have run83 : consume (wire .temp) 8 ((headBytes .temp).take 83)=⟨8,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 83++[wire .temp ((headBytes .temp).take 83).length]=(headBytes .temp).take 84 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 84) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run84]
  have run82 : consume (wire .temp) 9 ((headBytes .temp).take 82)=⟨9,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 82++[wire .temp ((headBytes .temp).take 82).length]=(headBytes .temp).take 83 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 83) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run83]
  have run81 : consume (wire .temp) 10 ((headBytes .temp).take 81)=⟨10,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 81++[wire .temp ((headBytes .temp).take 81).length]=(headBytes .temp).take 82 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 82) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run82]
  have run80 : consume (wire .temp) 11 ((headBytes .temp).take 80)=⟨11,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 80++[wire .temp ((headBytes .temp).take 80).length]=(headBytes .temp).take 81 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 81) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run81]
  have run79 : consume (wire .temp) 12 ((headBytes .temp).take 79)=⟨12,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 79++[wire .temp ((headBytes .temp).take 79).length]=(headBytes .temp).take 80 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 80) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run80]
  have run78 : consume (wire .temp) 13 ((headBytes .temp).take 78)=⟨13,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 78++[wire .temp ((headBytes .temp).take 78).length]=(headBytes .temp).take 79 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 79) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run79]
  have run77 : consume (wire .temp) 14 ((headBytes .temp).take 77)=⟨14,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 77++[wire .temp ((headBytes .temp).take 77).length]=(headBytes .temp).take 78 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 78) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run78]
  have run76 : consume (wire .temp) 15 ((headBytes .temp).take 76)=⟨15,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 76++[wire .temp ((headBytes .temp).take 76).length]=(headBytes .temp).take 77 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 77) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run77]
  have run75 : consume (wire .temp) 16 ((headBytes .temp).take 75)=⟨16,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 75++[wire .temp ((headBytes .temp).take 75).length]=(headBytes .temp).take 76 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 76) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run76]
  have run74 : consume (wire .temp) 17 ((headBytes .temp).take 74)=⟨17,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 74++[wire .temp ((headBytes .temp).take 74).length]=(headBytes .temp).take 75 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 75) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run75]
  have run73 : consume (wire .temp) 18 ((headBytes .temp).take 73)=⟨18,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 73++[wire .temp ((headBytes .temp).take 73).length]=(headBytes .temp).take 74 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 74) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run74]
  have run72 : consume (wire .temp) 19 ((headBytes .temp).take 72)=⟨19,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 72++[wire .temp ((headBytes .temp).take 72).length]=(headBytes .temp).take 73 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 73) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run73]
  have run71 : consume (wire .temp) 20 ((headBytes .temp).take 71)=⟨20,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 71++[wire .temp ((headBytes .temp).take 71).length]=(headBytes .temp).take 72 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 72) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run72]
  have run70 : consume (wire .temp) 21 ((headBytes .temp).take 70)=⟨21,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 70++[wire .temp ((headBytes .temp).take 70).length]=(headBytes .temp).take 71 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 71) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run71]
  have run69 : consume (wire .temp) 22 ((headBytes .temp).take 69)=⟨22,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 69++[wire .temp ((headBytes .temp).take 69).length]=(headBytes .temp).take 70 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 70) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run70]
  have run68 : consume (wire .temp) 23 ((headBytes .temp).take 68)=⟨23,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 68++[wire .temp ((headBytes .temp).take 68).length]=(headBytes .temp).take 69 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 69) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run69]
  have run67 : consume (wire .temp) 24 ((headBytes .temp).take 67)=⟨24,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 67++[wire .temp ((headBytes .temp).take 67).length]=(headBytes .temp).take 68 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 68) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run68]
  have run66 : consume (wire .temp) 25 ((headBytes .temp).take 66)=⟨25,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 66++[wire .temp ((headBytes .temp).take 66).length]=(headBytes .temp).take 67 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 67) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run67]
  have run65 : consume (wire .temp) 26 ((headBytes .temp).take 65)=⟨26,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 65++[wire .temp ((headBytes .temp).take 65).length]=(headBytes .temp).take 66 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 66) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run66]
  have run64 : consume (wire .temp) 27 ((headBytes .temp).take 64)=⟨27,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 64++[wire .temp ((headBytes .temp).take 64).length]=(headBytes .temp).take 65 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 65) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run65]
  have run63 : consume (wire .temp) 28 ((headBytes .temp).take 63)=⟨28,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 63++[wire .temp ((headBytes .temp).take 63).length]=(headBytes .temp).take 64 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 64) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run64]
  have run62 : consume (wire .temp) 29 ((headBytes .temp).take 62)=⟨29,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 62++[wire .temp ((headBytes .temp).take 62).length]=(headBytes .temp).take 63 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 63) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run63]
  have run61 : consume (wire .temp) 30 ((headBytes .temp).take 61)=⟨30,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 61++[wire .temp ((headBytes .temp).take 61).length]=(headBytes .temp).take 62 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 62) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run62]
  have run60 : consume (wire .temp) 31 ((headBytes .temp).take 60)=⟨31,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 60++[wire .temp ((headBytes .temp).take 60).length]=(headBytes .temp).take 61 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 61) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run61]
  have run59 : consume (wire .temp) 32 ((headBytes .temp).take 59)=⟨32,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 59++[wire .temp ((headBytes .temp).take 59).length]=(headBytes .temp).take 60 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 60) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run60]
  have run58 : consume (wire .temp) 33 ((headBytes .temp).take 58)=⟨33,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 58++[wire .temp ((headBytes .temp).take 58).length]=(headBytes .temp).take 59 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 59) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run59]
  have run57 : consume (wire .temp) 34 ((headBytes .temp).take 57)=⟨34,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 57++[wire .temp ((headBytes .temp).take 57).length]=(headBytes .temp).take 58 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 58) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run58]
  have run56 : consume (wire .temp) 35 ((headBytes .temp).take 56)=⟨35,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 56++[wire .temp ((headBytes .temp).take 56).length]=(headBytes .temp).take 57 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 57) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run57]
  have run55 : consume (wire .temp) 36 ((headBytes .temp).take 55)=⟨36,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 55++[wire .temp ((headBytes .temp).take 55).length]=(headBytes .temp).take 56 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 56) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run56]
  have run54 : consume (wire .temp) 37 ((headBytes .temp).take 54)=⟨37,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 54++[wire .temp ((headBytes .temp).take 54).length]=(headBytes .temp).take 55 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 55) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run55]
  have run53 : consume (wire .temp) 38 ((headBytes .temp).take 53)=⟨38,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 53++[wire .temp ((headBytes .temp).take 53).length]=(headBytes .temp).take 54 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 54) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run54]
  have run52 : consume (wire .temp) 39 ((headBytes .temp).take 52)=⟨39,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 52++[wire .temp ((headBytes .temp).take 52).length]=(headBytes .temp).take 53 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 53) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run53]
  have run51 : consume (wire .temp) 40 ((headBytes .temp).take 51)=⟨40,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 51++[wire .temp ((headBytes .temp).take 51).length]=(headBytes .temp).take 52 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 52) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run52]
  have run50 : consume (wire .temp) 41 ((headBytes .temp).take 50)=⟨41,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 50++[wire .temp ((headBytes .temp).take 50).length]=(headBytes .temp).take 51 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 51) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run51]
  have run49 : consume (wire .temp) 42 ((headBytes .temp).take 49)=⟨42,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 49++[wire .temp ((headBytes .temp).take 49).length]=(headBytes .temp).take 50 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 50) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run50]
  have run48 : consume (wire .temp) 43 ((headBytes .temp).take 48)=⟨43,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 48++[wire .temp ((headBytes .temp).take 48).length]=(headBytes .temp).take 49 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 49) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run49]
  have run47 : consume (wire .temp) 44 ((headBytes .temp).take 47)=⟨44,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 47++[wire .temp ((headBytes .temp).take 47).length]=(headBytes .temp).take 48 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 48) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run48]
  have run46 : consume (wire .temp) 45 ((headBytes .temp).take 46)=⟨45,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 46++[wire .temp ((headBytes .temp).take 46).length]=(headBytes .temp).take 47 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 47) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run47]
  have run45 : consume (wire .temp) 46 ((headBytes .temp).take 45)=⟨46,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 45++[wire .temp ((headBytes .temp).take 45).length]=(headBytes .temp).take 46 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 46) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run46]
  have run44 : consume (wire .temp) 47 ((headBytes .temp).take 44)=⟨47,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 44++[wire .temp ((headBytes .temp).take 44).length]=(headBytes .temp).take 45 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 45) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run45]
  have run43 : consume (wire .temp) 48 ((headBytes .temp).take 43)=⟨48,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 43++[wire .temp ((headBytes .temp).take 43).length]=(headBytes .temp).take 44 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 44) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run44]
  have run42 : consume (wire .temp) 49 ((headBytes .temp).take 42)=⟨49,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 42++[wire .temp ((headBytes .temp).take 42).length]=(headBytes .temp).take 43 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 43) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run43]
  have run41 : consume (wire .temp) 50 ((headBytes .temp).take 41)=⟨50,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 41++[wire .temp ((headBytes .temp).take 41).length]=(headBytes .temp).take 42 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 42) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run42]
  have run40 : consume (wire .temp) 51 ((headBytes .temp).take 40)=⟨51,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 40++[wire .temp ((headBytes .temp).take 40).length]=(headBytes .temp).take 41 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 41) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run41]
  have run39 : consume (wire .temp) 52 ((headBytes .temp).take 39)=⟨52,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 39++[wire .temp ((headBytes .temp).take 39).length]=(headBytes .temp).take 40 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 40) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run40]
  have run38 : consume (wire .temp) 53 ((headBytes .temp).take 38)=⟨53,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 38++[wire .temp ((headBytes .temp).take 38).length]=(headBytes .temp).take 39 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 39) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run39]
  have run37 : consume (wire .temp) 54 ((headBytes .temp).take 37)=⟨54,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 37++[wire .temp ((headBytes .temp).take 37).length]=(headBytes .temp).take 38 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 38) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run38]
  have run36 : consume (wire .temp) 55 ((headBytes .temp).take 36)=⟨55,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 36++[wire .temp ((headBytes .temp).take 36).length]=(headBytes .temp).take 37 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 37) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run37]
  have run35 : consume (wire .temp) 56 ((headBytes .temp).take 35)=⟨56,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 35++[wire .temp ((headBytes .temp).take 35).length]=(headBytes .temp).take 36 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 36) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run36]
  have run34 : consume (wire .temp) 57 ((headBytes .temp).take 34)=⟨57,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 34++[wire .temp ((headBytes .temp).take 34).length]=(headBytes .temp).take 35 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 35) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run35]
  have run33 : consume (wire .temp) 58 ((headBytes .temp).take 33)=⟨58,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 33++[wire .temp ((headBytes .temp).take 33).length]=(headBytes .temp).take 34 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 34) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run34]
  have run32 : consume (wire .temp) 59 ((headBytes .temp).take 32)=⟨59,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 32++[wire .temp ((headBytes .temp).take 32).length]=(headBytes .temp).take 33 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 33) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run33]
  have run31 : consume (wire .temp) 60 ((headBytes .temp).take 31)=⟨60,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 31++[wire .temp ((headBytes .temp).take 31).length]=(headBytes .temp).take 32 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 32) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run32]
  have run30 : consume (wire .temp) 61 ((headBytes .temp).take 30)=⟨61,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 30++[wire .temp ((headBytes .temp).take 30).length]=(headBytes .temp).take 31 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 31) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run31]
  have run29 : consume (wire .temp) 62 ((headBytes .temp).take 29)=⟨62,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 29++[wire .temp ((headBytes .temp).take 29).length]=(headBytes .temp).take 30 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 30) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run30]
  have run28 : consume (wire .temp) 63 ((headBytes .temp).take 28)=⟨63,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 28++[wire .temp ((headBytes .temp).take 28).length]=(headBytes .temp).take 29 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 29) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run29]
  have run27 : consume (wire .temp) 64 ((headBytes .temp).take 27)=⟨64,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 27++[wire .temp ((headBytes .temp).take 27).length]=(headBytes .temp).take 28 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 28) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run28]
  have run26 : consume (wire .temp) 65 ((headBytes .temp).take 26)=⟨65,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 26++[wire .temp ((headBytes .temp).take 26).length]=(headBytes .temp).take 27 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 27) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run27]
  have run25 : consume (wire .temp) 66 ((headBytes .temp).take 25)=⟨66,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 25++[wire .temp ((headBytes .temp).take 25).length]=(headBytes .temp).take 26 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 26) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run26]
  have run24 : consume (wire .temp) 67 ((headBytes .temp).take 24)=⟨67,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 24++[wire .temp ((headBytes .temp).take 24).length]=(headBytes .temp).take 25 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 25) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run25]
  have run23 : consume (wire .temp) 68 ((headBytes .temp).take 23)=⟨68,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 23++[wire .temp ((headBytes .temp).take 23).length]=(headBytes .temp).take 24 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 24) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run24]
  have run22 : consume (wire .temp) 69 ((headBytes .temp).take 22)=⟨69,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 22++[wire .temp ((headBytes .temp).take 22).length]=(headBytes .temp).take 23 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 23) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run23]
  have run21 : consume (wire .temp) 70 ((headBytes .temp).take 21)=⟨70,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 21++[wire .temp ((headBytes .temp).take 21).length]=(headBytes .temp).take 22 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 22) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run22]
  have run20 : consume (wire .temp) 71 ((headBytes .temp).take 20)=⟨71,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 20++[wire .temp ((headBytes .temp).take 20).length]=(headBytes .temp).take 21 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 21) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run21]
  have run19 : consume (wire .temp) 72 ((headBytes .temp).take 19)=⟨72,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 19++[wire .temp ((headBytes .temp).take 19).length]=(headBytes .temp).take 20 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 20) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run20]
  have run18 : consume (wire .temp) 73 ((headBytes .temp).take 18)=⟨73,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 18++[wire .temp ((headBytes .temp).take 18).length]=(headBytes .temp).take 19 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 19) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run19]
  have run17 : consume (wire .temp) 74 ((headBytes .temp).take 17)=⟨74,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 17++[wire .temp ((headBytes .temp).take 17).length]=(headBytes .temp).take 18 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 18) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run18]
  have run16 : consume (wire .temp) 75 ((headBytes .temp).take 16)=⟨75,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 16++[wire .temp ((headBytes .temp).take 16).length]=(headBytes .temp).take 17 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 17) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run17]
  have run15 : consume (wire .temp) 76 ((headBytes .temp).take 15)=⟨76,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 15++[wire .temp ((headBytes .temp).take 15).length]=(headBytes .temp).take 16 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 16) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run16]
  have run14 : consume (wire .temp) 77 ((headBytes .temp).take 14)=⟨77,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 14++[wire .temp ((headBytes .temp).take 14).length]=(headBytes .temp).take 15 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 15) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run15]
  have run13 : consume (wire .temp) 78 ((headBytes .temp).take 13)=⟨78,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 13++[wire .temp ((headBytes .temp).take 13).length]=(headBytes .temp).take 14 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 14) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run14]
  have run12 : consume (wire .temp) 79 ((headBytes .temp).take 12)=⟨79,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 12++[wire .temp ((headBytes .temp).take 12).length]=(headBytes .temp).take 13 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 13) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run13]
  have run11 : consume (wire .temp) 80 ((headBytes .temp).take 11)=⟨80,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 11++[wire .temp ((headBytes .temp).take 11).length]=(headBytes .temp).take 12 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 12) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run12]
  have run10 : consume (wire .temp) 81 ((headBytes .temp).take 10)=⟨81,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 10++[wire .temp ((headBytes .temp).take 10).length]=(headBytes .temp).take 11 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 11) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run11]
  have run9 : consume (wire .temp) 82 ((headBytes .temp).take 9)=⟨82,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 9++[wire .temp ((headBytes .temp).take 9).length]=(headBytes .temp).take 10 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 10) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run10]
  have run8 : consume (wire .temp) 83 ((headBytes .temp).take 8)=⟨83,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 8++[wire .temp ((headBytes .temp).take 8).length]=(headBytes .temp).take 9 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 9) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run9]
  have run7 : consume (wire .temp) 84 ((headBytes .temp).take 7)=⟨84,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 7++[wire .temp ((headBytes .temp).take 7).length]=(headBytes .temp).take 8 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 8) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run8]
  have run6 : consume (wire .temp) 85 ((headBytes .temp).take 6)=⟨85,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 6++[wire .temp ((headBytes .temp).take 6).length]=(headBytes .temp).take 7 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 7) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run7]
  have run5 : consume (wire .temp) 86 ((headBytes .temp).take 5)=⟨86,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 5++[wire .temp ((headBytes .temp).take 5).length]=(headBytes .temp).take 6 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 6) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run6]
  have run4 : consume (wire .temp) 87 ((headBytes .temp).take 4)=⟨87,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 4++[wire .temp ((headBytes .temp).take 4).length]=(headBytes .temp).take 5 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 5) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run5]
  have run3 : consume (wire .temp) 88 ((headBytes .temp).take 3)=⟨88,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 3++[wire .temp ((headBytes .temp).take 3).length]=(headBytes .temp).take 4 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 4) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run4]
  have run2 : consume (wire .temp) 89 ((headBytes .temp).take 2)=⟨89,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 2++[wire .temp ((headBytes .temp).take 2).length]=(headBytes .temp).take 3 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 3) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run3]
  have run1 : consume (wire .temp) 90 ((headBytes .temp).take 1)=⟨90,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 1++[wire .temp ((headBytes .temp).take 1).length]=(headBytes .temp).take 2 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 2) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run2]
  have run0 : consume (wire .temp) 91 ((headBytes .temp).take 0)=⟨91,headBytes .temp,.done (head .temp)⟩ := by
    have nextByte : (headBytes .temp).take 0++[wire .temp ((headBytes .temp).take 0).length]=(headBytes .temp).take 1 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .temp).take 1) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run1]
  exact run0

theorem header_mode : consume (wire .mode) (headBytes .mode).length []=⟨(headBytes .mode).length,headBytes .mode,.done (head .mode)⟩ := by
  have run89 : consume (wire .mode) 1 ((headBytes .mode).take 89)=⟨1,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 89++[wire .mode ((headBytes .mode).take 89).length]=(headBytes .mode).take 90 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 90) 1024 1024=.done (head .mode) := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    congr 1
  have run88 : consume (wire .mode) 2 ((headBytes .mode).take 88)=⟨2,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 88++[wire .mode ((headBytes .mode).take 88).length]=(headBytes .mode).take 89 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 89) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run89]
  have run87 : consume (wire .mode) 3 ((headBytes .mode).take 87)=⟨3,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 87++[wire .mode ((headBytes .mode).take 87).length]=(headBytes .mode).take 88 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 88) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run88]
  have run86 : consume (wire .mode) 4 ((headBytes .mode).take 86)=⟨4,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 86++[wire .mode ((headBytes .mode).take 86).length]=(headBytes .mode).take 87 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 87) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run87]
  have run85 : consume (wire .mode) 5 ((headBytes .mode).take 85)=⟨5,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 85++[wire .mode ((headBytes .mode).take 85).length]=(headBytes .mode).take 86 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 86) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run86]
  have run84 : consume (wire .mode) 6 ((headBytes .mode).take 84)=⟨6,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 84++[wire .mode ((headBytes .mode).take 84).length]=(headBytes .mode).take 85 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 85) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run85]
  have run83 : consume (wire .mode) 7 ((headBytes .mode).take 83)=⟨7,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 83++[wire .mode ((headBytes .mode).take 83).length]=(headBytes .mode).take 84 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 84) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run84]
  have run82 : consume (wire .mode) 8 ((headBytes .mode).take 82)=⟨8,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 82++[wire .mode ((headBytes .mode).take 82).length]=(headBytes .mode).take 83 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 83) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run83]
  have run81 : consume (wire .mode) 9 ((headBytes .mode).take 81)=⟨9,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 81++[wire .mode ((headBytes .mode).take 81).length]=(headBytes .mode).take 82 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 82) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run82]
  have run80 : consume (wire .mode) 10 ((headBytes .mode).take 80)=⟨10,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 80++[wire .mode ((headBytes .mode).take 80).length]=(headBytes .mode).take 81 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 81) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run81]
  have run79 : consume (wire .mode) 11 ((headBytes .mode).take 79)=⟨11,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 79++[wire .mode ((headBytes .mode).take 79).length]=(headBytes .mode).take 80 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 80) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run80]
  have run78 : consume (wire .mode) 12 ((headBytes .mode).take 78)=⟨12,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 78++[wire .mode ((headBytes .mode).take 78).length]=(headBytes .mode).take 79 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 79) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run79]
  have run77 : consume (wire .mode) 13 ((headBytes .mode).take 77)=⟨13,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 77++[wire .mode ((headBytes .mode).take 77).length]=(headBytes .mode).take 78 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 78) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run78]
  have run76 : consume (wire .mode) 14 ((headBytes .mode).take 76)=⟨14,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 76++[wire .mode ((headBytes .mode).take 76).length]=(headBytes .mode).take 77 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 77) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run77]
  have run75 : consume (wire .mode) 15 ((headBytes .mode).take 75)=⟨15,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 75++[wire .mode ((headBytes .mode).take 75).length]=(headBytes .mode).take 76 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 76) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run76]
  have run74 : consume (wire .mode) 16 ((headBytes .mode).take 74)=⟨16,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 74++[wire .mode ((headBytes .mode).take 74).length]=(headBytes .mode).take 75 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 75) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run75]
  have run73 : consume (wire .mode) 17 ((headBytes .mode).take 73)=⟨17,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 73++[wire .mode ((headBytes .mode).take 73).length]=(headBytes .mode).take 74 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 74) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run74]
  have run72 : consume (wire .mode) 18 ((headBytes .mode).take 72)=⟨18,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 72++[wire .mode ((headBytes .mode).take 72).length]=(headBytes .mode).take 73 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 73) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run73]
  have run71 : consume (wire .mode) 19 ((headBytes .mode).take 71)=⟨19,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 71++[wire .mode ((headBytes .mode).take 71).length]=(headBytes .mode).take 72 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 72) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run72]
  have run70 : consume (wire .mode) 20 ((headBytes .mode).take 70)=⟨20,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 70++[wire .mode ((headBytes .mode).take 70).length]=(headBytes .mode).take 71 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 71) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run71]
  have run69 : consume (wire .mode) 21 ((headBytes .mode).take 69)=⟨21,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 69++[wire .mode ((headBytes .mode).take 69).length]=(headBytes .mode).take 70 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 70) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run70]
  have run68 : consume (wire .mode) 22 ((headBytes .mode).take 68)=⟨22,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 68++[wire .mode ((headBytes .mode).take 68).length]=(headBytes .mode).take 69 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 69) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run69]
  have run67 : consume (wire .mode) 23 ((headBytes .mode).take 67)=⟨23,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 67++[wire .mode ((headBytes .mode).take 67).length]=(headBytes .mode).take 68 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 68) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run68]
  have run66 : consume (wire .mode) 24 ((headBytes .mode).take 66)=⟨24,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 66++[wire .mode ((headBytes .mode).take 66).length]=(headBytes .mode).take 67 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 67) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run67]
  have run65 : consume (wire .mode) 25 ((headBytes .mode).take 65)=⟨25,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 65++[wire .mode ((headBytes .mode).take 65).length]=(headBytes .mode).take 66 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 66) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run66]
  have run64 : consume (wire .mode) 26 ((headBytes .mode).take 64)=⟨26,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 64++[wire .mode ((headBytes .mode).take 64).length]=(headBytes .mode).take 65 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 65) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run65]
  have run63 : consume (wire .mode) 27 ((headBytes .mode).take 63)=⟨27,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 63++[wire .mode ((headBytes .mode).take 63).length]=(headBytes .mode).take 64 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 64) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run64]
  have run62 : consume (wire .mode) 28 ((headBytes .mode).take 62)=⟨28,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 62++[wire .mode ((headBytes .mode).take 62).length]=(headBytes .mode).take 63 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 63) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run63]
  have run61 : consume (wire .mode) 29 ((headBytes .mode).take 61)=⟨29,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 61++[wire .mode ((headBytes .mode).take 61).length]=(headBytes .mode).take 62 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 62) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run62]
  have run60 : consume (wire .mode) 30 ((headBytes .mode).take 60)=⟨30,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 60++[wire .mode ((headBytes .mode).take 60).length]=(headBytes .mode).take 61 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 61) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run61]
  have run59 : consume (wire .mode) 31 ((headBytes .mode).take 59)=⟨31,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 59++[wire .mode ((headBytes .mode).take 59).length]=(headBytes .mode).take 60 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 60) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run60]
  have run58 : consume (wire .mode) 32 ((headBytes .mode).take 58)=⟨32,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 58++[wire .mode ((headBytes .mode).take 58).length]=(headBytes .mode).take 59 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 59) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run59]
  have run57 : consume (wire .mode) 33 ((headBytes .mode).take 57)=⟨33,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 57++[wire .mode ((headBytes .mode).take 57).length]=(headBytes .mode).take 58 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 58) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run58]
  have run56 : consume (wire .mode) 34 ((headBytes .mode).take 56)=⟨34,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 56++[wire .mode ((headBytes .mode).take 56).length]=(headBytes .mode).take 57 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 57) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run57]
  have run55 : consume (wire .mode) 35 ((headBytes .mode).take 55)=⟨35,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 55++[wire .mode ((headBytes .mode).take 55).length]=(headBytes .mode).take 56 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 56) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run56]
  have run54 : consume (wire .mode) 36 ((headBytes .mode).take 54)=⟨36,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 54++[wire .mode ((headBytes .mode).take 54).length]=(headBytes .mode).take 55 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 55) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run55]
  have run53 : consume (wire .mode) 37 ((headBytes .mode).take 53)=⟨37,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 53++[wire .mode ((headBytes .mode).take 53).length]=(headBytes .mode).take 54 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 54) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run54]
  have run52 : consume (wire .mode) 38 ((headBytes .mode).take 52)=⟨38,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 52++[wire .mode ((headBytes .mode).take 52).length]=(headBytes .mode).take 53 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 53) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run53]
  have run51 : consume (wire .mode) 39 ((headBytes .mode).take 51)=⟨39,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 51++[wire .mode ((headBytes .mode).take 51).length]=(headBytes .mode).take 52 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 52) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run52]
  have run50 : consume (wire .mode) 40 ((headBytes .mode).take 50)=⟨40,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 50++[wire .mode ((headBytes .mode).take 50).length]=(headBytes .mode).take 51 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 51) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run51]
  have run49 : consume (wire .mode) 41 ((headBytes .mode).take 49)=⟨41,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 49++[wire .mode ((headBytes .mode).take 49).length]=(headBytes .mode).take 50 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 50) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run50]
  have run48 : consume (wire .mode) 42 ((headBytes .mode).take 48)=⟨42,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 48++[wire .mode ((headBytes .mode).take 48).length]=(headBytes .mode).take 49 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 49) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run49]
  have run47 : consume (wire .mode) 43 ((headBytes .mode).take 47)=⟨43,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 47++[wire .mode ((headBytes .mode).take 47).length]=(headBytes .mode).take 48 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 48) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run48]
  have run46 : consume (wire .mode) 44 ((headBytes .mode).take 46)=⟨44,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 46++[wire .mode ((headBytes .mode).take 46).length]=(headBytes .mode).take 47 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 47) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run47]
  have run45 : consume (wire .mode) 45 ((headBytes .mode).take 45)=⟨45,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 45++[wire .mode ((headBytes .mode).take 45).length]=(headBytes .mode).take 46 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 46) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run46]
  have run44 : consume (wire .mode) 46 ((headBytes .mode).take 44)=⟨46,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 44++[wire .mode ((headBytes .mode).take 44).length]=(headBytes .mode).take 45 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 45) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run45]
  have run43 : consume (wire .mode) 47 ((headBytes .mode).take 43)=⟨47,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 43++[wire .mode ((headBytes .mode).take 43).length]=(headBytes .mode).take 44 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 44) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run44]
  have run42 : consume (wire .mode) 48 ((headBytes .mode).take 42)=⟨48,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 42++[wire .mode ((headBytes .mode).take 42).length]=(headBytes .mode).take 43 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 43) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run43]
  have run41 : consume (wire .mode) 49 ((headBytes .mode).take 41)=⟨49,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 41++[wire .mode ((headBytes .mode).take 41).length]=(headBytes .mode).take 42 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 42) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run42]
  have run40 : consume (wire .mode) 50 ((headBytes .mode).take 40)=⟨50,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 40++[wire .mode ((headBytes .mode).take 40).length]=(headBytes .mode).take 41 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 41) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run41]
  have run39 : consume (wire .mode) 51 ((headBytes .mode).take 39)=⟨51,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 39++[wire .mode ((headBytes .mode).take 39).length]=(headBytes .mode).take 40 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 40) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run40]
  have run38 : consume (wire .mode) 52 ((headBytes .mode).take 38)=⟨52,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 38++[wire .mode ((headBytes .mode).take 38).length]=(headBytes .mode).take 39 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 39) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run39]
  have run37 : consume (wire .mode) 53 ((headBytes .mode).take 37)=⟨53,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 37++[wire .mode ((headBytes .mode).take 37).length]=(headBytes .mode).take 38 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 38) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run38]
  have run36 : consume (wire .mode) 54 ((headBytes .mode).take 36)=⟨54,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 36++[wire .mode ((headBytes .mode).take 36).length]=(headBytes .mode).take 37 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 37) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run37]
  have run35 : consume (wire .mode) 55 ((headBytes .mode).take 35)=⟨55,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 35++[wire .mode ((headBytes .mode).take 35).length]=(headBytes .mode).take 36 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 36) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run36]
  have run34 : consume (wire .mode) 56 ((headBytes .mode).take 34)=⟨56,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 34++[wire .mode ((headBytes .mode).take 34).length]=(headBytes .mode).take 35 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 35) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run35]
  have run33 : consume (wire .mode) 57 ((headBytes .mode).take 33)=⟨57,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 33++[wire .mode ((headBytes .mode).take 33).length]=(headBytes .mode).take 34 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 34) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run34]
  have run32 : consume (wire .mode) 58 ((headBytes .mode).take 32)=⟨58,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 32++[wire .mode ((headBytes .mode).take 32).length]=(headBytes .mode).take 33 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 33) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run33]
  have run31 : consume (wire .mode) 59 ((headBytes .mode).take 31)=⟨59,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 31++[wire .mode ((headBytes .mode).take 31).length]=(headBytes .mode).take 32 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 32) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run32]
  have run30 : consume (wire .mode) 60 ((headBytes .mode).take 30)=⟨60,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 30++[wire .mode ((headBytes .mode).take 30).length]=(headBytes .mode).take 31 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 31) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run31]
  have run29 : consume (wire .mode) 61 ((headBytes .mode).take 29)=⟨61,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 29++[wire .mode ((headBytes .mode).take 29).length]=(headBytes .mode).take 30 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 30) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run30]
  have run28 : consume (wire .mode) 62 ((headBytes .mode).take 28)=⟨62,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 28++[wire .mode ((headBytes .mode).take 28).length]=(headBytes .mode).take 29 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 29) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run29]
  have run27 : consume (wire .mode) 63 ((headBytes .mode).take 27)=⟨63,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 27++[wire .mode ((headBytes .mode).take 27).length]=(headBytes .mode).take 28 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 28) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run28]
  have run26 : consume (wire .mode) 64 ((headBytes .mode).take 26)=⟨64,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 26++[wire .mode ((headBytes .mode).take 26).length]=(headBytes .mode).take 27 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 27) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run27]
  have run25 : consume (wire .mode) 65 ((headBytes .mode).take 25)=⟨65,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 25++[wire .mode ((headBytes .mode).take 25).length]=(headBytes .mode).take 26 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 26) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run26]
  have run24 : consume (wire .mode) 66 ((headBytes .mode).take 24)=⟨66,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 24++[wire .mode ((headBytes .mode).take 24).length]=(headBytes .mode).take 25 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 25) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run25]
  have run23 : consume (wire .mode) 67 ((headBytes .mode).take 23)=⟨67,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 23++[wire .mode ((headBytes .mode).take 23).length]=(headBytes .mode).take 24 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 24) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run24]
  have run22 : consume (wire .mode) 68 ((headBytes .mode).take 22)=⟨68,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 22++[wire .mode ((headBytes .mode).take 22).length]=(headBytes .mode).take 23 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 23) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run23]
  have run21 : consume (wire .mode) 69 ((headBytes .mode).take 21)=⟨69,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 21++[wire .mode ((headBytes .mode).take 21).length]=(headBytes .mode).take 22 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 22) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run22]
  have run20 : consume (wire .mode) 70 ((headBytes .mode).take 20)=⟨70,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 20++[wire .mode ((headBytes .mode).take 20).length]=(headBytes .mode).take 21 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 21) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run21]
  have run19 : consume (wire .mode) 71 ((headBytes .mode).take 19)=⟨71,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 19++[wire .mode ((headBytes .mode).take 19).length]=(headBytes .mode).take 20 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 20) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run20]
  have run18 : consume (wire .mode) 72 ((headBytes .mode).take 18)=⟨72,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 18++[wire .mode ((headBytes .mode).take 18).length]=(headBytes .mode).take 19 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 19) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run19]
  have run17 : consume (wire .mode) 73 ((headBytes .mode).take 17)=⟨73,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 17++[wire .mode ((headBytes .mode).take 17).length]=(headBytes .mode).take 18 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 18) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run18]
  have run16 : consume (wire .mode) 74 ((headBytes .mode).take 16)=⟨74,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 16++[wire .mode ((headBytes .mode).take 16).length]=(headBytes .mode).take 17 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 17) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run17]
  have run15 : consume (wire .mode) 75 ((headBytes .mode).take 15)=⟨75,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 15++[wire .mode ((headBytes .mode).take 15).length]=(headBytes .mode).take 16 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 16) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run16]
  have run14 : consume (wire .mode) 76 ((headBytes .mode).take 14)=⟨76,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 14++[wire .mode ((headBytes .mode).take 14).length]=(headBytes .mode).take 15 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 15) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run15]
  have run13 : consume (wire .mode) 77 ((headBytes .mode).take 13)=⟨77,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 13++[wire .mode ((headBytes .mode).take 13).length]=(headBytes .mode).take 14 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 14) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run14]
  have run12 : consume (wire .mode) 78 ((headBytes .mode).take 12)=⟨78,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 12++[wire .mode ((headBytes .mode).take 12).length]=(headBytes .mode).take 13 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 13) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run13]
  have run11 : consume (wire .mode) 79 ((headBytes .mode).take 11)=⟨79,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 11++[wire .mode ((headBytes .mode).take 11).length]=(headBytes .mode).take 12 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 12) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run12]
  have run10 : consume (wire .mode) 80 ((headBytes .mode).take 10)=⟨80,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 10++[wire .mode ((headBytes .mode).take 10).length]=(headBytes .mode).take 11 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 11) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run11]
  have run9 : consume (wire .mode) 81 ((headBytes .mode).take 9)=⟨81,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 9++[wire .mode ((headBytes .mode).take 9).length]=(headBytes .mode).take 10 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 10) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run10]
  have run8 : consume (wire .mode) 82 ((headBytes .mode).take 8)=⟨82,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 8++[wire .mode ((headBytes .mode).take 8).length]=(headBytes .mode).take 9 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 9) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run9]
  have run7 : consume (wire .mode) 83 ((headBytes .mode).take 7)=⟨83,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 7++[wire .mode ((headBytes .mode).take 7).length]=(headBytes .mode).take 8 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 8) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run8]
  have run6 : consume (wire .mode) 84 ((headBytes .mode).take 6)=⟨84,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 6++[wire .mode ((headBytes .mode).take 6).length]=(headBytes .mode).take 7 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 7) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run7]
  have run5 : consume (wire .mode) 85 ((headBytes .mode).take 5)=⟨85,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 5++[wire .mode ((headBytes .mode).take 5).length]=(headBytes .mode).take 6 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 6) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run6]
  have run4 : consume (wire .mode) 86 ((headBytes .mode).take 4)=⟨86,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 4++[wire .mode ((headBytes .mode).take 4).length]=(headBytes .mode).take 5 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 5) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run5]
  have run3 : consume (wire .mode) 87 ((headBytes .mode).take 3)=⟨87,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 3++[wire .mode ((headBytes .mode).take 3).length]=(headBytes .mode).take 4 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 4) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run4]
  have run2 : consume (wire .mode) 88 ((headBytes .mode).take 2)=⟨88,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 2++[wire .mode ((headBytes .mode).take 2).length]=(headBytes .mode).take 3 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 3) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run3]
  have run1 : consume (wire .mode) 89 ((headBytes .mode).take 1)=⟨89,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 1++[wire .mode ((headBytes .mode).take 1).length]=(headBytes .mode).take 2 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 2) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run2]
  have run0 : consume (wire .mode) 90 ((headBytes .mode).take 0)=⟨90,headBytes .mode,.done (head .mode)⟩ := by
    have nextByte : (headBytes .mode).take 0++[wire .mode ((headBytes .mode).take 0).length]=(headBytes .mode).take 1 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .mode).take 1) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run1]
  exact run0

theorem header_range : consume (wire .range) (headBytes .range).length []=⟨(headBytes .range).length,headBytes .range,.done (head .range)⟩ := by
  have run93 : consume (wire .range) 1 ((headBytes .range).take 93)=⟨1,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 93++[wire .range ((headBytes .range).take 93).length]=(headBytes .range).take 94 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 94) 1024 1024=.done (head .range) := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    congr 1
  have run92 : consume (wire .range) 2 ((headBytes .range).take 92)=⟨2,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 92++[wire .range ((headBytes .range).take 92).length]=(headBytes .range).take 93 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 93) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run93]
  have run91 : consume (wire .range) 3 ((headBytes .range).take 91)=⟨3,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 91++[wire .range ((headBytes .range).take 91).length]=(headBytes .range).take 92 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 92) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run92]
  have run90 : consume (wire .range) 4 ((headBytes .range).take 90)=⟨4,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 90++[wire .range ((headBytes .range).take 90).length]=(headBytes .range).take 91 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 91) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run91]
  have run89 : consume (wire .range) 5 ((headBytes .range).take 89)=⟨5,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 89++[wire .range ((headBytes .range).take 89).length]=(headBytes .range).take 90 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 90) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run90]
  have run88 : consume (wire .range) 6 ((headBytes .range).take 88)=⟨6,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 88++[wire .range ((headBytes .range).take 88).length]=(headBytes .range).take 89 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 89) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run89]
  have run87 : consume (wire .range) 7 ((headBytes .range).take 87)=⟨7,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 87++[wire .range ((headBytes .range).take 87).length]=(headBytes .range).take 88 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 88) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run88]
  have run86 : consume (wire .range) 8 ((headBytes .range).take 86)=⟨8,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 86++[wire .range ((headBytes .range).take 86).length]=(headBytes .range).take 87 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 87) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run87]
  have run85 : consume (wire .range) 9 ((headBytes .range).take 85)=⟨9,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 85++[wire .range ((headBytes .range).take 85).length]=(headBytes .range).take 86 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 86) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run86]
  have run84 : consume (wire .range) 10 ((headBytes .range).take 84)=⟨10,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 84++[wire .range ((headBytes .range).take 84).length]=(headBytes .range).take 85 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 85) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run85]
  have run83 : consume (wire .range) 11 ((headBytes .range).take 83)=⟨11,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 83++[wire .range ((headBytes .range).take 83).length]=(headBytes .range).take 84 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 84) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run84]
  have run82 : consume (wire .range) 12 ((headBytes .range).take 82)=⟨12,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 82++[wire .range ((headBytes .range).take 82).length]=(headBytes .range).take 83 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 83) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run83]
  have run81 : consume (wire .range) 13 ((headBytes .range).take 81)=⟨13,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 81++[wire .range ((headBytes .range).take 81).length]=(headBytes .range).take 82 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 82) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run82]
  have run80 : consume (wire .range) 14 ((headBytes .range).take 80)=⟨14,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 80++[wire .range ((headBytes .range).take 80).length]=(headBytes .range).take 81 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 81) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run81]
  have run79 : consume (wire .range) 15 ((headBytes .range).take 79)=⟨15,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 79++[wire .range ((headBytes .range).take 79).length]=(headBytes .range).take 80 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 80) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run80]
  have run78 : consume (wire .range) 16 ((headBytes .range).take 78)=⟨16,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 78++[wire .range ((headBytes .range).take 78).length]=(headBytes .range).take 79 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 79) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run79]
  have run77 : consume (wire .range) 17 ((headBytes .range).take 77)=⟨17,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 77++[wire .range ((headBytes .range).take 77).length]=(headBytes .range).take 78 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 78) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run78]
  have run76 : consume (wire .range) 18 ((headBytes .range).take 76)=⟨18,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 76++[wire .range ((headBytes .range).take 76).length]=(headBytes .range).take 77 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 77) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run77]
  have run75 : consume (wire .range) 19 ((headBytes .range).take 75)=⟨19,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 75++[wire .range ((headBytes .range).take 75).length]=(headBytes .range).take 76 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 76) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run76]
  have run74 : consume (wire .range) 20 ((headBytes .range).take 74)=⟨20,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 74++[wire .range ((headBytes .range).take 74).length]=(headBytes .range).take 75 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 75) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run75]
  have run73 : consume (wire .range) 21 ((headBytes .range).take 73)=⟨21,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 73++[wire .range ((headBytes .range).take 73).length]=(headBytes .range).take 74 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 74) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run74]
  have run72 : consume (wire .range) 22 ((headBytes .range).take 72)=⟨22,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 72++[wire .range ((headBytes .range).take 72).length]=(headBytes .range).take 73 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 73) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run73]
  have run71 : consume (wire .range) 23 ((headBytes .range).take 71)=⟨23,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 71++[wire .range ((headBytes .range).take 71).length]=(headBytes .range).take 72 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 72) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run72]
  have run70 : consume (wire .range) 24 ((headBytes .range).take 70)=⟨24,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 70++[wire .range ((headBytes .range).take 70).length]=(headBytes .range).take 71 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 71) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run71]
  have run69 : consume (wire .range) 25 ((headBytes .range).take 69)=⟨25,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 69++[wire .range ((headBytes .range).take 69).length]=(headBytes .range).take 70 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 70) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run70]
  have run68 : consume (wire .range) 26 ((headBytes .range).take 68)=⟨26,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 68++[wire .range ((headBytes .range).take 68).length]=(headBytes .range).take 69 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 69) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run69]
  have run67 : consume (wire .range) 27 ((headBytes .range).take 67)=⟨27,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 67++[wire .range ((headBytes .range).take 67).length]=(headBytes .range).take 68 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 68) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run68]
  have run66 : consume (wire .range) 28 ((headBytes .range).take 66)=⟨28,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 66++[wire .range ((headBytes .range).take 66).length]=(headBytes .range).take 67 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 67) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run67]
  have run65 : consume (wire .range) 29 ((headBytes .range).take 65)=⟨29,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 65++[wire .range ((headBytes .range).take 65).length]=(headBytes .range).take 66 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 66) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run66]
  have run64 : consume (wire .range) 30 ((headBytes .range).take 64)=⟨30,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 64++[wire .range ((headBytes .range).take 64).length]=(headBytes .range).take 65 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 65) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run65]
  have run63 : consume (wire .range) 31 ((headBytes .range).take 63)=⟨31,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 63++[wire .range ((headBytes .range).take 63).length]=(headBytes .range).take 64 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 64) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run64]
  have run62 : consume (wire .range) 32 ((headBytes .range).take 62)=⟨32,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 62++[wire .range ((headBytes .range).take 62).length]=(headBytes .range).take 63 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 63) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run63]
  have run61 : consume (wire .range) 33 ((headBytes .range).take 61)=⟨33,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 61++[wire .range ((headBytes .range).take 61).length]=(headBytes .range).take 62 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 62) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run62]
  have run60 : consume (wire .range) 34 ((headBytes .range).take 60)=⟨34,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 60++[wire .range ((headBytes .range).take 60).length]=(headBytes .range).take 61 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 61) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run61]
  have run59 : consume (wire .range) 35 ((headBytes .range).take 59)=⟨35,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 59++[wire .range ((headBytes .range).take 59).length]=(headBytes .range).take 60 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 60) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run60]
  have run58 : consume (wire .range) 36 ((headBytes .range).take 58)=⟨36,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 58++[wire .range ((headBytes .range).take 58).length]=(headBytes .range).take 59 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 59) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run59]
  have run57 : consume (wire .range) 37 ((headBytes .range).take 57)=⟨37,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 57++[wire .range ((headBytes .range).take 57).length]=(headBytes .range).take 58 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 58) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run58]
  have run56 : consume (wire .range) 38 ((headBytes .range).take 56)=⟨38,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 56++[wire .range ((headBytes .range).take 56).length]=(headBytes .range).take 57 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 57) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run57]
  have run55 : consume (wire .range) 39 ((headBytes .range).take 55)=⟨39,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 55++[wire .range ((headBytes .range).take 55).length]=(headBytes .range).take 56 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 56) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run56]
  have run54 : consume (wire .range) 40 ((headBytes .range).take 54)=⟨40,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 54++[wire .range ((headBytes .range).take 54).length]=(headBytes .range).take 55 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 55) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run55]
  have run53 : consume (wire .range) 41 ((headBytes .range).take 53)=⟨41,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 53++[wire .range ((headBytes .range).take 53).length]=(headBytes .range).take 54 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 54) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run54]
  have run52 : consume (wire .range) 42 ((headBytes .range).take 52)=⟨42,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 52++[wire .range ((headBytes .range).take 52).length]=(headBytes .range).take 53 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 53) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run53]
  have run51 : consume (wire .range) 43 ((headBytes .range).take 51)=⟨43,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 51++[wire .range ((headBytes .range).take 51).length]=(headBytes .range).take 52 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 52) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run52]
  have run50 : consume (wire .range) 44 ((headBytes .range).take 50)=⟨44,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 50++[wire .range ((headBytes .range).take 50).length]=(headBytes .range).take 51 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 51) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run51]
  have run49 : consume (wire .range) 45 ((headBytes .range).take 49)=⟨45,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 49++[wire .range ((headBytes .range).take 49).length]=(headBytes .range).take 50 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 50) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run50]
  have run48 : consume (wire .range) 46 ((headBytes .range).take 48)=⟨46,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 48++[wire .range ((headBytes .range).take 48).length]=(headBytes .range).take 49 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 49) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run49]
  have run47 : consume (wire .range) 47 ((headBytes .range).take 47)=⟨47,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 47++[wire .range ((headBytes .range).take 47).length]=(headBytes .range).take 48 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 48) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run48]
  have run46 : consume (wire .range) 48 ((headBytes .range).take 46)=⟨48,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 46++[wire .range ((headBytes .range).take 46).length]=(headBytes .range).take 47 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 47) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run47]
  have run45 : consume (wire .range) 49 ((headBytes .range).take 45)=⟨49,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 45++[wire .range ((headBytes .range).take 45).length]=(headBytes .range).take 46 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 46) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run46]
  have run44 : consume (wire .range) 50 ((headBytes .range).take 44)=⟨50,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 44++[wire .range ((headBytes .range).take 44).length]=(headBytes .range).take 45 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 45) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run45]
  have run43 : consume (wire .range) 51 ((headBytes .range).take 43)=⟨51,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 43++[wire .range ((headBytes .range).take 43).length]=(headBytes .range).take 44 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 44) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run44]
  have run42 : consume (wire .range) 52 ((headBytes .range).take 42)=⟨52,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 42++[wire .range ((headBytes .range).take 42).length]=(headBytes .range).take 43 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 43) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run43]
  have run41 : consume (wire .range) 53 ((headBytes .range).take 41)=⟨53,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 41++[wire .range ((headBytes .range).take 41).length]=(headBytes .range).take 42 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 42) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run42]
  have run40 : consume (wire .range) 54 ((headBytes .range).take 40)=⟨54,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 40++[wire .range ((headBytes .range).take 40).length]=(headBytes .range).take 41 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 41) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run41]
  have run39 : consume (wire .range) 55 ((headBytes .range).take 39)=⟨55,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 39++[wire .range ((headBytes .range).take 39).length]=(headBytes .range).take 40 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 40) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run40]
  have run38 : consume (wire .range) 56 ((headBytes .range).take 38)=⟨56,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 38++[wire .range ((headBytes .range).take 38).length]=(headBytes .range).take 39 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 39) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run39]
  have run37 : consume (wire .range) 57 ((headBytes .range).take 37)=⟨57,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 37++[wire .range ((headBytes .range).take 37).length]=(headBytes .range).take 38 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 38) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run38]
  have run36 : consume (wire .range) 58 ((headBytes .range).take 36)=⟨58,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 36++[wire .range ((headBytes .range).take 36).length]=(headBytes .range).take 37 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 37) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run37]
  have run35 : consume (wire .range) 59 ((headBytes .range).take 35)=⟨59,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 35++[wire .range ((headBytes .range).take 35).length]=(headBytes .range).take 36 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 36) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run36]
  have run34 : consume (wire .range) 60 ((headBytes .range).take 34)=⟨60,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 34++[wire .range ((headBytes .range).take 34).length]=(headBytes .range).take 35 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 35) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run35]
  have run33 : consume (wire .range) 61 ((headBytes .range).take 33)=⟨61,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 33++[wire .range ((headBytes .range).take 33).length]=(headBytes .range).take 34 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 34) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run34]
  have run32 : consume (wire .range) 62 ((headBytes .range).take 32)=⟨62,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 32++[wire .range ((headBytes .range).take 32).length]=(headBytes .range).take 33 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 33) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run33]
  have run31 : consume (wire .range) 63 ((headBytes .range).take 31)=⟨63,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 31++[wire .range ((headBytes .range).take 31).length]=(headBytes .range).take 32 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 32) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run32]
  have run30 : consume (wire .range) 64 ((headBytes .range).take 30)=⟨64,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 30++[wire .range ((headBytes .range).take 30).length]=(headBytes .range).take 31 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 31) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run31]
  have run29 : consume (wire .range) 65 ((headBytes .range).take 29)=⟨65,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 29++[wire .range ((headBytes .range).take 29).length]=(headBytes .range).take 30 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 30) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run30]
  have run28 : consume (wire .range) 66 ((headBytes .range).take 28)=⟨66,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 28++[wire .range ((headBytes .range).take 28).length]=(headBytes .range).take 29 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 29) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run29]
  have run27 : consume (wire .range) 67 ((headBytes .range).take 27)=⟨67,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 27++[wire .range ((headBytes .range).take 27).length]=(headBytes .range).take 28 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 28) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run28]
  have run26 : consume (wire .range) 68 ((headBytes .range).take 26)=⟨68,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 26++[wire .range ((headBytes .range).take 26).length]=(headBytes .range).take 27 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 27) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run27]
  have run25 : consume (wire .range) 69 ((headBytes .range).take 25)=⟨69,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 25++[wire .range ((headBytes .range).take 25).length]=(headBytes .range).take 26 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 26) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run26]
  have run24 : consume (wire .range) 70 ((headBytes .range).take 24)=⟨70,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 24++[wire .range ((headBytes .range).take 24).length]=(headBytes .range).take 25 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 25) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run25]
  have run23 : consume (wire .range) 71 ((headBytes .range).take 23)=⟨71,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 23++[wire .range ((headBytes .range).take 23).length]=(headBytes .range).take 24 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 24) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run24]
  have run22 : consume (wire .range) 72 ((headBytes .range).take 22)=⟨72,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 22++[wire .range ((headBytes .range).take 22).length]=(headBytes .range).take 23 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 23) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run23]
  have run21 : consume (wire .range) 73 ((headBytes .range).take 21)=⟨73,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 21++[wire .range ((headBytes .range).take 21).length]=(headBytes .range).take 22 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 22) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run22]
  have run20 : consume (wire .range) 74 ((headBytes .range).take 20)=⟨74,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 20++[wire .range ((headBytes .range).take 20).length]=(headBytes .range).take 21 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 21) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run21]
  have run19 : consume (wire .range) 75 ((headBytes .range).take 19)=⟨75,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 19++[wire .range ((headBytes .range).take 19).length]=(headBytes .range).take 20 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 20) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run20]
  have run18 : consume (wire .range) 76 ((headBytes .range).take 18)=⟨76,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 18++[wire .range ((headBytes .range).take 18).length]=(headBytes .range).take 19 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 19) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run19]
  have run17 : consume (wire .range) 77 ((headBytes .range).take 17)=⟨77,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 17++[wire .range ((headBytes .range).take 17).length]=(headBytes .range).take 18 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 18) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run18]
  have run16 : consume (wire .range) 78 ((headBytes .range).take 16)=⟨78,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 16++[wire .range ((headBytes .range).take 16).length]=(headBytes .range).take 17 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 17) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run17]
  have run15 : consume (wire .range) 79 ((headBytes .range).take 15)=⟨79,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 15++[wire .range ((headBytes .range).take 15).length]=(headBytes .range).take 16 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 16) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run16]
  have run14 : consume (wire .range) 80 ((headBytes .range).take 14)=⟨80,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 14++[wire .range ((headBytes .range).take 14).length]=(headBytes .range).take 15 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 15) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run15]
  have run13 : consume (wire .range) 81 ((headBytes .range).take 13)=⟨81,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 13++[wire .range ((headBytes .range).take 13).length]=(headBytes .range).take 14 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 14) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run14]
  have run12 : consume (wire .range) 82 ((headBytes .range).take 12)=⟨82,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 12++[wire .range ((headBytes .range).take 12).length]=(headBytes .range).take 13 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 13) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run13]
  have run11 : consume (wire .range) 83 ((headBytes .range).take 11)=⟨83,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 11++[wire .range ((headBytes .range).take 11).length]=(headBytes .range).take 12 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 12) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run12]
  have run10 : consume (wire .range) 84 ((headBytes .range).take 10)=⟨84,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 10++[wire .range ((headBytes .range).take 10).length]=(headBytes .range).take 11 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 11) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run11]
  have run9 : consume (wire .range) 85 ((headBytes .range).take 9)=⟨85,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 9++[wire .range ((headBytes .range).take 9).length]=(headBytes .range).take 10 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 10) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run10]
  have run8 : consume (wire .range) 86 ((headBytes .range).take 8)=⟨86,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 8++[wire .range ((headBytes .range).take 8).length]=(headBytes .range).take 9 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 9) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run9]
  have run7 : consume (wire .range) 87 ((headBytes .range).take 7)=⟨87,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 7++[wire .range ((headBytes .range).take 7).length]=(headBytes .range).take 8 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 8) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run8]
  have run6 : consume (wire .range) 88 ((headBytes .range).take 6)=⟨88,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 6++[wire .range ((headBytes .range).take 6).length]=(headBytes .range).take 7 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 7) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run7]
  have run5 : consume (wire .range) 89 ((headBytes .range).take 5)=⟨89,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 5++[wire .range ((headBytes .range).take 5).length]=(headBytes .range).take 6 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 6) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run6]
  have run4 : consume (wire .range) 90 ((headBytes .range).take 4)=⟨90,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 4++[wire .range ((headBytes .range).take 4).length]=(headBytes .range).take 5 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 5) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run5]
  have run3 : consume (wire .range) 91 ((headBytes .range).take 3)=⟨91,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 3++[wire .range ((headBytes .range).take 3).length]=(headBytes .range).take 4 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 4) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run4]
  have run2 : consume (wire .range) 92 ((headBytes .range).take 2)=⟨92,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 2++[wire .range ((headBytes .range).take 2).length]=(headBytes .range).take 3 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 3) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run3]
  have run1 : consume (wire .range) 93 ((headBytes .range).take 1)=⟨93,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 1++[wire .range ((headBytes .range).take 1).length]=(headBytes .range).take 2 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 2) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run2]
  have run0 : consume (wire .range) 94 ((headBytes .range).take 0)=⟨94,headBytes .range,.done (head .range)⟩ := by
    have nextByte : (headBytes .range).take 0++[wire .range ((headBytes .range).take 0).length]=(headBytes .range).take 1 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .range).take 1) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run1]
  exact run0

theorem header_noAuth : consume (wire .noAuth) (headBytes .noAuth).length []=⟨(headBytes .noAuth).length,headBytes .noAuth,.done (head .noAuth)⟩ := by
  have run59 : consume (wire .noAuth) 1 ((headBytes .noAuth).take 59)=⟨1,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 59++[wire .noAuth ((headBytes .noAuth).take 59).length]=(headBytes .noAuth).take 60 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 60) 1024 1024=.done (head .noAuth) := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    congr 1
  have run58 : consume (wire .noAuth) 2 ((headBytes .noAuth).take 58)=⟨2,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 58++[wire .noAuth ((headBytes .noAuth).take 58).length]=(headBytes .noAuth).take 59 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 59) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run59]
  have run57 : consume (wire .noAuth) 3 ((headBytes .noAuth).take 57)=⟨3,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 57++[wire .noAuth ((headBytes .noAuth).take 57).length]=(headBytes .noAuth).take 58 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 58) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run58]
  have run56 : consume (wire .noAuth) 4 ((headBytes .noAuth).take 56)=⟨4,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 56++[wire .noAuth ((headBytes .noAuth).take 56).length]=(headBytes .noAuth).take 57 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 57) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run57]
  have run55 : consume (wire .noAuth) 5 ((headBytes .noAuth).take 55)=⟨5,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 55++[wire .noAuth ((headBytes .noAuth).take 55).length]=(headBytes .noAuth).take 56 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 56) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run56]
  have run54 : consume (wire .noAuth) 6 ((headBytes .noAuth).take 54)=⟨6,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 54++[wire .noAuth ((headBytes .noAuth).take 54).length]=(headBytes .noAuth).take 55 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 55) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run55]
  have run53 : consume (wire .noAuth) 7 ((headBytes .noAuth).take 53)=⟨7,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 53++[wire .noAuth ((headBytes .noAuth).take 53).length]=(headBytes .noAuth).take 54 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 54) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run54]
  have run52 : consume (wire .noAuth) 8 ((headBytes .noAuth).take 52)=⟨8,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 52++[wire .noAuth ((headBytes .noAuth).take 52).length]=(headBytes .noAuth).take 53 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 53) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run53]
  have run51 : consume (wire .noAuth) 9 ((headBytes .noAuth).take 51)=⟨9,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 51++[wire .noAuth ((headBytes .noAuth).take 51).length]=(headBytes .noAuth).take 52 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 52) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run52]
  have run50 : consume (wire .noAuth) 10 ((headBytes .noAuth).take 50)=⟨10,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 50++[wire .noAuth ((headBytes .noAuth).take 50).length]=(headBytes .noAuth).take 51 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 51) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run51]
  have run49 : consume (wire .noAuth) 11 ((headBytes .noAuth).take 49)=⟨11,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 49++[wire .noAuth ((headBytes .noAuth).take 49).length]=(headBytes .noAuth).take 50 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 50) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run50]
  have run48 : consume (wire .noAuth) 12 ((headBytes .noAuth).take 48)=⟨12,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 48++[wire .noAuth ((headBytes .noAuth).take 48).length]=(headBytes .noAuth).take 49 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 49) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run49]
  have run47 : consume (wire .noAuth) 13 ((headBytes .noAuth).take 47)=⟨13,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 47++[wire .noAuth ((headBytes .noAuth).take 47).length]=(headBytes .noAuth).take 48 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 48) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run48]
  have run46 : consume (wire .noAuth) 14 ((headBytes .noAuth).take 46)=⟨14,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 46++[wire .noAuth ((headBytes .noAuth).take 46).length]=(headBytes .noAuth).take 47 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 47) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run47]
  have run45 : consume (wire .noAuth) 15 ((headBytes .noAuth).take 45)=⟨15,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 45++[wire .noAuth ((headBytes .noAuth).take 45).length]=(headBytes .noAuth).take 46 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 46) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run46]
  have run44 : consume (wire .noAuth) 16 ((headBytes .noAuth).take 44)=⟨16,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 44++[wire .noAuth ((headBytes .noAuth).take 44).length]=(headBytes .noAuth).take 45 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 45) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run45]
  have run43 : consume (wire .noAuth) 17 ((headBytes .noAuth).take 43)=⟨17,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 43++[wire .noAuth ((headBytes .noAuth).take 43).length]=(headBytes .noAuth).take 44 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 44) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run44]
  have run42 : consume (wire .noAuth) 18 ((headBytes .noAuth).take 42)=⟨18,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 42++[wire .noAuth ((headBytes .noAuth).take 42).length]=(headBytes .noAuth).take 43 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 43) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run43]
  have run41 : consume (wire .noAuth) 19 ((headBytes .noAuth).take 41)=⟨19,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 41++[wire .noAuth ((headBytes .noAuth).take 41).length]=(headBytes .noAuth).take 42 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 42) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run42]
  have run40 : consume (wire .noAuth) 20 ((headBytes .noAuth).take 40)=⟨20,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 40++[wire .noAuth ((headBytes .noAuth).take 40).length]=(headBytes .noAuth).take 41 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 41) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run41]
  have run39 : consume (wire .noAuth) 21 ((headBytes .noAuth).take 39)=⟨21,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 39++[wire .noAuth ((headBytes .noAuth).take 39).length]=(headBytes .noAuth).take 40 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 40) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run40]
  have run38 : consume (wire .noAuth) 22 ((headBytes .noAuth).take 38)=⟨22,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 38++[wire .noAuth ((headBytes .noAuth).take 38).length]=(headBytes .noAuth).take 39 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 39) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run39]
  have run37 : consume (wire .noAuth) 23 ((headBytes .noAuth).take 37)=⟨23,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 37++[wire .noAuth ((headBytes .noAuth).take 37).length]=(headBytes .noAuth).take 38 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 38) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run38]
  have run36 : consume (wire .noAuth) 24 ((headBytes .noAuth).take 36)=⟨24,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 36++[wire .noAuth ((headBytes .noAuth).take 36).length]=(headBytes .noAuth).take 37 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 37) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run37]
  have run35 : consume (wire .noAuth) 25 ((headBytes .noAuth).take 35)=⟨25,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 35++[wire .noAuth ((headBytes .noAuth).take 35).length]=(headBytes .noAuth).take 36 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 36) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run36]
  have run34 : consume (wire .noAuth) 26 ((headBytes .noAuth).take 34)=⟨26,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 34++[wire .noAuth ((headBytes .noAuth).take 34).length]=(headBytes .noAuth).take 35 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 35) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run35]
  have run33 : consume (wire .noAuth) 27 ((headBytes .noAuth).take 33)=⟨27,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 33++[wire .noAuth ((headBytes .noAuth).take 33).length]=(headBytes .noAuth).take 34 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 34) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run34]
  have run32 : consume (wire .noAuth) 28 ((headBytes .noAuth).take 32)=⟨28,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 32++[wire .noAuth ((headBytes .noAuth).take 32).length]=(headBytes .noAuth).take 33 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 33) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run33]
  have run31 : consume (wire .noAuth) 29 ((headBytes .noAuth).take 31)=⟨29,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 31++[wire .noAuth ((headBytes .noAuth).take 31).length]=(headBytes .noAuth).take 32 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 32) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run32]
  have run30 : consume (wire .noAuth) 30 ((headBytes .noAuth).take 30)=⟨30,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 30++[wire .noAuth ((headBytes .noAuth).take 30).length]=(headBytes .noAuth).take 31 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 31) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run31]
  have run29 : consume (wire .noAuth) 31 ((headBytes .noAuth).take 29)=⟨31,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 29++[wire .noAuth ((headBytes .noAuth).take 29).length]=(headBytes .noAuth).take 30 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 30) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run30]
  have run28 : consume (wire .noAuth) 32 ((headBytes .noAuth).take 28)=⟨32,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 28++[wire .noAuth ((headBytes .noAuth).take 28).length]=(headBytes .noAuth).take 29 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 29) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run29]
  have run27 : consume (wire .noAuth) 33 ((headBytes .noAuth).take 27)=⟨33,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 27++[wire .noAuth ((headBytes .noAuth).take 27).length]=(headBytes .noAuth).take 28 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 28) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run28]
  have run26 : consume (wire .noAuth) 34 ((headBytes .noAuth).take 26)=⟨34,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 26++[wire .noAuth ((headBytes .noAuth).take 26).length]=(headBytes .noAuth).take 27 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 27) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run27]
  have run25 : consume (wire .noAuth) 35 ((headBytes .noAuth).take 25)=⟨35,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 25++[wire .noAuth ((headBytes .noAuth).take 25).length]=(headBytes .noAuth).take 26 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 26) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run26]
  have run24 : consume (wire .noAuth) 36 ((headBytes .noAuth).take 24)=⟨36,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 24++[wire .noAuth ((headBytes .noAuth).take 24).length]=(headBytes .noAuth).take 25 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 25) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run25]
  have run23 : consume (wire .noAuth) 37 ((headBytes .noAuth).take 23)=⟨37,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 23++[wire .noAuth ((headBytes .noAuth).take 23).length]=(headBytes .noAuth).take 24 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 24) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run24]
  have run22 : consume (wire .noAuth) 38 ((headBytes .noAuth).take 22)=⟨38,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 22++[wire .noAuth ((headBytes .noAuth).take 22).length]=(headBytes .noAuth).take 23 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 23) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run23]
  have run21 : consume (wire .noAuth) 39 ((headBytes .noAuth).take 21)=⟨39,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 21++[wire .noAuth ((headBytes .noAuth).take 21).length]=(headBytes .noAuth).take 22 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 22) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run22]
  have run20 : consume (wire .noAuth) 40 ((headBytes .noAuth).take 20)=⟨40,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 20++[wire .noAuth ((headBytes .noAuth).take 20).length]=(headBytes .noAuth).take 21 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 21) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run21]
  have run19 : consume (wire .noAuth) 41 ((headBytes .noAuth).take 19)=⟨41,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 19++[wire .noAuth ((headBytes .noAuth).take 19).length]=(headBytes .noAuth).take 20 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 20) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run20]
  have run18 : consume (wire .noAuth) 42 ((headBytes .noAuth).take 18)=⟨42,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 18++[wire .noAuth ((headBytes .noAuth).take 18).length]=(headBytes .noAuth).take 19 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 19) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run19]
  have run17 : consume (wire .noAuth) 43 ((headBytes .noAuth).take 17)=⟨43,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 17++[wire .noAuth ((headBytes .noAuth).take 17).length]=(headBytes .noAuth).take 18 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 18) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run18]
  have run16 : consume (wire .noAuth) 44 ((headBytes .noAuth).take 16)=⟨44,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 16++[wire .noAuth ((headBytes .noAuth).take 16).length]=(headBytes .noAuth).take 17 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 17) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run17]
  have run15 : consume (wire .noAuth) 45 ((headBytes .noAuth).take 15)=⟨45,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 15++[wire .noAuth ((headBytes .noAuth).take 15).length]=(headBytes .noAuth).take 16 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 16) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run16]
  have run14 : consume (wire .noAuth) 46 ((headBytes .noAuth).take 14)=⟨46,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 14++[wire .noAuth ((headBytes .noAuth).take 14).length]=(headBytes .noAuth).take 15 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 15) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run15]
  have run13 : consume (wire .noAuth) 47 ((headBytes .noAuth).take 13)=⟨47,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 13++[wire .noAuth ((headBytes .noAuth).take 13).length]=(headBytes .noAuth).take 14 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 14) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run14]
  have run12 : consume (wire .noAuth) 48 ((headBytes .noAuth).take 12)=⟨48,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 12++[wire .noAuth ((headBytes .noAuth).take 12).length]=(headBytes .noAuth).take 13 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 13) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run13]
  have run11 : consume (wire .noAuth) 49 ((headBytes .noAuth).take 11)=⟨49,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 11++[wire .noAuth ((headBytes .noAuth).take 11).length]=(headBytes .noAuth).take 12 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 12) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run12]
  have run10 : consume (wire .noAuth) 50 ((headBytes .noAuth).take 10)=⟨50,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 10++[wire .noAuth ((headBytes .noAuth).take 10).length]=(headBytes .noAuth).take 11 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 11) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run11]
  have run9 : consume (wire .noAuth) 51 ((headBytes .noAuth).take 9)=⟨51,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 9++[wire .noAuth ((headBytes .noAuth).take 9).length]=(headBytes .noAuth).take 10 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 10) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run10]
  have run8 : consume (wire .noAuth) 52 ((headBytes .noAuth).take 8)=⟨52,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 8++[wire .noAuth ((headBytes .noAuth).take 8).length]=(headBytes .noAuth).take 9 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 9) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run9]
  have run7 : consume (wire .noAuth) 53 ((headBytes .noAuth).take 7)=⟨53,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 7++[wire .noAuth ((headBytes .noAuth).take 7).length]=(headBytes .noAuth).take 8 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 8) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run8]
  have run6 : consume (wire .noAuth) 54 ((headBytes .noAuth).take 6)=⟨54,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 6++[wire .noAuth ((headBytes .noAuth).take 6).length]=(headBytes .noAuth).take 7 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 7) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run7]
  have run5 : consume (wire .noAuth) 55 ((headBytes .noAuth).take 5)=⟨55,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 5++[wire .noAuth ((headBytes .noAuth).take 5).length]=(headBytes .noAuth).take 6 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 6) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run6]
  have run4 : consume (wire .noAuth) 56 ((headBytes .noAuth).take 4)=⟨56,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 4++[wire .noAuth ((headBytes .noAuth).take 4).length]=(headBytes .noAuth).take 5 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 5) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run5]
  have run3 : consume (wire .noAuth) 57 ((headBytes .noAuth).take 3)=⟨57,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 3++[wire .noAuth ((headBytes .noAuth).take 3).length]=(headBytes .noAuth).take 4 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 4) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run4]
  have run2 : consume (wire .noAuth) 58 ((headBytes .noAuth).take 2)=⟨58,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 2++[wire .noAuth ((headBytes .noAuth).take 2).length]=(headBytes .noAuth).take 3 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 3) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run3]
  have run1 : consume (wire .noAuth) 59 ((headBytes .noAuth).take 1)=⟨59,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 1++[wire .noAuth ((headBytes .noAuth).take 1).length]=(headBytes .noAuth).take 2 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 2) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run2]
  have run0 : consume (wire .noAuth) 60 ((headBytes .noAuth).take 0)=⟨60,headBytes .noAuth,.done (head .noAuth)⟩ := by
    have nextByte : (headBytes .noAuth).take 0++[wire .noAuth ((headBytes .noAuth).take 0).length]=(headBytes .noAuth).take 1 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .noAuth).take 1) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run1]
  exact run0

theorem header_malformed : consume (wire .malformed) (headBytes .malformed).length []=⟨(headBytes .malformed).length,headBytes .malformed,.done (head .malformed)⟩ := by
  have run89 : consume (wire .malformed) 1 ((headBytes .malformed).take 89)=⟨1,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 89++[wire .malformed ((headBytes .malformed).take 89).length]=(headBytes .malformed).take 90 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 90) 1024 1024=.done (head .malformed) := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    congr 1
  have run88 : consume (wire .malformed) 2 ((headBytes .malformed).take 88)=⟨2,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 88++[wire .malformed ((headBytes .malformed).take 88).length]=(headBytes .malformed).take 89 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 89) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run89]
  have run87 : consume (wire .malformed) 3 ((headBytes .malformed).take 87)=⟨3,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 87++[wire .malformed ((headBytes .malformed).take 87).length]=(headBytes .malformed).take 88 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 88) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run88]
  have run86 : consume (wire .malformed) 4 ((headBytes .malformed).take 86)=⟨4,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 86++[wire .malformed ((headBytes .malformed).take 86).length]=(headBytes .malformed).take 87 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 87) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run87]
  have run85 : consume (wire .malformed) 5 ((headBytes .malformed).take 85)=⟨5,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 85++[wire .malformed ((headBytes .malformed).take 85).length]=(headBytes .malformed).take 86 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 86) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run86]
  have run84 : consume (wire .malformed) 6 ((headBytes .malformed).take 84)=⟨6,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 84++[wire .malformed ((headBytes .malformed).take 84).length]=(headBytes .malformed).take 85 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 85) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run85]
  have run83 : consume (wire .malformed) 7 ((headBytes .malformed).take 83)=⟨7,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 83++[wire .malformed ((headBytes .malformed).take 83).length]=(headBytes .malformed).take 84 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 84) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run84]
  have run82 : consume (wire .malformed) 8 ((headBytes .malformed).take 82)=⟨8,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 82++[wire .malformed ((headBytes .malformed).take 82).length]=(headBytes .malformed).take 83 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 83) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run83]
  have run81 : consume (wire .malformed) 9 ((headBytes .malformed).take 81)=⟨9,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 81++[wire .malformed ((headBytes .malformed).take 81).length]=(headBytes .malformed).take 82 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 82) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run82]
  have run80 : consume (wire .malformed) 10 ((headBytes .malformed).take 80)=⟨10,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 80++[wire .malformed ((headBytes .malformed).take 80).length]=(headBytes .malformed).take 81 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 81) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run81]
  have run79 : consume (wire .malformed) 11 ((headBytes .malformed).take 79)=⟨11,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 79++[wire .malformed ((headBytes .malformed).take 79).length]=(headBytes .malformed).take 80 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 80) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run80]
  have run78 : consume (wire .malformed) 12 ((headBytes .malformed).take 78)=⟨12,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 78++[wire .malformed ((headBytes .malformed).take 78).length]=(headBytes .malformed).take 79 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 79) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run79]
  have run77 : consume (wire .malformed) 13 ((headBytes .malformed).take 77)=⟨13,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 77++[wire .malformed ((headBytes .malformed).take 77).length]=(headBytes .malformed).take 78 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 78) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run78]
  have run76 : consume (wire .malformed) 14 ((headBytes .malformed).take 76)=⟨14,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 76++[wire .malformed ((headBytes .malformed).take 76).length]=(headBytes .malformed).take 77 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 77) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run77]
  have run75 : consume (wire .malformed) 15 ((headBytes .malformed).take 75)=⟨15,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 75++[wire .malformed ((headBytes .malformed).take 75).length]=(headBytes .malformed).take 76 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 76) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run76]
  have run74 : consume (wire .malformed) 16 ((headBytes .malformed).take 74)=⟨16,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 74++[wire .malformed ((headBytes .malformed).take 74).length]=(headBytes .malformed).take 75 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 75) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run75]
  have run73 : consume (wire .malformed) 17 ((headBytes .malformed).take 73)=⟨17,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 73++[wire .malformed ((headBytes .malformed).take 73).length]=(headBytes .malformed).take 74 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 74) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run74]
  have run72 : consume (wire .malformed) 18 ((headBytes .malformed).take 72)=⟨18,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 72++[wire .malformed ((headBytes .malformed).take 72).length]=(headBytes .malformed).take 73 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 73) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run73]
  have run71 : consume (wire .malformed) 19 ((headBytes .malformed).take 71)=⟨19,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 71++[wire .malformed ((headBytes .malformed).take 71).length]=(headBytes .malformed).take 72 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 72) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run72]
  have run70 : consume (wire .malformed) 20 ((headBytes .malformed).take 70)=⟨20,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 70++[wire .malformed ((headBytes .malformed).take 70).length]=(headBytes .malformed).take 71 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 71) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run71]
  have run69 : consume (wire .malformed) 21 ((headBytes .malformed).take 69)=⟨21,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 69++[wire .malformed ((headBytes .malformed).take 69).length]=(headBytes .malformed).take 70 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 70) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run70]
  have run68 : consume (wire .malformed) 22 ((headBytes .malformed).take 68)=⟨22,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 68++[wire .malformed ((headBytes .malformed).take 68).length]=(headBytes .malformed).take 69 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 69) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run69]
  have run67 : consume (wire .malformed) 23 ((headBytes .malformed).take 67)=⟨23,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 67++[wire .malformed ((headBytes .malformed).take 67).length]=(headBytes .malformed).take 68 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 68) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run68]
  have run66 : consume (wire .malformed) 24 ((headBytes .malformed).take 66)=⟨24,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 66++[wire .malformed ((headBytes .malformed).take 66).length]=(headBytes .malformed).take 67 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 67) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run67]
  have run65 : consume (wire .malformed) 25 ((headBytes .malformed).take 65)=⟨25,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 65++[wire .malformed ((headBytes .malformed).take 65).length]=(headBytes .malformed).take 66 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 66) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run66]
  have run64 : consume (wire .malformed) 26 ((headBytes .malformed).take 64)=⟨26,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 64++[wire .malformed ((headBytes .malformed).take 64).length]=(headBytes .malformed).take 65 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 65) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run65]
  have run63 : consume (wire .malformed) 27 ((headBytes .malformed).take 63)=⟨27,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 63++[wire .malformed ((headBytes .malformed).take 63).length]=(headBytes .malformed).take 64 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 64) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run64]
  have run62 : consume (wire .malformed) 28 ((headBytes .malformed).take 62)=⟨28,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 62++[wire .malformed ((headBytes .malformed).take 62).length]=(headBytes .malformed).take 63 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 63) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run63]
  have run61 : consume (wire .malformed) 29 ((headBytes .malformed).take 61)=⟨29,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 61++[wire .malformed ((headBytes .malformed).take 61).length]=(headBytes .malformed).take 62 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 62) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run62]
  have run60 : consume (wire .malformed) 30 ((headBytes .malformed).take 60)=⟨30,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 60++[wire .malformed ((headBytes .malformed).take 60).length]=(headBytes .malformed).take 61 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 61) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run61]
  have run59 : consume (wire .malformed) 31 ((headBytes .malformed).take 59)=⟨31,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 59++[wire .malformed ((headBytes .malformed).take 59).length]=(headBytes .malformed).take 60 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 60) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run60]
  have run58 : consume (wire .malformed) 32 ((headBytes .malformed).take 58)=⟨32,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 58++[wire .malformed ((headBytes .malformed).take 58).length]=(headBytes .malformed).take 59 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 59) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run59]
  have run57 : consume (wire .malformed) 33 ((headBytes .malformed).take 57)=⟨33,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 57++[wire .malformed ((headBytes .malformed).take 57).length]=(headBytes .malformed).take 58 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 58) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run58]
  have run56 : consume (wire .malformed) 34 ((headBytes .malformed).take 56)=⟨34,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 56++[wire .malformed ((headBytes .malformed).take 56).length]=(headBytes .malformed).take 57 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 57) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run57]
  have run55 : consume (wire .malformed) 35 ((headBytes .malformed).take 55)=⟨35,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 55++[wire .malformed ((headBytes .malformed).take 55).length]=(headBytes .malformed).take 56 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 56) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run56]
  have run54 : consume (wire .malformed) 36 ((headBytes .malformed).take 54)=⟨36,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 54++[wire .malformed ((headBytes .malformed).take 54).length]=(headBytes .malformed).take 55 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 55) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run55]
  have run53 : consume (wire .malformed) 37 ((headBytes .malformed).take 53)=⟨37,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 53++[wire .malformed ((headBytes .malformed).take 53).length]=(headBytes .malformed).take 54 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 54) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run54]
  have run52 : consume (wire .malformed) 38 ((headBytes .malformed).take 52)=⟨38,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 52++[wire .malformed ((headBytes .malformed).take 52).length]=(headBytes .malformed).take 53 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 53) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run53]
  have run51 : consume (wire .malformed) 39 ((headBytes .malformed).take 51)=⟨39,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 51++[wire .malformed ((headBytes .malformed).take 51).length]=(headBytes .malformed).take 52 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 52) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run52]
  have run50 : consume (wire .malformed) 40 ((headBytes .malformed).take 50)=⟨40,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 50++[wire .malformed ((headBytes .malformed).take 50).length]=(headBytes .malformed).take 51 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 51) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run51]
  have run49 : consume (wire .malformed) 41 ((headBytes .malformed).take 49)=⟨41,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 49++[wire .malformed ((headBytes .malformed).take 49).length]=(headBytes .malformed).take 50 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 50) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run50]
  have run48 : consume (wire .malformed) 42 ((headBytes .malformed).take 48)=⟨42,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 48++[wire .malformed ((headBytes .malformed).take 48).length]=(headBytes .malformed).take 49 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 49) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run49]
  have run47 : consume (wire .malformed) 43 ((headBytes .malformed).take 47)=⟨43,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 47++[wire .malformed ((headBytes .malformed).take 47).length]=(headBytes .malformed).take 48 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 48) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run48]
  have run46 : consume (wire .malformed) 44 ((headBytes .malformed).take 46)=⟨44,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 46++[wire .malformed ((headBytes .malformed).take 46).length]=(headBytes .malformed).take 47 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 47) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run47]
  have run45 : consume (wire .malformed) 45 ((headBytes .malformed).take 45)=⟨45,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 45++[wire .malformed ((headBytes .malformed).take 45).length]=(headBytes .malformed).take 46 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 46) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run46]
  have run44 : consume (wire .malformed) 46 ((headBytes .malformed).take 44)=⟨46,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 44++[wire .malformed ((headBytes .malformed).take 44).length]=(headBytes .malformed).take 45 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 45) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run45]
  have run43 : consume (wire .malformed) 47 ((headBytes .malformed).take 43)=⟨47,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 43++[wire .malformed ((headBytes .malformed).take 43).length]=(headBytes .malformed).take 44 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 44) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run44]
  have run42 : consume (wire .malformed) 48 ((headBytes .malformed).take 42)=⟨48,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 42++[wire .malformed ((headBytes .malformed).take 42).length]=(headBytes .malformed).take 43 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 43) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run43]
  have run41 : consume (wire .malformed) 49 ((headBytes .malformed).take 41)=⟨49,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 41++[wire .malformed ((headBytes .malformed).take 41).length]=(headBytes .malformed).take 42 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 42) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run42]
  have run40 : consume (wire .malformed) 50 ((headBytes .malformed).take 40)=⟨50,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 40++[wire .malformed ((headBytes .malformed).take 40).length]=(headBytes .malformed).take 41 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 41) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run41]
  have run39 : consume (wire .malformed) 51 ((headBytes .malformed).take 39)=⟨51,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 39++[wire .malformed ((headBytes .malformed).take 39).length]=(headBytes .malformed).take 40 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 40) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run40]
  have run38 : consume (wire .malformed) 52 ((headBytes .malformed).take 38)=⟨52,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 38++[wire .malformed ((headBytes .malformed).take 38).length]=(headBytes .malformed).take 39 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 39) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run39]
  have run37 : consume (wire .malformed) 53 ((headBytes .malformed).take 37)=⟨53,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 37++[wire .malformed ((headBytes .malformed).take 37).length]=(headBytes .malformed).take 38 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 38) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run38]
  have run36 : consume (wire .malformed) 54 ((headBytes .malformed).take 36)=⟨54,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 36++[wire .malformed ((headBytes .malformed).take 36).length]=(headBytes .malformed).take 37 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 37) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run37]
  have run35 : consume (wire .malformed) 55 ((headBytes .malformed).take 35)=⟨55,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 35++[wire .malformed ((headBytes .malformed).take 35).length]=(headBytes .malformed).take 36 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 36) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run36]
  have run34 : consume (wire .malformed) 56 ((headBytes .malformed).take 34)=⟨56,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 34++[wire .malformed ((headBytes .malformed).take 34).length]=(headBytes .malformed).take 35 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 35) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run35]
  have run33 : consume (wire .malformed) 57 ((headBytes .malformed).take 33)=⟨57,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 33++[wire .malformed ((headBytes .malformed).take 33).length]=(headBytes .malformed).take 34 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 34) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run34]
  have run32 : consume (wire .malformed) 58 ((headBytes .malformed).take 32)=⟨58,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 32++[wire .malformed ((headBytes .malformed).take 32).length]=(headBytes .malformed).take 33 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 33) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run33]
  have run31 : consume (wire .malformed) 59 ((headBytes .malformed).take 31)=⟨59,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 31++[wire .malformed ((headBytes .malformed).take 31).length]=(headBytes .malformed).take 32 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 32) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run32]
  have run30 : consume (wire .malformed) 60 ((headBytes .malformed).take 30)=⟨60,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 30++[wire .malformed ((headBytes .malformed).take 30).length]=(headBytes .malformed).take 31 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 31) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run31]
  have run29 : consume (wire .malformed) 61 ((headBytes .malformed).take 29)=⟨61,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 29++[wire .malformed ((headBytes .malformed).take 29).length]=(headBytes .malformed).take 30 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 30) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run30]
  have run28 : consume (wire .malformed) 62 ((headBytes .malformed).take 28)=⟨62,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 28++[wire .malformed ((headBytes .malformed).take 28).length]=(headBytes .malformed).take 29 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 29) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run29]
  have run27 : consume (wire .malformed) 63 ((headBytes .malformed).take 27)=⟨63,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 27++[wire .malformed ((headBytes .malformed).take 27).length]=(headBytes .malformed).take 28 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 28) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run28]
  have run26 : consume (wire .malformed) 64 ((headBytes .malformed).take 26)=⟨64,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 26++[wire .malformed ((headBytes .malformed).take 26).length]=(headBytes .malformed).take 27 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 27) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run27]
  have run25 : consume (wire .malformed) 65 ((headBytes .malformed).take 25)=⟨65,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 25++[wire .malformed ((headBytes .malformed).take 25).length]=(headBytes .malformed).take 26 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 26) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run26]
  have run24 : consume (wire .malformed) 66 ((headBytes .malformed).take 24)=⟨66,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 24++[wire .malformed ((headBytes .malformed).take 24).length]=(headBytes .malformed).take 25 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 25) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run25]
  have run23 : consume (wire .malformed) 67 ((headBytes .malformed).take 23)=⟨67,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 23++[wire .malformed ((headBytes .malformed).take 23).length]=(headBytes .malformed).take 24 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 24) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run24]
  have run22 : consume (wire .malformed) 68 ((headBytes .malformed).take 22)=⟨68,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 22++[wire .malformed ((headBytes .malformed).take 22).length]=(headBytes .malformed).take 23 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 23) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run23]
  have run21 : consume (wire .malformed) 69 ((headBytes .malformed).take 21)=⟨69,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 21++[wire .malformed ((headBytes .malformed).take 21).length]=(headBytes .malformed).take 22 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 22) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run22]
  have run20 : consume (wire .malformed) 70 ((headBytes .malformed).take 20)=⟨70,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 20++[wire .malformed ((headBytes .malformed).take 20).length]=(headBytes .malformed).take 21 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 21) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run21]
  have run19 : consume (wire .malformed) 71 ((headBytes .malformed).take 19)=⟨71,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 19++[wire .malformed ((headBytes .malformed).take 19).length]=(headBytes .malformed).take 20 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 20) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run20]
  have run18 : consume (wire .malformed) 72 ((headBytes .malformed).take 18)=⟨72,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 18++[wire .malformed ((headBytes .malformed).take 18).length]=(headBytes .malformed).take 19 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 19) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run19]
  have run17 : consume (wire .malformed) 73 ((headBytes .malformed).take 17)=⟨73,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 17++[wire .malformed ((headBytes .malformed).take 17).length]=(headBytes .malformed).take 18 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 18) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run18]
  have run16 : consume (wire .malformed) 74 ((headBytes .malformed).take 16)=⟨74,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 16++[wire .malformed ((headBytes .malformed).take 16).length]=(headBytes .malformed).take 17 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 17) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run17]
  have run15 : consume (wire .malformed) 75 ((headBytes .malformed).take 15)=⟨75,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 15++[wire .malformed ((headBytes .malformed).take 15).length]=(headBytes .malformed).take 16 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 16) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run16]
  have run14 : consume (wire .malformed) 76 ((headBytes .malformed).take 14)=⟨76,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 14++[wire .malformed ((headBytes .malformed).take 14).length]=(headBytes .malformed).take 15 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 15) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run15]
  have run13 : consume (wire .malformed) 77 ((headBytes .malformed).take 13)=⟨77,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 13++[wire .malformed ((headBytes .malformed).take 13).length]=(headBytes .malformed).take 14 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 14) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run14]
  have run12 : consume (wire .malformed) 78 ((headBytes .malformed).take 12)=⟨78,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 12++[wire .malformed ((headBytes .malformed).take 12).length]=(headBytes .malformed).take 13 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 13) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run13]
  have run11 : consume (wire .malformed) 79 ((headBytes .malformed).take 11)=⟨79,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 11++[wire .malformed ((headBytes .malformed).take 11).length]=(headBytes .malformed).take 12 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 12) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run12]
  have run10 : consume (wire .malformed) 80 ((headBytes .malformed).take 10)=⟨80,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 10++[wire .malformed ((headBytes .malformed).take 10).length]=(headBytes .malformed).take 11 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 11) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run11]
  have run9 : consume (wire .malformed) 81 ((headBytes .malformed).take 9)=⟨81,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 9++[wire .malformed ((headBytes .malformed).take 9).length]=(headBytes .malformed).take 10 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 10) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run10]
  have run8 : consume (wire .malformed) 82 ((headBytes .malformed).take 8)=⟨82,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 8++[wire .malformed ((headBytes .malformed).take 8).length]=(headBytes .malformed).take 9 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 9) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run9]
  have run7 : consume (wire .malformed) 83 ((headBytes .malformed).take 7)=⟨83,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 7++[wire .malformed ((headBytes .malformed).take 7).length]=(headBytes .malformed).take 8 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 8) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run8]
  have run6 : consume (wire .malformed) 84 ((headBytes .malformed).take 6)=⟨84,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 6++[wire .malformed ((headBytes .malformed).take 6).length]=(headBytes .malformed).take 7 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 7) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run7]
  have run5 : consume (wire .malformed) 85 ((headBytes .malformed).take 5)=⟨85,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 5++[wire .malformed ((headBytes .malformed).take 5).length]=(headBytes .malformed).take 6 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 6) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run6]
  have run4 : consume (wire .malformed) 86 ((headBytes .malformed).take 4)=⟨86,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 4++[wire .malformed ((headBytes .malformed).take 4).length]=(headBytes .malformed).take 5 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 5) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run5]
  have run3 : consume (wire .malformed) 87 ((headBytes .malformed).take 3)=⟨87,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 3++[wire .malformed ((headBytes .malformed).take 3).length]=(headBytes .malformed).take 4 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 4) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run4]
  have run2 : consume (wire .malformed) 88 ((headBytes .malformed).take 2)=⟨88,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 2++[wire .malformed ((headBytes .malformed).take 2).length]=(headBytes .malformed).take 3 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 3) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run3]
  have run1 : consume (wire .malformed) 89 ((headBytes .malformed).take 1)=⟨89,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 1++[wire .malformed ((headBytes .malformed).take 1).length]=(headBytes .malformed).take 2 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 2) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run2]
  have run0 : consume (wire .malformed) 90 ((headBytes .malformed).take 0)=⟨90,headBytes .malformed,.done (head .malformed)⟩ := by
    have nextByte : (headBytes .malformed).take 0++[wire .malformed ((headBytes .malformed).take 0).length]=(headBytes .malformed).take 1 := by decide +kernel
    have parsedPrefix : HttpRequestBytes.parse ((headBytes .malformed).take 1) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsedPrefix]
    rw [run1]
  exact run0

end E5R.Thermostat.ReceivedLiteralWriteWitness
