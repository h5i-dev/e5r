import Projects.thermostat.ChunkLayout
namespace E5R.Thermostat.ChunkWordMath
open E5R E5R.Thermostat

theorem extend_word (v : Word) : extend .w true v=v := by rfl

theorem first_byte (ram : Word → BitVec 8) (p : Word) :
    byteOf (ramRead ram p .w) 0=ram p := by
  apply BitVec.eq_of_toNat_eq
  have h0 := (ram p).isLt
  have h1 := (ram (p+1#32)).isLt
  have h2 := (ram (p+2#32)).isLt
  have h3 := (ram (p+3#32)).isLt
  simp only [byteOf,ramRead,BitVec.toNat_ofNat]
  omega

end E5R.Thermostat.ChunkWordMath
