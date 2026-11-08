import Projects.thermostat.Bytes
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.DigitMath
open E5R E5R.Thermostat

/-- The compiler's bounded reciprocal multiplications are exact decimal division. -/
theorem div100 (n : Nat) (hn : n < 10000) : (n/4*5243)/131072 = n/100 := by omega

theorem div10000 (n : Nat) (hn : n ≤ 32768) : (n/16*839)/524288 = n/10000 := by omega

theorem pair_index (n : Nat) (hn : n < 10000) : ((n/4*5243)/65536)/2*2 = 2*(n/100) := by
  have hd := div100 n hn
  omega

theorem remainder100 (n : Nat) : n-(n/100)*100 = n%100 := by omega

theorem remainder10000 (n : Nat) : n-(n/10000)*10000 = n%10000 := by omega
end E5R.Thermostat.DigitMath
