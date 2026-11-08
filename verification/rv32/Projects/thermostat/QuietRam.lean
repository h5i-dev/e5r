import Projects.thermostat.Quiet
import Projects.thermostat.ObservedRam
namespace E5R.Thermostat.Quiet
open E5R
variable {B : Board} {img : List Segment}

theorem interp_load_ram (o : Oracle) {w a atomic k ram i evs reads}
    (hal : a.toNat%w.bytes=0) (hin : B.inRam a w.bytes=true) :
    Observed.interp B img o (.load w a atomic k) ram i evs reads =
      Observed.interp B img o (k (ramRead ram a w)) ram i evs reads :=
  ObservedRam.load B img o w a atomic k ram i evs reads hal hin

theorem interp_store_ram (o : Oracle) {w a v atomic k ram i evs reads}
    (hal : a.toNat%w.bytes=0) (hin : B.inRam a w.bytes=true) :
    Observed.interp B img o (.store w a v atomic k) ram i evs reads =
      Observed.interp B img o k (ramWrite ram a v w) i evs reads :=
  ObservedRam.store B img o w a v atomic k ram i evs reads hal hin
end E5R.Thermostat.Quiet
