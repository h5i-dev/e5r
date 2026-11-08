import Theories.Logic
namespace E5R.Thermostat.IntegralReady
open E5R

structure Ready (c d : Core) (writer src len : Word) : Prop where
  pc : d.pc = 0x800022a0#32
  sp : d.get 2 = c.get 2
  writer : d.get 10 = writer
  source : d.get 11 = src
  length : d.get 12 = len
  csr : d.sameCsr c
  x1 : d.get 1 = c.get 1
  x8 : d.get 8 = c.get 8
  x9 : d.get 9 = c.get 9
  x18 : d.get 18 = c.get 18
  x19 : d.get 19 = c.get 19
  x20 : d.get 20 = c.get 20
  x21 : d.get 21 = c.get 21
  x22 : d.get 22 = c.get 22
  x23 : d.get 23 = c.get 23
  x24 : d.get 24 = c.get 24
  x25 : d.get 25 = c.get 25
  x26 : d.get 26 = c.get 26
  x27 : d.get 27 = c.get 27

end E5R.Thermostat.IntegralReady
