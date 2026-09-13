import PrimeGPF.Progressions
import PrimeNumberTheoremAnd.Wiener
import Mathlib.NumberTheory.LSeries.PrimesInAP

namespace PrimeGPF

open Filter Topology
open ArithmeticFunction
open ArithmeticFunction.vonMangoldt

#check nterm
#check cheby
#check chebyWith
#check cumsum
#check WienerIkeharaTheorem'
#check vonMangoldt_cheby
#print axioms WienerIkeharaTheorem'
#print axioms vonMangoldt_cheby
#check ArithmeticFunction.vonMangoldt.residueClass
#check ArithmeticFunction.vonMangoldt.residueClass_nonneg
#check ArithmeticFunction.vonMangoldt.residueClass_le
#check ArithmeticFunction.vonMangoldt.abscissaOfAbsConv_residueClass_le_one
#check ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux
#check ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux
#check ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux
#check ArithmeticFunction.LSeriesSummable_vonMangoldt
#check ZMod.isUnit_iff_coprime

end PrimeGPF
