import algebra.binary_module.decfree
import system.io

#eval io.put_str_ln "================================="
#eval io.put_str_ln "  algebra.binary_module.decfree  "
#eval io.put_str_ln "================================="

#eval io.put_str_ln "Axioms:"

open binary_module

#print axioms singlebit_nonzero_iff
#print axioms singlebit_support
#print axioms support_of_add_singlebit_of_nonzero
#print axioms waccum_funrel_zero
#print axioms waccum_funrel_single
#print axioms waccum_funrel_add
#print axioms unsafe.finsupp_bits.nonzero
#print axioms unsafe.waccum_single
#print axioms unsafe.finsupp_bits_free
#print axioms unsafe.finsupp_bits.is_free

