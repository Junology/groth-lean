import data.vect.chain
import system.io

open based_chain

#eval io.put_str_ln "==================="
#eval io.put_str_ln "  data.vect.chain  "
#eval io.put_str_ln "==================="

#eval io.put_str_ln "Axioms:"
#print axioms to_vect_is_monotonic
#print axioms from_vect
#print axioms from_vect'
#print axioms tail_heq
#print axioms to_vect_of_from
#print axioms head_of_to_vect
#print axioms from_vect_of_to

