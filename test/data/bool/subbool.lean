import data.bool.subbool
import system.io

#eval io.put_str_ln "====================="
#eval io.put_str_ln "  data.bool.subbool  "
#eval io.put_str_ln "====================="

#eval io.put_str_ln "Axioms:"
#print axioms subbool.ff
#print axioms subbool.tt
#print axioms subbool.and
#print axioms subbool.or
#print axioms subbool.xor
#print axioms subbool.xor_ff
#print axioms subbool.ff_xor
#print axioms subbool.xor_self
#print axioms subbool.xor_comm
#print axioms subbool.xor_assoc
#print axioms subbool.relax
#print axioms subbool.to_bool
#print axioms subbool.from_bool
