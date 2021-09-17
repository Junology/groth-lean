import logic.finite.basic
import system.io

#eval io.put_str_ln "======================"
#eval io.put_str_ln "  logic.finite.basic  "
#eval io.put_str_ln "======================"

#eval io.put_str_ln "Axioms:"
#print axioms finord.exhaustive_list
#print axioms exhaustive_list.nodup
#print axioms exhaustive_list.exhaustive
#print axioms exhaustive_list.perm
#print axioms exhaustive_list.translate
#print axioms exhaustive_list.subtype
#print axioms finord_is_finite
#print axioms isom_to_finord
#print axioms is_finite.has_exhaustive_list
