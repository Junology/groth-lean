import data.finite.finite
import system.io

#eval io.put_str_ln "======================"
#eval io.put_str_ln "  data.finite.finite  "
#eval io.put_str_ln "======================"

#eval io.put_str_ln "Axioms:"
#print axioms isom_to_finord
#print axioms is_finite.replace_finord
#print axioms is_finite.has_element_list
