import data.list.map_partial
import system.io

open list

#eval io.put_str_ln "========================="
#eval io.put_str_ln "  data.list.map_partial  "
#eval io.put_str_ln "========================="

#eval io.put_str_ln "Axioms:"
#print axioms map_partial_nil
#print axioms map_partial_cons
#print axioms mem_map_partial_of_mem
#print axioms mem_of_mem_map_partial
#print axioms nodup_map_partial_of_nodup
