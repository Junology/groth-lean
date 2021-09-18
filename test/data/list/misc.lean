import data.list.misc
import system.io

open list

#eval io.put_str_ln "=================="
#eval io.put_str_ln "  data.list.misc  "
#eval io.put_str_ln "=================="

#eval io.put_str_ln "Axioms:"
#print axioms nil_union
#print axioms cons_union
#print axioms mem_append'
#print axioms mem_filter
#print axioms mem_of_insert_self
#print axioms mem_of_insert_to_mem
#print axioms mem_union_iff
#print axioms mem_map_of_mem
#print axioms mem_of_mem_map
#print axioms not_mem_map_of_offimage
#print axioms is_nil_of_no_mem
#print axioms not_mem_filter
#print axioms subset_nil
#print axioms nodup_head
#print axioms nodup_tail
#print axioms nodup_tail_of_sub
#print axioms nodup_filter
#print axioms nodup_union
#print axioms nodup_of_nodup_map
#print axioms nodup_map_of_nodup
#print axioms perm.rfl
#print axioms perm.symm
#print axioms perm.subset
#print axioms perm.mem_iff
#print axioms perm.not_mem
#print axioms mem_perm_head
#print axioms perm_nodup
#print axioms nodup_perm_of_mem

