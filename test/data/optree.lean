import data.optree
import system.io

open optree

#eval io.put_str_ln "==============="
#eval io.put_str_ln "  data.optree  "
#eval io.put_str_ln "==============="

#eval io.put_str_ln "Axioms:"
#print axioms optree.nnodes
#print axioms optree.nnodes_vec_mem
#print axioms optree.nnodes_child
#print axioms optree.accessible
#print axioms optree.children_wf
#print axioms opnode_inj_nh
#print axioms varleaf_neq_opnode
#print axioms optree.map_comp
#print axioms join_unit_outer
#print axioms join_unit_inner
#print axioms join_assoc
#print axioms elim_aux_map
#print axioms elim_varleaf
#print axioms elim_opnode
#print axioms elim_funap
#print axioms elim_funext
#print axioms elim_prod
#print axioms elim_pi
#print axioms elim_subtype
#print axioms optree.unzip_inj

