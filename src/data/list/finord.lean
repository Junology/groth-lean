import data.finite.finord
import .misc

namespace finord

--- Complete list of elements
@[reducible]
definition elem_list : Π n, list (finord n)
| 0 := []
| (k+1) := fz :: (elem_list k).map fs

#print axioms elem_list

lemma elem_list_nodup : Π n, list.nodup (elem_list n)
| 0 := list.nodup.nil
| (k+1) :=
  list.nodup.cons
    (list.not_mem_map_of_offimage fz (@fz_not_fs k))
    (list.nodup_map_of_nodup fs_inj (elem_list_nodup k))

#print axioms elem_list_nodup

lemma elem_list_complete : Π {n}, ∀ (x : finord n), x ∈ elem_list n
| (k+1) fz := or.inl rfl
| (k+1) (fs j) := or.inr (list.mem_map_of_mem j _ (elem_list_complete j))

end finord
