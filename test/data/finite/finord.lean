import data.finite.finord
import system.io

open finord

#eval io.put_str_ln "======================"
#eval io.put_str_ln "  data.finite.finord  "
#eval io.put_str_ln "======================"

#eval io.put_str_ln "Axioms:"
#print axioms zero_empty
#print axioms fz_not_fs
#print axioms fs_inj
#print axioms finord.lt
#print axioms finord.lt_decidable
#print axioms finord.lt_irrefl
#print axioms finord.lt_asymm
#print axioms finord.lt_incomp_eq
#print axioms finord.lt_trans
#print axioms finord.lt_trichotomous
#print axioms inject_succ
#print axioms inject
#print axioms to_fin
#print axioms to_fs_succ
#print axioms from_fin
#print axioms from_succ_fs
#print axioms fromto_id
#print axioms tofrom_id
#print axioms card_of

definition is_mul_of_three : Π {n : ℕ}, finord n → Prop
| _ fz := true
| _ (fs fz) := false
| _ (fs (fs fz)) := false
| _ (fs (fs (fs n))) := is_mul_of_three n

instance test_dec : ∀ n (k : finord n), decidable (is_mul_of_three k)
| _ fz := is_true true.intro
| _ (fs fz) := is_false false.elim
| _ (fs (fs fz)) := is_false false.elim
| _ (fs (fs (fs k))) := test_dec _ k

example : card_of (@is_mul_of_three 0) = 0 := rfl
example : card_of (@is_mul_of_three 1) = 1 := rfl
example : card_of (@is_mul_of_three 2) = 1 := rfl
example : card_of (@is_mul_of_three 3) = 1 := rfl
example : card_of (@is_mul_of_three 4) = 2 := rfl
example : card_of (@is_mul_of_three 5) = 2 := rfl
example : card_of (@is_mul_of_three 6) = 2 := rfl
example : card_of (@is_mul_of_three 7) = 3 := rfl
example : card_of (@is_mul_of_three 8) = 3 := rfl
example : card_of (@is_mul_of_three 9) = 3 := rfl
example : card_of (@is_mul_of_three 10) = 4 := rfl
example : card_of (@is_mul_of_three 11) = 4 := rfl
example : card_of (@is_mul_of_three 12) = 4 := rfl
example : card_of (@is_mul_of_three 13) = 5 := rfl

