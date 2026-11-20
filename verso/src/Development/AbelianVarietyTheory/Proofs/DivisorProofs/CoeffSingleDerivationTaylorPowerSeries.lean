import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallMemFilt
open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

namespace GlobalTheory.FormalOrigin.Extend

/- English proof (translation)
Introduce `l hl`. Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons i l ih`. Rewrite `hl` using `[List.nodup_cons]`.

Rewrite using `[List.foldr_cons, ih hl.2]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[hl.1]`. Establish `hji : j ≠ i` using `fun h => hij h.symm`.

Simplify using `[Finsupp.single_apply, hij, hji]`.
-/
theorem list_foldr_iterate_single_of_nodup {A : Type} {n : ℕ} (d : Fin n → A → A) (j : Fin n) (f : A) :
    ∀ l : List (Fin n), l.Nodup →
      l.foldr (fun i g => (d i)^[(Finsupp.single j 1 : Fin n →₀ ℕ) i] g) f = if j ∈ l then d j f else f := by
  intro l hl
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    rw [List.foldr_cons, ih hl.2]
    by_cases hij : i = j
    · subst hij
      simp [hl.1]
    · have hji : j ≠ i := fun h => hij h.symm
      simp [Finsupp.single_apply, hij, hji]

/- English proof (translation)
Establish `hit : iterOp (fun i => ⇑(ds i)) (Finsupp.single j 1) f = ds j f`. Unfold `iterOp`. Rewrite using `[list_foldr_iterate_single_of_nodup _ j f _ (List.nodup_finRange n)]`. Simplify using `[List.mem_finRange]`. Establish `hprod : (∏ i, (((Finsupp.single j 1 : Fin n →₀ ℕ) i).factorial : ℚ)) = 1`.

Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Finsupp.single_apply, h]`.

Use `show (∏ i, (((Finsupp.single j 1 : Fin n →₀ ℕ) i).factorial : ℚ))⁻¹ • ev (iterOp (fun i => ⇑(ds i)) (Finsupp.single j 1) f) = _`. Rewrite using `[hit, hprod, inv_one, one_smul]`.
-/
theorem taylor_coeff_single (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B)
    (ds : Fin n → Derivation ℤ A A) (j : Fin n) (f : A) :
    MvPowerSeries.coeff (Finsupp.single j 1) (taylor ev (fun i => ⇑(ds i)) f) = ev (ds j f) := by
  have hit : iterOp (fun i => ⇑(ds i)) (Finsupp.single j 1) f = ds j f := by
    unfold iterOp
    rw [list_foldr_iterate_single_of_nodup _ j f _ (List.nodup_finRange n)]
    simp [List.mem_finRange]
  have hprod : (∏ i, (((Finsupp.single j 1 : Fin n →₀ ℕ) i).factorial : ℚ)) = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    by_cases h : j = i
    · subst h; simp
    · simp [Finsupp.single_apply, h]
  show (∏ i, (((Finsupp.single j 1 : Fin n →₀ ℕ) i).factorial : ℚ))⁻¹ • ev (iterOp (fun i => ⇑(ds i)) (Finsupp.single j 1) f) = _
  rw [hit, hprod, inv_one, one_smul]

end GlobalTheory.FormalOrigin.Extend
