import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianOrder.Development

noncomputable section

namespace PI.LocJacOrd.W.Ar

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacOrd
open scoped TensorProduct Classical

section AbsV

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Establish `h : Ideal.absNorm v.asIdeal ≠ 0` using `fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)`. Conclude with `h` after adjusting the coercions.
-/
theorem absNorm_ne_zero : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ≠ 0 := by
  have h : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  exact_mod_cast h

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[absV, hx]`. Distinguish the cases in `hy : y = 0`. Simplify using `[absV, hy]`. Establish `hx' : Valued.v x ≠ 0` using `(Valuation.ne_zero_iff _).2 hx`.

Establish `hy' : Valued.v y ≠ 0` using `(Valuation.ne_zero_iff _).2 hy`. Establish `hxy' : Valued.v (x * y) ≠ 0` using `(Valuation.ne_zero_iff _).2 (mul_ne_zero hx hy)`. Establish `hu : WithZero.unzero hxy' = WithZero.unzero hx' * WithZero.unzero hy'`. Apply `WithZero.coe_injective` to reduce the goal to its premises. Simplify using `only [WithZero.coe_unzero, WithZero.coe_mul, map_mul]`.

Simplify using `only [absV, dif_neg hx', dif_neg hy', dif_neg hxy', hu, toAdd_mul, zpow_add₀ (absNorm_ne_zero v)]`.
-/
theorem absV_mul (x y : Fv F v) : absV v (x * y) = absV v x * absV v y := by
  by_cases hx : x = 0
  · simp [absV, hx]
  by_cases hy : y = 0
  · simp [absV, hy]
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have hxy' : Valued.v (x * y) ≠ 0 := (Valuation.ne_zero_iff _).2 (mul_ne_zero hx hy)
  have hu : WithZero.unzero hxy' = WithZero.unzero hx' * WithZero.unzero hy' := by
    apply WithZero.coe_injective
    simp only [WithZero.coe_unzero, WithZero.coe_mul, map_mul]
  simp only [absV, dif_neg hx', dif_neg hy', dif_neg hxy', hu, toAdd_mul,
    zpow_add₀ (absNorm_ne_zero v)]

/- English proof (translation)
Simplify using `[absV]`.
-/
theorem absV_zero : absV v (0 : Fv F v) = 0 := by simp [absV]

/- English proof (translation)
Establish `h1 : Valued.v (1 : Fv F v) ≠ 0` using `by simp`. Establish `hu : WithZero.unzero h1 = 1`. Apply `WithZero.coe_injective` to reduce the goal to its premises. Simplify using `only [WithZero.coe_unzero, map_one, WithZero.coe_one]`. Simplify using `only [absV, dif_neg h1, hu, toAdd_one, zpow_zero]`.
-/
theorem absV_one : absV v (1 : Fv F v) = 1 := by
  have h1 : Valued.v (1 : Fv F v) ≠ 0 := by simp
  have hu : WithZero.unzero h1 = 1 := by
    apply WithZero.coe_injective
    simp only [WithZero.coe_unzero, map_one, WithZero.coe_one]
  simp only [absV, dif_neg h1, hu, toAdd_one, zpow_zero]

def absVHom : Fv F v →*₀ ℝ where
  toFun := absV v
  map_zero' := absV_zero v
  map_one' := absV_one v
  map_mul' := absV_mul v

/- English proof (translation)
Establish `hx' : Valued.v x ≠ 0` using `(Valuation.ne_zero_iff _).2 hx`. Simplify using `only [absV, dif_neg hx']`. Conclude with `zpow_ne_zero _ (absNorm_ne_zero v)`.
-/
theorem absV_ne_zero {x : Fv F v} (hx : x ≠ 0) : absV v x ≠ 0 := by
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  simp only [absV, dif_neg hx']
  exact zpow_ne_zero _ (absNorm_ne_zero v)

/- English proof (translation)
The claim follows from `(map_prod (absVHom v) (fun i => f i ^ 2) s).trans (Finset.prod_congr rfl fun i _ => map_pow (absVHom v) (f i) 2)`.
-/
theorem absV_prod_sq {r : ℕ} (s : Finset (Fin (r + 1))) (f : Fin (r + 1) → Fv F v) :
    absV v (∏ i ∈ s, f i ^ 2) = ∏ i ∈ s, absV v (f i) ^ 2 :=
  (map_prod (absVHom v) (fun i => f i ^ 2) s).trans
    (Finset.prod_congr rfl fun i _ => map_pow (absVHom v) (f i) 2)

/- English proof (translation)
Unfold `dV`. Use `split_ifs with h`. Conclude with `h.choose_spec.1`. Conclude with `one_ne_zero`.
-/
theorem dV_ne_zero : dV v ≠ 0 := by
  unfold dV
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_ne_zero

/- English proof (translation)
Unfold `alp`. Use `split_ifs`. Conclude with `pow_ne_zero _ (inv_ne_zero (dV_ne_zero v))`. Conclude with `one_ne_zero`.
-/
theorem alp_ne_zero (r : ℕ) (i : Fin (r + 1)) : alp v r i ≠ 0 := by
  unfold alp
  split_ifs
  · exact pow_ne_zero _ (inv_ne_zero (dV_ne_zero v))
  · exact one_ne_zero

end AbsV

section Real

/- English proof (translation)
Rewrite using `[Fintype.prod_prod_type]`. Simplify using `only [Finset.prod_filter]`. Rewrite using `[Finset.prod_comm]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Fin.prod_univ_succ]`.

Establish `h0 : ¬ i < (0 : Fin (r + 1))` using `by simp`. Rewrite using `[if_neg h0, one_mul]`. Use `Finset.prod_congr rfl fun l _ => ?_` and prove the remaining obligations. Establish `: (i < l.succ) ↔ ((i : ℕ) ≤ (l : ℕ))`. Rewrite using `[Fin.lt_def, Fin.val_succ]`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [this]`.
-/
theorem jac_count (r : ℕ) (b : Fin (r + 1) → ℝ) :
    ∏ l : Fin r, ∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)), b i =
      ∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then b p.1 else 1) := by
  rw [Fintype.prod_prod_type]
  simp only [Finset.prod_filter]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fin.prod_univ_succ]
  have h0 : ¬ i < (0 : Fin (r + 1)) := by simp
  rw [if_neg h0, one_mul]
  refine Finset.prod_congr rfl fun l _ => ?_
  have : (i < l.succ) ↔ ((i : ℕ) ≤ (l : ℕ)) := by
    rw [Fin.lt_def, Fin.val_succ]; omega
  simp only [this]

/- English proof (translation)
Establish `hm : m ^ ((r + 1) * (r + 1)) = ∏ _p : Fin (r + 1) × Fin (r + 1), m`. Simplify using `[Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]`. Establish `hP : ∏ i : Fin (r + 1), ∏ j : Fin (r + 1), ((a i * a j) ^ 2)⁻¹ = ∏ p : Fin (r + 1) × Fin (r + 1), ((a p.1 * a p.2) ^ 2)⁻¹` using `(Fintype.prod_prod_type (fun p : Fin (r + 1) × Fin (r + 1) => ((a p.1 * a p.2) ^ 2)⁻¹)).symm`. Establish `hJ : ∏ l : Fin r, ((∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)), a i ^ 2) ^ 2) ^ 2 = ∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then a p.1 ^ 8 else 1)`. Rewrite using `[← jac_count r (fun i => a i ^ 8)]`.

Use `Finset.prod_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_pow, ← Finset.prod_pow]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hU : ∏ q : UIdx r, (m ^ 2 * (a q.1.1 / a q.1.2) ^ 4) = ∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then m ^ 2 * (a p.1 / a p.2) ^ 4 else 1)`.

Rewrite using `[← Finset.prod_filter]`. Conclude with `(Finset.prod_subtype _ (fun p : Fin (r + 1) × Fin (r + 1) => by simp) (fun p : Fin (r + 1) × Fin (r + 1) => m ^ 2 * (a p.1 / a p.2) ^ 4)).symm`. Establish `hD : ∏ l : Fin (r + 1), (m * (a l ^ 4)⁻¹) = ∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 = p.2 then m * (a p.1 ^ 4)⁻¹ else 1)`. Rewrite using `[Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.prod_ite_eq]`. Simplify using the standard rewrite rules. Establish `hL : ∏ p : Fin (r + 1) × Fin (r + 1), (if p.2 < p.1 then m * ((a p.1 * a p.2) ^ 2)⁻¹ else 1) = ∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then m * ((a p.1 * a p.2) ^ 2)⁻¹ else 1)`. Use `Fintype.prod_equiv (Equiv.prodComm _ _) _ _ fun p => ?_` and prove the remaining obligations. Simplify using `only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, mul_comm (a p.2)]`.

Establish `hsplit : ∏ p : Fin (r + 1) × Fin (r + 1), (m * ((a p.1 * a p.2) ^ 2)⁻¹) = (∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then m * ((a p.1 * a p.2) ^ 2)⁻¹ else 1)) * (∏ p : Fin (r + 1) × Fin (r + 1), (if p.2 < p.1 then m * ((a p.1 * a p.2) ^ 2)⁻¹ else 1)) * (∏ p : Fin (r + 1) × F …`. Rewrite using `[← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun p _ => ?_` and prove the remaining obligations. Break down `lt_trichotomy p.1 p.2 with h | h | h` into its components or cases. Simplify using `[h, h.ne, not_lt.2 h.le]`.

Rewrite using `[if_neg (by simp [h]), if_neg (by simp [h]), if_pos h, h]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[h, h.ne', not_lt.2 h.le]`. Establish `key : (∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then m * ((a p.1 * a p.2) ^ 2)⁻¹ else 1)) * (∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then m * ((a p.1 * a p.2) ^ 2)⁻¹ else 1)) * (∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then a p.1 ^ 8 else 1)) = ∏ p : Fin (r + 1 …`. Rewrite using `[← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun p _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Establish `h1` using `ha p.1`. Establish `h2` using `ha p.2`. Clear the denominators using the available nonvanishing facts.

Simplify using the standard rewrite rules. Rewrite using `[hm, hP, ← Finset.prod_mul_distrib, hsplit, hL, hJ, hU, hD, ← key]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem arith_real (r : ℕ) (m : ℝ) (a : Fin (r + 1) → ℝ) (ha : ∀ i, a i ≠ 0) :
    m ^ ((r + 1) * (r + 1)) * (∏ i : Fin (r + 1), ∏ j : Fin (r + 1), ((a i * a j) ^ 2)⁻¹) *
        ∏ l : Fin r, ((∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)),
          a i ^ 2) ^ 2) ^ 2 =
      (∏ q : UIdx r, (m ^ 2 * (a q.1.1 / a q.1.2) ^ 4)) * ∏ l : Fin (r + 1), (m * (a l ^ 4)⁻¹) := by
  have hm : m ^ ((r + 1) * (r + 1)) = ∏ _p : Fin (r + 1) × Fin (r + 1), m := by
    simp [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  have hP : ∏ i : Fin (r + 1), ∏ j : Fin (r + 1), ((a i * a j) ^ 2)⁻¹ =
      ∏ p : Fin (r + 1) × Fin (r + 1), ((a p.1 * a p.2) ^ 2)⁻¹ :=
    (Fintype.prod_prod_type (fun p : Fin (r + 1) × Fin (r + 1) => ((a p.1 * a p.2) ^ 2)⁻¹)).symm
  have hJ : ∏ l : Fin r, ((∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)),
      a i ^ 2) ^ 2) ^ 2 =
      ∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then a p.1 ^ 8 else 1) := by
    rw [← jac_count r (fun i => a i ^ 8)]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [← Finset.prod_pow, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    ring
  have hU : ∏ q : UIdx r, (m ^ 2 * (a q.1.1 / a q.1.2) ^ 4) =
      ∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then m ^ 2 * (a p.1 / a p.2) ^ 4 else 1) := by
    rw [← Finset.prod_filter]
    exact (Finset.prod_subtype _ (fun p : Fin (r + 1) × Fin (r + 1) => by simp)
      (fun p : Fin (r + 1) × Fin (r + 1) => m ^ 2 * (a p.1 / a p.2) ^ 4)).symm
  have hD : ∏ l : Fin (r + 1), (m * (a l ^ 4)⁻¹) =
      ∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 = p.2 then m * (a p.1 ^ 4)⁻¹ else 1) := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_ite_eq]
    simp
  have hL : ∏ p : Fin (r + 1) × Fin (r + 1), (if p.2 < p.1 then m * ((a p.1 * a p.2) ^ 2)⁻¹ else 1) =
      ∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then m * ((a p.1 * a p.2) ^ 2)⁻¹ else 1) := by
    refine Fintype.prod_equiv (Equiv.prodComm _ _) _ _ fun p => ?_
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, mul_comm (a p.2)]
  have hsplit : ∏ p : Fin (r + 1) × Fin (r + 1), (m * ((a p.1 * a p.2) ^ 2)⁻¹) =
      (∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then m * ((a p.1 * a p.2) ^ 2)⁻¹ else 1)) *
      (∏ p : Fin (r + 1) × Fin (r + 1), (if p.2 < p.1 then m * ((a p.1 * a p.2) ^ 2)⁻¹ else 1)) *
      (∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 = p.2 then m * (a p.1 ^ 4)⁻¹ else 1)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rcases lt_trichotomy p.1 p.2 with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · rw [if_neg (by simp [h]), if_neg (by simp [h]), if_pos h, h]
      ring
    · simp [h, h.ne', not_lt.2 h.le]
  have key : (∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then m * ((a p.1 * a p.2) ^ 2)⁻¹ else 1)) *
      (∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then m * ((a p.1 * a p.2) ^ 2)⁻¹ else 1)) *
      (∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then a p.1 ^ 8 else 1)) =
      ∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then m ^ 2 * (a p.1 / a p.2) ^ 4 else 1) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    split_ifs with h
    · have h1 := ha p.1
      have h2 := ha p.2
      field_simp
    · simp
  rw [hm, hP, ← Finset.prod_mul_distrib, hsplit, hL, hJ, hU, hD, ← key]
  ring

end Real

end PI.LocJacOrd.W.Ar

namespace PI.LocJacOrd.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacOrd

/- English proof (translation)
Introduce `typed g r m ht`. Establish `hJ : jacS v typed g r = ∏ l : Fin r, ((∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)), absV v (alp v r i) ^ 2) ^ 2) ^ 2`. Rewrite using `[jacS]`. Use `Finset.prod_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg ht, mul_one, Ar.absV_prod_sq]`.

Rewrite using `[hJ]`. Conclude with `Ar.arith_real r m (fun i => absV v (alp v r i)) (fun i => Ar.absV_ne_zero v (Ar.alp_ne_zero v r i))`.
-/
theorem arithO_holds {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ArithO (F := F) v := by
  intro typed g r m ht
  have hJ : jacS v typed g r = ∏ l : Fin r, ((∏ i ∈ Finset.univ.filter
      (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)), absV v (alp v r i) ^ 2) ^ 2) ^ 2 := by
    rw [jacS]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [if_neg ht, mul_one, Ar.absV_prod_sq]
  rw [hJ]
  exact Ar.arith_real r m (fun i => absV v (alp v r i)) (fun i => Ar.absV_ne_zero v (Ar.alp_ne_zero v r i))

end PI.LocJacOrd.W
