import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.PMinorAff

noncomputable section

open scoped BigOperators
open Classical

namespace PI.EntAtD.W

open PI.EntAtD

/- English proof (translation)
Establish `hs1 : (κ - κ2).support ⊆ κ.support`. Introduce `v hv`. Rewrite `hv` using `[Finsupp.mem_support_iff, Finsupp.tsub_apply]`. Rewrite using `[Finsupp.mem_support_iff]`. Use linear arithmetic over natural numbers and integers.

Establish `hs2 : κ2.support ⊆ κ.support`. Introduce `v hv`. Rewrite `hv`, the goal using `[Finsupp.mem_support_iff]`. Use `h v` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite using `[Finsupp.prod_of_support_subset _ hs1 _ (fun _ _ => by simp), Finsupp.prod_of_support_subset _ hs2 _ (fun _ _ => by simp), Finsupp.prod_of_support_subset κ subset_rfl _ (fun _ _ => by simp)]`. Simplify using `only [binomF]`. Rewrite using `[Nat.cast_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.tsub_apply, mul_right_comm]`.

Conclude with `(Nat.choose_mul_factorial_mul_factorial (h v)).symm` after adjusting the coercions.
-/
theorem fprod_split_cast {H : Type} {N0 N1 p : ℕ} [Fact p.Prime] (κ κ2 : ZV H N0 N1 →₀ ℕ) (h : κ2 ≤ κ) :
    (κ.prod fun _ k => (k.factorial : ℂ_[p])) =
      ((binomF κ κ2 : ℕ) : ℂ_[p]) * ((κ - κ2).prod fun _ k => (k.factorial : ℂ_[p])) *
        (κ2.prod fun _ k => (k.factorial : ℂ_[p])) := by
  classical
  have hs1 : (κ - κ2).support ⊆ κ.support := by
    intro v hv
    rw [Finsupp.mem_support_iff, Finsupp.tsub_apply] at hv
    rw [Finsupp.mem_support_iff]
    omega
  have hs2 : κ2.support ⊆ κ.support := by
    intro v hv
    rw [Finsupp.mem_support_iff] at hv ⊢
    have := h v
    omega
  rw [Finsupp.prod_of_support_subset _ hs1 _ (fun _ _ => by simp),
    Finsupp.prod_of_support_subset _ hs2 _ (fun _ _ => by simp),
    Finsupp.prod_of_support_subset κ subset_rfl _ (fun _ _ => by simp)]
  simp only [binomF]
  rw [Nat.cast_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finsupp.tsub_apply, mul_right_comm]
  exact_mod_cast (Nat.choose_mul_factorial_mul_factorial (h v)).symm

/- English proof (translation)
Rewrite using `[MvPowerSeries.coeff_mul, Finset.mul_sum]`. Use `Finset.sum_nbij' (fun x => x.2) (fun κ2 => (κ - κ2, κ2)) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `x hx`. Simplify using `at hx`. Simplify using `only [Finset.mem_coe, Finset.mem_Iic]`.

Rewrite using `[← hx]`. Conclude with `le_add_self`. Introduce `κ2 hκ2`. Simplify using `only [Finset.mem_coe, Finset.mem_Iic] at hκ2`. Simplify using `using tsub_add_cancel_of_le hκ2`.

Introduce `x hx`. Simplify using `at hx`. Use `Prod.ext ?_ rfl` and prove the remaining obligations. Use `show κ - x.2 = x.1`. Rewrite using `[← hx, add_tsub_cancel_right]`.

Introduce `κ2 _`. Both sides reduce to the same expression. Introduce `x hx`. Simplify using `at hx`. Establish `hle : x.2 ≤ κ`.

Rewrite using `[← hx]`. Conclude with `le_add_self`. Establish `h1 : κ - x.2 = x.1`. Rewrite using `[← hx, add_tsub_cancel_right]`. Rewrite using `[fprod_split_cast κ x.2 hle, h1]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem fcoeff_mul {H : Type} [DecidableEq H] {N0 N1 p : ℕ} [Fact p.Prime] (E sg : MvPowerSeries (ZV H N0 N1) ℂ_[p])
    (κ : ZV H N0 N1 →₀ ℕ) :
    (κ.prod fun _ k => (k.factorial : ℂ_[p])) * MvPowerSeries.coeff κ (E * sg) =
      ∑ κ2 ∈ Finset.Iic κ, ((binomF κ κ2 : ℕ) : ℂ_[p]) *
        (((κ - κ2).prod fun _ k => (k.factorial : ℂ_[p])) * MvPowerSeries.coeff (κ - κ2) E) *
        ((κ2.prod fun _ k => (k.factorial : ℂ_[p])) * MvPowerSeries.coeff κ2 sg) := by
  rw [MvPowerSeries.coeff_mul, Finset.mul_sum]
  refine Finset.sum_nbij' (fun x => x.2) (fun κ2 => (κ - κ2, κ2)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp at hx
    simp only [Finset.mem_coe, Finset.mem_Iic]
    rw [← hx]
    exact le_add_self
  · intro κ2 hκ2
    simp only [Finset.mem_coe, Finset.mem_Iic] at hκ2
    simpa using tsub_add_cancel_of_le hκ2
  · intro x hx
    simp at hx
    refine Prod.ext ?_ rfl
    show κ - x.2 = x.1
    rw [← hx, add_tsub_cancel_right]
  · intro κ2 _
    rfl
  · intro x hx
    simp at hx
    have hle : x.2 ≤ κ := by
      rw [← hx]
      exact le_add_self
    have h1 : κ - x.2 = x.1 := by
      rw [← hx, add_tsub_cancel_right]
    rw [fprod_split_cast κ x.2 hle, h1]
    ring

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.tsub_apply]`. Conclude with `tsub_le_self.trans (by first`. Consider the case `exact le_of_eq rfl`.

Consider the case `exact (Finsupp.snd_sumFinsuppEquivProdFinsupp _ _).le)`. Use `_ = ∑ x ∈ (Finset.univ : Finset (Fin N0 × Fin N1)).image (fun ab => (Sum.inr ((true, t), ab.1, ab.2) : XZ (Bool × H) N0 N1)), μ x := by`. Rewrite using `[Finset.sum_image (by intro x _ y _ h; simpa [Prod.ext_iff] using h), Fintype.sum_prod_type]`. Use `_ ≤ ∑ x ∈ μ.support, μ x := Finset.sum_le_sum_of_ne_zero fun x _ hx => Finsupp.mem_support_iff.2 hx`. Use `_ ≤ P.totalDegree := MvPolynomial.le_totalDegree hμ`.
-/
theorem prof_le_totalDegree {H : Type} {N0 N1 : ℕ} (P : PolyXZ H N0 N1) (μ : XZ (Bool × H) N0 N1 →₀ ℕ)
    (hμ : μ ∈ P.support) (κ2 : ZV H N0 N1 →₀ ℕ) (t : H) :
    ∑ a : Fin N0, ∑ b : Fin N1, (zpart μ - κ2) ((true, t), a, b) ≤ P.totalDegree := by
  classical
  calc ∑ a : Fin N0, ∑ b : Fin N1, (zpart μ - κ2) ((true, t), a, b)
      ≤ ∑ a : Fin N0, ∑ b : Fin N1, μ (Sum.inr ((true, t), a, b)) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        rw [Finsupp.tsub_apply]
        exact tsub_le_self.trans (by
          first
          | exact le_of_eq rfl
          | exact (Finsupp.snd_sumFinsuppEquivProdFinsupp _ _).le)
    _ = ∑ x ∈ (Finset.univ : Finset (Fin N0 × Fin N1)).image
          (fun ab => (Sum.inr ((true, t), ab.1, ab.2) : XZ (Bool × H) N0 N1)), μ x := by
        rw [Finset.sum_image (by intro x _ y _ h; simpa [Prod.ext_iff] using h), Fintype.sum_prod_type]
    _ ≤ ∑ x ∈ μ.support, μ x :=
        Finset.sum_le_sum_of_ne_zero fun x _ hx => Finsupp.mem_support_iff.2 hx
    _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hμ

/- English proof (translation)
Set `T : (XZ (Bool × H) N0 N1 →₀ ℕ) → (ZV H N0 N1 →₀ ℕ) → ℂ_[p]` to `fun μ κ2 => if xpart μ = m ∧ κ2 ≤ zpart μ ∧ (∀ t a b, (zpart μ - κ2) ((false, t), a, b) = (zpart μ - κ2) ((true, t), a, b)) then ((MvPolynomial.coeff μ P : ℤ) : ℂ_[p]) * ((binomF (zpart μ) κ2 : ℕ) : ℂ_[p]) * (∏ t : H, ∏ a : Fin N0, ∏ b : Fin N1, (((zpart μ - κ2) ((true, t), a, b) …`. Establish `hL : MvPolynomial.coeff m (applyAt0 N0 N1 p (E * sg) P) = ∑ μ ∈ P.support, ∑ κ2 ∈ P.support.biUnion (fun μ => Finset.Iic (zpart μ)), T μ κ2`. Simplify using `only [applyAt0, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]`. Use `Finset.sum_congr rfl fun μ hμ => ?_` and prove the remaining obligations. Distinguish the cases in `hx : xpart μ = m`.

Rewrite using `[if_pos hx, mul_assoc, fcoeff_mul, Finset.mul_sum]`. Rewrite using `[← Finset.sum_subset (Finset.subset_biUnion_of_mem (fun μ => Finset.Iic (zpart μ)) hμ) (fun κ2 _ hn => by`. Simplify using `only [T]`. Rewrite using `[if_neg]`. Conclude with `fun h => hn (Finset.mem_Iic.2 h.2.1))]`.

Use `Finset.sum_congr rfl fun κ2 hκ2 => ?_` and prove the remaining obligations. Establish `hle : κ2 ≤ zpart μ` using `Finset.mem_Iic.1 hκ2`. Rewrite using `[hE]`. Simplify using `only [T]`. Distinguish the cases in `hb : ∀ t a b, (zpart μ - κ2) ((false, t), a, b) = (zpart μ - κ2) ((true, t), a, b)`.

Rewrite using `[if_pos hb, if_pos ⟨hx, hle, hb⟩]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hb, if_neg (fun h => hb h.2.2)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hx]`.

Use `symm`. Use `Finset.sum_eq_zero fun κ2 _ => ?_` and prove the remaining obligations. Simplify using `only [T]`. Rewrite using `[if_neg]`. Conclude with `fun h => hx h.1`.

Establish `hR : (∑ κ2 ∈ P.support.biUnion (fun μ => Finset.Iic (zpart μ)), ∑ n ∈ Fintype.piFinset (fun _ : H => Finset.range (P.totalDegree + 1)), ((κ2.prod fun _ k => (k.factorial : ℂ_[p])) * MvPowerSeries.coeff κ2 sg) * (∏ t : H, (-(S * ut t)) ^ n t) * ((Acon P m κ2 n : ℤ) : ℂ_[p])) = ∑ κ …`. Use `Finset.sum_congr rfl fun κ2 _ => ?_` and prove the remaining obligations. Simplify using `only [Acon, Int.cast_sum, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun μ hμ => ?_` and prove the remaining obligations.

Distinguish the cases in `hQ : xpart μ = m ∧ κ2 ≤ zpart μ ∧ (∀ t a b, (zpart μ - κ2) ((false, t), a, b) = (zpart μ - κ2) ((true, t), a, b))`. Establish `hB : Bal N0 N1 (fun t => ∑ a : Fin N0, ∑ b : Fin N1, (zpart μ - κ2) ((true, t), a, b)) (zpart μ - κ2)` using `And.intro hQ.2.2 fun t => rfl`. Rewrite using `[Finset.sum_eq_single (fun t => ∑ a : Fin N0, ∑ b : Fin N1, (zpart μ - κ2) ((true, t), a, b))]`. Rewrite using `[if_pos ⟨hQ.1, hQ.2.1, hB⟩]`. Simplify using `only [T]`.

Rewrite using `[if_pos hQ]`. Use `push_cast`. Apply the tactic sequence `simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum] <;> ring`. Introduce `n _ hn`. Rewrite using `[if_neg, Int.cast_zero, mul_zero]`.

Introduce and unpack `⟨_, _, hB'⟩`. Conclude with `hn (funext fun t => (hB'.2 t).symm)`. Introduce `hn`. It suffices to derive a contradiction. Conclude with `hn (Fintype.mem_piFinset.2 fun t => Finset.mem_range.2 (Nat.lt_succ_of_le (prof_le_totalDegree P μ hμ κ2 t)))`.

Simplify using `only [T]`. Rewrite using `[if_neg hQ]`. Use `Finset.sum_eq_zero fun n _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg, Int.cast_zero, mul_zero]`. Introduce and unpack `⟨h1, h2, hB'⟩`.

Conclude with `hQ ⟨h1, h2, hB'.1⟩`. Rewrite using `[hL, hR, Finset.sum_comm]`.
-/
theorem expand_gen {H : Type} [Fintype H] [DecidableEq H] {N0 N1 p : ℕ} [Fact p.Prime] (S : ℂ_[p])
    (ut : H → ℂ_[p]) (E sg : MvPowerSeries (ZV H N0 N1) ℂ_[p])
    (hE : ∀ κ : ZV H N0 N1 →₀ ℕ, (κ.prod fun _ k => (k.factorial : ℂ_[p])) * MvPowerSeries.coeff κ E =
      if ∀ t a b, κ ((false, t), a, b) = κ ((true, t), a, b) then
        ∏ t : H, ∏ a : Fin N0, ∏ b : Fin N1,
          ((κ ((true, t), a, b)).factorial : ℂ_[p]) * (-(S * ut t)) ^ κ ((true, t), a, b)
      else 0)
    (P : PolyXZ H N0 N1) (m : XV H N0 →₀ ℕ) :
    MvPolynomial.coeff m (applyAt0 N0 N1 p (E * sg) P) =
      ∑ κ2 ∈ P.support.biUnion (fun μ => Finset.Iic (zpart μ)),
        ∑ n ∈ Fintype.piFinset (fun _ : H => Finset.range (P.totalDegree + 1)),
          ((κ2.prod fun _ k => (k.factorial : ℂ_[p])) * MvPowerSeries.coeff κ2 sg) *
            (∏ t : H, (-(S * ut t)) ^ n t) * ((Acon P m κ2 n : ℤ) : ℂ_[p]) := by
  classical
  let T : (XZ (Bool × H) N0 N1 →₀ ℕ) → (ZV H N0 N1 →₀ ℕ) → ℂ_[p] := fun μ κ2 =>
    if xpart μ = m ∧ κ2 ≤ zpart μ ∧
        (∀ t a b, (zpart μ - κ2) ((false, t), a, b) = (zpart μ - κ2) ((true, t), a, b)) then
      ((MvPolynomial.coeff μ P : ℤ) : ℂ_[p]) * ((binomF (zpart μ) κ2 : ℕ) : ℂ_[p]) *
        (∏ t : H, ∏ a : Fin N0, ∏ b : Fin N1,
          (((zpart μ - κ2) ((true, t), a, b)).factorial : ℂ_[p]) *
            (-(S * ut t)) ^ (zpart μ - κ2) ((true, t), a, b)) *
        ((κ2.prod fun _ k => (k.factorial : ℂ_[p])) * MvPowerSeries.coeff κ2 sg)
    else 0
  have hL : MvPolynomial.coeff m (applyAt0 N0 N1 p (E * sg) P) =
      ∑ μ ∈ P.support, ∑ κ2 ∈ P.support.biUnion (fun μ => Finset.Iic (zpart μ)), T μ κ2 := by
    simp only [applyAt0, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    by_cases hx : xpart μ = m
    · rw [if_pos hx, mul_assoc, fcoeff_mul, Finset.mul_sum]
      rw [← Finset.sum_subset (Finset.subset_biUnion_of_mem (fun μ => Finset.Iic (zpart μ)) hμ)
        (fun κ2 _ hn => by
          simp only [T]
          rw [if_neg]
          exact fun h => hn (Finset.mem_Iic.2 h.2.1))]
      refine Finset.sum_congr rfl fun κ2 hκ2 => ?_
      have hle : κ2 ≤ zpart μ := Finset.mem_Iic.1 hκ2
      rw [hE]
      simp only [T]
      by_cases hb : ∀ t a b, (zpart μ - κ2) ((false, t), a, b) = (zpart μ - κ2) ((true, t), a, b)
      · rw [if_pos hb, if_pos ⟨hx, hle, hb⟩]
        ring
      · rw [if_neg hb, if_neg (fun h => hb h.2.2)]
        ring
    · rw [if_neg hx]
      symm
      refine Finset.sum_eq_zero fun κ2 _ => ?_
      simp only [T]
      rw [if_neg]
      exact fun h => hx h.1
  have hR : (∑ κ2 ∈ P.support.biUnion (fun μ => Finset.Iic (zpart μ)),
        ∑ n ∈ Fintype.piFinset (fun _ : H => Finset.range (P.totalDegree + 1)),
          ((κ2.prod fun _ k => (k.factorial : ℂ_[p])) * MvPowerSeries.coeff κ2 sg) *
            (∏ t : H, (-(S * ut t)) ^ n t) * ((Acon P m κ2 n : ℤ) : ℂ_[p])) =
      ∑ κ2 ∈ P.support.biUnion (fun μ => Finset.Iic (zpart μ)), ∑ μ ∈ P.support, T μ κ2 := by
    refine Finset.sum_congr rfl fun κ2 _ => ?_
    simp only [Acon, Int.cast_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    by_cases hQ : xpart μ = m ∧ κ2 ≤ zpart μ ∧
        (∀ t a b, (zpart μ - κ2) ((false, t), a, b) = (zpart μ - κ2) ((true, t), a, b))
    · have hB : Bal N0 N1 (fun t => ∑ a : Fin N0, ∑ b : Fin N1, (zpart μ - κ2) ((true, t), a, b))
          (zpart μ - κ2) := And.intro hQ.2.2 fun t => rfl
      rw [Finset.sum_eq_single (fun t => ∑ a : Fin N0, ∑ b : Fin N1, (zpart μ - κ2) ((true, t), a, b))]
      · rw [if_pos ⟨hQ.1, hQ.2.1, hB⟩]
        simp only [T]
        rw [if_pos hQ]
        push_cast
        simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum] <;> ring
      · intro n _ hn
        rw [if_neg, Int.cast_zero, mul_zero]
        rintro ⟨_, _, hB'⟩
        exact hn (funext fun t => (hB'.2 t).symm)
      · intro hn
        exfalso
        exact hn (Fintype.mem_piFinset.2 fun t =>
          Finset.mem_range.2 (Nat.lt_succ_of_le (prof_le_totalDegree P μ hμ κ2 t)))
    · simp only [T]
      rw [if_neg hQ]
      refine Finset.sum_eq_zero fun n _ => ?_
      rw [if_neg, Int.cast_zero, mul_zero]
      rintro ⟨h1, h2, hB'⟩
      exact hQ ⟨h1, h2, hB'.1⟩
  rw [hL, hR, Finset.sum_comm]

/- English proof (translation)
Introduce `H _ _ N0 N1 p _ S ut sg P m`. Conclude with `expand_gen S ut _ sg (fun κ => hX H N0 N1 p S ut κ) P m`.
-/
theorem expand_of (hX : PExpCoeff) : PExpand := by
  intro H _ _ N0 N1 p _ S ut sg P m
  exact expand_gen S ut _ sg (fun κ => hX H N0 N1 p S ut κ) P m

end PI.EntAtD.W
