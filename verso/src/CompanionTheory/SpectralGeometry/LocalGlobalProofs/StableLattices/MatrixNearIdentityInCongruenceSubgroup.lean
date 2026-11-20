import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaE

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

section SlopeTestRemainingChoices

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}

/- English proof (translation)
The claim follows from `_root_.Bl.FirstLemmaE.goal1 s f g h0 hf hg hfg`.
-/
theorem norm_prod_sub_prod_le {ι : Type} (s : Finset ι) (f g : ι → L) {r : ℝ} (h0 : 0 ≤ r)
    (hf : ∀ i, ‖f i‖ ≤ 1) (hg : ∀ i, ‖g i‖ ≤ 1) (hfg : ∀ i, ‖f i - g i‖ ≤ r) :
    ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ ≤ r :=
  _root_.Bl.FirstLemmaE.goal1 s f g h0 hf hg hfg

/- English proof (translation)
Rewrite using `[Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0 fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[← smul_sub]`. Establish `h` using `norm_prod_sub_prod_le Finset.univ (fun i => A (σ i) i) (fun i => B (σ i) i) h0 (fun i => hA _ _) (fun i => hB _ _) (fun i => by simpa using hAB (σ i) i)`. Establish `h' : ‖∏ i, B (σ i) i - ∏ i, A (σ i) i‖ ≤ r`.

Rewrite using `[norm_sub_rev]`. Conclude with `h`. Break down `Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs` into its components or cases. Simplify `h` using `[hs, Units.smul_def]`. Simplify `h'` using `[hs, Units.smul_def]`.
-/
theorem norm_det_sub_det_le {A B : Matrix (Fin n) (Fin n) L} {r : ℝ} (h0 : 0 ≤ r)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ i j, ‖B i j‖ ≤ 1) (hAB : ∀ i j, ‖(A - B) i j‖ ≤ r) :
    ‖A.det - B.det‖ ≤ r := by
  rw [Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0 fun σ _ => ?_
  rw [← smul_sub]
  have h := norm_prod_sub_prod_le Finset.univ (fun i => A (σ i) i) (fun i => B (σ i) i) h0
    (fun i => hA _ _) (fun i => hB _ _) (fun i => by simpa using hAB (σ i) i)
  have h' : ‖∏ i, B (σ i) i - ∏ i, A (σ i) i‖ ≤ r := by
    rw [norm_sub_rev]
    exact h
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa [hs, Units.smul_def] using h
  · simpa [hs, Units.smul_def] using h'

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_` and prove the remaining obligations. Establish `h : ‖∏ i, A (σ i) i‖ ≤ 1`. Rewrite using `[norm_prod]`. Conclude with `Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => hA _ _`.

Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simpa [hs, Units.smul_def] using h`.
-/
theorem norm_det_le_one {A : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, ‖A i j‖ ≤ 1) : ‖A.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  have h : ‖∏ i, A (σ i) i‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => hA _ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simpa [hs, Units.smul_def] using h

/- English proof (translation)
Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Rewrite using `[Matrix.one_apply_eq, norm_one]`. Rewrite using `[Matrix.one_apply_ne h, norm_zero]`. Conclude with `zero_le_one`.
-/
theorem norm_one_entry_le (i j : Fin n) : ‖(1 : Matrix (Fin n) (Fin n) L) i j‖ ≤ 1 := by
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, norm_one]
  · rw [Matrix.one_apply_ne h, norm_zero]
    exact zero_le_one

/- English proof (translation)
Rewrite using `[Matrix.adjugate_apply]`. Use `norm_det_le_one fun a b => ?_` and prove the remaining obligations. Distinguish the cases in `h : a = j`. Substitute `h` using the available equality. Rewrite using `[Matrix.updateRow_self]`.

Distinguish the cases in `h' : b = i`. Simplify using `[h']`. Simplify using `[Pi.single_eq_of_ne h']`. Rewrite using `[Matrix.updateRow_ne h]`. Conclude with `hA a b`.
-/
theorem norm_adjugate_entry_le {A : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, ‖A i j‖ ≤ 1) (i j : Fin n) :
    ‖A.adjugate i j‖ ≤ 1 := by
  rw [Matrix.adjugate_apply]
  refine norm_det_le_one fun a b => ?_
  by_cases h : a = j
  · subst h
    rw [Matrix.updateRow_self]
    by_cases h' : b = i
    · simp [h']
    · simp [Pi.single_eq_of_ne h']
  · rw [Matrix.updateRow_ne h]
    exact hA a b

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `L _ _ n r h0 h1 hr A hA`. Establish `hA1 : ∀ i j, ‖A i j‖ ≤ 1`. Introduce `i j`. Establish `e : A i j = (A - 1) i j + (1 : Matrix (Fin n) (Fin n) L) i j` using `by simp`. Rewrite using `[e]`.

Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((hA i j).trans h1) (norm_one_entry_le i j))`. Establish `hd : ‖A.det - 1‖ ≤ r`. Use `norm_det_sub_det_le h0 hA1 norm_one_entry_le hA` as an intermediate fact. Rewrite `this` using `[Matrix.det_one]`. Then use the resulting hypothesis. Establish `hd1 : 1 ≤ ‖A.det‖`.

Establish `e : (1 : L) = A.det + -(A.det - 1)` using `by ring`. Establish `h2 : ‖(1 : L)‖ ≤ max ‖A.det‖ ‖A.det - 1‖` using `by conv_lhs => rw [e]`. Rewrite using `[← norm_neg (A.det - 1)]`. Conclude with `IsUltrametricDist.norm_add_le_max _ _`. Rewrite `h2` using `[norm_one]`.

Break down `le_max_iff.mp h2 with h | h` into its components or cases. Conclude with `h`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hne : A.det ≠ 0`. Introduce `h`.

Rewrite `hd1` using `[h, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hinv : ∀ i j, ‖A⁻¹ i j‖ ≤ 1`. Introduce `i j`. Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv]`.

Conclude with `mul_le_one₀ (inv_le_one_of_one_le₀ hd1) (norm_nonneg _) (norm_adjugate_entry_le hA1 i j)`. Establish `hu : IsUnit A.det` using `isUnit_iff_ne_zero.mpr hne`. Establish `hk : ((Matrix.GeneralLinearGroup.mkOfDetNeZero A hne : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = A` using `rfl`. Use `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hne, ?_, hk⟩` and prove the remaining obligations. Rewrite using `[mem_congK]`.

Introduce `i j`. Use `⟨by rw [hk]; exact hA i j, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.coe_units_inv, hk]`. Establish `e : A⁻¹ - 1 = -(A⁻¹ * (A - 1))`. Rewrite using `[Matrix.mul_sub, Matrix.nonsing_inv_mul A hu, Matrix.mul_one]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e, Matrix.neg_apply, norm_neg]`. Simplify using `using entry_mul zero_le_one h0 hinv hA i j`.
-/
theorem exists_mem_congK_of_entries : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L]
    (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1), r < 1 → ∀ A : Matrix (Fin n) (Fin n) L,
    (∀ i j, ‖(A - 1) i j‖ ≤ r) →
    ∃ k ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1, (k : Matrix (Fin n) (Fin n) L) = A := by
  intro L _ _ n r h0 h1 hr A hA
  have hA1 : ∀ i j, ‖A i j‖ ≤ 1 := by
    intro i j
    have e : A i j = (A - 1) i j + (1 : Matrix (Fin n) (Fin n) L) i j := by simp
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ((hA i j).trans h1) (norm_one_entry_le i j))
  have hd : ‖A.det - 1‖ ≤ r := by
    have := norm_det_sub_det_le h0 hA1 norm_one_entry_le hA
    rwa [Matrix.det_one] at this
  have hd1 : 1 ≤ ‖A.det‖ := by
    have e : (1 : L) = A.det + -(A.det - 1) := by ring
    have h2 : ‖(1 : L)‖ ≤ max ‖A.det‖ ‖A.det - 1‖ := by
      conv_lhs => rw [e]
      rw [← norm_neg (A.det - 1)]
      exact IsUltrametricDist.norm_add_le_max _ _
    rw [norm_one] at h2
    rcases le_max_iff.mp h2 with h | h
    · exact h
    · linarith
  have hne : A.det ≠ 0 := by
    intro h
    rw [h, norm_zero] at hd1
    linarith
  have hinv : ∀ i j, ‖A⁻¹ i j‖ ≤ 1 := by
    intro i j
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv]
    exact mul_le_one₀ (inv_le_one_of_one_le₀ hd1) (norm_nonneg _) (norm_adjugate_entry_le hA1 i j)
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hne
  have hk : ((Matrix.GeneralLinearGroup.mkOfDetNeZero A hne : GL (Fin n) L) :
      Matrix (Fin n) (Fin n) L) = A := rfl
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hne, ?_, hk⟩
  rw [mem_congK]
  intro i j
  refine ⟨by rw [hk]; exact hA i j, ?_⟩
  rw [Matrix.coe_units_inv, hk]
  have e : A⁻¹ - 1 = -(A⁻¹ * (A - 1)) := by
    rw [Matrix.mul_sub, Matrix.nonsing_inv_mul A hu, Matrix.mul_one]
    abel
  rw [e, Matrix.neg_apply, norm_neg]
  simpa using entry_mul zero_le_one h0 hinv hA i j

end GlobalTheory.CompanionTheory.CartGL
