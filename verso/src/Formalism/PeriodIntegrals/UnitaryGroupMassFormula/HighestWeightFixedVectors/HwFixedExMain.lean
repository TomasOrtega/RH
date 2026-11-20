import Formalism.PeriodIntegrals.HwFixedLine
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightFixedVectors.MonomialMemGe

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV MvPolynomial Matrix

namespace PI.HwFix.UnitaryGroupMassFormula

def wt (ι : Type) (n : ℕ) : ι × Fin n × Fin n → ℕ := fun v => n - (v.2.1 : ℕ)

def tor (n : ℕ) (s : ℂˣ) : GL (Fin n) ℂ :=
  ⟨diagonal (fun a => ((s ^ (n - (a : ℕ)) : ℂˣ) : ℂ)), diagonal (fun a => (((s ^ (n - (a : ℕ)))⁻¹ : ℂˣ) : ℂ)),
    by rw [diagonal_mul_diagonal]; simp, by rw [diagonal_mul_diagonal]; simp⟩

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem trAct_tor {ι : Type} [Fintype ι] (n : ℕ) (s : ℂˣ) :
    trAct (fun _ : ι => tor n s) = sc (wt ι n) (s : ℂ) := by
  apply MvPolynomial.algHom_ext
  intro v
  obtain ⟨τ, a, c⟩ := v
  simp only [Formalism.L2.DIV.trAct, Formalism.GradedWeylDivisibility.blockAct, sc, MvPolynomial.aeval_X, wt, tor]
  rw [Finset.sum_eq_single a]
  · simp [Matrix.transpose_apply]
  · intro b _ hb
    simp [Matrix.transpose_apply, Matrix.diagonal_apply_ne _ hb]
  · simp

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem detTwK_ne {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (g : ι → GL (Fin n) ℂ) :
    detTwK lam g ≠ 0 := by
  unfold Formalism.L2.DIV.detTwK Formalism.BasicNotions.detPow
  exact Finset.prod_ne_zero_iff.mpr (fun τ _ => Units.ne_zero _)

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem detTwK_uni {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (g : ι → GL (Fin n) ℂ) (hg : MtwUni g) :
    detTwK lam g = 1 := by
  unfold Formalism.L2.DIV.detTwK Formalism.BasicNotions.detPow
  refine Finset.prod_eq_one (fun τ _ => ?_)

  have hd : Matrix.GeneralLinearGroup.det (g τ) = 1 := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.det_of_upperTriangular (fun i j hij => (hg τ).1 i j hij)]
    simp [(hg τ).2]
  rw [hd, _root_.one_zpow, Units.val_one]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem uni_X {ι : Type} [Fintype ι] {n : ℕ} (g : ι → GL (Fin n) ℂ) (hg : MtwUni g) (v : ι × Fin n × Fin n) :
    trAct g (X v) - X v ∈ Ge (wt ι n) (wt ι n v + 1) := by
  obtain ⟨τ, a, c⟩ := v
  have hX : ∀ u : ι × Fin n × Fin n, wt ι n (τ, a, c) + 1 ≤ wt ι n u →
      (X u : MvPolynomial (ι × Fin n × Fin n) ℂ) ∈ Ge (wt ι n) (wt ι n (τ, a, c) + 1) := by
    intro u hu
    show ∀ m, Finsupp.weight (wt ι n) m < _ → coeff m (X u) = 0
    intro m hm
    classical
    rw [MvPolynomial.coeff_X', if_neg]
    rintro rfl
    simp [Finsupp.weight_apply, Finsupp.sum_single_index] at hm
    omega
  simp only [Formalism.L2.DIV.trAct, Formalism.GradedWeylDivisibility.blockAct, MvPolynomial.aeval_X]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
  simp only [Matrix.transpose_apply, (hg τ).2 a, map_one, one_mul, add_sub_cancel_right]
  refine Submodule.sum_mem _ (fun b hb => ?_)
  have hba : b ≠ a := Finset.ne_of_mem_erase hb
  rcases lt_or_gt_of_ne hba with hlt | hgt
  · rw [MvPolynomial.C_mul']
    refine Submodule.smul_mem _ _ (hX _ ?_)
    simp only [wt]
    have := a.isLt
    have : (b : ℕ) < a := hlt
    omega
  · rw [(hg τ).1 b a hgt, map_zero, zero_mul]
    exact Submodule.zero_mem _

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Proceed by induction. Treat this case separately.

Extract witnesses or component facts from the available result. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression. Treat this case separately. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
-/
theorem vv_bound {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) :
    ∃ D : ℕ, ∀ F ∈ VV ℂ lam, ∀ k, D < k → weightedHomogeneousComponent (wt ι n) k F = 0 := by
  classical
  refine ⟨Finset.univ.sup fun i => (bVVfun ℂ lam i).support.sup (Finsupp.weight (wt ι n)), ?_⟩
  intro F hF k hk
  rw [← (bVVfun_spec ℂ lam).2] at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    ext m
    rw [coeff_weightedHomogeneousComponent, coeff_zero]
    split_ifs with h
    · by_contra hc
      have h1 := Finset.le_sup (f := Finsupp.weight (wt ι n)) (mem_support_iff.mpr hc)
      have h2 := Finset.le_sup (f := fun i => (bVVfun ℂ lam i).support.sup (Finsupp.weight (wt ι n)))
        (Finset.mem_univ i)
      omega
    · rfl
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [map_smul, hx, smul_zero]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem hwFixedEx_main : HwFixedEx := by
  classical
  intro ι _ n lam S hS hstab
  obtain ⟨D, hD⟩ := vv_bound lam
  let w := wt ι n
  let S' : Submodule ℂ (Pol ℂ ι n) := S.map (VV ℂ lam).subtype
  have hS'VV : ∀ F ∈ S', F ∈ VV ℂ lam := by
    intro F hF
    obtain ⟨x, _, rfl⟩ := Submodule.mem_map.mp hF
    exact x.2
  have hS'act : ∀ g F, F ∈ S' → actP lam g F ∈ S' := by
    intro g F hF
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hF
    exact Submodule.mem_map.mpr ⟨rhoK lam g x, hstab g x hx, rfl⟩
  have hS'tor : ∀ s : ℂˣ, ∀ F ∈ S', sc w (s : ℂ) F ∈ S' := by
    intro s F hF
    have h := S'.smul_mem (detTwK lam (fun _ : ι => tor n s))⁻¹ (hS'act (fun _ => tor n s) F hF)
    rw [actP, LinearMap.smul_apply, smul_smul, inv_mul_cancel₀ (detTwK_ne lam _), one_smul,
      AlgHom.toLinearMap_apply, trAct_tor] at h
    exact h
  have hS'P : ∀ F ∈ S', ∀ k, weightedHomogeneousComponent w k F ∈ S' := by
    intro F hF k
    by_cases hk : k < F.support.sup (Finsupp.weight w) + 1
    · refine coeffs_mem S' _ (fun j => weightedHomogeneousComponent w j F) ?_ k hk
      intro c hc
      have h := hS'tor (Units.mk0 c hc) F hF
      rwa [Units.val_mk0, sc_eq_sum w c F (F.support.sup (Finsupp.weight w) + 1)
        (fun m hm => Nat.lt_succ_of_le (Finset.le_sup hm))] at h
    · have h0 : weightedHomogeneousComponent w k F = 0 := by
        ext m
        rw [coeff_weightedHomogeneousComponent, coeff_zero]
        split_ifs with h
        · by_contra hc
          have := Finset.le_sup (f := Finsupp.weight w) (mem_support_iff.mpr hc)
          omega
        · rfl
      rw [h0]
      exact S'.zero_mem
  obtain ⟨x, hxS, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  have hx0' : (x : Pol ℂ ι n) ≠ 0 := fun h => hx0 (Subtype.ext h)
  obtain ⟨m0, hm0⟩ := MvPolynomial.ne_zero_iff.mp hx0'
  let good : ℕ → Prop := fun k => ∃ G ∈ S', weightedHomogeneousComponent w k G ≠ 0
  have hxS' : (x : Pol ℂ ι n) ∈ S' := Submodule.mem_map.mpr ⟨x, hxS, rfl⟩
  have hgood0 : good (Finsupp.weight w m0) := by
    refine ⟨x, hxS', fun h => hm0 ?_⟩
    have := congrArg (coeff m0) h
    rwa [coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero] at this
  have hbound : ∀ k, good k → k ≤ D := by
    rintro k ⟨G, hG, hne⟩
    by_contra h
    exact hne (hD G (hS'VV G hG) k (by omega))
  obtain ⟨G, hG, hGne⟩ : good (Nat.findGreatest good D) := Nat.findGreatest_spec (hbound _ hgood0) hgood0
  have hmax : ∀ k, Nat.findGreatest good D < k → ∀ F ∈ S', weightedHomogeneousComponent w k F = 0 := by
    intro k hk F hF
    by_cases hkD : k ≤ D
    · by_contra hne
      exact Nat.findGreatest_is_greatest hk hkD ⟨F, hF, hne⟩
    · exact hD F (hS'VV F hF) k (by omega)
  have hvGe : weightedHomogeneousComponent w (Nat.findGreatest good D) G ∈ Ge w (Nat.findGreatest good D) := by
    rw [mem_Ge]
    intro m hm
    rw [coeff_weightedHomogeneousComponent, if_neg (ne_of_lt hm)]
  obtain ⟨v0, hv0S, hv0⟩ := Submodule.mem_map.mp (hS'P G hG (Nat.findGreatest good D))
  refine ⟨v0, hv0S, fun h => hGne ?_, ?_⟩
  · rw [← hv0, h, map_zero]
  · intro g hg
    apply Subtype.ext
    show actP lam g (v0 : Pol ℂ ι n) = v0
    have hv0' : ((v0 : VV ℂ lam) : Pol ℂ ι n) = weightedHomogeneousComponent w (Nat.findGreatest good D) G := hv0
    rw [hv0', actP, LinearMap.smul_apply, detTwK_uni lam g hg, one_smul, AlgHom.toLinearMap_apply]
    have hd := uni_step w (trAct g) (uni_X g hg) _ _ hvGe
    have hd' : trAct g (weightedHomogeneousComponent w (Nat.findGreatest good D) G) -
        weightedHomogeneousComponent w (Nat.findGreatest good D) G ∈ S' := by
      refine S'.sub_mem ?_ (hS'P G hG _)
      have := hS'act g _ (hS'P G hG (Nat.findGreatest good D))
      rwa [actP, LinearMap.smul_apply, detTwK_uni lam g hg, one_smul, AlgHom.toLinearMap_apply] at this
    rw [← sub_eq_zero]
    ext m
    rw [coeff_zero]
    by_cases hm : Finsupp.weight w m < Nat.findGreatest good D + 1
    · exact mem_Ge.1 hd m hm
    · have := congrArg (coeff m) (hmax (Finsupp.weight w m) (by omega) _ hd')
      rwa [coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero] at this

end PI.HwFix.UnitaryGroupMassFormula
