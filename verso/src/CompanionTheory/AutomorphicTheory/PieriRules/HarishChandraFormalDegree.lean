import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.FormalDegreeConstantDiscrete
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.FinalExists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiGelfand
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeSquareIntegrable.Closed
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFormalDegree.VUnitInvVal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.HpkMulMulHpkApply

open MeasureTheory Matrix Finset

noncomputable section

namespace CompanionTheory.PieriExpansion.Fd

open PI.UpqRep ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

/- English proof (translation)
Establish `hq : S7.q0 ε ≤ n` using `(min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))`. Establish `hq' : (S7.q0 ε : ℝ) ≤ n` using `by exact_mod_cast hq`. Establish `hn' : (1 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hs : Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ 2 * n`. Rewrite using `[Real.sqrt_le_left (by positivity)]`.

Use polynomial arithmetic with `[(Nat.cast_nonneg (S7.q0 ε) : (0 : ℝ) ≤ _)]`. Establish `h1 : (n : ℝ) * (S7.q0 ε : ℝ) ≤ n * n` using `mul_le_mul_of_nonneg_left hq' (by positivity)`. Unfold `G2.thrS`. Apply the tactic sequence `rcases max_cases (2 * (n : ℝ)) (16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ))) with h2 | h2 <;>`. Apply the tactic sequence `rw [h2.1] <;> nlinarith`.
-/
theorem thrS_lt (ε : Fin n → Bool) (hn : 1 ≤ n) {h : ℝ} (hh : 43 * (n : ℝ) ^ 2 ≤ h) : G2.thrS ε + 1 < h := by
  have hq : S7.q0 ε ≤ n := (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))
  have hq' : (S7.q0 ε : ℝ) ≤ n := by exact_mod_cast hq
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ 2 * n := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [(Nat.cast_nonneg (S7.q0 ε) : (0 : ℝ) ≤ _)]
  have h1 : (n : ℝ) * (S7.q0 ε : ℝ) ≤ n * n := mul_le_mul_of_nonneg_left hq' (by positivity)
  unfold G2.thrS
  rcases max_cases (2 * (n : ℝ)) (16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ))) with h2 | h2 <;>
    rw [h2.1] <;> nlinarith

def HCFdegG : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), 1 ≤ pOf ε → 1 ≤ qOf ε → ∃ c : ℝ, 0 < c ∧
    ∀ (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ →
      ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h → G2.thrS ε + 1 < h → IsFdeg (muG ε) σ (c * fdegHC lam)

/- English proof (translation)
Introduce `n ε hp hq`. Take `⟨c, hc, hF⟩` from `G2.formal_degree_constant_measure n ε`. Use `⟨c, hc, fun lam H _ _ _ σ hl hσ h hg hh => ?_⟩` and prove the remaining obligations. Use `hσ.2.1` as an intermediate fact. Take `⟨d, hd⟩` from `PIW.HCFdeg.formal_degree_abstract_form n ε H σ hσ.2.2.1 hσ.2.2.2.1 hσ.2.2.2.2.1`.

Take `⟨v, hv⟩` from `exists_ne (0 : H)`. Establish `h8 : 8 * (n : ℝ) * (S7.q0 ε : ℝ) < h`. Establish `h16` using `(le_max_right _ _).trans_lt (lt_of_le_of_lt (le_add_of_nonneg_right zero_le_one) hh)`. Establish `hs : 0 ≤ Real.sqrt (2 * (S7.q0 ε : ℝ))` using `Real.sqrt_nonneg _`. Establish `hnq : 0 ≤ (n : ℝ) * (S7.q0 ε : ℝ)` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Establish `h1` using `hF lam H σ v hl hσ h hg hh hp hq (fun μ hμ hgμ => by`. Take `⟨T⟩` from `HW.kType_exists ε μ hμ`. Take `⟨Ψ, hP, -⟩` from `exists_isPsiFor S7.psiExists T hμ hgμ (le_min hp hq) h8`. Conclude with `⟨T, Ψ, hP⟩) hv`.

Establish `h2` using `PI.UnitaryGroupMassFormula.FdegHpk.fdegOf_eq (muG ε) σ d v hd hv`. Establish `h3 : d = c * fdegHC lam` using `h2.symm.trans h1`. Rewrite using `[← h3]` and apply the resulting hypothesis.
-/
theorem harish_chandra_formal_degree : HCFdegG := by
  intro n ε hp hq
  obtain ⟨c, hc, hF⟩ := G2.formal_degree_constant_measure n ε
  refine ⟨c, hc, fun lam H _ _ _ σ hl hσ h hg hh => ?_⟩
  have := hσ.2.1
  obtain ⟨d, hd⟩ := PIW.HCFdeg.formal_degree_abstract_form n ε H σ hσ.2.2.1 hσ.2.2.2.1 hσ.2.2.2.2.1
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  have h8 : 8 * (n : ℝ) * (S7.q0 ε : ℝ) < h := by
    have h16 := (le_max_right _ _).trans_lt (lt_of_le_of_lt (le_add_of_nonneg_right zero_le_one) hh)
    have hs : 0 ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
    have hnq : 0 ≤ (n : ℝ) * (S7.q0 ε : ℝ) := by positivity
    nlinarith
  have h1 := hF lam H σ v hl hσ h hg hh hp hq (fun μ hμ hgμ => by
    obtain ⟨T⟩ := HW.kType_exists ε μ hμ
    obtain ⟨Ψ, hP, -⟩ := exists_isPsiFor S7.psiExists T hμ hgμ (le_min hp hq) h8
    exact ⟨T, Ψ, hP⟩) hv
  have h2 := PI.UnitaryGroupMassFormula.FdegHpk.fdegOf_eq (muG ε) σ d v hd hv
  have h3 : d = c * fdegHC lam := h2.symm.trans h1
  rwa [← h3]

/- English proof (translation)
The claim follows from `G2.final_existsG_of (fun _ => S7.psiExists) n ε lam hl h hg hh`.
-/
theorem dsExistsG (ε : Fin n → Bool) (lam : Fin n → ℝ) (hl : IsHCParam lam) {h : ℝ}
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (hh : G2.thrS ε < h) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ :=
  G2.final_existsG_of (fun _ => S7.psiExists) n ε lam hl h hg hh

section Hpk

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

/- English proof (translation)
Assume the negation of the conclusion as `h0`. Establish `hall : ∀ a, ε a = true` using `fun a => by`. Assume the negation of the conclusion as `ha`. Conclude with `h0 (Finset.card_pos.2 ⟨a, by simpa using ha⟩)`. Establish `hJ : PI.UpqRep.Jm ε = 1` using `by simp [PI.UpqRep.Jm, hall]`.

Establish `h1` using `hP.1.2`. Rewrite `h1` using `[hJ, Matrix.mul_one, show Pᴴ * P = 1 from Matrix.mem_unitaryGroup_iff'.1 hP.2]`. Establish `h2` using `congrFun (congrFun h1 ⟨r + k, by omega⟩) ⟨r + k, by omega⟩`. Rewrite `h2` using `[Matrix.one_apply_eq, PI.HwUniqW.Hpk_apply, if_pos (Fin.ext (by rw [PI.HwUniqW.piI_val]; simp))]`. Simplify using `only [PI.HwUniqW.epsI, if_true] at h2`.

Evaluate the numerical expressions using `at h2`.
-/
theorem one_le_qOf (hP : IsCayleyU k r ε P) : 1 ≤ qOf ε := by
  by_contra h0
  have hall : ∀ a, ε a = true := fun a => by
    by_contra ha
    exact h0 (Finset.card_pos.2 ⟨a, by simpa using ha⟩)
  have hJ : PI.UpqRep.Jm ε = 1 := by simp [PI.UpqRep.Jm, hall]
  have h1 := hP.1.2
  rw [hJ, Matrix.mul_one, show Pᴴ * P = 1 from Matrix.mem_unitaryGroup_iff'.1 hP.2] at h1
  have h2 := congrFun (congrFun h1 ⟨r + k, by omega⟩) ⟨r + k, by omega⟩
  rw [Matrix.one_apply_eq, PI.HwUniqW.Hpk_apply, if_pos (Fin.ext (by rw [PI.HwUniqW.piI_val]; simp))] at h2
  simp only [PI.HwUniqW.epsI, if_true] at h2
  norm_num at h2

/- English proof (translation)
Assume the negation of the conclusion as `h0`. Establish `hall : ∀ a, ε a = false` using `fun a => by`. Assume the negation of the conclusion as `ha`. Conclude with `h0 (Finset.card_pos.2 ⟨a, by simpa using ha⟩)`. Establish `hJ : PI.UpqRep.Jm ε = -1`.

Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [PI.UpqRep.Jm, hall, h, Matrix.one_apply]`. Establish `h1` using `hP.1.2`. Rewrite `h1` using `[hJ, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, show Pᴴ * P = 1 from Matrix.mem_unitaryGroup_iff'.1 hP.2]`. Establish `h2` using `congrFun (congrFun h1 ⟨r, by omega⟩) ⟨r, by omega⟩`.

Rewrite `h2` using `[Matrix.neg_apply, Matrix.one_apply_eq, PI.HwUniqW.Hpk_apply, if_pos (Fin.ext (by rw [PI.HwUniqW.piI_val]; simp))]`. Simplify using `only [PI.HwUniqW.epsI] at h2`. Rewrite `h2` using `[if_neg (by omega)]`. Evaluate the numerical expressions using `at h2`.
-/
theorem one_le_pOf (hk : 1 ≤ k) (hP : IsCayleyU k r ε P) : 1 ≤ pOf ε := by
  by_contra h0
  have hall : ∀ a, ε a = false := fun a => by
    by_contra ha
    exact h0 (Finset.card_pos.2 ⟨a, by simpa using ha⟩)
  have hJ : PI.UpqRep.Jm ε = -1 := by
    ext i j
    by_cases h : i = j <;> simp [PI.UpqRep.Jm, hall, h, Matrix.one_apply]
  have h1 := hP.1.2
  rw [hJ, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, show Pᴴ * P = 1 from Matrix.mem_unitaryGroup_iff'.1 hP.2]
    at h1
  have h2 := congrFun (congrFun h1 ⟨r, by omega⟩) ⟨r, by omega⟩
  rw [Matrix.neg_apply, Matrix.one_apply_eq, PI.HwUniqW.Hpk_apply,
    if_pos (Fin.ext (by rw [PI.HwUniqW.piI_val]; simp))] at h2
  simp only [PI.HwUniqW.epsI] at h2
  rw [if_neg (by omega)] at h2
  norm_num at h2

/- English proof (translation)
Take `⟨H, _, _, σ, hσ⟩` from `dsExistsG ε lam hl hg hh`. Establish `hd` using `(Matrix.isUnit_iff_isUnit_det P).1 hP.1.1`. Use `⟨H, _, _, hσ.1, fun g => σ (P * g * P⁻¹), P, hP, ?_⟩` and prove the remaining obligations. Establish `e : (fun g => σ (P * (P⁻¹ * g * P) * P⁻¹)) = σ`. Use function extensionality and compare the values at `g`.

Use `congr 1`. Combine the equalities or inequalities in the displayed calculation. Use `show IsDS ε lam fun g => σ (P * (P⁻¹ * g * P) * P⁻¹)`. Rewrite using `[e]` and apply the resulting hypothesis.
-/
theorem dsExistsHpkG (hP : IsCayleyU k r ε P) (lam : Fin (2 * r + k + 1) → ℝ) (hl : IsHCParam lam) {h : ℝ}
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (hh : G2.thrS ε < h) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)), IsDSHpk k r ε lam σ := by
  obtain ⟨H, _, _, σ, hσ⟩ := dsExistsG ε lam hl hg hh
  have hd := (Matrix.isUnit_iff_isUnit_det P).1 hP.1.1
  refine ⟨H, _, _, hσ.1, fun g => σ (P * g * P⁻¹), P, hP, ?_⟩
  have e : (fun g => σ (P * (P⁻¹ * g * P) * P⁻¹)) = σ := by
    funext g
    congr 1
    calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [Matrix.mul_nonsing_inv P hd, Matrix.one_mul, Matrix.mul_one]
  show IsDS ε lam fun g => σ (P * (P⁻¹ * g * P) * P⁻¹)
  rwa [e]

end Hpk

end CompanionTheory.PieriExpansion.Fd
