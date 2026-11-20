import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.WeightCompApply
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementC

namespace Formalism.InvariantFactorPaths.PW

open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

/- English proof (translation)
Introduce `c hc d hd x hx`. Rewrite `hx`, the goal using `[IsoC, Submodule.mem_sInf]`. Introduce `S hS`. Conclude with `hS.2 c hc d hd x (hx S hS)`.
-/
theorem isoC_stable (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    GlStableC p LL j Cs (IsoC p LL j Cs la) := by
  intro c hc d hd x hx
  rw [IsoC, Submodule.mem_sInf] at hx ⊢
  intro S hS
  exact hS.2 c hc d hd x (hx S hS)

/- English proof (translation)
Rewrite using `[IsoC]`. Conclude with `le_sInf fun S hS => hS.1`.
-/
theorem hwc_le_isoC (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    HWC p LL j Cs la ≤ IsoC p LL j Cs la := by
  rw [IsoC]
  exact le_sInf fun S hS => hS.1

/- English proof (translation)
Use `conv_lhs => rw [x.as_sum]`. Rewrite using `[map_sum, coeff_sum]`. Simplify using `only [glAct_diag_monomial, coeff_smul, coeff_monomial, smul_eq_mul]`. Rewrite using `[Finset.sum_eq_single m]`. Rewrite using `[if_pos rfl]`.

Introduce `b _ hb`. Rewrite using `[if_neg hb, mul_zero]`. Introduce `hm`. Rewrite using `[if_pos rfl, notMem_support_iff.mp hm, mul_zero]`.
-/
theorem coeff_glAct_diag (LL : Letters N) (j : ℕ) (c : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (m : Fin N × Fin r →₀ ℕ) :
    coeff m (glAct p LL j c c x) = ((wt LL j c m : ℤ) : ℚ_[p]) * coeff m x := by
  classical
  conv_lhs => rw [x.as_sum]
  rw [map_sum, coeff_sum]
  simp only [glAct_diag_monomial, coeff_smul, coeff_monomial, smul_eq_mul]
  rw [Finset.sum_eq_single m]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg hb, mul_zero]
  · intro hm
    rw [if_pos rfl, notMem_support_iff.mp hm, mul_zero]

/- English proof (translation)
Rewrite using `[WtSpC, MvPolynomial.mem_restrictSupport_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h c hc`. Use extensionality with `m`. Rewrite using `[coeff_glAct_diag, coeff_smul, smul_eq_mul]`.

Distinguish the cases in `hm : coeff m x = 0`. Rewrite using `[hm, mul_zero, mul_zero]`. Use `h (Finset.mem_coe.mpr (mem_support_iff.mpr hm)) c hc` as an intermediate fact. Rewrite using `[this]`. Introduce `h m hm c hc`.

Establish `hm' : coeff m x ≠ 0` using `mem_support_iff.mp (Finset.mem_coe.mp hm)`. Establish `e` using `congrArg (coeff m) (h c hc)`. Rewrite `e` using `[coeff_glAct_diag, coeff_smul, smul_eq_mul]`. Use `mul_right_cancel₀ hm' e` as an intermediate fact. Conclude with `this` after adjusting the coercions.
-/
theorem wtSpC_iff_eig (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    x ∈ WtSpC p LL j Cs la ↔ ∀ c ∈ Cs, glAct p LL j c c x = ((la c : ℤ) : ℚ_[p]) • x := by
  rw [WtSpC, MvPolynomial.mem_restrictSupport_iff]
  constructor
  · intro h c hc
    ext m
    rw [coeff_glAct_diag, coeff_smul, smul_eq_mul]
    by_cases hm : coeff m x = 0
    · rw [hm, mul_zero, mul_zero]
    · have := h (Finset.mem_coe.mpr (mem_support_iff.mpr hm)) c hc
      rw [this]
  · intro h m hm c hc
    have hm' : coeff m x ≠ 0 := mem_support_iff.mp (Finset.mem_coe.mp hm)
    have e := congrArg (coeff m) (h c hc)
    rw [coeff_glAct_diag, coeff_smul, smul_eq_mul] at e
    have := mul_right_cancel₀ hm' e
    exact_mod_cast this

/- English proof (translation)
Introduce `x hx`. Rewrite `hx`, the goal using `[HWC, Submodule.mem_inf]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[wtSpC_iff_eig]`. Introduce `c hc`.

Rewrite using `[← hA c hc c hc, (wtSpC_iff_eig LL j Cs la x).mp hx.1 c hc, map_smul]`. Establish `h2` using `hx.2`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker] at h2 ⊢`. Introduce `c d hcd`. Rewrite using `[← hA c hcd.1 d hcd.2.1, h2 c d hcd, map_zero]`.
-/
theorem hwc_map_of_comm (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r))
    (A : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hA : ∀ c ∈ Cs, ∀ d ∈ Cs, ∀ x, A (glAct p LL j c d x) = glAct p LL j c d (A x)) (la : Fin r → ℤ) :
    ∀ x ∈ HWC p LL j Cs la, A x ∈ HWC p LL j Cs la := by
  intro x hx
  rw [HWC, Submodule.mem_inf] at hx ⊢
  refine ⟨?_, ?_⟩
  · rw [wtSpC_iff_eig]
    intro c hc
    rw [← hA c hc c hc, (wtSpC_iff_eig LL j Cs la x).mp hx.1 c hc, map_smul]
  · have h2 := hx.2
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at h2 ⊢
    intro c d hcd
    rw [← hA c hcd.1 d hcd.2.1, h2 c d hcd, map_zero]

/- English proof (translation)
Establish `hle : IsoC p LL j Cs la ≤ (IsoC p LL j Cs la).comap A` using `by conv_lhs => rw [IsoC]`. Use `sInf_le ⟨?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Conclude with `hwc_le_isoC LL j Cs la (hwc_map_of_comm LL j Cs A hA la x hx)`. Introduce `c hc d hd x hx`.

Rewrite `hx`, the goal using `[Submodule.mem_comap]`. Rewrite using `[hA c hc d hd]`. Conclude with `isoC_stable LL j Cs la c hc d hd _ hx`. Conclude with `fun x hx => hle hx`.
-/
theorem isoC_map_of_comm (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r))
    (A : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hA : ∀ c ∈ Cs, ∀ d ∈ Cs, ∀ x, A (glAct p LL j c d x) = glAct p LL j c d (A x)) (la : Fin r → ℤ) :
    ∀ x ∈ IsoC p LL j Cs la, A x ∈ IsoC p LL j Cs la := by
  have hle : IsoC p LL j Cs la ≤ (IsoC p LL j Cs la).comap A := by
    conv_lhs => rw [IsoC]
    refine sInf_le ⟨?_, ?_⟩
    · intro x hx
      exact hwc_le_isoC LL j Cs la (hwc_map_of_comm LL j Cs A hA la x hx)
    · intro c hc d hd x hx
      rw [Submodule.mem_comap] at hx ⊢
      rw [hA c hc d hd]
      exact isoC_stable LL j Cs la c hc d hd _ hx
  exact fun x hx => hle hx

/- English proof (translation)
Establish `hle : (⨆ (la : Fin r → ℤ) (_ : Q la), IsoC p LL j Cs la) ≤ (⨆ (la : Fin r → ℤ) (_ : Q la), IsoC p LL j Cs la).comap A`. Use `iSup_le fun la => iSup_le fun hla => ?_` and prove the remaining obligations. Introduce `x hx`. Rewrite using `[Submodule.mem_comap]`. Conclude with `(le_iSup_of_le la (le_iSup_of_le hla le_rfl) : IsoC p LL j Cs la ≤ ⨆ (la : Fin r → ℤ) (_ : Q la), IsoC p LL j Cs la) (hA la x hx)`.

Conclude with `fun x hx => hle hx`.
-/
theorem iSup_isoC_map (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (Q : (Fin r → ℤ) → Prop)
    (A : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hA : ∀ la, ∀ x ∈ IsoC p LL j Cs la, A x ∈ IsoC p LL j Cs la) :
    ∀ x ∈ (⨆ (la : Fin r → ℤ) (_ : Q la), IsoC p LL j Cs la),
      A x ∈ (⨆ (la : Fin r → ℤ) (_ : Q la), IsoC p LL j Cs la) := by
  have hle : (⨆ (la : Fin r → ℤ) (_ : Q la), IsoC p LL j Cs la) ≤
      (⨆ (la : Fin r → ℤ) (_ : Q la), IsoC p LL j Cs la).comap A := by
    refine iSup_le fun la => iSup_le fun hla => ?_
    intro x hx
    rw [Submodule.mem_comap]
    exact (le_iSup_of_le la (le_iSup_of_le hla le_rfl) :
      IsoC p LL j Cs la ≤ ⨆ (la : Fin r → ℤ) (_ : Q la), IsoC p LL j Cs la) (hA la x hx)
  exact fun x hx => hle hx

/- English proof (translation)
Take `⟨hPP, hr, hk⟩` from `hP`. Establish `hPP' : ∀ x, P (P x) = P x` using `fun x => congrArg (fun f => f x) hPP`. Establish `hR : ∀ x ∈ LinearMap.range P, A x ∈ LinearMap.range P`. Rewrite using `[hr]`. Conclude with `iSup_isoC_map LL j Cs (fun la => la ∈ T) A hA`.

Establish `hK : ∀ x ∈ LinearMap.ker P, A x ∈ LinearMap.ker P`. Rewrite using `[hk]`. Conclude with `iSup_isoC_map LL j Cs (fun la => la ∉ T) A hA`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply]`.

Establish `h1 : P (A (P x)) = A (P x)`. Take `⟨y, hy⟩` from `hR (P x) ⟨x, rfl⟩`. Rewrite using `[← hy, hPP']`. Establish `h2 : P (A (x - P x)) = 0`. Apply `hK` to reduce the goal to its premises.

Rewrite using `[LinearMap.mem_ker, map_sub, hPP', sub_self]`. Rewrite `h2` using `[map_sub, map_sub, h1, sub_eq_zero]`. Conclude with `h2`.
-/
theorem typeProj_comm (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j Cs T P)
    (A : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hA : ∀ la, ∀ x ∈ IsoC p LL j Cs la, A x ∈ IsoC p LL j Cs la) : P ∘ₗ A = A ∘ₗ P := by
  obtain ⟨hPP, hr, hk⟩ := hP
  have hPP' : ∀ x, P (P x) = P x := fun x => congrArg (fun f => f x) hPP
  have hR : ∀ x ∈ LinearMap.range P, A x ∈ LinearMap.range P := by
    rw [hr]; exact iSup_isoC_map LL j Cs (fun la => la ∈ T) A hA
  have hK : ∀ x ∈ LinearMap.ker P, A x ∈ LinearMap.ker P := by
    rw [hk]; exact iSup_isoC_map LL j Cs (fun la => la ∉ T) A hA
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  have h1 : P (A (P x)) = A (P x) := by
    obtain ⟨y, hy⟩ := hR (P x) ⟨x, rfl⟩
    rw [← hy, hPP']
  have h2 : P (A (x - P x)) = 0 := by
    apply hK
    rw [LinearMap.mem_ker, map_sub, hPP', sub_self]
  rw [map_sub, map_sub, h1, sub_eq_zero] at h2
  exact h2

/- English proof (translation)
Introduce `p _ N r LL j j' Cs Cs' T T' P P' hj hC hP hP'`. Establish `h1 : ∀ c ∈ Cs', ∀ d ∈ Cs', ∀ x, P (glAct p LL j' c d x) = glAct p LL j' c d (P x)`. Introduce `c hc d hd x`. Use `typeProj_comm LL j Cs T P hP (glAct p LL j' c d) (by` as an intermediate fact. Introduce `la y hy`.

Rewrite using `[glAct_split LL hj c d, LinearMap.add_apply]`. Use `Submodule.add_mem _ (isoC_stable LL j Cs la c (hC hc) d (hC hd) y hy) ?_` and prove the remaining obligations. Conclude with `isoC_map_of_comm LL j Cs (midAct p LL j j' c d) (fun c' _ d' _ z => midAct_comm LL j j' c d c' d' z) la y hy)`. Conclude with `congrArg (fun f => f x) this`. Conclude with `(typeProj_comm LL j' Cs' T' P' hP' P (isoC_map_of_comm LL j' Cs' P h1)).symm`.
-/
theorem comm_projection_holds : CommP := by
  intro p _ N r LL j j' Cs Cs' T T' P P' hj hC hP hP'
  have h1 : ∀ c ∈ Cs', ∀ d ∈ Cs', ∀ x, P (glAct p LL j' c d x) = glAct p LL j' c d (P x) := by
    intro c hc d hd x
    have := typeProj_comm LL j Cs T P hP (glAct p LL j' c d) (by
      intro la y hy
      rw [glAct_split LL hj c d, LinearMap.add_apply]
      refine Submodule.add_mem _ (isoC_stable LL j Cs la c (hC hc) d (hC hd) y hy) ?_
      exact isoC_map_of_comm LL j Cs (midAct p LL j j' c d)
        (fun c' _ d' _ z => midAct_comm LL j j' c d c' d' z) la y hy)
    exact congrArg (fun f => f x) this
  exact (typeProj_comm LL j' Cs' T' P' hP' P (isoC_map_of_comm LL j' Cs' P h1)).symm

end Formalism.InvariantFactorPaths.PW
