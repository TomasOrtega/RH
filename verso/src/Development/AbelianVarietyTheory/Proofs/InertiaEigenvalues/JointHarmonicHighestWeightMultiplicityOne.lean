import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFirstActionMatrixUnitEq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Sl2NonnegWeightOfHighestWeightVector
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZRYRCover
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointHighestWeightHarmonicOfFockLowestKTypeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointHighestWeightHarmonicMultiplicityOneCoverinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsJointHighestWeightHarmonicSliceOuterVariablesStatement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOfMemGfC
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsKHwMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.HarmLine

/- English proof (translation)
Introduce `σ _ k l N z y κ α β G P hG hGv hJ`. Establish `hd : ∀ u, u ∉ G.vars → ∀ Q : MvPolynomial σ ℂ, MvPolynomial.pderiv u (G * Q) = G * MvPolynomial.pderiv u Q`. Introduce `u hu Q`. Rewrite using `[Derivation.leibniz, MvPolynomial.pderiv_eq_zero_of_notMem_vars hu, smul_zero, add_zero, smul_eq_mul]`. Establish `hz : ∀ c Q, MvPolynomial.pderiv (z c) (G * Q) = G * MvPolynomial.pderiv (z c) Q` using `fun c Q => hd _ (fun h => (hGv _ h).1 c rfl) Q`.

Establish `hy : ∀ c Q, MvPolynomial.pderiv (y c) (G * Q) = G * MvPolynomial.pderiv (y c) Q` using `fun c Q => hd _ (fun h => (hGv _ h).2 c rfl) Q`. Establish `hmix : ∀ i j, GlobalTheory.Capelli.mixedOp ℂ z y i j (G * P) = G * GlobalTheory.Capelli.mixedOp ℂ z y i j P`. Introduce `i j`. Rewrite using `[GlobalTheory.Capelli.mixedOp_apply, GlobalTheory.Capelli.mixedOp_apply, mul_sub, Finset.mul_sum, Finset.mul_sum]`. Simplify using `only [hz, hy]`.

Conclude with `congrArg₂ (· - ·) (Finset.sum_congr rfl fun _ _ => by ring) (Finset.sum_congr rfl fun _ _ => by ring)`. Establish `hrz : ∀ c c', GlobalTheory.Capelli.rowOp ℂ z c c' (G * P) = G * GlobalTheory.Capelli.rowOp ℂ z c c' P`. Introduce `c c'`. Simplify using `only [GlobalTheory.Capelli.rowOp_apply, hz, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`.

Establish `hry : ∀ c c', GlobalTheory.Capelli.rowOp ℂ y c c' (G * P) = G * GlobalTheory.Capelli.rowOp ℂ y c c' P`. Introduce `c c'`. Simplify using `only [GlobalTheory.Capelli.rowOp_apply, hy, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`. Take `⟨h1, h2, h3, h4, h5, h6, h7⟩` from `hJ`.

Use `⟨fun i j hij => ?_, fun i => ?_, fun c c' h => ?_, fun c => ?_, fun d d' h => ?_, fun d => ?_, fun c d => ?_⟩` and prove the remaining obligations. Use `h1 i j hij` as an intermediate fact. Rewrite `this` using `[hmix]`. Conclude with `(mul_eq_zero.1 this).resolve_left hG`. Use `h2 i` as an intermediate fact.

Rewrite `this` using `[hmix, ← mul_smul_comm]`. Conclude with `mul_left_cancel₀ hG this`. Use `h3 c c' h` as an intermediate fact. Rewrite `this` using `[hrz]`. Conclude with `(mul_eq_zero.1 this).resolve_left hG`.

Use `h4 c` as an intermediate fact. Rewrite `this` using `[hrz, ← mul_smul_comm]`. Conclude with `mul_left_cancel₀ hG this`. Use `h5 d d' h` as an intermediate fact. Rewrite `this` using `[hry]`.

Conclude with `(mul_eq_zero.1 this).resolve_left hG`. Use `h6 d` as an intermediate fact. Rewrite `this` using `[hry, ← mul_smul_comm]`. Conclude with `mul_left_cancel₀ hG this`. Use `h7 c d` as an intermediate fact.

Simplify using `only [hy, hz, ← Finset.mul_sum] at this`. Conclude with `(mul_eq_zero.1 this).resolve_left hG`.
-/
theorem loc_jointTop : ∀ {σ : Type} [DecidableEq σ] {k l N : ℕ} (z : Fin k × Fin N → σ) (y : Fin l × Fin N → σ) (κ : Fin N → ℂ) (α : Fin k → ℂ) (β : Fin l → ℂ) (G P : MvPolynomial σ ℂ), G ≠ 0 → (∀ v ∈ G.vars, (∀ u, z u ≠ v) ∧ ∀ u, y u ≠ v) → GlobalTheory.CompactHarm.JointTop z y κ α β (G * P) → GlobalTheory.CompactHarm.JointTop z y κ α β P := by
  intro σ _ k l N z y κ α β G P hG hGv hJ
  have hd : ∀ u, u ∉ G.vars → ∀ Q : MvPolynomial σ ℂ,
      MvPolynomial.pderiv u (G * Q) = G * MvPolynomial.pderiv u Q := by
    intro u hu Q
    rw [Derivation.leibniz, MvPolynomial.pderiv_eq_zero_of_notMem_vars hu, smul_zero, add_zero, smul_eq_mul]
  have hz : ∀ c Q, MvPolynomial.pderiv (z c) (G * Q) = G * MvPolynomial.pderiv (z c) Q :=
    fun c Q => hd _ (fun h => (hGv _ h).1 c rfl) Q
  have hy : ∀ c Q, MvPolynomial.pderiv (y c) (G * Q) = G * MvPolynomial.pderiv (y c) Q :=
    fun c Q => hd _ (fun h => (hGv _ h).2 c rfl) Q
  have hmix : ∀ i j, GlobalTheory.Capelli.mixedOp ℂ z y i j (G * P) = G * GlobalTheory.Capelli.mixedOp ℂ z y i j P := by
    intro i j
    rw [GlobalTheory.Capelli.mixedOp_apply, GlobalTheory.Capelli.mixedOp_apply, mul_sub, Finset.mul_sum, Finset.mul_sum]
    simp only [hz, hy]
    exact congrArg₂ (· - ·) (Finset.sum_congr rfl fun _ _ => by ring) (Finset.sum_congr rfl fun _ _ => by ring)
  have hrz : ∀ c c', GlobalTheory.Capelli.rowOp ℂ z c c' (G * P) = G * GlobalTheory.Capelli.rowOp ℂ z c c' P := by
    intro c c'
    simp only [GlobalTheory.Capelli.rowOp_apply, hz, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hry : ∀ c c', GlobalTheory.Capelli.rowOp ℂ y c c' (G * P) = G * GlobalTheory.Capelli.rowOp ℂ y c c' P := by
    intro c c'
    simp only [GlobalTheory.Capelli.rowOp_apply, hy, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hJ
  refine ⟨fun i j hij => ?_, fun i => ?_, fun c c' h => ?_, fun c => ?_, fun d d' h => ?_, fun d => ?_,
    fun c d => ?_⟩
  · have := h1 i j hij
    rw [hmix] at this
    exact (mul_eq_zero.1 this).resolve_left hG
  · have := h2 i
    rw [hmix, ← mul_smul_comm] at this
    exact mul_left_cancel₀ hG this
  · have := h3 c c' h
    rw [hrz] at this
    exact (mul_eq_zero.1 this).resolve_left hG
  · have := h4 c
    rw [hrz, ← mul_smul_comm] at this
    exact mul_left_cancel₀ hG this
  · have := h5 d d' h
    rw [hry] at this
    exact (mul_eq_zero.1 this).resolve_left hG
  · have := h6 d
    rw [hry, ← mul_smul_comm] at this
    exact mul_left_cancel₀ hG this
  · have := h7 c d
    simp only [hy, hz, ← Finset.mul_sum] at this
    exact (mul_eq_zero.1 this).resolve_left hG

/- English proof (translation)
Introduce `D n m w lam P P' hP0 hH hH' hN hN' hK hK'`. Use `set κ : D.what₂.Tau → Fin n → ℂ := fun τ a => lam τ a - (m : ℂ) / 2 + ((m - w.p τ : ℕ) : ℂ) with hκ`. Establish `hJ` using `GlobalTheory.T.jointHighestWeightHarmonic_of_fock_lowestKType D n m w lam P hH hN hK`. Establish `hJ'` using `GlobalTheory.T.jointHighestWeightHarmonic_of_fock_lowestKType D n m w lam P' hH' hN' hK'`. Establish `hU : ∀ τ : D.what₂.Tau, ∃ Q₀ : MvPolynomial (Fin m × Fin n) ℂ, ∀ α β f, GlobalTheory.CompactHarm.JointTop (GlobalTheory.HarmLine.zR m n (w.p τ)) (GlobalTheory.HarmLine.yR m n (w.p τ)) (κ τ) α β f → ∃ r : ℂ, f = r • Q₀` using `fun τ => GlobalTheory.T.jointHighestWeightHarmonic_multiplicity_one_covering _ _ (GlobalTheory.HarmLine.zR_inj m n (w.p τ)) (GlobalTheory.HarmLine.yR_inj m n (w.p τ)) (GlobalTheory.HarmLine.zR_ne_yR m n (w.p τ)) (GlobalTheory.HarmLine.zR_yR_cover m n (w.p τ)) (κ τ)`.

Use `choose Q₀ hQ₀ using hU`. Set `Q : D.what₂.Tau → PolF D m n` to `fun τ => MvPolynomial.rename (Prod.mk τ) (Q₀ τ)`. Establish `hfac : ∀ (τ : D.what₂.Tau) (P : PolF D m n) α β, GlobalTheory.CompactHarm.JointTop (Prod.mk τ ∘ GlobalTheory.HarmLine.zR m n (w.p τ)) (Prod.mk τ ∘ GlobalTheory.HarmLine.yR m n (w.p τ)) (κ τ) α β P → ∃ R : PolF D m n, P = Q τ * R ∧ ∀ v ∈ R.vars, v.1 ≠ τ`. Introduce `τ P α β h`. Take `⟨s, f, g, hPs, hf, hg⟩` from `GlobalTheory.T.isJointHighestWeightHarmonic_slice_outer_variables (Prod.mk τ) (fun a b h => (Prod.mk.inj h).2) _ _ _ _ _ P h`.

Use `choose! r hr using fun i (hi : i ∈ s) => hQ₀ τ α β (f i) (hf i hi)`. Use `⟨∑ i ∈ s, r i • g i, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hPs, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[hr i hi, map_smul, smul_mul_assoc, mul_smul_comm]`.

Introduce `v hv hvτ`. Take `⟨i, hi, hvi⟩` from `Finset.mem_biUnion.1 (MvPolynomial.vars_sum_subset _ _ hv)`. Establish `hvi' : v ∈ (g i).vars`. Rewrite `hvi` using `[MvPolynomial.smul_eq_C_mul]`. Use `MvPolynomial.vars_mul (MvPolynomial.C (r i)) (g i) hvi` as an intermediate fact.

Simplify using `using this`. Conclude with `hg i hi v hvi' ⟨v.2, by rw [← hvτ]⟩`. Establish `hQne : ∀ τ, Q τ ≠ 0`. Introduce `τ h0`. Take `⟨α, β, hτ⟩` from `hJ τ`.

Take `⟨R, hR, -⟩` from `hfac τ P α β hτ`. Conclude with `hP0 (by rw [hR, h0, zero_mul])`. Establish `hE : ∀ s : Finset D.what₂.Tau, ∀ P : PolF D m n, (∀ τ ∈ s, ∃ α β, GlobalTheory.CompactHarm.JointTop (Prod.mk τ ∘ GlobalTheory.HarmLine.zR m n (w.p τ)) (Prod.mk τ ∘ GlobalTheory.HarmLine.yR m n (w.p τ)) (κ τ) α β P) → ∃ R : PolF D m n, P = (∏ τ ∈ s, Q τ) * R ∧ ∀ v ∈ R.vars, v.1 ∉ …`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => intro P _; exact ⟨P, by simp, by simp⟩`. Consider the case `insert τ₀ s hτ₀ ih`. Introduce `P hPs`. Take `⟨R, hPR, hRv⟩` from `ih P (fun τ hτ => hPs τ (Finset.mem_insert_of_mem hτ))`. Take `⟨α, β, hJ0⟩` from `hPs τ₀ (Finset.mem_insert_self _ _)`.

Establish `hG0 : (∏ τ ∈ s, Q τ) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun τ _ => hQne τ`. Establish `hGv : ∀ v ∈ (∏ τ ∈ s, Q τ).vars, v.1 ∈ s`. Introduce `v hv`. Take `⟨τ, hτ, hv'⟩` from `Finset.mem_biUnion.1 (MvPolynomial.vars_prod _ hv)`. Use `MvPolynomial.vars_rename (Prod.mk τ) (Q₀ τ) hv'` as an intermediate fact.

Take `⟨u, -, rfl⟩` from `Finset.mem_image.1 this`. Conclude with `hτ`. Establish `hJR` using `loc_jointTop _ _ _ α β _ R hG0 (fun v hv => ⟨fun u h => hτ₀ (by have := hGv v hv; rw [← h] at this; simpa using this), fun u h => hτ₀ (by have := hGv v hv; rw [← h] at this; simpa using this)⟩) (hPR ▸ hJ0)`. Take `⟨R', hRR', hR'v⟩` from `hfac τ₀ R α β hJR`. Use `⟨R', by rw [hPR, hRR', Finset.prod_insert hτ₀]; ring, ?_⟩` and prove the remaining obligations.

Introduce `v hv`. Rewrite using `[Finset.mem_insert, not_or]`. Use `⟨fun h => hR'v v hv h, hRv v ?_⟩` and prove the remaining obligations. Establish `hR'0 : R' ≠ 0` using `by rintro rfl; simp at hv`. Rewrite using `[hRR', MvPolynomial.mem_vars_iff_degreeOf_ne_zero, MvPolynomial.degreeOf_mul_eq (hQne τ₀) hR'0]`.

Rewrite `hv` using `[MvPolynomial.mem_vars_iff_degreeOf_ne_zero]`. Use linear arithmetic over natural numbers and integers. Take `⟨R, hR, hRv⟩` from `hE Finset.univ P (fun τ _ => hJ τ)`. Take `⟨R', hR', hR'v⟩` from `hE Finset.univ P' (fun τ _ => hJ' τ)`. Establish `hc : ∀ R : PolF D m n, (∀ v ∈ R.vars, v.1 ∉ (Finset.univ : Finset D.what₂.Tau)) → R = MvPolynomial.C (R.coeff 0)` using `fun R h => MvPolynomial.vars_eq_empty_iff_eq_C.1 (Finset.eq_empty_of_forall_notMem fun v hv => h v hv (Finset.mem_univ _))`.

Rewrite `hR` using `[hc R hRv]`. Rewrite `hR'` using `[hc R' hR'v]`. Establish `hc0 : R.coeff 0 ≠ 0`. Introduce `h0`. Apply `hP0` to reduce the goal to its premises.

Rewrite using `[hR, h0]`. Simplify using the standard rewrite rules. Use `⟨R'.coeff 0 / R.coeff 0, ?_⟩` and prove the remaining obligations. Rewrite using `[hR', hR, MvPolynomial.smul_eq_C_mul, ← mul_assoc, mul_comm (MvPolynomial.C _) (∏ τ, Q τ), mul_assoc, ← MvPolynomial.C_mul, div_mul_cancel₀ _ hc0]`.
-/
theorem joint_line : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (lam : D.what₂.Tau → Fin n → ℂ) (P P' : PolF D m n), P ≠ 0 → GlobalTheory.LowestKType.IsHarm w P → GlobalTheory.LowestKType.IsHarm w P' → GlobalTheory.LowestKType.IsNHw w lam P → GlobalTheory.LowestKType.IsNHw w lam P' → GlobalTheory.LowestKType.IsKHw w P → GlobalTheory.LowestKType.IsKHw w P' → ∃ c : ℂ, P' = c • P := by
  intro D n m w lam P P' hP0 hH hH' hN hN' hK hK'
  classical
  set κ : D.what₂.Tau → Fin n → ℂ := fun τ a => lam τ a - (m : ℂ) / 2 + ((m - w.p τ : ℕ) : ℂ) with hκ
  have hJ := GlobalTheory.T.jointHighestWeightHarmonic_of_fock_lowestKType D n m w lam P hH hN hK
  have hJ' := GlobalTheory.T.jointHighestWeightHarmonic_of_fock_lowestKType D n m w lam P' hH' hN' hK'
  have hU : ∀ τ : D.what₂.Tau, ∃ Q₀ : MvPolynomial (Fin m × Fin n) ℂ, ∀ α β f,
      GlobalTheory.CompactHarm.JointTop (GlobalTheory.HarmLine.zR m n (w.p τ)) (GlobalTheory.HarmLine.yR m n (w.p τ)) (κ τ) α β f →
        ∃ r : ℂ, f = r • Q₀ := fun τ =>
    GlobalTheory.T.jointHighestWeightHarmonic_multiplicity_one_covering _ _ (GlobalTheory.HarmLine.zR_inj m n (w.p τ)) (GlobalTheory.HarmLine.yR_inj m n (w.p τ))
      (GlobalTheory.HarmLine.zR_ne_yR m n (w.p τ)) (GlobalTheory.HarmLine.zR_yR_cover m n (w.p τ)) (κ τ)
  choose Q₀ hQ₀ using hU
  let Q : D.what₂.Tau → PolF D m n := fun τ => MvPolynomial.rename (Prod.mk τ) (Q₀ τ)
  have hfac : ∀ (τ : D.what₂.Tau) (P : PolF D m n) α β,
      GlobalTheory.CompactHarm.JointTop (Prod.mk τ ∘ GlobalTheory.HarmLine.zR m n (w.p τ))
        (Prod.mk τ ∘ GlobalTheory.HarmLine.yR m n (w.p τ)) (κ τ) α β P →
      ∃ R : PolF D m n, P = Q τ * R ∧ ∀ v ∈ R.vars, v.1 ≠ τ := by
    intro τ P α β h
    obtain ⟨s, f, g, hPs, hf, hg⟩ := GlobalTheory.T.isJointHighestWeightHarmonic_slice_outer_variables (Prod.mk τ) (fun a b h => (Prod.mk.inj h).2) _ _ _ _ _ P h
    choose! r hr using fun i (hi : i ∈ s) => hQ₀ τ α β (f i) (hf i hi)
    refine ⟨∑ i ∈ s, r i • g i, ?_, ?_⟩
    · rw [hPs, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hr i hi, map_smul, smul_mul_assoc, mul_smul_comm]
    · intro v hv hvτ
      obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.1 (MvPolynomial.vars_sum_subset _ _ hv)
      have hvi' : v ∈ (g i).vars := by
        rw [MvPolynomial.smul_eq_C_mul] at hvi
        have := MvPolynomial.vars_mul (MvPolynomial.C (r i)) (g i) hvi
        simpa using this
      exact hg i hi v hvi' ⟨v.2, by rw [← hvτ]⟩
  have hQne : ∀ τ, Q τ ≠ 0 := by
    intro τ h0
    obtain ⟨α, β, hτ⟩ := hJ τ
    obtain ⟨R, hR, -⟩ := hfac τ P α β hτ
    exact hP0 (by rw [hR, h0, zero_mul])
  have hE : ∀ s : Finset D.what₂.Tau, ∀ P : PolF D m n,
      (∀ τ ∈ s, ∃ α β, GlobalTheory.CompactHarm.JointTop (Prod.mk τ ∘ GlobalTheory.HarmLine.zR m n (w.p τ))
        (Prod.mk τ ∘ GlobalTheory.HarmLine.yR m n (w.p τ)) (κ τ) α β P) →
      ∃ R : PolF D m n, P = (∏ τ ∈ s, Q τ) * R ∧ ∀ v ∈ R.vars, v.1 ∉ s := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro P _; exact ⟨P, by simp, by simp⟩
    | insert τ₀ s hτ₀ ih =>
      intro P hPs
      obtain ⟨R, hPR, hRv⟩ := ih P (fun τ hτ => hPs τ (Finset.mem_insert_of_mem hτ))
      obtain ⟨α, β, hJ0⟩ := hPs τ₀ (Finset.mem_insert_self _ _)
      have hG0 : (∏ τ ∈ s, Q τ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => hQne τ
      have hGv : ∀ v ∈ (∏ τ ∈ s, Q τ).vars, v.1 ∈ s := by
        intro v hv
        obtain ⟨τ, hτ, hv'⟩ := Finset.mem_biUnion.1 (MvPolynomial.vars_prod _ hv)
        have := MvPolynomial.vars_rename (Prod.mk τ) (Q₀ τ) hv'
        obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 this
        exact hτ
      have hJR := loc_jointTop _ _ _ α β _ R hG0 (fun v hv =>
        ⟨fun u h => hτ₀ (by have := hGv v hv; rw [← h] at this; simpa using this),
         fun u h => hτ₀ (by have := hGv v hv; rw [← h] at this; simpa using this)⟩) (hPR ▸ hJ0)
      obtain ⟨R', hRR', hR'v⟩ := hfac τ₀ R α β hJR
      refine ⟨R', by rw [hPR, hRR', Finset.prod_insert hτ₀]; ring, ?_⟩
      intro v hv
      rw [Finset.mem_insert, not_or]
      refine ⟨fun h => hR'v v hv h, hRv v ?_⟩
      have hR'0 : R' ≠ 0 := by rintro rfl; simp at hv
      rw [hRR', MvPolynomial.mem_vars_iff_degreeOf_ne_zero, MvPolynomial.degreeOf_mul_eq (hQne τ₀) hR'0]
      rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero] at hv
      omega
  obtain ⟨R, hR, hRv⟩ := hE Finset.univ P (fun τ _ => hJ τ)
  obtain ⟨R', hR', hR'v⟩ := hE Finset.univ P' (fun τ _ => hJ' τ)
  have hc : ∀ R : PolF D m n, (∀ v ∈ R.vars, v.1 ∉ (Finset.univ : Finset D.what₂.Tau)) →
      R = MvPolynomial.C (R.coeff 0) := fun R h =>
    MvPolynomial.vars_eq_empty_iff_eq_C.1
      (Finset.eq_empty_of_forall_notMem fun v hv => h v hv (Finset.mem_univ _))
  rw [hc R hRv] at hR
  rw [hc R' hR'v] at hR'
  have hc0 : R.coeff 0 ≠ 0 := by
    intro h0; apply hP0; rw [hR, h0]; simp
  refine ⟨R'.coeff 0 / R.coeff 0, ?_⟩
  rw [hR', hR, MvPolynomial.smul_eq_C_mul, ← mul_assoc, mul_comm (MvPolynomial.C _) (∏ τ, Q τ), mul_assoc,
    ← MvPolynomial.C_mul, div_mul_cancel₀ _ hc0]

end GlobalTheory.HarmLine

end
