import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOneParamDerivOrthDecJoinedEqSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import GroundTheory.GlobalFields.Adele.IntegersLattice

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

noncomputable section
namespace GlobalTheory.FockLineJ

variable {D : D7}

/- English proof (translation)
Establish `h2 : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm`. Establish `: ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm = ⇑(GroundTheory.Global.homeomorphMixedSpace D.host.F).symm`. Use function extensionality and compare the values at `fun y => by`. Rewrite using `[Homeomorph.eq_symm_apply]`. Conclude with `(InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).apply_symm_apply y`.

Rewrite using `[this]`. Conclude with `(GroundTheory.Global.homeomorphMixedSpace D.host.F).symm.continuous`. Set `φ : ℝ →+* ℂ` to `((θ τ).comp Algebra.TensorProduct.includeLeftRingHom).comp ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm.toRingHom.comp (algebraMap ℝ (mixedEmbedding.mixedSpace D.host.F)))`. Establish `hφ : Continuous φ` using `(hθ τ).2.comp (h2.comp (continuous_algebraMap ℝ (mixedEmbedding.mixedSpace D.host.F)))`. Establish `e : ∀ s, φ s = θ τ (fstA D.host.F (realAd D.host.F s) ⊗ₜ[D.host.F] (1 : D.host.E))` using `fun s => rfl`.

Rewrite using `[← e]`. Establish `h1 : φ t = t * φ 1` using `GlobalTheory.WeilVacMove.additive_real φ.toAddMonoidHom hφ t`. Rewrite using `[h1, map_one, mul_one]`.
-/
theorem theta_realAd {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (t : ℝ) :
    θ τ (fstA D.host.F (realAd D.host.F t) ⊗ₜ[D.host.F] (1 : D.host.E)) = t := by
  have h2 : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm := by
    have : ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm = ⇑(GroundTheory.Global.homeomorphMixedSpace D.host.F).symm :=
      funext fun y => by
        rw [Homeomorph.eq_symm_apply]
        exact (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).apply_symm_apply y
    rw [this]
    exact (GroundTheory.Global.homeomorphMixedSpace D.host.F).symm.continuous
  let φ : ℝ →+* ℂ := ((θ τ).comp Algebra.TensorProduct.includeLeftRingHom).comp
    ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm.toRingHom.comp
      (algebraMap ℝ (mixedEmbedding.mixedSpace D.host.F)))
  have hφ : Continuous φ :=
    (hθ τ).2.comp (h2.comp (continuous_algebraMap ℝ (mixedEmbedding.mixedSpace D.host.F)))
  have e : ∀ s, φ s = θ τ (fstA D.host.F (realAd D.host.F s) ⊗ₜ[D.host.F] (1 : D.host.E)) := fun s => rfl
  rw [← e]
  have h1 : φ t = t * φ 1 := GlobalTheory.WeilVacMove.additive_real φ.toAddMonoidHom hφ t
  rw [h1, map_one, mul_one]

/- English proof (translation)
Rewrite using `[Algebra.smul_def]`. Both sides reduce to the same expression.
-/
theorem realAd_smul_eq (t : ℝ) (a : AE D) :
    realAd D.host.F t • a = (realAd D.host.F t ⊗ₜ[D.host.F] (1 : D.host.E)) * a := by
  rw [Algebra.smul_def]; rfl

/- English proof (translation)
Rewrite using `[realAd_smul_eq, map_mul]`. Establish `: finPart D (realAd D.host.F t ⊗ₜ[D.host.F] (1 : D.host.E)) = 0` using `by show sndA D.host.F (realAd D.host.F t) ⊗ₜ[D.host.F] (AlgHom.id D.host.F D.host.E 1) = 0`. Rewrite using `[show sndA D.host.F (realAd D.host.F t) = 0 from rfl, TensorProduct.zero_tmul]`. Rewrite using `[this, zero_mul]`.
-/
theorem finPart_realAd_smul (t : ℝ) (a : AE D) : finPart D (realAd D.host.F t • a) = 0 := by
  rw [realAd_smul_eq, map_mul]
  have : finPart D (realAd D.host.F t ⊗ₜ[D.host.F] (1 : D.host.E)) = 0 := by
    show sndA D.host.F (realAd D.host.F t) ⊗ₜ[D.host.F] (AlgHom.id D.host.F D.host.E 1) = 0
    rw [show sndA D.host.F (realAd D.host.F t) = 0 from rfl, TensorProduct.zero_tmul]
  rw [this, zero_mul]

/- English proof (translation)
Rewrite using `[realAd_smul_eq, map_mul, map_mul]`. Establish `: infPart D (realAd D.host.F t ⊗ₜ[D.host.F] (1 : D.host.E)) = fstA D.host.F (realAd D.host.F t) ⊗ₜ[D.host.F] (1 : D.host.E)` using `rfl`. Rewrite using `[this, theta_realAd hθ]`.
-/
theorem theta_realAd_smul {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (t : ℝ) (a : AE D) :
    θ τ (infPart D (realAd D.host.F t • a)) = t * θ τ (infPart D a) := by
  rw [realAd_smul_eq, map_mul, map_mul]
  have : infPart D (realAd D.host.F t ⊗ₜ[D.host.F] (1 : D.host.E)) =
      fstA D.host.F (realAd D.host.F t) ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  rw [this, theta_realAd hθ]

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[← sub_eq_zero]`. Establish `hl` using `fun τ => GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ (z τ)`. Establish `hs : ((∑ τ, lineAt θ τ (z τ)) t) i j = ∑ τ, lineAt θ τ (z τ) t i j`. Rewrite using `[AddMonoidHom.finset_sum_apply, Matrix.sum_apply]`.

Use `hσ.ext _ ?_ fun τ' => ?_` and prove the remaining obligations. Rewrite using `[map_sub, hs, map_sum, Matrix.smul_apply, finPart_realAd_smul, zero_sub, neg_eq_zero]`. Conclude with `Finset.sum_eq_zero fun τ _ => congrFun (congrFun ((hl τ).2.1 t) i) j`. Rewrite using `[map_sub, map_sub, hs, map_sum, map_sum, Matrix.smul_apply, theta_realAd_smul hθ, sub_eq_zero]`. Establish `e1 : θ τ' (infPart D (y i j)) = z τ' i j` using `congrFun (congrFun (hy τ') i) j`.

Establish `e2 : ∀ τ, θ τ' (infPart D (lineAt θ τ (z τ) t i j)) = if τ' = τ then (t : ℂ) * z τ i j else 0`. Introduce `τ`. Establish `h` using `congrFun (congrFun ((hl τ).2.2 t τ') i) j`. Rewrite `h` using `[compAt, Matrix.map_apply]`. Rewrite using `[h]`.

Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[e1, Finset.sum_congr rfl fun τ _ => e2 τ, Finset.sum_ite_eq]`. Simplify using the standard rewrite rules.
-/
theorem realAd_smul_eq_sum {m n : ℕ} {θ : InfFam D} (hθ : IsInfFam θ) {σ : (D.what₂.Tau → ℂ) →+ AE D}
    (hσ : GlobalTheory.FockCompare.Chart θ σ) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) (y : Mx D m n)
    (hy : ∀ τ, compAt θ τ y = z τ) (t : ℝ) :
    realAd D.host.F t • y = (∑ τ, lineAt θ τ (z τ)) t := by
  classical
  ext i j
  rw [← sub_eq_zero]
  have hl := fun τ => GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ (z τ)
  have hs : ((∑ τ, lineAt θ τ (z τ)) t) i j = ∑ τ, lineAt θ τ (z τ) t i j := by
    rw [AddMonoidHom.finset_sum_apply, Matrix.sum_apply]
  refine hσ.ext _ ?_ fun τ' => ?_
  · rw [map_sub, hs, map_sum, Matrix.smul_apply, finPart_realAd_smul, zero_sub, neg_eq_zero]
    exact Finset.sum_eq_zero fun τ _ => congrFun (congrFun ((hl τ).2.1 t) i) j
  · rw [map_sub, map_sub, hs, map_sum, map_sum, Matrix.smul_apply, theta_realAd_smul hθ, sub_eq_zero]
    have e1 : θ τ' (infPart D (y i j)) = z τ' i j := congrFun (congrFun (hy τ') i) j
    have e2 : ∀ τ, θ τ' (infPart D (lineAt θ τ (z τ) t i j)) = if τ' = τ then (t : ℂ) * z τ i j else 0 := by
      intro τ
      have h := congrFun (congrFun ((hl τ).2.2 t τ') i) j
      rw [compAt, Matrix.map_apply] at h
      rw [h]
      split_ifs <;> simp
    rw [e1, Finset.sum_congr rfl fun τ _ => e2 τ, Finset.sum_ite_eq]
    simp

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Use `⟨?_, fun t => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_empty] show Continuous fun _ : ℝ => (0 : WO S T)`. Conclude with `continuous_const`. Rewrite using `[Finset.sum_empty, AddMonoidHom.zero_apply]`.

Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_empty, Finset.sum_empty]`. Use function extensionality and compare the values at `w`. Simplify using `[GlobalTheory.WeilVacMove.dLine]`.

Introduce `a s ha ih`. Take `⟨h1, h2, h3⟩` from `ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Use `⟨?_, fun t => ?_, ?_⟩` and prove the remaining obligations. Use `show Continuous fun t => N a t + (∑ x ∈ s, N x) t`.

Conclude with `(hN a).add h1`. Rewrite using `[AddMonoidHom.add_apply, Matrix.map_add _ (finPart D).map_add, hN0 a t, h2 t, add_zero]`. Rewrite using `[GlobalTheory.BiJoinDeriv.dLine_add_line hψ (hN a) (hN0 a) h1 h2 hf, h3]`.
-/
theorem dLine_sum {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {ι : Type} (s : Finset ι)
    (N : ι → ℝ →+ WO S T) (hN : ∀ i, Continuous (N i)) (hN0 : ∀ i t, (N i t).map (finPart D) = 0)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    Continuous (⇑(∑ i ∈ s, N i) : ℝ → WO S T) ∧ (∀ t, ((∑ i ∈ s, N i) t).map (finPart D) = 0) ∧
      GlobalTheory.WeilVacMove.dLine ψ S T (∑ i ∈ s, N i) f = ∑ i ∈ s, GlobalTheory.WeilVacMove.dLine ψ S T (N i) f := by
  classical
  refine Finset.induction_on s ?_ ?_
  · refine ⟨?_, fun t => ?_, ?_⟩
    · rw [Finset.sum_empty]
      show Continuous fun _ : ℝ => (0 : WO S T)
      exact continuous_const
    · rw [Finset.sum_empty, AddMonoidHom.zero_apply]; ext i j; simp
    · rw [Finset.sum_empty, Finset.sum_empty]
      funext w
      simp [GlobalTheory.WeilVacMove.dLine]
  · intro a s ha ih
    obtain ⟨h1, h2, h3⟩ := ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨?_, fun t => ?_, ?_⟩
    · show Continuous fun t => N a t + (∑ x ∈ s, N x) t
      exact (hN a).add h1
    · rw [AddMonoidHom.add_apply, Matrix.map_add _ (finPart D).map_add, hN0 a t, h2 t, add_zero]
    · rw [GlobalTheory.BiJoinDeriv.dLine_add_line hψ (hN a) (hN0 a) h1 h2 hf, h3]

/- English proof (translation)
Introduce `D ψ θ S T sS sT f hψ hθ hf hvac x x' hx' w`. Take `⟨σ, hσ⟩` from `GlobalTheory.RealLineAt.exists_inverse_chart hθ`. Establish `hl` using `fun τ (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) => GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ z`. Set `c : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ` to `fun τ => compAt θ τ x`. Set `c' : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ` to `fun τ => cplxO (sS τ) (sT τ) (c τ)`.

Take `⟨L1, L2, L3⟩` from `dLine_sum hψ Finset.univ (fun τ => lineAt θ τ (c τ)) (fun τ => (hl τ _).1) (fun τ => (hl τ _).2.1) hf`. Take `⟨M1, M2, M3⟩` from `dLine_sum hψ Finset.univ (fun τ => lineAt θ τ (c' τ)) (fun τ => (hl τ _).1) (fun τ => (hl τ _).2.1) hf`. Establish `e : ∀ t, realAd D.host.F t • x = (∑ τ, lineAt θ τ (c τ)) t` using `realAd_smul_eq_sum hθ hσ c x (fun τ => rfl)`. Establish `e' : ∀ t, realAd D.host.F t • x' = (∑ τ, lineAt θ τ (c' τ)) t` using `realAd_smul_eq_sum hθ hσ c' x' hx'`. Establish `hd` using `(GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ L1 L2 hf).1 w`.

Establish `hd'` using `(GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ M1 M2 hf).1 w`. Use `⟨GlobalTheory.WeilVacMove.dLine ψ S T (∑ τ, lineAt θ τ (c τ)) f w, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [e]`. Conclude with `hd`. Establish `key : GlobalTheory.WeilVacMove.dLine ψ S T (∑ τ, lineAt θ τ (c' τ)) f w = Complex.I * GlobalTheory.WeilVacMove.dLine ψ S T (∑ τ, lineAt θ τ (c τ)) f w`.

Rewrite using `[L3, M3, Finset.sum_apply, Finset.sum_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `h : GlobalTheory.WeilVacMove.dLine ψ S T (lineAt θ τ (c τ)) f w + Complex.I * GlobalTheory.WeilVacMove.dLine ψ S T (lineAt θ τ (c' τ)) f w = 0` using `congrFun (hvac τ (c τ)) w`. Take the linear combination `(-Complex.I) * h + GlobalTheory.WeilVacMove.dLine ψ S T (lineAt θ τ (c' τ)) f w * Complex.I_sq`. Simplify using `only [e']`.

Rewrite using `[← key]`. Conclude with `hd'`.
-/
theorem fock_line_J : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ),
    IsStdChar D ψ (-1) → IsInfFam θ → IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) →
    ∀ x x' : WO S T, (∀ τ, compAt θ τ x' = cplxO (sS τ) (sT τ) (compAt θ τ x)) → ∀ w : WO S T, ∃ a : ℂ,
      HasDerivAt (fun t : ℝ => heisO ψ S T (realAd D.host.F t • x) f w) a 0 ∧
      HasDerivAt (fun t : ℝ => heisO ψ S T (realAd D.host.F t • x') f w) (Complex.I * a) 0 := by
  intro D ψ θ S T sS sT f hψ hθ hf hvac x x' hx' w
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hl := fun τ (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) => GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ z
  let c : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ := fun τ => compAt θ τ x
  let c' : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ := fun τ => cplxO (sS τ) (sT τ) (c τ)
  obtain ⟨L1, L2, L3⟩ := dLine_sum hψ Finset.univ (fun τ => lineAt θ τ (c τ)) (fun τ => (hl τ _).1)
    (fun τ => (hl τ _).2.1) hf
  obtain ⟨M1, M2, M3⟩ := dLine_sum hψ Finset.univ (fun τ => lineAt θ τ (c' τ)) (fun τ => (hl τ _).1)
    (fun τ => (hl τ _).2.1) hf
  have e : ∀ t, realAd D.host.F t • x = (∑ τ, lineAt θ τ (c τ)) t :=
    realAd_smul_eq_sum hθ hσ c x (fun τ => rfl)
  have e' : ∀ t, realAd D.host.F t • x' = (∑ τ, lineAt θ τ (c' τ)) t :=
    realAd_smul_eq_sum hθ hσ c' x' hx'
  have hd := (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ L1 L2 hf).1 w
  have hd' := (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ M1 M2 hf).1 w
  refine ⟨GlobalTheory.WeilVacMove.dLine ψ S T (∑ τ, lineAt θ τ (c τ)) f w, ?_, ?_⟩
  · simp only [e]
    exact hd
  · have key : GlobalTheory.WeilVacMove.dLine ψ S T (∑ τ, lineAt θ τ (c' τ)) f w =
        Complex.I * GlobalTheory.WeilVacMove.dLine ψ S T (∑ τ, lineAt θ τ (c τ)) f w := by
      rw [L3, M3, Finset.sum_apply, Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      have h : GlobalTheory.WeilVacMove.dLine ψ S T (lineAt θ τ (c τ)) f w +
          Complex.I * GlobalTheory.WeilVacMove.dLine ψ S T (lineAt θ τ (c' τ)) f w = 0 := congrFun (hvac τ (c τ)) w
      linear_combination (-Complex.I) * h + GlobalTheory.WeilVacMove.dLine ψ S T (lineAt θ τ (c' τ)) f w * Complex.I_sq
    simp only [e']
    rw [← key]
    exact hd'

end GlobalTheory.FockLineJ
