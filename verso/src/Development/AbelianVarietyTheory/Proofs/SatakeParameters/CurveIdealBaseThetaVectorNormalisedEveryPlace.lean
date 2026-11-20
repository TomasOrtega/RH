import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactTer
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.GlobalTheory.GL3.PFamily
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KappaNormAtSplitPrimesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KappaOnNonsplitPrimesStatement

noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity
open Formalism.L2.Th1.F (cmTheta)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace GlobalTheory.ThLoc.LocMM

/- English proof (translation)
Take `⟨k, rfl⟩` from `hb`. Use `⟨k, ?_⟩` and prove the remaining obligations. Simplify using `only [cmTheta]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cmTheta_odd (b : ℤ) (hb : Odd b) (d : ℕ) : ∃ k : ℤ, cmTheta b d = cmTheta 1 d + (k : ℂ) := by
  obtain ⟨k, rfl⟩ := hb
  refine ⟨k, ?_⟩
  simp only [cmTheta]
  push_cast
  ring

/- English proof (translation)
Introduce `x hx`. Take `⟨k, hk⟩` from `cmTheta_odd b hb d`. Rewrite using `[hk, add_smul]`. Use `Λ.add_mem (h x hx) ?_` and prove the remaining obligations. Rewrite using `[Int.cast_smul_eq_zsmul]`.

Conclude with `Λ.zsmul_mem hx k`.
-/
theorem stable_of_one {V : Type*} [AddCommGroup V] [Module ℂ V] (Λ : AddSubgroup V) (d : ℕ)
    (h : ∀ x ∈ Λ, cmTheta 1 d • x ∈ Λ) (b : ℤ) (hb : Odd b) : ∀ x ∈ Λ, cmTheta b d • x ∈ Λ := by
  intro x hx
  obtain ⟨k, hk⟩ := cmTheta_odd b hb d
  rw [hk, add_smul]
  refine Λ.add_mem (h x hx) ?_
  rw [Int.cast_smul_eq_zsmul]
  exact Λ.zsmul_mem hx k

/- English proof (translation)
Assume the negation of the conclusion as `hb`. Take `⟨k, rfl⟩` from `Int.not_odd_iff_even.1 hb`. Establish `h1` using `h.1`. Establish `h8` using `h.2.2.1`. Establish `h2 : (d : ℤ) = 4 * ((a : ℤ) * c - k * k)`.

Establish `: (k + k) ^ 2 = 4 * (k * k)` using `by ring`. Rewrite `h1` using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion. Generalize the expression as in `(a : ℤ) * c - k * k = t at h2`. Use linear arithmetic over natural numbers and integers.
-/
theorem odd_of_cmOK {a : ℕ} {b c : ℤ} {d : ℕ} (h : CmOK a b c d) : Odd b := by
  by_contra hb
  obtain ⟨k, rfl⟩ := Int.not_odd_iff_even.1 hb
  have h1 := h.1
  have h8 := h.2.2.1
  have h2 : (d : ℤ) = 4 * ((a : ℤ) * c - k * k) := by
    have : (k + k) ^ 2 = 4 * (k * k) := by ring
    rw [this] at h1
    linarith
  generalize (a : ℤ) * c - k * k = t at h2
  omega

/- English proof (translation)
Establish `key : ∀ (x : n → ℂ) (y : Fin 4 × n → ℂ), altE (matH (blk4 h)) (CmData.embA 0 x) y = altE (matH h) x (slice 0 y)`. Introduce `x y`. Simplify using `only [altE, matrixForm_fourfoldBlock, CmData.slice_embA]`. Rewrite using `[Finset.sum_eq_single (0 : Fin 4)]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Simplify using `[hb]`. Introduce `hh`. Conclude with `absurd (Finset.mem_univ _) hh`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `h1 : CmData.embA 0 x ∈ dualLat (matH (blk4 h)) (pow4 Λ)`. Introduce `y hy`. Take `⟨m, hm⟩` from `hx (slice 0 y) (hy 0)`.

Conclude with `⟨m, by rw [key, hm]⟩`. Rewrite `h1` using `[hsd]`. Establish `h2` using `h1 0`. Rewrite `h2` using `[CmData.slice_embA, if_pos rfl]`. Then use the resulting hypothesis. Introduce `hx y hy`.

Establish `h1 : CmData.embA 0 x ∈ dualLat (matH (blk4 h)) (pow4 Λ)`. Rewrite using `[hsd]`. Conclude with `CmData.embA_mem Λ 0 hx`. Take `⟨m, hm⟩` from `h1 _ (CmData.embA_mem Λ 0 hy)`. Use `⟨m, ?_⟩` and prove the remaining obligations.

Rewrite `hm` using `[key, CmData.slice_embA, if_pos rfl]`. Conclude with `hm`.
-/
theorem hermitianSelfDual_of_fourfoldBlock {n : Type} [Fintype n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (hsd : IsSelfDual (matH (blk4 h)) (pow4 Λ)) : IsSelfDual (matH h) Λ := by
  have key : ∀ (x : n → ℂ) (y : Fin 4 × n → ℂ), altE (matH (blk4 h)) (CmData.embA 0 x) y = altE (matH h) x (slice 0 y) := by
    intro x y
    simp only [altE, matrixForm_fourfoldBlock, CmData.slice_embA]
    rw [Finset.sum_eq_single (0 : Fin 4)]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  ext x
  constructor
  · intro hx
    have h1 : CmData.embA 0 x ∈ dualLat (matH (blk4 h)) (pow4 Λ) := by
      intro y hy
      obtain ⟨m, hm⟩ := hx (slice 0 y) (hy 0)
      exact ⟨m, by rw [key, hm]⟩
    rw [hsd] at h1
    have h2 := h1 0
    rwa [CmData.slice_embA, if_pos rfl] at h2
  · intro hx y hy
    have h1 : CmData.embA 0 x ∈ dualLat (matH (blk4 h)) (pow4 Λ) := by
      rw [hsd]
      exact CmData.embA_mem Λ 0 hx
    obtain ⟨m, hm⟩ := h1 _ (CmData.embA_mem Λ 0 hy)
    refine ⟨m, ?_⟩
    rw [key, CmData.slice_embA, if_pos rfl] at hm
    exact hm

section Base

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

/- English proof (translation)
Establish `h` using `((B.latAll hcc hδ (base_linkage_nonempty D cc δ B)).1 2 2 _ _ (Formalism.MainNotions.GlobalTheoryTheory.Inhab.Adm_std D 2 2 even_two even_two)).1`. Rewrite `h` using `[show TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) = _ from B.areaOK, show TaylorLogMetric.La D B.tor _ _ = _ from B.lat0OK 2 2]`. Establish `h2` using `SO.selfDual_img _ _ (SO.reix D.what₂.Tau) (SO.reix_isom B.L D.what₂.Tau) _ h`. Rewrite `h2` using `[SO.reix_pow]`. Conclude with `h2`.
-/
theorem selfDual_fourfold_curveIdeal_lattice (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    IsSelfDual (matH (blk4 (hOne B.L D.what₂.Tau))) (pow4 B.lamM) := by
  have h := ((B.latAll hcc hδ (base_linkage_nonempty D cc δ B)).1 2 2 _ _
    (Formalism.MainNotions.GlobalTheoryTheory.Inhab.Adm_std D 2 2 even_two even_two)).1
  rw [show TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) = _ from B.areaOK, show TaylorLogMetric.La D B.tor _ _ = _ from B.lat0OK 2 2] at h
  have h2 := SO.selfDual_img _ _ (SO.reix D.what₂.Tau) (SO.reix_isom B.L D.what₂.Tau) _ h
  rw [SO.reix_pow] at h2
  exact h2

/- English proof (translation)
The claim follows from `hermitianSelfDual_of_fourfoldBlock _ _ (selfDual_fourfold_curveIdeal_lattice B hcc hδ)`.
-/
theorem selfDual_lamM (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    IsSelfDual (matH (hOne B.L D.what₂.Tau)) B.lamM :=
  hermitianSelfDual_of_fourfoldBlock _ _ (selfDual_fourfold_curveIdeal_lattice B hcc hδ)

/- English proof (translation)
Use `stable_of_one _ _ (fun x hx => ?_) b hb` and prove the remaining obligations. Use `SO.lamMM_smul (AR.om D) hx` as an intermediate fact. Rewrite `this` using `[← SO.theta_eq]`. Conclude with `this`.
-/
theorem stable_lamM (b : ℤ) (hb : Odd b) : ∀ x ∈ B.lamM, cmTheta b D.host.d • x ∈ B.lamM := by
  refine stable_of_one _ _ (fun x hx => ?_) b hb
  have := SO.lamMM_smul (AR.om D) hx
  rw [← SO.theta_eq] at this
  exact this

end Base

/- English proof (translation)
Distinguish the cases in `hs : SplitK D p`. Conclude with `GlobalTheory.T.kappa_norm_at_splitPrimes D cc δ B hcc hδ p ι hs`. Conclude with `GlobalTheory.T.kappa_on_nonsplit_primes D cc δ B hcc hδ p ι hs`.
-/
theorem kappaAt {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) : B.KappaAt p ι := by
  by_cases hs : SplitK D p
  · exact GlobalTheory.T.kappa_norm_at_splitPrimes D cc δ B hcc hδ p ι hs
  · exact GlobalTheory.T.kappa_on_nonsplit_primes D cc δ B hcc hδ p ι hs

/- English proof (translation)
Introduce `D cc δ hcc hδ B a₀ b₀ c₀ ha hd lam hlam hcm hB l _ ι`. Establish `hK : B.KappaAt l ι` using `kappaAt B hcc hδ l ι`. Take `⟨hL, hω⟩` from `hB`. Establish `hS : StdData B.L B.ω₀ (hOne B.L D.what₂.Tau) B.lamM (alphaQ B.cq (matH (hOne B.L D.what₂.Tau))) (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))) B.gC` using `B.stdOK hcc hδ`. Establish `hsd` using `selfDual_lamM B hcc hδ`.

Establish `hst` using `stable_lamM B b₀ (odd_of_cmOK hcm)`. Establish `hspec` using `B.thMM_spec (B.stdOK hcc hδ)`. Establish `h2 : tens4 B.thMM = B.kappa • kernel4 B.L B.ω₀ B.lamM (alphaQ (Real.sqrt D.host.d / 2) (stdH B.L (Fin 4 × D.what₂.Tau))) B.gC` using `hspec.2`. Establish `iso` using `hS.isom`. Establish `i1` using `hS.idx₁`.

Establish `i2` using `hS.idx₂`. Unfold `Base.KappaAt Base.latA at hK`. Unfold `Base.LocNormMM LocNorm`. Rewrite `h2` using `[hω]`. Rewrite `h2`, `hK`, `iso`, `i1`, `i2`, `hsd`, the goal using `[hL]`.

Establish `hsda` using `CmData.selfDual_img _ _ B.gC iso _ (CmData.isSelfDual_matH_blk4_pow4 _ B.lamM hsd)`. Establish `hsta : ∀ x ∈ imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM), cmTheta b₀ D.host.d • x ∈ imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)`. Introduce and unpack `x ⟨x', hx', rfl⟩`. Use `⟨cmTheta b₀ D.host.d • x', fun a' => hst _ (hx' a'), ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.

Take `⟨u, huiso, hufix, j1, jl, j2⟩` from `localStandard a₀ b₀ c₀ D.host.d ha hd lam hlam hcm (Fin 4 × D.what₂.Tau) _ hsda hsta i1 i2 l Fact.out`. Establish `hκu` using `hK u huiso j1 jl j2`. Rewrite `j1`, `jl`, `j2` using `[← KR.imgLat_trans]`. Establish `hg₁ : IsIsom (matH (blk4 (hOne (cmL a₀ b₀ D.host.d ha hd lam hlam) D.what₂.Tau))) (stdH (cmL a₀ b₀ D.host.d ha hd lam hlam) (Fin 4 × D.what₂.Tau)) ((B.gC.trans u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → …`. Introduce `x y`.

Establish `h1` using `huiso (B.gC x) (B.gC y)`. Establish `h0` using `iso x y`. Simplify using `only [LinearEquiv.coe_coe, LinearEquiv.trans_apply] at h0 h1 ⊢`. Rewrite using `[h1, h0]`. Establish `D0` using `stdDataCm a₀ b₀ c₀ D.host.d ha hd lam hlam hcm.1 hcm.2.1 hcm.2.2.1 D.what₂.Tau _ B.lamM B.gC iso hsd hst i1 i2`.

Establish `D1` using `stdDataCm a₀ b₀ c₀ D.host.d ha hd lam hlam hcm.1 hcm.2.1 hcm.2.2.1 D.what₂.Tau _ B.lamM (B.gC.trans u) hg₁ hsd hst j1 j2`. Establish `hcomp : B.gC.symm.trans (B.gC.trans u) = u`. Use extensionality with `x`. Simplify using the standard rewrite rules. Establish `hfix : ∀ x, (B.gC.trans u) x = B.gC x → x = 0`.

Introduce `x hx`. Establish `h1 : B.gC x = 0` using `hufix _ hx`. Simplify using `using congrArg B.gC.symm h1`. Rewrite `hκu` using `[← hcomp]`. Take `⟨c, hc8, hc⟩` from `kernelRatio _ _ D.what₂.Tau _ B.lamM _ _ B.gC (B.gC.trans u) D0 D1 hfix`.

Use `⟨B.gC.trans u, B.kappa * c, hg₁, jl, j2, (KR.norm_mul_eq_one ι B.kappa c _ hc8 hκu).le, ?_⟩` and prove the remaining obligations. Rewrite using `[h2, hc, smul_smul]`.
-/
theorem locNormMM : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (B : Base D cc δ) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0),
    CmOK a₀ b₀ c₀ D.host.d → B.IsCm a₀ b₀ ha hd lam hlam →
    ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), B.LocNormMM a₀ b₀ ha hd lam hlam p ι := by
  intro D cc δ hcc hδ B a₀ b₀ c₀ ha hd lam hlam hcm hB l _ ι
  have hK : B.KappaAt l ι := kappaAt B hcc hδ l ι
  obtain ⟨hL, hω⟩ := hB
  have hS : StdData B.L B.ω₀ (hOne B.L D.what₂.Tau) B.lamM (alphaQ B.cq (matH (hOne B.L D.what₂.Tau)))
    (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))) B.gC := B.stdOK hcc hδ
  have hsd := selfDual_lamM B hcc hδ
  have hst := stable_lamM B b₀ (odd_of_cmOK hcm)
  have hspec := B.thMM_spec (B.stdOK hcc hδ)
  have h2 : tens4 B.thMM = B.kappa • kernel4 B.L B.ω₀ B.lamM
      (alphaQ (Real.sqrt D.host.d / 2) (stdH B.L (Fin 4 × D.what₂.Tau))) B.gC := hspec.2
  have iso := hS.isom
  have i1 := hS.idx₁
  have i2 := hS.idx₂
  unfold Base.KappaAt Base.latA at hK
  unfold Base.LocNormMM LocNorm
  rw [hω] at h2
  rw [hL] at h2 hK iso i1 i2 hsd ⊢
  have hsda := CmData.selfDual_img _ _ B.gC iso _ (CmData.isSelfDual_matH_blk4_pow4 _ B.lamM hsd)
  have hsta : ∀ x ∈ imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM),
      cmTheta b₀ D.host.d • x ∈ imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM) := by
    rintro x ⟨x', hx', rfl⟩
    refine ⟨cmTheta b₀ D.host.d • x', fun a' => hst _ (hx' a'), ?_⟩
    simp
  obtain ⟨u, huiso, hufix, j1, jl, j2⟩ := localStandard a₀ b₀ c₀ D.host.d ha hd lam hlam hcm (Fin 4 × D.what₂.Tau) _
    hsda hsta i1 i2 l Fact.out
  have hκu := hK u huiso j1 jl j2
  rw [← KR.imgLat_trans] at j1 jl j2
  have hg₁ : IsIsom (matH (blk4 (hOne (cmL a₀ b₀ D.host.d ha hd lam hlam) D.what₂.Tau)))
      (stdH (cmL a₀ b₀ D.host.d ha hd lam hlam) (Fin 4 × D.what₂.Tau))
      ((B.gC.trans u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) :
        (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) := by
    intro x y
    have h1 := huiso (B.gC x) (B.gC y)
    have h0 := iso x y
    simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply] at h0 h1 ⊢
    rw [h1, h0]
  have D0 := stdDataCm a₀ b₀ c₀ D.host.d ha hd lam hlam hcm.1 hcm.2.1 hcm.2.2.1 D.what₂.Tau _ B.lamM B.gC iso hsd hst i1 i2
  have D1 := stdDataCm a₀ b₀ c₀ D.host.d ha hd lam hlam hcm.1 hcm.2.1 hcm.2.2.1 D.what₂.Tau _ B.lamM (B.gC.trans u) hg₁
    hsd hst j1 j2
  have hcomp : B.gC.symm.trans (B.gC.trans u) = u := by
    ext x
    simp
  have hfix : ∀ x, (B.gC.trans u) x = B.gC x → x = 0 := by
    intro x hx
    have h1 : B.gC x = 0 := hufix _ hx
    simpa using congrArg B.gC.symm h1
  rw [← hcomp] at hκu
  obtain ⟨c, hc8, hc⟩ := kernelRatio _ _ D.what₂.Tau _ B.lamM _ _ B.gC (B.gC.trans u) D0 D1 hfix
  refine ⟨B.gC.trans u, B.kappa * c, hg₁, jl, j2, (KR.norm_mul_eq_one ι B.kappa c _ hc8 hκu).le, ?_⟩
  rw [h2, hc, smul_smul]

end GlobalTheory.ThLoc.LocMM
