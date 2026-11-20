import Mathlib
import GroundTheory.ArithmeticGeometry.ToricVarieties.Dimension
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelOpenMapping
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalLocallyIrreducible
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchOffHypersurface
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInjectiveHolomorphicOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericProjectionFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjectionsContainOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjHomInjective
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsExists
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLeadIdealDim
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLinearFormCut
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHomogDimZeroPow
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PUnitaryZariskiDense
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDiscriminantCover
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimitiveElementFibres
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Matrix

noncomputable section

/- English proof (translation)
Introduce `q hq` and use `by rw [← M.comap_eq] at hq; exact hq`.
-/
theorem NormalModel.le_comap {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : NormalModel J) :
    J ≤ M.ideal.comap
      (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ).toRingHom :=
  fun q hq => by rw [← M.comap_eq] at hq; exact hq

def NormalModel.quotMap {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : NormalModel J) :
    MvPolynomial (Fin n) ℂ ⧸ J →+* MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal :=
  Ideal.quotientMap M.ideal
    (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ).toRingHom
    M.le_comap

/- English proof (translation)
Set `_ : Algebra (MvPolynomial (Fin n) ℂ ⧸ J) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal)` to `M.quotMap.toAlgebra`. Establish `hf : ∀ q, algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) (Ideal.Quotient.mk J q) = Ideal.Quotient.mk M.ideal (rename Sum.inl q)` using `fun q => Ideal.quotientMap_mk (H := M.le_comap)`. Establish `hint : ∀ q : MvPolynomial (Fin n ⊕ Fin M.m) ℂ, IsIntegral (MvPolynomial (Fin n) ℂ ⧸ J) (Ideal.Quotient.mk M.ideal q)`. Introduce `q`. Proceed by induction on `q using MvPolynomial.induction_on with`.

Consider the case `C c`. Establish `: Ideal.Quotient.mk M.ideal (C c) = algebraMap _ _ (Ideal.Quotient.mk J (C c))`. Rewrite using `[hf, rename_C]`. Rewrite using `[this]`. Conclude with `isIntegral_algebraMap`.

Consider the case `add p q hp hq`. Rewrite using `[map_add]`. Conclude with `hp.add hq`. Consider the case `mul_X p i hp`. Rewrite using `[map_mul]`.

Use `hp.mul ?_` and prove the remaining obligations. Break down `i with j | j` into its components or cases. Establish `: Ideal.Quotient.mk M.ideal (X (Sum.inl j)) = algebraMap _ _ (Ideal.Quotient.mk J (X j))`. Rewrite using `[hf, rename_X]`. Rewrite using `[this]`.

Conclude with `isIntegral_algebraMap`. Take `⟨P, hPm, hP⟩` from `M.integral j`. Use `⟨P.map (Ideal.Quotient.mk J), hPm.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map]`. Establish `hcomp : (algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal)).comp (Ideal.Quotient.mk J) = (Ideal.Quotient.mk M.ideal).comp (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ).toRingHom` using `RingHom.ext fun q => hf q`.

Rewrite using `[hcomp, ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hP`. Establish `: Algebra.IsIntegral (MvPolynomial (Fin n) ℂ ⧸ J) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal)` using `⟨fun x => by`. Take `⟨q, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Conclude with `hint q⟩`.

Conclude with `GroundTheory.Arith.Toric.ringKrullDim_eq_of_isIntegral (Ideal.quotientMap_injective' (H := M.le_comap) (fun q hq => by rw [← M.comap_eq]; exact hq))`.
-/
theorem NormalModel.ringKrullDim_eq {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : NormalModel J) :
    ringKrullDim (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) =
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) := by
  let _ : Algebra (MvPolynomial (Fin n) ℂ ⧸ J) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) :=
    M.quotMap.toAlgebra
  have hf : ∀ q, algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal)
      (Ideal.Quotient.mk J q) = Ideal.Quotient.mk M.ideal (rename Sum.inl q) := fun q =>
    Ideal.quotientMap_mk (H := M.le_comap)
  have hint : ∀ q : MvPolynomial (Fin n ⊕ Fin M.m) ℂ,
      IsIntegral (MvPolynomial (Fin n) ℂ ⧸ J) (Ideal.Quotient.mk M.ideal q) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c =>
      have : Ideal.Quotient.mk M.ideal (C c) = algebraMap _ _ (Ideal.Quotient.mk J (C c)) := by
        rw [hf, rename_C]
      rw [this]
      exact isIntegral_algebraMap
    | add p q hp hq =>
      rw [map_add]
      exact hp.add hq
    | mul_X p i hp =>
      rw [map_mul]
      refine hp.mul ?_
      rcases i with j | j
      · have : Ideal.Quotient.mk M.ideal (X (Sum.inl j)) = algebraMap _ _ (Ideal.Quotient.mk J (X j)) := by
          rw [hf, rename_X]
        rw [this]
        exact isIntegral_algebraMap
      · obtain ⟨P, hPm, hP⟩ := M.integral j
        refine ⟨P.map (Ideal.Quotient.mk J), hPm.map _, ?_⟩
        rw [Polynomial.eval₂_map]
        have hcomp : (algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal)).comp
            (Ideal.Quotient.mk J) = (Ideal.Quotient.mk M.ideal).comp
              (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ).toRingHom :=
          RingHom.ext fun q => hf q
        rw [hcomp, ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem]
        exact hP
  have : Algebra.IsIntegral (MvPolynomial (Fin n) ℂ ⧸ J) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) :=
    ⟨fun x => by
      obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact hint q⟩
  exact GroundTheory.Arith.Toric.ringKrullDim_eq_of_isIntegral
    (Ideal.quotientMap_injective' (H := M.le_comap) (fun q hq => by rw [← M.comap_eq]; exact hq))

/- English proof (translation)
The claim follows from `(GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.proof (GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsContainOpen.proof GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsFinite.proof GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjHomInjective …`.
-/
theorem exists_isFiniteProjection {N d : ℕ} (I : Ideal (MvPolynomial (Fin N) ℂ)) (hI : I.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin N) ℂ ⧸ I) = d) :
    ∃ A : Matrix (Fin d) (Fin N) ℂ, GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection I A :=
  (GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.proof
    (GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsContainOpen.proof
      GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsFinite.proof
      GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjHomInjective.proof
      GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsOpen.proof
      (GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsExists.proof
        GroundTheory.Heights₂.Heights.ComplexSets.LeadIdealDim.proof
        GroundTheory.Heights₂.Heights.ComplexSets.LinearFormCut.proof
        GroundTheory.Heights₂.Heights.ComplexSets.HomogDimZeroPow.proof))
    GroundTheory.Heights₂.Heights.ComplexSets.UnitaryZariskiDense.proof N d I hI hdim).2.1

/- English proof (translation)
Take `⟨U0, V0, g, -, -, hV0, hzV0, -, -, hAg, hZV0⟩` from `hP _ hPt (φ t) ⟨hφZ ht, rfl⟩`. Establish `hAd : Differentiable ℂ (fun v : Fin N → ℂ => A *ᵥ v)` using `(LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).differentiable`. Establish `hWo : IsOpen (V ∩ φ ⁻¹' V0)` using `hφ.continuousOn.isOpen_inter_preimage hV hV0`. Establish `hkey : ∀ s ∈ V ∩ φ ⁻¹' V0, φ s = g (A *ᵥ φ s)`. Introduce `s hs`.

Establish `hmem : φ s ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet I ∩ V0` using `⟨hφZ hs.1, hs.2⟩`. Rewrite `hmem` using `[hZV0]`. Take `⟨u, hu, hgu⟩` from `hmem`. Rewrite using `[← hgu, hAg u hu]`. Establish `hFd : DifferentiableOn ℂ (fun s => A *ᵥ φ s) (V ∩ φ ⁻¹' V0)` using `hAd.comp_differentiableOn (hφ.mono Set.inter_subset_left)`.

Establish `hFi : Set.InjOn (fun s => A *ᵥ φ s) (V ∩ φ ⁻¹' V0)` using `fun s hs s' hs' hss' => hφi hs.1 hs'.1 (by rw [hkey s hs, hkey s' hs']; exact congrArg g hss')`. Establish `hΩ` using `hinj k _ _ hWo hFd hFi`. Use `⟨V0 ∩ (fun v => A *ᵥ v) ⁻¹' ((fun s => A *ᵥ φ s) '' (V ∩ φ ⁻¹' V0)), hV0.inter (hAd.continuous.isOpen_preimage _ hΩ), ⟨hzV0, t, ⟨ht, hzV0⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `z ⟨hzZ, hzV0', s, hsW, hsz⟩`. Establish `hmem : z ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet I ∩ V0` using `⟨hzZ, hzV0'⟩`.

Rewrite `hmem` using `[hZV0]`. Take `⟨u, hu, rfl⟩` from `hmem`. Use `⟨s, hsW.1, ?_⟩` and prove the remaining obligations. Rewrite using `[hkey s hsW]`. Simplify using `only at hsz`.

Rewrite using `[hsz, hAg u hu]`.
-/
theorem open_image_off_discriminant (hinj : InjectiveHolomorphicOpen.Statement) {N k : ℕ}
    {I : Ideal (MvPolynomial (Fin N) ℂ)} {A : Matrix (Fin k) (Fin N) ℂ} {P : MvPolynomial (Fin k) ℂ}
    (hP : ∀ y : Fin k → ℂ, eval y P ≠ 0 → ∀ x ∈ GroundTheory.Heights₂.Heights.ComplexSets.fibre I A y,
      ∃ (U : Set (Fin k → ℂ)) (V : Set (Fin N → ℂ)) (g : (Fin k → ℂ) → (Fin N → ℂ)),
        IsOpen U ∧ y ∈ U ∧ IsOpen V ∧ x ∈ V ∧ DifferentiableOn ℂ g U ∧ g y = x ∧
          (∀ w ∈ U, A.mulVec (g w) = w) ∧ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet I ∩ V = g '' U)
    {V : Set (Fin k → ℂ)} {φ : (Fin k → ℂ) → Fin N → ℂ} (hV : IsOpen V) (hφ : DifferentiableOn ℂ φ V)
    (hφi : Set.InjOn φ V) (hφZ : Set.MapsTo φ V (zeroSetIn I)) {t : Fin k → ℂ} (ht : t ∈ V)
    (hPt : eval (A *ᵥ φ t) P ≠ 0) :
    ∃ O : Set (Fin N → ℂ), IsOpen O ∧ φ t ∈ O ∧ zeroSetIn I ∩ O ⊆ φ '' V := by
  obtain ⟨U0, V0, g, -, -, hV0, hzV0, -, -, hAg, hZV0⟩ := hP _ hPt (φ t) ⟨hφZ ht, rfl⟩
  have hAd : Differentiable ℂ (fun v : Fin N → ℂ => A *ᵥ v) :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).differentiable
  have hWo : IsOpen (V ∩ φ ⁻¹' V0) := hφ.continuousOn.isOpen_inter_preimage hV hV0
  have hkey : ∀ s ∈ V ∩ φ ⁻¹' V0, φ s = g (A *ᵥ φ s) := by
    intro s hs
    have hmem : φ s ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet I ∩ V0 := ⟨hφZ hs.1, hs.2⟩
    rw [hZV0] at hmem
    obtain ⟨u, hu, hgu⟩ := hmem
    rw [← hgu, hAg u hu]
  have hFd : DifferentiableOn ℂ (fun s => A *ᵥ φ s) (V ∩ φ ⁻¹' V0) :=
    hAd.comp_differentiableOn (hφ.mono Set.inter_subset_left)
  have hFi : Set.InjOn (fun s => A *ᵥ φ s) (V ∩ φ ⁻¹' V0) := fun s hs s' hs' hss' =>
    hφi hs.1 hs'.1 (by rw [hkey s hs, hkey s' hs']; exact congrArg g hss')
  have hΩ := hinj k _ _ hWo hFd hFi
  refine ⟨V0 ∩ (fun v => A *ᵥ v) ⁻¹' ((fun s => A *ᵥ φ s) '' (V ∩ φ ⁻¹' V0)),
    hV0.inter (hAd.continuous.isOpen_preimage _ hΩ), ⟨hzV0, t, ⟨ht, hzV0⟩, rfl⟩, ?_⟩
  rintro z ⟨hzZ, hzV0', s, hsW, hsz⟩
  have hmem : z ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet I ∩ V0 := ⟨hzZ, hzV0'⟩
  rw [hZV0] at hmem
  obtain ⟨u, hu, rfl⟩ := hmem
  refine ⟨s, hsW.1, ?_⟩
  rw [hkey s hsW]
  simp only at hsz
  rw [hsz, hAg u hu]

/- English proof (translation)
Take `⟨A, hA⟩` from `exists_isFiniteProjection I hI hdim`. Take `⟨P, hP0, hP⟩` from `GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.proof GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveElementFibres.proof N k I A hI hdim hA`. Use `set h := GroundTheory.Heights₂.Heights.ComplexSets.pullback A P with hh`. Establish `hhe : ∀ z, eval z h = eval (A *ᵥ z) P` using `fun z => GroundTheory.Heights₂.Heights.ComplexSets.FibreBound.eval_pullback A z P`. Establish `hhI : h ∉ I`.

Introduce `hmem`. Apply `hP0` to reduce the goal to its premises. Apply `hA.injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 hmem`.

Establish `hP'` using `fun y hy => (hP y hy).2.2`. Establish `hloc : ∀ τ ∈ U, ∃ B : Set (Fin N → ℂ), IsOpen B ∧ φ τ ∈ B ∧ zeroSetIn I ∩ B ⊆ φ '' U`. Introduce `τ hτ`. Take `⟨ε, hε, hεU⟩` from `Metric.isOpen_iff.1 hU τ hτ`. Establish `hr0 : 0 < ε / 2` using `by positivity`.

Establish `hKU : Metric.closedBall τ (ε / 2) ⊆ U` using `(Metric.closedBall_subset_ball (by linarith)).trans hεU`. Establish `hVU : Metric.ball τ (ε / 2) ⊆ U` using `Metric.ball_subset_closedBall.trans hKU`. Establish `hKc : IsCompact (φ '' Metric.closedBall τ (ε / 2))` using `(isCompact_closedBall τ (ε / 2)).image_of_continuousOn (hφ.continuousOn.mono hKU)`. Establish `hSc : IsCompact (φ '' Metric.sphere τ (ε / 2))` using `(isCompact_sphere τ (ε / 2)).image_of_continuousOn (hφ.continuousOn.mono (Metric.sphere_subset_closedBall.trans hKU))`. Establish `hwS : φ τ ∉ φ '' Metric.sphere τ (ε / 2)`.

Introduce and unpack `⟨s, hs, hsτ⟩`. Establish `hst` using `hφi (Metric.sphere_subset_closedBall.trans hKU hs) hτ hsτ`. Rewrite `hs` using `[hst, Metric.mem_sphere, dist_self]`. Conclude with `hr0.ne hs`. Take `⟨B, hBo, hwB, hBS, hpre, hdense⟩` from `hirr (Fin N) I h (φ τ) hI hic hhI (hφZ hτ) (φ '' Metric.sphere τ (ε / 2))ᶜ (hSc.isClosed.isOpen_compl.mem_nhds hwS)`.

Use `set G := ⋃₀ {O : Set (Fin N → ℂ) | IsOpen O ∧ zeroSetIn I ∩ O ⊆ φ '' Metric.ball τ (ε / 2)} with hG`. Establish `hGo : IsOpen G` using `isOpen_sUnion fun O hO => hO.1`. Establish `hGZ : zeroSetIn I ∩ G ⊆ φ '' Metric.ball τ (ε / 2)`. Introduce and unpack `z ⟨hzZ, O, hO, hzO⟩`. Conclude with `hO.2 ⟨hzZ, hzO⟩`.

Establish `hVK : φ '' Metric.ball τ (ε / 2) ⊆ φ '' Metric.closedBall τ (ε / 2)` using `Set.image_mono Metric.ball_subset_closedBall`. Take `⟨t0, ⟨ht0V, ht0B⟩, ht0h⟩` from `hoff N k I h (Metric.ball τ (ε / 2) ∩ φ ⁻¹' B) φ hI hdim hhI ((hφ.continuousOn.mono hVU).isOpen_inter_preimage Metric.isOpen_ball hBo) ⟨τ, Metric.mem_ball_self hr0, hwB⟩ (hφ.mono (Set.inter_subset_left.trans hVU)) (hφi.mono (Set.inter_subset_left.trans hVU)) (fun s hs => hφZ (hVU …`. Establish `hcover : (zeroSetIn I ∩ B) \ {z | eval z h = 0} ⊆ G ∪ (φ '' Metric.closedBall τ (ε / 2))ᶜ`. Introduce and unpack `z ⟨⟨hzZ, hzB⟩, hzh⟩`. Distinguish the cases in `hzK : z ∈ φ '' Metric.closedBall τ (ε / 2)`.

Use `left`. Take `⟨s, hsK, rfl⟩` from `hzK`. Establish `hsV : s ∈ Metric.ball τ (ε / 2)`. Break down `(Metric.mem_closedBall.1 hsK).lt_or_eq with hlt | heq` into its components or cases. Conclude with `hlt`.

Conclude with `absurd ⟨s, heq, rfl⟩ (hBS hzB)`. Take `⟨O, hOo, hsO, hOZ⟩` from `open_image_off_discriminant hinj hP' Metric.isOpen_ball (hφ.mono hVU) (hφi.mono hVU) (fun s hs => hφZ (hVU hs)) hsV (by rw [← hhe]; exact hzh)`. Conclude with `⟨O, ⟨hOo, hOZ⟩, hsO⟩`. Conclude with `Or.inr hzK`. Establish `hdisj : (zeroSetIn I ∩ B) \ {z | eval z h = 0} ∩ (G ∩ (φ '' Metric.closedBall τ (ε / 2))ᶜ) = ∅` using `Set.eq_empty_iff_forall_notMem.2 fun z ⟨⟨⟨hzZ, _⟩, _⟩, hzG, hzK⟩ => hzK (hVK (hGZ ⟨hzZ, hzG⟩))`.

Establish `hDG : (zeroSetIn I ∩ B) \ {z | eval z h = 0} ⊆ G`. Break down `isPreconnected_iff_subset_of_disjoint.1 hpre _ _ hGo hKc.isClosed.isOpen_compl hcover hdisj with h1 | h1` into its components or cases. Conclude with `h1`. Conclude with `absurd (hVK ⟨t0, ht0V, rfl⟩) (h1 ⟨⟨hφZ (hVU ht0V), ht0B⟩, ht0h⟩)`. Establish `hDK : (zeroSetIn I ∩ B) \ {z | eval z h = 0} ⊆ φ '' Metric.closedBall τ (ε / 2)` using `fun z hz => hVK (hGZ ⟨hz.1.1, hDG hz⟩)`.

Conclude with `⟨B, hBo, hwB, fun z hz => Set.image_mono hKU (closure_minimal hDK hKc.isClosed (hdense hz))⟩`. Use `⟨⋃₀ {O : Set (Fin N → ℂ) | IsOpen O ∧ zeroSetIn I ∩ O ⊆ φ '' U}, isOpen_sUnion fun O hO => hO.1, Set.Subset.antisymm ?_ ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨τ, hτ, rfl⟩`. Take `⟨B, hBo, hτB, hBU⟩` from `hloc τ hτ`. Conclude with `⟨hφZ hτ, B, ⟨hBo, hBU⟩, hτB⟩`.

Introduce and unpack `z ⟨hzZ, O, hO, hzO⟩`. Conclude with `hO.2 ⟨hzZ, hzO⟩`.
-/
theorem openMapping_of_isIntegrallyClosed (hirr : NormalLocallyIrreducible.Statement)
    (hoff : BranchOffHypersurface.Statement) (hinj : InjectiveHolomorphicOpen.Statement) {N k : ℕ}
    (I : Ideal (MvPolynomial (Fin N) ℂ)) (hI : I.IsPrime) (hic : IsIntegrallyClosed (MvPolynomial (Fin N) ℂ ⧸ I))
    (hdim : ringKrullDim (MvPolynomial (Fin N) ℂ ⧸ I) = (k : ℕ)) (U : Set (Fin k → ℂ))
    (φ : (Fin k → ℂ) → Fin N → ℂ) (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U) (hφi : Set.InjOn φ U)
    (hφZ : Set.MapsTo φ U (zeroSetIn I)) :
    ∃ O : Set (Fin N → ℂ), IsOpen O ∧ φ '' U = zeroSetIn I ∩ O := by
  obtain ⟨A, hA⟩ := exists_isFiniteProjection I hI hdim
  obtain ⟨P, hP0, hP⟩ := GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.proof
    GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveElementFibres.proof N k I A hI hdim hA
  set h := GroundTheory.Heights₂.Heights.ComplexSets.pullback A P with hh
  have hhe : ∀ z, eval z h = eval (A *ᵥ z) P := fun z =>
    GroundTheory.Heights₂.Heights.ComplexSets.FibreBound.eval_pullback A z P
  have hhI : h ∉ I := by
    intro hmem
    apply hP0
    apply hA.injective
    rw [map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hmem
  have hP' := fun y hy => (hP y hy).2.2
  have hloc : ∀ τ ∈ U, ∃ B : Set (Fin N → ℂ), IsOpen B ∧ φ τ ∈ B ∧ zeroSetIn I ∩ B ⊆ φ '' U := by
    intro τ hτ
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU τ hτ
    have hr0 : 0 < ε / 2 := by positivity
    have hKU : Metric.closedBall τ (ε / 2) ⊆ U :=
      (Metric.closedBall_subset_ball (by linarith)).trans hεU
    have hVU : Metric.ball τ (ε / 2) ⊆ U := Metric.ball_subset_closedBall.trans hKU
    have hKc : IsCompact (φ '' Metric.closedBall τ (ε / 2)) :=
      (isCompact_closedBall τ (ε / 2)).image_of_continuousOn (hφ.continuousOn.mono hKU)
    have hSc : IsCompact (φ '' Metric.sphere τ (ε / 2)) :=
      (isCompact_sphere τ (ε / 2)).image_of_continuousOn
        (hφ.continuousOn.mono (Metric.sphere_subset_closedBall.trans hKU))
    have hwS : φ τ ∉ φ '' Metric.sphere τ (ε / 2) := by
      rintro ⟨s, hs, hsτ⟩
      have hst := hφi (Metric.sphere_subset_closedBall.trans hKU hs) hτ hsτ
      rw [hst, Metric.mem_sphere, dist_self] at hs
      exact hr0.ne hs
    obtain ⟨B, hBo, hwB, hBS, hpre, hdense⟩ := hirr (Fin N) I h (φ τ) hI hic hhI (hφZ hτ)
      (φ '' Metric.sphere τ (ε / 2))ᶜ (hSc.isClosed.isOpen_compl.mem_nhds hwS)
    set G := ⋃₀ {O : Set (Fin N → ℂ) | IsOpen O ∧ zeroSetIn I ∩ O ⊆ φ '' Metric.ball τ (ε / 2)} with hG
    have hGo : IsOpen G := isOpen_sUnion fun O hO => hO.1
    have hGZ : zeroSetIn I ∩ G ⊆ φ '' Metric.ball τ (ε / 2) := by
      rintro z ⟨hzZ, O, hO, hzO⟩
      exact hO.2 ⟨hzZ, hzO⟩
    have hVK : φ '' Metric.ball τ (ε / 2) ⊆ φ '' Metric.closedBall τ (ε / 2) :=
      Set.image_mono Metric.ball_subset_closedBall
    obtain ⟨t0, ⟨ht0V, ht0B⟩, ht0h⟩ := hoff N k I h (Metric.ball τ (ε / 2) ∩ φ ⁻¹' B) φ hI hdim hhI
      ((hφ.continuousOn.mono hVU).isOpen_inter_preimage Metric.isOpen_ball hBo)
      ⟨τ, Metric.mem_ball_self hr0, hwB⟩ (hφ.mono (Set.inter_subset_left.trans hVU))
      (hφi.mono (Set.inter_subset_left.trans hVU)) (fun s hs => hφZ (hVU hs.1))
    have hcover : (zeroSetIn I ∩ B) \ {z | eval z h = 0} ⊆ G ∪ (φ '' Metric.closedBall τ (ε / 2))ᶜ := by
      rintro z ⟨⟨hzZ, hzB⟩, hzh⟩
      by_cases hzK : z ∈ φ '' Metric.closedBall τ (ε / 2)
      · left
        obtain ⟨s, hsK, rfl⟩ := hzK
        have hsV : s ∈ Metric.ball τ (ε / 2) := by
          rcases (Metric.mem_closedBall.1 hsK).lt_or_eq with hlt | heq
          · exact hlt
          · exact absurd ⟨s, heq, rfl⟩ (hBS hzB)
        obtain ⟨O, hOo, hsO, hOZ⟩ := open_image_off_discriminant hinj hP' Metric.isOpen_ball
          (hφ.mono hVU) (hφi.mono hVU) (fun s hs => hφZ (hVU hs)) hsV (by rw [← hhe]; exact hzh)
        exact ⟨O, ⟨hOo, hOZ⟩, hsO⟩
      · exact Or.inr hzK
    have hdisj : (zeroSetIn I ∩ B) \ {z | eval z h = 0} ∩ (G ∩ (φ '' Metric.closedBall τ (ε / 2))ᶜ) = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun z ⟨⟨⟨hzZ, _⟩, _⟩, hzG, hzK⟩ => hzK (hVK (hGZ ⟨hzZ, hzG⟩))
    have hDG : (zeroSetIn I ∩ B) \ {z | eval z h = 0} ⊆ G := by
      rcases isPreconnected_iff_subset_of_disjoint.1 hpre _ _ hGo hKc.isClosed.isOpen_compl hcover hdisj
        with h1 | h1
      · exact h1
      · exact absurd (hVK ⟨t0, ht0V, rfl⟩) (h1 ⟨⟨hφZ (hVU ht0V), ht0B⟩, ht0h⟩)
    have hDK : (zeroSetIn I ∩ B) \ {z | eval z h = 0} ⊆ φ '' Metric.closedBall τ (ε / 2) :=
      fun z hz => hVK (hGZ ⟨hz.1.1, hDG hz⟩)
    exact ⟨B, hBo, hwB, fun z hz =>
      Set.image_mono hKU (closure_minimal hDK hKc.isClosed (hdense hz))⟩
  refine ⟨⋃₀ {O : Set (Fin N → ℂ) | IsOpen O ∧ zeroSetIn I ∩ O ⊆ φ '' U},
    isOpen_sUnion fun O hO => hO.1, Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨τ, hτ, rfl⟩
    obtain ⟨B, hBo, hτB, hBU⟩ := hloc τ hτ
    exact ⟨hφZ hτ, B, ⟨hBo, hBU⟩, hτB⟩
  · rintro z ⟨hzZ, O, hO, hzO⟩
    exact hO.2 ⟨hzZ, hzO⟩

/- English proof (translation)
Introduce `n k J M U φ hJ hdim hU hφ hφi hφZ`. Use `set e : Fin n ⊕ Fin M.m ≃ Fin (n + M.m) := finSumFinEquiv with he`. Use `set RE : MvPolynomial (Fin n ⊕ Fin M.m) ℂ ≃+* MvPolynomial (Fin (n + M.m)) ℂ := (renameEquiv ℂ e).toRingEquiv with hRE`. Use `set I' := M.ideal.map (RE : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* MvPolynomial (Fin (n + M.m)) ℂ) with hI'`. Establish `QE` using `Ideal.quotientEquiv M.ideal I' RE rfl`.

Use `M.isPrime` as an intermediate fact. Establish `hI'p : I'.IsPrime` using `Ideal.map_isPrime_of_equiv RE`. Use `M.isIntegrallyClosed` as an intermediate fact. Establish `hic : IsIntegrallyClosed (MvPolynomial (Fin (n + M.m)) ℂ ⧸ I')` using `IsIntegrallyClosed.of_equiv QE`. Establish `hdim' : ringKrullDim (MvPolynomial (Fin (n + M.m)) ℂ ⧸ I') = (k : ℕ)`.

Rewrite using `[← ringKrullDim_eq_of_ringEquiv QE, M.ringKrullDim_eq, hdim]`. Establish `hZ : ∀ z : Fin (n + M.m) → ℂ, z ∈ zeroSetIn I' ↔ (fun i => z (e i)) ∈ zeroSetIn M.ideal`. Introduce `z`. Prove the components needed by the constructor for the conclusion. Introduce `hz q hq`.

Establish `h2` using `hz _ (Ideal.mem_map_of_mem _ hq)`. Express the relevant statement in the definitionally equal form `eval z (rename e q) = 0 at h2`. Rewrite `h2` using `[eval_rename]`. Then use the resulting hypothesis. Introduce `hz q' hq'`. Take `⟨q, hq, rfl⟩` from `(Ideal.mem_map_of_equiv RE q').1 hq'`.

Express the relevant statement in the definitionally equal form `eval z (rename e q) = 0`. Rewrite using `[eval_rename]`. Conclude with `hz q hq`. Use `set φ' : (Fin k → ℂ) → Fin (n + M.m) → ℂ := fun t i => φ t (e.symm i) with hφ'`. Establish `hφ'd : DifferentiableOn ℂ φ' U` using `differentiableOn_pi.2 fun i => differentiableOn_pi.1 hφ (e.symm i)`.

Establish `hφ'e : ∀ t, (fun i => φ' t (e i)) = φ t` using `fun t => funext fun i => by simp [hφ']`. Establish `hφ'i : Set.InjOn φ' U` using `fun s hs t ht hst => hφi hs ht (by rw [← hφ'e s, ← hφ'e t, hst])`. Establish `hφ'Z : Set.MapsTo φ' U (zeroSetIn I')` using `fun t ht => (hZ _).2 (by rw [hφ'e]; exact hφZ ht)`. Take `⟨O', hO'o, hO'⟩` from `openMapping_of_isIntegrallyClosed hirr hoff hinj I' hI'p hic hdim' U φ' hU hφ'd hφ'i hφ'Z`. Use `⟨(fun w : Fin n ⊕ Fin M.m → ℂ => fun i => w (e.symm i)) ⁻¹' O', hO'o.preimage (continuous_pi fun i => continuous_apply _), ?_⟩` and prove the remaining obligations.

Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, rfl⟩`. Establish `hmem : φ' t ∈ zeroSetIn I' ∩ O'`. Rewrite using `[← hO']`.

Conclude with `⟨t, ht, rfl⟩`. Conclude with `⟨hφZ ht, hmem.2⟩`. Introduce and unpack `⟨hwZ, hwO⟩`. Establish `hw' : (fun i => w (e.symm i)) ∈ zeroSetIn I'` using `(hZ _).2 (by simpa using hwZ)`. Establish `hmem : (fun i => w (e.symm i)) ∈ φ' '' U`.

Rewrite using `[hO']`. Conclude with `⟨hw', hwO⟩`. Take `⟨t, ht, hteq⟩` from `hmem`. Use `⟨t, ht, funext fun i => ?_⟩` and prove the remaining obligations. Use `congrFun hteq (e i)` as an intermediate fact.

Simplify `this` using `[hφ']`.
-/
theorem NormalModelOpenMapping.proof (hirr : NormalLocallyIrreducible.Statement)
    (hoff : BranchOffHypersurface.Statement) (hinj : InjectiveHolomorphicOpen.Statement) :
    NormalModelOpenMapping.Statement := by
  intro n k J M U φ hJ hdim hU hφ hφi hφZ
  set e : Fin n ⊕ Fin M.m ≃ Fin (n + M.m) := finSumFinEquiv with he
  set RE : MvPolynomial (Fin n ⊕ Fin M.m) ℂ ≃+* MvPolynomial (Fin (n + M.m)) ℂ :=
    (renameEquiv ℂ e).toRingEquiv with hRE
  set I' := M.ideal.map (RE : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* MvPolynomial (Fin (n + M.m)) ℂ) with hI'
  have QE := Ideal.quotientEquiv M.ideal I' RE rfl
  have := M.isPrime
  have hI'p : I'.IsPrime := Ideal.map_isPrime_of_equiv RE
  have := M.isIntegrallyClosed
  have hic : IsIntegrallyClosed (MvPolynomial (Fin (n + M.m)) ℂ ⧸ I') := IsIntegrallyClosed.of_equiv QE
  have hdim' : ringKrullDim (MvPolynomial (Fin (n + M.m)) ℂ ⧸ I') = (k : ℕ) := by
    rw [← ringKrullDim_eq_of_ringEquiv QE, M.ringKrullDim_eq, hdim]
  have hZ : ∀ z : Fin (n + M.m) → ℂ, z ∈ zeroSetIn I' ↔ (fun i => z (e i)) ∈ zeroSetIn M.ideal := by
    intro z
    constructor
    · intro hz q hq
      have h2 := hz _ (Ideal.mem_map_of_mem _ hq)
      change eval z (rename e q) = 0 at h2
      rwa [eval_rename] at h2
    · intro hz q' hq'
      obtain ⟨q, hq, rfl⟩ := (Ideal.mem_map_of_equiv RE q').1 hq'
      change eval z (rename e q) = 0
      rw [eval_rename]
      exact hz q hq
  set φ' : (Fin k → ℂ) → Fin (n + M.m) → ℂ := fun t i => φ t (e.symm i) with hφ'
  have hφ'd : DifferentiableOn ℂ φ' U :=
    differentiableOn_pi.2 fun i => differentiableOn_pi.1 hφ (e.symm i)
  have hφ'e : ∀ t, (fun i => φ' t (e i)) = φ t := fun t => funext fun i => by simp [hφ']
  have hφ'i : Set.InjOn φ' U := fun s hs t ht hst => hφi hs ht (by rw [← hφ'e s, ← hφ'e t, hst])
  have hφ'Z : Set.MapsTo φ' U (zeroSetIn I') := fun t ht => (hZ _).2 (by rw [hφ'e]; exact hφZ ht)
  obtain ⟨O', hO'o, hO'⟩ := openMapping_of_isIntegrallyClosed hirr hoff hinj I' hI'p hic hdim' U φ' hU hφ'd
    hφ'i hφ'Z
  refine ⟨(fun w : Fin n ⊕ Fin M.m → ℂ => fun i => w (e.symm i)) ⁻¹' O',
    hO'o.preimage (continuous_pi fun i => continuous_apply _), ?_⟩
  ext w
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hmem : φ' t ∈ zeroSetIn I' ∩ O' := by
      rw [← hO']
      exact ⟨t, ht, rfl⟩
    exact ⟨hφZ ht, hmem.2⟩
  · rintro ⟨hwZ, hwO⟩
    have hw' : (fun i => w (e.symm i)) ∈ zeroSetIn I' := (hZ _).2 (by simpa using hwZ)
    have hmem : (fun i => w (e.symm i)) ∈ φ' '' U := by
      rw [hO']
      exact ⟨hw', hwO⟩
    obtain ⟨t, ht, hteq⟩ := hmem
    refine ⟨t, ht, funext fun i => ?_⟩
    have := congrFun hteq (e i)
    simpa [hφ'] using this

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
