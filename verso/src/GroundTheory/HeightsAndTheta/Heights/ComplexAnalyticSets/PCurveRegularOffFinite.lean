import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveRegularOffFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveProperClosedFinite
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StFrameGraphGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

/- English proof (translation)
Introduce `n W hW hdim`. Establish `hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = ((1 : ℕ) : WithBot ℕ∞)`. Rewrite using `[hdim]`. Both sides reduce to the same expression. Set `b` to `EuclideanSpace.basisFun (Fin n) ℂ`.

Take `⟨I₀, q, hcard, hqW, hreg⟩` from `hG n 1 W hW hd b`. Take `⟨i₀, hI₀⟩` from `Finset.card_eq_one.mp hcard`. Establish `hi₀ : i₀ ∈ I₀` using `by rw [hI₀]; exact Finset.mem_singleton_self i₀`. Establish `hsub : ∀ j : I₀, j = ⟨i₀, hi₀⟩` using `fun j => Subtype.ext (Finset.mem_singleton.mp (hI₀ ▸ j.2))`. Establish `hKW : ¬ Ideal.span {q} ≤ W` using `fun h => hqW (h (Ideal.subset_span rfl))`.

Use `⟨zeroSet W ∩ zeroSet (Ideal.span {q}), hP n W _ hW hdim hKW, ?_⟩` and prove the remaining obligations. Introduce `x hx hxF`. Establish `hqx : eval x q ≠ 0`. Introduce `h0`. Use `hxF ⟨hx, fun p hp => ?_⟩` and prove the remaining obligations.

Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.mp hp`. Simplify using `[h0]`. Set `T : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)` to `((EuclideanSpace.equiv (Fin n) ℂ).symm : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n))`. Set `S : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)` to `((EuclideanSpace.equiv (Fin n) ℂ) : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ))`. Establish `hST : ∀ y, S (T y) = y` using `fun y => rfl`.

Establish `hTS : ∀ w, T (S w) = w` using `fun w => rfl`. Establish `hZ : ∀ y : Fin n → ℂ, y ∈ zeroSet W ↔ T y ∈ zeroSetEuc W` using `fun y => Iff.rfl`. Take `⟨Ω, V, g, hΩ, hV, hxV, hg, hproj, hgraph⟩` from `hreg (T x) ((hZ x).mp hx) hqx`. Set `ι : ℂ →L[ℂ] (I₀ → ℂ)` to `ContinuousLinearMap.pi fun _ : I₀ => ContinuousLinearMap.id ℂ ℂ`. Set `A : (Fin n → ℂ) →L[ℂ] ℂ` to `ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i₀`.

Establish `hO : IsOpen (ι ⁻¹' Ω)` using `hΩ.preimage ι.continuous`. Use `⟨A, ι ⁻¹' Ω, T ⁻¹' V, fun y => S (g (ι y)), hO, hV.preimage T.continuous, hxV, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(S.differentiable.comp_differentiableOn (hg.comp ι.differentiable.differentiableOn fun y hy => hy)).analyticOnNhd hO`. Introduce `y hy`. Establish `h1` using `congrFun (hproj (ι y) hy) ⟨i₀, hi₀⟩`.

Simplify using `only [frameProj, b, EuclideanSpace.basisFun_inner] at h1`. Conclude with `h1`. Use extensionality with `x'`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx'Z, hx'V⟩`.

Establish `hmem : T x' ∈ zeroSetEuc W ∩ V` using `⟨(hZ x').mp hx'Z, hx'V⟩`. Rewrite `hmem` using `[hgraph]`. Take `⟨u, hu, hgu⟩` from `hmem`. Establish `hιu : ι (u ⟨i₀, hi₀⟩) = u` using `funext fun j => by rw [hsub j]; rfl`. Use `⟨u ⟨i₀, hi₀⟩, ?_, ?_⟩` and prove the remaining obligations.

Use `show ι _ ∈ Ω`. Rewrite using `[hιu]` and apply the resulting hypothesis. Simplify using `only [hιu, hgu, hST]`. Introduce and unpack `⟨y, hy, rfl⟩`. Establish `hmem : g (ι y) ∈ zeroSetEuc W ∩ V` using `hgraph ▸ Set.mem_image_of_mem g hy`.

Conclude with `⟨(hZ _).mpr (by rw [hTS]; exact hmem.1), by show T (S (g (ι y))) ∈ V; rw [hTS]; exact hmem.2⟩`.
-/
theorem CurveRegularOffFinite.proof (hG : FrameGraphGeneric.Statement)
    (hP : CurveProperClosedFinite.Statement) : CurveRegularOffFinite.Statement := by
  intro n W hW hdim
  have hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = ((1 : ℕ) : WithBot ℕ∞) := by
    rw [hdim]; rfl
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  obtain ⟨I₀, q, hcard, hqW, hreg⟩ := hG n 1 W hW hd b
  obtain ⟨i₀, hI₀⟩ := Finset.card_eq_one.mp hcard
  have hi₀ : i₀ ∈ I₀ := by rw [hI₀]; exact Finset.mem_singleton_self i₀
  have hsub : ∀ j : I₀, j = ⟨i₀, hi₀⟩ := fun j => Subtype.ext (Finset.mem_singleton.mp (hI₀ ▸ j.2))
  have hKW : ¬ Ideal.span {q} ≤ W := fun h => hqW (h (Ideal.subset_span rfl))
  refine ⟨zeroSet W ∩ zeroSet (Ideal.span {q}), hP n W _ hW hdim hKW, ?_⟩
  intro x hx hxF
  have hqx : eval x q ≠ 0 := by
    intro h0
    refine hxF ⟨hx, fun p hp => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    simp [h0]

  let T : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    ((EuclideanSpace.equiv (Fin n) ℂ).symm : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n))
  let S : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ) :=
    ((EuclideanSpace.equiv (Fin n) ℂ) : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ))
  have hST : ∀ y, S (T y) = y := fun y => rfl
  have hTS : ∀ w, T (S w) = w := fun w => rfl
  have hZ : ∀ y : Fin n → ℂ, y ∈ zeroSet W ↔ T y ∈ zeroSetEuc W := fun y => Iff.rfl
  obtain ⟨Ω, V, g, hΩ, hV, hxV, hg, hproj, hgraph⟩ := hreg (T x) ((hZ x).mp hx) hqx

  let ι : ℂ →L[ℂ] (I₀ → ℂ) := ContinuousLinearMap.pi fun _ : I₀ => ContinuousLinearMap.id ℂ ℂ
  let A : (Fin n → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i₀
  have hO : IsOpen (ι ⁻¹' Ω) := hΩ.preimage ι.continuous
  refine ⟨A, ι ⁻¹' Ω, T ⁻¹' V, fun y => S (g (ι y)), hO, hV.preimage T.continuous, hxV, ?_, ?_, ?_⟩
  · exact (S.differentiable.comp_differentiableOn
      (hg.comp ι.differentiable.differentiableOn fun y hy => hy)).analyticOnNhd hO
  · intro y hy
    have h1 := congrFun (hproj (ι y) hy) ⟨i₀, hi₀⟩
    simp only [frameProj, b, EuclideanSpace.basisFun_inner] at h1
    exact h1
  · ext x'
    constructor
    · rintro ⟨hx'Z, hx'V⟩
      have hmem : T x' ∈ zeroSetEuc W ∩ V := ⟨(hZ x').mp hx'Z, hx'V⟩
      rw [hgraph] at hmem
      obtain ⟨u, hu, hgu⟩ := hmem
      have hιu : ι (u ⟨i₀, hi₀⟩) = u := funext fun j => by rw [hsub j]; rfl
      refine ⟨u ⟨i₀, hi₀⟩, ?_, ?_⟩
      · show ι _ ∈ Ω
        rwa [hιu]
      · simp only [hιu, hgu, hST]
    · rintro ⟨y, hy, rfl⟩
      have hmem : g (ι y) ∈ zeroSetEuc W ∩ V := hgraph ▸ Set.mem_image_of_mem g hy
      exact ⟨(hZ _).mpr (by rw [hTS]; exact hmem.1), by show T (S (g (ι y))) ∈ V; rw [hTS]; exact hmem.2⟩

end GroundTheory.Heights₂.Heights
