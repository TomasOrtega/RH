import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `h`. Unfold `BaseOfChart`. Introduce `l O _ _ _ ϖ hϖ hl hlu Y g hg U hU`. Set `φ : O →+* Γ(Y, U)` to `(g.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom`. Establish `hφ : ∀ a : O, φ a = (Y.presheaf.map (homOfLE le_top).op).hom ((g.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a))` using `fun a => rfl`.

Establish `hsm : φ.Smooth`. Use `RingHom.Smooth.comp (RingHom.Smooth.of_bijective ?_) ?_` and prove the remaining obligations. Conclude with `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of O)).inv)`. Conclude with `HasRingHomProperty.appLE @Smooth g hg ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)`. Use `letI : Algebra O Γ(Y, U) := φ.toAlgebra`.

Use `haveI : Algebra.Smooth O Γ(Y, U) := hsm`. Establish `hb` using `h l O Γ(Y, U) ϖ hϖ hl hlu`. Establish `hϖφ : (algebraMap O Γ(Y, U)) ϖ = (Y.presheaf.map (homOfLE le_top).op).hom (fn g ϖ)` using `hφ ϖ`. Rewrite `hb` using `[hϖφ]`. Use `⟨hb, 1, ?_⟩` and prove the remaining obligations.

Establish `hmem : (l : O) ∈ Ideal.span {ϖ}`. Rewrite using `[← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).mpr hlu`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp hmem`. Rewrite using `[pow_one, ← hϖφ, Ideal.mem_span_singleton']`.

Use `⟨algebraMap O Γ(Y, U) c, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul, hc, map_natCast]`.
-/
theorem UpperTheory.Gal.crystallineComparison.baseChart_of :
    BaseOfSmooth → BaseOfChart := by
  intro h
  unfold BaseOfChart
  intro l O _ _ _ ϖ hϖ hl hlu Y g hg U hU
  let φ : O →+* Γ(Y, U) :=
    (g.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom
  have hφ : ∀ a : O, φ a = (Y.presheaf.map (homOfLE le_top).op).hom
      ((g.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a)) := fun a => rfl
  have hsm : φ.Smooth := by
    refine RingHom.Smooth.comp (RingHom.Smooth.of_bijective ?_) ?_
    · exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of O)).inv)
    · exact HasRingHomProperty.appLE @Smooth g hg ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  letI : Algebra O Γ(Y, U) := φ.toAlgebra
  haveI : Algebra.Smooth O Γ(Y, U) := hsm
  have hb := h l O Γ(Y, U) ϖ hϖ hl hlu
  have hϖφ : (algebraMap O Γ(Y, U)) ϖ = (Y.presheaf.map (homOfLE le_top).op).hom (fn g ϖ) := hφ ϖ
  rw [hϖφ] at hb
  refine ⟨hb, 1, ?_⟩
  have hmem : (l : O) ∈ Ideal.span {ϖ} := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
    exact (IsLocalRing.mem_maximalIdeal _).mpr hlu
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  rw [pow_one, ← hϖφ, Ideal.mem_span_singleton']
  refine ⟨algebraMap O Γ(Y, U) c, ?_⟩
  rw [← map_mul, hc, map_natCast]
