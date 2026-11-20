import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockGraphImage
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

/- English proof (translation)
Introduce `K _ ι _ Ω _ _ κ _ y k₀ M N x hB`. Set `φ : MRing ι ⧸ mCoordIdeal y →+* MvPolynomial K Ω` to `Ideal.Quotient.lift (mCoordIdeal y) (mConeMap y).toRingHom fun a ha => RingHom.mem_ker.1 ha`. Establish `hφ : Function.Injective φ`. Use `(injective_iff_map_eq_zero φ).2 fun a ha => ?_` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (RingHom.mem_ker.2 ha)`. Set `ψ : Polynomial Ω →+* MvPolynomial Unit (MvPolynomial K Ω)` to `Polynomial.eval₂RingHom ((C : MvPolynomial K Ω →+* _).comp C) (C (X k₀) * X ())`. Set `ev : MvPolynomial Unit (MvPolynomial K Ω) →+* Polynomial Ω` to `eval₂Hom (Polynomial.C.comp (MvPolynomial.eval fun _ => (1 : Ω))) fun _ => Polynomial.X`. Establish `hev : ∀ p, ev (ψ p) = p`. Establish `h : ev.comp ψ = RingHom.id _`.

Apply `Polynomial.ringHom_ext` to reduce the goal to its premises. Introduce `c`. Simplify using `[ψ, ev]`. Simplify using `[ψ, ev]`. Conclude with `fun p => RingHom.congr_fun h p`.

Establish `hcone : ∀ q, mConeMap y (blockForms k₀ M q) = C (x q) * X k₀`. Introduce `q`. Simplify using `only [blockForms, map_sum, map_mul, mConeMap, aeval_X, aeval_C, hB.1 q, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[mul_assoc]`.

Set `G : MRing (GlobalTheory κ) →+* MvPolynomial Unit (MvPolynomial K Ω)` to `(MvPolynomial.map φ).comp ((graphMap (mCoordIdeal y) (blockForms k₀ M)).comp (rename (inrV (ι := ι) (ι₂ := GlobalTheory κ)) : MRing (GlobalTheory κ) →ₐ[ℤ] _).toRingHom)`. Establish `hG : ∀ f, G f = ψ (coneMap ℤ x f)`. Establish `h : G = ψ.comp (coneMap ℤ x).toRingHom`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `n`.

Conclude with `RingHom.congr_fun (RingHom.ext_int (G.comp C) ((ψ.comp (coneMap ℤ x).toRingHom).comp C)) n`. Introduce and unpack `⟨u, j⟩`. Consider the cases of `u`. Simplify using `only [G, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X]`. Rewrite using `[show (inrV (ι := ι) (ι₂ := GlobalTheory κ) ⟨(), j⟩) = ⟨Sum.inr (), j⟩ from rfl]`.

Rewrite using `[graphMap, eval₂Hom_X']`. Simplify using `only [map_mul, map_C, map_X, coneMap, aeval_X]`. Rewrite using `[show φ (Ideal.Quotient.mk (mCoordIdeal y) (blockForms k₀ M ⟨(), j⟩)) = C (x ⟨(), j⟩) * X k₀ from (Ideal.Quotient.lift_mk _ _ _).trans (hcone _)]`. Simplify using `[ψ, mul_assoc]`. Conclude with `fun f => RingHom.congr_fun h f`.

Use extensionality with `f`. Use `show rename inrV f ∈ RingHom.ker (graphMap (mCoordIdeal y) (blockForms k₀ M)) ↔ f ∈ RingHom.ker (coneMap ℤ x)`. Rewrite using `[RingHom.mem_ker, RingHom.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `h0 : G f = 0` using `by show MvPolynomial.map φ (graphMap (mCoordIdeal y) (blockForms k₀ M) (rename inrV f)) = 0`. Rewrite using `[h, map_zero]`. Rewrite `h0` using `[hG]`. Rewrite using `[← hev (coneMap ℤ x f), h0, map_zero]`. Introduce `h`.

Apply `MvPolynomial.map_injective φ hφ` to reduce the goal to its premises. Rewrite using `[map_zero]`. Use `show G f = 0`. Rewrite using `[hG, h, map_zero]`.
-/
theorem BlockGraphImage.proof : BlockGraphImage.Statement := by
  intro K _ ι _ Ω _ _ κ _ y k₀ M N x hB

  let φ : MRing ι ⧸ mCoordIdeal y →+* MvPolynomial K Ω :=
    Ideal.Quotient.lift (mCoordIdeal y) (mConeMap y).toRingHom fun a ha => RingHom.mem_ker.1 ha
  have hφ : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun a ha => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact Ideal.Quotient.eq_zero_iff_mem.2 (RingHom.mem_ker.2 ha)

  let ψ : Polynomial Ω →+* MvPolynomial Unit (MvPolynomial K Ω) :=
    Polynomial.eval₂RingHom ((C : MvPolynomial K Ω →+* _).comp C) (C (X k₀) * X ())
  let ev : MvPolynomial Unit (MvPolynomial K Ω) →+* Polynomial Ω :=
    eval₂Hom (Polynomial.C.comp (MvPolynomial.eval fun _ => (1 : Ω))) fun _ => Polynomial.X
  have hev : ∀ p, ev (ψ p) = p := by
    have h : ev.comp ψ = RingHom.id _ := by
      apply Polynomial.ringHom_ext
      · intro c
        simp [ψ, ev]
      · simp [ψ, ev]
    exact fun p => RingHom.congr_fun h p

  have hcone : ∀ q, mConeMap y (blockForms k₀ M q) = C (x q) * X k₀ := by
    intro q
    simp only [blockForms, map_sum, map_mul, mConeMap, aeval_X, aeval_C, hB.1 q, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_assoc]
  let G : MRing (GlobalTheory κ) →+* MvPolynomial Unit (MvPolynomial K Ω) :=
    (MvPolynomial.map φ).comp ((graphMap (mCoordIdeal y) (blockForms k₀ M)).comp
      (rename (inrV (ι := ι) (ι₂ := GlobalTheory κ)) : MRing (GlobalTheory κ) →ₐ[ℤ] _).toRingHom)
  have hG : ∀ f, G f = ψ (coneMap ℤ x f) := by
    have h : G = ψ.comp (coneMap ℤ x).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro n
        exact RingHom.congr_fun (RingHom.ext_int (G.comp C) ((ψ.comp (coneMap ℤ x).toRingHom).comp C)) n
      · rintro ⟨u, j⟩
        cases u
        simp only [G, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X]
        rw [show (inrV (ι := ι) (ι₂ := GlobalTheory κ) ⟨(), j⟩) = ⟨Sum.inr (), j⟩ from rfl]
        rw [graphMap, eval₂Hom_X']
        simp only [map_mul, map_C, map_X, coneMap, aeval_X]
        rw [show φ (Ideal.Quotient.mk (mCoordIdeal y) (blockForms k₀ M ⟨(), j⟩)) = C (x ⟨(), j⟩) * X k₀ from
          (Ideal.Quotient.lift_mk _ _ _).trans (hcone _)]
        simp [ψ, mul_assoc]
    exact fun f => RingHom.congr_fun h f
  ext f
  show rename inrV f ∈ RingHom.ker (graphMap (mCoordIdeal y) (blockForms k₀ M)) ↔ f ∈ RingHom.ker (coneMap ℤ x)
  rw [RingHom.mem_ker, RingHom.mem_ker]
  constructor
  · intro h
    have h0 : G f = 0 := by
      show MvPolynomial.map φ (graphMap (mCoordIdeal y) (blockForms k₀ M) (rename inrV f)) = 0
      rw [h, map_zero]
    rw [hG] at h0
    rw [← hev (coneMap ℤ x f), h0, map_zero]
  · intro h
    apply MvPolynomial.map_injective φ hφ
    rw [map_zero]
    show G f = 0
    rw [hG, h, map_zero]

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
