import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLiftFormallySmoothSquareZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothRangeOfIdempotentAlgHomStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Obs

/- English proof (translation)
Introduce `R R₀ _ _ I hI π hπ hk B' B₀' _ _ _ _ p' hs' hp' hker' _ B₀ _ _ i r hri`. Take `⟨e, he, hpe⟩` from `GlobalTheory.T.exists_idempotent_lift_formallySmooth_squareZero R R₀ I hI π hπ hk B' B₀' p' hs' hp' hker' (i.comp r) (fun x ↦ by simp [hri])`. Establish `hmem : ∀ x ∈ I.map (algebraMap R B'), e.rangeRestrict x ∈ I.map (algebraMap R e.range)`. Introduce `x hx`. Establish `hle : I.map (algebraMap R B') ≤ (I.map (algebraMap R e.range)).comap (e.rangeRestrict : B' →+* e.range)`.

Rewrite using `[Ideal.map_le_iff_le_comap, Ideal.comap_comap]`. Introduce `y hy`. Simplify using `only [Ideal.mem_comap, RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]`. Rewrite using `[AlgHom.commutes]`. Conclude with `Ideal.mem_map_of_mem _ hy`.

Conclude with `hle hx`. Use `⟨e.range, inferInstance, inferInstance, ((r : B₀' →+* B₀).comp p').comp (e.range.val : e.range →+* B'), ?_, ?_, ?_, GlobalTheory.T.smooth_range_of_idempotent_algHom R B' e he⟩` and prove the remaining obligations. Introduce `c b show r (p' ((c • b : e.range) : B')) = π c • r (p' (b : B'))`. Rewrite using `[Subalgebra.coe_smul, hs' c (b : B'), map_smul]`. Introduce `y`.

Take `⟨b, hb⟩` from `hp' (i y)`. Use `⟨⟨e b, e.mem_range_self b⟩, ?_⟩` and prove the remaining obligations. Use `show r (p' (e b)) = y`. Rewrite using `[hpe, hb]`. Simplify using `[hri]`.

Introduce `b`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Express the relevant statement in the definitionally equal form `r (p' (b : B')) = 0 at h`. Take `⟨c, hc⟩` from `b.2`.

Express the relevant statement in the definitionally equal form `e c = (b : B') at hc`. Establish `hfix : e (b : B') = b` using `by rw [← hc, he]`. Establish `h0 : p' (b : B') = 0`. Rewrite using `[← hfix, hpe]`. Simplify using `[h]`.

Establish `hb : e.rangeRestrict (b : B') = b` using `Subtype.ext hfix`. Rewrite using `[← hb]`. Conclude with `hmem _ ((hker' _).mp h0)`. Introduce `h`. Establish `hle : I.map (algebraMap R e.range) ≤ RingHom.ker (((r : B₀' →+* B₀).comp p').comp (e.range.val : e.range →+* B'))`.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`. Simplify using `only [Ideal.mem_comap, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]`. Establish `hx0 : π x = 0` using `by rw [← RingHom.mem_ker, hk]; exact hx`. Use `show r (p' (algebraMap R B' x)) = 0`.

Rewrite using `[hs'.map_algebraMap, hx0, map_zero, map_zero]`. Conclude with `hle h`.
-/
theorem retractLift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) [Algebra.Smooth R B'] (B₀ : Type) [CommRing B₀] [Algebra R₀ B₀] (i : B₀ →ₐ[R₀] B₀') (r : B₀' →ₐ[R₀] B₀), (∀ x, r (i x) = x) → ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (p : B →+* B₀), SemiHom π p ∧ Function.Surjective p ∧ (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) ∧ Algebra.Smooth R B := by
  intro R R₀ _ _ I hI π hπ hk B' B₀' _ _ _ _ p' hs' hp' hker' _ B₀ _ _ i r hri
  obtain ⟨e, he, hpe⟩ := GlobalTheory.T.exists_idempotent_lift_formallySmooth_squareZero R R₀ I hI π hπ hk B' B₀' p' hs' hp' hker' (i.comp r) (fun x ↦ by simp [hri])
  have hmem : ∀ x ∈ I.map (algebraMap R B'), e.rangeRestrict x ∈ I.map (algebraMap R e.range) := by
    intro x hx
    have hle : I.map (algebraMap R B') ≤ (I.map (algebraMap R e.range)).comap (e.rangeRestrict : B' →+* e.range) := by
      rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap]
      intro y hy
      simp only [Ideal.mem_comap, RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
      rw [AlgHom.commutes]
      exact Ideal.mem_map_of_mem _ hy
    exact hle hx
  refine ⟨e.range, inferInstance, inferInstance,
    ((r : B₀' →+* B₀).comp p').comp (e.range.val : e.range →+* B'), ?_, ?_, ?_, GlobalTheory.T.smooth_range_of_idempotent_algHom R B' e he⟩
  · intro c b
    show r (p' ((c • b : e.range) : B')) = π c • r (p' (b : B'))
    rw [Subalgebra.coe_smul, hs' c (b : B'), map_smul]
  · intro y
    obtain ⟨b, hb⟩ := hp' (i y)
    refine ⟨⟨e b, e.mem_range_self b⟩, ?_⟩
    show r (p' (e b)) = y
    rw [hpe, hb]
    simp [hri]
  · intro b
    constructor
    · intro h
      change r (p' (b : B')) = 0 at h
      obtain ⟨c, hc⟩ := b.2
      change e c = (b : B') at hc
      have hfix : e (b : B') = b := by rw [← hc, he]
      have h0 : p' (b : B') = 0 := by
        rw [← hfix, hpe]
        simp [h]
      have hb : e.rangeRestrict (b : B') = b := Subtype.ext hfix
      rw [← hb]
      exact hmem _ ((hker' _).mp h0)
    · intro h
      have hle : I.map (algebraMap R e.range) ≤ RingHom.ker (((r : B₀' →+* B₀).comp p').comp (e.range.val : e.range →+* B')) := by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        simp only [Ideal.mem_comap, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
        have hx0 : π x = 0 := by rw [← RingHom.mem_ker, hk]; exact hx
        show r (p' (algebraMap R B' x)) = 0
        rw [hs'.map_algebraMap, hx0, map_zero, map_zero]
      exact hle h

end GlobalTheory.Obs
