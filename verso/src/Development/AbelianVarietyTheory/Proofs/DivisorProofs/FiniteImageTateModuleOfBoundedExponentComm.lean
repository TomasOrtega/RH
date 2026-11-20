import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderOfTrivialModSqTateModuleStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Proof.FiniteInertiaImage

/- English proof (translation)
Establish `hu : galTate A l (σ * τ⁻¹) = 1`. Use `GlobalTheory.T.eq_one_of_finite_order_of_trivial_mod_sq_tateModule l (ptOver K Ω ⟶ A) _ E hE0 (hE _ (I.mul_mem hσ (I.inv_mem hτ))) fun t => ?_` and prove the remaining obligations. Rewrite using `[lev_galTate]`. Establish `hy : galPts A τ⁻¹ (t.lev 2) ^ (l ^ 2) = 1` using `by rw [← map_pow, t.lev_pow, map_one]`. Establish `e1 : galPts A (σ * τ⁻¹) (t.lev 2) = galPts A σ (galPts A τ⁻¹ (t.lev 2))`.

Express the relevant statement in the definitionally equal form `specAut (σ * τ⁻¹) ≫ t.lev 2 = specAut σ ≫ specAut τ⁻¹ ≫ t.lev 2`. Rewrite using `[specAut_mul, Category.assoc]`. Establish `e2 : galPts A τ (galPts A τ⁻¹ (t.lev 2)) = t.lev 2`. Express the relevant statement in the definitionally equal form `specAut τ ≫ specAut τ⁻¹ ≫ t.lev 2 = t.lev 2`. Rewrite using `[← Category.assoc, ← specAut_mul, mul_inv_cancel, specAut_one, Category.id_comp]`.

Rewrite using `[e1, h _ hy, e2]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem galTate_eq_of_agree {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A]
    [IsCommMonObj A] (l : ℕ) [Fact l.Prime] (I : Subgroup (Ω ≃ₐ[K] Ω)) (E : ℕ) (hE0 : 0 < E)
    (hE : ∀ σ ∈ I, galTate A l σ ^ E = 1) {σ τ : Ω ≃ₐ[K] Ω} (hσ : σ ∈ I) (hτ : τ ∈ I)
    (h : ∀ x : ptOver K Ω ⟶ A, x ^ (l ^ 2) = 1 → galPts A σ x = galPts A τ x) :
    galTate A l σ = galTate A l τ := by
  have hu : galTate A l (σ * τ⁻¹) = 1 := by
    refine GlobalTheory.T.eq_one_of_finite_order_of_trivial_mod_sq_tateModule l (ptOver K Ω ⟶ A) _ E hE0 (hE _ (I.mul_mem hσ (I.inv_mem hτ))) fun t => ?_
    rw [lev_galTate]
    have hy : galPts A τ⁻¹ (t.lev 2) ^ (l ^ 2) = 1 := by rw [← map_pow, t.lev_pow, map_one]
    have e1 : galPts A (σ * τ⁻¹) (t.lev 2) = galPts A σ (galPts A τ⁻¹ (t.lev 2)) := by
      change specAut (σ * τ⁻¹) ≫ t.lev 2 = specAut σ ≫ specAut τ⁻¹ ≫ t.lev 2
      rw [specAut_mul, Category.assoc]
    have e2 : galPts A τ (galPts A τ⁻¹ (t.lev 2)) = t.lev 2 := by
      change specAut τ ≫ specAut τ⁻¹ ≫ t.lev 2 = t.lev 2
      rw [← Category.assoc, ← specAut_mul, mul_inv_cancel, specAut_one, Category.id_comp]
    rw [e1, h _ hy, e2]
  calc galTate A l σ = galTate A l (σ * τ⁻¹ * τ) := by rw [inv_mul_cancel_right]
    _ = galTate A l τ := by rw [map_mul, hu, _root_.one_mul]

/- English proof (translation)
Introduce `K Ω _ _ _ A _ _ l _ I hS _ ⟨E, hE0, hE⟩`. Set `S` to `{x : ptOver K Ω ⟶ A // x ^ (l ^ 2) = 1}`. Establish `hmap : ∀ (σ : Ω ≃ₐ[K] Ω) (x : S), galPts A σ x.1 ^ (l ^ 2) = 1` using `fun σ x => by`. Rewrite using `[← map_pow, x.2, map_one]`. Set `g : (Ω ≃ₐ[K] Ω) → S → S` to `fun σ x => ⟨galPts A σ x.1, hmap σ x⟩`.

Set `F : galTate A l '' (I : Set (Ω ≃ₐ[K] Ω)) → S → S` to `fun u => g u.2.choose`. Establish `hF : Function.Injective F`. Introduce and unpack `⟨u, hu⟩ ⟨u', hu'⟩ e`. Establish `h1` using `hu.choose_spec`. Establish `h2` using `hu'.choose_spec`.

Use `Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `u = u'`. Rewrite using `[← h1.2, ← h2.2]`. Use `galTate_eq_of_agree A l I E hE0 hE h1.1 h2.1 fun x hx => ?_` and prove the remaining obligations. Use `congrFun e ⟨x, hx⟩` as an intermediate fact.

Conclude with `congrArg Subtype.val this`. Conclude with `Set.finite_coe_iff.1 (Finite.of_injective F hF)`.
-/
theorem finite_image_galTate : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A]
    [IsCommMonObj A] (l : ℕ) [Fact l.Prime] (I : Subgroup (Ω ≃ₐ[K] Ω)),
    Finite {x : ptOver K Ω ⟶ A // x ^ (l ^ 2) = 1} →
    (∀ σ τ : Ω ≃ₐ[K] Ω, galTate A l σ * galTate A l τ = galTate A l τ * galTate A l σ) →
    (∃ E : ℕ, 0 < E ∧ ∀ σ ∈ I, galTate A l σ ^ E = 1) →
    (galTate A l '' (I : Set (Ω ≃ₐ[K] Ω))).Finite := by
  intro K Ω _ _ _ A _ _ l _ I hS _ ⟨E, hE0, hE⟩
  let S := {x : ptOver K Ω ⟶ A // x ^ (l ^ 2) = 1}
  have hmap : ∀ (σ : Ω ≃ₐ[K] Ω) (x : S), galPts A σ x.1 ^ (l ^ 2) = 1 := fun σ x => by
    rw [← map_pow, x.2, map_one]
  let g : (Ω ≃ₐ[K] Ω) → S → S := fun σ x => ⟨galPts A σ x.1, hmap σ x⟩
  let F : galTate A l '' (I : Set (Ω ≃ₐ[K] Ω)) → S → S := fun u => g u.2.choose
  have hF : Function.Injective F := by
    rintro ⟨u, hu⟩ ⟨u', hu'⟩ e
    have h1 := hu.choose_spec
    have h2 := hu'.choose_spec
    refine Subtype.ext ?_
    change u = u'
    rw [← h1.2, ← h2.2]
    refine galTate_eq_of_agree A l I E hE0 hE h1.1 h2.1 fun x hx => ?_
    have := congrFun e ⟨x, hx⟩
    exact congrArg Subtype.val this
  exact Set.finite_coe_iff.1 (Finite.of_injective F hF)

end GlobalTheory.Proof.FiniteInertiaImage
