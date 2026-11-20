import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOrderSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsOddNeZero
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.EqOneOfPowEqOneOfCongrOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsEqPowOfTorsionCompEqOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatAndSurjectiveOfIsFiniteAbelianEnd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulAFiniteFlatSurjectiveEtale
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteMulByNatAbelianVarietyAlgClosed
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianVarietyTorsionFiniteEndomorphismDivisible

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleRigid

open GlobalTheory.SerreField in

/- English proof (translation)
Introduce `hfin hsep K _ _ A _ _ hA L hL hamp N hN3 hNK σ hσ hpull hfix`. Use `haveI := hσ`. Take `⟨m, hm0, hord⟩` from `hfin K A hA L hL hamp σ hσ hpull`. Establish `hFS : ∀ n : ℕ, 1 ≤ n → Flat (Out.mulA A n).left ∧ Surjective (Out.mulA A n).left` using `fun n hn => flat_and_surjective_of_isFinite_abelianEnd forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K A hA _ (GlobalTheory.AbLaw.MulN.isMonHom_mulA A n) (GlobalTheory.MulFiniteAny.isFinite_mulA K A hA n hn)`. Establish `hu : IsMonHom (σ.hom * (𝟙 A)⁻¹)`.

Rewrite using `[Hom.mul_def, Hom.inv_def]`. Use `infer_instance`. Take `⟨-, hdiv⟩` from `GlobalTheory.TorsionDivisible.finite_torsion_and_divisible K A hA N hNK`. Take `⟨φ, hφ, e⟩` from `hdiv (σ.hom * (𝟙 A)⁻¹) hu (fun x hx => by`. Rewrite using `[MonObj.comp_mul, GrpObj.comp_inv, hfix K (𝟙 _) x hx, Category.comp_id, mul_inv_cancel])`.

Use `haveI := hφ`. Establish `key : toRing σ.hom = 1`. Use `GlobalTheory.eq_one_of_pow_eq_one_of_congr_one (homRing A) N hN3 ?_ ?_ (toRing σ.hom) (toRing φ) m hm0 ?_ ?_` and prove the remaining obligations. Introduce and unpack `k ⟨f, u, hu, hf⟩ hk h`. Establish `h1` using `congrArg (fun g : homRing A => g.1 (Additive.ofMul (𝟙 A))) h`.

Simplify using `only [natCast_mul_apply, hf, Category.id_comp] at h1`. Establish `h2 : u ^ k = 1` using `h1`. Establish `h3 : u = 1`. Take `⟨_, _⟩` from `hFS k (by omega)`. Use `haveI : Epi (Out.mulA A k).left := Flat.epi_of_flat_of_surjective _`.

Use `Over.OverMorphism.ext ((cancel_epi (Out.mulA A k).left).1 ?_)` and prove the remaining obligations. Rewrite using `[← Over.comp_left, ← Over.comp_left, MonObj.comp_one, Out.mulA, MonObj.pow_comp, Category.id_comp, h2]`. Conclude with `homRing_ext (by rw [hf, h3, Category.id_comp]; rfl)`. Introduce and unpack `q ⟨f, u, hu, hf⟩ hq h`. Establish `h3 : u = 1` using `hsep K A hA L hL hamp q hq u fun k => by`.

Take `⟨⟨g, v, hv, hg⟩, e⟩` from `h k`. Use `⟨v, hv, ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg (fun g : homRing A => g.1 (Additive.ofMul (𝟙 A))) e`. Simplify using `only [← Nat.cast_pow, natCast_mul_apply, hf, hg, Category.id_comp] at h1`. Conclude with `h1`.

Conclude with `homRing_ext (by rw [hf, h3, Category.id_comp]; rfl)`. Use `homRing_ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = Additive.ofMul (𝟙 A) + ((N : homRing A) * toRing φ).1 _`. Rewrite using `[natCast_mul_apply, toRing_apply, toRing_apply, Category.id_comp, Category.id_comp, ← ofMul_pow, ← e, ← ofMul_mul, mul_comm, inv_mul_cancel_right]`. Rewrite using `[toRing_pow]`.

Conclude with `homRing_ext (by rw [toRing_apply, hord, Category.id_comp]; rfl)`. Establish `h1` using `congrArg (fun g : homRing A => g.1 (Additive.ofMul (𝟙 A))) key`. Simplify using `only [toRing_apply, Category.id_comp] at h1`. Conclude with `h1`.
-/
theorem serreAmple_of_finiteOrder_of_separated :
    FiniteOrderSt → SeparatedSt → SerreAmpleSt := by
  intro hfin hsep K _ _ A _ _ hA L hL hamp N hN3 hNK σ hσ hpull hfix
  haveI := hσ
  obtain ⟨m, hm0, hord⟩ := hfin K A hA L hL hamp σ hσ hpull
  have hFS : ∀ n : ℕ, 1 ≤ n → Flat (Out.mulA A n).left ∧ Surjective (Out.mulA A n).left :=
    fun n hn => flat_and_surjective_of_isFinite_abelianEnd
      forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K A hA _
      (GlobalTheory.AbLaw.MulN.isMonHom_mulA A n) (GlobalTheory.MulFiniteAny.isFinite_mulA K A hA n hn)
  have hu : IsMonHom (σ.hom * (𝟙 A)⁻¹) := by
    rw [Hom.mul_def, Hom.inv_def]; infer_instance
  obtain ⟨-, hdiv⟩ := GlobalTheory.TorsionDivisible.finite_torsion_and_divisible K A hA N hNK
  obtain ⟨φ, hφ, e⟩ := hdiv (σ.hom * (𝟙 A)⁻¹) hu (fun x hx => by
    rw [MonObj.comp_mul, GrpObj.comp_inv, hfix K (𝟙 _) x hx, Category.comp_id, mul_inv_cancel])
  haveI := hφ
  have key : toRing σ.hom = 1 := by
    refine GlobalTheory.eq_one_of_pow_eq_one_of_congr_one (homRing A) N hN3 ?_ ?_ (toRing σ.hom) (toRing φ) m
      hm0 ?_ ?_
    · rintro k ⟨f, u, hu, hf⟩ hk h
      have h1 := congrArg (fun g : homRing A => g.1 (Additive.ofMul (𝟙 A))) h
      simp only [natCast_mul_apply, hf, Category.id_comp] at h1
      have h2 : u ^ k = 1 := h1
      have h3 : u = 1 := by
        obtain ⟨_, _⟩ := hFS k (by omega)
        haveI : Epi (Out.mulA A k).left := Flat.epi_of_flat_of_surjective _
        refine Over.OverMorphism.ext ((cancel_epi (Out.mulA A k).left).1 ?_)
        rw [← Over.comp_left, ← Over.comp_left, MonObj.comp_one, Out.mulA, MonObj.pow_comp,
          Category.id_comp, h2]
      exact homRing_ext (by rw [hf, h3, Category.id_comp]; rfl)
    · rintro q ⟨f, u, hu, hf⟩ hq h
      have h3 : u = 1 := hsep K A hA L hL hamp q hq u fun k => by
        obtain ⟨⟨g, v, hv, hg⟩, e⟩ := h k
        refine ⟨v, hv, ?_⟩
        have h1 := congrArg (fun g : homRing A => g.1 (Additive.ofMul (𝟙 A))) e
        simp only [← Nat.cast_pow, natCast_mul_apply, hf, hg, Category.id_comp] at h1
        exact h1
      exact homRing_ext (by rw [hf, h3, Category.id_comp]; rfl)
    · refine homRing_ext ?_
      change _ = Additive.ofMul (𝟙 A) + ((N : homRing A) * toRing φ).1 _
      rw [natCast_mul_apply, toRing_apply, toRing_apply, Category.id_comp, Category.id_comp,
        ← ofMul_pow, ← e, ← ofMul_mul, mul_comm, inv_mul_cancel_right]
    · rw [toRing_pow]
      exact homRing_ext (by rw [toRing_apply, hord, Category.id_comp]; rfl)
  have h1 := congrArg (fun g : homRing A => g.1 (Additive.ofMul (𝟙 A))) key
  simp only [toRing_apply, Category.id_comp] at h1
  exact h1

end GlobalTheory.AmpleRigid
