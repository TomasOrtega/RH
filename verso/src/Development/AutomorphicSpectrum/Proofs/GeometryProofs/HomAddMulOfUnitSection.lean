import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerRingInjective

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieEx.ModSrc

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.LieEx GlobalTheory.CompanionTheory.Ar.BT.Tan

variable {S : Scheme.{0}} {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S)
  {P V : Type} [AddCommGroup P] [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P]
  [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]

/- English proof (translation)
Use `ext1`. Use `joint_epi (TrivSqZeroExt.map (LinearMap.fst R P P)).toRingHom (TrivSqZeroExt.map (LinearMap.snd R P P)).toRingHom ?_ ?_ f.left g.left (congrArg CommaMorphism.left h₁) (congrArg CommaMorphism.left h₂)` and prove the remaining obligations. Introduce `a b hab`. Establish `e₁ : TrivSqZeroExt.map (LinearMap.fst R P P) a = TrivSqZeroExt.map (LinearMap.fst R P P) b` using `congrArg Prod.fst hab`. Establish `e₂ : TrivSqZeroExt.map (LinearMap.snd R P P) a = TrivSqZeroExt.map (LinearMap.snd R P P) b` using `congrArg Prod.snd hab`.

Use `ext`. Simplify using `using congrArg TrivSqZeroExt.fst e₁`. Simplify using `using congrArg TrivSqZeroExt.snd e₁`. Simplify using `using congrArg TrivSqZeroExt.snd e₂`. Introduce `p`.

Set `q : PrimeSpectrum (TrivSqZeroExt R P)` to `PrimeSpectrum.comap (TrivSqZeroExt.map (LinearMap.inl R P P)).toRingHom p`. Use `⟨q, PrimeSpectrum.ext (Ideal.ext fun a => ?_)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `TrivSqZeroExt.map (LinearMap.inl R P P) (TrivSqZeroExt.map (LinearMap.fst R P P) a) ∈ p.asIdeal ↔ a ∈ p.asIdeal`. Use `set b := TrivSqZeroExt.map (LinearMap.inl R P P) (TrivSqZeroExt.map (LinearMap.fst R P P) a) with hb`. Establish `h0 : (b - a).fst = 0` using `by simp [hb]`.

Establish `hm : b - a ∈ p.asIdeal`. Use `p.isPrime.mem_of_pow_mem 2 ?_` and prove the remaining obligations. Establish `: (b - a) ^ 2 = 0`. Rewrite using `[pow_two]`. Apply the tactic sequence `ext1 <;> simp [h0]`.

Rewrite using `[this]`. Conclude with `zero_mem _`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Simplify using `using p.asIdeal.sub_mem h hm`.

Introduce `h`. Simplify using `using p.asIdeal.add_mem hm h`.
-/
theorem ext_pair_mod {Z : Over S} (f g : ob x (P × P) ⟶ Z)
    (h₁ : hom x (LinearMap.fst R P P) ≫ f = hom x (LinearMap.fst R P P) ≫ g)
    (h₂ : hom x (LinearMap.snd R P P) ≫ f = hom x (LinearMap.snd R P P) ≫ g) : f = g := by
  ext1
  refine joint_epi (TrivSqZeroExt.map (LinearMap.fst R P P)).toRingHom
    (TrivSqZeroExt.map (LinearMap.snd R P P)).toRingHom ?_ ?_ f.left g.left
    (congrArg CommaMorphism.left h₁) (congrArg CommaMorphism.left h₂)
  · intro a b hab
    have e₁ : TrivSqZeroExt.map (LinearMap.fst R P P) a = TrivSqZeroExt.map (LinearMap.fst R P P) b :=
      congrArg Prod.fst hab
    have e₂ : TrivSqZeroExt.map (LinearMap.snd R P P) a = TrivSqZeroExt.map (LinearMap.snd R P P) b :=
      congrArg Prod.snd hab
    ext
    · simpa using congrArg TrivSqZeroExt.fst e₁
    · simpa using congrArg TrivSqZeroExt.snd e₁
    · simpa using congrArg TrivSqZeroExt.snd e₂
  · intro p
    let q : PrimeSpectrum (TrivSqZeroExt R P) :=
      PrimeSpectrum.comap (TrivSqZeroExt.map (LinearMap.inl R P P)).toRingHom p
    refine ⟨q, PrimeSpectrum.ext (Ideal.ext fun a => ?_)⟩
    change TrivSqZeroExt.map (LinearMap.inl R P P) (TrivSqZeroExt.map (LinearMap.fst R P P) a) ∈ p.asIdeal ↔
      a ∈ p.asIdeal
    set b := TrivSqZeroExt.map (LinearMap.inl R P P) (TrivSqZeroExt.map (LinearMap.fst R P P) a) with hb
    have h0 : (b - a).fst = 0 := by simp [hb]
    have hm : b - a ∈ p.asIdeal := by
      refine p.isPrime.mem_of_pow_mem 2 ?_
      have : (b - a) ^ 2 = 0 := by
        rw [pow_two]
        ext1 <;> simp [h0]
      rw [this]; exact zero_mem _
    constructor
    · intro h; simpa using p.asIdeal.sub_mem h hm
    · intro h; simpa using p.asIdeal.add_mem hm h

/- English proof (translation)
Establish `h0 : hom x (0 : P →ₗ[R] P) ≫ u = 1`. Rewrite using `[hom_zero, Category.assoc, hu, MonObj.comp_one]`. Establish `key : hom x (LinearMap.inl R P P + LinearMap.inr R P P) ≫ u = (hom x (LinearMap.inl R P P) ≫ u) * (hom x (LinearMap.inr R P P) ≫ u)`. Apply `ext_pair_mod` to reduce the goal to its premises. Simplify using `only [MonObj.comp_mul, ← Category.assoc, hom_comp, LinearMap.comp_add, LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, add_zero, h0, _root_.mul_one]`.

Simplify using `only [MonObj.comp_mul, ← Category.assoc, hom_comp, LinearMap.comp_add, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, zero_add, h0, _root_.one_mul]`. Use `congrArg (fun k => hom x (f.coprod g) ≫ k) key` as an intermediate fact. Simplify `this` using `only [MonObj.comp_mul, ← Category.assoc, hom_comp, LinearMap.comp_add, LinearMap.coprod_inl, LinearMap.coprod_inr]`.
-/
theorem hom_add_mod (G : Over S) [GrpObj G] (u : ob x P ⟶ G) (hu : zsec x ≫ u = 1) (f g : P →ₗ[R] V) :
    hom x (f + g) ≫ u = (hom x f ≫ u) * (hom x g ≫ u) := by
  have h0 : hom x (0 : P →ₗ[R] P) ≫ u = 1 := by
    rw [hom_zero, Category.assoc, hu, MonObj.comp_one]
  have key : hom x (LinearMap.inl R P P + LinearMap.inr R P P) ≫ u =
      (hom x (LinearMap.inl R P P) ≫ u) * (hom x (LinearMap.inr R P P) ≫ u) := by
    apply ext_pair_mod
    · simp only [MonObj.comp_mul, ← Category.assoc, hom_comp, LinearMap.comp_add, LinearMap.fst_comp_inl,
        LinearMap.fst_comp_inr, add_zero, h0, _root_.mul_one]
    · simp only [MonObj.comp_mul, ← Category.assoc, hom_comp, LinearMap.comp_add, LinearMap.snd_comp_inl,
        LinearMap.snd_comp_inr, zero_add, h0, _root_.one_mul]
  have := congrArg (fun k => hom x (f.coprod g) ≫ k) key
  simpa only [MonObj.comp_mul, ← Category.assoc, hom_comp, LinearMap.comp_add, LinearMap.coprod_inl,
    LinearMap.coprod_inr] using this

/- English proof (translation)
Introduce `_ _ _ x G _ _ _ _ _ _ _ _ _ _ _ u hu f g` and use `hom_add_mod x G u hu f g`.
-/
theorem hom_add_mod_closed : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (G : Over S) [GrpObj G] (P V : Type) [AddCommGroup P] [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P] [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V] (u : ob x P ⟶ G), zsec x ≫ u = 1 → ∀ f g : P →ₗ[R] V, hom x (f + g) ≫ u = (hom x f ≫ u) * (hom x g ≫ u) :=
  fun _ _ _ x G _ _ _ _ _ _ _ _ _ _ _ u hu f g => hom_add_mod x G u hu f g

end GlobalTheory.CompanionTheory.Ar.LieEx.ModSrc
