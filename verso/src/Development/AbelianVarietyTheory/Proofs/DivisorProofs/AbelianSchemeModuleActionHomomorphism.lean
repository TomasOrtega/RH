import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeIdPowFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionWithRangeInOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDivLocal

/- English proof (translation)
Establish `hn' : IsUnit (n : Γ(Sp V, ⊤))`. Simplify using `using hn.map (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom`. Take `⟨-, hfin, het, hsurj⟩` from `GlobalTheory.abelianScheme_id_pow_finite_etale_surjective (Sp V) B n hB hn'`. Use `set m : B ⟶ B := (𝟙 B) ^ n with hm`. Set `U : Over (Sp V)` to `Over.mk (pullback.snd m.left P.left)`.

Establish `hU : Smooth U.hom` using `by dsimp [U]; infer_instance`. Set `r : Sp (ResidueField V) ⟶ Sp V` to `spMap (residue V)`. Set `P₀ : Sp (ResidueField V) ⟶ B.left` to `r ≫ P.left`. Establish `: CompactSpace ↥(pullback m.left P₀)` using `QuasiCompact.compactSpace_of_compactSpace (pullback.snd m.left P₀)`. Take `⟨p, -⟩` from `(pullback.snd m.left P₀).surjective (default : PrimeSpectrum (ResidueField V))`.

Take `⟨z, -, hz⟩` from `isClosed_univ.exists_closed_singleton (X := ↥(pullback m.left P₀)) ⟨p, trivial⟩`. Establish `hw` using `pointOfClosedPoint_comp (pullback.snd m.left P₀) z hz`. Set `x₀ : Sp (ResidueField V) ⟶ U.left` to `pullback.lift (pointOfClosedPoint (pullback.snd m.left P₀) z hz ≫ pullback.fst _ _) r (by`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, hw, Category.id_comp])`. Establish `hx₀ : x₀ ≫ U.hom = spMap ((residue V).comp (RingHom.id V))`.

Rewrite using `[RingHom.comp_id]`. Conclude with `pullback.lift_snd _ _ _`. Take `⟨a, ha, -⟩` from `GlobalTheory.HenselLift.exists_lift_mem_open V V hc (RingHom.id V) U hU x₀ hx₀ ⊤ (by simp)`. Establish `ha' : a ≫ pullback.snd m.left P.left = 𝟙 _`. Use `ha.trans ?_` and prove the remaining obligations.

Rewrite using `[spMap, show CommRingCat.ofHom (RingHom.id V) = 𝟙 (CommRingCat.of V) from rfl, Spec.map_id]`. Establish `key : (a ≫ pullback.fst m.left P.left) ≫ m.left = P.left`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, ha', Category.id_comp]`. Use `⟨Over.homMk (a ≫ pullback.fst m.left P.left) ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Over.w m, ← Category.assoc, key]`.

Conclude with `Over.w P`. Establish `e : ∀ Q : 𝟙_ (Over (Sp V)) ⟶ B, Q ^ n = Q ≫ m` using `fun Q => by`. Rewrite using `[hm, comp_pow, Category.comp_id]`. Rewrite using `[e]`. Conclude with `Over.OverMorphism.ext key`.
-/
theorem exists_pow_eq {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    (hc : IsAdicComplete (maximalIdeal V) V) (hk : IsAlgClosed (ResidueField V))
    (B : Over (Sp V)) [GrpObj B] (hB : IsAbelianScheme B) (n : ℕ) (hn : IsUnit (n : V))
    (P : 𝟙_ (Over (Sp V)) ⟶ B) : ∃ Q : 𝟙_ (Over (Sp V)) ⟶ B, Q ^ n = P := by
  have hn' : IsUnit (n : Γ(Sp V, ⊤)) := by
    simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
  obtain ⟨-, hfin, het, hsurj⟩ :=
    GlobalTheory.abelianScheme_id_pow_finite_etale_surjective (Sp V) B n hB hn'
  set m : B ⟶ B := (𝟙 B) ^ n with hm
  let U : Over (Sp V) := Over.mk (pullback.snd m.left P.left)
  have hU : Smooth U.hom := by dsimp [U]; infer_instance
  let r : Sp (ResidueField V) ⟶ Sp V := spMap (residue V)
  let P₀ : Sp (ResidueField V) ⟶ B.left := r ≫ P.left
  have : CompactSpace ↥(pullback m.left P₀) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd m.left P₀)
  obtain ⟨p, -⟩ := (pullback.snd m.left P₀).surjective (default : PrimeSpectrum (ResidueField V))
  obtain ⟨z, -, hz⟩ :=
    isClosed_univ.exists_closed_singleton (X := ↥(pullback m.left P₀)) ⟨p, trivial⟩
  have hw := pointOfClosedPoint_comp (pullback.snd m.left P₀) z hz
  let x₀ : Sp (ResidueField V) ⟶ U.left :=
    pullback.lift (pointOfClosedPoint (pullback.snd m.left P₀) z hz ≫ pullback.fst _ _) r (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hw, Category.id_comp])
  have hx₀ : x₀ ≫ U.hom = spMap ((residue V).comp (RingHom.id V)) := by
    rw [RingHom.comp_id]
    exact pullback.lift_snd _ _ _
  obtain ⟨a, ha, -⟩ :=
    GlobalTheory.HenselLift.exists_lift_mem_open V V hc (RingHom.id V) U hU x₀ hx₀ ⊤ (by simp)
  have ha' : a ≫ pullback.snd m.left P.left = 𝟙 _ := by
    refine ha.trans ?_
    rw [spMap, show CommRingCat.ofHom (RingHom.id V) = 𝟙 (CommRingCat.of V) from rfl, Spec.map_id]
  have key : (a ≫ pullback.fst m.left P.left) ≫ m.left = P.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ha', Category.id_comp]
  refine ⟨Over.homMk (a ≫ pullback.fst m.left P.left) ?_, ?_⟩
  · rw [← Over.w m, ← Category.assoc, key]
    exact Over.w P
  · have e : ∀ Q : 𝟙_ (Over (Sp V)) ⟶ B, Q ^ n = Q ≫ m := fun Q => by
      rw [hm, comp_pow, Category.comp_id]
    rw [e]
    exact Over.OverMorphism.ext key

end GlobalTheory.AbDivLocal

namespace GlobalTheory.AbDivLocal

abbrev ptsModule {S : Scheme.{0}} (T : Over S) (B : Over S) [GrpObj B] [IsCommMonObj B] (O : Type)
    [CommRing O] (a : OAct O B) : Module O (Additive (T ⟶ B)) where
  smul o p := Additive.ofMul (p.toMul ≫ a.act o)
  one_smul p := by
    change Additive.ofMul (p.toMul ≫ a.act 1) = p
    rw [a.one, Category.comp_id]; rfl
  mul_smul o o' p := by
    change Additive.ofMul (p.toMul ≫ a.act (o * o')) =
      Additive.ofMul ((p.toMul ≫ a.act o') ≫ a.act o)
    rw [mul_comm, a.mul, Category.assoc]
  smul_zero o := by
    change Additive.ofMul ((1 : T ⟶ B) ≫ a.act o) = Additive.ofMul 1
    haveI := a.hom o
    rw [one_comp]
  smul_add o p q := by
    change Additive.ofMul ((p.toMul * q.toMul) ≫ a.act o) =
      Additive.ofMul ((p.toMul ≫ a.act o) * (q.toMul ≫ a.act o))
    haveI := a.hom o
    rw [mul_comp]
  add_smul o o' p := by
    change Additive.ofMul (p.toMul ≫ a.act (o + o')) =
      Additive.ofMul ((p.toMul ≫ a.act o) * (p.toMul ≫ a.act o'))
    rw [a.add, comp_mul]
  zero_smul p := by
    change Additive.ofMul (p.toMul ≫ a.act 0) = Additive.ofMul 1
    have h0 : a.act 0 = 1 := by
      have h := a.add 0 0
      rw [add_zero] at h
      exact (mul_eq_left.mp h.symm)
    rw [h0, comp_one]

/- English proof (translation)
Introduce `V _ _ _ _ hc hk B _ hB O _ _ _ a X _ _ _ _ x hadd hsmul n hn`. Use `haveI := hB.comm`. Use `letI := ptsModule (𝟙_ (Over (Sp V))) B O a`. Set `g : X →ₗ[O] Additive (𝟙_ (Over (Sp V)) ⟶ B)` to `{ toFun := fun y => Additive.ofMul (x y) map_add' := fun y z => by rw [hadd]; rfl map_smul' := fun o y => by rw [hsmul]; rfl }`. Set `f : Additive (𝟙_ (Over (Sp V)) ⟶ B) →ₗ[O] Additive (𝟙_ (Over (Sp V)) ⟶ B)` to `n • LinearMap.id`.

Establish `hf : Function.Surjective f`. Introduce `p`. Take `⟨Q, hQ⟩` from `exists_pow_eq hc hk B hB n hn p.toMul`. Use `⟨Additive.ofMul Q, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `n • Additive.ofMul Q = p`.

Rewrite using `[← ofMul_pow, hQ]`. Both sides reduce to the same expression. Take `⟨h, hh⟩` from `Module.projective_lifting_property f g hf`. Use `⟨fun y => (h y).toMul, fun y z => by` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(h (y + z)).toMul = (h y).toMul * (h z).toMul`.

Rewrite using `[map_add]`. Use the proof step `rfl,`. Use `fun o y => by`. Express the relevant statement in the definitionally equal form `(h (o • y)).toMul = (h y).toMul ≫ a.act o`. Rewrite using `[map_smul]`.

Use the proof step `rfl, fun y => ?_⟩`. Establish `e : n • h y = Additive.ofMul (x y)` using `LinearMap.congr_fun hh y`. Express the relevant statement in the definitionally equal form `(h (n • y)).toMul = x y`. Rewrite using `[map_nsmul, e]`. Both sides reduce to the same expression.
-/
theorem exists_divided_linear : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V], IsAdicComplete (maximalIdeal V) V → IsAlgClosed (ResidueField V) → ∀ (B : Over (Sp V)) [GrpObj B], IsAbelianScheme B → ∀ (O : Type) [CommRing O] [IsDomain O] [Module.Finite ℤ O] (a : OAct O B) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (x : X → (𝟙_ (Over (Sp V)) ⟶ B)), (∀ y z, x (y + z) = x y * x z) → (∀ (o : O) y, x (o • y) = x y ≫ a.act o) → ∀ n : ℕ, IsUnit (n : V) → ∃ x' : X → (𝟙_ (Over (Sp V)) ⟶ B), (∀ y z, x' (y + z) = x' y * x' z) ∧ (∀ (o : O) y, x' (o • y) = x' y ≫ a.act o) ∧ ∀ y, x' (n • y) = x y := by
  intro V _ _ _ _ hc hk B _ hB O _ _ _ a X _ _ _ _ x hadd hsmul n hn
  haveI := hB.comm
  letI := ptsModule (𝟙_ (Over (Sp V))) B O a
  let g : X →ₗ[O] Additive (𝟙_ (Over (Sp V)) ⟶ B) :=
    { toFun := fun y => Additive.ofMul (x y)
      map_add' := fun y z => by rw [hadd]; rfl
      map_smul' := fun o y => by rw [hsmul]; rfl }
  let f : Additive (𝟙_ (Over (Sp V)) ⟶ B) →ₗ[O] Additive (𝟙_ (Over (Sp V)) ⟶ B) :=
    n • LinearMap.id
  have hf : Function.Surjective f := by
    intro p
    obtain ⟨Q, hQ⟩ := exists_pow_eq hc hk B hB n hn p.toMul
    refine ⟨Additive.ofMul Q, ?_⟩
    change n • Additive.ofMul Q = p
    rw [← ofMul_pow, hQ]; rfl
  obtain ⟨h, hh⟩ := Module.projective_lifting_property f g hf
  refine ⟨fun y => (h y).toMul, fun y z => by
      change (h (y + z)).toMul = (h y).toMul * (h z).toMul
      rw [map_add]; rfl,
    fun o y => by
      change (h (o • y)).toMul = (h y).toMul ≫ a.act o
      rw [map_smul]; rfl, fun y => ?_⟩
  have e : n • h y = Additive.ofMul (x y) := LinearMap.congr_fun hh y
  change (h (n • y)).toMul = x y
  rw [map_nsmul, e]; rfl

end GlobalTheory.AbDivLocal
