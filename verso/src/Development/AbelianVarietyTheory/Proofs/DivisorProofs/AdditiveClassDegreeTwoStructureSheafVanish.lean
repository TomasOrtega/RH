import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxesO1OfProjectiveRankCupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafPullbackRelationsBasicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorPowerTwoDiagonalAdditiveEqZeroProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSquareAffineH1VanishStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs.PrimitivePullback

variable {R : Type} [CommRing R]

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem pullHO1_congr {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ ψ : X' ⟶ X} (e : φ = ψ)
    (h : φ ≫ s = s' ≫ spMap (RingHom.id R)) (h' : ψ ≫ s = s' ≫ spMap (RingHom.id R)) (c : HO1 s) :
    pullHO1 h c = pullHO1 h' c := by
  subst e; rfl

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem isPullO_congr {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ ψ : X' ⟶ X} (e : φ = ψ)
    (h : φ ≫ s = s' ≫ spMap (RingHom.id R)) (h' : ψ ≫ s = s' ≫ spMap (RingHom.id R)) {c : HO1 s} {c' : HO1 s'} :
    IsPullO h c c' ↔ IsPullO h' c c' := by
  subst e; rfl

/- English proof (translation)
The claim follows from `(IsPullO.eq_pullHO1 h (CoefMap.pullCohomologyOne_eq_of_natTrans (pairPull h) (pairRes _ s) (pairIdTrans X) (fun _ _ ↦ rfl) c)).symm`.
-/
theorem pullHO1_self {X : Scheme.{0}} {s : X ⟶ Sp R} (h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R)) (c : HO1 s) :
    pullHO1 h c = c :=
  (IsPullO.eq_pullHO1 h
    (CoefMap.pullCohomologyOne_eq_of_natTrans (pairPull h) (pairRes _ s) (pairIdTrans X) (fun _ _ ↦ rfl) c)).symm

/- English proof (translation)
Establish `h'' : (g.left ≫ f.left) ≫ C.hom = A.hom ≫ spMap (RingHom.id R)`. Rewrite using `[← Over.comp_left]`. Conclude with `overW (g ≫ f)`. Establish `k` using `(GlobalTheory.T.structureSheaf_pullback_relations_basic R C.left B.left C.hom B.hom f.left (overW f)).2.2 A.left A.hom g.left (overW g) h'' a _ _ (isPullO_pullHO1 _ a) (isPullO_pullHO1 _ _)`. Conclude with `IsPullO.eq_pullHO1 _ ((isPullO_congr (show g.left ≫ f.left = (g ≫ f).left from rfl) _ _).1 k)`.
-/
theorem pullHO1_comp {A B C : Over (Sp R)} (f : B ⟶ C) (g : A ⟶ B) (a : HO1 C.hom) :
    pullHO1 (overW g) (pullHO1 (overW f) a) = pullHO1 (overW (g ≫ f)) a := by
  have h'' : (g.left ≫ f.left) ≫ C.hom = A.hom ≫ spMap (RingHom.id R) := by
    rw [← Over.comp_left]; exact overW (g ≫ f)
  have k := (GlobalTheory.T.structureSheaf_pullback_relations_basic R C.left B.left C.hom B.hom f.left (overW f)).2.2 A.left A.hom g.left (overW g) h'' a _ _
    (isPullO_pullHO1 _ a) (isPullO_pullHO1 _ _)
  exact IsPullO.eq_pullHO1 _ ((isPullO_congr (show g.left ≫ f.left = (g ≫ f).left from rfl) _ _).1 k)

/- English proof (translation)
Rewrite using `[pullHO1_comp]`. Establish `h' : 𝟙 A.left ≫ A.hom = A.hom ≫ spMap (RingHom.id R)`. Rewrite using `[← Over.id_left]`. Conclude with `overW (𝟙 A)`. Rewrite using `[pullHO1_congr (show (g ≫ f).left = 𝟙 A.left by rw [e]; rfl) _ h', pullHO1_self]`.
-/
theorem pullHO1_pull_self {A B : Over (Sp R)} (f : B ⟶ A) (g : A ⟶ B) (e : g ≫ f = 𝟙 A) (a : HO1 A.hom) :
    pullHO1 (overW g) (pullHO1 (overW f) a) = a := by
  rw [pullHO1_comp]
  have h' : 𝟙 A.left ≫ A.hom = A.hom ≫ spMap (RingHom.id R) := by
    rw [← Over.id_left]; exact overW (𝟙 A)
  rw [pullHO1_congr (show (g ≫ f).left = 𝟙 A.left by rw [e]; rfl) _ h', pullHO1_self]

/- English proof (translation)
Rewrite using `[pullHO1_comp]`. Establish `h' : (toUnit A ≫ η[A]).left ≫ A.hom = A.hom ≫ spMap (RingHom.id R)` using `overW _`. Rewrite using `[pullHO1_congr (show (g ≫ f).left = (toUnit A ≫ η[A]).left by rw [e, Hom.one_def]) _ h', ← pullHO1_comp]`. Establish `: pullHO1 (overW η[A]) a = 0` using `by haveI : IsAffine (𝟙_ (Over (Sp R))).left := by change IsAffine (Sp R); infer_instance`. Conclude with `(GlobalTheory.T.abelian_square_affine_h1_vanish R).2 _ _ _`.

Rewrite using `[this, map_zero]`.
-/
theorem pullHO1_pull_one {A B : Over (Sp R)} [GrpObj A] (f : B ⟶ A) (g : A ⟶ B) (e : g ≫ f = 1) (a : HO1 A.hom) :
    pullHO1 (overW g) (pullHO1 (overW f) a) = 0 := by
  rw [pullHO1_comp]
  have h' : (toUnit A ≫ η[A]).left ≫ A.hom = A.hom ≫ spMap (RingHom.id R) := overW _
  rw [pullHO1_congr (show (g ≫ f).left = (toUnit A ≫ η[A]).left by rw [e, Hom.one_def]) _ h', ← pullHO1_comp]
  have : pullHO1 (overW η[A]) a = 0 := by
    haveI : IsAffine (𝟙_ (Over (Sp R))).left := by change IsAffine (Sp R); infer_instance
    exact (GlobalTheory.T.abelian_square_affine_h1_vanish R).2 _ _ _
  rw [this, map_zero]

variable (A : Over (Sp R)) [GrpObj A]

def sumPull : HO1 A.hom × HO1 A.hom →ₗ[R] HO1 (A ⊗ A).hom :=
  (pullHO1 (overW (fst A A))).coprod (pullHO1 (overW (snd A A)))

def axesPull : HO1 (A ⊗ A).hom →ₗ[R] HO1 A.hom × HO1 A.hom :=
  (pullHO1 (overW (lift (𝟙 A) (1 : A ⟶ A)))).prod (pullHO1 (overW (lift (1 : A ⟶ A) (𝟙 A))))

/- English proof (translation)
Take `⟨a, b⟩` from `x`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `pullHO1 (overW (lift (𝟙 A) (1 : A ⟶ A))) (pullHO1 (overW (fst A A)) a + pullHO1 (overW (snd A A)) b) = a`. Rewrite using `[map_add, pullHO1_pull_self _ _ (lift_fst _ _), pullHO1_pull_one _ _ (lift_snd _ _), add_zero]`. Express the relevant statement in the definitionally equal form `pullHO1 (overW (lift (1 : A ⟶ A) (𝟙 A))) (pullHO1 (overW (fst A A)) a + pullHO1 (overW (snd A A)) b) = b`.

Rewrite using `[map_add, pullHO1_pull_one _ _ (lift_fst _ _), pullHO1_pull_self _ _ (lift_snd _ _), zero_add]`.
-/
theorem axesPull_sumPull (x : HO1 A.hom × HO1 A.hom) : axesPull A (sumPull A x) = x := by
  obtain ⟨a, b⟩ := x
  refine Prod.ext ?_ ?_
  · change pullHO1 (overW (lift (𝟙 A) (1 : A ⟶ A))) (pullHO1 (overW (fst A A)) a + pullHO1 (overW (snd A A)) b) = a
    rw [map_add, pullHO1_pull_self _ _ (lift_fst _ _), pullHO1_pull_one _ _ (lift_snd _ _), add_zero]
  · change pullHO1 (overW (lift (1 : A ⟶ A) (𝟙 A))) (pullHO1 (overW (fst A A)) a + pullHO1 (overW (snd A A)) b) = b
    rw [map_add, pullHO1_pull_one _ _ (lift_fst _ _), pullHO1_pull_self _ _ (lift_snd _ _), zero_add]

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `x hx`. Establish `h1 : pullHO1 (overW (lift (𝟙 A) (1 : A ⟶ A))) x = 0` using `congrArg Prod.fst hx`. Establish `h2 : pullHO1 (overW (lift (1 : A ⟶ A) (𝟙 A))) x = 0` using `congrArg Prod.snd hx`. Use `hax R A g hA hg x ?_ ?_` and prove the remaining obligations.

Use `isPullO_pullHO1 (overW (lift (𝟙 A) (1 : A ⟶ A))) x` as an intermediate fact. Rewrite `this` using `[h1]`. Then use the resulting hypothesis. Use `isPullO_pullHO1 (overW (lift (1 : A ⟶ A) (𝟙 A))) x` as an intermediate fact. Rewrite `this` using `[h2]`. Then use the resulting hypothesis.
-/
theorem axesPull_injective (hax : AxesVanishingStructureSheafDegOne) (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    Function.Injective (axesPull A) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h1 : pullHO1 (overW (lift (𝟙 A) (1 : A ⟶ A))) x = 0 := congrArg Prod.fst hx
  have h2 : pullHO1 (overW (lift (1 : A ⟶ A) (𝟙 A))) x = 0 := congrArg Prod.snd hx
  refine hax R A g hA hg x ?_ ?_
  · have := isPullO_pullHO1 (overW (lift (𝟙 A) (1 : A ⟶ A))) x; rwa [h1] at this
  · have := isPullO_pullHO1 (overW (lift (1 : A ⟶ A) (𝟙 A))) x; rwa [h2] at this

/- English proof (translation)
Apply `axesPull_injective A hax g hA hg` to reduce the goal to its premises. Rewrite using `[axesPull_sumPull]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `pullHO1 (overW (lift (𝟙 A) (1 : A ⟶ A))) (pullHO1 (overW μ[A]) a) = a`. Conclude with `pullHO1_pull_self _ _ (by rw [Hom.one_def, lift_comp_one_right]) a`.

Express the relevant statement in the definitionally equal form `pullHO1 (overW (lift (1 : A ⟶ A) (𝟙 A))) (pullHO1 (overW μ[A]) a) = a`. Conclude with `pullHO1_pull_self _ _ (by rw [Hom.one_def, lift_comp_one_left]) a`.
-/
theorem pullHO1_mul (hax : AxesVanishingStructureSheafDegOne) (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (a : HO1 A.hom) : pullHO1 (overW μ[A]) a = sumPull A (a, a) := by
  apply axesPull_injective A hax g hA hg
  rw [axesPull_sumPull]
  refine Prod.ext ?_ ?_
  · change pullHO1 (overW (lift (𝟙 A) (1 : A ⟶ A))) (pullHO1 (overW μ[A]) a) = a
    exact pullHO1_pull_self _ _ (by rw [Hom.one_def, lift_comp_one_right]) a
  · change pullHO1 (overW (lift (1 : A ⟶ A) (𝟙 A))) (pullHO1 (overW μ[A]) a) = a
    exact pullHO1_pull_self _ _ (by rw [Hom.one_def, lift_comp_one_left]) a

/- English proof (translation)
Assemble the required witnesses or components as `⟨Function.LeftInverse.injective (axesPull_sumPull A), fun c ↦ ⟨axesPull A c, axesPull_injective A hax g hA hg (axesPull_sumPull A _)⟩⟩`.
-/
theorem sumPull_bijective (hax : AxesVanishingStructureSheafDegOne) (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    Function.Bijective (sumPull A) :=
  ⟨Function.LeftInverse.injective (axesPull_sumPull A), fun c ↦
    ⟨axesPull A c, axesPull_injective A hax g hA hg (axesPull_sumPull A _)⟩⟩

end GlobalTheory.Obs.PrimitivePullback

namespace GlobalTheory.Obs.PrimitivePullback

variable {R : Type} [CommRing R] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ : X' ⟶ X}
  {h : φ ≫ s = s' ≫ spMap (RingHom.id R)}

/- English proof (translation)
Unfold `IsPullbackH2Structure`. Rewrite using `[map_zero, map_zero]`.
-/
theorem isPullO2_zero : IsPullbackH2Structure h (0 : CatCoh.H2 (OAff s)) (0 : CatCoh.H2 (OAff s')) := by
  unfold IsPullbackH2Structure; rw [map_zero, map_zero]

/- English proof (translation)
Unfold `IsPullbackH2Structure at *`. Rewrite using `[map_add, map_add, ha, hb]`.
-/
theorem isPullO2_add {a b : CatCoh.H2 (OAff s)} {a' b' : CatCoh.H2 (OAff s')} (ha : IsPullbackH2Structure h a a')
    (hb : IsPullbackH2Structure h b b') : IsPullbackH2Structure h (a + b) (a' + b') := by
  unfold IsPullbackH2Structure at *; rw [map_add, map_add, ha, hb]

/- English proof (translation)
Unfold `IsPullbackH2Structure at *`. Rewrite using `[map_smulₛₗ, map_smulₛₗ, ha]`.
-/
theorem isPullO2_smul {a : CatCoh.H2 (OAff s)} {a' : CatCoh.H2 (OAff s')} (ha : IsPullbackH2Structure h a a') (r : R) :
    IsPullbackH2Structure h (r • a) (r • a') := by
  unfold IsPullbackH2Structure at *; rw [map_smulₛₗ, map_smulₛₗ, ha]

/- English proof (translation)
The claim follows from `(GlobalTheory.T.structureSheaf_pullback_relations_basic R X X' s s' φ h).1.1 (hx.symm.trans hy)`.
-/
theorem isPullO2_unique {c : CatCoh.H2 (OAff s)} {x y : CatCoh.H2 (OAff s')} (hx : IsPullbackH2Structure h c x)
    (hy : IsPullbackH2Structure h c y) : x = y :=
  (GlobalTheory.T.structureSheaf_pullback_relations_basic R X X' s s' φ h).1.1 (hx.symm.trans hy)

/- English proof (translation)
Establish `key : ∀ a b : HO1 s, IsPullbackH2Structure h (e (exteriorPower.ιMulti R 2 ![a, b])) (e' (exteriorPower.map 2 (pullHO1 h) (exteriorPower.ιMulti R 2 ![a, b])))`. Introduce `a b`. Establish `hc : (pullHO1 h) ∘ ![a, b] = ![pullHO1 h a, pullHO1 h b]`. Apply the tactic sequence `funext i; fin_cases i <;> try rfl`. Rewrite using `[exteriorPower.map_apply_ιMulti, hc, he, he']`.

Conclude with `(GlobalTheory.T.structureSheaf_pullback_relations_basic R X X' s s' φ h).2.1 a b _ _ (isPullO_pullHO1 h a) (isPullO_pullHO1 h b)`. Establish `ht : t ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2))`. Rewrite using `[exteriorPower.ιMulti_span]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `ht using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨v, rfl⟩` from `hx`. Apply the tactic sequence `have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> try rfl`. Use `key (v 0) (v 1)` as an intermediate fact. Rewrite `this` using `[← hv]`. Then use the resulting hypothesis.

Consider the case `zero => simp only [map_zero]`. Conclude with `isPullO2_zero`. Consider the case `add x y _ _ hx hy => simp only [map_add]`. Conclude with `isPullO2_add hx hy`. Consider the case `smul r x _ hx => simp only [map_smul]`.

Conclude with `isPullO2_smul hx r`.
-/
theorem pullback_wedge_cup_square (h : φ ≫ s = s' ≫ spMap (RingHom.id R))
    (e : ⋀[R]^2 (HO1 s) ≃ₗ[R] CatCoh.H2 (OAff s))
    (he : ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = CatCoh.cup (OAff s) a b)
    (e' : ⋀[R]^2 (HO1 s') ≃ₗ[R] CatCoh.H2 (OAff s'))
    (he' : ∀ a b, e' (exteriorPower.ιMulti R 2 ![a, b]) = CatCoh.cup (OAff s') a b) (t : ⋀[R]^2 (HO1 s)) :
    IsPullbackH2Structure h (e t) (e' (exteriorPower.map 2 (pullHO1 h) t)) := by
  have key : ∀ a b : HO1 s, IsPullbackH2Structure h (e (exteriorPower.ιMulti R 2 ![a, b]))
      (e' (exteriorPower.map 2 (pullHO1 h) (exteriorPower.ιMulti R 2 ![a, b]))) := by
    intro a b
    have hc : (pullHO1 h) ∘ ![a, b] = ![pullHO1 h a, pullHO1 h b] := by
      funext i; fin_cases i <;> try rfl
    rw [exteriorPower.map_apply_ιMulti, hc, he, he']
    exact (GlobalTheory.T.structureSheaf_pullback_relations_basic R X X' s s' φ h).2.1 a b _ _ (isPullO_pullHO1 h a) (isPullO_pullHO1 h b)
  have ht : t ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> try rfl
    have := key (v 0) (v 1)
    rwa [← hv] at this
  | zero => simp only [map_zero]; exact isPullO2_zero
  | add x y _ _ hx hy => simp only [map_add]; exact isPullO2_add hx hy
  | smul r x _ hx => simp only [map_smul]; exact isPullO2_smul hx r

end GlobalTheory.Obs.PrimitivePullback

open GlobalTheory.Obs.PrimitivePullback in

/- English proof (translation)
Introduce `R _ A _ g hA hg c c₁ c₂ hm h1 h2`. Establish `hax : AxesVanishingStructureSheafDegOne` using `GlobalTheory.T.axesO1_of_projective_rank_cup H`. Take `⟨hAA, hgg⟩` from `(GlobalTheory.T.abelian_square_affine_h1_vanish R).1 A g hA hg`. Take `⟨⟨_, hproj, _⟩, e, he⟩` from `H R A g hA hg`. Take `⟨_, e', he'⟩` from `H R (A ⊗ A) (g + g) hAA hgg`.

Take `⟨t, rfl⟩` from `e.surjective c`. Establish `km` using `pullback_wedge_cup_square (overW μ[A]) e he e' he' t`. Establish `k1` using `pullback_wedge_cup_square (overW (fst A A)) e he e' he' t`. Establish `k2` using `pullback_wedge_cup_square (overW (snd A A)) e he e' he' t`. Establish `E : exteriorPower.map 2 (pullHO1 (overW μ[A])) t = exteriorPower.map 2 (pullHO1 (overW (fst A A))) t + exteriorPower.map 2 (pullHO1 (overW (snd A A))) t`.

Apply `e'.injective` to reduce the goal to its premises. Rewrite using `[map_add, ← isPullO2_unique hm km, ← isPullO2_unique h1 k1, ← isPullO2_unique h2 k2]`. Set `P` to `LinearEquiv.ofBijective (sumPull A) (sumPull_bijective A hax g hA hg)`. Establish `hμ : (pullHO1 (overW μ[A]) : HO1 A.hom →ₗ[R] HO1 (A ⊗ A).hom) = sumPull A ∘ₗ (LinearMap.inl R (HO1 A.hom) (HO1 A.hom) + LinearMap.inr R (HO1 A.hom) (HO1 A.hom))`. Use `LinearMap.ext fun a ↦ ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.comp_apply, LinearMap.add_apply, LinearMap.inl_apply, LinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add]`. Conclude with `pullHO1_mul A hax g hA hg a`. Establish `h₁ : (pullHO1 (overW (fst A A)) : HO1 A.hom →ₗ[R] HO1 (A ⊗ A).hom) = sumPull A ∘ₗ LinearMap.inl R (HO1 A.hom) (HO1 A.hom)`. Use `LinearMap.ext fun a ↦ ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, LinearMap.inl_apply]`.

Simplify using `only [sumPull, LinearMap.coprod_apply, map_zero, add_zero]`. Establish `h₂ : (pullHO1 (overW (snd A A)) : HO1 A.hom →ₗ[R] HO1 (A ⊗ A).hom) = sumPull A ∘ₗ LinearMap.inr R (HO1 A.hom) (HO1 A.hom)`. Use `LinearMap.ext fun a ↦ ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, LinearMap.inr_apply]`. Simplify using `only [sumPull, LinearMap.coprod_apply, map_zero, zero_add]`.

Simplify using `only [hμ, h₁, h₂, exteriorPower.map_comp, LinearMap.comp_apply] at E`. Rewrite `E` using `[← map_add (exteriorPower.map 2 (sumPull A))]`. Establish `hid : P.symm.toLinearMap ∘ₗ sumPull A = LinearMap.id` using `LinearMap.ext fun x ↦ P.symm_apply_apply x`. Establish `hinj : Function.Injective (exteriorPower.map 2 (sumPull A))`. Introduce `x y hxy`.

Establish `k : ∀ z, exteriorPower.map 2 P.symm.toLinearMap (exteriorPower.map 2 (sumPull A) z) = z`. Introduce `z`. Rewrite using `[← LinearMap.comp_apply, ← exteriorPower.map_comp, hid, exteriorPower.map_id, LinearMap.id_apply]`. Rewrite using `[← k x, ← k y, hxy]`. Use `haveI := hproj`.

Rewrite using `[GlobalTheory.T.exteriorPowerTwo_diagonal_additive_eq_zero_projective R (HO1 A.hom) t (hinj E), map_zero]`.
-/
theorem GlobalTheory.Obs.primitiveStructureSheafDegTwoVanish_of_cup_iso
    (H : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
      SmoothOfRelativeDimension g A.hom →
      (Module.Finite R (HO1 A.hom) ∧ Module.Projective R (HO1 A.hom) ∧
        ∀ p : PrimeSpectrum R, Module.rankAtStalk (HO1 A.hom) p = g) ∧
      ∃ e : ⋀[R]^2 (HO1 A.hom) ≃ₗ[R] GlobalTheory.CatCoh.H2 (OAff A.hom),
        ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = GlobalTheory.CatCoh.cup (OAff A.hom) a b) : PrimitiveStructureSheafDegTwoVanish := by
  intro R _ A _ g hA hg c c₁ c₂ hm h1 h2
  have hax : AxesVanishingStructureSheafDegOne := GlobalTheory.T.axesO1_of_projective_rank_cup H
  obtain ⟨hAA, hgg⟩ := (GlobalTheory.T.abelian_square_affine_h1_vanish R).1 A g hA hg
  obtain ⟨⟨_, hproj, _⟩, e, he⟩ := H R A g hA hg
  obtain ⟨_, e', he'⟩ := H R (A ⊗ A) (g + g) hAA hgg
  obtain ⟨t, rfl⟩ := e.surjective c
  have km := pullback_wedge_cup_square (overW μ[A]) e he e' he' t
  have k1 := pullback_wedge_cup_square (overW (fst A A)) e he e' he' t
  have k2 := pullback_wedge_cup_square (overW (snd A A)) e he e' he' t
  have E : exteriorPower.map 2 (pullHO1 (overW μ[A])) t =
      exteriorPower.map 2 (pullHO1 (overW (fst A A))) t + exteriorPower.map 2 (pullHO1 (overW (snd A A))) t := by
    apply e'.injective
    rw [map_add, ← isPullO2_unique hm km, ← isPullO2_unique h1 k1, ← isPullO2_unique h2 k2]
  let P := LinearEquiv.ofBijective (sumPull A) (sumPull_bijective A hax g hA hg)
  have hμ : (pullHO1 (overW μ[A]) : HO1 A.hom →ₗ[R] HO1 (A ⊗ A).hom) =
      sumPull A ∘ₗ (LinearMap.inl R (HO1 A.hom) (HO1 A.hom) + LinearMap.inr R (HO1 A.hom) (HO1 A.hom)) := by
    refine LinearMap.ext fun a ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.inl_apply, LinearMap.inr_apply, Prod.mk_add_mk,
      add_zero, zero_add]
    exact pullHO1_mul A hax g hA hg a
  have h₁ : (pullHO1 (overW (fst A A)) : HO1 A.hom →ₗ[R] HO1 (A ⊗ A).hom) =
      sumPull A ∘ₗ LinearMap.inl R (HO1 A.hom) (HO1 A.hom) := by
    refine LinearMap.ext fun a ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.inl_apply]
    simp only [sumPull, LinearMap.coprod_apply, map_zero, add_zero]
  have h₂ : (pullHO1 (overW (snd A A)) : HO1 A.hom →ₗ[R] HO1 (A ⊗ A).hom) =
      sumPull A ∘ₗ LinearMap.inr R (HO1 A.hom) (HO1 A.hom) := by
    refine LinearMap.ext fun a ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.inr_apply]
    simp only [sumPull, LinearMap.coprod_apply, map_zero, zero_add]
  simp only [hμ, h₁, h₂, exteriorPower.map_comp, LinearMap.comp_apply] at E
  rw [← map_add (exteriorPower.map 2 (sumPull A))] at E
  have hid : P.symm.toLinearMap ∘ₗ sumPull A = LinearMap.id :=
    LinearMap.ext fun x ↦ P.symm_apply_apply x
  have hinj : Function.Injective (exteriorPower.map 2 (sumPull A)) := by
    intro x y hxy
    have k : ∀ z, exteriorPower.map 2 P.symm.toLinearMap (exteriorPower.map 2 (sumPull A) z) = z := by
      intro z
      rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, hid, exteriorPower.map_id, LinearMap.id_apply]
    rw [← k x, ← k y, hxy]
  haveI := hproj
  rw [GlobalTheory.T.exteriorPowerTwo_diagonal_additive_eq_zero_projective R (HO1 A.hom) t (hinj E), map_zero]
