import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAugmentationTensorSigmaMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapNaturalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapInjectiveOfFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDifferenceDerivationOfLiftsAddSwapUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDifferenceDerivationOfLiftsCompStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

/- English proof (translation)
Introduce `R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F C' _ F' L L' n l hL hL' hl w`. Establish `hdiff : ∀ (T T' : C') (a : T ⟶ T') (b : L.B (n.G.obj T)), (L'.ρ a).comp (l T) b - (l T').comp (L.ρ (n.G.map a)) b ∈ I.map (algebraMap R (L'.B T'))`. Introduce `T T' a b`. Rewrite using `[← L'.ker, map_sub, sub_eq_zero]`. Simplify using `only [AlgHom.comp_apply, L'.nat]`.

Rewrite using `[hl, hl, L.nat]`. Conclude with `(n.naturality a _).symm`. Establish `hκ : ∀ (T T' : C') (a : T ⟶ T'), ∃ κ : Ω[F.obj (n.G.obj T)⁄R₀] →+ L'.B T', IsTheta I (L.p (n.G.obj T)) ((L'.ρ a).comp (l T)) ((l T').comp (L.ρ (n.G.map a))) κ` using `fun T T' a ↦ ((theta_classify R R₀ (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L'.B T') I hI π hπ (L.p _) (L.semi _) (L.surj _) (L.ker _) _).1 _ (hdiff T T' a)).exists`. Use `choose κ hκ using hκ`. Establish `hσ : ∀ T, ∃ σ : R₁ ⊗[R₀] F'.obj T →+ L'.B T, α.IsSig (L'.p T) σ` using `fun T ↦ GlobalTheory.T.exists_augmentation_tensor_sigma_map R R₀ I hI π hπ hk R₁ α (L'.B T) (F'.obj T) (L'.p T) (L'.semi T) (L'.surj T) (L'.ker T)`.

Use `choose σ hσ using hσ`. Establish `hz : ∀ (T T' : C') (a : T ⟶ T'), ∃ y : R₁ ⊗[R₀] F'.obj T', α.KerQ y ∧ σ T' y = κ T T' a (w.1 _)` using `fun T T' a ↦ (GlobalTheory.T.augmentation_sigma_map_basic_properties R R₀ I hI π hπ hk R₁ α (L'.B T') (F'.obj T') (L'.p T') (L'.semi T') (L'.surj T') (L'.ker T') (σ T') (hσ T')).2.2.2 _ ((hκ T T' a).mem _)`. Use `choose z hzq hzs using hz`. Establish `hcomp : ∀ (T T' T'' : C') (a : T ⟶ T') (b : T' ⟶ T'') (x : Ω[F.obj (n.G.obj T)⁄R₀]), κ T T'' (a ≫ b) x = L'.ρ b (κ T T' a x) + κ T' T'' b (p1 F (n.G.map a) x)`. Introduce `T T' T'' a b x`.

Establish `t1` using `(GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _) (L.surj _) (L.ker _) (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _) (L.surj _) (L.ker _) (L'.B T') (L'.B T'') _ _ _ (hκ T T' a)).1 (L'.ρ b)`. Establish `t2` using `(GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B (n.G.obj T')) (F.obj (n.G.obj T')) (L.p _) (L.semi _) (L.surj _) (L.ker _) (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _) (L.surj _) (L.ker _) (L'.B T'') (L'.B T'') _ _ _ (hκ T' T'' b)).2 (L.ρ (n. …`. Establish `e0 : ((L'.ρ b).comp (l T')).comp (L.ρ (n.G.map a)) = (L'.ρ b).comp ((l T').comp (L.ρ (n.G.map a)))` using `AlgHom.ext fun _ ↦ rfl`. Rewrite `t2` using `[e0]`. Establish `t3` using `((GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _) (L.surj _) (L.ker _) (L'.B T'') _ _ _ _ _ t1).2.1 t2)`.

Establish `e1 : (L'.ρ b).comp ((L'.ρ a).comp (l T)) = (L'.ρ (a ≫ b)).comp (l T)` using `AlgHom.ext fun y ↦ (hL' a b _).symm`. Establish `e2 : ((l T'').comp (L.ρ (n.G.map b))).comp (L.ρ (n.G.map a)) = (l T'').comp (L.ρ (n.G.map (a ≫ b)))` using `AlgHom.ext fun y ↦ by show l T'' (L.ρ (n.G.map b) (L.ρ (n.G.map a) y)) = l T'' (L.ρ (n.G.map (a ≫ b)) y)`. Rewrite using `[Functor.map_comp, hL]`. Rewrite `t3` using `[e1, e2]`. Establish `e3` using `(GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _) (L.surj _) (L.ker _) (L'.B T'') _ _ ((l T'').comp (L.ρ (n.G.map (a ≫ b)))) _ _ (hκ T T'' (a ≫ b))).2.2.1 t3`.

Conclude with `congrArg (fun f ↦ f x) e3`. Set `zc : Z1 (ext R₁ F')` to `⟨fun T T' a ↦ z T T' a, fun T T' T'' a b ↦ by`. Establish `sn` using `GlobalTheory.T.augmentation_sigma_map_natural R R₀ I hI π hπ hk R₁ α (L'.B T') (F'.obj T') (L'.p T') (L'.semi T') (L'.surj T') (L'.ker T') (L'.B T'') (F'.obj T'') (L'.p T'') (L'.semi T'') (L'.surj T'') (L'.ker T'') (L'.ρ b) (mp F' b) (fun y ↦ L'.nat b y) (σ T') (σ T'') (hσ T') (h …`. Express the relevant statement in the definitionally equal form `z T T'' (a ≫ b) = extHom R₁ (mp F' b) (z T T' a) + z T' T'' b`. Rewrite using `[← sub_eq_zero]`.

Use `haveI := L'.smooth T''`. Use `GlobalTheory.T.augmentation_sigma_map_injective_of_flat R R₀ I hI π hπ hk R₁ α (L'.B T'') (F'.obj T'') (L'.p T'') (L'.semi T'') (L'.surj T'') (L'.ker T'') (σ T'') (hσ T'') _ ?_ ?_` and prove the remaining obligations. Establish `h1` using `hzq T T'' (a ≫ b)`. Establish `h2` using `sn.2 _ (hzq T T' a)`. Establish `h3` using `hzq T' T'' b`.

Unfold `Aug.KerQ at h1 h2 h3 ⊢`. Rewrite using `[map_sub, map_add, h1, h2, h3]`. Simplify using the standard rewrite rules. Rewrite using `[map_sub, map_add, ← sn.1, hzs, hzs, hzs, hcomp, w.2 (n.G.map a)] simp⟩`. Conclude with `⟨H1.mk _ zc, κ, σ, zc, hκ, hσ, rfl, fun T T' a ↦ ⟨hzq T T' a, hzs T T' a⟩⟩`.
-/
theorem exists_isOb1 : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) F F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T), L.IsFun → L'.IsFun → L.IsLift L' n l → ∀ w : Glob1 F, ∃ c, L.IsOb1 L' n l α w c := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F C' _ F' L L' n l hL hL' hl w
  classical
  have hdiff : ∀ (T T' : C') (a : T ⟶ T') (b : L.B (n.G.obj T)),
      (L'.ρ a).comp (l T) b - (l T').comp (L.ρ (n.G.map a)) b ∈ I.map (algebraMap R (L'.B T')) := by
    intro T T' a b
    rw [← L'.ker, map_sub, sub_eq_zero]
    simp only [AlgHom.comp_apply, L'.nat]
    rw [hl, hl, L.nat]
    exact (n.naturality a _).symm
  have hκ : ∀ (T T' : C') (a : T ⟶ T'), ∃ κ : Ω[F.obj (n.G.obj T)⁄R₀] →+ L'.B T',
      IsTheta I (L.p (n.G.obj T)) ((L'.ρ a).comp (l T)) ((l T').comp (L.ρ (n.G.map a))) κ := fun T T' a ↦
    ((theta_classify R R₀ (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L'.B T') I hI π hπ (L.p _) (L.semi _)
      (L.surj _) (L.ker _) _).1 _ (hdiff T T' a)).exists
  choose κ hκ using hκ
  have hσ : ∀ T, ∃ σ : R₁ ⊗[R₀] F'.obj T →+ L'.B T, α.IsSig (L'.p T) σ := fun T ↦
    GlobalTheory.T.exists_augmentation_tensor_sigma_map R R₀ I hI π hπ hk R₁ α (L'.B T) (F'.obj T) (L'.p T) (L'.semi T) (L'.surj T) (L'.ker T)
  choose σ hσ using hσ
  have hz : ∀ (T T' : C') (a : T ⟶ T'), ∃ y : R₁ ⊗[R₀] F'.obj T', α.KerQ y ∧ σ T' y = κ T T' a (w.1 _) :=
    fun T T' a ↦ (GlobalTheory.T.augmentation_sigma_map_basic_properties R R₀ I hI π hπ hk R₁ α (L'.B T') (F'.obj T') (L'.p T') (L'.semi T')
      (L'.surj T') (L'.ker T') (σ T') (hσ T')).2.2.2 _ ((hκ T T' a).mem _)
  choose z hzq hzs using hz

  have hcomp : ∀ (T T' T'' : C') (a : T ⟶ T') (b : T' ⟶ T'') (x : Ω[F.obj (n.G.obj T)⁄R₀]),
      κ T T'' (a ≫ b) x = L'.ρ b (κ T T' a x) + κ T' T'' b (p1 F (n.G.map a) x) := by
    intro T T' T'' a b x
    have t1 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _) (L.surj _) (L.ker _)
      (L'.B T') (L'.B T'') _ _ _ (hκ T T' a)).1 (L'.ρ b)
    have t2 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B (n.G.obj T')) (F.obj (n.G.obj T')) (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _) (L.surj _) (L.ker _)
      (L'.B T'') (L'.B T'') _ _ _ (hκ T' T'' b)).2 (L.ρ (n.G.map a)) (mp F (n.G.map a)) (fun y ↦ L.nat _ y)
    have e0 : ((L'.ρ b).comp (l T')).comp (L.ρ (n.G.map a)) = (L'.ρ b).comp ((l T').comp (L.ρ (n.G.map a))) :=
      AlgHom.ext fun _ ↦ rfl
    rw [e0] at t2
    have t3 := ((GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (L'.B T'') _ _ _ _ _ t1).2.1 t2)
    have e1 : (L'.ρ b).comp ((L'.ρ a).comp (l T)) = (L'.ρ (a ≫ b)).comp (l T) :=
      AlgHom.ext fun y ↦ (hL' a b _).symm
    have e2 : ((l T'').comp (L.ρ (n.G.map b))).comp (L.ρ (n.G.map a)) = (l T'').comp (L.ρ (n.G.map (a ≫ b))) :=
      AlgHom.ext fun y ↦ by
        show l T'' (L.ρ (n.G.map b) (L.ρ (n.G.map a) y)) = l T'' (L.ρ (n.G.map (a ≫ b)) y)
        rw [Functor.map_comp, hL]
    rw [e1, e2] at t3
    have e3 := (GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (L'.B T'') _ _ ((l T'').comp (L.ρ (n.G.map (a ≫ b)))) _ _ (hκ T T'' (a ≫ b))).2.2.1 t3
    exact congrArg (fun f ↦ f x) e3
  let zc : Z1 (ext R₁ F') := ⟨fun T T' a ↦ z T T' a, fun T T' T'' a b ↦ by
    have sn := GlobalTheory.T.augmentation_sigma_map_natural R R₀ I hI π hπ hk R₁ α (L'.B T') (F'.obj T') (L'.p T') (L'.semi T') (L'.surj T')
      (L'.ker T') (L'.B T'') (F'.obj T'') (L'.p T'') (L'.semi T'') (L'.surj T'') (L'.ker T'') (L'.ρ b) (mp F' b)
      (fun y ↦ L'.nat b y) (σ T') (σ T'') (hσ T') (hσ T'')
    change z T T'' (a ≫ b) = extHom R₁ (mp F' b) (z T T' a) + z T' T'' b
    rw [← sub_eq_zero]
    haveI := L'.smooth T''
    refine GlobalTheory.T.augmentation_sigma_map_injective_of_flat R R₀ I hI π hπ hk R₁ α (L'.B T'') (F'.obj T'') (L'.p T'') (L'.semi T'') (L'.surj T'')
      (L'.ker T'') (σ T'') (hσ T'') _ ?_ ?_
    · have h1 := hzq T T'' (a ≫ b)
      have h2 := sn.2 _ (hzq T T' a)
      have h3 := hzq T' T'' b
      unfold Aug.KerQ at h1 h2 h3 ⊢
      rw [map_sub, map_add, h1, h2, h3]; simp
    · rw [map_sub, map_add, ← sn.1, hzs, hzs, hzs, hcomp, w.2 (n.G.map a)]
      simp⟩
  exact ⟨H1.mk _ zc, κ, σ, zc, hκ, hσ, rfl, fun T T' a ↦ ⟨hzq T T' a, hzs T T' a⟩⟩

end GlobalTheory.Obs
