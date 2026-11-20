import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteProjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.LieRank

variable {S : Scheme.{0}}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dualMap_apply {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') (a : DualNumber R) :
    dualMap c a = TrivSqZeroExt.inl (c a.fst) + TrivSqZeroExt.inr (c a.snd) := rfl

/- English proof (translation)
Use `RingHom.ext fun r => ?_` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, dualMap_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, map_zero, TrivSqZeroExt.inr_zero, add_zero]`.
-/
theorem dualMap_comp_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') :
    (dualMap c).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp c := by
  refine RingHom.ext fun r => ?_
  simp only [RingHom.comp_apply, dualMap_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl,
    TrivSqZeroExt.snd_inl, map_zero, TrivSqZeroExt.inr_zero, add_zero]

/- English proof (translation)
Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(dualMap c a).fst = c a.fst`. Simplify using `[dualMap_apply]`.
-/
theorem fst_comp_dualMap {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap c) =
      c.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => ?_
  change (dualMap c a).fst = c a.fst
  simp [dualMap_apply]

/- English proof (translation)
Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `dualMap c (TrivSqZeroExt.map (r • (LinearMap.id : R →ₗ[R] R)) a) = TrivSqZeroExt.map (c r • (LinearMap.id : R' →ₗ[R'] R')) (dualMap c a)`. Apply the tactic sequence `ext <;> simp [dualMap_apply, mul_comm]`.
-/
theorem dualMap_comp_epsMul {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') (r : R) :
    (dualMap c).comp (epsMul r) = (epsMul (c r)).comp (dualMap c) := by
  refine RingHom.ext fun a => ?_
  change dualMap c (TrivSqZeroExt.map (r • (LinearMap.id : R →ₗ[R] R)) a) =
    TrivSqZeroExt.map (c r • (LinearMap.id : R' →ₗ[R'] R')) (dualMap c a)
  ext <;> simp [dualMap_apply, mul_comm]

def epsPull {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') (x : Sp R ⟶ S) :
    epsAt (spMap c ≫ x) ⟶ epsAt x :=
  Over.homMk (spMap (dualMap c)) (by
    change spMap (dualMap c) ≫ Spec.map _ ≫ x = Spec.map _ ≫ spMap c ≫ x
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    rw [spMap, spMap, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (dualMap_comp_algebraMap c))

/- English proof (translation)
Establish `h` using `MonObj.comp_one (Over.homMk (spMap c) rfl : Over.mk (spMap c ≫ x) ⟶ Over.mk x) (M := G)`. Conclude with `(congrArg (fun k => k.left) h).symm`.
-/
theorem one_left_pull (G : Over S) [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R')
    (x : Sp R ⟶ S) :
    (1 : Over.mk (spMap c ≫ x) ⟶ G).left = spMap c ≫ (1 : Over.mk x ⟶ G).left := by
  have h := MonObj.comp_one (Over.homMk (spMap c) rfl : Over.mk (spMap c ≫ x) ⟶ Over.mk x) (M := G)
  exact (congrArg (fun k => k.left) h).symm

/- English proof (translation)
Unfold `IsTanAt at hv ⊢`. Rewrite using `[one_left_pull, ← hv]`. Express the relevant statement in the definitionally equal form `_ ≫ spMap (dualMap c) ≫ v.left = _`. Rewrite using `[← Category.assoc, ← Category.assoc]`. Use `congr 1`.

Rewrite using `[spMap, spMap, ← Spec.map_comp, ← Spec.map_comp]`. Use `congr 1`. Conclude with `CommRingCat.hom_ext (by`. Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Conclude with `(RingHom.congr_fun (fst_comp_dualMap c) a))`.
-/
theorem isTanAt_pull (G : Over S) [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R')
    (x : Sp R ⟶ S) (v : epsAt x ⟶ G) (hv : IsTanAt G x v) :
    IsTanAt G (spMap c ≫ x) (epsPull c x ≫ v) := by
  unfold IsTanAt at hv ⊢
  rw [one_left_pull, ← hv]
  change _ ≫ spMap (dualMap c) ≫ v.left = _
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  rw [spMap, spMap, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (by
    refine RingHom.ext fun a => ?_
    exact (RingHom.congr_fun (fst_comp_dualMap c) a))

/- English proof (translation)
Simplify using `[epsPull]`.
-/
theorem epsPull_comp_left (G : Over S) {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R')
    (x : Sp R ⟶ S) (v : epsAt x ⟶ G) : (epsPull c x ≫ v).left = spMap (dualMap c) ≫ v.left := by
  simp [epsPull]

/- English proof (translation)
Establish `hex : ∀ e, ∃ e', M'.pt e' = epsPull (algebraMap R R') x ≫ M.pt e` using `fun e => M'.onto _ (isTanAt_pull G _ x _ (M.tan e))`. Use `choose f hf using hex`. Establish `hadd : ∀ a b, f (a + b) = f a + f b` using `fun a b => by`. Apply `M'.inj` to reduce the goal to its premises. Rewrite using `[M'.add, hf, hf, hf, M.add, MonObj.comp_mul]`.

Establish `hsmul : ∀ (r : R) a, f (r • a) = r • f a` using `fun r a => by`. Apply `M'.inj` to reduce the goal to its premises. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[← algebraMap_smul R' r (f a), M'.smul, hf, hf, epsPull_comp_left, epsPull_comp_left, M.smul, ← Category.assoc, ← Category.assoc]`. Use `congr 1`.

Rewrite using `[spMap, ← Spec.map_comp, ← Spec.map_comp]`. Use `congr 1`. Conclude with `CommRingCat.hom_ext (dualMap_comp_epsMul (algebraMap R R') r)`. Establish `hl : ∀ e, M.Lifts (algebraMap R R') (𝟙 G.left) e (M'.pt (f e))` using `fun e => by`. Unfold `LieModel.Lifts`.

Rewrite using `[hf, Category.comp_id, epsPull_comp_left]`. Conclude with `⟨⟨⟨f, hadd⟩, hsmul⟩, hl⟩`.
-/
theorem exists_lift (G : Over S) [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (x : Sp R ⟶ S) {E E' : Type} [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E'] [Module R E']
    [IsScalarTower R R' E'] (M : LieModel G x E) (M' : LieModel G (spMap (algebraMap R R') ≫ x) E') :
    ∃ j : E →ₗ[R] E', ∀ e, M.Lifts (algebraMap R R') (𝟙 G.left) e (M'.pt (j e)) := by
  have hex : ∀ e, ∃ e', M'.pt e' = epsPull (algebraMap R R') x ≫ M.pt e := fun e =>
    M'.onto _ (isTanAt_pull G _ x _ (M.tan e))
  choose f hf using hex
  have hadd : ∀ a b, f (a + b) = f a + f b := fun a b => by
    apply M'.inj
    rw [M'.add, hf, hf, hf, M.add, MonObj.comp_mul]
  have hsmul : ∀ (r : R) a, f (r • a) = r • f a := fun r a => by
    apply M'.inj
    apply Over.OverMorphism.ext
    rw [← algebraMap_smul R' r (f a), M'.smul, hf, hf, epsPull_comp_left, epsPull_comp_left, M.smul,
      ← Category.assoc, ← Category.assoc]
    congr 1
    rw [spMap, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (dualMap_comp_epsMul (algebraMap R R') r)
  have hl : ∀ e, M.Lifts (algebraMap R R') (𝟙 G.left) e (M'.pt (f e)) := fun e => by
    unfold LieModel.Lifts
    rw [hf, Category.comp_id, epsPull_comp_left]
  exact ⟨⟨⟨f, hadd⟩, hsmul⟩, hl⟩

/- English proof (translation)
Rewrite using `[← Module.rankAtStalk_baseChange (S := F) (M := E) p]`. Rewrite using `[Module.rankAtStalk_eq_finrank_of_free]`. Conclude with `(LinearEquiv.finrank_eq hj.equiv).symm`.
-/
theorem finrank_of_isBaseChange {A F : Type} [CommRing A] [Field F] [Algebra A F] {E E' : Type} [AddCommGroup E]
    [Module A E] [AddCommGroup E'] [Module F E'] [Module A E'] [IsScalarTower A F E'] [Module.Finite A E]
    [Module.Projective A E] (j : E →ₗ[A] E') (hj : IsBaseChange F j) (p : PrimeSpectrum F) :
    Module.finrank F E' = Module.rankAtStalk E (PrimeSpectrum.comap (algebraMap A F) p) := by
  rw [← Module.rankAtStalk_baseChange (S := F) (M := E) p]
  rw [Module.rankAtStalk_eq_finrank_of_free]
  exact (LinearEquiv.finrank_eq hj.equiv).symm

/- English proof (translation)
Establish `: IsLocalizedModule (nonZeroDivisors D) j` using `(isLocalizedModule_iff_isBaseChange (nonZeroDivisors D) L j).2 hj`. Establish `h1` using `IsLocalizedModule.rank_eq (nonZeroDivisors D) le_rfl j`. Establish `h2` using `IsLocalization.rank_eq L (N := E') (nonZeroDivisors D) le_rfl`. Simplify using `only [Module.finrank, h1, h2]`.
-/
theorem finrank_eq_of_isBaseChange_fractionRing {D L : Type} [CommRing D] [IsDomain D] [Field L] [Algebra D L]
    [IsFractionRing D L] {E E' : Type} [AddCommGroup E] [Module D E] [AddCommGroup E'] [Module L E'] [Module D E']
    [IsScalarTower D L E'] (j : E →ₗ[D] E') (hj : IsBaseChange L j) :
    Module.finrank D E = Module.finrank L E' := by
  have : IsLocalizedModule (nonZeroDivisors D) j :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors D) L j).2 hj
  have h1 := IsLocalizedModule.rank_eq (nonZeroDivisors D) le_rfl j
  have h2 := IsLocalization.rank_eq L (N := E') (nonZeroDivisors D) le_rfl
  simp only [Module.finrank, h1, h2]

end GlobalTheory.CompanionTheory.Ar.LieRank

namespace GlobalTheory.CompanionTheory.Ar.LieRank

/- English proof (translation)
Establish `hr : Set.range y ⊆ Set.range i₀`. Introduce and unpack `_ ⟨p, rfl⟩`. Establish `hp : p = IsLocalRing.closedPoint F` using `Subsingleton.elim _ _`. Rewrite using `[hp]`. Conclude with `h`.

Use `⟨(Spec.preimage (IsOpenImmersion.lift i₀ y hr)).hom, ?_⟩` and prove the remaining obligations. Establish `e : spMap (Spec.preimage (IsOpenImmersion.lift i₀ y hr)).hom = IsOpenImmersion.lift i₀ y hr` using `Spec.map_preimage _`. Rewrite using `[e]`. Conclude with `IsOpenImmersion.lift_fac i₀ y hr`.
-/
theorem exists_factor {X : Scheme.{0}} {A F : Type} [CommRing A] [Field F] (i₀ : Sp A ⟶ X) [IsOpenImmersion i₀]
    (y : Sp F ⟶ X) (h : genPt y ∈ Set.range i₀) : ∃ φ : A →+* F, spMap φ ≫ i₀ = y := by
  have hr : Set.range y ⊆ Set.range i₀ := by
    rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint F := Subsingleton.elim _ _
    rw [hp]
    exact h
  refine ⟨(Spec.preimage (IsOpenImmersion.lift i₀ y hr)).hom, ?_⟩
  have e : spMap (Spec.preimage (IsOpenImmersion.lift i₀ y hr)).hom = IsOpenImmersion.lift i₀ y hr :=
    Spec.map_preimage _
  rw [e]
  exact IsOpenImmersion.lift_fac i₀ y hr

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem genPt_comp {X : Scheme.{0}} {A F : Type} [CommRing A] [Field F] (i₀ : Sp A ⟶ X) (φ : A →+* F) :
    genPt (spMap φ ≫ i₀) = i₀ (PrimeSpectrum.comap φ (IsLocalRing.closedPoint F)) := rfl

/- English proof (translation)
Take `⟨hf, hp⟩` from `GlobalTheory.T.lie_model_finite_projective S G A i₀ E MA`. Use `letI : Algebra A F := φ.toAlgebra`. Use `letI : Module A Li := Module.compHom Li φ`. Use `haveI : IsScalarTower A F Li := ⟨fun a b c => by`. Rewrite using `[Algebra.smul_def, mul_smul]`.

Use the proof step `rfl⟩`. Take `⟨j, hj⟩` from `exists_lift G i₀ MA M`. Conclude with `finrank_of_isBaseChange j (GlobalTheory.T.lie_model_isBaseChange S G A F i₀ E Li MA M j hj) _`.
-/
theorem finrank_fieldPt {S : Scheme.{0}} (G : Over S) [GrpObj G] [Smooth G.hom] {A F : Type} [CommRing A] [Field F]
    (i₀ : Sp A ⟶ S) {E Li : Type} [AddCommGroup E] [Module A E] [AddCommGroup Li] [Module F Li]
    (MA : LieModel G i₀ E) (φ : A →+* F) (M : LieModel G (spMap φ ≫ i₀) Li) :
    Module.finrank F Li = Module.rankAtStalk E (PrimeSpectrum.comap φ (IsLocalRing.closedPoint F)) := by
  obtain ⟨hf, hp⟩ := GlobalTheory.T.lie_model_finite_projective S G A i₀ E MA
  letI : Algebra A F := φ.toAlgebra
  letI : Module A Li := Module.compHom Li φ
  haveI : IsScalarTower A F Li := ⟨fun a b c => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  obtain ⟨j, hj⟩ := exists_lift G i₀ MA M
  exact finrank_of_isBaseChange j (GlobalTheory.T.lie_model_isBaseChange S G A F i₀ E Li MA M j hj) _

/- English proof (translation)
Take `⟨U, hU, hqU, -⟩` from `exists_isAffineOpen_mem_and_subset (x := genPt y₂) (U := ⊤) trivial`. Establish `h₁U : genPt y₁ ∈ U` using `h.mem_open U.isOpen hqU`. Establish `hr : Set.range hU.fromSpec = (U : Set X)` using `hU.range_fromSpec`. Take `⟨φ₁, rfl⟩` from `exists_factor (A := Γ(X, U)) hU.fromSpec y₁ (by rw [hr]; exact h₁U)`. Take `⟨φ₂, rfl⟩` from `exists_factor (A := Γ(X, U)) hU.fromSpec y₂ (by rw [hr]; exact hqU)`.

Take `⟨E, _, _, ⟨MA⟩⟩` from `lieModel_exists X G Γ(X, U) hU.fromSpec`. Take `⟨hf, hp⟩` from `GlobalTheory.T.lie_model_finite_projective X G Γ(X, U) hU.fromSpec E MA`. Use `haveI := Module.finitePresentation_of_projective Γ(X, U) E`. Rewrite using `[finrank_fieldPt G _ MA φ₁ M₁, finrank_fieldPt G _ MA φ₂ M₂]`. Rewrite `h` using `[genPt_comp, genPt_comp]`.

Establish `hs` using `(hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff).1 h`. Conclude with `(hs.map (Module.isLocallyConstant_rankAtStalk (R := Γ(X, U)) (M := E)).continuous).eq`.
-/
theorem finrank_eq_of_specializes {X : Scheme.{0}} (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    {F₁ F₂ : Type} [Field F₁] [Field F₂] (y₁ : Sp F₁ ⟶ X) (y₂ : Sp F₂ ⟶ X) (h : genPt y₁ ⤳ genPt y₂)
    {E₁ E₂ : Type} [AddCommGroup E₁] [Module F₁ E₁] [AddCommGroup E₂] [Module F₂ E₂]
    (M₁ : LieModel G y₁ E₁) (M₂ : LieModel G y₂ E₂) :
    Module.finrank F₁ E₁ = Module.finrank F₂ E₂ := by
  obtain ⟨U, hU, hqU, -⟩ := exists_isAffineOpen_mem_and_subset (x := genPt y₂) (U := ⊤) trivial
  have h₁U : genPt y₁ ∈ U := h.mem_open U.isOpen hqU
  have hr : Set.range hU.fromSpec = (U : Set X) := hU.range_fromSpec
  obtain ⟨φ₁, rfl⟩ := exists_factor (A := Γ(X, U)) hU.fromSpec y₁ (by rw [hr]; exact h₁U)
  obtain ⟨φ₂, rfl⟩ := exists_factor (A := Γ(X, U)) hU.fromSpec y₂ (by rw [hr]; exact hqU)
  obtain ⟨E, _, _, ⟨MA⟩⟩ := lieModel_exists X G Γ(X, U) hU.fromSpec
  obtain ⟨hf, hp⟩ := GlobalTheory.T.lie_model_finite_projective X G Γ(X, U) hU.fromSpec E MA
  haveI := Module.finitePresentation_of_projective Γ(X, U) E
  rw [finrank_fieldPt G _ MA φ₁ M₁, finrank_fieldPt G _ MA φ₂ M₂]
  rw [genPt_comp, genPt_comp] at h
  have hs := (hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff).1 h
  exact (hs.map (Module.isLocallyConstant_rankAtStalk (R := Γ(X, U)) (M := E)).continuous).eq

end GlobalTheory.CompanionTheory.Ar.LieRank

namespace GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
Introduce `X Ω _ ξ hsp G _ _ _ Li _ _ M L _ _ z V _ _ MB`. Take `⟨V', _, _, ⟨M'⟩⟩` from `lieModel_exists X G L (spMap (algebraMap (𝓞 L) L) ≫ z)`. Use `letI : Module (𝓞 L) V' := Module.compHom V' (algebraMap (𝓞 L) L)`. Use `haveI : IsScalarTower (𝓞 L) L V' := ⟨fun a b c => by`. Rewrite using `[Algebra.smul_def, mul_smul]`.

Use the proof step `rfl⟩`. Take `⟨j, hj⟩` from `LieRank.exists_lift G z MB M'`. Rewrite using `[LieRank.finrank_eq_of_isBaseChange_fractionRing j (GlobalTheory.T.lie_model_isBaseChange X G (𝓞 L) L z V V' MB M' j hj)]`. Conclude with `(LieRank.finrank_eq_of_specializes G ξ _ (hsp _) M M').symm`.
-/
theorem lieModel_finrank_eq : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] (MB : LieModel G z V), Module.finrank (𝓞 L) V = Module.finrank Ω Li := by
  intro X Ω _ ξ hsp G _ _ _ Li _ _ M L _ _ z V _ _ MB
  obtain ⟨V', _, _, ⟨M'⟩⟩ := lieModel_exists X G L (spMap (algebraMap (𝓞 L) L) ≫ z)
  letI : Module (𝓞 L) V' := Module.compHom V' (algebraMap (𝓞 L) L)
  haveI : IsScalarTower (𝓞 L) L V' := ⟨fun a b c => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  obtain ⟨j, hj⟩ := LieRank.exists_lift G z MB M'
  rw [LieRank.finrank_eq_of_isBaseChange_fractionRing j (GlobalTheory.T.lie_model_isBaseChange X G (𝓞 L) L z V V' MB M' j hj)]
  exact (LieRank.finrank_eq_of_specializes G ξ _ (hsp _) M M').symm

end GlobalTheory.CompanionTheory.Ar
