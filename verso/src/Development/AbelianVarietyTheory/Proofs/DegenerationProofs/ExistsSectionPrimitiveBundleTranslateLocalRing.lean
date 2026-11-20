import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVR
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIsoOfFlatOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemSmulTopOfForallMem

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.PrimitiveOverLocalRing
open GlobalTheory.CechPic GlobalTheory.StabFlat GlobalTheory.PrimitiveOverValuationRing

/- English proof (translation)
Set `t` to `a ≫ B.hom`. Take `⟨F, hF, hΛ, hcl⟩` from `exists_family hL hO hΘ hu t (Over.homMk a rfl)`. Set `B'` to `(Over.pullback t).obj B`. Establish `hB' : IsAbelianScheme B'` using `TLinPf.isAb_pullback t B hB`. Establish `hpb : IsPullback (pullback.fst B.hom t) B'.hom B.hom t` using `IsPullback.of_hasPullback _ _`.

Establish `hp' : IsProjBy B'.hom` using `isProjBy_baseChange hp hpb`. Establish `hg' : SmoothOfRelativeDimension g B'.hom`. Use `smoothOfRelativeDimension_isStableUnderBaseChange g` as an intermediate fact. Conclude with `MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) hpb hg`. Establish `test : ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : A →+* R) (X' : Scheme.{0}) (π : X' ⟶ B'.left) (f' : X' ⟶ Spec (CommRingCat.of R)), IsPullback π f' B'.hom (Spec.map (CommRingCat.ofHom φ)) → (Triv (F.pull π) ↔ ∃ y : Spec (CommRingCat.of R) ⟶ H.left, y ≫ j.left = Spec.map (Com …`.

Introduce `R _ _ φ X' π f' h`. Set `T : Over (Spec (CommRingCat.of V))` to `Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ t)`. Set `x : T ⟶ B` to `Over.homMk (Spec.map (CommRingCat.ofHom φ) ≫ a) (Category.assoc _ _ _)`. Establish `hM : (LB.div (translDiff B L x) (O.pull (snd T B).left)).IsLB` using `LB.isLB_div (LB.isLB_linComb hL _ _) (pull_isLB hO _)`. Establish `q : IsPullback f' (π ≫ pullback.fst B.hom t) T.hom B.hom` using `(h.paste_horiz hpb).flip`.

Set `W : Over (Spec (CommRingCat.of V))` to `Over.mk (f' ≫ T.hom)`. Set `e : W ⟶ T ⊗ B` to `Over.homMk q.isoPullback.hom (by show q.isoPullback.hom ≫ pullback.fst T.hom B.hom ≫ T.hom = f' ≫ T.hom`. Rewrite using `[IsPullback.isoPullback_hom_fst_assoc])`. Establish `: IsIso e.left` using `inferInstanceAs (IsIso q.isoPullback.hom)`. Establish `c₁ : CechPic.pull π (cls F hF) = CechPic.pull e.left (cls _ hM)`.

Rewrite using `[cls_eq_dcl hL hO, pull_dcl]`. Use `hcl W π _ _ ?_ q.isoPullback_hom_snd` and prove the remaining obligations. Use `show q.isoPullback.hom ≫ pullback.fst T.hom B.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ a = π ≫ B'.hom ≫ a`. Rewrite using `[IsPullback.isoPullback_hom_fst_assoc, h.w_assoc]`. Use `(cls_eq_zero_iff (pull_isLB hF π)).symm.trans ?_` and prove the remaining obligations.

Rewrite using `[cls_pull hF, c₁, pull_iso_eq_zero]`. Use `((loc_triv_iff (R := R) (fst T B).left hM).symm.trans (hH T x)).trans ⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨y, hy⟩`. Conclude with `⟨y.left, congrArg (·.left) hy⟩`. Introduce and unpack `⟨y, hy⟩`.

Use `⟨Over.homMk y ?_, Over.OverMorphism.ext hy⟩` and prove the remaining obligations. Rewrite using `[← Over.w j, ← Category.assoc, hy]`. Conclude with `Category.assoc _ _ _`. Take `⟨P⟩` from `GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj A _ B'.hom hB'.smooth hp' F hF`. Use `hB'.proper` as an intermediate fact.

Use `hB'.geomConnected` as an intermediate fact. Establish `q₀` using `IsPullback.of_hasPullback B'.hom (Spec.map (CommRingCat.ofHom g₀))`. Take `⟨I, ⟨eI⟩, hI⟩` from `GlobalTheory.UU.SecCyclic.cyclic_ideal A _ B'.hom F hF P inferInstance inferInstance K₀ g₀ hg₀ _ _ _ q₀ (CubeOpen.bijective_appTop hG B' hB' q₀) ((test K₀ g₀ _ _ _ q₀).2 h₀)`. Take `⟨C, c₁, c₂, ⟨eC⟩, c₃⟩` from `GlobalTheory.T.exists_perfect_free_finite_complex A B' hB' hp' g hg' F hF hΛ P`. Use `⟨I, C, c₁, c₂, ⟨eC.trans eI⟩, fun p _ => ?_, fun R _ _ φ => (test R φ _ _ _ (IsPullback.of_hasPullback _ _)).symm.trans (hI R φ _ _ _ (IsPullback.of_hasPullback _ _))⟩` and prove the remaining obligations.

Set `K` to `AlgebraicClosure p.ResidueField`. Set `φ : A →+* K` to `(algebraMap p.ResidueField K).comp (algebraMap A p.ResidueField)`. Establish `hk : RingHom.ker φ = p`. Rewrite using `[RingHom.ker_comp_of_injective _ (algebraMap p.ResidueField K).injective, Ideal.ker_algebraMap_residueField]`. Use `⟨K, inferInstance, φ, hk, fun i hi => c₃ K φ _ _ _ (IsPullback.of_hasPullback _ _) i ?_⟩` and prove the remaining obligations.

Break down `hi with hi | hi` into its components or cases. Conclude with `Or.inr fun ht => hi (hk ▸ (hI K φ _ _ _ (IsPullback.of_hasPullback _ _)).1 ht)`. Conclude with `Or.inl hi`.
-/
theorem exists_ideal_complex (hG : GlobalFnsSt) {V : Type} [CommRing V] (B : Over (Spec (CommRingCat.of V))) [GrpObj B]
    [IsCommMonObj B] (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) {g : ℕ} (hg : SmoothOfRelativeDimension g B.hom)
    {L O : LB B.left} (hL : L.IsLB) (hO : O.IsLB) (hΘ : ∃ t : LB.Gen (Theta B L), t.IsGen)
    (hu : ∃ u : LB.Gen (abelian₂ B O), u.IsGen) {H : Over (Spec (CommRingCat.of V))} (j : H ⟶ B)
    (hH : ∀ (T : Over (Spec (CommRingCat.of V))) (x : T ⟶ B), (∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι)) ↔
        ∃ y : T ⟶ H, y ≫ j = x)
    (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (a : Spec (CommRingCat.of A) ⟶ B.left)
    (K₀ : Type) [Field K₀] (g₀ : A →+* K₀) (hg₀ : IsLocalHom g₀)
    (h₀ : ∃ y : Spec (CommRingCat.of K₀) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom g₀) ≫ a) :
    ∃ (I : Ideal A) (C : CochainComplex (ModuleCat.{0} A) ℕ), (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) ∧
      (∃ n, ∀ i, n < i → IsZero (C.X i)) ∧
      Nonempty ((Module.Dual A (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[A] A ⧸ I) ∧
      (∀ p : Ideal A, p.IsPrime → ∃ (K : Type) (_ : Field K) (φ : A →+* K), RingHom.ker φ = p ∧
        ∀ i, (¬ I ≤ p ∨ g < i) → (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) ∧
      ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : A →+* R),
        (∃ y : Spec (CommRingCat.of R) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ a) ↔
          I ≤ RingHom.ker φ := by
  let t := a ≫ B.hom
  obtain ⟨F, hF, hΛ, hcl⟩ := exists_family hL hO hΘ hu t (Over.homMk a rfl)
  let B' := (Over.pullback t).obj B
  have hB' : IsAbelianScheme B' := TLinPf.isAb_pullback t B hB
  have hpb : IsPullback (pullback.fst B.hom t) B'.hom B.hom t := IsPullback.of_hasPullback _ _
  have hp' : IsProjBy B'.hom := isProjBy_baseChange hp hpb
  have hg' : SmoothOfRelativeDimension g B'.hom := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange g
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) hpb hg
  have test : ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : A →+* R) (X' : Scheme.{0}) (π : X' ⟶ B'.left)
      (f' : X' ⟶ Spec (CommRingCat.of R)), IsPullback π f' B'.hom (Spec.map (CommRingCat.ofHom φ)) →
      (Triv (F.pull π) ↔
        ∃ y : Spec (CommRingCat.of R) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ a) := by
    intro R _ _ φ X' π f' h
    let T : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ t)
    let x : T ⟶ B := Over.homMk (Spec.map (CommRingCat.ofHom φ) ≫ a) (Category.assoc _ _ _)
    have hM : (LB.div (translDiff B L x) (O.pull (snd T B).left)).IsLB :=
      LB.isLB_div (LB.isLB_linComb hL _ _) (pull_isLB hO _)
    have q : IsPullback f' (π ≫ pullback.fst B.hom t) T.hom B.hom := (h.paste_horiz hpb).flip
    let W : Over (Spec (CommRingCat.of V)) := Over.mk (f' ≫ T.hom)
    let e : W ⟶ T ⊗ B := Over.homMk q.isoPullback.hom (by
      show q.isoPullback.hom ≫ pullback.fst T.hom B.hom ≫ T.hom = f' ≫ T.hom
      rw [IsPullback.isoPullback_hom_fst_assoc])
    have : IsIso e.left := inferInstanceAs (IsIso q.isoPullback.hom)
    have c₁ : CechPic.pull π (cls F hF) = CechPic.pull e.left (cls _ hM) := by
      rw [cls_eq_dcl hL hO, pull_dcl]
      refine hcl W π _ _ ?_ q.isoPullback_hom_snd
      show q.isoPullback.hom ≫ pullback.fst T.hom B.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ a =
        π ≫ B'.hom ≫ a
      rw [IsPullback.isoPullback_hom_fst_assoc, h.w_assoc]
    refine (cls_eq_zero_iff (pull_isLB hF π)).symm.trans ?_
    rw [cls_pull hF, c₁, pull_iso_eq_zero]
    refine ((loc_triv_iff (R := R) (fst T B).left hM).symm.trans (hH T x)).trans ⟨?_, ?_⟩
    · rintro ⟨y, hy⟩
      exact ⟨y.left, congrArg (·.left) hy⟩
    · rintro ⟨y, hy⟩
      refine ⟨Over.homMk y ?_, Over.OverMorphism.ext hy⟩
      rw [← Over.w j, ← Category.assoc, hy]
      exact Category.assoc _ _ _
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj A _ B'.hom hB'.smooth hp' F hF
  have := hB'.proper
  have := hB'.geomConnected
  have q₀ := IsPullback.of_hasPullback B'.hom (Spec.map (CommRingCat.ofHom g₀))
  obtain ⟨I, ⟨eI⟩, hI⟩ := GlobalTheory.UU.SecCyclic.cyclic_ideal A _ B'.hom F hF P inferInstance inferInstance K₀ g₀ hg₀ _ _ _
    q₀ (CubeOpen.bijective_appTop hG B' hB' q₀) ((test K₀ g₀ _ _ _ q₀).2 h₀)
  obtain ⟨C, c₁, c₂, ⟨eC⟩, c₃⟩ := GlobalTheory.T.exists_perfect_free_finite_complex A B' hB' hp' g hg' F hF hΛ P
  refine ⟨I, C, c₁, c₂, ⟨eC.trans eI⟩, fun p _ => ?_, fun R _ _ φ =>
    (test R φ _ _ _ (IsPullback.of_hasPullback _ _)).symm.trans (hI R φ _ _ _ (IsPullback.of_hasPullback _ _))⟩
  let K := AlgebraicClosure p.ResidueField
  let φ : A →+* K := (algebraMap p.ResidueField K).comp (algebraMap A p.ResidueField)
  have hk : RingHom.ker φ = p := by
    rw [RingHom.ker_comp_of_injective _ (algebraMap p.ResidueField K).injective, Ideal.ker_algebraMap_residueField]
  refine ⟨K, inferInstance, φ, hk, fun i hi => c₃ K φ _ _ _ (IsPullback.of_hasPullback _ _) i ?_⟩
  rcases hi with hi | hi
  · exact Or.inr fun ht => hi (hk ▸ (hI K φ _ _ _ (IsPullback.of_hasPullback _ _)).1 ht)
  · exact Or.inl hi

/- English proof (translation)
Introduce `hL _ V _ _ _ P O hO hu`. Establish `proj : IsProjBy P.A.hom`. Take `⟨d, -, n, s, hs⟩` from `(GlobalTheory.Unif.relAmple_iff_veryAmpleBy V P.A P.L P.isLB).1 P.ample`. Conclude with `⟨_, isLB_pw P.isLB _, n, s, hs⟩`. Take `⟨H, j, hj, hH⟩` from `GlobalTheory.T.exists_closed_subscheme_translation_kernel hL.globalFns V P.A P.isAb proj P.L O P.isLB hO`.

Establish `fin : IsFinite H.hom` using `GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hL.globalFns V P.A P.isAb P.L O P.isLB hO P.ample H j hj hH`. Take `⟨r, hr⟩` from `P.rigid`. Take `⟨c⟩` from `(hL.cube _ P ⟨P.L, r, P.isLB, hr⟩ rfl).1`. Establish `mono : Mono H.hom` using `⟨fun {Z} a b e => by`. Set `a' : Over.mk (b ≫ H.hom) ⟶ H` to `Over.homMk a e`.

Set `b' : Over.mk (b ≫ H.hom) ⟶ H` to `Over.homMk b rfl`. Use `(inK_mul_inv P.isLB hO (a' ≫ j) (b' ≫ j) ((hH _ _).2 ⟨_, rfl⟩) ((hH _ _).2 ⟨_, rfl⟩)).eq_one P.ktriv` as an intermediate fact. Rewrite `this` using `[mul_inv_eq_one]`. Conclude with `(cancel_mono j.left).1 (congrArg CommaMorphism.left this)⟩`. Establish `: IsClosedImmersion H.hom` using `(IsClosedImmersion.iff_isFinite_and_mono _).2 ⟨fin, mono⟩`.

Set `K : Type` to `AlgebraicClosure (IsLocalRing.ResidueField V)`. Set `φ : V →+* K` to `(algebraMap (IsLocalRing.ResidueField V) K).comp (IsLocalRing.residue V)`. Establish `: IsLocalHom φ` using `RingHom.isLocalHom_comp _ _`. Take `⟨x₀, hx₀⟩` from `exists_geometric_point hL P hO hu K (Spec.map (CommRingCat.ofHom φ))`. Take `⟨y, -⟩` from `(hH _ x₀).1 fun p => ⟨⊤, trivial, by`.

Establish `hM` using `LB.isLB_div (show (translDiff P.A P.L x₀).IsLB from LB.isLB_linComb P.isLB _ _) (pull_isLB hO (snd _ P.A).left)`. Use `(cls_eq_zero_iff (pull_isLB hM _)).1 ?_` and prove the remaining obligations. Rewrite using `[cls_pull hM, (cls_eq_zero_iff hM).2 hx₀, map_zero]⟩`. Set `y' : Spec (CommRingCat.of K) ⟶ H.left` to `y.left`. Establish `hy : H.hom (y' (IsLocalRing.closedPoint K)) = IsLocalRing.closedPoint V` using `(congrArg (fun q => q (IsLocalRing.closedPoint K)) (Over.w y)).trans (IsLocalRing.comap_closedPoint φ)`.

Take `⟨R, _, _, _, _, ξ, g₀, hfl, hξ, hξV, hg₀, hξK, hreg, hdim⟩` from `FibreAcyclic.exists_localRing P.A.hom P.g P.smoothDim (y' ≫ j.left) (by`. Use `j.left.isClosedEmbedding.isClosedMap _ (isClosed_of_isFinite H.hom _ hy)` as an intermediate fact. Rewrite using `[Set.image_singleton] at this) ((congrArg (fun q => q (y' (IsLocalRing.closedPoint K))) (Over.w j)).trans hy)` and apply the resulting hypothesis. Use `P.isAb.comm` as an intermediate fact. Take `⟨I, C, c₁, ⟨n, c₂⟩, ⟨e⟩, c₃, hI⟩` from `exists_ideal_complex hL.globalFns P.A P.isAb proj P.smoothDim P.isLB hO ⟨c.t, c.isGen⟩ hu j hH R ξ K g₀ hg₀ ⟨y', hξK.symm⟩`.

Establish `hI₀ : I ≠ ⊤` using `ne_top_of_le_ne_top (RingHom.ker_ne_top g₀) ((hI K g₀).1 ⟨y', hξK.symm⟩)`. Establish `: Nontrivial (R ⧸ I)` using `Ideal.Quotient.nontrivial_iff.2 hI₀`. Establish `: IsLocalRing (R ⧸ I)` using `IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective`. Take `⟨w, hw⟩` from `(hI (R ⧸ I) (Ideal.Quotient.mk I)).2 Ideal.mk_ker.ge`. Establish `hwV : w ≫ H.hom = Spec.map (CommRingCat.ofHom (algebraMap V (R ⧸ I)))`.

Rewrite using `[← Over.w j, ← Category.assoc, hw, Category.assoc, hξV, ← Spec.map_comp]`. Both sides reduce to the same expression. Establish `hN : (IsLocalRing.maximalIdeal V).map (algebraMap V R) ≤ IsLocalRing.maximalIdeal R` using `IsLocalRing.le_maximalIdeal (Ideal.Quotient.nontrivial_iff.1 inferInstance)`. Establish `hloc : IsLocalHom (algebraMap V R)` using `((IsLocalRing.local_hom_TFAE (algebraMap V R)).out 2 0).1 hN`. Establish `hsurj : Function.Surjective (algebraMap V (R ⧸ I))`.

Establish `: IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))` using `IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective`. Establish `: IsPreimmersion (w ≫ j.left)` using `hw ▸ inferInstance`. Establish `: IsPreimmersion w` using `IsPreimmersion.of_comp w j.left`. Establish `h₁ : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap V (R ⧸ I))))` using `hwV ▸ inferInstance`. Establish `: IsLocalHom (Ideal.Quotient.mk I)` using `IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective`.

Establish `: IsLocalHom (algebraMap V (R ⧸ I))` using `RingHom.isLocalHom_comp (Ideal.Quotient.mk I) (algebraMap V R)`. Conclude with `RingHom.surjectiveOnStalks_iff_of_isLocalHom.1 ((IsPreimmersion.SpecMap_iff _).1 h₁).2`. Establish `hinj : Function.Injective (algebraMap V (R ⧸ I))`. Establish `hfree` using `fun i => (c₁ i).1`. Establish `hfin` using `fun i => (c₁ i).2`.

Use `FibreAcyclic.injective_of_exact (C.d 0 1).hom (C.d 1 2).hom (DualCokernel.d_d_apply C 0 1 2) ?_ I hI₀ e hsurj` and prove the remaining obligations. Use `FibreAcyclic.exact_hom_one _ hN _ (fun s hs x => ?_) P.g (FibreAcyclic.extZero_quotient _ _ hdim) C c₁ n c₂ fun p hp hNp => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hs, zero_mul]`. Take `⟨K', _, ψ, hψ, hex⟩` from `c₃ p hp`. Use `⟨K', inferInstance, ψ, hψ, fun i hi => hex i (hi.imp_left fun hne hIp => hne ?_)⟩` and prove the remaining obligations.

Use `(IsLocalRing.le_maximalIdeal hp.ne_top).antisymm fun s hs => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `hsurj (Ideal.Quotient.mk I s)`. Establish `h₁ : algebraMap V R a - s ∈ I` using `Ideal.Quotient.eq.1 ha`. Establish `h₂ : algebraMap V R a ∈ IsLocalRing.maximalIdeal R`. Simplify using `using add_mem (IsLocalRing.le_maximalIdeal hI₀ h₁) hs`.

Establish `h₃ : a ∈ IsLocalRing.maximalIdeal V` using `fun h => h₂ (h.map _)`. Simplify using `using sub_mem (hNp (Ideal.mem_map_of_mem _ h₃)) (hIp h₁)`. Establish `: IsIso (CommRingCat.ofHom (algebraMap V (R ⧸ I)))` using `(ConcreteCategory.isIso_iff_bijective _).2 ⟨hinj, hsurj⟩`. Set `σ : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ H` to `Over.homMk (inv (Spec.map (CommRingCat.ofHom (algebraMap V (R ⧸ I)))) ≫ w) (by`. Rewrite using `[Category.assoc, hwV]`.

Conclude with `IsIso.inv_hom_id _)`. Take `⟨U, hU, ht⟩` from `(hH _ (σ ≫ j)).2 ⟨σ, rfl⟩ (IsLocalRing.closedPoint V)`. Take `rfl : U = ⊤` from `(IsLocalRing.closedPoint_mem_iff U).1 hU`. Establish `e` using `pull_eq_zero_of_mem ((fst _ P.A).left ⁻¹ᵁ ⊤) (lift (toUnit P.A) (𝟙 P.A)).left (fun _ => trivial) ((triv_iff P.isLB hO (σ ≫ j) _).1 ht)`. Rewrite `e` using `[map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul, lift_snd, lift_fst_assoc, sub_eq_zero, Over.id_left, pull_id (cls O hO)]`.

Conclude with `⟨σ ≫ j, (cls_eq_iff hO (LB.isLB_linComb P.isLB _ _)).1 (e.symm.trans (cls_pair P.isLB _ _ _).symm)⟩`.
-/
theorem exists_section_translate : Laws → Laws2 → ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (P : PolAV (Spec (CommRingCat.of A))) (O : LB P.A.left), O.IsLB → (∃ u : LB.Gen (abelian₂ P.A O), u.IsGen) → ∃ x : 𝟙_ _ ⟶ P.A, LBIso O (LB.LinComb P.L (K := Fin 2) ![((toUnit P.A ≫ x) * 𝟙 P.A).left, 𝟙 P.A.left] ![1, -1]) := by
  intro hL _ V _ _ _ P O hO hu
  have proj : IsProjBy P.A.hom := by
    obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy V P.A P.L P.isLB).1 P.ample
    exact ⟨_, isLB_pw P.isLB _, n, s, hs⟩
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.T.exists_closed_subscheme_translation_kernel hL.globalFns V P.A P.isAb proj P.L O P.isLB hO
  have fin : IsFinite H.hom := GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hL.globalFns V P.A P.isAb P.L O P.isLB hO
    P.ample H j hj hH
  obtain ⟨r, hr⟩ := P.rigid
  obtain ⟨c⟩ := (hL.cube _ P ⟨P.L, r, P.isLB, hr⟩ rfl).1
  have mono : Mono H.hom := ⟨fun {Z} a b e => by
    let a' : Over.mk (b ≫ H.hom) ⟶ H := Over.homMk a e
    let b' : Over.mk (b ≫ H.hom) ⟶ H := Over.homMk b rfl
    have := (inK_mul_inv P.isLB hO (a' ≫ j) (b' ≫ j) ((hH _ _).2 ⟨_, rfl⟩) ((hH _ _).2 ⟨_, rfl⟩)).eq_one P.ktriv
    rw [mul_inv_eq_one] at this
    exact (cancel_mono j.left).1 (congrArg CommaMorphism.left this)⟩
  have : IsClosedImmersion H.hom := (IsClosedImmersion.iff_isFinite_and_mono _).2 ⟨fin, mono⟩
  let K : Type := AlgebraicClosure (IsLocalRing.ResidueField V)
  let φ : V →+* K := (algebraMap (IsLocalRing.ResidueField V) K).comp (IsLocalRing.residue V)
  have : IsLocalHom φ := RingHom.isLocalHom_comp _ _
  obtain ⟨x₀, hx₀⟩ := exists_geometric_point hL P hO hu K (Spec.map (CommRingCat.ofHom φ))
  obtain ⟨y, -⟩ := (hH _ x₀).1 fun p => ⟨⊤, trivial, by
    have hM := LB.isLB_div (show (translDiff P.A P.L x₀).IsLB from LB.isLB_linComb P.isLB _ _)
      (pull_isLB hO (snd _ P.A).left)
    refine (cls_eq_zero_iff (pull_isLB hM _)).1 ?_
    rw [cls_pull hM, (cls_eq_zero_iff hM).2 hx₀, map_zero]⟩
  let y' : Spec (CommRingCat.of K) ⟶ H.left := y.left
  have hy : H.hom (y' (IsLocalRing.closedPoint K)) = IsLocalRing.closedPoint V :=
    (congrArg (fun q => q (IsLocalRing.closedPoint K)) (Over.w y)).trans (IsLocalRing.comap_closedPoint φ)
  obtain ⟨R, _, _, _, _, ξ, g₀, hfl, hξ, hξV, hg₀, hξK, hreg, hdim⟩ :=
    FibreAcyclic.exists_localRing P.A.hom P.g P.smoothDim (y' ≫ j.left) (by
      have := j.left.isClosedEmbedding.isClosedMap _ (isClosed_of_isFinite H.hom _ hy)
      rwa [Set.image_singleton] at this) ((congrArg (fun q => q (y' (IsLocalRing.closedPoint K))) (Over.w j)).trans hy)
  have := P.isAb.comm
  obtain ⟨I, C, c₁, ⟨n, c₂⟩, ⟨e⟩, c₃, hI⟩ := exists_ideal_complex hL.globalFns P.A P.isAb proj P.smoothDim P.isLB hO
    ⟨c.t, c.isGen⟩ hu j hH R ξ K g₀ hg₀ ⟨y', hξK.symm⟩
  have hI₀ : I ≠ ⊤ := ne_top_of_le_ne_top (RingHom.ker_ne_top g₀) ((hI K g₀).1 ⟨y', hξK.symm⟩)
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI₀
  have : IsLocalRing (R ⧸ I) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨w, hw⟩ := (hI (R ⧸ I) (Ideal.Quotient.mk I)).2 Ideal.mk_ker.ge
  have hwV : w ≫ H.hom = Spec.map (CommRingCat.ofHom (algebraMap V (R ⧸ I))) := by
    rw [← Over.w j, ← Category.assoc, hw, Category.assoc, hξV, ← Spec.map_comp]
    rfl
  have hN : (IsLocalRing.maximalIdeal V).map (algebraMap V R) ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal (Ideal.Quotient.nontrivial_iff.1 inferInstance)
  have hloc : IsLocalHom (algebraMap V R) := ((IsLocalRing.local_hom_TFAE (algebraMap V R)).out 2 0).1 hN
  have hsurj : Function.Surjective (algebraMap V (R ⧸ I)) := by
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have : IsPreimmersion (w ≫ j.left) := hw ▸ inferInstance
    have : IsPreimmersion w := IsPreimmersion.of_comp w j.left
    have h₁ : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap V (R ⧸ I)))) := hwV ▸ inferInstance
    have : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have : IsLocalHom (algebraMap V (R ⧸ I)) := RingHom.isLocalHom_comp (Ideal.Quotient.mk I) (algebraMap V R)
    exact RingHom.surjectiveOnStalks_iff_of_isLocalHom.1 ((IsPreimmersion.SpecMap_iff _).1 h₁).2
  have hinj : Function.Injective (algebraMap V (R ⧸ I)) := by
    have hfree := fun i => (c₁ i).1
    have hfin := fun i => (c₁ i).2
    refine FibreAcyclic.injective_of_exact (C.d 0 1).hom (C.d 1 2).hom (DualCokernel.d_d_apply C 0 1 2) ?_ I hI₀ e hsurj
    refine FibreAcyclic.exact_hom_one _ hN _ (fun s hs x => ?_) P.g (FibreAcyclic.extZero_quotient _ _ hdim) C c₁ n c₂
      fun p hp hNp => ?_
    · rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hs, zero_mul]
    · obtain ⟨K', _, ψ, hψ, hex⟩ := c₃ p hp
      refine ⟨K', inferInstance, ψ, hψ, fun i hi => hex i (hi.imp_left fun hne hIp => hne ?_)⟩
      refine (IsLocalRing.le_maximalIdeal hp.ne_top).antisymm fun s hs => ?_
      obtain ⟨a, ha⟩ := hsurj (Ideal.Quotient.mk I s)
      have h₁ : algebraMap V R a - s ∈ I := Ideal.Quotient.eq.1 ha
      have h₂ : algebraMap V R a ∈ IsLocalRing.maximalIdeal R := by
        simpa using add_mem (IsLocalRing.le_maximalIdeal hI₀ h₁) hs
      have h₃ : a ∈ IsLocalRing.maximalIdeal V := fun h => h₂ (h.map _)
      simpa using sub_mem (hNp (Ideal.mem_map_of_mem _ h₃)) (hIp h₁)
  have : IsIso (CommRingCat.ofHom (algebraMap V (R ⧸ I))) := (ConcreteCategory.isIso_iff_bijective _).2 ⟨hinj, hsurj⟩
  let σ : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ H :=
    Over.homMk (inv (Spec.map (CommRingCat.ofHom (algebraMap V (R ⧸ I)))) ≫ w) (by
      rw [Category.assoc, hwV]
      exact IsIso.inv_hom_id _)
  obtain ⟨U, hU, ht⟩ := (hH _ (σ ≫ j)).2 ⟨σ, rfl⟩ (IsLocalRing.closedPoint V)
  obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 hU
  have e := pull_eq_zero_of_mem ((fst _ P.A).left ⁻¹ᵁ ⊤) (lift (toUnit P.A) (𝟙 P.A)).left (fun _ => trivial)
    ((triv_iff P.isLB hO (σ ≫ j) _).1 ht)
  rw [map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul,
    lift_snd, lift_fst_assoc, sub_eq_zero, Over.id_left, pull_id (cls O hO)] at e
  exact ⟨σ ≫ j, (cls_eq_iff hO (LB.isLB_linComb P.isLB _ _)).1 (e.symm.trans (cls_pair P.isLB _ _ _).symm)⟩

end GlobalTheory.PrimitiveOverLocalRing
