import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSquareDiagonalSectionsGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSquareActionBundleIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSquareDiagonalRelAmpleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSquareActionSectionsGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullByCompStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullByFactorThroughStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructurePullbackExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraFiniteProjectiveRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraBaseChangeIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueBaseChangeVolumeFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopExteriorDualInvertibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeModuleTensorActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleActionOfFieldFibresStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.Obj

open GlobalTheory.CechPic

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

/- English proof (translation)
Use `letI : GrpObj ((Over.pullback b).obj X.A) := Functor.grpObjObj`. Use `haveI : IsCommMonObj ((Over.pullback b).obj X.A) := Functor.isCommMonObj_obj`. Establish `hg : IsGrpPullback ((Over.pullback b).obj X.A) X.A b (pullback.fst X.A.hom b)` using `isGrpPullback_pullback X.A b`. Take `⟨rm', hrm'⟩` from `GlobalTheory.OActPull.exists_oAct_of_isGrpPullback X.rm hg`. Set `A'` to `(Over.pullback b).obj X.A`.

Set `φ₂ : (G2 A').left ⟶ (G2 X.A).left` to `(lift (pushPt hg.1.w (fst A' A')) (pushPt hg.1.w (snd A' A'))).left`. Establish `hsq : IsSquare (pullback.fst X.A.hom b) φ₂`. Prove the components needed by the constructor for the conclusion. Express the relevant statement in the definitionally equal form `(lift (pushPt hg.1.w (fst A' A')) (pushPt hg.1.w (snd A' A')) ≫ fst X.A X.A).left = _`. Rewrite using `[lift_fst]`.

Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `(lift (pushPt hg.1.w (fst A' A')) (pushPt hg.1.w (snd A' A')) ≫ snd X.A X.A).left = _`. Rewrite using `[lift_snd]`. Both sides reduce to the same expression. Use `⟨{ A := A' ab := GlobalTheory.isAbelianScheme_pullback_obj b X.A X.ab dim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hg.1 X.dim rm := rm' P := fun c ↦ (X.P c).pull φ₂ isLB := fun c ↦ pull_isLB (X.isLB c) _ rig₁ := fun c ↦ (GlobalTheory.T.pullback_squar …` and prove the remaining obligations.

Use symmetry as in `:= fun c ↦ (GlobalTheory.T.pullback_square_action_bundle_iso X b A' _ hg rm' hrm' φ₂ hsq c c 1).1`. Use `add := fun c c' ↦ (GlobalTheory.T.pullback_square_action_bundle_iso X b A' _ hg rm' hrm' φ₂ hsq c c' 1).2.1`. Use `smul := fun a c ↦ (GlobalTheory.T.pullback_square_action_bundle_iso X b A' _ hg rm' hrm' φ₂ hsq c c a).2.2`. Use `pos := GlobalTheory.T.pullback_square_diagonal_rel_ample X b A' _ hg φ₂ hsq`. Use `ker := GlobalTheory.T.pullback_square_action_sections_generated X b A' _ hg rm' hrm' φ₂ hsq }, pullback.fst X.A.hom b, ⟨hg, hrm', φ₂, hsq, fun c ↦ ?_⟩⟩`.

Conclude with `(cls_eq_iff (pull_isLB (X.isLB c) φ₂) (pull_isLB (X.isLB c) φ₂)).1 rfl`.
-/
theorem exists_isPullBy {S S' : Scheme.{0}} (X : Obj F 𝔠 S) (b : S' ⟶ S) :
    ∃ (X' : Obj F 𝔠 S') (φ : X'.A.left ⟶ X.A.left), X'.IsPullBy X b φ := by
  letI : GrpObj ((Over.pullback b).obj X.A) := Functor.grpObjObj
  haveI : IsCommMonObj ((Over.pullback b).obj X.A) := Functor.isCommMonObj_obj
  have hg : IsGrpPullback ((Over.pullback b).obj X.A) X.A b (pullback.fst X.A.hom b) := isGrpPullback_pullback X.A b
  obtain ⟨rm', hrm'⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback X.rm hg
  let A' := (Over.pullback b).obj X.A
  let φ₂ : (G2 A').left ⟶ (G2 X.A).left := (lift (pushPt hg.1.w (fst A' A')) (pushPt hg.1.w (snd A' A'))).left
  have hsq : IsSquare (pullback.fst X.A.hom b) φ₂ := by
    constructor
    · change (lift (pushPt hg.1.w (fst A' A')) (pushPt hg.1.w (snd A' A')) ≫ fst X.A X.A).left = _
      rw [lift_fst]; rfl
    · change (lift (pushPt hg.1.w (fst A' A')) (pushPt hg.1.w (snd A' A')) ≫ snd X.A X.A).left = _
      rw [lift_snd]; rfl
  refine ⟨{ A := A'
            ab := GlobalTheory.isAbelianScheme_pullback_obj b X.A X.ab
            dim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hg.1 X.dim
            rm := rm'
            P := fun c ↦ (X.P c).pull φ₂
            isLB := fun c ↦ pull_isLB (X.isLB c) _
            rig₁ := fun c ↦ (GlobalTheory.T.pullback_square_diagonal_sections_generated X b A' _ hg φ₂ hsq c).1
            rig₂ := fun c ↦ (GlobalTheory.T.pullback_square_diagonal_sections_generated X b A' _ hg φ₂ hsq c).2
            symm := fun c ↦ (GlobalTheory.T.pullback_square_action_bundle_iso X b A' _ hg rm' hrm' φ₂ hsq c c 1).1
            add := fun c c' ↦ (GlobalTheory.T.pullback_square_action_bundle_iso X b A' _ hg rm' hrm' φ₂ hsq c c' 1).2.1
            smul := fun a c ↦ (GlobalTheory.T.pullback_square_action_bundle_iso X b A' _ hg rm' hrm' φ₂ hsq c c a).2.2
            pos := GlobalTheory.T.pullback_square_diagonal_rel_ample X b A' _ hg φ₂ hsq
            ker := GlobalTheory.T.pullback_square_action_sections_generated X b A' _ hg rm' hrm' φ₂ hsq }, pullback.fst X.A.hom b, ⟨hg, hrm', φ₂, hsq, fun c ↦ ?_⟩⟩
  exact (cls_eq_iff (pull_isLB (X.isLB c) φ₂) (pull_isLB (X.isLB c) φ₂)).1 rfl

/- English proof (translation)
The claim follows from `GlobalTheory.T.isPullBy_comp' h' h`.
-/
theorem IsPullBy.comp {S S' S'' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {X'' : Obj F 𝔠 S''}
    {b : S' ⟶ S} {b' : S'' ⟶ S'} {φ : X'.A.left ⟶ X.A.left} {ψ : X''.A.left ⟶ X'.A.left}
    (h' : X''.IsPullBy X' b' ψ) (h : X'.IsPullBy X b φ) : X''.IsPullBy X (b' ≫ b) (ψ ≫ φ) :=
  GlobalTheory.T.isPullBy_comp' h' h

/- English proof (translation)
The claim follows from `GlobalTheory.T.isPullBy_factor_through h h'`.
-/
theorem IsPullBy.cancel {S S' S'' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {X'' : Obj F 𝔠 S''}
    {b : S' ⟶ S} {b' : S'' ⟶ S'} {φ : X'.A.left ⟶ X.A.left} {χ : X''.A.left ⟶ X.A.left}
    (h : X''.IsPullBy X (b' ≫ b) χ) (h' : X'.IsPullBy X b φ) :
    ∃ ψ : X''.A.left ⟶ X'.A.left, X''.IsPullBy X' b' ψ ∧ ψ ≫ φ = χ :=
  GlobalTheory.T.isPullBy_factor_through h h'

/- English proof (translation)
Take `⟨α', hα'⟩` from `GlobalTheory.T.level_structure_pullback_exists h α`. Conclude with `⟨α', φ, h, hα'⟩`.
-/
theorem IsPullBy.exists_level {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {b : S' ⟶ S}
    {φ : X'.A.left ⟶ X.A.left} (h : X'.IsPullBy X b φ) {N : ℕ} (α : X.Level N) :
    ∃ α' : X'.Level N, IsLevelPull α' α b := by
  obtain ⟨α', hα'⟩ := GlobalTheory.T.level_structure_pullback_exists h α
  exact ⟨α', φ, h, hα'⟩

/- English proof (translation)
Take `⟨X', φ, h⟩` from `exists_isPullBy X b`. Take `⟨α', hα'⟩` from `h.exists_level α`. Conclude with `⟨X', α', hα'⟩`.
-/
theorem exists_isLevelPull {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {N : ℕ} (α : X.Level N) (b : S' ⟶ S) :
    ∃ (X' : Obj F 𝔠 S') (α' : X'.Level N), IsLevelPull α' α b := by
  obtain ⟨X', φ, h⟩ := exists_isPullBy X b
  obtain ⟨α', hα'⟩ := h.exists_level α
  exact ⟨X', α', hα'⟩

variable {R R' : Type} [CommRing R] [CommRing R']

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(v'.hom ≫ X'.rm.act a).left ≫ φ = spMap (Chart.dualMapR σ) ≫ (v.hom ≫ X.rm.act a).left`. Rewrite using `[Over.comp_left, Over.comp_left, Category.assoc, h.act a, ← Category.assoc, hv, Category.assoc]`.
-/
theorem lieCorr_smul {σ : R →+* R'} {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left} (h : X'.IsPullBy X (spMap σ) φ) {v : X.Lie} {v' : X'.Lie} (hv : LieCorr σ φ v v')
    (a : 𝓞 F) : LieCorr σ φ (a • v) (a • v') := by
  change (v'.hom ≫ X'.rm.act a).left ≫ φ = spMap (Chart.dualMapR σ) ≫ (v.hom ≫ X.rm.act a).left
  rw [Over.comp_left, Over.comp_left, Category.assoc, h.act a, ← Category.assoc, hv, Category.assoc]

/- English proof (translation)
Take `⟨e, he⟩` from `GlobalTheory.T.lie_algebra_base_change_iso (R := R) (R' := R') h`. Use `⟨e, he, fun a v ↦ ?_⟩` and prove the remaining obligations. Conclude with `((he _ _).1 (lieCorr_smul h ((he v _).2 rfl) a)).symm`.
-/
theorem exists_lieEquiv [Algebra R R'] {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left} (h : X'.IsPullBy X (spMap (algebraMap R R')) φ) :
    ∃ e : R' ⊗[R] X.Lie ≃ₗ[R'] X'.Lie, (∀ v v', LieCorr (algebraMap R R') φ v v' ↔ v' = e (1 ⊗ₜ v)) ∧
      ∀ (a : 𝓞 F) (v : X.Lie), e (1 ⊗ₜ (a • v)) = a • e (1 ⊗ₜ v) := by
  obtain ⟨e, he⟩ := GlobalTheory.T.lie_algebra_base_change_iso (R := R) (R' := R') h
  refine ⟨e, he, fun a v ↦ ?_⟩
  exact ((he _ _).1 (lieCorr_smul h ((he v _).2 rfl) a)).symm

/- English proof (translation)
Use `letI := σ.toAlgebra`. Take `⟨e, he, -⟩` from `exists_lieEquiv (R' := R') h`. Take `⟨hfin, hproj, -⟩` from `GlobalTheory.T.lie_algebra_finite_projective_rank X`. Establish `key : ∀ δ' : X'.DetOmega, DetCorr σ φ δ.1 δ' ↔ ∀ v : Fin (Module.finrank ℚ F) → X.Lie, δ' (fun i ↦ e (1 ⊗ₜ v i)) = algebraMap R R' (δ.1 v)` using `fun δ' ↦ by`. Use `⟨fun H v ↦ H v _ fun i ↦ (he _ _).2 rfl, fun H v v' hv ↦ ?_⟩` and prove the remaining obligations.

Take `rfl : v' = fun i ↦ e (1 ⊗ₜ v i)` from `funext fun i ↦ (he _ _).1 (hv i)`. Conclude with `H v`. Take `⟨δ', ⟨hs, hv⟩, hu⟩` from `GlobalTheory.T.exists_unique_base_change_volume_form R R' X.Lie X'.Lie e _ δ.1 δ.2`. Use `⟨⟨δ', hs⟩, (key δ').2 hv, fun δ'' hδ'' ↦ Subtype.ext (hu δ''.1 ⟨δ''.2, (key δ''.1).1 hδ''⟩)⟩` and prove the remaining obligations.
-/
theorem IsPullBy.existsUnique_detGen (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left} (h : X'.IsPullBy X (spMap σ) φ) (δ : X.DetGen) :
    ∃! δ' : X'.DetGen, DetCorr σ φ δ.1 δ'.1 := by
  letI := σ.toAlgebra
  obtain ⟨e, he, -⟩ := exists_lieEquiv (R' := R') h
  obtain ⟨hfin, hproj, -⟩ := GlobalTheory.T.lie_algebra_finite_projective_rank X
  have key : ∀ δ' : X'.DetOmega, DetCorr σ φ δ.1 δ' ↔ ∀ v : Fin (Module.finrank ℚ F) → X.Lie,
      δ' (fun i ↦ e (1 ⊗ₜ v i)) = algebraMap R R' (δ.1 v) := fun δ' ↦ by
    refine ⟨fun H v ↦ H v _ fun i ↦ (he _ _).2 rfl, fun H v v' hv ↦ ?_⟩
    obtain rfl : v' = fun i ↦ e (1 ⊗ₜ v i) := funext fun i ↦ (he _ _).1 (hv i)
    exact H v
  obtain ⟨δ', ⟨hs, hv⟩, hu⟩ := GlobalTheory.T.exists_unique_base_change_volume_form R R' X.Lie X'.Lie e _ δ.1 δ.2
  refine ⟨⟨δ', hs⟩, (key δ').2 hv, fun δ'' hδ'' ↦ Subtype.ext (hu δ''.1 ⟨δ''.2, (key δ''.1).1 hδ''⟩)⟩

/- English proof (translation)
Take `⟨hfin, hproj, hrk⟩` from `GlobalTheory.T.lie_algebra_finite_projective_rank X`. Conclude with `GlobalTheory.T.top_exterior_dual_invertible R X.Lie _ hrk`.
-/
theorem invertible_detOmega (X : Obj F 𝔠 (Sp R)) : Module.Invertible R X.DetOmega := by
  obtain ⟨hfin, hproj, hrk⟩ := GlobalTheory.T.lie_algebra_finite_projective_rank X
  exact GlobalTheory.T.top_exterior_dual_invertible R X.Lie _ hrk

/- English proof (translation)
Use `letI := σ.toAlgebra`. Take `⟨e, -, he⟩` from `exists_lieEquiv (R' := R') h`. Conclude with `GlobalTheory.T.base_change_module_tensor_action R R' (𝓞 F) X.Lie X'.Lie e he hX`.
-/
theorem IsPullBy.isRapoport (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left} (h : X'.IsPullBy X (spMap σ) φ) (hX : X.IsRapoport) : X'.IsRapoport := by
  letI := σ.toAlgebra
  obtain ⟨e, -, he⟩ := exists_lieEquiv (R' := R') h
  exact GlobalTheory.T.base_change_module_tensor_action R R' (𝓞 F) X.Lie X'.Lie e he hX

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hX`. Use `Set.eq_univ_of_forall fun s K _ t _ Y φ hY ↦ ?_` and prove the remaining obligations. Take `⟨σ, rfl⟩ : ∃ σ : R →+* K, spMap σ = t` from `⟨(Spec.preimage t).hom, Spec.map_preimage t⟩`. Conclude with `hY.isRapoport σ hX`.

Introduce `hX`. Take `⟨hfin, hproj, -⟩` from `GlobalTheory.T.lie_algebra_finite_projective_rank X`. Use `GlobalTheory.T.module_action_of_field_fibres R (𝓞 F) X.Lie fun K _ _ ↦ ?_` and prove the remaining obligations. Take `⟨Y, φ, hY⟩` from `exists_isPullBy X (spMap (algebraMap R K))`. Take `⟨x⟩ : Nonempty (Sp K)` from `inferInstance`.

Establish `hYr : Y.IsRapoport` using `(hX ▸ Set.mem_univ (spMap (algebraMap R K) x) : _ ∈ X.rapLocus) K _ ⟨x, rfl⟩ Y φ hY`. Take `⟨e, -, he⟩` from `exists_lieEquiv (R' := K) hY`. Conclude with `⟨Y.Lie, _, _, _, _, e, he, hYr⟩`.
-/
theorem isRapoport_iff (X : Obj F 𝔠 (Sp R)) : X.IsRapoport ↔ X.rapLocus = Set.univ := by
  constructor
  · intro hX
    refine Set.eq_univ_of_forall fun s K _ t _ Y φ hY ↦ ?_
    obtain ⟨σ, rfl⟩ : ∃ σ : R →+* K, spMap σ = t := ⟨(Spec.preimage t).hom, Spec.map_preimage t⟩
    exact hY.isRapoport σ hX
  · intro hX
    obtain ⟨hfin, hproj, -⟩ := GlobalTheory.T.lie_algebra_finite_projective_rank X
    refine GlobalTheory.T.module_action_of_field_fibres R (𝓞 F) X.Lie fun K _ _ ↦ ?_
    obtain ⟨Y, φ, hY⟩ := exists_isPullBy X (spMap (algebraMap R K))
    obtain ⟨x⟩ : Nonempty (Sp K) := inferInstance
    have hYr : Y.IsRapoport := (hX ▸ Set.mem_univ (spMap (algebraMap R K) x) : _ ∈ X.rapLocus) K _ ⟨x, rfl⟩ Y φ hY
    obtain ⟨e, -, he⟩ := exists_lieEquiv (R' := K) hY
    exact ⟨Y.Lie, _, _, _, _, e, he, hYr⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨exists_isPullBy, fun h' h ↦ h'.comp h, fun h h' ↦ h.cancel h', fun h _ α ↦ h.exists_level α, fun σ _ _ _ h ↦ ⟨h.existsUnique_detGen σ, invertible_detOmega _, h.isRapoport σ⟩, isRapoport_iff⟩`.
-/
theorem pullback_facts :
    (∀ {S S' : Scheme.{0}} (X : Obj F 𝔠 S) (b : S' ⟶ S), ∃ (X' : Obj F 𝔠 S') (φ : X'.A.left ⟶ X.A.left),
      X'.IsPullBy X b φ) ∧
    (∀ {S S' S'' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {X'' : Obj F 𝔠 S''}
      {b : S' ⟶ S} {b' : S'' ⟶ S'} {φ : X'.A.left ⟶ X.A.left} {ψ : X''.A.left ⟶ X'.A.left},
      X''.IsPullBy X' b' ψ → X'.IsPullBy X b φ → X''.IsPullBy X (b' ≫ b) (ψ ≫ φ)) ∧
    (∀ {S S' S'' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {X'' : Obj F 𝔠 S''}
      {b : S' ⟶ S} {b' : S'' ⟶ S'} {φ : X'.A.left ⟶ X.A.left} {χ : X''.A.left ⟶ X.A.left},
      X''.IsPullBy X (b' ≫ b) χ → X'.IsPullBy X b φ →
      ∃ ψ : X''.A.left ⟶ X'.A.left, X''.IsPullBy X' b' ψ ∧ ψ ≫ φ = χ) ∧
    (∀ {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {b : S' ⟶ S} {φ : X'.A.left ⟶ X.A.left},
      X'.IsPullBy X b φ → ∀ {N : ℕ} (α : X.Level N), ∃ α' : X'.Level N, IsLevelPull α' α b) ∧
    (∀ {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
      {φ : X'.A.left ⟶ X.A.left}, X'.IsPullBy X (spMap σ) φ →
      (∀ δ : X.DetGen, ∃! δ' : X'.DetGen, DetCorr σ φ δ.1 δ'.1) ∧ Module.Invertible R X.DetOmega ∧
        (X.IsRapoport → X'.IsRapoport)) ∧
    (∀ {R : Type} [CommRing R] (X : Obj F 𝔠 (Sp R)), X.IsRapoport ↔ X.rapLocus = Set.univ) :=
  ⟨exists_isPullBy, fun h' h ↦ h'.comp h, fun h h' ↦ h.cancel h', fun h _ α ↦ h.exists_level α,
    fun σ _ _ _ h ↦ ⟨h.existsUnique_detGen σ, invertible_detOmega _, h.isRapoport σ⟩, isRapoport_iff⟩

end GlobalTheory.RealMult.Obj
