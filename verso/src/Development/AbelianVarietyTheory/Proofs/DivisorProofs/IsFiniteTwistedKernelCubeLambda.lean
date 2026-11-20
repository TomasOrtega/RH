import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistKerFinite

/- English proof (translation)
Rewrite using `[evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst, lift_snd]`.
-/
theorem evc_lam {S : Scheme.{0}} {A Y : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (hP : (abelian₂ A L).IsLB)
    (x y : Y ⟶ A) : evc hP x y = lam (cls L hL) x y := by
  rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
    lift_snd]

/- English proof (translation)
Establish `hP : (abelian₂ A L).IsLB` using `LB.isLB_linComb hL _ _`. Establish `e` using `((same_iff hP hN a t).1 h₁).trans ((same_iff hP hN a' t).1 h₂).symm`. Rewrite `e` using `[evc_lam hL hP, evc_lam hL hP]`. Establish `e'` using `congrArg (CechPic.pull (lift (a⁻¹ * a'⁻¹) (𝟙 Y)).left) e`. Simplify using `only [pull_lam, lift_fst, lift_snd_assoc, Category.id_comp] at e'`.

Simplify using `only [lam] at e'`. Rewrite `e'` using `[show a⁻¹ * a'⁻¹ * a = a'⁻¹ by rw [mul_right_comm, inv_mul_cancel, _root_.one_mul], show a⁻¹ * a'⁻¹ * a' = a⁻¹ from inv_mul_cancel_right _ _]`. Take the linear combination `(norm := abel) e'.symm`.
-/
theorem add_inv_eq_of_same {S : Scheme.{0}} {A T Y : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}
    (hL : L.IsLB) {N : LB (A ⊗ T).left} (hN : N.IsLB) (a a' : Y ⟶ A) (t : Y ⟶ T)
    (h₁ : Same A (abelian₂ A L) N a t) (h₂ : Same A (abelian₂ A L) N a' t) :
    CechPic.pull a.left (cls L hL) + CechPic.pull (a⁻¹).left (cls L hL) =
      CechPic.pull a'.left (cls L hL) + CechPic.pull (a'⁻¹).left (cls L hL) := by
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have e := ((same_iff hP hN a t).1 h₁).trans ((same_iff hP hN a' t).1 h₂).symm
  rw [evc_lam hL hP, evc_lam hL hP] at e
  have e' := congrArg (CechPic.pull (lift (a⁻¹ * a'⁻¹) (𝟙 Y)).left) e
  simp only [pull_lam, lift_fst, lift_snd_assoc, Category.id_comp] at e'
  simp only [lam] at e'
  rw [show a⁻¹ * a'⁻¹ * a = a'⁻¹ by rw [mul_right_comm, inv_mul_cancel, _root_.one_mul],
    show a⁻¹ * a'⁻¹ * a' = a⁻¹ from inv_mul_cancel_right _ _] at e'
  linear_combination (norm := abel) e'.symm

/- English proof (translation)
Introduce `R _ _ A _ hB L hL hA T _ _ N hN H h hh hH`. Use `haveI := hB.comm`. Use `hB.proper` as an intermediate fact. Take `⟨d, -, n, s, hc, ha⟩` from `(GlobalTheory.Unif.relAmple_iff_veryAmpleBy R A L hL).1 hA`. Establish `hAT : IsPullback (fst A T).left (snd A T).left A.hom T.hom` using `IsPullback.of_hasPullback A.hom T.hom`.

Establish `: IsProper (snd A T).left` using `MorphismProperty.of_isPullback hAT inferInstance`. Establish `: IsAffineHom (fst A T).left` using `MorphismProperty.of_isPullback hAT.flip inferInstance`. Set `f : H.left ⟶ T.left` to `(h ≫ snd A T).left`. Establish `hf : f ≫ T.hom = H.hom` using `Over.w (h ≫ snd A T)`. Establish `: IsProper f` using `inferInstanceAs (IsProper (h.left ≫ (snd A T).left))`.

Express the relevant statement in the definitionally equal form `IsFinite f`. It suffices to establish `LocallyQuasiFinite f from .of_isProper_of_locallyQuasiFinite _`. Use `LocallyQuasiFinite.of_finite_preimage_singleton _ fun z => ?_` and prove the remaining obligations. Break down `Set.eq_empty_or_nonempty (f ⁻¹' {z}) with h0 | ⟨x₀, hx₀⟩` into its components or cases. Rewrite using `[h0]`.

Conclude with `Set.finite_empty`. Set `K : Type` to `H.left.residueField x₀`. Set `y₀ : Spec (CommRingCat.of K) ⟶ H.left` to `H.left.fromSpecResidueField x₀`. Set `g : Spec (CommRingCat.of K) ⟶ T.left` to `y₀ ≫ f`. Set `π : pullback f g ⟶ H.left` to `pullback.fst f g`.

Set `q : pullback f g ⟶ Spec (CommRingCat.of K)` to `pullback.snd f g`. Set `Z : Scheme.{0}` to `pullback f g`. Establish `hpb : IsPullback π q f g` using `IsPullback.of_hasPullback f g`. Establish `: IsProper q` using `MorphismProperty.of_isPullback hpb inferInstance`. Establish `: IsAffineHom π` using `MorphismProperty.of_isPullback hpb.flip inferInstance`.

Set `P : Over (Sp R)` to `Over.mk (y₀ ≫ H.hom)`. Set `Q : Over (Sp R)` to `Over.mk (π ≫ H.hom)`. Set `yo : P ⟶ H` to `Over.homMk y₀ rfl`. Set `qo : Q ⟶ P` to `Over.homMk q (by show q ≫ y₀ ≫ H.hom = π ≫ H.hom`. Rewrite using `[← hf, ← Category.assoc π, hpb.w]`.

Simplify using `only [g, Category.assoc])`. Set `p₁ : Q ⟶ H` to `Over.homMk π rfl`. Establish `hpt : p₁ ≫ h ≫ snd A T = qo ≫ yo ≫ h ≫ snd A T`. Use `ext`. Conclude with `hpb.w`.

Set `w : H ⟶ A` to `h ≫ fst A T`. Apply the tactic sequence `have hs₁ : Same A (abelian₂ A L) N (p₁ ≫ w) (p₁ ≫ h ≫ snd A T) := (hH _ _ _).2 ⟨p₁, by ext <;> simp [w]⟩`. Establish `hs₂ : Same A (abelian₂ A L) N (qo ≫ yo ≫ w) (p₁ ≫ h ≫ snd A T)`. Rewrite using `[hpt]`. Apply the tactic sequence `exact (hH _ _ _).2 ⟨qo ≫ yo, by ext <;> simp [w]⟩`.

Establish `key` using `add_inv_eq_of_same hL hN.isLB _ _ _ hs₁ hs₂`. Rewrite `key` using `[← GrpObj.comp_inv qo, Over.comp_left _ _ _ qo, Over.comp_left _ _ _ qo, pull_comp qo.left, pull_comp qo.left, GlobalTheory.AmpleStabFinite.pull_spec_local (K := K) (yo ≫ w).left, GlobalTheory.AmpleStabFinite.pull_spec_local (K := K) (yo ≫ w)⁻¹.left, map_zero, add_zero]`. Establish `: CompactSpace Z` using `QuasiCompact.compactSpace_of_compactSpace q`. Establish `: IsAffineHom (p₁ ≫ w).left` using `inferInstanceAs (IsAffineHom (π ≫ h.left ≫ (fst A T).left))`. Establish `: Z.IsQuasiAffine` using `GlobalTheory.AmpleStabFinite.quasiAffine_of_pull_add (p₁ ≫ w).left ((p₁ ≫ w)⁻¹).left (isLB_pw hL d) s hc (fun i => (ha i).1) (by`.

Rewrite using `[GlobalTheory.AmpleStabFinite.cls_pw hL, map_zsmul, map_zsmul, ← zsmul_add]`. Conclude with `(congrArg _ key).trans (zsmul_zero _))`. Establish `: IsAffine Z` using `GlobalTheory.AmpleStabFinite.isAffine_of_quasiAffine q`. Establish `: IsFinite q` using `IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩`. Establish `hfin : (Set.univ : Set Z).Finite`.

Use `q.finite_preimage_singleton (IsLocalRing.closedPoint K)` as an intermediate fact. Use `this.subset fun t _ => Subsingleton.elim _ _` and prove the remaining obligations. Use `(hfin.image π).subset fun v hv => ?_` and prove the remaining obligations. Establish `e : f v = g (IsLocalRing.closedPoint K)`. Establish `e₀ : y₀ (IsLocalRing.closedPoint K) = x₀` using `Scheme.fromSpecResidueField_apply x₀ _`.

Conclude with `(show f v = z from hv).trans ((show f x₀ = z from hx₀).symm.trans (congrArg f e₀).symm)`. Take `⟨t, ht, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) v _ e`. Conclude with `⟨t, trivial, ht⟩`.
-/
theorem isFinite_twisted_kernel : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ N : LB (A ⊗ T).left, Fam A N → ∀ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t) → IsFinite (h ≫ snd A T).left := by
  intro R _ _ A _ hB L hL hA T _ _ N hN H h hh hH
  haveI := hB.comm
  have := hB.proper
  obtain ⟨d, -, n, s, hc, ha⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R A L hL).1 hA
  have hAT : IsPullback (fst A T).left (snd A T).left A.hom T.hom := IsPullback.of_hasPullback A.hom T.hom
  have : IsProper (snd A T).left := MorphismProperty.of_isPullback hAT inferInstance
  have : IsAffineHom (fst A T).left := MorphismProperty.of_isPullback hAT.flip inferInstance
  let f : H.left ⟶ T.left := (h ≫ snd A T).left
  have hf : f ≫ T.hom = H.hom := Over.w (h ≫ snd A T)
  have : IsProper f := inferInstanceAs (IsProper (h.left ≫ (snd A T).left))
  change IsFinite f
  suffices LocallyQuasiFinite f from .of_isProper_of_locallyQuasiFinite _
  refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun z => ?_
  rcases Set.eq_empty_or_nonempty (f ⁻¹' {z}) with h0 | ⟨x₀, hx₀⟩
  · rw [h0]; exact Set.finite_empty
  let K : Type := H.left.residueField x₀
  let y₀ : Spec (CommRingCat.of K) ⟶ H.left := H.left.fromSpecResidueField x₀
  let g : Spec (CommRingCat.of K) ⟶ T.left := y₀ ≫ f
  let π : pullback f g ⟶ H.left := pullback.fst f g
  let q : pullback f g ⟶ Spec (CommRingCat.of K) := pullback.snd f g
  let Z : Scheme.{0} := pullback f g
  have hpb : IsPullback π q f g := IsPullback.of_hasPullback f g
  have : IsProper q := MorphismProperty.of_isPullback hpb inferInstance
  have : IsAffineHom π := MorphismProperty.of_isPullback hpb.flip inferInstance
  let P : Over (Sp R) := Over.mk (y₀ ≫ H.hom)
  let Q : Over (Sp R) := Over.mk (π ≫ H.hom)
  let yo : P ⟶ H := Over.homMk y₀ rfl
  let qo : Q ⟶ P := Over.homMk q (by
    show q ≫ y₀ ≫ H.hom = π ≫ H.hom
    rw [← hf, ← Category.assoc π, hpb.w]
    simp only [g, Category.assoc])
  let p₁ : Q ⟶ H := Over.homMk π rfl
  have hpt : p₁ ≫ h ≫ snd A T = qo ≫ yo ≫ h ≫ snd A T := by
    ext
    exact hpb.w
  let w : H ⟶ A := h ≫ fst A T
  have hs₁ : Same A (abelian₂ A L) N (p₁ ≫ w) (p₁ ≫ h ≫ snd A T) :=
    (hH _ _ _).2 ⟨p₁, by ext <;> simp [w]⟩
  have hs₂ : Same A (abelian₂ A L) N (qo ≫ yo ≫ w) (p₁ ≫ h ≫ snd A T) := by
    rw [hpt]
    exact (hH _ _ _).2 ⟨qo ≫ yo, by ext <;> simp [w]⟩
  have key := add_inv_eq_of_same hL hN.isLB _ _ _ hs₁ hs₂
  rw [← GrpObj.comp_inv qo, Over.comp_left _ _ _ qo, Over.comp_left _ _ _ qo, pull_comp qo.left,
    pull_comp qo.left, GlobalTheory.AmpleStabFinite.pull_spec_local (K := K) (yo ≫ w).left,
    GlobalTheory.AmpleStabFinite.pull_spec_local (K := K) (yo ≫ w)⁻¹.left, map_zero, add_zero] at key
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace q
  have : IsAffineHom (p₁ ≫ w).left := inferInstanceAs (IsAffineHom (π ≫ h.left ≫ (fst A T).left))
  have : Z.IsQuasiAffine := GlobalTheory.AmpleStabFinite.quasiAffine_of_pull_add (p₁ ≫ w).left ((p₁ ≫ w)⁻¹).left
    (isLB_pw hL d) s hc (fun i => (ha i).1) (by
      rw [GlobalTheory.AmpleStabFinite.cls_pw hL, map_zsmul, map_zsmul, ← zsmul_add]
      exact (congrArg _ key).trans (zsmul_zero _))
  have : IsAffine Z := GlobalTheory.AmpleStabFinite.isAffine_of_quasiAffine q
  have : IsFinite q := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  have hfin : (Set.univ : Set Z).Finite := by
    have := q.finite_preimage_singleton (IsLocalRing.closedPoint K)
    refine this.subset fun t _ => Subsingleton.elim _ _
  refine (hfin.image π).subset fun v hv => ?_
  have e : f v = g (IsLocalRing.closedPoint K) := by
    have e₀ : y₀ (IsLocalRing.closedPoint K) = x₀ := Scheme.fromSpecResidueField_apply x₀ _
    exact (show f v = z from hv).trans ((show f x₀ = z from hx₀).symm.trans (congrArg f e₀).symm)
  obtain ⟨t, ht, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) v _ e
  exact ⟨t, trivial, ht⟩

end GlobalTheory.TwistKerFinite
