import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCocCocOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorContractionTwoCochainProduct
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PreimageEqTopOfSurjective

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.ChernContr

section Dl

variable {R : Type} [CommRing R] {D D' : Type} [CommRing D] [CommRing D']

/- English proof (translation)
Take `⟨a, ha⟩` from `hu`. Take `⟨b, hb⟩` from `hu'`. Establish `e1 : (↑a : D) * ↑a⁻¹ = 1` using `Units.mul_inv a`. Establish `e2 : (↑b : D) * ↑b⁻¹ = 1` using `Units.mul_inv b`. Establish `e3 : Ring.inverse ((↑a : D) * ↑b) = ↑b⁻¹ * ↑a⁻¹`.

Rewrite using `[← Units.val_mul, Ring.inverse_unit, mul_inv_rev, Units.val_mul]`. Simplify using `only [dl, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, ← ha, ← hb, e3, Ring.inverse_unit, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]`. Take the linear combination `(u'.snd * ↑b⁻¹) * e1 + (u.snd * ↑a⁻¹) * e2`.
-/
theorem dl_mul (u u' : DualNumber D) (hu : IsUnit u.fst) (hu' : IsUnit u'.fst) :
    dl (u * u') = dl u + dl u' := by
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := hu'
  have e1 : (↑a : D) * ↑a⁻¹ = 1 := Units.mul_inv a
  have e2 : (↑b : D) * ↑b⁻¹ = 1 := Units.mul_inv b
  have e3 : Ring.inverse ((↑a : D) * ↑b) = ↑b⁻¹ * ↑a⁻¹ := by
    rw [← Units.val_mul, Ring.inverse_unit, mul_inv_rev, Units.val_mul]
  simp only [dl, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, ← ha, ← hb, e3,
    Ring.inverse_unit, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  linear_combination (u'.snd * ↑b⁻¹) * e1 + (u.snd * ↑a⁻¹) * e2

/- English proof (translation)
Simplify using `[dl, h]`.
-/
theorem dl_one_add (l : DualNumber D) (h : l.fst = 0) : dl (1 + l) = l.snd := by
  simp [dl, h]

/- English proof (translation)
Simplify using `[dl]`.
-/
theorem dl_one : dl (1 : DualNumber D) = 0 := by
  simp [dl]

/- English proof (translation)
Simplify using `[dl]`.
-/
theorem dl_inl (c : D) : dl (TrivSqZeroExt.inl c : DualNumber D) = 0 := by
  simp [dl]

/- English proof (translation)
Simplify using `[epsHom, DualNumber.lift_apply_apply]`.
-/
theorem fst_epsHom [Algebra R D] [Algebra R D'] (φ : D →ₐ[R] D') (z : DualNumber D) :
    (epsHom φ z).fst = φ z.fst := by
  simp [epsHom, DualNumber.lift_apply_apply]

/- English proof (translation)
Simplify using `[epsHom, DualNumber.lift_apply_apply]`.
-/
theorem snd_epsHom' [Algebra R D] [Algebra R D'] (φ : D →ₐ[R] D') (z : DualNumber D) :
    (epsHom φ z).snd = φ z.snd := by
  simp [epsHom, DualNumber.lift_apply_apply]

/- English proof (translation)
Take `⟨a, ha⟩` from `hz`. Establish `e : Ring.inverse (φ (a : D)) = φ (↑a⁻¹ : D)`. Rewrite using `[show φ (a : D) = ((Units.map (φ : D →* D') a : D'ˣ) : D') from rfl, Ring.inverse_unit]`. Both sides reduce to the same expression. Simplify using `only [dl, fst_epsHom, snd_epsHom', ← ha, e, Ring.inverse_unit, map_mul]`.
-/
theorem dl_epsHom [Algebra R D] [Algebra R D'] (φ : D →ₐ[R] D') (z : DualNumber D) (hz : IsUnit z.fst) :
    dl (epsHom φ z) = φ (dl z) := by
  obtain ⟨a, ha⟩ := hz
  have e : Ring.inverse (φ (a : D)) = φ (↑a⁻¹ : D) := by
    rw [show φ (a : D) = ((Units.map (φ : D →* D') a : D'ˣ) : D') from rfl, Ring.inverse_unit]
    rfl
  simp only [dl, fst_epsHom, snd_epsHom', ← ha, e, Ring.inverse_unit, map_mul]

/- English proof (translation)
Establish `e` using `congrArg dl h`. Rewrite `e` using `[dl_mul _ _ (by simp [hl]) hc, dl_mul _ _ ha hb, dl_one_add _ hl]`. Take the linear combination `e`.
-/
theorem snd_of_exp (l a b c : DualNumber D) (hl : l.fst = 0) (ha : IsUnit a.fst) (hb : IsUnit b.fst)
    (hc : IsUnit c.fst) (h : (1 + l) * c = a * b) : l.snd = dl a + dl b - dl c := by
  have e := congrArg dl h
  rw [dl_mul _ _ (by simp [hl]) hc, dl_mul _ _ ha hb, dl_one_add _ hl] at e
  linear_combination e

/- English proof (translation)
The claim follows from `h.map (TrivSqZeroExt.fstHom D D D)`.
-/
theorem isUnit_fst {u : DualNumber D} (h : IsUnit u) : IsUnit u.fst := h.map (TrivSqZeroExt.fstHom D D D)

end Dl

section Pts

variable {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

/- English proof (translation)
Rewrite using `[← Over.comp_left, pt0, AbDual.inl, comp_lift, Category.comp_id, MonObj.comp_one]`.
-/
theorem pointWithZeroSecondCoord_left {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) :
    (pt0 B x).left = x.left ≫ (AbDual.inl A B).left := by
  rw [← Over.comp_left, pt0, AbDual.inl, comp_lift, Category.comp_id, MonObj.comp_one]

/- English proof (translation)
Rewrite using `[pointWithZeroSecondCoord_left, Scheme.Hom.comp_preimage]`. Conclude with `h`.
-/
theorem pointWithZeroSecondCoord_mem_chart_of_restricted (P : LB (A ⊗ B).left) {D : Type} [CommRing D] [Algebra R D] {x : Pt A D} {c : P.ι}
    (h : ⊤ ≤ x.left ⁻¹ᵁ chartsA P c) : ⊤ ≤ (pt0 B x).left ⁻¹ᵁ P.U c := by
  rw [pointWithZeroSecondCoord_left, Scheme.Hom.comp_preimage]
  exact h

/- English proof (translation)
Establish `hsurj : Surjective (spOver (TrivSqZeroExt.fstHom R D D)).left`. Rewrite using `[spOver_left]`. Use `GlobalTheory.TorusLift.surjective_specMap _ (fun a ↦ ⟨TrivSqZeroExt.inl a, rfl⟩) ⟨2, ?_⟩` and prove the remaining obligations. Rewrite using `[sq, Ideal.zero_eq_bot, eq_bot_iff]`. Use `Ideal.mul_le.2 fun a ha b hb ↦ ?_` and prove the remaining obligations.

Establish `ha' : a.fst = 0` using `ha`. Establish `hb' : b.fst = 0` using `hb`. Rewrite using `[Ideal.mem_bot]`. Apply the tactic sequence `ext <;> simp [ha', hb']`. Establish `e : (spOver (TrivSqZeroExt.fstHom R D D) ≫ ptV v x).left = (pt0 B x).left`.

Rewrite using `[ContrMor.spOver_fst_ptV v hv x]`. Use `GlobalTheory.TorusLift.preimage_eq_top_of_surjective (spOver (TrivSqZeroExt.fstHom R D D)).left (ptV v x).left (U := P.U c) (by` as an intermediate fact. Rewrite using `[← Over.comp_left, e]`. Conclude with `top_unique (pointWithZeroSecondCoord_mem_chart_of_restricted P h))`. Conclude with `this.ge`.
-/
theorem ptV_mem (P : LB (A ⊗ B).left) {v : epsR R ⟶ B} (hv : IsTangent v) {D : Type} [CommRing D]
    [Algebra R D] {x : Pt A D} {c : P.ι} (h : ⊤ ≤ x.left ⁻¹ᵁ chartsA P c) : ⊤ ≤ (ptV v x).left ⁻¹ᵁ P.U c := by
  have hsurj : Surjective (spOver (TrivSqZeroExt.fstHom R D D)).left := by
    rw [spOver_left]
    refine GlobalTheory.TorusLift.surjective_specMap _ (fun a ↦ ⟨TrivSqZeroExt.inl a, rfl⟩) ⟨2, ?_⟩
    rw [sq, Ideal.zero_eq_bot, eq_bot_iff]
    refine Ideal.mul_le.2 fun a ha b hb ↦ ?_
    have ha' : a.fst = 0 := ha
    have hb' : b.fst = 0 := hb
    rw [Ideal.mem_bot]
    ext <;> simp [ha', hb']
  have e : (spOver (TrivSqZeroExt.fstHom R D D) ≫ ptV v x).left = (pt0 B x).left := by
    rw [ContrMor.spOver_fst_ptV v hv x]
  have := GlobalTheory.TorusLift.preimage_eq_top_of_surjective (spOver (TrivSqZeroExt.fstHom R D D)).left
    (ptV v x).left (U := P.U c) (by
      rw [← Over.comp_left, e]
      exact top_unique (pointWithZeroSecondCoord_mem_chart_of_restricted P h))
  exact this.ge

end Pts

section Ev

variable {X : Scheme.{0}}

/- English proof (translation)
Simplify using `only [evalAt, RingHom.comp_apply]`. Use `congr 1`. Rewrite using `[← CommRingCat.comp_apply, Scheme.Hom.map_appLE]`.
-/
theorem evalAt_res' {C : Type} [CommRing C] (x : Sp C ⟶ X) {V U : X.Opens} (hVU : V ≤ U)
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    evalAt x U hU f = evalAt x V hV ((X.presheaf.map (homOfLE hVU).op).hom f) := by
  simp only [evalAt, RingHom.comp_apply]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

/- English proof (translation)
Substitute `e` using the available equality. Establish `e : (spMap φ ≫ x).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of C')).hom = x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom ≫ CommRingCat.ofHom φ`. Rewrite using `[← Scheme.ΓSpecIso_naturality, ← Category.assoc, ← Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h le_rfl]`. Use `congr 2`. Conclude with `(congrArg (fun t ↦ t.hom f) e).symm`.
-/
theorem evalAt_spMap' {C C' : Type} [CommRing C] [CommRing C'] (φ : C →+* C') (x : Sp C ⟶ X)
    (x' : Sp C' ⟶ X) (e : spMap φ ≫ x = x') {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x' ⁻¹ᵁ U)
    (f : Γ(X, U)) : φ (evalAt x U h f) = evalAt x' U h' f := by
  subst e
  have e : (spMap φ ≫ x).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of C')).hom =
      x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom ≫ CommRingCat.ofHom φ := by
    rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc,
      ← Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h le_rfl]
    congr 2
  exact (congrArg (fun t ↦ t.hom f) e).symm

abbrev gv (L : LB X) {C : Type} [CommRing C] (x : Sp C ⟶ X) (a b : L.ι) : C :=
  evU x (L.U a ⊓ L.U b) (L.g a b).val

/- English proof (translation)
The claim follows from `dif_pos h`.
-/
theorem gv_eq (L : LB X) {C : Type} [CommRing C] (x : Sp C ⟶ X) {a b : L.ι}
    (h : ⊤ ≤ x ⁻¹ᵁ (L.U a ⊓ L.U b)) : gv L x a b = evalAt x (L.U a ⊓ L.U b) h (L.g a b).val := dif_pos h

/- English proof (translation)
Rewrite using `[gv_eq L x (le_inf ha hb)]`. Conclude with `(L.g a b).isUnit.map _`.
-/
theorem isUnit_gv (L : LB X) {C : Type} [CommRing C] (x : Sp C ⟶ X) {a b : L.ι}
    (ha : ⊤ ≤ x ⁻¹ᵁ L.U a) (hb : ⊤ ≤ x ⁻¹ᵁ L.U b) : IsUnit (gv L x a b) := by
  rw [gv_eq L x (le_inf ha hb)]
  exact (L.g a b).isUnit.map _

/- English proof (translation)
Establish `h₁ : ⊤ ≤ x ⁻¹ᵁ (L.U a ⊓ L.U b)` using `le_inf ha hb`. Establish `h₂ : ⊤ ≤ x ⁻¹ᵁ (L.U b ⊓ L.U c)` using `le_inf hb hc`. Establish `h₃ : ⊤ ≤ x ⁻¹ᵁ (L.U a ⊓ L.U c)` using `le_inf ha hc`. Establish `hW : ⊤ ≤ x ⁻¹ᵁ (L.U a ⊓ L.U b ⊓ L.U c)` using `le_inf h₁ hc`. Establish `e` using `congrArg (fun u : Γ(X, L.U a ⊓ L.U b ⊓ L.U c)ˣ ↦ evalAt x _ hW u.val) (hL.cocycle a b c)`.

Simplify using `only [Units.val_mul, map_mul] at e`. Rewrite using `[gv_eq L x h₁, gv_eq L x h₂, gv_eq L x h₃, evalAt_res' x inf_le_left h₁ hW, evalAt_res' x (le_inf (inf_le_left.trans inf_le_right) inf_le_right) h₂ hW, evalAt_res' x (le_inf (inf_le_left.trans inf_le_left) inf_le_right) h₃ hW]`. Conclude with `e`.
-/
theorem gv_cocycle (L : LB X) (hL : L.IsLB) {C : Type} [CommRing C] (x : Sp C ⟶ X) {a b c : L.ι}
    (ha : ⊤ ≤ x ⁻¹ᵁ L.U a) (hb : ⊤ ≤ x ⁻¹ᵁ L.U b) (hc : ⊤ ≤ x ⁻¹ᵁ L.U c) :
    gv L x a b * gv L x b c = gv L x a c := by
  have h₁ : ⊤ ≤ x ⁻¹ᵁ (L.U a ⊓ L.U b) := le_inf ha hb
  have h₂ : ⊤ ≤ x ⁻¹ᵁ (L.U b ⊓ L.U c) := le_inf hb hc
  have h₃ : ⊤ ≤ x ⁻¹ᵁ (L.U a ⊓ L.U c) := le_inf ha hc
  have hW : ⊤ ≤ x ⁻¹ᵁ (L.U a ⊓ L.U b ⊓ L.U c) := le_inf h₁ hc
  have e := congrArg (fun u : Γ(X, L.U a ⊓ L.U b ⊓ L.U c)ˣ ↦ evalAt x _ hW u.val) (hL.cocycle a b c)
  simp only [Units.val_mul, map_mul] at e
  rw [gv_eq L x h₁, gv_eq L x h₂, gv_eq L x h₃, evalAt_res' x inf_le_left h₁ hW,
    evalAt_res' x (le_inf (inf_le_left.trans inf_le_right) inf_le_right) h₂ hW,
    evalAt_res' x (le_inf (inf_le_left.trans inf_le_left) inf_le_right) h₃ hW]
  exact e

/- English proof (translation)
Establish `ka : ⊤ ≤ y' ⁻¹ᵁ L.U a`. Rewrite using `[← e]`. Conclude with `fun p _ ↦ ha (Set.mem_univ _)`. Establish `kb : ⊤ ≤ y' ⁻¹ᵁ L.U b`. Rewrite using `[← e]`.

Conclude with `fun p _ ↦ hb (Set.mem_univ _)`. Establish `e1` using `congrArg dl (gv_cocycle L hL y' hb' ha' ka)`. Establish `e2` using `congrArg dl (gv_cocycle L hL y' hb' kb ka)`. Rewrite `e1` using `[dl_mul _ _ (isUnit_fst (isUnit_gv L _ hb' ha')) (isUnit_fst (isUnit_gv L _ ha' ka))]`. Rewrite `e2` using `[dl_mul _ _ (isUnit_fst (isUnit_gv L _ hb' kb)) (isUnit_fst (isUnit_gv L _ kb ka))]`.

Establish `e3 : gv L y' b a = epsHom φ (gv L y b a)`. Rewrite using `[gv_eq L y' (le_inf kb ka), gv_eq L y (le_inf hb ha)]`. Conclude with `(evalAt_spMap' (epsHom φ : DualNumber D →+* DualNumber D') y y' e _ _ _).symm`. Rewrite `e2` using `[e3, dl_epsHom φ _ (isUnit_fst (isUnit_gv L _ hb ha))]`. Take the linear combination `e1 - e2`.
-/
theorem dl_gv {R : Type} [CommRing R] {D D' : Type} [CommRing D] [CommRing D'] [Algebra R D] [Algebra R D']
    (φ : D →ₐ[R] D') (L : LB X) (hL : L.IsLB) (y : Sp (DualNumber D) ⟶ X) (y' : Sp (DualNumber D') ⟶ X)
    (e : spMap (epsHom φ : DualNumber D →+* DualNumber D') ≫ y = y') {a b a' b' : L.ι}
    (ha : ⊤ ≤ y ⁻¹ᵁ L.U a) (hb : ⊤ ≤ y ⁻¹ᵁ L.U b) (ha' : ⊤ ≤ y' ⁻¹ᵁ L.U a') (hb' : ⊤ ≤ y' ⁻¹ᵁ L.U b') :
    dl (gv L y' a' a) = dl (gv L y' b' b) + φ (dl (gv L y b a)) - dl (gv L y' b' a') := by
  have ka : ⊤ ≤ y' ⁻¹ᵁ L.U a := by
    rw [← e]; exact fun p _ ↦ ha (Set.mem_univ _)
  have kb : ⊤ ≤ y' ⁻¹ᵁ L.U b := by
    rw [← e]; exact fun p _ ↦ hb (Set.mem_univ _)
  have e1 := congrArg dl (gv_cocycle L hL y' hb' ha' ka)
  have e2 := congrArg dl (gv_cocycle L hL y' hb' kb ka)
  rw [dl_mul _ _ (isUnit_fst (isUnit_gv L _ hb' ha')) (isUnit_fst (isUnit_gv L _ ha' ka))] at e1
  rw [dl_mul _ _ (isUnit_fst (isUnit_gv L _ hb' kb)) (isUnit_fst (isUnit_gv L _ kb ka))] at e2
  have e3 : gv L y' b a = epsHom φ (gv L y b a) := by
    rw [gv_eq L y' (le_inf kb ka), gv_eq L y (le_inf hb ha)]
    exact (evalAt_spMap' (epsHom φ : DualNumber D →+* DualNumber D') y y' e _ _ _).symm
  rw [e3, dl_epsHom φ _ (isUnit_fst (isUnit_gv L _ hb ha))] at e2
  linear_combination e1 - e2

end Ev

end GlobalTheory.PtExt.ChernContr

namespace GlobalTheory.PtExt.ChernContr
open ContrMor

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `R _ A B _ _ P hP v hv j hj w _ i hi U ℓ hU hℓ n hn κ hκ`. Establish `s0 : ∀ {D : Type} [CommRing D] [Algebra R D] {x : Pt A D}, Sm (chartsA P) x → Sm P.U (pt0 B x)` using `fun ⟨c, h⟩ ↦ ⟨c, pointWithZeroSecondCoord_mem_chart_of_restricted P h⟩`. Establish `sV : ∀ {D : Type} [CommRing D] [Algebra R D] {x : Pt A D}, Sm (chartsA P) x → Sm P.U (ptV v x)` using `fun ⟨c, h⟩ ↦ ⟨c, ptV_mem P hv h⟩`. Set `T0 : ∀ {D : Type} [CommRing D] [Algebra R D] {x : Pt A D}, Sm (chartsA P) x → SmallCat P.U` to `fun {_} _ _ {x} h ↦ ⟨trivAt (pt0 B x), s0 h⟩`. Set `TV : ∀ {D : Type} [CommRing D] [Algebra R D] {x : Pt A D}, Sm (chartsA P) x → SmallCat P.U` to `fun {_} _ _ {x} h ↦ ⟨trivAt (ptV v x), sV h⟩`.

Set `TT : ∀ {D : Type} [CommRing D] [Algebra R D] {x : Pt A D}, Sm (chartsA P) x → SmallCat P.U` to `fun {_} _ _ {x} h ↦ ⟨thickAt B x, s0 h⟩`. Set `sM : ∀ {D : Type} [CommRing D] [Algebra R D] {x : Pt A D} (h : Sm (chartsA P) x), T0 h ⟶ TT h` to `fun {_} _ _ {x} _ ↦ ObjectProperty.homMk (sHom x)`. Set `iM : ∀ {D : Type} [CommRing D] [Algebra R D] {x : Pt A D} (h : Sm (chartsA P) x), TV h ⟶ TT h` to `fun {_} _ _ {x} _ ↦ ObjectProperty.homMk (iHom v hv x)`. Set `k : ∀ {D : Type} [CommRing D] [Algebra R D] {x : Pt A D}, Sm (chartsA P) x → D` to `fun {D} _ _ {x} h ↦ TrivSqZeroExt.snd (R := D) (n _ _ (sM h)) - TrivSqZeroExt.snd (R := D) (n _ _ (iM h)) + (dl (U _ _ (sM h)) - dl (U _ _ (iM h))) + dl (gv P (ptV v x).left (j D x) (i (TV h)))`. Use `⟨fun D _ _ x ↦ if h : Sm (chartsA P) x then -k h else 0, ?_⟩` and prove the remaining obligations.

Introduce `D _ _ D' _ _ φ x hx`. Establish `hx' : Sm (chartsA P) (spOver φ ≫ x)` using `hx.map φ`. Simplify using `only [dif_pos hx, dif_pos hx', Fn1.add, Fn1.neg]`. Set `aM : T0 hx ⟶ T0 hx'` to `ObjectProperty.homMk (aHom φ x)`. Set `bM : TV hx ⟶ TV hx'` to `ObjectProperty.homMk (bHom v φ x)`.

Set `tM : TT hx ⟶ TT hx'` to `ObjectProperty.homMk (τHom φ x)`. Establish `c1 : sM hx ≫ tM = aM ≫ sM hx'` using `ObjectProperty.hom_ext _ (Thick.hom_ext fun r ↦ by`. Express the relevant statement in the definitionally equal form `epsHom φ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (φ r)`. Use `ext`. Conclude with `fst_epsHom φ _`.

Conclude with `(snd_epsHom' φ _).trans (map_zero φ))`. Establish `c2 : iM hx ≫ tM = bM ≫ iM hx'` using `ObjectProperty.hom_ext _ (Thick.hom_ext fun r ↦ rfl)`. Establish `uU : ∀ (S S' : SmallCat P.U) (f : S ⟶ S'), IsUnit (S'.obj.π (U S S' f))` using `fun S S' f ↦ by`. Rewrite using `[hU]`. Conclude with `(P.g _ _).isUnit.map _`.

Establish `key : ∀ (S S' : SmallCat P.U) (f : S ⟶ S') (g : S' ⟶ TT hx'), IsUnit (TrivSqZeroExt.fst (R` using `D') (M := D') (g.hom.φ (U _ _ f))) → TrivSqZeroExt.snd (R := D') (M := D') (w.1 _ _ _ f.hom g.hom) = TrivSqZeroExt.snd (R := D') (M := D') (g.hom.φ (n _ _ f)) - TrivSqZeroExt.snd (R := D') (M := D') (n _ _ (f ≫ g)) + TrivSqZeroExt.snd (R := D') (M := D') (n _ _ g) + (dl (D := D') …`. Introduce `S S' f g hu`. Take `⟨hm, he⟩` from `hℓ S S' (TT hx') f g`. Establish `e1 : dpExp (TT hx').obj.δ (ℓ.1 _ _ _ f g) = @HAdd.hAdd (DualNumber D') (DualNumber D') (DualNumber D') _ 1 (ℓ.1 _ _ _ f g)` using `dpExp_sqDP (epsExt R D').sq hm`. Establish `e2` using `snd_of_exp (D := D') (ℓ.1 _ _ _ f g) (g.hom.φ (U _ _ f)) (U _ _ g) (U _ _ (f ≫ g)) hm hu (uU _ _ g) (uU _ _ (f ≫ g)) ((congrArg (· * U _ _ (f ≫ g)) e1).symm.trans he)`.

Establish `e3` using `congrArg (TrivSqZeroExt.snd (R := D') (M := D')) (congrFun (congrFun (congrFun (congrFun (congrFun hn S) S') (TT hx')) f) g)`. Express the relevant statement in the definitionally equal form `TrivSqZeroExt.snd (R := D') (M := D') (g.hom.φ (n _ _ f)) - TrivSqZeroExt.snd (R := D') (M := D') (n _ _ (f ≫ g)) + TrivSqZeroExt.snd (R := D') (M := D') (n _ _ g) = TrivSqZeroExt.snd (R := D') (M := D') (w.1 _ _ _ f.hom g.hom) - TrivSqZeroExt.snd (R := D') (M := D') (ℓ.1 _ _ _ f …`. Take the linear combination `e2 - e3`. Establish `us : IsUnit (TrivSqZeroExt.fst (R` using `D) (M := D) (U _ _ (sM hx))) := uU _ _ (sM hx)`. Establish `ui : IsUnit (TrivSqZeroExt.fst (R` using `D) (M := D) (U _ _ (iM hx))) := uU _ _ (iM hx)`.

Establish `k1` using `key _ _ (sM hx) tM (((fst_epsHom φ _).symm ▸ us.map φ : IsUnit (epsHom φ (U _ _ (sM hx))).fst))`. Establish `k2` using `key _ _ aM (sM hx') (uU _ _ aM)`. Establish `k3` using `key _ _ (iM hx) tM (((fst_epsHom φ _).symm ▸ ui.map φ : IsUnit (epsHom φ (U _ _ (iM hx))).fst))`. Establish `k4` using `key _ _ bM (iM hx') (isUnit_fst (D := D') (uU _ _ bM))`. Rewrite `k1` using `[c1]`.

Rewrite `k3` using `[c2]`. Establish `a1 : TrivSqZeroExt.snd (R` using `D') (M := D') (tM.hom.φ (n _ _ (sM hx))) = φ (TrivSqZeroExt.snd (R := D) (n _ _ (sM hx))) := snd_epsHom' φ _`. Establish `a2 : TrivSqZeroExt.snd (R` using `D') (M := D') ((sM hx').hom.φ (n _ _ aM)) = 0 := rfl`. Establish `a3 : TrivSqZeroExt.snd (R` using `D') (M := D') (tM.hom.φ (n _ _ (iM hx))) = φ (TrivSqZeroExt.snd (R := D) (n _ _ (iM hx))) := snd_epsHom' φ _`. Establish `a4 : TrivSqZeroExt.snd (R` using `D') (M := D') ((iM hx').hom.φ (n _ _ bM)) = sndPull (cocOf P.U n) v D D' φ x := by`.

Establish `tr : ∀ (y y' : Pt (A ⊗ B) (DualNumber D')) (_ : y = y') (h : Sm P.U y) (h' : Sm P.U y') (f : TV hx ⟶ smallAt P.U y h) (f' : TV hx ⟶ smallAt P.U y' h'), (∀ r, f.hom.φ r = f'.hom.φ r) → n _ _ f = n _ _ f'`. Introduce and unpack `y _ rfl h h' f f' hf`. Establish `: f = f'` using `ObjectProperty.hom_ext _ (Thick.hom_ext hf)`. Substitute `this` using the available equality. Both sides reduce to the same expression.

Simplify using `only [sndPull, cocOf, dif_pos (sV hx)]`. Conclude with `congrArg (TrivSqZeroExt.snd (R := D') (M := D')) (tr _ _ (spOver_epsHom_ptV v φ x).symm (sV hx') ((sV hx).map (epsHom φ)) bM (ObjectProperty.homMk (trivMap (epsHom φ) (ptV v x))) fun _ ↦ rfl)`. Establish `b1 : dl (D` using `D') (tM.hom.φ (U _ _ (sM hx))) = φ (dl (U _ _ (sM hx))) := dl_epsHom φ _ us`. Establish `b2 : dl (D` using `D') ((sM hx').hom.φ (U _ _ aM)) = 0 := dl_inl _`. Establish `b3 : dl (D` using `D') (tM.hom.φ (U _ _ (iM hx))) = φ (dl (U _ _ (iM hx))) := dl_epsHom φ _ ui`.

Establish `b4 : dl (D` using `D') ((iM hx').hom.φ (U _ _ bM)) = tanCoc P j v D D' φ x + φ (dl (gv P (ptV v x).left (j D x) (i (TV hx)))) - dl (gv P (ptV v (spOver φ ≫ x)).left (j D' (spOver φ ≫ x)) (i (TV hx'))) := by`. Establish `e : (iM hx').hom.φ (U _ _ bM) = gv P (ptV v (spOver φ ≫ x)).left (i (TV hx')) (i (TV hx))` using `(hU _ _ bM).trans (gv_eq P _ _).symm`. Establish `e' : spMap (epsHom φ : DualNumber D →+* DualNumber D') ≫ (ptV v x).left = (ptV v (spOver φ ≫ x)).left` using `(bHom v φ x).pt`. Conclude with `(congrArg (dl (D := D')) e).trans (dl_gv φ P hP _ _ e' (hi (TV hx)) (ptV_mem P hv (hj D x hx)) (hi (TV hx')) (ptV_mem P hv (hj D' _ hx')))`. Establish `hk` using `hκ D D' φ x (sHom x) (iHom v hv x) (sHom _) (iHom v hv _) (aHom φ x) (bHom v φ x) (τHom φ x) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)`.

Express the relevant statement in the definitionally equal form `_ = TrivSqZeroExt.snd (R := D') (M := D') (w.1 _ _ _ (sM hx).hom tM.hom) - TrivSqZeroExt.snd (R := D') (M := D') (w.1 _ _ _ aM.hom (sM hx').hom) - TrivSqZeroExt.snd (R := D') (M := D') (w.1 _ _ _ (iM hx).hom tM.hom) + TrivSqZeroExt.snd (R := D') (M := D') (w.1 _ _ _ bM.hom (iM hx …`. Simplify using `only [k, map_neg, map_add, map_sub]`. Take the linear combination `hk + k1 - k2 - k3 + k4 + a1 - a2 - a3 + a4 + b1 - b2 - b3 + b4`.
-/
theorem contr_cohom : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB →
    ∀ v : epsR R ⟶ B, IsTangent v → ∀ (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι), IsChoice P j →
    ∀ w : Z2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)),
    (∀ (T T' T'' : Thick (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) (a : T ⟶ T') (b : T' ⟶ T''), T.J = ⊥ → T'.J = ⊥ →
      T''.J = ⊥ → w.1 T T' T'' a b = 0) →
    ∀ (i : (IsSmall (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) P.U).FullSubcategory → P.ι)
      (hi : ∀ T, ⊤ ≤ T.obj.x ⁻¹ᵁ P.U (i T))
      (U : ∀ T T' : (IsSmall (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) P.U).FullSubcategory, (T ⟶ T') → T'.obj.B)
      (ℓ : Z2 ((IsSmall (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) P.U).ι ⋙ O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))),
    (∀ T T' φ, T'.obj.π (U T T' φ) = evalAt T'.obj.x (P.U (i T') ⊓ P.U (i T))
      (le_inf (hi T') (φ.hom.le_preimage (hi T))) (P.g (i T') (i T)).val) →
    (∀ T T' T'' φ ψ, (ℓ.1 T T' T'' φ ψ : T''.obj.B) ∈ T''.obj.J ∧
      dpExp T''.obj.δ (ℓ.1 T T' T'' φ ψ) * U T T'' (φ ≫ ψ) = ψ.hom.φ (U T T' φ) * U T' T'' ψ) →
    ∀ n : C1 ((IsSmall (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) P.U).ι ⋙ O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)),
    d1 _ n = ((CoefMap.restrict (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))
      (IsSmall (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) P.U).ι).pullbackTwoCocycle w).1 - ℓ.1 →
    ∀ κ : Fn1 A, IsContr w.1 v κ → Cohom (chartsA P) κ ((tanCoc P j v).add (sndPull (cocOf P.U n) v)) := by
  classical
  intro R _ A B _ _ P hP v hv j hj w _ i hi U ℓ hU hℓ n hn κ hκ
  have s0 : ∀ {D : Type} [CommRing D] [Algebra R D] {x : Pt A D}, Sm (chartsA P) x → Sm P.U (pt0 B x) :=
    fun ⟨c, h⟩ ↦ ⟨c, pointWithZeroSecondCoord_mem_chart_of_restricted P h⟩
  have sV : ∀ {D : Type} [CommRing D] [Algebra R D] {x : Pt A D}, Sm (chartsA P) x → Sm P.U (ptV v x) :=
    fun ⟨c, h⟩ ↦ ⟨c, ptV_mem P hv h⟩
  let T0 : ∀ {D : Type} [CommRing D] [Algebra R D] {x : Pt A D}, Sm (chartsA P) x → SmallCat P.U :=
    fun {_} _ _ {x} h ↦ ⟨trivAt (pt0 B x), s0 h⟩
  let TV : ∀ {D : Type} [CommRing D] [Algebra R D] {x : Pt A D}, Sm (chartsA P) x → SmallCat P.U :=
    fun {_} _ _ {x} h ↦ ⟨trivAt (ptV v x), sV h⟩
  let TT : ∀ {D : Type} [CommRing D] [Algebra R D] {x : Pt A D}, Sm (chartsA P) x → SmallCat P.U :=
    fun {_} _ _ {x} h ↦ ⟨thickAt B x, s0 h⟩
  let sM : ∀ {D : Type} [CommRing D] [Algebra R D] {x : Pt A D} (h : Sm (chartsA P) x), T0 h ⟶ TT h :=
    fun {_} _ _ {x} _ ↦ ObjectProperty.homMk (sHom x)
  let iM : ∀ {D : Type} [CommRing D] [Algebra R D] {x : Pt A D} (h : Sm (chartsA P) x), TV h ⟶ TT h :=
    fun {_} _ _ {x} _ ↦ ObjectProperty.homMk (iHom v hv x)
  let k : ∀ {D : Type} [CommRing D] [Algebra R D] {x : Pt A D}, Sm (chartsA P) x → D :=
    fun {D} _ _ {x} h ↦ TrivSqZeroExt.snd (R := D) (n _ _ (sM h)) - TrivSqZeroExt.snd (R := D) (n _ _ (iM h)) +
      (dl (U _ _ (sM h)) - dl (U _ _ (iM h))) + dl (gv P (ptV v x).left (j D x) (i (TV h)))
  refine ⟨fun D _ _ x ↦ if h : Sm (chartsA P) x then -k h else 0, ?_⟩
  intro D _ _ D' _ _ φ x hx
  have hx' : Sm (chartsA P) (spOver φ ≫ x) := hx.map φ
  simp only [dif_pos hx, dif_pos hx', Fn1.add, Fn1.neg]
  let aM : T0 hx ⟶ T0 hx' := ObjectProperty.homMk (aHom φ x)
  let bM : TV hx ⟶ TV hx' := ObjectProperty.homMk (bHom v φ x)
  let tM : TT hx ⟶ TT hx' := ObjectProperty.homMk (τHom φ x)
  have c1 : sM hx ≫ tM = aM ≫ sM hx' := ObjectProperty.hom_ext _ (Thick.hom_ext fun r ↦ by
    change epsHom φ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (φ r)
    ext
    · exact fst_epsHom φ _
    · exact (snd_epsHom' φ _).trans (map_zero φ))
  have c2 : iM hx ≫ tM = bM ≫ iM hx' := ObjectProperty.hom_ext _ (Thick.hom_ext fun r ↦ rfl)
  have uU : ∀ (S S' : SmallCat P.U) (f : S ⟶ S'), IsUnit (S'.obj.π (U S S' f)) := fun S S' f ↦ by
    rw [hU]; exact (P.g _ _).isUnit.map _
  have key : ∀ (S S' : SmallCat P.U) (f : S ⟶ S') (g : S' ⟶ TT hx'),
      IsUnit (TrivSqZeroExt.fst (R := D') (M := D') (g.hom.φ (U _ _ f))) →
      TrivSqZeroExt.snd (R := D') (M := D') (w.1 _ _ _ f.hom g.hom) =
        TrivSqZeroExt.snd (R := D') (M := D') (g.hom.φ (n _ _ f)) -
          TrivSqZeroExt.snd (R := D') (M := D') (n _ _ (f ≫ g)) + TrivSqZeroExt.snd (R := D') (M := D') (n _ _ g) +
        (dl (D := D') (g.hom.φ (U _ _ f)) + dl (D := D') (U _ _ g) - dl (D := D') (U _ _ (f ≫ g))) := by
    intro S S' f g hu
    obtain ⟨hm, he⟩ := hℓ S S' (TT hx') f g
    have e1 : dpExp (TT hx').obj.δ (ℓ.1 _ _ _ f g) = @HAdd.hAdd (DualNumber D') (DualNumber D') (DualNumber D') _ 1 (ℓ.1 _ _ _ f g) :=
      dpExp_sqDP (epsExt R D').sq hm
    have e2 := snd_of_exp (D := D') (ℓ.1 _ _ _ f g) (g.hom.φ (U _ _ f)) (U _ _ g) (U _ _ (f ≫ g)) hm hu
      (uU _ _ g) (uU _ _ (f ≫ g)) ((congrArg (· * U _ _ (f ≫ g)) e1).symm.trans he)
    have e3 := congrArg (TrivSqZeroExt.snd (R := D') (M := D'))
      (congrFun (congrFun (congrFun (congrFun (congrFun hn S) S') (TT hx')) f) g)
    change TrivSqZeroExt.snd (R := D') (M := D') (g.hom.φ (n _ _ f)) -
          TrivSqZeroExt.snd (R := D') (M := D') (n _ _ (f ≫ g)) + TrivSqZeroExt.snd (R := D') (M := D') (n _ _ g) =
      TrivSqZeroExt.snd (R := D') (M := D') (w.1 _ _ _ f.hom g.hom) -
        TrivSqZeroExt.snd (R := D') (M := D') (ℓ.1 _ _ _ f g) at e3
    linear_combination e2 - e3
  have us : IsUnit (TrivSqZeroExt.fst (R := D) (M := D) (U _ _ (sM hx))) := uU _ _ (sM hx)
  have ui : IsUnit (TrivSqZeroExt.fst (R := D) (M := D) (U _ _ (iM hx))) := uU _ _ (iM hx)
  have k1 := key _ _ (sM hx) tM (((fst_epsHom φ _).symm ▸ us.map φ :
    IsUnit (epsHom φ (U _ _ (sM hx))).fst))
  have k2 := key _ _ aM (sM hx') (uU _ _ aM)
  have k3 := key _ _ (iM hx) tM (((fst_epsHom φ _).symm ▸ ui.map φ :
    IsUnit (epsHom φ (U _ _ (iM hx))).fst))
  have k4 := key _ _ bM (iM hx') (isUnit_fst (D := D') (uU _ _ bM))
  rw [c1] at k1
  rw [c2] at k3
  have a1 : TrivSqZeroExt.snd (R := D') (M := D') (tM.hom.φ (n _ _ (sM hx))) =
    φ (TrivSqZeroExt.snd (R := D) (n _ _ (sM hx))) := snd_epsHom' φ _
  have a2 : TrivSqZeroExt.snd (R := D') (M := D') ((sM hx').hom.φ (n _ _ aM)) = 0 := rfl
  have a3 : TrivSqZeroExt.snd (R := D') (M := D') (tM.hom.φ (n _ _ (iM hx))) =
    φ (TrivSqZeroExt.snd (R := D) (n _ _ (iM hx))) := snd_epsHom' φ _
  have a4 : TrivSqZeroExt.snd (R := D') (M := D') ((iM hx').hom.φ (n _ _ bM)) =
      sndPull (cocOf P.U n) v D D' φ x := by
    have tr : ∀ (y y' : Pt (A ⊗ B) (DualNumber D')) (_ : y = y') (h : Sm P.U y) (h' : Sm P.U y')
        (f : TV hx ⟶ smallAt P.U y h) (f' : TV hx ⟶ smallAt P.U y' h'),
        (∀ r, f.hom.φ r = f'.hom.φ r) → n _ _ f = n _ _ f' := by
      rintro y _ rfl h h' f f' hf
      have : f = f' := ObjectProperty.hom_ext _ (Thick.hom_ext hf)
      subst this; rfl
    simp only [sndPull, cocOf, dif_pos (sV hx)]
    exact congrArg (TrivSqZeroExt.snd (R := D') (M := D'))
      (tr _ _ (spOver_epsHom_ptV v φ x).symm (sV hx') ((sV hx).map (epsHom φ)) bM
        (ObjectProperty.homMk (trivMap (epsHom φ) (ptV v x))) fun _ ↦ rfl)
  have b1 : dl (D := D') (tM.hom.φ (U _ _ (sM hx))) = φ (dl (U _ _ (sM hx))) := dl_epsHom φ _ us
  have b2 : dl (D := D') ((sM hx').hom.φ (U _ _ aM)) = 0 := dl_inl _
  have b3 : dl (D := D') (tM.hom.φ (U _ _ (iM hx))) = φ (dl (U _ _ (iM hx))) := dl_epsHom φ _ ui
  have b4 : dl (D := D') ((iM hx').hom.φ (U _ _ bM)) = tanCoc P j v D D' φ x +
      φ (dl (gv P (ptV v x).left (j D x) (i (TV hx)))) -
      dl (gv P (ptV v (spOver φ ≫ x)).left (j D' (spOver φ ≫ x)) (i (TV hx'))) := by
    have e : (iM hx').hom.φ (U _ _ bM) = gv P (ptV v (spOver φ ≫ x)).left (i (TV hx')) (i (TV hx)) :=
      (hU _ _ bM).trans (gv_eq P _ _).symm
    have e' : spMap (epsHom φ : DualNumber D →+* DualNumber D') ≫ (ptV v x).left =
        (ptV v (spOver φ ≫ x)).left := (bHom v φ x).pt
    exact (congrArg (dl (D := D')) e).trans (dl_gv φ P hP _ _ e' (hi (TV hx)) (ptV_mem P hv (hj D x hx))
      (hi (TV hx')) (ptV_mem P hv (hj D' _ hx')))
  have hk := hκ D D' φ x (sHom x) (iHom v hv x) (sHom _) (iHom v hv _) (aHom φ x) (bHom v φ x) (τHom φ x)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  change _ = TrivSqZeroExt.snd (R := D') (M := D') (w.1 _ _ _ (sM hx).hom tM.hom) -
    TrivSqZeroExt.snd (R := D') (M := D') (w.1 _ _ _ aM.hom (sM hx').hom) -
    TrivSqZeroExt.snd (R := D') (M := D') (w.1 _ _ _ (iM hx).hom tM.hom) +
    TrivSqZeroExt.snd (R := D') (M := D') (w.1 _ _ _ bM.hom (iM hx').hom) at hk
  simp only [k, map_neg, map_add, map_sub]
  linear_combination hk + k1 - k2 - k3 + k4 + a1 - a2 - a3 + a4 + b1 - b2 - b3 + b4

end GlobalTheory.PtExt.ChernContr
