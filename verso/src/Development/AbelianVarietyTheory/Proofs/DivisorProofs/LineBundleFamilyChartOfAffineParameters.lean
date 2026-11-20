import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjRestrictSnd
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon.Zar

variable {S : Scheme.{0}} {A : Over S}

/- English proof (translation)
Rewrite `h`, the goal using `[same_iff hN hM]`. Establish `e` using `congrArg (CechPic.pull (lift (fst A Z) (snd A Z ≫ z)).left) h`. Simplify `e` using `only [pull_evc, lift_fst, lift_snd_assoc, Category.assoc]`.
-/
theorem same_comp {T U Y Z : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB) (hM : M.IsLB)
    {y : Y ⟶ T} {u : Y ⟶ U} (h : Same A N M y u) (z : Z ⟶ Y) : Same A N M (z ≫ y) (z ≫ u) := by
  rw [same_iff hN hM] at h ⊢
  have e := congrArg (CechPic.pull (lift (fst A Z) (snd A Z ≫ z)).left) h
  simpa only [pull_evc, lift_fst, lift_snd_assoc, Category.assoc] using e

/- English proof (translation)
Rewrite using `[same_iff (pull_isLB hN _) hM, same_iff hN hM, evc_ev hN]`. Simplify using `only [lift_fst, lift_snd_assoc, Category.assoc]`.
-/
theorem same_ev_iff {T U V Y : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB) (hM : M.IsLB)
    (j : V ⟶ T) (y : Y ⟶ V) (u : Y ⟶ U) :
    Same A (ev N (fst A V) (snd A V ≫ j)) M y u ↔ Same A N M (y ≫ j) u := by
  rw [same_iff (pull_isLB hN _) hM, same_iff hN hM, evc_ev hN]
  simp only [lift_fst, lift_snd_assoc, Category.assoc]

/- English proof (translation)
Set `V` to `y.left ⁻¹ᵁ z.left.opensRange`. Set `Y' : Over S` to `Over.mk (V.ι ≫ Y.hom)`. Set `i : Y' ⟶ Y` to `Over.homMk V.ι rfl`. Establish `hr : Set.range (i ≫ y).left ⊆ Set.range z.left`. Introduce and unpack `_ ⟨w, rfl⟩`.

Conclude with `w.2`. Set `t : Y' ⟶ Z` to `Over.homMk (IsOpenImmersion.lift z.left (i ≫ y).left hr) (by`. Rewrite using `[← Over.w z, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w])`. Use `⟨Y', i, t, inferInstanceAs (IsOpenImmersion V.ι), ⟨⟨p, hp⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Use `ext1`.

Conclude with `IsOpenImmersion.lift_fac _ _ _`.
-/
theorem exists_restrict {T Y Z : Over S} (y : Y ⟶ T) (z : Z ⟶ T) [IsOpenImmersion z.left] (p : Y.left)
    (hp : y.left p ∈ Set.range z.left) :
    ∃ (Y' : Over S) (i : Y' ⟶ Y) (t : Y' ⟶ Z), IsOpenImmersion i.left ∧ p ∈ Set.range i.left ∧ t ≫ z = i ≫ y := by
  let V := y.left ⁻¹ᵁ z.left.opensRange
  let Y' : Over S := Over.mk (V.ι ≫ Y.hom)
  let i : Y' ⟶ Y := Over.homMk V.ι rfl
  have hr : Set.range (i ≫ y).left ⊆ Set.range z.left := by
    rintro _ ⟨w, rfl⟩
    exact w.2
  let t : Y' ⟶ Z := Over.homMk (IsOpenImmersion.lift z.left (i ≫ y).left hr) (by
    rw [← Over.w z, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w])
  refine ⟨Y', i, t, inferInstanceAs (IsOpenImmersion V.ι), ⟨⟨p, hp⟩, rfl⟩, ?_⟩
  ext1; exact IsOpenImmersion.lift_fac _ _ _

variable [GrpObj A]

/- English proof (translation)
Use `choose Z z u ho hp hs using loc`. Set `𝒰 : Y.left.OpenCover` to `Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) Y.left (fun p ↦ (Z p).left) (fun p ↦ (z p).left) (fun p ↦ by obtain ⟨q, hq⟩ := hp p; exact ⟨p, q, hq⟩) ho`. Establish `hc : ∀ p q : Y.left, pullback.fst (z p).left (z q).left ≫ (u p).left = pullback.snd (z p).left (z q).left ≫ (u q).left`. Introduce `p q`. Set `P : Over S` to `Over.mk (pullback.fst (z p).left (z q).left ≫ (Z p).hom)`.

Set `a : P ⟶ Z p` to `Over.homMk (pullback.fst (z p).left (z q).left) rfl`. Set `b : P ⟶ Z q` to `Over.homMk (pullback.snd (z p).left (z q).left) (by`. Rewrite using `[← Over.w (z q), ← Category.assoc, ← pullback.condition, Category.assoc, Over.w]`. Use the proof step `rfl)`. Establish `hab : a ≫ z p = b ≫ z q` using `by ext1; exact pullback.condition`.

Establish `h₁` using `same_comp hN.isLB hM.isLB (hs p) a`. Establish `h₂` using `same_comp hN.isLB hM.isLB (hs q) b`. Rewrite `h₁` using `[← Category.assoc, hab, Category.assoc]`. Rewrite `h₁`, `h₂` using `[same_iff hN.isLB hM.isLB]`. Establish `h` using `hI P _ _ ((same_iff hM.isLB hM.isLB _ _).2 (h₁.symm.trans h₂))`.

Conclude with `congrArg (·.left) h`. Establish `hg : ∀ p, (z p).left ≫ 𝒰.glueMorphisms (fun p ↦ (u p).left) hc = (u p).left` using `𝒰.ι_glueMorphisms _ hc`. Set `g : Y ⟶ U` to `Over.homMk (𝒰.glueMorphisms (fun p ↦ (u p).left) hc) (𝒰.hom_ext _ _ fun (p : Y.left) ↦ ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ U.hom) (hg p))).trans ((Over.w (u p)).trans (Over.w (z p)).symm))`. Use `⟨g, same_of_local S A T U hA N M hN hM Y y g fun p ↦ ⟨Z p, z p, ho p, hp p, ?_⟩⟩` and prove the remaining obligations. Establish `e : z p ≫ g = u p` using `by ext1; exact hg p`.

Rewrite using `[e]`. Conclude with `hs p`.
-/
theorem exists_same_of_local (hA : IsAbelianScheme A) {T U Y : Over S} {N : LB (A ⊗ T).left}
    {M : LB (A ⊗ U).left} (hN : Fam A N) (hM : Fam A M) (hI : Inj A M) (y : Y ⟶ T)
    (loc : ∀ p : Y.left, ∃ (Z : Over S) (z : Z ⟶ Y) (u : Z ⟶ U), IsOpenImmersion z.left ∧
      p ∈ Set.range z.left ∧ Same A N M (z ≫ y) u) : ∃ u : Y ⟶ U, Same A N M y u := by
  choose Z z u ho hp hs using loc
  let 𝒰 : Y.left.OpenCover := Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) Y.left (fun p ↦ (Z p).left)
    (fun p ↦ (z p).left) (fun p ↦ by obtain ⟨q, hq⟩ := hp p; exact ⟨p, q, hq⟩) ho
  have hc : ∀ p q : Y.left, pullback.fst (z p).left (z q).left ≫ (u p).left =
      pullback.snd (z p).left (z q).left ≫ (u q).left := by
    intro p q
    let P : Over S := Over.mk (pullback.fst (z p).left (z q).left ≫ (Z p).hom)
    let a : P ⟶ Z p := Over.homMk (pullback.fst (z p).left (z q).left) rfl
    let b : P ⟶ Z q := Over.homMk (pullback.snd (z p).left (z q).left) (by
      rw [← Over.w (z q), ← Category.assoc, ← pullback.condition, Category.assoc, Over.w]; rfl)
    have hab : a ≫ z p = b ≫ z q := by ext1; exact pullback.condition
    have h₁ := same_comp hN.isLB hM.isLB (hs p) a
    have h₂ := same_comp hN.isLB hM.isLB (hs q) b
    rw [← Category.assoc, hab, Category.assoc] at h₁
    rw [same_iff hN.isLB hM.isLB] at h₁ h₂
    have h := hI P _ _ ((same_iff hM.isLB hM.isLB _ _).2 (h₁.symm.trans h₂))
    exact congrArg (·.left) h
  have hg : ∀ p, (z p).left ≫ 𝒰.glueMorphisms (fun p ↦ (u p).left) hc = (u p).left :=
    𝒰.ι_glueMorphisms _ hc
  let g : Y ⟶ U := Over.homMk (𝒰.glueMorphisms (fun p ↦ (u p).left) hc) (𝒰.hom_ext _ _ fun (p : Y.left) ↦
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ U.hom) (hg p))).trans
      ((Over.w (u p)).trans (Over.w (z p)).symm))
  refine ⟨g, same_of_local S A T U hA N M hN hM Y y g fun p ↦ ⟨Z p, z p, ho p, hp p, ?_⟩⟩
  have e : z p ≫ g = u p := by ext1; exact hg p
  rw [e]
  exact hs p

/- English proof (translation)
Establish `hM : (AbDual.ev N (fst A Y) (snd A Y ≫ y)).IsLB` using `pull_isLB h.isLB _`. Use `⟨hM, (isAdditive_iff hM).2 fun Z a a' t ↦ ?_⟩` and prove the remaining obligations. Simplify using `only [evc_ev h.isLB, lift_fst, lift_snd_assoc]`. Conclude with `(isAdditive_iff h.isLB).1 h.add _ _ _ _`.
-/
theorem fam_ev {T Y : Over S} {N : LB (A ⊗ T).left} (h : Fam A N) (y : Y ⟶ T) :
    Fam A (ev N (fst A Y) (snd A Y ≫ y)) := by
  have hM : (AbDual.ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB h.isLB _
  refine ⟨hM, (isAdditive_iff hM).2 fun Z a a' t ↦ ?_⟩
  simp only [evc_ev h.isLB, lift_fst, lift_snd_assoc]
  exact (isAdditive_iff h.isLB).1 h.add _ _ _ _

end GlobalTheory.DualCon.Zar

namespace GlobalTheory.DualCon

/- English proof (translation)
Introduce `S A _ hA U M hM hI aff T N hN`. Set `W : Set T.left` to `{x | ∃ (Z : Over S) (z : Z ⟶ T) (u : Z ⟶ U), IsOpenImmersion z.left ∧ x ∈ Set.range z.left ∧ Same A N M z u}`. Establish `hW : IsOpen W`. Rewrite using `[isOpen_iff_forall_mem_open]`. Introduce and unpack `x ⟨Z, z, u, ho, hx, hs⟩`.

Conclude with `⟨Set.range z.left, fun x' hx' ↦ ⟨Z, z, u, ho, hx', hs⟩, z.left.opensRange.2, hx⟩`. Use `⟨⟨W, hW⟩, fun Y y ↦ ⟨?_, fun h ↦ ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨u, hu⟩ p`. Take `⟨i, q, hq⟩` from `T.left.affineCover.exists_eq (y.left p)`. Set `V : Over S` to `Over.mk (T.left.affineCover.f i ≫ T.hom)`.

Set `j : V ⟶ T` to `Over.homMk (T.left.affineCover.f i) rfl`. Use `haveI : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion (T.left.affineCover.f i))`. Use `haveI : IsAffine V.left := inferInstanceAs (IsAffine (T.left.affineCover.X i))`. Take `⟨O, hO⟩` from `aff V _ (Zar.fam_ev hN j)`. Take `⟨Y', c, t, -, ⟨r, hr⟩, ht⟩` from `Zar.exists_restrict y j p ⟨q, hq⟩`.

Establish `h₁ : t.left r ∈ O` using `(hO Y' t).1 ⟨c ≫ u, by`. Rewrite using `[Zar.same_ev_iff hN.isLB hM.isLB, ht]`. Conclude with `Zar.same_comp hN.isLB hM.isLB hu c⟩ r`. Set `Z : Over S` to `Over.mk (O.ι ≫ V.hom)`. Set `k : Z ⟶ V` to `Over.homMk O.ι rfl`.

Use `haveI : IsOpenImmersion k.left := inferInstanceAs (IsOpenImmersion O.ι)`. Take `⟨v, hv⟩` from `(hO Z k).2 fun w ↦ w.2`. Use `⟨Z, k ≫ j, v, by rw [Over.comp_left]; infer_instance, ⟨⟨t.left r, h₁⟩, ?_⟩, (Zar.same_ev_iff hN.isLB hM.isLB _ _ _).1 hv⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(t ≫ j).left r = _`. Rewrite using `[ht, ← hr]`.

Both sides reduce to the same expression. Use `Zar.exists_same_of_local hA hN hM hI y fun p ↦ ?_` and prove the remaining obligations. Take `⟨Z, z, u, ho, hx, hs⟩` from `h p`. Take `⟨Y', c, t, hc, hp, ht⟩` from `Zar.exists_restrict y z p hx`. Conclude with `⟨Y', c, t ≫ u, hc, hp, ht ▸ Zar.same_comp hN.isLB hM.isLB hs t⟩`.
-/
theorem chartAt_of_affine : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (U : Over S) (M : LB (A ⊗ U).left), Fam A M → Inj A M →
    (∀ (T : Over S) [IsAffine T.left] (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N) →
    ∀ (T : Over S) (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N := by
  intro S A _ hA U M hM hI aff T N hN
  let W : Set T.left := {x | ∃ (Z : Over S) (z : Z ⟶ T) (u : Z ⟶ U), IsOpenImmersion z.left ∧
    x ∈ Set.range z.left ∧ Same A N M z u}
  have hW : IsOpen W := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨Z, z, u, ho, hx, hs⟩
    exact ⟨Set.range z.left, fun x' hx' ↦ ⟨Z, z, u, ho, hx', hs⟩, z.left.opensRange.2, hx⟩
  refine ⟨⟨W, hW⟩, fun Y y ↦ ⟨?_, fun h ↦ ?_⟩⟩
  · rintro ⟨u, hu⟩ p
    obtain ⟨i, q, hq⟩ := T.left.affineCover.exists_eq (y.left p)
    let V : Over S := Over.mk (T.left.affineCover.f i ≫ T.hom)
    let j : V ⟶ T := Over.homMk (T.left.affineCover.f i) rfl
    haveI : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion (T.left.affineCover.f i))
    haveI : IsAffine V.left := inferInstanceAs (IsAffine (T.left.affineCover.X i))
    obtain ⟨O, hO⟩ := aff V _ (Zar.fam_ev hN j)
    obtain ⟨Y', c, t, -, ⟨r, hr⟩, ht⟩ := Zar.exists_restrict y j p ⟨q, hq⟩
    have h₁ : t.left r ∈ O := (hO Y' t).1 ⟨c ≫ u, by
      rw [Zar.same_ev_iff hN.isLB hM.isLB, ht]
      exact Zar.same_comp hN.isLB hM.isLB hu c⟩ r
    let Z : Over S := Over.mk (O.ι ≫ V.hom)
    let k : Z ⟶ V := Over.homMk O.ι rfl
    haveI : IsOpenImmersion k.left := inferInstanceAs (IsOpenImmersion O.ι)
    obtain ⟨v, hv⟩ := (hO Z k).2 fun w ↦ w.2
    refine ⟨Z, k ≫ j, v, by rw [Over.comp_left]; infer_instance, ⟨⟨t.left r, h₁⟩, ?_⟩,
      (Zar.same_ev_iff hN.isLB hM.isLB _ _ _).1 hv⟩
    change (t ≫ j).left r = _
    rw [ht, ← hr]
    rfl
  · refine Zar.exists_same_of_local hA hN hM hI y fun p ↦ ?_
    obtain ⟨Z, z, u, ho, hx, hs⟩ := h p
    obtain ⟨Y', c, t, hc, hp, ht⟩ := Zar.exists_restrict y z p hx
    exact ⟨Y', c, t ≫ u, hc, hp, ht ▸ Zar.same_comp hN.isLB hM.isLB hs t⟩

end GlobalTheory.DualCon
