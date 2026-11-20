import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.Points GlobalTheory.ZM GlobalTheory.SiegelTor

namespace GlobalTheory.UPoinc

/- English proof (translation)
Introduce `E _ _ _ H Dw hpq l Xo cf C X p _ z ct U u' hU hwU hu'`. Use `haveI := X.ar.char`. Use `set w := (gPt p ≫ ct.y) (closedPoint (PadicAlgCl p)) with hw`. Establish `hne : (U : Set X.M.Z).Nonempty` using `⟨w, hwU⟩`. Establish `hle : X.M.ringOn U ≤ X.M.O w` using `RatModel.ringOn_le_O hwU`.

Establish `hsp : ∀ w', (gPt p ≫ ct.y) w' ⤳ w` using `fun w' => by`. Rewrite using `[Subsingleton.elim w' (closedPoint (PadicAlgCl p))]`. Set `y₀ : X.M.ringOn U →+* PadicAlgCl p` to `(RatModel.valHomOf (gPt p ≫ ct.y) w hsp).comp (Subalgebra.inclusion hle).toRingHom`. Establish `hy₀ : ∀ a : X.M.ringOn U, y₀ a = X.M.val (gPt p ≫ ct.y) a` using `fun a => rfl`. Take `⟨y₁, hy₁, -⟩` from `existsUnique_ratLift (X.M.ringOn U) (K := PadicAlgCl p) (fun n hn => IsUnit.mk0 _ (Int.cast_ne_zero.2 hn)) y₀`.

Establish `hy₁' : ∀ a : X.M.ringOn U, y₁ (toRat _ a) = y₀ a` using `fun a => RingHom.congr_fun hy₁ a`. Set `e : Sp (X.M.ringOn U) ⟶ X.M.Z` to `Spec.map (CommRingCat.ofHom (X.M.sectionsEquiv U hne).toRingHom) ≫ hU.fromSpec`. Establish `he : ∀ {K : Type} [CommRing K] (φ : X.M.ringOn U →+* K), ⊤ ≤ (spMap φ ≫ e) ⁻¹ᵁ U ∧ ∀ f, valR (spMap φ ≫ e) U f = φ (X.M.sectionsEquiv U hne f)`. Introduce `K _ φ`. Establish `e2 : spMap φ ≫ e = Spec.map (CommRingCat.ofHom (φ.comp (X.M.sectionsEquiv U hne).toRingHom)) ≫ hU.fromSpec`.

Rewrite using `[← Category.assoc, ← Spec.map_comp]`. Both sides reduce to the same expression. Rewrite using `[e2]`. Establish `hx` using `le_preimage_specMap_fromSpec hU (CommRingCat.ofHom (φ.comp (X.M.sectionsEquiv U hne).toRingHom))`. Use `⟨hx, fun f => ?_⟩` and prove the remaining obligations.

Rewrite using `[valR_eq _ U hx, valMap_specMap_fromSpec]`. Both sides reduce to the same expression. Establish `hyU : ⊤ ≤ (gPt p ≫ ct.y) ⁻¹ᵁ U` using `(le_preimage_iff _ U).2 hwU`. Establish `ha : spMap y₀ ≫ e = gPt p ≫ ct.y`. Use `ext_of_valR hU (he y₀).1 hyU fun f => ?_` and prove the remaining obligations.

Rewrite using `[(he y₀).2, hy₀, RatModel.coe_sectionsEquiv, RatModel.val_valF ((top_le_preimage_iff _ _).1 hyU)]`. Both sides reduce to the same expression. Establish `hgen : spMap (X.M.ringOn U).val.toRingHom ≫ e = X.M.pt`. Use `ext_of_valR hU (he _).1 (X.M.top_le_preimage_pt hne) fun f => ?_` and prove the remaining obligations. Rewrite using `[(he _).2]`.

Conclude with `(RatModel.coe_sectionsEquiv U hne f).trans (valF_eq_valR _ _ _)`. Establish `hdom : IsDominant (spMap (ratHull (X.M.ringOn U)).val.toRingHom)` using `⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]`. Conclude with `bot_le)⟩`. Use `haveI : IsProper C.z := ThetaDescent.isProper_of_isProjOver C.proj`.

Establish `hgen2 : spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ ((spMap (toRat _) ≫ e) ≫ X.π) = spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ (u' ≫ C.i)`. Rewrite using `[← Category.assoc, ← Category.assoc, spMap_val_toRat, hgen, X.comp, ← Category.assoc _ u' C.i, hu']`. Simplify using `only [USetup.uΩ, Category.assoc]`. Establish `hb : (spMap (toRat _) ≫ e) ≫ X.π = u' ≫ C.i` using `ext_of_isDominant_of_isSeparated C.z (ext_of_isDominant (spMap (ratHull (X.M.ringOn U)).val.toRingHom) (by`. Simplify using `only [← Category.assoc] at hgen2 ⊢`.

Rewrite using `[hgen2]))`. Use the proof step `(spMap (ratHull (X.M.ringOn U)).val.toRingHom) hgen2`. Use `haveI := C.isPreimmersion_i`. Establish `hy01 : spMap y₁ ≫ spMap (toRat (X.M.ringOn U)) = spMap y₀`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp, hy₁]`.

Establish `hpt' : spMap y₁ ≫ u' = spMap ct.ι ≫ ct.T.y`. Rewrite using `[← cancel_mono C.i, Category.assoc, ← hb, ← Category.assoc, ← Category.assoc, hy01, ha, Category.assoc, ct.comm, Category.assoc]`. Set `τ` to `Spec.preimage (ct.y ≫ X.M.s)`. Establish `hσ : (gPt p ≫ ct.y) ≫ X.M.s = spMap ((OO p).subtype.comp τ.hom)`. Rewrite using `[Category.assoc, ← Spec.map_preimage (ct.y ≫ X.M.s), ← Spec.map_comp]`.

Both sides reduce to the same expression. Use `⟨hle, y₁, fun a => (hy₁' a).trans (hy₀ a), hpt', fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[hy₁', hy₀]`. Use `show ‖X.M.val (gPt p ≫ ct.y) (algebraMap X.o₁ X.Ω₁ a)‖ ≤ 1`. Rewrite using `[RatModel.val_algebraMap hσ a]`.

Conclude with `(mem_OO_iff _).1 (τ.hom a).2`.
-/
theorem rechart_at_uClassical_trait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z) (U : X.M.Z.Opens) (u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf), IsAffineOpen U → (gPt p ≫ ct.y) (closedPoint (PadicAlgCl p)) ∈ U → spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ → X.M.ringOn U ≤ X.M.O ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) ∧ ∃ y₁ : ratHull (X.M.ringOn U) →+* PadicAlgCl p, (∀ a : X.M.ringOn U, y₁ (toRat _ a) = X.M.val (gPt p ≫ ct.y) a) ∧ spMap y₁ ≫ u' = spMap ct.ι ≫ ct.T.y ∧ ∀ a : X.o₁, ‖y₁ (toRat _ (algebraMap X.o₁ (X.M.ringOn U) a))‖ ≤ 1 := by
  intro E _ _ _ H Dw hpq l Xo cf C X p _ z ct U u' hU hwU hu'
  haveI := X.ar.char
  set w := (gPt p ≫ ct.y) (closedPoint (PadicAlgCl p)) with hw
  have hne : (U : Set X.M.Z).Nonempty := ⟨w, hwU⟩
  have hle : X.M.ringOn U ≤ X.M.O w := RatModel.ringOn_le_O hwU
  have hsp : ∀ w', (gPt p ≫ ct.y) w' ⤳ w := fun w' => by
    rw [Subsingleton.elim w' (closedPoint (PadicAlgCl p))]
  let y₀ : X.M.ringOn U →+* PadicAlgCl p :=
    (RatModel.valHomOf (gPt p ≫ ct.y) w hsp).comp (Subalgebra.inclusion hle).toRingHom
  have hy₀ : ∀ a : X.M.ringOn U, y₀ a = X.M.val (gPt p ≫ ct.y) a := fun a => rfl
  obtain ⟨y₁, hy₁, -⟩ := existsUnique_ratLift (X.M.ringOn U) (K := PadicAlgCl p)
    (fun n hn => IsUnit.mk0 _ (Int.cast_ne_zero.2 hn)) y₀
  have hy₁' : ∀ a : X.M.ringOn U, y₁ (toRat _ a) = y₀ a := fun a => RingHom.congr_fun hy₁ a
  let e : Sp (X.M.ringOn U) ⟶ X.M.Z :=
    Spec.map (CommRingCat.ofHom (X.M.sectionsEquiv U hne).toRingHom) ≫ hU.fromSpec
  have he : ∀ {K : Type} [CommRing K] (φ : X.M.ringOn U →+* K), ⊤ ≤ (spMap φ ≫ e) ⁻¹ᵁ U ∧
      ∀ f, valR (spMap φ ≫ e) U f = φ (X.M.sectionsEquiv U hne f) := by
    intro K _ φ
    have e2 : spMap φ ≫ e = Spec.map (CommRingCat.ofHom (φ.comp (X.M.sectionsEquiv U hne).toRingHom)) ≫
        hU.fromSpec := by
      rw [← Category.assoc, ← Spec.map_comp]; rfl
    rw [e2]
    have hx := le_preimage_specMap_fromSpec hU (CommRingCat.ofHom (φ.comp (X.M.sectionsEquiv U hne).toRingHom))
    refine ⟨hx, fun f => ?_⟩
    rw [valR_eq _ U hx, valMap_specMap_fromSpec]
    rfl
  have hyU : ⊤ ≤ (gPt p ≫ ct.y) ⁻¹ᵁ U := (le_preimage_iff _ U).2 hwU
  have ha : spMap y₀ ≫ e = gPt p ≫ ct.y := by
    refine ext_of_valR hU (he y₀).1 hyU fun f => ?_
    rw [(he y₀).2, hy₀, RatModel.coe_sectionsEquiv, RatModel.val_valF ((top_le_preimage_iff _ _).1 hyU)]
    rfl
  have hgen : spMap (X.M.ringOn U).val.toRingHom ≫ e = X.M.pt := by
    refine ext_of_valR hU (he _).1 (X.M.top_le_preimage_pt hne) fun f => ?_
    rw [(he _).2]
    exact (RatModel.coe_sectionsEquiv U hne f).trans (valF_eq_valR _ _ _)
  have hdom : IsDominant (spMap (ratHull (X.M.ringOn U)).val.toRingHom) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]; exact bot_le)⟩
  haveI : IsProper C.z := ThetaDescent.isProper_of_isProjOver C.proj
  have hgen2 : spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ ((spMap (toRat _) ≫ e) ≫ X.π) =
      spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ (u' ≫ C.i) := by
    rw [← Category.assoc, ← Category.assoc, spMap_val_toRat, hgen, X.comp, ← Category.assoc _ u' C.i, hu']
    simp only [USetup.uΩ, Category.assoc]
  have hb : (spMap (toRat _) ≫ e) ≫ X.π = u' ≫ C.i :=
    ext_of_isDominant_of_isSeparated C.z
      (ext_of_isDominant (spMap (ratHull (X.M.ringOn U)).val.toRingHom) (by
        simp only [← Category.assoc] at hgen2 ⊢; rw [hgen2]))
      (spMap (ratHull (X.M.ringOn U)).val.toRingHom) hgen2
  haveI := C.isPreimmersion_i
  have hy01 : spMap y₁ ≫ spMap (toRat (X.M.ringOn U)) = spMap y₀ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hy₁]
  have hpt' : spMap y₁ ≫ u' = spMap ct.ι ≫ ct.T.y := by
    rw [← cancel_mono C.i, Category.assoc, ← hb, ← Category.assoc, ← Category.assoc, hy01, ha, Category.assoc,
      ct.comm, Category.assoc]
  let τ := Spec.preimage (ct.y ≫ X.M.s)
  have hσ : (gPt p ≫ ct.y) ≫ X.M.s = spMap ((OO p).subtype.comp τ.hom) := by
    rw [Category.assoc, ← Spec.map_preimage (ct.y ≫ X.M.s), ← Spec.map_comp]; rfl
  refine ⟨hle, y₁, fun a => (hy₁' a).trans (hy₀ a), hpt', fun a => ?_⟩
  rw [hy₁', hy₀]
  show ‖X.M.val (gPt p ≫ ct.y) (algebraMap X.o₁ X.Ω₁ a)‖ ≤ 1
  rw [RatModel.val_algebraMap hσ a]
  exact (mem_OO_iff _).1 (τ.hom a).2

end GlobalTheory.UPoinc
