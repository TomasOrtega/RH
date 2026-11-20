import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddSumIntegral
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.IntegralAddSum.add_sum_integral`. Consider the case `exact _root_.GlobalTheory.IntegralAddSum.add_sum_integral`. Consider the case `(apply _root_.GlobalTheory.IntegralAddSum.add_sum_integral <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.IntegralAddSum.add_sum_integral <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.IntegralAddSum.add_sum_integral <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.IntegralAddSum.add_sum_integral ..)`.
-/
theorem sumForm_add {A C K B : Type} [CommRing A] [CommRing C] [CommRing K] [CommRing B]
    (φ : A →+* K) (gc : C →+* B) (gk : K →+* B) {x y : B}
    (hx : ∃ (n : ℕ) (c : Fin n → C) (b : Fin n → K), (∀ m, φ.IsIntegralElem (b m)) ∧ x = ∑ m, gc (c m) * gk (b m))
    (hy : ∃ (n : ℕ) (c : Fin n → C) (b : Fin n → K), (∀ m, φ.IsIntegralElem (b m)) ∧ y = ∑ m, gc (c m) * gk (b m)) :
    ∃ (n : ℕ) (c : Fin n → C) (b : Fin n → K), (∀ m, φ.IsIntegralElem (b m)) ∧ x + y = ∑ m, gc (c m) * gk (b m) := by
  first
  | exact @_root_.GlobalTheory.IntegralAddSum.add_sum_integral
  | exact _root_.GlobalTheory.IntegralAddSum.add_sum_integral
  | (apply _root_.GlobalTheory.IntegralAddSum.add_sum_integral <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralAddSum.add_sum_integral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralAddSum.add_sum_integral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralAddSum.add_sum_integral ..)

/- English proof (translation)
Use `haveI : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))`. Distinguish the cases in `h : (V : Set (Sp K)).Nonempty`. Take `⟨x, hx⟩` from `h`. Establish `: V = ⊤`. Use extensionality with `y`.

Simplify using `only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]`. Conclude with `Subsingleton.elim x y ▸ hx`. Rewrite using `[this]`. Conclude with `isAffineOpen_top _`. Establish `: V = ⊥`.

Use extensionality with `y`. Simplify using `only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]`. Conclude with `fun hy => h ⟨y, hy⟩`. Rewrite using `[this]`. Conclude with `isAffineOpen_bot _`.
-/
theorem isAffineOpen_Sp_field (K : Type) [Field K] (V : (Sp K).Opens) : IsAffineOpen V := by
  haveI : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  by_cases h : (V : Set (Sp K)).Nonempty
  · obtain ⟨x, hx⟩ := h
    have : V = ⊤ := by
      ext y
      simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
      exact Subsingleton.elim x y ▸ hx
    rw [this]; exact isAffineOpen_top _
  · have : V = ⊥ := by
      ext y
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hy => h ⟨y, hy⟩
    rw [this]; exact isAffineOpen_bot _

/- English proof (translation)
Introduce `R _ _ M G hG Y α t hpb W U hWU hW hU f hf`. Establish `hV : IsAffineOpen (M.gp ⁻¹ᵁ U)` using `isAffineOpen_Sp_field _ _`. Establish `hle` using `locInt_le_gen G.hom α t M.gp hpb.w W U hWU`. Establish `hUY : α ⁻¹ᵁ W = α ⁻¹ᵁ W ⊓ t ⁻¹ᵁ (M.gp ⁻¹ᵁ U)` using `(inf_eq_left.2 hle).symm`. Establish `po` using `(isIso_pushoutSection_iff hpb (US := U) (UT := M.gp ⁻¹ᵁ U) (UX := W) le_rfl hWU hUY).mp (isIso_pushoutSection_of_isAffineOpen hpb le_rfl hWU hUY hU hV hW)`.

Rewrite `po` using `[Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app]`. Use `letI : Algebra Γ(M.S, U) Γ(G.left, W) := (G.hom.appLE U W hWU).hom.toAlgebra`. Use `letI : Algebra Γ(M.S, U) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) := (M.gp.app U).hom.toAlgebra`. Use `letI : Algebra Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) := (α.app W).hom.toAlgebra`. Use `letI : Algebra Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) := (t.appLE (M.gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) hle).hom.toAlgebra`.

Use `letI : Algebra Γ(M.S, U) Γ(Y, α ⁻¹ᵁ W) := (G.hom.appLE U W hWU ≫ α.app W).hom.toAlgebra`. Use `haveI : IsScalarTower Γ(M.S, U) Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) := IsScalarTower.of_algebraMap_eq' rfl`. Use `haveI : IsScalarTower Γ(M.S, U) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom po.w)`. Use `haveI : Algebra.IsPushout Γ(M.S, U) Γ(G.left, W) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) := CommRingCat.isPushout_iff_isPushout.mp po`. Use `haveI : Algebra.Smooth Γ(M.S, U) Γ(G.left, W) := HasRingHomProperty.appLE @AlgebraicGeometry.Smooth G.hom hG ⟨U, hU⟩ ⟨W, hW⟩ hWU`.

Set `e` to `Algebra.IsPushout.equiv Γ(M.S, U) Γ(G.left, W) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W)`. Establish `hf' : IsIntegral Γ(G.left, W) f` using `hf`. Establish `hx : IsIntegral Γ(G.left, W) (e.symm f)` using `hf'.map e.symm.toAlgHom`. Take `⟨y, hy⟩` from `(TensorProduct.toIntegralClosure_bijective_of_smooth (R := Γ(M.S, U)) (S := Γ(G.left, W)) (B := Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U))).2 ⟨e.symm f, hx⟩`. Establish `hfy : f = e ((TensorProduct.toIntegralClosure Γ(M.S, U) Γ(G.left, W) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) y : _))`.

Rewrite using `[congrArg Subtype.val hy]`. Conclude with `(e.apply_symm_apply f).symm`. Rewrite using `[hfy]`. Use `clear hfy hy`. Proceed by induction on `y with`.

Consider the case `zero => exact ⟨0, Fin.elim0, Fin.elim0, fun m => m.elim0, by simp⟩`. Consider the case `tmul c b`. Use `⟨1, fun _ => c, fun _ => (b : Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U)), fun _ => b.2, ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_one]`. Conclude with `Algebra.IsPushout.equiv_tmul _ _ _ _ c (b : Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U))`.

Consider the case `add u v hu hv`. Rewrite using `[map_add, Subalgebra.coe_add, map_add]`. Conclude with `sumForm_add _ _ _ hu hv`.
-/
theorem eq_sum_of_isIntegral_genericChart : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S), Smooth G.hom → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)) (hpb : IsPullback α t G.hom M.gp) (W : G.left.Opens) (U : M.S.Opens) (hWU : W ≤ G.hom ⁻¹ᵁ U), IsAffineOpen W → IsAffineOpen U → ∀ f : Γ(Y, α ⁻¹ᵁ W), (α.app W).hom.IsIntegralElem f → ∃ (n : ℕ) (c : Fin n → Γ(G.left, W)) (b : Fin n → Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U)), (∀ m, (M.gp.app U).hom.IsIntegralElem (b m)) ∧ f = ∑ m, (α.app W).hom (c m) * (t.appLE (M.gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) (locInt_le_gen G.hom α t M.gp hpb.w W U hWU)).hom (b m) := by
  intro R _ _ M G hG Y α t hpb W U hWU hW hU f hf
  have hV : IsAffineOpen (M.gp ⁻¹ᵁ U) := isAffineOpen_Sp_field _ _
  have hle := locInt_le_gen G.hom α t M.gp hpb.w W U hWU
  have hUY : α ⁻¹ᵁ W = α ⁻¹ᵁ W ⊓ t ⁻¹ᵁ (M.gp ⁻¹ᵁ U) := (inf_eq_left.2 hle).symm
  have po := (isIso_pushoutSection_iff hpb (US := U) (UT := M.gp ⁻¹ᵁ U) (UX := W) le_rfl hWU hUY).mp
    (isIso_pushoutSection_of_isAffineOpen hpb le_rfl hWU hUY hU hV hW)
  rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app] at po
  letI : Algebra Γ(M.S, U) Γ(G.left, W) := (G.hom.appLE U W hWU).hom.toAlgebra
  letI : Algebra Γ(M.S, U) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) := (M.gp.app U).hom.toAlgebra
  letI : Algebra Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) := (α.app W).hom.toAlgebra
  letI : Algebra Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    (t.appLE (M.gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) hle).hom.toAlgebra
  letI : Algebra Γ(M.S, U) Γ(Y, α ⁻¹ᵁ W) := (G.hom.appLE U W hWU ≫ α.app W).hom.toAlgebra
  haveI : IsScalarTower Γ(M.S, U) Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(M.S, U) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom po.w)
  haveI : Algebra.IsPushout Γ(M.S, U) Γ(G.left, W) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    CommRingCat.isPushout_iff_isPushout.mp po
  haveI : Algebra.Smooth Γ(M.S, U) Γ(G.left, W) :=
    HasRingHomProperty.appLE @AlgebraicGeometry.Smooth G.hom hG ⟨U, hU⟩ ⟨W, hW⟩ hWU
  let e := Algebra.IsPushout.equiv Γ(M.S, U) Γ(G.left, W) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W)
  have hf' : IsIntegral Γ(G.left, W) f := hf
  have hx : IsIntegral Γ(G.left, W) (e.symm f) := hf'.map e.symm.toAlgHom
  obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth (R := Γ(M.S, U)) (S := Γ(G.left, W))
    (B := Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U))).2 ⟨e.symm f, hx⟩
  have hfy : f = e ((TensorProduct.toIntegralClosure Γ(M.S, U) Γ(G.left, W) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) y : _)) := by
    rw [congrArg Subtype.val hy]; exact (e.apply_symm_apply f).symm
  rw [hfy]
  clear hfy hy
  induction y with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun m => m.elim0, by simp⟩
  | tmul c b =>
    refine ⟨1, fun _ => c, fun _ => (b : Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U)), fun _ => b.2, ?_⟩
    rw [Fin.sum_univ_one]
    exact Algebra.IsPushout.equiv_tmul _ _ _ _ c (b : Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U))
  | add u v hu hv =>
    rw [map_add, Subalgebra.coe_add, map_add]
    exact sumForm_add _ _ _ hu hv

end GlobalTheory.Mum
