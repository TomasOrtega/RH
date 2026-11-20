import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.DlogCocycle

/- English proof (translation)
Simplify using `only [resG]`. Rewrite using `[← CommRingCat.comp_apply, ← Functor.map_comp]`. Both sides reduce to the same expression.
-/
theorem resG_resG {X : Scheme.{0}} {U V T : X.Opens} (h : V ≤ U) (h' : T ≤ V) (f : Γ(X, U)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem res_val {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) :
    (res h u).val = resG X h u.val := rfl

/- English proof (translation)
Rewrite using `[map_mul, ← hd.2.2 A T hTA hA, resG_resG, resG_resG]`.
-/
theorem resG_dlog {Z : Scheme.{0}} {W₀ : Z.Opens} {d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)} (hd : IsField W₀ d)
    {P A T : Z.Opens} (hA : A ≤ W₀) (hTA : T ≤ A) (hAP : A ≤ P) (u : Γ(Z, P)ˣ) :
    resG Z hTA (d A (resG Z hAP u.val) * resG Z hAP u⁻¹.val) =
      d T (resG Z (hTA.trans hAP) u.val) * resG Z (hTA.trans hAP) u⁻¹.val := by
  rw [map_mul, ← hd.2.2 A T hTA hA, resG_resG, resG_resG]

/- English proof (translation)
Introduce `Z L hL W₀ d hd J W j hW hj i i' i''`. Establish `hT0 : W i ⊓ W i' ⊓ W i'' ≤ W₀` using `inf_le_left.trans (inf_le_left.trans (hW i))`. Establish `hT : W i ⊓ W i' ⊓ W i'' ≤ L.U (j i) ⊓ L.U (j i') ⊓ L.U (j i'')` using `inf_le_inf (inf_le_inf (hj i) (hj i')) (hj i'')`. Rewrite using `[resG_dlog hd ((inf_le_left : W i ⊓ W i' ≤ W i).trans (hW i)), resG_dlog hd ((inf_le_left : W i' ⊓ W i'' ≤ W i').trans (hW i')), resG_dlog hd ((inf_le_left : W i ⊓ W i'' ≤ W i).trans (hW i))]`. Establish `e` using `congrArg (fun u => resG Z hT u.val) (hL.cocycle (j i) (j i') (j i''))`.

Simplify using `only [Units.val_mul, map_mul, res_val, resG_resG] at e`. Establish `inv : ∀ {P : Z.Opens} (h : W i ⊓ W i' ⊓ W i'' ≤ P) (u : Γ(Z, P)ˣ), resG Z h u.val * resG Z h u⁻¹.val = 1` using `fun h u => by rw [← map_mul, Units.mul_inv, map_one]`. Establish `e1` using `inv (((inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i').trans (inf_le_inf (hj i) (hj i')))) (L.g (j i) (j i'))`. Establish `e2` using `inv ((le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'').trans (inf_le_inf (hj i') (hj i''))) (L.g (j i') (j i''))`. Establish `e3` using `inv ((le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'').trans (inf_le_inf (hj i) (hj i''))) (L.g (j i) (j i''))`.

Generalize the expression as in `resG Z _ (L.g (j i) (j i')).val = x1 at e e1 ⊢`. Generalize the expression as in `resG Z _ (L.g (j i') (j i'')).val = x2 at e e2 ⊢`. Generalize the expression as in `resG Z _ (L.g (j i) (j i'')).val = x3 at e e3 ⊢`. Generalize the expression as in `resG Z _ (L.g (j i) (j i'))⁻¹.val = y1 at e1 ⊢`. Generalize the expression as in `resG Z _ (L.g (j i') (j i''))⁻¹.val = y2 at e2 ⊢`.

Generalize the expression as in `resG Z _ (L.g (j i) (j i''))⁻¹.val = y3 at e3 ⊢`. Establish `hy3 : y3 = y1 * y2`. Take the linear combination `(-y3 * x2 * y2) * e1 - y3 * e2 + y1 * y2 * e3 + y1 * y2 * y3 * e`. Rewrite using `[← e, hd.2.1 _ hT0, hy3]`. Take the linear combination `(-(d _ x2 * y2)) * e1 - (d _ x1 * y1) * e2`.
-/
theorem dlog_cocycle : ∀ (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (W₀ : Z.Opens) (d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)), IsField W₀ d → ∀ (J : Type) (W : J → Z.Opens) (j : J → L.ι), (∀ i, W i ≤ W₀) → ∀ (hj : ∀ i, W i ≤ L.U (j i)) (i i' i'' : J), resG Z (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (d (W i ⊓ W i') (resG Z (inf_le_inf (hj i) (hj i')) (L.g (j i) (j i')).val) * resG Z (inf_le_inf (hj i) (hj i')) (L.g (j i) (j i'))⁻¹.val) + resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (d (W i' ⊓ W i'') (resG Z (inf_le_inf (hj i') (hj i'')) (L.g (j i') (j i'')).val) * resG Z (inf_le_inf (hj i') (hj i'')) (L.g (j i') (j i''))⁻¹.val) = resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (d (W i ⊓ W i'') (resG Z (inf_le_inf (hj i) (hj i'')) (L.g (j i) (j i'')).val) * resG Z (inf_le_inf (hj i) (hj i'')) (L.g (j i) (j i''))⁻¹.val) := by
  intro Z L hL W₀ d hd J W j hW hj i i' i''
  have hT0 : W i ⊓ W i' ⊓ W i'' ≤ W₀ := inf_le_left.trans (inf_le_left.trans (hW i))
  have hT : W i ⊓ W i' ⊓ W i'' ≤ L.U (j i) ⊓ L.U (j i') ⊓ L.U (j i'') :=
    inf_le_inf (inf_le_inf (hj i) (hj i')) (hj i'')
  rw [resG_dlog hd ((inf_le_left : W i ⊓ W i' ≤ W i).trans (hW i)),
    resG_dlog hd ((inf_le_left : W i' ⊓ W i'' ≤ W i').trans (hW i')),
    resG_dlog hd ((inf_le_left : W i ⊓ W i'' ≤ W i).trans (hW i))]
  have e := congrArg (fun u => resG Z hT u.val) (hL.cocycle (j i) (j i') (j i''))
  simp only [Units.val_mul, map_mul, res_val, resG_resG] at e
  have inv : ∀ {P : Z.Opens} (h : W i ⊓ W i' ⊓ W i'' ≤ P) (u : Γ(Z, P)ˣ),
      resG Z h u.val * resG Z h u⁻¹.val = 1 := fun h u => by rw [← map_mul, Units.mul_inv, map_one]
  have e1 := inv (((inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i').trans (inf_le_inf (hj i) (hj i'))))
    (L.g (j i) (j i'))
  have e2 := inv ((le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'').trans
    (inf_le_inf (hj i') (hj i''))) (L.g (j i') (j i''))
  have e3 := inv ((le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'').trans
    (inf_le_inf (hj i) (hj i''))) (L.g (j i) (j i''))
  generalize resG Z _ (L.g (j i) (j i')).val = x1 at e e1 ⊢
  generalize resG Z _ (L.g (j i') (j i'')).val = x2 at e e2 ⊢
  generalize resG Z _ (L.g (j i) (j i'')).val = x3 at e e3 ⊢
  generalize resG Z _ (L.g (j i) (j i'))⁻¹.val = y1 at e1 ⊢
  generalize resG Z _ (L.g (j i') (j i''))⁻¹.val = y2 at e2 ⊢
  generalize resG Z _ (L.g (j i) (j i''))⁻¹.val = y3 at e3 ⊢
  have hy3 : y3 = y1 * y2 := by
    linear_combination (-y3 * x2 * y2) * e1 - y3 * e2 + y1 * y2 * e3 + y1 * y2 * y3 * e
  rw [← e, hd.2.1 _ hT0, hy3]
  linear_combination (-(d _ x2 * y2)) * e1 - (d _ x1 * y1) * e2

end GlobalTheory.DlogCocycle
