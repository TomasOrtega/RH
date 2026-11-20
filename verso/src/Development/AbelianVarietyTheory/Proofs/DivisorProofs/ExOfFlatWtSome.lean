import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PlaceShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMapToModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPoint

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G GlobalTheory.Frames GlobalTheory.HTLat
open scoped NNReal

namespace GlobalTheory.FlatFrameLaw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

open Classical in

/- English proof (translation)
Distinguish the cases in `h1 : σ = τ.1`. Substitute `h1` using the available equality. Establish `hi : (i : ℕ) < Dw.p`. Use `i.2` as an intermediate fact. Simplify using `only [Datum.mult, if_pos τ.2] at this`.

Conclude with `this`. Rewrite using `[if_pos rfl]`. Use `show (wtOf Dw (flatWt Dw τ) 0).1 (τ.1, i) = -1`. Rewrite using `[wtOf_big _ _ τ i hi]`. Simplify using `[flatWt, parWt]`.

Rewrite using `[if_neg h1]`. Distinguish the cases in `h2 : σ = conjEmb τ.1`. Substitute `h2` using the available equality. Establish `hi : (i : ℕ) < Dw.q`. Use `i.2` as an intermediate fact.

Simplify using `only [Datum.mult, if_neg (conj_not_mem τ)] at this`. Conclude with `this`. Rewrite using `[if_pos rfl]`. Use `show (wtOf Dw (flatWt Dw τ) 0).1 (conjEmb τ.1, i) = 1`. Rewrite using `[wtOf_small _ _ τ i hi]`.

Simplify using `[flatWt, parWt]`. Rewrite using `[if_neg h2] show (wtOf Dw (flatWt Dw τ) 0).1 (σ, i) = 0`. Simplify using `only [wtOf]`. Use `split_ifs with h h' h''`. Establish `hne : (⟨σ, h⟩ : Psi H) ≠ τ` using `fun e => h1 (congrArg Subtype.val e)`.

Simplify using `[flatWt, parWt, hne]`. Both sides reduce to the same expression. Establish `hne : (⟨conjEmb σ, h''⟩ : Psi H) ≠ τ` using `fun e => h2 (by`. Rewrite using `[← congrArg Subtype.val e, GlobalTheory.AllWt.conjEmb_conjEmb])`. Simplify using `[flatWt, parWt, hne]`.

Both sides reduce to the same expression. Both sides reduce to the same expression.
-/
theorem exOf_flatWt_some (τ : Psi H) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    exOf Dw (flatWt Dw τ) 0 (some ⟨σ, i⟩) =
      if σ = τ.1 then -1 else if σ = conjEmb τ.1 then 1 else 0 := by
  by_cases h1 : σ = τ.1
  · subst h1
    have hi : (i : ℕ) < Dw.p := by
      have := i.2; simp only [Datum.mult, if_pos τ.2] at this; exact this
    rw [if_pos rfl]
    show (wtOf Dw (flatWt Dw τ) 0).1 (τ.1, i) = -1
    rw [wtOf_big _ _ τ i hi]; simp [flatWt, parWt]
  · rw [if_neg h1]
    by_cases h2 : σ = conjEmb τ.1
    · subst h2
      have hi : (i : ℕ) < Dw.q := by
        have := i.2; simp only [Datum.mult, if_neg (conj_not_mem τ)] at this; exact this
      rw [if_pos rfl]
      show (wtOf Dw (flatWt Dw τ) 0).1 (conjEmb τ.1, i) = 1
      rw [wtOf_small _ _ τ i hi]; simp [flatWt, parWt]
    · rw [if_neg h2]
      show (wtOf Dw (flatWt Dw τ) 0).1 (σ, i) = 0
      simp only [wtOf]
      split_ifs with h h' h''
      · have hne : (⟨σ, h⟩ : Psi H) ≠ τ := fun e => h1 (congrArg Subtype.val e)
        simp [flatWt, parWt, hne]
      · rfl
      · have hne : (⟨conjEmb σ, h''⟩ : Psi H) ≠ τ := fun e => h2 (by
          rw [← congrArg Subtype.val e, GlobalTheory.AllWt.conjEmb_conjEmb])
        simp [flatWt, parWt, hne]
      · rfl
      · rfl

/- English proof (translation)
Simplify using `[exOf, exZ, wtOf]`.
-/
theorem exOf_flatWt_none (τ : Psi H) : exOf Dw (flatWt Dw τ) 0 none = 0 := by
  simp [exOf, exZ, wtOf]

/- English proof (translation)
Introduce `e` and use `conj_not_mem τ (e ▸ τ.2)`.
-/
theorem ne_conjEmb (τ : Psi H) : τ.1 ≠ conjEmb τ.1 := fun e => conj_not_mem τ (e ▸ τ.2)

end GlobalTheory.FlatFrameLaw

namespace GlobalTheory.FlatFrameLaw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

/- English proof (translation)
Establish `hdiag : ∀ σ, (g σ).det = ∏ i, g σ i i` using `fun σ => Matrix.det_of_lowerTriangular _ fun i j hij => hg σ i j hij`. Establish `hd : ∀ σ i, g σ i i ≠ 0` using `fun σ i => by`. Establish `hu` using `(hdet σ).ne_zero`. Rewrite `hu` using `[hdiag σ]`. Conclude with `Finset.prod_ne_zero_iff.1 hu i (Finset.mem_univ i)`.

Take `⟨h1, h2, pm, h3, h4, h5⟩` from `hch`. Set `t : Ix Dw → Cˣ` to `fun i => Option.rec (Units.mk0 a ha) (fun s => Units.mk0 _ (hd s.1 s.2)) i`. Establish `hb : FrBor t z y`. Use `⟨h1, fun σ i => ⟨g σ i, rfl, hg σ i, h2 σ i⟩, pm, h3, ?_, h5⟩` and prove the remaining obligations. Rewrite using `[h4, show spMap (RingHom.id C) = 𝟙 _ from Spec.map_id _]`.

Conclude with `Category.comp_id _`. Rewrite using `[GlobalTheory.FlagTan.evR_frBor hf hb]`. Use `congr 1`. Rewrite using `[Units.coe_prod, Fintype.prod_option, Fintype.prod_sigma]`. Establish `hF : ∀ σ, ∏ i : Fin (Dw.mult σ), ((t (some ⟨σ, i⟩) ^ exOf Dw (flatWt Dw τ) 0 (some ⟨σ, i⟩) : Cˣ) : C) = if σ = τ.1 then ((g σ).det)⁻¹ else if σ = conjEmb τ.1 then (g σ).det else 1` using `fun σ => by`.

Simplify using `only [exOf_flatWt_some, t, Units.val_zpow_eq_zpow_val, Units.val_mk0]`. Distinguish the cases in `e1 : σ = τ.1`. Simplify using `only [if_pos e1, zpow_neg_one, Finset.prod_inv_distrib, hdiag]`. Distinguish the cases in `e2 : σ = conjEmb τ.1`. Simplify using `only [if_neg e1, if_pos e2, zpow_one, hdiag]`.

Simplify using `only [if_neg e1, if_neg e2, zpow_zero, Finset.prod_const_one]`. Simplify using `only [hF, exOf_flatWt_none, zpow_zero, Units.val_one, one_mul]`. Rewrite using `[Fintype.prod_eq_mul τ.1 (conjEmb τ.1) (ne_conjEmb τ) fun σ hσ => by rw [if_neg hσ.1, if_neg hσ.2], if_pos rfl, if_neg (ne_conjEmb τ).symm, if_pos rfl]`.
-/
theorem evR_flat_frChg {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (τ : Psi H) {f : Rul Xo c}
    (hf : f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0)) {C : Type} [Field C] [Algebra c.F C]
    (g : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) C) (a : C)
    (z y : FrPt Xo c C) (hch : FrChg g a z y) (hg : ∀ σ i j, i < j → g σ i j = 0)
    (hdet : ∀ σ, IsUnit (g σ).det) (ha : a ≠ 0) :
    evR Xo c f y = ((g τ.1).det)⁻¹ * (g (conjEmb τ.1)).det * evR Xo c f z := by
  classical
  have hdiag : ∀ σ, (g σ).det = ∏ i, g σ i i := fun σ =>
    Matrix.det_of_lowerTriangular _ fun i j hij => hg σ i j hij
  have hd : ∀ σ i, g σ i i ≠ 0 := fun σ i => by
    have hu := (hdet σ).ne_zero
    rw [hdiag σ] at hu
    exact Finset.prod_ne_zero_iff.1 hu i (Finset.mem_univ i)
  obtain ⟨h1, h2, pm, h3, h4, h5⟩ := hch
  let t : Ix Dw → Cˣ := fun i => Option.rec (Units.mk0 a ha) (fun s => Units.mk0 _ (hd s.1 s.2)) i
  have hb : FrBor t z y := by
    refine ⟨h1, fun σ i => ⟨g σ i, rfl, hg σ i, h2 σ i⟩, pm, h3, ?_, h5⟩
    rw [h4, show spMap (RingHom.id C) = 𝟙 _ from Spec.map_id _]
    exact Category.comp_id _
  rw [GlobalTheory.FlagTan.evR_frBor hf hb]
  congr 1
  rw [Units.coe_prod, Fintype.prod_option, Fintype.prod_sigma]
  have hF : ∀ σ, ∏ i : Fin (Dw.mult σ), ((t (some ⟨σ, i⟩) ^ exOf Dw (flatWt Dw τ) 0 (some ⟨σ, i⟩) : Cˣ) : C) =
      if σ = τ.1 then ((g σ).det)⁻¹ else if σ = conjEmb τ.1 then (g σ).det else 1 := fun σ => by
    simp only [exOf_flatWt_some, t, Units.val_zpow_eq_zpow_val, Units.val_mk0]
    by_cases e1 : σ = τ.1
    · simp only [if_pos e1, zpow_neg_one, Finset.prod_inv_distrib, hdiag]
    · by_cases e2 : σ = conjEmb τ.1
      · simp only [if_neg e1, if_pos e2, zpow_one, hdiag]
      · simp only [if_neg e1, if_neg e2, zpow_zero, Finset.prod_const_one]
  simp only [hF, exOf_flatWt_none, zpow_zero, Units.val_one, one_mul]
  rw [Fintype.prod_eq_mul τ.1 (conjEmb τ.1) (ne_conjEmb τ) fun σ hσ => by rw [if_neg hσ.1, if_neg hσ.2],
    if_pos rfl, if_neg (ne_conjEmb τ).symm, if_pos rfl]

end GlobalTheory.FlatFrameLaw
