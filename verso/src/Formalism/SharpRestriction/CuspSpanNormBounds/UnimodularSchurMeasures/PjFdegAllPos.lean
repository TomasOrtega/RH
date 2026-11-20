import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.UnimodF
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.PjStarProj
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyProjectorSectionLocal

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def SepF (X : CData) : Prop := SecondCountableTopology X.I.Gf

def TensRep (X : CData) : Prop :=
  (∀ g h, X.σs (g * h) = X.σs g ∘L X.σs h) ∧ X.σs 1 = 1 ∧ (∀ g (x : X.Hs), ‖X.σs g x‖ = ‖x‖) ∧
    ∀ x : X.Hs, Continuous fun g => X.σs g x

abbrev muInf (X : CData) : Measure X.I.Ginf := Measure.pi fun v => Formalism.REAL.muG (X.I.ε v)

def SchurS (X : CData) : Prop :=
  ∀ x y : X.Hs, Integrable (fun g => ‖⟪y, X.σs g x⟫_ℂ‖ ^ 2) (muInf X) ∧
    ∫ g, ‖⟪y, X.σs g x⟫_ℂ‖ ^ 2 ∂(muInf X) = ‖x‖ ^ 2 * ‖y‖ ^ 2 / fdegAll X.I X.σ X.w

/- English proof (translation)
Unfold `fdegAll`. Use `Finset.prod_pos fun v _ => ?_` and prove the remaining obligations. Take `⟨d, hd⟩` from `h1 X.I.n (X.I.ε v) (X.lam v) (hX.1.2.2.2.2.1 v) (X.H v) (X.σ v) (hX.2.1.1 v)`. Rewrite using `[fdegOf_eq hd (hX.2.1.2.1 v).1]`. Conclude with `hd.1`.
-/
theorem pj_fdegAll_pos (D : Formalism.BasicNotions.D7) (h1 : adm1 D) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) :
    0 < fdegAll X.I X.σ X.w := by
  unfold fdegAll
  refine Finset.prod_pos fun v _ => ?_
  obtain ⟨d, hd⟩ := h1 X.I.n (X.I.ε v) (X.lam v) (hX.1.2.2.2.2.1 v) (X.H v) (X.σ v) (hX.2.1.1 v)
  rw [fdegOf_eq hd (hX.2.1.2.1 v).1]
  exact hd.1

/- English proof (translation)
Establish `h` using `hX.2.1.2.2.1.1 X.w X.w`. Establish `h2 : ∀ v, ⟪X.w v, X.w v⟫_ℂ = 1` using `fun v => by`. Rewrite using `[inner_self_eq_norm_sq_to_K, (hX.2.1.2.1 v).1]`. Simplify using the standard rewrite rules. Simplify using `only [h2, Finset.prod_const_one] at h`.

Establish `h3 : ‖X.tens X.w‖ ^ 2 = 1`. Rewrite using `[← inner_self_eq_norm_sq (𝕜 := ℂ), h]`. Simplify using the standard rewrite rules. Establish `h4 : (‖X.tens X.w‖ - 1) * (‖X.tens X.w‖ + 1) = 0` using `by ring_nf; linarith`. Break down `mul_eq_zero.1 h4 with h5 | h5` into its components or cases.

Combine the linear equalities and inequalities to obtain the conclusion. Use `norm_nonneg (X.tens X.w)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pj_norm_tens (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) : ‖X.tens X.w‖ = 1 := by
  have h := hX.2.1.2.2.1.1 X.w X.w
  have h2 : ∀ v, ⟪X.w v, X.w v⟫_ℂ = 1 := fun v => by
    rw [inner_self_eq_norm_sq_to_K, (hX.2.1.2.1 v).1]; simp
  simp only [h2, Finset.prod_const_one] at h
  have h3 : ‖X.tens X.w‖ ^ 2 = 1 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), h]; simp
  have h4 : (‖X.tens X.w‖ - 1) * (‖X.tens X.w‖ + 1) = 0 := by ring_nf; linarith
  rcases mul_eq_zero.1 h4 with h5 | h5
  · linarith
  · have := norm_nonneg (X.tens X.w); linarith

/- English proof (translation)
Rewrite using `[hX.2.1.2.2.1.2.1 g X.w, hX.2.1.2.2.1.1]`. Both sides reduce to the same expression.
-/
theorem pj_coef_tens (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (g : X.I.Ginf) :
    ⟪X.tens X.w, X.σs g (X.tens X.w)⟫_ℂ = ∏ v, coefOn (X.σ v) (X.w v) (X.w v) (g v) := by
  rw [hX.2.1.2.2.1.2.1 g X.w, hX.2.1.2.2.1.1]
  rfl

/- English proof (translation)
Establish `: SecondCountableTopology X.I.Gf` using `hSep`. Establish `: X.μf.IsMulRightInvariant` using `hUm`. Establish `: X.μf.IsHaarMeasure` using `hX.2.1.2.2.2.1`. Take `⟨hlc, hconv, hinv, hpos, -⟩` from `hX.1.2.2.2.2.2.2.1`. Take `⟨hei, heq⟩` from `hX.2.1.2.2.2.2.2.2`.

Establish `hbd : ∀ y, ‖X.e y‖ ≤ (X.e 1).re` using `Formalism.HermitianLatticeCounting.Final.S7.posTypeBound X.I.Gf X.e (positive_type_notation_eq X.I hpos)`. Distinguish the cases in `h0 : (X.e 1).re = 0`. Establish `he0 : ∀ y, X.e y = 0` using `fun y => norm_le_zero_iff.1 (h0 ▸ hbd y)`. Establish `: X.Re = 0` using `by ext1 y`. Use `ext_inner_left ℂ fun x => ?_` and prove the remaining obligations.

Rewrite using `[heq]`. Simplify using `[he0]`. Rewrite using `[this]`. Conclude with `⟨IsIdempotentElem.zero, IsSelfAdjoint.zero _⟩`. Establish `h1 : 0 < ‖X.e 1‖`.

Rewrite using `[norm_pos_iff]`. Introduce `h`. Conclude with `h0 (by rw [h]; rfl)`. Establish `hc : Continuous X.e` using `hlc.continuous`. Establish `: X.μf.IsInvInvariant` using `inv_invariant_of_bi_invariant X.μf (fun y => ‖X.e y‖) hc.norm hei.norm h1`.

Set `πf : X.I.Gf →* (X.L2 →L[ℂ] X.L2)` to `{ toFun := fun k => X.R (1, k) map_one' := hR.2.1 map_mul' := fun a b => by`. Rewrite using `[ContinuousLinearMap.mul_def, ← hR.1]`. Simplify using `}`. Use `pj_starProj X.μf X.e hc hei (fun g => by rw [hinv, star_star]) (fun y => congrFun hconv y) πf (fun g x => hR.2.2.1 _ x) (fun x => (hR.2.2.2 x).comp (by fun_prop)) X.Re ⟨hei, heq⟩` and prove the remaining obligations.
-/
theorem pj_Re_proj (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (hR : RepA X) (hUm : UnimodF X) (hSep : SepF X) :
    IsStarProjection X.Re := by
  have : SecondCountableTopology X.I.Gf := hSep
  have : X.μf.IsMulRightInvariant := hUm
  have : X.μf.IsHaarMeasure := hX.2.1.2.2.2.1
  obtain ⟨hlc, hconv, hinv, hpos, -⟩ := hX.1.2.2.2.2.2.2.1
  obtain ⟨hei, heq⟩ := hX.2.1.2.2.2.2.2.2
  have hbd : ∀ y, ‖X.e y‖ ≤ (X.e 1).re := Formalism.HermitianLatticeCounting.Final.S7.posTypeBound X.I.Gf X.e (positive_type_notation_eq X.I hpos)
  by_cases h0 : (X.e 1).re = 0
  · have he0 : ∀ y, X.e y = 0 := fun y => norm_le_zero_iff.1 (h0 ▸ hbd y)
    have : X.Re = 0 := by
      ext1 y
      refine ext_inner_left ℂ fun x => ?_
      rw [heq]
      simp [he0]
    rw [this]
    exact ⟨IsIdempotentElem.zero, IsSelfAdjoint.zero _⟩
  · have h1 : 0 < ‖X.e 1‖ := by
      rw [norm_pos_iff]
      intro h
      exact h0 (by rw [h]; rfl)
    have hc : Continuous X.e := hlc.continuous
    have : X.μf.IsInvInvariant := inv_invariant_of_bi_invariant X.μf (fun y => ‖X.e y‖) hc.norm hei.norm h1
    let πf : X.I.Gf →* (X.L2 →L[ℂ] X.L2) :=
      { toFun := fun k => X.R (1, k)
        map_one' := hR.2.1
        map_mul' := fun a b => by
          rw [ContinuousLinearMap.mul_def, ← hR.1]
          simp }
    refine pj_starProj X.μf X.e hc hei (fun g => by rw [hinv, star_star]) (fun y => congrFun hconv y) πf
      (fun g x => hR.2.2.1 _ x) (fun x => (hR.2.2.2 x).comp (by fun_prop)) X.Re ⟨hei, heq⟩

/- English proof (translation)
Establish `: SecondCountableTopology X.I.Gf` using `hSep`. Establish `: ∀ v, (Formalism.REAL.muG (X.I.ε v)).IsMulRightInvariant` using `fun v => ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular X.I.n (X.I.ε v) g⟩`. Establish `hd` using `pj_fdegAll_pos D h1 X hX`. Use `set d := fdegAll X.I X.σ X.w with hddef`. Establish `hw` using `pj_norm_tens X hX`.

Set `σH : X.I.Ginf →* (X.Hs →L[ℂ] X.Hs)` to `{ toFun := X.σs, map_one' := hTR.2.1, map_mul' := fun a b => hTR.1 a b }`. Set `π1 : X.I.Ginf →* (X.L2 →L[ℂ] X.L2)` to `{ toFun := fun g => X.R (g, 1) map_one' := hR.2.1 map_mul' := fun a b => by`. Rewrite using `[ContinuousLinearMap.mul_def, ← hR.1]`. Simplify using `}`. Establish `hphA : phOf X.I X.σ X.w = phA d σH (X.tens X.w)`.

Use function extensionality and compare the values at `g`. Unfold `phOf phA`. Rewrite using `[← pj_coef_tens X hX g]`. Both sides reduce to the same expression. Establish `hcoef : Integrable (fun g => ⟪X.tens X.w, σH g (X.tens X.w)⟫_ℂ) (muInf X)`.

Establish `h2 : Integrable (fun g => ((d : ℂ)⁻¹) * phOf X.I X.σ X.w g) (muInf X)` using `hph.const_mul _`. Establish `h3` using `(Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp h2`. Use `h3.congr (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Establish `hd0 : (d : ℂ) ≠ 0` using `by exact_mod_cast hd.ne'`. Rewrite using `[hphA]`.

Simplify using `only [phA]`. Rewrite using `[← mul_assoc, inv_mul_cancel₀ hd0, one_mul]`. Simplify using the standard rewrite rules. Take `⟨-, -, c3⟩` from `abstract_projector_statements_hold D X.I.Ginf (muInf X) X.Hs σH hTR.2.2.1 hTR.2.2.2 d hd hS (X.tens X.w) hw hcoef`. Take `⟨⟨P1, hP1⟩, c4⟩` from `c3 X.L2 π1 (fun g x => hR.2.2.1 _ x) (fun x => (hR.2.2.2 x).comp (by fun_prop))`.

Take `⟨hP1s, -, -, hrange⟩` from `c4 P1 hP1`. Establish `hRe` using `pj_Re_proj X hX hR hUm hSep`. Establish `hcyc` using `cyclic_of_schur_relation (muInf X) d hd σH hS (X.tens X.w) hw`. Establish `hcomm : ∀ g : X.I.Ginf, X.Re ∘L X.R (g, 1) = X.R (g, 1) ∘L X.Re` using `pj_comm X.μf X.R hR.1 X.e X.Re hX.2.1.2.2.2.2.2.2.2`. Establish `key : ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → T = P1 ∘L X.Re ∧ T = X.Re ∘L P1`.

Introduce `T hT`. Use `pj_fubini (muInf X) X.μf X.R hR.1 hR.2.2.1 (fun x y => (continuous_const.inner (hR.2.2.2 y)).aestronglyMeasurable) (phOf X.I X.σ X.w) X.e hT.1 P1 X.Re T ?_ hX.2.1.2.2.2.2.2.2.2 hT.2` and prove the remaining obligations. Introduce `x y`. Rewrite using `[hP1.2 x y, hphA]`. Both sides reduce to the same expression.

Establish `fin : ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → _` using `fun T hT => pj_counted X.σs (fun g => X.R (g, 1)) (X.tens X.w) P1 X.Re T hP1s hRe (key T hT).1 (key T hT).2 hrange hcomm hcyc (X.I.HomS X.σs X.μf X.fund X.R) (fun Ψ => Iff.rfl)`. Conclude with `⟨fun T hT => (fin T hT).1, fun T hT _ => (fin T hT).2⟩`.
-/
theorem pj_main (D : Formalism.BasicNotions.D7) (h1 : adm1 D) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A)
    (hph : Integrable (phOf X.I X.σ X.w) (muInf X))
    (hR : RepA X) (hUm : UnimodF X) (hSep : SepF X) (hTR : TensRep X) (hS : SchurS X) :
    X.ProjStep ∧ X.CountedStep := by
  have : SecondCountableTopology X.I.Gf := hSep
  have : ∀ v, (Formalism.REAL.muG (X.I.ε v)).IsMulRightInvariant :=
    fun v => ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular X.I.n (X.I.ε v) g⟩
  have hd := pj_fdegAll_pos D h1 X hX
  set d := fdegAll X.I X.σ X.w with hddef
  have hw := pj_norm_tens X hX
  let σH : X.I.Ginf →* (X.Hs →L[ℂ] X.Hs) :=
    { toFun := X.σs, map_one' := hTR.2.1, map_mul' := fun a b => hTR.1 a b }
  let π1 : X.I.Ginf →* (X.L2 →L[ℂ] X.L2) :=
    { toFun := fun g => X.R (g, 1)
      map_one' := hR.2.1
      map_mul' := fun a b => by
        rw [ContinuousLinearMap.mul_def, ← hR.1]
        simp }
  have hphA : phOf X.I X.σ X.w = phA d σH (X.tens X.w) := by
    funext g
    unfold phOf phA
    rw [← pj_coef_tens X hX g]
    rfl
  have hcoef : Integrable (fun g => ⟪X.tens X.w, σH g (X.tens X.w)⟫_ℂ) (muInf X) := by
    have h2 : Integrable (fun g => ((d : ℂ)⁻¹) * phOf X.I X.σ X.w g) (muInf X) := hph.const_mul _
    have h3 := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp h2
    refine h3.congr (Filter.Eventually.of_forall fun g => ?_)
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [hphA]
    simp only [phA]
    rw [← mul_assoc, inv_mul_cancel₀ hd0, one_mul]
    simp
  obtain ⟨-, -, c3⟩ := abstract_projector_statements_hold D X.I.Ginf (muInf X) X.Hs σH hTR.2.2.1 hTR.2.2.2 d hd hS (X.tens X.w) hw hcoef
  obtain ⟨⟨P1, hP1⟩, c4⟩ := c3 X.L2 π1 (fun g x => hR.2.2.1 _ x) (fun x => (hR.2.2.2 x).comp (by fun_prop))
  obtain ⟨hP1s, -, -, hrange⟩ := c4 P1 hP1
  have hRe := pj_Re_proj X hX hR hUm hSep
  have hcyc := cyclic_of_schur_relation (muInf X) d hd σH hS (X.tens X.w) hw
  have hcomm : ∀ g : X.I.Ginf, X.Re ∘L X.R (g, 1) = X.R (g, 1) ∘L X.Re :=
    pj_comm X.μf X.R hR.1 X.e X.Re hX.2.1.2.2.2.2.2.2.2
  have key : ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → T = P1 ∘L X.Re ∧ T = X.Re ∘L P1 := by
    intro T hT
    refine pj_fubini (muInf X) X.μf X.R hR.1 hR.2.2.1
      (fun x y => (continuous_const.inner (hR.2.2.2 y)).aestronglyMeasurable)
      (phOf X.I X.σ X.w) X.e hT.1 P1 X.Re T ?_ hX.2.1.2.2.2.2.2.2.2 hT.2
    intro x y
    rw [hP1.2 x y, hphA]
    rfl
  have fin : ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → _ := fun T hT =>
    pj_counted X.σs (fun g => X.R (g, 1)) (X.tens X.w) P1 X.Re T hP1s hRe (key T hT).1 (key T hT).2 hrange hcomm hcyc
      (X.I.HomS X.σs X.μf X.fund X.R) (fun Ψ => Iff.rfl)
  exact ⟨fun T hT => (fin T hT).1, fun T hT _ => (fin T hT).2⟩

end Formalism.MainNotions.LeviCoordinates

end
