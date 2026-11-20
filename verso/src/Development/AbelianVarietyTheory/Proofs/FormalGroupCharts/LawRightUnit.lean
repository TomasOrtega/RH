import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.WickOperatorVanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AxisPderivComp

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.ChartTrans

namespace GlobalTheory.HomChain

variable {k : Type} [CommRing k] {d : ℕ}

/- English proof (translation)
Establish `hs : ∀ j, GP ((![pt k (n` using `2) d 1, pt k (n := 2) d 0] : Fin 2 → Pt k 2 d) j) := pair_points_zero_constant (gp_pt 1) (gp_pt 0)`. Rewrite using `[← G.comm i, gt_ev_ev' _ _ axis_GP hs, eval_pair_points, evP_pt _ axis_GP, evP_pt _ axis_GP]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one]`. Conclude with `G.unit i`.
-/
theorem law_right_unit (G : FGLaw k d) (i : Fin d) :
    ev (n := 1) ![pt k (n := 1) d 0, 0] (G.F i) = (X ((0 : Fin 1), i) : PS k 1 d) := by
  have hs : ∀ j, GP ((![pt k (n := 2) d 1, pt k (n := 2) d 0] : Fin 2 → Pt k 2 d) j) :=
    pair_points_zero_constant (gp_pt 1) (gp_pt 0)
  rw [← G.comm i, gt_ev_ev' _ _ axis_GP hs, eval_pair_points, evP_pt _ axis_GP, evP_pt _ axis_GP]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact G.unit i

/- English proof (translation)
Establish `hφ : GP α` using `hα`. Establish `h0 : GP (comp1 α (pt k (n` using `2) d 0)) := gp_comp1 α _ hφ (gp_pt 0)`. Establish `h1 : GP (comp1 α (pt k (n` using `2) d 1)) := gp_comp1 α _ hφ (gp_pt 1)`. Establish `hΦ` using `pair_points_zero_constant h0 h1`. Establish `hF : GP G.F` using `G.const`.

Establish `hF' : GP G'.F` using `G'.const`. Establish `eF : G.add (pt k (n` using `2) d 0) (pt k (n := 2) d 1) = G.F := by`. Use function extensionality and compare the values at `i`. Establish `e : (![pt k (n` using `2) d 0, pt k (n := 2) d 1] : Fin 2 → Pt k 2 d) = pt k d := by`. Apply the tactic sequence `funext j; fin_cases j <;> rfl`.

Express the relevant statement in the definitionally equal form `ev ![pt k (n := 2) d 0, pt k (n := 2) d 1] (G.F i) = _`. Rewrite using `[e]`. Conclude with `congrFun (MvPowerSeries.subst_self (R := k) (σ := Fin 2 × Fin d)) (G.F i)`. Establish `key : ev (n` using `2) ![G.F] (ev (n := 1) ![α] g) = ev ![comp1 α (pt k (n := 2) d 0), comp1 α (pt k (n := 2) d 1)] (ev (n := 2) ![G'.F] g) := by`. Rewrite using `[gt_ev_ev' _ _ (single_point_zero_constant hF) (single_point_zero_constant hφ), vec1, gt_ev_ev' _ _ hΦ (single_point_zero_constant hF'), vec1]`.

Establish `: evP ![G.F] α = evP ![comp1 α (pt k (n` using `2) d 0), comp1 α (pt k (n := 2) d 1)] G'.F := by`. Rewrite `hom` using `[eF]`. Conclude with `hom`. Rewrite using `[this]`. Rewrite using `[dof_eq _ G.const (law_right_unit G), dof_eq _ G'.const (law_right_unit G'), key, ev_sum _ (single_point_zero_constant hφ)]`.

Simplify using `only [axis_pderiv_comp α hφ, ev_C_mul _ (single_point_zero_constant hφ)]`. Simplify using `only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dof_hom (G G' : FGLaw k d) (α : Pt k 1 d) (hα : ∀ i, constantCoeff (α i) = 0)
    (hom : comp1 α (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      G'.add (comp1 α (pt k (n := 2) d 0)) (comp1 α (pt k (n := 2) d 1)))
    (u : Fin d → k) (g : PS k 1 d) :
    Dof G.F u (ev (n := 1) ![α] g) = ev (n := 1) ![α] (Dof G'.F ((dLin α).mulVec u) g) := by
  have hφ : GP α := hα
  have h0 : GP (comp1 α (pt k (n := 2) d 0)) := gp_comp1 α _ hφ (gp_pt 0)
  have h1 : GP (comp1 α (pt k (n := 2) d 1)) := gp_comp1 α _ hφ (gp_pt 1)
  have hΦ := pair_points_zero_constant h0 h1
  have hF : GP G.F := G.const
  have hF' : GP G'.F := G'.const
  have eF : G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1) = G.F := by
    funext i
    have e : (![pt k (n := 2) d 0, pt k (n := 2) d 1] : Fin 2 → Pt k 2 d) = pt k d := by
      funext j; fin_cases j <;> rfl
    change ev ![pt k (n := 2) d 0, pt k (n := 2) d 1] (G.F i) = _
    rw [e]
    exact congrFun (MvPowerSeries.subst_self (R := k) (σ := Fin 2 × Fin d)) (G.F i)
  have key : ev (n := 2) ![G.F] (ev (n := 1) ![α] g) =
      ev ![comp1 α (pt k (n := 2) d 0), comp1 α (pt k (n := 2) d 1)] (ev (n := 2) ![G'.F] g) := by
    rw [gt_ev_ev' _ _ (single_point_zero_constant hF) (single_point_zero_constant hφ), vec1, gt_ev_ev' _ _ hΦ (single_point_zero_constant hF'), vec1]
    have : evP ![G.F] α = evP ![comp1 α (pt k (n := 2) d 0), comp1 α (pt k (n := 2) d 1)] G'.F := by
      rw [eF] at hom
      exact hom
    rw [this]
  rw [dof_eq _ G.const (law_right_unit G), dof_eq _ G'.const (law_right_unit G'), key,
    ev_sum _ (single_point_zero_constant hφ)]
  simp only [axis_pderiv_comp α hφ, ev_C_mul _ (single_point_zero_constant hφ)]
  simp only [Matrix.mulVec, dotProduct, map_sum,
    map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Introduce `k _ d G G' α hα hom ι _ u P g`. Establish `hφ : GP α` using `hα`. Establish `hit : ∀ (v : Fin d → k) (n : ℕ) (g : PS k 1 d), (Dof G.F v)^[n] (ev (n` using `1) ![α] g) = ev (n := 1) ![α] ((Dof G'.F ((dLin α).mulVec v))^[n] g) := by`. Introduce `v n`. Proceed by induction on `n with`.

Consider the case `zero => intro g`. Both sides reduce to the same expression. Consider the case `succ n ih`. Introduce `g`. Rewrite using `[Function.iterate_succ_apply, Function.iterate_succ_apply, dof_hom G G' α hα hom, ih]`.

Establish `hmon : ∀ m : ι →₀ ℕ, DmonOf G.F u m (ev (n` using `1) ![α] g) = ev (n := 1) ![α] (DmonOf G'.F (fun l => (dLin α).mulVec (u l)) m g) := by`. Introduce `m`. Unfold `DmonOf`. Proceed by induction on `(Finset.univ : Finset ι).toList with`. Consider the case `nil => rfl`.

Consider the case `cons a L ih => rw [List.foldr_cons, List.foldr_cons, ih, hit]`. Unfold `DpolyOf`. Rewrite using `[ev_sum _ (single_point_zero_constant hφ)]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[ev_C_mul _ (single_point_zero_constant hφ), hmon]`.
-/
theorem dpolyOf_hom :
    ∀ (k : Type) [CommRing k] (d : ℕ) (G G' : FGLaw k d) (α : Pt k 1 d),
      (∀ i, constantCoeff (α i) = 0) →
      comp1 α (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
        G'.add (comp1 α (pt k (n := 2) d 0)) (comp1 α (pt k (n := 2) d 1)) →
      ∀ (Λ : Type) [Fintype Λ] (u : Λ → Fin d → k) (Q : MvPolynomial Λ k) (g : PS k 1 d),
        DpolyOf G.F u Q (ev (n := 1) ![α] g) =
          ev (n := 1) ![α] (DpolyOf G'.F (fun l => (dLin α).mulVec (u l)) Q g) := by
  intro k _ d G G' α hα hom ι _ u P g
  have hφ : GP α := hα
  have hit : ∀ (v : Fin d → k) (n : ℕ) (g : PS k 1 d),
      (Dof G.F v)^[n] (ev (n := 1) ![α] g) =
        ev (n := 1) ![α] ((Dof G'.F ((dLin α).mulVec v))^[n] g) := by
    intro v n
    induction n with
    | zero => intro g; rfl
    | succ n ih =>
      intro g
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, dof_hom G G' α hα hom, ih]
  have hmon : ∀ m : ι →₀ ℕ, DmonOf G.F u m (ev (n := 1) ![α] g) =
      ev (n := 1) ![α] (DmonOf G'.F (fun l => (dLin α).mulVec (u l)) m g) := by
    intro m
    unfold DmonOf
    induction (Finset.univ : Finset ι).toList with
    | nil => rfl
    | cons a L ih => rw [List.foldr_cons, List.foldr_cons, ih, hit]
  unfold DpolyOf
  rw [ev_sum _ (single_point_zero_constant hφ)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ev_C_mul _ (single_point_zero_constant hφ), hmon]

end GlobalTheory.HomChain
