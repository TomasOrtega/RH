import Formalism.SharpRestriction.Divisibility.GeneratorPowers.HasSubstActPS

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

def ptm (C : ChartAt Xo c y) {n : ℕ} (P : Fin n → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (m : ℕ) :
    jO y (dL Dw) m 1 ⟶ jO y C.d m n :=
  homAt y.x (jetSubstPS (m := m) (fun p : Fin n × Fin C.d => P p.1 p.2))

/- English proof (translation)
Unfold `ptm`. Use `congrArg (homAt y.x) (GermD.jet_hom_ext fun q => ?_)` and prove the remaining obligations. Conclude with `(ExpGF.jetSubstPS_X m (fun p : Fin n × Fin C.d => P p.1 p.2) (fun p => hP p.1 p.2) q).trans ((h q.1 q.2).trans (ExpGF.jetSubstPS_X m (fun p : Fin n × Fin C.d => P' p.1 p.2) (fun p => hP' p.1 p.2) q).symm)`.
-/
theorem ptm_congr (C : ChartAt Xo c y) {n : ℕ} {P P' : Fin n → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S}
    (hP : ∀ i j, MvPowerSeries.constantCoeff (P i j) = 0) (hP' : ∀ i j, MvPowerSeries.constantCoeff (P' i j) = 0)
    (m : ℕ) (h : ∀ i j, psJet m (P i j) = psJet m (P' i j)) : ptm C P m = ptm C P' m := by
  unfold ptm
  refine congrArg (homAt y.x) (GermD.jet_hom_ext fun q => ?_)
  exact (ExpGF.jetSubstPS_X m (fun p : Fin n × Fin C.d => P p.1 p.2) (fun p => hP p.1 p.2) q).trans
    ((h q.1 q.2).trans (ExpGF.jetSubstPS_X m (fun p : Fin n × Fin C.d => P' p.1 p.2) (fun p => hP' p.1 p.2) q).symm)

/- English proof (translation)
Simplify using `only [actP, actPS, MvPolynomial.coe_mul, MvPolynomial.coe_C, MvPolynomial.coe_X]`. Rewrite using `[← MvPowerSeries.smul_eq_C_mul, algebraMap_smul]`.
-/
theorem coe_actP (u : 𝓞 E) (q : Fin 1 × Fin (dL Dw)) :
    ((actP (Dw := Dw) (S := S) c u q : MvPolynomial _ S) : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) =
      actPS (Dw := Dw) (S := S) c u q := by
  simp only [actP, actPS, MvPolynomial.coe_mul, MvPolynomial.coe_C, MvPolynomial.coe_X]
  rw [← MvPowerSeries.smul_eq_C_mul, algebraMap_smul]

/- English proof (translation)
Simplify using `[actP]`.
-/
theorem cc_actP (u : 𝓞 E) (q : Fin 1 × Fin (dL Dw)) :
    MvPolynomial.constantCoeff (actP (Dw := Dw) (S := S) c u q) = 0 := by
  simp [actP]

/- English proof (translation)
Rewrite using `[ExpGF.jetSubstP_eq_jetSubstPS m _ (fun q => cc_actP u q)]`. Use `congr 1`. Use function extensionality and compare the values at `q`. Conclude with `coe_actP u q`.
-/
theorem jetSubstP_actP (m : ℕ) (u : 𝓞 E) :
    jetSubstP m (actP (Dw := Dw) (S := S) c u) = jetSubstPS (m := m) (actPS (Dw := Dw) (S := S) c u) := by
  rw [ExpGF.jetSubstP_eq_jetSubstPS m _ (fun q => cc_actP u q)]
  congr 1
  funext q
  exact coe_actP u q

/- English proof (translation)
Unfold `ptm`. Rewrite using `[GermD.homAt_comp, jetSubstP_actP, ExpGF.jetSubstPS_comp m (fun p : Fin n × Fin C.d => P p.1 p.2) (actPS (Dw := Dw) (S := S) c u) (fun p => hP p.1 p.2) (const_actPS c u)]`.
-/
theorem sA_ptm (C : ChartAt Xo c y) {n : ℕ} (P : Fin n → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hP : ∀ i j, MvPowerSeries.constantCoeff (P i j) = 0) (m : ℕ) (u : 𝓞 E) :
    homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c u)) ≫ ptm C P m =
      ptm C (fun i j => MvPowerSeries.subst (actPS (Dw := Dw) (S := S) c u) (P i j)) m := by
  unfold ptm
  rw [GermD.homAt_comp, jetSubstP_actP,
    ExpGF.jetSubstPS_comp m (fun p : Fin n × Fin C.d => P p.1 p.2) (actPS (Dw := Dw) (S := S) c u)
      (fun p => hP p.1 p.2) (const_actPS c u)]

/- English proof (translation)
Establish `hs : MvPowerSeries.HasSubst (fun p : Fin n × Fin C.d => P p.1 p.2)` using `by first`. Consider the case `exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => hP p.1 p.2)`. Consider the case `exact MvPowerSeries.HasSubst.of_constantCoeff_zero (fun p => hP p.1 p.2)`. Consider the case `exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun q => by rw [(fun p => hP p.1 p.2) q]; exact IsNilpotent.zero)`. Unfold `ptm`.

Rewrite using `[GermD.homAt_comp, ExpGF.jetCopy_eq_PS, ExpGF.jetSubstPS_comp m (fun p : Fin 1 × Fin C.d => (MvPowerSeries.X (i, p.2) : MvPowerSeries (Fin n × Fin C.d) S)) (fun p : Fin n × Fin C.d => P p.1 p.2) (fun p => MvPowerSeries.constantCoeff_X _) (fun p => hP p.1 p.2)]`. Use `congrArg (homAt y.x) (congrArg (jetSubstPS (m := m)) ?_)` and prove the remaining obligations. Use function extensionality and compare the values at `p`. Take `⟨a, j⟩` from `p`. Use `fin_cases a`.

Simplify using `[MvPowerSeries.subst_X hs]`.
-/
theorem ptm_copy (C : ChartAt Xo c y) {n : ℕ} (P : Fin n → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hP : ∀ i j, MvPowerSeries.constantCoeff (P i j) = 0) (m : ℕ) (i : Fin n) :
    ptm C P m ≫ homAt y.x (jetCopy C.d m i) = ptm C ![P i] m := by
  have hs : MvPowerSeries.HasSubst (fun p : Fin n × Fin C.d => P p.1 p.2) := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => hP p.1 p.2)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero (fun p => hP p.1 p.2)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun q => by rw [(fun p => hP p.1 p.2) q]; exact IsNilpotent.zero)
  unfold ptm
  rw [GermD.homAt_comp, ExpGF.jetCopy_eq_PS,
    ExpGF.jetSubstPS_comp m (fun p : Fin 1 × Fin C.d => (MvPowerSeries.X (i, p.2) : MvPowerSeries (Fin n × Fin C.d) S))
      (fun p : Fin n × Fin C.d => P p.1 p.2) (fun p => MvPowerSeries.constantCoeff_X _) (fun p => hP p.1 p.2)]
  refine congrArg (homAt y.x) (congrArg (jetSubstPS (m := m)) ?_)
  funext p
  obtain ⟨a, j⟩ := p
  fin_cases a
  simp [MvPowerSeries.subst_X hs]

/- English proof (translation)
Unfold `ptm`. Rewrite using `[GermD.homAt_comp, ExpGF.jetSubstP_eq_jetSubstPS m σ hσ, ExpGF.jetSubstPS_comp m (fun k => ((σ k : MvPolynomial _ S) : MvPowerSeries (Fin n × Fin C.d) S)) (fun p : Fin n × Fin C.d => P p.1 p.2) (fun k => by`. Establish `h0 : MvPolynomial.coeff 0 (σ k) = 0` using `hσ k`. Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe, h0]) (fun p => hP p.1 p.2)]`.
-/
theorem ptm_subst (C : ChartAt Xo c y) {n n' : ℕ} (P : Fin n → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hP : ∀ i j, MvPowerSeries.constantCoeff (P i j) = 0) (m : ℕ)
    (σ : Fin n' × Fin C.d → MvPolynomial (Fin n × Fin C.d) S) (hσ : ∀ k, MvPolynomial.constantCoeff (σ k) = 0) :
    ptm C P m ≫ homAt y.x (jetSubstP m σ) =
      ptm C (fun i j => MvPowerSeries.subst (fun p : Fin n × Fin C.d => P p.1 p.2)
        ((σ (i, j) : MvPolynomial _ S) : MvPowerSeries (Fin n × Fin C.d) S)) m := by
  unfold ptm
  rw [GermD.homAt_comp, ExpGF.jetSubstP_eq_jetSubstPS m σ hσ,
    ExpGF.jetSubstPS_comp m (fun k => ((σ k : MvPolynomial _ S) : MvPowerSeries (Fin n × Fin C.d) S))
      (fun p : Fin n × Fin C.d => P p.1 p.2) (fun k => by
        have h0 : MvPolynomial.coeff 0 (σ k) = 0 := hσ k
        rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe, h0]) (fun p => hP p.1 p.2)]

/- English proof (translation)
Establish `e : (fun p : Fin 1 × Fin C.d => φ p.2) = (fun p : Fin 1 × Fin C.d => (![φ] : Fin 1 → _) p.1 p.2)`. Use function extensionality and compare the values at `p`. Take `⟨a, j⟩` from `p`. Use `fin_cases a`. Both sides reduce to the same expression.

Unfold `ptm jφ`. Rewrite using `[e]`.
-/
theorem jφ_eq (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (m : ℕ) :
    homAt y.x (jφ φ m) = ptm C ![φ] m := by
  have e : (fun p : Fin 1 × Fin C.d => φ p.2) = (fun p : Fin 1 × Fin C.d => (![φ] : Fin 1 → _) p.1 p.2) := by
    funext p
    obtain ⟨a, j⟩ := p
    fin_cases a
    rfl
  unfold ptm jφ
  rw [e]

/- English proof (translation)
Establish `hP : ∀ i j, MvPowerSeries.constantCoeff ((![φ] : Fin 1 → _) i j) = 0`. Introduce `i j`. Use `fin_cases i`. Conclude with `hφ j`. Establish `e : (fun i j => MvPowerSeries.subst (actPS (Dw` using `Dw) (S := S) c u) ((![φ] : Fin 1 → _) i j)) = ![φa c φ u] := by`.

Use function extensionality and compare the values at `i j`. Use `fin_cases i`. Both sides reduce to the same expression. Rewrite using `[hx.act m u, xExp, ← Category.assoc, jφ_eq, sA_ptm C _ hP m u, e]`.
-/
theorem exp_chart_action_point (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (hx : IsExpChart y (xExp y C φ)) (m : ℕ) (u : 𝓞 E) :
    xExp y C φ m ≫ Xo.univ.t.act.act u = ptm C ![φa c φ u] m ≫ C.x m := by
  have hP : ∀ i j, MvPowerSeries.constantCoeff ((![φ] : Fin 1 → _) i j) = 0 := by
    intro i j
    fin_cases i
    exact hφ j
  have e : (fun i j => MvPowerSeries.subst (actPS (Dw := Dw) (S := S) c u) ((![φ] : Fin 1 → _) i j)) =
      ![φa c φ u] := by
    funext i j
    fin_cases i
    rfl
  rw [hx.act m u, xExp, ← Category.assoc, jφ_eq, sA_ptm C _ hP m u, e]

/- English proof (translation)
Establish `hP : ∀ k j, MvPowerSeries.constantCoeff (φa c φ (us k) j) = 0` using `fun k j => const_φa c φ hφ (us k) j`. Rewrite using `[jpt, ← Category.assoc, ptm_copy C _ hP m i, exp_chart_action_point C φ hφ hx m (us i)]`.
-/
theorem ptm_jpt (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (hx : IsExpChart y (xExp y C φ)) (m : ℕ) {n : ℕ}
    (us : Fin n → 𝓞 E) (i : Fin n) :
    ptm C (fun k => φa c φ (us k)) m ≫ jpt y C.d C.x m i = xExp y C φ m ≫ Xo.univ.t.act.act (us i) := by
  have hP : ∀ k j, MvPowerSeries.constantCoeff (φa c φ (us k) j) = 0 := fun k j => const_φa c φ hφ (us k) j
  rw [jpt, ← Category.assoc, ptm_copy C _ hP m i, exp_chart_action_point C φ hφ hx m (us i)]

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
