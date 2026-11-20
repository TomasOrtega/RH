import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndFrFix
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTiePf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetSubstPSTrunc

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)

attribute [local instance] Over.cartesianMonoidalCategory

section Alg

variable {S : Type} [CommRing S] {d : ℕ}

/- English proof (translation)
Unfold `Formalism.L2.Pj.psJet`. Use `congr 1`. Unfold `Formalism.L2.Pj.psTrunc`. Use `Finset.sum_congr rfl fun e he => ?_` and prove the remaining obligations. Use `congr 1`.

Rewrite using `[MvPolynomial.coeff_coe]`. Simplify using `only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]`. Rewrite using `[Finset.sum_eq_single e]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Simplify using `[hb]`. Introduce `h`. Conclude with `absurd he h`.
-/
theorem psJet_coe_trunc {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (g : MvPowerSeries κ S) :
    psJet m ((psTrunc m g : MvPolynomial κ S) : MvPowerSeries κ S) = psJet m g := by
  unfold Formalism.L2.Pj.psJet
  congr 1
  unfold Formalism.L2.Pj.psTrunc
  refine Finset.sum_congr rfl fun e he => ?_
  congr 1
  rw [MvPolynomial.coeff_coe]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single e]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd he h

/- English proof (translation)
Establish `h : (fun p : Fin 1 × Fin d => (![pt S (n` using `1) d 0] : Fin 1 → Pt S 1 d) p.1 p.2) = MvPowerSeries.X := by`. Use function extensionality and compare the values at `p`. Take `⟨i, j⟩` from `p`. Rewrite using `[Fin.fin_one_eq_zero i]`. Both sides reduce to the same expression.

Unfold `ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev`. Rewrite using `[h]`. Use `first`. Consider the case `(rw [MvPowerSeries.subst_self]; rfl)`. Consider the case `exact congrFun MvPowerSeries.subst_self g`.

Consider the case `simp [MvPowerSeries.subst_self]`.
-/
theorem eval_single_point_id (g : PS S 1 d) : ev (n := 1) ![pt S (n := 1) d 0] g = g := by
  have h : (fun p : Fin 1 × Fin d => (![pt S (n := 1) d 0] : Fin 1 → Pt S 1 d) p.1 p.2) =
      MvPowerSeries.X := by
    funext p
    obtain ⟨i, j⟩ := p
    rw [Fin.fin_one_eq_zero i]
    rfl
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev
  rw [h]
  first
  | (rw [MvPowerSeries.subst_self]; rfl)
  | exact congrFun MvPowerSeries.subst_self g
  | simp [MvPowerSeries.subst_self]

/- English proof (translation)
Use `set P : Fin 2 × Fin d → MvPolynomial (Fin 1 × Fin d) S := fun p => (![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn d m ![0] (act j)] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S) p.1 p.2 with hPdef`. Establish `hsL : GermD.sL m act = jetSubstP m P` using `rfl`. Establish `hP : ∀ p, MvPolynomial.constantCoeff (P p) = 0`. Introduce and unpack `⟨i, j⟩`. Use `fin_cases i`.

Simplify using `[hPdef]`. Use `show MvPolynomial.constantCoeff (psIn d m ![0] (act j)) = 0`. Rewrite using `[GermD.power_series_in_fin_one, ExpGB.cc_psTrunc']`. Conclude with `hact j`. Establish `ha : ∀ p : Fin 2 × Fin d, MvPowerSeries.constantCoeff ((![pt S (n` using `1) d 0, comp1 act (pt S (n := 1) d 0)] : Fin 2 → Pt S 1 d) p.1 p.2) = 0 := by`.

Introduce and unpack `⟨i, j⟩`. Use `fin_cases i`. Simplify using `[pt]`. Use `show MvPowerSeries.constantCoeff (comp1 act (pt S (n := 1) d 0) j) = 0`. Unfold `comp1`.

Rewrite using `[eval_single_point_id]`. Conclude with `hact j`. Rewrite using `[hsL]`. Unfold `ev`. Rewrite using `[FBIdJet.psJet_subst m _ ha f]`.

Apply `DFunLike.congr_fun` to reduce the goal to its premises. Use `GermD.jet_hom_ext fun p => ?_` and prove the remaining obligations. Rewrite using `[jetSubstP, GermD.jetMap_mk, GermD.jetMap_mk, MvPolynomial.aeval_X, MvPolynomial.aeval_X, hP p, map_zero, sub_zero]`. Take `⟨i, j⟩` from `p`. Use `fin_cases i`.

Use `show Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j)) = psJet m (pt S (n := 1) d 0 j)`. Rewrite using `[show pt S (n := 1) d 0 j = ((MvPolynomial.X ((0 : Fin 1), j) : MvPolynomial (Fin 1 × Fin d) S) : MvPowerSeries (Fin 1 × Fin d) S) from (MvPolynomial.coe_X _).symm, psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe]`. Use `show Ideal.Quotient.mk _ (psIn d m ![0] (act j)) = psJet m (comp1 act (pt S (n := 1) d 0) j)`. Rewrite using `[GermD.power_series_in_fin_one]`. Unfold `comp1`.

Rewrite using `[eval_single_point_id]`. Both sides reduce to the same expression.
-/
theorem jet_sL (m : ℕ) (act : Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (hact : ∀ j, MvPowerSeries.constantCoeff (act j) = 0) (f : PS S 2 d) :
    GermD.sL m act (psJet m f) = psJet m (ev (n := 1) ![pt S (n := 1) d 0, comp1 act (pt S (n := 1) d 0)] f) := by
  set P : Fin 2 × Fin d → MvPolynomial (Fin 1 × Fin d) S := fun p =>
    (![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn d m ![0] (act j)] :
      Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S) p.1 p.2 with hPdef
  have hsL : GermD.sL m act = jetSubstP m P := rfl
  have hP : ∀ p, MvPolynomial.constantCoeff (P p) = 0 := by
    rintro ⟨i, j⟩
    fin_cases i
    · simp [hPdef]
    · show MvPolynomial.constantCoeff (psIn d m ![0] (act j)) = 0
      rw [GermD.power_series_in_fin_one, ExpGB.cc_psTrunc']
      exact hact j
  have ha : ∀ p : Fin 2 × Fin d, MvPowerSeries.constantCoeff
      ((![pt S (n := 1) d 0, comp1 act (pt S (n := 1) d 0)] : Fin 2 → Pt S 1 d) p.1 p.2) = 0 := by
    rintro ⟨i, j⟩
    fin_cases i
    · simp [pt]
    · show MvPowerSeries.constantCoeff (comp1 act (pt S (n := 1) d 0) j) = 0
      unfold comp1
      rw [eval_single_point_id]
      exact hact j
  rw [hsL]
  unfold ev
  rw [FBIdJet.psJet_subst m _ ha f]
  apply DFunLike.congr_fun
  refine GermD.jet_hom_ext fun p => ?_
  rw [jetSubstP, GermD.jetMap_mk, GermD.jetMap_mk, MvPolynomial.aeval_X, MvPolynomial.aeval_X, hP p, map_zero,
    sub_zero]
  obtain ⟨i, j⟩ := p
  fin_cases i
  · show Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j)) = psJet m (pt S (n := 1) d 0 j)
    rw [show pt S (n := 1) d 0 j = ((MvPolynomial.X ((0 : Fin 1), j) : MvPolynomial (Fin 1 × Fin d) S) :
      MvPowerSeries (Fin 1 × Fin d) S) from (MvPolynomial.coe_X _).symm, psJet, FBIdJet.psTrunc_eq,
      FBIdJet.mk_trunc_coe]
  · show Ideal.Quotient.mk _ (psIn d m ![0] (act j)) = psJet m (comp1 act (pt S (n := 1) d 0) j)
    rw [GermD.power_series_in_fin_one]
    unfold comp1
    rw [eval_single_point_id]
    rfl

end Alg

section Unit

variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}

/- English proof (translation)
Unfold `lg`. Rewrite using `[Sym.const_ev _ (fun p q => by fin_cases p; simp [pt])]`. Unfold `ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf`. Conclude with `ReciprocityTheory.ChartRestriction.G.TB.LogPf.constantCoeff_prim _`.
-/
theorem const_lg (G : FGLaw S d) {n : ℕ} (j : Fin n) (i : Fin d) :
    MvPowerSeries.constantCoeff (lg G j i) = 0 := by
  unfold lg
  rw [Sym.const_ev _ (fun p q => by fin_cases p; simp [pt])]
  unfold ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf
  exact ReciprocityTheory.ChartRestriction.G.TB.LogPf.constantCoeff_prim _

/- English proof (translation)
Simplify using `only [Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.bilL, map_sum]`. Use `Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Establish `h0 : MvPowerSeries.constantCoeff (lg G (0 : Fin 2) i * lg G (1 : Fin 2) l) = 0`. Rewrite using `[map_mul, const_lg, zero_mul]`. Use `first`.

Consider the case `simp [h0]`. Consider the case `(rw [MvPowerSeries.smul_eq_C_mul, map_mul, h0, mul_zero])`.
-/
theorem const_bilL (G : FGLaw S d) (cc : Fin d → Fin d → S) : MvPowerSeries.constantCoeff (bilL G cc) = 0 := by
  simp only [Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.bilL, map_sum]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun l _ => ?_
  have h0 : MvPowerSeries.constantCoeff (lg G (0 : Fin 2) i * lg G (1 : Fin 2) l) = 0 := by
    rw [map_mul, const_lg, zero_mul]
  first
  | simp [h0]
  | (rw [MvPowerSeries.smul_eq_C_mul, map_mul, h0, mul_zero])

variable {O : Type} [CommRing O] [StarRing O]

/- English proof (translation)
Use `fin_cases p`. Simplify using `[ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]`. Establish `h1 : comp1 (B.A.act w0) (pt S (n` using `1) d 0) q = B.A.act w0 q := eval_single_point_id _`. Simplify `B.A.const w0 q` using `[h1]`.
-/
theorem diag_const (B : FB S d O) (w0 : O) (p : Fin 2) (q : Fin d) :
    MvPowerSeries.constantCoeff ((![pt S (n := 1) d 0, comp1 (B.A.act w0) (pt S (n := 1) d 0)] : Fin 2 → Pt S 1 d) p q) = 0 := by
  fin_cases p
  · simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
  · have h1 : comp1 (B.A.act w0) (pt S (n := 1) d 0) q = B.A.act w0 q := eval_single_point_id _
    simpa [h1] using B.A.const w0 q

/- English proof (translation)
Establish `hs : MvPowerSeries.HasSubst (fun p : Fin m × Fin e => a p.1 p.2)` using `by first`. Consider the case `exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun p => by rw [ha p.1 p.2]; exact IsNilpotent.zero)`. Consider the case `exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun p => ha p.1 p.2)`. Consider the case `exact ⟨fun p => by rw [ha p.1 p.2]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩`. Unfold `ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev`.

Rewrite using `[MvPowerSeries.constantCoeff_subst hs]`. Apply `finsum_eq_zero_of_forall_eq_zero` to reduce the goal to its premises. Introduce `x`. Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality.

Simplify using `[hf]`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs'⟩ : ∃ s, x s ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hx (Finsupp.ext hc)`.

Rewrite using `[Finsupp.prod, map_prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs')]`. Simplify using the standard rewrite rules. Rewrite using `[map_pow, ha s.1 s.2, zero_pow hs']`.
-/
private theorem const_ev_lemma {R : Type} [CommRing R] {e m n : ℕ} (a : Fin m → Pt R n e) (f : PS R m e)
    (ha : ∀ p q, MvPowerSeries.constantCoeff (a p q) = 0) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (ev a f) = 0 := by
  have hs : MvPowerSeries.HasSubst (fun p : Fin m × Fin e => a p.1 p.2) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent
        (fun p => by rw [ha p.1 p.2]; exact IsNilpotent.zero)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun p => ha p.1 p.2)
    | exact ⟨fun p => by rw [ha p.1 p.2]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev
  rw [MvPowerSeries.constantCoeff_subst hs]
  apply finsum_eq_zero_of_forall_eq_zero
  intro x
  by_cases hx : x = 0
  · subst hx
    simp [hf]
  · obtain ⟨s, hs'⟩ : ∃ s, x s ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hx (Finsupp.ext hc)
    rw [Finsupp.prod, map_prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs')]
    · simp
    · rw [map_pow, ha s.1 s.2, zero_pow hs']

/- English proof (translation)
Conclude with `const_ev_lemma (![pt S (n := 1) d 0, comp1 (B.A.act w0) (pt S (n := 1) d 0)]) (bilL B.G cc) (diag_const B w0) (const_bilL B.G cc)`.
-/
theorem const_diagL (B : FB S d O) (w0 : O) (cc : Fin d → Fin d → S) :
    MvPowerSeries.constantCoeff (diagL B w0 cc) = 0 := by
  exact const_ev_lemma (![pt S (n := 1) d 0, comp1 (B.A.act w0) (pt S (n := 1) d 0)]) (bilL B.G cc)
    (diag_const B w0) (const_bilL B.G cc)

/- English proof (translation)
Establish `ha : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d => (![pt S (n` using `1) d 0, comp1 (B.A.act w0) (pt S (n := 1) d 0)] : Fin 2 → Pt S 1 d) p.1 p.2) := ⟨fun p => by rw [diag_const B w0 p.1 p.2]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩`. Establish `hb : MvPowerSeries.HasSubst (fun _ : Unit => -bilL B.G cc)` using `⟨fun _ => by rw [map_neg, const_bilL, neg_zero]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩`. Unfold `Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.expP ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev`. Simplify using `only [PowerSeries.subst]`. Rewrite using `[MvPowerSeries.subst_comp_subst_apply hb ha]`.

Use `congr 1`. Use function extensionality and compare the values at `_`. Rewrite using `[← MvPowerSeries.coe_substAlgHom ha, map_neg, MvPowerSeries.coe_substAlgHom]`. Both sides reduce to the same expression.
-/
theorem eval_expSeries_neg_bilinear (B : FB S d O) (w0 : O) (cc : Fin d → Fin d → S) :
    ev (n := 1) ![pt S (n := 1) d 0, comp1 (B.A.act w0) (pt S (n := 1) d 0)] (expP (-bilL B.G cc)) =
      expP (-diagL B w0 cc) := by
  have ha : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d =>
      (![pt S (n := 1) d 0, comp1 (B.A.act w0) (pt S (n := 1) d 0)] : Fin 2 → Pt S 1 d) p.1 p.2) :=
    ⟨fun p => by rw [diag_const B w0 p.1 p.2]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
  have hb : MvPowerSeries.HasSubst (fun _ : Unit => -bilL B.G cc) :=
    ⟨fun _ => by rw [map_neg, const_bilL, neg_zero]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
  unfold Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.expP ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev
  simp only [PowerSeries.subst]
  rw [MvPowerSeries.subst_comp_subst_apply hb ha]
  congr 1
  funext _
  rw [← MvPowerSeries.coe_substAlgHom ha, map_neg, MvPowerSeries.coe_substAlgHom]
  rfl

/- English proof (translation)
Rewrite using `[Units.val_pow_eq_pow_val, Units.coe_map]`. Use `show psJet m _ * ((GermD.sL m (B.A.act w0)) (u : Jet S (Fin 2 × Fin d) m)) ^ k = 1`. Rewrite using `[hu, jet_sL m _ (B.A.const w0), eval_expSeries_neg_bilinear, ← ExpTiePf.psJet_pow, ← FBIdJet.psJet_mul]`. Unfold `expP`. Rewrite using `[ExpTiePf.exp_pow_inv _ (const_diagL B w0 cc) k]`.

Conclude with `FBIdJet.psJet_one m`.
-/
theorem unit_jet (B : FB S d O) (w0 : O) (cc : Fin d → Fin d → S) (m k : ℕ) (u : (Jet S (Fin 2 × Fin d) m)ˣ)
    (hu : (u : Jet S (Fin 2 × Fin d) m) = psJet m (expP (-bilL B.G cc))) :
    psJet m (expP ((k : S) • diagL B w0 cc)) *
      ((Units.map (GermD.sL m (B.A.act w0)).toMonoidHom u ^ k : (Jet S (Fin 1 × Fin d) m)ˣ) :
        Jet S (Fin 1 × Fin d) m) = 1 := by
  rw [Units.val_pow_eq_pow_val, Units.coe_map]
  show psJet m _ * ((GermD.sL m (B.A.act w0)) (u : Jet S (Fin 2 × Fin d) m)) ^ k = 1
  rw [hu, jet_sL m _ (B.A.const w0), eval_expSeries_neg_bilinear, ← ExpTiePf.psJet_pow, ← FBIdJet.psJet_mul]
  unfold expP
  rw [ExpTiePf.exp_pow_inv _ (const_diagL B w0 cc) k]
  exact FBIdJet.psJet_one m

end Unit

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Simplify using `only [Formalism.L2.Pj.genPow, Formalism.L2.Pj.scaleGen, map_pow, mul_pow]`. Apply the tactic sequence `all_goals rfl`.
-/
theorem genPow_scale {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ)
    (w : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) (k : ℕ) :
    genPow φ ε (scaleGen φ ε w g) k = scaleGen φ _ (w ^ k) (genPow φ ε g k) := by
  simp only [Formalism.L2.Pj.genPow, Formalism.L2.Pj.scaleGen, map_pow, mul_pow]
  all_goals rfl

/- English proof (translation)
Establish `e : Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫ h.app W ≫ Z.presheaf.map (homOfLE hW).op = h.appTop ≫ Z.presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op`. Rewrite using `[← Category.assoc, Scheme.Hom.naturality, Category.assoc, ← Functor.map_comp]`. Both sides reduce to the same expression. Conclude with `congrArg (fun f => f.hom v) e`.
-/
private theorem app_res_top_lemma {Y Z : Scheme.{0}} (h : Z ⟶ Y) (W : Y.Opens) {W' : Z.Opens}
    (hW : W' ≤ h ⁻¹ᵁ W) (v : Γ(Y, ⊤)) :
    (Z.presheaf.map (homOfLE hW).op).hom ((h.app W).hom ((Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom v)) =
      (Z.presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op).hom (h.appTop.hom v) := by
  have e : Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫ h.app W ≫ Z.presheaf.map (homOfLE hW).op =
      h.appTop ≫ Z.presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op := by
    rw [← Category.assoc, Scheme.Hom.naturality, Category.assoc, ← Functor.map_comp]
    rfl
  exact congrArg (fun f => f.hom v) e

/- English proof (translation)
Simplify using `only [ReciprocityTheory.ChartRestriction.G.Semi.LB.pullGen, Formalism.L2.Pj.scaleGen]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Rewrite using `[map_mul, map_mul]`. Use `congr 1`.

Apply `Units.ext` to reduce the goal to its premises. Use `first`. Consider the case `exact app_res_top_lemma h _ _ v.val`. Consider the case `(simp only [ReciprocityTheory.ChartRestriction.G.Semi.res, ReciprocityTheory.ChartRestriction.G.Semi.pullU, Units.coe_map, MonoidHom.coe_coe]`. Conclude with `app_res_top_lemma h _ _ v.val)`.
-/
theorem pullGen_scale {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ)
    (v : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) (h : Z ⟶ Y) :
    LB.pullGen Xo.univ.t.PP.L φ ε (scaleGen φ ε v g) h =
      scaleGen (fun k => h ≫ φ k) ε (Units.map h.appTop.hom.toMonoidHom v) (LB.pullGen Xo.univ.t.PP.L φ ε g h) := by
  simp only [ReciprocityTheory.ChartRestriction.G.Semi.LB.pullGen, Formalism.L2.Pj.scaleGen]
  congr 1
  funext j
  rw [map_mul, map_mul]
  congr 1
  apply Units.ext
  first
  | exact app_res_top_lemma h _ _ v.val
  | (simp only [ReciprocityTheory.ChartRestriction.G.Semi.res, ReciprocityTheory.ChartRestriction.G.Semi.pullU, Units.coe_map, MonoidHom.coe_coe]
     exact app_res_top_lemma h _ _ v.val)

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Establish `e : X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫ X.presheaf.map (homOfLE h2).op = X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op`. Rewrite using `[← Functor.map_comp]`. Both sides reduce to the same expression. Conclude with `congrArg (fun f => f.hom x.val) e`.
-/
private theorem res_res_top_lemma {X : Scheme.{0}} {V W : X.Opens} (h2 : W ≤ V) (x : Γ(X, ⊤)ˣ) :
    ReciprocityTheory.ChartRestriction.G.Semi.res h2 (ReciprocityTheory.ChartRestriction.G.Semi.res (le_top : V ≤ ⊤) x) =
      ReciprocityTheory.ChartRestriction.G.Semi.res (le_top : W ≤ ⊤) x := by
  apply Units.ext
  have e : X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫ X.presheaf.map (homOfLE h2).op =
      X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op := by
    rw [← Functor.map_comp]
    rfl
  exact congrArg (fun f => f.hom x.val) e

/- English proof (translation)
Simplify using `only [ReciprocityTheory.ChartRestriction.G.Semi.LB.mulGen, Formalism.L2.Pj.scaleGen]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Rewrite using `[map_mul]`. Use `erw [res_res_top_lemma]`.

Conclude with `mul_left_comm _ _ _`.
-/
theorem mulGen_scale_right {Y : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ Xo.univ.t.G.left))
    (ε : K → ℤ) (φ' : K' → (Y ⟶ Xo.univ.t.G.left)) (ε' : K' → ℤ) (w : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) (g' : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ' ε')) :
    LB.mulGen Xo.univ.t.PP.L φ ε φ' ε' g (scaleGen φ' ε' w g') =
      scaleGen _ _ w (LB.mulGen Xo.univ.t.PP.L φ ε φ' ε' g g') := by
  simp only [ReciprocityTheory.ChartRestriction.G.Semi.LB.mulGen, Formalism.L2.Pj.scaleGen]
  congr 1
  funext j
  rw [map_mul]
  erw [res_res_top_lemma]
  exact mul_left_comm _ _ _

/- English proof (translation)
Take the linear combination `(-(a * t)) * h`.
-/
private theorem mul_cancel_lemma {R : Type} [CommRing R] (a b c t : R) (h : b * c = 1) :
    a * t = a * b * (c * t) := by
  linear_combination (-(a * t)) * h

/- English proof (translation)
Introduce `j`. Rewrite using `[hv j]`. Simplify using `only [Formalism.L2.Pj.scaleGen, ReciprocityTheory.ChartRestriction.G.Semi.res, Units.val_mul, Units.coe_map, MonoidHom.coe_coe]`. Rewrite using `[map_mul]`. Conclude with `mul_cancel_lemma _ _ _ _ (by erw [← map_mul, Units.inv_mul, map_one])`.
-/
theorem isValueAt_scale {a : ℤ} {T : Over Xo.X} {s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L a T)}
    {z : T ⟶ Xo.univ.t.G}
    {τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := T.left) (K := Fin 1) (fun _ => z.left) fun _ => a)}
    {v : Γ(T.left, ⊤)} (hv : IsValueAt Xo.univ.t.G Xo.univ.t.PP.L a s z τ v) (w : Γ(T.left, ⊤)ˣ) :
    IsValueAt Xo.univ.t.G Xo.univ.t.PP.L a s z (scaleGen _ _ w τ) (v * ((w⁻¹ : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤))) := by
  intro j
  rw [hv j]
  simp only [Formalism.L2.Pj.scaleGen, ReciprocityTheory.ChartRestriction.G.Semi.res, Units.val_mul, Units.coe_map, MonoidHom.coe_coe]
  rw [map_mul]
  exact mul_cancel_lemma _ _ _ _ (by erw [← map_mul, Units.inv_mul, map_one])

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Establish `e : Y.presheaf.map (homOfLE hU).op ≫ h.app U' ≫ Z.presheaf.map (homOfLE hA).op = h.app U ≫ Z.presheaf.map (homOfLE hB).op ≫ Z.presheaf.map (homOfLE hAB).op`. Rewrite using `[← Category.assoc, Scheme.Hom.naturality, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]`. Both sides reduce to the same expression. Conclude with `congrArg (fun f => f.hom x.val) e`.
-/
private theorem pull_res_lemma {Y Z : Scheme.{0}} (h : Z ⟶ Y) {U U' : Y.Opens} (hU : U' ≤ U) {A B : Z.Opens}
    (hA : A ≤ h ⁻¹ᵁ U') (hAB : A ≤ B) (hB : B ≤ h ⁻¹ᵁ U) (x : Γ(Y, U)ˣ) :
    ReciprocityTheory.ChartRestriction.G.Semi.res hA (ReciprocityTheory.ChartRestriction.G.Semi.pullU h U' (ReciprocityTheory.ChartRestriction.G.Semi.res hU x)) =
      ReciprocityTheory.ChartRestriction.G.Semi.res hAB (ReciprocityTheory.ChartRestriction.G.Semi.res hB (ReciprocityTheory.ChartRestriction.G.Semi.pullU h U x)) := by
  apply Units.ext
  have e : Y.presheaf.map (homOfLE hU).op ≫ h.app U' ≫ Z.presheaf.map (homOfLE hA).op =
      h.app U ≫ Z.presheaf.map (homOfLE hB).op ≫ Z.presheaf.map (homOfLE hAB).op := by
    rw [← Category.assoc, Scheme.Hom.naturality, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
    rfl
  exact congrArg (fun f => f.hom x.val) e

/- English proof (translation)
Unfold `ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen.Corr at hc ⊢`. Introduce `j j' hj hj' hjj'`. Establish `hc'` using `hc j j' (fun k₁ k₂ e => hj k₁ k₂ (congrArg (h ≫ ·) e)) (fun k₁ k₂ e => hj' k₁ k₂ (congrArg (h ≫ ·) e)) (fun k k' e => hjj' k k' (congrArg (h ≫ ·) e))`. Establish `h1 : ∀ i, ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L (fun k => h ≫ φ k) i ≤ h ⁻¹ᵁ ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L φ i` using `fun i _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k`. Establish `hA : ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L (fun k => h ≫ φ k) j ⊓ ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L (fun k => h ≫ φ k) j' ≤ h ⁻¹ᵁ (ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L φ j ⊓ ReciprocityThe …` using `fun _ hy => And.intro (Set.mem_iInter.2 fun k => Set.mem_iInter.1 (And.left hy) k) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 (And.right hy) k)`.

Establish `key` using `congrArg (fun (x : Γ(Y, ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L φ j ⊓ ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L φ j')ˣ) => ReciprocityTheory.ChartRestriction.G.Semi.res hA (ReciprocityTheory.ChartRestriction.G.Semi.pullU h _ x)) …`. Use `Eq.trans ?_ (key.trans ?_)` and prove the remaining obligations. Conclude with `(pull_res_lemma h inf_le_left hA inf_le_left (h1 j) (t.s j)).symm`. Simplify using `only [Formalism.L2.Pj.scaleGen] erw [map_mul, map_mul, map_mul, map_mul]`. Use `congr 1`.

Establish `s2 : ReciprocityTheory.ChartRestriction.G.Semi.res hA (ReciprocityTheory.ChartRestriction.G.Semi.pullU h _ (ReciprocityTheory.ChartRestriction.G.Semi.res (le_top : ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L φ j ⊓ ReciprocityTheory.ChartRestriction.G.Semi.L …` using `Units.ext (app_res_top_lemma h _ hA v.val)`. Use `(congrArg (fun (y : Γ(Y, ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L φ j ⊓ ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L φ j')ˣ) => ReciprocityTheory.ChartRestriction.G.Semi.res hA (ReciprocityTheory.ChartRestriction.G.Semi.pullU h _ y) …` and prove the remaining obligations. Use `s2.trans ?_` and prove the remaining obligations. Conclude with `(res_res_top_lemma inf_le_right _).symm`. Conclude with `pull_res_lemma h inf_le_right hA inf_le_right (h1 j') (t'.s j')`.
-/
theorem corr_pull_scale {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ)
    (t t' : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) (v : Γ(Y, ⊤)ˣ) (h : Z ⟶ Y)
    (hc : LB.Gen.Corr Xo.univ.t.PP.L φ ε φ ε t (scaleGen φ ε v t')) :
    LB.Gen.Corr Xo.univ.t.PP.L (fun k => h ≫ φ k) ε (fun k => h ≫ φ k) ε (LB.pullGen Xo.univ.t.PP.L φ ε t h)
      (scaleGen (fun k => h ≫ φ k) ε (Units.map h.appTop.hom.toMonoidHom v) (LB.pullGen Xo.univ.t.PP.L φ ε t' h)) := by
  unfold ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen.Corr at hc ⊢
  intro j j' hj hj' hjj'
  have hc' := hc j j' (fun k₁ k₂ e => hj k₁ k₂ (congrArg (h ≫ ·) e))
    (fun k₁ k₂ e => hj' k₁ k₂ (congrArg (h ≫ ·) e)) (fun k k' e => hjj' k k' (congrArg (h ≫ ·) e))
  have h1 : ∀ i, ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L (fun k => h ≫ φ k) i ≤
      h ⁻¹ᵁ ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L φ i :=
    fun i _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have hA : ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L (fun k => h ≫ φ k) j ⊓
      ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L (fun k => h ≫ φ k) j' ≤
      h ⁻¹ᵁ (ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L φ j ⊓
        ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L φ j') :=
    fun _ hy => And.intro (Set.mem_iInter.2 fun k => Set.mem_iInter.1 (And.left hy) k)
      (Set.mem_iInter.2 fun k => Set.mem_iInter.1 (And.right hy) k)
  have key := congrArg (fun (x : Γ(Y, ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L φ j ⊓
      ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L φ j')ˣ) =>
    ReciprocityTheory.ChartRestriction.G.Semi.res hA (ReciprocityTheory.ChartRestriction.G.Semi.pullU h _ x)) hc'
  refine Eq.trans ?_ (key.trans ?_)
  · exact (pull_res_lemma h inf_le_left hA inf_le_left (h1 j) (t.s j)).symm
  · simp only [Formalism.L2.Pj.scaleGen]
    erw [map_mul, map_mul, map_mul, map_mul]
    congr 1
    · have s2 : ReciprocityTheory.ChartRestriction.G.Semi.res hA (ReciprocityTheory.ChartRestriction.G.Semi.pullU h _
          (ReciprocityTheory.ChartRestriction.G.Semi.res (le_top : ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L φ j ⊓
            ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L φ j' ≤ ⊤) v)) =
          ReciprocityTheory.ChartRestriction.G.Semi.res le_top (Units.map h.appTop.hom.toMonoidHom v) :=
        Units.ext (app_res_top_lemma h _ hA v.val)
      refine (congrArg (fun (y : Γ(Y, ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L φ j ⊓
            ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L φ j')ˣ) =>
          ReciprocityTheory.ChartRestriction.G.Semi.res hA (ReciprocityTheory.ChartRestriction.G.Semi.pullU h _ y))
          (res_res_top_lemma inf_le_right v)).trans ?_
      refine s2.trans ?_
      exact (res_res_top_lemma inf_le_right _).symm
    · exact pull_res_lemma h inf_le_right hA inf_le_right (h1 j') (t'.s j')

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hL` using `Xo.univ.t.PP.isLB`. Take `⟨F₁, τ₁, hP₁, hC₁, hV₁⟩` from `hf m`. Take `⟨u, hu, hCe⟩` from `he m`. Establish `h1` using `corr_pull_scale _ _ (e' m) (C.e m) (unitΓ u) (homAt y.x (GermD.sL m (C.B.A.act H.w0))).left hCe`. Rewrite `h1` using `[FBIdLB.unitΓ_homAt]`.

Establish `hEL : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (eL y C.d C.x C.B.A.act e' C.wP m) (scaleGen _ _ (unitΓ (Units.map (GermD.sL m (C.B.A.act H.w0)).toMonoidHom u)) (eL y C.d C.x C.B.A.act C.e C.wP m))`. Establish `h2` using `ReciprocityTheory.ChartRestriction.G.DVR.corr_mulGen (ExpTieGerm.corr_refl (L := Xo.univ.t.PP.L) (LB.pullGen Xo.univ.t.PP.L _ _ C.wP (C.x m).left)) h1`. Rewrite `h2` using `[mulGen_scale_right]`. Conclude with `h2`. Use `set U : (Jet S (Fin 1 × Fin C.d) m)ˣ := Units.map (GermD.sL m (C.B.A.act H.w0)).toMonoidHom u with hU`.

Use `set w : Γ(Sp (Jet S (Fin 1 × Fin C.d) m), ⊤)ˣ := unitΓ U with hw`. Establish `hG : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (genPow _ _ (eL y C.d C.x C.B.A.act e' C.wP m) k) (scaleGen _ _ (w ^ k) (genPow _ _ (eL y C.d C.x C.B.A.act C.e C.wP m) k))`. Use `ExpTieGerm.corr_genPow hEL k` as an intermediate fact. Rewrite `this` using `[genPow_scale]`. Then use the resulting hypothesis. Establish `h3` using `ExpTieGerm.corr_scale hC₁ (w ^ k)`.

Establish `hC'` using `ReciprocityTheory.ChartRestriction.G.DVR.corr_trans hL h3 (ReciprocityTheory.ChartRestriction.G.DVR.corr_symm hG)`. Establish `hV'` using `isValueAt_scale hV₁ (w ^ k)`. Establish `hprod` using `unit_jet C.B H.w0 (cc m) m k u hu`. Establish `hinv : psJet m (expP ((k : S) • diagL C.B H.w0 (cc m))) = ↑((U ^ k)⁻¹)` using `by set X := psJet m (expP ((k : S) • diagL C.B H.w0 (cc m))) with hX`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Units.mul_inv, _root_.mul_one]`. Use `_ = (X * ↑(U ^ k)) * ↑((U ^ k)⁻¹) := (_root_.mul_assoc _ _ _).symm`. Use `_ = ↑((U ^ k)⁻¹) := by rw [hprod, _root_.one_mul]`. Establish `hw' : ((w ^ k)⁻¹ : Γ(Sp (Jet S (Fin 1 × Fin C.d) m), ⊤)ˣ) = unitΓ ((U ^ k)⁻¹)`. Simplify using `[hw, unitΓ, map_pow, map_inv]`.

Use `⟨F₁, _, hP₁, hC', ?_⟩` and prove the remaining obligations. Establish `hv : toΓ _ (psJet m (f * expP ((k : S) • diagL C.B H.w0 (cc m)))) = toΓ _ (psJet m f) * (((w ^ k)⁻¹ : Γ(Sp (Jet S (Fin 1 × Fin C.d) m), ⊤)ˣ) : Γ(Sp (Jet S (Fin 1 × Fin C.d) m), ⊤))`. Rewrite using `[hw']`. Use `show _ = toΓ _ _ * toΓ _ _`. Rewrite using `[← map_mul, FBIdJet.psJet_mul, hinv]`.

Rewrite using `[hv]`. Conclude with `hV'`.
-/
theorem germ_order {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] [StarRing (𝓞 E)] (y : FrPt Xo c S)
    (C : ChartAt Xo c y) (e' : ∀ m, FrTy y C.d C.x m) (cc : ℕ → Fin C.d → Fin C.d → S)
    (he : ∀ m, ∃ u : (Jet S (Fin 2 × Fin C.d) m)ˣ,
      (u : Jet S (Fin 2 × Fin C.d) m) = psJet m (expP (-bilL C.B.G (cc m))) ∧
        LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (scaleGen (Xo := Xo) _ _ (unitΓ u) (C.e m)))
    (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (f : MvPowerSeries (Fin 1 × Fin C.d) S)
    (hf : IsGerm y C.d C.x C.B.A.act C.e C.wP k F f) (m : ℕ) :
    ∃ (F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (jO y C.d m 1)))
      (τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (C.x m).left) fun _ => (k : ℤ))),
      IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (jBase y C.d m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F F' ∧
      LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ τ (genPow _ _ (eL y C.d C.x C.B.A.act e' C.wP m) k) ∧
      IsValueAt Xo.univ.t.G Xo.univ.t.PP.L k F' (C.x m) τ
        (toΓ _ (psJet m (f * expP ((k : S) • diagL C.B H.w0 (cc m))))) := by
  have hL := Xo.univ.t.PP.isLB
  obtain ⟨F₁, τ₁, hP₁, hC₁, hV₁⟩ := hf m
  obtain ⟨u, hu, hCe⟩ := he m
  have h1 := corr_pull_scale _ _ (e' m) (C.e m) (unitΓ u) (homAt y.x (GermD.sL m (C.B.A.act H.w0))).left hCe
  rw [FBIdLB.unitΓ_homAt] at h1
  have hEL : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (eL y C.d C.x C.B.A.act e' C.wP m)
      (scaleGen _ _ (unitΓ (Units.map (GermD.sL m (C.B.A.act H.w0)).toMonoidHom u))
        (eL y C.d C.x C.B.A.act C.e C.wP m)) := by
    have h2 := ReciprocityTheory.ChartRestriction.G.DVR.corr_mulGen
      (ExpTieGerm.corr_refl (L := Xo.univ.t.PP.L) (LB.pullGen Xo.univ.t.PP.L _ _ C.wP (C.x m).left)) h1
    rw [mulGen_scale_right] at h2
    exact h2
  set U : (Jet S (Fin 1 × Fin C.d) m)ˣ := Units.map (GermD.sL m (C.B.A.act H.w0)).toMonoidHom u with hU
  set w : Γ(Sp (Jet S (Fin 1 × Fin C.d) m), ⊤)ˣ := unitΓ U with hw
  have hG : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (genPow _ _ (eL y C.d C.x C.B.A.act e' C.wP m) k)
      (scaleGen _ _ (w ^ k) (genPow _ _ (eL y C.d C.x C.B.A.act C.e C.wP m) k)) := by
    have := ExpTieGerm.corr_genPow hEL k
    rwa [genPow_scale] at this
  have h3 := ExpTieGerm.corr_scale hC₁ (w ^ k)
  have hC' := ReciprocityTheory.ChartRestriction.G.DVR.corr_trans hL h3 (ReciprocityTheory.ChartRestriction.G.DVR.corr_symm hG)
  have hV' := isValueAt_scale hV₁ (w ^ k)
  have hprod := unit_jet C.B H.w0 (cc m) m k u hu
  have hinv : psJet m (expP ((k : S) • diagL C.B H.w0 (cc m))) = ↑((U ^ k)⁻¹) := by
    set X := psJet m (expP ((k : S) • diagL C.B H.w0 (cc m))) with hX
    calc X = X * ((↑(U ^ k) : Jet S (Fin 1 × Fin C.d) m) * ↑((U ^ k)⁻¹)) := by
          rw [Units.mul_inv, _root_.mul_one]
      _ = (X * ↑(U ^ k)) * ↑((U ^ k)⁻¹) := (_root_.mul_assoc _ _ _).symm
      _ = ↑((U ^ k)⁻¹) := by rw [hprod, _root_.one_mul]
  have hw' : ((w ^ k)⁻¹ : Γ(Sp (Jet S (Fin 1 × Fin C.d) m), ⊤)ˣ) = unitΓ ((U ^ k)⁻¹) := by
    simp [hw, unitΓ, map_pow, map_inv]
  refine ⟨F₁, _, hP₁, hC', ?_⟩
  have hv : toΓ _ (psJet m (f * expP ((k : S) • diagL C.B H.w0 (cc m)))) =
      toΓ _ (psJet m f) * (((w ^ k)⁻¹ : Γ(Sp (Jet S (Fin 1 × Fin C.d) m), ⊤)ˣ) : Γ(Sp (Jet S (Fin 1 × Fin C.d) m), ⊤)) := by
    rw [hw']
    show _ = toΓ _ _ * toΓ _ _
    rw [← map_mul, FBIdJet.psJet_mul, hinv]
  rw [hv]
  exact hV'

end Geo

end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c _ _ S _ _ _ y C e' hfr hrig cc hT he k F f hf`. Establish `hL` using `Xo.univ.t.PP.isLB`. Take `⟨f', hf'⟩` from `germSt_holds E H Xo.X Xo.univ.t S y.x C.d C.B.G.F C.B.A.act (Lt1 Dw) (fun ℓ => y.u ℓ.1 ℓ.2) C.uvec C.x C.B.ph1 C.B.ph2 C.B.sy C.B.ad e' C.wP ((isChart_iff y C.d _ _ _ _).1 C.chart) ((isFrame_iff y C.d _ _ _ _ _ _ _ _).1 hfr) ((isPrim_iff _).1 C.prim) (fun m => hT m) k F`. Establish `hg : IsGerm y C.d C.x C.B.A.act e' C.wP k F f'` using `(isGerm_iff y C.d _ _ _ _ _ _ _).2 hf'`. Use `⟨f', hg, fun D => ?_⟩` and prove the remaining obligations.

Take `⟨F₁, τ₁, hP₁, hC₁, hV₁⟩` from `hg D`. Take `⟨F₂, τ₂, hP₂, hC₂, hV₂⟩` from `CIndFrFix3.germ_order y C e' cc he k F f hf D`. Establish `hF` using `GermFun.pull_unique _ _ _ _ _ _ _ _ hP₁ hP₂`. Substitute `hF` using the available equality. Establish `hτ` using `GermFun.gen_eq_of_corr _ hL _ _ _ _ _ _ _ hC₁ hC₂`.

Substitute `hτ` using the available equality. Conclude with `GermFun.toΓ_injective _ (GermFun.value_unique _ _ hL _ _ _ _ _ _ hV₁ hV₂)`.
-/
theorem germFix_holds : GermFixSt := by
  intro E _ _ _ H Dw l Xo c _ _ S _ _ _ y C e' hfr hrig cc hT he k F f hf
  have hL := Xo.univ.t.PP.isLB
  obtain ⟨f', hf'⟩ := germSt_holds E H Xo.X Xo.univ.t S y.x C.d C.B.G.F C.B.A.act (Lt1 Dw)
    (fun ℓ => y.u ℓ.1 ℓ.2) C.uvec C.x C.B.ph1 C.B.ph2 C.B.sy C.B.ad e' C.wP
    ((isChart_iff y C.d _ _ _ _).1 C.chart) ((isFrame_iff y C.d _ _ _ _ _ _ _ _).1 hfr) ((isPrim_iff _).1 C.prim)
    (fun m => hT m) k F
  have hg : IsGerm y C.d C.x C.B.A.act e' C.wP k F f' := (isGerm_iff y C.d _ _ _ _ _ _ _).2 hf'
  refine ⟨f', hg, fun D => ?_⟩
  obtain ⟨F₁, τ₁, hP₁, hC₁, hV₁⟩ := hg D
  obtain ⟨F₂, τ₂, hP₂, hC₂, hV₂⟩ := CIndFrFix3.germ_order y C e' cc he k F f hf D
  have hF := GermFun.pull_unique _ _ _ _ _ _ _ _ hP₁ hP₂
  subst hF
  have hτ := GermFun.gen_eq_of_corr _ hL _ _ _ _ _ _ _ hC₁ hC₂
  subst hτ
  exact GermFun.toΓ_injective _ (GermFun.value_unique _ _ hL _ _ _ _ _ _ hV₁ hV₂)

end Formalism.MainNotions.ModuliIntegralCharts.H1
