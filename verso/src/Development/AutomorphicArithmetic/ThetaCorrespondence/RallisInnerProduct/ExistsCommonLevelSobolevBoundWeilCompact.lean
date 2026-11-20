import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SobContId
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DRhoSumAndSobOLe
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionHeisenbergWordSupLeLevelPow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

noncomputable section

namespace UpperTheory.Lit.Rallis.ThetaDens.WeilCompact
open GlobalTheory

variable {D : D7}

/- English proof (translation)
Unfold `Formalism.L2.Theta.mt`. Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
theorem mt_mul_eq (V : HSp D) (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

/- English proof (translation)
Unfold `Formalism.L2.Theta.mt`. Rewrite using `[map_one]`. Both sides reduce to the same expression.
-/
theorem mt_one_eq (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one]; rfl

/- English proof (translation)
The claim follows from `Units.continuous_val.comp continuous_subtype_val`.
-/
theorem continuous_mt_eq (V : HSp D) : Continuous (Formalism.L2.Theta.mt V) :=
  Units.continuous_val.comp continuous_subtype_val

/- English proof (translation)
Unfold `Formalism.IndefR.Datum.actO`. Rewrite using `[inv_inv]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (Formalism.L2.Theta.mt T h), ← mt_mul_eq, ← mt_mul_eq, mul_inv_cancel, mul_inv_cancel, mt_one_eq, mt_one_eq, Matrix.one_mul, Matrix.mul_one]`.
-/
theorem actO_actO_inv {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    Formalism.IndefR.Datum.actO S T g h (Formalism.IndefR.Datum.actO S T g⁻¹ h⁻¹ x) = x := by
  unfold Formalism.IndefR.Datum.actO
  rw [inv_inv]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Formalism.L2.Theta.mt T h), ← mt_mul_eq, ← mt_mul_eq, mul_inv_cancel, mul_inv_cancel,
    mt_one_eq, mt_one_eq, Matrix.one_mul, Matrix.mul_one]

open GlobalTheory.Size in

/- English proof (translation)
Rewrite using `[GlobalTheory.OrientedHeis.om_dRho hom hθ g h τ _ hf]`. Use `congr 1`. Establish `e1` using `GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ h`. Establish `e2` using `GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ g`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[e2, Matrix.mul_one, ← Matrix.mul_assoc, e1, Matrix.one_mul]`.
-/
theorem dRho_om {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ)
    (g : GA D S) (h : GA D T) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (om (g, h) f) =
      om (g, h) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ
        (compAt θ τ (Formalism.L2.Theta.mt T h⁻¹) * z * compAt θ τ (Formalism.L2.Theta.mt S g)) f) := by
  rw [GlobalTheory.OrientedHeis.om_dRho hom hθ g h τ _ hf]
  congr 1
  have e1 := GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ h
  have e2 := GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ g
  simp only [Matrix.mul_assoc]
  rw [e2, Matrix.mul_one, ← Matrix.mul_assoc, e1, Matrix.one_mul]

def dirSize (θ : InfFam D) (S T : HSp D) (x : GA D S × GA D T) : ℝ :=
  ∑ a : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool, ∑ i, ∑ j,
    (|((compAt θ a.1 (Formalism.L2.Theta.mt T x.2⁻¹) * Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) *
      compAt θ a.1 (Formalism.L2.Theta.mt S x.1)) i j).re| +
     |((compAt θ a.1 (Formalism.L2.Theta.mt T x.2⁻¹) * Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) *
      compAt θ a.1 (Formalism.L2.Theta.mt S x.1)) i j).im|)

/- English proof (translation)
Unfold `dirSize`. Use `continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_` and prove the remaining obligations. Establish `h1 : Continuous fun x : GA D S × GA D T => compAt θ a.1 (Formalism.L2.Theta.mt T x.2⁻¹)` using `(GlobalTheory.RealWeil.continuous_compAt hθ a.1 _ _).comp ((continuous_mt_eq T).comp continuous_snd.inv)`. Establish `h2 : Continuous fun x : GA D S × GA D T => compAt θ a.1 (Formalism.L2.Theta.mt S x.1)` using `(GlobalTheory.RealWeil.continuous_compAt hθ a.1 _ _).comp ((continuous_mt_eq S).comp continuous_fst)`. Establish `h3` using `((h1.matrix_mul (continuous_const (y := Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)))).matrix_mul h2).matrix_elem i j`.

Conclude with `(continuous_abs.comp (Complex.continuous_re.comp h3)).add (continuous_abs.comp (Complex.continuous_im.comp h3))`.
-/
theorem continuous_dirSize {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) : Continuous (dirSize θ S T) := by
  unfold dirSize
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  have h1 : Continuous fun x : GA D S × GA D T => compAt θ a.1 (Formalism.L2.Theta.mt T x.2⁻¹) :=
    (GlobalTheory.RealWeil.continuous_compAt hθ a.1 _ _).comp ((continuous_mt_eq T).comp continuous_snd.inv)
  have h2 : Continuous fun x : GA D S × GA D T => compAt θ a.1 (Formalism.L2.Theta.mt S x.1) :=
    (GlobalTheory.RealWeil.continuous_compAt hθ a.1 _ _).comp ((continuous_mt_eq S).comp continuous_fst)
  have h3 := ((h1.matrix_mul (continuous_const (y := Matrix.single a.2.1 a.2.2.1
    (if a.2.2.2 then Complex.I else 1)))).matrix_mul h2).matrix_elem i j
  exact (continuous_abs.comp (Complex.continuous_re.comp h3)).add (continuous_abs.comp (Complex.continuous_im.comp h3))

/- English proof (translation)
Unfold `Formalism.IndefR.Datum.actO`. Rewrite using `[Matrix.mul_add, Matrix.add_mul]`.
-/
theorem actO_add' {S T : HSp D} (g : GA D S) (h : GA D T) (x y : WO S T) :
    Formalism.IndefR.Datum.actO S T g h (x + y) = Formalism.IndefR.Datum.actO S T g h x + Formalism.IndefR.Datum.actO S T g h y := by
  unfold Formalism.IndefR.Datum.actO
  rw [Matrix.mul_add, Matrix.add_mul]

/- English proof (translation)
Unfold `Formalism.IndefR.Datum.actO`. Rewrite using `[Matrix.mul_zero, Matrix.zero_mul]`.
-/
theorem actO_zero' {S T : HSp D} (g : GA D S) (h : GA D T) : Formalism.IndefR.Datum.actO S T g h 0 = 0 := by
  unfold Formalism.IndefR.Datum.actO
  rw [Matrix.mul_zero, Matrix.zero_mul]

/- English proof (translation)
Unfold `Formalism.IndefR.Datum.actO`. Rewrite using `[Matrix.mul_neg, Matrix.neg_mul]`.
-/
theorem actO_neg' {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    Formalism.IndefR.Datum.actO S T g h (-x) = -Formalism.IndefR.Datum.actO S T g h x := by
  unfold Formalism.IndefR.Datum.actO
  rw [Matrix.mul_neg, Matrix.neg_mul]

open GlobalTheory.Size in

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Use `⟨1, fun l hl x _ g hg => ?_⟩` and prove the remaining obligations. Take `rfl : l = []` from `List.eq_nil_of_length_eq_zero hl`. Rewrite using `[wordAct_nil, l2O_om_apply_eq_of_isThetaFunO hom hμ.1 hμ.2.1 hg, sobO_zero, ENNReal.coe_one, one_mul]`.

Consider the case `succ k ih`. Take `⟨C, hC⟩` from `ih`. Use `⟨C * B, fun l hl x hx g hg => ?_⟩` and prove the remaining obligations. Take `⟨g1, h1⟩` from `x`. Establish `hne : l ≠ []` using `by rintro rfl; simp at hl`.

Rewrite using `[← List.dropLast_append_getLast hne, wordAct_append, wordAct_cons, wordAct_nil]`. Use `set a := l.getLast hne`. Establish `e` using `dRho_om hom hθ g1 h1 a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)) hg`. Establish `e' : heisDer ψ θ a (om (g1, h1) g) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)) (om (g1, h1) g)` using `rfl`. Rewrite using `[e', e]`.

Establish `hg'` using `GlobalTheory.OrientedHeis.theta_dRho hθ hom.std a.1 (compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) * Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) * compAt θ a.1 (Formalism.L2.Theta.mt S g1)) hg`. Establish `hs : ENNReal.ofReal (∑ i, ∑ j, (|((compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) * Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) * compAt θ a.1 (Formalism.L2.Theta.mt S g1)) i j).re| + |((compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) * Matrix.single a.2.1 a.2.2.1 (if …`. Rewrite using `[← ENNReal.ofReal_coe_nnreal]`. Use `ENNReal.ofReal_le_ofReal (le_trans ?_ (hB _ hx))` and prove the remaining obligations. Unfold `dirSize`.

Conclude with `Finset.single_le_sum (f := fun a : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool => ∑ i, ∑ j, (|((compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) * Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) * compAt θ a.1 (Formalism.L2.Theta.mt S g1)) i j).re| + |((compAt θ a.1 (F …`. Combine the equalities or inequalities in the displayed calculation. Conclude with `sobO_dRho_le hom.std hθ hg a.1 _ k`. Use `_ ≤ C * (B * sobO ψ θ μ 𝓕 (k + 1) g) := by gcongr`. Use `_ = ((C * B : ℝ≥0) : ℝ≥0∞) * sobO ψ θ μ 𝓕 (k + 1) g := by push_cast; ring`.
-/
theorem word_om_le {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ)
    {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓕) {K : Set (GA D S × GA D T)}
    (B : ℝ≥0) (hB : ∀ x ∈ K, dirSize θ S T x ≤ B) (k : ℕ) :
    ∃ C : ℝ≥0, ∀ l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), l.length = k → ∀ x ∈ K,
      ∀ g, IsThetaFunO ψ S T g → l2O μ 𝓕 (wordAct (heisDer ψ θ) l (om x g)) ≤ C * sobO ψ θ μ 𝓕 k g := by
  induction k with
  | zero =>
    refine ⟨1, fun l hl x _ g hg => ?_⟩
    obtain rfl : l = [] := List.eq_nil_of_length_eq_zero hl
    rw [wordAct_nil, l2O_om_apply_eq_of_isThetaFunO hom hμ.1 hμ.2.1 hg, sobO_zero, ENNReal.coe_one, one_mul]
  | succ k ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨C * B, fun l hl x hx g hg => ?_⟩
    obtain ⟨g1, h1⟩ := x
    have hne : l ≠ [] := by rintro rfl; simp at hl
    rw [← List.dropLast_append_getLast hne, wordAct_append, wordAct_cons, wordAct_nil]
    set a := l.getLast hne
    have e := dRho_om hom hθ g1 h1 a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)) hg
    have e' : heisDer ψ θ a (om (g1, h1) g) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ a.1
        (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)) (om (g1, h1) g) := rfl
    rw [e', e]
    have hg' := GlobalTheory.OrientedHeis.theta_dRho hθ hom.std a.1 (compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) *
      Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) * compAt θ a.1 (Formalism.L2.Theta.mt S g1)) hg
    have hs : ENNReal.ofReal (∑ i, ∑ j, (|((compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) *
        Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) * compAt θ a.1 (Formalism.L2.Theta.mt S g1)) i j).re| +
        |((compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) *
        Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) * compAt θ a.1 (Formalism.L2.Theta.mt S g1)) i j).im|))
        ≤ B := by
      rw [← ENNReal.ofReal_coe_nnreal]
      refine ENNReal.ofReal_le_ofReal (le_trans ?_ (hB _ hx))
      unfold dirSize
      exact Finset.single_le_sum (f := fun a : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool => ∑ i, ∑ j,
        (|((compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) * Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) *
          compAt θ a.1 (Formalism.L2.Theta.mt S g1)) i j).re| +
         |((compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) * Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) *
          compAt θ a.1 (Formalism.L2.Theta.mt S g1)) i j).im|))
        (fun b _ => by positivity) (Finset.mem_univ a)
    calc _ ≤ (C : ℝ≥0∞) * sobO ψ θ μ 𝓕 k _ := hC _ (by simp [hl]) _ hx _ hg'
      _ ≤ C * (ENNReal.ofReal _ * sobO ψ θ μ 𝓕 (k + 1) g) := by
          gcongr
          exact sobO_dRho_le hom.std hθ hg a.1 _ k
      _ ≤ C * (B * sobO ψ θ μ 𝓕 (k + 1) g) := by gcongr
      _ = ((C * B : ℝ≥0) : ℝ≥0∞) * sobO ψ θ μ 𝓕 (k + 1) g := by push_cast; ring

end UpperTheory.Lit.Rallis.ThetaDens.WeilCompact

open UpperTheory.Lit.Rallis.ThetaDens.WeilCompact GlobalTheory.Size in

/- English proof (translation)
Introduce `D ψ S T χS χT om hom θ hθ μ 𝓕 hμ K hK U hU`. Set `U' : AddSubgroup (WO S T)` to `{ carrier := {u | ∀ x ∈ K, Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ u ∈ U} add_mem' := fun {a b} ha hb x hx => by`. Rewrite `ha`, `hb` using `[Set.mem_setOf_eq]`. Use `show Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ (a + b) ∈ U`. Rewrite using `[actO_add']`.

Conclude with `U.add_mem (ha x hx) (hb x hx)`. Use the proof step `zero_mem' := fun x _ => by show Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ 0 ∈ U`. Rewrite using `[actO_zero']`. Conclude with `U.zero_mem`. Use the proof step `neg_mem' := fun {a} ha x hx => by show Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ (-a) ∈ U`.

Rewrite using `[actO_neg']`. Conclude with `U.neg_mem (ha x hx) }`. Establish `hU' : IsOpen (U' : Set (WO S T))`. Use `U'.isOpen_of_mem_nhds (g := 0) ?_` and prove the remaining obligations. Use `hK.eventually_forall_of_forall_eventually (x₀ := (0 : WO S T)) (P := fun u x => Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ u ∈ U) fun x _ => ?_` and prove the remaining obligations.

Establish `hc : Continuous fun p : WO S T × (GA D S × GA D T) => Formalism.IndefR.Datum.actO S T p.2.1⁻¹ p.2.2⁻¹ p.1`. Unfold `Formalism.IndefR.Datum.actO`. Conclude with `(((continuous_mt_eq T).comp continuous_snd.snd.inv).matrix_mul continuous_fst).matrix_mul ((continuous_mt_eq S).comp continuous_snd.fst.inv.inv)`. Use `(hU.preimage hc).mem_nhds ?_` and prove the remaining obligations. Use `show Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ 0 ∈ U`.

Rewrite using `[actO_zero']`. Conclude with `U.zero_mem`. Take `⟨B0, hB0⟩` from `hK.bddAbove_image (continuous_dirSize hθ S T).continuousOn`. Establish `hB : ∀ x ∈ K, dirSize θ S T x ≤ (B0.toNNReal : ℝ)` using `fun x hx => (hB0 ⟨x, hx, rfl⟩).trans (Real.le_coe_toNNReal B0)`. Use `⟨U', hU', fun f hf x hx => ⟨hom.om_pres x f hf.1, fun u hu h0 => ?_⟩, fun d => ?_⟩` and prove the remaining obligations.

Take `⟨g, h⟩` from `x`. Establish `hv : Formalism.IndefR.Datum.actO S T g⁻¹ h⁻¹ u ∈ U` using `hu (g, h) hx`. Establish `hv0 : (Formalism.IndefR.Datum.actO S T g⁻¹ h⁻¹ u).map (infPart D) = 0`. Unfold `Formalism.IndefR.Datum.actO`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, h0]`.

Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[actO_actO_inv]`. Use `_ = om (g, h) (heisO ψ S T (Formalism.IndefR.Datum.actO S T g⁻¹ h⁻¹ u) f) := (hom.om_heis g h _ f hf.1).symm`. Use `_ = om (g, h) f := by rw [hf.2 _ hv hv0]`.

Use `choose C hC using word_om_le hom hθ hμ _ hB`. Use `⟨d, ∑ k ∈ Finset.range (d + 1), ∑ _a : Fin k → D.what₂.Tau × Fin T.rank × Fin S.rank × Bool, C k, fun f hf x hx => ?_⟩` and prove the remaining obligations. Use `show wordSum (heisDer ψ θ) (l2O μ 𝓕) d (om x f) ≤ _`. Unfold `wordSum`. Rewrite using `[ENNReal.coe_finset_sum, Finset.sum_mul]`.

Use `Finset.sum_le_sum fun k hk => ?_` and prove the remaining obligations. Rewrite using `[ENNReal.coe_finset_sum, Finset.sum_mul]`. Use `Finset.sum_le_sum fun a _ => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Conclude with `sobO_mono (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))`.
-/
theorem UpperTheory.Lit.Rallis.ThetaDens.om_compact_sobCont : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ K : Set (GA D S × GA D T), IsCompact K → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ U' : AddSubgroup (WO S T), IsOpen (U' : Set (WO S T)) ∧ (∀ f ∈ thetaLevel ψ S T U, ∀ x ∈ K, om x f ∈ thetaLevel ψ S T U') ∧ ∀ d : ℕ, ∃ (d' : ℕ) (C : ℝ≥0), ∀ f ∈ thetaLevel ψ S T U, ∀ x ∈ K, sobO ψ θ μ 𝓕 d (om x f) ≤ C * sobO ψ θ μ 𝓕 d' f := by
  intro D ψ S T χS χT om hom θ hθ μ 𝓕 hμ K hK U hU
  let U' : AddSubgroup (WO S T) :=
    { carrier := {u | ∀ x ∈ K, Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ u ∈ U}
      add_mem' := fun {a b} ha hb x hx => by
        rw [Set.mem_setOf_eq] at ha hb
        show Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ (a + b) ∈ U
        rw [actO_add']; exact U.add_mem (ha x hx) (hb x hx)
      zero_mem' := fun x _ => by
        show Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ 0 ∈ U
        rw [actO_zero']; exact U.zero_mem
      neg_mem' := fun {a} ha x hx => by
        show Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ (-a) ∈ U
        rw [actO_neg']; exact U.neg_mem (ha x hx) }
  have hU' : IsOpen (U' : Set (WO S T)) := by
    refine U'.isOpen_of_mem_nhds (g := 0) ?_
    refine hK.eventually_forall_of_forall_eventually (x₀ := (0 : WO S T))
      (P := fun u x => Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ u ∈ U) fun x _ => ?_
    have hc : Continuous fun p : WO S T × (GA D S × GA D T) => Formalism.IndefR.Datum.actO S T p.2.1⁻¹ p.2.2⁻¹ p.1 := by
      unfold Formalism.IndefR.Datum.actO
      exact (((continuous_mt_eq T).comp continuous_snd.snd.inv).matrix_mul continuous_fst).matrix_mul
        ((continuous_mt_eq S).comp continuous_snd.fst.inv.inv)
    refine (hU.preimage hc).mem_nhds ?_
    show Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ 0 ∈ U
    rw [actO_zero']; exact U.zero_mem
  obtain ⟨B0, hB0⟩ := hK.bddAbove_image (continuous_dirSize hθ S T).continuousOn
  have hB : ∀ x ∈ K, dirSize θ S T x ≤ (B0.toNNReal : ℝ) := fun x hx =>
    (hB0 ⟨x, hx, rfl⟩).trans (Real.le_coe_toNNReal B0)
  refine ⟨U', hU', fun f hf x hx => ⟨hom.om_pres x f hf.1, fun u hu h0 => ?_⟩, fun d => ?_⟩
  · obtain ⟨g, h⟩ := x
    have hv : Formalism.IndefR.Datum.actO S T g⁻¹ h⁻¹ u ∈ U := hu (g, h) hx
    have hv0 : (Formalism.IndefR.Datum.actO S T g⁻¹ h⁻¹ u).map (infPart D) = 0 := by
      unfold Formalism.IndefR.Datum.actO
      rw [Matrix.map_mul, Matrix.map_mul, h0]; simp
    calc heisO ψ S T u (om (g, h) f)
        = heisO ψ S T (Formalism.IndefR.Datum.actO S T g h (Formalism.IndefR.Datum.actO S T g⁻¹ h⁻¹ u)) (om (g, h) f) := by
          rw [actO_actO_inv]
      _ = om (g, h) (heisO ψ S T (Formalism.IndefR.Datum.actO S T g⁻¹ h⁻¹ u) f) := (hom.om_heis g h _ f hf.1).symm
      _ = om (g, h) f := by rw [hf.2 _ hv hv0]
  · choose C hC using word_om_le hom hθ hμ _ hB
    refine ⟨d, ∑ k ∈ Finset.range (d + 1), ∑ _a : Fin k → D.what₂.Tau × Fin T.rank × Fin S.rank × Bool, C k,
      fun f hf x hx => ?_⟩
    show wordSum (heisDer ψ θ) (l2O μ 𝓕) d (om x f) ≤ _
    unfold wordSum
    rw [ENNReal.coe_finset_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [ENNReal.coe_finset_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun a _ => ?_
    calc _ ≤ (C k : ℝ≥0∞) * sobO ψ θ μ 𝓕 k f := hC k _ (List.length_ofFn) x hx f hf.1
      _ ≤ C k * sobO ψ θ μ 𝓕 d f := by
          gcongr
          exact sobO_mono (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))

end
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

/- English proof (translation)
Apply the tactic sequence `first | exact @UpperTheory.Lit.Rallis.ThetaDens.om_compact_sobCont | exact UpperTheory.Lit.Rallis.ThetaDens.om_compact_sobCont | (intros; apply UpperTheory.Lit.Rallis.ThetaDens.om_compact_sobCont <;> assumption)`.
-/
theorem _root_.UpperTheory.Lit.Rallis.T.exists_common_level_sobolev_bound_weil_compact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ K : Set (GA D S × GA D T), IsCompact K → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ U' : AddSubgroup (WO S T), IsOpen (U' : Set (WO S T)) ∧ (∀ f ∈ thetaLevel ψ S T U, ∀ x ∈ K, om x f ∈ thetaLevel ψ S T U') ∧ ∀ d : ℕ, ∃ (d' : ℕ) (C : ℝ≥0), ∀ f ∈ thetaLevel ψ S T U, ∀ x ∈ K, sobO ψ θ μ 𝓕 d (om x f) ≤ C * sobO ψ θ μ 𝓕 d' f := by
  first | exact @UpperTheory.Lit.Rallis.ThetaDens.om_compact_sobCont | exact UpperTheory.Lit.Rallis.ThetaDens.om_compact_sobCont | (intros; apply UpperTheory.Lit.Rallis.ThetaDens.om_compact_sobCont <;> assumption)
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

noncomputable section

namespace UpperTheory.Lit.Rallis.ThetaDensSup
open GlobalTheory

/- English proof (translation)
Introduce `D ψ hψ θ hθ S T μ 𝓕 hm U hU`. Use `haveI : LocallyCompactSpace (WO S T) := (GlobalTheory.MixModel.lattice_Mx D T.rank S.rank).2.1`. Take `⟨K₀, hK₀n, hK₀U, hK₀c⟩` from `local_compact_nhds (hU.mem_nhds U.zero_mem)`. Take `⟨C, hC⟩` from `GlobalTheory.LevelSupBound.pointwise (S := S) (T := T) hψ hθ hK₀n hK₀c`. Use `⟨Module.finrank ℝ (GlobalTheory.FockCompare.RW T S), C, fun f hf w => ?_⟩` and prove the remaining obligations.

Establish `h` using `hC μ 𝓕 hm 1 one_pos f hf.1 (fun u hu hinf => by rw [one_smul]; exact hf.2 u (hK₀U hu) hinf) w`. Use `h.trans (le_of_eq ?_)` and prove the remaining obligations. Use `congr 1`. Simplify using the standard rewrite rules.
-/
theorem sup_le_sobO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ (d : ℕ) (C : ℝ≥0), ∀ f ∈ thetaLevel ψ S T U, ∀ w, ‖f w‖ₑ ≤ C * sobO ψ θ μ 𝓕 d f := by
  intro D ψ hψ θ hθ S T μ 𝓕 hm U hU
  haveI : LocallyCompactSpace (WO S T) := (GlobalTheory.MixModel.lattice_Mx D T.rank S.rank).2.1
  obtain ⟨K₀, hK₀n, hK₀U, hK₀c⟩ := local_compact_nhds (hU.mem_nhds U.zero_mem)
  obtain ⟨C, hC⟩ := GlobalTheory.LevelSupBound.pointwise (S := S) (T := T) hψ hθ hK₀n hK₀c
  refine ⟨Module.finrank ℝ (GlobalTheory.FockCompare.RW T S), C, fun f hf w => ?_⟩
  have h := hC μ 𝓕 hm 1 one_pos f hf.1 (fun u hu hinf => by rw [one_smul]; exact hf.2 u (hK₀U hu) hinf) w
  refine h.trans (le_of_eq ?_)
  congr 1
  simp

end UpperTheory.Lit.Rallis.ThetaDensSup
end
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

/- English proof (translation)
Apply the tactic sequence `first | exact @UpperTheory.Lit.Rallis.ThetaDensSup.sup_le_sobO | exact UpperTheory.Lit.Rallis.ThetaDensSup.sup_le_sobO | (intros; apply UpperTheory.Lit.Rallis.ThetaDensSup.sup_le_sobO <;> assumption)`.
-/
theorem _root_.UpperTheory.Lit.Rallis.T.exists_sobolev_bound_theta_pointwise : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ (d : ℕ) (C : ℝ≥0), ∀ f ∈ thetaLevel ψ S T U, ∀ w, ‖f w‖ₑ ≤ C * sobO ψ θ μ 𝓕 d f := by
  first | exact @UpperTheory.Lit.Rallis.ThetaDensSup.sup_le_sobO | exact UpperTheory.Lit.Rallis.ThetaDensSup.sup_le_sobO | (intros; apply UpperTheory.Lit.Rallis.ThetaDensSup.sup_le_sobO <;> assumption)
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

noncomputable section

namespace UpperTheory.Lit.Rallis.ThetaDensCauchy
open GlobalTheory

open GlobalTheory.Size

section

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons a l ih`. Rewrite using `[GlobalTheory.Size.wordAct_cons, ih]`. Conclude with `GlobalTheory.Size.dRho_add hψ hθ a.1 _ (GlobalTheory.Size.theta_word hψ hθ l h) (GlobalTheory.Size.theta_word hψ hθ l h')`.
-/
theorem word_add (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool))
    {f f' : WO S T → ℂ} (h : IsThetaFunO ψ S T f) (h' : IsThetaFunO ψ S T f') :
    GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (f + f') =
      GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f + GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f' := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [GlobalTheory.Size.wordAct_cons, ih]
    exact GlobalTheory.Size.dRho_add hψ hθ a.1 _ (GlobalTheory.Size.theta_word hψ hθ l h) (GlobalTheory.Size.theta_word hψ hθ l h')

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact h`. Consider the case `cons a l ih`. Rewrite using `[GlobalTheory.Size.wordAct_cons]`. Conclude with `GlobalTheory.Size.dRho_mem_thetaLevel hψ hθ ih a.1 _`.
-/
theorem word_mem (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool))
    {U : AddSubgroup (WO S T)} {f : WO S T → ℂ} (h : f ∈ thetaLevel ψ S T U) :
    GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f ∈ thetaLevel ψ S T U := by
  induction l with
  | nil => exact h
  | cons a l ih =>
    rw [GlobalTheory.Size.wordAct_cons]
    exact GlobalTheory.Size.dRho_mem_thetaLevel hψ hθ ih a.1 _

/- English proof (translation)
Proceed by induction on `l generalizing d with`. Consider the case `nil => exact le_rfl`. Consider the case `cons a l ih`. Rewrite using `[GlobalTheory.Size.wordAct_cons]`. Use `(GlobalTheory.Size.sobO_heisDer_le d a).trans ((ih (d + 1)).trans (le_of_eq ?_))` and prove the remaining obligations.

Use `congr 1`. Simplify using `only [List.length_cons]`. Use linear arithmetic over natural numbers and integers.
-/
theorem sobO_word_le (μ : Measure (WO S T)) (𝓕 : Set (WO S T))
    (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) (f : WO S T → ℂ) (d : ℕ) :
    sobO ψ θ μ 𝓕 d (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f) ≤ sobO ψ θ μ 𝓕 (d + l.length) f := by
  induction l generalizing d with
  | nil => exact le_rfl
  | cons a l ih =>
    rw [GlobalTheory.Size.wordAct_cons]
    refine (GlobalTheory.Size.sobO_heisDer_le d a).trans ((ih (d + 1)).trans (le_of_eq ?_))
    congr 1
    simp only [List.length_cons]
    omega

end

/- English proof (translation)
Introduce `D ψ hψ θ hθ S T μ 𝓕 hm U hU u hu hC l`. Take `⟨d₀, C, hb⟩` from `UpperTheory.Lit.Rallis.ThetaDensSup.sup_le_sobO D ψ hψ θ hθ S T μ 𝓕 hm U hU`. Rewrite using `[Metric.uniformCauchySeqOn_iff]`. Introduce `ε hε`. Establish `hη : (0 : ℝ) < ε / (C + 1)` using `by positivity`.

Take `⟨J, hJ⟩` from `hC (d₀ + l.length) (ENNReal.ofReal (ε / (C + 1))) (ENNReal.ofReal_pos.2 hη)`. Use `⟨J, fun i hi j hj w _ => ?_⟩` and prove the remaining obligations. Establish `hd : u i - u j ∈ thetaLevel ψ S T U` using `Submodule.sub_mem _ (hu i) (hu j)`. Establish `he` using `word_add hψ hθ l hd.1 (hu j).1`. Rewrite `he` using `[sub_add_cancel]`.

Establish `h1` using `(hb _ (word_mem hψ hθ l hd) w).trans (mul_le_mul_right ((sobO_word_le μ 𝓕 l _ d₀).trans (hJ i hi j hj).le) _)`. Rewrite using `[dist_eq_norm, he, Pi.add_apply, add_sub_cancel_right]`. Rewrite `h1` using `[← ofReal_norm, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_le_ofReal_iff (by positivity)]`. Use `h1.trans_lt ?_` and prove the remaining obligations. Rewrite using `[← mul_div_assoc, div_lt_iff₀ (by positivity)]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem uniformCauchySeqOn_word : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ u : ℕ → WO S T → ℂ, (∀ j, u j ∈ thetaLevel ψ S T U) → (∀ d, ∀ ε : ℝ≥0∞, 0 < ε → ∃ J, ∀ i ≥ J, ∀ j ≥ J, sobO ψ θ μ 𝓕 d (u i - u j) < ε) → ∀ l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), UniformCauchySeqOn (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) Filter.atTop Set.univ := by
  intro D ψ hψ θ hθ S T μ 𝓕 hm U hU u hu hC l
  obtain ⟨d₀, C, hb⟩ := UpperTheory.Lit.Rallis.ThetaDensSup.sup_le_sobO D ψ hψ θ hθ S T μ 𝓕 hm U hU
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hη : (0 : ℝ) < ε / (C + 1) := by positivity
  obtain ⟨J, hJ⟩ := hC (d₀ + l.length) (ENNReal.ofReal (ε / (C + 1))) (ENNReal.ofReal_pos.2 hη)
  refine ⟨J, fun i hi j hj w _ => ?_⟩
  have hd : u i - u j ∈ thetaLevel ψ S T U := Submodule.sub_mem _ (hu i) (hu j)
  have he := word_add hψ hθ l hd.1 (hu j).1
  rw [sub_add_cancel] at he
  have h1 := (hb _ (word_mem hψ hθ l hd) w).trans
    (mul_le_mul_right ((sobO_word_le μ 𝓕 l _ d₀).trans (hJ i hi j hj).le) _)
  rw [dist_eq_norm, he, Pi.add_apply, add_sub_cancel_right]
  rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
  refine h1.trans_lt ?_
  rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
  nlinarith

end UpperTheory.Lit.Rallis.ThetaDensCauchy
end
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

/- English proof (translation)
Apply the tactic sequence `first | exact @UpperTheory.Lit.Rallis.ThetaDensCauchy.uniformCauchySeqOn_word | exact UpperTheory.Lit.Rallis.ThetaDensCauchy.uniformCauchySeqOn_word | (intros; apply UpperTheory.Lit.Rallis.ThetaDensCauchy.uniformCauchySeqOn_word <;> assumption)`.
-/
theorem _root_.UpperTheory.Lit.Rallis.T.uniformCauchySeqOn_heisenbergWord_sobolevCauchy : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ u : ℕ → WO S T → ℂ, (∀ j, u j ∈ thetaLevel ψ S T U) → (∀ d, ∀ ε : ℝ≥0∞, 0 < ε → ∃ J, ∀ i ≥ J, ∀ j ≥ J, sobO ψ θ μ 𝓕 d (u i - u j) < ε) → ∀ l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), UniformCauchySeqOn (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) Filter.atTop Set.univ := by
  first | exact @UpperTheory.Lit.Rallis.ThetaDensCauchy.uniformCauchySeqOn_word | exact UpperTheory.Lit.Rallis.ThetaDensCauchy.uniformCauchySeqOn_word | (intros; apply UpperTheory.Lit.Rallis.ThetaDensCauchy.uniformCauchySeqOn_word <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace UpperTheory.Lit.Rallis.ThetaDens
open GlobalTheory

/- English proof (translation)
Rewrite using `[ENNReal.tendsto_nhds_zero]`. Introduce `ε hε`. Take `⟨δ, hδ0, hδ⟩` from `ENNReal.lt_iff_exists_nnreal_btwn.1 hε`. Establish `hδ0' : (0 : ℝ) < δ` using `by exact_mod_cast hδ0`. Use `filter_upwards [Metric.tendstoUniformly_iff.1 h δ hδ0'] with j hj`.

Establish `hb : ∀ᵐ x ∂ν, ‖(g j - f) x‖ ≤ δ` using `Filter.Eventually.of_forall fun x => by`. Use `(hj x).le` as an intermediate fact. Rewrite `this` using `[dist_comm, dist_eq_norm]`. Then use the resulting hypothesis. Use `(eLpNorm_le_of_ae_bound hb).trans ?_` and prove the remaining obligations. Simplify `hδ.le` using `[hν]`.
-/
theorem eLpNorm_sub_tendsto_of_unif {X : Type} [MeasurableSpace X] (ν : Measure X) (hν : ν Set.univ = 1)
    (g : ℕ → X → ℂ) (f : X → ℂ) (h : TendstoUniformly g f Filter.atTop) :
    Filter.Tendsto (fun j => eLpNorm (g j - f) 2 ν) Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ0, hδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hε
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  filter_upwards [Metric.tendstoUniformly_iff.1 h δ hδ0'] with j hj
  have hb : ∀ᵐ x ∂ν, ‖(g j - f) x‖ ≤ δ := Filter.Eventually.of_forall fun x => by
    have := (hj x).le
    rwa [dist_comm, dist_eq_norm] at this
  refine (eLpNorm_le_of_ae_bound hb).trans ?_
  simpa [hν] using hδ.le

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons a l ih`. Rewrite using `[GlobalTheory.Size.wordAct_cons, ih, GlobalTheory.Size.wordAct_cons, GlobalTheory.Size.wordAct_cons, sub_eq_add_neg, sub_eq_add_neg, ← neg_one_smul ℂ, ← neg_one_smul ℂ (GlobalTheory.Size.heisDer ψ θ a _)]`. Simplify using `only [GlobalTheory.Size.heisDer]`.

Rewrite using `[GlobalTheory.Size.dRho_add hψ hθ a.1 _ (GlobalTheory.Size.theta_word hψ hθ l hf) (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.Size.theta_word hψ hθ l hg)), GlobalTheory.Size.dRho_smul]`.
-/
theorem wordAct_heisDer_sub {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D}
    (hθ : IsInfFam θ) {S T : HSp D} {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g)
    (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) :
    GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (f - g) =
      GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f - GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [GlobalTheory.Size.wordAct_cons, ih, GlobalTheory.Size.wordAct_cons, GlobalTheory.Size.wordAct_cons, sub_eq_add_neg, sub_eq_add_neg,
      ← neg_one_smul ℂ, ← neg_one_smul ℂ (GlobalTheory.Size.heisDer ψ θ a _)]
    simp only [GlobalTheory.Size.heisDer]
    rw [GlobalTheory.Size.dRho_add hψ hθ a.1 _ (GlobalTheory.Size.theta_word hψ hθ l hf)
      (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.Size.theta_word hψ hθ l hg)), GlobalTheory.Size.dRho_smul]

/- English proof (translation)
Introduce `D ψ hψ θ hθ S T μ 𝓕 hμ u f hf hu hl d`. Establish `key : ∀ l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), Filter.Tendsto (fun j => GlobalTheory.Size.l2O μ 𝓕 (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j - f))) Filter.atTop (nhds 0)`. Introduce `l`. Simplify using `only [wordAct_heisDer_sub hψ hθ (hu _) hf l, GlobalTheory.Size.l2O]`. Conclude with `eLpNorm_sub_tendsto_of_unif _ (by rw [Measure.restrict_apply_univ]; exact hμ.2.2) _ _ (hl l)`.

Use `tendsto_finset_sum (Finset.range (d + 1)) fun k _ => tendsto_finset_sum (Finset.univ : Finset (Fin k → D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) fun a _ => key (List.ofFn a)` as an intermediate fact. Simplify using `only [Finset.sum_const_zero] at this`. Conclude with `this`.
-/
theorem sobO_sub_tendsto_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (u : ℕ → WO S T → ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ j, IsThetaFunO ψ S T (u j)) → (∀ l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), TendstoUniformly (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f) Filter.atTop) → ∀ d, Filter.Tendsto (fun j => sobO ψ θ μ 𝓕 d (u j - f)) Filter.atTop (nhds 0) := by
  intro D ψ hψ θ hθ S T μ 𝓕 hμ u f hf hu hl d
  have key : ∀ l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), Filter.Tendsto
      (fun j => GlobalTheory.Size.l2O μ 𝓕 (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j - f))) Filter.atTop (nhds 0) := by
    intro l
    simp only [wordAct_heisDer_sub hψ hθ (hu _) hf l, GlobalTheory.Size.l2O]
    exact eLpNorm_sub_tendsto_of_unif _ (by rw [Measure.restrict_apply_univ]; exact hμ.2.2) _ _ (hl l)
  have := tendsto_finset_sum (Finset.range (d + 1)) fun k _ =>
    tendsto_finset_sum (Finset.univ : Finset (Fin k → D.what₂.Tau × Fin T.rank × Fin S.rank × Bool))
      fun a _ => key (List.ofFn a)
  simp only [Finset.sum_const_zero] at this
  exact this

end UpperTheory.Lit.Rallis.ThetaDens
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

/- English proof (translation)
Apply the tactic sequence `first | exact @UpperTheory.Lit.Rallis.ThetaDens.sobO_sub_tendsto_zero | exact UpperTheory.Lit.Rallis.ThetaDens.sobO_sub_tendsto_zero | (intros; apply UpperTheory.Lit.Rallis.ThetaDens.sobO_sub_tendsto_zero <;> assumption)`.
-/
theorem _root_.UpperTheory.Lit.Rallis.T.thetaSobolevSeminorm_sub_tendsto_zero_of_words_unif : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (u : ℕ → WO S T → ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ j, IsThetaFunO ψ S T (u j)) → (∀ l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), TendstoUniformly (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f) Filter.atTop) → ∀ d, Filter.Tendsto (fun j => sobO ψ θ μ 𝓕 d (u j - f)) Filter.atTop (nhds 0) := by
  first | exact @UpperTheory.Lit.Rallis.ThetaDens.sobO_sub_tendsto_zero | exact UpperTheory.Lit.Rallis.ThetaDens.sobO_sub_tendsto_zero | (intros; apply UpperTheory.Lit.Rallis.ThetaDens.sobO_sub_tendsto_zero <;> assumption)
end

section

noncomputable section

open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace UpperTheory.Lit.Rallis.ThetaLimDeriv
open GlobalTheory

/- English proof (translation)
Rewrite `h`, the goal using `[Metric.tendstoUniformly_iff]`. Introduce `ε hε`. Use `filter_upwards [h ε hε] with j hj t`. Use `hj (w + x t)` as an intermediate fact. Rewrite `this`, the goal using `[dist_eq_norm]`.

Simplify using `only [heisO]`. Rewrite using `[← mul_sub, norm_mul, hψ.1.2.1, one_mul]`. Conclude with `this`.
-/
theorem tendstoUniformly_heisO {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {G : ℕ → WO S T → ℂ} {F : WO S T → ℂ} (h : TendstoUniformly G F Filter.atTop) (x : ℝ → WO S T) (w : WO S T) :
    TendstoUniformly (fun j t => heisO ψ S T (x t) (G j) w) (fun t => heisO ψ S T (x t) F w) Filter.atTop := by
  rw [Metric.tendstoUniformly_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with j hj t
  have := hj (w + x t)
  rw [dist_eq_norm] at this ⊢
  simp only [heisO]
  rw [← mul_sub, norm_mul, hψ.1.2.1, one_mul]
  exact this

/- English proof (translation)
Introduce `D ψ hψ θ hθ S T G F F' hG hF a hF'`. Establish `hL` using `GlobalTheory.OrientedHeis.isRealDir_lineAt (S := S) (T := T) hθ a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1))`. Establish `e : ∀ f, GlobalTheory.Size.heisDer ψ θ a f = GlobalTheory.OrientedHeis.dLine ψ S T (lineAt θ a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1))) f` using `fun _ => rfl`. Simplify using `only [e] at hF' ⊢`. Generalize the expression as in `lineAt θ a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)) = L at hL hF' ⊢`.

Use function extensionality and compare the values at `w`. Establish `h1` using `tendstoUniformly_heisO hψ hF L w`. Establish `h2` using `tendstoUniformly_heisO hψ hF' L w`. Establish `h3` using `hasDerivAt_of_tendstoUniformly h2 (Filter.Eventually.of_forall fun j s => GlobalTheory.OrientedHeis.hasDerivAt_heisO hθ hψ hL (hG j) w s) (fun s => h1.tendsto_at s) 0`. Establish `h4` using `h3.deriv`.

Rewrite `h4` using `[map_zero, GlobalTheory.OrientedHeis.heisO_zero]`. Conclude with `h4`.
-/
theorem heisDer_of_tendstoUniformly : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (G : ℕ → WO S T → ℂ) (F F' : WO S T → ℂ), (∀ j, IsThetaFunO ψ S T (G j)) → TendstoUniformly G F Filter.atTop → ∀ a : (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), TendstoUniformly (fun j => GlobalTheory.Size.heisDer ψ θ a (G j)) F' Filter.atTop → GlobalTheory.Size.heisDer ψ θ a F = F' := by
  intro D ψ hψ θ hθ S T G F F' hG hF a hF'
  have hL := GlobalTheory.OrientedHeis.isRealDir_lineAt (S := S) (T := T) hθ a.1
    (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1))
  have e : ∀ f, GlobalTheory.Size.heisDer ψ θ a f = GlobalTheory.OrientedHeis.dLine ψ S T
      (lineAt θ a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1))) f := fun _ => rfl
  simp only [e] at hF' ⊢
  generalize lineAt θ a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)) = L at hL hF' ⊢
  funext w
  have h1 := tendstoUniformly_heisO hψ hF L w
  have h2 := tendstoUniformly_heisO hψ hF' L w
  have h3 := hasDerivAt_of_tendstoUniformly h2
    (Filter.Eventually.of_forall fun j s => GlobalTheory.OrientedHeis.hasDerivAt_heisO hθ hψ hL (hG j) w s)
    (fun s => h1.tendsto_at s) 0
  have h4 := h3.deriv
  rw [map_zero, GlobalTheory.OrientedHeis.heisO_zero] at h4
  exact h4

end UpperTheory.Lit.Rallis.ThetaLimDeriv

end
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

/- English proof (translation)
Apply the tactic sequence `first | exact @UpperTheory.Lit.Rallis.ThetaLimDeriv.heisDer_of_tendstoUniformly | exact UpperTheory.Lit.Rallis.ThetaLimDeriv.heisDer_of_tendstoUniformly | (intros; apply UpperTheory.Lit.Rallis.ThetaLimDeriv.heisDer_of_tendstoUniformly <;> assumption)`.
-/
theorem _root_.UpperTheory.Lit.Rallis.T.heisenbergBasisDeriv_eq_of_uniform_limits : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (G : ℕ → WO S T → ℂ) (F F' : WO S T → ℂ), (∀ j, IsThetaFunO ψ S T (G j)) → TendstoUniformly G F Filter.atTop → ∀ a : (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), TendstoUniformly (fun j => GlobalTheory.Size.heisDer ψ θ a (G j)) F' Filter.atTop → GlobalTheory.Size.heisDer ψ θ a F = F' := by
  first | exact @UpperTheory.Lit.Rallis.ThetaLimDeriv.heisDer_of_tendstoUniformly | exact UpperTheory.Lit.Rallis.ThetaLimDeriv.heisDer_of_tendstoUniformly | (intros; apply UpperTheory.Lit.Rallis.ThetaLimDeriv.heisDer_of_tendstoUniformly <;> assumption)
end

section
open scoped ContDiff Topology

namespace UpperTheory.Lit.Rallis
open GlobalTheory

open Filter

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.sum_empty]`. Introduce `u hu x`. Conclude with `⟨Set.univ, Filter.univ_mem, Filter.Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu⟩`.

Consider the case `insert a s ha ih`. Simplify using `only [Finset.sum_insert ha]`. Establish `h1 : TendstoLocallyUniformly (fun j y => f a j y • L a) (fun y => ψ a y • L a) atTop` using `((ContinuousLinearMap.id ℂ ℂ).smulRight (L a)).uniformContinuous.comp_tendstoLocallyUniformly (h a)`. Conclude with `h1.add ih`.
-/
theorem tendstoLocallyUniformly_sum_smul_const {E : Type} [TopologicalSpace E] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℂ F] {A : Type} (s : Finset A) (L : A → F)
    (f : A → ℕ → E → ℂ) (ψ : A → E → ℂ)
    (h : ∀ a, TendstoLocallyUniformly (f a) (ψ a) atTop) :
    TendstoLocallyUniformly (fun j y => ∑ a ∈ s, f a j y • L a)
      (fun y => ∑ a ∈ s, ψ a y • L a) atTop := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    intro u hu x
    exact ⟨Set.univ, Filter.univ_mem, Filter.Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu⟩
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have h1 : TendstoLocallyUniformly (fun j y => f a j y • L a) (fun y => ψ a y • L a) atTop :=
      ((ContinuousLinearMap.id ℂ ℂ).smulRight (L a)).uniformContinuous.comp_tendstoLocallyUniformly (h a)
    exact h1.add ih

/- English proof (translation)
Introduce `E _ _ A _ v c hc φ g ψ hg hφ hψ y`. Establish `key : ∀ (T : E →L[ℝ] ℂ), T = ∑ a, T (v a) • ((c a).smulRight (1 : ℂ))`. Introduce `T`. Use extensionality with `x`. Use `conv_lhs => rw [← hc x]`.

Simplify using `[map_sum, map_smul, mul_comm]`. Establish `hlim` using `tendstoLocallyUniformly_sum_smul_const (F := E →L[ℝ] ℂ) Finset.univ (fun a => (c a).smulRight (1 : ℂ)) (fun a j y => fderiv ℝ (g j) y (v a)) ψ hψ`. Establish `hlim' : TendstoLocallyUniformly (fun j y => fderiv ℝ (g j) y) (fun y => ∑ a, ψ a y • ((c a).smulRight (1 : ℂ))) atTop`. Establish `e : (fun j y => fderiv ℝ (g j) y) = fun j y => ∑ a, fderiv ℝ (g j) y (v a) • ((c a).smulRight (1 : ℂ))`. Use function extensionality and compare the values at `j z`.

Conclude with `key _`. Rewrite using `[e]`. Conclude with `hlim`. Establish `hd : HasFDerivAt φ (∑ a, ψ a y • ((c a).smulRight (1 : ℂ))) y` using `hasFDerivAt_of_tendstoLocallyUniformlyOn (l := atTop) (s := Set.univ) (f := g) (f' := fun j y => fderiv ℝ (g j) y) isOpen_univ (tendstoLocallyUniformlyOn_univ.2 hlim') (fun j x _ => (hg j x).hasFDerivAt) (fun x _ => (tendstoLocallyUniformlyOn_univ.2 hφ).tendsto_at (Set.mem_univ x …`. Use `⟨hd.differentiableAt, fun a => ?_⟩` and prove the remaining obligations.

Rewrite using `[hd.fderiv]`. Establish `h1` using `(tendstoLocallyUniformlyOn_univ.2 hlim').tendsto_at (Set.mem_univ y)`. Establish `h2` using `(tendstoLocallyUniformlyOn_univ.2 (hψ a)).tendsto_at (Set.mem_univ y)`. Establish `h3` using `((ContinuousLinearMap.apply ℝ ℂ (v a)).continuous.tendsto _).comp h1`. Conclude with `tendsto_nhds_unique h3 h2`.
-/
theorem differentiableAt_of_tendstoLocallyUniformly_directional :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Type} [Fintype A] (v : A → E) (c : A → E →L[ℝ] ℝ), (∀ x, ∑ a, c a x • v a = x) → ∀ (φ : E → ℂ) (g : ℕ → E → ℂ) (ψ : A → E → ℂ), (∀ j, Differentiable ℝ (g j)) → TendstoLocallyUniformly g φ Filter.atTop → (∀ a, TendstoLocallyUniformly (fun j y => fderiv ℝ (g j) y (v a)) (ψ a) Filter.atTop) → ∀ y, DifferentiableAt ℝ φ y ∧ ∀ a, fderiv ℝ φ y (v a) = ψ a y := by
  intro E _ _ A _ v c hc φ g ψ hg hφ hψ y
  have key : ∀ (T : E →L[ℝ] ℂ), T = ∑ a, T (v a) • ((c a).smulRight (1 : ℂ)) := by
    intro T
    ext x
    conv_lhs => rw [← hc x]
    simp [map_sum, map_smul, mul_comm]
  have hlim := tendstoLocallyUniformly_sum_smul_const (F := E →L[ℝ] ℂ) Finset.univ
    (fun a => (c a).smulRight (1 : ℂ)) (fun a j y => fderiv ℝ (g j) y (v a)) ψ hψ
  have hlim' : TendstoLocallyUniformly (fun j y => fderiv ℝ (g j) y)
      (fun y => ∑ a, ψ a y • ((c a).smulRight (1 : ℂ))) atTop := by
    have e : (fun j y => fderiv ℝ (g j) y) = fun j y =>
        ∑ a, fderiv ℝ (g j) y (v a) • ((c a).smulRight (1 : ℂ)) := by
      funext j z
      exact key _
    rw [e]
    exact hlim
  have hd : HasFDerivAt φ (∑ a, ψ a y • ((c a).smulRight (1 : ℂ))) y :=
    hasFDerivAt_of_tendstoLocallyUniformlyOn (l := atTop) (s := Set.univ) (f := g)
      (f' := fun j y => fderiv ℝ (g j) y) isOpen_univ
      (tendstoLocallyUniformlyOn_univ.2 hlim')
      (fun j x _ => (hg j x).hasFDerivAt)
      (fun x _ => (tendstoLocallyUniformlyOn_univ.2 hφ).tendsto_at (Set.mem_univ x))
      (Set.mem_univ y)
  refine ⟨hd.differentiableAt, fun a => ?_⟩
  rw [hd.fderiv]
  have h1 := (tendstoLocallyUniformlyOn_univ.2 hlim').tendsto_at (Set.mem_univ y)
  have h2 := (tendstoLocallyUniformlyOn_univ.2 (hψ a)).tendsto_at (Set.mem_univ y)
  have h3 := ((ContinuousLinearMap.apply ℝ ℂ (v a)).continuous.tendsto _).comp h1
  exact tendsto_nhds_unique h3 h2

end UpperTheory.Lit.Rallis
end

section
open scoped ContDiff Topology

/- English proof (translation)
Apply the tactic sequence `first | exact @UpperTheory.Lit.Rallis.differentiableAt_of_tendstoLocallyUniformly_directional | exact UpperTheory.Lit.Rallis.differentiableAt_of_tendstoLocallyUniformly_directional | (intros; apply UpperTheory.Lit.Rallis.differentiableAt_of_tendstoLocallyUniformly_directional <;> …`.
-/
theorem _root_.UpperTheory.Lit.Rallis.T.differentiableAt_limit_of_directional_derivs_converge : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Type} [Fintype A] (v : A → E) (c : A → E →L[ℝ] ℝ), (∀ x, ∑ a, c a x • v a = x) → ∀ (φ : E → ℂ) (g : ℕ → E → ℂ) (ψ : A → E → ℂ), (∀ j, Differentiable ℝ (g j)) → TendstoLocallyUniformly g φ Filter.atTop → (∀ a, TendstoLocallyUniformly (fun j y => fderiv ℝ (g j) y (v a)) (ψ a) Filter.atTop) → ∀ y, DifferentiableAt ℝ φ y ∧ ∀ a, fderiv ℝ φ y (v a) = ψ a y := by
  first | exact @UpperTheory.Lit.Rallis.differentiableAt_of_tendstoLocallyUniformly_directional | exact UpperTheory.Lit.Rallis.differentiableAt_of_tendstoLocallyUniformly_directional | (intros; apply UpperTheory.Lit.Rallis.differentiableAt_of_tendstoLocallyUniformly_directional <;> assumption)
end

section
open scoped ContDiff Topology

namespace UpperTheory.Lit.Rallis
open GlobalTheory

/- English proof (translation)
Introduce `E _ _ A _ v c hc P hP`. Establish `key : ∀ φ, P φ → Differentiable ℝ φ ∧ ∃ (α χ : A → E → ℂ), (∀ a, ContDiff ℝ ∞ (α a)) ∧ (∀ a, P (χ a)) ∧ fderiv ℝ φ = fun y => ∑ a, (α a y * φ y + χ a y) • ((c a).smulRight (1 : ℂ))`. Introduce `φ hφ`. Take `⟨g, hg, hlim, hd⟩` from `hP φ hφ`. Use `choose α hα χ hχ hlim' using hd`.

Establish `h` using `UpperTheory.Lit.Rallis.T.differentiableAt_limit_of_directional_derivs_converge v c hc φ g (fun a y => α a y * φ y + χ a y) hg hlim hlim'`. Use `⟨fun y => (h y).1, α, χ, hα, hχ, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `y`. Use extensionality with `x`. Use `conv_lhs => rw [← hc x]`.

Simplify using `only [map_sum, map_smul, (h y).2, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [Complex.real_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `main : ∀ n : ℕ, ∀ φ, P φ → ContDiff ℝ n φ`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `φ hφ`. Simplify using `using (key φ hφ).1.continuous`.

Consider the case `succ n ih`. Introduce `φ hφ`. Take `⟨hd, α, χ, hα, hχ, hf⟩` from `key φ hφ`. Establish `: ContDiff ℝ ((n : WithTop ℕ∞) + 1) φ`. Rewrite using `[contDiff_succ_iff_fderiv]`.

Use `⟨hd, by simp, ?_⟩` and prove the remaining obligations. Rewrite using `[hf]`. Use `ContDiff.sum fun a _ => ?_` and prove the remaining obligations. Establish `h1 : ContDiff ℝ n (α a)` using `(hα a).of_le (by exact_mod_cast le_top)`. Conclude with `((h1.mul (ih φ hφ)).add (ih _ (hχ a))).smul contDiff_const`.

Conclude with `this` after adjusting the coercions. Introduce `φ hφ`. Conclude with `contDiff_infty.2 fun n => main n φ hφ`.
-/
theorem contDiff_of_class_tendstoLocallyUniformly : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Type} [Fintype A] (v : A → E) (c : A → E →L[ℝ] ℝ), (∀ x, ∑ a, c a x • v a = x) → ∀ P : (E → ℂ) → Prop, (∀ φ, P φ → ∃ g : ℕ → E → ℂ, (∀ j, Differentiable ℝ (g j)) ∧ TendstoLocallyUniformly g φ Filter.atTop ∧ ∀ a, ∃ α : E → ℂ, ContDiff ℝ ∞ α ∧ ∃ χ, P χ ∧ TendstoLocallyUniformly (fun j y => fderiv ℝ (g j) y (v a)) (fun y => α y * φ y + χ y) Filter.atTop) → ∀ φ, P φ → ContDiff ℝ ∞ φ := by
  intro E _ _ A _ v c hc P hP
  have key : ∀ φ, P φ → Differentiable ℝ φ ∧ ∃ (α χ : A → E → ℂ), (∀ a, ContDiff ℝ ∞ (α a)) ∧
      (∀ a, P (χ a)) ∧ fderiv ℝ φ =
        fun y => ∑ a, (α a y * φ y + χ a y) • ((c a).smulRight (1 : ℂ)) := by
    intro φ hφ
    obtain ⟨g, hg, hlim, hd⟩ := hP φ hφ
    choose α hα χ hχ hlim' using hd
    have h := UpperTheory.Lit.Rallis.T.differentiableAt_limit_of_directional_derivs_converge v c hc φ g (fun a y => α a y * φ y + χ a y) hg hlim hlim'
    refine ⟨fun y => (h y).1, α, χ, hα, hχ, ?_⟩
    funext y
    ext x
    conv_lhs => rw [← hc x]
    simp only [map_sum, map_smul, (h y).2, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Complex.real_smul, smul_eq_mul]
    ring
  have main : ∀ n : ℕ, ∀ φ, P φ → ContDiff ℝ n φ := by
    intro n
    induction n with
    | zero =>
      intro φ hφ
      simpa using (key φ hφ).1.continuous
    | succ n ih =>
      intro φ hφ
      obtain ⟨hd, α, χ, hα, hχ, hf⟩ := key φ hφ
      have : ContDiff ℝ ((n : WithTop ℕ∞) + 1) φ := by
        rw [contDiff_succ_iff_fderiv]
        refine ⟨hd, by simp, ?_⟩
        rw [hf]
        refine ContDiff.sum fun a _ => ?_
        have h1 : ContDiff ℝ n (α a) := (hα a).of_le (by exact_mod_cast le_top)
        exact ((h1.mul (ih φ hφ)).add (ih _ (hχ a))).smul contDiff_const
      exact_mod_cast this
  intro φ hφ
  exact contDiff_infty.2 fun n => main n φ hφ

end UpperTheory.Lit.Rallis
end

section
open scoped ContDiff Topology

/- English proof (translation)
Apply the tactic sequence `first | exact @UpperTheory.Lit.Rallis.contDiff_of_class_tendstoLocallyUniformly | exact UpperTheory.Lit.Rallis.contDiff_of_class_tendstoLocallyUniformly | (intros; apply UpperTheory.Lit.Rallis.contDiff_of_class_tendstoLocallyUniformly <;> assumption)`.
-/
theorem _root_.UpperTheory.Lit.Rallis.T.smooth_of_limit_class_stable_under_directional_derivs : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Type} [Fintype A] (v : A → E) (c : A → E →L[ℝ] ℝ), (∀ x, ∑ a, c a x • v a = x) → ∀ P : (E → ℂ) → Prop, (∀ φ, P φ → ∃ g : ℕ → E → ℂ, (∀ j, Differentiable ℝ (g j)) ∧ TendstoLocallyUniformly g φ Filter.atTop ∧ ∀ a, ∃ α : E → ℂ, ContDiff ℝ ∞ α ∧ ∃ χ, P χ ∧ TendstoLocallyUniformly (fun j y => fderiv ℝ (g j) y (v a)) (fun y => α y * φ y + χ y) Filter.atTop) → ∀ φ, P φ → ContDiff ℝ ∞ φ := by
  first | exact @UpperTheory.Lit.Rallis.contDiff_of_class_tendstoLocallyUniformly | exact UpperTheory.Lit.Rallis.contDiff_of_class_tendstoLocallyUniformly | (intros; apply UpperTheory.Lit.Rallis.contDiff_of_class_tendstoLocallyUniformly <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace UpperTheory.Lit.Rallis.ThetaDens
open GlobalTheory

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.Size in

/- English proof (translation)
Introduce `w`. Use `UpperTheory.Lit.Rallis.T.smooth_of_limit_class_stable_under_directional_derivs v c hv (fun φ => ∃ l, φ = fun y => F l (w + ι y)) ?_ _ ⟨l, rfl⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨l, rfl⟩`. Establish `hU : ∀ l, TendstoLocallyUniformly (fun j y => g l j (w + ι y)) (fun y => F l (w + ι y)) Filter.atTop` using `fun l => ((hF l).comp fun y => w + ι y).tendstoLocallyUniformly`. Use `⟨fun j y => g l j (w + ι y), fun j => (hg l j w).differentiable (by simp), hU l, fun a => ?_⟩` and prove the remaining obligations.

Establish `h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x : R => (om.flip (v a) (p w + x) : ℝ)` using `(LinearMap.toContinuousLinearMap (om.flip (v a))).contDiff.comp (contDiff_const.add contDiff_id)`. Establish `hα : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x : R => (Real.pi * Complex.I : ℂ) * ((om.flip (v a) (p w + x) : ℝ) : ℂ)` using `contDiff_const.mul (Complex.ofRealCLM.contDiff.comp h1)`. Use `⟨_, hα, _, ⟨a :: l, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hc : Continuous fun y => F l (w + ι y)` using `(hU l).continuous (Filter.Eventually.of_forall fun j => (hg l j w).continuous).frequently`. Establish `h0 : TendstoLocallyUniformly (fun (_ : ℕ) (x : R) => (Real.pi * Complex.I : ℂ) * ((om.flip (v a) (p w + x) : ℝ) : ℂ)) (fun x : R => (Real.pi * Complex.I : ℂ) * ((om.flip (v a) (p w + x) : ℝ) : ℂ)) Filter.atTop` using `fun U hU x => ⟨Set.univ, Filter.univ_mem, Filter.Eventually.of_forall fun _ _ _ => refl_mem_uniformity hU⟩`.

Establish `h2` using `(h0.mul₀ (hU l) hα.continuous hc).add (hU (a :: l))`. Establish `e : (fun j y => fderiv ℝ (fun y => g l j (w + ι y)) y (v a)) = fun j x => (Real.pi * Complex.I : ℂ) * ((om.flip (v a) (p w + x) : ℝ) : ℂ) * g l j (w + ι x) + g (a :: l) j (w + ι x)`. Use function extensionality and compare the values at `j x`. Rewrite using `[hd, hD_eq_fderiv ι p om _ (hg l j), map_add p, hp, LinearMap.flip_apply]`. Use `fderiv_comp_add_left (𝕜 := ℝ) (f := fun y : R => g l j (w + ι y)) (x := 0) x` as an intermediate fact.

Rewrite `this` using `[add_zero]`. Establish `e2 : (fun y : R => g l j (w + ι x + ι y)) = fun y => g l j (w + ι (x + y))`. Use function extensionality and compare the values at `y`. Rewrite using `[map_add, add_assoc]`. Rewrite using `[← this, e2]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `h2`.
-/
theorem sm_of_tendstoUniformly_words {G R A : Type} [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R]
    [FiniteDimensional ℝ R] [Fintype A] (ι : R →+ G) (p : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (hp : ∀ x, p (ι x) = x)
    (v : A → R) (c : A → R →L[ℝ] ℝ) (hv : ∀ x, ∑ a, c a x • v a = x) (g : List A → ℕ → G → ℂ)
    (hg : ∀ l j, Sm ι (g l j)) (hd : ∀ a l j, g (a :: l) j = hD ι p om (v a) (g l j)) (F : List A → G → ℂ)
    (hF : ∀ l, TendstoUniformly (g l) (F l) Filter.atTop) (l : List A) : Sm ι (F l) := by
  intro w
  refine UpperTheory.Lit.Rallis.T.smooth_of_limit_class_stable_under_directional_derivs v c hv (fun φ => ∃ l, φ = fun y => F l (w + ι y)) ?_ _ ⟨l, rfl⟩
  rintro _ ⟨l, rfl⟩
  have hU : ∀ l, TendstoLocallyUniformly (fun j y => g l j (w + ι y)) (fun y => F l (w + ι y)) Filter.atTop :=
    fun l => ((hF l).comp fun y => w + ι y).tendstoLocallyUniformly
  refine ⟨fun j y => g l j (w + ι y), fun j => (hg l j w).differentiable (by simp), hU l, fun a => ?_⟩
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x : R => (om.flip (v a) (p w + x) : ℝ) :=
    (LinearMap.toContinuousLinearMap (om.flip (v a))).contDiff.comp (contDiff_const.add contDiff_id)
  have hα : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      fun x : R => (Real.pi * Complex.I : ℂ) * ((om.flip (v a) (p w + x) : ℝ) : ℂ) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp h1)
  refine ⟨_, hα, _, ⟨a :: l, rfl⟩, ?_⟩
  have hc : Continuous fun y => F l (w + ι y) :=
    (hU l).continuous (Filter.Eventually.of_forall fun j => (hg l j w).continuous).frequently
  have h0 : TendstoLocallyUniformly
      (fun (_ : ℕ) (x : R) => (Real.pi * Complex.I : ℂ) * ((om.flip (v a) (p w + x) : ℝ) : ℂ))
      (fun x : R => (Real.pi * Complex.I : ℂ) * ((om.flip (v a) (p w + x) : ℝ) : ℂ)) Filter.atTop :=
    fun U hU x => ⟨Set.univ, Filter.univ_mem, Filter.Eventually.of_forall fun _ _ _ => refl_mem_uniformity hU⟩
  have h2 := (h0.mul₀ (hU l) hα.continuous hc).add (hU (a :: l))
  have e : (fun j y => fderiv ℝ (fun y => g l j (w + ι y)) y (v a)) = fun j x =>
      (Real.pi * Complex.I : ℂ) * ((om.flip (v a) (p w + x) : ℝ) : ℂ) * g l j (w + ι x) + g (a :: l) j (w + ι x) := by
    funext j x
    rw [hd, hD_eq_fderiv ι p om _ (hg l j), map_add p, hp, LinearMap.flip_apply]
    have := fderiv_comp_add_left (𝕜 := ℝ) (f := fun y : R => g l j (w + ι y)) (x := 0) x
    rw [add_zero] at this
    have e2 : (fun y : R => g l j (w + ι x + ι y)) = fun y => g l j (w + ι (x + y)) := by
      funext y
      rw [map_add, add_assoc]
    rw [← this, e2]
    ring
  rw [e]
  exact h2

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, hv, Fintype.sum_prod_type, Matrix.single_apply]`. Rewrite using `[Finset.sum_eq_single τ (fun b _ hb => by simp [hb.symm]) (by simp), Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp), Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]`. Simplify using `[add_comm]`.
-/
theorem sum_coord_single {τs : Type} [Fintype τs] {m n : ℕ} (x : τs → Fin m → Fin n → ℂ)
    (v : τs × Fin m × Fin n × Bool → τs → Fin m → Fin n → ℂ)
    (hv : ∀ a τ i j, v a τ i j = if τ = a.1 then
      Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) i j else 0) :
    ∑ a : τs × Fin m × Fin n × Bool,
      (if a.2.2.2 then (x a.1 a.2.1 a.2.2.1).im else (x a.1 a.2.1 a.2.2.1).re) • v a = x := by
  funext τ i j
  simp only [Finset.sum_apply, Pi.smul_apply, hv, Fintype.sum_prod_type, Matrix.single_apply]
  rw [Finset.sum_eq_single τ (fun b _ hb => by simp [hb.symm]) (by simp),
    Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp),
    Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
  simp [add_comm]

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.Size in

/- English proof (translation)
Introduce `D ψ hψ θ hθ S T u hu F hF l`. Take `⟨σ, h⟩` from `GlobalTheory.RealLineAt.exists_inverse_chart hθ`. Use `((smooth_iff_sm_and_real_lines D θ σ h T S).1 (F l)).2 ?_` and prove the remaining obligations. Set `z : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool → Matrix (Fin T.rank) (Fin S.rank) ℂ` to `fun a => Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)`. Set `c : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool → RW T S →L[ℝ] ℝ` to `fun a => (if a.2.2.2 then Complex.imCLM else Complex.reCLM).comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin S.rank => ℂ) a.2.2.1).comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin T.rank => Fin S.rank → ℂ) a.2.1).comp (ContinuousLinearMap.proj (R := ℝ) (φ := f …`.

Use `sm_of_tendstoUniformly_words (iotaW σ T S) (piW θ T S) (omO S T) (h.pi_iota T S) (fun a => piW θ T S (lineAt θ a.1 (z a) 1)) c (fun x => ?_) (fun l j => wordAct (heisDer ψ θ) l (u j)) (fun l j => theta_sm h (theta_word hψ hθ l (hu j))) (fun a l j => dLine_eq_hD h hψ (isRealDir_li …` and prove the remaining obligations. Use `Eq.trans ?_ (sum_coord_single x (fun a => piW θ T S (lineAt θ a.1 (z a) 1)) fun a τ i j => ?_)` and prove the remaining obligations. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `congr 1`. Take `⟨τ, i, j, b⟩` from `a`.

Apply the tactic sequence `cases b <;> rfl`. Use `congrFun (congrFun ((GlobalTheory.OrientedHeis.isLineAt_lineAt hθ a.1 (z a)).2.2 1 τ) i) j` as an intermediate fact. Use `Eq.trans this ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp [z, *]`.
-/
theorem contDiff_of_tendstoUniformly_words : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (u : ℕ → WO S T → ℂ), (∀ j, IsThetaFunO ψ S T (u j)) → ∀ F : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) → WO S T → ℂ, (∀ l, TendstoUniformly (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (F l) Filter.atTop) → ∀ (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) (k : ℕ) (L : (Fin k → ℝ) →+ WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => F l (w + L t) := by
  intro D ψ hψ θ hθ S T u hu F hF l
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  refine ((smooth_iff_sm_and_real_lines D θ σ h T S).1 (F l)).2 ?_
  let z : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool → Matrix (Fin T.rank) (Fin S.rank) ℂ := fun a =>
    Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)
  let c : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool → RW T S →L[ℝ] ℝ := fun a =>
    (if a.2.2.2 then Complex.imCLM else Complex.reCLM).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin S.rank => ℂ) a.2.2.1).comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin T.rank => Fin S.rank → ℂ) a.2.1).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin T.rank → Fin S.rank → ℂ) a.1)))
  refine sm_of_tendstoUniformly_words (iotaW σ T S) (piW θ T S) (omO S T) (h.pi_iota T S)
    (fun a => piW θ T S (lineAt θ a.1 (z a) 1)) c (fun x => ?_) (fun l j => wordAct (heisDer ψ θ) l (u j))
    (fun l j => theta_sm h (theta_word hψ hθ l (hu j)))
    (fun a l j => dLine_eq_hD h hψ (isRealDir_lineAt hθ a.1 (z a)) _) F hF l
  refine Eq.trans ?_ (sum_coord_single x (fun a => piW θ T S (lineAt θ a.1 (z a) 1)) fun a τ i j => ?_)
  · refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    obtain ⟨τ, i, j, b⟩ := a
    cases b <;> rfl
  · have := congrFun (congrFun ((GlobalTheory.OrientedHeis.isLineAt_lineAt hθ a.1 (z a)).2.2 1 τ) i) j
    refine Eq.trans this ?_
    split_ifs <;> simp [z, *]

end UpperTheory.Lit.Rallis.ThetaDens
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

/- English proof (translation)
Apply the tactic sequence `first | exact @UpperTheory.Lit.Rallis.ThetaDens.contDiff_of_tendstoUniformly_words | exact UpperTheory.Lit.Rallis.ThetaDens.contDiff_of_tendstoUniformly_words | (intros; apply UpperTheory.Lit.Rallis.ThetaDens.contDiff_of_tendstoUniformly_words <;> assumption)`.
-/
theorem _root_.UpperTheory.Lit.Rallis.T.theta_word_limits_smooth_along_real_points : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (u : ℕ → WO S T → ℂ), (∀ j, IsThetaFunO ψ S T (u j)) → ∀ F : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) → WO S T → ℂ, (∀ l, TendstoUniformly (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (F l) Filter.atTop) → ∀ (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) (k : ℕ) (L : (Fin k → ℝ) →+ WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => F l (w + L t) := by
  first | exact @UpperTheory.Lit.Rallis.ThetaDens.contDiff_of_tendstoUniformly_words | exact UpperTheory.Lit.Rallis.ThetaDens.contDiff_of_tendstoUniformly_words | (intros; apply UpperTheory.Lit.Rallis.ThetaDens.contDiff_of_tendstoUniformly_words <;> assumption)
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace UpperTheory.Lit.Rallis.ThetaComplete
open GlobalTheory

/- English proof (translation)
Introduce `D ψ S T U u hu f hf`. Establish `ht : ∀ w, Filter.Tendsto (fun j => u j w) Filter.atTop (nhds (f w))` using `fun w => hf.tendsto_at w`. Use `⟨fun γ w => ?_, fun x hx h0 => ?_, hf.continuous (Filter.Frequently.of_forall fun j => (hu j).1.cont)⟩` and prove the remaining obligations. Use `tendsto_nhds_unique (ht _) ?_` and prove the remaining obligations. Establish `e : (fun j => u j (ratW T S γ + w)) = fun j => ψ (-(symplOH S T (ratW T S γ) w)) * u j w`.

Use function extensionality and compare the values at `fun j => (hu j).1.quasi γ w`. Rewrite using `[e]`. Conclude with `(ht w).const_mul _`. Use function extensionality and compare the values at `w`. Use `tendsto_nhds_unique ((ht (w + x)).const_mul (ψ (symplOH S T w x))) ?_` and prove the remaining obligations.

Establish `e : (fun j => ψ (symplOH S T w x) * u j (w + x)) = fun j => u j w`. Use function extensionality and compare the values at `fun j => congrFun ((hu j).2 x hx h0) w`. Rewrite using `[e]`. Conclude with `ht w`.
-/
theorem lim_clauses : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (U : AddSubgroup (WO S T)) (u : ℕ → WO S T → ℂ), (∀ j, u j ∈ thetaLevel ψ S T U) → ∀ f : WO S T → ℂ, TendstoUniformly u f Filter.atTop → (∀ γ w, f (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * f w) ∧ (∀ x ∈ U, x.map (infPart D) = 0 → heisO ψ S T x f = f) ∧ Continuous f := by
  intro D ψ S T U u hu f hf
  have ht : ∀ w, Filter.Tendsto (fun j => u j w) Filter.atTop (nhds (f w)) := fun w => hf.tendsto_at w
  refine ⟨fun γ w => ?_, fun x hx h0 => ?_, hf.continuous (Filter.Frequently.of_forall fun j => (hu j).1.cont)⟩
  · refine tendsto_nhds_unique (ht _) ?_
    have e : (fun j => u j (ratW T S γ + w)) = fun j => ψ (-(symplOH S T (ratW T S γ) w)) * u j w :=
      funext fun j => (hu j).1.quasi γ w
    rw [e]
    exact (ht w).const_mul _
  · funext w
    refine tendsto_nhds_unique ((ht (w + x)).const_mul (ψ (symplOH S T w x))) ?_
    have e : (fun j => ψ (symplOH S T w x) * u j (w + x)) = fun j => u j w :=
      funext fun j => congrFun ((hu j).2 x hx h0) w
    rw [e]
    exact ht w

/- English proof (translation)
The claim follows from `UpperTheory.Lit.Rallis.T.heisenbergBasisDeriv_eq_of_uniform_limits`.
-/
theorem lim_deriv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (G : ℕ → WO S T → ℂ) (F F' : WO S T → ℂ), (∀ j, IsThetaFunO ψ S T (G j)) → TendstoUniformly G F Filter.atTop → ∀ a : (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), TendstoUniformly (fun j => GlobalTheory.Size.heisDer ψ θ a (G j)) F' Filter.atTop → GlobalTheory.Size.heisDer ψ θ a F = F' := UpperTheory.Lit.Rallis.T.heisenbergBasisDeriv_eq_of_uniform_limits
/- English proof (translation)
The claim follows from `UpperTheory.Lit.Rallis.T.theta_word_limits_smooth_along_real_points`.
-/
theorem lim_smooth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (u : ℕ → WO S T → ℂ), (∀ j, IsThetaFunO ψ S T (u j)) → ∀ F : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) → WO S T → ℂ, (∀ l, TendstoUniformly (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (F l) Filter.atTop) → ∀ (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) (k : ℕ) (L : (Fin k → ℝ) →+ WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => F l (w + L t) := UpperTheory.Lit.Rallis.T.theta_word_limits_smooth_along_real_points

/- English proof (translation)
Introduce `D ψ hψ θ hθ S T U hU u hu F hF`. Establish `h0` using `lim_clauses D ψ S T U u hu (F []) (hF [])`. Establish `hth : IsThetaFunO ψ S T (F [])` using `⟨h0.1, ⟨U, hU, h0.2.1⟩, h0.2.2, lim_smooth D ψ hψ θ hθ S T u (fun j => (hu j).1) F hF []⟩`. Use `⟨⟨hth, h0.2.1⟩, fun l => ?_⟩` and prove the remaining obligations. Proceed by induction on `l with`.

Consider the case `nil => rfl`. Consider the case `cons a l ih`. Rewrite using `[GlobalTheory.Size.wordAct_cons, ih]`. Conclude with `lim_deriv D ψ hψ θ hθ S T (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (F l) (F (a :: l)) (fun j => GlobalTheory.Size.theta_word hψ hθ l (hu j).1) (hF l) a (hF (a :: l))`.
-/
theorem limit_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ u : ℕ → WO S T → ℂ, (∀ j, u j ∈ thetaLevel ψ S T U) → ∀ F : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) → WO S T → ℂ, (∀ l, TendstoUniformly (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (F l) Filter.atTop) → F [] ∈ thetaLevel ψ S T U ∧ ∀ l, GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (F []) = F l := by
  intro D ψ hψ θ hθ S T U hU u hu F hF
  have h0 := lim_clauses D ψ S T U u hu (F []) (hF [])
  have hth : IsThetaFunO ψ S T (F []) :=
    ⟨h0.1, ⟨U, hU, h0.2.1⟩, h0.2.2, lim_smooth D ψ hψ θ hθ S T u (fun j => (hu j).1) F hF []⟩
  refine ⟨⟨hth, h0.2.1⟩, fun l => ?_⟩
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [GlobalTheory.Size.wordAct_cons, ih]
    exact lim_deriv D ψ hψ θ hθ S T (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (F l) (F (a :: l))
      (fun j => GlobalTheory.Size.theta_word hψ hθ l (hu j).1) (hF l) a (hF (a :: l))

/- English proof (translation)
Introduce `D ψ hψ θ hθ S T μ 𝓕 hμ U hU u hu hc`. Establish `hC` using `UpperTheory.Lit.Rallis.T.uniformCauchySeqOn_heisenbergWord_sobolevCauchy D ψ hψ θ hθ S T μ 𝓕 hμ U hU u hu hc`. Establish `hlim : ∀ l w, ∃ z, Filter.Tendsto (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j) w) Filter.atTop (nhds z)` using `fun l w => cauchySeq_tendsto_of_complete ((hC l).cauchySeq (Set.mem_univ w))`. Use `choose F hF using hlim`. Establish `hFu : ∀ l, TendstoUniformly (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (F l) Filter.atTop` using `fun l => tendstoUniformlyOn_univ.1 ((hC l).tendstoUniformlyOn_of_tendsto fun w _ => hF l w)`.

Take `⟨h1, h2⟩` from `limit_theta D ψ hψ θ hθ S T U hU u hu F hFu`. Use `⟨F [], h1, UpperTheory.Lit.Rallis.T.thetaSobolevSeminorm_sub_tendsto_zero_of_words_unif D ψ hψ θ hθ S T μ 𝓕 hμ u (F []) h1.1 (fun j => (hu j).1) fun l => ?_⟩` and prove the remaining obligations. Rewrite using `[h2 l]`. Conclude with `hFu l`.
-/
theorem complete : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ u : ℕ → WO S T → ℂ, (∀ j, u j ∈ thetaLevel ψ S T U) → (∀ d, ∀ ε : ℝ≥0∞, 0 < ε → ∃ J, ∀ i ≥ J, ∀ j ≥ J, sobO ψ θ μ 𝓕 d (u i - u j) < ε) → ∃ f ∈ thetaLevel ψ S T U, ∀ d, Filter.Tendsto (fun j => sobO ψ θ μ 𝓕 d (u j - f)) Filter.atTop (nhds 0) := by
  intro D ψ hψ θ hθ S T μ 𝓕 hμ U hU u hu hc
  have hC := UpperTheory.Lit.Rallis.T.uniformCauchySeqOn_heisenbergWord_sobolevCauchy D ψ hψ θ hθ S T μ 𝓕 hμ U hU u hu hc
  have hlim : ∀ l w, ∃ z, Filter.Tendsto (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j) w) Filter.atTop (nhds z) :=
    fun l w => cauchySeq_tendsto_of_complete ((hC l).cauchySeq (Set.mem_univ w))
  choose F hF using hlim
  have hFu : ∀ l, TendstoUniformly (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (F l) Filter.atTop :=
    fun l => tendstoUniformlyOn_univ.1 ((hC l).tendstoUniformlyOn_of_tendsto fun w _ => hF l w)
  obtain ⟨h1, h2⟩ := limit_theta D ψ hψ θ hθ S T U hU u hu F hFu
  refine ⟨F [], h1, UpperTheory.Lit.Rallis.T.thetaSobolevSeminorm_sub_tendsto_zero_of_words_unif D ψ hψ θ hθ S T μ 𝓕 hμ u (F []) h1.1 (fun j => (hu j).1) fun l => ?_⟩
  rw [h2 l]
  exact hFu l

end UpperTheory.Lit.Rallis.ThetaComplete
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

/- English proof (translation)
Apply the tactic sequence `first | exact @UpperTheory.Lit.Rallis.ThetaComplete.complete | exact UpperTheory.Lit.Rallis.ThetaComplete.complete | (intros; apply UpperTheory.Lit.Rallis.ThetaComplete.complete <;> assumption)`.
-/
theorem _root_.UpperTheory.Lit.Rallis.T.thetaFunctions_open_level_complete_sobolev : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ u : ℕ → WO S T → ℂ, (∀ j, u j ∈ thetaLevel ψ S T U) → (∀ d, ∀ ε : ℝ≥0∞, 0 < ε → ∃ J, ∀ i ≥ J, ∀ j ≥ J, sobO ψ θ μ 𝓕 d (u i - u j) < ε) → ∃ f ∈ thetaLevel ψ S T U, ∀ d, Filter.Tendsto (fun j => sobO ψ θ μ 𝓕 d (u j - f)) Filter.atTop (nhds 0) := by
  first | exact @UpperTheory.Lit.Rallis.ThetaComplete.complete | exact UpperTheory.Lit.Rallis.ThetaComplete.complete | (intros; apply UpperTheory.Lit.Rallis.ThetaComplete.complete <;> assumption)
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace UpperTheory.Lit.Rallis.SobBaire
open GlobalTheory

open Filter Topology
open scoped Uniformity

/- English proof (translation)
Use `letI t : TopologicalSpace E := (SeminormFamily.moduleFilterBasis (𝕜 := ℂ) p).topology`. Establish `hp : WithSeminorms p` using `⟨rfl⟩`. Use `haveI : IsTopologicalAddGroup E := hp.topologicalAddGroup`. Use `letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E`. Use `haveI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup`.

Use `haveI : ContinuousSMul ℂ E := hp.continuousSMul`. Use `haveI : FirstCountableTopology E := hp.firstCountableTopology`. Use `haveI : (𝓤 E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated`. Use `haveI : CompleteSpace E := by`. Use `UniformSpace.complete_of_cauchySeq_tendsto fun u hu => ?_` and prove the remaining obligations.

Rewrite `hu` using `[cauchySeq_iff_tendsto, uniformity_eq_comap_nhds_zero, tendsto_comap_iff]`. Take `⟨x, hx⟩` from `hcomp u fun d ε hε => by`. Establish `h` using `(hp.tendsto_nhds _ 0).1 hu d ε hε`. Take `⟨⟨N₁, N₂⟩, hN⟩` from `eventually_atTop.1 h`. Use `⟨max N₁ N₂, fun i hi j hj => ?_⟩` and prove the remaining obligations.

Use `hN (j, i) (Prod.mk_le_mk.2 ⟨le_of_max_le_left hj, le_of_max_le_right hi⟩)` as an intermediate fact. Simplify using `using this`. Use `⟨x, (hp.tendsto_nhds u x).2 fun d ε hε => ?_⟩` and prove the remaining obligations. Conclude with `(hx d).eventually (gt_mem_nhds hε)`. Use `haveI : BarrelledSpace ℂ E := inferInstance`.

Establish `hlsc : LowerSemicontinuous q`. Rewrite using `[lowerSemicontinuous_iff_isClosed_preimage]`. Introduce `y`. Use `IsSeqClosed.isClosed fun u x hu hx => ?_` and prove the remaining obligations. Conclude with `hq u x (fun d => by`.

Use `((hp.continuous_seminorm d).tendsto 0).comp ((tendsto_sub_nhds_zero_iff).2 hx)` as an intermediate fact. Simplify `this) y hu` using `[Function.comp_def]`. Establish `hc : Continuous q` using `Seminorm.continuous_of_lowerSemicontinuous q hlsc`. Take `⟨s, C, -, hle⟩` from `Seminorm.bound_of_continuous hp q hc`. Establish `hmono' : ∀ d d' x, d ≤ d' → p d x ≤ p d' x` using `fun d d' x h => by`.

Proceed by induction on `h with`. Consider the case `refl => exact le_rfl`. Consider the case `step _ ih => exact ih.trans (hmono _ x)`. Use `⟨s.sup id, C, fun x => (hle x).trans ?_⟩` and prove the remaining obligations. Rewrite using `[Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]`.

Use `mul_le_mul_of_nonneg_left ?_ C.2` and prove the remaining obligations. Conclude with `Seminorm.finset_sup_apply_le (apply_nonneg _ _) fun i hi => hmono' _ _ _ (Finset.le_sup (f := id) hi)`.
-/
theorem exists_bound_of_complete {E : Type} [AddCommGroup E] [Module ℂ E] (p : ℕ → Seminorm ℂ E)
    (hmono : ∀ d x, p d x ≤ p (d + 1) x)
    (hcomp : ∀ u : ℕ → E, (∀ d, ∀ ε > 0, ∃ J, ∀ i ≥ J, ∀ j ≥ J, p d (u i - u j) < ε) →
      ∃ x, ∀ d, Tendsto (fun j => p d (u j - x)) atTop (𝓝 0))
    (q : Seminorm ℂ E) (hq : ∀ (u : ℕ → E) (x : E), (∀ d, Tendsto (fun j => p d (u j - x)) atTop (𝓝 0)) →
      ∀ y : ℝ, (∀ j, q (u j) ≤ y) → q x ≤ y) :
    ∃ (d : ℕ) (C : ℝ≥0), ∀ x, q x ≤ C * p d x := by
  letI t : TopologicalSpace E := (SeminormFamily.moduleFilterBasis (𝕜 := ℂ) p).topology
  have hp : WithSeminorms p := ⟨rfl⟩
  haveI : IsTopologicalAddGroup E := hp.topologicalAddGroup
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  haveI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  haveI : ContinuousSMul ℂ E := hp.continuousSMul
  haveI : FirstCountableTopology E := hp.firstCountableTopology
  haveI : (𝓤 E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  haveI : CompleteSpace E := by
    refine UniformSpace.complete_of_cauchySeq_tendsto fun u hu => ?_
    rw [cauchySeq_iff_tendsto, uniformity_eq_comap_nhds_zero, tendsto_comap_iff] at hu
    obtain ⟨x, hx⟩ := hcomp u fun d ε hε => by
      have h := (hp.tendsto_nhds _ 0).1 hu d ε hε
      obtain ⟨⟨N₁, N₂⟩, hN⟩ := eventually_atTop.1 h
      refine ⟨max N₁ N₂, fun i hi j hj => ?_⟩
      have := hN (j, i) (Prod.mk_le_mk.2 ⟨le_of_max_le_left hj, le_of_max_le_right hi⟩)
      simpa using this
    refine ⟨x, (hp.tendsto_nhds u x).2 fun d ε hε => ?_⟩
    exact (hx d).eventually (gt_mem_nhds hε)
  haveI : BarrelledSpace ℂ E := inferInstance
  have hlsc : LowerSemicontinuous q := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro y
    refine IsSeqClosed.isClosed fun u x hu hx => ?_
    exact hq u x (fun d => by
      have := ((hp.continuous_seminorm d).tendsto 0).comp ((tendsto_sub_nhds_zero_iff).2 hx)
      simpa [Function.comp_def] using this) y hu
  have hc : Continuous q := Seminorm.continuous_of_lowerSemicontinuous q hlsc
  obtain ⟨s, C, -, hle⟩ := Seminorm.bound_of_continuous hp q hc
  have hmono' : ∀ d d' x, d ≤ d' → p d x ≤ p d' x := fun d d' x h => by
    induction h with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (hmono _ x)
  refine ⟨s.sup id, C, fun x => (hle x).trans ?_⟩
  rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ C.2
  exact Seminorm.finset_sup_apply_le (apply_nonneg _ _) fun i hi => hmono' _ _ _ (Finset.le_sup (f := id) hi)

end UpperTheory.Lit.Rallis.SobBaire

namespace UpperTheory.Lit.Rallis.SobBaire
open GlobalTheory

open Filter Topology

/- English proof (translation)
Introduce `D ψ hψ θ hθ S T μ 𝓕 hm U hU N hadd hsmul hfin hlsc`. Establish `hB` using `UpperTheory.Lit.Rallis.T.thetaFunctions_open_level_complete_sobolev D ψ hψ θ hθ S T μ 𝓕 hm U hU`. Set `E` to `thetaLevel ψ S T U`. Establish `hsf : ∀ d (f : E), sobO ψ θ μ 𝓕 d (f : WO S T → ℂ) ≠ ⊤` using `fun d f => GlobalTheory.Size.sobO_ne_top hψ hθ hm.1 hm.2.1 f.2.1 d`. Set `p : ℕ → Seminorm ℂ E` to `fun d => Seminorm.of (fun f => (sobO ψ θ μ 𝓕 d (f : WO S T → ℂ)).toReal) (fun f g => by`.

Rewrite using `[← ENNReal.toReal_add (hsf d f) (hsf d g)]`. Conclude with `ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hsf d f, hsf d g⟩) (GlobalTheory.Size.sobO_add_le hψ hθ f.2.1 g.2.1 d))`. Use the proof step `(fun c f => by show (sobO ψ θ μ 𝓕 d (c • (f : WO S T → ℂ))).toReal = _`. Rewrite using `[GlobalTheory.Size.sobO_smul, ENNReal.toReal_mul, toReal_enorm])`. Establish `hp : ∀ d (f : E), p d f = (sobO ψ θ μ 𝓕 d (f : WO S T → ℂ)).toReal` using `fun _ _ => rfl`.

Set `q : Seminorm ℂ E` to `Seminorm.of (fun f => (N f).toReal) (fun f g => by`. Rewrite using `[← ENNReal.toReal_add (hfin f f.2) (hfin g g.2)]`. Conclude with `ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin f f.2, hfin g g.2⟩) (hadd f f.2 g g.2))`. Use the proof step `(fun c f => by show (N (c • (f : WO S T → ℂ))).toReal = _`. Rewrite using `[hsmul c f f.2, ENNReal.toReal_mul, toReal_enorm])`.

Establish `hq : ∀ f : E, q f = (N f).toReal` using `fun _ => rfl`. Take `⟨d, C, hC⟩` from `exists_bound_of_complete p (fun d f => by`. Rewrite using `[hp, hp]`. Conclude with `ENNReal.toReal_mono (hsf _ f) (GlobalTheory.Size.sobO_mono (Nat.le_succ d)))`. Use the proof step `(fun u hu => by`.

Take `⟨f, hf, hlim⟩` from `hB (fun j => (u j : WO S T → ℂ)) (fun j => (u j).2) fun d ε hε => by`. Break down `eq_or_ne ε ⊤ with rfl | hεt` into its components or cases. Conclude with `⟨0, fun i _ j _ => lt_top_iff_ne_top.2 (hsf d (u i - u j))⟩`. Take `⟨J, hJ⟩` from `hu d ε.toReal (ENNReal.toReal_pos hε.ne' hεt)`. Use `⟨J, fun i hi j hj => ?_⟩` and prove the remaining obligations.

Use `hJ i hi j hj` as an intermediate fact. Rewrite `this` using `[hp]`. Conclude with `(ENNReal.toReal_lt_toReal (hsf d (u i - u j)) hεt).1 this`. Use `⟨⟨f, hf⟩, fun d => ?_⟩` and prove the remaining obligations. Use `(ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hlim d)` as an intermediate fact.

Simplify `this)` using `[hp, Function.comp_def]`. Use `q (fun u x hux y hy => by`. Establish `hy0 : 0 ≤ y` using `(apply_nonneg q (u 0)).trans (hy 0)`. Establish `hconv : ∀ d, Tendsto (fun j => sobO ψ θ μ 𝓕 d ((u j : WO S T → ℂ) - x)) atTop (𝓝 0)` using `fun d => by`. Establish `h1` using `hux d`.

Simplify using `only [hp] at h1`. Rewrite `h1` using `[← ENNReal.toReal_zero]`. Conclude with `(ENNReal.tendsto_toReal_iff (fun j => hsf d (u j - x)) ENNReal.zero_ne_top).1 h1`. Establish `h2` using `hlsc (fun j => (u j : WO S T → ℂ)) (fun j => (u j).2) x x.2 hconv`. Establish `h3 : Filter.liminf (fun j => N (u j : WO S T → ℂ)) atTop ≤ ENNReal.ofReal y` using `Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun j => by`.

Rewrite using `[← ENNReal.ofReal_toReal (hfin _ (u j).2)]`. Conclude with `ENNReal.ofReal_le_ofReal ((hq _).symm.trans_le (hy j) |>.trans_eq' rfl))`. Rewrite using `[hq]`. Conclude with `ENNReal.toReal_le_of_le_ofReal hy0 (h2.trans h3))`. Use `⟨d, C, fun f hf => ?_⟩` and prove the remaining obligations.

Establish `h` using `hC ⟨f, hf⟩`. Rewrite `h` using `[hq, hp]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ENNReal.ofReal_mul (NNReal.coe_nonneg C), ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal (GlobalTheory.Size.sobO_ne_top hψ hθ hm.1 hm.2.1 hf.1 d)]`.
-/
theorem le_mul_sobO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ N : (WO S T → ℂ) → ℝ≥0∞, (∀ f ∈ thetaLevel ψ S T U, ∀ g ∈ thetaLevel ψ S T U, N (f + g) ≤ N f + N g) → (∀ (c : ℂ), ∀ f ∈ thetaLevel ψ S T U, N (c • f) = ‖c‖ₑ * N f) → (∀ f ∈ thetaLevel ψ S T U, N f ≠ ⊤) → (∀ (u : ℕ → WO S T → ℂ), (∀ j, u j ∈ thetaLevel ψ S T U) → ∀ f ∈ thetaLevel ψ S T U, (∀ d, Filter.Tendsto (fun j => sobO ψ θ μ 𝓕 d (u j - f)) Filter.atTop (nhds 0)) → N f ≤ Filter.liminf (fun j => N (u j)) Filter.atTop) → ∃ (d : ℕ) (C : ℝ≥0), ∀ f ∈ thetaLevel ψ S T U, N f ≤ C * sobO ψ θ μ 𝓕 d f := by
  intro D ψ hψ θ hθ S T μ 𝓕 hm U hU N hadd hsmul hfin hlsc
  have hB := UpperTheory.Lit.Rallis.T.thetaFunctions_open_level_complete_sobolev D ψ hψ θ hθ S T μ 𝓕 hm U hU
  let E := thetaLevel ψ S T U
  have hsf : ∀ d (f : E), sobO ψ θ μ 𝓕 d (f : WO S T → ℂ) ≠ ⊤ := fun d f =>
    GlobalTheory.Size.sobO_ne_top hψ hθ hm.1 hm.2.1 f.2.1 d
  let p : ℕ → Seminorm ℂ E := fun d => Seminorm.of (fun f => (sobO ψ θ μ 𝓕 d (f : WO S T → ℂ)).toReal)
    (fun f g => by
      rw [← ENNReal.toReal_add (hsf d f) (hsf d g)]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hsf d f, hsf d g⟩)
        (GlobalTheory.Size.sobO_add_le hψ hθ f.2.1 g.2.1 d))
    (fun c f => by
      show (sobO ψ θ μ 𝓕 d (c • (f : WO S T → ℂ))).toReal = _
      rw [GlobalTheory.Size.sobO_smul, ENNReal.toReal_mul, toReal_enorm])
  have hp : ∀ d (f : E), p d f = (sobO ψ θ μ 𝓕 d (f : WO S T → ℂ)).toReal := fun _ _ => rfl
  let q : Seminorm ℂ E := Seminorm.of (fun f => (N f).toReal)
    (fun f g => by
      rw [← ENNReal.toReal_add (hfin f f.2) (hfin g g.2)]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin f f.2, hfin g g.2⟩) (hadd f f.2 g g.2))
    (fun c f => by
      show (N (c • (f : WO S T → ℂ))).toReal = _
      rw [hsmul c f f.2, ENNReal.toReal_mul, toReal_enorm])
  have hq : ∀ f : E, q f = (N f).toReal := fun _ => rfl
  obtain ⟨d, C, hC⟩ := exists_bound_of_complete p
    (fun d f => by
      rw [hp, hp]
      exact ENNReal.toReal_mono (hsf _ f) (GlobalTheory.Size.sobO_mono (Nat.le_succ d)))
    (fun u hu => by
      obtain ⟨f, hf, hlim⟩ := hB (fun j => (u j : WO S T → ℂ)) (fun j => (u j).2) fun d ε hε => by
        rcases eq_or_ne ε ⊤ with rfl | hεt
        · exact ⟨0, fun i _ j _ => lt_top_iff_ne_top.2 (hsf d (u i - u j))⟩
        obtain ⟨J, hJ⟩ := hu d ε.toReal (ENNReal.toReal_pos hε.ne' hεt)
        refine ⟨J, fun i hi j hj => ?_⟩
        have := hJ i hi j hj
        rw [hp] at this
        exact (ENNReal.toReal_lt_toReal (hsf d (u i - u j)) hεt).1 this
      refine ⟨⟨f, hf⟩, fun d => ?_⟩
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hlim d)
      simpa [hp, Function.comp_def] using this)
    q (fun u x hux y hy => by
      have hy0 : 0 ≤ y := (apply_nonneg q (u 0)).trans (hy 0)
      have hconv : ∀ d, Tendsto (fun j => sobO ψ θ μ 𝓕 d ((u j : WO S T → ℂ) - x)) atTop (𝓝 0) := fun d => by
        have h1 := hux d
        simp only [hp] at h1
        rw [← ENNReal.toReal_zero] at h1
        exact (ENNReal.tendsto_toReal_iff (fun j => hsf d (u j - x)) ENNReal.zero_ne_top).1 h1
      have h2 := hlsc (fun j => (u j : WO S T → ℂ)) (fun j => (u j).2) x x.2 hconv
      have h3 : Filter.liminf (fun j => N (u j : WO S T → ℂ)) atTop ≤ ENNReal.ofReal y :=
        Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun j => by
          rw [← ENNReal.ofReal_toReal (hfin _ (u j).2)]
          exact ENNReal.ofReal_le_ofReal ((hq _).symm.trans_le (hy j) |>.trans_eq' rfl))
      rw [hq]
      exact ENNReal.toReal_le_of_le_ofReal hy0 (h2.trans h3))
  refine ⟨d, C, fun f hf => ?_⟩
  have h := hC ⟨f, hf⟩
  rw [hq, hp] at h
  calc N f = ENNReal.ofReal (N f).toReal := (ENNReal.ofReal_toReal (hfin f hf)).symm
    _ ≤ ENNReal.ofReal (C * (sobO ψ θ μ 𝓕 d f).toReal) := ENNReal.ofReal_le_ofReal h
    _ = C * sobO ψ θ μ 𝓕 d f := by
      rw [ENNReal.ofReal_mul (NNReal.coe_nonneg C), ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_toReal (GlobalTheory.Size.sobO_ne_top hψ hθ hm.1 hm.2.1 hf.1 d)]

end UpperTheory.Lit.Rallis.SobBaire
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

/- English proof (translation)
Apply the tactic sequence `first | exact @UpperTheory.Lit.Rallis.SobBaire.le_mul_sobO | exact UpperTheory.Lit.Rallis.SobBaire.le_mul_sobO | (intros; apply UpperTheory.Lit.Rallis.SobBaire.le_mul_sobO <;> assumption)`.
-/
theorem _root_.UpperTheory.Lit.Rallis.T.lsc_seminorm_thetaFunctionsLevel_le_sobolev : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ N : (WO S T → ℂ) → ℝ≥0∞, (∀ f ∈ thetaLevel ψ S T U, ∀ g ∈ thetaLevel ψ S T U, N (f + g) ≤ N f + N g) → (∀ (c : ℂ), ∀ f ∈ thetaLevel ψ S T U, N (c • f) = ‖c‖ₑ * N f) → (∀ f ∈ thetaLevel ψ S T U, N f ≠ ⊤) → (∀ (u : ℕ → WO S T → ℂ), (∀ j, u j ∈ thetaLevel ψ S T U) → ∀ f ∈ thetaLevel ψ S T U, (∀ d, Filter.Tendsto (fun j => sobO ψ θ μ 𝓕 d (u j - f)) Filter.atTop (nhds 0)) → N f ≤ Filter.liminf (fun j => N (u j)) Filter.atTop) → ∃ (d : ℕ) (C : ℝ≥0), ∀ f ∈ thetaLevel ψ S T U, N f ≤ C * sobO ψ θ μ 𝓕 d f := by
  first | exact @UpperTheory.Lit.Rallis.SobBaire.le_mul_sobO | exact UpperTheory.Lit.Rallis.SobBaire.le_mul_sobO | (intros; apply UpperTheory.Lit.Rallis.SobBaire.le_mul_sobO <;> assumption)
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace UpperTheory.Lit.Rallis.ThetaDens
open GlobalTheory

/- English proof (translation)
Establish `h1 : Filter.Tendsto (fun j => (C : ℝ≥0∞) * s j) Filter.atTop (nhds 0)`. Simplify using `using ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞)) hs (Or.inr ENNReal.coe_ne_top)`. Establish `h2 : Filter.Tendsto (fun j => edist (v j) a) Filter.atTop (nhds 0)` using `tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => zero_le) (fun j => by simpa [edist_eq_enorm_sub] using h j)`. Conclude with `(continuous_enorm.tendsto a).comp (tendsto_iff_edist_tendsto_0.2 h2)`.
-/
theorem tendsto_enorm_of_le {v : ℕ → ℂ} {a : ℂ} {s : ℕ → ℝ≥0∞} (C : ℝ≥0) (hs : Filter.Tendsto s Filter.atTop (nhds 0))
    (h : ∀ j, ‖v j - a‖ₑ ≤ C * s j) : Filter.Tendsto (fun j => ‖v j‖ₑ) Filter.atTop (nhds ‖a‖ₑ) := by
  have h1 : Filter.Tendsto (fun j => (C : ℝ≥0∞) * s j) Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞)) hs (Or.inr ENNReal.coe_ne_top)
  have h2 : Filter.Tendsto (fun j => edist (v j) a) Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => zero_le)
      (fun j => by simpa [edist_eq_enorm_sub] using h j)
  exact (continuous_enorm.tendsto a).comp (tendsto_iff_edist_tendsto_0.2 h2)

/- English proof (translation)
Introduce `D ψ S T χS χT om hom θ hθ μ 𝓕 hc m _ Z hadd hsm hZ hcomm hint U hU K hK`. Take `⟨U', hU', hl, hb⟩` from `UpperTheory.Lit.Rallis.T.exists_common_level_sobolev_bound_weil_compact D ψ S T χS χT om hom θ hθ μ 𝓕 hc (K ×ˢ {1}) (hK.prod isCompact_singleton) U hU`. Establish `pt : ∀ h : GA D T, ∃ (d : ℕ) (C : ℝ≥0), ∀ g ∈ thetaLevel ψ S T U', ‖thetaKO om 1 h (Z g)‖ₑ ≤ C * sobO ψ θ μ 𝓕 d g`. Introduce `h`. Take `⟨U₁, hU₁, hl₁, hb₁⟩` from `hZ U' hU'`.

Take `⟨U₂, hU₂, hl₂, hb₂⟩` from `UpperTheory.Lit.Rallis.T.exists_common_level_sobolev_bound_weil_compact D ψ S T χS χT om hom θ hθ μ 𝓕 hc {(1, h)} isCompact_singleton U₁ hU₁`. Take `⟨d₃, C₃, hb₃⟩` from `UpperTheory.Lit.Rallis.T.exists_sobolev_bound_theta_pointwise D ψ hom.std θ hθ S T μ 𝓕 hc U₂ hU₂`. Take `⟨d₂, C₂, hb₂⟩` from `hb₂ d₃`. Take `⟨d₁, C₁, hb₁⟩` from `hb₁ d₂`. Use `⟨d₁, C₃ * (C₂ * C₁), fun g hg => ?_⟩` and prove the remaining obligations.

Use `(hb₃ _ (hl₂ _ (hl₁ g hg) _ rfl) 0).trans ?_` and prove the remaining obligations. Rewrite using `[ENNReal.coe_mul, ENNReal.coe_mul, mul_assoc, mul_assoc]`. Use `gcongr`. Use `(hb₂ _ (hl₁ g hg) _ rfl).trans ?_` and prove the remaining obligations. Use `gcongr`.

Conclude with `hb₁ g hg`. Take `⟨d, C, hN⟩` from `UpperTheory.Lit.Rallis.T.lsc_seminorm_thetaFunctionsLevel_le_sobolev D ψ hom.std θ hθ S T μ 𝓕 hc U' hU' (fun f => ∫⁻ q, ‖descend (GQ T) (fun h => thetaKO om 1 h (Z f)) q‖ₑ ∂autMeasure T m) (fun f hf g hg => by`. Rewrite using `[← lintegral_add_left' (hint f hf.1).1.enorm]`. Use `lintegral_mono fun q => ?_` and prove the remaining obligations. Simplify using `only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO, hadd f g hf.1 hg.1, map_add, Pi.add_apply]`.

Conclude with `enorm_add_le _ _)`. Use the proof step `(fun c f hf => by`. Rewrite using `[← lintegral_const_mul' _ _ enorm_ne_top]`. Use `lintegral_congr fun q => ?_` and prove the remaining obligations. Simplify using `only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO, hsm c f hf.1, map_smul, Pi.smul_apply, enorm_smul])`.

Use the proof step `(fun f hf => (hint f hf.1).2.ne)`. Use the proof step `(fun u hu f hf ht => by`. Use `le_trans (lintegral_mono fun q => ?_) (lintegral_liminf_le' fun j => (hint _ (hu j).1).1.enorm)` and prove the remaining obligations. Take `⟨d, C, hp⟩` from `pt (Quotient.out q)`. Use `(tendsto_enorm_of_le C (ht d) fun j => ?_).liminf_eq.ge` and prove the remaining obligations.

Use `le_of_eq_of_le ?_ (hp _ (sub_mem (hu j) hf))` and prove the remaining obligations. Establish `e : u j - f = u j + (-1 : ℂ) • f` using `by rw [neg_one_smul, sub_eq_add_neg]`. Establish `hf' : (-1 : ℂ) • f ∈ thetaLevel ψ S T U'` using `Submodule.smul_mem _ _ hf`. Rewrite using `[e, hadd _ _ (hu j).1 hf'.1, hsm _ _ hf.1]`. Simplify using `only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO, map_add, Pi.add_apply, neg_one_smul, sub_eq_add_neg, map_neg, Pi.neg_apply])`.

Take `⟨d', C', hb⟩` from `hb d`. Use `⟨d', C * C', fun f hf x hx => ?_⟩` and prove the remaining obligations. Establish `hx' : ((x, 1) : GA D S × GA D T) ∈ K ×ˢ {1}` using `⟨hx, rfl⟩`. Use `le_of_eq_of_le ?_ ((hN _ (hl f hf _ hx')).trans ?_)` and prove the remaining obligations. Use `lintegral_congr fun q => ?_` and prove the remaining obligations.

Simplify using `only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO]`. Rewrite using `[← hcomm f hf.1 x, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]`. Rewrite using `[ENNReal.coe_mul, mul_assoc] gcongr`. Conclude with `hb f hf _ hx'`.
-/
theorem sobBdd_absThetaInt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ m : Measure (GA D T), m.IsHaarMeasure → ∀ Z : (WO S T → ℂ) → WO S T → ℂ, (∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → Z (f + f') = Z f + Z f') → (∀ (c : ℂ) f, IsThetaFunO ψ S T f → Z (c • f) = c • Z f) → Sobolev₂ ψ θ μ 𝓕 μ 𝓕 Z → (∀ f, IsThetaFunO ψ S T f → ∀ x, om (x, 1) (Z f) = Z (om (x, 1) f)) → (∀ f, IsThetaFunO ψ S T f → Integrable (descend (GQ T) fun h => thetaKO om 1 h (Z f)) (autMeasure T m)) → SobBdd ψ θ μ 𝓕 fun f x => ∫⁻ q, ‖descend (GQ T) (fun h => thetaKO om x h (Z f)) q‖ₑ ∂autMeasure T m := by
  intro D ψ S T χS χT om hom θ hθ μ 𝓕 hc m _ Z hadd hsm hZ hcomm hint U hU K hK
  obtain ⟨U', hU', hl, hb⟩ := UpperTheory.Lit.Rallis.T.exists_common_level_sobolev_bound_weil_compact D ψ S T χS χT om hom θ hθ μ 𝓕 hc (K ×ˢ {1})
    (hK.prod isCompact_singleton) U hU
  have pt : ∀ h : GA D T, ∃ (d : ℕ) (C : ℝ≥0), ∀ g ∈ thetaLevel ψ S T U',
      ‖thetaKO om 1 h (Z g)‖ₑ ≤ C * sobO ψ θ μ 𝓕 d g := by
    intro h
    obtain ⟨U₁, hU₁, hl₁, hb₁⟩ := hZ U' hU'
    obtain ⟨U₂, hU₂, hl₂, hb₂⟩ := UpperTheory.Lit.Rallis.T.exists_common_level_sobolev_bound_weil_compact D ψ S T χS χT om hom θ hθ μ 𝓕 hc {(1, h)}
      isCompact_singleton U₁ hU₁
    obtain ⟨d₃, C₃, hb₃⟩ := UpperTheory.Lit.Rallis.T.exists_sobolev_bound_theta_pointwise D ψ hom.std θ hθ S T μ 𝓕 hc U₂ hU₂
    obtain ⟨d₂, C₂, hb₂⟩ := hb₂ d₃
    obtain ⟨d₁, C₁, hb₁⟩ := hb₁ d₂
    refine ⟨d₁, C₃ * (C₂ * C₁), fun g hg => ?_⟩
    refine (hb₃ _ (hl₂ _ (hl₁ g hg) _ rfl) 0).trans ?_
    rw [ENNReal.coe_mul, ENNReal.coe_mul, mul_assoc, mul_assoc]
    gcongr
    refine (hb₂ _ (hl₁ g hg) _ rfl).trans ?_
    gcongr
    exact hb₁ g hg
  obtain ⟨d, C, hN⟩ := UpperTheory.Lit.Rallis.T.lsc_seminorm_thetaFunctionsLevel_le_sobolev D ψ hom.std θ hθ S T μ 𝓕 hc U' hU'
    (fun f => ∫⁻ q, ‖descend (GQ T) (fun h => thetaKO om 1 h (Z f)) q‖ₑ ∂autMeasure T m)
    (fun f hf g hg => by
      rw [← lintegral_add_left' (hint f hf.1).1.enorm]
      refine lintegral_mono fun q => ?_
      simp only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO, hadd f g hf.1 hg.1, map_add, Pi.add_apply]
      exact enorm_add_le _ _)
    (fun c f hf => by
      rw [← lintegral_const_mul' _ _ enorm_ne_top]
      refine lintegral_congr fun q => ?_
      simp only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO, hsm c f hf.1, map_smul, Pi.smul_apply, enorm_smul])
    (fun f hf => (hint f hf.1).2.ne)
    (fun u hu f hf ht => by
      refine le_trans (lintegral_mono fun q => ?_) (lintegral_liminf_le' fun j => (hint _ (hu j).1).1.enorm)
      obtain ⟨d, C, hp⟩ := pt (Quotient.out q)
      refine (tendsto_enorm_of_le C (ht d) fun j => ?_).liminf_eq.ge
      refine le_of_eq_of_le ?_ (hp _ (sub_mem (hu j) hf))
      have e : u j - f = u j + (-1 : ℂ) • f := by rw [neg_one_smul, sub_eq_add_neg]
      have hf' : (-1 : ℂ) • f ∈ thetaLevel ψ S T U' := Submodule.smul_mem _ _ hf
      rw [e, hadd _ _ (hu j).1 hf'.1, hsm _ _ hf.1]
      simp only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO, map_add, Pi.add_apply, neg_one_smul,
        sub_eq_add_neg, map_neg, Pi.neg_apply])
  obtain ⟨d', C', hb⟩ := hb d
  refine ⟨d', C * C', fun f hf x hx => ?_⟩
  have hx' : ((x, 1) : GA D S × GA D T) ∈ K ×ˢ {1} := ⟨hx, rfl⟩
  refine le_of_eq_of_le ?_ ((hN _ (hl f hf _ hx')).trans ?_)
  · refine lintegral_congr fun q => ?_
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO]
    rw [← hcomm f hf.1 x, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]
  · rw [ENNReal.coe_mul, mul_assoc]
    gcongr
    exact hb f hf _ hx'

end UpperTheory.Lit.Rallis.ThetaDens
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

/- English proof (translation)
Apply the tactic sequence `first | exact @UpperTheory.Lit.Rallis.ThetaDens.sobBdd_absThetaInt | exact UpperTheory.Lit.Rallis.ThetaDens.sobBdd_absThetaInt | (intros; apply UpperTheory.Lit.Rallis.ThetaDens.sobBdd_absThetaInt <;> assumption)`.
-/
theorem _root_.UpperTheory.Lit.Rallis.T.absThetaIntegral_le_sobolevSeminorm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ m : Measure (GA D T), m.IsHaarMeasure → ∀ Z : (WO S T → ℂ) → WO S T → ℂ, (∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → Z (f + f') = Z f + Z f') → (∀ (c : ℂ) f, IsThetaFunO ψ S T f → Z (c • f) = c • Z f) → Sobolev₂ ψ θ μ 𝓕 μ 𝓕 Z → (∀ f, IsThetaFunO ψ S T f → ∀ x, om (x, 1) (Z f) = Z (om (x, 1) f)) → (∀ f, IsThetaFunO ψ S T f → Integrable (descend (GQ T) fun h => thetaKO om 1 h (Z f)) (autMeasure T m)) → SobBdd ψ θ μ 𝓕 fun f x => ∫⁻ q, ‖descend (GQ T) (fun h => thetaKO om x h (Z f)) q‖ₑ ∂autMeasure T m := by
  first | exact @UpperTheory.Lit.Rallis.ThetaDens.sobBdd_absThetaInt | exact UpperTheory.Lit.Rallis.ThetaDens.sobBdd_absThetaInt | (intros; apply UpperTheory.Lit.Rallis.ThetaDens.sobBdd_absThetaInt <;> assumption)
end
