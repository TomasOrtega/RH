import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls
open CategoryTheory.Limits
open GlobalTheory.Twist (resM app_resM)

set_option autoImplicit false

namespace GlobalTheory.FlagCls

/- English proof (translation)
Proceed by induction on `k using Fin.induction with`. Consider the case `zero`. Take `⟨W, e, -, hpW, hWU, he⟩` from `(fl.isVB 0).exists_affine hp`. Use `⟨W, fun _ => 0, hWU, hpW, fun j hj => ?_⟩` and prove the remaining obligations. Take `rfl : j = 0` from `Fin.le_zero_iff.1 hj`.

Conclude with `⟨e, he, fun i => i.elim0⟩`. Consider the case `succ k ih`. Take `⟨W, s, hWU, hpW, H⟩` from `ih`. Take `⟨V, c, -, hpV, hVW, hc⟩` from `(fl.isVB_gr k).exists_affine hpW`. Take `⟨T, hTV, hpT, u, hu⟩` from `VBExt.exists_lifts (fl.π k) c hpV`.

Establish `hTW : T ≤ W` using `hTV.trans hVW`. Use `⟨T, fun n => if n = k then (fl.ι k.succ).app T (u 0) else resM N hTW (s n), hTW.trans hWU, hpT, fun j hj => ?_⟩` and prove the remaining obligations. Break down `hj.lt_or_eq with hj | rfl` into its components or cases. Establish `hj' : j ≤ k.castSucc` using `Fin.le_castSucc_iff.2 hj`. Take `⟨t, ht, e⟩` from `H j hj'`.

Use `⟨_, ht.res hTW, fun i => ?_⟩` and prove the remaining obligations. Establish `: (i : ℕ) ≠ k`. Establish `h1` using `i.2`. Establish `h2 : (j : ℕ) ≤ k` using `hj'`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [if_neg this]`. Rewrite using `[app_resM, e]`. Take `⟨t, ht, e⟩` from `H k.castSucc le_rfl`. Establish `hS : (ShortComplex.mk (fl.step k) (cokernel.π (fl.step k)) (cokernel.condition _)).ShortExact` using `{ exact := ShortComplex.exact_cokernel _ }`. Establish `hu' : IsFrame fun i => (fl.π k).app T (u i)`.

Rewrite using `[funext hu]`. Conclude with `hc.res hTV`. Establish `hf` using `(VBExt.isFrame_sumElim hS (ht.res hTW) hu').comp_equiv (finSumFinEquiv (m := k) (n := 1)).symm`. Use `⟨_, hf, fun i : Fin (k + 1) => ?_⟩` and prove the remaining obligations. Proceed by induction on `i using Fin.addCases with`.

Consider the case `left i`. Establish `: ((Fin.castAdd 1 i : Fin (k + 1)) : ℕ) ≠ k` using `i.2.ne`. Simplify using `only [if_neg this, Function.comp_apply, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]`. Use `(QCoh.app_app _ _ _ _).trans ?_` and prove the remaining obligations. Rewrite using `[fl.step_ι, app_resM]`.

Conclude with `congrArg _ (e i)`. Consider the case `right i`. Take `rfl : i = 0` from `Subsingleton.elim _ _`. Establish `: ((Fin.natAdd k (0 : Fin 1) : Fin (k + 1)) : ℕ) = k` using `rfl`. Simplify using `only [if_pos this, Function.comp_apply, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]`.
-/
theorem exists_adapted_upTo {Y : Scheme.{0}} {N : Y.Modules} {r : ℕ} (fl : Vert.Flag N r) {p : Y} {U : Y.Opens}
    (hp : p ∈ U) (k : Fin (r + 1)) :
    ∃ (W : Y.Opens) (s : ℕ → Γ(N, W)), W ≤ U ∧ p ∈ W ∧ ∀ j : Fin (r + 1), j ≤ k →
      ∃ t : Fin j → Γ(fl.F j, W), IsFrame t ∧ ∀ i : Fin j, (fl.ι j).app W (t i) = s i := by
  induction k using Fin.induction with
  | zero =>
    obtain ⟨W, e, -, hpW, hWU, he⟩ := (fl.isVB 0).exists_affine hp
    refine ⟨W, fun _ => 0, hWU, hpW, fun j hj => ?_⟩
    obtain rfl : j = 0 := Fin.le_zero_iff.1 hj
    exact ⟨e, he, fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨W, s, hWU, hpW, H⟩ := ih
    obtain ⟨V, c, -, hpV, hVW, hc⟩ := (fl.isVB_gr k).exists_affine hpW
    obtain ⟨T, hTV, hpT, u, hu⟩ := VBExt.exists_lifts (fl.π k) c hpV
    have hTW : T ≤ W := hTV.trans hVW
    refine ⟨T, fun n => if n = k then (fl.ι k.succ).app T (u 0) else resM N hTW (s n),
      hTW.trans hWU, hpT, fun j hj => ?_⟩
    rcases hj.lt_or_eq with hj | rfl
    · have hj' : j ≤ k.castSucc := Fin.le_castSucc_iff.2 hj
      obtain ⟨t, ht, e⟩ := H j hj'
      refine ⟨_, ht.res hTW, fun i => ?_⟩
      have : (i : ℕ) ≠ k := by
        have h1 := i.2
        have h2 : (j : ℕ) ≤ k := hj'
        omega
      simp only [if_neg this]
      rw [app_resM, e]
    · obtain ⟨t, ht, e⟩ := H k.castSucc le_rfl
      have hS : (ShortComplex.mk (fl.step k) (cokernel.π (fl.step k)) (cokernel.condition _)).ShortExact :=
        { exact := ShortComplex.exact_cokernel _ }
      have hu' : IsFrame fun i => (fl.π k).app T (u i) := by
        rw [funext hu]; exact hc.res hTV
      have hf := (VBExt.isFrame_sumElim hS (ht.res hTW) hu').comp_equiv
        (finSumFinEquiv (m := k) (n := 1)).symm
      refine ⟨_, hf, fun i : Fin (k + 1) => ?_⟩
      induction i using Fin.addCases with
      | left i =>
        have : ((Fin.castAdd 1 i : Fin (k + 1)) : ℕ) ≠ k := i.2.ne
        simp only [if_neg this, Function.comp_apply, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
        refine (QCoh.app_app _ _ _ _).trans ?_
        rw [fl.step_ι, app_resM]
        exact congrArg _ (e i)
      | right i =>
        obtain rfl : i = 0 := Subsingleton.elim _ _
        have : ((Fin.natAdd k (0 : Fin 1) : Fin (k + 1)) : ℕ) = k := rfl
        simp only [if_pos this, Function.comp_apply, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]

/- English proof (translation)
Introduce `Y N r fl p U hp`. Take `⟨W, s, hWU, hpW, H⟩` from `exists_adapted_upTo fl hp (Fin.last r)`. Use `⟨W, fun i => s i, hWU, hpW, ?_, fun k => H k (Fin.le_last k)⟩` and prove the remaining obligations. Take `⟨t, ht, e⟩` from `H (Fin.last r) le_rfl`. Use `ht.map_iso (fl.ι (Fin.last r))` as an intermediate fact.

Rewrite `this` using `[funext e]`. Conclude with `this`.
-/
theorem exists_adapted : ∀ (Y : Scheme.{0}) (N : Y.Modules) (r : ℕ) (fl : Vert.Flag N r) (p : Y) (U : Y.Opens),
    p ∈ U → ∃ (W : Y.Opens) (s : Fin r → Γ(N, W)), W ≤ U ∧ p ∈ W ∧ Adapted fl s := by
  intro Y N r fl p U hp
  obtain ⟨W, s, hWU, hpW, H⟩ := exists_adapted_upTo fl hp (Fin.last r)
  refine ⟨W, fun i => s i, hWU, hpW, ?_, fun k => H k (Fin.le_last k)⟩
  obtain ⟨t, ht, e⟩ := H (Fin.last r) le_rfl
  have := ht.map_iso (fl.ι (Fin.last r))
  rw [funext e] at this
  exact this

end GlobalTheory.FlagCls
