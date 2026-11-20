import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.FormalDegreeBessel.FinalG

noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped ENNReal

namespace GlobalTheory.Amp.RootMove

variable {k r : ℕ}

open MeasureTheory Matrix in
open scoped ENNReal in
variable {k r : ℕ} in
/- English proof (translation)
Use `isUnit_iff_exists_inv.2 ⟨(_root_.Formalism.QuantumDeterminants.Hpk k r).det, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.det_mul, _root_.Formalism.QuantumDeterminants.GBasic.Hpk_sq, Matrix.det_one]`.
-/
theorem _root_.GlobalTheory.Amp.RootMove.det_Hpk : IsUnit (_root_.Formalism.QuantumDeterminants.Hpk k r).det := by
  refine isUnit_iff_exists_inv.2 ⟨(_root_.Formalism.QuantumDeterminants.Hpk k r).det, ?_⟩
  rw [← Matrix.det_mul, _root_.Formalism.QuantumDeterminants.GBasic.Hpk_sq, Matrix.det_one]

open MeasureTheory Matrix in
open scoped ENNReal in
variable {k r : ℕ} in
/- English proof (translation)
The claim follows from `_root_.Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg`.
-/
theorem _root_.GlobalTheory.Amp.RootMove.unit_det {g : _root_.Formalism.MainNotions.S.MatKR k r} (hg : g ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r)) :
    IsUnit g.det := _root_.Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg

def lr (a b : MatKR k r) : Mt k r → Mt k r := fun x => fun i j => (a * Matrix.of x * b) i j

open MeasureTheory Matrix in
open scoped ENNReal in
variable {k r : ℕ} in
/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Simplify using `only [_root_.GlobalTheory.Amp.RootMove.lr, Matrix.mul_apply, Matrix.of_apply]`. Use `fun_prop`.
-/
theorem _root_.GlobalTheory.Amp.RootMove.continuous_lr (a b : _root_.Formalism.MainNotions.S.MatKR k r) :
    Continuous (_root_.GlobalTheory.Amp.RootMove.lr a b) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [_root_.GlobalTheory.Amp.RootMove.lr, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

open MeasureTheory Matrix in
open scoped ENNReal in
variable {k r : ℕ} in
/- English proof (translation)
Establish `hent : ∀ i j, Continuous fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => g i j` using `fun i j => (continuous_apply j).comp (continuous_apply i)`. Establish `e : _root_.Formalism.QuantumDeterminants.Nset k r = {g | gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * g = _root_.Formalism.QuantumDeterminants.Hpk k r} ∩ ((⋂ (a : Fin r) (i : Fin (2 * r + k + 1)) (_ : (a : ℕ) ≤ i), {g | g i (_root_.Formalism.QuantumDeterminants.eI k r a) = …`. Use extensionality with `g`. Simplify using `only [_root_.Formalism.QuantumDeterminants.Nset, _root_.Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]`. Rewrite using `[e]`.

Use `IsClosed.inter (isClosed_eq ?_ continuous_const) (IsClosed.inter ?_ ?_)` and prove the remaining obligations. Conclude with `(continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id`. Conclude with `isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_eq (hent _ _) continuous_const`. Conclude with `isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_eq (hent _ _) continuous_const`.
-/
private theorem isClosed_Nset' : IsClosed (_root_.Formalism.QuantumDeterminants.Nset k r) := by
  have hent : ∀ i j, Continuous fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => g i j :=
    fun i j => (continuous_apply j).comp (continuous_apply i)
  have e : _root_.Formalism.QuantumDeterminants.Nset k r = {g | gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * g = _root_.Formalism.QuantumDeterminants.Hpk k r} ∩
      ((⋂ (a : Fin r) (i : Fin (2 * r + k + 1)) (_ : (a : ℕ) ≤ i),
        {g | g i (_root_.Formalism.QuantumDeterminants.eI k r a) = if i = _root_.Formalism.QuantumDeterminants.eI k r a then 1 else 0}) ∩
      ⋂ (i : Fin (2 * r + k + 1)) (j : Fin (2 * r + k + 1)) (_ : r ≤ (j : ℕ)) (_ : (j : ℕ) ≤ r + k)
        (_ : r ≤ (i : ℕ)), {g | g i j = if i = j then 1 else 0}) := by
    ext g
    simp only [_root_.Formalism.QuantumDeterminants.Nset, _root_.Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  refine IsClosed.inter (isClosed_eq ?_ continuous_const) (IsClosed.inter ?_ ?_)
  · exact (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
  · exact isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_eq (hent _ _) continuous_const
  · exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_eq (hent _ _) continuous_const

open MeasureTheory Matrix in
open scoped ENNReal in
variable {k r : ℕ} in
/- English proof (translation)
Establish `h1 : Continuous fun x : _root_.Formalism.QuantumDeterminants.Mt k r => (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)` using `continuous_id`. Establish `h2 : Continuous fun x : _root_.Formalism.QuantumDeterminants.Mt k r => (g * Matrix.of x * g⁻¹ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)` using `(continuous_const.matrix_mul h1).matrix_mul continuous_const`. Establish `hc : IsClosed {x : _root_.Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ _root_.Formalism.MainNotions.S.Rset k r g}` using `(isClosed_Nset'.preimage h1).inter (isClosed_Nset'.preimage h2)`. Conclude with `hc.measurableSet.compl`.
-/
theorem _root_.GlobalTheory.Amp.RootMove.measurableSet_notR (g : _root_.Formalism.MainNotions.S.MatKR k r) :
    MeasurableSet {x : _root_.Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ _root_.Formalism.MainNotions.S.Rset k r g} := by
  have h1 : Continuous fun x : _root_.Formalism.QuantumDeterminants.Mt k r =>
      (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := continuous_id
  have h2 : Continuous fun x : _root_.Formalism.QuantumDeterminants.Mt k r =>
      (g * Matrix.of x * g⁻¹ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
    (continuous_const.matrix_mul h1).matrix_mul continuous_const
  have hc : IsClosed {x : _root_.Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ _root_.Formalism.MainNotions.S.Rset k r g} :=
    (isClosed_Nset'.preimage h1).inter (isClosed_Nset'.preimage h2)
  exact hc.measurableSet.compl

open MeasureTheory Matrix in
open scoped ENNReal in
variable {k r : ℕ} in
/- English proof (translation)
Use `measurable_pi_lambda _ fun q => Continuous.measurable ?_` and prove the remaining obligations. Distinguish the cases in `hi : ((q : Fin (r + 1) × Fin (r + 1)).1 : ℕ) < r`. Simplify using `only [_root_.Formalism.MainNotions.S.rootCoords, _root_.Formalism.MainNotions.S.flagMat, hi, dite_true, Matrix.mulVec, dotProduct, Matrix.of_apply] fun_prop`. Simplify using `only [_root_.Formalism.MainNotions.S.rootCoords, _root_.Formalism.MainNotions.S.flagMat, hi, dite_false]`. Conclude with `continuous_const`.
-/
theorem _root_.GlobalTheory.Amp.RootMove.measurable_rootCoords (z : Fin (2 * r + k + 1) → ℂ) (p : _root_.Formalism.MainNotions.S.Point ℂ (r + 1)) :
    Measurable (_root_.Formalism.MainNotions.S.rootCoords k r z p) := by
  refine measurable_pi_lambda _ fun q => Continuous.measurable ?_
  by_cases hi : ((q : Fin (r + 1) × Fin (r + 1)).1 : ℕ) < r
  · simp only [_root_.Formalism.MainNotions.S.rootCoords, _root_.Formalism.MainNotions.S.flagMat, hi, dite_true, Matrix.mulVec, dotProduct, Matrix.of_apply]
    fun_prop
  · simp only [_root_.Formalism.MainNotions.S.rootCoords, _root_.Formalism.MainNotions.S.flagMat, hi, dite_false]
    exact continuous_const

open MeasureTheory Matrix in
open scoped ENNReal in
variable {k r : ℕ} in
/- English proof (translation)
Establish `hfix : ∀ {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}, g ∈ _root_.Formalism.QuantumDeterminants.UWset k r z → ∀ c, g *ᵥ _root_.Formalism.QuantumDeterminants.fvec k r z c = _root_.Formalism.QuantumDeterminants.fvec k r z c`. Introduce `g hg c`. Take `⟨-, hb, hz⟩` from `hg`. Unfold `_root_.Formalism.QuantumDeterminants.fvec`. Use `split_ifs with hc`.

Conclude with `(hb _).1`. Conclude with `hz`. Take `⟨hU, hb, -⟩` from `id hh`. Establish `hrow : ∀ (a : Fin r) (j : Fin (2 * r + k + 1)), h (_root_.Formalism.QuantumDeterminants.eI k r a) j = if _root_.Formalism.QuantumDeterminants.eI k r a = j then 1 else 0`. Introduce `a j`.

Establish `hτ : _root_.Formalism.QuantumDeterminants.WeylGroupFacts.tau k r (_root_.Formalism.QuantumDeterminants.esI k r a) = _root_.Formalism.QuantumDeterminants.eI k r a`. Use `a.isLt` as an intermediate fact. Use `ext`. Simplify using `only [_root_.Formalism.QuantumDeterminants.WeylGroupFacts.tau, _root_.Formalism.QuantumDeterminants.esI, _root_.Formalism.QuantumDeterminants.eI]`. Distinguish the cases in `hc : 2 * r + k - (a : ℕ) < r ∨ r + k < 2 * r + k - (a : ℕ)`.

Simplify using `only [hc, ↓reduceIte]`. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Rewrite using `[← hτ]`. Conclude with `_root_.Formalism.QuantumDeterminants.WeylGroupFacts.row_of_fixed_col hU _ (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.col_of_fix (hb a).2) j`.

Use extensionality with `i j`. Simplify using `only [_root_.Formalism.MainNotions.S.flagMat, Matrix.of_apply]`. Use `split_ifs with hi`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfix (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh), _root_.Formalism.QuantumDeterminants.WeylGroupFacts.mulVec_apply_of_row _ _ (hrow _)]`. Apply the tactic sequence `all_goals rfl`.
-/
private theorem flagMat_conj_eq_of_mem_UWset {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ _root_.Formalism.QuantumDeterminants.UWset k r z)
    (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    _root_.Formalism.MainNotions.S.flagMat k r z (h * X * h⁻¹) = _root_.Formalism.MainNotions.S.flagMat k r z X := by
  have hfix : ∀ {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}, g ∈ _root_.Formalism.QuantumDeterminants.UWset k r z →
      ∀ c, g *ᵥ _root_.Formalism.QuantumDeterminants.fvec k r z c = _root_.Formalism.QuantumDeterminants.fvec k r z c := by
    intro g hg c
    obtain ⟨-, hb, hz⟩ := hg
    unfold _root_.Formalism.QuantumDeterminants.fvec
    split_ifs with hc
    · exact (hb _).1
    · exact hz
  obtain ⟨hU, hb, -⟩ := id hh
  have hrow : ∀ (a : Fin r) (j : Fin (2 * r + k + 1)),
      h (_root_.Formalism.QuantumDeterminants.eI k r a) j = if _root_.Formalism.QuantumDeterminants.eI k r a = j then 1 else 0 := by
    intro a j
    have hτ : _root_.Formalism.QuantumDeterminants.WeylGroupFacts.tau k r (_root_.Formalism.QuantumDeterminants.esI k r a) = _root_.Formalism.QuantumDeterminants.eI k r a := by
      have := a.isLt
      ext
      simp only [_root_.Formalism.QuantumDeterminants.WeylGroupFacts.tau, _root_.Formalism.QuantumDeterminants.esI, _root_.Formalism.QuantumDeterminants.eI]
      by_cases hc : 2 * r + k - (a : ℕ) < r ∨ r + k < 2 * r + k - (a : ℕ)
      · simp only [hc, ↓reduceIte]; omega
      · omega
    rw [← hτ]
    exact _root_.Formalism.QuantumDeterminants.WeylGroupFacts.row_of_fixed_col hU _ (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.col_of_fix (hb a).2) j
  ext i j
  simp only [_root_.Formalism.MainNotions.S.flagMat, Matrix.of_apply]
  split_ifs with hi
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfix (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh), _root_.Formalism.QuantumDeterminants.WeylGroupFacts.mulVec_apply_of_row _ _ (hrow _)]
  all_goals rfl

open MeasureTheory Matrix in
open scoped ENNReal in
variable {k r : ℕ} in

/- English proof (translation)
Introduce `D z z' p g a a' μ hz hz' _ _ _ ha ha' hμ`. Take `⟨h, hh, m, hm, rfl⟩` from `ha`. Take `⟨h', hh', m', hm', rfl⟩` from `ha'`. Take `⟨n, hn, n', hn', g₀, rfl, hZ, μ₀, hnull, hmap, rfl⟩` from `hμ`. Establish `hd : IsUnit h.det` using `_root_.Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh.1`.

Establish `hd' : IsUnit h'.det` using `_root_.Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh'.1`. Establish `hdm' : IsUnit m'.det` using `_root_.Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh ((_root_.Formalism.QuantumDeterminants.WeylGroupFacts.nset_iff m').1 hm').1`. Establish `hc' : Continuous (_root_.GlobalTheory.Amp.RootMove.lr h' h'⁻¹)` using `_root_.GlobalTheory.Amp.RootMove.continuous_lr h' h'⁻¹`. Use `⟨h * (m * n) * h⁻¹, (_root_.Formalism.QuantumDeterminants.uWNormal _ _ z hz h hh _ (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_mul hm hn)).1, h' * (n' * m'⁻¹) * h'⁻¹, (_root_.Formalism.QuantumDeterminants.uWNormal _ _ z' hz' h' hh' _ (_root_.Formalism.QuantumDeterm …` and prove the remaining obligations. Rewrite using `[Matrix.mul_inv_rev]`.

Simplify using `only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd, Matrix.nonsing_inv_mul_cancel_left _ _ hd']`. Establish `hF : h⁻¹ * _root_.Formalism.QuantumDeterminants.Fm _ _ z = _root_.Formalism.QuantumDeterminants.Fm _ _ z` using `_root_.Formalism.QuantumDeterminants.UW_F (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh)`. Establish `hF' : h'⁻¹ * _root_.Formalism.QuantumDeterminants.Fm _ _ z' = _root_.Formalism.QuantumDeterminants.Fm _ _ z'` using `_root_.Formalism.QuantumDeterminants.UW_F (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh')`. Establish `hU : (h⁻¹)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * h⁻¹ = _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS` using `_root_.Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hh.1`. Establish `hU2 : (h⁻¹)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS = _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * h` using `by conv_rhs => rw [← hU]`.

Rewrite using `[Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]`. Establish `key : (_root_.Formalism.QuantumDeterminants.Fm _ _ z)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * h = (_root_.Formalism.QuantumDeterminants.Fm _ _ z)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS`. Rewrite using `[Matrix.mul_assoc, ← hU2, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hF]`. Establish `E : (_root_.Formalism.QuantumDeterminants.Fm _ _ z)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (h * g₀ * h'⁻¹) * _root_.Formalism.QuantumDeterminants.Fm _ _ z' = (_root_.Formalism.QuantumDeterminants.Fm _ _ z)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R. …`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [key, hF']`. Rewrite using `[← hZ]`. Unfold `_root_.Formalism.MainNotions.S.ZhatO`. Rewrite using `[_root_.Formalism.QuantumDeterminants.Zhat_eq, _root_.Formalism.QuantumDeterminants.Zhat_eq, E]`.

Rewrite using `[Measure.map_apply hc'.measurable (_root_.GlobalTheory.Amp.RootMove.measurableSet_notR _)]`. Use `measure_mono_null ?_ hnull` and prove the remaining obligations. Introduce `x hx`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq] at hx ⊢`. Introduce `hR`.

Apply `hx` to reduce the goal to its premises. Take `⟨hR1, hR2⟩` from `hR`. Establish `e : (h * g₀ * h'⁻¹) * (h' * Matrix.of x * h'⁻¹) * (h * g₀ * h'⁻¹)⁻¹ = h * (g₀ * Matrix.of x * g₀⁻¹) * h⁻¹`. Simplify using `only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hd', Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd']`. Use `⟨(_root_.Formalism.QuantumDeterminants.uWNormal _ _ z' hz' h' hh' _ hR1).1, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(h * g₀ * h'⁻¹) * (h' * Matrix.of x * h'⁻¹) * (h * g₀ * h'⁻¹)⁻¹ ∈ _`. Rewrite using `[e]`. Conclude with `(_root_.Formalism.QuantumDeterminants.uWNormal _ _ z hz h hh _ hR2).1`. Rewrite using `[Measure.map_map (_root_.GlobalTheory.Amp.RootMove.measurable_rootCoords z' p) hc'.measurable]`. Use `hmap using 2` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `x`. Establish `hx` using `flagMat_conj_eq_of_mem_UWset hh' (Matrix.of x)`. Simplify using `only [Function.comp_apply]`. Unfold `_root_.Formalism.MainNotions.S.rootCoords`. Conclude with `congrArg (fun M => fun q : ↥(_root_.Formalism.MainNotions.S.rootPat p) => M q.1.1 q.1.2) hx`.

Establish `E : ∀ X : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ, (h' * m') * (n'⁻¹ * X * n') * (h' * m')⁻¹ = (h' * (n' * m'⁻¹) * h'⁻¹)⁻¹ * (h' * X * h'⁻¹) * (h' * (n' * m'⁻¹) * h'⁻¹)`. Introduce `X`. Simplify using `only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hd', Matrix.nonsing_inv_nonsing_inv _ hdm', Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd']`. Rewrite using `[Measure.map_map, Measure.map_map]`. Use `congr 1`.

Use function extensionality and compare the values at `x i j`. Conclude with `congrArg (fun M : Matrix _ _ ℂ => M i j) (E (Matrix.of x))`. Apply the tactic sequence `all_goals exact (_root_.GlobalTheory.Amp.RootMove.continuous_lr _ _).measurable`.
-/
theorem _root_.GlobalTheory.Amp.RootMove.rootMeas_move : ∀ (D : _root_.Formalism.BasicNotions.D7) (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (p : _root_.Formalism.MainNotions.S.Point ℂ (D.R.rS + 1)) (g a a' : _root_.Formalism.MainNotions.S.MatKR D.R.k D.R.rS) (μ : Measure (_root_.Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)), _root_.Formalism.QuantumDeterminants.inWb D.R.k D.R.rS z → _root_.Formalism.QuantumDeterminants.inWb D.R.k D.R.rS z' → 0 < _root_.Formalism.QuantumDeterminants.Tz D.R.k D.R.rS z → 0 < _root_.Formalism.QuantumDeterminants.Tz D.R.k D.R.rS z' → g ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) → a ∈ _root_.Formalism.QuantumDeterminants.Sset D.R.k D.R.rS z → a' ∈ _root_.Formalism.QuantumDeterminants.Sset D.R.k D.R.rS z' → _root_.Formalism.MainNotions.S.IsRootMeasR D z z' p g μ → _root_.Formalism.MainNotions.S.IsRootMeasR D z z' p (a * g * a'⁻¹) (μ.map fun x => fun i j => (a' * Matrix.of x * a'⁻¹) i j) := by
  intro D z z' p g a a' μ hz hz' _ _ _ ha ha' hμ
  obtain ⟨h, hh, m, hm, rfl⟩ := ha
  obtain ⟨h', hh', m', hm', rfl⟩ := ha'
  obtain ⟨n, hn, n', hn', g₀, rfl, hZ, μ₀, hnull, hmap, rfl⟩ := hμ
  have hd : IsUnit h.det := _root_.Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh.1
  have hd' : IsUnit h'.det := _root_.Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh'.1
  have hdm' : IsUnit m'.det := _root_.Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh ((_root_.Formalism.QuantumDeterminants.WeylGroupFacts.nset_iff m').1 hm').1
  have hc' : Continuous (_root_.GlobalTheory.Amp.RootMove.lr h' h'⁻¹) :=
    _root_.GlobalTheory.Amp.RootMove.continuous_lr h' h'⁻¹
  refine ⟨h * (m * n) * h⁻¹, (_root_.Formalism.QuantumDeterminants.uWNormal _ _ z hz h hh _ (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_mul hm hn)).1,
    h' * (n' * m'⁻¹) * h'⁻¹, (_root_.Formalism.QuantumDeterminants.uWNormal _ _ z' hz' h' hh' _ (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_mul hn' (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hm'))).1,
    h * g₀ * h'⁻¹, ?_, ?_, μ₀.map (_root_.GlobalTheory.Amp.RootMove.lr h' h'⁻¹), ?_, ?_, ?_⟩
  · rw [Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd,
      Matrix.nonsing_inv_mul_cancel_left _ _ hd']
  · have hF : h⁻¹ * _root_.Formalism.QuantumDeterminants.Fm _ _ z = _root_.Formalism.QuantumDeterminants.Fm _ _ z := _root_.Formalism.QuantumDeterminants.UW_F (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh)
    have hF' : h'⁻¹ * _root_.Formalism.QuantumDeterminants.Fm _ _ z' = _root_.Formalism.QuantumDeterminants.Fm _ _ z' := _root_.Formalism.QuantumDeterminants.UW_F (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh')
    have hU : (h⁻¹)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * h⁻¹ = _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := _root_.Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hh.1
    have hU2 : (h⁻¹)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS = _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * h := by
      conv_rhs => rw [← hU]
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]
    have key : (_root_.Formalism.QuantumDeterminants.Fm _ _ z)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * h = (_root_.Formalism.QuantumDeterminants.Fm _ _ z)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := by
      rw [Matrix.mul_assoc, ← hU2, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hF]
    have E : (_root_.Formalism.QuantumDeterminants.Fm _ _ z)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (h * g₀ * h'⁻¹) * _root_.Formalism.QuantumDeterminants.Fm _ _ z' =
        (_root_.Formalism.QuantumDeterminants.Fm _ _ z)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * g₀ * _root_.Formalism.QuantumDeterminants.Fm _ _ z' := by
      calc _ = ((_root_.Formalism.QuantumDeterminants.Fm _ _ z)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * h) * g₀ * (h'⁻¹ * _root_.Formalism.QuantumDeterminants.Fm _ _ z') := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [key, hF']
    rw [← hZ]
    unfold _root_.Formalism.MainNotions.S.ZhatO
    rw [_root_.Formalism.QuantumDeterminants.Zhat_eq, _root_.Formalism.QuantumDeterminants.Zhat_eq, E]
  · rw [Measure.map_apply hc'.measurable (_root_.GlobalTheory.Amp.RootMove.measurableSet_notR _)]
    refine measure_mono_null ?_ hnull
    intro x hx
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hx ⊢
    intro hR
    apply hx
    obtain ⟨hR1, hR2⟩ := hR
    have e : (h * g₀ * h'⁻¹) * (h' * Matrix.of x * h'⁻¹) * (h * g₀ * h'⁻¹)⁻¹ =
        h * (g₀ * Matrix.of x * g₀⁻¹) * h⁻¹ := by
      simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hd', Matrix.mul_assoc,
        Matrix.nonsing_inv_mul_cancel_left _ _ hd']
    refine ⟨(_root_.Formalism.QuantumDeterminants.uWNormal _ _ z' hz' h' hh' _ hR1).1, ?_⟩
    change (h * g₀ * h'⁻¹) * (h' * Matrix.of x * h'⁻¹) * (h * g₀ * h'⁻¹)⁻¹ ∈ _
    rw [e]
    exact (_root_.Formalism.QuantumDeterminants.uWNormal _ _ z hz h hh _ hR2).1
  · rw [Measure.map_map (_root_.GlobalTheory.Amp.RootMove.measurable_rootCoords z' p) hc'.measurable]
    convert hmap using 2
    funext x
    have hx := flagMat_conj_eq_of_mem_UWset hh' (Matrix.of x)
    simp only [Function.comp_apply]
    unfold _root_.Formalism.MainNotions.S.rootCoords
    exact congrArg (fun M => fun q : ↥(_root_.Formalism.MainNotions.S.rootPat p) => M q.1.1 q.1.2) hx
  · have E : ∀ X : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ,
        (h' * m') * (n'⁻¹ * X * n') * (h' * m')⁻¹ =
          (h' * (n' * m'⁻¹) * h'⁻¹)⁻¹ * (h' * X * h'⁻¹) * (h' * (n' * m'⁻¹) * h'⁻¹) := by
      intro X
      simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hd',
        Matrix.nonsing_inv_nonsing_inv _ hdm', Matrix.mul_assoc,
        Matrix.nonsing_inv_mul_cancel_left _ _ hd']
    rw [Measure.map_map, Measure.map_map]
    · congr 1
      funext x i j
      exact congrArg (fun M : Matrix _ _ ℂ => M i j) (E (Matrix.of x))
    all_goals exact (_root_.GlobalTheory.Amp.RootMove.continuous_lr _ _).measurable

end GlobalTheory.Amp.RootMove
