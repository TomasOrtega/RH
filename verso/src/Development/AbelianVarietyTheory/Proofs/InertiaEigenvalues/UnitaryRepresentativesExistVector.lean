import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOfMemGfC
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsKHwMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScalarWeightSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.UnitaryToGl

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.WeightSum.weight_sum_mem`. Consider the case `exact _root_.GlobalTheory.WeightSum.weight_sum_mem`. Consider the case `(apply _root_.GlobalTheory.WeightSum.weight_sum_mem <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.WeightSum.weight_sum_mem <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.WeightSum.weight_sum_mem <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.WeightSum.weight_sum_mem ..)`.
-/
theorem weighted_mem {E : Type} [AddCommGroup E] [Module ℂ E] (V : Submodule ℂ E) {ι : Type} (S : Finset ι)
    (w : ι → ℤ) (f : ι → E) (h : ∀ z : ℂ, ‖z‖ = 1 → ∑ s ∈ S, (z ^ w s) • f s ∈ V) :
    ∑ s ∈ S, (w s : ℂ) • f s ∈ V := by
  first
  | exact @_root_.GlobalTheory.WeightSum.weight_sum_mem
  | exact _root_.GlobalTheory.WeightSum.weight_sum_mem
  | (apply _root_.GlobalTheory.WeightSum.weight_sum_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.WeightSum.weight_sum_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.WeightSum.weight_sum_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.WeightSum.weight_sum_mem ..)

end GlobalTheory.UnitaryToGl

namespace GlobalTheory.UnitaryToGl

open MvPolynomial
open Formalism.IndefR.Links (PolF)
open Classical

noncomputable section

variable {D : D7} {m n : ℕ}

def gder (p : D.what₂.Tau → ℕ) (τ : D.what₂.Tau) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Derivation ℂ (PolF D m n) (PolF D m n) :=
  MvPolynomial.mkDerivation ℂ fun v =>
    if v.1 = τ then
      (if v.2.1.val < p τ then -∑ d, C (Z v.2.2 d) * X (τ, v.2.1, d) else ∑ d, C (Z d v.2.2) * X (τ, v.2.1, d))
    else 0

/- English proof (translation)
Simplify using `[gder, MvPolynomial.mkDerivation_X]`.
-/
theorem gder_X (p : D.what₂.Tau → ℕ) (τ : D.what₂.Tau) (Z : Matrix (Fin n) (Fin n) ℂ) (v : Formalism.IndefR.Datum.FVar D m n) :
    gder p τ Z (X v) = if v.1 = τ then
      (if v.2.1.val < p τ then -∑ d, C (Z v.2.2 d) * X (τ, v.2.1, d) else ∑ d, C (Z d v.2.2) * X (τ, v.2.1, d))
    else 0 := by
  simp [gder, MvPolynomial.mkDerivation_X]

def dU (c : Fin n) (z : ℂˣ) : GL (Fin n) ℂ where
  val := Matrix.diagonal (Function.update 1 c (z : ℂ))
  inv := Matrix.diagonal (Function.update 1 c ((z⁻¹ : ℂˣ) : ℂ))
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; by_cases h : i = c
    · subst h; simp
    · simp [Function.update_of_ne h]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; by_cases h : i = c
    · subst h; simp
    · simp [Function.update_of_ne h]

def tor (τ : D.what₂.Tau) (c : Fin n) (z : ℂˣ) : GlobalTheory.ExportSeries.GLR D n := Function.update 1 τ (dU c z)

def ex (p : D.what₂.Tau → ℕ) (τ : D.what₂.Tau) (c : Fin n) (v : Formalism.IndefR.Datum.FVar D m n) : ℤ :=
  if v.1 = τ ∧ v.2.2 = c then (if v.2.1.val < p τ then -1 else 1) else 0

def wt (p : D.what₂.Tau → ℕ) (τ : D.what₂.Tau) (c : Fin n) (s : Formalism.IndefR.Datum.FVar D m n →₀ ℕ) : ℤ :=
  s.sum fun v k => ex p τ c v * k

/- English proof (translation)
Simplify using `[wt]`.
-/
theorem wt_zero (p : D.what₂.Tau → ℕ) (τ : D.what₂.Tau) (c : Fin n) : wt (m := m) p τ c 0 = 0 := by
  simp [wt]

/- English proof (translation)
Rewrite using `[wt, Finsupp.sum_add_index' (by simp) (by intros; push_cast; ring), Finsupp.sum_single_index (by simp), ← wt]`.
-/
theorem wt_single_add (p : D.what₂.Tau → ℕ) (τ : D.what₂.Tau) (c : Fin n) (v : Formalism.IndefR.Datum.FVar D m n) (k : ℕ)
    (s : Formalism.IndefR.Datum.FVar D m n →₀ ℕ) : wt p τ c (Finsupp.single v k + s) = ex p τ c v * k + wt p τ c s := by
  rw [wt, Finsupp.sum_add_index' (by simp) (by intros; push_cast; ring), Finsupp.sum_single_index (by simp), ← wt]

/- English proof (translation)
Rewrite using `[Finset.sum_eq_single d (fun b _ hb => by simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)]) (by simp)]; simp`.
-/
theorem sum_diag_left (f : Fin n → ℂ) (d : Fin n) (Y : Fin n → PolF D m n) :
    ∑ x, C (Matrix.diagonal f d x) * Y x = C (f d) * Y d := by
  rw [Finset.sum_eq_single d (fun b _ hb => by simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)]) (by simp)]; simp

/- English proof (translation)
Rewrite using `[Finset.sum_eq_single d (fun b _ hb => by simp [Matrix.diagonal_apply_ne _ hb]) (by simp)]; simp`.
-/
theorem sum_diag_right (f : Fin n → ℂ) (d : Fin n) (Y : Fin n → PolF D m n) :
    ∑ x, C (Matrix.diagonal f x d) * Y x = C (f d) * Y d := by
  rw [Finset.sum_eq_single d (fun b _ hb => by simp [Matrix.diagonal_apply_ne _ hb]) (by simp)]; simp

/- English proof (translation)
Take `⟨σ, i, d⟩` from `v`. Rewrite using `[GlobalTheory.ExportSeries.fockSubst, aeval_X]`. Distinguish the cases in `hσ : σ = τ`. Substitute `hσ` using the available equality. Establish `h1 : (((dU c z)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (Function.update 1 c ((z⁻¹ : ℂˣ) : ℂ))` using `rfl`.

Establish `h2 : ((dU c z : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (Function.update 1 c (z : ℂ))` using `rfl`. Simplify using `only [tor, Function.update_self, ex, true_and, h1, h2, sum_diag_left, sum_diag_right]`. Distinguish the cases in `hd : d = c`. Substitute `hd` using the available equality. Apply the tactic sequence `by_cases hi : (i : ℕ) < p σ <;> simp [hi, smul_eq_C_mul]`.

Apply the tactic sequence `by_cases hi : (i : ℕ) < p σ <;> simp [hi, hd, Function.update_of_ne hd]`. Simplify using `[tor, Function.update_of_ne hσ, ex, hσ, Matrix.one_apply]`.
-/
theorem tor_X (p : D.what₂.Tau → ℕ) (τ : D.what₂.Tau) (c : Fin n) (z : ℂˣ) (v : Formalism.IndefR.Datum.FVar D m n) :
    GlobalTheory.ExportSeries.fockSubst p (tor τ c z) (X v) = ((z : ℂ) ^ ex p τ c v) • (X v : PolF D m n) := by
  obtain ⟨σ, i, d⟩ := v
  rw [GlobalTheory.ExportSeries.fockSubst, aeval_X]
  by_cases hσ : σ = τ
  · subst hσ
    have h1 : (((dU c z)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
        Matrix.diagonal (Function.update 1 c ((z⁻¹ : ℂˣ) : ℂ)) := rfl
    have h2 : ((dU c z : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (Function.update 1 c (z : ℂ)) := rfl
    simp only [tor, Function.update_self, ex, true_and, h1, h2, sum_diag_left, sum_diag_right]
    by_cases hd : d = c
    · subst hd
      by_cases hi : (i : ℕ) < p σ <;> simp [hi, smul_eq_C_mul]
    · by_cases hi : (i : ℕ) < p σ <;> simp [hi, hd, Function.update_of_ne hd]
  · simp [tor, Function.update_of_ne hσ, ex, hσ, Matrix.one_apply]

/- English proof (translation)
Proceed by induction on `s using Finsupp.induction with`. Consider the case `zero => simp [wt_zero, ← C_apply]`. Consider the case `single_add v k s hv hk ih`. Rewrite using `[monomial_single_add, map_mul, map_pow, tor_X, ih, wt_single_add, smul_pow, smul_mul_smul_comm, ← zpow_natCast, ← _root_.zpow_mul, ← zpow_add₀ (Units.ne_zero z)]`.
-/
theorem tor_monomial (p : D.what₂.Tau → ℕ) (τ : D.what₂.Tau) (c : Fin n) (z : ℂˣ) (s : Formalism.IndefR.Datum.FVar D m n →₀ ℕ)
    (a : ℂ) : GlobalTheory.ExportSeries.fockSubst p (tor τ c z) (monomial s a : PolF D m n) =
      ((z : ℂ) ^ wt p τ c s) • (monomial s a : PolF D m n) := by
  induction s using Finsupp.induction with
  | zero => simp [wt_zero, ← C_apply]
  | single_add v k s hv hk ih =>
    rw [monomial_single_add, map_mul, map_pow, tor_X, ih, wt_single_add, smul_pow, smul_mul_smul_comm,
      ← zpow_natCast, ← _root_.zpow_mul, ← zpow_add₀ (Units.ne_zero z)]

/- English proof (translation)
Take `⟨σ, i, d⟩` from `v`. Rewrite using `[gder_X]`. Distinguish the cases in `hσ : σ = τ`. Substitute `hσ` using the available equality. Simplify using `only [if_true]`.

Distinguish the cases in `hd : d = c`. Substitute `hd` using the available equality. Apply the tactic sequence `by_cases hi : (i : ℕ) < p σ <;> simp [ex, hi, Matrix.single_apply, smul_eq_C_mul]`. Apply the tactic sequence `by_cases hi : (i : ℕ) < p σ <;> simp [ex, hi, hd, Matrix.single_apply, Ne.symm hd]`. Simplify using `[ex, hσ]`.
-/
theorem gder_single_X (p : D.what₂.Tau → ℕ) (τ : D.what₂.Tau) (c : Fin n) (v : Formalism.IndefR.Datum.FVar D m n) :
    gder p τ (Matrix.single c c 1) (X v : PolF D m n) = (ex p τ c v : ℂ) • (X v : PolF D m n) := by
  obtain ⟨σ, i, d⟩ := v
  rw [gder_X]
  by_cases hσ : σ = τ
  · subst hσ
    simp only [if_true]
    by_cases hd : d = c
    · subst hd
      by_cases hi : (i : ℕ) < p σ <;> simp [ex, hi, Matrix.single_apply, smul_eq_C_mul]
    · by_cases hi : (i : ℕ) < p σ <;> simp [ex, hi, hd, Matrix.single_apply, Ne.symm hd]
  · simp [ex, hσ]

/- English proof (translation)
Proceed by induction on `s using Finsupp.induction with`. Consider the case `zero => simp [wt_zero, ← C_apply]`. Consider the case `single_add v k s hv hk ih`. Rewrite using `[monomial_single_add, Derivation.leibniz, Derivation.leibniz_pow, gder_single_X, ih, wt_single_add]`. Take `⟨k', rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hk`.

Simplify using `only [smul_eq_mul, nsmul_eq_mul, MvPolynomial.smul_eq_C_mul, Nat.succ_sub_one]`. Use `push_cast`. Simplify using `only [map_add, map_mul, map_intCast, map_natCast, map_one, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gder_monomial (p : D.what₂.Tau → ℕ) (τ : D.what₂.Tau) (c : Fin n) (s : Formalism.IndefR.Datum.FVar D m n →₀ ℕ) (a : ℂ) :
    gder p τ (Matrix.single c c 1) (monomial s a : PolF D m n) = (wt p τ c s : ℂ) • (monomial s a : PolF D m n) := by
  induction s using Finsupp.induction with
  | zero => simp [wt_zero, ← C_apply]
  | single_add v k s hv hk ih =>
    rw [monomial_single_add, Derivation.leibniz, Derivation.leibniz_pow, gder_single_X, ih, wt_single_add]
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    simp only [smul_eq_mul, nsmul_eq_mul, MvPolynomial.smul_eq_C_mul, Nat.succ_sub_one]
    push_cast
    simp only [map_add, map_mul, map_intCast, map_natCast, map_one, pow_succ]
    ring

end

end GlobalTheory.UnitaryToGl

namespace GlobalTheory.UnitaryToGl

open MvPolynomial
open Formalism.IndefR.Links (PolF)
open Classical

noncomputable section

variable {D : D7} {m n : ℕ}

def IsUF (u : GlobalTheory.ExportSeries.GLR D n) : Prop := ∀ σ, ((u σ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ

/- English proof (translation)
Introduce `σ`. Establish `h` using `hu σ`. Establish `e : (((u⁻¹) σ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = star ((u σ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)`. Rewrite using `[Pi.inv_apply, Matrix.coe_units_inv]`. Conclude with `Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.mp h)`.

Rewrite using `[e]`. Conclude with `Unitary.star_mem h`.
-/
theorem isUF_inv {u : GlobalTheory.ExportSeries.GLR D n} (hu : IsUF u) : IsUF u⁻¹ := by
  intro σ
  have h := hu σ
  have e : (((u⁻¹) σ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = star ((u σ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
    rw [Pi.inv_apply, Matrix.coe_units_inv]
    exact Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.mp h)
  rw [e]; exact Unitary.star_mem h

/- English proof (translation)
Introduce `σ`. Distinguish the cases in `h : σ = τ`. Substitute `h` using the available equality. Simplify using `using hG`. Rewrite using `[Function.update_of_ne h]`.

Conclude with `one_mem _`.
-/
theorem isUF_update (τ : D.what₂.Tau) (G : GL (Fin n) ℂ) (hG : (G : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    IsUF (Function.update (1 : GlobalTheory.ExportSeries.GLR D n) τ G) := by
  intro σ
  by_cases h : σ = τ
  · subst h; simpa using hG
  · rw [Function.update_of_ne h]; exact one_mem _

/- English proof (translation)
Rewrite using `[Matrix.mem_unitaryGroup_iff]`. Express the relevant statement in the definitionally equal form `Matrix.diagonal _ * star (Matrix.diagonal _) = 1`. Rewrite using `[Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Distinguish the cases in `h : i = c`. Substitute `h` using the available equality. Simplify using `only [Function.update_self, Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]`. Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne h]`.
-/
theorem dU_mem (c : Fin n) (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1) :
    ((dU c z : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change Matrix.diagonal _ * star (Matrix.diagonal _) = 1
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i
  by_cases h : i = c
  · subst h
    simp only [Function.update_self, Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    simp
  · simp [Function.update_of_ne h]

/- English proof (translation)
The claim follows from `isUF_update τ _ (dU_mem c z hz)`.
-/
theorem isUF_tor (τ : D.what₂.Tau) (c : Fin n) (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1) : IsUF (tor (D := D) τ c z) :=
  isUF_update τ _ (dU_mem c z hz)

section Frame

variable {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] (w : GlobalTheory.ExportSeries.Weight D n)
  (BS : GlobalTheory.ExportSeries.GLR D n) (r : K →* GlobalTheory.ExportSeries.GLR D n) (ρ : K →* Module.End ℂ W)

def IsEqv (φ : W →ₗ[ℂ] PolF D m n) : Prop := ∀ (k : K) (x : W), φ (ρ k x) = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ x)

def Transp (O : Module.End ℂ (PolF D m n)) : Prop :=
  ∃ A : Module.End ℂ W, ∀ φ : W →ₗ[ℂ] PolF D m n, IsEqv w BS r ρ φ → φ ∘ₗ A = O ∘ₗ φ

variable {w BS r ρ}

/- English proof (translation)
Take `⟨A, hA⟩` from `h`. Take `⟨A', hA'⟩` from `h'`. Use `⟨A + A', fun φ hφ => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.comp_add, hA φ hφ, hA' φ hφ, LinearMap.add_comp]`.
-/
theorem transp_add {O O' : Module.End ℂ (PolF D m n)} (h : Transp w BS r ρ O) (h' : Transp w BS r ρ O') :
    Transp w BS r ρ (O + O') := by
  obtain ⟨A, hA⟩ := h; obtain ⟨A', hA'⟩ := h'
  refine ⟨A + A', fun φ hφ => ?_⟩
  rw [LinearMap.comp_add, hA φ hφ, hA' φ hφ, LinearMap.add_comp]

/- English proof (translation)
Take `⟨A, hA⟩` from `h`. Use `⟨c • A, fun φ hφ => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.comp_smul, hA φ hφ, LinearMap.smul_comp]`.
-/
theorem transp_smul (c : ℂ) {O : Module.End ℂ (PolF D m n)} (h : Transp w BS r ρ O) : Transp w BS r ρ (c • O) := by
  obtain ⟨A, hA⟩ := h
  refine ⟨c • A, fun φ hφ => ?_⟩
  rw [LinearMap.comp_smul, hA φ hφ, LinearMap.smul_comp]

/- English proof (translation)
Take `⟨A, hA⟩` from `h`. Take `⟨A', hA'⟩` from `h'`. Use `⟨A * A', fun φ hφ => ?_⟩` and prove the remaining obligations. Rewrite using `[Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hA φ hφ, LinearMap.comp_assoc, hA' φ hφ, LinearMap.comp_assoc]`.
-/
theorem transp_mul {O O' : Module.End ℂ (PolF D m n)} (h : Transp w BS r ρ O) (h' : Transp w BS r ρ O') :
    Transp w BS r ρ (O * O') := by
  obtain ⟨A, hA⟩ := h; obtain ⟨A', hA'⟩ := h'
  refine ⟨A * A', fun φ hφ => ?_⟩
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hA φ hφ, LinearMap.comp_assoc, hA' φ hφ,
    LinearMap.comp_assoc]

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, fun φ _ => by rw [Module.End.one_eq_id, Module.End.one_eq_id, LinearMap.comp_id, LinearMap.id_comp]⟩`.
-/
theorem transp_one : Transp w BS r ρ (1 : Module.End ℂ (PolF D m n)) :=
  ⟨1, fun φ _ => by rw [Module.End.one_eq_id, Module.End.one_eq_id, LinearMap.comp_id, LinearMap.id_comp]⟩

/- English proof (translation)
Simplify using `using transp_smul (w := w) (BS := BS) (r := r) (ρ := ρ) 0 transp_one`.
-/
theorem transp_zero : Transp w BS r ρ (0 : Module.End ℂ (PolF D m n)) := by
  simpa using transp_smul (w := w) (BS := BS) (r := r) (ρ := ρ) 0 transp_one

/- English proof (translation)
Establish `hg : GlobalTheory.ExportSeries.inBasis BS (BS * u * BS⁻¹) = u`. Simplify using `[GlobalTheory.ExportSeries.inBasis, MulAut.conj_apply, mul_assoc]`. Take `⟨k, hk⟩` from `hr (BS * u * BS⁻¹) (by rw [hg]; exact hu)`. Use `⟨(((GlobalTheory.ExportSeries.detFam w.c (BS * u * BS⁻¹)) : ℂˣ) : ℂ) • ρ k, fun φ hφ => ?_⟩` and prove the remaining obligations. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.comp_apply, LinearMap.smul_apply, map_smul, hφ k x, hk, GlobalTheory.ExportSeries.fockGL_apply, hg, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]`. Both sides reduce to the same expression.
-/
theorem transp_subst
    (hr : ∀ g : GlobalTheory.ExportSeries.GLR D n, (∀ τ, ((GlobalTheory.ExportSeries.inBasis BS g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈
      Matrix.unitaryGroup (Fin n) ℂ) → ∃ k, r k = g)
    {u : GlobalTheory.ExportSeries.GLR D n} (hu : IsUF u) :
    Transp w BS r ρ (GlobalTheory.ExportSeries.fockSubst (m := m) w.p u).toLinearMap := by
  have hg : GlobalTheory.ExportSeries.inBasis BS (BS * u * BS⁻¹) = u := by
    simp [GlobalTheory.ExportSeries.inBasis, MulAut.conj_apply, mul_assoc]
  obtain ⟨k, hk⟩ := hr (BS * u * BS⁻¹) (by rw [hg]; exact hu)
  refine ⟨(((GlobalTheory.ExportSeries.detFam w.c (BS * u * BS⁻¹)) : ℂˣ) : ℂ) • ρ k, fun φ hφ => ?_⟩
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, hφ k x, hk, GlobalTheory.ExportSeries.fockGL_apply, hg, smul_smul,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  rfl

/- English proof (translation)
Establish `hR : ∀ v ∈ LinearMap.range ψ, O v ∈ LinearMap.range ψ`. Introduce and unpack `_ ⟨x, rfl⟩`. Take `⟨y, hy, -⟩` from `h ψ hψ x`. Conclude with `⟨y, hy⟩`. Set `e` to `LinearEquiv.ofInjective ψ hinj`.

Set `A : Module.End ℂ W` to `e.symm.toLinearMap ∘ₗ (O.restrict hR) ∘ₗ e.toLinearMap`. Establish `hA : ∀ x, ψ (A x) = O (ψ x)`. Introduce `x`. Establish `he : ∀ x', (e x' : PolF D m n) = ψ x'` using `fun x' => by simp [e]`. Establish `: ψ (e.symm ((O.restrict hR) (e x))) = ((O.restrict hR) (e x) : PolF D m n)`.

Rewrite using `[← he, LinearEquiv.apply_symm_apply]`. Simplify `this` using `[A, he]`. Use `⟨A, fun φ hφ => LinearMap.ext fun x => ?_⟩` and prove the remaining obligations. Take `⟨y, hy1, hy2⟩` from `h φ hφ x`. Establish `: y = A x` using `hinj (by rw [hy1, hA])`.

Simplify using `[← this, hy2]`.
-/
theorem transp_of_pairs {ψ : W →ₗ[ℂ] PolF D m n} (hinj : Function.Injective ψ) (hψ : IsEqv w BS r ρ ψ)
    {O : Module.End ℂ (PolF D m n)}
    (h : ∀ φ : W →ₗ[ℂ] PolF D m n, IsEqv w BS r ρ φ → ∀ x, ∃ y, ψ y = O (ψ x) ∧ φ y = O (φ x)) :
    Transp w BS r ρ O := by
  have hR : ∀ v ∈ LinearMap.range ψ, O v ∈ LinearMap.range ψ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy, -⟩ := h ψ hψ x
    exact ⟨y, hy⟩
  let e := LinearEquiv.ofInjective ψ hinj
  let A : Module.End ℂ W := e.symm.toLinearMap ∘ₗ (O.restrict hR) ∘ₗ e.toLinearMap
  have hA : ∀ x, ψ (A x) = O (ψ x) := by
    intro x
    have he : ∀ x', (e x' : PolF D m n) = ψ x' := fun x' => by simp [e]
    have : ψ (e.symm ((O.restrict hR) (e x))) = ((O.restrict hR) (e x) : PolF D m n) := by
      rw [← he, LinearEquiv.apply_symm_apply]
    simpa [A, he] using this
  refine ⟨A, fun φ hφ => LinearMap.ext fun x => ?_⟩
  obtain ⟨y, hy1, hy2⟩ := h φ hφ x
  have : y = A x := hinj (by rw [hy1, hA])
  simp [← this, hy2]

end Frame

/- English proof (translation)
Use `conv_lhs => rw [P.as_sum]`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun s _ => tor_monomial p τ c z s _`.
-/
theorem expand_tor (p : D.what₂.Tau → ℕ) (τ : D.what₂.Tau) (c : Fin n) (z : ℂˣ) (P : PolF D m n) :
    GlobalTheory.ExportSeries.fockSubst p (tor τ c z) P = ∑ s ∈ P.support, ((z : ℂ) ^ wt p τ c s) • monomial s (coeff s P) := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  exact Finset.sum_congr rfl fun s _ => tor_monomial p τ c z s _

/- English proof (translation)
Use `conv_lhs => rw [P.as_sum]`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun s _ => gder_monomial p τ c s _`.
-/
theorem expand_gder (p : D.what₂.Tau → ℕ) (τ : D.what₂.Tau) (c : Fin n) (P : PolF D m n) :
    gder p τ (Matrix.single c c 1) P = ∑ s ∈ P.support, (wt p τ c s : ℂ) • monomial s (coeff s P) := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  exact Finset.sum_congr rfl fun s _ => gder_monomial p τ c s _

end

end GlobalTheory.UnitaryToGl

namespace GlobalTheory.UnitaryToGl

open MvPolynomial
open Formalism.IndefR.Links (PolF)
open Classical

noncomputable section

variable {D : D7} {m n : ℕ}

/- English proof (translation)
Establish `sumApp : ∀ (f : Fin m → Derivation ℂ (PolF D m n) (PolF D m n)) (P : PolF D m n), (∑ i, f i) P = ∑ i, f i P`. Introduce `f P`. Proceed by induction on `(Finset.univ : Finset (Fin m)) using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, Derivation.add_apply, ih]`.

Set `T : Fin m → Derivation ℂ (PolF D m n) (PolF D m n)` to `fun i => if (i : ℕ) < w.p τ then (X (τ, i, a) : PolF D m n) • (pderiv (τ, i, b) : Derivation ℂ (PolF D m n) (PolF D m n)) else -((X (τ, i, b) : PolF D m n) • (pderiv (τ, i, a) : Derivation ℂ (PolF D m n) (PolF D m n)))`. Establish `hD : ∑ i, T i = -gder (m` using `m) w.p τ (Matrix.single b a 1) := by`. Use `MvPolynomial.derivation_ext fun v => ?_` and prove the remaining obligations. Take `⟨σ, j, c⟩` from `v`. Rewrite using `[sumApp, Derivation.neg_apply, gder_X]`.

Distinguish the cases in `hσ : σ = τ`. Substitute `hσ` using the available equality. Rewrite using `[Finset.sum_eq_single j]`. Distinguish the cases in `hj : (j : ℕ) < w.p σ`. Simplify using `[T, hj, Matrix.single_apply, Pi.single_apply]`.

Distinguish the cases in `hcb : c = b`. Substitute `hcb` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hcb, Ne.symm hcb]`. Simplify using `[T, hj, Matrix.single_apply, Pi.single_apply]`.

Distinguish the cases in `hca : c = a`. Substitute `hca` using the available equality. Simplify using `[Finset.sum_ite_eq]`. Simplify using `[hca, Ne.symm hca]`. Introduce `i _ hij`.

Apply the tactic sequence `by_cases hi : (i : ℕ) < w.p σ <;> simp [T, hi, Pi.single_apply, hij]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg hσ, neg_zero]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases hi : (i : ℕ) < w.p τ <;> simp [T, hi, Pi.single_apply, Ne.symm hσ]`.

Establish `hA : GlobalTheory.LowestKType.sop (m` using `m) w τ a b = ∑ i : Fin m, (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) i a * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO τ (fun _ : Fin n => true) (fun j : Fi …`. Unfold `GlobalTheory.LowestKType.sop GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS`. Rewrite using `[Finset.sum_eq_single a, Finset.sum_eq_single b]`. Simplify using the standard rewrite rules. Introduce `k _ hk`.

Simplify using `[Matrix.single_apply, Ne.symm hk]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Simplify using `[Matrix.single_apply, Ne.symm hj]`.

Simplify using the standard rewrite rules. Establish `hneg : ∀ P, -(gder (m` using `m) w.p τ (Matrix.single b a 1) P) = ∑ i, T i P := by`. Introduce `P`. Rewrite using `[← sumApp, hD, Derivation.neg_apply]`. Use `LinearMap.ext fun P => ?_` and prove the remaining obligations.

Establish `hc : ((gder (m` using `m) w.p τ (Matrix.single b a 1)).toLinearMap : PolF D m n →ₗ[ℂ] PolF D m n) P = gder (m := m) w.p τ (Matrix.single b a 1) P := rfl`. Rewrite using `[hA, LinearMap.add_apply, LinearMap.neg_apply, hc, hneg, LinearMap.smul_apply, Module.End.one_apply, Finset.sum_smul, LinearMap.sum_apply, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : (i : ℕ) < w.p τ`. Apply the tactic sequence `simp [T, hi, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn] split_ifs <;> simp`.

Simplify using `[T, hi, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using `only [if_true, Pi.single_eq_same, mul_one, LinearMap.smul_apply, Module.End.one_apply]`. Use `module`.

Simplify using `[hab, Pi.single_apply]`.
-/
theorem sop_eq (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin n) :
    GlobalTheory.LowestKType.sop (m := m) w τ a b = -(gder w.p τ (Matrix.single b a 1)).toLinearMap +
      (∑ i : Fin m, ((if a = b then (1 / 2 : ℂ) else 0) - (if (i : ℕ) < w.p τ then 0 else if a = b then 1 else 0))) • 1 := by
  have sumApp : ∀ (f : Fin m → Derivation ℂ (PolF D m n) (PolF D m n)) (P : PolF D m n),
      (∑ i, f i) P = ∑ i, f i P := by
    intro f P
    induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
    | empty => simp
    | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, Derivation.add_apply, ih]
  let T : Fin m → Derivation ℂ (PolF D m n) (PolF D m n) := fun i =>
    if (i : ℕ) < w.p τ then (X (τ, i, a) : PolF D m n) • (pderiv (τ, i, b) : Derivation ℂ (PolF D m n) (PolF D m n))
    else -((X (τ, i, b) : PolF D m n) • (pderiv (τ, i, a) : Derivation ℂ (PolF D m n) (PolF D m n)))
  have hD : ∑ i, T i = -gder (m := m) w.p τ (Matrix.single b a 1) := by
    refine MvPolynomial.derivation_ext fun v => ?_
    obtain ⟨σ, j, c⟩ := v
    rw [sumApp, Derivation.neg_apply, gder_X]
    by_cases hσ : σ = τ
    · subst hσ
      rw [Finset.sum_eq_single j]
      · by_cases hj : (j : ℕ) < w.p σ
        · simp [T, hj, Matrix.single_apply, Pi.single_apply]
          by_cases hcb : c = b
          · subst hcb; simp
          · simp [hcb, Ne.symm hcb]
        · simp [T, hj, Matrix.single_apply, Pi.single_apply]
          by_cases hca : c = a
          · subst hca; simp [Finset.sum_ite_eq]
          · simp [hca, Ne.symm hca]
      · intro i _ hij
        by_cases hi : (i : ℕ) < w.p σ <;> simp [T, hi, Pi.single_apply, hij]
      · simp
    · rw [if_neg hσ, neg_zero]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hi : (i : ℕ) < w.p τ <;> simp [T, hi, Pi.single_apply, Ne.symm hσ]
  have hA : GlobalTheory.LowestKType.sop (m := m) w τ a b = ∑ i : Fin m,
      (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) i a *
        GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) i b +
        if a = b then (1 / 2 : ℂ) • 1 else 0) := by
    unfold GlobalTheory.LowestKType.sop GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS
    rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
    · simp
    · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
    · simp
    · intro j _ hj; refine Finset.sum_eq_zero fun k _ => ?_; simp [Matrix.single_apply, Ne.symm hj]
    · simp
  have hneg : ∀ P, -(gder (m := m) w.p τ (Matrix.single b a 1) P) = ∑ i, T i P := by
    intro P; rw [← sumApp, hD, Derivation.neg_apply]
  refine LinearMap.ext fun P => ?_
  have hc : ((gder (m := m) w.p τ (Matrix.single b a 1)).toLinearMap : PolF D m n →ₗ[ℂ] PolF D m n) P =
      gder (m := m) w.p τ (Matrix.single b a 1) P := rfl
  rw [hA, LinearMap.add_apply, LinearMap.neg_apply, hc, hneg, LinearMap.smul_apply,
    Module.End.one_apply, Finset.sum_smul, LinearMap.sum_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : (i : ℕ) < w.p τ
  · simp [T, hi, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn]
    split_ifs <;> simp
  · simp [T, hi, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn]
    by_cases hab : a = b
    · subst hab
      simp only [if_true, Pi.single_eq_same, mul_one, LinearMap.smul_apply, Module.End.one_apply]
      module
    · simp [hab, Pi.single_apply]

/- English proof (translation)
Take `⟨gi, hgi⟩ : ∃ gi : Matrix (Fin n) (Fin n) ℂ, gi = (((g τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)` from `⟨_, rfl⟩`. Take `⟨g0, hg0⟩ : ∃ g0 : Matrix (Fin n) (Fin n) ℂ, g0 = (g τ : Matrix (Fin n) (Fin n) ℂ)` from `⟨_, rfl⟩`. Rewrite using `[← hgi, ← hg0]`. Take `⟨Z', hZ'⟩ : ∃ Z', Z' = g0 * Z * gi` from `⟨_, rfl⟩`. Rewrite using `[← hZ']`.

Establish `dsum : ∀ (A : Fin n → ℂ) (B : Fin n → Fin n → ℂ) (Y : Fin n → PolF D m n), ∑ d, C (A d) * ∑ b, C (B d b) * Y b = ∑ b, C (∑ d, A d * B d b) * Y b`. Introduce `A B Y`. Simplify using `only [Finset.mul_sum, map_sum, Finset.sum_mul, map_mul, mul_assoc]`. Conclude with `Finset.sum_comm`. Establish `lin : ∀ (E : Derivation ℂ (PolF D m n) (PolF D m n)) (k : Fin n → ℂ) (Y : Fin n → PolF D m n), E (∑ b, C (k b) * Y b) = ∑ b, C (k b) * E (Y b)`.

Introduce `E k Y`. Simplify using `only [← smul_eq_C_mul, map_sum, E.map_smul]`. Establish `linS : ∀ (k : Fin n → ℂ) (Y : Fin n → PolF D m n), GlobalTheory.ExportSeries.fockSubst (m` using `m) p g (∑ b, C (k b) * Y b) = ∑ b, C (k b) * GlobalTheory.ExportSeries.fockSubst (m := m) p g (Y b) := by`. Introduce `k Y`. Simplify using `only [map_sum, map_mul, algHom_C, algebraMap_eq]`.

Establish `hS : ∀ (σ : D.what₂.Tau) (i : Fin m) (c : Fin n), GlobalTheory.ExportSeries.fockSubst (m` using `m) p g (X (σ, i, c)) = if (i : ℕ) < p σ then ∑ b, C ((((g σ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) c b) * X (σ, i, b) else ∑ b, C (((g σ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) b c) * X (σ, i, b) := by`. Introduce `σ i c`. Rewrite using `[GlobalTheory.ExportSeries.fockSubst, aeval_X]`. Establish `hgg : gi * g0 = 1`. Rewrite using `[hgi, hg0, ← Units.val_mul, inv_mul_cancel, Units.val_one]`.

Establish `e1 : Z * gi = gi * Z'`. Rewrite using `[hZ', ← Matrix.mul_assoc, ← Matrix.mul_assoc, hgg, Matrix.one_mul]`. Establish `e2 : g0 * Z = Z' * g0`. Rewrite using `[hZ', Matrix.mul_assoc _ gi, hgg, Matrix.mul_one]`. Establish `hX : ∀ v, GlobalTheory.ExportSeries.fockSubst (m` using `m) p g (gder p τ Z (X v)) = gder p τ Z' (GlobalTheory.ExportSeries.fockSubst (m := m) p g (X v)) := by`.

Introduce and unpack `⟨σ, i, c⟩`. Distinguish the cases in `hσ : σ = τ`. Substitute `hσ` using the available equality. Rewrite using `[gder_X, hS]`. Simplify using `only [if_true]`.

Distinguish the cases in `hi : (i : ℕ) < p σ`. Rewrite using `[if_pos hi, if_pos hi, map_neg, linS, lin, ← hgi]`. Establish `h1 : ∀ d, GlobalTheory.ExportSeries.fockSubst (m` using `m) p g (X (σ, i, d)) = ∑ b, C (gi d b) * X (σ, i, b) := by`. Introduce `d`. Rewrite using `[hS, if_pos hi, hgi]`.

Establish `h2 : ∀ b, gder (m` using `m) p σ Z' (X (σ, i, b)) = -∑ e, C (Z' b e) * X (σ, i, e) := by`. Introduce `b`. Rewrite using `[gder_X]`. Simplify using `only [if_true]`. Rewrite using `[if_pos hi]`.

Establish `key : ∀ b, ∑ d, Z c d * gi d b = ∑ d, gi c d * Z' d b` using `fun b => congrFun (congrFun e1 c) b`. Establish `d1` using `dsum (Z c) gi (fun b => X (σ, i, b))`. Establish `d2` using `dsum (gi c) Z' (fun b => X (σ, i, b))`. Simplify using `only [h1, h2, mul_neg, Finset.sum_neg_distrib] at d1 d2 ⊢`. Rewrite using `[d1, d2]`.

Simplify using `only [key]`. Rewrite using `[if_neg hi, if_neg hi, linS, lin, ← hg0]`. Establish `h1 : ∀ d, GlobalTheory.ExportSeries.fockSubst (m` using `m) p g (X (σ, i, d)) = ∑ b, C (g0 b d) * X (σ, i, b) := by`. Introduce `d`. Rewrite using `[hS, if_neg hi, hg0]`.

Establish `h2 : ∀ b, gder (m` using `m) p σ Z' (X (σ, i, b)) = ∑ e, C (Z' e b) * X (σ, i, e) := by`. Introduce `b`. Rewrite using `[gder_X]`. Simplify using `only [if_true]`. Rewrite using `[if_neg hi]`.

Establish `key : ∀ e, ∑ d, Z d c * g0 e d = ∑ b, g0 b c * Z' e b`. Introduce `e`. Use `congrFun (congrFun e2 e) c` as an intermediate fact. Simplify using `only [Matrix.mul_apply] at this`. Rewrite using `[Finset.sum_congr rfl (fun d _ => mul_comm (Z d c) (g0 e d)), this]`.

Conclude with `Finset.sum_congr rfl fun _ _ => mul_comm _ _`. Establish `d1` using `dsum (fun d => Z d c) (fun d b => g0 b d) (fun b => X (σ, i, b))`. Establish `d2` using `dsum (fun b => g0 b c) (fun b e => Z' e b) (fun b => X (σ, i, b))`. Simplify using `only [h1, h2] at d1 d2 ⊢`. Rewrite using `[d1, d2]`.

Simplify using `only [key]`. Establish `h0 : ∀ b, gder (m` using `m) p τ Z' (X (σ, i, b)) = 0 := by`. Introduce `b`. Rewrite using `[gder_X]`. Conclude with `if_neg hσ`.

Rewrite using `[gder_X, if_neg hσ, map_zero, hS]`. Apply the tactic sequence `split_ifs <;> simp only [lin, h0, mul_zero, Finset.sum_const_zero]`. Use `LinearMap.ext fun P => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `GlobalTheory.ExportSeries.fockSubst (m := m) p g (gder p τ Z P) = gder p τ Z' (GlobalTheory.ExportSeries.fockSubst (m := m) p g P)`. Proceed by induction on `P using MvPolynomial.induction_on with`.

Consider the case `C a => simp [MvPolynomial.derivation_C]`. Consider the case `add P Q hP hQ => simp only [map_add, hP, hQ]`. Consider the case `mul_X P v hP`. Rewrite using `[Derivation.leibniz, map_mul, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, map_mul, map_mul, hP, hX]`.
-/
theorem subst_comp_gder (p : D.what₂.Tau → ℕ) (τ : D.what₂.Tau) (g : GlobalTheory.ExportSeries.GLR D n) (Z : Matrix (Fin n) (Fin n) ℂ) :
    (GlobalTheory.ExportSeries.fockSubst (m := m) p g).toLinearMap ∘ₗ (gder p τ Z).toLinearMap =
      (gder p τ ((g τ : Matrix (Fin n) (Fin n) ℂ) * Z * (((g τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))).toLinearMap ∘ₗ
        (GlobalTheory.ExportSeries.fockSubst p g).toLinearMap := by
  obtain ⟨gi, hgi⟩ : ∃ gi : Matrix (Fin n) (Fin n) ℂ, gi = (((g τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) :=
    ⟨_, rfl⟩
  obtain ⟨g0, hg0⟩ : ∃ g0 : Matrix (Fin n) (Fin n) ℂ, g0 = (g τ : Matrix (Fin n) (Fin n) ℂ) := ⟨_, rfl⟩
  rw [← hgi, ← hg0]
  obtain ⟨Z', hZ'⟩ : ∃ Z', Z' = g0 * Z * gi := ⟨_, rfl⟩
  rw [← hZ']
  have dsum : ∀ (A : Fin n → ℂ) (B : Fin n → Fin n → ℂ) (Y : Fin n → PolF D m n),
      ∑ d, C (A d) * ∑ b, C (B d b) * Y b = ∑ b, C (∑ d, A d * B d b) * Y b := by
    intro A B Y
    simp only [Finset.mul_sum, map_sum, Finset.sum_mul, map_mul, mul_assoc]
    exact Finset.sum_comm
  have lin : ∀ (E : Derivation ℂ (PolF D m n) (PolF D m n)) (k : Fin n → ℂ) (Y : Fin n → PolF D m n),
      E (∑ b, C (k b) * Y b) = ∑ b, C (k b) * E (Y b) := by
    intro E k Y
    simp only [← smul_eq_C_mul, map_sum, E.map_smul]
  have linS : ∀ (k : Fin n → ℂ) (Y : Fin n → PolF D m n),
      GlobalTheory.ExportSeries.fockSubst (m := m) p g (∑ b, C (k b) * Y b) =
        ∑ b, C (k b) * GlobalTheory.ExportSeries.fockSubst (m := m) p g (Y b) := by
    intro k Y
    simp only [map_sum, map_mul, algHom_C, algebraMap_eq]
  have hS : ∀ (σ : D.what₂.Tau) (i : Fin m) (c : Fin n), GlobalTheory.ExportSeries.fockSubst (m := m) p g (X (σ, i, c)) =
      if (i : ℕ) < p σ then
      ∑ b, C ((((g σ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) c b) * X (σ, i, b)
      else ∑ b, C (((g σ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) b c) * X (σ, i, b) := by
    intro σ i c
    rw [GlobalTheory.ExportSeries.fockSubst, aeval_X]
  have hgg : gi * g0 = 1 := by
    rw [hgi, hg0, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e1 : Z * gi = gi * Z' := by
    rw [hZ', ← Matrix.mul_assoc, ← Matrix.mul_assoc, hgg, Matrix.one_mul]
  have e2 : g0 * Z = Z' * g0 := by
    rw [hZ', Matrix.mul_assoc _ gi, hgg, Matrix.mul_one]
  have hX : ∀ v, GlobalTheory.ExportSeries.fockSubst (m := m) p g (gder p τ Z (X v)) =
      gder p τ Z' (GlobalTheory.ExportSeries.fockSubst (m := m) p g (X v)) := by
    rintro ⟨σ, i, c⟩
    by_cases hσ : σ = τ
    · subst hσ
      rw [gder_X, hS]
      simp only [if_true]
      by_cases hi : (i : ℕ) < p σ
      · rw [if_pos hi, if_pos hi, map_neg, linS, lin, ← hgi]
        have h1 : ∀ d, GlobalTheory.ExportSeries.fockSubst (m := m) p g (X (σ, i, d)) = ∑ b, C (gi d b) * X (σ, i, b) := by
          intro d; rw [hS, if_pos hi, hgi]
        have h2 : ∀ b, gder (m := m) p σ Z' (X (σ, i, b)) = -∑ e, C (Z' b e) * X (σ, i, e) := by
          intro b; rw [gder_X]; simp only [if_true]; rw [if_pos hi]
        have key : ∀ b, ∑ d, Z c d * gi d b = ∑ d, gi c d * Z' d b := fun b => congrFun (congrFun e1 c) b
        have d1 := dsum (Z c) gi (fun b => X (σ, i, b))
        have d2 := dsum (gi c) Z' (fun b => X (σ, i, b))
        simp only [h1, h2, mul_neg, Finset.sum_neg_distrib] at d1 d2 ⊢
        rw [d1, d2]
        simp only [key]
      · rw [if_neg hi, if_neg hi, linS, lin, ← hg0]
        have h1 : ∀ d, GlobalTheory.ExportSeries.fockSubst (m := m) p g (X (σ, i, d)) = ∑ b, C (g0 b d) * X (σ, i, b) := by
          intro d; rw [hS, if_neg hi, hg0]
        have h2 : ∀ b, gder (m := m) p σ Z' (X (σ, i, b)) = ∑ e, C (Z' e b) * X (σ, i, e) := by
          intro b; rw [gder_X]; simp only [if_true]; rw [if_neg hi]
        have key : ∀ e, ∑ d, Z d c * g0 e d = ∑ b, g0 b c * Z' e b := by
          intro e
          have := congrFun (congrFun e2 e) c
          simp only [Matrix.mul_apply] at this
          rw [Finset.sum_congr rfl (fun d _ => mul_comm (Z d c) (g0 e d)), this]
          exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
        have d1 := dsum (fun d => Z d c) (fun d b => g0 b d) (fun b => X (σ, i, b))
        have d2 := dsum (fun b => g0 b c) (fun b e => Z' e b) (fun b => X (σ, i, b))
        simp only [h1, h2] at d1 d2 ⊢
        rw [d1, d2]
        simp only [key]
    · have h0 : ∀ b, gder (m := m) p τ Z' (X (σ, i, b)) = 0 := by
        intro b; rw [gder_X]; exact if_neg hσ
      rw [gder_X, if_neg hσ, map_zero, hS]
      split_ifs <;> simp only [lin, h0, mul_zero, Finset.sum_const_zero]
  refine LinearMap.ext fun P => ?_
  change GlobalTheory.ExportSeries.fockSubst (m := m) p g (gder p τ Z P) = gder p τ Z' (GlobalTheory.ExportSeries.fockSubst (m := m) p g P)
  induction P using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.derivation_C]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P v hP =>
    rw [Derivation.leibniz, map_mul, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      map_mul, map_mul, hP, hX]

/- English proof (translation)
Set `α : ℂ` to `-2 / 5`. Set `s : ℂ` to `4 / 5`. Set `P : Matrix (Fin n) (Fin n) ℂ` to `Matrix.single a a 1 + Matrix.single b b 1`. Set `J : Matrix (Fin n) (Fin n) ℂ` to `Matrix.single b a 1 - Matrix.single a b 1`. Establish `hba : b ≠ a` using `Ne.symm hab`.

Establish `mm : ∀ (i j k l : Fin n), Matrix.single i j (1 : ℂ) * Matrix.single k l 1 = if j = k then Matrix.single i l 1 else 0`. Introduce `i j k l`. Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using `[Matrix.single_mul_single_same]`.

Use extensionality with `x y`. Simplify using `only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]`. Use `Finset.sum_eq_zero fun t _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases h1 : j = t <;> by_cases h2 : k = t <;> simp_all`. Establish `hGG : (1 + α • P + s • J) * (1 + α • P - s • J) = 1`.

Simplify using `only [P, J, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, mm, hab, hba, if_true, if_false, ↓reduceIte, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, sub_zero, zero_sub, smul_zero]`. Simplify using `only [α, s, zero_mul, mul_zero, add_zero, zero_add, sub_zero, zero_sub, smul_zero, smul_neg, neg_zero]`. Use `module`. Establish `hGG' : (1 + α • P - s • J) * (1 + α • P + s • J) = 1`. Simplify using `only [P, J, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, mm, hab, hba, if_true, if_false, ↓reduceIte, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, sub_zero, zero_sub, smul_zero]`.

Simplify using `only [α, s, zero_mul, mul_zero, add_zero, zero_add, sub_zero, zero_sub, smul_zero, smul_neg, neg_zero]`. Use `module`. Use `⟨⟨1 + α • P + s • J, 1 + α • P - s • J, hGG, hGG'⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff]`. Establish `: star (1 + α • P + s • J) = 1 + α • P - s • J`.

Simplify using `only [P, J, star_add, star_sub, star_smul, star_one, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, star_one]`. Simplify using `only [α, s]`. Establish `h1 : star (-2 / 5 : ℂ) = -2 / 5` using `by simp [Complex.ext_iff]`. Establish `h2 : star (4 / 5 : ℂ) = 4 / 5` using `by simp [Complex.ext_iff]`. Rewrite using `[h1, h2]`.

Use `module`. Rewrite using `[this]`. Conclude with `hGG`. Express the relevant statement in the definitionally equal form `(1 + α • P + s • J) * Matrix.single a a 1 * (1 + α • P - s • J) = _`. Simplify using `only [P, J, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, mm, hab, hba, if_true, if_false, ↓reduceIte]`.

Simplify using `only [α, s, zero_mul, mul_zero, add_zero, zero_add, sub_zero, zero_sub, smul_zero, smul_neg, neg_zero]`. Use `module`.
-/
theorem givens (a b : Fin n) (hab : a ≠ b) : ∃ G : GL (Fin n) ℂ,
    (G : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
    (G : Matrix (Fin n) (Fin n) ℂ) * Matrix.single a a 1 * ((G⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      (9 / 25 : ℂ) • Matrix.single a a 1 + (12 / 25 : ℂ) • (Matrix.single a b 1 + Matrix.single b a 1) +
        (16 / 25 : ℂ) • Matrix.single b b 1 := by
  let α : ℂ := -2 / 5
  let s : ℂ := 4 / 5
  let P : Matrix (Fin n) (Fin n) ℂ := Matrix.single a a 1 + Matrix.single b b 1
  let J : Matrix (Fin n) (Fin n) ℂ := Matrix.single b a 1 - Matrix.single a b 1
  have hba : b ≠ a := Ne.symm hab
  have mm : ∀ (i j k l : Fin n), Matrix.single i j (1 : ℂ) * Matrix.single k l 1 = if j = k then Matrix.single i l 1 else 0 := by
    intro i j k l
    split_ifs with h
    · subst h; simp [Matrix.single_mul_single_same]
    · ext x y
      simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero fun t _ => ?_
      by_cases h1 : j = t <;> by_cases h2 : k = t <;> simp_all
  have hGG : (1 + α • P + s • J) * (1 + α • P - s • J) = 1 := by
    simp only [P, J, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, mm, hab, hba, if_true, if_false, ↓reduceIte, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add, sub_zero, zero_sub, smul_zero]
    simp only [α, s, zero_mul, mul_zero, add_zero, zero_add, sub_zero, zero_sub, smul_zero, smul_neg, neg_zero]
    module
  have hGG' : (1 + α • P - s • J) * (1 + α • P + s • J) = 1 := by
    simp only [P, J, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, mm, hab, hba, if_true, if_false, ↓reduceIte, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add, sub_zero, zero_sub, smul_zero]
    simp only [α, s, zero_mul, mul_zero, add_zero, zero_add, sub_zero, zero_sub, smul_zero, smul_neg, neg_zero]
    module
  refine ⟨⟨1 + α • P + s • J, 1 + α • P - s • J, hGG, hGG'⟩, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    have : star (1 + α • P + s • J) = 1 + α • P - s • J := by
      simp only [P, J, star_add, star_sub, star_smul, star_one, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single,
        star_one]
      simp only [α, s]
      have h1 : star (-2 / 5 : ℂ) = -2 / 5 := by simp [Complex.ext_iff]
      have h2 : star (4 / 5 : ℂ) = 4 / 5 := by simp [Complex.ext_iff]
      rw [h1, h2]
      module
    rw [this]; exact hGG
  · change (1 + α • P + s • J) * Matrix.single a a 1 * (1 + α • P - s • J) = _
    simp only [P, J, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, mm, hab, hba, if_true, if_false, ↓reduceIte]
    simp only [α, s, zero_mul, mul_zero, add_zero, zero_add, sub_zero, zero_sub, smul_zero, smul_neg, neg_zero]
    module

/- English proof (translation)
Establish `h1 : (((dU b (Units.mk0 Complex.I Complex.I_ne_zero))⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (Function.update 1 b (((Units.mk0 Complex.I Complex.I_ne_zero)⁻¹ : ℂˣ) : ℂ))` using `rfl`. Establish `h2 : ((dU b (Units.mk0 Complex.I Complex.I_ne_zero) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (Function.update 1 b Complex.I)` using `rfl`. Rewrite using `[h1, h2]`. Use extensionality with `j k`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul]`.

Simplify using `only [Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, Function.update_apply, Pi.one_apply, Units.val_inv_eq_inv_val, Units.val_mk0, Complex.inv_I]`. Use `clear h1 h2`. Apply the tactic sequence `split_ifs <;> subst_vars <;> simp_all <;> ring`.
-/
theorem dU_conj (a b : Fin n) (hab : a ≠ b) :
    ((dU b (Units.mk0 Complex.I Complex.I_ne_zero) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *
        (Matrix.single a b 1 + Matrix.single b a 1) *
        (((dU b (Units.mk0 Complex.I Complex.I_ne_zero))⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      (-Complex.I) • Matrix.single a b 1 + Complex.I • Matrix.single b a 1 := by
  have h1 : (((dU b (Units.mk0 Complex.I Complex.I_ne_zero))⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      Matrix.diagonal (Function.update 1 b (((Units.mk0 Complex.I Complex.I_ne_zero)⁻¹ : ℂˣ) : ℂ)) := rfl
  have h2 : ((dU b (Units.mk0 Complex.I Complex.I_ne_zero) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      Matrix.diagonal (Function.update 1 b Complex.I) := rfl
  rw [h1, h2]
  ext j k
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, Function.update_apply, Pi.one_apply,
    Units.val_inv_eq_inv_val, Units.val_mk0, Complex.inv_I]
  clear h1 h2
  split_ifs <;> subst_vars <;> simp_all <;> ring

/- English proof (translation)
Use `MvPolynomial.derivation_ext fun v => ?_` and prove the remaining obligations. Rewrite using `[Derivation.add_apply, gder_X, gder_X, gder_X]`. Apply the tactic sequence `split_ifs <;> simp [Finset.sum_add_distrib, add_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gder_add (p : D.what₂.Tau → ℕ) (τ : D.what₂.Tau) (Z Z' : Matrix (Fin n) (Fin n) ℂ) :
    gder (m := m) p τ (Z + Z') = gder p τ Z + gder p τ Z' := by
  refine MvPolynomial.derivation_ext fun v => ?_
  rw [Derivation.add_apply, gder_X, gder_X, gder_X]
  split_ifs <;> simp [Finset.sum_add_distrib, add_mul]
  ring

/- English proof (translation)
Use `MvPolynomial.derivation_ext fun v => ?_` and prove the remaining obligations. Rewrite using `[Derivation.smul_apply, gder_X, gder_X]`. Apply the tactic sequence `split_ifs <;> simp [Finset.smul_sum, smul_eq_C_mul, mul_assoc]`.
-/
theorem gder_smul (p : D.what₂.Tau → ℕ) (τ : D.what₂.Tau) (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    gder (m := m) p τ (c • Z) = c • gder p τ Z := by
  refine MvPolynomial.derivation_ext fun v => ?_
  rw [Derivation.smul_apply, gder_X, gder_X]
  split_ifs <;> simp [Finset.smul_sum, smul_eq_C_mul, mul_assoc]

end

end GlobalTheory.UnitaryToGl

namespace GlobalTheory.UnitaryToGl

open MvPolynomial
open Formalism.IndefR.Links (PolF)
open Classical

noncomputable section

variable {D : D7} {m n : ℕ}

section Frame

variable {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] {w : GlobalTheory.ExportSeries.Weight D n}
  {BS : GlobalTheory.ExportSeries.GLR D n} {r : K →* GlobalTheory.ExportSeries.GLR D n} {ρ : K →* Module.End ℂ W}

/- English proof (translation)
Use `transp_of_pairs hinj hψ fun φ hφ x => ?_` and prove the remaining obligations. Set `f : (Formalism.IndefR.Datum.FVar D m n →₀ ℕ) ⊕ (Formalism.IndefR.Datum.FVar D m n →₀ ℕ) → PolF D m n × PolF D m n` to `Sum.elim (fun s => (monomial s (coeff s (ψ x)), 0)) (fun s => (0, monomial s (coeff s (φ x))))`. Set `wf : (Formalism.IndefR.Datum.FVar D m n →₀ ℕ) ⊕ (Formalism.IndefR.Datum.FVar D m n →₀ ℕ) → ℤ` to `Sum.elim (wt w.p τ c) (wt w.p τ c)`. Establish `hmem : ∑ i ∈ (ψ x).support.disjSum (φ x).support, (wf i : ℂ) • f i ∈ LinearMap.range (ψ.prod φ)`. Use `weighted_mem _ _ wf f fun z hz => ?_` and prove the remaining obligations.

Establish `hz0 : z ≠ 0` using `by rintro rfl; simp at hz`. Take `⟨A, hA⟩` from `transp_subst (m := m) (ρ := ρ) (w := w) hr (isUF_tor τ c (Units.mk0 z hz0) (by simpa using hz))`. Use `⟨A x, ?_⟩` and prove the remaining obligations. Establish `h1` using `LinearMap.congr_fun (hA ψ hψ) x`. Establish `h2` using `LinearMap.congr_fun (hA φ hφ) x`.

Simplify using `only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at h1 h2`. Use `show (ψ (A x), φ (A x)) = _`. Rewrite using `[h1, h2, expand_tor, expand_tor, Finset.sum_disjSum]`. Apply the tactic sequence `ext <;> simp [f, wf, Prod.fst_sum, Prod.snd_sum]`. Take `⟨y, hy⟩` from `hmem`.

Express the relevant statement in the definitionally equal form `(ψ y, φ y) = _ at hy`. Rewrite `hy` using `[Finset.sum_disjSum]`. Use `⟨y, ?_, ?_⟩` and prove the remaining obligations. Use `congrArg Prod.fst hy` as an intermediate fact. Simplify `this` using `[f, wf, Prod.fst_sum, expand_gder]`.

Use `congrArg Prod.snd hy` as an intermediate fact. Simplify `this` using `[f, wf, Prod.snd_sum, expand_gder]`.
-/
theorem transp_torus
    (hr : ∀ g : GlobalTheory.ExportSeries.GLR D n, (∀ τ, ((GlobalTheory.ExportSeries.inBasis BS g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈
      Matrix.unitaryGroup (Fin n) ℂ) → ∃ k, r k = g)
    {ψ : W →ₗ[ℂ] PolF D m n} (hinj : Function.Injective ψ) (hψ : IsEqv w BS r ρ ψ) (τ : D.what₂.Tau) (c : Fin n) :
    Transp w BS r ρ (gder (m := m) w.p τ (Matrix.single c c 1)).toLinearMap := by
  refine transp_of_pairs hinj hψ fun φ hφ x => ?_
  let f : (Formalism.IndefR.Datum.FVar D m n →₀ ℕ) ⊕ (Formalism.IndefR.Datum.FVar D m n →₀ ℕ) → PolF D m n × PolF D m n :=
    Sum.elim (fun s => (monomial s (coeff s (ψ x)), 0)) (fun s => (0, monomial s (coeff s (φ x))))
  let wf : (Formalism.IndefR.Datum.FVar D m n →₀ ℕ) ⊕ (Formalism.IndefR.Datum.FVar D m n →₀ ℕ) → ℤ :=
    Sum.elim (wt w.p τ c) (wt w.p τ c)
  have hmem : ∑ i ∈ (ψ x).support.disjSum (φ x).support, (wf i : ℂ) • f i ∈ LinearMap.range (ψ.prod φ) := by
    refine weighted_mem _ _ wf f fun z hz => ?_
    have hz0 : z ≠ 0 := by rintro rfl; simp at hz
    obtain ⟨A, hA⟩ := transp_subst (m := m) (ρ := ρ) (w := w) hr (isUF_tor τ c (Units.mk0 z hz0) (by simpa using hz))
    refine ⟨A x, ?_⟩
    have h1 := LinearMap.congr_fun (hA ψ hψ) x
    have h2 := LinearMap.congr_fun (hA φ hφ) x
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at h1 h2
    show (ψ (A x), φ (A x)) = _
    rw [h1, h2, expand_tor, expand_tor, Finset.sum_disjSum]
    ext <;> simp [f, wf, Prod.fst_sum, Prod.snd_sum]
  obtain ⟨y, hy⟩ := hmem
  change (ψ y, φ y) = _ at hy
  rw [Finset.sum_disjSum] at hy
  refine ⟨y, ?_, ?_⟩
  · have := congrArg Prod.fst hy
    simpa [f, wf, Prod.fst_sum, expand_gder] using this
  · have := congrArg Prod.snd hy
    simpa [f, wf, Prod.snd_sum, expand_gder] using this

/- English proof (translation)
Establish `key : (gder (m` using `m) w.p τ ((g τ : Matrix (Fin n) (Fin n) ℂ) * Z * (((g τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))).toLinearMap = (GlobalTheory.ExportSeries.fockSubst (m := m) w.p g).toLinearMap * (gder w.p τ Z).toLinearMap * (GlobalTheory.ExportSeries.fockSubst (m := m) w.p g⁻¹).toLinearMa …`. Use `LinearMap.ext fun P => ?_` and prove the remaining obligations. Establish `h1` using `LinearMap.congr_fun (subst_comp_gder (m := m) w.p τ g Z) (GlobalTheory.ExportSeries.fockSubst w.p g⁻¹ P)`. Establish `h2 : GlobalTheory.ExportSeries.fockSubst (m` using `m) w.p g (GlobalTheory.ExportSeries.fockSubst w.p g⁻¹ P) = P := by`. Rewrite using `[← AlgHom.comp_apply, ← GlobalTheory.ExportSeries.fockSubst_mul, mul_inv_cancel, GlobalTheory.ExportSeries.fockSubst_one]`.

Both sides reduce to the same expression. Simplify using `only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, h2] at h1`. Simplify using `only [Module.End.mul_apply, AlgHom.toLinearMap_apply]`. Conclude with `h1.symm`. Rewrite using `[key]`.

Conclude with `transp_mul (transp_mul (transp_subst hr hg) h) (transp_subst hr (isUF_inv hg))`.
-/
theorem transp_conj
    (hr : ∀ g : GlobalTheory.ExportSeries.GLR D n, (∀ τ, ((GlobalTheory.ExportSeries.inBasis BS g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈
      Matrix.unitaryGroup (Fin n) ℂ) → ∃ k, r k = g)
    (τ : D.what₂.Tau) {g : GlobalTheory.ExportSeries.GLR D n} (hg : IsUF g) {Z : Matrix (Fin n) (Fin n) ℂ}
    (h : Transp w BS r ρ (gder (m := m) w.p τ Z).toLinearMap) :
    Transp w BS r ρ (gder (m := m) w.p τ ((g τ : Matrix (Fin n) (Fin n) ℂ) * Z *
      (((g τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))).toLinearMap := by
  have key : (gder (m := m) w.p τ ((g τ : Matrix (Fin n) (Fin n) ℂ) * Z *
      (((g τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))).toLinearMap =
      (GlobalTheory.ExportSeries.fockSubst (m := m) w.p g).toLinearMap * (gder w.p τ Z).toLinearMap *
        (GlobalTheory.ExportSeries.fockSubst (m := m) w.p g⁻¹).toLinearMap := by
    refine LinearMap.ext fun P => ?_
    have h1 := LinearMap.congr_fun (subst_comp_gder (m := m) w.p τ g Z) (GlobalTheory.ExportSeries.fockSubst w.p g⁻¹ P)
    have h2 : GlobalTheory.ExportSeries.fockSubst (m := m) w.p g (GlobalTheory.ExportSeries.fockSubst w.p g⁻¹ P) = P := by
      rw [← AlgHom.comp_apply, ← GlobalTheory.ExportSeries.fockSubst_mul, mul_inv_cancel, GlobalTheory.ExportSeries.fockSubst_one]; rfl
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, h2] at h1
    simp only [Module.End.mul_apply, AlgHom.toLinearMap_apply]
    exact h1.symm
  rw [key]
  exact transp_mul (transp_mul (transp_subst hr hg) h) (transp_subst hr (isUF_inv hg))

def sp (w : GlobalTheory.ExportSeries.Weight D n) (BS : GlobalTheory.ExportSeries.GLR D n) (r : K →* GlobalTheory.ExportSeries.GLR D n)
    (ρ : K →* Module.End ℂ W) (m : ℕ) (τ : D.what₂.Tau) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {Z | Transp w BS r ρ (gder (m := m) w.p τ Z).toLinearMap}
  add_mem' {Z Z'} h h' := by
    simp only [Set.mem_setOf_eq, gder_add] at h h' ⊢
    exact transp_add h h'
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    have : gder (m := m) w.p τ (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
      simpa using gder_smul (m := m) w.p τ 0 (0 : Matrix (Fin n) (Fin n) ℂ)
    rw [this]
    exact transp_zero
  smul_mem' c {Z} h := by
    simp only [Set.mem_setOf_eq, gder_smul] at h ⊢
    exact transp_smul c h

end Frame

/- English proof (translation)
Introduce `D n m w BS K _ r hr W _ _ _ ρ ψ hinj hψ τ a b`. Establish `hψ' : IsEqv w BS r ρ ψ` using `hψ`. Set `S` to `sp w BS r ρ m τ`. Establish `hdiag : ∀ c, Matrix.single c c (1 : ℂ) ∈ S` using `fun c => transp_torus hr hinj hψ' τ c`. Establish `hconj : ∀ (G : GL (Fin n) ℂ), (G : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ → ∀ Z ∈ S, (G : Matrix (Fin n) (Fin n) ℂ) * Z * ((G⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ S`.

Introduce `G hG Z hZ`. Use `transp_conj (m := m) (w := w) (ρ := ρ) hr τ (isUF_update τ G hG) hZ` as an intermediate fact. Simplify using `only [Function.update_self] at this`. Conclude with `this`. Establish `hall : ∀ a b : Fin n, Matrix.single a b (1 : ℂ) ∈ S`.

Introduce `a b`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Conclude with `hdiag a`. Take `⟨G, hG, hGe⟩` from `givens a b hab`.

Establish `hQ1 : Matrix.single a b (1 : ℂ) + Matrix.single b a 1 ∈ S`. Establish `h1` using `hconj G hG _ (hdiag a)`. Rewrite `h1` using `[hGe]`. Establish `e : Matrix.single a b (1 : ℂ) + Matrix.single b a 1 = (25 / 12 : ℂ) • (((9 / 25 : ℂ) • Matrix.single a a 1 + (12 / 25 : ℂ) • (Matrix.single a b 1 + Matrix.single b a 1) + (16 / 25 : ℂ) • Matrix.single b b 1) - (9 / 25 : ℂ) • Matrix.single a a 1 - (16 / 25 : ℂ) • Matrix.single b b …` using `by module`. Rewrite using `[e]`.

Conclude with `S.smul_mem _ (S.sub_mem (S.sub_mem h1 (S.smul_mem _ (hdiag a))) (S.smul_mem _ (hdiag b)))`. Establish `hQ2 : (-Complex.I) • Matrix.single a b (1 : ℂ) + Complex.I • Matrix.single b a 1 ∈ S`. Establish `h2` using `hconj _ (dU_mem b (Units.mk0 Complex.I Complex.I_ne_zero) (by simp)) _ hQ1`. Rewrite `h2` using `[dU_conj a b hab]`. Then use the resulting hypothesis. Establish `e : Matrix.single a b (1 : ℂ) = (1 / 2 : ℂ) • ((Matrix.single a b 1 + Matrix.single b a 1) + Complex.I • ((-Complex.I) • Matrix.single a b 1 + Complex.I • Matrix.single b a 1))`.

Rewrite using `[smul_add Complex.I, smul_smul, smul_smul, mul_neg, Complex.I_mul_I, neg_neg]`. Use `module`. Rewrite using `[e]`. Conclude with `S.smul_mem _ (S.add_mem hQ1 (S.smul_mem _ hQ2))`. Establish `hT : Transp w BS r ρ (GlobalTheory.LowestKType.sop (m` using `m) w τ a b) := by`.

Rewrite using `[sop_eq, ← neg_one_smul ℂ (gder w.p τ (Matrix.single b a 1)).toLinearMap]`. Conclude with `transp_add (transp_smul _ (hall b a)) (transp_smul _ transp_one)`. Take `⟨A, hA⟩` from `hT`. Conclude with `⟨A, fun φ hφ => hA φ hφ⟩`.
-/
theorem exists_transport_sop : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (BS : GlobalTheory.ExportSeries.GLR D n) (K : Type) [Group K] (r : K →* GlobalTheory.ExportSeries.GLR D n), (∀ g : GlobalTheory.ExportSeries.GLR D n, (∀ τ, ((GlobalTheory.ExportSeries.inBasis BS g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∃ k, r k = g) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : K →* Module.End ℂ W) (ψ : W →ₗ[ℂ] PolF D m n), Function.Injective ψ → (∀ (k : K) (x : W), ψ (ρ k x) = GlobalTheory.ExportSeries.fockGL m w BS (r k) (ψ x)) → ∀ (τ : D.what₂.Tau) (a b : Fin n), ∃ A : Module.End ℂ W, ∀ φ : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (x : W), φ (ρ k x) = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ x)) → φ ∘ₗ A = GlobalTheory.LowestKType.sop w τ a b ∘ₗ φ := by
  intro D n m w BS K _ r hr W _ _ _ ρ ψ hinj hψ τ a b
  have hψ' : IsEqv w BS r ρ ψ := hψ
  let S := sp w BS r ρ m τ
  have hdiag : ∀ c, Matrix.single c c (1 : ℂ) ∈ S := fun c => transp_torus hr hinj hψ' τ c
  have hconj : ∀ (G : GL (Fin n) ℂ), (G : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ →
      ∀ Z ∈ S, (G : Matrix (Fin n) (Fin n) ℂ) * Z * ((G⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ S := by
    intro G hG Z hZ
    have := transp_conj (m := m) (w := w) (ρ := ρ) hr τ (isUF_update τ G hG) hZ
    simp only [Function.update_self] at this
    exact this
  have hall : ∀ a b : Fin n, Matrix.single a b (1 : ℂ) ∈ S := by
    intro a b
    by_cases hab : a = b
    · subst hab; exact hdiag a
    obtain ⟨G, hG, hGe⟩ := givens a b hab
    have hQ1 : Matrix.single a b (1 : ℂ) + Matrix.single b a 1 ∈ S := by
      have h1 := hconj G hG _ (hdiag a)
      rw [hGe] at h1
      have e : Matrix.single a b (1 : ℂ) + Matrix.single b a 1 = (25 / 12 : ℂ) • (((9 / 25 : ℂ) • Matrix.single a a 1 +
          (12 / 25 : ℂ) • (Matrix.single a b 1 + Matrix.single b a 1) + (16 / 25 : ℂ) • Matrix.single b b 1) -
          (9 / 25 : ℂ) • Matrix.single a a 1 - (16 / 25 : ℂ) • Matrix.single b b 1) := by
        module
      rw [e]
      exact S.smul_mem _ (S.sub_mem (S.sub_mem h1 (S.smul_mem _ (hdiag a))) (S.smul_mem _ (hdiag b)))
    have hQ2 : (-Complex.I) • Matrix.single a b (1 : ℂ) + Complex.I • Matrix.single b a 1 ∈ S := by
      have h2 := hconj _ (dU_mem b (Units.mk0 Complex.I Complex.I_ne_zero) (by simp)) _ hQ1
      rwa [dU_conj a b hab] at h2
    have e : Matrix.single a b (1 : ℂ) = (1 / 2 : ℂ) • ((Matrix.single a b 1 + Matrix.single b a 1) +
        Complex.I • ((-Complex.I) • Matrix.single a b 1 + Complex.I • Matrix.single b a 1)) := by
      rw [smul_add Complex.I, smul_smul, smul_smul, mul_neg, Complex.I_mul_I, neg_neg]
      module
    rw [e]
    exact S.smul_mem _ (S.add_mem hQ1 (S.smul_mem _ hQ2))
  have hT : Transp w BS r ρ (GlobalTheory.LowestKType.sop (m := m) w τ a b) := by
    rw [sop_eq, ← neg_one_smul ℂ (gder w.p τ (Matrix.single b a 1)).toLinearMap]
    exact transp_add (transp_smul _ (hall b a)) (transp_smul _ transp_one)
  obtain ⟨A, hA⟩ := hT
  exact ⟨A, fun φ hφ => hA φ hφ⟩

end

end GlobalTheory.UnitaryToGl
