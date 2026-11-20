import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeSqrtMulSum

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveCp GlobalTheory.CompanionTheory.WaveCp.Rep
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveCp.Rep.Mol

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

def Dm (n : ℕ) : Set (Mat n × Mat n) := GLs n ×ˢ GLs n

def Ldp (X : Mat n) (K : Mat n × Mat n → V) : Mat n × Mat n → V := fun p => fderiv ℝ K p (0, X * p.2)

def Hw (w : List (Bool × Fin n × Fin n)) (K : Mat n × Mat n → V) : Mat n × Mat n → V :=
  w.foldr (fun p h => Ldp (bs p) h) K

def Hf (f : Mat n → V) : Mat n × Mat n → V := fun p => f (p.1⁻¹ * p.2)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem Hw_nil (K : Mat n × Mat n → V) : Hw [] K = K := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Hw_cons (p : Bool × Fin n × Fin n) (w : List (Bool × Fin n × Fin n)) (K : Mat n × Mat n → V) :
    Hw (p :: w) K = Ldp (bs p) (Hw w K) := rfl

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.prod GlobalTheory.CompanionTheory.RCalc.isOpen_GLs`.
-/
theorem isOpen_Dm : IsOpen (Dm n) := GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.prod GlobalTheory.CompanionTheory.RCalc.isOpen_GLs

def fld (X : Mat n) : (Mat n × Mat n) →L[ℝ] (Mat n × Mat n) :=
  (ContinuousLinearMap.inr ℝ (Mat n) (Mat n)).comp ((GlobalTheory.CompanionTheory.RCalc.mulL X).comp (ContinuousLinearMap.snd ℝ (Mat n) (Mat n)))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fld_apply (X : Mat n) (p : Mat n × Mat n) : fld X p = (0, X * p.2) := rfl

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.RCalc.contDiffOn_fderiv_field isOpen_Dm hK (fld X)`.
-/
theorem Ldp_contDiffOn (X : Mat n) {K : Mat n × Mat n → V} (hK : ContDiffOn ℝ ∞ K (Dm n)) :
    ContDiffOn ℝ ∞ (Ldp X K) (Dm n) :=
  GlobalTheory.CompanionTheory.RCalc.contDiffOn_fderiv_field isOpen_Dm hK (fld X)

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => simpa using hK`. Consider the case `cons p w ih => rw [Hw_cons]`. Conclude with `Ldp_contDiffOn _ ih`.
-/
theorem Hw_contDiffOn (w : List (Bool × Fin n × Fin n)) {K : Mat n × Mat n → V} (hK : ContDiffOn ℝ ∞ K (Dm n)) :
    ContDiffOn ℝ ∞ (Hw w K) (Dm n) := by
  induction w with
  | nil => simpa using hK
  | cons p w ih => rw [Hw_cons]; exact Ldp_contDiffOn _ ih

/- English proof (translation)
Establish `: (fun y : G n => f y.val) = fun y => h y.val` using `funext fun y => e (GlobalTheory.CompanionTheory.KerUniq.val_mem y)`. Distinguish the cases in `hm : MemLp (fun y : G n => f y.val) 2 μ`. Conclude with `(isRep_toL (isRep_congr e (toL_coe hm))).symm`. Establish `hm' : ¬ MemLp (fun y : G n => h y.val) 2 μ` using `this ▸ hm`. Unfold `toL`.

Rewrite using `[dif_neg hm, dif_neg hm']`.
-/
theorem toL_congr {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [MeasurableSpace (G n)]
    (μ : Measure (G n)) {f h : Mat n → V} (e : Set.EqOn f h (GLs n)) : toL μ f = toL μ h := by
  have : (fun y : G n => f y.val) = fun y => h y.val := funext fun y => e (GlobalTheory.CompanionTheory.KerUniq.val_mem y)
  by_cases hm : MemLp (fun y : G n => f y.val) 2 μ
  · exact (isRep_toL (isRep_congr e (toL_coe hm))).symm
  · have hm' : ¬ MemLp (fun y : G n => h y.val) 2 μ := this ▸ hm
    unfold toL
    rw [dif_neg hm, dif_neg hm']

/- English proof (translation)
Take `⟨h1, h2⟩` from `hu n μ`. Set `u : G n` to `Matrix.GeneralLinearGroup.mkOfDetNeZero x hx`. Establish `hu' : u.val = x` using `rfl`. Set `F : G n → V` to `fun z => φ (x * (z⁻¹ : G n).val) • f z.val`. Establish `e1 : cvl μ φ (toL μ f) x = ∫ z, F z ∂μ`.

Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [toL_coe hf] with z hz`. Simplify using `only [F]`. Rewrite using `[hz]`. Establish `e2 : ∫ z, F z ∂μ = ∫ z, F (z⁻¹ * u) ∂μ`.

Rewrite using `[integral_inv_eq_self (fun z => F (z * u)) μ, integral_mul_right_eq_self F u]`. Rewrite using `[e1, e2]`. Use `integral_congr_ae (Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Establish `e3 : x * ((z⁻¹ * u)⁻¹ : G n).val = z.val`. Establish `e4 : (z⁻¹ * u)⁻¹ = u⁻¹ * z` using `by group`.

Rewrite using `[e4, Units.val_mul, ← mul_assoc]`. Establish `e5 : x * (u⁻¹ : G n).val = 1` using `by rw [← hu']; exact Units.mul_inv u`. Rewrite using `[e5, one_mul]`. Use `show φ (x * ((z⁻¹ * u)⁻¹ : G n).val) • f (z⁻¹ * u).val = φ z.val • f (z.val⁻¹ * x)`. Rewrite using `[e3]`.

Simplify using `[hu', Matrix.coe_units_inv]`.
-/
theorem cvl_eq (hu : Unimod) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (φ : Mat n → ℂ) {f : Mat n → V}
    (hf : MemLp (fun y : G n => f y.val) 2 μ) {x : Mat n} (hx : x ∈ GLs n) :
    cvl μ φ (toL μ f) x = ∫ z : G n, φ z.val • Hf f (z.val, x) ∂μ := by
  obtain ⟨h1, h2⟩ := hu n μ
  let u : G n := Matrix.GeneralLinearGroup.mkOfDetNeZero x hx
  have hu' : u.val = x := rfl
  let F : G n → V := fun z => φ (x * (z⁻¹ : G n).val) • f z.val
  have e1 : cvl μ φ (toL μ f) x = ∫ z, F z ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [toL_coe hf] with z hz
    simp only [F]
    rw [hz]
  have e2 : ∫ z, F z ∂μ = ∫ z, F (z⁻¹ * u) ∂μ := by
    rw [integral_inv_eq_self (fun z => F (z * u)) μ, integral_mul_right_eq_self F u]
  rw [e1, e2]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  have e3 : x * ((z⁻¹ * u)⁻¹ : G n).val = z.val := by
    have e4 : (z⁻¹ * u)⁻¹ = u⁻¹ * z := by group
    rw [e4, Units.val_mul, ← mul_assoc]
    have e5 : x * (u⁻¹ : G n).val = 1 := by rw [← hu']; exact Units.mul_inv u
    rw [e5, one_mul]
  show φ (x * ((z⁻¹ * u)⁻¹ : G n).val) • f (z⁻¹ * u).val = φ z.val • f (z.val⁻¹ * x)
  rw [e3]
  simp [hu', Matrix.coe_units_inv]

end GlobalTheory.CompanionTheory.WaveCp.Rep.Mol
