import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXSig
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXUni
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RowsBij

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf Formalism.MainNotions.S

section Coords

variable {m : ℕ}

def realifyE (X : Matrix (Fin m) (Fin m) ℂ) : EuclideanSpace ℝ (Fin m × Fin m × Bool) :=
  (WithLp.equiv 2 _).symm (realifyFun X)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem realifyE_apply (X : Matrix (Fin m) (Fin m) ℂ) (p : Fin m × Fin m × Bool) :
    (realifyE X).ofLp p = realifyFun X p := rfl

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Apply `Complex.ext` to reduce the goal to its premises. Apply the tactic sequence `first | rfl | simp [unrealify, realifyE, realifyFun]`. Apply the tactic sequence `first | rfl | simp [unrealify, realifyE, realifyFun]`.
-/
theorem unrealify_realifyE (X : Matrix (Fin m) (Fin m) ℂ) : unrealify (realifyE X) = X := by
  funext i j
  apply Complex.ext
  · first | rfl | simp [unrealify, realifyE, realifyFun]
  · first | rfl | simp [unrealify, realifyE, realifyFun]

/- English proof (translation)
Use `PiLp.ext fun p => ?_` and prove the remaining obligations. Take `⟨i, j, b⟩` from `p`. Consider the cases of `b`. Apply the tactic sequence `first | rfl | simp [unrealify, realifyE, realifyFun]`. Apply the tactic sequence `first | rfl | simp [unrealify, realifyE, realifyFun]`.
-/
theorem realifyE_unrealify (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : realifyE (unrealify x) = x := by
  refine PiLp.ext fun p => ?_
  obtain ⟨i, j, b⟩ := p
  cases b
  · first | rfl | simp [unrealify, realifyE, realifyFun]
  · first | rfl | simp [unrealify, realifyE, realifyFun]

/- English proof (translation)
Use `PiLp.ext fun p => ?_` and prove the remaining obligations. Take `⟨i, j, b⟩` from `p`. Apply the tactic sequence `cases b <;> simp [realifyE, realifyFun]`.
-/
theorem realifyE_add (X Y : Matrix (Fin m) (Fin m) ℂ) : realifyE (X + Y) = realifyE X + realifyE Y := by
  refine PiLp.ext fun p => ?_
  obtain ⟨i, j, b⟩ := p
  cases b <;> simp [realifyE, realifyFun]

/- English proof (translation)
Use `PiLp.ext fun p => ?_` and prove the remaining obligations. Take `⟨i, j, b⟩` from `p`. Apply the tactic sequence `cases b <;> simp [realifyE, realifyFun]`.
-/
theorem realifyE_smul (c : ℝ) (X : Matrix (Fin m) (Fin m) ℂ) : realifyE (c • X) = c • realifyE X := by
  refine PiLp.ext fun p => ?_
  obtain ⟨i, j, b⟩ := p
  cases b <;> simp [realifyE, realifyFun]

/- English proof (translation)
Rewrite using `[← realifyE_unrealify x, ← realifyE_unrealify y, ← realifyE_add, unrealify_realifyE, unrealify_realifyE, unrealify_realifyE]`.
-/
theorem unrealify_add (x y : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (x + y) = unrealify x + unrealify y := by
  rw [← realifyE_unrealify x, ← realifyE_unrealify y, ← realifyE_add, unrealify_realifyE, unrealify_realifyE,
    unrealify_realifyE]

/- English proof (translation)
Rewrite using `[← realifyE_unrealify x, ← realifyE_smul, unrealify_realifyE, unrealify_realifyE]`.
-/
theorem unrealify_smul (c : ℝ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (c • x) = c • unrealify x := by
  rw [← realifyE_unrealify x, ← realifyE_smul, unrealify_realifyE, unrealify_realifyE]

def adE (A B : Matrix (Fin m) (Fin m) ℂ) :
    EuclideanSpace ℝ (Fin m × Fin m × Bool) →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) where
  toFun x := realifyE (A * unrealify x * B)
  map_add' x y := by simp only [unrealify_add, Matrix.mul_add, Matrix.add_mul, realifyE_add]
  map_smul' c x := by
    simp only [unrealify_smul, Matrix.mul_smul, Matrix.smul_mul, realifyE_smul, RingHom.id_apply]

/- English proof (translation)
The claim follows from `unrealify_realifyE _`.
-/
theorem unrealify_adE (A B : Matrix (Fin m) (Fin m) ℂ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (adE A B x) = A * unrealify x * B := unrealify_realifyE _

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]`. Simplify using `only [Fintype.sum_prod_type, Fintype.sum_bool, trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [realifyE_apply, realifyFun, if_true, Bool.false_eq_true, if_false, Real.norm_eq_abs, sq_abs, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_sq_realifyE (Y : Matrix (Fin m) (Fin m) ℂ) : ‖realifyE Y‖ ^ 2 = (trace (Yᴴ * Y)).re := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [realifyE_apply, realifyFun, if_true, Bool.false_eq_true, if_false, Real.norm_eq_abs, sq_abs,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/- English proof (translation)
Establish `hsq : ‖adE Pᴴ P x‖ ^ 2 = ‖x‖ ^ 2` using `by show ‖realifyE (Pᴴ * unrealify x * P)‖ ^ 2 = ‖x‖ ^ 2 conv_rhs => rw [← realifyE_unrealify x]`. Rewrite using `[norm_sq_realifyE, norm_sq_realifyE]`. Use `congr 1`. Establish `e : (Pᴴ * unrealify x * P)ᴴ * (Pᴴ * unrealify x * P) = Pᴴ * ((unrealify x)ᴴ * unrealify x) * P`. Simplify using `only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc P Pᴴ, h2, Matrix.one_mul]`. Rewrite using `[e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]`. Rewrite using `[← Real.sqrt_sq (norm_nonneg (adE Pᴴ P x)), hsq, Real.sqrt_sq (norm_nonneg x)]`.
-/
theorem norm_adE {P : Matrix (Fin m) (Fin m) ℂ} (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1)
    (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : ‖adE Pᴴ P x‖ = ‖x‖ := by
  have hsq : ‖adE Pᴴ P x‖ ^ 2 = ‖x‖ ^ 2 := by
    show ‖realifyE (Pᴴ * unrealify x * P)‖ ^ 2 = ‖x‖ ^ 2
    conv_rhs => rw [← realifyE_unrealify x]
    rw [norm_sq_realifyE, norm_sq_realifyE]
    congr 1
    have e : (Pᴴ * unrealify x * P)ᴴ * (Pᴴ * unrealify x * P) = Pᴴ * ((unrealify x)ᴴ * unrealify x) * P := by
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P Pᴴ, h2, Matrix.one_mul]
    rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  rw [← Real.sqrt_sq (norm_nonneg (adE Pᴴ P x)), hsq, Real.sqrt_sq (norm_nonneg x)]

def adLE (P : Matrix (Fin m) (Fin m) ℂ) (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1) :
    EuclideanSpace ℝ (Fin m × Fin m × Bool) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) where
  toFun := adE Pᴴ P
  invFun := adE P Pᴴ
  map_add' := (adE Pᴴ P).map_add
  map_smul' := (adE Pᴴ P).map_smul
  left_inv x := by
    show realifyE (P * unrealify (realifyE (Pᴴ * unrealify x * P)) * Pᴴ) = x
    rw [unrealify_realifyE]
    simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
    rw [Matrix.mul_assoc _ P Pᴴ, h2, Matrix.mul_one, realifyE_unrealify]
  right_inv x := by
    show realifyE (Pᴴ * unrealify (realifyE (P * unrealify x * Pᴴ)) * P) = x
    rw [unrealify_realifyE]
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc _ Pᴴ P, h1, Matrix.mul_one, realifyE_unrealify]

def adIso (P : Matrix (Fin m) (Fin m) ℂ) (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1) :
    EuclideanSpace ℝ (Fin m × Fin m × Bool) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) :=
  ⟨adLE P h1 h2, norm_adE h1 h2⟩

end Coords

section Lie

variable {r k : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

/- English proof (translation)
Rewrite using `[← hPJ]`. Simplify using `only [← Matrix.mul_assoc, h2, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, h2, Matrix.mul_one]`.
-/
theorem PHP (hPJ : Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r) (h2 : P * Pᴴ = 1) :
    P * Hpk k r * Pᴴ = Formalism.REAL.Jm ε := by
  rw [← hPJ]
  simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
  rw [Matrix.mul_assoc, h2, Matrix.mul_one]

/- English proof (translation)
Establish `key : (Pᴴ * g * P)ᴴ * Hpk k r * (Pᴴ * g * P) = Pᴴ * (gᴴ * Formalism.REAL.Jm ε * g) * P`. Simplify using `only [conjTranspose_mul, conjTranspose_conjTranspose]`. Rewrite using `[← PHP hPJ h2]`. Simplify using `only [Matrix.mul_assoc]`. Use `show (Pᴴ * g * P)ᴴ * Hpk k r * (Pᴴ * g * P) = Hpk k r ↔ gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε`.

Rewrite using `[key]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h'` using `congrArg (fun M => P * M * Pᴴ) h`. Establish `eL : P * (Pᴴ * (gᴴ * Formalism.REAL.Jm ε * g) * P) * Pᴴ = gᴴ * Formalism.REAL.Jm ε * g`.

Simplify using `only [← Matrix.mul_assoc, h2, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc _ P Pᴴ, h2, Matrix.mul_one]`. Conclude with `eL.symm.trans (h'.trans (PHP hPJ h2))`. Introduce `h`. Rewrite using `[h, hPJ]`.
-/
theorem conj_UH_iff (hPJ : Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r) (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Pᴴ * g * P ∈ UH (Hpk k r) ↔ Formalism.REAL.inUJ ε g := by
  have key : (Pᴴ * g * P)ᴴ * Hpk k r * (Pᴴ * g * P) = Pᴴ * (gᴴ * Formalism.REAL.Jm ε * g) * P := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose]
    rw [← PHP hPJ h2]
    simp only [Matrix.mul_assoc]
  show (Pᴴ * g * P)ᴴ * Hpk k r * (Pᴴ * g * P) = Hpk k r ↔ gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
  rw [key]
  constructor
  · intro h
    have h' := congrArg (fun M => P * M * Pᴴ) h
    have eL : P * (Pᴴ * (gᴴ * Formalism.REAL.Jm ε * g) * P) * Pᴴ = gᴴ * Formalism.REAL.Jm ε * g := by
      simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
      rw [Matrix.mul_assoc _ P Pᴴ, h2, Matrix.mul_one]
    exact eL.symm.trans (h'.trans (PHP hPJ h2))
  · intro h
    rw [h, hPJ]

/- English proof (translation)
The claim follows from `(Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse h1)`.
-/
theorem isUnit_PH (h1 : Pᴴ * P = 1) : IsUnit Pᴴ :=
  (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse h1)

/- English proof (translation)
The claim follows from `Matrix.inv_eq_right_inv h1`.
-/
theorem inv_PH (h1 : Pᴴ * P = 1) : (Pᴴ)⁻¹ = P := Matrix.inv_eq_right_inv h1

/- English proof (translation)
Use `Matrix.exp_conj Pᴴ X (isUnit_PH h1)` as an intermediate fact. Rewrite `this` using `[inv_PH h1]`. Then use the resulting hypothesis.
-/
theorem exp_conjP (h1 : Pᴴ * P = 1) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    NormedSpace.exp (Pᴴ * X * P) = Pᴴ * NormedSpace.exp X * P := by
  have := Matrix.exp_conj Pᴴ X (isUnit_PH h1)
  rwa [inv_PH h1] at this

/- English proof (translation)
Simplify using `only [lieOf, Set.mem_setOf_eq]`. Use `forall_congr' fun t => ?_` and prove the remaining obligations. Rewrite using `[show ((t : ℂ) • (Pᴴ * X * P)) = Pᴴ * ((t : ℂ) • X) * P by rw [Matrix.mul_smul, Matrix.smul_mul], exp_conjP h1, conj_UH_iff hPJ h1 h2]`.
-/
theorem lieOf_conj (hPJ : Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r) (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1)
    (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Pᴴ * X * P ∈ lieOf (UH (Hpk k r)) ↔ X ∈ lieOf {g | Formalism.REAL.inUJ ε g} := by
  simp only [lieOf, Set.mem_setOf_eq]
  refine forall_congr' fun t => ?_
  rw [show ((t : ℂ) • (Pᴴ * X * P)) = Pᴴ * ((t : ℂ) • X) * P by rw [Matrix.mul_smul, Matrix.smul_mul],
    exp_conjP h1, conj_UH_iff hPJ h1 h2]

/- English proof (translation)
Use `show Submodule.map _ (Submodule.span ℝ _) = Submodule.span ℝ _`. Rewrite using `[Submodule.map_span]`. Use `congr 1`. Use extensionality with `y`. Simplify using `only [Set.mem_image]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, ⟨X, hX, rfl⟩, rfl⟩`. Use `⟨Pᴴ * X * P, (lieOf_conj hPJ h1 h2 X).2 hX, ?_⟩` and prove the remaining obligations. Use `show realifyE (Pᴴ * X * P) = realifyE (Pᴴ * unrealify (realifyE X) * P)`. Rewrite using `[unrealify_realifyE]`.

Introduce and unpack `⟨Y, hY, rfl⟩`. Use `⟨realifyE (P * Y * Pᴴ), ⟨P * Y * Pᴴ, (lieOf_conj hPJ h1 h2 _).1 ?_, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `: Pᴴ * (P * Y * Pᴴ) * P = Y`. Simplify using `only [← Matrix.mul_assoc, h1, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, h1, Matrix.mul_one]`.

Rewrite using `[this]`. Conclude with `hY`. Use `show realifyE (Pᴴ * unrealify (realifyE (P * Y * Pᴴ)) * P) = realifyE Y`. Rewrite using `[unrealify_realifyE]`. Simplify using `only [← Matrix.mul_assoc, h1, Matrix.one_mul]`.

Rewrite using `[Matrix.mul_assoc, h1, Matrix.mul_one]`.
-/
theorem map_lieE (hPJ : Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r) (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1) :
    Submodule.map ((adIso P h1 h2 : _ ≃ₗᵢ[ℝ] _).toLinearEquiv.toLinearMap) (Formalism.MainNotions.S.Gauge.gLie ε) =
      lieE (UH (Hpk k r)) := by
  show Submodule.map _ (Submodule.span ℝ _) = Submodule.span ℝ _
  rw [Submodule.map_span]
  congr 1
  ext y
  simp only [Set.mem_image]
  constructor
  · rintro ⟨x, ⟨X, hX, rfl⟩, rfl⟩
    refine ⟨Pᴴ * X * P, (lieOf_conj hPJ h1 h2 X).2 hX, ?_⟩
    show realifyE (Pᴴ * X * P) = realifyE (Pᴴ * unrealify (realifyE X) * P)
    rw [unrealify_realifyE]
  · rintro ⟨Y, hY, rfl⟩
    refine ⟨realifyE (P * Y * Pᴴ), ⟨P * Y * Pᴴ, (lieOf_conj hPJ h1 h2 _).1 ?_, rfl⟩, ?_⟩
    · have : Pᴴ * (P * Y * Pᴴ) * P = Y := by
        simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]; rw [Matrix.mul_assoc, h1, Matrix.mul_one]
      rw [this]; exact hY
    · show realifyE (Pᴴ * unrealify (realifyE (P * Y * Pᴴ)) * P) = realifyE Y
      rw [unrealify_realifyE]
      simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]; rw [Matrix.mul_assoc, h1, Matrix.mul_one]

def lieIso (hPJ : Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r) (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1) :
    Formalism.MainNotions.S.Gauge.gLie ε ≃ₗᵢ[ℝ] lieE (UH (Hpk k r)) :=
  (LinearIsometryEquiv.submoduleMap (Formalism.MainNotions.S.Gauge.gLie ε) (adIso P h1 h2)).trans
    (LinearIsometryEquiv.ofEq _ _ (map_lieE hPJ h1 h2))

/- English proof (translation)
Use `show unrealify (adE Pᴴ P (y : EuclideanSpace ℝ _)) = _`. Conclude with `unrealify_adE _ _ _`.
-/
theorem unrealify_lieIso (hPJ : Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r) (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1)
    (y : Formalism.MainNotions.S.Gauge.gLie ε) :
    unrealify ((lieIso hPJ h1 h2 y : lieE (UH (Hpk k r))) : EuclideanSpace ℝ _) =
      Pᴴ * unrealify (y : EuclideanSpace ℝ _) * P := by
  show unrealify (adE Pᴴ P (y : EuclideanSpace ℝ _)) = _
  exact unrealify_adE _ _ _

end Lie

section Gauge

variable {r k : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

/- English proof (translation)
Establish `hfin : ∀ i, (c • μ) (spanningSets μ i) < ⊤` using `fun i => by`. Rewrite using `[Measure.smul_apply, smul_eq_mul]`. Conclude with `ENNReal.mul_lt_top hc.lt_top (measure_spanningSets_lt_top μ i)`. Conclude with `⟨⟨⟨spanningSets μ, fun _ => trivial, hfin, iUnion_spanningSets μ⟩⟩⟩`.
-/
theorem sigmaFinite_smul' {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] {c : ℝ≥0∞}
    (hc : c ≠ ⊤) : SigmaFinite (c • μ) := by
  have hfin : ∀ i, (c • μ) (spanningSets μ i) < ⊤ := fun i => by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hc.lt_top (measure_spanningSets_lt_top μ i)
  exact ⟨⟨⟨spanningSets μ, fun _ => trivial, hfin, iUnion_spanningSets μ⟩⟩⟩

/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `h`. Use `⟨sigmaFinite_smul' ν hc, ?_, ?_, fun s hs => ?_⟩` and prove the remaining obligations. Introduce `h0`. Use `congrArg (fun μ : Measure (Mt k r) => μ Set.univ) h0` as an intermediate fact. Simplify using `only [Measure.smul_apply, smul_eq_mul, Measure.coe_zero, Pi.zero_apply, mul_eq_zero, hc0, false_or] at this`.

Conclude with `h2 (Measure.measure_univ_eq_zero.1 this)`. Rewrite using `[Measure.smul_apply, h3, smul_zero]`. Rewrite using `[Measure.map_smul, h4 s hs]`.
-/
theorem isHaarOn_smul {S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)} {ν : Measure (Mt k r)}
    (h : IsHaarOn S ν) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ⊤) : IsHaarOn S (c • ν) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨sigmaFinite_smul' ν hc, ?_, ?_, fun s hs => ?_⟩
  · intro h0
    have := congrArg (fun μ : Measure (Mt k r) => μ Set.univ) h0
    simp only [Measure.smul_apply, smul_eq_mul, Measure.coe_zero, Pi.zero_apply, mul_eq_zero, hc0, false_or] at this
    exact h2 (Measure.measure_univ_eq_zero.1 this)
  · rw [Measure.smul_apply, h3, smul_zero]
  · rw [Measure.map_smul, h4 s hs]

/- English proof (translation)
Use extensionality with `g`. Simplify using `only [Set.mem_preimage, expBall, Set.mem_image, Formalism.MainNotions.S.Gauge.expSet, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, hxe⟩ set y := (lieIso hPJ h1 h2).symm x`. Use `⟨y, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_ball_zero_iff, LinearIsometryEquiv.norm_map]`. Conclude with `mem_ball_zero_iff.1 hx`. Establish `hxy : lieIso hPJ h1 h2 y = x` using `LinearIsometryEquiv.apply_symm_apply _ _`. Establish `hu` using `unrealify_lieIso hPJ h1 h2 y`. Rewrite `hu` using `[hxy]`.

Establish `hg : Pᴴ * uMat g * P = NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _))`. Establish `: (fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j) = cM (ε` using `ε) Pᴴ P g := hxe`. Conclude with `(funext fun i => funext fun j => congrFun (congrFun this i) j).symm`. Rewrite `hg` using `[hu, exp_conjP h1]`. Use `congrArg (fun M => P * M * Pᴴ) hg` as an intermediate fact.

Simplify using `only [← Matrix.mul_assoc, h2, Matrix.one_mul] at this`. Rewrite `this` using `[Matrix.mul_assoc _ P Pᴴ, h2, Matrix.mul_one, Matrix.mul_assoc _ P Pᴴ, h2, Matrix.mul_one]`. Conclude with `this`. Introduce and unpack `⟨y, hy, hye⟩`. Use `⟨lieIso hPJ h1 h2 y, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_ball_zero_iff, LinearIsometryEquiv.norm_map]`. Conclude with `mem_ball_zero_iff.1 hy`. Use function extensionality and compare the values at `i j`. Rewrite using `[unrealify_lieIso, exp_conjP h1, ← hye]`. Both sides reduce to the same expression.
-/
theorem preimage_expBall (hPJ : Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r) (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1) (ρ : ℝ) :
    cM (ε := ε) Pᴴ P ⁻¹' expBall (UH (Hpk k r)) ρ = Formalism.MainNotions.S.Gauge.expSet ε (Metric.ball 0 ρ) := by
  ext g
  simp only [Set.mem_preimage, expBall, Set.mem_image, Formalism.MainNotions.S.Gauge.expSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, hxe⟩
    set y := (lieIso hPJ h1 h2).symm x
    refine ⟨y, ?_, ?_⟩
    · rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map]; exact mem_ball_zero_iff.1 hx
    · have hxy : lieIso hPJ h1 h2 y = x := LinearIsometryEquiv.apply_symm_apply _ _
      have hu := unrealify_lieIso hPJ h1 h2 y
      rw [hxy] at hu
      have hg : Pᴴ * uMat g * P = NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) := by
        have : (fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j) = cM (ε := ε) Pᴴ P g := hxe
        exact (funext fun i => funext fun j => congrFun (congrFun this i) j).symm
      rw [hu, exp_conjP h1] at hg
      have := congrArg (fun M => P * M * Pᴴ) hg
      simp only [← Matrix.mul_assoc, h2, Matrix.one_mul] at this
      rw [Matrix.mul_assoc _ P Pᴴ, h2, Matrix.mul_one, Matrix.mul_assoc _ P Pᴴ, h2, Matrix.mul_one] at this
      exact this
  · rintro ⟨y, hy, hye⟩
    refine ⟨lieIso hPJ h1 h2 y, ?_, ?_⟩
    · rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map]; exact mem_ball_zero_iff.1 hy
    · funext i j
      rw [unrealify_lieIso, exp_conjP h1, ← hye]
      rfl

/- English proof (translation)
Establish `hp` using `(lieIso hPJ h1 h2).measurePreserving`. Establish `hpre : (lieIso hPJ h1 h2) ⁻¹' Metric.ball 0 ρ = Metric.ball 0 ρ`. Use extensionality with `y`. Simplify using `only [Set.mem_preimage, mem_ball_zero_iff, LinearIsometryEquiv.norm_map]`. Rewrite using `[← hp.measure_preimage measurableSet_ball.nullMeasurableSet, hpre]`.
-/
theorem volume_ball_lie (hPJ : Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r) (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1) (ρ : ℝ) :
    volume (Metric.ball (0 : lieE (UH (Hpk k r))) ρ) = volume (Metric.ball (0 : Formalism.MainNotions.S.Gauge.gLie ε) ρ) := by
  have hp := (lieIso hPJ h1 h2).measurePreserving
  have hpre : (lieIso hPJ h1 h2) ⁻¹' Metric.ball 0 ρ = Metric.ball 0 ρ := by
    ext y; simp only [Set.mem_preimage, mem_ball_zero_iff, LinearIsometryEquiv.norm_map]
  rw [← hp.measure_preimage measurableSet_ball.nullMeasurableSet, hpre]

/- English proof (translation)
Establish `e : (fun g : Formalism.REAL.UJ ε => t⁻¹ * g * t) = (fun g => g * t) ∘ (fun g => t⁻¹ * g)` using `rfl`. Rewrite using `[e, ← Measure.map_map (measurable_mul_const t) (measurable_const_mul t⁻¹), map_mul_left_eq_self, map_mul_right_eq_self]`.
-/
theorem muG_conj (t : Formalism.REAL.UJ ε) :
    (Formalism.REAL.muG ε).map (fun g => t⁻¹ * g * t) = Formalism.REAL.muG ε := by
  have e : (fun g : Formalism.REAL.UJ ε => t⁻¹ * g * t) = (fun g => g * t) ∘ (fun g => t⁻¹ * g) := rfl
  rw [e, ← Measure.map_map (measurable_mul_const t) (measurable_const_mul t⁻¹), map_mul_left_eq_self,
    map_mul_right_eq_self]

end Gauge

/- English proof (translation)
Take `⟨P, hPJ, h1⟩` from `exists_unitary ε (sig_of_frame hF)`. Establish `h2 : P * Pᴴ = 1` using `mul_eq_one_comm.mp h1`. Use `set c : ℝ≥0∞ := (ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε))⁻¹ with hc`. Establish `hgpos` using `hG.2`. Establish `hc0 : c ≠ 0` using `ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top`.

Establish `hct : c ≠ ⊤` using `ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hgpos).ne'`. Establish `hQ` using `gramQ hF`. Establish `hQiQm` using `Qi_mul_Qm hF`. Establish `hQmQi` using `Qm_mul_Qi hF`. Establish `ht : (Qm e f wf z0 * Pᴴ)ᴴ * Formalism.REAL.Jm ε * (Qm e f wf z0 * Pᴴ) = Formalism.REAL.Jm ε`.

Simplify using `only [conjTranspose_mul, conjTranspose_conjTranspose]`. Combine the equalities or inequalities in the displayed calculation. Use `set t : Formalism.REAL.UJ ε := toUJ (Qm e f wf z0 * Pᴴ) ht`. Establish `hut : uMat t = Qm e f wf z0 * Pᴴ` using `uMat_toUJ _ _`. Establish `hut' : uMat t⁻¹ = P * Qi ε e f wf z0`.

Establish `hinv : uMat t⁻¹ * uMat t = 1` using `by rw [← uMat_mul, inv_mul_cancel, uMat_one]`. Establish `hr : uMat t * (P * Qi ε e f wf z0) = 1`. Rewrite using `[hut, Matrix.mul_assoc, ← Matrix.mul_assoc Pᴴ, h1, Matrix.one_mul, hQmQi]`. Combine the equalities or inequalities in the displayed calculation. Establish `hfun : cM (ε` using `ε) (Qi ε e f wf z0) (Qm e f wf z0) = cM (ε := ε) Pᴴ P ∘ (fun g => t⁻¹ * g * t) := by`.

Use function extensionality and compare the values at `g`. Use `show (Qi ε e f wf z0 * uMat g * Qm e f wf z0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = Pᴴ * uMat (t⁻¹ * g * t) * P`. Rewrite using `[uMat_mul, uMat_mul, hut, hut']`. Simplify using `only [← Matrix.mul_assoc, h1, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc _ Pᴴ P, h1, Matrix.mul_one]`.

Establish `emb` using `cM_measEmb (ε := ε) (A := Pᴴ) (B := P) (A' := P) (B' := Pᴴ) h2 h2`. Establish `hmapeq : (c • Formalism.REAL.muG ε).map (cM (ε` using `ε) (Qi ε e f wf z0) (Qm e f wf z0)) = (c • Formalism.REAL.muG ε).map (cM (ε := ε) Pᴴ P) := by`. Establish `hm : Measurable (fun g : Formalism.REAL.UJ ε => t⁻¹ * g * t)` using `(measurable_const_mul t⁻¹).mul_const t`. Rewrite using `[hfun, ← Measure.map_map emb.measurable hm, Measure.map_smul, muG_conj]`. Rewrite using `[hmapeq]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.map_smul]`. Conclude with `isHaarOn_smul (isHaarOn_G (P0 := P) (B0 := Pᴴ) ⟨hPJ, by`. Rewrite using `[← hPJ]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc P Pᴴ, h2, Matrix.one_mul, Formalism.REAL.Jm_mul_self, Matrix.mul_one]⟩) hc0 hct`. Establish `hratio : ∀ ρ : ℝ, (((c • Formalism.REAL.muG ε).map (cM (ε` using `ε) Pᴴ P)) (expBall (UH (Hpk k r)) ρ)).toReal / (volume (Metric.ball (0 : lieE (UH (Hpk k r))) ρ)).toReal = (Formalism.MainNotions.S.Gauge.gaugeU ε)⁻¹ * Formalism.MainNotions.S.Gauge.ratioAt ε ρ := by`. Introduce `ρ`. Rewrite using `[emb.map_apply, preimage_expBall hPJ h1 h2, volume_ball_lie hPJ h1 h2, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, hc, ENNReal.toReal_inv, ENNReal.toReal_ofReal hgpos.le, Formalism.MainNotions.S.Gauge.ratioAt, mul_div_assoc]`. Establish `hlim : Tendsto (fun ρ => (Formalism.MainNotions.S.Gauge.gaugeU ε)⁻¹ * Formalism.MainNotions.S.Gauge.ratioAt ε ρ) (𝓝[>] 0) (𝓝 ((Formalism.MainNotions.S.Gauge.gaugeU ε)⁻¹ * Formalism.MainNotions.S.Gauge.gaugeU ε))` using `hG.1.const_mul _`.

Rewrite `hlim` using `[inv_mul_cancel₀ hgpos.ne']`. Conclude with `hlim.congr fun ρ => (hratio ρ).symm`.
-/
theorem gaugeTr_of {r k : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
    {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ} (hF : IsFrameJ ε e f wf z0)
    (hG : Formalism.MainNotions.S.Gauge.GaugeDens ε) :
    IsGaugeOn (UH (Hpk k r))
      (((ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε))⁻¹ • Formalism.REAL.muG ε).map
        (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0))) := by
  obtain ⟨P, hPJ, h1⟩ := exists_unitary ε (sig_of_frame hF)
  have h2 : P * Pᴴ = 1 := mul_eq_one_comm.mp h1
  set c : ℝ≥0∞ := (ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε))⁻¹ with hc
  have hgpos := hG.2
  have hc0 : c ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
  have hct : c ≠ ⊤ := ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hgpos).ne'

  have hQ := gramQ hF
  have hQiQm := Qi_mul_Qm hF
  have hQmQi := Qm_mul_Qi hF
  have ht : (Qm e f wf z0 * Pᴴ)ᴴ * Formalism.REAL.Jm ε * (Qm e f wf z0 * Pᴴ) = Formalism.REAL.Jm ε := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose]
    calc P * (Qm e f wf z0)ᴴ * Formalism.REAL.Jm ε * (Qm e f wf z0 * Pᴴ)
        = P * ((Qm e f wf z0)ᴴ * Formalism.REAL.Jm ε * Qm e f wf z0) * Pᴴ := by simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [hQ, PHP hPJ h2]
  set t : Formalism.REAL.UJ ε := toUJ (Qm e f wf z0 * Pᴴ) ht
  have hut : uMat t = Qm e f wf z0 * Pᴴ := uMat_toUJ _ _
  have hut' : uMat t⁻¹ = P * Qi ε e f wf z0 := by
    have hinv : uMat t⁻¹ * uMat t = 1 := by rw [← uMat_mul, inv_mul_cancel, uMat_one]
    have hr : uMat t * (P * Qi ε e f wf z0) = 1 := by
      rw [hut, Matrix.mul_assoc, ← Matrix.mul_assoc Pᴴ, h1, Matrix.one_mul, hQmQi]
    calc uMat t⁻¹ = uMat t⁻¹ * (uMat t * (P * Qi ε e f wf z0)) := by rw [hr, Matrix.mul_one]
      _ = P * Qi ε e f wf z0 := by rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
  have hfun : cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) = cM (ε := ε) Pᴴ P ∘ (fun g => t⁻¹ * g * t) := by
    funext g
    show (Qi ε e f wf z0 * uMat g * Qm e f wf z0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) =
      Pᴴ * uMat (t⁻¹ * g * t) * P
    rw [uMat_mul, uMat_mul, hut, hut']
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc _ Pᴴ P, h1, Matrix.mul_one]
  have emb := cM_measEmb (ε := ε) (A := Pᴴ) (B := P) (A' := P) (B' := Pᴴ) h2 h2
  have hmapeq : (c • Formalism.REAL.muG ε).map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0)) =
      (c • Formalism.REAL.muG ε).map (cM (ε := ε) Pᴴ P) := by
    have hm : Measurable (fun g : Formalism.REAL.UJ ε => t⁻¹ * g * t) := (measurable_const_mul t⁻¹).mul_const t
    rw [hfun, ← Measure.map_map emb.measurable hm, Measure.map_smul, muG_conj]
  rw [hmapeq]
  refine ⟨?_, ?_⟩
  · rw [Measure.map_smul]
    exact isHaarOn_smul (isHaarOn_G (P0 := P) (B0 := Pᴴ) ⟨hPJ, by
      rw [← hPJ]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc P Pᴴ, h2, Matrix.one_mul,
        Formalism.REAL.Jm_mul_self, Matrix.mul_one]⟩) hc0 hct
  · have hratio : ∀ ρ : ℝ,
        (((c • Formalism.REAL.muG ε).map (cM (ε := ε) Pᴴ P)) (expBall (UH (Hpk k r)) ρ)).toReal /
          (volume (Metric.ball (0 : lieE (UH (Hpk k r))) ρ)).toReal =
        (Formalism.MainNotions.S.Gauge.gaugeU ε)⁻¹ * Formalism.MainNotions.S.Gauge.ratioAt ε ρ := by
      intro ρ
      rw [emb.map_apply, preimage_expBall hPJ h1 h2, volume_ball_lie hPJ h1 h2, Measure.smul_apply, smul_eq_mul,
        ENNReal.toReal_mul, hc, ENNReal.toReal_inv, ENNReal.toReal_ofReal hgpos.le, Formalism.MainNotions.S.Gauge.ratioAt,
        mul_div_assoc]
    have hlim : Tendsto (fun ρ => (Formalism.MainNotions.S.Gauge.gaugeU ε)⁻¹ * Formalism.MainNotions.S.Gauge.ratioAt ε ρ) (𝓝[>] 0)
        (𝓝 ((Formalism.MainNotions.S.Gauge.gaugeU ε)⁻¹ * Formalism.MainNotions.S.Gauge.gaugeU ε)) := hG.1.const_mul _
    rw [inv_mul_cancel₀ hgpos.ne'] at hlim
    exact hlim.congr fun ρ => (hratio ρ).symm

end Formalism.L2.SG.Pf.NcReal.JX
