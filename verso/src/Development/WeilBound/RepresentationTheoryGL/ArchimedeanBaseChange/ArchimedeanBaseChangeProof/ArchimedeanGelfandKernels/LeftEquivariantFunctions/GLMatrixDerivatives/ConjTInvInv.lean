import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.HalfOne
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.KcDual
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.InvContDiffOn

import PositivityTheory.Representations.BoundaryCones.ArchimedeanCones.ConeOverlaps.OpenConeCriteria.OpenConeFormulation.IsOpenConeInvariant

noncomputable section

open Matrix Finset
open scoped ContDiff ComplexOrder

namespace PositivityTheory.RgBcC.LfSt.Kchain.KcHalf2

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.Kchain
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
Use extensionality with `v`. Simplify using `[Complex.coe_smul]`.
-/
theorem real_smul_clm {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (r : ℝ) (f : V →L[ℂ] V) :
    r • f = (r : ℂ) • f := by
  ext v
  simp [Complex.coe_smul]

/- English proof (translation)
Establish `h : star H.trace = H.trace`. Rewrite using `[← Matrix.trace_conjTranspose, hH.eq]`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Use `congrArg Complex.im h` as an intermediate fact.

Simplify using `only [Complex.star_def, Complex.conj_im] at this`. Simplify using `only [Complex.ofReal_im]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem trace_real {H : Mat n} (hH : H.IsHermitian) : ((H.trace.re : ℝ) : ℂ) = H.trace := by
  have h : star H.trace = H.trace := by
    rw [← Matrix.trace_conjTranspose, hH.eq]
  apply Complex.ext
  · simp
  · have := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at this
    simp only [Complex.ofReal_im]
    linarith

/- English proof (translation)
Take `⟨hher, -, -, -, -, -, htr, -⟩` from `hH n`. Establish `e : ∑ p, ((hb p : Mat n).trace.re) • (hb p : Mat n) = 1`. Rewrite using `[← htr]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[← trace_real (hher p)]`.

Use extensionality with `a b`. Simplify using `[Complex.real_smul]`. Rewrite using `[← e, map_sum]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, real_smul_clm, trace_real (hher p)]`.
-/
theorem eps_sum_trace (hH : HbFacts) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ε : Mat n →ₗ[ℝ] (V →L[ℂ] V)) : ∑ p, ((hb p : Mat n).trace) • ε (hb p) = ε 1 := by
  obtain ⟨hher, -, -, -, -, -, htr, -⟩ := hH n
  have e : ∑ p, ((hb p : Mat n).trace.re) • (hb p : Mat n) = 1 := by
    rw [← htr]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← trace_real (hher p)]
    ext a b
    simp [Complex.real_smul]
  rw [← e, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, real_smul_clm, trace_real (hher p)]

/- English proof (translation)
Take `⟨-, -, -, -, -, hsq, -, -⟩` from `hH n`. Rewrite using `[← map_sum, Finset.sum_add_distrib, hsq]`. Establish `e : (n : ℂ) • (1 : Mat n) + (n : ℂ) • 1 = ((2 * n : ℕ) : ℝ) • (1 : Mat n)`. Use extensionality with `a b`. Simplify using `[Complex.real_smul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, map_smul, real_smul_clm]`. Use `norm_cast`.
-/
theorem eps_sum_sq (hH : HbFacts) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ε : Mat n →ₗ[ℝ] (V →L[ℂ] V)) : ∑ p, ε ((hb p : Mat n) * hb p + hb p * hb p) = ((2 * n : ℕ) : ℂ) • ε 1 := by
  obtain ⟨-, -, -, -, -, hsq, -, -⟩ := hH n
  rw [← map_sum, Finset.sum_add_distrib, hsq]
  have e : (n : ℂ) • (1 : Mat n) + (n : ℂ) • 1 = ((2 * n : ℕ) : ℝ) • (1 : Mat n) := by
    ext a b
    simp [Complex.real_smul]
    ring
  rw [e, map_smul, real_smul_clm]
  norm_cast

/- English proof (translation)
Rewrite using `[← mul_assoc, mul_assoc Γ, h.Tε, ← mul_assoc, h.Γε]`. Simplify using `only [neg_mul, mul_assoc]`.
-/
theorem gte {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)}
    {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V} (h : CxData lam E Fr ε ι S Γ T) (H : Mat n) (X : E.V →L[ℂ] E.V) :
    Γ * T * (ε H * X) = -(ε H * (Γ * T * X)) := by
  rw [← mul_assoc, mul_assoc Γ, h.Tε, ← mul_assoc, h.Γε]
  simp only [neg_mul, mul_assoc]

/- English proof (translation)
Take `⟨hher, -⟩` from `hH n`. Use `set D0 := ∑ p, ε (hb p) * fderiv ℝ Fr 1 (hb p) with hD0`. Establish `hTD : T * D0 = -(D0 * T)` using `h.TD`. Establish `hΓdF : ∀ p, Γ * fderiv ℝ Fr 1 (hb p) = fderiv ℝ Fr 1 (hb p) * Γ` using `fun p => (hc n lam E Fr ε ι S Γ T h (hb p) (hb p) (hher p) (hher p)).2`. Establish `hΓD : Γ * D0 = -(D0 * Γ)`.

Rewrite using `[hD0, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, h.Γε, neg_mul, mul_assoc, hΓdF p, ← mul_assoc]`. Establish `hGTD : Γ * T * D0 = D0 * (Γ * T)`. Rewrite using `[mul_assoc, hTD, mul_neg, ← mul_assoc, hΓD, neg_mul, neg_neg, mul_assoc]`.

Establish `hcomm : ∀ p, fderiv ℝ Fr 1 (hb p) * ε (hb p) = ε (hb p) * fderiv ℝ Fr 1 (hb p) - ε ((hb p : Mat n) * hb p + hb p * hb p)` using `fun p => (hc n lam E Fr ε ι S Γ T h (hb p) (hb p) (hher p) (hher p)).1`. Establish `hs : ∀ p, (((-(2 * n : ℂ)) * (hb p : Mat n).trace) • K0 * Γ * T - R (hb p) * Γ * T - K0 * Γ * T * fderiv ℝ Fr 1 (hb p)) * ε (hb p) = (R (hb p) * ε (hb p) - K0 * ε (hb p) * fderiv ℝ Fr 1 (hb p)) * Γ * T + (K0 * (ε (hb p) * fderiv ℝ Fr 1 (hb p)) * (Γ * T) - K0 * (Γ * T * (ε (hb p) …`. Introduce `p`. Establish `e1 : Γ * T * ε (hb p) = -(ε (hb p) * (Γ * T))`. Use `gte h (hb p) 1` as an intermediate fact.

Simplify using `using this`. Establish `e2 : Γ * T * ε ((hb p : Mat n) * hb p + hb p * hb p) = -(ε ((hb p : Mat n) * hb p + hb p * hb p) * (Γ * T))`. Use `gte h ((hb p : Mat n) * hb p + hb p * hb p) 1` as an intermediate fact. Simplify using `using this`. Establish `lhs : (((-(2 * n : ℂ)) * (hb p : Mat n).trace) • K0 * Γ * T - R (hb p) * Γ * T - K0 * Γ * T * fderiv ℝ Fr 1 (hb p)) * ε (hb p) = ((-(2 * n : ℂ)) * (hb p : Mat n).trace) • (K0 * (Γ * T * ε (hb p))) - R (hb p) * (Γ * T * ε (hb p)) - K0 * (Γ * T * (fderiv ℝ Fr 1 (hb p) * ε (hb p)))`.

Simplify using `only [sub_mul, smul_mul_assoc, mul_assoc]`. Rewrite using `[lhs, e1, hcomm p, mul_sub (Γ * T), e2]`. Simplify using `only [mul_neg, neg_mul, smul_neg, mul_sub, sub_mul, mul_assoc, mul_smul_comm, smul_mul_assoc]`. Normalize the expressions using the abelian group laws. Rewrite using `[Finset.sum_congr rfl fun p _ => hs p, Finset.sum_add_distrib, Finset.sum_add_distrib]`.

Establish `z1 : ∑ p, (K0 * (ε (hb p) * fderiv ℝ Fr 1 (hb p)) * (Γ * T) - K0 * (Γ * T * (ε (hb p) * fderiv ℝ Fr 1 (hb p)))) = 0`. Rewrite using `[Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← hD0, hGTD, mul_assoc, sub_self]`. Establish `z2 : ∑ p, (-(K0 * ((-(2 * n : ℂ)) * (hb p : Mat n).trace) • ε (hb p) * (Γ * T)) - K0 * ε ((hb p : Mat n) * hb p + hb p * hb p) * (Γ * T)) = 0`. Establish `s1 : ∑ p, ((-(2 * n : ℂ)) * (hb p : Mat n).trace) • ε (hb p) = (-(2 * n : ℂ)) • ε 1`. Rewrite using `[← eps_sum_trace hH ε, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul]`. Establish `s2` using `eps_sum_sq hH ε`. Establish `: ∑ p, (-(K0 * ((-(2 * n : ℂ)) * (hb p : Mat n).trace) • ε (hb p) * (Γ * T)) - K0 * ε ((hb p : Mat n) * hb p + hb p * hb p) * (Γ * T)) = -(K0 * (∑ p, ((-(2 * n : ℂ)) * (hb p : Mat n).trace) • ε (hb p)) * (Γ * T)) - K0 * (∑ p, ε ((hb p : Mat n) * hb p + hb p * hb p)) * (Γ * T)`. Rewrite using `[Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]`.

Rewrite using `[this, s1, s2]`. Use `push_cast`. Simplify using `only [mul_neg, neg_mul, neg_neg, mul_smul_comm, smul_mul_assoc, neg_smul, sub_self]`. Rewrite using `[z1, z2, add_zero, add_zero, Finset.sum_mul, Finset.sum_mul]`.
-/
theorem algPsi (hH : HbFacts) (hc : FrComm) {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)}
    {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)} {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}
    (h : CxData lam E Fr ε ι S Γ T) (K0 : E.V →L[ℂ] E.V) (R : Mat n → (E.V →L[ℂ] E.V)) :
    ∑ p, ((((-(2 * n : ℂ)) * (hb p : Mat n).trace) • K0 * Γ * T - R (hb p) * Γ * T -
        K0 * Γ * T * fderiv ℝ Fr 1 (hb p)) * ε (hb p)) =
      (∑ p, (R (hb p) * ε (hb p) - K0 * ε (hb p) * fderiv ℝ Fr 1 (hb p))) * Γ * T := by
  obtain ⟨hher, -⟩ := hH n
  set D0 := ∑ p, ε (hb p) * fderiv ℝ Fr 1 (hb p) with hD0
  have hTD : T * D0 = -(D0 * T) := h.TD
  have hΓdF : ∀ p, Γ * fderiv ℝ Fr 1 (hb p) = fderiv ℝ Fr 1 (hb p) * Γ := fun p =>
    (hc n lam E Fr ε ι S Γ T h (hb p) (hb p) (hher p) (hher p)).2
  have hΓD : Γ * D0 = -(D0 * Γ) := by
    rw [hD0, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← mul_assoc, h.Γε, neg_mul, mul_assoc, hΓdF p, ← mul_assoc]
  have hGTD : Γ * T * D0 = D0 * (Γ * T) := by
    rw [mul_assoc, hTD, mul_neg, ← mul_assoc, hΓD, neg_mul, neg_neg, mul_assoc]
  have hcomm : ∀ p, fderiv ℝ Fr 1 (hb p) * ε (hb p) =
      ε (hb p) * fderiv ℝ Fr 1 (hb p) - ε ((hb p : Mat n) * hb p + hb p * hb p) := fun p =>
    (hc n lam E Fr ε ι S Γ T h (hb p) (hb p) (hher p) (hher p)).1

  have hs : ∀ p, (((-(2 * n : ℂ)) * (hb p : Mat n).trace) • K0 * Γ * T - R (hb p) * Γ * T -
        K0 * Γ * T * fderiv ℝ Fr 1 (hb p)) * ε (hb p) =
      (R (hb p) * ε (hb p) - K0 * ε (hb p) * fderiv ℝ Fr 1 (hb p)) * Γ * T +
        (K0 * (ε (hb p) * fderiv ℝ Fr 1 (hb p)) * (Γ * T) - K0 * (Γ * T * (ε (hb p) * fderiv ℝ Fr 1 (hb p)))) +
        (-(K0 * ((-(2 * n : ℂ)) * (hb p : Mat n).trace) • ε (hb p) * (Γ * T)) -
          K0 * ε ((hb p : Mat n) * hb p + hb p * hb p) * (Γ * T)) := by
    intro p
    have e1 : Γ * T * ε (hb p) = -(ε (hb p) * (Γ * T)) := by
      have := gte h (hb p) 1
      simpa using this
    have e2 : Γ * T * ε ((hb p : Mat n) * hb p + hb p * hb p) =
        -(ε ((hb p : Mat n) * hb p + hb p * hb p) * (Γ * T)) := by
      have := gte h ((hb p : Mat n) * hb p + hb p * hb p) 1
      simpa using this
    have lhs : (((-(2 * n : ℂ)) * (hb p : Mat n).trace) • K0 * Γ * T - R (hb p) * Γ * T -
        K0 * Γ * T * fderiv ℝ Fr 1 (hb p)) * ε (hb p) =
        ((-(2 * n : ℂ)) * (hb p : Mat n).trace) • (K0 * (Γ * T * ε (hb p))) - R (hb p) * (Γ * T * ε (hb p)) -
          K0 * (Γ * T * (fderiv ℝ Fr 1 (hb p) * ε (hb p))) := by
      simp only [sub_mul, smul_mul_assoc, mul_assoc]
    rw [lhs, e1, hcomm p, mul_sub (Γ * T), e2]
    simp only [mul_neg, neg_mul, smul_neg, mul_sub, sub_mul, mul_assoc, mul_smul_comm, smul_mul_assoc]
    abel
  rw [Finset.sum_congr rfl fun p _ => hs p, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have z1 : ∑ p, (K0 * (ε (hb p) * fderiv ℝ Fr 1 (hb p)) * (Γ * T) -
      K0 * (Γ * T * (ε (hb p) * fderiv ℝ Fr 1 (hb p)))) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← hD0,
      hGTD, mul_assoc, sub_self]
  have z2 : ∑ p, (-(K0 * ((-(2 * n : ℂ)) * (hb p : Mat n).trace) • ε (hb p) * (Γ * T)) -
      K0 * ε ((hb p : Mat n) * hb p + hb p * hb p) * (Γ * T)) = 0 := by
    have s1 : ∑ p, ((-(2 * n : ℂ)) * (hb p : Mat n).trace) • ε (hb p) = (-(2 * n : ℂ)) • ε 1 := by
      rw [← eps_sum_trace hH ε, Finset.smul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [mul_smul]
    have s2 := eps_sum_sq hH ε
    have : ∑ p, (-(K0 * ((-(2 * n : ℂ)) * (hb p : Mat n).trace) • ε (hb p) * (Γ * T)) -
        K0 * ε ((hb p : Mat n) * hb p + hb p * hb p) * (Γ * T)) =
        -(K0 * (∑ p, ((-(2 * n : ℂ)) * (hb p : Mat n).trace) • ε (hb p)) * (Γ * T)) -
          K0 * (∑ p, ε ((hb p : Mat n) * hb p + hb p * hb p)) * (Γ * T) := by
      rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum,
        Finset.sum_mul]
    rw [this, s1, s2]
    push_cast
    simp only [mul_neg, neg_mul, neg_neg, mul_smul_comm, smul_mul_assoc, neg_smul, sub_self]
  rw [z1, z2, add_zero, add_zero, Finset.sum_mul, Finset.sum_mul]

/- English proof (translation)
Use `hf.hasFDerivAt.comp b (hasFDerivAt_prodMk_right a b)` as an intermediate fact. Establish `e : (fun b' => f (a, b')) = f ∘ Prod.mk a` using `rfl`. Rewrite using `[e, this.fderiv]`. Simplify using the standard rewrite rules.
-/
theorem partial_snd {A B Z : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] (f : A × B → Z) (a : A) (b : B) (hf : DifferentiableAt ℝ f (a, b)) (h : B) :
    fderiv ℝ f (a, b) (0, h) = fderiv ℝ (fun b' => f (a, b')) b h := by
  have := hf.hasFDerivAt.comp b (hasFDerivAt_prodMk_right a b)
  have e : (fun b' => f (a, b')) = f ∘ Prod.mk a := rfl
  rw [e, this.fderiv]
  simp

/- English proof (translation)
Unfold `hOf`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `p _ hp`. Simplify using `[Pi.single_apply, hp]`.

Simplify using the standard rewrite rules.
-/
theorem hOf_single (i : Fin n × Fin n) : hOf (Pi.single i (1 : ℝ)) = (hb i : Mat n) := by
  unfold hOf
  rw [Finset.sum_eq_single i]
  · simp
  · intro p _ hp
    simp [Pi.single_apply, hp]
  · simp

/- English proof (translation)
The claim follows from `isUnit_iff_ne_zero.mpr hy`.
-/
theorem unit_of {y : Mat n} (hy : y ∈ GLs n) : IsUnit y.det := isUnit_iff_ne_zero.mpr hy

/- English proof (translation)
The claim follows from `PositivityTheory.KcHalf2₂.isOpen_cone_of_hbFacts hH`.
-/
theorem isOpen_cone (hH : HbFacts) : IsOpen (cone n) := PositivityTheory.KcHalf2₂.isOpen_cone_of_hbFacts hH

section Main

variable {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)}
  {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[← h.mul _ (KcInv.inv_mem hy) _ hy, Matrix.nonsing_inv_mul _ (unit_of hy), h.one]`. Rewrite using `[← h.mul _ hy _ (KcInv.inv_mem hy), Matrix.mul_nonsing_inv _ (unit_of hy), h.one]`.
-/
theorem frInv (h : CxData lam E Fr ε ι S Γ T) {y : Mat n} (hy : y ∈ GLs n) :
    Fr y⁻¹ * Fr y = 1 ∧ Fr y * Fr y⁻¹ = 1 := by
  constructor
  · rw [← h.mul _ (KcInv.inv_mem hy) _ hy, Matrix.nonsing_inv_mul _ (unit_of hy), h.one]
  · rw [← h.mul _ hy _ (KcInv.inv_mem hy), Matrix.mul_nonsing_inv _ (unit_of hy), h.one]

/- English proof (translation)
Establish `e` using `h.frε y hy H hH`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem frInvEps (h : CxData lam E Fr ε ι S Γ T) {y : Mat n} (hy : y ∈ GLs n) {H : Mat n} (hH : H.IsHermitian) :
    Fr y⁻¹ * ε H = ε (yᴴ * H * y) * Fr y⁻¹ := by
  have e := h.frε y hy H hH
  calc Fr y⁻¹ * ε H = Fr y⁻¹ * ε H * (Fr y * Fr y⁻¹) := by rw [(frInv h hy).2, mul_one]
    _ = Fr y⁻¹ * (ε H * Fr y) * Fr y⁻¹ := by simp only [mul_assoc]
    _ = Fr y⁻¹ * (Fr y * ε (yᴴ * H * y)) * Fr y⁻¹ := by rw [e]
    _ = ε (yᴴ * H * y) * Fr y⁻¹ := by rw [← mul_assoc (Fr y⁻¹), (frInv h hy).1, one_mul]

def Gf (Fr k : Mat n → (E.V →L[ℂ] E.V)) (Γ T : E.V →L[ℂ] E.V) (c : ℝ) (d x : Mat n) : Mat n → (E.V →L[ℂ] E.V) :=
  fun y' => wt c y' • Kf Fr k Γ T d x y'

/- English proof (translation)
Establish `hW : ContDiffOn ℝ ∞ (fun y' : Mat n => wt c y') (GLs n)`. Unfold `wt`. Use `contDiffOn_const.mul (ContDiffOn.inv ?_ fun y hy => pow_ne_zero _ ?_)` and prove the remaining obligations. Conclude with `(KcInv.det_contDiff.comp_contDiffOn (KcInv.mul_contDiffOn contDiffOn_id KcInv.star_contDiff.contDiffOn)).pow n`. Conclude with `KcInv.mul_mem hy (KcInv.conjT_mem hy)`.

Establish `harg : ContDiffOn ℝ ∞ (fun y' : Mat n => x⁻¹ * d * y'ᴴ⁻¹) (GLs n)` using `KcInv.mul_contDiffOn contDiffOn_const (KcInv.inv_contDiffOn.comp KcInv.star_contDiff.contDiffOn fun y hy => KcInv.conjT_mem hy)`. Establish `hargm : ∀ y' ∈ GLs n, x⁻¹ * d * y'ᴴ⁻¹ ∈ GLs n` using `fun y' hy' => KcInv.mul_mem (KcInv.mul_mem (KcInv.inv_mem hx) hd) (KcInv.inv_mem (KcInv.conjT_mem hy'))`. Establish `hK : ContDiffOn ℝ ∞ (fun y' => Kf Fr k Γ T d x y') (GLs n)`. Unfold `Kf`. Conclude with `ContDiffOn.mul (ContDiffOn.mul (ContDiffOn.mul (ContDiffOn.mul contDiffOn_const (hk.comp harg hargm)) contDiffOn_const) contDiffOn_const) (h.smooth.comp KcInv.inv_contDiffOn fun y hy => KcInv.inv_mem hy)`.

Conclude with `hW.smul hK`.
-/
theorem Gf_smooth (h : CxData lam E Fr ε ι S Γ T) {k : Mat n → (E.V →L[ℂ] E.V)} (hk : ContDiffOn ℝ ∞ k (GLs n))
    (c : ℝ) {d x : Mat n} (hd : d ∈ GLs n) (hx : x ∈ GLs n) : ContDiffOn ℝ ∞ (Gf Fr k Γ T c d x) (GLs n) := by
  have hW : ContDiffOn ℝ ∞ (fun y' : Mat n => wt c y') (GLs n) := by
    unfold wt
    refine contDiffOn_const.mul (ContDiffOn.inv ?_ fun y hy => pow_ne_zero _ ?_)
    · exact (KcInv.det_contDiff.comp_contDiffOn (KcInv.mul_contDiffOn contDiffOn_id
        KcInv.star_contDiff.contDiffOn)).pow n
    · exact KcInv.mul_mem hy (KcInv.conjT_mem hy)
  have harg : ContDiffOn ℝ ∞ (fun y' : Mat n => x⁻¹ * d * y'ᴴ⁻¹) (GLs n) :=
    KcInv.mul_contDiffOn contDiffOn_const
      (KcInv.inv_contDiffOn.comp KcInv.star_contDiff.contDiffOn fun y hy => KcInv.conjT_mem hy)
  have hargm : ∀ y' ∈ GLs n, x⁻¹ * d * y'ᴴ⁻¹ ∈ GLs n := fun y' hy' =>
    KcInv.mul_mem (KcInv.mul_mem (KcInv.inv_mem hx) hd) (KcInv.inv_mem (KcInv.conjT_mem hy'))
  have hK : ContDiffOn ℝ ∞ (fun y' => Kf Fr k Γ T d x y') (GLs n) := by
    unfold Kf
    exact ContDiffOn.mul (ContDiffOn.mul (ContDiffOn.mul (ContDiffOn.mul contDiffOn_const (hk.comp harg hargm))
      contDiffOn_const) contDiffOn_const) (h.smooth.comp KcInv.inv_contDiffOn fun y hy => KcInv.inv_mem hy)
  exact hW.smul hK

/- English proof (translation)
Introduce `y hy u`. Establish `hu1 : u.1 * star u.1 = 1` using `(Matrix.mem_unitaryGroup_iff.mp u.2)`. Establish `hu2 : star u.1 * u.1 = 1` using `(Matrix.mem_unitaryGroup_iff'.mp u.2)`. Establish `hsu : star u.1 = u.1ᴴ` using `rfl`. Establish `huG : u.1 ∈ GLs n` using `by show u.1.det ≠ 0`.

Introduce `h0`. Use `congrArg Matrix.det hu2` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, h0, mul_zero, Matrix.det_one]`. Conclude with `zero_ne_one this`. Establish `hsuG : star u.1 ∈ GLs n` using `by rw [hsu]; exact KcInv.conjT_mem huG`.

Establish `e1 : (y * u.1) * (y * u.1)ᴴ = y * yᴴ`. Rewrite using `[Matrix.conjTranspose_mul, ← hsu, Matrix.mul_assoc, ← Matrix.mul_assoc u.1, hu1, Matrix.one_mul]`. Establish `e2 : (y * u.1)ᴴ⁻¹ = yᴴ⁻¹ * u.1`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.mul_inv_rev, ← hsu, Matrix.inv_eq_left_inv hu1]`. Establish `e3 : (y * u.1)⁻¹ = star u.1 * y⁻¹`.

Rewrite using `[Matrix.mul_inv_rev, Matrix.inv_eq_left_inv hu2]`. Establish `hw : x⁻¹ * d * yᴴ⁻¹ ∈ GLs n` using `KcInv.mul_mem (KcInv.mul_mem (KcInv.inv_mem hx) hd) (KcInv.inv_mem (KcInv.conjT_mem hy))`. Establish `ek : k (x⁻¹ * d * (y * u.1)ᴴ⁻¹) = k (x⁻¹ * d * yᴴ⁻¹) * E.ρ u`. Use `hkK _ hw 1 u` as an intermediate fact. Rewrite `this` using `[Submonoid.coe_one, Matrix.one_mul, map_one, one_mul]`.

Rewrite using `[e2, ← Matrix.mul_assoc, this]`. Establish `ef : Fr (y * u.1)⁻¹ = E.ρ u⁻¹ * Fr y⁻¹`. Rewrite using `[e3, h.mul _ hsuG _ (KcInv.inv_mem hy)]`. Use `congr 1`. Rewrite using `[← h.onK]`.

Use `congr 1`. Establish `hρΓ : E.ρ u * Γ = Γ * E.ρ u` using `by rw [← h.onK]; exact (h.ΓFr _ huG).symm`. Establish `hρT : E.ρ u * T = T * E.ρ u` using `(h.TK u).symm`. Establish `hρρ : E.ρ u * E.ρ u⁻¹ = 1` using `by rw [← map_mul, mul_inv_cancel, map_one]`. Unfold `Gf wt Kf`.

Rewrite using `[e1, ek, ef]`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem Gf_inv (h : CxData lam E Fr ε ι S Γ T) {k : Mat n → (E.V →L[ℂ] E.V)}
    (hkK : ∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂)
    (c : ℝ) {d x : Mat n} (hd : d ∈ GLs n) (hx : x ∈ GLs n) :
    ∀ y ∈ GLs n, ∀ u : Matrix.unitaryGroup (Fin n) ℂ, Gf Fr k Γ T c d x (y * u.1) = Gf Fr k Γ T c d x y := by
  intro y hy u
  have hu1 : u.1 * star u.1 = 1 := (Matrix.mem_unitaryGroup_iff.mp u.2)
  have hu2 : star u.1 * u.1 = 1 := (Matrix.mem_unitaryGroup_iff'.mp u.2)
  have hsu : star u.1 = u.1ᴴ := rfl
  have huG : u.1 ∈ GLs n := by
    show u.1.det ≠ 0
    intro h0
    have := congrArg Matrix.det hu2
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  have hsuG : star u.1 ∈ GLs n := by rw [hsu]; exact KcInv.conjT_mem huG
  have e1 : (y * u.1) * (y * u.1)ᴴ = y * yᴴ := by
    rw [Matrix.conjTranspose_mul, ← hsu, Matrix.mul_assoc, ← Matrix.mul_assoc u.1, hu1, Matrix.one_mul]
  have e2 : (y * u.1)ᴴ⁻¹ = yᴴ⁻¹ * u.1 := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_inv_rev, ← hsu, Matrix.inv_eq_left_inv hu1]
  have e3 : (y * u.1)⁻¹ = star u.1 * y⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.inv_eq_left_inv hu2]
  have hw : x⁻¹ * d * yᴴ⁻¹ ∈ GLs n :=
    KcInv.mul_mem (KcInv.mul_mem (KcInv.inv_mem hx) hd) (KcInv.inv_mem (KcInv.conjT_mem hy))
  have ek : k (x⁻¹ * d * (y * u.1)ᴴ⁻¹) = k (x⁻¹ * d * yᴴ⁻¹) * E.ρ u := by
    have := hkK _ hw 1 u
    rw [Submonoid.coe_one, Matrix.one_mul, map_one, one_mul] at this
    rw [e2, ← Matrix.mul_assoc, this]
  have ef : Fr (y * u.1)⁻¹ = E.ρ u⁻¹ * Fr y⁻¹ := by
    rw [e3, h.mul _ hsuG _ (KcInv.inv_mem hy)]
    congr 1
    rw [← h.onK]
    congr 1
  have hρΓ : E.ρ u * Γ = Γ * E.ρ u := by rw [← h.onK]; exact (h.ΓFr _ huG).symm
  have hρT : E.ρ u * T = T * E.ρ u := (h.TK u).symm
  have hρρ : E.ρ u * E.ρ u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  unfold Gf wt Kf
  rw [e1, ek, ef]
  congr 1
  calc Fr x * (k (x⁻¹ * d * yᴴ⁻¹) * E.ρ u) * Γ * T * (E.ρ u⁻¹ * Fr y⁻¹)
      = Fr x * k (x⁻¹ * d * yᴴ⁻¹) * (E.ρ u * Γ) * T * (E.ρ u⁻¹ * Fr y⁻¹) := by simp only [mul_assoc]
    _ = Fr x * k (x⁻¹ * d * yᴴ⁻¹) * Γ * (E.ρ u * T) * (E.ρ u⁻¹ * Fr y⁻¹) := by rw [hρΓ]; simp only [mul_assoc]
    _ = Fr x * k (x⁻¹ * d * yᴴ⁻¹) * Γ * T * ((E.ρ u * E.ρ u⁻¹) * Fr y⁻¹) := by rw [hρT]; simp only [mul_assoc]
    _ = Fr x * k (x⁻¹ * d * yᴴ⁻¹) * Γ * T * Fr y⁻¹ := by rw [hρρ, one_mul]

end Main

def psiL {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (K0 : V →L[ℂ] V) (Dk DF : Mat n →L[ℝ] (V →L[ℂ] V))
    (w0 : Mat n) (Γ T : V →L[ℂ] V) : Mat n →ₗ[ℝ] (V →L[ℂ] V) where
  toFun X := ((-(2 * n : ℂ)) * X.trace) • K0 * Γ * T - Dk (w0 * X) * Γ * T - K0 * Γ * T * DF X
  map_add' X Y := by
    simp only [Matrix.trace_add, mul_add, add_smul, add_mul, Matrix.mul_add, map_add]
    abel
  map_smul' r X := by
    simp only [Matrix.trace_smul, Matrix.mul_smul, map_smul, RingHom.id_apply]
    rw [real_smul_clm r (Dk (w0 * X)), real_smul_clm r (DF X), real_smul_clm r]
    have e : ((-(2 * n : ℂ)) * (r • X.trace)) = (r : ℂ) * ((-(2 * n : ℂ)) * X.trace) := by
      rw [Complex.real_smul]; ring
    rw [e, mul_smul]
    simp only [smul_mul_assoc, mul_smul_comm, smul_sub]

/- English proof (translation)
Rewrite using `[Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose]`.
-/
theorem conjT_inv_inv {y : Mat n} : (yᴴ⁻¹)ᴴ = y⁻¹ := by
  rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose]

/- English proof (translation)
Introduce `n lam E Fr ε ι S Γ T h σ hσs hσ k hk hkK d hd c v hv w hw`. Take `⟨hher, horth, -, hcoV, -, -, -, -⟩` from `hH n`. Establish `hgl` using `KcInv.coneGL n σ hσ`. Establish `hx : σ v ∈ GLs n` using `(hgl v hv).1`. Establish `hy : σ w ∈ GLs n` using `(hgl w hw).1`.

Establish `hyu : IsUnit (σ w).det` using `unit_of hy`. Establish `hyHu : IsUnit (σ w)ᴴ.det` using `unit_of (KcInv.conjT_mem hy)`. Establish `hKs` using `KcInv.kcSmooth n E.V σ c Fr k Γ T d hd hσs hσ h.smooth hk`. Establish `hop : IsOpen (cone n)` using `isOpen_cone hH`. Establish `hmem : (v, w) ∈ cone n ×ˢ cone n` using `⟨hv, hw⟩`.

Establish `hnh : cone n ×ˢ cone n ∈ nhds (v, w)` using `(hop.prod hop).mem_nhds hmem`. Establish `hca : ContDiffAt ℝ ∞ (Kc σ c Fr k Γ T d) (v, w)` using `hKs.contDiffAt hnh`. Establish `hdiff : DifferentiableAt ℝ (Kc σ c Fr k Γ T d) (v, w)` using `hca.differentiableAt (by norm_num)`. Use `set Ψ := psiL (k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹)) (fderiv ℝ k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹)) (fderiv ℝ Fr 1) ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹) Γ T with hΨ`. Use `set A : Fin n × Fin n → Mat n := fun i => (σ w)⁻¹ * hb i * (σ w)ᴴ⁻¹ with hA`.

Use `set A' : Fin n × Fin n → Mat n := fun i => (σ w)ᴴ * hb i * σ w with hA'`. Establish `hAh : ∀ i, (A i).IsHermitian` using `fun i => by show ((σ w)⁻¹ * hb i * (σ w)ᴴ⁻¹)ᴴ = (σ w)⁻¹ * hb i * (σ w)ᴴ⁻¹`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, conjT_inv_inv, (hher i).eq, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]`. Establish `hA'h : ∀ i, (A' i).IsHermitian` using `fun i => by show ((σ w)ᴴ * hb i * σ w)ᴴ = (σ w)ᴴ * hb i * σ w`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, (hher i).eq, Matrix.mul_assoc]`.

Establish `htr : ∀ i j, (A i * A' j).trace = if i = j then 1 else 0` using `fun i j => by show ((σ w)⁻¹ * hb i * (σ w)ᴴ⁻¹ * ((σ w)ᴴ * hb j * σ w)).trace = _`. Establish `e : (σ w)⁻¹ * hb i * (σ w)ᴴ⁻¹ * ((σ w)ᴴ * hb j * σ w) = (σ w)⁻¹ * (hb i * hb j * σ w)`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc ((σ w)ᴴ⁻¹), Matrix.nonsing_inv_mul _ hyHu, Matrix.one_mul]`. Rewrite using `[e, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hyu, Matrix.mul_one, horth]`.

Establish `hpart : ∀ i, fderiv ℝ (Kc σ c Fr k Γ T d) (v, w) (0, Pi.single i 1) = wt c (σ w) • (Fr (σ v) * Ψ ((1 / 2 : ℝ) • A i) * Fr (σ w)⁻¹)`. Introduce `i`. Rewrite using `[partial_snd _ v w hdiff]`. Establish `heq : (fun w' => Kc σ c Fr k Γ T d (v, w')) =ᶠ[nhds w] fun w' => Gf Fr k Γ T c d (σ v) (σ w')` using `by filter_upwards [hop.mem_nhds hw] with w' hw'`. Simplify using `only [Kc, Gf, wt]`.

Rewrite using `[hσ w' hw']`. Rewrite using `[heq.fderiv_eq]`. Establish `hXh : ((1 / 2 : ℝ) • A i).IsHermitian` using `by show ((1 / 2 : ℝ) • A i)ᴴ = (1 / 2 : ℝ) • A i`. Rewrite using `[Matrix.conjTranspose_smul, (hAh i).eq]`. Simplify using the standard rewrite rules.

Establish `hdir : coords ((2 : ℂ) • (σ w * ((1 / 2 : ℝ) • A i) * (σ w)ᴴ)) = Pi.single i 1`. Establish `e : (2 : ℂ) • (σ w * ((1 / 2 : ℝ) • A i) * (σ w)ᴴ) = hb i` using `by show (2 : ℂ) • (σ w * ((1 / 2 : ℝ) • ((σ w)⁻¹ * hb i * (σ w)ᴴ⁻¹)) * (σ w)ᴴ) = hb i`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul]`. Establish `e2 : σ w * ((σ w)⁻¹ * hb i * (σ w)ᴴ⁻¹) * (σ w)ᴴ = hb i`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[Matrix.nonsing_inv_mul _ hyHu, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hyu, Matrix.one_mul]`. Rewrite using `[e2]`. Use extensionality with `a b`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, ← hOf_single, hcoV]`. Establish `hFD` using `hF n (E.V →L[ℂ] E.V) σ (Gf Fr k Γ T c d (σ v)) hσs hσ (Gf_smooth h hk c hd hx) (Gf_inv h hkK c hd hx) w hw (σ w) hy (hσ w hw) _ hXh`. Rewrite `hFD` using `[hdir]`. Rewrite using `[hFD]`.

Conclude with `h2 n lam E Fr ε ι S Γ T h k hk c d (σ v) hd hx (σ w) hy _ hXh`. Establish `hsum : ∑ i, fderiv ℝ (Kc σ c Fr k Γ T d) (v, w) (0, Pi.single i 1) * ε (hb i) = wt c (σ w) • (Fr (σ v) * ((1 / 2 : ℂ) • ∑ i, Ψ (A i) * ε (A' i)) * Fr (σ w)⁻¹)`. Rewrite using `[Finset.smul_sum, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hpart i, map_smul, real_smul_clm, smul_mul_assoc]`.

Use `congr 1`. Rewrite using `[mul_assoc (Fr (σ v) * _) (Fr (σ w)⁻¹), frInvEps h hy (hher i), ← mul_assoc, mul_assoc (Fr (σ v)), smul_mul_assoc]`. Establish `hc2 : (((1 / 2 : ℝ)) : ℂ) = (1 / 2 : ℂ)` using `by norm_num`. Rewrite using `[hc2]`. Rewrite using `[hsum, hD n E.V Ψ ε A A' hAh hA'h htr]`.

Establish `halg` using `algPsi hH hc h (k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹)) (fun X => Rd X k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹))`. Establish `e : ∑ p, Ψ (hb p) * ε (hb p) = (∑ p, (Rd (hb p) k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹) * ε (hb p) - k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹) * ε (hb p) * fderiv ℝ Fr 1 (hb p))) * Γ * T` using `halg`. Rewrite using `[e]`. Establish `hwt : wt c (σ w) = (c : ℂ) * ((hOf w).det ^ n)⁻¹` using `by simp only [wt]; rw [hσ w hw]`. Rewrite using `[hwt]`.

Simplify using `only [smul_mul_assoc, mul_smul_comm, mul_assoc]`.
-/
theorem halfTwo_of (hH : HbFacts) (hF : FrameDer) (hc : FrComm) (h2 : DerTwo) (hD : DualSum) : HalfTwo := by
  intro n lam E Fr ε ι S Γ T h σ hσs hσ k hk hkK d hd c v hv w hw
  obtain ⟨hher, horth, -, hcoV, -, -, -, -⟩ := hH n
  have hgl := KcInv.coneGL n σ hσ
  have hx : σ v ∈ GLs n := (hgl v hv).1
  have hy : σ w ∈ GLs n := (hgl w hw).1
  have hyu : IsUnit (σ w).det := unit_of hy
  have hyHu : IsUnit (σ w)ᴴ.det := unit_of (KcInv.conjT_mem hy)
  have hKs := KcInv.kcSmooth n E.V σ c Fr k Γ T d hd hσs hσ h.smooth hk
  have hop : IsOpen (cone n) := isOpen_cone hH
  have hmem : (v, w) ∈ cone n ×ˢ cone n := ⟨hv, hw⟩
  have hnh : cone n ×ˢ cone n ∈ nhds (v, w) := (hop.prod hop).mem_nhds hmem
  have hca : ContDiffAt ℝ ∞ (Kc σ c Fr k Γ T d) (v, w) := hKs.contDiffAt hnh
  have hdiff : DifferentiableAt ℝ (Kc σ c Fr k Γ T d) (v, w) := hca.differentiableAt (by norm_num)
  set Ψ := psiL (k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹)) (fderiv ℝ k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹)) (fderiv ℝ Fr 1)
    ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹) Γ T with hΨ
  set A : Fin n × Fin n → Mat n := fun i => (σ w)⁻¹ * hb i * (σ w)ᴴ⁻¹ with hA
  set A' : Fin n × Fin n → Mat n := fun i => (σ w)ᴴ * hb i * σ w with hA'
  have hAh : ∀ i, (A i).IsHermitian := fun i => by
    show ((σ w)⁻¹ * hb i * (σ w)ᴴ⁻¹)ᴴ = (σ w)⁻¹ * hb i * (σ w)ᴴ⁻¹
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, conjT_inv_inv, (hher i).eq,
      Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]
  have hA'h : ∀ i, (A' i).IsHermitian := fun i => by
    show ((σ w)ᴴ * hb i * σ w)ᴴ = (σ w)ᴴ * hb i * σ w
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, (hher i).eq,
      Matrix.mul_assoc]
  have htr : ∀ i j, (A i * A' j).trace = if i = j then 1 else 0 := fun i j => by
    show ((σ w)⁻¹ * hb i * (σ w)ᴴ⁻¹ * ((σ w)ᴴ * hb j * σ w)).trace = _
    have e : (σ w)⁻¹ * hb i * (σ w)ᴴ⁻¹ * ((σ w)ᴴ * hb j * σ w) = (σ w)⁻¹ * (hb i * hb j * σ w) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc ((σ w)ᴴ⁻¹), Matrix.nonsing_inv_mul _ hyHu, Matrix.one_mul]
    rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hyu, Matrix.mul_one, horth]
  have hpart : ∀ i, fderiv ℝ (Kc σ c Fr k Γ T d) (v, w) (0, Pi.single i 1) =
      wt c (σ w) • (Fr (σ v) * Ψ ((1 / 2 : ℝ) • A i) * Fr (σ w)⁻¹) := by
    intro i
    rw [partial_snd _ v w hdiff]
    have heq : (fun w' => Kc σ c Fr k Γ T d (v, w')) =ᶠ[nhds w] fun w' => Gf Fr k Γ T c d (σ v) (σ w') := by
      filter_upwards [hop.mem_nhds hw] with w' hw'
      simp only [Kc, Gf, wt]
      rw [hσ w' hw']
    rw [heq.fderiv_eq]
    have hXh : ((1 / 2 : ℝ) • A i).IsHermitian := by
      show ((1 / 2 : ℝ) • A i)ᴴ = (1 / 2 : ℝ) • A i
      rw [Matrix.conjTranspose_smul, (hAh i).eq]
      simp
    have hdir : coords ((2 : ℂ) • (σ w * ((1 / 2 : ℝ) • A i) * (σ w)ᴴ)) = Pi.single i 1 := by
      have e : (2 : ℂ) • (σ w * ((1 / 2 : ℝ) • A i) * (σ w)ᴴ) = hb i := by
        show (2 : ℂ) • (σ w * ((1 / 2 : ℝ) • ((σ w)⁻¹ * hb i * (σ w)ᴴ⁻¹)) * (σ w)ᴴ) = hb i
        rw [Matrix.mul_smul, Matrix.smul_mul]
        have e2 : σ w * ((σ w)⁻¹ * hb i * (σ w)ᴴ⁻¹) * (σ w)ᴴ = hb i := by
          simp only [Matrix.mul_assoc]
          rw [Matrix.nonsing_inv_mul _ hyHu, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hyu,
            Matrix.one_mul]
        rw [e2]
        ext a b
        simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
        push_cast
        ring
      rw [e, ← hOf_single, hcoV]
    have hFD := hF n (E.V →L[ℂ] E.V) σ (Gf Fr k Γ T c d (σ v)) hσs hσ (Gf_smooth h hk c hd hx)
      (Gf_inv h hkK c hd hx) w hw (σ w) hy (hσ w hw) _ hXh
    rw [hdir] at hFD
    rw [hFD]
    exact h2 n lam E Fr ε ι S Γ T h k hk c d (σ v) hd hx (σ w) hy _ hXh
  have hsum : ∑ i, fderiv ℝ (Kc σ c Fr k Γ T d) (v, w) (0, Pi.single i 1) * ε (hb i) =
      wt c (σ w) • (Fr (σ v) * ((1 / 2 : ℂ) • ∑ i, Ψ (A i) * ε (A' i)) * Fr (σ w)⁻¹) := by
    rw [Finset.smul_sum, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hpart i, map_smul, real_smul_clm, smul_mul_assoc]
    congr 1
    rw [mul_assoc (Fr (σ v) * _) (Fr (σ w)⁻¹), frInvEps h hy (hher i), ← mul_assoc, mul_assoc (Fr (σ v)),
      smul_mul_assoc]
    have hc2 : (((1 / 2 : ℝ)) : ℂ) = (1 / 2 : ℂ) := by norm_num
    rw [hc2]
  rw [hsum, hD n E.V Ψ ε A A' hAh hA'h htr]
  have halg := algPsi hH hc h (k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹)) (fun X => Rd X k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹))
  have e : ∑ p, Ψ (hb p) * ε (hb p) =
      (∑ p, (Rd (hb p) k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹) * ε (hb p) -
        k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹) * ε (hb p) * fderiv ℝ Fr 1 (hb p))) * Γ * T := halg
  rw [e]
  have hwt : wt c (σ w) = (c : ℂ) * ((hOf w).det ^ n)⁻¹ := by simp only [wt]; rw [hσ w hw]
  rw [hwt]
  simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]

end PositivityTheory.RgBcC.LfSt.Kchain.KcHalf2
