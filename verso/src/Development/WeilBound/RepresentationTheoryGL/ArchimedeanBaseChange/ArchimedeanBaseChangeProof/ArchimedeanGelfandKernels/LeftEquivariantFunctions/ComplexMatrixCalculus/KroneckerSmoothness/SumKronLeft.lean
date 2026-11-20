import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.EigOf

noncomputable section

open Matrix
open scoped Kronecker ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC.Cxh

open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {lam : Fin n → ℤ}

def cjC (lam : Fin n → ℤ) : Matrix (Ix n lam) (Ix n lam) ℂ →L[ℝ] (EV n lam →L[ℂ] EV n lam) :=
  LinearMap.toContinuousLinearMap ((cjL lam).restrictScalars ℝ)

/- English proof (translation)
Establish `h : lefFr n lam = (cjC lam) ∘ fr0 lam` using `rfl`. Establish `h2` using `((cjC lam).hasFDerivAt.comp (1 : Mat n) hd.hasFDerivAt).fderiv`. Rewrite using `[h]`. Conclude with `congrFun (congrArg DFunLike.coe h2) X`.
-/
theorem fderiv_lefFr (hd : DifferentiableAt ℝ (fr0 lam) (1 : Mat n)) (X : Mat n) :
    fderiv ℝ (lefFr n lam) 1 X = cjL lam (fderiv ℝ (fr0 lam) 1 X) := by
  have h : lefFr n lam = (cjC lam) ∘ fr0 lam := rfl
  have h2 := ((cjC lam).hasFDerivAt.comp (1 : Mat n) hd.hasFDerivAt).fderiv
  rw [h]
  exact congrFun (congrArg DFunLike.coe h2) X

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul]`.
-/
theorem sum_kron_left {ι κ μ : Type*} [Fintype κ] [Fintype μ] (s : Finset ι) (A : ι → Matrix κ κ ℂ)
    (B : Matrix μ μ ℂ) : (∑ i ∈ s, A i) ⊗ₖ B = ∑ i ∈ s, A i ⊗ₖ B := by
  ext a b
  simp [kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[kroneckerMap_apply]`.
-/
theorem kron_neg' {κ μ : Type*} (A : Matrix κ κ ℂ) (B : Matrix μ μ ℂ) : A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  ext a b; simp [kroneckerMap_apply]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[kroneckerMap_apply]`.
-/
theorem zero_kron {κ μ : Type*} (B : Matrix μ μ ℂ) : (0 : Matrix κ κ ℂ) ⊗ₖ B = 0 := by
  ext a b; simp [kroneckerMap_apply]

/- English proof (translation)
Simplify using `[hbM]`.
-/
theorem hb_eq (p : Fin n × Fin n) : hb p = hbM (finProdFinEquiv p) := by
  simp [hbM]

end PositivityTheory.RgBcC.Cxh

namespace PositivityTheory.RgBcC

open Cxh
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

set_option maxHeartbeats 800000 in
/- English proof (translation)
Introduce `hAvg hOr hSw hFr hWd n lam`. Take `⟨hu, -, -, -, -⟩` from `hAvg n lam`. Take `⟨-, -, -, hsw, -⟩` from `hSw n lam`. Take `⟨hd, hfr⟩` from `hFr n lam`. Establish `hmul : ∀ A B : Matrix (Ix n lam) (Ix n lam) ℂ, cjL lam A * cjL lam B = cjL lam (A * B)`.

Introduce `A B`. Establish `hc : clm lam (A * B) = clm lam A * clm lam B` using `map_mul Matrix.toEuclideanCLM A B`. Establish `hi : Ring.inverse (sqQ lam) * sqQ lam = 1` using `Ring.inverse_mul_cancel _ hu`. Express the relevant statement in the definitionally equal form `sqQ lam * (clm lam A * Ring.inverse (sqQ lam)) * (sqQ lam * (clm lam B * Ring.inverse (sqQ lam))) = sqQ lam * (clm lam (A * B) * Ring.inverse (sqQ lam))`. Rewrite using `[hc]`.

Simplify using `only [mul_assoc]`. Rewrite using `[← mul_assoc (Ring.inverse (sqQ lam)) (sqQ lam), hi, one_mul]`. Establish `hherm : ∀ p : Fin n × Fin n, (hb p).IsHermitian` using `fun p => by`. Rewrite using `[hb_eq]`. Conclude with `(hOr n).2 _`.

Set `C : Fin n × Fin n → Matrix (Finset (Md n)) (Finset (Md n)) ℂ` to `fun p => creL n (cf n (hb p))`. Set `G : Fin n × Fin n → Matrix (Finset (Md n)) (Finset (Md n)) ℂ` to `fun p => fderiv ℝ (fun x : Mat n => gamM (Mt x⁻¹)ᵀ) 1 (hb p)`. Set `R : Fin n × Fin n → Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ` to `fun p => fderiv ℝ (rhoW lam) 1 (hb p)`. Establish `hw : ∑ p, C p * G p = 0` using `hWd n`. Establish `e1 : ∀ p, lefε n lam (hb p) * fderiv ℝ (lefFr n lam) 1 (hb p) = cjL lam ((C p * G p) ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ) + C p ⊗ₖ R p)`.

Introduce `p`. Rewrite using `[fderiv_lefFr hd, hfr _ (hherm p)]`. Express the relevant statement in the definitionally equal form `cjL lam (C p ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ)) * cjL lam (G p ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ) + (1 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ) ⊗ₖ R p) = _`. Rewrite using `[hmul, Matrix.mul_add, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]`. Simplify using `only [Matrix.mul_one, Matrix.one_mul]`.

Establish `hS : ∑ p, lefε n lam (hb p) * fderiv ℝ (lefFr n lam) 1 (hb p) = cjL lam (∑ p, C p ⊗ₖ R p)`. Rewrite using `[Finset.sum_congr rfl (fun p _ => e1 p), ← map_sum, Finset.sum_add_distrib, ← sum_kron_left, hw, zero_kron, zero_add]`. Rewrite using `[hS]`. Express the relevant statement in the definitionally equal form `cjL lam ((1 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ) ⊗ₖ swapJ lam) * _ = -(_ * cjL lam ((1 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ) ⊗ₖ swapJ lam))`. Rewrite using `[hmul, hmul, ← map_neg]`.

Use `congrArg (cjL lam) ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, show swapJ lam * R p = -(R p * swapJ lam) from hsw _ (hherm p), Matrix.one_mul, Matrix.mul_one, kron_neg']`.
-/
theorem tdOf : TDOf := by
  intro hAvg hOr hSw hFr hWd n lam
  obtain ⟨hu, -, -, -, -⟩ := hAvg n lam
  obtain ⟨-, -, -, hsw, -⟩ := hSw n lam
  obtain ⟨hd, hfr⟩ := hFr n lam
  have hmul : ∀ A B : Matrix (Ix n lam) (Ix n lam) ℂ, cjL lam A * cjL lam B = cjL lam (A * B) := by
    intro A B
    have hc : clm lam (A * B) = clm lam A * clm lam B := map_mul Matrix.toEuclideanCLM A B
    have hi : Ring.inverse (sqQ lam) * sqQ lam = 1 := Ring.inverse_mul_cancel _ hu
    change sqQ lam * (clm lam A * Ring.inverse (sqQ lam)) * (sqQ lam * (clm lam B * Ring.inverse (sqQ lam))) =
      sqQ lam * (clm lam (A * B) * Ring.inverse (sqQ lam))
    rw [hc]
    simp only [mul_assoc]
    rw [← mul_assoc (Ring.inverse (sqQ lam)) (sqQ lam), hi, one_mul]
  have hherm : ∀ p : Fin n × Fin n, (hb p).IsHermitian := fun p => by
    rw [hb_eq]
    exact (hOr n).2 _
  let C : Fin n × Fin n → Matrix (Finset (Md n)) (Finset (Md n)) ℂ := fun p => creL n (cf n (hb p))
  let G : Fin n × Fin n → Matrix (Finset (Md n)) (Finset (Md n)) ℂ := fun p =>
    fderiv ℝ (fun x : Mat n => gamM (Mt x⁻¹)ᵀ) 1 (hb p)
  let R : Fin n × Fin n → Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ := fun p =>
    fderiv ℝ (rhoW lam) 1 (hb p)
  have hw : ∑ p, C p * G p = 0 := hWd n
  have e1 : ∀ p, lefε n lam (hb p) * fderiv ℝ (lefFr n lam) 1 (hb p) =
      cjL lam ((C p * G p) ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ) + C p ⊗ₖ R p) := by
    intro p
    rw [fderiv_lefFr hd, hfr _ (hherm p)]
    change cjL lam (C p ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ)) *
      cjL lam (G p ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ) +
        (1 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ) ⊗ₖ R p) = _
    rw [hmul, Matrix.mul_add, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp only [Matrix.mul_one, Matrix.one_mul]
  have hS : ∑ p, lefε n lam (hb p) * fderiv ℝ (lefFr n lam) 1 (hb p) = cjL lam (∑ p, C p ⊗ₖ R p) := by
    rw [Finset.sum_congr rfl (fun p _ => e1 p), ← map_sum, Finset.sum_add_distrib, ← sum_kron_left, hw,
      zero_kron, zero_add]
  rw [hS]
  change cjL lam ((1 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ) ⊗ₖ swapJ lam) * _ =
    -(_ * cjL lam ((1 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ) ⊗ₖ swapJ lam))
  rw [hmul, hmul, ← map_neg]
  refine congrArg (cjL lam) ?_
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    show swapJ lam * R p = -(R p * swapJ lam) from hsw _ (hherm p), Matrix.one_mul, Matrix.mul_one, kron_neg']
