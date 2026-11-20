import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.UniformExportStatement
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GramBasic

open Matrix Polynomial
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

section

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}

/- English proof (translation)
Rewrite using `[ct, ct, ct, Matrix.map_mul, Matrix.transpose_mul]`.
-/
private theorem ct_mul (c : R ≃ₐ[k] R) (M N : Matrix (Fin n) (Fin n) R) :
    ct c (M * N) = ct c N * ct c M := by
  rw [ct, ct, ct, Matrix.map_mul, Matrix.transpose_mul]

/- English proof (translation)
Use extensionality with `i j`. Establish `h` using `AlgEquiv.congr_fun hc (M i j)`. Rewrite `h` using `[pow_two, AlgEquiv.mul_apply]`. Simplify `h` using `[ct]`.
-/
private theorem ct_ct {c : R ≃ₐ[k] R} (hc : c ^ 2 = 1) (M : Matrix (Fin n) (Fin n) R) :
    ct c (ct c M) = M := by
  ext i j
  have h := AlgEquiv.congr_fun hc (M i j)
  rw [pow_two, AlgEquiv.mul_apply] at h
  simpa [ct] using h

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem th_inv_val (c : R ≃ₐ[k] R) (y : GL (Fin n) R) :
    ((th c y)⁻¹ : GL (Fin n) R).val = ct c y.val := rfl

/- English proof (translation)
Establish `h : (thConj c y d)⁻¹ = (th c y)⁻¹ * d⁻¹ * y`. Simplify using `[thConj, mul_assoc]`. Rewrite using `[h, Units.val_mul, Units.val_mul, th_inv_val]`.
-/
private theorem thConj_inv (c : R ≃ₐ[k] R) (y d : GL (Fin n) R) :
    ((thConj c y d)⁻¹ : GL (Fin n) R).val = ct c y.val * (d⁻¹ : GL (Fin n) R).val * y.val := by
  have h : (thConj c y d)⁻¹ = (th c y)⁻¹ * d⁻¹ * y := by
    simp [thConj, mul_assoc]
  rw [h, Units.val_mul, Units.val_mul, th_inv_val]

end

/- English proof (translation)
Introduce `k R _ _ _ A _ _ n b c hc g hg w hw`. Take `⟨hG1, -, hG3⟩` from `gramBasic k R A n b c hc`. Take `⟨hu, hinj, hcomm⟩` from `hG3 g hg`. Establish `hc2 : c ^ 2 = 1` using `hc.pow`. Establish `hio : ∀ x : A, io c A ((1 : R) ⊗ₜ[k] x) = (1 : R) ⊗ₜ[k] x` using `fun x => by simp [io]`.

Establish `hu1 : ∀ x : Aˣ, IsUnit ((1 : R) ⊗ₜ[k] (x : A))` using `fun x => x.isUnit.map (Algebra.TensorProduct.includeRight : A →ₐ[k] R ⊗[k] A)`. Establish `hs : ∀ x : Aˣ, IsUnit (((1 : R) ⊗ₜ[k] (x : A)) * w.val)` using `fun x => (hu1 x).mul w.isUnit`. Establish `hgs : ∀ x : Aˣ, io c A (((1 : R) ⊗ₜ[k] (x : A)) * w.val) = ((1 : R) ⊗ₜ[k] (x : A)) * w.val * g.val` using `fun x => by`. Rewrite using `[map_mul, hio, hw]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hct : ∀ x : Aˣ, ct c (gramL b (((1 : R) ⊗ₜ[k] (x : A)) * w.val)) = gramL b (((1 : R) ⊗ₜ[k] (x : A)) * w.val) * mat b g.val` using `fun x => by`. Rewrite using `[(hG1 _ g.val).2.2.1, hgs, (hG1 _ g.val).2.1]`. Establish `hcong : ∀ (z s : R ⊗[k] A), ct c (mat b z) * gramL b s * mat b z = gramL b (io c A z * s * z)` using `fun z s => by`. Rewrite using `[(hG1 s z).1, (hG1 _ z).2.1]`. Establish `hmm : ∀ u v : R ⊗[k] A, mat b (u * v) = mat b u * mat b v` using `fun u v => map_mul (Algebra.leftMulMatrix (Algebra.TensorProduct.basis R b)) u v`.

Establish `hm1 : mat b (1 : R ⊗[k] A) = 1` using `map_one (Algebra.leftMulMatrix (Algebra.TensorProduct.basis R b))`. Establish `hminj : Function.Injective (mat (R` using `R) b) := Algebra.leftMulMatrix_injective _`. Establish `hdiv : ∀ x x' : Aˣ, (1 : R) ⊗ₜ[k] (x' : A) = ((1 : R) ⊗ₜ[k] ((x' / x : Aˣ) : A)) * ((1 : R) ⊗ₜ[k] (x : A))` using `fun x x' => by`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Units.val_mul, div_mul_cancel]`. Use `⟨fun x => ?_, fun x x' d d' hd hd' => ⟨?_, fun y => ?_⟩⟩` and prove the remaining obligations.

Establish `hdet : IsUnit (gramL b (((1 : R) ⊗ₜ[k] (x : A)) * w.val)).det`. Rewrite using `[(hG1 _ 1).2.2.2]`. Conclude with `((hs x).map (Algebra.norm R)).mul hu`. Use `⟨(Matrix.nonsingInvUnit _ hdet)⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[inv_inv]`.

Both sides reduce to the same expression. Use `Units.ext ?_` and prove the remaining obligations. Establish `h1 : (th c d).val = ct c (d⁻¹ : GL (Fin n) R).val` using `rfl`. Rewrite using `[Units.val_mul, h1, hd, hct, ← hd, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]`. Both sides reduce to the same expression.

Establish `hiff : d' = thConj c y d ↔ gramL b (((1 : R) ⊗ₜ[k] (x' : A)) * w.val) = ct c y.val * gramL b (((1 : R) ⊗ₜ[k] (x : A)) * w.val) * y.val`. Rewrite using `[← hd, ← hd', ← thConj_inv, ← inv_inj (a := d'), Units.ext_iff]`. Rewrite using `[hiff]`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Establish `hyM : y.val * mat b g.val = mat b g.val * y.val`. Establish `h1` using `congrArg (ct c) hy`. Rewrite `h1` using `[hct, ct_mul, ct_mul, ct_ct hc2, hct, hy]`. Establish `hU : IsUnit (ct c y.val * gramL b (((1 : R) ⊗ₜ[k] (x : A)) * w.val))`. Rewrite using `[← hd, ← th_inv_val, ← Units.val_mul]`.

Conclude with `Units.isUnit _`. Use `hU.mul_left_cancel ?_` and prove the remaining obligations. Establish `h2 : ct c y.val * gramL b (((1 : R) ⊗ₜ[k] (x : A)) * w.val) * (y.val * mat b g.val) = ct c y.val * (gramL b (((1 : R) ⊗ₜ[k] (x : A)) * w.val) * mat b g.val) * y.val`. Simplify `h1` using `only [mul_assoc]`. Rewrite using `[h2]`.

Simplify using `only [mul_assoc]`. Establish `hyM' : (y⁻¹ : GL (Fin n) R).val * mat b g.val = mat b g.val * (y⁻¹ : GL (Fin n) R).val`. Establish `e1 : (y⁻¹ : GL (Fin n) R).val * y.val = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `e2 : y.val * (y⁻¹ : GL (Fin n) R).val = 1`.

Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e2, mul_one]`. Use `_ = (y⁻¹ : GL (Fin n) R).val * (y.val * mat b g.val) * (y⁻¹ : GL (Fin n) R).val := by`. Rewrite using `[hyM]`.

Simplify using `only [mul_assoc]`. Use `_ = mat b g.val * (y⁻¹ : GL (Fin n) R).val := by`. Rewrite using `[← mul_assoc, e1, one_mul]`. Take `⟨z, hz⟩` from `hcomm y.val hyM`. Take `⟨z', hz'⟩` from `hcomm _ hyM'`.

Establish `hzz : z * z' = 1` using `hminj (by`. Rewrite using `[hmm, hm1, ← hz, ← hz', ← Units.val_mul, mul_inv_cancel, Units.val_one])`. Establish `hzz' : z' * z = 1` using `by rw [mul_comm, hzz]`. Use `⟨⟨z, z', hzz, hzz'⟩, Units.ext hz, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(1 : R) ⊗ₜ[k] ((x' / x : Aˣ) : A) = z * io c A z`.

Rewrite `hy` using `[hz, hcong]`. Establish `h3` using `hinj hy`. Rewrite `h3` using `[hdiv x x']`. Use `(hs x).mul_right_cancel ?_` and prove the remaining obligations. Rewrite `h3` using `[← mul_assoc]`.

Rewrite using `[← mul_assoc, h3]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨z, rfl, hz⟩`. Express the relevant statement in the definitionally equal form `_ = ct c (mat b z.val) * _ * mat b z.val`. Rewrite using `[hcong, hdiv x x', hz]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tIso : TIso := by
  intro k R _ _ _ A _ _ n b c hc g hg w hw
  obtain ⟨hG1, -, hG3⟩ := gramBasic k R A n b c hc
  obtain ⟨hu, hinj, hcomm⟩ := hG3 g hg
  have hc2 : c ^ 2 = 1 := hc.pow
  have hio : ∀ x : A, io c A ((1 : R) ⊗ₜ[k] x) = (1 : R) ⊗ₜ[k] x := fun x => by simp [io]
  have hu1 : ∀ x : Aˣ, IsUnit ((1 : R) ⊗ₜ[k] (x : A)) := fun x =>
    x.isUnit.map (Algebra.TensorProduct.includeRight : A →ₐ[k] R ⊗[k] A)
  have hs : ∀ x : Aˣ, IsUnit (((1 : R) ⊗ₜ[k] (x : A)) * w.val) := fun x => (hu1 x).mul w.isUnit
  have hgs : ∀ x : Aˣ, io c A (((1 : R) ⊗ₜ[k] (x : A)) * w.val) =
      ((1 : R) ⊗ₜ[k] (x : A)) * w.val * g.val := fun x => by
    rw [map_mul, hio, hw]; ring
  have hct : ∀ x : Aˣ, ct c (gramL b (((1 : R) ⊗ₜ[k] (x : A)) * w.val)) =
      gramL b (((1 : R) ⊗ₜ[k] (x : A)) * w.val) * mat b g.val := fun x => by
    rw [(hG1 _ g.val).2.2.1, hgs, (hG1 _ g.val).2.1]
  have hcong : ∀ (z s : R ⊗[k] A), ct c (mat b z) * gramL b s * mat b z =
      gramL b (io c A z * s * z) := fun z s => by
    rw [(hG1 s z).1, (hG1 _ z).2.1]
  have hmm : ∀ u v : R ⊗[k] A, mat b (u * v) = mat b u * mat b v := fun u v =>
    map_mul (Algebra.leftMulMatrix (Algebra.TensorProduct.basis R b)) u v
  have hm1 : mat b (1 : R ⊗[k] A) = 1 :=
    map_one (Algebra.leftMulMatrix (Algebra.TensorProduct.basis R b))
  have hminj : Function.Injective (mat (R := R) b) := Algebra.leftMulMatrix_injective _
  have hdiv : ∀ x x' : Aˣ, (1 : R) ⊗ₜ[k] (x' : A) =
      ((1 : R) ⊗ₜ[k] ((x' / x : Aˣ) : A)) * ((1 : R) ⊗ₜ[k] (x : A)) := fun x x' => by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Units.val_mul, div_mul_cancel]
  refine ⟨fun x => ?_, fun x x' d d' hd hd' => ⟨?_, fun y => ?_⟩⟩
  · have hdet : IsUnit (gramL b (((1 : R) ⊗ₜ[k] (x : A)) * w.val)).det := by
      rw [(hG1 _ 1).2.2.2]
      exact ((hs x).map (Algebra.norm R)).mul hu
    refine ⟨(Matrix.nonsingInvUnit _ hdet)⁻¹, ?_⟩
    rw [inv_inv]
    rfl
  · refine Units.ext ?_
    have h1 : (th c d).val = ct c (d⁻¹ : GL (Fin n) R).val := rfl
    rw [Units.val_mul, h1, hd, hct, ← hd, ← mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, one_mul]
    rfl
  · have hiff : d' = thConj c y d ↔
        gramL b (((1 : R) ⊗ₜ[k] (x' : A)) * w.val) =
          ct c y.val * gramL b (((1 : R) ⊗ₜ[k] (x : A)) * w.val) * y.val := by
      rw [← hd, ← hd', ← thConj_inv, ← inv_inj (a := d'), Units.ext_iff]
    rw [hiff]
    constructor
    · intro hy
      have hyM : y.val * mat b g.val = mat b g.val * y.val := by
        have h1 := congrArg (ct c) hy
        rw [hct, ct_mul, ct_mul, ct_ct hc2, hct, hy] at h1
        have hU : IsUnit (ct c y.val * gramL b (((1 : R) ⊗ₜ[k] (x : A)) * w.val)) := by
          rw [← hd, ← th_inv_val, ← Units.val_mul]
          exact Units.isUnit _
        refine hU.mul_left_cancel ?_
        have h2 : ct c y.val * gramL b (((1 : R) ⊗ₜ[k] (x : A)) * w.val) * (y.val * mat b g.val) =
            ct c y.val * (gramL b (((1 : R) ⊗ₜ[k] (x : A)) * w.val) * mat b g.val) * y.val := by
          simpa only [mul_assoc] using h1
        rw [h2]
        simp only [mul_assoc]
      have hyM' : (y⁻¹ : GL (Fin n) R).val * mat b g.val = mat b g.val * (y⁻¹ : GL (Fin n) R).val := by
        have e1 : (y⁻¹ : GL (Fin n) R).val * y.val = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        have e2 : y.val * (y⁻¹ : GL (Fin n) R).val = 1 := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        calc (y⁻¹ : GL (Fin n) R).val * mat b g.val
            = (y⁻¹ : GL (Fin n) R).val * (mat b g.val * (y.val * (y⁻¹ : GL (Fin n) R).val)) := by
              rw [e2, mul_one]
          _ = (y⁻¹ : GL (Fin n) R).val * (y.val * mat b g.val) * (y⁻¹ : GL (Fin n) R).val := by
              rw [hyM]; simp only [mul_assoc]
          _ = mat b g.val * (y⁻¹ : GL (Fin n) R).val := by
              rw [← mul_assoc, e1, one_mul]
      obtain ⟨z, hz⟩ := hcomm y.val hyM
      obtain ⟨z', hz'⟩ := hcomm _ hyM'
      have hzz : z * z' = 1 := hminj (by
        rw [hmm, hm1, ← hz, ← hz', ← Units.val_mul, mul_inv_cancel, Units.val_one])
      have hzz' : z' * z = 1 := by rw [mul_comm, hzz]
      refine ⟨⟨z, z', hzz, hzz'⟩, Units.ext hz, ?_⟩
      change (1 : R) ⊗ₜ[k] ((x' / x : Aˣ) : A) = z * io c A z
      rw [hz, hcong] at hy
      have h3 := hinj hy
      rw [hdiv x x'] at h3
      refine (hs x).mul_right_cancel ?_
      rw [← mul_assoc] at h3
      rw [← mul_assoc, h3]
      ring
    · rintro ⟨z, rfl, hz⟩
      change _ = ct c (mat b z.val) * _ * mat b z.val
      rw [hcong, hdiv x x', hz]
      congr 1
      ring

end UpperTheory.ConvolutionTheory.D
