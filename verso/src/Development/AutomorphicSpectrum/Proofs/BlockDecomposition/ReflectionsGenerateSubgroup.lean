import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.SaGen.PairList

open Matrix

variable {R : Type} [CommRing R] {M : ℕ}

def wv (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (a : Fin M → R) : Fin M → R :=
  fun j => ∑ i, c (a i) * Jm i j

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem qr_eq (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (a : Fin M → R) (k : R) :
    qr c Jm a k = 1 + k • vecMulVec a (wv c Jm a) := rfl

/- English proof (translation)
Simplify using `only [Formalism.UG.hform, wv, dotProduct, Finset.sum_mul]`. Conclude with `Finset.sum_comm`.
-/
theorem hform_eq (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (x y : Fin M → R) :
    Formalism.UG.hform c Jm x y = wv c Jm x ⬝ᵥ y := by
  simp only [Formalism.UG.hform, wv, dotProduct, Finset.sum_mul]
  exact Finset.sum_comm

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, vecMulVec_apply, mulVec, dotProduct, Finset.sum_mul, mul_assoc]`.
-/
theorem mat_mul_vmv (A : Matrix (Fin M) (Fin M) R) (u v : Fin M → R) :
    A * vecMulVec u v = vecMulVec (A *ᵥ u) v := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, mulVec, dotProduct, Finset.sum_mul, mul_assoc]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, vecMulVec_apply, vecMul, dotProduct, Finset.mul_sum, mul_assoc]`.
-/
theorem vmv_mul_mat (A : Matrix (Fin M) (Fin M) R) (u v : Fin M → R) :
    vecMulVec u v * A = vecMulVec u (v ᵥ* A) := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, vecMul, dotProduct, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, vecMulVec_apply, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun l _ => by ring`.
-/
theorem vmv_mul_vmv (u v x y : Fin M → R) :
    vecMulVec u v * vecMulVec x y = (v ⬝ᵥ x) • vecMulVec u y := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/- English proof (translation)
Simplify using `only [qr_eq]`. Establish `h` using `vmv_mul_vmv a (wv c Jm a) a (wv c Jm a)`. Rewrite `h` using `[← hform_eq]`. Rewrite using `[add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, smul_mul_smul_comm, h]`. Use `module`.
-/
theorem qr_mul (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (a : Fin M → R) (k₁ k₂ : R) :
    qr c Jm a k₁ * qr c Jm a k₂ = qr c Jm a (k₁ + k₂ + k₁ * k₂ * Formalism.UG.hform c Jm a a) := by
  simp only [qr_eq]
  have h := vmv_mul_vmv a (wv c Jm a) a (wv c Jm a)
  rw [← hform_eq] at h
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, smul_mul_smul_comm, h]
  module

/- English proof (translation)
Simplify using `[qr_eq]`.
-/
theorem qr_zero (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (a : Fin M → R) : qr c Jm a 0 = 1 := by
  simp [qr_eq]

/- English proof (translation)
Establish `h : k • vecMulVec a (wv c Jm a) = replicateCol Unit (k • a) * replicateRow Unit (wv c Jm a)`. Rewrite using `[← vecMulVec_eq]`. Use extensionality with `i j`. Simplify using `[vecMulVec_apply, mul_assoc]`. Rewrite using `[qr_eq, h, det_one_add_replicateCol_mul_replicateRow, hform_eq, dotProduct_smul, smul_eq_mul]`.
-/
theorem det_qr (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (a : Fin M → R) (k : R) :
    (qr c Jm a k).det = 1 + k * Formalism.UG.hform c Jm a a := by
  have h : k • vecMulVec a (wv c Jm a) =
      replicateCol Unit (k • a) * replicateRow Unit (wv c Jm a) := by
    rw [← vecMulVec_eq]
    ext i j
    simp [vecMulVec_apply, mul_assoc]
  rw [qr_eq, h, det_one_add_replicateCol_mul_replicateRow, hform_eq, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Establish `h1 : Formalism.UG.cT c (g : Matrix (Fin M) (Fin M) R) * Jm = Jm * ((g⁻¹ : GL (Fin M) R) : Matrix (Fin M) (Fin M) R)`. Establish `hg' : Formalism.UG.cT c (g : Matrix (Fin M) (Fin M) R) * Jm * (g : Matrix (Fin M) (Fin M) R) = Jm` using `hg`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]`. Use `_ = _ := by rw [← Matrix.mul_assoc, hg']`.

Establish `h2 : ∀ x : Fin M → R, wv c Jm x = (fun i => c (x i)) ᵥ* Jm` using `fun x => by`. Use extensionality with `j`. Simplify using `[wv, vecMul, dotProduct]`. Establish `h3 : (fun i => c (((g : Matrix (Fin M) (Fin M) R) *ᵥ a) i)) = (fun i => c (a i)) ᵥ* Formalism.UG.cT c (g : Matrix (Fin M) (Fin M) R)`. Use extensionality with `i`.

Simplify using `[mulVec, vecMul, dotProduct, Formalism.UG.cT, map_sum, mul_comm]`. Rewrite using `[h2, h2, h3, vecMul_vecMul, h1, vecMul_vecMul]`.
-/
theorem wv_mulVec (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (g : GL (Fin M) R)
    (hg : g ∈ Formalism.UG.UJ c Jm) (a : Fin M → R) :
    wv c Jm ((g : Matrix (Fin M) (Fin M) R) *ᵥ a) = wv c Jm a ᵥ* ((g⁻¹ : GL (Fin M) R) : Matrix (Fin M) (Fin M) R) := by
  have h1 : Formalism.UG.cT c (g : Matrix (Fin M) (Fin M) R) * Jm =
      Jm * ((g⁻¹ : GL (Fin M) R) : Matrix (Fin M) (Fin M) R) := by
    have hg' : Formalism.UG.cT c (g : Matrix (Fin M) (Fin M) R) * Jm * (g : Matrix (Fin M) (Fin M) R) = Jm := hg
    calc _ = Formalism.UG.cT c (g : Matrix (Fin M) (Fin M) R) * Jm * ((g : Matrix (Fin M) (Fin M) R) *
            ((g⁻¹ : GL (Fin M) R) : Matrix (Fin M) (Fin M) R)) := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hg']
  have h2 : ∀ x : Fin M → R, wv c Jm x = (fun i => c (x i)) ᵥ* Jm := fun x => by
    ext j; simp [wv, vecMul, dotProduct]
  have h3 : (fun i => c (((g : Matrix (Fin M) (Fin M) R) *ᵥ a) i)) =
      (fun i => c (a i)) ᵥ* Formalism.UG.cT c (g : Matrix (Fin M) (Fin M) R) := by
    ext i
    simp [mulVec, vecMul, dotProduct, Formalism.UG.cT, map_sum, mul_comm]
  rw [h2, h2, h3, vecMul_vecMul, h1, vecMul_vecMul]

/- English proof (translation)
Rewrite using `[qr_eq, qr_eq, wv_mulVec c Jm g hg, mul_add, add_mul, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_smul, Matrix.smul_mul, mat_mul_vmv, vmv_mul_mat]`.
-/
theorem conj_qr (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (g : GL (Fin M) R)
    (hg : g ∈ Formalism.UG.UJ c Jm) (a : Fin M → R) (k : R) :
    (g : Matrix (Fin M) (Fin M) R) * qr c Jm a k * ((g⁻¹ : GL (Fin M) R) : Matrix (Fin M) (Fin M) R) =
      qr c Jm ((g : Matrix (Fin M) (Fin M) R) *ᵥ a) k := by
  rw [qr_eq, qr_eq, wv_mulVec c Jm g hg, mul_add, add_mul, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.mul_smul, Matrix.smul_mul, mat_mul_vmv, vmv_mul_mat]

/- English proof (translation)
Rewrite using `[hform_eq, hform_eq, wv_mulVec c Jm g hg, ← dotProduct_mulVec, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]`.
-/
theorem hform_mulVec (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (g : GL (Fin M) R)
    (hg : g ∈ Formalism.UG.UJ c Jm) (a : Fin M → R) :
    Formalism.UG.hform c Jm ((g : Matrix (Fin M) (Fin M) R) *ᵥ a) ((g : Matrix (Fin M) (Fin M) R) *ᵥ a) =
      Formalism.UG.hform c Jm a a := by
  rw [hform_eq, hform_eq, wv_mulVec c Jm g hg, ← dotProduct_mulVec, mulVec_mulVec, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, one_mulVec]

/- English proof (translation)
Simplify using `only [Formalism.UG.hform, map_sum, map_mul, hc, hJ]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem hform_self_fixed (c : R →+* R) (hc : ∀ x, c (c x) = x) (Jm : Matrix (Fin M) (Fin M) R)
    (hJ : ∀ i j, c (Jm j i) = Jm i j) (a : Fin M → R) :
    c (Formalism.UG.hform c Jm a a) = Formalism.UG.hform c Jm a a := by
  simp only [Formalism.UG.hform, map_sum, map_mul, hc, hJ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Use `set w := wv c Jm a with hw`. Use `set u := Jm *ᵥ a with hu`. Establish `hcT : Formalism.UG.cT c (qr c Jm a k) = 1 + c k • vecMulVec u (fun i => c (a i))`. Use extensionality with `i j`. Establish `hcw : c (w i) = u i`.

Simplify using `only [hw, hu, wv, map_sum, map_mul, hc, hJ, mulVec, dotProduct]`. Conclude with `Finset.sum_congr rfl fun l _ => mul_comm _ _`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[Formalism.UG.cT, qr_eq, ← hw, vecMulVec_apply, hcw, mul_assoc, mul_comm]`.

Establish `hji : j ≠ i` using `fun h => hij h.symm`. Simplify using `[Formalism.UG.cT, qr_eq, ← hw, vecMulVec_apply, hcw, Matrix.one_apply, hij, hji, mul_assoc, mul_comm]`. Establish `hw' : (fun i => c (a i)) ᵥ* Jm = w`. Use extensionality with `j`. Simplify using `[hw, wv, vecMul, dotProduct]`.

Establish `h1 : vecMulVec u (fun i => c (a i)) * Jm = vecMulVec u w` using `by rw [vmv_mul_mat, hw']`. Establish `h2 : Jm * vecMulVec a w = vecMulVec u w` using `by rw [mat_mul_vmv]`. Establish `h3 : vecMulVec u w * vecMulVec a w = Formalism.UG.hform c Jm a a • vecMulVec u w`. Rewrite using `[vmv_mul_vmv, hw, ← hform_eq]`. Rewrite using `[hcT, qr_eq, ← hw, add_mul, one_mul, Matrix.smul_mul, h1, add_mul, mul_add, Matrix.mul_one, Matrix.mul_smul, h2, Matrix.smul_mul, mul_add, Matrix.mul_one, Matrix.mul_smul, h3]`.

Establish `: Jm + k • vecMulVec u w + c k • (vecMulVec u w + k • Formalism.UG.hform c Jm a a • vecMulVec u w) = Jm + (k + c k + c k * k * Formalism.UG.hform c Jm a a) • vecMulVec u w` using `by module`. Rewrite using `[this, hk, zero_smul, add_zero]`.
-/
theorem qr_unitary (c : R →+* R) (hc : ∀ x, c (c x) = x) (Jm : Matrix (Fin M) (Fin M) R)
    (hJ : ∀ i j, c (Jm j i) = Jm i j) (a : Fin M → R) (k : R)
    (hk : k + c k + c k * k * Formalism.UG.hform c Jm a a = 0) :
    Formalism.UG.cT c (qr c Jm a k) * Jm * qr c Jm a k = Jm := by
  set w := wv c Jm a with hw
  set u := Jm *ᵥ a with hu
  have hcT : Formalism.UG.cT c (qr c Jm a k) = 1 + c k • vecMulVec u (fun i => c (a i)) := by
    ext i j
    have hcw : c (w i) = u i := by
      simp only [hw, hu, wv, map_sum, map_mul, hc, hJ, mulVec, dotProduct]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    by_cases hij : i = j
    · subst hij
      simp [Formalism.UG.cT, qr_eq, ← hw, vecMulVec_apply, hcw, mul_assoc, mul_comm]
    · have hji : j ≠ i := fun h => hij h.symm
      simp [Formalism.UG.cT, qr_eq, ← hw, vecMulVec_apply, hcw, Matrix.one_apply, hij, hji, mul_assoc, mul_comm]
  have hw' : (fun i => c (a i)) ᵥ* Jm = w := by
    ext j; simp [hw, wv, vecMul, dotProduct]
  have h1 : vecMulVec u (fun i => c (a i)) * Jm = vecMulVec u w := by rw [vmv_mul_mat, hw']
  have h2 : Jm * vecMulVec a w = vecMulVec u w := by rw [mat_mul_vmv]
  have h3 : vecMulVec u w * vecMulVec a w = Formalism.UG.hform c Jm a a • vecMulVec u w := by
    rw [vmv_mul_vmv, hw, ← hform_eq]
  rw [hcT, qr_eq, ← hw, add_mul, one_mul, Matrix.smul_mul, h1, add_mul, mul_add, Matrix.mul_one, Matrix.mul_smul,
    h2, Matrix.smul_mul, mul_add, Matrix.mul_one, Matrix.mul_smul, h3]
  have : Jm + k • vecMulVec u w + c k • (vecMulVec u w + k • Formalism.UG.hform c Jm a a • vecMulVec u w)
      = Jm + (k + c k + c k * k * Formalism.UG.hform c Jm a a) • vecMulVec u w := by module
  rw [this, hk, zero_smul, add_zero]

/- English proof (translation)
Establish `h1 : c k * n = c l - 1`. Use `congrArg c hk` as an intermediate fact. Rewrite `this` using `[map_mul, hcn, map_sub, map_one]`. Then use the resulting hypothesis. Apply `hn.mul_right_cancel` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
-/
theorem num_cond (c : R →+* R) {n k l : R} (hn : IsUnit n) (hcn : c n = n) (hl : l * c l = 1)
    (hk : k * n = l - 1) : k + c k + c k * k * n = 0 := by
  have h1 : c k * n = c l - 1 := by
    have := congrArg c hk
    rwa [map_mul, hcn, map_sub, map_one] at this
  apply hn.mul_right_cancel
  calc (k + c k + c k * k * n) * n = k * n + c k * n + (c k * n) * (k * n) := by ring
    _ = l * c l - 1 := by rw [hk, h1]; ring
    _ = 0 * n := by rw [hl]; ring

/- English proof (translation)
Establish `hz : (μ - 1) * n' + (c μ - 1) * n' + (μ - 1) * n' * ((c μ - 1) * n') * Formalism.UG.hform c Jm a₀ a₀ = 0`. Take the linear combination `n' * hμ + n' * (μ - 1) * (c μ - 1) * hn'`. Establish `hz' : (c μ - 1) * n' + (μ - 1) * n' + (c μ - 1) * n' * ((μ - 1) * n') * Formalism.UG.hform c Jm a₀ a₀ = 0`. Take the linear combination `n' * hμ + n' * (μ - 1) * (c μ - 1) * hn'`. Establish `hu : IsUnit (Formalism.UG.hform c Jm a₀ a₀)` using `IsUnit.of_mul_eq_one n' (by rw [mul_comm]; exact hn')`.

Use `⟨⟨qr c Jm a₀ ((μ - 1) * n'), qr c Jm a₀ ((c μ - 1) * n'), ?_, ?_⟩, ?_, rfl, rfl⟩` and prove the remaining obligations. Rewrite using `[qr_mul, hz, qr_zero]`. Rewrite using `[qr_mul, hz', qr_zero]`. Use `qr_unitary c hc Jm hJ a₀ _ (num_cond c hu (hform_self_fixed c hc Jm hJ a₀) hμ ?_)` and prove the remaining obligations. Take the linear combination `(μ - 1) * hn'`.
-/
theorem tau_exists (c : R →+* R) (hc : ∀ x, c (c x) = x) (Jm : Matrix (Fin M) (Fin M) R)
    (hJ : ∀ i j, c (Jm j i) = Jm i j) (a₀ : Fin M → R) (n' : R)
    (hn' : n' * Formalism.UG.hform c Jm a₀ a₀ = 1) (μ : R) (hμ : μ * c μ = 1) :
    ∃ g : GL (Fin M) R, g ∈ Formalism.UG.UJ c Jm ∧
      (g : Matrix (Fin M) (Fin M) R) = qr c Jm a₀ ((μ - 1) * n') ∧
      ((g⁻¹ : GL (Fin M) R) : Matrix (Fin M) (Fin M) R) = qr c Jm a₀ ((c μ - 1) * n') := by
  have hz : (μ - 1) * n' + (c μ - 1) * n' + (μ - 1) * n' * ((c μ - 1) * n') * Formalism.UG.hform c Jm a₀ a₀ = 0 := by
    linear_combination n' * hμ + n' * (μ - 1) * (c μ - 1) * hn'
  have hz' : (c μ - 1) * n' + (μ - 1) * n' + (c μ - 1) * n' * ((μ - 1) * n') * Formalism.UG.hform c Jm a₀ a₀ = 0 := by
    linear_combination n' * hμ + n' * (μ - 1) * (c μ - 1) * hn'
  have hu : IsUnit (Formalism.UG.hform c Jm a₀ a₀) := IsUnit.of_mul_eq_one n' (by rw [mul_comm]; exact hn')
  refine ⟨⟨qr c Jm a₀ ((μ - 1) * n'), qr c Jm a₀ ((c μ - 1) * n'), ?_, ?_⟩, ?_, rfl, rfl⟩
  · rw [qr_mul, hz, qr_zero]
  · rw [qr_mul, hz', qr_zero]
  · refine qr_unitary c hc Jm hJ a₀ _ (num_cond c hu (hform_self_fixed c hc Jm hJ a₀) hμ ?_)
    linear_combination (μ - 1) * hn'

/- English proof (translation)
Establish `hu : IsUnit (Formalism.UG.hform c Jm a₀ a₀)` using `IsUnit.of_mul_eq_one n' (by rw [mul_comm]; exact hn')`. Proceed by induction on `l using List.reverseRecOn with`. Consider the case `nil`. Use `⟨1, H.one_mem, by simp, 1, by simp, 1, one_mem _, ?_, by simp⟩` and prove the remaining obligations. Simplify using `[qr_zero]`.

Consider the case `append_singleton l y ih`. Take `⟨h, hhH, hdet, μ, hμ, g, hgU, hg, hprod⟩` from `ih (fun z hz => hl z (List.mem_append_left _ hz))`. Take `⟨hyU, a, lam, k, ha, hlam, hk, hy⟩` from `hl y (by simp)`. Take `⟨gl, hglU, hgl, hgli⟩` from `tau_exists c hc Jm hJ a₀ n' hn' lam hlam`. Establish `hBU : g * y * gl⁻¹ * g⁻¹ ∈ Formalism.UG.UJ c Jm` using `mul_mem (mul_mem (mul_mem hgU hyU) (inv_mem hglU)) (inv_mem hgU)`.

Establish `hBmat : ((g * y * gl⁻¹ * g⁻¹ : GL (Fin M) R) : Matrix (Fin M) (Fin M) R) = qr c Jm ((g : Matrix (Fin M) (Fin M) R) *ᵥ a) k * qr c Jm ((g : Matrix (Fin M) (Fin M) R) *ᵥ a₀) ((c lam - 1) * n')`. Rewrite using `[← conj_qr c Jm g hgU, ← conj_qr c Jm g hgU, ← hy, ← hgli]`. Establish `: g * y * gl⁻¹ * g⁻¹ = (g * y * g⁻¹) * (g * gl⁻¹ * g⁻¹)` using `by group`. Rewrite using `[this]`. Simplify using `only [Units.val_mul]`.

Establish `hk' : k * Formalism.UG.hform c Jm ((g : Matrix (Fin M) (Fin M) R) *ᵥ a) ((g : Matrix (Fin M) (Fin M) R) *ᵥ a) = lam - 1`. Rewrite using `[hform_mulVec c Jm g hgU]`. Conclude with `hk`. Establish `hkb : (c lam - 1) * n' * Formalism.UG.hform c Jm ((g : Matrix (Fin M) (Fin M) R) *ᵥ a₀) ((g : Matrix (Fin M) (Fin M) R) *ᵥ a₀) = c lam - 1`. Rewrite using `[hform_mulVec c Jm g hgU]`.

Take the linear combination `(c lam - 1) * hn'`. Establish `hBH : g * y * gl⁻¹ * g⁻¹ ∈ H`. Use `hH _ hBU ⟨_, _, lam, k, (c lam - 1) * n', ?_, ?_, hlam, hk', hkb, hBmat⟩` and prove the remaining obligations. Rewrite using `[hform_mulVec c Jm g hgU]`. Conclude with `ha`.

Rewrite using `[hform_mulVec c Jm g hgU]`. Conclude with `hu`. Establish `hBdet : ((g * y * gl⁻¹ * g⁻¹ : GL (Fin M) R) : Matrix (Fin M) (Fin M) R).det = 1`. Rewrite using `[hBmat, Matrix.det_mul, det_qr, det_qr, hk', hkb]`. Take the linear combination `hlam`.

Use `⟨h * (g * y * gl⁻¹ * g⁻¹), mul_mem hhH hBH, ?_, μ * lam, ?_, g * gl, mul_mem hgU hglU, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, Matrix.det_mul, hdet, hBdet, one_mul]`. Rewrite using `[map_mul]`. Take the linear combination `(lam * c lam) * hμ + hlam`. Rewrite using `[Units.val_mul, hg, hgl, qr_mul]`.

Use `congr 1`. Take the linear combination `n' * (μ - 1) * (lam - 1) * hn'`. Rewrite using `[List.prod_append, hprod, List.prod_singleton] group`.
-/
theorem prod_claim (c : R →+* R) (hc : ∀ x, c (c x) = x) (Jm : Matrix (Fin M) (Fin M) R)
    (hJ : ∀ i j, c (Jm j i) = Jm i j) (a₀ : Fin M → R) (n' : R)
    (hn' : n' * Formalism.UG.hform c Jm a₀ a₀ = 1) (H : Subgroup (GL (Fin M) R))
    (hH : ∀ y ∈ Formalism.UG.UJ c Jm, IsQPair c Jm (y : Matrix (Fin M) (Fin M) R) → y ∈ H)
    (l : List (GL (Fin M) R))
    (hl : ∀ y ∈ l, y ∈ Formalism.UG.UJ c Jm ∧ IsQR c Jm (y : Matrix (Fin M) (Fin M) R)) :
    ∃ h ∈ H, (h : Matrix (Fin M) (Fin M) R).det = 1 ∧ ∃ μ : R, μ * c μ = 1 ∧
      ∃ g ∈ Formalism.UG.UJ c Jm, (g : Matrix (Fin M) (Fin M) R) = qr c Jm a₀ ((μ - 1) * n') ∧ l.prod = h * g := by
  have hu : IsUnit (Formalism.UG.hform c Jm a₀ a₀) := IsUnit.of_mul_eq_one n' (by rw [mul_comm]; exact hn')
  induction l using List.reverseRecOn with
  | nil =>
    refine ⟨1, H.one_mem, by simp, 1, by simp, 1, one_mem _, ?_, by simp⟩
    simp [qr_zero]
  | append_singleton l y ih =>
    obtain ⟨h, hhH, hdet, μ, hμ, g, hgU, hg, hprod⟩ := ih (fun z hz => hl z (List.mem_append_left _ hz))
    obtain ⟨hyU, a, lam, k, ha, hlam, hk, hy⟩ := hl y (by simp)
    obtain ⟨gl, hglU, hgl, hgli⟩ := tau_exists c hc Jm hJ a₀ n' hn' lam hlam
    have hBU : g * y * gl⁻¹ * g⁻¹ ∈ Formalism.UG.UJ c Jm :=
      mul_mem (mul_mem (mul_mem hgU hyU) (inv_mem hglU)) (inv_mem hgU)
    have hBmat : ((g * y * gl⁻¹ * g⁻¹ : GL (Fin M) R) : Matrix (Fin M) (Fin M) R) =
        qr c Jm ((g : Matrix (Fin M) (Fin M) R) *ᵥ a) k *
          qr c Jm ((g : Matrix (Fin M) (Fin M) R) *ᵥ a₀) ((c lam - 1) * n') := by
      rw [← conj_qr c Jm g hgU, ← conj_qr c Jm g hgU, ← hy, ← hgli]
      have : g * y * gl⁻¹ * g⁻¹ = (g * y * g⁻¹) * (g * gl⁻¹ * g⁻¹) := by group
      rw [this]
      simp only [Units.val_mul]
    have hk' : k * Formalism.UG.hform c Jm ((g : Matrix (Fin M) (Fin M) R) *ᵥ a) ((g : Matrix (Fin M) (Fin M) R) *ᵥ a) = lam - 1 := by
      rw [hform_mulVec c Jm g hgU]; exact hk
    have hkb : (c lam - 1) * n' * Formalism.UG.hform c Jm ((g : Matrix (Fin M) (Fin M) R) *ᵥ a₀) ((g : Matrix (Fin M) (Fin M) R) *ᵥ a₀) = c lam - 1 := by
      rw [hform_mulVec c Jm g hgU]
      linear_combination (c lam - 1) * hn'
    have hBH : g * y * gl⁻¹ * g⁻¹ ∈ H := by
      refine hH _ hBU ⟨_, _, lam, k, (c lam - 1) * n', ?_, ?_, hlam, hk', hkb, hBmat⟩
      · rw [hform_mulVec c Jm g hgU]; exact ha
      · rw [hform_mulVec c Jm g hgU]; exact hu
    have hBdet : ((g * y * gl⁻¹ * g⁻¹ : GL (Fin M) R) : Matrix (Fin M) (Fin M) R).det = 1 := by
      rw [hBmat, Matrix.det_mul, det_qr, det_qr, hk', hkb]
      linear_combination hlam
    refine ⟨h * (g * y * gl⁻¹ * g⁻¹), mul_mem hhH hBH, ?_, μ * lam, ?_, g * gl, mul_mem hgU hglU, ?_, ?_⟩
    · rw [Units.val_mul, Matrix.det_mul, hdet, hBdet, one_mul]
    · rw [map_mul]
      linear_combination (lam * c lam) * hμ + hlam
    · rw [Units.val_mul, hg, hgl, qr_mul]
      congr 1
      linear_combination n' * (μ - 1) * (lam - 1) * hn'
    · rw [List.prod_append, hprod, List.prod_singleton]
      group

/- English proof (translation)
Introduce `R _ c hc M Jm hJ a₀ ha₀ H hH l hl hdet`. Take `⟨n', hn'⟩` from `ha₀.exists_left_inv`. Take `⟨h, hhH, hdh, μ, hμ, g, hgU, hg, hprod⟩` from `prod_claim c hc Jm hJ a₀ n' hn' H hH l hl`. Establish `hμ1 : μ = 1`. Rewrite `hdet` using `[hprod, Units.val_mul, Matrix.det_mul, hdh, one_mul, hg, det_qr]`.

Take the linear combination `hdet - (μ - 1) * hn'`. Establish `hg1 : g = 1`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[hg, hμ1, sub_self, zero_mul, qr_zero, Units.val_one]`. Rewrite using `[hprod, hg1, mul_one]`.

Conclude with `hhH`.
-/
theorem pair_of_list : ∀ {R : Type} [CommRing R] (c : R →+* R), (∀ x, c (c x) = x) → ∀ {M : ℕ} (Jm : Matrix (Fin M) (Fin M) R), (∀ i j, c (Jm j i) = Jm i j) → ∀ a₀ : Fin M → R, IsUnit (Formalism.UG.hform c Jm a₀ a₀) → ∀ H : Subgroup (GL (Fin M) R), (∀ y ∈ Formalism.UG.UJ c Jm, IsQPair c Jm (y : Matrix (Fin M) (Fin M) R) → y ∈ H) → ∀ l : List (GL (Fin M) R), (∀ y ∈ l, y ∈ Formalism.UG.UJ c Jm ∧ IsQR c Jm (y : Matrix (Fin M) (Fin M) R)) → ((l.prod : GL (Fin M) R) : Matrix (Fin M) (Fin M) R).det = 1 → l.prod ∈ H := by
  intro R _ c hc M Jm hJ a₀ ha₀ H hH l hl hdet
  obtain ⟨n', hn'⟩ := ha₀.exists_left_inv
  obtain ⟨h, hhH, hdh, μ, hμ, g, hgU, hg, hprod⟩ := prod_claim c hc Jm hJ a₀ n' hn' H hH l hl
  have hμ1 : μ = 1 := by
    rw [hprod, Units.val_mul, Matrix.det_mul, hdh, one_mul, hg, det_qr] at hdet
    linear_combination hdet - (μ - 1) * hn'
  have hg1 : g = 1 := by
    apply Units.ext
    rw [hg, hμ1, sub_self, zero_mul, qr_zero, Units.val_one]
  rw [hprod, hg1, mul_one]
  exact hhH

end GlobalTheory.CompanionTheory.SaGen.PairList
