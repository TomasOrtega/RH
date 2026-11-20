import Mathlib

namespace GlobalTheory

open Module

section Defs

variable {R M : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]

def isoTransvection (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0) (b : R) : M ≃ₗ[R] M :=
  LinearEquiv.transvection (f := b • h.flip x) (v := x) (by simp [hx])

namespace isoTransvection

variable (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem apply (b : R) (v : M) : isoTransvection h x hx b v = v + (b * h v x) • x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_toLinearMap (b : R) :
    (isoTransvection h x hx b : M →ₗ[R] M) = LinearMap.transvection (b • h.flip x) x := rfl

/- English proof (translation)
Rewrite using `[apply, add_sub_cancel_left]`.
-/
theorem apply_sub (b : R) (v : M) : isoTransvection h x hx b v - v = (b * h v x) • x := by
  rw [apply, add_sub_cancel_left]

/- English proof (translation)
Use extensionality with `v`. Simplify using `[apply]`.
-/
@[simp] theorem zero : isoTransvection h x hx 0 = 1 := by
  ext v; simp [apply]

/- English proof (translation)
Simplify using `[apply, hx]`.
-/
@[simp] theorem apply_self (b : R) : isoTransvection h x hx b x = x := by
  simp [apply, hx]

/- English proof (translation)
Simplify using `[apply, hv]`.
-/
theorem apply_of_orth (b : R) {v : M} (hv : h v x = 0) : isoTransvection h x hx b v = v := by
  simp [apply, hv]

/- English proof (translation)
Simplify using `[apply, hx]`.
-/
@[simp] theorem form_apply_self (b : R) (v : M) :
    h (isoTransvection h x hx b v) x = h v x := by
  simp [apply, hx]

/- English proof (translation)
Simplify using `[apply, hx]`.
-/
@[simp] theorem form_self_apply (b : R) (v : M) :
    h x (isoTransvection h x hx b v) = h x v := by
  simp [apply, hx]

/- English proof (translation)
Rewrite using `[apply, form_apply_self, apply, apply, add_mul, add_smul, add_assoc, add_comm ((b' * _) • x)]`.
-/
theorem apply_apply (b b' : R) (v : M) :
    isoTransvection h x hx b (isoTransvection h x hx b' v) = isoTransvection h x hx (b + b') v := by
  rw [apply, form_apply_self, apply, apply, add_mul, add_smul, add_assoc, add_comm ((b' * _) • x)]

/- English proof (translation)
Use extensionality with `v`. Conclude with `apply_apply h x hx b b' v`.
-/
theorem mul (b b' : R) :
    isoTransvection h x hx b * isoTransvection h x hx b' = isoTransvection h x hx (b + b') := by
  ext v; exact apply_apply h x hx b b' v

/- English proof (translation)
Rewrite using `[Commute, SemiconjBy, mul, mul, add_comm]`.
-/
theorem commute (b b' : R) :
    Commute (isoTransvection h x hx b) (isoTransvection h x hx b') := by
  rw [Commute, SemiconjBy, mul, mul, add_comm]

/- English proof (translation)
The claim follows from `inv_eq_of_mul_eq_one_right (by rw [mul, add_neg_cancel, zero])`.
-/
theorem inv (b : R) : (isoTransvection h x hx b)⁻¹ = isoTransvection h x hx (-b) :=
  inv_eq_of_mul_eq_one_right (by rw [mul, add_neg_cancel, zero])

/- English proof (translation)
The claim follows from `inv h x hx b`.
-/
theorem symm (b : R) : (isoTransvection h x hx b).symm = isoTransvection h x hx (-b) :=
  inv h x hx b

end isoTransvection

def isoTransvectionHom (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0) :
    Multiplicative R →* (M ≃ₗ[R] M) where
  toFun b := isoTransvection h x hx b.toAdd
  map_one' := isoTransvection.zero h x hx
  map_mul' b b' := (isoTransvection.mul h x hx b.toAdd b'.toAdd).symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem isoTransvectionHom_apply (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0)
    (b : Multiplicative R) :
    isoTransvectionHom h x hx b = isoTransvection h x hx b.toAdd := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem isoTransvectionHom_ofAdd (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0) (b : R) :
    isoTransvectionHom h x hx (Multiplicative.ofAdd b) = isoTransvection h x hx b := rfl

namespace isoTransvection

variable (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0)

/- English proof (translation)
Rewrite using `[← isoTransvectionHom_ofAdd, ← map_pow, ← ofAdd_nsmul, isoTransvectionHom_ofAdd, nsmul_eq_mul]`.
-/
theorem pow (b : R) (n : ℕ) :
    isoTransvection h x hx b ^ n = isoTransvection h x hx (n * b) := by
  rw [← isoTransvectionHom_ofAdd, ← map_pow, ← ofAdd_nsmul, isoTransvectionHom_ofAdd,
    nsmul_eq_mul]

/- English proof (translation)
Rewrite using `[← isoTransvectionHom_ofAdd, ← map_zpow, ← ofAdd_zsmul, isoTransvectionHom_ofAdd, zsmul_eq_mul]`.
-/
theorem zpow (b : R) (n : ℤ) :
    isoTransvection h x hx b ^ n = isoTransvection h x hx (n * b) := by
  rw [← isoTransvectionHom_ofAdd, ← map_zpow, ← ofAdd_zsmul, isoTransvectionHom_ofAdd,
    zsmul_eq_mul]

/- English proof (translation)
Simplify using `[apply]`.
-/
theorem form_apply_left (b : R) (u v : M) :
    h (isoTransvection h x hx b u) v = h u v + b * h u x * h x v := by
  simp [apply]

variable {h}

/- English proof (translation)
Establish `: h x v = star (h v x)` using `hh v x`. Simplify using `only [apply, map_add, LinearMap.map_smulₛₗ, starRingEnd_apply, star_mul', smul_eq_mul, this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_apply_right (hh : ∀ u v, h v u = star (h u v)) (b : R) (u v : M) :
    h u (isoTransvection h x hx b v) = h u v + star b * h u x * h x v := by
  have : h x v = star (h v x) := hh v x
  simp only [apply, map_add, LinearMap.map_smulₛₗ, starRingEnd_apply, star_mul', smul_eq_mul, this]
  ring

/- English proof (translation)
Rewrite using `[form_apply_left, form_apply_right x hx hh, form_self_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_apply_apply (hh : ∀ u v, h v u = star (h u v)) (b : R) (u v : M) :
    h (isoTransvection h x hx b u) (isoTransvection h x hx b v)
      = h u v + (b + star b) * h u x * h x v := by
  rw [form_apply_left, form_apply_right x hx hh, form_self_apply]
  ring

/- English proof (translation)
Rewrite using `[form_apply_left, form_apply_right x hx hh, form_self_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_apply_apply' (hh : ∀ u v, h v u = star (h u v)) (b b' : R) (u v : M) :
    h (isoTransvection h x hx b u) (isoTransvection h x hx b' v)
      = h u v + (b + star b') * h u x * h x v := by
  rw [form_apply_left, form_apply_right x hx hh, form_self_apply]
  ring

/- English proof (translation)
Rewrite using `[form_apply_apply x hx hh, hh v x, mul_assoc]`.
-/
theorem form_apply_diag (hh : ∀ u v, h v u = star (h u v)) (b : R) (v : M) :
    h (isoTransvection h x hx b v) (isoTransvection h x hx b v)
      = h v v + (b + star b) * (h v x * star (h v x)) := by
  rw [form_apply_apply x hx hh, hh v x, mul_assoc]

/- English proof (translation)
Rewrite using `[form_apply_left, form_apply_right x hx hh, star_star]`.
-/
theorem adjoint (hh : ∀ u v, h v u = star (h u v)) (b : R) (u v : M) :
    h (isoTransvection h x hx b u) v = h u (isoTransvection h x hx (star b) v) := by
  rw [form_apply_left, form_apply_right x hx hh, star_star]

/- English proof (translation)
Introduce `u v` and use `adjoint x hx hh b u v`.
-/
theorem isAdjointPair (hh : ∀ u v, h v u = star (h u v)) (b : R) :
    LinearMap.IsAdjointPair h h (isoTransvection h x hx b) (isoTransvection h x hx (star b)) :=
  fun u v => adjoint x hx hh b u v

/- English proof (translation)
Rewrite using `[form_apply_apply' x hx hh]`. Simplify using the standard rewrite rules.
-/
theorem form_apply_neg_star (hh : ∀ u v, h v u = star (h u v)) (b : R) (u v : M) :
    h (isoTransvection h x hx b u) (isoTransvection h x hx (-star b) v) = h u v := by
  rw [form_apply_apply' x hx hh]; simp

/- English proof (translation)
Rewrite using `[form_apply_apply x hx hh, hb]`. Simplify using the standard rewrite rules.
-/
theorem isometry (hh : ∀ u v, h v u = star (h u v)) {b : R} (hb : b + star b = 0) (u v : M) :
    h (isoTransvection h x hx b u) (isoTransvection h x hx b v) = h u v := by
  rw [form_apply_apply x hx hh, hb]; simp

/- English proof (translation)
Apply the tactic sequence `refine ⟨fun H => ?_, fun hb => isometry x hx hh hb⟩`. Take `⟨v, hv⟩` from `hx0`. Use `H v v` as an intermediate fact. Rewrite `this` using `[form_apply_diag x hx hh, add_eq_left]`. Simplify `this` using `[hv]`.
-/
theorem isometry_iff [NoZeroDivisors R] (hh : ∀ u v, h v u = star (h u v))
    (hx0 : ∃ v, h v x ≠ 0) (b : R) :
    (∀ u v, h (isoTransvection h x hx b u) (isoTransvection h x hx b v) = h u v)
      ↔ b + star b = 0 := by
  refine ⟨fun H => ?_, fun hb => isometry x hx hh hb⟩
  obtain ⟨v, hv⟩ := hx0
  have := H v v
  rw [form_apply_diag x hx hh, add_eq_left] at this
  simpa [hv] using this

variable (h)

/- English proof (translation)
Take `⟨v, hv⟩` from `hx0`. Establish `hx1 : x ≠ 0` using `by rintro rfl; simp at hv`. Introduce `b b' H`. Establish `: isoTransvection h x hx b v = isoTransvection h x hx b' v` using `by rw [H]`. Rewrite `this` using `[apply, apply, add_right_inj]`.

Conclude with `mul_right_cancel₀ hv (smul_left_injective R hx1 this)`.
-/
theorem injective [IsDomain R] [IsTorsionFree R M] (hx0 : ∃ v, h v x ≠ 0) :
    Function.Injective (isoTransvection h x hx) := by
  obtain ⟨v, hv⟩ := hx0
  have hx1 : x ≠ 0 := by rintro rfl; simp at hv
  intro b b' H
  have : isoTransvection h x hx b v = isoTransvection h x hx b' v := by rw [H]
  rw [apply, apply, add_right_inj] at this
  exact mul_right_cancel₀ hv (smul_left_injective R hx1 this)

/- English proof (translation)
Rewrite using `[coe_toLinearMap, LinearMap.transvection.det]`. Simplify using `[hx]`.
-/
theorem det_toLinearMap [Module.Free R M] [Module.Finite R M] (b : R) :
    LinearMap.det (isoTransvection h x hx b : M →ₗ[R] M) = 1 := by
  rw [coe_toLinearMap, LinearMap.transvection.det]
  simp [hx]

/- English proof (translation)
Rewrite using `[← Units.val_inj, LinearEquiv.coe_det, det_toLinearMap, Units.val_one]`.
-/
theorem det [Module.Free R M] [Module.Finite R M] (b : R) :
    LinearEquiv.det (isoTransvection h x hx b) = 1 := by
  rw [← Units.val_inj, LinearEquiv.coe_det, det_toLinearMap, Units.val_one]

/- English proof (translation)
Use extensionality with `v`. Simplify using `only [apply, LinearMap.map_smulₛₗ, starRingEnd_apply, smul_eq_mul, smul_smul]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem smul_vec (a b : R) (hax : h (a • x) (a • x) = 0 := by simp [*]) :
    isoTransvection h (a • x) hax b = isoTransvection h x hx (b * (a * star a)) := by
  ext v
  simp only [apply, LinearMap.map_smulₛₗ, starRingEnd_apply, smul_eq_mul, smul_smul]
  congr 2; ring

/- English proof (translation)
Simplify using `[apply, hj]`.
-/
theorem map_apply {R' M' : Type*} [CommRing R'] [StarRing R'] [AddCommGroup M'] [Module R' M']
    {φ : R →+* R'} (j : M →ₛₗ[φ] M') (h' : M' →ₗ[R'] M' →ₗ⋆[R'] R')
    (hx' : h' (j x) (j x) = 0) (b : R) (v : M) (hj : h' (j v) (j x) = φ (h v x)) :
    j (isoTransvection h x hx b v) = isoTransvection h' (j x) hx' (φ b) (j v) := by
  simp [apply, hj]

/- English proof (translation)
Rewrite using `[mul_inv_eq_iff_eq_mul]`. Use extensionality with `v`. Simplify using `[LinearEquiv.mul_apply, apply, hg]`.
-/
theorem conj (g : M ≃ₗ[R] M) (hg : ∀ u v, h (g u) (g v) = h u v) (b : R)
    (hgx : h (g x) (g x) = 0) :
    g * isoTransvection h x hx b * g⁻¹ = isoTransvection h (g x) hgx b := by
  rw [mul_inv_eq_iff_eq_mul]
  ext v
  simp [LinearEquiv.mul_apply, apply, hg]

/- English proof (translation)
Use extensionality with `v`. Simplify using `[LinearEquiv.mul_apply, apply, hg, hgx]`.
-/
theorem commute_of_fix (g : M ≃ₗ[R] M) (hgx : g x = x) (hg : ∀ u, h (g u) x = h u x) (b : R) :
    Commute g (isoTransvection h x hx b) := by
  ext v
  simp [LinearEquiv.mul_apply, apply, hg, hgx]

section Lattice

variable {R₀ : Type*} [CommRing R₀] [Algebra R₀ R] [Module R₀ M] [IsScalarTower R₀ R M]

/- English proof (translation)
Take `⟨c, hc, hcb⟩` from `hb`. Rewrite using `[apply_sub, ← hcb, algebraMap_smul]`. Conclude with `Submodule.smul_mem_smul hc hxL`.
-/
theorem sub_mem_smul_of_mul {L : Submodule R₀ M} (hxL : x ∈ L) {I : Ideal R₀} {b : R} {v : M}
    (hb : ∃ c ∈ I, algebraMap R₀ R c = b * h v x) :
    isoTransvection h x hx b v - v ∈ I • L := by
  obtain ⟨c, hc, hcb⟩ := hb
  rw [apply_sub, ← hcb, algebraMap_smul]
  exact Submodule.smul_mem_smul hc hxL

/- English proof (translation)
Take `⟨c, hc⟩` from `hL v hv`. Conclude with `sub_mem_smul_of_mul h x hx hxL ⟨b * c, I.mul_mem_right c hb, by rw [map_mul, hc]⟩`.
-/
theorem sub_mem_smul {L : Submodule R₀ M} (hxL : x ∈ L)
    (hL : ∀ v ∈ L, h v x ∈ (algebraMap R₀ R).range) {I : Ideal R₀} {b : R₀} (hb : b ∈ I)
    {v : M} (hv : v ∈ L) :
    isoTransvection h x hx (algebraMap R₀ R b) v - v ∈ I • L := by
  obtain ⟨c, hc⟩ := hL v hv
  exact sub_mem_smul_of_mul h x hx hxL ⟨b * c, I.mul_mem_right c hb, by rw [map_mul, hc]⟩

/- English proof (translation)
Take `⟨c, hc⟩` from `hL v hv`. Use `⟨(b * c) • x, L.smul_mem _ hxL, ?_⟩` and prove the remaining obligations. Rewrite using `[apply_sub, ← hc, ← map_mul, algebraMap_smul, smul_smul, mul_assoc]`.
-/
theorem exists_sub_eq_smul {L : Submodule R₀ M} (hxL : x ∈ L)
    (hL : ∀ v ∈ L, h v x ∈ (algebraMap R₀ R).range) (q b : R₀) {v : M} (hv : v ∈ L) :
    ∃ w ∈ L, isoTransvection h x hx (algebraMap R₀ R (q * b)) v - v = q • w := by
  obtain ⟨c, hc⟩ := hL v hv
  refine ⟨(b * c) • x, L.smul_mem _ hxL, ?_⟩
  rw [apply_sub, ← hc, ← map_mul, algebraMap_smul, smul_smul, mul_assoc]

/- English proof (translation)
Take `⟨c, hc⟩` from `hL v hv`. Rewrite using `[apply, ← hc, ← map_mul, algebraMap_smul]`. Conclude with `L.add_mem hv (L.smul_mem _ hxL)`.
-/
theorem apply_mem {L : Submodule R₀ M} (hxL : x ∈ L)
    (hL : ∀ v ∈ L, h v x ∈ (algebraMap R₀ R).range) (b : R₀) {v : M} (hv : v ∈ L) :
    isoTransvection h x hx (algebraMap R₀ R b) v ∈ L := by
  obtain ⟨c, hc⟩ := hL v hv
  rw [apply, ← hc, ← map_mul, algebraMap_smul]
  exact L.add_mem hv (L.smul_mem _ hxL)

/- English proof (translation)
Use `⟨fun H => ?_, apply_mem h x hx hxL hL b⟩` and prove the remaining obligations. Use `apply_mem h x hx hxL hL (-b) H` as an intermediate fact. Rewrite `this` using `[apply_apply, map_neg, neg_add_cancel, zero]`. Then use the resulting hypothesis.
-/
theorem apply_mem_iff {L : Submodule R₀ M} (hxL : x ∈ L)
    (hL : ∀ v ∈ L, h v x ∈ (algebraMap R₀ R).range) (b : R₀) (v : M) :
    isoTransvection h x hx (algebraMap R₀ R b) v ∈ L ↔ v ∈ L := by
  refine ⟨fun H => ?_, apply_mem h x hx hxL hL b⟩
  have := apply_mem h x hx hxL hL (-b) H
  rwa [apply_apply, map_neg, neg_add_cancel, zero] at this

/- English proof (translation)
Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, rfl⟩`. Conclude with `apply_mem h x hx hxL hL b hv`. Introduce `hw`.

Use `⟨isoTransvection h x hx (algebraMap R₀ R (-b)) w, apply_mem h x hx hxL hL _ hw, ?_⟩` and prove the remaining obligations. Rewrite using `[apply_apply, map_neg, add_neg_cancel, zero]`. Both sides reduce to the same expression.
-/
theorem image_eq {L : Submodule R₀ M} (hxL : x ∈ L)
    (hL : ∀ v ∈ L, h v x ∈ (algebraMap R₀ R).range) (b : R₀) :
    isoTransvection h x hx (algebraMap R₀ R b) '' (L : Set M) = L := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact apply_mem h x hx hxL hL b hv
  · intro hw
    refine ⟨isoTransvection h x hx (algebraMap R₀ R (-b)) w, apply_mem h x hx hxL hL _ hw, ?_⟩
    rw [apply_apply, map_neg, add_neg_cancel, zero]; rfl

/- English proof (translation)
The claim follows from `SetLike.coe_injective (image_eq h x hx hxL hL b)`.
-/
theorem map_eq {L : Submodule R₀ M} (hxL : x ∈ L)
    (hL : ∀ v ∈ L, h v x ∈ (algebraMap R₀ R).range) (b : R₀) :
    L.map ((isoTransvection h x hx (algebraMap R₀ R b) : M →ₗ[R] M).restrictScalars R₀) = L :=
  SetLike.coe_injective (image_eq h x hx hxL hL b)

end Lattice

end isoTransvection

end Defs

section Complex

namespace isoTransvection

variable {W : Type*} [AddCommGroup W] [Module ℂ W] {h : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ} (x : W)
  (hx : h x x = 0)

/- English proof (translation)
Rewrite using `[form_apply_apply x hx hh, Complex.star_def, Complex.add_conj]`.
-/
theorem form_apply_apply_complex (hh : ∀ u v, h v u = star (h u v)) (b : ℂ) (u v : W) :
    h (isoTransvection h x hx b u) (isoTransvection h x hx b v)
      = h u v + (2 * b.re : ℝ) * h u x * h x v := by
  rw [form_apply_apply x hx hh, Complex.star_def, Complex.add_conj]

/- English proof (translation)
Rewrite using `[form_apply_diag x hx hh, Complex.star_def, Complex.add_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_apply_diag_complex (hh : ∀ u v, h v u = star (h u v)) (b : ℂ) (v : W) :
    h (isoTransvection h x hx b v) (isoTransvection h x hx b v)
      = h v v + ((2 * b.re * ‖h v x‖ ^ 2 : ℝ) : ℂ) := by
  rw [form_apply_diag x hx hh, Complex.star_def, Complex.add_conj, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  push_cast; ring

/- English proof (translation)
Rewrite using `[form_apply_diag_complex x hx hh, Complex.add_re, Complex.ofReal_re]`.
-/
theorem re_form_apply_diag_complex (hh : ∀ u v, h v u = star (h u v)) (b : ℂ) (v : W) :
    (h (isoTransvection h x hx b v) (isoTransvection h x hx b v)).re
      = (h v v).re + 2 * b.re * ‖h v x‖ ^ 2 := by
  rw [form_apply_diag_complex x hx hh, Complex.add_re, Complex.ofReal_re]

/- English proof (translation)
Rewrite using `[isometry_iff x hx hh hx0, Complex.star_def, Complex.add_conj]`. Simplify using the standard rewrite rules.
-/
theorem isometry_iff_re (hh : ∀ u v, h v u = star (h u v)) (hx0 : ∃ v, h v x ≠ 0) (b : ℂ) :
    (∀ u v, h (isoTransvection h x hx b u) (isoTransvection h x hx b v) = h u v)
      ↔ b.re = 0 := by
  rw [isometry_iff x hx hh hx0, Complex.star_def, Complex.add_conj]
  simp

/- English proof (translation)
Rewrite using `[form_apply_apply_complex x hx hh, hb]`. Simplify using the standard rewrite rules.
-/
theorem isometry_of_re (hh : ∀ u v, h v u = star (h u v)) {b : ℂ} (hb : b.re = 0) (u v : W) :
    h (isoTransvection h x hx b u) (isoTransvection h x hx b v) = h u v := by
  rw [form_apply_apply_complex x hx hh, hb]; simp

/- English proof (translation)
Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem re_mul_I_mul (b : ℂ) (s : ℝ) : (b * (Complex.I * s)).re = -s * b.im := by
  simp; ring

/- English proof (translation)
The claim follows from `isometry_of_re x hx hh (by rw [re_mul_I_mul]; simp) u v`.
-/
theorem isometry_ofReal_mul_I_mul (hh : ∀ u v, h v u = star (h u v)) (b s : ℝ) (u v : W) :
    h (isoTransvection h x hx (b * (Complex.I * s)) u)
      (isoTransvection h x hx (b * (Complex.I * s)) v) = h u v :=
  isometry_of_re x hx hh (by rw [re_mul_I_mul]; simp) u v

end isoTransvection

namespace isoTransvection

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] (h : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (x : W)
  (hx : h x x = 0)

/- English proof (translation)
Simplify using `only [apply]`. Use `fun_prop`.
-/
theorem differentiable_param (v : W) :
    Differentiable ℂ fun b : ℂ => isoTransvection h x hx b v := by
  simp only [apply]; fun_prop

/- English proof (translation)
Establish `: CompleteSpace W` using `FiniteDimensional.complete ℂ W`. Set `f : W →L[ℂ] ℂ` to `LinearMap.toContinuousLinearMap (h.flip x)`. Establish `: (fun p : ℂ × W => isoTransvection h x hx p.1 p.2) = fun p : ℂ × W => p.2 + (p.1 * f p.2) • x` using `rfl`. Rewrite using `[this]`. Introduce `p _`.

Conclude with `analyticAt_snd.add ((analyticAt_fst.mul ((f.analyticAt _).comp analyticAt_snd)).smul analyticAt_const)`.
-/
theorem analyticOnNhd_uncurry [FiniteDimensional ℂ W] :
    AnalyticOnNhd ℂ (fun p : ℂ × W => isoTransvection h x hx p.1 p.2) Set.univ := by
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  let f : W →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (h.flip x)
  have : (fun p : ℂ × W => isoTransvection h x hx p.1 p.2)
      = fun p : ℂ × W => p.2 + (p.1 * f p.2) • x := rfl
  rw [this]
  intro p _
  exact analyticAt_snd.add
    ((analyticAt_fst.mul ((f.analyticAt _).comp analyticAt_snd)).smul analyticAt_const)

/- English proof (translation)
Introduce `p` and use `(analyticOnNhd_uncurry h x hx p (Set.mem_univ p)).differentiableAt`.
-/
theorem differentiable_uncurry [FiniteDimensional ℂ W] :
    Differentiable ℂ fun p : ℂ × W => isoTransvection h x hx p.1 p.2 :=
  fun p => (analyticOnNhd_uncurry h x hx p (Set.mem_univ p)).differentiableAt

/- English proof (translation)
Set `f : W →L[ℂ] ℂ` to `LinearMap.toContinuousLinearMap (h.flip x)`. Establish `: (fun b : ℂ => LinearMap.toContinuousLinearMap (isoTransvection h x hx b : W →ₗ[ℂ] W)) = fun b : ℂ => ContinuousLinearMap.id ℂ W + b • f.smulRight x`. Use extensionality with `b v`. Simplify using `[apply, f, smul_smul]`. Rewrite using `[this]`.

Use `fun_prop`.
-/
theorem differentiable_toContinuousLinearMap [FiniteDimensional ℂ W] :
    Differentiable ℂ fun b : ℂ =>
      LinearMap.toContinuousLinearMap (isoTransvection h x hx b : W →ₗ[ℂ] W) := by
  let f : W →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (h.flip x)
  have : (fun b : ℂ => LinearMap.toContinuousLinearMap (isoTransvection h x hx b : W →ₗ[ℂ] W))
      = fun b : ℂ => ContinuousLinearMap.id ℂ W + b • f.smulRight x := by
    ext b v
    simp [apply, f, smul_smul]
  rw [this]
  fun_prop

end isoTransvection

end Complex

/- English proof (translation)
Apply the tactic sequence `refine ⟨fun _ _ => rfl, fun _ => rfl, isoTransvection.mul h x hx, isoTransvection.apply_self h x hx, isoTransvection.form_apply_self h x hx, isoTransvection.form_apply_apply x hx hh, isoTransvection.adjoint x hx hh, fun _ _ => isoTransvection.det_toLinearMap h x hx, fun b hb => i …`. Establish `hL' : ∀ v ∈ L, h v x ∈ (algebraMap R₀ R).range` using `fun v hv => ⟨⟨_, hL v hv⟩, rfl⟩`. Conclude with `⟨fun v hv => isoTransvection.sub_mem_smul h x hx hxL hL' hb hv, isoTransvection.image_eq h x hx hxL hL' b⟩`.
-/
theorem isoTransvection_spec {R M : Type*} [CommRing R] [StarRing R] [AddCommGroup M]
    [Module R M] (h : M →ₗ[R] M →ₗ⋆[R] R) (hh : ∀ u v, h v u = star (h u v))
    (x : M) (hx : h x x = 0) :
    (∀ b v, isoTransvectionHom h x hx (Multiplicative.ofAdd b) v = v + (b * h v x) • x) ∧
    (∀ b, isoTransvectionHom h x hx (Multiplicative.ofAdd b) = isoTransvection h x hx b) ∧
    (∀ b b', isoTransvection h x hx b * isoTransvection h x hx b'
      = isoTransvection h x hx (b + b')) ∧
    (∀ b, isoTransvection h x hx b x = x) ∧
    (∀ b v, h (isoTransvection h x hx b v) x = h v x) ∧
    (∀ b u v, h (isoTransvection h x hx b u) (isoTransvection h x hx b v)
      = h u v + (b + star b) * h u x * h x v) ∧
    (∀ b u v, h (isoTransvection h x hx b u) v = h u (isoTransvection h x hx (star b) v)) ∧
    (Module.Free R M → Module.Finite R M →
      ∀ b, LinearMap.det (isoTransvection h x hx b : M →ₗ[R] M) = 1) ∧
    (∀ b, b + star b = 0 →
      ∀ u v, h (isoTransvection h x hx b u) (isoTransvection h x hx b v) = h u v) ∧
    (∀ (R₀ : Subring R) (L : Submodule R₀ M) (I : Ideal R₀) (b : R₀), x ∈ L →
      (∀ v ∈ L, h v x ∈ R₀) → b ∈ I →
        (∀ v ∈ L, isoTransvection h x hx b v - v ∈ I • L) ∧
          isoTransvection h x hx b '' (L : Set M) = L) := by
  refine ⟨fun _ _ => rfl, fun _ => rfl, isoTransvection.mul h x hx,
    isoTransvection.apply_self h x hx, isoTransvection.form_apply_self h x hx,
    isoTransvection.form_apply_apply x hx hh, isoTransvection.adjoint x hx hh,
    fun _ _ => isoTransvection.det_toLinearMap h x hx,
    fun b hb => isoTransvection.isometry x hx hh hb, fun R₀ L I b hxL hL hb => ?_⟩
  have hL' : ∀ v ∈ L, h v x ∈ (algebraMap R₀ R).range := fun v hv => ⟨⟨_, hL v hv⟩, rfl⟩
  exact ⟨fun v hv => isoTransvection.sub_mem_smul h x hx hxL hL' hb hv,
    isoTransvection.image_eq h x hx hxL hL' b⟩

section Example

private noncomputable def hyp : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun u v => u.1 * star v.2 + u.2 * star v.1)
    (by intros; simp; ring) (by intros; simp; ring) (by intros; simp; ring)
    (by intros; simp; ring)

/- English proof (translation)
Use `⟨fun u v => ?_, ?_⟩` and prove the remaining obligations. Simplify using `[hyp]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[isoTransvection.apply, hyp]`.
-/
example (b : ℂ) : (∀ u v, hyp v u = star (hyp u v)) ∧
    isoTransvection hyp (1, 0) (by simp [hyp]) b (0, 1) = (b, 1) := by
  refine ⟨fun u v => ?_, ?_⟩
  · simp [hyp]; ring
  · simp [isoTransvection.apply, hyp]

end Example

end GlobalTheory
