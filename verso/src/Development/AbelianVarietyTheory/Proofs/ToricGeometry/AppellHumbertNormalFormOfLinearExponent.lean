import Mathlib

open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory
namespace AppellHumbert

open Complex Matrix Filter Topology in
open scoped BigOperators Real in

/- English proof (translation)
Use `haveI : IsZLattice ℝ Λ := ⟨hΛ⟩`. Set `b` to `Module.Free.chooseBasis ℤ Λ`. Set `bR` to `Module.Basis.ofZLatticeBasis ℝ Λ b`. Use `⟨bR.constr ℝ (fun i => f (b i)), fun l => ?_⟩` and prove the remaining obligations. Establish `key : ((bR.constr ℝ (fun i => f (b i))).restrictScalars ℤ ∘ₗ Λ.subtype) = f.toIntLinearMap`.

Use `b.ext fun i => ?_` and prove the remaining obligations. Use `show bR.constr ℝ (fun i => f (b i)) (b i : Fin g → ℂ) = f (b i)`. Rewrite using `[← Module.Basis.ofZLatticeBasis_apply ℝ Λ b i, Module.Basis.constr_basis]`. Conclude with `LinearMap.congr_fun key l`.
-/
theorem _root_.GlobalTheory.AppellHumbert.exists_real_extension {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    [DiscreteTopology Λ]
    (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) {W : Type*} [AddCommGroup W] [Module ℝ W]
    (f : Λ →+ W) : ∃ F : (Fin g → ℂ) →ₗ[ℝ] W, ∀ l : Λ, F l = f l := by
  haveI : IsZLattice ℝ Λ := ⟨hΛ⟩
  let b := Module.Free.chooseBasis ℤ Λ
  let bR := Module.Basis.ofZLatticeBasis ℝ Λ b
  refine ⟨bR.constr ℝ (fun i => f (b i)), fun l => ?_⟩
  have key : ((bR.constr ℝ (fun i => f (b i))).restrictScalars ℤ ∘ₗ Λ.subtype) =
      f.toIntLinearMap := by
    refine b.ext fun i => ?_
    show bR.constr ℝ (fun i => f (b i)) (b i : Fin g → ℂ) = f (b i)
    rw [← Module.Basis.ofZLatticeBasis_apply ℝ Λ b i, Module.Basis.constr_basis]
  exact LinearMap.congr_fun key l

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
/- English proof (translation)
Use extensionality with `i`. Simplify using `[Finset.sum_apply, Finset.sum_add_distrib, Pi.single_apply, Complex.re_add_im]`.
-/
theorem _root_.GlobalTheory.AppellHumbert.eq_sum_re_im {g : ℕ} (u : Fin g → ℂ) :
    u = ∑ j, ((u j).re • (Pi.single j (1 : ℂ) : Fin g → ℂ)
      + (u j).im • (Pi.single j I : Fin g → ℂ)) := by
  ext i
  simp [Finset.sum_apply, Finset.sum_add_distrib, Pi.single_apply, Complex.re_add_im]

/- English proof (translation)
Use `conv_lhs => rw [pi_eq_sum_univ' z]`. Simplify using `[map_sum]`.
-/
theorem apply_eq_sum {g : ℕ} (φ : (Fin g → ℂ) →ₗ[ℂ] ℂ) (z : Fin g → ℂ) :
    φ z = ∑ i, z i * φ (Pi.single i 1) := by
  conv_lhs => rw [pi_eq_sum_univ' z]
  simp [map_sum]

/- English proof (translation)
Use `⟨Matrix.of fun a b => (F (Pi.single b 1) (Pi.single a 1) - I * F (Pi.single b I) (Pi.single a 1)) / 2, Matrix.of fun a b => (F (Pi.single b 1) (Pi.single a 1) + I * F (Pi.single b I) (Pi.single a 1)) / 2, fun u z => ?_⟩` and prove the remaining obligations. Rewrite using `[apply_eq_sum, ← dotProduct_add, dotProduct]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `congr 1`. Use `conv_lhs => rw [eq_sum_re_im u]`.

Simplify using `only [map_sum, map_add, map_smul, LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply, mulVec, dotProduct, of_apply, ← Finset.sum_add_distrib, Pi.star_apply, real_smul]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Establish `h1 : u b = (u b).re + (u b).im * I` using `(re_add_im _).symm`. Establish `h2 : star (u b) = (u b).re - (u b).im * I`. Apply the tactic sequence `apply Complex.ext <;> simp`.

Rewrite using `[h2]`. Generalize the expression as in `(u b).re = x at *`. Generalize the expression as in `(u b).im = y at *`. Rewrite using `[h1]`. Take the linear combination `(y * F (Pi.single b I) (Pi.single a 1)) * I_mul_I`.
-/
theorem exists_split {g : ℕ} (F : (Fin g → ℂ) →ₗ[ℝ] ((Fin g → ℂ) →ₗ[ℂ] ℂ)) :
    ∃ S H : Matrix (Fin g) (Fin g) ℂ, ∀ u z,
      F u z = z ⬝ᵥ S.mulVec u + z ⬝ᵥ H.mulVec (star u) := by
  refine ⟨Matrix.of fun a b => (F (Pi.single b 1) (Pi.single a 1)
      - I * F (Pi.single b I) (Pi.single a 1)) / 2,
    Matrix.of fun a b => (F (Pi.single b 1) (Pi.single a 1)
      + I * F (Pi.single b I) (Pi.single a 1)) / 2, fun u z => ?_⟩
  rw [apply_eq_sum, ← dotProduct_add, dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  conv_lhs => rw [eq_sum_re_im u]
  simp only [map_sum, map_add, map_smul, LinearMap.sum_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Pi.add_apply, mulVec, dotProduct, of_apply, ← Finset.sum_add_distrib,
    Pi.star_apply, real_smul]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h1 : u b = (u b).re + (u b).im * I := (re_add_im _).symm
  have h2 : star (u b) = (u b).re - (u b).im * I := by
    apply Complex.ext <;> simp
  rw [h2]
  generalize (u b).re = x at *
  generalize (u b).im = y at *
  rw [h1]
  linear_combination (y * F (Pi.single b I) (Pi.single a 1)) * I_mul_I

end AppellHumbert

open Complex Matrix Filter Topology in
open scoped BigOperators Real in

/- English proof (translation)
Introduce `g Λ hdisc hΛ a B ha hcoc`. Use `haveI := hdisc`. Set `b : Λ →+ (Fin g → ℂ)` to `{ toFun := fun l j => B l (Pi.single j 1) map_zero' := by ext j; simp map_add' := fun l m => by ext j; simp }`. Take `⟨F, hF0⟩` from `_root_.GlobalTheory.AppellHumbert.exists_real_extension Λ hΛ b`. Establish `hF : ∀ (l : Λ) z, B l z = F l ⬝ᵥ z`.

Introduce `l z`. Rewrite using `[hF0]`. Use `conv_lhs => rw [show z = ∑ j, z j • (Pi.single j (1 : ℂ) : Fin g → ℂ) by ext i; simp [Pi.single_apply]]`. Simplify using `[map_sum, dotProduct, b, mul_comm]`. Establish `hskew : ∀ l m : Λ, ∃ n : ℤ, B l m = B m l + n * (2 * π * I)`.

Introduce `l m`. Establish `h` using `hcoc l m`. Rewrite `h` using `[add_comm, hcoc m l, mul_comm (a m) (a l)]`. Conclude with `Complex.exp_eq_exp_iff_exists_int.mp (mul_left_cancel₀ (mul_ne_zero (ha l) (ha m)) h).symm`. Establish `hlin : ∀ (P : (Fin g → ℂ) → Prop), P 0 → (∀ x y, P x → P y → P (x + y)) → (∀ (c : ℝ) x, P x → P (c • x)) → (∀ l : Λ, P l) → ∀ x, P x`.

Introduce `P h0 hadd hsmul hl x`. Establish `hx : x ∈ Submodule.span ℝ (Λ : Set (Fin g → ℂ))` using `by rw [hΛ]; trivial`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact hl ⟨y, hy⟩`. Consider the case `zero => exact h0`.

Consider the case `add y z _ _ hy hz => exact hadd y z hy hz`. Consider the case `smul c y _ hy => exact hsmul c y hy`. Establish `hD1 : ∀ u (m : Λ), (F u ⬝ᵥ m - F m ⬝ᵥ u).re = 0`. Introduce `u m`. Use `hlin (fun u => (F u ⬝ᵥ m - F m ⬝ᵥ u).re = 0) (by simp) (fun x y hx hy => ?_) (fun c x hx => ?_) (fun l => ?_) u` and prove the remaining obligations.

Simplify using `only [map_add, add_dotProduct, dotProduct_add, Complex.sub_re, Complex.add_re] at hx hy ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [map_smul, smul_dotProduct, dotProduct_smul, Complex.sub_re, Complex.smul_re, smul_eq_mul] at hx ⊢`. Rewrite using `[← mul_sub, hx, mul_zero]`. Take `⟨n, hn⟩` from `hskew l m`.

Rewrite using `[← hF, ← hF, hn]`. Simplify using the standard rewrite rules. Establish `hD : ∀ u v, (F u ⬝ᵥ v - F v ⬝ᵥ u).re = 0`. Introduce `u v`. Use `hlin (fun v => (F u ⬝ᵥ v - F v ⬝ᵥ u).re = 0) (by simp) (fun x y hx hy => ?_) (fun c x hx => ?_) (fun m => hD1 u m) v` and prove the remaining obligations.

Simplify using `only [map_add, add_dotProduct, dotProduct_add, Complex.sub_re, Complex.add_re] at hx hy ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [map_smul, smul_dotProduct, dotProduct_smul, Complex.sub_re, Complex.smul_re, smul_eq_mul] at hx ⊢`. Rewrite using `[← mul_sub, hx, mul_zero]`. Set `M : Matrix (Fin g) (Fin g) ℂ` to `fun k j => (1/2 : ℝ) • (F (Pi.single k 1) j - I * F (Pi.single k I) j)`.

Set `N : Matrix (Fin g) (Fin g) ℂ` to `fun k j => (1/2 : ℝ) • (F (Pi.single k 1) j + I * F (Pi.single k I) j)`. Establish `hFMN : ∀ u, F u = u ᵥ* M + star u ᵥ* N`. Introduce `u`. Use extensionality with `j`. Use `conv_lhs => rw [_root_.GlobalTheory.AppellHumbert.eq_sum_re_im u]`.

Simplify using `only [map_sum, map_add, map_smul, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, vecMul, dotProduct, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Apply the tactic sequence `apply Complex.ext <;> simp [M, N, Complex.mul_re, Complex.mul_im] <;> ring`. Establish `hsym : ∀ k j, (F (Pi.single k 1) j).re = (F (Pi.single j 1) k).re ∧ (F (Pi.single k I) j).im = (F (Pi.single j I) k).im ∧ (F (Pi.single k I) j).re = -(F (Pi.single j 1) k).im`. Introduce `k j`.

Establish `h1` using `hD (Pi.single k 1) (Pi.single j 1)`. Establish `h2` using `hD (Pi.single k I) (Pi.single j I)`. Establish `h3` using `hD (Pi.single k I) (Pi.single j 1)`. Simplify using `only [dotProduct_single, mul_one, Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, zero_sub, sub_zero] at h1 h2 h3`. Use `⟨by linarith, by linarith, by linarith⟩` and prove the remaining obligations.

Establish `hMsym : Mᵀ = M`. Use extensionality with `k j`. Rewrite using `[transpose_apply]`. Take `⟨a1, a2, a3⟩` from `hsym k j`. Take `⟨b1, b2, b3⟩` from `hsym j k`.

Apply the tactic sequence `apply Complex.ext <;> simp [M, Complex.mul_re, Complex.mul_im] <;> linarith`. Establish `hNherm : ∀ i j, (starRingEnd ℂ) (N i j) = N j i`. Introduce `k j`. Take `⟨a1, a2, a3⟩` from `hsym k j`. Take `⟨b1, b2, b3⟩` from `hsym j k`.

Apply the tactic sequence `apply Complex.ext <;> simp [N, Complex.mul_re, Complex.mul_im] <;> linarith`. Set `A : (Fin g → ℂ) → (Fin g → ℂ) → ℂ` to `fun u v => u ⬝ᵥ M *ᵥ v`. Set `K : (Fin g → ℂ) → (Fin g → ℂ) → ℂ` to `fun z u => z ⬝ᵥ Nᵀ *ᵥ star u`. Establish `hAsym : ∀ u v, A u v = A v u`. Introduce `u v`.

Simplify using `only [A]`. Use `conv_rhs => rw [← hMsym]`. Rewrite using `[mulVec_transpose, dotProduct_comm v, ← dotProduct_mulVec]`. Establish `hBF : ∀ (l : Λ) z, B l z = A l z + K z l`. Introduce `l z`.

Simplify using `only [A, K]`. Rewrite using `[hF, hFMN, add_dotProduct, dotProduct_mulVec, mulVec_transpose, dotProduct_comm z]`. Establish `hKherm : ∀ u v, K v u = (starRingEnd ℂ) (K u v)`. Introduce `u v`. Simplify using `only [K, dotProduct, mulVec, transpose_apply, map_sum, map_mul, Pi.star_apply, Complex.star_def, Complex.conj_conj, hNherm, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hAadd : ∀ u v, A (u + v) (u + v) = A u u + A u v + A u v + A v v`. Introduce `u v`.

Use `hAsym v u` as an intermediate fact. Simplify using `only [A, mulVec_add, dotProduct_add, add_dotProduct] at this ⊢`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hKadd : ∀ u v, K (u + v) (u + v) = K u u + K u v + K v u + K v v`.

Introduce `u v`. Simplify using `only [K, star_add, mulVec_add, dotProduct_add, add_dotProduct]`. Expand and normalize the polynomial expressions, which then agree. Set `Hm : Matrix (Fin g) (Fin g) ℂ` to `(Real.pi⁻¹ : ℝ) • Nᵀ`. Establish `hHmK : ∀ x y, (Real.pi : ℂ) * (x ⬝ᵥ Hm *ᵥ star y) = K x y`.

Introduce `x y`. Simplify using `only [Hm, K, Matrix.smul_mulVec, dotProduct_smul, Complex.real_smul, Complex.ofReal_inv]`. Establish `: (Real.pi : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr Real.pi_ne_zero`. Clear the denominators using the available nonvanishing facts. Establish `hHerm : Hm.IsHermitian`.

Use `Matrix.IsHermitian.ext fun i j => ?_` and prove the remaining obligations. Simplify using `[Hm, hNherm]`. Establish `hint : ∀ l m : Λ, ∃ n : ℤ, ((l : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (m : Fin g → ℂ)).im = n`. Introduce `l m`. Take `⟨n, hn⟩` from `hskew l m`.

Rewrite `hn` using `[hBF, hBF, hAsym m l, hKherm l m]`. Establish `him` using `congrArg Complex.im hn`. Simplify using `[Complex.mul_im] at him`. Establish `h1 : Real.pi * ((l : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (m : Fin g → ℂ)).im = (K l m).im`. Rewrite using `[← hHmK]`.

Simplify using the standard rewrite rules. Use `⟨-n, ?_⟩` and prove the remaining obligations. Use `push_cast`. Apply `mul_left_cancel₀ Real.pi_pos.ne'` to reduce the goal to its premises. Rewrite using `[h1]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `choose e he using hint`. Establish `headd1 : ∀ l l' m, e (l + l') m = e l m + e l' m`. Introduce `l l' m`. Apply `Int.cast_injective (α := ℝ)` to reduce the goal to its premises.

Use `push_cast`. Rewrite using `[← he, ← he, ← he]`. Simplify using `only [Submodule.coe_add, add_dotProduct, Complex.add_im]`. Establish `headd2 : ∀ l m m', e l (m + m') = e l m + e l m'`. Introduce `l m m'`.

Apply `Int.cast_injective (α := ℝ)` to reduce the goal to its premises. Use `push_cast`. Rewrite using `[← he, ← he, ← he]`. Simplify using `only [Submodule.coe_add, star_add, mulVec_add, dotProduct_add, Complex.add_im]`. Set `Ef : LinearMap.BilinForm ℤ Λ` to `LinearMap.mk₂ ℤ e headd1 (fun c l m => map_zsmul (AddMonoidHom.mk' (fun l => e l m) (fun l l' => headd1 l l' m)) c l) headd2 (fun c l m => map_zsmul (AddMonoidHom.mk' (fun m => e l m) (fun m m' => headd2 l m m')) c m)`.

Establish `ha0 : a 0 = 1`. Establish `h` using `hcoc 0 0`. Rewrite `h` using `[add_zero, map_zero, LinearMap.zero_apply, Complex.exp_zero, mul_one]`. Conclude with `mul_left_cancel₀ (ha 0) (h.symm.trans (mul_one (a 0)).symm)`. Set `φ0 : Λ →+ ℝ` to `{ toFun := fun l => Real.log ‖a l‖ - (A l l).re / 2 - (K l l).re / 2 map_zero' := by simp [ha0, A, K] map_add' := fun l m => by`.

Rewrite using `[hcoc, norm_mul, norm_mul, Complex.norm_exp, Real.log_mul (mul_ne_zero (norm_ne_zero_iff.mpr (ha l)) (norm_ne_zero_iff.mpr (ha m))) (Real.exp_pos _).ne', Real.log_mul (norm_ne_zero_iff.mpr (ha l)) (norm_ne_zero_iff.mpr (ha m)), Real.log_exp, Submodule.coe_add, hAadd, hKadd, hBF, …`. Simplify using `only [Complex.add_re, Complex.conj_re]`. Use `ring }`. Take `⟨φ, hφ⟩` from `_root_.GlobalTheory.AppellHumbert.exists_real_extension Λ hΛ φ0`. Set `c : Fin g → ℂ` to `fun j => (φ (Pi.single j 1) : ℂ) - I * φ (Pi.single j I)`.

Establish `hc : ∀ u, (c ⬝ᵥ u).re = φ u`. Introduce `u`. Use `conv_rhs => rw [_root_.GlobalTheory.AppellHumbert.eq_sum_re_im u]`. Simplify using `only [map_sum, map_add, map_smul, smul_eq_mul, dotProduct, Complex.re_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `[c, Complex.mul_re]`. Expand and normalize the polynomial expressions, which then agree. Set `χ : Λ → ℂ` to `fun l => a l * cexp (-(A l l) / 2 - K l l / 2) * cexp (-(c ⬝ᵥ (l : Fin g → ℂ)))`. Establish `hχ : ∀ l, ‖χ l‖ = 1`. Introduce `l`.

Establish `h1 : (c ⬝ᵥ (l : Fin g → ℂ)).re = Real.log ‖a l‖ - (A l l).re / 2 - (K l l).re / 2`. Rewrite using `[hc, hφ]`. Both sides reduce to the same expression. Simplify using `only [χ, norm_mul, Complex.norm_exp, Complex.neg_re, Complex.sub_re, Complex.div_ofNat_re, h1, mul_assoc, ← Real.exp_add]`. Rewrite using `[show -(A ↑l ↑l).re / 2 - (K ↑l ↑l).re / 2 + -(Real.log ‖a l‖ - (A ↑l ↑l).re / 2 - (K ↑l ↑l).re / 2) = -Real.log ‖a l‖ by ring, Real.exp_neg, Real.exp_log (norm_pos_iff.mpr (ha l))]`.

Conclude with `mul_inv_cancel₀ (norm_ne_zero_iff.mpr (ha l))`. Set `Q : (Fin g → ℂ) → ℂ` to `fun z => A z z / 2 + c ⬝ᵥ z`. Use `⟨Hm, χ, Ef, Q, hHerm, hχ, fun l m => (he l m).symm, ?_, by simp [Q, A], ?_⟩` and prove the remaining obligations. Simplify using `only [Q, A, dotProduct, mulVec] fun_prop`. Introduce `l z`.

Establish `hQ : Q z - Q (z + l) = -A l z - A l l / 2 - c ⬝ᵥ l`. Simplify using `only [Q, dotProduct_add]`. Rewrite using `[hAadd, hAsym z l]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : (Real.pi : ℂ) / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (l : Fin g → ℂ)) = K l l / 2`.

Rewrite using `[← hHmK]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hHmK, h2, mul_assoc, ← Complex.exp_add, hBF, hQ]`. Simplify using `only [χ]`. Rewrite using `[mul_assoc, mul_assoc, ← Complex.exp_add, ← Complex.exp_add]`.

Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.GlobalTheory.appellHumbert_normal_form_of_linear_exponent :
    (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (a : Λ → ℂ) (B : Λ →+ ((Fin g → ℂ) →ₗ[ℂ] ℂ)), (∀ l, a l ≠ 0) → (∀ l m : Λ, a (l + m) = a l * a m * cexp (B l m)) → ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ) (Q : (Fin g → ℂ) → ℂ), Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im) ∧ Differentiable ℂ Q ∧ Q 0 = 0 ∧ ∀ (l : Λ) z, a l * cexp (B l z) * cexp (Q z - Q (z + l)) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))))) := by
  intro g Λ hdisc hΛ a B ha hcoc
  classical
  haveI := hdisc
  let b : Λ →+ (Fin g → ℂ) :=
    { toFun := fun l j => B l (Pi.single j 1)
      map_zero' := by ext j; simp
      map_add' := fun l m => by ext j; simp }
  obtain ⟨F, hF0⟩ := _root_.GlobalTheory.AppellHumbert.exists_real_extension Λ hΛ b
  have hF : ∀ (l : Λ) z, B l z = F l ⬝ᵥ z := by
    intro l z
    rw [hF0]
    conv_lhs => rw [show z = ∑ j, z j • (Pi.single j (1 : ℂ) : Fin g → ℂ) by ext i; simp [Pi.single_apply]]
    simp [map_sum, dotProduct, b, mul_comm]
  have hskew : ∀ l m : Λ, ∃ n : ℤ, B l m = B m l + n * (2 * π * I) := by
    intro l m
    have h := hcoc l m
    rw [add_comm, hcoc m l, mul_comm (a m) (a l)] at h
    exact Complex.exp_eq_exp_iff_exists_int.mp (mul_left_cancel₀ (mul_ne_zero (ha l) (ha m)) h).symm
  have hlin : ∀ (P : (Fin g → ℂ) → Prop), P 0 → (∀ x y, P x → P y → P (x + y)) →
      (∀ (c : ℝ) x, P x → P (c • x)) → (∀ l : Λ, P l) → ∀ x, P x := by
    intro P h0 hadd hsmul hl x
    have hx : x ∈ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) := by rw [hΛ]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy => exact hl ⟨y, hy⟩
    | zero => exact h0
    | add y z _ _ hy hz => exact hadd y z hy hz
    | smul c y _ hy => exact hsmul c y hy
  have hD1 : ∀ u (m : Λ), (F u ⬝ᵥ m - F m ⬝ᵥ u).re = 0 := by
    intro u m
    refine hlin (fun u => (F u ⬝ᵥ m - F m ⬝ᵥ u).re = 0) (by simp) (fun x y hx hy => ?_)
      (fun c x hx => ?_) (fun l => ?_) u
    · simp only [map_add, add_dotProduct, dotProduct_add, Complex.sub_re, Complex.add_re] at hx hy ⊢
      linarith
    · simp only [map_smul, smul_dotProduct, dotProduct_smul, Complex.sub_re, Complex.smul_re,
        smul_eq_mul] at hx ⊢
      rw [← mul_sub, hx, mul_zero]
    · obtain ⟨n, hn⟩ := hskew l m
      rw [← hF, ← hF, hn]; simp
  have hD : ∀ u v, (F u ⬝ᵥ v - F v ⬝ᵥ u).re = 0 := by
    intro u v
    refine hlin (fun v => (F u ⬝ᵥ v - F v ⬝ᵥ u).re = 0) (by simp) (fun x y hx hy => ?_)
      (fun c x hx => ?_) (fun m => hD1 u m) v
    · simp only [map_add, add_dotProduct, dotProduct_add, Complex.sub_re, Complex.add_re] at hx hy ⊢
      linarith
    · simp only [map_smul, smul_dotProduct, dotProduct_smul, Complex.sub_re, Complex.smul_re,
        smul_eq_mul] at hx ⊢
      rw [← mul_sub, hx, mul_zero]
  let M : Matrix (Fin g) (Fin g) ℂ := fun k j =>
    (1/2 : ℝ) • (F (Pi.single k 1) j - I * F (Pi.single k I) j)
  let N : Matrix (Fin g) (Fin g) ℂ := fun k j =>
    (1/2 : ℝ) • (F (Pi.single k 1) j + I * F (Pi.single k I) j)
  have hFMN : ∀ u, F u = u ᵥ* M + star u ᵥ* N := by
    intro u; ext j
    conv_lhs => rw [_root_.GlobalTheory.AppellHumbert.eq_sum_re_im u]
    simp only [map_sum, map_add, map_smul, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, vecMul,
      dotProduct, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    apply Complex.ext <;> simp [M, N, Complex.mul_re, Complex.mul_im] <;> ring
  have hsym : ∀ k j, (F (Pi.single k 1) j).re = (F (Pi.single j 1) k).re ∧
      (F (Pi.single k I) j).im = (F (Pi.single j I) k).im ∧
      (F (Pi.single k I) j).re = -(F (Pi.single j 1) k).im := by
    intro k j
    have h1 := hD (Pi.single k 1) (Pi.single j 1)
    have h2 := hD (Pi.single k I) (Pi.single j I)
    have h3 := hD (Pi.single k I) (Pi.single j 1)
    simp only [dotProduct_single, mul_one, Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, zero_sub, sub_zero] at h1 h2 h3
    refine ⟨by linarith, by linarith, by linarith⟩
  have hMsym : Mᵀ = M := by
    ext k j
    rw [transpose_apply]
    obtain ⟨a1, a2, a3⟩ := hsym k j
    obtain ⟨b1, b2, b3⟩ := hsym j k
    apply Complex.ext <;> simp [M, Complex.mul_re, Complex.mul_im] <;> linarith
  have hNherm : ∀ i j, (starRingEnd ℂ) (N i j) = N j i := by
    intro k j
    obtain ⟨a1, a2, a3⟩ := hsym k j
    obtain ⟨b1, b2, b3⟩ := hsym j k
    apply Complex.ext <;> simp [N, Complex.mul_re, Complex.mul_im] <;> linarith

  let A : (Fin g → ℂ) → (Fin g → ℂ) → ℂ := fun u v => u ⬝ᵥ M *ᵥ v
  let K : (Fin g → ℂ) → (Fin g → ℂ) → ℂ := fun z u => z ⬝ᵥ Nᵀ *ᵥ star u
  have hAsym : ∀ u v, A u v = A v u := by
    intro u v
    simp only [A]
    conv_rhs => rw [← hMsym]
    rw [mulVec_transpose, dotProduct_comm v, ← dotProduct_mulVec]
  have hBF : ∀ (l : Λ) z, B l z = A l z + K z l := by
    intro l z
    simp only [A, K]
    rw [hF, hFMN, add_dotProduct, dotProduct_mulVec, mulVec_transpose, dotProduct_comm z]
  have hKherm : ∀ u v, K v u = (starRingEnd ℂ) (K u v) := by
    intro u v
    simp only [K, dotProduct, mulVec, transpose_apply, map_sum, map_mul, Pi.star_apply,
      Complex.star_def, Complex.conj_conj, hNherm, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hAadd : ∀ u v, A (u + v) (u + v) = A u u + A u v + A u v + A v v := by
    intro u v
    have := hAsym v u
    simp only [A, mulVec_add, dotProduct_add, add_dotProduct] at this ⊢
    rw [this]; ring
  have hKadd : ∀ u v, K (u + v) (u + v) = K u u + K u v + K v u + K v v := by
    intro u v
    simp only [K, star_add, mulVec_add, dotProduct_add, add_dotProduct]
    ring

  let Hm : Matrix (Fin g) (Fin g) ℂ := (Real.pi⁻¹ : ℝ) • Nᵀ
  have hHmK : ∀ x y, (Real.pi : ℂ) * (x ⬝ᵥ Hm *ᵥ star y) = K x y := by
    intro x y
    simp only [Hm, K, Matrix.smul_mulVec, dotProduct_smul, Complex.real_smul, Complex.ofReal_inv]
    have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  have hHerm : Hm.IsHermitian := by
    refine Matrix.IsHermitian.ext fun i j => ?_
    simp [Hm, hNherm]
  have hint : ∀ l m : Λ, ∃ n : ℤ, ((l : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (m : Fin g → ℂ)).im = n := by
    intro l m
    obtain ⟨n, hn⟩ := hskew l m
    rw [hBF, hBF, hAsym m l, hKherm l m] at hn
    have him := congrArg Complex.im hn
    simp [Complex.mul_im] at him
    have h1 : Real.pi * ((l : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (m : Fin g → ℂ)).im = (K l m).im := by
      rw [← hHmK]; simp
    refine ⟨-n, ?_⟩
    push_cast
    apply mul_left_cancel₀ Real.pi_pos.ne'
    rw [h1]; linarith
  choose e he using hint
  have headd1 : ∀ l l' m, e (l + l') m = e l m + e l' m := by
    intro l l' m
    apply Int.cast_injective (α := ℝ)
    push_cast
    rw [← he, ← he, ← he]
    simp only [Submodule.coe_add, add_dotProduct, Complex.add_im]
  have headd2 : ∀ l m m', e l (m + m') = e l m + e l m' := by
    intro l m m'
    apply Int.cast_injective (α := ℝ)
    push_cast
    rw [← he, ← he, ← he]
    simp only [Submodule.coe_add, star_add, mulVec_add, dotProduct_add, Complex.add_im]
  let Ef : LinearMap.BilinForm ℤ Λ := LinearMap.mk₂ ℤ e headd1
    (fun c l m => map_zsmul (AddMonoidHom.mk' (fun l => e l m) (fun l l' => headd1 l l' m)) c l)
    headd2
    (fun c l m => map_zsmul (AddMonoidHom.mk' (fun m => e l m) (fun m m' => headd2 l m m')) c m)
  have ha0 : a 0 = 1 := by
    have h := hcoc 0 0
    rw [add_zero, map_zero, LinearMap.zero_apply, Complex.exp_zero, mul_one] at h
    exact mul_left_cancel₀ (ha 0) (h.symm.trans (mul_one (a 0)).symm)
  let φ0 : Λ →+ ℝ :=
    { toFun := fun l => Real.log ‖a l‖ - (A l l).re / 2 - (K l l).re / 2
      map_zero' := by simp [ha0, A, K]
      map_add' := fun l m => by
        rw [hcoc, norm_mul, norm_mul, Complex.norm_exp,
          Real.log_mul (mul_ne_zero (norm_ne_zero_iff.mpr (ha l)) (norm_ne_zero_iff.mpr (ha m)))
            (Real.exp_pos _).ne',
          Real.log_mul (norm_ne_zero_iff.mpr (ha l)) (norm_ne_zero_iff.mpr (ha m)), Real.log_exp,
          Submodule.coe_add, hAadd, hKadd, hBF, hKherm (l : Fin g → ℂ) m]
        simp only [Complex.add_re, Complex.conj_re]
        ring }
  obtain ⟨φ, hφ⟩ := _root_.GlobalTheory.AppellHumbert.exists_real_extension Λ hΛ φ0
  let c : Fin g → ℂ := fun j => (φ (Pi.single j 1) : ℂ) - I * φ (Pi.single j I)
  have hc : ∀ u, (c ⬝ᵥ u).re = φ u := by
    intro u
    conv_rhs => rw [_root_.GlobalTheory.AppellHumbert.eq_sum_re_im u]
    simp only [map_sum, map_add, map_smul, smul_eq_mul, dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [c, Complex.mul_re]
    ring
  let χ : Λ → ℂ := fun l => a l * cexp (-(A l l) / 2 - K l l / 2) * cexp (-(c ⬝ᵥ (l : Fin g → ℂ)))
  have hχ : ∀ l, ‖χ l‖ = 1 := by
    intro l
    have h1 : (c ⬝ᵥ (l : Fin g → ℂ)).re = Real.log ‖a l‖ - (A l l).re / 2 - (K l l).re / 2 := by
      rw [hc, hφ]; rfl
    simp only [χ, norm_mul, Complex.norm_exp, Complex.neg_re, Complex.sub_re, Complex.div_ofNat_re,
      h1, mul_assoc, ← Real.exp_add]
    rw [show -(A ↑l ↑l).re / 2 - (K ↑l ↑l).re / 2 +
        -(Real.log ‖a l‖ - (A ↑l ↑l).re / 2 - (K ↑l ↑l).re / 2) = -Real.log ‖a l‖ by ring,
      Real.exp_neg, Real.exp_log (norm_pos_iff.mpr (ha l))]
    exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr (ha l))
  let Q : (Fin g → ℂ) → ℂ := fun z => A z z / 2 + c ⬝ᵥ z
  refine ⟨Hm, χ, Ef, Q, hHerm, hχ, fun l m => (he l m).symm, ?_, by simp [Q, A], ?_⟩
  · simp only [Q, A, dotProduct, mulVec]
    fun_prop
  · intro l z
    have hQ : Q z - Q (z + l) = -A l z - A l l / 2 - c ⬝ᵥ l := by
      simp only [Q, dotProduct_add]
      rw [hAadd, hAsym z l]; ring
    have h2 : (Real.pi : ℂ) / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (l : Fin g → ℂ)) = K l l / 2 := by
      rw [← hHmK]; ring
    rw [hHmK, h2, mul_assoc, ← Complex.exp_add, hBF, hQ]
    simp only [χ]
    rw [mul_assoc, mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    ring

end GlobalTheory
