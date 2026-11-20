import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockSphereMeanEqOfFrameNormEq

set_option autoImplicit false

noncomputable section

open MvPolynomial NumberField Module GlobalTheory.ChowHt GlobalTheory.CompHt

namespace GlobalTheory.ImageHeightUnique

set_option autoImplicit false in
open MvPolynomial NumberField Module in
open scoped Matrix in

/- English proof (translation)
Unfold `_root_.GlobalTheory.ChowHt.linSubst`. Establish `key : (MvPolynomial.map φ).comp (aeval fun p : Fin B × Fin N ↦ ∑ k, C (M p.2 k) * X (p.1, k)).toRingHom = (aeval fun p : Fin B × Fin N ↦ ∑ k, C (M.map φ p.2 k) * X (p.1, k)).toRingHom.comp (MvPolynomial.map φ)`. Apply the tactic sequence `apply MvPolynomial.ringHom_ext <;> intro <;> simp [map_sum]`. Conclude with `RingHom.congr_fun key f`.
-/
theorem _root_.GlobalTheory.ImageHeightUnique.map_linSubst {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {B N n : ℕ} (M : Matrix (Fin N) (Fin n) R)
    (f : MvPolynomial (Fin B × Fin N) R) :
    MvPolynomial.map φ (_root_.GlobalTheory.ChowHt.linSubst M f) = _root_.GlobalTheory.ChowHt.linSubst (M.map φ) (MvPolynomial.map φ f) := by
  unfold _root_.GlobalTheory.ChowHt.linSubst
  have key : (MvPolynomial.map φ).comp
      (aeval fun p : Fin B × Fin N ↦ ∑ k, C (M p.2 k) * X (p.1, k)).toRingHom =
      (aeval fun p : Fin B × Fin N ↦ ∑ k, C (M.map φ p.2 k) * X (p.1, k)).toRingHom.comp
        (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext <;> intro <;> simp [map_sum]
  exact RingHom.congr_fun key f

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] {N : ℕ}

omit [NumberField K] in

/- English proof (translation)
Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Use `congr 2`. Use function extensionality and compare the values at `k i`. Simplify using `[Matrix.mul_apply, Basis.toMatrix_apply, mul_comm]`.
-/
theorem map_span (b b' : Basis (Fin N) K V) {n : ℕ} (w : Matrix (Fin N) (Fin n) K) :
    (Submodule.span (𝓞 K) (Set.range fun k => ∑ j, w j k • b' j)).map (b.equivFun.toLinearMap.restrictScalars (𝓞 K)) =
      Submodule.span (𝓞 K) (Set.range (b.toMatrix b' * w).col) := by
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext k i
  simp [Matrix.mul_apply, Basis.toMatrix_apply, mul_comm]

set_option autoImplicit false in
open MvPolynomial NumberField Module in
open scoped Matrix in
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] {N : ℕ} in
/- English proof (translation)
Establish `hL` using `h.span`. Establish `hL'` using `h'.span`. Establish `hmem : ∀ k : Fin n', (∑ j, w' j k • b' j) ∈ Submodule.span (𝓞 K) (Set.range fun i ↦ ∑ j, w j i • b j)`. Introduce `k`. Rewrite using `[hL, ← hL']`.

Conclude with `Submodule.subset_span ⟨k, rfl⟩`. Use `choose c hc using fun k => (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 (hmem k)`. Use `⟨Matrix.of fun i k => c k i, ?_⟩` and prove the remaining obligations. Use extensionality with `j k`. Establish `hk` using `congr_arg (fun x => b.repr x j) (hc k)`.

Simplify using `only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at hk`. Simplify using `only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Basis.toMatrix_apply]`. Rewrite using `[show (∑ x, (b.repr (b' x)) j * w' x k) = ∑ x, w' x k * (b.repr (b' x)) j from Finset.sum_congr rfl fun _ _ => mul_comm _ _, ← hk]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← IsScalarTower.algebraMap_smul K (c k i), map_smul, Finsupp.smul_apply, smul_eq_mul]`.

Simplify using `[map_sum, Finsupp.single_apply, mul_comm]`.
-/
private theorem exists_integral_matrix_toMatrix_mul_eq_of_isFrame {Nm : (K →+* ℂ) → V → ℝ} {L : Submodule (𝓞 K) V}
    {n n' : ℕ} {b b' : Basis (Fin N) K V} {w : Matrix (Fin N) (Fin n) K}
    {w' : Matrix (Fin N) (Fin n') K} {A A' : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ}
    (h : _root_.GlobalTheory.CompHt.IsFrame Nm L b w A) (h' : _root_.GlobalTheory.CompHt.IsFrame Nm L b' w' A') :
    ∃ U : Matrix (Fin n) (Fin n') (𝓞 K), b.toMatrix b' * w' = w * U.map ((↑) : 𝓞 K → K) := by
  have hL := h.span
  have hL' := h'.span
  have hmem : ∀ k : Fin n', (∑ j, w' j k • b' j) ∈
      Submodule.span (𝓞 K) (Set.range fun i ↦ ∑ j, w j i • b j) := by
    intro k
    rw [hL, ← hL']
    exact Submodule.subset_span ⟨k, rfl⟩
  choose c hc using fun k => (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 (hmem k)
  refine ⟨Matrix.of fun i k => c k i, ?_⟩
  ext j k
  have hk := congr_arg (fun x => b.repr x j) (hc k)
  simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul,
    Pi.smul_apply, smul_eq_mul] at hk
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Basis.toMatrix_apply]
  rw [show (∑ x, (b.repr (b' x)) j * w' x k) = ∑ x, w' x k * (b.repr (b' x)) j from
    Finset.sum_congr rfl fun _ _ => mul_comm _ _, ← hk]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← IsScalarTower.algebraMap_smul K (c k i), map_smul, Finsupp.smul_apply, smul_eq_mul]
  simp [map_sum, Finsupp.single_apply, mul_comm]

set_option autoImplicit false in
open MvPolynomial NumberField Module in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
/- English proof (translation)
Unfold `_root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs`. Rewrite using `[← Real.coe_toNNReal c hc, NNReal.coe_le_coe]`. Conclude with `Finset.sup_le fun s _ => Real.toNNReal_le_toNNReal (h s)`.
-/
private theorem gaussAbs_le_of_forall_coeff_le {ι : Type} {v : FinitePlace K} {p : MvPolynomial ι K}
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ s, v (coeff s p) ≤ c) : _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v p ≤ c := by
  unfold _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs
  rw [← Real.coe_toNNReal c hc, NNReal.coe_le_coe]
  exact Finset.sup_le fun s _ => Real.toNNReal_le_toNNReal (h s)

set_option autoImplicit false in
open MvPolynomial NumberField Module in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => simpa using hc`. Consider the case `insert a t ha ih`. Rewrite using `[Finset.sum_insert ha]`. Use `(FinitePlace.add_le v _ _).trans (max_le (h a (Finset.mem_insert_self a t)) ?_)` and prove the remaining obligations.

Conclude with `ih fun x hx => h x (Finset.mem_insert_of_mem hx)`.
-/
private theorem finitePlace_finset_sum_le_of_forall_le {α : Type} (v : FinitePlace K) (t : Finset α) (g : α → K)
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ x ∈ t, v (g x) ≤ c) : v (∑ x ∈ t, g x) ≤ c := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hc
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    refine (FinitePlace.add_le v _ _).trans (max_le (h a (Finset.mem_insert_self a t)) ?_)
    exact ih fun x hx => h x (Finset.mem_insert_of_mem hx)

set_option autoImplicit false in
open MvPolynomial NumberField Module in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
/- English proof (translation)
Unfold `_root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs`. Conclude with `NNReal.coe_nonneg _`.
-/
private theorem gaussAbs_nonneg' {ι : Type} (v : FinitePlace K) (p : MvPolynomial ι K) :
    0 ≤ _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v p := by
  unfold _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs
  exact NNReal.coe_nonneg _

set_option autoImplicit false in
open MvPolynomial NumberField Module in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
/- English proof (translation)
Distinguish the cases in `h : coeff s p = 0`. Rewrite using `[h, map_zero]`. Conclude with `gaussAbs_nonneg' v p`. Unfold `_root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs`. Establish `hs` using `Finset.le_sup (f := fun s => (v (coeff s p)).toNNReal) (mem_support_iff.2 h)`.

Combine the equalities or inequalities in the displayed calculation.
-/
private theorem finitePlace_coeff_le_gaussAbs {ι : Type} (v : FinitePlace K) (p : MvPolynomial ι K)
    (s : ι →₀ ℕ) : v (coeff s p) ≤ _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v p := by
  by_cases h : coeff s p = 0
  · rw [h, map_zero]; exact gaussAbs_nonneg' v p
  unfold _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs
  have hs := Finset.le_sup (f := fun s => (v (coeff s p)).toNNReal) (mem_support_iff.2 h)
  calc v (coeff s p) = ((v (coeff s p)).toNNReal : ℝ) :=
        (Real.coe_toNNReal _ (apply_nonneg v _)).symm
    _ ≤ _ := NNReal.coe_le_coe.2 hs

set_option autoImplicit false in
open MvPolynomial NumberField Module in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
/- English proof (translation)
Use `gaussAbs_le_of_forall_coeff_le hc fun s => ?_` and prove the remaining obligations. Rewrite using `[coeff_sum]`. Conclude with `finitePlace_finset_sum_le_of_forall_le v t _ hc fun x hx => (finitePlace_coeff_le_gaussAbs v _ s).trans (h x hx)`.
-/
private theorem gaussAbs_finset_sum_le_of_forall_le {ι α : Type} (v : FinitePlace K) (t : Finset α)
    (F : α → MvPolynomial ι K) {c : ℝ} (hc : 0 ≤ c) (h : ∀ x ∈ t, _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v (F x) ≤ c) :
    _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v (∑ x ∈ t, F x) ≤ c := by
  refine gaussAbs_le_of_forall_coeff_le hc fun s => ?_
  rw [coeff_sum]
  exact finitePlace_finset_sum_le_of_forall_le v t _ hc fun x hx => (finitePlace_coeff_le_gaussAbs v _ s).trans (h x hx)

set_option autoImplicit false in
open MvPolynomial NumberField Module in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
/- English proof (translation)
Use `gaussAbs_le_of_forall_coeff_le (mul_nonneg (apply_nonneg v c) (gaussAbs_nonneg' v p)) fun s => ?_` and prove the remaining obligations. Rewrite using `[coeff_C_mul, map_mul]`. Conclude with `mul_le_mul_of_nonneg_left (finitePlace_coeff_le_gaussAbs v p s) (apply_nonneg v c)`.
-/
private theorem gaussAbs_C_mul_le' {ι : Type} (v : FinitePlace K) (c : K) (p : MvPolynomial ι K) :
    _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v (C c * p) ≤ v c * _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v p := by
  refine gaussAbs_le_of_forall_coeff_le (mul_nonneg (apply_nonneg v c) (gaussAbs_nonneg' v p)) fun s => ?_
  rw [coeff_C_mul, map_mul]
  exact mul_le_mul_of_nonneg_left (finitePlace_coeff_le_gaussAbs v p s) (apply_nonneg v c)

set_option autoImplicit false in
open MvPolynomial NumberField Module in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
/- English proof (translation)
Use `gaussAbs_le_of_forall_coeff_le zero_le_one fun s => ?_` and prove the remaining obligations. Rewrite using `[coeff_one]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem gaussAbs_one_le_one {ι : Type} (v : FinitePlace K) :
    _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v (1 : MvPolynomial ι K) ≤ 1 := by
  classical
  refine gaussAbs_le_of_forall_coeff_le zero_le_one fun s => ?_
  rw [coeff_one]
  split_ifs <;> simp

set_option autoImplicit false in
open MvPolynomial NumberField Module in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
/- English proof (translation)
Use `gaussAbs_le_of_forall_coeff_le (mul_nonneg (gaussAbs_nonneg' v p) (gaussAbs_nonneg' v q)) fun s => ?_` and prove the remaining obligations. Rewrite using `[coeff_mul]`. Use `finitePlace_finset_sum_le_of_forall_le v _ _ (mul_nonneg (gaussAbs_nonneg' v p) (gaussAbs_nonneg' v q)) fun x _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_le_mul (finitePlace_coeff_le_gaussAbs v p _) (finitePlace_coeff_le_gaussAbs v q _) (apply_nonneg v _) (gaussAbs_nonneg' v p)`.
-/
private theorem gaussAbs_mul_le' {ι : Type} (v : FinitePlace K) (p q : MvPolynomial ι K) :
    _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v (p * q) ≤ _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v p * _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v q := by
  classical
  refine gaussAbs_le_of_forall_coeff_le (mul_nonneg (gaussAbs_nonneg' v p) (gaussAbs_nonneg' v q))
    fun s => ?_
  rw [coeff_mul]
  refine finitePlace_finset_sum_le_of_forall_le v _ _ (mul_nonneg (gaussAbs_nonneg' v p) (gaussAbs_nonneg' v q))
    fun x _ => ?_
  rw [map_mul]
  exact mul_le_mul (finitePlace_coeff_le_gaussAbs v p _) (finitePlace_coeff_le_gaussAbs v q _)
    (apply_nonneg v _) (gaussAbs_nonneg' v p)

set_option autoImplicit false in
open MvPolynomial NumberField Module in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => simpa using gaussAbs_one_le_one v`. Consider the case `insert a t ha ih`. Rewrite using `[Finset.prod_insert ha]`. Use `(gaussAbs_mul_le' v _ _).trans ?_` and prove the remaining obligations.

Establish `h1` using `h a (Finset.mem_insert_self a t)`. Establish `h2` using `ih fun x hx => h x (Finset.mem_insert_of_mem hx)`. Use polynomial arithmetic with `[gaussAbs_nonneg' v (F a), gaussAbs_nonneg' v (∏ x ∈ t, F x)]`.
-/
private theorem gaussAbs_finset_prod_le_one_of_forall_le_one {ι α : Type} (v : FinitePlace K) (t : Finset α)
    (F : α → MvPolynomial ι K) (h : ∀ x ∈ t, _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v (F x) ≤ 1) :
    _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v (∏ x ∈ t, F x) ≤ 1 := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using gaussAbs_one_le_one v
  | insert a t ha ih =>
    rw [Finset.prod_insert ha]
    refine (gaussAbs_mul_le' v _ _).trans ?_
    have h1 := h a (Finset.mem_insert_self a t)
    have h2 := ih fun x hx => h x (Finset.mem_insert_of_mem hx)
    nlinarith [gaussAbs_nonneg' v (F a), gaussAbs_nonneg' v (∏ x ∈ t, F x)]

set_option autoImplicit false in
open MvPolynomial NumberField Module in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
/- English proof (translation)
Simplify using `using gaussAbs_finset_prod_le_one_of_forall_le_one v (Finset.range n) (fun _ => p) (fun _ _ => hp)`.
-/
private theorem gaussAbs_pow_le_one_of_le_one {ι : Type} (v : FinitePlace K) (p : MvPolynomial ι K)
    (hp : _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v p ≤ 1) (n : ℕ) : _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v (p ^ n) ≤ 1 := by
  simpa using gaussAbs_finset_prod_le_one_of_forall_le_one v (Finset.range n) (fun _ => p) (fun _ _ => hp)

set_option autoImplicit false in
open MvPolynomial NumberField Module in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
/- English proof (translation)
Use `conv_lhs => rw [g.as_sum]`. Rewrite using `[map_sum]`. Use `gaussAbs_finset_sum_le_of_forall_le v _ _ (gaussAbs_nonneg' v g) fun s _ => ?_` and prove the remaining obligations. Rewrite using `[aeval_monomial, algebraMap_eq]`. Use `(gaussAbs_C_mul_le' v _ _).trans ?_` and prove the remaining obligations.

Establish `hprod : _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v (s.prod fun i k => ψ i ^ k) ≤ 1` using `gaussAbs_finset_prod_le_one_of_forall_le_one v _ _ fun i _ => gaussAbs_pow_le_one_of_le_one v _ (hψ i) _`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem gaussAbs_aeval_le_of_gaussAbs_le_one {ι κ : Type} (v : FinitePlace K) (ψ : ι → MvPolynomial κ K)
    (hψ : ∀ i, _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v (ψ i) ≤ 1) (g : MvPolynomial ι K) :
    _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v (aeval ψ g) ≤ _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v g := by
  conv_lhs => rw [g.as_sum]
  rw [map_sum]
  refine gaussAbs_finset_sum_le_of_forall_le v _ _ (gaussAbs_nonneg' v g) fun s _ => ?_
  rw [aeval_monomial, algebraMap_eq]
  refine (gaussAbs_C_mul_le' v _ _).trans ?_
  have hprod : _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v (s.prod fun i k => ψ i ^ k) ≤ 1 :=
    gaussAbs_finset_prod_le_one_of_forall_le_one v _ _ fun i _ => gaussAbs_pow_le_one_of_le_one v _ (hψ i) _
  calc v (coeff s g) * _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v (s.prod fun i k => ψ i ^ k) ≤ v (coeff s g) * 1 :=
        mul_le_mul_of_nonneg_left hprod (apply_nonneg v _)
    _ ≤ _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v g := by rw [mul_one]; exact finitePlace_coeff_le_gaussAbs v g s

set_option autoImplicit false in
open MvPolynomial NumberField Module in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
/- English proof (translation)
Take `⟨P, hP⟩` from `v.2`. Establish `h` using `FinitePlace.norm_le_one K P x`. Establish `: v (x : K) = place (FinitePlace.embedding P) (x : K)` using `by rw [hP]; rfl`. Rewrite using `[this]`. Conclude with `h`.
-/
private theorem finitePlace_coe_ringOfIntegers_le_one (v : FinitePlace K) (x : 𝓞 K) : v (x : K) ≤ 1 := by
  obtain ⟨P, hP⟩ := v.2
  have h := FinitePlace.norm_le_one K P x
  have : v (x : K) = place (FinitePlace.embedding P) (x : K) := by rw [hP]; rfl
  rw [this]
  exact h

set_option autoImplicit false in
open MvPolynomial NumberField Module in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
/- English proof (translation)
Use `gaussAbs_le_of_forall_coeff_le zero_le_one fun s => ?_` and prove the remaining obligations. Rewrite using `[coeff_X']`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem gaussAbs_X_le_one {ι : Type} (v : FinitePlace K) (i : ι) :
    _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v (X i : MvPolynomial ι K) ≤ 1 := by
  classical
  refine gaussAbs_le_of_forall_coeff_le zero_le_one fun s => ?_
  rw [coeff_X']
  split_ifs <;> simp

set_option autoImplicit false in
open MvPolynomial NumberField Module in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
/- English proof (translation)
Unfold `_root_.GlobalTheory.ChowHt.linSubst`. Use `gaussAbs_aeval_le_of_gaussAbs_le_one v _ (fun p => ?_) g` and prove the remaining obligations. Use `gaussAbs_finset_sum_le_of_forall_le v _ _ zero_le_one fun k _ => ?_` and prove the remaining obligations. Use `(gaussAbs_C_mul_le' v _ _).trans ?_` and prove the remaining obligations. Establish `h1 : v (U.map ((↑) : 𝓞 K → K) p.2 k) ≤ 1` using `finitePlace_coe_ringOfIntegers_le_one v _`.

Establish `h2` using `gaussAbs_X_le_one (K := K) v (p.1, k)`. Use polynomial arithmetic with `[apply_nonneg v (U.map ((↑) : 𝓞 K → K) p.2 k), gaussAbs_nonneg' v (X (p.1, k) : MvPolynomial (Fin B × Fin n) K)]`.
-/
private theorem gaussAbs_linSubst_integral_matrix_le {B N n : ℕ} (v : FinitePlace K)
    (U : Matrix (Fin N) (Fin n) (𝓞 K)) (g : MvPolynomial (Fin B × Fin N) K) :
    _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v (_root_.GlobalTheory.ChowHt.linSubst (U.map ((↑) : 𝓞 K → K)) g) ≤ _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v g := by
  unfold _root_.GlobalTheory.ChowHt.linSubst
  refine gaussAbs_aeval_le_of_gaussAbs_le_one v _ (fun p => ?_) g
  refine gaussAbs_finset_sum_le_of_forall_le v _ _ zero_le_one fun k _ => ?_
  refine (gaussAbs_C_mul_le' v _ _).trans ?_
  have h1 : v (U.map ((↑) : 𝓞 K → K) p.2 k) ≤ 1 := finitePlace_coe_ringOfIntegers_le_one v _
  have h2 := gaussAbs_X_le_one (K := K) v (p.1, k)
  nlinarith [apply_nonneg v (U.map ((↑) : 𝓞 K → K) p.2 k), gaussAbs_nonneg' v (X (p.1, k) : MvPolynomial (Fin B × Fin n) K)]

set_option autoImplicit false in
open MvPolynomial NumberField Module in
open scoped Matrix in
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] {N : ℕ} in
/- English proof (translation)
Use `set P := b.toMatrix b' with hP`. Establish `hflip : P * b'.toMatrix b = 1` using `Basis.toMatrix_mul_toMatrix_flip b b'`. Establish `hdetP : P.det ≠ 0`. Introduce `h0`. Establish `h1` using `congr_arg Matrix.det hflip`.

Rewrite `h1` using `[Matrix.det_mul, h0, zero_mul, Matrix.det_one]`. Conclude with `zero_ne_one h1`. Establish `hdetPσ : (P.map σ).det ≠ 0`. Rewrite using `[show (P.map σ).det = σ P.det from (RingHom.map_det σ _).symm]`. Conclude with `(map_ne_zero σ).2 hdetP`.

Establish `hA : ∀ y : Fin N → K, _root_.GlobalTheory.ChowHt.frameNorm (A' σ) (fun j => σ (y j)) = _root_.GlobalTheory.ChowHt.frameNorm (A σ) (fun j => σ ((P *ᵥ y) j))`. Introduce `y`. Establish `h1` using `h'.norm σ (b'.equivFun.symm y)`. Establish `h2` using `h.norm σ (b'.equivFun.symm y)`. Establish `r1 : ⇑(b'.repr (b'.equivFun.symm y)) = y`.

Rewrite using `[← Basis.equivFun_apply]`. Conclude with `b'.equivFun.apply_symm_apply y`. Establish `r2 : ⇑(b.repr (b'.equivFun.symm y)) = P *ᵥ y`. Establish `t` using `Basis.toMatrix_mulVec_repr b' b (b'.equivFun.symm y)`. Rewrite `t` using `[r1]`.

Rewrite using `[hP]`. Conclude with `t.symm`. Rewrite `h1` using `[r1]`. Rewrite `h2` using `[r2]`. Rewrite using `[h1, h2]`.

Establish `hB : ∀ u : Fin N → ℂ, _root_.GlobalTheory.ChowHt.frameNorm (P.map σ * A' σ) (P.map σ *ᵥ u) = _root_.GlobalTheory.ChowHt.frameNorm (A' σ) u`. Introduce `u`. Unfold `_root_.GlobalTheory.ChowHt.frameNorm`. Rewrite using `[Matrix.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdetPσ), Matrix.mul_one]`. Establish `hmap : ∀ y : Fin N → K, (fun j => σ ((P *ᵥ y) j)) = P.map σ *ᵥ fun j => σ (y j)`.

Introduce `y`. Use function extensionality and compare the values at `j`. Conclude with `RingHom.map_mulVec σ P y j`. Establish `hK : ∀ y : Fin N → K, _root_.GlobalTheory.ChowHt.frameNorm (P.map σ * A' σ) (fun j => σ (y j)) = _root_.GlobalTheory.ChowHt.frameNorm (A σ) (fun j => σ (y j))`. Introduce `y`.

Establish `hy : P *ᵥ (P⁻¹ *ᵥ y) = y`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdetP), Matrix.one_mulVec]`. Rewrite using `[← hy, hmap, hB, hA, hy, ← hmap, hy]`. Use `set G₁ := (P.map σ * A' σ)⁻¹`. Use `set G₂ := (A σ)⁻¹`.

Use `set H := G₁ᴴ * G₁ - G₂ᴴ * G₂ with hH`. Establish `hsq : ∀ (M : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ), _root_.GlobalTheory.ChowHt.frameNorm M x ^ 2 = (star x ⬝ᵥ ((M⁻¹)ᴴ * M⁻¹) *ᵥ x).re`. Introduce `M x`. Unfold `_root_.GlobalTheory.ChowHt.frameNorm`. Rewrite using `[Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]`.

Rewrite using `[← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, dotProduct]`. Simplify using `[Complex.re_sum, Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, mul_comm]`. Establish `hdiff : ∀ x : Fin N → ℂ, (star x ⬝ᵥ H *ᵥ x).re = _root_.GlobalTheory.ChowHt.frameNorm (P.map σ * A' σ) x ^ 2 - _root_.GlobalTheory.ChowHt.frameNorm (A σ) x ^ 2`. Introduce `x`. Rewrite using `[hsq, hsq, hH, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]`.

Establish `hpair : ∀ (j k : Fin N) (c : ℂ), (star (Pi.single j 1 + c • Pi.single k 1 : Fin N → ℂ) ⬝ᵥ H *ᵥ (Pi.single j 1 + c • Pi.single k 1)).re = (H j j).re + 2 * (c * H j k).re + Complex.normSq c * (H k k).re`. Introduce `j k c`. Establish `hherm : H k j = star (H j k)`. Rewrite using `[hH]`. Simplify using `[Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm]`.

Establish `e : star (Pi.single j 1 + c • Pi.single k 1 : Fin N → ℂ) ⬝ᵥ H *ᵥ (Pi.single j 1 + c • Pi.single k 1) = H j j + star c * H k j + c * H j k + star c * c * H k k`. Simplify using `[Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, Pi.star_single]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, hherm]`. Simplify using `[Complex.mul_re, Complex.normSq_apply]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hzeroK : ∀ y : Fin N → K, (star (fun j => σ (y j)) ⬝ᵥ H *ᵥ fun j => σ (y j)).re = 0`. Introduce `y`. Rewrite using `[hdiff, hK, sub_self]`. Establish `hdiag : ∀ j, (H j j).re = 0`.

Introduce `j`. Use `hzeroK (Pi.single j 1)` as an intermediate fact. Establish `e : (fun i => σ ((Pi.single j 1 : Fin N → K) i)) = (Pi.single j 1 + (0 : ℂ) • Pi.single j 1 : Fin N → ℂ)`. Apply the tactic sequence `funext i; by_cases hi : i = j <;> simp [hi, Pi.single_apply]`. Rewrite `this` using `[e, hpair]`.

Simplify using `using this`. Establish `hre : ∀ (j k : Fin N) (a : K), (σ a * H j k).re = 0`. Introduce `j k a`. Use `hzeroK (Pi.single j 1 + a • Pi.single k 1)` as an intermediate fact. Establish `e : (fun i => σ ((Pi.single j 1 + a • Pi.single k 1 : Fin N → K) i)) = (Pi.single j 1 + σ a • Pi.single k 1 : Fin N → ℂ)`.

Apply the tactic sequence `funext i; simp [Pi.single_apply]; split_ifs <;> simp`. Rewrite `this` using `[e, hpair, hdiag, hdiag]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hHz : H = 0`. Use extensionality with `j k`.

Establish `h1 : (H j k).re = 0` using `by simpa using hre j k 1`. Distinguish the cases in `hreal : ∃ a : K, (σ a).im ≠ 0`. Take `⟨a, ha⟩` from `hreal`. Establish `h2` using `hre j k a`. Rewrite `h2` using `[Complex.mul_re, h1, mul_zero, zero_sub, neg_eq_zero]`.

Conclude with `Complex.ext h1 ((mul_eq_zero.1 h2).resolve_left ha)`. Use `push_neg at hreal`. Establish `hσ : (starRingEnd ℂ).comp σ = σ`. Use extensionality with `a`. Simplify using `[Complex.ext_iff, hreal a]`.

Establish `hPr : ∀ u : Fin N → ℂ, star (P.map σ *ᵥ u) = P.map σ *ᵥ star u`. Introduce `u`. Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.star_apply, star_sum, star_mul', Matrix.map_apply]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Establish `hs : star (σ (P i l)) = σ (P i l)` using `congr_fun (congr_arg DFunLike.coe hσ) (P i l)`. Rewrite using `[hs]`. Establish `hc2 : ∀ x, _root_.GlobalTheory.ChowHt.frameNorm (A σ) (star x) = _root_.GlobalTheory.ChowHt.frameNorm (A σ) x`. Introduce `x`. Use `h.conj σ x` as an intermediate fact.

Rewrite `this` using `[hσ]`. Conclude with `this`. Establish `hc1 : ∀ x, _root_.GlobalTheory.ChowHt.frameNorm (P.map σ * A' σ) (star x) = _root_.GlobalTheory.ChowHt.frameNorm (P.map σ * A' σ) x`. Introduce `x`. Establish `hx : P.map σ *ᵥ ((P.map σ)⁻¹ *ᵥ x) = x`.

Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdetPσ), Matrix.one_mulVec]`. Use `h'.conj σ ((P.map σ)⁻¹ *ᵥ x)` as an intermediate fact. Rewrite `this` using `[hσ]`. Use `conv_lhs => rw [← hx]`. Use `conv_rhs => rw [← hx]`.

Rewrite using `[hPr, hB, hB]`. Conclude with `this`. Establish `hcf : ∀ x y : Fin N → ℂ, star x = y → (star y ⬝ᵥ H *ᵥ y).re = (star x ⬝ᵥ H *ᵥ x).re`. Introduce `x y hxy`. Rewrite using `[← hxy, hdiff, hdiff, hc1, hc2]`.

Establish `e2 : star (Pi.single j 1 + Complex.I • Pi.single k 1 : Fin N → ℂ) = Pi.single j 1 + (-Complex.I) • Pi.single k 1`. Apply the tactic sequence `funext i; simp [Pi.single_apply]; split_ifs <;> simp`. Establish `e1` using `hcf _ _ e2`. Rewrite `e1` using `[hpair, hpair]`. Simplify using `only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.normSq_neg] at e1`.

Conclude with `Complex.ext h1 (by simp only [Matrix.zero_apply, Complex.zero_im]; linarith)`. Establish `hsq' : _root_.GlobalTheory.ChowHt.frameNorm (P.map σ * A' σ) z ^ 2 = _root_.GlobalTheory.ChowHt.frameNorm (A σ) z ^ 2`. Use `hdiff z` as an intermediate fact. Rewrite `this` using `[hHz, Matrix.zero_mulVec, dotProduct_zero, Complex.zero_re]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `n1 : 0 ≤ _root_.GlobalTheory.ChowHt.frameNorm (P.map σ * A' σ) z` using `by unfold _root_.GlobalTheory.ChowHt.frameNorm; positivity`. Establish `n2 : 0 ≤ _root_.GlobalTheory.ChowHt.frameNorm (A σ) z` using `by unfold _root_.GlobalTheory.ChowHt.frameNorm; positivity`. Conclude with `(sq_eq_sq₀ n1 n2).1 hsq'`.
-/
private theorem frameNorm_toMatrix_map_mul_eq_of_isFrame {Nm : (K →+* ℂ) → V → ℝ} {L : Submodule (𝓞 K) V}
    {n n' : ℕ} {b b' : Basis (Fin N) K V} {w : Matrix (Fin N) (Fin n) K}
    {w' : Matrix (Fin N) (Fin n') K} {A A' : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ}
    (h : _root_.GlobalTheory.CompHt.IsFrame Nm L b w A) (h' : _root_.GlobalTheory.CompHt.IsFrame Nm L b' w' A')
    (σ : K →+* ℂ) (z : Fin N → ℂ) :
    _root_.GlobalTheory.ChowHt.frameNorm ((b.toMatrix b').map σ * A' σ) z = _root_.GlobalTheory.ChowHt.frameNorm (A σ) z := by
  set P := b.toMatrix b' with hP
  have hflip : P * b'.toMatrix b = 1 := Basis.toMatrix_mul_toMatrix_flip b b'
  have hdetP : P.det ≠ 0 := by
    intro h0
    have h1 := congr_arg Matrix.det hflip
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  have hdetPσ : (P.map σ).det ≠ 0 := by
    rw [show (P.map σ).det = σ P.det from (RingHom.map_det σ _).symm]
    exact (map_ne_zero σ).2 hdetP

  have hA : ∀ y : Fin N → K, _root_.GlobalTheory.ChowHt.frameNorm (A' σ) (fun j => σ (y j)) =
      _root_.GlobalTheory.ChowHt.frameNorm (A σ) (fun j => σ ((P *ᵥ y) j)) := by
    intro y
    have h1 := h'.norm σ (b'.equivFun.symm y)
    have h2 := h.norm σ (b'.equivFun.symm y)
    have r1 : ⇑(b'.repr (b'.equivFun.symm y)) = y := by
      rw [← Basis.equivFun_apply]; exact b'.equivFun.apply_symm_apply y
    have r2 : ⇑(b.repr (b'.equivFun.symm y)) = P *ᵥ y := by
      have t := Basis.toMatrix_mulVec_repr b' b (b'.equivFun.symm y)
      rw [r1] at t
      rw [hP]; exact t.symm
    rw [r1] at h1
    rw [r2] at h2
    rw [h1, h2]
  have hB : ∀ u : Fin N → ℂ, _root_.GlobalTheory.ChowHt.frameNorm (P.map σ * A' σ) (P.map σ *ᵥ u) =
      _root_.GlobalTheory.ChowHt.frameNorm (A' σ) u := by
    intro u
    unfold _root_.GlobalTheory.ChowHt.frameNorm
    rw [Matrix.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdetPσ), Matrix.mul_one]
  have hmap : ∀ y : Fin N → K, (fun j => σ ((P *ᵥ y) j)) = P.map σ *ᵥ fun j => σ (y j) := by
    intro y; funext j; exact RingHom.map_mulVec σ P y j
  have hK : ∀ y : Fin N → K, _root_.GlobalTheory.ChowHt.frameNorm (P.map σ * A' σ) (fun j => σ (y j)) =
      _root_.GlobalTheory.ChowHt.frameNorm (A σ) (fun j => σ (y j)) := by
    intro y
    have hy : P *ᵥ (P⁻¹ *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdetP),
        Matrix.one_mulVec]
    rw [← hy, hmap, hB, hA, hy, ← hmap, hy]

  set G₁ := (P.map σ * A' σ)⁻¹
  set G₂ := (A σ)⁻¹
  set H := G₁ᴴ * G₁ - G₂ᴴ * G₂ with hH
  have hsq : ∀ (M : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ),
      _root_.GlobalTheory.ChowHt.frameNorm M x ^ 2 = (star x ⬝ᵥ ((M⁻¹)ᴴ * M⁻¹) *ᵥ x).re := by
    intro M x
    unfold _root_.GlobalTheory.ChowHt.frameNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, dotProduct]
    simp [Complex.re_sum, Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, mul_comm]
  have hdiff : ∀ x : Fin N → ℂ, (star x ⬝ᵥ H *ᵥ x).re =
      _root_.GlobalTheory.ChowHt.frameNorm (P.map σ * A' σ) x ^ 2 - _root_.GlobalTheory.ChowHt.frameNorm (A σ) x ^ 2 := by
    intro x
    rw [hsq, hsq, hH, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]
  have hpair : ∀ (j k : Fin N) (c : ℂ), (star (Pi.single j 1 + c • Pi.single k 1 : Fin N → ℂ) ⬝ᵥ
      H *ᵥ (Pi.single j 1 + c • Pi.single k 1)).re =
      (H j j).re + 2 * (c * H j k).re + Complex.normSq c * (H k k).re := by
    intro j k c
    have hherm : H k j = star (H j k) := by
      rw [hH]
      simp [Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm]
    have e : star (Pi.single j 1 + c • Pi.single k 1 : Fin N → ℂ) ⬝ᵥ H *ᵥ (Pi.single j 1 + c • Pi.single k 1) =
        H j j + star c * H k j + c * H j k + star c * c * H k k := by
      simp [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, Pi.star_single]
      ring
    rw [e, hherm]
    simp [Complex.mul_re, Complex.normSq_apply]
    ring
  have hzeroK : ∀ y : Fin N → K, (star (fun j => σ (y j)) ⬝ᵥ H *ᵥ fun j => σ (y j)).re = 0 := by
    intro y
    rw [hdiff, hK, sub_self]
  have hdiag : ∀ j, (H j j).re = 0 := by
    intro j
    have := hzeroK (Pi.single j 1)
    have e : (fun i => σ ((Pi.single j 1 : Fin N → K) i)) = (Pi.single j 1 + (0 : ℂ) • Pi.single j 1 : Fin N → ℂ) := by
      funext i; by_cases hi : i = j <;> simp [hi, Pi.single_apply]
    rw [e, hpair] at this
    simpa using this
  have hre : ∀ (j k : Fin N) (a : K), (σ a * H j k).re = 0 := by
    intro j k a
    have := hzeroK (Pi.single j 1 + a • Pi.single k 1)
    have e : (fun i => σ ((Pi.single j 1 + a • Pi.single k 1 : Fin N → K) i)) =
        (Pi.single j 1 + σ a • Pi.single k 1 : Fin N → ℂ) := by
      funext i; simp [Pi.single_apply]; split_ifs <;> simp
    rw [e, hpair, hdiag, hdiag] at this
    linarith
  have hHz : H = 0 := by
    ext j k
    have h1 : (H j k).re = 0 := by simpa using hre j k 1
    by_cases hreal : ∃ a : K, (σ a).im ≠ 0
    · obtain ⟨a, ha⟩ := hreal
      have h2 := hre j k a
      rw [Complex.mul_re, h1, mul_zero, zero_sub, neg_eq_zero] at h2
      exact Complex.ext h1 ((mul_eq_zero.1 h2).resolve_left ha)
    · push_neg at hreal
      have hσ : (starRingEnd ℂ).comp σ = σ := by
        ext a; simp [Complex.ext_iff, hreal a]
      have hPr : ∀ u : Fin N → ℂ, star (P.map σ *ᵥ u) = P.map σ *ᵥ star u := by
        intro u; funext i
        simp only [Matrix.mulVec, dotProduct, Pi.star_apply, star_sum, star_mul', Matrix.map_apply]
        refine Finset.sum_congr rfl fun l _ => ?_
        have hs : star (σ (P i l)) = σ (P i l) := congr_fun (congr_arg DFunLike.coe hσ) (P i l)
        rw [hs]
      have hc2 : ∀ x, _root_.GlobalTheory.ChowHt.frameNorm (A σ) (star x) = _root_.GlobalTheory.ChowHt.frameNorm (A σ) x := by
        intro x
        have := h.conj σ x
        rw [hσ] at this
        exact this
      have hc1 : ∀ x, _root_.GlobalTheory.ChowHt.frameNorm (P.map σ * A' σ) (star x) =
          _root_.GlobalTheory.ChowHt.frameNorm (P.map σ * A' σ) x := by
        intro x
        have hx : P.map σ *ᵥ ((P.map σ)⁻¹ *ᵥ x) = x := by
          rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdetPσ),
            Matrix.one_mulVec]
        have := h'.conj σ ((P.map σ)⁻¹ *ᵥ x)
        rw [hσ] at this
        conv_lhs => rw [← hx]
        conv_rhs => rw [← hx]
        rw [hPr, hB, hB]
        exact this
      have hcf : ∀ x y : Fin N → ℂ, star x = y →
          (star y ⬝ᵥ H *ᵥ y).re = (star x ⬝ᵥ H *ᵥ x).re := by
        intro x y hxy; rw [← hxy, hdiff, hdiff, hc1, hc2]
      have e2 : star (Pi.single j 1 + Complex.I • Pi.single k 1 : Fin N → ℂ) =
          Pi.single j 1 + (-Complex.I) • Pi.single k 1 := by
        funext i; simp [Pi.single_apply]; split_ifs <;> simp
      have e1 := hcf _ _ e2
      rw [hpair, hpair] at e1
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
        Complex.normSq_neg] at e1
      exact Complex.ext h1 (by simp only [Matrix.zero_apply, Complex.zero_im]; linarith)
  have hsq' : _root_.GlobalTheory.ChowHt.frameNorm (P.map σ * A' σ) z ^ 2 = _root_.GlobalTheory.ChowHt.frameNorm (A σ) z ^ 2 := by
    have := hdiff z
    rw [hHz, Matrix.zero_mulVec, dotProduct_zero, Complex.zero_re] at this
    linarith
  have n1 : 0 ≤ _root_.GlobalTheory.ChowHt.frameNorm (P.map σ * A' σ) z := by unfold _root_.GlobalTheory.ChowHt.frameNorm; positivity
  have n2 : 0 ≤ _root_.GlobalTheory.ChowHt.frameNorm (A σ) z := by unfold _root_.GlobalTheory.ChowHt.frameNorm; positivity
  exact (sq_eq_sq₀ n1 n2).1 hsq'

set_option autoImplicit false in
open MvPolynomial NumberField Module in
open scoped Matrix in
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] {N : ℕ} in

/- English proof (translation)
Take `⟨U, hU⟩` from `exists_integral_matrix_toMatrix_mul_eq_of_isFrame h h'`. Take `⟨U', hU'⟩` from `exists_integral_matrix_toMatrix_mul_eq_of_isFrame h' h`. Use `set P := b.toMatrix b' with hP`. Establish `hflip : P * b'.toMatrix b = 1` using `Basis.toMatrix_mul_toMatrix_flip b b'`. Establish `hw : P * w' * U'.map ((↑) : 𝓞 K → K) = w`.

Rewrite using `[Matrix.mul_assoc, ← hU', ← Matrix.mul_assoc, hflip, Matrix.one_mul]`. Establish `hdetP : P.det ≠ 0`. Introduce `h0`. Establish `h1` using `congr_arg Matrix.det hflip`. Rewrite `h1` using `[Matrix.det_mul, h0, zero_mul, Matrix.det_one]`.

Conclude with `zero_ne_one h1`. Establish `hfin : ∀ v : FinitePlace K, _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v (_root_.GlobalTheory.ChowHt.linSubst w' (_root_.GlobalTheory.ChowHt.linSubst P f)) = _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v (_root_.GlobalTheory.ChowHt.linSubst w f)`. Introduce `v`. Establish `e1 : _root_.GlobalTheory.ChowHt.linSubst w' (_root_.GlobalTheory.ChowHt.linSubst P f) = _root_.GlobalTheory.ChowHt.linSubst (U.map ((↑) : 𝓞 K → K)) (_root_.GlobalTheory.ChowHt.linSubst w f)`. Rewrite using `[_root_.GlobalTheory.HeightUnique.linSubst_linSubst, _root_.GlobalTheory.HeightUnique.linSubst_linSubst, hU]`.

Establish `e2 : _root_.GlobalTheory.ChowHt.linSubst w f = _root_.GlobalTheory.ChowHt.linSubst (U'.map ((↑) : 𝓞 K → K)) (_root_.GlobalTheory.ChowHt.linSubst w' (_root_.GlobalTheory.ChowHt.linSubst P f))`. Rewrite using `[_root_.GlobalTheory.HeightUnique.linSubst_linSubst, _root_.GlobalTheory.HeightUnique.linSubst_linSubst, ← Matrix.mul_assoc, hw]`. Use `le_antisymm ?_ ?_` and prove the remaining obligations. Rewrite using `[e1]`. Conclude with `gaussAbs_linSubst_integral_matrix_le v U _`.

Rewrite using `[e2]`. Conclude with `gaussAbs_linSubst_integral_matrix_le v U' _`. Establish `harch : ∀ σ : K →+* ℂ, _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B N (_root_.GlobalTheory.ChowHt.linSubst (A' σ) (MvPolynomial.map σ (_root_.GlobalTheory.ChowHt.linSubst P f))) = _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B N (_root_.Globa …`. Introduce `σ`. Rewrite using `[_root_.GlobalTheory.ImageHeightUnique.map_linSubst, _root_.GlobalTheory.HeightUnique.linSubst_linSubst]`.

Use `_root_.GlobalTheory.SphereMeanFrame.blockSphereMean_eq_of_frameNorm_eq B N _ _ ?_ (h.herm σ) (frameNorm_toMatrix_map_mul_eq_of_isFrame h h' σ) _` and prove the remaining obligations. Rewrite using `[Matrix.det_mul, show ((b.toMatrix b').map σ).det = σ (b.toMatrix b').det from (RingHom.map_det σ _).symm]`. Conclude with `mul_ne_zero ((map_ne_zero σ).2 hdetP) (h'.herm σ)`. Unfold `_root_.GlobalTheory.ChowHt.formHeight`. Simplify using `only [hfin, harch]`.
-/
theorem _root_.GlobalTheory.ImageHeightUnique.formHeight_linSubst {Nm : (K →+* ℂ) → V → ℝ} {L : Submodule (𝓞 K) V} {n n' B : ℕ} {b b' : Basis (Fin N) K V}
    {w : Matrix (Fin N) (Fin n) K} {w' : Matrix (Fin N) (Fin n') K} {A A' : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ}
    (h : _root_.GlobalTheory.CompHt.IsFrame Nm L b w A) (h' : _root_.GlobalTheory.CompHt.IsFrame Nm L b' w' A') (δ : ℕ) (f : MvPolynomial (Fin B × Fin N) K) :
    _root_.GlobalTheory.ChowHt.formHeight δ w' A' (_root_.GlobalTheory.ChowHt.linSubst (b.toMatrix b') f) = _root_.GlobalTheory.ChowHt.formHeight δ w A f := by
  obtain ⟨U, hU⟩ := exists_integral_matrix_toMatrix_mul_eq_of_isFrame h h'
  obtain ⟨U', hU'⟩ := exists_integral_matrix_toMatrix_mul_eq_of_isFrame h' h
  set P := b.toMatrix b' with hP
  have hflip : P * b'.toMatrix b = 1 := Basis.toMatrix_mul_toMatrix_flip b b'
  have hw : P * w' * U'.map ((↑) : 𝓞 K → K) = w := by
    rw [Matrix.mul_assoc, ← hU', ← Matrix.mul_assoc, hflip, Matrix.one_mul]
  have hdetP : P.det ≠ 0 := by
    intro h0
    have h1 := congr_arg Matrix.det hflip
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  have hfin : ∀ v : FinitePlace K, _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v (_root_.GlobalTheory.ChowHt.linSubst w' (_root_.GlobalTheory.ChowHt.linSubst P f)) =
      _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v (_root_.GlobalTheory.ChowHt.linSubst w f) := by
    intro v
    have e1 : _root_.GlobalTheory.ChowHt.linSubst w' (_root_.GlobalTheory.ChowHt.linSubst P f) =
        _root_.GlobalTheory.ChowHt.linSubst (U.map ((↑) : 𝓞 K → K)) (_root_.GlobalTheory.ChowHt.linSubst w f) := by
      rw [_root_.GlobalTheory.HeightUnique.linSubst_linSubst, _root_.GlobalTheory.HeightUnique.linSubst_linSubst, hU]
    have e2 : _root_.GlobalTheory.ChowHt.linSubst w f = _root_.GlobalTheory.ChowHt.linSubst (U'.map ((↑) : 𝓞 K → K))
        (_root_.GlobalTheory.ChowHt.linSubst w' (_root_.GlobalTheory.ChowHt.linSubst P f)) := by
      rw [_root_.GlobalTheory.HeightUnique.linSubst_linSubst, _root_.GlobalTheory.HeightUnique.linSubst_linSubst, ← Matrix.mul_assoc, hw]
    refine le_antisymm ?_ ?_
    · rw [e1]; exact gaussAbs_linSubst_integral_matrix_le v U _
    · rw [e2]; exact gaussAbs_linSubst_integral_matrix_le v U' _
  have harch : ∀ σ : K →+* ℂ, _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B N (_root_.GlobalTheory.ChowHt.linSubst (A' σ)
      (MvPolynomial.map σ (_root_.GlobalTheory.ChowHt.linSubst P f))) =
      _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B N (_root_.GlobalTheory.ChowHt.linSubst (A σ) (MvPolynomial.map σ f)) := by
    intro σ
    rw [_root_.GlobalTheory.ImageHeightUnique.map_linSubst, _root_.GlobalTheory.HeightUnique.linSubst_linSubst]
    refine _root_.GlobalTheory.SphereMeanFrame.blockSphereMean_eq_of_frameNorm_eq B N _ _ ?_
      (h.herm σ) (frameNorm_toMatrix_map_mul_eq_of_isFrame h h' σ) _
    rw [Matrix.det_mul, show ((b.toMatrix b').map σ).det = σ (b.toMatrix b').det from
      (RingHom.map_det σ _).symm]
    exact mul_ne_zero ((map_ne_zero σ).2 hdetP) (h'.herm σ)
  unfold _root_.GlobalTheory.ChowHt.formHeight
  simp only [hfin, harch]

set_option autoImplicit false in
open MvPolynomial NumberField Module in
open scoped Matrix in
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] {N : ℕ} in

/- English proof (translation)
Take `⟨N₁, n₁, b₁, w₁, A₁, δ₁, f₁, hF₁, hC₁, hx₁⟩` from `hx`. Take `⟨N₂, n₂, b₂, w₂, A₂, δ₂, f₂, hF₂, hC₂, hy₂⟩` from `hy`. Choose the witnesses or unpack the hypotheses as in `rfl : N₁ = N₂ := by`. Establish `e₁` using `Module.finrank_eq_card_basis b₁`. Establish `e₂` using `Module.finrank_eq_card_basis b₂`.

Simplify using `using e₁.symm.trans e₂`. Establish `hT` using `_root_.GlobalTheory.CompHt.isChowFormInt_basis ev b₁ b₂ hC₁`. Take `⟨rfl, c, hc, hf⟩` from `hT.unique hC₂`. Establish `hδ : (0 : ℝ) < ((D : ℝ) + 1) * δ₁`. Use `hC₁.pos` as an intermediate fact.

Check the signs of the components of the expression. Establish `hN : 0 < N₁`. Take `⟨z, hz, -⟩` from `hC₁.exists_point`. Break down `Nat.eq_zero_or_pos N₁ with h0 | h0` into its components or cases. Substitute `h0` using the available equality.

Conclude with `absurd (Subsingleton.elim z 0) hz`. Conclude with `h0`. Establish `hhom` using `hT.1`. Establish `hH : _root_.GlobalTheory.ChowHt.formHeight δ₁ w₂ A₂ f₂ = _root_.GlobalTheory.ChowHt.formHeight δ₁ w₁ A₁ f₁`. Rewrite using `[hf, _root_.GlobalTheory.HeightUnique.formHeight_C_mul hN δ₁ hF₂.full hF₂.herm hT.ne_zero hhom hc]`.

Conclude with `_root_.GlobalTheory.ImageHeightUnique.formHeight_linSubst hF₁ hF₂ δ₁ f₁`. Establish `: ((D : ℝ) + 1) * δ₁ * x = ((D : ℝ) + 1) * δ₁ * y` using `by rw [hx₁, hy₂, hH]`. Conclude with `mul_left_cancel₀ hδ.ne' this`.
-/
theorem _root_.GlobalTheory.ImageHeightUnique.isImageHeight_unique {Ω : Type} [Field Ω] [Algebra K Ω] {Nm : (K →+* ℂ) → V → ℝ} {L : Submodule (𝓞 K) V}
    {ev : V →ₗ[K] Ω} {D : ℕ} {x y : ℝ} (hx : _root_.GlobalTheory.CompHt.IsImageHeight Nm L ev D x) (hy : _root_.GlobalTheory.CompHt.IsImageHeight Nm L ev D y) : x = y := by
  obtain ⟨N₁, n₁, b₁, w₁, A₁, δ₁, f₁, hF₁, hC₁, hx₁⟩ := hx
  obtain ⟨N₂, n₂, b₂, w₂, A₂, δ₂, f₂, hF₂, hC₂, hy₂⟩ := hy
  obtain rfl : N₁ = N₂ := by
    have e₁ := Module.finrank_eq_card_basis b₁
    have e₂ := Module.finrank_eq_card_basis b₂
    simpa using e₁.symm.trans e₂
  have hT := _root_.GlobalTheory.CompHt.isChowFormInt_basis ev b₁ b₂ hC₁
  obtain ⟨rfl, c, hc, hf⟩ := hT.unique hC₂
  have hδ : (0 : ℝ) < ((D : ℝ) + 1) * δ₁ := by
    have := hC₁.pos
    positivity
  have hN : 0 < N₁ := by
    obtain ⟨z, hz, -⟩ := hC₁.exists_point
    rcases Nat.eq_zero_or_pos N₁ with h0 | h0
    · subst h0; exact absurd (Subsingleton.elim z 0) hz
    · exact h0
  have hhom := hT.1
  have hH : _root_.GlobalTheory.ChowHt.formHeight δ₁ w₂ A₂ f₂ = _root_.GlobalTheory.ChowHt.formHeight δ₁ w₁ A₁ f₁ := by
    rw [hf, _root_.GlobalTheory.HeightUnique.formHeight_C_mul hN δ₁ hF₂.full hF₂.herm hT.ne_zero hhom hc]
    exact _root_.GlobalTheory.ImageHeightUnique.formHeight_linSubst hF₁ hF₂ δ₁ f₁
  have : ((D : ℝ) + 1) * δ₁ * x = ((D : ℝ) + 1) * δ₁ * y := by rw [hx₁, hy₂, hH]
  exact mul_left_cancel₀ hδ.ne' this

set_option autoImplicit false in
open MvPolynomial NumberField Module in
open scoped Matrix in

/- English proof (translation)
Introduce `K V Ω _ _ _ _ _ _ _ _ Nm L ev D h hh`. Conclude with `_root_.GlobalTheory.ImageHeightUnique.isImageHeight_unique (_root_.GlobalTheory.CompHt.isImageHeight_imageHeight ⟨h, hh⟩) hh`.
-/
theorem _root_.GlobalTheory.ImageHeightUnique.imageHeight_eq : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V)
    (ev : V →ₗ[K] Ω) (D : ℕ) (h : ℝ), _root_.GlobalTheory.CompHt.IsImageHeight Nm L ev D h → _root_.GlobalTheory.CompHt.imageHeight Nm L ev D = h := by
  intro K V Ω _ _ _ _ _ _ _ _ Nm L ev D h hh
  exact _root_.GlobalTheory.ImageHeightUnique.isImageHeight_unique (_root_.GlobalTheory.CompHt.isImageHeight_imageHeight ⟨h, hh⟩) hh

end GlobalTheory.ImageHeightUnique
