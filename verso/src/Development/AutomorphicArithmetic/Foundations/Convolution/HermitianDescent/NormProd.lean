import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NormAlmostAll
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalBase

open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

section SlopeTestRemainingChoices

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R]

/- English proof (translation)
Apply `h.fix` to reduce the goal to its premises. Rewrite using `[map_sum]`. Establish `h1` using `Finset.sum_range_succ (fun j => (σ ^ j) y) q`. Establish `h2` using `Finset.sum_range_succ' (fun j => (σ ^ j) y) q`. Rewrite `h1` using `[h2, h.pow, pow_zero]`.

Establish `h3` using `add_right_cancel h1`. Rewrite using `[← h3]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[pow_succ', AlgEquiv.mul_apply]`.
-/
private lemma tr_mem {σ : R ≃ₐ[k] R} {q : ℕ} (h : IsGal σ q) (y : R) :
    ∃ t : k, algebraMap k R t = ∑ j ∈ Finset.range q, (σ ^ j) y := by
  apply h.fix
  rw [map_sum]
  have h1 := Finset.sum_range_succ (fun j => (σ ^ j) y) q
  have h2 := Finset.sum_range_succ' (fun j => (σ ^ j) y) q
  rw [h2, h.pow, pow_zero] at h1
  have h3 := add_right_cancel h1
  rw [← h3]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_succ', AlgEquiv.mul_apply]

/- English proof (translation)
Repeatedly rewrite using `[Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Establish `: ∀ j ∈ Finset.range q, ∑ i, (σ ^ j) (y i * r) * x i = if j = 0 then r else 0`. Introduce `j hj`. Use `hs j (Finset.mem_range.1 hj)` as an intermediate fact.

Establish `h2 : ∑ i, (σ ^ j) (y i * r) * x i = (∑ i, x i * (σ ^ j) (y i)) * (σ ^ j) r`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h2, this]`. Use `split_ifs with h0`. Simplify using `[h0]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_congr rfl this, Finset.sum_ite_eq' ]`.

Simplify using `[hq]`.
-/
private lemma expand {σ : R ≃ₐ[k] R} {q s : ℕ} (hq : 0 < q) {x y : Fin s → R}
    (hs : ∀ j < q, ∑ i, x i * (σ ^ j) (y i) = if j = 0 then 1 else 0) (r : R) :
    ∑ i, (∑ j ∈ Finset.range q, (σ ^ j) (y i * r)) * x i = r := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ j ∈ Finset.range q, ∑ i, (σ ^ j) (y i * r) * x i = if j = 0 then r else 0 := by
    intro j hj
    have := hs j (Finset.mem_range.1 hj)
    have h2 : ∑ i, (σ ^ j) (y i * r) * x i = (∑ i, x i * (σ ^ j) (y i)) * (σ ^ j) r := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul]; ring
    rw [h2, this]
    split_ifs with h0
    · simp [h0]
    · simp
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' ]
  simp [hq]

private def phi (σ : R ≃ₐ[k] R) (q : ℕ) : R ⊗[k] R →ₐ[R] (Fin q → R) :=
  Algebra.TensorProduct.lift (Algebra.ofId R (Fin q → R))
    (Pi.algHom k _ fun j : Fin q => ((σ ^ (j : ℕ) : R ≃ₐ[k] R) : R →ₐ[k] R)) fun _ _ => Commute.all _ _

/- English proof (translation)
Simplify using `[phi, Algebra.ofId_apply]`.
-/
private lemma phi_tmul (σ : R ≃ₐ[k] R) (q : ℕ) (a b : R) (j : Fin q) :
    phi σ q (a ⊗ₜ b) j = a * (σ ^ (j : ℕ)) b := by
  simp [phi, Algebra.ofId_apply]

/- English proof (translation)
Take `⟨s, x, y, hs⟩` from `h.sep`. Establish `key : ∀ z : R ⊗[k] R, ∑ i, (∑ j : Fin q, (σ ^ (j : ℕ)) (y i) * phi σ q z j) ⊗ₜ[k] x i = z`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add u v hu hv`. Simplify using `only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib, TensorProduct.add_tmul, hu, hv]`. Consider the case `tmul a b => choose t ht using fun i => tr_mem h (y i * b)`. Establish `hb` using `expand h.pos hs b`. Use `conv_rhs => rw [← hb, TensorProduct.tmul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← ht, ← Algebra.smul_def, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, ht, Finset.sum_range, Finset.sum_mul]`. Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[phi_tmul, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `u v huv`. Rewrite using `[← key u, ← key v, huv]`.
-/
private lemma phi_inj {σ : R ≃ₐ[k] R} {q : ℕ} (h : IsGal σ q) : Function.Injective (phi σ q) := by
  obtain ⟨s, x, y, hs⟩ := h.sep
  have key : ∀ z : R ⊗[k] R, ∑ i, (∑ j : Fin q, (σ ^ (j : ℕ)) (y i) * phi σ q z j) ⊗ₜ[k] x i = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv =>
      simp only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib, TensorProduct.add_tmul, hu, hv]
    | tmul a b =>
      choose t ht using fun i => tr_mem h (y i * b)
      have hb := expand h.pos hs b
      conv_rhs => rw [← hb, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← ht, ← Algebra.smul_def, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, ht,
        Finset.sum_range, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [phi_tmul, map_mul]; ring
  intro u v huv
  rw [← key u, ← key v, huv]

/- English proof (translation)
Take `⟨s, x, y, hs⟩` from `h.sep`. Establish `key : ∀ m j : Fin q, phi σ q (∑ i, x i ⊗ₜ[k] (σ ^ (q - m)) (y i)) j = if j = m then 1 else 0`. Introduce `m j`. Rewrite using `[map_sum, Finset.sum_apply]`. Repeatedly rewrite using `[phi_tmul, ← AlgEquiv.mul_apply, ← pow_add]`.

Rewrite using `[pow_eq_pow_mod _ h.pow, hs _ (Nat.mod_lt _ h.pos)]`. Establish `hm` using `m.2`. Establish `hj` using `j.2`. Use `if_congr ?_ rfl rfl` and prove the remaining obligations. Rewrite using `[Fin.ext_iff]`.

Break down `lt_or_ge (j : ℕ) m with hl | hl` into its components or cases. Rewrite using `[Nat.mod_eq_of_lt (by omega)]; omega`. Rewrite using `[Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega`. Introduce `f`. Use `⟨∑ m : Fin q, f m • ∑ i, x i ⊗ₜ[k] (σ ^ (q - m)) (y i), ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `j`. Rewrite using `[map_sum, Finset.sum_apply]`. Repeatedly rewrite using `[map_smul, Pi.smul_apply, key]`. Simplify using the standard rewrite rules.
-/
private lemma phi_surj {σ : R ≃ₐ[k] R} {q : ℕ} (h : IsGal σ q) : Function.Surjective (phi σ q) := by
  obtain ⟨s, x, y, hs⟩ := h.sep
  have key : ∀ m j : Fin q, phi σ q (∑ i, x i ⊗ₜ[k] (σ ^ (q - m)) (y i)) j = if j = m then 1 else 0 := by
    intro m j
    rw [map_sum, Finset.sum_apply]
    simp_rw [phi_tmul, ← AlgEquiv.mul_apply, ← pow_add]
    rw [pow_eq_pow_mod _ h.pow, hs _ (Nat.mod_lt _ h.pos)]
    have hm := m.2
    have hj := j.2
    refine if_congr ?_ rfl rfl
    rw [Fin.ext_iff]
    rcases lt_or_ge (j : ℕ) m with hl | hl
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  intro f
  refine ⟨∑ m : Fin q, f m • ∑ i, x i ⊗ₜ[k] (σ ^ (q - m)) (y i), ?_⟩
  funext j
  rw [map_sum, Finset.sum_apply]
  simp_rw [map_smul, Pi.smul_apply, key]
  simp

/- English proof (translation)
Take `⟨s, x, y, hs⟩` from `h.sep`. Use `Module.Finite.of_surjective (Fintype.linearCombination k x) fun b => ?_` and prove the remaining obligations. Use `choose t ht using fun i => tr_mem h (y i * b)`. Use `⟨t, ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.linearCombination_apply]`.

Repeatedly rewrite using `[Algebra.smul_def, ht]`. Conclude with `expand h.pos hs b`.
-/
private lemma fin {σ : R ≃ₐ[k] R} {q : ℕ} (h : IsGal σ q) : Module.Finite k R := by
  obtain ⟨s, x, y, hs⟩ := h.sep
  refine Module.Finite.of_surjective (Fintype.linearCombination k x) fun b => ?_
  choose t ht using fun i => tr_mem h (y i * b)
  refine ⟨t, ?_⟩
  rw [Fintype.linearCombination_apply]
  simp_rw [Algebra.smul_def, ht]
  exact expand h.pos hs b

/- English proof (translation)
Rewrite using `[Algebra.norm_eq_matrix_det (Pi.basisFun R (Fin q)), ← Matrix.det_diagonal]`. Use `congr 1`. Use extensionality with `i j`. Rewrite using `[Algebra.leftMulMatrix_eq_repr_mul]`. Distinguish the cases in `hij : i = j`.

Simplify using `[hij]`. Simplify using `[hij]`.
-/
private lemma norm_pi {q : ℕ} (f : Fin q → R) : Algebra.norm R f = ∏ j, f j := by
  rw [Algebra.norm_eq_matrix_det (Pi.basisFun R (Fin q)), ← Matrix.det_diagonal]
  congr 1
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.D

/- English proof (translation)
Introduce `k R _ _ _ _ σ q h r`. Use `haveI := UpperTheory.ConvolutionTheory.D.fin h`. Establish `h1 : algebraMap k R (Algebra.norm k r) = Algebra.norm R ((1 : R) ⊗ₜ[k] r)`. Rewrite using `[Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]`. Use `congr 1`.

Use extensionality with `b`. Simplify using the standard rewrite rules. Set `e` to `AlgEquiv.ofBijective (UpperTheory.ConvolutionTheory.D.phi σ q) ⟨UpperTheory.ConvolutionTheory.D.phi_inj h, UpperTheory.ConvolutionTheory.D.phi_surj h⟩`. Rewrite using `[h1, ← Algebra.norm_eq_of_algEquiv e, UpperTheory.ConvolutionTheory.D.norm_pi, Finset.prod_range]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations.

Conclude with `(UpperTheory.ConvolutionTheory.D.phi_tmul σ q 1 r j).trans (one_mul _)`.
-/
theorem UpperTheory.ConvolutionTheory.D.normProd :
    UpperTheory.ConvolutionTheory.D.NormProd := by
  intro k R _ _ _ _ σ q h r
  haveI := UpperTheory.ConvolutionTheory.D.fin h
  have h1 : algebraMap k R (Algebra.norm k r) = Algebra.norm R ((1 : R) ⊗ₜ[k] r) := by
    rw [Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]
    congr 1
    ext b
    simp
  let e := AlgEquiv.ofBijective (UpperTheory.ConvolutionTheory.D.phi σ q) ⟨UpperTheory.ConvolutionTheory.D.phi_inj h, UpperTheory.ConvolutionTheory.D.phi_surj h⟩
  rw [h1, ← Algebra.norm_eq_of_algEquiv e, UpperTheory.ConvolutionTheory.D.norm_pi, Finset.prod_range]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact (UpperTheory.ConvolutionTheory.D.phi_tmul σ q 1 r j).trans (one_mul _)
