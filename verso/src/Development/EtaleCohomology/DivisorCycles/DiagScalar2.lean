import Development.EtaleCohomology.DivisorCycles.CycleCount

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.DiagScalar₂
open LateralTheory.DivDb

variable {C : Type} [Field C] {N n : ℕ}

/- English proof (translation)
Rewrite using `[Finset.sum_mul, Finset.sum_eq_single j]`. Rewrite using `[smul_mul_assoc, (hp.1.idem j).eq]`. Introduce `b _ hb`. Rewrite using `[smul_mul_assoc, hp.1.ortho hb, smul_zero]`. Simplify using the standard rewrite rules.
-/
theorem mul_p (p : Fin n → Mat C N) (hp : Sys p) (e : Fin n → C) (j : Fin n) :
    (∑ i, e i • p i) * p j = e j • p j := by
  rw [Finset.sum_mul, Finset.sum_eq_single j]
  · rw [smul_mul_assoc, (hp.1.idem j).eq]
  · intro b _ hb; rw [smul_mul_assoc, hp.1.ortho hb, smul_zero]
  · simp

/- English proof (translation)
Rewrite using `[Finset.mul_sum, Finset.sum_eq_single j]`. Rewrite using `[mul_smul_comm, (hp.1.idem j).eq]`. Introduce `b _ hb`. Rewrite using `[mul_smul_comm, hp.1.ortho (Ne.symm hb), smul_zero]`. Simplify using the standard rewrite rules.
-/
theorem p_mul (p : Fin n → Mat C N) (hp : Sys p) (e : Fin n → C) (j : Fin n) :
    p j * (∑ i, e i • p i) = e j • p j := by
  rw [Finset.mul_sum, Finset.sum_eq_single j]
  · rw [mul_smul_comm, (hp.1.idem j).eq]
  · intro b _ hb; rw [mul_smul_comm, hp.1.ortho (Ne.symm hb), smul_zero]
  · simp

/- English proof (translation)
Establish `h1 : (∑ k, p k) *ᵥ v = v` using `by rw [hp.1.complete]; simp`. Rewrite `h1` using `[Matrix.sum_mulVec, Finset.sum_eq_single i]`. Conclude with `h1`. Introduce `b _ hb`. Conclude with `hv b hb`.

Simplify using the standard rewrite rules.
-/
theorem vec_of (p : Fin n → Mat C N) (hp : Sys p) (i : Fin n) (v : Fin N → C)
    (hv : ∀ k, k ≠ i → p k *ᵥ v = 0) : p i *ᵥ v = v := by
  have h1 : (∑ k, p k) *ᵥ v = v := by rw [hp.1.complete]; simp
  rw [Matrix.sum_mulVec, Finset.sum_eq_single i] at h1
  · exact h1
  · intro b _ hb; exact hv b hb
  · simp

/- English proof (translation)
Establish `h` using `vec_of p hp i v hv`. Use `conv_lhs => rw [← h]`. Rewrite using `[Matrix.mulVec_mulVec, mul_p p hp e i, Matrix.smul_mulVec, h]`.
-/
theorem X_vec (p : Fin n → Mat C N) (hp : Sys p) (e : Fin n → C) (i : Fin n) (v : Fin N → C)
    (hv : ∀ k, k ≠ i → p k *ᵥ v = 0) : (∑ k, e k • p k) *ᵥ v = e i • v := by
  have h := vec_of p hp i v hv
  conv_lhs => rw [← h]
  rw [Matrix.mulVec_mulVec, mul_p p hp e i, Matrix.smul_mulVec, h]

/- English proof (translation)
Rewrite using `[Polynomial.IsRoot, Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]`. Use `⟨v, hv, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.sub_mulVec, h, Matrix.scalar_apply]`. Use extensionality with `k`. Simplify using `[Matrix.mulVec_diagonal]`.
-/
theorem root_of_eig (Y : Mat C N) (μ : C) (v : Fin N → C) (hv : v ≠ 0) (h : Y *ᵥ v = μ • v) :
    Y.charpoly.IsRoot μ := by
  rw [Polynomial.IsRoot, Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, h, Matrix.scalar_apply]
  ext k; simp [Matrix.mulVec_diagonal]

/- English proof (translation)
Take `⟨q, hq, hd, ha⟩` from `h`. Use `⟨Polynomial.taylor (-c) q, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ne, Polynomial.taylor_eq_zero]` and apply the resulting hypothesis. Rewrite using `[Polynomial.natDegree_taylor]` and apply the resulting hypothesis. Rewrite using `[Polynomial.taylor_apply, Polynomial.aeval_comp]`.

Simplify using `[ha]`.
-/
theorem deg_shift (x : Mat C N) (c : C) (h : Deg n x) : Deg n (x + algebraMap C (Mat C N) c) := by
  obtain ⟨q, hq, hd, ha⟩ := h
  refine ⟨Polynomial.taylor (-c) q, ?_, ?_, ?_⟩
  · rwa [Ne, Polynomial.taylor_eq_zero]
  · rwa [Polynomial.natDegree_taylor]
  · rw [Polynomial.taylor_apply, Polynomial.aeval_comp]
    simp [ha]

/- English proof (translation)
Rewrite using `[Matrix.algebraMap_eq_diagonal]`. Use extensionality with `k`. Simplify using `[Matrix.mulVec_diagonal]`.
-/
theorem alg_vec (c : C) (v : Fin N → C) : (algebraMap C (Mat C N) c) *ᵥ v = c • v := by
  rw [Matrix.algebraMap_eq_diagonal]; ext k; simp [Matrix.mulVec_diagonal]

end LateralTheory.DivDb.DiagScalar₂

namespace LateralTheory.DivDb
open DiagScalar₂ in
/- English proof (translation)
Introduce `C _ _ _ N n p e Y hp he hY hD i`. Establish `: Infinite C` using `Infinite.of_injective _ Nat.cast_injective`. Use `set X := ∑ i, e i • p i with hX`. Use `set R := Y.charpoly.roots.toFinset with hR`. Use `set B : Finset C := insert 0 ((R ×ˢ R ×ˢ (Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n))).image (fun t => (e t.2.2.2 - e t.2.2.1) / (t.1 - t.2.1))) with hB`.

Take `⟨s, hs⟩` from `Infinite.exists_notMem_finset B`. Establish `hs0 : s ≠ 0` using `fun h => hs (h ▸ Finset.mem_insert_self _ _)`. Use `set M := s • Y + X with hM`. Take `⟨c', hc'⟩` from `Infinite.exists_notMem_finset ((-M).charpoly.roots.toFinset)`. Use `set y := M + algebraMap C (Mat C N) c' with hy`.

Establish `hunit : IsUnit y`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]`. Introduce `h0`. Apply `hc'` to reduce the goal to its premises. Rewrite using `[Multiset.mem_toFinset, Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero, Polynomial.IsRoot, Matrix.eval_charpoly]`.

Use `h0 using 2` and compare the differences between its conclusion and the goal. Rewrite using `[hy, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply, sub_neg_eq_add, add_comm]`. Both sides reduce to the same expression. Establish `hcomm : ∀ j, y * p j = p ((1 : Equiv.Perm (Fin n)) j) * y`. Introduce `j`.

Rewrite using `[Equiv.Perm.one_apply, hy, hM, add_mul, add_mul, mul_add, mul_add, smul_mul_assoc, mul_smul_comm, hY j, hX, mul_p p hp e j, p_mul p hp e j, Algebra.commutes]`. Establish `hdeg : Deg n y` using `deg_shift _ c' (hD s)`. Establish `key : ∀ (i : Fin n) (l : C) (v : Fin N → C), v ≠ 0 → y *ᵥ v = l • v → (∀ k, ¬ i = k → p k *ᵥ v = 0) → ∃ μ ∈ R, s * μ + e i = l - c'`. Introduce `i l v hv hyv hpv`. Establish `hXv` using `X_vec p hp e i v (fun k hk => hpv k (Ne.symm hk))`.

Establish `h1 : y *ᵥ v = s • (Y *ᵥ v) + e i • v + c' • v`. Rewrite using `[hy, hM, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, hX, hXv, alg_vec]`. Rewrite `hyv` using `[h1]`. Establish `h2 : s • (Y *ᵥ v) = (l - c' - e i) • v` using `by rw [sub_smul, sub_smul, ← hyv]; abel`. Use `⟨s⁻¹ * (l - c' - e i), ?_, by field_simp; ring⟩` and prove the remaining obligations.

Rewrite using `[hR, Multiset.mem_toFinset, Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero]`. Apply `root_of_eig Y _ v hv` to reduce the goal to its premises. Rewrite using `[mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hs0, one_smul]`. Establish `hdisj : Disj y 1 p`. Introduce `i j hij l v w hv hw hyv hyw hpv hpw`.

Simplify using `only [Equiv.Perm.sameCycle_one] at hij hpv hpw`. Take `⟨μ, hμ, h1⟩` from `key i l v hv hyv hpv`. Take `⟨μ', hμ', h2⟩` from `key j l w hw hyw hpw`. Establish `hne : e i ≠ e j` using `he.ne hij`. Establish `hμμ : μ - μ' ≠ 0`.

Introduce `h`. Apply `hne` to reduce the goal to its premises. Establish `: μ = μ'` using `sub_eq_zero.mp h`. Substitute `this` using the available equality. Take the linear combination `h1 - h2`.

Apply `hs` to reduce the goal to its premises. Apply `Finset.mem_insert_of_mem` to reduce the goal to its premises. Rewrite using `[Finset.mem_image]`. Use `⟨(μ, μ', i, j), by simp [hμ, hμ'], ?_⟩` and prove the remaining obligations. Use `show (e j - e i) / (μ - μ') = s`.

Rewrite using `[div_eq_iff hμμ]`. Take the linear combination `h2 - h1`. Take `⟨_, hfix⟩` from `hC C N n p y 1 hp hunit hcomm hdeg hdisj`. Take `⟨c, hc⟩` from `hfix i rfl`. Use `⟨s⁻¹ * (c - e i - c'), ?_⟩` and prove the remaining obligations.

Establish `h4 : y * p i = s • (Y * p i) + e i • p i + c' • p i`. Rewrite using `[hy, hM, add_mul, add_mul, smul_mul_assoc, hX, mul_p p hp e i, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]`. Rewrite `hc` using `[h4]`. Establish `h3 : s • (Y * p i) = (c - e i - c') • p i` using `by rw [sub_smul, sub_smul, ← hc]; abel`. Rewrite using `[mul_smul, ← h3, smul_smul, inv_mul_cancel₀ hs0, one_smul]`.
-/
theorem DiagScalar_of (hC : CycleCount) : DiagScalar := by
  intro C _ _ _ N n p e Y hp he hY hD i
  classical
  have : Infinite C := Infinite.of_injective _ Nat.cast_injective
  set X := ∑ i, e i • p i with hX
  set R := Y.charpoly.roots.toFinset with hR
  set B : Finset C := insert 0 ((R ×ˢ R ×ˢ (Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n))).image
    (fun t => (e t.2.2.2 - e t.2.2.1) / (t.1 - t.2.1))) with hB
  obtain ⟨s, hs⟩ := Infinite.exists_notMem_finset B
  have hs0 : s ≠ 0 := fun h => hs (h ▸ Finset.mem_insert_self _ _)
  set M := s • Y + X with hM
  obtain ⟨c', hc'⟩ := Infinite.exists_notMem_finset ((-M).charpoly.roots.toFinset)
  set y := M + algebraMap C (Mat C N) c' with hy
  have hunit : IsUnit y := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro h0; apply hc'
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero, Polynomial.IsRoot,
      Matrix.eval_charpoly]
    convert h0 using 2
    rw [hy, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply, sub_neg_eq_add, add_comm]; rfl
  have hcomm : ∀ j, y * p j = p ((1 : Equiv.Perm (Fin n)) j) * y := by
    intro j
    rw [Equiv.Perm.one_apply, hy, hM, add_mul, add_mul, mul_add, mul_add, smul_mul_assoc, mul_smul_comm, hY j,
      hX, mul_p p hp e j, p_mul p hp e j, Algebra.commutes]
  have hdeg : Deg n y := deg_shift _ c' (hD s)
  have key : ∀ (i : Fin n) (l : C) (v : Fin N → C), v ≠ 0 → y *ᵥ v = l • v →
      (∀ k, ¬ i = k → p k *ᵥ v = 0) → ∃ μ ∈ R, s * μ + e i = l - c' := by
    intro i l v hv hyv hpv
    have hXv := X_vec p hp e i v (fun k hk => hpv k (Ne.symm hk))
    have h1 : y *ᵥ v = s • (Y *ᵥ v) + e i • v + c' • v := by
      rw [hy, hM, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, hX, hXv, alg_vec]
    rw [h1] at hyv
    have h2 : s • (Y *ᵥ v) = (l - c' - e i) • v := by rw [sub_smul, sub_smul, ← hyv]; abel
    refine ⟨s⁻¹ * (l - c' - e i), ?_, by field_simp; ring⟩
    rw [hR, Multiset.mem_toFinset, Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero]
    apply root_of_eig Y _ v hv
    rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  have hdisj : Disj y 1 p := by
    intro i j hij l v w hv hw hyv hyw hpv hpw
    simp only [Equiv.Perm.sameCycle_one] at hij hpv hpw
    obtain ⟨μ, hμ, h1⟩ := key i l v hv hyv hpv
    obtain ⟨μ', hμ', h2⟩ := key j l w hw hyw hpw
    have hne : e i ≠ e j := he.ne hij
    have hμμ : μ - μ' ≠ 0 := by
      intro h; apply hne
      have : μ = μ' := sub_eq_zero.mp h
      subst this; linear_combination h1 - h2
    apply hs
    apply Finset.mem_insert_of_mem
    rw [Finset.mem_image]
    refine ⟨(μ, μ', i, j), by simp [hμ, hμ'], ?_⟩
    show (e j - e i) / (μ - μ') = s
    rw [div_eq_iff hμμ]; linear_combination h2 - h1
  obtain ⟨_, hfix⟩ := hC C N n p y 1 hp hunit hcomm hdeg hdisj
  obtain ⟨c, hc⟩ := hfix i rfl
  refine ⟨s⁻¹ * (c - e i - c'), ?_⟩
  have h4 : y * p i = s • (Y * p i) + e i • p i + c' • p i := by
    rw [hy, hM, add_mul, add_mul, smul_mul_assoc, hX, mul_p p hp e i, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      one_mul]
  rw [h4] at hc
  have h3 : s • (Y * p i) = (c - e i - c') • p i := by rw [sub_smul, sub_smul, ← hc]; abel
  rw [mul_smul, ← h3, smul_smul, inv_mul_cancel₀ hs0, one_smul]

end LateralTheory.DivDb
