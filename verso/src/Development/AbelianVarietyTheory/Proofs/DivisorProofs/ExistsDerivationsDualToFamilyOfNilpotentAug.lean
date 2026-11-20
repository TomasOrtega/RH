import Mathlib
open scoped TensorProduct

/- English proof (translation)
Introduce `k A _ _ _ ε hnil d x D hD`. Set `M : Matrix (Fin d) (Fin d) A` to `Matrix.of fun i j => D i (x j)`. Establish `hε : (ε : A →+* k).mapMatrix M = 1`. Use extensionality with `i j`. Simplify using `[M, hD, Matrix.one_apply]`.

Establish `hdet : ε M.det = 1`. Establish `h` using `RingHom.map_det (ε : A →+* k) M`. Rewrite `h` using `[hε, Matrix.det_one]`. Simplify using `using h`. Establish `hunit : IsUnit M.det`.

Take `⟨n, hn⟩` from `hnil`. Establish `hmem : M.det - 1 ∈ RingHom.ker ε` using `by simp [RingHom.mem_ker, hdet]`. Establish `hN : IsNilpotent (M.det - 1)` using `⟨n, by`. Establish `h : (M.det - 1) ^ n ∈ (RingHom.ker ε) ^ n` using `Ideal.pow_mem_pow hmem n`. Rewrite `h` using `[hn]`.

Simplify using `using h⟩`. Establish `h` using `hN.isUnit_one_add`. Simplify using `using h`. Use `⟨fun i => ∑ l, (M⁻¹ i l) • D l, fun i j => ?_⟩` and prove the remaining obligations. Establish `hinv : M⁻¹ * M = 1` using `Matrix.nonsing_inv_mul M hunit`.

Establish `h` using `congrFun (congrFun hinv i) j`. Rewrite `h` using `[Matrix.mul_apply, Matrix.one_apply]`. Rewrite using `[← h]`. Establish `hev` using `map_sum (AddMonoidHom.mk' (fun δ : Derivation k A A => δ (x j)) (fun a b => rfl)) (fun l => M⁻¹ i l • D l) Finset.univ`. Simplify using `only [AddMonoidHom.mk'_apply] at hev`.

Rewrite using `[hev]`. Simplify using `[M]`.
-/
theorem GlobalTheory.derivation_normalise_family : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k), IsNilpotent (RingHom.ker ε) → ∀ (d : ℕ) (x : Fin d → A) (D : Fin d → Derivation k A A), (∀ i j, ε (D i (x j)) = if i = j then 1 else 0) → ∃ E : Fin d → Derivation k A A, ∀ i j, E i (x j) = if i = j then 1 else 0 := by
  intro k A _ _ _ ε hnil d x D hD
  let M : Matrix (Fin d) (Fin d) A := Matrix.of fun i j => D i (x j)
  have hε : (ε : A →+* k).mapMatrix M = 1 := by
    ext i j
    simp [M, hD, Matrix.one_apply]
  have hdet : ε M.det = 1 := by
    have h := RingHom.map_det (ε : A →+* k) M
    rw [hε, Matrix.det_one] at h
    simpa using h
  have hunit : IsUnit M.det := by
    obtain ⟨n, hn⟩ := hnil
    have hmem : M.det - 1 ∈ RingHom.ker ε := by simp [RingHom.mem_ker, hdet]
    have hN : IsNilpotent (M.det - 1) := ⟨n, by
      have h : (M.det - 1) ^ n ∈ (RingHom.ker ε) ^ n := Ideal.pow_mem_pow hmem n
      rw [hn] at h
      simpa using h⟩
    have h := hN.isUnit_one_add
    simpa using h
  refine ⟨fun i => ∑ l, (M⁻¹ i l) • D l, fun i j => ?_⟩
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hunit
  have h := congrFun (congrFun hinv i) j
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  rw [← h]
  have hev := map_sum (AddMonoidHom.mk' (fun δ : Derivation k A A => δ (x j)) (fun a b => rfl))
    (fun l => M⁻¹ i l • D l) Finset.univ
  simp only [AddMonoidHom.mk'_apply] at hev
  rw [hev]
  simp [M]
