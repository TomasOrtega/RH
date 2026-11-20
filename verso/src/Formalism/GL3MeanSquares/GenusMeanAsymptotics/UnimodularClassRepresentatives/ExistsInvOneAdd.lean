import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsLocUnif

open Matrix

namespace Formalism.HermitianLattices.Ext.L3.HU

variable {K : Type*} [Field K] [StarRing K] {S : Subring K} {ϖ : K}
variable {n : Type*} [Fintype n] [DecidableEq n]

/- English proof (translation)
Take `⟨M₀, rfl⟩` from `hM.exists_map`. Set `ϖ₀ : S` to `⟨ϖ, hS.mem⟩`. Use `⟨((Matrix.trace M₀ + (Matrix.det (1 + (Polynomial.X : Polynomial S) • M₀.map Polynomial.C)).divX.divX.eval ϖ₀ * ϖ₀ : S) : K), SetLike.coe_mem _, ?_⟩` and prove the remaining obligations. Establish `hmap : (1 : Matrix n n K) + ϖ • M₀.map S.subtype = S.subtype.mapMatrix (1 + ϖ₀ • M₀)`. Use extensionality with `i j`.

Apply the tactic sequence `by_cases h : i = j <;> simp [h, ϖ₀]`. Rewrite using `[hmap, ← RingHom.map_det, Matrix.det_one_add_smul ϖ₀ M₀]`. Simplify using `only [map_add, map_mul, map_one, map_pow, Subring.coe_subtype]`. Simplify using `only [Subring.coe_add, Subring.coe_mul, ϖ₀]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Cayley.exists_det_one_add (hS : IsLocUnif S ϖ) {M : Matrix n n K} (hM : Ent S M) :
    ∃ s ∈ S, (1 + ϖ • M).det = 1 + ϖ * s := by
  obtain ⟨M₀, rfl⟩ := hM.exists_map
  let ϖ₀ : S := ⟨ϖ, hS.mem⟩
  refine ⟨((Matrix.trace M₀ + (Matrix.det (1 + (Polynomial.X : Polynomial S) •
      M₀.map Polynomial.C)).divX.divX.eval ϖ₀ * ϖ₀ : S) : K), SetLike.coe_mem _, ?_⟩
  have hmap : (1 : Matrix n n K) + ϖ • M₀.map S.subtype = S.subtype.mapMatrix (1 + ϖ₀ • M₀) := by
    ext i j
    by_cases h : i = j <;> simp [h, ϖ₀]
  rw [hmap, ← RingHom.map_det, Matrix.det_one_add_smul ϖ₀ M₀]
  simp only [map_add, map_mul, map_one, map_pow, Subring.coe_subtype]
  simp only [Subring.coe_add, Subring.coe_mul, ϖ₀]
  ring

/- English proof (translation)
Take `⟨s, hs, hdet⟩` from `Cayley.exists_det_one_add hS hM`. Take `⟨hne, hinv⟩` from `hS.rad s hs`. Establish `hA : Ent S (1 + ϖ • M)` using `Ent.add Ent.one (Ent.smul hS.mem hM)`. Use `⟨(1 + ϖ * s)⁻¹ • (1 + ϖ • M).adjugate, Ent.smul hinv hA.adjugate, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_smul, Matrix.mul_adjugate, hdet, smul_smul, inv_mul_cancel₀ hne, one_smul]`.
-/
theorem Cayley.exists_inv_one_add (hS : IsLocUnif S ϖ) {M : Matrix n n K} (hM : Ent S M) :
    ∃ Q : Matrix n n K, Ent S Q ∧ (1 + ϖ • M) * Q = 1 := by
  obtain ⟨s, hs, hdet⟩ := Cayley.exists_det_one_add hS hM
  obtain ⟨hne, hinv⟩ := hS.rad s hs
  have hA : Ent S (1 + ϖ • M) := Ent.add Ent.one (Ent.smul hS.mem hM)
  refine ⟨(1 + ϖ * s)⁻¹ • (1 + ϖ • M).adjugate, Ent.smul hinv hA.adjugate, ?_⟩
  rw [Matrix.mul_smul, Matrix.mul_adjugate, hdet, smul_smul, inv_mul_cancel₀ hne, one_smul]

/- English proof (translation)
Use `set j := N - 2 * l - e with hj`. Establish `hj1 : 1 ≤ j` using `by omega`. Establish `hNj : N = j + e + 2 * l` using `by omega`. Establish `hϖ0 : ϖ ≠ 0` using `hS.ne`. Establish `hstar : ∀ k : ℕ, star (ϖ ^ k) = ϖ ^ k` using `fun k => by rw [star_pow, hS.fix]`.

Establish `hcs : star c ∈ S` using `hS.star_mem c hc`. Take `⟨A, hA⟩ : ∃ A : Matrix n n K, A = c • (1 : Matrix n n K) + star c • X` from `⟨_, rfl⟩`. Rewrite `hWW` using `[← hA]`. Establish `hAent : Ent S A`. Rewrite using `[hA]`.

Conclude with `Ent.add (Ent.smul hc Ent.one) (Ent.smul hcs hX)`. Establish `hWA : W' * A = ϖ ^ l • (1 : Matrix n n K)`. Establish `hne : ϖ ^ l ≠ 0` using `pow_ne_zero _ hϖ0`. Establish `h1 : A * ((ϖ ^ l)⁻¹ • W') = 1`. Rewrite using `[Matrix.mul_smul, hWW, smul_smul, inv_mul_cancel₀ hne, one_smul]`.

Establish `h2 : ((ϖ ^ l)⁻¹ • W') * A = 1` using `mul_eq_one_comm.mp h1`. Rewrite `h2` using `[Matrix.smul_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_smul, mul_inv_cancel₀ hne, one_smul]`. Use `_ = ϖ ^ l • (1 : Matrix n n K) := by rw [h2]`.

Establish `hAW : ∀ M : Matrix n n K, Aᴴ * (W'ᴴ * M) = ϖ ^ l • M`. Introduce `M`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hWA, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hstar, Matrix.smul_mul, Matrix.one_mul]`. Establish `hHE' : ∀ M : Matrix n n K, H * (E * M) = ϖ ^ e • M`. Introduce `M`.

Rewrite using `[← Matrix.mul_assoc, hHE, Matrix.smul_mul, Matrix.one_mul]`. Establish `hZh : Zᴴ = Z`. Establish `h1 : (Xᴴ * H * X)ᴴ = Xᴴ * H * X`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH, Matrix.mul_assoc]`. Rewrite `h1` using `[hXZ, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hH, hstar]`.

Conclude with `smul_right_injective _ (pow_ne_zero N hϖ0) (add_left_cancel h1)`. Take `⟨D₁, hD₁⟩ : ∃ D₁ : Matrix n n K, D₁ = E * (W'ᴴ * (Z * W'))` from `⟨_, rfl⟩`. Establish `hD₁ent : Ent S D₁`. Rewrite using `[hD₁]`. Conclude with `Ent.mul hES (Ent.mul (Ent.conjTranspose hS.star_mem hW') (Ent.mul hZ hW'))`.

Take `⟨Δ, hΔ⟩ : ∃ Δ : Matrix n n K, Δ = (c * ϖ ^ j) • (D₁ * A)` from `⟨_, rfl⟩`. Establish `key1 : Aᴴ * (H * Δ) = (c * ϖ ^ N) • Z`. Rewrite using `[hΔ, hD₁]`. Simplify using `only [Matrix.mul_smul, Matrix.mul_assoc]`. Rewrite using `[hHE']`.

Simplify using `only [Matrix.mul_smul]`. Rewrite using `[hAW, hWA]`. Simplify using `only [Matrix.mul_smul, Matrix.mul_one, smul_smul]`. Use `congr 1`. Rewrite using `[hNj]`.

Expand and normalize the polynomial expressions, which then agree. Establish `key2 : Δᴴ * (H * A) = (star c * ϖ ^ N) • Z`. Establish `h : Δᴴ * (H * A) = (Aᴴ * (H * Δ))ᴴ`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH, Matrix.mul_assoc]`. Rewrite using `[h, key1, Matrix.conjTranspose_smul, hZh, star_mul', hstar]`.

Establish `hAh : Aᴴ = star c • (1 : Matrix n n K) + c • Xᴴ`. Rewrite using `[hA, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_star]`. Establish `k1 : star c • (H * Δ) + c • (Xᴴ * (H * Δ)) = (c * ϖ ^ N) • Z`. Rewrite using `[← key1, hAh, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]`. Establish `k2 : c • (Δᴴ * H) + star c • (Δᴴ * (H * X)) = (star c * ϖ ^ N) • Z`.

Rewrite using `[← key2, hA, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]`. Establish `k0 : Xᴴ * (H * X) = H + ϖ ^ N • Z` using `by rw [← Matrix.mul_assoc, hXZ]`. Establish `hTR : (X - c • Δ)ᴴ * H * (X - c • Δ) = (1 + star c • Δ)ᴴ * H * (1 + star c • Δ)`. Simplify using `only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_star, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]`. Rewrite using `[k0]`.

Take the linear combination `(norm := module) -k1 - k2 - hcc • (ϖ ^ N • Z)`. Establish `hMent : Ent S ((star c * c * ϖ ^ (j - 1)) • (D₁ * A))` using `Ent.smul (mul_mem (mul_mem hcs hc) (_root_.pow_mem hS.mem _)) (Ent.mul hD₁ent hAent)`. Take `⟨Q, hQent, hRQ⟩` from `Cayley.exists_inv_one_add hS hMent`. Establish `hjj : ϖ * ϖ ^ (j - 1) = ϖ ^ j`. Rewrite using `[← pow_succ']`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `hR : (1 : Matrix n n K) + ϖ • ((star c * c * ϖ ^ (j - 1)) • (D₁ * A)) = 1 + star c • Δ`. Rewrite using `[hΔ, smul_smul, smul_smul]`. Use `congr 2`.

Rewrite using `[← hjj]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hRQ` using `[hR]`. Establish `hRQ' : Q + star c • (Δ * Q) = 1`. Establish `h` using `hRQ`.

Rewrite `h` using `[Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]`. Conclude with `h`. Use `⟨(X - c • Δ) * Q, -(star c * c) • (X * (D₁ * (A * Q))) - (c * c) • (D₁ * (A * Q)), ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Ent.sub (Ent.smul (neg_mem (mul_mem hcs hc)) (Ent.mul hX (Ent.mul hD₁ent (Ent.mul hAent hQent)))) (Ent.smul (mul_mem hc hc) (Ent.mul hD₁ent (Ent.mul hAent hQent)))`. Rewrite using `[Matrix.conjTranspose_mul]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = H := by rw [hRQ]; simp`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]`.

Normalize the expressions using the abelian group laws. Use `_ = X + ϖ ^ j • (-(star c * c) • (X * (D₁ * (A * Q))) - (c * c) • (D₁ * (A * Q))) := by`. Rewrite using `[hRQ', Matrix.mul_one, hΔ]`. Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]`. Use `module`.
-/
theorem exists_cayley (hS : IsLocUnif S ϖ) {H E : Matrix n n K} (hH : Hᴴ = H) (hHS : Ent S H)
    (hES : Ent S E) {e l N : ℕ} (hHE : H * E = ϖ ^ e • (1 : Matrix n n K)) (hN : 2 * l + e + 1 ≤ N)
    {X Z W' : Matrix n n K} (hX : Ent S X) (hZ : Ent S Z) (hXZ : Xᴴ * H * X = H + ϖ ^ N • Z)
    {c : K} (hc : c ∈ S) (hcc : c + star c = 1) (hW' : Ent S W')
    (hWW : (c • (1 : Matrix n n K) + star c • X) * W' = ϖ ^ l • (1 : Matrix n n K)) :
    ∃ G D : Matrix n n K, Ent S D ∧ Gᴴ * H * G = H ∧ G = X + ϖ ^ (N - 2 * l - e) • D := by
  classical
  set j := N - 2 * l - e with hj
  have hj1 : 1 ≤ j := by omega
  have hNj : N = j + e + 2 * l := by omega
  have hϖ0 : ϖ ≠ 0 := hS.ne
  have hstar : ∀ k : ℕ, star (ϖ ^ k) = ϖ ^ k := fun k => by rw [star_pow, hS.fix]
  have hcs : star c ∈ S := hS.star_mem c hc
  obtain ⟨A, hA⟩ : ∃ A : Matrix n n K, A = c • (1 : Matrix n n K) + star c • X := ⟨_, rfl⟩
  rw [← hA] at hWW
  have hAent : Ent S A := by
    rw [hA]
    exact Ent.add (Ent.smul hc Ent.one) (Ent.smul hcs hX)
  have hWA : W' * A = ϖ ^ l • (1 : Matrix n n K) := by
    have hne : ϖ ^ l ≠ 0 := pow_ne_zero _ hϖ0
    have h1 : A * ((ϖ ^ l)⁻¹ • W') = 1 := by
      rw [Matrix.mul_smul, hWW, smul_smul, inv_mul_cancel₀ hne, one_smul]
    have h2 : ((ϖ ^ l)⁻¹ • W') * A = 1 := mul_eq_one_comm.mp h1
    rw [Matrix.smul_mul] at h2
    calc W' * A = ϖ ^ l • ((ϖ ^ l)⁻¹ • (W' * A)) := by
          rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
      _ = ϖ ^ l • (1 : Matrix n n K) := by rw [h2]
  have hAW : ∀ M : Matrix n n K, Aᴴ * (W'ᴴ * M) = ϖ ^ l • M := by
    intro M
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hWA, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, hstar, Matrix.smul_mul, Matrix.one_mul]
  have hHE' : ∀ M : Matrix n n K, H * (E * M) = ϖ ^ e • M := by
    intro M
    rw [← Matrix.mul_assoc, hHE, Matrix.smul_mul, Matrix.one_mul]
  have hZh : Zᴴ = Z := by
    have h1 : (Xᴴ * H * X)ᴴ = Xᴴ * H * X := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH,
        Matrix.mul_assoc]
    rw [hXZ, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hH, hstar] at h1
    exact smul_right_injective _ (pow_ne_zero N hϖ0) (add_left_cancel h1)
  obtain ⟨D₁, hD₁⟩ : ∃ D₁ : Matrix n n K, D₁ = E * (W'ᴴ * (Z * W')) := ⟨_, rfl⟩
  have hD₁ent : Ent S D₁ := by
    rw [hD₁]
    exact Ent.mul hES (Ent.mul (Ent.conjTranspose hS.star_mem hW') (Ent.mul hZ hW'))
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : Matrix n n K, Δ = (c * ϖ ^ j) • (D₁ * A) := ⟨_, rfl⟩
  have key1 : Aᴴ * (H * Δ) = (c * ϖ ^ N) • Z := by
    rw [hΔ, hD₁]
    simp only [Matrix.mul_smul, Matrix.mul_assoc]
    rw [hHE']
    simp only [Matrix.mul_smul]
    rw [hAW, hWA]
    simp only [Matrix.mul_smul, Matrix.mul_one, smul_smul]
    congr 1
    rw [hNj]
    ring
  have key2 : Δᴴ * (H * A) = (star c * ϖ ^ N) • Z := by
    have h : Δᴴ * (H * A) = (Aᴴ * (H * Δ))ᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH,
        Matrix.mul_assoc]
    rw [h, key1, Matrix.conjTranspose_smul, hZh, star_mul', hstar]
  have hAh : Aᴴ = star c • (1 : Matrix n n K) + c • Xᴴ := by
    rw [hA, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, star_star]
  have k1 : star c • (H * Δ) + c • (Xᴴ * (H * Δ)) = (c * ϖ ^ N) • Z := by
    rw [← key1, hAh, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]
  have k2 : c • (Δᴴ * H) + star c • (Δᴴ * (H * X)) = (star c * ϖ ^ N) • Z := by
    rw [← key2, hA, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.mul_smul, Matrix.mul_one]
  have k0 : Xᴴ * (H * X) = H + ϖ ^ N • Z := by rw [← Matrix.mul_assoc, hXZ]
  have hTR : (X - c • Δ)ᴴ * H * (X - c • Δ) = (1 + star c • Δ)ᴴ * H * (1 + star c • Δ) := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, star_star, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul,
      Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc]
    rw [k0]
    linear_combination (norm := module) -k1 - k2 - hcc • (ϖ ^ N • Z)
  have hMent : Ent S ((star c * c * ϖ ^ (j - 1)) • (D₁ * A)) :=
    Ent.smul (mul_mem (mul_mem hcs hc) (_root_.pow_mem hS.mem _)) (Ent.mul hD₁ent hAent)
  obtain ⟨Q, hQent, hRQ⟩ := Cayley.exists_inv_one_add hS hMent
  have hjj : ϖ * ϖ ^ (j - 1) = ϖ ^ j := by
    rw [← pow_succ']
    congr 1
    omega
  have hR : (1 : Matrix n n K) + ϖ • ((star c * c * ϖ ^ (j - 1)) • (D₁ * A)) =
      1 + star c • Δ := by
    rw [hΔ, smul_smul, smul_smul]
    congr 2
    rw [← hjj]
    ring
  rw [hR] at hRQ
  have hRQ' : Q + star c • (Δ * Q) = 1 := by
    have h := hRQ
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul] at h
    exact h
  refine ⟨(X - c • Δ) * Q, -(star c * c) • (X * (D₁ * (A * Q))) - (c * c) • (D₁ * (A * Q)), ?_, ?_, ?_⟩
  · exact Ent.sub (Ent.smul (neg_mem (mul_mem hcs hc)) (Ent.mul hX (Ent.mul hD₁ent (Ent.mul hAent hQent))))
      (Ent.smul (mul_mem hc hc) (Ent.mul hD₁ent (Ent.mul hAent hQent)))
  · rw [Matrix.conjTranspose_mul]
    calc Qᴴ * (X - c • Δ)ᴴ * H * ((X - c • Δ) * Q)
        = Qᴴ * ((X - c • Δ)ᴴ * H * (X - c • Δ)) * Q := by simp only [Matrix.mul_assoc]
      _ = Qᴴ * ((1 + star c • Δ)ᴴ * H * (1 + star c • Δ)) * Q := by rw [hTR]
      _ = ((1 + star c • Δ) * Q)ᴴ * H * ((1 + star c • Δ) * Q) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = H := by rw [hRQ]; simp
  · calc (X - c • Δ) * Q = X * (Q + star c • (Δ * Q)) - star c • (X * (Δ * Q)) - c • (Δ * Q) := by
          simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
          abel
      _ = X + ϖ ^ j • (-(star c * c) • (X * (D₁ * (A * Q))) - (c * c) • (D₁ * (A * Q))) := by
          rw [hRQ', Matrix.mul_one, hΔ]
          simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
          module

end Formalism.HermitianLattices.Ext.L3.HU
