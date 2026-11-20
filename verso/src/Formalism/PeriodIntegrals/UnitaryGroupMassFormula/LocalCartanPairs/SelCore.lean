import Mathlib

noncomputable section
open Matrix

namespace PI.SqPair.LCP

variable {R : Type} [CommRing R] [IsDomain R]

/- English proof (translation)
Establish `hex : ∃ n : ℕ, ∃ i j, h i j ≠ 0 ∧ ∃ u : R, IsUnit u ∧ h i j = ϖ ^ n * u`. Assume the negation of the conclusion as `hne`. Apply `hh` to reduce the goal to its premises. Use extensionality with `i j`. Rewrite using `[Matrix.zero_apply]`.

Assume the negation of the conclusion as `hij`. Take `⟨n, u, hu, he⟩` from `hval _ hij`. Conclude with `hne ⟨n, i, j, hij, u, hu, he⟩`. Take `⟨i₀, j₀, _, u₀, hu₀, he₀⟩` from `Nat.find_spec hex`. Establish `hdiv : ∀ i j, ∃ z : R, h i j = ϖ ^ Nat.find hex * z`.

Introduce `i j`. Distinguish the cases in `hij : h i j = 0`. Conclude with `⟨0, by rw [hij, mul_zero]⟩`. Take `⟨n, u, hu, he⟩` from `hval _ hij`. Establish `hmn : Nat.find hex ≤ n` using `Nat.find_min' hex ⟨i, j, hij, u, hu, he⟩`.

Use `⟨ϖ ^ (n - Nat.find hex) * u, ?_⟩` and prove the remaining obligations. Rewrite using `[he, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hmn]`. Use `choose h₁ hh₁ using hdiv`. Use `⟨Nat.find hex, Matrix.of h₁, i₀, j₀, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Simplify using `only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]`. Conclude with `hh₁ i j`. Establish `e : h₁ i₀ j₀ = u₀` using `mul_left_cancel₀ (pow_ne_zero _ hϖ0) ((hh₁ i₀ j₀).symm.trans he₀)`. Simplify using `only [Matrix.of_apply, e]`. Conclude with `hu₀`.
-/
theorem sel_factor (ϖ : R) (hϖ0 : ϖ ≠ 0)
    (hval : ∀ x : R, x ≠ 0 → ∃ n : ℕ, ∃ u : R, IsUnit u ∧ x = ϖ ^ n * u)
    {ι κ : Type} (h : Matrix ι κ R) (hh : h ≠ 0) :
    ∃ (m : ℕ) (h₁ : Matrix ι κ R) (i : ι) (j : κ), h = ϖ ^ m • h₁ ∧ IsUnit (h₁ i j) := by
  classical
  have hex : ∃ n : ℕ, ∃ i j, h i j ≠ 0 ∧ ∃ u : R, IsUnit u ∧ h i j = ϖ ^ n * u := by
    by_contra hne
    apply hh
    ext i j
    rw [Matrix.zero_apply]
    by_contra hij
    obtain ⟨n, u, hu, he⟩ := hval _ hij
    exact hne ⟨n, i, j, hij, u, hu, he⟩
  obtain ⟨i₀, j₀, _, u₀, hu₀, he₀⟩ := Nat.find_spec hex
  have hdiv : ∀ i j, ∃ z : R, h i j = ϖ ^ Nat.find hex * z := by
    intro i j
    by_cases hij : h i j = 0
    · exact ⟨0, by rw [hij, mul_zero]⟩
    · obtain ⟨n, u, hu, he⟩ := hval _ hij
      have hmn : Nat.find hex ≤ n := Nat.find_min' hex ⟨i, j, hij, u, hu, he⟩
      refine ⟨ϖ ^ (n - Nat.find hex) * u, ?_⟩
      rw [he, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hmn]
  choose h₁ hh₁ using hdiv
  refine ⟨Nat.find hex, Matrix.of h₁, i₀, j₀, ?_, ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    exact hh₁ i j
  · have e : h₁ i₀ j₀ = u₀ :=
      mul_left_cancel₀ (pow_ne_zero _ hϖ0) ((hh₁ i₀ j₀).symm.trans he₀)
    simp only [Matrix.of_apply, e]
    exact hu₀

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, hσϖ]`.
-/
theorem sel_star_smul (σ : R ≃+* R) (ϖ : R) (hσϖ : σ ϖ = ϖ) (m : ℕ) {ι κ : Type}
    (h : Matrix ι κ R) : ((ϖ ^ m • h).map σ)ᵀ = ϖ ^ m • (h.map σ)ᵀ := by
  ext i j
  simp [Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, hσϖ]

/- English proof (translation)
Use extensionality with `i j`. Establish `h'` using `congrFun (congrFun h i) j`. Simplify using `only [Matrix.smul_apply, smul_eq_mul] at h'`. Conclude with `mul_left_cancel₀ hc h'`.
-/
theorem sel_smul_cancel {ι κ : Type} {c : R} (hc : c ≠ 0) {X Y : Matrix ι κ R}
    (h : c • X = c • Y) : X = Y := by
  ext i j
  have h' := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h'
  exact mul_left_cancel₀ hc h'

/- English proof (translation)
Establish `hB : ϖ ^ (2 * m) • ((h₁.map σ)ᵀ * A * h₁) = ϖ ^ (2 * k) • A'`. Rewrite using `[← hrel, sel_star_smul σ ϖ hσϖ]`. Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add, two_mul]`. Establish `hp0 : ∀ t : ℕ, ϖ ^ t ≠ 0` using `fun t => pow_ne_zero _ hϖ0`. Distinguish the cases in `hmk : m ≤ k`.

Use `⟨hmk, sel_smul_cancel (hp0 (2 * m)) ?_⟩` and prove the remaining obligations. Rewrite using `[hB, smul_smul, ← pow_add]`. Use `congr 2`. Use linear arithmetic over natural numbers and integers. Use `exfalso push_neg at hmk`.

Establish `h2 : ϖ ^ (2 * k) • (ϖ ^ (2 * (m - k)) • ((h₁.map σ)ᵀ * A * h₁)) = ϖ ^ (2 * k) • A'`. Rewrite using `[smul_smul, ← pow_add, ← hB]`. Use `congr 2`. Use linear arithmetic over natural numbers and integers. Establish `h3` using `sel_smul_cancel (hp0 (2 * k)) h2`.

Establish `h4` using `congrArg Matrix.det h3`. Rewrite `h4` using `[Matrix.det_smul]`. Rewrite `hA'` using `[← h4]`. Establish `h5 : IsUnit ((ϖ ^ (2 * (m - k))) ^ Fintype.card ι)` using `isUnit_of_mul_isUnit_left hA'`. Rewrite `h5` using `[← pow_mul]`.

Establish `hpos : 2 * (m - k) * Fintype.card ι ≠ 0` using `Nat.pos_iff_ne_zero.mp (Nat.mul_pos (by omega) Fintype.card_pos)`. Conclude with `hϖ ((isUnit_pow_iff hpos).mp h5)`.
-/
theorem sel_le (σ : R ≃+* R) (ϖ : R) (hϖ0 : ϖ ≠ 0) (hϖ : ¬ IsUnit ϖ) (hσϖ : σ ϖ = ϖ)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A A' h₁ : Matrix ι ι R) (hA' : IsUnit A'.det) (m k : ℕ)
    (hrel : ((ϖ ^ m • h₁).map σ)ᵀ * A * (ϖ ^ m • h₁) = ϖ ^ (2 * k) • A') :
    m ≤ k ∧ (h₁.map σ)ᵀ * A * h₁ = ϖ ^ (2 * (k - m)) • A' := by
  have hB : ϖ ^ (2 * m) • ((h₁.map σ)ᵀ * A * h₁) = ϖ ^ (2 * k) • A' := by
    rw [← hrel, sel_star_smul σ ϖ hσϖ]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add, two_mul]
  have hp0 : ∀ t : ℕ, ϖ ^ t ≠ 0 := fun t => pow_ne_zero _ hϖ0
  by_cases hmk : m ≤ k
  · refine ⟨hmk, sel_smul_cancel (hp0 (2 * m)) ?_⟩
    rw [hB, smul_smul, ← pow_add]
    congr 2
    omega
  · exfalso
    push_neg at hmk
    have h2 : ϖ ^ (2 * k) • (ϖ ^ (2 * (m - k)) • ((h₁.map σ)ᵀ * A * h₁)) = ϖ ^ (2 * k) • A' := by
      rw [smul_smul, ← pow_add, ← hB]
      congr 2
      omega
    have h3 := sel_smul_cancel (hp0 (2 * k)) h2
    have h4 := congrArg Matrix.det h3
    rw [Matrix.det_smul] at h4
    rw [← h4] at hA'
    have h5 : IsUnit ((ϖ ^ (2 * (m - k))) ^ Fintype.card ι) := isUnit_of_mul_isUnit_left hA'
    rw [← pow_mul] at h5
    have hpos : 2 * (m - k) * Fintype.card ι ≠ 0 :=
      Nat.pos_iff_ne_zero.mp (Nat.mul_pos (by omega) Fintype.card_pos)
    exact hϖ ((isUnit_pow_iff hpos).mp h5)

/- English proof (translation)
Establish `e` using `congrArg Matrix.det hrel`. Rewrite `e` using `[Matrix.det_mul, Matrix.det_mul]`. Rewrite `hA'` using `[← e]`. Conclude with `isUnit_of_mul_isUnit_right hA'`.
-/
theorem sel_unit_of_rel (σ : R ≃+* R) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A A' h₁ : Matrix ι ι R) (hA' : IsUnit A'.det)
    (hrel : (h₁.map σ)ᵀ * A * h₁ = A') : IsUnit h₁.det := by
  have e := congrArg Matrix.det hrel
  rw [Matrix.det_mul, Matrix.det_mul] at e
  rw [← e] at hA'
  exact isUnit_of_mul_isUnit_right hA'

/- English proof (translation)
Establish `hdet : g.det * h.det = c ^ Fintype.card ι`. Rewrite using `[← Matrix.det_mul, hgh, Matrix.det_smul, Matrix.det_one, mul_one]`. Establish `hh0 : h.det ≠ 0`. Introduce `h0`. Rewrite `hdet` using `[h0, mul_zero]`.

Conclude with `pow_ne_zero _ hc hdet.symm`. Establish `key : (h * g - c • 1) * h = 0`. Rewrite using `[Matrix.sub_mul, Matrix.mul_assoc, hgh, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, sub_self]`. Establish `key2 : h.det • (h * g - c • 1) = 0`. Establish `e` using `congrArg (· * h.adjugate) key`.

Simplify using `only [Matrix.zero_mul] at e`. Rewrite `e` using `[Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]`. Conclude with `e`. Establish `e0 : h * g - c • 1 = 0`. Use extensionality with `i j`.

Establish `e` using `congrFun (congrFun key2 i) j`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at e ⊢`. Conclude with `(mul_eq_zero.mp e).resolve_left hh0`. Conclude with `sub_eq_zero.mp e0`.
-/
theorem sel_comm {ι : Type} [Fintype ι] [DecidableEq ι] {c : R} (hc : c ≠ 0)
    (g h : Matrix ι ι R) (hgh : g * h = c • 1) : h * g = c • 1 := by
  have hdet : g.det * h.det = c ^ Fintype.card ι := by
    rw [← Matrix.det_mul, hgh, Matrix.det_smul, Matrix.det_one, mul_one]
  have hh0 : h.det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdet
    exact pow_ne_zero _ hc hdet.symm
  have key : (h * g - c • 1) * h = 0 := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, hgh, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, sub_self]
  have key2 : h.det • (h * g - c • 1) = 0 := by
    have e := congrArg (· * h.adjugate) key
    simp only [Matrix.zero_mul] at e
    rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at e
    exact e
  have e0 : h * g - c • 1 = 0 := by
    ext i j
    have e := congrFun (congrFun key2 i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at e ⊢
    exact (mul_eq_zero.mp e).resolve_left hh0
  exact sub_eq_zero.mp e0

/- English proof (translation)
Establish `h1 : (A'⁻¹ * (h₁.map σ)ᵀ * A) * h₁ = c • 1`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ A h₁, hrel, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hA']`. Conclude with `⟨h1, sel_comm hc _ _ h1⟩`.
-/
theorem sel_inv (σ : R ≃+* R) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A A' h₁ : Matrix ι ι R) (hA' : IsUnit A'.det) {c : R} (hc : c ≠ 0)
    (hrel : (h₁.map σ)ᵀ * A * h₁ = c • A') :
    (A'⁻¹ * (h₁.map σ)ᵀ * A) * h₁ = c • 1 ∧ h₁ * (A'⁻¹ * (h₁.map σ)ᵀ * A) = c • 1 := by
  have h1 : (A'⁻¹ * (h₁.map σ)ᵀ * A) * h₁ = c • 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ A h₁, hrel, Matrix.mul_smul,
      Matrix.nonsing_inv_mul _ hA']
  exact ⟨h1, sel_comm hc _ _ h1⟩

/- English proof (translation)
Take `⟨u, hu⟩` from `hx.map σ`. Use `⟨A⁻¹ *ᵥ Pi.single i (↑u⁻¹ : R), ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA, Matrix.one_mulVec, dotProduct_single]`. Simplify using `[← hu]`.
-/
theorem sel_dual (σ : R ≃+* R) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (hA : IsUnit A.det) (x : ι → R) (i : ι) (hx : IsUnit (x i)) :
    ∃ y : ι → R, (fun l => σ (x l)) ⬝ᵥ (A *ᵥ y) = 1 := by
  obtain ⟨u, hu⟩ := hx.map σ
  refine ⟨A⁻¹ *ᵥ Pi.single i (↑u⁻¹ : R), ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA, Matrix.one_mulVec, dotProduct_single]
  simp [← hu]

/- English proof (translation)
Establish `e : (fun l => σ ((M *ᵥ v) l)) = (M.map σ) *ᵥ (fun l => σ (v l))`. Use function extensionality and compare the values at `l`. Conclude with `RingHom.map_mulVec (σ : R →+* R) M v l`. Rewrite using `[e, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`.
-/
theorem sel_form (σ : R ≃+* R) {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι R) (M : Matrix ι κ R) (v w : κ → R) :
    (fun l => σ ((M *ᵥ v) l)) ⬝ᵥ (A *ᵥ (M *ᵥ w)) =
      (fun l => σ (v l)) ⬝ᵥ (((M.map σ)ᵀ * A * M) *ᵥ w) := by
  have e : (fun l => σ ((M *ᵥ v) l)) = (M.map σ) *ᵥ (fun l => σ (v l)) := by
    funext l
    exact RingHom.map_mulVec (σ : R →+* R) M v l
  rw [e, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

end PI.SqPair.LCP
