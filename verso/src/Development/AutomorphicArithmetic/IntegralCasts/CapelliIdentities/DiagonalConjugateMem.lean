import Mathlib

/- English proof (translation)
Establish `hdet : (Matrix.of a).det = 1`. Rewrite using `[Matrix.det_of_upperTriangular (M := Matrix.of a) (fun i j hij => hlow i j hij)]`. Simplify using `[hd]`. Set `H : GL (Fin n) R` to `Matrix.GeneralLinearGroup.mk'' (Matrix.of a) (by rw [hdet]; exact isUnit_one)`. Use `⟨H, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[SetLike.mem_coe, MonoidHom.mem_ker]`. Use extensionality with `i j`. Break down `lt_trichotomy i j with hij | rfl | hij` into its components or cases. Establish `: Ideal.Quotient.mk I (a i j) = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr (hI i j hij)`. Simplify `this` using `[H, Matrix.one_apply, hij.ne]`.

Simplify using `[H, hd]`. Simplify using `[H, hlow i j hij, Matrix.one_apply, hij.ne']`. Use extensionality with `i j`. Simplify using `[H, ha]`.
-/
private lemma liftUnitri {R K : Type} [CommRing R] [CommRing K] (f : R →+* K) (I : Ideal R) {n : ℕ}
    (h : GL (Fin n) K) (a : Fin n → Fin n → R)
    (ha : ∀ i j, f (a i j) = (h : Matrix (Fin n) (Fin n) K) i j)
    (hlow : ∀ i j, j < i → a i j = 0) (hd : ∀ i, a i i = 1)
    (hI : ∀ i j, i < j → a i j ∈ I) :
    h ∈ Subgroup.map (Matrix.GeneralLinearGroup.map f)
      (Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk I)).ker := by
  have hdet : (Matrix.of a).det = 1 := by
    rw [Matrix.det_of_upperTriangular (M := Matrix.of a) (fun i j hij => hlow i j hij)]
    simp [hd]
  let H : GL (Fin n) R := Matrix.GeneralLinearGroup.mk'' (Matrix.of a) (by rw [hdet]; exact isUnit_one)
  refine ⟨H, ?_, ?_⟩
  · rw [SetLike.mem_coe, MonoidHom.mem_ker]
    ext i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · have : Ideal.Quotient.mk I (a i j) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hI i j hij)
      simpa [H, Matrix.one_apply, hij.ne] using this
    · simp [H, hd]
    · simp [H, hlow i j hij, Matrix.one_apply, hij.ne']
  · ext i j
    simp [H, ha]

/- English proof (translation)
Introduce `k _ _ _ _ n ϖ hϖ c z g hz hg hb hd`. Take `⟨g0, hg0⟩` from `hg`. Establish `hg0' : ∀ i j, algebraMap (↥(ValuativeRel.valuation k).integer) k ((g0 : Matrix (Fin n) (Fin n) _) i j) = (g : Matrix (Fin n) (Fin n) k) i j`. Introduce `i j`. Rewrite using `[← hg0]`.

Simplify using the standard rewrite rules. Set `p : ↥(ValuativeRel.valuation k).integer` to `⟨(ϖ : k), hϖ.le⟩`. Establish `hp : p ∈ IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation k).integer`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`.

Take `⟨q, hq⟩` from `hu.exists_right_inv`. Establish `h1 : ValuativeRel.valuation k ((p * q : ↥(ValuativeRel.valuation k).integer) : k) = 1`. Rewrite using `[hq]`. Simplify using the standard rewrite rules. Establish `h2 : ValuativeRel.valuation k ((q : ↥(ValuativeRel.valuation k).integer) : k) ≤ 1` using `q.2`.

Rewrite `h1` using `[Subring.coe_mul, map_mul]`. Establish `h3 : ValuativeRel.valuation k (ϖ : k) * ValuativeRel.valuation k ((q : ↥(ValuativeRel.valuation k).integer) : k) < 1` using `lt_of_le_of_lt (mul_le_of_le_one_right' h2) hϖ`. Conclude with `absurd h1 h3.ne`. Set `t : Fin n → kˣ` to `fun i => ϖ ^ ((n : ℤ) - 1 - ((i : ℕ) : ℤ))`. Establish `hz1 : ((z ^ c : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = Matrix.diagonal (fun i => (((t i) ^ c : kˣ) : k))`.

Rewrite using `[Units.val_pow_eq_pow_val, hz, Matrix.diagonal_pow]`. Use `congr 1`. Establish `hz2 : (((z ^ c)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = Matrix.diagonal (fun i => ((((t i) ^ c)⁻¹ : kˣ) : k))`. Apply `Units.inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Rewrite using `[hz1, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`.

Use `congr 1`. Use extensionality with `i`. Rewrite using `[← Units.val_mul]`. Simplify using the standard rewrite rules. Establish `hent : ∀ i j, ((z ^ c * g * (z ^ c)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j = (((t i) ^ c : kˣ) : k) * (g : Matrix (Fin n) (Fin n) k) i j * ((((t j) ^ c)⁻¹ : kˣ) : k)`.

Introduce `i j`. Rewrite using `[Units.val_mul, Units.val_mul, hz2, hz1, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Establish `hpow : ∀ i j : Fin n, i < j → (((t i) ^ c : kˣ) : k) * ((((t j) ^ c)⁻¹ : kˣ) : k) = (ϖ : k) ^ (((j : ℕ) - (i : ℕ)) * c)`. Introduce `i j hij`. Rewrite using `[← Units.val_mul, ← Units.val_pow_eq_pow_val]`.

Use `congr 1`. Establish `hle : (i : ℕ) ≤ (j : ℕ)` using `hij.le`. Simplify using `only [t]`. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_neg, ← zpow_add]`. Use `congr 1`.

Move the coercions through the operations in `[Nat.cast_sub hle]`. Expand and normalize the polynomial expressions, which then agree. Use `liftUnitri _ _ _ (fun i j => if i < j then p ^ (((j : ℕ) - (i : ℕ)) * c) * (g0 : Matrix (Fin n) (Fin n) _) i j else if i = j then 1 else 0) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `i j`. Rewrite using `[hent]`.

Break down `lt_trichotomy i j with hij | rfl | hij` into its components or cases. Rewrite using `[if_pos hij, map_mul, hg0', map_pow, mul_right_comm, hpow i j hij]`. Both sides reduce to the same expression. Rewrite using `[if_neg (lt_irrefl _), if_pos rfl, hd, map_one, mul_one, ← Units.val_mul]`. Simplify using the standard rewrite rules.

Rewrite using `[if_neg hij.not_gt, if_neg hij.ne', hb hij]`. Simplify using the standard rewrite rules. Introduce `i j hij`. Rewrite using `[if_neg hij.not_gt, if_neg hij.ne']`. Introduce `i`.

Simplify using the standard rewrite rules. Introduce `i j hij`. Rewrite using `[if_pos hij]`. Apply `Ideal.mul_mem_right` to reduce the goal to its premises. Establish `hpos : (j : ℕ) - (i : ℕ) ≠ 0`.

Establish `: (i : ℕ) < (j : ℕ)` using `hij`. Use linear arithmetic over natural numbers and integers. Rewrite using `[pow_mul]`. Conclude with `Ideal.pow_mem_pow (Ideal.pow_mem_of_mem _ hp _ (Nat.pos_of_ne_zero hpos)) c`.
-/
theorem UpperTheory.diagonal_conjugate_mem :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (ϖ : kˣ), ValuativeRel.valuation k (ϖ : k) < 1 →
        ∀ (c : ℕ) (z g : GL (Fin n) k),
        (z : Matrix (Fin n) (Fin n) k) = Matrix.diagonal (fun i : Fin n => ((ϖ ^ ((n : ℤ) - 1 - ((i : ℕ) : ℤ)) : kˣ) : k)) →
        g ∈ (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap (↥(ValuativeRel.valuation k).integer) k)).range →
        (g : Matrix (Fin n) (Fin n) k).BlockTriangular id → (∀ i, (g : Matrix (Fin n) (Fin n) k) i i = 1) →
        z ^ c * g * (z ^ c)⁻¹ ∈ Subgroup.map (Matrix.GeneralLinearGroup.map (algebraMap (↥(ValuativeRel.valuation k).integer) k))
          (Matrix.GeneralLinearGroup.map (n := Fin n)
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation k).integer ^ c))).ker := by
  intro k _ _ _ _ n ϖ hϖ c z g hz hg hb hd
  obtain ⟨g0, hg0⟩ := hg
  have hg0' : ∀ i j, algebraMap (↥(ValuativeRel.valuation k).integer) k ((g0 : Matrix (Fin n) (Fin n) _) i j)
      = (g : Matrix (Fin n) (Fin n) k) i j := by
    intro i j
    rw [← hg0]
    simp
  let p : ↥(ValuativeRel.valuation k).integer := ⟨(ϖ : k), hϖ.le⟩
  have hp : p ∈ IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation k).integer := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨q, hq⟩ := hu.exists_right_inv
    have h1 : ValuativeRel.valuation k ((p * q : ↥(ValuativeRel.valuation k).integer) : k) = 1 := by
      rw [hq]; simp
    have h2 : ValuativeRel.valuation k ((q : ↥(ValuativeRel.valuation k).integer) : k) ≤ 1 := q.2
    rw [Subring.coe_mul, map_mul] at h1
    have h3 : ValuativeRel.valuation k (ϖ : k) * ValuativeRel.valuation k ((q : ↥(ValuativeRel.valuation k).integer) : k) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' h2) hϖ
    exact absurd h1 h3.ne
  let t : Fin n → kˣ := fun i => ϖ ^ ((n : ℤ) - 1 - ((i : ℕ) : ℤ))
  have hz1 : ((z ^ c : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
      = Matrix.diagonal (fun i => (((t i) ^ c : kˣ) : k)) := by
    rw [Units.val_pow_eq_pow_val, hz, Matrix.diagonal_pow]
    congr 1
  have hz2 : (((z ^ c)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
      = Matrix.diagonal (fun i => ((((t i) ^ c)⁻¹ : kˣ) : k)) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hz1, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    rw [← Units.val_mul]
    simp
  have hent : ∀ i j, ((z ^ c * g * (z ^ c)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j
      = (((t i) ^ c : kˣ) : k) * (g : Matrix (Fin n) (Fin n) k) i j * ((((t j) ^ c)⁻¹ : kˣ) : k) := by
    intro i j
    rw [Units.val_mul, Units.val_mul, hz2, hz1, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hpow : ∀ i j : Fin n, i < j →
      (((t i) ^ c : kˣ) : k) * ((((t j) ^ c)⁻¹ : kˣ) : k) = (ϖ : k) ^ (((j : ℕ) - (i : ℕ)) * c) := by
    intro i j hij
    rw [← Units.val_mul, ← Units.val_pow_eq_pow_val]
    congr 1
    have hle : (i : ℕ) ≤ (j : ℕ) := hij.le
    simp only [t]
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_neg, ← zpow_add]
    congr 1
    push_cast [Nat.cast_sub hle]
    ring
  refine liftUnitri _ _ _
    (fun i j => if i < j then p ^ (((j : ℕ) - (i : ℕ)) * c) * (g0 : Matrix (Fin n) (Fin n) _) i j
      else if i = j then 1 else 0) ?_ ?_ ?_ ?_
  · intro i j
    rw [hent]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [if_pos hij, map_mul, hg0', map_pow, mul_right_comm, hpow i j hij]
      rfl
    · rw [if_neg (lt_irrefl _), if_pos rfl, hd, map_one, mul_one, ← Units.val_mul]
      simp
    · rw [if_neg hij.not_gt, if_neg hij.ne', hb hij]
      simp
  · intro i j hij
    rw [if_neg hij.not_gt, if_neg hij.ne']
  · intro i
    simp
  · intro i j hij
    rw [if_pos hij]
    apply Ideal.mul_mem_right
    have hpos : (j : ℕ) - (i : ℕ) ≠ 0 := by
      have : (i : ℕ) < (j : ℕ) := hij
      omega
    rw [pow_mul]
    exact Ideal.pow_mem_pow (Ideal.pow_mem_of_mem _ hp _ (Nat.pos_of_ne_zero hpos)) c
