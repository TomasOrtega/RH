import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.SqrtO

namespace UpperTheory.V.Z.Sym.Loc

open IsLocalRing Polynomial QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ : K}

/- English proof (translation)
Introduce `h`. Establish `hu : IsUnit (2 : ResidueField O)`. Establish `h2` using `L.two.map (residue O)`. Rewrite `h2` using `[map_ofNat]`. Then use the resulting hypothesis. Establish `h2 : ((ringChar (ResidueField O) : ℕ) : ResidueField O) = 0` using `ringChar.Nat.cast_ringChar`.

Rewrite `h2` using `[h]`. Conclude with `hu.ne_zero (by exact_mod_cast h2)`.
-/
theorem IsLoc.char_ne (L : IsLoc O Δ) : ringChar (ResidueField O) ≠ 2 := by
  intro h
  have hu : IsUnit (2 : ResidueField O) := by
    have h2 := L.two.map (residue O)
    rwa [map_ofNat] at h2
  have h2 : ((ringChar (ResidueField O) : ℕ) : ResidueField O) = 0 := ringChar.Nat.cast_ringChar
  rw [h] at h2
  exact hu.ne_zero (by exact_mod_cast h2)

/- English proof (translation)
Use `haveI := L.fin`. Use `letI := Fintype.ofFinite (ResidueField O)`. Establish `hodd : Fintype.card (ResidueField O) % 2 = 1`. Establish `h2` using `L.char_ne`. Rewrite `h2` using `[Ne, FiniteField.even_card_iff_char_two]`.

Use linear arithmetic over natural numbers and integers. Establish `hε0 : residue O (ε : O) ≠ 0` using `(ε.isUnit.map (residue O)).ne_zero`. Establish `hu0 : residue O (u : O) ≠ 0` using `(u.isUnit.map (residue O)).ne_zero`. Take `⟨a', b', hroot⟩` from `FiniteField.exists_root_sum_quadratic (f := X ^ 2 - C (residue O (u : O))) (g := C (-residue O (ε : O)) * X ^ 2) (degree_X_pow_sub_C (by norm_num) _) (degree_C_mul_X_pow 2 (neg_ne_zero.2 hε0)) hodd`. Take `⟨a0, rfl⟩` from `residue_surjective a'`.

Take `⟨b0, rfl⟩` from `residue_surjective b'`. Establish `hab : residue O (a0 ^ 2 - u - ε * b0 ^ 2) = 0`. Simplify using `only [eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C, map_sub, map_mul, map_pow] at hroot ⊢`. Take the linear combination `hroot`. Distinguish the cases in `ha : residue O a0 = 0`.

Establish `hb : IsUnit b0`. Rewrite using `[← residue_ne_zero_iff_isUnit]`. Introduce `hb`. Apply `hu0` to reduce the goal to its premises. Simplify using `only [map_sub, map_mul, map_pow, ha, hb] at hab`.

Take the linear combination `-hab`. Take `⟨r, hr, -⟩` from `sqrtO O K Δ L ((a0 ^ 2 - u) * ↑ε⁻¹) b0 hb (by`. Rewrite using `[← residue_eq_zero_iff]`. Establish `e1 : (a0 ^ 2 - u) * ↑ε⁻¹ - b0 ^ 2 = (a0 ^ 2 - u - ε * b0 ^ 2) * ↑ε⁻¹`. Use `ε.mul_inv` as an intermediate fact.

Take the linear combination `b0 ^ 2 * this`. Rewrite using `[e1, map_mul, hab, zero_mul])`. Use `⟨a0, r, ?_⟩` and prove the remaining obligations. Rewrite using `[hr]`. Use `ε.mul_inv` as an intermediate fact.

Take the linear combination `(-(a0 ^ 2 - u)) * this`. Establish `ha' : IsUnit a0` using `(residue_ne_zero_iff_isUnit a0).1 ha`. Take `⟨r, hr, -⟩` from `sqrtO O K Δ L (u + ε * b0 ^ 2) a0 ha' (by`. Rewrite using `[← residue_eq_zero_iff]`. Establish `e1 : (u : O) + ε * b0 ^ 2 - a0 ^ 2 = -(a0 ^ 2 - u - ε * b0 ^ 2)` using `by ring`.

Rewrite using `[e1, map_neg, hab, neg_zero])`. Conclude with `⟨r, b0, by rw [hr]; ring⟩`.
-/
theorem IsLoc.nm_unit (L : IsLoc O Δ) (ε u : Oˣ) : ∃ a b : O, a ^ 2 - ε * b ^ 2 = u := by
  haveI := L.fin
  letI := Fintype.ofFinite (ResidueField O)
  have hodd : Fintype.card (ResidueField O) % 2 = 1 := by
    have h2 := L.char_ne
    rw [Ne, FiniteField.even_card_iff_char_two] at h2
    omega
  have hε0 : residue O (ε : O) ≠ 0 := (ε.isUnit.map (residue O)).ne_zero
  have hu0 : residue O (u : O) ≠ 0 := (u.isUnit.map (residue O)).ne_zero
  obtain ⟨a', b', hroot⟩ := FiniteField.exists_root_sum_quadratic
    (f := X ^ 2 - C (residue O (u : O))) (g := C (-residue O (ε : O)) * X ^ 2)
    (degree_X_pow_sub_C (by norm_num) _) (degree_C_mul_X_pow 2 (neg_ne_zero.2 hε0)) hodd
  obtain ⟨a0, rfl⟩ := residue_surjective a'
  obtain ⟨b0, rfl⟩ := residue_surjective b'
  have hab : residue O (a0 ^ 2 - u - ε * b0 ^ 2) = 0 := by
    simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C, map_sub, map_mul, map_pow] at hroot ⊢
    linear_combination hroot
  by_cases ha : residue O a0 = 0
  · have hb : IsUnit b0 := by
      rw [← residue_ne_zero_iff_isUnit]
      intro hb
      apply hu0
      simp only [map_sub, map_mul, map_pow, ha, hb] at hab
      linear_combination -hab
    obtain ⟨r, hr, -⟩ := sqrtO O K Δ L ((a0 ^ 2 - u) * ↑ε⁻¹) b0 hb (by
      rw [← residue_eq_zero_iff]
      have e1 : (a0 ^ 2 - u) * ↑ε⁻¹ - b0 ^ 2 = (a0 ^ 2 - u - ε * b0 ^ 2) * ↑ε⁻¹ := by
        have := ε.mul_inv
        linear_combination b0 ^ 2 * this
      rw [e1, map_mul, hab, zero_mul])
    refine ⟨a0, r, ?_⟩
    rw [hr]
    have := ε.mul_inv
    linear_combination (-(a0 ^ 2 - u)) * this
  · have ha' : IsUnit a0 := (residue_ne_zero_iff_isUnit a0).1 ha
    obtain ⟨r, hr, -⟩ := sqrtO O K Δ L (u + ε * b0 ^ 2) a0 ha' (by
      rw [← residue_eq_zero_iff]
      have e1 : (u : O) + ε * b0 ^ 2 - a0 ^ 2 = -(a0 ^ 2 - u - ε * b0 ^ 2) := by ring
      rw [e1, map_neg, hab, neg_zero])
    exact ⟨r, b0, by rw [hr]; ring⟩

omit [IsDomain O] [IsDiscreteValuationRing O] [Algebra O K] in
/- English proof (translation)
Take `⟨a, b, hab⟩` from `h`. Distinguish the cases in `hb : b = 0`. Substitute `hb` using the available equality. Establish `ha : a ≠ 0`. Introduce and unpack `rfl`.

Apply `hy` to reduce the goal to its premises. Rewrite using `[← hab]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨(x + 1) / 2, (x - 1) / (2 * a), ?_⟩` and prove the remaining obligations. Rewrite using `[← hab]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `⟨a / b, 1 / b, ?_⟩` and prove the remaining obligations. Rewrite using `[← hab]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem nm_symm {x y : K} (hx : x ≠ 0) (h2 : (2 : K) ≠ 0) (h : ∃ a b : K, a ^ 2 - x * b ^ 2 = y) (hy : y ≠ 0) : ∃ a b : K, a ^ 2 - y * b ^ 2 = x := by
  obtain ⟨a, b, hab⟩ := h
  by_cases hb : b = 0
  · subst hb
    have ha : a ≠ 0 := by
      rintro rfl
      apply hy
      rw [← hab]
      ring
    refine ⟨(x + 1) / 2, (x - 1) / (2 * a), ?_⟩
    rw [← hab]
    field_simp
    ring
  · refine ⟨a / b, 1 / b, ?_⟩
    rw [← hab]
    field_simp
    ring

/- English proof (translation)
Rewrite using `[← residue_ne_zero_iff_isUnit]`. Introduce `h0`. Simplify using `only [map_sub, map_mul, map_pow] at h0`. Distinguish the cases in `hy : residue O y = 0`. Establish `hx : residue O x = 0`.

Rewrite `h0` using `[hy]`. Establish `: residue O x ^ 2 = 0` using `by linear_combination h0`. Conclude with `pow_eq_zero_iff (by norm_num) |>.1 this`. Break down `h with h | h` into its components or cases. Conclude with `(residue_ne_zero_iff_isUnit x).2 h hx`.

Conclude with `(residue_ne_zero_iff_isUnit y).2 h hy`. Apply `hε` to reduce the goal to its premises. Use `⟨residue O x / residue O y, ?_⟩` and prove the remaining obligations. Rewrite using `[div_mul_div_comm, eq_div_iff (mul_ne_zero hy hy)]`. Take the linear combination `-h0`.
-/
private theorem isUnit_sq_sub_mul_sq_of_not_isSquare_residue (ε : O) (hε : ¬ IsSquare (residue O ε)) (x y : O)
    (h : IsUnit x ∨ IsUnit y) : IsUnit (x ^ 2 - ε * y ^ 2) := by
  rw [← residue_ne_zero_iff_isUnit]
  intro h0
  simp only [map_sub, map_mul, map_pow] at h0
  by_cases hy : residue O y = 0
  · have hx : residue O x = 0 := by
      rw [hy] at h0
      have : residue O x ^ 2 = 0 := by linear_combination h0
      exact pow_eq_zero_iff (by norm_num) |>.1 this
    rcases h with h | h
    · exact (residue_ne_zero_iff_isUnit x).2 h hx
    · exact (residue_ne_zero_iff_isUnit y).2 h hy
  · apply hε
    refine ⟨residue O x / residue O y, ?_⟩
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hy hy)]
    linear_combination -h0

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Establish `hy : y ≠ 0` using `by tauto`. Take `⟨n, v, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hπ`. Conclude with `⟨n, 0, v, by simp [hx], by ring, Or.inr v.isUnit⟩`. Distinguish the cases in `hy : y = 0`.

Take `⟨m, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ`. Conclude with `⟨m, u, 0, by ring, by simp [hy], Or.inl u.isUnit⟩`. Take `⟨m, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ`. Take `⟨n, v, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hπ`. Break down `le_total m n with hmn | hnm` into its components or cases.

Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hmn`. Conclude with `⟨m, u, v * π ^ d, by ring, by ring, Or.inl u.isUnit⟩`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hnm`. Conclude with `⟨n, u * π ^ d, v, by ring, by ring, Or.inr v.isUnit⟩`.
-/
private theorem exists_common_pow_factor_coprime_units {π : O} (hπ : Irreducible π) (x y : O) (h : x ≠ 0 ∨ y ≠ 0) :
    ∃ (k : ℕ) (x' y' : O), x = π ^ k * x' ∧ y = π ^ k * y' ∧ (IsUnit x' ∨ IsUnit y') := by
  by_cases hx : x = 0
  · have hy : y ≠ 0 := by tauto
    obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hπ
    exact ⟨n, 0, v, by simp [hx], by ring, Or.inr v.isUnit⟩
  by_cases hy : y = 0
  · obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
    exact ⟨m, u, 0, by ring, by simp [hy], Or.inl u.isUnit⟩
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hπ
  rcases le_total m n with hmn | hnm
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact ⟨m, u, v * π ^ d, by ring, by ring, Or.inl u.isUnit⟩
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    exact ⟨n, u * π ^ d, v, by ring, by ring, Or.inr v.isUnit⟩

/- English proof (translation)
Introduce and unpack `⟨c, hc⟩`. Take `⟨r₀, rfl⟩` from `residue_surjective c`. Establish `hε0 : residue O (ε : O) ≠ 0` using `(ε.isUnit.map (residue O)).ne_zero`. Establish `hr₀ : IsUnit r₀`. Rewrite using `[← residue_ne_zero_iff_isUnit]`.

Introduce `h0`. Rewrite `hc` using `[h0, mul_zero]`. Conclude with `hε0 hc`. Take `⟨r, hr, -⟩` from `sqrtO O K Δ L ε r₀ hr₀ (by`. Rewrite using `[← residue_eq_zero_iff, map_sub, map_pow, hc, sq, sub_self])`.

Apply `hε` to reduce the goal to its premises. Conclude with `⟨algebraMap O K r, by rw [← map_mul, ← sq, hr]⟩`.
-/
private theorem not_isSquare_residue_of_not_isSquare (L : IsLoc O Δ) (ε : Oˣ) (hε : ¬ IsSquare (algebraMap O K ε)) :
    ¬ IsSquare (residue O (ε : O)) := by
  rintro ⟨c, hc⟩
  obtain ⟨r₀, rfl⟩ := residue_surjective c
  have hε0 : residue O (ε : O) ≠ 0 := (ε.isUnit.map (residue O)).ne_zero
  have hr₀ : IsUnit r₀ := by
    rw [← residue_ne_zero_iff_isUnit]
    intro h0
    rw [h0, mul_zero] at hc
    exact hε0 hc
  obtain ⟨r, hr, -⟩ := sqrtO O K Δ L ε r₀ hr₀ (by
    rw [← residue_eq_zero_iff, map_sub, map_pow, hc, sq, sub_self])
  apply hε
  exact ⟨algebraMap O K r, by rw [← map_mul, ← sq, hr]⟩

/- English proof (translation)
Use `haveI := L.frac`. Establish `hres` using `not_isSquare_residue_of_not_isSquare L ε hε`. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨x1, z1, hz1, rfl⟩` from `IsFractionRing.div_surjective (A := O) a`. Take `⟨y1, z2, hz2, rfl⟩` from `IsFractionRing.div_surjective (A := O) b`.

Establish `hz1' : algebraMap O K z1 ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hz1`. Establish `hz2' : algebraMap O K z2 ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hz2`. Establish `heq : (algebraMap O K x1 / algebraMap O K z1) ^ 2 - algebraMap O K ε * (algebraMap O K y1 / algebraMap O K z2) ^ 2 = algebraMap O K ((x1 * z2) ^ 2 - ε * (y1 * z1) ^ 2) / (algebraMap O K (z1 * z2)) ^ 2`. Simplify using `only [map_sub, map_mul, map_pow]`. Clear the denominators using the available nonvanishing facts.

Rewrite `h`, the goal using `[heq]`. Establish `hnz : x1 * z2 ≠ 0 ∨ y1 * z1 ≠ 0`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Apply `h` to reduce the goal to its premises.

Rewrite using `[hc.1, hc.2]`. Simplify using the standard rewrite rules. Take `⟨k, x', y', hx, hy, hu⟩` from `exists_common_pow_factor_coprime_units hπ _ _ hnz`. Establish `hw` using `isUnit_sq_sub_mul_sq_of_not_isSquare_residue (ε : O) hres x' y' hu`. Establish `hπ0 : algebraMap O K π ≠ 0`.

Rewrite using `[ne_eq, map_eq_zero_iff _ (IsFractionRing.injective O K)]`. Conclude with `hπ.ne_zero`. Establish `hzz : algebraMap O K (z1 * z2) ≠ 0`. Rewrite using `[map_mul]`. Conclude with `mul_ne_zero hz1' hz2'`.

Use `⟨hw.unit, algebraMap O K π ^ k / algebraMap O K (z1 * z2), div_ne_zero (pow_ne_zero _ hπ0) hzz, ?_⟩` and prove the remaining obligations. Rewrite using `[hx, hy, IsUnit.unit_spec]`. Simplify using `only [map_sub, map_mul, map_pow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem IsLoc.even_of_norm (L : IsLoc O Δ) (ε : Oˣ) (hε : ¬ IsSquare (algebraMap O K ε)) {a b : K}
    (h : a ^ 2 - algebraMap O K ε * b ^ 2 ≠ 0) : EvenVal O (a ^ 2 - algebraMap O K ε * b ^ 2) := by
  haveI := L.frac
  have hres := not_isSquare_residue_of_not_isSquare L ε hε
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨x1, z1, hz1, rfl⟩ := IsFractionRing.div_surjective (A := O) a
  obtain ⟨y1, z2, hz2, rfl⟩ := IsFractionRing.div_surjective (A := O) b
  have hz1' : algebraMap O K z1 ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hz1
  have hz2' : algebraMap O K z2 ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hz2
  have heq : (algebraMap O K x1 / algebraMap O K z1) ^ 2
      - algebraMap O K ε * (algebraMap O K y1 / algebraMap O K z2) ^ 2
      = algebraMap O K ((x1 * z2) ^ 2 - ε * (y1 * z1) ^ 2) / (algebraMap O K (z1 * z2)) ^ 2 := by
    simp only [map_sub, map_mul, map_pow]
    field_simp
  rw [heq] at h ⊢
  have hnz : x1 * z2 ≠ 0 ∨ y1 * z1 ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply h
    rw [hc.1, hc.2]
    simp
  obtain ⟨k, x', y', hx, hy, hu⟩ := exists_common_pow_factor_coprime_units hπ _ _ hnz
  have hw := isUnit_sq_sub_mul_sq_of_not_isSquare_residue (ε : O) hres x' y' hu
  have hπ0 : algebraMap O K π ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective O K)]
    exact hπ.ne_zero
  have hzz : algebraMap O K (z1 * z2) ≠ 0 := by
    rw [map_mul]
    exact mul_ne_zero hz1' hz2'
  refine ⟨hw.unit, algebraMap O K π ^ k / algebraMap O K (z1 * z2),
    div_ne_zero (pow_ne_zero _ hπ0) hzz, ?_⟩
  rw [hx, hy, IsUnit.unit_spec]
  simp only [map_sub, map_mul, map_pow]
  field_simp

/- English proof (translation)
Use `haveI := L.frac`. Introduce and unpack `⟨u, s, hs, he⟩`. Take `⟨x, y, hy, rfl⟩` from `IsFractionRing.div_surjective (A := O) s`. Establish `hy0 : y ≠ 0` using `nonZeroDivisors.ne_zero hy`. Establish `hyK : algebraMap O K y ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy`.

Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hs`. Establish `key : p * y ^ 2 = (u : O) * x ^ 2`. Apply `IsFractionRing.injective O K` to reduce the goal to its premises.

Simplify using `only [map_mul, map_pow]`. Rewrite using `[he]`. Clear the denominators using the available nonvanishing facts. Take `⟨m, v, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hp`. Take `⟨n, w, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hp`.

Establish `e2 : ((w ^ 2 : Oˣ) : O) * p ^ (2 * n + 1) = ((u * v ^ 2 : Oˣ) : O) * p ^ (2 * m)`. Use `push_cast`. Take the linear combination `key`. Use `IsDiscreteValuationRing.unit_mul_pow_congr_pow hp hp _ _ _ _ e2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem IsLoc.not_even (L : IsLoc O Δ) {p : O} (hp : Irreducible p) : ¬ EvenVal O (algebraMap O K p) := by
  haveI := L.frac
  rintro ⟨u, s, hs, he⟩
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := O) s
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hyK : algebraMap O K y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hs
  have key : p * y ^ 2 = (u : O) * x ^ 2 := by
    apply IsFractionRing.injective O K
    simp only [map_mul, map_pow]
    rw [he]
    field_simp
  obtain ⟨m, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hp
  obtain ⟨n, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hp
  have e2 : ((w ^ 2 : Oˣ) : O) * p ^ (2 * n + 1) = ((u * v ^ 2 : Oˣ) : O) * p ^ (2 * m) := by
    push_cast
    linear_combination key
  have := IsDiscreteValuationRing.unit_mul_pow_congr_pow hp hp _ _ _ _ e2
  omega

/- English proof (translation)
Use `haveI := L.frac`. Use `haveI := L.fin`. Use `letI := Fintype.ofFinite (ResidueField O)`. Take `⟨c, hc⟩` from `FiniteField.exists_nonsquare L.char_ne`. Take `⟨e, rfl⟩` from `residue_surjective c`.

Establish `he : IsUnit e`. Rewrite using `[← residue_ne_zero_iff_isUnit]`. Introduce `h0`. Apply `hc` to reduce the goal to its premises. Rewrite using `[h0]`.

Conclude with `⟨0, by simp⟩`. Use `⟨he.unit, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨t, ht⟩`. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨x, z, hz, rfl⟩` from `IsFractionRing.div_surjective (A := O) t`.

Establish `hz0 : z ≠ 0` using `nonZeroDivisors.ne_zero hz`. Establish `hz' : algebraMap O K z ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hz`. Rewrite `ht` using `[IsUnit.unit_spec]`. Establish `h0 : x ^ 2 - e * z ^ 2 = 0`. Apply `IsFractionRing.injective O K` to reduce the goal to its premises.

Simplify using `only [map_sub, map_mul, map_pow, map_zero, ht]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Take `⟨k, x', z', hx, hz2, hu⟩` from `exists_common_pow_factor_coprime_units hπ x z (Or.inr hz0)`. Establish `hw` using `isUnit_sq_sub_mul_sq_of_not_isSquare_residue e hc x' z' hu`.

Establish `e3 : π ^ (2 * k) * (x' ^ 2 - e * z' ^ 2) = 0`. Rewrite using `[← h0, hx, hz2]`. Expand and normalize the polynomial expressions, which then agree. Break down `mul_eq_zero.1 e3 with h | h` into its components or cases. Conclude with `pow_ne_zero _ hπ.ne_zero h`.

Conclude with `hw.ne_zero h`.
-/
theorem IsLoc.exists_nonsq (L : IsLoc O Δ) : ∃ ε : Oˣ, ¬ IsSquare (algebraMap O K ε) := by
  haveI := L.frac
  haveI := L.fin
  letI := Fintype.ofFinite (ResidueField O)
  obtain ⟨c, hc⟩ := FiniteField.exists_nonsquare L.char_ne
  obtain ⟨e, rfl⟩ := residue_surjective c
  have he : IsUnit e := by
    rw [← residue_ne_zero_iff_isUnit]
    intro h0
    apply hc
    rw [h0]
    exact ⟨0, by simp⟩
  refine ⟨he.unit, ?_⟩
  rintro ⟨t, ht⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨x, z, hz, rfl⟩ := IsFractionRing.div_surjective (A := O) t
  have hz0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
  have hz' : algebraMap O K z ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hz
  rw [IsUnit.unit_spec] at ht
  have h0 : x ^ 2 - e * z ^ 2 = 0 := by
    apply IsFractionRing.injective O K
    simp only [map_sub, map_mul, map_pow, map_zero, ht]
    field_simp
    ring
  obtain ⟨k, x', z', hx, hz2, hu⟩ := exists_common_pow_factor_coprime_units hπ x z (Or.inr hz0)
  have hw := isUnit_sq_sub_mul_sq_of_not_isSquare_residue e hc x' z' hu
  have e3 : π ^ (2 * k) * (x' ^ 2 - e * z' ^ 2) = 0 := by
    rw [← h0, hx, hz2]
    ring
  rcases mul_eq_zero.1 e3 with h | h
  · exact pow_ne_zero _ hπ.ne_zero h
  · exact hw.ne_zero h

end UpperTheory.V.Z.Sym.Loc
