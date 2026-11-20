import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.CyclotomicInertiaSpan.CycIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.PlacesQ

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

/- English proof (translation)
Apply `sq_eq_sq_iff_eq_or_eq_neg.1` to reduce the goal to its premises. Rewrite using `[← map_pow, hx, map_intCast]`.
-/
private theorem galois_sqrt_sign {Ω : Type} [Field Ω] [CharZero Ω] (s : G ℚ Ω) {x : Ω} {n : ℤ} (hx : x ^ 2 = n) :
    s x = x ∨ s x = -x := by
  apply sq_eq_sq_iff_eq_or_eq_neg.1
  rw [← map_pow, hx, map_intCast]

/- English proof (translation)
Use `(galois_sqrt_sign s hx).resolve_right fun h => ?_` and prove the remaining obligations. Use `set y : Ω := (1 + x) / 2 with hy`. Establish `h1 : s y = 1 - y` using `by rw [hy, map_div₀, map_add, map_one, h, map_ofNat]; ring`. Establish `h2 : y * (1 - y) = -k`. Move the coercions through the operations in `at hx`.

Rewrite using `[hy]`. Take the linear combination `(-1 / 4 : Ω) * hx`. Establish `h3 : B.valuation (1 - y) < 1 ↔ B.valuation y < 1` using `by rw [← h1]; exact valuation_apply_lt_one_iff hs y`. Establish `h4 : B.valuation y < 1`. Assume the negation of the conclusion as `h5`.

Establish `h6 : 1 ≤ B.valuation (y * (1 - y))`. Rewrite using `[map_mul]`. Conclude with `one_le_mul (not_lt.1 h5) (not_lt.1 (h3.not.2 h5))`. Rewrite `h6` using `[h2, Valuation.map_neg]`. Conclude with `absurd hk (not_lt.2 h6)`.

Establish `h7` using `B.valuation.map_add_lt h4 (h3.2 h4)`. Simplify using `at h7`.
-/
private theorem decomposition_fixes_sqrt {Ω : Type} [Field Ω] [CharZero Ω] (B : ValuationSubring Ω) {x : Ω} {k : ℤ}
    (hx : x ^ 2 = ((1 + 4 * k : ℤ) : Ω)) (hk : B.valuation (k : Ω) < 1) {s : G ℚ Ω} (hs : s ∈ Dec (F := ℚ) B) : s x = x := by
  refine (galois_sqrt_sign s hx).resolve_right fun h => ?_
  set y : Ω := (1 + x) / 2 with hy
  have h1 : s y = 1 - y := by rw [hy, map_div₀, map_add, map_one, h, map_ofNat]; ring
  have h2 : y * (1 - y) = -k := by
    push_cast at hx
    rw [hy]; linear_combination (-1 / 4 : Ω) * hx
  have h3 : B.valuation (1 - y) < 1 ↔ B.valuation y < 1 := by rw [← h1]; exact valuation_apply_lt_one_iff hs y
  have h4 : B.valuation y < 1 := by
    by_contra h5
    have h6 : 1 ≤ B.valuation (y * (1 - y)) := by
      rw [map_mul]; exact one_le_mul (not_lt.1 h5) (not_lt.1 (h3.not.2 h5))
    rw [h2, Valuation.map_neg] at h6
    exact absurd hk (not_lt.2 h6)
  have h7 := B.valuation.map_add_lt h4 (h3.2 h4)
  simp at h7

/- English proof (translation)
Introduce `hn`. Take `⟨a, b, hab⟩` from `Nat.isCoprime_iff_coprime.2 h`. Establish `e : (a : Ω) * p + b * n = 1` using `by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab`. Establish `hm : ∀ (c : ℤ) (z : Ω), B.valuation z < 1 → B.valuation (c * z) < 1` using `fun c z hz => by`. Rewrite using `[map_mul]`.

Conclude with `(mul_le_of_le_one_left' ((B.valuation_le_one_iff _).2 (intCast_mem B c))).trans_lt hz`. Use `B.valuation.map_add_lt (hm a _ hp) (hm b _ hn)` as an intermediate fact. Rewrite `this` using `[e, map_one]`. Conclude with `lt_irrefl _ this`.
-/
private theorem etaleSimplicialCochain_scheme_section_extension_naturality {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {p n : ℕ} (hp : B.valuation (p : Ω) < 1)
    (h : p.Coprime n) : ¬ B.valuation (n : Ω) < 1 := by
  intro hn
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have e : (a : Ω) * p + b * n = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  have hm : ∀ (c : ℤ) (z : Ω), B.valuation z < 1 → B.valuation (c * z) < 1 := fun c z hz => by
    rw [map_mul]
    exact (mul_le_of_le_one_left' ((B.valuation_le_one_iff _).2 (intCast_mem B c))).trans_lt hz
  have := B.valuation.map_add_lt (hm a _ hp) (hm b _ hn)
  rw [e, map_one] at this
  exact lt_irrefl _ this

/- English proof (translation)
Use `(galois_sqrt_sign s (n := -D) (by rw [hδ]; simp)).resolve_right fun h => hD ?_` and prove the remaining obligations. Establish `h1 : B.valuation δ ≤ 1`. Establish `: B.valuation δ ^ 2 ≤ 1`. Rewrite using `[← map_pow, hδ, Valuation.map_neg]`. Conclude with `(B.valuation_le_one_iff _).2 (natCast_mem B D)`.

Conclude with `(pow_le_one_iff_of_nonneg zero_le' two_ne_zero).1 this`. Establish `h2` using `hs.2 δ h1`. Establish `e : ((4 * D : ℕ) : Ω) = -((s δ - δ) ^ 2)` using `by rw [h]; push_cast; linear_combination (4 : Ω) * hδ`. Rewrite using `[e, Valuation.map_neg, map_pow]`. Conclude with `pow_lt_one₀ zero_le' h2 two_ne_zero`.
-/
private theorem inertia_fixes_sqrt_discriminant {Ω : Type} [Field Ω] [CharZero Ω] (B : ValuationSubring Ω) {δ : Ω} {D : ℕ}
    (hδ : δ ^ 2 = -(D : Ω)) (hD : ¬ B.valuation ((4 * D : ℕ) : Ω) < 1) {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) B) : s δ = δ := by
  refine (galois_sqrt_sign s (n := -D) (by rw [hδ]; simp)).resolve_right fun h => hD ?_
  have h1 : B.valuation δ ≤ 1 := by
    have : B.valuation δ ^ 2 ≤ 1 := by
      rw [← map_pow, hδ, Valuation.map_neg]; exact (B.valuation_le_one_iff _).2 (natCast_mem B D)
    exact (pow_le_one_iff_of_nonneg zero_le' two_ne_zero).1 this
  have h2 := hs.2 δ h1
  have e : ((4 * D : ℕ) : Ω) = -((s δ - δ) ^ 2) := by rw [h]; push_cast; linear_combination (4 : Ω) * hδ
  rw [e, Valuation.map_neg, map_pow]
  exact pow_lt_one₀ zero_le' h2 two_ne_zero

/- English proof (translation)
Establish `: IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed ℚ`. Establish `: NeZero (p : Ω)` using `⟨Nat.cast_ne_zero.2 hp.out.ne_zero⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω p`. Establish `h2 : ringChar (ZMod p) ≠ 2` using `by rw [ZMod.ringChar_zmod_n]; omega`. Set `ψ` to `AddChar.zmodChar p hζ.pow_eq_one`.

Establish `hψ : ψ.IsPrimitive` using `AddChar.zmodChar_primitive_of_primitive_root p hζ`. Set `χ` to `(quadraticChar (ZMod p)).ringHomComp (Int.castRingHom Ω)`. Establish `hχ : χ ≠ 1` using `(MulChar.ringHomComp_ne_one_iff (RingHom.injective_int _)).2 (quadraticChar_ne_one h2)`. Establish `hq : χ.IsQuadratic` using `(quadraticChar_isQuadratic _).comp _`. Establish `hm : χ (-1) = -1` using `by show ((quadraticChar (ZMod p) (-1) : ℤ) : Ω) = -1`.

Rewrite using `[quadraticChar_neg_one h2, ZMod.card, ZMod.χ₄_nat_three_mod_four h4]`. Simplify using the standard rewrite rules. Establish `hmem : (-1 : (ZMod p)ˣ) ∈ (Ine (F` using `ℚ) B).map (B1.cycN ℚ Ω p) := by`. Rewrite using `[B1.cycIne Ω p p B hB, B3.pPart, MonoidHom.mem_ker]`. Establish `: ordCompl[p] p = 1` using `by rw [hp.out.factorization_self, pow_one, Nat.div_self hp.out.pos]`.

Establish `: Subsingleton (ZMod (ordCompl[p] p))` using `by rw [this]; infer_instance`. Conclude with `Subsingleton.elim _ _`. Take `⟨s, hs, hs'⟩` from `hmem`. Use `⟨gaussSum χ ψ, by rw [gaussSum_sq hχ hq hψ, hm, ZMod.card]; simp, s, hs, ?_⟩` and prove the remaining obligations. Establish `h3` using `gaussSum_mulShift χ ψ (-1)`.

Rewrite `h3` using `[Units.val_neg, Units.val_one, hm, neg_one_mul, neg_eq_iff_eq_neg]`. Rewrite using `[← h3, gaussSum, gaussSum, map_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Use `congr 1`.

Conclude with `map_intCast s _`. Establish `h5 : ψ a ^ p = 1` using `by rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]`. Rewrite using `[B1.cycN_spec ℚ Ω p s h5, hs', ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_zmod_val, AddChar.mulShift_apply]`. Simplify using the standard rewrite rules.
-/
private theorem gauss_sqrt_inertia_negates {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [hp : Fact p.Prime] (h4 : p % 4 = 3)
    (B : ValuationSubring Ω) (hB : B.valuation (p : Ω) < 1) :
    ∃ x : Ω, x ^ 2 = -(p : Ω) ∧ ∃ s ∈ Ine (F := ℚ) B, s x = -x := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero (p : Ω) := ⟨Nat.cast_ne_zero.2 hp.out.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω p
  have h2 : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  let ψ := AddChar.zmodChar p hζ.pow_eq_one
  have hψ : ψ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root p hζ
  let χ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom Ω)
  have hχ : χ ≠ 1 := (MulChar.ringHomComp_ne_one_iff (RingHom.injective_int _)).2 (quadraticChar_ne_one h2)
  have hq : χ.IsQuadratic := (quadraticChar_isQuadratic _).comp _
  have hm : χ (-1) = -1 := by
    show ((quadraticChar (ZMod p) (-1) : ℤ) : Ω) = -1
    rw [quadraticChar_neg_one h2, ZMod.card, ZMod.χ₄_nat_three_mod_four h4]; simp
  have hmem : (-1 : (ZMod p)ˣ) ∈ (Ine (F := ℚ) B).map (B1.cycN ℚ Ω p) := by
    rw [B1.cycIne Ω p p B hB, B3.pPart, MonoidHom.mem_ker]
    have : ordCompl[p] p = 1 := by rw [hp.out.factorization_self, pow_one, Nat.div_self hp.out.pos]
    have : Subsingleton (ZMod (ordCompl[p] p)) := by rw [this]; infer_instance
    exact Subsingleton.elim _ _
  obtain ⟨s, hs, hs'⟩ := hmem
  refine ⟨gaussSum χ ψ, by rw [gaussSum_sq hχ hq hψ, hm, ZMod.card]; simp, s, hs, ?_⟩
  have h3 := gaussSum_mulShift χ ψ (-1)
  rw [Units.val_neg, Units.val_one, hm, neg_one_mul, neg_eq_iff_eq_neg] at h3
  rw [← h3, gaussSum, gaussSum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul]
  congr 1
  · exact map_intCast s _
  · have h5 : ψ a ^ p = 1 := by rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]
    rw [B1.cycN_spec ℚ Ω p s h5, hs', ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_zmod_val, AddChar.mulShift_apply]
    simp

/- English proof (translation)
Use `(galois_sqrt_sign τ (n := n) (by rw [hz]; simp)).resolve_right fun h1 => ?_` and prove the remaining obligations. Take `⟨j, hj⟩` from `h`. Establish `h2 : starRingEnd ℂ (j z) = -j z` using `by rw [← map_neg, ← h1]; exact (hj z).symm`. Establish `h3` using `Complex.mul_conj (j z)`. Rewrite `h3` using `[h2, mul_neg, ← sq, ← map_pow, hz, map_natCast]`.

Establish `h4 : -(n : ℝ) = Complex.normSq (j z)` using `by exact_mod_cast h3`. Establish `h5` using `Complex.normSq_nonneg (j z)`. Establish `h6 : (0 : ℝ) < n` using `by exact_mod_cast hn`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem complex_conjugation_fixes_sqrt {Ω : Type} [Field Ω] [CharZero Ω] {τ : G ℚ Ω} (h : IsCC τ) {z : Ω} {n : ℕ} (hn : 0 < n)
    (hz : z ^ 2 = n) : τ z = z := by
  refine (galois_sqrt_sign τ (n := n) (by rw [hz]; simp)).resolve_right fun h1 => ?_
  obtain ⟨j, hj⟩ := h
  have h2 : starRingEnd ℂ (j z) = -j z := by rw [← map_neg, ← h1]; exact (hj z).symm
  have h3 := Complex.mul_conj (j z)
  rw [h2, mul_neg, ← sq, ← map_pow, hz, map_natCast] at h3
  have h4 : -(n : ℝ) = Complex.normSq (j z) := by exact_mod_cast h3
  have h5 := Complex.normSq_nonneg (j z)
  have h6 : (0 : ℝ) < n := by exact_mod_cast hn
  linarith

/- English proof (translation)
Introduce `Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG`. Take `⟨D, δ, hD, -, hδ, hη⟩` from `hG.quad`. Establish `hM` using `hG.M_ne`. Take `⟨p, hlt, hp, hmod⟩` from `Nat.forall_exists_prime_gt_and_zmodEq (4 * D + M) (q := 4 * M) (a := -1) (by omega) isCoprime_one_left.neg_left`. Establish `: Fact p.Prime` using `⟨hp⟩`.

Take `⟨t, ht⟩` from `hmod.dvd`. Establish `ht' : -(p : ℤ) = 1 + 4 * (M * t)` using `by push_cast at ht; linear_combination ht`. Take `⟨A, hA⟩` from `(B3.placesQ Ω).1 p hp`. Take `⟨x, hx, s, hs, hsx⟩` from `gauss_sqrt_inertia_negates p (by omega) A hA`. Establish `hsδ : s δ = δ` using `inertia_fixes_sqrt_discriminant A hδ (etaleSimplicialCochain_scheme_section_extension_naturality A hA (Nat.coprime_of_lt_prime (by omega) (by omega) hp)) hs`.

Establish `hz : (δ * x) ^ 2 = ((D * p : ℕ) : Ω)` using `by rw [mul_pow, hδ, hx]; push_cast; ring`. Establish `hpos : 0 < D * p` using `Nat.mul_pos hD hp.pos`. Establish `hz0 : δ * x ≠ 0` using `fun h => by`. Rewrite `hz` using `[h, zero_pow two_ne_zero]`. Conclude with `hpos.ne (by exact_mod_cast hz)`.

Establish `hne : -(δ * x) ≠ δ * x` using `fun h => hz0 (by linear_combination (-1 / 2 : Ω) * h)`. Establish `hsz : s (δ * x) = -(δ * x)` using `by rw [map_mul, hsδ, hsx, mul_neg]`. Establish `hmem : ∀ g : G ℚ Ω, g ∈ MulAction.stabilizer (G ℚ Ω) (δ * x) ↔ g (δ * x) = δ * x` using `fun g => Iff.rfl`. Establish `: Algebra.IsAlgebraic ℚ Ω` using `IsAlgClosure.isAlgebraic`. Use `⟨MulAction.stabilizer (G ℚ Ω) (δ * x), stabilizer_isOpen_of_isIntegral _, ?_, fun τ hτ => complex_conjugation_fixes_sqrt hτ hpos hz, fun B' hB' => ?_, A, etaleSimplicialCochain_scheme_section_extension_naturality A hA (Nat.coprime_of_lt_prime hM (by omega) hp), fun h => hne (hsz. …` and prove the remaining obligations.

Use `Subgroup.index_eq_two_iff.2 ⟨s, fun b => ?_⟩` and prove the remaining obligations. Rewrite using `[hmem, hmem, AlgEquiv.mul_apply, hsz, map_neg]`. Break down `galois_sqrt_sign b (n := (D * p : ℕ)) (hz.trans (Int.cast_natCast _).symm) with h | h` into its components or cases. Rewrite using `[h]`. Conclude with `Or.inr ⟨rfl, hne⟩`.

Rewrite using `[h, neg_neg]`. Conclude with `Or.inl ⟨rfl, hne⟩`. Establish `hk : B'.valuation ((M * t : ℤ) : Ω) < 1`. Rewrite using `[Int.cast_mul, Int.cast_natCast, map_mul]`. Conclude with `mul_lt_one_of_lt_of_le hB' ((B'.valuation_le_one_iff _).2 (intCast_mem B' t))`.

Use extensionality with `g`. Use `and_congr_right fun hg => ?_` and prove the remaining obligations. Establish `hgx : g x = x` using `decomposition_fixes_sqrt B' (by rw [← ht', hx]; simp) hk hg`. Use `show g (δ * x) = δ * x ↔ η g = 1`. Rewrite using `[map_mul, hgx, hη]`.

Break down `Int.units_eq_one_or (η g) with h | h` into its components or cases. Simplify using `[h]`. Rewrite using `[h]`. Use `iff_of_false (fun h' => hne ?_) (by decide)` and prove the remaining obligations. Simplify using `using h'`.
-/
theorem UpperTheory.V.Fr.exists_twistCharacter_continuousCohomology :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∃ H₀, FrobeniusSplitPrimeDatum η M H₀ := by
  intro Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG
  obtain ⟨D, δ, hD, -, hδ, hη⟩ := hG.quad
  have hM := hG.M_ne
  obtain ⟨p, hlt, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_zmodEq (4 * D + M) (q := 4 * M) (a := -1) (by omega)
    isCoprime_one_left.neg_left
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht⟩ := hmod.dvd
  have ht' : -(p : ℤ) = 1 + 4 * (M * t) := by push_cast at ht; linear_combination ht
  obtain ⟨A, hA⟩ := (B3.placesQ Ω).1 p hp
  obtain ⟨x, hx, s, hs, hsx⟩ := gauss_sqrt_inertia_negates p (by omega) A hA
  have hsδ : s δ = δ := inertia_fixes_sqrt_discriminant A hδ (etaleSimplicialCochain_scheme_section_extension_naturality A hA (Nat.coprime_of_lt_prime (by omega) (by omega) hp)) hs
  have hz : (δ * x) ^ 2 = ((D * p : ℕ) : Ω) := by rw [mul_pow, hδ, hx]; push_cast; ring
  have hpos : 0 < D * p := Nat.mul_pos hD hp.pos
  have hz0 : δ * x ≠ 0 := fun h => by
    rw [h, zero_pow two_ne_zero] at hz
    exact hpos.ne (by exact_mod_cast hz)
  have hne : -(δ * x) ≠ δ * x := fun h => hz0 (by linear_combination (-1 / 2 : Ω) * h)
  have hsz : s (δ * x) = -(δ * x) := by rw [map_mul, hsδ, hsx, mul_neg]
  have hmem : ∀ g : G ℚ Ω, g ∈ MulAction.stabilizer (G ℚ Ω) (δ * x) ↔ g (δ * x) = δ * x := fun g => Iff.rfl
  have : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  refine ⟨MulAction.stabilizer (G ℚ Ω) (δ * x), stabilizer_isOpen_of_isIntegral _, ?_, fun τ hτ => complex_conjugation_fixes_sqrt hτ hpos hz,
    fun B' hB' => ?_, A, etaleSimplicialCochain_scheme_section_extension_naturality A hA (Nat.coprime_of_lt_prime hM (by omega) hp), fun h => hne (hsz.symm.trans (h hs))⟩
  · refine Subgroup.index_eq_two_iff.2 ⟨s, fun b => ?_⟩
    rw [hmem, hmem, AlgEquiv.mul_apply, hsz, map_neg]
    rcases galois_sqrt_sign b (n := (D * p : ℕ)) (hz.trans (Int.cast_natCast _).symm) with h | h
    · rw [h]; exact Or.inr ⟨rfl, hne⟩
    · rw [h, neg_neg]; exact Or.inl ⟨rfl, hne⟩
  · have hk : B'.valuation ((M * t : ℤ) : Ω) < 1 := by
      rw [Int.cast_mul, Int.cast_natCast, map_mul]
      exact mul_lt_one_of_lt_of_le hB' ((B'.valuation_le_one_iff _).2 (intCast_mem B' t))
    ext g
    refine and_congr_right fun hg => ?_
    have hgx : g x = x := decomposition_fixes_sqrt B' (by rw [← ht', hx]; simp) hk hg
    show g (δ * x) = δ * x ↔ η g = 1
    rw [map_mul, hgx, hη]
    rcases Int.units_eq_one_or (η g) with h | h
    · simp [h]
    · rw [h]
      refine iff_of_false (fun h' => hne ?_) (by decide)
      simpa using h'
