import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open UpperTheory.V UpperTheory.V.Af
open scoped Pointwise

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

omit [NumberField F] in
/- English proof (translation)
Establish `e : ∀ z : Ω, g z ∈ g • A ↔ z ∈ A` using `fun z => by`. Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, show g z = g • z from rfl, inv_smul_smul]`. Rewrite using `[valuation_lt_one_iff', valuation_lt_one_iff', e, ← map_inv₀, e, map_eq_zero]`.
-/
private theorem val_smul_lt (g : G F Ω) (A : ValuationSubring Ω) (y : Ω) :
    (g • A).valuation (g y) < 1 ↔ A.valuation y < 1 := by
  have e : ∀ z : Ω, g z ∈ g • A ↔ z ∈ A := fun z => by
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, show g z = g • z from rfl, inv_smul_smul]
  rw [valuation_lt_one_iff', valuation_lt_one_iff', e, ← map_inv₀, e, map_eq_zero]

omit [NumberField F] in
/- English proof (translation)
Rewrite using `[ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, show g y = g • y from rfl, inv_smul_smul]`.
-/
private theorem val_smul_le (g : G F Ω) (A : ValuationSubring Ω) (y : Ω) :
    (g • A).valuation (g y) ≤ 1 ↔ A.valuation y ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, show g y = g • y from rfl, inv_smul_smul]

omit [NumberField F] in
/- English proof (translation)
Establish `h1 : τ • g • A = g • A` using `h`. Use `show (g⁻¹ * τ * g) • A = A`. Rewrite using `[mul_smul, mul_smul, h1, inv_smul_smul]`.
-/
private theorem conj_dec {g τ : G F Ω} {A : ValuationSubring Ω} (h : τ ∈ (g • A).decompositionSubgroup F) :
    g⁻¹ * τ * g ∈ A.decompositionSubgroup F := by
  have h1 : τ • g • A = g • A := h
  show (g⁻¹ * τ * g) • A = A
  rw [mul_smul, mul_smul, h1, inv_smul_smul]

omit [NumberField F] in
/- English proof (translation)
Express the relevant statement in the definitionally equal form `g • ((g⁻¹ * τ * g) • x) = τ • (g • x)`. Rewrite using `[mul_smul, mul_smul, smul_inv_smul]`.
-/
private theorem conj_apply (g τ : G F Ω) (x : Ω) : g ((g⁻¹ * τ * g) x) = τ (g x) := by
  change g • ((g⁻¹ * τ * g) • x) = τ • (g • x)
  rw [mul_smul, mul_smul, smul_inv_smul]

omit [NumberField F] in
/- English proof (translation)
Use `⟨conj_dec h.1, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h1` using `h.2 (g x) ((val_smul_le g A x).2 hx)`. Rewrite `h1` using `[← conj_apply, ← map_pow, ← map_sub, val_smul_lt]`. Then use the resulting hypothesis.
-/
private theorem conj_frob {g τ : G F Ω} {A : ValuationSubring Ω} {q : ℕ} (h : IsFrob (g • A) q τ) :
    IsFrob A q (g⁻¹ * τ * g) := by
  refine ⟨conj_dec h.1, fun x hx => ?_⟩
  have h1 := h.2 (g x) ((val_smul_le g A x).2 hx)
  rwa [← conj_apply, ← map_pow, ← map_sub, val_smul_lt] at h1

/- English proof (translation)
Use `⟨conj_dec h.1, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h1` using `h.2 (g x) ((val_smul_le g A x).2 hx)`. Rewrite `h1` using `[← conj_apply, ← map_sub, val_smul_lt]`. Then use the resulting hypothesis.
-/
private theorem conj_ine {g τ : G F Ω} {A : ValuationSubring Ω} (h : τ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * τ * g ∈ Ine (F := F) A := by
  refine ⟨conj_dec h.1, fun x hx => ?_⟩
  have h1 := h.2 (g x) ((val_smul_le g A x).2 hx)
  rwa [← conj_apply, ← map_sub, val_smul_lt] at h1

/- English proof (translation)
Use `set v := A.valuation with hvdef`. Establish `hM0 : M ≠ 0`. Introduce and unpack `rfl`. Conclude with `hM (by simp)`. Establish `hvM : ¬ v (M : Ω) < 1`.

Introduce `hlt`. Apply `hM` to reduce the goal to its premises. Rewrite using `[← hA]`. Simplify using `using hlt`. Establish `hζ1 : v ζ = 1`.

Break down `lt_trichotomy (v ζ) 1 with h | h | h` into its components or cases. Establish `h2` using `pow_lt_one' h hM0`. Rewrite `h2` using `[← map_pow, hζ, map_one]`. Conclude with `absurd h2 (lt_irrefl 1)`. Conclude with `h`.

Establish `h2` using `one_lt_pow' h hM0`. Rewrite `h2` using `[← map_pow, hζ, map_one]`. Conclude with `absurd h2 (lt_irrefl 1)`. Establish `hζ0 : ζ ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at hζ1`. Establish `hsd : v (s ζ - ζ) < 1` using `hs.2 ζ hζ1.le`. Establish `hηM : (s ζ) ^ M = 1` using `by rw [← map_pow, hζ, map_one]`. Use `set η := s ζ with hη`. Use `set u := η * ζ⁻¹ with hu`.

Establish `huM : u ^ M = 1` using `by rw [hu, mul_pow, inv_pow, hηM, hζ, inv_one, mul_one]`. Establish `hu1 : v (u - 1) < 1`. Establish `e : u - 1 = (η - ζ) * ζ⁻¹` using `by rw [hu, sub_mul, mul_inv_cancel₀ hζ0]`. Rewrite using `[e, map_mul, map_inv₀, hζ1, inv_one, mul_one]`. Conclude with `hsd`.

Establish `hule : v u ≤ 1`. Establish `e : u = (u - 1) + 1` using `by ring`. Rewrite using `[e]`. Conclude with `(v.map_add _ _).trans (max_le hu1.le (by rw [map_one]))`. Assume the negation of the conclusion as `hne`.

Establish `hu_ne : u ≠ 1`. Introduce `h1`. Apply `hne` to reduce the goal to its premises. Establish `e : η = u * ζ` using `by rw [hu, mul_assoc, inv_mul_cancel₀ hζ0, mul_one]`. Rewrite using `[e, h1, one_mul]`.

Establish `hsum : ∑ i ∈ Finset.range M, u ^ i = 0`. Establish `h` using `geom_sum_mul u M`. Rewrite `h` using `[huM, sub_self]`. Conclude with `(mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hu_ne)`. Establish `hlt : v (∑ i ∈ Finset.range M, (u ^ i - 1)) < 1`.

Apply `Valuation.map_sum_lt v one_ne_zero` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[← geom_sum_mul u i, map_mul]`. Establish `hs1 : v (∑ j ∈ Finset.range i, u ^ j) ≤ 1` using `Valuation.map_sum_le v (fun j _ => by rw [map_pow]; exact pow_le_one' hule j)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite `hlt` using `[Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_range, zero_sub, Valuation.map_neg]`. Apply `hvM` to reduce the goal to its premises. Simplify using `using hlt`.
-/
private theorem ine_fix {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A w) {M : ℕ}
    (hM : ((M : ℕ) : 𝓞 F) ∉ w.asIdeal) {s : G F Ω} (hs : s ∈ Ine (F := F) A) (ζ : Ω) (hζ : ζ ^ M = 1) : s ζ = ζ := by
  set v := A.valuation with hvdef
  have hM0 : M ≠ 0 := by
    rintro rfl
    exact hM (by simp)
  have hvM : ¬ v (M : Ω) < 1 := by
    intro hlt
    apply hM
    rw [← hA]
    simpa using hlt
  have hζ1 : v ζ = 1 := by
    rcases lt_trichotomy (v ζ) 1 with h | h | h
    · have h2 := pow_lt_one' h hM0
      rw [← map_pow, hζ, map_one] at h2
      exact absurd h2 (lt_irrefl 1)
    · exact h
    · have h2 := one_lt_pow' h hM0
      rw [← map_pow, hζ, map_one] at h2
      exact absurd h2 (lt_irrefl 1)
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hζ1
  have hsd : v (s ζ - ζ) < 1 := hs.2 ζ hζ1.le
  have hηM : (s ζ) ^ M = 1 := by rw [← map_pow, hζ, map_one]
  set η := s ζ with hη
  set u := η * ζ⁻¹ with hu
  have huM : u ^ M = 1 := by rw [hu, mul_pow, inv_pow, hηM, hζ, inv_one, mul_one]
  have hu1 : v (u - 1) < 1 := by
    have e : u - 1 = (η - ζ) * ζ⁻¹ := by rw [hu, sub_mul, mul_inv_cancel₀ hζ0]
    rw [e, map_mul, map_inv₀, hζ1, inv_one, mul_one]
    exact hsd
  have hule : v u ≤ 1 := by
    have e : u = (u - 1) + 1 := by ring
    rw [e]
    exact (v.map_add _ _).trans (max_le hu1.le (by rw [map_one]))
  by_contra hne
  have hu_ne : u ≠ 1 := by
    intro h1
    apply hne
    have e : η = u * ζ := by rw [hu, mul_assoc, inv_mul_cancel₀ hζ0, mul_one]
    rw [e, h1, one_mul]
  have hsum : ∑ i ∈ Finset.range M, u ^ i = 0 := by
    have h := geom_sum_mul u M
    rw [huM, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hu_ne)
  have hlt : v (∑ i ∈ Finset.range M, (u ^ i - 1)) < 1 := by
    apply Valuation.map_sum_lt v one_ne_zero
    intro i _
    rw [← geom_sum_mul u i, map_mul]
    have hs1 : v (∑ j ∈ Finset.range i, u ^ j) ≤ 1 :=
      Valuation.map_sum_le v (fun j _ => by rw [map_pow]; exact pow_le_one' hule j)
    calc v (∑ j ∈ Finset.range i, u ^ j) * v (u - 1) ≤ 1 * v (u - 1) := by gcongr
      _ = v (u - 1) := one_mul _
      _ < 1 := hu1
  rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_range, zero_sub, Valuation.map_neg] at hlt
  apply hvM
  simpa using hlt

end

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l _ ι n r w`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `B B' hB hB'`. Take `⟨A, hA⟩` from `exists_isPlaceOver Ω w`. Take `⟨σ, hσ⟩` from `exists_isFrob hA`.

Establish `h1` using `(hB A hA).2 σ hσ`. Establish `h2` using `(hB' A hA).2 σ hσ`. Establish `h3` using `congrArg Polynomial.roots (h1.symm.trans h2)`. Simplify `h3` using `[Polynomial.roots_multiset_prod_X_sub_C]`. Introduce `M hlev hl hM`.

Take `⟨A0, hA0, χ, hχ, P, hP⟩` from `hlev w hl`. Establish `hI0 : ∀ t ∈ Ine (F` using `F) A0, r t = 1 := by`. Introduce `t ht`. Establish `hd` using `hP t ht`. Establish `hc : ∀ i, χ i t = 1` using `fun i => hχ i t (fun ζ hζ => ine_fix hA0 hM ht ζ hζ)`.

Simplify using `only [hc, Units.val_one, Matrix.diagonal_one] at hd`. Establish `hq : P * r t * P⁻¹ = 1` using `Units.ext hd`. Combine the equalities or inequalities in the displayed calculation. Take `⟨σ0, hσ0⟩` from `exists_isFrob hA0`. Use `⟨(Polynomial.map ι.toRingHom ((r σ0⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly).roots, ?_⟩` and prove the remaining obligations.

Introduce `A hA`. Take `⟨g, hg⟩` from `exists_smul_eq_of_isPlaceOver hA0 hA`. Substitute `hg` using the available equality. Use `⟨fun s hs => ?_, fun σ hσ => ?_⟩` and prove the remaining obligations. Establish `ht` using `hI0 _ (conj_ine hs)`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [map_mul, map_inv]`. Use `group`. Use `_ = 1 := by rw [ht]; simp`. Establish `hc` using `inv_mul_mem_Ine_of_isFrob hσ0 (conj_frob hσ)`.

Establish `he : r (g⁻¹ * σ * g) = r σ0`. Establish `h4` using `hI0 _ hc`. Rewrite `h4` using `[map_mul, map_inv]`. Conclude with `(inv_mul_eq_one.1 h4).symm`. Establish `hu : r σ⁻¹ = r g * r σ0⁻¹ * (r g)⁻¹`.

Rewrite using `[map_inv r σ0, ← he]`. Simplify using `only [map_mul, map_inv]`. Use `group`. Rewrite using `[hu, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]`. Conclude with `Polynomial.Splits.eq_prod_roots_of_monic (IsAlgClosed.splits _) ((Matrix.charpoly_monic _).map _)`.
-/
theorem UpperTheory.V.Br.frobEx :
    UpperTheory.V.Br.FrobEx := by
  intro F Ω _ _ _ _ _ l _ ι n r w
  refine ⟨?_, ?_⟩
  · intro B B' hB hB'
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨σ, hσ⟩ := exists_isFrob hA
    have h1 := (hB A hA).2 σ hσ
    have h2 := (hB' A hA).2 σ hσ
    have h3 := congrArg Polynomial.roots (h1.symm.trans h2)
    simpa [Polynomial.roots_multiset_prod_X_sub_C] using h3
  · intro M hlev hl hM
    obtain ⟨A0, hA0, χ, hχ, P, hP⟩ := hlev w hl
    have hI0 : ∀ t ∈ Ine (F := F) A0, r t = 1 := by
      intro t ht
      have hd := hP t ht
      have hc : ∀ i, χ i t = 1 := fun i => hχ i t (fun ζ hζ => ine_fix hA0 hM ht ζ hζ)
      simp only [hc, Units.val_one, Matrix.diagonal_one] at hd
      have hq : P * r t * P⁻¹ = 1 := Units.ext hd
      calc r t = P⁻¹ * (P * r t * P⁻¹) * P := by group
        _ = 1 := by rw [hq]; group
    obtain ⟨σ0, hσ0⟩ := exists_isFrob hA0
    refine ⟨(Polynomial.map ι.toRingHom
      ((r σ0⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly).roots, ?_⟩
    intro A hA
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver hA0 hA
    subst hg
    refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
    · have ht := hI0 _ (conj_ine hs)
      calc r s = r g * r (g⁻¹ * s * g) * r g⁻¹ := by
            simp only [map_mul, map_inv]
            group
        _ = 1 := by rw [ht]; simp
    · have hc := inv_mul_mem_Ine_of_isFrob hσ0 (conj_frob hσ)
      have he : r (g⁻¹ * σ * g) = r σ0 := by
        have h4 := hI0 _ hc
        rw [map_mul, map_inv] at h4
        exact (inv_mul_eq_one.1 h4).symm
      have hu : r σ⁻¹ = r g * r σ0⁻¹ * (r g)⁻¹ := by
        rw [map_inv r σ0, ← he]
        simp only [map_mul, map_inv]
        group
      rw [hu, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
      exact Polynomial.Splits.eq_prod_roots_of_monic (IsAlgClosed.splits _)
        ((Matrix.charpoly_monic _).map _)
