import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.Detint
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Sumval

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

/- English proof (translation)
Take `⟨e, n', hn', he⟩` from `Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hX) l hl.out.one_lt.ne'`. Establish `hn0 : n' ≠ 0`. Introduce and unpack `rfl`. Conclude with `hn' (dvd_zero l)`. Use `⟨e, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[he]`. Conclude with `Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hn0)`. Establish `hu : IsUnit ((n' : ℤ) : ℤ_[l])`. Rewrite using `[PadicInt.isUnit_iff]`. Use `le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hn' ?_)` and prove the remaining obligations.

Conclude with `(PadicInt.norm_int_lt_one_iff_dvd _).mp h` after adjusting the coercions. Rewrite `hu` using `[Int.cast_natCast]`. Establish `h1 : (X : ℤ_[l]) ∣ ((X.natAbs : ℤ) : ℤ_[l])` using `map_dvd (Int.castRingHom ℤ_[l]) (Int.dvd_natAbs.mpr dvd_rfl)`. Use `h1.trans ?_` and prove the remaining obligations. Rewrite using `[he]`.

Use `push_cast`. Conclude with `hu.mul_right_dvd.mpr dvd_rfl`.
-/
private theorem int_dvd_pow (l : ℕ) [hl : Fact l.Prime] (X : ℤ) (hX : X ≠ 0) :
    ∃ r : ℕ, l ^ r ≤ X.natAbs ∧ (X : ℤ_[l]) ∣ (l : ℤ_[l]) ^ r := by
  obtain ⟨e, n', hn', he⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hX) l hl.out.one_lt.ne'
  have hn0 : n' ≠ 0 := by
    rintro rfl
    exact hn' (dvd_zero l)
  refine ⟨e, ?_, ?_⟩
  · rw [he]
    exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hn0)
  · have hu : IsUnit ((n' : ℤ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hn' ?_)
      exact_mod_cast (PadicInt.norm_int_lt_one_iff_dvd _).mp h
    rw [Int.cast_natCast] at hu
    have h1 : (X : ℤ_[l]) ∣ ((X.natAbs : ℤ) : ℤ_[l]) :=
      map_dvd (Int.castRingHom ℤ_[l]) (Int.dvd_natAbs.mpr dvd_rfl)
    refine h1.trans ?_
    rw [he]
    push_cast
    exact hu.mul_right_dvd.mpr dvd_rfl

/- English proof (translation)
Introduce `l _ Γ _ _ N _ φ e a ha hs hφ he ha1 z hz`. Take `⟨X, hX0, hXb, hXe⟩` from `higherStickelberger_det_exists_int_bounded φ a ha (e + 1) ha1 (by omega) hφ`. Take `⟨r, hr1, hr2⟩` from `int_dvd_pow l X hX0`. Use `⟨r, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : ((l : ℝ) ^ r) ≤ (bdX N a (e + 1) : ℝ) ^ (Nat.card Γ / 2)`.

Conclude with `hr1.trans hXb` after adjusting the coercions. Establish `hl0 : (0 : ℝ) < (l : ℝ) ^ r`. Use `(Fact.out : l.Prime).pos` as an intermediate fact. Check the signs of the components of the expression. Establish `h2` using `Real.log_le_log hl0 h1`.

Rewrite `h2` using `[Real.log_pow, Real.log_pow]`. Establish `h3 : ((Nat.card Γ / 2 : ℕ) : ℝ) ≤ (Nat.card Γ : ℝ)`. Conclude with `Nat.div_le_self _ _` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation. Use `dvd_trans ?_ hr2` and prove the remaining obligations.

Establish `hmap : MonoidAlgebra.mapRingHom Γ PadicInt.Coe.ringHom z = MonoidAlgebra.mapRingHom Γ (Rat.castHom ℚ_[l]) (yEl (e + 1) a ha φ)`. Use extensionality with `g`. Establish `h` using `hz g`. Simplify using the standard rewrite rules. Conclude with `h`.

Establish `hd` using `congrArg (detR (φ (-1)) ((-1) ^ (e + 1))) hmap`. Rewrite `hd` using `[detR_map, detR_map]`. Establish `hq` using `congrArg (Rat.castHom ℚ_[l]) hXe`. Rewrite `hq` using `[map_mul, map_pow, ← hd]`. Establish `hX'' : (X : ℤ_[l]) = (denY N (e + 1) : ℤ_[l]) ^ (Nat.card Γ / 2) * detR (φ (-1)) ((-1) ^ (e + 1)) z`.

Apply `PadicInt.ext` to reduce the goal to its premises. Use `push_cast`. Simplify using `at hq`. Conclude with `hq`. Rewrite using `[hX'']`.

Conclude with `dvd_mul_left _ _`.
-/
theorem UpperTheory.V.Odd.detVal :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [CommGroup Γ] [Finite Γ] (N : ℕ) [NeZero N] (φ : (ZMod N)ˣ →* Γ) (e a : ℕ) (ha : a.Coprime N), Function.Surjective φ → φ (-1) ≠ 1 → 1 ≤ e → 1 < a → ∀ z : MonoidAlgebra ℤ_[l] Γ, IsInt l z (yEl (e + 1) a ha φ) → ∃ r : ℕ, (r : ℝ) * Real.log l ≤ Nat.card Γ * Real.log (bdX N a (e + 1)) ∧ detR (φ (-1)) ((-1) ^ (e + 1)) z ∣ (l : ℤ_[l]) ^ r := by
  intro l _ Γ _ _ N _ φ e a ha hs hφ he ha1 z hz
  obtain ⟨X, hX0, hXb, hXe⟩ := higherStickelberger_det_exists_int_bounded φ a ha (e + 1) ha1 (by omega) hφ
  obtain ⟨r, hr1, hr2⟩ := int_dvd_pow l X hX0
  refine ⟨r, ?_, ?_⟩
  · have h1 : ((l : ℝ) ^ r) ≤ (bdX N a (e + 1) : ℝ) ^ (Nat.card Γ / 2) := by
      exact_mod_cast hr1.trans hXb
    have hl0 : (0 : ℝ) < (l : ℝ) ^ r := by
      have := (Fact.out : l.Prime).pos
      positivity
    have h2 := Real.log_le_log hl0 h1
    rw [Real.log_pow, Real.log_pow] at h2
    have h3 : ((Nat.card Γ / 2 : ℕ) : ℝ) ≤ (Nat.card Γ : ℝ) := by
      exact_mod_cast Nat.div_le_self _ _
    calc (r : ℝ) * Real.log l ≤ ((Nat.card Γ / 2 : ℕ) : ℝ) * Real.log (bdX N a (e + 1)) := h2
      _ ≤ Nat.card Γ * Real.log (bdX N a (e + 1)) :=
        mul_le_mul_of_nonneg_right h3 (Real.log_natCast_nonneg _)
  · refine dvd_trans ?_ hr2
    have hmap : MonoidAlgebra.mapRingHom Γ PadicInt.Coe.ringHom z =
        MonoidAlgebra.mapRingHom Γ (Rat.castHom ℚ_[l]) (yEl (e + 1) a ha φ) := by
      ext g
      have h := hz g
      simp
      exact h
    have hd := congrArg (detR (φ (-1)) ((-1) ^ (e + 1))) hmap
    rw [detR_map, detR_map] at hd
    have hq := congrArg (Rat.castHom ℚ_[l]) hXe
    rw [map_mul, map_pow, ← hd] at hq
    have hX'' : (X : ℤ_[l]) =
        (denY N (e + 1) : ℤ_[l]) ^ (Nat.card Γ / 2) * detR (φ (-1)) ((-1) ^ (e + 1)) z := by
      apply PadicInt.ext
      push_cast
      simp at hq
      exact hq
    rw [hX'']
    exact dvd_mul_left _ _
