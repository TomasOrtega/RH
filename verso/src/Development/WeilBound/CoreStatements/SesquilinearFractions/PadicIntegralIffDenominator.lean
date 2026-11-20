import Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsUnitValueSkewHermitian
import Development.WeilBound.CoreStatements.SesquilinearFractions.NIdeal
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FirstStatementF
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl Polynomial
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf

namespace UI

variable {p : Nat.Primes}

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.PadicComplexProdXSubCCoeffNorm.main s hs`.
-/
theorem coeff_prod_le (s : Multiset ℂ_[p]) (hs : ∀ r ∈ s, ‖r‖ ≤ 1) :
    ∀ i, ‖((s.map fun r => X - C r).prod).coeff i‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.PadicComplexProdXSubCCoeffNorm.main s hs

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap']`. Conclude with `Padic.norm_p_lt_one`.
-/
theorem norm_p_cp_lt : ‖((p : ℕ) : ℂ_[p])‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap']
  exact Padic.norm_p_lt_one

/- English proof (translation)
Take `⟨m, rfl⟩` from `hn`. Rewrite using `[Nat.cast_mul, norm_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ m)) norm_p_cp_lt`.
-/
theorem norm_nat_cp_lt (n : ℕ) (hn : (p : ℕ) ∣ n) : ‖(n : ℂ_[p])‖ < 1 := by
  obtain ⟨m, rfl⟩ := hn
  rw [Nat.cast_mul, norm_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ m)) norm_p_cp_lt

/- English proof (translation)
Break down `Int.natAbs_eq k with h | h` into its components or cases. Use `conv_lhs => rw [h]`. Rewrite using `[Int.cast_natCast]`. Use `conv_lhs => rw [h]`. Rewrite using `[Int.cast_neg, norm_neg, Int.cast_natCast]`.
-/
theorem norm_natAbs_cp (k : ℤ) : ‖(k : ℂ_[p])‖ = ‖(k.natAbs : ℂ_[p])‖ := by
  rcases Int.natAbs_eq k with h | h
  · conv_lhs => rw [h]
    rw [Int.cast_natCast]
  · conv_lhs => rw [h]
    rw [Int.cast_neg, norm_neg, Int.cast_natCast]

/- English proof (translation)
Introduce `hd`. Establish `hnum : ¬ (p : ℕ) ∣ c.num.natAbs` using `fun h1 => (Nat.Prime.coprime_iff_not_dvd p.2).mp (Nat.Coprime.coprime_dvd_left h1 c.reduced) hd`. Establish `hden : ‖((c.den : ℕ) : ℂ_[p])‖ < 1` using `norm_nat_cp_lt _ hd`. Establish `e : algebraMap ℚ ℂ_[p] c * ((c.den : ℕ) : ℂ_[p]) = (c.num : ℂ_[p])`. Use `congrArg (algebraMap ℚ ℂ_[p]) (Rat.mul_den_eq_num c)` as an intermediate fact.

Rewrite `this` using `[map_mul, map_natCast, map_intCast]`. Conclude with `this`. Establish `h2` using `congrArg norm e`. Rewrite `h2` using `[norm_mul, norm_natAbs_cp, LocGen.norm_natCast_cp p _ hnum]`. Establish `: ‖algebraMap ℚ ℂ_[p] c‖ * ‖((c.den : ℕ) : ℂ_[p])‖ < 1` using `lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hc) hden`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem not_dvd_den (c : ℚ) (hc : ‖algebraMap ℚ ℂ_[p] c‖ ≤ 1) : ¬ (p : ℕ) ∣ c.den := by
  intro hd
  have hnum : ¬ (p : ℕ) ∣ c.num.natAbs := fun h1 =>
    (Nat.Prime.coprime_iff_not_dvd p.2).mp (Nat.Coprime.coprime_dvd_left h1 c.reduced) hd
  have hden : ‖((c.den : ℕ) : ℂ_[p])‖ < 1 := norm_nat_cp_lt _ hd
  have e : algebraMap ℚ ℂ_[p] c * ((c.den : ℕ) : ℂ_[p]) = (c.num : ℂ_[p]) := by
    have := congrArg (algebraMap ℚ ℂ_[p]) (Rat.mul_den_eq_num c)
    rw [map_mul, map_natCast, map_intCast] at this
    exact this
  have h2 := congrArg norm e
  rw [norm_mul, norm_natAbs_cp, LocGen.norm_natCast_cp p _ hnum] at h2
  have : ‖algebraMap ℚ ℂ_[p] c‖ * ‖((c.den : ℕ) : ℂ_[p])‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hc) hden
  linarith

end UI

/- English proof (translation)
Introduce `E _ _ p x`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hint : IsIntegral ℚ x` using `Algebra.IsIntegral.isIntegral x`. Use `set q := minpoly ℚ x with hqdef`.

Establish `hq : q.Monic` using `minpoly.monic hint`. Establish `hA : ∀ i, ‖algebraMap ℚ ℂ_[p] (q.coeff i)‖ ≤ 1` using `by set Q := q.map (algebraMap ℚ ℂ_[p])`. Establish `hQs : Q.Splits` using `IsAlgClosed.splits Q`. Establish `hQm : Q.Monic` using `hq.map _`. Establish `hroots : ∀ r ∈ Q.roots, ‖r‖ ≤ 1`.

Introduce `r hr`. Establish `hr' : aeval r q = 0`. Rewrite using `[aeval_def, ← eval_map]`. Conclude with `(mem_roots hQm.ne_zero).mp hr`. Take `⟨φ, hφ⟩` from `IntermediateField.exists_algHom_of_splits_of_aeval (fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) hr'`.

Rewrite using `[← hφ]`. Conclude with `h φ.toRingHom`. Introduce `i`. Establish `e : Q.coeff i = algebraMap ℚ ℂ_[p] (q.coeff i)` using `coeff_map _ _`. Rewrite using `[← e, hQs.eq_prod_roots_of_monic hQm]`.

Conclude with `UI.coeff_prod_le _ hroots i`. Establish `hB : ∀ i, ¬ (p : ℕ) ∣ (q.coeff i).den` using `fun i => UI.not_dvd_den _ (hA i)`. Use `set N : ℕ := ∏ i ∈ Finset.range (q.natDegree + 1), (q.coeff i).den with hN`. Establish `hNp : ¬ (p : ℕ) ∣ N`. Rewrite using `[hN, Prime.dvd_finsetProd_iff (Nat.Prime.prime p.2)]`.

Introduce and unpack `⟨i, -, hi⟩`. Conclude with `hB i hi`. Establish `hN0 : (N : ℚ) ≠ 0`. Rewrite using `[hN]`. Use `push_cast`.

Conclude with `Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (q.coeff i).den_ne_zero`. Establish `hlift : C (N : ℚ) * q ∈ lifts (Int.castRingHom ℚ)`. Rewrite using `[lifts_iff_coeff_lifts]`. Introduce `i`. Rewrite using `[coeff_C_mul]`.

Distinguish the cases in `hi : i ≤ q.natDegree`. Establish `hdvd : (q.coeff i).den ∣ N` using `Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))`. Take `⟨k, hk⟩` from `hdvd`. Use `⟨k * (q.coeff i).num, ?_⟩` and prove the remaining obligations. Simplify using `only [eq_intCast, Int.cast_mul, Int.cast_natCast]`.

Rewrite using `[hk]`. Use `push_cast`. Rewrite using `[mul_comm ((q.coeff i).den : ℚ) (k : ℚ), mul_assoc, Rat.den_mul_eq_num]`. Rewrite using `[coeff_eq_zero_of_natDegree_lt (not_le.mp hi), mul_zero]`. Conclude with `⟨0, by simp⟩`.

Take `⟨P, hP0⟩` from `hlift`. Establish `hP : P.map (Int.castRingHom ℚ) = C (N : ℚ) * q` using `hP0`. Establish `hPlc : P.leadingCoeff = N`. Establish `h1` using `leadingCoeff_map_of_injective (Int.castRingHom ℚ).injective_int P`. Rewrite `h1` using `[hP, leadingCoeff_mul, leadingCoeff_C, hq.leadingCoeff, mul_one]`.

Establish `h2 : ((P.leadingCoeff : ℤ) : ℚ) = ((N : ℤ) : ℚ)`. Establish `h3 : (Int.castRingHom ℚ) P.leadingCoeff = ((N : ℕ) : ℚ)` using `h1.symm`. Rewrite `h3` using `[eq_intCast]`. Rewrite using `[h3]`. Use `push_cast`.

Both sides reduce to the same expression. Conclude with `h2` after adjusting the coercions. Establish `hPx : aeval x P = 0`. Rewrite using `[← aeval_map_algebraMap ℚ x P, algebraMap_int_eq, hP, map_mul, aeval_C, minpoly.aeval, mul_zero]`. Establish `hi : IsIntegral ℤ (P.leadingCoeff • x)` using `isIntegral_leadingCoeff_smul P x hPx`.

Rewrite `hi` using `[hPlc, natCast_zsmul]`. Use `⟨N, ⟨N • x, hi⟩, hNp, ?_⟩` and prove the remaining obligations. Simplify using `[nsmul_eq_mul]`. Introduce and unpack `⟨n, a, hn, h⟩ j`. Establish `h1` using `congrArg (fun z => ‖j z‖) h`.

Simplify using `only [map_mul, norm_mul, map_natCast] at h1`. Rewrite `h1` using `[LocGen.norm_natCast_cp p n hn, one_mul]`. Rewrite using `[h1]`. Conclude with `NI.norm_int_le (j.comp (algebraMap (𝓞 E) E)) a`.
-/
theorem padic_integral_iff_denominator : ∀ (E : Type) [Field E] [NumberField E] (p : Nat.Primes) (x : E), ((∀ j : E →+* ℂ_[p], ‖j x‖ ≤ 1) ↔ ∃ (n : ℕ) (a : 𝓞 E), ¬ (p : ℕ) ∣ n ∧ (n : E) * x = a) := by
  intro E _ _ p x
  constructor
  · intro h
    have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    set q := minpoly ℚ x with hqdef
    have hq : q.Monic := minpoly.monic hint

    have hA : ∀ i, ‖algebraMap ℚ ℂ_[p] (q.coeff i)‖ ≤ 1 := by
      set Q := q.map (algebraMap ℚ ℂ_[p])
      have hQs : Q.Splits := IsAlgClosed.splits Q
      have hQm : Q.Monic := hq.map _
      have hroots : ∀ r ∈ Q.roots, ‖r‖ ≤ 1 := by
        intro r hr
        have hr' : aeval r q = 0 := by
          rw [aeval_def, ← eval_map]
          exact (mem_roots hQm.ne_zero).mp hr
        obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits_of_aeval
          (fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) hr'
        rw [← hφ]
        exact h φ.toRingHom
      intro i
      have e : Q.coeff i = algebraMap ℚ ℂ_[p] (q.coeff i) := coeff_map _ _
      rw [← e, hQs.eq_prod_roots_of_monic hQm]
      exact UI.coeff_prod_le _ hroots i
    have hB : ∀ i, ¬ (p : ℕ) ∣ (q.coeff i).den := fun i => UI.not_dvd_den _ (hA i)
    set N : ℕ := ∏ i ∈ Finset.range (q.natDegree + 1), (q.coeff i).den with hN
    have hNp : ¬ (p : ℕ) ∣ N := by
      rw [hN, Prime.dvd_finsetProd_iff (Nat.Prime.prime p.2)]
      rintro ⟨i, -, hi⟩
      exact hB i hi
    have hN0 : (N : ℚ) ≠ 0 := by
      rw [hN]; push_cast
      exact Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (q.coeff i).den_ne_zero

    have hlift : C (N : ℚ) * q ∈ lifts (Int.castRingHom ℚ) := by
      rw [lifts_iff_coeff_lifts]
      intro i
      rw [coeff_C_mul]
      by_cases hi : i ≤ q.natDegree
      · have hdvd : (q.coeff i).den ∣ N := Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
        obtain ⟨k, hk⟩ := hdvd
        refine ⟨k * (q.coeff i).num, ?_⟩
        simp only [eq_intCast, Int.cast_mul, Int.cast_natCast]
        rw [hk]
        push_cast
        rw [mul_comm ((q.coeff i).den : ℚ) (k : ℚ), mul_assoc, Rat.den_mul_eq_num]
      · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp hi), mul_zero]
        exact ⟨0, by simp⟩
    obtain ⟨P, hP0⟩ := hlift
    have hP : P.map (Int.castRingHom ℚ) = C (N : ℚ) * q := hP0
    have hPlc : P.leadingCoeff = N := by
      have h1 := leadingCoeff_map_of_injective (Int.castRingHom ℚ).injective_int P
      rw [hP, leadingCoeff_mul, leadingCoeff_C, hq.leadingCoeff, mul_one] at h1
      have h2 : ((P.leadingCoeff : ℤ) : ℚ) = ((N : ℤ) : ℚ) := by
        have h3 : (Int.castRingHom ℚ) P.leadingCoeff = ((N : ℕ) : ℚ) := h1.symm
        rw [eq_intCast] at h3
        rw [h3]; push_cast; rfl
      exact_mod_cast h2
    have hPx : aeval x P = 0 := by
      rw [← aeval_map_algebraMap ℚ x P, algebraMap_int_eq, hP, map_mul, aeval_C, minpoly.aeval, mul_zero]
    have hi : IsIntegral ℤ (P.leadingCoeff • x) := isIntegral_leadingCoeff_smul P x hPx
    rw [hPlc, natCast_zsmul] at hi
    refine ⟨N, ⟨N • x, hi⟩, hNp, ?_⟩
    simp [nsmul_eq_mul]
  · rintro ⟨n, a, hn, h⟩ j
    have h1 := congrArg (fun z => ‖j z‖) h
    simp only [map_mul, norm_mul, map_natCast] at h1
    rw [LocGen.norm_natCast_cp p n hn, one_mul] at h1
    rw [h1]
    exact NI.norm_int_le (j.comp (algebraMap (𝓞 E) E)) a

end PositivityTheory.Xgf

end
