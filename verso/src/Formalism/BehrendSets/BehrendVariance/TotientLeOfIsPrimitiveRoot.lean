import Formalism.BehrendSets.StatementE

open Polynomial Module Matrix

namespace Formalism.BehrendSets.Stab

/- English proof (translation)
Establish `: CharZero K` using `charZero_of_injective_algebraMap (algebraMap E K).injective`. Establish `: IsScalarTower ℚ E K` using `IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)`. Establish `: FiniteDimensional ℚ K` using `Module.Finite.trans E K`. Rewrite using `[Module.finrank_mul_finrank ℚ E K]`. Establish `h1` using `minpoly.natDegree_le (A := ℚ) ζ`.

Rewrite `h1` using `[← cyclotomic_eq_minpoly_rat hζ hg, natDegree_cyclotomic]`. Conclude with `h1`.
-/
theorem totient_le_of_isPrimitiveRoot {E K : Type} [Field E] [NumberField E] [Field K] [Algebra E K]
    [FiniteDimensional E K] {g : ℕ} (hg : 0 < g) {ζ : K} (hζ : IsPrimitiveRoot ζ g) :
    Nat.totient g ≤ finrank ℚ E * finrank E K := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap E K).injective
  have : IsScalarTower ℚ E K := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  have : FiniteDimensional ℚ K := Module.Finite.trans E K
  rw [Module.finrank_mul_finrank ℚ E K]
  have h1 := minpoly.natDegree_le (A := ℚ) ζ
  rw [← cyclotomic_eq_minpoly_rat hζ hg, natDegree_cyclotomic] at h1
  exact h1

/- English proof (translation)
Use `Fact.mk hg` as an intermediate fact. Establish `hint : IsIntegral E M` using `IsIntegral.of_finite E M`. Establish `hμ0 : minpoly E M ≠ 0` using `minpoly.ne_zero hint`. Establish `hdvd : minpoly E M ∣ cyclotomic g E * (X - 1)`. Rewrite using `[cyclotomic_prime_mul_X_sub_one]`.

Apply `minpoly.dvd` to reduce the goal to its premises. Simplify using `[hM]`. Establish `hnc : ¬ IsCoprime (minpoly E M) (cyclotomic g E)`. Introduce `hc`. Establish `h1 : minpoly E M ∣ X - 1` using `hc.dvd_of_dvd_mul_left hdvd`.

Establish `h2` using `aeval_eq_zero_of_dvd_aeval_eq_zero h1 (minpoly.aeval E M)`. Apply `hM1` to reduce the goal to its premises. Simplify `h2` using `[sub_eq_zero]`. Choose the witnesses or unpack the hypotheses as in `⟨q, hq, hqμ, hqΦ⟩ : ∃ q, Irreducible q ∧ q ∣ minpoly E M ∧ q ∣ cyclotomic g E := by`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Conclude with `hnc (isCoprime_of_irreducible_dvd (fun h' => hμ0 h'.1) fun z hz h1 h2 => h z hz h1 h2)`. Establish `hq0 : q ≠ 0` using `hq.ne_zero`. Establish `hqdeg : q.natDegree ≤ k`. Combine the equalities or inequalities in the displayed calculation.

Establish `: Fact (Irreducible q)` using `⟨hq⟩`. Set `pb` to `AdjoinRoot.powerBasis hq0`. Establish `: FiniteDimensional E (AdjoinRoot q)` using `pb.finite`. Establish `hfin : finrank E (AdjoinRoot q) = q.natDegree`. Rewrite using `[pb.finrank, AdjoinRoot.powerBasis_dim]`.

Establish `hroot : aeval (AdjoinRoot.root q) (cyclotomic g E) = 0` using `aeval_eq_zero_of_dvd_aeval_eq_zero hqΦ (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])`. Establish `: CharZero (AdjoinRoot q)` using `charZero_of_injective_algebraMap (algebraMap E _).injective`. Establish `: NeZero (g : AdjoinRoot q)` using `⟨Nat.cast_ne_zero.mpr hg.ne_zero⟩`. Establish `hprim : IsPrimitiveRoot (AdjoinRoot.root q) g`. Rewrite using `[← isRoot_cyclotomic_iff, ← map_cyclotomic g (algebraMap E (AdjoinRoot q)), IsRoot, eval_map, ← aeval_def]`.

Conclude with `hroot`. Establish `h3` using `totient_le_of_isPrimitiveRoot (E := E) hg.pos hprim`. Rewrite `h3` using `[Nat.totient_prime hg, hfin]`. Conclude with `h3.trans (Nat.mul_le_mul_left _ hqdeg)`.
-/
theorem sub_one_le_of_pow_eq_one {E : Type} [Field E] [NumberField E] {k g : ℕ} (hg : g.Prime)
    (M : Matrix (Fin k) (Fin k) E) (hM : M ^ g = 1) (hM1 : M ≠ 1) :
    g - 1 ≤ finrank ℚ E * k := by
  have := Fact.mk hg
  have hint : IsIntegral E M := IsIntegral.of_finite E M
  have hμ0 : minpoly E M ≠ 0 := minpoly.ne_zero hint
  have hdvd : minpoly E M ∣ cyclotomic g E * (X - 1) := by
    rw [cyclotomic_prime_mul_X_sub_one]
    apply minpoly.dvd
    simp [hM]
  have hnc : ¬ IsCoprime (minpoly E M) (cyclotomic g E) := by
    intro hc
    have h1 : minpoly E M ∣ X - 1 := hc.dvd_of_dvd_mul_left hdvd
    have h2 := aeval_eq_zero_of_dvd_aeval_eq_zero h1 (minpoly.aeval E M)
    apply hM1
    simpa [sub_eq_zero] using h2
  obtain ⟨q, hq, hqμ, hqΦ⟩ : ∃ q, Irreducible q ∧ q ∣ minpoly E M ∧ q ∣ cyclotomic g E := by
    by_contra h
    push Not at h
    exact hnc (isCoprime_of_irreducible_dvd (fun h' => hμ0 h'.1) fun z hz h1 h2 => h z hz h1 h2)
  have hq0 : q ≠ 0 := hq.ne_zero
  have hqdeg : q.natDegree ≤ k := by
    calc q.natDegree ≤ (minpoly E M).natDegree := natDegree_le_of_dvd hqμ hμ0
      _ ≤ M.charpoly.natDegree :=
          natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly M) (Matrix.charpoly_monic M).ne_zero
      _ = k := by rw [Matrix.charpoly_natDegree_eq_dim]; simp
  have : Fact (Irreducible q) := ⟨hq⟩
  let pb := AdjoinRoot.powerBasis hq0
  have : FiniteDimensional E (AdjoinRoot q) := pb.finite
  have hfin : finrank E (AdjoinRoot q) = q.natDegree := by
    rw [pb.finrank, AdjoinRoot.powerBasis_dim]
  have hroot : aeval (AdjoinRoot.root q) (cyclotomic g E) = 0 :=
    aeval_eq_zero_of_dvd_aeval_eq_zero hqΦ (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])
  have : CharZero (AdjoinRoot q) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have : NeZero (g : AdjoinRoot q) := ⟨Nat.cast_ne_zero.mpr hg.ne_zero⟩
  have hprim : IsPrimitiveRoot (AdjoinRoot.root q) g := by
    rw [← isRoot_cyclotomic_iff, ← map_cyclotomic g (algebraMap E (AdjoinRoot q)), IsRoot,
      eval_map, ← aeval_def]
    exact hroot
  have h3 := totient_le_of_isPrimitiveRoot (E := E) hg.pos hprim
  rw [Nat.totient_prime hg, hfin] at h3
  exact h3.trans (Nat.mul_le_mul_left _ hqdeg)

end Formalism.BehrendSets.Stab

namespace Formalism.BehrendSets

/- English proof (translation)
Introduce `E _ _ k g hg hdeg Γ hfin hp`. Use `Fact.mk hg` as an intermediate fact. Assume the negation of the conclusion as `hne`. Establish `hcard : g ∣ Nat.card Γ`. Take `⟨n, hn⟩` from `(IsPGroup.iff_card).mp hp`.

Establish `hn0 : n ≠ 0`. Introduce and unpack `rfl`. Conclude with `hne (Subgroup.card_eq_one.mp (by simpa using hn))`. Rewrite using `[hn]`. Conclude with `dvd_pow_self g hn0`.

Take `⟨x, hx⟩` from `exists_prime_orderOf_dvd_card' g hcard`. Establish `hA : orderOf (x : GL (Fin k) E) = g` using `by rw [Subgroup.orderOf_coe]; exact hx`. Establish `hMg : ((x : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) ^ g = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, ← hA, pow_orderOf_eq_one, Units.val_one]`. Establish `hM1 : ((x : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) ≠ 1`.

Introduce `h`. Establish `h1 : (x : GL (Fin k) E) = 1` using `Units.ext h`. Rewrite `hA` using `[h1, orderOf_one]`. Conclude with `hg.one_lt.ne hA`. Use `Stab.sub_one_le_of_pow_eq_one hg _ hMg hM1` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem trivStab : TrivStab := by
  intro E _ _ k g hg hdeg Γ hfin hp
  have := Fact.mk hg
  by_contra hne
  have hcard : g ∣ Nat.card Γ := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hp
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.card_eq_one.mp (by simpa using hn))
    rw [hn]
    exact dvd_pow_self g hn0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' g hcard
  have hA : orderOf (x : GL (Fin k) E) = g := by rw [Subgroup.orderOf_coe]; exact hx
  have hMg : ((x : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) ^ g = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hA, pow_orderOf_eq_one, Units.val_one]
  have hM1 : ((x : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) ≠ 1 := by
    intro h
    have h1 : (x : GL (Fin k) E) = 1 := Units.ext h
    rw [h1, orderOf_one] at hA
    exact hg.one_lt.ne hA
  have := Stab.sub_one_le_of_pow_eq_one hg _ hMg hM1
  omega

end Formalism.BehrendSets
