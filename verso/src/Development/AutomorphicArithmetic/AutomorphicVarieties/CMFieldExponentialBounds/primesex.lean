import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.StmtFields

open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

open Polynomial in
/- English proof (translation)
Use `set f : ℚ[X] := X ^ 2 + C (p : ℚ) with hf`. Establish `hdeg : f.natDegree = 2`. Rewrite using `[hf]`. Use `compute_degree!`. Establish `hmon : f.Monic`.

Rewrite using `[hf]`. Use `monicity!`. Establish `hpq : (0 : ℚ) < p` using `by exact_mod_cast hp`. Establish `hnoroot : ∀ x : ℚ, ¬ f.IsRoot x`. Introduce `x hx`.

Rewrite `hx` using `[hf]`. Simplify using `[Polynomial.IsRoot] at hx`. Use polynomial arithmetic with `[sq_nonneg x]`. Establish `hirr : Irreducible f` using `Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) hnoroot`. Establish `hspl` using `IsSplittingField.splits L f`.

Establish `hdeg0 : (f.map (algebraMap ℚ L)).degree ≠ 0`. Rewrite using `[Polynomial.degree_map, Polynomial.degree_eq_natDegree hmon.ne_zero, hdeg]`. Evaluate the decidable proposition. Take `⟨α, hα⟩` from `hspl.exists_eval_eq_zero hdeg0`. Establish `haeval : aeval α f = 0`.

Rewrite using `[aeval_def, ← eval_map]`. Conclude with `hα`. Establish `hmin : f = minpoly ℚ α` using `minpoly.eq_of_irreducible_of_monic hirr haeval hmon`. Establish `hint : IsIntegral ℚ α` using `⟨f, hmon, by rw [← aeval_def]; exact haeval⟩`. Establish `hfin : Module.finrank ℚ (IntermediateField.adjoin ℚ {α}) = 2`.

Rewrite using `[IntermediateField.adjoin.finrank hint, ← hmin, hdeg]`. Establish `htop : IntermediateField.adjoin ℚ {α} = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `y _`. Establish `hy : y ∈ Algebra.adjoin ℚ (f.rootSet L)`.

Rewrite using `[IsSplittingField.adjoin_rootSet L f]`. Discharge the goal by the elementary cases of `trivial`. Establish `hle : Algebra.adjoin ℚ (f.rootSet L) ≤ (IntermediateField.adjoin ℚ {α}).toSubalgebra`. Apply `Algebra.adjoin_le` to reduce the goal to its premises. Introduce `β hβ`.

Rewrite `hβ` using `[Polynomial.mem_rootSet]`. Establish `e1` using `hβ.2`. Establish `e2` using `haeval`. Rewrite `e1`, `e2` using `[hf]`. Simplify using `at e1 e2`.

Establish `: (β - α) * (β + α) = 0` using `by linear_combination e1 - e2`. Break down `mul_eq_zero.mp this with h | h` into its components or cases. Establish `hb : β = α` using `by linear_combination h`. Rewrite using `[hb]`. Conclude with `IntermediateField.mem_adjoin_simple_self ℚ α`.

Establish `hb : β = -α` using `by linear_combination h`. Rewrite using `[hb]`. Conclude with `neg_mem (IntermediateField.mem_adjoin_simple_self ℚ α)`. Conclude with `hle hy`. Rewrite using `[← IntermediateField.finrank_top', ← htop, hfin]`.
-/
private theorem finrank_quadratic_splitting_field (p : ℕ) (hp : 0 < p) (L : Type) [Field L] [Algebra ℚ L]
    [h : IsSplittingField ℚ L (X ^ 2 + C (p : ℚ) : ℚ[X])] : Module.finrank ℚ L = 2 := by
  set f : ℚ[X] := X ^ 2 + C (p : ℚ) with hf
  have hdeg : f.natDegree = 2 := by
    rw [hf]
    compute_degree!
  have hmon : f.Monic := by
    rw [hf]
    monicity!
  have hpq : (0 : ℚ) < p := by exact_mod_cast hp
  have hnoroot : ∀ x : ℚ, ¬ f.IsRoot x := by
    intro x hx
    rw [hf] at hx
    simp [Polynomial.IsRoot] at hx
    nlinarith [sq_nonneg x]
  have hirr : Irreducible f :=
    Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) hnoroot
  have hspl := IsSplittingField.splits L f
  have hdeg0 : (f.map (algebraMap ℚ L)).degree ≠ 0 := by
    rw [Polynomial.degree_map, Polynomial.degree_eq_natDegree hmon.ne_zero, hdeg]
    decide
  obtain ⟨α, hα⟩ := hspl.exists_eval_eq_zero hdeg0
  have haeval : aeval α f = 0 := by
    rw [aeval_def, ← eval_map]
    exact hα
  have hmin : f = minpoly ℚ α := minpoly.eq_of_irreducible_of_monic hirr haeval hmon
  have hint : IsIntegral ℚ α := ⟨f, hmon, by rw [← aeval_def]; exact haeval⟩
  have hfin : Module.finrank ℚ (IntermediateField.adjoin ℚ {α}) = 2 := by
    rw [IntermediateField.adjoin.finrank hint, ← hmin, hdeg]
  have htop : IntermediateField.adjoin ℚ {α} = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : y ∈ Algebra.adjoin ℚ (f.rootSet L) := by
      rw [IsSplittingField.adjoin_rootSet L f]
      trivial
    have hle : Algebra.adjoin ℚ (f.rootSet L) ≤ (IntermediateField.adjoin ℚ {α}).toSubalgebra := by
      apply Algebra.adjoin_le
      intro β hβ
      rw [Polynomial.mem_rootSet] at hβ
      have e1 := hβ.2
      have e2 := haeval
      rw [hf] at e1 e2
      simp at e1 e2
      have : (β - α) * (β + α) = 0 := by linear_combination e1 - e2
      rcases mul_eq_zero.mp this with h | h
      · have hb : β = α := by linear_combination h
        rw [hb]
        exact IntermediateField.mem_adjoin_simple_self ℚ α
      · have hb : β = -α := by linear_combination h
        rw [hb]
        exact neg_mem (IntermediateField.mem_adjoin_simple_self ℚ α)
    exact hle hy
  rw [← IntermediateField.finrank_top', ← htop, hfin]

open Polynomial in
/- English proof (translation)
Use `show Module.finrank ℚ (SplittingField (X ^ 2 + C (p : ℚ))) = 2`. Conclude with `@finrank_quadratic_splitting_field p hp _ _ _ (Polynomial.IsSplittingField.splittingField _)`.
-/
private theorem finrank_kstar (p : ℕ) (hp : 0 < p) : Module.finrank ℚ (Kstar p) = 2 := by
  show Module.finrank ℚ (SplittingField (X ^ 2 + C (p : ℚ))) = 2
  exact @finrank_quadratic_splitting_field p hp _ _ _ (Polynomial.IsSplittingField.splittingField _)

/- English proof (translation)
Introduce `ψ`. Establish `hN : ψ.N ≠ 0` using `NeZero.ne _`. Establish `hne1 : {p | Nat.Prime p ∧ p % 4 = 3 ∧ 7 ≤ p ∧ p.Coprime ψ.N}.Nonempty`. Take `⟨p, hpgt, hp, hpm⟩` from `Nat.forall_exists_prime_gt_and_eq_mod (q := 4) (a := 3) (by decide) (ψ.N + 7)`. Use `⟨p, hp, ?_, by omega, ?_⟩` and prove the remaining obligations.

Establish `h3 : ((p : ℕ) : ZMod 4) = ((3 : ℕ) : ZMod 4)` using `by simpa using hpm`. Rewrite `h3` using `[ZMod.natCast_eq_natCast_iff']`. Simplify using `using h3`. Rewrite using `[Nat.Prime.coprime_iff_not_dvd hp]`. Introduce `h`.

Use `Nat.le_of_dvd (Nat.pos_of_ne_zero hN) h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `h1 : (pK ψ).Prime ∧ pK ψ % 4 = 3 ∧ 7 ≤ pK ψ ∧ (pK ψ).Coprime ψ.N` using `Nat.sInf_mem hne1`. Establish `hord : ordC ψ ≠ 0` using `(orderOf_pos _).ne'`. Establish `hk : ordC ψ / 2 ^ (ordC ψ).factorization 2 ≠ 0` using `(Nat.ordCompl_pos 2 hord).ne'`.

Establish `hm : 0 < 2 * ψ.N * pK ψ`. Use `h1.1.pos` as an intermediate fact. Use `Nat.pos_of_ne_zero hN` as an intermediate fact. Check the signs of the components of the expression. Establish `hne2 : {p | Nat.Prime p ∧ p ≡ 1 [MOD ordC ψ / 2 ^ (ordC ψ).factorization 2] ∧ p.Coprime (2 * ψ.N * pK ψ)}.Nonempty`.

Take `⟨p, hp, hpgt, hpm⟩` from `Nat.exists_prime_gt_modEq_one (2 * ψ.N * pK ψ) hk`. Use `⟨p, hp, hpm, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.Prime.coprime_iff_not_dvd hp]`. Introduce `h`. Use `Nat.le_of_dvd hm h` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `h2` using `Nat.sInf_mem hne2`. Conclude with `⟨h1, h2, finrank_kstar _ h1.1.pos⟩`.
-/
theorem UpperTheory.V.pK_pOne_prime_conditions :
    ∀ ψ : PChar, ((pK ψ).Prime ∧ pK ψ % 4 = 3 ∧ 7 ≤ pK ψ ∧ (pK ψ).Coprime ψ.N) ∧
      ((pOne ψ).Prime ∧ pOne ψ ≡ 1 [MOD ordCompl[2] (ordC ψ)] ∧ (pOne ψ).Coprime (2 * ψ.N * pK ψ)) ∧ Module.finrank ℚ (Kstar (pK ψ)) = 2 := by
  intro ψ
  have hN : ψ.N ≠ 0 := NeZero.ne _
  have hne1 : {p | Nat.Prime p ∧ p % 4 = 3 ∧ 7 ≤ p ∧ p.Coprime ψ.N}.Nonempty := by
    obtain ⟨p, hpgt, hp, hpm⟩ :=
      Nat.forall_exists_prime_gt_and_eq_mod (q := 4) (a := 3) (by decide) (ψ.N + 7)
    refine ⟨p, hp, ?_, by omega, ?_⟩
    · have h3 : ((p : ℕ) : ZMod 4) = ((3 : ℕ) : ZMod 4) := by simpa using hpm
      rw [ZMod.natCast_eq_natCast_iff'] at h3
      simpa using h3
    · rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) h
      omega
  have h1 : (pK ψ).Prime ∧ pK ψ % 4 = 3 ∧ 7 ≤ pK ψ ∧ (pK ψ).Coprime ψ.N := Nat.sInf_mem hne1
  have hord : ordC ψ ≠ 0 := (orderOf_pos _).ne'
  have hk : ordC ψ / 2 ^ (ordC ψ).factorization 2 ≠ 0 := (Nat.ordCompl_pos 2 hord).ne'
  have hm : 0 < 2 * ψ.N * pK ψ := by
    have := h1.1.pos
    have := Nat.pos_of_ne_zero hN
    positivity
  have hne2 : {p | Nat.Prime p ∧ p ≡ 1 [MOD ordC ψ / 2 ^ (ordC ψ).factorization 2] ∧
      p.Coprime (2 * ψ.N * pK ψ)}.Nonempty := by
    obtain ⟨p, hp, hpgt, hpm⟩ := Nat.exists_prime_gt_modEq_one (2 * ψ.N * pK ψ) hk
    refine ⟨p, hp, hpm, ?_⟩
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    have := Nat.le_of_dvd hm h
    omega
  have h2 := Nat.sInf_mem hne2
  exact ⟨h1, h2, finrank_kstar _ h1.1.pos⟩
