import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.MinorRtr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.MinorDeg

open Matrix UpperTheory.V.Weyl

/- English proof (translation)
Introduce `n ν hν H hH`. Establish `hmem : ∀ (h : ℕ) (hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty) (i : Fin n), i ∈ Finset.univ.filter (fun i : Fin n => h < ν i) ↔ i ≤ (Finset.univ.filter (fun i : Fin n => h < ν i)).max' hs`. Introduce `h hs i`. Prove the components needed by the constructor for the conclusion. Introduce `hi`.

Conclude with `Finset.le_max' _ _ hi`. Introduce `hi`. Establish `hm` using `Finset.max'_mem _ hs`. Rewrite `hm`, the goal using `[Finset.mem_filter]`. Conclude with `⟨Finset.mem_univ _, lt_of_lt_of_le hm.2 (hν hi)⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨g, hg1, hg2, hg3⟩ : ∃ g : ℕ → Pol n, (∀ h, g h ≠ 0) ∧ (∀ h, (g h).totalDegree ≤ n) ∧ ∀ b : Matrix (Fin n) (Fin n) ℂ, (∀ i j, j < i → b i j = 0) → ∀ h, rtr b (g h) = (∏ i ∈ Finset.univ.filter (fun i : Fin n => h < ν i), b i i) • g h := by`. Use `⟨fun h => if hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty then minor ((Finset.univ.filter (fun i : Fin n => h < ν i)).max' hs) else 1, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Distinguish the cases in `hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty`. Simplify using `only [dif_pos hs]`.

Conclude with `(minorDeg n _).1`. Simplify using `only [dif_neg hs]`. Conclude with `one_ne_zero`. Introduce `h`. Distinguish the cases in `hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty`.

Simplify using `only [dif_pos hs]`. Establish `h1` using `(minorDeg n ((Finset.univ.filter (fun i : Fin n => h < ν i)).max' hs)).2`. Establish `h2` using `((Finset.univ.filter (fun i : Fin n => h < ν i)).max' hs).isLt`. Use linear arithmetic over natural numbers and integers. Simplify using `only [dif_neg hs, MvPolynomial.totalDegree_one]`.

Conclude with `Nat.zero_le _`. Introduce `b hb h`. Distinguish the cases in `hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty`. Simplify using `only [dif_pos hs]`. Rewrite using `[minorRtr n _ b hb]`.

Use `congr 1`. Apply `Finset.prod_congr _ (fun _ _ => rfl)` to reduce the goal to its premises. Use extensionality with `i`. Rewrite using `[hmem h hs i, Finset.mem_filter]`. Simplify using the standard rewrite rules.

Simplify using `only [dif_neg hs]`. Rewrite using `[Finset.not_nonempty_iff_eq_empty.mp hs]`. Simplify using the standard rewrite rules. Use `⟨∏ h ∈ Finset.range H, g h, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Finset.prod_ne_zero_iff.mpr (fun h _ => hg1 h)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]`. Introduce `b hb`. Establish `key : ∏ h ∈ Finset.range H, ∏ i ∈ Finset.univ.filter (fun i : Fin n => h < ν i), b i i = ∏ k, b k k ^ ν k`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.prod_congr rfl (fun h _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.prod_filter]`. Use `_ = ∏ i, ∏ h ∈ Finset.range H, (if h < ν i then b i i else 1) := Finset.prod_comm`. Use `_ = ∏ k, b k k ^ ν k := by`. Use `Finset.prod_congr rfl (fun i _ => ?_)` and prove the remaining obligations.

Rewrite using `[Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]`. Use `congr 1`. Establish `hf : (Finset.range H).filter (fun h => h < ν i) = Finset.range (ν i)`. Use extensionality with `h`. Simplify using `only [Finset.mem_filter, Finset.mem_range]`.

Use `hH i` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[hf, Finset.card_range]`. Rewrite using `[map_prod, Finset.prod_congr rfl (fun h _ => hg3 b hb h), ← key]`. Simplify using `only [Algebra.smul_def, map_prod, Finset.prod_mul_distrib]`.
-/
theorem UpperTheory.V.Weyl.topPol :
    ∀ (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∀ H : ℕ, (∀ k, ν k ≤ H) → ∃ f : Pol n, f ≠ 0 ∧ f.totalDegree ≤ n * H ∧
      ∀ b : Matrix (Fin n) (Fin n) ℂ, (∀ i j, j < i → b i j = 0) → rtr b f = (∏ k, b k k ^ ν k) • f := by
  intro n ν hν H hH
  classical
  have hmem : ∀ (h : ℕ) (hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty) (i : Fin n),
      i ∈ Finset.univ.filter (fun i : Fin n => h < ν i) ↔ i ≤ (Finset.univ.filter (fun i : Fin n => h < ν i)).max' hs := by
    intro h hs i
    constructor
    · intro hi
      exact Finset.le_max' _ _ hi
    · intro hi
      have hm := Finset.max'_mem _ hs
      rw [Finset.mem_filter] at hm ⊢
      exact ⟨Finset.mem_univ _, lt_of_lt_of_le hm.2 (hν hi)⟩
  obtain ⟨g, hg1, hg2, hg3⟩ : ∃ g : ℕ → Pol n, (∀ h, g h ≠ 0) ∧ (∀ h, (g h).totalDegree ≤ n) ∧
      ∀ b : Matrix (Fin n) (Fin n) ℂ, (∀ i j, j < i → b i j = 0) → ∀ h,
        rtr b (g h) = (∏ i ∈ Finset.univ.filter (fun i : Fin n => h < ν i), b i i) • g h := by
    refine ⟨fun h => if hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty then
      minor ((Finset.univ.filter (fun i : Fin n => h < ν i)).max' hs) else 1, ?_, ?_, ?_⟩
    · intro h
      by_cases hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty
      · simp only [dif_pos hs]
        exact (minorDeg n _).1
      · simp only [dif_neg hs]
        exact one_ne_zero
    · intro h
      by_cases hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty
      · simp only [dif_pos hs]
        have h1 := (minorDeg n ((Finset.univ.filter (fun i : Fin n => h < ν i)).max' hs)).2
        have h2 := ((Finset.univ.filter (fun i : Fin n => h < ν i)).max' hs).isLt
        omega
      · simp only [dif_neg hs, MvPolynomial.totalDegree_one]
        exact Nat.zero_le _
    · intro b hb h
      by_cases hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty
      · simp only [dif_pos hs]
        rw [minorRtr n _ b hb]
        congr 1
        apply Finset.prod_congr _ (fun _ _ => rfl)
        ext i
        rw [hmem h hs i, Finset.mem_filter]
        simp
      · simp only [dif_neg hs]
        rw [Finset.not_nonempty_iff_eq_empty.mp hs]
        simp
  refine ⟨∏ h ∈ Finset.range H, g h, ?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr (fun h _ => hg1 h)
  · calc (∏ h ∈ Finset.range H, g h).totalDegree ≤ ∑ h ∈ Finset.range H, (g h).totalDegree :=
          MvPolynomial.totalDegree_finset_prod _ _
      _ ≤ ∑ h ∈ Finset.range H, n := Finset.sum_le_sum (fun h _ => hg2 h)
      _ = n * H := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]
  · intro b hb
    have key : ∏ h ∈ Finset.range H, ∏ i ∈ Finset.univ.filter (fun i : Fin n => h < ν i), b i i =
        ∏ k, b k k ^ ν k := by
      calc ∏ h ∈ Finset.range H, ∏ i ∈ Finset.univ.filter (fun i : Fin n => h < ν i), b i i
          = ∏ h ∈ Finset.range H, ∏ i, (if h < ν i then b i i else 1) := by
            refine Finset.prod_congr rfl (fun h _ => ?_)
            rw [Finset.prod_filter]
        _ = ∏ i, ∏ h ∈ Finset.range H, (if h < ν i then b i i else 1) := Finset.prod_comm
        _ = ∏ k, b k k ^ ν k := by
            refine Finset.prod_congr rfl (fun i _ => ?_)
            rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
            congr 1
            have hf : (Finset.range H).filter (fun h => h < ν i) = Finset.range (ν i) := by
              ext h
              simp only [Finset.mem_filter, Finset.mem_range]
              have := hH i
              omega
            rw [hf, Finset.card_range]
    rw [map_prod, Finset.prod_congr rfl (fun h _ => hg3 b hb h), ← key]
    simp only [Algebra.smul_def, map_prod, Finset.prod_mul_distrib]
