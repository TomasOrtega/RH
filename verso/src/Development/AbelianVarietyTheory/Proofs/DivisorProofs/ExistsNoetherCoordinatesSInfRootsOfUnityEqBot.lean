import Mathlib

namespace GlobalTheory

/- English proof (translation)
Establish `h : ∀ n : ℕ, ∃ z : K, IsPrimitiveRoot z (n + 1)` using `fun n => HasEnoughRootsOfUnity.exists_primitiveRoot K (n + 1)`. Use `choose f hf using h`. Use `Set.infinite_of_injective_forall_mem (f := f) ?_ ?_` and prove the remaining obligations. Introduce `a b hab`. Establish `h1` using `(hf a).eq_orderOf`.

Establish `h2` using `(hf b).eq_orderOf`. Rewrite `h1` using `[hab, ← h2]`. Use linear arithmetic over natural numbers and integers. Introduce `n`. Conclude with `⟨n + 1, Nat.succ_pos n, (hf n).pow_eq_one⟩`.
-/
theorem infinite_rootsOfUnity_of_isAlgClosed (K : Type) [Field K] [CharZero K] [IsAlgClosed K] :
    {z : K | ∃ n : ℕ, 0 < n ∧ z ^ n = 1}.Infinite := by
  have h : ∀ n : ℕ, ∃ z : K, IsPrimitiveRoot z (n + 1) := fun n =>
    HasEnoughRootsOfUnity.exists_primitiveRoot K (n + 1)
  choose f hf using h
  refine Set.infinite_of_injective_forall_mem (f := f) ?_ ?_
  · intro a b hab
    have h1 := (hf a).eq_orderOf
    have h2 := (hf b).eq_orderOf
    rw [hab, ← h2] at h1
    omega
  · intro n
    exact ⟨n + 1, Nat.succ_pos n, (hf n).pow_eq_one⟩

/- English proof (translation)
Set `K` to `AlgebraicClosure F`. Establish `hex : ∃ ζ : Fin d → K, (∀ j, ∃ n : ℕ, 0 < n ∧ ζ j ^ n = 1) ∧ MvPolynomial.aeval ζ a ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Apply `ha` to reduce the goal to its premises.

Apply `MvPolynomial.map_injective (algebraMap F K) (algebraMap F K).injective` to reduce the goal to its premises. Use `MvPolynomial.funext_set (fun _ => {z : K | ∃ n : ℕ, 0 < n ∧ z ^ n = 1}) (fun _ => infinite_rootsOfUnity_of_isAlgClosed K) ?_` and prove the remaining obligations. Introduce `x hx`. Use `hcon x (fun j => hx j (Set.mem_univ j))` as an intermediate fact. Rewrite using `[MvPolynomial.eval_map, ← MvPolynomial.aeval_def, this]`.

Simplify using the standard rewrite rules. Take `⟨ζ, hζ, hne⟩` from `hex`. Establish `hint : (MvPolynomial.aeval (R` using `F) ζ).toRingHom.IsIntegral := by`. Use `RingHom.IsIntegral.tower_top (algebraMap F (MvPolynomial (Fin d) F)) _ ?_` and prove the remaining obligations. Establish `: (MvPolynomial.aeval (R` using `F) ζ).toRingHom.comp (algebraMap F (MvPolynomial (Fin d) F)) = algebraMap F K := by`.

Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Introduce `x`. Conclude with `Algebra.IsIntegral.isIntegral (R := F) x`.

Use `⟨Ideal.comap (MvPolynomial.aeval (R := F) ζ).toRingHom ⊥, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `haveI : (⊥ : Ideal K).IsMaximal := Ideal.bot_isMaximal`. Conclude with `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ hint ⊥`. Simplify `hne` using `[Ideal.mem_comap]`. Introduce `j`.

Take `⟨n, hn, h⟩` from `hζ j`. Conclude with `⟨n, hn, by simp [Ideal.mem_comap, h]⟩`.
-/
theorem exists_maximal_rootsOfUnity_notMem (F : Type) [Field F] [CharZero F] (d : ℕ)
    (a : MvPolynomial (Fin d) F) (ha : a ≠ 0) :
    ∃ P : Ideal (MvPolynomial (Fin d) F), P.IsMaximal ∧ a ∉ P ∧
      ∀ j, ∃ n : ℕ, 0 < n ∧ (MvPolynomial.X j : MvPolynomial (Fin d) F) ^ n - 1 ∈ P := by
  let K := AlgebraicClosure F
  have hex : ∃ ζ : Fin d → K, (∀ j, ∃ n : ℕ, 0 < n ∧ ζ j ^ n = 1) ∧
      MvPolynomial.aeval ζ a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply ha
    apply MvPolynomial.map_injective (algebraMap F K) (algebraMap F K).injective
    refine MvPolynomial.funext_set (fun _ => {z : K | ∃ n : ℕ, 0 < n ∧ z ^ n = 1})
      (fun _ => infinite_rootsOfUnity_of_isAlgClosed K) ?_
    intro x hx
    have := hcon x (fun j => hx j (Set.mem_univ j))
    rw [MvPolynomial.eval_map, ← MvPolynomial.aeval_def, this]
    simp
  obtain ⟨ζ, hζ, hne⟩ := hex
  have hint : (MvPolynomial.aeval (R := F) ζ).toRingHom.IsIntegral := by
    refine RingHom.IsIntegral.tower_top (algebraMap F (MvPolynomial (Fin d) F)) _ ?_
    have : (MvPolynomial.aeval (R := F) ζ).toRingHom.comp (algebraMap F (MvPolynomial (Fin d) F))
        = algebraMap F K := by
      ext x
      simp
    rw [this]
    intro x
    exact Algebra.IsIntegral.isIntegral (R := F) x
  refine ⟨Ideal.comap (MvPolynomial.aeval (R := F) ζ).toRingHom ⊥, ?_, ?_, ?_⟩
  · haveI : (⊥ : Ideal K).IsMaximal := Ideal.bot_isMaximal
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ hint ⊥
  · simpa [Ideal.mem_comap] using hne
  · intro j
    obtain ⟨n, hn, h⟩ := hζ j
    exact ⟨n, hn, by simp [Ideal.mem_comap, h]⟩

/- English proof (translation)
Introduce `F R _ _ _ _ _ _`. Take `⟨d, g, hinj, hint⟩` from `exists_integral_inj_algHom_of_fg F R`. Establish `hg : MvPolynomial.aeval (fun j => g (MvPolynomial.X j)) = g`. Use extensionality with `j`. Simplify using the standard rewrite rules.

Use `⟨d, fun j => g (MvPolynomial.X j), ?_, ?_⟩` and prove the remaining obligations. Introduce `r`. Rewrite using `[hg]`. Conclude with `hint r`. Use `letI : Algebra (MvPolynomial (Fin d) F) R := g.toRingHom.toAlgebra haveI : Algebra.IsIntegral (MvPolynomial (Fin d) F) R := ⟨fun r => hint r⟩`.

Apply `Ideal.eq_bot_of_comap_eq_bot (R := MvPolynomial (Fin d) F)` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`. Introduce `a haI`. Rewrite using `[Ideal.mem_bot]`. Assume the negation of the conclusion as `ha`.

Take `⟨P, hP, haP, hX⟩` from `exists_maximal_rootsOfUnity_notMem F d a ha`. Establish `hker : RingHom.ker (algebraMap (MvPolynomial (Fin d) F) R) ≤ P`. Introduce `x hx`. Establish `: x = 0` using `hinj (by rw [map_zero]; exact hx)`. Rewrite using `[this]`.

Conclude with `P.zero_mem`. Take `⟨Q, hQ, hQP⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := R) P hker`. Apply `haP` to reduce the goal to its premises. Rewrite using `[← hQP]`. Rewrite `haI`, the goal using `[Ideal.mem_comap]`.

Use `Submodule.mem_sInf.1 haI Q ⟨hQ, fun j => ?_⟩` and prove the remaining obligations. Take `⟨n, hn, h⟩` from `hX j`. Use `⟨n, hn, ?_⟩` and prove the remaining obligations. Rewrite `h` using `[← hQP, Ideal.mem_comap, map_sub, map_pow, map_one]`. Conclude with `h`.
-/
theorem exists_noether_coordinates_sInf_rootsOfUnity_eq_bot :
    ∀ (F R : Type) [Field F] [CharZero F] [CommRing R] [IsDomain R] [Algebra F R]
      [Algebra.FiniteType F R],
    ∃ (d : ℕ) (t : Fin d → R),
      (∀ r : R, ∃ p : Polynomial (MvPolynomial (Fin d) F), p.Monic ∧
        p.eval₂ (MvPolynomial.aeval t).toRingHom r = 0) ∧
      sInf {m : Ideal R | m.IsMaximal ∧ ∀ j, ∃ n : ℕ, 0 < n ∧ t j ^ n - 1 ∈ m} = ⊥ := by
  intro F R _ _ _ _ _ _
  obtain ⟨d, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg F R
  have hg : MvPolynomial.aeval (fun j => g (MvPolynomial.X j)) = g := by
    ext j
    simp
  refine ⟨d, fun j => g (MvPolynomial.X j), ?_, ?_⟩
  · intro r
    rw [hg]
    exact hint r
  · letI : Algebra (MvPolynomial (Fin d) F) R := g.toRingHom.toAlgebra
    haveI : Algebra.IsIntegral (MvPolynomial (Fin d) F) R := ⟨fun r => hint r⟩
    apply Ideal.eq_bot_of_comap_eq_bot (R := MvPolynomial (Fin d) F)
    rw [eq_bot_iff]
    intro a haI
    rw [Ideal.mem_bot]
    by_contra ha
    obtain ⟨P, hP, haP, hX⟩ := exists_maximal_rootsOfUnity_notMem F d a ha
    have hker : RingHom.ker (algebraMap (MvPolynomial (Fin d) F) R) ≤ P := by
      intro x hx
      have : x = 0 := hinj (by rw [map_zero]; exact hx)
      rw [this]
      exact P.zero_mem
    obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := R) P hker
    apply haP
    rw [← hQP]
    rw [Ideal.mem_comap] at haI ⊢
    refine Submodule.mem_sInf.1 haI Q ⟨hQ, fun j => ?_⟩
    obtain ⟨n, hn, h⟩ := hX j
    refine ⟨n, hn, ?_⟩
    rw [← hQP, Ideal.mem_comap, map_sub, map_pow, map_one] at h
    exact h

end GlobalTheory
