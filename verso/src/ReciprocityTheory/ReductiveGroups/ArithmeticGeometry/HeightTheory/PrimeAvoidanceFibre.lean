import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SpanTopOfComplete

namespace ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre

open IsLocalRing

/- English proof (translation)
Use `haveI := hM.isPrime`. Use `set I : Ideal B := q ⊔ Ideal.span {w} with hI`. Establish `hfin` using `Ideal.finite_minimalPrimes_of_isNoetherianRing B I`. Establish `hprop : ∀ p ∈ I.minimalPrimes, p.IsPrime ∧ I ≤ p` using `fun p hp => hp.1`. Establish `hnot : ∀ p ∈ I.minimalPrimes, p ≠ M → ¬ p ≤ M`.

Introduce `p hp hne hle`. Take `⟨hpp, hIp⟩` from `hprop p hp`. Conclude with `hne (hchain p hpp (le_trans le_sup_left hIp) hle (hIp (Ideal.mem_sup_right (Ideal.mem_span_singleton_self w))))`. Establish `hex : ∀ p ∈ I.minimalPrimes, p ≠ M → ∃ x ∈ p, x ∉ M` using `fun p hp hne => SetLike.not_le_iff_exists.mp (hnot p hp hne)`. Set `f : Ideal B → B` to `fun p => if h : p ∈ I.minimalPrimes ∧ p ≠ M then (hex p h.1 h.2).choose else 1`.

Set `T` to `hfin.toFinset.filter (· ≠ M)`. Use `⟨∏ p ∈ T, f p, ?_, ?_⟩` and prove the remaining obligations. Introduce `hmem`. Take `⟨p, hpT, hpM⟩` from `Ideal.IsPrime.prod_mem_iff.mp hmem`. Simplify using `only [T, Finset.mem_filter, Set.Finite.mem_toFinset] at hpT`.

Establish `h1` using `(hex p hpT.1 hpT.2).choose_spec.2`. Simplify using `only [f, dif_pos hpT] at hpM`. Conclude with `h1 hpM`. Introduce `P hP hqP hwP hsP`. Establish `hIP : I ≤ P` using `sup_le hqP ((Ideal.span_singleton_le_iff_mem P).mpr hwP)`.

Take `⟨p, hp, hpP⟩` from `Ideal.exists_minimalPrimes_le hIP`. Distinguish the cases in `hpM : p = M`. Rewrite `hpP` using `[hpM]`. Conclude with `(hM.eq_of_le hP.ne_top hpP).symm`. It suffices to derive a contradiction.

Apply `hsP` to reduce the goal to its premises. Apply `Ideal.IsPrime.prod_mem_iff.mpr` to reduce the goal to its premises. Use `⟨p, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [T, Finset.mem_filter, Set.Finite.mem_toFinset]`. Conclude with `⟨hp, hpM⟩`.

Simplify using `only [f, dif_pos (And.intro hp hpM)]`. Conclude with `hpP (hex p hp hpM).choose_spec.1`.
-/
theorem avoid {B : Type*} [CommRing B] [IsNoetherianRing B] (M q : Ideal B) [hM : M.IsMaximal] (w : B)
    (hchain : ∀ P : Ideal B, P.IsPrime → q ≤ P → P ≤ M → w ∈ P → P = M) :
    ∃ s ∉ M, ∀ P : Ideal B, P.IsPrime → q ≤ P → w ∈ P → s ∉ P → P = M := by
  classical
  haveI := hM.isPrime
  set I : Ideal B := q ⊔ Ideal.span {w} with hI
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing B I
  have hprop : ∀ p ∈ I.minimalPrimes, p.IsPrime ∧ I ≤ p := fun p hp => hp.1
  have hnot : ∀ p ∈ I.minimalPrimes, p ≠ M → ¬ p ≤ M := by
    intro p hp hne hle
    obtain ⟨hpp, hIp⟩ := hprop p hp
    exact hne (hchain p hpp (le_trans le_sup_left hIp) hle
      (hIp (Ideal.mem_sup_right (Ideal.mem_span_singleton_self w))))
  have hex : ∀ p ∈ I.minimalPrimes, p ≠ M → ∃ x ∈ p, x ∉ M :=
    fun p hp hne => SetLike.not_le_iff_exists.mp (hnot p hp hne)
  let f : Ideal B → B := fun p =>
    if h : p ∈ I.minimalPrimes ∧ p ≠ M then (hex p h.1 h.2).choose else 1
  let T := hfin.toFinset.filter (· ≠ M)
  refine ⟨∏ p ∈ T, f p, ?_, ?_⟩
  · intro hmem
    obtain ⟨p, hpT, hpM⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    simp only [T, Finset.mem_filter, Set.Finite.mem_toFinset] at hpT
    have h1 := (hex p hpT.1 hpT.2).choose_spec.2
    simp only [f, dif_pos hpT] at hpM
    exact h1 hpM
  · intro P hP hqP hwP hsP
    have hIP : I ≤ P := sup_le hqP ((Ideal.span_singleton_le_iff_mem P).mpr hwP)
    obtain ⟨p, hp, hpP⟩ := Ideal.exists_minimalPrimes_le hIP
    by_cases hpM : p = M
    · rw [hpM] at hpP
      exact (hM.eq_of_le hP.ne_top hpP).symm
    · exfalso
      apply hsP
      apply Ideal.IsPrime.prod_mem_iff.mpr
      refine ⟨p, ?_, ?_⟩
      · simp only [T, Finset.mem_filter, Set.Finite.mem_toFinset]
        exact ⟨hp, hpM⟩
      · simp only [f, dif_pos (And.intro hp hpM)]
        exact hpP (hex p hp hpM).choose_spec.1

/- English proof (translation)
Use `set w := algebraMap O T ϖ with hw`. Use `set J : Ideal T := Ideal.span {w} with hJ`. Take `⟨P0, hP0, hwP0⟩` from `hex`. Establish `hJtop : J ≠ ⊤` using `fun h => hP0.ne_top (eq_top_iff.2 (h ▸ (Ideal.span_singleton_le_iff_mem P0).2 hwP0))`. Establish `hdim : Ring.KrullDimLE 0 (T ⧸ J)`.

Rewrite using `[Ring.krullDimLE_zero_iff]`. Introduce `I hI`. Take `⟨N, hN, hIN⟩` from `Ideal.exists_le_maximal I hI.ne_top`. Establish `hwI : w ∈ Ideal.comap (Ideal.Quotient.mk J) I`. Rewrite using `[Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self w)]`.

Conclude with `I.zero_mem`. Establish `hwN : w ∈ Ideal.comap (Ideal.Quotient.mk J) N` using `Ideal.comap_mono hIN hwI`. Establish `e` using `huniq _ _ (Ideal.comap_isPrime _ I) (Ideal.comap_isPrime _ N) hwI hwN`. Establish `: I = N`. Establish `h1` using `congrArg (Ideal.map (Ideal.Quotient.mk J)) e`.

Rewrite `h1` using `[Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]`. Then use the resulting hypothesis. Rewrite using `[this]`. Conclude with `hN`. Establish `hart : IsArtinianRing (T ⧸ J)` using `IsNoetherianRing.isArtinianRing_of_krullDimLE_zero`. Establish `hmJ : maximalIdeal O ≤ Ideal.comap (algebraMap O T) J`.

Rewrite using `[hϖ.maximalIdeal_eq, Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `Ideal.mem_span_singleton_self w`. Set `_ : Algebra (O ⧸ maximalIdeal O) (T ⧸ J)` to `Ideal.Quotient.algebraQuotientOfLEComap hmJ`. Establish `hmk : ∀ c : O, algebraMap (O ⧸ maximalIdeal O) (T ⧸ J) (Ideal.Quotient.mk _ c) = Ideal.Quotient.mk J (algebraMap O T c)` using `fun c => rfl`. Establish `: IsScalarTower O (O ⧸ maximalIdeal O) (T ⧸ J)` using `IsScalarTower.of_algebraMap_eq fun c => (hmk c).symm`.

Establish `: Algebra.FiniteType O (T ⧸ J)` using `Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ O J) Ideal.Quotient.mk_surjective`. Establish `: Algebra.FiniteType (O ⧸ maximalIdeal O) (T ⧸ J)` using `Algebra.FiniteType.of_restrictScalars_finiteType O _ _`. Establish `: IsJacobsonRing (O ⧸ maximalIdeal O)`. Set `_` to `Ideal.Quotient.field (maximalIdeal O)`. Use `infer_instance`.

Establish `: Module.Finite (O ⧸ maximalIdeal O) (T ⧸ J)` using `Module.finite_of_isArtinianRing _ _`. Take `⟨n, g, hg⟩` from `Module.Finite.exists_fin (R := O ⧸ maximalIdeal O) (M := T ⧸ J)`. Use `choose S hS using fun i => Ideal.Quotient.mk_surjective (g i)`. Establish `hgen : ∀ x : T, ∃ c : Fin n → O, ∃ y : T, x = ∑ i, c i • S i + ϖ • y`. Introduce `x`.

Establish `hx : Ideal.Quotient.mk J x ∈ Submodule.span (O ⧸ maximalIdeal O) (Set.range g)`. Rewrite using `[hg]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨cb, hcb⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 hx`. Use `choose c hc using fun i => Ideal.Quotient.mk_surjective (cb i)`.

Establish `hmem : x - ∑ i, c i • S i ∈ J`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum, ← hcb, sub_eq_zero]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← hc i, ← hS i, Algebra.smul_def, Algebra.smul_def, map_mul, hmk]`. Take `⟨y, hy⟩` from `Ideal.mem_span_singleton'.1 hmem`.

Use `⟨c, y, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, ← hw, mul_comm, hy]`. Normalize the expressions using the abelian group laws. Establish `hsep : ∀ x : T, (∀ k : ℕ, ∃ y : T, x = ϖ ^ k • y) → x = 0`. Introduce `x hx`.

Establish `h0` using `Ideal.iInf_pow_eq_bot_of_isDomain J hJtop`. Establish `: x ∈ ⨅ k : ℕ, J ^ k`. Rewrite using `[Ideal.mem_iInf]`. Introduce `k`. Take `⟨y, rfl⟩` from `hx k`.

Rewrite using `[hJ, Ideal.span_singleton_pow, Algebra.smul_def, map_pow, ← hw]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`. Rewrite `this` using `[h0]`. Conclude with `(Submodule.mem_bot T).1 this`. Establish `: IsAdicComplete (Ideal.span {ϖ}) O` using `hϖ.maximalIdeal_eq ▸ inferInstance`.

Establish `htop` using `SpanTopOfComplete.span_eq_top_of_complete ϖ hsep S hgen`. Conclude with `⟨Submodule.fg_def.2 ⟨Set.range S, Set.finite_range S, htop⟩⟩`.
-/
theorem finite_of_fibre {O T : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing T] [IsDomain T] [IsNoetherianRing T] [Algebra O T]
    [Algebra.FiniteType O T] (ϖ : O) (hϖ : Irreducible ϖ)
    (hex : ∃ P : Ideal T, P.IsPrime ∧ algebraMap O T ϖ ∈ P)
    (huniq : ∀ P P' : Ideal T, P.IsPrime → P'.IsPrime → algebraMap O T ϖ ∈ P → algebraMap O T ϖ ∈ P' →
      P = P') : Module.Finite O T := by
  classical
  set w := algebraMap O T ϖ with hw
  set J : Ideal T := Ideal.span {w} with hJ
  obtain ⟨P0, hP0, hwP0⟩ := hex
  have hJtop : J ≠ ⊤ := fun h => hP0.ne_top (eq_top_iff.2 (h ▸ (Ideal.span_singleton_le_iff_mem P0).2 hwP0))

  have hdim : Ring.KrullDimLE 0 (T ⧸ J) := by
    rw [Ring.krullDimLE_zero_iff]
    intro I hI
    obtain ⟨N, hN, hIN⟩ := Ideal.exists_le_maximal I hI.ne_top
    have hwI : w ∈ Ideal.comap (Ideal.Quotient.mk J) I := by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self w)]
      exact I.zero_mem
    have hwN : w ∈ Ideal.comap (Ideal.Quotient.mk J) N := Ideal.comap_mono hIN hwI
    have e := huniq _ _ (Ideal.comap_isPrime _ I) (Ideal.comap_isPrime _ N) hwI hwN
    have : I = N := by
      have h1 := congrArg (Ideal.map (Ideal.Quotient.mk J)) e
      rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective,
        Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h1
    rw [this]; exact hN
  have hart : IsArtinianRing (T ⧸ J) := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

  have hmJ : maximalIdeal O ≤ Ideal.comap (algebraMap O T) J := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_span_singleton_self w
  let _ : Algebra (O ⧸ maximalIdeal O) (T ⧸ J) := Ideal.Quotient.algebraQuotientOfLEComap hmJ
  have hmk : ∀ c : O, algebraMap (O ⧸ maximalIdeal O) (T ⧸ J) (Ideal.Quotient.mk _ c) =
      Ideal.Quotient.mk J (algebraMap O T c) := fun c => rfl
  have : IsScalarTower O (O ⧸ maximalIdeal O) (T ⧸ J) := IsScalarTower.of_algebraMap_eq fun c => (hmk c).symm
  have : Algebra.FiniteType O (T ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ O J) Ideal.Quotient.mk_surjective
  have : Algebra.FiniteType (O ⧸ maximalIdeal O) (T ⧸ J) :=
    Algebra.FiniteType.of_restrictScalars_finiteType O _ _
  have : IsJacobsonRing (O ⧸ maximalIdeal O) := by
    let _ := Ideal.Quotient.field (maximalIdeal O); infer_instance
  have : Module.Finite (O ⧸ maximalIdeal O) (T ⧸ J) := Module.finite_of_isArtinianRing _ _
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := O ⧸ maximalIdeal O) (M := T ⧸ J)
  choose S hS using fun i => Ideal.Quotient.mk_surjective (g i)
  have hgen : ∀ x : T, ∃ c : Fin n → O, ∃ y : T, x = ∑ i, c i • S i + ϖ • y := by
    intro x
    have hx : Ideal.Quotient.mk J x ∈ Submodule.span (O ⧸ maximalIdeal O) (Set.range g) := by
      rw [hg]; trivial
    obtain ⟨cb, hcb⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
    choose c hc using fun i => Ideal.Quotient.mk_surjective (cb i)
    have hmem : x - ∑ i, c i • S i ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum, ← hcb, sub_eq_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hc i, ← hS i, Algebra.smul_def, Algebra.smul_def, map_mul, hmk]
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨c, y, ?_⟩
    rw [Algebra.smul_def, ← hw, mul_comm, hy]
    abel
  have hsep : ∀ x : T, (∀ k : ℕ, ∃ y : T, x = ϖ ^ k • y) → x = 0 := by
    intro x hx
    have h0 := Ideal.iInf_pow_eq_bot_of_isDomain J hJtop
    have : x ∈ ⨅ k : ℕ, J ^ k := by
      rw [Ideal.mem_iInf]
      intro k
      obtain ⟨y, rfl⟩ := hx k
      rw [hJ, Ideal.span_singleton_pow, Algebra.smul_def, map_pow, ← hw]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [h0] at this
    exact (Submodule.mem_bot T).1 this
  have : IsAdicComplete (Ideal.span {ϖ}) O := hϖ.maximalIdeal_eq ▸ inferInstance
  have htop := SpanTopOfComplete.span_eq_top_of_complete ϖ hsep S hgen
  exact ⟨Submodule.fg_def.2 ⟨Set.range S, Set.finite_range S, htop⟩⟩

end ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre
