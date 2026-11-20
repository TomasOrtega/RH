import Mathlib

open IsLocalRing

/- English proof (translation)
Introduce `O Ω _ _ _ _ _ _ _ hO ϖ hϖ hlt S hS E hE hdig`. Establish `hI : maximalIdeal O = Ideal.span {ϖ}` using `hϖ.maximalIdeal_eq`. Establish `hhaus : IsHausdorff (maximalIdeal O) S`. Use `⟨fun x hx => ?_⟩` and prove the remaining obligations. Establish `hb : ∀ n : ℕ, ‖(x : Ω)‖ ≤ ‖algebraMap O Ω ϖ‖ ^ n`.

Introduce `n`. Establish `h` using `hx n`. Rewrite `h` using `[SModEq.zero, hI, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]`. Take `⟨t, -, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h`. Establish `: (((ϖ ^ n) • t : S) : Ω) = algebraMap O Ω ϖ ^ n * (t : Ω)`.

Simplify using `[Algebra.smul_def]`. Rewrite using `[this, norm_mul, norm_pow]`. Conclude with `mul_le_of_le_one_right (by positivity) (hS _ t.2)`. Establish `hlim : Filter.Tendsto (fun n : ℕ => ‖algebraMap O Ω ϖ‖ ^ n) Filter.atTop (nhds 0)` using `tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hlt`. Establish `h0 : ‖(x : Ω)‖ ≤ 0` using `ge_of_tendsto' hlim hb`.

Conclude with `Subtype.ext (norm_le_zero_iff.1 h0)`. Establish `hpre : IsPrecomplete (maximalIdeal O) (E → O)`. Use `⟨fun g hg => ?_⟩` and prove the remaining obligations. Establish `hcoord : ∀ {m : ℕ} (x : E → O), x ∈ (maximalIdeal O ^ m • ⊤ : Submodule O (E → O)) → ∀ i, x i ∈ maximalIdeal O ^ m`. Introduce `m x hx i`.

Establish `h` using `Submodule.mem_map_of_mem (f := (LinearMap.proj i : (E → O) →ₗ[O] O)) hx`. Rewrite `h` using `[Submodule.map_smul'']`. Establish `h2 : x i ∈ (maximalIdeal O ^ m • ⊤ : Submodule O O)` using `Submodule.smul_mono le_rfl le_top h`. Simplify using `using h2`. Establish `hc : ∀ i : E, ∃ L : O, ∀ n, g n i ≡ L [SMOD (maximalIdeal O ^ n • ⊤ : Submodule O O)]`.

Introduce `i`. Use `IsPrecomplete.prec (I := maximalIdeal O) (M := O) inferInstance (f := fun n => g n i) ?_` and prove the remaining obligations. Introduce `m n hmn`. Establish `h` using `(SModEq.sub_mem.1 (hg hmn))`. Use `SModEq.sub_mem.2 ?_` and prove the remaining obligations.

Establish `h2` using `hcoord _ h i`. Simplify using `using h2`. Use `choose L hL using hc`. Use `⟨L, fun n => ?_⟩` and prove the remaining obligations. Use `SModEq.sub_mem.2 ?_` and prove the remaining obligations.

Establish `hsum : g n - L = ∑ i : E, (g n i - L i) • (Pi.single i 1 : E → O)`. Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[hsum]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ trivial` and prove the remaining obligations.

Establish `h` using `SModEq.sub_mem.1 (hL i n)`. Simplify using `using h`. Set `v : E → S` to `fun e => ⟨e, hE e e.2⟩`. Set `f : (E → O) →ₗ[O] S` to `Fintype.linearCombination O v`. Establish `hsurj : Function.Surjective f`.

Use `surjective_of_mkQ_comp_surjective (I := maximalIdeal O) ?_` and prove the remaining obligations. Introduce `y`. Take `⟨s, rfl⟩` from `Submodule.mkQ_surjective _ y`. Take `⟨e, he, s', hs', hs⟩` from `hdig s s.2`. Use `⟨Pi.single ⟨e, he⟩ 1, ?_⟩` and prove the remaining obligations.

Establish `hf : f (Pi.single ⟨e, he⟩ 1) = ⟨e, hE e he⟩`. Simplify using `[f, v, Fintype.linearCombination_apply_single]`. Simplify using `only [LinearMap.comp_apply, hf]`. Rewrite using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hI, Submodule.ideal_span_singleton_smul]`. Use `(Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨-⟨s', hs'⟩, trivial, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[hs]`. Conclude with `Module.Finite.of_surjective f hsurj`.
-/
theorem UpperTheory.digit_expansion_lattice :
    ∀ {O Ω : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [NormedField Ω] [IsUltrametricDist Ω] [Algebra O Ω]
        (hO : ∀ a : O, ‖algebraMap O Ω a‖ ≤ 1) (ϖ : O) (hϖ : Irreducible ϖ) (hlt : ‖algebraMap O Ω ϖ‖ < 1)
        (S : Submodule O Ω) (hS : ∀ s ∈ S, ‖s‖ ≤ 1) (E : Finset Ω) (hE : ∀ e ∈ E, e ∈ S)
        (hdig : ∀ s ∈ S, ∃ e ∈ E, ∃ s' ∈ S, s = e + ϖ • s'),
        Module.Finite O S := by
  intro O Ω _ _ _ _ _ _ _ hO ϖ hϖ hlt S hS E hE hdig
  classical
  have hI : maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hhaus : IsHausdorff (maximalIdeal O) S := by
    refine ⟨fun x hx => ?_⟩
    have hb : ∀ n : ℕ, ‖(x : Ω)‖ ≤ ‖algebraMap O Ω ϖ‖ ^ n := by
      intro n
      have h := hx n
      rw [SModEq.zero, hI, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul] at h
      obtain ⟨t, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h
      have : (((ϖ ^ n) • t : S) : Ω) = algebraMap O Ω ϖ ^ n * (t : Ω) := by
        simp [Algebra.smul_def]
      rw [this, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (by positivity) (hS _ t.2)
    have hlim : Filter.Tendsto (fun n : ℕ => ‖algebraMap O Ω ϖ‖ ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hlt
    have h0 : ‖(x : Ω)‖ ≤ 0 := ge_of_tendsto' hlim hb
    exact Subtype.ext (norm_le_zero_iff.1 h0)
  have hpre : IsPrecomplete (maximalIdeal O) (E → O) := by
    refine ⟨fun g hg => ?_⟩
    have hcoord : ∀ {m : ℕ} (x : E → O),
        x ∈ (maximalIdeal O ^ m • ⊤ : Submodule O (E → O)) → ∀ i, x i ∈ maximalIdeal O ^ m := by
      intro m x hx i
      have h := Submodule.mem_map_of_mem (f := (LinearMap.proj i : (E → O) →ₗ[O] O)) hx
      rw [Submodule.map_smul''] at h
      have h2 : x i ∈ (maximalIdeal O ^ m • ⊤ : Submodule O O) :=
        Submodule.smul_mono le_rfl le_top h
      simpa using h2
    have hc : ∀ i : E, ∃ L : O, ∀ n, g n i ≡ L [SMOD (maximalIdeal O ^ n • ⊤ : Submodule O O)] := by
      intro i
      refine IsPrecomplete.prec (I := maximalIdeal O) (M := O) inferInstance (f := fun n => g n i) ?_
      intro m n hmn
      have h := (SModEq.sub_mem.1 (hg hmn))
      refine SModEq.sub_mem.2 ?_
      have h2 := hcoord _ h i
      simpa using h2
    choose L hL using hc
    refine ⟨L, fun n => ?_⟩
    refine SModEq.sub_mem.2 ?_
    have hsum : g n - L = ∑ i : E, (g n i - L i) • (Pi.single i 1 : E → O) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ trivial
    have h := SModEq.sub_mem.1 (hL i n)
    simpa using h
  let v : E → S := fun e => ⟨e, hE e e.2⟩
  let f : (E → O) →ₗ[O] S := Fintype.linearCombination O v
  have hsurj : Function.Surjective f := by
    refine surjective_of_mkQ_comp_surjective (I := maximalIdeal O) ?_
    intro y
    obtain ⟨s, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨e, he, s', hs', hs⟩ := hdig s s.2
    refine ⟨Pi.single ⟨e, he⟩ 1, ?_⟩
    have hf : f (Pi.single ⟨e, he⟩ 1) = ⟨e, hE e he⟩ := by
      simp [f, v, Fintype.linearCombination_apply_single]
    simp only [LinearMap.comp_apply, hf]
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hI,
      Submodule.ideal_span_singleton_smul]
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨-⟨s', hs'⟩, trivial, ?_⟩
    apply Subtype.ext
    simp [hs]
  exact Module.Finite.of_surjective f hsurj
