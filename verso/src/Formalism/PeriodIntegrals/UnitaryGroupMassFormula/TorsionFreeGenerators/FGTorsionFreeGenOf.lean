import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TorsionFreeGenerators.RankOneStep

namespace PI.FGTFG

open Module

/- English proof (translation)
The claim follows from `Function.Injective.noZeroSMulDivisors _ Subtype.val_injective rfl (fun _ _ => rfl)`.
-/
theorem nzsd_sub {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [NoZeroSMulDivisors R M] (N : Submodule R M) : NoZeroSMulDivisors R N :=
  Function.Injective.noZeroSMulDivisors _ Subtype.val_injective rfl (fun _ _ => rfl)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Establish `h1` using `(LinearMap.ker φ).finrank_quotient_add_finrank`. Establish `h2 : finrank R (M ⧸ LinearMap.ker φ) = 1`. Rewrite using `[(φ.quotKerEquivRange).finrank_eq, hφ]`. Rewrite using `[← (LinearEquiv.toSpanNonzeroSingleton R R b hb).finrank_eq]`.

Conclude with `Module.finrank_self R`. Use linear arithmetic over natural numbers and integers. Establish `hbm : b ∈ LinearMap.range φ` using `hφ ▸ Ideal.mem_span_singleton_self b`. Take `⟨e, he⟩` from `hbm`. Use `⟨e, eq_top_iff.mpr fun m _ => ?_⟩` and prove the remaining obligations.

Establish `hm' : φ m ∈ LinearMap.range φ` using `LinearMap.mem_range_self φ m`. Rewrite `hm'` using `[hφ, Ideal.mem_span_singleton']`. Take `⟨t, ht⟩` from `hm'`. Establish `hm : m = (m - t • e) + t • e` using `by abel`. Rewrite using `[hm]`.

Use `Submodule.add_mem_sup ?_ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e))` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, map_sub, map_smul, he, smul_eq_mul, ht, sub_self]`.
-/
theorem peel {R M : Type} [CommRing R] [IsDedekindDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [NoZeroSMulDivisors R M] (φ : M →ₗ[R] R) (b : R) (hb : b ≠ 0)
    (hφ : LinearMap.range φ = Ideal.span {b}) :
    finrank R (LinearMap.ker φ) + 1 = finrank R M ∧
    ∃ e : M, LinearMap.ker φ ⊔ Submodule.span R {e} = ⊤ := by
  constructor
  · have h1 := (LinearMap.ker φ).finrank_quotient_add_finrank
    have h2 : finrank R (M ⧸ LinearMap.ker φ) = 1 := by
      rw [(φ.quotKerEquivRange).finrank_eq, hφ]
      rw [← (LinearEquiv.toSpanNonzeroSingleton R R b hb).finrank_eq]
      exact Module.finrank_self R
    omega
  · have hbm : b ∈ LinearMap.range φ := hφ ▸ Ideal.mem_span_singleton_self b
    obtain ⟨e, he⟩ := hbm
    refine ⟨e, eq_top_iff.mpr fun m _ => ?_⟩
    have hm' : φ m ∈ LinearMap.range φ := LinearMap.mem_range_self φ m
    rw [hφ, Ideal.mem_span_singleton'] at hm'
    obtain ⟨t, ht⟩ := hm'
    have hm : m = (m - t • e) + t • e := by abel
    rw [hm]
    refine Submodule.add_mem_sup ?_ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e))
    rw [LinearMap.mem_ker, map_sub, map_smul, he, smul_eq_mul, ht, sub_self]

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `M _ _ _ _ hM`. Establish `: Subsingleton M` using `Module.finrank_zero_iff.mp hM`.

Conclude with `⟨∅, by simp, Subsingleton.elim _ _⟩`. Consider the case `succ n ih`. Introduce `M _ _ _ _ hM`. Break down `Nat.lt_or_ge n 1 with hn | hn` into its components or cases. Take `⟨s, hs, hsp⟩` from `h1 R M (by omega)`.

Conclude with `⟨s, by omega, hsp⟩`. Take `⟨φ, b, hb, hφ⟩` from `hS R M (by omega)`. Take `⟨hr, e, he⟩` from `peel φ b hb hφ`. Use `haveI := nzsd_sub (LinearMap.ker φ)`. Take `⟨s, hs, hspan⟩` from `ih (LinearMap.ker φ) (by omega)`.

Use `⟨insert e (s.map (Function.Embedding.subtype _)), ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `himg : Submodule.span R ((s.map (Function.Embedding.subtype _) : Finset M) : Set M) = LinearMap.ker φ`. Rewrite using `[Finset.coe_map, Function.Embedding.coe_subtype]`. Use `Submodule.span_image (R := R) (s := (s : Set (LinearMap.ker φ))) (LinearMap.ker φ).subtype` as an intermediate fact.

Rewrite `this` using `[Submodule.coe_subtype]`. Rewrite using `[this, hspan, Submodule.map_top, Submodule.range_subtype]`. Rewrite using `[Finset.coe_insert, Submodule.span_insert, himg, sup_comm, he]`.
-/
theorem main (hS : SplitStep) (h1 : RankOneStep) (R : Type) [CommRing R] [IsDedekindDomain R] :
    ∀ n : ℕ, ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
      [NoZeroSMulDivisors R M], finrank R M = n →
      ∃ s : Finset M, s.card ≤ n + 1 ∧ Submodule.span R (s : Set M) = ⊤ := by
  intro n
  induction n with
  | zero =>
    intro M _ _ _ _ hM
    have : Subsingleton M := Module.finrank_zero_iff.mp hM
    exact ⟨∅, by simp, Subsingleton.elim _ _⟩
  | succ n ih =>
    intro M _ _ _ _ hM
    rcases Nat.lt_or_ge n 1 with hn | hn
    · obtain ⟨s, hs, hsp⟩ := h1 R M (by omega)
      exact ⟨s, by omega, hsp⟩
    · obtain ⟨φ, b, hb, hφ⟩ := hS R M (by omega)
      obtain ⟨hr, e, he⟩ := peel φ b hb hφ
      haveI := nzsd_sub (LinearMap.ker φ)
      obtain ⟨s, hs, hspan⟩ := ih (LinearMap.ker φ) (by omega)
      classical
      refine ⟨insert e (s.map (Function.Embedding.subtype _)), ?_, ?_⟩
      · calc _ ≤ (s.map (Function.Embedding.subtype _)).card + 1 := Finset.card_insert_le _ _
          _ ≤ n + 1 + 1 := by rw [Finset.card_map]; omega
      · have himg : Submodule.span R ((s.map (Function.Embedding.subtype _) : Finset M) : Set M)
            = LinearMap.ker φ := by
          rw [Finset.coe_map, Function.Embedding.coe_subtype]
          have := Submodule.span_image (R := R) (s := (s : Set (LinearMap.ker φ)))
            (LinearMap.ker φ).subtype
          rw [Submodule.coe_subtype] at this
          rw [this, hspan, Submodule.map_top, Submodule.range_subtype]
        rw [Finset.coe_insert, Submodule.span_insert, himg, sup_comm, he]

end PI.FGTFG
