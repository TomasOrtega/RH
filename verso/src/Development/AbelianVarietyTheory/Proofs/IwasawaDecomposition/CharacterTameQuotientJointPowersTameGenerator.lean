import Mathlib
import ReciprocityTheory.GaloisValuations.Global
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootEqOfClose
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemZpowersOfTameGen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalCompatibilityAtTypes
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2

namespace GlobalTheory.TameTau

/- English proof (translation)
Establish `e : ({c} : Set O) = ⋂ M : ℕ, (fun x => x - c) ⁻¹' ((IsLocalRing.maximalIdeal O ^ M : Ideal O) : Set O)`. Use extensionality with `x`. Simplify using `only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl M`.

Simplify using the standard rewrite rules. Introduce `h`. Establish `h2` using `Ideal.mem_iInf.2 h`. Rewrite `h2` using `[Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top]`. Simplify `h2` using `[sub_eq_zero]`.

Rewrite using `[e]`. Use `isClosed_iInter fun M => IsClosed.preimage (continuous_id.sub continuous_const) ?_` and prove the remaining obligations. Conclude with `AddSubgroup.isClosed_of_isOpen (IsLocalRing.maximalIdeal O ^ M : Ideal O).toAddSubgroup ((isAdic_iff.1 had).1 M)`.
-/
theorem isClosed_singleton_of_isAdic {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [TopologicalSpace O] [IsTopologicalRing O] (had : IsAdic (IsLocalRing.maximalIdeal O)) (c : O) :
    IsClosed ({c} : Set O) := by
  have e : ({c} : Set O) = ⋂ M : ℕ, (fun x => x - c) ⁻¹'
      ((IsLocalRing.maximalIdeal O ^ M : Ideal O) : Set O) := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · rintro rfl M
      simp
    · intro h
      have h2 := Ideal.mem_iInf.2 h
      rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top] at h2
      simpa [sub_eq_zero] using h2
  rw [e]
  refine isClosed_iInter fun M => IsClosed.preimage (continuous_id.sub continuous_const) ?_
  exact AddSubgroup.isClosed_of_isOpen (IsLocalRing.maximalIdeal O ^ M : Ideal O).toAddSubgroup
    ((isAdic_iff.1 had).1 M)

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A γ hγ O _ _ _ _ _ had χ hχ m hm0 hm hI e π hπ he`. Use `set q : Ω := γ π / π with hqdef`. Establish `hroot : ∀ τ : G E Ω, (τ π / π) ^ m = 1`. Introduce `τ`. Rewrite using `[div_pow, ← map_pow, he, AlgEquiv.commutes, ← he, div_self (pow_ne_zero _ hπ)]`.

Establish `hq : q ^ m = 1` using `hroot γ`. Establish `hc : χ γ ^ m = 1` using `hI γ hγ.1`. Establish `hinv : ∀ {M : Type} [Group M] (x : M), x ^ m = 1 → ∀ n : ℕ, (x ^ n)⁻¹ = x ^ (n * (m - 1))`. Introduce `M _ x hx n`. Use `(eq_inv_of_mul_eq_one_left ?_).symm` and prove the remaining obligations.

Rewrite using `[← pow_add, show n * (m - 1) + n = n * m by`. Take `⟨k, rfl⟩ : ∃ k, m = k + 1` from `⟨m - 1, by omega⟩`. Simplify using `[Nat.mul_add]]`. Rewrite using `[pow_mul', hx, one_pow]`. Establish `hinv0 : ∀ (x : Ω), x ^ m = 1 → ∀ n : ℕ, (x ^ n)⁻¹ = x ^ (n * (m - 1))`.

Introduce `x hx n`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Rewrite `hx` using `[zero_pow hm0.ne']`. Conclude with `zero_ne_one hx`.

Use `hinv (Units.mk0 x hx0) (by ext; simpa using hx) n` as an intermediate fact. Use `congrArg (fun u : Ωˣ => (u : Ω)) this` as an intermediate fact. Simplify using `using this`. Set `H : Subgroup (G E Ω)` to `{ carrier := {σ | σ ∈ Ine (F := E) A ∧ ∃ n : ℕ, χ σ = χ γ ^ n ∧ σ π / π = q ^ n} mul_mem' := by`. Introduce and unpack `σ τ ⟨hσ, n₁, h₁, h₁'⟩ ⟨hτ, n₂, h₂, h₂'⟩`.

Use `⟨mul_mem hσ hτ, n₁ + n₂, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, h₁, h₂, pow_add]`. Rewrite using `[quot_mul hσ m hm hπ he, h₁', h₂', pow_add]`. Use the proof step `one_mem' := ⟨one_mem _, 0, by simp, by simp [div_self hπ]⟩`. Use the proof step `inv_mem' := by`.

Introduce and unpack `σ ⟨hσ, n, h₁, h₁'⟩`. Establish `hσi : σ⁻¹ ∈ Ine (F` using `E) A := inv_mem hσ`. Use `⟨hσi, n * (m - 1), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_inv, h₁, hinv _ hc]`. Establish `h3` using `quot_mul hσi m hm hπ he (τ := σ)`.

Rewrite `h3` using `[inv_mul_cancel, AlgEquiv.one_apply, div_self hπ, h₁']`. Rewrite using `[← hinv0 q hq, eq_inv_of_mul_eq_one_left h3.symm] }`. Establish `hclosed : IsClosed (H : Set (G E Ω))`. Establish `e : (H : Set (G E Ω)) = (Ine (F` using `E) A : Set (G E Ω)) ∩ ⋃ n ∈ Finset.range m, ({σ : G E Ω | ((χ σ : Oˣ) : O) = ((χ γ ^ n : Oˣ) : O)} ∩ {σ : G E Ω | σ π = q ^ n * π}) := by`. Use extensionality with `σ`.

Simplify using `only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_range, exists_prop, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hσ, n, h₁, h₁'⟩`. Use `⟨hσ, n % m, Nat.mod_lt _ hm0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h₁, ← pow_mod_orderOf, ← pow_mod_orderOf (χ γ) (n % m)]`.

Use `congr 2`. Establish `hd` using `orderOf_dvd_of_pow_eq_one hc`. Rewrite using `[Nat.mod_mod_of_dvd _ hd]`. Rewrite using `[← pow_mod_orderOf, ← div_eq_iff hπ, h₁']`. Rewrite using `[← pow_mod_orderOf q n]`.

Use `congr 1`. Rewrite using `[Nat.mod_mod_of_dvd _ (orderOf_dvd_of_pow_eq_one hq)]`. Introduce and unpack `⟨hσ, n, -, h₁, h₁'⟩`. Conclude with `⟨hσ, n, Units.ext h₁, by rw [h₁', mul_div_cancel_right₀ _ hπ]⟩`. Rewrite using `[e]`.

Use `(isClosed_Ine A).inter (isClosed_biUnion_finset fun n _ => IsClosed.inter ?_ ?_)` and prove the remaining obligations. Conclude with `(isClosed_singleton_of_isAdic had _).preimage hχ`. Conclude with `isClosed_setOf_apply π (fun y => y = q ^ n * π)`. Introduce `σ hσ`. Establish `hle : Subgroup.closure (insert γ {σ : G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}) ≤ H`.

Use `(Subgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `τ (rfl | hτ)`. Conclude with `⟨hγ.1, 1, by simp, by simp [hqdef]⟩`. Establish `hτI : τ ∈ Ine (F` using `E) A := GlobalTheory.TameGenPowers.wild_mem_Ine hτ`. Use `⟨hτI, 0, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_zero]`. Conclude with `GlobalTheory.WildSetSQ.char_eq_one_of_wild A had χ hχ τ hτ m hm (hI τ hτI)`. Rewrite using `[pow_zero]`. Conclude with `eq_one_of_pow_eq_one A hm (hroot τ) (hτ π hπ)`. Establish `hmem` using `closure_minimal (SetLike.coe_subset_coe.2 hle) hclosed (hγ.2 hσ)`.

Conclude with `hmem.2`.
-/
theorem joint_pow_of_tameGen : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (γ : G E Ω), TameGenAt A γ → ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → ∀ (m : ℕ), 0 < m → ¬ A.valuation (m : Ω) < 1 → (∀ σ ∈ Ine (F := E) A, χ σ ^ m = 1) → ∀ (e : E) (π : Ω), π ≠ 0 → π ^ m = algebraMap E Ω e → ∀ σ ∈ Ine (F := E) A, ∃ n : ℕ, χ σ = χ γ ^ n ∧ σ π / π = (γ π / π) ^ n := by
  intro E Ω _ _ _ _ _ A γ hγ O _ _ _ _ _ had χ hχ m hm0 hm hI e π hπ he
  set q : Ω := γ π / π with hqdef
  have hroot : ∀ τ : G E Ω, (τ π / π) ^ m = 1 := by
    intro τ
    rw [div_pow, ← map_pow, he, AlgEquiv.commutes, ← he, div_self (pow_ne_zero _ hπ)]
  have hq : q ^ m = 1 := hroot γ
  have hc : χ γ ^ m = 1 := hI γ hγ.1
  have hinv : ∀ {M : Type} [Group M] (x : M), x ^ m = 1 → ∀ n : ℕ, (x ^ n)⁻¹ = x ^ (n * (m - 1)) := by
    intro M _ x hx n
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [← pow_add, show n * (m - 1) + n = n * m by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp [Nat.mul_add]]
    rw [pow_mul', hx, one_pow]
  have hinv0 : ∀ (x : Ω), x ^ m = 1 → ∀ n : ℕ, (x ^ n)⁻¹ = x ^ (n * (m - 1)) := by
    intro x hx n
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow hm0.ne'] at hx
      exact zero_ne_one hx
    have := hinv (Units.mk0 x hx0) (by ext; simpa using hx) n
    have := congrArg (fun u : Ωˣ => (u : Ω)) this
    simpa using this
  let H : Subgroup (G E Ω) :=
    { carrier := {σ | σ ∈ Ine (F := E) A ∧ ∃ n : ℕ, χ σ = χ γ ^ n ∧ σ π / π = q ^ n}
      mul_mem' := by
        rintro σ τ ⟨hσ, n₁, h₁, h₁'⟩ ⟨hτ, n₂, h₂, h₂'⟩
        refine ⟨mul_mem hσ hτ, n₁ + n₂, ?_, ?_⟩
        · rw [map_mul, h₁, h₂, pow_add]
        · rw [quot_mul hσ m hm hπ he, h₁', h₂', pow_add]
      one_mem' := ⟨one_mem _, 0, by simp, by simp [div_self hπ]⟩
      inv_mem' := by
        rintro σ ⟨hσ, n, h₁, h₁'⟩
        have hσi : σ⁻¹ ∈ Ine (F := E) A := inv_mem hσ
        refine ⟨hσi, n * (m - 1), ?_, ?_⟩
        · rw [map_inv, h₁, hinv _ hc]
        · have h3 := quot_mul hσi m hm hπ he (τ := σ)
          rw [inv_mul_cancel, AlgEquiv.one_apply, div_self hπ, h₁'] at h3
          rw [← hinv0 q hq, eq_inv_of_mul_eq_one_left h3.symm] }
  have hclosed : IsClosed (H : Set (G E Ω)) := by
    have e : (H : Set (G E Ω)) = (Ine (F := E) A : Set (G E Ω)) ∩
        ⋃ n ∈ Finset.range m, ({σ : G E Ω | ((χ σ : Oˣ) : O) = ((χ γ ^ n : Oˣ) : O)} ∩
          {σ : G E Ω | σ π = q ^ n * π}) := by
      ext σ
      simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_range, exists_prop,
        SetLike.mem_coe]
      constructor
      · rintro ⟨hσ, n, h₁, h₁'⟩
        refine ⟨hσ, n % m, Nat.mod_lt _ hm0, ?_, ?_⟩
        · rw [h₁, ← pow_mod_orderOf, ← pow_mod_orderOf (χ γ) (n % m)]
          congr 2
          have hd := orderOf_dvd_of_pow_eq_one hc
          rw [Nat.mod_mod_of_dvd _ hd]
        · rw [← pow_mod_orderOf, ← div_eq_iff hπ, h₁']
          rw [← pow_mod_orderOf q n]
          congr 1
          rw [Nat.mod_mod_of_dvd _ (orderOf_dvd_of_pow_eq_one hq)]
      · rintro ⟨hσ, n, -, h₁, h₁'⟩
        exact ⟨hσ, n, Units.ext h₁, by rw [h₁', mul_div_cancel_right₀ _ hπ]⟩
    rw [e]
    refine (isClosed_Ine A).inter (isClosed_biUnion_finset fun n _ => IsClosed.inter ?_ ?_)
    · exact (isClosed_singleton_of_isAdic had _).preimage hχ
    · exact isClosed_setOf_apply π (fun y => y = q ^ n * π)
  intro σ hσ
  have hle : Subgroup.closure (insert γ {σ : G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}) ≤ H := by
    refine (Subgroup.closure_le _).2 ?_
    rintro τ (rfl | hτ)
    · exact ⟨hγ.1, 1, by simp, by simp [hqdef]⟩
    · have hτI : τ ∈ Ine (F := E) A := GlobalTheory.TameGenPowers.wild_mem_Ine hτ
      refine ⟨hτI, 0, ?_, ?_⟩
      · rw [pow_zero]
        exact GlobalTheory.WildSetSQ.char_eq_one_of_wild A had χ hχ τ hτ m hm (hI τ hτI)
      · rw [pow_zero]
        exact eq_one_of_pow_eq_one A hm (hroot τ) (hτ π hπ)
  have hmem := closure_minimal (SetLike.coe_subset_coe.2 hle) hclosed (hγ.2 hσ)
  exact hmem.2

end GlobalTheory.TameTau
