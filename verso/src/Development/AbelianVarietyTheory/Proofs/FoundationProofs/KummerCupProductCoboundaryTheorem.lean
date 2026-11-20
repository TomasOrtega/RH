import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupKummerCoboundaryOfNormsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCochainCharacterGaloisInvariantClassStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerExponentOfGaloisElementIsKummerCharacter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TsenTheoremStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FieldNormSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZetaMemRange
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerDivisorDescendsFunctionFieldStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixesAdjoinKummerRootsAndValuesEqStatement

open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.KummerCob

/- English proof (translation)
Introduce `k K Ω _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ a b α β haA hai hbA hbi ha0 hb0 hα hβ`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K`. Use `haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic`. Use `haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap (RatFunc k) K).injective`. Take `⟨z, hz⟩` from `zeta_mem_range k K Ω N ζ hN hζ`.

Establish `hfix : ∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ` using `fun g => by rw [← hz]; exact g.commutes z`. Establish `hC1 : IsFirstChernClassOfLineBundle K` using `GlobalTheory.T.tsen_theorem k K`. Establish `hnorm : ∀ (L : IntermediateField K Ω), FiniteDimensional K L → ∀ c : K, c ≠ 0 → ∃ x : L, Algebra.norm K x = c` using `fun L _ c hc => GlobalTheory.T.exists_algebra_norm_eq_of_isFirstChernClass K L hC1 c hc`. Take `⟨η₀, hη₀c, hη₀⟩` from `GlobalTheory.T.exists_locallyConstant_kum_cup_coboundary_of_norm_surj K Ω N ζ hN hζ hfix hnorm a b α β ha0 hb0 hα hβ`. Take `⟨θ, hθ0, hθE, hθη, hθs⟩` from `GlobalTheory.T.kummer_cochain_character_galoisInvariant_class K Ω N ζ hN hζ hfix a b α β ha0 hb0 hα hβ η₀ hη₀c hη₀`.

Take `⟨f, hf0, hfB⟩` from `GlobalTheory.T.kummer_divisor_descends_functionField k K Ω N ζ hN hζ a b α β haA hai hbA hbi ha0 hb0 hα hβ θ hθ0 hθE hθs`. Take `⟨θ₀, hθ₀⟩` from `IsAlgClosed.exists_pow_nat_eq (algebraMap K Ω f) hN`. Establish `hθ₀0 : θ₀ ≠ 0`. Introduce and unpack `rfl`. Rewrite `hθ₀` using `[zero_pow hN.ne']`.

Conclude with `hf0 ((map_eq_zero_iff _ (algebraMap K Ω).injective).1 hθ₀.symm)`. Take `⟨hk0c, -, hk0add, -⟩` from `GlobalTheory.NeedB.KumLemma.kummer_character_main K Ω N ζ θ₀ hN hζ hfix hθ₀0 ⟨f, hθ₀.symm⟩`. Use `⟨fun g => η₀ g - kum ζ θ₀ g, hη₀c.sub hk0c, ?_, ?_⟩` and prove the remaining obligations. Introduce `g h`. Simplify using `only`.

Rewrite using `[hη₀ g h, hk0add g h]`. Expand and normalize the polynomial expressions, which then agree. Introduce `B hB g hg`. Take `⟨c, hcE, hc0, hcv⟩` from `hfB B hB`. Rewrite `hcv` using `[← hθ₀]`.

Take `⟨hgE, hk⟩` from `GlobalTheory.T.inertia_fixes_adjoin_kummer_roots_and_values_eq k K Ω N ζ hN hζ a b α β haA hai hbA hbi ha0 hb0 hα hβ θ θ₀ hθ0 hθ₀0 hθE ⟨f, hθ₀.symm⟩ B hB g hg c hcE hc0 hcv`. Use `show η₀ g - kum ζ θ₀ g = 0`. Rewrite using `[hθη g hgE, hk, sub_self]`.
-/
theorem cup_eq_coboundary_vanishing_on_inertia : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (a b : K) (α β : Ω), a ∈ FunctionField.ringOfIntegers k K → a⁻¹ ∈ FunctionField.ringOfIntegers k K →
      b ∈ FunctionField.ringOfIntegers k K → b⁻¹ ∈ FunctionField.ringOfIntegers k K → a ≠ 0 → b ≠ 0 →
      α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
      ∃ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η ∧
        (∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g) ∧
        ∀ B : ValuationSubring Ω, Over (FunctionField.ringOfIntegers k K).toSubring B → ∀ g, Inert B g → η g = 0 := by
  intro k K Ω _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ a b α β haA hai hbA hbi ha0 hb0 hα hβ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap (RatFunc k) K).injective
  obtain ⟨z, hz⟩ := zeta_mem_range k K Ω N ζ hN hζ
  have hfix : ∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ := fun g => by rw [← hz]; exact g.commutes z
  have hC1 : IsFirstChernClassOfLineBundle K := GlobalTheory.T.tsen_theorem k K
  have hnorm : ∀ (L : IntermediateField K Ω), FiniteDimensional K L → ∀ c : K, c ≠ 0 →
      ∃ x : L, Algebra.norm K x = c := fun L _ c hc => GlobalTheory.T.exists_algebra_norm_eq_of_isFirstChernClass K L hC1 c hc
  obtain ⟨η₀, hη₀c, hη₀⟩ := GlobalTheory.T.exists_locallyConstant_kum_cup_coboundary_of_norm_surj K Ω N ζ hN hζ hfix hnorm a b α β ha0 hb0 hα hβ
  obtain ⟨θ, hθ0, hθE, hθη, hθs⟩ :=
    GlobalTheory.T.kummer_cochain_character_galoisInvariant_class K Ω N ζ hN hζ hfix a b α β ha0 hb0 hα hβ η₀ hη₀c hη₀
  obtain ⟨f, hf0, hfB⟩ := GlobalTheory.T.kummer_divisor_descends_functionField k K Ω N ζ hN hζ a b α β haA hai hbA hbi ha0 hb0 hα hβ θ hθ0 hθE hθs
  obtain ⟨θ₀, hθ₀⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K Ω f) hN
  have hθ₀0 : θ₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hθ₀
    exact hf0 ((map_eq_zero_iff _ (algebraMap K Ω).injective).1 hθ₀.symm)
  obtain ⟨hk0c, -, hk0add, -⟩ :=
    GlobalTheory.NeedB.KumLemma.kummer_character_main K Ω N ζ θ₀ hN hζ hfix hθ₀0 ⟨f, hθ₀.symm⟩
  refine ⟨fun g => η₀ g - kum ζ θ₀ g, hη₀c.sub hk0c, ?_, ?_⟩
  · intro g h
    simp only
    rw [hη₀ g h, hk0add g h]
    ring
  · intro B hB g hg
    obtain ⟨c, hcE, hc0, hcv⟩ := hfB B hB
    rw [← hθ₀] at hcv
    obtain ⟨hgE, hk⟩ := GlobalTheory.T.inertia_fixes_adjoin_kummer_roots_and_values_eq k K Ω N ζ hN hζ a b α β haA hai hbA hbi ha0 hb0 hα hβ θ θ₀ hθ0 hθ₀0 hθE
      ⟨f, hθ₀.symm⟩ B hB g hg c hcE hc0 hcv
    show η₀ g - kum ζ θ₀ g = 0
    rw [hθη g hgE, hk, sub_self]

/- English proof (translation)
Introduce `k K Ω _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ a b α β ha0 hb0 haA hai hbA hbi hα hβ`. Use `haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic`. Take `⟨z, hz⟩` from `zeta_mem_range k K Ω N ζ hN hζ`. Establish `hfix : ∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ` using `fun g => by rw [← hz]; exact g.commutes z`. Establish `hα0 : α ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hα` using `[zero_pow hN.ne']`. Conclude with `ha0 ((map_eq_zero_iff _ (algebraMap K Ω).injective).1 hα.symm)`. Establish `hβ0 : β ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hβ` using `[zero_pow hN.ne']`. Conclude with `hb0 ((map_eq_zero_iff _ (algebraMap K Ω).injective).1 hβ.symm)`. Take `⟨hαc, -, hαadd, -⟩` from `GlobalTheory.NeedB.KumLemma.kummer_character_main K Ω N ζ α hN hζ hfix hα0 ⟨a, hα.symm⟩`. Take `⟨hβc, -, hβadd, -⟩` from `GlobalTheory.NeedB.KumLemma.kummer_character_main K Ω N ζ β hN hζ hfix hβ0 ⟨b, hβ.symm⟩`. Conclude with `⟨hαadd, hαc, hβadd, hβc, cup_eq_coboundary_vanishing_on_inertia k K Ω N ζ hN hζ a b α β haA hai hbA hbi ha0 hb0 hα hβ⟩`.
-/
theorem thmA : GlobalTheory.NeedB.ThmA := by
  intro k K Ω _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ a b α β ha0 hb0 haA hai hbA hbi hα hβ
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  obtain ⟨z, hz⟩ := zeta_mem_range k K Ω N ζ hN hζ
  have hfix : ∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ := fun g => by rw [← hz]; exact g.commutes z
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hα
    exact ha0 ((map_eq_zero_iff _ (algebraMap K Ω).injective).1 hα.symm)
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hβ
    exact hb0 ((map_eq_zero_iff _ (algebraMap K Ω).injective).1 hβ.symm)
  obtain ⟨hαc, -, hαadd, -⟩ :=
    GlobalTheory.NeedB.KumLemma.kummer_character_main K Ω N ζ α hN hζ hfix hα0 ⟨a, hα.symm⟩
  obtain ⟨hβc, -, hβadd, -⟩ :=
    GlobalTheory.NeedB.KumLemma.kummer_character_main K Ω N ζ β hN hζ hfix hβ0 ⟨b, hβ.symm⟩
  exact ⟨hαadd, hαc, hβadd, hβc,
    cup_eq_coboundary_vanishing_on_inertia k K Ω N ζ hN hζ a b α β haA hai hbA hbi ha0 hb0 hα hβ⟩

end GlobalTheory.KummerCob
