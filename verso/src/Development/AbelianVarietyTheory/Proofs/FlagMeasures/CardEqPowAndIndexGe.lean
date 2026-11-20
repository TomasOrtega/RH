import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.FiniteModuleOrder

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `D _ _ _ hn`. Break down `subsingleton_or_nontrivial D with h | h` into its components or cases. Conclude with `⟨0, by simp⟩`.

Establish `hfin : Finite (Submodule R D)` using `Finite.of_injective _ SetLike.coe_injective`. Take `⟨M, hM, -⟩` from `(eq_top_or_exists_le_coatom (⊥ : Submodule R D)).resolve_left bot_ne_top`. Establish `hs : IsSimpleModule R (D ⧸ M)` using `isSimpleModule_iff_isCoatom.2 hM`. Take `⟨I, hI, ⟨e⟩⟩` from `isSimpleModule_iff_quot_maximal.1 hs`. Establish `hI' : I = IsLocalRing.maximalIdeal R` using `IsLocalRing.eq_maximalIdeal hI`.

Substitute `hI'` using the available equality. Establish `hc` using `Submodule.card_eq_card_quotient_mul_card M`. Establish `hnt : Nontrivial (D ⧸ M)` using `IsSimpleModule.nontrivial R _`. Establish `hf : Finite (D ⧸ M)` using `Finite.of_surjective _ (Submodule.Quotient.mk_surjective M)`. Establish `h2 : 1 < Nat.card (D ⧸ M)` using `Finite.one_lt_card`.

Establish `hpos : 0 < Nat.card M` using `Nat.card_pos`. Take `⟨i, hi⟩` from `ih (Nat.card M) (by rw [← hn, hc]; nlinarith) M rfl`. Conclude with `⟨i + 1, by rw [hc, hi, Nat.card_congr e.toEquiv, pow_succ]⟩`.
-/
theorem exists_card_eq_pow (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) :
    ∀ (D : Type) [AddCommGroup D] [Module R D] [Finite D], Nat.card D = n →
      ∃ i : ℕ, Nat.card D = Nat.card (R ⧸ IsLocalRing.maximalIdeal R) ^ i := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro D _ _ _ hn
    rcases subsingleton_or_nontrivial D with h | h
    · exact ⟨0, by simp⟩
    have hfin : Finite (Submodule R D) := Finite.of_injective _ SetLike.coe_injective
    obtain ⟨M, hM, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule R D)).resolve_left bot_ne_top
    have hs : IsSimpleModule R (D ⧸ M) := isSimpleModule_iff_isCoatom.2 hM
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hs
    have hI' : I = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hI
    subst hI'
    have hc := Submodule.card_eq_card_quotient_mul_card M
    have hnt : Nontrivial (D ⧸ M) := IsSimpleModule.nontrivial R _
    have hf : Finite (D ⧸ M) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective M)
    have h2 : 1 < Nat.card (D ⧸ M) := Finite.one_lt_card
    have hpos : 0 < Nat.card M := Nat.card_pos
    obtain ⟨i, hi⟩ := ih (Nat.card M) (by rw [← hn, hc]; nlinarith) M rfl
    exact ⟨i + 1, by rw [hc, hi, Nat.card_congr e.toEquiv, pow_succ]⟩

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L ϖ hϖ`. Establish `hint : ∀ a : 𝒪[F], algebraMap F E a ∈ L.O` using `fun a => (GlobalTheory.UnramOrder.algebraMap_mem_iff L a).2 a.2`. Set `i : 𝒪[F] →+* L.O` to `(algebraMap 𝒪[F] E).codRestrict L.O hint`. Establish `key : ∀ (D : Type) [AddCommGroup D] [Module L.O D] [Finite D], ∃ i : ℕ, Nat.card D = resQ ϖ ^ i`. Introduce `D _ _ _`.

Set `: Module 𝒪[F] D` to `Module.compHom D i`. Rewrite using `[resQ, ← hϖ.maximalIdeal_eq]`. Conclude with `exists_card_eq_pow 𝒪[F] _ D rfl`. Introduce `D _ _ _`. Use `⟨key D, fun I hI => ?_⟩` and prove the remaining obligations.

Establish `hnt : Nontrivial (D ⧸ I)` using `Submodule.Quotient.nontrivial_iff.2 hI`. Establish `hf : Finite (D ⧸ I)` using `Finite.of_surjective _ (Submodule.Quotient.mk_surjective I)`. Establish `h2 : 1 < Nat.card (D ⧸ I)` using `Finite.one_lt_card`. Take `⟨j, hj⟩` from `key (D ⧸ I)`. Establish `hj0 : j ≠ 0` using `by rintro rfl; rw [pow_zero] at hj; omega`.

Rewrite using `[Submodule.card_eq_card_quotient_mul_card I, hj, mul_comm]`. Conclude with `Nat.mul_le_mul_left _ (Nat.le_self_pow hj0 _)`.
-/
theorem card_eq_pow_and_index_ge : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (D : Type) [AddCommGroup D] [Module L.O D] [Finite D], (∃ i : ℕ, Nat.card D = resQ ϖ ^ i) ∧ ∀ I : Submodule L.O D, I ≠ ⊤ → resQ ϖ * Nat.card I ≤ Nat.card D := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ
  have hint : ∀ a : 𝒪[F], algebraMap F E a ∈ L.O := fun a =>
    (GlobalTheory.UnramOrder.algebraMap_mem_iff L a).2 a.2
  let i : 𝒪[F] →+* L.O := (algebraMap 𝒪[F] E).codRestrict L.O hint
  have key : ∀ (D : Type) [AddCommGroup D] [Module L.O D] [Finite D],
      ∃ i : ℕ, Nat.card D = resQ ϖ ^ i := by
    intro D _ _ _
    let : Module 𝒪[F] D := Module.compHom D i
    rw [resQ, ← hϖ.maximalIdeal_eq]
    exact exists_card_eq_pow 𝒪[F] _ D rfl
  intro D _ _ _
  refine ⟨key D, fun I hI => ?_⟩
  have hnt : Nontrivial (D ⧸ I) := Submodule.Quotient.nontrivial_iff.2 hI
  have hf : Finite (D ⧸ I) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective I)
  have h2 : 1 < Nat.card (D ⧸ I) := Finite.one_lt_card
  obtain ⟨j, hj⟩ := key (D ⧸ I)
  have hj0 : j ≠ 0 := by rintro rfl; rw [pow_zero] at hj; omega
  rw [Submodule.card_eq_card_quotient_mul_card I, hj, mul_comm]
  exact Nat.mul_le_mul_left _ (Nat.le_self_pow hj0 _)

end GlobalTheory.FiniteModuleOrder
