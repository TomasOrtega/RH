import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerWordNeZeroReversedWordNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumMapRootEqSumCount
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteSpanRaisingOperatorWordsLowestKTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordReachingIrreducibleKModuleReachesHighestWeigStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KTypeLeKFiniteVectorsFiniteDimensionalStatement
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

/- English proof (translation)
Introduce `n ε H _ _ σ D E lam hP hC hDS hK μ S hS`. Establish `hcomp : CompleteSpace H` using `hDS.1`. Establish `hU : IsURepOn (UJset ε) σ` using `hDS.2.2.1`. Establish `hI : IsIrredOn (UJset ε) σ` using `hDS.2.2.2.1`. Take `⟨w, hw0, -, hwH⟩` from `hK.hw μ S hS`.

Establish `key : ∃ T : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) T ∧ ∃ x ∈ T.comap D.subtype, ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ⟪w, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x⟫_ℂ ≠ 0`. Assume the negation of the conclusion as `hne`. Set `Q : Submodule ℂ D` to `{ carrier := {x | ∀ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) → ⟪w, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x⟫_ℂ = 0} add_mem' := by`. Introduce `a b ha hb l hl`. Rewrite using `[map_add, inner_add_right, ha l hl, hb l hl, add_zero]`.

Use the proof step `zero_mem' := by`. Introduce `l hl`. Rewrite using `[map_zero, inner_zero_right]`. Use the proof step `smul_mem' := by`. Introduce `c a ha l hl`.

Rewrite using `[map_smul, inner_smul_right, ha l hl, mul_zero] }`. Establish `hT : ∀ T ∈ {S : Submodule ℂ H | IsKTypeOf ε σ (lowK ε lam) S}, T ≤ Q.map D.subtype`. Introduce `T hT y hy`. Establish `hTD` using `(GlobalTheory.T.kType_le_kFiniteVectors_finiteDimensional n ε H σ D E hcomp hU hI hK _ T hT).1`. Use `⟨⟨y, hTD hy⟩, ?_, rfl⟩` and prove the remaining obligations.

Introduce `l hl`. Assume the negation of the conclusion as `h`. Conclude with `hne ⟨T, hT, ⟨y, hTD hy⟩, hy, l, hl, h⟩`. Establish `hlow : lowKSub ε lam σ ≤ Q.map D.subtype` using `sSup_le hT`. Establish `hspan` using `GlobalTheory.T.kFinite_span_raisingOperator_words_lowestKType n ε H σ D E lam hP hC hDS hK`.

Establish `hle : Submodule.span ℂ {y : D | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ (lowKSub ε lam σ).comap D.subtype, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} ≤ (ℂ ∙ w)ᗮ`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `y ⟨l, hl, x, hx, rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]`. Take `⟨x', hx', hxx⟩` from `hlow hx`.

Establish `: x' = x` using `Subtype.ext hxx`. Substitute `this` using the available equality. Conclude with `hx' l hl`. Rewrite `hle` using `[hspan]`. Establish `hw : w ∈ (ℂ ∙ w)ᗮ` using `hle Submodule.mem_top`.

Rewrite `hw` using `[Submodule.mem_orthogonal_singleton_iff_inner_right, inner_self_eq_zero]`. Conclude with `hw0 hw`. Take `⟨T, hT, x, hx, l, hl, hne⟩` from `key`. Establish `hadj` using `GlobalTheory.T.inner_word_ne_zero_reversedWord_ne_zero n ε D E hK.unit l w x hne`. Take `⟨-, hfd, hstab, hhw⟩` from `GlobalTheory.T.kType_le_kFiniteVectors_finiteDimensional n ε H σ D E hcomp hU hI hK _ T hT`.

Establish `hl' : ∀ p ∈ l.reverse.map Prod.swap, ε p.1 = false ∧ ε p.2 = true`. Introduce `p hp`. Rewrite `hp` using `[List.mem_map]`. Take `⟨q, hq, rfl⟩` from `hp`. Rewrite `hq` using `[List.mem_reverse]`.

Conclude with `⟨(hl q hq).2, (hl q hq).1⟩`. Establish `hKU : KUnit ε E` using `fun a b hab y z => Formalism.REAL.isUnitary_kUnit ε E hK.unit a b hab y z`. Take `⟨l', -, hl'ty, hsum⟩` from `GlobalTheory.T.word_reaching_irreducible_k_module_reaches_highest_weight n ε D E hK.gl hKU (T.comap D.subtype) hfd hstab (lowK ε lam) hhw μ w hwH false true _ hl' x hx hadj`. Conclude with `GlobalTheory.root_word_count_letters n ε μ (lowK ε lam) l' hl'ty hsum`.
-/
theorem GlobalTheory.kType_weight_in_cone_over_lowK : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D) (lam : Fin n → ℝ), IsHCParam lam → IsHolChamber ε lam → IsDS ε lam σ → IsKMod ε σ D E → ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S → ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → ε a = true ∧ ε b = false) ∧ μ = lowK ε lam + ∑ a, ∑ b, (c a b : ℝ) • root a b := by
  intro n ε H _ _ σ D E lam hP hC hDS hK μ S hS
  have hcomp : CompleteSpace H := hDS.1
  have hU : IsURepOn (UJset ε) σ := hDS.2.2.1
  have hI : IsIrredOn (UJset ε) σ := hDS.2.2.2.1
  obtain ⟨w, hw0, -, hwH⟩ := hK.hw μ S hS
  have key : ∃ T : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) T ∧ ∃ x ∈ T.comap D.subtype,
      ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧
        ⟪w, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x⟫_ℂ ≠ 0 := by
    by_contra hne
    let Q : Submodule ℂ D :=
      { carrier := {x | ∀ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) →
          ⟪w, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x⟫_ℂ = 0}
        add_mem' := by
          intro a b ha hb l hl
          rw [map_add, inner_add_right, ha l hl, hb l hl, add_zero]
        zero_mem' := by
          intro l hl
          rw [map_zero, inner_zero_right]
        smul_mem' := by
          intro c a ha l hl
          rw [map_smul, inner_smul_right, ha l hl, mul_zero] }
    have hT : ∀ T ∈ {S : Submodule ℂ H | IsKTypeOf ε σ (lowK ε lam) S}, T ≤ Q.map D.subtype := by
      intro T hT y hy
      have hTD := (GlobalTheory.T.kType_le_kFiniteVectors_finiteDimensional n ε H σ D E hcomp hU hI hK _ T hT).1
      refine ⟨⟨y, hTD hy⟩, ?_, rfl⟩
      intro l hl
      by_contra h
      exact hne ⟨T, hT, ⟨y, hTD hy⟩, hy, l, hl, h⟩
    have hlow : lowKSub ε lam σ ≤ Q.map D.subtype := sSup_le hT
    have hspan := GlobalTheory.T.kFinite_span_raisingOperator_words_lowestKType n ε H σ D E lam hP hC hDS hK
    have hle : Submodule.span ℂ {y : D | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧
        ∃ x ∈ (lowKSub ε lam σ).comap D.subtype, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} ≤
        (ℂ ∙ w)ᗮ := by
      rw [Submodule.span_le]
      rintro y ⟨l, hl, x, hx, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
      obtain ⟨x', hx', hxx⟩ := hlow hx
      have : x' = x := Subtype.ext hxx
      subst this
      exact hx' l hl
    rw [hspan] at hle
    have hw : w ∈ (ℂ ∙ w)ᗮ := hle Submodule.mem_top
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_self_eq_zero] at hw
    exact hw0 hw
  obtain ⟨T, hT, x, hx, l, hl, hne⟩ := key
  have hadj := GlobalTheory.T.inner_word_ne_zero_reversedWord_ne_zero n ε D E hK.unit l w x hne
  obtain ⟨-, hfd, hstab, hhw⟩ := GlobalTheory.T.kType_le_kFiniteVectors_finiteDimensional n ε H σ D E hcomp hU hI hK _ T hT
  have hl' : ∀ p ∈ l.reverse.map Prod.swap, ε p.1 = false ∧ ε p.2 = true := by
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [List.mem_reverse] at hq
    exact ⟨(hl q hq).2, (hl q hq).1⟩
  have hKU : KUnit ε E := fun a b hab y z => Formalism.REAL.isUnitary_kUnit ε E hK.unit a b hab y z
  obtain ⟨l', -, hl'ty, hsum⟩ := GlobalTheory.T.word_reaching_irreducible_k_module_reaches_highest_weight n ε D E hK.gl hKU (T.comap D.subtype) hfd hstab (lowK ε lam) hhw
    μ w hwH false true _ hl' x hx hadj
  exact GlobalTheory.root_word_count_letters n ε μ (lowK ε lam) l' hl'ty hsum
