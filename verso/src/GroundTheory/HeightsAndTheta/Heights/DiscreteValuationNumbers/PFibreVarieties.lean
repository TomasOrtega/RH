import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFibreVar
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsComponentDim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsGenericDimGe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

/- English proof (translation)
Proceed by induction on `a using WithBot.recBotCoe with`. Consider the case `bot`. It suffices to derive a contradiction. Establish `e : ((m : WithBot ℕ∞) + 1) = (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞)` using `by push_cast; rfl`. Rewrite `h` using `[Nat.cast_add, Nat.cast_one, e]`.

Conclude with `WithBot.bot_ne_coe h`. Consider the case `coe a`. Proceed by induction on `a using ENat.recTopCoe with`. Consider the case `top`. It suffices to derive a contradiction.

Simplify using `at h`. Establish `e : ((m : ℕ∞) : WithBot ℕ∞) = (m : WithBot ℕ∞)` using `rfl`. Rewrite `h` using `[← e]`. Conclude with `ENat.top_ne_natCast m (WithBot.coe_injective h)`. Consider the case `coe a`.

Establish `h' : ((a + 1 : ℕ) : WithBot ℕ∞) = ((m + 1 : ℕ) : WithBot ℕ∞)`. Rewrite using `[← h]`. Use `push_cast`. Both sides reduce to the same expression. Establish `: a + 1 = m + 1` using `by exact_mod_cast h'`.

Establish `ham : a = m` using `by omega`. Substitute `ham` using the available equality. Both sides reduce to the same expression.
-/
private theorem withBot_eq_of_add_one_eq (a : WithBot ℕ∞) (m : ℕ)
    (h : a + 1 = ((m + 1 : ℕ) : WithBot ℕ∞)) : a = (m : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot =>
    exfalso
    have e : ((m : WithBot ℕ∞) + 1) = (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by push_cast; rfl
    rw [Nat.cast_add, Nat.cast_one, e] at h
    exact WithBot.bot_ne_coe h
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      simp at h
      have e : ((m : ℕ∞) : WithBot ℕ∞) = (m : WithBot ℕ∞) := rfl
      rw [← e] at h
      exact ENat.top_ne_natCast m (WithBot.coe_injective h)
    | coe a =>
      have h' : ((a + 1 : ℕ) : WithBot ℕ∞) = ((m + 1 : ℕ) : WithBot ℕ∞) := by
        rw [← h]; push_cast; rfl
      have : a + 1 = m + 1 := by exact_mod_cast h'
      have ham : a = m := by omega
      subst ham
      rfl

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ P d hP`. Take `⟨hprime, hhomog, hforms⟩` from `hGen O K ι P hP.multiProj hP.noTorsion`. Establish `hcast : ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) = ((d + Fintype.card K + 1 : ℕ) : WithBot ℕ∞)`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Use `⟨⟨⟨hprime, hhomog, ?_⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `k`. Take `⟨i, hi⟩` from `hP.multiProj.relevant k`. Take `⟨-, h⟩` from `hforms _ _ (isWeightedHomogeneous_X O (blockWeight ι) ⟨k, i⟩) hi`. Conclude with `⟨i, by simpa [MvPolynomial.map_X] using h⟩`.

Establish `h1` using `hBound O K ι P hP.multiProj hP.noTorsion`. Establish `h2` using `hGe O K ι P hP.multiProj.isPrime hP.noTorsion`. Rewrite `h1`, `h2` using `[hP.dim, hcast]`. Conclude with `withBot_eq_of_add_one_eq _ _ (le_antisymm h1 h2)`. Introduce `W hW`.

Establish `hW0` using `hW`. Unfold `divCycle at hW`. Use `split_ifs at hW with h`. Take `⟨hWmin, hWrel⟩` from `h`. Establish `hWp : W.IsPrime` using `hWmin.1.1`.

Establish `hϖW : (C ϖ : MRing ι O) ∈ W` using `hWmin.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))`. Take `⟨hsp, -, hrel, -⟩` from `hCorr O ϖ hϖ K ι P W hWp hϖW`. Establish `hJ : IsMultiHomogIdeal (P ⊔ Ideal.span {(C ϖ : MRing ι O)})` using `hSup O K ι P (C ϖ) 0 hP.multiProj.multiHomog (isWeightedHomogeneous_C _ _)`. Establish `hWh : IsMultiHomogIdeal W` using `hMin O K ι _ W hJ hWmin`. Establish `hϖP : (C ϖ : MRing ι O) ∉ P`.

Introduce `hmem`. Establish `: ϖ ∈ P.comap (C : O →+* MRing ι O)` using `hmem`. Rewrite `this` using `[hP.noTorsion, Ideal.mem_bot]`. Conclude with `hϖ.ne_zero this`. Use `⟨⟨hsp, hSpecHomog O K ι W hWh, hrel.mp hWrel⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hQuot O ϖ hϖ K ι W hϖW]`. Conclude with `hComp O ϖ hϖ K ι P d hP 0 (C ϖ) (isWeightedHomogeneous_C _ _) hϖP W hW0 hϖW`. Conclude with `absurd rfl hW`.
-/
theorem FibreVarieties.proof
    (hGen : GenericFibProps.Statement.{u}) (hBound : GenericDimBound.Statement.{u})
    (hGe : GenericDimGe.Statement.{u}) (hCorr : SpecialIdealCorresp.Statement.{u})
    (hSpecHomog : SpecialIdealMultiHomog.Statement.{u}) (hSup : SupSpanMultiHomog.Statement.{u})
    (hMin : MinimalPrimeMultiHomog.Statement.{u}) (hQuot : SpecialQuotDim.Statement.{u})
    (hComp : ComponentDim.Statement.{u}) : FibreVarieties.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP
  obtain ⟨hprime, hhomog, hforms⟩ := hGen O K ι P hP.multiProj hP.noTorsion
  have hcast : ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) =
      ((d + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) := by
    congr 1; omega
  refine ⟨⟨⟨hprime, hhomog, ?_⟩, ?_⟩, ?_⟩
  ·
    intro k
    obtain ⟨i, hi⟩ := hP.multiProj.relevant k
    obtain ⟨-, h⟩ := hforms _ _ (isWeightedHomogeneous_X O (blockWeight ι) ⟨k, i⟩) hi
    exact ⟨i, by simpa [MvPolynomial.map_X] using h⟩
  ·
    have h1 := hBound O K ι P hP.multiProj hP.noTorsion
    have h2 := hGe O K ι P hP.multiProj.isPrime hP.noTorsion
    rw [hP.dim, hcast] at h1 h2
    exact withBot_eq_of_add_one_eq _ _ (le_antisymm h1 h2)
  ·
    intro W hW
    have hW0 := hW
    unfold divCycle at hW
    split_ifs at hW with h
    · obtain ⟨hWmin, hWrel⟩ := h
      have hWp : W.IsPrime := hWmin.1.1
      have hϖW : (C ϖ : MRing ι O) ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
      obtain ⟨hsp, -, hrel, -⟩ := hCorr O ϖ hϖ K ι P W hWp hϖW
      have hJ : IsMultiHomogIdeal (P ⊔ Ideal.span {(C ϖ : MRing ι O)}) :=
        hSup O K ι P (C ϖ) 0 hP.multiProj.multiHomog (isWeightedHomogeneous_C _ _)
      have hWh : IsMultiHomogIdeal W := hMin O K ι _ W hJ hWmin
      have hϖP : (C ϖ : MRing ι O) ∉ P := by
        intro hmem
        have : ϖ ∈ P.comap (C : O →+* MRing ι O) := hmem
        rw [hP.noTorsion, Ideal.mem_bot] at this
        exact hϖ.ne_zero this
      refine ⟨⟨hsp, hSpecHomog O K ι W hWh, hrel.mp hWrel⟩, ?_⟩
      rw [hQuot O ϖ hϖ K ι W hϖW]
      exact hComp O ϖ hϖ K ι P d hP 0 (C ϖ) (isWeightedHomogeneous_C _ _) hϖP W hW0 hϖW
    · exact absurd rfl hW

end GroundTheory.Heights₂.Heights.NumbersDVR
