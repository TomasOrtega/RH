import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
universe u

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

structure PrincipalizationRules where
  divisorRed : ∀ T : MarkedIdealWithBoundary.{u},
    (∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) → ℕ → T.SequenceOfBlowups
  maxOrderRed : ∀ T : MarkedIdealWithBoundary.{u},
    (∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups) → T.SequenceOfBlowups
  orderRed : ∀ T : MarkedIdealWithBoundary.{u},
    (∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) → T.SequenceOfBlowups

namespace PrincipalizationRules

def divisorFamily (B : PrincipalizationRules.{u}) (L : PrincipalizationAssignment.{u}) (j : ℕ) :
    PrincipalizationAssignment.{u} :=
  fun T => B.divisorRed T (fun S _ => L S) j

/- English proof (authored)
The family at the chosen boundary index is obtained by applying the divisor rule to the input. Each strictly smaller request is answered by the supplied assignment, which is exactly the displayed rule.
-/
theorem divisorFamily_apply (B : PrincipalizationRules.{u}) (L : PrincipalizationAssignment.{u}) (j : ℕ)
    (T : MarkedIdealWithBoundary.{u}) :
    B.divisorFamily L j T = B.divisorRed T (fun S _ => L S) j := rfl

def orderFamily (B : PrincipalizationRules.{u}) (D : ℕ → PrincipalizationAssignment.{u}) :
    PrincipalizationAssignment.{u} :=
  fun T => B.orderRed T (fun S _ j => D j S)

/- English proof (authored)
The order family applies the order rule to the given input. Its auxiliary procedure uses the supplied divisor assignment at the requested boundary index, on each permitted input.
-/
theorem orderFamily_apply (B : PrincipalizationRules.{u}) (D : ℕ → PrincipalizationAssignment.{u})
    (T : MarkedIdealWithBoundary.{u}) :
    B.orderFamily D T = B.orderRed T (fun S _ j => D j S) := rfl

def maxOrderFamily (B : PrincipalizationRules.{u}) (A : PrincipalizationAssignment.{u}) :
    PrincipalizationAssignment.{u} :=
  fun T => B.maxOrderRed T (fun S _ => A S)

/- English proof (authored)
The maximal-order family applies the maximal-order rule to the input and answers each auxiliary request by the supplied order assignment.
-/
theorem maxOrderFamily_apply (B : PrincipalizationRules.{u}) (A : PrincipalizationAssignment.{u})
    (T : MarkedIdealWithBoundary.{u}) :
    B.maxOrderFamily A T = B.maxOrderRed T (fun S _ => A S) := rfl

def nextLevel (B : PrincipalizationRules.{u}) (L : OrderReductionData.{u}) : OrderReductionData.{u} where
  maxOrderRed := B.maxOrderFamily (B.orderFamily (fun j => B.divisorFamily L.maxOrderRed j))
  orderRed := B.orderFamily (fun j => B.divisorFamily L.maxOrderRed j)

/- English proof (authored)
The next level obtains its order reduction by first forming the divisor family with the previous maximal-order reduction and then applying the order rule to that family.
-/
@[simp] theorem nextLevel_orderReduction (B : PrincipalizationRules.{u}) (L : OrderReductionData.{u}) :
    (B.nextLevel L).orderRed = B.orderFamily (fun j => B.divisorFamily L.maxOrderRed j) := rfl

/- English proof (authored)
The next level first constructs its new order reduction from the divisor family of the previous maximal-order reduction. It then applies the maximal-order rule with this new order reduction.
-/
@[simp] theorem nextLevel_maxOrderReduction (B : PrincipalizationRules.{u}) (L : OrderReductionData.{u}) :
    (B.nextLevel L).maxOrderRed =
      B.maxOrderFamily (B.orderFamily (fun j => B.divisorFamily L.maxOrderRed j)) := rfl

def inputLevelData (B : PrincipalizationRules.{u}) : ℕ → OrderReductionData.{u}
  | 0 => trivialOrderReductionData.{u}
  | n + 1 => B.nextLevel (B.inputLevelData n)

def outputLevelData (B : PrincipalizationRules.{u}) (n : ℕ) : OrderReductionData.{u} := B.nextLevel (B.inputLevelData n)

/- English proof (authored)
The recursion begins at level zero with the trivial order reduction data.
-/
@[simp] theorem inputLevelData_zero (B : PrincipalizationRules.{u}) :
    B.inputLevelData 0 = trivialOrderReductionData.{u} := rfl

/- English proof (authored)
The output at a level is obtained by applying the next-level construction to that level's input data.
-/
theorem outputLevelData_eq_nextLevel (B : PrincipalizationRules.{u}) (n : ℕ) :
    B.outputLevelData n = B.nextLevel (B.inputLevelData n) := rfl

/- English proof (authored)
The recursion defines the successor input by applying the next-level construction to the preceding input, which is exactly the preceding output.
-/
@[simp] theorem inputLevelData_succ (B : PrincipalizationRules.{u}) (n : ℕ) :
    B.inputLevelData (n + 1) = B.outputLevelData n := rfl

def levelDivisorFamily (B : PrincipalizationRules.{u}) (n : ℕ) (j : ℕ) : PrincipalizationAssignment.{u} :=
  B.divisorFamily (B.inputLevelData n).maxOrderRed j

/- English proof (authored)
The order reduction of the output level is the order rule applied to its divisor family. At every boundary index that family uses the maximal-order reduction from the input level.
-/
theorem outputLevelData_orderReduction_eq_orderFamily (B : PrincipalizationRules.{u}) (n : ℕ) :
    (B.outputLevelData n).orderRed = B.orderFamily (fun j => B.levelDivisorFamily n j) := rfl

/- English proof (authored)
The maximal-order reduction of the output is constructed by applying the maximal-order rule to the order reduction at the same output level.
-/
theorem outputLevelData_maxOrderReduction_eq (B : PrincipalizationRules.{u}) (n : ℕ) :
    (B.outputLevelData n).maxOrderRed = B.maxOrderFamily (B.outputLevelData n).orderRed := rfl

structure ReducesInductivelyOnDimension (B : PrincipalizationRules.{u}) : Prop where
  divisorSpec : ∀ (n : ℕ) (L O : PrincipalizationAssignment.{u}),
    IsMaxOrderReduction (fun d => d < n) L O →
    ∀ j : ℕ, IsBoundaryDivisorReduction (fun d => d ≤ n) j (B.divisorFamily L j) L
  divisorShift : ∀ (n : ℕ) (L O : PrincipalizationAssignment.{u}),
    IsMaxOrderReduction (fun d => d < n) L O →
    IsBoundaryPositionInvariant (fun d => d ≤ n) (fun j => B.divisorFamily L j)
  maxOrderSpec : ∀ (n : ℕ) (A L : PrincipalizationAssignment.{u}),
    IsOrderReduction (fun d => d ≤ n) A L →
    IsMaxOrderReduction (fun d => d ≤ n) (B.maxOrderFamily A) A
  orderSpec : ∀ (n : ℕ) (D : ℕ → PrincipalizationAssignment.{u}) (L O : PrincipalizationAssignment.{u}),
    IsMaxOrderReduction (fun d => d < n) L O →
    (∀ j : ℕ, IsBoundaryDivisorReduction (fun d => d ≤ n) j (D j) L) →
    IsBoundaryPositionInvariant (fun d => d ≤ n) D →
    IsOrderReduction (fun d => d ≤ n) (B.orderFamily D) L

/- English proof (authored)
For a request from the order rule, the auxiliary marked ideal has dimension index at most that of the original input. Its divisor rule uses the previous maximal-order reduction only on strictly smaller inputs. All those inputs are strictly smaller than the original input, so the two previous reductions agree there by hypothesis. The auxiliary divisor procedures are therefore equal at every request. Applying the same order rule gives equal outputs.
-/
private theorem nextLevel_orderReduction_congr (B : PrincipalizationRules.{u}) (L L' : OrderReductionData.{u})
    (T : MarkedIdealWithBoundary.{u})
    (h : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → L.maxOrderRed S = L'.maxOrderRed S) :
    (B.nextLevel L).orderRed T = (B.nextLevel L').orderRed T := by
  have hfun : (fun (S : MarkedIdealWithBoundary.{u}) (_ : S.krullDimSucc ≤ T.krullDimSucc) (j : ℕ) =>
        B.divisorFamily L.maxOrderRed j S)
      = (fun (S : MarkedIdealWithBoundary.{u}) (_ : S.krullDimSucc ≤ T.krullDimSucc) (j : ℕ) =>
        B.divisorFamily L'.maxOrderRed j S) := by
    funext S hS j
    have hinner : (fun (S' : MarkedIdealWithBoundary.{u}) (_ : S'.krullDimSucc < S.krullDimSucc) => L.maxOrderRed S')
        = (fun (S' : MarkedIdealWithBoundary.{u}) (_ : S'.krullDimSucc < S.krullDimSucc) => L'.maxOrderRed S') := by
      funext S' h'
      exact h S' (lt_of_lt_of_le h' hS)
    show B.divisorRed S (fun S' _ => L.maxOrderRed S') j
        = B.divisorRed S (fun S' _ => L'.maxOrderRed S') j
    exact congrArg (fun f => B.divisorRed S f j) hinner
  show B.orderRed T (fun S _ j => B.divisorFamily L.maxOrderRed j S)
      = B.orderRed T (fun S _ j => B.divisorFamily L'.maxOrderRed j S)
  exact congrArg (B.orderRed T) hfun

/- English proof (authored)
The maximal-order rule consults the new order reduction only on inputs of at most the original dimension index. For each such input the hypothesis gives agreement of the previous maximal-order reductions on all strictly smaller indices. The next-level order reduction comparison thus gives equal replies to every request. Hence the maximal-order rule has the same output.
-/
private theorem nextLevel_maxOrderReduction_congr (B : PrincipalizationRules.{u}) (L L' : OrderReductionData.{u})
    (T : MarkedIdealWithBoundary.{u})
    (h : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → L.maxOrderRed S = L'.maxOrderRed S) :
    (B.nextLevel L).maxOrderRed T = (B.nextLevel L').maxOrderRed T := by
  have hfun : (fun (S : MarkedIdealWithBoundary.{u}) (_ : S.krullDimSucc ≤ T.krullDimSucc) => (B.nextLevel L).orderRed S)
      = (fun (S : MarkedIdealWithBoundary.{u}) (_ : S.krullDimSucc ≤ T.krullDimSucc) => (B.nextLevel L').orderRed S) := by
    funext S hS
    exact nextLevel_orderReduction_congr B L L' S (fun S' h' => h S' (lt_of_lt_of_le h' hS))
  show B.maxOrderRed T (fun S _ => (B.nextLevel L).orderRed S)
      = B.maxOrderRed T (fun S _ => (B.nextLevel L').orderRed S)
  exact congrArg (B.maxOrderRed T) hfun

/- English proof (authored)
Induct on the given dimension bound. Both levels under comparison are positive, so compute their values by applying the next-level construction to the preceding inputs. At dimension bound zero there can be no strictly smaller auxiliary dimension. The next-level comparisons therefore give equality of both reductions. At a successor bound, every strictly smaller auxiliary input has dimension index at most the preceding bound. The preceding levels are still above that bound and are in the given order. Thus induction gives equality of their maximal-order reductions on each auxiliary input. The next-level comparisons use exactly these equalities to show that both current reductions agree.
-/
private theorem inputLevelData_reductions_eq_of_dim_lt (B : PrincipalizationRules.{u}) :
    ∀ (d : ℕ) (T : MarkedIdealWithBoundary.{u}), T.krullDimSucc ≤ d → ∀ m M : ℕ, d < m → m ≤ M →
      (B.inputLevelData m).maxOrderRed T = (B.inputLevelData M).maxOrderRed T ∧
        (B.inputLevelData m).orderRed T = (B.inputLevelData M).orderRed T := by
  intro d
  induction d with
  | zero =>
      intro T hT m M hm hmM
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      have h0 : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc →
          (B.inputLevelData m').maxOrderRed S = (B.inputLevelData M').maxOrderRed S := by
        intro S hS
        exact absurd (lt_of_lt_of_le hS hT) (Nat.not_lt_zero _)
      exact ⟨nextLevel_maxOrderReduction_congr B (B.inputLevelData m') (B.inputLevelData M') T h0,
        nextLevel_orderReduction_congr B (B.inputLevelData m') (B.inputLevelData M') T h0⟩
  | succ d ih =>
      intro T hT m M hm hmM
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      have h0 : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc →
          (B.inputLevelData m').maxOrderRed S = (B.inputLevelData M').maxOrderRed S := by
        intro S hS
        exact (ih S (by omega) m' M' (by omega) (by omega)).1
      exact ⟨nextLevel_maxOrderReduction_congr B (B.inputLevelData m') (B.inputLevelData M') T h0,
        nextLevel_orderReduction_congr B (B.inputLevelData m') (B.inputLevelData M') T h0⟩

/- English proof (authored)
Induct on the level. At zero there are no natural dimension indices strictly below zero, so the specification holds vacuously. Given the specification for the input at level n, the rule hypotheses give the divisor reduction specifications and their boundary invariance through dimension n. These yield the new order reduction specification. Applying the maximal-order rule gives the maximal-order specification through dimension n for the output. This output is the next input, and being at most n is equivalent to being strictly below n plus one.
-/
private theorem inputLevelData_isMaxOrderReduction (B : PrincipalizationRules.{u}) (hB : B.ReducesInductivelyOnDimension)
    (n : ℕ) :
    IsMaxOrderReduction (fun d => d < n) (B.inputLevelData n).maxOrderRed (B.inputLevelData n).orderRed := by
  induction n with
  | zero => exact isMaxOrderReduction_of_forall_not _ (fun m => Nat.not_lt_zero m) _ _
  | succ n ih =>
      have hord : IsOrderReduction (fun d => d ≤ n) (B.outputLevelData n).orderRed
          (B.inputLevelData n).maxOrderRed :=
        hB.orderSpec n (fun j => B.divisorFamily (B.inputLevelData n).maxOrderRed j)
          (B.inputLevelData n).maxOrderRed (B.inputLevelData n).orderRed ih
          (fun j => hB.divisorSpec n (B.inputLevelData n).maxOrderRed (B.inputLevelData n).orderRed ih j)
          (hB.divisorShift n (B.inputLevelData n).maxOrderRed (B.inputLevelData n).orderRed ih)
      have hmax : IsMaxOrderReduction (fun d => d ≤ n) (B.outputLevelData n).maxOrderRed
          (B.outputLevelData n).orderRed :=
        hB.maxOrderSpec n (B.outputLevelData n).orderRed (B.inputLevelData n).maxOrderRed hord
      exact hmax.mono (fun d => d < n + 1) (fun m hm => Nat.lt_succ_iff.mp hm)

/- English proof (authored)
The input level's maximal-order and order reductions satisfy the specification below the current dimension. Thus the rule hypotheses give the boundary divisor reductions and their boundary invariance through the current dimension. Applying the order rule specification to these procedures gives the claimed order reduction property of the output.
-/
theorem isOrderReduction_outputLevelData (B : PrincipalizationRules.{u}) (hB : B.ReducesInductivelyOnDimension) (n : ℕ) :
    IsOrderReduction (fun d => d ≤ n) (B.outputLevelData n).orderRed (B.inputLevelData n).maxOrderRed :=
  hB.orderSpec n (fun j => B.divisorFamily (B.inputLevelData n).maxOrderRed j)
    (B.inputLevelData n).maxOrderRed (B.inputLevelData n).orderRed
    (inputLevelData_isMaxOrderReduction B hB n)
    (fun j => hB.divisorSpec n (B.inputLevelData n).maxOrderRed (B.inputLevelData n).orderRed
      (inputLevelData_isMaxOrderReduction B hB n) j)
    (hB.divisorShift n (B.inputLevelData n).maxOrderRed (B.inputLevelData n).orderRed
      (inputLevelData_isMaxOrderReduction B hB n))

/- English proof (authored)
The order reduction of the output level satisfies its specification through the current dimension. The maximal-order rule uses this order reduction, so its specification hypothesis gives the required maximal-order reduction property at that level.
-/
theorem isMaxOrderReduction_outputLevelData (B : PrincipalizationRules.{u}) (hB : B.ReducesInductivelyOnDimension) (n : ℕ) :
    IsMaxOrderReduction (fun d => d ≤ n) (B.outputLevelData n).maxOrderRed (B.outputLevelData n).orderRed :=
  hB.maxOrderSpec n (B.outputLevelData n).orderRed (B.inputLevelData n).maxOrderRed
    (isOrderReduction_outputLevelData B hB n)

/- English proof (authored)
The two outputs are the inputs at their respective successor levels. The dimension index of the marked ideal is at most the smaller bound, and both successor levels are strictly above that bound. The stabilization theorem for input levels gives equality of their maximal-order reductions.
-/
theorem outputLevelData_maxOrderReduction_eq_of_le (B : PrincipalizationRules.{u}) {n N : ℕ} (hnN : n ≤ N)
    (T : MarkedIdealWithBoundary.{u}) (hT : T.krullDimSucc ≤ n) :
    (B.outputLevelData N).maxOrderRed T = (B.outputLevelData n).maxOrderRed T :=
  (inputLevelData_reductions_eq_of_dim_lt B n T hT (n + 1) (N + 1) (Nat.lt_succ_self n)
    (Nat.succ_le_succ hnN)).1.symm

/- English proof (authored)
Take the smaller level to be the dimension index of the marked ideal itself. The ideal satisfies this bound by equality, so the comparison with any larger level applies.
-/
theorem outputLevelData_maxOrderReduction_eq_at_dim (B : PrincipalizationRules.{u}) (T : MarkedIdealWithBoundary.{u}) {N : ℕ}
    (hT : T.krullDimSucc ≤ N) :
    (B.outputLevelData N).maxOrderRed T = (B.outputLevelData T.krullDimSucc).maxOrderRed T :=
  outputLevelData_maxOrderReduction_eq_of_le B hT T le_rfl

end PrincipalizationRules

end FunctorialResolution.EmbeddedResolution
