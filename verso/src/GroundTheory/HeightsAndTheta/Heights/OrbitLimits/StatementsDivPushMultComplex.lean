import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def DivPushMultComplex.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I W : Ideal (MRing ι))
    (Wa : Ideal (MRingOver ℂ ι)),
    W ∈ I.minimalPrimes → IsHorizontal W →
    Wa ∈ (W.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes →
    multAt I W = multAt (I.map (MvPolynomial.map (Int.castRingHom ℂ))) Wa

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem DivPushMultComplex.hyps_inhabited :
    (Ideal.span {Xc 2 0} : Ideal (MRing (PBlk 2))) ∈ (Ideal.span {Xc 2 0} : Ideal (MRing (PBlk 2))).minimalPrimes ∧
      IsHorizontal (Ideal.span {Xc 2 0} : Ideal (MRing (PBlk 2))) ∧
      (Ideal.span {X ⟨(), 0⟩} : Ideal (MRingOver ℂ (PBlk 2))) ∈
        ((Ideal.span {Xc 2 0} : Ideal (MRing (PBlk 2))).map
          (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes := by
  have hprime : (Ideal.span {(Xc 2 0 : MRing (PBlk 2))}).IsPrime :=
    (Ideal.span_singleton_prime (X_ne_zero _)).mpr X_prime
  have hprimeC : (Ideal.span {(X ⟨(), 0⟩ : MRingOver ℂ (PBlk 2))}).IsPrime :=
    (Ideal.span_singleton_prime (X_ne_zero _)).mpr X_prime
  refine ⟨?_, ?_, ?_⟩
  · rw [Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  · rw [IsHorizontal, eq_bot_iff]
    intro c hc
    rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hc
    obtain ⟨q, hq⟩ := hc
    have h := congrArg constantCoeff hq
    simpa using h
  · rw [Ideal.map_span, Set.image_singleton, Xc, map_X, Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _

end GroundTheory.Heights₂.Heights.Targets
