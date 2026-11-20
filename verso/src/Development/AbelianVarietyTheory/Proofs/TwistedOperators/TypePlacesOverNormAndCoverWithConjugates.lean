import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CPAsIdeal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChiSRfl
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

namespace GlobalTheory.SeeConjRead

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components.

Supply the required witnesses or components. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Supply the required witnesses or components.

Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem places_over_g : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → (∀ PP ∈ R.Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧ ∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ PP ∈ R.Pg, Q = PP ∨ Q = GlobalTheory.IdemSupport.cP PP := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL
  have hPg := hL.Pg
  refine ⟨fun PP hP => ?_, fun Q hQ => ?_⟩
  · obtain ⟨k, hk⟩ := (hPg PP).1 hP
    have h1 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := R.C.P.overP hk
    rw [Nat.cast_mul]
    fin_cases k
    · exact PP.asIdeal.mul_mem_right _ h1
    · exact PP.asIdeal.mul_mem_left _ h1
  · rw [Nat.cast_mul] at hQ
    obtain ⟨k, hk⟩ : ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal := by
      rcases Q.isPrime.mem_or_mem hQ with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    have hc : GlobalTheory.Mem.Chr.ConjPl D.host.conj.toRingEquiv Q (GlobalTheory.IdemSupport.cP Q) := by
      refine (GlobalTheory.Mem.Chr.conjPl_iff_mem _ _ _).2 fun x y hxy => ?_
      have h1 : y = GlobalTheory.IdemSupport.cO D x := by
        apply RingOfIntegers.ext
        rw [hxy, GlobalTheory.IdemSupport.cO_coe]
        exact (Formalism.BasicNotions.bridge_star_holds D.R D.host _).symm
      rw [GlobalTheory.IdemSupport.mem_cP, h1, GlobalTheory.IdemSupport.cO_cO]
    have hsp := (GlobalTheory.Mem.Chr.splitsC_main D.R D.host _ (D.host.g_prime k) (D.nd.g_split k) Q hk).2.2.2
      (R.C.P.pb k) (R.C.P.pb_over k) _ hc
    by_cases hu : Q.under (𝓞 D.host.K) = R.C.P.pb k
    · exact ⟨Q, (hPg Q).2 ⟨k, hu⟩, Or.inl rfl⟩
    · have hu' : (GlobalTheory.IdemSupport.cP Q).under (𝓞 D.host.K) = R.C.P.pb k := by
        by_contra hn
        exact hu (hsp.2.2 hn)
      exact ⟨GlobalTheory.IdemSupport.cP Q, (hPg _).2 ⟨k, hu'⟩, Or.inr (GlobalTheory.StdFrames.cP_cP Q).symm⟩

end GlobalTheory.SeeConjRead
