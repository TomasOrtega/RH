import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularSemisimpleTorusEllipticElementRealPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerTorusEllipticElementRealPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoefficientRegularCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactRealPlaceTorusClassesSignVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDiscreteSeriesCharacterEqWeylCharacterStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct

namespace GlobalTheory.TrMult

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D V lam S M μa fa hodd hlam hM hμa hfa P ρ dt hdt`. Establish `hf` using `hfa ρ`. Use `(M.ds ρ).1` as an intermediate fact. Use `hμa (placeOf D ρ)` as an intermediate fact. Establish `hl : Formalism.QuantumDeterminants.IsHCParam (M.lam ρ)`.

Take `⟨k, hk⟩` from `hodd`. Use `⟨fun a b hab => ?_, fun a => ⟨lam ρ a - k, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hM, hM]`. Conclude with `hlam ρ hab` after adjusting the coercions. Rewrite using `[hM, hk]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Phi, PhiReal]`. Use `split_ifs with hc`. Take `⟨hfin, y, θ, hbij, hexp, hconj⟩` from `GlobalTheory.T.compactRealPlace_torusClasses_signVectors V M ρ P hc`.

Establish `hval : ∀ q : XSet P (placeOf D ρ).Completion V.gram, orbCls (J` using `V.gram) (μa (placeOf D ρ)) dt (fa (placeOf D ρ)) q = conj (dsChar (M.ε ρ) (M.lam ρ) (θ q)) / (dt.real univ : ℂ) := by`. Introduce `q`. Take `⟨hH, hR, hvol, hcpt⟩` from `GlobalTheory.T.centralizer_torusEllipticElement_realPlace V P ρ dt q.2.choose_spec.choose_spec.2`. Take `⟨g, hg⟩` from `hconj q`. Use `GlobalTheory.T.pseudo_coefficient_regular_character hHC.2.1 M ρ (μa (placeOf D ρ)) (fa (placeOf D ρ)) hl hf _ (GlobalTheory.T.isRegularSemisimple_torusEllipticElement_realPlace V P ρ q.2.choose_spec.choose_spec.2) (hcpt.2 hc) g (θ q) hg (centMeas _ dt)` as an intermediate fact.

Rewrite using `[orbCls, this.orbInt_eq, hvol]`. Establish `: Finite (XSet P (placeOf D ρ).Completion V.gram)` using `hfin.to_subtype`. Establish `hlam' : M.lam ρ = fun a => ((lam ρ a : ℤ) : ℝ)` using `funext (hM ρ)`. Establish `hinj : Function.Injective (cxRoots (embOverOf D ρ).1 P)`. Use `P.2.2.1.separable.map (f := (embOverOf D ρ).1)` as an intermediate fact.

Rewrite `this` using `[cxRoots_spec]`. Conclude with `Polynomial.separable_prod_X_sub_C_iff.1 this`. Establish `h2` using `GlobalTheory.T.finsum_discreteSeriesCharacter_eq_weylCharacter V.rank (M.ε ρ) (lam ρ) (cxRoots (embOverOf D ρ).1 P) _ y θ hodd hinj hbij hexp`. Rewrite using `[finsum_congr hval, hlam', ← h2]`. Use `Fintype.ofFinite (XSet P (placeOf D ρ).Completion V.gram)` as an intermediate fact.

Rewrite using `[finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum, Finset.sum_div]`. Use `(finsum_congr fun q => ?_).trans finsum_zero` and prove the remaining obligations. Take `⟨hH, hR, hvol, hcpt⟩` from `GlobalTheory.T.centralizer_torusEllipticElement_realPlace V P ρ dt q.2.choose_spec.choose_spec.2`. Conclude with `(hf.orb_noncompact _ (GlobalTheory.T.isRegularSemisimple_torusEllipticElement_realPlace V P ρ q.2.choose_spec.choose_spec.2) (mt hcpt.1 hc) _).orbInt_eq`.
-/
theorem realStable_of_harishChandra (hHC : HarishChandraCharacters) : RealStable := by
  intro D V lam S M μa fa hodd hlam hM hμa hfa P ρ dt hdt
  have hf := hfa ρ
  have := (M.ds ρ).1
  have := hμa (placeOf D ρ)
  have hl : Formalism.QuantumDeterminants.IsHCParam (M.lam ρ) := by
    obtain ⟨k, hk⟩ := hodd
    refine ⟨fun a b hab => ?_, fun a => ⟨lam ρ a - k, ?_⟩⟩
    · rw [hM, hM]; exact_mod_cast hlam ρ hab
    · rw [hM, hk]; push_cast; ring
  rw [Phi, PhiReal]
  split_ifs with hc
  · obtain ⟨hfin, y, θ, hbij, hexp, hconj⟩ := GlobalTheory.T.compactRealPlace_torusClasses_signVectors V M ρ P hc
    have hval : ∀ q : XSet P (placeOf D ρ).Completion V.gram, orbCls (J := V.gram) (μa (placeOf D ρ)) dt (fa (placeOf D ρ)) q =
        conj (dsChar (M.ε ρ) (M.lam ρ) (θ q)) / (dt.real univ : ℂ) := by
      intro q
      obtain ⟨hH, hR, hvol, hcpt⟩ := GlobalTheory.T.centralizer_torusEllipticElement_realPlace V P ρ dt q.2.choose_spec.choose_spec.2
      obtain ⟨g, hg⟩ := hconj q
      have := GlobalTheory.T.pseudo_coefficient_regular_character hHC.2.1 M ρ (μa (placeOf D ρ)) (fa (placeOf D ρ)) hl hf _
        (GlobalTheory.T.isRegularSemisimple_torusEllipticElement_realPlace V P ρ q.2.choose_spec.choose_spec.2) (hcpt.2 hc) g (θ q) hg (centMeas _ dt)
      rw [orbCls, this.orbInt_eq, hvol]
    have : Finite (XSet P (placeOf D ρ).Completion V.gram) := hfin.to_subtype
    have hlam' : M.lam ρ = fun a => ((lam ρ a : ℤ) : ℝ) := funext (hM ρ)
    have hinj : Function.Injective (cxRoots (embOverOf D ρ).1 P) := by
      have := P.2.2.1.separable.map (f := (embOverOf D ρ).1)
      rw [cxRoots_spec] at this
      exact Polynomial.separable_prod_X_sub_C_iff.1 this
    have h2 := GlobalTheory.T.finsum_discreteSeriesCharacter_eq_weylCharacter V.rank (M.ε ρ) (lam ρ) (cxRoots (embOverOf D ρ).1 P) _ y θ hodd hinj hbij hexp
    rw [finsum_congr hval, hlam', ← h2]
    have := Fintype.ofFinite (XSet P (placeOf D ρ).Completion V.gram)
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum, Finset.sum_div]
  · refine (finsum_congr fun q => ?_).trans finsum_zero
    obtain ⟨hH, hR, hvol, hcpt⟩ := GlobalTheory.T.centralizer_torusEllipticElement_realPlace V P ρ dt q.2.choose_spec.choose_spec.2
    exact (hf.orb_noncompact _ (GlobalTheory.T.isRegularSemisimple_torusEllipticElement_realPlace V P ρ q.2.choose_spec.choose_spec.2) (mt hcpt.1 hc) _).orbInt_eq

end GlobalTheory.TrMult
