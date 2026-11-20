import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorsAtPrimeUniqueStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryElementaryDivisorsSplitPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryElementaryDivisorsInertPrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LabChar

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Simplify using the standard rewrite rules. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Rewrite the conclusion using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem conjPl_eq_cP {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)) : conjPl P = GlobalTheory.IdemSupport.cP P := by
  apply HeightOneSpectrum.ext
  show P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) = P.asIdeal.comap (GlobalTheory.IdemSupport.cO D).toRingHom
  have h : Formalism.DivisionValues.cO D.host.E = GlobalTheory.IdemSupport.cO D := rfl
  rw [h]
  have inv : ∀ y, GlobalTheory.IdemSupport.cO D (GlobalTheory.IdemSupport.cO D y) = y := fun y => by
    apply RingOfIntegers.ext
    simp [GlobalTheory.IdemSupport.cO]
  ext x
  rw [Ideal.mem_map_of_equiv, Ideal.mem_comap]
  constructor
  · rintro ⟨y, hy, rfl⟩
    show GlobalTheory.IdemSupport.cO D (GlobalTheory.IdemSupport.cO D y) ∈ P.asIdeal
    rwa [inv]
  · intro hx
    exact ⟨_, hx, inv x⟩

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. It suffices to derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem eq_of_fixed {D : D7} (V : HSp D) {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : Formalism.L2.Theta.AE D}
    (h : IsPrimeIdem P e f) (hc : conjPl P = P) : f = e := by
  rcases id h with ⟨hs, rfl⟩ | ⟨rfl, -⟩
  · exfalso
    have H := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
    have hcc : Formalism.IndefR.Lev.IsConjPl P P := by
      rw [GlobalTheory.IdemSupport.isConjPl_iff, ← conjPl_eq_cP, hc]
    have hs' := H.2.2.2 P P e hs hcc
    have h' : IsPrimeIdem P (cA D e) (cA D e + cA D (cA D e)) := Or.inl ⟨hs', rfl⟩
    have hee := ((H.2.2.1 P e _ h).2.2.2.1 _ _ h').1
    obtain ⟨⟨h1, h2, -⟩, ht⟩ := hs
    have e0 : e = 0 := by
      rw [hee, h1] at h2
      exact h2
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    have := (ht x hx0).1 hx
    apply this
    rw [e0, zero_mul, map_zero]
    exact zero_mem _
  · rfl

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. It suffices to derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

By extensionality, compare the relevant components. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem fixed_of_tie {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D}
    (h : IsPrimeIdem P e e) : conjPl P = P := by
  rcases h with ⟨hs, he⟩ | ⟨-, ⟨v, ε, -, rfl⟩, ht⟩
  · exfalso
    obtain ⟨⟨h1, h2, -⟩, ht⟩ := hs
    have hc : cA D e = 0 := by
      have := he
      nth_rewrite 1 [← add_zero e] at this
      exact (add_left_cancel this).symm
    have e0 : e = 0 := by
      have := congrArg (cA D) hc
      rwa [cA_cA, map_zero] at this
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    apply (ht x hx0).1 hx
    rw [e0, zero_mul, map_zero]
    exact zero_mem _
  · have ht' := GlobalTheory.IdemSupport.Comparison₂.conj ht
    rw [GlobalTheory.IdemSupport.cA_algebraMap] at ht'
    rw [conjPl_eq_cP]
    apply HeightOneSpectrum.ext
    ext x
    by_cases hx : x = 0
    · subst hx; simp only [zero_mem]
    · rw [ht' x hx, ht x hx]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result.

A detailed English derivation is pending.
-/
theorem lab_char (hU : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E) (d d' : List ℤ) (g : GA D V), IsPrimeIdem P e f → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → d.Pairwise (fun a b => b ≤ a) → d'.Pairwise (fun a b => b ≤ a) → DivAt V e (ϖ : D.host.E) d g → DivAt V e (ϖ : D.host.E) d' g → d = d') (hS : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E) (d : List ℤ), Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → d.length = V.rank → ∃ g : GA D V, SuppF V (e + cA D e) g ∧ DivAt V e (ϖ : D.host.E) d g) (hI : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (x : 𝓞 D.host.F) (ϖ : 𝓞 D.host.E) (d : List ℤ), IsPrimeIdem P e e → (ϖ : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → d.length = V.rank → dualLab d = d → ∃ g : GA D V, SuppF V e g ∧ DivAt V e (ϖ : D.host.E) d g) : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), ∀ d : List ℤ, IsLab V P d ↔ d.length = V.rank ∧ d.Pairwise (fun a b => b ≤ a) ∧ (conjPl P = P → dualLab d = d) := by
  intro D V P d
  have H := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  constructor
  · rintro ⟨R, e, f, ϖ, α, -, h, h1, h2, hd, -, -, hα, hD, -, -⟩
    refine ⟨hD.1, hd, fun hc => ?_⟩
    obtain rfl := eq_of_fixed V h hc
    have he : f * f = f := (H.2.2.1 P f f h).1
    obtain ⟨⟨a, b, ha, -, hb, -, hinv⟩, -⟩ :=
      GlobalTheory.InertDoubleCoset.inert_double_cosets V P f h (GlobalTheory.SphLabelOps.exists_real_unif D P) α hα
    have hϖ0 := GlobalTheory.SphLabelOps.unif_ne_zero h2
    have hx := GlobalTheory.DivDual.divAt_inv_and_mul V f (ϖ : D.host.E) d α he hϖ0 hD
    have h3 := hx.2 a ha b hb
    rw [← hinv] at h3
    exact hU V P f f ϖ (dualLab d) d α⁻¹ h h1 h2 (GlobalTheory.SphLabelOps.dualLab_pairwise hd) hd hx.1 h3
  · rintro ⟨hl, hd, hs⟩
    obtain ⟨e, f, h⟩ := H.2.1 P
    obtain ⟨x, y, hy, h1, h2⟩ := GlobalTheory.SphLabelOps.exists_real_unif D P
    by_cases hc : conjPl P = P
    · obtain rfl := eq_of_fixed V h hc
      obtain ⟨g, hg, hD⟩ := hI V P f x y d h hy h1 h2 hl (hs hc)
      exact GlobalTheory.SphLabelOps.isLab_of_divAt h h1 h2 hd hg hD
    · rcases id h with ⟨hi, rfl⟩ | ⟨rfl, -⟩
      · obtain ⟨g, hg, hD⟩ := hS V P e y d hi h1 h2 hl
        exact GlobalTheory.SphLabelOps.isLab_of_divAt h h1 h2 hd hg hD
      · exact absurd (fixed_of_tie h) hc

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem labels_char : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), ∀ d : List ℤ, IsLab V P d ↔ d.length = V.rank ∧ d.Pairwise (fun a b => b ≤ a) ∧ (conjPl P = P → dualLab d = d) :=
  lab_char GlobalTheory.T.elementaryDivisorsAtPrime_unique GlobalTheory.T.exists_unitary_elementaryDivisors_splitPrime GlobalTheory.T.exists_unitary_elementaryDivisors_inertPrime

end GlobalTheory.LabChar
