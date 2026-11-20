import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis

open NumberField
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Published

def idealInvariants (K : Type) [Field K] [NumberField K] [Algebra K ℂ] : Set ℂ :=
  {x | ∃ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L : PeriodPair),
    IsIdealLattice 𝔟 L ∧ (latticeCurve L).j = x}

def IdealInvariantsOneOrbitSt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Algebra K ℂ],
    Module.finrank ℚ K = 2 →
    ∀ (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L : PeriodPair), IsIdealLattice 𝔞 L →
      IsAlgebraic K (latticeCurve L).j ∧
      MulAction.orbit (ℂ ≃ₐ[K] ℂ) (latticeCurve L).j = idealInvariants K

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Use the resulting assumption. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ComplexMultiplicationJSt.oneOrbit (h : ComplexMultiplicationJSt) :
    IdealInvariantsOneOrbitSt := by
  intro K _ _ _ _ h2 𝔞 L hL
  obtain ⟨H, art, hH, -, hgen, hact⟩ := h K h2
  have hjH : (latticeCurve L).j ∈ H := by
    rw [← hgen 𝔞 L hL]
    exact IntermediateField.mem_adjoin_simple_self K _
  have : FiniteDimensional K H := hH.1.1
  have : IsAbelianGalois K H := hH.1.2.1
  refine ⟨?_, ?_⟩
  · have hx : IsIntegral K (⟨_, hjH⟩ : H) := IsIntegral.of_finite K _
    exact (IntermediateField.isIntegral_iff.mp hx).isAlgebraic
  · ext x
    constructor
    · rintro ⟨ρ, rfl⟩
      obtain ⟨c, hc⟩ : ∃ c, ClassGroup.mk K c = art.symm (ρ.restrictNormal H) :=
        ClassGroup.induction (R := 𝓞 K) K (P := fun d => ∃ c, ClassGroup.mk K c = d)
          (fun c => ⟨c, rfl⟩) _
      obtain ⟨L', hL'⟩ := exists_isIdealLattice h2 (c⁻¹ * 𝔞)
      refine ⟨c⁻¹ * 𝔞, L', hL', ?_⟩
      have key := hact 𝔞 c L L' hL hL' ⟨_, hjH⟩ rfl
      rw [hc, art.apply_symm_apply] at key
      show _ = ρ (latticeCurve L).j
      rw [← key]
      exact AlgEquiv.restrictNormal_commutes ρ H ⟨_, hjH⟩
    · rintro ⟨𝔠, L'', hc, rfl⟩
      obtain ⟨ρ, hρ⟩ :=
        GlobalTheory.GaloisDescent.exists_algEquiv_extend (L := ℂ) (art (ClassGroup.mk K (𝔞 * 𝔠⁻¹)))
      refine ⟨ρ, ?_⟩
      have hL'' : IsIdealLattice ((𝔞 * 𝔠⁻¹)⁻¹ * 𝔞) L'' := by
        rwa [show (𝔞 * 𝔠⁻¹)⁻¹ * 𝔞 = 𝔠 by group]
      show ρ (latticeCurve L).j = _
      rw [← hact 𝔞 _ L L'' hL hL'' ⟨_, hjH⟩ rfl]
      exact hρ ⟨_, hjH⟩

section Use

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem IdealInvariantsOneOrbitSt.exists_algEquiv [Algebra K ℂ] (h : IdealInvariantsOneOrbitSt)
    (h2 : Module.finrank ℚ K = 2) {𝔞 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {L L' : PeriodPair}
    (hL : IsIdealLattice 𝔞 L) (hL' : IsIdealLattice 𝔟 L') :
    ∃ ρ : ℂ ≃ₐ[K] ℂ, ρ (latticeCurve L).j = (latticeCurve L').j := by
  have hmem : (latticeCurve L').j ∈ MulAction.orbit (ℂ ≃ₐ[K] ℂ) (latticeCurve L).j := by
    rw [(h K h2 𝔞 L hL).2]
    exact ⟨𝔟, L', hL', rfl⟩
  obtain ⟨ρ, hρ⟩ := hmem
  exact ⟨ρ, hρ⟩

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem IdealInvariantsOneOrbitSt.exists_ideal [Algebra K ℂ] (h : IdealInvariantsOneOrbitSt)
    (h2 : Module.finrank ℚ K = 2) {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {L : PeriodPair}
    (hL : IsIdealLattice 𝔞 L) (ρ : ℂ ≃ₐ[K] ℂ) :
    ∃ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L' : PeriodPair),
      IsIdealLattice 𝔟 L' ∧ (latticeCurve L').j = ρ (latticeCurve L).j := by
  have hmem : ρ (latticeCurve L).j ∈ idealInvariants K := by
    rw [← (h K h2 𝔞 L hL).2]
    exact ⟨ρ, rfl⟩
  obtain ⟨𝔟, L', hL', hj⟩ := hmem
  exact ⟨𝔟, L', hL', hj⟩

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem IdealInvariantsOneOrbitSt.exists_ringEquiv (h : IdealInvariantsOneOrbitSt)
    (h2 : Module.finrank ℚ K = 2) (φ : K →+* ℂ) {𝔠 𝔠' : (Ideal (𝓞 K))⁰} {L L' : PeriodPair}
    (hL : (L.lattice : Set ℂ) = (fun x : 𝓞 K => φ x) '' (𝔠 : Ideal (𝓞 K)))
    (hL' : (L'.lattice : Set ℂ) = (fun x : 𝓞 K => φ x) '' (𝔠' : Ideal (𝓞 K))) :
    ∃ s : ℂ ≃+* ℂ, (∀ x : K, s (φ x) = φ x) ∧
      s (1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) =
        1728 * L'.g₂ ^ 3 / (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2) := by
  let _ : Algebra K ℂ := φ.toAlgebra
  have hlat : ∀ (𝔡 : (Ideal (𝓞 K))⁰) (M : PeriodPair),
      (M.lattice : Set ℂ) = (fun x : 𝓞 K => φ x) '' (𝔡 : Ideal (𝓞 K)) →
      IsIdealLattice (Units.mk0 ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
        (FractionalIdeal.coeIdeal_ne_zero.mpr (nonZeroDivisors.coe_ne_zero 𝔡))) M := by
    intro 𝔡 M hM
    unfold IsIdealLattice
    rw [hM]
    ext z
    simp only [Set.mem_image, Units.val_mk0, SetLike.mem_coe, FractionalIdeal.mem_coeIdeal]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨algebraMap (𝓞 K) K x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
  obtain ⟨ρ, hρ⟩ := h.exists_algEquiv h2 (hlat 𝔠 L hL) (hlat 𝔠' L' hL')
  refine ⟨ρ.toRingEquiv, fun x => ρ.commutes x, ?_⟩
  rw [← latticeCurve_j_eq, ← latticeCurve_j_eq]
  exact hρ

end Use

end GlobalTheory.Published
