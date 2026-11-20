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
Introduce `K _ _ _ _ h2 𝔞 L hL`. Take `⟨H, art, hH, -, hgen, hact⟩` from `h K h2`. Establish `hjH : (latticeCurve L).j ∈ H`. Rewrite using `[← hgen 𝔞 L hL]`. Conclude with `IntermediateField.mem_adjoin_simple_self K _`.

Establish `: FiniteDimensional K H` using `hH.1.1`. Establish `: IsAbelianGalois K H` using `hH.1.2.1`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hx : IsIntegral K (⟨_, hjH⟩ : H)` using `IsIntegral.of_finite K _`. Conclude with `(IntermediateField.isIntegral_iff.mp hx).isAlgebraic`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨ρ, rfl⟩`. Take `⟨c, hc⟩ : ∃ c, ClassGroup.mk K c = art.symm (ρ.restrictNormal H)` from `ClassGroup.induction (R := 𝓞 K) K (P := fun d => ∃ c, ClassGroup.mk K c = d) (fun c => ⟨c, rfl⟩) _`. Take `⟨L', hL'⟩` from `exists_isIdealLattice h2 (c⁻¹ * 𝔞)`.

Use `⟨c⁻¹ * 𝔞, L', hL', ?_⟩` and prove the remaining obligations. Establish `key` using `hact 𝔞 c L L' hL hL' ⟨_, hjH⟩ rfl`. Rewrite `key` using `[hc, art.apply_symm_apply]`. Use `show _ = ρ (latticeCurve L).j`. Rewrite using `[← key]`.

Conclude with `AlgEquiv.restrictNormal_commutes ρ H ⟨_, hjH⟩`. Introduce and unpack `⟨𝔠, L'', hc, rfl⟩`. Take `⟨ρ, hρ⟩` from `GlobalTheory.GaloisDescent.exists_algEquiv_extend (L := ℂ) (art (ClassGroup.mk K (𝔞 * 𝔠⁻¹)))`. Use `⟨ρ, ?_⟩` and prove the remaining obligations. Establish `hL'' : IsIdealLattice ((𝔞 * 𝔠⁻¹)⁻¹ * 𝔞) L''`.

Rewrite using `[show (𝔞 * 𝔠⁻¹)⁻¹ * 𝔞 = 𝔠 by group]` and apply the resulting hypothesis. Use `show ρ (latticeCurve L).j = _`. Rewrite using `[← hact 𝔞 _ L L'' hL hL'' ⟨_, hjH⟩ rfl]`. Conclude with `hρ ⟨_, hjH⟩`.
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
Establish `hmem : (latticeCurve L').j ∈ MulAction.orbit (ℂ ≃ₐ[K] ℂ) (latticeCurve L).j`. Rewrite using `[(h K h2 𝔞 L hL).2]`. Conclude with `⟨𝔟, L', hL', rfl⟩`. Take `⟨ρ, hρ⟩` from `hmem`. Conclude with `⟨ρ, hρ⟩`.
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
Establish `hmem : ρ (latticeCurve L).j ∈ idealInvariants K`. Rewrite using `[← (h K h2 𝔞 L hL).2]`. Conclude with `⟨ρ, rfl⟩`. Take `⟨𝔟, L', hL', hj⟩` from `hmem`. Conclude with `⟨𝔟, L', hL', hj⟩`.
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
Set `_ : Algebra K ℂ` to `φ.toAlgebra`. Establish `hlat : ∀ (𝔡 : (Ideal (𝓞 K))⁰) (M : PeriodPair), (M.lattice : Set ℂ) = (fun x : 𝓞 K => φ x) '' (𝔡 : Ideal (𝓞 K)) → IsIdealLattice (Units.mk0 ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.mpr (nonZeroDivisors.coe_ne_zero 𝔡))) M`. Introduce `𝔡 M hM`. Unfold `IsIdealLattice`. Rewrite using `[hM]`.

Use extensionality with `z`. Simplify using `only [Set.mem_image, Units.val_mk0, SetLike.mem_coe, FractionalIdeal.mem_coeIdeal]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨algebraMap (𝓞 K) K x, ⟨x, hx, rfl⟩, rfl⟩`.

Introduce and unpack `⟨y, ⟨x, hx, rfl⟩, rfl⟩`. Conclude with `⟨x, hx, rfl⟩`. Take `⟨ρ, hρ⟩` from `h.exists_algEquiv h2 (hlat 𝔠 L hL) (hlat 𝔠' L' hL')`. Use `⟨ρ.toRingEquiv, fun x => ρ.commutes x, ?_⟩` and prove the remaining obligations. Rewrite using `[← latticeCurve_j_eq, ← latticeCurve_j_eq]`.

Conclude with `hρ`.
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
