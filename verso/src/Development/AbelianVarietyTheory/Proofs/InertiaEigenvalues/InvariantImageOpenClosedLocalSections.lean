import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryActionHermitianInvariantsTransitiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousCongruenceNearSymmetricMatrixStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompanionMatrixOfCoeffsCharpolyCoeffEqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BorderedMatrixInvariantSpaceExistsCompactOpenSubStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOrbitProperOfInvertibleKrylovColumnsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOnHermitianBlockMatrixOfInvariantsStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.ImgSec

/- English proof (translation)
The claim follows from `GlobalTheory.T.companionMatrixOfCoeffs_charpoly_coeff_eq`.
-/
theorem charpoly_companion_coeff : ∀ (k : Type) [CommRing k] (r : ℕ) (p : Fin r → k) (i : Fin r), (companion p).charpoly.coeff (i : ℕ) = p i := GlobalTheory.T.companionMatrixOfCoeffs_charpoly_coeff_eq
/- English proof (translation)
The claim follows from `GlobalTheory.T.borderedMatrixInvariantSpace_exists_compact_open_subset`.
-/
theorem exists_compact_open_nhd : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (U : Set (Inv r F)) (a₀ : Inv r F), IsOpen U → a₀ ∈ U → ∃ Ω : Set (Inv r F), IsCompact Ω ∧ IsOpen Ω ∧ a₀ ∈ Ω ∧ Ω ⊆ U := GlobalTheory.T.borderedMatrixInvariantSpace_exists_compact_open_subset
/- English proof (translation)
The claim follows from `GlobalTheory.T.unitaryOrbit_proper_of_invertible_krylovColumns`.
-/
theorem isCompact_orbit : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Ω : Set (Inv r F)) (s : Inv r F → Hn r F E) (h : Inv r F → Matrix (Fin r) (Fin r) E), IsCompact Ω → ContinuousOn s Ω → ContinuousOn h Ω → (∀ a ∈ Ω, IsUnit (h a).det ∧ Bm (s a).toGl = h a) → ∀ C : Set (Hn r F E), IsCompact C → IsCompact {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C} := GlobalTheory.T.unitaryOrbit_proper_of_invertible_krylovColumns
/- English proof (translation)
The claim follows from `GlobalTheory.T.continuousOn_hermitianBlockMatrixOfInvariants`.
-/
theorem continuousOn_mkX : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Ω : Set (Inv r F)) (h : Inv r F → Matrix (Fin r) (Fin r) E), ContinuousOn h Ω → (∀ a ∈ Ω, IsUnit (h a).det) → ContinuousOn (fun a => GlobalTheory.JR.ImgSec.mkX a (h a)) Ω := GlobalTheory.T.continuousOn_hermitianBlockMatrixOfInvariants

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] {r : ℕ}

/- English proof (translation)
Unfold `HasInv inv`. Use `Prod.ext ?_ (Prod.ext ?_ ?_)` and prove the remaining obligations. Use function extensionality and compare the values at `i show ((mkX a h).1.1).charpoly.coeff i = algebraMap F E (a.1 i)`. Rewrite using `[mkX_fst hh hd]`. Set `u : (Matrix (Fin r) (Fin r) E)ˣ` to `Matrix.nonsingInvUnit h hd`.

Establish `e : h * (companion a.1).map (algebraMap F E) * h⁻¹ = (u : Matrix (Fin r) (Fin r) E) * (companion a.1).map (algebraMap F E) * (u : Matrix (Fin r) (Fin r) E)⁻¹` using `rfl`. Rewrite using `[e, Matrix.charpoly_units_conj, Matrix.charpoly_map, Polynomial.coeff_map, charpoly_companion_coeff]`. Use function extensionality and compare the values at `i`. Conclude with `mom_mkX hh hd i`. Both sides reduce to the same expression.
-/
theorem hasInv_mkX {a : Inv r F} {h : Matrix (Fin r) (Fin r) E} (hh : hᴴ * h = (hankel a).map (algebraMap F E))
    (hd : IsUnit h.det) : HasInv (mkX a h) a := by
  unfold HasInv inv
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext i
    show ((mkX a h).1.1).charpoly.coeff i = algebraMap F E (a.1 i)
    rw [mkX_fst hh hd]
    let u : (Matrix (Fin r) (Fin r) E)ˣ := Matrix.nonsingInvUnit h hd
    have e : h * (companion a.1).map (algebraMap F E) * h⁻¹ =
        (u : Matrix (Fin r) (Fin r) E) * (companion a.1).map (algebraMap F E) *
          (u : Matrix (Fin r) (Fin r) E)⁻¹ := rfl
    rw [e, Matrix.charpoly_units_conj, Matrix.charpoly_map, Polynomial.coeff_map, charpoly_companion_coeff]
  · funext i; exact mom_mkX hh hd i
  · rfl

end GlobalTheory.JR.ImgSec

open GlobalTheory.JR.ImgSec in

/- English proof (translation)
Introduce `F E _ _ _ _ _ r a₀ hΔ`. Use `haveI := continuousStar (E := E) F`. Take `⟨-, -, -, hcrit⟩` from `GlobalTheory.T.unitary_action_hermitian_invariants_transitive F E r`. Take `⟨Ω₁, κ, hΩ₁, hH₀, hκ, -, hκeq⟩` from `GlobalTheory.T.exists_continuous_congruence_near_symmetric_matrix F E r (hankel a₀) (hankel_isSymm a₀) hΔ`. Use `set φ := algebraMap F E with hφ`.

Set `U : Set (Inv r F)` to `{a | Delta a ≠ 0} ∩ (fun a => hankel a) ⁻¹' Ω₁`. Establish `hU : IsOpen U` using `(isOpen_ne_fun continuous_delta continuous_const).inter (hΩ₁.preimage continuous_hankel)`. Establish `ha₀ : a₀ ∈ U` using `⟨hΔ, hH₀⟩`. Establish `hK : ∀ a ∈ U, (κ (hankel a))ᵀ * hankel a₀ * κ (hankel a) = hankel a` using `fun a ha => hκeq _ ha.2 (hankel_isSymm a)`. Establish `hKd : ∀ a ∈ U, IsUnit (κ (hankel a)).det`.

Introduce `a ha`. Use `isUnit_iff_ne_zero.2 fun h0 => ha.1 ?_` and prove the remaining obligations. Use `congrArg Matrix.det (hK a ha)` as an intermediate fact. Rewrite `this` using `[det_mul, det_mul, h0, mul_zero]`. Conclude with `this.symm`.

Establish `hdm : ∀ M : Matrix (Fin r) (Fin r) F, (M.map φ).det = φ M.det` using `fun M => (RingHom.map_det φ M).symm`. Establish `hKd' : ∀ a ∈ U, IsUnit ((κ (hankel a)).map φ).det` using `fun a ha => by`. Rewrite using `[hdm]`. Conclude with `(hKd a ha).map φ`. Establish `hmapK : ∀ a ∈ U, ((κ (hankel a)).map φ)ᴴ * ((hankel a₀).map φ * (κ (hankel a)).map φ) = (hankel a).map φ`.

Introduce `a ha`. Rewrite using `[ImgSec.conjTranspose_map, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.mul_assoc, hK a ha]`. Establish `transport : ∀ a ∈ U, (∃ h : Matrix (Fin r) (Fin r) E, hᴴ * h = (hankel a).map φ) → ∃ h : Matrix (Fin r) (Fin r) E, hᴴ * h = (hankel a₀).map φ`. Introduce and unpack `a ha ⟨h, hh⟩`. Use `set K' := (κ (hankel a)).map φ`.

Establish `hu' : IsUnit K'ᴴ.det` using `by rw [det_conjTranspose]; exact (hKd' a ha).star`. Use `⟨h * K'⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[conjTranspose_mul, conjTranspose_nonsing_inv]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[nonsing_inv_mul_cancel_left _ _ hu', mul_nonsing_inv_cancel_right _ _ (hKd' a ha)]`.

Use `⟨fun hno => ?_, fun hex => ?_⟩` and prove the remaining obligations. Use `filter_upwards [hU.mem_nhds ha₀] with a ha`. Introduce and unpack `⟨X, hX⟩`. Apply `hno` to reduce the goal to its premises. Rewrite using `[hcrit a₀ hΔ]`.

Conclude with `transport a ha ((hcrit a ha.1).1 ⟨X, hX⟩)`. Take `⟨h₀, hh₀⟩` from `(hcrit a₀ hΔ).1 hex`. Establish `hd₀ : IsUnit h₀.det`. Use `isUnit_iff_ne_zero.2 fun h0 => ?_` and prove the remaining obligations. Use `congrArg Matrix.det hh₀` as an intermediate fact.

Rewrite `this` using `[det_mul, h0, mul_zero, hdm]`. Conclude with `hΔ ((map_eq_zero_iff φ φ.injective).1 this.symm)`. Take `⟨Ω, hΩc, hΩo, ha₀Ω, hΩU⟩` from `exists_compact_open_nhd F E r U a₀ hU ha₀`. Set `hf : Inv r F → Matrix (Fin r) (Fin r) E` to `fun a => h₀ * (κ (hankel a)).map φ`. Establish `hhf : ∀ a ∈ U, (hf a)ᴴ * hf a = (hankel a).map φ`.

Introduce `a ha`. Simplify using `only [hf]`. Rewrite using `[conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc h₀ᴴ, hh₀, hmapK a ha]`. Establish `hdf : ∀ a ∈ U, IsUnit (hf a).det` using `fun a ha => by`. Simplify using `only [hf]`.

Rewrite using `[det_mul]`. Conclude with `hd₀.mul (hKd' a ha)`. Establish `hcf : ContinuousOn hf Ω`. Establish `h1 : ContinuousOn (fun a => κ (hankel a)) Ω` using `hκ.comp continuous_hankel.continuousOn fun a ha => (hΩU ha).2`. Conclude with `continuousOn_const.mul ((continuous_id.matrix_map (continuous_algebraMap F E)).comp_continuousOn h1)`.

Establish `hcs : ContinuousOn (fun a => mkX a (hf a)) Ω` using `continuousOn_mkX F E r Ω hf hcf fun a ha => hdf a (hΩU ha)`. Use `⟨Ω, fun a => mkX a (hf a), hΩc, hΩo, ha₀Ω, hcs, fun a ha => ⟨(hΩU ha).1, hasInv_mkX (hhf a (hΩU ha)) (hdf a (hΩU ha))⟩, ?_⟩` and prove the remaining obligations. Introduce `C hC`. Conclude with `isCompact_orbit F E r Ω (fun a => mkX a (hf a)) hf hΩc hcs hcf (fun a ha => ⟨hdf a (hΩU ha), bm_mkX (hhf a (hΩU ha)) (hdf a (hΩU ha))⟩) C hC`.
-/
theorem GlobalTheory.JR.image_openClosed_section : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (a₀ : Inv r F), Delta a₀ ≠ 0 → ((¬ ∃ X : Hn r F E, HasInv X a₀) → ∀ᶠ a in 𝓝 a₀, ¬ ∃ X : Hn r F E, HasInv X a) ∧ ((∃ X : Hn r F E, HasInv X a₀) → ∃ (Ω : Set (Inv r F)) (s : Inv r F → Hn r F E), IsCompact Ω ∧ IsOpen Ω ∧ a₀ ∈ Ω ∧ ContinuousOn s Ω ∧ (∀ a ∈ Ω, Delta a ≠ 0 ∧ HasInv (s a) a) ∧ ∀ C : Set (Hn r F E), IsCompact C → IsCompact {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C}) := by
  intro F E _ _ _ _ _ r a₀ hΔ
  haveI := continuousStar (E := E) F
  obtain ⟨-, -, -, hcrit⟩ := GlobalTheory.T.unitary_action_hermitian_invariants_transitive F E r
  obtain ⟨Ω₁, κ, hΩ₁, hH₀, hκ, -, hκeq⟩ := GlobalTheory.T.exists_continuous_congruence_near_symmetric_matrix F E r (hankel a₀) (hankel_isSymm a₀) hΔ
  set φ := algebraMap F E with hφ
  let U : Set (Inv r F) := {a | Delta a ≠ 0} ∩ (fun a => hankel a) ⁻¹' Ω₁
  have hU : IsOpen U := (isOpen_ne_fun continuous_delta continuous_const).inter (hΩ₁.preimage continuous_hankel)
  have ha₀ : a₀ ∈ U := ⟨hΔ, hH₀⟩
  have hK : ∀ a ∈ U, (κ (hankel a))ᵀ * hankel a₀ * κ (hankel a) = hankel a :=
    fun a ha => hκeq _ ha.2 (hankel_isSymm a)
  have hKd : ∀ a ∈ U, IsUnit (κ (hankel a)).det := by
    intro a ha
    refine isUnit_iff_ne_zero.2 fun h0 => ha.1 ?_
    have := congrArg Matrix.det (hK a ha)
    rw [det_mul, det_mul, h0, mul_zero] at this
    exact this.symm
  have hdm : ∀ M : Matrix (Fin r) (Fin r) F, (M.map φ).det = φ M.det := fun M => (RingHom.map_det φ M).symm
  have hKd' : ∀ a ∈ U, IsUnit ((κ (hankel a)).map φ).det := fun a ha => by
    rw [hdm]; exact (hKd a ha).map φ
  have hmapK : ∀ a ∈ U, ((κ (hankel a)).map φ)ᴴ * ((hankel a₀).map φ * (κ (hankel a)).map φ) = (hankel a).map φ := by
    intro a ha
    rw [ImgSec.conjTranspose_map, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.mul_assoc, hK a ha]
  have transport : ∀ a ∈ U, (∃ h : Matrix (Fin r) (Fin r) E, hᴴ * h = (hankel a).map φ) →
      ∃ h : Matrix (Fin r) (Fin r) E, hᴴ * h = (hankel a₀).map φ := by
    rintro a ha ⟨h, hh⟩
    set K' := (κ (hankel a)).map φ
    have hu' : IsUnit K'ᴴ.det := by rw [det_conjTranspose]; exact (hKd' a ha).star
    refine ⟨h * K'⁻¹, ?_⟩
    rw [conjTranspose_mul, conjTranspose_nonsing_inv]
    calc K'ᴴ⁻¹ * hᴴ * (h * K'⁻¹) = K'ᴴ⁻¹ * (hᴴ * h) * K'⁻¹ := by simp only [Matrix.mul_assoc]
      _ = K'ᴴ⁻¹ * (K'ᴴ * ((hankel a₀).map φ * K')) * K'⁻¹ := by rw [hh, ← hmapK a ha]
      _ = (hankel a₀).map φ := by
        rw [nonsing_inv_mul_cancel_left _ _ hu', mul_nonsing_inv_cancel_right _ _ (hKd' a ha)]
  refine ⟨fun hno => ?_, fun hex => ?_⟩
  · filter_upwards [hU.mem_nhds ha₀] with a ha
    rintro ⟨X, hX⟩
    apply hno
    rw [hcrit a₀ hΔ]
    exact transport a ha ((hcrit a ha.1).1 ⟨X, hX⟩)
  · obtain ⟨h₀, hh₀⟩ := (hcrit a₀ hΔ).1 hex
    have hd₀ : IsUnit h₀.det := by
      refine isUnit_iff_ne_zero.2 fun h0 => ?_
      have := congrArg Matrix.det hh₀
      rw [det_mul, h0, mul_zero, hdm] at this
      exact hΔ ((map_eq_zero_iff φ φ.injective).1 this.symm)
    obtain ⟨Ω, hΩc, hΩo, ha₀Ω, hΩU⟩ := exists_compact_open_nhd F E r U a₀ hU ha₀
    let hf : Inv r F → Matrix (Fin r) (Fin r) E := fun a => h₀ * (κ (hankel a)).map φ
    have hhf : ∀ a ∈ U, (hf a)ᴴ * hf a = (hankel a).map φ := by
      intro a ha
      simp only [hf]
      rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc h₀ᴴ, hh₀, hmapK a ha]
    have hdf : ∀ a ∈ U, IsUnit (hf a).det := fun a ha => by
      simp only [hf]; rw [det_mul]; exact hd₀.mul (hKd' a ha)
    have hcf : ContinuousOn hf Ω := by
      have h1 : ContinuousOn (fun a => κ (hankel a)) Ω :=
        hκ.comp continuous_hankel.continuousOn fun a ha => (hΩU ha).2
      exact continuousOn_const.mul ((continuous_id.matrix_map (continuous_algebraMap F E)).comp_continuousOn h1)
    have hcs : ContinuousOn (fun a => mkX a (hf a)) Ω :=
      continuousOn_mkX F E r Ω hf hcf fun a ha => hdf a (hΩU ha)
    refine ⟨Ω, fun a => mkX a (hf a), hΩc, hΩo, ha₀Ω, hcs,
      fun a ha => ⟨(hΩU ha).1, hasInv_mkX (hhf a (hΩU ha)) (hdf a (hΩU ha))⟩, ?_⟩
    intro C hC
    exact isCompact_orbit F E r Ω (fun a => mkX a (hf a)) hf hΩc hcs hcf
      (fun a ha => ⟨hdf a (hΩU ha), bm_mkX (hhf a (hΩU ha)) (hdf a (hΩU ha))⟩) C hC
