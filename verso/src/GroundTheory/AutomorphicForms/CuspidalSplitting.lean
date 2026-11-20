import Mathlib
import GroundTheory.AutomorphicForms.CuspidalSplittingIsotypic
import GroundTheory.AutomorphicForms.LeviStagesProduct
import GroundTheory.AutomorphicForms.LeviStagesExact
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Function Iwasawa

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

/- English proof (translation)
Express the relevant statement in the definitionally equal form `MeasureTheory.Measure.modularCharacterFun g = 1`. Use `borelize H`. Rewrite using `[MeasureTheory.Measure.modularCharacterFun_eq_haarScalarFactor MeasureTheory.Measure.haar g]`. Establish `hcomm : (fun x : H => x * g) = (fun x => g * x)`. Use function extensionality and compare the values at `fun x => Subgroup.mem_center_iff.1 hg x`.

Establish `key : MeasureTheory.Measure.map (fun x : H => x * g) (MeasureTheory.Measure.haar : MeasureTheory.Measure H) = MeasureTheory.Measure.haar`. Rewrite using `[hcomm]`. Conclude with `MeasureTheory.map_mul_left_eq_self _ g`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem modularCharacter_eq_one_of_mem_center {H : Type*} [TopologicalSpace H] [Group H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] {g : H} (hg : g ∈ Subgroup.center H) :
    MeasureTheory.Measure.modularCharacter g = 1 := by
  change MeasureTheory.Measure.modularCharacterFun g = 1
  borelize H
  rw [MeasureTheory.Measure.modularCharacterFun_eq_haarScalarFactor
    MeasureTheory.Measure.haar g]
  have hcomm : (fun x : H => x * g) = (fun x => g * x) :=
    funext fun x => Subgroup.mem_center_iff.1 hg x
  have key : MeasureTheory.Measure.map (fun x : H => x * g)
      (MeasureTheory.Measure.haar : MeasureTheory.Measure H) = MeasureTheory.Measure.haar := by
    rw [hcomm]
    exact MeasureTheory.map_mul_left_eq_self _ g
  calc MeasureTheory.Measure.haarScalarFactor
        (MeasureTheory.Measure.map (fun x : H => x * g)
          (MeasureTheory.Measure.haar : MeasureTheory.Measure H))
        (MeasureTheory.Measure.haar : MeasureTheory.Measure H)
      = MeasureTheory.Measure.haarScalarFactor
          (MeasureTheory.Measure.haar : MeasureTheory.Measure H)
          (MeasureTheory.Measure.haar : MeasureTheory.Measure H) := by congr 1
    _ = 1 := MeasureTheory.Measure.haarScalarFactor_self _

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

/- English proof (translation)
Introduce `z hz`. Take `⟨a, ha⟩` from `Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 hz`. Rewrite using `[mem_levi]`. Introduce `i j hij`. Establish `hij' : i ≠ j` using `fun h => hij (h ▸ rfl)`.

Express the relevant statement in the definitionally equal form `(z : Matrix (Fin n) (Fin n) F) i j = 0`. Rewrite using `[← ha, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij']`.
-/
theorem center_le_levi {α : Type*} [LinearOrder α] (β : Fin n → α) :
    Subgroup.center (GL (Fin n) F) ≤ levi F n β := by
  intro z hz
  obtain ⟨a, ha⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 hz
  rw [mem_levi]
  intro i j hij
  have hij' : i ≠ j := fun h => hij (h ▸ rfl)
  change (z : Matrix (Fin n) (Fin n) F) i j = 0
  rw [← ha, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij']

/- English proof (translation)
Establish `hc : (⟨z, levi_le_blockUpper (center_le_levi β hz)⟩ : blockUpper F n β) ∈ Subgroup.center (blockUpper F n β)` using `Subgroup.mem_center_iff.2 fun p => Subtype.ext (Subgroup.mem_center_iff.1 hz p)`. Express the relevant statement in the definitionally equal form `((NNReal.sqrt (MeasureTheory.Measure.modularCharacter _) : ℝ) : ℂ) = 1`. Rewrite using `[modularCharacter_eq_one_of_mem_center hc]`. Simplify using the standard rewrite rules.
-/
theorem sqrtModular_of_mem_center {α : Type*} [LinearOrder α] {β : Fin n → α}
    {z : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F)) :
    sqrtModular F n β ⟨z, levi_le_blockUpper (center_le_levi β hz)⟩ = 1 := by
  have hc : (⟨z, levi_le_blockUpper (center_le_levi β hz)⟩ : blockUpper F n β) ∈
      Subgroup.center (blockUpper F n β) :=
    Subgroup.mem_center_iff.2 fun p => Subtype.ext (Subgroup.mem_center_iff.1 hz p)
  change ((NNReal.sqrt (MeasureTheory.Measure.modularCharacter _) : ℝ) : ℂ) = 1
  rw [modularCharacter_eq_one_of_mem_center hc]
  simp

/- English proof (translation)
Introduce `z hz f`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Establish `hf` using `((mem_parabolicIndSpace τ).1 f.2).1 ⟨z, levi_le_blockUpper (center_le_levi β hz)⟩ x`. Express the relevant statement in the definitionally equal form `(f : GL (Fin n) F → W) (x * z) = ω z • (f : GL (Fin n) F → W) x`.

Rewrite using `[Subgroup.mem_center_iff.1 hz x]`. Express the relevant statement in the definitionally equal form `(f : GL (Fin n) F → W) (z * x) = _ at hf`. Rewrite using `[hf, sqrtModular_of_mem_center hz, one_smul, leviProj_of_mem_levi (center_le_levi β hz), hτ z hz]`.
-/
theorem hasCentralChar_parabolicInd {α : Type*} [LinearOrder α] {β : Fin n → α}
    {W : Type*} [AddCommGroup W] [Module ℂ W] {τ : Representation ℂ (levi F n β) W}
    {ω : GL (Fin n) F → ℂ}
    (hτ : ∀ z (hz : z ∈ Subgroup.center (GL (Fin n) F)), ∀ w,
      τ ⟨z, center_le_levi β hz⟩ w = ω z • w) :
    HasCentralChar (parabolicInd F n β τ) ω := by
  intro z hz f
  apply Subtype.ext
  funext x
  have hf := ((mem_parabolicIndSpace τ).1 f.2).1 ⟨z, levi_le_blockUpper (center_le_levi β hz)⟩ x
  change (f : GL (Fin n) F → W) (x * z) = ω z • (f : GL (Fin n) F → W) x
  rw [Subgroup.mem_center_iff.1 hz x]
  change (f : GL (Fin n) F → W) (z * x) = _ at hf
  rw [hf, sqrtModular_of_mem_center hz, one_smul, leviProj_of_mem_levi (center_le_levi β hz),
    hτ z hz]

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}

/- English proof (translation)
Introduce `hp`. Take `⟨u₀, hu₀⟩` from `exists_ne_zero_of_isIrreducible (ρ := π)`. Establish `hωπ : HasCentralChar π ω`. Introduce `z hz x`. Take `⟨a, rfl⟩` from `hp x`.

Rewrite using `[← Representation.IntertwiningMap.isIntertwining, (hωτ.toRepresentation A) z hz a, map_smul]`. Take `⟨s, hs⟩` from `exists_lift_of_isSupercuspidal hπ hsc hωπ (isSmooth_toRepresentation (isSmooth_parabolicInd τ) A) (hωτ.toRepresentation A) p hp (Representation.IntertwiningMap.id π)`. Set `Φ` to `(subrepIncl A).comp s`. Establish `hJ` using `hsc β hβ`. Establish `h0 : frobeniusParabolic F n β τ hπ Φ = 0` using `Representation.IntertwiningMap.ext (LinearMap.ext fun x => by`.

Rewrite using `[Subsingleton.elim x 0, map_zero]`. Use the proof step `rfl)`. Establish `hΦ : Φ = 0` using `(frobeniusParabolic F n β τ hπ).injective (h0.trans (map_zero _).symm)`. Establish `h1 : p (s u₀) = u₀` using `congrArg (fun φ : Representation.IntertwiningMap π π => φ u₀) hs`. Establish `h2 : s u₀ = 0` using `Subtype.ext (congrArg (fun φ : Representation.IntertwiningMap π (parabolicInd F n β τ) => φ u₀) hΦ)`.

Rewrite `h1` using `[h2, map_zero]`. Conclude with `hu₀ h1.symm`.
-/
theorem not_surjective_of_le_parabolicInd [π.IsIrreducible] (hπ : IsSmooth π)
    (hsc : IsSupercuspidal π) {β : Fin n → ℕ} (hβ : ∃ i j, β i ≠ β j) {W : Type*}
    [AddCommGroup W] [Module ℂ W] {τ : Representation ℂ (levi F n β) W}
    {ω : GL (Fin n) F → ℂ} (hωτ : HasCentralChar (parabolicInd F n β τ) ω)
    (A : Subrepresentation (parabolicInd F n β τ))
    (p : Representation.IntertwiningMap A.toRepresentation π) : ¬ Surjective p := by
  intro hp
  obtain ⟨u₀, hu₀⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  have hωπ : HasCentralChar π ω := by
    intro z hz x
    obtain ⟨a, rfl⟩ := hp x
    rw [← Representation.IntertwiningMap.isIntertwining, (hωτ.toRepresentation A) z hz a,
      map_smul]
  obtain ⟨s, hs⟩ := exists_lift_of_isSupercuspidal hπ hsc hωπ
    (isSmooth_toRepresentation (isSmooth_parabolicInd τ) A) (hωτ.toRepresentation A) p hp
    (Representation.IntertwiningMap.id π)
  let Φ := (subrepIncl A).comp s
  have hJ := hsc β hβ
  have h0 : frobeniusParabolic F n β τ hπ Φ = 0 :=
    Representation.IntertwiningMap.ext (LinearMap.ext fun x => by
      rw [Subsingleton.elim x 0, map_zero]
      rfl)
  have hΦ : Φ = 0 := (frobeniusParabolic F n β τ hπ).injective (h0.trans (map_zero _).symm)
  have h1 : p (s u₀) = u₀ := congrArg (fun φ : Representation.IntertwiningMap π π => φ u₀) hs
  have h2 : s u₀ = 0 := Subtype.ext (congrArg (fun φ : Representation.IntertwiningMap π
    (parabolicInd F n β τ) => φ u₀) hΦ)
  rw [h2, map_zero] at h1
  exact hu₀ h1.symm

/- English proof (translation)
Establish `hc : ∀ z (hz : z ∈ Subgroup.center (GL (Fin n) F)), ∃ c : ℂ, ∀ w, τ ⟨z, center_le_levi β hz⟩ w = c • w` using `fun z hz => exists_central_character hτ (Subgroup.mem_center_iff.2 fun m => Subtype.ext (Subgroup.mem_center_iff.1 hz m))`. Set `ω : GL (Fin n) F → ℂ` to `fun z => if hz : z ∈ Subgroup.center (GL (Fin n) F) then (hc z hz).choose else 0`. Establish `hωτ : ∀ z (hz : z ∈ Subgroup.center (GL (Fin n) F)), ∀ w, τ ⟨z, center_le_levi β hz⟩ w = ω z • w` using `fun z hz w => by`. Simplify using `only [ω, dif_pos hz]`. Conclude with `(hc z hz).choose_spec w`.

Conclude with `not_surjective_of_le_parabolicInd hπ hsc hβ (hasCentralChar_parabolicInd hωτ) A p`.
-/
theorem not_surjective_of_isIrreducible [π.IsIrreducible] (hπ : IsSmooth π)
    (hsc : IsSupercuspidal π) {β : Fin n → ℕ} (hβ : ∃ i j, β i ≠ β j) {W : Type*}
    [AddCommGroup W] [Module ℂ W] {τ : Representation ℂ (levi F n β) W} [τ.IsIrreducible]
    (hτ : IsSmooth τ) (A : Subrepresentation (parabolicInd F n β τ))
    (p : Representation.IntertwiningMap A.toRepresentation π) : ¬ Surjective p := by
  classical
  have hc : ∀ z (hz : z ∈ Subgroup.center (GL (Fin n) F)), ∃ c : ℂ, ∀ w,
      τ ⟨z, center_le_levi β hz⟩ w = c • w := fun z hz =>
    exists_central_character hτ (Subgroup.mem_center_iff.2 fun m =>
      Subtype.ext (Subgroup.mem_center_iff.1 hz m))
  let ω : GL (Fin n) F → ℂ := fun z =>
    if hz : z ∈ Subgroup.center (GL (Fin n) F) then (hc z hz).choose else 0
  have hωτ : ∀ z (hz : z ∈ Subgroup.center (GL (Fin n) F)), ∀ w,
      τ ⟨z, center_le_levi β hz⟩ w = ω z • w := fun z hz w => by
    simp only [ω, dif_pos hz]
    exact (hc z hz).choose_spec w
  exact not_surjective_of_le_parabolicInd hπ hsc hβ (hasCentralChar_parabolicInd hωτ) A p

end Parabolic

end GroundTheory.Automorphic
