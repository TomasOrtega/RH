import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DistribHaarCharTransport
open GlobalTheory.JR MeasureTheory
open scoped Pointwise

namespace GlobalTheory.JR.EtProdAbs

/- English proof (translation)
Use `borelize R₁ R₂`. Set `μ₁ : Measure R₁` to `Measure.addHaar`. Set `μ₂ : Measure R₂` to `Measure.addHaar`. Take `⟨S₁⟩ : Nonempty (TopologicalSpace.PositiveCompacts R₁)` from `inferInstance`. Take `⟨S₂⟩ : Nonempty (TopologicalSpace.PositiveCompacts R₂)` from `inferInstance`.

Establish `h0₁ : μ₁ (S₁ : Set R₁) ≠ 0` using `(Measure.measure_pos_of_nonempty_interior μ₁ S₁.interior_nonempty).ne'`. Establish `h0₂ : μ₂ (S₂ : Set R₂) ≠ 0` using `(Measure.measure_pos_of_nonempty_interior μ₂ S₂.interior_nonempty).ne'`. Establish `h1₁ : μ₁ (S₁ : Set R₁) ≠ ⊤` using `S₁.isCompact.measure_lt_top.ne`. Establish `h1₂ : μ₂ (S₂ : Set R₂) ≠ ⊤` using `S₂.isCompact.measure_lt_top.ne`. Use `distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ₁.prod μ₂) (s := (S₁ : Set R₁) ×ˢ (S₂ : Set R₂)) (by rw [Measure.prod_prod]; exact mul_ne_zero h0₁ h0₂) (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top h1₁ h1₂) ?_` and prove the remaining obligations.

Establish `hs : v • ((S₁ : Set R₁) ×ˢ (S₂ : Set R₂)) = (Units.map (RingHom.fst R₁ R₂ : R₁ × R₂ →* R₁) v • (S₁ : Set R₁)) ×ˢ (Units.map (RingHom.snd R₁ R₂ : R₁ × R₂ →* R₂) v • (S₂ : Set R₂))`. Use extensionality with `⟨x, y⟩`. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem, Set.mem_prod, Set.mem_prod, Set.mem_smul_set_iff_inv_smul_mem, Set.mem_smul_set_iff_inv_smul_mem, ← map_inv, ← map_inv]`. Conclude with `Iff.rfl`. Rewrite using `[hs, Measure.prod_prod, Measure.prod_prod, ← distribHaarChar_mul μ₁, ← distribHaarChar_mul μ₂]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem distribHaarChar_prod {R₁ R₂ : Type} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [LocallyCompactSpace R₁] [T2Space R₁] [SecondCountableTopology R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂]
    [LocallyCompactSpace R₂] [T2Space R₂] [SecondCountableTopology R₂] (v : (R₁ × R₂)ˣ) :
    distribHaarChar (R₁ × R₂) v =
      distribHaarChar R₁ (Units.map (RingHom.fst R₁ R₂ : R₁ × R₂ →* R₁) v) *
        distribHaarChar R₂ (Units.map (RingHom.snd R₁ R₂ : R₁ × R₂ →* R₂) v) := by
  borelize R₁ R₂
  let μ₁ : Measure R₁ := Measure.addHaar
  let μ₂ : Measure R₂ := Measure.addHaar
  obtain ⟨S₁⟩ : Nonempty (TopologicalSpace.PositiveCompacts R₁) := inferInstance
  obtain ⟨S₂⟩ : Nonempty (TopologicalSpace.PositiveCompacts R₂) := inferInstance
  have h0₁ : μ₁ (S₁ : Set R₁) ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ₁ S₁.interior_nonempty).ne'
  have h0₂ : μ₂ (S₂ : Set R₂) ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ₂ S₂.interior_nonempty).ne'
  have h1₁ : μ₁ (S₁ : Set R₁) ≠ ⊤ := S₁.isCompact.measure_lt_top.ne
  have h1₂ : μ₂ (S₂ : Set R₂) ≠ ⊤ := S₂.isCompact.measure_lt_top.ne
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ₁.prod μ₂) (s := (S₁ : Set R₁) ×ˢ (S₂ : Set R₂))
    (by rw [Measure.prod_prod]; exact mul_ne_zero h0₁ h0₂)
    (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top h1₁ h1₂) ?_
  have hs : v • ((S₁ : Set R₁) ×ˢ (S₂ : Set R₂)) =
      (Units.map (RingHom.fst R₁ R₂ : R₁ × R₂ →* R₁) v • (S₁ : Set R₁)) ×ˢ
        (Units.map (RingHom.snd R₁ R₂ : R₁ × R₂ →* R₂) v • (S₂ : Set R₂)) := by
    ext ⟨x, y⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_prod, Set.mem_prod, Set.mem_smul_set_iff_inv_smul_mem,
      Set.mem_smul_set_iff_inv_smul_mem, ← map_inv, ← map_inv]
    exact Iff.rfl
  rw [hs, Measure.prod_prod, Measure.prod_prod, ← distribHaarChar_mul μ₁, ← distribHaarChar_mul μ₂]
  push_cast
  ring

/- English proof (translation)
Introduce `F E _ _ _ _ U A A₁ A₂ eK t`. Use `U.ultraF` as an intermediate fact. Use `U.lcF` as an intermediate fact. Take `⟨_, _, _, _, -⟩` from `EtMeas.top_facts F A.K`. Take `⟨_, _, _, _, -⟩` from `EtMeas.top_facts F A₁.K`.

Take `⟨_, _, _, _, -⟩` from `EtMeas.top_facts F A₂.K`. Distinguish the cases in `ht : IsUnit t`. Set `u : A.Kˣ` to `ht.unit`. Set `v : (A₁.K × A₂.K)ˣ` to `Units.map (eK : A.K →* A₁.K × A₂.K) u`. Set `e' : A.K ≃ₜ+ A₁.K × A₂.K` to `{ eK.toAddEquiv with continuous_toFun := IsModuleTopology.continuous_of_linearMap eK.toLinearMap continuous_invFun := IsModuleTopology.continuous_of_linearMap eK.symm.toLinearMap }`.

Establish `h1 : distribHaarChar (A₁.K × A₂.K) v = distribHaarChar A.K u` using `ModuleNorm.distribHaarChar_transport e' u v (fun x => by`. Express the relevant statement in the definitionally equal form `eK ((u : A.K) * x) = eK (u : A.K) * eK x`. Rewrite using `[map_mul])`. Rewrite `h1` using `[distribHaarChar_prod]`. Establish `ht' : t = (u : A.K)` using `(IsUnit.unit_spec ht).symm`.

Establish `e1 : (eK t).1 = ((Units.map (RingHom.fst A₁.K A₂.K : A₁.K × A₂.K →* A₁.K) v : A₁.Kˣ) : A₁.K)`. Rewrite using `[ht']`. Both sides reduce to the same expression. Establish `e2 : (eK t).2 = ((Units.map (RingHom.snd A₁.K A₂.K : A₁.K × A₂.K →* A₂.K) v : A₂.Kˣ) : A₂.K)`. Rewrite using `[ht']`.

Both sides reduce to the same expression. Rewrite using `[e1, e2, ht', EtMeas.absK_unit, EtMeas.absK_unit, EtMeas.absK_unit, ← h1]`. Use `push_cast`. Both sides reduce to the same expression. Establish `h0 : A.absK t = 0` using `by simp [Et.absK, ht]`.

Establish `hn : ¬ IsUnit (eK t)` using `fun h => ht ((isUnit_map_iff eK t).1 h)`. Rewrite `hn` using `[Prod.isUnit_iff, not_and_or]`. Rewrite using `[h0]`. Break down `hn with hn | hn` into its components or cases. Establish `: A₁.absK (eK t).1 = 0` using `by simp [Et.absK, hn]`.

Rewrite using `[this, zero_mul]`. Establish `: A₂.absK (eK t).2 = 0` using `by simp [Et.absK, hn]`. Rewrite using `[this, mul_zero]`.
-/
theorem absK_prod : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (t : A.K),
    A.absK t = A₁.absK (eK t).1 * A₂.absK (eK t).2 := by
  intro F E _ _ _ _ U A A₁ A₂ eK t
  have := U.ultraF; have := U.lcF
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A₁.K
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A₂.K
  by_cases ht : IsUnit t
  · let u : A.Kˣ := ht.unit
    let v : (A₁.K × A₂.K)ˣ := Units.map (eK : A.K →* A₁.K × A₂.K) u
    let e' : A.K ≃ₜ+ A₁.K × A₂.K :=
      { eK.toAddEquiv with
        continuous_toFun := IsModuleTopology.continuous_of_linearMap eK.toLinearMap
        continuous_invFun := IsModuleTopology.continuous_of_linearMap eK.symm.toLinearMap }
    have h1 : distribHaarChar (A₁.K × A₂.K) v = distribHaarChar A.K u :=
      ModuleNorm.distribHaarChar_transport e' u v (fun x => by
        change eK ((u : A.K) * x) = eK (u : A.K) * eK x
        rw [map_mul])
    rw [distribHaarChar_prod] at h1
    have ht' : t = (u : A.K) := (IsUnit.unit_spec ht).symm
    have e1 : (eK t).1 = ((Units.map (RingHom.fst A₁.K A₂.K : A₁.K × A₂.K →* A₁.K) v : A₁.Kˣ) : A₁.K) := by
      rw [ht']; rfl
    have e2 : (eK t).2 = ((Units.map (RingHom.snd A₁.K A₂.K : A₁.K × A₂.K →* A₂.K) v : A₂.Kˣ) : A₂.K) := by
      rw [ht']; rfl
    rw [e1, e2, ht', EtMeas.absK_unit, EtMeas.absK_unit, EtMeas.absK_unit, ← h1]
    push_cast
    rfl
  · have h0 : A.absK t = 0 := by simp [Et.absK, ht]
    have hn : ¬ IsUnit (eK t) := fun h => ht ((isUnit_map_iff eK t).1 h)
    rw [Prod.isUnit_iff, not_and_or] at hn
    rw [h0]
    rcases hn with hn | hn
    · have : A₁.absK (eK t).1 = 0 := by simp [Et.absK, hn]
      rw [this, zero_mul]
    · have : A₂.absK (eK t).2 = 0 := by simp [Et.absK, hn]
      rw [this, mul_zero]

end GlobalTheory.JR.EtProdAbs
