import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitsLocallyCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactModNormOneKernelInvolution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerSimilitudeBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCentralizerComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqrtFixedNearOneCommutativeCentralizerStatement
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf.TorusNorm

/- English proof (translation)
Set `T : Z × S →* Z × S` to `{ toFun := fun h => (τ h.1 * (ι h.2)⁻¹, h.2⁻¹) map_one' := by simp map_mul' := fun h k => by`. Use `ext`. Use `show τ (h.1 * k.1) * (ι (h.2 * k.2))⁻¹ = τ h.1 * (ι h.2)⁻¹ * (τ k.1 * (ι k.2)⁻¹)`. Rewrite using `[map_mul, map_mul, _root_.mul_inv_rev, hZ (ι k.2)⁻¹ (ι h.2)⁻¹]`. Simplify using `only [mul_assoc]`.

Use `congr 1`. Rewrite using `[← mul_assoc, ← mul_assoc, hZ (ι h.2)⁻¹ (τ k.1)]`. Use `show (h.2 * k.2)⁻¹ = h.2⁻¹ * k.2⁻¹`. Rewrite using `[_root_.mul_inv_rev, hS] }`. Establish `hT : ∀ h, T h = (τ h.1 * (ι h.2)⁻¹, h.2⁻¹)` using `fun h => rfl`.

Establish `hcomm : ∀ a b : Z × S, a * b = b * a` using `fun a b => Prod.ext (hZ _ _) (hS _ _)`. Establish `hTc : Continuous T` using `by show Continuous fun h : Z × S => (τ h.1 * (ι h.2)⁻¹, h.2⁻¹)`. Conclude with `((hτc.comp continuous_fst).mul (hιc.comp continuous_snd).inv).prodMk continuous_snd.inv`. Establish `hTi : ∀ h, T (T h) = h`. Introduce `h`.

Rewrite using `[hT, hT]`. Use `ext`. Simplify using `only [map_mul, map_inv, hτi, hτι, inv_inv]`. Rewrite using `[mul_assoc, inv_mul_cancel, mul_one]`. Simplify using the standard rewrite rules.

Take `⟨W, hW, hWs⟩` from `hsq`. Take `⟨U, hU1, hUs⟩` from `hU`. Establish `hsqT : ∃ W' ∈ nhds (1 : Z × S), ∀ s ∈ W', T s = s → ∃ r : Z × S, T r = r ∧ r * r = s`. Use `⟨W ×ˢ U, prod_mem_nhds hW hU1, fun s hs hTs => ?_⟩` and prove the remaining obligations. Establish `h2 : s.2⁻¹ = s.2` using `congrArg Prod.snd hTs`.

Establish `ha : s.2 = 1` using `hUs _ hs.2 (by`. Combine the equalities or inequalities in the displayed calculation. Establish `h1 : τ s.1 * (ι s.2)⁻¹ = s.1` using `congrArg Prod.fst hTs`. Rewrite `h1` using `[ha, map_one, inv_one, mul_one]`. Take `⟨r, hr, hrr⟩` from `hWs _ hs.1 h1`.

Use `⟨(r, 1), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hT]`. Simplify using `[hr]`. Use `ext`. Conclude with `hrr`.

Simplify using `[ha]`. Use `haveI : T2Space (Z × S) := inferInstance`. Take `⟨B, hB, hBs⟩` from `GlobalTheory.InvolutionNorm.exists_compact_mod_kernel (Z × S) hcomm T hTc hTi hsqT (D ×ˢ {1}) (hD.prod isCompact_singleton)`. Use `⟨Prod.fst '' B, hB.image continuous_fst, fun z a hz => ?_⟩` and prove the remaining obligations. Establish `hmem : T (z, a) * (z, a) ∈ D ×ˢ ({1} : Set S)`.

Rewrite using `[hT]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show τ z * (ι a)⁻¹ * z ∈ D`. Rewrite using `[mul_assoc, hZ (ι a)⁻¹ z, ← mul_assoc]`. Conclude with `hz`.

Use `show a⁻¹ * a = 1`. Conclude with `inv_mul_cancel a`. Take `⟨t, ht, b, hb, hzb⟩` from `hBs _ hmem`. Use `⟨t.1, t.2, ?_, b.1, ⟨b, hb, rfl⟩, congrArg Prod.fst hzb⟩` and prove the remaining obligations. Establish `h1 : τ t.1 * (ι t.2)⁻¹ * t.1 = 1` using `congrArg Prod.fst ht`.

Rewrite `h1` using `[mul_assoc, hZ _ t.1, ← mul_assoc]`. Conclude with `mul_inv_eq_one.1 h1`.
-/
theorem exists_compact_mod_sim (Z S : Type) [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z]
    [LocallyCompactSpace Z] [SigmaCompactSpace Z] [T2Space Z]
    [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [LocallyCompactSpace S] [SigmaCompactSpace S]
    [T2Space S] (hZ : ∀ a b : Z, a * b = b * a) (hS : ∀ a b : S, a * b = b * a)
    (τ : Z →* Z) (hτc : Continuous τ) (hτi : ∀ z, τ (τ z) = z)
    (hsq : ∃ W ∈ nhds (1 : Z), ∀ s ∈ W, τ s = s → ∃ r : Z, τ r = r ∧ r * r = s)
    (ι : S →* Z) (hιc : Continuous ι) (hτι : ∀ a, τ (ι a) = ι a)
    (hU : ∃ U ∈ nhds (1 : S), ∀ a ∈ U, a * a = 1 → a = 1) (D : Set Z) (hD : IsCompact D) :
    ∃ B : Set Z, IsCompact B ∧ ∀ (z : Z) (a : S), τ z * z * (ι a)⁻¹ ∈ D →
      ∃ u : Z, ∃ l : S, τ u * u = ι l ∧ ∃ b ∈ B, z = u * b := by
  let T : Z × S →* Z × S :=
    { toFun := fun h => (τ h.1 * (ι h.2)⁻¹, h.2⁻¹)
      map_one' := by simp
      map_mul' := fun h k => by
        ext
        · show τ (h.1 * k.1) * (ι (h.2 * k.2))⁻¹ = τ h.1 * (ι h.2)⁻¹ * (τ k.1 * (ι k.2)⁻¹)
          rw [map_mul, map_mul, _root_.mul_inv_rev, hZ (ι k.2)⁻¹ (ι h.2)⁻¹]
          simp only [mul_assoc]
          congr 1
          rw [← mul_assoc, ← mul_assoc, hZ (ι h.2)⁻¹ (τ k.1)]
        · show (h.2 * k.2)⁻¹ = h.2⁻¹ * k.2⁻¹
          rw [_root_.mul_inv_rev, hS] }
  have hT : ∀ h, T h = (τ h.1 * (ι h.2)⁻¹, h.2⁻¹) := fun h => rfl
  have hcomm : ∀ a b : Z × S, a * b = b * a := fun a b => Prod.ext (hZ _ _) (hS _ _)
  have hTc : Continuous T := by
    show Continuous fun h : Z × S => (τ h.1 * (ι h.2)⁻¹, h.2⁻¹)
    exact ((hτc.comp continuous_fst).mul (hιc.comp continuous_snd).inv).prodMk continuous_snd.inv
  have hTi : ∀ h, T (T h) = h := by
    intro h
    rw [hT, hT]
    ext
    · simp only [map_mul, map_inv, hτi, hτι, inv_inv]
      rw [mul_assoc, inv_mul_cancel, mul_one]
    · simp
  obtain ⟨W, hW, hWs⟩ := hsq
  obtain ⟨U, hU1, hUs⟩ := hU
  have hsqT : ∃ W' ∈ nhds (1 : Z × S), ∀ s ∈ W', T s = s → ∃ r : Z × S, T r = r ∧ r * r = s := by
    refine ⟨W ×ˢ U, prod_mem_nhds hW hU1, fun s hs hTs => ?_⟩
    have h2 : s.2⁻¹ = s.2 := congrArg Prod.snd hTs
    have ha : s.2 = 1 := hUs _ hs.2 (by
      calc s.2 * s.2 = s.2 * s.2⁻¹ := by rw [h2]
        _ = 1 := mul_inv_cancel _)
    have h1 : τ s.1 * (ι s.2)⁻¹ = s.1 := congrArg Prod.fst hTs
    rw [ha, map_one, inv_one, mul_one] at h1
    obtain ⟨r, hr, hrr⟩ := hWs _ hs.1 h1
    refine ⟨(r, 1), ?_, ?_⟩
    · rw [hT]; simp [hr]
    · ext
      · exact hrr
      · simp [ha]
  haveI : T2Space (Z × S) := inferInstance
  obtain ⟨B, hB, hBs⟩ := GlobalTheory.InvolutionNorm.exists_compact_mod_kernel (Z × S) hcomm T hTc hTi hsqT
    (D ×ˢ {1}) (hD.prod isCompact_singleton)
  refine ⟨Prod.fst '' B, hB.image continuous_fst, fun z a hz => ?_⟩
  have hmem : T (z, a) * (z, a) ∈ D ×ˢ ({1} : Set S) := by
    rw [hT]
    refine ⟨?_, ?_⟩
    · show τ z * (ι a)⁻¹ * z ∈ D
      rw [mul_assoc, hZ (ι a)⁻¹ z, ← mul_assoc]; exact hz
    · show a⁻¹ * a = 1
      exact inv_mul_cancel a
  obtain ⟨t, ht, b, hb, hzb⟩ := hBs _ hmem
  refine ⟨t.1, t.2, ?_, b.1, ⟨b, hb, rfl⟩, congrArg Prod.fst hzb⟩
  have h1 : τ t.1 * (ι t.2)⁻¹ * t.1 = 1 := congrArg Prod.fst ht
  rw [mul_assoc, hZ _ t.1, ← mul_assoc] at h1
  exact mul_inv_eq_one.1 h1

end GlobalTheory.OrbFinAf.TorusNorm

namespace GlobalTheory.OrbFinAf.TorusNorm

end GlobalTheory.OrbFinAf.TorusNorm
