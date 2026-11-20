import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.LocPBLatTransport

noncomputable section

open scoped Classical

namespace PI.TermAttrConst.UnitaryGroupMassFormula

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.DCRelEquiv PI.DCRelEquiv.UnitaryGroupMassFormula

section GP

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

/- English proof (translation)
The claim follows from `(algebraMap_smul E o v).symm`.
-/
theorem gp_osmul (o : 𝓞 E) (v : S.V) : o • v = (algebraMap (𝓞 E) E o) • v :=
  (algebraMap_smul E o v).symm

/- English proof (translation)
Rewrite using `[gp_osmul, gp_osmul, smul_smul, smul_smul, mul_comm]`.
-/
theorem gp_smul_comm (o : 𝓞 E) (c : E) (v : S.V) : o • (c • v) = c • (o • v) := by
  rw [gp_osmul, gp_osmul, smul_smul, smul_smul, mul_comm]

/- English proof (translation)
Rewrite using `[gp_osmul, gp_osmul, map_smul]`.
-/
theorem gp_map_osmul (n : S.V ≃ₗ[E] S.V) (o : 𝓞 E) (v : S.V) : n (o • v) = o • n v := by
  rw [gp_osmul, gp_osmul, map_smul]

variable (p : Ideal (𝓞 E)) [p.IsPrime]

/- English proof (translation)
Introduce `h`. Apply `hs` to reduce the goal to its premises. Establish `h0 : s = 0` using `FaithfulSMul.algebraMap_injective (𝓞 E) E (h.trans (map_zero _).symm)`. Rewrite using `[h0]`. Conclude with `p.zero_mem`.
-/
theorem gp_ne_zero {s : 𝓞 E} (hs : s ∈ p.primeCompl) : algebraMap (𝓞 E) E s ≠ 0 := by
  intro h
  apply hs
  have h0 : s = 0 := FaithfulSMul.algebraMap_injective (𝓞 E) E (h.trans (map_zero _).symm)
  rw [h0]
  exact p.zero_mem

/- English proof (translation)
Introduce `v hv` and use `(mem_localization_iff p L v).2 ⟨1, p.primeCompl.one_mem, by simpa using hv⟩`.
-/
theorem gp_le_locP (L : Submodule (𝓞 E) S.V) : L ≤ Formalism.HermitianLatticesTheory.localization₂ p L :=
  fun v hv => (mem_localization_iff p L v).2 ⟨1, p.primeCompl.one_mem, by simpa using hv⟩

/- English proof (translation)
Introduce `v hv`. Take `⟨s, hs, hv⟩` from `(mem_localization_iff p L v).1 hv`. Conclude with `(mem_localization_iff p L' v).2 ⟨s, hs, h hv⟩`.
-/
theorem locP_mono {L L' : Submodule (𝓞 E) S.V} (h : L ≤ L') :
    Formalism.HermitianLatticesTheory.localization₂ p L ≤ Formalism.HermitianLatticesTheory.localization₂ p L' := by
  intro v hv
  obtain ⟨s, hs, hv⟩ := (mem_localization_iff p L v).1 hv
  exact (mem_localization_iff p L' v).2 ⟨s, hs, h hv⟩

/- English proof (translation)
Introduce `v hv`. Take `⟨s, hs, hv⟩` from `(mem_localization_iff p _ v).1 hv`. Take `⟨t, ht, hv⟩` from `(mem_localization_iff p L _).1 hv`. Conclude with `(mem_localization_iff p L v).2 ⟨t * s, p.primeCompl.mul_mem ht hs, by rw [mul_smul]; exact hv⟩`.
-/
theorem locP_locP_le (L : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.localization₂ p (Formalism.HermitianLatticesTheory.localization₂ p L) ≤ Formalism.HermitianLatticesTheory.localization₂ p L := by
  intro v hv
  obtain ⟨s, hs, hv⟩ := (mem_localization_iff p _ v).1 hv
  obtain ⟨t, ht, hv⟩ := (mem_localization_iff p L _).1 hv
  exact (mem_localization_iff p L v).2 ⟨t * s, p.primeCompl.mul_mem ht hs, by rw [mul_smul]; exact hv⟩

/- English proof (translation)
The claim follows from `(locP_mono p h).trans (locP_locP_le p L')`.
-/
theorem locP_le {L L' : Submodule (𝓞 E) S.V} (h : L ≤ Formalism.HermitianLatticesTheory.localization₂ p L') :
    Formalism.HermitianLatticesTheory.localization₂ p L ≤ Formalism.HermitianLatticesTheory.localization₂ p L' :=
  (locP_mono p h).trans (locP_locP_le p L')

/- English proof (translation)
The claim follows from `locP_locP_le p L ((mem_localization_iff p _ v).2 ⟨s, hs, h⟩)`.
-/
theorem gp_of_smul {L : Submodule (𝓞 E) S.V} {s : 𝓞 E} (hs : s ∈ p.primeCompl) {v : S.V}
    (h : s • v ∈ Formalism.HermitianLatticesTheory.localization₂ p L) : v ∈ Formalism.HermitianLatticesTheory.localization₂ p L :=
  locP_locP_le p L ((mem_localization_iff p _ v).2 ⟨s, hs, h⟩)

/- English proof (translation)
Take `⟨s, hs, hv⟩` from `(mem_localization_iff p L v).1 hv`. Establish `h1` using `hL _ hv`. Rewrite `h1` using `[gp_osmul]`. Establish `h2` using `U.smul_mem (algebraMap (𝓞 E) E s)⁻¹ h1`. Rewrite `h2` using `[smul_smul, inv_mul_cancel₀ (gp_ne_zero p hs), one_smul]`. Then use the resulting hypothesis.
-/
theorem gp_locP_sub_E {L : Submodule (𝓞 E) S.V} {U : Submodule E S.V} (hL : ∀ w ∈ L, w ∈ U) {v : S.V}
    (hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ p L) : v ∈ U := by
  obtain ⟨s, hs, hv⟩ := (mem_localization_iff p L v).1 hv
  have h1 := hL _ hv
  rw [gp_osmul] at h1
  have h2 := U.smul_mem (algebraMap (𝓞 E) E s)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ (gp_ne_zero p hs), one_smul] at h2

def gpK (M N : Submodule (𝓞 E) S.V) (c : E) : Submodule (𝓞 E) S.V where
  carrier := {k | ∃ μ ∈ Formalism.HermitianLatticesTheory.localization₂ p M, ∃ ν ∈ Formalism.HermitianLatticesTheory.localization₂ p N, k = μ + c • ν}
  zero_mem' := ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  add_mem' := by
    rintro a b ⟨μ, hμ, ν, hν, rfl⟩ ⟨μ', hμ', ν', hν', rfl⟩
    exact ⟨μ + μ', add_mem hμ hμ', ν + ν', add_mem hν hν', by rw [smul_add]; abel⟩
  smul_mem' := by
    rintro o a ⟨μ, hμ, ν, hν, rfl⟩
    exact ⟨o • μ, Submodule.smul_mem _ o hμ, o • ν, Submodule.smul_mem _ o hν,
      by rw [smul_add, gp_smul_comm]⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem gp_mem_K {M N : Submodule (𝓞 E) S.V} {c : E} {k : S.V} :
    k ∈ gpK p M N c ↔ ∃ μ ∈ Formalism.HermitianLatticesTheory.localization₂ p M, ∃ ν ∈ Formalism.HermitianLatticesTheory.localization₂ p N, k = μ + c • ν := Iff.rfl

/- English proof (translation)
Take `⟨μ, hμ, ν, hν, he⟩` from `(gp_mem_K p).1 hk`. Establish `hs0` using `gp_ne_zero p hs`. Use `set t : E := (algebraMap (𝓞 E) E s)⁻¹ with ht`. Establish `hsμ : s • (t • μ) = μ` using `by rw [gp_osmul, smul_smul, ht, mul_inv_cancel₀ hs0, one_smul]`. Establish `hsν : s • (t • ν) = ν` using `by rw [gp_osmul, smul_smul, ht, mul_inv_cancel₀ hs0, one_smul]`.

Use `(gp_mem_K p).2 ⟨t • μ, gp_of_smul p hs (by rw [hsμ]; exact hμ), t • ν, gp_of_smul p hs (by rw [hsν]; exact hν), ?_⟩` and prove the remaining obligations. Establish `hk' : k = t • (s • k)` using `by rw [gp_osmul, smul_smul, ht, inv_mul_cancel₀ hs0, one_smul]`. Rewrite using `[hk', he, smul_add, smul_comm t c ν]`.
-/
theorem gp_K_loc {M N : Submodule (𝓞 E) S.V} {c : E} {s : 𝓞 E} (hs : s ∈ p.primeCompl) {k : S.V}
    (hk : s • k ∈ gpK p M N c) : k ∈ gpK p M N c := by
  obtain ⟨μ, hμ, ν, hν, he⟩ := (gp_mem_K p).1 hk
  have hs0 := gp_ne_zero p hs
  set t : E := (algebraMap (𝓞 E) E s)⁻¹ with ht
  have hsμ : s • (t • μ) = μ := by rw [gp_osmul, smul_smul, ht, mul_inv_cancel₀ hs0, one_smul]
  have hsν : s • (t • ν) = ν := by rw [gp_osmul, smul_smul, ht, mul_inv_cancel₀ hs0, one_smul]
  refine (gp_mem_K p).2 ⟨t • μ, gp_of_smul p hs (by rw [hsμ]; exact hμ),
    t • ν, gp_of_smul p hs (by rw [hsν]; exact hν), ?_⟩
  have hk' : k = t • (s • k) := by rw [gp_osmul, smul_smul, ht, inv_mul_cancel₀ hs0, one_smul]
  rw [hk', he, smul_add, smul_comm t c ν]

/- English proof (translation)
Distinguish the cases in `hc : c = 0`. Rewrite using `[hv, hc, inv_zero, zero_smul]`. Conclude with `zero_mem _`. Take `⟨μ, hμ, ν, hν, he⟩` from `(gp_mem_K p).1 hH`. Establish `hq : v - w - ν = c⁻¹ • (μ - s + s')`.

Establish `ht : t = t' + (μ + c • ν)` using `by rw [← he]; abel`. Rewrite using `[hv, hw, ht, show t' + (μ + c • ν) - s = (μ - s + s') + (t' - s') + c • ν by abel, smul_add, smul_add, smul_smul, inv_mul_cancel₀ hc, one_smul]`. Normalize the expressions using the abelian group laws. Establish `hqU : v - w - ν ∈ U`. Rewrite using `[hq]`.

Use `U.smul_mem _ (U.add_mem (U.sub_mem (gp_locP_sub_E p hMU hμ) hs) (gp_locP_sub_E p hMU hs'))` and prove the remaining obligations. Establish `hqΛ : v - w - ν ∈ Formalism.HermitianLatticesTheory.localization₂ p Λ` using `sub_mem (sub_mem hvΛ (locP_locP_le p Λ (gp_le_locP p _ (hN hwN)))) (locP_locP_le p Λ (locP_mono p hN hν))`. Establish `hqM` using `hsat _ hqΛ hqU`. Establish `hv' : v = (v - w - ν) + w + ν` using `by abel`. Rewrite using `[hv']`.

Use `add_mem (add_mem (locP_mono p le_sup_left hqM) ?_) (locP_mono p le_sup_right hν)` and prove the remaining obligations. Conclude with `gp_le_locP p _ (Submodule.mem_sup_right hwN)`.
-/
theorem gp_core {M Λ N : Submodule (𝓞 E) S.V} {U : Submodule E S.V} {c : E}
    (hsat : ∀ w ∈ Formalism.HermitianLatticesTheory.localization₂ p Λ, w ∈ U → w ∈ Formalism.HermitianLatticesTheory.localization₂ p M) (hMU : ∀ w ∈ M, w ∈ U)
    (hN : N ≤ Formalism.HermitianLatticesTheory.localization₂ p Λ) {t s t' s' v w : S.V}
    (hv : v = c⁻¹ • (t - s)) (hvΛ : v ∈ Formalism.HermitianLatticesTheory.localization₂ p Λ) (hs : s ∈ U)
    (hs' : s' ∈ Formalism.HermitianLatticesTheory.localization₂ p M) (hw : w = c⁻¹ • (t' - s')) (hwN : w ∈ N)
    (hH : t - t' ∈ gpK p M N c) : v ∈ Formalism.HermitianLatticesTheory.localization₂ p (M ⊔ N) := by
  by_cases hc : c = 0
  · rw [hv, hc, inv_zero, zero_smul]
    exact zero_mem _
  obtain ⟨μ, hμ, ν, hν, he⟩ := (gp_mem_K p).1 hH
  have hq : v - w - ν = c⁻¹ • (μ - s + s') := by
    have ht : t = t' + (μ + c • ν) := by rw [← he]; abel
    rw [hv, hw, ht, show t' + (μ + c • ν) - s = (μ - s + s') + (t' - s') + c • ν by abel, smul_add, smul_add,
      smul_smul, inv_mul_cancel₀ hc, one_smul]
    abel
  have hqU : v - w - ν ∈ U := by
    rw [hq]
    refine U.smul_mem _ (U.add_mem (U.sub_mem (gp_locP_sub_E p hMU hμ) hs) (gp_locP_sub_E p hMU hs'))
  have hqΛ : v - w - ν ∈ Formalism.HermitianLatticesTheory.localization₂ p Λ :=
    sub_mem (sub_mem hvΛ (locP_locP_le p Λ (gp_le_locP p _ (hN hwN))))
      (locP_locP_le p Λ (locP_mono p hN hν))
  have hqM := hsat _ hqΛ hqU
  have hv' : v = (v - w - ν) + w + ν := by abel
  rw [hv']
  refine add_mem (add_mem (locP_mono p le_sup_left hqM) ?_) (locP_mono p le_sup_right hν)
  exact gp_le_locP p _ (Submodule.mem_sup_right hwN)

end GP

end PI.TermAttrConst.UnitaryGroupMassFormula
