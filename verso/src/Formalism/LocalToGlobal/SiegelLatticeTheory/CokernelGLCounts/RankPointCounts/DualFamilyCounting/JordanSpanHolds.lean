import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SplitAtOf

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

/- English proof (translation)
Introduce `K F V _ _ _ _ _ _ _ _ _ _ hK hF P hP n b v`. Establish `hPp` using `hP.isPrime`. Prove the components needed by the constructor for the conclusion. Introduce `hv`. Take `⟨s, hs, hsv⟩` from `Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp hv`.

Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hsv`. Establish `hs0` using `algebraMap_ne_zero_of_mem_hcompl hPp hs`. Use `⟨fun i => algebraMap (𝓞 K) K (c i) / algebraMap (𝓞 K) K s, fun i => div_mem_locRing hPp (c i) hs, ?_⟩` and prove the remaining obligations. Establish `e : v = (algebraMap (𝓞 K) K s)⁻¹ • (algebraMap (𝓞 K) K s • v)`. Rewrite using `[smul_smul, inv_mul_cancel₀ hs0, one_smul]`.

Rewrite using `[e, algebraMap_smul, ← hc, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← algebraMap_smul K (c i) (b i), smul_smul]`. Simplify using `only [div_eq_inv_mul]`. Introduce and unpack `⟨d, hd, rfl⟩`.

Use `Submodule.sum_mem _ fun i _ => smul_mem_loc hPp (hd i) ?_` and prove the remaining obligations. Conclude with `Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem local_span_holds : LocSpan := by
  intro K F V _ _ _ _ _ _ _ _ _ _ hK hF P hP n b v
  have hPp := hP.isPrime
  constructor
  · intro hv
    obtain ⟨s, hs, hsv⟩ := Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp hv
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hsv
    have hs0 := algebraMap_ne_zero_of_mem_hcompl hPp hs
    refine ⟨fun i => algebraMap (𝓞 K) K (c i) / algebraMap (𝓞 K) K s,
      fun i => div_mem_locRing hPp (c i) hs, ?_⟩
    have e : v = (algebraMap (𝓞 K) K s)⁻¹ • (algebraMap (𝓞 K) K s • v) := by
      rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [e, algebraMap_smul, ← hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul K (c i) (b i), smul_smul]
    simp only [div_eq_inv_mul]
  · rintro ⟨d, hd, rfl⟩
    refine Submodule.sum_mem _ fun i _ => smul_mem_loc hPp (hd i) ?_
    exact Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ (Submodule.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Introduce `K F V _ _ _ _ _ _ _ _ _ _ _ L hL 𝔭 h𝔭 n b hb`. Rewrite using `[eq_top_iff, ← hL.span_eq_top, Submodule.span_le]`. Introduce `x hx`. Establish `hx' : x ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range b))`. Rewrite using `[hb]`.

Conclude with `LocF.le_locF 𝔭 L hx`. Take `⟨t, ht, htx⟩` from `(LocF.mem_locF_iff h𝔭.isPrime _ x).mp hx'`. Establish `ht0 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0`. Introduce `h0`. Apply `ht` to reduce the goal to its premises.

Establish `h1 : algebraMap (𝓞 F) (𝓞 K) t = 0` using `FaithfulSMul.algebraMap_injective (𝓞 K) K (by rw [h0, map_zero])`. Establish `h2 : t = 0` using `FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K) (by rw [h1, map_zero])`. Rewrite using `[h2]`. Conclude with `𝔭.zero_mem`. Establish `hmem` using `Submodule.span_le_restrictScalars (𝓞 K) K (Set.range b) htx`.

Establish `e : x = (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ • (algebraMap (𝓞 F) (𝓞 K) t • x)`. Rewrite using `[← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) x, smul_smul, inv_mul_cancel₀ ht0, one_smul]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ hmem`.
-/
theorem jordan_span_holds : JordSpan := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ L hL 𝔭 h𝔭 n b hb
  rw [eq_top_iff, ← hL.span_eq_top, Submodule.span_le]
  intro x hx
  have hx' : x ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) := by
    rw [hb]
    exact LocF.le_locF 𝔭 L hx
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff h𝔭.isPrime _ x).mp hx'
  have ht0 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
    intro h0
    apply ht
    have h1 : algebraMap (𝓞 F) (𝓞 K) t = 0 :=
      FaithfulSMul.algebraMap_injective (𝓞 K) K (by rw [h0, map_zero])
    have h2 : t = 0 := FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K) (by rw [h1, map_zero])
    rw [h2]
    exact 𝔭.zero_mem
  have hmem := Submodule.span_le_restrictScalars (𝓞 K) K (Set.range b) htx
  have e : x = (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ •
      (algebraMap (𝓞 F) (𝓞 K) t • x) := by
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) x, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ hmem

end Formalism.L2.SG.Pf.G3
