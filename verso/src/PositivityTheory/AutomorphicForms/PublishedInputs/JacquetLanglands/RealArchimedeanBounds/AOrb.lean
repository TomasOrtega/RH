import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ATrans
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.MemParahoricTimesPrincipalCongruenceIff

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

/- English proof (translation)
Introduce `_ F _ _ c hc x`. Establish `hT` using `UpperTheory.V.Sd.Wc.kcTop F`. Establish `hK0 : IsCompact (K0 F : Set (GF F))` using `((hT.1 (fun _ => 0) (by simp)).2)`. Establish `hKo : IsOpen (Kc c : Set (GF F))` using `(hT.1 c hc).1`. Establish `hs : IsCompact ((fun k : GF F => k * x) '' (K0 F : Set (GF F)))` using `hK0.image (continuous_id.mul continuous_const)`.

Take `⟨t, -, ht⟩` from `hs.elim_nhds_subcover (fun g => (fun y : GF F => g⁻¹ * y) ⁻¹' (Kc c : Set (GF F))) (fun g _ => (hKo.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [(Kc c).one_mem]))`. Use `⟨t, fun k hk => ?_⟩` and prove the remaining obligations. Establish `hm` using `ht ⟨k, hk, rfl⟩`. Simplify using `only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at hm`. Take `⟨g, hg, hgk⟩` from `hm`.

Conclude with `⟨g, hg, g⁻¹ * (k * x), hgk, by rw [mul_inv_cancel_left]⟩`.
-/
theorem aOrb : AMem → AOrb := by
  intro _ F _ _ c hc x
  have hT := UpperTheory.V.Sd.Wc.kcTop F
  have hK0 : IsCompact (K0 F : Set (GF F)) := ((hT.1 (fun _ => 0) (by simp)).2)
  have hKo : IsOpen (Kc c : Set (GF F)) := (hT.1 c hc).1
  have hs : IsCompact ((fun k : GF F => k * x) '' (K0 F : Set (GF F))) :=
    hK0.image (continuous_id.mul continuous_const)
  obtain ⟨t, -, ht⟩ := hs.elim_nhds_subcover (fun g => (fun y : GF F => g⁻¹ * y) ⁻¹' (Kc c : Set (GF F)))
    (fun g _ => (hKo.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [(Kc c).one_mem]))
  refine ⟨t, fun k hk => ?_⟩
  have hm := ht ⟨k, hk, rfl⟩
  simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at hm
  obtain ⟨g, hg, hgk⟩ := hm
  exact ⟨g, hg, g⁻¹ * (k * x), hgk, by rw [mul_inv_cancel_left]⟩

end UpperTheory.Esk
