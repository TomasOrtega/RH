import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMonomialLevelFormDvr
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.MemberReflect

/- English proof (translation)
Introduce `O _ _ _ hic hno hdim W _ _ _ _ g hg hloc I a ha`. Use `haveI := hic`. Use `haveI := hno`. Establish `hDVR : IsDiscreteValuationRing O`. Take `⟨hf, hrad⟩` from `ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.1 hdim`.

Establish `key` using `(IsDiscreteValuationRing.TFAE O hf).out 0 3`. Apply the tactic sequence `try simp only [List.length_cons, List.getElem_cons_succ, List.getElem_cons_zero] at key`. Use `key.2 ⟨inferInstance, maximalIdeal O, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `(isField_iff_maximalIdeal_eq).not.1 hf`. Conclude with `(maximalIdeal.isMaximal O).isPrime`.

Introduce and unpack `P ⟨hP, hPp⟩`. Take `⟨x, hxP, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hP`. Use `le_antisymm (le_maximalIdeal hPp.ne_top) ?_` and prove the remaining obligations. Use `(hrad x hx0).trans ?_` and prove the remaining obligations. Rewrite using `[hPp.radical_le_iff, Ideal.span_singleton_le_iff_mem]`.

Conclude with `hxP`. Use `letI := g.toAlgebra`. Use `haveI : IsLocalHom (algebraMap O W) := hloc`. Use `haveI : Module.Flat O W := by`. Rewrite using `[Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]`.

Introduce `x hx`. Take `⟨⟨r, hr⟩, hrx⟩` from `hx`. Establish `hr0 : r ≠ 0` using `nonZeroDivisors.ne_zero hr`. Establish `h1 : g r * x = 0`. Establish `: r • x = 0` using `hrx`.

Rewrite `this` using `[Algebra.smul_def]`. Conclude with `this`. Establish `h2 : g r ≠ 0` using `fun h => hr0 (hg (by simpa using h))`. Simplify using `using (mul_eq_zero.1 h1).resolve_left h2`. Use `haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := O) (B := W)`.

Rewrite using `[← Ideal.comap_map_eq_self_of_faithfullyFlat (B := W) I, Ideal.mem_comap]`. Conclude with `ha`.
-/
theorem mem_of_map_mem_map : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O], IsIntegrallyClosed O →
    IsNoetherianRing O → ringKrullDim O = 1 → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W →
    ∀ (g : O →+* W), Function.Injective g → IsLocalHom g → ∀ (I : Ideal O) (a : O), g a ∈ I.map g → a ∈ I := by
  intro O _ _ _ hic hno hdim W _ _ _ _ g hg hloc I a ha
  haveI := hic
  haveI := hno
  have hDVR : IsDiscreteValuationRing O := by
    obtain ⟨hf, hrad⟩ := ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.1 hdim
    have key := (IsDiscreteValuationRing.TFAE O hf).out 0 3
    try simp only [List.length_cons, List.getElem_cons_succ, List.getElem_cons_zero] at key
    refine key.2 ⟨inferInstance, maximalIdeal O, ⟨?_, ?_⟩, ?_⟩
    · exact (isField_iff_maximalIdeal_eq).not.1 hf
    · exact (maximalIdeal.isMaximal O).isPrime
    · rintro P ⟨hP, hPp⟩
      obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
      refine le_antisymm (le_maximalIdeal hPp.ne_top) ?_
      refine (hrad x hx0).trans ?_
      rw [hPp.radical_le_iff, Ideal.span_singleton_le_iff_mem]
      exact hxP
  letI := g.toAlgebra
  haveI : IsLocalHom (algebraMap O W) := hloc
  haveI : Module.Flat O W := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    intro x hx
    obtain ⟨⟨r, hr⟩, hrx⟩ := hx
    have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
    have h1 : g r * x = 0 := by
      have : r • x = 0 := hrx
      rw [Algebra.smul_def] at this; exact this
    have h2 : g r ≠ 0 := fun h => hr0 (hg (by simpa using h))
    simpa using (mul_eq_zero.1 h1).resolve_left h2
  haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := O) (B := W)
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := W) I, Ideal.mem_comap]
  exact ha

end GlobalTheory.MemberReflect
