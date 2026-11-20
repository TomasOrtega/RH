import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocLocalize
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocQuot
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.RelevantMinimalOfDivCycleNeZero
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PRepresentative
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

/- English proof (translation)
Introduce `F _ K _ _ ι _ P hP 𝒲 h𝒲 h𝒲P`. Use `hP.isPrime` as an intermediate fact. Introduce `W hW y hy`. Establish `hWp` using `h𝒲P W hW`. Establish `: W.IsPrime` using `hWp.1.isPrime`.

Take `⟨c, f, g, hf, hg, hgP, hgW, rfl⟩` from `DegZeroLocQuot.proof F K ι P {W} (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact this) y hy`. Establish `hgW' : g ∉ W` using `hgW W rfl`. Take `⟨e, h, hh, hce, hhS⟩` from `exists_form_avoid_primes (insert P h𝒲.toFinset) (fun W' hW' => by`. Break down `Finset.mem_insert.mp hW' with rfl | hW'` into its components or cases. Conclude with `⟨hP.isPrime, hP.multiHomog, hP.relevant⟩`.

Establish `h'` using `(h𝒲P W' (h𝒲.mem_toFinset.mp hW')).1`. Conclude with `⟨h'.isPrime, h'.multiHomog, h'.relevant⟩) c`. Establish `hhP : h ∉ P` using `hhS P (Finset.mem_insert_self _ _)`. Establish `hh𝒲 : ∀ W' ∈ 𝒲, h ∉ W'` using `fun W' hW' => hhS W' (Finset.mem_insert_of_mem (h𝒲.mem_toFinset.mpr hW'))`. Take `⟨m, hm, hmW⟩` from `exists_form_not_mem_of_isRelevant (H := W) hWp.1.relevant (e - c)`.

Establish `hfm : IsMultiHomog (f * m) e`. Use `IsWeightedHomogeneous.mul hf hm` as an intermediate fact. Rewrite `this` using `[add_tsub_cancel_of_le hce]`. Then use the resulting hypothesis. Establish `hgm : IsMultiHomog (g * m) e`. Use `IsWeightedHomogeneous.mul hg hm` as an intermediate fact.

Rewrite `this` using `[add_tsub_cancel_of_le hce]`. Then use the resulting hypothesis. Establish `hgmW : g * m ∉ W` using `fun h' => (this.mem_or_mem h').elim hgW' hmW`. Establish `hgmP : g * m ∉ P` using `fun h' => hgmW (hWp.2 h')`. Establish `hq0 : ∀ a : MRing ι F, a ∉ P → algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P a) ≠ 0` using `fun a ha => by`. Rewrite using `[Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `ha`. Use `⟨_, div_mem_degZeroLoc P 𝒲 hfm hh hhP hh𝒲, _, div_mem_degZeroLoc P 𝒲 hgm hh hhP hh𝒲, ⟨_, div_mem_degZeroLoc P {W} hh hgm hgmP (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hgmW), ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[div_mul_div_comm, mul_comm, div_self (mul_ne_zero (hq0 _ hhP) (hq0 _ hgmP))]`. Establish `h1` using `hq0 _ hgP`. Establish `h2` using `hq0 _ hhP`.

Simplify using `only [map_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem DegZeroLocLocalize.proof : DegZeroLocLocalize.Statement.{u} := by
  intro F _ K _ _ ι _ P hP 𝒲 h𝒲 h𝒲P
  have := hP.isPrime
  intro W hW y hy
  have hWp := h𝒲P W hW
  have : W.IsPrime := hWp.1.isPrime
  obtain ⟨c, f, g, hf, hg, hgP, hgW, rfl⟩ :=
    DegZeroLocQuot.proof F K ι P {W} (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact this)
      y hy
  have hgW' : g ∉ W := hgW W rfl
  obtain ⟨e, h, hh, hce, hhS⟩ := exists_form_avoid_primes (insert P h𝒲.toFinset)
    (fun W' hW' => by
      rcases Finset.mem_insert.mp hW' with rfl | hW'
      · exact ⟨hP.isPrime, hP.multiHomog, hP.relevant⟩
      · have h' := (h𝒲P W' (h𝒲.mem_toFinset.mp hW')).1
        exact ⟨h'.isPrime, h'.multiHomog, h'.relevant⟩) c
  have hhP : h ∉ P := hhS P (Finset.mem_insert_self _ _)
  have hh𝒲 : ∀ W' ∈ 𝒲, h ∉ W' := fun W' hW' =>
    hhS W' (Finset.mem_insert_of_mem (h𝒲.mem_toFinset.mpr hW'))
  obtain ⟨m, hm, hmW⟩ := exists_form_not_mem_of_isRelevant (H := W) hWp.1.relevant (e - c)
  have hfm : IsMultiHomog (f * m) e := by
    have := IsWeightedHomogeneous.mul hf hm
    rwa [add_tsub_cancel_of_le hce] at this
  have hgm : IsMultiHomog (g * m) e := by
    have := IsWeightedHomogeneous.mul hg hm
    rwa [add_tsub_cancel_of_le hce] at this
  have hgmW : g * m ∉ W := fun h' => (this.mem_or_mem h').elim hgW' hmW
  have hgmP : g * m ∉ P := fun h' => hgmW (hWp.2 h')
  have hq0 : ∀ a : MRing ι F, a ∉ P →
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P a) ≠ 0 :=
    fun a ha => by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact ha
  refine ⟨_, div_mem_degZeroLoc P 𝒲 hfm hh hhP hh𝒲, _, div_mem_degZeroLoc P 𝒲 hgm hh hhP hh𝒲,
    ⟨_, div_mem_degZeroLoc P {W} hh hgm hgmP (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hgmW),
      ?_⟩, ?_⟩
  · rw [div_mul_div_comm, mul_comm, div_self (mul_ne_zero (hq0 _ hhP) (hq0 _ hgmP))]
  · have h1 := hq0 _ hgP
    have h2 := hq0 _ hhP
    simp only [map_mul]
    field_simp

end

end GroundTheory.Heights₂.Heights.FieldNumbers
