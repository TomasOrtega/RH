import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherSide
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockEqChartRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)

noncomputable section

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

/- English proof (translation)
The claim follows from `mem_locIn.mpr ⟨⟨a, ha⟩, 1, one_not_mem_of_prime hp, by simp⟩`.
-/
theorem subset_locIn_of_prime {A : Subalgebra S Ω} {p : Ideal A} [hp : p.IsPrime] {a : Ω} (ha : a ∈ A) :
    a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p :=
  mem_locIn.mpr ⟨⟨a, ha⟩, 1, one_not_mem_of_prime hp, by simp⟩

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Subfield.closure_le]`. Introduce `u hu`. Take `⟨a, b, _, rfl⟩` from `mem_locIn.mp hu`. Conclude with `div_mem (Subfield.subset_closure a.2) (Subfield.subset_closure b.2)`.

Conclude with `Subfield.closure_mono (fun a ha => subset_locIn_of_prime ha)`.
-/
theorem closure_locIn (A : Subalgebra S Ω) (p : Ideal A) [p.IsPrime] :
    Subfield.closure (IndefiniteRowSideFullHecke.Kleiman2.locIn A p : Set Ω) = Subfield.closure (A : Set Ω) := by
  apply le_antisymm
  · rw [Subfield.closure_le]
    intro u hu
    obtain ⟨a, b, _, rfl⟩ := mem_locIn.mp hu
    exact div_mem (Subfield.subset_closure a.2) (Subfield.subset_closure b.2)
  · exact Subfield.closure_mono (fun a ha => subset_locIn_of_prime ha)

def toLocIn (A : Subalgebra S Ω) (p : Ideal A) [p.IsPrime] : A →+* IndefiniteRowSideFullHecke.Kleiman2.locIn A p :=
  (algebraMap A Ω).codRestrict _ (fun a => subset_locIn_of_prime a.2)

/- English proof (translation)
Set `_` to `(toLocIn A p).toAlgebra`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨b, hb⟩`. Establish `hb' : b ∉ p` using `Ideal.mem_primeCompl_iff.mp hb`. Use `IsUnit.of_mul_eq_one ⟨(b : Ω)⁻¹, mem_locIn.mpr ⟨1, b, hb', by simp⟩⟩ ?_` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show (b : Ω) * (b : Ω)⁻¹ = 1`. Conclude with `mul_inv_cancel₀ (coe_ne_zero_of_not_mem hb')`. Introduce and unpack `⟨u, hu⟩`. Take `⟨a, b, hb, rfl⟩` from `mem_locIn.mp hu`.

Use `⟨(a, ⟨b, Ideal.mem_primeCompl_iff.mpr hb⟩), ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (a : Ω) / b * b = a`. Conclude with `div_mul_cancel₀ _ (coe_ne_zero_of_not_mem hb)`. Introduce `x y h`.

Use `⟨1, ?_⟩` and prove the remaining obligations. Establish `h2 : ((algebraMap A (IndefiniteRowSideFullHecke.Kleiman2.locIn A p) x : IndefiniteRowSideFullHecke.Kleiman2.locIn A p) : Ω) = ((algebraMap A (IndefiniteRowSideFullHecke.Kleiman2.locIn A p) y : IndefiniteRowSideFullHecke.Kleiman2.locIn A p) : Ω)` using `by rw [h]`. Establish `hxy : x = y` using `Subtype.ext h2`. Rewrite using `[hxy]`.
-/
theorem isLocalization_locIn (A : Subalgebra S Ω) (p : Ideal A) [p.IsPrime] :
    letI := (toLocIn A p).toAlgebra
    IsLocalization.AtPrime (IndefiniteRowSideFullHecke.Kleiman2.locIn A p) p := by
  let _ := (toLocIn A p).toAlgebra
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨b, hb⟩
    have hb' : b ∉ p := Ideal.mem_primeCompl_iff.mp hb
    refine IsUnit.of_mul_eq_one ⟨(b : Ω)⁻¹, mem_locIn.mpr ⟨1, b, hb', by simp⟩⟩ ?_
    apply Subtype.ext
    show (b : Ω) * (b : Ω)⁻¹ = 1
    exact mul_inv_cancel₀ (coe_ne_zero_of_not_mem hb')
  · rintro ⟨u, hu⟩
    obtain ⟨a, b, hb, rfl⟩ := mem_locIn.mp hu
    refine ⟨(a, ⟨b, Ideal.mem_primeCompl_iff.mpr hb⟩), ?_⟩
    apply Subtype.ext
    show (a : Ω) / b * b = a
    exact div_mul_cancel₀ _ (coe_ne_zero_of_not_mem hb)
  · intro x y h
    refine ⟨1, ?_⟩
    have h2 : ((algebraMap A (IndefiniteRowSideFullHecke.Kleiman2.locIn A p) x : IndefiniteRowSideFullHecke.Kleiman2.locIn A p) : Ω) =
        ((algebraMap A (IndefiniteRowSideFullHecke.Kleiman2.locIn A p) y : IndefiniteRowSideFullHecke.Kleiman2.locIn A p) : Ω) := by rw [h]
    have hxy : x = y := Subtype.ext h2
    rw [hxy]

/- English proof (translation)
Establish `h' : IndefiniteRowSideFullHecke.Kleiman2.modelPts S y = IndefiniteRowSideFullHecke.Kleiman2.modelPts S y'` using `h`. Establish `hz : IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver S y c) P ∈ IndefiniteRowSideFullHecke.Kleiman2.modelPts S y'`. Rewrite using `[← h']`. Conclude with `⟨c, hc, P, hP, rfl⟩`. Take `⟨c', hc', P', hP', hzz⟩` from `hz`.

Conclude with `⟨c', hc', P', hP', hzz⟩`.
-/
theorem exists_point_of_sameModel {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
    {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι' k) → Ω} (h : IndefiniteRowSideFullHecke.Kleiman2.SameModel S y y')
    {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (P : Ideal (chartRingOver S y c)) [hP : P.IsPrime] :
    ∃ c' : ∀ k, ι' k, (∀ k, y' ⟨k, c' k⟩ ≠ 0) ∧ ∃ P' : Ideal (chartRingOver S y' c'), P'.IsPrime ∧
      IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver S y c) P = IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver S y' c') P' := by
  have h' : IndefiniteRowSideFullHecke.Kleiman2.modelPts S y = IndefiniteRowSideFullHecke.Kleiman2.modelPts S y' := h
  have hz : IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver S y c) P ∈ IndefiniteRowSideFullHecke.Kleiman2.modelPts S y' := by
    rw [← h']
    exact ⟨c, hc, P, hP, rfl⟩
  obtain ⟨c', hc', P', hP', hzz⟩ := hz
  exact ⟨c', hc', P', hP', hzz⟩

/- English proof (translation)
Introduce `c hc`. Take `⟨P, hP⟩` from `Ideal.exists_maximal (chartRingOver S y c)`. Use `hP.isPrime` as an intermediate fact. Take `⟨c', hc', P', hP', hzz⟩` from `exists_point_of_sameModel h hc P`. Use `hP'` as an intermediate fact.

Rewrite using `[← closure_locIn _ P, hzz, closure_locIn]`. Conclude with `hb c' hc'`.
-/
theorem birational_of_sameModel {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
    {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι' k) → Ω} (h : IndefiniteRowSideFullHecke.Kleiman2.SameModel S y y')
    (hb : IndefiniteRowSideFullHecke.Kleiman2.IsBirational S y') : IndefiniteRowSideFullHecke.Kleiman2.IsBirational S y := by
  intro c hc
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (chartRingOver S y c)
  have := hP.isPrime
  obtain ⟨c', hc', P', hP', hzz⟩ := exists_point_of_sameModel h hc P
  have := hP'
  rw [← closure_locIn _ P, hzz, closure_locIn]
  exact hb c' hc'

/- English proof (translation)
Introduce `c hc`. Use `@IsIntegrallyClosed.of_isLocalization_maximal _ _ (fun P _ => IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver S y c) P) (fun _ _ => inferInstance) (fun P _ => (toLocIn _ P).toAlgebra) (fun P _ => isLocalization_locIn _ P) inferInstance (fun P _ => ?_)` and prove the remaining obligations. Take `⟨c', hc', P', hP', hzz⟩` from `exists_point_of_sameModel h hc P`. Use `hP'` as an intermediate fact. Use `hn c' hc'` as an intermediate fact.

Set `_` to `(toLocIn (chartRingOver S y' c') P').toAlgebra`. Use `isLocalization_locIn (chartRingOver S y' c') P'` as an intermediate fact. Use `show IsIntegrallyClosed (IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver S y c) P)`. Rewrite using `[hzz]`. Conclude with `isIntegrallyClosed_of_isLocalization _ P'.primeCompl P'.primeCompl_le_nonZeroDivisors`.
-/
theorem normal_of_sameModel {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
    {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι' k) → Ω} (h : IndefiniteRowSideFullHecke.Kleiman2.SameModel S y y')
    (hn : IndefiniteRowSideFullHecke.Kleiman2.IsNormalModel S y') : IndefiniteRowSideFullHecke.Kleiman2.IsNormalModel S y := by
  intro c hc
  refine @IsIntegrallyClosed.of_isLocalization_maximal _ _
    (fun P _ => IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver S y c) P) (fun _ _ => inferInstance)
    (fun P _ => (toLocIn _ P).toAlgebra) (fun P _ => isLocalization_locIn _ P) inferInstance
    (fun P _ => ?_)
  obtain ⟨c', hc', P', hP', hzz⟩ := exists_point_of_sameModel h hc P
  have := hP'
  have := hn c' hc'
  let _ := (toLocIn (chartRingOver S y' c') P').toAlgebra
  have := isLocalization_locIn (chartRingOver S y' c') P'
  show IsIntegrallyClosed (IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver S y c) P)
  rw [hzz]
  exact isIntegrallyClosed_of_isLocalization _ P'.primeCompl P'.primeCompl_le_nonZeroDivisors

/- English proof (translation)
Introduce `S _ Ω _ _ K _ ι _ K' _ ι' _ y y' _ _ h`. Establish `hs : IndefiniteRowSideFullHecke.Kleiman2.SameModel S y' y` using `Eq.symm h`. Conclude with `⟨⟨birational_of_sameModel hs, birational_of_sameModel h⟩, ⟨normal_of_sameModel hs, normal_of_sameModel h⟩⟩`.
-/
theorem ModelInvariants.full : ModelInvariants.Statement := by
  intro S _ Ω _ _ K _ ι _ K' _ ι' _ y y' _ _ h
  have hs : IndefiniteRowSideFullHecke.Kleiman2.SameModel S y' y := Eq.symm h
  exact ⟨⟨birational_of_sameModel hs, birational_of_sameModel h⟩,
    ⟨normal_of_sameModel hs, normal_of_sameModel h⟩⟩

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
