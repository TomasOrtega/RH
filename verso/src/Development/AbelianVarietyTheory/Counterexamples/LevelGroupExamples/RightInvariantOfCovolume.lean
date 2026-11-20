import Mathlib

noncomputable section
open MeasureTheory
open scoped Pointwise
namespace GlobalTheory.AutQuotCheck

section Alg
variable {G : Type} [Group G] (Γ : Subgroup G)

abbrev cls (g : G) : Quotient (QuotientGroup.rightRel Γ) := Quotient.mk _ g

open MeasureTheory in
open scoped Pointwise in
variable {G : Type} [Group G] (Γ : Subgroup G) in

/- English proof (translation)
Rewrite using `[Quotient.eq, QuotientGroup.rightRel_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨g' * g⁻¹, h, by group⟩`. Introduce and unpack `⟨γ, hγ, rfl⟩`.

Simplify using `using hγ`.
-/
theorem _root_.GlobalTheory.AutQuotCheck.cls_eq_iff (g g' : G) :
    _root_.GlobalTheory.AutQuotCheck.cls Γ g = _root_.GlobalTheory.AutQuotCheck.cls Γ g' ↔ ∃ γ ∈ Γ, g' = γ * g := by
  rw [Quotient.eq, QuotientGroup.rightRel_apply]
  constructor
  · intro h
    exact ⟨g' * g⁻¹, h, by group⟩
  · rintro ⟨γ, hγ, rfl⟩
    simpa using hγ

open MeasureTheory in
open scoped Pointwise in
variable {G : Type} [Group G] (Γ : Subgroup G) in
/- English proof (translation)
Rewrite using `[_root_.GlobalTheory.AutQuotCheck.cls_eq_iff]`. Use `⟨(γ : G)⁻¹, Γ.inv_mem γ.2, ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.smul_def, smul_eq_mul, inv_mul_cancel_left]`.
-/
theorem _root_.GlobalTheory.AutQuotCheck.cls_smul (γ : Γ) (x : G) :
    _root_.GlobalTheory.AutQuotCheck.cls Γ (γ • x) = _root_.GlobalTheory.AutQuotCheck.cls Γ x := by
  rw [_root_.GlobalTheory.AutQuotCheck.cls_eq_iff]
  refine ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, ?_⟩
  rw [Subgroup.smul_def, smul_eq_mul, inv_mul_cancel_left]

open MeasureTheory in
open scoped Pointwise in
variable {G : Type} [Group G] (Γ : Subgroup G) in
/- English proof (translation)
Introduce `_ hs` and use `hs`.
-/
theorem _root_.GlobalTheory.AutQuotCheck.measurable_cls [MeasurableSpace G] :
    Measurable (_root_.GlobalTheory.AutQuotCheck.cls Γ) := fun _ hs => hs

open MeasureTheory in
open scoped Pointwise in
variable {G : Type} [Group G] (Γ : Subgroup G) in

/- English proof (translation)
Use extensionality with `s hs`. Establish `hA` using `_root_.GlobalTheory.AutQuotCheck.measurable_cls Γ hs`. Rewrite using `[Measure.map_apply (_root_.GlobalTheory.AutQuotCheck.measurable_cls Γ) hs, Measure.map_apply (_root_.GlobalTheory.AutQuotCheck.measurable_cls Γ) hs, Measure.restrict_apply hA, Measure.restrict_apply hA]`. Use `h.measure_set_eq h' hA fun γ => ?_` and prove the remaining obligations. Use extensionality with `x`.

Simplify using `only [Set.mem_preimage, _root_.GlobalTheory.AutQuotCheck.cls_smul]`.
-/
theorem _root_.GlobalTheory.AutQuotCheck.map_restrict_eq [MeasurableSpace G] [Countable Γ]
    [MeasurableConstSMul Γ G] (μ : Measure G) [SMulInvariantMeasure Γ G μ] {F F' : Set G}
    (h : IsFundamentalDomain Γ F μ) (h' : IsFundamentalDomain Γ F' μ) :
    (μ.restrict F).map (_root_.GlobalTheory.AutQuotCheck.cls Γ) =
      (μ.restrict F').map (_root_.GlobalTheory.AutQuotCheck.cls Γ) := by
  ext s hs
  have hA := _root_.GlobalTheory.AutQuotCheck.measurable_cls Γ hs
  rw [Measure.map_apply (_root_.GlobalTheory.AutQuotCheck.measurable_cls Γ) hs,
    Measure.map_apply (_root_.GlobalTheory.AutQuotCheck.measurable_cls Γ) hs,
    Measure.restrict_apply hA, Measure.restrict_apply hA]
  refine h.measure_set_eq h' hA fun γ => ?_
  ext x
  simp only [Set.mem_preimage, _root_.GlobalTheory.AutQuotCheck.cls_smul]

/- English proof (translation)
Rewrite using `[Measure.map_apply (measurable_cls Γ) MeasurableSet.univ]`. Simplify using the standard rewrite rules.
-/
theorem map_dirac_one_univ_eq_one [MeasurableSpace G] :
    (((Measure.dirac (1 : G)).restrict Set.univ).map (cls Γ)) Set.univ = 1 := by
  rw [Measure.map_apply (measurable_cls Γ) MeasurableSet.univ]
  simp

end Alg

section Top
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [Countable Γ]

open MeasureTheory in
open scoped Pointwise in
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [Countable Γ] in

/- English proof (translation)
Use `haveI := Measure.isHaarMeasure_map_mul_right μ g`. Establish `hc` using `Measure.isMulLeftInvariant_eq_smul (μ.map (· * g)) μ`. Establish `hF' : IsFundamentalDomain Γ ((· * g) ⁻¹' F) μ` using `h.preimage_of_equiv (quasiMeasurePreserving_mul_right μ g) Function.bijective_id fun γ x => by simp [Subgroup.smul_def, mul_assoc]`. Establish `hmeas : μ.map (· * g) F = μ F`. Rewrite using `[show (· * g) = (MeasurableEquiv.mulRight g : G → G) from rfl, MeasurableEquiv.map_apply]`.

Conclude with `hF'.measure_eq h`. Establish `hc1 : (μ.map (· * g)).haarScalarFactor μ = 1`. Rewrite `hmeas` using `[hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]`. Conclude with `ENNReal.coe_eq_one.mp ((ENNReal.mul_eq_right h0 h1).mp hmeas)`. Rewrite using `[hc, hc1, one_smul]`.
-/
theorem _root_.GlobalTheory.AutQuotCheck.rightInvariant_of_covolume (μ : Measure G) [μ.IsHaarMeasure] {F : Set G}
    (h : IsFundamentalDomain Γ F μ) (h0 : μ F ≠ 0) (h1 : μ F ≠ ⊤) (g : G) :
    μ.map (· * g) = μ := by
  haveI := Measure.isHaarMeasure_map_mul_right μ g
  have hc := Measure.isMulLeftInvariant_eq_smul (μ.map (· * g)) μ
  have hF' : IsFundamentalDomain Γ ((· * g) ⁻¹' F) μ :=
    h.preimage_of_equiv (quasiMeasurePreserving_mul_right μ g) Function.bijective_id
      fun γ x => by simp [Subgroup.smul_def, mul_assoc]
  have hmeas : μ.map (· * g) F = μ F := by
    rw [show (· * g) = (MeasurableEquiv.mulRight g : G → G) from rfl,
      MeasurableEquiv.map_apply]
    exact hF'.measure_eq h
  have hc1 : (μ.map (· * g)).haarScalarFactor μ = 1 := by
    rw [hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hmeas
    exact ENNReal.coe_eq_one.mp ((ENNReal.mul_eq_right h0 h1).mp hmeas)
  rw [hc, hc1, one_smul]

/- English proof (translation)
Establish `e` using `Measure.isMulLeftInvariant_eq_smul μ ν`. Establish `hc0` using `Measure.haarScalarFactor_pos_of_isHaarMeasure μ ν`. Use `set c := Measure.haarScalarFactor μ ν with hc`. Establish `hF' : IsFundamentalDomain Γ F' μ`. Use `h'.mono ?_` and prove the remaining obligations.

Rewrite using `[e]`. Conclude with `Measure.smul_absolutelyContinuous`. Establish `e' : μ = (c : ENNReal) • ν` using `e`. Establish `hq2 : (μ.restrict F).map (cls Γ) = (c : ENNReal) • (ν.restrict F').map (cls Γ)`. Rewrite using `[map_restrict_eq Γ μ h hF', ← Measure.map_smul, ← Measure.restrict_smul, ← e']`.

Establish `hu : μ F = c * ν F'`. Rewrite using `[h.measure_eq hF']`. Use `conv_lhs => rw [e']`. Both sides reduce to the same expression. Rewrite using `[hu, hq2, smul_smul]`.

Use `congr 1`. Establish `c0 : (c : ENNReal) ≠ 0` using `by exact_mod_cast hc0.ne'`. Rewrite using `[ENNReal.mul_inv (Or.inl c0) (Or.inl ENNReal.coe_ne_top), mul_comm (c : ENNReal)⁻¹, mul_assoc, ENNReal.inv_mul_cancel c0 ENNReal.coe_ne_top, mul_one]`.
-/
theorem normalised_eq (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure] {F F' : Set G}
    (h : IsFundamentalDomain Γ F μ) (h' : IsFundamentalDomain Γ F' ν) :
    (μ F)⁻¹ • (μ.restrict F).map (cls Γ) = (ν F')⁻¹ • (ν.restrict F').map (cls Γ) := by
  have e := Measure.isMulLeftInvariant_eq_smul μ ν
  have hc0 := Measure.haarScalarFactor_pos_of_isHaarMeasure μ ν
  set c := Measure.haarScalarFactor μ ν with hc
  have hF' : IsFundamentalDomain Γ F' μ := by
    refine h'.mono ?_
    rw [e]; exact Measure.smul_absolutelyContinuous
  have e' : μ = (c : ENNReal) • ν := e
  have hq2 : (μ.restrict F).map (cls Γ) = (c : ENNReal) • (ν.restrict F').map (cls Γ) := by
    rw [map_restrict_eq Γ μ h hF', ← Measure.map_smul, ← Measure.restrict_smul, ← e']
  have hu : μ F = c * ν F' := by
    rw [h.measure_eq hF']
    conv_lhs => rw [e']
    rfl
  rw [hu, hq2, smul_smul]
  congr 1
  have c0 : (c : ENNReal) ≠ 0 := by exact_mod_cast hc0.ne'
  rw [ENNReal.mul_inv (Or.inl c0) (Or.inl ENNReal.coe_ne_top), mul_comm (c : ENNReal)⁻¹, mul_assoc,
    ENNReal.inv_mul_cancel c0 ENNReal.coe_ne_top, mul_one]

end Top
end GlobalTheory.AutQuotCheck
