import Development.EtaleCohomology.EtaleSheaves.SpecSubalgebraPullbackLiftIsClosedImmersion

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.GluedCurveChartOverlaps

/- English proof (translation)
Proceed by induction. Treat this case separately. Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities.

Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_adj {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (B : Subalgebra Ω L) (u : L) (hu : u ≠ 0)
    (huB : u⁻¹ ∈ B) (d : L) (hd : d ∈ Algebra.adjoin Ω ((B : Set L) ∪ {u})) : ∃ n : ℕ, d * u⁻¹ ^ n ∈ B := by
  induction hd using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨0, by simpa using hx⟩
    · rw [Set.mem_singleton_iff.mp hx]; exact ⟨1, by rw [pow_one, mul_inv_cancel₀ hu]; exact B.one_mem⟩
  | algebraMap r => exact ⟨0, by simpa using B.algebraMap_mem r⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx; obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : (x + y) * u⁻¹ ^ (n + m) = (x * u⁻¹ ^ n) * u⁻¹ ^ m + (y * u⁻¹ ^ m) * u⁻¹ ^ n := by ring
    rw [this]
    exact B.add_mem (B.mul_mem hn (B.pow_mem huB _)) (B.mul_mem hm (B.pow_mem huB _))
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx; obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : (x * y) * u⁻¹ ^ (n + m) = (x * u⁻¹ ^ n) * (y * u⁻¹ ^ m) := by ring
    rw [this]; exact B.mul_mem hn hm

/- English proof (translation)
Equip the data with the indicated structure. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Both sides reduce to the same expression.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem away {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (B D : Subalgebra Ω L) (hB : B ≤ D) (u : L)
    (hu : u ≠ 0) (huB : u⁻¹ ∈ B) (huD : u ∈ D) (hD : D ≤ Algebra.adjoin Ω ((B : Set L) ∪ {u})) :
    letI : Algebra B D := (Subalgebra.inclusion hB).toRingHom.toAlgebra
    IsLocalization.Away (⟨u⁻¹, huB⟩ : B) D := by
  letI : Algebra B D := (Subalgebra.inclusion hB).toRingHom.toAlgebra
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, n, rfl⟩
    show IsUnit (algebraMap B D ((⟨u⁻¹, huB⟩ : B) ^ n))
    rw [map_pow]
    refine IsUnit.pow n ?_
    exact ⟨⟨algebraMap B D ⟨u⁻¹, huB⟩, ⟨u, huD⟩, Subtype.ext (inv_mul_cancel₀ hu),
      Subtype.ext (mul_inv_cancel₀ hu)⟩, rfl⟩
  · intro d
    obtain ⟨n, hn⟩ := mem_adj B u hu huB d (hD d.2)
    refine ⟨(⟨d * u⁻¹ ^ n, hn⟩, ⟨_, n, rfl⟩), Subtype.ext ?_⟩
    show d * u⁻¹ ^ n = (d : L) * (u⁻¹ ^ n)
    rfl
  · intro x y hxy
    refine ⟨1, ?_⟩
    have : (x : L) = (y : L) := by
      have h2 := congrArg (fun z : D => (z : L)) hxy
      exact h2
    simp [Subtype.ext this]

set_option backward.isDefEq.respectTransparency false in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Equip the data with the indicated structure.

Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem glued_curve_chart_overlap_is_pullback : LeafGluePullback := by
  intro Ω L _ _ _ A B u h G
  haveI := G.hiA; haveI := G.hiB
  have hadj := h.2.2.2.2.2.2.2.2.2.2.2.1
  have huD : u ∈ Dr Ω A u := Algebra.subset_adjoin (Or.inl h.2.1)
  have hD : Dr Ω A u ≤ Algebra.adjoin Ω ((B : Set L) ∪ {u}) := hadj.le
  haveI hjB : IsOpenImmersion (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (le_Dr_B A B u hadj)).toRingHom)) := by
    letI : Algebra B (Dr Ω A u) := (Subalgebra.inclusion (le_Dr_B A B u hadj)).toRingHom.toAlgebra
    haveI := away B (Dr Ω A u) (le_Dr_B A B u hadj) u h.1 h.2.2.1 huD hD
    exact IsOpenImmersion.of_isLocalization (S := Dr Ω A u) (⟨u⁻¹, h.2.2.1⟩ : B)
  refine IsOpenImmersion.isPullback _ _ _ _ G.agree.symm ?_
  ext x
  show G.iB.base x ∈ Set.range G.iA.base ↔ x ∈ Set.range _
  constructor
  · intro hx
    have hx' : G.iB.base x ∈ Set.range G.iA.base ∩ Set.range G.iB.base := ⟨hx, x, rfl⟩
    rw [G.inter, G.agree] at hx'
    obtain ⟨y, hy⟩ := hx'
    refine ⟨y, G.iB.isOpenEmbedding.injective ?_⟩
    rw [← hy]; rfl
  · rintro ⟨y, rfl⟩
    refine ⟨(Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (le_Dr_A A u)).toRingHom)).base y, ?_⟩
    rw [← Scheme.Hom.comp_apply, G.agree]; rfl

end LateralTheory.E.GluedCurveChartOverlaps

namespace LateralTheory.E.GluedCurveSeparated

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LeafGlueSep_of : LateralTheory.E.LeafGlueIsProperPf.LeafGlueSep :=
  LateralTheory.E.GluedCurveChartOverlaps.LeafGlueSep_of LateralTheory.E.GluedCurveChartOverlaps.glued_curve_chart_overlap_is_pullback
    LateralTheory.E.GluedCurveChartOverlaps.spec_subalgebra_pullback_lift_is_closed_immersion

end LateralTheory.E.GluedCurveSeparated
