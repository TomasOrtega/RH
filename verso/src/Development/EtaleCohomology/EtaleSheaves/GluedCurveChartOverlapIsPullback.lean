import Development.EtaleCohomology.EtaleSheaves.SpecSubalgebraPullbackLiftIsClosedImmersion

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.GluedCurveChartOverlaps

/- English proof (translation)
Proceed by induction on `hd using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Break down `hx with hx | hx` into its components or cases. Conclude with `⟨0, by simpa using hx⟩`. Rewrite using `[Set.mem_singleton_iff.mp hx]; exact ⟨1, by rw [pow_one, mul_inv_cancel₀ hu]; exact B.one_mem⟩`.

Consider the case `algebraMap r => exact ⟨0, by simpa using B.algebraMap_mem r⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨n, hn⟩` from `hx`. Take `⟨m, hm⟩` from `hy`. Use `⟨n + m, ?_⟩` and prove the remaining obligations.

Establish `: (x + y) * u⁻¹ ^ (n + m) = (x * u⁻¹ ^ n) * u⁻¹ ^ m + (y * u⁻¹ ^ m) * u⁻¹ ^ n` using `by ring`. Rewrite using `[this]`. Conclude with `B.add_mem (B.mul_mem hn (B.pow_mem huB _)) (B.mul_mem hm (B.pow_mem huB _))`. Consider the case `mul x y _ _ hx hy`. Take `⟨n, hn⟩` from `hx`.

Take `⟨m, hm⟩` from `hy`. Use `⟨n + m, ?_⟩` and prove the remaining obligations. Establish `: (x * y) * u⁻¹ ^ (n + m) = (x * u⁻¹ ^ n) * (y * u⁻¹ ^ m)` using `by ring`. Rewrite using `[this]`. Conclude with `B.mul_mem hn hm`.
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
Use `letI : Algebra B D := (Subalgebra.inclusion hB).toRingHom.toAlgebra`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨y, n, rfl⟩ show IsUnit (algebraMap B D ((⟨u⁻¹, huB⟩ : B) ^ n))`. Rewrite using `[map_pow]`. Use `IsUnit.pow n ?_` and prove the remaining obligations.

Conclude with `⟨⟨algebraMap B D ⟨u⁻¹, huB⟩, ⟨u, huD⟩, Subtype.ext (inv_mul_cancel₀ hu), Subtype.ext (mul_inv_cancel₀ hu)⟩, rfl⟩`. Introduce `d`. Take `⟨n, hn⟩` from `mem_adj B u hu huB d (hD d.2)`. Use `⟨(⟨d * u⁻¹ ^ n, hn⟩, ⟨_, n, rfl⟩), Subtype.ext ?_⟩` and prove the remaining obligations. Use `show d * u⁻¹ ^ n = (d : L) * (u⁻¹ ^ n)`.

Both sides reduce to the same expression. Introduce `x y hxy`. Use `⟨1, ?_⟩` and prove the remaining obligations. Establish `: (x : L) = (y : L)`. Establish `h2` using `congrArg (fun z : D => (z : L)) hxy`.

Conclude with `h2`. Simplify using `[Subtype.ext this]`.
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
Introduce `Ω L _ _ _ A B u h G`. Use `haveI := G.hiA`. Use `haveI := G.hiB`. Establish `hadj` using `h.2.2.2.2.2.2.2.2.2.2.2.1`. Establish `huD : u ∈ Dr Ω A u` using `Algebra.subset_adjoin (Or.inl h.2.1)`.

Establish `hD : Dr Ω A u ≤ Algebra.adjoin Ω ((B : Set L) ∪ {u})` using `hadj.le`. Use `haveI hjB : IsOpenImmersion (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (le_Dr_B A B u hadj)).toRingHom)) := by`. Use `letI : Algebra B (Dr Ω A u) := (Subalgebra.inclusion (le_Dr_B A B u hadj)).toRingHom.toAlgebra`. Use `haveI := away B (Dr Ω A u) (le_Dr_B A B u hadj) u h.1 h.2.2.1 huD hD`. Conclude with `IsOpenImmersion.of_isLocalization (S := Dr Ω A u) (⟨u⁻¹, h.2.2.1⟩ : B)`.

Use `IsOpenImmersion.isPullback _ _ _ _ G.agree.symm ?_` and prove the remaining obligations. Use extensionality with `x`. Use `show G.iB.base x ∈ Set.range G.iA.base ↔ x ∈ Set.range _`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Establish `hx' : G.iB.base x ∈ Set.range G.iA.base ∩ Set.range G.iB.base` using `⟨hx, x, rfl⟩`. Rewrite `hx'` using `[G.inter, G.agree]`. Take `⟨y, hy⟩` from `hx'`. Use `⟨y, G.iB.isOpenEmbedding.injective ?_⟩` and prove the remaining obligations. Rewrite using `[← hy]`.

Both sides reduce to the same expression. Introduce and unpack `⟨y, rfl⟩`. Use `⟨(Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (le_Dr_A A u)).toRingHom)).base y, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, G.agree]`. Both sides reduce to the same expression.
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
The claim follows from `LateralTheory.E.GluedCurveChartOverlaps.LeafGlueSep_of LateralTheory.E.GluedCurveChartOverlaps.glued_curve_chart_overlap_is_pullback LateralTheory.E.GluedCurveChartOverlaps.spec_subalgebra_pullback_lift_is_closed_immersion`.
-/
theorem LeafGlueSep_of : LateralTheory.E.LeafGlueIsProperPf.LeafGlueSep :=
  LateralTheory.E.GluedCurveChartOverlaps.LeafGlueSep_of LateralTheory.E.GluedCurveChartOverlaps.glued_curve_chart_overlap_is_pullback
    LateralTheory.E.GluedCurveChartOverlaps.spec_subalgebra_pullback_lift_is_closed_immersion

end LateralTheory.E.GluedCurveSeparated
