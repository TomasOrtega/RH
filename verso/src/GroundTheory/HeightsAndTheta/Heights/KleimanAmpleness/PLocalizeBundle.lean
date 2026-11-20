import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LocalizeBundleSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

noncomputable section

universe u u' w

section BaseChange

variable {S : Type u} [CommRing S] {O : Type u'} [CommRing O] [Algebra S O]
  {Ω : Type w} [Field Ω] [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

/- English proof (translation)
Proceed by induction on `hs using Submonoid.closure_induction with`. Consider the case `mem a ha`. Take `⟨i, hi, rfl⟩` from `ha`. Rewrite using `[map_X]`. Conclude with `Submonoid.subset_closure ⟨i, hi, rfl⟩`.

Consider the case `one => rw [map_one]`. Conclude with `one_mem _`. Consider the case `mul a b _ _ ha hb => rw [map_mul]`. Conclude with `mul_mem ha hb`.
-/
theorem map_mem_monos_base {I : Finset (Fin (N + 1))} {s : Poly S N} (hs : s ∈ monos I) :
    map (algebraMap S O) s ∈ monos (S := O) I := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    rw [map_X]
    exact Submonoid.subset_closure ⟨i, hi, rfl⟩
  | one => rw [map_one]; exact one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

/- English proof (translation)
Take `⟨f, s, e, hs, hf, hse, rfl⟩` from `ha`. Conclude with `⟨map (algebraMap S O) f, map (algebraMap S O) s, e, map_mem_monos_base hs, hf.map _, hse.map _, by rw [aeval_map_algebraMap, aeval_map_algebraMap]⟩`.
-/
theorem mem_chartRing_base {I : Chart x} {a : Ω} (ha : a ∈ chartRing S x I) :
    a ∈ chartRing O x I := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
  exact ⟨map (algebraMap S O) f, map (algebraMap S O) s, e, map_mem_monos_base hs, hf.map _,
    hse.map _, by rw [aeval_map_algebraMap, aeval_map_algebraMap]⟩

/- English proof (translation)
Establish `: a • y = (⟨(a : Ω), mem_chartRing_base a.2⟩ : chartRing O x I) • y`. Rewrite using `[chartRing_smul_def, chartRing_smul_def]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem smul_mem_span_base {I : Chart x} (P : Set Ω) (a : chartRing S x I) {y : Ω}
    (hy : y ∈ Submodule.span (chartRing O x I) P) : a • y ∈ Submodule.span (chartRing O x I) P := by
  have : a • y = (⟨(a : Ω), mem_chartRing_base a.2⟩ : chartRing O x I) • y := by
    rw [chartRing_smul_def, chartRing_smul_def]
  rw [this]
  exact Submodule.smul_mem _ _ hy

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.mpr fun y hy => ?_` and prove the remaining obligations. Use `Submodule.span_induction (p := fun y _ => y ∈ Submodule.span (chartRing O x I) P) ?_ ?_ ?_ ?_ hy` and prove the remaining obligations. Introduce `z hz`. Conclude with `Submodule.subset_span hz`.

Conclude with `Submodule.zero_mem _`. Introduce `a b _ _ ha hb`. Conclude with `Submodule.add_mem _ ha hb`. Introduce `a z _ hz`. Conclude with `smul_mem_span_base P a hz`.

Conclude with `Submodule.span_mono Submodule.subset_span`.
-/
theorem span_base_span (I : Chart x) (P : Set Ω) :
    Submodule.span (chartRing O x I) (Submodule.span (chartRing S x I) P : Set Ω) =
      Submodule.span (chartRing O x I) P := by
  apply le_antisymm
  · refine Submodule.span_le.mpr fun y hy => ?_
    refine Submodule.span_induction
      (p := fun y _ => y ∈ Submodule.span (chartRing O x I) P) ?_ ?_ ?_ ?_ hy
    · intro z hz; exact Submodule.subset_span hz
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
    · intro a z _ hz; exact smul_mem_span_base P a hz
  · exact Submodule.span_mono Submodule.subset_span

/- English proof (translation)
Take `⟨v, hv⟩` from `isUnit_iff_exists_inv.mp ha`. Use `isUnit_iff_exists_inv.mpr ⟨⟨(v : Ω), mem_chartRing_base v.2⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val hv` as an intermediate fact. Express the relevant statement in the definitionally equal form `(a : Ω) * (v : Ω) = 1 at this`. Express the relevant statement in the definitionally equal form `(a : Ω) * (v : Ω) = 1`.

Conclude with `this`.
-/
theorem isUnit_base {I J : Chart x} (h : I.1 ⊆ J.1) {a : chartRing S x I}
    (ha : IsUnit (chartIncl h a)) :
    IsUnit (chartIncl h (⟨(a : Ω), mem_chartRing_base a.2⟩ : chartRing O x I)) := by
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp ha
  refine isUnit_iff_exists_inv.mpr ⟨⟨(v : Ω), mem_chartRing_base v.2⟩, Subtype.ext ?_⟩
  have := congrArg Subtype.val hv
  change (a : Ω) * (v : Ω) = 1 at this
  change (a : Ω) * (v : Ω) = 1
  exact this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hy`. Express the relevant statement in the definitionally equal form `y ∈ Submodule.span (chartRing O x J) (M.sub J : Set Ω) at hy`. Set `T : Submodule (chartRing O x J) Ω` to `{ carrier := {y | ∃ a : chartRing O x I, IsUnit (chartIncl h a) ∧ (a : Ω) • y ∈ Submodule.span (chartRing O x I) (M.sub I : Set Ω)} add_mem' := by`. Introduce and unpack `y₁ y₂ ⟨a₁, ha₁, h₁⟩ ⟨a₂, ha₂, h₂⟩`.

Use `⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩` and prove the remaining obligations. Establish `: ((a₁ * a₂ : chartRing O x I) : Ω) • (y₁ + y₂) = a₂ • ((a₁ : Ω) • y₁) + a₁ • ((a₂ : Ω) • y₂)`. Express the relevant statement in the definitionally equal form `(a₁ : Ω) * a₂ * (y₁ + y₂) = (a₂ : Ω) * ((a₁ : Ω) * y₁) + (a₁ : Ω) * ((a₂ : Ω) * y₂)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)`. Use the proof step `zero_mem' := ⟨1, by rw [map_one]; exact isUnit_one, by`. Rewrite using `[smul_zero]`. Conclude with `Submodule.zero_mem _⟩`. Use the proof step `smul_mem' := by`.

Introduce and unpack `b y ⟨a, ha, hay⟩`. Take `⟨c, hc, hcb⟩` from `exists_isUnit_mul_mem (S := O) h b`. Use `⟨c * a, by rw [map_mul]; exact hc.mul ha, ?_⟩` and prove the remaining obligations. Establish `: ((c * a : chartRing O x I) : Ω) • (b • y) = (⟨(c : Ω) * b, hcb⟩ : chartRing O x I) • ((a : Ω) • y)`. Express the relevant statement in the definitionally equal form `(c : Ω) * a * ((b : Ω) * y) = (c : Ω) * b * ((a : Ω) * y)`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hay }`. Establish `hle : Submodule.span (chartRing O x J) (M.sub J : Set Ω) ≤ T`. Use `Submodule.span_le.mpr fun m hm => ?_` and prove the remaining obligations.

Take `⟨a, ha, ham⟩` from `(M.mem_iff I J h m).mp hm`. Conclude with `⟨⟨(a : Ω), mem_chartRing_base a.2⟩, isUnit_base h ha, Submodule.subset_span ham⟩`. Conclude with `hle hy`. Introduce and unpack `⟨a, ⟨u, hu⟩, hay⟩`. Establish `hJ` using `(M.toSubSystem.baseChange O).mono I J h _ hay`.

Establish `hinv : ((↑u⁻¹ : chartRing O x J) : Ω) * (a : Ω) = 1`. Use `congrArg Subtype.val (Units.inv_mul u)` as an intermediate fact. Rewrite `this` using `[hu]`. Conclude with `this`. Establish `hy : y = (↑u⁻¹ : chartRing O x J) • ((a : Ω) • y)`.

Rewrite using `[chartRing_smul_def, smul_eq_mul, ← mul_assoc, hinv, one_mul]`. Rewrite using `[hy]`. Conclude with `Submodule.smul_mem _ _ hJ`.
-/
theorem LocalizeBundle.mem_iff_baseChange (M : LineBundle S x) (I J : Chart x) (h : I.1 ⊆ J.1)
    (y : Ω) :
    y ∈ (M.toSubSystem.baseChange O).sub J ↔
      ∃ a : chartRing O x I, IsUnit (chartIncl h a) ∧
        (a : Ω) • y ∈ (M.toSubSystem.baseChange O).sub I := by
  constructor
  · intro hy
    change y ∈ Submodule.span (chartRing O x J) (M.sub J : Set Ω) at hy
    let T : Submodule (chartRing O x J) Ω :=
      { carrier := {y | ∃ a : chartRing O x I, IsUnit (chartIncl h a) ∧
          (a : Ω) • y ∈ Submodule.span (chartRing O x I) (M.sub I : Set Ω)}
        add_mem' := by
          rintro y₁ y₂ ⟨a₁, ha₁, h₁⟩ ⟨a₂, ha₂, h₂⟩
          refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩
          have : ((a₁ * a₂ : chartRing O x I) : Ω) • (y₁ + y₂) =
              a₂ • ((a₁ : Ω) • y₁) + a₁ • ((a₂ : Ω) • y₂) := by
            change (a₁ : Ω) * a₂ * (y₁ + y₂) = (a₂ : Ω) * ((a₁ : Ω) * y₁) + (a₁ : Ω) * ((a₂ : Ω) * y₂)
            ring
          rw [this]
          exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
        zero_mem' := ⟨1, by rw [map_one]; exact isUnit_one, by
          rw [smul_zero]; exact Submodule.zero_mem _⟩
        smul_mem' := by
          rintro b y ⟨a, ha, hay⟩
          obtain ⟨c, hc, hcb⟩ := exists_isUnit_mul_mem (S := O) h b
          refine ⟨c * a, by rw [map_mul]; exact hc.mul ha, ?_⟩
          have : ((c * a : chartRing O x I) : Ω) • (b • y) =
              (⟨(c : Ω) * b, hcb⟩ : chartRing O x I) • ((a : Ω) • y) := by
            change (c : Ω) * a * ((b : Ω) * y) = (c : Ω) * b * ((a : Ω) * y)
            ring
          rw [this]
          exact Submodule.smul_mem _ _ hay }
    have hle : Submodule.span (chartRing O x J) (M.sub J : Set Ω) ≤ T := by
      refine Submodule.span_le.mpr fun m hm => ?_
      obtain ⟨a, ha, ham⟩ := (M.mem_iff I J h m).mp hm
      exact ⟨⟨(a : Ω), mem_chartRing_base a.2⟩, isUnit_base h ha, Submodule.subset_span ham⟩
    exact hle hy
  · rintro ⟨a, ⟨u, hu⟩, hay⟩
    have hJ := (M.toSubSystem.baseChange O).mono I J h _ hay
    have hinv : ((↑u⁻¹ : chartRing O x J) : Ω) * (a : Ω) = 1 := by
      have := congrArg Subtype.val (Units.inv_mul u)
      rw [hu] at this
      exact this
    have hy : y = (↑u⁻¹ : chartRing O x J) • ((a : Ω) • y) := by
      rw [chartRing_smul_def, smul_eq_mul, ← mul_assoc, hinv, one_mul]
    rw [hy]
    exact Submodule.smul_mem _ _ hJ

/- English proof (translation)
Take `⟨s, hs⟩` from `M.fg I`. Use `⟨s, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Submodule.span (chartRing O x I) (s : Set Ω) = Submodule.span (chartRing O x I) (M.sub I : Set Ω)`. Rewrite using `[← hs, span_base_span]`.
-/
theorem LocalizeBundle.fg_baseChange (M : LineBundle S x) (I : Chart x) :
    ((M.toSubSystem.baseChange O).sub I).FG := by
  obtain ⟨s, hs⟩ := M.fg I
  refine ⟨s, ?_⟩
  change Submodule.span (chartRing O x I) (s : Set Ω) =
    Submodule.span (chartRing O x I) (M.sub I : Set Ω)
  rw [← hs, span_base_span]

/- English proof (translation)
Take `⟨Q', hQ⟩` from `M.invertible I`. Use `⟨Submodule.span (chartRing O x I) (Q' : Set Ω), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Submodule.span (chartRing O x I) (M.sub I : Set Ω) * Submodule.span (chartRing O x I) (Q' : Set Ω) = 1`. Rewrite using `[Submodule.span_mul_span, ← span_base_span (S := S) (O := O) I, ← Submodule.mul_eq_span_mul_set, hQ, Submodule.one_eq_span (R := chartRing S x I), span_base_span]`. Conclude with `(Submodule.one_eq_span).symm`.
-/
theorem LocalizeBundle.invertible_baseChange (M : LineBundle S x) (I : Chart x) :
    ∃ Q' : Submodule (chartRing O x I) Ω, (M.toSubSystem.baseChange O).sub I * Q' = 1 := by
  obtain ⟨Q', hQ⟩ := M.invertible I
  refine ⟨Submodule.span (chartRing O x I) (Q' : Set Ω), ?_⟩
  change Submodule.span (chartRing O x I) (M.sub I : Set Ω) *
    Submodule.span (chartRing O x I) (Q' : Set Ω) = 1
  rw [Submodule.span_mul_span, ← span_base_span (S := S) (O := O) I,
    ← Submodule.mul_eq_span_mul_set, hQ, Submodule.one_eq_span (R := chartRing S x I),
    span_base_span]
  exact (Submodule.one_eq_span).symm

def LocalizeBundle.lineBundleBaseChange (M : LineBundle S x) : LineBundle O x :=
  { M.toSubSystem.baseChange O with
    mem_iff := LocalizeBundle.mem_iff_baseChange M
    fg := LocalizeBundle.fg_baseChange M
    invertible := LocalizeBundle.invertible_baseChange M }

end BaseChange

/- English proof (translation)
Introduce `S _ 𝔪 _ O _ _ _ Ω _ _ _ _ N x M`. Conclude with `⟨LocalizeBundle.lineBundleBaseChange M, rfl⟩`.
-/
theorem LocalizeBundle.proof : LocalizeBundle.Statement := by
  intro S _ 𝔪 _ O _ _ _ Ω _ _ _ _ N x M
  exact ⟨LocalizeBundle.lineBundleBaseChange M, rfl⟩

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
