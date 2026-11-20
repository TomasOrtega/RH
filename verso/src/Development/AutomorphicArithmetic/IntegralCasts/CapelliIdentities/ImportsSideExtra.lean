import Mathlib

namespace MeasureEqCardCosetsMul
end MeasureEqCardCosetsMul

/- English proof (translation)
Introduce `G _ _ _ _ _ μ _ I hI D hD S hS`. Use `set f : G ⧸ I → Set G := fun q => (fun h => (Quotient.out q)⁻¹ * h) ⁻¹' (I : Set G) with hf`. Establish `hmem : ∀ q x, x ∈ f q ↔ (Quotient.out q)⁻¹ * x ∈ I` using `fun q x => Iff.rfl`. Establish `hmk : ∀ q x, x ∈ f q → (QuotientGroup.mk x : G ⧸ I) = q`. Introduce `q x hx`.

Rewrite `hx` using `[hmem]`. Establish `: (QuotientGroup.mk (Quotient.out q) : G ⧸ I) = QuotientGroup.mk x` using `QuotientGroup.eq.mpr hx`. Rewrite using `[← this]`. Conclude with `Quotient.out_eq' q`. Establish `hDeq : D = ⋃ q ∈ S, f q`.

Use extensionality with `x`. Simplify using `only [Set.mem_iUnion, exists_prop]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `⟨(QuotientGroup.mk x : G ⧸ I), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hS]`. Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul I x`. Rewrite using `[hh]`. Conclude with `hD x hx h h.2`. Rewrite using `[hmem]`.

Establish `: (QuotientGroup.mk (Quotient.out (QuotientGroup.mk x : G ⧸ I)) : G ⧸ I) = QuotientGroup.mk x` using `Quotient.out_eq' _`. Conclude with `QuotientGroup.eq.mp this`. Introduce and unpack `⟨q, hq, hx⟩`. Rewrite `hx` using `[hmem]`. Establish `h1` using `hD _ ((hS q).mp hq) _ hx`.

Simplify using `using h1`. Establish `hdisj : (S : Set (G ⧸ I)).PairwiseDisjoint f`. Introduce `a _ b _ hab`. Rewrite using `[Function.onFun, Set.disjoint_left]`. Introduce `x hxa hxb`.

Conclude with `hab ((hmk a x hxa).symm.trans (hmk b x hxb))`. Establish `hmeas : ∀ q ∈ S, MeasurableSet (f q)`. Introduce `q _`. Conclude with `(hI.preimage (continuous_const.mul continuous_id)).measurableSet`. Rewrite using `[hDeq, MeasureTheory.measure_biUnion_finset hdisj hmeas]`.

Establish `: ∀ q ∈ S, μ (f q) = μ (I : Set G)`. Introduce `q _`. Conclude with `MeasureTheory.measure_preimage_mul μ _ _`. Rewrite using `[Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]`.
-/
theorem UpperTheory.Reformulated.B.Yla7.main :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : MeasurableSpace G]
      [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsMulLeftInvariant] {I : Subgroup G},
      IsOpen (↑I : Set G) →
        ∀ {D : Set G},
          (∀ g ∈ D, ∀ i ∈ I, g * i ∈ D) →
            ∀ (S : Finset (G ⧸ I)),
              (∀ (q : G ⧸ I), q ∈ S ↔ Quotient.out q ∈ D) →
                (μ : Set G → ENNReal) D = (↑S.card : ENNReal) * (μ : Set G → ENNReal) (↑I : Set G) := by
  intro G _ _ _ _ _ μ _ I hI D hD S hS
  classical
  set f : G ⧸ I → Set G := fun q => (fun h => (Quotient.out q)⁻¹ * h) ⁻¹' (I : Set G) with hf
  have hmem : ∀ q x, x ∈ f q ↔ (Quotient.out q)⁻¹ * x ∈ I := fun q x => Iff.rfl
  have hmk : ∀ q x, x ∈ f q → (QuotientGroup.mk x : G ⧸ I) = q := by
    intro q x hx
    rw [hmem] at hx
    have : (QuotientGroup.mk (Quotient.out q) : G ⧸ I) = QuotientGroup.mk x :=
      QuotientGroup.eq.mpr hx
    rw [← this]
    exact Quotient.out_eq' q
  have hDeq : D = ⋃ q ∈ S, f q := by
    ext x
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · intro hx
      refine ⟨(QuotientGroup.mk x : G ⧸ I), ?_, ?_⟩
      · rw [hS]
        obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul I x
        rw [hh]
        exact hD x hx h h.2
      · rw [hmem]
        have : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk x : G ⧸ I)) : G ⧸ I) = QuotientGroup.mk x :=
          Quotient.out_eq' _
        exact QuotientGroup.eq.mp this
    · rintro ⟨q, hq, hx⟩
      rw [hmem] at hx
      have h1 := hD _ ((hS q).mp hq) _ hx
      simpa using h1
  have hdisj : (S : Set (G ⧸ I)).PairwiseDisjoint f := by
    intro a _ b _ hab
    rw [Function.onFun, Set.disjoint_left]
    intro x hxa hxb
    exact hab ((hmk a x hxa).symm.trans (hmk b x hxb))
  have hmeas : ∀ q ∈ S, MeasurableSet (f q) := by
    intro q _
    exact (hI.preimage (continuous_const.mul continuous_id)).measurableSet
  rw [hDeq, MeasureTheory.measure_biUnion_finset hdisj hmeas]
  have : ∀ q ∈ S, μ (f q) = μ (I : Set G) := by
    intro q _
    exact MeasureTheory.measure_preimage_mul μ _ _
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
