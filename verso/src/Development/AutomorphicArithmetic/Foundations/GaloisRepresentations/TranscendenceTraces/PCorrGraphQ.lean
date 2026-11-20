import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `hT hW S Y f d`. Use `⟨⟨S, 𝟙 S, f, Wt.const S d, inferInstance, hW.2.2 (𝟙 S) d⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `B bY`. Simplify using the standard rewrite rules. Introduce `Ω _ _ x y`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hs : {z : gp Ω ⟶ S | z ≫ 𝟙 S = x ∧ z ≫ f = y} = {x}`. Use extensionality with `z`. Simplify using `only [Set.mem_setOf_eq, Set.mem_singleton_iff, Category.comp_id]`.

Prove the components needed by the constructor for the conclusion. Conclude with `fun hz => hz.1`. Introduce and unpack `rfl`. Conclude with `⟨rfl, h⟩`. Express the relevant statement in the definitionally equal form `∑ᶠ z ∈ {z : gp Ω ⟶ S | z ≫ 𝟙 S = x ∧ z ≫ f = y}, Wt.const S d Ω z = d`.

Rewrite using `[hs, finsum_mem_singleton]`. Both sides reduce to the same expression. Introduce `h`. Establish `hs : {z : gp Ω ⟶ S | z ≫ 𝟙 S = x ∧ z ≫ f = y} = ∅`. Use extensionality with `z`.

Simplify using `only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, Category.comp_id]`. Introduce and unpack `⟨rfl, h'⟩`. Conclude with `h h'`. Express the relevant statement in the definitionally equal form `∑ᶠ z ∈ {z : gp Ω ⟶ S | z ≫ 𝟙 S = x ∧ z ≫ f = y}, Wt.const S d Ω z = 0`. Rewrite using `[hs, finsum_mem_empty]`.

Introduce `l _ n i hl`. Express the relevant statement in the definitionally equal form `(trHQ l (𝟙 S) (Wt.const S d) n i).comp (pullHQ l (sch.map f) n i) = _`. Rewrite using `[hT l n i S d hl, LinearMap.smul_comp, LinearMap.id_comp]`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.corrGraphQ_of :
    TrIdQ → WtLin → CorrGraphQ := by
  intro hT hW S Y f d
  refine ⟨⟨S, 𝟙 S, f, Wt.const S d, inferInstance, hW.2.2 (𝟙 S) d⟩, ?_, ?_, ?_⟩
  · intro B bY
    simp
  · intro Ω _ _ x y
    constructor
    · intro h
      have hs : {z : gp Ω ⟶ S | z ≫ 𝟙 S = x ∧ z ≫ f = y} = {x} := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Category.comp_id]
        constructor
        · exact fun hz => hz.1
        · rintro rfl
          exact ⟨rfl, h⟩
      change ∑ᶠ z ∈ {z : gp Ω ⟶ S | z ≫ 𝟙 S = x ∧ z ≫ f = y}, Wt.const S d Ω z = d
      rw [hs, finsum_mem_singleton]
      rfl
    · intro h
      have hs : {z : gp Ω ⟶ S | z ≫ 𝟙 S = x ∧ z ≫ f = y} = ∅ := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, Category.comp_id]
        rintro ⟨rfl, h'⟩
        exact h h'
      change ∑ᶠ z ∈ {z : gp Ω ⟶ S | z ≫ 𝟙 S = x ∧ z ≫ f = y}, Wt.const S d Ω z = 0
      rw [hs, finsum_mem_empty]
  · intro l _ n i hl
    change (trHQ l (𝟙 S) (Wt.const S d) n i).comp (pullHQ l (sch.map f) n i) = _
    rw [hT l n i S d hl, LinearMap.smul_comp, LinearMap.id_comp]
