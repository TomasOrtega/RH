import Development.EtaleCohomology.CohomologicalPurity.LeafExcSheafCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity

/- English proof (translation)
Introduce `X' X Z f _ ι' ι _ hp U hU T t`. Set `F : Bool → Scheme.{0}` to `fun b => Bool.rec (pullback t f) (t ⁻¹ᵁ U).toScheme b`. Set `m : ∀ b, F b ⟶ T` to `fun b => Bool.rec (pullback.fst t f) (t ⁻¹ᵁ U).ι b`. Establish `hR : Presieve.ofArrows F m ∈ Scheme.precoverage @Etale T`. Use `(Scheme.ofArrows_mem_precoverage_iff @Etale).mpr ⟨fun x => ?_, fun b => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hx : t.base x ∈ (U : Set X)`. Use `⟨true, ?_⟩ show x ∈ Set.range (t ⁻¹ᵁ U).ι.base` and prove the remaining obligations. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `hx`. Rewrite `hx` using `[hU, Set.notMem_compl_iff]`.

Take `⟨z, hz⟩` from `hx`. Establish `hw : f.base (ι'.base z) = ι.base z`. Rewrite using `[← Scheme.Hom.comp_apply, hp.w]`. Simplify using the standard rewrite rules. Take `⟨p, hp1, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := t) (g := f) x (ι'.base z) (by rw [hw, hz])`.

Conclude with `⟨false, p, hp1⟩`. Apply the tactic sequence `cases b <;> dsimp [m] <;> infer_instance`. Use `⟨Sieve.generate (Presieve.ofArrows F m), Precoverage.generate_mem_toGrothendieck hR, ?_⟩` and prove the remaining obligations. Introduce `V g hg`. Take `⟨W, h, k, hk, rfl⟩` from `hg`.

Take `⟨b⟩` from `hk`. Consider the cases of `b`. Use `right`. Use `⟨h ≫ pullback.snd t f, ?_⟩` and prove the remaining obligations. Simplify using `only [m, Category.assoc, ← pullback.condition]`.

Use `left`. Use `⟨h ≫ (t ∣_ U), ?_⟩` and prove the remaining obligations. Simplify using `only [m, Category.assoc, morphismRestrict_ι]`.
-/
theorem LeafSurjGeo_of : LeafSurjGeo := by
  intro X' X Z f _ ι' ι _ hp U hU T t
  let F : Bool → Scheme.{0} := fun b => Bool.rec (pullback t f) (t ⁻¹ᵁ U).toScheme b
  let m : ∀ b, F b ⟶ T := fun b => Bool.rec (pullback.fst t f) (t ⁻¹ᵁ U).ι b
  have hR : Presieve.ofArrows F m ∈ Scheme.precoverage @Etale T := by
    refine (Scheme.ofArrows_mem_precoverage_iff @Etale).mpr ⟨fun x => ?_, fun b => ?_⟩
    · by_cases hx : t.base x ∈ (U : Set X)
      · refine ⟨true, ?_⟩
        show x ∈ Set.range (t ⁻¹ᵁ U).ι.base
        rw [Scheme.Opens.range_ι]; exact hx
      · rw [hU, Set.notMem_compl_iff] at hx
        obtain ⟨z, hz⟩ := hx
        have hw : f.base (ι'.base z) = ι.base z := by
          rw [← Scheme.Hom.comp_apply, hp.w]; simp
        obtain ⟨p, hp1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := t) (g := f) x (ι'.base z)
          (by rw [hw, hz])
        exact ⟨false, p, hp1⟩
    · cases b <;> dsimp [m] <;> infer_instance
  refine ⟨Sieve.generate (Presieve.ofArrows F m),
    Precoverage.generate_mem_toGrothendieck hR, ?_⟩
  intro V g hg
  obtain ⟨W, h, k, hk, rfl⟩ := hg
  obtain ⟨b⟩ := hk
  cases b
  · right
    refine ⟨h ≫ pullback.snd t f, ?_⟩
    simp only [m, Category.assoc, ← pullback.condition]
  · left
    refine ⟨h ≫ (t ∣_ U), ?_⟩
    simp only [m, Category.assoc, morphismRestrict_ι]

end LateralTheory.CohomologicalPurity
