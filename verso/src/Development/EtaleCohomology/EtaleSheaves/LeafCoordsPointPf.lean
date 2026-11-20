import Development.EtaleCohomology.EtaleSheaves.LeafCoordsPointPfClear
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothOfDefectZero

noncomputable section

namespace LateralTheory.E.LeafCoordsPointPf

open LateralTheory.E.LeafCoordsPf
open scoped Pointwise TensorProduct

/- English proof (translation)
Use `set N := Submodule.span B (Set.range g)`. Set `f` to `LinearMap.baseChange P.ResidueField N.mkQ`. Establish `hf : Function.Surjective f` using `LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective N)`. Establish `hr : LinearMap.range f = ⊥`. Rewrite using `[LinearMap.range_eq_map, ← hg, Submodule.map_span, Submodule.span_eq_bot]`.

Introduce and unpack `_ ⟨_, ⟨i, rfl⟩, rfl⟩`. Establish `: g i ∈ N` using `Submodule.subset_span (Set.mem_range_self i)`. Simplify using `[f, (Submodule.Quotient.mk_eq_zero N).mpr this]`. Establish `: Subsingleton (P.ResidueField ⊗[B] (M ⧸ N))`. Establish `h0 : ∀ z : P.ResidueField ⊗[B] (M ⧸ N), z = 0` using `fun z => by`.

Take `⟨w, rfl⟩` from `hf z`. Establish `: f w ∈ LinearMap.range f` using `⟨w, rfl⟩`. Rewrite `this` using `[hr]`. Conclude with `this`. Conclude with `⟨fun a b => by rw [h0 a, h0 b]⟩`.

Take `⟨u, hu, hum⟩` from `GlobalTheory.SS.DefectZero.exists_smul_eq_zero B P.ResidueField (M ⧸ N) (N.mkQ m)`. Use `⟨u, fun H => hu (Ideal.algebraMap_residueField_eq_zero.mpr H), ?_⟩` and prove the remaining obligations. Establish `: (Submodule.Quotient.mk (u • m) : M ⧸ N) = 0` using `by rw [Submodule.Quotient.mk_smul]; exact hum`. Conclude with `(Submodule.Quotient.mk_eq_zero N).mp this`.
-/
theorem exists_smul_mem_of_span {B M ι : Type} [CommRing B] [AddCommGroup M] [Module B M] [Module.Finite B M]
    (P : Ideal B) [P.IsPrime] (g : ι → M)
    (hg : Submodule.span P.ResidueField (Set.range fun i => (1 : P.ResidueField) ⊗ₜ[B] g i) = ⊤) (m : M) :
    ∃ s ∉ P, s • m ∈ Submodule.span B (Set.range g) := by
  set N := Submodule.span B (Set.range g)
  let f := LinearMap.baseChange P.ResidueField N.mkQ
  have hf : Function.Surjective f := LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective N)
  have hr : LinearMap.range f = ⊥ := by
    rw [LinearMap.range_eq_map, ← hg, Submodule.map_span, Submodule.span_eq_bot]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have : g i ∈ N := Submodule.subset_span (Set.mem_range_self i)
    simp [f, (Submodule.Quotient.mk_eq_zero N).mpr this]
  have : Subsingleton (P.ResidueField ⊗[B] (M ⧸ N)) := by
    have h0 : ∀ z : P.ResidueField ⊗[B] (M ⧸ N), z = 0 := fun z => by
      obtain ⟨w, rfl⟩ := hf z
      have : f w ∈ LinearMap.range f := ⟨w, rfl⟩
      rw [hr] at this
      exact this
    exact ⟨fun a b => by rw [h0 a, h0 b]⟩
  obtain ⟨u, hu, hum⟩ := GlobalTheory.SS.DefectZero.exists_smul_eq_zero B P.ResidueField (M ⧸ N) (N.mkQ m)
  refine ⟨u, fun H => hu (Ideal.algebraMap_residueField_eq_zero.mpr H), ?_⟩
  have : (Submodule.Quotient.mk (u • m) : M ⧸ N) = 0 := by rw [Submodule.Quotient.mk_smul]; exact hum
  exact (Submodule.Quotient.mk_eq_zero N).mp this

def LeafCoordsPointRes : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ (P : Ideal B) [P.IsPrime], I ≤ P → ∃ (t : Fin d → I) (y : Fin e → B),
    Submodule.span P.ResidueField (Set.range fun j => (1 : P.ResidueField) ⊗ₜ[B] t j) = ⊤ ∧
    Submodule.span P.ResidueField
      (Set.range fun i => (1 : P.ResidueField) ⊗ₜ[B] dyt (A := A) y (fun j => (t j : B)) i) = ⊤

/- English proof (translation)
Introduce `d e A B _ _ _ I hB hBI P hP hIP`. Take `⟨t, y, hI, hΩ⟩` from `hR d e A B I hB hBI P hIP`. Establish `hfg` using `ideal_fg I _ _ hB hBI`. Establish `: Module.Finite B I` using `Module.Finite.iff_fg.mpr hfg`. Use `hB.isStandardSmooth` as an intermediate fact.

Use `⟨fun j => t j, y, fun j => (t j).2, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨s, hs, hsm⟩` from `exists_smul_mem_of_span P t hI ⟨x, hx⟩`. Use `⟨s, hs, Submodule.mem_sup_left ?_⟩` and prove the remaining obligations. Use `Submodule.mem_map_of_mem (f := I.subtype) hsm` as an intermediate fact.

Rewrite `this` using `[Submodule.map_span, ← Set.range_comp]`. Simplify `this` using `[Function.comp_def]`. Introduce `ω`. Take `⟨s, hs, hsm⟩` from `exists_smul_mem_of_span P _ hΩ ω`. Conclude with `⟨s, hs, Submodule.mem_sup_left hsm⟩`.
-/
theorem LeafCoordsPointLoc_of (hR : LeafCoordsPointRes) : LeafCoordsPointLoc := by
  intro d e A B _ _ _ I hB hBI P hP hIP
  obtain ⟨t, y, hI, hΩ⟩ := hR d e A B I hB hBI P hIP
  have hfg := ideal_fg I _ _ hB hBI
  have : Module.Finite B I := Module.Finite.iff_fg.mpr hfg
  have := hB.isStandardSmooth
  refine ⟨fun j => t j, y, fun j => (t j).2, ?_, ?_⟩
  · intro x hx
    obtain ⟨s, hs, hsm⟩ := exists_smul_mem_of_span P t hI ⟨x, hx⟩
    refine ⟨s, hs, Submodule.mem_sup_left ?_⟩
    have := Submodule.mem_map_of_mem (f := I.subtype) hsm
    rw [Submodule.map_span, ← Set.range_comp] at this
    simpa [Function.comp_def] using this
  · intro ω
    obtain ⟨s, hs, hsm⟩ := exists_smul_mem_of_span P _ hΩ ω
    exact ⟨s, hs, Submodule.mem_sup_left hsm⟩

/- English proof (translation)
The claim follows from `LeafCoordsPoint_of (LeafCoordsPointLoc_of hR)`.
-/
theorem LeafCoordsPoint_of_res (hR : LeafCoordsPointRes) : LeafCoordsPoint :=
  LeafCoordsPoint_of (LeafCoordsPointLoc_of hR)

end LateralTheory.E.LeafCoordsPointPf
