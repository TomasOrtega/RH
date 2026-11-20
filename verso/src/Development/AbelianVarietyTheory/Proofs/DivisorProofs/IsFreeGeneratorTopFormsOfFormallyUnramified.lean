import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

namespace GlobalTheory.TopForm

/- English proof (translation)
Introduce `k A B _ _ _ α β ψ h n hU ω hω hex`. Take `⟨ω', hω'⟩` from `hex`. Use `letI := α.toAlgebra`. Use `letI := β.toAlgebra`. Use `letI := ψ.toAlgebra`.

Use `haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' h.symm`. Use `haveI : Algebra.FormallyUnramified A B := hU`. Establish `hspan : Submodule.span B (Set.range fun a : A => KaehlerDifferential.D k B (ψ a)) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce and unpack `x -`.

Take `⟨y, rfl⟩` from `(KaehlerDifferential.exact_mapBaseChange_map k A B x).mp (Subsingleton.elim _ _)`. Proceed by induction on `y with`. Consider the case `zero => simp`. Consider the case `add _ _ h1 h2 => rw [map_add]`. Conclude with `add_mem h1 h2`.

Consider the case `tmul b m`. Rewrite using `[KaehlerDifferential.mapBaseChange_tmul]`. Use `Submodule.smul_mem _ b ?_` and prove the remaining obligations. Establish `hm : m ∈ Submodule.span A (Set.range (KaehlerDifferential.D k A))`. Rewrite using `[KaehlerDifferential.span_range_derivation]`.

Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hm using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, rfl⟩` from `hx`. Rewrite using `[KaehlerDifferential.map_D]`.

Conclude with `Submodule.subset_span ⟨a, rfl⟩`. Consider the case `zero => simp`. Consider the case `add _ _ _ _ h1 h2 => rw [map_add]`. Conclude with `add_mem h1 h2`. Consider the case `smul a x _ hx`.

Rewrite using `[map_smul, ← algebraMap_smul B a]`. Conclude with `Submodule.smul_mem _ _ hx`. Establish `hgen : Submodule.span B {formMap n ψ h ω} = ⊤`. Rewrite using `[eq_top_iff, ← exteriorPower.ιMulti_span_of_span B n (Omega β) hspan, Submodule.span_le]`. Introduce and unpack `_ ⟨w, hw, rfl⟩`.

Use `choose v hv using fun i => hw (Set.mem_range_self i)`. Establish `e : exteriorPower.ιMulti B n w = formMap n ψ h (dForm α v)`. Rewrite using `[formMap_dForm, dForm_eq]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Conclude with `(hv i).symm`. Rewrite using `[SetLike.mem_coe, e, ← hω.repr_smul (dForm α v), map_smulₛₗ]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)`. Establish `hmem : ω' ∈ Submodule.span B {formMap n ψ h ω}` using `hgen ▸ Submodule.mem_top`. Take `⟨c, hc⟩` from `Submodule.mem_span_singleton.mp hmem`.

Establish `hb` using `hω'.repr_smul (formMap n ψ h ω)`. Rewrite `hc`, the goal using `[← hb]`. Use `hω'.smul_iff.mpr (IsUnit.of_mul_eq_one c ?_)` and prove the remaining obligations. Use `hω'.1 ?_` and prove the remaining obligations. Simplify using `only [mul_comm _ c, mul_smul, one_smul]`.

Conclude with `hc`.
-/
theorem isFreeGen_formMap_of_formallyUnramified :
    ∀ {k A B : Type} [CommRing k] [CommRing A] [CommRing B] (α : k →+* A) (β : k →+* B) (ψ : A →+* B) (h : ψ.comp α = β) (n : ℕ), (letI := ψ.toAlgebra; Algebra.FormallyUnramified A B) → ∀ ω : Forms α n, IsFreeGen A ω → (∃ ω' : Forms β n, IsFreeGen B ω') → IsFreeGen B (TopForm.formMap n ψ h ω) := by
  intro k A B _ _ _ α β ψ h n hU ω hω hex
  obtain ⟨ω', hω'⟩ := hex
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ψ.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' h.symm
  haveI : Algebra.FormallyUnramified A B := hU
  have hspan : Submodule.span B (Set.range fun a : A => KaehlerDifferential.D k B (ψ a)) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨y, rfl⟩ :=
      (KaehlerDifferential.exact_mapBaseChange_map k A B x).mp (Subsingleton.elim _ _)
    induction y with
    | zero => simp
    | add _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
    | tmul b m =>
      rw [KaehlerDifferential.mapBaseChange_tmul]
      refine Submodule.smul_mem _ b ?_
      have hm : m ∈ Submodule.span A (Set.range (KaehlerDifferential.D k A)) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hm using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        rw [KaehlerDifferential.map_D]
        exact Submodule.subset_span ⟨a, rfl⟩
      | zero => simp
      | add _ _ _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
      | smul a x _ hx =>
        rw [map_smul, ← algebraMap_smul B a]
        exact Submodule.smul_mem _ _ hx
  have hgen : Submodule.span B {formMap n ψ h ω} = ⊤ := by
    rw [eq_top_iff, ← exteriorPower.ιMulti_span_of_span B n (Omega β) hspan, Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    choose v hv using fun i => hw (Set.mem_range_self i)
    have e : exteriorPower.ιMulti B n w = formMap n ψ h (dForm α v) := by
      rw [formMap_dForm, dForm_eq]
      congr 1
      funext i
      exact (hv i).symm
    rw [SetLike.mem_coe, e, ← hω.repr_smul (dForm α v), map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hmem : ω' ∈ Submodule.span B {formMap n ψ h ω} := hgen ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hb := hω'.repr_smul (formMap n ψ h ω)
  rw [← hb] at hc ⊢
  refine hω'.smul_iff.mpr (IsUnit.of_mul_eq_one c ?_)
  refine hω'.1 ?_
  simp only [mul_comm _ c, mul_smul, one_smul]
  exact hc

end GlobalTheory.TopForm
