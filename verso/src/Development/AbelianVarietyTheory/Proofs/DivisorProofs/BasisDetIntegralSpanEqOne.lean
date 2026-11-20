import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory

/- English proof (translation)
Introduce `F V _ _ _ _ _ _ d β`. Establish `key : ∀ v ∈ Submodule.span (𝓞 F) (Set.range β), ∀ i, ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = β.repr v i`. Introduce `v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨j, rfl⟩` from `hx`. Introduce `i`. Use `⟨if j = i then 1 else 0, ?_⟩` and prove the remaining obligations. Rewrite using `[Module.Basis.repr_self, Finsupp.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Consider the case `zero => intro i; exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Introduce `i`. Take `⟨a, ha⟩` from `hx i`. Take `⟨b, hb⟩` from `hy i`.

Conclude with `⟨a + b, by simp [ha, hb]⟩`. Consider the case `smul r x _ hx`. Introduce `i`. Take `⟨a, ha⟩` from `hx i`. Use `⟨r * a, ?_⟩` and prove the remaining obligations.

Rewrite using `[← algebraMap_smul F r x, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, ha]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `y ⟨w, hw, rfl⟩`. Use `choose a ha using fun i => key (w i) (hw i)`.

Rewrite using `[SetLike.mem_coe, Submodule.mem_one, Module.Basis.det_apply]`. Establish `hm : β.toMatrix w = (Matrix.of fun j i => a i j).map (algebraMap (𝓞 F) F)`. Use extensionality with `j i`. Simplify using `[Module.Basis.toMatrix_apply, ha]`. Rewrite using `[hm]`.

Conclude with `⟨(Matrix.of fun j i => a i j).det, by rw [RingHom.map_det]; rfl⟩`. Rewrite using `[Submodule.one_le]`. Conclude with `Submodule.subset_span ⟨β, fun i => Submodule.subset_span ⟨i, rfl⟩, (β.det_self).symm⟩`.
-/
theorem basis_det_integral_span_eq_one : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (d : ℕ) (β : Module.Basis (Fin d) F V), Submodule.span (𝓞 F) {y | ∃ w : Fin d → V, (∀ i, w i ∈ Submodule.span (𝓞 F) (Set.range β)) ∧ y = β.det w} = 1 := by
  intro F V _ _ _ _ _ _ d β
  have key : ∀ v ∈ Submodule.span (𝓞 F) (Set.range β), ∀ i, ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = β.repr v i := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro i
      refine ⟨if j = i then 1 else 0, ?_⟩
      rw [Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs <;> simp
    | zero => intro i; exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      intro i
      obtain ⟨a, ha⟩ := hx i
      obtain ⟨b, hb⟩ := hy i
      exact ⟨a + b, by simp [ha, hb]⟩
    | smul r x _ hx =>
      intro i
      obtain ⟨a, ha⟩ := hx i
      refine ⟨r * a, ?_⟩
      rw [← algebraMap_smul F r x, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, ha]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro y ⟨w, hw, rfl⟩
    choose a ha using fun i => key (w i) (hw i)
    rw [SetLike.mem_coe, Submodule.mem_one, Module.Basis.det_apply]
    have hm : β.toMatrix w = (Matrix.of fun j i => a i j).map (algebraMap (𝓞 F) F) := by
      ext j i
      simp [Module.Basis.toMatrix_apply, ha]
    rw [hm]
    exact ⟨(Matrix.of fun j i => a i j).det, by rw [RingHom.map_det]; rfl⟩
  · rw [Submodule.one_le]
    exact Submodule.subset_span ⟨β, fun i => Submodule.subset_span ⟨i, rfl⟩, (β.det_self).symm⟩

end GlobalTheory
