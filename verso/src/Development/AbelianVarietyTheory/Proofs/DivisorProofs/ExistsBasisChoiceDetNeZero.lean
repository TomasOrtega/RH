import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory

/- English proof (translation)
Introduce `F E A A' _ _ _ _ _ _ _ ι V r δ bb res h`. Establish `hsub : ι '' (V : Set A) ⊆ Submodule.span E (Set.range fun i => ι (bb i))`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `hx' : x = ∑ i, bb.repr ⟨x, hx⟩ i • ((bb i : V) : A)`. Use `congrArg Subtype.val (bb.sum_repr ⟨x, hx⟩)` as an intermediate fact.

Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at this`. Conclude with `this.symm`. Rewrite using `[hx', map_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smulₛₗ]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Establish `hspan : Submodule.span E (Set.range fun i => res (ι (bb i))) = ⊤`. Establish `h1` using `Submodule.map_mono (f := res) (Submodule.span_le.mpr hsub)`. Rewrite `h1` using `[h, Submodule.map_span, ← Set.range_comp]`. Conclude with `eq_top_iff.mpr h1`.

Take `⟨b, hb, hbspan, hli⟩` from `exists_linearIndependent E (Set.range fun i => res (ι (bb i)))`. Set `bs` to `Module.Basis.mk hli (by rw [Subtype.range_coe, hbspan, hspan])`. Set `e` to `bs.indexEquiv (Pi.basisFun E (Fin δ))`. Establish `hmem : ∀ p, ((e.symm p : b) : Fin δ → E) ∈ Set.range fun i => res (ι (bb i))` using `fun p => hb (e.symm p).2`. Use `choose σ hσ using hmem`.

Use `⟨σ, ?_⟩` and prove the remaining obligations. Establish `hli2 : LinearIndependent E (fun p => res (ι (bb (σ p))))`. Establish `: (fun p => res (ι (bb (σ p)))) = ((↑) : b → Fin δ → E) ∘ e.symm` using `funext fun p => hσ p`. Rewrite using `[this]`. Conclude with `hli.comp _ e.symm.injective`.

Establish `hunit : IsUnit (Matrix.of fun p' p => res (ι (bb (σ p))) p')`. Rewrite using `[← Matrix.linearIndependent_cols_iff_isUnit]`. Conclude with `hli2`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero`.
-/
theorem exists_basis_choice_det_ne_zero : ∀ (F E A A' : Type) [Field F] [Field E] [Algebra F E] [AddCommGroup A] [Module F A] [AddCommGroup A'] [Module E A'] (ι : A →ₛₗ[algebraMap F E] A') (V : Submodule F A) (r δ : ℕ) (bb : Module.Basis (Fin r) F V) (res : A' →ₗ[E] (Fin δ → E)), (Submodule.span E (ι '' (V : Set A))).map res = ⊤ → ∃ σ : Fin δ → Fin r, (Matrix.of fun p' p => res (ι (bb (σ p))) p').det ≠ 0 := by
  intro F E A A' _ _ _ _ _ _ _ ι V r δ bb res h
  have hsub : ι '' (V : Set A) ⊆ Submodule.span E (Set.range fun i => ι (bb i)) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x = ∑ i, bb.repr ⟨x, hx⟩ i • ((bb i : V) : A) := by
      have := congrArg Subtype.val (bb.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    rw [hx', map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspan : Submodule.span E (Set.range fun i => res (ι (bb i))) = ⊤ := by
    have h1 := Submodule.map_mono (f := res) (Submodule.span_le.mpr hsub)
    rw [h, Submodule.map_span, ← Set.range_comp] at h1
    exact eq_top_iff.mpr h1
  obtain ⟨b, hb, hbspan, hli⟩ := exists_linearIndependent E (Set.range fun i => res (ι (bb i)))
  let bs := Module.Basis.mk hli (by rw [Subtype.range_coe, hbspan, hspan])
  let e := bs.indexEquiv (Pi.basisFun E (Fin δ))
  have hmem : ∀ p, ((e.symm p : b) : Fin δ → E) ∈ Set.range fun i => res (ι (bb i)) :=
    fun p => hb (e.symm p).2
  choose σ hσ using hmem
  refine ⟨σ, ?_⟩
  have hli2 : LinearIndependent E (fun p => res (ι (bb (σ p)))) := by
    have : (fun p => res (ι (bb (σ p)))) = ((↑) : b → Fin δ → E) ∘ e.symm := funext fun p => hσ p
    rw [this]
    exact hli.comp _ e.symm.injective
  have hunit : IsUnit (Matrix.of fun p' p => res (ι (bb (σ p))) p') := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli2
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero

end GlobalTheory
