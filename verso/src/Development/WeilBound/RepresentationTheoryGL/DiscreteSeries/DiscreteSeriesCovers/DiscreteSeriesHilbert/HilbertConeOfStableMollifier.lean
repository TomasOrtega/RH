import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt

noncomputable section

open Finset

namespace PositivityTheory.RgDs.Hilb

open ReciprocityTheory.ChartRestriction.DS

/- English proof (translation)
Introduce `hSt hMo hWt n ε lam T Ψ _hHC hPsi hKey η S hSH hSK`. Establish `: FiniteDimensional ℂ S` using `hSK.1`. Establish `hcl : IsClosed ((Hlam ε Ψ T.w : Submodule ℂ (L2 ε)) : Set (L2 ε))`. Unfold `Hlam closGen`. Conclude with `Submodule.isClosed_topologicalClosure _`.

Take `⟨A, hAK, hAinj, hAsm, hAW⟩` from `hMo n ε (Hlam ε Ψ T.w) S hcl (hSt n ε lam T Ψ hPsi) inferInstance hSH hSK.2.1`. Use `set S₂ : Submodule ℂ (L2 ε) := S.map A with hS₂`. Establish `hfin : FiniteDimensional ℂ S₂` using `Module.Finite.map S A`. Establish `hK₂ : Formalism.MainNotions.S.IsKStableOn ε (rreg ε) S₂`. Introduce and unpack `g hg _ ⟨w, hw, rfl⟩`.

Conclude with `⟨rreg ε g w, hSK.2.1 g hg w hw, hAK g hg w⟩`. Establish `hne : S₂ ≠ ⊥`. Take `⟨v, hv, hv0, -⟩` from `hSK.2.2.2.1`. Introduce `h`. Establish `hmem : A v ∈ S₂` using `⟨v, hv, rfl⟩`.

Rewrite `hmem` using `[h]`. Conclude with `hv0 (hAinj v hv ((Submodule.mem_bot ℂ).1 hmem))`. Take `⟨N, _i1, _i2, e, φ, h1, h2, -⟩` from `hKey S₂ hfin (hAW.trans le_rfl) hK₂`. Take `⟨x₀, -, hx₀⟩` from `h1 S₂ le_rfl hK₂ hne`. Establish `he : e ≠ 0`.

Introduce `h`. Apply `hx₀` to reduce the goal to its premises. Rewrite using `[h, LinearMap.zero_apply]`. Take `⟨ν, x, hxw, hex⟩` from `hWt n ε S₂ hfin hAsm hK₂ N e he`. Establish `hνc : InCone (lowK ε lam) ν` using `h2 ν x hxw hex`.

Establish `hx0 : (x : L2 ε) ≠ 0`. Introduce `h`. Apply `hex` to reduce the goal to its premises. Establish `: x = 0` using `Subtype.ext h`. Rewrite using `[this, map_zero]`.

Take `⟨y, hy, hyx⟩` from `x.2`. Establish `hy0 : y ≠ 0`. Introduce `h`. Apply `hx0` to reduce the goal to its premises. Rewrite using `[← hyx, h, map_zero]`.

Establish `hyw : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) (rreg ε) ν y`. Introduce `θ hθ`. Establish `h1' : A (rreg ε (Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) y - Complex.exp (((∑ a, ν a * θ a : ℝ) : ℂ) * Complex.I) • y) = 0`. Rewrite using `[map_sub, map_smul, hAK _ hθ, hyx, hxw θ hθ, sub_self]`. Establish `h2'` using `hAinj _ (Submodule.sub_mem _ (hSK.2.1 _ hθ y hy) (Submodule.smul_mem _ _ hy)) h1'`.

Conclude with `sub_eq_zero.1 h2'`. Take `⟨c', hc', hd⟩` from `hSK.2.2.2.2 ν y hy hy0 hyw`. Take `⟨c, hc, hν⟩` from `hνc`. Use `⟨fun a b => c a b + c' a b, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b hab`.

Establish `hab' : c a b + c' a b ≠ 0` using `hab`. Distinguish the cases in `h : c a b = 0`. Rewrite `hab'` using `[h, zero_add]`. Conclude with `(hc' a b hab').1`. Conclude with `hc a b h`.

Establish `hη : η = ν + (η - ν)` using `by abel`. Rewrite using `[hη, hd, hν]`. Simplify using `only [Nat.cast_add, add_smul, Finset.sum_add_distrib]`. Normalize the expressions using the abelian group laws.
-/
theorem hilbert_cone_of_stable_mollifier : StepStable → StepMoll → StepWtSpan → StepCone := by
  intro hSt hMo hWt n ε lam T Ψ _hHC hPsi hKey η S hSH hSK
  have : FiniteDimensional ℂ S := hSK.1
  have hcl : IsClosed ((Hlam ε Ψ T.w : Submodule ℂ (L2 ε)) : Set (L2 ε)) := by
    unfold Hlam closGen
    exact Submodule.isClosed_topologicalClosure _
  obtain ⟨A, hAK, hAinj, hAsm, hAW⟩ :=
    hMo n ε (Hlam ε Ψ T.w) S hcl (hSt n ε lam T Ψ hPsi) inferInstance hSH hSK.2.1
  set S₂ : Submodule ℂ (L2 ε) := S.map A with hS₂
  have hfin : FiniteDimensional ℂ S₂ := Module.Finite.map S A
  have hK₂ : Formalism.MainNotions.S.IsKStableOn ε (rreg ε) S₂ := by
    rintro g hg _ ⟨w, hw, rfl⟩
    exact ⟨rreg ε g w, hSK.2.1 g hg w hw, hAK g hg w⟩
  have hne : S₂ ≠ ⊥ := by
    obtain ⟨v, hv, hv0, -⟩ := hSK.2.2.2.1
    intro h
    have hmem : A v ∈ S₂ := ⟨v, hv, rfl⟩
    rw [h] at hmem
    exact hv0 (hAinj v hv ((Submodule.mem_bot ℂ).1 hmem))
  obtain ⟨N, _i1, _i2, e, φ, h1, h2, -⟩ := hKey S₂ hfin (hAW.trans le_rfl) hK₂
  obtain ⟨x₀, -, hx₀⟩ := h1 S₂ le_rfl hK₂ hne
  have he : e ≠ 0 := by
    intro h
    apply hx₀
    rw [h, LinearMap.zero_apply]
  obtain ⟨ν, x, hxw, hex⟩ := hWt n ε S₂ hfin hAsm hK₂ N e he
  have hνc : InCone (lowK ε lam) ν := h2 ν x hxw hex
  have hx0 : (x : L2 ε) ≠ 0 := by
    intro h
    apply hex
    have : x = 0 := Subtype.ext h
    rw [this, map_zero]
  obtain ⟨y, hy, hyx⟩ := x.2
  have hy0 : y ≠ 0 := by
    intro h
    apply hx0
    rw [← hyx, h, map_zero]
  have hyw : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) (rreg ε) ν y := by
    intro θ hθ
    have h1' : A (rreg ε (Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) y -
        Complex.exp (((∑ a, ν a * θ a : ℝ) : ℂ) * Complex.I) • y) = 0 := by
      rw [map_sub, map_smul, hAK _ hθ, hyx, hxw θ hθ, sub_self]
    have h2' := hAinj _ (Submodule.sub_mem _ (hSK.2.1 _ hθ y hy) (Submodule.smul_mem _ _ hy)) h1'
    exact sub_eq_zero.1 h2'
  obtain ⟨c', hc', hd⟩ := hSK.2.2.2.2 ν y hy hy0 hyw
  obtain ⟨c, hc, hν⟩ := hνc
  refine ⟨fun a b => c a b + c' a b, ?_, ?_⟩
  · intro a b hab
    have hab' : c a b + c' a b ≠ 0 := hab
    by_cases h : c a b = 0
    · rw [h, zero_add] at hab'
      exact (hc' a b hab').1
    · exact hc a b h
  · have hη : η = ν + (η - ν) := by abel
    rw [hη, hd, hν]
    simp only [Nat.cast_add, add_smul, Finset.sum_add_distrib]
    abel

end PositivityTheory.RgDs.Hilb
