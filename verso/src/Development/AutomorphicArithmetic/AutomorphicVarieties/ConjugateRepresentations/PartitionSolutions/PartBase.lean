import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
import Mathlib.Geometry.Manifold.PartitionOfUnity

noncomputable section

open scoped ContDiff Manifold Topology

namespace UpperTheory.V.Cj.A

/- English proof (translation)
Introduce `V _ _ _ Y hY D hD hDp`. Set `Y' : TopologicalSpace.Opens V` to `⟨Y, hY⟩`. Use `haveI : ProperSpace V := FiniteDimensional.proper_real V`. Use `haveI : LocallyCompactSpace Y' := Y'.isOpen.locallyCompactSpace`. Use `haveI : SecondCountableTopology V := inferInstance`.

Take `⟨f, hf⟩` from `SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, V) (M := Y') isClosed_univ (fun j => ((↑) : Y' → V) ⁻¹' D j) (fun j => (hD j).preimage continuous_subtype_val) (fun x _ => Set.mem_iUnion.2 ⟨(x : V), hDp x x.2⟩)`. Use `⟨fun j p => if h : p ∈ Y then f j ⟨p, h⟩ else 0, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j x hx`. Set `g : V → ℝ` to `fun p => if h : p ∈ Y then f j ⟨p, h⟩ else 0`. Establish `h1 : ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ) ∞ (fun y : Y' => g (y : V)) ⟨x, hx⟩`.

Establish `e : (fun y : Y' => g (y : V)) = f j`. Use function extensionality and compare the values at `y`. Conclude with `dif_pos y.2`. Rewrite using `[e]`. Conclude with `(f j).contMDiff.contMDiffAt`.

Establish `h2 : ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ) ∞ g x` using `(contMDiffAt_subtype_iff (U := Y') (f := g) (x := ⟨x, hx⟩)).1 h1`. Conclude with `(contMDiffAt_iff_contDiffAt.1 h2).contDiffWithinAt`. Introduce `p hp`. Take `⟨t, ht, htf⟩` from `f.locallyFinite ⟨p, hp⟩`. Take `⟨N, hN, hNt⟩` from `(mem_nhds_subtype _ _ _).1 ht`.

Use `⟨N, hN, htf.subset ?_⟩` and prove the remaining obligations. Introduce and unpack `j ⟨x, hxN, hne⟩`. Distinguish the cases in `hxY : x ∈ Y`. Establish `h : f j ⟨x, hxY⟩ ≠ 0` using `by simpa [hxY] using hne`. Conclude with `⟨⟨x, hxY⟩, h, hNt hxN⟩`.

Conclude with `(hne (dif_neg hxY)).elim`. Introduce `p hp`. Use `Eq.trans ?_ (f.sum_eq_one (x := ⟨p, hp⟩) (Set.mem_univ _))` and prove the remaining obligations. Conclude with `finsum_congr fun j => dif_pos hp`. Introduce `j p hne`.

Distinguish the cases in `hpY : p ∈ Y`. Establish `h : f j ⟨p, hpY⟩ ≠ 0` using `by simpa [hpY] using hne`. Conclude with `hf j (subset_tsupport _ h)`. Conclude with `(hne (dif_neg hpY)).elim`.
-/
theorem partBase : PartBase := by
  intro V _ _ _ Y hY D hD hDp
  let Y' : TopologicalSpace.Opens V := ⟨Y, hY⟩
  haveI : ProperSpace V := FiniteDimensional.proper_real V
  haveI : LocallyCompactSpace Y' := Y'.isOpen.locallyCompactSpace
  haveI : SecondCountableTopology V := inferInstance
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, V) (M := Y') isClosed_univ
    (fun j => ((↑) : Y' → V) ⁻¹' D j) (fun j => (hD j).preimage continuous_subtype_val)
    (fun x _ => Set.mem_iUnion.2 ⟨(x : V), hDp x x.2⟩)
  classical
  refine ⟨fun j p => if h : p ∈ Y then f j ⟨p, h⟩ else 0, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    let g : V → ℝ := fun p => if h : p ∈ Y then f j ⟨p, h⟩ else 0
    have h1 : ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ) ∞ (fun y : Y' => g (y : V)) ⟨x, hx⟩ := by
      have e : (fun y : Y' => g (y : V)) = f j := by
        funext y
        exact dif_pos y.2
      rw [e]
      exact (f j).contMDiff.contMDiffAt
    have h2 : ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ) ∞ g x :=
      (contMDiffAt_subtype_iff (U := Y') (f := g) (x := ⟨x, hx⟩)).1 h1
    exact (contMDiffAt_iff_contDiffAt.1 h2).contDiffWithinAt
  · intro p hp
    obtain ⟨t, ht, htf⟩ := f.locallyFinite ⟨p, hp⟩
    obtain ⟨N, hN, hNt⟩ := (mem_nhds_subtype _ _ _).1 ht
    refine ⟨N, hN, htf.subset ?_⟩
    rintro j ⟨x, hxN, hne⟩
    by_cases hxY : x ∈ Y
    · have h : f j ⟨x, hxY⟩ ≠ 0 := by simpa [hxY] using hne
      exact ⟨⟨x, hxY⟩, h, hNt hxN⟩
    · exact (hne (dif_neg hxY)).elim
  · intro p hp
    refine Eq.trans ?_ (f.sum_eq_one (x := ⟨p, hp⟩) (Set.mem_univ _))
    exact finsum_congr fun j => dif_pos hp
  · intro j p hne
    by_cases hpY : p ∈ Y
    · have h : f j ⟨p, hpY⟩ ≠ 0 := by simpa [hpY] using hne
      exact hf j (subset_tsupport _ h)
    · exact (hne (dif_neg hpY)).elim

end UpperTheory.V.Cj.A
