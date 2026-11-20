import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveCompact
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.AcycDirected

open Set UpperTheory.V.ConeExtensionAcyclic

/- English proof (translation)
Introduce `I F _ _ X A hX hne hcl hcv hfin hcov`. Apply `acyc_directed` to reduce the goal to its premises. Introduce `n s hs`. Establish `hw : ∀ t ∈ (s : Set (Fin n → I)), ∃ x ∈ X, ∀ j, x ∈ A (t j)` using `fun t ht => hs ht`. Use `choose! w hwX hwA using hw`.

Take `⟨x0, hx0⟩` from `hne`. Set `P : Set F` to `insert x0 (w '' (s : Set (Fin n → I)))`. Establish `hPfin : P.Finite` using `(s.finite_toSet.image w).insert x0`. Establish `hPX : P ⊆ X`. Introduce `x hx`.

Break down `hx with rfl | ⟨t, ht, rfl⟩` into its components or cases. Conclude with `hx0`. Conclude with `hwX t ht`. Set `K : Set F` to `convexHull ℝ P`. Establish `hKX : K ⊆ X` using `convexHull_min hPX hX`.

Establish `hKc : IsCompact K` using `hPfin.isCompact_convexHull (𝕜 := ℝ)`. Use `⟨nerve K A, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `k t ht`. Take `⟨x, hx, hxA⟩` from `ht`. Conclude with `⟨x, hKX hx, hxA⟩`.

Introduce `t ht`. Use `⟨w t, subset_convexHull ℝ P (Set.mem_insert_of_mem _ ⟨t, ht, rfl⟩), hwA t ht⟩` and prove the remaining obligations. Apply `nerve_compact K A hKc (convex_convexHull ℝ P) ⟨x0, subset_convexHull ℝ P (Set.mem_insert _ _)⟩ hcl hcv (hfin P hPfin hPX)` to reduce the goal to its premises. Introduce `x hx`. Conclude with `hcov x (hKX hx)`.
-/
theorem UpperTheory.V.ConeExtensionAcyclic.nerve_convex :
    ∀ {I F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (X : Set F) (A : I → Set F), Convex ℝ X → X.Nonempty → (∀ i, IsClosed (A i)) → (∀ i, Convex ℝ (A i)) → (∀ s : Set F, s.Finite → s ⊆ X → {i | (convexHull ℝ s ∩ A i).Nonempty}.Finite) → (∀ x ∈ X, ∃ i, x ∈ A i) → Acyc (nerve X A) := by
  intro I F _ _ X A hX hne hcl hcv hfin hcov
  apply acyc_directed
  intro n s hs
  have hw : ∀ t ∈ (s : Set (Fin n → I)), ∃ x ∈ X, ∀ j, x ∈ A (t j) := fun t ht => hs ht
  choose! w hwX hwA using hw
  obtain ⟨x0, hx0⟩ := hne
  let P : Set F := insert x0 (w '' (s : Set (Fin n → I)))
  have hPfin : P.Finite := (s.finite_toSet.image w).insert x0
  have hPX : P ⊆ X := by
    intro x hx
    rcases hx with rfl | ⟨t, ht, rfl⟩
    · exact hx0
    · exact hwX t ht
  let K : Set F := convexHull ℝ P
  have hKX : K ⊆ X := convexHull_min hPX hX
  have hKc : IsCompact K := hPfin.isCompact_convexHull (𝕜 := ℝ)
  refine ⟨nerve K A, ?_, ?_, ?_⟩
  · intro k t ht
    obtain ⟨x, hx, hxA⟩ := ht
    exact ⟨x, hKX hx, hxA⟩
  · intro t ht
    refine ⟨w t, subset_convexHull ℝ P (Set.mem_insert_of_mem _ ⟨t, ht, rfl⟩), hwA t ht⟩
  · apply nerve_compact K A hKc (convex_convexHull ℝ P)
      ⟨x0, subset_convexHull ℝ P (Set.mem_insert _ _)⟩ hcl hcv (hfin P hPfin hPX)
    intro x hx
    exact hcov x (hKX hx)
