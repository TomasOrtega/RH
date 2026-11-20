import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.KirCusp
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.Z.Desc.V0

/- English proof (translation)
Introduce `S R _ _ f hf n x hx`. Take `⟨hlow, hdiag⟩` from `(mem_unipB R).1 hx`. Set `A : Matrix (Fin n) (Fin n) S` to `fun i j => if i < j then Function.surjInv hf ((x : Matrix (Fin n) (Fin n) R) i j) else if i = j then 1 else 0`. Establish `hA : A.BlockTriangular id`. Introduce `i j hij`.

Establish `h1 : ¬ i < j` using `not_lt.2 (le_of_lt hij)`. Establish `h2 : i ≠ j` using `ne_of_gt hij`. Simplify using `[A, h1, h2]`. Establish `hdet : A.det = 1`. Rewrite using `[Matrix.det_of_upperTriangular hA]`.

Conclude with `Finset.prod_eq_one fun i _ => by simp [A]`. Establish `hunit : IsUnit A.det` using `by simp [hdet, isUnit_one]`. Establish `hcoe : ((GeneralLinearGroup.mk'' A hunit : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) = A` using `rfl`. Use `⟨GeneralLinearGroup.mk'' A hunit, (mem_unipB S).2 ⟨fun i j hji => ?_, fun i => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hcoe]`.

Conclude with `hA hji`. Rewrite using `[hcoe]`. Simplify using `[A]`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`.

Establish `hmap : ((GeneralLinearGroup.map (n` using `Fin n) f (GeneralLinearGroup.mk'' A hunit) : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j = f (A i j) := rfl`. Rewrite using `[hmap]`. Break down `lt_trichotomy i j with h | h | h` into its components or cases. Simplify using `only [A, if_pos h]`. Conclude with `Function.surjInv_eq hf _`.

Substitute `h` using the available equality. Simplify using `[A, hdiag]`. Establish `h1 : ¬ i < j` using `not_lt.2 (le_of_lt h)`. Establish `h2 : i ≠ j` using `ne_of_gt h`. Simplify using `[A, h1, h2, hlow i j h]`.
-/
theorem UpperTheory.unipotent_upper_map_surjective :
    ∀ {S R : Type} [CommRing S] [CommRing R] (f : S →+* R), Function.Surjective f → ∀ (n : ℕ) (x : GL (Fin n) R), x ∈ unipB R (Fin n) →
        ∃ y ∈ unipB S (Fin n), GeneralLinearGroup.map (n := Fin n) f y = x := by
  intro S R _ _ f hf n x hx
  obtain ⟨hlow, hdiag⟩ := (mem_unipB R).1 hx
  let A : Matrix (Fin n) (Fin n) S := fun i j =>
    if i < j then Function.surjInv hf ((x : Matrix (Fin n) (Fin n) R) i j) else if i = j then 1 else 0
  have hA : A.BlockTriangular id := by
    intro i j hij
    have h1 : ¬ i < j := not_lt.2 (le_of_lt hij)
    have h2 : i ≠ j := ne_of_gt hij
    simp [A, h1, h2]
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_upperTriangular hA]
    exact Finset.prod_eq_one fun i _ => by simp [A]
  have hunit : IsUnit A.det := by simp [hdet, isUnit_one]
  have hcoe : ((GeneralLinearGroup.mk'' A hunit : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) = A := rfl
  refine ⟨GeneralLinearGroup.mk'' A hunit, (mem_unipB S).2 ⟨fun i j hji => ?_, fun i => ?_⟩, ?_⟩
  · rw [hcoe]
    exact hA hji
  · rw [hcoe]
    simp [A]
  · apply Units.ext
    ext i j
    have hmap : ((GeneralLinearGroup.map (n := Fin n) f (GeneralLinearGroup.mk'' A hunit) : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j = f (A i j) := rfl
    rw [hmap]
    rcases lt_trichotomy i j with h | h | h
    · simp only [A, if_pos h]
      exact Function.surjInv_eq hf _
    · subst h
      simp [A, hdiag]
    · have h1 : ¬ i < j := not_lt.2 (le_of_lt h)
      have h2 : i ≠ j := ne_of_gt h
      simp [A, h1, h2, hlow i j h]
