import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg

open Polynomial UpperTheory.V.W

/- English proof (translation)
Introduce `A G _ _ B _ _ x`. Establish `hs : ∀ g : G, MonoidAlgebra.mapRingHom G (algebraMap A B) (MonoidAlgebra.single g 1) = MonoidAlgebra.single g (1 : B)`. Introduce `g`. Simplify using the standard rewrite rules. Simplify using `only [hs]`.

Proceed by induction on `x using MonoidAlgebra.induction_on with`. Consider the case `of g`. Conclude with `⟨1, fun _ => g, fun _ => 1, by simp [MonoidAlgebra.of_apply]⟩`. Consider the case `add x y hx hy`. Take `⟨m, g, b, rfl⟩` from `hx`.

Take `⟨n, h, c, rfl⟩` from `hy`. Use `⟨m + n, Fin.append g h, Fin.append b c, ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_add]`. Simplify using `[Fin.append_left, Fin.append_right]`. Consider the case `smul r x hx`.

Take `⟨m, g, b, rfl⟩` from `hx`. Use `⟨m, g, fun j => r * b j, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.smul_sum]`. Simplify using `[smul_smul]`.
-/
theorem UpperTheory.V.AlgebraTools.Det.genSpan :
    ∀ {A G : Type} [CommRing A] [Group G] (B : Type) [CommRing B] [Algebra A B] (x : MonoidAlgebra B G),
    ∃ (m : ℕ) (g : Fin m → G) (b : Fin m → B), x = ∑ j, b j • MonoidAlgebra.mapRingHom G (algebraMap A B) (MonoidAlgebra.single (g j) 1) := by
  intro A G _ _ B _ _ x
  have hs : ∀ g : G, MonoidAlgebra.mapRingHom G (algebraMap A B) (MonoidAlgebra.single g 1)
      = MonoidAlgebra.single g (1 : B) := by
    intro g
    simp
  simp only [hs]
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    exact ⟨1, fun _ => g, fun _ => 1, by simp [MonoidAlgebra.of_apply]⟩
  | add x y hx hy =>
    obtain ⟨m, g, b, rfl⟩ := hx
    obtain ⟨n, h, c, rfl⟩ := hy
    refine ⟨m + n, Fin.append g h, Fin.append b c, ?_⟩
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
  | smul r x hx =>
    obtain ⟨m, g, b, rfl⟩ := hx
    refine ⟨m, g, fun j => r * b j, ?_⟩
    rw [Finset.smul_sum]
    simp [smul_smul]
