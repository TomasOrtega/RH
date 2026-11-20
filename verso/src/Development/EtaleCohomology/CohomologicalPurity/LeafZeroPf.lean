import Development.EtaleCohomology.CohomologicalPurity.LeafFlqPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Cl.Flq

/- English proof (translation)
Establish `h1 : Sec.map (𝟙 G) a = a` using `rfl`. Establish `h2 : Sec.map (0 : G ⟶ G) a = 0` using `rfl`. Rewrite using `[← h1, hG.eq_of_src (𝟙 G) 0, h2]`.
-/
theorem sec_eq_zero_of_isZero {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} (hG : IsZero G) (a : Sec G X) :
    a = 0 := by
  have h1 : Sec.map (𝟙 G) a = a := rfl
  have h2 : Sec.map (0 : G ⟶ G) a = 0 := rfl
  rw [← h1, hG.eq_of_src (𝟙 G) 0, h2]

/- English proof (translation)
Introduce `R _ K X U n hz`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `V W h a _`. Rewrite using `[sec_eq_zero_of_isZero hz (rs h a)]`. Conclude with `zero_mem _`.

Introduce `W a _`. Rewrite using `[sec_eq_zero_of_isZero hz a]`. Conclude with `zero_mem _`. Introduce `V W h a _`. Conclude with `⟨0, zero_mem _, (sec_eq_zero_of_isZero hz _).trans (sec_eq_zero_of_isZero hz a).symm⟩`.
-/
theorem LeafZero_of : LeafZero := by
  intro R _ K X U n hz
  refine ⟨?_, ?_, ?_⟩
  · intro V W h a _
    rw [sec_eq_zero_of_isZero hz (rs h a)]
    exact zero_mem _
  · intro W a _
    rw [sec_eq_zero_of_isZero hz a]
    exact zero_mem _
  · intro V W h a _
    exact ⟨0, zero_mem _, (sec_eq_zero_of_isZero hz _).trans (sec_eq_zero_of_isZero hz a).symm⟩

end LateralTheory.CohomologicalPurity.Cl.Flq
