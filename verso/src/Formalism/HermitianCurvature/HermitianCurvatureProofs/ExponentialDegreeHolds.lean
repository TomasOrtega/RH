import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapRWordsOfParts

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

/- English proof (translation)
Introduce `k r gens`. Proceed by induction on `gens with`. Consider the case `nil`. Introduce `_ t ht`. Simplify using `only [fexp, List.mem_singleton] at ht`.

Substitute `ht` using the available equality. Simplify using the standard rewrite rules. Consider the case `cons gn gs ih`. Introduce `hdeg t ht`. Establish `hgn : gn.1.natDegree ≤ 1` using `hdeg gn (by simp)`.

Establish `ih'` using `ih (fun g hg => hdeg g (List.mem_cons_of_mem _ hg))`. Simplify using `only [fexp, List.mem_append, List.mem_map, List.mem_flatMap] at ht`. Break down `ht with ⟨t', ht', rfl⟩ | ⟨dX, hdX, t', ht', rfl⟩` into its components or cases. Take `⟨h1, h2⟩` from `ih' t' ht'`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Use `Polynomial.natDegree_mul_le (p := gn.1) (q := t'.1)` as an intermediate fact. Simplify using `only [List.length_cons]`. Use linear arithmetic over natural numbers and integers. Introduce `X hX`. Take `⟨g, hg, d, hd⟩` from `h2 X hX`.

Conclude with `⟨g, List.mem_cons_of_mem _ hg, d, hd⟩`. Take `⟨h1, h2⟩` from `ih' t' ht'`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `Polynomial.natDegree_C_mul_le dX.1 t'.1` as an intermediate fact. Simplify using `only [List.length_cons]`.

Use linear arithmetic over natural numbers and integers. Introduce `X hX`. Break down `List.mem_cons.1 hX with rfl | hX` into its components or cases. Conclude with `⟨gn, by simp, dX.1, hdX⟩`. Take `⟨g, hg, d, hd⟩` from `h2 X hX`.

Conclude with `⟨g, List.mem_cons_of_mem _ hg, d, hd⟩`.
-/
theorem exponential_degree_holds : FExpDeg := by
  intro k r gens
  induction gens with
  | nil =>
    intro _ t ht
    simp only [fexp, List.mem_singleton] at ht
    subst ht
    simp
  | cons gn gs ih =>
    intro hdeg t ht
    have hgn : gn.1.natDegree ≤ 1 := hdeg gn (by simp)
    have ih' := ih (fun g hg => hdeg g (List.mem_cons_of_mem _ hg))
    simp only [fexp, List.mem_append, List.mem_map, List.mem_flatMap] at ht
    rcases ht with ⟨t', ht', rfl⟩ | ⟨dX, hdX, t', ht', rfl⟩
    · obtain ⟨h1, h2⟩ := ih' t' ht'
      refine ⟨?_, ?_⟩
      · have := Polynomial.natDegree_mul_le (p := gn.1) (q := t'.1)
        simp only [List.length_cons]
        omega
      · intro X hX
        obtain ⟨g, hg, d, hd⟩ := h2 X hX
        exact ⟨g, List.mem_cons_of_mem _ hg, d, hd⟩
    · obtain ⟨h1, h2⟩ := ih' t' ht'
      refine ⟨?_, ?_⟩
      · have := Polynomial.natDegree_C_mul_le dX.1 t'.1
        simp only [List.length_cons]
        omega
      · intro X hX
        rcases List.mem_cons.1 hX with rfl | hX
        · exact ⟨gn, by simp, dX.1, hdX⟩
        · obtain ⟨g, hg, d, hd⟩ := h2 X hX
          exact ⟨g, List.mem_cons_of_mem _ hg, d, hd⟩

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
