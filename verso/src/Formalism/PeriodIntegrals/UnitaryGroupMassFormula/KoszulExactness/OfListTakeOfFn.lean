import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KoszulExactness.Ii

noncomputable section

universe u

namespace PI.KoszulExact

open RingTheory.Sequence

/- English proof (translation)
Unfold `Ideal.ofList Ii`. Use `congr 1`. Use extensionality with `r`. Simplify using `only [Set.mem_setOf_eq, Set.mem_image]`. Rewrite using `[List.mem_iff_getElem]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨j, hj, rfl⟩`. Simplify using `only [List.length_take, List.length_ofFn] at hj`. Conclude with `⟨⟨j, by omega⟩, by simp only; omega, by simp⟩`. Introduce and unpack `⟨j, hj, rfl⟩`.

Use `j.isLt` as an intermediate fact. Conclude with `⟨j, by simp only [List.length_take, List.length_ofFn]; omega, by simp⟩`.
-/
theorem ofList_take_ofFn {R : Type u} [CommRing R] {D : ℕ} (s : Fin D → R) (i : ℕ) :
    Ideal.ofList ((List.ofFn s).take i) = Ii s i := by
  unfold Ideal.ofList Ii
  congr 1
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_image]
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simp only [List.length_take, List.length_ofFn] at hj
    exact ⟨⟨j, by omega⟩, by simp only; omega, by simp⟩
  · rintro ⟨j, hj, rfl⟩
    have := j.isLt
    exact ⟨j, by simp only [List.length_take, List.length_ofFn]; omega, by simp⟩

/- English proof (translation)
Establish `key` using `hs.regular_mod_prev i (by simp)`. Establish `hsm : (Ideal.ofList ((List.ofFn s).take i) • ⊤ : Submodule R R) = Ii s i`. Rewrite using `[Ideal.smul_eq_mul, Ideal.mul_top, ofList_take_ofFn]`. Establish `e : (List.ofFn s)[(i : ℕ)]'(by simp) = s i` using `by simp`. Rewrite `key` using `[e]`.

Establish `h1 : s i • (Submodule.Quotient.mk r : R ⧸ (Ideal.ofList ((List.ofFn s).take i) • ⊤ : Submodule R R)) = s i • 0`. Rewrite using `[smul_zero, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hsm, smul_eq_mul]`. Conclude with `hr`. Establish `h2` using `key h1`. Rewrite `h2` using `[Submodule.Quotient.mk_eq_zero, hsm]`. Then use the resulting hypothesis.
-/
theorem weak {R : Type u} [CommRing R] {D : ℕ} (s : Fin D → R)
    (hs : IsWeaklyRegular R (List.ofFn s)) (i : Fin D) (r : R) (hr : s i * r ∈ Ii s i) :
    r ∈ Ii s i := by
  have key := hs.regular_mod_prev i (by simp)
  have hsm : (Ideal.ofList ((List.ofFn s).take i) • ⊤ : Submodule R R) = Ii s i := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, ofList_take_ofFn]
  have e : (List.ofFn s)[(i : ℕ)]'(by simp) = s i := by simp
  rw [e] at key
  have h1 : s i • (Submodule.Quotient.mk r :
      R ⧸ (Ideal.ofList ((List.ofFn s).take i) • ⊤ : Submodule R R)) = s i • 0 := by
    rw [smul_zero, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hsm, smul_eq_mul]
    exact hr
  have h2 := key h1
  rwa [Submodule.Quotient.mk_eq_zero, hsm] at h2

end PI.KoszulExact
