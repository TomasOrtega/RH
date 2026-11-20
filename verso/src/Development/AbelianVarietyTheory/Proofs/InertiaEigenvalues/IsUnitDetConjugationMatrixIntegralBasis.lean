import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

namespace GlobalTheory.UnitLemma.Unr

/- English proof (translation)
Introduce `K K' d φ hφ`. Use `letI : Algebra K.E K'.E := φ.toAlgebra`. Introduce `w hw`. Use `set C : Matrix (Fin d) (Fin d) K.E := Matrix.of fun m l => w.repr (K'.c (w l)) m with hC`. Establish `hsm : ∀ (e : K.E) (x : K'.E), e • x = φ e * x` using `fun e x => rfl`.

Establish `hint : ∀ m l, ∃ a : K.O, algebraMap K.O K.E a = C m l`. Introduce `m l`. Establish `h1 : ∃ y : K'.O, algebraMap K'.O K'.E y = w l`. Rewrite using `[hw]`. Introduce `k`.

Rewrite using `[w.repr_self]`. Distinguish the cases in `h : l = k`. Substitute `h; exact ⟨1, by simp⟩` using the available equality. Conclude with `⟨0, by simp [Finsupp.single_apply, h]⟩`. Take `⟨y, hy⟩` from `h1`.

Take `⟨y', hy'⟩` from `K'.c_int y`. Establish `h2 : ∃ y : K'.O, algebraMap K'.O K'.E y = K'.c (w l)` using `⟨y', by rw [← hy', hy]⟩`. Conclude with `(hw _).1 h2 m`. Use `choose A hA using hint`. Establish `hrep : ∀ (x : K'.E) (n : Fin d), w.repr (K'.c x) n = ∑ m, K.c (w.repr x m) * C n m`.

Introduce `x n`. Establish `hx : K'.c x = ∑ m, K.c (w.repr x m) • K'.c (w m)` using `by conv_lhs => rw [← w.sum_repr x]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[hsm, hsm, map_mul, ← hφ]`.

Rewrite using `[hx, map_sum, Finsupp.finset_sum_apply]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Finsupp.smul_apply, smul_eq_mul]`. Both sides reduce to the same expression. Establish `hCC : C * (K.c : K.E →+* K.E).mapMatrix C = 1`.

Use extensionality with `n l`. Establish `h` using `hrep (K'.c (w l)) n`. Rewrite `h` using `[K'.c_c, w.repr_self, Finsupp.single_apply]`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.coe_coe]`.

Rewrite using `[eq_comm]`. Use `h using 1` and compare the differences between its conclusion and the goal. Conclude with `if_congr eq_comm rfl rfl`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`.

Both sides reduce to the same expression. Establish `hdet : C.det * K.c C.det = 1`. Establish `h` using `congrArg Matrix.det hCC`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_one, ← RingHom.map_det]`. Conclude with `h`.

Establish `hdetA : algebraMap K.O K.E (Matrix.of A).det = C.det`. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `m l`. Simplify using `[hA]`.

Use `⟨(Matrix.of A).det, ?_, hdetA⟩` and prove the remaining obligations. Take `⟨β, hβ⟩` from `K.c_int (Matrix.of A).det`. Apply `IsUnit.of_mul_eq_one β` to reduce the goal to its premises. Apply `IsFractionRing.injective K.O K.E` to reduce the goal to its premises. Rewrite using `[map_mul, ← hβ, hdetA, hdet, map_one]`.
-/
theorem conj_matrix_det_isUnit : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), (∀ x, φ (K.c x) = K'.c (φ x)) → letI : Algebra K.E K'.E := φ.toAlgebra; ∀ w : Module.Basis (Fin d) K.E K'.E, (∀ z : K'.E, (∃ y : K'.O, algebraMap K'.O K'.E y = z) ↔ ∀ k, ∃ a : K.O, algebraMap K.O K.E a = w.repr z k) → ∃ u : K.O, IsUnit u ∧ algebraMap K.O K.E u = (Matrix.of fun m l => w.repr (K'.c (w l)) m).det := by
  intro K K' d φ hφ
  letI : Algebra K.E K'.E := φ.toAlgebra
  intro w hw
  set C : Matrix (Fin d) (Fin d) K.E := Matrix.of fun m l => w.repr (K'.c (w l)) m with hC
  have hsm : ∀ (e : K.E) (x : K'.E), e • x = φ e * x := fun e x => rfl
  have hint : ∀ m l, ∃ a : K.O, algebraMap K.O K.E a = C m l := by
    intro m l
    have h1 : ∃ y : K'.O, algebraMap K'.O K'.E y = w l := by
      rw [hw]
      intro k
      rw [w.repr_self]
      by_cases h : l = k
      · subst h; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [Finsupp.single_apply, h]⟩
    obtain ⟨y, hy⟩ := h1
    obtain ⟨y', hy'⟩ := K'.c_int y
    have h2 : ∃ y : K'.O, algebraMap K'.O K'.E y = K'.c (w l) := ⟨y', by rw [← hy', hy]⟩
    exact (hw _).1 h2 m
  choose A hA using hint
  have hrep : ∀ (x : K'.E) (n : Fin d), w.repr (K'.c x) n = ∑ m, K.c (w.repr x m) * C n m := by
    intro x n
    have hx : K'.c x = ∑ m, K.c (w.repr x m) • K'.c (w m) := by
      conv_lhs => rw [← w.sum_repr x]
      rw [map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hsm, hsm, map_mul, ← hφ]
    rw [hx, map_sum, Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    rfl
  have hCC : C * (K.c : K.E →+* K.E).mapMatrix C = 1 := by
    ext n l
    have h := hrep (K'.c (w l)) n
    rw [K'.c_c, w.repr_self, Finsupp.single_apply] at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.coe_coe]
    rw [eq_comm]
    convert h using 1
    · exact if_congr eq_comm rfl rfl
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_comm]
    rfl
  have hdet : C.det * K.c C.det = 1 := by
    have h := congrArg Matrix.det hCC
    rw [Matrix.det_mul, Matrix.det_one, ← RingHom.map_det] at h
    exact h
  have hdetA : algebraMap K.O K.E (Matrix.of A).det = C.det := by
    rw [RingHom.map_det]
    congr 1
    ext m l
    simp [hA]
  refine ⟨(Matrix.of A).det, ?_, hdetA⟩
  obtain ⟨β, hβ⟩ := K.c_int (Matrix.of A).det
  apply IsUnit.of_mul_eq_one β
  apply IsFractionRing.injective K.O K.E
  rw [map_mul, ← hβ, hdetA, hdet, map_one]

end GlobalTheory.UnitLemma.Unr
