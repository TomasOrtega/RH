import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace PointIntegral

variable {n : ℕ}

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [zeroSet, Set.mem_ofPred_eq, Set.mem_singleton_iff, RingHom.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use function extensionality and compare the values at `i`.

Use `h (X i - C (p i)) (by simp)` as an intermediate fact. Simplify `this` using `[sub_eq_zero]`. Introduce and unpack `rfl q hq`. Conclude with `hq`.
-/
theorem zeroSet_ker_eval (p : Fin n → ℂ) :
    zeroSet (RingHom.ker (MvPolynomial.eval p)) = {p} := by
  ext x
  simp only [zeroSet, Set.mem_ofPred_eq, Set.mem_singleton_iff, RingHom.mem_ker]
  constructor
  · intro h
    funext i
    have := h (X i - C (p i)) (by simp)
    simpa [sub_eq_zero] using this
  · rintro rfl q hq
    exact hq

/- English proof (translation)
Establish `hsurj : Function.Surjective (projHom (RingHom.ker (MvPolynomial.eval p)) A)`. Introduce `q`. Take `⟨q, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Use `⟨C (eval p q), ?_⟩` and prove the remaining obligations. Simplify using `only [projHom, pullback, AlgHom.comp_apply, aeval_C, Ideal.Quotient.mkₐ_eq_mk]`.

Rewrite using `[Ideal.Quotient.eq, RingHom.mem_ker]`. Simplify using the standard rewrite rules. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `P Q hPQ`. Take `⟨a, rfl⟩ : ∃ a, P = C a` from `⟨coeff 0 P, (eq_C_of_isEmpty P)⟩`.

Take `⟨b, rfl⟩ : ∃ b, Q = C b` from `⟨coeff 0 Q, (eq_C_of_isEmpty Q)⟩`. Simplify using `only [projHom, pullback, AlgHom.comp_apply, aeval_C, Ideal.Quotient.mkₐ_eq_mk] at hPQ`. Rewrite `hPQ` using `[Ideal.Quotient.eq, RingHom.mem_ker]`. Simplify using `[sub_eq_zero] at hPQ`. Rewrite using `[hPQ]`.

Conclude with `RingHom.Finite.of_surjective _ hsurj`.
-/
theorem isFiniteProjection (p : Fin n → ℂ) (A : Matrix (Fin 0) (Fin n) ℂ) :
    IsFiniteProjection (RingHom.ker (MvPolynomial.eval p)) A := by
  have hsurj : Function.Surjective (projHom (RingHom.ker (MvPolynomial.eval p)) A) := by
    intro q
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨C (eval p q), ?_⟩
    simp only [projHom, pullback, AlgHom.comp_apply, aeval_C, Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq, RingHom.mem_ker]
    simp
  refine ⟨?_, ?_⟩
  · intro P Q hPQ
    obtain ⟨a, rfl⟩ : ∃ a, P = C a := ⟨coeff 0 P, (eq_C_of_isEmpty P)⟩
    obtain ⟨b, rfl⟩ : ∃ b, Q = C b := ⟨coeff 0 Q, (eq_C_of_isEmpty Q)⟩
    simp only [projHom, pullback, AlgHom.comp_apply, aeval_C, Ideal.Quotient.mkₐ_eq_mk] at hPQ
    rw [Ideal.Quotient.eq, RingHom.mem_ker] at hPQ
    simp [sub_eq_zero] at hPQ
    rw [hPQ]
  · exact RingHom.Finite.of_surjective _ hsurj

/- English proof (translation)
Introduce `n p f φ`. Use `set J := RingHom.ker (MvPolynomial.eval p)`. Establish `hZ : zeroSet J = {p}` using `zeroSet_ker_eval p`. Establish `hex : ∃ A : Matrix (Fin 0) (Fin n) ℂ, IsFiniteProjection J A` using `⟨0, isFiniteProjection p 0⟩`. Rewrite using `[varInt, dif_pos hex]`.

Use `set A := hex.choose`. Establish `hsheet : IsSheetAt J A p (fun _ => p)`. Use `⟨Set.univ, isOpen_univ, trivial, differentiableOn_const _, rfl, ?_, Set.univ, Filter.univ_mem, ?_⟩` and prove the remaining obligations. Introduce `y _`. Conclude with `⟨Subsingleton.elim _ _, by rw [hZ]; rfl⟩`.

Introduce `x hx _`. Rewrite `hx` using `[hZ]`. Conclude with `hx.1`. Establish `hfib : ∀ y, fibre J A y = {p}`. Introduce `y`.

Use extensionality with `x`. Simplify using `only [fibre, Set.mem_ofPred_eq, hZ, Set.mem_singleton_iff]`. Conclude with `⟨fun h => h.1, fun h => ⟨h, Subsingleton.elim _ _⟩⟩`. Establish `hdens : ∀ y, chartDens J A f φ y = f p`. Introduce `y`.

Rewrite using `[chartDens, sheetSum, hfib y, finsum_mem_singleton]`. Establish `hs : ∃ s, IsSheetAt J A p s` using `⟨_, hsheet⟩`. Rewrite using `[dif_pos hs]`. Simplify using `[ReciprocityTheory.AnForm.maDens, ReciprocityTheory.AnForm.mdisc_zero]`. Rewrite using `[chartInt]`.

Repeatedly rewrite using `[hdens]`. Simplify using `[Measure.real, MeasureTheory.volume_pi]`.
-/
theorem proof : PointIntegral.Statement := by
  intro n p f φ
  set J := RingHom.ker (MvPolynomial.eval p)
  have hZ : zeroSet J = {p} := zeroSet_ker_eval p
  have hex : ∃ A : Matrix (Fin 0) (Fin n) ℂ, IsFiniteProjection J A :=
    ⟨0, isFiniteProjection p 0⟩
  rw [varInt, dif_pos hex]
  set A := hex.choose
  have hsheet : IsSheetAt J A p (fun _ => p) := by
    refine ⟨Set.univ, isOpen_univ, trivial, differentiableOn_const _, rfl, ?_, Set.univ,
      Filter.univ_mem, ?_⟩
    · intro y _
      exact ⟨Subsingleton.elim _ _, by rw [hZ]; rfl⟩
    · intro x hx _
      rw [hZ] at hx
      exact hx.1
  have hfib : ∀ y, fibre J A y = {p} := by
    intro y
    ext x
    simp only [fibre, Set.mem_ofPred_eq, hZ, Set.mem_singleton_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, Subsingleton.elim _ _⟩⟩
  have hdens : ∀ y, chartDens J A f φ y = f p := by
    intro y
    rw [chartDens, sheetSum, hfib y, finsum_mem_singleton]
    have hs : ∃ s, IsSheetAt J A p s := ⟨_, hsheet⟩
    rw [dif_pos hs]
    simp [ReciprocityTheory.AnForm.maDens, ReciprocityTheory.AnForm.mdisc_zero]
  rw [chartInt]
  simp_rw [hdens]
  simp [Measure.real, MeasureTheory.volume_pi]

end PointIntegral

end

end GroundTheory.Heights₂.Heights
