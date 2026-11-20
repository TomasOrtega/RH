import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.Chcard
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.SumCharMulQuotientMatrixEqCharEvalMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.LinearIndependentCharactersOnQuotientReps

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

/- English proof (translation)
Introduce `A _ Ω _ _ Γ _ _ _ c ε hc hc1 hε z`. Establish `hcard` using `card_signedInvolutionChar_eq_card_involutionQuotient (Ω := Ω) c ε hc hc1 hε`. Set `e : Ch Ω c ε ≃ Qc c` to `Fintype.equivOfCardEq hcard`. Set `P : Matrix (Qc c) (Qc c) Ω` to `Matrix.of fun k i => ((e.symm k).1 (rep i) : Ω)`. Set `M : Matrix (Qc c) (Qc c) Ω` to `(algebraMap A Ω).mapMatrix (mat c ε z)`.

Set `d : Qc c → Ω` to `fun k => ev A (e.symm k).1 z`. Establish `hPM : P * M = Matrix.diagonal d * P`. Use extensionality with `k j`. Rewrite using `[Matrix.mul_apply, Matrix.diagonal_mul]`. Simplify using `only [P, M, d, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]`.

Conclude with `sum_char_mul_quotientMatrix_eq_charEval_mul c ε hc hc1 (e.symm k) z j`. Establish `hind : LinearIndependent Ω (fun k => P k)` using `(linearIndependent_characters_on_quotientReps (Ω := Ω) c ε hc).comp e.symm e.symm.injective`. Establish `hP : IsUnit P` using `Matrix.linearIndependent_rows_iff_isUnit.mp hind`. Establish `hdet : P.det ≠ 0` using `(Matrix.isUnit_iff_isUnit_det P |>.mp hP).ne_zero`. Establish `h2 : P.det * M.det = (∏ k, d k) * P.det`.

Rewrite using `[← Matrix.det_mul, hPM, Matrix.det_mul, Matrix.det_diagonal]`. Establish `h3 : M.det = ∏ k, d k`. Use `h2` as an intermediate fact. Rewrite `this` using `[mul_comm ((∏ k, d k))]`. Conclude with `mul_left_cancel₀ hdet this`.

Establish `h4 : algebraMap A Ω (detR c ε z) = M.det`. Unfold `detR`. Rewrite using `[RingHom.map_det]`. Rewrite using `[h4, h3]`. Conclude with `Equiv.prod_comp e.symm (fun χ => ev A χ.1 z)`.
-/
theorem UpperTheory.V.B5.det_mul_quotientByOrderTwo_eq_prod_charEval :
    ∀ {A : Type} [CommRing A] {Ω : Type} [Field Ω] [Algebra A Ω] {Γ : Type} [CommGroup Γ] [Finite Γ] [HasEnoughRootsOfUnity Ω (Monoid.exponent Γ)] (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ε * ε = 1 → ∀ z : MonoidAlgebra A Γ, algebraMap A Ω (detR c ε z) = ∏ χ : Ch Ω c ε, ev A χ.1 z := by
  intro A _ Ω _ _ Γ _ _ _ c ε hc hc1 hε z
  classical
  have hcard := card_signedInvolutionChar_eq_card_involutionQuotient (Ω := Ω) c ε hc hc1 hε
  let e : Ch Ω c ε ≃ Qc c := Fintype.equivOfCardEq hcard
  let P : Matrix (Qc c) (Qc c) Ω := Matrix.of fun k i => ((e.symm k).1 (rep i) : Ω)
  let M : Matrix (Qc c) (Qc c) Ω := (algebraMap A Ω).mapMatrix (mat c ε z)
  let d : Qc c → Ω := fun k => ev A (e.symm k).1 z
  have hPM : P * M = Matrix.diagonal d * P := by
    ext k j
    rw [Matrix.mul_apply, Matrix.diagonal_mul]
    simp only [P, M, d, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    exact sum_char_mul_quotientMatrix_eq_charEval_mul c ε hc hc1 (e.symm k) z j
  have hind : LinearIndependent Ω (fun k => P k) :=
    (linearIndependent_characters_on_quotientReps (Ω := Ω) c ε hc).comp e.symm e.symm.injective
  have hP : IsUnit P := Matrix.linearIndependent_rows_iff_isUnit.mp hind
  have hdet : P.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det P |>.mp hP).ne_zero
  have h2 : P.det * M.det = (∏ k, d k) * P.det := by
    rw [← Matrix.det_mul, hPM, Matrix.det_mul, Matrix.det_diagonal]
  have h3 : M.det = ∏ k, d k := by
    have := h2
    rw [mul_comm ((∏ k, d k))] at this
    exact mul_left_cancel₀ hdet this
  have h4 : algebraMap A Ω (detR c ε z) = M.det := by
    unfold detR
    rw [RingHom.map_det]
  rw [h4, h3]
  exact Equiv.prod_comp e.symm (fun χ => ev A χ.1 z)
