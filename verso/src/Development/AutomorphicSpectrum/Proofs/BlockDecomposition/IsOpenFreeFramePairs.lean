import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FreeFrames

/- English proof (translation)
Rewrite using `[isOpen_iff_mem_nhds]`. Introduce and unpack `z₀ ⟨L₁, L₂, h11, h12, h21, h22⟩`. Set `L : Matrix (Fin r ⊕ Fin t) (Fin a) R` to `Matrix.fromRows L₁ L₂`. Set `Z : Matrix (Fin a) (Fin r) R × Matrix (Fin a) (Fin t) R → Matrix (Fin a) (Fin r ⊕ Fin t) R` to `fun z => Matrix.fromCols (e • z.1) (e • z.2)`. Set `C : Matrix (Fin a) (Fin r) R × Matrix (Fin a) (Fin t) R → Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R` to `fun z => L * Z z + (1 - e) • (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R)`.

Establish `hone : (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R) = Matrix.fromBlocks 1 0 0 1` using `Matrix.fromBlocks_one.symm`. Establish `hLZ : L * Z z₀ = e • (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R)`. Simplify using `only [L, Z]`. Rewrite using `[Matrix.fromRows_mul_fromCols, h11, h12, h21, h22, hone, Matrix.fromBlocks_smul]`. Simplify using `only [smul_zero]`.

Establish `hC0 : C z₀ = 1`. Simplify using `only [C]`. Rewrite using `[hLZ, ← add_smul]`. Simplify using the standard rewrite rules. Establish `hZc : Continuous Z`.

Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Consider the cases of `j with`. Consider the case `inl j`. Establish `h : Continuous fun z : Matrix (Fin a) (Fin r) R × Matrix (Fin a) (Fin t) R => e * z.1 i j` using `Continuous.mul continuous_const (continuous_fst.matrix_elem i j)`. Simplify `h` using `[Z]`.

Consider the case `inr j`. Establish `h : Continuous fun z : Matrix (Fin a) (Fin r) R × Matrix (Fin a) (Fin t) R => e * z.2 i j` using `Continuous.mul continuous_const (continuous_snd.matrix_elem i j)`. Simplify `h` using `[Z]`. Establish `hCc : Continuous C`. Conclude with `(continuous_const.matrix_mul hZc).add continuous_const`.

Establish `hd : Continuous fun z => (C z).det` using `hCc.matrix_det`. Establish `hnhds : (fun z => (C z).det) ⁻¹' U ∈ 𝓝 z₀`. Use `(hU.preimage hd).mem_nhds ?_` and prove the remaining obligations. Simplify `h1` using `[Set.mem_preimage, hC0]`. Use `Filter.mem_of_superset hnhds ?_` and prove the remaining obligations.

Introduce `z hz`. Take `⟨b, hb'⟩` from `hb _ hz`. Establish `hLz : L * Z z = C z - (1 - e) • (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R)`. Simplify using `only [C, add_sub_cancel_right]`. Establish `hee : e * (1 - e) = 0` using `by rw [mul_sub, he, mul_one, sub_self]`.

Establish `key : ((e * b) • ((C z).adjugate * L)) * Z z = e • (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R)`. Rewrite using `[Matrix.smul_mul, Matrix.mul_assoc, hLz, Matrix.mul_sub, Matrix.adjugate_mul, Matrix.mul_smul, Matrix.mul_one, smul_sub, smul_smul, smul_smul]`. Establish `h2 : e * b * (1 - e) = 0`. Rewrite using `[mul_right_comm, hee, zero_mul]`. Establish `h3 : e * b * (C z).det = e`.

Rewrite using `[mul_assoc, mul_comm b, hb', he]`. Rewrite using `[h2, h3, zero_smul, sub_zero]`. Use `set L' := (e * b) • ((C z).adjugate * L) with hL'`. Establish `key' : Matrix.fromBlocks (L'.toRows₁ * (e • z.1)) (L'.toRows₁ * (e • z.2)) (L'.toRows₂ * (e • z.1)) (L'.toRows₂ * (e • z.2)) = Matrix.fromBlocks (e • 1) 0 0 (e • 1)`. Rewrite using `[← Matrix.fromRows_mul_fromCols, Matrix.fromRows_toRows]`.

Use `key` as an intermediate fact. Simplify using `only [Z] at this`. Rewrite using `[this, hone, Matrix.fromBlocks_smul]`. Simplify using `only [smul_zero]`. Take `⟨a1, a2, a3, a4⟩` from `Matrix.fromBlocks_inj.1 key'`.

Conclude with `⟨L'.toRows₁, L'.toRows₂, a1, a2, a3, a4⟩`.
-/
theorem isOpen_free_frame_pairs {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (r t a : ℕ) (e : R) (he : e * e = e) (U : Set R) (hU : IsOpen U) (h1 : (1 : R) ∈ U)
    (hb : ∀ x ∈ U, ∃ b, x * b = e) :
    IsOpen {z : Matrix (Fin a) (Fin r) R × Matrix (Fin a) (Fin t) R |
      ∃ (L₁ : Matrix (Fin r) (Fin a) R) (L₂ : Matrix (Fin t) (Fin a) R),
        L₁ * (e • z.1) = e • 1 ∧ L₁ * (e • z.2) = 0 ∧ L₂ * (e • z.1) = 0 ∧ L₂ * (e • z.2) = e • 1} := by
  classical
  rw [isOpen_iff_mem_nhds]
  rintro z₀ ⟨L₁, L₂, h11, h12, h21, h22⟩
  let L : Matrix (Fin r ⊕ Fin t) (Fin a) R := Matrix.fromRows L₁ L₂
  let Z : Matrix (Fin a) (Fin r) R × Matrix (Fin a) (Fin t) R → Matrix (Fin a) (Fin r ⊕ Fin t) R :=
    fun z => Matrix.fromCols (e • z.1) (e • z.2)
  let C : Matrix (Fin a) (Fin r) R × Matrix (Fin a) (Fin t) R → Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R :=
    fun z => L * Z z + (1 - e) • (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R)
  have hone : (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R) = Matrix.fromBlocks 1 0 0 1 :=
    Matrix.fromBlocks_one.symm
  have hLZ : L * Z z₀ = e • (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R) := by
    simp only [L, Z]
    rw [Matrix.fromRows_mul_fromCols, h11, h12, h21, h22, hone, Matrix.fromBlocks_smul]
    simp only [smul_zero]
  have hC0 : C z₀ = 1 := by
    simp only [C]
    rw [hLZ, ← add_smul]
    simp
  have hZc : Continuous Z := by
    refine continuous_matrix fun i j => ?_
    cases j with
    | inl j =>
      have h : Continuous fun z : Matrix (Fin a) (Fin r) R × Matrix (Fin a) (Fin t) R => e * z.1 i j :=
        Continuous.mul continuous_const (continuous_fst.matrix_elem i j)
      simpa [Z] using h
    | inr j =>
      have h : Continuous fun z : Matrix (Fin a) (Fin r) R × Matrix (Fin a) (Fin t) R => e * z.2 i j :=
        Continuous.mul continuous_const (continuous_snd.matrix_elem i j)
      simpa [Z] using h
  have hCc : Continuous C := by
    exact (continuous_const.matrix_mul hZc).add continuous_const
  have hd : Continuous fun z => (C z).det := hCc.matrix_det
  have hnhds : (fun z => (C z).det) ⁻¹' U ∈ 𝓝 z₀ := by
    refine (hU.preimage hd).mem_nhds ?_
    simpa [Set.mem_preimage, hC0] using h1
  refine Filter.mem_of_superset hnhds ?_
  intro z hz
  obtain ⟨b, hb'⟩ := hb _ hz
  have hLz : L * Z z = C z - (1 - e) • (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R) := by
    simp only [C, add_sub_cancel_right]
  have hee : e * (1 - e) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  have key : ((e * b) • ((C z).adjugate * L)) * Z z = e • (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R) := by
    rw [Matrix.smul_mul, Matrix.mul_assoc, hLz, Matrix.mul_sub, Matrix.adjugate_mul, Matrix.mul_smul,
      Matrix.mul_one, smul_sub, smul_smul, smul_smul]
    have h2 : e * b * (1 - e) = 0 := by
      rw [mul_right_comm, hee, zero_mul]
    have h3 : e * b * (C z).det = e := by
      rw [mul_assoc, mul_comm b, hb', he]
    rw [h2, h3, zero_smul, sub_zero]
  set L' := (e * b) • ((C z).adjugate * L) with hL'
  have key' : Matrix.fromBlocks (L'.toRows₁ * (e • z.1)) (L'.toRows₁ * (e • z.2))
      (L'.toRows₂ * (e • z.1)) (L'.toRows₂ * (e • z.2)) =
      Matrix.fromBlocks (e • 1) 0 0 (e • 1) := by
    rw [← Matrix.fromRows_mul_fromCols, Matrix.fromRows_toRows]
    have := key
    simp only [Z] at this
    rw [this, hone, Matrix.fromBlocks_smul]
    simp only [smul_zero]
  obtain ⟨a1, a2, a3, a4⟩ := Matrix.fromBlocks_inj.1 key'
  exact ⟨L'.toRows₁, L'.toRows₂, a1, a2, a3, a4⟩

/- English proof (translation)
Introduce and unpack `D r t a e he ⟨U, hU, h1, hb⟩`. Conclude with `isOpen_free_frame_pairs r t a e he U hU h1 hb`.
-/
theorem isOpen_free : ∀ (D : D7) (r t a : ℕ) (e : AE D), e * e = e →
    (∃ U : Set (AE D), IsOpen U ∧ 1 ∈ U ∧ ∀ x ∈ U, ∃ b, x * b = e) →
    IsOpen {z : Mx D a r × Mx D a t | Free e (e • z.1, e • z.2)} := by
  rintro D r t a e he ⟨U, hU, h1, hb⟩
  exact isOpen_free_frame_pairs r t a e he U hU h1 hb

end GlobalTheory.CompanionTheory.FreeFrames
