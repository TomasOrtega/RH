import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColJoinColLColR

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.Orth

variable {D : D7}

/- English proof (translation)
Establish `h : LinearMap.mulLeft (AF D.host.F) (incA D e) = LinearMap.baseChange (AF D.host.F) (LinearMap.mulLeft D.host.F e)`. Use extensionality with `b`. Simplify using `[TensorProduct.AlgebraTensorModule.curry_apply, incA, inclR, LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]`. Simplify using `only [trA, Algebra.trace_apply]`. Express the relevant statement in the definitionally equal form `LinearMap.trace _ _ (LinearMap.mulLeft (AF D.host.F) (incA D e)) = algebraMap _ _ (LinearMap.trace _ _ (LinearMap.mulLeft D.host.F e))`.

Rewrite using `[h, LinearMap.trace_baseChange]`.
-/
theorem trA_incA_eq (e : D.host.E) :
    trA (incA D e) =
      algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E e) := by
  have h : LinearMap.mulLeft (AF D.host.F) (incA D e) =
      LinearMap.baseChange (AF D.host.F) (LinearMap.mulLeft D.host.F e) := by
    ext b
    simp [TensorProduct.AlgebraTensorModule.curry_apply, incA, inclR, LinearMap.baseChange_tmul,
      Algebra.TensorProduct.tmul_mul_tmul]
  simp only [trA, Algebra.trace_apply]
  change LinearMap.trace _ _ (LinearMap.mulLeft (AF D.host.F) (incA D e)) =
    algebraMap _ _ (LinearMap.trace _ _ (LinearMap.mulLeft D.host.F e))
  rw [h, LinearMap.trace_baseChange]

/- English proof (translation)
Establish `hE` using `D.host.toHostAx.der.finrank_E`. Establish `hF` using `D.host.toHostAx.der.finrank_F`. Establish `hpos : 0 < Module.finrank ℚ D.host.F` using `Module.finrank_pos`. Establish `htow` using `Module.finrank_mul_finrank ℚ D.host.F D.host.E`. Establish `h2 : Module.finrank D.host.F D.host.E = 2`.

Rewrite `hpos`, `htow` using `[hF]`. Rewrite `htow` using `[hE]`. Establish `h4 : 2 * D.R.ord * Module.finrank D.host.F D.host.E = 2 * D.R.ord * 2`. Rewrite using `[htow]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `Nat.eq_of_mul_eq_mul_left hpos h4`. Establish `hhalf : trA (half D) = 1`. Rewrite using `[half, trA_incA_eq]`. Establish `: (1 / 2 : D.host.E) = algebraMap D.host.F D.host.E (1 / 2)`. Rewrite using `[map_div₀, map_one, map_ofNat]`.

Rewrite using `[this, Algebra.trace_algebraMap, h2]`. Evaluate the numerical expressions. Establish `hlin : trA (x • half D) = x * trA (half D)`. Simplify using `only [trA, map_smul, smul_eq_mul]`. Rewrite using `[hlin, hhalf, mul_one]`.
-/
theorem trA_smul_half (x : AF D.host.F) :
    trA (x • half D) = x := by
  have hE := D.host.toHostAx.der.finrank_E
  have hF := D.host.toHostAx.der.finrank_F
  have hpos : 0 < Module.finrank ℚ D.host.F := Module.finrank_pos
  have htow := Module.finrank_mul_finrank ℚ D.host.F D.host.E
  have h2 : Module.finrank D.host.F D.host.E = 2 := by
    rw [hF] at hpos htow
    rw [hE] at htow
    have h4 : 2 * D.R.ord * Module.finrank D.host.F D.host.E = 2 * D.R.ord * 2 := by
      rw [htow]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos h4
  have hhalf : trA (half D) = 1 := by
    rw [half, trA_incA_eq]
    have : (1 / 2 : D.host.E) = algebraMap D.host.F D.host.E (1 / 2) := by
      rw [map_div₀, map_one, map_ofNat]
    rw [this, Algebra.trace_algebraMap, h2]
    norm_num
  have hlin : trA (x • half D) = x * trA (half D) := by
    simp only [trA, map_smul, smul_eq_mul]
  rw [hlin, hhalf, mul_one]

/- English proof (translation)
Simplify using `only [GlobalTheory.StdUnn.inner]`. Rewrite using `[← rat_conjTranspose, gA, ← Matrix.mul_assoc, ← rat_mul]`.
-/
theorem inner_rat_eq (V : HSp D) {s : ℕ} (q : Matrix (Fin V.rank) (Fin s) D.host.E) (y : Mx D V.rank s) :
    GlobalTheory.StdUnn.inner V (rat q) y = rat (qᴴ * V.gram) ⬝ y := by
  simp only [GlobalTheory.StdUnn.inner]
  rw [← rat_conjTranspose, gA, ← Matrix.mul_assoc, ← rat_mul]

/- English proof (translation)
Simplify using `only [GlobalTheory.StdUnn.inner, Matrix.mul_add, Matrix.trace_add, trA, map_add, AddChar.map_add_eq_mul]`.
-/
theorem chi_add (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {s : ℕ} (x y u : Mx D V.rank s) :
    ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V x (y + u)))) =
      ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V x y))) * ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V x u))) := by
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_add, Matrix.trace_add, trA, map_add, AddChar.map_add_eq_mul]

/- English proof (translation)
Take `⟨g, rfl⟩` from `mem_ratMx.mp hγ`. Establish `htr : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E), Matrix.trace (rat M) = incA D (Matrix.trace M)`. Introduce `n M`. Simplify using `[rat, Matrix.trace, map_sum]`. Rewrite using `[inner_rat_eq]`.

Express the relevant statement in the definitionally equal form `ψ (trA (Matrix.trace (rat (qᴴ * V.gram) * rat g))) = 1`. Rewrite using `[← rat_mul, htr, trA_incA_eq]`. Conclude with `hψ.2.2.1 _`.
-/
theorem chi_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) {s : ℕ}
    (q : Matrix (Fin V.rank) (Fin s) D.host.E) {γ : Mx D V.rank s} (hγ : γ ∈ ratMx D V.rank s) :
    ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V (rat q) γ))) = 1 := by
  obtain ⟨g, rfl⟩ := mem_ratMx.mp hγ
  have htr : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E), Matrix.trace (rat M) = incA D (Matrix.trace M) := by
    intro n M
    simp [rat, Matrix.trace, map_sum]
  rw [inner_rat_eq]
  change ψ (trA (Matrix.trace (rat (qᴴ * V.gram) * rat g))) = 1
  rw [← rat_mul, htr, trA_incA_eq]
  exact hψ.2.2.1 _

/- English proof (translation)
Take `⟨x, hx⟩` from `hψ.2.2.2`. Establish `hM : qᴴ * V.gram ≠ 0`. Introduce `h`. Apply `hq` to reduce the goal to its premises. Establish `h1 : qᴴ = 0`.

Rewrite using `[← Matrix.mul_nonsing_inv_cancel_right V.gram qᴴ (gram_isUnit_det V), h, Matrix.zero_mul]`. Simplify using `using congrArg Matrix.conjTranspose h1`. Choose the witnesses or unpack the hypotheses as in `⟨i, j, hij⟩ : ∃ i j, (qᴴ * V.gram) i j ≠ 0 := by`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`.

Conclude with `hM (Matrix.ext hne)`. Establish `key : ∀ (A : Mx D s V.rank) (c : AE D), Matrix.trace (A * Matrix.single j i c) = A i j * c`. Introduce `A c`. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply, ite_and, mul_ite, mul_zero]`. Simplify using `[Finset.sum_ite_eq, Finset.sum_ite_eq']`.

Use `⟨Matrix.single j i (incA D ((qᴴ * V.gram) i j)⁻¹ * (x • half D)), ?_⟩` and prove the remaining obligations. Rewrite using `[inner_rat_eq]`. Express the relevant statement in the definitionally equal form `ψ (trA (Matrix.trace (rat (qᴴ * V.gram) * Matrix.single j i (incA D ((qᴴ * V.gram) i j)⁻¹ * (x • half D))))) ≠ 1`. Rewrite using `[key, show rat (qᴴ * V.gram) i j = incA D ((qᴴ * V.gram) i j) from rfl, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hij, map_one, one_mul, trA_smul_half]`. Conclude with `hx`.
-/
theorem exists_chi_ne_one {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) {s : ℕ}
    {q : Matrix (Fin V.rank) (Fin s) D.host.E} (hq : q ≠ 0) :
    ∃ u : Mx D V.rank s, ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V (rat q) u))) ≠ 1 := by
  obtain ⟨x, hx⟩ := hψ.2.2.2
  have hM : qᴴ * V.gram ≠ 0 := by
    intro h
    apply hq
    have h1 : qᴴ = 0 := by
      rw [← Matrix.mul_nonsing_inv_cancel_right V.gram qᴴ (gram_isUnit_det V), h, Matrix.zero_mul]
    simpa using congrArg Matrix.conjTranspose h1
  obtain ⟨i, j, hij⟩ : ∃ i j, (qᴴ * V.gram) i j ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hM (Matrix.ext hne)
  have key : ∀ (A : Mx D s V.rank) (c : AE D), Matrix.trace (A * Matrix.single j i c) = A i j * c := by
    intro A c
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply, ite_and, mul_ite, mul_zero]
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
  refine ⟨Matrix.single j i (incA D ((qᴴ * V.gram) i j)⁻¹ * (x • half D)), ?_⟩
  rw [inner_rat_eq]
  change ψ (trA (Matrix.trace (rat (qᴴ * V.gram) *
      Matrix.single j i (incA D ((qᴴ * V.gram) i j)⁻¹ * (x • half D))))) ≠ 1
  rw [key, show rat (qᴴ * V.gram) i j = incA D ((qᴴ * V.gram) i j) from rfl, ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ hij, map_one, one_mul, trA_smul_half]
  exact hx

/- English proof (translation)
Introduce `D ψ hψ V s μs 𝓕s hcov q`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Establish `h0 : ∀ y : Mx D V.rank s, ψ (trA (Matrix.trace (inner V (rat (0 : Matrix (Fin V.rank) (Fin s) D.host.E)) y))) = 1`. Introduce `y`.

Simplify using `[GlobalTheory.StdUnn.inner, rat_zero, adj_zero, trA]`. Repeatedly rewrite using `[h0]`. Rewrite using `[MeasureTheory.setIntegral_const]`. Simplify using `[Measure.real, hcov.2.2]`. Introduce `hq`.

Take `⟨u, hu⟩` from `exists_chi_ne_one hψ V hq`. Use `set φ : Mx D V.rank s → ℂ := fun y => ψ (trA (Matrix.trace (inner V (rat q) y))) with hφ`. Establish `hper : ∀ γ ∈ ratMx D V.rank s, ∀ a, φ (γ + a) = φ a`. Introduce `γ hγ a`. Simplify using `only [hφ]`.

Rewrite using `[chi_add, chi_rat hψ V q hγ, one_mul]`. Establish `h1` using `covolOne_integral_add hcov φ hper u`. Establish `h2 : ∀ a, φ (a + u) = φ u * φ a`. Introduce `a`. Simplify using `only [hφ]`.

Rewrite using `[chi_add, mul_comm]`. Simplify using `only [h2] at h1`. Rewrite `h1` using `[MeasureTheory.integral_const_mul]`. Establish `h3 : (φ u - 1) * ∫ y in 𝓕s, φ y ∂μs = 0` using `by rw [sub_mul, h1, one_mul, sub_self]`. Break down `mul_eq_zero.mp h3 with h | h` into its components or cases.

Conclude with `absurd (sub_eq_zero.mp h) hu`. Conclude with `h`.
-/
theorem orthogonality : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (V : HSp D) (s : ℕ)
    (μs : Measure (Mx D V.rank s)) (𝓕s : Set (Mx D V.rank s)), IsCovolOne (ratMx D V.rank s) μs 𝓕s →
    ∀ q : Matrix (Fin V.rank) (Fin s) D.host.E,
      (q = 0 → ∫ y in 𝓕s, ψ (trA (Matrix.trace (inner V (rat q) y))) ∂μs = 1) ∧
      (q ≠ 0 → ∫ y in 𝓕s, ψ (trA (Matrix.trace (inner V (rat q) y))) ∂μs = 0) := by
  intro D ψ hψ V s μs 𝓕s hcov q
  constructor
  · rintro rfl
    have h0 : ∀ y : Mx D V.rank s, ψ (trA (Matrix.trace (inner V (rat (0 : Matrix (Fin V.rank) (Fin s) D.host.E)) y))) = 1 := by
      intro y
      simp [GlobalTheory.StdUnn.inner, rat_zero, adj_zero, trA]
    simp_rw [h0]
    rw [MeasureTheory.setIntegral_const]
    simp [Measure.real, hcov.2.2]
  · intro hq
    obtain ⟨u, hu⟩ := exists_chi_ne_one hψ V hq
    set φ : Mx D V.rank s → ℂ := fun y => ψ (trA (Matrix.trace (inner V (rat q) y))) with hφ
    have hper : ∀ γ ∈ ratMx D V.rank s, ∀ a, φ (γ + a) = φ a := by
      intro γ hγ a
      simp only [hφ]
      rw [chi_add, chi_rat hψ V q hγ, one_mul]
    have h1 := covolOne_integral_add hcov φ hper u
    have h2 : ∀ a, φ (a + u) = φ u * φ a := by
      intro a
      simp only [hφ]
      rw [chi_add, mul_comm]
    simp only [h2] at h1
    rw [MeasureTheory.integral_const_mul] at h1
    have h3 : (φ u - 1) * ∫ y in 𝓕s, φ y ∂μs = 0 := by rw [sub_mul, h1, one_mul, sub_self]
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd (sub_eq_zero.mp h) hu
    · exact h

end GlobalTheory.CompanionTheory.EisUnfold.Orth

end
