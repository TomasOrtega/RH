import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastNeZeroG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelLabelExtendsOfOrthogonalToExtended
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LetterConjugation
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqHalf

section Lattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

def latMat {n : ℕ} (b : Module.Basis (Fin n) ℤ Dw.La) : 𝓞 E →+* Matrix (Fin n) (Fin n) ℤ :=
  (LinearMap.toMatrixAlgEquiv b).toRingHom.comp (Module.toModuleEnd ℤ (S := 𝓞 E) Dw.La)

/- English proof (translation)
Simplify using `[latMat, LinearMap.toMatrixAlgEquiv_apply]`.
-/
theorem latMat_apply {n : ℕ} (b : Module.Basis (Fin n) ℤ Dw.La) (a : 𝓞 E) (i j : Fin n) :
    latMat Dw b a i j = b.repr (a • b j) i := by
  simp [latMat, LinearMap.toMatrixAlgEquiv_apply]

def gram {n : ℕ} (b : Module.Basis (Fin n) ℤ Dw.La) : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun m m' => Dw.EF (b m) (b m')

def chiAct {n : ℕ} (b : Module.Basis (Fin n) ℤ Dw.La) : 𝓞 E →+* Matrix (Fin n) (Fin n) ℤ where
  toFun a := (latMat Dw b (H.bar a)).transpose
  map_one' := by simp
  map_mul' a a' := by
    show (latMat Dw b (H.bar (a * a'))).transpose = (latMat Dw b (H.bar a)).transpose * (latMat Dw b (H.bar a')).transpose
    rw [← Matrix.transpose_mul, ← map_mul (latMat Dw b), ← map_mul H.bar, mul_comm a' a]
  map_zero' := by simp
  map_add' a a' := by simp [Matrix.transpose_add]

def dualForm {n : ℕ} (b : Module.Basis (Fin n) ℤ Dw.La) : Matrix (Fin n) (Fin n) ℤ := (gram Dw b)⁻¹.transpose

end Lattice

section Setup

variable {D : D7} (O : Setup D)

def cmSet : Set (D.host.E →+* D.what₂.LL) :=
  {σ | ((O.κ.e (σ (O.A.H.rt : D.host.E)) : O.κ.c.F) : ℂ) = O.A.H.rt0}

def letterEmb (l : ℕ) : D.host.E →+* D.what₂.LL :=
  match (letters O.S.Dw)[l]? with
  | some x => O.κ.e.symm.toRingHom.comp (x.1.codRestrict O.κ.c.F.toSubfield (O.κ.c.conj x.1))
  | none => D.embE

end Setup

end GlobalTheory.EqHalf

namespace GlobalTheory.EqHalf

section LatticeThm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

/- English proof (translation)
Set `e : Dw.La ≃ₗ[ℤ] Module.Dual ℤ Dw.La` to `LinearEquiv.ofBijective Dw.EF Dw.unimod`. Establish `h` using `LinearEquiv.isUnit_det e b b.dualBasis`. Establish `hm : LinearMap.toMatrix b b.dualBasis (e : Dw.La →ₗ[ℤ] Module.Dual ℤ Dw.La) = (gram Dw b).transpose`. Use extensionality with `i j`. Simplify using `[LinearMap.toMatrix_apply, gram, e]`.

Rewrite `h` using `[hm, Matrix.det_transpose]`. Conclude with `h`.
-/
theorem isUnit_det_gram {n : ℕ} (b : Module.Basis (Fin n) ℤ Dw.La) : IsUnit (gram Dw b).det := by
  let e : Dw.La ≃ₗ[ℤ] Module.Dual ℤ Dw.La := LinearEquiv.ofBijective Dw.EF Dw.unimod
  have h := LinearEquiv.isUnit_det e b b.dualBasis
  have hm : LinearMap.toMatrix b b.dualBasis (e : Dw.La →ₗ[ℤ] Module.Dual ℤ Dw.La) = (gram Dw b).transpose := by
    ext i j
    simp [LinearMap.toMatrix_apply, gram, e]
  rw [hm, Matrix.det_transpose] at h
  exact h

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, latMat_apply, gram, Matrix.of_apply]`. Establish `h1 : Dw.EF (a • b i) (b j) = ∑ m, b.repr (a • b i) m * Dw.EF (b m) (b j)` using `by conv_lhs => rw [← b.sum_repr (a • b i)]`. Simplify using `only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, smul_eq_mul]`. Establish `h2 : Dw.EF (b i) (H.bar a • b j) = ∑ m, Dw.EF (b i) (b m) * b.repr (H.bar a • b j) m` using `by conv_lhs => rw [← b.sum_repr (H.bar a • b j)]`.

Simplify using `only [map_sum, map_zsmul, smul_eq_mul, mul_comm]`. Rewrite using `[← h1, ← h2, Dw.adj]`.
-/
theorem latMat_transpose_mul_gram {n : ℕ} (b : Module.Basis (Fin n) ℤ Dw.La) (a : 𝓞 E) :
    (latMat Dw b a).transpose * gram Dw b = gram Dw b * latMat Dw b (H.bar a) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, latMat_apply, gram, Matrix.of_apply]
  have h1 : Dw.EF (a • b i) (b j) = ∑ m, b.repr (a • b i) m * Dw.EF (b m) (b j) := by
    conv_lhs => rw [← b.sum_repr (a • b i)]
    simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, smul_eq_mul]
  have h2 : Dw.EF (b i) (H.bar a • b j) = ∑ m, Dw.EF (b i) (b m) * b.repr (H.bar a • b j) m := by
    conv_lhs => rw [← b.sum_repr (H.bar a • b j)]
    simp only [map_sum, map_zsmul, smul_eq_mul, mul_comm]
  rw [← h1, ← h2, Dw.adj]

/- English proof (translation)
Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[H.bar_eq, H.bar_eq]`. Conclude with `IsCMField.complexConj_apply_apply E (a : E)`.
-/
theorem bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq]
  exact IsCMField.complexConj_apply_apply E (a : E)

/- English proof (translation)
Establish `hG` using `isUnit_det_gram Dw b`. Establish `key` using `latMat_transpose_mul_gram Dw b (H.bar a)`. Rewrite `key` using `[bar_bar]`. Establish `k2 : (gram Dw b)⁻¹ * (latMat Dw b (H.bar a)).transpose = latMat Dw b a * (gram Dw b)⁻¹`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.mul_one]`. Use `_ = latMat Dw b a * (gram Dw b)⁻¹ := by`. Rewrite using `[key, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hG, Matrix.one_mul]`. Use `show (latMat Dw b (H.bar a)).transpose.transpose * (gram Dw b)⁻¹.transpose = (gram Dw b)⁻¹.transpose * (latMat Dw b (H.bar (H.bar a))).transpose`. Rewrite using `[bar_bar, Matrix.transpose_transpose, ← Matrix.transpose_mul, ← k2, Matrix.transpose_mul, Matrix.transpose_transpose]`.
-/
theorem chiAct_adj {n : ℕ} (b : Module.Basis (Fin n) ℤ Dw.La) (a : 𝓞 E) :
    (chiAct Dw b a).transpose * dualForm Dw b = dualForm Dw b * chiAct Dw b (H.bar a) := by
  have hG := isUnit_det_gram Dw b
  have key := latMat_transpose_mul_gram Dw b (H.bar a)
  rw [bar_bar] at key

  have k2 : (gram Dw b)⁻¹ * (latMat Dw b (H.bar a)).transpose = latMat Dw b a * (gram Dw b)⁻¹ := by
    calc (gram Dw b)⁻¹ * (latMat Dw b (H.bar a)).transpose
        = (gram Dw b)⁻¹ * ((latMat Dw b (H.bar a)).transpose * gram Dw b) * (gram Dw b)⁻¹ := by
          simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.mul_one]
      _ = latMat Dw b a * (gram Dw b)⁻¹ := by
          rw [key, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hG, Matrix.one_mul]
  show (latMat Dw b (H.bar a)).transpose.transpose * (gram Dw b)⁻¹.transpose =
    (gram Dw b)⁻¹.transpose * (latMat Dw b (H.bar (H.bar a))).transpose
  rw [bar_bar, Matrix.transpose_transpose, ← Matrix.transpose_mul, ← k2, Matrix.transpose_mul,
    Matrix.transpose_transpose]

/- English proof (translation)
Rewrite using `[dualForm, Matrix.det_transpose]`. Conclude with `Matrix.isUnit_nonsing_inv_det _ (isUnit_det_gram Dw b)`.
-/
theorem isUnit_det_dualForm {n : ℕ} (b : Module.Basis (Fin n) ℤ Dw.La) : IsUnit (dualForm Dw b).det := by
  rw [dualForm, Matrix.det_transpose]
  exact Matrix.isUnit_nonsing_inv_det _ (isUnit_det_gram Dw b)

end LatticeThm

section SetupThm

variable {D : D7} (O : Setup D)

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `GlobalTheory.Coisotropic.lattice_rank D.host.E O.A.H O.S.Dw`. Establish `hf` using `GlobalTheory.Proof.LetterConjugation.finrank_host D`. Establish `hN` using `O.S.rank_eq`. Use `⟨Module.finBasisOfFinrankEq ℤ _ ?_⟩` and prove the remaining obligations. Rewrite using `[h3, hf, Nat.mul_div_cancel_left _ two_pos, hN]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem nonempty_basis : Nonempty (Module.Basis (Fin (D.R.f * O.N + D.R.f * O.N)) ℤ O.S.Dw.La) := by
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.Coisotropic.lattice_rank D.host.E O.A.H O.S.Dw
  have hf := GlobalTheory.Proof.LetterConjugation.finrank_host D
  have hN := O.S.rank_eq
  refine ⟨Module.finBasisOfFinrankEq ℤ _ ?_⟩
  rw [h3, hf, Nat.mul_div_cancel_left _ two_pos, hN]
  ring

/- English proof (translation)
Establish `h1 : (O.A.H.bar O.A.H.rt) ^ 2 = O.A.H.rt ^ 2` using `by rw [← map_pow, O.A.H.rt_sq]; simp`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h` into its components or cases. It suffices to derive a contradiction. Take `⟨φ⟩ : Nonempty (D.host.E →+* ℂ)` from `inferInstance`. Establish `h2 : IsCMField.complexConj D.host.E (O.A.H.rt : D.host.E) = (O.A.H.rt : D.host.E)` using `by rw [← O.A.H.bar_eq, h]`.

Establish `h3` using `IsCMField.complexEmbedding_complexConj D.host.E φ (O.A.H.rt : D.host.E)`. Rewrite `h3` using `[h2]`. Establish `h4 : (φ (O.A.H.rt : D.host.E)) ^ 2 = -(O.A.H.d : ℂ)`. Use `congrArg (fun x : 𝓞 D.host.E => φ (x : D.host.E)) O.A.H.rt_sq` as an intermediate fact. Simplify using `using this`.

Establish `h5 : (φ (O.A.H.rt : D.host.E)).im = 0` using `Complex.conj_eq_iff_im.1 h3.symm`. Establish `h6` using `congrArg Complex.re h4`. Simplify using `[sq, h5] at h6`. Establish `h7 : (0 : ℝ) < O.A.H.d` using `by exact_mod_cast O.A.H.d_prime.pos`. Use polynomial arithmetic with `[mul_self_nonneg (φ (O.A.H.rt : D.host.E)).re]`.

Conclude with `h`.
-/
theorem bar_rt : O.A.H.bar O.A.H.rt = -O.A.H.rt := by
  have h1 : (O.A.H.bar O.A.H.rt) ^ 2 = O.A.H.rt ^ 2 := by rw [← map_pow, O.A.H.rt_sq]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exfalso
    obtain ⟨φ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    have h2 : IsCMField.complexConj D.host.E (O.A.H.rt : D.host.E) = (O.A.H.rt : D.host.E) := by rw [← O.A.H.bar_eq, h]
    have h3 := IsCMField.complexEmbedding_complexConj D.host.E φ (O.A.H.rt : D.host.E)
    rw [h2] at h3
    have h4 : (φ (O.A.H.rt : D.host.E)) ^ 2 = -(O.A.H.d : ℂ) := by
      have := congrArg (fun x : 𝓞 D.host.E => φ (x : D.host.E)) O.A.H.rt_sq
      simpa using this
    have h5 : (φ (O.A.H.rt : D.host.E)).im = 0 := Complex.conj_eq_iff_im.1 h3.symm
    have h6 := congrArg Complex.re h4
    simp [sq, h5] at h6
    have h7 : (0 : ℝ) < O.A.H.d := by exact_mod_cast O.A.H.d_prime.pos
    nlinarith [mul_self_nonneg (φ (O.A.H.rt : D.host.E)).re]
  · exact h

/- English proof (translation)
Simplify using `only [cmSet, Set.mem_setOf_eq, O.κ.e_emb]`. Establish `hrt : τ (O.A.H.rt : D.host.E) = -σ (O.A.H.rt : D.host.E)`. Rewrite using `[h, bar_rt O]`. Simplify using the standard rewrite rules. Rewrite using `[hrt, map_neg]`.

Establish `hz : (D.what₂.embLL (σ (O.A.H.rt : D.host.E))) ^ 2 = O.A.H.rt0 ^ 2`. Rewrite using `[O.A.H.sqrt_neg_disc_sq]`. Use `congrArg (fun x : 𝓞 D.host.E => D.what₂.embLL (σ (x : D.host.E))) O.A.H.rt_sq` as an intermediate fact. Simplify using `using this`. Establish `h0 : O.A.H.rt0 ≠ 0`.

Introduce `h0`. Establish `h5` using `O.A.H.sqrt_neg_disc_sq`. Establish `h6` using `O.A.H.d_prime.ne_zero`. Rewrite `h5` using `[h0]`. Simplify using `at h5`.

Conclude with `h6 (by exact_mod_cast h5)`. Prove the components needed by the constructor for the conclusion. Introduce `h1 h2`. Apply `h0` to reduce the goal to its premises. Take the linear combination `(-(1 : ℂ) / 2) * h1 + (-(1 : ℂ) / 2) * h2`.

Introduce `h1`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 hz with h2 | h2` into its components or cases. Conclude with `h2`. Conclude with `absurd (by rw [h2, neg_neg]) h1`.
-/
theorem mem_cmSet_iff (σ τ : D.host.E →+* D.what₂.LL)
    (h : ∀ α : 𝓞 D.host.E, τ (α : D.host.E) = σ ((O.A.H.bar α : 𝓞 D.host.E) : D.host.E)) :
    σ ∈ cmSet O ↔ τ ∉ cmSet O := by
  simp only [cmSet, Set.mem_setOf_eq, O.κ.e_emb]
  have hrt : τ (O.A.H.rt : D.host.E) = -σ (O.A.H.rt : D.host.E) := by
    rw [h, bar_rt O]
    simp
  rw [hrt, map_neg]
  have hz : (D.what₂.embLL (σ (O.A.H.rt : D.host.E))) ^ 2 = O.A.H.rt0 ^ 2 := by
    rw [O.A.H.sqrt_neg_disc_sq]
    have := congrArg (fun x : 𝓞 D.host.E => D.what₂.embLL (σ (x : D.host.E))) O.A.H.rt_sq
    simpa using this
  have h0 : O.A.H.rt0 ≠ 0 := by
    intro h0
    have h5 := O.A.H.sqrt_neg_disc_sq
    have h6 := O.A.H.d_prime.ne_zero
    rw [h0] at h5
    simp at h5
    exact h6 (by exact_mod_cast h5)
  constructor
  · intro h1 h2
    apply h0
    linear_combination (-(1 : ℂ) / 2) * h1 + (-(1 : ℂ) / 2) * h2
  · intro h1
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hz with h2 | h2
    · exact h2
    · exact absurd (by rw [h2, neg_neg]) h1

end SetupThm

end GlobalTheory.EqHalf
