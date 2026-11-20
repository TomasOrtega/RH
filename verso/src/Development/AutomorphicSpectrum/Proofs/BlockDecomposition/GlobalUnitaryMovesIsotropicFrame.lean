import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActWOneApply
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicSumNondegenerateFrame
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.WittOne

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

/- English proof (translation)
Simplify using `[hE, hform, mul_add, Finset.sum_add_distrib]`.
-/
theorem hE_add_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y z : Fin M → E) :
    hE σ J x (y + z) = hE σ J x y + hE σ J x z := by
  simp [hE, hform, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[hE, hform, add_mul, Finset.sum_add_distrib]`.
-/
theorem hE_add_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y z : Fin M → E) :
    hE σ J (x + y) z = hE σ J x z + hE σ J y z := by
  simp [hE, hform, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hE, hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hE_smul_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : E)
    (x y : Fin M → E) : hE σ J x (c • y) = c * hE σ J x y := by
  simp only [hE, hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `only [hE, hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hE_smul_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : E)
    (x y : Fin M → E) : hE σ J (c • x) y = σ c * hE σ J x y := by
  simp only [hE, hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul,
    AlgHom.coe_toRingHom, RingHom.coe_coe]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `only [hE, hform, map_sum, map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe, hσ]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hJ i j]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hE_herm (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (y z : Fin M → E) : σ (hE σ J y z) = hE σ J z y := by
  simp only [hE, hform, map_sum, map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ i j]
  ring

/- English proof (translation)
Establish `hherm` using `hE_herm σ hσ K hK.1`. Establish `hex : ∃ y₀, hE σ K x y₀ ≠ 0`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Establish `hv : Matrix.vecMul (fun i => σ (x i)) K = 0`.

Use function extensionality and compare the values at `j`. Use `hall (Pi.single j 1)` as an intermediate fact. Simplify `this` using `[hE, hform, Pi.single_apply, Matrix.vecMul, dotProduct]`. Establish `hz : (fun i => σ (x i)) = 0`. Establish `hu : IsUnit K` using `(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hK.2)`.

Conclude with `(Matrix.vecMul_injective_of_isUnit hu) (by simpa using hv)`. Apply `hx0` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Establish `h` using `congrArg σ (congrFun hz i)`. Simplify `h` using `[hσ]`.

Take `⟨y₀, hy₀⟩` from `hex`. Take `⟨y₁, hxy₁⟩ : ∃ y₁, hE σ K x y₁ = 1` from `⟨(hE σ K x y₀)⁻¹ • y₀, by rw [hE_smul_right]; exact inv_mul_cancel₀ hy₀⟩`. Establish `hy₁x : hE σ K y₁ x = 1` using `by rw [← hherm, hxy₁, map_one]`. Take `⟨q, hq⟩ : ∃ q, q = hE σ K y₁ y₁` from `⟨_, rfl⟩`. Establish `hqs : σ q = q` using `by rw [hq]; exact hherm _ _`.

Take `⟨y, hy⟩ : ∃ y : Fin N → E, y = y₁ + (-(q / 2)) • x` from `⟨_, rfl⟩`. Establish `hxy : hE σ K x y = 1`. Rewrite using `[hy, hE_add_right, hE_smul_right, hxy₁, hxx]`. Simplify using the standard rewrite rules. Establish `hyy : hE σ K y y = 0`.

Establish `hs2 : σ (-(q / 2)) = -(q / 2)`. Rewrite using `[map_neg, map_div₀, hqs, map_ofNat]`. Rewrite using `[hy, hE_add_right, hE_add_left, hE_add_left, hE_smul_right, hE_smul_right, hE_smul_left, hE_smul_left, hs2, hy₁x, hxy₁, hxx, ← hq]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Conclude with `⟨y, hxy, hyy⟩`.
-/
theorem exists_partner [CharZero E] (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {N : ℕ}
    (K : Matrix (Fin N) (Fin N) E) (hK : IsHermND σ K) (x : Fin N → E) (hx0 : x ≠ 0)
    (hxx : hE σ K x x = 0) : ∃ y, hE σ K x y = 1 ∧ hE σ K y y = 0 := by
  have hherm := hE_herm σ hσ K hK.1
  have hex : ∃ y₀, hE σ K x y₀ ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hv : Matrix.vecMul (fun i => σ (x i)) K = 0 := by
      funext j
      have := hall (Pi.single j 1)
      simpa [hE, hform, Pi.single_apply, Matrix.vecMul, dotProduct] using this
    have hz : (fun i => σ (x i)) = 0 := by
      have hu : IsUnit K := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hK.2)
      exact (Matrix.vecMul_injective_of_isUnit hu) (by simpa using hv)
    apply hx0
    funext i
    have h := congrArg σ (congrFun hz i)
    simpa [hσ] using h
  obtain ⟨y₀, hy₀⟩ := hex
  obtain ⟨y₁, hxy₁⟩ : ∃ y₁, hE σ K x y₁ = 1 :=
    ⟨(hE σ K x y₀)⁻¹ • y₀, by rw [hE_smul_right]; exact inv_mul_cancel₀ hy₀⟩
  have hy₁x : hE σ K y₁ x = 1 := by rw [← hherm, hxy₁, map_one]
  obtain ⟨q, hq⟩ : ∃ q, q = hE σ K y₁ y₁ := ⟨_, rfl⟩
  have hqs : σ q = q := by rw [hq]; exact hherm _ _
  obtain ⟨y, hy⟩ : ∃ y : Fin N → E, y = y₁ + (-(q / 2)) • x := ⟨_, rfl⟩
  have hxy : hE σ K x y = 1 := by
    rw [hy, hE_add_right, hE_smul_right, hxy₁, hxx]; simp
  have hyy : hE σ K y y = 0 := by
    have hs2 : σ (-(q / 2)) = -(q / 2) := by
      rw [map_neg, map_div₀, hqs, map_ofNat]
    rw [hy, hE_add_right, hE_add_left, hE_add_left, hE_smul_right, hE_smul_right, hE_smul_left,
      hE_smul_left, hs2, hy₁x, hxy₁, hxx, ← hq]
    field_simp
    ring
  exact ⟨y, hxy, hyy⟩

/- English proof (translation)
Use extensionality with `a b`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp [gramE, h1, h2, h3, h4]`.
-/
theorem gramE_pair (σ : E →ₐ[F] E) {N : ℕ} (K : Matrix (Fin N) (Fin N) E) (u v : Fin N → E)
    (h1 : hE σ K u u = 0) (h2 : hE σ K u v = 1) (h3 : hE σ K v u = 1) (h4 : hE σ K v v = 0) :
    gramE σ K ![u, v] = !![0, 1; 1, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [gramE, h1, h2, h3, h4]

/- English proof (translation)
Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_⟩ <;>`. Simplify using `[hE, hform, Fin.sum_univ_succ, hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one]`.
-/
theorem hE_hypOne_basis (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    hE σ (hypOne J) (Fin.cons 1 fun _ => 0) (Fin.cons 1 fun _ => 0) = 0 ∧
    hE σ (hypOne J) (Fin.cons 1 fun _ => 0) (Fin.cons 0 (Fin.cons 1 fun _ => 0)) = 1 ∧
    hE σ (hypOne J) (Fin.cons 0 (Fin.cons 1 fun _ => 0)) (Fin.cons 1 fun _ => 0) = 1 ∧
    hE σ (hypOne J) (Fin.cons 0 (Fin.cons 1 fun _ => 0)) (Fin.cons 0 (Fin.cons 1 fun _ => 0)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [hE, hform, Fin.sum_univ_succ, hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one]

end Alg

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ q hq`. Take `⟨hσ, -⟩` from `GlobalTheory.CompanionTheory.SW.HaarCoord.conj_facts hCM`. Establish `hK` using `isHermND_hypOne σ hJ`. Take `⟨hli, hg⟩` from `hq`. Establish `hx0 : q 0 ≠ 0` using `hli.ne_zero 0`.

Establish `hxx : hE σ (hypOne J) (q 0) (q 0) = 0` using `congrFun (congrFun hg 0) 0`. Take `⟨y, hxy, hyy⟩` from `exists_partner σ hσ (hypOne J) hK (q 0) hx0 hxx`. Establish `hyx : hE σ (hypOne J) y (q 0) = 1`. Rewrite using `[← hE_herm σ hσ _ hK.1, hxy, map_one]`. Take `⟨b1, b2, b3, b4⟩` from `hE_hypOne_basis σ J`.

Establish `hX` using `gramE_pair σ (hypOne J) (q 0) y hxx hxy hyx hyy`. Establish `hY` using `gramE_pair σ (hypOne J) _ _ b1 b2 b3 b4`. Take `⟨g, hgU, hgX⟩` from `GlobalTheory.T.witt_extension_global F E σ hCM (M + 2) (hypOne J) hK 2 _ _ (hX.trans hY.symm) (by rw [hX]; simp [Matrix.det_fin_two_of])`. Use `⟨⟨g, hgU⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a`.

Take `rfl : a = 0` from `Subsingleton.elim _ _`. Conclude with `hgX 0`.
-/
theorem exists_unitary_e0 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ q : Fin 1 → Fin (M + 2) → E, q ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) → ∃ g : UJ (σ : E →+* E) (hypOne J), gact σ g q = e0 E M := by
  intro F E _ _ _ _ _ σ hCM M J hJ q hq
  obtain ⟨hσ, -⟩ := GlobalTheory.CompanionTheory.SW.HaarCoord.conj_facts hCM
  have hK := isHermND_hypOne σ hJ
  obtain ⟨hli, hg⟩ := hq
  have hx0 : q 0 ≠ 0 := hli.ne_zero 0
  have hxx : hE σ (hypOne J) (q 0) (q 0) = 0 := congrFun (congrFun hg 0) 0
  obtain ⟨y, hxy, hyy⟩ := exists_partner σ hσ (hypOne J) hK (q 0) hx0 hxx
  have hyx : hE σ (hypOne J) y (q 0) = 1 := by
    rw [← hE_herm σ hσ _ hK.1, hxy, map_one]
  obtain ⟨b1, b2, b3, b4⟩ := hE_hypOne_basis σ J
  have hX := gramE_pair σ (hypOne J) (q 0) y hxx hxy hyx hyy
  have hY := gramE_pair σ (hypOne J) _ _ b1 b2 b3 b4
  obtain ⟨g, hgU, hgX⟩ := GlobalTheory.T.witt_extension_global F E σ hCM (M + 2) (hypOne J) hK 2 _ _ (hX.trans hY.symm)
    (by rw [hX]; simp [Matrix.det_fin_two_of])
  refine ⟨⟨g, hgU⟩, ?_⟩
  funext a
  obtain rfl : a = 0 := Subsingleton.elim _ _
  exact hgX 0

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.WittOne
