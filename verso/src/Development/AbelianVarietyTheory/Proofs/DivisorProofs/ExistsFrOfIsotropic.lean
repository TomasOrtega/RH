import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis.FrameCompl

variable {E : Type} [Field E]

/- English proof (translation)
Simplify using `only [cT, Matrix.map_mul, Matrix.transpose_mul]`.
-/
theorem cT_mul (τ : E →+* E) {a b c : ℕ} (A : Matrix (Fin a) (Fin b) E) (B : Matrix (Fin b) (Fin c) E) :
    cT τ (A * B) = cT τ B * cT τ A := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

/- English proof (translation)
Use extensionality with `i k`. Simplify using `[cT]`.
-/
theorem cT_add (τ : E →+* E) {a b : ℕ} (A B : Matrix (Fin a) (Fin b) E) :
    cT τ (A + B) = cT τ A + cT τ B := by
  ext i k; simp [cT]

/- English proof (translation)
Use extensionality with `i k`. Simplify using `[cT, hτ]`.
-/
theorem cT_cT (τ : E →+* E) (hτ : ∀ x, τ (τ x) = x) {a b : ℕ} (A : Matrix (Fin a) (Fin b) E) :
    cT τ (cT τ A) = A := by
  ext i k; simp [cT, hτ]

/- English proof (translation)
Apply the tactic sequence `ext i k; simp [cT, Matrix.one_apply]; split_ifs <;> simp_all [eq_comm]`.
-/
theorem cT_one (τ : E →+* E) {a : ℕ} : cT τ (1 : Matrix (Fin a) (Fin a) E) = 1 := by
  ext i k; simp [cT, Matrix.one_apply]; split_ifs <;> simp_all [eq_comm]

/- English proof (translation)
Use extensionality with `i k`. Simplify using `[cT]`.
-/
theorem cT_zero (τ : E →+* E) {a b : ℕ} : cT τ (0 : Matrix (Fin a) (Fin b) E) = 0 := by
  ext i k; simp [cT]

end GlobalTheory.SphEis.FrameCompl

open GlobalTheory.SphEis.FrameCompl in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm n J hJ j C D hcc hdd hcd`. Use `set τ : E →+* E := (σ : E →+* E) with hτdef`. Establish `hτ : ∀ x, τ (τ x) = x` using `fun x => GlobalTheory.SiegelSet.sigma_sigma (σ := σ) hcm x`. Establish `hJJ : cT τ J = J` using `by ext i k; exact hJ.1 i k`. Establish `hdc : cT τ D * J * C = 1`.

Use `congrArg (cT τ) hcd` as an intermediate fact. Rewrite `this` using `[cT_mul, cT_mul, cT_cT τ hτ, hJJ, cT_one, ← Matrix.mul_assoc]`. Then use the resulting hypothesis. Set `W : Submodule E (Fin n → E)` to `LinearMap.ker (Matrix.toLin' (cT τ C * J)) ⊓ LinearMap.ker (Matrix.toLin' (cT τ D * J))`. Set `m` to `Module.finrank E W`. Set `b : Module.Basis (Fin m) E W` to `Module.finBasis E W`.

Set `Z : Matrix (Fin n) (Fin m) E` to `Matrix.of fun r k => (b k : Fin n → E) r`. Establish `hZv : ∀ u : Fin m → E, Z *ᵥ u = ((∑ k, u k • b k : W) : Fin n → E)`. Introduce `u`. Use extensionality with `r`. Simplify using `[Z, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]`.

Establish `hk : ∀ k, Z *ᵥ Pi.single k 1 = (b k : Fin n → E)`. Introduce `k`. Rewrite using `[hZv]`. Simplify using `[Pi.single_apply]`. Establish `hCZ : cT τ C * J * Z = 0`.

Apply `Matrix.ext_of_mulVec_single` to reduce the goal to its premises. Introduce `k`. Rewrite using `[← Matrix.mulVec_mulVec, Matrix.zero_mulVec, hk]`. Conclude with `(b k).2.1`. Establish `hDZ : cT τ D * J * Z = 0`.

Apply `Matrix.ext_of_mulVec_single` to reduce the goal to its premises. Introduce `k`. Rewrite using `[← Matrix.mulVec_mulVec, Matrix.zero_mulVec, hk]`. Conclude with `(b k).2.2`. Establish `hZC : cT τ Z * J * C = 0`.

Use `congrArg (cT τ) hCZ` as an intermediate fact. Rewrite `this` using `[cT_mul, cT_mul, cT_cT τ hτ, hJJ, cT_zero, ← Matrix.mul_assoc]`. Then use the resulting hypothesis. Establish `hZD : cT τ Z * J * D = 0`. Use `congrArg (cT τ) hDZ` as an intermediate fact. Rewrite `this` using `[cT_mul, cT_mul, cT_cT τ hτ, hJJ, cT_zero, ← Matrix.mul_assoc]`. Then use the resulting hypothesis.

Use `set Pr : Matrix (Fin n) (Fin n) E := 1 - C * (cT τ D * J) - D * (cT τ C * J) with hPr`. Establish `hCPr : cT τ C * J * Pr = 0`. Simplify using `only [hPr, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hcc, hcd, Matrix.zero_mul, Matrix.one_mul]`. Normalize the expressions using the abelian group laws. Establish `hDPr : cT τ D * J * Pr = 0`.

Simplify using `only [hPr, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hdc, hdd, Matrix.zero_mul, Matrix.one_mul]`. Normalize the expressions using the abelian group laws. Establish `hmem : ∀ i, Pr *ᵥ Pi.single i 1 ∈ W`. Introduce `i`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Use `show Matrix.toLin' _ _ = 0`. Rewrite using `[Matrix.toLin'_apply, Matrix.mulVec_mulVec, hCPr, Matrix.zero_mulVec]`. Use `show Matrix.toLin' _ _ = 0`. Rewrite using `[Matrix.toLin'_apply, Matrix.mulVec_mulVec, hDPr, Matrix.zero_mulVec]`. Set `M : Matrix (Fin m) (Fin n) E` to `Matrix.of fun k i => b.repr ⟨_, hmem i⟩ k`.

Establish `hZM : Z * M = Pr`. Apply `Matrix.ext_of_mulVec_single` to reduce the goal to its premises. Introduce `i`. Rewrite using `[← Matrix.mulVec_mulVec]`. Establish `: M *ᵥ Pi.single i 1 = fun k => b.repr ⟨_, hmem i⟩ k`.

Use extensionality with `k`. Simplify using `[M, Matrix.mulVec, dotProduct, Pi.single_apply]`. Rewrite using `[this, hZv, b.sum_repr]`. Establish `hdec : C * (cT τ D * J) + D * (cT τ C * J) + Z * M = 1`. Rewrite using `[hZM, hPr]`.

Normalize the expressions using the abelian group laws. Use `set J₀ : Matrix (Fin m) (Fin m) E := cT τ Z * J * Z with hJ₀`. Establish `hJ₀h : cT τ J₀ = J₀`. Rewrite using `[hJ₀, cT_mul, cT_mul, cT_cT τ hτ, hJJ, Matrix.mul_assoc]`. Establish `hCZ' : cT τ C * (J * Z) = 0` using `(Matrix.mul_assoc _ _ _).symm.trans hCZ`.

Establish `hDZ' : cT τ D * (J * Z) = 0` using `(Matrix.mul_assoc _ _ _).symm.trans hDZ`. Establish `key : J * Z = cT τ M * J₀`. Establish `h1 : cT τ (C * (cT τ D * J) + D * (cT τ C * J) + Z * M) = 1` using `by rw [hdec, cT_one]`. Rewrite `h1` using `[cT_add, cT_add, cT_mul, cT_mul, cT_mul, cT_mul, cT_mul, cT_cT τ hτ, cT_cT τ hτ, hJJ]`. Use `conv_lhs => rw [← Matrix.one_mul (J * Z), ← h1]`.

Simplify using `only [Matrix.add_mul, Matrix.mul_assoc, hCZ', hDZ', Matrix.mul_zero, zero_add, hJ₀]`. Establish `hdet : J₀.det ≠ 0`. Introduce `h0`. Take `⟨u, hu0, hu⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr h0`. Establish `hJz : J *ᵥ (Z *ᵥ u) = 0`.

Rewrite using `[Matrix.mulVec_mulVec, key, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_zero]`. Establish `hz` using `Matrix.eq_zero_of_mulVec_eq_zero hJ.2 hJz`. Rewrite `hz` using `[hZv]`. Establish `hs : (∑ k, u k • b k : W) = 0` using `Subtype.ext hz`. Conclude with `hu0 (funext fun k => Fintype.linearIndependent_iff.mp b.linearIndependent u hs k)`.

Establish `hinv : J₀⁻¹ * J₀ = 1` using `Matrix.nonsing_inv_mul J₀ (isUnit_iff_ne_zero.mpr hdet)`. Use `set S : Matrix (Fin n) (Fin n) E := C * (cT τ D * J) + Z * (J₀⁻¹ * (cT τ Z * J)) + D * (cT τ C * J) with hS`. Establish `a1 : cT τ D * (J * C) = 1` using `(Matrix.mul_assoc _ _ _).symm.trans hdc`. Establish `a2 : cT τ Z * (J * C) = 0` using `(Matrix.mul_assoc _ _ _).symm.trans hZC`. Establish `a3 : cT τ C * (J * C) = 0` using `(Matrix.mul_assoc _ _ _).symm.trans hcc`.

Establish `a4 : cT τ D * (J * D) = 0` using `(Matrix.mul_assoc _ _ _).symm.trans hdd`. Establish `a5 : cT τ Z * (J * D) = 0` using `(Matrix.mul_assoc _ _ _).symm.trans hZD`. Establish `a6 : cT τ C * (J * D) = 1` using `(Matrix.mul_assoc _ _ _).symm.trans hcd`. Establish `a7 : cT τ Z * (J * Z) = J₀` using `(Matrix.mul_assoc _ _ _).symm`. Establish `hSC : S * C = C`.

Simplify using `only [hS, Matrix.add_mul, Matrix.mul_assoc, a1, a2, a3, Matrix.mul_zero, Matrix.mul_one, add_zero]`. Establish `hSD : S * D = D`. Simplify using `only [hS, Matrix.add_mul, Matrix.mul_assoc, a4, a5, a6, Matrix.mul_zero, Matrix.mul_one, zero_add]`. Establish `hSZ : S * Z = Z`. Simplify using `only [hS, Matrix.add_mul, Matrix.mul_assoc, hCZ', hDZ', a7, Matrix.mul_zero, add_zero, zero_add]`.

Rewrite using `[hinv, Matrix.mul_one]`. Establish `hS1 : S = 1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_add, Matrix.mul_assoc]`. Use `_ = 1 := by rw [hSC, hSD, hSZ, hdec]`.

Establish `hdim : m + 2 * j = n`. Establish `ht` using `congrArg Matrix.trace hS1`. Rewrite `ht` using `[hS, Matrix.trace_add, Matrix.trace_add, Matrix.trace_mul_comm C, Matrix.trace_mul_comm Z, Matrix.trace_mul_comm D]`. Simplify using `only [Matrix.mul_assoc, a1, a6, a7, hinv, Matrix.trace_one, Fintype.card_fin] at ht`. Establish `: ((m + 2 * j : ℕ) : E) = (n : E)` using `by push_cast; rw [← ht]; ring`.

Conclude with `this` after adjusting the coercions. Use `⟨m, Z, J₀, hcm, hJ, ⟨fun i k => ?_, hdet⟩, hcc, hdd, hcd, hdc, hCZ, hDZ, hZC, hZD, rfl, hS1, hdim⟩` and prove the remaining obligations. Use `congrFun (congrFun hJ₀h i) k` as an intermediate fact. Simplify using `only [cT, Matrix.transpose_apply, Matrix.map_apply] at this`. Conclude with `this`.
-/
theorem GlobalTheory.SphEis.exists_fr_of_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (j : ℕ) (C D : Matrix (Fin n) (Fin j) E), cT (σ : E →+* E) C * J * C = 0 → cT (σ : E →+* E) D * J * D = 0 → cT (σ : E →+* E) C * J * D = 1 → ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ := by
  intro F E _ _ _ _ _ σ hcm n J hJ j C D hcc hdd hcd
  set τ : E →+* E := (σ : E →+* E) with hτdef
  have hτ : ∀ x, τ (τ x) = x := fun x => GlobalTheory.SiegelSet.sigma_sigma (σ := σ) hcm x
  have hJJ : cT τ J = J := by ext i k; exact hJ.1 i k
  have hdc : cT τ D * J * C = 1 := by
    have := congrArg (cT τ) hcd
    rwa [cT_mul, cT_mul, cT_cT τ hτ, hJJ, cT_one, ← Matrix.mul_assoc] at this

  let W : Submodule E (Fin n → E) :=
    LinearMap.ker (Matrix.toLin' (cT τ C * J)) ⊓ LinearMap.ker (Matrix.toLin' (cT τ D * J))
  let m := Module.finrank E W
  let b : Module.Basis (Fin m) E W := Module.finBasis E W
  let Z : Matrix (Fin n) (Fin m) E := Matrix.of fun r k => (b k : Fin n → E) r
  have hZv : ∀ u : Fin m → E, Z *ᵥ u = ((∑ k, u k • b k : W) : Fin n → E) := by
    intro u; ext r
    simp [Z, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hk : ∀ k, Z *ᵥ Pi.single k 1 = (b k : Fin n → E) := by
    intro k; rw [hZv]; simp [Pi.single_apply]
  have hCZ : cT τ C * J * Z = 0 := by
    apply Matrix.ext_of_mulVec_single; intro k
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec, hk]
    exact (b k).2.1
  have hDZ : cT τ D * J * Z = 0 := by
    apply Matrix.ext_of_mulVec_single; intro k
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec, hk]
    exact (b k).2.2
  have hZC : cT τ Z * J * C = 0 := by
    have := congrArg (cT τ) hCZ
    rwa [cT_mul, cT_mul, cT_cT τ hτ, hJJ, cT_zero, ← Matrix.mul_assoc] at this
  have hZD : cT τ Z * J * D = 0 := by
    have := congrArg (cT τ) hDZ
    rwa [cT_mul, cT_mul, cT_cT τ hτ, hJJ, cT_zero, ← Matrix.mul_assoc] at this

  set Pr : Matrix (Fin n) (Fin n) E := 1 - C * (cT τ D * J) - D * (cT τ C * J) with hPr
  have hCPr : cT τ C * J * Pr = 0 := by
    simp only [hPr, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hcc, hcd, Matrix.zero_mul, Matrix.one_mul]
    abel
  have hDPr : cT τ D * J * Pr = 0 := by
    simp only [hPr, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hdc, hdd, Matrix.zero_mul, Matrix.one_mul]
    abel
  have hmem : ∀ i, Pr *ᵥ Pi.single i 1 ∈ W := by
    intro i
    refine ⟨?_, ?_⟩
    · show Matrix.toLin' _ _ = 0
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hCPr, Matrix.zero_mulVec]
    · show Matrix.toLin' _ _ = 0
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hDPr, Matrix.zero_mulVec]
  let M : Matrix (Fin m) (Fin n) E := Matrix.of fun k i => b.repr ⟨_, hmem i⟩ k
  have hZM : Z * M = Pr := by
    apply Matrix.ext_of_mulVec_single; intro i
    rw [← Matrix.mulVec_mulVec]
    have : M *ᵥ Pi.single i 1 = fun k => b.repr ⟨_, hmem i⟩ k := by
      ext k; simp [M, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [this, hZv, b.sum_repr]
  have hdec : C * (cT τ D * J) + D * (cT τ C * J) + Z * M = 1 := by
    rw [hZM, hPr]; abel

  set J₀ : Matrix (Fin m) (Fin m) E := cT τ Z * J * Z with hJ₀
  have hJ₀h : cT τ J₀ = J₀ := by
    rw [hJ₀, cT_mul, cT_mul, cT_cT τ hτ, hJJ, Matrix.mul_assoc]
  have hCZ' : cT τ C * (J * Z) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hCZ
  have hDZ' : cT τ D * (J * Z) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hDZ
  have key : J * Z = cT τ M * J₀ := by
    have h1 : cT τ (C * (cT τ D * J) + D * (cT τ C * J) + Z * M) = 1 := by rw [hdec, cT_one]
    rw [cT_add, cT_add, cT_mul, cT_mul, cT_mul, cT_mul, cT_mul, cT_cT τ hτ, cT_cT τ hτ, hJJ] at h1
    conv_lhs => rw [← Matrix.one_mul (J * Z), ← h1]
    simp only [Matrix.add_mul, Matrix.mul_assoc, hCZ', hDZ', Matrix.mul_zero, zero_add, hJ₀]
  have hdet : J₀.det ≠ 0 := by
    intro h0
    obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hJz : J *ᵥ (Z *ᵥ u) = 0 := by
      rw [Matrix.mulVec_mulVec, key, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_zero]
    have hz := Matrix.eq_zero_of_mulVec_eq_zero hJ.2 hJz
    rw [hZv] at hz
    have hs : (∑ k, u k • b k : W) = 0 := Subtype.ext hz
    exact hu0 (funext fun k => Fintype.linearIndependent_iff.mp b.linearIndependent u hs k)
  have hinv : J₀⁻¹ * J₀ = 1 := Matrix.nonsing_inv_mul J₀ (isUnit_iff_ne_zero.mpr hdet)
  set S : Matrix (Fin n) (Fin n) E := C * (cT τ D * J) + Z * (J₀⁻¹ * (cT τ Z * J)) + D * (cT τ C * J) with hS
  have a1 : cT τ D * (J * C) = 1 := (Matrix.mul_assoc _ _ _).symm.trans hdc
  have a2 : cT τ Z * (J * C) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hZC
  have a3 : cT τ C * (J * C) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hcc
  have a4 : cT τ D * (J * D) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hdd
  have a5 : cT τ Z * (J * D) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hZD
  have a6 : cT τ C * (J * D) = 1 := (Matrix.mul_assoc _ _ _).symm.trans hcd
  have a7 : cT τ Z * (J * Z) = J₀ := (Matrix.mul_assoc _ _ _).symm
  have hSC : S * C = C := by
    simp only [hS, Matrix.add_mul, Matrix.mul_assoc, a1, a2, a3, Matrix.mul_zero, Matrix.mul_one, add_zero]
  have hSD : S * D = D := by
    simp only [hS, Matrix.add_mul, Matrix.mul_assoc, a4, a5, a6, Matrix.mul_zero, Matrix.mul_one, zero_add]
  have hSZ : S * Z = Z := by
    simp only [hS, Matrix.add_mul, Matrix.mul_assoc, hCZ', hDZ', a7, Matrix.mul_zero, add_zero, zero_add]
    rw [hinv, Matrix.mul_one]
  have hS1 : S = 1 := by
    calc S = S * (C * (cT τ D * J) + D * (cT τ C * J) + Z * M) := by rw [hdec, Matrix.mul_one]
      _ = S * C * (cT τ D * J) + S * D * (cT τ C * J) + S * Z * M := by
          simp only [Matrix.mul_add, Matrix.mul_assoc]
      _ = 1 := by rw [hSC, hSD, hSZ, hdec]
  have hdim : m + 2 * j = n := by
    have ht := congrArg Matrix.trace hS1
    rw [hS, Matrix.trace_add, Matrix.trace_add, Matrix.trace_mul_comm C, Matrix.trace_mul_comm Z,
      Matrix.trace_mul_comm D] at ht
    simp only [Matrix.mul_assoc, a1, a6, a7, hinv, Matrix.trace_one, Fintype.card_fin] at ht
    have : ((m + 2 * j : ℕ) : E) = (n : E) := by push_cast; rw [← ht]; ring
    exact_mod_cast this
  refine ⟨m, Z, J₀, hcm, hJ, ⟨fun i k => ?_, hdet⟩, hcc, hdd, hcd, hdc, hCZ, hDZ, hZC, hZD, rfl, hS1, hdim⟩
  have := congrFun (congrFun hJ₀h i) k
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply] at this
  exact this
