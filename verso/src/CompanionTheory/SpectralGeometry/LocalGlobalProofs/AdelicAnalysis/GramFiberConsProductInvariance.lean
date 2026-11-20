import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StageData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorInvolutionAlgebraProperties

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.BsetUnit

/- English proof (translation)
Apply the tactic sequence `let e : Unit ⊕ Fin n ≃ Fin (n + 1) := { toFun := Sum.elim (fun _ => 0) Fin.succ invFun := fun i => Fin.cases (Sum.inl ()) Sum.inr i left_inv := by rintro (_ | j) <;> simp right_inv := by intro i; refine Fin.cases ?_ ?_ i <;> simp }`. Establish `h1 : S.det = (S.submatrix e e).det` using `(Matrix.det_submatrix_equiv_self e S).symm`. Set `A : Matrix Unit Unit K` to `fun _ _ => S 0 0`. Set `B : Matrix Unit (Fin n) K` to `fun _ j => S 0 j.succ`. Set `C : Matrix (Fin n) Unit K` to `fun i _ => S i.succ 0`.

Set `D : Matrix (Fin n) (Fin n) K` to `fun i j => S i.succ j.succ`. Set `Wm : Matrix Unit Unit K` to `fun _ _ => w`. Establish `h2 : S.submatrix e e = Matrix.fromBlocks A B C D`. Apply the tactic sequence `ext (_ | i) (_ | j) <;> rfl`. Use `letI : Invertible A := ⟨Wm, by ext i j; rw [Matrix.mul_apply]; simp [A, Wm]; rw [mul_comm]; exact hw, by ext i j; rw [Matrix.mul_apply]; simp [A, Wm, hw]⟩`.

Establish `hA : A.det = S 0 0` using `by rw [Matrix.det_unique]`. Establish `hD : D - C * ⅟A * B = Matrix.of fun i j : Fin n => S i.succ j.succ - S i.succ 0 * w * S 0 j.succ`. Establish `hinv : ⅟A = Wm` using `rfl`. Use extensionality with `i j`. Rewrite using `[hinv, Matrix.sub_apply, Matrix.mul_apply]`.

Simplify using `only [Finset.univ_unique, Finset.sum_singleton, Matrix.mul_apply, Matrix.of_apply]`. Simplify using `[C, B, D, Wm]`. Rewrite using `[h1, h2, Matrix.det_fromBlocks₁₁, hA, hD]`.
-/
theorem det_eq_corner_mul {K : Type} [CommRing K] {n : ℕ} (S : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (w : K) (hw : S 0 0 * w = 1) :
    S.det = S 0 0 *
      (Matrix.of fun i j : Fin n => S i.succ j.succ - S i.succ 0 * w * S 0 j.succ).det := by
  let e : Unit ⊕ Fin n ≃ Fin (n + 1) :=
    { toFun := Sum.elim (fun _ => 0) Fin.succ
      invFun := fun i => Fin.cases (Sum.inl ()) Sum.inr i
      left_inv := by rintro (_ | j) <;> simp
      right_inv := by intro i; refine Fin.cases ?_ ?_ i <;> simp }
  have h1 : S.det = (S.submatrix e e).det := (Matrix.det_submatrix_equiv_self e S).symm
  let A : Matrix Unit Unit K := fun _ _ => S 0 0
  let B : Matrix Unit (Fin n) K := fun _ j => S 0 j.succ
  let C : Matrix (Fin n) Unit K := fun i _ => S i.succ 0
  let D : Matrix (Fin n) (Fin n) K := fun i j => S i.succ j.succ
  let Wm : Matrix Unit Unit K := fun _ _ => w
  have h2 : S.submatrix e e = Matrix.fromBlocks A B C D := by
    ext (_ | i) (_ | j) <;> rfl
  letI : Invertible A :=
    ⟨Wm, by ext i j; rw [Matrix.mul_apply]; simp [A, Wm]; rw [mul_comm]; exact hw,
      by ext i j; rw [Matrix.mul_apply]; simp [A, Wm, hw]⟩
  have hA : A.det = S 0 0 := by rw [Matrix.det_unique]
  have hD : D - C * ⅟A * B =
      Matrix.of fun i j : Fin n => S i.succ j.succ - S i.succ 0 * w * S 0 j.succ := by
    have hinv : ⅟A = Wm := rfl
    ext i j
    rw [hinv, Matrix.sub_apply, Matrix.mul_apply]
    simp only [Finset.univ_unique, Finset.sum_singleton, Matrix.mul_apply, Matrix.of_apply]
    simp [C, B, D, Wm]
  rw [h1, h2, Matrix.det_fromBlocks₁₁, hA, hD]

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]

/- English proof (translation)
Establish `h : (r ⊗ₜ[F] (1 : E) : R ⊗[F] E) = algebraMap R (R ⊗[F] E) r`. Simplify using `[Algebra.TensorProduct.algebraMap_apply]`. Rewrite using `[h, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R b)]`. Establish `h2 : algebraMap F R (1 / 2) * 2 = 1`. Rewrite using `[← map_ofNat (algebraMap F R) 2, ← map_mul, one_div, inv_mul_cancel₀ h2F, map_one]`.

Simplify using `only [Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]`. Rewrite using `[← mul_assoc, h2, one_mul]`.
-/
theorem half_trace_tmul (h2F : (2 : F) ≠ 0) (b : Module.Basis (Fin 2) F E) (r : R) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] (1 : E)) = r := by
  have h : (r ⊗ₜ[F] (1 : E) : R ⊗[F] E) = algebraMap R (R ⊗[F] E) r := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [h, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R b)]
  have h2 : algebraMap F R (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap F R) 2, ← map_mul, one_div, inv_mul_cancel₀ h2F, map_one]
  simp only [Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  rw [← mul_assoc, h2, one_mul]

/- English proof (translation)
Establish `hi : inclR R (algebraMap F E t) = (1 : R) ⊗ₜ[F] (algebraMap F E t)` using `rfl`. Establish `hE : algebraMap F E t⁻¹ * algebraMap F E t = 1`. Rewrite using `[← map_mul, inv_mul_cancel₀ ht, map_one]`. Establish `hu : (u : R) * ((u⁻¹ : Rˣ) : R) = 1` using `u.mul_inv`. Rewrite using `[hi, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, hE, mul_one, one_mul, one_mul]`.

Establish `e1 : (u : R) ^ 2 * algebraMap F R t * (((u⁻¹ : Rˣ) : R) * ((u⁻¹ : Rˣ) : R)) = algebraMap F R t`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e1, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def t, ← map_mul, mul_inv_cancel₀ ht, map_one]`. Both sides reduce to the same expression.
-/
theorem corner_mul_inv {t : F} (ht : t ≠ 0) (u : Rˣ) :
    (((u : R) ^ 2 * algebraMap F R t) ⊗ₜ[F] (1 : E)) *
      ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * inclR R (algebraMap F E t) *
        (((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹))) = 1 := by
  have hi : inclR R (algebraMap F E t) = (1 : R) ⊗ₜ[F] (algebraMap F E t) := rfl
  have hE : algebraMap F E t⁻¹ * algebraMap F E t = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ht, map_one]
  have hu : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := u.mul_inv
  rw [hi, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, hE, mul_one, one_mul, one_mul]
  have e1 : (u : R) ^ 2 * algebraMap F R t * (((u⁻¹ : Rˣ) : R) * ((u⁻¹ : Rˣ) : R)) =
      algebraMap F R t := by
    calc _ = ((u : R) * ((u⁻¹ : Rˣ) : R)) ^ 2 * algebraMap F R t := by ring
      _ = _ := by rw [hu]; ring
  rw [e1, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def t,
    ← map_mul, mul_inv_cancel₀ ht, map_one]
  rfl

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D S hS`. Take `⟨-, -, -, -, hArt, hRed, -, -⟩` from `D.hR`. Take `⟨-, -, -, -, -, hfix, -⟩` from `KAlg.algebra_tensor_invol F E σ D.hCM R`. Establish `hfr : Module.finrank F E = 2` using `D.hCM.2.2.1`. Establish `: Module.Finite F E` using `Module.finite_of_finrank_pos (by omega)`.

Set `b₂ : Module.Basis (Fin 2) F E` to `Module.finBasisOfFinrankEq F E hfr`. Establish `hsig : ∀ (p : R) (e : E), sigR R σ (p ⊗ₜ[F] e) = p ⊗ₜ[F] σ e` using `fun _ _ => rfl`. Use `set T : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E) := S.1 with hT`. Establish `hH : ∀ i j, sigR R σ (T j i) = T i j` using `S.2`. Take `⟨x, hx⟩` from `hfix (T 0 0) (hH 0 0)`.

Establish `hs0 : s0 R T = x`. Rewrite using `[s0, hx]`. Conclude with `half_trace_tmul two_ne_zero b₂ x`. Establish `hxB : x ∈ B₀`. Establish `h : s0 R T ∈ B₀` using `hS.1`.

Rewrite `h` using `[hs0]`. Then use the resulting hypothesis. Use `set u : Rˣ := a x with hu`. Use `set p : R ⊗[F] E := ((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹) with hp`. Use `set τ : R ⊗[F] E := inclR R (algebraMap F E t) with hτ`. Establish `hsp : sigR R σ p = p` using `by rw [hp, hsig, AlgHom.commutes]`.

Establish `hsτ : sigR R σ τ = τ` using `by show sigR R σ ((1 : R) ⊗ₜ[F] (algebraMap F E t)) = (1 : R) ⊗ₜ[F] (algebraMap F E t)`. Rewrite using `[hsig, AlgHom.commutes]`. Establish `hw : T 0 0 * (p * τ * p) = 1`. Rewrite using `[hx]`. Use `corner_mul_inv (E := E) (R := R) D.ht u` as an intermediate fact.

Establish `hq : x = (u : R) ^ 2 * algebraMap F R t` using `D.hsq x hxB`. Rewrite `this` using `[← hq]`. Then use the resulting hypothesis. Establish `hschur : ∀ i j, schurM R σ t a T i j = T i.succ j.succ - T i.succ 0 * (p * τ * p) * T 0 j.succ`. Introduce `i j`. Establish `hc : ∀ k, cvec R t a T k = p * T 0 k.succ`.

Introduce `k`. Rewrite using `[cvec, hs0]`. Simplify using `only [schurM]`. Rewrite using `[hc, hc, map_mul, hsp, hH]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hmem : schurM R σ t a T ∈ HermR R σ n`. Introduce `i j`. Rewrite using `[hschur, hschur, map_sub, map_mul, map_mul, map_mul, map_mul, hsp, hsτ, hH, hH, hH]`. Expand and normalize the polynomial expressions, which then agree. Establish `hdet` using `det_eq_corner_mul T _ hw`.

Establish `hU : IsUnit (T 0 0)` using `IsUnit.of_mul_eq_one _ hw`. Establish `hsch : (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = Matrix.of fun i j : Fin n => T i.succ j.succ - T i.succ 0 * (p * τ * p) * T 0 j.succ`. Rewrite using `[schur_coe R σ t a S hmem]`. Use extensionality with `i j`. Conclude with `hschur i j`.

Establish `h2` using `hS.2`. Rewrite `h2` using `[hsch]`. Rewrite using `[hdet]`. Conclude with `hU.mul h2`.
-/
theorem isUnit_det_of_mem_Bset : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ S ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))), IsUnit (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)).det := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D S hS
  obtain ⟨-, -, -, -, hArt, hRed, -, -⟩ := D.hR
  obtain ⟨-, -, -, -, -, hfix, -⟩ := KAlg.algebra_tensor_invol F E σ D.hCM R
  have hfr : Module.finrank F E = 2 := D.hCM.2.2.1
  have : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  let b₂ : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hfr
  have hsig : ∀ (p : R) (e : E), sigR R σ (p ⊗ₜ[F] e) = p ⊗ₜ[F] σ e := fun _ _ => rfl
  set T : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E) := S.1 with hT
  have hH : ∀ i j, sigR R σ (T j i) = T i j := S.2
  obtain ⟨x, hx⟩ := hfix (T 0 0) (hH 0 0)
  have hs0 : s0 R T = x := by
    rw [s0, hx]; exact half_trace_tmul two_ne_zero b₂ x
  have hxB : x ∈ B₀ := by
    have h : s0 R T ∈ B₀ := hS.1
    rwa [hs0] at h
  set u : Rˣ := a x with hu
  set p : R ⊗[F] E := ((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹) with hp
  set τ : R ⊗[F] E := inclR R (algebraMap F E t) with hτ
  have hsp : sigR R σ p = p := by rw [hp, hsig, AlgHom.commutes]
  have hsτ : sigR R σ τ = τ := by
    show sigR R σ ((1 : R) ⊗ₜ[F] (algebraMap F E t)) = (1 : R) ⊗ₜ[F] (algebraMap F E t)
    rw [hsig, AlgHom.commutes]
  have hw : T 0 0 * (p * τ * p) = 1 := by
    rw [hx]
    have := corner_mul_inv (E := E) (R := R) D.ht u
    have hq : x = (u : R) ^ 2 * algebraMap F R t := D.hsq x hxB
    rwa [← hq] at this
  have hschur : ∀ i j, schurM R σ t a T i j = T i.succ j.succ - T i.succ 0 * (p * τ * p) * T 0 j.succ := by
    intro i j
    have hc : ∀ k, cvec R t a T k = p * T 0 k.succ := by
      intro k; rw [cvec, hs0]
    simp only [schurM]
    rw [hc, hc, map_mul, hsp, hH]
    ring
  have hmem : schurM R σ t a T ∈ HermR R σ n := by
    intro i j
    rw [hschur, hschur, map_sub, map_mul, map_mul, map_mul, map_mul, hsp, hsτ, hH, hH, hH]
    ring
  have hdet := det_eq_corner_mul T _ hw
  have hU : IsUnit (T 0 0) := IsUnit.of_mul_eq_one _ hw
  have hsch : (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      Matrix.of fun i j : Fin n => T i.succ j.succ - T i.succ 0 * (p * τ * p) * T 0 j.succ := by
    rw [schur_coe R σ t a S hmem]
    ext i j
    exact hschur i j
  have h2 := hS.2
  rw [hsch] at h2
  rw [hdet]
  exact hU.mul h2

end GlobalTheory.CompanionTheory.SW.PiLocalization₂.BsetUnit
