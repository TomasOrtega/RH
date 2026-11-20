import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor.PolyBd

section Gen

variable {P : Type} {A : P → ℝ}

def PB (A : P → ℝ) (f : P → ℂ) : Prop := ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ p, ‖f p‖ ≤ C * A p ^ k

/- English proof (translation)
Assemble the required witnesses or components as `⟨‖a‖, 0, norm_nonneg _, fun _ => by simp⟩`.
-/
theorem PB.const (a : ℂ) : PB A fun _ => a := ⟨‖a‖, 0, norm_nonneg _, fun _ => by simp⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, 1, zero_le_one, fun p => by simpa using h p⟩`.
-/
theorem PB.of_le {f : P → ℂ} (h : ∀ p, ‖f p‖ ≤ A p) : PB A f := ⟨1, 1, zero_le_one, fun p => by simpa using h p⟩

/- English proof (translation)
Take `⟨C, k, hC, h⟩` from `hf`. Take `⟨D, n, hD, h'⟩` from `hg`. Use `⟨C * D, k + n, mul_nonneg hC hD, fun p => ?_⟩` and prove the remaining obligations. Rewrite using `[norm_mul, pow_add]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem PB.mul {f g : P → ℂ} (hf : PB A f) (hg : PB A g) : PB A fun p => f p * g p := by
  obtain ⟨C, k, hC, h⟩ := hf
  obtain ⟨D, n, hD, h'⟩ := hg
  refine ⟨C * D, k + n, mul_nonneg hC hD, fun p => ?_⟩
  rw [norm_mul, pow_add]
  calc _ ≤ (C * A p ^ k) * (D * A p ^ n) :=
        mul_le_mul (h p) (h' p) (norm_nonneg _) ((norm_nonneg _).trans (h p))
    _ = _ := by ring

/- English proof (translation)
Take `⟨C, k, hC, h⟩` from `hf`. Take `⟨D, n, hD, h'⟩` from `hg`. Use `⟨max C D, max k n, le_max_of_le_left hC, fun p => ⟨(h p).trans ?_, (h' p).trans ?_⟩⟩` and prove the remaining obligations. Conclude with `mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ (hA p) (le_max_left _ _)) (pow_nonneg (zero_le_one.trans (hA p)) _) (le_max_of_le_left hC)`. Conclude with `mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ (hA p) (le_max_right _ _)) (pow_nonneg (zero_le_one.trans (hA p)) _) (le_max_of_le_left hC)`.
-/
theorem PB.both (hA : ∀ p, 1 ≤ A p) {f g : P → ℂ} (hf : PB A f) (hg : PB A g) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ p, ‖f p‖ ≤ C * A p ^ k ∧ ‖g p‖ ≤ C * A p ^ k := by
  obtain ⟨C, k, hC, h⟩ := hf
  obtain ⟨D, n, hD, h'⟩ := hg
  refine ⟨max C D, max k n, le_max_of_le_left hC, fun p => ⟨(h p).trans ?_, (h' p).trans ?_⟩⟩
  · exact mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ (hA p) (le_max_left _ _))
      (pow_nonneg (zero_le_one.trans (hA p)) _) (le_max_of_le_left hC)
  · exact mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ (hA p) (le_max_right _ _))
      (pow_nonneg (zero_le_one.trans (hA p)) _) (le_max_of_le_left hC)

/- English proof (translation)
Take `⟨C, k, hC, h⟩` from `hf.both hA hg`. Use `⟨2 * C, k, by positivity, fun p => (norm_add_le _ _).trans ?_⟩` and prove the remaining obligations. Combine the linear relations using `[(h p).1, (h p).2]`.
-/
theorem PB.add (hA : ∀ p, 1 ≤ A p) {f g : P → ℂ} (hf : PB A f) (hg : PB A g) : PB A fun p => f p + g p := by
  obtain ⟨C, k, hC, h⟩ := hf.both hA hg
  refine ⟨2 * C, k, by positivity, fun p => (norm_add_le _ _).trans ?_⟩
  linarith [(h p).1, (h p).2]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using PB.const (A := A) 0`. Consider the case `insert a s ha ih => simpa [Finset.sum_insert ha] using (hf a).add hA ih`.
-/
theorem PB.sum (hA : ∀ p, 1 ≤ A p) {I : Type} (s : Finset I) {f : I → P → ℂ} (hf : ∀ i, PB A (f i)) :
    PB A fun p => ∑ i ∈ s, f i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PB.const (A := A) 0
  | insert a s ha ih => simpa [Finset.sum_insert ha] using (hf a).add hA ih

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using PB.const (A := A) 1`. Consider the case `insert a s ha ih => simpa [Finset.prod_insert ha] using (hf a).mul ih`.
-/
theorem PB.prod {I : Type} (s : Finset I) {f : I → P → ℂ} (hf : ∀ i, PB A (f i)) :
    PB A fun p => ∏ i ∈ s, f i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PB.const (A := A) 1
  | insert a s ha ih => simpa [Finset.prod_insert ha] using (hf a).mul ih

/- English proof (translation)
Simplify using `only [Matrix.det_apply']`. Conclude with `PB.sum hA _ fun s => (PB.const _).mul (PB.prod _ fun i => hM _ _)`.
-/
theorem PB.det (hA : ∀ p, 1 ≤ A p) {I : Type} [Fintype I] [DecidableEq I] {M : P → Matrix I I ℂ}
    (hM : ∀ i j, PB A fun p => M p i j) : PB A fun p => (M p).det := by
  simp only [Matrix.det_apply']
  exact PB.sum hA _ fun s => (PB.const _).mul (PB.prod _ fun i => hM _ _)

/- English proof (translation)
Simplify using `only [Matrix.mul_apply]`. Conclude with `PB.sum hA _ fun k => (hM _ _).mul (hN _ _)`.
-/
theorem PB.matMul (hA : ∀ p, 1 ≤ A p) {a b d : Type} [Fintype b] {M : P → Matrix a b ℂ} {N : P → Matrix b d ℂ}
    (hM : ∀ i j, PB A fun p => M p i j) (hN : ∀ i j, PB A fun p => N p i j) (i : a) (j : d) :
    PB A fun p => (M p * N p) i j := by
  simp only [Matrix.mul_apply]
  exact PB.sum hA _ fun k => (hM _ _).mul (hN _ _)

/- English proof (translation)
Establish `h1 : PB A fun p => horVal (K p) (C p)`. Simplify using `only [fun p => horVal_eq (h p) (hR p) (hS p)]`. Use `PB.det hA fun i j => ?_` and prove the remaining obligations. Break down `i with i | i` into its components or cases. Simplify using `using bR i j`.

Simplify using `using bC i j`. Establish `h2 : PB A fun p => (horVal (K p) (C p))⁻¹`. Simplify using `only [fun p => inv_eq_of_mul_eq_one_right (horVal_mul (h p) (hR p) (hS p))]`. Use `PB.det hA fun i j => ?_` and prove the remaining obligations. Break down `j with j | j` into its components or cases.

Simplify using `using bK i j`. Simplify using `using bS i j`. Conclude with `h1.both hA h2`.
-/
theorem horVal_bound (hA : ∀ p, 1 ≤ A p) {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {K : P → Matrix (m ⊕ n) m ℂ} {C : P → Matrix n (m ⊕ n) ℂ} {R : P → Matrix m (m ⊕ n) ℂ}
    {S : P → Matrix (m ⊕ n) n ℂ} (h : ∀ p, C p * K p = 0) (hR : ∀ p, R p * K p = 1) (hS : ∀ p, C p * S p = 1)
    (bK : ∀ i j, PB A fun p => K p i j) (bC : ∀ i j, PB A fun p => C p i j) (bR : ∀ i j, PB A fun p => R p i j)
    (bS : ∀ i j, PB A fun p => S p i j) :
    ∃ (D : ℝ) (k : ℕ), 0 ≤ D ∧ ∀ p, ‖horVal (K p) (C p)‖ ≤ D * A p ^ k ∧ ‖(horVal (K p) (C p))⁻¹‖ ≤ D * A p ^ k := by
  have h1 : PB A fun p => horVal (K p) (C p) := by
    simp only [fun p => horVal_eq (h p) (hR p) (hS p)]
    refine PB.det hA fun i j => ?_
    rcases i with i | i
    · simpa using bR i j
    · simpa using bC i j
  have h2 : PB A fun p => (horVal (K p) (C p))⁻¹ := by
    simp only [fun p => inv_eq_of_mul_eq_one_right (horVal_mul (h p) (hR p) (hS p))]
    refine PB.det hA fun i j => ?_
    rcases j with j | j
    · simpa using bK i j
    · simpa using bS i j
  exact h1.both hA h2

end Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Di : Datum H}

/- English proof (translation)
Take `⟨n, hn, hv⟩` from `hv`. Take `⟨a, ha⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 hv`. Use `⟨fun t k => (n : ℂ)⁻¹ * f t (a k : E), fun Q hQ z => ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (fun w => Q w z) ha`. Simplify using `only [map_sum, Finset.sum_apply, hQ, map_nsmul, Pi.smul_apply, nsmul_eq_mul] at h`.

Establish `hn' : (n : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hn`. Simplify using `only [_root_.mul_assoc]`. Rewrite using `[← Finset.mul_sum, h, inv_mul_cancel_left₀ hn']`.
-/
theorem exists_comb {J : Type} [Fintype J] (x : J → Di.La) (f : (E →+* ℂ) → (E →+* ℂ)) (v : Di.La)
    (hv : ∃ n : ℕ, n ≠ 0 ∧ n • v ∈ Submodule.span (𝓞 E) (Set.range x)) :
    ∃ B : (E →+* ℂ) → J → ℂ, ∀ Q : Di.La →+ (Letter Dw → ℂ),
      (∀ (a : 𝓞 E) v (z : Letter Dw), Q (a • v) z = f z.1 (a : E) * Q v z) →
      ∀ z : Letter Dw, Q v z = ∑ k, B z.1 k * Q (x k) z := by
  obtain ⟨n, hn, hv⟩ := hv
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hv
  refine ⟨fun t k => (n : ℂ)⁻¹ * f t (a k : E), fun Q hQ z => ?_⟩
  have h := congrArg (fun w => Q w z) ha
  simp only [map_sum, Finset.sum_apply, hQ, map_nsmul, Pi.smul_apply, nsmul_eq_mul] at h
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  simp only [_root_.mul_assoc]
  rw [← Finset.mul_sum, h, inv_mul_cancel_left₀ hn']

/- English proof (translation)
Set `P : Type` to `{p : (Di.La →+ (Letter Dw → ℂ)) × Matrix (Letter Dw) (Fin g) ℂ × Matrix (Fin g) (Letter Dw) ℂ × (Fin r → Fin g → ℂ) × ℝ // GoodPer c σ τ x hm p.1 ∧ p.2.1 * p.2.2.1 = 1 ∧ (∀ v, ∑ z, p.1 v z • p.2.1 z = ∑ m, T₀ v m • p.2.2.2.1 m) ∧ (∀ j, ∑ m, ρ j m • p.2.2.2.1 m = Pi.single j 1) ∧ …`. Set `A : P → ℝ` to `fun p => p.1.2.2.2.2`. Establish `hA : ∀ p, 1 ≤ A p` using `fun p => p.2.2.2.2.2.1`. Use `choose B hB using fun m : Fin r => exists_comb (Dw := Dw) x (Formalism.L2.PjFree.relab c σ) (T₀.symm (Pi.single m 1)) (hx.2.1 _)`. Establish `hQ : ∀ (p : P) v z, p.1.1 v z = ∑ j, (∑ m, (T₀ v m : ℂ) * p.1.2.2.2.1 m j) * p.1.2.2.1 j z`.

Introduce and unpack `⟨⟨Q, W, Wi, lam, a⟩, -, h1, h2, -⟩ v z`. Simplify using `only at h1 h2 ⊢`. Establish `h3 : ∀ j, ∑ m, (T₀ v m : ℂ) * lam m j = (Q v ᵥ* W) j` using `fun j => by`. Use `congrFun (h2 v) j` as an intermediate fact. Simplify using `only [Finset.sum_apply, Pi.smul_apply] at this`.

Simplify using `only [smul_eq_mul, zsmul_eq_mul] at this`. Rewrite using `[← this]`. Both sides reduce to the same expression. Simplify using `only [h3]`. Establish `: Q v = (Q v ᵥ* W) ᵥ* Wi` using `by rw [Matrix.vecMul_vecMul, h1, Matrix.vecMul_one]`.

Conclude with `congrFun this z`. Establish `bQ : ∀ v z, PB A fun p => p.1.1 v z` using `fun v z => by`. Simplify using `only [hQ]`. Conclude with `PB.sum hA _ fun j => (PB.sum hA _ fun m => (PB.const _).mul (PB.of_le fun p => p.2.2.2.2.2.2.2.2 m j)).mul (PB.of_le fun p => p.2.2.2.2.2.2.2.1 j z)`. Set `S : ∀ t : E →+* ℂ, P → Matrix (Idx Dw τ) (Fin (Dw.mult t)) ℂ` to `fun t p => Matrix.of fun k i => ∑ j, p.1.2.1 ⟨t, i⟩ j * ∑ m, ρ j m * B m t k`.

Establish `bS : ∀ t k i, PB A fun p => S t p k i` using `fun t k i => by`. Simplify using `only [S, Matrix.of_apply]`. Conclude with `PB.sum hA _ fun j => (PB.of_le fun p => p.2.2.2.2.2.2.1 _ j).mul (PB.const _)`. Establish `hS : ∀ t (p : P), perMat x p.1.1 t * S t p = 1`. Introduce `t p`.

Establish `h4 : ∀ j z, ∑ m, ρ j m * p.1.1 (T₀.symm (Pi.single m 1)) z = p.1.2.2.1 j z`. Introduce `j z`. Establish `h5 : ∀ j', ∑ m, ρ j m * p.1.2.2.2.1 m j' = (Pi.single j (1 : ℂ) : Fin g → ℂ) j'` using `fun j' => by`. Simplify `congrFun (p.2.2.2.2.1 j) j'` using `[Finset.sum_apply]`. Simplify using `only [hQ, AddEquiv.apply_symm_apply, Pi.single_apply, Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, _root_.one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Simplify using `only [← _root_.mul_assoc, ← Finset.sum_mul, h5, Pi.single_apply, ite_mul, _root_.one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Use extensionality with `i i'`. Establish `h6` using `congrFun (congrFun p.2.2.1 ⟨t, i'⟩) ⟨t, i⟩`. Establish `h7 : (1 : Matrix (Letter Dw) (Letter Dw) ℂ) ⟨t, i'⟩ ⟨t, i⟩ = (1 : Matrix (Fin (Dw.mult t)) (Fin (Dw.mult t)) ℂ) i i'`.

Simplify using `[Matrix.one_apply, eq_comm]`. Rewrite using `[← h7, ← h6]`. Simplify using `only [Matrix.mul_apply, ← h4, hB _ _ p.2.1.1, perMat, S, Matrix.of_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hdet : IsUnit ((hm.map (Formalism.L2.PjFree.relab c σ τ))ᵀ).det`. Rewrite using `[Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`.

Conclude with `((map_ne_zero _).2 hx.2.2.2).isUnit`. Take `⟨D, k, -, h⟩` from `horVal_bound hA (K := fun p => kerMat c σ τ x hm p.1.1) (C := fun p => perMat x p.1.1 τ) (R := fun p => (S (conjEmb τ) p)ᵀ * (hm.map (Formalism.L2.PjFree.relab c σ τ))ᵀ) (S := S τ) (fun p => p.2.1.2.1) (fun p => by`. Rewrite using `[kerMat, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hdet, ← Matrix.transpose_mul, hS, Matrix.transpose_one])`. Use the proof step `(hS τ) (PB.matMul hA (fun _ _ => PB.const _) fun i j => bQ _ _) (fun i j => bQ _ _)`. Use the proof step `(PB.matMul hA (fun i j => bS _ _ _) fun _ _ => PB.const _) (bS τ)`.

Conclude with `⟨D, k, fun Q W Wi lam a h1 h2 _ h3 h4 h5 h6 h7 h8 => h ⟨⟨Q, W, Wi, lam, a⟩, h1, h2, h3, h4, h5, h6, h7, h8⟩⟩`.
-/
theorem perVal_bound (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (Di : Datum H) (τ : E →+* ℂ) (x : Idx Dw τ → Di.La)
    (hm : Matrix (Idx Dw τ) (Idx Dw τ) E) (g r : ℕ) (T₀ : Di.La ≃+ (Fin r → ℤ)) (ρ : Fin g → Fin r → ℂ)
    (hx : IsPerBasis Di x hm) : ∃ (C : ℝ) (k : ℕ), ∀ (Q : Di.La →+ (Letter Dw → ℂ))
      (W : Matrix (Letter Dw) (Fin g) ℂ) (Wi : Matrix (Fin g) (Letter Dw) ℂ) (lam : Fin r → Fin g → ℂ) (A : ℝ),
      GoodPer c σ τ x hm Q → W * Wi = 1 → Wi * W = 1 → (∀ v, ∑ z, Q v z • W z = ∑ m, T₀ v m • lam m) →
      (∀ j, ∑ m, ρ j m • lam m = Pi.single j 1) → 1 ≤ A → (∀ z j, ‖W z j‖ ≤ A) → (∀ j z, ‖Wi j z‖ ≤ A) →
      (∀ m j, ‖lam m j‖ ≤ A) → ‖perVal c σ τ x hm Q‖ ≤ C * A ^ k ∧ ‖(perVal c σ τ x hm Q)⁻¹‖ ≤ C * A ^ k := by
  let P : Type := {p : (Di.La →+ (Letter Dw → ℂ)) × Matrix (Letter Dw) (Fin g) ℂ × Matrix (Fin g) (Letter Dw) ℂ ×
      (Fin r → Fin g → ℂ) × ℝ // GoodPer c σ τ x hm p.1 ∧ p.2.1 * p.2.2.1 = 1 ∧
      (∀ v, ∑ z, p.1 v z • p.2.1 z = ∑ m, T₀ v m • p.2.2.2.1 m) ∧
      (∀ j, ∑ m, ρ j m • p.2.2.2.1 m = Pi.single j 1) ∧ 1 ≤ p.2.2.2.2 ∧ (∀ z j, ‖p.2.1 z j‖ ≤ p.2.2.2.2) ∧
      (∀ j z, ‖p.2.2.1 j z‖ ≤ p.2.2.2.2) ∧ (∀ m j, ‖p.2.2.2.1 m j‖ ≤ p.2.2.2.2)}
  let A : P → ℝ := fun p => p.1.2.2.2.2
  have hA : ∀ p, 1 ≤ A p := fun p => p.2.2.2.2.2.1
  choose B hB using fun m : Fin r =>
    exists_comb (Dw := Dw) x (Formalism.L2.PjFree.relab c σ) (T₀.symm (Pi.single m 1)) (hx.2.1 _)
  have hQ : ∀ (p : P) v z, p.1.1 v z = ∑ j, (∑ m, (T₀ v m : ℂ) * p.1.2.2.2.1 m j) * p.1.2.2.1 j z := by
    rintro ⟨⟨Q, W, Wi, lam, a⟩, -, h1, h2, -⟩ v z
    dsimp only at h1 h2 ⊢
    have h3 : ∀ j, ∑ m, (T₀ v m : ℂ) * lam m j = (Q v ᵥ* W) j := fun j => by
      have := congrFun (h2 v) j
      simp only [Finset.sum_apply, Pi.smul_apply] at this
      simp only [smul_eq_mul, zsmul_eq_mul] at this
      rw [← this]; rfl
    simp only [h3]
    have : Q v = (Q v ᵥ* W) ᵥ* Wi := by rw [Matrix.vecMul_vecMul, h1, Matrix.vecMul_one]
    exact congrFun this z
  have bQ : ∀ v z, PB A fun p => p.1.1 v z := fun v z => by
    simp only [hQ]
    exact PB.sum hA _ fun j => (PB.sum hA _ fun m => (PB.const _).mul (PB.of_le fun p => p.2.2.2.2.2.2.2.2 m j)).mul
      (PB.of_le fun p => p.2.2.2.2.2.2.2.1 j z)
  let S : ∀ t : E →+* ℂ, P → Matrix (Idx Dw τ) (Fin (Dw.mult t)) ℂ := fun t p =>
    Matrix.of fun k i => ∑ j, p.1.2.1 ⟨t, i⟩ j * ∑ m, ρ j m * B m t k
  have bS : ∀ t k i, PB A fun p => S t p k i := fun t k i => by
    simp only [S, Matrix.of_apply]
    exact PB.sum hA _ fun j => (PB.of_le fun p => p.2.2.2.2.2.2.1 _ j).mul (PB.const _)
  have hS : ∀ t (p : P), perMat x p.1.1 t * S t p = 1 := by
    intro t p
    have h4 : ∀ j z, ∑ m, ρ j m * p.1.1 (T₀.symm (Pi.single m 1)) z = p.1.2.2.1 j z := by
      intro j z
      have h5 : ∀ j', ∑ m, ρ j m * p.1.2.2.2.1 m j' = (Pi.single j (1 : ℂ) : Fin g → ℂ) j' := fun j' => by
        simpa [Finset.sum_apply] using congrFun (p.2.2.2.2.1 j) j'
      simp only [hQ, AddEquiv.apply_symm_apply, Pi.single_apply, Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul,
        _root_.one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [← _root_.mul_assoc, ← Finset.sum_mul, h5, Pi.single_apply, ite_mul,
        _root_.one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ext i i'
    have h6 := congrFun (congrFun p.2.2.1 ⟨t, i'⟩) ⟨t, i⟩
    have h7 : (1 : Matrix (Letter Dw) (Letter Dw) ℂ) ⟨t, i'⟩ ⟨t, i⟩ =
        (1 : Matrix (Fin (Dw.mult t)) (Fin (Dw.mult t)) ℂ) i i' := by
      simp [Matrix.one_apply, eq_comm]
    rw [← h7, ← h6]
    simp only [Matrix.mul_apply, ← h4, hB _ _ p.2.1.1, perMat, S, Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have hdet : IsUnit ((hm.map (Formalism.L2.PjFree.relab c σ τ))ᵀ).det := by
    rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ((map_ne_zero _).2 hx.2.2.2).isUnit
  obtain ⟨D, k, -, h⟩ := horVal_bound hA (K := fun p => kerMat c σ τ x hm p.1.1) (C := fun p => perMat x p.1.1 τ)
    (R := fun p => (S (conjEmb τ) p)ᵀ * (hm.map (Formalism.L2.PjFree.relab c σ τ))ᵀ) (S := S τ)
    (fun p => p.2.1.2.1)
    (fun p => by
      rw [kerMat, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hdet, ← Matrix.transpose_mul, hS,
        Matrix.transpose_one])
    (hS τ) (PB.matMul hA (fun _ _ => PB.const _) fun i j => bQ _ _) (fun i j => bQ _ _)
    (PB.matMul hA (fun i j => bS _ _ _) fun _ _ => PB.const _) (bS τ)
  exact ⟨D, k, fun Q W Wi lam a h1 h2 _ h3 h4 h5 h6 h7 h8 =>
    h ⟨⟨Q, W, Wi, lam, a⟩, h1, h2, h3, h4, h5, h6, h7, h8⟩⟩

end GlobalTheory.ShFam.Hor.PolyBd
