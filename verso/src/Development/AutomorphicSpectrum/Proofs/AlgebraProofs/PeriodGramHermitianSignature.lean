import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodHermitianTypeCompatibility
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.SignTau

open GlobalTheory.CompanionTheory.Ar.Flat.RiemannTau

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `h1 : ∑ a, f (e a) = ∑ i : {i // ty i = σ}, f i` using `Equiv.sum_comp e (fun i : {i // ty i = σ} => f i)`. Rewrite using `[h1, ← Finset.sum_subtype (p := fun j => ty j = σ) (Finset.univ.filter fun j => ty j = σ) (by simp) f, Finset.sum_filter]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Both sides reduce to the same expression.

Conclude with `hf j h`.
-/
theorem sum_type {g n : ℕ} (ty : Fin g → (E →+* ℂ)) (σ : E →+* ℂ) (e : Fin n ≃ {i // ty i = σ}) (f : Fin g → ℂ)
    (hf : ∀ j, ty j ≠ σ → f j = 0) : ∑ j, f j = ∑ a, f (e a) := by
  classical
  have h1 : ∑ a, f (e a) = ∑ i : {i // ty i = σ}, f i := Equiv.sum_comp e (fun i : {i // ty i = σ} => f i)
  rw [h1, ← Finset.sum_subtype (p := fun j => ty j = σ) (Finset.univ.filter fun j => ty j = σ) (by simp) f,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rfl
  · exact hf j h

/- English proof (translation)
Rewrite using `[hermForm_eq_sum]`. Establish `h1 : ∀ j, ty j ≠ σ → ∑ k, tyPart ty σ z j * M j k * star (tyPart ty σ w k) = 0`. Introduce `j hj`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `k _`.

Simplify using `[tyPart, hj]`. Rewrite using `[sum_type ty σ e _ h1]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Establish `h2 : ∀ k, ty k ≠ σ → tyPart ty σ z (e a) * M (e a) k * star (tyPart ty σ w k) = 0`. Introduce `k hk`.

Simplify using `[tyPart, hk]`. Rewrite using `[sum_type ty σ e _ h2]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `[tyPart, (e a).2, (e b).2]`.
-/
theorem hermForm_tyPart {g n : ℕ} (ty : Fin g → (E →+* ℂ)) (σ : E →+* ℂ) (e : Fin n ≃ {i // ty i = σ})
    (M : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm M (tyPart ty σ z) (tyPart ty σ w) =
      ∑ a, ∑ b, z (e a) * M (e a) (e b) * star (w (e b)) := by
  classical
  rw [hermForm_eq_sum]
  have h1 : ∀ j, ty j ≠ σ → ∑ k, tyPart ty σ z j * M j k * star (tyPart ty σ w k) = 0 := by
    intro j hj
    apply Finset.sum_eq_zero
    intro k _
    simp [tyPart, hj]
  rw [sum_type ty σ e _ h1]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h2 : ∀ k, ty k ≠ σ → tyPart ty σ z (e a) * M (e a) k * star (tyPart ty σ w k) = 0 := by
    intro k hk
    simp [tyPart, hk]
  rw [sum_type ty σ e _ h2]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [tyPart, (e a).2, (e b).2]

/- English proof (translation)
Rewrite using `[hermForm_eq_sum, hermForm_eq_sum]`. Simplify using `only [star_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[star_mul', star_mul', star_star, hM.apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem star_hermForm {g : ℕ} {M : Matrix (Fin g) (Fin g) ℂ} (hM : M.IsHermitian) (z w : Fin g → ℂ) :
    star (hermForm M z w) = hermForm M w z := by
  rw [hermForm_eq_sum, hermForm_eq_sum]
  simp only [star_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [star_mul', star_mul', star_star, hM.apply]
  ring

/- English proof (translation)
Use `⟨hM, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hx' : star (⇑x) ≠ 0`. Introduce `h0`. Apply `hx` to reduce the goal to its premises. Use extensionality with `i`.

Simplify using `using congrFun h0 i`. Establish `h1` using `hpos (star ⇑x) hx'`. Establish `h2 : (starRingEnd ℂ) (hermForm M (star ⇑x) (star ⇑x)) = hermForm M (star ⇑x) (star ⇑x)` using `star_hermForm hM _ _`. Establish `h3 : (x.sum fun i xi => x.sum fun j xj => star xi * M i j * xj) = ∑ i, ∑ j, star (x i) * M i j * x j`. Rewrite using `[Finsupp.sum_fintype x (fun i xi => x.sum fun j xj => star xi * M i j * xj) (fun i => by simp [Finsupp.sum])]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Conclude with `Finsupp.sum_fintype x (fun j xj => star (x i) * M i j * xj) (fun j => by simp)`. Establish `h4 : ∑ i, ∑ j, star (x i) * M i j * x j = hermForm M (star ⇑x) (star ⇑x)`. Rewrite using `[hermForm_eq_sum]`. Simplify using the standard rewrite rules.

Rewrite using `[h3, h4, Complex.lt_def]`. Conclude with `⟨by simpa using h1, by simp [Complex.conj_eq_iff_im.mp h2]⟩`.
-/
theorem posDef_of_hermForm {g : ℕ} {M : Matrix (Fin g) (Fin g) ℂ} (hM : M.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm M z z).re) : M.PosDef := by
  refine ⟨hM, fun x hx => ?_⟩
  have hx' : star (⇑x) ≠ 0 := by
    intro h0
    apply hx
    ext i
    simpa using congrFun h0 i
  have h1 := hpos (star ⇑x) hx'
  have h2 : (starRingEnd ℂ) (hermForm M (star ⇑x) (star ⇑x)) = hermForm M (star ⇑x) (star ⇑x) :=
    star_hermForm hM _ _
  have h3 : (x.sum fun i xi => x.sum fun j xj => star xi * M i j * xj) =
      ∑ i, ∑ j, star (x i) * M i j * x j := by
    rw [Finsupp.sum_fintype x (fun i xi => x.sum fun j xj => star xi * M i j * xj)
      (fun i => by simp [Finsupp.sum])]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finsupp.sum_fintype x (fun j xj => star (x i) * M i j * xj) (fun j => by simp)
  have h4 : ∑ i, ∑ j, star (x i) * M i j * x j = hermForm M (star ⇑x) (star ⇑x) := by
    rw [hermForm_eq_sum]
    simp
  rw [h3, h4, Complex.lt_def]
  exact ⟨by simpa using h1, by simp [Complex.conj_eq_iff_im.mp h2]⟩

/- English proof (translation)
Rewrite using `[Matrix.fromCols_mul_fromBlocks, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromCols_mul_fromRows]`. Simplify using `[sub_eq_add_neg]`.
-/
theorem fromCols_block {I : Type} [Fintype I] {p q : ℕ} (A : Matrix I (Fin p) ℂ) (B : Matrix I (Fin q) ℂ)
    (G₁ : Matrix (Fin p) (Fin p) ℂ) (G₂ : Matrix (Fin q) (Fin q) ℂ) :
    Matrix.fromCols A B * Matrix.fromBlocks G₁ 0 0 (-G₂) * (Matrix.fromCols A B)ᴴ =
      A * G₁ * Aᴴ - B * G₂ * Bᴴ := by
  rw [Matrix.fromCols_mul_fromBlocks, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromCols_mul_fromRows]
  simp [sub_eq_add_neg]

/- English proof (translation)
Rewrite using `[← key]`. Simplify using `only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, two_smul, Matrix.mul_assoc]`.
-/
private theorem add_mul_mul_conjTranspose_add_eq_of_two_smul {r p q : ℕ} (C : Matrix (Fin r) (Fin p ⊕ Fin q) ℂ)
    (V M N : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (key : V * ((2 : ℂ) • M) * Vᴴ = N) :
    (C * V + C * V) * M * (C * V + C * V)ᴴ = C * N * Cᴴ + C * N * Cᴴ := by
  rw [← key]
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_smul, Matrix.smul_mul, two_smul, Matrix.mul_assoc]

/- English proof (translation)
Establish `hN : (Matrix.fromBlocks G₁ 0 0 (-G₂))ᴴ = Matrix.fromBlocks G₁ 0 0 (-G₂)`. Rewrite using `[Matrix.fromBlocks_conjTranspose, h₁.1.eq, Matrix.conjTranspose_neg, h₂.1.eq, Matrix.conjTranspose_zero, Matrix.conjTranspose_zero]`. Establish `hMh : M.IsHermitian`. Establish `h2 : ((2 : ℂ) • M)ᴴ = (2 : ℂ) • M`. Rewrite using `[hM, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hN, Matrix.mul_assoc]`.

Rewrite `h2` using `[Matrix.conjTranspose_smul]`. Establish `h3 : (2 : ℂ) • Mᴴ = (2 : ℂ) • M` using `by simpa using h2`. Conclude with `smul_right_injective _ two_ne_zero h3`. Establish `hW : IsUnit W.det`. Rewrite using `[isUnit_iff_ne_zero]`.

Introduce `h0`. Establish `h4` using `congrArg Matrix.det hM`. Rewrite `h4` using `[Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, h0]`. Simplify using `[hdet] at h4`. Establish `hVW : W⁻¹ * W = 1` using `Matrix.nonsing_inv_mul W hW`.

Establish `hWV : Wᴴ * (W⁻¹)ᴴ = 1`. Rewrite using `[← Matrix.conjTranspose_mul, hVW, Matrix.conjTranspose_one]`. Establish `key : W⁻¹ * ((2 : ℂ) • M) * (W⁻¹)ᴴ = Matrix.fromBlocks G₁ 0 0 (-G₂)`. Rewrite using `[hM]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = Matrix.fromBlocks G₁ 0 0 (-G₂) := by rw [hVW, hWV, Matrix.one_mul, Matrix.mul_one]`. Use `⟨hMh, ⟨Matrix.fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (0 : Matrix (Fin p) (Fin q) ℂ) * W⁻¹ + Matrix.fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (0 : Matrix (Fin p) (Fin q) ℂ) * W⁻¹, ?_⟩, ⟨Matrix.fromCols (0 : Matrix (Fin q) (Fin p) ℂ) (1 : Matrix (Fin q) (Fin q) ℂ) * W⁻¹ + Matrix.fro …` and prove the remaining obligations. Rewrite using `[add_mul_mul_conjTranspose_add_eq_of_two_smul _ _ _ _ key, fromCols_block]`. Simplify using `only [Matrix.mul_one, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.zero_mul, sub_zero]`.

Conclude with `h₁.add h₁`. Rewrite using `[add_mul_mul_conjTranspose_add_eq_of_two_smul _ _ _ _ key, fromCols_block]`. Simplify using `only [Matrix.mul_one, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.zero_mul, zero_sub, neg_add_rev, neg_neg]`. Conclude with `h₂.add h₂`.
-/
theorem signature_of_factor {p q : ℕ} (M W : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    (G₁ : Matrix (Fin p) (Fin p) ℂ) (G₂ : Matrix (Fin q) (Fin q) ℂ) (h₁ : G₁.PosDef) (h₂ : G₂.PosDef)
    (hM : (2 : ℂ) • M = W * Matrix.fromBlocks G₁ 0 0 (-G₂) * Wᴴ) (hdet : M.det ≠ 0) :
    M.IsHermitian ∧ (∃ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, (C * M * Cᴴ).PosDef) ∧
      ∃ C : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ, (-(C * M * Cᴴ)).PosDef := by
  have hN : (Matrix.fromBlocks G₁ 0 0 (-G₂))ᴴ = Matrix.fromBlocks G₁ 0 0 (-G₂) := by
    rw [Matrix.fromBlocks_conjTranspose, h₁.1.eq, Matrix.conjTranspose_neg, h₂.1.eq,
      Matrix.conjTranspose_zero, Matrix.conjTranspose_zero]
  have hMh : M.IsHermitian := by
    have h2 : ((2 : ℂ) • M)ᴴ = (2 : ℂ) • M := by
      rw [hM, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hN,
        Matrix.mul_assoc]
    rw [Matrix.conjTranspose_smul] at h2
    have h3 : (2 : ℂ) • Mᴴ = (2 : ℂ) • M := by simpa using h2
    exact smul_right_injective _ two_ne_zero h3
  have hW : IsUnit W.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have h4 := congrArg Matrix.det hM
    rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, h0] at h4
    simp [hdet] at h4
  have hVW : W⁻¹ * W = 1 := Matrix.nonsing_inv_mul W hW
  have hWV : Wᴴ * (W⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hVW, Matrix.conjTranspose_one]
  have key : W⁻¹ * ((2 : ℂ) • M) * (W⁻¹)ᴴ = Matrix.fromBlocks G₁ 0 0 (-G₂) := by
    rw [hM]
    calc W⁻¹ * (W * Matrix.fromBlocks G₁ 0 0 (-G₂) * Wᴴ) * (W⁻¹)ᴴ
        = (W⁻¹ * W) * Matrix.fromBlocks G₁ 0 0 (-G₂) * (Wᴴ * (W⁻¹)ᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.fromBlocks G₁ 0 0 (-G₂) := by rw [hVW, hWV, Matrix.one_mul, Matrix.mul_one]
  refine ⟨hMh, ⟨Matrix.fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (0 : Matrix (Fin p) (Fin q) ℂ) * W⁻¹ +
      Matrix.fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (0 : Matrix (Fin p) (Fin q) ℂ) * W⁻¹, ?_⟩,
    ⟨Matrix.fromCols (0 : Matrix (Fin q) (Fin p) ℂ) (1 : Matrix (Fin q) (Fin q) ℂ) * W⁻¹ +
      Matrix.fromCols (0 : Matrix (Fin q) (Fin p) ℂ) (1 : Matrix (Fin q) (Fin q) ℂ) * W⁻¹, ?_⟩⟩
  · rw [add_mul_mul_conjTranspose_add_eq_of_two_smul _ _ _ _ key, fromCols_block]
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.zero_mul, sub_zero]
    exact h₁.add h₁
  · rw [add_mul_mul_conjTranspose_add_eq_of_two_smul _ _ _ _ key, fromCols_block]
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.zero_mul, zero_sub,
      neg_add_rev, neg_neg]
    exact h₂.add h₂

/- English proof (translation)
Introduce `h`. Establish `him : H.rt0.im = 0` using `Complex.conj_eq_iff_im.mp h`. Establish `hre` using `congrArg Complex.re H.sqrt_neg_disc_sq`. Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Simplify using `[sq, Complex.mul_re, him] at hre`.

Use polynomial arithmetic with `[mul_self_nonneg H.rt0.re]`.
-/
theorem conj_cmHostRoot_ne_self (H : Host E) : starRingEnd ℂ H.rt0 ≠ H.rt0 := by
  intro h
  have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.mp h
  have hre := congrArg Complex.re H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  simp [sq, Complex.mul_re, him] at hre
  nlinarith [mul_self_nonneg H.rt0.re]

end GlobalTheory.CompanionTheory.Ar.Fl.SignTau

/- English proof (translation)
Apply `GlobalTheory.CompanionTheory.Ar.Fl.SignTau.posDef_of_hermForm` to reduce the goal to its premises. Use extensionality with `a b`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.of_apply]`. Conclude with `hH.apply _ _`. Introduce `z hz`.

Set `w : Fin g → ℂ` to `fun i => if h : ty i = σ then z (e.symm ⟨i, h⟩) else 0`. Establish `hw : ∀ a, w (e a) = z a` using `fun a => by simp [w, (e a).2]`. Establish `hw0 : ∀ i, ty i ≠ σ → w i = 0` using `fun i hi => by simp [w, hi]`. Establish `hwz : w ≠ 0`. Take `⟨a, ha⟩` from `Function.ne_iff.mp hz`.

Conclude with `fun h => ha (by simpa [h] using (hw a).symm)`. Establish `key : hermForm Hm w w = hermForm (Matrix.of fun a b => Hm (e a) (e b)) z z`. Rewrite using `[GlobalTheory.CompanionTheory.Ar.Flat.RiemannTau.hermForm_eq_sum, GlobalTheory.CompanionTheory.Ar.Flat.RiemannTau.hermForm_eq_sum]`. Establish `h1 : ∀ j, ty j ≠ σ → ∑ k, w j * Hm j k * star (w k) = 0` using `fun j hj => by`. Simplify using `[hw0 j hj]`.

Rewrite using `[GlobalTheory.CompanionTheory.Ar.Fl.SignTau.sum_type ty σ e _ h1]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Establish `h2 : ∀ k, ty k ≠ σ → w (e a) * Hm (e a) k * star (w k) = 0` using `fun k hk => by`. Simplify using `[hw0 k hk]`. Rewrite using `[GlobalTheory.CompanionTheory.Ar.Fl.SignTau.sum_type ty σ e _ h2]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `[hw]`. Rewrite using `[← key]`. Conclude with `hpos w hwz`.
-/
private theorem posDef_reindex_of_hermForm_re_pos {E : Type} [Field E] [NumberField E] [IsCMField E] {g n : ℕ}
    (ty : Fin g → (E →+* ℂ)) (σ : E →+* ℂ) (e : Fin n ≃ {i // ty i = σ})
    (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) :
    (Matrix.of fun a b => Hm (e a) (e b)).PosDef := by
  classical
  apply GlobalTheory.CompanionTheory.Ar.Fl.SignTau.posDef_of_hermForm
  · ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    exact hH.apply _ _
  · intro z hz
    let w : Fin g → ℂ := fun i => if h : ty i = σ then z (e.symm ⟨i, h⟩) else 0
    have hw : ∀ a, w (e a) = z a := fun a => by simp [w, (e a).2]
    have hw0 : ∀ i, ty i ≠ σ → w i = 0 := fun i hi => by simp [w, hi]
    have hwz : w ≠ 0 := by
      obtain ⟨a, ha⟩ := Function.ne_iff.mp hz
      exact fun h => ha (by simpa [h] using (hw a).symm)
    have key : hermForm Hm w w = hermForm (Matrix.of fun a b => Hm (e a) (e b)) z z := by
      rw [GlobalTheory.CompanionTheory.Ar.Flat.RiemannTau.hermForm_eq_sum, GlobalTheory.CompanionTheory.Ar.Flat.RiemannTau.hermForm_eq_sum]
      have h1 : ∀ j, ty j ≠ σ → ∑ k, w j * Hm j k * star (w k) = 0 := fun j hj => by
        simp [hw0 j hj]
      rw [GlobalTheory.CompanionTheory.Ar.Fl.SignTau.sum_type ty σ e _ h1]
      refine Finset.sum_congr rfl fun a _ => ?_
      have h2 : ∀ k, ty k ≠ σ → w (e a) * Hm (e a) k * star (w k) = 0 := fun k hk => by
        simp [hw0 k hk]
      rw [GlobalTheory.CompanionTheory.Ar.Fl.SignTau.sum_type ty σ e _ h2]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp [hw]
    rw [← key]
    exact hpos w hwz

/- English proof (translation)
Introduce `E _ _ _ H D g ty P p q X τ hP hT hX hpq hτ`. Take `⟨-, -, -, -, Hm, hH, hpos, hEF⟩` from `id hP`. Take `⟨-, hcomp, hC⟩` from `GlobalTheory.CompanionTheory.Ar.Flat.riemann_tau_component E H D g ty P Hm hP hH hEF`. Establish `hτc : ComplexEmbedding.conjugate τ (H.rt : E) ≠ H.rt0`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, hτ]`.

Conclude with `GlobalTheory.CompanionTheory.Ar.Fl.SignTau.conj_cmHostRoot_ne_self H`. Set `e₁ : Fin p ≃ {i // ty i = τ}` to `(Finite.equivFinOfCardEq ((hT τ).1 hτ)).symm`. Set `e₂ : Fin q ≃ {i // ty i = ComplexEmbedding.conjugate τ}` to `(Finite.equivFinOfCardEq ((hT (ComplexEmbedding.conjugate τ)).2 hτc)).symm`. Set `G₁ : Matrix (Fin p) (Fin p) ℂ` to `Matrix.of fun a b => Hm (e₁ a) (e₁ b)`. Set `G₂ : Matrix (Fin q) (Fin q) ℂ` to `(Matrix.of fun a b => Hm (e₂ a) (e₂ b))ᵀ`.

Set `A : Matrix (Fin p ⊕ Fin q) (Fin p) ℂ` to `Matrix.of fun m a => P (X m) (e₁ a)`. Set `B : Matrix (Fin p ⊕ Fin q) (Fin q) ℂ` to `Matrix.of fun m b => star (P (X m) (e₂ b))`. Establish `h₁ : G₁.PosDef` using `posDef_reindex_of_hermForm_re_pos ty τ e₁ Hm hH hpos`. Establish `h₂ : G₂.PosDef` using `(posDef_reindex_of_hermForm_re_pos ty (ComplexEmbedding.conjugate τ) e₂ Hm hH hpos).transpose`. Establish `hfac : (2 : ℂ) • ((gramE D X).map fun a => Complex.I * τ a) = Matrix.fromCols A B * Matrix.fromBlocks G₁ 0 0 (-G₂) * (Matrix.fromCols A B)ᴴ`.

Rewrite using `[GlobalTheory.CompanionTheory.Ar.Fl.SignTau.fromCols_block]`. Use extensionality with `m n`. Establish `key` using `hcomp τ (X m) (X n)`. Rewrite `key` using `[GlobalTheory.CompanionTheory.Ar.Fl.SignTau.hermForm_tyPart ty τ e₁, GlobalTheory.CompanionTheory.Ar.Fl.SignTau.hermForm_tyPart ty (ComplexEmbedding.conjugate τ) e₂]`. Establish `hA : (A * G₁ * Aᴴ) m n = ∑ a, ∑ b, P (X m) (e₁ a) * Hm (e₁ a) (e₁ b) * star (P (X n) (e₁ b))`.

Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, A, G₁, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Establish `hB : (B * G₂ * Bᴴ) m n = star (∑ a, ∑ b, P (X m) (e₂ a) * Hm (e₂ a) (e₂ b) * star (P (X n) (e₂ b)))`. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.of_apply, B, G₂, Finset.sum_mul, star_sum, star_mul', star_star]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[hH.apply]`. Rewrite using `[Matrix.sub_apply, hA, hB, key]`. Simplify using `only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]`. Rewrite using `[show gramE D X m n = sesq D (X m) (X n) from rfl]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hdetA : (gramE D X).det ≠ 0` using `hC 0 (Fin p ⊕ Fin q) X (by simp [hpq]) hX`. Establish `hdetM : ((gramE D X).map fun a => Complex.I * τ a).det ≠ 0`. Establish `hM' : ((gramE D X).map fun a => Complex.I * τ a) = Complex.I • (τ.mapMatrix (gramE D X))`. Use extensionality with `m n`.

Simplify using `[Matrix.map_apply]`. Rewrite using `[hM', Matrix.det_smul, ← RingHom.map_det]`. Conclude with `mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) ((map_ne_zero τ).mpr hdetA)`. Conclude with `GlobalTheory.CompanionTheory.Ar.Fl.SignTau.signature_of_factor _ (Matrix.fromCols A B) G₁ G₂ h₁ h₂ hfac hdetM`.
-/
theorem GlobalTheory.CompanionTheory.Ar.Fl.signature_tau_gram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (p q : ℕ) (X : Fin p ⊕ Fin q → D.La) (τ : E →+* ℂ), IsPeriod D ty P → IsTypeFn H p q ty → LinearIndependent (𝓞 E) X → p + q = D.p + D.q → τ (H.rt : E) = H.rt0 → ((gramE D X).map fun a => Complex.I * τ a).IsHermitian ∧ (∃ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, (C * ((gramE D X).map fun a => Complex.I * τ a) * Cᴴ).PosDef) ∧ ∃ C : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ, (-(C * ((gramE D X).map fun a => Complex.I * τ a) * Cᴴ)).PosDef := by
  intro E _ _ _ H D g ty P p q X τ hP hT hX hpq hτ
  obtain ⟨-, -, -, -, Hm, hH, hpos, hEF⟩ := id hP
  obtain ⟨-, hcomp, hC⟩ := GlobalTheory.CompanionTheory.Ar.Flat.riemann_tau_component E H D g ty P Hm hP hH hEF
  have hτc : ComplexEmbedding.conjugate τ (H.rt : E) ≠ H.rt0 := by
    rw [ComplexEmbedding.conjugate_coe_eq, hτ]
    exact GlobalTheory.CompanionTheory.Ar.Fl.SignTau.conj_cmHostRoot_ne_self H
  let e₁ : Fin p ≃ {i // ty i = τ} := (Finite.equivFinOfCardEq ((hT τ).1 hτ)).symm
  let e₂ : Fin q ≃ {i // ty i = ComplexEmbedding.conjugate τ} :=
    (Finite.equivFinOfCardEq ((hT (ComplexEmbedding.conjugate τ)).2 hτc)).symm
  let G₁ : Matrix (Fin p) (Fin p) ℂ := Matrix.of fun a b => Hm (e₁ a) (e₁ b)
  let G₂ : Matrix (Fin q) (Fin q) ℂ := (Matrix.of fun a b => Hm (e₂ a) (e₂ b))ᵀ
  let A : Matrix (Fin p ⊕ Fin q) (Fin p) ℂ := Matrix.of fun m a => P (X m) (e₁ a)
  let B : Matrix (Fin p ⊕ Fin q) (Fin q) ℂ := Matrix.of fun m b => star (P (X m) (e₂ b))
  have h₁ : G₁.PosDef := posDef_reindex_of_hermForm_re_pos ty τ e₁ Hm hH hpos
  have h₂ : G₂.PosDef := (posDef_reindex_of_hermForm_re_pos ty (ComplexEmbedding.conjugate τ) e₂ Hm hH hpos).transpose
  have hfac : (2 : ℂ) • ((gramE D X).map fun a => Complex.I * τ a) =
      Matrix.fromCols A B * Matrix.fromBlocks G₁ 0 0 (-G₂) * (Matrix.fromCols A B)ᴴ := by
    rw [GlobalTheory.CompanionTheory.Ar.Fl.SignTau.fromCols_block]
    ext m n
    have key := hcomp τ (X m) (X n)
    rw [GlobalTheory.CompanionTheory.Ar.Fl.SignTau.hermForm_tyPart ty τ e₁,
      GlobalTheory.CompanionTheory.Ar.Fl.SignTau.hermForm_tyPart ty (ComplexEmbedding.conjugate τ) e₂] at key
    have hA : (A * G₁ * Aᴴ) m n =
        ∑ a, ∑ b, P (X m) (e₁ a) * Hm (e₁ a) (e₁ b) * star (P (X n) (e₁ b)) := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, A, G₁, Finset.sum_mul]
      rw [Finset.sum_comm]
    have hB : (B * G₂ * Bᴴ) m n =
        star (∑ a, ∑ b, P (X m) (e₂ a) * Hm (e₂ a) (e₂ b) * star (P (X n) (e₂ b))) := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.of_apply, B, G₂,
        Finset.sum_mul, star_sum, star_mul', star_star]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hH.apply]
    rw [Matrix.sub_apply, hA, hB, key]
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [show gramE D X m n = sesq D (X m) (X n) from rfl]
    ring
  have hdetA : (gramE D X).det ≠ 0 := hC 0 (Fin p ⊕ Fin q) X (by simp [hpq]) hX
  have hdetM : ((gramE D X).map fun a => Complex.I * τ a).det ≠ 0 := by
    have hM' : ((gramE D X).map fun a => Complex.I * τ a) = Complex.I • (τ.mapMatrix (gramE D X)) := by
      ext m n
      simp [Matrix.map_apply]
    rw [hM', Matrix.det_smul, ← RingHom.map_det]
    exact mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) ((map_ne_zero τ).mpr hdetA)
  exact GlobalTheory.CompanionTheory.Ar.Fl.SignTau.signature_of_factor _ (Matrix.fromCols A B) G₁ G₂ h₁ h₂ hfac hdetM
