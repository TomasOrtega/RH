import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs

open Matrix Polynomial
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.Tf.Loc (twConj)

noncomputable section

namespace GlobalTheory.CompanionTheory.EllipticTwist

/- English proof (translation)
Establish `hne : N.charpoly ≠ 0` using `(Matrix.charpoly_monic N).ne_zero`. Establish `hcard : N.charpoly.roots.toFinset.card = n`. Rewrite using `[Multiset.toFinset_card_of_nodup (nodup_roots hs), splits_iff_card_roots.1 (IsAlgClosed.splits _), charpoly_natDegree_eq_dim, Fintype.card_fin]`. Set `e` to `Finset.equivFinOfCardEq hcard`. Set `γ : Fin n → ℂ` to `fun i => (e.symm i).1`.

Establish `hinj : Function.Injective γ` using `fun i j hij => e.symm.injective (Subtype.ext hij)`. Establish `hroot : ∀ i, N.charpoly.IsRoot (γ i)` using `fun i => (mem_roots hne).1 (Multiset.mem_toFinset.1 (e.symm i).2)`. Establish `hev : ∀ i, ∃ v : Fin n → ℂ, v ≠ 0 ∧ (scalar (Fin n) (γ i) - N) *ᵥ v = 0` using `fun i => exists_mulVec_eq_zero_iff.2 (by rw [← eval_charpoly]; exact hroot i)`. Use `choose v hv0 hv using hev`. Establish `hNv : ∀ i, N *ᵥ v i = γ i • v i` using `fun i => by`.

Establish `h1` using `hv i`. Rewrite `h1` using `[sub_mulVec, sub_eq_zero]`. Rewrite using `[← h1]`. Use extensionality with `k`. Simplify using `[scalar_apply, mulVec_diagonal]`.

Establish `hli : LinearIndependent ℂ v` using `Module.End.eigenvectors_linearIndependent' (Matrix.toLin' N) γ hinj v (fun i => Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 (by simpa using hNv i), hv0 i⟩)`. Establish `hu : IsUnit (Matrix.of v)ᵀ` using `linearIndependent_cols_iff_isUnit.1 hli`. Take `⟨h, hh⟩` from `hu`. Use `⟨h, γ, hinj, hroot, ?_⟩` and prove the remaining obligations. Establish `hh' : h.val = (Matrix.of v)ᵀ` using `hh`.

Rewrite using `[hh']`. Use extensionality with `i j`. Establish `h2` using `congrFun (hNv j) i`. Rewrite using `[mul_diagonal]`. Simplify `h2` using `[mul_apply, mulVec, dotProduct, mul_comm]`.
-/
theorem exists_eigenbasis {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) (hs : N.charpoly.Separable) :
    ∃ (h : GL (Fin n) ℂ) (γ : Fin n → ℂ), Function.Injective γ ∧ (∀ i, N.charpoly.IsRoot (γ i)) ∧
      N * h.val = h.val * diagonal γ := by
  have hne : N.charpoly ≠ 0 := (Matrix.charpoly_monic N).ne_zero
  have hcard : N.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hs), splits_iff_card_roots.1 (IsAlgClosed.splits _),
      charpoly_natDegree_eq_dim, Fintype.card_fin]
  let e := Finset.equivFinOfCardEq hcard
  let γ : Fin n → ℂ := fun i => (e.symm i).1
  have hinj : Function.Injective γ := fun i j hij => e.symm.injective (Subtype.ext hij)
  have hroot : ∀ i, N.charpoly.IsRoot (γ i) := fun i =>
    (mem_roots hne).1 (Multiset.mem_toFinset.1 (e.symm i).2)
  have hev : ∀ i, ∃ v : Fin n → ℂ, v ≠ 0 ∧ (scalar (Fin n) (γ i) - N) *ᵥ v = 0 := fun i =>
    exists_mulVec_eq_zero_iff.2 (by rw [← eval_charpoly]; exact hroot i)
  choose v hv0 hv using hev
  have hNv : ∀ i, N *ᵥ v i = γ i • v i := fun i => by
    have h1 := hv i
    rw [sub_mulVec, sub_eq_zero] at h1
    rw [← h1]
    ext k
    simp [scalar_apply, mulVec_diagonal]
  have hli : LinearIndependent ℂ v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' N) γ hinj v
      (fun i => Module.End.hasEigenvector_iff.2
        ⟨Module.End.mem_eigenspace_iff.2 (by simpa using hNv i), hv0 i⟩)
  have hu : IsUnit (Matrix.of v)ᵀ := linearIndependent_cols_iff_isUnit.1 hli
  obtain ⟨h, hh⟩ := hu
  refine ⟨h, γ, hinj, hroot, ?_⟩
  have hh' : h.val = (Matrix.of v)ᵀ := hh
  rw [hh']
  ext i j
  have h2 := congrFun (hNv j) i
  rw [mul_diagonal]
  simpa [mul_apply, mulVec, dotProduct, mul_comm] using h2

variable {n : ℕ}

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[thetaR_val, conjTranspose_apply]`.
-/
theorem theta_val (g : GL (Fin n) ℂ) :
    (thetaR (starRingEnd ℂ) n g).val = (g⁻¹).valᴴ := by
  ext i j
  simp [thetaR_val, conjTranspose_apply]

/- English proof (translation)
Rewrite using `[← map_inv, theta_val, inv_inv]`.
-/
theorem theta_inv_val (g : GL (Fin n) ℂ) :
    ((thetaR (starRingEnd ℂ) n g)⁻¹).val = g.valᴴ := by
  rw [← map_inv, theta_val, inv_inv]

/- English proof (translation)
The claim follows from `Units.ext (by rw [theta_val, theta_inv_val, conjTranspose_conjTranspose])`.
-/
theorem theta_theta (g : GL (Fin n) ℂ) :
    thetaR (starRingEnd ℂ) n (thetaR (starRingEnd ℂ) n g) = g :=
  Units.ext (by rw [theta_val, theta_inv_val, conjTranspose_conjTranspose])

/- English proof (translation)
Establish `h2 : Dᴴ = D * diagonal (star γ)` using `by conv_lhs => rw [hD]`. Rewrite using `[conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose]`. Establish `h3 : D i j = γ i * (D i j * star (γ j))` using `by conv_lhs => rw [hD, h2]`. Rewrite using `[diagonal_mul, mul_diagonal]`. Both sides reduce to the same expression.

Assume the negation of the conclusion as `hne`. Establish `h4 : γ i * star (γ j) = 1`. Apply `mul_left_cancel₀ hne` to reduce the goal to its premises. Take the linear combination `-h3`. Establish `h5 : star (γ j) * γ j = 1`.

Use `Complex.conj_mul' (γ j)` as an intermediate fact. Rewrite `this` using `[hγ j]`. Simplify using `using this`. Apply `hij` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises.

Take the linear combination `-γ i * h5 + γ j * h4`.
-/
theorem offDiag_eq_zero (D : Matrix (Fin n) (Fin n) ℂ) (γ : Fin n → ℂ) (hγ : ∀ i, ‖γ i‖ = 1)
    (hinj : Function.Injective γ) (hD : D = diagonal γ * Dᴴ) {i j : Fin n} (hij : i ≠ j) : D i j = 0 := by
  have h2 : Dᴴ = D * diagonal (star γ) := by
    conv_lhs => rw [hD]
    rw [conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose]
  have h3 : D i j = γ i * (D i j * star (γ j)) := by
    conv_lhs => rw [hD, h2]
    rw [diagonal_mul, mul_diagonal]
    rfl
  by_contra hne
  have h4 : γ i * star (γ j) = 1 := by
    apply mul_left_cancel₀ hne
    linear_combination -h3
  have h5 : star (γ j) * γ j = 1 := by
    have := Complex.conj_mul' (γ j)
    rw [hγ j] at this
    simpa using this
  apply hij
  apply hinj
  linear_combination -γ i * h5 + γ j * h4

/- English proof (translation)
Introduce `n d hd`. Take `⟨hs, hn⟩` from `hd`. Take `⟨h, γ, hinj, hroot, hN⟩` from `exists_eigenbasis _ hs`. Establish `hγ : ∀ i, ‖γ i‖ = 1` using `fun i => hn _ (hroot i)`. Use `set θ := thetaR (starRingEnd ℂ) n with hθ`.

Set `d₁ : GL (Fin n) ℂ` to `twConj θ h d`. Establish `hnorm : (d₁ * θ d₁).val = diagonal γ`. Establish `h1 : d₁ * θ d₁ = h⁻¹ * (d * θ d) * h`. Simplify using `[d₁, twConj, map_mul, map_inv, hθ, theta_theta, mul_assoc]`. Rewrite using `[h1, Units.val_mul, Units.val_mul, mul_assoc, hN, ← mul_assoc, ← Units.val_mul]`.

Simplify using the standard rewrite rules. Establish `hD : d₁.val = diagonal γ * d₁.valᴴ`. Rewrite using `[← hnorm, ← theta_inv_val, ← Units.val_mul]`. Simplify using `[hθ]`. Set `b : Fin n → ℂ` to `fun i => d₁.val i i`.

Establish `hdiag : d₁.val = diagonal b`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[b]`.

Rewrite using `[offDiag_eq_zero _ γ hγ hinj hD hij, diagonal_apply_ne _ hij]`. Establish `hb0 : ∀ i, b i ≠ 0`. Introduce `i hi`. Establish `h0 : d₁.val.det = 0`. Rewrite using `[hdiag, det_diagonal]`.

Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) hi`. Establish `h1` using `(Matrix.isUnit_iff_isUnit_det _).1 d₁.isUnit`. Rewrite `h1` using `[h0]`. Conclude with `not_isUnit_zero h1`. Establish `hbγ : ∀ i, b i = γ i * (starRingEnd ℂ) (b i)`.

Introduce `i`. Establish `h1` using `congrFun (congrFun hD i) i`. Rewrite `h1` using `[diagonal_mul]`. Simplify `h1` using `[conjTranspose_apply]`. Set `s : Fin n → ℂ` to `fun i => ((Real.sqrt ‖b i‖ : ℝ) : ℂ)`.

Establish `hnb : ∀ i, 0 < ‖b i‖` using `fun i => norm_pos_iff.2 (hb0 i)`. Establish `hs0 : ∀ i, s i ≠ 0` using `fun i => Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hnb i)).ne'`. Establish `hss : ∀ i, s i * s i = (‖b i‖ : ℂ)` using `fun i => by`. Simplify using `only [s]`. Rewrite using `[← Complex.ofReal_mul, Real.mul_self_sqrt (hnb i).le]`.

Set `t : GL (Fin n) ℂ` to `⟨diagonal s, diagonal fun i => (s i)⁻¹, by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; ext i; exact mul_inv_cancel₀ (hs0 i), by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; ext i; exact inv_mul_cancel₀ (hs0 i)⟩`. Establish `htinv : (t⁻¹).val = diagonal fun i => (s i)⁻¹` using `rfl`. Establish `htθ : (θ t).val = diagonal fun i => (s i)⁻¹`. Rewrite using `[hθ, theta_val, htinv, diagonal_conjTranspose]`. Use `congr 1`.

Use extensionality with `i`. Simplify using `[s]`. Set `z : Fin n → ℂ` to `fun i => b i / (‖b i‖ : ℂ)`. Establish `hz2 : ∀ i, z i ^ 2 = γ i`. Introduce `i`.

Establish `hne : (‖b i‖ : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 (hnb i).ne'`. Establish `h1` using `Complex.mul_conj' (b i)`. Simplify using `only [z]`. Rewrite using `[div_pow, div_eq_iff (pow_ne_zero 2 hne), ← h1]`. Use `conv_lhs => rw [sq]`.

Use `enter [1]`. Rewrite using `[hbγ i]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨(h * t)⁻¹, twConj θ t d₁, z, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(t⁻¹ * d₁ * θ t).val = _`.

Rewrite using `[Units.val_mul, Units.val_mul, htinv, hdiag, htθ, diagonal_mul_diagonal, diagonal_mul_diagonal]`. Use `congr 1`. Use extensionality with `i`. Use `hss i` as an intermediate fact. Establish `h0` using `hs0 i`.

Simplify using `only [z]`. Rewrite using `[← this]`. Clear the denominators using the available nonvanishing facts. Introduce `i`. Simplify using `only [z]`.

Rewrite using `[norm_div, Complex.norm_real, norm_norm, div_self (hnb i).ne']`. Introduce `i j hij`. Apply `hinj` to reduce the goal to its premises. Use `hz2 i` as an intermediate fact. Use `hz2 j` as an intermediate fact.

Simplify using `only at hij`. Rewrite using `[← hz2 i, ← hz2 j, hij]`. Simplify using `[twConj, d₁, map_mul, map_inv, mul_assoc]`.
-/
theorem ellDiag : EllDiag := by
  intro n d hd
  obtain ⟨hs, hn⟩ := hd
  obtain ⟨h, γ, hinj, hroot, hN⟩ := exists_eigenbasis _ hs
  have hγ : ∀ i, ‖γ i‖ = 1 := fun i => hn _ (hroot i)
  set θ := thetaR (starRingEnd ℂ) n with hθ
  let d₁ : GL (Fin n) ℂ := twConj θ h d
  have hnorm : (d₁ * θ d₁).val = diagonal γ := by
    have h1 : d₁ * θ d₁ = h⁻¹ * (d * θ d) * h := by
      simp [d₁, twConj, map_mul, map_inv, hθ, theta_theta, mul_assoc]
    rw [h1, Units.val_mul, Units.val_mul, mul_assoc, hN, ← mul_assoc, ← Units.val_mul]
    simp
  have hD : d₁.val = diagonal γ * d₁.valᴴ := by
    rw [← hnorm, ← theta_inv_val, ← Units.val_mul]
    simp [hθ]
  let b : Fin n → ℂ := fun i => d₁.val i i
  have hdiag : d₁.val = diagonal b := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [b]
    · rw [offDiag_eq_zero _ γ hγ hinj hD hij, diagonal_apply_ne _ hij]
  have hb0 : ∀ i, b i ≠ 0 := by
    intro i hi
    have h0 : d₁.val.det = 0 := by
      rw [hdiag, det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    have h1 := (Matrix.isUnit_iff_isUnit_det _).1 d₁.isUnit
    rw [h0] at h1
    exact not_isUnit_zero h1
  have hbγ : ∀ i, b i = γ i * (starRingEnd ℂ) (b i) := by
    intro i
    have h1 := congrFun (congrFun hD i) i
    rw [diagonal_mul] at h1
    simpa [conjTranspose_apply] using h1
  let s : Fin n → ℂ := fun i => ((Real.sqrt ‖b i‖ : ℝ) : ℂ)
  have hnb : ∀ i, 0 < ‖b i‖ := fun i => norm_pos_iff.2 (hb0 i)
  have hs0 : ∀ i, s i ≠ 0 := fun i =>
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hnb i)).ne'
  have hss : ∀ i, s i * s i = (‖b i‖ : ℂ) := fun i => by
    simp only [s]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hnb i).le]
  let t : GL (Fin n) ℂ := ⟨diagonal s, diagonal fun i => (s i)⁻¹,
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; ext i; exact mul_inv_cancel₀ (hs0 i),
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; ext i; exact inv_mul_cancel₀ (hs0 i)⟩
  have htinv : (t⁻¹).val = diagonal fun i => (s i)⁻¹ := rfl
  have htθ : (θ t).val = diagonal fun i => (s i)⁻¹ := by
    rw [hθ, theta_val, htinv, diagonal_conjTranspose]
    congr 1
    ext i
    simp [s]
  let z : Fin n → ℂ := fun i => b i / (‖b i‖ : ℂ)
  have hz2 : ∀ i, z i ^ 2 = γ i := by
    intro i
    have hne : (‖b i‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hnb i).ne'
    have h1 := Complex.mul_conj' (b i)
    simp only [z]
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hne), ← h1]
    conv_lhs => rw [sq]; enter [1]; rw [hbγ i]
    ring
  refine ⟨(h * t)⁻¹, twConj θ t d₁, z, ?_, ?_, ?_, ?_⟩
  · change (t⁻¹ * d₁ * θ t).val = _
    rw [Units.val_mul, Units.val_mul, htinv, hdiag, htθ, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    ext i
    have := hss i
    have h0 := hs0 i
    simp only [z]
    rw [← this]
    field_simp
  · intro i
    simp only [z]
    rw [norm_div, Complex.norm_real, norm_norm, div_self (hnb i).ne']
  · intro i j hij
    apply hinj
    have := hz2 i
    have := hz2 j
    simp only at hij
    rw [← hz2 i, ← hz2 j, hij]
  · simp [twConj, d₁, map_mul, map_inv, mul_assoc]

end GlobalTheory.CompanionTheory.EllipticTwist

end
