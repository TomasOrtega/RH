import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
noncomputable section
namespace GlobalTheory.MBLow.Cl.Exp

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X}

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem co_add (χ χ' : N.X) : co bX (χ + χ') = co bX χ + co bX χ' := by
  funext l; simp [co]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem co_basis (l : Fin r) : co bX (bX l) = Pi.single l 1 := by
  funext l'; simp [co, Pi.single_apply, Finsupp.single_apply, eq_comm]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem co_sum (n : Fin r → ℤ) : co bX (∑ l, n l • bX l) = cv n := by
  funext l; simp [co, cv, Finsupp.single_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem leftComponent_add (σ : Fin g ≃ Fin g' ⊕ Fin r) (Z Z' : Fin g → ℂ) : zP σ (Z + Z') = zP σ Z + zP σ Z' := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem secondBlock_add (σ : Fin g ≃ Fin g' ⊕ Fin r) (Z Z' : Fin g → ℂ) : tP σ (Z + Z') = tP σ Z + tP σ Z' := rfl

def asm {A : Type} (σ : Fin g ≃ Fin g' ⊕ Fin r) (u : Fin g' → A) (w : Fin r → A) : Fin g → A := fun j => Sum.elim u w (σ j)

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
@[simp] theorem leftComponent_assemble {A : Type} (σ : Fin g ≃ Fin g' ⊕ Fin r) (u : Fin g' → A) (w : Fin r → A) : zP σ (asm σ u w) = u := by
  funext i; simp [zP, asm]
/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
@[simp] theorem secondBlock_assemble {A : Type} (σ : Fin g ≃ Fin g' ⊕ Fin r) (u : Fin g' → A) (w : Fin r → A) : tP σ (asm σ u w) = w := by
  funext i; simp [tP, asm]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Extract witnesses or component facts from the available result. Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately.
-/
theorem ext_zP_tP {A : Type} (σ : Fin g ≃ Fin g' ⊕ Fin r) {Z Z' : Fin g → A} (h1 : zP σ Z = zP σ Z') (h2 : tP σ Z = tP σ Z') :
    Z = Z' := by
  funext j
  obtain ⟨k, rfl⟩ := σ.symm.surjective j
  cases k with
  | inl i => exact congrFun h1 i
  | inr l => exact congrFun h2 l

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem leftComponent_intCast (σ : Fin g ≃ Fin g' ⊕ Fin r) (M : Fin g → ℤ) : zP σ (cv M) = cv (zP σ M) := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem secondBlock_intCast (σ : Fin g ≃ Fin g' ⊕ Fin r) (M : Fin g → ℤ) : tP σ (cv M) = cv (tP σ M) := rfl

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem leftComponent_periodVector (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r) (S : Matrix (Fin r) (Fin r) ℂ) (M Nn : Fin g → ℤ) :
    zP σ (perV (d.full σ S) M Nn) = perV d.τ (zP σ M) (zP σ Nn) + d.t12 *ᵥ cv (tP σ Nn) := by
  funext i
  simp [perV, CD.full, zP, tP, cv, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, Function.comp_def, add_assoc]
  rfl

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem secondBlock_periodVector (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r) (S : Matrix (Fin r) (Fin r) ℂ) (M Nn : Fin g → ℤ) :
    tP σ (perV (d.full σ S) M Nn) = cv (tP σ M) + d.t12ᵀ *ᵥ cv (zP σ Nn) + (d.t22 + S) *ᵥ cv (tP σ Nn) := by
  funext i
  simp [perV, CD.full, zP, tP, cv, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, Function.comp_def, add_assoc]
  rfl

end GlobalTheory.MBLow.Cl.Exp
end

noncomputable section
namespace GlobalTheory.MBLow.Cl.Exp

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X}

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Put the polynomial expressions in normal form.
-/
theorem exp_two_pi_add (u v : ℂ) : Complex.exp (2 * Real.pi * Complex.I * (u + v)) =
    Complex.exp (2 * Real.pi * Complex.I * u) * Complex.exp (2 * Real.pi * Complex.I * v) := by
  rw [← Complex.exp_add]; ring_nf

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem exists_log_char (φ : N.X → ℂˣ) (h : ∀ x y, φ (x + y) = φ x * φ y) :
    ∃ w : Fin r → ℂ, ∀ χ, (φ χ : ℂ) = Complex.exp (2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ w)) := by
  let w : Fin r → ℂ := fun l => Complex.log (φ (bX l)) / (2 * Real.pi * Complex.I)
  let F : N.X →+ Additive ℂˣ := AddMonoidHom.mk' (fun x => Additive.ofMul (φ x)) fun x y => by rw [h, ofMul_mul]
  let G : N.X →+ Additive ℂˣ := AddMonoidHom.mk'
    (fun x => Additive.ofMul (Units.mk0 (Complex.exp (2 * Real.pi * Complex.I * (co bX x ⬝ᵥ w))) (Complex.exp_ne_zero _)))
    fun x y => by
      rw [← ofMul_mul]
      congr 1
      exact Units.ext (by simp [co_add, add_dotProduct, exp_two_pi_add])
  have e : F.toIntLinearMap = G.toIntLinearMap := bX.ext fun l => by
    change Additive.ofMul (φ (bX l)) = Additive.ofMul (Units.mk0 _ (Complex.exp_ne_zero _))
    congr 1
    refine Units.ext ?_
    simp only [Units.val_mk0, co_basis, single_dotProduct, _root_.one_mul, w]
    rw [mul_div_cancel₀ _ Complex.two_pi_I_ne_zero, Complex.exp_log (φ (bX l)).ne_zero]
  refine ⟨w, fun x => ?_⟩
  exact congrArg (fun a : Additive ℂˣ => ((Additive.toMul a : ℂˣ) : ℂ)) (LinearMap.congr_fun e x)

variable (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cube_val (x y z : Fin g' → ℂ) :
    (N.θ (d.ex x) (d.ex y) (d.ex z) : ℂ) * d.fr (x + y) * d.fr (x + z) * d.fr (y + z) =
      d.fr (x + y + z) * d.fr x * d.fr y * d.fr z := by
  exact_mod_cast congrArg Units.val (d.cub x y z)

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Simplify using the standard rewrite rules. Introduce a local definition for the expression. Establish an intermediate fact.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem existsUnique_isPt (Z : Fin g → ℂ) : ∃! h, d.IsPt σ Z h := by
  set z := zP σ Z
  let E : N.X → ℂ := fun χ => Complex.exp (2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ tP σ Z))
  have hE : ∀ χ χ', E (χ + χ') = E χ * E χ' := fun χ χ' => by
    simp only [E, co_add, add_dotProduct, exp_two_pi_add]
  let s : N.X → ℂˣ := fun χ => Units.mk0 (E χ) (Complex.exp_ne_zero _) * d.fr (d.t12 *ᵥ co bX χ) * d.fr z /
    d.fr (d.t12 *ᵥ co bX χ + z)
  have hs : ∀ χ, (s χ : ℂ) * d.fr (d.t12 *ᵥ co bX χ + z) = E χ * d.fr (d.t12 *ᵥ co bX χ) * d.fr z := fun χ => by
    simp [s]
  refine ⟨⟨d.ex z, s, fun χ χ' => ?_⟩, ⟨rfl, fun χ => hs χ⟩, fun h hh => ?_⟩
  · rw [d.c_eq, d.c_eq]
    apply Units.ext
    have h1 := hs χ
    have h2 := hs χ'
    have h3 := hs (χ + χ')
    have h4 := cube_val d (d.t12 *ᵥ co bX χ) (d.t12 *ᵥ co bX χ') z
    rw [co_add, mulVec_add, hE] at h3
    apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (d.fr (d.t12 *ᵥ co bX χ + d.t12 *ᵥ co bX χ' + z)).ne_zero
      (d.fr (d.t12 *ᵥ co bX χ + z)).ne_zero) (d.fr (d.t12 *ᵥ co bX χ' + z)).ne_zero)
    push_cast
    linear_combination ((N.θ (d.ex (d.t12 *ᵥ co bX χ)) (d.ex (d.t12 *ᵥ co bX χ')) (d.ex z) : ℂ) *
        d.fr (d.t12 *ᵥ co bX χ + z) * d.fr (d.t12 *ᵥ co bX χ' + z)) * h3 +
      (E χ * E χ' * d.fr z) * h4 -
      (d.fr (d.t12 *ᵥ co bX χ + d.t12 *ᵥ co bX χ' + z) * s χ' * d.fr (d.t12 *ᵥ co bX χ' + z)) * h1 -
      (d.fr (d.t12 *ᵥ co bX χ + d.t12 *ᵥ co bX χ' + z) * E χ * d.fr (d.t12 *ᵥ co bX χ) * d.fr z) * h2
  · refine NumD.Gt.ext hh.1 (funext fun χ => ?_)
    apply Units.ext
    apply mul_right_cancel₀ (d.fr (d.t12 *ᵥ co bX χ + z)).ne_zero
    rw [hh.2]
    exact (hs χ).symm

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Clear the denominators using the available nonvanishing facts. A detailed English derivation is pending.
-/
theorem exists_isPt (h : N.Gt) : ∃ Z, d.IsPt σ Z h := by
  obtain ⟨z, hz⟩ := d.onto h.b
  obtain ⟨w, hw⟩ := exists_log_char (bX := bX)
    (fun χ => h.s χ * d.fr (d.t12 *ᵥ co bX χ + z) / (d.fr (d.t12 *ᵥ co bX χ) * d.fr z)) fun χ χ' => by
      have a := h.mult χ χ'
      have c := d.cub (d.t12 *ᵥ co bX χ) (d.t12 *ᵥ co bX χ') z
      rw [d.c_eq, d.c_eq, ← hz] at a
      rw [co_add, mulVec_add]
      replace a := congrArg Additive.ofMul a
      replace c := congrArg Additive.ofMul c
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_div] at a c ⊢
      linear_combination (norm := abel) a - c
  refine ⟨asm σ z w, by rw [leftComponent_assemble, hz], fun χ => ?_⟩
  rw [leftComponent_assemble, secondBlock_assemble, ← hw χ]
  push_cast
  field_simp

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem IsPt.add {Z Z' : Fin g → ℂ} {h h' : N.Gt} (hh : d.IsPt σ Z h) (hh' : d.IsPt σ Z' h') :
    d.IsPt σ (Z + Z') (h * h') := by
  refine ⟨by rw [NumD.Gt.mul_b, hh.1, hh'.1, leftComponent_add, d.ex_add], fun χ => ?_⟩
  have h1 := hh.2 χ
  have h2 := hh'.2 χ
  have h4 := cube_val d (d.t12 *ᵥ co bX χ) (zP σ Z) (zP σ Z')
  rw [NumD.Gt.mul_s, d.c_eq, hh.1, hh'.1, leftComponent_add, secondBlock_add, dotProduct_add, exp_two_pi_add, ← add_assoc]
  push_cast
  rw [div_mul_eq_mul_div, div_eq_iff (Units.ne_zero _)]
  apply mul_right_cancel₀ (mul_ne_zero (d.fr (d.t12 *ᵥ co bX χ + zP σ Z)).ne_zero (d.fr (d.t12 *ᵥ co bX χ + zP σ Z')).ne_zero)
  linear_combination (d.fr (d.t12 *ᵥ co bX χ + zP σ Z + zP σ Z') * h'.s χ * d.fr (d.t12 *ᵥ co bX χ + zP σ Z')) * h1 +
    (d.fr (d.t12 *ᵥ co bX χ + zP σ Z + zP σ Z') * Complex.exp (2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ tP σ Z)) *
      d.fr (d.t12 *ᵥ co bX χ) * d.fr (zP σ Z)) * h2 -
    (Complex.exp (2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ tP σ Z)) *
      Complex.exp (2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ tP σ Z')) * d.fr (d.t12 *ᵥ co bX χ)) * h4

end GlobalTheory.MBLow.Cl.Exp
end

noncomputable section
namespace GlobalTheory.MBLow.Cl.Exp

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X}

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem cv_zero {k : ℕ} : cv (0 : Fin k → ℤ) = 0 := by funext i; simp [cv]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem dotProduct_mulVec_eq_transpose_mulVec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (u : Fin m → ℂ) (v : Fin n → ℂ) :
    u ⬝ᵥ A *ᵥ v = v ⬝ᵥ Aᵀ *ᵥ u := by
  rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem exp_int_dot (χ : N.X) (K : Fin r → ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ cv K)) = 1 := by
  have : co bX χ ⬝ᵥ cv K = ((∑ l, bX.repr χ l * K l : ℤ) : ℂ) := by simp [co, cv, dotProduct]
  rw [this, mul_comm, Complex.exp_int_mul_two_pi_mul_I]

variable (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem fr_shift (M n : Fin g' → ℤ) (x : Fin g' → ℂ) :
    (d.fr (x + perV d.τ M n) : ℂ) = d.fr x * Complex.exp (2 * Real.pi * Complex.I * (cv n ⬝ᵥ x)) * d.fr (perV d.τ M n) := by
  have h1 := d.fr_per M n x
  have h0 := d.fr_per M n 0
  rw [d.fr_zero, zero_add, Units.val_one] at h0
  have hA : autV d.τ d.a d.b M n x * Complex.exp (2 * Real.pi * Complex.I * (cv n ⬝ᵥ x)) = autV d.τ d.a d.b M n 0 := by
    simp only [autV, ← Complex.exp_add, dotProduct_zero]; congr 1; ring
  have hne : autV d.τ d.a d.b M n 0 ≠ 0 := Complex.exp_ne_zero _
  apply mul_left_cancel₀ hne
  linear_combination (-(d.fr (x + perV d.τ M n) : ℂ)) * hA - Complex.exp (2 * Real.pi * Complex.I * (cv n ⬝ᵥ x)) * h1 +
    Complex.exp (2 * Real.pi * Complex.I * (cv n ⬝ᵥ x)) * d.fr x * h0

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ex_perV (M n : Fin g' → ℤ) : d.ex (perV d.τ M n) = 1 := (d.ker _).2 ⟨M, n, rfl⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Put the polynomial expressions in normal form.

Reduce the claim to the hypotheses of an applicable result. Take a linear combination of the given relations to obtain the conclusion. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Take a linear combination of the given relations to obtain the conclusion.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Assume the hypotheses and unpack their components. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem isPt_one_iff (Z : Fin g → ℂ) : d.IsPt σ Z 1 ↔ ∃ M Nn, tP σ Nn = 0 ∧ Z = perV (d.full σ 0) M Nn := by
  constructor
  · rintro ⟨hb, hs⟩
    obtain ⟨M', n, hMn⟩ := (d.ker _).1 hb.symm
    have key : ∀ l, ∃ k : ℤ, tP σ Z l = k + (d.t12ᵀ *ᵥ cv n) l := fun l => by
      have h1 := hs (bX l)
      rw [NumD.Gt.generator_inv_base, Units.val_one, _root_.one_mul, hMn, fr_shift, co_basis, single_dotProduct, _root_.one_mul,
        dotProduct_mulVec_eq_transpose_mulVec, single_dotProduct, _root_.one_mul] at h1
      have h5 : Complex.exp (2 * Real.pi * Complex.I * (tP σ Z l - (d.t12ᵀ *ᵥ cv n) l)) = 1 := by
        have e : Complex.exp (2 * Real.pi * Complex.I * (tP σ Z l - (d.t12ᵀ *ᵥ cv n) l)) *
            Complex.exp (2 * Real.pi * Complex.I * (d.t12ᵀ *ᵥ cv n) l) = Complex.exp (2 * Real.pi * Complex.I * tP σ Z l) := by
          rw [← Complex.exp_add]; ring_nf
        apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (d.fr (d.t12 *ᵥ Pi.single l 1)).ne_zero
          (d.fr (perV d.τ M' n)).ne_zero) (Complex.exp_ne_zero (2 * Real.pi * Complex.I * (d.t12ᵀ *ᵥ cv n) l)))
        linear_combination (d.fr (d.t12 *ᵥ Pi.single l 1) * d.fr (perV d.τ M' n)) * e - h1
      obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 h5
      refine ⟨k, ?_⟩
      have := Complex.two_pi_I_ne_zero
      have e2 : tP σ Z l - (d.t12ᵀ *ᵥ cv n) l = k := by
        apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
        rw [hk]; ring
      linear_combination e2
    choose K hK using key
    refine ⟨asm σ M' K, asm σ n 0, secondBlock_assemble σ _ _, ext_zP_tP σ ?_ ?_⟩
    · rw [leftComponent_periodVector, leftComponent_assemble, leftComponent_assemble, secondBlock_assemble, hMn, cv_zero, mulVec_zero, add_zero]
    · rw [secondBlock_periodVector, secondBlock_assemble, leftComponent_assemble, secondBlock_assemble]
      funext l
      simp [cv_zero, hK, cv]
  · rintro ⟨M, Nn, h0, rfl⟩
    have hc : cv (tP σ Nn) = 0 := by rw [h0]; funext l; simp [cv]
    refine ⟨?_, fun χ => ?_⟩
    · rw [leftComponent_periodVector, hc, mulVec_zero, add_zero, ex_perV]; rfl
    · simp only [leftComponent_periodVector, secondBlock_periodVector, hc, mulVec_zero, add_zero, NumD.Gt.generator_inv_base, Units.val_one, _root_.one_mul]
      rw [fr_shift, dotProduct_add, exp_two_pi_add, exp_int_dot, _root_.one_mul, dotProduct_mulVec_eq_transpose_mulVec d.t12 (cv (zP σ Nn))]
      ring

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression.

Establish an intermediate fact. Move the embeddings inside the algebraic operations. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem isPt_perV (M Nn : Fin g → ℤ) :
    d.IsPt σ (perV (d.full σ 0) M Nn) (N.io (∑ l, tP σ Nn l • bX l)) := by
  set y := ∑ l, tP σ Nn l • bX l
  have hy : co bX y = cv (tP σ Nn) := co_sum _
  refine ⟨?_, fun χ => ?_⟩
  · rw [NumD.io_b, d.c_eq, leftComponent_periodVector, hy, d.ex_add, ex_perV, _root_.one_mul]
  rw [NumD.io_s, leftComponent_periodVector, secondBlock_periodVector, ← hy, add_zero]
  set p := perV d.τ (zP σ M) (zP σ Nn)
  set xy := d.t12 *ᵥ co bX y
  set xc := d.t12 *ᵥ co bX χ
  let Q : N.X → ℂ := fun χ => Complex.exp (Real.pi * Complex.I * (co bX χ ⬝ᵥ d.t22 *ᵥ co bX χ) +
    2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ d.b2))
  have hψ := congrArg Units.val (N.ψ_add y χ)
  push_cast at hψ
  have h1 : (N.ψ y : ℂ) * d.fr xy = Q y := d.ψ_eq y
  have h2 : (N.ψ χ : ℂ) * d.fr xc = Q χ := d.ψ_eq χ
  have h3 : (N.ψ (y + χ) : ℂ) * d.fr (xy + xc) = Q (y + χ) := by
    rw [← mulVec_add, ← co_add]; exact d.ψ_eq (y + χ)
  have hQ : Q (y + χ) = Q y * Q χ * Complex.exp (2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ d.t22 *ᵥ co bX y)) := by
    simp only [Q, ← Complex.exp_add]
    congr 1
    have hs : co bX y ⬝ᵥ d.t22 *ᵥ co bX χ = co bX χ ⬝ᵥ d.t22 *ᵥ co bX y := by
      rw [dotProduct_mulVec_eq_transpose_mulVec, d.toricPeriodBlock_isSymm.eq]
    rw [co_add, mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, add_dotProduct, hs]
    ring
  have hτ : (N.τ y χ : ℂ) * d.fr (xy + xc) =
      Complex.exp (2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ d.t22 *ᵥ co bX y)) * d.fr xy * d.fr xc := by
    apply mul_left_cancel₀ (mul_ne_zero (N.ψ y).ne_zero (N.ψ χ).ne_zero)
    linear_combination (-(d.fr (xy + xc) : ℂ)) * hψ + h3 + hQ -
      Complex.exp (2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ d.t22 *ᵥ co bX y)) * Q χ * h1 -
      Complex.exp (2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ d.t22 *ᵥ co bX y)) * (N.ψ y : ℂ) * d.fr xy * h2
  have hF1 : (d.fr (xc + (p + xy)) : ℂ) = d.fr (xy + xc) * Complex.exp (2 * Real.pi * Complex.I * (cv (zP σ Nn) ⬝ᵥ xc)) *
      Complex.exp (2 * Real.pi * Complex.I * (cv (zP σ Nn) ⬝ᵥ xy)) * d.fr p := by
    rw [show xc + (p + xy) = (xy + xc) + p by abel, fr_shift, dotProduct_add, exp_two_pi_add]; ring
  have hF2 : (d.fr (p + xy) : ℂ) = d.fr xy * Complex.exp (2 * Real.pi * Complex.I * (cv (zP σ Nn) ⬝ᵥ xy)) * d.fr p := by
    rw [add_comm, fr_shift]
  have hE : Complex.exp (2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ (cv (tP σ M) + d.t12ᵀ *ᵥ cv (zP σ Nn) +
      d.t22 *ᵥ co bX y))) = Complex.exp (2 * Real.pi * Complex.I * (cv (zP σ Nn) ⬝ᵥ xc)) *
      Complex.exp (2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ d.t22 *ᵥ co bX y)) := by
    rw [dotProduct_add, dotProduct_add, exp_two_pi_add, exp_two_pi_add, exp_int_dot, _root_.one_mul,
      dotProduct_mulVec_eq_transpose_mulVec d.t12 (cv (zP σ Nn))]
  rw [hF1, hF2, hE]
  linear_combination Complex.exp (2 * Real.pi * Complex.I * (cv (zP σ Nn) ⬝ᵥ xc)) *
    Complex.exp (2 * Real.pi * Complex.I * (cv (zP σ Nn) ⬝ᵥ xy)) * d.fr p * hτ

end GlobalTheory.MBLow.Cl.Exp
end

namespace GlobalTheory.MBLow.Cl

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem exp_onto_torusExt : AllCD fun {N} {g'} {r} {g} {bX} d σ => (∀ Z, ∃! h, d.IsPt σ Z h) ∧ (∀ h, ∃ Z, d.IsPt σ Z h) ∧ (∀ Z Z' h h', d.IsPt σ Z h → d.IsPt σ Z' h' → d.IsPt σ (Z + Z') (h * h')) ∧ (∀ Z, d.IsPt σ Z 1 ↔ ∃ M Nn, tP σ Nn = 0 ∧ Z = perV (d.full σ 0) M Nn) ∧ ∀ M Nn, d.IsPt σ (perV (d.full σ 0) M Nn) (N.io (∑ l, tP σ Nn l • bX l)) :=
  fun _ _ _ _ _ d σ => ⟨Exp.existsUnique_isPt d σ, Exp.exists_isPt d σ, fun _ _ _ _ h h' => Exp.IsPt.add d σ h h',
    Exp.isPt_one_iff d σ, Exp.isPt_perV d σ⟩

end GlobalTheory.MBLow.Cl
