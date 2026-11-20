import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionDiscreteSeriesProperties
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionBracket

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.ComplexifiedAction

open PI.UpqRep GlobalTheory.DerivedAction

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

/- English proof (translation)
The claim follows from `(Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).1`.
-/
theorem gram_herm (k r : ℕ) : (Formalism.QuantumDeterminants.Hpk k r)ᴴ = Formalism.QuantumDeterminants.Hpk k r := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).1

/- English proof (translation)
The claim follows from `(Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).2.1`.
-/
theorem gram_sq (k r : ℕ) : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).2.1

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem lie_iff {X : Mx k r} : InLieHpk k r X ↔ Xᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * X = 0 := Iff.rfl

/- English proof (translation)
Establish `h` using `eq_neg_of_add_eq_zero_left (lie_iff.1 hX)`. Rewrite using `[Matrix.mul_assoc, h, Matrix.mul_neg, ← Matrix.mul_assoc, gram_sq, Matrix.one_mul]`.
-/
theorem adj_of_lie {X : Mx k r} (hX : InLieHpk k r X) :
    Formalism.QuantumDeterminants.Hpk k r * Xᴴ * Formalism.QuantumDeterminants.Hpk k r = -X := by
  have h := eq_neg_of_add_eq_zero_left (lie_iff.1 hX)
  rw [Matrix.mul_assoc, h, Matrix.mul_neg, ← Matrix.mul_assoc, gram_sq, Matrix.one_mul]

/- English proof (translation)
Rewrite using `[lie_iff]`. Establish `h2` using `congrArg (fun A => Formalism.QuantumDeterminants.Hpk k r * A) h`. Simplify using `only [← Matrix.mul_assoc, gram_sq, Matrix.one_mul, Matrix.mul_neg] at h2`. Rewrite using `[h2, neg_add_cancel]`.
-/
theorem lie_of_adj {X : Mx k r} (h : Formalism.QuantumDeterminants.Hpk k r * Xᴴ * Formalism.QuantumDeterminants.Hpk k r = -X) : InLieHpk k r X := by
  rw [lie_iff]
  have h2 := congrArg (fun A => Formalism.QuantumDeterminants.Hpk k r * A) h
  simp only [← Matrix.mul_assoc, gram_sq, Matrix.one_mul, Matrix.mul_neg] at h2
  rw [h2, neg_add_cancel]

/- English proof (translation)
Simplify using `only [conjTranspose_mul, conjTranspose_conjTranspose, gram_herm, ← Matrix.mul_assoc, gram_sq, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, gram_sq, Matrix.mul_one]`.
-/
theorem adj_adj (Y : Mx k r) :
    Formalism.QuantumDeterminants.Hpk k r * (Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r = Y := by
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, gram_herm, ← Matrix.mul_assoc, gram_sq, Matrix.one_mul]
  rw [Matrix.mul_assoc, gram_sq, Matrix.mul_one]

/- English proof (translation)
Apply `lie_of_adj` to reduce the goal to its premises. Establish `e : star (1 / 2 : ℂ) = 1 / 2` using `by simp`. Rewrite using `[conjTranspose_smul, conjTranspose_add, conjTranspose_neg, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, adj_adj, e]`. Use `module`.
-/
theorem lie_re (Y : Mx k r) :
    InLieHpk k r ((1 / 2 : ℂ) • (Y + -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) := by
  apply lie_of_adj
  have e : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [conjTranspose_smul, conjTranspose_add, conjTranspose_neg, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, adj_adj, e]
  module

/- English proof (translation)
Apply `lie_of_adj` to reduce the goal to its premises. Establish `e : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I))` using `by simp`. Rewrite using `[conjTranspose_smul, conjTranspose_sub, conjTranspose_neg, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, adj_adj, e]`. Use `module`.
-/
theorem lie_im (Y : Mx k r) :
    InLieHpk k r ((1 / (2 * Complex.I)) • (Y - -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) := by
  apply lie_of_adj
  have e : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by simp
  rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_neg, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, adj_adj, e]
  module

/- English proof (translation)
Use `⟨_, _, lie_re Y, lie_im Y, ?_⟩` and prove the remaining obligations. Establish `e : Complex.I * (1 / (2 * Complex.I)) = 1 / 2` using `by field_simp`. Rewrite using `[smul_smul, e]`. Use `module`.
-/
theorem exists_decomp (Y : Mx k r) : ∃ X₁ X₂, InLieHpk k r X₁ ∧ InLieHpk k r X₂ ∧ Y = X₁ + Complex.I • X₂ := by
  refine ⟨_, _, lie_re Y, lie_im Y, ?_⟩
  have e : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
  rw [smul_smul, e]
  module

/- English proof (translation)
Establish `e : star Complex.I = -Complex.I` using `by simp`. Rewrite using `[conjTranspose_add, conjTranspose_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, adj_of_lie h₁, adj_of_lie h₂, e]`. Use `module`.
-/
theorem adj_decomp {X₁ X₂ : Mx k r} (h₁ : InLieHpk k r X₁) (h₂ : InLieHpk k r X₂) :
    Formalism.QuantumDeterminants.Hpk k r * (X₁ + Complex.I • X₂)ᴴ * Formalism.QuantumDeterminants.Hpk k r = -X₁ + Complex.I • X₂ := by
  have e : star Complex.I = -Complex.I := by simp
  rw [conjTranspose_add, conjTranspose_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    adj_of_lie h₁, adj_of_lie h₂, e]
  module

/- English proof (translation)
Establish `e : (1 / (2 * Complex.I)) * (2 * Complex.I) = 1` using `by field_simp`. Establish `e1 : (1 / 2 : ℂ) • (X₁ + Complex.I • X₂ + -(-X₁ + Complex.I • X₂)) = X₁` using `by module`. Establish `e2 : (1 / (2 * Complex.I)) • (X₁ + Complex.I • X₂ - -(-X₁ + Complex.I • X₂)) = X₂`. Establish `: X₁ + Complex.I • X₂ - -(-X₁ + Complex.I • X₂) = (2 * Complex.I) • X₂` using `by module`. Rewrite using `[this, smul_smul, e, one_smul]`.

Unfold `Rep.dC`. Rewrite using `[adj_decomp h₁ h₂, e1, e2]`.
-/
theorem dC_decomp (R : Rep k r) {X₁ X₂ : Mx k r} (h₁ : InLieHpk k r X₁) (h₂ : InLieHpk k r X₂) (v : R.H) :
    R.dC (X₁ + Complex.I • X₂) v =
      dsig (k := k) (r := r) R.σ X₁ v + Complex.I • dsig (k := k) (r := r) R.σ X₂ v := by
  have e : (1 / (2 * Complex.I)) * (2 * Complex.I) = 1 := by field_simp
  have e1 : (1 / 2 : ℂ) • (X₁ + Complex.I • X₂ + -(-X₁ + Complex.I • X₂)) = X₁ := by module
  have e2 : (1 / (2 * Complex.I)) • (X₁ + Complex.I • X₂ - -(-X₁ + Complex.I • X₂)) = X₂ := by
    have : X₁ + Complex.I • X₂ - -(-X₁ + Complex.I • X₂) = (2 * Complex.I) • X₂ := by module
    rw [this, smul_smul, e, one_smul]
  unfold Rep.dC
  rw [adj_decomp h₁ h₂, e1, e2]

/- English proof (translation)
Rewrite using `[lie_iff]`. Simplify using the standard rewrite rules.
-/
theorem lie_zero : InLieHpk k r 0 := by rw [lie_iff]; simp

/- English proof (translation)
Apply `lie_of_adj` to reduce the goal to its premises. Rewrite using `[conjTranspose_add, Matrix.mul_add, Matrix.add_mul, adj_of_lie hX, adj_of_lie hY, neg_add]`.
-/
theorem lie_add {X Y : Mx k r} (hX : InLieHpk k r X) (hY : InLieHpk k r Y) : InLieHpk k r (X + Y) := by
  apply lie_of_adj
  rw [conjTranspose_add, Matrix.mul_add, Matrix.add_mul, adj_of_lie hX, adj_of_lie hY, neg_add]

/- English proof (translation)
Apply `lie_of_adj` to reduce the goal to its premises. Rewrite using `[conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, adj_of_lie hX, star_trivial, smul_neg]`.
-/
theorem lie_smul (a : ℝ) {X : Mx k r} (hX : InLieHpk k r X) : InLieHpk k r (a • X) := by
  apply lie_of_adj
  rw [conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, adj_of_lie hX, star_trivial, smul_neg]

/- English proof (translation)
Simplify using `using lie_smul (-1) hX`.
-/
theorem lie_neg {X : Mx k r} (hX : InLieHpk k r X) : InLieHpk k r (-X) := by
  simpa using lie_smul (-1) hX

/- English proof (translation)
Establish `h1` using `eq_neg_of_add_eq_zero_left (lie_iff.1 hX)`. Establish `h2` using `eq_neg_of_add_eq_zero_left (lie_iff.1 hY)`. Rewrite using `[lie_iff]`. Generalize the expression as in `Formalism.QuantumDeterminants.Hpk k r = H at h1 h2 ⊢`. Establish `e1 : (X * Y)ᴴ * H = H * (Y * X)`.

Rewrite using `[conjTranspose_mul, Matrix.mul_assoc, h1, Matrix.mul_neg, ← Matrix.mul_assoc, h2, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]`. Establish `e2 : (Y * X)ᴴ * H = H * (X * Y)`. Rewrite using `[conjTranspose_mul, Matrix.mul_assoc, h2, Matrix.mul_neg, ← Matrix.mul_assoc, h1, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]`. Rewrite using `[conjTranspose_sub, Matrix.sub_mul, e1, e2, Matrix.mul_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem lie_br {X Y : Mx k r} (hX : InLieHpk k r X) (hY : InLieHpk k r Y) : InLieHpk k r (X * Y - Y * X) := by
  have h1 := eq_neg_of_add_eq_zero_left (lie_iff.1 hX)
  have h2 := eq_neg_of_add_eq_zero_left (lie_iff.1 hY)
  rw [lie_iff]
  generalize Formalism.QuantumDeterminants.Hpk k r = H at h1 h2 ⊢
  have e1 : (X * Y)ᴴ * H = H * (Y * X) := by
    rw [conjTranspose_mul, Matrix.mul_assoc, h1, Matrix.mul_neg, ← Matrix.mul_assoc, h2, Matrix.neg_mul, neg_neg,
      Matrix.mul_assoc]
  have e2 : (Y * X)ᴴ * H = H * (X * Y) := by
    rw [conjTranspose_mul, Matrix.mul_assoc, h2, Matrix.mul_neg, ← Matrix.mul_assoc, h1, Matrix.neg_mul, neg_neg,
      Matrix.mul_assoc]
  rw [conjTranspose_sub, Matrix.sub_mul, e1, e2, Matrix.mul_sub]
  abel

/- English proof (translation)
Take `⟨L, hL⟩` from `exists_lin hv`. Rewrite using `[(hL _ hX).1, (hL _ hY).1, (hL _ (lie_add hX hY)).1, map_add]`.
-/
theorem dsig_add_left (R : Rep k r) {X Y : Mx k r} (hX : InLieHpk k r X) (hY : InLieHpk k r Y) {v : R.H}
    (hv : v ∈ R.sm) : dsig (k := k) (r := r) R.σ (X + Y) v =
      dsig (k := k) (r := r) R.σ X v + dsig (k := k) (r := r) R.σ Y v := by
  obtain ⟨L, hL⟩ := exists_lin hv
  rw [(hL _ hX).1, (hL _ hY).1, (hL _ (lie_add hX hY)).1, map_add]

/- English proof (translation)
Take `⟨L, hL⟩` from `exists_lin hv`. Rewrite using `[(hL _ hX).1, (hL _ (lie_smul a hX)).1, map_smul, Complex.coe_smul]`.
-/
theorem dsig_smul_left (R : Rep k r) (a : ℝ) {X : Mx k r} (hX : InLieHpk k r X) {v : R.H}
    (hv : v ∈ R.sm) : dsig (k := k) (r := r) R.σ (a • X) v = (a : ℂ) • dsig (k := k) (r := r) R.σ X v := by
  obtain ⟨L, hL⟩ := exists_lin hv
  rw [(hL _ hX).1, (hL _ (lie_smul a hX)).1, map_smul, Complex.coe_smul]

/- English proof (translation)
Simplify using `using dsig_smul_left R (-1) hX hv`.
-/
theorem dsig_neg_left (R : Rep k r) {X : Mx k r} (hX : InLieHpk k r X) {v : R.H}
    (hv : v ∈ R.sm) : dsig (k := k) (r := r) R.σ (-X) v = -dsig (k := k) (r := r) R.σ X v := by
  simpa using dsig_smul_left R (-1) hX hv

/- English proof (translation)
Establish `h` using `dC_decomp R hX lie_zero v`. Establish `h0` using `dsig_smul_left R 0 hX hv`. Rewrite `h0` using `[zero_smul]`. Rewrite `h` using `[smul_zero, add_zero, h0]`. Simplify using `using h`.
-/
theorem dC_lie (R : Rep k r) {X : Mx k r} (hX : InLieHpk k r X) {v : R.H} (hv : v ∈ R.sm) :
    R.dC X v = dsig (k := k) (r := r) R.σ X v := by
  have h := dC_decomp R hX lie_zero v
  have h0 := dsig_smul_left R 0 hX hv
  rw [zero_smul] at h0
  rw [smul_zero, add_zero, h0] at h
  simpa using h

/- English proof (translation)
Take `⟨Y₁, Y₂, h1, h2, rfl⟩` from `exists_decomp Y`. Take `⟨Z₁, Z₂, h3, h4, rfl⟩` from `exists_decomp Z`. Take `⟨x, y, rfl⟩ : ∃ x y : ℝ, a = x + y * Complex.I` from `⟨a.re, a.im, (Complex.re_add_im a).symm⟩`. Establish `e : ((x : ℂ) + y * Complex.I) • (Y₁ + Complex.I • Y₂) + (Z₁ + Complex.I • Z₂) = (x • Y₁ + (-y) • Y₂ + Z₁) + Complex.I • (y • Y₁ + x • Y₂ + Z₂)`. Simplify using `only [← Complex.coe_smul]`.

Use `push_cast`. Take the linear combination `(norm := module) (y * Complex.I_mul_I) • Y₂`. Establish `a1` using `lie_smul x h1`. Establish `a2` using `lie_smul (-y) h2`. Establish `a3` using `lie_smul y h1`.

Establish `a4` using `lie_smul x h2`. Rewrite using `[e, dC_decomp R (lie_add (lie_add a1 a2) h3) (lie_add (lie_add a3 a4) h4), dC_decomp R h1 h2, dC_decomp R h3 h4, dsig_add_left R (lie_add a1 a2) h3 hv, dsig_add_left R a1 a2 hv, dsig_add_left R (lie_add a3 a4) h4 hv, dsig_add_left R a3 a4 hv, dsig_smul_left R _ h1 hv, dsig_smul_l …`. Use `push_cast`. Take the linear combination `(norm := module) (-(y : ℂ) * Complex.I_mul_I) • dsig (k := k) (r := r) R.σ Y₂ v`.
-/
theorem dC_lin_left (R : Rep k r) (Y Z : Mx k r) (a : ℂ) {v : R.H} (hv : v ∈ R.sm) :
    R.dC (a • Y + Z) v = a • R.dC Y v + R.dC Z v := by
  obtain ⟨Y₁, Y₂, h1, h2, rfl⟩ := exists_decomp Y
  obtain ⟨Z₁, Z₂, h3, h4, rfl⟩ := exists_decomp Z
  obtain ⟨x, y, rfl⟩ : ∃ x y : ℝ, a = x + y * Complex.I := ⟨a.re, a.im, (Complex.re_add_im a).symm⟩
  have e : ((x : ℂ) + y * Complex.I) • (Y₁ + Complex.I • Y₂) + (Z₁ + Complex.I • Z₂) =
      (x • Y₁ + (-y) • Y₂ + Z₁) + Complex.I • (y • Y₁ + x • Y₂ + Z₂) := by
    simp only [← Complex.coe_smul]
    push_cast
    linear_combination (norm := module) (y * Complex.I_mul_I) • Y₂
  have a1 := lie_smul x h1
  have a2 := lie_smul (-y) h2
  have a3 := lie_smul y h1
  have a4 := lie_smul x h2
  rw [e, dC_decomp R (lie_add (lie_add a1 a2) h3) (lie_add (lie_add a3 a4) h4), dC_decomp R h1 h2,
    dC_decomp R h3 h4, dsig_add_left R (lie_add a1 a2) h3 hv, dsig_add_left R a1 a2 hv,
    dsig_add_left R (lie_add a3 a4) h4 hv, dsig_add_left R a3 a4 hv, dsig_smul_left R _ h1 hv,
    dsig_smul_left R _ h2 hv, dsig_smul_left R _ h1 hv, dsig_smul_left R _ h2 hv]
  push_cast
  linear_combination (norm := module) (-(y : ℂ) * Complex.I_mul_I) • dsig (k := k) (r := r) R.σ Y₂ v

/- English proof (translation)
Introduce `hK k r ε mu R hR`. Establish `hsm : ∀ {X}, InLieHpk k r X → ∀ {v}, v ∈ R.sm → dsig (k` using `k) (r := r) R.σ X v ∈ R.sm := fun hX _ hv => dsig_smooth hR.2 hX hv`. Establish `hlin : ∀ {X}, InLieHpk k r X → ∀ (a : ℂ) {v w}, v ∈ R.sm → w ∈ R.sm → dsig (k` using `k) (r := r) R.σ X (v + a • w) = dsig (k := k) (r := r) R.σ X v + a • dsig (k := k) (r := r) R.σ X w := by`. Introduce `X hX a v w hv hw`. Rewrite using `[dsig_add hX hv (R.smSub.smul_mem a hw), dsig_smul hX a hw]`.

Use `⟨fun Y v hv => ?_, fun Y a v hv w hw => ?_, fun Y Z a v hv => dC_lin_left R Y Z a hv, fun X hX v hv => dC_lie R hX hv, fun Y Z v hv => ?_, fun Y v hv w hw => ?_⟩` and prove the remaining obligations. Conclude with `R.smSub.add_mem (hsm (lie_re Y) hv) (R.smSub.smul_mem _ (hsm (lie_im Y) hv))`. Take `⟨Y₁, Y₂, h1, h2, rfl⟩` from `exists_decomp Y`. Rewrite using `[dC_decomp R h1 h2, dC_decomp R h1 h2, dC_decomp R h1 h2, add_comm (a • v) w, hlin h1 a hw hv, hlin h2 a hw hv]`. Use `module`.

Take `⟨Y₁, Y₂, h1, h2, rfl⟩` from `exists_decomp Y`. Take `⟨Z₁, Z₂, h3, h4, rfl⟩` from `exists_decomp Z`. Establish `e : (Y₁ + Complex.I • Y₂) * (Z₁ + Complex.I • Z₂) - (Z₁ + Complex.I • Z₂) * (Y₁ + Complex.I • Y₂) = ((Y₁ * Z₁ - Z₁ * Y₁) + -(Y₂ * Z₂ - Z₂ * Y₂)) + Complex.I • ((Y₁ * Z₂ - Z₂ * Y₁) + (Y₂ * Z₁ - Z₁ * Y₂))`. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]`. Take the linear combination `(norm := module) Complex.I_mul_I • (Y₂ * Z₂ - Z₂ * Y₂)`.

Establish `b` using `GlobalTheory.DerivedBracket.derived_action_bracket hK k r ε mu R hR`. Rewrite using `[e, dC_decomp R (lie_add (lie_br h1 h3) (lie_neg (lie_br h2 h4))) (lie_add (lie_br h1 h4) (lie_br h2 h3)), dsig_add_left R (lie_br h1 h3) (lie_neg (lie_br h2 h4)) hv, dsig_neg_left R (lie_br h2 h4) hv, dsig_add_left R (lie_br h1 h4) (lie_br h2 h3) hv, ← b _ _ h1 h3 v hv, ← b _ _ …`. Simplify using `only [dC_decomp R h1 h2, dC_decomp R h3 h4]`. Rewrite using `[hlin h1 _ (hsm h3 hv) (hsm h4 hv), hlin h2 _ (hsm h3 hv) (hsm h4 hv), hlin h3 _ (hsm h1 hv) (hsm h2 hv), hlin h4 _ (hsm h1 hv) (hsm h2 hv)]`. Take the linear combination `(norm := module) Complex.I_mul_I • (dsig (k := k) (r := r) R.σ Y₂ (dsig (k := k) (r := r) R.σ Z₂ v) - dsig (k := k) (r := r) R.σ Z₂ (dsig (k := k) (r := r) R.σ Y₂ v))`.

Take `⟨Y₁, Y₂, h1, h2, rfl⟩` from `exists_decomp Y`. Rewrite using `[adj_decomp h1 h2, dC_decomp R h1 h2, dC_decomp R (lie_neg h1) h2, dsig_neg_left R h1 hw, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, inner_neg_right, dsig_skew hR.2 h1 hv hw, dsig_skew hR.2 h2 hv hw, Complex.conj_I]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem complexified_action : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → (∀ Y, ∀ v ∈ R.sm, R.dC Y v ∈ R.sm) ∧ (∀ Y (a : ℂ), ∀ v ∈ R.sm, ∀ w ∈ R.sm, R.dC Y (a • v + w) = a • R.dC Y v + R.dC Y w) ∧ (∀ Y Z (a : ℂ), ∀ v ∈ R.sm, R.dC (a • Y + Z) v = a • R.dC Y v + R.dC Z v) ∧ (∀ X, PI.UpqRep.InLieHpk k r X → ∀ v ∈ R.sm, R.dC X v = PI.UpqRep.dsig (k := k) (r := r) R.σ X v) ∧ (∀ Y Z, ∀ v ∈ R.sm, R.dC Y (R.dC Z v) - R.dC Z (R.dC Y v) = R.dC (Y * Z - Z * Y) v) ∧ ∀ Y, ∀ v ∈ R.sm, ∀ w ∈ R.sm, ⟪R.dC Y v, w⟫_ℂ = ⟪v, R.dC ((Formalism.QuantumDeterminants.Hpk k r) * Yᴴ * (Formalism.QuantumDeterminants.Hpk k r)) w⟫_ℂ := by
  intro hK k r ε mu R hR
  have hsm : ∀ {X}, InLieHpk k r X → ∀ {v}, v ∈ R.sm → dsig (k := k) (r := r) R.σ X v ∈ R.sm :=
    fun hX _ hv => dsig_smooth hR.2 hX hv
  have hlin : ∀ {X}, InLieHpk k r X → ∀ (a : ℂ) {v w}, v ∈ R.sm → w ∈ R.sm →
      dsig (k := k) (r := r) R.σ X (v + a • w) =
        dsig (k := k) (r := r) R.σ X v + a • dsig (k := k) (r := r) R.σ X w := by
    intro X hX a v w hv hw
    rw [dsig_add hX hv (R.smSub.smul_mem a hw), dsig_smul hX a hw]
  refine ⟨fun Y v hv => ?_, fun Y a v hv w hw => ?_, fun Y Z a v hv => dC_lin_left R Y Z a hv,
    fun X hX v hv => dC_lie R hX hv, fun Y Z v hv => ?_, fun Y v hv w hw => ?_⟩
  · exact R.smSub.add_mem (hsm (lie_re Y) hv) (R.smSub.smul_mem _ (hsm (lie_im Y) hv))
  · obtain ⟨Y₁, Y₂, h1, h2, rfl⟩ := exists_decomp Y
    rw [dC_decomp R h1 h2, dC_decomp R h1 h2, dC_decomp R h1 h2, add_comm (a • v) w, hlin h1 a hw hv,
      hlin h2 a hw hv]
    module
  · obtain ⟨Y₁, Y₂, h1, h2, rfl⟩ := exists_decomp Y
    obtain ⟨Z₁, Z₂, h3, h4, rfl⟩ := exists_decomp Z
    have e : (Y₁ + Complex.I • Y₂) * (Z₁ + Complex.I • Z₂) - (Z₁ + Complex.I • Z₂) * (Y₁ + Complex.I • Y₂) =
        ((Y₁ * Z₁ - Z₁ * Y₁) + -(Y₂ * Z₂ - Z₂ * Y₂)) + Complex.I • ((Y₁ * Z₂ - Z₂ * Y₁) + (Y₂ * Z₁ - Z₁ * Y₂)) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
      linear_combination (norm := module) Complex.I_mul_I • (Y₂ * Z₂ - Z₂ * Y₂)
    have b := GlobalTheory.DerivedBracket.derived_action_bracket hK k r ε mu R hR
    rw [e, dC_decomp R (lie_add (lie_br h1 h3) (lie_neg (lie_br h2 h4))) (lie_add (lie_br h1 h4) (lie_br h2 h3)),
      dsig_add_left R (lie_br h1 h3) (lie_neg (lie_br h2 h4)) hv, dsig_neg_left R (lie_br h2 h4) hv,
      dsig_add_left R (lie_br h1 h4) (lie_br h2 h3) hv, ← b _ _ h1 h3 v hv, ← b _ _ h2 h4 v hv,
      ← b _ _ h1 h4 v hv, ← b _ _ h2 h3 v hv]
    simp only [dC_decomp R h1 h2, dC_decomp R h3 h4]
    rw [hlin h1 _ (hsm h3 hv) (hsm h4 hv), hlin h2 _ (hsm h3 hv) (hsm h4 hv), hlin h3 _ (hsm h1 hv) (hsm h2 hv),
      hlin h4 _ (hsm h1 hv) (hsm h2 hv)]
    linear_combination (norm := module) Complex.I_mul_I • (dsig (k := k) (r := r) R.σ Y₂ (dsig (k := k) (r := r) R.σ Z₂ v) -
      dsig (k := k) (r := r) R.σ Z₂ (dsig (k := k) (r := r) R.σ Y₂ v))
  · obtain ⟨Y₁, Y₂, h1, h2, rfl⟩ := exists_decomp Y
    rw [adj_decomp h1 h2, dC_decomp R h1 h2, dC_decomp R (lie_neg h1) h2, dsig_neg_left R h1 hw, inner_add_left,
      inner_add_right, inner_smul_left, inner_smul_right, inner_neg_right, dsig_skew hR.2 h1 hv hw,
      dsig_skew hR.2 h2 hv hw, Complex.conj_I]
    ring

end GlobalTheory.ComplexifiedAction
