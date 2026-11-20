import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IoInjective
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SkewOfCommute
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuadraticGelfandInvariantEqNegSumSqDefinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.HCCusp.QuadGelf

open GlobalTheory.UnitaryLieComplexification

section Frame

variable {n : ℕ}

def sg (e : Fin n → Bool) (a b : Fin n) : ℂ := if e a = e b then 1 else -1

def gv (e : Fin n → Bool) (p : Fin n × Fin n × Bool) : Matrix (Fin n) (Fin n) ℂ :=
  if p.2.2 then (1 / 2 : ℂ) • (single p.1 p.2.1 1 - sg e p.1 p.2.1 • single p.2.1 p.1 1)
  else (1 / (2 * Complex.I) : ℂ) • (single p.1 p.2.1 1 + sg e p.1 p.2.1 • single p.2.1 p.1 1)

def xv (e : Fin n → Bool) (p : Fin n × Fin n × Bool) : Matrix (Fin n) (Fin n) ℂ :=
  if e p.1 = e p.2.1 then 0 else gv e p

def yv (e : Fin n → Bool) (p : Fin n × Fin n × Bool) : Matrix (Fin n) (Fin n) ℂ :=
  if e p.1 = e p.2.1 then gv e p else 0

/- English proof (translation)
Establish an intermediate fact. Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules. Evaluate the numerical expressions. Separate the alternatives or extract the components of the hypothesis.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem pair_sq {A : Type} [Ring A] [Algebra ℂ A] (F G : A) {s : ℂ} (hs : s = 1 ∨ s = -1) :
    ((1 / 2 : ℂ) • (F - s • G)) * ((1 / 2 : ℂ) • (F - s • G)) +
      ((1 / (2 * Complex.I) : ℂ) • (F + s • G)) * ((1 / (2 * Complex.I) : ℂ) • (F + s • G)) =
    (-s) • ((1 / 2 : ℂ) • (F * G + G * F)) := by
  have h : (1 / (2 * Complex.I) : ℂ) * (1 / (2 * Complex.I)) = -(1 / 4) := by
    field_simp
    simp
    norm_num
  rcases hs with rfl | rfl
  · simp only [smul_mul_smul_comm, h, mul_add, add_mul, mul_sub, sub_mul, one_smul]
    module
  · simp only [smul_mul_smul_comm, h, mul_add, add_mul, mul_sub, sub_mul, neg_smul, one_smul, mul_neg, neg_mul,
      neg_neg]
    module

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.

Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sum_frame {A : Type} [Ring A] [Algebra ℂ A] (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A) (e : Fin n → Bool) :
    ∑ a, ∑ b, L (single a b 1) * L (single b a 1) =
      ∑ p, L (xv e p) * L (xv e p) - ∑ p, L (yv e p) * L (yv e p) := by
  have hT : ∀ a b, (L (xv e (a, b, true)) * L (xv e (a, b, true)) + L (xv e (a, b, false)) * L (xv e (a, b, false))) -
      (L (yv e (a, b, true)) * L (yv e (a, b, true)) + L (yv e (a, b, false)) * L (yv e (a, b, false))) =
      (1 / 2 : ℂ) • (L (single a b 1) * L (single b a 1) + L (single b a 1) * L (single a b 1)) := by
    intro a b
    by_cases c : e a = e b
    · have := pair_sq (L (single a b 1)) (L (single b a 1)) (s := 1) (Or.inl rfl)
      simp only [xv, yv, gv, c, sg, if_true, if_false, map_zero, mul_zero, map_smul, map_sub, map_add, Bool.false_eq_true]
      rw [add_zero, zero_sub, this]
      module
    · have := pair_sq (L (single a b 1)) (L (single b a 1)) (s := -1) (Or.inr rfl)
      simp only [xv, yv, gv, c, sg, if_true, if_false, map_zero, mul_zero, map_smul, map_sub, map_add, Bool.false_eq_true]
      rw [add_zero, sub_zero, this]
      module
  rw [← Finset.sum_sub_distrib, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  have hT' : ∀ a b, L (xv e (a, b, true)) * L (xv e (a, b, true)) - L (yv e (a, b, true)) * L (yv e (a, b, true)) +
      (L (xv e (a, b, false)) * L (xv e (a, b, false)) - L (yv e (a, b, false)) * L (yv e (a, b, false))) =
      (1 / 2 : ℂ) • (L (single a b 1) * L (single b a 1) + L (single b a 1) * L (single a b 1)) := by
    intro a b
    rw [← hT]
    abel
  simp only [hT', Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [Finset.sum_comm (f := fun a b => L (single b a 1) * L (single a b 1))]
  module

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem Jm_herm (e : Fin n → Bool) : (Formalism.REAL.Jm e)ᴴ = Formalism.REAL.Jm e := by
  unfold Formalism.REAL.Jm
  rw [diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : e a <;> simp [h]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem Jm_sq (e : Fin n → Bool) : Formalism.REAL.Jm e * Formalism.REAL.Jm e = 1 := by
  unfold Formalism.REAL.Jm
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  by_cases h : e a <;> simp [h]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Jm_unit (e : Fin n → Bool) : IsUnit (Formalism.REAL.Jm e).det := isUnit_det_of_right_inverse (Jm_sq e)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
-/
theorem cj_single (e : Fin n → Bool) (a b : Fin n) :
    cj (Formalism.REAL.Jm e) (single a b 1) = -(sg e a b • single b a 1) := by
  unfold GlobalTheory.UnitaryLieComplexification.cj
  rw [inv_eq_right_inv (Jm_sq e), conjTranspose_single, star_one]
  congr 1
  ext i j
  unfold Formalism.REAL.Jm
  rw [mul_diagonal, diagonal_mul, Matrix.smul_apply, single_apply]
  by_cases h : b = i ∧ a = j
  · obtain ⟨rfl, rfl⟩ := h
    by_cases h1 : e a <;> by_cases h2 : e b <;> simp [sg, h1, h2]
  · simp [h]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem gv_true (e : Fin n → Bool) (a b : Fin n) :
    gv e (a, b, true) = (1 / 2 : ℂ) • (single a b 1 + cj (Formalism.REAL.Jm e) (single a b 1)) := by
  rw [cj_single, gv, if_pos rfl, sub_eq_add_neg]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem gv_false (e : Fin n → Bool) (a b : Fin n) :
    gv e (a, b, false) = (1 / (2 * Complex.I) : ℂ) • (single a b 1 - cj (Formalism.REAL.Jm e) (single a b 1)) := by
  rw [cj_single, gv, if_neg (by simp), sub_neg_eq_add]

/- English proof (translation)
Extract witnesses or component facts from the available result. Split into cases according to the possible forms of the given data. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem gv_skew (e : Fin n → Bool) (p : Fin n × Fin n × Bool) :
    (gv e p)ᴴ * Formalism.REAL.Jm e + Formalism.REAL.Jm e * gv e p = 0 := by
  obtain ⟨a, b, c⟩ := p
  cases c
  · rw [gv_false]
    exact (imPart (Jm_herm e) (Jm_unit e) (single a b 1)).2
  · rw [gv_true]
    exact (rePart (Jm_herm e) (Jm_unit e) (single a b 1)).2

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Treat this case separately.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the chosen expression with an arbitrary variable. Replace the chosen expression with an arbitrary variable. Rewrite the conclusion using the stated equalities.

Replace the chosen expression with an arbitrary variable. Replace the chosen expression with an arbitrary variable. Substitute using the available equality. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations.

Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem mem_span_gv (e : Fin n → Bool) {Z : Matrix (Fin n) (Fin n) ℂ}
    (hZ : Zᴴ * Formalism.REAL.Jm e + Formalism.REAL.Jm e * Z = 0) : Z ∈ Submodule.span ℝ (Set.range (gv e)) := by
  let S := Submodule.span ℝ (Set.range (gv e))
  have key : ∀ W : Matrix (Fin n) (Fin n) ℂ, (1 / 2 : ℂ) • (W + cj (Formalism.REAL.Jm e) W) ∈ S := by
    intro W
    induction W using Matrix.induction_on' with
    | h_zero => simp [GlobalTheory.UnitaryLieComplexification.cj]
    | h_add p q hp hq =>
      have : (1 / 2 : ℂ) • (p + q + cj (Formalism.REAL.Jm e) (p + q)) =
          (1 / 2 : ℂ) • (p + cj (Formalism.REAL.Jm e) p) + (1 / 2 : ℂ) • (q + cj (Formalism.REAL.Jm e) q) := by
        rw [cj_add]
        module
      rw [this]
      exact S.add_mem hp hq
    | h_std_basis a b c =>
      have h1 : gv e (a, b, true) ∈ S := Submodule.subset_span ⟨_, rfl⟩
      have h2 : gv e (a, b, false) ∈ S := Submodule.subset_span ⟨_, rfl⟩
      have e0 : single a b c = c • (single a b 1 : Matrix (Fin n) (Fin n) ℂ) := by
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
      have hI : (1 / (2 * Complex.I) : ℂ) = -Complex.I / 2 := by
        field_simp
        simp
      have hc : c = c.re + c.im * Complex.I := (Complex.re_add_im c).symm
      have hs : star c = c.re - c.im * Complex.I := by
        apply Complex.ext <;> simp
      have e1 : (1 / 2 : ℂ) • (single a b c + cj (Formalism.REAL.Jm e) (single a b c)) =
          c.re • gv e (a, b, true) + (-c.im) • gv e (a, b, false) := by
        rw [e0, cj_smul, gv_true, gv_false]
        generalize cj (Formalism.REAL.Jm e) (single a b 1) = C
        generalize (single a b 1 : Matrix (Fin n) (Fin n) ℂ) = E
        rw [hs, hI]
        generalize c.re = x at *
        generalize c.im = y at *
        subst hc
        simp only [← Complex.coe_smul]
        push_cast
        match_scalars <;> ring
      rw [e1]
      exact S.add_mem (S.smul_mem _ h1) (S.smul_mem _ h2)
  have hz : cj (Formalism.REAL.Jm e) Z = Z := (mem_iff_cj (Jm_unit e) Z).1 hZ
  have := key Z
  rw [hz] at this
  have e2 : (1 / 2 : ℂ) • (Z + Z) = Z := by module
  rwa [e2] at this

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Establish an intermediate fact.

Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities.
-/
theorem conj_skew {J P Q Z : Matrix (Fin n) (Fin n) ℂ} (hPQ : P * Q = 1) (hZ : Zᴴ * J + J * Z = 0) :
    (Q * Z * P)ᴴ * (Pᴴ * J * P) + (Pᴴ * J * P) * (Q * Z * P) = 0 := by
  have h3 : Qᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, hPQ, conjTranspose_one]
  have e1 : (Q * Z * P)ᴴ * (Pᴴ * J * P) = Pᴴ * (Zᴴ * J) * P := by
    rw [conjTranspose_mul, conjTranspose_mul]
    calc Pᴴ * (Zᴴ * Qᴴ) * (Pᴴ * J * P) = Pᴴ * Zᴴ * (Qᴴ * Pᴴ) * J * P := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h3, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have e2 : (Pᴴ * J * P) * (Q * Z * P) = Pᴴ * (J * Z) * P := by
    calc _ = Pᴴ * J * (P * Q) * Z * P := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPQ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, hZ, Matrix.mul_zero, Matrix.zero_mul]

/- English proof (translation)
Consider separately whether the proposition holds or fails. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Split into cases according to the possible forms of the given data. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem yv_kLie (e : Fin n → Bool) (p : Fin n × Fin n × Bool) : IsKLie e (yv e p) := by
  by_cases c : e p.1 = e p.2.1
  · have hs : (yv e p)ᴴ = -yv e p := by
      obtain ⟨a, b, d⟩ := p
      have c' : e a = e b := c
      have hst : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
        simp [Complex.conj_I]
      cases d
      · simp only [yv, gv, c', sg, if_true, Bool.false_eq_true, if_false, one_smul, conjTranspose_smul, hst,
          conjTranspose_add, conjTranspose_single, star_one]
        rw [add_comm, neg_smul]
      · simp only [yv, gv, c', sg, if_true, one_smul, conjTranspose_smul, conjTranspose_sub, conjTranspose_single,
          star_one]
        simp only [star_div₀, star_one, star_ofNat]
        module
    refine ⟨hs, ?_⟩
    have h := gv_skew e p
    have hy : yv e p = gv e p := by simp [yv, c]
    rw [← hy, hs, neg_mul] at h
    exact (neg_add_eq_zero.1 h)
  · have hy : yv e p = 0 := by simp [yv, c]
    rw [hy]
    simp [IsKLie]

end Frame

end GlobalTheory.CompanionTheory.HCCusp.QuadGelf

namespace GlobalTheory.CompanionTheory.HCCusp

open QuadGelf

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Consider separately whether the proposition holds or fails.

Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Simplify to obtain the desired conclusion from the available facts.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Replace the chosen expression with an arbitrary variable.

Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails.

Prove the second alternative. Prove the first alternative. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.

Treat this case separately. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem quadGelf_frame : ∀ (D : D7) (θ : GlobalTheory.Mem.Th.InfF D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (e : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm e * P = gramAt D V τ → ∃ (n₁ n₂ : ℕ) (X : Fin n₁ → Matrix (Fin V.rank) (Fin V.rank) ℂ) (y : Fin n₂ → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ a, X a ∈ lieAt V τ) ∧ (∀ b, GlobalTheory.CompanionTheory.HCCusp.IsKLie e (y b)) ∧ (∀ Z ∈ lieAt V τ, Z ∈ Submodule.span ℝ (Set.range X ∪ Set.range fun b => P⁻¹ * y b * P)) ∧ ∀ f ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, gelf θ V τ 1 f = ∑ a, Rder θ V τ (X a) (Rder θ V τ (X a) f) - ∑ b, Rder θ V τ (P⁻¹ * y b * P) (Rder θ V τ (P⁻¹ * y b * P) f) := by
  intro D θ hθ V τ e P hP hJ
  classical
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  let q := Fintype.equivFin (Fin V.rank × Fin V.rank × Bool)
  have hconj : ∀ {Y : Matrix (Fin V.rank) (Fin V.rank) ℂ}, Yᴴ * Formalism.REAL.Jm e + Formalism.REAL.Jm e * Y = 0 →
      P⁻¹ * Y * P ∈ lieAt V τ := fun {Y} hY => by
    have := conj_skew h1 hY
    rw [hJ] at this
    exact this
  have hxl : ∀ p, P⁻¹ * xv e p * P ∈ lieAt V τ := fun p => hconj (by
    by_cases c : e p.1 = e p.2.1
    · simp [xv, c]
    · simpa [xv, c] using gv_skew e p)
  have hyl : ∀ p, P⁻¹ * yv e p * P ∈ lieAt V τ := fun p => hconj (by
    by_cases c : e p.1 = e p.2.1
    · simpa [yv, c] using gv_skew e p
    · simp [yv, c])
  refine ⟨_, _, fun i => P⁻¹ * xv e (q.symm i) * P, fun i => yv e (q.symm i), fun a => hxl _,
    fun b => yv_kLie e _, ?_, ?_⟩
  · intro Z hZ
    have hZ' : Zᴴ * (Pᴴ * Formalism.REAL.Jm e * P) + (Pᴴ * Formalism.REAL.Jm e * P) * Z = 0 := by
      rw [hJ]
      exact hZ
    have hb : (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm e * P) * P⁻¹ = Formalism.REAL.Jm e := by
      have h3 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
      calc _ = ((P⁻¹)ᴴ * Pᴴ) * Formalism.REAL.Jm e * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [h3, h1, Matrix.one_mul, Matrix.mul_one]
    have hW := conj_skew h2 hZ'
    rw [hb] at hW
    have hs := mem_span_gv e hW
    have hZe : Z = P⁻¹ * (P * Z * P⁻¹) * P := by
      calc Z = (P⁻¹ * P) * Z * (P⁻¹ * P) := by rw [h2, Matrix.one_mul, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [hZe]
    generalize P * Z * P⁻¹ = W at hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      refine Submodule.subset_span ?_
      by_cases c : e p.1 = e p.2.1
      · exact Or.inr ⟨q p, by simp [yv, c]⟩
      · exact Or.inl ⟨q p, by simp [xv, c]⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [Matrix.mul_add, Matrix.add_mul]
      exact add_mem hx hy
    | smul r x _ hx =>
      rw [Matrix.mul_smul, Matrix.smul_mul]
      exact Submodule.smul_mem _ _ hx
  · intro f hf
    let φ : GlobalTheory.Mem.AutSpace.SmFun θ V := ⟨f, hf⟩
    let R := GlobalTheory.Mem.RealTranslate.derEnd (V := V) hθ τ
    let L : Matrix (Fin V.rank) (Fin V.rank) ℂ →ₗ[ℂ] Module.End ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V) :=
      R ∘ₗ (LinearMap.mulRight ℂ P) ∘ₗ (LinearMap.mulLeft ℂ P⁻¹)
    have hL : ∀ Z, L Z = R (P⁻¹ * Z * P) := fun _ => rfl
    have hg : gelf θ V τ 1 f = ((∑ a, ∑ b, R (Matrix.single a b 1) * R (Matrix.single b a 1)) φ).1 := by
      rw [gelf, ← (finTwoArrowEquiv _).symm.sum_comp, Fintype.sum_prod_type]
      simp only [LinearMap.sum_apply, Submodule.coe_sum, Module.End.mul_apply]
      rfl
    have key : ∑ a, ∑ b, R (Matrix.single a b 1) * R (Matrix.single b a 1) =
        ∑ p, L (xv e p) * L (xv e p) - ∑ p, L (yv e p) * L (yv e p) := by
      rw [GlobalTheory.DefiniteUnitaryCasimir.casimir_conj R P hdet]
      exact sum_frame L e
    have hsq : ∀ {Y : Matrix (Fin V.rank) (Fin V.rank) ℂ}, P⁻¹ * Y * P ∈ lieAt V τ →
        ((L Y * L Y) φ).1 = Rder θ V τ (P⁻¹ * Y * P) (Rder θ V τ (P⁻¹ * Y * P) f) := fun {Y} hY => by
      rw [Module.End.mul_apply, hL, GlobalTheory.CuspLie.derEnd_coe hθ hY, GlobalTheory.CuspLie.derEnd_coe hθ hY]
    rw [hg, key, LinearMap.sub_apply, Submodule.coe_sub, LinearMap.sum_apply, LinearMap.sum_apply, Submodule.coe_sum,
      Submodule.coe_sum, ← q.symm.sum_comp, ← q.symm.sum_comp (fun p => ((L (yv e p) * L (yv e p)) φ).1)]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => hsq (hxl _)
    · exact Finset.sum_congr rfl fun i _ => hsq (hyl _)

end GlobalTheory.CompanionTheory.HCCusp
