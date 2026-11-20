import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.CenterScalar

/- English proof (translation)
Use `open scoped Matrix.Norms.L2Operator in`. Establish `hall : ∀ M : Matrix (Fin n) (Fin n) ℂ, M * C = C * M`. Introduce `M`. Establish `hM : M ∈ Submodule.span ℂ (unitary (Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ))`. Rewrite using `[CStarAlgebra.span_unitary]`.

Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hM using Submodule.span_induction with`. Consider the case `mem U hU => exact h U hU.1`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [Matrix.add_mul, Matrix.mul_add, ha, hb]`.

Consider the case `smul c a _ ha => rw [Matrix.smul_mul, Matrix.mul_smul, ha]`. Take `⟨ζ, hζ⟩` from `Matrix.mem_range_scalar_of_commute_single (M := C) (fun i j _ => hall _)`. Conclude with `⟨ζ, by rw [← hζ, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩`.
-/
theorem scalar_of_comm_unitary {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 → U * C = C * U) : ∃ ζ : ℂ, C = ζ • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  open scoped Matrix.Norms.L2Operator in
  have hall : ∀ M : Matrix (Fin n) (Fin n) ℂ, M * C = C * M := by
    intro M
    have hM : M ∈ Submodule.span ℂ (unitary (Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ)) := by
      rw [CStarAlgebra.span_unitary]; trivial
    induction hM using Submodule.span_induction with
    | mem U hU => exact h U hU.1
    | zero => simp
    | add a b _ _ ha hb => rw [Matrix.add_mul, Matrix.mul_add, ha, hb]
    | smul c a _ ha => rw [Matrix.smul_mul, Matrix.mul_smul, ha]
  obtain ⟨ζ, hζ⟩ := Matrix.mem_range_scalar_of_commute_single (M := C) (fun i j _ => hall _)
  exact ⟨ζ, by rw [← hζ, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩

/- English proof (translation)
Take `⟨ε, hε, h1, h2⟩` from `hB`. Establish `hdet : (Matrix.diagonal (fun a => (ε a : ℂ))).det ≠ 0`. Rewrite using `[Matrix.det_diagonal]`. Use `Finset.prod_ne_zero_iff.2 fun a _ => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases hε a with h | h <;> simp [h.1]`.

Rewrite `hdet` using `[← h1, Matrix.det_mul, Matrix.det_mul]`. Establish `hBu : IsUnit B.det` using `(right_ne_zero_of_mul hdet).isUnit`. Establish `hG : G.det ≠ 0` using `right_ne_zero_of_mul (left_ne_zero_of_mul hdet)`. Establish `i1 : B⁻¹ * B = 1` using `Matrix.nonsing_inv_mul _ hBu`. Establish `i2 : B * B⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hBu`.

Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : ℂ, Bᴴ * G * B = c • (1 : Matrix (Fin n) (Fin n) ℂ) := by`. Establish `e : B⁻¹ * (s * B) = Matrix.diagonal (fun a => (ε a : ℂ))`. Rewrite using `[h2, ← Matrix.mul_assoc, i1, Matrix.one_mul]`. Break down `hs with rfl | rfl` into its components or cases. Conclude with `⟨1, by rw [h1, ← e, Matrix.one_mul, i1, one_smul]⟩`.

Conclude with `⟨-1, by rw [h1, ← e, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg, i1, neg_smul, one_smul]⟩`. Establish `hG' : (B⁻¹)ᴴ * (Bᴴ * G * B) * B⁻¹ = G`. Combine the equalities or inequalities in the displayed calculation. Take `⟨ζ, hζ⟩` from `scalar_of_comm_unitary (B⁻¹ * A * B) fun U hU => by`. Establish `k` using `h (B * U * B⁻¹) (by`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = (B⁻¹)ᴴ * (Bᴴ * G * B) * B⁻¹ := by`. Rewrite using `[hc, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU]`. Use `_ = G := hG')`.

Combine the equalities or inequalities in the displayed calculation. Establish `hAζ : A = ζ • (1 : Matrix (Fin n) (Fin n) ℂ)`. Combine the equalities or inequalities in the displayed calculation. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Conclude with `⟨1, norm_one, Subsingleton.elim _ _⟩`.

Use `⟨ζ, ?_, hAζ⟩ haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩` and prove the remaining obligations. Establish `hG0 : G ≠ 0` using `fun e => hG (by rw [e, Matrix.det_zero])`. Rewrite `hA` using `[hAζ, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]`. Establish `e : ζ * star ζ = 1`. Assume the negation of the conclusion as `hne`.

Apply `hG0` to reduce the goal to its premises. Establish `: (ζ * star ζ - 1) • G = 0` using `by rw [sub_smul, hA, one_smul, sub_self]`. Conclude with `(smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)`. Establish `e2 : ‖ζ‖ * ‖ζ‖ = 1` using `by simpa using congrArg norm e`. Use polynomial arithmetic with `[norm_nonneg ζ]`.
-/
theorem scalar_of_comm {n : ℕ} (G s B A : Matrix (Fin n) (Fin n) ℂ) (p : ℕ) (hs : s = 1 ∨ s = -1)
    (hB : IsONBasis G s B p) (hA : Aᴴ * G * A = G)
    (h : ∀ M : Matrix (Fin n) (Fin n) ℂ, Mᴴ * G * M = G → M * A = A * M) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ A = ζ • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  obtain ⟨ε, hε, h1, h2⟩ := hB
  have hdet : (Matrix.diagonal (fun a => (ε a : ℂ))).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
    rcases hε a with h | h <;> simp [h.1]
  rw [← h1, Matrix.det_mul, Matrix.det_mul] at hdet
  have hBu : IsUnit B.det := (right_ne_zero_of_mul hdet).isUnit
  have hG : G.det ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hdet)
  have i1 : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul _ hBu
  have i2 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hBu
  obtain ⟨c, hc⟩ : ∃ c : ℂ, Bᴴ * G * B = c • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have e : B⁻¹ * (s * B) = Matrix.diagonal (fun a => (ε a : ℂ)) := by
      rw [h2, ← Matrix.mul_assoc, i1, Matrix.one_mul]
    rcases hs with rfl | rfl
    · exact ⟨1, by rw [h1, ← e, Matrix.one_mul, i1, one_smul]⟩
    · exact ⟨-1, by rw [h1, ← e, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg, i1, neg_smul, one_smul]⟩
  have hG' : (B⁻¹)ᴴ * (Bᴴ * G * B) * B⁻¹ = G := by
    calc _ = (B * B⁻¹)ᴴ * G * (B * B⁻¹) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [i2]; simp
  obtain ⟨ζ, hζ⟩ := scalar_of_comm_unitary (B⁻¹ * A * B) fun U hU => by
    have k := h (B * U * B⁻¹) (by
      calc _ = (B⁻¹)ᴴ * (Uᴴ * (Bᴴ * G * B) * U) * B⁻¹ := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = (B⁻¹)ᴴ * (Bᴴ * G * B) * B⁻¹ := by
            rw [hc, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU]
        _ = G := hG')
    calc U * (B⁻¹ * A * B) = (B⁻¹ * B) * U * (B⁻¹ * A * B) := by rw [i1, Matrix.one_mul]
      _ = B⁻¹ * (B * U * B⁻¹ * A) * B := by simp only [Matrix.mul_assoc]
      _ = B⁻¹ * A * B * U * (B⁻¹ * B) := by rw [k]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [i1, Matrix.mul_one]
  have hAζ : A = ζ • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    calc A = (B * B⁻¹) * A * (B * B⁻¹) := by rw [i2, Matrix.one_mul, Matrix.mul_one]
      _ = B * (B⁻¹ * A * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hζ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, i2]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, norm_one, Subsingleton.elim _ _⟩
  · refine ⟨ζ, ?_, hAζ⟩
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hG0 : G ≠ 0 := fun e => hG (by rw [e, Matrix.det_zero])
    rw [hAζ, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one, smul_smul] at hA
    have e : ζ * star ζ = 1 := by
      by_contra hne
      apply hG0
      have : (ζ * star ζ - 1) • G = 0 := by rw [sub_smul, hA, one_smul, sub_self]
      exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
    have e2 : ‖ζ‖ * ‖ζ‖ = 1 := by simpa using congrArg norm e
    nlinarith [norm_nonneg ζ]

/- English proof (translation)
Introduce `D θ hθ S x hx z _ hz τ`. Take `⟨p, hp⟩` from `hx.onb τ`. Use `scalar_of_comm (gramAt D S τ) (x.s τ) (x.B τ) _ p (hx.pm τ) hp (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ S z τ) fun M hM => ?_` and prove the remaining obligations. Establish `ha` using `GlobalTheory.PointAtPlaceHom.atTau_spec hθ S τ (g := M) hM`. Establish `hc` using `congrArg (infMat D.sp.cm.sig S.gram (θ τ)) (Subgroup.mem_center_iff.1 hz (atTau θ S τ M))`.

Rewrite `hc` using `[GlobalTheory.PointAtPlaceHom.infMat_mul, GlobalTheory.PointAtPlaceHom.infMat_mul, ha.2.1]`. Conclude with `hc`.
-/
theorem center_scalar : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (S : HSp D) (x : DefSp S), x.Is → ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ∀ τ : D.what₂.Tau, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ compAt θ τ (Formalism.L2.Theta.mt S z) = ζ • (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) := by
  intro D θ hθ S x hx z _ hz τ
  obtain ⟨p, hp⟩ := hx.onb τ
  refine scalar_of_comm (gramAt D S τ) (x.s τ) (x.B τ) _ p (hx.pm τ) hp
    (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ S z τ) fun M hM => ?_
  have ha := GlobalTheory.PointAtPlaceHom.atTau_spec hθ S τ (g := M) hM
  have hc := congrArg (infMat D.sp.cm.sig S.gram (θ τ)) (Subgroup.mem_center_iff.1 hz (atTau θ S τ M))
  rw [GlobalTheory.PointAtPlaceHom.infMat_mul, GlobalTheory.PointAtPlaceHom.infMat_mul, ha.2.1] at hc
  exact hc

end GlobalTheory.CenterScalar

end
