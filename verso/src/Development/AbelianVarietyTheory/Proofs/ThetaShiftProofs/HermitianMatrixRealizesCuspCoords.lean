import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsSt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsPfA
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsPfB
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceEqSumRingHom

open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt
open scoped ComplexConjugate

namespace GlobalTheory.HermExpo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj`. Consider the case `exact _root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj`. Consider the case `(apply _root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj ..)`.
-/
theorem sum_re_eq_trace (X : Data E r) (x : E) :
    ∑ τ : X.Ψ, (τ.1 (x + cc x)).re = ((Algebra.trace ℚ E x : ℚ) : ℝ) := by
  first
  | exact @_root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj
  | exact _root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj
  | (apply _root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj <;> assumption)
  | (intros; apply _root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj ..)

/- English proof (translation)
Use `X.ξ0_ne` as an intermediate fact. Apply the tactic sequence `rcases X.κ0_xi with h | h <;> rw [h] <;> simpa using this`.
-/
theorem kappa_ne (X : Data E r) : X.κ0 ≠ 0 := by
  have := X.ξ0_ne
  rcases X.κ0_xi with h | h <;> rw [h] <;> simpa using this

/- English proof (translation)
Establish `h : ∀ g : E →ₗ[ℚ] ℚ, ∃ c : E, ∀ y, g y = Algebra.trace ℚ E (c * y)`. Introduce `g`. Use `⟨((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).symm g, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[← Algebra.traceForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]`. Use `choose c hc using fun a b : Fin ρ => h (f ∘ₗ Matrix.singleLinearMap ℚ a b)`.

Use `⟨Matrix.of c, fun β => ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [Matrix.matrix_eq_sum_single β]`. Simplify using `only [map_sum, Matrix.of_apply, ← hc]`. Both sides reduce to the same expression.
-/
theorem exists_trace_repr (f : Matrix (Fin ρ) (Fin ρ) E →ₗ[ℚ] ℚ) :
    ∃ c : Matrix (Fin ρ) (Fin ρ) E, ∀ β,
      f β = Algebra.trace ℚ E (∑ a, ∑ b, c a b * β a b) := by
  have h : ∀ g : E →ₗ[ℚ] ℚ, ∃ c : E, ∀ y, g y = Algebra.trace ℚ E (c * y) := by
    intro g
    refine ⟨((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).symm g, fun y => ?_⟩
    rw [← Algebra.traceForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]
  choose c hc using fun a b : Fin ρ => h (f ∘ₗ Matrix.singleLinearMap ℚ a b)
  refine ⟨Matrix.of c, fun β => ?_⟩
  conv_lhs => rw [Matrix.matrix_eq_sum_single β]
  simp only [map_sum, Matrix.of_apply, ← hc]
  rfl

/- English proof (translation)
Establish `hli : LinearIndependent ℚ (zBas X cu)` using `(LinearIndependent.iff_fractionRing ℤ ℚ).1 hb.1`. Choose the witnesses or unpack the hypotheses as in `⟨f, hf⟩ : ∃ f : Matrix (Fin ρ) (Fin ρ) E →ₗ[ℚ] ℚ, ∀ k, f (zBas X cu k) = m k := by`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective (Finsupp.linearCombination ℚ (zBas X cu)) (LinearMap.ker_eq_bot.2 hli)`. Use `⟨Finsupp.linearCombination ℚ (fun k => (m k : ℚ)) ∘ₗ g, fun k => ?_⟩` and prove the remaining obligations. Establish `h1` using `LinearMap.congr_fun hg (Finsupp.single k 1)`.

Simplify using `only [LinearMap.comp_apply, Finsupp.linearCombination_single, one_smul, LinearMap.id_apply] at h1`. Simplify using `[h1]`. Take `⟨c, hc⟩` from `exists_trace_repr f`. Establish `hκ : X.κ0 / 2 ≠ 0` using `div_ne_zero (kappa_ne X) two_ne_zero`. Establish `hκc : cc (X.κ0 / 2) = -(X.κ0 / 2)`.

Use `maxCuspsA_kappa_cc X` as an intermediate fact. Unfold `cc at this ⊢`. Rewrite using `[map_div₀, this, map_ofNat, neg_div]`. Establish `hcc : ∀ y : E, cc (cc y) = y` using `fun y => IsCMField.complexConj_apply_apply E y`. Establish `hmul : ∀ y z : E, cc (y * z) = cc y * cc z` using `fun y z => map_mul _ y z`.

Establish `hadd : ∀ y z : E, cc (y + z) = cc y + cc z` using `fun y z => map_add _ y z`. Establish `hsub : ∀ y z : E, cc (y - z) = cc y - cc z` using `fun y z => map_sub _ y z`. Use `⟨Matrix.of fun a b => (X.κ0 / 2) * (c a b - cc (c b a)), fun a b => ?_, fun k => ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.of_apply, hmul, hsub, hκc, hcc]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hs` using `zBas_skew X cu ⟨_, hb⟩ k`. Establish `hx : Matrix.trace ((Matrix.of fun a b => (X.κ0 / 2) * (c a b - cc (c b a))).transpose * zBas X cu k) / (X.κ0 / 2) = (∑ a, ∑ b, c a b * zBas X cu k a b) + cc (∑ a, ∑ b, c a b * zBas X cu k a b)`. Establish `h1 : cc (∑ a, ∑ b, c a b * zBas X cu k a b) = ∑ a, ∑ b, -(cc (c b a) * zBas X cu k a b)`. Rewrite using `[Finset.sum_comm]`. Unfold `cc`.

Simplify using `only [map_sum, map_mul]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[show IsCMField.complexConj E (zBas X cu k b a) = cc (zBas X cu k b a) from rfl, hs, mul_neg]`. Rewrite using `[h1, div_eq_iff hκ, ← Finset.sum_add_distrib]`. Simplify using `only [← Finset.sum_add_distrib, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Unfold `phZ prE`. Rewrite using `[hx, sum_re_eq_trace, ← hc, hf]`.

Simplify using the standard rewrite rules.
-/
theorem exists_herm_phase (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ)
    (X : Data E r) (cu : CuspFD X ρ) (hb : IsZBasis X cu (zBas X cu))
    (m : Fin (nZ X ρ) → ℤ) :
    ∃ χ : Matrix (Fin ρ) (Fin ρ) E, IsHermE χ ∧ ∀ k, phZ X cu χ k = m k := by
  have hli : LinearIndependent ℚ (zBas X cu) := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hb.1
  obtain ⟨f, hf⟩ : ∃ f : Matrix (Fin ρ) (Fin ρ) E →ₗ[ℚ] ℚ, ∀ k, f (zBas X cu k) = m k := by
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective
      (Finsupp.linearCombination ℚ (zBas X cu)) (LinearMap.ker_eq_bot.2 hli)
    refine ⟨Finsupp.linearCombination ℚ (fun k => (m k : ℚ)) ∘ₗ g, fun k => ?_⟩
    have h1 := LinearMap.congr_fun hg (Finsupp.single k 1)
    simp only [LinearMap.comp_apply, Finsupp.linearCombination_single, one_smul,
      LinearMap.id_apply] at h1
    simp [h1]
  obtain ⟨c, hc⟩ := exists_trace_repr f
  have hκ : X.κ0 / 2 ≠ 0 := div_ne_zero (kappa_ne X) two_ne_zero
  have hκc : cc (X.κ0 / 2) = -(X.κ0 / 2) := by
    have := maxCuspsA_kappa_cc X
    unfold cc at this ⊢
    rw [map_div₀, this, map_ofNat, neg_div]
  have hcc : ∀ y : E, cc (cc y) = y := fun y => IsCMField.complexConj_apply_apply E y
  have hmul : ∀ y z : E, cc (y * z) = cc y * cc z := fun y z => map_mul _ y z
  have hadd : ∀ y z : E, cc (y + z) = cc y + cc z := fun y z => map_add _ y z
  have hsub : ∀ y z : E, cc (y - z) = cc y - cc z := fun y z => map_sub _ y z
  refine ⟨Matrix.of fun a b => (X.κ0 / 2) * (c a b - cc (c b a)), fun a b => ?_, fun k => ?_⟩
  · simp only [Matrix.of_apply, hmul, hsub, hκc, hcc]
    ring
  · have hs := zBas_skew X cu ⟨_, hb⟩ k
    have hx : Matrix.trace ((Matrix.of fun a b => (X.κ0 / 2) * (c a b - cc (c b a))).transpose *
        zBas X cu k) / (X.κ0 / 2) =
        (∑ a, ∑ b, c a b * zBas X cu k a b) + cc (∑ a, ∑ b, c a b * zBas X cu k a b) := by
      have h1 : cc (∑ a, ∑ b, c a b * zBas X cu k a b) =
          ∑ a, ∑ b, -(cc (c b a) * zBas X cu k a b) := by
        rw [Finset.sum_comm]
        unfold cc
        simp only [map_sum, map_mul]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [show IsCMField.complexConj E (zBas X cu k b a) = cc (zBas X cu k b a) from rfl, hs,
          mul_neg]
      rw [h1, div_eq_iff hκ, ← Finset.sum_add_distrib]
      simp only [← Finset.sum_add_distrib, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.of_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    unfold phZ prE
    rw [hx, sum_re_eq_trace, ← hc, hf]
    simp

end GlobalTheory.HermExpo

/- English proof (translation)
The claim follows from `GlobalTheory.HermExpo.exists_herm_phase`.
-/
theorem GlobalTheory.exists_isHermE_phZ_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : CuspFD X ρ), IsZBasis X cu (zBas X cu) → ∀ m : Fin (nZ X ρ) → ℤ, ∃ χ : Matrix (Fin ρ) (Fin ρ) E, IsHermE χ ∧ ∀ k, phZ X cu χ k = m k :=
  GlobalTheory.HermExpo.exists_herm_phase
