import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasProdMoebiusConvOfNormLe

open Ad3 Ad3.S LSeries
open scoped LSeries.notation ArithmeticFunction.Moebius

namespace GlobalTheory.CompanionTheory.SquareEuler

/- English proof (translation)
Break down `Nat.eq_zero_or_pos d with rfl | hd` into its components or cases. Simplify using `[RR]`. Rewrite using `[LSeries.term_of_ne_zero hd.ne', h1 n d hd, LSeries.convolution_def]`. Simplify using `only [Pi.mul_apply]`. Rewrite using `[Nat.sum_divisorsAntidiagonal' (f := fun a b => ((μ a : ℤ) : ℂ) * (NN n b : ℂ))]`.

Establish `hd0 : (d : ℂ) ≠ 0` using `by exact_mod_cast hd.ne'`. Establish `hp : (d : ℂ) ^ (-(s + 1)) = ((d : ℂ) ^ s)⁻¹ * (d : ℂ)⁻¹`. Rewrite using `[show -(s + 1) = -s + -1 by ring, Complex.cpow_add _ _ hd0, Complex.cpow_neg_one, Complex.cpow_neg]`. Rewrite using `[hp]`. Establish `hds : (d : ℂ) ^ s ≠ 0` using `by simp [hd0]`.

Clear the denominators using the available nonvanishing facts.
-/
lemma term_coeff_eq (h1 : N1) {M : ℕ} (c : DirichletCharacter ℂ M) (n : ℤ) (s : ℂ) (d : ℕ) :
    c (d : ZMod M) * RR n d * (d : ℂ) ^ (-(s + 1)) =
      LSeries.term (↗c * ((↗μ : ℕ → ℂ) ⍟ (fun e => (NN n e : ℂ)))) s d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [RR]
  · rw [LSeries.term_of_ne_zero hd.ne', h1 n d hd, LSeries.convolution_def]
    simp only [Pi.mul_apply]
    rw [Nat.sum_divisorsAntidiagonal' (f := fun a b => ((μ a : ℤ) : ℂ) * (NN n b : ℂ))]
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hp : (d : ℂ) ^ (-(s + 1)) = ((d : ℂ) ^ s)⁻¹ * (d : ℂ)⁻¹ := by
      rw [show -(s + 1) = -s + -1 by ring, Complex.cpow_add _ _ hd0, Complex.cpow_neg_one,
        Complex.cpow_neg]
    rw [hp]
    have hds : (d : ℂ) ^ s ≠ 0 := by simp [hd0]
    field_simp

/- English proof (translation)
Introduce `h1 h2 M _ c n s hs`. Use `set N : ℕ → ℂ := fun e => (NN n e : ℂ)`. Establish `hNle : ∀ d : ℕ, d ≠ 0 → ‖N d‖ ≤ d` using `fun d _ => by`. Simplify using `only [N, Complex.norm_natCast]`. Conclude with `(h2 n).2.1 d` after adjusting the coercions.

Establish `hNs : LSeriesSummable N s`. Use `LSeriesSummable_of_le_const_mul_rpow (x := 2) hs ⟨1, fun d hd => ?_⟩` and prove the remaining obligations. Establish `: (d : ℝ) ^ ((2 : ℝ) - 1) = d` using `by norm_num`. Rewrite using `[this, one_mul]`. Conclude with `hNle d hd`.

Establish `hμs : LSeriesSummable (↗μ : ℕ → ℂ) s` using `ArithmeticFunction.LSeriesSummable_moebius_iff.mpr (by linarith)`. Establish `hconv : LSeriesSummable ((↗μ : ℕ → ℂ) ⍟ N) s` using `hμs.convolution hNs`. Establish `hT` using `DirichletCharacter.LSeriesSummable_mul c hconv`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `hT.norm.congr fun d => by rw [term_coeff_eq h1 c n s d]`.

Establish `hD : Dn c n s = L (↗c * ((↗μ : ℕ → ℂ) ⍟ N)) s` using `tsum_congr (term_coeff_eq h1 c n s)`. Establish `hL : DirichletCharacter.LFunction (c ^ 2) (2 * s) = L ↗(c ^ 2) (2 * s)` using `DirichletCharacter.LFunction_eq_LSeries _ (by rw [Complex.mul_re]; norm_num; linarith)`. Rewrite using `[hD, hL, mul_comm]`. Use `hasProd_moebius_conv_of_norm_le c (N := N) (by simp [N, (h2 n).1]) ?_ hNle hs` and prove the remaining obligations. Introduce `a b hab`.

Simplify using `only [N, (h2 n).2.2.1 a b hab, Nat.cast_mul]`.
-/
theorem euler_coeff : N1 → N2 → A2 := by
  intro h1 h2 M _ c n s hs
  set N : ℕ → ℂ := fun e => (NN n e : ℂ)
  have hNle : ∀ d : ℕ, d ≠ 0 → ‖N d‖ ≤ d := fun d _ => by
    simp only [N, Complex.norm_natCast]; exact_mod_cast (h2 n).2.1 d
  have hNs : LSeriesSummable N s := by
    refine LSeriesSummable_of_le_const_mul_rpow (x := 2) hs ⟨1, fun d hd => ?_⟩
    have : (d : ℝ) ^ ((2 : ℝ) - 1) = d := by norm_num
    rw [this, one_mul]
    exact hNle d hd
  have hμs : LSeriesSummable (↗μ : ℕ → ℂ) s :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr (by linarith)
  have hconv : LSeriesSummable ((↗μ : ℕ → ℂ) ⍟ N) s := hμs.convolution hNs
  have hT := DirichletCharacter.LSeriesSummable_mul c hconv
  refine ⟨?_, ?_⟩
  · exact hT.norm.congr fun d => by rw [term_coeff_eq h1 c n s d]
  · have hD : Dn c n s = L (↗c * ((↗μ : ℕ → ℂ) ⍟ N)) s := tsum_congr (term_coeff_eq h1 c n s)
    have hL : DirichletCharacter.LFunction (c ^ 2) (2 * s) = L ↗(c ^ 2) (2 * s) :=
      DirichletCharacter.LFunction_eq_LSeries _ (by rw [Complex.mul_re]; norm_num; linarith)
    rw [hD, hL, mul_comm]
    refine hasProd_moebius_conv_of_norm_le c (N := N) (by simp [N, (h2 n).1]) ?_ hNle hs
    intro a b hab
    simp only [N, (h2 n).2.2.1 a b hab, Nat.cast_mul]

end GlobalTheory.CompanionTheory.SquareEuler
