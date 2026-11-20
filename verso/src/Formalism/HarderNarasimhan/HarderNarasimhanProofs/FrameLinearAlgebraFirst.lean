import Mathlib
import Formalism.HarderNarasimhan.StatementFrameF
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
import Formalism.CorankShare.CorankShareProofs.SumNormSqLeHilbertSchmidt

noncomputable section

namespace Formalism.HN

namespace PframeLA1

open Finset Module LinearMap Formalism.CorankShareLayerCake.FR Formalism.CorankShareLayerCake.FR.Pgsn2pfrla
open scoped InnerProductSpace

/- English proof (translation)
Establish `hsw : √w ^ 2 = w` using `Real.sq_sqrt hw0`. Establish `hsX : √X ^ 2 = X` using `Real.sq_sqrt hX0`. Establish `hse0 : 0 ≤ √e` using `Real.sqrt_nonneg e`. Establish `hse : √e ≤ 1 / 2`. Rewrite using `[show (1 / 2 : ℝ) = √((1 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]`.

Conclude with `Real.sqrt_le_sqrt (by linarith)`. Establish `hRt : R ≤ 2 * t` using `by nlinarith [mul_le_mul_of_nonneg_left hse hR.le]`. Establish `htpos : 0 < t` using `by linarith`. Establish `hη : 0 ≤ η`. Establish `h1 : 0 ≤ η * t ^ 2 / D` using `le_trans hX0 hX`.

Establish `h2 : 0 ≤ η * t ^ 2`. Use `mul_nonneg h1 hD.le` as an intermediate fact. Rewrite `this` using `[div_mul_cancel₀ _ hD.ne']`. Then use the resulting hypothesis. Assume the negation of the conclusion as `hneg`. Use `push_neg at hneg`.

Establish `: η * t ^ 2 < 0` using `mul_neg_of_neg_of_pos hneg (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `hε4 : 1 / 4 ≤ ε`. Use polynomial arithmetic with `[mul_nonneg (by linarith : (0:ℝ) ≤ η + 4 * ε + 4 * √e - 1) hD.le]`. Use `push_neg at hε4`.

Use `set q := √(ε * e) with hq`. Establish `hq0 : 0 ≤ q` using `Real.sqrt_nonneg _`. Establish `hqe : q ≤ √e` using `Real.sqrt_le_sqrt (by nlinarith)`. Use `set y := D / t * √X with hy`. Establish `hy2 : y ^ 2 ≤ η * D`.

Establish `h1 : y ^ 2 = D ^ 2 * X / t ^ 2` using `by rw [hy, mul_pow, div_pow, hsX]; ring`. Rewrite using `[h1, div_le_iff₀ (by positivity)]`. Establish `h2 : X * D ≤ η * t ^ 2` using `(le_div_iff₀ hD).mp hX`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h2 hD.le]`. Establish `hyt : y * t = D * √X` using `by rw [hy]; field_simp`.

Establish `hDt : D * (t / D) = t` using `by field_simp`. Establish `hkey : t * (w - √w * y) ≤ t * (2 * D * (ε + q))`. Establish `h1 : t / D * w - √w * √X ≤ R * (ε + q)` using `by linarith`. Establish `h2 : t * w - D * (√w * √X) ≤ D * (R * (ε + q))`. Use `mul_le_mul_of_nonneg_left h1 hD.le` as an intermediate fact.

Establish `e1 : D * (t / D * w - √w * √X) = t * w - D * (√w * √X)`. Take the linear combination `w * hDt`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : D * (R * (ε + q)) ≤ D * (2 * t * (ε + q))`. Apply `mul_le_mul_of_nonneg_left _ hD.le` to reduce the goal to its premises.

Use the polynomial consequences of the given equalities and inequalities. Establish `e2 : t * (√w * y) = D * (√w * √X)` using `by linear_combination √w * hyt`. Use the polynomial consequences of the given equalities and inequalities. Establish `hmain : w - √w * y ≤ 2 * D * (ε + q)` using `le_of_mul_le_mul_left hkey htpos`. Establish `hamgm : √w * y ≤ (w + y ^ 2) / 2` using `by nlinarith [sq_nonneg (√w - y)]`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hqe hD.le]`.
-/
lemma final_real1 (D R w e ε η t X tW : ℝ) (hD : 0 < D) (hR : 0 < R) (he0 : 0 ≤ e) (he : e ≤ 1/4)
    (hε : 0 ≤ ε) (hw0 : 0 ≤ w) (hwD : w ≤ D) (ht : R * (1 - √e) ≤ t) (hX0 : 0 ≤ X)
    (hX : X ≤ η * t ^ 2 / D) (hlow : t / D * w - √w * √X ≤ tW)
    (hup : tW ≤ ε * R + R * √(ε * e)) : w ≤ (η + 4 * ε + 4 * √e) * D := by
  have hsw : √w ^ 2 = w := Real.sq_sqrt hw0
  have hsX : √X ^ 2 = X := Real.sq_sqrt hX0
  have hse0 : 0 ≤ √e := Real.sqrt_nonneg e
  have hse : √e ≤ 1 / 2 := by
    rw [show (1 / 2 : ℝ) = √((1 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hRt : R ≤ 2 * t := by nlinarith [mul_le_mul_of_nonneg_left hse hR.le]
  have htpos : 0 < t := by linarith
  have hη : 0 ≤ η := by
    have h1 : 0 ≤ η * t ^ 2 / D := le_trans hX0 hX
    have h2 : 0 ≤ η * t ^ 2 := by
      have := mul_nonneg h1 hD.le
      rwa [div_mul_cancel₀ _ hD.ne'] at this
    by_contra hneg
    push_neg at hneg
    have : η * t ^ 2 < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
    linarith
  by_cases hε4 : 1 / 4 ≤ ε
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ η + 4 * ε + 4 * √e - 1) hD.le]
  push_neg at hε4
  set q := √(ε * e) with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqe : q ≤ √e := Real.sqrt_le_sqrt (by nlinarith)
  set y := D / t * √X with hy
  have hy2 : y ^ 2 ≤ η * D := by
    have h1 : y ^ 2 = D ^ 2 * X / t ^ 2 := by rw [hy, mul_pow, div_pow, hsX]; ring
    rw [h1, div_le_iff₀ (by positivity)]
    have h2 : X * D ≤ η * t ^ 2 := (le_div_iff₀ hD).mp hX
    nlinarith [mul_le_mul_of_nonneg_left h2 hD.le]
  have hyt : y * t = D * √X := by rw [hy]; field_simp
  have hDt : D * (t / D) = t := by field_simp
  have hkey : t * (w - √w * y) ≤ t * (2 * D * (ε + q)) := by
    have h1 : t / D * w - √w * √X ≤ R * (ε + q) := by linarith
    have h2 : t * w - D * (√w * √X) ≤ D * (R * (ε + q)) := by
      have := mul_le_mul_of_nonneg_left h1 hD.le
      have e1 : D * (t / D * w - √w * √X) = t * w - D * (√w * √X) := by
        linear_combination w * hDt
      linarith
    have h3 : D * (R * (ε + q)) ≤ D * (2 * t * (ε + q)) := by
      apply mul_le_mul_of_nonneg_left _ hD.le
      nlinarith
    have e2 : t * (√w * y) = D * (√w * √X) := by linear_combination √w * hyt
    nlinarith
  have hmain : w - √w * y ≤ 2 * D * (ε + q) := le_of_mul_le_mul_left hkey htpos
  have hamgm : √w * y ≤ (w + y ^ 2) / 2 := by nlinarith [sq_nonneg (√w - y)]
  nlinarith [mul_le_mul_of_nonneg_left hqe hD.le]

end PframeLA1

open Finset Module LinearMap Formalism.CorankShareLayerCake.FR Formalism.CorankShareLayerCake.FR.Pgsn2pfrla PframeLA1
open scoped InnerProductSpace

/- English proof (translation)
Rewrite using `[hilbert_schmidt_eq_basis_sum A (stdOrthonormalBasis ℂ E)]`. Conclude with `Finset.sum_nonneg (fun m _ => sq_nonneg _)`.
-/
private lemma hs2_nonneg {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (A : E →ₗ[ℂ] F) : 0 ≤ hs2 A := by
  rw [hilbert_schmidt_eq_basis_sum A (stdOrthonormalBasis ℂ E)]
  exact Finset.sum_nonneg (fun m _ => sq_nonneg _)

/- English proof (translation)
Introduce `ι _ V _ _ _ H _ _ _ B c Nτ e η ε hc hd hK he0 he hη hQ hN`. Use `set W : Submodule ℂ H := (⨆ i, (Nτ i).map (B i))ᗮ with hW`. Establish `hwD : (finrank ℂ W : ℝ) ≤ (finrank ℂ H : ℝ)` using `by exact_mod_cast Submodule.finrank_le W`. Distinguish the cases in `hD0 : finrank ℂ H = 0`. Establish `h0 : finrank ℂ W = 0` using `by have := Submodule.finrank_le W; omega`.

Simplify using `[h0, hD0]`. Establish `hD : 0 < (finrank ℂ H : ℝ)` using `by exact_mod_cast Nat.pos_of_ne_zero hD0`. Establish `hR : 0 < ∑ i, (finrank ℂ (V i) : ℝ)` using `by rw [← Nat.cast_sum]; exact_mod_cast hd`. Establish `hnk : ∀ i, (finrank ℂ (Nτ i) : ℝ) ≤ finrank ℂ (V i)` using `fun i => by`. Conclude with `Submodule.finrank_le (Nτ i)` after adjusting the coercions.

Establish `hKnn : 0 ≤ ∑ i, ((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i))` using `Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (hnk i))`. Establish `hε : 0 ≤ ε`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `: ε * ∑ i, (finrank ℂ (V i) : ℝ) < 0` using `mul_neg_of_neg_of_pos h hR`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfull : ∀ i, (finrank ℂ (V i) : ℝ) - √(finrank ℂ (V i) : ℝ) * √(hs2 (frK (c i) (B i) - LinearMap.id)) ≤ c i * ∑ m, ‖B i (stdOrthonormalBasis ℂ (V i) m)‖ ^ 2`. Introduce `i`. Establish `h` using `fam_bound (c i) (B i) (stdOrthonormalBasis ℂ (V i)).orthonormal`. Simplify using `only [Fintype.card_fin] at h`.

Use `(abs_le.mp h).1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hCS1 : ∑ i, √(finrank ℂ (V i) : ℝ) * √(hs2 (frK (c i) (B i) - LinearMap.id)) ≤ (∑ i, (finrank ℂ (V i) : ℝ)) * √e`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.sqrt_mul he0]`.

Use `Real.mul_self_sqrt hR.le` as an intermediate fact. Take the linear combination `√e * this`. Establish `ht : (∑ i, (finrank ℂ (V i) : ℝ)) * (1 - √e) ≤ (LinearMap.trace ℂ H (frQ c B)).re`. Rewrite using `[tQ_eq c B]`. Establish `h2` using `Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hfull i)`.

Rewrite `h2` using `[Finset.sum_sub_distrib]`. Use polynomial arithmetic with `[hCS1]`. Use `set b := stdOrthonormalBasis ℂ W with hb`. Use `set g : Fin (finrank ℂ W) → H := fun l => (b l : H) with hgdef`. Apply the tactic sequence `have hg : Orthonormal ℂ g := b.orthonormal.comp_linearIsometry W.subtypeₗᵢ`.

Use `set tW : ℝ := ∑ l, (⟪g l, frQ c B (g l)⟫_ℂ).re with htWdef`. Establish `htW : tW = ∑ i, c i * ∑ l, ‖adjoint (B i) (g l)‖ ^ 2`. Rewrite using `[htWdef]`. Simplify using `only [re_inner_Q, Finset.mul_sum]`. Conclude with `Finset.sum_comm`.

Establish `hWi : ∀ i, c i * ∑ l, ‖adjoint (B i) (g l)‖ ^ 2 ≤ ((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i)) + √((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i)) * √(hs2 (frK (c i) (B i) - LinearMap.id))`. Introduce `i`. Establish `hperp : ∀ l, ∀ n ∈ Nτ i, ⟪B i n, g l⟫_ℂ = 0`. Introduce `l n hn`. Establish `hmem : B i n ∈ ⨆ j, (Nτ j).map (B j)` using `Submodule.mem_iSup_of_mem i (Submodule.mem_map_of_mem hn)`.

Conclude with `(Submodule.mem_orthogonal _ _).mp (b l).2 _ hmem`. Establish `h1` using `W_upper (B i) (Nτ i) hg hperp`. Apply the tactic sequence `have hf : Orthonormal ℂ (fun m => ((stdOrthonormalBasis ℂ (Nτ i)ᗮ m : (Nτ i)ᗮ) : V i)) := (stdOrthonormalBasis ℂ (Nτ i)ᗮ).orthonormal.comp_linearIsometry (Nτ i)ᗮ.subtypeₗᵢ`. Establish `h2` using `fam_bound (c i) (B i) hf`. Simplify using `only [Fintype.card_fin] at h2`.

Establish `hk : (finrank ℂ (Nτ i)ᗮ : ℝ) = finrank ℂ (V i) - finrank ℂ (Nτ i)`. Use `Submodule.finrank_add_finrank_orthogonal (Nτ i)` as an intermediate fact. Rewrite using `[eq_sub_iff_add_eq]`. Conclude with `(by omega : finrank ℂ (Nτ i)ᗮ + finrank ℂ (Nτ i) = finrank ℂ (V i))` after adjusting the coercions. Rewrite `h2` using `[hk]`.

Establish `h3` using `(abs_le.mp h2).2`. Establish `h4` using `mul_le_mul_of_nonneg_left h1 (hc i).le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hup : tW ≤ ε * (∑ i, (finrank ℂ (V i) : ℝ)) + (∑ i, (finrank ℂ (V i) : ℝ)) * √(ε * e)`. Rewrite using `[htW]`.

Establish `h1` using `Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hWi i)`. Rewrite `h1` using `[Finset.sum_add_distrib]`. Establish `hCS : ∑ i, √((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i)) * √(hs2 (frK (c i) (B i) - LinearMap.id)) ≤ (∑ i, (finrank ℂ (V i) : ℝ)) * √(ε * e)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.sqrt_mul (mul_nonneg hε hR.le), show ε * (∑ i, (finrank ℂ (V i) : ℝ)) * (e * ∑ i, (finrank ℂ (V i) : ℝ)) = ε * e * (∑ i, (finrank ℂ (V i) : ℝ)) ^ 2 by ring, Real.sqrt_mul (mul_nonneg hε he0), Real.sqrt_sq hR.le]`.

Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion. Use `set s : ℝ := (LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ) with hs`. Use `set A : H →ₗ[ℂ] H := frQ c B - (s : ℂ) • LinearMap.id with hA`. Establish `hlow : (LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ) * (finrank ℂ W : ℝ) - √(finrank ℂ W : ℝ) * √(hs2 A) ≤ tW`.

Establish `h` using `sum_re_inner_bound A hg`. Simplify using `only [Fintype.card_fin] at h`. Establish `h1 : ∀ l, ⟪g l, g l⟫_ℂ = 1` using `fun l => by`. Rewrite using `[inner_self_eq_norm_sq_to_K, hg.1 l]`. Simplify using the standard rewrite rules.

Establish `hsum : ∑ l, (⟪g l, A (g l)⟫_ℂ).re = tW - s * (finrank ℂ W : ℝ)`. Simplify using `only [hA, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, inner_sub_right, inner_smul_right, h1, mul_one, Complex.sub_re, Complex.ofReal_re, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, htWdef]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[hsum]`. Use `(abs_le.mp h).1` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hX : hs2 A ≤ η * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ)` using `by set u := stdOrthonormalBasis ℂ H with hu`. Establish `hterm : ∀ n, ‖A (u n)‖ ^ 2 = ‖frQ c B (u n)‖ ^ 2 - 2 * s * (⟪u n, frQ c B (u n)⟫_ℂ).re + s ^ 2`. Introduce `n`. Simplify using `only [hA, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]`.

Establish `hsym : (⟪frQ c B (u n), u n⟫_ℂ).re = (⟪u n, frQ c B (u n)⟫_ℂ).re` using `inner_re_symm (𝕜 := ℂ) _ _`. Rewrite using `[norm_sub_sq (𝕜 := ℂ), inner_smul_right, norm_smul, u.orthonormal.1 n]`. Simplify using `only [RCLike.re_to_complex, Complex.re_ofReal_mul, Complex.norm_real, Real.norm_eq_abs, mul_one, sq_abs, hsym]`. Expand and normalize the polynomial expressions, which then agree. Establish `htr : (LinearMap.trace ℂ H (frQ c B)).re = ∑ n, (⟪u n, frQ c B (u n)⟫_ℂ).re`.

Rewrite using `[LinearMap.trace_eq_sum_inner (frQ c B) u, Complex.re_sum]`. Establish `hT2 : (LinearMap.trace ℂ H (frQ c B ∘ₗ frQ c B)).re = ∑ n, ‖frQ c B (u n)‖ ^ 2` using `trace_frame_sq_eq_sum c B`. Rewrite using `[hilbert_schmidt_eq_basis_sum _ u]`. Simplify using `only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Rewrite using `[← htr, ← hT2]`.

Establish `hsD : s * (finrank ℂ H : ℝ) = (LinearMap.trace ℂ H (frQ c B)).re`. Rewrite using `[hs]`. Clear the denominators using the available nonvanishing facts. Establish `hst : (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) = s * (LinearMap.trace ℂ H (frQ c B)).re`. Rewrite using `[hs]`.

Clear the denominators using the available nonvanishing facts. Establish `hQ' : (LinearMap.trace ℂ H (frQ c B ∘ₗ frQ c B)).re ≤ (1 + η) * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ)` using `hQ`. Rewrite `hQ'` using `[show (1 + η) * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) = (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) + η * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) by ring]`. Establish `hDs2 : (finrank ℂ H : ℝ) * s ^ 2 = s * (LinearMap.trace ℂ H (frQ c B)).re`. Rewrite using `[← hsD]`.

Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `final_real1 _ _ _ e ε η _ _ tW hD hR he0 he hε (Nat.cast_nonneg _) hwD ht (hs2_nonneg _) hX hlow hup`.
-/
theorem frame_linear_algebra_first : FrameLA1 := by
  intro ι _ V _ _ _ H _ _ _ B c Nτ e η ε hc hd hK he0 he hη hQ hN
  set W : Submodule ℂ H := (⨆ i, (Nτ i).map (B i))ᗮ with hW
  have hwD : (finrank ℂ W : ℝ) ≤ (finrank ℂ H : ℝ) := by exact_mod_cast Submodule.finrank_le W
  by_cases hD0 : finrank ℂ H = 0
  · have h0 : finrank ℂ W = 0 := by have := Submodule.finrank_le W; omega
    simp [h0, hD0]
  have hD : 0 < (finrank ℂ H : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hD0
  have hR : 0 < ∑ i, (finrank ℂ (V i) : ℝ) := by rw [← Nat.cast_sum]; exact_mod_cast hd
  have hnk : ∀ i, (finrank ℂ (Nτ i) : ℝ) ≤ finrank ℂ (V i) := fun i => by
    exact_mod_cast Submodule.finrank_le (Nτ i)
  have hKnn : 0 ≤ ∑ i, ((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i)) :=
    Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (hnk i))
  have hε : 0 ≤ ε := by
    by_contra h
    push_neg at h
    have : ε * ∑ i, (finrank ℂ (V i) : ℝ) < 0 := mul_neg_of_neg_of_pos h hR
    linarith

  have hfull : ∀ i, (finrank ℂ (V i) : ℝ) - √(finrank ℂ (V i) : ℝ) * √(hs2 (frK (c i) (B i) - LinearMap.id))
      ≤ c i * ∑ m, ‖B i (stdOrthonormalBasis ℂ (V i) m)‖ ^ 2 := by
    intro i
    have h := fam_bound (c i) (B i) (stdOrthonormalBasis ℂ (V i)).orthonormal
    simp only [Fintype.card_fin] at h
    have := (abs_le.mp h).1
    linarith
  have hCS1 : ∑ i, √(finrank ℂ (V i) : ℝ) * √(hs2 (frK (c i) (B i) - LinearMap.id))
      ≤ (∑ i, (finrank ℂ (V i) : ℝ)) * √e := by
    calc _ ≤ √(∑ i, (finrank ℂ (V i) : ℝ)) * √(∑ i, hs2 (frK (c i) (B i) - LinearMap.id)) :=
          Real.sum_sqrt_mul_sqrt_le Finset.univ (fun i => Nat.cast_nonneg _) (fun i => hs2_nonneg _)
      _ ≤ √(∑ i, (finrank ℂ (V i) : ℝ)) * √(e * ∑ i, (finrank ℂ (V i) : ℝ)) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hK) (Real.sqrt_nonneg _)
      _ = (∑ i, (finrank ℂ (V i) : ℝ)) * √e := by
          rw [Real.sqrt_mul he0]
          have := Real.mul_self_sqrt hR.le
          linear_combination √e * this
  have ht : (∑ i, (finrank ℂ (V i) : ℝ)) * (1 - √e) ≤ (LinearMap.trace ℂ H (frQ c B)).re := by
    rw [tQ_eq c B]
    have h2 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hfull i)
    rw [Finset.sum_sub_distrib] at h2
    nlinarith [hCS1]

  set b := stdOrthonormalBasis ℂ W with hb
  set g : Fin (finrank ℂ W) → H := fun l => (b l : H) with hgdef
  have hg : Orthonormal ℂ g := b.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  set tW : ℝ := ∑ l, (⟪g l, frQ c B (g l)⟫_ℂ).re with htWdef
  have htW : tW = ∑ i, c i * ∑ l, ‖adjoint (B i) (g l)‖ ^ 2 := by
    rw [htWdef]
    simp only [re_inner_Q, Finset.mul_sum]
    exact Finset.sum_comm
  have hWi : ∀ i, c i * ∑ l, ‖adjoint (B i) (g l)‖ ^ 2 ≤
      ((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i)) +
        √((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i)) * √(hs2 (frK (c i) (B i) - LinearMap.id)) := by
    intro i
    have hperp : ∀ l, ∀ n ∈ Nτ i, ⟪B i n, g l⟫_ℂ = 0 := by
      intro l n hn
      have hmem : B i n ∈ ⨆ j, (Nτ j).map (B j) :=
        Submodule.mem_iSup_of_mem i (Submodule.mem_map_of_mem hn)
      exact (Submodule.mem_orthogonal _ _).mp (b l).2 _ hmem
    have h1 := W_upper (B i) (Nτ i) hg hperp
    have hf : Orthonormal ℂ (fun m => ((stdOrthonormalBasis ℂ (Nτ i)ᗮ m : (Nτ i)ᗮ) : V i)) :=
      (stdOrthonormalBasis ℂ (Nτ i)ᗮ).orthonormal.comp_linearIsometry (Nτ i)ᗮ.subtypeₗᵢ
    have h2 := fam_bound (c i) (B i) hf
    simp only [Fintype.card_fin] at h2
    have hk : (finrank ℂ (Nτ i)ᗮ : ℝ) = finrank ℂ (V i) - finrank ℂ (Nτ i) := by
      have := Submodule.finrank_add_finrank_orthogonal (Nτ i)
      rw [eq_sub_iff_add_eq]
      exact_mod_cast (by omega : finrank ℂ (Nτ i)ᗮ + finrank ℂ (Nτ i) = finrank ℂ (V i))
    rw [hk] at h2
    have h3 := (abs_le.mp h2).2
    have h4 := mul_le_mul_of_nonneg_left h1 (hc i).le
    linarith
  have hup : tW ≤ ε * (∑ i, (finrank ℂ (V i) : ℝ)) + (∑ i, (finrank ℂ (V i) : ℝ)) * √(ε * e) := by
    rw [htW]
    have h1 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hWi i)
    rw [Finset.sum_add_distrib] at h1
    have hCS : ∑ i, √((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i)) * √(hs2 (frK (c i) (B i) - LinearMap.id))
        ≤ (∑ i, (finrank ℂ (V i) : ℝ)) * √(ε * e) := by
      calc _ ≤ √(∑ i, ((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i))) *
              √(∑ i, hs2 (frK (c i) (B i) - LinearMap.id)) :=
            Real.sum_sqrt_mul_sqrt_le Finset.univ (fun i => sub_nonneg.mpr (hnk i))
              (fun i => hs2_nonneg _)
        _ ≤ √(ε * ∑ i, (finrank ℂ (V i) : ℝ)) * √(e * ∑ i, (finrank ℂ (V i) : ℝ)) :=
            mul_le_mul (Real.sqrt_le_sqrt hN) (Real.sqrt_le_sqrt hK) (Real.sqrt_nonneg _)
              (Real.sqrt_nonneg _)
        _ = (∑ i, (finrank ℂ (V i) : ℝ)) * √(ε * e) := by
            rw [← Real.sqrt_mul (mul_nonneg hε hR.le),
              show ε * (∑ i, (finrank ℂ (V i) : ℝ)) * (e * ∑ i, (finrank ℂ (V i) : ℝ))
                = ε * e * (∑ i, (finrank ℂ (V i) : ℝ)) ^ 2 by ring,
              Real.sqrt_mul (mul_nonneg hε he0), Real.sqrt_sq hR.le]
            ring
    linarith

  set s : ℝ := (LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ) with hs
  set A : H →ₗ[ℂ] H := frQ c B - (s : ℂ) • LinearMap.id with hA
  have hlow : (LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ) * (finrank ℂ W : ℝ)
      - √(finrank ℂ W : ℝ) * √(hs2 A) ≤ tW := by
    have h := sum_re_inner_bound A hg
    simp only [Fintype.card_fin] at h
    have h1 : ∀ l, ⟪g l, g l⟫_ℂ = 1 := fun l => by
      rw [inner_self_eq_norm_sq_to_K, hg.1 l]; simp
    have hsum : ∑ l, (⟪g l, A (g l)⟫_ℂ).re
        = tW - s * (finrank ℂ W : ℝ) := by
      simp only [hA, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, inner_sub_right,
        inner_smul_right, h1, mul_one, Complex.sub_re, Complex.ofReal_re, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, htWdef]
      ring
    rw [hsum] at h
    have := (abs_le.mp h).1
    linarith
  have hX : hs2 A
      ≤ η * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) := by
    set u := stdOrthonormalBasis ℂ H with hu
    have hterm : ∀ n, ‖A (u n)‖ ^ 2
        = ‖frQ c B (u n)‖ ^ 2 - 2 * s * (⟪u n, frQ c B (u n)⟫_ℂ).re + s ^ 2 := by
      intro n
      simp only [hA, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      have hsym : (⟪frQ c B (u n), u n⟫_ℂ).re = (⟪u n, frQ c B (u n)⟫_ℂ).re :=
        inner_re_symm (𝕜 := ℂ) _ _
      rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, norm_smul, u.orthonormal.1 n]
      simp only [RCLike.re_to_complex, Complex.re_ofReal_mul, Complex.norm_real, Real.norm_eq_abs,
        mul_one, sq_abs, hsym]
      ring
    have htr : (LinearMap.trace ℂ H (frQ c B)).re = ∑ n, (⟪u n, frQ c B (u n)⟫_ℂ).re := by
      rw [LinearMap.trace_eq_sum_inner (frQ c B) u, Complex.re_sum]
    have hT2 : (LinearMap.trace ℂ H (frQ c B ∘ₗ frQ c B)).re = ∑ n, ‖frQ c B (u n)‖ ^ 2 := trace_frame_sq_eq_sum c B
    rw [hilbert_schmidt_eq_basis_sum _ u]
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← htr, ← hT2]
    have hsD : s * (finrank ℂ H : ℝ) = (LinearMap.trace ℂ H (frQ c B)).re := by
      rw [hs]; field_simp
    have hst : (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ)
        = s * (LinearMap.trace ℂ H (frQ c B)).re := by
      rw [hs]; field_simp
    have hQ' : (LinearMap.trace ℂ H (frQ c B ∘ₗ frQ c B)).re
        ≤ (1 + η) * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) := hQ
    rw [show (1 + η) * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ)
        = (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ)
          + η * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) by ring] at hQ'
    have hDs2 : (finrank ℂ H : ℝ) * s ^ 2 = s * (LinearMap.trace ℂ H (frQ c B)).re := by
      rw [← hsD]; ring
    linarith
  exact final_real1 _ _ _ e ε η _ _ tW hD hR he0 he hε (Nat.cast_nonneg _) hwD ht
    (hs2_nonneg _) hX hlow hup

end Formalism.HN
