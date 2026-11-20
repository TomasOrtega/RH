import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocCC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPhi
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

/- English proof (translation)
Rewrite using `[iteratedDeriv_succ', Real.deriv_log', iteratedDeriv_eq_iterate, iter_deriv_inv]`. Rewrite using `[norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_natCast]`. Use `congr 1`. Establish `e : (-1 - (m : ℤ)) = -((m + 1 : ℕ) : ℤ)` using `by push_cast; ring`. Rewrite using `[e, zpow_neg, zpow_natCast, norm_inv, norm_pow, Real.norm_of_nonneg hx.le]`.
-/
theorem lphi_log_deriv (m : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖iteratedDeriv (m + 1) Real.log x‖ = (m.factorial : ℝ) * (x ^ (m + 1))⁻¹ := by
  rw [iteratedDeriv_succ', Real.deriv_log', iteratedDeriv_eq_iterate, iter_deriv_inv]
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_natCast]
  congr 1
  have e : (-1 - (m : ℤ)) = -((m + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e, zpow_neg, zpow_natCast, norm_inv, norm_pow, Real.norm_of_nonneg hx.le]

/- English proof (translation)
Use `choose C hC using hld`. Use `set Φ : ℝ → ℝ := fun u => φ (Real.exp u) with hΦdef`. Establish `hΦ : ContDiff ℝ ∞ Φ` using `hφ`. Use `set s : Set ℝ := Set.Ioi a with hs`. Establish `hso : IsOpen s` using `isOpen_Ioi`.

Use `set K : ℝ := ∑ i ∈ Finset.range (j + 1), |C i| with hK`. Establish `hKi : ∀ i ≤ j, |C i| ≤ K` using `fun i hi => Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))`. Use `set M : ℝ := max 1 a⁻¹ with hM`. Establish `hM1 : 1 ≤ M` using `le_max_left _ _`. Use `set Dd : ℝ := (j.factorial : ℝ) * M with hDd`.

Use `⟨(j.factorial : ℝ) * K * Dd ^ j, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hx0 : 0 < x` using `ha.trans hx`. Establish `hxs : x ∈ s` using `hx`. Establish `hlogc : ContDiffOn ℝ ∞ Real.log s` using `Real.contDiffOn_log.mono fun y hy => ne_of_gt (ha.trans (show a < y from hy))`. Establish `hFdB` using `norm_iteratedFDerivWithin_comp_le (n := j) (N := ∞) (g := Φ) (f := Real.log) (t := Set.univ) hΦ.contDiffOn hlogc (by exact_mod_cast le_top) uniqueDiffOn_univ hso.uniqueDiffOn (Set.mapsTo_univ _ _) hxs (C := K) (D := Dd) (fun i hi => by`.

Rewrite using `[iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv]`. Use `hC i x hx0` as an intermediate fact. Unfold `LE.ld at this`. Rewrite using `[Real.norm_eq_abs]`. Conclude with `this.trans ((le_abs_self _).trans (hKi i hi)))`.

Use the proof step `(fun i hi1 hij => by`. Rewrite using `[iteratedFDerivWithin_of_isOpen i hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]`. Take `⟨m, rfl⟩ : ∃ m, i = m + 1` from `⟨i - 1, by omega⟩`. Rewrite using `[lphi_log_deriv m hx0]`. Establish `hxi : (x ^ (m + 1))⁻¹ ≤ M ^ (m + 1)`.

Rewrite using `[← inv_pow]`. Conclude with `pow_le_pow_left₀ (inv_nonneg.2 hx0.le) ((inv_anti₀ ha hx.le).trans (le_max_right _ _)) _`. Establish `hf1 : (m.factorial : ℝ) ≤ (j.factorial : ℝ)` using `by exact_mod_cast Nat.factorial_le (by omega)`. Establish `hj1 : (1 : ℝ) ≤ (j.factorial : ℝ)` using `by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero j)`. Establish `hjp : (j.factorial : ℝ) ≤ (j.factorial : ℝ) ^ (m + 1)` using `le_self_pow₀ hj1 (by omega)`.

Rewrite using `[hDd, mul_pow]`. Conclude with `mul_le_mul (hf1.trans hjp) hxi (by positivity) (by positivity))`. Rewrite `hFdB` using `[iteratedFDerivWithin_of_isOpen j hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]`. Establish `heq : (Φ ∘ Real.log) =ᶠ[nhds x] φ` using `by filter_upwards [isOpen_Ioi.mem_nhds hx0] with y hy`. Simplify using `[hΦdef, Real.exp_log (show (0 : ℝ) < y from hy)]`.

Rewrite using `[← heq.iteratedDeriv_eq]`. Conclude with `hFdB`.
-/
theorem lphi_deriv_bdd {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (hld : ∀ p, ∃ C, ∀ x, 0 < x → |LE.ld p φ x| ≤ C)
    {a : ℝ} (ha : 0 < a) (j : ℕ) : ∃ D : ℝ, ∀ x, a < x → ‖iteratedDeriv j φ x‖ ≤ D := by
  choose C hC using hld
  set Φ : ℝ → ℝ := fun u => φ (Real.exp u) with hΦdef
  have hΦ : ContDiff ℝ ∞ Φ := hφ
  set s : Set ℝ := Set.Ioi a with hs
  have hso : IsOpen s := isOpen_Ioi
  set K : ℝ := ∑ i ∈ Finset.range (j + 1), |C i| with hK
  have hKi : ∀ i ≤ j, |C i| ≤ K := fun i hi =>
    Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  set M : ℝ := max 1 a⁻¹ with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  set Dd : ℝ := (j.factorial : ℝ) * M with hDd
  refine ⟨(j.factorial : ℝ) * K * Dd ^ j, fun x hx => ?_⟩
  have hx0 : 0 < x := ha.trans hx
  have hxs : x ∈ s := hx
  have hlogc : ContDiffOn ℝ ∞ Real.log s :=
    Real.contDiffOn_log.mono fun y hy => ne_of_gt (ha.trans (show a < y from hy))
  have hFdB := norm_iteratedFDerivWithin_comp_le (n := j) (N := ∞) (g := Φ) (f := Real.log) (t := Set.univ)
    hΦ.contDiffOn hlogc (by exact_mod_cast le_top) uniqueDiffOn_univ hso.uniqueDiffOn (Set.mapsTo_univ _ _) hxs
    (C := K) (D := Dd) (fun i hi => by
      rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      have := hC i x hx0
      unfold LE.ld at this
      rw [Real.norm_eq_abs]
      exact this.trans ((le_abs_self _).trans (hKi i hi)))
    (fun i hi1 hij => by
      rw [iteratedFDerivWithin_of_isOpen i hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
      rw [lphi_log_deriv m hx0]
      have hxi : (x ^ (m + 1))⁻¹ ≤ M ^ (m + 1) := by
        rw [← inv_pow]
        exact pow_le_pow_left₀ (inv_nonneg.2 hx0.le)
          ((inv_anti₀ ha hx.le).trans (le_max_right _ _)) _
      have hf1 : (m.factorial : ℝ) ≤ (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_le (by omega)
      have hj1 : (1 : ℝ) ≤ (j.factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero j)
      have hjp : (j.factorial : ℝ) ≤ (j.factorial : ℝ) ^ (m + 1) := le_self_pow₀ hj1 (by omega)
      rw [hDd, mul_pow]
      exact mul_le_mul (hf1.trans hjp) hxi (by positivity) (by positivity))
  rw [iteratedFDerivWithin_of_isOpen j hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hFdB
  have heq : (Φ ∘ Real.log) =ᶠ[nhds x] φ := by
    filter_upwards [isOpen_Ioi.mem_nhds hx0] with y hy
    simp [hΦdef, Real.exp_log (show (0 : ℝ) < y from hy)]
  rw [← heq.iteratedDeriv_eq]
  exact hFdB

/- English proof (translation)
Use `set χ₀ : ℝ → ℝ := fun y => Real.smoothTransition (2 * y - 1) with hχ₀`. Establish `hχ : C6.IsCut0 χ₀`. Use `⟨Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const), ⟨1 / 2, by norm_num, fun y hy => Real.smoothTransition.zero_of_nonpos (by linarith)⟩, fun y hy => Real.smoothTransition.one_of_one_le (by linarith)⟩` and prove the remaining obligations. Take `⟨δ₀, hδ₀, hcut, -⟩` from `Formalism.FourierDecayAlt.P.JCTx6.Lev0.isCutG_div hχ hδ`. Use `set ψ : ℝ → ℝ := fun x => χ₀ (x / δ) with hψ`.

Establish `hε : 0 < δ₀ * δ` using `mul_pos hδ₀ hδ`. Establish `hψ1 : ∀ x, δ ≤ x → ψ x = 1` using `fun x hx => hχ.2.2 _ (by rw [le_div_iff₀ hδ]; linarith)`. Establish `hψ0 : ∀ x, x < δ₀ * δ → ψ x = 0` using `hcut.2.2`. Establish `hφc` using `smoothLog_contDiffOn hφ`. Use `⟨fun x => ψ x * φ x, δ₀ * δ, ⟨?_, ?_, fun x hx => by simp [hψ0 x hx]⟩, fun x hx => by simp [hψ1 x hx]⟩` and prove the remaining obligations.

Rewrite using `[contDiff_iff_contDiffAt]`. Introduce `x`. Distinguish the cases in `hx : x < δ₀ * δ`. Use `contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_ filter_upwards [isOpen_Iio.mem_nhds hx] with y hy` and prove the remaining obligations. Simplify using `[hψ0 y hy]`.

Establish `hx0 : 0 < x` using `lt_of_lt_of_le hε (not_lt.1 hx)`. Conclude with `hcut.1.contDiffAt.mul (hφc.contDiffAt (isOpen_Ioi.mem_nhds hx0))`. Introduce `q set a : ℝ := δ₀ * δ / 2 with ha`. Establish `ha0 : 0 < a` using `by positivity`. Use `choose cψ hcψ using hcut.2.1`.

Use `choose D hD using fun j => lphi_deriv_bdd hφ hld ha0 j`. Use `⟨∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * |cψ i| * |D (q - i)|, fun x => ?_⟩` and prove the remaining obligations. Establish `hS0 : 0 ≤ ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * |cψ i| * |D (q - i)|` using `Finset.sum_nonneg fun i _ => by positivity`. Distinguish the cases in `hx : x < δ₀ * δ`. Establish `e : (fun x => ψ x * φ x) =ᶠ[nhds x] fun _ => (0 : ℝ)` using `by filter_upwards [isOpen_Iio.mem_nhds hx] with y hy`.

Simplify using `[hψ0 y hy]`. Rewrite using `[e.iteratedDeriv_eq]`. Simplify using `only [iteratedDeriv_const]`. Apply the tactic sequence `split_ifs <;> simpa using hS0`. Establish `hxa : a < x` using `by linarith [not_lt.1 hx] set s : Set ℝ := Set.Ioi a with hs`.

Establish `hso : IsOpen s` using `isOpen_Ioi`. Establish `hxs : x ∈ s` using `hxa`. Establish `hφs : ContDiffOn ℝ ∞ φ s` using `hφc.mono fun y hy => ha0.trans (show a < y from hy)`. Establish `hL` using `norm_iteratedFDerivWithin_mul_le (N := ∞) (hcut.1.contDiffOn (s := s)) hφs hso.uniqueDiffOn hxs (n := q) (by exact_mod_cast le_top)`. Rewrite `hL` using `[iteratedFDerivWithin_of_isOpen q hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]`.

Use `hL.trans (Finset.sum_le_sum fun i hi => ?_)` and prove the remaining obligations. Rewrite using `[iteratedFDerivWithin_of_isOpen i hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedFDerivWithin_of_isOpen (q - i) hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]`. Establish `h1 : ‖iteratedDeriv i ψ x‖ ≤ |cψ i|` using `(hcψ i x).trans (le_abs_self _)`. Establish `h2 : ‖iteratedDeriv (q - i) φ x‖ ≤ |D (q - i)|` using `(hD (q - i) x hxa).trans (le_abs_self _)`. Conclude with `mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (norm_nonneg _) (by positivity)`.
-/
theorem lphi_cut {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (hld : ∀ p, ∃ C, ∀ x, 0 < x → |LE.ld p φ x| ≤ C)
    {δ : ℝ} (hδ : 0 < δ) : ∃ (h : ℝ → ℝ) (ε' : ℝ), U.IsCutG ε' h ∧ ∀ x, δ ≤ x → h x = φ x := by
  set χ₀ : ℝ → ℝ := fun y => Real.smoothTransition (2 * y - 1) with hχ₀
  have hχ : C6.IsCut0 χ₀ := by
    refine ⟨Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const),
      ⟨1 / 2, by norm_num, fun y hy => Real.smoothTransition.zero_of_nonpos (by linarith)⟩,
      fun y hy => Real.smoothTransition.one_of_one_le (by linarith)⟩
  obtain ⟨δ₀, hδ₀, hcut, -⟩ := Formalism.FourierDecayAlt.P.JCTx6.Lev0.isCutG_div hχ hδ
  set ψ : ℝ → ℝ := fun x => χ₀ (x / δ) with hψ
  have hε : 0 < δ₀ * δ := mul_pos hδ₀ hδ
  have hψ1 : ∀ x, δ ≤ x → ψ x = 1 := fun x hx =>
    hχ.2.2 _ (by rw [le_div_iff₀ hδ]; linarith)
  have hψ0 : ∀ x, x < δ₀ * δ → ψ x = 0 := hcut.2.2
  have hφc := smoothLog_contDiffOn hφ
  refine ⟨fun x => ψ x * φ x, δ₀ * δ, ⟨?_, ?_, fun x hx => by simp [hψ0 x hx]⟩,
    fun x hx => by simp [hψ1 x hx]⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x < δ₀ * δ
    · refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
      simp [hψ0 y hy]
    · have hx0 : 0 < x := lt_of_lt_of_le hε (not_lt.1 hx)
      exact hcut.1.contDiffAt.mul (hφc.contDiffAt (isOpen_Ioi.mem_nhds hx0))
  · intro q
    set a : ℝ := δ₀ * δ / 2 with ha
    have ha0 : 0 < a := by positivity
    choose cψ hcψ using hcut.2.1
    choose D hD using fun j => lphi_deriv_bdd hφ hld ha0 j
    refine ⟨∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * |cψ i| * |D (q - i)|, fun x => ?_⟩
    have hS0 : 0 ≤ ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * |cψ i| * |D (q - i)| :=
      Finset.sum_nonneg fun i _ => by positivity
    by_cases hx : x < δ₀ * δ
    · have e : (fun x => ψ x * φ x) =ᶠ[nhds x] fun _ => (0 : ℝ) := by
        filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
        simp [hψ0 y hy]
      rw [e.iteratedDeriv_eq]
      simp only [iteratedDeriv_const]
      split_ifs <;> simpa using hS0
    · have hxa : a < x := by linarith [not_lt.1 hx]
      set s : Set ℝ := Set.Ioi a with hs
      have hso : IsOpen s := isOpen_Ioi
      have hxs : x ∈ s := hxa
      have hφs : ContDiffOn ℝ ∞ φ s := hφc.mono fun y hy => ha0.trans (show a < y from hy)
      have hL := norm_iteratedFDerivWithin_mul_le (N := ∞) (hcut.1.contDiffOn (s := s)) hφs hso.uniqueDiffOn
        hxs (n := q) (by exact_mod_cast le_top)
      rw [iteratedFDerivWithin_of_isOpen q hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hL
      refine hL.trans (Finset.sum_le_sum fun i hi => ?_)
      rw [iteratedFDerivWithin_of_isOpen i hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
        iteratedFDerivWithin_of_isOpen (q - i) hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      have h1 : ‖iteratedDeriv i ψ x‖ ≤ |cψ i| := (hcψ i x).trans (le_abs_self _)
      have h2 : ‖iteratedDeriv (q - i) φ x‖ ≤ |D (q - i)| := (hD (q - i) x hxa).trans (le_abs_self _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (norm_nonneg _) (by positivity)

/- English proof (translation)
Use `⟨2, by norm_num, ?_⟩` and prove the remaining obligations. Introduce `E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top Cb A₀ hB v φ Bg A J hφ hld hBg hJ hFF`. Use `⟨hFF, fun δ hδ => ?_⟩` and prove the remaining obligations. Take `⟨F, hF1, hF2, hF3⟩` from `hJ.2 δ hδ`. Take `⟨h, ε', hcut, hhφ⟩` from `lphi_cut hφ hld hδ`.

Take `⟨hck, hcc⟩` from `gcut_graded (T v).base.z (T v).base.z' h ε' hcut (A := A) hBg hF1 hF2`. Use `⟨fun g => ((h (GfP S T v g) : ℝ) : ℂ) • F g, hck, hcc, fun x hx hG => ?_⟩` and prove the remaining obligations. Establish `e1 : (fun g => ((h (GfP S T v g) : ℝ) : ℂ) • F g) = D.cutF (T v).base h F 1`. Use function extensionality and compare the values at `g`. Simplify using `[D.cutF, GfP]`.

Rewrite using `[e1, Formalism.FourierDecayAlt.P.JCTx2.JF_cutF, div_one, ← hF3 x hx hG]`. Simplify using `only [mulG]`. Unfold `GfP at hG`. Rewrite using `[hhφ _ hG]`. Both sides reduce to the same expression.
-/
theorem local_phi_transfer_holds : JALocPhi := by
  refine ⟨2, by norm_num, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top Cb A₀ hB v φ Bg A J hφ hld hBg hJ hFF
  refine ⟨hFF, fun δ hδ => ?_⟩
  obtain ⟨F, hF1, hF2, hF3⟩ := hJ.2 δ hδ
  obtain ⟨h, ε', hcut, hhφ⟩ := lphi_cut hφ hld hδ
  obtain ⟨hck, hcc⟩ := gcut_graded (T v).base.z (T v).base.z' h ε' hcut (A := A) hBg hF1 hF2
  refine ⟨fun g => ((h (GfP S T v g) : ℝ) : ℂ) • F g, hck, hcc, fun x hx hG => ?_⟩
  have e1 : (fun g => ((h (GfP S T v g) : ℝ) : ℂ) • F g) = D.cutF (T v).base h F 1 := by
    funext g; simp [D.cutF, GfP]
  rw [e1, Formalism.FourierDecayAlt.P.JCTx2.JF_cutF, div_one, ← hF3 x hx hG]
  simp only [mulG]
  unfold GfP at hG
  rw [hhφ _ hG]
  rfl

end Formalism.FourierDecayAlt.P.CutMP.JA

end
