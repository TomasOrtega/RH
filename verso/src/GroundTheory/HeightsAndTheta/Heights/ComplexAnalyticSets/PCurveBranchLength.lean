import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveBranchLength
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationLength
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchNormalisation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

/- English proof (translation)
Establish `htop : J.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) = ⊤` using `Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hg) (IsLocalization.map_units _ (⟨g, fun h ↦ hgq (RingHom.mem_ker.1 h)⟩ : (RingHom.ker (eval q)).primeCompl))`. Establish `hs` using `Ideal.Quotient.subsingleton_iff.2 htop`. Rewrite using `[localMult, dif_pos (isPrime_ker_eval q), Module.length_eq_zero_iff.2 hs]`. Both sides reduce to the same expression.
-/
theorem localMult_ker_eval_eq_zero {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    {g : MvPolynomial (Fin n) ℂ} (hg : g ∈ J) (hgq : eval q g ≠ 0) :
    localMult J (RingHom.ker (eval q)) = 0 := by
  have htop : J.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hg)
      (IsLocalization.map_units _ (⟨g, fun h ↦ hgq (RingHom.mem_ker.1 h)⟩ : (RingHom.ker (eval q)).primeCompl))
  have hs := Ideal.Quotient.subsingleton_iff.2 htop
  rw [localMult, dif_pos (isPrime_ker_eval q), Module.length_eq_zero_iff.2 hs]
  rfl

/- English proof (translation)
Introduce `n I u q m c ord hrad hcov hdisj hord`. Establish `hlin : ∀ x, eval x (linForm u) = linEval u x` using `fun x ↦ by simp [linForm, linEval]`. Establish `hq0 : ∀ b, linEval u q = 0 ↔ 0 < ord b`. Introduce `b`. Take `⟨H, -, hH, hF⟩` from `hord b`.

Establish `h0` using `hF 0 (Metric.mem_ball_self (c b).radius_pos)`. Simplify using `only [(c b).map_zero] at h0`. Rewrite using `[h0]`. Simplify using `[hH 0 (Metric.mem_ball_self (c b).radius_pos), Nat.pos_iff_ne_zero]`. Distinguish the cases in `hmain : linEval u q = 0 ∧ 0 < m`.

Use `swap`. Establish `hsum : ∑ b, ord b = 0` using `Finset.sum_eq_zero fun b _ ↦ by`. Assume the negation of the conclusion as `hb`. Conclude with `hmain ⟨(hq0 b).2 (Nat.pos_of_ne_zero hb), Fin.pos_iff_nonempty.2 ⟨b⟩⟩`. Rewrite using `[hsum]`.

Distinguish the cases in `hu : linEval u q = 0`. Establish `hm : m = 0` using `by by_contra hm; exact hmain ⟨hu, Nat.pos_of_ne_zero hm⟩`. Substitute `hm` using the available equality. Take `⟨N, hNq, hsub⟩` from `hcov`. Establish `hq : q ∉ zeroSet I` using `fun hq ↦ by simpa using hsub ⟨hq, mem_of_mem_nhds hNq⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨g, hg, hgq⟩ : ∃ g ∈ I, eval q g ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hq h`. Conclude with `localMult_ker_eval_eq_zero (Ideal.mem_sup_left hg) hgq`.

Conclude with `localMult_ker_eval_eq_zero (Ideal.mem_sup_right (Ideal.subset_span rfl)) (by rwa [hlin])`. Take `⟨hu0, hm⟩` from `hmain`. Establish `hpt : ∀ b, ∀ x ∈ (c b).image, linEval u x = 0 → x = q`. Introduce and unpack `b _ ⟨t, ht, rfl⟩ hx`. Take `⟨H, -, hH, hF⟩` from `hord b`.

Rewrite `hx` using `[show linEval u ((c b).toFun t) = t 0 ^ ord b * H t from hF t ht, mul_eq_zero]`. Establish `ht0 : t 0 = 0` using `hx.elim eq_zero_of_pow_eq_zero fun h ↦ absurd h (hH t ht)`. Establish `ht' : t = 0` using `funext fun i ↦ by rw [Subsingleton.elim i 0]; exact ht0`. Rewrite using `[ht', (c b).map_zero]`. Take `⟨hdim, hnzd, e, he⟩` from `hB n I q m c hrad hm hcov fun b b' hbb x hx ↦ hpt b x hx.1 (hdisj b b' hbb hx)`.

Establish `hordb : ∀ b, branchOrder (c b) (linForm u) = ord b` using `fun b ↦ branchOrder_eq_of_vanishesToOrder (c b) _ _ (by simpa only [hlin] using hord b)`. Establish `hL` using `hN n I q (linForm u) hrad hdim (hnzd _ fun b ↦ by rw [hordb b]; exact ENat.natCast_ne_top _)`. Rewrite `hL` using `[← finsum_comp_equiv e, finsum_eq_sum_of_fintype]`. Simplify using `only [(he _).1, mul_one, (he _).2, hordb] at hL`. Conclude with `hL` after adjusting the coercions.
-/
theorem CurveBranchLength.proof (hN : CurveNormalisationLength.Statement)
    (hB : BranchNormalisation.Statement) : CurveBranchLength.Statement := by
  intro n I u q m c ord hrad hcov hdisj hord
  have hlin : ∀ x, eval x (linForm u) = linEval u x := fun x ↦ by simp [linForm, linEval]
  have hq0 : ∀ b, linEval u q = 0 ↔ 0 < ord b := by
    intro b
    obtain ⟨H, -, hH, hF⟩ := hord b
    have h0 := hF 0 (Metric.mem_ball_self (c b).radius_pos)
    simp only [(c b).map_zero] at h0
    rw [h0]
    simp [hH 0 (Metric.mem_ball_self (c b).radius_pos), Nat.pos_iff_ne_zero]
  by_cases hmain : linEval u q = 0 ∧ 0 < m
  swap
  · have hsum : ∑ b, ord b = 0 := Finset.sum_eq_zero fun b _ ↦ by
      by_contra hb
      exact hmain ⟨(hq0 b).2 (Nat.pos_of_ne_zero hb), Fin.pos_iff_nonempty.2 ⟨b⟩⟩
    rw [hsum]
    by_cases hu : linEval u q = 0
    · have hm : m = 0 := by by_contra hm; exact hmain ⟨hu, Nat.pos_of_ne_zero hm⟩
      subst hm
      obtain ⟨N, hNq, hsub⟩ := hcov
      have hq : q ∉ zeroSet I := fun hq ↦ by simpa using hsub ⟨hq, mem_of_mem_nhds hNq⟩
      obtain ⟨g, hg, hgq⟩ : ∃ g ∈ I, eval q g ≠ 0 := by
        by_contra h
        push Not at h
        exact hq h
      exact localMult_ker_eval_eq_zero (Ideal.mem_sup_left hg) hgq
    · exact localMult_ker_eval_eq_zero (Ideal.mem_sup_right (Ideal.subset_span rfl)) (by rwa [hlin])
  obtain ⟨hu0, hm⟩ := hmain
  have hpt : ∀ b, ∀ x ∈ (c b).image, linEval u x = 0 → x = q := by
    rintro b _ ⟨t, ht, rfl⟩ hx
    obtain ⟨H, -, hH, hF⟩ := hord b
    rw [show linEval u ((c b).toFun t) = t 0 ^ ord b * H t from hF t ht, mul_eq_zero] at hx
    have ht0 : t 0 = 0 := hx.elim eq_zero_of_pow_eq_zero fun h ↦ absurd h (hH t ht)
    have ht' : t = 0 := funext fun i ↦ by rw [Subsingleton.elim i 0]; exact ht0
    rw [ht', (c b).map_zero]
  obtain ⟨hdim, hnzd, e, he⟩ := hB n I q m c hrad hm hcov
    fun b b' hbb x hx ↦ hpt b x hx.1 (hdisj b b' hbb hx)
  have hordb : ∀ b, branchOrder (c b) (linForm u) = ord b := fun b ↦
    branchOrder_eq_of_vanishesToOrder (c b) _ _ (by simpa only [hlin] using hord b)
  have hL := hN n I q (linForm u) hrad hdim (hnzd _ fun b ↦ by rw [hordb b]; exact ENat.natCast_ne_top _)
  rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype] at hL
  simp only [(he _).1, mul_one, (he _).2, hordb] at hL
  exact_mod_cast hL

end GroundTheory.Heights₂.Heights
