import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfNormConst

noncomputable section

namespace GlobalTheory.FlatCore

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c r U x hU hF Z la s t`. Take `σ : c.F →+* ℂ` from `c.F.val.toRingHom`. Establish `hσ₀ : GoodEmb c (goodOf c σ)` using `goodEmb_goodOf c σ`. Use `set V := U (goodOf c σ) with hV`. Establish `hinv : s.inv ∈ suppOn Z`.

Establish `h` using `mul_mem_suppOn s.inv (idem_mem_suppOn Z)`. Rewrite `h` using `[mul_comm, s.idem_inv]`. Then use the resulting hypothesis. Establish `hg0 : t.sig * s.inv ∈ secZ Xo c 0`. Establish `h` using `mul_mem_secZ t.sig_mem s.inv_mem`. Rewrite `h` using `[add_neg_cancel]`. Then use the resulting hypothesis.

Establish `hgs : t.sig * s.inv ∈ suppOn Z` using `mul_mem_suppOn t.sig hinv`. Establish `hb : ∀ z ∈ framesOn V Z, ‖rdU V (t.sig * s.inv) z.1 z.2‖ = t.cInf σ / s.cInf σ`. Introduce `z hz`. Choose the witnesses or unpack the hypotheses as in `⟨K, hK⟩ : ∃ K : ℝ, ∀ f : Rul Xo c, homN V x (wtOf Dw la 0) f z = ‖rdU V f z.1 z.2‖ * K := by`. Use `⟨lieFacZ Dw x (wtOf Dw la 0) * (V.X z.1).pnorm (modelWt V (wtOf Dw la 0) z.1) (fun _ => 1) z.2, fun f => ?_⟩` and prove the remaining obligations.

Simplify using `only [homN, ptN, ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm, norm_one, one_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `ht : ‖rdU V t.sig z.1 z.2‖ * K = t.cInf σ`. Rewrite using `[← hK]`. Establish `h` using `t.norm_inf σ ▸ Set.mem_image_of_mem (homN V x (wtOf Dw la 0) t.sig) hz`.

Conclude with `h`. Establish `hs : ‖rdU V s.sig z.1 z.2‖ * K = s.cInf σ`. Rewrite using `[← hK]`. Establish `h` using `s.norm_inf σ ▸ Set.mem_image_of_mem (homN V x (wtOf Dw la 0) s.sig) hz`. Conclude with `h`.

Establish `hspos` using `s.cInf_pos σ`. Establish `hs0 : rdU V s.sig z.1 z.2 ≠ 0`. Introduce `h0`. Rewrite `hs` using `[h0, norm_zero, zero_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hread : ∀ f g : Rul Xo c, rdU V (f * g) z.1 z.2 = rdU V f z.1 z.2 * rdU V g z.1 z.2`. Introduce `f g`. Rewrite using `[AllWt.rdU_mul]`. Both sides reduce to the same expression. Establish `hidem : rdU V (idem Z) z.1 z.2 = 1`.

Establish `h` using `congrArg (fun f => rdU V f z.1 z.2) s.idem_sig`. Simplify using `only [hread] at h`. Conclude with `(mul_eq_right₀ hs0).mp h`. Establish `hone : rdU V s.sig z.1 z.2 * rdU V s.inv z.1 z.2 = 1`. Rewrite using `[← hread, s.mul_inv, hidem]`.

Rewrite using `[eq_div_iff hspos.ne', ← hs, hread, norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = t.cInf σ := by rw [ht, hone, norm_one, mul_one]`.

Take `⟨a, ha⟩` from `exists_eq_smul_idem V hσ₀ (hU _ hσ₀) hF hg0 hgs hb`. Establish `hts : t.sig = s.sig * (t.sig * s.inv)`. Combine the equalities or inequalities in the displayed calculation. Establish `hsi : s.sig * idem Z = s.sig` using `by rw [mul_comm]; exact s.idem_sig`. Establish `hta : t.sig = a • s.sig`.

Rewrite using `[hts, ha, mul_smul_comm, hsi]`. Distinguish the cases in `ha0 : a = 0`. Use `⟨1, one_ne_zero, ?_⟩` and prove the remaining obligations. Establish `ht0 : t.sig = 0` using `by rw [hta, ha0, zero_smul]`. Establish `hi0 : idem Z = 0` using `by rw [← t.mul_inv, ht0, zero_mul]`.

Establish `hs0 : s.sig = 0` using `by rw [← s.idem_sig, hi0, zero_mul]`. Rewrite using `[ht0, hs0, smul_zero]`. Conclude with `⟨a, ha0, hta⟩`.
-/
theorem archSec_exists_eq_smul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ)
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → FnAlgClosed Xo c →
    ∀ (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw) (s t : ArchSec U x Z la), ∃ a : c.F, a ≠ 0 ∧ t.sig = a • s.sig := by
  intro E _ _ _ H Dw l Xo c r U x hU hF Z la s t
  obtain σ : c.F →+* ℂ := c.F.val.toRingHom
  have hσ₀ : GoodEmb c (goodOf c σ) := goodEmb_goodOf c σ
  set V := U (goodOf c σ) with hV

  have hinv : s.inv ∈ suppOn Z := by
    have h := mul_mem_suppOn s.inv (idem_mem_suppOn Z)
    rwa [mul_comm, s.idem_inv] at h
  have hg0 : t.sig * s.inv ∈ secZ Xo c 0 := by
    have h := mul_mem_secZ t.sig_mem s.inv_mem
    rwa [add_neg_cancel] at h
  have hgs : t.sig * s.inv ∈ suppOn Z := mul_mem_suppOn t.sig hinv

  have hb : ∀ z ∈ framesOn V Z, ‖rdU V (t.sig * s.inv) z.1 z.2‖ = t.cInf σ / s.cInf σ := by
    intro z hz
    obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ f : Rul Xo c, homN V x (wtOf Dw la 0) f z = ‖rdU V f z.1 z.2‖ * K := by
      refine ⟨lieFacZ Dw x (wtOf Dw la 0) *
        (V.X z.1).pnorm (modelWt V (wtOf Dw la 0) z.1) (fun _ => 1) z.2, fun f => ?_⟩
      simp only [homN, ptN, ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm, norm_one, one_mul]
      ring
    have ht : ‖rdU V t.sig z.1 z.2‖ * K = t.cInf σ := by
      rw [← hK]
      have h := t.norm_inf σ ▸ Set.mem_image_of_mem (homN V x (wtOf Dw la 0) t.sig) hz
      exact h
    have hs : ‖rdU V s.sig z.1 z.2‖ * K = s.cInf σ := by
      rw [← hK]
      have h := s.norm_inf σ ▸ Set.mem_image_of_mem (homN V x (wtOf Dw la 0) s.sig) hz
      exact h
    have hspos := s.cInf_pos σ
    have hs0 : rdU V s.sig z.1 z.2 ≠ 0 := by
      intro h0
      rw [h0, norm_zero, zero_mul] at hs
      linarith
    have hread : ∀ f g : Rul Xo c, rdU V (f * g) z.1 z.2 = rdU V f z.1 z.2 * rdU V g z.1 z.2 := by
      intro f g
      rw [AllWt.rdU_mul]
      rfl
    have hidem : rdU V (idem Z) z.1 z.2 = 1 := by
      have h := congrArg (fun f => rdU V f z.1 z.2) s.idem_sig
      simp only [hread] at h
      exact (mul_eq_right₀ hs0).mp h
    have hone : rdU V s.sig z.1 z.2 * rdU V s.inv z.1 z.2 = 1 := by
      rw [← hread, s.mul_inv, hidem]
    rw [eq_div_iff hspos.ne', ← hs, hread, norm_mul]
    calc ‖rdU V t.sig z.1 z.2‖ * ‖rdU V s.inv z.1 z.2‖ * (‖rdU V s.sig z.1 z.2‖ * K)
        = ‖rdU V t.sig z.1 z.2‖ * K * ‖rdU V s.sig z.1 z.2 * rdU V s.inv z.1 z.2‖ := by
          rw [norm_mul]; ring
      _ = t.cInf σ := by rw [ht, hone, norm_one, mul_one]
  obtain ⟨a, ha⟩ := exists_eq_smul_idem V hσ₀ (hU _ hσ₀) hF hg0 hgs hb
  have hts : t.sig = s.sig * (t.sig * s.inv) := by
    calc t.sig = idem Z * t.sig := t.idem_sig.symm
      _ = s.sig * s.inv * t.sig := by rw [s.mul_inv]
      _ = s.sig * (t.sig * s.inv) := by ring
  have hsi : s.sig * idem Z = s.sig := by rw [mul_comm]; exact s.idem_sig
  have hta : t.sig = a • s.sig := by
    rw [hts, ha, mul_smul_comm, hsi]
  by_cases ha0 : a = 0
  · refine ⟨1, one_ne_zero, ?_⟩
    have ht0 : t.sig = 0 := by rw [hta, ha0, zero_smul]
    have hi0 : idem Z = 0 := by rw [← t.mul_inv, ht0, zero_mul]
    have hs0 : s.sig = 0 := by rw [← s.idem_sig, hi0, zero_mul]
    rw [ht0, hs0, smul_zero]
  · exact ⟨a, ha0, hta⟩

end GlobalTheory.FlatCore
