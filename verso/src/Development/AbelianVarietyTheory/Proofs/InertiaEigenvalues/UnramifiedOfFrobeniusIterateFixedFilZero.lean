import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemUnramifiedOfFrobeniusIterateFixedFil
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedExtFixedFieldFrobeniusPowDegreeStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

/- English proof (translation)
Introduce `l _ P AI T h hh c hc hF`. Take `⟨E, ω, hEle, hEdim, hEfix, -⟩` from `GlobalTheory.T.unramifiedExt_fixedField_frobeniusPow_degree l h hh`. Establish `hK0 : K0 E = E.1` using `inf_eq_left.2 hEle`. Establish `hdim : Module.finrank ℚ_[l] ↥(K0 E) = h` using `by rw [hK0]; exact hEdim`. Establish `hper : Function.IsPeriodicPt (⇑P.φB) h c` using `hc`.

Establish `hall : ∀ j : ℕ, P.ιB ((⇑P.φB)^[j] c) ∈ (P.PD E).Fil 0`. Introduce `j`. Establish `hj : (⇑P.φB)^[j] c = (⇑P.φB)^[j % h] c` using `by conv_lhs => rw [← Nat.mod_add_div j h]`. Rewrite using `[Function.iterate_add_apply, (hper.mul_const (j / h)).eq]`. Establish `h1` using `hF (j % h) (Nat.mod_lt _ hh)`.

Rewrite using `[← SetLike.mem_coe, ← P.PD_Fil _ E 0, hj]`. Conclude with `h1`. Take `⟨a, ha⟩` from `GlobalTheory.CrisPerFix.mem_unramified_of_frobenius_iterate_fixed_fil_alt l P AI T E c (by rw [hdim]; exact hc) hall`. Use `⟨⟨(a : Om l), a.2.2⟩, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(hEfix ⟨(a : Om l), a.2.2⟩).2 a.2.1`.

Rewrite using `[ha]`. Both sides reduce to the same expression.
-/
theorem unr_of_iterate_fixed :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h : ℕ), 0 < h →
      ∀ c : P.R.B, P.φB^[h] c = c → (∀ j < h, ev P j c ∈ Fil P 0) →
        ∃ a : ↥(MaximalUnramifiedExtension l), fr l h a = a ∧ c = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B a := by
  intro l _ P AI T h hh c hc hF
  obtain ⟨E, ω, hEle, hEdim, hEfix, -⟩ := GlobalTheory.T.unramifiedExt_fixedField_frobeniusPow_degree l h hh
  have hK0 : K0 E = E.1 := inf_eq_left.2 hEle
  have hdim : Module.finrank ℚ_[l] ↥(K0 E) = h := by rw [hK0]; exact hEdim
  have hper : Function.IsPeriodicPt (⇑P.φB) h c := hc
  have hall : ∀ j : ℕ, P.ιB ((⇑P.φB)^[j] c) ∈ (P.PD E).Fil 0 := by
    intro j
    have hj : (⇑P.φB)^[j] c = (⇑P.φB)^[j % h] c := by
      conv_lhs => rw [← Nat.mod_add_div j h]
      rw [Function.iterate_add_apply, (hper.mul_const (j / h)).eq]
    have h1 := hF (j % h) (Nat.mod_lt _ hh)
    rw [← SetLike.mem_coe, ← P.PD_Fil _ E 0, hj]
    exact h1
  obtain ⟨a, ha⟩ := GlobalTheory.CrisPerFix.mem_unramified_of_frobenius_iterate_fixed_fil_alt l P AI T E c (by rw [hdim]; exact hc) hall
  refine ⟨⟨(a : Om l), a.2.2⟩, ?_, ?_⟩
  · exact (hEfix ⟨(a : Om l), a.2.2⟩).2 a.2.1
  · rw [ha]; rfl

end GlobalTheory.PMon
