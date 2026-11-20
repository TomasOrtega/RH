import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.Development
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanMulMem

noncomputable section

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol MeasureTheory NumberField
  IsDedekindDomain
open scoped TensorProduct Classical

section Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_oev_iff (x : Fv F v ⊗[F] E) :
    x ∈ OEv (E := E) v ↔ x ∈ Submodule.span (v.adicCompletionIntegers F)
      ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) := Iff.rfl

/- English proof (translation)
Rewrite using `[mem_oev_iff]`. Conclude with `Submodule.zero_mem _`.
-/
theorem oev_zero : (0 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  rw [mem_oev_iff]; exact Submodule.zero_mem _

/- English proof (translation)
Rewrite `*` using `[mem_oev_iff]`. Conclude with `Submodule.add_mem _ ha hb`.
-/
theorem oev_add {a b : Fv F v ⊗[F] E} (ha : a ∈ OEv (E := E) v) (hb : b ∈ OEv (E := E) v) :
    a + b ∈ OEv (E := E) v := by
  rw [mem_oev_iff] at *; exact Submodule.add_mem _ ha hb

/- English proof (translation)
Rewrite `*` using `[mem_oev_iff]`. Conclude with `Submodule.neg_mem _ ha`.
-/
theorem oev_neg {a : Fv F v ⊗[F] E} (ha : a ∈ OEv (E := E) v) : -a ∈ OEv (E := E) v := by
  rw [mem_oev_iff] at *; exact Submodule.neg_mem _ ha

/- English proof (translation)
Apply the tactic sequence `first | exact GlobalTheory.SpanMulInertiaEigenvalues.main .. | (apply GlobalTheory.SpanMulInertiaEigenvalues.main <;> assumption) | (intros; apply GlobalTheory.SpanMulInertiaEigenvalues.main <;> assumption) | (apply @GlobalTheory.SpanMulInertiaEigenvalues.main <;> assumption) | ( …`.
-/
theorem oev_mul {a b : Fv F v ⊗[F] E} (ha : a ∈ OEv (E := E) v) (hb : b ∈ OEv (E := E) v) :
    a * b ∈ OEv (E := E) v := by
  first | exact GlobalTheory.SpanMulInertiaEigenvalues.main .. | (apply GlobalTheory.SpanMulInertiaEigenvalues.main <;> assumption) | (intros; apply GlobalTheory.SpanMulInertiaEigenvalues.main <;> assumption) | (apply @GlobalTheory.SpanMulInertiaEigenvalues.main <;> assumption) | (intros; apply @GlobalTheory.SpanMulInertiaEigenvalues.main <;> assumption) | (apply @GlobalTheory.SpanMulInertiaEigenvalues.main <;> first | assumption | infer_instance) | exact @GlobalTheory.SpanMulInertiaEigenvalues.main F E ‹_› ‹_› ‹_› ‹_› v a b ha hb | exact @GlobalTheory.SpanMulInertiaEigenvalues.main F E ‹_› ‹_› ‹_› ‹_› v a b ha | exact @GlobalTheory.SpanMulInertiaEigenvalues.main F E ‹_› ‹_› ‹_› ‹_› v a b | exact @GlobalTheory.SpanMulInertiaEigenvalues.main F E ‹_› ‹_› ‹_› ‹_› v a | exact @GlobalTheory.SpanMulInertiaEigenvalues.main F E ‹_› ‹_› ‹_› ‹_› v | exact @GlobalTheory.SpanMulInertiaEigenvalues.main F E ‹_› ‹_› ‹_› ‹_› | exact @GlobalTheory.SpanMulInertiaEigenvalues.main F E ‹_› ‹_› ‹_› | exact @GlobalTheory.SpanMulInertiaEigenvalues.main F E ‹_› ‹_› | exact @GlobalTheory.SpanMulInertiaEigenvalues.main F E ‹_› | exact @GlobalTheory.SpanMulInertiaEigenvalues.main F E | exact @GlobalTheory.SpanMulInertiaEigenvalues.main F

/- English proof (translation)
Simplify using `[sc, Algebra.TensorProduct.tmul_mul_tmul]`.
-/
theorem sc_mul' (a b : Fv F v) : sc (E := E) v a * sc (E := E) v b = sc (E := E) v (a * b) := by
  simp [sc, Algebra.TensorProduct.tmul_mul_tmul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sc_one' : sc (E := E) v (1 : Fv F v) = 1 := rfl

/- English proof (translation)
Rewrite using `[smul_smul, sc_mul']`.
-/
theorem sc_smul_sc (a b : Fv F v) (w : Fin n → Fv F v ⊗[F] E) :
    sc (E := E) v a • sc (E := E) v b • w = sc (E := E) v (a * b) • w := by
  rw [smul_smul, sc_mul']

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, sc]`. Rewrite using `[show c • z i = (c : Fv F v) • z i from rfl, Algebra.smul_def]`. Both sides reduce to the same expression.
-/
theorem osmul_eq (c : v.adicCompletionIntegers F) (z : Fin n → Fv F v ⊗[F] E) :
    c • z = sc (E := E) v (c : Fv F v) • z := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, sc]
  rw [show c • z i = (c : Fv F v) • z i from rfl, Algebra.smul_def]
  rfl

/- English proof (translation)
Rewrite using `[osmul_eq]`. Simplify using the standard rewrite rules.
-/
theorem nat_osmul (g : ℕ) (z : Fin n → Fv F v ⊗[F] E) :
    (g : v.adicCompletionIntegers F) • z = sc (E := E) v (g : Fv F v) • z := by
  rw [osmul_eq]; simp

/- English proof (translation)
Unfold `dV`. Use `split_ifs with h`. Conclude with `h.choose_spec.1`. Conclude with `one_ne_zero`.
-/
theorem dV_ne' : dV v ≠ 0 := by
  unfold dV
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_ne_zero

/- English proof (translation)
Unfold `alp`. Use `split_ifs`. Conclude with `pow_ne_zero _ (inv_ne_zero (dV_ne' v))`. Conclude with `one_ne_zero`.
-/
theorem alp_ne' (r : ℕ) (a : Fin (r + 1)) : alp v r a ≠ 0 := by
  unfold alp
  split_ifs
  · exact pow_ne_zero _ (inv_ne_zero (dV_ne' v))
  · exact one_ne_zero

end Ring

end PI.LocMassTypW
