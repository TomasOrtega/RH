import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKFin

/- English proof (translation)
Use `haveI : Fintype F := Fintype.ofFinite F`. Establish `hker : RingHom.ker (WittVector.truncate (p` using `l) (R := F) n) = Ideal.span {(l : WittVector l F) ^ n} := by`. Use extensionality with `x`. Rewrite using `[WittVector.mem_ker_truncate, WittVector.mem_span_p_pow_iff_le_coeff_eq_zero]`. Conclude with `Finite.of_equiv _ ((Ideal.quotEquivOfEq hker).symm.trans (RingHom.quotientKerEquivOfSurjective (WittVector.truncate_surjective l n F))).toEquiv.symm`.
-/
theorem finite_witt_quot (l : ℕ) [Fact l.Prime] (F : Type) [Field F] [Finite F] [CharP F l] (n : ℕ) :
    Finite (WittVector l F ⧸ Ideal.span {(l : WittVector l F) ^ n}) := by
  haveI : Fintype F := Fintype.ofFinite F
  have hker : RingHom.ker (WittVector.truncate (p := l) (R := F) n) =
      Ideal.span {(l : WittVector l F) ^ n} := by
    ext x
    rw [WittVector.mem_ker_truncate, WittVector.mem_span_p_pow_iff_le_coeff_eq_zero]
  exact Finite.of_equiv _ ((Ideal.quotEquivOfEq hker).symm.trans
    (RingHom.quotientKerEquivOfSurjective (WittVector.truncate_surjective l n F))).toEquiv.symm

/- English proof (translation)
Introduce `l _ K bk n c`. Use `haveI : Finite (Wq l bk.a ⧸ Ideal.span {(l : Wq l bk.a) ^ n}) := finite_witt_quot l (Fq l bk.a) n`. Set `J : Ideal (Wq l bk.a)` to `Ideal.span {(l : Wq l bk.a) ^ n}`. Set `I : Ideal bk.S` to `Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {(X : bk.S) ^ c}`. Set `g : (Fin c → Wq l bk.a ⧸ J) → bk.S ⧸ I` to `fun t => Ideal.Quotient.mk I (∑ i ∈ Finset.range c, C (if h : i < c then (t ⟨i, h⟩).out else 0) * X ^ i)`.

Use `Finite.of_surjective g ?_` and prove the remaining obligations. Introduce `q`. Take `⟨s, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Use `⟨fun i => Ideal.Quotient.mk J (coeff (i : ℕ) s), ?_⟩` and prove the remaining obligations. Set `w : ℕ → Wq l bk.a` to `fun i => if h : i < c then (Ideal.Quotient.mk J (coeff i s)).out else 0`.

Use `show Ideal.Quotient.mk I (∑ i ∈ Finset.range c, C (w i) * X ^ i) = Ideal.Quotient.mk I s`. Rewrite using `[Ideal.Quotient.eq]`. Establish `hw : ∀ i < c, w i - coeff i s ∈ J`. Introduce `i hi`. Simplify using `only [w, dif_pos hi]`.

Rewrite using `[← Ideal.Quotient.eq]`. Conclude with `Ideal.Quotient.mk_out _`. Establish `hsplit : (∑ i ∈ Finset.range c, C (w i) * X ^ i) - s = (∑ i ∈ Finset.range c, C (w i - coeff i s) * X ^ i) + ((∑ i ∈ Finset.range c, C (coeff i s) * X ^ i) - s)`. Simplify using `only [map_sub, sub_mul, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hsplit]`. Use `Ideal.add_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right ?_)` and prove the remaining obligations. Use `Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ ?_` and prove the remaining obligations. Take `⟨y, hy⟩` from `Ideal.mem_span_singleton'.1 (hw i (Finset.mem_range.1 hi))`. Rewrite using `[← hy, map_mul, map_pow, map_natCast]`.

Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)`. Rewrite using `[Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]`. Introduce `m hm`. Simplify using `[PowerSeries.coeff_C_mul_X_pow, Finset.sum_ite_eq', hm]`.
-/
theorem finite_quot : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n c : ℕ),
    Finite (bk.S ⧸ (Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {(X : bk.S) ^ c})) := by
  intro l _ K bk n c
  haveI : Finite (Wq l bk.a ⧸ Ideal.span {(l : Wq l bk.a) ^ n}) := finite_witt_quot l (Fq l bk.a) n
  let J : Ideal (Wq l bk.a) := Ideal.span {(l : Wq l bk.a) ^ n}
  let I : Ideal bk.S := Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {(X : bk.S) ^ c}
  let g : (Fin c → Wq l bk.a ⧸ J) → bk.S ⧸ I := fun t => Ideal.Quotient.mk I
    (∑ i ∈ Finset.range c, C (if h : i < c then (t ⟨i, h⟩).out else 0) * X ^ i)
  refine Finite.of_surjective g ?_
  intro q
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨fun i => Ideal.Quotient.mk J (coeff (i : ℕ) s), ?_⟩
  let w : ℕ → Wq l bk.a := fun i => if h : i < c then (Ideal.Quotient.mk J (coeff i s)).out else 0
  show Ideal.Quotient.mk I (∑ i ∈ Finset.range c, C (w i) * X ^ i) = Ideal.Quotient.mk I s
  rw [Ideal.Quotient.eq]
  have hw : ∀ i < c, w i - coeff i s ∈ J := by
    intro i hi
    simp only [w, dif_pos hi]
    rw [← Ideal.Quotient.eq]
    exact Ideal.Quotient.mk_out _
  have hsplit : (∑ i ∈ Finset.range c, C (w i) * X ^ i) - s =
      (∑ i ∈ Finset.range c, C (w i - coeff i s) * X ^ i) +
        ((∑ i ∈ Finset.range c, C (coeff i s) * X ^ i) - s) := by
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  refine Ideal.add_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right ?_)
  · refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ ?_
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (hw i (Finset.mem_range.1 hi))
    rw [← hy, map_mul, map_pow, map_natCast]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
    intro m hm
    simp [PowerSeries.coeff_C_mul_X_pow, Finset.sum_ite_eq', hm]

end GlobalTheory.BKFin
