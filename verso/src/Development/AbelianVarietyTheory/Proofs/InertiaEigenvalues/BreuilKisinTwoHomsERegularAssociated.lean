import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOrientedPrismUniformizerFrameBreuilKisinHomStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Establish `hdI : d ∈ I` using `hd ▸ Ideal.mem_span_singleton_self d`. Set `φ : A →ₗ[A] ↥I` to `LinearMap.toSpanSingleton A ↥I ⟨d, hdI⟩`. Establish `hs : Function.Surjective φ`. Introduce and unpack `⟨x, hx⟩`. Rewrite `hx` using `[hd]`.

Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.1 hx`. Conclude with `⟨a, Subtype.ext (by simp [φ])⟩`. Establish `hb` using `Module.Invertible.bijective_of_surjective hs`. Use `mem_nonZeroDivisors_iff.2 ⟨fun a ha => ?_, fun a ha => ?_⟩` and prove the remaining obligations. Use `hb.1 (?_ : φ a = φ 0)` and prove the remaining obligations.

Conclude with `Subtype.ext (by simp [φ]; linear_combination ha)`. Use `hb.1 (?_ : φ a = φ 0)` and prove the remaining obligations. Conclude with `Subtype.ext (by simp [φ]; linear_combination ha)`.
-/
theorem mem_nonZeroDivisors_of_invertible_span {A : Type} [CommRing A] {I : Ideal A}
    (hI : Module.Invertible A ↥I) {d : A} (hd : I = Ideal.span {d}) : d ∈ nonZeroDivisors A := by
  have hdI : d ∈ I := hd ▸ Ideal.mem_span_singleton_self d
  let φ : A →ₗ[A] ↥I := LinearMap.toSpanSingleton A ↥I ⟨d, hdI⟩
  have hs : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    rw [hd] at hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    exact ⟨a, Subtype.ext (by simp [φ])⟩
  have hb := Module.Invertible.bijective_of_surjective hs
  refine mem_nonZeroDivisors_iff.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · refine hb.1 (?_ : φ a = φ 0)
    exact Subtype.ext (by simp [φ]; linear_combination ha)
  · refine hb.1 (?_ : φ a = φ 0)
    exact Subtype.ext (by simp [φ]; linear_combination ha)

/- English proof (translation)
Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.1 (h ▸ Ideal.mem_span_singleton_self d)`. Take `⟨b, hb⟩` from `Ideal.mem_span_singleton'.1 (h.symm ▸ Ideal.mem_span_singleton_self d')`. Establish `hab : a * b = 1`. Establish `: d * (a * b - 1) = 0` using `by linear_combination a * hb + ha`. Conclude with `sub_eq_zero.1 ((mem_nonZeroDivisors_iff.1 hd).1 _ this)`.

Conclude with `⟨⟨b, a, by rw [mul_comm]; exact hab, hab⟩, by rw [Units.val_mk, mul_comm]; exact hb⟩`.
-/
theorem associated_of_span_eq {A : Type} [CommRing A] {d d' : A} (hd : d ∈ nonZeroDivisors A)
    (h : Ideal.span {d} = Ideal.span {d'}) : Associated d d' := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (h ▸ Ideal.mem_span_singleton_self d)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (h.symm ▸ Ideal.mem_span_singleton_self d')
  have hab : a * b = 1 := by
    have : d * (a * b - 1) = 0 := by linear_combination a * hb + ha
    exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff.1 hd).1 _ this)
  exact ⟨⟨b, a, by rw [mul_comm]; exact hab, hab⟩, by rw [Units.val_mk, mul_comm]; exact hb⟩

/- English proof (translation)
Introduce `l _ K bk B f g`. Take `⟨hfI, hfX⟩` from `GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk B f`. Take `⟨hgI, hgX⟩` from `GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk B g`. Establish `hreg` using `mem_nonZeroDivisors_of_invertible_span B.inv hfI`. Use `⟨hreg, associated_of_span_eq hreg (hfI.symm.trans hgI), ?_⟩` and prove the remaining obligations.

Rewrite using `[← Ideal.mem_span_singleton, ← hfI]`. Conclude with `Ideal.Quotient.eq.1 (hgX.trans hfX.symm)`.
-/
theorem hf_E_pair : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (f g : Hom bk.prism B),
    BK.hf f bk.E ∈ nonZeroDivisors B.A ∧ Associated (BK.hf f bk.E) (BK.hf g bk.E) ∧
      BK.hf f bk.E ∣ BK.hf g X - BK.hf f X := by
  intro l _ K bk B f g
  obtain ⟨hfI, hfX⟩ := GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk B f
  obtain ⟨hgI, hgX⟩ := GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk B g
  have hreg := mem_nonZeroDivisors_of_invertible_span B.inv hfI
  refine ⟨hreg, associated_of_span_eq hreg (hfI.symm.trans hgI), ?_⟩
  rw [← Ideal.mem_span_singleton, ← hfI]
  exact Ideal.Quotient.eq.1 (hgX.trans hfX.symm)

end GlobalTheory.BSP
