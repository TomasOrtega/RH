import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvertibleIdealEqOfNotLeMaximalMulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimeNotMemSqAndDeltaNotMemStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.Prism.Rigid

/- English proof (translation)
Rewrite using `[D.φ_eq]`. Conclude with `Ideal.add_mem _ (Ideal.pow_mem_of_mem _ hx _ hl) (Ideal.mul_mem_right _ _ hlm)`.
-/
theorem φ_mem_of_mem {l : ℕ} (hl : 0 < l) {A : Type} [CommRing A] (D : Delta l A) {m : Ideal A}
    (hlm : (l : A) ∈ m) {x : A} (hx : x ∈ m) : D.φ x ∈ m := by
  rw [D.φ_eq]
  exact Ideal.add_mem _ (Ideal.pow_mem_of_mem _ hx _ hl) (Ideal.mul_mem_right _ _ hlm)

/- English proof (translation)
Establish `h : (m ^ 2).map D.φ ≤ m ^ 2`. Rewrite using `[Ideal.map_pow, sq, sq]`. Establish `hm : m.map D.φ ≤ m` using `Ideal.map_le_iff_le_comap.2 fun y hy => φ_mem_of_mem hl D hlm hy`. Conclude with `Ideal.mul_mono hm hm`. Conclude with `h (Ideal.mem_map_of_mem _ hx)`.
-/
theorem φ_mem_sq {l : ℕ} (hl : 0 < l) {A : Type} [CommRing A] (D : Delta l A) {m : Ideal A}
    (hlm : (l : A) ∈ m) {x : A} (hx : x ∈ m ^ 2) : D.φ x ∈ m ^ 2 := by
  have h : (m ^ 2).map D.φ ≤ m ^ 2 := by
    rw [Ideal.map_pow, sq, sq]
    have hm : m.map D.φ ≤ m := Ideal.map_le_iff_le_comap.2 fun y hy => φ_mem_of_mem hl D hlm hy
    exact Ideal.mul_mono hm hm
  exact h (Ideal.mem_map_of_mem _ hx)

/- English proof (translation)
Establish `hl0 : 0 < l` using `hl.out.pos`. Establish `hNI : B.I.map f.f ≤ B'.I` using `Ideal.map_le_iff_le_comap.2 fun a ha => f.f_I a ha`. Use `GlobalTheory.T.eq_of_le_invertible_of_not_le_maximal_mul B'.A B'.I (B.I.map f.f) B'.inv hNI ?_` and prove the remaining obligations. Introduce `m hm hN`. Establish `hjac : Ideal.span {(l : B'.A)} ⊔ B'.I ≤ m` using `by haveI := B'.complete`.

Use `le_trans (IsAdicComplete.le_jacobson_bot (Ideal.span {(l : B'.A)} ⊔ B'.I)) ?_` and prove the remaining obligations. Conclude with `sInf_le ⟨bot_le, hm⟩`. Establish `hlm : (l : B'.A) ∈ m` using `hjac (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))`. Establish `hIm : B'.I ≤ m` using `le_trans le_sup_right hjac`. Establish `hN2 : B.I.map f.f ≤ m ^ 2`.

Rewrite using `[sq]`. Conclude with `le_trans hN (Ideal.mul_mono_right hIm)`. Establish `hmap : B.I ⊔ B.I.map B.D.φ ≤ (m ^ 2).comap f.f`. Use `sup_le (fun a ha => hN2 (Ideal.mem_map_of_mem _ ha)) ?_` and prove the remaining obligations. Use `Ideal.map_le_iff_le_comap.2 fun a ha => ?_` and prove the remaining obligations.

Use `show f.f (B.D.φ a) ∈ m ^ 2`. Rewrite using `[f.f_φ]`. Conclude with `φ_mem_sq hl0 B'.D hlm (hN2 (Ideal.mem_map_of_mem _ ha))`. Establish `hl2 : (l : B'.A) ∈ m ^ 2`. Use `hmap B.l_mem` as an intermediate fact.

Simplify `this` using `[map_natCast]`. Conclude with `(GlobalTheory.T.prime_not_mem_sq_and_delta_not_mem l B'.A B'.D m hm.ne_top hlm).1 hl2`.
-/
theorem map_I_eq (l : ℕ) [hl : Fact l.Prime] (R : Type) [CommRing R] (B B' : Obj l R) (f : Hom B B') :
    B.I.map f.f = B'.I := by
  have hl0 : 0 < l := hl.out.pos
  have hNI : B.I.map f.f ≤ B'.I := Ideal.map_le_iff_le_comap.2 fun a ha => f.f_I a ha
  refine GlobalTheory.T.eq_of_le_invertible_of_not_le_maximal_mul B'.A B'.I (B.I.map f.f) B'.inv hNI ?_
  intro m hm hN

  have hjac : Ideal.span {(l : B'.A)} ⊔ B'.I ≤ m := by
    haveI := B'.complete
    refine le_trans (IsAdicComplete.le_jacobson_bot (Ideal.span {(l : B'.A)} ⊔ B'.I)) ?_
    exact sInf_le ⟨bot_le, hm⟩
  have hlm : (l : B'.A) ∈ m := hjac (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  have hIm : B'.I ≤ m := le_trans le_sup_right hjac
  have hN2 : B.I.map f.f ≤ m ^ 2 := by
    rw [sq]; exact le_trans hN (Ideal.mul_mono_right hIm)

  have hmap : B.I ⊔ B.I.map B.D.φ ≤ (m ^ 2).comap f.f := by
    refine sup_le (fun a ha => hN2 (Ideal.mem_map_of_mem _ ha)) ?_
    refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
    show f.f (B.D.φ a) ∈ m ^ 2
    rw [f.f_φ]
    exact φ_mem_sq hl0 B'.D hlm (hN2 (Ideal.mem_map_of_mem _ ha))
  have hl2 : (l : B'.A) ∈ m ^ 2 := by
    have := hmap B.l_mem
    simpa [map_natCast] using this
  exact (GlobalTheory.T.prime_not_mem_sq_and_delta_not_mem l B'.A B'.D m hm.ne_top hlm).1 hl2

end GlobalTheory.Prism.Rigid
