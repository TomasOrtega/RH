import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdSubOfDvdSubX
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory

/- English proof (translation)
Introduce `l hl a _ P Q hP hdvd hQ`. Establish `hl0 : 0 < l` using `hl.out.pos`. Use `set σ : Wq l a →+* Wq l a := (sigma l a : Wq l a →+* Wq l a) with hσ`. Establish `hσinj : Function.Injective σ` using `(sigma l a).injective`. Establish `hcoe : frobS l a (P : (Wq l a)⟦X⟧) = ((Polynomial.expand (Wq l a) l (P.map σ) : Polynomial (Wq l a)) : (Wq l a)⟦X⟧)`.

Use `PowerSeries.ext fun n => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `PowerSeries.coeff n (PowerSeries.map σ (PowerSeries.expand l hl.out.ne_zero (P : (Wq l a)⟦X⟧))) = _`. Rewrite using `[PowerSeries.coeff_map, PowerSeries.coeff_expand, Polynomial.coeff_coe, Polynomial.coeff_coe, Polynomial.coeff_expand hl0]`. Apply the tactic sequence `split_ifs <;> simp [Polynomial.coeff_map]`. Rewrite `hQ` using `[hcoe]`.

Use `haveI : IsAdicComplete (Ideal.span {(l : Wq l a)}) (Wq l a) := WittVector.isAdicCompleteIdealSpanP`. Establish `hmon : (Polynomial.expand (Wq l a) l (P.map σ)).Monic` using `(hP.map σ).expand hl0`. Establish `hdeg : (Polynomial.expand (Wq l a) l (P.map σ)).natDegree = P.natDegree * l`. Rewrite using `[Polynomial.natDegree_expand, Polynomial.natDegree_map_eq_of_injective hσinj]`. Establish `H : (Polynomial.expand (Wq l a) l (P.map σ)).IsDistinguishedAt (Ideal.span {(l : Wq l a)})` using `{ mem := fun {n} hn => by`.

Rewrite using `[Ideal.mem_span_singleton, Polynomial.coeff_expand hl0]`. Rewrite `hn` using `[hdeg]`. Use `split_ifs with h`. Rewrite using `[Polynomial.coeff_map]`. Establish `hlt : n / l < P.natDegree`.

Rewrite using `[Nat.div_lt_iff_lt_mul hl0]`. Conclude with `hn`. Take `⟨c, hc⟩` from `hdvd _ hlt`. Use `⟨σ c, ?_⟩` and prove the remaining obligations. Rewrite using `[hc, map_mul, map_natCast]`.

Conclude with `dvd_zero _`. Use `monic := hmon }`. Conclude with `GlobalTheory.NB.LT.poly_dvd_of_dvd H hQ`.
-/
theorem expand_map_dvd_of_frobS_dvd : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (P Q : Polynomial (Wq l a)), P.Monic →
    (∀ i < P.natDegree, (l : Wq l a) ∣ P.coeff i) → frobS l a (P : (Wq l a)⟦X⟧) ∣ (Q : (Wq l a)⟦X⟧) →
    Polynomial.expand (Wq l a) l (P.map (sigma l a : Wq l a →+* Wq l a)) ∣ Q := by
  intro l hl a _ P Q hP hdvd hQ
  have hl0 : 0 < l := hl.out.pos
  set σ : Wq l a →+* Wq l a := (sigma l a : Wq l a →+* Wq l a) with hσ
  have hσinj : Function.Injective σ := (sigma l a).injective
  have hcoe : frobS l a (P : (Wq l a)⟦X⟧) =
      ((Polynomial.expand (Wq l a) l (P.map σ) : Polynomial (Wq l a)) : (Wq l a)⟦X⟧) := by
    refine PowerSeries.ext fun n => ?_
    change PowerSeries.coeff n (PowerSeries.map σ (PowerSeries.expand l hl.out.ne_zero (P : (Wq l a)⟦X⟧))) = _
    rw [PowerSeries.coeff_map, PowerSeries.coeff_expand, Polynomial.coeff_coe, Polynomial.coeff_coe, Polynomial.coeff_expand hl0]
    split_ifs <;> simp [Polynomial.coeff_map]
  rw [hcoe] at hQ
  haveI : IsAdicComplete (Ideal.span {(l : Wq l a)}) (Wq l a) := WittVector.isAdicCompleteIdealSpanP
  have hmon : (Polynomial.expand (Wq l a) l (P.map σ)).Monic := (hP.map σ).expand hl0
  have hdeg : (Polynomial.expand (Wq l a) l (P.map σ)).natDegree = P.natDegree * l := by
    rw [Polynomial.natDegree_expand, Polynomial.natDegree_map_eq_of_injective hσinj]
  have H : (Polynomial.expand (Wq l a) l (P.map σ)).IsDistinguishedAt (Ideal.span {(l : Wq l a)}) :=
    { mem := fun {n} hn => by
        rw [Ideal.mem_span_singleton, Polynomial.coeff_expand hl0]
        rw [hdeg] at hn
        split_ifs with h
        · rw [Polynomial.coeff_map]
          have hlt : n / l < P.natDegree := by
            rw [Nat.div_lt_iff_lt_mul hl0]; exact hn
          obtain ⟨c, hc⟩ := hdvd _ hlt
          refine ⟨σ c, ?_⟩
          rw [hc, map_mul, map_natCast]
        · exact dvd_zero _
      monic := hmon }
  exact GlobalTheory.NB.LT.poly_dvd_of_dvd H hQ

end GlobalTheory
