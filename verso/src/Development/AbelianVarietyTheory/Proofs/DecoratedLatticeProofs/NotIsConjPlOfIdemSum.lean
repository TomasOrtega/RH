import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TowerIsChain
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevelLawOfPairLaw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.FlagAct

open GlobalTheory.ChainOnto.FlagModel

variable {D : D7} {c : Com D} {s : PiLocalization₂ D}

/- English proof (translation)
Introduce `PP hP PP' hP' hc`. Take `⟨⟨es, hes, he⟩, h0⟩` from `h`. Establish `hsum : ∑ x ∈ P ×ˢ P, es x.1 * cA D (es x.2) = 0`. Rewrite using `[Finset.sum_product, ← h0, he, map_sum, Finset.sum_mul_sum]`. Establish `hidem : ∀ x ∈ P ×ˢ P, (es x.1 * cA D (es x.2)) * (es x.1 * cA D (es x.2)) = es x.1 * cA D (es x.2)`.

Introduce `x hx`. Take `⟨h1, h2⟩` from `Finset.mem_product.1 hx`. Rewrite using `[mul_mul_mul_comm, ← map_mul, (hes _ h1).1.1, (hes _ h2).1.1]`. Establish `horth : es PP * cA D (es PP') = 0` using `GlobalTheory.PlaceVec.idem_eq_zero_of_sum (A := AE D) (ι := Pl D.host.E × Pl D.host.E) (fun n z hn hz => GlobalTheory.PlaceVec.natCast_mul_eq_zero (D := D) n z hn hz) (fun x => es x.1 * cA D (es x.2)) (P ×ˢ P) hidem hsum (PP, PP') (Finset.mem_product.2 ⟨hP, hP'⟩)`. Establish `hfw : ∀ x, x ∈ PP.asIdeal → Formalism.L2.Col.cO D.host.E x ∈ PP'.asIdeal`.

Introduce `x hx`. Take `⟨c', hc', hcv⟩` from `hc x hx`. Establish `e1 : c' = Formalism.L2.Col.cO D.host.E x` using `RingOfIntegers.ext hcv`. Rewrite using `[← e1]`. Conclude with `hc'`.

Establish `hiff : ∀ x, x ∈ PP.asIdeal ↔ Formalism.L2.Col.cO D.host.E x ∈ PP'.asIdeal`. Establish `hle : PP.asIdeal ≤ PP'.asIdeal.comap (Formalism.L2.Col.cO D.host.E)` using `fun x hx => hfw x hx`. Use `haveI := PP'.isPrime`. Establish `heq` using `PP.isMaximal.eq_of_le (Ideal.IsPrime.comap (Formalism.L2.Col.cO D.host.E)).ne_top hle`. Introduce `x`.

Rewrite using `[heq]`. Conclude with `Ideal.mem_comap`. Establish `hconj` using `GlobalTheory.MovedIdem.isIdemAt_conj (hes PP' hP') hiff`. Establish `heq : es PP = cA D (es PP')` using `(GlobalTheory.ExportSeries.idemAt_eq (hes PP hP)).symm.trans (GlobalTheory.ExportSeries.idemAt_eq hconj)`. Establish `hz : es PP = 0`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨x, hxP, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot PP.ne_bot`. Establish `h3` using `((hes PP hP).2 x hx0).1 hxP`. Rewrite `h3` using `[hz, zero_mul, map_zero]`. Conclude with `h3 (zero_mem _)`.
-/
theorem not_isConjPl_of_idemSum {e : AE D} {P : Finset (Pl D.host.E)} (h : IsIdemSum e P) :
    ∀ PP ∈ P, ∀ PP' ∈ P, ¬ Lev.IsConjPl PP PP' := by
  classical
  intro PP hP PP' hP' hc
  obtain ⟨⟨es, hes, he⟩, h0⟩ := h
  have hsum : ∑ x ∈ P ×ˢ P, es x.1 * cA D (es x.2) = 0 := by
    rw [Finset.sum_product, ← h0, he, map_sum, Finset.sum_mul_sum]
  have hidem : ∀ x ∈ P ×ˢ P,
      (es x.1 * cA D (es x.2)) * (es x.1 * cA D (es x.2)) = es x.1 * cA D (es x.2) := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hx
    rw [mul_mul_mul_comm, ← map_mul, (hes _ h1).1.1, (hes _ h2).1.1]
  have horth : es PP * cA D (es PP') = 0 :=
    GlobalTheory.PlaceVec.idem_eq_zero_of_sum (A := AE D) (ι := Pl D.host.E × Pl D.host.E)
      (fun n z hn hz => GlobalTheory.PlaceVec.natCast_mul_eq_zero (D := D) n z hn hz) (fun x => es x.1 * cA D (es x.2)) (P ×ˢ P)
      hidem hsum (PP, PP') (Finset.mem_product.2 ⟨hP, hP'⟩)
  have hfw : ∀ x, x ∈ PP.asIdeal → Formalism.L2.Col.cO D.host.E x ∈ PP'.asIdeal := by
    intro x hx
    obtain ⟨c', hc', hcv⟩ := hc x hx
    have e1 : c' = Formalism.L2.Col.cO D.host.E x := RingOfIntegers.ext hcv
    rw [← e1]; exact hc'
  have hiff : ∀ x, x ∈ PP.asIdeal ↔ Formalism.L2.Col.cO D.host.E x ∈ PP'.asIdeal := by
    have hle : PP.asIdeal ≤ PP'.asIdeal.comap (Formalism.L2.Col.cO D.host.E) := fun x hx => hfw x hx
    haveI := PP'.isPrime
    have heq := PP.isMaximal.eq_of_le (Ideal.IsPrime.comap (Formalism.L2.Col.cO D.host.E)).ne_top hle
    intro x
    rw [heq]
    exact Ideal.mem_comap
  have hconj := GlobalTheory.MovedIdem.isIdemAt_conj (hes PP' hP') hiff
  have heq : es PP = cA D (es PP') :=
    (GlobalTheory.ExportSeries.idemAt_eq (hes PP hP)).symm.trans (GlobalTheory.ExportSeries.idemAt_eq hconj)
  have hz : es PP = 0 := by
    calc es PP = es PP * es PP := ((hes PP hP).1.1).symm
      _ = es PP * cA D (es PP') := congrArg (es PP * ·) heq
      _ = 0 := horth
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot PP.ne_bot
  have h3 := ((hes PP hP).2 x hx0).1 hxP
  rw [hz, zero_mul, map_zero] at h3
  exact h3 (zero_mem _)

/- English proof (translation)
Take `⟨N, hN, -⟩` from `hs.base`. Take `⟨hr, ξ, hL⟩` from `hs.lev`. Take `⟨e, he⟩` from `hc.split`. Establish `hnc` using `not_isConjPl_of_idemSum he`. Establish `hPg : s.L.Pg = c.Pg` using `by rw [hL]; rfl`.

Establish `hQ : s.L.Q = ∅` using `by rw [hL]; rfl`. Use `GlobalTheory.ParahoricLift.liftsExist s.V s.β s.L s.Λ N hN (fun PP hP PP' hP' => ?_) ?_` and prove the remaining obligations. Rewrite `hP` using `[hPg]`. Rewrite `hP'` using `[hPg, hQ]`. Break down `hP' with h | h` into its components or cases.

Conclude with `hnc PP hP PP' h`. Conclude with `absurd h (Finset.notMem_empty _)`. Rewrite using `[hQ]`. Conclude with `Finset.disjoint_empty_right _`.
-/
theorem liftsExist_stage {c : Com D} (hc : c.Is) {j : ℕ} {s : PiLocalization₂ D} (hs : s.Is c j) :
    Lev.LiftsExist s.V s.β s.L := by
  obtain ⟨N, hN, -⟩ := hs.base
  obtain ⟨hr, ξ, hL⟩ := hs.lev
  obtain ⟨e, he⟩ := hc.split
  have hnc := not_isConjPl_of_idemSum he
  have hPg : s.L.Pg = c.Pg := by rw [hL]; rfl
  have hQ : s.L.Q = ∅ := by rw [hL]; rfl
  refine GlobalTheory.ParahoricLift.liftsExist s.V s.β s.L s.Λ N hN (fun PP hP PP' hP' => ?_) ?_
  · rw [hPg] at hP
    rw [hPg, hQ] at hP'
    rcases hP' with h | h
    · exact hnc PP hP PP' h
    · exact absurd h (Finset.notMem_empty _)
  · rw [hQ]; exact Finset.disjoint_empty_right _

end GlobalTheory.ChainOnto.FlagAct
