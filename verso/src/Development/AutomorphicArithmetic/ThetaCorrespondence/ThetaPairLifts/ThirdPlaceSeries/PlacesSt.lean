import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawLeftRestrictionGlobal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealTwLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Links2OfRows

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.TupLe
variable {D : D7}
open Classical in
/- English proof (translation)
Introduce `D L hT Gi Gl Kc Y cX ex Csz p j hr hm w hw hok ρ hρ hpin _ _`. Establish `hPA` using `placesAt (j := j) hw hρ hpin`. Establish `hL` using `_root_.GlobalTheory.BigOn.links2_of_rows_alt _ _ _ _ _ _ _ _ _ _ p hr hm.1`. Establish `hC : GlobalTheory.Hk3.Core (R2 p) (F2 p)` using `⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩`. Establish `hXs : SplitSet (p.R.Q (p.R.mu (D.plEq w)))`.

Take `⟨-, e, he, -⟩` from `hC.thP.vP j (p.R.mu (D.plEq w))`. Conclude with `SplitSet.mono ⟨e, he⟩ Finset.subset_union_right`. Establish `hl : ∀ P ∈ p.R.Q (p.R.mu (D.plEq w)), ((D.ntw.l (ex.nch.twI w) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal`. Introduce `P hP`. Break down `(hPA.2 P).1 (Or.inl hP) with hD | hQ` into its components or cases.

Establish `h1 : P ∈ (↑(D.ntw.pD (ex.nch.twI w)) : Set (Pl D.host.E))` using `hD`. Rewrite `h1` using `[D.ntw.pD_eq]`. Establish `hlp` using `(D.ntw.lPrime (ex.nch.twI w)).out`. Use `not_mem_of_coprime h1 ?_` and prove the remaining obligations. Use `split_ifs with h`.

Conclude with `(Nat.coprime_primes hlp D.host.pde'_prime).2 (by rw [h]; exact D.host.pde_ne)`. Conclude with `(Nat.coprime_primes hlp D.host.pde_prime).2 h`. Conclude with `fun hlP => Finset.disjoint_left.1 hok.2.1 hQ (D.ntw.twistExcludedPlaces_contains_residueChar _ hlP)`. Use `⟨hXs, hl, ?_⟩` and prove the remaining obligations. Take `⟨-, hadm, -⟩` from `GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ _ j (ex.nch.sd w) _ _ _ hok`.

Take `⟨R, -, hR, hRs⟩` from `hadm.1.split`. Establish `hYs` using `hRs.mono hR`. Establish `hXC : ∀ P, P ∈ p.R.Q (p.R.mu (D.plEq w)) ∪ (p.R.Q (p.R.mu (D.plEq w))).image Formalism.L2.DIV.conjPl ↔ (P ∈ D.ntw.pD (ex.nch.twI w) ∨ P ∈ ex.nch.Q w)` using `fun P => by`. Rewrite using `[← hPA.2 P, Finset.mem_union, Finset.mem_image]`. Use `or_congr Iff.rfl (exists_congr fun P' => and_congr Iff.rfl ?_)` and prove the remaining obligations.

Rewrite using `[lev_isConjPl_iff, eq_comm]`. Establish `hne : ∀ P, P ∈ D.ntw.pD (ex.nch.twI w) ∨ P ∈ ex.nch.Q w → Formalism.L2.DIV.conjPl P ≠ P` using `fun P hP e => by`. Break down `Finset.mem_union.1 ((hXC P).2 hP) with h | h` into its components or cases. Conclude with `Finset.disjoint_left.1 (disjoint_conj hXs) h (Finset.mem_image.2 ⟨P, h, e⟩)`. Take `⟨P', hP', rfl⟩` from `Finset.mem_image.1 h`.

Rewrite `e` using `[Formalism.L2.DIV.conjPl_conjPl]`. Conclude with `Finset.disjoint_left.1 (disjoint_conj hXs) hP' (Finset.mem_image.2 ⟨P', hP', e.symm⟩)`. Establish `hcl : ∀ P, P ∈ D.ntw.pD (ex.nch.twI w) ∨ P ∈ ex.nch.Q w → Formalism.L2.DIV.conjPl P ∈ D.ntw.pD (ex.nch.twI w) ∨ Formalism.L2.DIV.conjPl P ∈ ex.nch.Q w` using `fun P hP => by`. Rewrite `hP`, the goal using `[← hXC]`. Break down `Finset.mem_union.1 hP with h | h` into its components or cases.

Conclude with `Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)`. Take `⟨P', hP', rfl⟩` from `Finset.mem_image.1 h`. Rewrite using `[Formalism.L2.DIV.conjPl_conjPl]`. Conclude with `Finset.mem_union_left _ hP'`. Establish `hY : (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.Q ∪ (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).Q = half (ρ.ch (ex.nch.twI w)) (D.ntw.pD (ex.nch.twI w)) ∪ half (ρ.ch (ex.nch.twI w)) (ex.nch.Q w)`.

Rewrite using `[hρ.delta]`. Both sides reduce to the same expression. Rewrite `hYs`, the goal using `[hY]`. Conclude with `idem_add_cA_eq hXs hYs fun P => (hXC P).trans (mem_half_closure ((hρ.ch _).pair) hcl hne P).symm`.
-/
theorem placesSt_alt : _root_.GlobalTheory.BigOn.Exp.TupLe.PlacesCondition := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j hr hm w hw hok ρ hρ hpin _ _
  have hPA := placesAt (j := j) hw hρ hpin
  have hL := _root_.GlobalTheory.BigOn.links2_of_rows_alt _ _ _ _ _ _ _ _ _ _ p hr hm.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hXs : SplitSet (p.R.Q (p.R.mu (D.plEq w))) := by
    obtain ⟨-, e, he, -⟩ := hC.thP.vP j (p.R.mu (D.plEq w))
    exact SplitSet.mono ⟨e, he⟩ Finset.subset_union_right
  have hl : ∀ P ∈ p.R.Q (p.R.mu (D.plEq w)), ((D.ntw.l (ex.nch.twI w) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro P hP
    rcases (hPA.2 P).1 (Or.inl hP) with hD | hQ
    · have h1 : P ∈ (↑(D.ntw.pD (ex.nch.twI w)) : Set (Pl D.host.E)) := hD
      rw [D.ntw.pD_eq] at h1
      have hlp := (D.ntw.lPrime (ex.nch.twI w)).out
      refine not_mem_of_coprime h1 ?_
      split_ifs with h
      · exact (Nat.coprime_primes hlp D.host.pde'_prime).2 (by rw [h]; exact D.host.pde_ne)
      · exact (Nat.coprime_primes hlp D.host.pde_prime).2 h
    · exact fun hlP => Finset.disjoint_left.1 hok.2.1 hQ (D.ntw.twistExcludedPlaces_contains_residueChar _ hlP)
  refine ⟨hXs, hl, ?_⟩
  obtain ⟨-, hadm, -⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ _ j (ex.nch.sd w) _ _ _ hok
  obtain ⟨R, -, hR, hRs⟩ := hadm.1.split
  have hYs := hRs.mono hR
  have hXC : ∀ P, P ∈ p.R.Q (p.R.mu (D.plEq w)) ∪ (p.R.Q (p.R.mu (D.plEq w))).image Formalism.L2.DIV.conjPl ↔
      (P ∈ D.ntw.pD (ex.nch.twI w) ∨ P ∈ ex.nch.Q w) := fun P => by
    rw [← hPA.2 P, Finset.mem_union, Finset.mem_image]
    refine or_congr Iff.rfl (exists_congr fun P' => and_congr Iff.rfl ?_)
    rw [lev_isConjPl_iff, eq_comm]
  have hne : ∀ P, P ∈ D.ntw.pD (ex.nch.twI w) ∨ P ∈ ex.nch.Q w → Formalism.L2.DIV.conjPl P ≠ P := fun P hP e => by
    rcases Finset.mem_union.1 ((hXC P).2 hP) with h | h
    · exact Finset.disjoint_left.1 (disjoint_conj hXs) h (Finset.mem_image.2 ⟨P, h, e⟩)
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 h
      rw [Formalism.L2.DIV.conjPl_conjPl] at e
      exact Finset.disjoint_left.1 (disjoint_conj hXs) hP' (Finset.mem_image.2 ⟨P', hP', e.symm⟩)
  have hcl : ∀ P, P ∈ D.ntw.pD (ex.nch.twI w) ∨ P ∈ ex.nch.Q w →
      Formalism.L2.DIV.conjPl P ∈ D.ntw.pD (ex.nch.twI w) ∨ Formalism.L2.DIV.conjPl P ∈ ex.nch.Q w := fun P hP => by
    rw [← hXC] at hP ⊢
    rcases Finset.mem_union.1 hP with h | h
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 h
      rw [Formalism.L2.DIV.conjPl_conjPl]
      exact Finset.mem_union_left _ hP'
  have hY : (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.Q ∪
      (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).Q =
      half (ρ.ch (ex.nch.twI w)) (D.ntw.pD (ex.nch.twI w)) ∪ half (ρ.ch (ex.nch.twI w)) (ex.nch.Q w) := by
    rw [hρ.delta]
    rfl
  rw [hY] at hYs ⊢
  exact idem_add_cA_eq hXs hYs fun P =>
    (hXC P).trans (mem_half_closure ((hρ.ch _).pair) hcl hne P).symm
end GlobalTheory.BigOn.Exp.TupLe
end
end
