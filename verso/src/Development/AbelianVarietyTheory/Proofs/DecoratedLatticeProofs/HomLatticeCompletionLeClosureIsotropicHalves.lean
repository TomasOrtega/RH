import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HalfGen

variable {D : D7}

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp [GlobalTheory.FinPlLoc.pairA_zero]`. Consider the case `cons a l ih => simp [List.map_cons, List.sum_cons, ih, GlobalTheory.FinPlLoc.pairA_add, TensorProduct.add_tmul]`.
-/
theorem list_sum_pair {ι : Type} (l : List ι) (α : ι → Af D.host.F) :
    (l.map fun i => pairA D.host.F 0 (α i) ⊗ₜ[D.host.F] (1 : D.host.E)).sum =
      pairA D.host.F 0 (l.map α).sum ⊗ₜ[D.host.F] (1 : D.host.E) := by
  induction l with
  | nil => simp [GlobalTheory.FinPlLoc.pairA_zero]
  | cons a l ih => simp [List.map_cons, List.sum_cons, ih, GlobalTheory.FinPlLoc.pairA_add, TensorProduct.add_tmul]

/- English proof (translation)
Use `choose ε hε hεe using fun i => (p i).above`. Use `choose α hαe hα1 hα0 using hε`. Establish `hterm : ∀ i, (p i).e + cA D (p i).e = pairA D.host.F 0 (α i) ⊗ₜ[D.host.F] (1 : D.host.E)`. Introduce `i`. Rewrite using `[hεe i, hαe i]`.

Both sides reduce to the same expression. Rewrite using `[List.map_congr_left (fun i _ => hterm i), list_sum_pair]`. Unfold `GlobalTheory.FinPlLoc.idem`. Use `congr 2`. Use `RestrictedProduct.ext _ _ fun w => ?_` and prove the remaining obligations.

Use `show evalV D.host.F w (I.map α).sum = evalV D.host.F w (GlobalTheory.FinPlLoc.ePl D P)`. Rewrite using `[GlobalTheory.FinPlLoc.evalV_ePl, map_list_sum, List.map_map, ← List.sum_toFinset _ h.nodup]`. Distinguish the cases in `hw : P w`. Rewrite using `[if_pos hw]`. Take `⟨j, rfl⟩` from `(h.mem w).1 hw`.

Establish `hj : ∀ i, evalV D.host.F (p j).v (α i) = if i = j then 1 else 0`. Introduce `i`. Use `split_ifs with hij`. Substitute `hij` using the available equality. Conclude with `hα1 i`.

Conclude with `hα0 i _ fun hv => hij (h.inj hv.symm)`. Simplify using `only [Function.comp_apply, hj]`. Rewrite using `[Finset.sum_ite_eq' , if_pos (List.mem_toFinset.2 (h.all j))]`. Rewrite using `[if_neg hw]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations.

Conclude with `hα0 i w fun hv => hw ((h.mem w).2 ⟨i, hv⟩)`.
-/
theorem sum_splitIdem_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ι : Type} {p : ι → SplitPt D k} {I : List ι} {P : Pl D → Prop} (h : Places p I P) :
    (I.map fun i => (p i).e + cA D (p i).e).sum = GlobalTheory.FinPlLoc.idem D P := by
  classical
  choose ε hε hεe using fun i => (p i).above
  choose α hαe hα1 hα0 using hε
  have hterm : ∀ i, (p i).e + cA D (p i).e = pairA D.host.F 0 (α i) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    intro i
    rw [hεe i, hαe i]
    rfl
  rw [List.map_congr_left (fun i _ => hterm i), list_sum_pair]
  unfold GlobalTheory.FinPlLoc.idem
  congr 2
  refine RestrictedProduct.ext _ _ fun w => ?_
  show evalV D.host.F w (I.map α).sum = evalV D.host.F w (GlobalTheory.FinPlLoc.ePl D P)
  rw [GlobalTheory.FinPlLoc.evalV_ePl, map_list_sum, List.map_map, ← List.sum_toFinset _ h.nodup]
  by_cases hw : P w
  · rw [if_pos hw]
    obtain ⟨j, rfl⟩ := (h.mem w).1 hw
    have hj : ∀ i, evalV D.host.F (p j).v (α i) = if i = j then 1 else 0 := by
      intro i
      split_ifs with hij
      · subst hij; exact hα1 i
      · exact hα0 i _ fun hv => hij (h.inj hv.symm)
    simp only [Function.comp_apply, hj]
    rw [Finset.sum_ite_eq' , if_pos (List.mem_toFinset.2 (h.all j))]
  · rw [if_neg hw]
    refine Finset.sum_eq_zero fun i _ => ?_
    exact hα0 i w fun hv => hw ((h.mem w).2 ⟨i, hv⟩)

/- English proof (translation)
Take `⟨h1, h2, v, ε, hε, hsum⟩` from `he`. Use `⟨by rw [← map_mul, h1], ?_, v, ε, hε, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.DualPairCheck.cA_cA, mul_comm, h2]`. Rewrite using `[GlobalTheory.DualPairCheck.cA_cA, add_comm, hsum]`.
-/
theorem isSplitIdem_cA {e : AE D} (he : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hε, hsum⟩ := he
  refine ⟨by rw [← map_mul, h1], ?_, v, ε, hε, ?_⟩
  · rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, h2]
  · rw [GlobalTheory.DualPairCheck.cA_cA, add_comm, hsum]

/- English proof (translation)
Establish `hee : e * e = e` using `he.1`. Use `⟨GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT P e ?_ u hu, e, he, ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.AdIdem.idempotent_mem_intAE D (finPart D e) (by rw [← map_mul, hee])`. Rewrite using `[GlobalTheory.SplitScalar.isHalf_iff, smul_smul, hee]`.
-/
theorem smul_mem_halves {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : Pl D → Prop} {e : AE D} (he : IsSplitIdem D e) {u : WO S T} (hu : u ∈ latO S T LS LT P) :
    e • u ∈ {x | x ∈ latO S T LS LT P ∧ ∃ e, IsSplitIdem D e ∧ IsHalf e x} := by
  have hee : e * e = e := he.1
  refine ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT P e ?_ u hu, e, he, ?_⟩
  · exact GlobalTheory.AdIdem.idempotent_mem_intAE D (finPart D e) (by rw [← map_mul, hee])
  · rw [GlobalTheory.SplitScalar.isHalf_iff, smul_smul, hee]

/- English proof (translation)
Proceed by induction on `hu using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨α, -, hα, a, -, s, -, t, -, rfl⟩` from `hy`. Conclude with `fun i j => GlobalTheory.FinPlLoc.pair_mem_idAt P α hα _`. Consider the case `zero => exact fun i j => zero_mem _`.

Consider the case `add y z _ _ hy hz => exact fun i j => add_mem (hy i j) (hz i j)`. Consider the case `neg y _ hy => exact fun i j => neg_mem (hy i j)`.
-/
theorem entry_mem_idAt {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : Pl D → Prop} {u : WO S T} (hu : u ∈ latO S T LS LT P) : ∀ i j, u i j ∈ idAt D P := by
  induction hu using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, -, hα, a, -, s, -, t, -, rfl⟩ := hy
    exact fun i j => GlobalTheory.FinPlLoc.pair_mem_idAt P α hα _
  | zero => exact fun i j => zero_mem _
  | add y z _ _ hy hz => exact fun i j => add_mem (hy i j) (hz i j)
  | neg y _ hy => exact fun i j => neg_mem (hy i j)

/- English proof (translation)
Introduce `D k _ _ _ _ ι p I P h S T LS LT u hu`. Establish `hsum` using `sum_splitIdem_eq h`. Establish `hu' : GlobalTheory.FinPlLoc.idem D P • u = u`. Use extensionality with `i j`. Rewrite using `[Matrix.smul_apply, smul_eq_mul]`.

Conclude with `(GlobalTheory.FinPlLoc.mem_idAt_iff P _).1 (entry_mem_idAt hu i j)`. Establish `hdec : u = (I.map fun i => (p i).e • u + cA D (p i).e • u).sum` using `by conv_lhs => rw [← hu', ← hsum, List.sum_smul, List.map_map]`. Use `congr 1`. Use `List.map_congr_left fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, add_smul]`.

Rewrite using `[hdec]`. Use `AddSubgroup.list_sum_mem _ fun x hx => ?_` and prove the remaining obligations. Take `⟨i, -, rfl⟩` from `List.mem_map.1 hx`. Conclude with `add_mem (AddSubgroup.subset_closure (smul_mem_halves (p i).split hu)) (AddSubgroup.subset_closure (smul_mem_halves (isSplitIdem_cA (p i).split) hu))`.
-/
theorem latO_le_closure_halves : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)), ∀ u ∈ latO S T LS LT P, u ∈ AddSubgroup.closure {x | x ∈ latO S T LS LT P ∧ ∃ e, IsSplitIdem D e ∧ IsHalf e x} := by
  intro D k _ _ _ _ ι p I P h S T LS LT u hu
  have hsum := sum_splitIdem_eq h
  have hu' : GlobalTheory.FinPlLoc.idem D P • u = u := by
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact (GlobalTheory.FinPlLoc.mem_idAt_iff P _).1 (entry_mem_idAt hu i j)
  have hdec : u = (I.map fun i => (p i).e • u + cA D (p i).e • u).sum := by
    conv_lhs => rw [← hu', ← hsum, List.sum_smul, List.map_map]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply, add_smul]
  rw [hdec]
  refine AddSubgroup.list_sum_mem _ fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact add_mem (AddSubgroup.subset_closure (smul_mem_halves (p i).split hu))
    (AddSubgroup.subset_closure (smul_mem_halves (isSplitIdem_cA (p i).split) hu))

end GlobalTheory.HalfGen
