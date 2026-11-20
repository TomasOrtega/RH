import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Formalism.LocalToGlobal.GlobalTheory.ConcNWeight
import Formalism.PadicSubsetSums.StableGradedCounts.DominantNumbersEighthOfSharp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LemmaLSeriesWeightsOfGreenCuspidalParametrisatio
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Formalism.LocalToGlobal.GlobalTheory.ConcNP
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CovTop.LocShareNum

open Formalism.MainNotions.ArithmeticCylinders (admLq TieAdmG eUk eJk locShare goodAt VecAt IsLabel)
open Formalism.L2.GlobalTheoryTheory.ConcN (Wg SizesRec SizesAt weight_numbers_bound)
open Formalism.L2.GlobalTheoryTheory.ConcNWeight (RangeW host_facts sum_wtOf eUk_coeff_one_re_pos eJk_coeff_one_re_pos wtOf_eq_zero_of_not_label rangeW_of_sizes)

local instance factG {D : D7} (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

local instance neZeroG {D : D7} (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

/- English proof (translation)
Introduce `k` and use `⟨D.host.g_prime k, D.nd.g_split k, D.ntypes.g_Mray k, D.ntypes.g_cond k⟩`.
-/
theorem tieAdmG_rec (D : D7) : TieAdmG D := fun k =>
  ⟨D.host.g_prime k, D.nd.g_split k, D.ntypes.g_Mray k, D.ntypes.g_cond k⟩

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Set `eV : VecAt D` to `fun k _ => eUk D k (ψ₀ k)`. Establish `hv : ∀ (k : Fin 2) (v : D.nd.PlG k), eV k v = eUk D k (ψ₀ k) ∨ eV k v = eJk D k (ψ₀ k)` using `fun _ _ => Or.inl rfl`. Use `show locShare D eV k S ≤ _`. Take `⟨hnn, hsq, hcmp, -⟩` from `hL k (ψ₀ k) (hψ k)`. Take `⟨hq, hd, hqd, hq2, hd2, h16m, h16, hqg, hdg⟩` from `host_facts hA k`.

Set `wJ : D.nd.PlG k → (Fin D.R.r → ZMod (D.host.g k)) → ℝ` to `fun v c => Formalism.MainNotions.ArithmeticCylinders.wtOf D k (eV k v) (Formalism.CyclotomicNorms.monicOf c)`. Set `P : (Fin D.R.r → ZMod (D.host.g k)) → ℝ` to `fun c => Formalism.MainNotions.ArithmeticCylinders.wtOf D k (eUk D k (ψ₀ k)) (Formalism.CyclotomicNorms.monicOf c)`. Establish `hJnn : ∀ v f, 0 ≤ Formalism.MainNotions.ArithmeticCylinders.wtOf D k (eV k v) f`. Introduce `v f`. Apply the tactic sequence `rcases hv k v with h | h <;> rw [h]`.

Conclude with `(hnn f).1`. Conclude with `(hnn f).2`. Establish `hPnn : ∀ c, 0 ≤ P c` using `fun c => (hnn _).1`. Establish `hJsum : ∀ v, ∑ c, wJ v c = 1`. Introduce `v`.

Break down `hv k v with h | h` into its components or cases. Simplify using `only [wJ]`. Rewrite using `[h]`. Conclude with `sum_wtOf k _ (eUk_coeff_one_re_pos k _).ne'`. Simplify using `only [wJ]`.

Rewrite using `[h]`. Conclude with `sum_wtOf k _ (eJk_coeff_one_re_pos k _).ne'`. Establish `hPsum : ∑ c, P c = 1` using `sum_wtOf k _ (eUk_coeff_one_re_pos k _).ne'`. Establish `hg1 : (1 : ℝ) ≤ (D.host.g k : ℝ)` using `by exact_mod_cast (D.host.g_prime k).one_lt.le`. Establish `hcmpv : ∀ v c, (1 - 1 / (D.host.g k : ℝ)) * P c ≤ wJ v c`.

Introduce `v c`. Establish `hle : 1 - 1 / (D.host.g k : ℝ) ≤ 1` using `sub_le_self _ (by positivity)`. Break down `hv k v with h | h` into its components or cases. Establish `: wJ v c = P c` using `by simp only [wJ, P]; rw [h]`. Rewrite using `[this]`.

Conclude with `mul_le_of_le_one_left (hPnn c) hle`. Establish `: wJ v c = Formalism.MainNotions.ArithmeticCylinders.wtOf D k (eJk D k (ψ₀ k)) (Formalism.CyclotomicNorms.monicOf c)` using `by simp only [wJ]; rw [h]`. Rewrite using `[this]`. Distinguish the cases in `hlab : IsLabel D k (Formalism.CyclotomicNorms.monicOf c)`. Conclude with `hcmp _ hlab`.

Simplify using `only [P]`. Rewrite using `[wtOf_eq_zero_of_not_label _ hlab, wtOf_eq_zero_of_not_label _ hlab, mul_zero]`. Establish `hred : locShare D eV k S ≤ ∑ x ∈ (Finset.univ : Finset (D.nd.PlG k → Fin D.R.r → ZMod (D.host.g k))).filter (fun x => ¬ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.GoodAt (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) D.R.r (fun v => Formalism.Irre …`. Unfold `locShare`. Set `cv : Formalism.MainNotions.ArithmeticCylinders.Tup D k → (D.nd.PlG k → Fin D.R.r → ZMod (D.host.g k))` to `fun t v i => (t v).coeff i`.

Establish `hS' : ∑ t ∈ S, ∏ v, Formalism.MainNotions.ArithmeticCylinders.wtOf D k (eV k v) (t v) = ∑ t ∈ S.filter (fun t => ∀ v, IsLabel D k (t v)), ∏ v, Formalism.MainNotions.ArithmeticCylinders.wtOf D k (eV k v) (t v)`. Rewrite using `[Finset.sum_filter_of_ne]`. Introduce `t _ hne v`. Assume the negation of the conclusion as `hv'`. Conclude with `hne (Finset.prod_eq_zero (Finset.mem_univ v) (wtOf_eq_zero_of_not_label _ hv'))`.

Establish `hcv : ∀ t : Formalism.MainNotions.ArithmeticCylinders.Tup D k, (∀ v, IsLabel D k (t v)) → ∀ v, Formalism.CyclotomicNorms.monicOf (cv t v) = t v` using `fun t ht v => Formalism.CyclotomicNorms.Sqf.monicOf_coeffs (t v) (ht v).1 (ht v).2.1`. Rewrite using `[hS']`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun t ht => ?_` and prove the remaining obligations. Establish `ht` using `(Finset.mem_filter.1 ht).2`.

Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Simplify using `only [wJ]`. Rewrite using `[hcv t ht v]`. Use `_ = ∑ x ∈ (S.filter (fun t => ∀ v, IsLabel D k (t v))).image cv, ∏ v, wJ v (x v) := by`. Rewrite using `[Finset.sum_image]`.

Introduce `t ht t' ht' h`. Establish `ht` using `(Finset.mem_filter.1 ht).2`. Establish `ht'` using `(Finset.mem_filter.1 ht').2`. Use function extensionality and compare the values at `v`. Rewrite using `[← hcv t ht v, ← hcv t' ht' v]`.

Conclude with `congrArg Formalism.CyclotomicNorms.monicOf (congrFun h v)`. Use `_ ≤ _ := by`. Use `Finset.sum_le_sum_of_subset_of_nonneg ?_ fun x _ _ => Finset.prod_nonneg fun v _ => hJnn v _` and prove the remaining obligations. Introduce `x hx`. Take `⟨t, ht, rfl⟩` from `Finset.mem_image.1 hx`.

Take `⟨htS, htl⟩` from `Finset.mem_filter.1 ht`. Use `Finset.mem_filter.2 ⟨Finset.mem_univ _, fun hgood => hS t htS ?_⟩` and prove the remaining obligations. Establish `hfun : (fun v => Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf (cv t v)) = t` using `funext fun v => hcv t htl v`. Rewrite `hgood` using `[hfun]`. Conclude with `Formalism.MainNotions.N.PlaceLabelTeichmuller.good_of D.R.r t (D.nd.chiT k) hgood`.

Establish `hT` using `Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.comparison_transfer_holds (D.nd.PlG k) (fun _ => Fin D.R.r → ZMod (D.host.g k)) (fun _ => P) wJ (D.host.g k : ℝ) ((Finset.univ : Finset (D.nd.PlG k → Fin D.R.r → ZMod (D.host.g k))).filter (fun x => ¬ Formalism.IrreducibleC …`. Establish `hW` using `Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.property_W_of_estimates (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (D.nd.PlG k) (Fin D.R.m) D.R.r D.host.q D.host.d (D.nd.chiT k) P hR.1 (by rw [ZMod.card]; exact hR.2 k) hq hd hqd hq2 hd2 h16m (by rw …`. Introduce `c hc`. Establish `hc' : c ∈ (Finset.univ : Finset (Fin D.R.r → ZMod (D.host.g k))).filter (fun c => Squarefree (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c) ∧ (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c).coeff 0 ≠ 0)`. Unfold `Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.sqSet at hc`.

Use `hc` and compare the differences between its conclusion and the goal. Take `⟨-, hsqf, h0⟩` from `Finset.mem_filter.1 hc'`. Establish `hlab : IsLabel D k (Formalism.CyclotomicNorms.monicOf c)` using `⟨Formalism.CyclotomicNorms.Sqf.monic_monicOf c, Formalism.CyclotomicNorms.Sqf.natDegree_monicOf c, h0⟩`. Use `show Formalism.MainNotions.ArithmeticCylinders.wtOf D k (eUk D k (ψ₀ k)) (Formalism.CyclotomicNorms.monicOf c) = _`. Rewrite using `[hsq _ hlab hsqf, Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.sqWeight, ZMod.card, one_div, ← Multiset.prod_map_inv]`.

Apply the tactic sequence `convert rfl <;> rfl)`. Use `le_trans hred (le_trans hT ?_)` and prove the remaining obligations. Use `le_trans (add_le_add hW le_rfl) (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[ZMod.card, D.nd.card_PlG k, Fintype.card_fin]`. Unfold `Wg`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem locShare_eUk_le_Wg {D : D7} (hL : admLq D) (hA : TieAdmG D) (hR : RangeW D)
    (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ) (hψ : ∀ k, ψ₀ k ≠ 1)
    (k : Fin 2) (S : Finset (Formalism.MainNotions.ArithmeticCylinders.Tup D k)) (hS : ∀ t ∈ S, ¬ goodAt D k t) :
    locShare D (fun k _ => eUk D k (ψ₀ k)) k S ≤ Wg D.R.f D.R.m D.R.r (D.host.g k) D.host.q D.host.d := by
  classical
  let eV : VecAt D := fun k _ => eUk D k (ψ₀ k)
  have hv : ∀ (k : Fin 2) (v : D.nd.PlG k), eV k v = eUk D k (ψ₀ k) ∨ eV k v = eJk D k (ψ₀ k) :=
    fun _ _ => Or.inl rfl
  show locShare D eV k S ≤ _
  obtain ⟨hnn, hsq, hcmp, -⟩ := hL k (ψ₀ k) (hψ k)
  obtain ⟨hq, hd, hqd, hq2, hd2, h16m, h16, hqg, hdg⟩ := host_facts hA k
  let wJ : D.nd.PlG k → (Fin D.R.r → ZMod (D.host.g k)) → ℝ :=
    fun v c => Formalism.MainNotions.ArithmeticCylinders.wtOf D k (eV k v) (Formalism.CyclotomicNorms.monicOf c)
  let P : (Fin D.R.r → ZMod (D.host.g k)) → ℝ := fun c => Formalism.MainNotions.ArithmeticCylinders.wtOf D k (eUk D k (ψ₀ k)) (Formalism.CyclotomicNorms.monicOf c)
  have hJnn : ∀ v f, 0 ≤ Formalism.MainNotions.ArithmeticCylinders.wtOf D k (eV k v) f := by
    intro v f
    rcases hv k v with h | h <;> rw [h]
    · exact (hnn f).1
    · exact (hnn f).2
  have hPnn : ∀ c, 0 ≤ P c := fun c => (hnn _).1
  have hJsum : ∀ v, ∑ c, wJ v c = 1 := by
    intro v
    rcases hv k v with h | h
    · simp only [wJ]; rw [h]; exact sum_wtOf k _ (eUk_coeff_one_re_pos k _).ne'
    · simp only [wJ]; rw [h]; exact sum_wtOf k _ (eJk_coeff_one_re_pos k _).ne'
  have hPsum : ∑ c, P c = 1 := sum_wtOf k _ (eUk_coeff_one_re_pos k _).ne'
  have hg1 : (1 : ℝ) ≤ (D.host.g k : ℝ) := by exact_mod_cast (D.host.g_prime k).one_lt.le
  have hcmpv : ∀ v c, (1 - 1 / (D.host.g k : ℝ)) * P c ≤ wJ v c := by
    intro v c
    have hle : 1 - 1 / (D.host.g k : ℝ) ≤ 1 := sub_le_self _ (by positivity)
    rcases hv k v with h | h
    · have : wJ v c = P c := by simp only [wJ, P]; rw [h]
      rw [this]
      exact mul_le_of_le_one_left (hPnn c) hle
    · have : wJ v c = Formalism.MainNotions.ArithmeticCylinders.wtOf D k (eJk D k (ψ₀ k)) (Formalism.CyclotomicNorms.monicOf c) := by simp only [wJ]; rw [h]
      rw [this]
      by_cases hlab : IsLabel D k (Formalism.CyclotomicNorms.monicOf c)
      · exact hcmp _ hlab
      · simp only [P]
        rw [wtOf_eq_zero_of_not_label _ hlab, wtOf_eq_zero_of_not_label _ hlab, mul_zero]
  have hred : locShare D eV k S ≤
      ∑ x ∈ (Finset.univ : Finset (D.nd.PlG k → Fin D.R.r → ZMod (D.host.g k))).filter
        (fun x => ¬ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.GoodAt (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) D.R.r
          (fun v => Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf (x v)) (D.nd.chiT k)), ∏ v, wJ v (x v) := by
    unfold locShare
    let cv : Formalism.MainNotions.ArithmeticCylinders.Tup D k → (D.nd.PlG k → Fin D.R.r → ZMod (D.host.g k)) := fun t v i => (t v).coeff i
    have hS' : ∑ t ∈ S, ∏ v, Formalism.MainNotions.ArithmeticCylinders.wtOf D k (eV k v) (t v) =
        ∑ t ∈ S.filter (fun t => ∀ v, IsLabel D k (t v)), ∏ v, Formalism.MainNotions.ArithmeticCylinders.wtOf D k (eV k v) (t v) := by
      rw [Finset.sum_filter_of_ne]
      intro t _ hne v
      by_contra hv'
      exact hne (Finset.prod_eq_zero (Finset.mem_univ v) (wtOf_eq_zero_of_not_label _ hv'))
    have hcv : ∀ t : Formalism.MainNotions.ArithmeticCylinders.Tup D k, (∀ v, IsLabel D k (t v)) → ∀ v, Formalism.CyclotomicNorms.monicOf (cv t v) = t v :=
      fun t ht v => Formalism.CyclotomicNorms.Sqf.monicOf_coeffs (t v) (ht v).1 (ht v).2.1
    rw [hS']
    calc ∑ t ∈ S.filter (fun t => ∀ v, IsLabel D k (t v)), ∏ v, Formalism.MainNotions.ArithmeticCylinders.wtOf D k (eV k v) (t v)
        = ∑ t ∈ S.filter (fun t => ∀ v, IsLabel D k (t v)), ∏ v, wJ v (cv t v) := by
          refine Finset.sum_congr rfl fun t ht => ?_
          have ht := (Finset.mem_filter.1 ht).2
          refine Finset.prod_congr rfl fun v _ => ?_
          simp only [wJ]
          rw [hcv t ht v]
      _ = ∑ x ∈ (S.filter (fun t => ∀ v, IsLabel D k (t v))).image cv, ∏ v, wJ v (x v) := by
          rw [Finset.sum_image]
          intro t ht t' ht' h
          have ht := (Finset.mem_filter.1 ht).2
          have ht' := (Finset.mem_filter.1 ht').2
          funext v
          rw [← hcv t ht v, ← hcv t' ht' v]
          exact congrArg Formalism.CyclotomicNorms.monicOf (congrFun h v)
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_
            fun x _ _ => Finset.prod_nonneg fun v _ => hJnn v _
          intro x hx
          obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hx
          obtain ⟨htS, htl⟩ := Finset.mem_filter.1 ht
          refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun hgood => hS t htS ?_⟩
          have hfun : (fun v => Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf (cv t v)) = t := funext fun v => hcv t htl v
          rw [hfun] at hgood
          exact Formalism.MainNotions.N.PlaceLabelTeichmuller.good_of D.R.r t (D.nd.chiT k) hgood
  have hT := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.comparison_transfer_holds (D.nd.PlG k) (fun _ => Fin D.R.r → ZMod (D.host.g k))
    (fun _ => P) wJ (D.host.g k : ℝ)
    ((Finset.univ : Finset (D.nd.PlG k → Fin D.R.r → ZMod (D.host.g k))).filter
        (fun x => ¬ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.GoodAt (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) D.R.r
          (fun v => Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf (x v)) (D.nd.chiT k)))
    hg1 (fun _ => hPnn) (fun _ => hPsum) hJsum hcmpv
  have hW := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.property_W_of_estimates (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (D.nd.PlG k)
    (Fin D.R.m) D.R.r D.host.q D.host.d (D.nd.chiT k) P hR.1 (by rw [ZMod.card]; exact hR.2 k) hq hd hqd hq2
    hd2 h16m (by rw [ZMod.card]; exact h16) (by rw [ZMod.card]; exact hqg) (by rw [ZMod.card]; exact hdg)
    hPnn hPsum (by
      intro c hc
      have hc' : c ∈ (Finset.univ : Finset (Fin D.R.r → ZMod (D.host.g k))).filter
          (fun c => Squarefree (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c) ∧ (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c).coeff 0 ≠ 0) := by
        unfold Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.sqSet at hc
        convert hc
      obtain ⟨-, hsqf, h0⟩ := Finset.mem_filter.1 hc'
      have hlab : IsLabel D k (Formalism.CyclotomicNorms.monicOf c) :=
        ⟨Formalism.CyclotomicNorms.Sqf.monic_monicOf c, Formalism.CyclotomicNorms.Sqf.natDegree_monicOf c, h0⟩
      show Formalism.MainNotions.ArithmeticCylinders.wtOf D k (eUk D k (ψ₀ k)) (Formalism.CyclotomicNorms.monicOf c) = _
      rw [hsq _ hlab hsqf, Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.sqWeight, ZMod.card, one_div, ← Multiset.prod_map_inv]
      convert rfl <;> rfl)
  refine le_trans hred (le_trans hT ?_)
  refine le_trans (add_le_add hW le_rfl) (le_of_eq ?_)
  rw [ZMod.card, D.nd.card_PlG k, Fintype.card_fin]
  unfold Wg
  ring

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨hN, -, hK, -, -, -, hQD, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -, -⟩` from `Fm.sizes x hx i`. Establish `hLx : (Fm.L x i).sc.x = x` using `Fm.L_x x i hx`. Establish `hLe : (Fm.L x i).sc.eps = eps` using `Fm.L_eps x i`. Establish `hε0 : 0 < eps` using `hLe ▸ (Fm.L x i).sc.eps_pos`. Establish `hε1 : eps < 1 / 52` using `hLe ▸ (Fm.L x i).sc.eps_lt`.

Establish `hx1 : (1 : ℝ) ≤ x` using `by linarith`. Establish `hx0 : (0 : ℝ) < x` using `by linarith`. Establish `hLz : (Fm.L x i).sc.ez = Fm.ez` using `Fm.toFamCore.L_ez x i`. Establish `hz0 : 0 < Fm.ez` using `div_pos hε0 (lt_of_lt_of_le one_pos Fm.toFamCore.one_le_J)`. Establish `hzle : Fm.ez ≤ eps` using `div_le_self hε0.le Fm.toFamCore.one_le_J`.

Simplify using `only [SizeN, SizeK, SizeQD, SizeG, szTh, hLx, hLe, hLz] at hN hK hQD hG`. Establish `hf : ((Fm.D x i).R.f : ℝ) = 2 * ((Fm.D x i).R.n : ℝ)` using `by simp [Ranks.f]`. Establish `hfk : (Fm.D x i).R.f ≤ (Fm.D x i).R.k`. Use `(Fm.D x i).R.f_le_k` as an intermediate fact. Simplify `this` using `[Ranks.f, Ranks.n]`.

Establish `hmf : (Fm.D x i).R.m ≤ (Fm.D x i).R.f`. Use `(Fm.D x i).R.m_le_f` as an intermediate fact. Simplify `this` using `[Ranks.f, Ranks.n]`. Establish `hm2 : 2 ≤ (Fm.D x i).R.m` using `(Fm.D x i).R.two_le_m`. Establish `hrk : (Fm.D x i).R.k ≤ (Fm.D x i).R.r` using `by unfold Ranks.r; omega`.

Establish `hr2k : (Fm.D x i).R.r ≤ 2 * (Fm.D x i).R.k` using `by unfold Ranks.r; omega`. Establish `h5 : x ^ (9 / 2 + 10 * eps + eps / 100) ≤ x ^ (5 : ℝ)` using `Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)`. Establish `h56 : x ^ (5 : ℝ) ≤ x ^ Cs` using `Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)`. Establish `h6 : x ^ (6 : ℝ) ≤ x ^ Cs` using `Real.rpow_le_rpow_of_exponent_le hx1 hCs`. Establish `h4 : x ^ (4 : ℝ) ≤ x ^ (9 / 2 + 10 * eps - eps / 100)` using `Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)`.

Establish `h2 : x ^ (2 : ℝ) ≤ x ^ (2 + 8 * eps - eps / 100)` using `Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)`. Establish `hx4p : (256 : ℝ) ≤ x ^ (4 : ℝ)`. Rewrite using `[show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]`. Establish `: (4 : ℝ) ^ 4 ≤ x ^ 4` using `pow_le_pow_left₀ (by norm_num) hx4 4`. Evaluate the numerical expressions using `at this ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hx65 : 2 * x ^ (5 : ℝ) ≤ x ^ (6 : ℝ)`. Rewrite using `[show (6 : ℝ) = 5 + 1 by norm_num, Real.rpow_add hx0, Real.rpow_one]`. Establish `h0 : 0 ≤ x ^ (5 : ℝ)` using `Real.rpow_nonneg hx0.le _`. Use `mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ x by linarith) h0` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hkx : ((Fm.D x i).R.k : ℝ) ≤ x ^ (5 : ℝ)` using `le_trans hK.2 h5`. Establish `hkl : (256 : ℝ) ≤ (Fm.D x i).R.k` using `le_trans (le_trans hx4p h4) hK.1`. Establish `hfkR : ((Fm.D x i).R.f : ℝ) ≤ (Fm.D x i).R.k` using `by exact_mod_cast hfk`. Establish `hmfR : ((Fm.D x i).R.m : ℝ) ≤ (Fm.D x i).R.f` using `by exact_mod_cast hmf`.

Establish `hr2kR : ((Fm.D x i).R.r : ℝ) ≤ 2 * (Fm.D x i).R.k` using `by exact_mod_cast hr2k`. Establish `hrkR : ((Fm.D x i).R.k : ℝ) ≤ (Fm.D x i).R.r` using `by exact_mod_cast hrk`. Establish `hεq : x ^ (Fm.ez / 6) ≤ x ^ (Fm.ez / 5 - Fm.ez / 100)` using `Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)`. Establish `hpos6 : 0 < x ^ (Fm.ez / 6)` using `Real.rpow_pos_of_pos hx0 _`. Establish `hq : Real.exp (x ^ (Fm.ez / 6)) ≤ ((Fm.D x i).host.q : ℝ)`.

Establish `hl` using `hQD.1`. Establish `hq0 : (0 : ℝ) < (Fm.D x i).host.q`. Break down `Nat.eq_zero_or_pos (Fm.D x i).host.q with h0 | h0` into its components or cases. Rewrite `hl` using `[h0]`. Simplify using `at hl`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `h0` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation. Establish `hd : Real.exp (x ^ (Fm.ez / 6)) ≤ ((Fm.D x i).host.d : ℝ)`. Establish `hl : x ^ (Fm.ez / 6) ≤ Real.log (Fm.D x i).host.d` using `le_trans hεq hQD.2.2.2.1`.

Establish `hd0 : (0 : ℝ) < (Fm.D x i).host.d`. Break down `Nat.eq_zero_or_pos (Fm.D x i).host.d with h0 | h0` into its components or cases. Rewrite `hl` using `[h0]`. Simplify using `at hl`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `h0` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation. Introduce `j`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hg` using `(hG j j).1`.

Establish `hb : Real.exp (8 * x ^ eps) = (Real.exp (x ^ eps)) ^ 8`. Rewrite using `[← Real.exp_nat_mul]`. Evaluate the numerical expressions. Establish `hb0 : 0 ≤ Real.exp (x ^ eps)` using `(Real.exp_pos _).le`. Establish `hkb : Real.exp (x ^ eps) ≤ ((Fm.D x i).R.k : ℝ) * Real.exp (x ^ eps)`.

Establish `: (1 : ℝ) ≤ (Fm.D x i).R.k` using `by linarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `hsc : (Fm.L x i).sc.b = Real.exp (x ^ eps)`. Rewrite using `[show (Fm.L x i).sc.b = Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) from rfl, hLx, hLe]`. Rewrite `hg` using `[hsc]`.

Establish `hze : x ^ Fm.ez ≤ x ^ eps` using `Real.rpow_le_rpow_of_exponent_le hx1 hzle`. Use `le_trans (Real.exp_le_exp.2 (by linarith : 8 * x ^ Fm.ez ≤ 8 * x ^ eps)) ?_` and prove the remaining obligations. Rewrite using `[hb]`. Conclude with `le_trans (pow_le_pow_left₀ hb0 hkb 8) hg`. Rewrite using `[← Real.rpow_two]`.

Establish `hn0 : (0 : ℝ) ≤ (Fm.D x i).R.n` using `Nat.cast_nonneg _`. Establish `hnf : ((Fm.D x i).R.n : ℝ) ≤ (Fm.D x i).R.f` using `by rw [hf]; linarith`. Conclude with `le_trans h2 (le_trans hN.1 hnf)`. Conclude with `le_trans hfkR (le_trans hkx h56)`. Conclude with `le_trans hmfR (le_trans hfkR (le_trans hkx h56))`.

Establish `h256 : 256 ≤ (Fm.D x i).R.k` using `by exact_mod_cast hkl`. Use linear arithmetic over natural numbers and integers. Establish `h2k : 2 * ((Fm.D x i).R.k : ℝ) ≤ 2 * x ^ (5 : ℝ)` using `mul_le_mul_of_nonneg_left hkx (by norm_num)`. Conclude with `le_trans hr2kR (le_trans h2k (le_trans hx65 h6))`. Rewrite using `[Nat.cast_min]`.

Conclude with `le_min hq hd`.
-/
theorem sizesRec_at_point {eps : ℝ} (Fm : FamP eps) {x : ℝ} (hx : Fm.x1 < x) (hx4 : 4 ≤ x) (i : Fm.Ix x) {Cs : ℝ}
    (hCs : 6 ≤ Cs) : SizesRec (Fm.D x i) x Fm.ez Cs := by
  obtain ⟨hN, -, hK, -, -, -, hQD, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -, -⟩ := Fm.sizes x hx i
  have hLx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
  have hLe : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have hε0 : 0 < eps := hLe ▸ (Fm.L x i).sc.eps_pos
  have hε1 : eps < 1 / 52 := hLe ▸ (Fm.L x i).sc.eps_lt
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hLz : (Fm.L x i).sc.ez = Fm.ez := Fm.toFamCore.L_ez x i
  have hz0 : 0 < Fm.ez := div_pos hε0 (lt_of_lt_of_le one_pos Fm.toFamCore.one_le_J)
  have hzle : Fm.ez ≤ eps := div_le_self hε0.le Fm.toFamCore.one_le_J
  simp only [SizeN, SizeK, SizeQD, SizeG, szTh, hLx, hLe, hLz] at hN hK hQD hG

  have hf : ((Fm.D x i).R.f : ℝ) = 2 * ((Fm.D x i).R.n : ℝ) := by simp [Ranks.f]
  have hfk : (Fm.D x i).R.f ≤ (Fm.D x i).R.k := by
    have := (Fm.D x i).R.f_le_k
    simpa [Ranks.f, Ranks.n] using this
  have hmf : (Fm.D x i).R.m ≤ (Fm.D x i).R.f := by
    have := (Fm.D x i).R.m_le_f
    simpa [Ranks.f, Ranks.n] using this
  have hm2 : 2 ≤ (Fm.D x i).R.m := (Fm.D x i).R.two_le_m
  have hrk : (Fm.D x i).R.k ≤ (Fm.D x i).R.r := by unfold Ranks.r; omega
  have hr2k : (Fm.D x i).R.r ≤ 2 * (Fm.D x i).R.k := by unfold Ranks.r; omega

  have h5 : x ^ (9 / 2 + 10 * eps + eps / 100) ≤ x ^ (5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h56 : x ^ (5 : ℝ) ≤ x ^ Cs := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h6 : x ^ (6 : ℝ) ≤ x ^ Cs := Real.rpow_le_rpow_of_exponent_le hx1 hCs
  have h4 : x ^ (4 : ℝ) ≤ x ^ (9 / 2 + 10 * eps - eps / 100) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h2 : x ^ (2 : ℝ) ≤ x ^ (2 + 8 * eps - eps / 100) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hx4p : (256 : ℝ) ≤ x ^ (4 : ℝ) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have : (4 : ℝ) ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) hx4 4
    norm_num at this ⊢; linarith
  have hx65 : 2 * x ^ (5 : ℝ) ≤ x ^ (6 : ℝ) := by
    rw [show (6 : ℝ) = 5 + 1 by norm_num, Real.rpow_add hx0, Real.rpow_one]
    have h0 : 0 ≤ x ^ (5 : ℝ) := Real.rpow_nonneg hx0.le _
    have := mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ x by linarith) h0
    linarith
  have hkx : ((Fm.D x i).R.k : ℝ) ≤ x ^ (5 : ℝ) := le_trans hK.2 h5
  have hkl : (256 : ℝ) ≤ (Fm.D x i).R.k := le_trans (le_trans hx4p h4) hK.1
  have hfkR : ((Fm.D x i).R.f : ℝ) ≤ (Fm.D x i).R.k := by exact_mod_cast hfk
  have hmfR : ((Fm.D x i).R.m : ℝ) ≤ (Fm.D x i).R.f := by exact_mod_cast hmf
  have hr2kR : ((Fm.D x i).R.r : ℝ) ≤ 2 * (Fm.D x i).R.k := by exact_mod_cast hr2k
  have hrkR : ((Fm.D x i).R.k : ℝ) ≤ (Fm.D x i).R.r := by exact_mod_cast hrk

  have hεq : x ^ (Fm.ez / 6) ≤ x ^ (Fm.ez / 5 - Fm.ez / 100) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hpos6 : 0 < x ^ (Fm.ez / 6) := Real.rpow_pos_of_pos hx0 _
  have hq : Real.exp (x ^ (Fm.ez / 6)) ≤ ((Fm.D x i).host.q : ℝ) := by
    have hl := hQD.1
    have hq0 : (0 : ℝ) < (Fm.D x i).host.q := by
      rcases Nat.eq_zero_or_pos (Fm.D x i).host.q with h0 | h0
      · rw [h0] at hl; simp at hl; linarith
      · exact_mod_cast h0
    calc Real.exp (x ^ (Fm.ez / 6)) ≤ Real.exp (Real.log (Fm.D x i).host.q) := Real.exp_le_exp.2 hl
      _ = (Fm.D x i).host.q := Real.exp_log hq0
  have hd : Real.exp (x ^ (Fm.ez / 6)) ≤ ((Fm.D x i).host.d : ℝ) := by
    have hl : x ^ (Fm.ez / 6) ≤ Real.log (Fm.D x i).host.d := le_trans hεq hQD.2.2.2.1
    have hd0 : (0 : ℝ) < (Fm.D x i).host.d := by
      rcases Nat.eq_zero_or_pos (Fm.D x i).host.d with h0 | h0
      · rw [h0] at hl; simp at hl; linarith
      · exact_mod_cast h0
    calc Real.exp (x ^ (Fm.ez / 6)) ≤ Real.exp (Real.log (Fm.D x i).host.d) := Real.exp_le_exp.2 hl
      _ = (Fm.D x i).host.d := Real.exp_log hd0
  intro j
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hg := (hG j j).1
    have hb : Real.exp (8 * x ^ eps) = (Real.exp (x ^ eps)) ^ 8 := by
      rw [← Real.exp_nat_mul]; norm_num
    have hb0 : 0 ≤ Real.exp (x ^ eps) := (Real.exp_pos _).le
    have hkb : Real.exp (x ^ eps) ≤ ((Fm.D x i).R.k : ℝ) * Real.exp (x ^ eps) := by
      have : (1 : ℝ) ≤ (Fm.D x i).R.k := by linarith
      nlinarith
    have hsc : (Fm.L x i).sc.b = Real.exp (x ^ eps) := by
      rw [show (Fm.L x i).sc.b = Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) from rfl, hLx, hLe]
    rw [hsc] at hg
    have hze : x ^ Fm.ez ≤ x ^ eps := Real.rpow_le_rpow_of_exponent_le hx1 hzle
    refine le_trans (Real.exp_le_exp.2 (by linarith : 8 * x ^ Fm.ez ≤ 8 * x ^ eps)) ?_
    rw [hb]
    exact le_trans (pow_le_pow_left₀ hb0 hkb 8) hg
  ·
    rw [← Real.rpow_two]
    have hn0 : (0 : ℝ) ≤ (Fm.D x i).R.n := Nat.cast_nonneg _
    have hnf : ((Fm.D x i).R.n : ℝ) ≤ (Fm.D x i).R.f := by rw [hf]; linarith
    exact le_trans h2 (le_trans hN.1 hnf)
  · exact le_trans hfkR (le_trans hkx h56)
  · exact le_trans hmfR (le_trans hfkR (le_trans hkx h56))
  ·
    have h256 : 256 ≤ (Fm.D x i).R.k := by exact_mod_cast hkl
    omega
  · have h2k : 2 * ((Fm.D x i).R.k : ℝ) ≤ 2 * x ^ (5 : ℝ) := mul_le_mul_of_nonneg_left hkx (by norm_num)
    exact le_trans hr2kR (le_trans h2k (le_trans hx65 h6))
  · rw [Nat.cast_min]
    exact le_min hq hd

end GlobalTheory.CovTop.LocShareNum

namespace GlobalTheory.CovTop.LocShareNum

open Formalism.MainNotions.ArithmeticCylinders (admLq TieAdmG eUk eJk locShare goodAt VecAt IsLabel)
open Formalism.L2.GlobalTheoryTheory.ConcN (Wg SizesRec SizesAt weight_numbers_bound)
open Formalism.L2.GlobalTheoryTheory.ConcNWeight (RangeW rangeW_of_sizes)

/- English proof (translation)
Assemble the required witnesses or components as `⟨(D.host.g_prime k).ne_zero⟩ (ZMod.stdAddChar : AddChar (ZMod (D.host.g k)) ℂ) ≠ 1 := by haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩ haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩ have h := ZMod.isPrimitive_stdAddChar (D.host.g k) (one_ne_zero : (1 : ZMod ( …`.
-/
theorem stdAddChar_ne_one (D : D7) (k : Fin 2) :
    haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
    (ZMod.stdAddChar : AddChar (ZMod (D.host.g k)) ℂ) ≠ 1 := by
  haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have h := ZMod.isPrimitive_stdAddChar (D.host.g k) (one_ne_zero : (1 : ZMod (D.host.g k)) ≠ 0)
  rwa [AddChar.mulShift_one] at h

/- English proof (translation)
Take `⟨a, ha⟩` from `Filter.eventually_atTop.1 (weight_numbers_bound eps 6 he he1)`. Take `⟨b, hb⟩` from `Filter.eventually_atTop.1 (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.dominant_numbers_sharp_holds (3 * 6 + 3) eps he)`. Use `⟨max a b, fun x hx D hS => ?_⟩` and prove the remaining obligations. Establish `h0` using `ha x (le_trans (le_max_left _ _) hx) _ _ _ _ _ _ (hS 0)`. Establish `h1` using `ha x (le_trans (le_max_left _ _) hx) _ _ _ _ _ _ (hS 1)`.

Establish `h2` using `hb x (le_trans (le_max_right _ _) hx)`. Establish `hE : 0 ≤ Real.exp (-(x ^ (eps / 7)))` using `(Real.exp_pos _).le`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem wg_sum_le (eps : ℝ) (he : 0 < eps) (he1 : eps ≤ 1) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ D : D7, SizesRec D x eps 6 →
      Wg D.R.f D.R.m D.R.r (D.host.g 0) D.host.q D.host.d + Wg D.R.f D.R.m D.R.r (D.host.g 1) D.host.q D.host.d
        ≤ Real.exp (-(x ^ (eps / 7))) := by
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 (weight_numbers_bound eps 6 he he1)
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.1 (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.dominant_numbers_sharp_holds (3 * 6 + 3) eps he)
  refine ⟨max a b, fun x hx D hS => ?_⟩
  have h0 := ha x (le_trans (le_max_left _ _) hx) _ _ _ _ _ _ (hS 0)
  have h1 := ha x (le_trans (le_max_left _ _) hx) _ _ _ _ _ _ (hS 1)
  have h2 := hb x (le_trans (le_max_right _ _) hx)
  have hE : 0 ≤ Real.exp (-(x ^ (eps / 7))) := (Real.exp_pos _).le
  linarith

/- English proof (translation)
Introduce `_hP hG`. Use `⟨1 / 52, by norm_num, fun eps he he1 => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ⟨0, le_rfl, ?_⟩⟩⟩` and prove the remaining obligations. Establish `hez : 0 < Fm.ez` using `div_pos he (lt_of_lt_of_le one_pos Fm.toFamCore.one_le_J)`. Establish `hez1 : Fm.ez ≤ 1` using `le_trans (div_le_self he.le Fm.toFamCore.one_le_J) (by linarith)`. Take `⟨a, ha⟩` from `wg_sum_le Fm.ez hez hez1`.

Use `⟨max (max a (Fm.x1 + 1)) (max 4 ((3 / 2 : ℝ) ^ (1 / Fm.ez))), fun x hx hle ι p hp _ => ?_⟩` and prove the remaining obligations. Establish `hx4 : 4 ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hle`. Establish `hxa : a ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hle`. Establish `hx1 : (3 / 2 : ℝ) ^ (1 / Fm.ez) ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hle`. Establish `hxe : 3 / 2 ≤ x ^ Fm.ez`.

Establish `hpos : 0 ≤ (3 / 2 : ℝ) ^ (1 / Fm.ez)` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_mul (by norm_num), one_div_mul_cancel hez.ne', Real.rpow_one]`. Use `_ ≤ x ^ Fm.ez := Real.rpow_le_rpow hpos hx1 hez.le`. Establish `hS` using `sizesRec_at_point Fm hx hx4 ι (le_refl (6 : ℝ))`.

Establish `hR` using `rangeW_of_sizes hS hxe`. Establish `hL` using `GlobalTheory.GLq.lemmaL_series_weights_of_greenCuspidalParametrisation hG _ hp.2.2`. Simplify using `only`. Rewrite using `[Fm.L_x x ι hx, Fm.toFamCore.L_ez x ι]`. Establish `hψ` using `stdAddChar_ne_one (Fm.D x ι)`.

Use `⟨fun k => @ZMod.stdAddChar _ ⟨((Fm.D x ι).host.g_prime k).ne_zero⟩, hψ, fun S hS' => ?_⟩` and prove the remaining obligations. Establish `h0` using `locShare_eUk_le_Wg hL (tieAdmG_rec _) hR _ hψ 0 (S 0) (hS' 0)`. Establish `h1` using `locShare_eUk_le_Wg hL (tieAdmG_rec _) hR _ hψ 1 (S 1) (hS' 1)`. Establish `h2` using `ha x hxa _ hS`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem locShares_le_exp : Hypotheses2 → GlobalTheory.Published.GreenCuspidal → Lifts fun Fm x _ ι _ _ _ _ => ∃ ψ₀ : ∀ k : Fin 2, AddChar (ZMod ((Fm.D x ι).host.g k)) ℂ, (∀ k, ψ₀ k ≠ 1) ∧ ∀ S : ∀ k : Fin 2, Finset (Formalism.MainNotions.ArithmeticCylinders.Tup (Fm.D x ι) k), (∀ k, ∀ t ∈ S k, ¬ Formalism.MainNotions.ArithmeticCylinders.goodAt (Fm.D x ι) k t) → Formalism.MainNotions.ArithmeticCylinders.locShare (Fm.D x ι) (fun k _ => Formalism.MainNotions.ArithmeticCylinders.eUk (Fm.D x ι) k (ψ₀ k)) 0 (S 0) + Formalism.MainNotions.ArithmeticCylinders.locShare (Fm.D x ι) (fun k _ => Formalism.MainNotions.ArithmeticCylinders.eUk (Fm.D x ι) k (ψ₀ k)) 1 (S 1) ≤ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) := by
  intro _hP hG
  refine ⟨1 / 52, by norm_num, fun eps he he1 => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ⟨0, le_rfl, ?_⟩⟩⟩
  have hez : 0 < Fm.ez := div_pos he (lt_of_lt_of_le one_pos Fm.toFamCore.one_le_J)
  have hez1 : Fm.ez ≤ 1 := le_trans (div_le_self he.le Fm.toFamCore.one_le_J) (by linarith)
  obtain ⟨a, ha⟩ := wg_sum_le Fm.ez hez hez1
  refine ⟨max (max a (Fm.x1 + 1)) (max 4 ((3 / 2 : ℝ) ^ (1 / Fm.ez))), fun x hx hle ι p hp _ => ?_⟩
  have hx4 : 4 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hle
  have hxa : a ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hle
  have hx1 : (3 / 2 : ℝ) ^ (1 / Fm.ez) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hle
  have hxe : 3 / 2 ≤ x ^ Fm.ez := by
    have hpos : 0 ≤ (3 / 2 : ℝ) ^ (1 / Fm.ez) := by positivity
    calc (3 / 2 : ℝ) = ((3 / 2 : ℝ) ^ (1 / Fm.ez)) ^ Fm.ez := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hez.ne', Real.rpow_one]
      _ ≤ x ^ Fm.ez := Real.rpow_le_rpow hpos hx1 hez.le
  have hS := sizesRec_at_point Fm hx hx4 ι (le_refl (6 : ℝ))
  have hR := rangeW_of_sizes hS hxe
  have hL := GlobalTheory.GLq.lemmaL_series_weights_of_greenCuspidalParametrisation hG _ hp.2.2
  dsimp only
  rw [Fm.L_x x ι hx, Fm.toFamCore.L_ez x ι]
  have hψ := stdAddChar_ne_one (Fm.D x ι)
  refine ⟨fun k => @ZMod.stdAddChar _ ⟨((Fm.D x ι).host.g_prime k).ne_zero⟩, hψ, fun S hS' => ?_⟩
  have h0 := locShare_eUk_le_Wg hL (tieAdmG_rec _) hR _ hψ 0 (S 0) (hS' 0)
  have h1 := locShare_eUk_le_Wg hL (tieAdmG_rec _) hR _ hψ 1 (S 1) (hS' 1)
  have h2 := ha x hxa _ hS
  linarith

end GlobalTheory.CovTop.LocShareNum
