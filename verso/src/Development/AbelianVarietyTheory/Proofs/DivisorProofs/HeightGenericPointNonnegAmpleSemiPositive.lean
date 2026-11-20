import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricDegreePosOfAmpleSemiPositiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightAddMulGeometricDegreeNonnegOfSmallSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCountRadiusOneLowerBoundAmpleSemiPosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionsTwistedPowerEncardEqBall
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

/- English proof (translation)
Introduce `hAr hHS k _ X _ p D hX hD C h hA hS hH hnn`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `hg : 0 < gdeg C D` using `GlobalTheory.T.geometricDegree_pos_of_ample_semiPositive hAr hHS k X p D hX C hA hS`. Use `set c := h (genericPoint X) with hcdef`.

Use `set g := gdeg C D with hgdef`. Establish `hD' : (1 : ℝ) ≤ D` using `by exact_mod_cast hD`. Use `set x : ℝ := -c / g with hx`. Establish `hx0 : 0 < x` using `div_pos (by linarith) hg`. Establish `hxg : x * g = -c` using `by rw [hx]; field_simp`.

Use `set u : ℝ := x * (D + 2) / (2 * (D + 1)) with hu`. Establish `hu0 : 0 ≤ u` using `by rw [hu]; positivity`. Use `set α : ℝ := c + ((D : ℝ) + 1) * u * g with hα`. Establish `hαv : α = -c * D / 2`. Rewrite using `[hα, hu]`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `((D : ℝ) + 2) * hxg`. Establish `hα0 : 0 < α` using `by rw [hαv]; have : 0 < -c := by linarith`. Check the signs of the components of the expression. Establish `hcu : c + u * g < 0`.

Establish `e : c + u * g = c * D / (2 * (D + 1))`. Rewrite using `[hu]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `((D : ℝ) + 2) * hxg`. Rewrite using `[e]; exact div_neg_of_neg_of_pos (by nlinarith) (by positivity)`.

Use `set C' := C.shift (fun _ => u) fun _ => rfl with hC'`. Establish `hself : C.IsSelfInter c` using `⟨h, hH, rfl⟩`. Establish `hα' : C'.IsSelfInter α` using `hAr.arShift k X p D hX C c u hself`. Establish `hA' : IsAmpleLB C'.B` using `hA`. Establish `hS' : C'.SemiPos D` using `hS.shift _ _`.

Take `⟨P, hPL, -⟩` from `exists_pair C' C'`. Establish `hrep : P.Rep 1 0 C'` using `hPL ▸ (GlobalTheory.VolBr.Pair.rep_base k X p P).1`. Establish `hfac : (0 : ℝ) < ((D + 1).factorial : ℝ)` using `by positivity`. Establish `hε : 0 < α / (2 * ((D + 1).factorial : ℝ))` using `by positivity`. Take `⟨m, hm, hm0⟩` from `((GlobalTheory.T.log_count_radius_one_lower_bound_ample_semiPos hHS k X p D hX P 1 0 0 0 C' α hrep hA' hS' hα' _ hε).and (eventually_gt_atTop 0)).exists`.

Establish `hcoef : α / ((D + 1).factorial : ℝ) - α / (2 * ((D + 1).factorial : ℝ)) = α / (2 * ((D + 1).factorial : ℝ))` using `by field_simp; ring`. Rewrite `hm` using `[hcoef]`. Establish `hlc : 0 < P.lc ((m : ℤ) * 1) ((m : ℤ) * 0) 1`. Establish `: (0 : ℝ) < (m : ℝ) ^ (D + 1)` using `by positivity`. Use `mul_pos hε this` as an intermediate fact.

Simplify using `using lt_of_lt_of_le this hm`. Establish `hn : 1 < (P.Bl ((m : ℤ) * 1) ((m : ℤ) * 0) 1).ncard`. Assume the negation of the conclusion as `hle`. Use `push_neg at hle`. Establish `: ((P.Bl ((m : ℤ) * 1) ((m : ℤ) * 0) 1).ncard : ℝ) ≤ 1` using `by exact_mod_cast hle`.

Conclude with `absurd hlc (not_lt.2 (Real.log_nonpos (Nat.cast_nonneg _) this))`. Establish `hfin : (P.Bl ((m : ℤ) * 1) ((m : ℤ) * 0) 1).Finite` using `Set.finite_of_ncard_ne_zero (by omega)`. Establish `henc : 1 < ((C'.pow m).smallSec).encard`. Rewrite using `[(GlobalTheory.VolBr.SmallBall.main k X p P 1 0 C' hrep 0 m).2.1, ← hfin.cast_ncard_eq]`. Conclude with `hn` after adjusting the coercions.

Take `⟨a, b, ha, hb, hab⟩` from `Set.one_lt_encard_iff.1 henc`. Establish `hex : ∃ s ∈ (C'.pow m).smallSec, s ≠ 0`. Distinguish the cases in `ha0 : a = 0`. Conclude with `⟨b, hb, fun hb0 => hab (ha0.trans hb0.symm)⟩`. Conclude with `⟨a, ha, ha0⟩`.

Use `GlobalTheory.T.height_add_mul_geometricDegree_nonneg_of_smallSection hAr k X p D hX hD C h hS hH hnn m u hm0 hu0 hex` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem GlobalTheory.HSNef.height_generic_nonneg_of_ample : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → 1 ≤ D → ∀ (C : HermLB p) (h : X → ℝ), IsAmpleLB C.B → C.SemiPos D → C.IsArithHeight h → (∀ z, z ≠ genericPoint X → 0 ≤ h z) → 0 ≤ h (genericPoint X) := by
  intro hAr hHS k _ X _ p D hX hD C h hA hS hH hnn
  by_contra hc
  push_neg at hc
  have hg : 0 < gdeg C D := GlobalTheory.T.geometricDegree_pos_of_ample_semiPositive hAr hHS k X p D hX C hA hS
  set c := h (genericPoint X) with hcdef
  set g := gdeg C D with hgdef
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  set x : ℝ := -c / g with hx
  have hx0 : 0 < x := div_pos (by linarith) hg
  have hxg : x * g = -c := by rw [hx]; field_simp
  set u : ℝ := x * (D + 2) / (2 * (D + 1)) with hu
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  set α : ℝ := c + ((D : ℝ) + 1) * u * g with hα
  have hαv : α = -c * D / 2 := by
    rw [hα, hu]; field_simp; linear_combination ((D : ℝ) + 2) * hxg
  have hα0 : 0 < α := by rw [hαv]; have : 0 < -c := by linarith
                         positivity
  have hcu : c + u * g < 0 := by
    have e : c + u * g = c * D / (2 * (D + 1)) := by
      rw [hu]; field_simp; linear_combination ((D : ℝ) + 2) * hxg
    rw [e]; exact div_neg_of_neg_of_pos (by nlinarith) (by positivity)
  set C' := C.shift (fun _ => u) fun _ => rfl with hC'
  have hself : C.IsSelfInter c := ⟨h, hH, rfl⟩
  have hα' : C'.IsSelfInter α := hAr.arShift k X p D hX C c u hself
  have hA' : IsAmpleLB C'.B := hA
  have hS' : C'.SemiPos D := hS.shift _ _
  obtain ⟨P, hPL, -⟩ := exists_pair C' C'
  have hrep : P.Rep 1 0 C' := hPL ▸ (GlobalTheory.VolBr.Pair.rep_base k X p P).1
  have hfac : (0 : ℝ) < ((D + 1).factorial : ℝ) := by positivity
  have hε : 0 < α / (2 * ((D + 1).factorial : ℝ)) := by positivity
  obtain ⟨m, hm, hm0⟩ := ((GlobalTheory.T.log_count_radius_one_lower_bound_ample_semiPos hHS k X p D hX P 1 0 0 0 C' α hrep hA' hS' hα' _ hε).and
    (eventually_gt_atTop 0)).exists
  have hcoef : α / ((D + 1).factorial : ℝ) - α / (2 * ((D + 1).factorial : ℝ)) = α / (2 * ((D + 1).factorial : ℝ)) := by
    field_simp; ring
  rw [hcoef] at hm
  have hlc : 0 < P.lc ((m : ℤ) * 1) ((m : ℤ) * 0) 1 := by
    have : (0 : ℝ) < (m : ℝ) ^ (D + 1) := by positivity
    have := mul_pos hε this
    simpa using lt_of_lt_of_le this hm
  have hn : 1 < (P.Bl ((m : ℤ) * 1) ((m : ℤ) * 0) 1).ncard := by
    by_contra hle
    push_neg at hle
    have : ((P.Bl ((m : ℤ) * 1) ((m : ℤ) * 0) 1).ncard : ℝ) ≤ 1 := by exact_mod_cast hle
    exact absurd hlc (not_lt.2 (Real.log_nonpos (Nat.cast_nonneg _) this))
  have hfin : (P.Bl ((m : ℤ) * 1) ((m : ℤ) * 0) 1).Finite :=
    Set.finite_of_ncard_ne_zero (by omega)
  have henc : 1 < ((C'.pow m).smallSec).encard := by
    rw [(GlobalTheory.VolBr.SmallBall.main k X p P 1 0 C' hrep 0 m).2.1, ← hfin.cast_ncard_eq]
    exact_mod_cast hn
  obtain ⟨a, b, ha, hb, hab⟩ := Set.one_lt_encard_iff.1 henc
  have hex : ∃ s ∈ (C'.pow m).smallSec, s ≠ 0 := by
    by_cases ha0 : a = 0
    · exact ⟨b, hb, fun hb0 => hab (ha0.trans hb0.symm)⟩
    · exact ⟨a, ha, ha0⟩
  have := GlobalTheory.T.height_add_mul_geometricDegree_nonneg_of_smallSection hAr k X p D hX hD C h hS hH hnn m u hm0 hu0 hex
  linarith
