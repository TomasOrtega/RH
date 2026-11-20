import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlockVeronese
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerHeightsirational
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlockArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlockMetric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlockMeasure
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResVolume
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter MeasureTheory

noncomputable section

namespace PowerBlockDatum

/- English proof (translation)
Take `⟨i, hi⟩` from `hV.2.1.2.2 k`. Use `⟨i, fun h0 => hi ?_⟩` and prove the remaining obligations. Use `show (X ⟨k, i⟩ : MRing ι) ∈ RingHom.ker (mConeMap y)`. Rewrite using `[RingHom.mem_ker]`. Simplify using `[mConeMap, h0]`.
-/
theorem exists_coord_ne_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {d : ℕ} (hV : IsArithVar (mCoordIdeal y) d) (k : K) : ∃ i, y ⟨k, i⟩ ≠ 0 := by
  obtain ⟨i, hi⟩ := hV.2.1.2.2 k
  refine ⟨i, fun h0 => hi ?_⟩
  show (X ⟨k, i⟩ : MRing ι) ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  simp [mConeMap, h0]

/- English proof (translation)
Assemble the required witnesses or components as `⟨{1}, fun f hf => ⟨fun _ => 0, by rw [Set.mem_singleton_iff.mp hf] intro m hm k rw [MvPolynomial.support_one, Finset.mem_singleton] at hm subst hm simp⟩, Ideal.span_singleton_one.symm⟩`.
-/
theorem isMultiHomogIdeal_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    IsMultiHomogIdeal (⊤ : Ideal (MRing ι)) :=
  ⟨{1}, fun f hf => ⟨fun _ => 0, by
    rw [Set.mem_singleton_iff.mp hf]
    intro m hm k
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp⟩, Ideal.span_singleton_one.symm⟩

end PowerBlockDatum

open PowerBlockDatum in

/- English proof (translation)
Introduce `K _ _ ι _ Ω _ _ y D A P0 hD hArith hBiry hSG hConj`. Take `⟨q, w, hw, hgen, -⟩` from `hSG.gen`. Take `⟨m₁, hm₁⟩` from `hVer K ι Ω y A.a q w (exists_coord_ne_zero hArith) hw hgen`. Take `⟨m₂, hm₂⟩` from `hBir K ι Ω y D A.a q w hD hArith hBiry hw hgen hSG.deg_pos`. Take `⟨N, v, hspan, hgenv, hver⟩` from `hm₁ (max (max m₁ m₂) 1) (le_trans (le_max_left _ _) (le_max_left _ _))`.

Establish `hbir` using `hm₂ (max (max m₁ m₂) 1) (le_trans (le_max_right _ _) (le_max_left _ _)) N v hspan`. Establish `hv : ∀ j, v j ∈ chartLat y A.a (max (max m₁ m₂) 1)` using `fun j => hspan ▸ AddSubgroup.subset_closure (Set.mem_range_self j)`. Establish `hArv` using `hAr K ι Ω y D A.a _ N v hArith hv hgenv`. Take `⟨B, P0', hBa, hBconj, hP0', hBsemi, hrel⟩` from `hMet K ι Ω y A P0 _ N v hSG.normalForm_baseLattice_le_dualSpan_sup_line hSG.semipos hConj hv hgenv`. Take `⟨J', -, -, -, ⟨R'⟩⟩` from `hE (Option K) (addIdx ι N) (mCoordIdeal (addBlock y v)) ⊤ D hArv isMultiHomogIdeal_top (fun h => hArv.2.1.1.ne_top (top_le_iff.mp h))`.

Set `_ : MeasurableSpace R'.toAnRes.X` to `borel _`. Establish `_ : BorelSpace R'.toAnRes.X` using `⟨rfl⟩`. Take `⟨dV, hdV⟩` from `hV (Option K) (addIdx ι N) _ _ D R'.toAnRes hArv`. Take `⟨μ, hμp, hμn, hμd, hμ⟩` from `hMeas K ι Ω y A _ N D v B J' R'.toAnRes dV hSG.semipos.1 hBsemi.1 hBa hdV hv hgenv hrel`. Set `d : HSMBlockDatum D (Option K) (addIdx ι N) Ω` to `{ y := addBlock y v, k₀ := none, A := B, P0 := P0', J := J', R := R'.toAnRes, meas := borel _, borel := ⟨rfl⟩, dV := dV, one_le := hD, arith := hArv, birat := hbir, deg := hBa, conjInv := hBconj, normalForm_baseLattice_le_dualSpan_sup_line := hP0', semipos := hBsemi, vol := hdV }`.

Conclude with `⟨max (max m₁ m₂) 1, N, v, d, μ, le_max_right _ _, rfl, rfl, hv, hgenv, hrel, eventually_atTop.2 ⟨1, fun n hn => hver n hn⟩, hμp, hμn, hμd, fun q f hf => hμ q f hf⟩`.
-/
theorem PowerBlockDatum.proof (hE : ResExistsStatement) (hV : ResVolume.Statement)
    (hVer : PowerBlockVeronese.Statement) (hBir : PowerHeightsirational.Statement)
    (hAr : PowerBlockArith.Statement) (hMet : PowerBlockMetric.Statement)
    (hMeas : PowerBlockMeasure.Statement) : PowerBlockDatum.Statement := by
  intro K _ _ ι _ Ω _ _ y D A P0 hD hArith hBiry hSG hConj
  obtain ⟨q, w, hw, hgen, -⟩ := hSG.gen
  obtain ⟨m₁, hm₁⟩ := hVer K ι Ω y A.a q w (exists_coord_ne_zero hArith) hw hgen
  obtain ⟨m₂, hm₂⟩ := hBir K ι Ω y D A.a q w hD hArith hBiry hw hgen hSG.deg_pos
  obtain ⟨N, v, hspan, hgenv, hver⟩ := hm₁ (max (max m₁ m₂) 1) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hbir := hm₂ (max (max m₁ m₂) 1) (le_trans (le_max_right _ _) (le_max_left _ _)) N v hspan
  have hv : ∀ j, v j ∈ chartLat y A.a (max (max m₁ m₂) 1) := fun j =>
    hspan ▸ AddSubgroup.subset_closure (Set.mem_range_self j)
  have hArv := hAr K ι Ω y D A.a _ N v hArith hv hgenv
  obtain ⟨B, P0', hBa, hBconj, hP0', hBsemi, hrel⟩ :=
    hMet K ι Ω y A P0 _ N v hSG.normalForm_baseLattice_le_dualSpan_sup_line hSG.semipos hConj hv hgenv
  obtain ⟨J', -, -, -, ⟨R'⟩⟩ := hE (Option K) (addIdx ι N) (mCoordIdeal (addBlock y v)) ⊤ D hArv
    isMultiHomogIdeal_top (fun h => hArv.2.1.1.ne_top (top_le_iff.mp h))
  let _ : MeasurableSpace R'.toAnRes.X := borel _
  have _ : BorelSpace R'.toAnRes.X := ⟨rfl⟩
  obtain ⟨dV, hdV⟩ := hV (Option K) (addIdx ι N) _ _ D R'.toAnRes hArv
  obtain ⟨μ, hμp, hμn, hμd, hμ⟩ :=
    hMeas K ι Ω y A _ N D v B J' R'.toAnRes dV hSG.semipos.1 hBsemi.1 hBa hdV hv hgenv hrel
  let d : HSMBlockDatum D (Option K) (addIdx ι N) Ω :=
    { y := addBlock y v, k₀ := none, A := B, P0 := P0', J := J', R := R'.toAnRes, meas := borel _,
      borel := ⟨rfl⟩, dV := dV, one_le := hD, arith := hArv, birat := hbir, deg := hBa, conjInv := hBconj,
      normalForm_baseLattice_le_dualSpan_sup_line := hP0', semipos := hBsemi, vol := hdV }
  exact ⟨max (max m₁ m₂) 1, N, v, d, μ, le_max_right _ _, rfl, rfl, hv, hgenv, hrel,
    eventually_atTop.2 ⟨1, fun n hn => hver n hn⟩, hμp, hμn, hμd, fun q f hf => hμ q f hf⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
