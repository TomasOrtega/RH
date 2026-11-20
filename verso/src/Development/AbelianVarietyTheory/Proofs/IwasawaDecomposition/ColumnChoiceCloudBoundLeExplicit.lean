import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalRingCardinality.SpanPowerMembership.TwCore
import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MtOfFactors
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Formalism.LocalRingCardinality.SpanPowerMembership.EntPlNonempty
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnChoicesKernelDatumAdaptedBasesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeLayerTrueColumnsParametersFreeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsKernelDataAtServedPlaceStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparisonStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScaleStatement
import Formalism.LocalToGlobal.GroupLattices.CloudFilling.WLeWjOne

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl.CloudRec

def ScaleOK (K : Ctx) : Prop :=
  ∀ R : Ranks, RankVal K.s R →
    16 * (R.k : ℝ) * (Delv K.s K.cD : ℝ) + R.k + 2 ≤ K.s.w'' R.n ∧ K.s.w'' R.n ≤ K.s.b

/- English proof (translation)
Take `⟨x2, hx2⟩` from `GlobalTheory.T.scale_polynomial_quantities_comparison eps (cD + 6) (1 / 2) he (by norm_num)`. Take `⟨x3, hx3⟩` from `GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he he'`. Use `⟨max 35 (max x2 x3), fun K e1 e2 hx R hR => ?_⟩` and prove the remaining obligations. Establish `h35 : 35 ≤ K.s.x` using `le_trans (le_max_left _ _) hx`. Establish `hxa : x2 ≤ K.s.x` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx`.

Establish `hxb : x3 ≤ K.s.x` using `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx`. Take `⟨hf, -, hr, hkr, -⟩` from `hx3 K.s R e1 hxb hR`. Establish `hx0 : 0 < K.s.x` using `by linarith`. Establish `hx1 : 1 ≤ K.s.x` using `by linarith`. Establish `hn1 : 1 ≤ R.n` using `Formalism.HC.Frame.ord_pos _`.

Establish `hn3 : (R.n : ℝ) ≤ K.s.x ^ (3 : ℝ)`. Use `le_trans ?_ hf` and prove the remaining obligations. Simplify using `only [Ranks.f]`. Use `push_cast`. Establish `: (0:ℝ) ≤ R.n` using `Nat.cast_nonneg _`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `H` using `hx2 K.s e1 hxa`. Take `⟨-, -, -, hb'b, -, hw, -⟩` from `H`. Take `⟨hw1, hw2, -⟩` from `hw R.n hn1 hn3`. Establish `hL0 : 0 ≤ K.s.L` using `by unfold Scale.L; positivity`.

Establish `hb1 : 1 ≤ K.s.b` using `by unfold Scale.b; exact Real.one_le_exp hL0`. Establish `hbk : 1 ≤ K.s.b ^ (1 - (1 / 2 : ℝ))` using `Real.one_le_rpow hb1 (by norm_num)`. Establish `hxc0 : 0 ≤ K.s.x ^ (cD + 6)` using `by positivity`. Establish `hxc : K.s.x ^ (cD + 6) ≤ K.s.w'' R.n`. Combine the equalities or inequalities in the displayed calculation.

Establish `hxc1 : 1 ≤ K.s.x ^ (cD + 0)` using `by rw [add_zero]; exact Real.one_le_rpow hx1 hcD`. Establish `hD : (Delv K.s K.cD : ℝ) ≤ 2 * K.s.x ^ cD`. Unfold `Delv`. Rewrite using `[e2]`. Use `Nat.ceil_lt_add_one (Real.rpow_nonneg hx0.le cD)` as an intermediate fact.

Rewrite `hxc1` using `[add_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hk5 : (R.k : ℝ) ≤ K.s.x ^ (5 : ℝ)` using `le_trans (by exact_mod_cast hkr) hr`. Establish `hsplit : K.s.x ^ (cD + 6) = K.s.x ^ cD * K.s.x ^ (5 : ℝ) * K.s.x`. Rewrite using `[← Real.rpow_add hx0, ← Real.rpow_add_one hx0.ne']`.

Put the polynomial expressions in normal form. Establish `hxcD : 1 ≤ K.s.x ^ cD` using `by rw [add_zero] at hxc1; exact hxc1`. Establish `hx5 : 1 ≤ K.s.x ^ (5 : ℝ)` using `Real.one_le_rpow hx1 (by norm_num)`. Establish `hk0 : (0 : ℝ) ≤ R.k` using `Nat.cast_nonneg _`. Establish `hD0 : (0 : ℝ) ≤ (Delv K.s K.cD : ℝ)` using `Nat.cast_nonneg _`.

Use `⟨?_, le_trans hw2 ?_⟩` and prove the remaining obligations. Establish `h1 : 16 * (R.k : ℝ) * (Delv K.s K.cD : ℝ) ≤ 32 * (K.s.x ^ cD * K.s.x ^ (5 : ℝ))`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : 1 ≤ K.s.x ^ cD * K.s.x ^ (5 : ℝ)` using `one_le_mul_of_one_le_of_one_le hxcD hx5`. Establish `h3 : (R.k : ℝ) ≤ K.s.x ^ cD * K.s.x ^ (5 : ℝ)` using `le_trans hk5 (le_mul_of_one_le_left (by linarith) hxcD)`.

Establish `h4 : 35 * (K.s.x ^ cD * K.s.x ^ (5 : ℝ)) ≤ K.s.x ^ cD * K.s.x ^ (5 : ℝ) * K.s.x`. Rewrite using `[mul_comm 35]`. Use `gcongr`. Combine the linear equalities and inequalities to obtain the conclusion. Use `hb'b` as an intermediate fact.

Establish `h0 : 0 ≤ K.s.b'` using `by unfold Scale.b' Scale.a Scale.X' Scale.b; positivity`. Establish `hx6 : 1 ≤ K.s.x ^ (cD + 6)` using `Real.one_le_rpow hx1 (by linarith)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem scaleOK_large (eps : ℝ) (he : 0 < eps) (he' : eps < 1 / 52) (cD : ℝ) (hcD : 0 ≤ cD) :
    ∃ x1 : ℝ, ∀ K : Ctx, K.s.eps = eps → K.cD = cD → x1 ≤ K.s.x → ScaleOK K := by
  obtain ⟨x2, hx2⟩ := GlobalTheory.T.scale_polynomial_quantities_comparison eps (cD + 6) (1 / 2) he (by norm_num)
  obtain ⟨x3, hx3⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he he'
  refine ⟨max 35 (max x2 x3), fun K e1 e2 hx R hR => ?_⟩
  have h35 : 35 ≤ K.s.x := le_trans (le_max_left _ _) hx
  have hxa : x2 ≤ K.s.x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxb : x3 ≤ K.s.x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨hf, -, hr, hkr, -⟩ := hx3 K.s R e1 hxb hR
  have hx0 : 0 < K.s.x := by linarith
  have hx1 : 1 ≤ K.s.x := by linarith
  have hn1 : 1 ≤ R.n := Formalism.HC.Frame.ord_pos _
  have hn3 : (R.n : ℝ) ≤ K.s.x ^ (3 : ℝ) := by
    refine le_trans ?_ hf
    simp only [Ranks.f]; push_cast
    have : (0:ℝ) ≤ R.n := Nat.cast_nonneg _
    linarith
  have H := hx2 K.s e1 hxa
  obtain ⟨-, -, -, hb'b, -, hw, -⟩ := H
  obtain ⟨hw1, hw2, -⟩ := hw R.n hn1 hn3
  have hL0 : 0 ≤ K.s.L := by unfold Scale.L; positivity
  have hb1 : 1 ≤ K.s.b := by unfold Scale.b; exact Real.one_le_exp hL0
  have hbk : 1 ≤ K.s.b ^ (1 - (1 / 2 : ℝ)) := Real.one_le_rpow hb1 (by norm_num)
  have hxc0 : 0 ≤ K.s.x ^ (cD + 6) := by positivity
  have hxc : K.s.x ^ (cD + 6) ≤ K.s.w'' R.n := by
    calc K.s.x ^ (cD + 6) = 1 * K.s.x ^ (cD + 6) := by ring
      _ ≤ K.s.b ^ (1 - (1 / 2 : ℝ)) * K.s.x ^ (cD + 6) := by gcongr
      _ ≤ _ := hw1
  have hxc1 : 1 ≤ K.s.x ^ (cD + 0) := by rw [add_zero]; exact Real.one_le_rpow hx1 hcD
  have hD : (Delv K.s K.cD : ℝ) ≤ 2 * K.s.x ^ cD := by
    unfold Delv
    rw [e2]
    have := Nat.ceil_lt_add_one (Real.rpow_nonneg hx0.le cD)
    rw [add_zero] at hxc1
    linarith
  have hk5 : (R.k : ℝ) ≤ K.s.x ^ (5 : ℝ) := le_trans (by exact_mod_cast hkr) hr
  have hsplit : K.s.x ^ (cD + 6) = K.s.x ^ cD * K.s.x ^ (5 : ℝ) * K.s.x := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add_one hx0.ne']; ring_nf
  have hxcD : 1 ≤ K.s.x ^ cD := by rw [add_zero] at hxc1; exact hxc1
  have hx5 : 1 ≤ K.s.x ^ (5 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hk0 : (0 : ℝ) ≤ R.k := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ (Delv K.s K.cD : ℝ) := Nat.cast_nonneg _
  refine ⟨?_, le_trans hw2 ?_⟩
  · have h1 : 16 * (R.k : ℝ) * (Delv K.s K.cD : ℝ) ≤ 32 * (K.s.x ^ cD * K.s.x ^ (5 : ℝ)) := by
      calc 16 * (R.k : ℝ) * (Delv K.s K.cD : ℝ) ≤ 16 * K.s.x ^ (5 : ℝ) * (2 * K.s.x ^ cD) := by gcongr
        _ = _ := by ring
    have h2 : 1 ≤ K.s.x ^ cD * K.s.x ^ (5 : ℝ) := one_le_mul_of_one_le_of_one_le hxcD hx5
    have h3 : (R.k : ℝ) ≤ K.s.x ^ cD * K.s.x ^ (5 : ℝ) := le_trans hk5 (le_mul_of_one_le_left (by linarith) hxcD)
    have h4 : 35 * (K.s.x ^ cD * K.s.x ^ (5 : ℝ)) ≤ K.s.x ^ cD * K.s.x ^ (5 : ℝ) * K.s.x := by
      rw [mul_comm 35]; gcongr
    linarith
  · have := hb'b
    have h0 : 0 ≤ K.s.b' := by unfold Scale.b' Scale.a Scale.X' Scale.b; positivity
    have hx6 : 1 ≤ K.s.x ^ (cD + 6) := Real.one_le_rpow hx1 (by linarith)
    nlinarith

end GlobalTheory.Mem.Top.Bl.CloudRec

namespace GlobalTheory.Mem.Top.Bl.CloudRec

/- English proof (translation)
Take `⟨sp, hT, hY, hA, hV, hz, rfl, -⟩` from `hO`. Simplify using `only [Pre.ofCh]`. Establish `ok` using `K.ok`. Establish `hx1 : 1 < K.s.x` using `K.s.one_lt_alt`. Establish `hx0 : 0 < K.s.x` using `by linarith`.

Establish `hD1 : (1 : ℝ) ≤ (Delv K.s K.cD : ℝ)`. Unfold `Delv`. Establish `h : 0 < K.s.x ^ K.cD` using `Real.rpow_pos_of_pos hx0 _`. Conclude with `Nat.one_le_iff_ne_zero.2 (by` after adjusting the coercions. Introduce `h0`.

Rewrite `h0` using `[Nat.ceil_eq_zero]`. Use the proof step `linarith)`. Take `⟨hS1, hS2⟩` from `hS K.P.R ok.rank`. Use `⟨hD1, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `u τ i hi1 hi2`.

Establish `hv` using `(ok.hc u).1`. Establish `hcode` using `ok.code u τ (i.1 - 1) (by omega)`. Establish `e : (⟨i.1 - 1 + 1, by omega⟩ : Fin K.P.R.k) = i` using `Fin.ext (by simp only; omega)`. Rewrite `hcode` using `[e, hv τ ⟨i.1 - 1, by omega⟩]`. Establish `hcR` using `congrArg (Rat.cast (K := ℝ)) hcode`.

Rewrite using `[hcR]`. Establish `hl1 : 1 ≤ K.P.R.k - 2 - (i.1 - 1)` using `by omega`. Establish `hl2 : K.P.R.k - 2 - (i.1 - 1) ≤ K.P.R.k` using `by omega`. Establish `c1 : (1 : ℝ) ≤ ((K.P.R.k - 2 - (i.1 - 1) : ℕ) : ℝ)` using `by exact_mod_cast hl1`. Establish `c2 : ((K.P.R.k - 2 - (i.1 - 1) : ℕ) : ℝ) ≤ K.P.R.k` using `by exact_mod_cast hl2`.

Establish `hD0 : (0 : ℝ) ≤ (Delv K.s K.cD : ℝ)` using `by linarith`. Apply the tactic sequence `split_ifs <;> push_cast <;> constructor <;> nlinarith`. Introduce `u τ hk htop`. Establish `h` using `(ok.hc u).2.1 τ hk htop`. Prove the components needed by the constructor for the conclusion.

Use `congrArg (Rat.cast (K := ℝ)) h.1` as an intermediate fact. Rewrite using `[this]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `congrArg (Rat.cast (K := ℝ)) h.2` as an intermediate fact.

Rewrite using `[this]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `u τ hm`. Take `⟨b1, hb, htopb, hthick, hthin⟩` from `(ok.hc u).2.2.1`.

Establish `hgap` using `(K.P.hcW u τ).gap_be ⟨0, hm⟩`. Establish `hb0` using `(hb τ ⟨0, hm⟩).1`. Simplify using `only [Nat.cast_zero, zero_mul, add_zero] at hb0`. Rewrite `hgap` using `[hb0]`. Establish `hgapR : ((K.P.R.t : ℝ) + 3) / 2 ≤ (((K.P.hcW u τ).e ⟨0, hm⟩ : ℚ) : ℝ) - (b1 τ : ℝ)`.

Establish `h'` using `(Rat.cast_le (K := ℝ)).2 hgap`. Move the coercions through the operations in `at h'`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hwb : K.s.w'' K.P.R.n ≤ (b1 τ : ℝ) + 1`. Distinguish the cases in `ht : (τ : K.P.R.GG) ∈ K.P.H.topPlaces`.

Take `⟨t, htT, hte⟩` from `Finset.mem_image.1 ht`. Establish `e1` using `htopb τ ⟨t, htT⟩ hte.symm`. Establish `hwin` using `(ok.win t htT).2.1`. Rewrite using `[e1]`. Use `push_cast`.

Establish `hfl` using `Int.sub_one_lt_floor (K.s.b' / K.s.x)`. Establish `hb'0 : 0 ≤ K.s.b'` using `by unfold Scale.b' Scale.a Scale.X' Scale.b; positivity`. Establish `hn1 : (1 : ℝ) ≤ K.P.R.n` using `by exact_mod_cast (Formalism.HC.Frame.ord_pos _ : 1 ≤ K.P.R.n)`. Establish `hw'' : K.s.w'' K.P.R.n ≤ K.s.b' / K.s.x`. Unfold `Scale.w''`.

Rewrite using `[div_le_div_iff₀ (by positivity) hx0]`. Establish `: K.s.b' * K.s.x ≤ K.s.b' * (K.s.x * K.P.R.n)`. Apply `mul_le_mul_of_nonneg_left _ hb'0` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hbt : K.s.b' ≤ ((K.b t : ℤ) : ℝ)` using `hwin`. Use the polynomial consequences of the given equalities and inequalities. Distinguish the cases in `hth : (τ : K.P.R.GG) ∈ K.P.H.thickPlaces`. Establish `h1` using `(hthick τ hth).1`. Establish `hc : K.s.b ≤ (⌈K.s.b⌉ : ℝ)` using `Int.le_ceil _`.

Establish `h2 : ((⌈K.s.b⌉ : ℤ) : ℝ) ≤ ((b1 τ : ℤ) : ℝ)` using `by exact_mod_cast h1`. Combine the linear equalities and inequalities to obtain the conclusion. Use `hthin τ ⟨τ.2, ht, hth⟩` as an intermediate fact. Rewrite using `[this]`. Use `Int.le_ceil (K.s.w'' K.P.R.n)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hk0 : (0 : ℝ) ≤ K.P.R.k` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem facts_pre {K : Ctx} (hS : ScaleOK K) {Bp : Pre} (hO : K.Over Bp) :
    (1 : ℝ) ≤ (Delv K.s K.cD : ℝ) ∧
    (∀ u (τ : Tau Bp.R) (i : Fin Bp.R.k), 1 ≤ i.1 → i.1 + 1 < Bp.R.k →
      3 * (Delv K.s K.cD : ℝ) - 1 / 2 ≤ (((Bp.hcW u τ).u i : ℚ) : ℝ) ∧
      (((Bp.hcW u τ).u i : ℚ) : ℝ) ≤ 4 * (Bp.R.k : ℝ) * (Delv K.s K.cD : ℝ)) ∧
    (∀ u (τ : Tau Bp.R) (hk : 0 < Bp.R.k), (τ : Bp.R.GG) ∉ Bp.host.topPlaces →
      (((Bp.hcW u τ).u ⟨0, hk⟩ : ℚ) : ℝ) =
        ((Bp.R.k - 2 : ℕ) : ℝ) * (4 * (Delv K.s K.cD : ℝ)) + (Bp.R.k : ℝ) * (4 * (Delv K.s K.cD : ℝ)) + 1 / 2 ∧
      (((Bp.hcW u τ).u ⟨Bp.R.k - 1, by omega⟩ : ℚ) : ℝ) = -1 / 2) ∧
    (∀ u (τ : Tau Bp.R) (hm : 0 < Bp.R.m),
      16 * (Bp.R.k : ℝ) * (Delv K.s K.cD : ℝ) + ((Bp.R.k : ℝ) + Bp.R.t + 1) / 2 + 1 ≤ (((Bp.hcW u τ).e ⟨0, hm⟩ : ℚ) : ℝ)) := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := hO
  dsimp only [Pre.ofCh]
  have ok := K.ok
  have hx1 : 1 < K.s.x := K.s.one_lt_alt
  have hx0 : 0 < K.s.x := by linarith
  have hD1 : (1 : ℝ) ≤ (Delv K.s K.cD : ℝ) := by
    unfold Delv
    have h : 0 < K.s.x ^ K.cD := Real.rpow_pos_of_pos hx0 _
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by
      intro h0; rw [Nat.ceil_eq_zero] at h0; linarith)
  obtain ⟨hS1, hS2⟩ := hS K.P.R ok.rank
  refine ⟨hD1, ?_, ?_, ?_⟩
  · intro u τ i hi1 hi2
    have hv := (ok.hc u).1
    have hcode := ok.code u τ (i.1 - 1) (by omega)
    have e : (⟨i.1 - 1 + 1, by omega⟩ : Fin K.P.R.k) = i := Fin.ext (by simp only; omega)
    rw [e, hv τ ⟨i.1 - 1, by omega⟩] at hcode
    have hcR := congrArg (Rat.cast (K := ℝ)) hcode
    rw [hcR]
    have hl1 : 1 ≤ K.P.R.k - 2 - (i.1 - 1) := by omega
    have hl2 : K.P.R.k - 2 - (i.1 - 1) ≤ K.P.R.k := by omega
    have c1 : (1 : ℝ) ≤ ((K.P.R.k - 2 - (i.1 - 1) : ℕ) : ℝ) := by exact_mod_cast hl1
    have c2 : ((K.P.R.k - 2 - (i.1 - 1) : ℕ) : ℝ) ≤ K.P.R.k := by exact_mod_cast hl2
    have hD0 : (0 : ℝ) ≤ (Delv K.s K.cD : ℝ) := by linarith
    split_ifs <;> push_cast <;> constructor <;> nlinarith
  · intro u τ hk htop
    have h := (ok.hc u).2.1 τ hk htop
    constructor
    · have := congrArg (Rat.cast (K := ℝ)) h.1
      rw [this]; push_cast; ring
    · have := congrArg (Rat.cast (K := ℝ)) h.2
      rw [this]; push_cast; ring
  · intro u τ hm
    obtain ⟨b1, hb, htopb, hthick, hthin⟩ := (ok.hc u).2.2.1
    have hgap := (K.P.hcW u τ).gap_be ⟨0, hm⟩
    have hb0 := (hb τ ⟨0, hm⟩).1
    simp only [Nat.cast_zero, zero_mul, add_zero] at hb0
    rw [hb0] at hgap
    have hgapR : ((K.P.R.t : ℝ) + 3) / 2 ≤ (((K.P.hcW u τ).e ⟨0, hm⟩ : ℚ) : ℝ) - (b1 τ : ℝ) := by
      have h' := (Rat.cast_le (K := ℝ)).2 hgap
      push_cast at h'
      linarith
    have hwb : K.s.w'' K.P.R.n ≤ (b1 τ : ℝ) + 1 := by
      by_cases ht : (τ : K.P.R.GG) ∈ K.P.H.topPlaces
      · obtain ⟨t, htT, hte⟩ := Finset.mem_image.1 ht
        have e1 := htopb τ ⟨t, htT⟩ hte.symm
        have hwin := (ok.win t htT).2.1
        rw [e1]
        push_cast
        have hfl := Int.sub_one_lt_floor (K.s.b' / K.s.x)
        have hb'0 : 0 ≤ K.s.b' := by unfold Scale.b' Scale.a Scale.X' Scale.b; positivity
        have hn1 : (1 : ℝ) ≤ K.P.R.n := by exact_mod_cast (Formalism.HC.Frame.ord_pos _ : 1 ≤ K.P.R.n)
        have hw'' : K.s.w'' K.P.R.n ≤ K.s.b' / K.s.x := by
          unfold Scale.w''
          rw [div_le_div_iff₀ (by positivity) hx0]
          have : K.s.b' * K.s.x ≤ K.s.b' * (K.s.x * K.P.R.n) := by
            apply mul_le_mul_of_nonneg_left _ hb'0; nlinarith
          linarith
        have hbt : K.s.b' ≤ ((K.b t : ℤ) : ℝ) := hwin
        nlinarith
      · by_cases hth : (τ : K.P.R.GG) ∈ K.P.H.thickPlaces
        · have h1 := (hthick τ hth).1
          have hc : K.s.b ≤ (⌈K.s.b⌉ : ℝ) := Int.le_ceil _
          have h2 : ((⌈K.s.b⌉ : ℤ) : ℝ) ≤ ((b1 τ : ℤ) : ℝ) := by exact_mod_cast h1
          linarith
        · have := hthin τ ⟨τ.2, ht, hth⟩
          rw [this]
          have := Int.le_ceil (K.s.w'' K.P.R.n)
          linarith
    have hk0 : (0 : ℝ) ≤ K.P.R.k := Nat.cast_nonneg _
    linarith

end GlobalTheory.Mem.Top.Bl.CloudRec

namespace GlobalTheory.Mem.Top.Bl.CloudRec

/- English proof (translation)
Establish `hD1R : (1 : ℝ) ≤ (Δ : ℝ)` using `by exact_mod_cast hD1`. Establish `hk5 : 5 ≤ D.R.k` using `by have h1 := D.R.two_le_m; have h2 := D.R.m_add_three_le_k; omega`. Establish `hkR : (5 : ℝ) ≤ (D.R.k : ℝ)` using `by exact_mod_cast hk5`. Establish `hc : (((16 * D.R.k * Δ : ℕ) : ℤ) : ℝ) = 16 * (D.R.k : ℝ) * (Δ : ℝ)` using `by push_cast; ring`. Establish `hmidL : ∀ (g : D.R.Psi) (i : Fin (D.R.k - 1 + 1)), 0 < i.val → i.val < D.R.k - 1 → |Formalism.L2.G.lamRec D u g i| ≤ ((16 * D.R.k * Δ : ℕ) : ℤ)`.

Introduce `g i h0 h1`. Establish `hi : i.1 < D.R.k` using `by omega`. Establish `h` using `Formalism.L2.G.lamRec_real D u g i hi`. Establish `hb` using `hmid u (D.eTau.symm g) ⟨i.1, hi⟩ h0 (by show i.1 + 1 < D.R.k; omega)`. Establish `hiR : (i.1 : ℝ) + 1 ≤ (D.R.k : ℝ)` using `by exact_mod_cast hi`.

Establish `hi0 : (0 : ℝ) ≤ (i.1 : ℝ)` using `Nat.cast_nonneg _`. Establish `h2 : |((Formalism.L2.G.lamRec D u g i : ℤ) : ℝ)| ≤ (((16 * D.R.k * Δ : ℕ) : ℤ) : ℝ)`. Rewrite using `[h, hc, abs_le]`. Apply the tactic sequence `constructor <;> nlinarith [hb.1, hb.2]`. Conclude with `h2` after adjusting the coercions.

Use `⟨fun g _ i h0 h1 => hmidL g i h0 h1, fun g hg i => ?_, fun g => ?_⟩` and prove the remaining obligations. Establish `hg' : ((D.eTau (D.eTau.symm g) : D.R.Psi) : D.R.GG) ∉ D.host.topPlaces`. Rewrite using `[Equiv.apply_symm_apply]` and apply the resulting hypothesis. Establish `hk0 : 0 < D.R.k` using `by omega`. Take `⟨e0, e1⟩` from `hoff u (D.eTau.symm g) hk0 hg'`.

Distinguish the cases in `h0 : i.val = 0`. Establish `hi : i.1 < D.R.k` using `by omega`. Establish `h` using `Formalism.L2.G.lamRec_real D u g i hi`. Establish `e : (⟨i.1, hi⟩ : Fin D.R.k) = ⟨0, hk0⟩` using `Fin.ext h0`. Rewrite `h` using `[e, e0, h0]`.

Establish `hk2 : ((D.R.k - 2 : ℕ) : ℝ) ≤ D.R.k` using `by exact_mod_cast Nat.sub_le _ _`. Establish `hk2' : (0 : ℝ) ≤ ((D.R.k - 2 : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Establish `h2 : |((Formalism.L2.G.lamRec D u g i : ℤ) : ℝ)| ≤ (((16 * D.R.k * Δ : ℕ) : ℤ) : ℝ)`. Rewrite using `[h, hc, abs_le]`. Use `push_cast`.

Apply the tactic sequence `constructor <;> nlinarith`. Conclude with `h2` after adjusting the coercions. Distinguish the cases in `h1 : i.val < D.R.k - 1`. Conclude with `hmidL g i (Nat.pos_of_ne_zero h0) h1`. Establish `hi1 : i.val = D.R.k - 1` using `by have := i.2; omega`.

Establish `hi : i.1 < D.R.k` using `by omega`. Establish `h` using `Formalism.L2.G.lamRec_real D u g i hi`. Establish `e : (⟨i.1, hi⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩` using `Fin.ext hi1`. Establish `hkR1 : ((D.R.k - 1 : ℕ) : ℝ) = (D.R.k : ℝ) - 1`. Rewrite using `[Nat.cast_sub (by omega)]; simp`.

Rewrite `h` using `[e, e1, hi1, hkR1]`. Establish `h2 : |((Formalism.L2.G.lamRec D u g i : ℤ) : ℝ)| ≤ (((16 * D.R.k * Δ : ℕ) : ℤ) : ℝ)`. Rewrite using `[h, hc, abs_le]`. Apply the tactic sequence `constructor <;> nlinarith`. Conclude with `h2` after adjusting the coercions.

Establish `hm : 0 < D.R.m` using `by have := D.R.two_le_m; omega`. Establish `h1 : (1 : ℕ) ∈ SizeData₂.lifts D` using `Finset.mem_Icc.2 ⟨le_rfl, by have := D.R.two_le_m; omega⟩`. Establish `hw` using `Formalism.L2.G.wRec_eq D u g 1 h1`. Establish `hf` using `hfill u (D.eTau.symm g) hm`. Establish `hfe : (((D.hcW u (D.eTau.symm g)).e ⟨0, hm⟩ : ℚ) : ℝ) = Formalism.BasicNotions.wj D 1 (D.eTau.symm g)`.

Unfold `Formalism.BasicNotions.wj`. Rewrite using `[dif_pos (by omega), D.hcW_e]`. Rewrite `hf` using `[hfe]`. Establish `hka : Formalism.MainNotions.G.kaJ D 1 = ((D.R.k : ℝ) + D.R.t + 1) / 2`. Unfold `Formalism.MainNotions.G.kaJ`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : (((16 * D.R.k * Δ : ℕ) : ℤ) : ℝ) ≤ ((Formalism.L2.G.wRec D u g 1 : ℤ) : ℝ)`. Rewrite using `[hw, hka, hc]`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `h2` after adjusting the coercions.
-/
theorem cloudBound_of (D : D7) (Δ : ℕ) (hD1 : 1 ≤ Δ)
    (hmid : ∀ (u : D.what₂.Word) (τ : D.what₂.Tau) (i : Fin D.R.k), 1 ≤ i.1 → i.1 + 1 < D.R.k →
      3 * (Δ : ℝ) - 1 / 2 ≤ (((D.hcW u τ).u i : ℚ) : ℝ) ∧ (((D.hcW u τ).u i : ℚ) : ℝ) ≤ 4 * (D.R.k : ℝ) * Δ)
    (hoff : ∀ (u : D.what₂.Word) (τ : D.what₂.Tau) (hk : 0 < D.R.k),
      ((D.eTau τ : D.R.Psi) : D.R.GG) ∉ D.host.topPlaces →
      (((D.hcW u τ).u ⟨0, hk⟩ : ℚ) : ℝ) = ((D.R.k - 2 : ℕ) : ℝ) * (4 * (Δ : ℝ)) + (D.R.k : ℝ) * (4 * (Δ : ℝ)) + 1 / 2 ∧
      (((D.hcW u τ).u ⟨D.R.k - 1, by omega⟩ : ℚ) : ℝ) = -1 / 2)
    (hfill : ∀ (u : D.what₂.Word) (τ : D.what₂.Tau) (hm : 0 < D.R.m),
      16 * (D.R.k : ℝ) * Δ + ((D.R.k : ℝ) + D.R.t + 1) / 2 + 1 ≤ (((D.hcW u τ).e ⟨0, hm⟩ : ℚ) : ℝ))
    (u : D.what₂.Word) : Formalism.L2.G.CloudBound D u (16 * D.R.k * Δ) := by
  have hD1R : (1 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hD1
  have hk5 : 5 ≤ D.R.k := by have h1 := D.R.two_le_m; have h2 := D.R.m_add_three_le_k; omega
  have hkR : (5 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast hk5
  have hc : (((16 * D.R.k * Δ : ℕ) : ℤ) : ℝ) = 16 * (D.R.k : ℝ) * (Δ : ℝ) := by push_cast; ring
  have hmidL : ∀ (g : D.R.Psi) (i : Fin (D.R.k - 1 + 1)), 0 < i.val → i.val < D.R.k - 1 →
      |Formalism.L2.G.lamRec D u g i| ≤ ((16 * D.R.k * Δ : ℕ) : ℤ) := by
    intro g i h0 h1
    have hi : i.1 < D.R.k := by omega
    have h := Formalism.L2.G.lamRec_real D u g i hi
    have hb := hmid u (D.eTau.symm g) ⟨i.1, hi⟩ h0 (by show i.1 + 1 < D.R.k; omega)
    have hiR : (i.1 : ℝ) + 1 ≤ (D.R.k : ℝ) := by exact_mod_cast hi
    have hi0 : (0 : ℝ) ≤ (i.1 : ℝ) := Nat.cast_nonneg _
    have h2 : |((Formalism.L2.G.lamRec D u g i : ℤ) : ℝ)| ≤ (((16 * D.R.k * Δ : ℕ) : ℤ) : ℝ) := by
      rw [h, hc, abs_le]
      constructor <;> nlinarith [hb.1, hb.2]
    exact_mod_cast h2
  refine ⟨fun g _ i h0 h1 => hmidL g i h0 h1, fun g hg i => ?_, fun g => ?_⟩
  · have hg' : ((D.eTau (D.eTau.symm g) : D.R.Psi) : D.R.GG) ∉ D.host.topPlaces := by
      rwa [Equiv.apply_symm_apply]
    have hk0 : 0 < D.R.k := by omega
    obtain ⟨e0, e1⟩ := hoff u (D.eTau.symm g) hk0 hg'
    by_cases h0 : i.val = 0
    · have hi : i.1 < D.R.k := by omega
      have h := Formalism.L2.G.lamRec_real D u g i hi
      have e : (⟨i.1, hi⟩ : Fin D.R.k) = ⟨0, hk0⟩ := Fin.ext h0
      rw [e, e0, h0] at h
      have hk2 : ((D.R.k - 2 : ℕ) : ℝ) ≤ D.R.k := by exact_mod_cast Nat.sub_le _ _
      have hk2' : (0 : ℝ) ≤ ((D.R.k - 2 : ℕ) : ℝ) := Nat.cast_nonneg _
      have h2 : |((Formalism.L2.G.lamRec D u g i : ℤ) : ℝ)| ≤ (((16 * D.R.k * Δ : ℕ) : ℤ) : ℝ) := by
        rw [h, hc, abs_le]
        push_cast
        constructor <;> nlinarith
      exact_mod_cast h2
    · by_cases h1 : i.val < D.R.k - 1
      · exact hmidL g i (Nat.pos_of_ne_zero h0) h1
      · have hi1 : i.val = D.R.k - 1 := by have := i.2; omega
        have hi : i.1 < D.R.k := by omega
        have h := Formalism.L2.G.lamRec_real D u g i hi
        have e : (⟨i.1, hi⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ := Fin.ext hi1
        have hkR1 : ((D.R.k - 1 : ℕ) : ℝ) = (D.R.k : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        rw [e, e1, hi1, hkR1] at h
        have h2 : |((Formalism.L2.G.lamRec D u g i : ℤ) : ℝ)| ≤ (((16 * D.R.k * Δ : ℕ) : ℤ) : ℝ) := by
          rw [h, hc, abs_le]
          constructor <;> nlinarith
        exact_mod_cast h2
  · have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
    have h1 : (1 : ℕ) ∈ SizeData₂.lifts D := Finset.mem_Icc.2 ⟨le_rfl, by have := D.R.two_le_m; omega⟩
    have hw := Formalism.L2.G.wRec_eq D u g 1 h1
    have hf := hfill u (D.eTau.symm g) hm
    have hfe : (((D.hcW u (D.eTau.symm g)).e ⟨0, hm⟩ : ℚ) : ℝ) = Formalism.BasicNotions.wj D 1 (D.eTau.symm g) := by
      unfold Formalism.BasicNotions.wj
      rw [dif_pos (by omega), D.hcW_e]
    rw [hfe] at hf
    have hka : Formalism.MainNotions.G.kaJ D 1 = ((D.R.k : ℝ) + D.R.t + 1) / 2 := by
      unfold Formalism.MainNotions.G.kaJ; push_cast; ring
    have h2 : (((16 * D.R.k * Δ : ℕ) : ℤ) : ℝ) ≤ ((Formalism.L2.G.wRec D u g 1 : ℤ) : ℝ) := by
      rw [hw, hka, hc]; linarith
    exact_mod_cast h2

/- English proof (translation)
Take `⟨hD1, hmid, hoff, hfill⟩` from `facts_pre hS hO`. Conclude with `cloudBound_of (w.D Z) (Delv K.s K.cD) (by exact_mod_cast hD1) (fun u τ i h1 h2 => hmid u τ i h1 h2) (fun u τ hk h => hoff u τ hk h) (fun u τ hm => hfill u τ hm) u`.
-/
theorem cloudBound_rec {K : Ctx} (hS : ScaleOK K) {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T)
    (hO : K.Over B.toPre) (Z : w.Lt) (u : (w.D Z).what₂.Word) :
    Formalism.L2.G.CloudBound (w.D Z) u (16 * (w.D Z).R.k * Delv K.s K.cD) := by
  obtain ⟨hD1, hmid, hoff, hfill⟩ := facts_pre hS hO
  exact cloudBound_of (w.D Z) (Delv K.s K.cD) (by exact_mod_cast hD1) (fun u τ i h1 h2 => hmid u τ i h1 h2)
    (fun u τ hk h => hoff u τ hk h) (fun u τ hm => hfill u τ hm) u

end GlobalTheory.Mem.Top.Bl.CloudRec

namespace GlobalTheory.Mem.Top.Bl.CloudRec

/- English proof (translation)
Take `⟨ε0, hε0, H⟩` from `evG_good`. Use `⟨ε0, hε0, fun eps C8 C5 c6 Cb he h1 h2 h3 => ?_⟩` and prove the remaining obligations. Take `⟨K0, HK⟩` from `H eps C8 C5 c6 Cb he h1 h2 h3`. Use `⟨K0, fun C hC h4 h5 => ?_⟩` and prove the remaining obligations. Take `⟨c1, H1⟩` from `HK C hC h4 h5`.

Use `⟨max c1 0, fun cD hcD => ?_⟩` and prove the remaining obligations. Take `⟨c2, H2⟩` from `H1 cD (le_trans (le_max_left _ _) hcD)`. Use `⟨c2, fun ch hch => ?_⟩` and prove the remaining obligations. Take `⟨x0, -⟩` from `H2 ch hch`. Take `⟨x1, hx1⟩` from `scaleOK_large eps he h2 cD (le_trans (le_max_right _ _) hcD)`.

Conclude with `⟨max x0 x1, fun K _ e2 _ e4 e5 _ => hx1 K e4 e2 (le_trans (le_max_right _ _) e5)⟩`.
-/
theorem evG_scaleOK : EvG ScaleOK := by
  obtain ⟨ε0, hε0, H⟩ := evG_good
  refine ⟨ε0, hε0, fun eps C8 C5 c6 Cb he h1 h2 h3 => ?_⟩
  obtain ⟨K0, HK⟩ := H eps C8 C5 c6 Cb he h1 h2 h3
  refine ⟨K0, fun C hC h4 h5 => ?_⟩
  obtain ⟨c1, H1⟩ := HK C hC h4 h5
  refine ⟨max c1 0, fun cD hcD => ?_⟩
  obtain ⟨c2, H2⟩ := H1 cD (le_trans (le_max_left _ _) hcD)
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, -⟩ := H2 ch hch
  obtain ⟨x1, hx1⟩ := scaleOK_large eps he h2 cD (le_trans (le_max_right _ _) hcD)
  exact ⟨max x0 x1, fun K _ e2 _ e4 e5 _ => hx1 K e4 e2 (le_trans (le_max_right _ _) e5)⟩

end GlobalTheory.Mem.Top.Bl.CloudRec

namespace GlobalTheory.Mem.Top.Bl

/- English proof (translation)
The claim follows from `Step.of_evG (CloudRec.evG_scaleOK.imp fun K _ _ _ _ hS B _ _ hO _ _ _ w _ Z => ⟨16 * (w.D Z).R.k * Delv K.s K.cD, CloudRec.cloudBound_rec hS w hO Z, fun L hL hV => by unfold G.cG rw [L.Sc_eq, hV.Del_eq, hL] push_cast linarith⟩)`.
-/
theorem cloudBound_step : StepW Pinned fun K B f T w => ∀ Z : w.Lt, ∃ c : ℕ, (∀ u, Formalism.L2.G.CloudBound (w.D Z) u c) ∧
    ∀ L : SizeData₂ (w.D Z), L.sc = K.s → Val K.C K.cD K.ch L → (c : ℝ) ≤ G.cG L :=
  Step.of_evG (CloudRec.evG_scaleOK.imp fun K _ _ _ _ hS B _ _ hO _ _ _ w _ Z =>
    ⟨16 * (w.D Z).R.k * Delv K.s K.cD, CloudRec.cloudBound_rec hS w hO Z, fun L hL hV => by
      unfold G.cG
      rw [L.Sc_eq, hV.Del_eq, hL]
      push_cast
      linarith⟩)

end GlobalTheory.Mem.Top.Bl
