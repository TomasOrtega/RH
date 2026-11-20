import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsNefCountAlongMultiples
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsAmpleCountAlongMultiples
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsNefCountDimZero
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenDegGeomDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConstantShift
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsSemipositiveRelConstShift
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.CharacterNondegenerate
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.CoeffLeOfEvalLeMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace NefCountAlongMultiples

section Transport

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

/- English proof (translation)
Establish `hc : Real.exp (-((p : ℝ) * C)) ^ n * Real.exp (((p * n : ℕ) : ℝ) * C) = 1`. Rewrite using `[← Real.exp_nat_mul, ← Real.exp_add]`. Use `Real.exp_zero using 2` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hsm : ∀ s : {s : chartLat y (HermLine.constShift N ((p : ℝ) * C)).a n // IsSmallH (mCoordIdeal y) y (HermLine.constShift N ((p : ℝ) * C)) n (s : Ω)}, (s.1 : Ω) * e ^ (p * n) ∈ chartLat y A.a (q * n) ∧ IsSmallH (mCoordIdeal y) y A (q * n) ((s.1 : Ω) * e ^ (p * n))`. Introduce and unpack `⟨⟨x, hx⟩, hxs⟩`. Establish `hxs' : IsSmallH (mCoordIdeal y) y (HermLine.constShift N ((p : ℝ) * C)) n x` using `hxs`. Rewrite `hx` using `[constShift_a]`. Use `show x * e ^ (p * n) ∈ chartLat y A.a (q * n) ∧ IsSmallH (mCoordIdeal y) y A (q * n) (x * e ^ (p * n))`.

Take `⟨hm, hb⟩` from `hmap x hx`. Use `⟨hm, fun dg dh g h z hg hh hdeg heq hz => ?_⟩` and prove the remaining obligations. Establish `hB : IsBoundedH (mCoordIdeal y) y N n (Real.exp (-((p : ℝ) * C)) ^ n) x`. Introduce `dg' dh' g' h' z' hg' hh' hdeg' heq' hz'`. Use `hxs' dg' dh' g' h' z' hg' hh' (by rw [constShift_a]; exact hdeg') heq' hz'` as an intermediate fact.

Rewrite `this` using `[constShift_h, mul_pow]`. Conclude with `this.trans (le_of_eq (by ring))`. Use `hb _ hB dg dh g h z hg hh hdeg heq hz` as an intermediate fact. Rewrite `this` using `[hc, one_mul]`. Then use the resulting hypothesis. Establish `: Finite {s : chartLat y A.a (q * n) // IsSmallH (mCoordIdeal y) y A (q * n) (s : Ω)}` using `hfin.to_subtype`.

Establish `hcard : Nat.card {s : chartLat y (HermLine.constShift N ((p : ℝ) * C)).a n // IsSmallH (mCoordIdeal y) y (HermLine.constShift N ((p : ℝ) * C)) n (s : Ω)} ≤ Nat.card {s : chartLat y A.a (q * n) // IsSmallH (mCoordIdeal y) y A (q * n) (s : Ω)}` using `Nat.card_le_card_of_injective (fun s => ⟨⟨(s.1 : Ω) * e ^ (p * n), (hsm s).1⟩, (hsm s).2⟩) fun s s' h => by`. Simplify using `only [Subtype.mk.injEq] at h`. Conclude with `Subtype.ext (Subtype.ext (mul_right_cancel₀ (pow_ne_zero _ he0) h))`. Unfold `smallSectionCount`. Break down `Nat.eq_zero_or_pos (Nat.card {s : chartLat y (HermLine.constShift N ((p : ℝ) * C)).a n // IsSmallH (mCoordIdeal y) y (HermLine.constShift N ((p : ℝ) * C)) n (s : Ω)}) with h0 | hpos` into its components or cases.

Rewrite using `[h0, Nat.cast_zero, Real.log_zero]`. Conclude with `Real.log_natCast_nonneg _`. Conclude with `Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hcard)`.
-/
theorem count_shift_le {y : (Σ k, ι k) → Ω} {A N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {e : Ω} {C : ℝ} {p q n : ℕ}
    (he0 : e ≠ 0)
    (hmap : ∀ s : Ω, s ∈ chartLat y N.a n → s * e ^ (p * n) ∈ chartLat y A.a (q * n) ∧
      ∀ c : ℝ, IsBoundedH (mCoordIdeal y) y N n c s →
        IsBoundedH (mCoordIdeal y) y A (q * n) (c * Real.exp (((p * n : ℕ) : ℝ) * C)) (s * e ^ (p * n)))
    (hfin : {s : chartLat y A.a (q * n) | IsSmallH (mCoordIdeal y) y A (q * n) (s : Ω)}.Finite) :
    smallSectionCount (IsSmallH (mCoordIdeal y) y (HermLine.constShift N ((p : ℝ) * C)))
        (chartLat y (HermLine.constShift N ((p : ℝ) * C)).a) n ≤
      smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) (q * n) := by
  have hc : Real.exp (-((p : ℝ) * C)) ^ n * Real.exp (((p * n : ℕ) : ℝ) * C) = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    convert Real.exp_zero using 2
    push_cast
    ring
  have hsm : ∀ s : {s : chartLat y (HermLine.constShift N ((p : ℝ) * C)).a n //
      IsSmallH (mCoordIdeal y) y (HermLine.constShift N ((p : ℝ) * C)) n (s : Ω)},
      (s.1 : Ω) * e ^ (p * n) ∈ chartLat y A.a (q * n) ∧
        IsSmallH (mCoordIdeal y) y A (q * n) ((s.1 : Ω) * e ^ (p * n)) := by
    rintro ⟨⟨x, hx⟩, hxs⟩
    have hxs' : IsSmallH (mCoordIdeal y) y (HermLine.constShift N ((p : ℝ) * C)) n x := hxs
    rw [constShift_a] at hx
    show x * e ^ (p * n) ∈ chartLat y A.a (q * n) ∧ IsSmallH (mCoordIdeal y) y A (q * n) (x * e ^ (p * n))
    obtain ⟨hm, hb⟩ := hmap x hx
    refine ⟨hm, fun dg dh g h z hg hh hdeg heq hz => ?_⟩
    have hB : IsBoundedH (mCoordIdeal y) y N n (Real.exp (-((p : ℝ) * C)) ^ n) x := by
      intro dg' dh' g' h' z' hg' hh' hdeg' heq' hz'
      have := hxs' dg' dh' g' h' z' hg' hh' (by rw [constShift_a]; exact hdeg') heq' hz'
      rw [constShift_h, mul_pow] at this
      exact this.trans (le_of_eq (by ring))
    have := hb _ hB dg dh g h z hg hh hdeg heq hz
    rwa [hc, one_mul] at this
  have : Finite {s : chartLat y A.a (q * n) // IsSmallH (mCoordIdeal y) y A (q * n) (s : Ω)} :=
    hfin.to_subtype
  have hcard : Nat.card {s : chartLat y (HermLine.constShift N ((p : ℝ) * C)).a n //
        IsSmallH (mCoordIdeal y) y (HermLine.constShift N ((p : ℝ) * C)) n (s : Ω)} ≤
      Nat.card {s : chartLat y A.a (q * n) // IsSmallH (mCoordIdeal y) y A (q * n) (s : Ω)} :=
    Nat.card_le_card_of_injective (fun s => ⟨⟨(s.1 : Ω) * e ^ (p * n), (hsm s).1⟩, (hsm s).2⟩) fun s s' h => by
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (Subtype.ext (mul_right_cancel₀ (pow_ne_zero _ he0) h))
  unfold smallSectionCount
  rcases Nat.eq_zero_or_pos (Nat.card {s : chartLat y (HermLine.constShift N ((p : ℝ) * C)).a n //
      IsSmallH (mCoordIdeal y) y (HermLine.constShift N ((p : ℝ) * C)) n (s : Ω)}) with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hcard)

end Transport

/- English proof (translation)
Establish `hQ : 0 < q ^ (D + 1)` using `by positivity`. Establish `hQD : 0 < q ^ D` using `by positivity`. Rewrite `hI`, `hG` using `[abs_sub_lt_iff]`. Establish `h1 : (T - ε / 4) * q ^ (D + 1) < I` using `(lt_div_iff₀ hQ).1 (by linarith [hI.2])`. Establish `h2 : G < (g + ε / 4) * q ^ D` using `(div_lt_iff₀ hQD).1 (by linarith [hG.1])`.

Establish `h3 : ((D : ℝ) + 1) * (((1 : ℕ) : ℝ) * C) * G ≤ ((D : ℝ) + 1) * C * ((g + ε / 4) * q ^ D)`. Rewrite using `[Nat.cast_one, one_mul]`. Conclude with `mul_le_mul_of_nonneg_left h2.le (by positivity)`. Establish `h4 : ((D : ℝ) + 1) * C * ((g + ε / 4) * q ^ D) ≤ ε / 4 * q ^ (D + 1)`. Combine the equalities or inequalities in the displayed calculation.

Use polynomial arithmetic with `[mul_pos hε hQ]`.
-/
theorem num_bound {T ε I G g C q : ℝ} {D : ℕ} (hε : 0 < ε) (hq : 0 < q) (hC : 0 ≤ C)
    (hI : |I / q ^ (D + 1) - T| < ε / 4) (hG : |G / q ^ D - g| < ε / 4)
    (hqC : ((D : ℝ) + 1) * C * (g + ε / 4) < q * (ε / 4)) :
    (T - ε) * q ^ (D + 1) + ε / 4 * q ^ (D + 1) ≤ I - ((D : ℝ) + 1) * (((1 : ℕ) : ℝ) * C) * G := by
  have hQ : 0 < q ^ (D + 1) := by positivity
  have hQD : 0 < q ^ D := by positivity
  rw [abs_sub_lt_iff] at hI hG
  have h1 : (T - ε / 4) * q ^ (D + 1) < I := (lt_div_iff₀ hQ).1 (by linarith [hI.2])
  have h2 : G < (g + ε / 4) * q ^ D := (div_lt_iff₀ hQD).1 (by linarith [hG.1])
  have h3 : ((D : ℝ) + 1) * (((1 : ℕ) : ℝ) * C) * G ≤ ((D : ℝ) + 1) * C * ((g + ε / 4) * q ^ D) := by
    rw [Nat.cast_one, one_mul]
    exact mul_le_mul_of_nonneg_left h2.le (by positivity)
  have h4 : ((D : ℝ) + 1) * C * ((g + ε / 4) * q ^ D) ≤ ε / 4 * q ^ (D + 1) :=
    calc ((D : ℝ) + 1) * C * ((g + ε / 4) * q ^ D) = (((D : ℝ) + 1) * C * (g + ε / 4)) * q ^ D := by ring
      _ ≤ (q * (ε / 4)) * q ^ D := (mul_lt_mul_of_pos_right hqC hQD).le
      _ = ε / 4 * q ^ (D + 1) := by ring
  nlinarith [mul_pos hε hQ]

/- English proof (translation)
Take `⟨b, hb1, hev⟩` from `hAC K ι Ω y D (HermLine.constShift N ((p : ℝ) * C)) P0 II hD hII har hb hP0 (isSemipositiveRel_constShift hsp _) (isConjInvariantH_constShift hci _) (by rw [constShift_a]; exact hamp) (by rw [constShift_a]; exact hampl) (ε / 4 * (q : ℝ) ^ (D + 1)) (by positivity)`. Establish `htop : II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.constShift N ((p : ℝ) * C)) = II K ι (mCoordIdeal y) (D + 1) (fun _ => N) - ((D : ℝ) + 1) * ((p : ℝ) * C) * (genDeg (mCoordIdeal y) D N.a : ℝ)`. Rewrite using `[ConstantShift.proof K ι (II K ι) (mCoordIdeal y) D N _ (hII K ι) har hsp.1, hGD K ι Ω y D N har hsp.1]`. Establish `hfin` using `(hPk K ι Ω y D A (chartLat y A.a) har hb hsA (fun τ _ hs' c hc' => isIntegral_algebraMap (x := (⟨_, hs' c hc'⟩ : chartRingZ y c)))).1`. Use `⟨q * b, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩` and prove the remaining obligations.

Use `filter_upwards [hev] with j hj`. Establish `hX : (0 : ℝ) ≤ ((b * j : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ (II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.constShift N ((p : ℝ) * C)) - ε / 4 * (q : ℝ) ^ (D + 1)) * (((b * j : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := mul_le_mul_of_nonneg_right (by rw [htop]; linarith) hX`. Use `_ ≤ _ := hj`. Use `_ ≤ smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) (q * (b * j)) := count_shift_le he0 (hmap (b * j)) (hfin _)`. Use `_ = _ := by rw [mul_assoc]`.
-/
theorem along_of_shift (hAC : AmpleCountAlongMultiples.Statement) (hGD : GenDegGeomDeg.Statement)
    (hPk : PackingStatement)
    {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {D : ℕ} {A N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    {P0 : Ideal (MRing ι)} {II : IntersectionSystem} {e : Ω} {C T ε : ℝ} {p q : ℕ}
    (hD : 1 ≤ D) (hII : IsIntersectionSystem II) (har : IsArithVar (mCoordIdeal y) (D + 1)) (hb : Birational y)
    (hP0 : P0 ≤ mCoordIdeal y) (hsA : IsSmoothHerm A) (hq : 1 ≤ q) (hε : 0 < ε)
    (hsp : IsSemipositiveRel P0 (mCoordIdeal y) N) (hci : IsConjInvariantH N)
    (hamp : KH.AmpleV ℚ (KH.genIdeal y) N.a)
    (hampl : ∀ ℓ : ℕ, ℓ.Prime → KH.AmpleV (ZMod ℓ) (fibreIdeal ℓ y) N.a) (he0 : e ≠ 0)
    (hmap : ∀ (n : ℕ) (s : Ω), s ∈ chartLat y N.a n → s * e ^ (p * n) ∈ chartLat y A.a (q * n) ∧
      ∀ c : ℝ, IsBoundedH (mCoordIdeal y) y N n c s →
        IsBoundedH (mCoordIdeal y) y A (q * n) (c * Real.exp (((p * n : ℕ) : ℝ) * C)) (s * e ^ (p * n)))
    (hnum : (T - ε) * (q : ℝ) ^ (D + 1) + ε / 4 * (q : ℝ) ^ (D + 1) ≤
      II K ι (mCoordIdeal y) (D + 1) (fun _ => N) -
        ((D : ℝ) + 1) * ((p : ℝ) * C) * (genDeg (mCoordIdeal y) D N.a : ℝ)) :
    ∃ a : ℕ, 1 ≤ a ∧ ∀ᶠ k : ℕ in atTop,
      (T - ε) * (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) ≤
        smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) (a * k) := by
  obtain ⟨b, hb1, hev⟩ := hAC K ι Ω y D (HermLine.constShift N ((p : ℝ) * C)) P0 II hD hII har hb hP0
    (isSemipositiveRel_constShift hsp _) (isConjInvariantH_constShift hci _)
    (by rw [constShift_a]; exact hamp) (by rw [constShift_a]; exact hampl)
    (ε / 4 * (q : ℝ) ^ (D + 1)) (by positivity)
  have htop : II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.constShift N ((p : ℝ) * C)) =
      II K ι (mCoordIdeal y) (D + 1) (fun _ => N) -
        ((D : ℝ) + 1) * ((p : ℝ) * C) * (genDeg (mCoordIdeal y) D N.a : ℝ) := by
    rw [ConstantShift.proof K ι (II K ι) (mCoordIdeal y) D N _ (hII K ι) har hsp.1, hGD K ι Ω y D N har hsp.1]
  have hfin := (hPk K ι Ω y D A (chartLat y A.a) har hb hsA
    (fun τ _ hs' c hc' => isIntegral_algebraMap (x := (⟨_, hs' c hc'⟩ : chartRingZ y c)))).1
  refine ⟨q * b, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
  filter_upwards [hev] with j hj
  have hX : (0 : ℝ) ≤ ((b * j : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by positivity
  calc (T - ε) * (((q * b * j : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))
      = ((T - ε) * (q : ℝ) ^ (D + 1)) * (((b * j : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
        push_cast
        ring
    _ ≤ (II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.constShift N ((p : ℝ) * C)) -
          ε / 4 * (q : ℝ) ^ (D + 1)) * (((b * j : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_right (by rw [htop]; linarith) hX
    _ ≤ _ := hj
    _ ≤ smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) (q * (b * j)) :=
        count_shift_le he0 (hmap (b * j)) (hfin _)
    _ = _ := by rw [mul_assoc]

/- English proof (translation)
Establish `: CharZero Ω` using `ArithmeticVolumeDegreeZero.charZero_of_horizontal y har.2.2.1`. Set `_ : LinearOrder K` to `LinearOrder.lift' _ (Fintype.equivFin K).injective`. Set `_ : ∀ k, LinearOrder (ι k)` to `fun k => LinearOrder.lift' _ (Fintype.equivFin (ι k)).injective`. Take `⟨k, e, C, -, hC, he0, -, -, hpq, hconv⟩` from `hG2 K ι Ω y D A P0 II hD hII har hb hA`. Take `⟨δ, hδ, hδc⟩` from `hconv (ε / 4) (by linarith)`.

Establish `hg0 : (0 : ℝ) < (genDeg (mCoordIdeal y) D A.a : ℝ)` using `by exact_mod_cast hA.big`. Take `⟨q, hq⟩` from `exists_nat_gt ((k : ℝ) + 1 / δ + 4 * (((D : ℝ) + 1) * C * ((genDeg (mCoordIdeal y) D A.a : ℝ) + ε / 4)) / ε)`. Establish `hX0 : 0 ≤ 4 * (((D : ℝ) + 1) * C * ((genDeg (mCoordIdeal y) D A.a : ℝ) + ε / 4)) / ε`. Check the signs of the components of the expression. Establish `hδ' : 0 < 1 / δ` using `by positivity`.

Establish `hkq : k * 1 < q`. Establish `: (k : ℝ) < q` using `by linarith`. Rewrite using `[mul_one]`. Conclude with `this` after adjusting the coercions. Establish `hq1 : 1 ≤ q` using `by omega`.

Establish `hqpos : (0 : ℝ) < q` using `by exact_mod_cast hq1`. Establish `hpqδ : ((1 : ℕ) : ℝ) / q < δ`. Establish `h1 : 1 / δ < q` using `by linarith`. Rewrite `h1` using `[div_lt_iff₀ hδ]`. Rewrite using `[Nat.cast_one, div_lt_iff₀ hqpos]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hqC : ((D : ℝ) + 1) * C * ((genDeg (mCoordIdeal y) D A.a : ℝ) + ε / 4) < q * (ε / 4)`. Establish `h1 : 4 * (((D : ℝ) + 1) * C * ((genDeg (mCoordIdeal y) D A.a : ℝ) + ε / 4)) / ε < q` using `by linarith`. Rewrite `h1` using `[div_lt_iff₀ hε]`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨hsp, hci, hamp, hampl, hmap⟩` from `hpq 1 q one_pos hkq`. Take `⟨htop, hdeg⟩` from `hδc 1 q one_pos (by omega) hpqδ`. Conclude with `along_of_shift hAC hGD hPk hD hII har hb hA.normalForm_baseLattice_le_dualSpan_sup_line hA.semipos.1 hq1 hε hsp hci hamp hampl he0 hmap (num_bound hε hqpos hC htop hdeg hqC)`.
-/
theorem big (hG2 : G2.Statement) (hAC : AmpleCountAlongMultiples.Statement) (hGD : GenDegGeomDeg.Statement)
    (hPk : PackingStatement)
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι))
    (II : IntersectionSystem) (hD : 1 ≤ D) (hII : IsIntersectionSystem II)
    (har : IsArithVar (mCoordIdeal y) (D + 1)) (hb : Birational y) (hA : IsNefBigDatum P0 y D A)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a : ℕ, 1 ≤ a ∧ ∀ᶠ k : ℕ in atTop,
      (II K ι (mCoordIdeal y) (D + 1) (fun _ => A) - ε) *
          (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) ≤
        smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) (a * k) := by
  have : CharZero Ω := ArithmeticVolumeDegreeZero.charZero_of_horizontal y har.2.2.1
  let _ : LinearOrder K := LinearOrder.lift' _ (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k => LinearOrder.lift' _ (Fintype.equivFin (ι k)).injective
  obtain ⟨k, e, C, -, hC, he0, -, -, hpq, hconv⟩ := hG2 K ι Ω y D A P0 II hD hII har hb hA
  obtain ⟨δ, hδ, hδc⟩ := hconv (ε / 4) (by linarith)
  have hg0 : (0 : ℝ) < (genDeg (mCoordIdeal y) D A.a : ℝ) := by exact_mod_cast hA.big
  obtain ⟨q, hq⟩ := exists_nat_gt ((k : ℝ) + 1 / δ +
    4 * (((D : ℝ) + 1) * C * ((genDeg (mCoordIdeal y) D A.a : ℝ) + ε / 4)) / ε)
  have hX0 : 0 ≤ 4 * (((D : ℝ) + 1) * C * ((genDeg (mCoordIdeal y) D A.a : ℝ) + ε / 4)) / ε := by
    positivity
  have hδ' : 0 < 1 / δ := by positivity
  have hkq : k * 1 < q := by
    have : (k : ℝ) < q := by linarith
    rw [mul_one]
    exact_mod_cast this
  have hq1 : 1 ≤ q := by omega
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  have hpqδ : ((1 : ℕ) : ℝ) / q < δ := by
    have h1 : 1 / δ < q := by linarith
    rw [div_lt_iff₀ hδ] at h1
    rw [Nat.cast_one, div_lt_iff₀ hqpos]
    linarith
  have hqC : ((D : ℝ) + 1) * C * ((genDeg (mCoordIdeal y) D A.a : ℝ) + ε / 4) < q * (ε / 4) := by
    have h1 : 4 * (((D : ℝ) + 1) * C * ((genDeg (mCoordIdeal y) D A.a : ℝ) + ε / 4)) / ε < q := by linarith
    rw [div_lt_iff₀ hε] at h1
    linarith
  obtain ⟨hsp, hci, hamp, hampl, hmap⟩ := hpq 1 q one_pos hkq
  obtain ⟨htop, hdeg⟩ := hδc 1 q one_pos (by omega) hpqδ
  exact along_of_shift hAC hGD hPk hD hII har hb hA.normalForm_baseLattice_le_dualSpan_sup_line hA.semipos.1 hq1 hε hsp hci hamp hampl he0 hmap
    (num_bound hε hqpos hC htop hdeg hqC)

/- English proof (translation)
Take `⟨B, hB⟩` from `NormCountBounded.norm_count_bounded D hC`. Establish `hbdd : IsBoundedUnder (· ≤ ·) atTop (fun k : ℕ => smallSectionCount Pr La (1 * k) / (((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)))`. Use `⟨B, ?_⟩` and prove the remaining obligations. Simplify using `using hB`. Use `le_of_forall_pos_le_add fun ε hε => ?_` and prove the remaining obligations.

Take `⟨a, ha, hev⟩` from `h ε hε`. Establish `hfreq : ∃ᶠ k : ℕ in atTop, T - ε ≤ smallSectionCount Pr La (1 * k) / (((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))`. Rewrite using `[frequently_atTop]`. Introduce `N`. Take `⟨k, hk⟩` from `(hev.and (eventually_ge_atTop (N + 1))).exists`.

Use `⟨a * k, le_trans (by omega) (Nat.le_mul_of_pos_left k ha), ?_⟩` and prove the remaining obligations. Establish `hak : 0 < a * k` using `Nat.mul_pos ha (by omega)`. Establish `hpos : (0 : ℝ) < ((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)` using `div_pos (pow_pos (by exact_mod_cast hak) _) (by exact_mod_cast Nat.factorial_pos _)`. Rewrite using `[one_mul, le_div_iff₀ hpos]`. Conclude with `hk.1`.

Use `le_limsup_of_frequently_le hfreq hbdd` as an intermediate fact. Unfold `arVolP`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem le_arithmeticVolume_of_alongMultiples {Ω : Type} [Field Ω] {Pr : ℕ → Ω → Prop} {La : ℕ → AddSubgroup Ω} {D : ℕ}
    {T Cp : ℝ} (hC : ∀ τ, smallSectionCount Pr La τ ≤ Cp * ((τ : ℝ) + 1) ^ (D + 1))
    (h : ∀ ε : ℝ, 0 < ε → ∃ a : ℕ, 1 ≤ a ∧ ∀ᶠ k : ℕ in atTop,
      (T - ε) * (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) ≤ smallSectionCount Pr La (a * k)) :
    T ≤ arVolP Pr La 1 D := by
  obtain ⟨B, hB⟩ := NormCountBounded.norm_count_bounded D hC
  have hbdd : IsBoundedUnder (· ≤ ·) atTop (fun k : ℕ => smallSectionCount Pr La (1 * k) /
      (((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))) := by
    refine ⟨B, ?_⟩
    simpa using hB
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨a, ha, hev⟩ := h ε hε
  have hfreq : ∃ᶠ k : ℕ in atTop, T - ε ≤ smallSectionCount Pr La (1 * k) /
      (((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
    rw [frequently_atTop]
    intro N
    obtain ⟨k, hk⟩ := (hev.and (eventually_ge_atTop (N + 1))).exists
    refine ⟨a * k, le_trans (by omega) (Nat.le_mul_of_pos_left k ha), ?_⟩
    have hak : 0 < a * k := Nat.mul_pos ha (by omega)
    have hpos : (0 : ℝ) < ((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) :=
      div_pos (pow_pos (by exact_mod_cast hak) _) (by exact_mod_cast Nat.factorial_pos _)
    rw [one_mul, le_div_iff₀ hpos]
    exact hk.1
  have := le_limsup_of_frequently_le hfreq hbdd
  unfold arVolP
  linarith

/- English proof (translation)
Introduce `K _ ι _ Ω _ _ y D M P0 II hD hII har hb hM`. Take `⟨-, Cp, hCp⟩` from `hPk K ι Ω y D M (chartLat y M.a) har hb hM.semipos.1 (fun τ _ hs' c hc' => isIntegral_algebraMap (x := (⟨_, hs' c hc'⟩ : chartRingZ y c)))`. Conclude with `le_arithmeticVolume_of_alongMultiples hCp fun ε hε => big hG2 hAC hGD hPk K ι Ω y D M P0 II hD hII har hb hM ε hε`.
-/
theorem statementB (hG2 : G2.Statement) (hAC : AmpleCountAlongMultiples.Statement)
    (hGD : GenDegGeomDeg.Statement) (hPk : PackingStatement) : G6.StatementB := by
  intro K _ ι _ Ω _ _ y D M P0 II hD hII har hb hM
  obtain ⟨-, Cp, hCp⟩ := hPk K ι Ω y D M (chartLat y M.a) har hb hM.semipos.1
    (fun τ _ hs' c hc' => isIntegral_algebraMap (x := (⟨_, hs' c hc'⟩ : chartRingZ y c)))
  exact le_arithmeticVolume_of_alongMultiples hCp fun ε hε => big hG2 hAC hGD hPk K ι Ω y D M P0 II hD hII har hb hM ε hε

/- English proof (translation)
Establish `: CharZero Ω` using `ArithmeticVolumeDegreeZero.charZero_of_horizontal y har.2.2.1`. Establish `hB` using `statementB hG2 hAC hGD hPk`. Take `⟨C, hC0, hC⟩` from `hV K ι Ω y D A P0 hD har hb hP0 hs hnef hc`. Take `⟨p, hpdeg, hpc, hp⟩` from `hI K ι II (mCoordIdeal y) (D + 1) A (fsH ι) hII har hs.1 (GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs 1)`. Take `⟨r, hrdeg, hrc, hr⟩` from `hG K ι (mCoordIdeal y) D A.a ((1 : ℤ) • (fsH ι).a) har`.

Establish `hbound : ∀ q : ℕ, 1 ≤ q → p.eval (q : ℝ) ≤ C * ((q : ℝ) + 1) * r.eval (q : ℝ)`. Introduce `q hq`. Rewrite using `[← hp q, ← hr q]`. Conclude with `(hB K ι Ω y D _ P0 II hD hII har hb (hN K ι Ω y D A P0 hD har hb hP0 hs hnef hc q hq)).trans (hC q hq)`. Rewrite using `[← hpc]`.

Conclude with `ArithmeticVolumeDegreeZero.coeff_le_of_eval_le_mul p r hC0 hpdeg hrdeg (by rw [hrc]; exact_mod_cast hdeg) hbound`.
-/
theorem top_nonpos (hG2 : G2.Statement) (hAC : AmpleCountAlongMultiples.Statement)
    (hGD : GenDegGeomDeg.Statement) (hPk : PackingStatement) (hN : ShiftNefBig.Statement)
    (hV : ShiftVolumeBound.Statement) (hI : ShiftIntersectionPolynomial.Statement)
    (hG : ShiftDegreePolynomial.Statement)
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {D : ℕ} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {P0 : Ideal (MRing ι)}
    {II : IntersectionSystem} (hD : 1 ≤ D) (hII : IsIntersectionSystem II)
    (har : IsArithVar (mCoordIdeal y) (D + 1)) (hb : Birational y) (hP0 : P0 ≤ mCoordIdeal y)
    (hs : IsSemipositiveRel P0 (mCoordIdeal y) A) (hnef : NefOnFibres (mCoordIdeal y) A.a)
    (hc : IsConjInvariantH A) (hdeg : genDeg (mCoordIdeal y) D A.a ≤ 0) :
    II K ι (mCoordIdeal y) (D + 1) (fun _ => A) ≤ 0 := by
  have : CharZero Ω := ArithmeticVolumeDegreeZero.charZero_of_horizontal y har.2.2.1
  have hB := statementB hG2 hAC hGD hPk
  obtain ⟨C, hC0, hC⟩ := hV K ι Ω y D A P0 hD har hb hP0 hs hnef hc
  obtain ⟨p, hpdeg, hpc, hp⟩ := hI K ι II (mCoordIdeal y) (D + 1) A (fsH ι) hII har hs.1
    (GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs 1)
  obtain ⟨r, hrdeg, hrc, hr⟩ := hG K ι (mCoordIdeal y) D A.a ((1 : ℤ) • (fsH ι).a) har
  have hbound : ∀ q : ℕ, 1 ≤ q → p.eval (q : ℝ) ≤ C * ((q : ℝ) + 1) * r.eval (q : ℝ) := by
    intro q hq
    rw [← hp q, ← hr q]
    exact (hB K ι Ω y D _ P0 II hD hII har hb (hN K ι Ω y D A P0 hD har hb hP0 hs hnef hc q hq)).trans (hC q hq)
  rw [← hpc]
  exact ArithmeticVolumeDegreeZero.coeff_le_of_eval_le_mul p r hC0 hpdeg hrdeg (by rw [hrc]; exact_mod_cast hdeg) hbound

/- English proof (translation)
Introduce `K _ ι _ Ω _ y D A P0 II hII har hb hP0 hs hc hnef hgen hht ε hε`. Distinguish the cases in `hT : II K ι (mCoordIdeal y) (D + 1) (fun _ => A) - ε ≤ 0`. Conclude with `⟨1, le_rfl, Eventually.of_forall fun n => (mul_nonpos_of_nonpos_of_nonneg hT (by positivity)).trans (Real.log_natCast_nonneg _)⟩`. Break down `Nat.eq_zero_or_pos D with rfl | hD` into its components or cases. Use `⟨1, le_rfl, ?_⟩ filter_upwards [hZ K ι Ω y A P0 II hII har hb hP0 hs hc hnef hgen hht ε hε] with n hn` and prove the remaining obligations.

Simplify using `using hn`. Distinguish the cases in `hg : genDeg (mCoordIdeal y) D A.a ≤ 0`. Conclude with `absurd (top_nonpos hG2 hAC hGD hPk hN hV hI hG hD hII har hb hP0 hs hnef hc hg) (by linarith)`. Conclude with `big hG2 hAC hGD hPk K ι Ω y D A P0 II hD hII har hb ⟨hP0, hs, hc, hnef, by omega⟩ ε hε`.
-/
theorem proof (hG2 : G2.Statement) (hAC : AmpleCountAlongMultiples.Statement) (hGD : GenDegGeomDeg.Statement)
    (hPk : PackingStatement) (hZ : NefCountDimZero.Statement) (hN : ShiftNefBig.Statement)
    (hV : ShiftVolumeBound.Statement) (hI : ShiftIntersectionPolynomial.Statement)
    (hG : ShiftDegreePolynomial.Statement) : NefCountAlongMultiples.Statement := by
  intro K _ ι _ Ω _ y D A P0 II hII har hb hP0 hs hc hnef hgen hht ε hε
  by_cases hT : II K ι (mCoordIdeal y) (D + 1) (fun _ => A) - ε ≤ 0
  · exact ⟨1, le_rfl, Eventually.of_forall fun n =>
      (mul_nonpos_of_nonpos_of_nonneg hT (by positivity)).trans (Real.log_natCast_nonneg _)⟩
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · refine ⟨1, le_rfl, ?_⟩
    filter_upwards [hZ K ι Ω y A P0 II hII har hb hP0 hs hc hnef hgen hht ε hε] with n hn
    simpa using hn
  by_cases hg : genDeg (mCoordIdeal y) D A.a ≤ 0
  · exact absurd (top_nonpos hG2 hAC hGD hPk hN hV hI hG hD hII har hb hP0 hs hnef hc hg) (by linarith)
  exact big hG2 hAC hGD hPk K ι Ω y D A P0 II hD hII har hb ⟨hP0, hs, hc, hnef, by omega⟩ ε hε

end NefCountAlongMultiples

end

end GroundTheory.Heights₂.Heights.Targets
