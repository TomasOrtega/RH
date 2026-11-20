import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTopConstantTwist
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBirationalModelExists
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallSectionPointHeight
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsCurvePointsFinite
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCurveComplexPoint
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCurveIsOrbit
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPtsIntegralZeroLowerNE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDerived
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 Filter Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace LatticeWithoutBigness

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Establish `: {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0}`. Use extensionality with `z`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `isOpen_iInter_of_finite fun k => isOpen_iUnion fun i => isOpen_ne_fun (continuous_apply _) continuous_const`.
-/
theorem isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tensor_constLine_h (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ) (z : (Σ k, ι k) → ℂ) :
    (A.tensor (constLine c)).h z = A.h z * Real.exp (-c) := rfl

/- English proof (translation)
Use `show A.a + (constLine (ι := ι) c).a = A.a`. Simplify using `[constLine, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight]`.
-/
theorem tensor_constLine_a (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ) : (A.tensor (constLine c)).a = A.a := by
  show A.a + (constLine (ι := ι) c).a = A.a
  simp [constLine, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight]

/- English proof (translation)
Unfold `IsSmoothHerm`. Establish `: (A.tensor (constLine c)).h = fun z => A.h z * Real.exp (-c)` using `rfl`. Rewrite using `[this]`. Conclude with `hA.mul contDiffOn_const`.
-/
theorem isSmoothHerm_twist {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) (c : ℝ) :
    IsSmoothHerm (A.tensor (constLine c)) := by
  unfold IsSmoothHerm
  have : (A.tensor (constLine c)).h = fun z => A.h z * Real.exp (-c) := rfl
  rw [this]
  exact hA.mul contDiffOn_const

/- English proof (translation)
Establish `hev : (fun z => Real.log ((A.tensor (constLine c)).h z)) =ᶠ[𝓝 z] (fun z => Real.log (A.h z) + (-c))` using `by filter_upwards [isOpen_blockNonzero.mem_nhds hz] with z' hz'`. Rewrite using `[tensor_constLine_h, Real.log_mul (A.pos z' hz').ne' (Real.exp_pos _).ne', Real.log_exp]`. Establish `h2 : fderiv ℝ (fderiv ℝ (fun z => Real.log ((A.tensor (constLine c)).h z))) z = fderiv ℝ (fderiv ℝ (fun z => Real.log (A.h z))) z`. Rewrite using `[hev.fderiv.fderiv_eq]`. Use `congr 1`.

Use function extensionality and compare the values at `z'`. Conclude with `fderiv_add_const _`. Unfold `leviForm`. Rewrite using `[h2]`.
-/
theorem leviForm_twist (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (w : (Σ k, ι k) → ℂ) :
    leviForm (fun z => Real.log ((A.tensor (constLine c)).h z)) z w =
      leviForm (fun z => Real.log (A.h z)) z w := by
  have hev : (fun z => Real.log ((A.tensor (constLine c)).h z)) =ᶠ[𝓝 z]
      (fun z => Real.log (A.h z) + (-c)) := by
    filter_upwards [isOpen_blockNonzero.mem_nhds hz] with z' hz'
    rw [tensor_constLine_h, Real.log_mul (A.pos z' hz').ne' (Real.exp_pos _).ne', Real.log_exp]
  have h2 : fderiv ℝ (fderiv ℝ (fun z => Real.log ((A.tensor (constLine c)).h z))) z =
      fderiv ℝ (fderiv ℝ (fun z => Real.log (A.h z))) z := by
    rw [hev.fderiv.fderiv_eq]
    congr 1
    funext z'
    exact fderiv_add_const _
  unfold leviForm
  rw [h2]

/- English proof (translation)
Use `⟨isSmoothHerm_twist h.1 c, fun z hz w hw => ?_⟩` and prove the remaining obligations. Rewrite using `[leviForm_twist A c hz.1 w]`. Conclude with `h.2 z hz w hw`.
-/
theorem isSemipositiveRel_twist {P0 P : Ideal (MRing ι)} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (h : IsSemipositiveRel P0 P A) (c : ℝ) : IsSemipositiveRel P0 P (A.tensor (constLine c)) := by
  refine ⟨isSmoothHerm_twist h.1 c, fun z hz w hw => ?_⟩
  rw [leviForm_twist A c hz.1 w]
  exact h.2 z hz w hw

/- English proof (translation)
Introduce `z`. Rewrite using `[tensor_constLine_h, tensor_constLine_h, h z]`.
-/
theorem isConjInvariantH_twist {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (h : IsConjInvariantH A) (c : ℝ) :
    IsConjInvariantH (A.tensor (constLine c)) := by
  intro z
  rw [tensor_constLine_h, tensor_constLine_h, h z]

/- English proof (translation)
Rewrite using `[tensor_constLine_a]`. Conclude with `h`.
-/
theorem nefOnFibres_twist {P : Ideal (MRing ι)} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (h : NefOnFibres P A.a) (c : ℝ) :
    NefOnFibres P (A.tensor (constLine c)).a := by
  rw [tensor_constLine_a]
  exact h

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Establish `hzero : ∀ k : ℕ, smallSectionCount Q La (1 * k) / (((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) = 0`. Introduce `k`. Break down `Nat.eq_zero_or_pos k with hk | hk` into its components or cases.

Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Establish `hsub : Subsingleton {s : La (1 * k) // Q (1 * k) (s : Ω)}`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha⟩ ⟨b, hb⟩`.

Establish `ha0 : (a : Ω) = 0`. Assume the negation of the conclusion as `h0`. Conclude with `hne (1 * k) (by omega) a a.2 h0 ha`. Establish `hb0 : (b : Ω) = 0`. Assume the negation of the conclusion as `h0`.

Conclude with `hne (1 * k) (by omega) b b.2 h0 hb`. Conclude with `Subtype.ext (Subtype.ext (ha0.trans hb0.symm))`. Establish `hcard : Nat.card {s : La (1 * k) // Q (1 * k) (s : Ω)} ≤ 1` using `Finite.card_le_one_iff_subsingleton.mpr hsub`. Establish `hlog : smallSectionCount Q La (1 * k) = 0`. Unfold `smallSectionCount`.

Apply the tactic sequence `rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with h | h <;> rw [h] <;> simp`. Rewrite using `[hlog, zero_div]`. Establish `: arVolP Q La 1 D = 0`. Unfold `arVolP`. Simplify using `only [hzero]`.

Conclude with `limsup_const 0`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_small_section_of_arithmeticVolume_pos {Ω : Type} [Field Ω] {Q : ℕ → Ω → Prop} {La : ℕ → AddSubgroup Ω}
    {D : ℕ} (h : 0 < arVolP Q La 1 D) : ∃ τ, 1 ≤ τ ∧ ∃ s ∈ La τ, s ≠ 0 ∧ Q τ s := by
  by_contra hne
  push Not at hne
  have hzero : ∀ k : ℕ, smallSectionCount Q La (1 * k) /
      (((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) = 0 := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
    · have hsub : Subsingleton {s : La (1 * k) // Q (1 * k) (s : Ω)} := by
        constructor
        rintro ⟨a, ha⟩ ⟨b, hb⟩
        have ha0 : (a : Ω) = 0 := by
          by_contra h0
          exact hne (1 * k) (by omega) a a.2 h0 ha
        have hb0 : (b : Ω) = 0 := by
          by_contra h0
          exact hne (1 * k) (by omega) b b.2 h0 hb
        exact Subtype.ext (Subtype.ext (ha0.trans hb0.symm))
      have hcard : Nat.card {s : La (1 * k) // Q (1 * k) (s : Ω)} ≤ 1 :=
        Finite.card_le_one_iff_subsingleton.mpr hsub
      have hlog : smallSectionCount Q La (1 * k) = 0 := by
        unfold smallSectionCount
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with h | h <;> rw [h] <;> simp
      rw [hlog, zero_div]
  have : arVolP Q La 1 D = 0 := by
    unfold arVolP
    simp only [hzero]
    exact limsup_const 0
  linarith

/- English proof (translation)
Distinguish the cases in `hg : g ≤ 0`. Use `⟨e' + 1, by linarith, ?_⟩` and prove the remaining obligations. Establish `h1 : N * (e' + 1) * g = N * e' * g + N * g` using `by ring`. Establish `h2 : N * g ≤ 0` using `mul_nonpos_of_nonneg_of_nonpos hN.le hg`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `push Not at hg`. Establish `hd : 0 < (T - N * e' * g) / (2 * N * g)` using `div_pos (by linarith) (by positivity)`. Use `⟨e' + (T - N * e' * g) / (2 * N * g), by linarith, ?_⟩` and prove the remaining obligations. Establish `h1 : N * (e' + (T - N * e' * g) / (2 * N * g)) * g = N * e' * g + (T - N * e' * g) / 2`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[h1]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_gt_of_lt {N e' g T : ℝ} (hN : 0 < N) (h : N * e' * g < T) :
    ∃ e'', e' < e'' ∧ N * e'' * g < T := by
  by_cases hg : g ≤ 0
  · refine ⟨e' + 1, by linarith, ?_⟩
    have h1 : N * (e' + 1) * g = N * e' * g + N * g := by ring
    have h2 : N * g ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hN.le hg
    linarith
  · push Not at hg
    have hd : 0 < (T - N * e' * g) / (2 * N * g) := div_pos (by linarith) (by positivity)
    refine ⟨e' + (T - N * e' * g) / (2 * N * g), by linarith, ?_⟩
    have h1 : N * (e' + (T - N * e' * g) / (2 * N * g)) * g = N * e' * g + (T - N * e' * g) / 2 := by
      field_simp
    rw [h1]
    linarith

end LatticeWithoutBigness

open LatticeWithoutBigness in

/- English proof (translation)
Introduce `K _ ι _ P P0 D A e' F II hII har hP0 hsemi hnef hconj hF hdense`. Establish `hA : IsSmoothHerm A` using `hsemi.1`. Establish `: Nonempty K` using `har.1`. Establish `hdeg : ∀ W : Ideal (MRing ι), IsArithVar W 1 → (0 : ℝ) < degC W`. Introduce `W hW`.

Establish `: Finite (projPts W)` using `hfin K ι W hW`. Take `⟨z, hz⟩` from `IndefiniteRowSideFullHecke.HeightsSet.CurveComplexPoint.full K ι W hW`. Establish `: Nonempty (projPts W)` using `⟨Quot.mk _ ⟨z, hz⟩⟩`. Establish `: 0 < Nat.card (projPts W)` using `Nat.card_pos`. Conclude with `this` after adjusting the coercions.

Establish `hmc : ∀ W : Ideal (MRing ι), IsArithVar W 1 → ∀ c : ℝ, II K ι W 1 ![A.tensor (constLine c)] = II K ι W 1 ![A] - ptsIntegral (e` using `0) W (pot (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)) (fun _ => c) := by`. Introduce `W hW c`. Establish `h` using `metricChange K ι (II K ι) (hII K ι) W 0 ![] A (fun _ => c) (fun _ _ _ => rfl) hW (fun j => j.elim0) hA contDiffOn_const`. Establish `e1 : ∀ B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, (Fin.snoc (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) B : Fin (0 + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) = ![B]` using `fun B => by`. Use function extensionality and compare the values at `i`.

Use `fin_cases i`. Both sides reduce to the same expression. Rewrite `h` using `[e1, e1]`. Conclude with `h`. Establish `hlow : ∀ W : Ideal (MRing ι), IsArithVar W 1 → ∀ c : ℝ, c * degC W ≤ ptsIntegral (e` using `0) W (pot (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)) (fun _ => c) := by`.

Introduce `W hW c`. Conclude with `PtsIntegralZeroLowerNE.proof K ι W _ (fun _ => c) c hW.2.1.2.1 (hfin K ι W hW) (fun _ _ _ _ => rfl) (fun _ _ => le_rfl)`. Establish `h1P : (1 : MRing ι) ∉ P` using `fun h => har.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h)`. Establish `hfun : ∀ B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, (fun _ : Fin 1 => B) = ![B]` using `fun B => by`. Use function extensionality and compare the values at `i`.

Use `fin_cases i`. Both sides reduce to the same expression. Break down `Nat.eq_zero_or_pos D with hD | hD` into its components or cases. Substitute `hD` using the available equality. Take `⟨W, hWF, -⟩` from `hdense 1 ⟨fun _ => 0, isMultiHomog_one⟩ h1P`.

Take `⟨hW, hPW, hle⟩` from `hF W hWF`. Establish `: P.IsPrime` using `har.2.1.1`. Establish `hWP : P = W` using `CurveIsOrbit.eq_of_le_of_ringKrullDim_eq (d := 1 + Fintype.card K) hPW har.2.2.2 hW.2.2.2`. Rewrite `hle` using `[← hWP]`. Establish `htw : II K ι P 1 (fun _ => A.tensor (constLine e')) = II K ι P 1 (fun _ => A) - ((1 : ℕ) : ℝ) * e' * geomDeg P A 0` using `hT K ι P 0 A e' II hII har hA`.

Rewrite `htw` using `[hfun, hfun]`. Establish `hm` using `hmc P har e'`. Establish `hl` using `hlow P har e'`. Use `show II K ι P 1 (fun _ => A) ≤ ((1 : ℕ) : ℝ) * e' * geomDeg P A 0`. Rewrite using `[hfun]`.

Move the coercions through the operations in `at htw ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨Ω, _, y, hyP, hbir⟩` from `hM K ι P (D + 1) har`. Substitute `hyP` using the available equality. Assume the negation of the conclusion as `hlt`.

Use `push Not at hlt`. Take `⟨e'', hgt, htop⟩` from `exists_gt_of_lt (N := ((D + 1 : ℕ) : ℝ)) (by positivity) hlt`. Establish `htw` using `hT K ι (mCoordIdeal y) D A e'' II hII har hA`. Establish `hvol` using `hG K ι Ω y D (A.tensor (constLine e'')) P0 II hD hII har hbir hP0 (isSemipositiveRel_twist hsemi e'') (nefOnFibres_twist hnef e'') (isConjInvariantH_twist hconj e'')`. Establish `hpos : 0 < arVolP (IsSmallH (mCoordIdeal y) y (A.tensor (constLine e''))) (chartLatNm y (A.tensor (constLine e'')).a) 1 D`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨τ, hτ, s, hsL, hs0, hsm⟩` from `exists_small_section_of_arithmeticVolume_pos hpos`. Take `⟨f, hfh, hfP, hfW⟩` from `hS K ι Ω y D (A.tensor (constLine e'')) τ s II hII har hbir (isSmoothHerm_twist hA e'') hτ hsL hs0 hsm`. Take `⟨W, hWF, hfW'⟩` from `hdense f hfh hfP`. Take `⟨hW, hPW, hle⟩` from `hF W hWF`.

Establish `h0` using `hfW W hW hPW hfW'`. Establish `hm` using `hmc W hW e''`. Establish `hl` using `hlow W hW e''`. Establish `hd` using `hdeg W hW`. Use polynomial arithmetic with `[mul_pos (sub_pos.mpr hgt) hd]`.
-/
theorem LatticeWithoutBigness.proof (hG : ArithmeticVolumeBigRefined.Statement) (hT : TopConstantTwist.Statement)
    (hM : BirationalModelExists.Statement) (hS : SmallSectionPointHeight.Statement)
    (hfin : CurvePointsFinite.Statement) : LatticeWithoutBigness.Statement := by
  intro K _ ι _ P P0 D A e' F II hII har hP0 hsemi hnef hconj hF hdense
  have hA : IsSmoothHerm A := hsemi.1
  have : Nonempty K := har.1

  have hdeg : ∀ W : Ideal (MRing ι), IsArithVar W 1 → (0 : ℝ) < degC W := by
    intro W hW
    have : Finite (projPts W) := hfin K ι W hW
    obtain ⟨z, hz⟩ := IndefiniteRowSideFullHecke.HeightsSet.CurveComplexPoint.full K ι W hW
    have : Nonempty (projPts W) := ⟨Quot.mk _ ⟨z, hz⟩⟩
    have : 0 < Nat.card (projPts W) := Nat.card_pos
    exact_mod_cast this

  have hmc : ∀ W : Ideal (MRing ι), IsArithVar W 1 → ∀ c : ℝ, II K ι W 1 ![A.tensor (constLine c)] =
      II K ι W 1 ![A] - ptsIntegral (e := 0) W (pot (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)) (fun _ => c) := by
    intro W hW c
    have h := metricChange K ι (II K ι) (hII K ι) W 0 ![] A (fun _ => c) (fun _ _ _ => rfl) hW
      (fun j => j.elim0) hA contDiffOn_const
    have e1 : ∀ B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, (Fin.snoc (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) B : Fin (0 + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) = ![B] :=
      fun B => by
        funext i
        fin_cases i
        rfl
    rw [e1, e1] at h
    exact h
  have hlow : ∀ W : Ideal (MRing ι), IsArithVar W 1 → ∀ c : ℝ,
      c * degC W ≤ ptsIntegral (e := 0) W (pot (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)) (fun _ => c) := by
    intro W hW c
    exact PtsIntegralZeroLowerNE.proof K ι W _ (fun _ => c) c hW.2.1.2.1 (hfin K ι W hW)
      (fun _ _ _ _ => rfl) (fun _ _ => le_rfl)
  have h1P : (1 : MRing ι) ∉ P := fun h => har.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  have hfun : ∀ B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, (fun _ : Fin 1 => B) = ![B] := fun B => by
    funext i
    fin_cases i
    rfl
  rcases Nat.eq_zero_or_pos D with hD | hD
  ·
    subst hD
    obtain ⟨W, hWF, -⟩ := hdense 1 ⟨fun _ => 0, isMultiHomog_one⟩ h1P
    obtain ⟨hW, hPW, hle⟩ := hF W hWF
    have : P.IsPrime := har.2.1.1
    have hWP : P = W :=
      CurveIsOrbit.eq_of_le_of_ringKrullDim_eq (d := 1 + Fintype.card K) hPW har.2.2.2 hW.2.2.2
    rw [← hWP] at hle
    have htw : II K ι P 1 (fun _ => A.tensor (constLine e')) =
        II K ι P 1 (fun _ => A) - ((1 : ℕ) : ℝ) * e' * geomDeg P A 0 := hT K ι P 0 A e' II hII har hA
    rw [hfun, hfun] at htw
    have hm := hmc P har e'
    have hl := hlow P har e'
    show II K ι P 1 (fun _ => A) ≤ ((1 : ℕ) : ℝ) * e' * geomDeg P A 0
    rw [hfun]
    push_cast at htw ⊢
    linarith
  ·
    obtain ⟨Ω, _, y, hyP, hbir⟩ := hM K ι P (D + 1) har
    subst hyP
    by_contra hlt
    push Not at hlt
    obtain ⟨e'', hgt, htop⟩ := exists_gt_of_lt (N := ((D + 1 : ℕ) : ℝ)) (by positivity) hlt
    have htw := hT K ι (mCoordIdeal y) D A e'' II hII har hA
    have hvol := hG K ι Ω y D (A.tensor (constLine e'')) P0 II hD hII har hbir hP0
      (isSemipositiveRel_twist hsemi e'') (nefOnFibres_twist hnef e'') (isConjInvariantH_twist hconj e'')
    have hpos : 0 < arVolP (IsSmallH (mCoordIdeal y) y (A.tensor (constLine e'')))
        (chartLatNm y (A.tensor (constLine e'')).a) 1 D := by
      linarith
    obtain ⟨τ, hτ, s, hsL, hs0, hsm⟩ := exists_small_section_of_arithmeticVolume_pos hpos
    obtain ⟨f, hfh, hfP, hfW⟩ := hS K ι Ω y D (A.tensor (constLine e'')) τ s II hII har hbir
      (isSmoothHerm_twist hA e'') hτ hsL hs0 hsm
    obtain ⟨W, hWF, hfW'⟩ := hdense f hfh hfP
    obtain ⟨hW, hPW, hle⟩ := hF W hWF
    have h0 := hfW W hW hPW hfW'
    have hm := hmc W hW e''
    have hl := hlow W hW e''
    have hd := hdeg W hW
    nlinarith [mul_pos (sub_pos.mpr hgt) hd]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
