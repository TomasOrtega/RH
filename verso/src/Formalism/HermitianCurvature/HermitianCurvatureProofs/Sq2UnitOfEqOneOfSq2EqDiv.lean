import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleOfUnitWords
import Mathlib.Geometry.Manifold.PartitionOfUnity

open Matrix Set
open scoped ComplexConjugate ContDiff Manifold Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def utv {k r m : ℕ} (ε T : ℝ) (Gp : Mat k r → ℝ) (om : Mat k r → Fin m → ℂ) (g : Mat k r) : Fin m → ℂ :=
  fun a => (Real.sqrt T : ℂ) * (Phh ε ((Gp g : ℝ) : ℂ) * om g a)

/- English proof (translation)
Establish `hx : 0 < Gp g` using `by linarith`. Use function extensionality and compare the values at `a`. Simplify using `only [C6.unitOf, utv, Phh, hh, Complex.ofReal_re, sc_one hε hg.le, one_mul, Pi.smul_apply, smul_eq_mul, sqrt_div_eq hT hx, Complex.ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma utv_eq {k r m : ℕ} {ε T : ℝ} (hε : 0 < ε) (hT : 0 < T) (Gp : Mat k r → ℝ) (om : Mat k r → Fin m → ℂ)
    {g : Mat k r} (hg : ε / 2 < Gp g) : C6.unitOf T (Gp g) (om g) = utv ε T Gp om g := by
  have hx : 0 < Gp g := by linarith
  funext a
  simp only [C6.unitOf, utv, Phh, hh, Complex.ofReal_re, sc_one hε hg.le, one_mul, Pi.smul_apply,
    smul_eq_mul, sqrt_div_eq hT hx, Complex.ofReal_mul]
  ring

/- English proof (translation)
Use `contDiff_pi.2 fun a => ?_` and prove the remaining obligations. Simplify using `only [utv]`. Conclude with `contDiff_const.mul (((Phh_cd hε).comp hG).mul (ho a))`.
-/
lemma utv_cd {k r m : ℕ} {ε T : ℝ} (hε : 0 < ε) {Gp : Mat k r → ℝ} {om : Mat k r → Fin m → ℂ}
    (hG : ContDiff ℝ ∞ (fun g => ((Gp g : ℝ) : ℂ))) (ho : ∀ a, ContDiff ℝ ∞ (fun g => om g a)) :
    ContDiff ℝ ∞ (utv ε T Gp om) := by
  refine contDiff_pi.2 fun a => ?_
  simp only [utv]
  exact contDiff_const.mul (((Phh_cd hε).comp hG).mul (ho a))

/- English proof (translation)
Unfold `C6.sq2 C6.unitOf at *`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_ofReal]`. Rewrite using `[← Finset.mul_sum, hv, Real.mul_self_sqrt (div_nonneg hT.le hG.le), div_mul_div_comm, mul_comm T Gv, div_self (mul_pos hG hT).ne']`.
-/
lemma sq2_unitOf_eq_one_of_sq2_eq_div {m : ℕ} {T Gv : ℝ} (hT : 0 < T) (hG : 0 < Gv) {v : Fin m → ℂ} (hv : C6.sq2 v = Gv / T) :
    C6.sq2 (C6.unitOf T Gv v) = 1 := by
  unfold C6.sq2 C6.unitOf at *
  simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_ofReal]
  rw [← Finset.mul_sum, hv, Real.mul_self_sqrt (div_nonneg hT.le hG.le), div_mul_div_comm, mul_comm T Gv,
    div_self (mul_pos hG hT).ne']

/- English proof (translation)
Unfold `C6.sq2`. Conclude with `continuous_finset_sum _ fun a _ => Complex.continuous_normSq.comp (continuous_apply a)`.
-/
lemma continuous_sum_squares (m : ℕ) : Continuous (C6.sq2 (m := m)) := by
  unfold C6.sq2
  exact continuous_finset_sum _ fun a _ => Complex.continuous_normSq.comp (continuous_apply a)

/- English proof (translation)
Use `(pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => ?_` and prove the remaining obligations. Establish `h1 : Complex.normSq (v a) ≤ 1`. Rewrite using `[← h]`. Unfold `C6.sq2`. Conclude with `Finset.single_le_sum (f := fun a => Complex.normSq (v a)) (fun i _ => Complex.normSq_nonneg _) (Finset.mem_univ a)`.

Establish `h2 : ‖v a‖ ^ 2 ≤ 1` using `by rw [← Complex.normSq_eq_norm_sq]; exact h1`. Use polynomial arithmetic with `[norm_nonneg (v a)]`.
-/
lemma norm_le_one_of_sq2_eq_one {m : ℕ} {v : Fin m → ℂ} (h : C6.sq2 v = 1) : ‖v‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => ?_
  have h1 : Complex.normSq (v a) ≤ 1 := by
    rw [← h]
    unfold C6.sq2
    exact Finset.single_le_sum (f := fun a => Complex.normSq (v a)) (fun i _ => Complex.normSq_nonneg _)
      (Finset.mem_univ a)
  have h2 : ‖v a‖ ^ 2 ≤ 1 := by rw [← Complex.normSq_eq_norm_sq]; exact h1
  nlinarith [norm_nonneg (v a)]

/- English proof (translation)
Apply `Metric.isCompact_of_isClosed_isBounded` to reduce the goal to its premises. Conclude with `(isClosed_eq ((continuous_sum_squares m).comp continuous_fst) continuous_const).inter (isClosed_eq ((continuous_sum_squares m').comp continuous_snd) continuous_const)`. Use `(Metric.isBounded_closedBall (x := (0 : (Fin m → ℂ) × (Fin m' → ℂ))) (r := 1)).subset ?_` and prove the remaining obligations. Introduce `w hw`. Rewrite using `[Metric.mem_closedBall, dist_zero_right]`.

Conclude with `norm_prod_le_iff.2 ⟨norm_le_one_of_sq2_eq_one hw.1, norm_le_one_of_sq2_eq_one hw.2⟩`.
-/
lemma spheres_compact (m m' : ℕ) :
    IsCompact {w : (Fin m → ℂ) × (Fin m' → ℂ) | C6.sq2 w.1 = 1 ∧ C6.sq2 w.2 = 1} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact (isClosed_eq ((continuous_sum_squares m).comp continuous_fst) continuous_const).inter
      (isClosed_eq ((continuous_sum_squares m').comp continuous_snd) continuous_const)
  · refine (Metric.isBounded_closedBall (x := (0 : (Fin m → ℂ) × (Fin m' → ℂ))) (r := 1)).subset ?_
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_prod_le_iff.2 ⟨norm_le_one_of_sq2_eq_one hw.1, norm_le_one_of_sq2_eq_one hw.2⟩

/- English proof (translation)
Take `⟨V, hVo, hKV, hVO, -⟩` from `exists_open_between_and_isCompact_closure hK hO hKO`. Take `⟨χ, hχ0, hχ1, -⟩` from `exists_contMDiffMap_zero_one_of_isClosed (I := 𝓘(ℝ, F)) hVo.isClosed_compl hK.isClosed (disjoint_compl_left_iff_subset.2 hKV)`. Establish `hχ : ContDiff ℝ ∞ (χ : F → ℝ)` using `contMDiff_iff_contDiff.1 χ.contMDiff`. Establish `hΦ : ContDiff ℝ ∞ (fun y => χ y • Pi y)`. Rewrite using `[contDiff_iff_contDiffAt]`.

Introduce `x`. Distinguish the cases in `hx : x ∈ O`. Conclude with `hχ.contDiffAt.smul (hPi.contDiffAt (hO.mem_nhds hx))`. Establish `hx' : x ∈ (closure V)ᶜ` using `fun h => hx (hVO h)`. Establish `h0 : (fun y => χ y • Pi y) =ᶠ[𝓝 x] fun _ => (0 : E)` using `by filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx'] with y hy`.

Establish `hyV : y ∈ Vᶜ` using `fun h => hy (subset_closure h)`. Simplify using `[hχ0 hyV]`. Conclude with `contDiffAt_const.congr_of_eventuallyEq h0`. Use `⟨fun y => χ y • Pi y, hΦ, fun y hy => by simp [hχ1 hy], fun j => ?_⟩` and prove the remaining obligations. Conclude with `hK.exists_bound_of_continuousOn ((hΦ.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)).continuousOn)`.
-/
lemma bump_ext {F E : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (K O : Set F) (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (Pi : F → E) (hPi : ContDiffOn ℝ ∞ Pi O) :
    ∃ Φ : F → E, ContDiff ℝ ∞ Φ ∧ (∀ y ∈ K, Φ y = Pi y) ∧
      ∀ j : ℕ, ∃ B : ℝ, ∀ y ∈ K, ‖iteratedFDeriv ℝ j Φ y‖ ≤ B := by
  obtain ⟨V, hVo, hKV, hVO, -⟩ := exists_open_between_and_isCompact_closure hK hO hKO
  obtain ⟨χ, hχ0, hχ1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed (I := 𝓘(ℝ, F)) hVo.isClosed_compl
    hK.isClosed (disjoint_compl_left_iff_subset.2 hKV)
  have hχ : ContDiff ℝ ∞ (χ : F → ℝ) := contMDiff_iff_contDiff.1 χ.contMDiff
  have hΦ : ContDiff ℝ ∞ (fun y => χ y • Pi y) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ O
    · exact hχ.contDiffAt.smul (hPi.contDiffAt (hO.mem_nhds hx))
    · have hx' : x ∈ (closure V)ᶜ := fun h => hx (hVO h)
      have h0 : (fun y => χ y • Pi y) =ᶠ[𝓝 x] fun _ => (0 : E) := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx'] with y hy
        have hyV : y ∈ Vᶜ := fun h => hy (subset_closure h)
        simp [hχ0 hyV]
      exact contDiffAt_const.congr_of_eventuallyEq h0
  refine ⟨fun y => χ y • Pi y, hΦ, fun y hy => by simp [hχ1 hy], fun j => ?_⟩
  exact hK.exists_bound_of_continuousOn
    ((hΦ.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)).continuousOn)

end Formalism.FourierDecayAlt.P.AdmissibleLieWords

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `hU k r m m' om om' Gp T T' E _ _ Pi O hom hom' hGp hT hT' hsq hsq' hO hKO hPi ε hε i`. Establish `hGcd : ContDiff ℝ ∞ (fun g => ((Gp g : ℝ) : ℂ))` using `(poly_adm (n := 0) hGp).1`. Establish `hGc : Continuous Gp`. Establish `h` using `Complex.continuous_re.comp hGcd.continuous`. Simplify using `only [Function.comp_def, Complex.ofReal_re] at h`.

Conclude with `h`. Establish `ho : ∀ a, ContDiff ℝ ∞ (fun g => om g a)` using `fun a => (poly_adm (n := 0) (hom a)).1`. Establish `ho' : ∀ a, ContDiff ℝ ∞ (fun g => om' g a)` using `fun a => (poly_adm (n := 0) (hom' a)).1`. Establish `hu1 : ContDiff ℝ ∞ (utv ε T Gp om)` using `utv_cd hε hGcd ho`. Establish `hu2 : ContDiff ℝ ∞ (utv ε T' Gp om')` using `utv_cd hε hGcd ho'`.

Establish `hψ : ContDiff ℝ ∞ (fun g => (utv ε T Gp om g, utv ε T' Gp om' g))` using `hu1.prodMk hu2`. Establish `hOε : IsOpen {g : Mat k r | ε / 2 < Gp g}` using `isOpen_lt continuous_const hGc`. Establish `hsph : ∀ g ∈ GV k r, ε / 2 < Gp g → C6.unitOf T (Gp g) (om g) = utv ε T Gp om g ∧ C6.unitOf T' (Gp g) (om' g) = utv ε T' Gp om' g ∧ (C6.unitOf T (Gp g) (om g), C6.unitOf T' (Gp g) (om' g)) ∈ {w : (Fin m → ℂ) × (Fin m' → ℂ) | C6.sq2 w.1 = 1 ∧ C6.sq2 w.2 = 1}`. Introduce `g hg hgt`. Establish `hpos : 0 < Gp g` using `by linarith`.

Conclude with `⟨utv_eq hε hT Gp om hgt, utv_eq hε hT' Gp om' hgt, sq2_unitOf_eq_one_of_sq2_eq_div hT hpos (hsq g hg), sq2_unitOf_eq_one_of_sq2_eq_div hT' hpos (hsq' g hg)⟩`. Take `⟨Φ, hΦ, hΦK, hΦb⟩` from `bump_ext _ O (spheres_compact m m') hO hKO Pi hPi`. Establish `hwl : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) → ∀ x ∈ wL u ++ wR v, inLie k r x.2`. Introduce `u v hu hv x hx`. Break down `List.mem_append.mp hx with hx | hx` into its components or cases.

Simplify using `only [wL, List.mem_map] at hx`. Take `⟨X, hX, rfl⟩` from `hx`. Conclude with `(hu X hX).1`. Simplify using `only [wR, List.mem_map, List.mem_reverse] at hx`. Take `⟨X, hX, rfl⟩` from `hx`.

Conclude with `(hv X hX).1`. Establish `hlen : ∀ u v : List (Mat k r), (wL u ++ wR v).length = u.length + v.length`. Introduce `u v`. Simplify using `[wL, wR]`. Use `choose C1 hC1 using hU k r m om Gp T hom hGp hT hsq ε hε`.

Use `choose C2 hC2 using hU k r m' om' Gp T' hom' hGp hT' hsq' ε hε`. Take `⟨M, hM⟩ : ∃ M : ℝ, M = ∑ j ∈ Finset.range (i + 1), (|C1 j| + |C2 j|)` from `⟨_, rfl⟩`. Establish `hCM : ∀ j ≤ i, C1 j ≤ M ∧ C2 j ≤ M`. Introduce `j hj`. Establish `hmem : j ∈ Finset.range (i + 1)` using `Finset.mem_range.mpr (by omega)`.

Establish `hle` using `Finset.single_le_sum (f := fun j => |C1 j| + |C2 j|) (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hmem`. Rewrite `hle` using `[← hM]`. Conclude with `⟨by linarith [le_abs_self (C1 j), abs_nonneg (C2 j)], by linarith [le_abs_self (C2 j), abs_nonneg (C1 j)]⟩`. Establish `H : ∀ w, admitted i w → w ≠ [] → ∀ g ∈ {g : Mat k r | g ∈ GV k r ∧ ε ≤ Gp g}, ‖Dw w (fun g => (utv ε T Gp om g, utv ε T' Gp om' g)) g‖ ≤ M * gN g ^ (2 * (r + 1) * w.length + (r + 1))`. Introduce and unpack `w ⟨u, v, hu, hv, hl, rfl⟩ - g ⟨hg, hge⟩`.

Establish `hgt : ε / 2 < Gp g` using `by linarith`. Establish `hw` using `hwl u v hu hv`. Establish `huv : C6.UnitWords k r u v (u.length + v.length)` using `⟨hu, hv, rfl⟩`. Establish `e1 : Dw (wL u ++ wR v) (utv ε T Gp om) g = Dw (wL u ++ wR v) (fun g' => C6.unitOf T (Gp g') (om g')) g` using `Dw_congr_loc hw hOε (fun g' hg' hg'O => ((hsph g' hg' hg'O).1).symm) g hg hgt`. Establish `e2 : Dw (wL u ++ wR v) (utv ε T' Gp om') g = Dw (wL u ++ wR v) (fun g' => C6.unitOf T' (Gp g') (om' g')) g` using `Dw_congr_loc hw hOε (fun g' hg' hg'O => ((hsph g' hg' hg'O).2.1).symm) g hg hgt`.

Establish `f1 : Dw (wL u ++ wR v) (utv ε T Gp om) g = (Dw (wL u ++ wR v) (fun g => (utv ε T Gp om g, utv ε T' Gp om' g)) g).1`. Establish `h` using `congrFun (dw_clm (ContinuousLinearMap.fst ℝ (Fin m → ℂ) (Fin m' → ℂ)) (wL u ++ wR v) hψ) g`. Simplify using `using h`. Establish `f2 : Dw (wL u ++ wR v) (utv ε T' Gp om') g = (Dw (wL u ++ wR v) (fun g => (utv ε T Gp om g, utv ε T' Gp om' g)) g).2`. Establish `h` using `congrFun (dw_clm (ContinuousLinearMap.snd ℝ (Fin m → ℂ) (Fin m' → ℂ)) (wL u ++ wR v) hψ) g`.

Simplify using `using h`. Establish `b1` using `hC1 _ u v huv g hg hge`. Establish `b2` using `hC2 _ u v huv g hg hge`. Rewrite `b1` using `[dLR_eq, ← e1, f1]`. Rewrite `b2` using `[dLR_eq, ← e2, f2]`.

Establish `hexp : (r + 1) * (2 * (u.length + v.length) + 1) = 2 * (r + 1) * (wL u ++ wR v).length + (r + 1)`. Rewrite using `[hlen]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `b1`, `b2` using `[hexp]`. Establish `hY : 0 ≤ gN g ^ (2 * (r + 1) * (wL u ++ wR v).length + (r + 1))` using `pow_nonneg (le_trans zero_le_one (gN_ge_one hg)) _`.

Take `⟨m1, m2⟩` from `hCM _ hl`. Rewrite using `[Prod.norm_def]`. Conclude with `max_le (b1.trans (mul_le_mul_of_nonneg_right m1 hY)) (b2.trans (mul_le_mul_of_nonneg_right m2 hY))`. Take `⟨C, -, hC⟩` from `fdb (fun g => (utv ε T Gp om g, utv ε T' Gp om' g)) hψ {g : Mat k r | g ∈ GV k r ∧ ε ≤ Gp g} _ (fun g hg => by rw [← (hsph g hg.1 (by linarith [hg.2])).1, ← (hsph g hg.1 (by linarith [hg.2])).2.1]`. Conclude with `(hsph g hg.1 (by linarith [hg.2])).2.2)`.

Use `gN (fun g hg => gN_ge_one hg.1) (2 * (r + 1)) (r + 1) M i H i E Φ hΦ hΦb`. Use `⟨C, fun u v huv g hg hge => ?_⟩` and prove the remaining obligations. Establish `hw` using `hwl u v huv.1 huv.2.1`. Rewrite using `[dLR_eq]`. Establish `e : Dw (wL u ++ wR v) (fun g' => Pi (C6.unitOf T (Gp g') (om g'), C6.unitOf T' (Gp g') (om' g'))) g = Dw (wL u ++ wR v) (fun g' => Φ (utv ε T Gp om g', utv ε T' Gp om' g')) g`.

Use `Dw_congr_loc hw hOε (fun g' hg' hg'O => ?_) g hg (show ε / 2 < Gp g by linarith)` and prove the remaining obligations. Take `⟨h1, h2, h3⟩` from `hsph g' hg' hg'O`. Rewrite using `[← hΦK _ h3, h1, h2]`. Rewrite using `[e]`. Establish `hl : (wL u ++ wR v).length = i` using `by rw [hlen]; exact huv.2.2`.

Establish `hb` using `hC (wL u ++ wR v) (admissible_of_unit_words huv) hl.le g ⟨hg, hge⟩`. Rewrite `hb` using `[hl]`. Establish `hexp : (2 * (r + 1) + (r + 1)) * i = 3 * (r + 1) * i` using `by ring`. Rewrite `hb` using `[hexp]`. Then use the resulting hypothesis.
-/
theorem c6_fib_cost_of_pieces : C6.FibCostOfParts := by
  intro hU k r m m' om om' Gp T T' E _ _ Pi O hom hom' hGp hT hT' hsq hsq' hO hKO hPi ε hε i
  have hGcd : ContDiff ℝ ∞ (fun g => ((Gp g : ℝ) : ℂ)) := (poly_adm (n := 0) hGp).1
  have hGc : Continuous Gp := by
    have h := Complex.continuous_re.comp hGcd.continuous
    simp only [Function.comp_def, Complex.ofReal_re] at h
    exact h
  have ho : ∀ a, ContDiff ℝ ∞ (fun g => om g a) := fun a => (poly_adm (n := 0) (hom a)).1
  have ho' : ∀ a, ContDiff ℝ ∞ (fun g => om' g a) := fun a => (poly_adm (n := 0) (hom' a)).1
  have hu1 : ContDiff ℝ ∞ (utv ε T Gp om) := utv_cd hε hGcd ho
  have hu2 : ContDiff ℝ ∞ (utv ε T' Gp om') := utv_cd hε hGcd ho'
  have hψ : ContDiff ℝ ∞ (fun g => (utv ε T Gp om g, utv ε T' Gp om' g)) := hu1.prodMk hu2
  have hOε : IsOpen {g : Mat k r | ε / 2 < Gp g} := isOpen_lt continuous_const hGc

  have hsph : ∀ g ∈ GV k r, ε / 2 < Gp g →
      C6.unitOf T (Gp g) (om g) = utv ε T Gp om g ∧ C6.unitOf T' (Gp g) (om' g) = utv ε T' Gp om' g ∧
      (C6.unitOf T (Gp g) (om g), C6.unitOf T' (Gp g) (om' g)) ∈
        {w : (Fin m → ℂ) × (Fin m' → ℂ) | C6.sq2 w.1 = 1 ∧ C6.sq2 w.2 = 1} := by
    intro g hg hgt
    have hpos : 0 < Gp g := by linarith
    exact ⟨utv_eq hε hT Gp om hgt, utv_eq hε hT' Gp om' hgt, sq2_unitOf_eq_one_of_sq2_eq_div hT hpos (hsq g hg),
      sq2_unitOf_eq_one_of_sq2_eq_div hT' hpos (hsq' g hg)⟩
  obtain ⟨Φ, hΦ, hΦK, hΦb⟩ := bump_ext _ O (spheres_compact m m') hO hKO Pi hPi

  have hwl : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
      ∀ x ∈ wL u ++ wR v, inLie k r x.2 := by
    intro u v hu hv x hx
    rcases List.mem_append.mp hx with hx | hx
    · simp only [wL, List.mem_map] at hx
      obtain ⟨X, hX, rfl⟩ := hx
      exact (hu X hX).1
    · simp only [wR, List.mem_map, List.mem_reverse] at hx
      obtain ⟨X, hX, rfl⟩ := hx
      exact (hv X hX).1
  have hlen : ∀ u v : List (Mat k r), (wL u ++ wR v).length = u.length + v.length := by
    intro u v
    simp [wL, wR]
  choose C1 hC1 using hU k r m om Gp T hom hGp hT hsq ε hε
  choose C2 hC2 using hU k r m' om' Gp T' hom' hGp hT' hsq' ε hε
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∑ j ∈ Finset.range (i + 1), (|C1 j| + |C2 j|) := ⟨_, rfl⟩
  have hCM : ∀ j ≤ i, C1 j ≤ M ∧ C2 j ≤ M := by
    intro j hj
    have hmem : j ∈ Finset.range (i + 1) := Finset.mem_range.mpr (by omega)
    have hle := Finset.single_le_sum (f := fun j => |C1 j| + |C2 j|)
      (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hmem
    rw [← hM] at hle
    exact ⟨by linarith [le_abs_self (C1 j), abs_nonneg (C2 j)], by linarith [le_abs_self (C2 j), abs_nonneg (C1 j)]⟩
  have H : ∀ w, admitted i w → w ≠ [] → ∀ g ∈ {g : Mat k r | g ∈ GV k r ∧ ε ≤ Gp g},
      ‖Dw w (fun g => (utv ε T Gp om g, utv ε T' Gp om' g)) g‖ ≤
        M * gN g ^ (2 * (r + 1) * w.length + (r + 1)) := by
    rintro w ⟨u, v, hu, hv, hl, rfl⟩ - g ⟨hg, hge⟩
    have hgt : ε / 2 < Gp g := by linarith
    have hw := hwl u v hu hv
    have huv : C6.UnitWords k r u v (u.length + v.length) := ⟨hu, hv, rfl⟩
    have e1 : Dw (wL u ++ wR v) (utv ε T Gp om) g =
        Dw (wL u ++ wR v) (fun g' => C6.unitOf T (Gp g') (om g')) g :=
      Dw_congr_loc hw hOε (fun g' hg' hg'O => ((hsph g' hg' hg'O).1).symm) g hg hgt
    have e2 : Dw (wL u ++ wR v) (utv ε T' Gp om') g =
        Dw (wL u ++ wR v) (fun g' => C6.unitOf T' (Gp g') (om' g')) g :=
      Dw_congr_loc hw hOε (fun g' hg' hg'O => ((hsph g' hg' hg'O).2.1).symm) g hg hgt
    have f1 : Dw (wL u ++ wR v) (utv ε T Gp om) g =
        (Dw (wL u ++ wR v) (fun g => (utv ε T Gp om g, utv ε T' Gp om' g)) g).1 := by
      have h := congrFun (dw_clm (ContinuousLinearMap.fst ℝ (Fin m → ℂ) (Fin m' → ℂ)) (wL u ++ wR v) hψ) g
      simpa using h
    have f2 : Dw (wL u ++ wR v) (utv ε T' Gp om') g =
        (Dw (wL u ++ wR v) (fun g => (utv ε T Gp om g, utv ε T' Gp om' g)) g).2 := by
      have h := congrFun (dw_clm (ContinuousLinearMap.snd ℝ (Fin m → ℂ) (Fin m' → ℂ)) (wL u ++ wR v) hψ) g
      simpa using h
    have b1 := hC1 _ u v huv g hg hge
    have b2 := hC2 _ u v huv g hg hge
    rw [dLR_eq, ← e1, f1] at b1
    rw [dLR_eq, ← e2, f2] at b2
    have hexp : (r + 1) * (2 * (u.length + v.length) + 1) =
        2 * (r + 1) * (wL u ++ wR v).length + (r + 1) := by
      rw [hlen]; ring
    rw [hexp] at b1 b2
    have hY : 0 ≤ gN g ^ (2 * (r + 1) * (wL u ++ wR v).length + (r + 1)) :=
      pow_nonneg (le_trans zero_le_one (gN_ge_one hg)) _
    obtain ⟨m1, m2⟩ := hCM _ hl
    rw [Prod.norm_def]
    exact max_le (b1.trans (mul_le_mul_of_nonneg_right m1 hY)) (b2.trans (mul_le_mul_of_nonneg_right m2 hY))
  obtain ⟨C, -, hC⟩ := fdb (fun g => (utv ε T Gp om g, utv ε T' Gp om' g)) hψ
    {g : Mat k r | g ∈ GV k r ∧ ε ≤ Gp g} _
    (fun g hg => by rw [← (hsph g hg.1 (by linarith [hg.2])).1, ← (hsph g hg.1 (by linarith [hg.2])).2.1]
                    exact (hsph g hg.1 (by linarith [hg.2])).2.2)
    gN (fun g hg => gN_ge_one hg.1) (2 * (r + 1)) (r + 1) M i H i E Φ hΦ hΦb
  refine ⟨C, fun u v huv g hg hge => ?_⟩
  have hw := hwl u v huv.1 huv.2.1
  rw [dLR_eq]
  have e : Dw (wL u ++ wR v) (fun g' => Pi (C6.unitOf T (Gp g') (om g'), C6.unitOf T' (Gp g') (om' g'))) g =
      Dw (wL u ++ wR v) (fun g' => Φ (utv ε T Gp om g', utv ε T' Gp om' g')) g := by
    refine Dw_congr_loc hw hOε (fun g' hg' hg'O => ?_) g hg (show ε / 2 < Gp g by linarith)
    obtain ⟨h1, h2, h3⟩ := hsph g' hg' hg'O
    rw [← hΦK _ h3, h1, h2]
  rw [e]
  have hl : (wL u ++ wR v).length = i := by rw [hlen]; exact huv.2.2
  have hb := hC (wL u ++ wR v) (admissible_of_unit_words huv) hl.le g ⟨hg, hge⟩
  rw [hl] at hb
  have hexp : (2 * (r + 1) + (r + 1)) * i = 3 * (r + 1) * i := by ring
  rwa [hexp] at hb

/- English proof (translation)
The claim follows from `c6_fib_cost_of_pieces fibre_unit_normalization`.
-/
theorem fibre_cost_estimate : C6.FibCost := c6_fib_cost_of_pieces fibre_unit_normalization

end Formalism.FourierDecayAlt.P
