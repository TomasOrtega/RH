import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormSubLeOfDerivIcc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

namespace GlobalTheory.TypeSum

variable {n : ℕ} {ε : Fin n → Bool}

/- English proof (translation)
Take `⟨C, hC⟩` from `hG w hw`. Take `⟨M, hM⟩` from `hK.bddAbove_image continuous_hs.continuousOn`. Use `⟨|C| * (1 + max M 0) ^ N, by positivity, fun y hy => ?_⟩` and prove the remaining obligations. Establish `h1 : hs y ≤ max M 0` using `(hM ⟨y, hy, rfl⟩).trans (le_max_left _ _)`. Establish `h0 : 0 ≤ hs y` using `hs_nonneg y`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem FamGrowth.bdd_of_isCompact {N : ℕ} {F : List (Mx n) → Mx n → ℂ} (hG : FamGrowth ε N F)
    {w : List (Mx n)} (hw : ∀ Y ∈ w, Y ∈ lieSet ε) {K : Set (Mx n)} (hK : IsCompact K) (hKU : K ⊆ UJset ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ K, ‖F w y‖ ≤ B := by
  obtain ⟨C, hC⟩ := hG w hw
  obtain ⟨M, hM⟩ := hK.bddAbove_image continuous_hs.continuousOn
  refine ⟨|C| * (1 + max M 0) ^ N, by positivity, fun y hy => ?_⟩
  have h1 : hs y ≤ max M 0 := (hM ⟨y, hy, rfl⟩).trans (le_max_left _ _)
  have h0 : 0 ≤ hs y := hs_nonneg y
  calc ‖F w y‖ ≤ C * (1 + hs y) ^ N := hC y (hKU hy)
    _ ≤ |C| * (1 + hs y) ^ N := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (1 + max M 0) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) N) (abs_nonneg C)

def expSweep (K : Set (Mx n)) (X : Mx n) : Set (Mx n) :=
  (fun p : Mx n × ℝ => p.1 * NormedSpace.exp (p.2 • X)) '' (K ×ˢ Set.Icc (-1 : ℝ) 1)

/- English proof (translation)
The claim follows from `(hK.prod (isCompact_Icc (a := (-1 : ℝ)) (b := 1))).image (continuous_fst.matrix_mul ((continuous_exp_smul X).comp continuous_snd))`.
-/
theorem isCompact_expSweep {K : Set (Mx n)} (hK : IsCompact K) (X : Mx n) : IsCompact (expSweep K X) :=
  (hK.prod (isCompact_Icc (a := (-1 : ℝ)) (b := 1))).image
    (continuous_fst.matrix_mul ((continuous_exp_smul X).comp continuous_snd))
/- English proof (translation)
Introduce and unpack `_ ⟨⟨z, s⟩, ⟨hz, -⟩, rfl⟩`. Conclude with `mul_mem_UJ (hKU hz) (exp_mem_UJ hX s)`.
-/
theorem expSweep_sub {K : Set (Mx n)} (hKU : K ⊆ UJset ε) {X : Mx n} (hX : X ∈ lieSet ε) :
    expSweep K X ⊆ UJset ε := by
  rintro _ ⟨⟨z, s⟩, ⟨hz, -⟩, rfl⟩
  exact mul_mem_UJ (hKU hz) (exp_mem_UJ hX s)

/- English proof (translation)
Assemble the required witnesses or components as `⟨(z, s), ⟨hz, hs⟩, rfl⟩`.
-/
theorem mem_expSweep {K : Set (Mx n)} {z : Mx n} (hz : z ∈ K) (X : Mx n) {s : ℝ} (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    z * NormedSpace.exp (s • X) ∈ expSweep K X := ⟨(z, s), ⟨hz, hs⟩, rfl⟩

/- English proof (translation)
Rewrite using `[zero_smul, NormedSpace.exp_zero]`.
-/
theorem exp_zero_smul_mx (X : Mx n) : NormedSpace.exp ((0 : ℝ) • X) = 1 := by
  rw [zero_smul, NormedSpace.exp_zero]

/- English proof (translation)
Establish `h` using `norm_sub_le_of_deriv_Icc (f := fun s => F w (z * NormedSpace.exp (s • X))) (fun s => hF.hasDerivAt_exp hw hX hz s) zero_le_one hB (t := t) (abs_le.1 ht)`. Simplify `h` using `only [exp_zero_smul_mx, Matrix.mul_one]`.
-/
theorem IsDerFam.norm_sub_exp_le {F : List (Mx n) → Mx n → ℂ} (hF : IsDerFam ε F) {w : List (Mx n)}
    (hw : ∀ Y ∈ w, Y ∈ lieSet ε) {X : Mx n} (hX : X ∈ lieSet ε) {z : Mx n} (hz : z ∈ UJset ε) {B : ℝ}
    (hB : ∀ s ∈ Set.Icc (-1 : ℝ) 1, ‖F (X :: w) (z * NormedSpace.exp (s • X))‖ ≤ B) {t : ℝ} (ht : |t| ≤ 1) :
    ‖F w (z * NormedSpace.exp (t • X)) - F w z‖ ≤ B * |t| := by
  have h := norm_sub_le_of_deriv_Icc (f := fun s => F w (z * NormedSpace.exp (s • X)))
    (fun s => hF.hasDerivAt_exp hw hX hz s) zero_le_one hB (t := t) (abs_le.1 ht)
  simpa only [exp_zero_smul_mx, Matrix.mul_one] using h

/- English proof (translation)
Establish `hXw : ∀ Y ∈ X :: w, Y ∈ lieSet ε`. Introduce `Y hY`. Break down `List.mem_cons.1 hY with rfl | hY` into its components or cases. Use `exacts [hX, hw Y hY]`. Establish `hB0 : 0 ≤ B` using `(norm_nonneg _).trans (hB 0 ⟨by norm_num, by norm_num⟩)`.

Establish `h1 : ∀ s ∈ Set.Icc (-|t|) |t|, ‖F (X :: w) (z * NormedSpace.exp (s • X)) - F (X :: w) z‖ ≤ B * |t|`. Introduce `s hs`. Establish `hs1 : |s| ≤ |t|` using `abs_le.2 hs`. Conclude with `(hF.norm_sub_exp_le hXw hX hz hB (hs1.trans ht)).trans (mul_le_mul_of_nonneg_left hs1 hB0)`. Establish `hd : ∀ s, HasDerivAt (fun s : ℝ => F w (z * NormedSpace.exp (s • X)) - s • F (X :: w) z) (F (X :: w) (z * NormedSpace.exp (s • X)) - F (X :: w) z) s`.

Introduce `s`. Use `(hF.hasDerivAt_exp hw hX hz s).fun_sub ((hasDerivAt_id s).smul_const (F (X :: w) z))` as an intermediate fact. Simplify `this` using `only [id, one_smul]`. Establish `h` using `norm_sub_le_of_deriv_Icc hd (abs_nonneg t) h1 (t := t) ⟨neg_abs_le t, le_abs_self t⟩`. Simplify using `only [exp_zero_smul_mx, Matrix.mul_one, zero_smul, sub_zero, NormedSpace.exp_zero] at h`.

Establish `e : F w (z * NormedSpace.exp (t • X)) - F w z - t • F (X :: w) z = F w (z * NormedSpace.exp (t • X)) - t • F (X :: w) z - F w z` using `by abel`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem IsDerFam.norm_taylor_exp_le {F : List (Mx n) → Mx n → ℂ} (hF : IsDerFam ε F) {w : List (Mx n)}
    (hw : ∀ Y ∈ w, Y ∈ lieSet ε) {X : Mx n} (hX : X ∈ lieSet ε) {z : Mx n} (hz : z ∈ UJset ε) {B : ℝ}
    (hB : ∀ s ∈ Set.Icc (-1 : ℝ) 1, ‖F (X :: X :: w) (z * NormedSpace.exp (s • X))‖ ≤ B) {t : ℝ} (ht : |t| ≤ 1) :
    ‖F w (z * NormedSpace.exp (t • X)) - F w z - t • F (X :: w) z‖ ≤ B * t ^ 2 := by
  have hXw : ∀ Y ∈ X :: w, Y ∈ lieSet ε := by
    intro Y hY
    rcases List.mem_cons.1 hY with rfl | hY
    exacts [hX, hw Y hY]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨by norm_num, by norm_num⟩)
  have h1 : ∀ s ∈ Set.Icc (-|t|) |t|,
      ‖F (X :: w) (z * NormedSpace.exp (s • X)) - F (X :: w) z‖ ≤ B * |t| := by
    intro s hs
    have hs1 : |s| ≤ |t| := abs_le.2 hs
    exact (hF.norm_sub_exp_le hXw hX hz hB (hs1.trans ht)).trans (mul_le_mul_of_nonneg_left hs1 hB0)
  have hd : ∀ s, HasDerivAt (fun s : ℝ => F w (z * NormedSpace.exp (s • X)) - s • F (X :: w) z)
      (F (X :: w) (z * NormedSpace.exp (s • X)) - F (X :: w) z) s := by
    intro s
    have := (hF.hasDerivAt_exp hw hX hz s).fun_sub ((hasDerivAt_id s).smul_const (F (X :: w) z))
    simpa only [id, one_smul] using this
  have h := norm_sub_le_of_deriv_Icc hd (abs_nonneg t) h1 (t := t) ⟨neg_abs_le t, le_abs_self t⟩
  simp only [exp_zero_smul_mx, Matrix.mul_one, zero_smul, sub_zero, NormedSpace.exp_zero] at h
  have e : F w (z * NormedSpace.exp (t • X)) - F w z - t • F (X :: w) z =
      F w (z * NormedSpace.exp (t • X)) - t • F (X :: w) z - F w z := by abel
  rw [e]
  calc _ ≤ B * |t| * |t| := h
    _ = B * t ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/- English proof (translation)
Introduce `Z hZ`. Break down `List.mem_cons.1 hZ with rfl | hZ` into its components or cases. Use `exacts [hY, hw Z hZ]`.
-/
theorem lie_cons {Y : Mx n} {w : List (Mx n)} (hY : Y ∈ lieSet ε) (hw : ∀ Z ∈ w, Z ∈ lieSet ε) :
    ∀ Z ∈ Y :: w, Z ∈ lieSet ε := by
  intro Z hZ
  rcases List.mem_cons.1 hZ with rfl | hZ
  exacts [hY, hw Z hZ]

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `b hb K hK hKU`. Use `⟨0, le_rfl, fun z _ t _ => ?_⟩` and prove the remaining obligations.

Simplify using the standard rewrite rules. Consider the case `succ d ih`. Introduce `b hb K hK hKU`. Establish `hX` using `hb 0`. Establish `hK'` using `isCompact_expSweep hK (b 0)`.

Establish `hK'U` using `expSweep_sub hKU hX`. Take `⟨C', hC'0, hC'⟩` from `ih (fun i => b i.succ) (fun i => hb _) _ hK' hK'U`. Take `⟨B0, hB00, hB0⟩` from `hG.bdd_of_isCompact (lie_cons hX (lie_cons hX hl)) hK' hK'U`. Establish `hBi : ∀ i : Fin d, ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ expSweep K (b 0), ‖F (b 0 :: b i.succ :: l) y‖ ≤ B` using `fun i => hG.bdd_of_isCompact (lie_cons hX (lie_cons (hb _) hl)) hK' hK'U`. Use `choose B hBnn hB using hBi`.

Establish `hBs : 0 ≤ ∑ i, B i` using `Finset.sum_nonneg fun i _ => hBnn i`. Use `⟨C' + ∑ i, B i + B0, by positivity, fun z hz t ht => ?_⟩` and prove the remaining obligations. Establish `hzU` using `hKU hz`. Establish `hti : ∀ i, |t i| ≤ ‖t‖` using `fun i => by simpa using norm_le_pi_norm t i`. Establish `ht0 : t 0 ∈ Set.Icc (-1 : ℝ) 1` using `abs_le.1 ((hti 0).trans ht)`.

Establish `ht' : ‖(fun i : Fin d => t i.succ)‖ ≤ ‖t‖` using `(pi_norm_le_iff_of_nonneg (norm_nonneg t)).2 fun i => norm_le_pi_norm t i.succ`. Establish `hz1` using `mem_expSweep hz (b 0) ht0`. Establish `hprod : z * (List.ofFn fun i => NormedSpace.exp (t i • b i)).prod = z * NormedSpace.exp (t 0 • b 0) * (List.ofFn fun i : Fin d => NormedSpace.exp (t i.succ • b i.succ)).prod`. Rewrite using `[List.ofFn_succ, List.prod_cons, Matrix.mul_assoc]`. Rewrite using `[hprod, Fin.sum_univ_succ]`.

Use `set z1 := z * NormedSpace.exp (t 0 • b 0) with hz1def`. Establish `h1` using `hC' z1 hz1 (fun i => t i.succ) (ht'.trans ht)`. Establish `h2 : ‖∑ i : Fin d, t i.succ • (F (b i.succ :: l) z1 - F (b i.succ :: l) z)‖ ≤ (∑ i, B i) * ‖t‖ ^ 2`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`.

Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Rewrite using `[norm_smul, Real.norm_eq_abs]`. Establish `hd` using `hF.norm_sub_exp_le (lie_cons (hb i.succ) hl) hX hzU (fun s hs => hB i _ (mem_expSweep hz (b 0) hs)) (abs_le.2 ht0)`. Combine the equalities or inequalities in the displayed calculation. Establish `h3` using `hF.norm_taylor_exp_le hl hX hzU (fun s hs => hB0 _ (mem_expSweep hz (b 0) hs)) (abs_le.2 ht0)`.

Establish `h3' : B0 * t 0 ^ 2 ≤ B0 * ‖t‖ ^ 2`. Use `mul_le_mul_of_nonneg_left ?_ hB00` and prove the remaining obligations. Rewrite using `[← sq_abs]`. Conclude with `pow_le_pow_left₀ (abs_nonneg _) (hti 0) 2`. Establish `h1' : C' * ‖(fun i : Fin d => t i.succ)‖ ^ 2 ≤ C' * ‖t‖ ^ 2` using `mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ht' 2) hC'0`.

Establish `e : F l (z1 * (List.ofFn fun i : Fin d => NormedSpace.exp (t i.succ • b i.succ)).prod) - F l z - (t 0 • F (b 0 :: l) z + ∑ i : Fin d, t i.succ • F (b i.succ :: l) z) = (F l (z1 * (List.ofFn fun i : Fin d => NormedSpace.exp (t i.succ • b i.succ)).prod) - F l z1 - ∑ i : Fin d, t i. …`. Simplify using `only [smul_sub, Finset.sum_sub_distrib]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Use `(norm_add₃_le).trans ?_` and prove the remaining obligations.

Establish `: (C' + ∑ i, B i + B0) * ‖t‖ ^ 2 = C' * ‖t‖ ^ 2 + (∑ i, B i) * ‖t‖ ^ 2 + B0 * ‖t‖ ^ 2` using `by ring`. Rewrite using `[this]`. Conclude with `add_le_add_three (h1.trans h1') h2 (h3.trans h3')`.
-/
theorem IsDerFam.taylor_prod {N : ℕ} {F : List (Mx n) → Mx n → ℂ} (hF : IsDerFam ε F) (hG : FamGrowth ε N F)
    {l : List (Mx n)} (hl : ∀ Y ∈ l, Y ∈ lieSet ε) : ∀ (d : ℕ) (b : Fin d → Mx n), (∀ i, b i ∈ lieSet ε) →
    ∀ K : Set (Mx n), IsCompact K → K ⊆ UJset ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ t : Fin d → ℝ, ‖t‖ ≤ 1 →
      ‖F l (z * (List.ofFn fun i => NormedSpace.exp (t i • b i)).prod) - F l z - ∑ i, t i • F (b i :: l) z‖ ≤
        C * ‖t‖ ^ 2 := by
  intro d
  induction d with
  | zero =>
    intro b hb K hK hKU
    refine ⟨0, le_rfl, fun z _ t _ => ?_⟩
    simp
  | succ d ih =>
    intro b hb K hK hKU
    have hX := hb 0
    have hK' := isCompact_expSweep hK (b 0)
    have hK'U := expSweep_sub hKU hX
    obtain ⟨C', hC'0, hC'⟩ := ih (fun i => b i.succ) (fun i => hb _) _ hK' hK'U
    obtain ⟨B0, hB00, hB0⟩ := hG.bdd_of_isCompact (lie_cons hX (lie_cons hX hl)) hK' hK'U
    have hBi : ∀ i : Fin d, ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ expSweep K (b 0), ‖F (b 0 :: b i.succ :: l) y‖ ≤ B :=
      fun i => hG.bdd_of_isCompact (lie_cons hX (lie_cons (hb _) hl)) hK' hK'U
    choose B hBnn hB using hBi
    have hBs : 0 ≤ ∑ i, B i := Finset.sum_nonneg fun i _ => hBnn i
    refine ⟨C' + ∑ i, B i + B0, by positivity, fun z hz t ht => ?_⟩
    have hzU := hKU hz
    have hti : ∀ i, |t i| ≤ ‖t‖ := fun i => by simpa using norm_le_pi_norm t i
    have ht0 : t 0 ∈ Set.Icc (-1 : ℝ) 1 := abs_le.1 ((hti 0).trans ht)
    have ht' : ‖(fun i : Fin d => t i.succ)‖ ≤ ‖t‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg t)).2 fun i => norm_le_pi_norm t i.succ
    have hz1 := mem_expSweep hz (b 0) ht0
    have hprod : z * (List.ofFn fun i => NormedSpace.exp (t i • b i)).prod =
        z * NormedSpace.exp (t 0 • b 0) * (List.ofFn fun i : Fin d => NormedSpace.exp (t i.succ • b i.succ)).prod := by
      rw [List.ofFn_succ, List.prod_cons, Matrix.mul_assoc]
    rw [hprod, Fin.sum_univ_succ]
    set z1 := z * NormedSpace.exp (t 0 • b 0) with hz1def
    have h1 := hC' z1 hz1 (fun i => t i.succ) (ht'.trans ht)
    have h2 : ‖∑ i : Fin d, t i.succ • (F (b i.succ :: l) z1 - F (b i.succ :: l) z)‖ ≤ (∑ i, B i) * ‖t‖ ^ 2 := by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_smul, Real.norm_eq_abs]
      have hd := hF.norm_sub_exp_le (lie_cons (hb i.succ) hl) hX hzU
        (fun s hs => hB i _ (mem_expSweep hz (b 0) hs)) (abs_le.2 ht0)
      calc |t i.succ| * ‖F (b i.succ :: l) z1 - F (b i.succ :: l) z‖ ≤ ‖t‖ * (B i * ‖t‖) :=
            mul_le_mul (hti _) (hd.trans (mul_le_mul_of_nonneg_left (hti 0) (hBnn i))) (norm_nonneg _)
              (norm_nonneg _)
        _ = B i * ‖t‖ ^ 2 := by ring
    have h3 := hF.norm_taylor_exp_le hl hX hzU (fun s hs => hB0 _ (mem_expSweep hz (b 0) hs)) (abs_le.2 ht0)
    have h3' : B0 * t 0 ^ 2 ≤ B0 * ‖t‖ ^ 2 := by
      refine mul_le_mul_of_nonneg_left ?_ hB00
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hti 0) 2
    have h1' : C' * ‖(fun i : Fin d => t i.succ)‖ ^ 2 ≤ C' * ‖t‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ht' 2) hC'0
    have e : F l (z1 * (List.ofFn fun i : Fin d => NormedSpace.exp (t i.succ • b i.succ)).prod) - F l z -
        (t 0 • F (b 0 :: l) z + ∑ i : Fin d, t i.succ • F (b i.succ :: l) z) =
        (F l (z1 * (List.ofFn fun i : Fin d => NormedSpace.exp (t i.succ • b i.succ)).prod) - F l z1 -
          ∑ i : Fin d, t i.succ • F (b i.succ :: l) z1) +
        ∑ i : Fin d, t i.succ • (F (b i.succ :: l) z1 - F (b i.succ :: l) z) +
        (F l z1 - F l z - t 0 • F (b 0 :: l) z) := by
      simp only [smul_sub, Finset.sum_sub_distrib]
      abel
    rw [e]
    refine (norm_add₃_le).trans ?_
    have : (C' + ∑ i, B i + B0) * ‖t‖ ^ 2 = C' * ‖t‖ ^ 2 + (∑ i, B i) * ‖t‖ ^ 2 + B0 * ‖t‖ ^ 2 := by ring
    rw [this]
    exact add_le_add_three (h1.trans h1') h2 (h3.trans h3')

/- English proof (translation)
Introduce `n ε N F hF hG l hl d b hb g hg`. Take `⟨C, -, hC⟩` from `hF.taylor_prod hG hl d b hb {g} isCompact_singleton (Set.singleton_subset_iff.2 hg)`. Rewrite using `[hasFDerivAt_iff_isLittleO_nhds_zero]`. Establish `e0 : (List.ofFn fun i => NormedSpace.exp ((0 : Fin d → ℝ) i • b i)).prod = 1`. Simplify using `[List.prod_ofFn]`.

Use `Asymptotics.IsBigO.trans_isLittleO ?_ (Asymptotics.isLittleO_norm_pow_id (n := 2) one_lt_two)` and prove the remaining obligations. Use `Asymptotics.IsBigO.of_bound C ?_` and prove the remaining obligations. Use `filter_upwards [Metric.closedBall_mem_nhds (0 : Fin d → ℝ) one_pos] with h hh`. Rewrite `hh` using `[mem_closedBall_zero_iff]`. Simplify using `only [zero_add, e0, Matrix.mul_one, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, norm_pow, norm_norm]`.

Conclude with `hC g rfl h hh`.
-/
theorem hasFDerivAt_derFam_prodExp : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ),
    GlobalTheory.TypeSum.IsDerFam ε F → GlobalTheory.TypeSum.FamGrowth ε N F →
    ∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ (d : ℕ) (b : Fin d → GlobalTheory.TypeSum.Mx n), (∀ i, b i ∈ lieSet ε) →
    ∀ g ∈ UJset ε, HasFDerivAt (fun t : Fin d → ℝ => F l (g * (List.ofFn fun i => NormedSpace.exp (t i • b i)).prod))
      (∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (F (b i :: l) g)) 0 := by
  intro n ε N F hF hG l hl d b hb g hg
  obtain ⟨C, -, hC⟩ := hF.taylor_prod hG hl d b hb {g} isCompact_singleton (Set.singleton_subset_iff.2 hg)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have e0 : (List.ofFn fun i => NormedSpace.exp ((0 : Fin d → ℝ) i • b i)).prod = 1 := by
    simp [List.prod_ofFn]
  refine Asymptotics.IsBigO.trans_isLittleO ?_ (Asymptotics.isLittleO_norm_pow_id (n := 2) one_lt_two)
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : Fin d → ℝ) one_pos] with h hh
  rw [mem_closedBall_zero_iff] at hh
  simp only [zero_add, e0, Matrix.mul_one, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, norm_pow, norm_norm]
  exact hC g rfl h hh

end GlobalTheory.TypeSum
