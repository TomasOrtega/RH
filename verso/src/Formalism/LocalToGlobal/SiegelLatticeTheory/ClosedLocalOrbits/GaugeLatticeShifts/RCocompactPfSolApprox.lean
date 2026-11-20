import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfApprox

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

namespace Formalism.L2.SG.Pf.RationalApproximateSolutions

variable {ι K L : Type*} [Fintype ι] [DecidableEq ι] [Field K] [Field L]

def condMat (lv : ι → ℕ) (k : ℕ) (G G' : Matrix ι ι K) : Matrix ((ι × ι) ⊕ (ι × ι)) (ι × ι) K :=
  Matrix.of fun r q => Sum.elim (fun p : ι × ι => if lv p.2 < lv p.1 + k ∧ q = p then (1 : K) else 0)
    (fun p => if lv p.2 < lv p.1 + 1 then G' p.1 q.1 * G q.2 p.2 else 0) r

def matOf (z : ι × ι → L) : Matrix ι ι L := Matrix.of fun a b => z (a, b)

/- English proof (translation)
Use `first`. Consider the case `simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, condMat, Matrix.of_apply, Sum.elim_inl]`. Consider the case `simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.map_apply, condMat, Matrix.of_apply, Sum.elim_inl]`. Distinguish the cases in `h : lv j < lv i + k`. Rewrite using `[if_pos h, Finset.sum_eq_single (i, j)]`.

Simplify using `[h]`. Introduce `q _ hq`. Simplify using `[hq]`. Introduce `hn`. Conclude with `absurd (Finset.mem_univ _) hn`.

Rewrite using `[if_neg h]`. Simplify using `[h]`.
-/
theorem condMat_inl (lv : ι → ℕ) (k : ℕ) (G G' : Matrix ι ι K) (f : K →+* L) (z : ι × ι → L) (i j : ι) :
    ((condMat lv k G G').map f *ᵥ z) (Sum.inl (i, j)) = if lv j < lv i + k then z (i, j) else 0 := by
  first
    | simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, condMat, Matrix.of_apply, Sum.elim_inl]
    | simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.map_apply, condMat, Matrix.of_apply, Sum.elim_inl]
  by_cases h : lv j < lv i + k
  · rw [if_pos h, Finset.sum_eq_single (i, j)]
    · simp [h]
    · intro q _ hq
      simp [hq]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · rw [if_neg h]
    simp [h]

/- English proof (translation)
Use `first`. Consider the case `simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, condMat, Matrix.of_apply, Sum.elim_inr]`. Consider the case `simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.map_apply, condMat, Matrix.of_apply, Sum.elim_inr]`. Distinguish the cases in `h : lv j < lv i + 1`. Simplify using `only [h, ↓reduceIte, map_mul]`.

Rewrite using `[Fintype.sum_prod_type]`. Simplify using `only [Matrix.mul_apply, Matrix.map_apply, matOf, Matrix.of_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Simplify using `[h]`.
-/
theorem condMat_inr (lv : ι → ℕ) (k : ℕ) (G G' : Matrix ι ι K) (f : K →+* L) (z : ι × ι → L) (i j : ι) :
    ((condMat lv k G G').map f *ᵥ z) (Sum.inr (i, j)) =
      if lv j < lv i + 1 then (G'.map f * matOf z * G.map f) i j else 0 := by
  first
    | simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, condMat, Matrix.of_apply, Sum.elim_inr]
    | simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.map_apply, condMat, Matrix.of_apply, Sum.elim_inr]
  by_cases h : lv j < lv i + 1
  · simp only [h, ↓reduceIte, map_mul]
    rw [Fintype.sum_prod_type]
    simp only [Matrix.mul_apply, Matrix.map_apply, matOf, Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  · simp [h]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hz`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij`. Use `congrFun hz (Sum.inl (i, j))` as an intermediate fact.

Rewrite `this` using `[condMat_inl, if_pos hij]`. Simplify `this` using `[matOf]`. Introduce `i j hij`. Use `congrFun hz (Sum.inr (i, j))` as an intermediate fact. Rewrite `this` using `[condMat_inr, if_pos hij]`.

Simplify using `using this`. Introduce and unpack `⟨h1, h2⟩`. Use function extensionality and compare the values at `r`. Break down `r with ⟨i, j⟩ | ⟨i, j⟩` into its components or cases. Rewrite using `[condMat_inl] split_ifs with hij`.

Simplify `h1 i j hij` using `[matOf]`. Both sides reduce to the same expression. Rewrite using `[condMat_inr] split_ifs with hij`. Simplify using `using h2 i j hij`. Both sides reduce to the same expression.
-/
theorem cond_iff (lv : ι → ℕ) (k : ℕ) (G G' : Matrix ι ι K) (f : K →+* L) (z : ι × ι → L) :
    (condMat lv k G G').map f *ᵥ z = 0 ↔
      InPat lv k (matOf z) ∧ InPat lv 1 (G'.map f * matOf z * G.map f) := by
  constructor
  · intro hz
    refine ⟨?_, ?_⟩
    · intro i j hij
      have := congrFun hz (Sum.inl (i, j))
      rw [condMat_inl, if_pos hij] at this
      simpa [matOf] using this
    · intro i j hij
      have := congrFun hz (Sum.inr (i, j))
      rw [condMat_inr, if_pos hij] at this
      simpa using this
  · rintro ⟨h1, h2⟩
    funext r
    rcases r with ⟨i, j⟩ | ⟨i, j⟩
    · rw [condMat_inl]
      split_ifs with hij
      · simpa [matOf] using h1 i j hij
      · rfl
    · rw [condMat_inr]
      split_ifs with hij
      · simpa using h2 i j hij
      · rfl

end Formalism.L2.SG.Pf.RationalApproximateSolutions

namespace Formalism.L2.SG.TermOp.Vanish

open Formalism.L2.SG.Pf.RationalApproximateSolutions

/- English proof (translation)
Introduce `D X G G' k N hN`. Take `⟨P0, hMP0, hfix0⟩` from `Formalism.L2.SG.Pf.RCoc.kerBaseChange_holds X.B.I.E X.B.I.E (RingHom.id _) _ _ (condMat (lvk X) k G G')`. Establish `hfixE : ∀ w : Kap X × Kap X → X.B.I.E, condMat (lvk X) k G G' *ᵥ w = 0 → P0 *ᵥ w = w`. Introduce `w hw`. Establish `e` using `hfix0 w (by simpa using hw)`.

Simplify using `using e`. Establish `hfixV : ∀ v (z : Kap X × Kap X → ℂ), (condMat (lvk X) k G G').map (X.B.I.φ v) *ᵥ z = 0 → P0.map (X.B.I.φ v) *ᵥ z = z`. Introduce `v z hz`. Take `⟨Pv, hMPv, hfixv⟩` from `Formalism.L2.SG.Pf.RCoc.kerBaseChange_holds X.B.I.E ℂ (X.B.I.φ v) _ _ (condMat (lvk X) k G G')`. Establish `hPP : P0 * Pv = Pv`.

Use `Matrix.ext_of_mulVec_single fun q => ?_` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec]`. Apply `hfixE` to reduce the goal to its premises. Rewrite using `[Matrix.mulVec_mulVec, hMPv, Matrix.zero_mulVec]`. Establish `e` using `hfixv z hz`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨c, hc, hcI⟩` from `exists_common_den (E := X.B.I.E) (fun q : (Kap X × Kap X) × (Kap X × Kap X) => P0 q.1 q.2)`. Set `Q : Matrix (Kap X × Kap X) (Kap X × Kap X) (𝓞 X.B.I.E)` to `Matrix.of fun a b => ⟨(c : X.B.I.E) * P0 a b, hcI (a, b)⟩`. Establish `hQ : ∀ a b, algebraMap (𝓞 X.B.I.E) X.B.I.E (Q a b) = (c : X.B.I.E) * P0 a b` using `fun a b => rfl`. Take `⟨R0, hR0⟩` from `Formalism.L2.SG.Pf.oeApprox_holds X.B.I.F X.B.I.E X.B.I.cm.totReal X.B.I.cm.cmUnram.1 X.B.I.cm.deg2 X.B.I.φ X.B.I.φ_over`.

Take `⟨Nc, hNcd⟩ : ∃ Nc : ℕ, Nc = N * c` from `⟨_, rfl⟩`. Establish `hNc0 : (Nc : ℂ) ≠ 0`. Rewrite using `[hNcd]`. Conclude with `Nat.cast_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))`. Use `⟨((Nc : ℝ) * max R0 0) * ∑ v, ∑ q, ∑ r, ‖X.B.I.φ v (P0 q r)‖, fun P hP => ?_⟩` and prove the remaining obligations.

Use `choose y hy using fun q : Kap X × Kap X => hR0 (fun v => P v q.1 q.2 / (Nc : ℂ))`. Use `set Yv : Kap X × Kap X → X.B.I.E := (Nc : X.B.I.E) • (P0 *ᵥ fun q => (y q : X.B.I.E)) with hYvd`. Establish `hYv : condMat (lvk X) k G G' *ᵥ Yv = 0`. Rewrite using `[hYvd, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hMP0, Matrix.zero_mulVec, smul_zero]`. Establish `hcond` using `(cond_iff (lvk X) k G G' (RingHom.id X.B.I.E) Yv).1 (by simpa using hYv)`.

Use `⟨matOf Yv, hcond.1, by simpa using hcond.2, ?_, ?_⟩` and prove the remaining obligations. Use `⟨Matrix.of fun a b => (Q *ᵥ y) (a, b), ?_⟩` and prove the remaining obligations. Use extensionality with `a b`. Establish `e` using `RingHom.map_mulVec (algebraMap (𝓞 X.B.I.E) X.B.I.E) Q y (a, b)`. Simplify using `only [matOf, hYvd, Matrix.of_apply, Matrix.smul_apply, Matrix.map_apply, Pi.smul_apply, smul_eq_mul]`.

Express the relevant statement in the definitionally equal form `_ = (N : X.B.I.E) * algebraMap (𝓞 X.B.I.E) X.B.I.E ((Q *ᵥ y) (a, b))`. Rewrite using `[e]`. Simplify using `only [mulVec, dotProduct, Matrix.map_apply, Function.comp_apply, hQ, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[hNcd]`.

Rewrite using `[show algebraMap (𝓞 X.B.I.E) X.B.I.E (y r) = (y r : X.B.I.E) from rfl]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `v i j`. Establish `hm : matOf (fun q : Kap X × Kap X => P v q.1 q.2) = P v`.

Use extensionality with `a b`. Both sides reduce to the same expression. Establish `hz : (condMat (lvk X) k G G').map (X.B.I.φ v) *ᵥ (fun q : Kap X × Kap X => P v q.1 q.2) = 0` using `(cond_iff (lvk X) k G G' (X.B.I.φ v) _).2 (by rw [hm]; exact ⟨(hP v).1, (hP v).2⟩)`. Establish `hfz` using `congrFun (hfixV v _ hz) (i, j)`. Simplify using `only [mulVec, dotProduct, Matrix.map_apply] at hfz`.

Establish `key : ((matOf Yv).map (X.B.I.φ v) - P v) i j = ∑ r, X.B.I.φ v (P0 (i, j) r) * ((Nc : ℂ) * X.B.I.φ v (y r : X.B.I.E) - P v r.1 r.2)`. Simplify using `only [Matrix.sub_apply, Matrix.map_apply, matOf, Matrix.of_apply, hYvd, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, map_mul, map_sum, map_natCast]`. Use `conv_lhs => rw [← hfz]`. Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Establish `hM0 : 0 ≤ (Nc : ℝ) * max R0 0` using `mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)`. Rewrite using `[key]`. Combine the equalities or inequalities in the displayed calculation. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)` and prove the remaining obligations.

Rewrite using `[norm_mul]`. Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations. Establish `h1 : ‖P v r.1 r.2 / (Nc : ℂ) - X.B.I.φ v (y r : X.B.I.E)‖ ≤ R0` using `hy r v`. Establish `h2 : (Nc : ℂ) * (P v r.1 r.2 / (Nc : ℂ)) = P v r.1 r.2` using `by field_simp`. Establish `e2 : (Nc : ℂ) * X.B.I.φ v (y r : X.B.I.E) - P v r.1 r.2 = -((Nc : ℂ) * (P v r.1 r.2 / (Nc : ℂ) - X.B.I.φ v (y r : X.B.I.E)))`.

Rewrite using `[mul_sub, h2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2, norm_neg, norm_mul, Complex.norm_natCast]`. Conclude with `mul_le_mul_of_nonneg_left (h1.trans (le_max_left _ _)) (Nat.cast_nonneg _)`. Use `_ = ((Nc : ℝ) * max R0 0) * ∑ r, ‖X.B.I.φ v (P0 (i, j) r)‖ := by`.

Rewrite using `[← Finset.sum_mul, mul_comm]`. Use `_ ≤ ((Nc : ℝ) * max R0 0) * ∑ v, ∑ q, ∑ r, ‖X.B.I.φ v (P0 q r)‖ := by`. Use `mul_le_mul_of_nonneg_left ?_ hM0` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ratSolApprox_holds : RatSolApprox := by
  intro D X G G' k N hN
  obtain ⟨P0, hMP0, hfix0⟩ :=
    Formalism.L2.SG.Pf.RCoc.kerBaseChange_holds X.B.I.E X.B.I.E (RingHom.id _) _ _ (condMat (lvk X) k G G')
  have hfixE : ∀ w : Kap X × Kap X → X.B.I.E, condMat (lvk X) k G G' *ᵥ w = 0 → P0 *ᵥ w = w := by
    intro w hw
    have e := hfix0 w (by simpa using hw)
    simpa using e
  have hfixV : ∀ v (z : Kap X × Kap X → ℂ), (condMat (lvk X) k G G').map (X.B.I.φ v) *ᵥ z = 0 →
      P0.map (X.B.I.φ v) *ᵥ z = z := by
    intro v z hz
    obtain ⟨Pv, hMPv, hfixv⟩ :=
      Formalism.L2.SG.Pf.RCoc.kerBaseChange_holds X.B.I.E ℂ (X.B.I.φ v) _ _ (condMat (lvk X) k G G')
    have hPP : P0 * Pv = Pv := by
      refine Matrix.ext_of_mulVec_single fun q => ?_
      rw [← Matrix.mulVec_mulVec]
      apply hfixE
      rw [Matrix.mulVec_mulVec, hMPv, Matrix.zero_mulVec]
    have e := hfixv z hz
    calc P0.map (X.B.I.φ v) *ᵥ z = P0.map (X.B.I.φ v) *ᵥ (Pv.map (X.B.I.φ v) *ᵥ z) := by rw [e]
      _ = (P0 * Pv).map (X.B.I.φ v) *ᵥ z := by rw [Matrix.mulVec_mulVec, Matrix.map_mul]
      _ = z := by rw [hPP, e]
  obtain ⟨c, hc, hcI⟩ := exists_common_den (E := X.B.I.E)
    (fun q : (Kap X × Kap X) × (Kap X × Kap X) => P0 q.1 q.2)
  let Q : Matrix (Kap X × Kap X) (Kap X × Kap X) (𝓞 X.B.I.E) :=
    Matrix.of fun a b => ⟨(c : X.B.I.E) * P0 a b, hcI (a, b)⟩
  have hQ : ∀ a b, algebraMap (𝓞 X.B.I.E) X.B.I.E (Q a b) = (c : X.B.I.E) * P0 a b := fun a b => rfl
  obtain ⟨R0, hR0⟩ := Formalism.L2.SG.Pf.oeApprox_holds X.B.I.F X.B.I.E X.B.I.cm.totReal X.B.I.cm.cmUnram.1
    X.B.I.cm.deg2 X.B.I.φ X.B.I.φ_over
  obtain ⟨Nc, hNcd⟩ : ∃ Nc : ℕ, Nc = N * c := ⟨_, rfl⟩
  have hNc0 : (Nc : ℂ) ≠ 0 := by
    rw [hNcd]
    exact Nat.cast_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  refine ⟨((Nc : ℝ) * max R0 0) * ∑ v, ∑ q, ∑ r, ‖X.B.I.φ v (P0 q r)‖, fun P hP => ?_⟩
  choose y hy using fun q : Kap X × Kap X => hR0 (fun v => P v q.1 q.2 / (Nc : ℂ))
  set Yv : Kap X × Kap X → X.B.I.E := (Nc : X.B.I.E) • (P0 *ᵥ fun q => (y q : X.B.I.E)) with hYvd
  have hYv : condMat (lvk X) k G G' *ᵥ Yv = 0 := by
    rw [hYvd, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hMP0, Matrix.zero_mulVec, smul_zero]
  have hcond := (cond_iff (lvk X) k G G' (RingHom.id X.B.I.E) Yv).1 (by simpa using hYv)
  refine ⟨matOf Yv, hcond.1, by simpa using hcond.2, ?_, ?_⟩
  · refine ⟨Matrix.of fun a b => (Q *ᵥ y) (a, b), ?_⟩
    ext a b
    have e := RingHom.map_mulVec (algebraMap (𝓞 X.B.I.E) X.B.I.E) Q y (a, b)
    simp only [matOf, hYvd, Matrix.of_apply, Matrix.smul_apply, Matrix.map_apply, Pi.smul_apply, smul_eq_mul]
    change _ = (N : X.B.I.E) * algebraMap (𝓞 X.B.I.E) X.B.I.E ((Q *ᵥ y) (a, b))
    rw [e]
    simp only [mulVec, dotProduct, Matrix.map_apply, Function.comp_apply, hQ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hNcd]
    rw [show algebraMap (𝓞 X.B.I.E) X.B.I.E (y r) = (y r : X.B.I.E) from rfl]
    push_cast
    ring
  · intro v i j
    have hm : matOf (fun q : Kap X × Kap X => P v q.1 q.2) = P v := by
      ext a b
      rfl
    have hz : (condMat (lvk X) k G G').map (X.B.I.φ v) *ᵥ (fun q : Kap X × Kap X => P v q.1 q.2) = 0 :=
      (cond_iff (lvk X) k G G' (X.B.I.φ v) _).2 (by rw [hm]; exact ⟨(hP v).1, (hP v).2⟩)
    have hfz := congrFun (hfixV v _ hz) (i, j)
    simp only [mulVec, dotProduct, Matrix.map_apply] at hfz
    have key : ((matOf Yv).map (X.B.I.φ v) - P v) i j =
        ∑ r, X.B.I.φ v (P0 (i, j) r) * ((Nc : ℂ) * X.B.I.φ v (y r : X.B.I.E) - P v r.1 r.2) := by
      simp only [Matrix.sub_apply, Matrix.map_apply, matOf, Matrix.of_apply, hYvd, Pi.smul_apply, smul_eq_mul,
        mulVec, dotProduct, map_mul, map_sum, map_natCast]
      conv_lhs => rw [← hfz]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
    have hM0 : 0 ≤ (Nc : ℝ) * max R0 0 := mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)
    rw [key]
    calc ‖∑ r, X.B.I.φ v (P0 (i, j) r) * ((Nc : ℂ) * X.B.I.φ v (y r : X.B.I.E) - P v r.1 r.2)‖
        ≤ ∑ r, ‖X.B.I.φ v (P0 (i, j) r)‖ * ((Nc : ℝ) * max R0 0) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have h1 : ‖P v r.1 r.2 / (Nc : ℂ) - X.B.I.φ v (y r : X.B.I.E)‖ ≤ R0 := hy r v
          have h2 : (Nc : ℂ) * (P v r.1 r.2 / (Nc : ℂ)) = P v r.1 r.2 := by field_simp
          have e2 : (Nc : ℂ) * X.B.I.φ v (y r : X.B.I.E) - P v r.1 r.2 =
              -((Nc : ℂ) * (P v r.1 r.2 / (Nc : ℂ) - X.B.I.φ v (y r : X.B.I.E))) := by
            rw [mul_sub, h2]
            ring
          rw [e2, norm_neg, norm_mul, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_left (h1.trans (le_max_left _ _)) (Nat.cast_nonneg _)
      _ = ((Nc : ℝ) * max R0 0) * ∑ r, ‖X.B.I.φ v (P0 (i, j) r)‖ := by
          rw [← Finset.sum_mul, mul_comm]
      _ ≤ ((Nc : ℝ) * max R0 0) * ∑ v, ∑ q, ∑ r, ‖X.B.I.φ v (P0 q r)‖ := by
          refine mul_le_mul_of_nonneg_left ?_ hM0
          calc ∑ r, ‖X.B.I.φ v (P0 (i, j) r)‖ ≤ ∑ q, ∑ r, ‖X.B.I.φ v (P0 q r)‖ :=
                Finset.single_le_sum (f := fun q => ∑ r, ‖X.B.I.φ v (P0 q r)‖)
                  (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ (i, j))
            _ ≤ ∑ v', ∑ q, ∑ r, ‖X.B.I.φ v' (P0 q r)‖ :=
                Finset.single_le_sum (f := fun v' => ∑ q, ∑ r, ‖X.B.I.φ v' (P0 q r)‖)
                  (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
                  (Finset.mem_univ v)

end Formalism.L2.SG.TermOp.Vanish
