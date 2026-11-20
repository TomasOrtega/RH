import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPoint

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov

/- English proof (translation)
Simplify using `only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply, mul_assoc]`.
-/
private theorem hform_eq_dotProduct_mulVec {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (s y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J s y = star s ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply,
    mul_assoc]

/- English proof (translation)
Introduce `I xf a j hj S hS F hF hFm hFS`. Establish `hmaj` using `GlobalTheory.Count.FrameMajorant.frames_give_majorants I (1, xf)`. Use `haveI : IsTotallyComplex I.E := hmaj.1`. Establish `hf : Formalism.HN.nPl I.E = I.f` using `hmaj.2.1`. Establish `hX : ∀ w, IsUnit (frm I (1, xf) w).det` using `fun w => GlobalTheory.Count.FrameMajorant.frm_unit I (1, xf) w`.

Establish `hΛfg : (lamX I (1, xf)).FG` using `(GlobalTheory.PointLattice.lamX_selfDual I (1, xf)).2.1`. Establish `hmain` using `GlobalTheory.Count.PerpStep.main I (1, xf)`. Establish `hht1 : Formalism.HN.ht (bas I) (frm I (1, xf)) (lamX I (1, xf)) = 1` using `hmain.1`. Establish `hperp` using `hmain.2.2.2`. Establish `hfg : ∀ N : Submodule (𝓞 I.E) (Fin I.n → I.E), N ≤ lamX I (1, xf) → N.FG`.

Introduce `N hN`. Use `haveI := isNoetherian_of_fg_of_noetherian _ hΛfg`. Establish `h1 : (N.comap (lamX I (1, xf)).subtype).FG` using `IsNoetherian.noetherian _`. Establish `h2` using `h1.map (lamX I (1, xf)).subtype`. Rewrite `h2` using `[Submodule.map_comap_subtype, inf_eq_right.mpr hN]`. Then use the resulting hypothesis.

Establish `hrat : ∀ N T : Submodule (𝓞 I.E) (Fin I.n → I.E), N ≤ lamX I (1, xf) → Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I (1, xf))) N T → Formalism.HN.ht (bas I) (frm I (1, xf)) N / Formalism.HN.ht (bas I) (frm I (1, xf)) T = Formalism.HN.htQ (bas I) (fr …`. Introduce `N T hN hT`. Rewrite using `[GlobalTheory.Count.PerpStep.ht_eq (bas I) (frm I (1, xf)) hX N (hfg N hN), GlobalTheory.Count.PerpStep.ht_eq (bas I) (frm I (1, xf)) hX T (hfg T (hT.1.trans hN)), GlobalTheory.Count.PerpStep.htQ_eq (bas I) (frm I (1, xf)) hX N T (hfg N hN) hT, ← Real.exp_sub]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `hqpos : ∀ N T : Submodule (𝓞 I.E) (Fin I.n → I.E), N ≤ lamX I (1, xf) → Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I (1, xf))) N T → 0 < Formalism.HN.htQ (bas I) (frm I (1, xf)) N T`. Introduce `N T hN hT`. Rewrite using `[GlobalTheory.Count.PerpStep.htQ_eq (bas I) (frm I (1, xf)) hX N T (hfg N hN) hT]`. Conclude with `Real.exp_pos _`. Establish `hdual : ∀ b, b ≤ 2 * a + 1 → perpIn I (1, xf) (F b) = F (2 * a + 1 - b)`.

Introduce `b hb`. Use extensionality with `y`. Rewrite using `[GlobalTheory.Count.PerpStep.perpIn_eq, GlobalTheory.Count.PerpStep.mem_perp, hF.2.2.2 b hb y, hFm]`. Use `and_congr_right fun _ => forall₂_congr fun s _ => ?_` and prove the remaining obligations. Rewrite using `[hform_eq_dotProduct_mulVec]`.

Establish `hsatS : ∀ i : Fin (a + 1), Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I (1, xf))) (lamX I (1, xf)) (S i)`. Introduce `i`. Establish `h` using `GlobalTheory.Count.PerpStep.sat_inf (bas I) (frm I (1, xf)) hX (lamX I (1, xf)) hΛfg (Submodule.span I.E (S i : Set (Fin I.n → I.E)))`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `y`.

Rewrite using `[Submodule.mem_inf, Submodule.restrictScalars_mem]`. Conclude with `hS.2.2.2.1 i y`. Establish `hsatF : ∀ b, b ≤ 2 * a + 1 → Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I (1, xf))) (lamX I (1, xf)) (F b)`. Introduce `b hb`. Distinguish the cases in `hba : b ≤ a`.

Establish `e : F b = S ⟨b, by omega⟩` using `hFS ⟨b, by omega⟩`. Rewrite using `[e]`. Conclude with `hsatS _`. Establish `e : F (2 * a + 1 - b) = S ⟨2 * a + 1 - b, by omega⟩` using `hFS ⟨2 * a + 1 - b, by omega⟩`. Establish `h` using `(hperp (F (2 * a + 1 - b)) (F (2 * a + 1 - b)) (by rw [e]; exact hsatS _) (by rw [e]; exact hsatS _) le_rfl).1`.

Rewrite `h` using `[hdual _ (by omega), show 2 * a + 1 - (2 * a + 1 - b) = b by omega]`. Then use the resulting hypothesis. Establish `hpiece : ∀ b, b + 1 ≤ 2 * a + 1 → pieceHt (frm I (1, xf)) F b = Formalism.HN.htQ (bas I) (frm I (1, xf)) (F (b + 1)) (F b)`. Introduce `b hb`. Unfold `pieceHt`. Conclude with `hrat _ _ (hsatF _ hb).1 (GlobalTheory.Count.PerpStep.sat_mono (bas I) (frm I (1, xf)) (hsatF b (by omega)) (hF.1 (Nat.le_succ b)) (hsatF _ hb).1)`.

Establish `hsat' : ∀ b, b + 1 ≤ 2 * a + 1 → Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I (1, xf))) (F (b + 1)) (F b)` using `fun b hb => GlobalTheory.Count.PerpStep.sat_mono (bas I) (frm I (1, xf)) (hsatF b (by omega)) (hF.1 (Nat.le_succ b)) (hsatF _ hb).1`. Use `⟨fun i => ?_, ?_, fun b hb => ?_⟩` and prove the remaining obligations. Establish `hi` using `i.isLt`. Establish `hFi : F i = S i.castSucc` using `by simpa using hFS i.castSucc`. Establish `hFi1 : F (i + 1) = S i.succ` using `by simpa using hFS i.succ`.

Establish `hq` using `hqpos _ _ (hsatF _ (by omega)).1 (hsat' i (by omega))`. Rewrite `hq` using `[hFi1, hFi]`. Establish `hrk : ((Formalism.HN.rkK (S i.succ) : ℝ) - Formalism.HN.rkK (S i.castSucc)) = j i`. Rewrite using `[hS.2.2.1 i]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hjpos : (0 : ℝ) < j i` using `by exact_mod_cast hj i`. Establish `hfpos : (0 : ℝ) < I.f`. Rewrite using `[← hf]`. Conclude with `Fintype.card_pos` after adjusting the coercions.

Establish `hsz : Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) = Formalism.HN.htQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ^ ((1 : ℝ) / (2 * (I.f : ℝ) * (j i : ℝ)))`. Unfold `Formalism.HN.sizeQ`. Rewrite using `[hrk, hf]`. Establish `hpow : Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ^ (2 * I.f * j i) = Formalism.HN.htQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc)`. Rewrite using `[hsz, ← Real.rpow_natCast, ← Real.rpow_mul hq.le]`.

Establish `hc : (1 : ℝ) / (2 * (I.f : ℝ) * (j i : ℝ)) * ((2 * I.f * j i : ℕ) : ℝ) = 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hc, Real.rpow_one]`. Establish `hpi : pieceHt (frm I (1, xf)) F i = Formalism.HN.htQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc)`.

Rewrite using `[hpiece i (by omega), hFi1, hFi]`. Use `⟨by rw [hsz]; exact Real.rpow_pos_of_pos hq _, by rw [hpi, hpow], ?_⟩` and prove the remaining obligations. Rewrite using `[hpow, hpiece (2 * a - i) (by omega)]`. Establish `hPi` using `hdual i (by omega)`. Establish `hPi1` using `hdual (i + 1) (by omega)`.

Rewrite `hPi` using `[show 2 * a + 1 - i = 2 * a - i + 1 by omega]`. Rewrite `hPi1` using `[show 2 * a + 1 - (i + 1) = 2 * a - i by omega]`. Establish `h` using `(hperp (F i) (F (i + 1)) (hsatF _ (by omega)) (hsatF _ (by omega)) (hF.1 (Nat.le_succ _))).2.2.2.2`. Rewrite `h` using `[hPi, hPi1, hFi1, hFi]`. Conclude with `h`.

Establish `hPa` using `hdual a (by omega)`. Establish `hPa1` using `hdual (a + 1) (by omega)`. Rewrite `hPa` using `[show 2 * a + 1 - a = a + 1 by omega]`. Rewrite `hPa1` using `[show 2 * a + 1 - (a + 1) = a by omega]`. Establish `h` using `(hperp (F a) (F (a + 1)) (hsatF _ (by omega)) (hsatF _ (by omega)) (hF.1 (Nat.le_succ _))).2.2.2.2`.

Rewrite `h` using `[hPa, hPa1]`. Establish `hq` using `hqpos _ _ (hsatF _ (by omega)).1 (hsat' a (by omega))`. Rewrite using `[hpiece a (by omega)]`. Use `set q := Formalism.HN.htQ (bas I) (frm I (1, xf)) (F (a + 1)) (F a) with hqdef`. Establish `hmul : q * q = 1`.

Combine the equalities or inequalities in the displayed calculation. Use the polynomial consequences of the given equalities and inequalities. Unfold `pieceHt`. Rewrite using `[hF.2.2.1 (b + 1) (by omega), hF.2.2.1 b hb, hFm, hht1]`. Evaluate the numerical expressions.
-/
theorem pieceHt_dualFlag : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ), (∀ i, 1 ≤ j i) → ∀ (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∀ F : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E), IsDualFlag I.J F (2 * a + 1) → F (2 * a + 1) = lamX I (1, xf) → (∀ i : Fin (a + 1), F i = S i) → (∀ i : Fin a, 0 < Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ∧ pieceHt (frm I (1, xf)) F i = Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ^ (2 * I.f * j i) ∧ pieceHt (frm I (1, xf)) F (2 * a - i) = (Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ^ (2 * I.f * j i))⁻¹) ∧ pieceHt (frm I (1, xf)) F a = 1 ∧ ∀ b, 2 * a + 1 ≤ b → pieceHt (frm I (1, xf)) F b = 1 := by
  intro I xf a j hj S hS F hF hFm hFS
  have hmaj := GlobalTheory.Count.FrameMajorant.frames_give_majorants I (1, xf)
  haveI : IsTotallyComplex I.E := hmaj.1
  have hf : Formalism.HN.nPl I.E = I.f := hmaj.2.1
  have hX : ∀ w, IsUnit (frm I (1, xf) w).det := fun w => GlobalTheory.Count.FrameMajorant.frm_unit I (1, xf) w
  have hΛfg : (lamX I (1, xf)).FG := (GlobalTheory.PointLattice.lamX_selfDual I (1, xf)).2.1
  have hmain := GlobalTheory.Count.PerpStep.main I (1, xf)
  have hht1 : Formalism.HN.ht (bas I) (frm I (1, xf)) (lamX I (1, xf)) = 1 := hmain.1
  have hperp := hmain.2.2.2
  have hfg : ∀ N : Submodule (𝓞 I.E) (Fin I.n → I.E), N ≤ lamX I (1, xf) → N.FG := by
    intro N hN
    haveI := isNoetherian_of_fg_of_noetherian _ hΛfg
    have h1 : (N.comap (lamX I (1, xf)).subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map (lamX I (1, xf)).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hN] at h2

  have hrat : ∀ N T : Submodule (𝓞 I.E) (Fin I.n → I.E), N ≤ lamX I (1, xf) →
      Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I (1, xf))) N T →
      Formalism.HN.ht (bas I) (frm I (1, xf)) N / Formalism.HN.ht (bas I) (frm I (1, xf)) T =
        Formalism.HN.htQ (bas I) (frm I (1, xf)) N T := by
    intro N T hN hT
    rw [GlobalTheory.Count.PerpStep.ht_eq (bas I) (frm I (1, xf)) hX N (hfg N hN),
      GlobalTheory.Count.PerpStep.ht_eq (bas I) (frm I (1, xf)) hX T (hfg T (hT.1.trans hN)),
      GlobalTheory.Count.PerpStep.htQ_eq (bas I) (frm I (1, xf)) hX N T (hfg N hN) hT, ← Real.exp_sub]
    congr 1
    ring
  have hqpos : ∀ N T : Submodule (𝓞 I.E) (Fin I.n → I.E), N ≤ lamX I (1, xf) →
      Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I (1, xf))) N T →
      0 < Formalism.HN.htQ (bas I) (frm I (1, xf)) N T := by
    intro N T hN hT
    rw [GlobalTheory.Count.PerpStep.htQ_eq (bas I) (frm I (1, xf)) hX N T (hfg N hN) hT]
    exact Real.exp_pos _

  have hdual : ∀ b, b ≤ 2 * a + 1 → perpIn I (1, xf) (F b) = F (2 * a + 1 - b) := by
    intro b hb
    ext y
    rw [GlobalTheory.Count.PerpStep.perpIn_eq, GlobalTheory.Count.PerpStep.mem_perp, hF.2.2.2 b hb y, hFm]
    refine and_congr_right fun _ => forall₂_congr fun s _ => ?_
    rw [hform_eq_dotProduct_mulVec]

  have hsatS : ∀ i : Fin (a + 1),
      Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I (1, xf))) (lamX I (1, xf)) (S i) := by
    intro i
    have h := GlobalTheory.Count.PerpStep.sat_inf (bas I) (frm I (1, xf)) hX (lamX I (1, xf)) hΛfg
      (Submodule.span I.E (S i : Set (Fin I.n → I.E)))
    convert h using 1
    ext y
    rw [Submodule.mem_inf, Submodule.restrictScalars_mem]
    exact hS.2.2.2.1 i y
  have hsatF : ∀ b, b ≤ 2 * a + 1 →
      Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I (1, xf))) (lamX I (1, xf)) (F b) := by
    intro b hb
    by_cases hba : b ≤ a
    · have e : F b = S ⟨b, by omega⟩ := hFS ⟨b, by omega⟩
      rw [e]
      exact hsatS _
    · have e : F (2 * a + 1 - b) = S ⟨2 * a + 1 - b, by omega⟩ := hFS ⟨2 * a + 1 - b, by omega⟩
      have h := (hperp (F (2 * a + 1 - b)) (F (2 * a + 1 - b)) (by rw [e]; exact hsatS _)
        (by rw [e]; exact hsatS _) le_rfl).1
      rwa [hdual _ (by omega), show 2 * a + 1 - (2 * a + 1 - b) = b by omega] at h
  have hpiece : ∀ b, b + 1 ≤ 2 * a + 1 →
      pieceHt (frm I (1, xf)) F b = Formalism.HN.htQ (bas I) (frm I (1, xf)) (F (b + 1)) (F b) := by
    intro b hb
    unfold pieceHt
    exact hrat _ _ (hsatF _ hb).1
      (GlobalTheory.Count.PerpStep.sat_mono (bas I) (frm I (1, xf)) (hsatF b (by omega))
        (hF.1 (Nat.le_succ b)) (hsatF _ hb).1)
  have hsat' : ∀ b, b + 1 ≤ 2 * a + 1 →
      Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I (1, xf))) (F (b + 1)) (F b) := fun b hb =>
    GlobalTheory.Count.PerpStep.sat_mono (bas I) (frm I (1, xf)) (hsatF b (by omega))
      (hF.1 (Nat.le_succ b)) (hsatF _ hb).1
  refine ⟨fun i => ?_, ?_, fun b hb => ?_⟩
  · have hi := i.isLt
    have hFi : F i = S i.castSucc := by simpa using hFS i.castSucc
    have hFi1 : F (i + 1) = S i.succ := by simpa using hFS i.succ
    have hq := hqpos _ _ (hsatF _ (by omega)).1 (hsat' i (by omega))
    rw [hFi1, hFi] at hq
    have hrk : ((Formalism.HN.rkK (S i.succ) : ℝ) - Formalism.HN.rkK (S i.castSucc)) = j i := by
      rw [hS.2.2.1 i]
      push_cast
      ring
    have hjpos : (0 : ℝ) < j i := by exact_mod_cast hj i
    have hfpos : (0 : ℝ) < I.f := by
      rw [← hf]
      exact_mod_cast Fintype.card_pos
    have hsz : Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) =
        Formalism.HN.htQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ^
          ((1 : ℝ) / (2 * (I.f : ℝ) * (j i : ℝ))) := by
      unfold Formalism.HN.sizeQ
      rw [hrk, hf]
    have hpow : Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ^ (2 * I.f * j i) =
        Formalism.HN.htQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) := by
      rw [hsz, ← Real.rpow_natCast, ← Real.rpow_mul hq.le]
      have hc : (1 : ℝ) / (2 * (I.f : ℝ) * (j i : ℝ)) * ((2 * I.f * j i : ℕ) : ℝ) = 1 := by
        push_cast
        field_simp
      rw [hc, Real.rpow_one]
    have hpi : pieceHt (frm I (1, xf)) F i =
        Formalism.HN.htQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) := by
      rw [hpiece i (by omega), hFi1, hFi]
    refine ⟨by rw [hsz]; exact Real.rpow_pos_of_pos hq _, by rw [hpi, hpow], ?_⟩
    rw [hpow, hpiece (2 * a - i) (by omega)]
    have hPi := hdual i (by omega)
    have hPi1 := hdual (i + 1) (by omega)
    rw [show 2 * a + 1 - i = 2 * a - i + 1 by omega] at hPi
    rw [show 2 * a + 1 - (i + 1) = 2 * a - i by omega] at hPi1
    have h := (hperp (F i) (F (i + 1)) (hsatF _ (by omega)) (hsatF _ (by omega))
      (hF.1 (Nat.le_succ _))).2.2.2.2
    rw [hPi, hPi1, hFi1, hFi] at h
    exact h
  · have hPa := hdual a (by omega)
    have hPa1 := hdual (a + 1) (by omega)
    rw [show 2 * a + 1 - a = a + 1 by omega] at hPa
    rw [show 2 * a + 1 - (a + 1) = a by omega] at hPa1
    have h := (hperp (F a) (F (a + 1)) (hsatF _ (by omega)) (hsatF _ (by omega))
      (hF.1 (Nat.le_succ _))).2.2.2.2
    rw [hPa, hPa1] at h
    have hq := hqpos _ _ (hsatF _ (by omega)).1 (hsat' a (by omega))
    rw [hpiece a (by omega)]
    set q := Formalism.HN.htQ (bas I) (frm I (1, xf)) (F (a + 1)) (F a) with hqdef
    have hmul : q * q = 1 := by
      calc q * q = q⁻¹ * q := by rw [← h]
        _ = 1 := inv_mul_cancel₀ hq.ne'
    nlinarith
  · unfold pieceHt
    rw [hF.2.2.1 (b + 1) (by omega), hF.2.2.1 b hb, hFm, hht1]
    norm_num

end GlobalTheory.RadCov
