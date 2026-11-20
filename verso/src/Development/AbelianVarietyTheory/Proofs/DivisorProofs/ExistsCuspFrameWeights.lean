import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatField
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodWeightAntitoneGapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatConstantAbsLeNineExplicitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntitoneWeightLogBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterStrictAntitoneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundsForFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatFrameOfIsShortGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WtBigRun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchoredWeightIndefiniteLiftGaps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizesLargeOfPowerBounds
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
namespace GlobalTheory.FrameBerg

/- English proof (translation)
Rewrite using `[gap, dif_pos hk]`. Use `hv (show (⟨k, by omega⟩ : Fin N) < ⟨k + 1, hk⟩ from Fin.mk_lt_mk.2 (Nat.lt_succ_self k))` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem one_le_gap_of_strictAnti {N : ℕ} {v : Fin N → ℤ} (hv : StrictAnti v) {k : ℕ} (hk : k + 1 < N) :
    1 ≤ gap v k := by
  rw [gap, dif_pos hk]
  have := hv (show (⟨k, by omega⟩ : Fin N) < ⟨k + 1, hk⟩ from Fin.mk_lt_mk.2 (Nat.lt_succ_self k))
  omega

/- English proof (translation)
Unfold `gap`. Use `split_ifs`. Simplify using `only [Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem gap_add {N : ℕ} (v w : Fin N → ℤ) (k : ℕ) : gap (v + w) k = gap v k + gap w k := by
  unfold gap
  split_ifs
  · simp only [Pi.add_apply]; ring
  · simp

/- English proof (translation)
Establish `key : ∀ d (a b : Fin N), (b : ℕ) = a + d → v b ≤ v a`. Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `a b hab`.

Establish `e : b = a` using `Fin.ext (by simpa using hab)`. Rewrite using `[e]`. Consider the case `succ d ih`. Introduce `a b hab`. Establish `hc : (a : ℕ) + d < N` using `by omega`.

Establish `h1` using `ih a ⟨(a : ℕ) + d, hc⟩ rfl`. Establish `h2` using `h ((a : ℕ) + d) (by omega)`. Rewrite `h2` using `[gap, dif_pos (by omega)]`. Establish `e : b = ⟨(a : ℕ) + d + 1, by omega⟩` using `Fin.ext (by simp only; omega)`. Rewrite using `[e]`.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `a b hab`. Conclude with `key ((b : ℕ) - a) a b (by have : (a : ℕ) ≤ b := hab; omega)`.
-/
theorem antitone_of_gap_nonneg {N : ℕ} {v : Fin N → ℤ} (h : ∀ k, k + 1 < N → 0 ≤ gap v k) : Antitone v := by
  have key : ∀ d (a b : Fin N), (b : ℕ) = a + d → v b ≤ v a := by
    intro d
    induction d with
    | zero =>
      intro a b hab
      have e : b = a := Fin.ext (by simpa using hab)
      rw [e]
    | succ d ih =>
      intro a b hab
      have hc : (a : ℕ) + d < N := by omega
      have h1 := ih a ⟨(a : ℕ) + d, hc⟩ rfl
      have h2 := h ((a : ℕ) + d) (by omega)
      rw [gap, dif_pos (by omega)] at h2
      have e : b = ⟨(a : ℕ) + d + 1, by omega⟩ := Fin.ext (by simp only; omega)
      rw [e]
      linarith
  intro a b hab
  exact key ((b : ℕ) - a) a b (by have : (a : ℕ) ≤ b := hab; omega)

end GlobalTheory.FrameBerg

namespace GlobalTheory.FrameBerg

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `hP2 _hDG hS hFD`. Take `⟨C1, hC1, H1⟩` from `GlobalTheory.T.flat_constant_abs_le_nine_explicit hP2`. Take `⟨C2, hC2, H2⟩` from `GlobalTheory.T.antitone_weight_log_bound hP2`. Establish `H0` using `GlobalTheory.T.good_weight_antitone_gap hP2`. Use `(((GlobalTheory.T.weight_parameter_strict_antitone hS).and (GlobalTheory.T.size_bounds_for_family hS)).and (wtBig_run.and hFD)).imp fun Fm CH _ hh => ?_` and prove the remaining obligations.

Take `⟨⟨⟨_, _, a, ha⟩, ⟨_, _, b, hb⟩⟩, ⟨⟨_, _, c, hc⟩, ⟨_, _, d, hd⟩⟩⟩` from `hh`. Take `⟨e, he⟩` from `GlobalTheory.family_sizes_eventually_large _ Fm (2 * C1 + C2 + 1)`. Use `⟨0, le_rfl, max (max a b) (max (max c d) e), fun x hx hle ι p hp i hi Y hY => ?_⟩` and prove the remaining obligations. Establish `hA` using `ha x hx ((le_max_left _ _).trans ((le_max_left _ _).trans hle)) ι p hp i hi`. Establish `hB` using `hb x hx ((le_max_right _ _).trans ((le_max_left _ _).trans hle)) ι p hp i hi Y hY`.

Establish `hW` using `hc x hx ((le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hle))) ι p hp i hi`. Establish `hF` using `hd x hx ((le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hle))) ι p hp i hi Y hY`. Establish `hLM` using `(he x ((le_max_right _ _).trans ((le_max_right _ _).trans hle)) ι).2.2.1`. Use `clear ha hb hc hd he`. Take `⟨h1p, h1q, hfin, -, hanti, -⟩` from `hA`.

Take `⟨hLaws, hInR, hL1, hM, hfs, hfr, -, -, h8f, h100r, hflat, hkap, hZ12, -, -, -, hsum, -⟩` from `hB`. Take `⟨hr, hdim, -⟩` from `GlobalTheory.RecGaps.gaps p (Fm.params x hx ι) i hi`. Introduce `Zc`. Use `set P : WtPar (dat p i) := ⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i (Fm.parT x hx ι).PP⟩ with hPdef`. Establish `hq : (dat p i).p - 1 + 1 < (dat p i).p + (dat p i).q` using `by omega`.

Establish `hg1 : ∀ τ, 1 ≤ gap (P.u₁ τ) ((dat p i).p - 1)` using `fun τ => one_le_gap_of_strictAnti (hanti τ).1 hq`. Establish `ha1 : ∀ τ, Antitone (P.u₁ τ)` using `fun τ => (hanti τ).1.antitone`. Establish `hgap2 : ∀ τ k, k + 1 < (dat p i).p + (dat p i).q → 1 ≤ gap (P.u₂ τ) k`. Introduce `τ k hk`. Establish `e : P.u₂ τ = P.u₁ τ + P.rem τ` using `rfl`.

Rewrite using `[e, gap_add]`. Use `one_le_gap_of_strictAnti (hanti τ).1 hk` as an intermediate fact. Use `(P.gap_rem τ k).1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `ha2 : ∀ τ, Antitone (P.u₂ τ)` using `fun τ => antitone_of_gap_nonneg fun k hk => (zero_lt_one.le).trans (hgap2 τ k hk)`.

Establish `hG` using `H0 (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) h1p h1q hfin hInR Y _ _ hY.1`. Use `⟨nonempty_cuspFrame ((hG P.u₂ ha2 fun τ => hgap2 τ _ hq).2 Zc), ?_⟩` and prove the remaining obligations. Establish `hgapBig : ∀ τ, ((8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 10 : ℕ) : ℤ) ≤ gap (P.u₁ τ) ((dat p i).p - 1)`. Introduce `τ`. Use `le_trans ?_ (hW.gaps τ ((dat p i).p - 1) hq)` and prove the remaining obligations.

Establish `h9 : 9 * (Fm.D x ι).R.r ≤ (Fm.D x ι).R.r.choose 2`. Rewrite using `[Nat.choose_two_right]`. Apply `(Nat.le_div_iff_mul_le two_pos).2` to reduce the goal to its premises. Establish `: 100 ≤ (Fm.D x ι).R.r` using `h100r`. Establish `: 99 ≤ (Fm.D x ι).R.r - 1` using `by omega`.

Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[hdim, hr]`. Generalize the expression as in `(Fm.D x ι).R.r.choose 2 = c at h9 ⊢`. Generalize the expression as in `((Fm.D x ι).R.f * c + 1).choose 2 = B`. Establish `h1 : 9 * (Fm.D x ι).R.f * (Fm.D x ι).R.r ≤ (Fm.D x ι).R.f * c`.

Rewrite using `[mul_assoc, mul_comm 9, mul_assoc, mul_comm (Fm.D x ι).R.r]`. Conclude with `Nat.mul_le_mul_left _ h9`. Establish `h2 : B + 4 * (Fm.D x ι).R.r + (Fm.D x ι).R.f * c + 3 ≤ ((Fm.D x ι).R.f * c + 3) * (B + 4 * (Fm.D x ι).R.r + (Fm.D x ι).R.f * c + 3)` using `Nat.le_mul_of_pos_left _ (by omega)`. Establish `h3 : 8 ≤ (Fm.D x ι).R.f` using `h8f`. Establish `h4 : 8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 10 ≤ 9 * (Fm.D x ι).R.f * (Fm.D x ι).R.r`.

Establish `: 10 ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `(h4.trans (h1.trans (by omega))).trans h2` after adjusting the coercions. Establish `hL1' : (1 : ℝ) ≤ (Fm.L x ι).sc.L` using `hL1`. Establish `hZdef : ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L = zBase (Fm.L x ι)` using `rfl`.

Establish `hf8 : (8 : ℝ) ≤ (Fm.D x ι).R.f` using `by exact_mod_cast h8f`. Establish `hr100 : (100 : ℝ) ≤ (Fm.D x ι).R.r` using `by exact_mod_cast h100r`. Establish `hfrpos : (0 : ℝ) < ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r` using `by positivity`. Establish `hE2 : (2 : ℝ) ≤ Real.exp (Fm.L x ι).sc.L` using `by linarith [Real.add_one_le_exp (Fm.L x ι).sc.L]`. Establish `hfrE : ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r ≤ Real.exp (Fm.L x ι).sc.L`.

Use `Real.exp_le_exp.2 hfr` as an intermediate fact. Rewrite `this` using `[Real.exp_log (by exact_mod_cast hfrpos)]`. Then use the resulting hypothesis. Establish `hLE : (Fm.L x ι).sc.L ≤ Real.exp (Fm.L x ι).sc.L` using `by linarith [Real.add_one_le_exp (Fm.L x ι).sc.L]`. Establish `hZE : zBase (Fm.L x ι) ≤ Real.exp (Fm.L x ι).sc.L ^ 2`. Rewrite using `[← hZdef, sq]; exact mul_le_mul hfrE hLE (by linarith) (Real.exp_pos _).le`.

Establish `hZL : (Fm.L x ι).sc.L ≤ zBase (Fm.L x ι)`. Rewrite using `[← hZdef]`. Establish `: (1 : ℝ) ≤ ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `hZ1 : (1 : ℝ) ≤ zBase (Fm.L x ι)` using `hL1'.trans hZL`.

Establish `hkap0 : 0 ≤ kap p i` using `by unfold CovTop.kap sizeK; positivity`. Establish `hkapE : kap p i ≤ Real.exp (Fm.L x ι).sc.L ^ 2`. Break down `hkap0.eq_or_lt with h0 | h0` into its components or cases. Rewrite using `[← h0]`. Check the signs of the components of the expression.

Use `Real.exp_le_exp.2 hkap` as an intermediate fact. Rewrite `this` using `[Real.exp_log h0]`. Rewrite using `[← Real.exp_nat_mul]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hK1 : (1 : ℝ) ≤ kap p i / lenT p i (Fm.parT x hx ι).PP + 1`. Establish `: 0 ≤ kap p i / lenT p i (Fm.parT x hx ι).PP` using `div_nonneg hkap0 (Nat.cast_nonneg _)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hKle : kap p i / lenT p i (Fm.parT x hx ι).PP ≤ kap p i`. Break down `Nat.eq_zero_or_pos (lenT p i (Fm.parT x hx ι).PP) with h0 | h0` into its components or cases.

Rewrite using `[h0]`. Simplify using `[hkap0]`. Conclude with `div_le_self hkap0 (by exact_mod_cast h0)`. Establish `hS` using `hsum P.u₁ (by simp)`. Establish `hS0 : 0 ≤ ∑ τ, ∑ k, |(P.u₁ τ k : ℝ)|` using `by positivity`.

Establish `hSE : ∑ τ, ∑ k, |(P.u₁ τ k : ℝ)| ≤ Real.exp (7 * (Fm.L x ι).sc.L)`. Establish `e7 : Real.exp (7 * (Fm.L x ι).sc.L) = Real.exp (Fm.L x ι).sc.L ^ 7`. Rewrite using `[← Real.exp_nat_mul]`. Evaluate the numerical expressions. Rewrite using `[e7]`.

Use `hS.trans ?_` and prove the remaining obligations. Establish `hZ2 : zBase (Fm.L x ι) ^ 2 ≤ Real.exp (Fm.L x ι).sc.L ^ 4`. Combine the equalities or inequalities in the displayed calculation. Establish `hK3 : kap p i / lenT p i (Fm.parT x hx ι).PP + 1 ≤ Real.exp (Fm.L x ι).sc.L ^ 3`. Use the polynomial consequences of the given equalities and inequalities.

Combine the equalities or inequalities in the displayed calculation. Establish `hlogS : Real.log (∑ τ, ∑ k, |(P.u₁ τ k : ℝ)|) ≤ 7 * (Fm.L x ι).sc.L`. Break down `hS0.eq_or_lt with h0 | h0` into its components or cases. Rewrite using `[← h0, Real.log_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `(Real.log_le_iff_le_exp h0).2 hSE`. Establish `ho : 391 * zBase (Fm.L x ι) ^ 2 ≤ 391 * (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) ^ 2`. Rewrite using `[hZdef]`. Establish `hc₁ : |-GlobalTheory.FlatLine.flatDegVal (dat p i) (Formalism.L2.DIV.ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| ≤ 9 * (Fm.D x ι).R.r * (Fm.L x ι).sc.L` using `by rw [abs_neg]; exact hflat`. Take `⟨n, w, abelian₂, hsg, hLam, hn⟩` from `H1 (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) h1p h1q hfin hInR Y _ _ hY.1 (Fm.L x ι).sc.L hL1 hM hfs hfr ho _ hF hc₁ P.u₁ ha1 hgapBig (by linarith) Zc`.

Take `⟨f, hfn, -, hfN⟩` from `exists_latFrame_of_isShortGen _ _ _ _ n w abelian₂ (nonempty_cuspFrame ((hG P.u₁ ha1 hg1).2 Zc)) hsg`. Establish `hb` using `(H2 (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) h1p h1q hfin hInR Y _ _ hY.1 (Fm.L x ι).sc.L hL1 hM hfs hfr ho P.u₁ ha1 (by linarith) Zc).1`. Rewrite `hLam`, `hn`, `hb` using `[hZdef]`. Establish `hMZ : 2 * C1 + C2 + 1 ≤ zBase (Fm.L x ι)` using `hLM.trans hZL`. Establish `hZ35 : zBase (Fm.L x ι) ^ 3 ≤ zBase (Fm.L x ι) ^ 5` using `pow_le_pow_right₀ hZ1 (by norm_num)`.

Establish `hZ612 : zBase (Fm.L x ι) ^ 6 ≤ zBase (Fm.L x ι) ^ 12` using `pow_le_pow_right₀ hZ1 (by norm_num)`. Establish `hZ5 : 0 ≤ zBase (Fm.L x ι) ^ 5` using `by positivity`. Establish `hkey : (2 * C1 + C2) * zBase (Fm.L x ι) ^ 5 ≤ zBase (Fm.L x ι) ^ 12`. Establish `: (2 * C1 + C2) * zBase (Fm.L x ι) ^ 5 ≤ zBase (Fm.L x ι) * zBase (Fm.L x ι) ^ 5` using `mul_le_mul_of_nonneg_right (by linarith) hZ5`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hPP0 : 0 ≤ (Fm.parT x hx ι).PP` using `le_trans (by positivity) hZ12`. Establish `hC1Z : C1 * zBase (Fm.L x ι) ^ 3 ≤ (Fm.parT x hx ι).PP` using `by nlinarith`. Establish `hC2Z : C2 * zBase (Fm.L x ι) ^ 3 ≤ (Fm.parT x hx ι).PP` using `by nlinarith`. Use `⟨f, max abelian₂ 1, Real.exp (C2 * zBase (Fm.L x ι) ^ 3), le_max_right _ _, Real.one_le_exp (by positivity), ?_, ?_, ?_, fun q σ => (hfN q σ).trans (le_max_left _ _), hb⟩` and prove the remaining obligations. Rewrite using `[hfn]`.

Conclude with `hn.trans hC1Z`. Rewrite using `[Real.log_exp]`. Conclude with `hC2Z`. Break down `le_total abelian₂ 1 with hl | hl` into its components or cases. Rewrite using `[max_eq_right hl, Real.log_one]`.

Check the signs of the components of the expression. Rewrite using `[max_eq_left hl]`. Use `hLam.trans ?_` and prove the remaining obligations. Establish `h3 : zBase (Fm.L x ι) ^ 3 * ∑ τ, ∑ k, |(P.u₁ τ k : ℝ)| ≤ zBase (Fm.L x ι) ^ 5 * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1)`. Use `mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ zBase (Fm.L x ι) ^ 3)` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Establish `h4 : C1 * (zBase (Fm.L x ι) ^ 3 * ∑ τ, ∑ k, |(P.u₁ τ k : ℝ)| + zBase (Fm.L x ι) ^ 5) ≤ (2 * C1 * zBase (Fm.L x ι) ^ 5) * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1)`. Establish `h6` using `mul_le_mul_of_nonneg_left h3 hC1`. Establish `h5 : C1 * zBase (Fm.L x ι) ^ 5 ≤ C1 * zBase (Fm.L x ι) ^ 5 * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1)` using `le_mul_of_one_le_right (by positivity) hK1`. Combine the linear relations using `[h6, h5]`.

Use `h4.trans (mul_le_mul_of_nonneg_right ?_ (by linarith))` and prove the remaining obligations. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem frames_short_berg : Hypotheses2 → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ Z, Nonempty (CuspFrame Z Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂) ∧ ∃ (f₁ : CuspFrame Z Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁) (Λ β : ℝ), 1 ≤ Λ ∧ 1 ≤ β ∧ Real.log f₁.n ≤ PP ∧ Real.log β ≤ PP ∧ Real.log Λ ≤ PP * (kap p i / lenT p i PP + 1) ∧ (∀ q σ, ChowHt.frameNorm (f₁.A σ) (fun a => σ (f₁.w.col q a)) ≤ Λ) ∧ BergLe Z Y.U (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ β := by
  intro hP2 _hDG hS hFD
  obtain ⟨C1, hC1, H1⟩ := GlobalTheory.T.flat_constant_abs_le_nine_explicit hP2
  obtain ⟨C2, hC2, H2⟩ := GlobalTheory.T.antitone_weight_log_bound hP2
  have H0 := GlobalTheory.T.good_weight_antitone_gap hP2
  refine (((GlobalTheory.T.weight_parameter_strict_antitone hS).and (GlobalTheory.T.size_bounds_for_family hS)).and (wtBig_run.and hFD)).imp fun Fm CH _ hh => ?_
  obtain ⟨⟨⟨_, _, a, ha⟩, ⟨_, _, b, hb⟩⟩, ⟨⟨_, _, c, hc⟩, ⟨_, _, d, hd⟩⟩⟩ := hh
  obtain ⟨e, he⟩ := GlobalTheory.family_sizes_eventually_large _ Fm (2 * C1 + C2 + 1)
  refine ⟨0, le_rfl, max (max a b) (max (max c d) e), fun x hx hle ι p hp i hi Y hY => ?_⟩
  have hA := ha x hx ((le_max_left _ _).trans ((le_max_left _ _).trans hle)) ι p hp i hi
  have hB := hb x hx ((le_max_right _ _).trans ((le_max_left _ _).trans hle)) ι p hp i hi Y hY
  have hW := hc x hx ((le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hle))) ι p hp i hi
  have hF := hd x hx ((le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hle))) ι p hp i hi Y hY
  have hLM := (he x ((le_max_right _ _).trans ((le_max_right _ _).trans hle)) ι).2.2.1
  clear ha hb hc hd he
  obtain ⟨h1p, h1q, hfin, -, hanti, -⟩ := hA
  obtain ⟨hLaws, hInR, hL1, hM, hfs, hfr, -, -, h8f, h100r, hflat, hkap, hZ12, -, -, -, hsum, -⟩ := hB
  obtain ⟨hr, hdim, -⟩ := GlobalTheory.RecGaps.gaps p (Fm.params x hx ι) i hi

  intro Zc
  set P : WtPar (dat p i) := ⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i (Fm.parT x hx ι).PP⟩ with hPdef
  have hq : (dat p i).p - 1 + 1 < (dat p i).p + (dat p i).q := by omega
  have hg1 : ∀ τ, 1 ≤ gap (P.u₁ τ) ((dat p i).p - 1) := fun τ => one_le_gap_of_strictAnti (hanti τ).1 hq
  have ha1 : ∀ τ, Antitone (P.u₁ τ) := fun τ => (hanti τ).1.antitone
  have hgap2 : ∀ τ k, k + 1 < (dat p i).p + (dat p i).q → 1 ≤ gap (P.u₂ τ) k := by
    intro τ k hk
    have e : P.u₂ τ = P.u₁ τ + P.rem τ := rfl
    rw [e, gap_add]
    have := one_le_gap_of_strictAnti (hanti τ).1 hk
    have := (P.gap_rem τ k).1
    omega
  have ha2 : ∀ τ, Antitone (P.u₂ τ) := fun τ =>
    antitone_of_gap_nonneg fun k hk => (zero_lt_one.le).trans (hgap2 τ k hk)
  have hG := H0 (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) h1p h1q hfin hInR Y _ _ hY.1
  refine ⟨nonempty_cuspFrame ((hG P.u₂ ha2 fun τ => hgap2 τ _ hq).2 Zc), ?_⟩

  have hgapBig : ∀ τ, ((8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 10 : ℕ) : ℤ) ≤ gap (P.u₁ τ) ((dat p i).p - 1) := by
    intro τ
    refine le_trans ?_ (hW.gaps τ ((dat p i).p - 1) hq)
    have h9 : 9 * (Fm.D x ι).R.r ≤ (Fm.D x ι).R.r.choose 2 := by
      rw [Nat.choose_two_right]
      apply (Nat.le_div_iff_mul_le two_pos).2
      have : 100 ≤ (Fm.D x ι).R.r := h100r
      have : 99 ≤ (Fm.D x ι).R.r - 1 := by omega
      nlinarith
    rw [hdim, hr]
    generalize (Fm.D x ι).R.r.choose 2 = c at h9 ⊢
    generalize ((Fm.D x ι).R.f * c + 1).choose 2 = B
    have h1 : 9 * (Fm.D x ι).R.f * (Fm.D x ι).R.r ≤ (Fm.D x ι).R.f * c := by
      rw [mul_assoc, mul_comm 9, mul_assoc, mul_comm (Fm.D x ι).R.r]; exact Nat.mul_le_mul_left _ h9
    have h2 : B + 4 * (Fm.D x ι).R.r + (Fm.D x ι).R.f * c + 3 ≤
        ((Fm.D x ι).R.f * c + 3) * (B + 4 * (Fm.D x ι).R.r + (Fm.D x ι).R.f * c + 3) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have h3 : 8 ≤ (Fm.D x ι).R.f := h8f
    have h4 : 8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 10 ≤ 9 * (Fm.D x ι).R.f * (Fm.D x ι).R.r := by
      have : 10 ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r := by nlinarith
      nlinarith
    exact_mod_cast (h4.trans (h1.trans (by omega))).trans h2

  have hL1' : (1 : ℝ) ≤ (Fm.L x ι).sc.L := hL1
  have hZdef : ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L = zBase (Fm.L x ι) := rfl
  have hf8 : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast h8f
  have hr100 : (100 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast h100r
  have hfrpos : (0 : ℝ) < ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r := by positivity
  have hE2 : (2 : ℝ) ≤ Real.exp (Fm.L x ι).sc.L := by linarith [Real.add_one_le_exp (Fm.L x ι).sc.L]
  have hfrE : ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r ≤ Real.exp (Fm.L x ι).sc.L := by
    have := Real.exp_le_exp.2 hfr
    rwa [Real.exp_log (by exact_mod_cast hfrpos)] at this
  have hLE : (Fm.L x ι).sc.L ≤ Real.exp (Fm.L x ι).sc.L := by linarith [Real.add_one_le_exp (Fm.L x ι).sc.L]
  have hZE : zBase (Fm.L x ι) ≤ Real.exp (Fm.L x ι).sc.L ^ 2 := by
    rw [← hZdef, sq]; exact mul_le_mul hfrE hLE (by linarith) (Real.exp_pos _).le
  have hZL : (Fm.L x ι).sc.L ≤ zBase (Fm.L x ι) := by
    rw [← hZdef]
    have : (1 : ℝ) ≤ ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r := by nlinarith
    nlinarith
  have hZ1 : (1 : ℝ) ≤ zBase (Fm.L x ι) := hL1'.trans hZL
  have hkap0 : 0 ≤ kap p i := by unfold CovTop.kap sizeK; positivity
  have hkapE : kap p i ≤ Real.exp (Fm.L x ι).sc.L ^ 2 := by
    rcases hkap0.eq_or_lt with h0 | h0
    · rw [← h0]; positivity
    · have := Real.exp_le_exp.2 hkap
      rw [Real.exp_log h0] at this
      rw [← Real.exp_nat_mul]; push_cast; linarith
  have hK1 : (1 : ℝ) ≤ kap p i / lenT p i (Fm.parT x hx ι).PP + 1 := by
    have : 0 ≤ kap p i / lenT p i (Fm.parT x hx ι).PP := div_nonneg hkap0 (Nat.cast_nonneg _)
    linarith
  have hKle : kap p i / lenT p i (Fm.parT x hx ι).PP ≤ kap p i := by
    rcases Nat.eq_zero_or_pos (lenT p i (Fm.parT x hx ι).PP) with h0 | h0
    · rw [h0]; simp [hkap0]
    · exact div_le_self hkap0 (by exact_mod_cast h0)
  have hS := hsum P.u₁ (by simp)
  have hS0 : 0 ≤ ∑ τ, ∑ k, |(P.u₁ τ k : ℝ)| := by positivity
  have hSE : ∑ τ, ∑ k, |(P.u₁ τ k : ℝ)| ≤ Real.exp (7 * (Fm.L x ι).sc.L) := by
    have e7 : Real.exp (7 * (Fm.L x ι).sc.L) = Real.exp (Fm.L x ι).sc.L ^ 7 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [e7]
    refine hS.trans ?_
    have hZ2 : zBase (Fm.L x ι) ^ 2 ≤ Real.exp (Fm.L x ι).sc.L ^ 4 := by
      calc zBase (Fm.L x ι) ^ 2 ≤ (Real.exp (Fm.L x ι).sc.L ^ 2) ^ 2 := pow_le_pow_left₀ (by linarith) hZE 2
        _ = _ := by ring
    have hK3 : kap p i / lenT p i (Fm.parT x hx ι).PP + 1 ≤ Real.exp (Fm.L x ι).sc.L ^ 3 := by
      nlinarith
    calc zBase (Fm.L x ι) ^ 2 * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1)
        ≤ Real.exp (Fm.L x ι).sc.L ^ 4 * Real.exp (Fm.L x ι).sc.L ^ 3 :=
          mul_le_mul hZ2 hK3 (by linarith) (by positivity)
      _ = _ := by ring
  have hlogS : Real.log (∑ τ, ∑ k, |(P.u₁ τ k : ℝ)|) ≤ 7 * (Fm.L x ι).sc.L := by
    rcases hS0.eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero]; linarith
    · exact (Real.log_le_iff_le_exp h0).2 hSE

  have ho : 391 * zBase (Fm.L x ι) ^ 2 ≤ 391 * (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) ^ 2 := by
    rw [hZdef]
  have hc₁ : |-GlobalTheory.FlatLine.flatDegVal (dat p i) (Formalism.L2.DIV.ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| ≤
      9 * (Fm.D x ι).R.r * (Fm.L x ι).sc.L := by rw [abs_neg]; exact hflat
  obtain ⟨n, w, abelian₂, hsg, hLam, hn⟩ := H1 (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) h1p h1q hfin hInR Y _ _ hY.1
    (Fm.L x ι).sc.L hL1 hM hfs hfr ho _ hF hc₁ P.u₁ ha1 hgapBig (by linarith) Zc
  obtain ⟨f, hfn, -, hfN⟩ := exists_latFrame_of_isShortGen _ _ _ _ n w abelian₂
    (nonempty_cuspFrame ((hG P.u₁ ha1 hg1).2 Zc)) hsg
  have hb := (H2 (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) h1p h1q hfin hInR Y _ _ hY.1
    (Fm.L x ι).sc.L hL1 hM hfs hfr ho P.u₁ ha1 (by linarith) Zc).1
  rw [hZdef] at hLam hn hb

  have hMZ : 2 * C1 + C2 + 1 ≤ zBase (Fm.L x ι) := hLM.trans hZL
  have hZ35 : zBase (Fm.L x ι) ^ 3 ≤ zBase (Fm.L x ι) ^ 5 := pow_le_pow_right₀ hZ1 (by norm_num)
  have hZ612 : zBase (Fm.L x ι) ^ 6 ≤ zBase (Fm.L x ι) ^ 12 := pow_le_pow_right₀ hZ1 (by norm_num)
  have hZ5 : 0 ≤ zBase (Fm.L x ι) ^ 5 := by positivity
  have hkey : (2 * C1 + C2) * zBase (Fm.L x ι) ^ 5 ≤ zBase (Fm.L x ι) ^ 12 := by
    have : (2 * C1 + C2) * zBase (Fm.L x ι) ^ 5 ≤ zBase (Fm.L x ι) * zBase (Fm.L x ι) ^ 5 :=
      mul_le_mul_of_nonneg_right (by linarith) hZ5
    nlinarith
  have hPP0 : 0 ≤ (Fm.parT x hx ι).PP := le_trans (by positivity) hZ12
  have hC1Z : C1 * zBase (Fm.L x ι) ^ 3 ≤ (Fm.parT x hx ι).PP := by nlinarith
  have hC2Z : C2 * zBase (Fm.L x ι) ^ 3 ≤ (Fm.parT x hx ι).PP := by nlinarith
  refine ⟨f, max abelian₂ 1, Real.exp (C2 * zBase (Fm.L x ι) ^ 3), le_max_right _ _,
    Real.one_le_exp (by positivity), ?_, ?_, ?_, fun q σ => (hfN q σ).trans (le_max_left _ _), hb⟩
  · rw [hfn]; exact hn.trans hC1Z
  · rw [Real.log_exp]; exact hC2Z
  · rcases le_total abelian₂ 1 with hl | hl
    · rw [max_eq_right hl, Real.log_one]; positivity
    · rw [max_eq_left hl]
      refine hLam.trans ?_
      have h3 : zBase (Fm.L x ι) ^ 3 * ∑ τ, ∑ k, |(P.u₁ τ k : ℝ)| ≤
          zBase (Fm.L x ι) ^ 5 * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1) := by
        have := mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ zBase (Fm.L x ι) ^ 3)
        nlinarith
      have h4 : C1 * (zBase (Fm.L x ι) ^ 3 * ∑ τ, ∑ k, |(P.u₁ τ k : ℝ)| + zBase (Fm.L x ι) ^ 5) ≤
          (2 * C1 * zBase (Fm.L x ι) ^ 5) * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1) := by
        have h6 := mul_le_mul_of_nonneg_left h3 hC1
        have h5 : C1 * zBase (Fm.L x ι) ^ 5 ≤ C1 * zBase (Fm.L x ι) ^ 5 * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1) :=
          le_mul_of_one_le_right (by positivity) hK1
        linarith [h6, h5]
      refine h4.trans (mul_le_mul_of_nonneg_right ?_ (by linarith))
      nlinarith

end GlobalTheory.FrameBerg
