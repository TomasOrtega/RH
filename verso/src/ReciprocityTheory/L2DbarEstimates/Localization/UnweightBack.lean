import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackA

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

/- English proof (translation)
Unfold `UnweightBackStatement`. Introduce `z hz ph ψ f w σ hph hψ hf hw hσ hfc hwc hσc hflat`. Unfold `FlatApprox at hflat`. Take `⟨K₀, hK₀, happ⟩` from `hflat`. Choose the witnesses or unpack the hypotheses as in `⟨K, hK, hout⟩ : ∃ K : Set M, IsCompact K ∧ ∀ x, x ∉ K → x ∉ K₀ ∧ f x = 0 ∧ w x = 0 ∧ σ x = 0 := by`.

Use `⟨K₀ ∪ (tsupport f ∪ (tsupport w ∪ tsupport σ)), hK₀.union (hfc.union (hwc.union hσc)), ?_⟩` and prove the remaining obligations. Introduce `x hx`. Simplify using `only [Set.mem_union, not_or] at hx`. Take `⟨h0, hf', hw', hσ'⟩` from `hx`. Use `⟨h0, ?_, ?_, ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `h`. Conclude with `hf' (subset_tsupport _ (Function.mem_support.mpr h))`. Assume the negation of the conclusion as `h`. Conclude with `hw' (subset_tsupport _ (Function.mem_support.mpr h))`. Assume the negation of the conclusion as `h`.

Conclude with `hσ' (subset_tsupport _ (Function.mem_support.mpr h))`. Establish `hphc : Continuous ph` using `unwBack_contR n z hz ph hph`. Establish `hψc : Continuous ψ` using `unwBack_contR n z hz ψ hψ`. Establish `hw2c : Continuous (w2 ph ψ)` using `by show Continuous (fun x => ph x - ψ x); exact hphc.sub hψc`. Establish `hw1c : Continuous (w1 ph ψ)` using `by show Continuous (fun x => ph x - 2 * ψ x); exact hphc.sub (continuous_const.mul hψc)`.

Establish `hw2s : Smooth n z (fun y => ((w2 ph ψ y : ℝ) : ℂ))` using `smooth_ofReal_secondWeight n z ph ψ hph hψ`. Establish `hE : Smooth n z (fun y => (Real.exp (w2 ph ψ y) : ℂ))` using `unwBack_smooth_exp n z (w2 ph ψ) hw2s`. Establish `hE1 : Ck n z 1 (fun y => (Real.exp (w2 ph ψ y) : ℂ))` using `Smooth.ck n z 1 _ hE`. Establish `hW1 : Ck n z 1 (fun y => ((w2 ph ψ y : ℝ) : ℂ))` using `Smooth.ck n z 1 _ hw2s`. Establish `hdbc : ∀ j, Continuous (db n z j (fun y => ((w2 ph ψ y : ℝ) : ℂ)))` using `fun j => Smooth.continuous n z hz _ (Smooth.db n z j _ hw2s)`.

Establish `hFc : Continuous (fun x => Real.exp (w2 ph ψ x) + Real.exp (w1 ph ψ x) + Real.exp (w1 ph ψ x) * (2 + 4 * ∑ j, ‖db n z j (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x‖ ^ 2))` using `by first`. Consider the case `exact ((Real.continuous_exp.comp hw2c).add (Real.continuous_exp.comp hw1c)).add ((Real.continuous_exp.comp hw1c).mul (continuous_const.add (continuous_const.mul (continuous_finset_sum _ (fun j _ => ((hdbc j).norm.pow 2))))))`. Consider the case `fun_prop`. Take `⟨C, hC, hCK⟩` from `unwBack_bound K hK _ hFc`. Establish `hbd : ∀ x ∈ K, Real.exp (w2 ph ψ x) ≤ C ∧ Real.exp (w1 ph ψ x) ≤ C ∧ Real.exp (w1 ph ψ x) * (2 + 4 * ∑ j, ‖db n z j (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x‖ ^ 2) ≤ C`.

Introduce `x hx`. Establish `h` using `hCK x hx`. Apply the tactic sequence `try dsimp only at h`. Establish `p1` using `Real.exp_pos (w2 ph ψ x)`. Establish `p2` using `Real.exp_pos (w1 ph ψ x)`.

Establish `p3 : 0 ≤ Real.exp (w1 ph ψ x) * (2 + 4 * ∑ j, ‖db n z j (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x‖ ^ 2)` using `by positivity`. Conclude with `⟨by linarith, by linarith, by linarith⟩`. Establish `hinv : ∀ a : ℝ, (Real.exp (-a) : ℂ) * (Real.exp a : ℂ) = 1`. Introduce `a`. Rewrite using `[← Complex.ofReal_mul, ← Real.exp_add]`.

Simplify using the standard rewrite rules. Establish `hinv' : ∀ a : ℝ, (Real.exp a : ℂ) * (Real.exp (-a) : ℂ) = 1`. Introduce `a`. Rewrite using `[mul_comm]`. Conclude with `hinv a`.

Establish `hsq2 : ∀ s : Fin n → Fin n → ℂ, 0 ≤ sq2 n s` using `fun s => by unfold sq2; positivity`. Establish `hEexp : (fun y => (Real.exp (w2 ph ψ y) : ℂ)) = fun y => Complex.exp ((w2 ph ψ y : ℝ) : ℂ)`. Use function extensionality and compare the values at `fun y => Complex.ofReal_exp _`. Establish `hdbE : ∀ i x, db n z i (fun y => (Real.exp (w2 ph ψ y) : ℂ)) x = (Real.exp (w2 ph ψ x) : ℂ) * db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x`. Introduce `i x`.

Rewrite using `[hEexp, db_cexp n z _ hW1 i x, Complex.ofReal_exp]`. Establish `hEm : Continuous (fun x => (Real.exp (-w2 ph ψ x) : ℂ))` using `Complex.continuous_ofReal.comp (Real.continuous_exp.comp hw2c.neg)`. Unfold `GraphApprox`. Introduce `δ hδ`. Take `⟨δ', hδ', hsmall⟩` from `unwBack_small δ hδ C hC`.

Take `⟨g, hg, hg0, h1, h2, h3⟩` from `happ δ' hδ'`. Establish `hg1 : ∀ l, Ck n z 1 (fun y => g y l)` using `fun l => Ck.mono n z 1 2 (by norm_num) _ (hg l).1`. Establish `hgcj : ∀ l, Continuous (fun y => g y l)` using `fun l => Ck.continuous n z hz 2 _ (hg l).1`. Establish `hgc : Continuous g` using `by first`. Consider the case `exact continuous_induced_rng.2 (continuous_pi hgcj)`.

Consider the case `exact (PiLp.continuous_toLp 2 _).comp (continuous_pi hgcj)`. Consider the case `exact (PiLp.continuous_equiv_symm 2 _).comp (continuous_pi hgcj)`. Consider the case `exact continuous_pi hgcj`. Consider the case `exact (EuclideanSpace.equiv (Fin n) ℂ).symm.continuous.comp (continuous_pi hgcj)`. Establish `hBs : AEStronglyMeasurable (fun x => g x - unwG ph ψ f x) (vol n z)` using `hgc.aestronglyMeasurable.sub (hEm.aestronglyMeasurable.smul hf.1)`.

Establish `hBm : AEMeasurable (fun x => ENNReal.ofReal (‖g x - unwG ph ψ f x‖ ^ 2)) (vol n z)` using `ENNReal.measurable_ofReal.comp_aemeasurable (hBs.norm.aemeasurable.pow_const 2)`. Take `⟨g', hg'v⟩ : ∃ g' : M → V n, ∀ y, g' y = (Real.exp (w2 ph ψ y) : ℂ) • g y` from `⟨fun y => (Real.exp (w2 ph ψ y) : ℂ) • g y, fun y => rfl⟩`. Establish `hg'c : ∀ y j, g' y j = (Real.exp (w2 ph ψ y) : ℂ) * g y j`. Introduce `y j`. Rewrite using `[hg'v y]`.

Apply the tactic sequence `first | rfl | simp [PiLp.smul_apply] | simp`. Establish `hg'f : ∀ l, (fun y => g' y l) = fun y => (Real.exp (w2 ph ψ y) : ℂ) * g y l` using `fun l => funext fun y => hg'c y l`. Establish `hdiv0 : ∀ x, x ∉ K₀ → divF n z g x = 0`. Introduce `x hx`. Unfold `divF`.

Conclude with `Finset.sum_eq_zero (fun j _ => (unwBack_off n z K₀ hK₀ (fun y => g y j) (fun y hy => by simp [hg0 y hy]) x hx j).1)`. Establish `hu : ∀ l y, y ∉ K₀ → g' y l = 0`. Introduce `l y hy`. Rewrite using `[hg'c y l, hg0 y hy]`. Simplify using the standard rewrite rules.

Establish `hsb0 : ∀ x, x ∉ K₀ → sbar n z g' x = 0`. Introduce `x hx`. Use function extensionality and compare the values at `j k`. Simplify using `only [sbar, Pi.zero_apply]`. Rewrite using `[(unwBack_off n z K₀ hK₀ (fun y => g' y k) (hu k) x hx j).2, (unwBack_off n z K₀ hK₀ (fun y => g' y j) (hu j) x hx k).2, sub_zero]`.

Establish `hid1 : ∀ x, g' x - f x = (Real.exp (w2 ph ψ x) : ℂ) • (g x - unwG ph ψ f x)`. Introduce `x`. Rewrite using `[smul_sub, ← hg'v x]`. Simplify using `only [unwG]`. Rewrite using `[smul_smul, hinv' (w2 ph ψ x), one_smul]`.

Establish `hfun : ∀ j, (fun y => (Real.exp (-w2 ph ψ y) : ℂ) * g' y j) = fun y => g y j`. Introduce `j`. Use function extensionality and compare the values at `y`. Rewrite using `[hg'c y j, ← mul_assoc, hinv, one_mul]`. Establish `htid : ∀ x, tstar n z (w1 ph ψ) (w2 ph ψ) g' x - w x = -((Real.exp (w1 ph ψ x) : ℂ) * (divF n z g x - unwD ph ψ w x))`.

Introduce `x`. Establish `hsum : ∑ j, d n z j (fun y => (Real.exp (-w2 ph ψ y) : ℂ) * g' y j) x = divF n z g x`. Unfold `divF`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[hfun j]`.

Simplify using `only [tstar]`. Rewrite using `[hsum]`. Simplify using `only [unwD]`. Take the linear combination `(w x) * hinv (w1 ph ψ x)`. Establish `hsb : ∀ x j k, sbar n z g' x j k = (Real.exp (w2 ph ψ x) : ℂ) * sbar n z g x j k + (Real.exp (w2 ph ψ x) : ℂ) * wedge (fun i => db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x) (fun i => g x i) j k`.

Introduce `x j k`. Establish `hm : ∀ i l, db n z i (fun y => g' y l) x = (Real.exp (w2 ph ψ x) : ℂ) * db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x * g x l + (Real.exp (w2 ph ψ x) : ℂ) * db n z i (fun y => g y l) x`. Introduce `i l`. Rewrite using `[hg'f l, db_mul n z _ _ hE1 (hg1 l) i x, hdbE i x]`. Simplify using `only [sbar, wedge]`.

Rewrite using `[hm j k, hm k j]`. Expand and normalize the polynomial expressions, which then agree. Establish `hid : ∀ x, sbar n z g' x - σ x = fun j k => (Real.exp (w2 ph ψ x) : ℂ) * (sbar n z g x - unwS n z ph ψ f σ x) j k + (Real.exp (w2 ph ψ x) : ℂ) * wedge (fun i => db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x) (fun i => (g x - unwG ph ψ f x) i) j k`. Introduce `x`. Use function extensionality and compare the values at `j k`.

Simplify using `only [Pi.sub_apply]`. Rewrite using `[hsb x j k]`. Simplify using `only [unwS, unwG, wedge, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]`. Take the linear combination `(σ x j k) * hinv (w2 ph ψ x)`. Use `⟨g', ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Unfold `IsTestForm`. Introduce `j`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hg'f j]`. Conclude with `Ck.mul n z 2 _ _ (Smooth.ck n z 2 _ hE) (hg j).1`.

Rewrite using `[hg'f j] first`. Consider the case `exact (hg j).2.mul_left`. Consider the case `exact HasCompactSupport.mul_left (hg j).2`. Establish `hle : nV n z (fun x => g' x - f x) (w2 ph ψ) ≤ ENNReal.ofReal C * nV n z (fun x => g x - unwG ph ψ f x) (fun _ => 0)`. Unfold `nV`.

Use `unwBack_lint (vol n z) _ _ C hC ?_` and prove the remaining obligations. Introduce `x`. Simplify using `only [neg_zero, Real.exp_zero, mul_one]`. Rewrite using `[hid1 x, norm_smul, unwBack_norm_exp]`. Distinguish the cases in `hx : x ∈ K`.

Rewrite using `[show ∀ a b c : ℝ, (a * b) ^ 2 * c = (a ^ 2 * c) * b ^ 2 from fun a b c => by ring, unwBack_exp_sq]`. Conclude with `mul_le_mul_of_nonneg_right (hbd x hx).1 (sq_nonneg _)`. Take `⟨h0, hfx, -, -⟩` from `hout x hx`. Simplify using `[unwG, hg0 x h0, hfx]`. Establish `hs` using `hsmall _ 0 h1 hδ'`.

Rewrite `hs` using `[add_zero]`. Conclude with `lt_of_le_of_lt hle hs`. Establish `hle : wint n z (fun x => tstar n z (w1 ph ψ) (w2 ph ψ) g' x - w x) (w1 ph ψ) ≤ ENNReal.ofReal C * wint n z (fun x => divF n z g x - unwD ph ψ w x) (fun _ => 0)`. Unfold `wint`. Use `unwBack_lint (vol n z) _ _ C hC ?_` and prove the remaining obligations.

Introduce `x`. Simplify using `only [neg_zero, Real.exp_zero, mul_one]`. Rewrite using `[htid x, norm_neg, norm_mul, unwBack_norm_exp]`. Distinguish the cases in `hx : x ∈ K`. Rewrite using `[show ∀ a b c : ℝ, (a * b) ^ 2 * c = (a ^ 2 * c) * b ^ 2 from fun a b c => by ring, unwBack_exp_sq]`.

Conclude with `mul_le_mul_of_nonneg_right (hbd x hx).2.1 (sq_nonneg _)`. Take `⟨h0, -, hwx, -⟩` from `hout x hx`. Rewrite using `[hdiv0 x h0]`. Simplify using `[unwD, hwx]`. Establish `hs` using `hsmall _ 0 h2 hδ'`.

Rewrite `hs` using `[add_zero]`. Conclude with `lt_of_le_of_lt hle hs`. Establish `hle : n2 n z (fun x => sbar n z g' x - σ x) ph ≤ ENNReal.ofReal C * (n2 n z (fun x => sbar n z g x - unwS n z ph ψ f σ x) (fun _ => 0) + nV n z (fun x => g x - unwG ph ψ f x) (fun _ => 0))`. Establish `e1 : n2 n z (fun x => sbar n z g x - unwS n z ph ψ f σ x) (fun _ => 0) = ∫⁻ x, ENNReal.ofReal (sq2 n (sbar n z g x - unwS n z ph ψ f σ x)) ∂vol n z`. Unfold `n2`.

Simplify using `only [neg_zero, Real.exp_zero, mul_one]`. Establish `e2 : nV n z (fun x => g x - unwG ph ψ f x) (fun _ => 0) = ∫⁻ x, ENNReal.ofReal (‖g x - unwG ph ψ f x‖ ^ 2) ∂vol n z`. Unfold `nV`. Simplify using `only [neg_zero, Real.exp_zero, mul_one]`. Rewrite using `[e1, e2]`.

Unfold `n2`. Use `unwBack_lint2 (vol n z) _ (fun x => sq2 n (sbar n z g x - unwS n z ph ψ f σ x)) (fun x => ‖g x - unwG ph ψ f x‖ ^ 2) C hC (fun x => hsq2 _) (fun x => sq_nonneg _) hBm ?_` and prove the remaining obligations. Introduce `x`. Simplify using `only`. Distinguish the cases in `hx : x ∈ K`.

Rewrite using `[hid x]`. Establish `hs` using `sqNorm_wedge_twist_le (n := n) ((Real.exp (w2 ph ψ x) : ℂ)) (sbar n z g x - unwS n z ph ψ f σ x) (fun i => db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x) (g x - unwG ph ψ f x)`. Rewrite `hs` using `[unwBack_norm_exp]`. Establish `hexp : Real.exp (w2 ph ψ x) ^ 2 * Real.exp (-ph x) = Real.exp (w1 ph ψ x)`. Rewrite using `[sq, ← Real.exp_add, ← Real.exp_add]`.

Use `congr 1`. Simplify using `only [w1, w2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hAB : 0 ≤ sq2 n (sbar n z g x - unwS n z ph ψ f σ x) + ‖g x - unwG ph ψ f x‖ ^ 2` using `add_nonneg (hsq2 _) (sq_nonneg _)`. Use `le_trans (mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le) ?_` and prove the remaining obligations.

Rewrite using `[show ∀ a b c e : ℝ, a ^ 2 * b * c * e = (a ^ 2 * e * b) * c from fun a b c e => by ring, hexp]`. Conclude with `mul_le_mul_of_nonneg_right (hbd x hx).2.2 hAB`. Take `⟨h0, -, -, hσx⟩` from `hout x hx`. Rewrite using `[hsb0 x h0, hσx, sub_zero]`. Establish `hz0 : sq2 n 0 = 0` using `by simp [sq2]`.

Rewrite using `[hz0, zero_mul]`. Conclude with `mul_nonneg hC (add_nonneg (hsq2 _) (sq_nonneg _))`. Conclude with `lt_of_le_of_lt hle (hsmall _ _ h3 h1)`.
-/
theorem unweightBack (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : UnweightBackStatement n M := by
  unfold UnweightBackStatement
  intro z hz ph ψ f w σ hph hψ hf hw hσ hfc hwc hσc hflat
  unfold FlatApprox at hflat
  obtain ⟨K₀, hK₀, happ⟩ := hflat

  obtain ⟨K, hK, hout⟩ : ∃ K : Set M, IsCompact K ∧
      ∀ x, x ∉ K → x ∉ K₀ ∧ f x = 0 ∧ w x = 0 ∧ σ x = 0 := by
    refine ⟨K₀ ∪ (tsupport f ∪ (tsupport w ∪ tsupport σ)), hK₀.union (hfc.union (hwc.union hσc)), ?_⟩
    intro x hx
    simp only [Set.mem_union, not_or] at hx
    obtain ⟨h0, hf', hw', hσ'⟩ := hx
    refine ⟨h0, ?_, ?_, ?_⟩
    · by_contra h; exact hf' (subset_tsupport _ (Function.mem_support.mpr h))
    · by_contra h; exact hw' (subset_tsupport _ (Function.mem_support.mpr h))
    · by_contra h; exact hσ' (subset_tsupport _ (Function.mem_support.mpr h))
  have hphc : Continuous ph := unwBack_contR n z hz ph hph
  have hψc : Continuous ψ := unwBack_contR n z hz ψ hψ
  have hw2c : Continuous (w2 ph ψ) := by
    show Continuous (fun x => ph x - ψ x); exact hphc.sub hψc
  have hw1c : Continuous (w1 ph ψ) := by
    show Continuous (fun x => ph x - 2 * ψ x); exact hphc.sub (continuous_const.mul hψc)
  have hw2s : Smooth n z (fun y => ((w2 ph ψ y : ℝ) : ℂ)) := smooth_ofReal_secondWeight n z ph ψ hph hψ
  have hE : Smooth n z (fun y => (Real.exp (w2 ph ψ y) : ℂ)) := unwBack_smooth_exp n z (w2 ph ψ) hw2s
  have hE1 : Ck n z 1 (fun y => (Real.exp (w2 ph ψ y) : ℂ)) := Smooth.ck n z 1 _ hE
  have hW1 : Ck n z 1 (fun y => ((w2 ph ψ y : ℝ) : ℂ)) := Smooth.ck n z 1 _ hw2s
  have hdbc : ∀ j, Continuous (db n z j (fun y => ((w2 ph ψ y : ℝ) : ℂ))) := fun j =>
    Smooth.continuous n z hz _ (Smooth.db n z j _ hw2s)
  have hFc : Continuous (fun x => Real.exp (w2 ph ψ x) + Real.exp (w1 ph ψ x) +
      Real.exp (w1 ph ψ x) * (2 + 4 * ∑ j, ‖db n z j (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x‖ ^ 2)) := by
    first
    | exact ((Real.continuous_exp.comp hw2c).add (Real.continuous_exp.comp hw1c)).add
        ((Real.continuous_exp.comp hw1c).mul (continuous_const.add (continuous_const.mul
          (continuous_finset_sum _ (fun j _ => ((hdbc j).norm.pow 2))))))
    | fun_prop
  obtain ⟨C, hC, hCK⟩ := unwBack_bound K hK _ hFc
  have hbd : ∀ x ∈ K, Real.exp (w2 ph ψ x) ≤ C ∧ Real.exp (w1 ph ψ x) ≤ C ∧
      Real.exp (w1 ph ψ x) * (2 + 4 * ∑ j, ‖db n z j (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x‖ ^ 2) ≤ C := by
    intro x hx
    have h := hCK x hx
    try dsimp only at h
    have p1 := Real.exp_pos (w2 ph ψ x)
    have p2 := Real.exp_pos (w1 ph ψ x)
    have p3 : 0 ≤ Real.exp (w1 ph ψ x) *
        (2 + 4 * ∑ j, ‖db n z j (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x‖ ^ 2) := by positivity
    exact ⟨by linarith, by linarith, by linarith⟩
  have hinv : ∀ a : ℝ, (Real.exp (-a) : ℂ) * (Real.exp a : ℂ) = 1 := by
    intro a; rw [← Complex.ofReal_mul, ← Real.exp_add]; simp
  have hinv' : ∀ a : ℝ, (Real.exp a : ℂ) * (Real.exp (-a) : ℂ) = 1 := by
    intro a; rw [mul_comm]; exact hinv a
  have hsq2 : ∀ s : Fin n → Fin n → ℂ, 0 ≤ sq2 n s := fun s => by unfold sq2; positivity
  have hEexp : (fun y => (Real.exp (w2 ph ψ y) : ℂ)) = fun y => Complex.exp ((w2 ph ψ y : ℝ) : ℂ) :=
    funext fun y => Complex.ofReal_exp _
  have hdbE : ∀ i x, db n z i (fun y => (Real.exp (w2 ph ψ y) : ℂ)) x =
      (Real.exp (w2 ph ψ x) : ℂ) * db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x := by
    intro i x
    rw [hEexp, db_cexp n z _ hW1 i x, Complex.ofReal_exp]
  have hEm : Continuous (fun x => (Real.exp (-w2 ph ψ x) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp hw2c.neg)
  unfold GraphApprox
  intro δ hδ
  obtain ⟨δ', hδ', hsmall⟩ := unwBack_small δ hδ C hC
  obtain ⟨g, hg, hg0, h1, h2, h3⟩ := happ δ' hδ'
  have hg1 : ∀ l, Ck n z 1 (fun y => g y l) := fun l => Ck.mono n z 1 2 (by norm_num) _ (hg l).1
  have hgcj : ∀ l, Continuous (fun y => g y l) := fun l => Ck.continuous n z hz 2 _ (hg l).1
  have hgc : Continuous g := by
    first
    | exact continuous_induced_rng.2 (continuous_pi hgcj)
    | exact (PiLp.continuous_toLp 2 _).comp (continuous_pi hgcj)
    | exact (PiLp.continuous_equiv_symm 2 _).comp (continuous_pi hgcj)
    | exact continuous_pi hgcj
    | exact (EuclideanSpace.equiv (Fin n) ℂ).symm.continuous.comp (continuous_pi hgcj)
  have hBs : AEStronglyMeasurable (fun x => g x - unwG ph ψ f x) (vol n z) :=
    hgc.aestronglyMeasurable.sub (hEm.aestronglyMeasurable.smul hf.1)
  have hBm : AEMeasurable (fun x => ENNReal.ofReal (‖g x - unwG ph ψ f x‖ ^ 2)) (vol n z) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hBs.norm.aemeasurable.pow_const 2)

  obtain ⟨g', hg'v⟩ : ∃ g' : M → V n, ∀ y, g' y = (Real.exp (w2 ph ψ y) : ℂ) • g y :=
    ⟨fun y => (Real.exp (w2 ph ψ y) : ℂ) • g y, fun y => rfl⟩
  have hg'c : ∀ y j, g' y j = (Real.exp (w2 ph ψ y) : ℂ) * g y j := by
    intro y j; rw [hg'v y]
    first | rfl | simp [PiLp.smul_apply] | simp
  have hg'f : ∀ l, (fun y => g' y l) = fun y => (Real.exp (w2 ph ψ y) : ℂ) * g y l :=
    fun l => funext fun y => hg'c y l
  have hdiv0 : ∀ x, x ∉ K₀ → divF n z g x = 0 := by
    intro x hx; unfold divF
    exact Finset.sum_eq_zero (fun j _ =>
      (unwBack_off n z K₀ hK₀ (fun y => g y j) (fun y hy => by simp [hg0 y hy]) x hx j).1)
  have hu : ∀ l y, y ∉ K₀ → g' y l = 0 := by
    intro l y hy; rw [hg'c y l, hg0 y hy]; simp
  have hsb0 : ∀ x, x ∉ K₀ → sbar n z g' x = 0 := by
    intro x hx
    funext j k
    simp only [sbar, Pi.zero_apply]
    rw [(unwBack_off n z K₀ hK₀ (fun y => g' y k) (hu k) x hx j).2,
      (unwBack_off n z K₀ hK₀ (fun y => g' y j) (hu j) x hx k).2, sub_zero]
  have hid1 : ∀ x, g' x - f x = (Real.exp (w2 ph ψ x) : ℂ) • (g x - unwG ph ψ f x) := by
    intro x
    rw [smul_sub, ← hg'v x]
    simp only [unwG]
    rw [smul_smul, hinv' (w2 ph ψ x), one_smul]
  have hfun : ∀ j, (fun y => (Real.exp (-w2 ph ψ y) : ℂ) * g' y j) = fun y => g y j := by
    intro j; funext y
    rw [hg'c y j, ← mul_assoc, hinv, one_mul]
  have htid : ∀ x, tstar n z (w1 ph ψ) (w2 ph ψ) g' x - w x =
      -((Real.exp (w1 ph ψ x) : ℂ) * (divF n z g x - unwD ph ψ w x)) := by
    intro x
    have hsum : ∑ j, d n z j (fun y => (Real.exp (-w2 ph ψ y) : ℂ) * g' y j) x = divF n z g x := by
      unfold divF
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hfun j]
    simp only [tstar]
    rw [hsum]
    simp only [unwD]
    linear_combination (w x) * hinv (w1 ph ψ x)
  have hsb : ∀ x j k, sbar n z g' x j k = (Real.exp (w2 ph ψ x) : ℂ) * sbar n z g x j k +
      (Real.exp (w2 ph ψ x) : ℂ) *
        wedge (fun i => db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x) (fun i => g x i) j k := by
    intro x j k
    have hm : ∀ i l, db n z i (fun y => g' y l) x =
        (Real.exp (w2 ph ψ x) : ℂ) * db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x * g x l +
          (Real.exp (w2 ph ψ x) : ℂ) * db n z i (fun y => g y l) x := by
      intro i l
      rw [hg'f l, db_mul n z _ _ hE1 (hg1 l) i x, hdbE i x]
    simp only [sbar, wedge]
    rw [hm j k, hm k j]
    ring
  have hid : ∀ x, sbar n z g' x - σ x = fun j k =>
      (Real.exp (w2 ph ψ x) : ℂ) * (sbar n z g x - unwS n z ph ψ f σ x) j k +
        (Real.exp (w2 ph ψ x) : ℂ) * wedge (fun i => db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x)
          (fun i => (g x - unwG ph ψ f x) i) j k := by
    intro x; funext j k
    simp only [Pi.sub_apply]
    rw [hsb x j k]
    simp only [unwS, unwG, wedge, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    linear_combination (σ x j k) * hinv (w2 ph ψ x)
  refine ⟨g', ?_, ?_, ?_, ?_⟩
  ·
    unfold IsTestForm
    intro j
    refine ⟨?_, ?_⟩
    · rw [hg'f j]; exact Ck.mul n z 2 _ _ (Smooth.ck n z 2 _ hE) (hg j).1
    · rw [hg'f j]
      first
      | exact (hg j).2.mul_left
      | exact HasCompactSupport.mul_left (hg j).2
  · have hle : nV n z (fun x => g' x - f x) (w2 ph ψ) ≤
        ENNReal.ofReal C * nV n z (fun x => g x - unwG ph ψ f x) (fun _ => 0) := by
      unfold nV
      refine unwBack_lint (vol n z) _ _ C hC ?_
      intro x
      simp only [neg_zero, Real.exp_zero, mul_one]
      rw [hid1 x, norm_smul, unwBack_norm_exp]
      by_cases hx : x ∈ K
      · rw [show ∀ a b c : ℝ, (a * b) ^ 2 * c = (a ^ 2 * c) * b ^ 2 from fun a b c => by ring,
          unwBack_exp_sq]
        exact mul_le_mul_of_nonneg_right (hbd x hx).1 (sq_nonneg _)
      · obtain ⟨h0, hfx, -, -⟩ := hout x hx
        simp [unwG, hg0 x h0, hfx]
    have hs := hsmall _ 0 h1 hδ'
    rw [add_zero] at hs
    exact lt_of_le_of_lt hle hs
  · have hle : wint n z (fun x => tstar n z (w1 ph ψ) (w2 ph ψ) g' x - w x) (w1 ph ψ) ≤
        ENNReal.ofReal C * wint n z (fun x => divF n z g x - unwD ph ψ w x) (fun _ => 0) := by
      unfold wint
      refine unwBack_lint (vol n z) _ _ C hC ?_
      intro x
      simp only [neg_zero, Real.exp_zero, mul_one]
      rw [htid x, norm_neg, norm_mul, unwBack_norm_exp]
      by_cases hx : x ∈ K
      · rw [show ∀ a b c : ℝ, (a * b) ^ 2 * c = (a ^ 2 * c) * b ^ 2 from fun a b c => by ring,
          unwBack_exp_sq]
        exact mul_le_mul_of_nonneg_right (hbd x hx).2.1 (sq_nonneg _)
      · obtain ⟨h0, -, hwx, -⟩ := hout x hx
        rw [hdiv0 x h0]
        simp [unwD, hwx]
    have hs := hsmall _ 0 h2 hδ'
    rw [add_zero] at hs
    exact lt_of_le_of_lt hle hs
  · have hle : n2 n z (fun x => sbar n z g' x - σ x) ph ≤
        ENNReal.ofReal C * (n2 n z (fun x => sbar n z g x - unwS n z ph ψ f σ x) (fun _ => 0) +
          nV n z (fun x => g x - unwG ph ψ f x) (fun _ => 0)) := by
      have e1 : n2 n z (fun x => sbar n z g x - unwS n z ph ψ f σ x) (fun _ => 0) =
          ∫⁻ x, ENNReal.ofReal (sq2 n (sbar n z g x - unwS n z ph ψ f σ x)) ∂vol n z := by
        unfold n2; simp only [neg_zero, Real.exp_zero, mul_one]
      have e2 : nV n z (fun x => g x - unwG ph ψ f x) (fun _ => 0) =
          ∫⁻ x, ENNReal.ofReal (‖g x - unwG ph ψ f x‖ ^ 2) ∂vol n z := by
        unfold nV; simp only [neg_zero, Real.exp_zero, mul_one]
      rw [e1, e2]
      unfold n2
      refine unwBack_lint2 (vol n z) _ (fun x => sq2 n (sbar n z g x - unwS n z ph ψ f σ x))
        (fun x => ‖g x - unwG ph ψ f x‖ ^ 2) C hC (fun x => hsq2 _) (fun x => sq_nonneg _) hBm ?_
      intro x
      dsimp only
      by_cases hx : x ∈ K
      · rw [hid x]
        have hs := sqNorm_wedge_twist_le (n := n) ((Real.exp (w2 ph ψ x) : ℂ))
          (sbar n z g x - unwS n z ph ψ f σ x) (fun i => db n z i (fun y => ((w2 ph ψ y : ℝ) : ℂ)) x)
          (g x - unwG ph ψ f x)
        rw [unwBack_norm_exp] at hs
        have hexp : Real.exp (w2 ph ψ x) ^ 2 * Real.exp (-ph x) = Real.exp (w1 ph ψ x) := by
          rw [sq, ← Real.exp_add, ← Real.exp_add]
          congr 1
          simp only [w1, w2]
          ring
        have hAB : 0 ≤ sq2 n (sbar n z g x - unwS n z ph ψ f σ x) + ‖g x - unwG ph ψ f x‖ ^ 2 :=
          add_nonneg (hsq2 _) (sq_nonneg _)
        refine le_trans (mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le) ?_
        rw [show ∀ a b c e : ℝ, a ^ 2 * b * c * e = (a ^ 2 * e * b) * c from
          fun a b c e => by ring, hexp]
        exact mul_le_mul_of_nonneg_right (hbd x hx).2.2 hAB
      · obtain ⟨h0, -, -, hσx⟩ := hout x hx
        rw [hsb0 x h0, hσx, sub_zero]
        have hz0 : sq2 n 0 = 0 := by simp [sq2]
        rw [hz0, zero_mul]
        exact mul_nonneg hC (add_nonneg (hsq2 _) (sq_nonneg _))
    exact lt_of_le_of_lt hle (hsmall _ _ h3 h1)

end

end ReciprocityTheory.L2DbarEstimates.F
