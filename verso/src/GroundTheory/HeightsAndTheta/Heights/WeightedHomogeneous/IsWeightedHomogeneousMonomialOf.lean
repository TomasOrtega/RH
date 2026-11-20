import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PSectionSmall
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

namespace MonomialMap

/- English proof (translation)
Simplify using `only [IntegralSection.toFun, IntegralSection.mul, map_mul]`. Rewrite using `[mul_div_mul_comm]`.
-/
theorem toFun_mul {P : ArithVariety n} {a b : ι → ℤ} (s : IntegralSection P a) (t : IntegralSection P b) :
    (s.mul t).toFun = s.toFun * t.toFun := by
  simp only [IntegralSection.toFun, IntegralSection.mul, map_mul]
  rw [mul_div_mul_comm]

/- English proof (translation)
Simplify using `only [IntegralSection.toFun, IntegralSection.pow, map_pow, div_pow]`.
-/
theorem toFun_pow {P : ArithVariety n} {a : ι → ℤ} (s : IntegralSection P a) (m : ℕ) :
    (s.pow m).toFun = s.toFun ^ m := by
  simp only [IntegralSection.toFun, IntegralSection.pow, map_pow, div_pow]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toFun_cast {P : ArithVariety n} {a b : ι → ℤ} (h : a = b) (s : IntegralSection P a) :
    (s.cast h).toFun = s.toFun := rfl

/- English proof (translation)
Simplify `(GroundTheory.Heights₂.Heights.SectionSmall.proof ι n P A s).1 0 hs p q h z hz` using `[Real.exp_zero]`.
-/
theorem bound {P : ArithVariety n} {A : HermLine n} {s : IntegralSection P A.deg} (hs : s.SupNormLE A 0)
    {p q : MvPolynomial (Coord n) ℤ} (h : P.mkF p = s.toFun * P.mkF q) {z : Cone n ℂ} (hz : z ∈ P.points ℂ) :
    ‖evalCone z p‖ ≤ ‖evalCone z q‖ * A.metric z := by
  simpa [Real.exp_zero] using (GroundTheory.Heights₂.Heights.SectionSmall.proof ι n P A s).1 0 hs p q h z hz

/- English proof (translation)
Take `⟨d, e, he⟩` from `s.regular c (GroundTheory.Heights₂.Heights.SectionSmall.live_of_ne hz hc)`. Establish `h` using `GroundTheory.Heights₂.Heights.SectionSmall.mkF_eq_of_mem s he.2`. Conclude with `⟨d, e, h, bound hs h hz⟩`.
-/
theorem chart_bound {P : ArithVariety n} {A : HermLine n} {s : IntegralSection P A.deg} (hs : s.SupNormLE A 0)
    {z : Cone n ℂ} (hz : z ∈ P.points ℂ) {c : (k : ι) → Fin (n k + 1)} (hc : ∀ k, z k (c k) ≠ 0) :
    ∃ (d : ι → ℕ) (e : MvPolynomial (Coord n) ℤ), P.mkF e = s.toFun * P.mkF (chartMonomial c d) ∧
      ‖evalCone z e‖ ≤ ‖evalCone z (chartMonomial c d)‖ * A.metric z := by
  obtain ⟨d, e, he⟩ := s.regular c (GroundTheory.Heights₂.Heights.SectionSmall.live_of_ne hz hc)
  have h := GroundTheory.Heights₂.Heights.SectionSmall.mkF_eq_of_mem s he.2
  exact ⟨d, e, h, bound hs h hz⟩

/- English proof (translation)
Introduce `ι _ _ n P L _ q m r hr g h hg hgs hh hhs`. Establish `hX0 : g.toFun ^ (q - r) * h.toFun ^ (m + 1) ≠ 0` using `mul_ne_zero (pow_ne_zero _ hg) (pow_ne_zero _ hh)`. Establish `hdeg : (L.pow (q * m + r)).deg + (q - r) • L.deg + (m + 1) • (HermLine.standard n).deg = (((L.pow q).mul (HermLine.standard n)).pow (m + 1)).deg`. Use function extensionality and compare the values at `k`. Simplify using `only [HermLine.pow, HermLine.mul, HermLine.standard, Pi.add_apply, Pi.smul_apply]`.

Simplify using `only [nsmul_eq_mul]`. Move the coercions through the operations in `[Nat.cast_sub hr.le]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨fun s hs ↦ ?_, fun s₁ s₂ h12 ↦ ?_⟩` and prove the remaining obligations. Use `⟨((s.mul (g.pow (q - r))).mul (h.pow (m + 1))).cast hdeg, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[toFun_cast, toFun_mul, toFun_mul, toFun_pow, toFun_pow]`. Use `((GroundTheory.Heights₂.Heights.SectionSmall.proof ι n P _ _).2).mpr ?_` and prove the remaining obligations. Introduce `p p' δp δp' _ _ _ hpp' z hz`. Rewrite `hpp'` using `[toFun_cast, toFun_mul, toFun_mul, toFun_pow, toFun_pow]`. Take `⟨c, hc⟩` from `GroundTheory.Heights₂.Heights.SectionSmall.exists_chart hz`.

Take `⟨dg, eg, hegF, heg⟩` from `chart_bound hgs hz hc`. Take `⟨dh, eh, hehF, heh⟩` from `chart_bound hhs hz hc`. Establish `hrep : P.mkF (p * chartMonomial c dg ^ (q - r) * chartMonomial c dh ^ (m + 1)) = s.toFun * P.mkF (p' * eg ^ (q - r) * eh ^ (m + 1))`. Simplify using `only [map_mul, map_pow, hpp', hegF, hehF]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hb` using `bound hs hrep hz`. Establish `hgm` using `GroundTheory.Heights₂.Heights.SectionSmall.evalCone_chartMonomial_ne_zero hc dg`. Establish `hhm` using `GroundTheory.Heights₂.Heights.SectionSmall.evalCone_chartMonomial_ne_zero hc dh`. Establish `hmul : ∀ f f' : MvPolynomial (Coord n) ℤ, evalCone z (f * f') = evalCone z f * evalCone z f'`. Introduce `f f'`.

Simplify using `[evalCone, eval₂_mul]`. Establish `hpow : ∀ (f : MvPolynomial (Coord n) ℤ) (j : ℕ), evalCone z (f ^ j) = evalCone z f ^ j`. Introduce `f j`. Simplify using `[evalCone, eval₂_pow]`. Rewrite `hb` using `[hmul, hmul, hpow, hpow, hmul, hmul, hpow, hpow]`.

Simplify using `only [norm_mul, norm_pow] at hb`. Use `set Mg := ‖evalCone z (chartMonomial c dg)‖`. Use `set Mh := ‖evalCone z (chartMonomial c dh)‖`. Use `set Eg := ‖evalCone z eg‖`. Use `set Eh := ‖evalCone z eh‖`.

Use `set Q := ‖evalCone z p'‖`. Use `set P0 := ‖evalCone z p‖`. Establish `hMg : 0 < Mg` using `norm_pos_iff.mpr hgm`. Establish `hMh : 0 < Mh` using `norm_pos_iff.mpr hhm`. Establish `ha : 0 < L.metric z` using `L.metric_pos z hz.1`.

Express the relevant statement in the definitionally equal form `P0 * Mg ^ (q - r) * Mh ^ (m + 1) ≤ Q * Eg ^ (q - r) * Eh ^ (m + 1) * L.metric z ^ (q * m + r) at hb`. Express the relevant statement in the definitionally equal form `Eg ≤ Mg * L.metric z at heg`. Express the relevant statement in the definitionally equal form `Eh ≤ Mh * (HermLine.standard n).metric z at heh`. Express the relevant statement in the definitionally equal form `P0 ≤ Q * (L.metric z ^ q * (HermLine.standard n).metric z) ^ (m + 1)`. Establish `hexp : L.metric z ^ (q - r) * L.metric z ^ (q * m + r) = (L.metric z ^ q) ^ (m + 1)`.

Rewrite using `[← pow_add, ← pow_mul]`. Use `congr 1`. Rewrite using `[Nat.mul_succ]`. Use linear arithmetic over natural numbers and integers. Establish `key : Q * Eg ^ (q - r) * Eh ^ (m + 1) * L.metric z ^ (q * m + r) ≤ Q * (Mg * L.metric z) ^ (q - r) * (Mh * (HermLine.standard n).metric z) ^ (m + 1) * L.metric z ^ (q * m + r)`.

Establish `h1 : Eg ^ (q - r) ≤ (Mg * L.metric z) ^ (q - r)` using `pow_le_pow_left₀ (norm_nonneg _) heg _`. Establish `h2 : Eh ^ (m + 1) ≤ (Mh * (HermLine.standard n).metric z) ^ (m + 1)` using `pow_le_pow_left₀ (norm_nonneg _) heh _`. Establish `hQ : 0 ≤ Q` using `norm_nonneg _`. Establish `hL : 0 ≤ L.metric z ^ (q * m + r)` using `(pow_pos ha _).le`. Establish `hE : 0 ≤ Eg ^ (q - r)` using `pow_nonneg (norm_nonneg _) _`.

Establish `hF : 0 ≤ (Mg * L.metric z) ^ (q - r)` using `pow_nonneg (mul_nonneg hMg.le ha.le) _`. Establish `hE' : 0 ≤ Eh ^ (m + 1)` using `pow_nonneg (norm_nonneg _) _`. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left h1 hQ) h2 hE' (mul_nonneg hQ hF)) hL`. Establish `heq : Q * (Mg * L.metric z) ^ (q - r) * (Mh * (HermLine.standard n).metric z) ^ (m + 1) * L.metric z ^ (q * m + r) = Q * (L.metric z ^ q * (HermLine.standard n).metric z) ^ (m + 1) * (Mg ^ (q - r) * Mh ^ (m + 1))`. Combine the equalities or inequalities in the displayed calculation.

Use `le_of_mul_le_mul_right ?_ (mul_pos (pow_pos hMg (q - r)) (pow_pos hMh (m + 1)))` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite `h12` using `[mul_assoc, mul_assoc]`. Conclude with `mul_right_cancel₀ hX0 h12`.
-/
theorem sectionTyping_holds : GroundTheory.Heights₂.Heights.MonomialMap.Statement := by
  intro ι _ _ n P L _ q m r hr g h hg hgs hh hhs
  have hX0 : g.toFun ^ (q - r) * h.toFun ^ (m + 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hg) (pow_ne_zero _ hh)
  have hdeg : (L.pow (q * m + r)).deg + (q - r) • L.deg + (m + 1) • (HermLine.standard n).deg =
      (((L.pow q).mul (HermLine.standard n)).pow (m + 1)).deg := by
    funext k
    simp only [HermLine.pow, HermLine.mul, HermLine.standard, Pi.add_apply, Pi.smul_apply]
    simp only [nsmul_eq_mul]
    push_cast [Nat.cast_sub hr.le]
    ring
  refine ⟨fun s hs ↦ ?_, fun s₁ s₂ h12 ↦ ?_⟩
  · refine ⟨((s.mul (g.pow (q - r))).mul (h.pow (m + 1))).cast hdeg, ?_, ?_⟩
    · rw [toFun_cast, toFun_mul, toFun_mul, toFun_pow, toFun_pow]
    · refine ((GroundTheory.Heights₂.Heights.SectionSmall.proof ι n P _ _).2).mpr ?_
      intro p p' δp δp' _ _ _ hpp' z hz
      rw [toFun_cast, toFun_mul, toFun_mul, toFun_pow, toFun_pow] at hpp'
      obtain ⟨c, hc⟩ := GroundTheory.Heights₂.Heights.SectionSmall.exists_chart hz
      obtain ⟨dg, eg, hegF, heg⟩ := chart_bound hgs hz hc
      obtain ⟨dh, eh, hehF, heh⟩ := chart_bound hhs hz hc
      have hrep : P.mkF (p * chartMonomial c dg ^ (q - r) * chartMonomial c dh ^ (m + 1)) =
          s.toFun * P.mkF (p' * eg ^ (q - r) * eh ^ (m + 1)) := by
        simp only [map_mul, map_pow, hpp', hegF, hehF]
        ring
      have hb := bound hs hrep hz
      have hgm := GroundTheory.Heights₂.Heights.SectionSmall.evalCone_chartMonomial_ne_zero hc dg
      have hhm := GroundTheory.Heights₂.Heights.SectionSmall.evalCone_chartMonomial_ne_zero hc dh
      have hmul : ∀ f f' : MvPolynomial (Coord n) ℤ, evalCone z (f * f') = evalCone z f * evalCone z f' := by
        intro f f'; simp [evalCone, eval₂_mul]
      have hpow : ∀ (f : MvPolynomial (Coord n) ℤ) (j : ℕ), evalCone z (f ^ j) = evalCone z f ^ j := by
        intro f j; simp [evalCone, eval₂_pow]
      rw [hmul, hmul, hpow, hpow, hmul, hmul, hpow, hpow] at hb
      simp only [norm_mul, norm_pow] at hb
      set Mg := ‖evalCone z (chartMonomial c dg)‖
      set Mh := ‖evalCone z (chartMonomial c dh)‖
      set Eg := ‖evalCone z eg‖
      set Eh := ‖evalCone z eh‖
      set Q := ‖evalCone z p'‖
      set P0 := ‖evalCone z p‖
      have hMg : 0 < Mg := norm_pos_iff.mpr hgm
      have hMh : 0 < Mh := norm_pos_iff.mpr hhm
      have ha : 0 < L.metric z := L.metric_pos z hz.1
      change P0 * Mg ^ (q - r) * Mh ^ (m + 1) ≤ Q * Eg ^ (q - r) * Eh ^ (m + 1) * L.metric z ^ (q * m + r) at hb
      change Eg ≤ Mg * L.metric z at heg
      change Eh ≤ Mh * (HermLine.standard n).metric z at heh
      change P0 ≤ Q * (L.metric z ^ q * (HermLine.standard n).metric z) ^ (m + 1)
      have hexp : L.metric z ^ (q - r) * L.metric z ^ (q * m + r) = (L.metric z ^ q) ^ (m + 1) := by
        rw [← pow_add, ← pow_mul]
        congr 1
        rw [Nat.mul_succ]
        omega
      have key : Q * Eg ^ (q - r) * Eh ^ (m + 1) * L.metric z ^ (q * m + r) ≤
          Q * (Mg * L.metric z) ^ (q - r) * (Mh * (HermLine.standard n).metric z) ^ (m + 1) *
            L.metric z ^ (q * m + r) := by
        have h1 : Eg ^ (q - r) ≤ (Mg * L.metric z) ^ (q - r) := pow_le_pow_left₀ (norm_nonneg _) heg _
        have h2 : Eh ^ (m + 1) ≤ (Mh * (HermLine.standard n).metric z) ^ (m + 1) :=
          pow_le_pow_left₀ (norm_nonneg _) heh _
        have hQ : 0 ≤ Q := norm_nonneg _
        have hL : 0 ≤ L.metric z ^ (q * m + r) := (pow_pos ha _).le
        have hE : 0 ≤ Eg ^ (q - r) := pow_nonneg (norm_nonneg _) _
        have hF : 0 ≤ (Mg * L.metric z) ^ (q - r) := pow_nonneg (mul_nonneg hMg.le ha.le) _
        have hE' : 0 ≤ Eh ^ (m + 1) := pow_nonneg (norm_nonneg _) _
        exact mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left h1 hQ) h2 hE'
          (mul_nonneg hQ hF)) hL
      have heq : Q * (Mg * L.metric z) ^ (q - r) * (Mh * (HermLine.standard n).metric z) ^ (m + 1) *
            L.metric z ^ (q * m + r) =
          Q * (L.metric z ^ q * (HermLine.standard n).metric z) ^ (m + 1) * (Mg ^ (q - r) * Mh ^ (m + 1)) := by
        calc _ = Q * Mg ^ (q - r) * Mh ^ (m + 1) * (HermLine.standard n).metric z ^ (m + 1) *
              (L.metric z ^ (q - r) * L.metric z ^ (q * m + r)) := by ring
          _ = _ := by rw [hexp]; ring
      refine le_of_mul_le_mul_right ?_ (mul_pos (pow_pos hMg (q - r)) (pow_pos hMh (m + 1)))
      calc P0 * (Mg ^ (q - r) * Mh ^ (m + 1)) = P0 * Mg ^ (q - r) * Mh ^ (m + 1) := by ring
        _ ≤ _ := hb.trans key
        _ = _ := heq
  · rw [mul_assoc, mul_assoc] at h12
    exact mul_right_cancel₀ hX0 h12

omit [Fintype ι] in
/- English proof (translation)
Simplify using `[val, map_mul]`.
-/
theorem val_mul (P : ArithVariety n) (f g : MvPolynomial (Coord n) ℤ) : val P (f * g) = val P f * val P g := by
  simp [val, map_mul]

omit [Fintype ι] in
/- English proof (translation)
Simplify using `[val, map_pow]`.
-/
theorem val_pow (P : ArithVariety n) (f : MvPolynomial (Coord n) ℤ) (k : ℕ) : val P (f ^ k) = val P f ^ k := by
  simp [val, map_pow]

/- English proof (translation)
Simplify using `[monomialOf, val, genPt, map_prod, map_pow]`.
-/
theorem val_monomialOf (P : ArithVariety n) (μ : Coord n → ℕ) :
    val P (monomialOf μ) = ∏ v, genPt P v ^ μ v := by
  simp [monomialOf, val, genPt, map_prod, map_pow]

/- English proof (translation)
Establish `h` using `IsWeightedHomogeneous.prod Finset.univ (fun v ↦ (X v : MvPolynomial (Coord n) ℤ) ^ μ v) (fun v ↦ μ v • coordDeg n v) (fun v _ ↦ (isWeightedHomogeneous_X ℤ (coordDeg n) v).pow (μ v))`. Establish `hd : (∑ v, μ v • coordDeg n v) = fun k ↦ ∑ i, μ ⟨k, i⟩`. Use function extensionality and compare the values at `k`. Rewrite using `[Finset.sum_apply, Fintype.sum_sigma]`. Simplify using `[coordDeg, Pi.single_apply]`.

Rewrite using `[← hd]`. Conclude with `h`.
-/
theorem isWeightedHomogeneous_monomialOf (μ : Coord n → ℕ) :
    IsWeightedHomogeneous (coordDeg n) (monomialOf μ) (fun k ↦ ∑ i, μ ⟨k, i⟩) := by
  have h := IsWeightedHomogeneous.prod Finset.univ (fun v ↦ (X v : MvPolynomial (Coord n) ℤ) ^ μ v)
    (fun v ↦ μ v • coordDeg n v) (fun v _ ↦ (isWeightedHomogeneous_X ℤ (coordDeg n) v).pow (μ v))
  have hd : (∑ v, μ v • coordDeg n v) = fun k ↦ ∑ i, μ ⟨k, i⟩ := by
    funext k
    rw [Finset.sum_apply, Fintype.sum_sigma]
    simp [coordDeg, Pi.single_apply]
  rw [← hd]
  exact h

omit [DecidableEq ι] in

/- English proof (translation)
Establish `he : evalCone z (monomialOf μ) = ∏ v, z v.1 v.2 ^ μ v`. Simplify using `[evalCone, monomialOf, eval₂_prod, eval₂_pow]`. Rewrite using `[he, norm_prod]`. Use `show ∏ v, ‖z v.1 v.2 ^ μ v‖ ≤ ∏ k, l2Norm (z k)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[norm_pow]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) (norm_le_l2Norm _ _) _`. Use `_ = ∏ k, l2Norm (z k) := by`. Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ ↦ ?_` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hμ k, pow_one]`.
-/
theorem norm_evalCone_monomialOf_le (z : Cone n ℂ) (μ : Coord n → ℕ) (hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = 1) :
    ‖evalCone z (monomialOf μ)‖ ≤ (HermLine.standard n).metric z := by
  have he : evalCone z (monomialOf μ) = ∏ v, z v.1 v.2 ^ μ v := by
    simp [evalCone, monomialOf, eval₂_prod, eval₂_pow]
  rw [he, norm_prod]
  show ∏ v, ‖z v.1 v.2 ^ μ v‖ ≤ ∏ k, l2Norm (z k)
  calc ∏ v, ‖z v.1 v.2 ^ μ v‖ ≤ ∏ v : Coord n, l2Norm (z v.1) ^ μ v :=
        Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) fun v _ ↦ by
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_l2Norm _ _) _
    _ = ∏ k, l2Norm (z k) := by
        rw [Fintype.prod_sigma]
        refine Finset.prod_congr rfl fun k _ ↦ ?_
        dsimp only
        rw [Finset.prod_pow_eq_pow_sum, hμ k, pow_one]

/- English proof (translation)
Establish `heq : val P (monomialOf μ) * ∏ k, genPt P ⟨k, c k⟩ ^ (-(a k : ℤ)) = ∏ v : Coord n, (genPt P v / genPt P ⟨v.1, c v.1⟩) ^ μ v`. Rewrite using `[val_monomialOf]`. Simplify using `only [div_pow, Finset.prod_div_distrib]`. Rewrite using `[div_eq_mul_inv]`. Use `congr 1`.

Rewrite using `[Fintype.prod_sigma, ← Finset.prod_inv_distrib]`. Use `Finset.prod_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hμ k, zpow_neg, zpow_natCast]`. Rewrite using `[heq]`.

Conclude with `Subalgebra.prod_mem _ fun v _ ↦ Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self v)) _`.
-/
theorem monomial_mul_mem (P : ArithVariety n) (μ : Coord n → ℕ) (a : ι → ℕ) (hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = a k)
    (c : (k : ι) → Fin (n k + 1)) :
    val P (monomialOf μ) * ∏ k, genPt P ⟨k, c k⟩ ^ (-(a k : ℤ)) ∈ chartRingZ (genPt P) c := by
  have heq : val P (monomialOf μ) * ∏ k, genPt P ⟨k, c k⟩ ^ (-(a k : ℤ)) =
      ∏ v : Coord n, (genPt P v / genPt P ⟨v.1, c v.1⟩) ^ μ v := by
    rw [val_monomialOf]
    simp only [div_pow, Finset.prod_div_distrib]
    rw [div_eq_mul_inv]
    congr 1
    rw [Fintype.prod_sigma, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum, hμ k, zpow_neg, zpow_natCast]
  rw [heq]
  exact Subalgebra.prod_mem _ fun v _ ↦ Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self v)) _

/- English proof (translation)
Introduce `ι _ _ n P L a _ hmono q m r hr μg μh hμg hμh hg0 hh0`. Establish `hX0 : val P (monomialOf μg) ^ (q - r) * val P (monomialOf μh) ^ (m + 1) ≠ 0` using `mul_ne_zero (pow_ne_zero _ hg0) (pow_ne_zero _ hh0)`. Use `⟨fun s₁ _ s₂ _ h12 ↦ ?_, fun s hs hsmall ↦ ⟨?_, ?_⟩⟩` and prove the remaining obligations. Simplify using `only at h12`. Rewrite `h12` using `[mul_assoc, mul_assoc]`.

Conclude with `mul_right_cancel₀ hX0 h12`. Introduce `c hc`. Establish `hs'` using `hs c hc`. Establish `hG` using `monomial_mul_mem P μg a hμg c`. Establish `hH` using `monomial_mul_mem P μh (fun _ ↦ 1) hμh c`.

Establish `key : s * val P (monomialOf μg) ^ (q - r) * val P (monomialOf μh) ^ (m + 1) * ∏ k, genPt P ⟨k, c k⟩ ^ (-(((m + 1 : ℕ) : ℤ) * ((q * a k + 1 : ℕ) : ℤ))) = (s * ∏ k, genPt P ⟨k, c k⟩ ^ (-(((q * m + r : ℕ) : ℤ) * (a k : ℤ)))) * (val P (monomialOf μg) * ∏ k, genPt P ⟨k, c k⟩ ^ (-(a k …`. Establish `hy : ∏ k, genPt P ⟨k, c k⟩ ^ (-(((m + 1 : ℕ) : ℤ) * ((q * a k + 1 : ℕ) : ℤ))) = (∏ k, genPt P ⟨k, c k⟩ ^ (-(((q * m + r : ℕ) : ℤ) * (a k : ℤ)))) * (∏ k, genPt P ⟨k, c k⟩ ^ (-(a k : ℤ))) ^ (q - r) * (∏ k, genPt P ⟨k, c k⟩ ^ (-(((fun _ ↦ 1 : ι → ℕ) k : ℕ) : ℤ))) ^ (m + 1)`. Rewrite using `[← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ (hc k), ← zpow_add₀ (hc k)]`.

Use `congr 1`. Move the coercions through the operations in `[Nat.cast_sub hr.le]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hy]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only at hs'`. Rewrite using `[key]`. Establish `mem : ∀ x ∈ chartRingZ (genPt P) c, x ∈ integralClosure (chartRingZ (genPt P) c) (FunField P)` using `fun x hx ↦ Subalgebra.algebraMap_mem (integralClosure (chartRingZ (genPt P) c) (FunField P)) (⟨x, hx⟩ : chartRingZ (genPt P) c)`. Conclude with `mul_mem (mul_mem hs' (pow_mem (mem _ hG) _)) (pow_mem (mem _ hH) _)`. Introduce `p p' dp dp' hp hp' hdeg hval z hz`.

Establish `hGh : IsWeightedHomogeneous (coordDeg n) (monomialOf μg) a`. Use `isWeightedHomogeneous_monomialOf μg using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Conclude with `(hμg k).symm`. Establish `hHh : IsWeightedHomogeneous (coordDeg n) (monomialOf μh) (fun _ ↦ 1)`.

Use `isWeightedHomogeneous_monomialOf μh using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Conclude with `(hμh k).symm`. Establish `h1` using `hsmall p (p' * monomialOf μg ^ (q - r) * monomialOf μh ^ (m + 1)) dp (dp' + (q - r) • a + (m + 1) • fun _ ↦ 1) hp ((hp'.mul (hGh.pow _)).mul (hHh.pow _)) (fun k ↦ by`. Use `hdeg k` as an intermediate fact.

Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢`. Rewrite using `[this]`. Move the coercions through the operations in `[Nat.cast_sub hr.le]`. Use the proof step `ring)`. Use the proof step `(by rw [val_mul, val_mul, val_pow, val_pow, hval]; ring) z hz`.

Establish `ha : 0 < L.metric z` using `L.metric_pos z hz.1`. Establish `hG` using `hmono z hz μg hμg`. Establish `hH` using `norm_evalCone_monomialOf_le z μh hμh`. Establish `hmul : ∀ f f' : MvPolynomial (Coord n) ℤ, evalCone z (f * f') = evalCone z f * evalCone z f'`. Introduce `f f'`.

Simplify using `[evalCone, eval₂_mul]`. Establish `hpow : ∀ (f : MvPolynomial (Coord n) ℤ) (j : ℕ), evalCone z (f ^ j) = evalCone z f ^ j`. Introduce `f j`. Simplify using `[evalCone, eval₂_pow]`. Rewrite `h1` using `[hmul, hmul, hpow, hpow]`.

Simplify using `only [norm_mul, norm_pow] at h1`. Establish `hexp : L.metric z ^ (q - r) * L.metric z ^ (q * m + r) = (L.metric z ^ q) ^ (m + 1)`. Rewrite using `[← pow_add, ← pow_mul]`. Use `congr 1`. Rewrite using `[Nat.mul_succ]`.

Use linear arithmetic over natural numbers and integers. Use `h1.trans ?_` and prove the remaining obligations. Establish `h2` using `pow_le_pow_left₀ (norm_nonneg _) hG (q - r)`. Establish `h3` using `pow_le_pow_left₀ (norm_nonneg _) hH (m + 1)`. Establish `hL : 0 ≤ L.metric z ^ (q * m + r)` using `(pow_pos ha _).le`.

Establish `hQ : 0 ≤ ‖evalCone z p'‖` using `norm_nonneg _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem statement_holds : MonomialMap.Statement := by
  intro ι _ _ n P L a _ hmono q m r hr μg μh hμg hμh hg0 hh0
  have hX0 : val P (monomialOf μg) ^ (q - r) * val P (monomialOf μh) ^ (m + 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hg0) (pow_ne_zero _ hh0)
  refine ⟨fun s₁ _ s₂ _ h12 ↦ ?_, fun s hs hsmall ↦ ⟨?_, ?_⟩⟩
  · simp only at h12
    rw [mul_assoc, mul_assoc] at h12
    exact mul_right_cancel₀ hX0 h12
  · intro c hc
    have hs' := hs c hc
    have hG := monomial_mul_mem P μg a hμg c
    have hH := monomial_mul_mem P μh (fun _ ↦ 1) hμh c
    have key : s * val P (monomialOf μg) ^ (q - r) * val P (monomialOf μh) ^ (m + 1) *
          ∏ k, genPt P ⟨k, c k⟩ ^ (-(((m + 1 : ℕ) : ℤ) * ((q * a k + 1 : ℕ) : ℤ))) =
        (s * ∏ k, genPt P ⟨k, c k⟩ ^ (-(((q * m + r : ℕ) : ℤ) * (a k : ℤ)))) *
          (val P (monomialOf μg) * ∏ k, genPt P ⟨k, c k⟩ ^ (-(a k : ℤ))) ^ (q - r) *
          (val P (monomialOf μh) * ∏ k, genPt P ⟨k, c k⟩ ^ (-(((fun _ ↦ 1 : ι → ℕ) k : ℕ) : ℤ))) ^ (m + 1) := by
      have hy : ∏ k, genPt P ⟨k, c k⟩ ^ (-(((m + 1 : ℕ) : ℤ) * ((q * a k + 1 : ℕ) : ℤ))) =
          (∏ k, genPt P ⟨k, c k⟩ ^ (-(((q * m + r : ℕ) : ℤ) * (a k : ℤ)))) *
            (∏ k, genPt P ⟨k, c k⟩ ^ (-(a k : ℤ))) ^ (q - r) *
            (∏ k, genPt P ⟨k, c k⟩ ^ (-(((fun _ ↦ 1 : ι → ℕ) k : ℕ) : ℤ))) ^ (m + 1) := by
        rw [← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ ↦ ?_
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ (hc k),
          ← zpow_add₀ (hc k)]
        congr 1
        push_cast [Nat.cast_sub hr.le]
        ring
      rw [hy]
      ring
    simp only at hs'
    rw [key]
    have mem : ∀ x ∈ chartRingZ (genPt P) c, x ∈ integralClosure (chartRingZ (genPt P) c) (FunField P) :=
      fun x hx ↦ Subalgebra.algebraMap_mem (integralClosure (chartRingZ (genPt P) c) (FunField P))
        (⟨x, hx⟩ : chartRingZ (genPt P) c)
    exact mul_mem (mul_mem hs' (pow_mem (mem _ hG) _)) (pow_mem (mem _ hH) _)
  · intro p p' dp dp' hp hp' hdeg hval z hz
    have hGh : IsWeightedHomogeneous (coordDeg n) (monomialOf μg) a := by
      convert isWeightedHomogeneous_monomialOf μg using 1
      funext k
      exact (hμg k).symm
    have hHh : IsWeightedHomogeneous (coordDeg n) (monomialOf μh) (fun _ ↦ 1) := by
      convert isWeightedHomogeneous_monomialOf μh using 1
      funext k
      exact (hμh k).symm
    have h1 := hsmall p (p' * monomialOf μg ^ (q - r) * monomialOf μh ^ (m + 1)) dp
      (dp' + (q - r) • a + (m + 1) • fun _ ↦ 1) hp ((hp'.mul (hGh.pow _)).mul (hHh.pow _))
      (fun k ↦ by
        have := hdeg k
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
        rw [this]
        push_cast [Nat.cast_sub hr.le]
        ring)
      (by rw [val_mul, val_mul, val_pow, val_pow, hval]; ring) z hz
    have ha : 0 < L.metric z := L.metric_pos z hz.1
    have hG := hmono z hz μg hμg
    have hH := norm_evalCone_monomialOf_le z μh hμh
    have hmul : ∀ f f' : MvPolynomial (Coord n) ℤ, evalCone z (f * f') = evalCone z f * evalCone z f' := by
      intro f f'; simp [evalCone, eval₂_mul]
    have hpow : ∀ (f : MvPolynomial (Coord n) ℤ) (j : ℕ), evalCone z (f ^ j) = evalCone z f ^ j := by
      intro f j; simp [evalCone, eval₂_pow]
    rw [hmul, hmul, hpow, hpow] at h1
    simp only [norm_mul, norm_pow] at h1
    have hexp : L.metric z ^ (q - r) * L.metric z ^ (q * m + r) = (L.metric z ^ q) ^ (m + 1) := by
      rw [← pow_add, ← pow_mul]
      congr 1
      rw [Nat.mul_succ]
      omega
    refine h1.trans ?_
    have h2 := pow_le_pow_left₀ (norm_nonneg _) hG (q - r)
    have h3 := pow_le_pow_left₀ (norm_nonneg _) hH (m + 1)
    have hL : 0 ≤ L.metric z ^ (q * m + r) := (pow_pos ha _).le
    have hQ : 0 ≤ ‖evalCone z p'‖ := norm_nonneg _
    calc _ ≤ ‖evalCone z p'‖ * L.metric z ^ (q - r) * (HermLine.standard n).metric z ^ (m + 1) *
            L.metric z ^ (q * m + r) :=
          mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left h2 hQ) h3
            (pow_nonneg (norm_nonneg _) _) (mul_nonneg hQ (pow_pos ha _).le)) hL
      _ = ‖evalCone z p'‖ * (HermLine.standard n).metric z ^ (m + 1) *
            (L.metric z ^ (q - r) * L.metric z ^ (q * m + r)) := by ring
      _ = _ := by rw [hexp]; ring

end MonomialMap

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ ↦ MonomialMap.statement_holds, fun _ ↦ MonomialMap.sectionTyping_holds⟩`.
-/
theorem MonomialMap.equiv : GroundTheory.Heights₂.Heights.MonomialMap.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.MonomialMap.Statement :=
  ⟨fun _ ↦ MonomialMap.statement_holds, fun _ ↦ MonomialMap.sectionTyping_holds⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
