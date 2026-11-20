import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscCoefficientsTopologicallyFree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscToDiscInjectiveOfAdicBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPolyEqZeroOfDiscDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionZeroOneProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinClosedDiscNormMulMultiplicative
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DiscDvd

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

/- English proof (translation)
Establish `hl : (1 : ℝ≥0) < (l : ℝ≥0)` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `he : (0 : ℝ) < bk.Ep.natDegree` using `by exact_mod_cast bk.deg_pos`. Use `⟨NNReal.rpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos), ?_⟩` and prove the remaining obligations. Conclude with `NNReal.rpow_lt_one_of_one_lt_of_neg hl (by rw [neg_lt_zero]; positivity)`.
-/
theorem ρ₀_pos_lt (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have hl : (1 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have he : (0 : ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
  refine ⟨NNReal.rpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos), ?_⟩
  exact NNReal.rpow_lt_one_of_one_lt_of_neg hl (by rw [neg_lt_zero]; positivity)

/- English proof (translation)
Use `haveI : IsAdicComplete (Ideal.span {(l : Wq l bk.a)}) (Wq l bk.a) := WittVector.isAdicCompleteIdealSpanP`. Establish `hsurj : Function.Surjective (WittVector.constantCoeff (p` using `l) (R := Fq l bk.a)) := fun x => ⟨WittVector.teichmuller l x, by simp⟩`. Establish `hm : IsLocalRing.maximalIdeal (Wq l bk.a) = Ideal.span {(l : Wq l bk.a)}`. Rewrite using `[← WittVector.ker_constantCoeff]`. Use `haveI := RingHom.ker_isMaximal_of_surjective _ hsurj`.

Conclude with `(IsLocalRing.eq_maximalIdeal this).symm`. Conclude with `hm ▸ inferInstance`.
-/
theorem complete_max (bk : BK K) :
    IsAdicComplete (IsLocalRing.maximalIdeal (Wq l bk.a)) (Wq l bk.a) := by
  haveI : IsAdicComplete (Ideal.span {(l : Wq l bk.a)}) (Wq l bk.a) := WittVector.isAdicCompleteIdealSpanP
  have hsurj : Function.Surjective (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) :=
    fun x => ⟨WittVector.teichmuller l x, by simp⟩
  have hm : IsLocalRing.maximalIdeal (Wq l bk.a) = Ideal.span {(l : Wq l bk.a)} := by
    rw [← WittVector.ker_constantCoeff]
    haveI := RingHom.ker_isMaximal_of_surjective _ hsurj
    exact (IsLocalRing.eq_maximalIdeal this).symm
  exact hm ▸ inferInstance

/- English proof (translation)
Use `haveI := complete_max bk`. Establish `hg : PowerSeries.map (IsLocalRing.residue (Wq l bk.a)) bk.E ≠ 0`. Introduce `h0`. Establish `h1` using `congrArg (PowerSeries.coeff bk.Ep.natDegree) h0`. Rewrite `h1` using `[PowerSeries.coeff_map, BK.E, Polynomial.coeff_coe, bk.monic.coeff_natDegree, map_one, map_zero]`.

Conclude with `one_ne_zero h1`. Establish `e1` using `s.eq_mul_weierstrassDiv_add_weierstrassMod hg`. Use `set r := s %ʷ bk.E`. Establish `e2` using `Polynomial.modByMonic_add_div r bk.Ep`. Establish `e3 : s = bk.E * (s /ʷ bk.E + ((r /ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S)) + ((r %ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S)` using `by conv_lhs => rw [e1, ← e2]`.

Rewrite using `[Polynomial.coe_add, Polynomial.coe_mul]`. Simplify using `only [BK.E]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : toDisc l (X : bk.S) bk.ρ₀ bk.E ∣ toDisc l (X : bk.S) bk.ρ₀ ((r %ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S)`. Establish `: ((r %ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S) = s - bk.E * (s /ʷ bk.E + ((r /ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S))`.

Rewrite using `[eq_sub_iff_add_eq, add_comm, ← e3]`. Rewrite using `[this, map_sub, map_mul]`. Conclude with `dvd_sub h (dvd_mul_right _ _)`. Establish `h4` using `GlobalTheory.BSP.DiscRem.eq_zero_of_dvd l K bk _ (Polynomial.degree_modByMonic_lt r bk.monic) h3`. Rewrite using `[e3, h4, Polynomial.coe_zero, add_zero]`.

Conclude with `dvd_mul_right _ _`.
-/
theorem dvd_E (bk : BK K) (s : bk.S) (h : toDisc l (X : bk.S) bk.ρ₀ bk.E ∣ toDisc l (X : bk.S) bk.ρ₀ s) :
    bk.E ∣ s := by
  haveI := complete_max bk
  have hg : PowerSeries.map (IsLocalRing.residue (Wq l bk.a)) bk.E ≠ 0 := by
    intro h0
    have h1 := congrArg (PowerSeries.coeff bk.Ep.natDegree) h0
    rw [PowerSeries.coeff_map, BK.E, Polynomial.coeff_coe, bk.monic.coeff_natDegree, map_one,
      map_zero] at h1
    exact one_ne_zero h1
  have e1 := s.eq_mul_weierstrassDiv_add_weierstrassMod hg
  set r := s %ʷ bk.E
  have e2 := Polynomial.modByMonic_add_div r bk.Ep
  have e3 : s = bk.E * (s /ʷ bk.E + ((r /ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S)) +
      ((r %ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S) := by
    conv_lhs => rw [e1, ← e2]
    rw [Polynomial.coe_add, Polynomial.coe_mul]
    simp only [BK.E]; ring
  have h3 : toDisc l (X : bk.S) bk.ρ₀ bk.E ∣ toDisc l (X : bk.S) bk.ρ₀ ((r %ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S) := by
    have : ((r %ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S) =
        s - bk.E * (s /ʷ bk.E + ((r /ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S)) := by
      rw [eq_sub_iff_add_eq, add_comm, ← e3]
    rw [this, map_sub, map_mul]
    exact dvd_sub h (dvd_mul_right _ _)
  have h4 := GlobalTheory.BSP.DiscRem.eq_zero_of_dvd l K bk _ (Polynomial.degree_modByMonic_lt r bk.monic) h3
  rw [e3, h4, Polynomial.coe_zero, add_zero]
  exact dvd_mul_right _ _

/- English proof (translation)
Rewrite using `[PowerSeries.X_dvd_iff]`. Establish `hh : ‖toDisc l (0 : Wq l bk.a) 1 ((PowerSeries.constantCoeff : bk.S →+* Wq l bk.a) X)‖ ≤ bk.ρ₀`. Rewrite using `[PowerSeries.constantCoeff_X, map_zero, norm_zero]`. Conclude with `NNReal.coe_nonneg _`. Establish `hm` using `isDiscMap_map (l := l) (u := (X : bk.S)) (ρ := bk.ρ₀) (u' := (0 : Wq l bk.a)) (ρ' := 1) (PowerSeries.constantCoeff : bk.S →+* Wq l bk.a) hh`.

Take `⟨z, hz⟩` from `h`. Establish `h1` using `congrArg (Disc.map (PowerSeries.constantCoeff : bk.S →+* Wq l bk.a) hh) hz`. Rewrite `h1` using `[map_mul, hm.ext, hm.ext, PowerSeries.constantCoeff_X, map_zero, zero_mul]`. Conclude with `(GlobalTheory.BSP.disc_zero_one l K bk).2.2.1 (h1.trans (map_zero _).symm)`.
-/
theorem dvd_X (bk : BK K) (s : bk.S) (h : toDisc l (X : bk.S) bk.ρ₀ X ∣ toDisc l (X : bk.S) bk.ρ₀ s) :
    (X : bk.S) ∣ s := by
  rw [PowerSeries.X_dvd_iff]
  have hh : ‖toDisc l (0 : Wq l bk.a) 1 ((PowerSeries.constantCoeff : bk.S →+* Wq l bk.a) X)‖ ≤ bk.ρ₀ := by
    rw [PowerSeries.constantCoeff_X, map_zero, norm_zero]; exact NNReal.coe_nonneg _
  have hm := isDiscMap_map (l := l) (u := (X : bk.S)) (ρ := bk.ρ₀) (u' := (0 : Wq l bk.a)) (ρ' := 1)
    (PowerSeries.constantCoeff : bk.S →+* Wq l bk.a) hh
  obtain ⟨z, hz⟩ := h
  have h1 := congrArg (Disc.map (PowerSeries.constantCoeff : bk.S →+* Wq l bk.a) hh) hz
  rw [map_mul, hm.ext, hm.ext, PowerSeries.constantCoeff_X, map_zero, zero_mul] at h1
  exact (GlobalTheory.BSP.disc_zero_one l K bk).2.2.1 (h1.trans (map_zero _).symm)

/- English proof (translation)
Use `haveI : IsAdicComplete bk.J bk.S := bk.complete`. Conclude with `(GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk bk.S (RingHom.id bk.S) Unit (TopBasis.self bk.J) bk.ρ₀ (ρ₀_pos_lt bk).1 (ρ₀_pos_lt bk).2).1`.
-/
theorem toDisc_inj (bk : BK K) : Function.Injective (toDisc l (X : bk.S) bk.ρ₀) := by
  haveI : IsAdicComplete bk.J bk.S := bk.complete
  exact (GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk bk.S (RingHom.id bk.S) Unit (TopBasis.self bk.J) bk.ρ₀
    (ρ₀_pos_lt bk).1 (ρ₀_pos_lt bk).2).1

/- English proof (translation)
Use `mem_nonZeroDivisors_iff.2 ⟨fun y hy => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Use `GlobalTheory.BSP.GaussMul.norm_mul l K bk bk.ρ₀ (ρ₀_pos_lt bk).1 (ρ₀_pos_lt bk).2 x y` as an intermediate fact. Rewrite `this` using `[hy, norm_zero]`. Conclude with `norm_eq_zero.1 ((mul_eq_zero.1 this.symm).resolve_left (norm_ne_zero_iff.2 hx))`. Use `GlobalTheory.BSP.GaussMul.norm_mul l K bk bk.ρ₀ (ρ₀_pos_lt bk).1 (ρ₀_pos_lt bk).2 y x` as an intermediate fact.

Rewrite `this` using `[hy, norm_zero]`. Conclude with `norm_eq_zero.1 ((mul_eq_zero.1 this.symm).resolve_right (norm_ne_zero_iff.2 hx))`.
-/
theorem mem_nzd (bk : BK K) {x : bk.DS bk.ρ₀} (hx : x ≠ 0) : x ∈ nonZeroDivisors (bk.DS bk.ρ₀) := by
  refine mem_nonZeroDivisors_iff.2 ⟨fun y hy => ?_, fun y hy => ?_⟩
  · have := GlobalTheory.BSP.GaussMul.norm_mul l K bk bk.ρ₀ (ρ₀_pos_lt bk).1 (ρ₀_pos_lt bk).2 x y
    rw [hy, norm_zero] at this
    exact norm_eq_zero.1 ((mul_eq_zero.1 this.symm).resolve_left (norm_ne_zero_iff.2 hx))
  · have := GlobalTheory.BSP.GaussMul.norm_mul l K bk bk.ρ₀ (ρ₀_pos_lt bk).1 (ρ₀_pos_lt bk).2 y x
    rw [hy, norm_zero] at this
    exact norm_eq_zero.1 ((mul_eq_zero.1 this.symm).resolve_right (norm_ne_zero_iff.2 hx))

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => intro s _`. Rewrite using `[pow_zero]`. Conclude with `one_dvd _`. Consider the case `succ m ih`.

Introduce `s h`. Take `⟨s', rfl⟩` from `dvd_E bk s ((dvd_pow_self _ (Nat.succ_ne_zero m)).trans h)`. Take `⟨z, hz⟩` from `h`. Establish `hE : toDisc l (X : bk.S) bk.ρ₀ bk.E ≠ 0` using `fun h0 => bk.E_ne_zero (toDisc_inj bk (h0.trans (map_zero _).symm))`. Rewrite `hz` using `[map_mul, pow_succ', mul_assoc]`.

Use `(mul_cancel_left_mem_nonZeroDivisors (mem_nzd bk hE)).1 hz` as an intermediate fact. Rewrite using `[pow_succ']`. Conclude with `mul_dvd_mul_left _ (ih s' ⟨z, this⟩)`.
-/
theorem dvd_E_pow (bk : BK K) (m : ℕ) : ∀ s : bk.S,
    toDisc l (X : bk.S) bk.ρ₀ bk.E ^ m ∣ toDisc l (X : bk.S) bk.ρ₀ s → bk.E ^ m ∣ s := by
  induction m with
  | zero => intro s _; rw [pow_zero]; exact one_dvd _
  | succ m ih =>
    intro s h
    obtain ⟨s', rfl⟩ := dvd_E bk s ((dvd_pow_self _ (Nat.succ_ne_zero m)).trans h)
    obtain ⟨z, hz⟩ := h
    have hE : toDisc l (X : bk.S) bk.ρ₀ bk.E ≠ 0 := fun h0 =>
      bk.E_ne_zero (toDisc_inj bk (h0.trans (map_zero _).symm))
    rw [map_mul, pow_succ', mul_assoc] at hz
    have := (mul_cancel_left_mem_nonZeroDivisors (mem_nzd bk hE)).1 hz
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih s' ⟨z, this⟩)

end GlobalTheory.BSP.DiscDvd

namespace GlobalTheory.BSP.DiscDvd

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

/- English proof (translation)
Take `⟨ι, ⟨TB⟩⟩` from `GlobalTheory.BSP.AinfTopBasis.main l K bk`. Take `⟨h0, h1⟩` from `ρ₀_pos_lt bk`. Establish `hj : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀`. Simplify using `using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 h0`. Establish `hjm` using `isDiscMap_map (l := l) (u := (X : bk.S)) (ρ := bk.ρ₀) (u' := bk.ev X) (ρ' := bk.ρ₀) bk.ev hj`.

Take `⟨cD, hc1, hc2, -, hc4, -⟩` from `GlobalTheory.BSP.disc_coefficients l K bk (Ainf l) bk.ev ι TB bk.ρ₀ h0 h1 _ hjm`. Take `⟨y, hy⟩` from `h`. Establish `hiS : bk.iS g = Disc.map bk.ev hj (toDisc l (X : bk.S) bk.ρ₀ g)` using `(hjm.ext g).symm`. Establish `hq : ∀ i, ∃ q : bk.S, TB.c i a = g * q ∧ toDisc l (X : bk.S) bk.ρ₀ q = cD i y`. Introduce `i`.

Establish `e : toDisc l (X : bk.S) bk.ρ₀ (TB.c i a) = toDisc l (X : bk.S) bk.ρ₀ g * cD i y`. Rewrite using `[← hc1, show toDisc l (bk.ev X) bk.ρ₀ a = bk.iA a from rfl, hy, hiS, hc2]`. Take `⟨q, hq⟩` from `hdiv _ ⟨_, e⟩`. Use `⟨q, hq, ?_⟩` and prove the remaining obligations. Rewrite `e` using `[hq, map_mul]`.

Conclude with `(mul_cancel_left_mem_nonZeroDivisors hreg).1 e`. Use `choose q hq1 hq2 using hq`. Use `haveI : IsAdicComplete bk.J bk.S := bk.complete`. Establish `hsmall` using `(GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk bk.S (RingHom.id bk.S) Unit (TopBasis.self bk.J) bk.ρ₀ h0 h1).2.1`. Establish `hfin : ∀ n, {i | q i ∉ bk.J ^ n}.Finite`.

Introduce `n`. Take `⟨r, hr, hr'⟩` from `hsmall n`. Establish `hev : ∀ᶠ i in Filter.cofinite, ‖cD i y‖ < r` using `(hc4 y).norm.eventually (gt_mem_nhds (by simpa using hr))`. Use `(Filter.eventually_cofinite.1 hev).subset fun i hi hlt => hi ?_` and prove the remaining obligations. Establish `h5 : ‖toDisc l (X : bk.S) bk.ρ₀ (q i)‖ ≤ r` using `by rw [hq2 i]; exact hlt.le`.

Establish `h6` using `hr' (q i) h5`. Rewrite `h6` using `[Ideal.map_id]`. Then use the resulting hypothesis. Set `F : ℕ → Finset ι` to `fun n => (hfin n).toFinset`. Establish `hF : ∀ n i, i ∉ F n → q i ∈ bk.J ^ n` using `fun n i hi => by`. Simplify `hi` using `[F]`.

Set `I : Ideal (Ainf l)` to `bk.J.map bk.ev`. Establish `key : ∀ n i, i ∉ F n → bk.ev (q i) ∈ I ^ n` using `fun n i hi => by`. Rewrite using `[← Ideal.map_pow]`. Conclude with `Ideal.mem_map_of_mem _ (hF n i hi)`. Set `f : ℕ → Ainf l` to `fun n => ∑ i ∈ F n, bk.ev (q i) * TB.b i`.

Establish `hmono : ∀ {m n : ℕ}, m ≤ n → F m ⊆ F n` using `fun {m n} hmn i hi => by`. Simplify using `only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hi ⊢`. Conclude with `fun hn => hi (Ideal.pow_le_pow_right hmn hn)`. Establish `hsm : ∀ n : ℕ, (I ^ n • (⊤ : Submodule (Ainf l) (Ainf l))) = I ^ n` using `fun n => by`. Rewrite using `[smul_eq_mul, Ideal.mul_top]`.

Establish `hcauchy : ∀ {m n : ℕ}, m ≤ n → f m ≡ f n [SMOD I ^ m • (⊤ : Submodule (Ainf l) (Ainf l))]`. Introduce `m n hmn`. Rewrite using `[SModEq.sub_mem, hsm]`. Establish `e : f m - f n = -∑ i ∈ F n \ F m, bk.ev (q i) * TB.b i`. Simplify using `only [f]`.

Rewrite using `[← Finset.sum_sdiff (hmono hmn)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `neg_mem (Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ (key m i ?_))` and prove the remaining obligations. Conclude with `(Finset.mem_sdiff.1 hi).2`.

Use `haveI : IsAdicComplete I (Ainf l) := TB.complete`. Take `⟨L, hL⟩` from `IsPrecomplete.prec (inferInstance : IsPrecomplete I (Ainf l)) hcauchy`. Use `⟨L, ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`. Use `IsHausdorff.haus (inferInstance : IsHausdorff I (Ainf l)) _ fun n => ?_` and prove the remaining obligations.

Rewrite using `[SModEq.sub_mem, sub_zero, hsm]`. Establish `happ` using `TB.approx a n (F n) fun i hi => by rw [hq1 i]; exact Ideal.mul_mem_left _ _ (hF n i hi)`. Rewrite `happ` using `[Ideal.map_pow]`. Establish `hs : ∑ i ∈ F n, bk.ev (TB.c i a) * TB.b i = bk.ev g * f n`. Simplify using `only [f, Finset.mul_sum, hq1, map_mul, mul_assoc]`.

Rewrite `happ` using `[hs]`. Establish `hLn` using `hL n`. Rewrite `hLn` using `[SModEq.sub_mem, hsm]`. Establish `e : a - bk.ev g * L = (a - bk.ev g * f n) + bk.ev g * (f n - L)` using `by ring`. Rewrite using `[e]`.

Conclude with `add_mem happ (Ideal.mul_mem_left _ _ hLn)`.
-/
theorem lift (bk : BK K) (g : bk.S) (hreg : toDisc l (X : bk.S) bk.ρ₀ g ∈ nonZeroDivisors (bk.DS bk.ρ₀))
    (hdiv : ∀ s : bk.S, toDisc l (X : bk.S) bk.ρ₀ g ∣ toDisc l (X : bk.S) bk.ρ₀ s → g ∣ s)
    (a : Ainf l) (h : bk.iS g ∣ bk.iA a) : bk.ev g ∣ a := by
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  obtain ⟨h0, h1⟩ := ρ₀_pos_lt bk
  have hj : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 h0
  have hjm := isDiscMap_map (l := l) (u := (X : bk.S)) (ρ := bk.ρ₀) (u' := bk.ev X) (ρ' := bk.ρ₀) bk.ev hj
  obtain ⟨cD, hc1, hc2, -, hc4, -⟩ :=
    GlobalTheory.BSP.disc_coefficients l K bk (Ainf l) bk.ev ι TB bk.ρ₀ h0 h1 _ hjm
  obtain ⟨y, hy⟩ := h
  have hiS : bk.iS g = Disc.map bk.ev hj (toDisc l (X : bk.S) bk.ρ₀ g) := (hjm.ext g).symm
  have hq : ∀ i, ∃ q : bk.S, TB.c i a = g * q ∧ toDisc l (X : bk.S) bk.ρ₀ q = cD i y := by
    intro i
    have e : toDisc l (X : bk.S) bk.ρ₀ (TB.c i a) = toDisc l (X : bk.S) bk.ρ₀ g * cD i y := by
      rw [← hc1, show toDisc l (bk.ev X) bk.ρ₀ a = bk.iA a from rfl, hy, hiS, hc2]
    obtain ⟨q, hq⟩ := hdiv _ ⟨_, e⟩
    refine ⟨q, hq, ?_⟩
    rw [hq, map_mul] at e
    exact (mul_cancel_left_mem_nonZeroDivisors hreg).1 e
  choose q hq1 hq2 using hq
  classical
  haveI : IsAdicComplete bk.J bk.S := bk.complete
  have hsmall := (GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk bk.S (RingHom.id bk.S) Unit
    (TopBasis.self bk.J) bk.ρ₀ h0 h1).2.1
  have hfin : ∀ n, {i | q i ∉ bk.J ^ n}.Finite := by
    intro n
    obtain ⟨r, hr, hr'⟩ := hsmall n
    have hev : ∀ᶠ i in Filter.cofinite, ‖cD i y‖ < r :=
      (hc4 y).norm.eventually (gt_mem_nhds (by simpa using hr))
    refine (Filter.eventually_cofinite.1 hev).subset fun i hi hlt => hi ?_
    have h5 : ‖toDisc l (X : bk.S) bk.ρ₀ (q i)‖ ≤ r := by rw [hq2 i]; exact hlt.le
    have h6 := hr' (q i) h5
    rwa [Ideal.map_id] at h6
  let F : ℕ → Finset ι := fun n => (hfin n).toFinset
  have hF : ∀ n i, i ∉ F n → q i ∈ bk.J ^ n := fun n i hi => by
    simpa [F] using hi
  let I : Ideal (Ainf l) := bk.J.map bk.ev
  have key : ∀ n i, i ∉ F n → bk.ev (q i) ∈ I ^ n := fun n i hi => by
    rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ (hF n i hi)
  let f : ℕ → Ainf l := fun n => ∑ i ∈ F n, bk.ev (q i) * TB.b i
  have hmono : ∀ {m n : ℕ}, m ≤ n → F m ⊆ F n := fun {m n} hmn i hi => by
    simp only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hi ⊢
    exact fun hn => hi (Ideal.pow_le_pow_right hmn hn)
  have hsm : ∀ n : ℕ, (I ^ n • (⊤ : Submodule (Ainf l) (Ainf l))) = I ^ n := fun n => by
    rw [smul_eq_mul, Ideal.mul_top]
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → f m ≡ f n [SMOD I ^ m • (⊤ : Submodule (Ainf l) (Ainf l))] := by
    intro m n hmn
    rw [SModEq.sub_mem, hsm]
    have e : f m - f n = -∑ i ∈ F n \ F m, bk.ev (q i) * TB.b i := by
      simp only [f]
      rw [← Finset.sum_sdiff (hmono hmn)]; ring
    rw [e]
    refine neg_mem (Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ (key m i ?_))
    exact (Finset.mem_sdiff.1 hi).2
  haveI : IsAdicComplete I (Ainf l) := TB.complete
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I (Ainf l)) hcauchy
  refine ⟨L, ?_⟩
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (inferInstance : IsHausdorff I (Ainf l)) _ fun n => ?_
  rw [SModEq.sub_mem, sub_zero, hsm]
  have happ := TB.approx a n (F n) fun i hi => by rw [hq1 i]; exact Ideal.mul_mem_left _ _ (hF n i hi)
  rw [Ideal.map_pow] at happ
  have hs : ∑ i ∈ F n, bk.ev (TB.c i a) * TB.b i = bk.ev g * f n := by
    simp only [f, Finset.mul_sum, hq1, map_mul, mul_assoc]
  rw [hs] at happ
  have hLn := hL n
  rw [SModEq.sub_mem, hsm] at hLn
  have e : a - bk.ev g * L = (a - bk.ev g * f n) + bk.ev g * (f n - L) := by ring
  rw [e]
  exact add_mem happ (Ideal.mul_mem_left _ _ hLn)

end GlobalTheory.BSP.DiscDvd

namespace GlobalTheory.BSP

/- English proof (translation)
Introduce `l _ K bk a`. Establish `hE : toDisc l (X : bk.S) bk.ρ₀ bk.E ≠ 0` using `fun h0 => bk.E_ne_zero (DiscDvd.toDisc_inj bk (h0.trans (map_zero _).symm))`. Establish `hX : toDisc l (X : bk.S) bk.ρ₀ X ≠ 0` using `fun h0 => PowerSeries.X_ne_zero (DiscDvd.toDisc_inj bk (h0.trans (map_zero _).symm))`. Use `⟨fun m h => ?_, fun h => DiscDvd.lift bk X (DiscDvd.mem_nzd bk hX) (DiscDvd.dvd_X bk) a h⟩` and prove the remaining obligations. Rewrite `h`, the goal using `[← map_pow]`.

Use `DiscDvd.lift bk (bk.E ^ m) ?_ (fun s hs => DiscDvd.dvd_E_pow bk m s ?_) a h` and prove the remaining obligations. Rewrite using `[map_pow]`. Conclude with `pow_mem (DiscDvd.mem_nzd bk hE) m`. Rewrite `hs` using `[map_pow]`. Then use the resulting hypothesis.
-/
theorem ainf_dvd_of_disc_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (a : Ainf l),
    (∀ m : ℕ, bk.iS bk.E ^ m ∣ bk.iA a → bk.ev bk.E ^ m ∣ a) ∧ (bk.iS X ∣ bk.iA a → bk.ev X ∣ a) := by
  intro l _ K bk a
  have hE : toDisc l (X : bk.S) bk.ρ₀ bk.E ≠ 0 := fun h0 =>
    bk.E_ne_zero (DiscDvd.toDisc_inj bk (h0.trans (map_zero _).symm))
  have hX : toDisc l (X : bk.S) bk.ρ₀ X ≠ 0 := fun h0 =>
    PowerSeries.X_ne_zero (DiscDvd.toDisc_inj bk (h0.trans (map_zero _).symm))
  refine ⟨fun m h => ?_, fun h => DiscDvd.lift bk X (DiscDvd.mem_nzd bk hX) (DiscDvd.dvd_X bk) a h⟩
  rw [← map_pow] at h ⊢
  refine DiscDvd.lift bk (bk.E ^ m) ?_ (fun s hs => DiscDvd.dvd_E_pow bk m s ?_) a h
  · rw [map_pow]; exact pow_mem (DiscDvd.mem_nzd bk hE) m
  · rwa [map_pow] at hs

end GlobalTheory.BSP
