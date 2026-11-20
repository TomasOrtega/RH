import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.ContDiffOfContDiffOnZeroOff
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LogInt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenCoord
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood

namespace ReciprocityTheory.AnForm.A

open MeasureTheory Filter Topology

open scoped ContDiff

noncomputable section

variable {n : ℕ}

/- English proof (translation)
Take `⟨hh, hhc⟩` from `hDens_props i hp`. Take `⟨hU, hv, hvc, hvU, hφ⟩` from `hp`. Establish `hg : ContDiff ℝ 3 (fun y : Fin (n + 1) → ℂ => gReg ε (y i))` using `(gReg_contDiff hε).comp (contDiff_apply ℝ ℂ i)`. Establish `h1` using `(parts_thm n φ v (fun y => gReg ε (y i)) U ⟨hU, hv.contDiffOn, hvc, hvU, hg.contDiffOn, fun k => by exact_mod_cast contDiffOn_infty.1 (hφ k) 3⟩).2.2.2.2`. Establish `h2` using `(parts_thm n (psiRef n) (hDens i v φ) (fun y => gReg ε (y i)) Set.univ ⟨isOpen_univ, hh.contDiffOn, hhc, Set.subset_univ _, hg.contDiffOn, fun k => (psiRef_contDiff k).contDiffOn⟩).2.2.2.2`.

Simplify using `only [maInt, Measure.restrict_univ] at h1 h2`. Establish `e1 : ∫ z in U, gReg ε (z i) * maDens (Fin.cons v φ) z = ∫ z, gReg ε (z i) * maDens (Fin.cons v φ) z` using `setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by`. Rewrite using `[maDens_cons_eq_zero φ (fun h => hz (hvU h)), mul_zero]`. Establish `e2 : ∫ z in U, v z * maDens (Fin.cons (fun y => gReg ε (y i)) φ) z = ∫ z, v z * maDens (Fin.cons (fun y => gReg ε (y i)) φ) z` using `setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by`. Rewrite using `[image_eq_zero_of_notMem_tsupport (fun h => hz (hvU h)), zero_mul]`.

Rewrite `h1` using `[e1, e2]`. Unfold `densV`. Rewrite using `[h1, h2]`. Use `integral_congr_ae (Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Simplify using `only [maDens_cons_gReg hε, minorDens_psiRef, hDens]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_gReg_eq (i : Fin (n + 1)) {U : Set (Fin (n + 1) → ℂ)}
    {v : (Fin (n + 1) → ℂ) → ℝ} {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} (hp : PoincareLelongData U v φ)
    {ε : ℝ} (hε : 0 < ε) :
    ∫ z, gReg ε (z i) * densV v φ z =
      ∫ z, gReg ε (z i) * maDens (Fin.cons (hDens i v φ) (psiRef n)) z := by
  obtain ⟨hh, hhc⟩ := hDens_props i hp
  obtain ⟨hU, hv, hvc, hvU, hφ⟩ := hp
  have hg : ContDiff ℝ 3 (fun y : Fin (n + 1) → ℂ => gReg ε (y i)) :=
    (gReg_contDiff hε).comp (contDiff_apply ℝ ℂ i)
  have h1 := (parts_thm n φ v (fun y => gReg ε (y i)) U
    ⟨hU, hv.contDiffOn, hvc, hvU, hg.contDiffOn,
      fun k => by exact_mod_cast contDiffOn_infty.1 (hφ k) 3⟩).2.2.2.2
  have h2 := (parts_thm n (psiRef n) (hDens i v φ) (fun y => gReg ε (y i)) Set.univ
    ⟨isOpen_univ, hh.contDiffOn, hhc, Set.subset_univ _, hg.contDiffOn,
      fun k => (psiRef_contDiff k).contDiffOn⟩).2.2.2.2
  simp only [maInt, Measure.restrict_univ] at h1 h2
  have e1 : ∫ z in U, gReg ε (z i) * maDens (Fin.cons v φ) z =
      ∫ z, gReg ε (z i) * maDens (Fin.cons v φ) z :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      rw [maDens_cons_eq_zero φ (fun h => hz (hvU h)), mul_zero]
  have e2 : ∫ z in U, v z * maDens (Fin.cons (fun y => gReg ε (y i)) φ) z =
      ∫ z, v z * maDens (Fin.cons (fun y => gReg ε (y i)) φ) z :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hvU h)), zero_mul]
  rw [e1, e2] at h1
  unfold densV
  rw [h1, h2]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [maDens_cons_gReg hε, minorDens_psiRef, hDens]
  ring

/- English proof (translation)
Take `⟨hh, hhc⟩` from `hDens_props i hp`. Establish `hlog` using `logCoordLocInt_thm (n + 1) i`. Establish `t1` using `tendsto_integral_gReg i (densV v φ) (maDens_cons_continuous hp.1 hp.2.1 hp.2.2.2.1 hp.2.2.2.2) (maDens_cons_hasCompactSupport hp.2.2.1 φ) hlog`. Establish `t2` using `tendsto_integral_gReg i (maDens (Fin.cons (hDens i v φ) (psiRef n))) (maDens_cons_continuous isOpen_univ hh (Set.subset_univ _) fun k => (psiRef_contDiff k).contDiffOn) (maDens_cons_hasCompactSupport hhc _) hlog`. Conclude with `tendsto_nhds_unique t1 (t2.congr fun k => (integral_gReg_eq i hp (by positivity)).symm)`.
-/
theorem integral_log_densV_eq (i : Fin (n + 1)) {U : Set (Fin (n + 1) → ℂ)}
    {v : (Fin (n + 1) → ℂ) → ℝ} {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} (hp : PoincareLelongData U v φ) :
    ∫ z, Real.log ‖z i‖ * densV v φ z =
      ∫ z, Real.log ‖z i‖ * maDens (Fin.cons (hDens i v φ) (psiRef n)) z := by
  obtain ⟨hh, hhc⟩ := hDens_props i hp
  have hlog := logCoordLocInt_thm (n + 1) i
  have t1 := tendsto_integral_gReg i (densV v φ)
    (maDens_cons_continuous hp.1 hp.2.1 hp.2.2.2.1 hp.2.2.2.2)
    (maDens_cons_hasCompactSupport hp.2.2.1 φ) hlog
  have t2 := tendsto_integral_gReg i (maDens (Fin.cons (hDens i v φ) (psiRef n)))
    (maDens_cons_continuous isOpen_univ hh (Set.subset_univ _)
      fun k => (psiRef_contDiff k).contDiffOn)
    (maDens_cons_hasCompactSupport hhc _) hlog
  exact tendsto_nhds_unique t1 (t2.congr fun k => (integral_gReg_eq i hp (by positivity)).symm)

/- English proof (translation)
Unfold `maDens`. Rewrite using `[hessC_cons]`. Establish `hp : (fun k => hessC (psiRef n k) z) = fun _ => 1` using `funext fun k => hessC_sum_normSq z`. Rewrite using `[hp, mdisc_cons_eq_sum]`. Unfold `kDens`.

Both sides reduce to the same expression.
-/
theorem maDens_cons_psiRef (h : (Fin (n + 1) → ℂ) → ℝ) (z : Fin (n + 1) → ℂ) :
    maDens (Fin.cons h (psiRef n)) z = kDens n *
      (∑ j, ∑ k, hessC h z j k *
        mixedCof (fun _ : Fin n => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) j k).re := by
  unfold maDens
  rw [hessC_cons]
  have hp : (fun k => hessC (psiRef n k) z) = fun _ => 1 := funext fun k => hessC_sum_normSq z
  rw [hp, mdisc_cons_eq_sum]
  unfold kDens
  rfl

/- English proof (translation)
Rewrite using `[mixedCof_diag]`. Establish `h1 : (fun _ : Fin n => ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).submatrix i.succAbove i.succAbove) = fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)`. Use function extensionality and compare the values at `_`. Conclude with `Matrix.submatrix_one _ Fin.succAbove_right_injective`. Rewrite using `[h1, mdisc_const, Matrix.det_one, mul_one]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mixedCof_one_diag (i : Fin (n + 1)) :
    mixedCof (fun _ : Fin n => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) i i =
      ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) := by
  rw [mixedCof_diag]
  have h1 : (fun _ : Fin n => ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).submatrix i.succAbove i.succAbove) =
      fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) := by
    funext _
    exact Matrix.submatrix_one _ Fin.succAbove_right_injective
  rw [h1, mdisc_const, Matrix.det_one, mul_one]
  push_cast
  ring

/- English proof (translation)
Simplify using `[hessC, levi, Complex.div_ofNat_re]`.
-/
theorem re_hessC_diag {D : ℕ} (f : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (j : Fin D) :
    (hessC f z j j).re = levi f z (Pi.single j 1) := by
  simp [hessC, levi, Complex.div_ofNat_re]

def fTerm (i : Fin (n + 1)) (h : (Fin (n + 1) → ℂ) → ℝ) (j k : Fin (n + 1))
    (z : Fin (n + 1) → ℂ) : ℝ :=
  ((Real.log ‖z i‖ : ℂ) * (hessC h z j k *
    mixedCof (fun _ : Fin n => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) j k)).re

/- English proof (translation)
Establish `hG` using `greenCoord_thm n i h hh hhc`. Distinguish the cases in `hjk : j = i ∧ k = i`. Take `⟨hj, hk⟩` from `hjk`. Rewrite using `[hj, hk]`. Establish `e : ∀ z, fTerm i h i i z = (Real.pi / 2) * (1 / ((n : ℝ) + 1)) * (Real.log ‖z i‖ * ddcCoordDens i h z)`.

Introduce `z`. Simplify using `only [fTerm, mixedCof_one_diag, Complex.re_ofReal_mul, Complex.re_mul_ofReal, re_hessC_diag, ddcCoordDens]`. Clear the denominators using the available nonvanishing facts. Establish `e' : fTerm i h i i = fun z => (Real.pi / 2) * (1 / ((n : ℝ) + 1)) * (Real.log ‖z i‖ * ddcCoordDens i h z)` using `funext e`. Rewrite using `[e', if_pos ⟨rfl, rfl⟩, integral_const_mul, hG.2]`.

Conclude with `⟨hG.1.const_mul _, rfl⟩`. Establish `hne : (j, k) ≠ (i, i)` using `fun h' => hjk ⟨(Prod.mk.inj h').1, (Prod.mk.inj h').2⟩`. Establish `hm` using `greenMixed_thm n i j k h hh hhc hne`. Use `set M := mixedCof (fun _ : Fin n => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) j k`. Establish `hi : Integrable (fun z : Fin (n + 1) → ℂ => (Real.log ‖z i‖ : ℂ) * (hessC h z j k * M))`.

Simplify `hm.1.mul_const M` using `[mul_assoc]`. Use `⟨Complex.reCLM.integrable_comp hi, ?_⟩` and prove the remaining obligations. Rewrite using `[if_neg hjk]`. Use `Complex.reCLM.integral_comp_comm hi` as an intermediate fact. Simplify using `only [Complex.reCLM_apply] at this`.

Simplify using `only [fTerm]`. Rewrite using `[this]`. Repeatedly rewrite using `[← mul_assoc]`. Rewrite using `[integral_mul_const, hm.2]`. Simplify using the standard rewrite rules.
-/
theorem fTerm_props (i : Fin (n + 1)) {h : (Fin (n + 1) → ℂ) → ℝ} (hh : ContDiff ℝ 2 h)
    (hhc : HasCompactSupport h) (j k : Fin (n + 1)) :
    Integrable (fTerm i h j k) ∧ ∫ z, fTerm i h j k z =
      if j = i ∧ k = i then
        (Real.pi / 2) * (1 / ((n : ℝ) + 1)) * ∫ w, h (Fin.insertNth i 0 w)
      else 0 := by
  have hG := greenCoord_thm n i h hh hhc
  by_cases hjk : j = i ∧ k = i
  · obtain ⟨hj, hk⟩ := hjk
    rw [hj, hk]
    have e : ∀ z, fTerm i h i i z =
        (Real.pi / 2) * (1 / ((n : ℝ) + 1)) * (Real.log ‖z i‖ * ddcCoordDens i h z) := by
      intro z
      simp only [fTerm, mixedCof_one_diag, Complex.re_ofReal_mul, Complex.re_mul_ofReal,
        re_hessC_diag, ddcCoordDens]
      field_simp
    have e' : fTerm i h i i = fun z =>
        (Real.pi / 2) * (1 / ((n : ℝ) + 1)) * (Real.log ‖z i‖ * ddcCoordDens i h z) := funext e
    rw [e', if_pos ⟨rfl, rfl⟩, integral_const_mul, hG.2]
    exact ⟨hG.1.const_mul _, rfl⟩
  · have hne : (j, k) ≠ (i, i) := fun h' => hjk ⟨(Prod.mk.inj h').1, (Prod.mk.inj h').2⟩
    have hm := greenMixed_thm n i j k h hh hhc hne
    set M := mixedCof (fun _ : Fin n => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) j k
    have hi : Integrable (fun z : Fin (n + 1) → ℂ =>
        (Real.log ‖z i‖ : ℂ) * (hessC h z j k * M)) := by
      simpa [mul_assoc] using hm.1.mul_const M
    refine ⟨Complex.reCLM.integrable_comp hi, ?_⟩
    rw [if_neg hjk]
    have := Complex.reCLM.integral_comp_comm hi
    simp only [Complex.reCLM_apply] at this
    simp only [fTerm]
    rw [this]
    simp_rw [← mul_assoc]
    rw [integral_mul_const, hm.2]
    simp

/- English proof (translation)
Establish `hsplit : (fun z => Real.log ‖z i‖ * maDens (Fin.cons h (psiRef n)) z) = fun z => kDens n * ∑ j, ∑ k, fTerm i h j k z`. Use function extensionality and compare the values at `z`. Rewrite using `[maDens_cons_psiRef, Complex.re_sum]`. Simplify using `only [fTerm, Complex.re_ofReal_mul, Complex.re_sum, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring`.

Establish `hint : ∀ j, ∫ z, ∑ k, fTerm i h j k z = ∑ k, ∫ z, fTerm i h j k z` using `fun j => integral_finset_sum _ fun k _ => (fTerm_props i hh hhc j k).1`. Establish `hval : ∀ j k, ∫ z, fTerm i h j k z = if j = i ∧ k = i then (Real.pi / 2) * (1 / ((n : ℝ) + 1)) * ∫ w, h (Fin.insertNth i 0 w) else 0` using `fun j k => (fTerm_props i hh hhc j k).2`. Rewrite using `[hsplit, integral_const_mul, integral_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ => (fTerm_props i hh hhc j k).1]`. Simplify using `only [hint, hval]`. Simplify using `[ite_and]`.
-/
theorem integral_log_maDens_psiRef (i : Fin (n + 1)) {h : (Fin (n + 1) → ℂ) → ℝ}
    (hh : ContDiff ℝ 2 h) (hhc : HasCompactSupport h) :
    ∫ z, Real.log ‖z i‖ * maDens (Fin.cons h (psiRef n)) z =
      kDens n * ((Real.pi / 2) * (1 / ((n : ℝ) + 1)) * ∫ w, h (Fin.insertNth i 0 w)) := by
  classical
  have hsplit : (fun z => Real.log ‖z i‖ * maDens (Fin.cons h (psiRef n)) z) =
      fun z => kDens n * ∑ j, ∑ k, fTerm i h j k z := by
    funext z
    rw [maDens_cons_psiRef, Complex.re_sum]
    simp only [fTerm, Complex.re_ofReal_mul, Complex.re_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have hint : ∀ j, ∫ z, ∑ k, fTerm i h j k z = ∑ k, ∫ z, fTerm i h j k z := fun j =>
    integral_finset_sum _ fun k _ => (fTerm_props i hh hhc j k).1
  have hval : ∀ j k, ∫ z, fTerm i h j k z = if j = i ∧ k = i then
      (Real.pi / 2) * (1 / ((n : ℝ) + 1)) * ∫ w, h (Fin.insertNth i 0 w) else 0 :=
    fun j k => (fTerm_props i hh hhc j k).2
  rw [hsplit, integral_const_mul, integral_finset_sum _ fun j _ =>
    integrable_finset_sum _ fun k _ => (fTerm_props i hh hhc j k).1]
  simp only [hint, hval]
  simp [ite_and]

/- English proof (translation)
Take `⟨hU, hv, hvc, hvU, hφ⟩` from `hp`. Distinguish the cases in `hw : hypInclAt i w ∈ U`. Establish `hr : ∀ k, hessC (φ k ∘ hypInclAt i) w = (hessC (φ k) (hypInclAt i w)).submatrix i.succAbove i.succAbove` using `fun k => hessCRestrict_thm n (φ k) U i hU (by exact_mod_cast contDiffOn_infty.1 (hφ k) 2) w hw`. Simplify using `only [densHypAt, maDens, hr]`. Simplify using `only [hDens, minorDens]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h0 : v (hypInclAt i w) = 0` using `image_eq_zero_of_notMem_tsupport fun h => hw (hvU h)`. Simplify using `[hDens, h0]`.
-/
theorem v_densHypAt_eq (i : Fin (n + 1)) {U : Set (Fin (n + 1) → ℂ)}
    {v : (Fin (n + 1) → ℂ) → ℝ} {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} (hp : PoincareLelongData U v φ)
    (w : Fin n → ℂ) :
    v (hypInclAt i w) * densHypAt i φ w =
      ((n.factorial : ℝ) * (2 / Real.pi) ^ n) * hDens i v φ (hypInclAt i w) := by
  obtain ⟨hU, hv, hvc, hvU, hφ⟩ := hp
  by_cases hw : hypInclAt i w ∈ U
  · have hr : ∀ k, hessC (φ k ∘ hypInclAt i) w =
        (hessC (φ k) (hypInclAt i w)).submatrix i.succAbove i.succAbove := fun k =>
      hessCRestrict_thm n (φ k) U i hU (by exact_mod_cast contDiffOn_infty.1 (hφ k) 2) w hw
    simp only [densHypAt, maDens, hr]
    simp only [hDens, minorDens]
    ring
  · have h0 : v (hypInclAt i w) = 0 := image_eq_zero_of_notMem_tsupport fun h => hw (hvU h)
    simp [hDens, h0]

/- English proof (translation)
Unfold `hypInclAt`. Conclude with `Continuous.finInsertNth i continuous_const continuous_id`.
-/
theorem continuous_hypInclAt (i : Fin (n + 1)) : Continuous (hypInclAt (n := n) i) := by
  unfold hypInclAt
  exact Continuous.finInsertNth i continuous_const continuous_id

/- English proof (translation)
Establish `hr : Continuous (fun z : Fin (n + 1) → ℂ => Fin.removeNth i z)` using `continuous_pi fun j => continuous_apply _`. Establish `hK : IsCompact ((fun z : Fin (n + 1) → ℂ => Fin.removeNth i z) '' tsupport h)` using `hhc.image hr`. Unfold `HasCompactSupport`. Use `IsCompact.of_isClosed_subset hK (isClosed_tsupport _) ?_` and prove the remaining obligations. Use `closure_minimal ?_ hK.isClosed` and prove the remaining obligations.

Introduce `w hw`. Conclude with `⟨hypInclAt i w, subset_tsupport _ hw, by simp [hypInclAt, Fin.removeNth_insertNth]⟩`.
-/
theorem hasCompactSupport_comp_hypInclAt (i : Fin (n + 1)) {h : (Fin (n + 1) → ℂ) → ℝ}
    (hhc : HasCompactSupport h) : HasCompactSupport (fun w : Fin n → ℂ => h (hypInclAt i w)) := by
  have hr : Continuous (fun z : Fin (n + 1) → ℂ => Fin.removeNth i z) :=
    continuous_pi fun j => continuous_apply _
  have hK : IsCompact ((fun z : Fin (n + 1) → ℂ => Fin.removeNth i z) '' tsupport h) := hhc.image hr
  unfold HasCompactSupport
  refine IsCompact.of_isClosed_subset hK (isClosed_tsupport _) ?_
  refine closure_minimal ?_ hK.isClosed
  intro w hw
  exact ⟨hypInclAt i w, subset_tsupport _ hw, by simp [hypInclAt, Fin.removeNth_insertNth]⟩

/- English proof (translation)
Establish `hπ : Real.pi ≠ 0` using `Real.pi_ne_zero`. Establish `hn : (n : ℝ) + 1 ≠ 0` using `by positivity`. Unfold `kDens`. Rewrite using `[Nat.factorial_succ, pow_succ]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts.
-/
theorem kDens_mul : kDens n * (Real.pi / 2 * (1 / ((n : ℝ) + 1))) =
    (n.factorial : ℝ) * (2 / Real.pi) ^ n := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  unfold kDens
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

/- English proof (translation)
Take `⟨hh, hhc⟩` from `hDens_props i hp`. Establish `hcont : Continuous (densV v φ)` using `maDens_cons_continuous hp.1 hp.2.1 hp.2.2.2.1 hp.2.2.2.2`. Establish `hcs : HasCompactSupport (densV v φ)` using `maDens_cons_hasCompactSupport hp.2.2.1 φ`. Establish `hR : (fun w => v (hypInclAt i w) * densHypAt i φ w) = fun w => ((n.factorial : ℝ) * (2 / Real.pi) ^ n) * hDens i v φ (hypInclAt i w)`. Use function extensionality and compare the values at `(v_densHypAt_eq i hp)`.

Establish `hRi : Integrable (fun w : Fin n → ℂ => hDens i v φ (hypInclAt i w))` using `(hh.continuous.comp (continuous_hypInclAt i)).integrable_of_hasCompactSupport (hasCompactSupport_comp_hypInclAt i hhc)`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `(logCoordLocInt_thm (n + 1) i).integrable_smul_left_of_hasCompactSupport hcont hcs` as an intermediate fact. Simplify `this` using `[smul_eq_mul, mul_comm]`. Rewrite using `[hR]`.

Conclude with `hRi.const_mul _`. Rewrite using `[integral_log_densV_eq i hp, integral_log_maDens_psiRef i (hh.of_le (by norm_num)) hhc, hR, integral_const_mul, ← kDens_mul]`. Simplify using `only [hypInclAt]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_norm_integral_at_coordinate (n : ℕ) (i : Fin (n + 1)) (U : Set (Fin (n + 1) → ℂ))
    (v : (Fin (n + 1) → ℂ) → ℝ) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (hp : PoincareLelongData U v φ) :
    Integrable (fun z => Real.log ‖z i‖ * densV v φ z) volume ∧
    Integrable (fun w => v (hypInclAt i w) * densHypAt i φ w) volume ∧
    ∫ z, Real.log ‖z i‖ * densV v φ z = ∫ w, v (hypInclAt i w) * densHypAt i φ w := by
  obtain ⟨hh, hhc⟩ := hDens_props i hp
  have hcont : Continuous (densV v φ) := maDens_cons_continuous hp.1 hp.2.1 hp.2.2.2.1 hp.2.2.2.2
  have hcs : HasCompactSupport (densV v φ) := maDens_cons_hasCompactSupport hp.2.2.1 φ
  have hR : (fun w => v (hypInclAt i w) * densHypAt i φ w) =
      fun w => ((n.factorial : ℝ) * (2 / Real.pi) ^ n) * hDens i v φ (hypInclAt i w) :=
    funext (v_densHypAt_eq i hp)
  have hRi : Integrable (fun w : Fin n → ℂ => hDens i v φ (hypInclAt i w)) :=
    (hh.continuous.comp (continuous_hypInclAt i)).integrable_of_hasCompactSupport
      (hasCompactSupport_comp_hypInclAt i hhc)
  refine ⟨?_, ?_, ?_⟩
  · have := (logCoordLocInt_thm (n + 1) i).integrable_smul_left_of_hasCompactSupport hcont hcs
    simpa [smul_eq_mul, mul_comm] using this
  · rw [hR]; exact hRi.const_mul _
  · rw [integral_log_densV_eq i hp, integral_log_maDens_psiRef i (hh.of_le (by norm_num)) hhc, hR,
      integral_const_mul, ← kDens_mul]
    simp only [hypInclAt]
    ring

/- English proof (translation)
Establish `ha : AnalyticOnNhd ℂ u U` using `ReciprocityTheory.AnForm.Osgood.osgood D U u hU hu`. Establish `hc : ContDiffOn ℝ ∞ u U` using `(ha.contDiffOn hU.uniqueDiffOn).restrict_scalars ℝ`. Establish `h2 : ContDiffOn ℝ ∞ (fun z => ‖u z‖ ^ 2) U` using `(contDiff_norm_sq ℝ).comp_contDiffOn hc`. Establish `h3 : ContDiffOn ℝ ∞ (fun z => (1 / 2 : ℝ) * Real.log (‖u z‖ ^ 2)) U` using `contDiffOn_const.mul (h2.log fun z hz => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hu0 z hz)))`. Use `h3.congr fun z _ => ?_` and prove the remaining obligations.

Rewrite using `[Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_norm_contDiffOn {D : ℕ} {U : Set (Fin D → ℂ)} (hU : IsOpen U)
    {u : (Fin D → ℂ) → ℂ} (hu : DifferentiableOn ℂ u U) (hu0 : ∀ z ∈ U, u z ≠ 0) :
    ContDiffOn ℝ ∞ (fun z => Real.log ‖u z‖) U := by
  have ha : AnalyticOnNhd ℂ u U := ReciprocityTheory.AnForm.Osgood.osgood D U u hU hu
  have hc : ContDiffOn ℝ ∞ u U := (ha.contDiffOn hU.uniqueDiffOn).restrict_scalars ℝ
  have h2 : ContDiffOn ℝ ∞ (fun z => ‖u z‖ ^ 2) U := (contDiff_norm_sq ℝ).comp_contDiffOn hc
  have h3 : ContDiffOn ℝ ∞ (fun z => (1 / 2 : ℝ) * Real.log (‖u z‖ ^ 2)) U :=
    contDiffOn_const.mul (h2.log fun z hz => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hu0 z hz)))
  refine h3.congr fun z _ => ?_
  rw [Real.log_pow]
  push_cast
  ring

/- English proof (translation)
Take `⟨hU, hv, hvc, hvU, hφ⟩` from `hp`. Establish `hl` using `log_norm_contDiffOn hU hu hu0`. Establish `hP` using `parts_thm n φ v (fun z => Real.log ‖u z‖) U ⟨hU, hv.contDiffOn, hvc, hvU, by exact_mod_cast contDiffOn_infty.1 hl 3, fun k => by exact_mod_cast contDiffOn_infty.1 (hφ k) 3⟩`. Establish `hsupp : Function.support (fun z => Real.log ‖u z‖ * densV v φ z) ⊆ U`. Introduce `z hz`.

Assume the negation of the conclusion as `hzU`. Apply `hz` to reduce the goal to its premises. Use `show Real.log ‖u z‖ * maDens (Fin.cons v φ) z = 0`. Rewrite using `[maDens_cons_eq_zero φ (fun h => hzU (hvU h)), mul_zero]`. Establish `hzero : ∀ z ∈ U, maDens (Fin.cons (fun z => Real.log ‖u z‖) φ) z = 0`.

Introduce `z hz`. Unfold `maDens`. Rewrite using `[hessC_cons, hessC_log_norm u z (ReciprocityTheory.AnForm.Osgood.osgood _ U u hU hu z hz) (hu0 z hz), mdisc_cons_zero]`. Simplify using the standard rewrite rules. Use `⟨(integrableOn_iff_integrable_of_support_subset hsupp).1 hP.2.1, ?_⟩` and prove the remaining obligations.

Establish `h5` using `hP.2.2.2.2`. Simplify using `only [maInt] at h5`. Establish `e : ∫ z, Real.log ‖u z‖ * densV v φ z = ∫ z in U, Real.log ‖u z‖ * densV v φ z` using `(setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => Function.notMem_support.1 fun h => hz (hsupp h)).symm`. Rewrite using `[e]`. Use `show ∫ z in U, Real.log ‖u z‖ * maDens (Fin.cons v φ) z = 0`.

Rewrite using `[h5]`. Conclude with `setIntegral_eq_zero_of_forall_eq_zero fun z hz => by rw [hzero z hz, mul_zero]`.
-/
theorem unit_part {U : Set (Fin (n + 1) → ℂ)} {v : (Fin (n + 1) → ℂ) → ℝ}
    {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} (hp : PoincareLelongData U v φ) {u : (Fin (n + 1) → ℂ) → ℂ}
    (hu : DifferentiableOn ℂ u U) (hu0 : ∀ z ∈ U, u z ≠ 0) :
    Integrable (fun z => Real.log ‖u z‖ * densV v φ z) ∧
      ∫ z, Real.log ‖u z‖ * densV v φ z = 0 := by
  obtain ⟨hU, hv, hvc, hvU, hφ⟩ := hp
  have hl := log_norm_contDiffOn hU hu hu0
  have hP := parts_thm n φ v (fun z => Real.log ‖u z‖) U
    ⟨hU, hv.contDiffOn, hvc, hvU, by exact_mod_cast contDiffOn_infty.1 hl 3,
      fun k => by exact_mod_cast contDiffOn_infty.1 (hφ k) 3⟩
  have hsupp : Function.support (fun z => Real.log ‖u z‖ * densV v φ z) ⊆ U := by
    intro z hz
    by_contra hzU
    apply hz
    show Real.log ‖u z‖ * maDens (Fin.cons v φ) z = 0
    rw [maDens_cons_eq_zero φ (fun h => hzU (hvU h)), mul_zero]
  have hzero : ∀ z ∈ U, maDens (Fin.cons (fun z => Real.log ‖u z‖) φ) z = 0 := by
    intro z hz
    unfold maDens
    rw [hessC_cons, hessC_log_norm u z (ReciprocityTheory.AnForm.Osgood.osgood _ U u hU hu z hz) (hu0 z hz),
      mdisc_cons_zero]
    simp
  refine ⟨(integrableOn_iff_integrable_of_support_subset hsupp).1 hP.2.1, ?_⟩
  have h5 := hP.2.2.2.2
  simp only [maInt] at h5
  have e : ∫ z, Real.log ‖u z‖ * densV v φ z = ∫ z in U, Real.log ‖u z‖ * densV v φ z :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz =>
      Function.notMem_support.1 fun h => hz (hsupp h)).symm
  rw [e]
  show ∫ z in U, Real.log ‖u z‖ * maDens (Fin.cons v φ) z = 0
  rw [h5]
  exact setIntegral_eq_zero_of_forall_eq_zero fun z hz => by rw [hzero z hz, mul_zero]

end

end ReciprocityTheory.AnForm.A
