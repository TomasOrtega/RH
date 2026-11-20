import Mathlib
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Definitions.Foundations.TrueColumnChoicesHeckeCharReferenceEqOne

noncomputable section

open NumberField IsDedekindDomain Filter Topology

namespace GlobalTheory.Mem.Chr.TieModel

open Formalism.BasicNotions Formalism.FrobeniusOrbits

/- English proof (translation)
Establish `key : ∀ x : L, ∑ i, (m i : ℂ) * σ i x = 0`. Introduce `x`. Set `f : ℂ → ℂ` to `fun t => ∏ i, (1 + t * σ i x) ^ m i`. Establish `hd : ∀ i ∈ (Finset.univ : Finset I), HasDerivAt (fun t : ℂ => (1 + t * σ i x) ^ m i) ((m i : ℂ) * σ i x) 0`. Introduce `i _`.

Establish `h1 : HasDerivAt (fun t : ℂ => 1 + t * σ i x) (σ i x) 0`. Simplify using `using ((hasDerivAt_id (0 : ℂ)).mul_const (σ i x)).const_add 1`. Establish `h2` using `(hasDerivAt_zpow (m i) ((fun t : ℂ => 1 + t * σ i x) 0) (Or.inl (by simp))).comp (0 : ℂ) h1`. Simplify `h2` using `[Function.comp_def]`. Establish `hf : HasDerivAt f (∑ i, (m i : ℂ) * σ i x) 0`.

Use `HasDerivAt.fun_finset_prod hd` as an intermediate fact. Simplify `this` using `[f]`. Establish `hs` using `hasDerivAt_iff_tendsto_slope.1 hf`. Establish `hu : Tendsto (fun n : ℕ => ((1 : ℂ) / ((n : ℂ) + 1))) atTop (𝓝[≠] 0)`. Use `tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ), Eventually.of_forall fun n => ?_⟩` and prove the remaining obligations.

Conclude with `one_div_ne_zero (Nat.cast_add_one_ne_zero n)`. Establish `hfin : ∀ᶠ n : ℕ in atTop, (1 + (1 / ((n : L) + 1)) * x) ≠ 0`. Rewrite using `[← Nat.cofinite_eq_atTop]`. Use `Set.Subsingleton.finite ?_` and prove the remaining obligations. Introduce `a ha b hb`.

Simplify using `only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at ha hb`. Establish `ha1 : ((a : L) + 1) ≠ 0` using `Nat.cast_add_one_ne_zero a`. Establish `hb1 : ((b : L) + 1) ≠ 0` using `Nat.cast_add_one_ne_zero b`. Clear denominators, using `at ha hb` for the nonvanishing conditions. Establish `: (a : L) = b` using `by linear_combination ha - hb`.

Conclude with `this` after adjusting the coercions. Establish `h0 : Tendsto (fun n : ℕ => slope f 0 ((1 : ℂ) / ((n : ℂ) + 1))) atTop (𝓝 0)`. Use `tendsto_const_nhds.congr' (hfin.mono fun n hn => ?_)` and prove the remaining obligations. Establish `h1` using `h _ hn`. Establish `h2 : f ((1 : ℂ) / ((n : ℂ) + 1)) = 1`.

Use `Eq.trans ?_ h1` and prove the remaining obligations. Simplify using `[f]`. Establish `h3 : f 0 = 1` using `by simp [f]`. Simplify using `only [slope, h2, h3, vsub_self, smul_zero]`. Conclude with `tendsto_nhds_unique (hs.comp hu) h0`.

Establish `li` using `(linearIndependent_monoidHom L ℂ).comp (fun i => (σ i : L →* ℂ)) (fun i j hij => hσ (RingHom.coe_monoidHom_injective hij))`. Use `Fintype.linearIndependent_iff.1 li (fun i => (m i : ℂ)) (by` as an intermediate fact. Use function extensionality and compare the values at `x`. Simplify `key x)` using `[Finset.sum_apply]`. Use function extensionality and compare the values at `i`.

Conclude with `this i` after adjusting the coercions.
-/
theorem emb_mul_indep {L I : Type} [Field L] [CharZero L] [Fintype I] (σ : I → L →+* ℂ) (hσ : Function.Injective σ)
    (m : I → ℤ) (h : ∀ k : L, k ≠ 0 → ∏ i, σ i k ^ m i = 1) : m = 0 := by
  classical
  have key : ∀ x : L, ∑ i, (m i : ℂ) * σ i x = 0 := by
    intro x
    let f : ℂ → ℂ := fun t => ∏ i, (1 + t * σ i x) ^ m i
    have hd : ∀ i ∈ (Finset.univ : Finset I),
        HasDerivAt (fun t : ℂ => (1 + t * σ i x) ^ m i) ((m i : ℂ) * σ i x) 0 := by
      intro i _
      have h1 : HasDerivAt (fun t : ℂ => 1 + t * σ i x) (σ i x) 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (σ i x)).const_add 1
      have h2 := (hasDerivAt_zpow (m i) ((fun t : ℂ => 1 + t * σ i x) 0) (Or.inl (by simp))).comp (0 : ℂ) h1
      simpa [Function.comp_def] using h2
    have hf : HasDerivAt f (∑ i, (m i : ℂ) * σ i x) 0 := by
      have := HasDerivAt.fun_finset_prod hd
      simpa [f] using this
    have hs := hasDerivAt_iff_tendsto_slope.1 hf
    have hu : Tendsto (fun n : ℕ => ((1 : ℂ) / ((n : ℂ) + 1))) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ), Eventually.of_forall fun n => ?_⟩
      exact one_div_ne_zero (Nat.cast_add_one_ne_zero n)
    have hfin : ∀ᶠ n : ℕ in atTop, (1 + (1 / ((n : L) + 1)) * x) ≠ 0 := by
      rw [← Nat.cofinite_eq_atTop]
      refine Set.Subsingleton.finite ?_
      intro a ha b hb
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at ha hb
      have ha1 : ((a : L) + 1) ≠ 0 := Nat.cast_add_one_ne_zero a
      have hb1 : ((b : L) + 1) ≠ 0 := Nat.cast_add_one_ne_zero b
      field_simp at ha hb
      have : (a : L) = b := by linear_combination ha - hb
      exact_mod_cast this
    have h0 : Tendsto (fun n : ℕ => slope f 0 ((1 : ℂ) / ((n : ℂ) + 1))) atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' (hfin.mono fun n hn => ?_)
      have h1 := h _ hn
      have h2 : f ((1 : ℂ) / ((n : ℂ) + 1)) = 1 := by
        refine Eq.trans ?_ h1; simp [f]
      have h3 : f 0 = 1 := by simp [f]
      simp only [slope, h2, h3, vsub_self, smul_zero]
    exact tendsto_nhds_unique (hs.comp hu) h0
  have li := (linearIndependent_monoidHom L ℂ).comp (fun i => (σ i : L →* ℂ))
    (fun i j hij => hσ (RingHom.coe_monoidHom_injective hij))
  have := Fintype.linearIndependent_iff.1 li (fun i => (m i : ℂ)) (by
    funext x
    simpa [Finset.sum_apply] using key x)
  funext i
  exact_mod_cast this i

/- English proof (translation)
Establish `h1 : ((‖z‖ : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast norm_ne_zero_iff.2 hz`. Establish `h2 : starRingEnd ℂ z ≠ 0` using `by simpa using hz`. Establish `h3 : z * starRingEnd ℂ z = ((‖z‖ : ℝ) : ℂ) ^ 2`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Clear the denominators using the available nonvanishing facts. Rewrite using `[← h3]`.
-/
theorem unit_sq (z : ℂ) (hz : z ≠ 0) : (z / ((‖z‖ : ℝ) : ℂ)) ^ 2 = z / starRingEnd ℂ z := by
  have h1 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
  have h2 : starRingEnd ℂ z ≠ 0 := by simpa using hz
  have h3 : z * starRingEnd ℂ z = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  field_simp
  rw [← h3]

/- English proof (translation)
Set `σ : I ⊕ I → L →+* ℂ` to `Sum.elim φ fun i => (starRingEnd ℂ).comp (φ i)`. Establish `hσ : Function.Injective σ`. Introduce and unpack `(i | i) (j | j) hij`. Conclude with `congrArg _ (h1 hij)`. Conclude with `absurd hij (h2 i j)`.

Conclude with `absurd hij.symm (h2 j i)`. Use `congrArg _ (h1 (RingHom.ext fun x => ?_))` and prove the remaining obligations. Use `congrArg (fun f : L →+* ℂ => starRingEnd ℂ (f x)) hij` as an intermediate fact. Simplify `this` using `[σ]`. Use `emb_mul_indep σ hσ (Sum.elim (n - n') (n' - n)) (fun k hk => by` as an intermediate fact.

Establish `e` using `(h (Units.mk0 k hk)).symm.trans (h' (Units.mk0 k hk))`. Simplify using `only [Units.val_mk0] at e`. Establish `hne : ∀ i, φ i k ≠ 0` using `fun i => by simpa using hk`. Establish `hu : ∀ i, φ i k / ((‖φ i k‖ : ℝ) : ℂ) ≠ 0` using `fun i => div_ne_zero (hne i) (by exact_mod_cast norm_ne_zero_iff.2 (hne i))`. Establish `e2 : ∏ i, (φ i k / ((‖φ i k‖ : ℝ) : ℂ)) ^ (n i - n' i) = 1`.

Repeatedly rewrite using `[zpow_sub₀ (hu _)]`. Rewrite using `[Finset.prod_div_distrib, e, div_self]`. Conclude with `Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hu i)`. Establish `e3` using `congrArg (· ^ 2) e2`. Simplify using `only [← Finset.prod_pow, one_pow] at e3`.

Rewrite using `[Fintype.prod_sum_type, ← Finset.prod_mul_distrib, ← e3]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_natCast, ← zpow_mul, mul_comm (n i - n' i), zpow_mul, zpow_natCast, unit_sq _ (hne i), div_zpow]`. Simplify using `only [σ, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply, RingHom.comp_apply]`. Rewrite using `[div_eq_mul_inv, ← zpow_neg, neg_sub])`.

Use function extensionality and compare the values at `i`. Use `congrFun this (Sum.inl i)` as an intermediate fact. Simplify `this` using `[sub_eq_zero]`.
-/
theorem hasInf_unique {L I : Type} [Field L] [NumberField L] [Fintype I] (φ : I → L →+* ℂ) (h1 : Function.Injective φ)
    (h2 : ∀ i j, φ i ≠ (starRingEnd ℂ).comp (φ j)) {χ : HChar L} {n n' : I → ℤ} (h : χ.HasInf φ n) (h' : χ.HasInf φ n') :
    n = n' := by
  let σ : I ⊕ I → L →+* ℂ := Sum.elim φ fun i => (starRingEnd ℂ).comp (φ i)
  have hσ : Function.Injective σ := by
    rintro (i | i) (j | j) hij
    · exact congrArg _ (h1 hij)
    · exact absurd hij (h2 i j)
    · exact absurd hij.symm (h2 j i)
    · refine congrArg _ (h1 (RingHom.ext fun x => ?_))
      have := congrArg (fun f : L →+* ℂ => starRingEnd ℂ (f x)) hij
      simpa [σ] using this
  have := emb_mul_indep σ hσ (Sum.elim (n - n') (n' - n)) (fun k hk => by
    have e := (h (Units.mk0 k hk)).symm.trans (h' (Units.mk0 k hk))
    simp only [Units.val_mk0] at e
    have hne : ∀ i, φ i k ≠ 0 := fun i => by simpa using hk
    have hu : ∀ i, φ i k / ((‖φ i k‖ : ℝ) : ℂ) ≠ 0 := fun i =>
      div_ne_zero (hne i) (by exact_mod_cast norm_ne_zero_iff.2 (hne i))
    have e2 : ∏ i, (φ i k / ((‖φ i k‖ : ℝ) : ℂ)) ^ (n i - n' i) = 1 := by
      simp_rw [zpow_sub₀ (hu _)]
      rw [Finset.prod_div_distrib, e, div_self]
      exact Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hu i)
    have e3 := congrArg (· ^ 2) e2
    simp only [← Finset.prod_pow, one_pow] at e3
    rw [Fintype.prod_sum_type, ← Finset.prod_mul_distrib, ← e3]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm (n i - n' i), zpow_mul, zpow_natCast, unit_sq _ (hne i), div_zpow]
    simp only [σ, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply, RingHom.comp_apply]
    rw [div_eq_mul_inv, ← zpow_neg, neg_sub])
  funext i
  have := congrFun this (Sum.inl i)
  simpa [sub_eq_zero] using this

/- English proof (translation)
Establish `hx : ∀ x, (χ.1 x) ^ n = 1` using `fun x => congrArg (fun ξ : HChar L => ξ.1 x) h`. Establish `hw : ∀ (w : InfinitePlace L) (y : (w.Completion)ˣ), χ.1 (infIdele L w y) = 1`. Introduce `w y`. Set `e` to `InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)`. Take `⟨z, hz⟩` from `IsAlgClosed.exists_pow_nat_eq (e (y : w.Completion)) hn`.

Establish `hz' : (e.symm z) ^ n = y` using `by rw [← map_pow, hz]; simp`. Establish `hz0 : e.symm z ≠ 0`. Introduce `h0`. Rewrite `hz'` using `[h0, zero_pow hn.ne']`. Conclude with `y.ne_zero hz'.symm`.

Establish `: y = (Units.mk0 _ hz0) ^ n` using `Units.ext (by simp [hz'])`. Rewrite using `[this, map_pow, map_pow, hx]`. Use `show χ.1 (infDiag k) = 1`. Unfold `infDiag`. Rewrite using `[MonoidHom.finset_prod_apply, map_prod]`.

Conclude with `Finset.prod_eq_one fun w _ => hw w _`.
-/
theorem inf_eq_one_of_order {L : Type} [Field L] [NumberField L] [IsTotallyComplex L] {χ : HChar L} {n : ℕ} (hn : 0 < n)
    (h : χ.OrderDvd n) (k : Lˣ) : χ.inf k = 1 := by
  have hx : ∀ x, (χ.1 x) ^ n = 1 := fun x => congrArg (fun ξ : HChar L => ξ.1 x) h
  have hw : ∀ (w : InfinitePlace L) (y : (w.Completion)ˣ), χ.1 (infIdele L w y) = 1 := by
    intro w y
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (y : w.Completion)) hn
    have hz' : (e.symm z) ^ n = y := by rw [← map_pow, hz]; simp
    have hz0 : e.symm z ≠ 0 := by
      intro h0; rw [h0, zero_pow hn.ne'] at hz'; exact y.ne_zero hz'.symm
    have : y = (Units.mk0 _ hz0) ^ n := Units.ext (by simp [hz'])
    rw [this, map_pow, map_pow, hx]
  show χ.1 (infDiag k) = 1
  unfold infDiag
  rw [MonoidHom.finset_prod_apply, map_prod]
  exact Finset.prod_eq_one fun w _ => hw w _

instance totallyComplexE {R : Ranks} (H : Formalism.BasicNotions.Host R) : IsTotallyComplex H.E := by
  haveI := H.isCMField_hostE
  infer_instance

/- English proof (translation)
Introduce `_ _ h` and use `D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))`.
-/
theorem embTau_inj (D : D7) : Function.Injective (embTau D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

/- English proof (translation)
Introduce `h`. Establish `hi : embTau D i (D.host.sqd) = Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ)` using `((factEmb D.R D.host).2 _).2 (D.eTau i).2`. Establish `hj : embTau D j (D.host.sqd) = Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ)` using `((factEmb D.R D.host).2 _).2 (D.eTau j).2`. Rewrite `hi` using `[h, RingHom.comp_apply, hj, map_mul, Complex.conj_I, Complex.conj_ofReal]`. Establish `h0 : ((Real.sqrt D.host.d : ℝ) : ℂ) = 0`.

Establish `: (2 * Complex.I) * ((Real.sqrt D.host.d : ℝ) : ℂ) = 0` using `by linear_combination -hi`. Conclude with `(mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)`. Establish `hd : 0 < D.host.d` using `D.host.hyp.2.1.pos`. Establish `: (0 : ℝ) < Real.sqrt D.host.d` using `Real.sqrt_pos.2 (by exact_mod_cast hd)`. Conclude with `this.ne' (by exact_mod_cast h0)`.
-/
theorem embTau_ne_conj (D : D7) (i j : D.what₂.Tau) : embTau D i ≠ (starRingEnd ℂ).comp (embTau D j) := by
  intro h
  have hi : embTau D i (D.host.sqd) = Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ) :=
    ((factEmb D.R D.host).2 _).2 (D.eTau i).2
  have hj : embTau D j (D.host.sqd) = Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ) :=
    ((factEmb D.R D.host).2 _).2 (D.eTau j).2
  rw [h, RingHom.comp_apply, hj, map_mul, Complex.conj_I, Complex.conj_ofReal] at hi
  have h0 : ((Real.sqrt D.host.d : ℝ) : ℂ) = 0 := by
    have : (2 * Complex.I) * ((Real.sqrt D.host.d : ℝ) : ℂ) = 0 := by linear_combination -hi
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  have hd : 0 < D.host.d := D.host.hyp.2.1.pos
  have : (0 : ℝ) < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  exact this.ne' (by exact_mod_cast h0)

/- English proof (translation)
Take `⟨n, hn, h⟩` from `h`. Take `⟨n', hn', h'⟩` from `h'`. Take `rfl` from `hasInf_unique _ (embTau_inj D) (embTau_ne_conj D) h h'`. Use function extensionality and compare the values at `i`. Use `(hn i).symm.trans (hn' i)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hasInfQ_unique (D : D7) {χ : HChar D.host.E} {a a' : D.what₂.Tau → ℚ} (h : χ.HasInfQ (embTau D) a)
    (h' : χ.HasInfQ (embTau D) a') : a = a' := by
  obtain ⟨n, hn, h⟩ := h
  obtain ⟨n', hn', h'⟩ := h'
  obtain rfl := hasInf_unique _ (embTau_inj D) (embTau_ne_conj D) h h'
  funext i
  have := (hn i).symm.trans (hn' i)
  linarith

/- English proof (translation)
Take `⟨n, hn, h⟩` from `h`. Use `⟨fun τ => n (D.eTau τ), fun τ => hn _, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[h k]`. Conclude with `(Fintype.prod_equiv D.eTau _ _ fun _ => rfl).symm`.
-/
theorem hasInfQ_tau (D : D7) {χ : HChar D.host.E} {a : D.R.Psi → ℚ} (h : χ.HasInfQ (embPsi D.host) a) :
    χ.HasInfQ (embTau D) (fun τ => a (D.eTau τ)) := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨fun τ => n (D.eTau τ), fun τ => hn _, fun k => ?_⟩
  rw [h k]
  exact (Fintype.prod_equiv D.eTau _ _ fun _ => rfl).symm

/- English proof (translation)
Take `⟨n, hn, h⟩` from `h`. Take `⟨n', hn', h'⟩` from `h'`. Use `⟨n + n', fun i => by simp [hn, hn', mul_add], fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[HChar.inf_mul, Units.val_mul, h k, h' k, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Establish `hne : φ i k ≠ 0` using `by simp`. Rewrite using `[Pi.add_apply, zpow_add₀ (div_ne_zero hne (by exact_mod_cast norm_ne_zero_iff.2 hne))]`.
-/
theorem hasInfQ_mul {L I : Type} [Field L] [NumberField L] [Fintype I] {φ : I → L →+* ℂ} {χ χ' : HChar L} {a a' : I → ℚ}
    (h : χ.HasInfQ φ a) (h' : χ'.HasInfQ φ a') : (χ * χ').HasInfQ φ (a + a') := by
  obtain ⟨n, hn, h⟩ := h
  obtain ⟨n', hn', h'⟩ := h'
  refine ⟨n + n', fun i => by simp [hn, hn', mul_add], fun k => ?_⟩
  rw [HChar.inf_mul, Units.val_mul, h k, h' k, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hne : φ i k ≠ 0 := by simp
  rw [Pi.add_apply, zpow_add₀ (div_ne_zero hne (by exact_mod_cast norm_ne_zero_iff.2 hne))]

/- English proof (translation)
Take `⟨n, hn, h⟩` from `h`. Use `⟨-n, fun i => by simp [hn], fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[HChar.inf_inv, Units.val_inv_eq_inv_val, h k, ← Finset.prod_inv_distrib]`. Simplify using the standard rewrite rules.
-/
theorem hasInfQ_inv {L I : Type} [Field L] [NumberField L] [Fintype I] {φ : I → L →+* ℂ} {χ : HChar L} {a : I → ℚ}
    (h : χ.HasInfQ φ a) : (χ⁻¹).HasInfQ φ (-a) := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨-n, fun i => by simp [hn], fun k => ?_⟩
  rw [HChar.inf_inv, Units.val_inv_eq_inv_val, h k, ← Finset.prod_inv_distrib]
  simp

variable {D : D7} {C : CharFrame D} {nch : NChoice D}

/- English proof (translation)
Take `⟨n, hn, ho⟩` from `Tp.xi_fin μ`. Conclude with `(C.isMu0 j).unitary.mul (HChar.isUnitary_of_order hn ho)`.
-/
theorem tup_unitary (Tp : TupTied D C nch) (μ : D.what₂.Tup) (j : Fin D.R.m) : (Tp.tup μ j).IsUnitary := by
  obtain ⟨n, hn, ho⟩ := Tp.xi_fin μ
  exact (C.isMu0 j).unitary.mul (HChar.isUnitary_of_order hn ho)

/- English proof (translation)
Take `⟨n, hn, ho⟩` from `Tp.xi_fin μ`. Establish `h` using `hasInfQ_tau D ((C.isMu0 j).inf.mul_triv (inf_eq_one_of_order hn ho))`. Simplify `h` using `[eExp, TupTied.tup]`.
-/
theorem tup_inf (Tp : TupTied D C nch) (μ : D.what₂.Tup) (j : Fin D.R.m) :
    (Tp.tup μ j).HasInfQ (embTau D) (fun τ => -(D.hc τ).e j) := by
  obtain ⟨n, hn, ho⟩ := Tp.xi_fin μ
  have h := hasInfQ_tau D ((C.isMu0 j).inf.mul_triv (inf_eq_one_of_order hn ho))
  simpa [eExp, TupTied.tup] using h

/- English proof (translation)
The claim follows from `hasInfQ_tau D (a := fun _ => 1 / 2) ⟨fun _ => 1, fun _ => by norm_num, C.isEta.inf⟩`.
-/
theorem eta_inf (C : CharFrame D) : C.eta.HasInfQ (embTau D) (fun _ => 1 / 2) :=
  hasInfQ_tau D (a := fun _ => 1 / 2) ⟨fun _ => 1, fun _ => by norm_num, C.isEta.inf⟩

def halfInt (D : D7) : Subgroup (HChar D.host.E) where
  carrier := {χ | χ.IsUnitary ∧ ∃ a : D.what₂.Tau → ℚ, χ.HasInfQ (embTau D) a}
  one_mem' := ⟨isClsF_one.unitary, 0, 0, fun _ => by simp, fun k => by
    show ((1 : ℂˣ) : ℂ) = _
    simp⟩
  mul_mem' := fun ⟨h, a, ha⟩ ⟨h', a', ha'⟩ => ⟨h.mul h', a + a', hasInfQ_mul ha ha'⟩
  inv_mem' := fun ⟨h, a, ha⟩ => ⟨h.inv, -a, hasInfQ_inv ha⟩

def expo (c : halfInt D) : D.what₂.Tau → ℚ := c.2.2.choose

/- English proof (translation)
The claim follows from `c.2.2.choose_spec`.
-/
theorem expo_spec (c : halfInt D) : c.1.HasInfQ (embTau D) (expo c) := c.2.2.choose_spec

def tupEl (Tp : TupTied D C nch) (μ : D.what₂.Tup) (j : Fin D.R.m) : halfInt D :=
  ⟨Tp.tup μ j, tup_unitary Tp μ j, _, tup_inf Tp μ j⟩

def tupNat (Tp : TupTied D C nch) (μ : D.what₂.Tup) (j : ℕ) : halfInt D :=
  if h : 0 < j ∧ j - 1 < D.R.m then tupEl Tp μ ⟨j - 1, h.2⟩ else 1

/- English proof (translation)
The claim follows from `dif_pos ⟨Nat.succ_pos _, j.2⟩`.
-/
theorem tupNat_succ (Tp : TupTied D C nch) (μ : D.what₂.Tup) (j : Fin D.R.m) : tupNat Tp μ (j.1 + 1) = tupEl Tp μ j :=
  dif_pos ⟨Nat.succ_pos _, j.2⟩

/- English proof (translation)
The claim follows from `hasInfQ_unique D (expo_spec c) h`.
-/
theorem expo_eq (c : halfInt D) {a : D.what₂.Tau → ℚ} (h : c.1.HasInfQ (embTau D) a) : expo c = a :=
  hasInfQ_unique D (expo_spec c) h

/- English proof (translation)
Rewrite using `[tupNat_succ]`. Conclude with `congrFun (expo_eq (tupEl Tp μ j) (tup_inf Tp μ j)) τ`.
-/
theorem expo_tupNat (Tp : TupTied D C nch) (μ : D.what₂.Tup) (j : Fin D.R.m) (τ : D.what₂.Tau) :
    expo (tupNat Tp μ (j.1 + 1)) τ = -(D.hc τ).e j := by
  rw [tupNat_succ]
  exact congrFun (expo_eq (tupEl Tp μ j) (tup_inf Tp μ j)) τ

def etaEl (C : CharFrame D) : halfInt D := ⟨C.eta, C.isEta.unitary, _, eta_inf C⟩

/- English proof (translation)
The claim follows from `congrFun (expo_eq (etaEl C) (eta_inf C)) τ`.
-/
theorem expo_etaEl (C : CharFrame D) (τ : D.what₂.Tau) : expo (etaEl C) τ = 1 / 2 :=
  congrFun (expo_eq (etaEl C) (eta_inf C)) τ

/- English proof (translation)
The claim follows from `congrFun (expo_eq (χ * χ') (hasInfQ_mul (expo_spec χ) (expo_spec χ'))) τ`.
-/
theorem expo_mul (χ χ' : halfInt D) (τ : D.what₂.Tau) : expo (χ * χ') τ = expo χ τ + expo χ' τ :=
  congrFun (expo_eq (χ * χ') (hasInfQ_mul (expo_spec χ) (expo_spec χ'))) τ

def withChars (Tp : TupTied D C nch) (X : ThetaX D)
    (th : ∀ V W, halfInt D → halfInt D → X.Sch V W →ₗ[ℂ] X.cusp V →ₗ[ℂ] X.AF W) : ThetaX D :=
  { X with
    Chr := halfInt D
    chrGrp := inferInstance
    infTy := expo
    infTy_mul := expo_mul
    chrOf := tupNat Tp
    chrOf_inf := expo_tupNat Tp
    etaT := etaEl C
    etaT_inf := fun τ => Or.inl (expo_etaEl C τ)
    etaT_pos := expo_etaEl C
    th := th }

def thetaCharacterCompatibility (Tp : TupTied D C nch) (X : ThetaX D)
    (th : ∀ V W, halfInt D → halfInt D → X.Sch V W →ₗ[ℂ] X.cusp V →ₗ[ℂ] X.AF W) :
    ThetaChrTied D C nch Tp (withChars Tp X th) where
  eChr := (halfInt D).subtype
  inj := Subtype.val_injective
  range χ := ⟨fun ⟨c, hc⟩ => hc ▸ c.2, fun h => ⟨⟨χ, h⟩, rfl⟩⟩
  infTy c := expo_spec c
  chrOf μ j := congrArg Subtype.val (tupNat_succ Tp μ j)
  etaT := rfl

/- English proof (translation)
Establish `hP : ∀ k, ∃ p : HeightOneSpectrum (𝓞 D.host.K), ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ p.asIdeal`. Introduce `k`. Establish `hg` using `D.host.g_prime k`. Establish `hnu : ¬ IsUnit ((D.host.g k : ℕ) : 𝓞 D.host.K)`. Introduce `hu`.

Establish `h1 : IsUnit (algebraMap ℤ (𝓞 D.host.K) (D.host.g k : ℤ))` using `by simpa using hu`. Establish `h2` using `(isUnit_map_iff (algebraMap ℤ (𝓞 D.host.K)) _).1 h1`. Rewrite `h2` using `[Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast]`. Conclude with `hg.ne_one h2`. Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal (Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.K)}) (by rwa [Ne, Ideal.span_singleton_eq_top])`.

Establish `hmem` using `hle (Ideal.mem_span_singleton_self _)`. Use `⟨⟨M, hM.isPrime, ?_⟩, hmem⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hg.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hmem))`. Establish `hW : ∀ k, ∃ f : (ZMod (D.host.g k))ˣ →* ℂˣ, Function.Injective f`.

Introduce `k`. Use `haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩`. Take `⟨e⟩ : Nonempty ((ZMod (D.host.g k))ˣ ≃* rootsOfUnity (Nat.card (ZMod (D.host.g k))ˣ) ℂ)` from `by haveI : NeZero (Nat.card (ZMod (D.host.g k))ˣ) := ⟨Nat.card_pos.ne'⟩`. Conclude with `⟨mulEquivOfCyclicCardEq (by first`. Consider the case `exact (Complex.card_rootsOfUnity _).symm`.

Consider the case `exact (HasEnoughRootsOfUnity.natCard_rootsOfUnity ℂ _).symm)⟩`. Conclude with `⟨(rootsOfUnity _ ℂ).subtype.comp e.toMonoidHom, Subtype.val_injective.comp e.injective⟩`. Use `choose pb hpb using hP`. Use `choose om hom using hW`. Use `choose mu hmu using hμ ⟨pb, hpb⟩ ⟨om, hom⟩`.

Take `⟨η, hη⟩` from `hη`. Take `⟨δ, hδ⟩` from `hδ`. Take `⟨δ', hδ'⟩` from `hδ'`. Conclude with `⟨⟨⟨pb, hpb⟩, ⟨om, hom⟩, mu, η, η * η, δ, δ', hmu, hη, hη.sq_chiPsi, hδ, hδ'⟩⟩`.
-/
theorem charFrame_nonempty (D : D7) (hη : EtaTExists D.host)
    (hμ : ∀ P W j, Mu0Exists (H := D.host) P W (eExp D j) j.1)
    (hδ : DeltaExists (H := D.host) D.host.pde) (hδ' : DeltaExists (H := D.host) D.host.pde') : Nonempty (CharFrame D) := by
  have hP : ∀ k, ∃ p : HeightOneSpectrum (𝓞 D.host.K), ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ p.asIdeal := by
    intro k
    have hg := D.host.g_prime k
    have hnu : ¬ IsUnit ((D.host.g k : ℕ) : 𝓞 D.host.K) := by
      intro hu
      have h1 : IsUnit (algebraMap ℤ (𝓞 D.host.K) (D.host.g k : ℤ)) := by simpa using hu
      have h2 := (isUnit_map_iff (algebraMap ℤ (𝓞 D.host.K)) _).1 h1
      rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at h2
      exact hg.ne_one h2
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.K)})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    have hmem := hle (Ideal.mem_span_singleton_self _)
    refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
    rintro rfl
    exact hg.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hmem))
  have hW : ∀ k, ∃ f : (ZMod (D.host.g k))ˣ →* ℂˣ, Function.Injective f := by
    intro k
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    obtain ⟨e⟩ : Nonempty ((ZMod (D.host.g k))ˣ ≃* rootsOfUnity (Nat.card (ZMod (D.host.g k))ˣ) ℂ) := by
      haveI : NeZero (Nat.card (ZMod (D.host.g k))ˣ) := ⟨Nat.card_pos.ne'⟩
      exact ⟨mulEquivOfCyclicCardEq (by
        first
        | exact (Complex.card_rootsOfUnity _).symm
        | exact (HasEnoughRootsOfUnity.natCard_rootsOfUnity ℂ _).symm)⟩
    exact ⟨(rootsOfUnity _ ℂ).subtype.comp e.toMonoidHom, Subtype.val_injective.comp e.injective⟩
  choose pb hpb using hP
  choose om hom using hW
  choose mu hmu using hμ ⟨pb, hpb⟩ ⟨om, hom⟩
  obtain ⟨η, hη⟩ := hη
  obtain ⟨δ, hδ⟩ := hδ
  obtain ⟨δ', hδ'⟩ := hδ'
  exact ⟨⟨⟨pb, hpb⟩, ⟨om, hom⟩, mu, η, η * η, δ, δ', hmu, hη, hη.sq_chiPsi, hδ, hδ'⟩⟩

def finPart {L : Type} [Field L] [NumberField L] (k : Lˣ) : Ideles L := diagUnits L k * (infDiag k)⁻¹

/- English proof (translation)
Set `p : Ideles L →* w.Completion` to `((Pi.evalMonoidHom (fun w : InfinitePlace L => w.Completion) w).comp (MonoidHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))).comp (Units.coeHom _)`. Use `show p (infDiag k) = _`. Unfold `infDiag`. Rewrite using `[MonoidHom.finset_prod_apply, map_prod, Finset.prod_eq_single w]`. Use `show Pi.mulSingle (M := fun w : InfinitePlace L => w.Completion) w _ w = _`.

Rewrite using `[Pi.mulSingle_eq_same]`. Both sides reduce to the same expression. Introduce `w' _ hw show Pi.mulSingle (M := fun w : InfinitePlace L => w.Completion) w' _ w = _`. Rewrite using `[Pi.mulSingle_eq_of_ne hw.symm]`. Simplify using the standard rewrite rules.
-/
theorem infDiag_fst {L : Type} [Field L] [NumberField L] (k : Lˣ) (w : InfinitePlace L) :
    ((infDiag k : Ideles L) : AdeleRing (𝓞 L) L).1 w = algebraMap L w.Completion (k : L) := by
  classical
  let p : Ideles L →* w.Completion :=
    ((Pi.evalMonoidHom (fun w : InfinitePlace L => w.Completion) w).comp
      (MonoidHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))).comp (Units.coeHom _)
  show p (infDiag k) = _
  unfold infDiag
  rw [MonoidHom.finset_prod_apply, map_prod, Finset.prod_eq_single w]
  · show Pi.mulSingle (M := fun w : InfinitePlace L => w.Completion) w _ w = _
    rw [Pi.mulSingle_eq_same]; rfl
  · intro w' _ hw
    show Pi.mulSingle (M := fun w : InfinitePlace L => w.Completion) w' _ w = _
    rw [Pi.mulSingle_eq_of_ne hw.symm]
  · simp

/- English proof (translation)
Introduce `w`. Rewrite using `[finPart, ← map_inv, Units.val_mul]`. Use `show algebraMap L w.Completion (k : L) * ((infDiag k⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).1 w = 1`. Rewrite using `[infDiag_fst, ← map_mul, Units.mul_inv, map_one]`.
-/
theorem isFinIdele_finPart {L : Type} [Field L] [NumberField L] (k : Lˣ) : IsFinIdele (finPart k) := by
  intro w
  rw [finPart, ← map_inv, Units.val_mul]
  show algebraMap L w.Completion (k : L) * ((infDiag k⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).1 w = 1
  rw [infDiag_fst, ← map_mul, Units.mul_inv, map_one]

/- English proof (translation)
Rewrite using `[finPart, map_mul, map_inv, χ.2.2, one_mul, Units.val_inv_eq_inv_val]`. Use `h k` as an intermediate fact. Rewrite using `[show χ.1 (infDiag k) = χ.inf k from rfl, this, ← Finset.prod_inv_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[zpow_mul, zpow_neg, ← unit_sq _ (by simp)]; rfl`.
-/
theorem val_finPart {L I : Type} [Field L] [NumberField L] [Fintype I] {φ : I → L →+* ℂ} {χ : HChar L} {n : I → ℤ}
    (h : χ.HasInf φ (fun i => 2 * n i)) (k : Lˣ) :
    ((χ.1 (finPart k) : ℂˣ) : ℂ) = ∏ i, (φ i k / starRingEnd ℂ (φ i k)) ^ (-n i) := by
  rw [finPart, map_mul, map_inv, χ.2.2, one_mul, Units.val_inv_eq_inv_val]
  have := h k
  rw [show χ.1 (infDiag k) = χ.inf k from rfl, this, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [zpow_mul, zpow_neg, ← unit_sq _ (by simp)]; rfl

/- English proof (translation)
Establish `: T.eDt (infDiag k) = 1`. Unfold `infDiag`. Rewrite using `[MonoidHom.finset_prod_apply, map_prod]`. Conclude with `Finset.prod_eq_one fun w _ => T.inf w _`. Rewrite using `[finPart, map_mul, map_inv, this, inv_one, mul_one]`.
-/
theorem eDt_finPart (T : DtTied D C) (k : D.host.Eˣ) : T.eDt (finPart k) = T.eDt (diagUnits D.host.E k) := by
  have : T.eDt (infDiag k) = 1 := by
    unfold infDiag
    rw [MonoidHom.finset_prod_apply, map_prod]
    exact Finset.prod_eq_one fun w _ => T.inf w _
  rw [finPart, map_mul, map_inv, this, inv_one, mul_one]

/- English proof (translation)
Rewrite using `[← eDt_finPart, T.chiD_eq _ (isFinIdele_finPart k), val_finPart (n := fun _ => 1) C.isChi.inf]`. Simplify using the standard rewrite rules.
-/
theorem chiD_rat (T : DtTied D C) (k : D.host.Eˣ) :
    ((D.chiD (T.eDt (diagUnits D.host.E k)) : ℂˣ) : ℂ) =
      ∏ g : D.R.Psi, (embPsi D.host g k / starRingEnd ℂ (embPsi D.host g k))⁻¹ := by
  rw [← eDt_finPart, T.chiD_eq _ (isFinIdele_finPart k), val_finPart (n := fun _ => 1) C.isChi.inf]
  simp

/- English proof (translation)
Take `⟨n, hn, h⟩` from `(C.isMu0 j).inf`. Establish `: n = fun g => 2 * -e g` using `funext fun g => by`. Use `hn g` as an intermediate fact. Simplify using `only [he] at this`. Conclude with `this` after adjusting the coercions.

Substitute `this` using the available equality. Rewrite using `[← eDt_finPart, T.muTil_eq j _ (isFinIdele_finPart k), val_finPart h]`. Simplify using the standard rewrite rules.
-/
theorem muTil_rat (T : DtTied D C) (j : Fin D.R.m) (e : D.R.Psi → ℤ) (he : ∀ g, eExp D j g = e g) (k : D.host.Eˣ) :
    ((D.muTil (j.1 + 1) (T.eDt (diagUnits D.host.E k)) : ℂˣ) : ℂ) =
      ∏ g : D.R.Psi, (embPsi D.host g k / starRingEnd ℂ (embPsi D.host g k)) ^ e g := by
  obtain ⟨n, hn, h⟩ := (C.isMu0 j).inf
  have : n = fun g => 2 * -e g := funext fun g => by
    have := hn g
    simp only [he] at this
    exact_mod_cast this
  subst this
  rw [← eDt_finPart, T.muTil_eq j _ (isFinIdele_finPart k), val_finPart h]
  simp

/- English proof (translation)
Establish `hnu : ¬ IsUnit ((p : ℕ) : 𝓞 L)`. Introduce `hu`. Establish `h1 : IsUnit (algebraMap ℤ (𝓞 L) (p : ℤ))` using `by simpa using hu`. Establish `h2` using `(isUnit_map_iff (algebraMap ℤ (𝓞 L)) _).1 h1`. Rewrite `h2` using `[Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast]`.

Conclude with `hg.ne_one h2`. Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal (Ideal.span {((p : ℕ) : 𝓞 L)}) (by rwa [Ne, Ideal.span_singleton_eq_top])`. Establish `hmem` using `hle (Ideal.mem_span_singleton_self _)`. Use `⟨⟨M, hM.isPrime, ?_⟩, hmem⟩` and prove the remaining obligations. Introduce and unpack `rfl`.

Conclude with `hg.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hmem))`.
-/
theorem exists_place_over {L : Type} [Field L] [NumberField L] {p : ℕ} (hg : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 L), ((p : ℕ) : 𝓞 L) ∈ v.asIdeal := by
  have hnu : ¬ IsUnit ((p : ℕ) : 𝓞 L) := by
    intro hu
    have h1 : IsUnit (algebraMap ℤ (𝓞 L) (p : ℤ)) := by simpa using hu
    have h2 := (isUnit_map_iff (algebraMap ℤ (𝓞 L)) _).1 h1
    rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at h2
    exact hg.ne_one h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {((p : ℕ) : 𝓞 L)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  rintro rfl
  exact hg.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hmem))

/- English proof (translation)
Introduce `h`. Establish `h1 : C.del = 1` using `by rw [← Tp.xi_star, ← h, Tp.trueColumnChoices_heckeChar_reference_eq_one]`. Take `⟨v, hv⟩` from `exists_place_over (L := D.host.E) D.host.pde_prime`. Use `(C.isDel.ine v hv 1).1 fun x _ => by rw [h1, pow_one]; rfl` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem reference_tuple_ne_base_tuple (Tp : TupTied D C nch) : D.what₂.mu0 ≠ D.what₂.muStar := by
  intro h
  have h1 : C.del = 1 := by rw [← Tp.xi_star, ← h, Tp.trueColumnChoices_heckeChar_reference_eq_one]
  obtain ⟨v, hv⟩ := exists_place_over (L := D.host.E) D.host.pde_prime
  have := (C.isDel.ine v hv 1).1 fun x _ => by rw [h1, pow_one]; rfl
  omega

/- English proof (translation)
Apply `Tp.xi_inj` to reduce the goal to its premises. Rewrite using `[Tp.xi_tw, Tp.psi_un w h, mul_one, CharFrame.delAt]`. Use `split_ifs`. Conclude with `Tp.xi_star'.symm`. Conclude with `Tp.xi_star.symm`.
-/
theorem muTw_of_untwisted (Tp : TupTied D C nch) (w : D.what₂.places.Pl) (h : D.what₂.muAt w = D.what₂.mu0) :
    D.what₂.muTw w = if D.what₂.places.resChar w = D.host.pde then D.what₂.muStar' else D.what₂.muStar := by
  apply Tp.xi_inj
  rw [Tp.xi_tw, Tp.psi_un w h, mul_one, CharFrame.delAt]
  split_ifs
  · exact Tp.xi_star'.symm
  · exact Tp.xi_star.symm

end GlobalTheory.Mem.Chr.TieModel
