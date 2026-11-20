import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartForm

variable {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d)

/- English proof (translation)
Establish `h : (c.ev n).comp (MvPolynomial.coeToMvPowerSeries.algHom O) = MvPolynomial.aeval (c.x n)` using `MvPolynomial.algHom_ext fun i => by`. Simplify using `[MvPolynomial.coeToMvPowerSeries.algHom_apply, (c.isEval n).1 i]`. Establish `h2` using `DFunLike.congr_fun h P`. Simplify `h2` using `[MvPolynomial.coeToMvPowerSeries.algHom_apply]`.
-/
theorem ev_coe (n : ℕ) (P : MvPolynomial (Fin d) O) :
    c.ev n (P : MvPowerSeries (Fin d) O) = MvPolynomial.aeval (c.x n) P := by
  have h : (c.ev n).comp (MvPolynomial.coeToMvPowerSeries.algHom O) =
      MvPolynomial.aeval (c.x n) :=
    MvPolynomial.algHom_ext fun i => by
      simp [MvPolynomial.coeToMvPowerSeries.algHom_apply, (c.isEval n).1 i]
  have h2 := DFunLike.congr_fun h P
  simpa [MvPolynomial.coeToMvPowerSeries.algHom_apply] using h2

/- English proof (translation)
Take `⟨N, hN⟩` from `(c.isEval n).2 m`. Use `set P := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => max N 2) f with hP`. Establish `hle : ∀ α : Fin d →₀ ℕ, α.degree < max N 2 → α ≤ Finsupp.equivFunOnFinite.symm fun _ => max N 2`. Introduce `α hα i`. Use `show α i ≤ max N 2`.

Conclude with `(Finsupp.le_degree i α).trans hα.le`. Take `⟨a, ha⟩` from `hN (f - P) fun α hα => by`. Rewrite using `[map_sub, MvPolynomial.coeff_coe, hP, coeff_trunc', if_pos (hle α (lt_of_lt_of_le hα (le_max_left _ _))), sub_self]`. Use `⟨P, a, ?_, ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[← ev_coe, ← ha, ← map_add, add_sub_cancel]`.

Rewrite using `[MvPolynomial.constantCoeff_eq, hP, coeff_trunc', if_pos (hle 0 (by simp)), coeff_zero_eq_constantCoeff_apply]`. Rewrite using `[hP, coeff_trunc', if_pos (hle _ (lt_of_lt_of_le (by simp) (le_max_right N 2))), lin]`.
-/
theorem exists_split (n m : ℕ) (f : MvPowerSeries (Fin d) O) :
    ∃ (P : MvPolynomial (Fin d) O) (a : G.A n),
      c.ev n f = MvPolynomial.aeval (c.x n) P + (p : G.A n) ^ m * a ∧
      MvPolynomial.constantCoeff P = constantCoeff f ∧
      ∀ i, MvPolynomial.coeff (Finsupp.single i 1) P = lin f i := by
  obtain ⟨N, hN⟩ := (c.isEval n).2 m
  set P := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => max N 2) f with hP
  have hle : ∀ α : Fin d →₀ ℕ, α.degree < max N 2 →
      α ≤ Finsupp.equivFunOnFinite.symm fun _ => max N 2 := by
    intro α hα i
    show α i ≤ max N 2
    exact (Finsupp.le_degree i α).trans hα.le
  obtain ⟨a, ha⟩ := hN (f - P) fun α hα => by
    rw [map_sub, MvPolynomial.coeff_coe, hP, coeff_trunc',
      if_pos (hle α (lt_of_lt_of_le hα (le_max_left _ _))), sub_self]
  refine ⟨P, a, ?_, ?_, fun i => ?_⟩
  · rw [← ev_coe, ← ha, ← map_add, add_sub_cancel]
  · rw [MvPolynomial.constantCoeff_eq, hP, coeff_trunc',
      if_pos (hle 0 (by simp)), coeff_zero_eq_constantCoeff_apply]
  · rw [hP, coeff_trunc', if_pos (hle _ (lt_of_lt_of_le (by simp) (le_max_right N 2))), lin]

/- English proof (translation)
The claim follows from `IsHausdorff.haus' (I := Ideal.span {(p : O)}) x fun m => by rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton, sub_zero] exact h m`.
-/
theorem eq_zero_of_dvd [IsAdicComplete (Ideal.span {(p : O)}) O] (x : O)
    (h : ∀ m, (p : O) ^ m ∣ x) : x = 0 :=
  IsHausdorff.haus' (I := Ideal.span {(p : O)}) x fun m => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, sub_zero]
    exact h m

/- English proof (translation)
Rewrite using `[← AlgHom.comp_apply, MvPolynomial.comp_aeval]`. Establish `h : (fun i => Bialgebra.counitAlgHom O (G.A n) (c.x n i)) = 0`. Use function extensionality and compare the values at `fun i => by simpa using c.aug n i`. Rewrite using `[h, MvPolynomial.aeval_zero]`. Both sides reduce to the same expression.
-/
theorem counit_aeval (n : ℕ) (P : MvPolynomial (Fin d) O) :
    Bialgebra.counitAlgHom O (G.A n) (MvPolynomial.aeval (c.x n) P) =
      MvPolynomial.constantCoeff P := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have h : (fun i => Bialgebra.counitAlgHom O (G.A n) (c.x n i)) = 0 :=
    funext fun i => by simpa using c.aug n i
  rw [h, MvPolynomial.aeval_zero]
  rfl

/- English proof (translation)
Use `sub_eq_zero.1 (eq_zero_of_dvd (p := p) _ fun m => ?_)` and prove the remaining obligations. Take `⟨P, a, h1, h2, -⟩` from `(exists_split c) n m f`. Rewrite using `[h1, map_add, counit_aeval, h2, map_mul, map_pow, map_natCast, add_sub_cancel_left]`. Conclude with `dvd_mul_right _ _`.
-/
theorem counit_ev [IsAdicComplete (Ideal.span {(p : O)}) O] (n : ℕ)
    (f : MvPowerSeries (Fin d) O) :
    Bialgebra.counitAlgHom O (G.A n) (c.ev n f) = constantCoeff f := by
  refine sub_eq_zero.1 (eq_zero_of_dvd (p := p) _ fun m => ?_)
  obtain ⟨P, a, h1, h2, -⟩ := (exists_split c) n m f
  rw [h1, map_add, counit_aeval, h2, map_mul, map_pow, map_natCast, add_sub_cancel_left]
  exact dvd_mul_right _ _

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a`. Establish `h0 : ∀ x : Fin d, ¬ (0 : Fin d →₀ ℕ) = Finsupp.single x 1` using `fun x h => (Finsupp.single_ne_zero.2 one_ne_zero) h.symm`. Rewrite using `[MvPolynomial.aeval_C]`. Simplify using `[MvPolynomial.coeff_C, PDiv.dUnit, h0]`.

Consider the case `add P Q hP hQ`. Unfold `PDiv.dUnit at *`. Rewrite using `[map_add, map_add, hP, hQ, ← Finset.sum_add_distrib]`. Simplify using `[add_smul]`. Consider the case `mul_X P j h`.

Establish `hc : ∀ i, MvPolynomial.coeff (Finsupp.single i 1) (P * MvPolynomial.X j) = if j = i then MvPolynomial.constantCoeff P else 0`. Introduce `i`. Rewrite using `[MvPolynomial.coeff_mul_X']`. Distinguish the cases in `hij : j = i`. Substitute `hij` using the available equality.

Simplify using `[MvPolynomial.constantCoeff_eq]`. Simplify using `[hij, Finsupp.support_single_ne_zero]`. Simplify using `only [hc, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Establish `hx : Bialgebra.counitAlgHom O (G.A n) (c.x n j) = 0` using `by simpa using c.aug n j`. Rewrite using `[map_mul, MvPolynomial.aeval_X, PDiv.dUnit, AugCot.d_mul, counit_aeval, hx, zero_smul, add_zero]`.
-/
theorem d_aeval (n : ℕ) (P : MvPolynomial (Fin d) O) :
    PDiv.dUnit O (MvPolynomial.aeval (c.x n) P) =
      ∑ i, MvPolynomial.coeff (Finsupp.single i 1) P • PDiv.dUnit O (c.x n i) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h0 : ∀ x : Fin d, ¬ (0 : Fin d →₀ ℕ) = Finsupp.single x 1 := fun x h =>
      (Finsupp.single_ne_zero.2 one_ne_zero) h.symm
    rw [MvPolynomial.aeval_C]
    simp [MvPolynomial.coeff_C, PDiv.dUnit, h0]
  | add P Q hP hQ =>
    unfold PDiv.dUnit at *
    rw [map_add, map_add, hP, hQ, ← Finset.sum_add_distrib]
    simp [add_smul]
  | mul_X P j h =>
    have hc : ∀ i, MvPolynomial.coeff (Finsupp.single i 1) (P * MvPolynomial.X j) =
        if j = i then MvPolynomial.constantCoeff P else 0 := by
      intro i
      rw [MvPolynomial.coeff_mul_X']
      by_cases hij : j = i
      · subst hij; simp [MvPolynomial.constantCoeff_eq]
      · simp [hij, Finsupp.support_single_ne_zero]
    simp only [hc, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hx : Bialgebra.counitAlgHom O (G.A n) (c.x n j) = 0 := by simpa using c.aug n j
    rw [map_mul, MvPolynomial.aeval_X, PDiv.dUnit, AugCot.d_mul, counit_aeval, hx, zero_smul,
      add_zero]

/- English proof (translation)
Take `⟨P, a, h1, -, h3⟩` from `(exists_split c) n n f`. Establish `h4 : AugCot.d (Bialgebra.counitAlgHom O (G.A n)) ((p : G.A n) ^ n * a) = 0`. Rewrite using `[show (p : G.A n) ^ n * a = ((p : O) ^ n) • a by`. Rewrite using `[Algebra.smul_def, map_pow, map_natCast], map_smul]`. Conclude with `G.pow_smul_cot n _`.

Rewrite using `[h1, PDiv.dUnit, map_add, h4, add_zero, ← PDiv.dUnit, (d_aeval c)]`. Simplify using `only [h3]`.
-/
theorem d_ev (n : ℕ) (f : MvPowerSeries (Fin d) O) :
    PDiv.dUnit O (c.ev n f) = ∑ i, lin f i • PDiv.dUnit O (c.x n i) := by
  obtain ⟨P, a, h1, -, h3⟩ := (exists_split c) n n f
  have h4 : AugCot.d (Bialgebra.counitAlgHom O (G.A n)) ((p : G.A n) ^ n * a) = 0 := by
    rw [show (p : G.A n) ^ n * a = ((p : O) ^ n) • a by
      rw [Algebra.smul_def, map_pow, map_natCast], map_smul]
    exact G.pow_smul_cot n _
  rw [h1, PDiv.dUnit, map_add, h4, add_zero, ← PDiv.dUnit, (d_aeval c)]
  simp only [h3]

/- English proof (translation)
Rewrite `hh` using `[pow_two]`. Use `Submodule.mul_induction_on hh (fun f hf g hg => ?_) (fun f g hf hg => ?_)` and prove the remaining obligations. Rewrite using `[coeff_mul]`. Use `Finset.sum_eq_zero fun q hq => ?_` and prove the remaining obligations. Rewrite `hq` using `[Finset.HasAntidiagonal.mem_antidiagonal]`.

Establish `hdeg` using `congrArg Finsupp.degree hq`. Rewrite `hdeg` using `[map_add, Finsupp.degree_single]`. Break down `(show q.1.degree = 0 ∨ q.2.degree = 0 by omega) with h0 | h0` into its components or cases. Rewrite using `[(Finsupp.degree_eq_zero_iff _).1 h0, coeff_zero_eq_constantCoeff_apply, RingHom.mem_ker.1 hf, zero_mul]`. Rewrite using `[(Finsupp.degree_eq_zero_iff _).1 h0, coeff_zero_eq_constantCoeff_apply, RingHom.mem_ker.1 hg, mul_zero]`.

Rewrite using `[map_add, hf, hg, add_zero]`.
-/
theorem coeff_single_of_mem_sq {h : MvPowerSeries (Fin d) O}
    (hh : h ∈ RingHom.ker (constantCoeff : MvPowerSeries (Fin d) O →+* O) ^ 2) (i : Fin d) :
    coeff (Finsupp.single i 1) h = 0 := by
  rw [pow_two] at hh
  refine Submodule.mul_induction_on hh (fun f hf g hg => ?_) (fun f g hf hg => ?_)
  · rw [coeff_mul]
    refine Finset.sum_eq_zero fun q hq => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have hdeg := congrArg Finsupp.degree hq
    rw [map_add, Finsupp.degree_single] at hdeg
    rcases (show q.1.degree = 0 ∨ q.2.degree = 0 by omega) with h0 | h0
    · rw [(Finsupp.degree_eq_zero_iff _).1 h0, coeff_zero_eq_constantCoeff_apply,
        RingHom.mem_ker.1 hf, zero_mul]
    · rw [(Finsupp.degree_eq_zero_iff _).1 h0, coeff_zero_eq_constantCoeff_apply,
        RingHom.mem_ker.1 hg, mul_zero]
  · rw [map_add, hf, hg, add_zero]

def lvl (n : ℕ) : (Fin d → O) →ₗ[O] PDiv.Cot O (G.A n) :=
  Fintype.linearCombination O fun i => PDiv.dUnit O (c.x n i)

/- English proof (translation)
The claim follows from `Fintype.linearCombination_apply ..`.
-/
theorem lvl_apply (n : ℕ) (a : Fin d → O) :
    lvl c n a = ∑ i, a i • PDiv.dUnit O (c.x n i) := Fintype.linearCombination_apply ..

/- English proof (translation)
Rewrite using `[Fintype.linearCombination_apply, lvl_apply]`. Simplify using `[QLog.Chart.form]`.
-/
theorem val_comb (a : Fin d → O) (n : ℕ) :
    (Fintype.linearCombination O c.form a).1 n = lvl c n a := by
  rw [Fintype.linearCombination_apply, lvl_apply]
  simp [QLog.Chart.form]

/- English proof (translation)
Simplify using `[lvl_apply, map_sum, map_smul, PDiv.cotMap_d, c.res]`.
-/
theorem res_lvl (n : ℕ) (a : Fin d → O) :
    PDiv.cotMap (G.res n) (lvl c (n + 1) a) = lvl c n a := by
  simp [lvl_apply, map_sum, map_smul, PDiv.cotMap_d, c.res]

/- English proof (translation)
Use `revert hk`. Proceed by induction on `k, h using Nat.le_induction with`. Consider the case `base => exact id`. Consider the case `succ k hnk ih => exact fun hk => ih (by rw [← res_lvl c, hk, w.2 k])`.
-/
theorem lvl_le (w : G.omega) (a : Fin d → O) {n k : ℕ} (h : n ≤ k)
    (hk : lvl c k a = w.1 k) : lvl c n a = w.1 n := by
  revert hk
  induction k, h using Nat.le_induction with
  | base => exact id
  | succ k hnk ih => exact fun hk => ih (by rw [← res_lvl c, hk, w.2 k])

/- English proof (translation)
Take `⟨n, hn⟩` from `c.ker m 2`. Use `⟨n, fun a ha i => ?_⟩` and prove the remaining obligations. Use `set y : G.A n := ∑ j, a j • c.x n j with hy0`. Establish `hx : ∀ j, Bialgebra.counitAlgHom O (G.A n) (c.x n j) = 0` using `fun j => by`. Simplify using `using c.aug n j`.

Establish `hεy : Bialgebra.counitAlgHom O (G.A n) y = 0`. Simplify using `[hy0, map_sum, map_smul, hx]`. Establish `hy : PDiv.dUnit O y = 0`. Rewrite using `[hy0, PDiv.dUnit, map_sum]`. Simplify `ha` using `[map_smul, lvl_apply]`.

Rewrite `hy` using `[PDiv.dUnit, AugCot.d_eq_zero_iff, hεy, map_zero, sub_zero]`. Establish `hI : RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) ≤ Ideal.map (c.ev n) (RingHom.ker (constantCoeff : MvPowerSeries (Fin d) O →+* O))`. Introduce `z hz`. Take `⟨g, rfl⟩` from `c.surj n z`. Use `Ideal.mem_map_of_mem _ ?_` and prove the remaining obligations.

Rewrite using `[RingHom.mem_ker, ← counit_ev c]`. Conclude with `hz`. Establish `hy2 : y ∈ Ideal.map (c.ev n) (RingHom.ker (constantCoeff : MvPowerSeries (Fin d) O →+* O) ^ 2)`. Rewrite using `[Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono hI 2 hy`.

Take `⟨h, hh, hev⟩` from `(Ideal.mem_map_iff_of_surjective _ (c.surj n)).1 hy2`. Establish `hz : c.ev n ((∑ j, a j • X j) - h) = 0`. Rewrite using `[map_sub, hev, map_sum, hy0]`. Simplify using `[map_smul, (c.isEval n).1]`. Use `hn _ hz (Finsupp.single i 1) (by simp)` as an intermediate fact.

Rewrite `this` using `[map_sub, coeff_single_of_mem_sq hh, sub_zero]`. Simplify `this` using `[coeff_X, Finsupp.single_left_inj one_ne_zero]`.
-/
theorem exists_level_dvd [IsAdicComplete (Ideal.span {(p : O)}) O] (m : ℕ) :
    ∃ n, ∀ a : Fin d → O, lvl c n a = 0 → ∀ i, (p : O) ^ m ∣ a i := by
  obtain ⟨n, hn⟩ := c.ker m 2
  refine ⟨n, fun a ha i => ?_⟩
  set y : G.A n := ∑ j, a j • c.x n j with hy0
  have hx : ∀ j, Bialgebra.counitAlgHom O (G.A n) (c.x n j) = 0 := fun j => by
    simpa using c.aug n j
  have hεy : Bialgebra.counitAlgHom O (G.A n) y = 0 := by
    simp [hy0, map_sum, map_smul, hx]
  have hy : PDiv.dUnit O y = 0 := by
    rw [hy0, PDiv.dUnit, map_sum]
    simpa [map_smul, lvl_apply] using ha
  rw [PDiv.dUnit, AugCot.d_eq_zero_iff, hεy, map_zero, sub_zero] at hy
  have hI : RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) ≤
      Ideal.map (c.ev n) (RingHom.ker (constantCoeff : MvPowerSeries (Fin d) O →+* O)) := by
    intro z hz
    obtain ⟨g, rfl⟩ := c.surj n z
    refine Ideal.mem_map_of_mem _ ?_
    rw [RingHom.mem_ker, ← counit_ev c]
    exact hz
  have hy2 : y ∈ Ideal.map (c.ev n)
      (RingHom.ker (constantCoeff : MvPowerSeries (Fin d) O →+* O) ^ 2) := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hI 2 hy
  obtain ⟨h, hh, hev⟩ := (Ideal.mem_map_iff_of_surjective _ (c.surj n)).1 hy2
  have hz : c.ev n ((∑ j, a j • X j) - h) = 0 := by
    rw [map_sub, hev, map_sum, hy0]
    simp [map_smul, (c.isEval n).1]
  have := hn _ hz (Finsupp.single i 1) (by simp)
  rw [map_sub, coeff_single_of_mem_sq hh, sub_zero] at this
  classical
  simpa [coeff_X, Finsupp.single_left_inj one_ne_zero] using this

/- English proof (translation)
Use `choose nm hnm using (exists_level_dvd c)`. Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Use function extensionality and compare the values at `i`.

Use `eq_zero_of_dvd _ fun m => hnm m a ?_ i` and prove the remaining obligations. Rewrite using `[← val_comb c, ha]`. Both sides reduce to the same expression. Introduce `w`. Establish `hb : ∀ k, ∃ b : Fin d → O, lvl c k b = w.1 k`.

Introduce `k`. Take `⟨y, hy⟩` from `AugCot.d_surjective _ (w.1 k)`. Take `⟨g, rfl⟩` from `c.surj k y`. Conclude with `⟨lin g, by rw [lvl_apply, ← d_ev c]; exact hy⟩`. Use `choose b hb using hb`.

Set `K : ℕ → ℕ` to `fun m => m + ∑ j ∈ Finset.range (m + 1), nm j`. Establish `hK : ∀ {m n}, m ≤ n → K m ≤ K n` using `fun h => add_le_add h (Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ h)))`. Establish `hnK : ∀ m, nm m ≤ K m` using `fun m => le_add_left (Finset.single_le_sum (fun j _ => Nat.zero_le (nm j)) (Finset.self_mem_range_succ m))`. Establish `hnK' : ∀ m, m ≤ K m` using `fun m => Nat.le_add_right _ _`. Establish `hcauchy : ∀ {m n}, m ≤ n → ∀ i, (p : O) ^ m ∣ b (K m) i - b (K n) i`.

Introduce `m n hmn i`. Use `hnm m (b (K m) - b (K n)) ?_ i` and prove the remaining obligations. Rewrite using `[map_sub, (lvl_le c) w _ (hnK m) (hb _), (lvl_le c) w _ ((hnK m).trans (hK hmn)) (hb _), sub_self]`. Establish `hL : ∀ i, ∃ L : O, ∀ n, (p : O) ^ n ∣ b (K n) i - L`. Introduce `i`.

Take `⟨L, hL⟩` from `IsPrecomplete.prec' (I := Ideal.span {(p : O)}) (fun m => b (K m) i) fun {m n} hmn => by`. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Conclude with `hcauchy hmn i`. Use `⟨L, fun n => ?_⟩` and prove the remaining obligations. Establish `h1` using `hL n`.

Rewrite `h1` using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Conclude with `h1`. Use `choose L hL using hL`. Use `⟨L, Subtype.ext (funext fun n => ?_)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(Fintype.linearCombination O c.form L).1 n = w.1 n`.

Rewrite using `[(val_comb c)]`. Use `choose v hv using fun i => hL i n`. Establish `hLv : L = b (K n) - (p : O) ^ n • v`. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← hv i]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hLv, map_sub, map_smul, G.pow_smul_cot, sub_zero]`. Conclude with `(lvl_le c) w _ (hnK' n) (hb _)`.
-/
theorem comb_bijective [IsAdicComplete (Ideal.span {(p : O)}) O] :
    Function.Bijective (Fintype.linearCombination O c.form) := by
  choose nm hnm using (exists_level_dvd c)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    funext i
    refine eq_zero_of_dvd _ fun m => hnm m a ?_ i
    rw [← val_comb c, ha]
    rfl
  · intro w
    have hb : ∀ k, ∃ b : Fin d → O, lvl c k b = w.1 k := by
      intro k
      obtain ⟨y, hy⟩ := AugCot.d_surjective _ (w.1 k)
      obtain ⟨g, rfl⟩ := c.surj k y
      exact ⟨lin g, by rw [lvl_apply, ← d_ev c]; exact hy⟩
    choose b hb using hb
    let K : ℕ → ℕ := fun m => m + ∑ j ∈ Finset.range (m + 1), nm j
    have hK : ∀ {m n}, m ≤ n → K m ≤ K n := fun h =>
      add_le_add h (Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ h)))
    have hnK : ∀ m, nm m ≤ K m := fun m =>
      le_add_left (Finset.single_le_sum (fun j _ => Nat.zero_le (nm j))
        (Finset.self_mem_range_succ m))
    have hnK' : ∀ m, m ≤ K m := fun m => Nat.le_add_right _ _
    have hcauchy : ∀ {m n}, m ≤ n → ∀ i, (p : O) ^ m ∣ b (K m) i - b (K n) i := by
      intro m n hmn i
      refine hnm m (b (K m) - b (K n)) ?_ i
      rw [map_sub, (lvl_le c) w _ (hnK m) (hb _), (lvl_le c) w _ ((hnK m).trans (hK hmn)) (hb _),
        sub_self]
    have hL : ∀ i, ∃ L : O, ∀ n, (p : O) ^ n ∣ b (K n) i - L := by
      intro i
      obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : O)})
        (fun m => b (K m) i) fun {m n} hmn => by
          rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
            Ideal.mem_span_singleton]
          exact hcauchy hmn i
      refine ⟨L, fun n => ?_⟩
      have h1 := hL n
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton] at h1
      exact h1
    choose L hL using hL
    refine ⟨L, Subtype.ext (funext fun n => ?_)⟩
    change (Fintype.linearCombination O c.form L).1 n = w.1 n
    rw [(val_comb c)]
    choose v hv using fun i => hL i n
    have hLv : L = b (K n) - (p : O) ^ n • v := by
      funext i
      rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← hv i]
      ring
    rw [hLv, map_sub, map_smul, G.pow_smul_cot, sub_zero]
    exact (lvl_le c) w _ (hnK' n) (hb _)

end GlobalTheory.ChartForm

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ _ _ G d c`. Conclude with `⟨ChartForm.comb_bijective c, fun n f _ => ChartForm.d_ev c n f⟩`.
-/
theorem GlobalTheory.chart_form_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), Function.Bijective (Fintype.linearCombination O c.form) ∧ ∀ (n : ℕ) (f : MvPowerSeries (Fin d) O), constantCoeff f = 0 → PDiv.dUnit O (c.ev n f) = ∑ i, lin f i • PDiv.dUnit O (c.x n i) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ G d c
  exact ⟨ChartForm.comb_bijective c, fun n f _ => ChartForm.d_ev c n f⟩
