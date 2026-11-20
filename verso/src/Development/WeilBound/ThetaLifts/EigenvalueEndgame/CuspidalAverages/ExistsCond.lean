import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.KeyThree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Cusp.Key

open scoped Matrix
open Filter Topology ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SplitWeil

/- English proof (translation)
Set `N` to `LinearMap.ker p.mulVecLin`. Set `b` to `Module.finBasis K N`. Establish `hs : Function.Surjective p.mulVecLin` using `fun y => ⟨u *ᵥ y, by simp [h]⟩`. Establish `hd : j + Module.finrank K N = d`. Use `p.mulVecLin.finrank_range_add_finrank_ker` as an intermediate fact.

Rewrite `this` using `[LinearMap.range_eq_top.2 hs]`. Simplify using `using this`. Set `q : Fin j ⊕ Fin (Module.finrank K N) ≃ Fin d` to `finSumFinEquiv.trans (finCongr hd)`. Set `w : Matrix (Fin d) (Fin (Module.finrank K N)) K` to `Matrix.of fun a i => (b i).1 a`. Establish `hw : p * w = 0` using `Matrix.ext fun a i => congrFun (b i).2 a`.

Set `c : Matrix (Fin d) (Fin d) K` to `(Matrix.fromCols u w).submatrix id q.symm`. Establish `hc : IsUnit c`. Rewrite using `[← Matrix.mulVec_injective_iff_isUnit]`. Use `(injective_iff_map_eq_zero c.mulVecLin).2 fun x hx => ?_` and prove the remaining obligations. Establish `h1 : u *ᵥ (fun i => x (q (.inl i))) + w *ᵥ (fun i => x (q (.inr i))) = 0`.

Rewrite using `[← hx]`. Use function extensionality and compare the values at `a`. Simplify using `[c, Matrix.mulVec, dotProduct, ← q.sum_comp]`. Establish `h2 : (fun i => x (q (.inl i))) = 0`. Use `congrArg (p *ᵥ ·) h1` as an intermediate fact.

Simplify `this` using `[Matrix.mulVec_add, h, hw]`. Rewrite `h1` using `[h2, Matrix.mulVec_zero, zero_add]`. Establish `h3 : ∀ i, x (q (.inr i)) = 0` using `Fintype.linearIndependent_iff.1 b.linearIndependent _ (Subtype.ext (by`. Use function extensionality and compare the values at `a`. Simplify `congrFun h1 a))` using `[w, Matrix.mulVec, dotProduct, mul_comm]`.

Use function extensionality and compare the values at `a`. Take `⟨i | i, rfl⟩` from `q.surjective a`. Use `exacts [congrFun h2 i, h3 i]`. Use `⟨fun i => q (.inl i), hc.unit, fun _ _ h => Sum.inl_injective (q.injective h), fun a i => by simp [c], ?_⟩` and prove the remaining obligations. Use extensionality with `a b'`.

Take `⟨i | i, rfl⟩` from `q.surjective b'`. Use `congrFun (congrFun h a) i` as an intermediate fact. Simplify `this` using `[c, Matrix.mul_apply, Matrix.one_apply]`. Use `congrFun (congrFun hw a) i` as an intermediate fact. Simplify `this` using `[c, Matrix.mul_apply, Matrix.one_apply]`.
-/
theorem exists_compl {K : Type} [Field K] {d j : ℕ} (u : Matrix (Fin d) (Fin j) K) (p : Matrix (Fin j) (Fin d) K) (h : p * u = 1) :
    ∃ (e : Fin j → Fin d) (c : GL (Fin d) K), Function.Injective e ∧ (∀ a i, c.1 a (e i) = u a i) ∧
      p * c.1 = (1 : Matrix (Fin d) (Fin d) K).submatrix e id := by
  let N := LinearMap.ker p.mulVecLin
  let b := Module.finBasis K N
  have hs : Function.Surjective p.mulVecLin := fun y => ⟨u *ᵥ y, by simp [h]⟩
  have hd : j + Module.finrank K N = d := by
    have := p.mulVecLin.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.2 hs] at this
    simpa using this
  let q : Fin j ⊕ Fin (Module.finrank K N) ≃ Fin d := finSumFinEquiv.trans (finCongr hd)
  let w : Matrix (Fin d) (Fin (Module.finrank K N)) K := Matrix.of fun a i => (b i).1 a
  have hw : p * w = 0 := Matrix.ext fun a i => congrFun (b i).2 a
  let c : Matrix (Fin d) (Fin d) K := (Matrix.fromCols u w).submatrix id q.symm
  have hc : IsUnit c := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    refine (injective_iff_map_eq_zero c.mulVecLin).2 fun x hx => ?_
    have h1 : u *ᵥ (fun i => x (q (.inl i))) + w *ᵥ (fun i => x (q (.inr i))) = 0 := by
      rw [← hx]
      funext a
      simp [c, Matrix.mulVec, dotProduct, ← q.sum_comp]
    have h2 : (fun i => x (q (.inl i))) = 0 := by
      have := congrArg (p *ᵥ ·) h1
      simpa [Matrix.mulVec_add, h, hw] using this
    rw [h2, Matrix.mulVec_zero, zero_add] at h1
    have h3 : ∀ i, x (q (.inr i)) = 0 := Fintype.linearIndependent_iff.1 b.linearIndependent _ (Subtype.ext (by
      funext a
      simpa [w, Matrix.mulVec, dotProduct, mul_comm] using congrFun h1 a))
    funext a
    obtain ⟨i | i, rfl⟩ := q.surjective a
    exacts [congrFun h2 i, h3 i]
  refine ⟨fun i => q (.inl i), hc.unit, fun _ _ h => Sum.inl_injective (q.injective h), fun a i => by simp [c], ?_⟩
  ext a b'
  obtain ⟨i | i, rfl⟩ := q.surjective b'
  · have := congrFun (congrFun h a) i
    simpa [c, Matrix.mul_apply, Matrix.one_apply] using this
  · have := congrFun (congrFun hw a) i
    simpa [c, Matrix.mul_apply, Matrix.one_apply] using this

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

/- English proof (translation)
The claim follows from `hϖ ▸ uniformizer_lt_one`.
-/
theorem unif_lt {ϖ : kˣ} (hϖ : IsUnif ϖ) : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one

/- English proof (translation)
Establish `hl` using `unif_lt hϖ`. Establish `h0 : 0 < valuation k (ϖ : k)` using `by rw [pos_iff_ne_zero]; simp`. Set `P : ℤ → Prop` to `fun c => ∀ x, valuation k x ≤ valuation k ((ϖ ^ c : kˣ) : k) → ψ x = 1`. Establish `ex : ∃ c, P c`. Establish `: {x | ‖ψ x - 1‖ < 1 / 2} ∈ 𝓝 (0 : k)` using `(isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)`.

Take `⟨γ, hγ⟩` from `IsValuativeTopology.mem_nhds_zero_iff _ |>.1 this`. Take `⟨m, hm⟩` from `exists_pow_lt₀ hl γ`. Use `⟨m, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hb : ∀ i : ℕ, ‖ψ x ^ i - 1‖ < 1 / 2` using `fun i => by`. Rewrite using `[← AddChar.map_nsmul_eq_pow]`.

Use `hγ (lt_of_le_of_lt ?_ hm)` and prove the remaining obligations. Establish `: valuation k (i • x) ≤ valuation k x`. Rewrite using `[nsmul_eq_mul, map_mul]`. Conclude with `mul_le_of_le_one_left' (natCast_mem (valuation k).integer i)`. Simplify using `using this.trans hx`.

Establish `hg : ∀ i : ℕ, (3 / 2 : ℝ) ^ i * ‖ψ x - 1‖ ≤ ‖ψ x ^ 2 ^ i - 1‖` using `fun i => by`. Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ i ih`. Establish `e : ψ x ^ 2 ^ (i + 1) - 1 = (ψ x ^ 2 ^ i - 1) * (2 + (ψ x ^ 2 ^ i - 1))` using `by rw [pow_succ, pow_mul]; ring`.

Establish `a` using `norm_sub_norm_le (2 : ℂ) (-(ψ x ^ 2 ^ i - 1))`. Rewrite `a` using `[sub_neg_eq_add, norm_neg, Complex.norm_two]`. Establish `b` using `hb (2 ^ i)`. Rewrite using `[e, norm_mul, pow_succ]`. Use polynomial arithmetic with `[norm_nonneg (ψ x ^ 2 ^ i - 1)]`.

Assume the negation of the conclusion as `hne`. Establish `hp : 0 < ‖ψ x - 1‖` using `norm_pos_iff.2 (sub_ne_zero.2 hne)`. Take `⟨i, hi⟩` from `pow_unbounded_of_one_lt (1 / ‖ψ x - 1‖) (show (1 : ℝ) < 3 / 2 by norm_num)`. Rewrite `hi` using `[div_lt_iff₀ hp]`. Combine the linear relations using `[hg i, hb (2 ^ i)]`.

Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, ψ x ≠ 1 := by`. Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Conclude with `h1 (AddChar.ext _ _ hn)`. Establish `hx0 : x ≠ 0` using `by rintro rfl; simp at hx`.

Establish `hv : 0 < valuation k x` using `by rw [pos_iff_ne_zero]; simpa`. Take `⟨m, hm⟩` from `exists_pow_lt₀ hl (Units.mk0 (valuation k x)⁻¹ (inv_ne_zero hv.ne'))`. Take `⟨c, hc1, hc2⟩` from `Int.exists_least_of_bdd (P := P) ⟨-m, fun z hz => by`. Assume the negation of the conclusion as `hn`. Use `hx (hz x ?_)` and prove the remaining obligations.

Rewrite using `[Units.val_zpow_eq_zpow_val, map_zpow₀]`. Use `le_trans ?_ (zpow_le_zpow_right_of_le_one₀ h0 hl.le (not_le.1 hn).le)` and prove the remaining obligations. Rewrite using `[zpow_neg, zpow_natCast]`. Conclude with `(le_inv_comm₀ (pow_pos h0 _) hv).1 (by simpa using hm.le)⟩ ex`. Use `⟨c, hc1, ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Use `hc2 (c - 1) hn` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_cond {ϖ : kˣ} (hϖ : IsUnif ϖ) {ψ : AddChar k ℂ} (hc : Continuous ψ) (h1 : ψ ≠ 1) : ∃ c : ℤ,
    (∀ x, valuation k x ≤ valuation k ((ϖ ^ c : kˣ) : k) → ψ x = 1) ∧
      ∃ x, valuation k x ≤ valuation k ((ϖ ^ (c - 1) : kˣ) : k) ∧ ψ x ≠ 1 := by
  have hl := unif_lt hϖ
  have h0 : 0 < valuation k (ϖ : k) := by rw [pos_iff_ne_zero]; simp
  let P : ℤ → Prop := fun c => ∀ x, valuation k x ≤ valuation k ((ϖ ^ c : kˣ) : k) → ψ x = 1
  have ex : ∃ c, P c := by
    have : {x | ‖ψ x - 1‖ < 1 / 2} ∈ 𝓝 (0 : k) := (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)
    obtain ⟨γ, hγ⟩ := IsValuativeTopology.mem_nhds_zero_iff _ |>.1 this
    obtain ⟨m, hm⟩ := exists_pow_lt₀ hl γ
    refine ⟨m, fun x hx => ?_⟩
    have hb : ∀ i : ℕ, ‖ψ x ^ i - 1‖ < 1 / 2 := fun i => by
      rw [← AddChar.map_nsmul_eq_pow]
      refine hγ (lt_of_le_of_lt ?_ hm)
      have : valuation k (i • x) ≤ valuation k x := by
        rw [nsmul_eq_mul, map_mul]
        exact mul_le_of_le_one_left' (natCast_mem (valuation k).integer i)
      simpa using this.trans hx
    have hg : ∀ i : ℕ, (3 / 2 : ℝ) ^ i * ‖ψ x - 1‖ ≤ ‖ψ x ^ 2 ^ i - 1‖ := fun i => by
      induction i with
      | zero => simp
      | succ i ih =>
        have e : ψ x ^ 2 ^ (i + 1) - 1 = (ψ x ^ 2 ^ i - 1) * (2 + (ψ x ^ 2 ^ i - 1)) := by rw [pow_succ, pow_mul]; ring
        have a := norm_sub_norm_le (2 : ℂ) (-(ψ x ^ 2 ^ i - 1))
        rw [sub_neg_eq_add, norm_neg, Complex.norm_two] at a
        have b := hb (2 ^ i)
        rw [e, norm_mul, pow_succ]
        nlinarith [norm_nonneg (ψ x ^ 2 ^ i - 1)]
    by_contra hne
    have hp : 0 < ‖ψ x - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt (1 / ‖ψ x - 1‖) (show (1 : ℝ) < 3 / 2 by norm_num)
    rw [div_lt_iff₀ hp] at hi
    linarith [hg i, hb (2 ^ i)]
  obtain ⟨x, hx⟩ : ∃ x, ψ x ≠ 1 := by
    by_contra hn
    push Not at hn
    exact h1 (AddChar.ext _ _ hn)
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hv : 0 < valuation k x := by rw [pos_iff_ne_zero]; simpa
  obtain ⟨m, hm⟩ := exists_pow_lt₀ hl (Units.mk0 (valuation k x)⁻¹ (inv_ne_zero hv.ne'))
  obtain ⟨c, hc1, hc2⟩ := Int.exists_least_of_bdd (P := P) ⟨-m, fun z hz => by
    by_contra hn
    refine hx (hz x ?_)
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
    refine le_trans ?_ (zpow_le_zpow_right_of_le_one₀ h0 hl.le (not_le.1 hn).le)
    rw [zpow_neg, zpow_natCast]
    exact (le_inv_comm₀ (pow_pos h0 _) hv).1 (by simpa using hm.le)⟩ ex
  refine ⟨c, hc1, ?_⟩
  by_contra hn
  push Not at hn
  have := hc2 (c - 1) hn
  omega

def IntM {a b : Type} (Y : Matrix a b k) : Prop := ∀ i j, valuation k (Y i j) ≤ 1

/- English proof (translation)
Introduce `i j` and use `show (Y * Z) i j ∈ (valuation k).integer from Subring.sum_mem _ fun l _ => Subring.mul_mem _ (h i l) (h' l j)`.
-/
theorem IntM.mul {a b c : Type} [Fintype b] {Y : Matrix a b k} {Z : Matrix b c k} (h : IntM Y) (h' : IntM Z) : IntM (Y * Z) :=
  fun i j => show (Y * Z) i j ∈ (valuation k).integer from
    Subring.sum_mem _ fun l _ => Subring.mul_mem _ (h i l) (h' l j)

/- English proof (translation)
Establish `: IntM (Y * g.1) ↔ IntM Y` using `⟨fun a => by simpa [Matrix.mul_assoc] using a.mul h', fun a => a.mul h⟩`. Distinguish the cases in `hY : IntM Y`. Rewrite using `[oneO, Set.indicator_of_mem (this.2 hY), Set.indicator_of_mem hY]`. Both sides reduce to the same expression. Rewrite using `[oneO, Set.indicator_of_notMem (mt this.1 hY), Set.indicator_of_notMem hY]`.
-/
theorem oneO_mul {g : GL (Fin d) k} (h : IntM g.1) (h' : IntM (g⁻¹).1) (Y : Matrix (Fin n) (Fin d) k) :
    oneO k n d (Y * g.1) = oneO k n d Y := by
  have : IntM (Y * g.1) ↔ IntM Y := ⟨fun a => by simpa [Matrix.mul_assoc] using a.mul h', fun a => a.mul h⟩
  by_cases hY : IntM Y
  · rw [oneO, Set.indicator_of_mem (this.2 hY), Set.indicator_of_mem hY]; rfl
  · rw [oneO, Set.indicator_of_notMem (mt this.1 hY), Set.indicator_of_notMem hY]

/- English proof (translation)
The claim follows from `(valuation k).isOpen_integer`.
-/
theorem isOpen_int : IsOpen {x : k | valuation k x ≤ 1} := (valuation k).isOpen_integer

/- English proof (translation)
Rewrite using `[show ((2 * m : ℕ) : ℂ) / 2 = m by push_cast; ring, apow, nabs_uniformiser hϖ.irreducible (x := ϖ) rfl, Complex.cpow_natCast]`. Simplify using the standard rewrite rules.
-/
theorem apow_unif {ϖ : kˣ} (hϖ : IsUnif ϖ) (m : ℕ) : apow ϖ (((2 * m : ℕ) : ℂ) / 2) = ((resCard k : ℂ) ^ m)⁻¹ := by
  rw [show ((2 * m : ℕ) : ℂ) / 2 = m by push_cast; ring, apow, nabs_uniformiser hϖ.irreducible (x := ϖ) rfl, Complex.cpow_natCast]
  simp

def yy (q r : ℂ) (c : ℤ) (m : ℕ) : ℂ := (q * r) ^ (-(m : ℤ)) * ∑ i ∈ Finset.range (2 * m - c + 1).toNat, r ^ i

/- English proof (translation)
Unfold `yy`. Break down `le_or_gt (2 * m - c + 1) 0 with h | h` into its components or cases. Simplify using `[Int.toNat_eq_zero.2 h]`. Take `⟨N, hN⟩ : ∃ N : ℕ, 2 * m - c = N` from `⟨(2 * m - c).toNat, by omega⟩`. Establish `e : (2 * m - c + 1).toNat = N + 1` using `by omega`.

Establish `s : ∑ i ∈ Finset.range (N + 1), r⁻¹ ^ i = (r ^ N)⁻¹ * ∑ i ∈ Finset.range (N + 1), r ^ i`. Rewrite using `[← Finset.sum_range_reflect, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Take `⟨l, rfl⟩` from `Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))`. Rewrite using `[show i + l + 1 - 1 - i = l by omega, pow_add, inv_pow]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e, s, show c = (m : ℤ) + m - N by omega, zpow_sub₀ hr, zpow_add₀ hr]`. Simplify using `only [zpow_neg, zpow_natCast, inv_pow, mul_pow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem yy_inv (q : ℂ) {r : ℂ} (hr : r ≠ 0) (c : ℤ) (m : ℕ) : yy q r⁻¹ c m = r ^ c * yy q r c m := by
  unfold yy
  rcases le_or_gt (2 * m - c + 1) 0 with h | h
  · simp [Int.toNat_eq_zero.2 h]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 * m - c = N := ⟨(2 * m - c).toNat, by omega⟩
  have e : (2 * m - c + 1).toNat = N + 1 := by omega
  have s : ∑ i ∈ Finset.range (N + 1), r⁻¹ ^ i = (r ^ N)⁻¹ * ∑ i ∈ Finset.range (N + 1), r ^ i := by
    rw [← Finset.sum_range_reflect, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
    rw [show i + l + 1 - 1 - i = l by omega, pow_add, inv_pow]
    field_simp
  rw [e, s, show c = (m : ℤ) + m - N by omega, zpow_sub₀ hr, zpow_add₀ hr]
  simp only [zpow_neg, zpow_natCast, inv_pow, mul_pow]
  field_simp

/- English proof (translation)
Use `set R := ‖r‖ with hR`. Establish `hR1 : 1 < R` using `hq.trans hr`. Establish `h1 : Tendsto (fun m : ℕ => (R ^ (1 - c) * (R / q) ^ m - 1) / (R + 1)) atTop atTop` using `(tendsto_atTop_add_const_right _ (-1) ((tendsto_pow_atTop_atTop_of_one_lt ((one_lt_div (by linarith)).2 hr)).const_mul_atTop (by positivity))).atTop_div_const (by linarith)`. Use `tendsto_atTop_mono' _ ?_ h1` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop c.toNat] with m hm`.

Take `⟨N, hN⟩ : ∃ N : ℕ, 2 * m - c + 1 = N` from `⟨(2 * m - c + 1).toNat, by omega⟩`. Establish `a : R ^ N - 1 ≤ ‖∑ i ∈ Finset.range N, r ^ i‖ * (R + 1)`. Establish `b` using `norm_sub_norm_le (r ^ N) 1`. Rewrite `b` using `[← geom_sum_mul, norm_mul, norm_pow, norm_one]`. Conclude with `b.trans (mul_le_mul_of_nonneg_left (by simpa using norm_sub_le r 1) (norm_nonneg _))`.

Establish `hQ : 1 ≤ (q * R) ^ m` using `one_le_pow₀ (by nlinarith)`. Establish `e : R ^ (1 - c) * (R / q) ^ m = ((q * R) ^ m)⁻¹ * R ^ N`. Rewrite using `[← zpow_natCast R N, ← hN, show 2 * (m : ℤ) - c + 1 = m + m + (1 - c) by ring, zpow_add₀ (by linarith), zpow_add₀ (by linarith), zpow_natCast, div_pow, mul_pow]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[yy, hN, Int.toNat_natCast, norm_mul, norm_zpow, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith), zpow_neg, zpow_natCast, div_le_iff₀ (by linarith), e, mul_assoc]`.

Establish `i1 : ((q * R) ^ m)⁻¹ ≤ 1` using `inv_le_one_of_one_le₀ hQ`. Establish `i0 : 0 ≤ ((q * R) ^ m)⁻¹` using `by positivity`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left a i0]`.
-/
theorem yy_tendsto {q : ℝ} (hq : 1 < q) {r : ℂ} (hr : q < ‖r‖) (c : ℤ) : Tendsto (fun m => ‖yy q r c m‖) atTop atTop := by
  set R := ‖r‖ with hR
  have hR1 : 1 < R := hq.trans hr
  have h1 : Tendsto (fun m : ℕ => (R ^ (1 - c) * (R / q) ^ m - 1) / (R + 1)) atTop atTop :=
    (tendsto_atTop_add_const_right _ (-1) ((tendsto_pow_atTop_atTop_of_one_lt
      ((one_lt_div (by linarith)).2 hr)).const_mul_atTop (by positivity))).atTop_div_const (by linarith)
  refine tendsto_atTop_mono' _ ?_ h1
  filter_upwards [eventually_ge_atTop c.toNat] with m hm
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 * m - c + 1 = N := ⟨(2 * m - c + 1).toNat, by omega⟩
  have a : R ^ N - 1 ≤ ‖∑ i ∈ Finset.range N, r ^ i‖ * (R + 1) := by
    have b := norm_sub_norm_le (r ^ N) 1
    rw [← geom_sum_mul, norm_mul, norm_pow, norm_one] at b
    exact b.trans (mul_le_mul_of_nonneg_left (by simpa using norm_sub_le r 1) (norm_nonneg _))
  have hQ : 1 ≤ (q * R) ^ m := one_le_pow₀ (by nlinarith)
  have e : R ^ (1 - c) * (R / q) ^ m = ((q * R) ^ m)⁻¹ * R ^ N := by
    rw [← zpow_natCast R N, ← hN, show 2 * (m : ℤ) - c + 1 = m + m + (1 - c) by ring, zpow_add₀ (by linarith), zpow_add₀ (by linarith),
      zpow_natCast, div_pow, mul_pow]
    field_simp
  rw [yy, hN, Int.toNat_natCast, norm_mul, norm_zpow, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith), zpow_neg,
    zpow_natCast, div_le_iff₀ (by linarith), e, mul_assoc]
  have i1 : ((q * R) ^ m)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hQ
  have i0 : 0 ≤ ((q * R) ^ m)⁻¹ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left a i0]

end PositivityTheory.ThKEnd.Cusp.Key

end
