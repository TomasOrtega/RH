import ReciprocityTheory.AnalyticForms.PotentialTheory.IsCompatChartChart
import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas

namespace ReciprocityTheory.AnForm.M.PLAux

open MeasureTheory FinHolAtlas Filter Topology
open ReciprocityTheory.AnForm.A (hypInclAt densHypAt)
open scoped ContDiff

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]

omit [TopologicalSpace X] [T2Space X] [CompactSpace X] in
/- English proof (translation)
Repeatedly rewrite using `[hg]`. Establish `h1 : ∀ k, (σ k).elim 1 (fun i => z i ^ m k) = ∏ i, (if σ k = some i then z i ^ m k else 1)`. Introduce `k`. Consider the cases of `h : σ k with`. Consider the case `none => simp`.

Consider the case `some j => simp [Finset.prod_ite_eq]`. Repeatedly rewrite using `[h1]`. Rewrite using `[Finset.prod_comm]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[zpow_natCast, ← Finset.prod_pow_eq_pow_sum]`.

Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem prod_sigma {r n : ℕ} (σ : Fin r → Option (Fin n)) (m : Fin r → ℕ) (z : Fin n → ℂ)
    (g : Fin r → ℂ) (hg : ∀ k, g k = (σ k).elim 1 (fun i => z i ^ m k)) :
    ∏ k, g k = ∏ i, z i ^ ((∑ k, if σ k = some i then m k else 0 : ℕ) : ℤ) := by
  simp_rw [hg]
  have h1 : ∀ k, (σ k).elim 1 (fun i => z i ^ m k) = ∏ i, (if σ k = some i then z i ^ m k else 1) := by
    intro k
    cases h : σ k with
    | none => simp
    | some j => simp [Finset.prod_ite_eq]
  simp_rw [h1]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [zpow_natCast, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  split_ifs <;> simp

omit [TopologicalSpace X] [T2Space X] [CompactSpace X] in
/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `push_cast`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Apply the tactic sequence `split_ifs <;> simp`. Use `_ = ∑ k, (m k : ℝ) * ∑ i, (if σ k = some i then Xs i else 0) := by`. Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[Finset.mul_sum]`.
-/
theorem sum_sigma {r n : ℕ} (σ : Fin r → Option (Fin n)) (m : Fin r → ℕ) (Xs : Fin n → ℝ) :
    ∑ i, (((∑ k, if σ k = some i then m k else 0 : ℕ) : ℤ) : ℝ) * Xs i =
      ∑ k, (m k : ℝ) * ∑ i, (if σ k = some i then Xs i else 0) := by
  calc ∑ i, (((∑ k, if σ k = some i then m k else 0 : ℕ) : ℤ) : ℝ) * Xs i
      = ∑ i, ∑ k, (m k : ℝ) * (if σ k = some i then Xs i else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        push_cast
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs <;> simp
    _ = ∑ k, (m k : ℝ) * ∑ i, (if σ k = some i then Xs i else 0) := by
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.sum_empty]`. Conclude with `mInt_zero_fun A Φ (fun _ => rfl)`. Consider the case `insert j s hj ih`.

Establish `hcont : Continuous (fun p => ∑ j ∈ s, f j p)` using `continuous_finset_sum _ fun j _ => hf j`. Establish `h` using `mIntLinear A Φ hΦ 1 (f j) (fun p => ∑ j ∈ s, f j p) (mIntegrableCont A Φ hΦ _ (hf j)) (mIntegrableCont A Φ hΦ _ hcont)`. Simplify using `only [one_mul] at h`. Repeatedly rewrite using `[Finset.sum_insert hj]`. Rewrite using `[← ih]`.

Conclude with `h`.
-/
theorem mInt_sum_cont {e' : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    (A : FinHolAtlas e' Y) (Φ : Fin e' → LocPot Y) (hΦ : ∀ i, IsPotential A (Φ i)) {ι : Type}
    (s : Finset ι) (f : ι → Y → ℝ) (hf : ∀ j, Continuous (f j)) :
    mInt A Φ (fun p => ∑ j ∈ s, f j p) = ∑ j ∈ s, mInt A Φ (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact mInt_zero_fun A Φ (fun _ => rfl)
  | insert j s hj ih =>
    have hcont : Continuous (fun p => ∑ j ∈ s, f j p) := continuous_finset_sum _ fun j _ => hf j
    have h := mIntLinear A Φ hΦ 1 (f j) (fun p => ∑ j ∈ s, f j p)
      (mIntegrableCont A Φ hΦ _ (hf j)) (mIntegrableCont A Φ hΦ _ hcont)
    simp only [one_mul] at h
    simp_rw [Finset.sum_insert hj]
    rw [← ih]
    exact h

/- English proof (translation)
Establish `hdens : ∀ (j' : Fin A.n) (y : Fin (e + 1) → ℂ), y ∈ (A.chart j').target → locDens A (Fin.cons (LocPot.ofFun fun p => ∑ j ∈ t, f j p) Φ) j' y = ∑ j ∈ t, locDens A (Fin.cons (LocPot.ofFun (f j)) Φ) j' y`. Introduce `j' y hy`. Set `ψs : Fin e → (Fin (e + 1) → ℂ) → ℝ` to `fun i y' => (Φ i).φ ((A.chart j').symm y) ((A.chart j').symm y')`. Establish `hfam : ∀ u : X → ℝ, (fun i y' => ((Fin.cons (LocPot.ofFun u) Φ : Fin (e + 1) → LocPot X) i).φ ((A.chart j').symm y) ((A.chart j').symm y')) = Fin.cons (u ∘ (A.chart j').symm) ψs`. Introduce `u`.

Use function extensionality and compare the values at `i`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> rfl`. Establish `hmem : (A.chart j').target ∩ (A.chart j').symm ⁻¹' Set.univ ∈ nhds y`. Simplify using `using (A.chart j').open_target.mem_nhds hy`. Establish `hsmooth : ∀ j, ContDiffAt ℝ 2 (f j ∘ (A.chart j').symm) y` using `fun j => by`.

Establish `h` using `((hf j) j').contDiffAt hmem`. Establish `hle : (2 : WithTop ℕ∞) ≤ ∞` using `by first`. Consider the case `exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)`. Consider the case `exact WithTop.coe_le_coe.2 le_top`. Consider the case `(norm_num; done)`.

Consider the case `(simp; done)`. Conclude with `h.of_le hle`. Establish `key : ∀ F G : (Fin (e + 1) → ℂ) → ℝ, ContDiffAt ℝ 2 F y → ContDiffAt ℝ 2 G y → maDens (Fin.cons (fun w => F w + G w) ψs) y = maDens (Fin.cons F ψs) y + maDens (Fin.cons G ψs) y`. Introduce `F G hF hG`. Unfold `maDens`.

Establish `e1 : ∀ H : (Fin (e + 1) → ℂ) → ℝ, (fun k => hessC ((Fin.cons H ψs : Fin (e + 1) → (Fin (e + 1) → ℂ) → ℝ) k) y) = Fin.cons (hessC H y) (fun k => hessC (ψs k) y)`. Introduce `H`. Use function extensionality and compare the values at `k`. Apply the tactic sequence `refine Fin.cases ?_ (fun k => ?_) k <;> rfl`. Rewrite using `[e1, e1, e1, ReciprocityTheory.AnForm.A.hessC_add F G y hF hG]`.

Establish `h` using `ReciprocityTheory.AnForm.A.mdisc_cons_smul_add 1 1 (hessC F y) (hessC G y) (fun k => hessC (ψs k) y)`. Simplify using `only [one_smul, one_mul] at h`. Rewrite using `[h, Complex.add_re]`. Expand and normalize the polynomial expressions, which then agree. Establish `key0 : maDens (Fin.cons (fun _ => (0 : ℝ)) ψs) y = 0`.

Establish `h` using `key (fun _ => 0) (fun _ => 0) contDiffAt_const contDiffAt_const`. Simplify using `only [add_zero] at h`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [locDens, hfam]`. Proceed by induction on `t using Finset.induction_on with`.

Consider the case `empty`. Establish `h0 : ((fun p => ∑ i ∈ (∅ : Finset ι), f i p) ∘ (A.chart j').symm) = fun _ => (0 : ℝ)`. Use function extensionality and compare the values at `w`. Simplify using the standard rewrite rules. Rewrite using `[h0, Finset.sum_empty, key0]`.

Consider the case `insert j t hj ih`. Rewrite using `[Finset.sum_insert hj, ← ih]`. Establish `e2 : ((fun p => ∑ i ∈ insert j t, f i p) ∘ (A.chart j').symm) = fun w => (f j ∘ (A.chart j').symm) w + ((fun p => ∑ i ∈ t, f i p) ∘ (A.chart j').symm) w`. Use function extensionality and compare the values at `w`. Simplify using `[Finset.sum_insert hj]`.

Establish `hsum : ContDiffAt ℝ 2 ((fun p => ∑ i ∈ t, f i p) ∘ (A.chart j').symm) y` using `by show ContDiffAt ℝ 2 (fun w => ∑ i ∈ t, (f i ∘ (A.chart j').symm) w) y`. Conclude with `ContDiffAt.sum fun i _ => hsmooth i`. Rewrite using `[e2, key _ _ (hsmooth j) hsum]`. Establish `hint : ∀ j, MIntegrable A (Fin.cons (LocPot.ofFun (f j)) Φ) (logNormSec L s)` using `fun j => hℓ _ (fun i => by`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations.

Conclude with `isPotential_ofFun A (f j) (hf j)`. Conclude with `hΦ i)`. Unfold `mInt`. Use `split_ifs with hP`. Unfold `integralWith conv_rhs => rw [Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun j' _ => ?_` and prove the remaining obligations. Rewrite using `[← integral_finset_sum t (fun j _ => integrableOn_weight A hP.some _ _ (hint j) j')]`. Establish `heq : Set.EqOn (fun y => hP.some.χ j' ((A.chart j').symm y) * logNormSec L s ((A.chart j').symm y) * locDens A (Fin.cons (LocPot.ofFun fun p => ∑ j ∈ t, f j p) Φ) j' y) (fun y => ∑ j ∈ t, hP.some.χ j' ((A.chart j').symm y) * logNormSec L s ((A.chart j').symm y) * locDens A (Fin.c …`. Introduce `y hy`. Simplify using `only`.

Rewrite using `[hdens j' y hy, Finset.mul_sum]`. Use `first`. Consider the case `exact setIntegral_congr_fun (A.chart j').open_target.measurableSet heq`. Consider the case `exact setIntegral_congr (A.chart j').open_target.measurableSet heq`. Simplify using the standard rewrite rules.
-/
theorem lhs_sum (A : FinHolAtlas (e + 1) X) (L : LocPot X) (s : X → X → ℂ)
    (hℓ : ∀ Φ' : Fin (e + 1) → LocPot X, (∀ i, IsPotential A (Φ' i)) →
      MIntegrable A Φ' (logNormSec L s))
    (Φ : Fin e → LocPot X) (hΦ : ∀ k, IsPotential A (Φ k)) {ι : Type} (t : Finset ι)
    (f : ι → X → ℝ) (hf : ∀ j, A.Smooth (f j)) :
    mInt A (Fin.cons (LocPot.ofFun fun p => ∑ j ∈ t, f j p) Φ) (logNormSec L s) =
      ∑ j ∈ t, mInt A (Fin.cons (LocPot.ofFun (f j)) Φ) (logNormSec L s) := by
  classical
  have hdens : ∀ (j' : Fin A.n) (y : Fin (e + 1) → ℂ), y ∈ (A.chart j').target →
      locDens A (Fin.cons (LocPot.ofFun fun p => ∑ j ∈ t, f j p) Φ) j' y =
        ∑ j ∈ t, locDens A (Fin.cons (LocPot.ofFun (f j)) Φ) j' y := by
    intro j' y hy
    let ψs : Fin e → (Fin (e + 1) → ℂ) → ℝ :=
      fun i y' => (Φ i).φ ((A.chart j').symm y) ((A.chart j').symm y')
    have hfam : ∀ u : X → ℝ, (fun i y' => ((Fin.cons (LocPot.ofFun u) Φ : Fin (e + 1) → LocPot X) i).φ
        ((A.chart j').symm y) ((A.chart j').symm y')) = Fin.cons (u ∘ (A.chart j').symm) ψs := by
      intro u
      funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> rfl
    have hmem : (A.chart j').target ∩ (A.chart j').symm ⁻¹' Set.univ ∈ nhds y := by
      simpa using (A.chart j').open_target.mem_nhds hy
    have hsmooth : ∀ j, ContDiffAt ℝ 2 (f j ∘ (A.chart j').symm) y := fun j => by
      have h := ((hf j) j').contDiffAt hmem
      have hle : (2 : WithTop ℕ∞) ≤ ∞ := by
        first
          | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
          | exact WithTop.coe_le_coe.2 le_top
          | (norm_num; done)
          | (simp; done)
      exact h.of_le hle
    have key : ∀ F G : (Fin (e + 1) → ℂ) → ℝ, ContDiffAt ℝ 2 F y → ContDiffAt ℝ 2 G y →
        maDens (Fin.cons (fun w => F w + G w) ψs) y =
          maDens (Fin.cons F ψs) y + maDens (Fin.cons G ψs) y := by
      intro F G hF hG
      unfold maDens
      have e1 : ∀ H : (Fin (e + 1) → ℂ) → ℝ,
          (fun k => hessC ((Fin.cons H ψs : Fin (e + 1) → (Fin (e + 1) → ℂ) → ℝ) k) y) =
            Fin.cons (hessC H y) (fun k => hessC (ψs k) y) := by
        intro H
        funext k
        refine Fin.cases ?_ (fun k => ?_) k <;> rfl
      rw [e1, e1, e1, ReciprocityTheory.AnForm.A.hessC_add F G y hF hG]
      have h := ReciprocityTheory.AnForm.A.mdisc_cons_smul_add 1 1 (hessC F y) (hessC G y) (fun k => hessC (ψs k) y)
      simp only [one_smul, one_mul] at h
      rw [h, Complex.add_re]
      ring
    have key0 : maDens (Fin.cons (fun _ => (0 : ℝ)) ψs) y = 0 := by
      have h := key (fun _ => 0) (fun _ => 0) contDiffAt_const contDiffAt_const
      simp only [add_zero] at h
      linarith
    simp only [locDens, hfam]
    induction t using Finset.induction_on with
    | empty =>
      have h0 : ((fun p => ∑ i ∈ (∅ : Finset ι), f i p) ∘ (A.chart j').symm) = fun _ => (0 : ℝ) := by
        funext w
        simp
      rw [h0, Finset.sum_empty, key0]
    | insert j t hj ih =>
      rw [Finset.sum_insert hj, ← ih]
      have e2 : ((fun p => ∑ i ∈ insert j t, f i p) ∘ (A.chart j').symm) =
          fun w => (f j ∘ (A.chart j').symm) w + ((fun p => ∑ i ∈ t, f i p) ∘ (A.chart j').symm) w := by
        funext w
        simp [Finset.sum_insert hj]
      have hsum : ContDiffAt ℝ 2 ((fun p => ∑ i ∈ t, f i p) ∘ (A.chart j').symm) y := by
        show ContDiffAt ℝ 2 (fun w => ∑ i ∈ t, (f i ∘ (A.chart j').symm) w) y
        exact ContDiffAt.sum fun i _ => hsmooth i
      rw [e2, key _ _ (hsmooth j) hsum]
  have hint : ∀ j, MIntegrable A (Fin.cons (LocPot.ofFun (f j)) Φ) (logNormSec L s) := fun j =>
    hℓ _ (fun i => by
      refine Fin.cases ?_ (fun i => ?_) i
      · exact isPotential_ofFun A (f j) (hf j)
      · exact hΦ i)
  unfold mInt
  split_ifs with hP
  · unfold integralWith
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [← integral_finset_sum t (fun j _ => integrableOn_weight A hP.some _ _ (hint j) j')]
    have heq : Set.EqOn
        (fun y => hP.some.χ j' ((A.chart j').symm y) * logNormSec L s ((A.chart j').symm y) *
          locDens A (Fin.cons (LocPot.ofFun fun p => ∑ j ∈ t, f j p) Φ) j' y)
        (fun y => ∑ j ∈ t, hP.some.χ j' ((A.chart j').symm y) * logNormSec L s ((A.chart j').symm y) *
          locDens A (Fin.cons (LocPot.ofFun (f j)) Φ) j' y) (A.chart j').target := by
      intro y hy
      simp only
      rw [hdens j' y hy, Finset.mul_sum]
    first
      | exact setIntegral_congr_fun (A.chart j').open_target.measurableSet heq
      | exact setIntegral_congr (A.chart j').open_target.measurableSet heq
  · simp

/- English proof (translation)
Establish `hℓ : ∀ Φ' : Fin (e + 1) → LocPot X, (∀ i, IsPotential A (Φ' i)) → MIntegrable A Φ' (logNormSec L s)` using `fun Φ' hΦ' => logNormIntegrable A L s m W hL hs hSNC Φ' hΦ'`. Establish `hsu' : ∀ p ∈ ψ.source, s x p = u p * ∏ i, ψ p i ^ (((∑ k, if σ k = some i then m k else 0 : ℕ) : ℤ))`. Introduce `p hp`. Rewrite using `[hsu p hp, prod_sigma σ m (ψ p) (fun k => (σ k).elim 1 (fun i => ψ p i ^ m k)) (fun k => rfl)]`. Rewrite using `[pl_chart A L s hL hs hℓ Φ hΦ x ψ hψ hψL u hu hu0 (fun i => ((∑ k, if σ k = some i then m k else 0 : ℕ) : ℤ)) hsu' hV hVψ hVΦ hv hvV]`.

Use `congr 1`. Rewrite using `[sum_sigma σ m (fun i => ∫ w, chartExt ψ v (hypInclAt i w) * densHypAt i (fun k => (Φ k).φ x ∘ ψ.symm) w)]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `congr 1`. Consider the cases of `hσ : σ k with`.

Consider the case `none`. Simplify using `only [reduceCtorEq, if_false, Finset.sum_const_zero]`. Use `(mInt_zero_fun (B k) _ (fun p => ?_)).symm` and prove the remaining obligations. Use `show v p.1 = 0`. Assume the negation of the conclusion as `hne`.

Establish `hp : p.1 ∈ tsupport v` using `subset_tsupport _ hne`. Establish `hpψ` using `hVψ (hvV hp)`. Establish `hmem : p.1 ∈ W k ∩ ψ.source` using `⟨p.2, hpψ⟩`. Rewrite `hmem` using `[hWψ k]`. Take `⟨i, hi, -⟩` from `hmem.2`.

Rewrite `hi` using `[hσ]`. Conclude with `absurd hi (by simp)`. Consider the case `some i`. Simplify using `only [Option.some.injEq, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Use `haveI : CompactSpace (W k) := isCompact_iff_compactSpace.1 (SimpleNormalCrossingSliceCharts.isClosed_divisorComponent A L s m W hSNC k).isCompact`.

Establish `hWψ' : W k ∩ ψ.source = {p ∈ ψ.source | ψ p i = 0}`. Rewrite using `[hWψ k, hσ]`. Use extensionality with `y`. Simplify using the standard rewrite rules. Conclude with `(slice_mInt (B k) (hB k) Φ hΦ hψ hWψ' x hV hVψ hVΦ (hxW k) hv hvV).symm`.
-/
theorem pl_good (A : FinHolAtlas (e + 1) X) (L : LocPot X) (s : X → X → ℂ) {r : ℕ} (m : Fin r → ℕ)
    (W : Fin r → Set X) (B : ∀ k, FinHolAtlas e (W k)) (hL : IsPotential A L)
    (hs : IsSection A L s) (hSNC : IsSNC A L s m W) (hB : ∀ k, HoloMap (B k) A Subtype.val)
    (Φ : Fin e → LocPot X) (hΦ : ∀ k, IsPotential A (Φ k)) (x : X)
    (ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)) (hψ : IsCompatChart A ψ)
    (hψL : ψ.source ⊆ L.U x) (σ : Fin r → Option (Fin (e + 1)))
    (hWψ : ∀ k, W k ∩ ψ.source = {y ∈ ψ.source | ∃ i, σ k = some i ∧ ψ y i = 0})
    (u : X → ℂ) (hu : A.HoloOn ψ.source u) (hu0 : ∀ y ∈ ψ.source, u y ≠ 0)
    (hsu : ∀ y ∈ ψ.source, s x y = u y * ∏ k, (σ k).elim 1 (fun i => ψ y i ^ m k))
    {V : Set X} (hV : IsOpen V) (hVψ : V ⊆ ψ.source) (hVΦ : ∀ k, V ⊆ (Φ k).U x)
    (hxW : ∀ k, x ∉ W k → V ∩ W k = ∅) {v : X → ℝ} (hv : A.Smooth v) (hvV : tsupport v ⊆ V) :
    mInt A (Fin.cons (LocPot.ofFun v) Φ) (logNormSec L s) =
      ∑ k, (m k : ℝ) * mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val)
          (v ∘ Subtype.val) - mInt A (Fin.cons L Φ) v := by
  classical
  have hℓ : ∀ Φ' : Fin (e + 1) → LocPot X, (∀ i, IsPotential A (Φ' i)) →
      MIntegrable A Φ' (logNormSec L s) :=
    fun Φ' hΦ' => logNormIntegrable A L s m W hL hs hSNC Φ' hΦ'
  have hsu' : ∀ p ∈ ψ.source, s x p =
      u p * ∏ i, ψ p i ^ (((∑ k, if σ k = some i then m k else 0 : ℕ) : ℤ)) := by
    intro p hp
    rw [hsu p hp, prod_sigma σ m (ψ p) (fun k => (σ k).elim 1 (fun i => ψ p i ^ m k)) (fun k => rfl)]
  rw [pl_chart A L s hL hs hℓ Φ hΦ x ψ hψ hψL u hu hu0
    (fun i => ((∑ k, if σ k = some i then m k else 0 : ℕ) : ℤ)) hsu' hV hVψ hVΦ hv hvV]
  congr 1
  rw [sum_sigma σ m (fun i => ∫ w, chartExt ψ v (hypInclAt i w) *
    densHypAt i (fun k => (Φ k).φ x ∘ ψ.symm) w)]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  cases hσ : σ k with
  | none =>
    simp only [reduceCtorEq, if_false, Finset.sum_const_zero]
    refine (mInt_zero_fun (B k) _ (fun p => ?_)).symm
    show v p.1 = 0
    by_contra hne
    have hp : p.1 ∈ tsupport v := subset_tsupport _ hne
    have hpψ := hVψ (hvV hp)
    have hmem : p.1 ∈ W k ∩ ψ.source := ⟨p.2, hpψ⟩
    rw [hWψ k] at hmem
    obtain ⟨i, hi, -⟩ := hmem.2
    rw [hσ] at hi
    exact absurd hi (by simp)
  | some i =>
    simp only [Option.some.injEq, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    haveI : CompactSpace (W k) :=
      isCompact_iff_compactSpace.1 (SimpleNormalCrossingSliceCharts.isClosed_divisorComponent A L s m W hSNC k).isCompact
    have hWψ' : W k ∩ ψ.source = {p ∈ ψ.source | ψ p i = 0} := by
      rw [hWψ k, hσ]
      ext y
      simp
    exact (slice_mInt (B k) (hB k) Φ hΦ hψ hWψ' x hV hVψ hVΦ (hxW k) hv hvV).symm

end

end ReciprocityTheory.AnForm.M.PLAux
