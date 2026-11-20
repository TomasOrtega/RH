import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.MultiIndexDerivation
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealOrderDecrease
namespace FunctorialResolution.EmbeddedResolution

open IsLocalRing

def multiIndicesOfDegree (h r : ℕ) : Finset (Fin h → ℕ) :=
  (Fintype.piFinset fun _ : Fin h => Finset.range (r + 1)).filter fun β => ∑ i, β i = r

/- English proof (translation)
Simplify using `only [multiIndicesOfDegree, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]`. Prove the components needed by the constructor for the conclusion. Conclude with `fun hβ => hβ.2`. Introduce `hs`. Use `⟨fun i => ?_, hs⟩` and prove the remaining obligations.

Establish `h1 : β i ≤ r`. Rewrite using `[← hs]`. Conclude with `Finset.single_le_sum (f := β) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)`. Use linear arithmetic over natural numbers and integers.
-/
theorem mem_multiIndicesOfDegree {h r : ℕ} (β : Fin h → ℕ) :
    β ∈ multiIndicesOfDegree h r ↔ ∑ i, β i = r := by
  simp only [multiIndicesOfDegree, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · exact fun hβ => hβ.2
  · intro hs
    refine ⟨fun i => ?_, hs⟩
    have h1 : β i ≤ r := by
      rw [← hs]
      exact Finset.single_le_sum (f := β) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero`. Introduce `f _ hβ`. Establish `h0` using `hβ (fun _ => 0) (by simp)`. Rewrite `h0` using `[multiIndexDeriv_fun_zero]`.

Simplify using `using h0`. Consider the case `succ r ih`. Introduce `f hf hβ`. Establish `key : ∀ i, D i f ∈ IsLocalRing.maximalIdeal R ^ (r + 1)`. Introduce `i`.

Use `ih (D i f) ?_ ?_` and prove the remaining obligations. Establish `h1` using `multiIndexDeriv_mem_pow_sub D (IsLocalRing.maximalIdeal R) (r + 1) hf (unitMultiIndex i)`. Rewrite `h1` using `[multiIndexDeriv_unitMultiIndex, sum_unitMultiIndex]`. Simplify using `using h1`. Introduce `β hβ'`.

Establish `hsum : ∑ j, (β + unitMultiIndex i) j = r + 1`. Simplify using `only [Pi.add_apply]`. Rewrite using `[Finset.sum_add_distrib, hβ', sum_unitMultiIndex]`. Establish `h2` using `hβ (β + unitMultiIndex i) hsum`. Rewrite `h2` using `[multiIndexDeriv_add_unitMultiIndex_apply_first D hDD β i f]`. Then use the resulting hypothesis.

Establish `hfx : f ∈ Ideal.span (Set.range x) ^ (r + 1)` using `by rw [hx]; exact hf`. Establish `hdx : ∀ i, D i f ∈ Ideal.span (Set.range x) ^ (r + 1)`. Introduce `i`. Rewrite using `[hx]`. Conclude with `key i`.

Establish `hres` using `mem_pow_succ_of_deriv_mem_pow k x D hD (hunit (r + 1) (by omega)) hfx hdx`. Rewrite `hres` using `[hx]`. Conclude with `hres`.
-/
private theorem mem_maximalIdeal_pow_succ_of_multiIndexDeriv_mem {k R : Type*} [CommRing k] [CommRing R]
    [IsLocalRing R] [Algebra k R] {h : ℕ} (x : Fin h → R) (D : Fin h → Derivation k R R)
    (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hDD : ∀ i j : Fin h, ∀ a : R, D i (D j a) = D j (D i a))
    (hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((n : ℕ) : R)) (r : ℕ) :
    ∀ f : R, f ∈ IsLocalRing.maximalIdeal R ^ r →
      (∀ β : Fin h → ℕ, (∑ i, β i = r) → multiIndexDeriv D β f ∈ IsLocalRing.maximalIdeal R) →
      f ∈ IsLocalRing.maximalIdeal R ^ (r + 1) := by
  induction r with
  | zero =>
    intro f _ hβ
    have h0 := hβ (fun _ => 0) (by simp)
    rw [multiIndexDeriv_fun_zero] at h0
    simpa using h0
  | succ r ih =>
    intro f hf hβ
    have key : ∀ i, D i f ∈ IsLocalRing.maximalIdeal R ^ (r + 1) := by
      intro i
      refine ih (D i f) ?_ ?_
      · have h1 := multiIndexDeriv_mem_pow_sub D (IsLocalRing.maximalIdeal R) (r + 1) hf
          (unitMultiIndex i)
        rw [multiIndexDeriv_unitMultiIndex, sum_unitMultiIndex] at h1
        simpa using h1
      · intro β hβ'
        have hsum : ∑ j, (β + unitMultiIndex i) j = r + 1 := by
          simp only [Pi.add_apply]
          rw [Finset.sum_add_distrib, hβ', sum_unitMultiIndex]
        have h2 := hβ (β + unitMultiIndex i) hsum
        rwa [multiIndexDeriv_add_unitMultiIndex_apply_first D hDD β i f] at h2
    have hfx : f ∈ Ideal.span (Set.range x) ^ (r + 1) := by rw [hx]; exact hf
    have hdx : ∀ i, D i f ∈ Ideal.span (Set.range x) ^ (r + 1) := by
      intro i; rw [hx]; exact key i
    have hres := mem_pow_succ_of_deriv_mem_pow k x D hD (hunit (r + 1) (by omega)) hfx hdx
    rw [hx] at hres
    exact hres

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hfs β hβ`. Establish `hβ' : ∑ i, β i = r` using `(mem_multiIndicesOfDegree β).mp hβ`. Establish `hm` using `multiIndexDeriv_mem_pow_sub D (IsLocalRing.maximalIdeal R) (r + 1) hfs β`. Rewrite `hm` using `[hβ']`.

Establish `hr1 : r + 1 - r = 1` using `by omega`. Rewrite `hm` using `[hr1, pow_one]`. Conclude with `hm`. Introduce `hall`. Conclude with `mem_maximalIdeal_pow_succ_of_multiIndexDeriv_mem x D hx hD hDD hunit r f hf (fun β hb => hall β ((mem_multiIndicesOfDegree β).mpr hb))`.
-/
theorem mem_maximalIdeal_pow_succ_iff_multiIndexDeriv_mem {k R : Type*} [CommRing k] [CommRing R]
    [IsLocalRing R] [Algebra k R] {h : ℕ} (x : Fin h → R) (D : Fin h → Derivation k R R)
    (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hDD : ∀ i j : Fin h, ∀ a : R, D i (D j a) = D j (D i a))
    (hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((n : ℕ) : R))
    (r : ℕ) {f : R} (hf : f ∈ IsLocalRing.maximalIdeal R ^ r) :
    f ∈ IsLocalRing.maximalIdeal R ^ (r + 1) ↔
      ∀ β ∈ multiIndicesOfDegree h r, multiIndexDeriv D β f ∈ IsLocalRing.maximalIdeal R := by
  constructor
  · intro hfs β hβ
    have hβ' : ∑ i, β i = r := (mem_multiIndicesOfDegree β).mp hβ
    have hm := multiIndexDeriv_mem_pow_sub D (IsLocalRing.maximalIdeal R) (r + 1) hfs β
    rw [hβ'] at hm
    have hr1 : r + 1 - r = 1 := by omega
    rw [hr1, pow_one] at hm
    exact hm
  · intro hall
    exact mem_maximalIdeal_pow_succ_of_multiIndexDeriv_mem x D hx hD hDD hunit r f hf
      (fun β hb => hall β ((mem_multiIndicesOfDegree β).mpr hb))

/- English proof (translation)
Establish `h3 : (n : ℕ∞) ≤ idealOrder I` using `(le_idealOrder_iff I n).mpr h1`. Establish `h4 : ¬ (((n + 1 : ℕ) : ℕ∞) ≤ idealOrder I)` using `fun hc => h2 ((le_idealOrder_iff I (n + 1)).mp hc)`. Rewrite `h4` using `[not_le]`. Take `⟨m, hm⟩` from `ENat.ne_top_iff_exists.mp (ne_top_of_lt h4)`. Rewrite `h3`, `h4`, the goal using `[← hm]`.

Establish `hle : n ≤ m` using `by exact_mod_cast h3`. Establish `hlt : m < n + 1` using `by exact_mod_cast h4`. Establish `hme : m = n` using `by omega`. Conclude with `hme` after adjusting the coercions.
-/
private theorem idealOrder_eq_of_le_of_not_le {R : Type*} [CommRing R] [IsLocalRing R] {n : ℕ}
    {I : Ideal R} (h1 : I ≤ IsLocalRing.maximalIdeal R ^ n)
    (h2 : ¬ I ≤ IsLocalRing.maximalIdeal R ^ (n + 1)) : idealOrder I = (n : ℕ∞) := by
  have h3 : (n : ℕ∞) ≤ idealOrder I := (le_idealOrder_iff I n).mpr h1
  have h4 : ¬ (((n + 1 : ℕ) : ℕ∞) ≤ idealOrder I) := fun hc =>
    h2 ((le_idealOrder_iff I (n + 1)).mp hc)
  rw [not_le] at h4
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt h4)
  rw [← hm] at h3 h4 ⊢
  have hle : n ≤ m := by exact_mod_cast h3
  have hlt : m < n + 1 := by exact_mod_cast h4
  have hme : m = n := by omega
  exact_mod_cast hme

private def ofDigitsFin (N : ℕ) {h : ℕ} (β : Fin h → ℕ) : ℕ := ∑ i, β i * N ^ (i : ℕ)

/- English proof (translation)
Simplify using `only [ofDigitsFin, add_mul]`. Rewrite using `[Finset.sum_add_distrib]`.
-/
private theorem ofDigits_add (N : ℕ) {h : ℕ} (β γ : Fin h → ℕ) :
    ofDigitsFin N (fun i => β i + γ i) = ofDigitsFin N β + ofDigitsFin N γ := by
  simp only [ofDigitsFin, add_mul]
  rw [Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [ofDigitsFin]`. Rewrite using `[Fin.sum_univ_succ, Finset.sum_mul]`. Use `congr 1`. Simplify using the standard rewrite rules. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Fin.val_succ, pow_succ, mul_assoc]`.
-/
private theorem ofDigits_fin_succ (N : ℕ) {n : ℕ} (δ : Fin (n + 1) → ℕ) :
    ofDigitsFin N δ = δ 0 + (ofDigitsFin N fun i : Fin n => δ i.succ) * N := by
  simp only [ofDigitsFin]
  rw [Fin.sum_univ_succ, Finset.sum_mul]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.val_succ, pow_succ, mul_assoc]

/- English proof (translation)
Introduce `h`. Proceed by induction on `h with`. Consider the case `zero`. Introduce `β γ _ _ _`. Use function extensionality and compare the values at `i`.

Conclude with `i.elim0`. Consider the case `succ n ih`. Introduce `β γ hβ hγ hsum`. Rewrite `hsum` using `[ofDigits_fin_succ N β, ofDigits_fin_succ N γ]`. Establish `h0 : β 0 = γ 0`.

Establish `hmod : (β 0 + (ofDigitsFin N fun i : Fin n => β i.succ) * N) % N = (γ 0 + (ofDigitsFin N fun i : Fin n => γ i.succ) * N) % N` using `by rw [hsum]`. Rewrite `hmod` using `[Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (hβ 0), Nat.mod_eq_of_lt (hγ 0)]`. Then use the resulting hypothesis. Rewrite `hsum` using `[h0]`. Establish `h1 : (ofDigitsFin N fun i : Fin n => β i.succ) = ofDigitsFin N fun i : Fin n => γ i.succ` using `Nat.eq_of_mul_eq_mul_right hN (Nat.add_left_cancel hsum)`. Establish `h2` using `ih _ _ (fun i => hβ i.succ) (fun i => hγ i.succ) h1`.

Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ ?_ i` and prove the remaining obligations. Conclude with `h0`. Introduce `j`. Conclude with `congrFun h2 j`.
-/
private theorem ofDigits_injective_of_lt (N : ℕ) (hN : 0 < N) : ∀ (h : ℕ) (β γ : Fin h → ℕ),
    (∀ i, β i < N) → (∀ i, γ i < N) → ofDigitsFin N β = ofDigitsFin N γ → β = γ := by
  intro h
  induction h with
  | zero =>
    intro β γ _ _ _
    funext i
    exact i.elim0
  | succ n ih =>
    intro β γ hβ hγ hsum
    rw [ofDigits_fin_succ N β, ofDigits_fin_succ N γ] at hsum
    have h0 : β 0 = γ 0 := by
      have hmod : (β 0 + (ofDigitsFin N fun i : Fin n => β i.succ) * N) % N
          = (γ 0 + (ofDigitsFin N fun i : Fin n => γ i.succ) * N) % N := by rw [hsum]
      rwa [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt (hβ 0), Nat.mod_eq_of_lt (hγ 0)] at hmod
    rw [h0] at hsum
    have h1 : (ofDigitsFin N fun i : Fin n => β i.succ) = ofDigitsFin N fun i : Fin n => γ i.succ :=
      Nat.eq_of_mul_eq_mul_right hN (Nat.add_left_cancel hsum)
    have h2 := ih _ _ (fun i => hβ i.succ) (fun i => hγ i.succ) h1
    funext i
    refine Fin.cases ?_ ?_ i
    · exact h0
    · intro j
      exact congrFun h2 j

/- English proof (translation)
Take `⟨β₁, hβ₁, hP₁⟩` from `hex`. Take `⟨β₀, hmem, hmin⟩` from `Finset.exists_min_image ((multiIndicesOfDegree h r).filter P) (ofDigitsFin N) ⟨β₁, Finset.mem_filter.mpr ⟨(mem_multiIndicesOfDegree β₁).mpr hβ₁, hP₁⟩⟩`. Rewrite `hmem` using `[Finset.mem_filter, mem_multiIndicesOfDegree]`. Conclude with `⟨β₀, hmem.1, hmem.2, fun β hβ hPβ => hmin β (Finset.mem_filter.mpr ⟨(mem_multiIndicesOfDegree β).mpr hβ, hPβ⟩)⟩`.
-/
private theorem exists_ofDigits_le_of_sum_eq {h : ℕ} (P : (Fin h → ℕ) → Prop) (r N : ℕ)
    (hex : ∃ β : Fin h → ℕ, (∑ i, β i = r) ∧ P β) :
    ∃ β₀ : Fin h → ℕ, (∑ i, β₀ i = r) ∧ P β₀ ∧
      ∀ β : Fin h → ℕ, (∑ i, β i = r) → P β → ofDigitsFin N β₀ ≤ ofDigitsFin N β := by
  classical
  obtain ⟨β₁, hβ₁, hP₁⟩ := hex
  obtain ⟨β₀, hmem, hmin⟩ := Finset.exists_min_image
    ((multiIndicesOfDegree h r).filter P) (ofDigitsFin N)
    ⟨β₁, Finset.mem_filter.mpr ⟨(mem_multiIndicesOfDegree β₁).mpr hβ₁, hP₁⟩⟩
  rw [Finset.mem_filter, mem_multiIndicesOfDegree] at hmem
  exact ⟨β₀, hmem.1, hmem.2, fun β hβ hPβ =>
    hmin β (Finset.mem_filter.mpr ⟨(mem_multiIndicesOfDegree β).mpr hβ, hPβ⟩)⟩

/- English proof (translation)
Introduce `hsum`. Use `hFa ?_` and prove the remaining obligations. Establish `h1 : (∑ b ∈ t.erase a, F b) ∈ I` using `Ideal.sum_mem _ fun b hb => hrest b (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb)`. Establish `h2 : F a + ∑ b ∈ t.erase a, F b = ∑ b ∈ t, F b` using `Finset.add_sum_erase t F ha`. Establish `h3` using `sub_mem hsum h1`.

Rewrite `h3` using `[← h2, add_sub_cancel_right]`. Conclude with `h3`.
-/
private theorem sum_notMem_of_unique_notMem {R : Type*} [CommRing R] {I : Ideal R} {ι : Type*}
    [DecidableEq ι] (t : Finset ι) (F : ι → R) (a : ι) (ha : a ∈ t) (hFa : F a ∉ I)
    (hrest : ∀ b ∈ t, b ≠ a → F b ∈ I) : (∑ b ∈ t, F b) ∉ I := by
  intro hsum
  refine hFa ?_
  have h1 : (∑ b ∈ t.erase a, F b) ∈ I :=
    Ideal.sum_mem _ fun b hb => hrest b (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb)
  have h2 : F a + ∑ b ∈ t.erase a, F b = ∑ b ∈ t, F b := Finset.add_sum_erase t F ha
  have h3 := sub_mem hsum h1
  rw [← h2, add_sub_cancel_right] at h3
  exact h3

/- English proof (translation)
Establish `hfex : ∃ β : Fin h → ℕ, (∑ i, β i = r) ∧ multiIndexDeriv D β f ∉ IsLocalRing.maximalIdeal R`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Use `hnf ((mem_maximalIdeal_pow_succ_iff_multiIndexDeriv_mem x D hx hD hDD hunit r hf).mpr ?_)` and prove the remaining obligations. Introduce `β hβ`.

Conclude with `hcon β ((mem_multiIndicesOfDegree β).mp hβ)`. Establish `hgex : ∃ γ : Fin h → ℕ, (∑ i, γ i = s) ∧ multiIndexDeriv D γ g ∉ IsLocalRing.maximalIdeal R`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Use `hng ((mem_maximalIdeal_pow_succ_iff_multiIndexDeriv_mem x D hx hD hDD hunit s hg).mpr ?_)` and prove the remaining obligations.

Introduce `γ hγ`. Conclude with `hcon γ ((mem_multiIndicesOfDegree γ).mp hγ)`. Take `⟨β₀, hβ₀deg, hβ₀f, hβ₀min⟩` from `exists_ofDigits_le_of_sum_eq (fun β => multiIndexDeriv D β f ∉ IsLocalRing.maximalIdeal R) r (r + s + 1) hfex`. Take `⟨γ₀, hγ₀deg, hγ₀g, hγ₀min⟩` from `exists_ofDigits_le_of_sum_eq (fun γ => multiIndexDeriv D γ g ∉ IsLocalRing.maximalIdeal R) s (r + s + 1) hgex`. Take `⟨α, hα⟩ : ∃ α : Fin h → ℕ, ∀ i, α i = β₀ i + γ₀ i` from `⟨_, fun _ => rfl⟩`.

Establish `hαsum : ∑ i, α i = r + s`. Establish `hc : ∑ i, α i = ∑ i, (β₀ i + γ₀ i)` using `Finset.sum_congr rfl fun i _ => hα i`. Rewrite using `[hc, Finset.sum_add_distrib, hβ₀deg, hγ₀deg]`. Establish `hbase : ofDigitsFin (r + s + 1) α = ofDigitsFin (r + s + 1) β₀ + ofDigitsFin (r + s + 1) γ₀`. Rewrite using `[← ofDigits_add]`.

Conclude with `congrArg (ofDigitsFin (r + s + 1)) (funext hα)`. Introduce `hmem`. Establish `hfg : f * g ∈ IsLocalRing.maximalIdeal R ^ (r + s)`. Rewrite using `[pow_add]`. Conclude with `Ideal.mul_mem_mul hf hg`.

Establish `hkey` using `(mem_maximalIdeal_pow_succ_iff_multiIndexDeriv_mem x D hx hD hDD hunit (r + s) hfg).mp hmem α ((mem_multiIndicesOfDegree α).mpr hαsum)`. Establish `hsub` using `multiIndexDeriv_mul_sub_sum_mem D (IsLocalRing.maximalIdeal R) r s α hαsum hf hg`. Establish `hT` using `sub_mem hkey hsub`. Rewrite `hT` using `[sub_sub_cancel]`. Use `(sum_notMem_of_unique_notMem _ _ β₀ ?_ ?_ ?_) hT` and prove the remaining obligations.

Rewrite using `[Finset.mem_filter, Fintype.mem_piFinset]`. Use `⟨fun i => Finset.mem_range.mpr ?_, hβ₀deg⟩` and prove the remaining obligations. Use `hα i` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hγeq : (fun i => α i - β₀ i) = γ₀`.

Use function extensionality and compare the values at `i`. Use `hα i` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[hγeq]`. Establish `hcne : (∏ i, (α i).choose (β₀ i)) ≠ 0`.

Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `i _`. Use `(Nat.choose_pos ?_).ne'` and prove the remaining obligations. Use `hα i` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Conclude with `IsLocalRing.notMem_maximalIdeal.mpr (((hunit _ (Nat.one_le_iff_ne_zero.mpr hcne)).mul (IsLocalRing.notMem_maximalIdeal.mp hβ₀f)).mul (IsLocalRing.notMem_maximalIdeal.mp hγ₀g))`. Introduce `β hβt hβne`. Rewrite `hβt` using `[Finset.mem_filter, Fintype.mem_piFinset]`. Take `⟨hβrange, hβsum⟩` from `hβt`. Establish `hβle : ∀ i, β i ≤ α i` using `fun i => Nat.lt_succ_iff.mp (Finset.mem_range.mp (hβrange i))`.

Distinguish the cases in `hcase : multiIndexDeriv D β f ∈ IsLocalRing.maximalIdeal R`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hcase)`. Establish `hmin1 : ofDigitsFin (r + s + 1) β₀ ≤ ofDigitsFin (r + s + 1) β` using `hβ₀min β hβsum hcase`. Establish `hbβ : ∀ i, β i < r + s + 1`. Introduce `i`.

Establish `h1 : β i ≤ r`. Rewrite using `[← hβsum]`. Conclude with `Finset.single_le_sum (f := β) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)`. Use linear arithmetic over natural numbers and integers. Establish `hbβ₀ : ∀ i, β₀ i < r + s + 1`.

Introduce `i`. Establish `h1 : β₀ i ≤ r`. Rewrite using `[← hβ₀deg]`. Conclude with `Finset.single_le_sum (f := β₀) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)`. Use linear arithmetic over natural numbers and integers.

Establish `hne : ofDigitsFin (r + s + 1) β₀ ≠ ofDigitsFin (r + s + 1) β` using `fun heq => hβne (ofDigits_injective_of_lt (r + s + 1) (by omega) h β β₀ hbβ hbβ₀ heq.symm)`. Establish `hstrict : ofDigitsFin (r + s + 1) β₀ < ofDigitsFin (r + s + 1) β` using `lt_of_le_of_ne hmin1 hne`. Establish `hγsum : ∑ i, (α i - β i) = s`. Establish `h1 : ∑ i, ((α i - β i) + β i) = ∑ i, α i` using `Finset.sum_congr rfl fun i _ => by`. Use `hβle i` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite `h1` using `[Finset.sum_add_distrib, hβsum, hαsum]`. Use linear arithmetic over natural numbers and integers. Establish `hsplit : ofDigitsFin (r + s + 1) β + ofDigitsFin (r + s + 1) (fun i => α i - β i) = ofDigitsFin (r + s + 1) α`. Rewrite using `[← ofDigits_add]`.

Conclude with `congrArg (ofDigitsFin (r + s + 1)) (funext fun i => by show β i + (α i - β i) = α i`. Use `hβle i` as an intermediate fact. Use the proof step `omega)`. Establish `hγlt : ofDigitsFin (r + s + 1) (fun i => α i - β i) < ofDigitsFin (r + s + 1) γ₀`. Use linear arithmetic over natural numbers and integers.

Establish `hgmem : multiIndexDeriv D (fun i => α i - β i) g ∈ IsLocalRing.maximalIdeal R`. Assume the negation of the conclusion as `hcon2`. Conclude with `absurd (hγ₀min _ hγsum hcon2) (by omega)`. Conclude with `Ideal.mul_mem_left _ _ hgmem`.
-/
private theorem mul_notMem_maximalIdeal_pow_add_succ {k R : Type*} [CommRing k] [CommRing R]
    [IsLocalRing R] [Algebra k R] {h : ℕ} (x : Fin h → R) (D : Fin h → Derivation k R R)
    (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hDD : ∀ i j : Fin h, ∀ a : R, D i (D j a) = D j (D i a))
    (hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((n : ℕ) : R))
    {r s : ℕ} {f g : R} (hf : f ∈ IsLocalRing.maximalIdeal R ^ r)
    (hnf : f ∉ IsLocalRing.maximalIdeal R ^ (r + 1))
    (hg : g ∈ IsLocalRing.maximalIdeal R ^ s)
    (hng : g ∉ IsLocalRing.maximalIdeal R ^ (s + 1)) :
    f * g ∉ IsLocalRing.maximalIdeal R ^ (r + s + 1) := by
  have hfex : ∃ β : Fin h → ℕ, (∑ i, β i = r) ∧
      multiIndexDeriv D β f ∉ IsLocalRing.maximalIdeal R := by
    by_contra hcon
    push Not at hcon
    refine hnf ((mem_maximalIdeal_pow_succ_iff_multiIndexDeriv_mem x D hx hD hDD hunit r hf).mpr ?_)
    intro β hβ
    exact hcon β ((mem_multiIndicesOfDegree β).mp hβ)
  have hgex : ∃ γ : Fin h → ℕ, (∑ i, γ i = s) ∧
      multiIndexDeriv D γ g ∉ IsLocalRing.maximalIdeal R := by
    by_contra hcon
    push Not at hcon
    refine hng ((mem_maximalIdeal_pow_succ_iff_multiIndexDeriv_mem x D hx hD hDD hunit s hg).mpr ?_)
    intro γ hγ
    exact hcon γ ((mem_multiIndicesOfDegree γ).mp hγ)
  obtain ⟨β₀, hβ₀deg, hβ₀f, hβ₀min⟩ := exists_ofDigits_le_of_sum_eq
    (fun β => multiIndexDeriv D β f ∉ IsLocalRing.maximalIdeal R) r (r + s + 1) hfex
  obtain ⟨γ₀, hγ₀deg, hγ₀g, hγ₀min⟩ := exists_ofDigits_le_of_sum_eq
    (fun γ => multiIndexDeriv D γ g ∉ IsLocalRing.maximalIdeal R) s (r + s + 1) hgex
  obtain ⟨α, hα⟩ : ∃ α : Fin h → ℕ, ∀ i, α i = β₀ i + γ₀ i := ⟨_, fun _ => rfl⟩
  have hαsum : ∑ i, α i = r + s := by
    have hc : ∑ i, α i = ∑ i, (β₀ i + γ₀ i) := Finset.sum_congr rfl fun i _ => hα i
    rw [hc, Finset.sum_add_distrib, hβ₀deg, hγ₀deg]
  have hbase : ofDigitsFin (r + s + 1) α
      = ofDigitsFin (r + s + 1) β₀ + ofDigitsFin (r + s + 1) γ₀ := by
    rw [← ofDigits_add]
    exact congrArg (ofDigitsFin (r + s + 1)) (funext hα)
  intro hmem
  have hfg : f * g ∈ IsLocalRing.maximalIdeal R ^ (r + s) := by
    rw [pow_add]
    exact Ideal.mul_mem_mul hf hg
  have hkey := (mem_maximalIdeal_pow_succ_iff_multiIndexDeriv_mem x D hx hD hDD hunit (r + s) hfg).mp hmem
    α ((mem_multiIndicesOfDegree α).mpr hαsum)
  have hsub := multiIndexDeriv_mul_sub_sum_mem D (IsLocalRing.maximalIdeal R) r s α hαsum hf hg
  have hT := sub_mem hkey hsub
  rw [sub_sub_cancel] at hT
  refine (sum_notMem_of_unique_notMem _ _ β₀ ?_ ?_ ?_) hT
  · rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun i => Finset.mem_range.mpr ?_, hβ₀deg⟩
    have := hα i
    omega
  · have hγeq : (fun i => α i - β₀ i) = γ₀ := by
      funext i
      have := hα i
      omega
    rw [hγeq]
    have hcne : (∏ i, (α i).choose (β₀ i)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro i _
      refine (Nat.choose_pos ?_).ne'
      have := hα i
      omega
    exact IsLocalRing.notMem_maximalIdeal.mpr
      (((hunit _ (Nat.one_le_iff_ne_zero.mpr hcne)).mul
        (IsLocalRing.notMem_maximalIdeal.mp hβ₀f)).mul
        (IsLocalRing.notMem_maximalIdeal.mp hγ₀g))
  · intro β hβt hβne
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hβt
    obtain ⟨hβrange, hβsum⟩ := hβt
    have hβle : ∀ i, β i ≤ α i := fun i =>
      Nat.lt_succ_iff.mp (Finset.mem_range.mp (hβrange i))
    by_cases hcase : multiIndexDeriv D β f ∈ IsLocalRing.maximalIdeal R
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hcase)
    · have hmin1 : ofDigitsFin (r + s + 1) β₀ ≤ ofDigitsFin (r + s + 1) β := hβ₀min β hβsum hcase
      have hbβ : ∀ i, β i < r + s + 1 := by
        intro i
        have h1 : β i ≤ r := by
          rw [← hβsum]
          exact Finset.single_le_sum (f := β) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        omega
      have hbβ₀ : ∀ i, β₀ i < r + s + 1 := by
        intro i
        have h1 : β₀ i ≤ r := by
          rw [← hβ₀deg]
          exact Finset.single_le_sum (f := β₀) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        omega
      have hne : ofDigitsFin (r + s + 1) β₀ ≠ ofDigitsFin (r + s + 1) β := fun heq =>
        hβne (ofDigits_injective_of_lt (r + s + 1) (by omega) h β β₀ hbβ hbβ₀ heq.symm)
      have hstrict : ofDigitsFin (r + s + 1) β₀ < ofDigitsFin (r + s + 1) β :=
        lt_of_le_of_ne hmin1 hne
      have hγsum : ∑ i, (α i - β i) = s := by
        have h1 : ∑ i, ((α i - β i) + β i) = ∑ i, α i :=
          Finset.sum_congr rfl fun i _ => by
            have := hβle i
            omega
        rw [Finset.sum_add_distrib, hβsum, hαsum] at h1
        omega
      have hsplit : ofDigitsFin (r + s + 1) β + ofDigitsFin (r + s + 1) (fun i => α i - β i)
          = ofDigitsFin (r + s + 1) α := by
        rw [← ofDigits_add]
        exact congrArg (ofDigitsFin (r + s + 1)) (funext fun i => by
          show β i + (α i - β i) = α i
          have := hβle i
          omega)
      have hγlt : ofDigitsFin (r + s + 1) (fun i => α i - β i) < ofDigitsFin (r + s + 1) γ₀ := by
        omega
      have hgmem : multiIndexDeriv D (fun i => α i - β i) g ∈ IsLocalRing.maximalIdeal R := by
        by_contra hcon2
        exact absurd (hγ₀min _ hγsum hcon2) (by omega)
      exact Ideal.mul_mem_left _ _ hgmem

/- English proof (translation)
Distinguish the cases in `hI : I = ⊥`. Substitute `hI` using the available equality. Establish `hbm : (⊥ : Ideal R) * J = ⊥`. Use `le_antisymm (Ideal.mul_le.mpr ?_) bot_le` and prove the remaining obligations. Introduce `a ha b _`.

Rewrite `ha`, the goal using `[Ideal.mem_bot]`. Rewrite using `[ha, zero_mul]`. Rewrite using `[hbm, idealOrder_bot]`. Conclude with `le_antisymm le_self_add le_top`. Distinguish the cases in `hJ : J = ⊥`.

Substitute `hJ` using the available equality. Establish `hbm : I * (⊥ : Ideal R) = ⊥`. Use `le_antisymm (Ideal.mul_le.mpr ?_) bot_le` and prove the remaining obligations. Introduce `a _ b hb`. Rewrite `hb`, the goal using `[Ideal.mem_bot]`.

Rewrite using `[hb, mul_zero]`. Rewrite using `[hbm, idealOrder_bot]`. Conclude with `le_antisymm le_add_self le_top`. Take `⟨r, hr⟩` from `exists_idealOrder_eq_coe hI`. Take `⟨s, hs⟩` from `exists_idealOrder_eq_coe hJ`.

Establish `hIr : I ≤ IsLocalRing.maximalIdeal R ^ r` using `(le_idealOrder_iff I r).mp (le_of_eq hr.symm)`. Establish `hJs : J ≤ IsLocalRing.maximalIdeal R ^ s` using `(le_idealOrder_iff J s).mp (le_of_eq hs.symm)`. Establish `hIn : ¬ I ≤ IsLocalRing.maximalIdeal R ^ (r + 1)`. Introduce `hc`. Establish `hle` using `(le_idealOrder_iff I (r + 1)).mpr hc`.

Rewrite `hle` using `[hr]`. Establish `hnat : r + 1 ≤ r` using `by exact_mod_cast hle`. Use linear arithmetic over natural numbers and integers. Establish `hJn : ¬ J ≤ IsLocalRing.maximalIdeal R ^ (s + 1)`. Introduce `hc`.

Establish `hle` using `(le_idealOrder_iff J (s + 1)).mpr hc`. Rewrite `hle` using `[hs]`. Establish `hnat : s + 1 ≤ s` using `by exact_mod_cast hle`. Use linear arithmetic over natural numbers and integers. Choose the witnesses or unpack the hypotheses as in `⟨a, haI, han⟩ : ∃ a ∈ I, a ∉ IsLocalRing.maximalIdeal R ^ (r + 1) := by`.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hIn fun y hy => hc y hy`. Choose the witnesses or unpack the hypotheses as in `⟨b, hbJ, hbn⟩ : ∃ b ∈ J, b ∉ IsLocalRing.maximalIdeal R ^ (s + 1) := by`. Assume the negation of the conclusion as `hc`.

Use `push Not at hc`. Conclude with `hJn fun y hy => hc y hy`. Establish `hmul : a * b ∉ IsLocalRing.maximalIdeal R ^ (r + s + 1)` using `mul_notMem_maximalIdeal_pow_add_succ x D hx hD hDD hunit (hIr haI) han (hJs hbJ) hbn`. Establish `h1 : ¬ I * J ≤ IsLocalRing.maximalIdeal R ^ (r + s + 1)` using `fun hc => hmul (hc (Ideal.mul_mem_mul haI hbJ))`. Establish `h2 : I * J ≤ IsLocalRing.maximalIdeal R ^ (r + s)`.

Rewrite using `[pow_add]`. Conclude with `Ideal.mul_mono hIr hJs`. Rewrite using `[idealOrder_eq_of_le_of_not_le h2 h1, hr, hs]`. Conclude with `Nat.cast_add r s`.
-/
theorem idealOrder_mul {k R : Type*} [CommRing k] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Algebra k R] {h : ℕ} (x : Fin h → R) (D : Fin h → Derivation k R R)
    (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hDD : ∀ i j : Fin h, ∀ a : R, D i (D j a) = D j (D i a))
    (hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((n : ℕ) : R)) (I J : Ideal R) :
    idealOrder (I * J) = idealOrder I + idealOrder J := by
  by_cases hI : I = ⊥
  · subst hI
    have hbm : (⊥ : Ideal R) * J = ⊥ := by
      refine le_antisymm (Ideal.mul_le.mpr ?_) bot_le
      intro a ha b _
      rw [Ideal.mem_bot] at ha ⊢
      rw [ha, zero_mul]
    rw [hbm, idealOrder_bot]
    exact le_antisymm le_self_add le_top
  · by_cases hJ : J = ⊥
    · subst hJ
      have hbm : I * (⊥ : Ideal R) = ⊥ := by
        refine le_antisymm (Ideal.mul_le.mpr ?_) bot_le
        intro a _ b hb
        rw [Ideal.mem_bot] at hb ⊢
        rw [hb, mul_zero]
      rw [hbm, idealOrder_bot]
      exact le_antisymm le_add_self le_top
    · obtain ⟨r, hr⟩ := exists_idealOrder_eq_coe hI
      obtain ⟨s, hs⟩ := exists_idealOrder_eq_coe hJ
      have hIr : I ≤ IsLocalRing.maximalIdeal R ^ r :=
        (le_idealOrder_iff I r).mp (le_of_eq hr.symm)
      have hJs : J ≤ IsLocalRing.maximalIdeal R ^ s :=
        (le_idealOrder_iff J s).mp (le_of_eq hs.symm)
      have hIn : ¬ I ≤ IsLocalRing.maximalIdeal R ^ (r + 1) := by
        intro hc
        have hle := (le_idealOrder_iff I (r + 1)).mpr hc
        rw [hr] at hle
        have hnat : r + 1 ≤ r := by exact_mod_cast hle
        omega
      have hJn : ¬ J ≤ IsLocalRing.maximalIdeal R ^ (s + 1) := by
        intro hc
        have hle := (le_idealOrder_iff J (s + 1)).mpr hc
        rw [hs] at hle
        have hnat : s + 1 ≤ s := by exact_mod_cast hle
        omega
      obtain ⟨a, haI, han⟩ : ∃ a ∈ I, a ∉ IsLocalRing.maximalIdeal R ^ (r + 1) := by
        by_contra hc
        push Not at hc
        exact hIn fun y hy => hc y hy
      obtain ⟨b, hbJ, hbn⟩ : ∃ b ∈ J, b ∉ IsLocalRing.maximalIdeal R ^ (s + 1) := by
        by_contra hc
        push Not at hc
        exact hJn fun y hy => hc y hy
      have hmul : a * b ∉ IsLocalRing.maximalIdeal R ^ (r + s + 1) :=
        mul_notMem_maximalIdeal_pow_add_succ x D hx hD hDD hunit (hIr haI) han (hJs hbJ) hbn
      have h1 : ¬ I * J ≤ IsLocalRing.maximalIdeal R ^ (r + s + 1) := fun hc =>
        hmul (hc (Ideal.mul_mem_mul haI hbJ))
      have h2 : I * J ≤ IsLocalRing.maximalIdeal R ^ (r + s) := by
        rw [pow_add]
        exact Ideal.mul_mono hIr hJs
      rw [idealOrder_eq_of_le_of_not_le h2 h1, hr, hs]
      exact Nat.cast_add r s

/- English proof (translation)
Proceed by induction on `c with`. Consider the case `zero`. Rewrite using `[pow_zero, Ideal.one_eq_top, idealOrder_top]`. Simplify using the standard rewrite rules. Consider the case `succ c ih`.

Rewrite using `[pow_succ, idealOrder_mul x D hx hD hDD hunit, ih, Nat.cast_add, Nat.cast_one, add_mul, one_mul]`.
-/
theorem idealOrder_pow {k R : Type*} [CommRing k] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Algebra k R] {h : ℕ} (x : Fin h → R) (D : Fin h → Derivation k R R)
    (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hDD : ∀ i j : Fin h, ∀ a : R, D i (D j a) = D j (D i a))
    (hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((n : ℕ) : R)) (I : Ideal R) (c : ℕ) :
    idealOrder (I ^ c) = (c : ℕ∞) * idealOrder I := by
  induction c with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top, idealOrder_top]
    simp
  | succ c ih =>
    rw [pow_succ, idealOrder_mul x D hx hD hDD hunit, ih, Nat.cast_add, Nat.cast_one, add_mul,
      one_mul]

end FunctorialResolution.EmbeddedResolution
