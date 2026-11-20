import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

open GlobalTheory.InertZeta

noncomputable section

namespace GlobalTheory.InertZeta

/- English proof (translation)
Use `set y := (q : 𝕜) ^ (N + 1) * x with hy`. Establish `hy2 : ‖y ^ 2‖ < 1`. Rewrite using `[norm_pow]`. Use polynomial arithmetic with `[norm_nonneg y]`. Establish `hg` using `hasSum_geometric_of_norm_lt_one hy2`.

Establish `fe : (fun k : ℕ => ((c * q ^ (2 * N * ((2 * k) / 2) + 2 * k) : ℕ) : 𝕜) * x ^ (2 * k)) = fun k => (c : 𝕜) * (y ^ 2) ^ k`. Use function extensionality and compare the values at `k`. Rewrite using `[Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]`. Use `push_cast`. Rewrite using `[hy]`.

Expand and normalize the polynomial expressions, which then agree. Establish `fo : (fun k : ℕ => ((c * q ^ (2 * N * ((2 * k + 1) / 2) + (2 * k + 1)) : ℕ) : 𝕜) * x ^ (2 * k + 1)) = fun k => ((c : 𝕜) * q * x) * (y ^ 2) ^ k`. Use function extensionality and compare the values at `k`. Rewrite using `[show (2 * k + 1) / 2 = k by omega]`. Use `push_cast`.

Rewrite using `[hy]`. Expand and normalize the polynomial expressions, which then agree. Establish `he` using `hg.mul_left (c : 𝕜)`. Establish `ho` using `hg.mul_left ((c : 𝕜) * q * x)`. Rewrite `he` using `[← fe]`.

Rewrite `ho` using `[← fo]`. Use `HasSum.even_add_odd (f := fun j : ℕ => ((c * q ^ (2 * N * (j / 2) + j) : ℕ) : 𝕜) * x ^ j) he ho` as an intermediate fact. Rewrite using `[show (c : 𝕜) * (1 + q * x) / (1 - y ^ 2) = c * (1 - y ^ 2)⁻¹ + c * q * x * (1 - y ^ 2)⁻¹ by`. Rewrite using `[div_eq_mul_inv]`. Use the proof step `ring]`.

Conclude with `this`.
-/
theorem genFun_counts_hasSum {𝕜 : Type} [NormedField 𝕜] [CompleteSpace 𝕜] (c q N : ℕ) (x : 𝕜)
    (hx : ‖(q : 𝕜) ^ (N + 1) * x‖ < 1) :
    HasSum (fun j : ℕ => ((c * q ^ (2 * N * (j / 2) + j) : ℕ) : 𝕜) * x ^ j)
      (c * (1 + q * x) / (1 - ((q : 𝕜) ^ (N + 1) * x) ^ 2)) := by
  set y := (q : 𝕜) ^ (N + 1) * x with hy
  have hy2 : ‖y ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg y]
  have hg := hasSum_geometric_of_norm_lt_one hy2
  have fe : (fun k : ℕ => ((c * q ^ (2 * N * ((2 * k) / 2) + 2 * k) : ℕ) : 𝕜) * x ^ (2 * k)) =
      fun k => (c : 𝕜) * (y ^ 2) ^ k := by
    funext k
    rw [Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]
    push_cast
    rw [hy]; ring
  have fo : (fun k : ℕ => ((c * q ^ (2 * N * ((2 * k + 1) / 2) + (2 * k + 1)) : ℕ) : 𝕜) * x ^ (2 * k + 1)) =
      fun k => ((c : 𝕜) * q * x) * (y ^ 2) ^ k := by
    funext k
    rw [show (2 * k + 1) / 2 = k by omega]
    push_cast
    rw [hy]; ring
  have he := hg.mul_left (c : 𝕜)
  have ho := hg.mul_left ((c : 𝕜) * q * x)
  rw [← fe] at he
  rw [← fo] at ho
  have := HasSum.even_add_odd (f := fun j : ℕ => ((c * q ^ (2 * N * (j / 2) + j) : ℕ) : 𝕜) * x ^ j) he ho
  rw [show (c : 𝕜) * (1 + q * x) / (1 - y ^ 2) = c * (1 - y ^ 2)⁻¹ + c * q * x * (1 - y ^ 2)⁻¹ by
    rw [div_eq_mul_inv]; ring]
  exact this

/- English proof (translation)
Set `h : ℕ → 𝕜` to `fun j => if j = 0 then 0 else (C (j - 1) : 𝕜) * x ^ j`. Establish `hsh : (fun n => h (n + 1)) = fun n => x * ((C n : 𝕜) * x ^ n)`. Use function extensionality and compare the values at `n`. Simplify using `only [h, Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero n)]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h1 : HasSum (fun n => h (n + 1)) (x * S)` using `by rw [hsh]; exact hA.mul_left x`. Establish `hh : HasSum h (x * S)`. Use `(hasSum_nat_add_iff (f := h) 1).1 h1` as an intermediate fact. Simplify `this` using `[h]`. Establish `hd : (fun j => (d j : 𝕜) * x ^ j) = fun j => (C j : 𝕜) * x ^ j - h j`.

Use function extensionality and compare the values at `j`. Break down `j with _ | j` into its components or cases. Simplify using `[h, h0]`. Simplify using `only [h, if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel, hs j] push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hd, show (1 - x) * S = S - x * S by ring]`. Conclude with `hA.sub hh`.
-/
theorem genFun_diff_hasSum {𝕜 : Type} [NormedField 𝕜] (C d : ℕ → ℕ) (x S : 𝕜)
    (h0 : d 0 = C 0) (hs : ∀ j, C (j + 1) = C j + d (j + 1))
    (hA : HasSum (fun j => (C j : 𝕜) * x ^ j) S) :
    HasSum (fun j => (d j : 𝕜) * x ^ j) ((1 - x) * S) := by
  let h : ℕ → 𝕜 := fun j => if j = 0 then 0 else (C (j - 1) : 𝕜) * x ^ j
  have hsh : (fun n => h (n + 1)) = fun n => x * ((C n : 𝕜) * x ^ n) := by
    funext n
    simp only [h, Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero n)]
    ring
  have h1 : HasSum (fun n => h (n + 1)) (x * S) := by rw [hsh]; exact hA.mul_left x
  have hh : HasSum h (x * S) := by
    have := (hasSum_nat_add_iff (f := h) 1).1 h1
    simpa [h] using this
  have hd : (fun j => (d j : 𝕜) * x ^ j) = fun j => (C j : 𝕜) * x ^ j - h j := by
    funext j
    rcases j with _ | j
    · simp [h, h0]
    · simp only [h, if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel, hs j]
      push_cast; ring
  rw [hd, show (1 - x) * S = S - x * S by ring]
  exact hA.sub hh

/- English proof (translation)
Use `haveI : Finite {i // f i - l = j} := hfin.to_subtype`. Use `haveI : Fintype {i // f i - l = j} := Fintype.ofFinite _`. Establish `hc : ∀ y : {i // f i - l = j}, x ^ f y.1 = x ^ (l + j)` using `fun y => by`. Use `hl y.1` as an intermediate fact. Use `y.2` as an intermediate fact.

Rewrite using `[show f y.1 = l + j by omega]`. Establish `e : Nat.card {i // f i - l = j} = Set.ncard {i | f i - l = j}` using `Nat.card_coe_set_eq _`. Establish `h` using `hasSum_fintype (fun y : {i // f i - l = j} => x ^ f y.1)`. Rewrite `h` using `[Finset.sum_congr rfl (fun y _ => hc y), Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, e]`. Conclude with `h`.
-/
theorem genFun_fibre_hasSum {ι 𝕜 : Type} [NormedField 𝕜] (f : ι → ℕ) (l j : ℕ) (x : 𝕜)
    (hfin : Set.Finite {i | f i - l = j}) (hl : ∀ i, l ≤ f i) :
    HasSum (fun y : {i // f i - l = j} => x ^ f y.1) ((Set.ncard {i | f i - l = j} : 𝕜) * x ^ (l + j)) := by
  haveI : Finite {i // f i - l = j} := hfin.to_subtype
  haveI : Fintype {i // f i - l = j} := Fintype.ofFinite _
  have hc : ∀ y : {i // f i - l = j}, x ^ f y.1 = x ^ (l + j) := fun y => by
    have := hl y.1; have := y.2
    rw [show f y.1 = l + j by omega]
  have e : Nat.card {i // f i - l = j} = Set.ncard {i | f i - l = j} := Nat.card_coe_set_eq _
  have h := hasSum_fintype (fun y : {i // f i - l = j} => x ^ f y.1)
  rw [Finset.sum_congr rfl (fun y _ => hc y), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, e] at h
  exact h

/- English proof (translation)
Introduce `ι f l c q N X hc hq hl hcard hX`. Set `C : ℕ → ℕ` to `fun j => c * q ^ (2 * N * (j / 2) + j)`. Set `g : ι → ℕ` to `fun i => f i - l`. Establish `hCpos : ∀ j, C j ≠ 0` using `fun j => Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega))`. Establish `hle : ∀ j, {i | g i ≤ j} = {i | f i ≤ l + j}` using `fun j => by`.

Use extensionality with `i`. Simplify using `only [Set.mem_setOf_eq, g]`. Use `hl i` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hcum : ∀ j, Set.ncard {i | g i ≤ j} = C j` using `fun j => by`.

Rewrite using `[hle, ← Nat.card_coe_set_eq]`. Conclude with `hcard j`. Establish `hfin : ∀ j, Set.Finite {i | g i ≤ j}` using `fun j => by`. Apply `Set.finite_of_ncard_ne_zero` to reduce the goal to its premises. Rewrite using `[hcum]`.

Conclude with `hCpos j`. Establish `hfin' : ∀ j, Set.Finite {i | f i - l = j}` using `fun j => (hfin j).subset fun i hi => by simp only [Set.mem_setOf_eq, g] at hi ⊢; omega`. Set `d : ℕ → ℕ` to `fun j => Set.ncard {i | f i - l = j}`. Establish `h0 : d 0 = C 0`. Rewrite using `[← hcum 0]`.

Use `show Set.ncard {i | f i - l = 0} = _`. Use `congr 1`. Use extensionality with `i`. Simplify using `only [Set.mem_setOf_eq, g]`. Use linear arithmetic over natural numbers and integers.

Establish `hs : ∀ j, C (j + 1) = C j + d (j + 1)` using `fun j => by`. Establish `hdis : Disjoint {i | g i ≤ j} {i | f i - l = j + 1}` using `Set.disjoint_left.2 fun i h1 h2 => by simp only [Set.mem_setOf_eq, g] at h1 h2; omega`. Establish `hun : {i | g i ≤ j + 1} = {i | g i ≤ j} ∪ {i | f i - l = j + 1}`. Use extensionality with `i`. Simplify using `only [Set.mem_setOf_eq, Set.mem_union, g]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[← hcum, ← hcum, hun, Set.ncard_union_eq hdis (hfin j) (hfin' (j + 1))]`. Set `e` to `Equiv.sigmaFiberEquiv g`. Establish `hr : ‖(q : ℝ) ^ (N + 1) * ‖X‖‖ < 1`. Rewrite using `[norm_mul, norm_pow, Real.norm_natCast, norm_norm]`.

Rewrite `hX` using `[norm_mul, norm_pow, Complex.norm_natCast]`. Then use the resulting hypothesis. Establish `hRB` using `(genFun_diff_hasSum C d ‖X‖ _ h0 hs (genFun_counts_hasSum c q N ‖X‖ hr)).mul_left (‖X‖ ^ l)`. Establish `hsumR : Summable (fun i => ‖X‖ ^ f i)`. Rewrite using `[← e.summable_iff]`. Use `(summable_sigma_of_nonneg (f := (fun i => ‖X‖ ^ f i) ∘ e) (fun _ => pow_nonneg (norm_nonneg _) _)).2 ⟨fun j => (genFun_fibre_hasSum f l j ‖X‖ (hfin' j) hl).summable, ?_⟩` and prove the remaining obligations.

Use `hRB.summable.congr fun j => ?_` and prove the remaining obligations. Establish `ht : ∑' (y : {x // g x = j}), ((fun i => ‖X‖ ^ f i) ∘ e) ⟨j, y⟩ = (d j : ℝ) * ‖X‖ ^ (l + j)` using `(genFun_fibre_hasSum f l j ‖X‖ (hfin' j) hl).tsum_eq`. Rewrite using `[ht, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsumC : Summable (fun i => X ^ f i)` using `Summable.of_norm (by simpa [norm_pow] using hsumR)`.

Establish `hB` using `(genFun_diff_hasSum C d X _ h0 hs (genFun_counts_hasSum c q N X hX)).mul_left (X ^ l)`. Establish `hBC : HasSum (fun j => (d j : ℂ) * X ^ (l + j)) (c * X ^ l * jFac q N X)`. Establish `e1 : (fun j => (d j : ℂ) * X ^ (l + j)) = fun j => X ^ l * ((d j : ℂ) * X ^ j)`. Use function extensionality and compare the values at `j`. Rewrite using `[pow_add]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, show (c : ℂ) * X ^ l * jFac q N X = X ^ l * ((1 - X) * (c * (1 + q * X) / (1 - ((q : ℂ) ^ (N + 1) * X) ^ 2))) by unfold jFac; ring]`. Conclude with `hB`. Establish `hsig` using `HasSum.sigma_of_hasSum (f := (fun i => X ^ f i) ∘ e) hBC (fun j => genFun_fibre_hasSum f l j X (hfin' j) hl) (e.summable_iff.2 hsumC)`. Conclude with `e.hasSum_iff.1 hsig`.
-/
theorem genFun_holds : GenFun := by
  intro ι f l c q N X hc hq hl hcard hX
  let C : ℕ → ℕ := fun j => c * q ^ (2 * N * (j / 2) + j)
  let g : ι → ℕ := fun i => f i - l
  have hCpos : ∀ j, C j ≠ 0 := fun j =>
    Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega))
  have hle : ∀ j, {i | g i ≤ j} = {i | f i ≤ l + j} := fun j => by
    ext i; simp only [Set.mem_setOf_eq, g]; have := hl i; omega
  have hcum : ∀ j, Set.ncard {i | g i ≤ j} = C j := fun j => by
    rw [hle, ← Nat.card_coe_set_eq]; exact hcard j
  have hfin : ∀ j, Set.Finite {i | g i ≤ j} := fun j => by
    apply Set.finite_of_ncard_ne_zero; rw [hcum]; exact hCpos j
  have hfin' : ∀ j, Set.Finite {i | f i - l = j} := fun j =>
    (hfin j).subset fun i hi => by simp only [Set.mem_setOf_eq, g] at hi ⊢; omega
  let d : ℕ → ℕ := fun j => Set.ncard {i | f i - l = j}
  have h0 : d 0 = C 0 := by
    rw [← hcum 0]
    show Set.ncard {i | f i - l = 0} = _
    congr 1; ext i; simp only [Set.mem_setOf_eq, g]; omega
  have hs : ∀ j, C (j + 1) = C j + d (j + 1) := fun j => by
    have hdis : Disjoint {i | g i ≤ j} {i | f i - l = j + 1} :=
      Set.disjoint_left.2 fun i h1 h2 => by simp only [Set.mem_setOf_eq, g] at h1 h2; omega
    have hun : {i | g i ≤ j + 1} = {i | g i ≤ j} ∪ {i | f i - l = j + 1} := by
      ext i; simp only [Set.mem_setOf_eq, Set.mem_union, g]; omega
    rw [← hcum, ← hcum, hun, Set.ncard_union_eq hdis (hfin j) (hfin' (j + 1))]
  let e := Equiv.sigmaFiberEquiv g
  have hr : ‖(q : ℝ) ^ (N + 1) * ‖X‖‖ < 1 := by
    rw [norm_mul, norm_pow, Real.norm_natCast, norm_norm]
    rwa [norm_mul, norm_pow, Complex.norm_natCast] at hX
  have hRB := (genFun_diff_hasSum C d ‖X‖ _ h0 hs (genFun_counts_hasSum c q N ‖X‖ hr)).mul_left (‖X‖ ^ l)
  have hsumR : Summable (fun i => ‖X‖ ^ f i) := by
    rw [← e.summable_iff]
    refine (summable_sigma_of_nonneg (f := (fun i => ‖X‖ ^ f i) ∘ e) (fun _ => pow_nonneg (norm_nonneg _) _)).2 ⟨fun j => (genFun_fibre_hasSum f l j ‖X‖ (hfin' j) hl).summable, ?_⟩
    refine hRB.summable.congr fun j => ?_
    have ht : ∑' (y : {x // g x = j}), ((fun i => ‖X‖ ^ f i) ∘ e) ⟨j, y⟩ = (d j : ℝ) * ‖X‖ ^ (l + j) :=
      (genFun_fibre_hasSum f l j ‖X‖ (hfin' j) hl).tsum_eq
    rw [ht, pow_add]
    ring
  have hsumC : Summable (fun i => X ^ f i) := Summable.of_norm (by simpa [norm_pow] using hsumR)
  have hB := (genFun_diff_hasSum C d X _ h0 hs (genFun_counts_hasSum c q N X hX)).mul_left (X ^ l)
  have hBC : HasSum (fun j => (d j : ℂ) * X ^ (l + j)) (c * X ^ l * jFac q N X) := by
    have e1 : (fun j => (d j : ℂ) * X ^ (l + j)) = fun j => X ^ l * ((d j : ℂ) * X ^ j) := by
      funext j; rw [pow_add]; ring
    rw [e1, show (c : ℂ) * X ^ l * jFac q N X =
      X ^ l * ((1 - X) * (c * (1 + q * X) / (1 - ((q : ℂ) ^ (N + 1) * X) ^ 2))) by unfold jFac; ring]
    exact hB
  have hsig := HasSum.sigma_of_hasSum (f := (fun i => X ^ f i) ∘ e) hBC
    (fun j => genFun_fibre_hasSum f l j X (hfin' j) hl) (e.summable_iff.2 hsumC)
  exact e.hasSum_iff.1 hsig

end GlobalTheory.InertZeta
