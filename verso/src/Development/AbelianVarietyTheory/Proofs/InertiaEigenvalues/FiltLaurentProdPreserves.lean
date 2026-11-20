import Mathlib

open PowerSeries

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `xs with`. Consider the case `nil => simpa using hf`. Consider the case `cons x xs ih`. Rewrite using `[List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply]`. Use `set g := Polynomial.aeval D (xs.map fun x => (Polynomial.X - Polynomial.C (c x) : Polynomial L)).prod f`.

Establish `h1 : X ^ i ∣ D g - e i • g` using `(pow_dvd_pow X (Nat.le_succ i)).trans (hD i g ih)`. Establish `h2 : Polynomial.aeval D (Polynomial.X - Polynomial.C (c x) : Polynomial L) g = (D g - e i • g) + (e i - c x) • g`. Simplify using `[sub_smul, Module.algebraMap_end_apply]`. Rewrite using `[h2]`. Conclude with `dvd_add h1 (Dvd.dvd.trans ih ⟨PowerSeries.C (e i - c x), by`.

Rewrite using `[PowerSeries.smul_eq_C_mul, mul_comm]⟩)`.
-/
theorem filtLaurent_prod_preserves {L : Type} [Field L] (D : Module.End L L⟦X⟧) (e : ℕ → L)
    (hD : ∀ (i : ℕ) (f : L⟦X⟧), X ^ i ∣ f → X ^ (i + 1) ∣ D f - e i • f)
    (c : ℤ → L) (xs : List ℤ) (i : ℕ) (f : L⟦X⟧) (hf : X ^ i ∣ f) :
    X ^ i ∣ Polynomial.aeval D
      (xs.map fun x => (Polynomial.X - Polynomial.C (c x) : Polynomial L)).prod f := by
  induction xs with
  | nil => simpa using hf
  | cons x xs ih =>
    rw [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply]
    set g := Polynomial.aeval D
      (xs.map fun x => (Polynomial.X - Polynomial.C (c x) : Polynomial L)).prod f
    have h1 : X ^ i ∣ D g - e i • g := (pow_dvd_pow X (Nat.le_succ i)).trans (hD i g ih)
    have h2 : Polynomial.aeval D (Polynomial.X - Polynomial.C (c x) : Polynomial L) g
        = (D g - e i • g) + (e i - c x) • g := by
      simp [sub_smul, Module.algebraMap_end_apply]
    rw [h2]
    exact dvd_add h1 (Dvd.dvd.trans ih ⟨PowerSeries.C (e i - c x), by
      rw [PowerSeries.smul_eq_C_mul, mul_comm]⟩)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact fun xs i f hf _ => filtLaurent_prod_preserves D _ hD c xs i f hf`. Consider the case `succ n ih`. Introduce `xs i f hf hxs`. Establish `hx : -(K + i) ∈ xs` using `hxs i le_rfl (by omega)`.

Establish `hperm` using `((List.perm_cons_erase hx).map fun x => (Polynomial.X - Polynomial.C (c x) : Polynomial L)).prod_eq`. Rewrite using `[hperm, List.map_cons, List.prod_cons, mul_comm, map_mul, Module.End.mul_apply]`. Establish `h2 : Polynomial.aeval D (Polynomial.X - Polynomial.C (c (-(K + i))) : Polynomial L) f = D f - c (-(K + i)) • f`. Simplify using `[Module.algebraMap_end_apply]`. Rewrite using `[h2, show i + (n + 1) = (i + 1) + n by omega]`.

Use `ih _ (i + 1) _ (hD i f hf) fun l hl hl' => ?_` and prove the remaining obligations. Conclude with `(List.mem_erase_of_ne (by omega)).2 (hxs l (by omega) (by omega))`.
-/
theorem filtLaurent_prod_raises {L : Type} [Field L] (D : Module.End L L⟦X⟧) (c : ℤ → L) (K : ℤ)
    (hD : ∀ (i : ℕ) (f : L⟦X⟧), X ^ i ∣ f → X ^ (i + 1) ∣ D f - c (-(K + i)) • f)
    (n : ℕ) : ∀ (xs : List ℤ) (i : ℕ) (f : L⟦X⟧), X ^ i ∣ f →
      (∀ l : ℕ, i ≤ l → l < i + n → -(K + l) ∈ xs) →
      X ^ (i + n) ∣ Polynomial.aeval D
        (xs.map fun x => (Polynomial.X - Polynomial.C (c x) : Polynomial L)).prod f := by
  induction n with
  | zero => exact fun xs i f hf _ => filtLaurent_prod_preserves D _ hD c xs i f hf
  | succ n ih =>
    intro xs i f hf hxs
    have hx : -(K + i) ∈ xs := hxs i le_rfl (by omega)
    have hperm := ((List.perm_cons_erase hx).map
      fun x => (Polynomial.X - Polynomial.C (c x) : Polynomial L)).prod_eq
    rw [hperm, List.map_cons, List.prod_cons, mul_comm, map_mul, Module.End.mul_apply]
    have h2 : Polynomial.aeval D (Polynomial.X - Polynomial.C (c (-(K + i))) : Polynomial L) f
        = D f - c (-(K + i)) • f := by
      simp [Module.algebraMap_end_apply]
    rw [h2, show i + (n + 1) = (i + 1) + n by omega]
    refine ih _ (i + 1) _ (hD i f hf) fun l hl hl' => ?_
    exact (List.mem_erase_of_ne (by omega)).2 (hxs l (by omega) (by omega))

noncomputable def filtLaurentDiag {L : Type} [Field L] (w : ℕ → L) : Module.End L L⟦X⟧ where
  toFun f := PowerSeries.mk fun i => w i * coeff i f
  map_add' f g := by ext i; simp [mul_add]
  map_smul' a f := by ext i; simp [mul_left_comm]

/- English proof (translation)
Establish `h1 : (LinearMap.mulLeft L p⁻¹ ∘ₗ filtLaurentDiag w) f - a • f = p⁻¹ * (filtLaurentDiag w f - a • (p * f))`. Rewrite using `[mul_sub, mul_smul_comm, ← mul_assoc, PowerSeries.inv_mul_cancel _ hp, one_mul]`. Both sides reduce to the same expression. Rewrite using `[h1]`. Use `Dvd.dvd.mul_left ?_ _` and prove the remaining obligations.

Rewrite using `[X_pow_dvd_iff]`. Introduce `l hl`. Establish `hpf : X ^ i ∣ p * f` using `hf.mul_left p`. Break down `Nat.lt_succ_iff_lt_or_eq.1 hl with h | rfl` into its components or cases. Simplify using `[filtLaurentDiag, X_pow_dvd_iff.1 hf l h, X_pow_dvd_iff.1 hpf l h]`.

Take `⟨g, rfl⟩` from `hf`. Establish `e1 : coeff l (X ^ l * g) = constantCoeff g`. Simplify using `using coeff_X_pow_mul g l 0`. Establish `e2 : coeff l (p * (X ^ l * g)) = constantCoeff p * constantCoeff g`. Rewrite using `[mul_left_comm]`.

Simplify using `using coeff_X_pow_mul (p * g) l 0`. Simplify using `only [map_sub, filtLaurentDiag, LinearMap.coe_mk, AddHom.coe_mk, coeff_mk, map_smul, e1, e2, smul_eq_mul, ← ha]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem filtLaurent_triangular {L : Type} [Field L] (w : ℕ → L) (p : L⟦X⟧)
    (hp : constantCoeff p ≠ 0) (i : ℕ) (a : L) (ha : constantCoeff p * a = w i)
    (f : L⟦X⟧) (hf : X ^ i ∣ f) :
    X ^ (i + 1) ∣ (LinearMap.mulLeft L p⁻¹ ∘ₗ filtLaurentDiag w) f - a • f := by
  have h1 : (LinearMap.mulLeft L p⁻¹ ∘ₗ filtLaurentDiag w) f - a • f
      = p⁻¹ * (filtLaurentDiag w f - a • (p * f)) := by
    rw [mul_sub, mul_smul_comm, ← mul_assoc, PowerSeries.inv_mul_cancel _ hp, one_mul]
    rfl
  rw [h1]
  refine Dvd.dvd.mul_left ?_ _
  rw [X_pow_dvd_iff]
  intro l hl
  have hpf : X ^ i ∣ p * f := hf.mul_left p
  rcases Nat.lt_succ_iff_lt_or_eq.1 hl with h | rfl
  · simp [filtLaurentDiag, X_pow_dvd_iff.1 hf l h, X_pow_dvd_iff.1 hpf l h]
  · obtain ⟨g, rfl⟩ := hf
    have e1 : coeff l (X ^ l * g) = constantCoeff g := by
      simpa using coeff_X_pow_mul g l 0
    have e2 : coeff l (p * (X ^ l * g)) = constantCoeff p * constantCoeff g := by
      rw [mul_left_comm]
      simpa using coeff_X_pow_mul (p * g) l 0
    simp only [map_sub, filtLaurentDiag, LinearMap.coe_mk, AddHom.coe_mk, coeff_mk, map_smul,
      e1, e2, smul_eq_mul, ← ha]
    ring

/- English proof (translation)
Introduce `L _ M _ _ Fl hFl u p c hp hc y' Y xs hxs seq hbd hrec h0 k`. Rewrite using `[← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]`. Introduce `φ hφ`. Rewrite `hφ` using `[Submodule.mem_dualAnnihilator]`. Use `choose k₀ hk₀ using hbd`.

Establish `core : ∀ (K : ℤ), (∀ m ≤ xs.length, K ≤ k₀ m) → ∀ i n : ℕ, (∀ l < i, φ (seq 0 (K + l)) = 0) → (∀ l : ℕ, i ≤ l → l < i + n → -(K + l) ∈ xs) → ∀ l < i + n, φ (seq xs.length (K + l)) = 0`. Introduce `K hK i n hi hn`. Use `set w : ℕ → L := fun l => ((u ^ (K + l) : Lˣ) : L) - 1 with hw`. Use `set D : Module.End L L⟦X⟧ := LinearMap.mulLeft L p⁻¹ ∘ₗ filtLaurentDiag w with hDdef`. Use `set G : ℕ → L⟦X⟧ := fun m => PowerSeries.mk fun l => φ (seq m (K + l)) with hG`.

Establish `hstep : ∀ m < xs.length, G (m + 1) = D (G m) - c (xs.getD m 0) • G m`. Introduce `m hm`. Establish `key : p * (G (m + 1) + c (xs.getD m 0) • G m) = filtLaurentDiag w (G m)`. Use extensionality with `l`. Establish `h1` using `hrec m hm (K + l)`.

Rewrite `h1` using `[finsum_eq_sum_of_support_subset (s := Finset.range (l + 1))]`. Establish `h2` using `congrArg φ h1`. Rewrite using `[coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => coeff a p * coeff b (G (m + 1) + c (xs.getD m 0) • G m))]`. Rewrite `h2` using `[map_sum, map_smul]`. Simplify using `only [filtLaurentDiag, LinearMap.coe_mk, AddHom.coe_mk, coeff_mk, hG, hw]`.

Rewrite using `[← smul_eq_mul, ← h2]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Establish `hj' : j ≤ l` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)`. Establish `: K + ((l - j : ℕ) : ℤ) = K + l - j` using `by omega`. Simplify using `only [map_add, map_smul, coeff_mk, this, smul_eq_mul]`.

Introduce `j hj`. Assume the negation of the conclusion as `hj'`. Establish `hj'' : l + 1 ≤ j` using `by simpa using hj'`. Establish `a1` using `hK m hm.le`. Establish `a2` using `hK (m + 1) hm`.

Apply `hj` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[hk₀ (m + 1) _ (by omega), hk₀ m _ (by omega)]`. Simplify using the standard rewrite rules. Rewrite using `[eq_sub_iff_add_eq, hDdef, LinearMap.comp_apply, ← key, LinearMap.mulLeft_apply, ← mul_assoc, PowerSeries.inv_mul_cancel _ hp, one_mul]`.

Establish `hall : ∀ m ≤ xs.length, G m = Polynomial.aeval D ((xs.take m).map fun x => (Polynomial.X - Polynomial.C (c x) : Polynomial L)).prod (G 0)`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`.

Introduce `hm`. Establish `hm' : m < xs.length` using `hm`. Rewrite using `[hstep m hm', List.take_succ_eq_append_getElem hm', List.map_append, List.prod_append, mul_comm, map_mul, Module.End.mul_apply, ← ih hm'.le, List.getD_eq_getElem _ _ hm']`. Simplify using `[Module.algebraMap_end_apply]`. Establish `hfin` using `filtLaurent_prod_raises D c K (fun l f hf => filtLaurent_triangular w p hp l _ (by rw [hc, neg_neg]) f hf) n xs i (G 0) (X_pow_dvd_iff.2 fun l hl => by simpa [hG] using hi l hl) hn`.

Establish `h3` using `hall xs.length le_rfl`. Rewrite `h3` using `[List.take_length]`. Rewrite `hfin` using `[← h3]`. Introduce `l hl`. Simplify `X_pow_dvd_iff.1 hfin l hl` using `[hG]`.

Take `⟨K₀, hK₀⟩` from `((Set.finite_le_nat xs.length).image k₀).bddBelow`. Establish `hK₁ : ∀ m ≤ xs.length, K₀ ≤ k₀ m` using `fun m hm => hK₀ ⟨m, hm, rfl⟩`. Distinguish the cases in `hex : ∃ a : ℤ, ¬ ∀ v ∈ Fl a, φ v = 0`. Establish `hbdd : ∀ a : ℤ, (¬ ∀ v ∈ Fl a, φ v = 0) → a < -k - y'`. Introduce `a ha`.

Assume the negation of the conclusion as `h`. Conclude with `ha fun v hv => hφ v (hFl (not_lt.1 h) hv)`. Take `⟨a, ha, hmax⟩` from `Int.exists_greatest_of_bdd ⟨-k - y', fun a ha => (hbdd a ha).le⟩ hex`. Establish `ha1 : ∀ v ∈ Fl (a + 1), φ v = 0`. Assume the negation of the conclusion as `h`.

Use `hmax _ h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hjump : Fl (a + 1) ≠ Fl a` using `fun h => ha (h ▸ ha1)`. Establish `hlt` using `hbdd a ha`. Use `set K := min K₀ (min k (-a - Y)) with hK`.

Use `core K (fun m hm => (min_le_left _ _).trans (hK₁ m hm)) (-a - Y - K).toNat (Y - y') (fun l hl => ha1 _ (hFl (by omega) (h0 _))) (fun l hl hl' => by` as an intermediate fact. Use `hxs a (-(K + l) - a).toNat hjump (by omega) (by omega)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use the proof step `omega) (k - K).toNat (by omega)`. Use `this using 3` and compare the differences between its conclusion and the goal.

Use linear arithmetic over natural numbers and integers. Use `push Not at hex set K := min K₀ k with hK`. Use `core K (fun m hm => (min_le_left _ _).trans (hK₁ m hm)) ((k - K).toNat + 1) 0 (fun l _ => hex _ _ (h0 _)) (fun l hl hl' => by omega) (k - K).toNat (by omega)` as an intermediate fact. Use `this using 3` and compare the differences between its conclusion and the goal. Use linear arithmetic over natural numbers and integers.
-/
theorem filtLaurent_shift_line : ∀ (L : Type) [Field L] (M : Type) [AddCommGroup M] [Module L M] (Fl : ℤ → Submodule L M), Antitone Fl → ∀ (u : Lˣ) (p : PowerSeries L) (c : ℤ → L), PowerSeries.constantCoeff p ≠ 0 → (∀ x : ℤ, PowerSeries.constantCoeff p * c x = ((u ^ (-x) : Lˣ) : L) - 1) → ∀ (y' Y : ℕ) (xs : List ℤ), (∀ (a : ℤ) (j : ℕ), Fl (a + 1) ≠ Fl a → y' < j → j ≤ Y → a + (j : ℤ) ∈ xs) → ∀ seq : ℕ → ℤ → M, (∀ m, ∃ k₀ : ℤ, ∀ k < k₀, seq m k = 0) → (∀ m < xs.length, ∀ k : ℤ, ∑ᶠ j : ℕ, PowerSeries.coeff j p • (seq (m + 1) (k - j) + c (xs.getD m 0) • seq m (k - j)) = (((u ^ k : Lˣ) : L) - 1) • seq m k) → (∀ k : ℤ, seq 0 k ∈ Fl (-k - Y)) → ∀ k : ℤ, seq xs.length k ∈ Fl (-k - y') := by
  intro L _ M _ _ Fl hFl u p c hp hc y' Y xs hxs seq hbd hrec h0 k
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator] at hφ
  choose k₀ hk₀ using hbd

  have core : ∀ (K : ℤ), (∀ m ≤ xs.length, K ≤ k₀ m) → ∀ i n : ℕ,
      (∀ l < i, φ (seq 0 (K + l)) = 0) → (∀ l : ℕ, i ≤ l → l < i + n → -(K + l) ∈ xs) →
      ∀ l < i + n, φ (seq xs.length (K + l)) = 0 := by
    intro K hK i n hi hn
    set w : ℕ → L := fun l => ((u ^ (K + l) : Lˣ) : L) - 1 with hw
    set D : Module.End L L⟦X⟧ := LinearMap.mulLeft L p⁻¹ ∘ₗ filtLaurentDiag w with hDdef
    set G : ℕ → L⟦X⟧ := fun m => PowerSeries.mk fun l => φ (seq m (K + l)) with hG
    have hstep : ∀ m < xs.length, G (m + 1) = D (G m) - c (xs.getD m 0) • G m := by
      intro m hm
      have key : p * (G (m + 1) + c (xs.getD m 0) • G m) = filtLaurentDiag w (G m) := by
        ext l
        have h1 := hrec m hm (K + l)
        rw [finsum_eq_sum_of_support_subset (s := Finset.range (l + 1))] at h1
        · have h2 := congrArg φ h1
          rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun a b => coeff a p * coeff b (G (m + 1) + c (xs.getD m 0) • G m))]
          rw [map_sum, map_smul] at h2
          simp only [filtLaurentDiag, LinearMap.coe_mk, AddHom.coe_mk, coeff_mk, hG, hw]
          rw [← smul_eq_mul, ← h2]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hj' : j ≤ l := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
          have : K + ((l - j : ℕ) : ℤ) = K + l - j := by omega
          simp only [map_add, map_smul, coeff_mk, this, smul_eq_mul]
        · intro j hj
          by_contra hj'
          have hj'' : l + 1 ≤ j := by simpa using hj'
          have a1 := hK m hm.le
          have a2 := hK (m + 1) hm
          apply hj
          simp only
          rw [hk₀ (m + 1) _ (by omega), hk₀ m _ (by omega)]
          simp
      rw [eq_sub_iff_add_eq, hDdef, LinearMap.comp_apply, ← key, LinearMap.mulLeft_apply,
        ← mul_assoc, PowerSeries.inv_mul_cancel _ hp, one_mul]
    have hall : ∀ m ≤ xs.length, G m = Polynomial.aeval D
        ((xs.take m).map fun x => (Polynomial.X - Polynomial.C (c x) : Polynomial L)).prod
          (G 0) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        intro hm
        have hm' : m < xs.length := hm
        rw [hstep m hm', List.take_succ_eq_append_getElem hm', List.map_append, List.prod_append,
          mul_comm, map_mul, Module.End.mul_apply, ← ih hm'.le, List.getD_eq_getElem _ _ hm']
        simp [Module.algebraMap_end_apply]
    have hfin := filtLaurent_prod_raises D c K (fun l f hf =>
      filtLaurent_triangular w p hp l _ (by rw [hc, neg_neg]) f hf) n xs i (G 0)
      (X_pow_dvd_iff.2 fun l hl => by simpa [hG] using hi l hl) hn
    have h3 := hall xs.length le_rfl
    rw [List.take_length] at h3
    rw [← h3] at hfin
    intro l hl
    simpa [hG] using X_pow_dvd_iff.1 hfin l hl
  obtain ⟨K₀, hK₀⟩ := ((Set.finite_le_nat xs.length).image k₀).bddBelow
  have hK₁ : ∀ m ≤ xs.length, K₀ ≤ k₀ m := fun m hm => hK₀ ⟨m, hm, rfl⟩
  by_cases hex : ∃ a : ℤ, ¬ ∀ v ∈ Fl a, φ v = 0
  · have hbdd : ∀ a : ℤ, (¬ ∀ v ∈ Fl a, φ v = 0) → a < -k - y' := by
      intro a ha
      by_contra h
      exact ha fun v hv => hφ v (hFl (not_lt.1 h) hv)
    obtain ⟨a, ha, hmax⟩ := Int.exists_greatest_of_bdd
      ⟨-k - y', fun a ha => (hbdd a ha).le⟩ hex
    have ha1 : ∀ v ∈ Fl (a + 1), φ v = 0 := by
      by_contra h
      have := hmax _ h
      omega
    have hjump : Fl (a + 1) ≠ Fl a := fun h => ha (h ▸ ha1)
    have hlt := hbdd a ha
    set K := min K₀ (min k (-a - Y)) with hK
    have := core K (fun m hm => (min_le_left _ _).trans (hK₁ m hm)) (-a - Y - K).toNat (Y - y')
      (fun l hl => ha1 _ (hFl (by omega) (h0 _)))
      (fun l hl hl' => by
        have := hxs a (-(K + l) - a).toNat hjump (by omega) (by omega)
        convert this using 1
        omega) (k - K).toNat (by omega)
    convert this using 3
    omega
  · push Not at hex
    set K := min K₀ k with hK
    have := core K (fun m hm => (min_le_left _ _).trans (hK₁ m hm)) ((k - K).toNat + 1) 0
      (fun l _ => hex _ _ (h0 _)) (fun l hl hl' => by omega) (k - K).toNat (by omega)
    convert this using 3
    omega

end GlobalTheory
