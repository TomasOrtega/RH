import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsGrpPullbackOfLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRingEquiv

noncomputable section

open CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompRat PeriodPair

namespace GlobalTheory.CompRat.Inertia

open GlobalTheory.CompRat.Weber

/- English proof (translation)
Simplify using `only [ValuationSubring.mem_nonunits_iff, not_lt] at *`. Establish `e₁ : A.valuation ((a - 1) * (x₁ - x₂)) < 1`. Rewrite using `[show (a - 1) * (x₁ - x₂) = (a * x₁ + b - x₁) - (a * x₂ + b - x₂) by ring]`. Conclude with `Valuation.map_sub_lt _ h₁ h₂`. Rewrite `e₁` using `[map_mul]`.

Establish `e₂ : A.valuation (a - 1) < 1` using `lt_of_le_of_lt (le_mul_of_one_le_right' h) e₁`. Rewrite using `[show a * y + b - y = (a * x₁ + b - x₁) + (a - 1) * (y - x₁) by ring]`. Use `Valuation.map_add_lt _ h₁ ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 (sub_mem my m₁))) e₂`.
-/
theorem affine_sub_mem (A : ValuationSubring ℂ) {a b x₁ x₂ y : ℂ} (m₁ : x₁ ∈ A) (my : y ∈ A)
    (h : x₁ - x₂ ∉ A.nonunits) (h₁ : a * x₁ + b - x₁ ∈ A.nonunits) (h₂ : a * x₂ + b - x₂ ∈ A.nonunits) :
    a * y + b - y ∈ A.nonunits := by
  simp only [ValuationSubring.mem_nonunits_iff, not_lt] at *
  have e₁ : A.valuation ((a - 1) * (x₁ - x₂)) < 1 := by
    rw [show (a - 1) * (x₁ - x₂) = (a * x₁ + b - x₁) - (a * x₂ + b - x₂) by ring]
    exact Valuation.map_sub_lt _ h₁ h₂
  rw [map_mul] at e₁
  have e₂ : A.valuation (a - 1) < 1 := lt_of_le_of_lt (le_mul_of_one_le_right' h) e₁
  rw [show a * y + b - y = (a * x₁ + b - x₁) + (a - 1) * (y - x₁) by ring]
  refine Valuation.map_add_lt _ h₁ ?_
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 (sub_mem my m₁))) e₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Establish `hd : 0 < H.d` using `H.d_prime.pos`. Establish `hs : Real.sqrt H.d ≠ 0` using `by positivity`. Establish `h2 : s.2 = 0`. Use `congrArg Complex.im h` as an intermediate fact. Apply the tactic sequence `rcases cmHost_rootComplex_eq_pm_sqrt H with e | e <;> simpa [wC, e, hs, hd.ne'] using this`.

Establish `h1 : s.1 = 0` using `by simpa [wC, h2] using h`. Conclude with `Prod.ext h1 h2`.
-/
theorem eq_zero_of_wC_eq_zero {s : ℤ × ℤ} (h : wC H s = 0) : s = 0 := by
  have hd : 0 < H.d := H.d_prime.pos
  have hs : Real.sqrt H.d ≠ 0 := by positivity
  have h2 : s.2 = 0 := by
    have := congrArg Complex.im h
    rcases cmHost_rootComplex_eq_pm_sqrt H with e | e <;> simpa [wC, e, hs, hd.ne'] using this
  have h1 : s.1 = 0 := by simpa [wC, h2] using h
  exact Prod.ext h1 h2

/- English proof (translation)
Take `⟨t, ht⟩` from `(hL _).1 h`. Establish `hk' : (k : ℂ) ≠ 0` using `by exact_mod_cast hk`. Rewrite `ht` using `[div_eq_iff hk']`. Establish `e : (s.1 - k * t.1, s.2 - k * t.2) = (0 : ℤ × ℤ)` using `eq_zero_of_wC_eq_zero (H := H) (by`. Simplify using `only [wC] at ht ⊢`.

Use `push_cast`. Take the linear combination `ht)`. Conclude with `⟨⟨t.1, sub_eq_zero.1 (congrArg Prod.fst e)⟩, ⟨t.2, sub_eq_zero.1 (congrArg Prod.snd e)⟩⟩`.
-/
theorem dvd_of_div_mem {L : PeriodPair} (hL : ∀ x, x ∈ L.lattice ↔ ∃ s, x = wC H s) {k : ℕ} (hk : k ≠ 0) {s : ℤ × ℤ}
    (h : wC H s / k ∈ L.lattice) : (k : ℤ) ∣ s.1 ∧ (k : ℤ) ∣ s.2 := by
  obtain ⟨t, ht⟩ := (hL _).1 h
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  rw [div_eq_iff hk'] at ht
  have e : (s.1 - k * t.1, s.2 - k * t.2) = (0 : ℤ × ℤ) := eq_zero_of_wC_eq_zero (H := H) (by
    simp only [wC] at ht ⊢
    push_cast
    linear_combination ht)
  exact ⟨⟨t.1, sub_eq_zero.1 (congrArg Prod.fst e)⟩, ⟨t.2, sub_eq_zero.1 (congrArg Prod.snd e)⟩⟩

/- English proof (translation)
Introduce and unpack `E _ _ _ H m n p A τ hp hA hn hmn h3 ⟨C, io, h, hfix⟩ hτ`. Establish `hm0 : m ≠ 0` using `by rintro rfl; simp at h3`. Establish `hn0 : n ≠ 0` using `by rintro rfl; exact hn (dvd_zero _)`. Establish `hk : ¬ p ∣ m / p ^ m.factorization p` using `Nat.not_dvd_ordCompl hp hm0`. Establish `hqk : p ^ m.factorization p * (m / p ^ m.factorization p) = m` using `Nat.ordProj_mul_ordCompl_eq_self m p`.

Generalize the expression as in `m / p ^ m.factorization p = k at h3 hk hqk`. Generalize the expression as in `p ^ m.factorization p = q at hqk`. Establish `hk0 : k ≠ 0` using `by omega`. Establish `hm' : (m : ℂ) ≠ 0` using `by exact_mod_cast hm0`. Establish `hn' : (n : ℂ) ≠ 0` using `by exact_mod_cast hn0`.

Establish `hk' : (k : ℂ) ≠ 0` using `by exact_mod_cast hk0`. Establish `hqk' : (q : ℂ) * k = m` using `by exact_mod_cast hqk`. Establish `hOK` using `GlobalTheory.MomOne.Basic.isOK_okPair H.d H.d_prime.pos`. Generalize the expression as in `GlobalTheory.MomOne.Basic.okPair H.d H.d_prime.pos = L at hOK`. Establish `hL : ∀ x, x ∈ L.lattice ↔ ∃ s, x = wC H s` using `fun x => (hOK x).trans (exists_wC_iff H x).symm`.

Take `⟨c, hc⟩` from `exists_multiplier C hL h`. Take `⟨x, α, β, hα, hx, hint, hsep⟩` from `exists_coord H.d_prime H.d_mod hOK hp A hA (N := k * n) fun hd => ((Nat.Prime.dvd_mul hp).1 hd).elim hk hn`. Establish `hpt : ∀ z z', C.pt z = C.pt z' ↔ z - z' ∈ L.lattice` using `fun z z' => by rw [pt_eq_iff, hL]`. Set `T : ℂ → ℂ → Prop` to `fun z z' => C.pt z ≫ io = spMap (τ : ℂ →+* ℂ) ≫ C.pt z'`. Establish `hm : ∀ a, T (wC H a / m) (wC H a / m)` using `fun a => by simpa [wC] using hfix a`.

Establish `h0 : T 0 0` using `by simpa [wC] using hm 0`. Establish `huniq : ∀ {z w z' w'}, T z z' → T w w' → z' - w' ∈ L.lattice → z - w ∈ L.lattice` using `fun {z w z' w'} a b e => (hpt _ _).1 (conj_inj h (a.trans ((congrArg _ ((hpt _ _).2 e)).trans b.symm)))`. Establish `hmul : ∀ {z z'}, T z z' → ∀ j : ℕ, T (j * z) (j * z')` using `fun {z z'} a j => by`. Proceed by induction on `j with`. Consider the case `zero => simpa using h0`.

Consider the case `succ j ih => simpa only [Nat.cast_succ, add_mul, one_mul] using conj_add h ih a`. Establish `hkT : ∀ a, T (wC H a / k) (wC H a / k)` using `fun a => by`. Establish `e : wC H ((q : ℤ) • a) / m = wC H a / k`. Rewrite `hm'`, the goal using `[← hqk']`. Use `left_ne_zero_of_mul hm'` as an intermediate fact.

Simplify using `only [wC, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Conclude with `e ▸ hm _`. Establish `hkN : ∀ a, ((k * n : ℕ) : ℂ) * (wC H a / k) ∈ L.lattice` using `fun a => (hL _).2 ⟨(n : ℤ) • a, by`.

Simplify using `only [wC, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]`. Use `push_cast`. Use the proof step `field_simp⟩`. Establish `hnN : ∀ a, ((k * n : ℕ) : ℂ) * (wC H a / n) ∈ L.lattice` using `fun a => (hL _).2 ⟨(k : ℤ) • a, by`. Simplify using `only [wC, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]`.

Use `push_cast`. Use the proof step `field_simp⟩`. Establish `hnot : ∀ (j : ℤ) (z : ℂ) (b : ℤ), j = 1 ∨ j = 2 → z = wC H (j, b) / k → z ∉ L.lattice`. Introduce and unpack `j _ b hj rfl hz`. Use `Int.le_of_dvd (by omega) (dvd_of_div_mem hL hk0 hz).1` as an intermediate fact.

Simplify using `only at this`. Use linear arithmetic over natural numbers and integers. Establish `haff : ∀ z z', T z z' → z' ∉ L.lattice → τ (x z') = τ α * c / α * x z + (τ β - τ α * c / α * β)` using `fun z z' a b => by`. Rewrite using `[hx, hx, map_add, map_mul, (hc z z' a b).2]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Generalize the expression as in `τ α * c / α = a at haff`. Generalize the expression as in `τ β - a * β = b at haff`. Establish `n₁ : wC H (1, 0) / k ∉ L.lattice` using `hnot 1 _ 0 (.inl rfl) rfl`. Establish `n₂ : wC H (1, 1) / k ∉ L.lattice` using `hnot 1 _ 1 (.inl rfl) rfl`.

Establish `key : ∀ z z', T z z' → ((k * n : ℕ) : ℂ) * z' ∈ L.lattice → z - z' ∈ L.lattice ∨ z + z' ∈ L.lattice`. Introduce `z z' t hz'`. Distinguish the cases in `hl : z' ∈ L.lattice`. Conclude with `.inl (sub_mem (by simpa using huniq t h0 (by simpa using hl)) hl)`. Establish `hz : ((k * n : ℕ) : ℂ) * z ∈ L.lattice` using `by simpa using huniq (hmul t (k * n)) h0 (by simpa using hz')`.

Establish `hl'` using `(hc z z' t hl).1`. Use `hsep z z' hz hz' hl' hl ?_` and prove the remaining obligations. Establish `i₁` using `hint _ (hkN _) n₁`. Establish `i₂` using `hint _ (hkN _) n₂`. Establish `e₁` using `affine_sub_mem A (a := a) (b := b) (x₂ := x (wC H (1, 1) / k)) i₁.2 (hint z hz hl').2 (fun e => (hsep _ _ (hkN _) (hkN _) n₁ n₂ e).elim (fun e' => ?_) (hnot 2 _ 1 (.inr rfl) (by simp only [wC]; push_cast; ring))) (haff _ _ (hkT _) n₁ ▸ hτ _ i₁.1 i₁.2) (haff _ _ (hkT _) n₂ ▸ hτ _ …`.

Establish `e₂` using `hτ _ (hint z' hz' hl).1 (hint z' hz' hl).2`. Rewrite `e₂` using `[haff z z' t hl]`. Rewrite `e₁`, `e₂`, the goal using `[ValuationSubring.mem_nonunits_iff]`. Rewrite using `[show x z - x z' = (a * x z + b - x z') - (a * x z + b - x z) by ring]`. Conclude with `Valuation.map_sub_lt _ e₂ e₁`.

Establish `e₂ : wC H (1, 0) / k - wC H (1, 1) / k = wC H (0, -1) / k` using `by simp only [wC]; push_cast; ring`. Use `Int.le_of_dvd (by omega) (Int.dvd_neg.1 (dvd_of_div_mem hL hk0 (e₂ ▸ e')).2)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hnT : ∀ s, T (wC H s / n) (wC H s / n)` using `fun s => by`. Take `⟨z, t⟩` from `exists_conj_pt h (wC H s / n)`.

It suffices to establish `e : z - wC H s / n ∈ L.lattice from (congrArg (· ≫ io) ((hpt _ _).2 e)).symm.trans t`. Use `(key _ _ t (hnN s)).elim id fun e => ?_` and prove the remaining obligations. Use `(key _ _ (conj_add h t (hkT (1, 0))) (by rw [mul_add]; exact add_mem (hnN _) (hkN _))).elim (fun e' => by simpa using e') fun e' => ?_` and prove the remaining obligations. Conclude with `absurd (sub_mem e' e) (hnot 2 _ 0 (.inr rfl) (by simp only [wC]; push_cast; ring))`. Use `⟨C, io, h, fun s => ?_⟩` and prove the remaining obligations.

Take `⟨u, v, huv⟩` from `Nat.isCoprime_iff_coprime.2 hmn`. Establish `huv' : (u : ℂ) * m + v * n = 1` using `by exact_mod_cast huv`. Establish `e : wC H s / (m * n : ℕ) = wC H (v • s) / m + wC H (u • s) / n`. Simplify using `only [wC, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `-(s.1 * 2 + s.2 * (1 + H.rt0)) * huv'`. Rewrite using `[show wC H (1, 0) = 1 by simp [wC], one_mul, e]`. Conclude with `conj_add h (hm _) (hnT _)`.
-/
theorem fixesCurve_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (m n p : ℕ) (A : ValuationSubring ℂ) (τ : ℂ ≃+* ℂ), p.Prime → (p : ℂ) ∈ A.nonunits → ¬ p ∣ n → Nat.Coprime m n → 3 ≤ m / p ^ m.factorization p → FixesCurve H τ m → (∀ x : ℂ, IsAlgebraic ℚ x → x ∈ A → τ x - x ∈ A.nonunits) → FixesCurve H τ (m * n) := by
  rintro E _ _ _ H m n p A τ hp hA hn hmn h3 ⟨C, io, h, hfix⟩ hτ
  have hm0 : m ≠ 0 := by rintro rfl; simp at h3
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero _)
  have hk : ¬ p ∣ m / p ^ m.factorization p := Nat.not_dvd_ordCompl hp hm0
  have hqk : p ^ m.factorization p * (m / p ^ m.factorization p) = m := Nat.ordProj_mul_ordCompl_eq_self m p
  generalize m / p ^ m.factorization p = k at h3 hk hqk
  generalize p ^ m.factorization p = q at hqk
  have hk0 : k ≠ 0 := by omega
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm0
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
  have hqk' : (q : ℂ) * k = m := by exact_mod_cast hqk
  have hOK := GlobalTheory.MomOne.Basic.isOK_okPair H.d H.d_prime.pos
  generalize GlobalTheory.MomOne.Basic.okPair H.d H.d_prime.pos = L at hOK
  have hL : ∀ x, x ∈ L.lattice ↔ ∃ s, x = wC H s := fun x => (hOK x).trans (exists_wC_iff H x).symm
  obtain ⟨c, hc⟩ := exists_multiplier C hL h
  obtain ⟨x, α, β, hα, hx, hint, hsep⟩ := exists_coord H.d_prime H.d_mod hOK hp A hA (N := k * n)
    fun hd => ((Nat.Prime.dvd_mul hp).1 hd).elim hk hn
  have hpt : ∀ z z', C.pt z = C.pt z' ↔ z - z' ∈ L.lattice := fun z z' => by rw [pt_eq_iff, hL]
  let T : ℂ → ℂ → Prop := fun z z' => C.pt z ≫ io = spMap (τ : ℂ →+* ℂ) ≫ C.pt z'
  have hm : ∀ a, T (wC H a / m) (wC H a / m) := fun a => by simpa [wC] using hfix a
  have h0 : T 0 0 := by simpa [wC] using hm 0
  have huniq : ∀ {z w z' w'}, T z z' → T w w' → z' - w' ∈ L.lattice → z - w ∈ L.lattice := fun {z w z' w'} a b e =>
    (hpt _ _).1 (conj_inj h (a.trans ((congrArg _ ((hpt _ _).2 e)).trans b.symm)))
  have hmul : ∀ {z z'}, T z z' → ∀ j : ℕ, T (j * z) (j * z') := fun {z z'} a j => by
    induction j with
    | zero => simpa using h0
    | succ j ih => simpa only [Nat.cast_succ, add_mul, one_mul] using conj_add h ih a
  have hkT : ∀ a, T (wC H a / k) (wC H a / k) := fun a => by
    have e : wC H ((q : ℤ) • a) / m = wC H a / k := by
      rw [← hqk'] at hm' ⊢
      have := left_ne_zero_of_mul hm'
      simp only [wC, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      push_cast
      field_simp
    exact e ▸ hm _
  have hkN : ∀ a, ((k * n : ℕ) : ℂ) * (wC H a / k) ∈ L.lattice := fun a => (hL _).2 ⟨(n : ℤ) • a, by
    simp only [wC, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    push_cast
    field_simp⟩
  have hnN : ∀ a, ((k * n : ℕ) : ℂ) * (wC H a / n) ∈ L.lattice := fun a => (hL _).2 ⟨(k : ℤ) • a, by
    simp only [wC, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    push_cast
    field_simp⟩
  have hnot : ∀ (j : ℤ) (z : ℂ) (b : ℤ), j = 1 ∨ j = 2 → z = wC H (j, b) / k → z ∉ L.lattice := by
    rintro j _ b hj rfl hz
    have := Int.le_of_dvd (by omega) (dvd_of_div_mem hL hk0 hz).1
    simp only at this
    omega
  have haff : ∀ z z', T z z' → z' ∉ L.lattice →
      τ (x z') = τ α * c / α * x z + (τ β - τ α * c / α * β) := fun z z' a b => by
    rw [hx, hx, map_add, map_mul, (hc z z' a b).2]
    field_simp
    ring
  generalize τ α * c / α = a at haff
  generalize τ β - a * β = b at haff
  have n₁ : wC H (1, 0) / k ∉ L.lattice := hnot 1 _ 0 (.inl rfl) rfl
  have n₂ : wC H (1, 1) / k ∉ L.lattice := hnot 1 _ 1 (.inl rfl) rfl
  have key : ∀ z z', T z z' → ((k * n : ℕ) : ℂ) * z' ∈ L.lattice → z - z' ∈ L.lattice ∨ z + z' ∈ L.lattice := by
    intro z z' t hz'
    by_cases hl : z' ∈ L.lattice
    · exact .inl (sub_mem (by simpa using huniq t h0 (by simpa using hl)) hl)
    have hz : ((k * n : ℕ) : ℂ) * z ∈ L.lattice := by simpa using huniq (hmul t (k * n)) h0 (by simpa using hz')
    have hl' := (hc z z' t hl).1
    refine hsep z z' hz hz' hl' hl ?_
    have i₁ := hint _ (hkN _) n₁
    have i₂ := hint _ (hkN _) n₂
    have e₁ := affine_sub_mem A (a := a) (b := b) (x₂ := x (wC H (1, 1) / k)) i₁.2 (hint z hz hl').2
      (fun e => (hsep _ _ (hkN _) (hkN _) n₁ n₂ e).elim (fun e' => ?_)
        (hnot 2 _ 1 (.inr rfl) (by simp only [wC]; push_cast; ring)))
      (haff _ _ (hkT _) n₁ ▸ hτ _ i₁.1 i₁.2) (haff _ _ (hkT _) n₂ ▸ hτ _ i₂.1 i₂.2)
    · have e₂ := hτ _ (hint z' hz' hl).1 (hint z' hz' hl).2
      rw [haff z z' t hl] at e₂
      rw [ValuationSubring.mem_nonunits_iff] at e₁ e₂ ⊢
      rw [show x z - x z' = (a * x z + b - x z') - (a * x z + b - x z) by ring]
      exact Valuation.map_sub_lt _ e₂ e₁
    · have e₂ : wC H (1, 0) / k - wC H (1, 1) / k = wC H (0, -1) / k := by simp only [wC]; push_cast; ring
      have := Int.le_of_dvd (by omega) (Int.dvd_neg.1 (dvd_of_div_mem hL hk0 (e₂ ▸ e')).2)
      omega
  have hnT : ∀ s, T (wC H s / n) (wC H s / n) := fun s => by
    obtain ⟨z, t⟩ := exists_conj_pt h (wC H s / n)
    suffices e : z - wC H s / n ∈ L.lattice from (congrArg (· ≫ io) ((hpt _ _).2 e)).symm.trans t
    refine (key _ _ t (hnN s)).elim id fun e => ?_
    refine (key _ _ (conj_add h t (hkT (1, 0))) (by rw [mul_add]; exact add_mem (hnN _) (hkN _))).elim
      (fun e' => by simpa using e') fun e' => ?_
    exact absurd (sub_mem e' e) (hnot 2 _ 0 (.inr rfl) (by simp only [wC]; push_cast; ring))
  refine ⟨C, io, h, fun s => ?_⟩
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hmn
  have huv' : (u : ℂ) * m + v * n = 1 := by exact_mod_cast huv
  have e : wC H s / (m * n : ℕ) = wC H (v • s) / m + wC H (u • s) / n := by
    simp only [wC, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    push_cast
    field_simp
    linear_combination -(s.1 * 2 + s.2 * (1 + H.rt0)) * huv'
  rw [show wC H (1, 0) = 1 by simp [wC], one_mul, e]
  exact conj_add h (hm _) (hnT _)

end GlobalTheory.CompRat.Inertia
