import Formalism.WachLatticeTwists.WachProductBases.Statement
import Formalism.WindowSums.AnnihilatorPolynomials.ZpowVal

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N1

open Formalism.CoboundaryTransfers Finset

/- English proof (translation)
Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by omega⟩`. Use `⟨∑ k ∈ range m, (((m + 1).choose (k + 1 + 1) : ℕ) : A) * x ^ k, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_range_succ', Finset.mul_sum, add_comm]`. Use `congr 1`. Simplify using the standard rewrite rules.

Use `sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem q_mod {A : Type} [CommRing A] (x : A) (n : ℕ) (hn : 0 < n) :
    ∃ t : A, ∑ k ∈ range n, ((n.choose (k + 1) : ℕ) : A) * x ^ k = (n : A) + x * t := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨∑ k ∈ range m, (((m + 1).choose (k + 1 + 1) : ℕ) : A) * x ^ k, ?_⟩
  rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
  congr 1
  · simp
  · refine sum_congr rfl fun k _ => ?_
    ring

/- English proof (translation)
Introduce `O A _ _ _ S`. Establish `hX1 : ∃ t : A, S.X = S.π * t`. Rewrite using `[S.X_eq, HidaSetting.ε, HidaSetting.one_add_pow_sub_one]`. Conclude with `⟨_, rfl⟩`. Take `⟨t₂, hQ⟩ : ∃ t : A, S.Q = (S.ℓ : A) + S.X * t` from `q_mod S.X S.ℓ S.hℓ.pos`.

Use `set n : ℕ := S.ℓ ^ (S.s - 1) with hn`. Establish `hnpos : 0 < n` using `pow_pos S.hℓ.pos _`. Use `set c : A := algebraMap O A S.c₀ with hc`. Use `set w : A := c + S.X * S.Q * S.c₁ with hw`. Use `set σ : A := ∑ k ∈ range n, ((n.choose (k + 1) : ℕ) : A) * (S.X * S.Q * w) ^ k with hσdef`.

Take `⟨t₁, hσ⟩ : ∃ t : A, σ = (n : A) + (S.X * S.Q * w) * t` from `q_mod _ n hnpos`. Establish `hε : S.ε ^ n = 1 + S.X` using `by rw [S.X_eq]; ring`. Establish `hγε : S.γ S.ε = S.ε * (1 + S.X * S.Q * w)`. Use `S.γπ` as an intermediate fact. Rewrite `this` using `[S.iterate_phi_s_pi_eq_X_mul_Q]`.

Conclude with `this`. Establish `hγX : S.γ S.X = (1 + S.X) * (1 + S.X * S.Q * w * σ) - 1`. Establish `h1 : (1 + S.X * S.Q * w) ^ n = 1 + S.X * S.Q * w * σ`. Use `HidaSetting.one_add_pow_sub_one (S.X * S.Q * w) n` as an intermediate fact. Rewrite `this` using `[← hσdef]`.

Rewrite using `[← this]`. Expand and normalize the polynomial expressions, which then agree. Use `conv_lhs => rw [S.X_eq]`. Rewrite using `[map_sub, map_pow, map_one, hγε, mul_pow, h1, ← hn, hε]`. Establish `hpow : (S.ℓ : A) ^ S.s = (S.ℓ : A) * (n : A)`.

Establish `: S.s = (S.s - 1) + 1` using `by have := S.hs; omega`. Rewrite using `[hn, Nat.cast_pow]`. Use `conv_lhs => rw [this]`. Rewrite using `[pow_succ']`. Establish `hu : algebraMap O A S.u = 1 + (S.ℓ : A) ^ S.s * c`.

Simplify using `[HidaSetting.u, hc]`. Establish `h5 : S.γ S.X - S.X = S.X * S.Q * ((1 + S.X) * w * σ)`. Rewrite using `[hγX]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨hX1, ⟨t₂, hQ⟩, S.φ_X, ?_, ⟨_, h5⟩, ?_⟩` and prove the remaining obligations.

Use `⟨t₂ * (1 + S.X) * w * σ + (S.ℓ : A) * w * σ + (S.ℓ : A) * (S.Q * S.c₁) * σ + (S.ℓ : A) * c * (S.Q * w * t₁), ?_⟩` and prove the remaining obligations. Rewrite using `[hγX, hu]`. Take the linear combination `S.X * (1 + S.X) * w * σ * hQ + S.X * (S.ℓ : A) * c * hσ - S.X * c * hpow + S.X * (S.ℓ : A) * σ * hw`. Establish `hdvd : (S.γ S.X - S.X) ∣ (S.γ S.Q - S.Q)`. Rewrite using `[HidaSetting.Q, map_sum, ← Finset.sum_sub_distrib]`.

Apply `Finset.dvd_sum` to reduce the goal to its premises. Introduce `k _`. Rewrite using `[map_mul, map_natCast, map_pow, ← mul_sub]`. Conclude with `Dvd.dvd.mul_left (sub_dvd_pow_sub_pow _ _ k) _`. Take `⟨r, hr⟩` from `hdvd`.

Use `⟨(1 + S.X) * w * σ * r, ?_, ?_⟩` and prove the remaining obligations. Rewrite `hr` using `[h5]`. Take the linear combination `hr`. Introduce `hrad`. Take `⟨t₀, ht₀⟩` from `hX1`.

Use `(Ideal.mem_jacobson_bot.1 hrad) (t₀ * ((1 + S.X) * w * σ * r))` as an intermediate fact. Rewrite `this` using `[add_comm, ← mul_assoc, ← ht₀]`. Conclude with `this`.
-/
theorem base_facts_holds : BaseFacts := by
  intro O A _ _ _ S
  have hX1 : ∃ t : A, S.X = S.π * t := by
    rw [S.X_eq, HidaSetting.ε, HidaSetting.one_add_pow_sub_one]
    exact ⟨_, rfl⟩
  obtain ⟨t₂, hQ⟩ : ∃ t : A, S.Q = (S.ℓ : A) + S.X * t := q_mod S.X S.ℓ S.hℓ.pos
  set n : ℕ := S.ℓ ^ (S.s - 1) with hn
  have hnpos : 0 < n := pow_pos S.hℓ.pos _
  set c : A := algebraMap O A S.c₀ with hc
  set w : A := c + S.X * S.Q * S.c₁ with hw
  set σ : A := ∑ k ∈ range n, ((n.choose (k + 1) : ℕ) : A) * (S.X * S.Q * w) ^ k with hσdef
  obtain ⟨t₁, hσ⟩ : ∃ t : A, σ = (n : A) + (S.X * S.Q * w) * t := q_mod _ n hnpos
  have hε : S.ε ^ n = 1 + S.X := by rw [S.X_eq]; ring
  have hγε : S.γ S.ε = S.ε * (1 + S.X * S.Q * w) := by
    have := S.γπ
    rw [S.iterate_phi_s_pi_eq_X_mul_Q] at this
    exact this
  have hγX : S.γ S.X = (1 + S.X) * (1 + S.X * S.Q * w * σ) - 1 := by
    have h1 : (1 + S.X * S.Q * w) ^ n = 1 + S.X * S.Q * w * σ := by
      have := HidaSetting.one_add_pow_sub_one (S.X * S.Q * w) n
      rw [← hσdef] at this
      rw [← this]; ring
    conv_lhs => rw [S.X_eq]
    rw [map_sub, map_pow, map_one, hγε, mul_pow, h1, ← hn, hε]
  have hpow : (S.ℓ : A) ^ S.s = (S.ℓ : A) * (n : A) := by
    have : S.s = (S.s - 1) + 1 := by have := S.hs; omega
    rw [hn, Nat.cast_pow]
    conv_lhs => rw [this]
    rw [pow_succ']
  have hu : algebraMap O A S.u = 1 + (S.ℓ : A) ^ S.s * c := by
    simp [HidaSetting.u, hc]
  have h5 : S.γ S.X - S.X = S.X * S.Q * ((1 + S.X) * w * σ) := by
    rw [hγX]; ring
  refine ⟨hX1, ⟨t₂, hQ⟩, S.φ_X, ?_, ⟨_, h5⟩, ?_⟩
  · refine ⟨t₂ * (1 + S.X) * w * σ + (S.ℓ : A) * w * σ + (S.ℓ : A) * (S.Q * S.c₁) * σ +
      (S.ℓ : A) * c * (S.Q * w * t₁), ?_⟩
    rw [hγX, hu]
    linear_combination S.X * (1 + S.X) * w * σ * hQ + S.X * (S.ℓ : A) * c * hσ - S.X * c * hpow +
      S.X * (S.ℓ : A) * σ * hw
  · have hdvd : (S.γ S.X - S.X) ∣ (S.γ S.Q - S.Q) := by
      rw [HidaSetting.Q, map_sum, ← Finset.sum_sub_distrib]
      apply Finset.dvd_sum
      intro k _
      rw [map_mul, map_natCast, map_pow, ← mul_sub]
      exact Dvd.dvd.mul_left (sub_dvd_pow_sub_pow _ _ k) _
    obtain ⟨r, hr⟩ := hdvd
    refine ⟨(1 + S.X) * w * σ * r, ?_, ?_⟩
    · rw [h5] at hr
      linear_combination hr
    · intro hrad
      obtain ⟨t₀, ht₀⟩ := hX1
      have := (Ideal.mem_jacobson_bot.1 hrad) (t₀ * ((1 + S.X) * w * σ * r))
      rw [add_comm, ← mul_assoc, ← ht₀] at this
      exact this

/- English proof (translation)
Introduce `O A _ _ _ S`. Take `⟨-, -, h3, h4, -, t, h6, h7⟩` from `base_facts_holds O A S`. Use `⟨⟨1, ?_⟩, h4, fun hrad => ⟨1 + S.X * t, h7 hrad, ⟨t, rfl⟩, ?_⟩⟩` and prove the remaining obligations. Use `show S.φ S.X = S.X * S.Q ^ 1 * 1`. Rewrite using `[h3]`.

Expand and normalize the polynomial expressions, which then agree. Use `show S.γ S.Q = (1 + S.X * t) * S.Q`. Rewrite using `[h6]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem base_wach_holds : BaseWach := by
  intro O A _ _ _ S
  obtain ⟨-, -, h3, h4, -, t, h6, h7⟩ := base_facts_holds O A S
  refine ⟨⟨1, ?_⟩, h4, fun hrad => ⟨1 + S.X * t, h7 hrad, ⟨t, rfl⟩, ?_⟩⟩
  · show S.φ S.X = S.X * S.Q ^ 1 * 1
    rw [h3]; ring
  · show S.γ S.Q = (1 + S.X * t) * S.Q
    rw [h6]; ring

/- English proof (translation)
Introduce `A _ Δ _ _ _ φ γ π q r E u t w hφ hγ hφπ hw hwπ hr hq hE hγπ hu`. Establish `hprod : ∀ (d : Δ) (f : Δ → A), d • ∏ x, f x = ∏ x, d • f x` using `fun d f => map_prod (MulSemiringAction.toRingHom Δ A d) f univ`. Establish `hinv : ∀ (a : A) (d : Δ), d • (∏ d' : Δ, d' • a) = ∏ d' : Δ, d' • a`. Introduce `a d`. Rewrite using `[hprod]`.

Simplify using `only [smul_smul]`. Conclude with `Fintype.prod_equiv (Equiv.mulLeft d) _ _ (fun _ => rfl)`. Establish `hgen : ∀ (s : Finset Δ) (c : Δ → A), ∃ t', ∏ d ∈ s, (u + π * c d) = u ^ s.card + π * t'` using `by classical`. Introduce `s c`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => exact ⟨0, by simp⟩`. Consider the case `insert a s ha ih`. Take `⟨t', ht'⟩` from `ih`. Use `⟨c a * (u ^ s.card + π * t') + u * t', ?_⟩` and prove the remaining obligations. Rewrite using `[prod_insert ha, ht', card_insert_of_notMem ha]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨hinv π, ⟨∏ d, w d, ?_, ?_⟩, ⟨∏ d : Δ, d • r, ?_, hinv r, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one (fun d _ => hw d)`. Simplify using `only [hwπ]`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]`.

Conclude with `Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one (fun d _ => hr.map (MulSemiringAction.toRingHom Δ A d))`. Rewrite using `[map_prod]`. Simplify using `only [hφ, hφπ, hq, smul_mul', hE]`. Rewrite using `[prod_mul_distrib, prod_mul_distrib, prod_const, card_univ]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨t', ht'⟩` from `hgen univ (fun d => w d * d • t)`. Use `⟨t', ?_⟩` and prove the remaining obligations. Rewrite using `[map_prod, ← card_univ, ← ht', ← prod_mul_distrib]`. Use `prod_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[hγ, hγπ, smul_mul', smul_add, smul_mul', hu, hwπ]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem invariant_norm_holds : InvariantNorm := by
  intro A _ Δ _ _ _ φ γ π q r E u t w hφ hγ hφπ hw hwπ hr hq hE hγπ hu
  have hprod : ∀ (d : Δ) (f : Δ → A), d • ∏ x, f x = ∏ x, d • f x :=
    fun d f => map_prod (MulSemiringAction.toRingHom Δ A d) f univ
  have hinv : ∀ (a : A) (d : Δ), d • (∏ d' : Δ, d' • a) = ∏ d' : Δ, d' • a := by
    intro a d
    rw [hprod]
    simp only [smul_smul]
    exact Fintype.prod_equiv (Equiv.mulLeft d) _ _ (fun _ => rfl)
  have hgen : ∀ (s : Finset Δ) (c : Δ → A),
      ∃ t', ∏ d ∈ s, (u + π * c d) = u ^ s.card + π * t' := by
    classical
    intro s c
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert a s ha ih =>
      obtain ⟨t', ht'⟩ := ih
      refine ⟨c a * (u ^ s.card + π * t') + u * t', ?_⟩
      rw [prod_insert ha, ht', card_insert_of_notMem ha]
      ring
  refine ⟨hinv π, ⟨∏ d, w d, ?_, ?_⟩, ⟨∏ d : Δ, d • r, ?_, hinv r, ?_⟩, ?_⟩
  · exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one (fun d _ => hw d)
  · simp only [hwπ]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  · exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one
      (fun d _ => hr.map (MulSemiringAction.toRingHom Δ A d))
  · rw [map_prod]
    simp only [hφ, hφπ, hq, smul_mul', hE]
    rw [prod_mul_distrib, prod_mul_distrib, prod_const, card_univ]
    ring
  · obtain ⟨t', ht'⟩ := hgen univ (fun d => w d * d • t)
    refine ⟨t', ?_⟩
    rw [map_prod, ← card_univ, ← ht', ← prod_mul_distrib]
    refine prod_congr rfl fun d _ => ?_
    rw [hγ, hγπ, smul_mul', smul_add, smul_mul', hu, hwπ]
    ring

/- English proof (translation)
Introduce `ℓ _ u hℓ2 hv`. Establish `Z` using `Formalism.WindowSums.valuation_zpow_sub_one ℓ u 1 le_rfl (fun h => absurd h hℓ2) hv`. Establish `hℓ0 : (ℓ : ℤ_[ℓ]) ≠ 0`. Conclude with `(Fact.out : ℓ.Prime).ne_zero` after adjusting the coercions. Establish `hdiv : ∀ x : ℤ, (ℓ : ℤ_[ℓ]) ∣ 1 - ((u ^ (-x) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])`.

Introduce `x`. Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Take `⟨hne, hval⟩` from `Z (-x) (neg_ne_zero.2 hx)`. Establish `h1 : (ℓ : ℤ_[ℓ]) ^ 1 ∣ ((u ^ (-x) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1`.

Rewrite using `[← Ideal.mem_span_singleton, PadicInt.mem_span_pow_iff_le_valuation _ hne]`. Use linear arithmetic over natural numbers and integers. Rewrite `h1` using `[pow_one]`. Rewrite using `[← neg_sub]`. Conclude with `(dvd_neg).2 h1`.

Use `choose c hc using hdiv`. Use `⟨c, fun x => (hc x).symm, ?_, ?_⟩` and prove the remaining obligations. Establish `h0` using `hc 0`. Simplify using `at h0`. Break down `h0 with h | h` into its components or cases.

Conclude with `absurd h (Fact.out : ℓ.Prime).ne_zero`. Conclude with `h`. Introduce `x y hxy`. Take `⟨hne, hval⟩` from `Z (x - y) (sub_ne_zero.2 hxy)`. Establish `hspec` using `PadicInt.unitCoeff_spec hne`.

Rewrite `hspec` using `[hval]`. Take `⟨uc, huc⟩ : ∃ uc : ℤ_[ℓ]ˣ, ((u ^ (x - y) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 = (uc : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ (1 + padicValInt ℓ (x - y))` from `⟨_, hspec⟩`. Establish `hmul : ((u ^ (-y) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = ((u ^ (-x) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * ((u ^ (x - y) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])`. Rewrite using `[← Units.val_mul, ← zpow_add]`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree. Establish `h1 : (ℓ : ℤ_[ℓ]) * (c x - c y) = (ℓ : ℤ_[ℓ]) * ((ℓ : ℤ_[ℓ]) ^ padicValInt ℓ (x - y) * (((u ^ (-x) : ℤ_[ℓ]ˣ) * uc : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))`. Rewrite using `[mul_sub, ← hc x, ← hc y, Units.val_mul]`. Establish `h2 : ((u ^ (-y) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - ((u ^ (-x) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = ((u ^ (-x) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * (((u ^ (x - y) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1)`. Rewrite using `[hmul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h3 : (1 - ((u ^ (-x) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) - (1 - ((u ^ (-y) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) = ((u ^ (-y) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - ((u ^ (-x) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])` using `by ring`. Rewrite using `[h3, h2, huc]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `(Associated.symm ⟨_, (mul_left_cancel₀ hℓ0 h1).symm⟩)`.
-/
theorem consequence_five_holds : C5 := by
  intro ℓ _ u hℓ2 hv
  have Z := Formalism.WindowSums.valuation_zpow_sub_one ℓ u 1 le_rfl (fun h => absurd h hℓ2) hv
  have hℓ0 : (ℓ : ℤ_[ℓ]) ≠ 0 := by
    exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  have hdiv : ∀ x : ℤ, (ℓ : ℤ_[ℓ]) ∣ 1 - ((u ^ (-x) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · obtain ⟨hne, hval⟩ := Z (-x) (neg_ne_zero.2 hx)
      have h1 : (ℓ : ℤ_[ℓ]) ^ 1 ∣ ((u ^ (-x) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 := by
        rw [← Ideal.mem_span_singleton, PadicInt.mem_span_pow_iff_le_valuation _ hne]
        omega
      rw [pow_one] at h1
      rw [← neg_sub]
      exact (dvd_neg).2 h1
  choose c hc using hdiv
  refine ⟨c, fun x => (hc x).symm, ?_, ?_⟩
  · have h0 := hc 0
    simp at h0
    rcases h0 with h | h
    · exact absurd h (Fact.out : ℓ.Prime).ne_zero
    · exact h
  · intro x y hxy
    obtain ⟨hne, hval⟩ := Z (x - y) (sub_ne_zero.2 hxy)
    have hspec := PadicInt.unitCoeff_spec hne
    rw [hval] at hspec
    obtain ⟨uc, huc⟩ : ∃ uc : ℤ_[ℓ]ˣ, ((u ^ (x - y) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 =
        (uc : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ (1 + padicValInt ℓ (x - y)) := ⟨_, hspec⟩
    have hmul : ((u ^ (-y) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) =
        ((u ^ (-x) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * ((u ^ (x - y) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) := by
      rw [← Units.val_mul, ← zpow_add]
      congr 2
      ring
    have h1 : (ℓ : ℤ_[ℓ]) * (c x - c y) = (ℓ : ℤ_[ℓ]) * ((ℓ : ℤ_[ℓ]) ^ padicValInt ℓ (x - y) *
        (((u ^ (-x) : ℤ_[ℓ]ˣ) * uc : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) := by
      rw [mul_sub, ← hc x, ← hc y, Units.val_mul]
      have h2 : ((u ^ (-y) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - ((u ^ (-x) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) =
          ((u ^ (-x) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * (((u ^ (x - y) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) := by
        rw [hmul]; ring
      have h3 : (1 - ((u ^ (-x) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) - (1 - ((u ^ (-y) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) =
          ((u ^ (-y) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - ((u ^ (-x) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) := by ring
      rw [h3, h2, huc]
      ring
    exact (Associated.symm ⟨_, (mul_left_cancel₀ hℓ0 h1).symm⟩)

end Formalism.RepresentationBoundsCohomology.N1
