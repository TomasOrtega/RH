import Mathlib
import Development.AutomorphicArithmetic.CMTraceForms.Places

open NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs Formalism.L2.Pj UpperTheory.Depth

/- English proof (translation)
Establish `h1 : (H.bar H.rt) ^ 2 = H.rt ^ 2` using `by rw [← map_pow, H.rt_sq]; simp`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h` into its components or cases. It suffices to derive a contradiction. Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `h2 : IsCMField.complexConj E (H.rt : E) = (H.rt : E)` using `by rw [← H.bar_eq, h]`.

Establish `h3` using `IsCMField.complexEmbedding_complexConj E φ (H.rt : E)`. Rewrite `h3` using `[h2]`. Establish `h4 : (φ (H.rt : E)) ^ 2 = -(H.d : ℂ)`. Use `congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq` as an intermediate fact. Simplify using `using this`.

Establish `h5 : (φ (H.rt : E)).im = 0` using `Complex.conj_eq_iff_im.1 h3.symm`. Establish `h6` using `congrArg Complex.re h4`. Simplify using `[sq, h5] at h6`. Establish `h7 : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Use polynomial arithmetic with `[mul_self_nonneg (φ (H.rt : E)).re]`.

Conclude with `h`.
-/
private theorem bar_rt' {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : H.bar H.rt = -H.rt := by
  have h1 : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exfalso
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h2 : IsCMField.complexConj E (H.rt : E) = (H.rt : E) := by rw [← H.bar_eq, h]
    have h3 := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
    rw [h2] at h3
    have h4 : (φ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
      have := congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
      simpa using this
    have h5 : (φ (H.rt : E)).im = 0 := Complex.conj_eq_iff_im.1 h3.symm
    have h6 := congrArg Complex.re h4
    simp [sq, h5] at h6
    have h7 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [mul_self_nonneg (φ (H.rt : E)).re]
  · exact h

/- English proof (translation)
Establish `h` using `congrArg H.bar H.two_weight_eq_one_add_root`. Rewrite `h` using `[map_mul, map_add, map_one, bar_rt', map_ofNat]`. Establish `h2 : (2 : 𝓞 E) * H.bar H.w0 = 2 * (1 - H.w0)` using `by linear_combination h + H.two_weight_eq_one_add_root`. Conclude with `mul_left_cancel₀ two_ne_zero h2`.
-/
private theorem host_bar_w0_eq_one_sub_w0 {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.bar H.w0 = 1 - H.w0 := by
  have h := congrArg H.bar H.two_weight_eq_one_add_root
  rw [map_mul, map_add, map_one, bar_rt', map_ofNat] at h
  have h2 : (2 : 𝓞 E) * H.bar H.w0 = 2 * (1 - H.w0) := by linear_combination h + H.two_weight_eq_one_add_root
  exact mul_left_cancel₀ two_ne_zero h2

/- English proof (translation)
Use `haveI := Fact.mk hp`. Establish `hdm` using `H.d_mod`. Distinguish the cases in `hp2 : p = 2`. Substitute `hp2` using the available equality. Establish `hpd : ¬ 2 ∣ H.d` using `by omega`.

Use `⟨hpd, H.w0, H.bar H.w0, (H.d + 1) / 4, 1, rfl, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[host_bar_w0_eq_one_sub_w0, map_sub, map_one, host_bar_w0_eq_one_sub_w0]`. Expand and normalize the polynomial expressions, which then agree. Establish `hn4 : 4 * ((H.d + 1) / 4) = H.d + 1` using `by omega`. Establish `hn4' : (4 : 𝓞 E) * (((H.d + 1) / 4 : ℕ) : 𝓞 E) = (H.d : 𝓞 E) + 1`.

Conclude with `hn4` after adjusting the coercions. Rewrite using `[host_bar_w0_eq_one_sub_w0]`. Apply `mul_left_cancel₀ (show (4 : 𝓞 E) ≠ 0 by norm_num)` to reduce the goal to its premises. Take the linear combination `(-(2 * H.w0 - 1 + H.rt)) * H.two_weight_eq_one_add_root - H.rt_sq - hn4'`. Rewrite using `[host_bar_w0_eq_one_sub_w0]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Establish `hjac : jacobiSym (-(H.d : ℤ)) p = 1`.

Break down `hs with h | h` into its components or cases. Conclude with `absurd h hp2`. Conclude with `h`. Establish `hleg : legendreSym p (-(H.d : ℤ)) = 1`. Rewrite using `[jacobiSym.legendreSym.to_jacobiSym]`.

Conclude with `hjac`. Establish `hpd : ¬ p ∣ H.d`. Introduce `hdiv`. Establish `h0 : ((-(H.d : ℤ) : ℤ) : ZMod p) = 0`. Use `push_cast`.

Rewrite using `[(ZMod.natCast_eq_zero_iff _ _).mpr hdiv, neg_zero]`. Rewrite `hleg` using `[(legendreSym.eq_zero_iff p _).mpr h0]`. Conclude with `zero_ne_one hleg`. Establish `hne : ((-(H.d : ℤ) : ℤ) : ZMod p) ≠ 0`. Introduce `h0`.

Apply `hpd` to reduce the goal to its premises. Rewrite using `[← ZMod.natCast_eq_zero_iff]`. Establish `: -((H.d : ℕ) : ZMod p) = 0` using `by exact_mod_cast h0`. Conclude with `neg_eq_zero.mp this`. Take `⟨r, hr⟩` from `(legendreSym.eq_one_iff p hne).mp hleg`.

Take `⟨a, hra⟩ : ∃ a : ℕ, (a : ZMod p) = r` from `⟨r.val, ZMod.natCast_zmod_val r⟩`. Establish `hn : p ∣ a ^ 2 + H.d`. Rewrite using `[← ZMod.natCast_eq_zero_iff]`. Establish `hr' : -((H.d : ℕ) : ZMod p) = r * r` using `by exact_mod_cast hr`. Use `push_cast`.

Rewrite using `[hra, sq, ← hr']`. Expand and normalize the polynomial expressions, which then agree. Establish `ht : ¬ p ∣ 2 * a`. Introduce `h2a`. Break down `(Nat.Prime.dvd_mul hp).mp h2a with h | h` into its components or cases.

Conclude with `hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)`. Apply `hne` to reduce the goal to its premises. Establish `: r = 0`. Rewrite using `[← hra]`. Conclude with `(ZMod.natCast_eq_zero_iff _ _).mpr h`.

Rewrite using `[hr, this, mul_zero]`. Use `⟨hpd, (a : 𝓞 E) + H.rt, (a : 𝓞 E) - H.rt, a ^ 2 + H.d, 2 * a, ?_, ?_, ?_, ?_, hn, ht⟩` and prove the remaining obligations. Rewrite using `[map_add, map_natCast, bar_rt']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_sub, map_natCast, bar_rt']`.

Expand and normalize the polynomial expressions, which then agree. Use `push_cast`. Take the linear combination `(-1 : 𝓞 E) * H.rt_sq`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem exists_beta {p : ℕ} (hp : p.Prime) {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (hs : SplitAt H.d p) : ¬ p ∣ H.d ∧ ∃ (β γ : 𝓞 E) (n t : ℕ), H.bar β = γ ∧ H.bar γ = β ∧ γ * β = (n : 𝓞 E) ∧
      β + γ = (t : 𝓞 E) ∧ p ∣ n ∧ ¬ p ∣ t := by
  haveI := Fact.mk hp
  have hdm := H.d_mod
  by_cases hp2 : p = 2
  · subst hp2
    have hpd : ¬ 2 ∣ H.d := by omega
    refine ⟨hpd, H.w0, H.bar H.w0, (H.d + 1) / 4, 1, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [host_bar_w0_eq_one_sub_w0, map_sub, map_one, host_bar_w0_eq_one_sub_w0]
      ring
    · have hn4 : 4 * ((H.d + 1) / 4) = H.d + 1 := by omega
      have hn4' : (4 : 𝓞 E) * (((H.d + 1) / 4 : ℕ) : 𝓞 E) = (H.d : 𝓞 E) + 1 := by
        exact_mod_cast hn4
      rw [host_bar_w0_eq_one_sub_w0]
      apply mul_left_cancel₀ (show (4 : 𝓞 E) ≠ 0 by norm_num)
      linear_combination (-(2 * H.w0 - 1 + H.rt)) * H.two_weight_eq_one_add_root - H.rt_sq - hn4'
    · rw [host_bar_w0_eq_one_sub_w0]
      push_cast
      ring
    · omega
    · omega
  · have hjac : jacobiSym (-(H.d : ℤ)) p = 1 := by
      rcases hs with h | h
      · exact absurd h hp2
      · exact h
    have hleg : legendreSym p (-(H.d : ℤ)) = 1 := by
      rw [jacobiSym.legendreSym.to_jacobiSym]
      exact hjac
    have hpd : ¬ p ∣ H.d := by
      intro hdiv
      have h0 : ((-(H.d : ℤ) : ℤ) : ZMod p) = 0 := by
        push_cast
        rw [(ZMod.natCast_eq_zero_iff _ _).mpr hdiv, neg_zero]
      rw [(legendreSym.eq_zero_iff p _).mpr h0] at hleg
      exact zero_ne_one hleg
    have hne : ((-(H.d : ℤ) : ℤ) : ZMod p) ≠ 0 := by
      intro h0
      apply hpd
      rw [← ZMod.natCast_eq_zero_iff]
      have : -((H.d : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
      exact neg_eq_zero.mp this
    obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff p hne).mp hleg
    obtain ⟨a, hra⟩ : ∃ a : ℕ, (a : ZMod p) = r := ⟨r.val, ZMod.natCast_zmod_val r⟩
    have hn : p ∣ a ^ 2 + H.d := by
      rw [← ZMod.natCast_eq_zero_iff]
      have hr' : -((H.d : ℕ) : ZMod p) = r * r := by exact_mod_cast hr
      push_cast
      rw [hra, sq, ← hr']
      ring
    have ht : ¬ p ∣ 2 * a := by
      intro h2a
      rcases (Nat.Prime.dvd_mul hp).mp h2a with h | h
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
      · apply hne
        have : r = 0 := by
          rw [← hra]
          exact (ZMod.natCast_eq_zero_iff _ _).mpr h
        rw [hr, this, mul_zero]
    refine ⟨hpd, (a : 𝓞 E) + H.rt, (a : 𝓞 E) - H.rt, a ^ 2 + H.d, 2 * a, ?_, ?_, ?_, ?_, hn, ht⟩
    · rw [map_add, map_natCast, bar_rt']
      ring
    · rw [map_sub, map_natCast, bar_rt']
      ring
    · push_cast
      linear_combination (-1 : 𝓞 E) * H.rt_sq
    · push_cast
      ring

/- English proof (translation)
Introduce `p hp E _ _ _ H hs C _ _ v O _ _ hv hpu`. Use `haveI := Fact.mk hp`. Take `⟨hpd, β, γ, n, t, hβ, hγ, hn, ht, hpn, hpt⟩` from `exists_beta hp H hs`. Establish `vle : ∀ z : ℤ, v (z : C) ≤ 1` using `fun z => by`. Establish `h` using `hv.map_le_one (z : O)`.

Rewrite `h` using `[map_intCast]`. Then use the resulting hypothesis. Establish `vp : v (p : C) < 1`. Establish `h1` using `hv.map_le_one (p : O)`. Rewrite `h1` using `[map_natCast]`. Use `lt_of_le_of_ne h1 ?_` and prove the remaining obligations.

Introduce `h`. Apply `hpu` to reduce the goal to its premises. Apply `hv.isUnit_of_one'` to reduce the goal to its premises. Rewrite using `[map_natCast]`. Conclude with `h`.

Establish `vcop : ∀ m : ℕ, ¬ p ∣ m → v (m : C) = 1`. Introduce `m hm`. Establish `hle : v (m : C) ≤ 1` using `by exact_mod_cast vle m`. Use `le_antisymm hle ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`.

Use `push_neg at hlt`. Establish `hcop : Nat.Coprime p m` using `(Nat.Prime.coprime_iff_not_dvd hp).mpr hm`. Establish `hb` using `Nat.gcd_eq_gcd_ab p m`. Rewrite `hb` using `[Nat.Coprime.gcd_eq_one hcop]`. Establish `h1 : (1 : C) = (p : C) * (Nat.gcdA p m : C) + (m : C) * (Nat.gcdB p m : C)`.

Conclude with `hb` after adjusting the coercions. Establish `h2 : v (1 : C) < 1`. Rewrite using `[h1]`. Apply `Valuation.map_add_lt` to reduce the goal to its premises. Rewrite using `[map_mul]`.

Conclude with `mul_lt_one_of_nonneg_of_lt_one_left (by positivity) vp (vle _)`. Rewrite using `[map_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_left (by positivity) hlt (vle _)`. Simplify using `at h2`. Establish `vn : v (n : C) ≤ v (p : C)`.

Establish `h` using `hv.le_of_dvd (Nat.cast_dvd_cast hpn : (p : O) ∣ (n : O))`. Simplify `h` using `only [map_natCast]`. Establish `key : ∀ (b g : O), b * g = (n : O) → b + g = (t : O) → v (algebraMap O C b) = 1 → ∀ k : ℕ, (p : O) ^ (k + 1) ∣ b ^ ((p - 1) * p ^ k) - 1`. Introduce `b g hbg hbgt hb k`. Establish `hvn : v (algebraMap O C g) = v (n : C)`.

Rewrite using `[← map_natCast (algebraMap O C) n, ← hbg, map_mul, map_mul, hb, one_mul]`. Establish `hpg : (p : O) ∣ g`. Apply `hv.dvd_of_le` to reduce the goal to its premises. Rewrite using `[hvn, map_natCast (algebraMap O C)]`. Conclude with `vn`.

Establish `hpb : (p : O) ∣ b - t`. Establish `h : b - t = -g`. Rewrite using `[← hbgt]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`.

Conclude with `(dvd_neg).mpr hpg`. Establish `h1 : (p : O) ∣ b ^ (p - 1) - (t : O) ^ (p - 1)` using `dvd_trans hpb (sub_dvd_pow_sub_pow _ _ _)`. Establish `h2` using `dvd_sub_pow_of_dvd_sub h1 k`. Rewrite `h2` using `[← pow_mul, ← pow_mul]`. Establish `hcop : Nat.Coprime t (p ^ (k + 1))` using `Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpt).symm`.

Establish `h3` using `Nat.ModEq.pow_totient hcop`. Rewrite `h3` using `[Nat.totient_prime_pow_succ hp k]`. Establish `h4` using `map_dvd (Int.castRingHom O) h3.symm.dvd`. Move the coercions through the operations in `[eq_intCast] at h4`. Rewrite `h4` using `[mul_comm (p ^ k)]`.

Establish `h5 : b ^ ((p - 1) * p ^ k) - 1 = (b ^ ((p - 1) * p ^ k) - (t : O) ^ ((p - 1) * p ^ k)) + ((t : O) ^ ((p - 1) * p ^ k) - 1)` using `by ring`. Rewrite using `[h5]`. Conclude with `dvd_add h2 h4`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `σ`.

Establish `hw : σ H.w0 - σ (H.bar H.w0) = σ H.rt`. Rewrite using `[host_bar_w0_eq_one_sub_w0, ← map_sub]`. Use `congr 1`. Take the linear combination `H.two_weight_eq_one_add_root`. Rewrite using `[hw]`.

Establish `hdu : IsUnit (H.d : O)` using `hv.isUnit_of_one' (by rw [map_natCast]; exact vcop _ hpd)`. Establish `hsq : σ H.rt ^ 2 = -(H.d : O)`. Rewrite using `[← map_pow, H.rt_sq, map_neg, map_natCast]`. Establish `hu : IsUnit (σ H.rt ^ 2)`. Rewrite using `[hsq]`.

Conclude with `hdu.neg`. Conclude with `(isUnit_pow_iff two_ne_zero).mp hu`. Introduce `x hx`. Establish `hvx : 0 < v (algebraMap O C x)` using `hv.valuation_pos_iff_ne_zero.mpr hx`. Take `⟨k, hk⟩` from `NNReal.exists_pow_lt_of_lt_one hvx vp`.

Establish `hkM : k + 1 ≤ (p - 1) * p ^ k`. Establish `h1 : k < p ^ k` using `Nat.lt_pow_self hp.one_lt`. Establish `h2 : 1 ≤ p - 1`. Use `hp.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use the polynomial consequences of the given equalities and inequalities. Use `⟨n ^ ((p - 1) * p ^ k), ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Nat.cast_pow, map_pow]`. Use `_ ≤ v (p : C) ^ ((p - 1) * p ^ k) := pow_le_pow_left₀ (by positivity) vn _`.

Use `_ ≤ v (p : C) ^ k := pow_le_pow_of_le_one (by positivity) vp.le (by omega)`. Use `_ < _ := hk`. Introduce `σ`. Establish `hbg : σ β * σ γ = (n : O)`. Rewrite using `[← map_mul, mul_comm β γ, hn, map_natCast]`.

Establish `hsum : σ β + σ γ = (t : O)`. Rewrite using `[← map_add, ht, map_natCast]`. Establish `close : ∀ b : O, (p : O) ^ (k + 1) ∣ b ^ ((p - 1) * p ^ k) - 1 → v (algebraMap O C (b ^ ((p - 1) * p ^ k) - 1)) < v (algebraMap O C x)`. Introduce `b hb`. Combine the equalities or inequalities in the displayed calculation.

Establish `hor : v (algebraMap O C (σ β)) = 1 ∨ v (algebraMap O C (σ γ)) = 1`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `h1 : v (algebraMap O C (σ β)) < 1` using `lt_of_le_of_ne (hv.map_le_one _) hc.1`. Establish `h2 : v (algebraMap O C (σ γ)) < 1` using `lt_of_le_of_ne (hv.map_le_one _) hc.2`.

Establish `h3 : v (algebraMap O C (σ β + σ γ)) < 1`. Rewrite using `[map_add]`. Conclude with `Valuation.map_add_lt v h1 h2`. Rewrite `h3` using `[hsum, map_natCast, vcop t hpt]`. Conclude with `lt_irrefl _ h3`.

Break down `hor with h | h` into its components or cases. Use `⟨β ^ ((p - 1) * p ^ k), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow, hβ, ← mul_pow, hn, Nat.cast_pow]`. Rewrite using `[map_pow]`. Conclude with `close _ (key _ _ hbg hsum h k)`.

Use `⟨γ ^ ((p - 1) * p ^ k), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow, hγ, ← mul_pow, mul_comm β γ, hn, Nat.cast_pow]`. Rewrite using `[map_pow]`. Conclude with `close _ (key _ _ (by rw [mul_comm]; exact hbg) (by rw [add_comm]; exact hsum) h k)`.
-/
theorem UpperTheory.cmDatum_splitPlaces_conj_stable :
    ∀ (p : ℕ), p.Prime → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), SplitAt H.d p →
      ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ¬ IsUnit (p : O) →
      (∀ σ : 𝓞 E →+* O, IsUnit (σ H.w0 - σ (H.bar H.w0))) ∧ ∀ x : O, x ≠ 0 → ∃ N : ℕ, v (N : C) < v (algebraMap O C x) ∧
        ∀ σ : 𝓞 E →+* O, ∃ a : 𝓞 E, H.bar a * a = (N : 𝓞 E) ∧ v (algebraMap O C (σ a - 1)) < v (algebraMap O C x) := by
  intro p hp E _ _ _ H hs C _ _ v O _ _ hv hpu
  haveI := Fact.mk hp
  obtain ⟨hpd, β, γ, n, t, hβ, hγ, hn, ht, hpn, hpt⟩ := exists_beta hp H hs
  have vle : ∀ z : ℤ, v (z : C) ≤ 1 := fun z => by
    have h := hv.map_le_one (z : O)
    rwa [map_intCast] at h
  have vp : v (p : C) < 1 := by
    have h1 := hv.map_le_one (p : O)
    rw [map_natCast] at h1
    refine lt_of_le_of_ne h1 ?_
    intro h
    apply hpu
    apply hv.isUnit_of_one'
    rw [map_natCast]
    exact h
  have vcop : ∀ m : ℕ, ¬ p ∣ m → v (m : C) = 1 := by
    intro m hm
    have hle : v (m : C) ≤ 1 := by exact_mod_cast vle m
    refine le_antisymm hle ?_
    by_contra hlt
    push_neg at hlt
    have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hm
    have hb := Nat.gcd_eq_gcd_ab p m
    rw [Nat.Coprime.gcd_eq_one hcop] at hb
    have h1 : (1 : C) = (p : C) * (Nat.gcdA p m : C) + (m : C) * (Nat.gcdB p m : C) := by
      exact_mod_cast hb
    have h2 : v (1 : C) < 1 := by
      rw [h1]
      apply Valuation.map_add_lt
      · rw [map_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_left (by positivity) vp (vle _)
      · rw [map_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_left (by positivity) hlt (vle _)
    simp at h2
  have vn : v (n : C) ≤ v (p : C) := by
    have h := hv.le_of_dvd (Nat.cast_dvd_cast hpn : (p : O) ∣ (n : O))
    simpa only [map_natCast] using h
  have key : ∀ (b g : O), b * g = (n : O) → b + g = (t : O) → v (algebraMap O C b) = 1 →
      ∀ k : ℕ, (p : O) ^ (k + 1) ∣ b ^ ((p - 1) * p ^ k) - 1 := by
    intro b g hbg hbgt hb k
    have hvn : v (algebraMap O C g) = v (n : C) := by
      rw [← map_natCast (algebraMap O C) n, ← hbg, map_mul, map_mul, hb, one_mul]
    have hpg : (p : O) ∣ g := by
      apply hv.dvd_of_le
      rw [hvn, map_natCast (algebraMap O C)]
      exact vn
    have hpb : (p : O) ∣ b - t := by
      have h : b - t = -g := by
        rw [← hbgt]
        ring
      rw [h]
      exact (dvd_neg).mpr hpg
    have h1 : (p : O) ∣ b ^ (p - 1) - (t : O) ^ (p - 1) :=
      dvd_trans hpb (sub_dvd_pow_sub_pow _ _ _)
    have h2 := dvd_sub_pow_of_dvd_sub h1 k
    rw [← pow_mul, ← pow_mul] at h2
    have hcop : Nat.Coprime t (p ^ (k + 1)) :=
      Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpt).symm
    have h3 := Nat.ModEq.pow_totient hcop
    rw [Nat.totient_prime_pow_succ hp k] at h3
    have h4 := map_dvd (Int.castRingHom O) h3.symm.dvd
    push_cast [eq_intCast] at h4
    rw [mul_comm (p ^ k)] at h4
    have h5 : b ^ ((p - 1) * p ^ k) - 1 = (b ^ ((p - 1) * p ^ k) - (t : O) ^ ((p - 1) * p ^ k)) +
        ((t : O) ^ ((p - 1) * p ^ k) - 1) := by ring
    rw [h5]
    exact dvd_add h2 h4
  refine ⟨?_, ?_⟩
  · intro σ
    have hw : σ H.w0 - σ (H.bar H.w0) = σ H.rt := by
      rw [host_bar_w0_eq_one_sub_w0, ← map_sub]
      congr 1
      linear_combination H.two_weight_eq_one_add_root
    rw [hw]
    have hdu : IsUnit (H.d : O) := hv.isUnit_of_one' (by rw [map_natCast]; exact vcop _ hpd)
    have hsq : σ H.rt ^ 2 = -(H.d : O) := by
      rw [← map_pow, H.rt_sq, map_neg, map_natCast]
    have hu : IsUnit (σ H.rt ^ 2) := by
      rw [hsq]
      exact hdu.neg
    exact (isUnit_pow_iff two_ne_zero).mp hu
  · intro x hx
    have hvx : 0 < v (algebraMap O C x) := hv.valuation_pos_iff_ne_zero.mpr hx
    obtain ⟨k, hk⟩ := NNReal.exists_pow_lt_of_lt_one hvx vp
    have hkM : k + 1 ≤ (p - 1) * p ^ k := by
      have h1 : k < p ^ k := Nat.lt_pow_self hp.one_lt
      have h2 : 1 ≤ p - 1 := by
        have := hp.two_le
        omega
      nlinarith
    refine ⟨n ^ ((p - 1) * p ^ k), ?_, ?_⟩
    · calc v (((n ^ ((p - 1) * p ^ k) : ℕ)) : C) = v (n : C) ^ ((p - 1) * p ^ k) := by
            rw [Nat.cast_pow, map_pow]
        _ ≤ v (p : C) ^ ((p - 1) * p ^ k) := pow_le_pow_left₀ (by positivity) vn _
        _ ≤ v (p : C) ^ k := pow_le_pow_of_le_one (by positivity) vp.le (by omega)
        _ < _ := hk
    · intro σ
      have hbg : σ β * σ γ = (n : O) := by
        rw [← map_mul, mul_comm β γ, hn, map_natCast]
      have hsum : σ β + σ γ = (t : O) := by
        rw [← map_add, ht, map_natCast]
      have close : ∀ b : O, (p : O) ^ (k + 1) ∣ b ^ ((p - 1) * p ^ k) - 1 →
          v (algebraMap O C (b ^ ((p - 1) * p ^ k) - 1)) < v (algebraMap O C x) := by
        intro b hb
        calc v (algebraMap O C (b ^ ((p - 1) * p ^ k) - 1))
            ≤ v (algebraMap O C ((p : O) ^ (k + 1))) := hv.le_of_dvd hb
          _ = v (p : C) ^ (k + 1) := by rw [map_pow, map_natCast, map_pow]
          _ ≤ v (p : C) ^ k := pow_le_pow_of_le_one (by positivity) vp.le (by omega)
          _ < _ := hk
      have hor : v (algebraMap O C (σ β)) = 1 ∨ v (algebraMap O C (σ γ)) = 1 := by
        by_contra hc
        push_neg at hc
        have h1 : v (algebraMap O C (σ β)) < 1 := lt_of_le_of_ne (hv.map_le_one _) hc.1
        have h2 : v (algebraMap O C (σ γ)) < 1 := lt_of_le_of_ne (hv.map_le_one _) hc.2
        have h3 : v (algebraMap O C (σ β + σ γ)) < 1 := by
          rw [map_add]
          exact Valuation.map_add_lt v h1 h2
        rw [hsum, map_natCast, vcop t hpt] at h3
        exact lt_irrefl _ h3
      rcases hor with h | h
      · refine ⟨β ^ ((p - 1) * p ^ k), ?_, ?_⟩
        · rw [map_pow, hβ, ← mul_pow, hn, Nat.cast_pow]
        · rw [map_pow]
          exact close _ (key _ _ hbg hsum h k)
      · refine ⟨γ ^ ((p - 1) * p ^ k), ?_, ?_⟩
        · rw [map_pow, hγ, ← mul_pow, mul_comm β γ, hn, Nat.cast_pow]
        · rw [map_pow]
          exact close _ (key _ _ (by rw [mul_comm]; exact hbg) (by rw [add_comm]; exact hsum) h k)
