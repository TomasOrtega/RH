import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsResQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.BarFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Introduce `hxm`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hn`. Use `set u := Units.mk0 x hx0 with hu_def`.

Establish `hu : u ^ 2 ^ n = 1` using `Units.ext (by simpa [u] using hn)`. Establish `hum : u ^ m = 1` using `Units.ext (by simpa [u] using hxm)`. Take `⟨j, -, hoj⟩` from `(Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hu)`. Establish `hdm : (orderOf u : ℤ) ∣ m` using `orderOf_dvd_iff_zpow_eq_one.mpr hum`. Consider the cases of `j with`.

Consider the case `zero`. Rewrite `hoj` using `[pow_zero, orderOf_eq_one_iff]`. Apply `h4` to reduce the goal to its premises. Establish `hx1 : x = 1` using `by simpa [u] using congrArg Units.val hoj`. Simplify using `[hx1]`.

Consider the case `succ j`. Establish `h2 : (2 : ℤ) ∣ m`. Use `dvd_trans ?_ hdm` and prove the remaining obligations. Rewrite using `[hoj]`. Conclude with `dvd_pow_self 2 (Nat.succ_ne_zero j)` after adjusting the coercions.

Conclude with `(Int.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2)`.
-/
private theorem odd_pow_ne {k : Type} [Field k] {x : k} {n : ℕ} (hn : x ^ 2 ^ n = 1) (h4 : x ^ 4 ≠ 1) {m : ℤ} (hm : Odd m) :
    x ^ m ≠ 1 := by
  intro hxm
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hn
  set u := Units.mk0 x hx0 with hu_def
  have hu : u ^ 2 ^ n = 1 := Units.ext (by simpa [u] using hn)
  have hum : u ^ m = 1 := Units.ext (by simpa [u] using hxm)
  obtain ⟨j, -, hoj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hu)
  have hdm : (orderOf u : ℤ) ∣ m := orderOf_dvd_iff_zpow_eq_one.mpr hum
  cases j with
  | zero =>
    rw [pow_zero, orderOf_eq_one_iff] at hoj
    apply h4
    have hx1 : x = 1 := by simpa [u] using congrArg Units.val hoj
    simp [hx1]
  | succ j =>
    have h2 : (2 : ℤ) ∣ m := by
      refine dvd_trans ?_ hdm
      rw [hoj]
      exact_mod_cast dvd_pow_self 2 (Nat.succ_ne_zero j)
    exact (Int.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2)

/- English proof (translation)
Establish `h2 : (2 : k) ≠ 0`. Introduce `h`. Apply `h1` to reduce the goal to its premises. Take the linear combination `-h`. Introduce `i j h`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp at h ⊢`. Apply the tactic sequence `all_goals first`. Consider the case `exact absurd (by linear_combination h * h) hx`. Consider the case `exact absurd (by linear_combination (-x - 1) * h) hx`. Consider the case `exact absurd (by linear_combination (x - 1) * h) hx`.

Consider the case `exact absurd (by linear_combination (-x + 1) * h) hx`. Consider the case `exact absurd (by linear_combination (x + 1) * h) hx`. Consider the case `exact h1 h`. Consider the case `exact h1 h.symm`. Consider the case `exact h0 ((mul_eq_zero.mp (by linear_combination -h : (2 : k) * x = 0)).resolve_left h2)`.

Consider the case `exact h0 ((mul_eq_zero.mp (by linear_combination h : (2 : k) * x = 0)).resolve_left h2)`.
-/
private theorem dist4 {k : Type} [Field k] {x : k} (h1 : (-1 : k) ≠ 1) (h0 : x ≠ 0) (hx : x ^ 2 ≠ 1) :
    Function.Injective (![x * -1, -1, x, 1] : Fin 4 → k) := by
  have h2 : (2 : k) ≠ 0 := by
    intro h
    apply h1
    linear_combination -h
  intro i j h
  fin_cases i <;> fin_cases j <;> simp at h ⊢
  all_goals first
    | exact absurd (by linear_combination h * h) hx
    | exact absurd (by linear_combination (-x - 1) * h) hx
    | exact absurd (by linear_combination (x - 1) * h) hx
    | exact absurd (by linear_combination (-x + 1) * h) hx
    | exact absurd (by linear_combination (x + 1) * h) hx
    | exact h1 h
    | exact h1 h.symm
    | exact h0 ((mul_eq_zero.mp (by linear_combination -h : (2 : k) * x = 0)).resolve_left h2)
    | exact h0 ((mul_eq_zero.mp (by linear_combination h : (2 : k) * x = 0)).resolve_left h2)

/- English proof (translation)
Apply the tactic sequence `cases pr <;> decide`.
-/
private theorem lab_inj (pr : Bool) : Function.Injective (lab pr) := by
  cases pr <;> decide

/- English proof (translation)
Apply the tactic sequence `cases pr <;> decide`.
-/
private theorem lab_surj (pr : Bool) : ∃ i, lab pr i = 3 := by
  cases pr <;> decide

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D hD X T hOn a u t hE`. Take `⟨h1, -, hal, hth, -, -, hrb, -, -⟩` from `barFacts D hD`. Take `⟨n, hn⟩` from `X.ord`. Establish `hxord : ∀ g, Raw.bar D.ξ g ^ 2 ^ n = 1`. Introduce `g`.

Simplify using `only [Raw.bar]`. Rewrite using `[← map_pow, ← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hn]`. Simplify using the standard rewrite rules. Establish `hchi : ∀ b i, chi D b i = D.ps (lab b i)` using `fun b i => rfl`. Establish `lift : ∀ y ∈ X.H ⊓ X.η.ker, ∃ s ∈ T.GalL, resQ T.F s = y`.

Introduce `y hy`. Take `⟨s, hs⟩` from `exists_resQ (F := T.F) (g := y) (by rw [hOn.1]; exact hy.1)`. Use `⟨s, ?_, hs⟩` and prove the remaining obligations. Unfold `Tower.GalL`. Rewrite using `[Subgroup.mem_comap, hOn.2, hs]`.

Conclude with `hy.2`. Establish `hbu : Raw.bar D.om u = 1` using `by simp [Raw.bar, hE.u_om]`. Establish `hxu1 : Raw.bar D.ξ u ≠ 1`. Introduce `h`. Apply `hE.u_xi` to reduce the goal to its premises.

Rewrite using `[h, one_pow]`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `w`. Break down `Int.even_or_odd w.1 with he | ho` into its components or cases. Take `⟨s, hsG, hs⟩` from `lift a hE.a_mem`.

Use `⟨s, hsG, ?_⟩` and prove the remaining obligations. Rewrite using `[hrb, hs, hE.a_xi, hE.a_psi, hE.a_om, one_zpow, mul_one, he.neg_one_zpow]`. Conclude with `fun h => h1 h.symm`. Take `⟨s, hsG, hs⟩` from `lift u hE.u_mem`. Use `⟨s, hsG, ?_⟩` and prove the remaining obligations.

Rewrite using `[hrb, hs, hE.u_psi, one_zpow, mul_one, hbu]`. Conclude with `odd_pow_ne (hxord u) hE.u_xi ho`. Introduce `w hw`. Distinguish the cases in `ho : Odd w.1`. Take `⟨s, hsG, hs⟩` from `lift u hE.u_mem`.

Use `⟨s, hsG, ?_⟩` and prove the remaining obligations. Rewrite using `[hrb, hs, hE.u_psi, one_zpow, mul_one]`. Conclude with `odd_pow_ne (hxord u) hE.u_xi ho`. Take `⟨w1, w2⟩` from `w`. Simplify using `[UpperTheory.V.Ws.roots, oddRoots, wAl, wBe, wTh, wPs] at hw`.

Take `⟨s, hsG, hs⟩` from `lift t hE.t_mem`. Use `⟨s, hsG, ?_⟩` and prove the remaining obligations. Rewrite using `[hrb, hs, hE.t_psi]`. Break down `hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩` into its components or cases. Apply the tactic sequence `all_goals first`.

Consider the case `exact absurd (by decide) ho`. Consider the case `(split_ifs <;> simpa using h1)`. Introduce `η hη2 hηom hperm`. Take `⟨i0, hi0⟩` from `lab_surj T.pr`. Take `⟨j, hj⟩` from `hperm i0`.

Establish `key : ∀ s : T.GalL, (η s : ResidueField c.O) = Raw.bar (D.ps (lab T.pr j)) (resQ T.F s)`. Introduce `s`. Establish `h` using `hj s`. Rewrite `h` using `[hchi, hchi, hi0]`. Establish `h3 : D.ps 3 = 1` using `rfl`.

Rewrite `h` using `[h3]`. Simplify `h` using `[Raw.bar]`. Take `⟨su, hsuG, hsu⟩` from `lift u hE.u_mem`. Take `⟨st, hstG, hst⟩` from `lift t hE.t_mem`. Establish `hηu : η ⟨su, hsuG⟩ = 1` using `hηom _ (by simp only [hsu]; exact hE.u_om)`.

Establish `hηt : η ⟨st, hstG⟩ = 1` using `hηom _ (by simp only [hst]; exact hE.t_om)`. Establish `ku` using `key ⟨su, hsuG⟩`. Establish `kt` using `key ⟨st, hstG⟩`. Rewrite `ku` using `[hηu]`. Rewrite `kt` using `[hηt]`.

Simplify using `only [hsu] at ku`. Simplify using `only [hst] at kt`. Generalize the expression as in `lab T.pr j = k at ku kt key`. Use `fin_cases k`. It suffices to derive a contradiction.

Express the relevant statement in the definitionally equal form `_ = Raw.bar D.th u at ku`. Simplify using `only [hth, hE.u_psi, mul_one, Units.val_one] at ku`. Conclude with `hxu1 ku.symm`. It suffices to derive a contradiction. Express the relevant statement in the definitionally equal form `_ = Raw.bar D.Psi t at kt`.

Simplify using `only [hE.t_psi, Units.val_one] at kt`. Conclude with `h1 kt.symm`. It suffices to derive a contradiction. Express the relevant statement in the definitionally equal form `_ = Raw.bar D.al u at ku`. Simplify using `only [hal, Units.val_one] at ku`.

Conclude with `hxu1 ku.symm`. Use extensionality with `s`. Establish `h0 : D.ps 3 = 1` using `rfl`. Use `key s` as an intermediate fact. Simplify using `only [Fin.reduceFinMk, Fin.isValue] at this`.

Rewrite `this` using `[h0]`. Simplify `this` using `[Raw.bar]`. Use `⟨(1, 0), by simp [UpperTheory.V.Ws.roots, oddRoots, wAl], fun m hm0 hm4 => ?_⟩` and prove the remaining obligations. Take `⟨s, hsG, hs⟩` from `lift u hE.u_mem`. Use `⟨s, hsG, ?_⟩` and prove the remaining obligations.

Rewrite using `[hrb, hs, hE.u_psi]`. Simplify using `only [one_zpow, mul_one, zpow_one]`. Use `interval_cases m`. Simplify using `using hxu1`. Introduce `h`.

Apply `hE.u_xi` to reduce the goal to its premises. Rewrite using `[show 4 = 2 * 2 by rfl, pow_mul, h, one_pow]`. Establish `h3` using `odd_pow_ne (hxord u) hE.u_xi (m := 3) (by decide)`. Simplify using `using h3`. Conclude with `hE.u_xi`.

Introduce `hg0 i j hij heq`. Rewrite `heq` using `[hg0]`. Establish `hx0 : Raw.bar D.ξ t ≠ 0`. Introduce `h0`. Establish `h` using `hxord t`.

Rewrite `h` using `[h0, zero_pow (by positivity)]`. Conclude with `zero_ne_one h`. Establish `hinj` using `dist4 h1 hx0 hE.t_xi`. Establish `hvals : ∀ k, Raw.bar (D.ps k) t = ![Raw.bar D.ξ t * -1, -1, Raw.bar D.ξ t, 1] k`. Introduce `k`.

Use `fin_cases k`. Use `show Raw.bar D.th t = _`. Simplify using `[hth, hE.t_psi]`. Use `show Raw.bar D.Psi t = _`. Simplify using `[hE.t_psi]`.

Use `show Raw.bar D.al t = _`. Simplify using `[hal]`. Use `show Raw.bar (1 : G ℚ Ω →* (↥c.O)ˣ) t = _`. Simplify using `[Raw.bar]`. Rewrite `heq` using `[hchi, hchi, hvals, hvals]`.

Conclude with `hij (lab_inj T.pr (hinj heq))`.
-/
theorem UpperTheory.V.Ws.ok2A :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (X : Set2 D) (T : Tower D), X.On T → ∀ a u t, X.Elts a u t → (∀ w, ∃ g ∈ T.GalL, T.rb w g ≠ Raw.bar D.om (resQ T.F g)) ∧ (∀ w ∈ roots, ∃ g ∈ T.GalL, T.rb w g ≠ 1) ∧ (∀ η : T.GalL →* (ResidueField c.O)ˣ, η ^ 2 = 1 → (∀ g : T.GalL, D.om (resQ T.F g) = 1 → η g = 1) → (∀ i, ∃ j, ∀ g : T.GalL, η g * Raw.bar (chi D T.pr i) (resQ T.F g) = Raw.bar (chi D T.pr j) (resQ T.F g)) → η = 1) ∧ (∃ w ∈ roots, ∀ n : ℕ, 0 < n → n ≤ 4 → ∃ g ∈ T.GalL, T.rb w g ^ n ≠ 1) ∧ (resQ T.F T.g0 = t → ∀ i j, i ≠ j → Raw.bar (chi D T.pr i) (resQ T.F T.g0) ≠ Raw.bar (chi D T.pr j) (resQ T.F T.g0)) := by
  intro Ω _ _ _ l _ c D hD X T hOn a u t hE
  obtain ⟨h1, -, hal, hth, -, -, hrb, -, -⟩ := barFacts D hD
  obtain ⟨n, hn⟩ := X.ord
  have hxord : ∀ g, Raw.bar D.ξ g ^ 2 ^ n = 1 := by
    intro g
    simp only [Raw.bar]
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hn]
    simp
  have hchi : ∀ b i, chi D b i = D.ps (lab b i) := fun b i => rfl
  have lift : ∀ y ∈ X.H ⊓ X.η.ker, ∃ s ∈ T.GalL, resQ T.F s = y := by
    intro y hy
    obtain ⟨s, hs⟩ := exists_resQ (F := T.F) (g := y) (by rw [hOn.1]; exact hy.1)
    refine ⟨s, ?_, hs⟩
    unfold Tower.GalL
    rw [Subgroup.mem_comap, hOn.2, hs]
    exact hy.2
  have hbu : Raw.bar D.om u = 1 := by simp [Raw.bar, hE.u_om]
  have hxu1 : Raw.bar D.ξ u ≠ 1 := by
    intro h
    apply hE.u_xi
    rw [h, one_pow]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w
    rcases Int.even_or_odd w.1 with he | ho
    · obtain ⟨s, hsG, hs⟩ := lift a hE.a_mem
      refine ⟨s, hsG, ?_⟩
      rw [hrb, hs, hE.a_xi, hE.a_psi, hE.a_om, one_zpow, mul_one, he.neg_one_zpow]
      exact fun h => h1 h.symm
    · obtain ⟨s, hsG, hs⟩ := lift u hE.u_mem
      refine ⟨s, hsG, ?_⟩
      rw [hrb, hs, hE.u_psi, one_zpow, mul_one, hbu]
      exact odd_pow_ne (hxord u) hE.u_xi ho
  · intro w hw
    by_cases ho : Odd w.1
    · obtain ⟨s, hsG, hs⟩ := lift u hE.u_mem
      refine ⟨s, hsG, ?_⟩
      rw [hrb, hs, hE.u_psi, one_zpow, mul_one]
      exact odd_pow_ne (hxord u) hE.u_xi ho
    · obtain ⟨w1, w2⟩ := w
      simp [UpperTheory.V.Ws.roots, oddRoots, wAl, wBe, wTh, wPs] at hw
      obtain ⟨s, hsG, hs⟩ := lift t hE.t_mem
      refine ⟨s, hsG, ?_⟩
      rw [hrb, hs, hE.t_psi]
      rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals first
        | exact absurd (by decide) ho
        | (split_ifs <;> simpa using h1)
  · intro η hη2 hηom hperm
    obtain ⟨i0, hi0⟩ := lab_surj T.pr
    obtain ⟨j, hj⟩ := hperm i0
    have key : ∀ s : T.GalL, (η s : ResidueField c.O) = Raw.bar (D.ps (lab T.pr j)) (resQ T.F s) := by
      intro s
      have h := hj s
      rw [hchi, hchi, hi0] at h
      have h3 : D.ps 3 = 1 := rfl
      rw [h3] at h
      simpa [Raw.bar] using h
    obtain ⟨su, hsuG, hsu⟩ := lift u hE.u_mem
    obtain ⟨st, hstG, hst⟩ := lift t hE.t_mem
    have hηu : η ⟨su, hsuG⟩ = 1 := hηom _ (by simp only [hsu]; exact hE.u_om)
    have hηt : η ⟨st, hstG⟩ = 1 := hηom _ (by simp only [hst]; exact hE.t_om)
    have ku := key ⟨su, hsuG⟩
    have kt := key ⟨st, hstG⟩
    rw [hηu] at ku
    rw [hηt] at kt
    simp only [hsu] at ku
    simp only [hst] at kt
    generalize lab T.pr j = k at ku kt key
    fin_cases k
    · exfalso
      change _ = Raw.bar D.th u at ku
      simp only [hth, hE.u_psi, mul_one, Units.val_one] at ku
      exact hxu1 ku.symm
    · exfalso
      change _ = Raw.bar D.Psi t at kt
      simp only [hE.t_psi, Units.val_one] at kt
      exact h1 kt.symm
    · exfalso
      change _ = Raw.bar D.al u at ku
      simp only [hal, Units.val_one] at ku
      exact hxu1 ku.symm
    · ext s
      have h0 : D.ps 3 = 1 := rfl
      have := key s
      simp only [Fin.reduceFinMk, Fin.isValue] at this
      rw [h0] at this
      simpa [Raw.bar] using this
  · refine ⟨(1, 0), by simp [UpperTheory.V.Ws.roots, oddRoots, wAl], fun m hm0 hm4 => ?_⟩
    obtain ⟨s, hsG, hs⟩ := lift u hE.u_mem
    refine ⟨s, hsG, ?_⟩
    rw [hrb, hs, hE.u_psi]
    simp only [one_zpow, mul_one, zpow_one]
    interval_cases m
    · simpa using hxu1
    · intro h
      apply hE.u_xi
      rw [show 4 = 2 * 2 by rfl, pow_mul, h, one_pow]
    · have h3 := odd_pow_ne (hxord u) hE.u_xi (m := 3) (by decide)
      simpa using h3
    · exact hE.u_xi
  · intro hg0 i j hij heq
    rw [hg0] at heq
    have hx0 : Raw.bar D.ξ t ≠ 0 := by
      intro h0
      have h := hxord t
      rw [h0, zero_pow (by positivity)] at h
      exact zero_ne_one h
    have hinj := dist4 h1 hx0 hE.t_xi
    have hvals : ∀ k, Raw.bar (D.ps k) t = ![Raw.bar D.ξ t * -1, -1, Raw.bar D.ξ t, 1] k := by
      intro k
      fin_cases k
      · show Raw.bar D.th t = _
        simp [hth, hE.t_psi]
      · show Raw.bar D.Psi t = _
        simp [hE.t_psi]
      · show Raw.bar D.al t = _
        simp [hal]
      · show Raw.bar (1 : G ℚ Ω →* (↥c.O)ˣ) t = _
        simp [Raw.bar]
    rw [hchi, hchi, hvals, hvals] at heq
    exact hij (lab_inj T.pr (hinj heq))
