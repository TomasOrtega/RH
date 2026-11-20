import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KerPow
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro g _`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `g hg`.

Rewrite `hg` using `[pow_succ]`. Use `Submodule.mul_induction_on hg (fun a ha b hb => ?_) ?_` and prove the remaining obligations. Rewrite `hb` using `[RingHom.mem_ker]`. Rewrite using `[map_mul]`. Use `le_trans ?_ MvPowerSeries.le_order_mul` and prove the remaining obligations.

Use `push_cast`. Use `add_le_add (ih a ha) (MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.2 ?_)` and prove the remaining obligations. Rewrite using `[hc, hb, map_zero]`. Introduce `a b ha hb`. Rewrite using `[map_add]`.

Conclude with `le_trans (le_min ha hb) MvPowerSeries.min_order_le_add`.
-/
private lemma order_pow {O A K τ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing K] [Algebra O K]
    (x : A →ₐ[O] O) (φ : A →ₐ[O] MvPowerSeries τ K)
    (hc : ∀ f, MvPowerSeries.constantCoeff (φ f) = algebraMap O K (x f)) (n : ℕ) :
    ∀ g ∈ RingHom.ker x ^ n, (n : ℕ∞) ≤ (φ g).order := by
  induction n with
  | zero => intro g _; simp
  | succ n ih =>
    intro g hg
    rw [pow_succ] at hg
    refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) ?_
    · rw [RingHom.mem_ker] at hb
      rw [map_mul]
      refine le_trans ?_ MvPowerSeries.le_order_mul
      push_cast
      refine add_le_add (ih a ha) (MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.2 ?_)
      rw [hc, hb, map_zero]
    · intro a b ha hb
      rw [map_add]
      exact le_trans (le_min ha hb) MvPowerSeries.min_order_le_add

/- English proof (translation)
Use `choose a ha using ha`. Set `ψ : R → MvPowerSeries τ K` to `fun x m => MvPowerSeries.coeff m (φ (a (m.degree + 1) x))`. Establish `spec : ∀ (n : ℕ) (x : R) (y : A), x - y ∈ q ^ n → ∀ m : τ →₀ ℕ, m.degree < n → MvPowerSeries.coeff m (ψ x) = MvPowerSeries.coeff m (φ y)`. Introduce `n x y hy m hm`. Use `show MvPowerSeries.coeff m (φ (a (m.degree + 1) x)) = _`.

Establish `h1 : x - y ∈ q ^ (m.degree + 1)` using `Ideal.pow_le_pow_right hm hy`. Establish `h2 : ((a (m.degree + 1) x - y : A) : R) ∈ q ^ (m.degree + 1)`. Use `Ideal.sub_mem _ h1 (ha (m.degree + 1) x)` as an intermediate fact. Rewrite `this` using `[sub_sub_sub_cancel_left]`. Conclude with `this`.

Establish `h3 : MvPowerSeries.coeff m (φ (a (m.degree + 1) x - y)) = 0`. Use `MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le ?_ (ho _ _ h2))` and prove the remaining obligations. Conclude with `Nat.lt_succ_self _` after adjusting the coercions. Rewrite `h3` using `[map_sub, map_sub, sub_eq_zero]`. Then use the resulting hypothesis. Establish `onA : ∀ y : A, ψ y = φ y` using `fun y => by`.

Use extensionality with `m`. Conclude with `spec (m.degree + 1) y y (by simp) m (Nat.lt_succ_self _)`. Establish `hadd : ∀ x x', ψ (x + x') = ψ x + ψ x'` using `fun x x' => by`. Use extensionality with `m`. Establish `hm` using `Nat.lt_succ_self m.degree`.

Rewrite using `[map_add, spec _ x _ (ha _ x) m hm, spec _ x' _ (ha _ x') m hm, ← map_add, ← map_add]`. Use `spec _ _ _ ?_ m hm` and prove the remaining obligations. Use `Ideal.add_mem _ (ha (m.degree + 1) x) (ha (m.degree + 1) x')` as an intermediate fact. Rewrite `this` using `[sub_add_sub_comm]`. Conclude with `this`.

Establish `hmul : ∀ x x', ψ (x * x') = ψ x * ψ x'` using `fun x x' => by`. Use extensionality with `m`. Establish `hm` using `Nat.lt_succ_self m.degree`. Establish `h1 : x * x' - ((a (m.degree + 1) x * a (m.degree + 1) x' : A) : R) ∈ q ^ (m.degree + 1)`. Use `Ideal.add_mem _ (Ideal.mul_mem_right x' _ (ha (m.degree + 1) x)) (Ideal.mul_mem_left _ (a (m.degree + 1) x : R) (ha (m.degree + 1) x'))` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[spec _ _ _ h1 m hm, map_mul, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]`. Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations.

Establish `h2 : p.1.degree + p.2.degree = m.degree`. Rewrite using `[← Finset.HasAntidiagonal.mem_antidiagonal.1 hp, map_add]`. Rewrite using `[spec _ x _ (ha (m.degree + 1) x) p.1 (by omega), spec _ x' _ (ha (m.degree + 1) x') p.2 (by omega)]`. Use `⟨{ toFun := ψ map_one' := (onA 1).trans (map_one φ) map_mul' := hmul map_zero' := (onA 0).trans (map_zero φ) map_add' := hadd commutes' := fun c => (onA (algebraMap O A c)).trans (φ.commutes c) }, spec⟩` and prove the remaining obligations.
-/
private lemma extend {O R K τ : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing K] [Algebra O K]
    (A : Subalgebra O R) (q : Ideal R) (φ : A →ₐ[O] MvPowerSeries τ K)
    (ho : ∀ (n : ℕ) (y : A), (y : R) ∈ q ^ n → (n : ℕ∞) ≤ (φ y).order)
    (ha : ∀ (n : ℕ) (x : R), ∃ y : A, x - y ∈ q ^ n) :
    ∃ ψ : R →ₐ[O] MvPowerSeries τ K, ∀ (n : ℕ) (x : R) (y : A), x - y ∈ q ^ n → ∀ m : τ →₀ ℕ, m.degree < n →
      MvPowerSeries.coeff m (ψ x) = MvPowerSeries.coeff m (φ y) := by
  classical
  choose a ha using ha
  let ψ : R → MvPowerSeries τ K := fun x m => MvPowerSeries.coeff m (φ (a (m.degree + 1) x))
  have spec : ∀ (n : ℕ) (x : R) (y : A), x - y ∈ q ^ n → ∀ m : τ →₀ ℕ, m.degree < n →
      MvPowerSeries.coeff m (ψ x) = MvPowerSeries.coeff m (φ y) := by
    intro n x y hy m hm
    show MvPowerSeries.coeff m (φ (a (m.degree + 1) x)) = _
    have h1 : x - y ∈ q ^ (m.degree + 1) := Ideal.pow_le_pow_right hm hy
    have h2 : ((a (m.degree + 1) x - y : A) : R) ∈ q ^ (m.degree + 1) := by
      have := Ideal.sub_mem _ h1 (ha (m.degree + 1) x)
      rw [sub_sub_sub_cancel_left] at this
      exact this
    have h3 : MvPowerSeries.coeff m (φ (a (m.degree + 1) x - y)) = 0 := by
      refine MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le ?_ (ho _ _ h2))
      exact_mod_cast Nat.lt_succ_self _
    rwa [map_sub, map_sub, sub_eq_zero] at h3
  have onA : ∀ y : A, ψ y = φ y := fun y => by
    ext m
    exact spec (m.degree + 1) y y (by simp) m (Nat.lt_succ_self _)
  have hadd : ∀ x x', ψ (x + x') = ψ x + ψ x' := fun x x' => by
    ext m
    have hm := Nat.lt_succ_self m.degree
    rw [map_add, spec _ x _ (ha _ x) m hm, spec _ x' _ (ha _ x') m hm, ← map_add, ← map_add]
    refine spec _ _ _ ?_ m hm
    have := Ideal.add_mem _ (ha (m.degree + 1) x) (ha (m.degree + 1) x')
    rw [sub_add_sub_comm] at this
    exact this
  have hmul : ∀ x x', ψ (x * x') = ψ x * ψ x' := fun x x' => by
    ext m
    have hm := Nat.lt_succ_self m.degree
    have h1 : x * x' - ((a (m.degree + 1) x * a (m.degree + 1) x' : A) : R) ∈ q ^ (m.degree + 1) := by
      have := Ideal.add_mem _ (Ideal.mul_mem_right x' _ (ha (m.degree + 1) x))
        (Ideal.mul_mem_left _ (a (m.degree + 1) x : R) (ha (m.degree + 1) x'))
      convert this using 1
      push_cast
      ring
    rw [spec _ _ _ h1 m hm, map_mul, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have h2 : p.1.degree + p.2.degree = m.degree := by
      rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hp, map_add]
    rw [spec _ x _ (ha (m.degree + 1) x) p.1 (by omega), spec _ x' _ (ha (m.degree + 1) x') p.2 (by omega)]
  refine ⟨{ toFun := ψ
            map_one' := (onA 1).trans (map_one φ)
            map_mul' := hmul
            map_zero' := (onA 0).trans (map_zero φ)
            map_add' := hadd
            commutes' := fun c => (onA (algebraMap O A c)).trans (φ.commutes c) }, spec⟩

/- English proof (translation)
Introduce and unpack `O X R _ _ _ _ _ _ _ _ W h n ⟨τ, fτ, wt, φ, H, hn⟩`. Take `⟨ψ, spec⟩` from `extend W.A (RingHom.ker (W.origin h)) φ (fun k y hy => order_pow (W.originA h) φ H.const k y (by`. Rewrite using `[← (ker_pow O R X W h k).1]`. Conclude with `hy))`. Use the proof step `(fun k => (ker_pow O R X W h k).2)`.

Establish `onA : ∀ y : W.A, ψ y = φ y` using `fun y => by`. Use extensionality with `m`. Conclude with `spec (m.degree + 1) y y (by simp) m (Nat.lt_succ_self _)`. Take `⟨h1, h2⟩` from `ker_pow O R X W h 2`. Establish `hx : ∀ (f : R) (y : W.A), f - y ∈ RingHom.ker (W.origin h) ^ 2 → W.origin h f = W.originA h y`.

Introduce `f y hy`. Use `Ideal.pow_le_self (two_ne_zero) hy` as an intermediate fact. Rewrite `this` using `[RingHom.mem_ker, map_sub, sub_eq_zero]`. Conclude with `this`. Use `⟨τ, fτ, wt, ψ, ⟨fun j f hf => ?_, fun f => ?_, fun i => ?_, fun f hf hl => ?_⟩, hn⟩` and prove the remaining obligations.

Use `H.graded j ⟨f, W.part_le_A hf⟩ hf` as an intermediate fact. Rewrite `this` using `[← onA]`. Conclude with `this`. Take `⟨y, hy⟩` from `h2 f`. Rewrite using `[hx f y hy, ← H.const, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]`.

Conclude with `spec 2 f y hy 0 (by simp)`. Take `⟨f, hf, hf'⟩` from `H.onto i`. Rewrite `hf`, `hf'` using `[← onA]`. Conclude with `⟨f, hf, hf'⟩`. Take `⟨y, hy⟩` from `h2 f`.

Take `⟨c, hc, hcy⟩` from `H.inj y ((hx f y hy).symm.trans hf) (fun i => by`. Rewrite using `[← spec 2 f y hy _ (by rw [Finsupp.degree_single]; norm_num)]`. Conclude with `hl i)`. Rewrite `hcy` using `[← h1]`. Establish `h3 : c • (y : R) ∈ RingHom.ker (W.origin h) ^ 2` using `hcy`.

Use `⟨c, hc, ?_⟩` and prove the remaining obligations. Establish `h4` using `Ideal.add_mem _ (Submodule.smul_of_tower_mem _ c hy) h3`. Rewrite `h4` using `[← smul_add, sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.smoothPt_part_of_smoothPt_associatedGraded :
    ∀ (O X R : Type) [CommRing O] [IsDomain O] [AddCommGroup X] [DecidableEq X] [Module.Free ℤ X] [Module.Finite ℤ X] [CommRing R] [Algebra O R] (W : WPres O X R) (h : W.HasOrigin) (n : X → ℕ), SmoothPt W.gr (W.originA h) n → SmoothPt W.part (W.origin h) n := by
  rintro O X R _ _ _ _ _ _ _ _ W h n ⟨τ, fτ, wt, φ, H, hn⟩
  obtain ⟨ψ, spec⟩ := extend W.A (RingHom.ker (W.origin h)) φ
    (fun k y hy => order_pow (W.originA h) φ H.const k y (by
      rw [← (ker_pow O R X W h k).1]
      exact hy))
    (fun k => (ker_pow O R X W h k).2)
  have onA : ∀ y : W.A, ψ y = φ y := fun y => by
    ext m
    exact spec (m.degree + 1) y y (by simp) m (Nat.lt_succ_self _)
  obtain ⟨h1, h2⟩ := ker_pow O R X W h 2
  have hx : ∀ (f : R) (y : W.A), f - y ∈ RingHom.ker (W.origin h) ^ 2 → W.origin h f = W.originA h y := by
    intro f y hy
    have := Ideal.pow_le_self (two_ne_zero) hy
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
    exact this
  refine ⟨τ, fτ, wt, ψ, ⟨fun j f hf => ?_, fun f => ?_, fun i => ?_, fun f hf hl => ?_⟩, hn⟩
  · have := H.graded j ⟨f, W.part_le_A hf⟩ hf
    rw [← onA] at this
    exact this
  · obtain ⟨y, hy⟩ := h2 f
    rw [hx f y hy, ← H.const, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact spec 2 f y hy 0 (by simp)
  · obtain ⟨f, hf, hf'⟩ := H.onto i
    rw [← onA] at hf hf'
    exact ⟨f, hf, hf'⟩
  · obtain ⟨y, hy⟩ := h2 f
    obtain ⟨c, hc, hcy⟩ := H.inj y ((hx f y hy).symm.trans hf) (fun i => by
      rw [← spec 2 f y hy _ (by rw [Finsupp.degree_single]; norm_num)]
      exact hl i)
    rw [← h1] at hcy
    have h3 : c • (y : R) ∈ RingHom.ker (W.origin h) ^ 2 := hcy
    refine ⟨c, hc, ?_⟩
    have h4 := Ideal.add_mem _ (Submodule.smul_of_tower_mem _ c hy) h3
    rwa [← smul_add, sub_add_cancel] at h4
