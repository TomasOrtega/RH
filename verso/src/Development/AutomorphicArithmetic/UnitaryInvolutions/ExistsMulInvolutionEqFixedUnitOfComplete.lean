import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteInvolutionFixedUnitEqMulConj
open scoped Classical

/- English proof (translation)
Take the linear combination `(1 + P * (b + bb) + P ^ 2 * b * bb) * h1 + (u + P * a) * P * hb - P * a * hv`.
-/
private lemma normStep_algebra {T : Type} [CommRing T] (z zb u P a b bb v : T)
    (h1 : z * zb - u = P * a) (hb : b + bb = -(v * a)) (hv : v * u = 1) :
    z * (1 + P * b) * (zb * (1 + P * bb)) - u
      = P * P * (u * b * bb - v * a * a + P * a * b * bb) := by
  linear_combination (1 + P * (b + bb) + P ^ 2 * b * bb) * h1 + (u + P * a) * P * hb - P * a * hv

/- English proof (translation)
Take the linear combination `-Lb * h - (F - P * e) * hb + hf`.
-/
private lemma normLimit_algebra {T : Type} [CommRing T] (F Fb L Lb u P e eb c : T)
    (h : F - L = P * e) (hb : Fb - Lb = P * eb) (hf : F * Fb - u = P * c) :
    L * Lb - u = P * (c - e * Fb - F * eb + P * e * eb) := by
  linear_combination -Lb * h - (F - P * e) * hb + hf

/- English proof (translation)
Proceed by induction on `n generalizing x with`. Consider the case `zero => simpa using h`. Consider the case `succ n ih`. Apply `hreg` to reduce the goal to its premises. Apply `ih` to reduce the goal to its premises.

Rewrite using `[← mul_assoc, ← pow_succ]`. Conclude with `h`.
-/
private lemma pow_regular {T : Type} [CommRing T] (ϖ : T) (hreg : ∀ x : T, ϖ * x = 0 → x = 0)
    (n : ℕ) (x : T) (h : ϖ ^ n * x = 0) : x = 0 := by
  induction n generalizing x with
  | zero => simpa using h
  | succ n ih =>
    apply hreg
    apply ih
    rw [← mul_assoc, ← pow_succ]
    exact h

/- English proof (translation)
Establish `hle : Ideal.span {ϖ} ≤ (Ideal.span {ϖ}).comap ι`. Rewrite using `[Ideal.span_le]`. Introduce `x hx`. Establish `hx' : x = ϖ` using `hx`. Substitute `hx'` using the available equality.

Express the relevant statement in the definitionally equal form `ι x ∈ Ideal.span {x}`. Rewrite using `[hϖ]`. Conclude with `Ideal.mem_span_singleton_self x`. Set `c : (T ⧸ Ideal.span {ϖ}) →+* (T ⧸ Ideal.span {ϖ})` to `Ideal.quotientMap (Ideal.span {ϖ}) ι hle`. Establish `hc : ∀ x : T, c (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (ι x)` using `fun x => Ideal.quotientMap_mk`.

Establish `hinv : ∀ x, c (c x) = x`. Introduce `x`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite using `[hc, hc, hι]`. Establish `hunit : IsUnit ((Ideal.Quotient.mk (Ideal.span {ϖ}) ω) - c (Ideal.Quotient.mk _ ω))`.

Rewrite using `[hc, ← map_sub]`. Conclude with `hω.map _`. Take `⟨x, hx⟩` from `GlobalTheory.finite_involution_fixed_unit_isNorm (T ⧸ Ideal.span {ϖ}) c hinv ⟨_, hunit⟩ (Ideal.Quotient.mk _ u) (by rw [hc, hfix]) (hu.map _)`. Take `⟨z, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite `hx` using `[hc, ← map_mul]`.

Establish `hmem : z * ι z - u ∈ Ideal.span {ϖ}`. Rewrite using `[← Ideal.Quotient.eq]`. Conclude with `hx`. Take `⟨a, ha⟩` from `Ideal.mem_span_singleton.mp hmem`. Conclude with `⟨z, a, by simpa using ha⟩`.
-/
private lemma norm_level_zero (T : Type) [CommRing T] (ι : T →+* T) (ϖ ω : T)
    (hι : ∀ x, ι (ι x) = x) (hϖ : ι ϖ = ϖ) (hfin : Finite (T ⧸ Ideal.span {ϖ}))
    (hω : IsUnit (ω - ι ω)) (u : T) (hu : IsUnit u) (hfix : ι u = u) :
    ∃ z a, z * ι z - u = ϖ ^ (0 + 1) * a := by
  have hle : Ideal.span {ϖ} ≤ (Ideal.span {ϖ}).comap ι := by
    rw [Ideal.span_le]
    intro x hx
    have hx' : x = ϖ := hx
    subst hx'
    change ι x ∈ Ideal.span {x}
    rw [hϖ]
    exact Ideal.mem_span_singleton_self x
  let c : (T ⧸ Ideal.span {ϖ}) →+* (T ⧸ Ideal.span {ϖ}) :=
    Ideal.quotientMap (Ideal.span {ϖ}) ι hle
  have hc : ∀ x : T, c (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (ι x) := fun x =>
    Ideal.quotientMap_mk
  have hinv : ∀ x, c (c x) = x := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hc, hc, hι]
  have hunit : IsUnit ((Ideal.Quotient.mk (Ideal.span {ϖ}) ω) - c (Ideal.Quotient.mk _ ω)) := by
    rw [hc, ← map_sub]
    exact hω.map _
  obtain ⟨x, hx⟩ := GlobalTheory.finite_involution_fixed_unit_isNorm (T ⧸ Ideal.span {ϖ}) c hinv
    ⟨_, hunit⟩ (Ideal.Quotient.mk _ u) (by rw [hc, hfix]) (hu.map _)
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [hc, ← map_mul] at hx
  have hmem : z * ι z - u ∈ Ideal.span {ϖ} := by
    rw [← Ideal.Quotient.eq]
    exact hx
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hmem
  exact ⟨z, a, by simpa using ha⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `hz`. Establish `hιP : ι (ϖ ^ (j + 1)) = ϖ ^ (j + 1)` using `by rw [map_pow, hϖ]`. Establish `haι : ι a = a`. Establish `h2 : z * ι z - u = ϖ ^ (j + 1) * ι a`. Use `congrArg ι ha` as an intermediate fact.

Simplify using `only [map_sub, map_mul, hι, hfix, hιP] at this`. Rewrite using `[← this]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : ϖ ^ (j + 1) * (ι a - a) = 0`. Take the linear combination `ha - h2`.

Conclude with `sub_eq_zero.mp (pow_regular ϖ hreg _ _ h3)`. Take `⟨v, hv⟩` from `hu.exists_left_inv`. Take `⟨w, hw⟩` from `hω.exists_left_inv`. Establish `hιv : ι v = v`. Establish `h1 : ι v * u = 1`.

Use `congrArg ι hv` as an intermediate fact. Simplify `this` using `[hfix]`. Take the linear combination `v * h1 - ι v * hv`. Establish `hιw : ι w = -w`. Establish `h1 : ι w * (ι ω - ω) = 1`.

Use `congrArg ι hw` as an intermediate fact. Simplify `this` using `[hι]`. Take the linear combination `(-w) * h1 - ι w * hw`. Establish `hsum : ω * w + ι (ω * w) = 1`. Rewrite using `[map_mul, hιw]`.

Take the linear combination `hw`. Use `set b : T := -(ω * w * v * a) with hbdef`. Establish `hbsum : b + ι b = -(v * a)`. Establish `: ι b = -(ι (ω * w) * v * a)`. Rewrite using `[hbdef]`.

Simplify using `only [map_neg, map_mul, hιv, haι]`. Rewrite using `[this, hbdef]`. Take the linear combination `(-(v * a)) * hsum`. Use `⟨z * (1 + ϖ ^ (j + 1) * b), ⟨ϖ ^ j * (u * b * ι b - v * a * a + ϖ ^ (j + 1) * a * b * ι b), ?_⟩, ⟨z * b, by ring⟩⟩` and prove the remaining obligations. Establish `h` using `normStep_algebra z (ι z) u (ϖ ^ (j + 1)) a b (ι b) v ha hbsum hv`.

Establish `hι' : ι (z * (1 + ϖ ^ (j + 1) * b)) = ι z * (1 + ϖ ^ (j + 1) * ι b)`. Simplify using `only [map_mul, map_add, map_one, hιP]`. Rewrite using `[hι', h]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma norm_step (T : Type) [CommRing T] (ι : T →+* T) (ϖ ω : T)
    (hι : ∀ x, ι (ι x) = x) (hϖ : ι ϖ = ϖ) (hreg : ∀ x : T, ϖ * x = 0 → x = 0)
    (hω : IsUnit (ω - ι ω)) (u : T) (hu : IsUnit u) (hfix : ι u = u)
    (j : ℕ) (z : T) (hz : ∃ a, z * ι z - u = ϖ ^ (j + 1) * a) :
    ∃ z', (∃ a, z' * ι z' - u = ϖ ^ (j + 1 + 1) * a) ∧ ∃ e, z' - z = ϖ ^ (j + 1) * e := by
  obtain ⟨a, ha⟩ := hz
  have hιP : ι (ϖ ^ (j + 1)) = ϖ ^ (j + 1) := by rw [map_pow, hϖ]
  have haι : ι a = a := by
    have h2 : z * ι z - u = ϖ ^ (j + 1) * ι a := by
      have := congrArg ι ha
      simp only [map_sub, map_mul, hι, hfix, hιP] at this
      rw [← this]
      ring
    have h3 : ϖ ^ (j + 1) * (ι a - a) = 0 := by
      linear_combination ha - h2
    exact sub_eq_zero.mp (pow_regular ϖ hreg _ _ h3)
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  obtain ⟨w, hw⟩ := hω.exists_left_inv
  have hιv : ι v = v := by
    have h1 : ι v * u = 1 := by
      have := congrArg ι hv
      simpa [hfix] using this
    linear_combination v * h1 - ι v * hv
  have hιw : ι w = -w := by
    have h1 : ι w * (ι ω - ω) = 1 := by
      have := congrArg ι hw
      simpa [hι] using this
    linear_combination (-w) * h1 - ι w * hw
  have hsum : ω * w + ι (ω * w) = 1 := by
    rw [map_mul, hιw]
    linear_combination hw
  set b : T := -(ω * w * v * a) with hbdef
  have hbsum : b + ι b = -(v * a) := by
    have : ι b = -(ι (ω * w) * v * a) := by
      rw [hbdef]
      simp only [map_neg, map_mul, hιv, haι]
    rw [this, hbdef]
    linear_combination (-(v * a)) * hsum
  refine ⟨z * (1 + ϖ ^ (j + 1) * b), ⟨ϖ ^ j * (u * b * ι b - v * a * a +
    ϖ ^ (j + 1) * a * b * ι b), ?_⟩, ⟨z * b, by ring⟩⟩
  have h := normStep_algebra z (ι z) u (ϖ ^ (j + 1)) a b (ι b) v ha hbsum hv
  have hι' : ι (z * (1 + ϖ ^ (j + 1) * b)) = ι z * (1 + ϖ ^ (j + 1) * ι b) := by
    simp only [map_mul, map_add, map_one, hιP]
  rw [hι', h]
  ring

/- English proof (translation)
Introduce `T _ ι ϖ ω hι hϖ hreg hcomp hsep hfin hω u hu hfix`. Take `⟨z₀, hz₀⟩` from `norm_level_zero T ι ϖ ω hι hϖ hfin hω u hu hfix`. Establish `step` using `norm_step T ι ϖ ω hι hϖ hreg hω u hu hfix`. Set `g : (j : ℕ) → {z : T // ∃ a, z * ι z - u = ϖ ^ (j + 1) * a}` to `fun j => Nat.rec ⟨z₀, hz₀⟩ (fun j p => ⟨(step j p.1 p.2).choose, (step j p.1 p.2).choose_spec.1⟩) j`. Establish `hg : ∀ j, ∃ e, (g (j + 1)).1 - (g j).1 = ϖ ^ (j + 1) * e` using `fun j => (step j (g j).1 (g j).2).choose_spec.2`.

Take `⟨L, hL⟩` from `hcomp (fun j => (g j).1) (fun m => by`. Take `⟨e, he⟩` from `hg m`. Conclude with `⟨ϖ * e, by rw [he, pow_succ]; ring⟩)`. Use `⟨L, sub_eq_zero.mp (hsep _ fun m => ?_)⟩` and prove the remaining obligations. Take `⟨e, he⟩` from `hL m`.

Take `⟨a, ha⟩` from `(g m).2`. Establish `heι : ι (g m).1 - ι L = ϖ ^ m * ι e`. Use `congrArg ι he` as an intermediate fact. Simplify `this` using `[hϖ]`. Establish `hf : (g m).1 * ι (g m).1 - u = ϖ ^ m * (ϖ * a)`.

Rewrite using `[ha, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `⟨_, normLimit_algebra _ _ _ _ _ _ _ _ _ he heι hf⟩`.
-/
theorem UpperTheory.exists_mul_involution_eq_fixed_unit_of_complete :
    ∀ (T : Type) [CommRing T] (ι : T →+* T) (ϖ ω : T), (∀ x, ι (ι x) = x) → ι ϖ = ϖ →
        (∀ x : T, ϖ * x = 0 → x = 0) →
        (∀ f : ℕ → T, (∀ m, ∃ e, f (m + 1) - f m = ϖ ^ m * e) → ∃ L, ∀ m, ∃ e, f m - L = ϖ ^ m * e) →
        (∀ x : T, (∀ m : ℕ, ∃ e, x = ϖ ^ m * e) → x = 0) →
        Finite (T ⧸ Ideal.span {ϖ}) → IsUnit (ω - ι ω) →
        ∀ u : T, IsUnit u → ι u = u → ∃ z, z * ι z = u := by
  intro T _ ι ϖ ω hι hϖ hreg hcomp hsep hfin hω u hu hfix
  obtain ⟨z₀, hz₀⟩ := norm_level_zero T ι ϖ ω hι hϖ hfin hω u hu hfix
  have step := norm_step T ι ϖ ω hι hϖ hreg hω u hu hfix
  let g : (j : ℕ) → {z : T // ∃ a, z * ι z - u = ϖ ^ (j + 1) * a} := fun j =>
    Nat.rec ⟨z₀, hz₀⟩
      (fun j p => ⟨(step j p.1 p.2).choose, (step j p.1 p.2).choose_spec.1⟩) j
  have hg : ∀ j, ∃ e, (g (j + 1)).1 - (g j).1 = ϖ ^ (j + 1) * e := fun j =>
    (step j (g j).1 (g j).2).choose_spec.2
  obtain ⟨L, hL⟩ := hcomp (fun j => (g j).1) (fun m => by
    obtain ⟨e, he⟩ := hg m
    exact ⟨ϖ * e, by rw [he, pow_succ]; ring⟩)
  refine ⟨L, sub_eq_zero.mp (hsep _ fun m => ?_)⟩
  obtain ⟨e, he⟩ := hL m
  obtain ⟨a, ha⟩ := (g m).2
  have heι : ι (g m).1 - ι L = ϖ ^ m * ι e := by
    have := congrArg ι he
    simpa [hϖ] using this
  have hf : (g m).1 * ι (g m).1 - u = ϖ ^ m * (ϖ * a) := by
    rw [ha, pow_succ]
    ring
  exact ⟨_, normLimit_algebra _ _ _ _ _ _ _ _ _ he heι hf⟩
