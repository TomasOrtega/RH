import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IsFixMapIff

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Establish `s1 : (2 + (b + c)) * (2 + (d + e)) = 0`. Take the linear combination `E1 - (2 + (d + e) + (d * e - 1)) * hbc - (2 + (b + c)) * hde`. Establish `t2 : (1 - c) * (1 - b) * (1 - e) * (1 - d) = 0`. Take the linear combination `u ^ 4 * E2 - (1 - c) * (1 - b) * (1 - e) * (1 - d) * (w * u + 1) * (w ^ 2 * u ^ 2 + 1) * hwu`. Establish `s2 : (2 - (b + c)) * (2 - (d + e)) = 0`.

Take the linear combination `t2 - (2 - (d + e) + (d * e - 1)) * hbc - (2 - (b + c)) * hde`. Establish `s3 : (b + c) + (d + e) = 0`. Take the linear combination `v ^ 2 * (s1 - s2) - ((b + c) + (d + e)) * (2 * v + 1) * h2v`. Establish `s4 : (b + c) * (d + e) + 4 = 0`. Take the linear combination `v * (s1 + s2) - ((b + c) * (d + e) + 4) * h2v`.

Establish `t3 : (2 + (b + c) - w ^ 2 * (2 - (b + c)) + 2 * (w * (b - c))) * (2 + (d + e) - w ^ 2 * (2 - (d + e)) + 2 * (w * (d - e))) = 0`. Take the linear combination `E3 - (1 - w ^ 2) * (2 + (d + e) - w ^ 2 * (2 - (d + e)) + 2 * (w * (d - e)) + (d * e - 1) * (1 - w ^ 2)) * hbc - (1 - w ^ 2) * (2 + (b + c) - w ^ 2 * (2 - (b + c)) + 2 * (w * (b - c))) * hde`. Establish `t4 : (2 + (b + c) - w ^ 2 * (2 - (b + c)) - 2 * (w * (b - c))) * (2 + (d + e) - w ^ 2 * (2 - (d + e)) - 2 * (w * (d - e))) = 0`. Take the linear combination `E4 - (1 - w ^ 2) * (2 + (d + e) - w ^ 2 * (2 - (d + e)) - 2 * (w * (d - e)) + (d * e - 1) * (1 - w ^ 2)) * hbc - (1 - w ^ 2) * (2 + (b + c) - w ^ 2 * (2 - (b + c)) - 2 * (w * (b - c))) * hde`. Establish `t5 : 8 * (w * (b - c) * (w * (d - e))) - 32 * w ^ 2 = 0`.

Take the linear combination `t3 + t4 - 2 * (1 + w ^ 2) ^ 2 * s4 - 4 * (1 - w ^ 4) * s3`. Establish `t6 : (w * (b - c) * (w * (d - e))) ^ 2 = 0`. Take the linear combination `w ^ 4 * (2 - (b + c)) * (2 - (d + e)) * s1 - 4 * w ^ 4 * ((d + e) ^ 2 - 4 - 4 * (d * e - 1)) * hbc - 4 * w ^ 4 * ((b + c) ^ 2 - 4) * hde`. Establish `t7 : 1024 * w ^ 4 = 0`. Take the linear combination `64 * t6 - (8 * (w * (b - c) * (w * (d - e))) + 32 * w ^ 2) * t5`.

Take the linear combination `v ^ 10 * u ^ 4 * t7 - (w * u) ^ 4 * (1 + 2 * v + (2 * v) ^ 2 + (2 * v) ^ 3 + (2 * v) ^ 4 + (2 * v) ^ 5 + (2 * v) ^ 6 + (2 * v) ^ 7 + (2 * v) ^ 8 + (2 * v) ^ 9) * h2v - ((w * u) ^ 3 + (w * u) ^ 2 + w * u + 1) * hwu`.
-/
private theorem UpperTheory.V.Z.Sym.Loc.one_eq_zero_of_products_vanish {A : Type} [CommRing A] (b c d e w u v : A)
    (hbc : b * c = 1) (hde : d * e = 1) (hwu : w * u = 1) (h2v : 2 * v = 1)
    (E1 : (1 + c) * (1 + b) * (1 + e) * (1 + d) = 0)
    (E2 : (w * (1 - c)) * (-w * (1 - b)) * ((1 - e) * w) * ((1 - d) * -w) = 0)
    (E3 : (1 + c + w * (1 - c)) * (1 + b + -w * (1 - b)) * (1 + e + (1 - e) * w)
      * (1 + d + (1 - d) * -w) = 0)
    (E4 : (1 + c - w * (1 - c)) * (1 + b - -w * (1 - b)) * (1 + e - (1 - e) * w)
      * (1 + d - (1 - d) * -w) = 0) :
    (1 : A) = 0 := by
  have s1 : (2 + (b + c)) * (2 + (d + e)) = 0 := by
    linear_combination E1 - (2 + (d + e) + (d * e - 1)) * hbc - (2 + (b + c)) * hde
  have t2 : (1 - c) * (1 - b) * (1 - e) * (1 - d) = 0 := by
    linear_combination u ^ 4 * E2
      - (1 - c) * (1 - b) * (1 - e) * (1 - d) * (w * u + 1) * (w ^ 2 * u ^ 2 + 1) * hwu
  have s2 : (2 - (b + c)) * (2 - (d + e)) = 0 := by
    linear_combination t2 - (2 - (d + e) + (d * e - 1)) * hbc - (2 - (b + c)) * hde
  have s3 : (b + c) + (d + e) = 0 := by
    linear_combination v ^ 2 * (s1 - s2) - ((b + c) + (d + e)) * (2 * v + 1) * h2v
  have s4 : (b + c) * (d + e) + 4 = 0 := by
    linear_combination v * (s1 + s2) - ((b + c) * (d + e) + 4) * h2v
  have t3 : (2 + (b + c) - w ^ 2 * (2 - (b + c)) + 2 * (w * (b - c)))
      * (2 + (d + e) - w ^ 2 * (2 - (d + e)) + 2 * (w * (d - e))) = 0 := by
    linear_combination E3
      - (1 - w ^ 2) * (2 + (d + e) - w ^ 2 * (2 - (d + e)) + 2 * (w * (d - e))
        + (d * e - 1) * (1 - w ^ 2)) * hbc
      - (1 - w ^ 2) * (2 + (b + c) - w ^ 2 * (2 - (b + c)) + 2 * (w * (b - c))) * hde
  have t4 : (2 + (b + c) - w ^ 2 * (2 - (b + c)) - 2 * (w * (b - c)))
      * (2 + (d + e) - w ^ 2 * (2 - (d + e)) - 2 * (w * (d - e))) = 0 := by
    linear_combination E4
      - (1 - w ^ 2) * (2 + (d + e) - w ^ 2 * (2 - (d + e)) - 2 * (w * (d - e))
        + (d * e - 1) * (1 - w ^ 2)) * hbc
      - (1 - w ^ 2) * (2 + (b + c) - w ^ 2 * (2 - (b + c)) - 2 * (w * (b - c))) * hde
  have t5 : 8 * (w * (b - c) * (w * (d - e))) - 32 * w ^ 2 = 0 := by
    linear_combination t3 + t4 - 2 * (1 + w ^ 2) ^ 2 * s4 - 4 * (1 - w ^ 4) * s3
  have t6 : (w * (b - c) * (w * (d - e))) ^ 2 = 0 := by
    linear_combination w ^ 4 * (2 - (b + c)) * (2 - (d + e)) * s1
      - 4 * w ^ 4 * ((d + e) ^ 2 - 4 - 4 * (d * e - 1)) * hbc
      - 4 * w ^ 4 * ((b + c) ^ 2 - 4) * hde
  have t7 : 1024 * w ^ 4 = 0 := by
    linear_combination 64 * t6 - (8 * (w * (b - c) * (w * (d - e))) + 32 * w ^ 2) * t5
  linear_combination v ^ 10 * u ^ 4 * t7
    - (w * u) ^ 4 * (1 + 2 * v + (2 * v) ^ 2 + (2 * v) ^ 3 + (2 * v) ^ 4 + (2 * v) ^ 5
      + (2 * v) ^ 6 + (2 * v) ^ 7 + (2 * v) ^ 8 + (2 * v) ^ 9) * h2v
    - ((w * u) ^ 3 + (w * u) ^ 2 + w * u + 1) * hwu

/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ τ hL hτ β hβ`. Establish `h2 : (2 : K) ≠ 0`. Use `(hL.two.map (algebraMap O K)).ne_zero` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis. Take `⟨u0, s, hs, hΔeq⟩` from `hL.even`.

Establish `hΔ : Δ ≠ 0`. Rewrite using `[hΔeq]`. Conclude with `mul_ne_zero (u0.isUnit.map (algebraMap O K)).ne_zero (pow_ne_zero 2 hs)`. Set `w : EL Δ τ` to `⟨⟨0, 1⟩, 0⟩`. Apply the tactic sequence `have hsw : sigL w = -w := by ext <;> simp [w, sigL]`.

Apply the tactic sequence `have hstw : star w = w := by ext <;> simp [w]`. Set `u : EL Δ τ` to `⟨⟨0, Δ⁻¹⟩, 0⟩`. Apply the tactic sequence `have hwu : w * u = 1 := by ext <;> simp [w, u, hΔ]`. Set `v : EL Δ τ` to `⟨⟨2⁻¹, 0⟩, 0⟩`. Apply the tactic sequence `have h2v : 2 * v = 1 := by ext <;> simp [v, h2]`.

Establish `sadd : ∀ x y : EL Δ τ, sigL (x + y) = sigL x + sigL y`. Introduce `x y`. Apply the tactic sequence `ext <;> simp [sigL]`. Establish `ssub : ∀ x y : EL Δ τ, sigL (x - y) = sigL x - sigL y`. Introduce `x y`.

Apply the tactic sequence `ext <;> simp [sigL]`. Establish `hne : (1 : EL Δ τ) ≠ 0` using `fun h => by`. Use `congrArg (fun z => z.re.re) h` as an intermediate fact. Simplify using `at this`. Establish `dich : ∀ x : EL Δ τ, sigL x = x → star x = x → IsUnit x ∨ x = 0`.

Introduce and unpack `⟨⟨r1, r2⟩, ⟨r3, r4⟩⟩ hs' ht`. Establish `a` using `congrArg (fun z => z.re.im) hs'`. Establish `c` using `congrArg (fun z => z.im.re) ht`. Establish `d` using `congrArg (fun z => z.im.im) ht`. Simplify using `[sigL] at a c d`.

Establish `z2 : r2 = 0`. Establish `h : (2 : K) * r2 = 0` using `by linear_combination -a`. Conclude with `(mul_eq_zero.mp h).resolve_left h2`. Establish `z3 : r3 = 0`. Establish `h : (2 : K) * r3 = 0` using `by linear_combination -c`.

Conclude with `(mul_eq_zero.mp h).resolve_left h2`. Establish `z4 : r4 = 0`. Establish `h : (2 : K) * r4 = 0` using `by linear_combination -d`. Conclude with `(mul_eq_zero.mp h).resolve_left h2`. Substitute `z2 z3 z4` using the available equality.

Distinguish the cases in `hr : r1 = 0`. Use `right`. Substitute `hr` using the available equality. Apply the tactic sequence `ext <;> simp`. Use `left`.

Use `isUnit_iff_exists_inv.mpr ⟨⟨⟨r1⁻¹, 0⟩, 0⟩, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [hr]`. Set `M : EL Δ τ → EL Δ τ` to `fun z => z * sigL z * star z * star (sigL z)`. Establish `fixσ : ∀ z, sigL (M z) = M z`. Introduce `z`.

Simplify using `only [M, sigL_mul, sigL_sigL, sigL_star]`. Expand and normalize the polynomial expressions, which then agree. Establish `fixs : ∀ z, star (M z) = M z`. Introduce `z`. Simplify using `only [M, star_mul, star_star]`.

Expand and normalize the polynomial expressions, which then agree. Establish `key : ∀ z : EL Δ τ, sigL z = β * z → IsUnit (M z) → ∃ y : (EL Δ τ)ˣ, sigL (y : EL Δ τ) = β * (y : EL Δ τ)`. Introduce `z hz hM`. Establish `hu : IsUnit z`. Establish `e : M z = z * (sigL z * star z * star (sigL z))`.

Simplify using `only [M]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hM` using `[e]`. Conclude with `isUnit_of_mul_isUnit_left hM`. Conclude with `⟨hu.unit, by rw [hu.unit_spec]; exact hz⟩`.

Set `y1 : EL Δ τ` to `1 + sigL β`. Set `y2 : EL Δ τ` to `w * (1 - sigL β)`. Establish `g1 : sigL y1 = β * y1`. Simplify using `only [y1, sadd, sigL_one, sigL_sigL]`. Take the linear combination `-hβ`.

Establish `g2 : sigL y2 = β * y2`. Simplify using `only [y2, sigL_mul, ssub, sigL_one, sigL_sigL, hsw]`. Take the linear combination `w * hβ`. Establish `g3 : sigL (y1 + y2) = β * (y1 + y2)`. Rewrite using `[sadd, g1, g2]`.

Expand and normalize the polynomial expressions, which then agree. Establish `g4 : sigL (y1 - y2) = β * (y1 - y2)`. Rewrite using `[ssub, g1, g2]`. Expand and normalize the polynomial expressions, which then agree. Break down `dich (M y1) (fixσ _) (fixs _) with h | h1` into its components or cases.

Conclude with `key _ g1 h`. Break down `dich (M y2) (fixσ _) (fixs _) with h | h2'` into its components or cases. Conclude with `key _ g2 h`. Break down `dich (M (y1 + y2)) (fixσ _) (fixs _) with h | h3` into its components or cases. Conclude with `key _ g3 h`.

Break down `dich (M (y1 - y2)) (fixσ _) (fixs _) with h | h4` into its components or cases. Conclude with `key _ g4 h`. It suffices to derive a contradiction. Apply `hne` to reduce the goal to its premises. Use `UpperTheory.V.Z.Sym.Loc.one_eq_zero_of_products_vanish β (sigL β) (star β) (star (sigL β)) w u v hβ ?_ hwu h2v ?_ ?_ ?_ ?_` and prove the remaining obligations.

Establish `h` using `congrArg star hβ`. Simplify using `only [star_mul, star_one] at h`. Take the linear combination `h`. Rewrite using `[← h1]`. Simplify using `only [M, y1, sadd, sigL_one, sigL_sigL, star_add, star_one]`.

Rewrite using `[← h2']`. Simplify using `only [M, y2, sigL_mul, ssub, sigL_one, sigL_sigL, hsw, star_mul, star_sub, star_one, star_neg, hstw]`. Rewrite using `[← h3]`. Simplify using `only [M, y1, y2, sadd, sigL_mul, ssub, sigL_one, sigL_sigL, hsw, star_add, star_mul, star_sub, star_one, star_neg, hstw]`. Rewrite using `[← h4]`.

Simplify using `only [M, y1, y2, sadd, sigL_mul, ssub, sigL_one, sigL_sigL, hsw, star_add, star_mul, star_sub, star_one, star_neg, hstw]`.
-/
theorem UpperTheory.V.Z.Sym.Loc.h90 : UpperTheory.V.Z.Sym.Loc.H90 := by
  intro O K _ _ _ _ _ Δ τ hL hτ β hβ
  have h2 : (2 : K) ≠ 0 := by
    have := (hL.two.map (algebraMap O K)).ne_zero
    rwa [map_ofNat] at this
  obtain ⟨u0, s, hs, hΔeq⟩ := hL.even
  have hΔ : Δ ≠ 0 := by
    rw [hΔeq]
    exact mul_ne_zero (u0.isUnit.map (algebraMap O K)).ne_zero (pow_ne_zero 2 hs)
  let w : EL Δ τ := ⟨⟨0, 1⟩, 0⟩
  have hsw : sigL w = -w := by ext <;> simp [w, sigL]
  have hstw : star w = w := by ext <;> simp [w]
  let u : EL Δ τ := ⟨⟨0, Δ⁻¹⟩, 0⟩
  have hwu : w * u = 1 := by ext <;> simp [w, u, hΔ]
  let v : EL Δ τ := ⟨⟨2⁻¹, 0⟩, 0⟩
  have h2v : 2 * v = 1 := by ext <;> simp [v, h2]
  have sadd : ∀ x y : EL Δ τ, sigL (x + y) = sigL x + sigL y := by
    intro x y
    ext <;> simp [sigL]
  have ssub : ∀ x y : EL Δ τ, sigL (x - y) = sigL x - sigL y := by
    intro x y
    ext <;> simp [sigL]
  have hne : (1 : EL Δ τ) ≠ 0 := fun h => by
    have := congrArg (fun z => z.re.re) h
    simp at this
  have dich : ∀ x : EL Δ τ, sigL x = x → star x = x → IsUnit x ∨ x = 0 := by
    rintro ⟨⟨r1, r2⟩, ⟨r3, r4⟩⟩ hs' ht
    have a := congrArg (fun z => z.re.im) hs'
    have c := congrArg (fun z => z.im.re) ht
    have d := congrArg (fun z => z.im.im) ht
    simp [sigL] at a c d
    have z2 : r2 = 0 := by
      have h : (2 : K) * r2 = 0 := by linear_combination -a
      exact (mul_eq_zero.mp h).resolve_left h2
    have z3 : r3 = 0 := by
      have h : (2 : K) * r3 = 0 := by linear_combination -c
      exact (mul_eq_zero.mp h).resolve_left h2
    have z4 : r4 = 0 := by
      have h : (2 : K) * r4 = 0 := by linear_combination -d
      exact (mul_eq_zero.mp h).resolve_left h2
    subst z2 z3 z4
    by_cases hr : r1 = 0
    · right
      subst hr
      ext <;> simp
    · left
      refine isUnit_iff_exists_inv.mpr ⟨⟨⟨r1⁻¹, 0⟩, 0⟩, ?_⟩
      ext <;> simp [hr]
  let M : EL Δ τ → EL Δ τ := fun z => z * sigL z * star z * star (sigL z)
  have fixσ : ∀ z, sigL (M z) = M z := by
    intro z
    simp only [M, sigL_mul, sigL_sigL, sigL_star]
    ring
  have fixs : ∀ z, star (M z) = M z := by
    intro z
    simp only [M, star_mul, star_star]
    ring
  have key : ∀ z : EL Δ τ, sigL z = β * z → IsUnit (M z) →
      ∃ y : (EL Δ τ)ˣ, sigL (y : EL Δ τ) = β * (y : EL Δ τ) := by
    intro z hz hM
    have hu : IsUnit z := by
      have e : M z = z * (sigL z * star z * star (sigL z)) := by
        simp only [M]
        ring
      rw [e] at hM
      exact isUnit_of_mul_isUnit_left hM
    exact ⟨hu.unit, by rw [hu.unit_spec]; exact hz⟩
  let y1 : EL Δ τ := 1 + sigL β
  let y2 : EL Δ τ := w * (1 - sigL β)
  have g1 : sigL y1 = β * y1 := by
    simp only [y1, sadd, sigL_one, sigL_sigL]
    linear_combination -hβ
  have g2 : sigL y2 = β * y2 := by
    simp only [y2, sigL_mul, ssub, sigL_one, sigL_sigL, hsw]
    linear_combination w * hβ
  have g3 : sigL (y1 + y2) = β * (y1 + y2) := by
    rw [sadd, g1, g2]
    ring
  have g4 : sigL (y1 - y2) = β * (y1 - y2) := by
    rw [ssub, g1, g2]
    ring
  rcases dich (M y1) (fixσ _) (fixs _) with h | h1
  · exact key _ g1 h
  rcases dich (M y2) (fixσ _) (fixs _) with h | h2'
  · exact key _ g2 h
  rcases dich (M (y1 + y2)) (fixσ _) (fixs _) with h | h3
  · exact key _ g3 h
  rcases dich (M (y1 - y2)) (fixσ _) (fixs _) with h | h4
  · exact key _ g4 h
  exfalso
  apply hne
  refine UpperTheory.V.Z.Sym.Loc.one_eq_zero_of_products_vanish β (sigL β) (star β) (star (sigL β)) w u v hβ ?_ hwu h2v ?_ ?_ ?_ ?_
  · have h := congrArg star hβ
    simp only [star_mul, star_one] at h
    linear_combination h
  · rw [← h1]
    simp only [M, y1, sadd, sigL_one, sigL_sigL, star_add, star_one]
  · rw [← h2']
    simp only [M, y2, sigL_mul, ssub, sigL_one, sigL_sigL, hsw, star_mul, star_sub, star_one,
      star_neg, hstw]
  · rw [← h3]
    simp only [M, y1, y2, sadd, sigL_mul, ssub, sigL_one, sigL_sigL, hsw, star_add, star_mul,
      star_sub, star_one, star_neg, hstw]
  · rw [← h4]
    simp only [M, y1, y2, sadd, sigL_mul, ssub, sigL_one, sigL_sigL, hsw, star_add, star_mul,
      star_sub, star_one, star_neg, hstw]
