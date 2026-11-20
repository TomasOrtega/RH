import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.QuadraticBasis.StatementO

namespace Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis

section
variable {W O : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]

/- English proof (translation)
Assume the negation of the conclusion as `h`. Establish `h1 : b ∈ IsLocalRing.maximalIdeal W` using `(IsLocalRing.mem_maximalIdeal b).2 h`. Rewrite `h1` using `[hpW.maximalIdeal_eq, Ideal.mem_span_singleton]`. Conclude with `hb h1`.
-/
theorem qb_unit_of_not_dvd {p : ℕ} (hpW : Irreducible (p : W)) {b : W} (hb : ¬ (p : W) ∣ b) :
    IsUnit b := by
  by_contra h
  have h1 : b ∈ IsLocalRing.maximalIdeal W := (IsLocalRing.mem_maximalIdeal b).2 h
  rw [hpW.maximalIdeal_eq, Ideal.mem_span_singleton] at h1
  exact hb h1

/- English proof (translation)
Establish `hb : (p : W) ∣ b`. Assume the negation of the conclusion as `hb`. Take `⟨u, rfl⟩` from `qb_unit_of_not_dvd hpW hb`. Apply `hθ (-(↑u⁻¹ * a))` to reduce the goal to its premises. Establish `h0` using `Dvd.dvd.mul_left h (j ↑u⁻¹)`.

Establish `e : j ↑u⁻¹ * (j a + j ↑u * θ) = θ - j (-(↑u⁻¹ * a))`. Establish `h1 : j ↑u⁻¹ * j ↑u = 1` using `by rw [← map_mul]; simp`. Rewrite using `[map_neg, map_mul]`. Take the linear combination `θ * h1`. Rewrite `h0` using `[e]`. Then use the resulting hypothesis.

Use `⟨?_, hb⟩` and prove the remaining obligations. Assume the negation of the conclusion as `ha`. Establish `hu` using `(qb_unit_of_not_dvd hpW ha).map j`. Take `⟨b', rfl⟩` from `hb`. Establish `h2 : w ∣ j ((p : W) * b') * θ`.

Rewrite using `[map_mul, map_natCast, ← hw2]`. Conclude with `⟨w * j b' * θ, by ring⟩`. Establish `h3 : w ∣ j a` using `(dvd_add_left h2).1 h`. Conclude with `hw.not_isUnit (isUnit_of_dvd_unit h3 hu)`.
-/
theorem qb_I {p : ℕ} (j : W →+* O) (w θ : O) (hpW : Irreducible (p : W)) (hw2 : w ^ 2 = (p : O))
    (hw : Irreducible w) (hθ : ∀ a : W, ¬ w ∣ θ - j a) {a b : W} (h : w ∣ j a + j b * θ) :
    (p : W) ∣ a ∧ (p : W) ∣ b := by
  have hb : (p : W) ∣ b := by
    by_contra hb
    obtain ⟨u, rfl⟩ := qb_unit_of_not_dvd hpW hb
    apply hθ (-(↑u⁻¹ * a))
    have h0 := Dvd.dvd.mul_left h (j ↑u⁻¹)
    have e : j ↑u⁻¹ * (j a + j ↑u * θ) = θ - j (-(↑u⁻¹ * a)) := by
      have h1 : j ↑u⁻¹ * j ↑u = 1 := by rw [← map_mul]; simp
      rw [map_neg, map_mul]
      linear_combination θ * h1
    rwa [e] at h0
  refine ⟨?_, hb⟩
  by_contra ha
  have hu := (qb_unit_of_not_dvd hpW ha).map j
  obtain ⟨b', rfl⟩ := hb
  have h2 : w ∣ j ((p : W) * b') * θ := by
    rw [map_mul, map_natCast, ← hw2]
    exact ⟨w * j b' * θ, by ring⟩
  have h3 : w ∣ j a := (dvd_add_left h2).1 h
  exact hw.not_isUnit (isUnit_of_dvd_unit h3 hu)

/- English proof (translation)
Establish `hle : Ideal.span {(p : W)} ≤ Ideal.comap j (Ideal.span {w})`. Rewrite using `[Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast, ← hw2, Ideal.mem_span_singleton]`. Conclude with `dvd_pow_self w two_ne_zero`. Set `ι` to `Ideal.quotientMap (Ideal.span {w}) j hle`. Set `g : (W ⧸ Ideal.span {(p : W)}) × (W ⧸ Ideal.span {(p : W)}) → O ⧸ Ideal.span {w}` to `fun t => ι t.1 + ι t.2 * Ideal.Quotient.mk _ θ`.

Establish `hg : ∀ a b : W, g (Ideal.Quotient.mk _ a, Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ (j a + j b * θ)`. Introduce `a b`. Simplify using `only [g, ι, Ideal.quotientMap_mk, map_add, map_mul]`. Establish `hinj : Function.Injective g`. Introduce and unpack `⟨a, b⟩ ⟨a', b'⟩ h`.

Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Take `⟨a', rfl⟩` from `Ideal.Quotient.mk_surjective a'`. Take `⟨b', rfl⟩` from `Ideal.Quotient.mk_surjective b'`. Rewrite `h` using `[hg, hg, Ideal.Quotient.eq, Ideal.mem_span_singleton]`.

Establish `h2 : w ∣ j (a - a') + j (b - b') * θ`. Establish `e : j (a - a') + j (b - b') * θ = j a + j b * θ - (j a' + j b' * θ)`. Simplify using `only [map_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]` and apply the resulting hypothesis.

Take `⟨h3, h4⟩` from `qb_I j w θ hpW hw2 hw hθ h2`. Establish `k3 : (Ideal.Quotient.mk (Ideal.span {(p : W)})) a = Ideal.Quotient.mk _ a'` using `Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 h3)`. Establish `k4 : (Ideal.Quotient.mk (Ideal.span {(p : W)})) b = Ideal.Quotient.mk _ b'` using `Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 h4)`. Rewrite using `[k3, k4]`. Use `haveI : Finite (O ⧸ Ideal.span {w}) := Nat.finite_of_card_ne_zero (by rw [cO]; exact (pow_pos hp.pos _).ne')`.

Establish `hbij` using `hinj.bijective_of_nat_card_le (by rw [Nat.card_prod, cW, cO, two_mul, pow_add])`. Take `⟨⟨a, b⟩, hab⟩` from `hbij.2 (Ideal.Quotient.mk _ x)`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Rewrite `hab` using `[hg, eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton]`.

Take `⟨x', hx'⟩` from `hab`. Conclude with `⟨a, b, x', by linear_combination hx'⟩`.
-/
theorem qb_S {p n' : ℕ} (hp : p.Prime) (j : W →+* O) (w θ : O) (hpW : Irreducible (p : W))
    (cW : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n') (hw2 : w ^ 2 = (p : O)) (hw : Irreducible w)
    (cO : Nat.card (O ⧸ Ideal.span {w}) = p ^ (2 * n')) (hθ : ∀ a : W, ¬ w ∣ θ - j a) (x : O) :
    ∃ (a b : W) (x' : O), x = j a + j b * θ + w * x' := by
  have hle : Ideal.span {(p : W)} ≤ Ideal.comap j (Ideal.span {w}) := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast, ← hw2, Ideal.mem_span_singleton]
    exact dvd_pow_self w two_ne_zero
  let ι := Ideal.quotientMap (Ideal.span {w}) j hle
  let g : (W ⧸ Ideal.span {(p : W)}) × (W ⧸ Ideal.span {(p : W)}) → O ⧸ Ideal.span {w} :=
    fun t => ι t.1 + ι t.2 * Ideal.Quotient.mk _ θ
  have hg : ∀ a b : W, g (Ideal.Quotient.mk _ a, Ideal.Quotient.mk _ b)
      = Ideal.Quotient.mk _ (j a + j b * θ) := by
    intro a b
    simp only [g, ι, Ideal.quotientMap_mk, map_add, map_mul]
  have hinj : Function.Injective g := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a'
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b'
    rw [hg, hg, Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
    have h2 : w ∣ j (a - a') + j (b - b') * θ := by
      have e : j (a - a') + j (b - b') * θ = j a + j b * θ - (j a' + j b' * θ) := by
        simp only [map_sub]; ring
      rwa [e]
    obtain ⟨h3, h4⟩ := qb_I j w θ hpW hw2 hw hθ h2
    have k3 : (Ideal.Quotient.mk (Ideal.span {(p : W)})) a = Ideal.Quotient.mk _ a' :=
      Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 h3)
    have k4 : (Ideal.Quotient.mk (Ideal.span {(p : W)})) b = Ideal.Quotient.mk _ b' :=
      Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 h4)
    rw [k3, k4]
  haveI : Finite (O ⧸ Ideal.span {w}) :=
    Nat.finite_of_card_ne_zero (by rw [cO]; exact (pow_pos hp.pos _).ne')
  have hbij := hinj.bijective_of_nat_card_le (by rw [Nat.card_prod, cW, cO, two_mul, pow_add])
  obtain ⟨⟨a, b⟩, hab⟩ := hbij.2 (Ideal.Quotient.mk _ x)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [hg, eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hab
  obtain ⟨x', hx'⟩ := hab
  exact ⟨a, b, x', by linear_combination hx'⟩

/- English proof (translation)
Establish `hw0 : w ≠ 0` using `hw.ne_zero`. Establish `h1 : w ∣ j a + j b * θ` using `⟨-(j c + j d * θ), by linear_combination h⟩`. Take `⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩` from `qb_I j w θ hpW hw2 hw hθ h1`. Simplify using `only [map_mul, map_natCast, ← hw2] at h`. Establish `h2 : w * (w * (j a' + j b' * θ) + (j c + j d * θ)) = 0` using `by linear_combination h`.

Establish `h3` using `(mul_eq_zero.1 h2).resolve_left hw0`. Establish `h4 : w ∣ j c + j d * θ` using `⟨-(j a' + j b' * θ), by linear_combination h3⟩`. Take `⟨⟨c', rfl⟩, ⟨d', rfl⟩⟩` from `qb_I j w θ hpW hw2 hw hθ h4`. Simplify using `only [map_mul, map_natCast, ← hw2] at h3`. Use `⟨a', b', c', d', rfl, rfl, rfl, rfl, ?_⟩` and prove the remaining obligations.

Establish `h5 : w * (j a' + j b' * θ + j c' * w + j d' * θ * w) = 0` using `by linear_combination h3`. Conclude with `(mul_eq_zero.1 h5).resolve_left hw0`.
-/
theorem qb_step {p : ℕ} (j : W →+* O) (w θ : O) (hpW : Irreducible (p : W)) (hw2 : w ^ 2 = (p : O))
    (hw : Irreducible w) (hθ : ∀ a : W, ¬ w ∣ θ - j a) {a b c d : W}
    (h : j a + j b * θ + j c * w + j d * θ * w = 0) :
    ∃ a' b' c' d' : W, a = p * a' ∧ b = p * b' ∧ c = p * c' ∧ d = p * d' ∧
      j a' + j b' * θ + j c' * w + j d' * θ * w = 0 := by
  have hw0 : w ≠ 0 := hw.ne_zero
  have h1 : w ∣ j a + j b * θ := ⟨-(j c + j d * θ), by linear_combination h⟩
  obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := qb_I j w θ hpW hw2 hw hθ h1
  simp only [map_mul, map_natCast, ← hw2] at h
  have h2 : w * (w * (j a' + j b' * θ) + (j c + j d * θ)) = 0 := by linear_combination h
  have h3 := (mul_eq_zero.1 h2).resolve_left hw0
  have h4 : w ∣ j c + j d * θ := ⟨-(j a' + j b' * θ), by linear_combination h3⟩
  obtain ⟨⟨c', rfl⟩, ⟨d', rfl⟩⟩ := qb_I j w θ hpW hw2 hw hθ h4
  simp only [map_mul, map_natCast, ← hw2] at h3
  refine ⟨a', b', c', d', rfl, rfl, rfl, rfl, ?_⟩
  have h5 : w * (j a' + j b' * θ + j c' * w + j d' * θ * w) = 0 := by linear_combination h3
  exact (mul_eq_zero.1 h5).resolve_left hw0

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => intro a b c d _`. Simplify using the standard rewrite rules. Consider the case `succ m ih`. Introduce `a b c d h`.

Take `⟨a', b', c', d', rfl, rfl, rfl, rfl, h'⟩` from `qb_step j w θ hpW hw2 hw hθ h`. Take `⟨ha, hb, hc, hd⟩` from `ih h'`. Simplify using `only [pow_succ']`. Conclude with `⟨mul_dvd_mul_left _ ha, mul_dvd_mul_left _ hb, mul_dvd_mul_left _ hc, mul_dvd_mul_left _ hd⟩`.
-/
theorem qb_pow {p : ℕ} (j : W →+* O) (w θ : O) (hpW : Irreducible (p : W)) (hw2 : w ^ 2 = (p : O))
    (hw : Irreducible w) (hθ : ∀ a : W, ¬ w ∣ θ - j a) (m : ℕ) : ∀ {a b c d : W},
    j a + j b * θ + j c * w + j d * θ * w = 0 →
    (p : W) ^ m ∣ a ∧ (p : W) ^ m ∣ b ∧ (p : W) ^ m ∣ c ∧ (p : W) ^ m ∣ d := by
  induction m with
  | zero => intro a b c d _; simp
  | succ m ih =>
    intro a b c d h
    obtain ⟨a', b', c', d', rfl, rfl, rfl, rfl, h'⟩ := qb_step j w θ hpW hw2 hw hθ h
    obtain ⟨ha, hb, hc, hd⟩ := ih h'
    simp only [pow_succ']
    exact ⟨mul_dvd_mul_left _ ha, mul_dvd_mul_left _ hb, mul_dvd_mul_left _ hc, mul_dvd_mul_left _ hd⟩

/- English proof (translation)
Assume the negation of the conclusion as `ha`. Take `⟨n, hn⟩` from `FiniteMultiplicity.of_not_isUnit hpW.not_isUnit ha`. Conclude with `hn (h _)`.
-/
theorem qb_zero_of_pow {p : ℕ} (hpW : Irreducible (p : W)) {a : W} (h : ∀ m, (p : W) ^ m ∣ a) : a = 0 := by
  by_contra ha
  obtain ⟨n, hn⟩ := FiniteMultiplicity.of_not_isUnit hpW.not_isUnit ha
  exact hn (h _)

/- English proof (translation)
Assemble the required witnesses or components as `⟨qb_zero_of_pow hpW fun m => (qb_pow j w θ hpW hw2 hw hθ m h).1, qb_zero_of_pow hpW fun m => (qb_pow j w θ hpW hw2 hw hθ m h).2.1, qb_zero_of_pow hpW fun m => (qb_pow j w θ hpW hw2 hw hθ m h).2.2.1, qb_zero_of_pow hpW fun m => (qb_pow j w θ hpW hw2 hw hθ m h).2.2.2⟩`.
-/
theorem qb_indep {p : ℕ} (j : W →+* O) (w θ : O) (hpW : Irreducible (p : W)) (hw2 : w ^ 2 = (p : O))
    (hw : Irreducible w) (hθ : ∀ a : W, ¬ w ∣ θ - j a) {a b c d : W}
    (h : j a + j b * θ + j c * w + j d * θ * w = 0) : a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 :=
  ⟨qb_zero_of_pow hpW fun m => (qb_pow j w θ hpW hw2 hw hθ m h).1,
   qb_zero_of_pow hpW fun m => (qb_pow j w θ hpW hw2 hw hθ m h).2.1,
   qb_zero_of_pow hpW fun m => (qb_pow j w θ hpW hw2 hw hθ m h).2.2.1,
   qb_zero_of_pow hpW fun m => (qb_pow j w θ hpW hw2 hw hθ m h).2.2.2⟩

/- English proof (translation)
Use `letI : Algebra W O := j.toAlgebra`. Use `haveI : Module.Finite W O := hfin`. Establish `hsm : ∀ (r : W) (y : O), r • y = j r * y` using `fun r y => Algebra.smul_def r y`. Set `M : Submodule W O` to `{ carrier := {y | ∃ a b c d : W, y = j a + j b * θ + j c * w + j d * θ * w} add_mem' := by`. Introduce and unpack `_ _ ⟨a, b, c, d, rfl⟩ ⟨a', b', c', d', rfl⟩`.

Conclude with `⟨a + a', b + b', c + c', d + d', by simp only [map_add]; ring⟩`. Use the proof step `zero_mem' := ⟨0, 0, 0, 0, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `r _ ⟨a, b, c, d, rfl⟩`. Conclude with `⟨r * a, r * b, r * c, r * d, by rw [hsm]; simp only [map_mul]; ring⟩ }`.

Establish `hJ : Ideal.span {(p : W)} ≤ Ideal.jacobson (⊥ : Ideal W)`. Rewrite using `[← hpW.maximalIdeal_eq]`. Conclude with `IsLocalRing.maximalIdeal_le_jacobson _`. Establish `hle : (⊤ : Submodule W O) ≤ M ⊔ Ideal.span {(p : W)} • (⊤ : Submodule W O)`. Introduce `y _`.

Take `⟨a, b, y', hy⟩` from `qb_S hp j w θ hpW cW hw2 hw cO hθ y`. Take `⟨c, d, y'', hy'⟩` from `qb_S hp j w θ hpW cW hw2 hw cO hθ y'`. Use `Submodule.mem_sup.2 ⟨j a + j b * θ + j c * w + j d * θ * w, ⟨a, b, c, d, rfl⟩, (p : W) • y'', Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top, ?_⟩` and prove the remaining obligations. Rewrite using `[hsm, map_natCast, ← hw2, hy, hy']`. Expand and normalize the polynomial expressions, which then agree.

Establish `htop` using `Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hJ hle`. Conclude with `htop (Submodule.mem_top : x ∈ ⊤)`.
-/
theorem qb_span {p n' : ℕ} (hp : p.Prime) (j : W →+* O) (w θ : O) (hpW : Irreducible (p : W))
    (cW : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n') (hfin : j.Finite) (hw2 : w ^ 2 = (p : O))
    (hw : Irreducible w) (cO : Nat.card (O ⧸ Ideal.span {w}) = p ^ (2 * n'))
    (hθ : ∀ a : W, ¬ w ∣ θ - j a) (x : O) :
    ∃ a b c d : W, x = j a + j b * θ + j c * w + j d * θ * w := by
  letI : Algebra W O := j.toAlgebra
  haveI : Module.Finite W O := hfin
  have hsm : ∀ (r : W) (y : O), r • y = j r * y := fun r y => Algebra.smul_def r y
  let M : Submodule W O :=
    { carrier := {y | ∃ a b c d : W, y = j a + j b * θ + j c * w + j d * θ * w}
      add_mem' := by
        rintro _ _ ⟨a, b, c, d, rfl⟩ ⟨a', b', c', d', rfl⟩
        exact ⟨a + a', b + b', c + c', d + d', by simp only [map_add]; ring⟩
      zero_mem' := ⟨0, 0, 0, 0, by simp⟩
      smul_mem' := by
        rintro r _ ⟨a, b, c, d, rfl⟩
        exact ⟨r * a, r * b, r * c, r * d, by rw [hsm]; simp only [map_mul]; ring⟩ }
  have hJ : Ideal.span {(p : W)} ≤ Ideal.jacobson (⊥ : Ideal W) := by
    rw [← hpW.maximalIdeal_eq]
    exact IsLocalRing.maximalIdeal_le_jacobson _
  have hle : (⊤ : Submodule W O) ≤ M ⊔ Ideal.span {(p : W)} • (⊤ : Submodule W O) := by
    intro y _
    obtain ⟨a, b, y', hy⟩ := qb_S hp j w θ hpW cW hw2 hw cO hθ y
    obtain ⟨c, d, y'', hy'⟩ := qb_S hp j w θ hpW cW hw2 hw cO hθ y'
    refine Submodule.mem_sup.2 ⟨j a + j b * θ + j c * w + j d * θ * w, ⟨a, b, c, d, rfl⟩,
      (p : W) • y'', Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top, ?_⟩
    rw [hsm, map_natCast, ← hw2, hy, hy']
    ring
  have htop := Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hJ hle
  exact htop (Submodule.mem_top : x ∈ ⊤)

end

/- English proof (translation)
Introduce `p n' hp W O _ _ _ _ _ _ j w θ hpW cW hfin hw2 hw cO hθ x`. Take `⟨a, b, c, d, hx⟩` from `qb_span hp j w θ hpW cW hfin hw2 hw cO hθ x`. Use `⟨(a, b, c, d), hx, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨a', b', c', d'⟩ hx'`. Simplify using `only at hx'`.

Establish `h : j (a' - a) + j (b' - b) * θ + j (c' - c) * w + j (d' - d) * θ * w = 0`. Simplify using `only [map_sub]`. Take the linear combination `hx - hx'`. Take `⟨h1, h2, h3, h4⟩` from `qb_indep j w θ hpW hw2 hw hθ h`. Rewrite using `[sub_eq_zero.1 h1, sub_eq_zero.1 h2, sub_eq_zero.1 h3, sub_eq_zero.1 h4]`.
-/
theorem basisCriterion_holds : QuadBasis := by
  intro p n' hp W O _ _ _ _ _ _ j w θ hpW cW hfin hw2 hw cO hθ x
  obtain ⟨a, b, c, d, hx⟩ := qb_span hp j w θ hpW cW hfin hw2 hw cO hθ x
  refine ⟨(a, b, c, d), hx, ?_⟩
  rintro ⟨a', b', c', d'⟩ hx'
  simp only at hx'
  have h : j (a' - a) + j (b' - b) * θ + j (c' - c) * w + j (d' - d) * θ * w = 0 := by
    simp only [map_sub]
    linear_combination hx - hx'
  obtain ⟨h1, h2, h3, h4⟩ := qb_indep j w θ hpW hw2 hw hθ h
  rw [sub_eq_zero.1 h1, sub_eq_zero.1 h2, sub_eq_zero.1 h3, sub_eq_zero.1 h4]

end Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
