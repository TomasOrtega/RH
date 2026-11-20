import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIdem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ChartValJ

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.TorsFac

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Establish `h0 : t.act.act 0 = 1`. Establish `h` using `t.act.add 0 0`. Rewrite `h` using `[add_zero]`. Establish `h2` using `congrArg (fun f => (t.act.act 0)⁻¹ * f) h`. Simplify using `only [inv_mul_cancel, inv_mul_cancel_left] at h2`.

Conclude with `h2.symm`. Proceed by induction on `n with`. Consider the case `zero => rw [Nat.cast_zero, pow_zero, h0, MonObj.comp_one]`. Consider the case `succ n ih => rw [Nat.cast_succ, t.act.add, MonObj.comp_mul, ih, t.act.one, Category.comp_id, pow_succ]`.
-/
theorem act_nat {S : Scheme.{0}} (t : SAB H S) {T : Over S} (x : T ⟶ t.G) (n : ℕ) :
    x ≫ t.act.act (n : 𝓞 E) = x ^ n := by
  have h0 : t.act.act 0 = 1 := by
    have h := t.act.add 0 0
    rw [add_zero] at h
    have h2 := congrArg (fun f => (t.act.act 0)⁻¹ * f) h
    simp only [inv_mul_cancel, inv_mul_cancel_left] at h2
    exact h2.symm
  induction n with
  | zero => rw [Nat.cast_zero, pow_zero, h0, MonObj.comp_one]
  | succ n ih => rw [Nat.cast_succ, t.act.add, MonObj.comp_mul, ih, t.act.one, Category.comp_id, pow_succ]

/- English proof (translation)
Rewrite using `[t.act.mul, ← Category.assoc, act_nat]`.
-/
theorem act_pow {S : Scheme.{0}} (t : SAB H S) {T : Over S} (x : T ⟶ t.G) (b : 𝓞 E) (n : ℕ) :
    (x ≫ t.act.act b) ^ n = x ≫ t.act.act (b * n) := by
  rw [t.act.mul, ← Category.assoc, act_nat]

/- English proof (translation)
Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]`.
-/
theorem bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

/- English proof (translation)
Establish `h : (l.M : 𝓞 E) ∈ Ideal.span {(l.M : 𝓞 E)}` using `Ideal.mem_span_singleton_self _`. Rewrite `h` using `[← l.prod]`. Conclude with `(Ideal.mul_le_left : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb) h`.
-/
theorem M_mem (l : Level H) : (l.M : 𝓞 E) ∈ l.Mb := by
  have h : (l.M : 𝓞 E) ∈ Ideal.span {(l.M : 𝓞 E)} := Ideal.mem_span_singleton_self _
  rw [← l.prod] at h
  exact (Ideal.mul_le_left : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb) h

/- English proof (translation)
Rewrite using `[Xo.univ.t.act.mul, ← Category.assoc, act_nat]`. Conclude with `h a ha`.
-/
theorem kill {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {T : Over Xo.X} (t : T ⟶ Xo.univ.t.G) (N : ℕ)
    (h : KilledBy Xo l.Mb (t ^ N)) (a : 𝓞 E) (ha : a ∈ l.Mb) : t ≫ Xo.univ.t.act.act (N * a) = 1 := by
  rw [Xo.univ.t.act.mul, ← Category.assoc, act_nat]
  exact h a ha

omit [IsCMField E] in
/- English proof (translation)
Establish `h2` using `map_dvd (Algebra.norm ℤ) h`. Establish `e1 : (p : 𝓞 E) = algebraMap ℤ (𝓞 E) (p : ℤ)` using `by simp`. Establish `e2 : (m : 𝓞 E) = algebraMap ℤ (𝓞 E) (m : ℤ)` using `by simp`. Rewrite `h2` using `[e1, e2, Algebra.norm_algebraMap, Algebra.norm_algebraMap]`. Establish `hr : Module.finrank ℤ (𝓞 E) ≠ 0` using `Module.finrank_pos.ne'`.

Rewrite `h2` using `[IsIntegrallyClosed.pow_dvd_pow_iff hr]`. Conclude with `Int.natCast_dvd_natCast.mp h2`.
-/
theorem dvd_of_cast_dvd {p m : ℕ} (hp : p.Prime) (h : (p : 𝓞 E) ∣ (m : 𝓞 E)) : p ∣ m := by
  have h2 := map_dvd (Algebra.norm ℤ) h
  have e1 : (p : 𝓞 E) = algebraMap ℤ (𝓞 E) (p : ℤ) := by simp
  have e2 : (m : 𝓞 E) = algebraMap ℤ (𝓞 E) (m : ℤ) := by simp
  rw [e1, e2, Algebra.norm_algebraMap, Algebra.norm_algebraMap] at h2
  have hr : Module.finrank ℤ (𝓞 E) ≠ 0 := Module.finrank_pos.ne'
  rw [IsIntegrallyClosed.pow_dvd_pow_iff hr] at h2
  exact Int.natCast_dvd_natCast.mp h2

/- English proof (translation)
Take `⟨m, rfl⟩` from `h1`. Establish `hm : ¬ ℓ ∣ m` using `fun ⟨c, hc⟩ => h2 ⟨c, by rw [hc]; ring⟩`. Establish `hcop : Nat.Coprime m (ℓ ^ e)` using `Nat.Coprime.pow_right e ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm`. Take `⟨k, hk⟩` from `hcop.dvd_of_dvd_mul_left ((Dvd.intro_left ℓ rfl).trans h)`. Conclude with `⟨m, k, rfl, hk⟩`.
-/
theorem split_once {M ℓ e n' : ℕ} (hp : ℓ.Prime) (h1 : ℓ ∣ M) (h2 : ¬ ℓ ^ 2 ∣ M) (h : M ∣ ℓ ^ e * n') :
    ∃ m k, M = ℓ * m ∧ n' = m * k := by
  obtain ⟨m, rfl⟩ := h1
  have hm : ¬ ℓ ∣ m := fun ⟨c, hc⟩ => h2 ⟨c, by rw [hc]; ring⟩
  have hcop : Nat.Coprime m (ℓ ^ e) :=
    Nat.Coprime.pow_right e ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm
  obtain ⟨k, hk⟩ := hcop.dvd_of_dvd_mul_left ((Dvd.intro_left ℓ rfl).trans h)
  exact ⟨m, k, rfl, hk⟩

/- English proof (translation)
Establish `hN : (N : 𝓞 E) ∈ l.Mb`. Take `⟨q, rfl⟩` from `hMN`. Use `push_cast`. Conclude with `Ideal.mul_mem_right _ _ (M_mem l)`. Rewrite using `[sq, pow_mul, ← act_nat Xo.univ.t (t ^ N) N]`.

Conclude with `hk _ hN`.
-/
private theorem sq_lemma' {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {T : Over Xo.X} (t : T ⟶ Xo.univ.t.G)
    {N : ℕ} (hMN : l.M ∣ N) (hk : KilledBy Xo l.Mb (t ^ N)) : t ^ (N ^ 2) = 1 := by
  have hN : (N : 𝓞 E) ∈ l.Mb := by
    obtain ⟨q, rfl⟩ := hMN
    push_cast
    exact Ideal.mul_mem_right _ _ (M_mem l)
  rw [sq, pow_mul, ← act_nat Xo.univ.t (t ^ N) N]
  exact hk _ hN

/- English proof (translation)
Take `⟨q, rfl⟩` from `h`. Use `push_cast`. Conclude with `Ideal.mul_mem_right _ _ (M_mem l)`.
-/
private theorem natCast_mem_level_of_dvd {l : Level H} {k : ℕ} (h : l.M ∣ k) : (k : 𝓞 E) ∈ l.Mb := by
  obtain ⟨q, rfl⟩ := h
  push_cast
  exact Ideal.mul_mem_right _ _ (M_mem l)

/- English proof (translation)
Distinguish the cases in `h1 : ℓ ∣ M`. Take `⟨m, k, rfl, rfl⟩` from `split_once hp h1 h2 h`. Conclude with `⟨k, by ring⟩`. Establish `hc : Nat.Coprime M (ℓ ^ e)` using `Nat.Coprime.pow_right e ((Nat.Prime.coprime_iff_not_dvd hp).2 h1).symm`. Conclude with `Dvd.dvd.mul_left (hc.dvd_of_dvd_mul_left h) ℓ`.
-/
private theorem dvd_lemma_3 {M ℓ e n' : ℕ} (hp : ℓ.Prime) (h2 : ¬ ℓ ^ 2 ∣ M) (h : M ∣ ℓ ^ e * n') :
    M ∣ ℓ * n' := by
  by_cases h1 : ℓ ∣ M
  · obtain ⟨m, k, rfl, rfl⟩ := split_once hp h1 h2 h
    exact ⟨k, by ring⟩
  · have hc : Nat.Coprime M (ℓ ^ e) :=
      Nat.Coprime.pow_right e ((Nat.Prime.coprime_iff_not_dvd hp).2 h1).symm
    exact Dvd.dvd.mul_left (hc.dvd_of_dvd_mul_left h) ℓ

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo N ℓ hN hMN hp`. Establish `hN0 : N ≠ 0` using `hN.pos.ne'`. Use `⟨fun hℓM => ?_, fun α A hA h2 hc => ?_⟩` and prove the remaining obligations. Take `⟨j, n', hn', hNe⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hN0 ℓ hp.one_lt.ne'`. Establish `hcop : Nat.Coprime n' ℓ` using `((Nat.Prime.coprime_iff_not_dvd hp).2 hn').symm`.

Establish `hMn : l.M ∣ n'`. Establish `hc : Nat.Coprime l.M (ℓ ^ j)` using `Nat.Coprime.pow_right j ((Nat.Prime.coprime_iff_not_dvd hp).2 hℓM).symm`. Conclude with `hc.dvd_of_dvd_mul_left (hNe ▸ hMN)`. Use `⟨n', j, hcop, hNe, fun T t hk hi => ⟨sq_lemma' Xo t hMN hk, ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[act_pow]`.

Establish `he : (ℓ : 𝓞 E) ^ j * ((n' ^ 2 * 1 : ℕ) : 𝓞 E) = (N : 𝓞 E) * (n' : 𝓞 E)`. Rewrite using `[hNe]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he]`.

Conclude with `kill Xo t N hk _ (natCast_mem_level_of_dvd hMn)`. Take `⟨i, hi⟩` from `hi`. Use `⟨i, ?_⟩` and prove the remaining obligations. Rewrite using `[← act_nat Xo.univ.t t, Nat.cast_pow]`. Conclude with `hi _ (Ideal.pow_mem_pow (M_mem l) i)`.

Establish `hℓN : ℓ ∣ N`. Break down `hc with ⟨hA', hle⟩ | ⟨_, hℓM⟩` into its components or cases. Establish `hbM : H.bar α ∣ (l.M : 𝓞 E)` using `Ideal.mem_span_singleton.mp (hle (M_mem l))`. Establish `haM : α ∣ (l.M : 𝓞 E)`. Establish `h3` using `map_dvd H.bar hbM`.

Rewrite `h3` using `[bar_bar, map_natCast]`. Then use the resulting hypothesis. Establish `hl : (ℓ : 𝓞 E) = α * H.bar α` using `by rw [hA, hA']`. Establish `h4 : (ℓ : 𝓞 E) ∣ ((N ^ 2 : ℕ) : 𝓞 E)`. Take `⟨q, rfl⟩` from `hMN`. Rewrite using `[hl]`.

Conclude with `(mul_dvd_mul haM hbM).trans ⟨(q : 𝓞 E) ^ 2, by push_cast; ring⟩`. Conclude with `hp.dvd_of_dvd_pow (dvd_of_cast_dvd hp h4)`. Conclude with `hℓM.trans hMN`. Take `⟨N', hN'⟩` from `hℓN`. Establish `hN'0 : N' ≠ 0` using `right_ne_zero_of_mul (hN' ▸ hN0)`.

Take `⟨e, n', hn', hN'e⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hN'0 ℓ hp.one_lt.ne'`. Establish `hNe : N = ℓ ^ (e + 1) * n'` using `by rw [hN', hN'e]; ring`. Establish `hcop : Nat.Coprime n' ℓ` using `((Nat.Prime.coprime_iff_not_dvd hp).2 hn').symm`. Establish `hMl : l.M ∣ ℓ * n'` using `dvd_lemma_3 hp h2 (by rw [← hNe]; exact hMN)`. Establish `hmem : ((ℓ * n' : ℕ) : 𝓞 E) ∈ l.Mb` using `natCast_mem_level_of_dvd hMl`.

Break down `hc with ⟨hA', hle⟩ | ⟨hα, _⟩` into its components or cases. Establish `hl : (ℓ : 𝓞 E) = α * H.bar α` using `by rw [hA, hA']`. Use `⟨n', ℓ ^ (2 * e + 1), 2 * e + 2, (ℓ : 𝓞 E) ^ e * H.bar α, hcop, ?_, ?_, ?_, fun T t hk _ => ⟨sq_lemma' Xo t hMN hk, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hNe]`. Use `push_cast`.

Rewrite using `[hl]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_mul, map_pow, map_natCast, bar_bar]`. Use `push_cast`. Rewrite using `[hl]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hA']`. Expand and normalize the polynomial expressions, which then agree. Establish `htop : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)`. Rewrite using `[l.coprime]`.

Conclude with `Submodule.mem_top`. Take `⟨x, hx, y, hy, hxy⟩` from `Submodule.mem_sup.mp htop`. Establish `hy' : y ∈ Ideal.span {α}`. Establish `h5` using `Ideal.map_mono (f := (H.bar : 𝓞 E →+* 𝓞 E)) hle hy`. Simplify `h5` using `[Ideal.map_span, bar_bar]`.

Take `⟨z, hz⟩` from `Ideal.mem_span_singleton'.mp hy'`. Establish `hb : (n' : 𝓞 E) * H.bar α ∈ l.Mb`. Establish `h6 : (n' : 𝓞 E) * H.bar α = x * ((n' : 𝓞 E) * H.bar α) + z * ((ℓ * n' : ℕ) : 𝓞 E)`. Use `push_cast`. Take the linear combination `(-((n' : 𝓞 E) * H.bar α)) * hxy + (-((n' : 𝓞 E) * H.bar α)) * hz + (-(z * (n' : 𝓞 E))) * hl`.

Rewrite using `[h6]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_right _ _ hx) (Ideal.mul_mem_left _ z hmem)`. Rewrite using `[act_pow]`. Establish `he : (ℓ : 𝓞 E) ^ e * H.bar α * ((n' ^ 2 * A : ℕ) : 𝓞 E) = (N : 𝓞 E) * ((n' : 𝓞 E) * H.bar α)`. Rewrite using `[hNe, hA']`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he]`. Conclude with `kill Xo t N hk _ hb`. Establish `hA2 : A = ℓ ^ 2`.

Establish `h7 : ((A : ℕ) : 𝓞 E) = ((ℓ ^ 2 : ℕ) : 𝓞 E)`. Rewrite using `[← hA, hα, map_natCast]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Conclude with `Nat.cast_injective h7`.

Use `⟨n', ℓ ^ (2 * e), 2 * e + 2, (ℓ : 𝓞 E) ^ e, hcop, ?_, ?_, ?_, fun T t hk _ => ⟨sq_lemma' Xo t hMN hk, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hNe, hα]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_pow, map_natCast]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hA2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[act_pow, hA2]`.

Establish `he : (ℓ : 𝓞 E) ^ e * ((n' ^ 2 * ℓ ^ 2 : ℕ) : 𝓞 E) = (N : 𝓞 E) * ((ℓ * n' : ℕ) : 𝓞 E)`. Rewrite using `[hNe]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he]`.

Conclude with `kill Xo t N hk _ hmem`.
-/
theorem factorisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N ℓ : ℕ), Odd N → l.M ∣ N → ℓ.Prime → (¬ ℓ ∣ l.M → ∃ (n' j : ℕ), Nat.Coprime n' ℓ ∧ N = ℓ ^ j * n' ∧ ∀ (T : Over Xo.X) (t : T ⟶ Xo.univ.t.G), KilledBy Xo l.Mb (t ^ N) → (∃ i : ℕ, KilledBy Xo (l.Mb ^ i) t) → t ^ (N ^ 2) = 1 ∧ (t ≫ Xo.univ.t.act.act ((ℓ : 𝓞 E) ^ j)) ^ (n' ^ 2 * 1) = 1 ∧ ∃ i : ℕ, t ^ (l.M ^ i) = 1) ∧ ∀ (α : 𝓞 E) (A : ℕ), α * H.bar α = (A : 𝓞 E) → ¬ ℓ ^ 2 ∣ l.M → ((A = ℓ ∧ l.Mb ≤ Ideal.span {H.bar α}) ∨ (α = (ℓ : 𝓞 E) ∧ ℓ ∣ l.M)) → ∃ (n' Bn j : ℕ) (β : 𝓞 E), Nat.Coprime n' ℓ ∧ (N : 𝓞 E) = β * α * n' ∧ β * H.bar β = (Bn : 𝓞 E) ∧ A * Bn = ℓ ^ j ∧ ∀ (T : Over Xo.X) (t : T ⟶ Xo.univ.t.G), KilledBy Xo l.Mb (t ^ N) → (∃ i : ℕ, KilledBy Xo (l.Mb ^ i) t) → t ^ (N ^ 2) = 1 ∧ (t ≫ Xo.univ.t.act.act β) ^ (n' ^ 2 * A) = 1 := by
  intro E _ _ _ H Dw l Xo N ℓ hN hMN hp
  have hN0 : N ≠ 0 := hN.pos.ne'
  refine ⟨fun hℓM => ?_, fun α A hA h2 hc => ?_⟩
  · obtain ⟨j, n', hn', hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 ℓ hp.one_lt.ne'
    have hcop : Nat.Coprime n' ℓ := ((Nat.Prime.coprime_iff_not_dvd hp).2 hn').symm
    have hMn : l.M ∣ n' := by
      have hc : Nat.Coprime l.M (ℓ ^ j) :=
        Nat.Coprime.pow_right j ((Nat.Prime.coprime_iff_not_dvd hp).2 hℓM).symm
      exact hc.dvd_of_dvd_mul_left (hNe ▸ hMN)
    refine ⟨n', j, hcop, hNe, fun T t hk hi => ⟨sq_lemma' Xo t hMN hk, ?_, ?_⟩⟩
    · rw [act_pow]
      have he : (ℓ : 𝓞 E) ^ j * ((n' ^ 2 * 1 : ℕ) : 𝓞 E) = (N : 𝓞 E) * (n' : 𝓞 E) := by
        rw [hNe]; push_cast; ring
      rw [he]
      exact kill Xo t N hk _ (natCast_mem_level_of_dvd hMn)
    · obtain ⟨i, hi⟩ := hi
      refine ⟨i, ?_⟩
      rw [← act_nat Xo.univ.t t, Nat.cast_pow]
      exact hi _ (Ideal.pow_mem_pow (M_mem l) i)
  · have hℓN : ℓ ∣ N := by
      rcases hc with ⟨hA', hle⟩ | ⟨_, hℓM⟩
      · have hbM : H.bar α ∣ (l.M : 𝓞 E) := Ideal.mem_span_singleton.mp (hle (M_mem l))
        have haM : α ∣ (l.M : 𝓞 E) := by
          have h3 := map_dvd H.bar hbM
          rwa [bar_bar, map_natCast] at h3
        have hl : (ℓ : 𝓞 E) = α * H.bar α := by rw [hA, hA']
        have h4 : (ℓ : 𝓞 E) ∣ ((N ^ 2 : ℕ) : 𝓞 E) := by
          obtain ⟨q, rfl⟩ := hMN
          rw [hl]
          exact (mul_dvd_mul haM hbM).trans ⟨(q : 𝓞 E) ^ 2, by push_cast; ring⟩
        exact hp.dvd_of_dvd_pow (dvd_of_cast_dvd hp h4)
      · exact hℓM.trans hMN
    obtain ⟨N', hN'⟩ := hℓN
    have hN'0 : N' ≠ 0 := right_ne_zero_of_mul (hN' ▸ hN0)
    obtain ⟨e, n', hn', hN'e⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN'0 ℓ hp.one_lt.ne'
    have hNe : N = ℓ ^ (e + 1) * n' := by rw [hN', hN'e]; ring
    have hcop : Nat.Coprime n' ℓ := ((Nat.Prime.coprime_iff_not_dvd hp).2 hn').symm
    have hMl : l.M ∣ ℓ * n' := dvd_lemma_3 hp h2 (by rw [← hNe]; exact hMN)
    have hmem : ((ℓ * n' : ℕ) : 𝓞 E) ∈ l.Mb := natCast_mem_level_of_dvd hMl
    rcases hc with ⟨hA', hle⟩ | ⟨hα, _⟩
    · have hl : (ℓ : 𝓞 E) = α * H.bar α := by rw [hA, hA']
      refine ⟨n', ℓ ^ (2 * e + 1), 2 * e + 2, (ℓ : 𝓞 E) ^ e * H.bar α, hcop, ?_, ?_, ?_,
        fun T t hk _ => ⟨sq_lemma' Xo t hMN hk, ?_⟩⟩
      · rw [hNe]; push_cast; rw [hl]; ring
      · rw [map_mul, map_pow, map_natCast, bar_bar]; push_cast; rw [hl]; ring
      · rw [hA']; ring
      · have htop : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
          rw [l.coprime]; exact Submodule.mem_top
        obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp htop
        have hy' : y ∈ Ideal.span {α} := by
          have h5 := Ideal.map_mono (f := (H.bar : 𝓞 E →+* 𝓞 E)) hle hy
          simpa [Ideal.map_span, bar_bar] using h5
        obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hy'
        have hb : (n' : 𝓞 E) * H.bar α ∈ l.Mb := by
          have h6 : (n' : 𝓞 E) * H.bar α = x * ((n' : 𝓞 E) * H.bar α) + z * ((ℓ * n' : ℕ) : 𝓞 E) := by
            push_cast
            linear_combination (-((n' : 𝓞 E) * H.bar α)) * hxy + (-((n' : 𝓞 E) * H.bar α)) * hz +
              (-(z * (n' : 𝓞 E))) * hl
          rw [h6]
          exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hx) (Ideal.mul_mem_left _ z hmem)
        rw [act_pow]
        have he : (ℓ : 𝓞 E) ^ e * H.bar α * ((n' ^ 2 * A : ℕ) : 𝓞 E) =
            (N : 𝓞 E) * ((n' : 𝓞 E) * H.bar α) := by
          rw [hNe, hA']; push_cast; ring
        rw [he]
        exact kill Xo t N hk _ hb
    · have hA2 : A = ℓ ^ 2 := by
        have h7 : ((A : ℕ) : 𝓞 E) = ((ℓ ^ 2 : ℕ) : 𝓞 E) := by
          rw [← hA, hα, map_natCast]; push_cast; ring
        exact Nat.cast_injective h7
      refine ⟨n', ℓ ^ (2 * e), 2 * e + 2, (ℓ : 𝓞 E) ^ e, hcop, ?_, ?_, ?_,
        fun T t hk _ => ⟨sq_lemma' Xo t hMN hk, ?_⟩⟩
      · rw [hNe, hα]; push_cast; ring
      · rw [map_pow, map_natCast]; push_cast; ring
      · rw [hA2]; ring
      · rw [act_pow, hA2]
        have he : (ℓ : 𝓞 E) ^ e * ((n' ^ 2 * ℓ ^ 2 : ℕ) : 𝓞 E) = (N : 𝓞 E) * ((ℓ * n' : ℕ) : 𝓞 E) := by
          rw [hNe]; push_cast; ring
        rw [he]
        exact kill Xo t N hk _ hmem

end GlobalTheory.TorsFac
