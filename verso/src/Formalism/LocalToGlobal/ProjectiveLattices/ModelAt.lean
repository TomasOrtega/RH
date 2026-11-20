import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
import Formalism.LocalToGlobal.ProjectiveLattices.ResChPrime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def PartIAt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → l.GoodAt p →
    ∃ Y : Model Xo c (c.V W).subtype, Y.N3 ∧ PushInvertible Y.t.G Y.t.PP.L

/- English proof (translation)
Use `set V := (la.valuation c.F).valuationSubring with hVdef`. Set `g : V →+* ℂ` to `c.F.val.toRingHom.comp V.subtype`. Establish `hg : Function.Injective g` using `fun a b h => Subtype.ext (c.F.val.injective h)`. Set `e : V ≃+* g.range` to `RingEquiv.ofBijective g.rangeRestrict ⟨fun a b h => hg (congrArg (fun z : g.range => (z : ℂ)) h), g.rangeRestrict_surjective⟩`. Establish `hmax : ((IsLocalRing.maximalIdeal V).map e).IsMaximal` using `Ideal.map_isMaximal_of_equiv e`.

Take `⟨W, hAW, hIW⟩` from `Ideal.image_subset_nonunits_valuationSubring _ hmax.ne_top`. Establish `hnon : ∀ y : V, y ∈ IsLocalRing.maximalIdeal V → g y ∈ W.nonunits` using `fun y hy => hIW ⟨e y, Ideal.mem_map_of_mem _ hy, rfl⟩`. Use `⟨W, fun x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hxV : algebraMap (𝓞 c.F) c.F x ∈ V`. Rewrite using `[hVdef, Valuation.mem_valuationSubring_iff, HeightOneSpectrum.valuation_of_algebraMap]`.

Conclude with `la.intValuation_le_one x`. Establish `hxm : (⟨_, hxV⟩ : V) ∈ IsLocalRing.maximalIdeal V`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Take `⟨w, hw⟩` from `isUnit_iff_exists_inv.1 hu`.

Establish `h1 : la.valuation c.F (algebraMap (𝓞 c.F) c.F x) < 1`. Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `(la.intValuation_lt_one_iff_mem x).2 hx`. Establish `h2 : la.valuation c.F ((w : V) : c.F) ≤ 1` using `w.2`. Establish `h3` using `congrArg (fun z : V => la.valuation c.F (z : c.F)) hw`.

Simplify using `only [MulMemClass.coe_mul, OneMemClass.coe_one, map_mul, map_one] at h3`. Establish `h4 : la.valuation c.F (algebraMap (𝓞 c.F) c.F x) * la.valuation c.F ((w : V) : c.F) < 1` using `lt_of_lt_of_le (mul_lt_one_of_nonneg_of_lt_one_left zero_le h1 h2) le_rfl`. Rewrite `h4` using `[h3]`. Conclude with `lt_irrefl _ h4`. Conclude with `hnon _ hxm`.

Assume the negation of the conclusion as `hv push_neg at hv`. Establish `hx0 : x ≠ 0` using `by rintro rfl; simp at hv`. Establish `hiV : x⁻¹ ∈ V`. Rewrite using `[hVdef, Valuation.mem_valuationSubring_iff, map_inv₀]`. Conclude with `(inv_lt_one_of_one_lt₀ hv).le`.

Establish `him : (⟨x⁻¹, hiV⟩ : V) ∈ IsLocalRing.maximalIdeal V`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Take `⟨w, hw⟩` from `isUnit_iff_exists_inv.1 hu`. Establish `h1 : (w : c.F) = x`.

Use `congrArg (fun z : V => (z : c.F)) hw` as an intermediate fact. Simplify using `only [MulMemClass.coe_mul, OneMemClass.coe_one] at this`. Clear denominators, using `at this` for the nonvanishing conditions. Conclude with `this`. Establish `h2 : la.valuation c.F ((w : V) : c.F) ≤ 1` using `w.2`.

Rewrite `h2` using `[h1]`. Conclude with `absurd h2 (not_le.2 hv)`. Establish `h5` using `hnon _ him`. Rewrite `h5` using `[ValuationSubring.mem_nonunits_iff]`. Establish `h6` using `(ValuationSubring.valuation_le_one_iff W _).2 hx`.

Establish `h7 : g ⟨x⁻¹, hiV⟩ = ((x : ℂ))⁻¹` using `by show ((x⁻¹ : c.F) : ℂ) = _`. Conclude with `map_inv₀ c.F.val x`. Rewrite `h5` using `[h7, map_inv₀]`. Establish `hW0 : W.valuation (x : ℂ) ≠ 0`. Rewrite using `[Valuation.ne_zero_iff]`.

Conclude with `hx0` after adjusting the coercions. Conclude with `absurd ((inv_lt_one₀ (zero_lt_iff.2 hW0)).1 h5) (not_lt.2 h6)`.
-/
theorem exists_lieElement_middleBlockPart (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) :
    ∃ W : ValuationSubring ℂ, (∀ x : 𝓞 c.F, x ∈ la.asIdeal → (((algebraMap (𝓞 c.F) c.F x : c.F) : ℂ)) ∈ W.nonunits) ∧
      ∀ x : c.F, (x : ℂ) ∈ W → la.valuation c.F x ≤ 1 := by
  set V := (la.valuation c.F).valuationSubring with hVdef
  let g : V →+* ℂ := c.F.val.toRingHom.comp V.subtype
  have hg : Function.Injective g := fun a b h => Subtype.ext (c.F.val.injective h)
  let e : V ≃+* g.range := RingEquiv.ofBijective g.rangeRestrict ⟨fun a b h => hg (congrArg (fun z : g.range => (z : ℂ)) h),
    g.rangeRestrict_surjective⟩
  have hmax : ((IsLocalRing.maximalIdeal V).map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
  obtain ⟨W, hAW, hIW⟩ := Ideal.image_subset_nonunits_valuationSubring _ hmax.ne_top
  have hnon : ∀ y : V, y ∈ IsLocalRing.maximalIdeal V → g y ∈ W.nonunits := fun y hy =>
    hIW ⟨e y, Ideal.mem_map_of_mem _ hy, rfl⟩
  refine ⟨W, fun x hx => ?_, fun x hx => ?_⟩
  · have hxV : algebraMap (𝓞 c.F) c.F x ∈ V := by
      rw [hVdef, Valuation.mem_valuationSubring_iff, HeightOneSpectrum.valuation_of_algebraMap]
      exact la.intValuation_le_one x
    have hxm : (⟨_, hxV⟩ : V) ∈ IsLocalRing.maximalIdeal V := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 hu
      have h1 : la.valuation c.F (algebraMap (𝓞 c.F) c.F x) < 1 := by
        rw [HeightOneSpectrum.valuation_of_algebraMap]; exact (la.intValuation_lt_one_iff_mem x).2 hx
      have h2 : la.valuation c.F ((w : V) : c.F) ≤ 1 := w.2
      have h3 := congrArg (fun z : V => la.valuation c.F (z : c.F)) hw
      simp only [MulMemClass.coe_mul, OneMemClass.coe_one, map_mul, map_one] at h3
      have h4 : la.valuation c.F (algebraMap (𝓞 c.F) c.F x) * la.valuation c.F ((w : V) : c.F) < 1 :=
        lt_of_lt_of_le (mul_lt_one_of_nonneg_of_lt_one_left zero_le h1 h2) le_rfl
      rw [h3] at h4
      exact lt_irrefl _ h4
    exact hnon _ hxm
  · by_contra hv
    push_neg at hv
    have hx0 : x ≠ 0 := by rintro rfl; simp at hv
    have hiV : x⁻¹ ∈ V := by
      rw [hVdef, Valuation.mem_valuationSubring_iff, map_inv₀]
      exact (inv_lt_one_of_one_lt₀ hv).le
    have him : (⟨x⁻¹, hiV⟩ : V) ∈ IsLocalRing.maximalIdeal V := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 hu
      have h1 : (w : c.F) = x := by
        have := congrArg (fun z : V => (z : c.F)) hw
        simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
        field_simp at this
        exact this
      have h2 : la.valuation c.F ((w : V) : c.F) ≤ 1 := w.2
      rw [h1] at h2
      exact absurd h2 (not_le.2 hv)
    have h5 := hnon _ him
    rw [ValuationSubring.mem_nonunits_iff] at h5
    have h6 := (ValuationSubring.valuation_le_one_iff W _).2 hx
    have h7 : g ⟨x⁻¹, hiV⟩ = ((x : ℂ))⁻¹ := by
      show ((x⁻¹ : c.F) : ℂ) = _
      exact map_inv₀ c.F.val x
    rw [h7, map_inv₀] at h5
    have hW0 : W.valuation (x : ℂ) ≠ 0 := by
      rw [Valuation.ne_zero_iff]; exact_mod_cast hx0
    exact absurd ((inv_lt_one₀ (zero_lt_iff.2 hW0)).1 h5) (not_lt.2 h6)

/- English proof (translation)
Take `⟨W, hWnon, hWkey⟩` from `exists_lieElement_middleBlockPart c la`. Establish `hp : (Formalism.MainNotions.WeightAlgebra.resCh la).Prime` using `resCh_prime la`. Establish `hmem : ((Formalism.MainNotions.WeightAlgebra.resCh la : ℕ) : 𝓞 c.F) ∈ la.asIdeal`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`. Conclude with `ringChar.Nat.cast_ringChar`.

Establish `hpW : ((Formalism.MainNotions.WeightAlgebra.resCh la : ℕ) : ℂ) ∈ W.nonunits`. Use `hWnon _ hmem` as an intermediate fact. Simplify using `using this`. Take `⟨Y, hN3, hPI⟩` from `hI _ W hp hpW (hgood _ hp)`. Use `⟨c.V W, inferInstance, (c.V W).subtype, Y, hN3, hPI, fun Tc io e ho => ?_⟩` and prove the remaining obligations.

Establish `hint : ∀ x : c.V W, io (x : c.F) ∈ (algebraMap Tc.V Tc.Fr).range`. Introduce `x`. Establish `hx : la.valuation c.F (x : c.F) ≤ 1` using `hWkey _ x.2`. Apply `HeightOneSpectrum.mem_integers_of_valuation_le_one` to reduce the goal to its premises. Introduce `v`.

Establish `hv : v = IsDiscreteValuationRing.maximalIdeal Tc.V` using `HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal v.isMaximal)`. Substitute `hv` using the available equality. Distinguish the cases in `hx0 : (x : c.F) = 0`. Rewrite using `[hx0, map_zero, map_zero]`. Conclude with `zero_le`.

Establish `hvx0 : la.valuation c.F (x : c.F) ≠ 0` using `(Valuation.ne_zero_iff _).2 hx0`. Establish `hla : 0 ≤ vLa la (x : c.F)`. Unfold `vLa`. Rewrite `hx` using `[← WithZero.exp_log hvx0, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hvV : 0 ≤ vV Tc.V (io (x : c.F))`. Rewrite using `[ho.2 (x : c.F)]`. Check the signs of the components of the expression. Establish `hio0 : io (x : c.F) ≠ 0` using `(map_ne_zero io).2 hx0`. Establish `hval0 : valV Tc.V (io (x : c.F)) ≠ 0` using `valV_ne_zero hio0`.

Use `show valV Tc.V (io (x : c.F)) ≤ 1`. Unfold `vV at hvV`. Rewrite using `[← WithZero.exp_log hval0, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Combine the linear equalities and inequalities to obtain the conclusion. Set `f : c.V W →+* (algebraMap Tc.V Tc.Fr).range` to `(io.comp (c.V W).subtype).codRestrict _ hint`.

Set `eq : Tc.V ≃+* (algebraMap Tc.V Tc.Fr).range` to `RingEquiv.ofBijective (algebraMap Tc.V Tc.Fr).rangeRestrict ⟨fun a b h => IsFractionRing.injective Tc.V Tc.Fr (congrArg (fun z : (algebraMap Tc.V Tc.Fr).range => (z : Tc.Fr)) h), (algebraMap Tc.V Tc.Fr).rangeRestrict_surjective⟩`. Use `⟨eq.symm.toRingHom.comp f, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Use `congrArg (fun z : (algebraMap Tc.V Tc.Fr).range => (z : Tc.Fr)) (eq.apply_symm_apply (f x))` as an intermediate fact. Conclude with `this`.
-/
theorem modelAtSt_of {Xo : Moduli Dw l} {c : Coeff l} (hI : PartIAt Xo c) (hgood : ∀ p : ℕ, p.Prime → l.GoodAt p)
    (la : HeightOneSpectrum (𝓞 c.F)) : ModelAtSt Xo c la := by
  obtain ⟨W, hWnon, hWkey⟩ := exists_lieElement_middleBlockPart c la
  have hp : (Formalism.MainNotions.WeightAlgebra.resCh la).Prime := resCh_prime la
  have hmem : ((Formalism.MainNotions.WeightAlgebra.resCh la : ℕ) : 𝓞 c.F) ∈ la.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact ringChar.Nat.cast_ringChar
  have hpW : ((Formalism.MainNotions.WeightAlgebra.resCh la : ℕ) : ℂ) ∈ W.nonunits := by
    have := hWnon _ hmem
    simpa using this
  obtain ⟨Y, hN3, hPI⟩ := hI _ W hp hpW (hgood _ hp)
  refine ⟨c.V W, inferInstance, (c.V W).subtype, Y, hN3, hPI, fun Tc io e ho => ?_⟩
  have hint : ∀ x : c.V W, io (x : c.F) ∈ (algebraMap Tc.V Tc.Fr).range := by
    intro x
    have hx : la.valuation c.F (x : c.F) ≤ 1 := hWkey _ x.2
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro v
    have hv : v = IsDiscreteValuationRing.maximalIdeal Tc.V :=
      HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal v.isMaximal)
    subst hv
    by_cases hx0 : (x : c.F) = 0
    · rw [hx0, map_zero, map_zero]; exact zero_le
    have hvx0 : la.valuation c.F (x : c.F) ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
    have hla : 0 ≤ vLa la (x : c.F) := by
      unfold vLa
      rw [← WithZero.exp_log hvx0, ← WithZero.exp_zero, WithZero.exp_le_exp] at hx
      linarith
    have hvV : 0 ≤ vV Tc.V (io (x : c.F)) := by
      rw [ho.2 (x : c.F)]
      positivity
    have hio0 : io (x : c.F) ≠ 0 := (map_ne_zero io).2 hx0
    have hval0 : valV Tc.V (io (x : c.F)) ≠ 0 := valV_ne_zero hio0
    show valV Tc.V (io (x : c.F)) ≤ 1
    unfold vV at hvV
    rw [← WithZero.exp_log hval0, ← WithZero.exp_zero, WithZero.exp_le_exp]
    linarith
  let f : c.V W →+* (algebraMap Tc.V Tc.Fr).range := (io.comp (c.V W).subtype).codRestrict _ hint
  let eq : Tc.V ≃+* (algebraMap Tc.V Tc.Fr).range := RingEquiv.ofBijective (algebraMap Tc.V Tc.Fr).rangeRestrict
    ⟨fun a b h => IsFractionRing.injective Tc.V Tc.Fr (congrArg (fun z : (algebraMap Tc.V Tc.Fr).range => (z : Tc.Fr)) h),
      (algebraMap Tc.V Tc.Fr).rangeRestrict_surjective⟩
  refine ⟨eq.symm.toRingHom.comp f, ?_⟩
  ext x
  have := congrArg (fun z : (algebraMap Tc.V Tc.Fr).range => (z : Tc.Fr)) (eq.apply_symm_apply (f x))
  exact this

/- English proof (translation)
Unfold `Level.GoodAt`. Establish `hodd : Odd (g0 * g1)` using `hM ▸ l.odd`. Establish `h3 : 3 ≤ g0 * g1` using `hM ▸ l.three_le`. Establish `o0 : Odd g0` using `(Nat.odd_mul.1 hodd).1`. Establish `o1 : Odd g1` using `(Nat.odd_mul.1 hodd).2`.

Establish `t0 : 3 ≤ g0`. Use `h0.two_le` as an intermediate fact. Use `Nat.odd_iff.1 o0` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `t1 : 3 ≤ g1`.

Use `h1.two_le` as an intermediate fact. Use `Nat.odd_iff.1 o1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[hM, Nat.factorization_mul h0.ne_zero h1.ne_zero, Finsupp.add_apply, h0.factorization, h1.factorization]`. Distinguish the cases in `e0 : p = g0`.

Establish `e : (Finsupp.single g0 1 : ℕ →₀ ℕ) p + (Finsupp.single g1 1 : ℕ →₀ ℕ) p = 1`. Simplify using `[Finsupp.single_apply, e0, hne, hne.symm]`. Rewrite using `[e, pow_one, e0, Nat.mul_div_cancel_left g1 h0.pos]`. Conclude with `t1`. Distinguish the cases in `e1 : p = g1`.

Establish `e : (Finsupp.single g0 1 : ℕ →₀ ℕ) p + (Finsupp.single g1 1 : ℕ →₀ ℕ) p = 1`. Simplify using `[Finsupp.single_apply, e1, hne, hne.symm]`. Rewrite using `[e, pow_one, e1, Nat.mul_div_cancel g0 h1.pos]`. Conclude with `t0`. Establish `e : (Finsupp.single g0 1 : ℕ →₀ ℕ) p + (Finsupp.single g1 1 : ℕ →₀ ℕ) p = 0`.

Simplify using `[Finsupp.single_apply, e0, e1, Ne.symm e0, Ne.symm e1]`. Rewrite using `[e, pow_zero, Nat.div_one]`. Conclude with `h3`.
-/
theorem goodAt_of_two_primes {g0 g1 : ℕ} (hM : l.M = g0 * g1) (h0 : g0.Prime) (h1 : g1.Prime)
    (hne : g0 ≠ g1) (p : ℕ) (hp : p.Prime) : l.GoodAt p := by
  unfold Level.GoodAt
  have hodd : Odd (g0 * g1) := hM ▸ l.odd
  have h3 : 3 ≤ g0 * g1 := hM ▸ l.three_le
  have o0 : Odd g0 := (Nat.odd_mul.1 hodd).1
  have o1 : Odd g1 := (Nat.odd_mul.1 hodd).2
  have t0 : 3 ≤ g0 := by
    have := h0.two_le
    have := Nat.odd_iff.1 o0
    omega
  have t1 : 3 ≤ g1 := by
    have := h1.two_le
    have := Nat.odd_iff.1 o1
    omega
  rw [hM, Nat.factorization_mul h0.ne_zero h1.ne_zero, Finsupp.add_apply, h0.factorization, h1.factorization]
  by_cases e0 : p = g0
  · have e : (Finsupp.single g0 1 : ℕ →₀ ℕ) p + (Finsupp.single g1 1 : ℕ →₀ ℕ) p = 1 := by
      simp [Finsupp.single_apply, e0, hne, hne.symm]
    rw [e, pow_one, e0, Nat.mul_div_cancel_left g1 h0.pos]
    exact t1
  · by_cases e1 : p = g1
    · have e : (Finsupp.single g0 1 : ℕ →₀ ℕ) p + (Finsupp.single g1 1 : ℕ →₀ ℕ) p = 1 := by
        simp [Finsupp.single_apply, e1, hne, hne.symm]
      rw [e, pow_one, e1, Nat.mul_div_cancel g0 h1.pos]
      exact t0
    · have e : (Finsupp.single g0 1 : ℕ →₀ ℕ) p + (Finsupp.single g1 1 : ℕ →₀ ℕ) p = 0 := by
        simp [Finsupp.single_apply, e0, e1, Ne.symm e0, Ne.symm e1]
      rw [e, pow_zero, Nat.div_one]
      exact h3

/- English proof (translation)
Take `⟨-, hI⟩` from `hP`. Set `Xf : ∀ l' : Level H, Moduli Dw l'` to `fun l' => if h : l' = l then h ▸ Xo else Classical.choice (hN E H Dw l' hpq)`. Take `⟨Y, hY, -⟩` from `hI E H Dw hpq Xf`. Introduce `p W hp hW hg`. Take `⟨hN2, hrest⟩` from `hY p W hp hW`.

Set `i : Idx H p` to `⟨l, c, hg⟩`. Establish `hPIi` using `(hN2.1 i).2.2.1`. Establish `hN3` using `(hrest i).2.1`. Establish `hX : Xf l = Xo` using `by simp [Xf]`. Establish `key : ∀ (X' : Moduli Dw l), X' = Xo → ∀ Y' : Model X' c (c.V W).subtype, Y'.N3 → PushInvertible Y'.t.G Y'.t.PP.L → ∃ Y : Model Xo c (c.V W).subtype, Y.N3 ∧ PushInvertible Y.t.G Y.t.PP.L`.

Introduce and unpack `X' rfl Y' h1 h2`. Conclude with `⟨Y', h1, h2⟩`. Conclude with `key (Xf l) hX (Y p W hp hW i) hN3 hPIi`.
-/
theorem partIAt_of (hP : PartI) (hN : N1ab) (Xo : Moduli Dw l) (c : Coeff l) (hpq : 1 ≤ Dw.p + Dw.q) : PartIAt Xo c := by
  classical
  obtain ⟨-, hI⟩ := hP
  let Xf : ∀ l' : Level H, Moduli Dw l' := fun l' =>
    if h : l' = l then h ▸ Xo else Classical.choice (hN E H Dw l' hpq)
  obtain ⟨Y, hY, -⟩ := hI E H Dw hpq Xf
  intro p W hp hW hg
  obtain ⟨hN2, hrest⟩ := hY p W hp hW
  let i : Idx H p := ⟨l, c, hg⟩
  have hPIi := (hN2.1 i).2.2.1
  have hN3 := (hrest i).2.1
  have hX : Xf l = Xo := by simp [Xf]
  have key : ∀ (X' : Moduli Dw l), X' = Xo → ∀ Y' : Model X' c (c.V W).subtype, Y'.N3 →
      PushInvertible Y'.t.G Y'.t.PP.L → ∃ Y : Model Xo c (c.V W).subtype, Y.N3 ∧ PushInvertible Y.t.G Y.t.PP.L := by
    rintro X' rfl Y' h1 h2
    exact ⟨Y', h1, h2⟩
  exact key (Xf l) hX (Y p W hp hW i) hN3 hPIi

end Formalism.L2.Pj
