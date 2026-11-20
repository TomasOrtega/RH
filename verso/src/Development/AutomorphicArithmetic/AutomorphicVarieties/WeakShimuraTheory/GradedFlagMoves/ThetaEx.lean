import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.CyclotomicInertiaSpan.CycIne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Establish `h2` using `congrArg A.valuation h`. Rewrite `h2` using `[map_pow, map_one]`. Conclude with `(pow_eq_one_iff_of_nonneg zero_le' hm).mp h2`.
-/
private theorem thetaEx_val {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0) {ζ : Ω}
    (h : ζ ^ m = 1) : A.valuation ζ = 1 := by
  have h2 := congrArg A.valuation h
  rw [map_pow, map_one] at h2
  exact (pow_eq_one_iff_of_nonneg zero_le' hm).mp h2

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `e : (1 : Ω) - η ^ (n + 1) = (1 - η ^ n) + η ^ n * (1 - η)` using `by ring`. Rewrite using `[e]`.

Use `Valuation.map_add_lt _ ih ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, h1, one_pow, one_mul, ← Valuation.map_neg, neg_sub]`. Conclude with `h`.
-/
private theorem thetaEx_pow {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {η : Ω} (h1 : A.valuation η = 1)
    (h : A.valuation (η - 1) < 1) (i : ℕ) : A.valuation (1 - η ^ i) < 1 := by
  induction i with
  | zero => simp
  | succ n ih =>
    have e : (1 : Ω) - η ^ (n + 1) = (1 - η ^ n) + η ^ n * (1 - η) := by ring
    rw [e]
    refine Valuation.map_add_lt _ ih ?_
    rw [map_mul, map_pow, h1, one_pow, one_mul, ← Valuation.map_neg, neg_sub]
    exact h

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hsub : η - 1 ≠ 0` using `sub_ne_zero.mpr hne`. Establish `hg : (∑ i ∈ Finset.range m, η ^ i) = 0`. Use `geom_sum_mul η m` as an intermediate fact. Rewrite `this` using `[hη, sub_self]`.

Conclude with `(mul_eq_zero.mp this).resolve_right hsub`. Establish `hm' : (m : Ω) = ∑ i ∈ Finset.range m, (1 - η ^ i)`. Rewrite using `[Finset.sum_sub_distrib, hg, sub_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]`. Apply `hv` to reduce the goal to its premises. Rewrite using `[hm']`.

Conclude with `Valuation.map_sum_lt _ one_ne_zero (fun i _ => thetaEx_pow A (thetaEx_val A hm hη) h i)`.
-/
private theorem thetaEx_eta {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0)
    (hv : ¬ A.valuation (m : Ω) < 1) {η : Ω} (hη : η ^ m = 1) (h : A.valuation (η - 1) < 1) : η = 1 := by
  by_contra hne
  have hsub : η - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hg : (∑ i ∈ Finset.range m, η ^ i) = 0 := by
    have := geom_sum_mul η m
    rw [hη, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right hsub
  have hm' : (m : Ω) = ∑ i ∈ Finset.range m, (1 - η ^ i) := by
    rw [Finset.sum_sub_distrib, hg, sub_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  apply hv
  rw [hm']
  exact Valuation.map_sum_lt _ one_ne_zero (fun i _ => thetaEx_pow A (thetaEx_val A hm hη) h i)

/- English proof (translation)
Establish `hv1 : A.valuation ζ = 1` using `thetaEx_val A hm hζ`. Establish `hz : ζ ≠ 0`. Introduce `h0`. Rewrite `hv1` using `[h0, map_zero]`. Conclude with `zero_ne_one hv1`.

Establish `hg' : g ∈ Inertia A` using `hg`. Unfold `Inertia at hg'`. Establish `hd : A.valuation (g ζ - ζ) < 1` using `hg'.2 ζ hv1.le`. Establish `hpow : (g ζ * ζ⁻¹) ^ m = 1`. Rewrite using `[mul_pow, ← map_pow, hζ, map_one, inv_pow, hζ, inv_one, one_mul]`.

Establish `hlt : A.valuation (g ζ * ζ⁻¹ - 1) < 1`. Establish `e : g ζ * ζ⁻¹ - 1 = (g ζ - ζ) * ζ⁻¹` using `by field_simp`. Rewrite using `[e, map_mul, map_inv₀, hv1, inv_one, mul_one]`. Conclude with `hd`. Establish `h1` using `thetaEx_eta A hm hw hpow hlt`.

Establish `: g ζ = ζ`. Use `congrArg (· * ζ) h1` as an intermediate fact. Simplify `this` using `[hz]`. Conclude with `this`.
-/
private theorem thetaEx_fix {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) {m : ℕ}
    (hm : m ≠ 0) (hw : ¬ A.valuation (m : Ω) < 1) {ζ : Ω} (hζ : ζ ^ m = 1) (g : G ℚ Ω) (hg : g ∈ Ine (F := ℚ) A) :
    g ζ = ζ := by
  have hv1 : A.valuation ζ = 1 := thetaEx_val A hm hζ
  have hz : ζ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv1
    exact zero_ne_one hv1
  have hg' : g ∈ Inertia A := hg
  unfold Inertia at hg'
  have hd : A.valuation (g ζ - ζ) < 1 := hg'.2 ζ hv1.le
  have hpow : (g ζ * ζ⁻¹) ^ m = 1 := by
    rw [mul_pow, ← map_pow, hζ, map_one, inv_pow, hζ, inv_one, one_mul]
  have hlt : A.valuation (g ζ * ζ⁻¹ - 1) < 1 := by
    have e : g ζ * ζ⁻¹ - 1 = (g ζ - ζ) * ζ⁻¹ := by field_simp
    rw [e, map_mul, map_inv₀, hv1, inv_one, mul_one]
    exact hd
  have h1 := thetaEx_eta A hm hw hpow hlt
  have : g ζ = ζ := by
    have := congrArg (· * ζ) h1
    simpa [hz] using this
  exact this

/- English proof (translation)
Establish `hc : Nat.card (ZMod w)ˣ = w - 1`. Rewrite using `[Nat.card_eq_fintype_card, ZMod.card_units]`. Establish `hd : l ∣ Nat.card (ZMod w)ˣ` using `hc ▸ h`. Set `e` to `(zmodCyclicMulEquiv (inferInstance : IsCyclic (ZMod w)ˣ)).symm`. Set `ψ : Multiplicative (ZMod (Nat.card (ZMod w)ˣ)) →* Multiplicative (ZMod l)` to `AddMonoidHom.toMultiplicative (ZMod.castHom hd (ZMod l)).toAddMonoidHom`.

Use `⟨ψ.comp e.toMonoidHom, e.symm (Multiplicative.ofAdd 1), ?_⟩` and prove the remaining obligations. Simplify using `only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]`. Use `show Multiplicative.ofAdd ((ZMod.castHom hd (ZMod l)) 1) ≠ 1`. Rewrite using `[map_one, ne_eq, ofAdd_eq_one]`. Conclude with `(one_ne_zero : (1 : ZMod l) ≠ 0)`.
-/
private theorem thetaEx_hom (l w : ℕ) [hl : Fact l.Prime] [hw : Fact w.Prime] (h : l ∣ w - 1) :
    ∃ φ : (ZMod w)ˣ →* Multiplicative (ZMod l), ∃ b, φ b ≠ 1 := by
  have hc : Nat.card (ZMod w)ˣ = w - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hd : l ∣ Nat.card (ZMod w)ˣ := hc ▸ h
  let e := (zmodCyclicMulEquiv (inferInstance : IsCyclic (ZMod w)ˣ)).symm
  let ψ : Multiplicative (ZMod (Nat.card (ZMod w)ˣ)) →* Multiplicative (ZMod l) :=
    AddMonoidHom.toMultiplicative (ZMod.castHom hd (ZMod l)).toAddMonoidHom
  refine ⟨ψ.comp e.toMonoidHom, e.symm (Multiplicative.ofAdd 1), ?_⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  show Multiplicative.ofAdd ((ZMod.castHom hd (ZMod l)) 1) ≠ 1
  rw [map_one, ne_eq, ofAdd_eq_one]
  exact (one_ne_zero : (1 : ZMod l) ≠ 0)

/- English proof (translation)
Introduce `Ω _ _ _ l _ w hw h`. Use `haveI : Fact w.Prime := ⟨hw⟩`. Use `haveI : NeZero w := ⟨hw.ne_zero⟩`. Use `haveI : Fact (1 < w) := ⟨hw.one_lt⟩`. Take `⟨φ, b, hb⟩` from `thetaEx_hom l w h`.

Use `⟨φ.comp (UpperTheory.V.B1.cycN ℚ Ω w), ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `ho` using `(UpperTheory.V.B1.cycCompat ℚ Ω w).1`. Use `Subgroup.isOpen_mono ?_ ho` and prove the remaining obligations. Introduce `g hg`. Rewrite `hg`, the goal using `[MonoidHom.mem_ker]`.

Rewrite using `[MonoidHom.comp_apply, hg, map_one]`. Introduce `A hA g hg`. Rewrite using `[MonoidHom.mem_ker, MonoidHom.comp_apply]`. Establish `hA'` using `hA`. Unfold `Raw.Away at hA'`.

Establish `h1 : UpperTheory.V.B1.cycN ℚ Ω w g = 1`. Rewrite using `[UpperTheory.V.B1.cycN_eq_iff]`. Introduce `ζ hζ`. Rewrite using `[Units.val_one, ZMod.val_one, pow_one]`. Conclude with `thetaEx_fix A hw.ne_zero (hA' w (Finset.mem_singleton_self w)) hζ g hg`.

Rewrite using `[h1, map_one]`. Introduce `A hA`. Establish `hmap` using `UpperTheory.V.B1.cycIne Ω w w A hA`. Establish `hb' : b ∈ UpperTheory.V.B3.pPart w w`. Unfold `UpperTheory.V.B3.pPart`.

Rewrite using `[MonoidHom.mem_ker]`. Establish `hk : ordCompl[w] w = 1`. Rewrite using `[hw.factorization_self, pow_one, Nat.div_self hw.pos]`. Use `haveI : Subsingleton (ZMod (ordCompl[w] w)) := by`. Rewrite using `[ZMod.subsingleton_iff]`.

Conclude with `hk`. Conclude with `Subsingleton.elim _ _`. Rewrite `hb'` using `[← hmap]`. Take `⟨g, hg, hgb⟩` from `hb'`. Use `⟨g, hg, ?_⟩` and prove the remaining obligations.

Rewrite using `[MonoidHom.comp_apply, hgb]`. Conclude with `hb`.
-/
theorem UpperTheory.V.Ws.Rt.thetaEx :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (w : ℕ), w.Prime → l ∣ w - 1 →
      ∃ θ : G ℚ Ω →* Multiplicative (ZMod l), IsOpen (θ.ker : Set (G ℚ Ω)) ∧ (∀ A, Raw.Away {w} A → Ine (F := ℚ) A ≤ θ.ker) ∧
        ∀ A : ValuationSubring Ω, A.valuation (w : Ω) < 1 → ∃ g ∈ Ine (F := ℚ) A, θ g ≠ 1 := by
  intro Ω _ _ _ l _ w hw h
  haveI : Fact w.Prime := ⟨hw⟩
  haveI : NeZero w := ⟨hw.ne_zero⟩
  haveI : Fact (1 < w) := ⟨hw.one_lt⟩
  obtain ⟨φ, b, hb⟩ := thetaEx_hom l w h
  refine ⟨φ.comp (UpperTheory.V.B1.cycN ℚ Ω w), ?_, ?_, ?_⟩
  · have ho := (UpperTheory.V.B1.cycCompat ℚ Ω w).1
    refine Subgroup.isOpen_mono ?_ ho
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    rw [MonoidHom.comp_apply, hg, map_one]
  · intro A hA g hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    have hA' := hA
    unfold Raw.Away at hA'
    have h1 : UpperTheory.V.B1.cycN ℚ Ω w g = 1 := by
      rw [UpperTheory.V.B1.cycN_eq_iff]
      intro ζ hζ
      rw [Units.val_one, ZMod.val_one, pow_one]
      exact thetaEx_fix A hw.ne_zero (hA' w (Finset.mem_singleton_self w)) hζ g hg
    rw [h1, map_one]
  · intro A hA
    have hmap := UpperTheory.V.B1.cycIne Ω w w A hA
    have hb' : b ∈ UpperTheory.V.B3.pPart w w := by
      unfold UpperTheory.V.B3.pPart
      rw [MonoidHom.mem_ker]
      have hk : ordCompl[w] w = 1 := by
        rw [hw.factorization_self, pow_one, Nat.div_self hw.pos]
      haveI : Subsingleton (ZMod (ordCompl[w] w)) := by
        rw [ZMod.subsingleton_iff]
        exact hk
      exact Subsingleton.elim _ _
    rw [← hmap] at hb'
    obtain ⟨g, hg, hgb⟩ := hb'
    refine ⟨g, hg, ?_⟩
    rw [MonoidHom.comp_apply, hgb]
    exact hb
