import Mathlib
open PowerSeries

namespace GlobalTheory

/- English proof (translation)
Establish `key : ∀ p : ℕ, p.Prime → ∀ ε : ℤ_[l], ε ^ p = 1 → PadicInt.toZMod ε = 1 → ε = 1`. Introduce `p hp ε hε he1`. Assume the negation of the conclusion as `hne`. Establish `hsum : ∑ i ∈ Finset.range p, ε ^ i = 0`. Use `geom_sum_mul ε p` as an intermediate fact.

Rewrite `this` using `[hε, sub_self]`. Conclude with `(mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)`. Establish `hp0 : (p : ZMod l) = 0`. Use `congrArg PadicInt.toZMod hsum` as an intermediate fact. Simplify `this` using `[map_sum, map_pow, he1]`.

Establish `hpl : l = p` using `(Nat.prime_dvd_prime_iff_eq hl.out hp).mp ((ZMod.natCast_eq_zero_iff _ _).mp hp0)`. Substitute `hpl` using the available equality. Establish `hmem : ∀ z : ℤ_[l], (l : ℤ_[l]) ∣ z ↔ PadicInt.toZMod z = 0`. Introduce `z`. Rewrite using `[← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]`.

Establish `h` using `emultiplicity_geom_sum₂_eq_one (p := l) (x := ε) (y := 1) PadicInt.prime_p (hl.out.odd_of_ne_two h2) ((hmem _).mpr (by simp [he1])) (by rw [hmem, he1]; exact one_ne_zero)`. Simplify using `[hsum] at h`. Proceed by induction on `n using Nat.recOnMul generalizing δ with`. Consider the case `zero => exact absurd rfl hn`. Consider the case `one => simpa using hδ`.

Consider the case `prime p hp => exact key p hp δ hδ h1`. Consider the case `mul a b iha ihb`. Establish `ha : a ≠ 0` using `left_ne_zero_of_mul hn`. Establish `hb : b ≠ 0` using `right_ne_zero_of_mul hn`. Use `iha δ ha (ihb (δ ^ a) hb (by rw [← pow_mul, hδ]) (by rw [map_pow, h1, one_pow])) h1` and prove the remaining obligations.
-/
theorem padicInt_eq_one_of_pow_eq_one_of_toZMod_eq_one {l : ℕ} [hl : Fact l.Prime] (h2 : l ≠ 2)
    (δ : ℤ_[l]) {n : ℕ} (hn : n ≠ 0) (hδ : δ ^ n = 1) (h1 : PadicInt.toZMod δ = 1) : δ = 1 := by
  have key : ∀ p : ℕ, p.Prime → ∀ ε : ℤ_[l], ε ^ p = 1 → PadicInt.toZMod ε = 1 → ε = 1 := by
    intro p hp ε hε he1
    by_contra hne
    have hsum : ∑ i ∈ Finset.range p, ε ^ i = 0 := by
      have := geom_sum_mul ε p
      rw [hε, sub_self] at this
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
    have hp0 : (p : ZMod l) = 0 := by
      have := congrArg PadicInt.toZMod hsum
      simpa [map_sum, map_pow, he1] using this
    have hpl : l = p := (Nat.prime_dvd_prime_iff_eq hl.out hp).mp ((ZMod.natCast_eq_zero_iff _ _).mp hp0)
    subst hpl
    have hmem : ∀ z : ℤ_[l], (l : ℤ_[l]) ∣ z ↔ PadicInt.toZMod z = 0 := by
      intro z
      rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
        Ideal.mem_span_singleton]
    have h := emultiplicity_geom_sum₂_eq_one (p := l) (x := ε) (y := 1) PadicInt.prime_p
      (hl.out.odd_of_ne_two h2) ((hmem _).mpr (by simp [he1])) (by rw [hmem, he1]; exact one_ne_zero)
    simp [hsum] at h
  induction n using Nat.recOnMul generalizing δ with
  | zero => exact absurd rfl hn
  | one => simpa using hδ
  | prime p hp => exact key p hp δ hδ h1
  | mul a b iha ihb =>
    have ha : a ≠ 0 := left_ne_zero_of_mul hn
    have hb : b ≠ 0 := right_ne_zero_of_mul hn
    refine iha δ ha (ihb (δ ^ a) hb (by rw [← pow_mul, hδ]) (by rw [map_pow, h1, one_pow])) h1

/- English proof (translation)
Set `g : Δ →* (ZMod l)ˣ` to `(Units.map (PadicInt.toZMod (p := l) : ℤ_[l] →+* ZMod l).toMonoidHom).comp Δ.subtype`. Establish `hg : ∀ d : Δ, (g d : ZMod l) = PadicInt.toZMod ((d : ℤ_[l]ˣ) : ℤ_[l])` using `fun _ => rfl`. Establish `hs : Nat.card Δ ≠ 0` using `Nat.card_pos.ne'`. Establish `hinj : Function.Injective g`. Rewrite using `[injective_iff_map_eq_one]`.

Introduce `d hd`. Establish `h1 : PadicInt.toZMod ((d : ℤ_[l]ˣ) : ℤ_[l]) = 1` using `by rw [← hg, hd]; rfl`. Establish `hp : ((d : ℤ_[l]ˣ) : ℤ_[l]) ^ Nat.card Δ = 1`. Establish `: d ^ Nat.card Δ = 1` using `pow_card_eq_one'`. Use `congrArg (fun z : Δ => ((z : ℤ_[l]ˣ) : ℤ_[l])) this` as an intermediate fact.

Simplify `this` using `only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one]`. Conclude with `Subtype.ext (Units.ext (padicInt_eq_one_of_pow_eq_one_of_toZMod_eq_one h2 _ hs hp h1))`. Set `H : Subgroup (ZMod l)ˣ` to `g.range`. Establish `hH : Nat.card H = Nat.card Δ` using `(Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm`. Establish `hHmem : ∀ x : (ZMod l)ˣ, x ^ Nat.card Δ = 1 → x ∈ H`.

Introduce `x hx`. Establish `hle : H ≤ (powMonoidHom (Nat.card Δ) : (ZMod l)ˣ →* (ZMod l)ˣ).ker`. Introduce `y hy`. Establish `: (⟨y, hy⟩ : H) ^ Nat.card H = 1` using `pow_card_eq_one'`. Rewrite `this` using `[hH]`.

Simplify using `using congrArg Subtype.val this`. Establish `hc : Nat.card (powMonoidHom (Nat.card Δ) : (ZMod l)ˣ →* (ZMod l)ˣ).ker ≤ Nat.card H`. Rewrite using `[IsCyclic.card_powMonoidHom_ker, hH]`. Conclude with `Nat.gcd_le_right _ (Nat.pos_of_ne_zero hs)`. Rewrite using `[Subgroup.eq_of_le_of_card_ge hle hc]`.

Simplify using `using hx`. Set `φ : ((ZMod l)ˣ ⧸ H) ≃ Fin (Nat.card ((ZMod l)ˣ ⧸ H))` to `Finite.equivFin _`. Set `r : Fin (Nat.card ((ZMod l)ˣ ⧸ H)) → (ZMod l)ˣ` to `fun τ => (φ.symm τ).out`. Establish `hr : ∀ τ, ((r τ : (ZMod l)ˣ) : (ZMod l)ˣ ⧸ H) = φ.symm τ` using `fun τ => Quotient.out_eq _`. Establish `hcast : ∀ τ, (((r τ : ZMod l).val : ℕ) : ZMod l) = r τ` using `fun τ => ZMod.natCast_zmod_val _`.

Establish `hreq : ∀ τ τ', (r τ)⁻¹ * r τ' ∈ H → τ = τ'`. Introduce `τ τ' h`. Use `QuotientGroup.eq.mpr h` as an intermediate fact. Rewrite `this` using `[hr, hr]`. Conclude with `φ.symm.injective this`.

Use `⟨_, fun τ => (r τ : ZMod l).val, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hH, ← Subgroup.card_eq_card_quotient_mul_card_subgroup, Nat.card_eq_fintype_card, ZMod.card_units]`. Introduce `τ h`. Use `(ZMod.natCast_eq_zero_iff _ _).mpr h` as an intermediate fact. Rewrite `this` using `[hcast]`.

Conclude with `(r τ).ne_zero this`. Introduce `τ τ' hne h`. Simplify using `only [hcast] at h`. Establish `h' : r τ ^ Nat.card Δ = r τ' ^ Nat.card Δ` using `Units.ext (by simpa using h)`. Conclude with `hne (hreq _ _ (hHmem _ (by rw [mul_pow, inv_pow, h', inv_mul_cancel])))`.

Introduce `x hx`. Set `u : (ZMod l)ˣ` to `Units.mk0 x hx`. Establish `hu : (r (φ u))⁻¹ * u ∈ H`. Rewrite using `[← QuotientGroup.eq, hr, Equiv.symm_apply_apply]`. Take `⟨d, hd⟩` from `hu`.

Establish `hform : ∀ p : Fin (Nat.card ((ZMod l)ˣ ⧸ H)) × Δ, x = (((r p.1 : ZMod l).val : ℕ) : ZMod l) * PadicInt.toZMod ((p.2 : ℤ_[l]ˣ) : ℤ_[l]) ↔ u = r p.1 * g p.2`. Introduce `p`. Rewrite using `[hcast, ← hg, Units.ext_iff]`. Both sides reduce to the same expression. Establish `hd' : u = r (φ u) * g d` using `by rw [hd, mul_inv_cancel_left]`.

Use `⟨(φ u, d), (hform _).mpr hd', ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨τ, d'⟩ hp`. Establish `hp' : u = r τ * g d'` using `(hform _).mp hp`. Establish `hτ : τ = φ u`. Apply `hreq` to reduce the goal to its premises.

Use `⟨d' * d⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_inv, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← hp', mul_inv_eq_iff_eq_mul]`. Conclude with `hd'`. Rewrite `hp'` using `[hτ]`. Establish `: g d' = g d` using `mul_left_cancel (hp'.symm.trans hd')`.

Rewrite using `[hτ, hinj this]`.
-/
theorem exists_coset_representatives_of_finite_subgroup_padicInt_units {l : ℕ} [hl : Fact l.Prime]
    (Δ : Subgroup ℤ_[l]ˣ) [Finite Δ] (h2 : l ≠ 2) :
    ∃ (e : ℕ) (a : Fin e → ℕ), e * Nat.card Δ = l - 1 ∧ (∀ τ, ¬ l ∣ a τ) ∧
      (∀ τ τ', τ ≠ τ' → (a τ : ZMod l) ^ Nat.card Δ ≠ (a τ' : ZMod l) ^ Nat.card Δ) ∧
      ∀ x : ZMod l, x ≠ 0 → ∃! p : Fin e × Δ,
        x = (a p.1 : ZMod l) * PadicInt.toZMod ((p.2 : ℤ_[l]ˣ) : ℤ_[l]) := by
  classical
  let g : Δ →* (ZMod l)ˣ :=
    (Units.map (PadicInt.toZMod (p := l) : ℤ_[l] →+* ZMod l).toMonoidHom).comp Δ.subtype
  have hg : ∀ d : Δ, (g d : ZMod l) = PadicInt.toZMod ((d : ℤ_[l]ˣ) : ℤ_[l]) := fun _ => rfl
  have hs : Nat.card Δ ≠ 0 := Nat.card_pos.ne'
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have h1 : PadicInt.toZMod ((d : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by rw [← hg, hd]; rfl
    have hp : ((d : ℤ_[l]ˣ) : ℤ_[l]) ^ Nat.card Δ = 1 := by
      have : d ^ Nat.card Δ = 1 := pow_card_eq_one'
      have := congrArg (fun z : Δ => ((z : ℤ_[l]ˣ) : ℤ_[l])) this
      simpa only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
        Units.val_one] using this
    exact Subtype.ext (Units.ext (padicInt_eq_one_of_pow_eq_one_of_toZMod_eq_one h2 _ hs hp h1))
  let H : Subgroup (ZMod l)ˣ := g.range
  have hH : Nat.card H = Nat.card Δ := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hHmem : ∀ x : (ZMod l)ˣ, x ^ Nat.card Δ = 1 → x ∈ H := by
    intro x hx
    have hle : H ≤ (powMonoidHom (Nat.card Δ) : (ZMod l)ˣ →* (ZMod l)ˣ).ker := by
      intro y hy
      have : (⟨y, hy⟩ : H) ^ Nat.card H = 1 := pow_card_eq_one'
      rw [hH] at this
      simpa using congrArg Subtype.val this
    have hc : Nat.card (powMonoidHom (Nat.card Δ) : (ZMod l)ˣ →* (ZMod l)ˣ).ker ≤ Nat.card H := by
      rw [IsCyclic.card_powMonoidHom_ker, hH]
      exact Nat.gcd_le_right _ (Nat.pos_of_ne_zero hs)
    rw [Subgroup.eq_of_le_of_card_ge hle hc]
    simpa using hx
  let φ : ((ZMod l)ˣ ⧸ H) ≃ Fin (Nat.card ((ZMod l)ˣ ⧸ H)) := Finite.equivFin _
  let r : Fin (Nat.card ((ZMod l)ˣ ⧸ H)) → (ZMod l)ˣ := fun τ => (φ.symm τ).out
  have hr : ∀ τ, ((r τ : (ZMod l)ˣ) : (ZMod l)ˣ ⧸ H) = φ.symm τ := fun τ => Quotient.out_eq _
  have hcast : ∀ τ, (((r τ : ZMod l).val : ℕ) : ZMod l) = r τ := fun τ => ZMod.natCast_zmod_val _
  have hreq : ∀ τ τ', (r τ)⁻¹ * r τ' ∈ H → τ = τ' := by
    intro τ τ' h
    have := QuotientGroup.eq.mpr h
    rw [hr, hr] at this
    exact φ.symm.injective this
  refine ⟨_, fun τ => (r τ : ZMod l).val, ?_, ?_, ?_, ?_⟩
  · rw [← hH, ← Subgroup.card_eq_card_quotient_mul_card_subgroup, Nat.card_eq_fintype_card,
      ZMod.card_units]
  · intro τ h
    have := (ZMod.natCast_eq_zero_iff _ _).mpr h
    rw [hcast] at this
    exact (r τ).ne_zero this
  · intro τ τ' hne h
    simp only [hcast] at h
    have h' : r τ ^ Nat.card Δ = r τ' ^ Nat.card Δ := Units.ext (by simpa using h)
    exact hne (hreq _ _ (hHmem _ (by rw [mul_pow, inv_pow, h', inv_mul_cancel])))
  · intro x hx
    let u : (ZMod l)ˣ := Units.mk0 x hx
    have hu : (r (φ u))⁻¹ * u ∈ H := by
      rw [← QuotientGroup.eq, hr, Equiv.symm_apply_apply]
    obtain ⟨d, hd⟩ := hu
    have hform : ∀ p : Fin (Nat.card ((ZMod l)ˣ ⧸ H)) × Δ,
        x = (((r p.1 : ZMod l).val : ℕ) : ZMod l) * PadicInt.toZMod ((p.2 : ℤ_[l]ˣ) : ℤ_[l]) ↔
          u = r p.1 * g p.2 := by
      intro p
      rw [hcast, ← hg, Units.ext_iff]
      rfl
    have hd' : u = r (φ u) * g d := by rw [hd, mul_inv_cancel_left]
    refine ⟨(φ u, d), (hform _).mpr hd', ?_⟩
    rintro ⟨τ, d'⟩ hp
    have hp' : u = r τ * g d' := (hform _).mp hp
    have hτ : τ = φ u := by
      apply hreq
      refine ⟨d' * d⁻¹, ?_⟩
      rw [map_mul, map_inv, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← hp', mul_inv_eq_iff_eq_mul]
      exact hd'
    rw [hτ] at hp'
    have : g d' = g d := mul_left_cancel (hp'.symm.trans hd')
    rw [hτ, hinj this]

end GlobalTheory
