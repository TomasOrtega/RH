import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPowRootOfUnity

noncomputable section

open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.LKRes GlobalTheory.LKRes.ResSplit

namespace GlobalTheory.LKRes.ResSplit.Tau

/- English proof (translation)
Establish `h' : a % N = b % N` using `h`. Rewrite using `[← Nat.mod_add_div a N, ← Nat.mod_add_div b N, pow_add, pow_add, pow_mul, pow_mul, hζ, one_pow, one_pow, h']`.
-/
theorem pow_eq_pow_of_modEq' {M : Type*} [Monoid M] {ζ : M} {N a b : ℕ} (hζ : ζ ^ N = 1)
    (h : a ≡ b [MOD N]) : ζ ^ a = ζ ^ b := by
  have h' : a % N = b % N := h
  rw [← Nat.mod_add_div a N, ← Nat.mod_add_div b N, pow_add, pow_add, pow_mul, pow_mul, hζ, one_pow,
    one_pow, h']

/- English proof (translation)
Establish `h1 : p ^ r ≡ 1 [MOD p ^ r - 1]` using `((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp)).2 dvd_rfl).symm`. Establish `h2` using `(Nat.ModEq.pow (a / r) h1).mul_left (p ^ (a % r))`. Rewrite `h2` using `[one_pow, mul_one, ← pow_mul, ← pow_add, Nat.mod_add_div]`. Conclude with `h2`.
-/
theorem pow_modEq_pow_mod (p r a : ℕ) (hp : 1 ≤ p) : p ^ a ≡ p ^ (a % r) [MOD p ^ r - 1] := by
  have h1 : p ^ r ≡ 1 [MOD p ^ r - 1] := ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp)).2 dvd_rfl).symm
  have h2 := (Nat.ModEq.pow (a / r) h1).mul_left (p ^ (a % r))
  rw [one_pow, mul_one, ← pow_mul, ← pow_add, Nat.mod_add_div] at h2
  exact h2

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rfl`. Consider the case `succ n ih => rw [pow_succ', AlgEquiv.mul_apply, ih, h]`.
-/
theorem pow_fix {σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p} {x : PadicAlgCl p} (h : σ x = x) (n : ℕ) :
    (σ ^ n) x = x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', AlgEquiv.mul_apply, ih, h]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `h1 : (ζ ^ q ^ n) ^ N = 1` using `by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]`. Rewrite using `[pow_succ', AlgEquiv.mul_apply, ih, h _ h1, ← pow_mul, pow_succ]`.
-/
theorem pow_apply_root' {σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p} {q N : ℕ}
    (h : ∀ ζ : PadicAlgCl p, ζ ^ N = 1 → σ ζ = ζ ^ q) {ζ : PadicAlgCl p} (hζ : ζ ^ N = 1) (k : ℕ) :
    (σ ^ k) ζ = ζ ^ q ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    have h1 : (ζ ^ q ^ n) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
    rw [pow_succ', AlgEquiv.mul_apply, ih, h _ h1, ← pow_mul, pow_succ]

/- English proof (translation)
Establish `h` using `(IsFrobOn.pow_fixes_iff p K hK hm ((isFrob_frobK hK).isFrobOn m) (m * (a / m))).2 (dvd_mul_right _ _)`. Use `conv_lhs => rw [← Nat.mod_add_div a m, pow_add, AlgEquiv.mul_apply, h x hx]`.
-/
theorem frob_pow_mod (hK : FiniteDimensional ℚ_[p] K) {m : ℕ} (hm : 0 < m) {x : PadicAlgCl p}
    (hx : x ∈ Kn p K m) (a : ℕ) : (frobK p K ^ a) x = (frobK p K ^ (a % m)) x := by
  have h := (IsFrobOn.pow_fixes_iff p K hK hm ((isFrob_frobK hK).isFrobOn m) (m * (a / m))).2
    (dvd_mul_right _ _)
  conv_lhs => rw [← Nat.mod_add_div a m, pow_add, AlgEquiv.mul_apply, h x hx]

/- English proof (translation)
Introduce `p _ K hK f r hq hr`. Establish `hp0 : 0 < p` using `(Nat.Prime.one_lt Fact.out).le`. Establish `hd0 : 0 < Nat.gcd f r` using `Nat.gcd_pos_of_pos_right f hr`. Establish `hm0 : 0 < r / Nat.gcd f r` using `Nat.div_pos (Nat.gcd_le_right (m := f) (n := r) hr) hd0`. Establish `hrdm : r = Nat.gcd f r * (r / Nat.gcd f r)` using `(Nat.mul_div_cancel' (Nat.gcd_dvd_right f r)).symm`.

Establish `hfdf : f = Nat.gcd f r * (f / Nat.gcd f r)` using `(Nat.mul_div_cancel' (Nat.gcd_dvd_left f r)).symm`. Establish `hcop : Nat.Coprime (f / Nat.gcd f r) (r / Nat.gcd f r)` using `Nat.coprime_div_gcd_div_gcd hd0`. Use `set d := Nat.gcd f r with hd`. Use `set m := r / d with hm`. Use `set f' := f / d with hf'`.

Use `set k := f' ^ (Nat.totient m - 1) with hk`. Establish `hk1 : f' * k ≡ 1 [MOD m]`. Establish `ht : 0 < Nat.totient m` using `Nat.totient_pos.2 hm0`. Use `Nat.ModEq.pow_totient hcop` as an intermediate fact. Rewrite `this` using `[← Nat.sub_add_cancel ht, pow_succ']`. Then use the resulting hypothesis.

Establish `hk2 : f * k ≡ d [MOD r]`. Use `Nat.ModEq.mul_left' d hk1` as an intermediate fact. Rewrite `this` using `[mul_one, ← mul_assoc, ← hfdf, ← hrdm]`. Conclude with `this`. Set `σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p` to `frobK p K ^ k`.

Establish `hσ : ∀ x ∈ Kn p K m, σ x ∈ Kn p K m` using `fun x hx => UnramifiedExtensions.map_mem_Kn K m σ hx`. Establish `hσ' : ∀ x ∈ Kn p K m, σ⁻¹ x ∈ Kn p K m` using `fun x hx => UnramifiedExtensions.map_mem_Kn K m σ⁻¹ hx`. Set `τ : Kn p K m ≃+* Kn p K m` to `{ toFun := fun x => ⟨σ x, hσ x x.2⟩ invFun := fun x => ⟨σ⁻¹ x, hσ' x x.2⟩ left_inv := fun x => Subtype.ext (by show σ⁻¹ (σ (x : PadicAlgCl p)) = x`. Rewrite using `[AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply])`. Use `right_inv := fun x => Subtype.ext (by show σ (σ⁻¹ (x : PadicAlgCl p)) = x`.

Rewrite using `[AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply])`. Use the proof step `map_mul' := fun x y => Subtype.ext (map_mul σ (x : PadicAlgCl p) y)`. Use the proof step `map_add' := fun x y => Subtype.ext (map_add σ (x : PadicAlgCl p) y) }`. Establish `hτ : ∀ x, ((τ x : Kn p K m) : PadicAlgCl p) = σ x` using `fun _ => rfl`. Use `⟨τ, fun x => ⟨fun h => ?_, fun h => ?_⟩, fun x => ?_, fun b => ?_⟩` and prove the remaining obligations.

Establish `h1 : σ x = x` using `by rw [← hτ, h]`. Establish `h2 : (frobK p K ^ (k * f')) x = x` using `by rw [pow_mul]; exact pow_fix h1 f'`. Establish `h3 : frobK p K (x : PadicAlgCl p) = x`. Establish `e` using `frob_pow_mod hK hm0 x.2 (k * f')`. Establish `e1` using `frob_pow_mod hK hm0 x.2 1`.

Rewrite `e1` using `[pow_one]`. Establish `e2 : (k * f') % m = 1 % m` using `by rw [mul_comm]; exact hk1`. Rewrite using `[e1, ← e2, ← e, h2]`. Conclude with `mem_of_frobK_fixed hK (Kn_le_Kur hm0 x.2) h3`. Conclude with `Subtype.ext (show σ (x : PadicAlgCl p) = x from σ.commutes ⟨x, h⟩)`.

Establish `hit : ∀ n (y : Kn p K m), (((⇑τ)^[n] y : Kn p K m) : PadicAlgCl p) = (σ ^ n) y`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro y`. Both sides reduce to the same expression.

Consider the case `succ n ih`. Introduce `y`. Rewrite using `[Function.iterate_succ_apply', pow_succ', AlgEquiv.mul_apply, ← ih]`. Both sides reduce to the same expression. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[hit, ← pow_mul, frob_pow_mod hK hm0 x.2, show k * m % m = 0 by simp, pow_zero]`. Both sides reduce to the same expression. Establish `hN : ¬ p ∣ p ^ r - 1`. Introduce `h`. Establish `h2` using `Nat.dvd_sub (dvd_pow_self p hr.ne') h`.

Rewrite `h2` using `[Nat.sub_sub_self (Nat.one_le_pow _ _ hp0)]`. Conclude with `(Nat.Prime.one_lt Fact.out).ne' (Nat.dvd_one.1 h2)`. Establish `hpow : p ^ (f * k) ≡ p ^ d [MOD p ^ r - 1]`. Establish `e` using `pow_modEq_pow_mod p r (f * k) hp0`. Rewrite `e` using `[show f * k % r = d % r from hk2]`.

Conclude with `e.trans (pow_modEq_pow_mod p r d hp0).symm`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hτ, coe_incQ, coe_incQ, coe_frobQ_pow]`. Use `UnramifiedExtensions.eqOn_Kn (Q0 p) (σ := resGK bot_le σ) (τ := frobK p (Q0 p) ^ d) (fun ζ hζ => ?_) b.2` and prove the remaining obligations. Rewrite `hζ` using `[residue_cardinality_base_field]`.

Rewrite using `[resGK_apply, frobenius_pow_root_of_unity p hN hζ d]`. Establish `hfr` using `fun ζ' hζ' => (isFrob_iff hK (frobK p K)).1 (isFrob_frobK hK) ζ' (p ^ r - 1) hN hζ'`. Use `show (frobK p K ^ k) ζ = _`. Rewrite using `[pow_apply_root' hfr hζ k, hq, ← pow_mul]`. Conclude with `pow_eq_pow_of_modEq' hζ hpow`.
-/
theorem exists_tau : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
    FiniteDimensional ℚ_[p] K → ∀ (f r : ℕ) (hq : qK p K = p ^ f), 0 < r →
    ∃ τ : Kn p K (r / Nat.gcd f r) ≃+* Kn p K (r / Nat.gcd f r),
      (∀ x, τ x = x ↔ (x : PadicAlgCl p) ∈ K) ∧ (∀ x, (⇑τ)^[r / Nat.gcd f r] x = x) ∧
      ∀ b : Qr p r, τ (incQ p K hq r b) = incQ p K hq r ((frobQ p r ^ Nat.gcd f r) b) := by
  intro p _ K hK f r hq hr
  have hp0 : 0 < p := (Nat.Prime.one_lt Fact.out).le
  have hd0 : 0 < Nat.gcd f r := Nat.gcd_pos_of_pos_right f hr
  have hm0 : 0 < r / Nat.gcd f r := Nat.div_pos (Nat.gcd_le_right (m := f) (n := r) hr) hd0
  have hrdm : r = Nat.gcd f r * (r / Nat.gcd f r) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right f r)).symm
  have hfdf : f = Nat.gcd f r * (f / Nat.gcd f r) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left f r)).symm
  have hcop : Nat.Coprime (f / Nat.gcd f r) (r / Nat.gcd f r) := Nat.coprime_div_gcd_div_gcd hd0
  set d := Nat.gcd f r with hd
  set m := r / d with hm
  set f' := f / d with hf'
  set k := f' ^ (Nat.totient m - 1) with hk
  have hk1 : f' * k ≡ 1 [MOD m] := by
    have ht : 0 < Nat.totient m := Nat.totient_pos.2 hm0
    have := Nat.ModEq.pow_totient hcop
    rwa [← Nat.sub_add_cancel ht, pow_succ'] at this
  have hk2 : f * k ≡ d [MOD r] := by
    have := Nat.ModEq.mul_left' d hk1
    rw [mul_one, ← mul_assoc, ← hfdf, ← hrdm] at this
    exact this
  let σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p := frobK p K ^ k
  have hσ : ∀ x ∈ Kn p K m, σ x ∈ Kn p K m := fun x hx => UnramifiedExtensions.map_mem_Kn K m σ hx
  have hσ' : ∀ x ∈ Kn p K m, σ⁻¹ x ∈ Kn p K m := fun x hx => UnramifiedExtensions.map_mem_Kn K m σ⁻¹ hx
  let τ : Kn p K m ≃+* Kn p K m :=
    { toFun := fun x => ⟨σ x, hσ x x.2⟩
      invFun := fun x => ⟨σ⁻¹ x, hσ' x x.2⟩
      left_inv := fun x => Subtype.ext (by
        show σ⁻¹ (σ (x : PadicAlgCl p)) = x
        rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply])
      right_inv := fun x => Subtype.ext (by
        show σ (σ⁻¹ (x : PadicAlgCl p)) = x
        rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply])
      map_mul' := fun x y => Subtype.ext (map_mul σ (x : PadicAlgCl p) y)
      map_add' := fun x y => Subtype.ext (map_add σ (x : PadicAlgCl p) y) }
  have hτ : ∀ x, ((τ x : Kn p K m) : PadicAlgCl p) = σ x := fun _ => rfl
  refine ⟨τ, fun x => ⟨fun h => ?_, fun h => ?_⟩, fun x => ?_, fun b => ?_⟩
  · have h1 : σ x = x := by rw [← hτ, h]
    have h2 : (frobK p K ^ (k * f')) x = x := by rw [pow_mul]; exact pow_fix h1 f'
    have h3 : frobK p K (x : PadicAlgCl p) = x := by
      have e := frob_pow_mod hK hm0 x.2 (k * f')
      have e1 := frob_pow_mod hK hm0 x.2 1
      rw [pow_one] at e1
      have e2 : (k * f') % m = 1 % m := by rw [mul_comm]; exact hk1
      rw [e1, ← e2, ← e, h2]
    exact mem_of_frobK_fixed hK (Kn_le_Kur hm0 x.2) h3
  · exact Subtype.ext (show σ (x : PadicAlgCl p) = x from σ.commutes ⟨x, h⟩)
  · have hit : ∀ n (y : Kn p K m), (((⇑τ)^[n] y : Kn p K m) : PadicAlgCl p) = (σ ^ n) y := by
      intro n
      induction n with
      | zero => intro y; rfl
      | succ n ih =>
        intro y
        rw [Function.iterate_succ_apply', pow_succ', AlgEquiv.mul_apply, ← ih]
        rfl
    apply Subtype.ext
    rw [hit, ← pow_mul, frob_pow_mod hK hm0 x.2, show k * m % m = 0 by simp, pow_zero]
    rfl
  · have hN : ¬ p ∣ p ^ r - 1 := by
      intro h
      have h2 := Nat.dvd_sub (dvd_pow_self p hr.ne') h
      rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp0)] at h2
      exact (Nat.Prime.one_lt Fact.out).ne' (Nat.dvd_one.1 h2)
    have hpow : p ^ (f * k) ≡ p ^ d [MOD p ^ r - 1] := by
      have e := pow_modEq_pow_mod p r (f * k) hp0
      rw [show f * k % r = d % r from hk2] at e
      exact e.trans (pow_modEq_pow_mod p r d hp0).symm
    apply Subtype.ext
    rw [hτ, coe_incQ, coe_incQ, coe_frobQ_pow]
    refine UnramifiedExtensions.eqOn_Kn (Q0 p) (σ := resGK bot_le σ) (τ := frobK p (Q0 p) ^ d) (fun ζ hζ => ?_) b.2
    rw [residue_cardinality_base_field] at hζ
    rw [resGK_apply, frobenius_pow_root_of_unity p hN hζ d]
    have hfr := fun ζ' hζ' => (isFrob_iff hK (frobK p K)).1 (isFrob_frobK hK) ζ' (p ^ r - 1) hN hζ'
    show (frobK p K ^ k) ζ = _
    rw [pow_apply_root' hfr hζ k, hq, ← pow_mul]
    exact pow_eq_pow_of_modEq' hζ hpow

end GlobalTheory.LKRes.ResSplit.Tau
