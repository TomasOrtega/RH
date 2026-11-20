import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTwInv

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.CocBound

/- English proof (translation)
Establish `key : ∀ (γ γ' : G), γ ∈ Γ → γ' ∈ Γ → ∀ i j : ℕ, i < j → j < m → γ * a * g ^ i ≠ γ' * a * g ^ j`. Introduce `γ γ' hγ hγ' i j hij hj h`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_lt hij`. Apply `hfree a (d + 1) (by omega) (by omega)` to reduce the goal to its premises. Establish `e : a * g ^ (d + 1) * a⁻¹ = γ'⁻¹ * γ`.

Establish `h2 : γ * a * g ^ i = (γ' * a * g ^ (d + 1)) * g ^ i`. Rewrite using `[h, mul_assoc (γ' * a), ← pow_add]`. Use `congr 2`. Use linear arithmetic over natural numbers and integers. Establish `h3` using `mul_right_cancel h2`.

Rewrite using `[eq_inv_mul_iff_mul_eq, ← mul_assoc, ← mul_assoc, ← h3, mul_inv_cancel_right]`. Rewrite using `[e]`. Conclude with `Γ.mul_mem (Γ.inv_mem hγ') hγ`. Rewrite `h` using `[pow_eq_pow_mod i hg, pow_eq_pow_mod j hg]`. Break down `lt_trichotomy (i % m) (j % m) with hlt | heq | hlt` into its components or cases.

Conclude with `absurd h (key γ γ' hγ hγ' _ _ hlt (Nat.mod_lt _ hm))`. Conclude with `heq`. Conclude with `absurd h.symm (key γ' γ hγ' hγ _ _ hlt (Nat.mod_lt _ hm))`.
-/
theorem free_mod_eq {G : Type} [Group G] (Γ : Subgroup G) (g : G) (m : ℕ) (hm : 0 < m)
    (hg : g ^ m = 1) (hfree : ∀ (x : G) (k : ℕ), 0 < k → k < m → x * g ^ k * x⁻¹ ∉ Γ)
    (a γ γ' : G) (hγ : γ ∈ Γ) (hγ' : γ' ∈ Γ) (i j : ℕ)
    (h : γ * a * g ^ i = γ' * a * g ^ j) : i % m = j % m := by
  have key : ∀ (γ γ' : G), γ ∈ Γ → γ' ∈ Γ → ∀ i j : ℕ, i < j → j < m →
      γ * a * g ^ i ≠ γ' * a * g ^ j := by
    intro γ γ' hγ hγ' i j hij hj h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
    apply hfree a (d + 1) (by omega) (by omega)
    have e : a * g ^ (d + 1) * a⁻¹ = γ'⁻¹ * γ := by
      have h2 : γ * a * g ^ i = (γ' * a * g ^ (d + 1)) * g ^ i := by
        rw [h, mul_assoc (γ' * a), ← pow_add]
        congr 2
        omega
      have h3 := mul_right_cancel h2
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← mul_assoc, ← h3, mul_inv_cancel_right]
    rw [e]
    exact Γ.mul_mem (Γ.inv_mem hγ') hγ
  rw [pow_eq_pow_mod i hg, pow_eq_pow_mod j hg] at h
  rcases lt_trichotomy (i % m) (j % m) with hlt | heq | hlt
  · exact absurd h (key γ γ' hγ hγ' _ _ hlt (Nat.mod_lt _ hm))
  · exact heq
  · exact absurd h.symm (key γ' γ hγ' hγ _ _ hlt (Nat.mod_lt _ hm))

def freeSetoid {G : Type} [Group G] (Γ : Subgroup G) (g : G) (m : ℕ) (hm : 0 < m)
    (hg : g ^ m = 1) : Setoid G where
  r x y := ∃ γ ∈ Γ, ∃ k : ℕ, y = γ * x * g ^ k
  iseqv :=
    { refl := fun x => ⟨1, Γ.one_mem, 0, by simp⟩
      symm := by
        rintro x y ⟨γ, hγ, k, rfl⟩
        refine ⟨γ⁻¹, Γ.inv_mem hγ, k * (m - 1), ?_⟩
        obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hm
        have : g ^ k * g ^ (k * (0 + n + 1 - 1)) = 1 := by
          rw [← pow_add]
          have : k + k * (0 + n + 1 - 1) = (0 + n + 1) * k := by
            simp only [zero_add, Nat.add_sub_cancel]
            ring
          rw [this, pow_mul, hg, one_pow]
        rw [mul_assoc, mul_assoc, this, mul_one, inv_mul_cancel_left]
      trans := by
        rintro x y z ⟨γ, hγ, k, rfl⟩ ⟨δ, hδ, l, rfl⟩
        refine ⟨δ * γ, Γ.mul_mem hδ hγ, k + l, ?_⟩
        simp only [pow_add, mul_assoc] }

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ, ← mul_assoc, hf.2, ih, pow_succ', Module.End.mul_apply]`.
-/
theorem twInv_apply_pow {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]
    {Γ : Subgroup G} {g : G} {A : E →ₗ[ℂ] E} {f : G → E} (hf : f ∈ twInv Γ g A) (x : G) (k : ℕ) :
    f (x * g ^ k) = (A ^ k) (f x) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← mul_assoc, hf.2, ih, pow_succ', Module.End.mul_apply]

/- English proof (translation)
Set `s` to `freeSetoid Γ g m hm hg`. Establish `hs : ∀ x y : G, s.r x y ↔ ∃ γ ∈ Γ, ∃ k : ℕ, y = γ * x * g ^ k` using `fun _ _ => Iff.rfl`. Set `R` to `Quotient s`. Establish `hmk : ∀ γ ∈ Γ, ∀ (x : G) (k : ℕ), Quotient.mk s (γ * x * g ^ k) = Quotient.mk s x` using `fun γ hγ x k => (Quotient.sound (s := s) ((hs _ _).2 ⟨γ, hγ, k, rfl⟩)).symm`. Establish `hout : ∀ x : G, ∃ γ ∈ Γ, ∃ k : ℕ, x = γ * (Quotient.mk s x).out * g ^ k` using `fun x => (hs _ _).1 (Quotient.mk_out (s := s) x)`.

Set `F : R × Fin m → Quotient (QuotientGroup.rightRel Γ)` to `fun p => Quotient.mk _ (p.1.out * g ^ (p.2 : ℕ))`. Establish `hF : Function.Bijective F`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, i⟩ ⟨d, j⟩ h`. Establish `h1` using `QuotientGroup.rightRel_apply.1 (Quotient.exact h)`.

Simplify using `only at h1`. Use `set γ := d.out * g ^ (j : ℕ) * (c.out * g ^ (i : ℕ))⁻¹ with hγ`. Establish `h2 : 1 * d.out * g ^ (j : ℕ) = γ * c.out * g ^ (i : ℕ)`. Rewrite using `[hγ, mul_assoc _ c.out, inv_mul_cancel_right, one_mul]`. Establish `h3 : d = c`.

Use `congrArg (Quotient.mk s) h2` as an intermediate fact. Rewrite `this` using `[hmk 1 Γ.one_mem, hmk γ h1, Quotient.out_eq, Quotient.out_eq]`. Conclude with `this`. Substitute `h3` using the available equality. Establish `h4` using `free_mod_eq Γ g m hm hg hfree _ _ _ Γ.one_mem h1 _ _ h2`.

Rewrite `h4` using `[Nat.mod_eq_of_lt j.2, Nat.mod_eq_of_lt i.2]`. Rewrite using `[Fin.ext h4]`. Introduce `q`. Proceed by induction on `q using Quotient.inductionOn with`. Consider the case `h x`.

Take `⟨γ, hγ, k, hx⟩` from `hout x`. Use `⟨(Quotient.mk s x, ⟨k % m, Nat.mod_lt _ hm⟩), ?_⟩` and prove the remaining obligations. Apply `Quotient.sound` to reduce the goal to its premises. Apply `QuotientGroup.rightRel_apply.2` to reduce the goal to its premises. Simplify using `only`.

Rewrite using `[← pow_eq_pow_mod k hg]`. Establish `: x * ((Quotient.mk s x).out * g ^ k)⁻¹ = γ`. Rewrite using `[mul_inv_eq_iff_eq_mul, ← mul_assoc]`. Conclude with `hx`. Rewrite using `[this]`.

Conclude with `hγ`. Establish `hcard : Nat.card R * m = Γ.index`. Establish `h1` using `Nat.card_congr (Equiv.ofBijective F hF)`. Rewrite `h1` using `[Nat.card_prod, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin, Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ)]`. Conclude with `h1`.

Establish `hR : Finite R`. Apply `Nat.finite_of_card_ne_zero` to reduce the goal to its premises. Introduce `h0`. Rewrite `hcard` using `[h0, zero_mul]`. Conclude with `hΓ.index_ne_zero hcard.symm`.

Use `letI : Fintype R := Fintype.ofFinite R`. Set `ev : twInv Γ g A →ₗ[ℂ] (R → E)` to `{ toFun := fun f c => (f : G → E) c.out map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hev : Function.Bijective ev`. Prove the components needed by the constructor for the conclusion. Introduce `f f' h`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Take `⟨γ, hγ, k, hx⟩` from `hout x`. Establish `h1 : (f : G → E) (Quotient.mk s x).out = (f' : G → E) (Quotient.mk s x).out` using `congrFun h (Quotient.mk s x)`. Rewrite using `[hx, twInv_apply_pow f.2, twInv_apply_pow f'.2, f.2.1 γ hγ, f'.2.1 γ hγ, h1]`.

Introduce `φ choose γ hγ κ hκ using hout`. Establish `hval : ∀ (x δ : G) (k : ℕ), δ ∈ Γ → x = δ * (Quotient.mk s x).out * g ^ k → A ^ κ x = A ^ k`. Introduce `x δ k hδ hx`. Use `free_mod_eq Γ g m hm hg hfree _ _ _ (hγ x) hδ _ _ ((hκ x).symm.trans hx)` as an intermediate fact. Rewrite using `[pow_eq_pow_mod _ hA, this, ← pow_eq_pow_mod _ hA]`.

Use `⟨⟨fun x => (A ^ κ x) (φ (Quotient.mk s x)), ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `δ hδ x`. Establish `e : Quotient.mk s (δ * x) = Quotient.mk s x`. Simplify using `using hmk δ hδ x 0`. Use `hval (δ * x) (δ * γ x) (κ x) (Γ.mul_mem hδ (hγ x)) (by` as an intermediate fact.

Rewrite using `[e, mul_assoc, mul_assoc δ, ← mul_assoc (γ x), ← hκ x])`. Simplify using `only`. Rewrite using `[this, e]`. Introduce `x`. Establish `e : Quotient.mk s (x * g) = Quotient.mk s x`.

Simplify using `using hmk 1 Γ.one_mem x 1`. Use `hval (x * g) (γ x) (κ x + 1) (hγ x) (by` as an intermediate fact. Rewrite using `[e, pow_succ, ← mul_assoc, ← hκ x])`. Simplify using `only`. Rewrite using `[this, e, pow_succ', Module.End.mul_apply]`.

Use function extensionality and compare the values at `c`. Use `hval c.out 1 0 Γ.one_mem (by rw [Quotient.out_eq]; simp)` as an intermediate fact. Express the relevant statement in the definitionally equal form `(A ^ κ c.out) (φ (Quotient.mk s c.out)) = φ c`. Rewrite using `[this, Quotient.out_eq]`. Simplify using the standard rewrite rules.

Set `e` to `LinearEquiv.ofBijective ev hev`. Use `⟨LinearEquiv.finiteDimensional e.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[e.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, ← hcard]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finrank_twInv_mul_of_free {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]
    (Γ : Subgroup G) (g : G) (A : E →ₗ[ℂ] E) (m : ℕ) (hΓ : Γ.FiniteIndex)
    (hE : FiniteDimensional ℂ E) (hm : 0 < m) (hg : g ^ m = 1) (hA : A ^ m = 1)
    (hfree : ∀ (x : G) (k : ℕ), 0 < k → k < m → x * g ^ k * x⁻¹ ∉ Γ) :
    FiniteDimensional ℂ (twInv Γ g A) ∧
      Module.finrank ℂ (twInv Γ g A) * m = Γ.index * Module.finrank ℂ E := by
  classical
  let s := freeSetoid Γ g m hm hg
  have hs : ∀ x y : G, s.r x y ↔ ∃ γ ∈ Γ, ∃ k : ℕ, y = γ * x * g ^ k := fun _ _ => Iff.rfl
  let R := Quotient s
  have hmk : ∀ γ ∈ Γ, ∀ (x : G) (k : ℕ), Quotient.mk s (γ * x * g ^ k) = Quotient.mk s x :=
    fun γ hγ x k => (Quotient.sound (s := s) ((hs _ _).2 ⟨γ, hγ, k, rfl⟩)).symm
  have hout : ∀ x : G, ∃ γ ∈ Γ, ∃ k : ℕ, x = γ * (Quotient.mk s x).out * g ^ k :=
    fun x => (hs _ _).1 (Quotient.mk_out (s := s) x)

  let F : R × Fin m → Quotient (QuotientGroup.rightRel Γ) :=
    fun p => Quotient.mk _ (p.1.out * g ^ (p.2 : ℕ))
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨c, i⟩ ⟨d, j⟩ h
      have h1 := QuotientGroup.rightRel_apply.1 (Quotient.exact h)
      dsimp only at h1
      set γ := d.out * g ^ (j : ℕ) * (c.out * g ^ (i : ℕ))⁻¹ with hγ
      have h2 : 1 * d.out * g ^ (j : ℕ) = γ * c.out * g ^ (i : ℕ) := by
        rw [hγ, mul_assoc _ c.out, inv_mul_cancel_right, one_mul]
      have h3 : d = c := by
        have := congrArg (Quotient.mk s) h2
        rw [hmk 1 Γ.one_mem, hmk γ h1, Quotient.out_eq, Quotient.out_eq] at this
        exact this
      subst h3
      have h4 := free_mod_eq Γ g m hm hg hfree _ _ _ Γ.one_mem h1 _ _ h2
      rw [Nat.mod_eq_of_lt j.2, Nat.mod_eq_of_lt i.2] at h4
      rw [Fin.ext h4]
    · intro q
      induction q using Quotient.inductionOn with
      | h x =>
        obtain ⟨γ, hγ, k, hx⟩ := hout x
        refine ⟨(Quotient.mk s x, ⟨k % m, Nat.mod_lt _ hm⟩), ?_⟩
        apply Quotient.sound
        apply QuotientGroup.rightRel_apply.2
        dsimp only
        rw [← pow_eq_pow_mod k hg]
        have : x * ((Quotient.mk s x).out * g ^ k)⁻¹ = γ := by
          rw [mul_inv_eq_iff_eq_mul, ← mul_assoc]
          exact hx
        rw [this]
        exact hγ
  have hcard : Nat.card R * m = Γ.index := by
    have h1 := Nat.card_congr (Equiv.ofBijective F hF)
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin,
      Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ)] at h1
    exact h1
  have hR : Finite R := by
    apply Nat.finite_of_card_ne_zero
    intro h0
    rw [h0, zero_mul] at hcard
    exact hΓ.index_ne_zero hcard.symm
  letI : Fintype R := Fintype.ofFinite R

  let ev : twInv Γ g A →ₗ[ℂ] (R → E) :=
    { toFun := fun f c => (f : G → E) c.out
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : Function.Bijective ev := by
    constructor
    · intro f f' h
      apply Subtype.ext
      funext x
      obtain ⟨γ, hγ, k, hx⟩ := hout x
      have h1 : (f : G → E) (Quotient.mk s x).out = (f' : G → E) (Quotient.mk s x).out :=
        congrFun h (Quotient.mk s x)
      rw [hx, twInv_apply_pow f.2, twInv_apply_pow f'.2, f.2.1 γ hγ, f'.2.1 γ hγ, h1]
    · intro φ
      choose γ hγ κ hκ using hout
      have hval : ∀ (x δ : G) (k : ℕ), δ ∈ Γ → x = δ * (Quotient.mk s x).out * g ^ k →
          A ^ κ x = A ^ k := by
        intro x δ k hδ hx
        have := free_mod_eq Γ g m hm hg hfree _ _ _ (hγ x) hδ _ _ ((hκ x).symm.trans hx)
        rw [pow_eq_pow_mod _ hA, this, ← pow_eq_pow_mod _ hA]
      refine ⟨⟨fun x => (A ^ κ x) (φ (Quotient.mk s x)), ?_, ?_⟩, ?_⟩
      · intro δ hδ x
        have e : Quotient.mk s (δ * x) = Quotient.mk s x := by
          simpa using hmk δ hδ x 0
        have := hval (δ * x) (δ * γ x) (κ x) (Γ.mul_mem hδ (hγ x)) (by
          rw [e, mul_assoc, mul_assoc δ, ← mul_assoc (γ x), ← hκ x])
        dsimp only
        rw [this, e]
      · intro x
        have e : Quotient.mk s (x * g) = Quotient.mk s x := by
          simpa using hmk 1 Γ.one_mem x 1
        have := hval (x * g) (γ x) (κ x + 1) (hγ x) (by
          rw [e, pow_succ, ← mul_assoc, ← hκ x])
        dsimp only
        rw [this, e, pow_succ', Module.End.mul_apply]
      · funext c
        have := hval c.out 1 0 Γ.one_mem (by rw [Quotient.out_eq]; simp)
        change (A ^ κ c.out) (φ (Quotient.mk s c.out)) = φ c
        rw [this, Quotient.out_eq]
        simp
  let e := LinearEquiv.ofBijective ev hev
  refine ⟨LinearEquiv.finiteDimensional e.symm, ?_⟩
  rw [e.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, ← hcard]
  ring

end GlobalTheory.HeckeFamilyMatrices.CocBound
