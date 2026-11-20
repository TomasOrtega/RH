import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs

/- English proof (translation)
Establish `hσ : ∀ q : Quotient r, ∃ y ∈ Y, Quotient.mk r y = q`. Introduce `q`. Proceed by induction on `q using Quotient.inductionOn with`. Consider the case `h g`. Take `⟨y, hy, h⟩` from `hY g`.

Conclude with `⟨y, hy, Quotient.sound h⟩`. Use `choose σ hσY hσ using hσ`. Use `haveI : Finite (Quotient r) := by`. Use `Finite.of_injective (fun q => (⟨σ q, hσY q⟩ : Y)) ?_` and prove the remaining obligations. Introduce `a b h`.

Establish `h' : σ a = σ b` using `congrArg Subtype.val h`. Rewrite using `[← hσ a, ← hσ b, h']`. Use `haveI : Nonempty (Quotient r) := ⟨Quotient.mk r x₀⟩`. Take `⟨n, hn⟩ : ∃ n, Nat.card (Quotient r) = n + 1` from `Nat.exists_eq_succ_of_ne_zero (Nat.card_pos (α := Quotient r)).ne'`. Set `e₀ : Fin (n + 1) ≃ Quotient r` to `(Finite.equivFinOfCardEq hn).symm`.

Set `e : Fin (n + 1) ≃ Quotient r` to `e₀.trans (Equiv.swap (e₀ 0) (Quotient.mk r x₀))`. Establish `he : e 0 = Quotient.mk r x₀` using `by simp [e]`. Set `x : Fin (n + 1) → G` to `fun i => if i = 0 then x₀ else σ (e i)`. Establish `hx : ∀ i, Quotient.mk r (x i) = e i`. Introduce `i`.

Distinguish the cases in `h : i = 0`. Substitute `h` using the available equality. Simplify using `[x, he]`. Simplify using `[x, h, hσ]`. Use `⟨n, x, by simp [x], ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `i`. Distinguish the cases in `h : i = 0`. Use `left`. Simplify using `[x, h]`. Use `right`.

Simplify using `[x, h, hσY]`. Introduce `i j h`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[← hx, ← hx]`. Conclude with `Quotient.sound h`.

Introduce `g`. Use `⟨e.symm (Quotient.mk r g), Quotient.exact ?_⟩` and prove the remaining obligations. Rewrite using `[hx]`. Simplify using the standard rewrite rules.
-/
private theorem reps_setoid {G : Type} (r : Setoid G) (Y : Finset G) (x₀ : G)
    (hY : ∀ g, ∃ y ∈ Y, r y g) :
    ∃ (n : ℕ) (x : Fin (n + 1) → G), x 0 = x₀ ∧ (∀ i, x i = x₀ ∨ x i ∈ Y) ∧
      (∀ i j, r (x i) (x j) → i = j) ∧ ∀ g, ∃ i, r (x i) g := by
  classical
  have hσ : ∀ q : Quotient r, ∃ y ∈ Y, Quotient.mk r y = q := by
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      obtain ⟨y, hy, h⟩ := hY g
      exact ⟨y, hy, Quotient.sound h⟩
  choose σ hσY hσ using hσ
  haveI : Finite (Quotient r) := by
    refine Finite.of_injective (fun q => (⟨σ q, hσY q⟩ : Y)) ?_
    intro a b h
    have h' : σ a = σ b := congrArg Subtype.val h
    rw [← hσ a, ← hσ b, h']
  haveI : Nonempty (Quotient r) := ⟨Quotient.mk r x₀⟩
  obtain ⟨n, hn⟩ : ∃ n, Nat.card (Quotient r) = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Nat.card_pos (α := Quotient r)).ne'
  let e₀ : Fin (n + 1) ≃ Quotient r := (Finite.equivFinOfCardEq hn).symm
  let e : Fin (n + 1) ≃ Quotient r := e₀.trans (Equiv.swap (e₀ 0) (Quotient.mk r x₀))
  have he : e 0 = Quotient.mk r x₀ := by simp [e]
  let x : Fin (n + 1) → G := fun i => if i = 0 then x₀ else σ (e i)
  have hx : ∀ i, Quotient.mk r (x i) = e i := by
    intro i
    by_cases h : i = 0
    · subst h; simp [x, he]
    · simp [x, h, hσ]
  refine ⟨n, x, by simp [x], ?_, ?_, ?_⟩
  · intro i
    by_cases h : i = 0
    · left; simp [x, h]
    · right; simp [x, h, hσY]
  · intro i j h
    apply e.injective
    rw [← hx, ← hx]
    exact Quotient.sound h
  · intro g
    refine ⟨e.symm (Quotient.mk r g), Quotient.exact ?_⟩
    rw [hx]; simp

/- English proof (translation)
Introduce `Γ G _ _ ι S U' Y x₀ hS hY`. Set `r : Setoid G` to `{ r := fun a b => ∃ γ, ∃ s ∈ S, ∃ u ∈ U', b = ι γ * s * a * u iseqv := { refl := fun a => ⟨1, 1, S.one_mem, 1, U'.one_mem, by simp⟩`. Use symmetry as in `:= by`. Introduce and unpack `a b ⟨γ, s, hs, u, hu, rfl⟩`. Use `⟨γ⁻¹, ι γ * s⁻¹ * (ι γ)⁻¹, hS.conj_mem _ (S.inv_mem hs) _, u⁻¹, U'.inv_mem hu, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_inv]`. Use `group`. Use `trans := by`. Introduce and unpack `a b c ⟨γ, s, hs, u, hu, rfl⟩ ⟨γ', s', hs', u', hu', rfl⟩`. Use `⟨γ' * γ, (ι γ)⁻¹ * s' * (ι γ)⁻¹⁻¹ * s, S.mul_mem (hS.conj_mem _ hs' _) hs, u * u', U'.mul_mem hu hu', ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul]`. Use `group } }`. Take `⟨n, x, h0, h1, h2, h3⟩` from `reps_setoid r Y x₀ (by`. Introduce `g`. Take `⟨γ, s, hs, y, hy, u, hu, h⟩` from `hY g`.

Conclude with `⟨y, hy, γ, s, hs, u, hu, h⟩)`. Use `⟨n, x, h0, h1, fun i j γ s hs u hu h => h2 i j ⟨γ, s, hs, u, hu, h⟩, fun g => ?_⟩` and prove the remaining obligations. Take `⟨i, γ, s, hs, u, hu, h⟩` from `h3 g`. Conclude with `⟨i, γ, s, hs, u, hu, h⟩`.
-/
theorem UpperTheory.orbitalFiber_representatives :
    UpperTheory.V.Z.Sym.Glob.Fib.Reps := by
  intro Γ G _ _ ι S U' Y x₀ hS hY
  let r : Setoid G :=
    { r := fun a b => ∃ γ, ∃ s ∈ S, ∃ u ∈ U', b = ι γ * s * a * u
      iseqv :=
        { refl := fun a => ⟨1, 1, S.one_mem, 1, U'.one_mem, by simp⟩
          symm := by
            rintro a b ⟨γ, s, hs, u, hu, rfl⟩
            refine ⟨γ⁻¹, ι γ * s⁻¹ * (ι γ)⁻¹, hS.conj_mem _ (S.inv_mem hs) _, u⁻¹, U'.inv_mem hu, ?_⟩
            rw [map_inv]; group
          trans := by
            rintro a b c ⟨γ, s, hs, u, hu, rfl⟩ ⟨γ', s', hs', u', hu', rfl⟩
            refine ⟨γ' * γ, (ι γ)⁻¹ * s' * (ι γ)⁻¹⁻¹ * s,
              S.mul_mem (hS.conj_mem _ hs' _) hs, u * u', U'.mul_mem hu hu', ?_⟩
            rw [map_mul]; group } }
  obtain ⟨n, x, h0, h1, h2, h3⟩ := reps_setoid r Y x₀ (by
    intro g
    obtain ⟨γ, s, hs, y, hy, u, hu, h⟩ := hY g
    exact ⟨y, hy, γ, s, hs, u, hu, h⟩)
  refine ⟨n, x, h0, h1, fun i j γ s hs u hu h => h2 i j ⟨γ, s, hs, u, hu, h⟩, fun g => ?_⟩
  obtain ⟨i, γ, s, hs, u, hu, h⟩ := h3 g
  exact ⟨i, γ, s, hs, u, hu, h⟩
