import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle

open UpperTheory.V.FW

/- English proof (translation)
Use `set g : H →+ V := f.comp H.subtype with hg`. Establish `h1` using `AddSubgroup.card_mul_index (AddMonoidHom.ker g)`. Rewrite `h1` using `[AddSubgroup.index_ker]`. Establish `h2 : AddMonoidHom.range g = H.map f`. Rewrite using `[hg, ← AddMonoidHom.map_range, AddSubgroup.range_subtype]`.

Establish `h3 : Nat.card (AddMonoidHom.ker g) ≤ Nat.card (AddMonoidHom.ker f)`. Use `Nat.card_le_card_of_injective (fun x => (⟨(x.1 : V), by` and prove the remaining obligations. Establish `hx` using `x.2`. Rewrite `hx`, the goal using `[AddMonoidHom.mem_ker]`. Conclude with `hx⟩ : AddMonoidHom.ker f)) ?_`.

Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using congrArg Subtype.val hab`. Rewrite using `[← h1, h2]`.

Conclude with `Nat.mul_le_mul_right _ h3`.
-/
private theorem card_le_card_ker_mul_card_map {V : Type} [AddCommGroup V] [Finite V] (f : V →+ V)
    (H : AddSubgroup V) :
    Nat.card H ≤ Nat.card (AddMonoidHom.ker f) * Nat.card (H.map f) := by
  set g : H →+ V := f.comp H.subtype with hg
  have h1 := AddSubgroup.card_mul_index (AddMonoidHom.ker g)
  rw [AddSubgroup.index_ker] at h1
  have h2 : AddMonoidHom.range g = H.map f := by
    rw [hg, ← AddMonoidHom.map_range, AddSubgroup.range_subtype]
  have h3 : Nat.card (AddMonoidHom.ker g) ≤ Nat.card (AddMonoidHom.ker f) := by
    refine Nat.card_le_card_of_injective
      (fun x => (⟨(x.1 : V), by
        have hx := x.2
        rw [AddMonoidHom.mem_ker] at hx ⊢
        exact hx⟩ : AddMonoidHom.ker f)) ?_
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val hab
  rw [← h1, h2]
  exact Nat.mul_le_mul_right _ h3

/- English proof (translation)
Introduce `V _ _ T N hN`. Use `set K := Nat.card (AddMonoidHom.ker (T : V →+ V)) with hK`. Establish `hidx : (AddMonoidHom.range (T : V →+ V)).index = K`. Establish `a` using `AddSubgroup.card_mul_index (AddMonoidHom.ker (T : V →+ V))`. Establish `c` using `AddSubgroup.index_ker (T : V →+ V)`.

Rewrite `a` using `[c]`. Establish `b` using `AddSubgroup.card_mul_index (AddMonoidHom.range (T : V →+ V))`. Establish `hpos : 0 < Nat.card (AddMonoidHom.range (T : V →+ V))` using `Nat.card_pos`. Establish `: Nat.card (AddMonoidHom.range (T : V →+ V)) * (AddMonoidHom.range (T : V →+ V)).index = Nat.card (AddMonoidHom.range (T : V →+ V)) * K`. Rewrite using `[b, ← a, Nat.mul_comm]`.

Conclude with `Nat.eq_of_mul_eq_mul_left hpos this`. Establish `step : ∀ k : ℕ, Nat.card (AddMonoidHom.range ((T ^ k : AddMonoid.End V) : V →+ V)) ≤ K * Nat.card (AddMonoidHom.range ((T ^ (k + 1) : AddMonoid.End V) : V →+ V))`. Introduce `k`. Establish `h` using `card_le_card_ker_mul_card_map (T : V →+ V) (AddMonoidHom.range ((T ^ k : AddMonoid.End V) : V →+ V))`. Establish `e : (AddMonoidHom.range ((T ^ k : AddMonoid.End V) : V →+ V)).map (T : V →+ V) = AddMonoidHom.range ((T ^ (k + 1) : AddMonoid.End V) : V →+ V)`.

Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨x, rfl⟩, rfl⟩`. Use `⟨x, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ']`.

Both sides reduce to the same expression. Introduce and unpack `⟨x, rfl⟩`. Use `⟨(T ^ k) x, ⟨x, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ']`. Both sides reduce to the same expression.

Rewrite `h` using `[e]`. Conclude with `h`. Establish `main : ∀ k : ℕ, Nat.card V ≤ K ^ k * Nat.card (AddMonoidHom.range ((T ^ k : AddMonoid.End V) : V →+ V))`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero`. Rewrite using `[pow_zero, Nat.one_mul]`. Use `Nat.card_le_card_of_injective (fun x => (⟨x, x, by rw [pow_zero]; rfl⟩ : AddMonoidHom.range ((T ^ 0 : AddMonoid.End V) : V →+ V))) ?_` and prove the remaining obligations. Introduce `a b hab`. Simplify using `using congrArg Subtype.val hab`.

Consider the case `succ k ih`. Combine the equalities or inequalities in the displayed calculation. Establish `hN1 : Nat.card (AddMonoidHom.range ((T ^ N : AddMonoid.End V) : V →+ V)) ≤ 1`. Establish `hinj : Function.Injective (fun _ : AddMonoidHom.range ((T ^ N : AddMonoid.End V) : V →+ V) => ())`. Introduce and unpack `⟨a, x, rfl⟩ ⟨b, y, rfl⟩ _`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show (T ^ N) x = (T ^ N) y`. Rewrite using `[hN]`. Both sides reduce to the same expression. Use `Nat.card_le_card_of_injective _ hinj` as an intermediate fact.

Simplify using `using this`. Rewrite using `[hidx]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.V.FW.nilCard :
    ∀ (V : Type) [AddCommGroup V] [Finite V] (T : AddMonoid.End V) (N : ℕ), T ^ N = 0 → Nat.card V ≤ (AddMonoidHom.range T).index ^ N := by
  intro V _ _ T N hN
  set K := Nat.card (AddMonoidHom.ker (T : V →+ V)) with hK
  have hidx : (AddMonoidHom.range (T : V →+ V)).index = K := by
    have a := AddSubgroup.card_mul_index (AddMonoidHom.ker (T : V →+ V))
    have c := AddSubgroup.index_ker (T : V →+ V)
    rw [c] at a
    have b := AddSubgroup.card_mul_index (AddMonoidHom.range (T : V →+ V))
    have hpos : 0 < Nat.card (AddMonoidHom.range (T : V →+ V)) := Nat.card_pos
    have : Nat.card (AddMonoidHom.range (T : V →+ V)) * (AddMonoidHom.range (T : V →+ V)).index
        = Nat.card (AddMonoidHom.range (T : V →+ V)) * K := by
      rw [b, ← a, Nat.mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have step : ∀ k : ℕ, Nat.card (AddMonoidHom.range ((T ^ k : AddMonoid.End V) : V →+ V))
      ≤ K * Nat.card (AddMonoidHom.range ((T ^ (k + 1) : AddMonoid.End V) : V →+ V)) := by
    intro k
    have h := card_le_card_ker_mul_card_map (T : V →+ V) (AddMonoidHom.range ((T ^ k : AddMonoid.End V) : V →+ V))
    have e : (AddMonoidHom.range ((T ^ k : AddMonoid.End V) : V →+ V)).map (T : V →+ V)
        = AddMonoidHom.range ((T ^ (k + 1) : AddMonoid.End V) : V →+ V) := by
      ext y
      constructor
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        refine ⟨x, ?_⟩
        rw [pow_succ']
        rfl
      · rintro ⟨x, rfl⟩
        refine ⟨(T ^ k) x, ⟨x, rfl⟩, ?_⟩
        rw [pow_succ']
        rfl
    rw [e] at h
    exact h
  have main : ∀ k : ℕ, Nat.card V
      ≤ K ^ k * Nat.card (AddMonoidHom.range ((T ^ k : AddMonoid.End V) : V →+ V)) := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, Nat.one_mul]
      refine Nat.card_le_card_of_injective
        (fun x => (⟨x, x, by rw [pow_zero]; rfl⟩ :
          AddMonoidHom.range ((T ^ 0 : AddMonoid.End V) : V →+ V))) ?_
      intro a b hab
      simpa using congrArg Subtype.val hab
    | succ k ih =>
      calc Nat.card V
          ≤ K ^ k * Nat.card (AddMonoidHom.range ((T ^ k : AddMonoid.End V) : V →+ V)) := ih
        _ ≤ K ^ k * (K * Nat.card
            (AddMonoidHom.range ((T ^ (k + 1) : AddMonoid.End V) : V →+ V))) :=
          Nat.mul_le_mul_left _ (step k)
        _ = K ^ (k + 1) * Nat.card
            (AddMonoidHom.range ((T ^ (k + 1) : AddMonoid.End V) : V →+ V)) := by ring
  have hN1 : Nat.card (AddMonoidHom.range ((T ^ N : AddMonoid.End V) : V →+ V)) ≤ 1 := by
    have hinj : Function.Injective
        (fun _ : AddMonoidHom.range ((T ^ N : AddMonoid.End V) : V →+ V) => ()) := by
      rintro ⟨a, x, rfl⟩ ⟨b, y, rfl⟩ _
      apply Subtype.ext
      show (T ^ N) x = (T ^ N) y
      rw [hN]
      rfl
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  rw [hidx]
  calc Nat.card V
      ≤ K ^ N * Nat.card (AddMonoidHom.range ((T ^ N : AddMonoid.End V) : V →+ V)) := main N
    _ ≤ K ^ N * 1 := Nat.mul_le_mul_left _ hN1
    _ = K ^ N := Nat.mul_one _
