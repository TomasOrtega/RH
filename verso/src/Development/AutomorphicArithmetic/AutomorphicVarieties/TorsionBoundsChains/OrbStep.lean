import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle

open CategoryTheory UpperTheory.V.KH

/- English proof (translation)
Introduce `u`. Rewrite using `[SubMulAction.stabilizer_of_subMul]`. Conclude with `h u`.
-/
private theorem UpperTheory.V.KH.stabLe_sub {G X : Type} [Group G] [MulAction G X] {s : ℕ}
    (h : StabLe G X s) (U : SubMulAction G X) : StabLe G U s := by
  intro u
  rw [SubMulAction.stabilizer_of_subMul]
  exact h u

/- English proof (translation)
Introduce `G X _ _ A s x hO hS`. Set `U : SubMulAction G X` to `{ carrier := MulAction.orbit G x smul_mem' := by`. Introduce and unpack `g y ⟨h, rfl⟩`. Conclude with `⟨g * h, mul_smul _ _ _⟩ }`. Establish `hxU : x ∈ U` using `MulAction.mem_orbit_self x`.

Use `⟨U, Uᶜ, fun y => Iff.rfl, ⟨⟨x, hxU⟩⟩, ?_, stabLe_sub hS U, stabLe_sub hS Uᶜ, ?_⟩` and prove the remaining obligations. Use `⟨fun a b => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `a`. Take `⟨b, hb⟩` from `b`. Take `⟨g, rfl⟩` from `ha`.

Take `⟨h, rfl⟩` from `hb`. Use `⟨h * g⁻¹, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(h * g⁻¹) • g • x = h • x`. Rewrite using `[smul_smul, inv_mul_cancel_right]`. Establish `hrel : ∀ a b : (Uᶜ : SubMulAction G X), (MulAction.orbitRel G (Uᶜ : SubMulAction G X)) a b ↔ (MulAction.orbitRel G X) a b`.

Introduce `a b`. Rewrite using `[SubMulAction.orbitRel_of_subMul]`. Both sides reduce to the same expression. Set `f : MulAction.orbitRel.Quotient G (Uᶜ : SubMulAction G X) → MulAction.orbitRel.Quotient G X` to `Quotient.map (fun a => (a : X)) (fun a b hab => (hrel a b).1 hab)`. Set `F : Option (MulAction.orbitRel.Quotient G (Uᶜ : SubMulAction G X)) → MulAction.orbitRel.Quotient G X` to `fun o => o.elim (Quotient.mk _ x) f`.

Establish `hF : Function.Injective F`. Establish `hne : ∀ a : (Uᶜ : SubMulAction G X), (Quotient.mk _ (a : X) : MulAction.orbitRel.Quotient G X) ≠ Quotient.mk _ x`. Introduce `a hax`. Establish `h1 : (MulAction.orbitRel G X) (a : X) x` using `Quotient.exact hax`. Conclude with `a.2 h1`.

Introduce and unpack `(_ | p) (_ | q) hpq`. Both sides reduce to the same expression. Proceed by induction on `q using Quotient.inductionOn with`. Consider the case `h b => exact absurd hpq.symm (hne b)`. Proceed by induction on `p using Quotient.inductionOn with`.

Consider the case `h a => exact absurd hpq (hne a)`. Proceed by induction on `p using Quotient.inductionOn with`. Consider the case `h a`. Proceed by induction on `q using Quotient.inductionOn with`. Consider the case `h b`.

Use `congr 1`. Conclude with `Quotient.sound ((hrel a b).2 (Quotient.exact hpq))`. Use `haveI : Finite (MulAction.orbitRel.Quotient G X) := hO.1`. Use `haveI : Finite (Option (MulAction.orbitRel.Quotient G (Uᶜ : SubMulAction G X))) := Finite.of_injective F hF`. Use `haveI : Finite (MulAction.orbitRel.Quotient G (Uᶜ : SubMulAction G X)) := Finite.of_injective some (Option.some_injective _)`.

Use `⟨inferInstance, ?_⟩` and prove the remaining obligations. Establish `h2` using `Nat.card_le_card_of_injective F hF`. Rewrite `h2` using `[Finite.card_option]`. Establish `h3` using `hO.2`. Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.V.KH.orbStep :
    ∀ (G X : Type) [Group G] [MulAction G X] (A s : ℕ) (x : X), OrbLe G X (A + 1) → StabLe G X s →
      ∃ U V : SubMulAction G X, (∀ y, y ∈ V ↔ y ∉ U) ∧ Nonempty U ∧ MulAction.IsPretransitive G U ∧
        StabLe G U s ∧ StabLe G V s ∧ OrbLe G V A := by
  intro G X _ _ A s x hO hS
  let U : SubMulAction G X :=
    { carrier := MulAction.orbit G x
      smul_mem' := by
        rintro g y ⟨h, rfl⟩
        exact ⟨g * h, mul_smul _ _ _⟩ }
  have hxU : x ∈ U := MulAction.mem_orbit_self x
  refine ⟨U, Uᶜ, fun y => Iff.rfl, ⟨⟨x, hxU⟩⟩, ?_, stabLe_sub hS U, stabLe_sub hS Uᶜ, ?_⟩
  · refine ⟨fun a b => ?_⟩
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    obtain ⟨g, rfl⟩ := ha
    obtain ⟨h, rfl⟩ := hb
    refine ⟨h * g⁻¹, Subtype.ext ?_⟩
    change (h * g⁻¹) • g • x = h • x
    rw [smul_smul, inv_mul_cancel_right]
  · have hrel : ∀ a b : (Uᶜ : SubMulAction G X),
        (MulAction.orbitRel G (Uᶜ : SubMulAction G X)) a b ↔ (MulAction.orbitRel G X) a b := by
      intro a b
      rw [SubMulAction.orbitRel_of_subMul]
      rfl
    let f : MulAction.orbitRel.Quotient G (Uᶜ : SubMulAction G X) → MulAction.orbitRel.Quotient G X :=
      Quotient.map (fun a => (a : X)) (fun a b hab => (hrel a b).1 hab)
    let F : Option (MulAction.orbitRel.Quotient G (Uᶜ : SubMulAction G X)) →
        MulAction.orbitRel.Quotient G X := fun o => o.elim (Quotient.mk _ x) f
    have hF : Function.Injective F := by
      have hne : ∀ a : (Uᶜ : SubMulAction G X),
          (Quotient.mk _ (a : X) : MulAction.orbitRel.Quotient G X) ≠ Quotient.mk _ x := by
        intro a hax
        have h1 : (MulAction.orbitRel G X) (a : X) x := Quotient.exact hax
        exact a.2 h1
      rintro (_ | p) (_ | q) hpq
      · rfl
      · induction q using Quotient.inductionOn with
        | h b => exact absurd hpq.symm (hne b)
      · induction p using Quotient.inductionOn with
        | h a => exact absurd hpq (hne a)
      · induction p using Quotient.inductionOn with
        | h a =>
          induction q using Quotient.inductionOn with
          | h b =>
            congr 1
            exact Quotient.sound ((hrel a b).2 (Quotient.exact hpq))
    haveI : Finite (MulAction.orbitRel.Quotient G X) := hO.1
    haveI : Finite (Option (MulAction.orbitRel.Quotient G (Uᶜ : SubMulAction G X))) :=
      Finite.of_injective F hF
    haveI : Finite (MulAction.orbitRel.Quotient G (Uᶜ : SubMulAction G X)) :=
      Finite.of_injective some (Option.some_injective _)
    refine ⟨inferInstance, ?_⟩
    have h2 := Nat.card_le_card_of_injective F hF
    rw [Finite.card_option] at h2
    have h3 := hO.2
    omega
