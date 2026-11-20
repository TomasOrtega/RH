import Mathlib

namespace GlobalTheory.ClassPart

/- English proof (translation)
Rewrite using `[hF]`. Use `congr 3`. Use `symm`. Apply `Nat.card_congr` to reduce the goal to its premises. Use `Equiv.subtypeEquiv (MulAut.conj η).toEquiv ?_` and prove the remaining obligations.

Introduce `s`. Simplify using `only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff, mul_smul, inv_smul_smul, smul_left_cancel_iff]`. Use `and_congr_right (fun _ => ?_)` and prove the remaining obligations. Rewrite using `[show η * s * η⁻¹ * (η * γ * η⁻¹) = η * (s * γ) * η⁻¹ by group, show η * γ * η⁻¹ * (η * s * η⁻¹) = η * (γ * s) * η⁻¹ by group, mul_left_inj, mul_right_inj]`.
-/
private lemma summand_conj {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ)
    (hF : ∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) (η : Γ) (y : Y) (γ : Γ) :
    ((Nat.card (MulAction.stabilizer Γ (η • y) ⊓ Subgroup.centralizer {η * γ * η⁻¹} : Subgroup Γ) : ℕ) : ℂ)⁻¹ *
        F (η • y) (η * γ * η⁻¹) =
      ((Nat.card (MulAction.stabilizer Γ y ⊓ Subgroup.centralizer {γ} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F y γ := by
  rw [hF]
  congr 3
  symm
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (MulAut.conj η).toEquiv ?_
  intro s
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv,
    MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff, mul_smul, inv_smul_smul, smul_left_cancel_iff]
  refine and_congr_right (fun _ => ?_)
  rw [show η * s * η⁻¹ * (η * γ * η⁻¹) = η * (s * γ) * η⁻¹ by group,
    show η * γ * η⁻¹ * (η * s * η⁻¹) = η * (γ * s) * η⁻¹ by group, mul_left_inj, mul_right_inj]

/- English proof (translation)
Introduce `Γ Y _ _ F hF γ g`. Use `set S : Γ → Y → ℂ := fun c y => ((Nat.card (MulAction.stabilizer Γ y ⊓ Subgroup.centralizer {c} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F y c with hSdef`. Establish `hS : ∀ (η : Γ) (y : Y) (c : Γ), S (η * c * η⁻¹) (η • y) = S c y` using `fun η y c => summand_conj F hF η y c`. Establish `hZ : ∀ (c : Γ) (ζ : Γ), ζ ∈ Subgroup.centralizer {c} → ∀ y, S c (ζ • y) = S c y`. Introduce `c ζ hζ y`.

Establish `hcj : ζ * c * ζ⁻¹ = c`. Rewrite `hζ` using `[Subgroup.mem_centralizer_singleton_iff]`. Rewrite using `[hζ]`. Use `group`. Use `hS ζ y c` as an intermediate fact.

Rewrite `this` using `[hcj]`. Then use the resulting hypothesis. Use `set γ' := g * γ * g⁻¹ with hγ'`. Establish `hrel : ∀ a b : Y, (MulAction.orbitRel (Subgroup.centralizer {γ}) Y) a b ↔ (MulAction.orbitRel (Subgroup.centralizer {γ'}) Y) (g • a) (g • b)`. Introduce `a b`. Simplify using `only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, Subtype.exists, Subgroup.mk_smul]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨ζ, hζ, h⟩`. Use `⟨g * ζ * g⁻¹, ?_, ?_⟩` and prove the remaining obligations. Rewrite `hζ`, the goal using `[Subgroup.mem_centralizer_singleton_iff]`. Rewrite using `[hγ']`.

Rewrite using `[show g * ζ * g⁻¹ * (g * γ * g⁻¹) = g * (ζ * γ) * g⁻¹ by group, show g * γ * g⁻¹ * (g * ζ * g⁻¹) = g * (γ * ζ) * g⁻¹ by group, hζ]`. Rewrite using `[← h]`. Simplify using `[mul_smul]`. Introduce and unpack `⟨ζ, hζ, h⟩`. Use `⟨g⁻¹ * ζ * g, ?_, ?_⟩` and prove the remaining obligations.

Rewrite `hζ`, the goal using `[Subgroup.mem_centralizer_singleton_iff]`. Rewrite `hζ` using `[hγ']`. Establish `h2 : g⁻¹ * (g * γ * g⁻¹ * ζ) * g = g⁻¹ * (ζ * (g * γ * g⁻¹)) * g` using `by rw [hζ]`. Rewrite `h2` using `[show g⁻¹ * (g * γ * g⁻¹ * ζ) * g = γ * (g⁻¹ * ζ * g) by group, show g⁻¹ * (ζ * (g * γ * g⁻¹)) * g = g⁻¹ * ζ * g * γ by group]`. Conclude with `h2.symm`.

Use `congrArg (g⁻¹ • ·) h` as an intermediate fact. Simplify `this` using `[mul_smul]`. Set `e : MulAction.orbitRel.Quotient (Subgroup.centralizer {γ}) Y ≃ MulAction.orbitRel.Quotient (Subgroup.centralizer {γ'}) Y` to `Quotient.congr (MulAction.toPerm g) hrel`. Express the relevant statement in the definitionally equal form `∑ᶠ o, S γ (Quotient.out o) = ∑ᶠ o, S γ' (Quotient.out o)`. Rewrite using `[← finsum_comp_equiv e]`.

Apply `finsum_congr` to reduce the goal to its premises. Introduce `o`. Establish `hmk : (Quotient.mk _ (Quotient.out (e o)) : MulAction.orbitRel.Quotient (Subgroup.centralizer {γ'}) Y) = Quotient.mk _ (g • Quotient.out o)`. Rewrite using `[Quotient.out_eq]`. Use `conv_lhs => rw [← Quotient.out_eq o]`.

Both sides reduce to the same expression. Establish `hr` using `Quotient.exact hmk`. Establish `hr' : Quotient.out (e o) ∈ MulAction.orbit (Subgroup.centralizer {γ'}) (g • Quotient.out o)` using `hr`. Rewrite `hr'` using `[MulAction.mem_orbit_iff]`. Take `⟨ζ, hζ⟩` from `hr'`.

Rewrite using `[← hζ, Subgroup.smul_def, hZ γ' ζ ζ.2, hγ', hS]`.
-/
theorem orbitSum_conj : ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ), (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) → ∀ (γ g : Γ), ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {γ}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {γ} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) γ = ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {g * γ * g⁻¹}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {g * γ * g⁻¹} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) (g * γ * g⁻¹) := by
  intro Γ Y _ _ F hF γ g
  set S : Γ → Y → ℂ := fun c y =>
    ((Nat.card (MulAction.stabilizer Γ y ⊓ Subgroup.centralizer {c} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F y c with hSdef
  have hS : ∀ (η : Γ) (y : Y) (c : Γ), S (η * c * η⁻¹) (η • y) = S c y := fun η y c => summand_conj F hF η y c
  have hZ : ∀ (c : Γ) (ζ : Γ), ζ ∈ Subgroup.centralizer {c} → ∀ y, S c (ζ • y) = S c y := by
    intro c ζ hζ y
    have hcj : ζ * c * ζ⁻¹ = c := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hζ
      rw [hζ]; group
    have := hS ζ y c
    rwa [hcj] at this
  set γ' := g * γ * g⁻¹ with hγ'
  have hrel : ∀ a b : Y, (MulAction.orbitRel (Subgroup.centralizer {γ}) Y) a b ↔
      (MulAction.orbitRel (Subgroup.centralizer {γ'}) Y) (g • a) (g • b) := by
    intro a b
    simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, Subtype.exists, Subgroup.mk_smul]
    constructor
    · rintro ⟨ζ, hζ, h⟩
      refine ⟨g * ζ * g⁻¹, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff] at hζ ⊢
        rw [hγ']
        rw [show g * ζ * g⁻¹ * (g * γ * g⁻¹) = g * (ζ * γ) * g⁻¹ by group,
          show g * γ * g⁻¹ * (g * ζ * g⁻¹) = g * (γ * ζ) * g⁻¹ by group, hζ]
      · rw [← h]; simp [mul_smul]
    · rintro ⟨ζ, hζ, h⟩
      refine ⟨g⁻¹ * ζ * g, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff] at hζ ⊢
        rw [hγ'] at hζ
        have h2 : g⁻¹ * (g * γ * g⁻¹ * ζ) * g = g⁻¹ * (ζ * (g * γ * g⁻¹)) * g := by rw [hζ]
        rw [show g⁻¹ * (g * γ * g⁻¹ * ζ) * g = γ * (g⁻¹ * ζ * g) by group,
          show g⁻¹ * (ζ * (g * γ * g⁻¹)) * g = g⁻¹ * ζ * g * γ by group] at h2
        exact h2.symm
      · have := congrArg (g⁻¹ • ·) h
        simpa [mul_smul] using this
  let e : MulAction.orbitRel.Quotient (Subgroup.centralizer {γ}) Y ≃
      MulAction.orbitRel.Quotient (Subgroup.centralizer {γ'}) Y :=
    Quotient.congr (MulAction.toPerm g) hrel
  change ∑ᶠ o, S γ (Quotient.out o) = ∑ᶠ o, S γ' (Quotient.out o)
  rw [← finsum_comp_equiv e]
  apply finsum_congr
  intro o
  have hmk : (Quotient.mk _ (Quotient.out (e o)) : MulAction.orbitRel.Quotient (Subgroup.centralizer {γ'}) Y) =
      Quotient.mk _ (g • Quotient.out o) := by
    rw [Quotient.out_eq]
    conv_lhs => rw [← Quotient.out_eq o]
    rfl
  have hr := Quotient.exact hmk
  have hr' : Quotient.out (e o) ∈ MulAction.orbit (Subgroup.centralizer {γ'}) (g • Quotient.out o) := hr
  rw [MulAction.mem_orbit_iff] at hr'
  obtain ⟨ζ, hζ⟩ := hr'
  rw [← hζ, Subgroup.smul_def, hZ γ' ζ ζ.2, hγ', hS]

end GlobalTheory.ClassPart
