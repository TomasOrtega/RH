import Mathlib

noncomputable def UpperTheory.Reformulated.B.HeckeGelfandPair.IsHecke :
    {G : Type} → [inst : Group G] → [TopologicalSpace G] → Subgroup G → (G → ℂ) → Prop :=
    fun {G : Type} [Group G] [TopologicalSpace G] (K' : Subgroup G) (f : G → ℂ) ↦
      HasCompactSupport f ∧ ∀ k ∈ K', ∀ (x : G), f (k * x) = f x ∧ f (x * k) = f x

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
theorem UpperTheory.Reformulated.B.HeckeGelfandPair.aux2 :
    ∀ {H : Type} [inst : Group H] (u : H → ℂ) {a b : H},
      a ∈ {k : H | ∀ (x : H), u (x * k) = u x} → b ∈ {k : H | ∀ (x : H), u (x * k) = u x} → ∀ (x : H), u (x * (a * b)) = u x := by
  intro H _ u a b ha hb x
  rw [← mul_assoc, hb, ha]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
theorem UpperTheory.Reformulated.B.HeckeGelfandPair.aux3 :
    ∀ {H : Type} [inst : Group H] (u : H → ℂ) (a : H), u (a * (1 : H)) = u a := by
  intro H _ u a
  rw [mul_one]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Reformulated.B.HeckeGelfandPair.aux4 :
    ∀ {H : Type} [inst : Group H] (u : H → ℂ) {a : H},
      a ∈ {k : H | ∀ (x : H), u (x * k) = u x} → ∀ (x : H), u (x * a⁻¹) = u x := by
  intro H _ u a ha x
  have h := ha (x * a⁻¹)
  rw [inv_mul_cancel_right] at h
  exact h.symm

noncomputable def UpperTheory.Reformulated.B.HeckeGelfandPair.rStab :
    {H : Type} → [inst : Group H] → (H → ℂ) → Subgroup H :=
    fun {H : Type} [inst : Group H] (u : H → ℂ) ↦
      { carrier := {k : H | ∀ (x : H), u (x * k) = u x}, mul_mem' := @UpperTheory.Reformulated.B.HeckeGelfandPair.aux2 H inst u,
        one_mem' := UpperTheory.Reformulated.B.HeckeGelfandPair.aux3 u, inv_mem' := @UpperTheory.Reformulated.B.HeckeGelfandPair.aux4 H inst u : Subgroup H }

noncomputable def UpperTheory.Reformulated.B.HeckeGelfandPair.hint :
    {H : Type} → [inst : Group H] → Subgroup H → (H → ℂ) → ℂ :=
    fun {H : Type} [Group H] (K : Subgroup H) (u : H → ℂ) ↦
      (↑((UpperTheory.Reformulated.B.HeckeGelfandPair.rStab u ⊓ K).relIndex K) : ℂ)⁻¹ * ∑ᶠ (q : H ⧸ UpperTheory.Reformulated.B.HeckeGelfandPair.rStab u ⊓ K), u (Quotient.out q)

noncomputable def UpperTheory.Reformulated.B.HeckeGelfandPair.cv :
    {G : Type} → [inst : Group G] → Subgroup G → (G → ℂ) → (G → ℂ) → G → ℂ :=
    fun {G : Type} [Group G] (K : Subgroup G) (f g : G → ℂ) (y : G) ↦ UpperTheory.Reformulated.B.HeckeGelfandPair.hint K fun (z : G) ↦ f z * g (z⁻¹ * y)

noncomputable def UpperTheory.Reformulated.B.HeckeGelfandPair.CvGelfand :
    Prop :=
    ∀ (G : Type) [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G),
      IsOpen (↑K : Set G) →
        IsCompact (↑K : Set G) →
          ∀ (τ : G → G),
            (∀ (x y : G), τ (x * y) = τ y * τ x) →
              (∀ (x : G), τ (τ x) = x) →
                (∀ k ∈ K, τ k ∈ K) →
                  (∀ (x : G), ∃ k ∈ K, ∃ k' ∈ K, τ x = k * x * k') →
                    ∀ (f g : G → ℂ),
                      UpperTheory.Reformulated.B.HeckeGelfandPair.IsHecke K f →
                        UpperTheory.Reformulated.B.HeckeGelfandPair.IsHecke K g → UpperTheory.Reformulated.B.HeckeGelfandPair.cv K f g = UpperTheory.Reformulated.B.HeckeGelfandPair.cv K g f

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private theorem UpperTheory.Reformulated.B.HeckeGelfandPair.hint_eq {H : Type} [Group H] (K : Subgroup H) (u : H → ℂ)
    (hu : ∀ k ∈ K, ∀ x, u (x * k) = u x) :
    UpperTheory.Reformulated.B.HeckeGelfandPair.hint K u = ∑ᶠ q : H ⧸ K, u (Quotient.out q) := by
  have h : UpperTheory.Reformulated.B.HeckeGelfandPair.rStab u ⊓ K = K := inf_eq_right.mpr (fun k hk => hu k hk)
  unfold UpperTheory.Reformulated.B.HeckeGelfandPair.hint
  rw [h]
  simp

/- English proof (translation)
Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Both sides reduce to the same expression. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem UpperTheory.Reformulated.B.HeckeGelfandPair.sum_congr {H : Type} [Group H] (K : Subgroup H) (u v : H → ℂ)
    (hv : ∀ k ∈ K, ∀ x, v (x * k) = v x) (e : H ≃ H)
    (he : ∀ a b, a⁻¹ * b ∈ K ↔ (e a)⁻¹ * e b ∈ K) (huv : ∀ z, v (e z) = u z) :
    ∑ᶠ q : H ⧸ K, u (Quotient.out q) = ∑ᶠ q : H ⧸ K, v (Quotient.out q) := by
  let E : H ⧸ K ≃ H ⧸ K := Quotient.congr e (fun a b => by
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    exact he a b)
  rw [← finsum_comp_equiv E (f := fun q : H ⧸ K => v (Quotient.out q))]
  refine finsum_congr (fun q => ?_)
  have h1 : E q = (QuotientGroup.mk (e q.out) : H ⧸ K) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (e q.out)
  rw [h1, hk, hv _ k.2, huv]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument.

Extract witnesses or component facts from the available result. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Reformulated.B.HeckeGelfandPair.cvGelfand :
    UpperTheory.Reformulated.B.HeckeGelfandPair.CvGelfand := by
  intro G _ _ _ K _ _ τ hmul hinv hK hdc f g hf hg
  have h1 : τ 1 = 1 := by
    have h := hmul 1 1
    rw [mul_one] at h
    exact left_eq_mul.mp h
  have hi : ∀ x, τ x⁻¹ = (τ x)⁻¹ := fun x => by
    apply eq_inv_of_mul_eq_one_right
    rw [← hmul, inv_mul_cancel, h1]
  have hτ : ∀ φ : G → ℂ, UpperTheory.Reformulated.B.HeckeGelfandPair.IsHecke K φ → ∀ x, φ (τ x) = φ x := by
    intro φ hφ x
    obtain ⟨k, hk, k', hk', h⟩ := hdc x
    rw [h, (hφ.2 k' hk' _).2, (hφ.2 k hk _).1]
  have hr : ∀ φ ψ : G → ℂ, UpperTheory.Reformulated.B.HeckeGelfandPair.IsHecke K φ → UpperTheory.Reformulated.B.HeckeGelfandPair.IsHecke K ψ →
      ∀ y, ∀ k ∈ K, ∀ x, φ (x * k) * ψ ((x * k)⁻¹ * y) = φ x * ψ (x⁻¹ * y) := by
    intro φ ψ hφ hψ y k hk x
    rw [(hφ.2 k hk x).2, mul_inv_rev, mul_assoc, (hψ.2 k⁻¹ (K.inv_mem hk) _).1]
  funext y
  obtain ⟨k, hk, k', hk', hy⟩ := hdc y
  unfold UpperTheory.Reformulated.B.HeckeGelfandPair.cv
  rw [UpperTheory.Reformulated.B.HeckeGelfandPair.hint_eq K _ (hr f g hf hg y), UpperTheory.Reformulated.B.HeckeGelfandPair.hint_eq K _ (hr g f hg hf y)]
  let e : G ≃ G :=
    { toFun := fun z => y * k' * (τ z)⁻¹
      invFun := fun w => τ (w⁻¹ * (y * k'))
      left_inv := fun z => by
        have : (y * k' * (τ z)⁻¹)⁻¹ * (y * k') = τ z := by group
        simp only [this, hinv]
      right_inv := fun w => by
        simp only [hinv]
        group }
  refine UpperTheory.Reformulated.B.HeckeGelfandPair.sum_congr K (fun z => f z * g (z⁻¹ * y)) (fun z => g z * f (z⁻¹ * y))
    (hr g f hg hf y) e ?_ ?_
  · intro a b
    have h : (e a)⁻¹ * e b = τ (a⁻¹ * b)⁻¹ := by
      change (y * k' * (τ a)⁻¹)⁻¹ * (y * k' * (τ b)⁻¹) = _
      rw [hi, hmul, hi]
      group
    rw [h]
    constructor
    · exact fun hab => hK _ (K.inv_mem hab)
    · intro hab
      have h2 := hK _ hab
      rw [hinv] at h2
      exact K.inv_mem_iff.mp h2
  · intro z
    change g (y * k' * (τ z)⁻¹) * f ((y * k' * (τ z)⁻¹)⁻¹ * y) = f z * g (z⁻¹ * y)
    have h2 : (y * k' * (τ z)⁻¹)⁻¹ * y = τ z * k'⁻¹ := by group
    have h3 : τ (z⁻¹ * y) = k * (y * k' * (τ z)⁻¹) := by
      rw [hmul, hi, hy]
      group
    rw [h2, (hf.2 _ (K.inv_mem hk') _).2, hτ f hf, ← hτ g hg (z⁻¹ * y), h3, (hg.2 k hk _).1,
      mul_comm]
