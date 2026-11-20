import Mathlib
open scoped Pointwise

namespace GlobalTheory

/- English proof (translation)
Use `set U : Subgroup G := T ⊓ K'.map (MulAut.conj x).toMonoidHom with hU`. Establish `memU : ∀ u : G, u ∈ U ↔ u ∈ T ∧ x⁻¹ * u * x ∈ K'`. Introduce `u`. Simplify using `only [hU, Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hT, k, hk, rfl⟩`. Conclude with `⟨hT, by simpa [mul_assoc] using hk⟩`. Introduce and unpack `⟨hT, hk⟩`. Conclude with `⟨hT, _, hk, by group⟩`. Set `F` to `fun q : DoubleCoset.Quotient ((Γ ⊓ T : Subgroup G) : Set G) (K' : Set G) => DoubleCoset.mk T K' (Quotient.out q)`.

Establish `hland : ∀ t : T, DoubleCoset.mk (Γ ⊓ T) K' ((t : G) * x) ∈ F ⁻¹' {DoubleCoset.mk T K' x}`. Introduce `t`. Take `⟨h, k, hh, hk, he⟩` from `DoubleCoset.mk_out_eq_mul (Γ ⊓ T) K' ((t : G) * x)`. Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff, F]`. Rewrite using `[eq_comm, DoubleCoset.eq]`.

Use `⟨h * t, T.mul_mem (Subgroup.mem_inf.mp hh).2 t.2, k, hk, ?_⟩` and prove the remaining obligations. Rewrite using `[he]`. Use `group`. Set `φ₀ : T → F ⁻¹' {DoubleCoset.mk T K' x}` to `fun t => ⟨_, hland t⟩`. Establish `hwd : ∀ a b : T, (DoubleCoset.setoid ((Γ.subgroupOf T : Subgroup T) : Set T) ((U.subgroupOf T : Subgroup T) : Set T)) a b → φ₀ a = φ₀ b`.

Introduce `a b hab`. Take `⟨g, hg, u, hu, rfl⟩` from `DoubleCoset.rel_iff.mp hab`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [φ₀]`. Rewrite using `[DoubleCoset.eq]`.

Rewrite `hg`, `hu` using `[Subgroup.mem_subgroupOf]`. Use `⟨g, Subgroup.mem_inf.mpr ⟨hg, g.2⟩, x⁻¹ * u * x, ((memU u).mp hu).2, ?_⟩` and prove the remaining obligations. Simplify using `only [Subgroup.coe_mul]`. Use `group`. Set `φ : DoubleCoset.Quotient ((Γ.subgroupOf T : Subgroup T) : Set T) ((U.subgroupOf T : Subgroup T) : Set T) → F ⁻¹' {DoubleCoset.mk T K' x}` to `Quotient.lift (s := DoubleCoset.setoid _ _) φ₀ hwd`.

Establish `hφ : Function.Bijective φ`. Prove the components needed by the constructor for the conclusion. Introduce `p q hpq`. Proceed by induction on `p using Quotient.inductionOn with | h a => ?_`. Proceed by induction on `q using Quotient.inductionOn with | h b => ?_`.

Establish `h1 : DoubleCoset.mk (Γ ⊓ T) K' ((a : G) * x) = DoubleCoset.mk (Γ ⊓ T) K' ((b : G) * x)` using `congrArg Subtype.val hpq`. Take `⟨h, hh, k, hk, he⟩` from `(DoubleCoset.eq _ _ _ _).mp h1`. Establish `hhT : h ∈ T` using `(Subgroup.mem_inf.mp hh).2`. Establish `huT : (a : G)⁻¹ * h⁻¹ * b ∈ T` using `T.mul_mem (T.mul_mem (T.inv_mem a.2) (T.inv_mem hhT)) b.2`. Apply `Quotient.sound` to reduce the goal to its premises.

Use `DoubleCoset.rel_iff.mpr ⟨⟨h, hhT⟩, ?_, ⟨_, huT⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.mem_subgroupOf]`. Conclude with `(Subgroup.mem_inf.mp hh).1`. Rewrite using `[Subgroup.mem_subgroupOf, memU]`. Use `⟨huT, ?_⟩` and prove the remaining obligations.

Establish `: x⁻¹ * ((a : G)⁻¹ * h⁻¹ * b) * x = k`. Rewrite using `[show (b : G) = h * a * x * k * x⁻¹ by`. Rewrite using `[show h * (a : G) * x * k * x⁻¹ = h * ((a : G) * x) * k * x⁻¹ by group, ← he]; group]`. Use `group`. Rewrite using `[this]`.

Conclude with `hk`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Subgroup.coe_mul]`. Use `group`. Introduce and unpack `⟨q, hq⟩`.

Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff, F] at hq`. Take `⟨s, hs, k, hk, he⟩` from `(DoubleCoset.eq _ _ _ _).mp hq`. Use `⟨Quotient.mk _ ⟨s⁻¹, T.inv_mem hs⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use `show DoubleCoset.mk (Γ ⊓ T) K' (s⁻¹ * x) = q`.

Use `conv_rhs => rw [← DoubleCoset.out_eq' _ _ q]`. Rewrite using `[DoubleCoset.eq]`. Use `⟨1, Subgroup.one_mem _, k⁻¹, K'.inv_mem hk, ?_⟩` and prove the remaining obligations. Rewrite using `[he]`. Use `group`.

Conclude with `(Nat.card_eq_of_bijective φ hφ).symm`.
-/
theorem doubleCoset_fibre_card {G : Type} [Group G] (T Γ K' : Subgroup G) (x : G) :
    Nat.card ((fun q : DoubleCoset.Quotient ((Γ ⊓ T : Subgroup G) : Set G) (K' : Set G) =>
        DoubleCoset.mk T K' (Quotient.out q)) ⁻¹' {DoubleCoset.mk T K' x}) =
      Nat.card (DoubleCoset.Quotient ((Γ.subgroupOf T : Subgroup T) : Set T)
        (((T ⊓ K'.map (MulAut.conj x).toMonoidHom).subgroupOf T : Subgroup T) : Set T)) := by
  classical
  set U : Subgroup G := T ⊓ K'.map (MulAut.conj x).toMonoidHom with hU
  have memU : ∀ u : G, u ∈ U ↔ u ∈ T ∧ x⁻¹ * u * x ∈ K' := by
    intro u
    simp only [hU, Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨hT, k, hk, rfl⟩
      exact ⟨hT, by simpa [mul_assoc] using hk⟩
    · rintro ⟨hT, hk⟩
      exact ⟨hT, _, hk, by group⟩
  let F := fun q : DoubleCoset.Quotient ((Γ ⊓ T : Subgroup G) : Set G) (K' : Set G) =>
        DoubleCoset.mk T K' (Quotient.out q)
  have hland : ∀ t : T, DoubleCoset.mk (Γ ⊓ T) K' ((t : G) * x) ∈ F ⁻¹' {DoubleCoset.mk T K' x} := by
    intro t
    obtain ⟨h, k, hh, hk, he⟩ := DoubleCoset.mk_out_eq_mul (Γ ⊓ T) K' ((t : G) * x)
    simp only [Set.mem_preimage, Set.mem_singleton_iff, F]
    rw [eq_comm, DoubleCoset.eq]
    refine ⟨h * t, T.mul_mem (Subgroup.mem_inf.mp hh).2 t.2, k, hk, ?_⟩
    rw [he]; group
  let φ₀ : T → F ⁻¹' {DoubleCoset.mk T K' x} := fun t => ⟨_, hland t⟩
  have hwd : ∀ a b : T, (DoubleCoset.setoid ((Γ.subgroupOf T : Subgroup T) : Set T)
      ((U.subgroupOf T : Subgroup T) : Set T)) a b → φ₀ a = φ₀ b := by
    intro a b hab
    obtain ⟨g, hg, u, hu, rfl⟩ := DoubleCoset.rel_iff.mp hab
    apply Subtype.ext
    simp only [φ₀]
    rw [DoubleCoset.eq]
    rw [Subgroup.mem_subgroupOf] at hg hu
    refine ⟨g, Subgroup.mem_inf.mpr ⟨hg, g.2⟩, x⁻¹ * u * x, ((memU u).mp hu).2, ?_⟩
    simp only [Subgroup.coe_mul]
    group
  let φ : DoubleCoset.Quotient ((Γ.subgroupOf T : Subgroup T) : Set T)
      ((U.subgroupOf T : Subgroup T) : Set T) → F ⁻¹' {DoubleCoset.mk T K' x} :=
    Quotient.lift (s := DoubleCoset.setoid _ _) φ₀ hwd
  have hφ : Function.Bijective φ := by
    constructor
    · intro p q hpq
      induction p using Quotient.inductionOn with | h a => ?_
      induction q using Quotient.inductionOn with | h b => ?_
      have h1 : DoubleCoset.mk (Γ ⊓ T) K' ((a : G) * x) = DoubleCoset.mk (Γ ⊓ T) K' ((b : G) * x) :=
        congrArg Subtype.val hpq
      obtain ⟨h, hh, k, hk, he⟩ := (DoubleCoset.eq _ _ _ _).mp h1
      have hhT : h ∈ T := (Subgroup.mem_inf.mp hh).2
      have huT : (a : G)⁻¹ * h⁻¹ * b ∈ T :=
        T.mul_mem (T.mul_mem (T.inv_mem a.2) (T.inv_mem hhT)) b.2
      apply Quotient.sound
      refine DoubleCoset.rel_iff.mpr ⟨⟨h, hhT⟩, ?_, ⟨_, huT⟩, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]; exact (Subgroup.mem_inf.mp hh).1
      · rw [Subgroup.mem_subgroupOf, memU]
        refine ⟨huT, ?_⟩
        have : x⁻¹ * ((a : G)⁻¹ * h⁻¹ * b) * x = k := by
          rw [show (b : G) = h * a * x * k * x⁻¹ by
            rw [show h * (a : G) * x * k * x⁻¹ = h * ((a : G) * x) * k * x⁻¹ by group, ← he]; group]
          group
        rw [this]; exact hk
      · apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group
    · rintro ⟨q, hq⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff, F] at hq
      obtain ⟨s, hs, k, hk, he⟩ := (DoubleCoset.eq _ _ _ _).mp hq
      refine ⟨Quotient.mk _ ⟨s⁻¹, T.inv_mem hs⟩, ?_⟩
      apply Subtype.ext
      show DoubleCoset.mk (Γ ⊓ T) K' (s⁻¹ * x) = q
      conv_rhs => rw [← DoubleCoset.out_eq' _ _ q]
      rw [DoubleCoset.eq]
      refine ⟨1, Subgroup.one_mem _, k⁻¹, K'.inv_mem hk, ?_⟩
      rw [he]; group
  exact (Nat.card_eq_of_bijective φ hφ).symm

end GlobalTheory
