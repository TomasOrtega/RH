import Mathlib
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLengthEqAndCardEqPowOfIsFiniteLength
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[Nat.card_congr (PadicInt.residueField (p := l)).toEquiv, Nat.card_zmod]`.
-/
theorem card_residueField_padicInt (l : ℕ) [Fact l.Prime] :
    Nat.card (IsLocalRing.ResidueField ℤ_[l]) = l := by
  rw [Nat.card_congr (PadicInt.residueField (p := l)).toEquiv, Nat.card_zmod]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨n, -, hc⟩` from `exists_length_eq_and_card_eq_pow_of_isFiniteLength ℤ_[l] X (Module.length_ne_top_iff.mp hne)`. Rewrite `hc` using `[card_residueField_padicInt]`. Conclude with `h (Nat.finite_of_card_ne_zero (by`. Rewrite using `[hc]`.

Conclude with `pow_ne_zero _ (Fact.out : l.Prime).ne_zero))`.
-/
theorem padicInt_length_eq_top_of_infinite (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X]
    [Module ℤ_[l] X] (h : ¬ Finite X) : Module.length ℤ_[l] X = ⊤ := by
  by_contra hne
  obtain ⟨n, -, hc⟩ := exists_length_eq_and_card_eq_pow_of_isFiniteLength ℤ_[l] X
    (Module.length_ne_top_iff.mp hne)
  rw [card_residueField_padicInt] at hc
  exact h (Nat.finite_of_card_ne_zero (by
    rw [hc]; exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero))

/- English proof (translation)
Take `⟨n, hn, hc⟩` from `exists_length_eq_and_card_eq_pow ℤ_[l] X`. Take `⟨m, hm, hd⟩` from `exists_length_eq_and_card_eq_pow ℤ_[l] Y`. Rewrite `hc`, `hd` using `[card_residueField_padicInt]`. Establish `: n = m` using `Nat.pow_right_injective (Fact.out : l.Prime).two_le (by`. Simplify using `only`.

Rewrite using `[← hc, ← hd, h])`. Rewrite using `[hn, hm, this]`.
-/
theorem padicInt_length_eq_of_card_eq (l : ℕ) [Fact l.Prime] (X Y : Type) [AddCommGroup X]
    [Module ℤ_[l] X] [AddCommGroup Y] [Module ℤ_[l] Y] [Finite X] [Finite Y]
    (h : Nat.card X = Nat.card Y) : Module.length ℤ_[l] X = Module.length ℤ_[l] Y := by
  obtain ⟨n, hn, hc⟩ := exists_length_eq_and_card_eq_pow ℤ_[l] X
  obtain ⟨m, hm, hd⟩ := exists_length_eq_and_card_eq_pow ℤ_[l] Y
  rw [card_residueField_padicInt] at hc hd
  have : n = m := Nat.pow_right_injective (Fact.out : l.Prime).two_le (by
    simp only; rw [← hc, ← hd, h])
  rw [hn, hm, this]

/- English proof (translation)
Establish `key : ∀ r0, c ≤ r0 → (∀ r, r0 ≤ r → Nat.card (P r) ≤ Nat.card (P r0)) → Module.length ℤ_[l] X = Module.length ℤ_[l] Y`. Introduce `r0 h0 hb`. Establish `hfin : ∀ r, c ≤ r → Finite (X ⧸ N r)` using `fun r hr => by`. Use `(hc r hr).1` as an intermediate fact. Conclude with `Nat.finite_of_card_ne_zero (by rw [(hc r hr).2]; exact Nat.card_pos.ne')`.

Establish `hPtop : P r0 = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `y _`. Take `⟨r, hr⟩` from `hex y`. Establish `hle : r0 ≤ max r r0` using `le_max_right _ _`.

Use `(hc _ (h0.trans hle)).1` as an intermediate fact. Establish `hbij : Function.Bijective (Submodule.inclusion (hP hle))` using `(Submodule.inclusion_injective _).bijective_of_nat_card_le (hb _ hle)`. Take `⟨z, hz⟩` from `hbij.2 ⟨y, hP (le_max_left r r0) hr⟩`. Establish `: (z : Y) = y` using `congrArg Subtype.val hz`. Conclude with `this ▸ z.2`.

Establish `hNbot : N r0 = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Use `(Submodule.mem_bot _).mpr (hsep x fun r => ?_)` and prove the remaining obligations. Establish `hle : r0 ≤ max r r0` using `le_max_right _ _`.

Use `hfin _ (h0.trans hle)` as an intermediate fact. Establish `hbij : Function.Bijective (Submodule.factor (hN hle))` using `(Submodule.factor_surjective _).bijective_of_nat_card_le (by`. Rewrite using `[(hc _ (h0.trans hle)).2, (hc _ h0).2]`. Conclude with `hb _ hle)`. Establish `h1 : (N (max r r0)).mkQ x = 0` using `hbij.1 (by`.

Rewrite using `[map_zero, Submodule.factor_mk]`. Conclude with `(Submodule.Quotient.mk_eq_zero _).mpr hx)`. Conclude with `hN (le_max_left r r0) ((Submodule.Quotient.mk_eq_zero _).mp h1)`. Establish `eX : (X ⧸ N r0) ≃ₗ[ℤ_[l]] X` using `Submodule.quotEquivOfEqBot _ hNbot`. Establish `eY : (P r0) ≃ₗ[ℤ_[l]] Y` using `LinearEquiv.ofTop _ hPtop`.

Use `hfin _ h0` as an intermediate fact. Use `(hc _ h0).1` as an intermediate fact. Rewrite using `[← eX.length_eq, ← eY.length_eq]`. Conclude with `padicInt_length_eq_of_card_eq l _ _ (hc _ h0).2`. Establish `bdd : ∀ B : ℕ, (∀ r, c ≤ r → Nat.card (P r) ≤ B) → Module.length ℤ_[l] X = Module.length ℤ_[l] Y`.

Introduce `B hB`. Establish `hS : ((fun r => Nat.card (P r)) '' {r | c ≤ r}).Finite` using `(Set.finite_le_nat B).subset (by rintro _ ⟨r, hr, rfl⟩; exact hB r hr)`. Take `⟨_, ⟨r0, hr0, rfl⟩, hmax⟩` from `Set.exists_max_image _ id hS ⟨_, c, le_refl c, rfl⟩`. Conclude with `key r0 hr0 fun r hr => hmax _ ⟨r, le_trans hr0 hr, rfl⟩`. Distinguish the cases in `hX : Finite X`.

Use `bdd (Nat.card X) fun r hr => ?_` and prove the remaining obligations. Rewrite using `[← (hc r hr).2]`. Conclude with `Nat.card_le_card_of_surjective _ (N r).mkQ_surjective`. Distinguish the cases in `hY : Finite Y`. Conclude with `bdd (Nat.card Y) fun r _ => Nat.card_le_card_of_injective _ (P r).subtype_injective`.

Rewrite using `[padicInt_length_eq_top_of_infinite l X hX, padicInt_length_eq_top_of_infinite l Y hY]`.
-/
theorem padicInt_length_eq_of_card_quotient_eq_card_submodule (l : ℕ) [Fact l.Prime] (X Y : Type)
    [AddCommGroup X] [Module ℤ_[l] X] [AddCommGroup Y] [Module ℤ_[l] Y]
    (N : ℕ → Submodule ℤ_[l] X) (P : ℕ → Submodule ℤ_[l] Y) (c : ℕ) (hN : Antitone N)
    (hsep : ∀ x, (∀ r, x ∈ N r) → x = 0) (hP : Monotone P) (hex : ∀ y, ∃ r, y ∈ P r)
    (hc : ∀ r, c ≤ r → Finite (P r) ∧ Nat.card (X ⧸ N r) = Nat.card (P r)) :
    Module.length ℤ_[l] X = Module.length ℤ_[l] Y := by
  have key : ∀ r0, c ≤ r0 → (∀ r, r0 ≤ r → Nat.card (P r) ≤ Nat.card (P r0)) →
      Module.length ℤ_[l] X = Module.length ℤ_[l] Y := by
    intro r0 h0 hb
    have hfin : ∀ r, c ≤ r → Finite (X ⧸ N r) := fun r hr => by
      have := (hc r hr).1
      exact Nat.finite_of_card_ne_zero (by rw [(hc r hr).2]; exact Nat.card_pos.ne')
    have hPtop : P r0 = ⊤ := by
      rw [eq_top_iff]
      intro y _
      obtain ⟨r, hr⟩ := hex y
      have hle : r0 ≤ max r r0 := le_max_right _ _
      have := (hc _ (h0.trans hle)).1
      have hbij : Function.Bijective (Submodule.inclusion (hP hle)) :=
        (Submodule.inclusion_injective _).bijective_of_nat_card_le (hb _ hle)
      obtain ⟨z, hz⟩ := hbij.2 ⟨y, hP (le_max_left r r0) hr⟩
      have : (z : Y) = y := congrArg Subtype.val hz
      exact this ▸ z.2
    have hNbot : N r0 = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      refine (Submodule.mem_bot _).mpr (hsep x fun r => ?_)
      have hle : r0 ≤ max r r0 := le_max_right _ _
      have := hfin _ (h0.trans hle)
      have hbij : Function.Bijective (Submodule.factor (hN hle)) :=
        (Submodule.factor_surjective _).bijective_of_nat_card_le (by
          rw [(hc _ (h0.trans hle)).2, (hc _ h0).2]; exact hb _ hle)
      have h1 : (N (max r r0)).mkQ x = 0 := hbij.1 (by
        rw [map_zero, Submodule.factor_mk]
        exact (Submodule.Quotient.mk_eq_zero _).mpr hx)
      exact hN (le_max_left r r0) ((Submodule.Quotient.mk_eq_zero _).mp h1)
    have eX : (X ⧸ N r0) ≃ₗ[ℤ_[l]] X := Submodule.quotEquivOfEqBot _ hNbot
    have eY : (P r0) ≃ₗ[ℤ_[l]] Y := LinearEquiv.ofTop _ hPtop
    have := hfin _ h0
    have := (hc _ h0).1
    rw [← eX.length_eq, ← eY.length_eq]
    exact padicInt_length_eq_of_card_eq l _ _ (hc _ h0).2
  have bdd : ∀ B : ℕ, (∀ r, c ≤ r → Nat.card (P r) ≤ B) →
      Module.length ℤ_[l] X = Module.length ℤ_[l] Y := by
    intro B hB
    have hS : ((fun r => Nat.card (P r)) '' {r | c ≤ r}).Finite :=
      (Set.finite_le_nat B).subset (by rintro _ ⟨r, hr, rfl⟩; exact hB r hr)
    obtain ⟨_, ⟨r0, hr0, rfl⟩, hmax⟩ := Set.exists_max_image _ id hS ⟨_, c, le_refl c, rfl⟩
    exact key r0 hr0 fun r hr => hmax _ ⟨r, le_trans hr0 hr, rfl⟩
  by_cases hX : Finite X
  · refine bdd (Nat.card X) fun r hr => ?_
    rw [← (hc r hr).2]
    exact Nat.card_le_card_of_surjective _ (N r).mkQ_surjective
  by_cases hY : Finite Y
  · exact bdd (Nat.card Y) fun r _ =>
      Nat.card_le_card_of_injective _ (P r).subtype_injective
  rw [padicInt_length_eq_top_of_infinite l X hX, padicInt_length_eq_top_of_infinite l Y hY]

end GlobalTheory
