import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

/- English proof (translation)
Use `haveI : Finite V := Module.finite_of_finite F`. Use `haveI : Finite (Submodule F V) := Finite.of_injective (fun W : Submodule F V => (W : Set V)) SetLike.coe_injective`. Use `haveI : Fintype {W : Submodule F V // ∀ x ∈ W, g x ∈ W} := Fintype.ofFinite _`. Establish `key : ∀ (W W' : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}) (v : W.1), (∀ U : Submodule F (W.1), (∀ x ∈ U, (g.restrict W.2) x ∈ U) → v ∈ U → U = ⊤) → (v : V) ∈ W'.1 → W.1 ≤ W'.1`. Introduce `W W' v hv hv' x hx`.

Establish `h` using `hv (W'.1.comap W.1.subtype) (fun y hy => W'.2 _ hy) hv'`. Establish `: (⟨x, hx⟩ : W.1) ∈ W'.1.comap W.1.subtype` using `h ▸ Submodule.mem_top`. Conclude with `this`. Set `f : (Σ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}, {v : W.1 // ∀ U : Submodule F (W.1), (∀ x ∈ U, (g.restrict W.2) x ∈ U) → v ∈ U → U = ⊤}) → V` to `fun p => (p.2.1 : V)`. Establish `hf : Function.Bijective f`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨W, v, hv⟩ ⟨W', v', hv'⟩ h`. Establish `h' : (v : V) = v'` using `h`. Establish `hW : W = W'` using `Subtype.ext (le_antisymm (key W W' v hv (h' ▸ v'.2)) (key W' W v' hv' (h' ▸ v.2)))`. Substitute `hW` using the available equality.

Establish `: v = v'` using `Subtype.ext h'`. Substitute `this` using the available equality. Both sides reduce to the same expression. Introduce `v`. Set `S : Set (Submodule F V)` to `{U | (∀ x ∈ U, g x ∈ U) ∧ v ∈ U}`.

Establish `hinv : ∀ x ∈ sInf S, g x ∈ sInf S`. Introduce `x hx`. Rewrite `hx`, the goal using `[Submodule.mem_sInf]`. Conclude with `fun p hp => hp.1 x (hx p hp)`. Establish `hv : v ∈ sInf S`.

Rewrite using `[Submodule.mem_sInf]`. Conclude with `fun p hp => hp.2`. Use `⟨⟨⟨sInf S, hinv⟩, ⟨v, hv⟩, ?_⟩, rfl⟩` and prove the remaining obligations. Introduce `U hU hvU`. Establish `hle : sInf S ≤ U.map (sInf S).subtype`.

Use `sInf_le ⟨?_, ⟨_, hvU, rfl⟩⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `⟨_, hU y hy, rfl⟩`. Rewrite using `[eq_top_iff]`. Introduce and unpack `⟨x, hx⟩ -`.

Take `⟨y, hy, hyx⟩` from `hle hx`. Establish `: y = ⟨x, hx⟩` using `Subtype.ext hyx`. Conclude with `this ▸ hy`. Establish `hc` using `Nat.card_congr (Equiv.ofBijective f hf)`. Rewrite `hc` using `[Nat.card_sigma, Module.natCard_eq_pow_finrank (K := F)]`.

Rewrite using `[finsum_eq_sum_of_fintype]`. Conclude with `hc` after adjusting the coercions.
-/
theorem finsum_card_cyclic_eq (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (g : Module.End F V) :
    ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W},
      (Nat.card {v : W.1 // ∀ U : Submodule F (W.1),
        (∀ x ∈ U, (g.restrict W.2) x ∈ U) → v ∈ U → U = ⊤} : ℂ)
      = (Nat.card F : ℂ) ^ Module.finrank F V := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Submodule F V) :=
    Finite.of_injective (fun W : Submodule F V => (W : Set V)) SetLike.coe_injective
  haveI : Fintype {W : Submodule F V // ∀ x ∈ W, g x ∈ W} := Fintype.ofFinite _
  have key : ∀ (W W' : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}) (v : W.1),
      (∀ U : Submodule F (W.1), (∀ x ∈ U, (g.restrict W.2) x ∈ U) → v ∈ U → U = ⊤) →
      (v : V) ∈ W'.1 → W.1 ≤ W'.1 := by
    intro W W' v hv hv' x hx
    have h := hv (W'.1.comap W.1.subtype) (fun y hy => W'.2 _ hy) hv'
    have : (⟨x, hx⟩ : W.1) ∈ W'.1.comap W.1.subtype := h ▸ Submodule.mem_top
    exact this
  let f : (Σ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}, {v : W.1 // ∀ U : Submodule F (W.1),
        (∀ x ∈ U, (g.restrict W.2) x ∈ U) → v ∈ U → U = ⊤}) → V := fun p => (p.2.1 : V)
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨W, v, hv⟩ ⟨W', v', hv'⟩ h
      have h' : (v : V) = v' := h
      have hW : W = W' := Subtype.ext (le_antisymm (key W W' v hv (h' ▸ v'.2))
        (key W' W v' hv' (h' ▸ v.2)))
      subst hW
      have : v = v' := Subtype.ext h'
      subst this
      rfl
    · intro v
      let S : Set (Submodule F V) := {U | (∀ x ∈ U, g x ∈ U) ∧ v ∈ U}
      have hinv : ∀ x ∈ sInf S, g x ∈ sInf S := by
        intro x hx
        rw [Submodule.mem_sInf] at hx ⊢
        exact fun p hp => hp.1 x (hx p hp)
      have hv : v ∈ sInf S := by
        rw [Submodule.mem_sInf]
        exact fun p hp => hp.2
      refine ⟨⟨⟨sInf S, hinv⟩, ⟨v, hv⟩, ?_⟩, rfl⟩
      intro U hU hvU
      have hle : sInf S ≤ U.map (sInf S).subtype := by
        refine sInf_le ⟨?_, ⟨_, hvU, rfl⟩⟩
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨_, hU y hy, rfl⟩
      rw [eq_top_iff]
      rintro ⟨x, hx⟩ -
      obtain ⟨y, hy, hyx⟩ := hle hx
      have : y = ⟨x, hx⟩ := Subtype.ext hyx
      exact this ▸ hy
  have hc := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_sigma, Module.natCard_eq_pow_finrank (K := F)] at hc
  rw [finsum_eq_sum_of_fintype]
  exact_mod_cast hc

end GlobalTheory.CuspGL
