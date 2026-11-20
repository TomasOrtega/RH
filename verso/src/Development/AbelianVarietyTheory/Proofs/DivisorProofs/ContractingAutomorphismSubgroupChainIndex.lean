import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

/- English proof (translation)
Use extensionality with `a`. Establish `h : (c ^ (j + 1)) a = c ((c ^ j) a)`. Rewrite using `[add_comm, zpow_add, zpow_one, MulAut.mul_apply]`. Simplify using `only [Subgroup.mem_comap, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, h]`. Prove the components needed by the constructor for the conclusion.

Introduce `ha`. Conclude with `⟨_, ha, rfl⟩`. Introduce and unpack `⟨x, hx, hxa⟩`. Rewrite using `[← c.injective hxa]`. Conclude with `hx`.
-/
theorem chain_comap_eq {A : Type} [Group A] (U : Subgroup A) (c : MulAut A) (j : ℤ) :
    U.comap (c ^ j).toMonoidHom = (U.map c.toMonoidHom).comap (c ^ (j + 1)).toMonoidHom := by
  ext a
  have h : (c ^ (j + 1)) a = c ((c ^ j) a) := by
    rw [add_comm, zpow_add, zpow_one, MulAut.mul_apply]
  simp only [Subgroup.mem_comap, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, h]
  constructor
  · intro ha
    exact ⟨_, ha, rfl⟩
  · rintro ⟨x, hx, hxa⟩
    rw [← c.injective hxa]
    exact hx

/- English proof (translation)
Rewrite using `[chain_comap_eq U c j]`. Use `⟨Subgroup.comap_mono ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `hc x hx`. Rewrite using `[Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective]`.

Conclude with `(c ^ (j + 1)).surjective`.
-/
theorem chain_step {A : Type} [Group A] (U : Subgroup A) (c : MulAut A) (hc : ∀ a ∈ U, c a ∈ U) (j : ℤ) :
    U.comap (c ^ j).toMonoidHom ≤ U.comap (c ^ (j + 1)).toMonoidHom ∧
      (U.comap (c ^ j).toMonoidHom).relIndex (U.comap (c ^ (j + 1)).toMonoidHom) =
        (U.map c.toMonoidHom).relIndex U := by
  rw [chain_comap_eq U c j]
  refine ⟨Subgroup.comap_mono ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hc x hx
  · rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective]
    exact (c ^ (j + 1)).surjective

/- English proof (translation)
Introduce `A _ U c Q hc hQ j l`. Proceed by induction on `l with`. Consider the case `zero => simp`. Consider the case `succ l ih`. Take `⟨h1, h2⟩` from `chain_step U c hc (j + l)`.

Establish `e : j + ((l + 1 : ℕ) : ℤ) = j + l + 1` using `by push_cast; ring`. Rewrite using `[e]`. Use `⟨ih.1.trans h1, ?_⟩` and prove the remaining obligations. Rewrite using `[← Subgroup.relIndex_mul_relIndex _ _ _ ih.1 h1, ih.2, h2, hQ, pow_succ]`.
-/
theorem chainIndex : ChainIndex := by
  intro A _ U c Q hc hQ j l
  induction l with
  | zero => simp
  | succ l ih =>
    obtain ⟨h1, h2⟩ := chain_step U c hc (j + l)
    have e : j + ((l + 1 : ℕ) : ℤ) = j + l + 1 := by push_cast; ring
    rw [e]
    refine ⟨ih.1.trans h1, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ ih.1 h1, ih.2, h2, hQ, pow_succ]

end GlobalTheory.SatakeWeyl
