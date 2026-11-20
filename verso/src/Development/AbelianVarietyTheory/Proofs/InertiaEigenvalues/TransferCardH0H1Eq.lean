import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.ShapeNeg

/- English proof (translation)
Introduce `O _ G G' _ _ _ _ i M _ _ ρ p r _ c h`. Use `letI := levZ (M := M) p r h`. Establish `hact : ∀ (g' : G') (x : Lev M c), levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom) g' x = levRep ρ c (i.symm g') x` using `fun g' x => rfl`. Prove the components needed by the constructor for the conclusion. Apply `Nat.card_congr` to reduce the goal to its premises.

Use `Equiv.subtypeEquivRight ?_` and prove the remaining obligations. Introduce `x`. Use `show (∀ g, levRep ρ c g x = x) ↔ ∀ g', levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom) g' x = x`. Prove the components needed by the constructor for the conclusion. Introduce `hx g'`.

Rewrite using `[hact]`. Conclude with `hx _`. Introduce `hx g`. Use `hx (i g)` as an intermediate fact. Rewrite `this` using `[hact, ContinuousMulEquiv.symm_apply_apply]`.

Conclude with `this`. Apply `Nat.card_congr` to reduce the goal to its premises. Set `ρ'` to `levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom)`. Establish `hs : Continuous (i.symm : G' → G)` using `i.symm.continuous`. Establish `hi : Continuous (i : G → G')` using `i.continuous`.

Set `e : Z1 (levRep ρ c) ≃ Z1 ρ'` to `{ toFun := fun f => ⟨(f : G → Lev M c) ∘ i.symm, f.2.1.comp hs, fun a b => by show (f : G → Lev M c) (i.symm (a * b)) = (f : G → Lev M c) (i.symm a) + ρ' a ((f : G → Lev M c) (i.symm b))`. Rewrite using `[map_mul, f.2.2]`. Use the proof step `rfl⟩`. Use `invFun := fun f => ⟨(f : G' → Lev M c) ∘ i, f.2.1.comp hi, fun a b => by show (f : G' → Lev M c) (i (a * b)) = (f : G' → Lev M c) (i a) + levRep ρ c a ((f : G' → Lev M c) (i b))`. Rewrite using `[map_mul, f.2.2, hact, ContinuousMulEquiv.symm_apply_apply]⟩`.

Use `left_inv := fun f => by`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Use `show (f : G → Lev M c) (i.symm (i g)) = _`. Rewrite using `[ContinuousMulEquiv.symm_apply_apply]`.

Use `right_inv := fun f => by`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Use `show (f : G' → Lev M c) (i (i.symm g)) = _`. Rewrite using `[ContinuousMulEquiv.apply_symm_apply] }`.

Use `Quotient.congr e ?_` and prove the remaining obligations. Introduce `a b`. Rewrite using `[Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap, Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_subtype, mem_coboundaries1, mem_coboundaries1]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, hm⟩`.

Use `⟨m, fun g' => ?_⟩` and prove the remaining obligations. Use `hm (i.symm g')` as an intermediate fact. Rewrite using `[hact]`. Conclude with `this`. Introduce and unpack `⟨m, hm⟩`.

Use `⟨m, fun g => ?_⟩` and prove the remaining obligations. Use `hm (i g)` as an intermediate fact. Rewrite `this` using `[hact]`. Express the relevant statement in the definitionally equal form `(a : G → Lev M c) (i.symm (i g)) - (b : G → Lev M c) (i.symm (i g)) = _ at this`. Rewrite `this` using `[ContinuousMulEquiv.symm_apply_apply]`.

Conclude with `this`.
-/
theorem transfer_card_H0_H1 : ∀ {O : Type} [CommRing O] {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
    (i : G ≃ₜ* G') {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M)
    (p r : ℕ) [NeZero (p ^ r)] (c : O) (h : ((p : O) ^ r) ∈ Ideal.span {c}),
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p r h
    Nat.card (ReciprocityTheory.Gal.H0 (GlobalTheory.ShapeNeg.levRep ρ c)) =
        Nat.card (ReciprocityTheory.Gal.H0 (GlobalTheory.ShapeNeg.levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom))) ∧
      Nat.card (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRep ρ c)) =
        Nat.card (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom))) := by
  intro O _ G G' _ _ _ _ i M _ _ ρ p r _ c h
  letI := levZ (M := M) p r h

  have hact : ∀ (g' : G') (x : Lev M c),
      levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom) g' x = levRep ρ c (i.symm g') x :=
    fun g' x => rfl
  constructor
  · apply Nat.card_congr
    refine Equiv.subtypeEquivRight ?_
    intro x
    show (∀ g, levRep ρ c g x = x) ↔ ∀ g', levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom) g' x = x
    constructor
    · intro hx g'; rw [hact]; exact hx _
    · intro hx g
      have := hx (i g)
      rw [hact, ContinuousMulEquiv.symm_apply_apply] at this
      exact this
  · apply Nat.card_congr
    let ρ' := levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom)
    have hs : Continuous (i.symm : G' → G) := i.symm.continuous
    have hi : Continuous (i : G → G') := i.continuous
    let e : Z1 (levRep ρ c) ≃ Z1 ρ' :=
      { toFun := fun f => ⟨(f : G → Lev M c) ∘ i.symm, f.2.1.comp hs, fun a b => by
          show (f : G → Lev M c) (i.symm (a * b)) = (f : G → Lev M c) (i.symm a) + ρ' a ((f : G → Lev M c) (i.symm b))
          rw [map_mul, f.2.2]; rfl⟩
        invFun := fun f => ⟨(f : G' → Lev M c) ∘ i, f.2.1.comp hi, fun a b => by
          show (f : G' → Lev M c) (i (a * b)) = (f : G' → Lev M c) (i a) + levRep ρ c a ((f : G' → Lev M c) (i b))
          rw [map_mul, f.2.2, hact, ContinuousMulEquiv.symm_apply_apply]⟩
        left_inv := fun f => by
          apply Subtype.ext; funext g; show (f : G → Lev M c) (i.symm (i g)) = _
          rw [ContinuousMulEquiv.symm_apply_apply]
        right_inv := fun f => by
          apply Subtype.ext; funext g; show (f : G' → Lev M c) (i (i.symm g)) = _
          rw [ContinuousMulEquiv.apply_symm_apply] }
    refine Quotient.congr e ?_
    intro a b
    rw [Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap, Submodule.mem_comap,
      Submodule.coe_subtype, Submodule.coe_subtype, mem_coboundaries1, mem_coboundaries1]
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨m, fun g' => ?_⟩
      have := hm (i.symm g')
      rw [hact]
      exact this
    · rintro ⟨m, hm⟩
      refine ⟨m, fun g => ?_⟩
      have := hm (i g)
      rw [hact] at this
      change (a : G → Lev M c) (i.symm (i g)) - (b : G → Lev M c) (i.symm (i g)) = _ at this
      rw [ContinuousMulEquiv.symm_apply_apply] at this
      exact this

end GlobalTheory.ShapeNeg
