import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
open CompanionTheory.Rg.Fl

namespace GlobalTheory.CompanionTheory.RgFl

variable {G G' : Type} [Group G] [Group G']

def cosetEquiv (e : G ≃* G') (K : Subgroup G) : G ⧸ K ≃ G' ⧸ K.map e.toMonoidHom :=
  Quotient.congr (ra := QuotientGroup.leftRel K) (rb := QuotientGroup.leftRel (K.map e.toMonoidHom))
    e.toEquiv (by
      intro a b
      have h : (e.toEquiv a)⁻¹ * e.toEquiv b = e.toMonoidHom (a⁻¹ * b) := by simp
      rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, h]
      exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).symm)

/- English proof (translation)
Proceed by induction on `x using QuotientGroup.induction_on with`. Consider the case `H a`. Express the relevant statement in the definitionally equal form `((e (g * a) : G') : G' ⧸ K.map e.toMonoidHom) = ((e g * e a : G') : G' ⧸ K.map e.toMonoidHom)`. Rewrite using `[map_mul]`.
-/
lemma cosetEquiv_smul (e : G ≃* G') (K : Subgroup G) (g : G) (x : G ⧸ K) :
    cosetEquiv e K (g • x) = e g • cosetEquiv e K x := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    change ((e (g * a) : G') : G' ⧸ K.map e.toMonoidHom) = ((e g * e a : G') : G' ⧸ K.map e.toMonoidHom)
    rw [map_mul]

/- English proof (translation)
Introduce `G G' _ _ e K hK S`. Set `φ` to `cosetEquiv e K`. Take `⟨Γ', hfin, hstab, hsep⟩` from `hK (S.image φ)`. Set `Γ : Subgroup G` to `Γ'.comap e.toMonoidHom`. Establish `hmem : ∀ γ : Γ, e (γ : G) ∈ Γ'` using `fun γ => γ.2`.

Establish `hsymm : ∀ γ' : Γ', e.symm (γ' : G') ∈ Γ` using `fun γ' => by`. Express the relevant statement in the definitionally equal form `e (e.symm (γ' : G')) ∈ Γ'`. Simplify using `using γ'.2`. Establish `hact : ∀ (γ : Γ) (x : G ⧸ K), φ (γ • x) = (⟨e (γ : G), hmem γ⟩ : Γ') • φ x` using `fun γ x => cosetEquiv_smul e K (γ : G) x`. Use `⟨Γ, ?_, ?_, ?_⟩` and prove the remaining obligations.

Set `f : MulAction.orbitRel.Quotient Γ' (G' ⧸ K.map e.toMonoidHom) → MulAction.orbitRel.Quotient Γ (G ⧸ K)` to `Quotient.map' φ.symm (by`. Introduce and unpack `a b ⟨γ', rfl⟩`. Use `⟨⟨e.symm (γ' : G'), hsymm γ'⟩, ?_⟩` and prove the remaining obligations. Apply `φ.injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `φ (_ • φ.symm b) = φ (φ.symm (γ' • b))`.

Rewrite using `[hact]`. Establish `h : (⟨e (e.symm (γ' : G')), hmem ⟨e.symm (γ' : G'), hsymm γ'⟩⟩ : Γ') = γ'` using `Subtype.ext (e.apply_symm_apply _)`. Rewrite using `[h, φ.apply_symm_apply, φ.apply_symm_apply])`. Use `Finite.of_surjective f ?_` and prove the remaining obligations. Introduce `q`.

Proceed by induction on `q using Quotient.inductionOn' with`. Consider the case `h x`. Conclude with `⟨Quotient.mk'' (φ x), congrArg (Quotient.mk'' (s₁ := MulAction.orbitRel Γ (G ⧸ K))) (φ.symm_apply_apply x)⟩`. Introduce `x`. Set `f : MulAction.stabilizer Γ x → MulAction.stabilizer Γ' (φ x)` to `fun γ => ⟨⟨e ((γ : Γ) : G), hmem γ⟩, by`.

Rewrite using `[MulAction.mem_stabilizer_iff, ← hact, MulAction.mem_stabilizer_iff.mp γ.2]⟩`. Use `Finite.of_injective f ?_` and prove the remaining obligations. Introduce `a b hab`. Establish `h` using `congrArg (fun c : MulAction.stabilizer Γ' (φ x) => ((c : Γ') : G')) hab`. Conclude with `Subtype.ext (Subtype.ext (e.injective h))`.

Introduce `x hx y hy γ hxy`. Apply `φ.injective` to reduce the goal to its premises. Conclude with `hsep (φ x) (Finset.mem_image_of_mem φ hx) (φ y) (Finset.mem_image_of_mem φ hy) ⟨e (γ : G), hmem γ⟩ (by rw [← hact, hxy])`.
-/
theorem stSepMove : StSepMove := by
  intro G G' _ _ e K hK S
  classical
  let φ := cosetEquiv e K
  obtain ⟨Γ', hfin, hstab, hsep⟩ := hK (S.image φ)
  let Γ : Subgroup G := Γ'.comap e.toMonoidHom
  have hmem : ∀ γ : Γ, e (γ : G) ∈ Γ' := fun γ => γ.2
  have hsymm : ∀ γ' : Γ', e.symm (γ' : G') ∈ Γ := fun γ' => by
    change e (e.symm (γ' : G')) ∈ Γ'
    simpa using γ'.2
  have hact : ∀ (γ : Γ) (x : G ⧸ K), φ (γ • x) = (⟨e (γ : G), hmem γ⟩ : Γ') • φ x := fun γ x =>
    cosetEquiv_smul e K (γ : G) x
  refine ⟨Γ, ?_, ?_, ?_⟩
  · let f : MulAction.orbitRel.Quotient Γ' (G' ⧸ K.map e.toMonoidHom) →
        MulAction.orbitRel.Quotient Γ (G ⧸ K) :=
      Quotient.map' φ.symm (by
        rintro a b ⟨γ', rfl⟩
        refine ⟨⟨e.symm (γ' : G'), hsymm γ'⟩, ?_⟩
        apply φ.injective
        change φ (_ • φ.symm b) = φ (φ.symm (γ' • b))
        rw [hact]
        have h : (⟨e (e.symm (γ' : G')), hmem ⟨e.symm (γ' : G'), hsymm γ'⟩⟩ : Γ') = γ' :=
          Subtype.ext (e.apply_symm_apply _)
        rw [h, φ.apply_symm_apply, φ.apply_symm_apply])
    refine Finite.of_surjective f ?_
    intro q
    induction q using Quotient.inductionOn' with
    | h x =>
      exact ⟨Quotient.mk'' (φ x),
        congrArg (Quotient.mk'' (s₁ := MulAction.orbitRel Γ (G ⧸ K))) (φ.symm_apply_apply x)⟩
  · intro x
    let f : MulAction.stabilizer Γ x → MulAction.stabilizer Γ' (φ x) := fun γ =>
      ⟨⟨e ((γ : Γ) : G), hmem γ⟩, by
        rw [MulAction.mem_stabilizer_iff, ← hact, MulAction.mem_stabilizer_iff.mp γ.2]⟩
    refine Finite.of_injective f ?_
    intro a b hab
    have h := congrArg (fun c : MulAction.stabilizer Γ' (φ x) => ((c : Γ') : G')) hab
    exact Subtype.ext (Subtype.ext (e.injective h))
  · intro x hx y hy γ hxy
    apply φ.injective
    exact hsep (φ x) (Finset.mem_image_of_mem φ hx) (φ y) (Finset.mem_image_of_mem φ hy)
      ⟨e (γ : G), hmem γ⟩ (by rw [← hact, hxy])

end GlobalTheory.CompanionTheory.RgFl
