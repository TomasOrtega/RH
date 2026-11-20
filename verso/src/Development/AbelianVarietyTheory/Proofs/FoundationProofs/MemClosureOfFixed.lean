import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.ArtinFix

variable {K G : Type} [Field K] [Group G] (ρ : G →* RingAut K)

/- English proof (translation)
Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
lemma rho_mul_apply (a b : G) (x : K) : ρ (a * b) x = ρ a (ρ b x) := by
  rw [map_mul]; rfl

/- English proof (translation)
Rewrite using `[← rho_mul_apply, inv_mul_cancel, map_one]`. Both sides reduce to the same expression.
-/
lemma rho_inv_apply_apply (g : G) (x : K) : ρ g⁻¹ (ρ g x) = x := by
  rw [← rho_mul_apply, inv_mul_cancel, map_one]; rfl

/- English proof (translation)
Rewrite using `[← rho_mul_apply, mul_inv_cancel, map_one]`. Both sides reduce to the same expression.
-/
lemma rho_apply_inv_apply (g : G) (x : K) : ρ g (ρ g⁻¹ x) = x := by
  rw [← rho_mul_apply, mul_inv_cancel, map_one]; rfl

variable (Δ : Subgroup G)

def fixSub : Subfield K where
  carrier := {x | ∀ δ ∈ Δ, ρ δ x = x}
  mul_mem' := by
    intro a b ha hb δ hδ
    simp [map_mul, ha δ hδ, hb δ hδ]
  one_mem' := by intro δ _; simp
  add_mem' := by
    intro a b ha hb δ hδ
    simp [map_add, ha δ hδ, hb δ hδ]
  zero_mem' := by intro δ _; simp
  neg_mem' := by
    intro a ha δ hδ
    simp [map_neg, ha δ hδ]
  inv_mem' := by
    intro a ha δ hδ
    simp [map_inv₀, ha δ hδ]

/- English proof (translation)
Introduce `δ hδ`. Establish `hm : g⁻¹ * δ * g ∈ Δ` using `by simpa using hN.conj_mem δ hδ g⁻¹`. Establish `h` using `hx _ hm`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← rho_mul_apply, ← rho_mul_apply]`.

Use `congr 1`. Use `group`. Use `_ = ρ g x := by rw [h]`.
-/
lemma map_mem_fixSub [hN : Δ.Normal] (g : G) {x : K} (hx : x ∈ fixSub ρ Δ) :
    ρ g x ∈ fixSub ρ Δ := by
  intro δ hδ
  have hm : g⁻¹ * δ * g ∈ Δ := by simpa using hN.conj_mem δ hδ g⁻¹
  have h := hx _ hm
  calc ρ δ (ρ g x) = ρ g (ρ (g⁻¹ * δ * g) x) := by
        rw [← rho_mul_apply, ← rho_mul_apply]; congr 1; group
    _ = ρ g x := by rw [h]

def restr [Δ.Normal] : G →* RingAut (fixSub ρ Δ) where
  toFun g :=
    { toFun := fun x => ⟨ρ g x, map_mem_fixSub ρ Δ g x.2⟩
      invFun := fun x => ⟨ρ g⁻¹ x, map_mem_fixSub ρ Δ g⁻¹ x.2⟩
      left_inv := fun x => Subtype.ext (rho_inv_apply_apply ρ g (x : K))
      right_inv := fun x => Subtype.ext (rho_apply_inv_apply ρ g (x : K))
      map_mul' := fun x y => Subtype.ext (map_mul (ρ g) (x : K) (y : K))
      map_add' := fun x y => Subtype.ext (map_add (ρ g) (x : K) (y : K)) }
  map_one' := by
    ext x
    simp
  map_mul' := by
    intro a b
    ext x
    exact rho_mul_apply ρ a b x

/- English proof (translation)
Introduce `δ hδ`. Rewrite using `[MonoidHom.mem_ker]`. Use extensionality with `x`. Conclude with `x.2 δ hδ`.
-/
lemma le_ker_restr [Δ.Normal] : Δ ≤ (restr ρ Δ).ker := by
  intro δ hδ
  rw [MonoidHom.mem_ker]
  ext x
  exact x.2 δ hδ

/- English proof (translation)
Set `L` to `fixSub ρ Δ`. Set `act : G ⧸ Δ →* RingAut L` to `QuotientGroup.lift Δ (restr ρ Δ) (le_ker_restr ρ Δ)`. Use `letI : MulSemiringAction (G ⧸ Δ) L := MulSemiringAction.compHom L act`. Establish `hsmul : ∀ (g : G) (x : L), (((QuotientGroup.mk g : G ⧸ Δ) • x : L) : K) = ρ g x` using `fun g x => rfl`. Set `F` to `FixedPoints.subfield (G ⧸ Δ) L`.

Set `Y' : Set L` to `{y | (y : K) ∈ Y}`. Set `E : IntermediateField F L` to `IntermediateField.adjoin F Y'`. Establish `hfE : (⟨f, hf⟩ : L) ∈ E`. Rewrite using `[← IsGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]`. Introduce `σ hσ`.

Rewrite `hσ` using `[IntermediateField.mem_fixingSubgroup_iff]`. Take `⟨q, rfl⟩` from `FixedPoints.toAlgAut_surjective (G ⧸ Δ) L σ`. Proceed by induction on `q using QuotientGroup.induction_on with`. Consider the case `H g`. Express the relevant statement in the definitionally equal form `(QuotientGroup.mk g : G ⧸ Δ) • (⟨f, hf⟩ : L) = ⟨f, hf⟩`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hsmul]`. Apply `hfix g` to reduce the goal to its premises. Introduce `y hy`. Establish `h1` using `hσ ⟨y, hY y hy⟩ (IntermediateField.subset_adjoin F Y' hy)`.

Establish `h2` using `congrArg Subtype.val h1`. Conclude with `(hsmul g ⟨y, hY y hy⟩).symm.trans h2`. Establish `hle : E.toSubfield ≤ (Subfield.closure ({x | ∀ g : G, ρ g x = x} ∪ Y)).comap L.subtype`. Rewrite using `[IntermediateField.adjoin_toSubfield, Subfield.closure_le]`. Introduce and unpack `x (⟨c, rfl⟩ | hx)`.

Apply `Subfield.subset_closure left` to reduce the goal to its premises. Introduce `g`. Establish `h1` using `c.2 (QuotientGroup.mk g : G ⧸ Δ)`. Conclude with `(hsmul g _).symm.trans (congrArg Subtype.val h1)`. Conclude with `Subfield.subset_closure (Or.inr hx)`.

Conclude with `hle (show (⟨f, hf⟩ : L) ∈ E.toSubfield from hfE)`.
-/
theorem mem_closure_of_fixed (K G : Type) [Field K] [Group G] (ρ : G →* RingAut K)
    (Δ : Subgroup G) (hN : Δ.Normal) (hfi : Δ.FiniteIndex) (Y : Set K) (f : K)
    (hY : ∀ y ∈ Y, ∀ δ ∈ Δ, ρ δ y = y) (hf : ∀ δ ∈ Δ, ρ δ f = f)
    (hfix : ∀ g : G, (∀ y ∈ Y, ρ g y = y) → ρ g f = f) :
    f ∈ Subfield.closure ({x | ∀ g : G, ρ g x = x} ∪ Y) := by
  let L := fixSub ρ Δ
  let act : G ⧸ Δ →* RingAut L := QuotientGroup.lift Δ (restr ρ Δ) (le_ker_restr ρ Δ)
  letI : MulSemiringAction (G ⧸ Δ) L := MulSemiringAction.compHom L act
  have hsmul : ∀ (g : G) (x : L), (((QuotientGroup.mk g : G ⧸ Δ) • x : L) : K) = ρ g x :=
    fun g x => rfl
  let F := FixedPoints.subfield (G ⧸ Δ) L
  let Y' : Set L := {y | (y : K) ∈ Y}
  let E : IntermediateField F L := IntermediateField.adjoin F Y'
  have hfE : (⟨f, hf⟩ : L) ∈ E := by
    rw [← IsGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
    obtain ⟨q, rfl⟩ := FixedPoints.toAlgAut_surjective (G ⧸ Δ) L σ
    induction q using QuotientGroup.induction_on with
    | H g =>
      change (QuotientGroup.mk g : G ⧸ Δ) • (⟨f, hf⟩ : L) = ⟨f, hf⟩
      apply Subtype.ext
      rw [hsmul]
      apply hfix g
      intro y hy
      have h1 := hσ ⟨y, hY y hy⟩ (IntermediateField.subset_adjoin F Y' hy)
      have h2 := congrArg Subtype.val h1
      exact (hsmul g ⟨y, hY y hy⟩).symm.trans h2
  have hle : E.toSubfield ≤ (Subfield.closure ({x | ∀ g : G, ρ g x = x} ∪ Y)).comap L.subtype := by
    rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro x (⟨c, rfl⟩ | hx)
    · apply Subfield.subset_closure
      left
      intro g
      have h1 := c.2 (QuotientGroup.mk g : G ⧸ Δ)
      exact (hsmul g _).symm.trans (congrArg Subtype.val h1)
    · exact Subfield.subset_closure (Or.inr hx)
  exact hle (show (⟨f, hf⟩ : L) ∈ E.toSubfield from hfE)

end GlobalTheory.ArtinFix
