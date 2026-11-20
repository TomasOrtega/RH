import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainFibFinite
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.JetGlue

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory.IwLevel.KerDet

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem isClosed_pt {k : Type} [Field k] {X : Scheme.{0}} (s : X ⟶ Sp k) [IsFinite s] (x : X) :
    IsClosed ({x} : Set X) := by
  rw [← closure_subset_iff_isClosed]
  intro w hw
  have h : x ⤳ w := specializes_iff_mem_closure.mpr hw
  have e : s w = s x := Subsingleton.elim (α := Spec (CommRingCat.of k)) _ _
  have hd := (s.isDiscrete_preimage_singleton (s x)).to_subtype
  have hs : (⟨x, rfl⟩ : s ⁻¹' {s x}) ⤳ ⟨w, e⟩ := Topology.IsInducing.subtypeVal.specializes_iff.mp h
  exact congrArg Subtype.val hs.eq.symm

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities.
-/
theorem exists_section {k L : Type} [Field k] [IsAlgClosed k] [Field L] {X : Scheme.{0}} (s : X ⟶ Sp k)
    [IsFinite s] (u : Sp L ⟶ X) : ∃ a : Sp k ⟶ X, a ≫ s = 𝟙 _ ∧ u = (u ≫ s) ≫ a := by
  obtain ⟨⟨x, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField L X).symm.surjective u
  have hx := isClosed_pt s x
  refine ⟨pointOfClosedPoint s x hx, pointOfClosedPoint_comp s x hx, ?_⟩
  change Spec.map φ ≫ X.fromSpecResidueField x =
    ((Spec.map φ ≫ X.fromSpecResidueField x) ≫ s) ≫ Spec.map (residueFieldIsoBase s x hx).hom ≫
      X.fromSpecResidueField x
  simp only [Category.assoc]
  rw [← SpecMap_residueFieldIsoBase_inv_assoc s x hx, ← Spec.map_comp_assoc (residueFieldIsoBase s x hx).hom,
    Iso.hom_inv_id, Spec.map_id, Category.id_comp]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Substitute using the available equality.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem exists_stalk_factor {X : Scheme.{0}} {R : CommRingCat.{0}} [IsLocalRing R] (f : Spec R ⟶ X) (x : X)
    (hx : f (IsLocalRing.closedPoint R) = x) : ∃ ψ : X.presheaf.stalk x ⟶ R, f = Spec.map ψ ≫ X.fromSpecStalk x := by
  obtain ⟨⟨y, φ, hφ⟩, rfl⟩ := (SpecToEquivOfLocalRing X R).symm.surjective f
  have hy : y = x := by
    rw [← hx]
    change y = (Spec.map φ ≫ X.fromSpecStalk y) _
    exact ((Scheme.Hom.comp_apply _ _ _).trans
      ((congrArg (X.fromSpecStalk y) Spec_closedPoint).trans Scheme.fromSpecStalk_closedPoint)).symm
  subst hy
  exact ⟨φ, rfl⟩

variable {k : Type} [Field k]

def InK {A B : Over (Sp k)} [GrpObj B] (π : A ⟶ B) {T : Scheme.{0}} (y : T ⟶ A.left) : Prop :=
  ∃ z : T ⟶ Sp k, z ≫ (η[B]).left = y ≫ π.left

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem inK_iff {A B : Over (Sp k)} [GrpObj B] (π : A ⟶ B) {T : Scheme.{0}} (y : T ⟶ A.left) :
    InK π y ↔ y ≫ π.left = (y ≫ A.hom) ≫ (η[B]).left := by
  have hη : (η[B]).left ≫ B.hom = 𝟙 _ := by simpa using Over.w (η[B])
  refine ⟨fun ⟨z, hz⟩ => ?_, fun h => ⟨_, h.symm⟩⟩
  have e : z = y ≫ A.hom := by
    have := congrArg (· ≫ B.hom) hz
    simp only [Category.assoc, hη, Category.comp_id, Over.w π] at this
    exact this
  rw [← hz, e]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem comp_eq_one_iff {A B : Over (Sp k)} [GrpObj B] (π : A ⟶ B) {T : Over (Sp k)} (Y : T ⟶ A) :
    Y ≫ π = 1 ↔ InK π Y.left := by
  have hT : (toUnit T).left = T.hom := by simpa using Over.w (toUnit T)
  rw [inK_iff, Over.w Y, ← hT]
  constructor
  · intro h; exact congrArg (fun q => q.left) h
  · intro h; exact Over.OverMorphism.ext h

end GlobalTheory.IwLevel.KerDet

namespace GlobalTheory.IwLevel.KerDet

variable {k : Type} [Field k]

/- English proof (translation)
Simplify to obtain the desired conclusion from the available facts.
-/
theorem toUnit_left (T : Over (Sp k)) : (toUnit T).left = T.hom := by simpa using Over.w (toUnit T)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem one_left {A T : Over (Sp k)} [GrpObj A] : (1 : T ⟶ A).left = T.hom ≫ (η[A]).left := by
  rw [← toUnit_left]; rfl

variable [IsAlgClosed k]

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Extract witnesses or component facts from the available result.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Introduce a local definition for the expression. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem local_step {A B B' : Over (Sp k)} [GrpObj A] [GrpObj B] [GrpObj B'] (π : A ⟶ B) (π' : A ⟶ B')
    [IsMonHom π] [IsMonHom π'] [IsFinite π.left]
    (h1 : ∀ a : 𝟙_ (Over (Sp k)) ⟶ A, a ≫ π = 1 → a ≫ π' = 1)
    (x₀ : A.left) (hx₀ : x₀ ∈ Set.range (η[A]).left.base)
    (h2 : ∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'),
      InK π (Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) →
      InK π' (Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀))
    {R : CommRingCat.{0}} [IsLocalRing R] (y : Spec R ⟶ A.left) (hy : InK π y) : InK π' y := by
  let c : Sp (IsLocalRing.ResidueField R) ⟶ Spec R := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  haveI : IsLocalHom (CommRingCat.ofHom (IsLocalRing.residue R)).hom :=
    inferInstanceAs (IsLocalHom (IsLocalRing.residue R))
  have hc : c (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) = IsLocalRing.closedPoint R :=
    Spec_closedPoint
  obtain ⟨z, hz⟩ := hy
  let ũ : Sp (IsLocalRing.ResidueField R) ⟶ pullback π.left (η[B]).left :=
    pullback.lift (c ≫ y) (c ≫ z) (by rw [Category.assoc, Category.assoc, hz])
  obtain ⟨a', ha's, hu⟩ := exists_section (pullback.snd π.left (η[B]).left) ũ
  let a0 := a' ≫ pullback.fst π.left (η[B]).left
  have hη : (η[B]).left ≫ B.hom = 𝟙 _ := by simpa using Over.w (η[B])
  have ha0 : a0 ≫ A.hom = 𝟙 _ := by
    simp only [a0, Category.assoc]
    rw [← Over.w π, pullback.condition_assoc, hη, Category.comp_id, ha's]
  let a : 𝟙_ (Over (Sp k)) ⟶ A := Over.homMk a0 ha0
  have ha : a ≫ π = 1 := (comp_eq_one_iff π a).2 ⟨a' ≫ pullback.snd _ _, by
    simp only [a, a0, Over.homMk_left, Category.assoc, pullback.condition]⟩
  have ha' : a ≫ π' = 1 := h1 a ha
  have e1 : c ≫ y = (ũ ≫ pullback.snd _ _) ≫ a0 := by
    simp only [a0]; rw [← Category.assoc, ← hu]; exact (pullback.lift_fst _ _ _).symm
  have hu' : c ≫ y = ((c ≫ y) ≫ A.hom) ≫ a0 := by
    have e2 : (c ≫ y) ≫ A.hom = ũ ≫ pullback.snd _ _ := by
      rw [e1, Category.assoc, ha0]; exact Category.comp_id _
    rw [e2]; exact e1
  let T' : Over (Sp k) := Over.mk (y ≫ A.hom)
  let Y : T' ⟶ A := Over.homMk y rfl
  let Ta : T' ⟶ A := toUnit T' ≫ a
  let D : T' ⟶ A := Y / Ta
  have hYπ : Y ≫ π = 1 := (comp_eq_one_iff π Y).2 ⟨z, hz⟩
  have hDπ : D ≫ π = 1 := by
    simp only [D, Ta]
    rw [GrpObj.div_comp, hYπ, Category.assoc, ha, MonObj.comp_one, div_one]
  let C : Over.mk ((c ≫ y) ≫ A.hom) ⟶ T' := Over.homMk c (by simp [T'])
  have hCY : C ≫ Y = C ≫ Ta := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Ta, toUnit_left, Over.homMk_left, C, Y, T', Over.mk_hom]
    rw [← Category.assoc c, ← Category.assoc c]
    exact hu'
  have hCD : C ≫ D = 1 := by
    simp only [D]; rw [GrpObj.comp_div, hCY, div_self']
  have hD0 : c ≫ D.left = ((c ≫ y) ≫ A.hom) ≫ (η[A]).left := by
    have := congrArg (fun q => q.left) hCD
    simp only [Over.comp_left, one_left] at this
    exact this
  have hDx : D.left (IsLocalRing.closedPoint R) = x₀ := by
    obtain ⟨p, hp⟩ := hx₀
    rw [← hc]
    change (c ≫ D.left) _ = x₀
    rw [hD0, ← hp]
    change (η[A]).left (((c ≫ y) ≫ A.hom) _) = (η[A]).left p
    exact congrArg (η[A]).left (Subsingleton.elim (α := Spec (CommRingCat.of k)) _ _)
  obtain ⟨ψ, hψ⟩ := exists_stalk_factor D.left x₀ hDx
  have hDK : InK π D.left := (comp_eq_one_iff π D).1 hDπ
  have hDK' : InK π' D.left := by
    rw [hψ] at hDK ⊢
    exact h2 R ψ.hom hDK
  have hDπ' : D ≫ π' = 1 := (comp_eq_one_iff π' D).2 hDK'
  have hYπ' : Y ≫ π' = 1 := by
    rw [← div_mul_cancel Y Ta, MonObj.mul_comp, hDπ', Category.assoc, ha', MonObj.comp_one, _root_.one_mul]
  exact (comp_eq_one_iff π' Y).1 hYπ'

end GlobalTheory.IwLevel.KerDet

namespace GlobalTheory.IwLevel.KerDet

variable {k : Type} [Field k] [IsAlgClosed k]

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem inK_of_inK {A B B' : Over (Sp k)} [GrpObj A] [GrpObj B] [GrpObj B'] (π : A ⟶ B) (π' : A ⟶ B')
    [IsMonHom π] [IsMonHom π'] [IsFinite π.left]
    (h1 : ∀ a : 𝟙_ (Over (Sp k)) ⟶ A, a ≫ π = 1 → a ≫ π' = 1)
    (x₀ : A.left) (hx₀ : x₀ ∈ Set.range (η[A]).left.base)
    (h2 : ∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'),
      InK π (Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) →
      InK π' (Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀))
    {T : Scheme.{0}} (y : T ⟶ A.left) (hy : InK π y) : InK π' y := by
  rw [inK_iff] at hy ⊢
  refine ReciprocityTheory.ChartRestriction.G.TB.JGPf.ext_of_fromSpecStalk _ _ fun t => ?_
  have h := local_step π π' h1 x₀ hx₀ h2 (T.fromSpecStalk t ≫ y) ((inK_iff π _).2 (by
    simp only [Category.assoc]; rw [hy, Category.assoc]))
  rw [inK_iff] at h
  simpa only [Category.assoc] using h

end GlobalTheory.IwLevel.KerDet

namespace GlobalTheory.IwLevel

end GlobalTheory.IwLevel
