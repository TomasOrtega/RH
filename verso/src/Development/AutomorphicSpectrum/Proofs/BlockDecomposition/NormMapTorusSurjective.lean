import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
import GroundTheory.LocalFields.Uniqueness

open PositivityTheory.Rg.Tf.Loc GroundTheory.LocalField Topology
open Matrix

namespace GlobalTheory.CompanionTheory.LocTop

section Field

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Use `letI N : NontriviallyNormedField F := nontriviallyNormedField F`. Establish `hw : @WeaklyLocallyCompactSpace F N.toUniformSpace.toTopologicalSpace` using `(inferInstance : WeaklyLocallyCompactSpace F)`. Use `haveI : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F`. Establish `h : @SecondCountableTopology F N.toUniformSpace.toTopologicalSpace` using `inferInstance`. Conclude with `h`.
-/
theorem secondCountable_field : SecondCountableTopology F := by
  letI N : NontriviallyNormedField F := nontriviallyNormedField F
  have hw : @WeaklyLocallyCompactSpace F N.toUniformSpace.toTopologicalSpace :=
    (inferInstance : WeaklyLocallyCompactSpace F)
  haveI : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have h : @SecondCountableTopology F N.toUniformSpace.toTopologicalSpace := inferInstance
  exact h

variable (n : ℕ)

def intMat : Set (Matrix (Fin n) (Fin n) F) := {X | ∀ i j, X i j ∈ intO F}

/- English proof (translation)
Establish `hO : IsCompact ((intO F : Subring F) : Set F)` using `IsNonarchimedeanLocalField.isCompact_closedBall F 1`. Establish `hrow : IsCompact (Set.pi Set.univ fun _ : Fin n => ((intO F : Subring F) : Set F))` using `isCompact_univ_pi fun _ => hO`. Establish `hmat : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => ((intO F : Subring F) : Set F))` using `isCompact_univ_pi fun _ => hrow`. Establish `hset : intMat F n = Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => ((intO F : Subring F) : Set F)`. Use extensionality with `X`.

Conclude with `⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩`. Rewrite using `[hset]`. Conclude with `hmat`.
-/
theorem isCompact_intMat : IsCompact (intMat F n) := by
  have hO : IsCompact ((intO F : Subring F) : Set F) :=
    IsNonarchimedeanLocalField.isCompact_closedBall F 1
  have hrow : IsCompact (Set.pi Set.univ fun _ : Fin n => ((intO F : Subring F) : Set F)) :=
    isCompact_univ_pi fun _ => hO
  have hmat : IsCompact (Set.pi Set.univ fun _ : Fin n =>
      Set.pi Set.univ fun _ : Fin n => ((intO F : Subring F) : Set F)) :=
    isCompact_univ_pi fun _ => hrow
  have hset : intMat F n = Set.pi Set.univ fun _ : Fin n =>
      Set.pi Set.univ fun _ : Fin n => ((intO F : Subring F) : Set F) := by
    ext X
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
  rw [hset]
  exact hmat

/- English proof (translation)
Establish `hO : IsOpen ((intO F : Subring F) : Set F)` using `Valuation.isOpen_integer (v := ValuativeRel.valuation F)`. Establish `hset : intMat F n = ⋂ i : Fin n, ⋂ j : Fin n, (fun X : Matrix (Fin n) (Fin n) F => X i j) ⁻¹' ((intO F : Subring F) : Set F)`. Use extensionality with `X`. Simplify using `[intMat]`. Rewrite using `[hset]`.

Use `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hO.preimage ?_` and prove the remaining obligations. Conclude with `(continuous_apply j).comp (continuous_apply i)`.
-/
theorem isOpen_intMat : IsOpen (intMat F n) := by
  have hO : IsOpen ((intO F : Subring F) : Set F) :=
    Valuation.isOpen_integer (v := ValuativeRel.valuation F)
  have hset : intMat F n =
      ⋂ i : Fin n, ⋂ j : Fin n, (fun X : Matrix (Fin n) (Fin n) F => X i j) ⁻¹'
        ((intO F : Subring F) : Set F) := by
    ext X
    simp [intMat]
  rw [hset]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hO.preimage ?_
  exact (continuous_apply j).comp (continuous_apply i)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, rfl⟩`. Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Conclude with `((h : Matrix (Fin n) (Fin n) (intO F)) i j).2`. Rewrite using `[← map_inv]`.

Conclude with `(((h⁻¹ : GL (Fin n) (intO F)) : Matrix (Fin n) (Fin n) (intO F)) i j).2`. Introduce and unpack `⟨h1, h2⟩`. Set `A : Matrix (Fin n) (Fin n) (intO F)` to `fun i j => ⟨(g : Matrix (Fin n) (Fin n) F) i j, h1 i j⟩`. Set `B : Matrix (Fin n) (Fin n) (intO F)` to `fun i j => ⟨((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j, h2 i j⟩`. Establish `hA : A.map (intO F).subtype = (g : Matrix (Fin n) (Fin n) F)` using `by ext i j; rfl`.

Establish `hB : B.map (intO F).subtype = ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)`. Use extensionality with `i j`. Both sides reduce to the same expression. Establish `hinj : Function.Injective (fun X : Matrix (Fin n) (Fin n) (intO F) => X.map (intO F).subtype)` using `Matrix.map_injective Subtype.val_injective`. Establish `hAB : A * B = 1` using `hinj (by`.

Simplify using `only`. Rewrite using `[Matrix.map_mul, hA, hB, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])`. Establish `hBA : B * A = 1` using `hinj (by`. Simplify using `only`. Rewrite using `[Matrix.map_mul, hA, hB, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])`.

Use `⟨⟨A, B, hAB, hBA⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Both sides reduce to the same expression.
-/
theorem mem_unitGL_iff (g : GL (Fin n) F) :
    g ∈ unitGL (n := Fin n) F ↔
      (g : Matrix (Fin n) (Fin n) F) ∈ intMat F n ∧
        ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ∈ intMat F n := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact ((h : Matrix (Fin n) (Fin n) (intO F)) i j).2
    · rw [← map_inv]
      exact (((h⁻¹ : GL (Fin n) (intO F)) : Matrix (Fin n) (Fin n) (intO F)) i j).2
  · rintro ⟨h1, h2⟩
    let A : Matrix (Fin n) (Fin n) (intO F) := fun i j => ⟨(g : Matrix (Fin n) (Fin n) F) i j, h1 i j⟩
    let B : Matrix (Fin n) (Fin n) (intO F) :=
      fun i j => ⟨((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j, h2 i j⟩
    have hA : A.map (intO F).subtype = (g : Matrix (Fin n) (Fin n) F) := by ext i j; rfl
    have hB : B.map (intO F).subtype = ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      ext i j; rfl
    have hinj : Function.Injective
        (fun X : Matrix (Fin n) (Fin n) (intO F) => X.map (intO F).subtype) :=
      Matrix.map_injective Subtype.val_injective
    have hAB : A * B = 1 := hinj (by
      simp only
      rw [Matrix.map_mul, hA, hB, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
    have hBA : B * A = 1 := hinj (by
      simp only
      rw [Matrix.map_mul, hA, hB, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])
    refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
    ext i j
    rfl

variable [T2Space F]

/- English proof (translation)
Use extensionality with `g`. Conclude with `mem_unitGL_iff F n g`.
-/
theorem unitGL_eq_preimage :
    (unitGL (n := Fin n) F : Set (GL (Fin n) F)) =
      Units.embedProduct (Matrix (Fin n) (Fin n) F) ⁻¹'
        (intMat F n ×ˢ (MulOpposite.unop ⁻¹' intMat F n)) := by
  ext g
  exact mem_unitGL_iff F n g

/- English proof (translation)
Rewrite using `[unitGL_eq_preimage]`. Conclude with `((isOpen_intMat F n).prod ((isOpen_intMat F n).preimage MulOpposite.continuous_unop)).preimage Units.continuous_embedProduct`.
-/
theorem isOpen_unitGL : IsOpen (unitGL (n := Fin n) F : Set (GL (Fin n) F)) := by
  rw [unitGL_eq_preimage]
  exact ((isOpen_intMat F n).prod ((isOpen_intMat F n).preimage MulOpposite.continuous_unop)).preimage
    Units.continuous_embedProduct

/- English proof (translation)
Rewrite using `[unitGL_eq_preimage]`. Use `(Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) F)).isCompact_preimage ((isCompact_intMat F n).prod ?_)` and prove the remaining obligations. Conclude with `(MulOpposite.opHomeomorph.symm.isCompact_preimage).2 (isCompact_intMat F n)`.
-/
theorem isCompact_unitGL : IsCompact (unitGL (n := Fin n) F : Set (GL (Fin n) F)) := by
  rw [unitGL_eq_preimage]
  refine (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) F)).isCompact_preimage
    ((isCompact_intMat F n).prod ?_)
  exact (MulOpposite.opHomeomorph.symm.isCompact_preimage).2 (isCompact_intMat F n)

/- English proof (translation)
Use `haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) F) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → F))`. Use `haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) F)ᵐᵒᵖ := MulOpposite.opHomeomorph.isClosedEmbedding.locallyCompactSpace`. Conclude with `(Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) F)).locallyCompactSpace`.
-/
theorem locallyCompact_GL : LocallyCompactSpace (GL (Fin n) F) := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → F))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.isClosedEmbedding.locallyCompactSpace
  exact (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) F)).locallyCompactSpace

/- English proof (translation)
Use `haveI := secondCountable_field F`. Use `haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) F) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → F))`. Use `haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) F)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology`. Conclude with `(Units.isEmbedding_embedProduct (M := Matrix (Fin n) (Fin n) F)).secondCountableTopology`.
-/
theorem secondCountable_GL : SecondCountableTopology (GL (Fin n) F) := by
  haveI := secondCountable_field F
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → F))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact (Units.isEmbedding_embedProduct (M := Matrix (Fin n) (Fin n) F)).secondCountableTopology

end Field

section Twisted

variable {k E : Type} [Field k] [Field E] [TopologicalSpace E] [IsTopologicalRing E] [T2Space E]
  [Algebra k E]

/- English proof (translation)
Rewrite using `[Units.continuous_iff]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `Units.continuous_val.matrix_map hσ`. Establish `: (fun g : GL (Fin n) E => (((sigmaGL σ g : GL (Fin n) E)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) = fun g : GL (Fin n) E => ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map σ`. Use function extensionality and compare the values at `g`.

Rewrite using `[← map_inv]`. Both sides reduce to the same expression. Use `show Continuous (fun g : GL (Fin n) E => (((sigmaGL σ g : GL (Fin n) E)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E))`. Rewrite using `[this]`. Conclude with `(Units.continuous_val.comp continuous_inv).matrix_map hσ`.
-/
theorem continuous_sigmaGL (σ : E ≃ₐ[k] E) (hσ : Continuous σ) (n : ℕ) :
    Continuous (sigmaGL σ : Monoid.End (GL (Fin n) E)) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_map hσ
  · have : (fun g : GL (Fin n) E => (((sigmaGL σ g : GL (Fin n) E)⁻¹ : GL (Fin n) E) :
        Matrix (Fin n) (Fin n) E)) =
        fun g : GL (Fin n) E => ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map σ := by
      funext g
      rw [← map_inv]
      rfl
    show Continuous (fun g : GL (Fin n) E => (((sigmaGL σ g : GL (Fin n) E)⁻¹ : GL (Fin n) E) :
        Matrix (Fin n) (Fin n) E))
    rw [this]
    exact (Units.continuous_val.comp continuous_inv).matrix_map hσ

/- English proof (translation)
Use `haveI : T2Space (GL (Fin n) E) := (Units.isEmbedding_embedProduct (M := Matrix (Fin n) (Fin n) E)).t2Space`. Establish `hθ` using `continuous_sigmaGL σ hσ n`. Establish `: (twCent (sigmaGL σ) δ : Set (GL (Fin n) E)) = {g | g⁻¹ * δ * sigmaGL σ g = δ}` using `rfl`. Rewrite using `[this]`. Conclude with `isClosed_eq ((continuous_inv.mul continuous_const).mul hθ) continuous_const`.
-/
theorem isClosed_twCent (σ : E ≃ₐ[k] E) (hσ : Continuous σ) (n : ℕ) (δ : GL (Fin n) E) :
    IsClosed (twCent (sigmaGL σ) δ : Set (GL (Fin n) E)) := by
  haveI : T2Space (GL (Fin n) E) :=
    (Units.isEmbedding_embedProduct (M := Matrix (Fin n) (Fin n) E)).t2Space
  have hθ := continuous_sigmaGL σ hσ n
  have : (twCent (sigmaGL σ) δ : Set (GL (Fin n) E)) = {g | g⁻¹ * δ * sigmaGL σ g = δ} := rfl
  rw [this]
  exact isClosed_eq ((continuous_inv.mul continuous_const).mul hθ) continuous_const

end Twisted

/- English proof (translation)
Use `⟨fun F _ _ _ _ n => ?_, ?_⟩` and prove the remaining obligations. Use `haveI : T2Space F := t2Space_of_isNonarchimedeanLocalField F`. Conclude with `⟨locallyCompact_GL F n, secondCountable_GL F n, isOpen_unitGL F n, isCompact_unitGL F n⟩`. Introduce `k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ _ n δ haveI : T2Space E := t2Space_of_isNonarchimedeanLocalField E`. Conclude with `isClosed_twCent σ (continuous_algHom σ.toAlgHom) n δ`.
-/
theorem t0 : T0 := by
  refine ⟨fun F _ _ _ _ n => ?_, ?_⟩
  · haveI : T2Space F := t2Space_of_isNonarchimedeanLocalField F
    exact ⟨locallyCompact_GL F n, secondCountable_GL F n, isOpen_unitGL F n, isCompact_unitGL F n⟩
  · intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ _ n δ
    haveI : T2Space E := t2Space_of_isNonarchimedeanLocalField E
    exact isClosed_twCent σ (continuous_algHom σ.toAlgHom) n δ

end GlobalTheory.CompanionTheory.LocTop
