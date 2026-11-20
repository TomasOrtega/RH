import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutEtaB
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepBI
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PLocalLatticeIndex

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
open UpperTheory.TP.W

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
private theorem relIndex_map_of_injOn {G G' : Type} [AddGroup G] [AddGroup G'] (f : G →+ G') (R H K : AddSubgroup G)
    (hH : H ≤ R) (hK : K ≤ R) (hf : ∀ x ∈ R, f x = 0 → x = 0) :
    (H.map f).relIndex (K.map f) = H.relIndex K := by
  have hinj : Function.Injective (f.comp R.subtype) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact Subtype.ext (hf x x.2 hx)
  have h1 := AddSubgroup.relIndex_map_map_of_injective (H.addSubgroupOf R) (K.addSubgroupOf R) hinj
  have h2 := AddSubgroup.relIndex_map_map_of_injective (H.addSubgroupOf R) (K.addSubgroupOf R) R.subtype_injective
  rw [AddSubgroup.map_addSubgroupOf_eq_of_le hH, AddSubgroup.map_addSubgroupOf_eq_of_le hK] at h2
  rw [← AddSubgroup.map_map, ← AddSubgroup.map_map, AddSubgroup.map_addSubgroupOf_eq_of_le hH,
    AddSubgroup.map_addSubgroupOf_eq_of_le hK] at h1
  exact h1.trans h2.symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Introduce a local definition for the expression. Establish an intermediate fact. Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

By extensionality, compare the relevant components. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Establish an intermediate fact. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Prove the components needed by the constructor for the conclusion.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.lattice_determinant_comparison_at_split_place :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {nS nT : ℕ}
        (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (e : AEF F E), e * e = e →
        ∀ (P : HeightOneSpectrum (𝓞 E)), ev F E P e = 1 → (∀ a : AEF F E, e * a = a → ev F E P a = 0 → a = 0) →
        ∀ (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E))
          (L : Submodule (P.adicCompletionIntegers E) (Matrix (Fin nT) (Fin nS) (P.adicCompletion E))),
          (∀ v, v ∈ L ↔ ∃ x ∈ latF F E nS nT Λ, (x : WOF F E nS nT).map (ev F E P) = v) →
        ∀ (g : GAF σ JS) (h : GAF σ JT)
          (T : Matrix (Fin nT) (Fin nS) (P.adicCompletion E) →ₗ[P.adicCompletion E] Matrix (Fin nT) (Fin nS) (P.adicCompletion E)),
          (∀ u, T u = (mtF σ JT h).map (ev F E P) * u * (mtF σ JS g⁻¹).map (ev F E P)) →
          idx ((latF F E nS nT Λ).map (mulFF e)) (((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))).map (mulFF e)) =
            idx L (L.map (T.restrictScalars (P.adicCompletionIntegers E))) ∧
          idx (((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))).map (mulFF e)) ((latF F E nS nT Λ).map (mulFF e)) =
            idx (L.map (T.restrictScalars (P.adicCompletionIntegers E))) L := by
  intro F E _ _ _ _ _ σ nS nT JS JT e he P hev hinj Λ L hL g h T hT
  let φ : XFF F E nS nT →+ Matrix (Fin nT) (Fin nS) (P.adicCompletion E) :=
    AddMonoidHom.mk' (fun x => (x : WOF F E nS nT).map (ev F E P)) (fun x y => by
      rw [XFF.coe_add]
      ext i j
      simp [Matrix.map_apply, map_add])
  have hφ : ∀ x, φ x = (x : WOF F E nS nT).map (ev F E P) := fun _ => rfl
  have hφe : ∀ x, φ (mulFF e x) = φ x := by
    intro x
    rw [hφ, hφ, coe_mulFF]
    ext i j
    simp [Matrix.map_apply, Matrix.smul_apply, map_mul, hev]
  have hφr : ∀ x, φ (rhoFF σ JS JT (g, h) x) = T (φ x) := by
    intro x
    rw [hT, hφ, hφ, coe_rhoFF]
    show ((mtF σ JT h * (x : WOF F E nS nT)) * mtF σ JS g⁻¹).map (ev F E P) = _
    rw [Matrix.map_mul, Matrix.map_mul]
  let R : AddSubgroup (XFF F E nS nT) :=
    (LinearMap.range (mulFF e : XFF F E nS nT →ₗ[𝓞 E] XFF F E nS nT)).toAddSubgroup
  have hR : ∀ x ∈ R, φ x = 0 → x = 0 := by
    rintro _ ⟨y, rfl⟩ h0
    apply XFF.ext
    rw [XFF.coe_zero]
    ext i j
    apply hinj
    · rw [coe_mulFF]
      simp [Matrix.smul_apply, ← mul_assoc, he]
    · exact congrFun (congrFun h0 i) j
  have hmapA : ((latF F E nS nT Λ).map (mulFF e)).toAddSubgroup.map φ = L.toAddSubgroup := by
    ext v
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_map]
    rw [hL]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (hφe x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, hφe x⟩
  have hmapB : (((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))).map (mulFF e)).toAddSubgroup.map φ =
      (L.map (T.restrictScalars (P.adicCompletionIntegers E))).toAddSubgroup := by
    ext v
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_map]
    constructor
    · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
      refine ⟨φ x, (hL _).2 ⟨x, hx, rfl⟩, ?_⟩
      show T (φ x) = _
      rw [hφe, hφr]
    · rintro ⟨_, hu, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (hL _).1 hu
      refine ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
      exact (hφe _).trans (hφr x)
  have hleA : ((latF F E nS nT Λ).map (mulFF e)).toAddSubgroup ≤ R := by
    rintro _ ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  have hleB : (((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))).map (mulFF e)).toAddSubgroup ≤ R := by
    rintro _ ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  constructor
  · unfold idx
    rw [← hmapA, ← hmapB]
    exact (relIndex_map_of_injOn φ R _ _ hleA hleB hR).symm
  · unfold idx
    rw [← hmapA, ← hmapB]
    exact (relIndex_map_of_injOn φ R _ _ hleB hleA hR).symm
