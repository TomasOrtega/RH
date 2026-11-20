import Development.AutomorphicArithmetic.CommutativeAlgebra.MapZeroS
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexDifferentialValuesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchClsCocycleSecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAWExistsUniqueBiadditiveEtaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupEqClassOfIsAWStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Kun

namespace UpperTheory.Kun.InL

variable {R : Type} [CommRing R]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
private theorem sgn {A : Type*} [AddCommGroup A] (a b : ℤˣ) (x : A) : b • a • a • b • x = x := by
  rcases Int.units_eq_one_or a with rfl | rfl <;> rcases Int.units_eq_one_or b with rfl | rfl <;> simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem inL_coe {K I Q : Cx R} {m n : ℤ} (h : m + 1 = n) (α₁ : Cocycle K I n) (α₂ : Cocycle K Q m) :
    (inL h α₁ α₂).1 = α₁.1.comp (Cochain.ofHom (biprod.inl : I ⟶ LL I Q)) (add_zero n) +
      n.negOnePow • (α₂.1.rightShift (-1) n (by omega)).comp (Cochain.ofHom (biprod.inr : sh Q ⟶ LL I Q)) (add_zero n) := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private theorem inL_fst {K I Q : Cx R} {m n : ℤ} (h : m + 1 = n) (α₁ : Cocycle K I n) (α₂ : Cocycle K Q m) :
    (inL h α₁ α₂).1.comp (Cochain.ofHom (biprod.fst : LL I Q ⟶ I)) (add_zero n) = α₁.1 := by
  rw [inL_coe, Cochain.add_comp, Cochain.units_smul_comp, Cochain.comp_assoc_of_second_is_zero_cochain,
    Cochain.comp_assoc_of_second_is_zero_cochain, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp,
    biprod.inl_fst, biprod.inr_fst, Cochain.comp_id]
  simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private theorem inL_snd {K I Q : Cx R} {m n : ℤ} (h : m + 1 = n) (α₁ : Cocycle K I n) (α₂ : Cocycle K Q m) :
    (inL h α₁ α₂).1.comp (Cochain.ofHom (biprod.snd : LL I Q ⟶ sh Q)) (add_zero n) =
      n.negOnePow • α₂.1.rightShift (-1) n (by omega) := by
  rw [inL_coe, Cochain.add_comp, Cochain.units_smul_comp, Cochain.comp_assoc_of_second_is_zero_cochain,
    Cochain.comp_assoc_of_second_is_zero_cochain, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp,
    biprod.inl_snd, biprod.inr_snd, Cochain.comp_id]
  simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
private theorem decomp {K I Q : Cx R} {n : ℤ} (x : Cochain K (LL I Q) n) :
    (x.comp (Cochain.ofHom (biprod.fst : LL I Q ⟶ I)) (add_zero n)).comp (Cochain.ofHom (biprod.inl : I ⟶ LL I Q)) (add_zero n) +
      (x.comp (Cochain.ofHom (biprod.snd : LL I Q ⟶ sh Q)) (add_zero n)).comp (Cochain.ofHom (biprod.inr : sh Q ⟶ LL I Q)) (add_zero n) = x := by
  rw [Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.comp_assoc_of_second_is_zero_cochain,
    ← Cochain.ofHom_comp, ← Cochain.ofHom_comp, ← Cochain.comp_add, ← Cochain.ofHom_add, biprod.total, Cochain.comp_id]

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities.
-/
private theorem unsh {K Q : Cx R} {m n : ℤ} (h : m + 1 = n) (ε : ℤˣ) (y : Cocycle K (sh Q) n) :
    ∃ a : Cocycle K Q m, ε • a.1.rightShift (-1) n (by omega) = y.1 := by
  have hy : n + -1 = m := by omega
  refine ⟨Cocycle.mk (ε • y.1.rightUnshift m hy) (m + 1) rfl ?_, ?_⟩
  · rw [δ_units_smul, Cochain.δ_rightUnshift _ m hy (m + 1) (n + 1) (by omega), Cocycle.δ_eq_zero]
    simp
  · change ε • (ε • y.1.rightUnshift m hy).rightShift (-1) n hy = y.1
    rw [Cochain.rightShift_units_smul, Cochain.rightShift_rightUnshift, smul_smul, Int.units_mul_self, one_smul]

end UpperTheory.Kun.InL

open UpperTheory.Kun.InL in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.cohomologyClass_inL_surjective_and_injective :
    ∀ (R : Type) [CommRing R] {K I Q : Cx R} {m n : ℤ} (h : m + 1 = n),
        (∀ x : Cocycle K (LL I Q) n, ∃ (α₁ : Cocycle K I n) (α₂ : Cocycle K Q m), CohomologyClass.mk x = CohomologyClass.mk (inL h α₁ α₂)) ∧
        ∀ (α₁ : Cocycle K I n) (α₂ : Cocycle K Q m), CohomologyClass.mk (inL h α₁ α₂) = 0 → CohomologyClass.mk α₁ = 0 ∧ CohomologyClass.mk α₂ = 0 := by
  intro R _ K I Q m n h
  refine ⟨fun x => ?_, fun α₁ α₂ h0 => ?_⟩
  · obtain ⟨a, ha⟩ := unsh (K := K) (Q := Q) h n.negOnePow (zcomp x (Cocycle.ofHom (biprod.snd : LL I Q ⟶ sh Q)) (add_zero n))
    refine ⟨zcomp x (Cocycle.ofHom (biprod.fst : LL I Q ⟶ I)) (add_zero n), a, ?_⟩
    congr 1
    apply Cocycle.ext
    rw [inL_coe]
    have e : n.negOnePow • a.1.rightShift (-1) n (by omega) = x.1.comp (Cochain.ofHom (biprod.snd : LL I Q ⟶ sh Q)) (add_zero n) := ha
    rw [← Cochain.units_smul_comp, e]
    exact (decomp x.1).symm
  · obtain ⟨p, hp, y, hy⟩ := (CohomologyClass.mk_eq_zero_iff _).1 h0
    have hy' : δ p n y = (inL h α₁ α₂).1 := hy
    constructor
    · rw [CohomologyClass.mk_eq_zero_iff]
      refine ⟨p, hp, y.comp (Cochain.ofHom (biprod.fst : LL I Q ⟶ I)) (add_zero p), ?_⟩
      rw [δ_comp_ofHom, hy', inL_fst]
    · rw [CohomologyClass.mk_eq_zero_iff]
      have hs : δ p n (y.comp (Cochain.ofHom (biprod.snd : LL I Q ⟶ sh Q)) (add_zero p)) =
          n.negOnePow • α₂.1.rightShift (-1) n (by omega) := by
        rw [δ_comp_ofHom, hy', inL_snd]
      have hn : n + -1 = m := by omega
      have e : δ (p + -1) m ((y.comp (Cochain.ofHom (biprod.snd : LL I Q ⟶ sh Q)) (add_zero p)).rightUnshift (p + -1) rfl) =
          (-1 : ℤ).negOnePow • n.negOnePow • α₂.1 := by
        rw [Cochain.δ_rightUnshift _ (p + -1) rfl m n hn, hs, Cochain.rightUnshift_units_smul, Cochain.rightUnshift_rightShift]
      refine ⟨p + -1, by omega, n.negOnePow • (-1 : ℤ).negOnePow •
        (y.comp (Cochain.ofHom (biprod.snd : LL I Q ⟶ sh Q)) (add_zero p)).rightUnshift (p + -1) rfl, ?_⟩
      rw [δ_units_smul, δ_units_smul, e, sgn]
