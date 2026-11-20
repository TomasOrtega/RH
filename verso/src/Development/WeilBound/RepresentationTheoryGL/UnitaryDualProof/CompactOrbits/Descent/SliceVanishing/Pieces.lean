import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.ExistsConjEqSemisimple
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.IsUnimodOfEquiv
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.SemisimpleAdjoint.IsSemisimpleOfMem

noncomputable section

open Matrix Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.T.Desc.SLF

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Substitute using the available equality. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem centralizer_le_of {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {s x : Matrix (Fin n) (Fin n) k}
    (hx : ∀ a ∈ Z, a * x = x * a) (hs : s * x = x * s) :
    adj Z s ≤ Subalgebra.centralizer k ({x} : Set (Matrix (Fin n) (Fin n) k)) := by
  apply Algebra.adjoin_le
  intro a ha
  rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  rcases Set.mem_insert_iff.mp ha with rfl | ha
  · exact hs.symm
  · exact (hx a ha).symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_Bz_adj {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {s x : Matrix (Fin n) (Fin n) k}
    (hx : x ∈ Bz Z) (hs : s * x = x * s) : x ∈ Bz (adj Z s) := by
  show ∀ a ∈ adj Z s, a * x = x * a
  intro a ha
  have h := centralizer_le_of hx hs ha
  rw [Subalgebra.mem_centralizer_iff] at h
  exact (h x (Set.mem_singleton x)).symm

/- English proof (translation)
Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_Gz_adj_iff {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {s : Matrix (Fin n) (Fin n) k} {g : GL (Fin n) k} :
    g ∈ Gz (adj Z s) ↔ g ∈ Gz Z ∧ s * g.val = g.val * s := by
  simp only [Gz, Set.mem_setOf_eq]
  constructor
  · intro h
    exact ⟨fun a ha => h a (Algebra.subset_adjoin (Set.mem_insert_of_mem _ ha)),
      h s (Algebra.subset_adjoin (Set.mem_insert _ _))⟩
  · rintro ⟨h1, h2⟩ a ha
    have h := centralizer_le_of (x := (g : Matrix (Fin n) (Fin n) k)) h1 h2 ha
    rw [Subalgebra.mem_centralizer_iff] at h
    exact (h _ (Set.mem_singleton _)).symm

def Xs (F : Set (Matrix (Fin n) (Fin n) k)) : Set (Sp k n) := F ×ˢ Set.univ

section Act

variable {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {F : Set (Matrix (Fin n) (Fin n) k)}
  (hFinv : ∀ g ∈ Gz Z, ∀ x ∈ F, g.val * x * g⁻¹.val ∈ F)

include hFinv in
/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem act_mem_Xs {g : GL (Fin n) k} (hg : g ∈ Gz Z) {q : Sp k n} (hq : q ∈ Xs F) : act g q ∈ Xs F := by
  refine Set.mem_prod.mpr ⟨?_, Set.mem_univ _⟩
  exact hFinv g hg q.1 (Set.mem_prod.mp hq).1

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem act_mul (g h : GL (Fin n) k) (q : Sp k n) : act (g * h) q = act g (act h q) := by
  simp only [act, Units.val_mul, _root_.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem act_one (q : Sp k n) : act (1 : GL (Fin n) k) q = q := by simp [act]

def actX : MulAction (GzS Z) (Xs F) where
  smul g q := ⟨act g.1 q.1, act_mem_Xs hFinv g.2 q.2⟩
  one_smul q := Subtype.ext (act_one q.1)
  mul_smul g h q := Subtype.ext (act_mul g.1 h.1 q.1)

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem continuous_act : Continuous fun p : GL (Fin n) k × Sp k n => act p.1 p.2 := by
  unfold act
  refine Continuous.prodMk ?_ ?_
  · exact ((Units.continuous_val.comp continuous_fst).matrix_mul
      (continuous_fst.comp continuous_snd)).matrix_mul
      (Units.continuous_coe_inv.comp continuous_fst)
  · exact (Units.continuous_val.comp continuous_fst).matrix_mulVec
      (continuous_snd.comp continuous_snd)

/- English proof (translation)
Equip the data with the indicated structure. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem continuousSMul_actX : @ContinuousSMul (GzS Z) (Xs F) (actX hFinv).toSMul _ _ := by
  letI := actX hFinv
  refine ⟨Continuous.subtype_mk ?_ _⟩
  exact continuous_act.comp ((continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd))

end Act

end PositivityTheory.RgUd.T.Desc.SLF
