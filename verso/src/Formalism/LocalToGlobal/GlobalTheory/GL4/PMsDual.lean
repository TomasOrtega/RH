import Formalism.LocalToGlobal.GlobalTheory.GL4.PMsCount

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions NumberField Formalism.MainNotions.flipTwoThree

section DualIndex

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem mulDual_eq_nsmul (S : HSpace E) (M : ℕ) (L : Submodule (𝓞 E) S.V) :
    mulDual S M L = (dualSub S L).map (nsmulAddMonoidHom (α := S.V) M) := by
  unfold mulDual
  congr 1
  ext v
  simp [Nat.cast_smul_eq_nsmul]

abbrev qModule (S : HSpace E) : Module ℚ S.V := Module.compHom S.V (algebraMap ℚ E)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem qsmul_def (S : HSpace E) (q : ℚ) (v : S.V) :
    letI := qModule S; q • v = (algebraMap ℚ E q) • v := rfl

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Establish an intermediate fact. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

Treat this case separately. Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem span_rat_eq_top (S : HSpace E) (L : Submodule (𝓞 E) S.V) [hL : Submodule.IsLattice E L] :
    letI := qModule S; Submodule.span ℚ (L : Set S.V) = ⊤ := by
  let _ := qModule S
  set W := Submodule.span ℚ (L : Set S.V) with hW
  have key : ∀ (e : E) (v : S.V), v ∈ W → e • v ∈ W := by
    intro e v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy0, hy⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) e)).exists_integral_multiple
      set a : 𝓞 E := ⟨y • e, hy⟩ with ha
      have hax : a • x ∈ L := L.smul_mem a hx
      have h1 : e • x = (((y : ℚ)⁻¹ : ℚ)) • (a • x) := by
        rw [qsmul_def, ← algebraMap_smul E a x, smul_smul]
        congr 1
        have hy' : (y : E) ≠ 0 := by exact_mod_cast hy0
        simp only [ha, zsmul_eq_mul, map_inv₀, map_intCast]
        field_simp
        rfl
      rw [h1]
      exact W.smul_mem _ (Submodule.subset_span hax)
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact W.add_mem hx hy
    | smul q x _ hx =>
      have : e • (q • x) = q • (e • x) := by
        rw [qsmul_def, qsmul_def, smul_smul, smul_smul, mul_comm]
      rw [this]; exact W.smul_mem q hx
  let W' : Submodule E S.V :=
    { carrier := W
      add_mem' := W.add_mem
      zero_mem' := W.zero_mem
      smul_mem' := fun e v hv => key e v hv }
  have hle : Submodule.span E (L : Set S.V) ≤ W' := Submodule.span_le.2 fun x hx => Submodule.subset_span hx
  rw [hL.span_eq_top] at hle
  exact eq_top_iff.2 fun v _ => (hle (Submodule.mem_top : v ∈ (⊤ : Submodule E S.V)))

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem relIndex_mulDual (S : HSpace E) (L : Submodule (𝓞 E) S.V) [hL : Submodule.IsLattice E L]
    (q : ℕ) (hq : LatT S q L) (hq0 : q ≠ 0) (M : ℕ) :
    (mulDual S M L).relIndex (dualSub S L) = M ^ (Module.finrank ℚ E * S.rank) := by
  let _ := qModule S
  have _tow : IsScalarTower ℚ E S.V := ⟨fun x y z => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  have _fin : Module.Finite ℚ S.V := Module.Finite.trans E S.V
  set A := dualSub S L with hA
  have hLA : L.restrictScalars ℤ ≤ A.toIntSubmodule := fun x hx => hq.1 x hx
  have hLfg : (L.restrictScalars ℤ).FG := hL.fg.restrictScalars
  have _hLl : Submodule.IsLattice ℚ (L.restrictScalars ℤ) :=
    ⟨hLfg, by
      have h := span_rat_eq_top S L
      simpa using h⟩

  let φ : S.V →ₗ[ℤ] S.V := (q : ℤ) • LinearMap.id
  have hφ : Function.Injective φ := by
    intro v w hvw
    have h1 : (q : ℤ) • (v - w) = 0 := by
      simp only [φ, LinearMap.smul_apply, LinearMap.id_apply] at hvw
      rw [smul_sub, hvw, sub_self]
    have h2 : ((q : E)) • (v - w) = 0 := by
      rw [← h1, ← Int.cast_smul_eq_zsmul E]; simp
    rcases smul_eq_zero.1 h2 with h | h
    · exact absurd h (by exact_mod_cast hq0)
    · exact sub_eq_zero.1 h
  have hmap : A.toIntSubmodule.map φ ≤ L.restrictScalars ℤ := by
    rintro _ ⟨a, ha, rfl⟩
    have h := AddSubgroup.nsmul_relIndex_mem L.toAddSubgroup (show a ∈ A from ha)
    rw [hq.2] at h
    simpa [φ, natCast_zsmul] using h
  have hAfg : A.toIntSubmodule.FG :=
    Submodule.fg_of_fg_map_injective φ hφ (Submodule.FG.of_le hLfg hmap)
  have _hAl : Submodule.IsLattice ℚ A.toIntSubmodule :=
    Submodule.IsLattice.of_le_of_isLattice_of_fg ℚ hLA hAfg
  have hrank : Module.finrank ℤ A.toIntSubmodule = Module.finrank ℚ E * S.rank := by
    apply Module.finrank_eq_of_rank_eq
    rw [Submodule.IsLattice.rank' ℚ A.toIntSubmodule, ← Module.finrank_eq_rank ℚ S.V,
      ← Module.finrank_mul_finrank ℚ E S.V, S.rank_eq]
  rw [mulDual_eq_nsmul, AddSubgroup.relIndex_map_nsmul]
  rw [← hrank]
  rfl

end DualIndex

section DualIdxRecord

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities.
-/
theorem dual_index (D : D7) : DualIdx D := by
  intro u M _
  refine ⟨fun i hi L hL hT => ?_, fun L hL hT => ?_⟩
  · rw [relIndex_mulDual (D.sp.X i) L _ hT (pow_ne_zero _ (D.mem u).A.T_prime.ne_zero) M,
      Formalism.MainNotions.flipTwoThree.b_finrank_host, D.sp.X_rank i hi]
  · have hN : D.R.N D.R.m - 1 = D.R.rankX' := by
      have := Formalism.BasicNotions.factXm D.R
      omega
    rw [relIndex_mulDual D.sp.X' L 1 hT one_ne_zero M, Formalism.MainNotions.flipTwoThree.b_finrank_host, D.sp.X'_rank, hN]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem msCount_of_isoCount (D : D7) (C₀ : ℝ) (hC : 1 ≤ C₀) (hI : IsoCount D C₀) : MsCount D C₀ :=
  msCount_of D C₀ hC hI (dual_index D)

end DualIdxRecord

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
