import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.DualProjApply
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField
open scoped ComplexOrder

noncomputable section

namespace DualGeometricDegreePositive

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]

def stdLattice (F : HermLattice K i) : HermLattice K i where
  lattice := F.lattice
  fg := F.fg
  span_eq := F.span_eq
  metric := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one
  conj := fun _ => by simp

def oneLine : HermLine (dualBlocks T) :=
  HermLine.ofWeight (fun _ => (1 : ℝ)) (fun _ _ _ => rfl)

omit [Fintype T] [DecidableEq T] in
/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem logNorm_oneLine : logNorm (oneLine (T := T)) 1 = fun _ => (1 : ℝ) := by
  funext z
  simp [logNorm, oneLine, HermLine.ofWeight]

omit [Fintype T] [DecidableEq T] in
/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem segre_apply (z : (Σ _ : Unit, T) → ℂ) (s : (k : Unit) → dualBlocks T k) :
    segre (ι := dualBlocks T) z s = z ⟨(), s ()⟩ := by
  simp [segre]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Substitute using the available equality. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem isGoodProj (hOn : DualPtsOnPlane.Statement) {D : ℕ} {F : HermLattice K (D + 1)}
    (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) :
    IsGoodProj (dualIdeal b) (dualProj b hb) := by
  intro z hz h0
  obtain ⟨σ, hσ⟩ := hOn K (D + 1) F T b hb z hz
  have hne : dualRecover b hb (fun t => z ⟨(), t⟩) ≠ 0 := by
    intro h
    obtain ⟨t, ht⟩ := hz.1 ()
    exact ht (congrFun ((dualRecover b hb).map_eq_zero_iff.mp h) t)
  obtain ⟨⟨τ, j⟩, hτ⟩ := Function.ne_iff.mp hne
  have hτσ : τ = σ := by
    by_contra h
    exact hτ (hσ τ h j)
  subst hτσ
  have h1 := congrFun h0 j
  rw [dualProj_apply] at h1
  simp only [segre_apply] at h1
  rw [Finset.sum_eq_single τ (fun τ' _ h => hσ τ' h j) (fun h => absurd (Finset.mem_univ τ) h)] at h1
  exact hτ h1

end DualGeometricDegreePositive

open DualGeometricDegreePositive in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem DualGeomDegPos.proof (hDeg : DegreeStatement) (hInd : PtsIndepStatement)
    (hArith : DualArithVar.Statement) (hSemi : DualLineSemipositive.Statement)
    (hOn : DualPtsOnPlane.Statement) (hMass : DualStdMassAt.Statement) :
    DualGeomDegPos.Statement := by
  intro K _ _ i F T _ _ b hb hi
  obtain ⟨D, rfl⟩ : ∃ D, i = D + 1 := ⟨i - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hV : IsArithVar (dualIdeal b) (D + 1) := hArith K (D + 1) F T b hi
  have hS1 : IsSmoothHerm (dualLine (stdLattice F) b hb) := (hSemi K (D + 1) (stdLattice F) T b hb).1
  have e0 := hDeg Unit (dualBlocks T) (dualIdeal b) D (fun _ => dualLine F b hb) 2 hV
    (fun _ => (hSemi K (D + 1) F T b hb).1) Nat.prime_two
  have e1 := hDeg Unit (dualBlocks T) (dualIdeal b) D (fun _ => dualLine (stdLattice F) b hb) 2 hV
    (fun _ => hS1) Nat.prime_two
  have hswap : geomDeg (dualIdeal b) (dualLine F b hb) D =
      geomDeg (dualIdeal b) (dualLine (stdLattice F) b hb) D := by
    change ptsIntegral (dualIdeal b) (pot fun _ => dualLine F b hb) (fun _ => 1) =
      ptsIntegral (dualIdeal b) (pot fun _ => dualLine (stdLattice F) b hb) (fun _ => 1)
    rw [e0, e1]
    rfl
  have hgood := isGoodProj hOn b hb
  have hΨ : ∃ Ψ : (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ),
      IsGoodProj (dualIdeal b) Ψ := ⟨_, hgood⟩
  have hsec : IsSectionOn (dualIdeal b) (oneLine (T := T)) 1 := by
    refine ⟨fun _ => 0, fun _ => rfl, ?_, ?_⟩
    · intro d hd k
      rw [support_one] at hd
      simp only [Finset.mem_singleton] at hd
      simp [hd]
    · exact (Ideal.ne_top_iff_one _).1 hV.2.1.1.ne_top
  have h := hInd Unit (dualBlocks T) (dualIdeal b) D hΨ.choose (dualProj b hb)
    (fun _ => dualLine (stdLattice F) b hb) oneLine 1 hV hΨ.choose_spec hgood (fun _ => hS1)
    contDiffOn_const hsec
  rw [logNorm_oneLine] at h
  have hm := hMass K D (stdLattice F) T b hb fun _ => rfl
  have hval : geomDeg (dualIdeal b) (dualLine (stdLattice F) b hb) D = Fintype.card (K →+* ℂ) := by
    unfold geomDeg ptsIntegral
    rw [dif_pos hΨ]
    exact h.trans hm
  rw [hswap, hval]
  exact_mod_cast Fintype.card_pos

end

end GroundTheory.Heights₂.Heights
