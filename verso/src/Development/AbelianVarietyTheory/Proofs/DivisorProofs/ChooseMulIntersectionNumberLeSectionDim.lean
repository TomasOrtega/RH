import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Formalism.HarderNarasimhan.StatementPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperplaneSectionVanishingShiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZeroDimSupportEulerCharStatement
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Proceed by induction.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem choose_mul_interNum_le_hdim : ∀ (k : Type) [Field k] [Infinite k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k Y) → ∀ (L : LB Y) (hL : L.IsLB) (N : ℕ) (b : Fin N → L.Sec), (∀ y : Y, ∃ i, y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (b i)) → ∀ (d : ℕ) (F : Y.Modules) [IsFiniteQC F], suppDim F ≤ d → ∀ (j₀ : ℤ), VanishFrom L F j₀ → ∀ m : ℕ, (m.choose d : ℤ) * GlobalTheory.interNum k F (fun _ : Fin d => L) ≤ GlobalTheory.hdim k (GlobalTheory.twistZ F L (j₀ + m)) 0 := by
  intro k _ _ Y _ hY L hL N b hb d
  have hNo : AlgebraicGeometry.IsNoetherian Y := isNoetherian_of_isProjOver hY
  have hb' : ⨆ i, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (b i) = ⊤ :=
    top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 (hb y)
  have hf := algebraMap_eq_strHom k Y
  induction d with
  | zero =>
    intro F _ hF j₀ _ m
    rw [interNum_of_isEmpty, GlobalTheory.T.zero_dim_support_euler_char k Y hY L hL F (by simpa using hF)]
    simp
  | succ d ih =>
    intro F _ hF j₀ hV m
    obtain ⟨c, hc⟩ := exists_sum_mono_cutHom (k := k) F hL b hb'
    set t : L.Sec := ∑ i, algebraMap k Γ(Y, ⊤) (c i) • b i
    obtain ⟨hV', hr⟩ := GlobalTheory.T.hyperplane_section_vanishing_shift k Y hY L hL F t j₀ hV
    have hI : GlobalTheory.interNum k F (fun _ : Fin (d + 1) => L) =
        GlobalTheory.interNum k (GlobalTheory.cut F hL t) (fun _ : Fin d => L) := by
      rw [← interNum_cons_eq_interNum_cut hL t (P := fun _ : Fin d => L) (fun _ => hL)
        (finiteCohTwists_of_isProjOver hf F hY)]
      congr 1
      funext i
      refine Fin.cases rfl (fun _ => rfl) i
    have ih' := ih (GlobalTheory.cut F hL t) (suppDim_cut_le F hL t hF) (j₀ + 1) hV'
    rw [hI]
    induction m with
    | zero => simp
    | succ m ihm =>
      have h1 := hr (j₀ + 1 + m) (by omega)
      have h2 := ih' m
      have e1 : j₀ + ((m + 1 : ℕ) : ℤ) = j₀ + 1 + m := by push_cast; ring
      have e2 : j₀ + 1 + (m : ℤ) - 1 = j₀ + m := by ring
      rw [e2] at h1
      rw [e1, h1, Nat.choose_succ_succ']
      push_cast
      linarith

end GlobalTheory.HSCore
