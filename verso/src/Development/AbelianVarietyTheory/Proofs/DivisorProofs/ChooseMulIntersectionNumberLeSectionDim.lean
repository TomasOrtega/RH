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
Introduce `k _ _ Y _ hY L hL N b hb d`. Establish `hNo : AlgebraicGeometry.IsNoetherian Y` using `isNoetherian_of_isProjOver hY`. Establish `hb' : ⨆ i, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (b i) = ⊤` using `top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 (hb y)`. Establish `hf` using `algebraMap_eq_strHom k Y`. Proceed by induction on `d with`.

Consider the case `zero`. Introduce `F _ hF j₀ _ m`. Rewrite using `[interNum_of_isEmpty, GlobalTheory.T.zero_dim_support_euler_char k Y hY L hL F (by simpa using hF)]`. Simplify using the standard rewrite rules. Consider the case `succ d ih`.

Introduce `F _ hF j₀ hV m`. Take `⟨c, hc⟩` from `exists_sum_mono_cutHom (k := k) F hL b hb'`. Use `set t : L.Sec := ∑ i, algebraMap k Γ(Y, ⊤) (c i) • b i`. Take `⟨hV', hr⟩` from `GlobalTheory.T.hyperplane_section_vanishing_shift k Y hY L hL F t j₀ hV`. Establish `hI : GlobalTheory.interNum k F (fun _ : Fin (d + 1) => L) = GlobalTheory.interNum k (GlobalTheory.cut F hL t) (fun _ : Fin d => L)`.

Rewrite using `[← interNum_cons_eq_interNum_cut hL t (P := fun _ : Fin d => L) (fun _ => hL) (finiteCohTwists_of_isProjOver hf F hY)]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Use `Fin.cases rfl (fun _ => rfl) i` and prove the remaining obligations. Establish `ih'` using `ih (GlobalTheory.cut F hL t) (suppDim_cut_le F hL t hF) (j₀ + 1) hV'`.

Rewrite using `[hI]`. Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ihm`. Establish `h1` using `hr (j₀ + 1 + m) (by omega)`.

Establish `h2` using `ih' m`. Establish `e1 : j₀ + ((m + 1 : ℕ) : ℤ) = j₀ + 1 + m` using `by push_cast; ring`. Establish `e2 : j₀ + 1 + (m : ℤ) - 1 = j₀ + m` using `by ring`. Rewrite `h1` using `[e2]`. Rewrite using `[e1, h1, Nat.choose_succ_succ']`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
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
