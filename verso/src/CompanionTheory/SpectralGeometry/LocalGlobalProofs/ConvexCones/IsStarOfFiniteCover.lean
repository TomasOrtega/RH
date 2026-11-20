import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionCellsFiniteCoverUpToAut
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealConeCoveredByStarAtPointStatement
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarFiniteCover

/- English proof (translation)
Take `⟨c, hc, hβ⟩` from `h`. Use `choose j hj using fun i => hsub (Set.mem_range_self i)`. Use `⟨fun a => ∑ i ∈ Finset.univ.filter (fun i => j i = a), c i, fun a => Finset.sum_nonneg fun i _ => hc i, ?_⟩` and prove the remaining obligations. Rewrite using `[hβ]`. Use `symm`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_smul]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[(Finset.mem_filter.mp hi).2]`.

Use `_ = ∑ i, c i • GlobalTheory.PolFan.toReal (γ (j i)) := Finset.sum_fiberwise _ _ _`. Use `_ = ∑ i, c i • GlobalTheory.PolFan.toReal (γ' i) := by simp_rw [hj]`.
-/
private theorem inRCone_mono_of_range_subset {X : Type} [AddCommGroup X] {m n : ℕ}
    (γ : Fin m → LinearMap.BilinForm ℤ X) (γ' : Fin n → LinearMap.BilinForm ℤ X)
    (hsub : Set.range γ' ⊆ Set.range γ) {β : LinearMap.BilinForm ℤ X}
    (h : GlobalTheory.PolFan.InRCone γ' β) : GlobalTheory.PolFan.InRCone γ β := by
  classical
  obtain ⟨c, hc, hβ⟩ := h
  choose j hj using fun i => hsub (Set.mem_range_self i)
  refine ⟨fun a => ∑ i ∈ Finset.univ.filter (fun i => j i = a), c i,
    fun a => Finset.sum_nonneg fun i _ => hc i, ?_⟩
  rw [hβ]
  symm
  calc ∑ a, (∑ i ∈ Finset.univ.filter (fun i => j i = a), c i) • GlobalTheory.PolFan.toReal (γ a)
      = ∑ a, ∑ i ∈ Finset.univ.filter (fun i => j i = a), c i • GlobalTheory.PolFan.toReal (γ (j i)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [(Finset.mem_filter.mp hi).2]
    _ = ∑ i, c i • GlobalTheory.PolFan.toReal (γ (j i)) := Finset.sum_fiberwise _ _ _
    _ = ∑ i, c i • GlobalTheory.PolFan.toReal (γ' i) := by simp_rw [hj]

/- English proof (translation)
Introduce `O _ _ _ _ bar hO q ψ w ψ' hψ hC hStar X _ _ _ _ hq`. Take `⟨hS1, hS2, -⟩` from `hStar`. Take `⟨S0, hS0, hcov⟩` from `(hψ X hq).finite`. Take `⟨ch, hch⟩ : ∃ ch : Set (LinearMap.BilinForm ℤ X) → LinearMap.BilinForm ℤ X, ∀ T : Set (LinearMap.BilinForm ℤ X), (∃ β, β ∈ GlobalTheory.PolFan.balForms bar X ∧ (∀ y, 0 ≤ β y y) ∧ w.evalZ β = 1 ∧ ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), GlobalTheory.PolFan.IsCell bar ψ γ ∧ …` from `⟨fun T => @Classical.epsilon _ ⟨0⟩ (fun β => β ∈ GlobalTheory.PolFan.balForms bar X ∧ (∀ y, 0 ≤ β y y) ∧ w.evalZ β = 1 ∧ ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), GlobalTheory.PolFan.IsCell bar ψ γ ∧ Set.range γ = T ∧ GlobalTheory.PolFan.InRCone γ β), fun T h => Classical. …`. Use `⟨S0 ∪ ch '' {T | T ⊆ S0}, hS0.union (hS0.finite_subsets.image _), ?_⟩` and prove the remaining obligations.

Introduce `B hB`. Take `⟨e, m, γ, c, hcell, hγS, hc, hBe⟩` from `hcov B hB`. Distinguish the cases in `hz : ∀ β ∈ GlobalTheory.PolFan.balForms bar X, (∀ y, 0 ≤ β y y) → GlobalTheory.PolFan.InRCone γ β → w.evalZ β = 0`. Conclude with `⟨e, m, γ, c, hS1 X hq m γ hcell hz, fun i => Set.mem_union_left _ (hγS i), hc, hBe⟩`. Use `push Not at hz`.

Take `⟨β₀, hbal, hpsd, hin, hne⟩` from `hz`. Establish `hw1 : w.evalZ β₀ = 1` using `((hC X hq).1 β₀ hbal hpsd).resolve_left hne`. Establish `hβne : β₀ ≠ 0`. Introduce `h0`. Establish `h21` using `(hC X hq).2.1 β₀ hbal hpsd hw1 2 0 (by rw [h0, smul_zero])`.

Use linear arithmetic over natural numbers and integers. Establish `hsymm : ∀ (i : Fin m) (y z : X), (γ i) y z = (γ i) z y` using `fun i => (show (∀ y z : X, (γ i) y z = (γ i) z y) ∧ _ from hcell.mem i).1`. Establish `hBr : GlobalTheory.PolFan.pullR e.toLinearMap B ∈ GlobalTheory.PolCell.rcone γ`. Simplify using `only [GlobalTheory.PolCell.rcone, Set.mem_ofPred_eq]`. Conclude with `⟨c, hc, hBe⟩`.

Take `⟨m', s, h, hcut, hpos, hB'⟩` from `GlobalTheory.T.realCone_covered_by_star_at_point X m γ β₀ (GlobalTheory.PolFan.pullR e.toLinearMap B) hsymm hcell.nonneg hβne hin hBr`. Take `⟨t, ht, htB⟩` from `hB'`. Use `⟨e, m' + 1, Fin.cons β₀ fun j => γ (s j), t, hS2 X hq m γ hcell β₀ hbal hpsd hw1 hin m' s h hcut hpos, ?_, ht, htB⟩` and prove the remaining obligations. Introduce `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations.

Rewrite using `[Fin.cons_zero]`. Use `Set.mem_union_right _ ⟨Set.range γ, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hγS i`. Take `⟨hb', hp', hw', m'', γ'', hcell'', hrange, hin''⟩` from `hch (Set.range γ) ⟨β₀, hbal, hpsd, hw1, m, γ, hcell, rfl, hin⟩`.

Establish `hin2 : GlobalTheory.PolFan.InRCone γ (ch (Set.range γ))` using `inRCone_mono_of_range_subset γ γ'' hrange.le hin''`. Conclude with `(hC X hq).2.2 m γ hcell _ hb' hp' β₀ hbal hpsd hw' hw1 hin2 hin`. Rewrite using `[Fin.cons_succ]`. Conclude with `Set.mem_union_left _ (hγS (s j))`.
-/
theorem isStarOf_finite_cover : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O),
    CMOrd O bar → ∀ (q : ℕ) (ψ w ψ' : InvFun O), IsPolyFan bar q ψ → IsCentreSet bar q ψ w → IsStarOf bar q ψ w ψ' →
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
    Module.finrank O X ≤ q → ∃ S : Set (LinearMap.BilinForm ℤ X), S.Finite ∧ ∀ B ∈ psdCone bar X,
      ∃ (e : X ≃ₗ[O] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell bar ψ' γ ∧
        (∀ i, γ i ∈ S) ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i) := by
  intro O _ _ _ _ bar hO q ψ w ψ' hψ hC hStar X _ _ _ _ hq
  classical
  obtain ⟨hS1, hS2, -⟩ := hStar
  obtain ⟨S0, hS0, hcov⟩ := (hψ X hq).finite
  obtain ⟨ch, hch⟩ : ∃ ch : Set (LinearMap.BilinForm ℤ X) → LinearMap.BilinForm ℤ X,
      ∀ T : Set (LinearMap.BilinForm ℤ X),
        (∃ β, β ∈ GlobalTheory.PolFan.balForms bar X ∧ (∀ y, 0 ≤ β y y) ∧ w.evalZ β = 1 ∧
          ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), GlobalTheory.PolFan.IsCell bar ψ γ ∧
            Set.range γ = T ∧ GlobalTheory.PolFan.InRCone γ β) →
        (ch T ∈ GlobalTheory.PolFan.balForms bar X ∧ (∀ y, 0 ≤ ch T y y) ∧ w.evalZ (ch T) = 1 ∧
          ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), GlobalTheory.PolFan.IsCell bar ψ γ ∧
            Set.range γ = T ∧ GlobalTheory.PolFan.InRCone γ (ch T)) :=
    ⟨fun T => @Classical.epsilon _ ⟨0⟩ (fun β => β ∈ GlobalTheory.PolFan.balForms bar X ∧ (∀ y, 0 ≤ β y y) ∧
        w.evalZ β = 1 ∧ ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), GlobalTheory.PolFan.IsCell bar ψ γ ∧
          Set.range γ = T ∧ GlobalTheory.PolFan.InRCone γ β),
      fun T h => Classical.epsilon_spec h⟩
  refine ⟨S0 ∪ ch '' {T | T ⊆ S0}, hS0.union (hS0.finite_subsets.image _), ?_⟩
  intro B hB
  obtain ⟨e, m, γ, c, hcell, hγS, hc, hBe⟩ := hcov B hB
  by_cases hz : ∀ β ∈ GlobalTheory.PolFan.balForms bar X, (∀ y, 0 ≤ β y y) → GlobalTheory.PolFan.InRCone γ β → w.evalZ β = 0
  · exact ⟨e, m, γ, c, hS1 X hq m γ hcell hz, fun i => Set.mem_union_left _ (hγS i), hc, hBe⟩
  · push Not at hz
    obtain ⟨β₀, hbal, hpsd, hin, hne⟩ := hz
    have hw1 : w.evalZ β₀ = 1 := ((hC X hq).1 β₀ hbal hpsd).resolve_left hne
    have hβne : β₀ ≠ 0 := by
      intro h0
      have h21 := (hC X hq).2.1 β₀ hbal hpsd hw1 2 0 (by rw [h0, smul_zero])
      omega
    have hsymm : ∀ (i : Fin m) (y z : X), (γ i) y z = (γ i) z y := fun i =>
      (show (∀ y z : X, (γ i) y z = (γ i) z y) ∧ _ from hcell.mem i).1
    have hBr : GlobalTheory.PolFan.pullR e.toLinearMap B ∈ GlobalTheory.PolCell.rcone γ := by
      simp only [GlobalTheory.PolCell.rcone, Set.mem_ofPred_eq]
      exact ⟨c, hc, hBe⟩
    obtain ⟨m', s, h, hcut, hpos, hB'⟩ :=
      GlobalTheory.T.realCone_covered_by_star_at_point X m γ β₀ (GlobalTheory.PolFan.pullR e.toLinearMap B) hsymm hcell.nonneg hβne hin hBr
    obtain ⟨t, ht, htB⟩ := hB'
    refine ⟨e, m' + 1, Fin.cons β₀ fun j => γ (s j), t,
      hS2 X hq m γ hcell β₀ hbal hpsd hw1 hin m' s h hcut hpos, ?_, ht, htB⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Fin.cons_zero]
      refine Set.mem_union_right _ ⟨Set.range γ, ?_, ?_⟩
      · rintro _ ⟨i, rfl⟩
        exact hγS i
      · obtain ⟨hb', hp', hw', m'', γ'', hcell'', hrange, hin''⟩ :=
          hch (Set.range γ) ⟨β₀, hbal, hpsd, hw1, m, γ, hcell, rfl, hin⟩
        have hin2 : GlobalTheory.PolFan.InRCone γ (ch (Set.range γ)) :=
          inRCone_mono_of_range_subset γ γ'' hrange.le hin''
        exact (hC X hq).2.2 m γ hcell _ hb' hp' β₀ hbal hpsd hw' hw1 hin2 hin
    · rw [Fin.cons_succ]
      exact Set.mem_union_left _ (hγS (s j))

end GlobalTheory.CompanionTheory.Ar.Fan.StarFiniteCover
