import Development.WeilBound.CoreStatements.MultihomogeneousSquares.AntisymmetryFibreSquares
import Development.WeilBound.CoreStatements.FlagImmersions.SumFundOnRoot

noncomputable section

namespace SquareStatements

open Filter Topology ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

/- English proof (translation)
Use `show ContDiffOn ℝ _ (fun z => ∏ j, (ℓ j).h z ^ n j) _`. Use `contDiffOn_prod fun j _ => ?_` and prove the remaining obligations. Break down `n j with m | m` into its components or cases. Simplify using `using (h j).pow m`. Simplify using `only [zpow_negSucc]`.

Conclude with `((h j).pow (m + 1)).inv fun z hz => (pow_pos ((ℓ j).pos z hz) _).ne'`.
-/
theorem smooth_comb {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} [Fintype J]
    (ℓ : J → HermLine ι) (n : J → ℤ) (h : ∀ j, IsSmoothHerm (ℓ j)) : IsSmoothHerm (Top.combLine ℓ n) := by
  show ContDiffOn ℝ _ (fun z => ∏ j, (ℓ j).h z ^ n j) _
  refine contDiffOn_prod fun j _ => ?_
  rcases n j with m | m
  · simpa using (h j).pow m
  · simp only [zpow_negSucc]
    exact ((h j).pow (m + 1)).inv fun z hz => (pow_pos ((ℓ j).pos z hz) _).ne'

/- English proof (translation)
Introduce `Ψ _ _ N K _ ι _ P e S Re sing h0 hd hc`. Set `cl : ℝ → ℝ` to `fun t => if 0 < t ∧ t ≤ S.t₀ then t else S.t₀`. Establish `hcl : ∀ t, 0 < cl t ∧ cl t ≤ S.t₀` using `fun t => by`. Distinguish the cases in `h : 0 < t ∧ t ≤ S.t₀`. Simplify using `only [cl, if_pos h]`.

Conclude with `h`. Simplify using `only [cl, if_neg h]`. Conclude with `⟨h0, le_rfl⟩`. Use `⟨fun t r => Top.combLine (fun a => Re.line a (cl t)) (Cmp.rootOnFund r), fun t r => ?_, fun t r => smooth_comb _ _ fun a => Re.line_smooth a _ (hcl t).1 (hcl t).2, fun t r z => ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k`.

Establish `h1 : ∀ a, (Re.line a (cl t)).a k = -∑ m ∈ Finset.Iic a.2, (sing (a.1, m)).a k` using `fun a => by`. Rewrite using `[Re.line_deg, hd]`. Use `show (∑ r, _ • (sing r).a) k = _`. Rewrite using `[RootFieldNumerics.Sq.sum_fundOnRoot]`. Simplify using `[Finset.sum_apply]`.

Establish `h2` using `RootFieldNumerics.Sq.sum_root_fund r fun r' => ((sing r').a k : ℝ)`. Use `show (∑ a, Cmp.rootOnFund r a • (Re.line a (cl t)).a) k = _`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, h1, smul_eq_mul]`. Simplify using `only [zsmul_eq_mul] at h2`.

Conclude with `h2` after adjusting the coercions. Use `show ∏ a, _ = ∏ a, _`. Conclude with `Finset.prod_congr rfl fun a _ => by rw [hc a (cl t) z]`. Use `filter_upwards [Ioo_mem_nhdsGT h0] with t ht r z _`. Establish `: cl t = t` using `if_pos ⟨ht.1, ht.2.le⟩`.

Rewrite using `[this]`.
-/
theorem stXB : StX := by
  intro Ψ _ _ N K _ ι _ P e S Re sing h0 hd hc
  classical
  let cl : ℝ → ℝ := fun t => if 0 < t ∧ t ≤ S.t₀ then t else S.t₀
  have hcl : ∀ t, 0 < cl t ∧ cl t ≤ S.t₀ := fun t => by
    by_cases h : 0 < t ∧ t ≤ S.t₀
    · simp only [cl, if_pos h]; exact h
    · simp only [cl, if_neg h]; exact ⟨h0, le_rfl⟩
  refine ⟨fun t r => Top.combLine (fun a => Re.line a (cl t)) (Cmp.rootOnFund r), fun t r => ?_,
    fun t r => smooth_comb _ _ fun a => Re.line_smooth a _ (hcl t).1 (hcl t).2, fun t r z => ?_, ?_⟩
  · funext k
    have h1 : ∀ a, (Re.line a (cl t)).a k = -∑ m ∈ Finset.Iic a.2, (sing (a.1, m)).a k := fun a => by
      rw [Re.line_deg, hd]
      show (∑ r, _ • (sing r).a) k = _
      rw [RootFieldNumerics.Sq.sum_fundOnRoot]
      simp [Finset.sum_apply]
    have h2 := RootFieldNumerics.Sq.sum_root_fund r fun r' => ((sing r').a k : ℝ)
    show (∑ a, Cmp.rootOnFund r a • (Re.line a (cl t)).a) k = _
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, h1, smul_eq_mul]
    simp only [zsmul_eq_mul] at h2
    exact_mod_cast h2
  · show ∏ a, _ = ∏ a, _
    exact Finset.prod_congr rfl fun a _ => by rw [hc a (cl t) z]
  · filter_upwards [Ioo_mem_nhdsGT h0] with t ht r z _
    have : cl t = t := if_pos ⟨ht.1, ht.2.le⟩
    rw [this]

end SquareStatements
