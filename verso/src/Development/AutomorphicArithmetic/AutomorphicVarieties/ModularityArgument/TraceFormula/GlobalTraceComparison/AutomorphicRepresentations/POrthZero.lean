import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.OrthZero

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.OZ

private def bump (s : ℝ) : ℂ := ((max 0 (min 1 (2 - |s|)) : ℝ) : ℂ)

/- English proof (translation)
Unfold `bump`. Use `fun_prop`.
-/
private theorem bump_cont : Continuous bump := by
  unfold bump
  fun_prop

/- English proof (translation)
Use `HasCompactSupport.intro (isCompact_Icc (a := (-2 : ℝ)) (b := 2)) fun s hs => ?_` and prove the remaining obligations. Establish `h : 2 < |s|`. Assume the negation of the conclusion as `hc`. Conclude with `hs (abs_le.1 (not_lt.1 hc))`. Establish `h1 : min 1 (2 - |s|) ≤ 0` using `(min_le_right _ _).trans (by linarith)`.

Simplify using `[bump, max_eq_left h1]`.
-/
private theorem bump_supp : HasCompactSupport bump := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (-2 : ℝ)) (b := 2)) fun s hs => ?_
  have h : 2 < |s| := by
    by_contra hc
    exact hs (abs_le.1 (not_lt.1 hc))
  have h1 : min 1 (2 - |s|) ≤ 0 := (min_le_right _ _).trans (by linarith)
  simp [bump, max_eq_left h1]

/- English proof (translation)
Establish `h1 : |s| < 1` using `abs_lt.2 h`. Establish `h2 : min 1 (2 - |s|) = 1` using `min_eq_left (by linarith)`. Simplify using `[bump, h2]`.
-/
private theorem bump_one {s : ℝ} (h : s ∈ Set.Ioo (-1 : ℝ) 1) : bump s = 1 := by
  have h1 : |s| < 1 := abs_lt.2 h
  have h2 : min 1 (2 - |s|) = 1 := min_eq_left (by linarith)
  simp [bump, h2]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.OZ

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.OZ in
/- English proof (translation)
Introduce `hB hA _ E _ _ _ n hn D π _ f hf hS ho`. Take `⟨hl, hmul, -⟩` from `hB E n hn`. Take `⟨hfc, hfr, hfs, -⟩` from `hf`. Take `⟨v, hv, hve⟩` from `hS bump bump_cont bump_supp`. Establish `horth : v ∈ (piSp D π Unit)ᗮ`.

Rewrite using `[piSp, Submodule.orthogonal_closure, Submodule.mem_orthogonal]`. Introduce `g hg`. Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem g hg`. Take `⟨ψ, hψ, u, hu, hus, he⟩` from `hg ()`.

Establish `hz` using `ho ψ hψ (fun s => starRingEnd ℂ (u s) * bump s) ((Complex.continuous_conj.comp hu).mul bump_cont) ((hus.comp_left (g := starRingEnd ℂ) (map_zero _)).mul_right)`. Rewrite using `[PiLp.inner_apply]`. Simplify using `only [Finset.univ_unique, Finset.sum_singleton]`. Rewrite using `[L2.inner_def]`. Rewrite using `[← hz, prW]`.

Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [he, hve] with x h1 h2`. Simplify using `only [PUnit.default_eq_unit]`. Rewrite using `[h1, h2]`. Simplify using `only [RCLike.inner_apply, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]`. Consider the case `smul r x _ hx => rw [inner_smul_left, hx, mul_zero]`. Establish `hv0 : v = 0` using `inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 horth v hv)`.

Establish `hlat : ∀ x : H E n 0, ldet x ∈ Set.Ioo (-1 : ℝ) 1 → f x.1 = 0`. Use `hA E n D (fun x => f x.1) (fun _ => 0) (Set.Ioo (-1 : ℝ) 1) (hfc.comp continuous_fst) continuous_const ?_ (fun _ _ => rfl) isOpen_Ioo ?_` and prove the remaining obligations. Introduce `γ x`. Take `⟨⟨a, b⟩, hab⟩` from `γ.2`. Establish `h1 : (γ : H E n 0).1 = ratGL E n a` using `by rw [← hab]; rfl`.

Use `show f ((γ : H E n 0).1 * x.1) = f x.1`. Rewrite using `[h1, hfr]`. Establish `hz : ((v () : Lp ℂ 2 D.ν) : H E n 0 → ℂ) =ᵐ[D.ν] 0`. Rewrite using `[hv0]`. Conclude with `Lp.coeFn_zero _ _ _`.

Use `filter_upwards [hve, hz] with x h1 h2 h3`. Rewrite `h1` using `[h2]`. Simplify `h1.symm` using `[bump_one h3]`. Use function extensionality and compare the values at `g`. Establish `hx` using `hlat (ac E n (-ldet ((g, 1) : H E n 0)) * (g, 1)) (by`.

Rewrite using `[hmul, hl]`. Use the proof step `simp)`. Establish `: (ac E n (-ldet ((g, 1) : H E n 0)) * (g, 1) : H E n 0).1 = splitCentre E n (-ldet ((g, 1) : H E n 0) / (n * Module.finrank ℚ E)) * g` using `rfl`. Rewrite `hx` using `[this, hfs]`. Conclude with `hx`.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.orthZero_pf :
    Basic → AeEq → WtInd → OrthZero := by
  intro hB hA _ E _ _ _ n hn D π _ f hf hS ho
  obtain ⟨hl, hmul, -⟩ := hB E n hn
  obtain ⟨hfc, hfr, hfs, -⟩ := hf
  obtain ⟨v, hv, hve⟩ := hS bump bump_cont bump_supp
  have horth : v ∈ (piSp D π Unit)ᗮ := by
    rw [piSp, Submodule.orthogonal_closure, Submodule.mem_orthogonal]
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨ψ, hψ, u, hu, hus, he⟩ := hg ()
      have hz := ho ψ hψ (fun s => starRingEnd ℂ (u s) * bump s)
        ((Complex.continuous_conj.comp hu).mul bump_cont)
        ((hus.comp_left (g := starRingEnd ℂ) (map_zero _)).mul_right)
      rw [PiLp.inner_apply]
      simp only [Finset.univ_unique, Finset.sum_singleton]
      rw [L2.inner_def]
      rw [← hz, prW]
      refine integral_congr_ae ?_
      filter_upwards [he, hve] with x h1 h2
      simp only [PUnit.default_eq_unit]
      rw [h1, h2]
      simp only [RCLike.inner_apply, map_mul]
      ring
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul r x _ hx => rw [inner_smul_left, hx, mul_zero]
  have hv0 : v = 0 := inner_self_eq_zero.1
    ((Submodule.mem_orthogonal _ _).1 horth v hv)
  have hlat : ∀ x : H E n 0, ldet x ∈ Set.Ioo (-1 : ℝ) 1 → f x.1 = 0 := by
    refine hA E n D (fun x => f x.1) (fun _ => 0) (Set.Ioo (-1 : ℝ) 1) (hfc.comp continuous_fst)
      continuous_const ?_ (fun _ _ => rfl) isOpen_Ioo ?_
    · intro γ x
      obtain ⟨⟨a, b⟩, hab⟩ := γ.2
      have h1 : (γ : H E n 0).1 = ratGL E n a := by rw [← hab]; rfl
      show f ((γ : H E n 0).1 * x.1) = f x.1
      rw [h1, hfr]
    · have hz : ((v () : Lp ℂ 2 D.ν) : H E n 0 → ℂ) =ᵐ[D.ν] 0 := by
        rw [hv0]
        exact Lp.coeFn_zero _ _ _
      filter_upwards [hve, hz] with x h1 h2 h3
      rw [h2] at h1
      simpa [bump_one h3] using h1.symm
  funext g
  have hx := hlat (ac E n (-ldet ((g, 1) : H E n 0)) * (g, 1)) (by
    rw [hmul, hl]; simp)
  have : (ac E n (-ldet ((g, 1) : H E n 0)) * (g, 1) : H E n 0).1 =
      splitCentre E n (-ldet ((g, 1) : H E n 0) / (n * Module.finrank ℚ E)) * g := rfl
  rw [this, hfs] at hx
  exact hx
