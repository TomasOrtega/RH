import Mathlib
import Formalism.LocalToGlobal.Columns.BrzoPairAtZeroRight
import Formalism.SizeWindowBrackets.ChainSlopeWindows.TruncatedLatticeHolds
import Formalism.MeanHeightDescent.AverageDegreeBounds.SpanMuMin

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN

section F3

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.majAt`. Rewrite using `[star_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[star_mul', star_star, mul_comm]`.
-/
theorem majorant_conj_symm (A : HLat K) (v : InfinitePlace K) (x y : A.V) :
    majAt A.b A.X v y x = star (majAt A.b A.X v x y) := by
  unfold Formalism.HermitianLatticesTheory.majAt
  rw [star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_mul', star_star, mul_comm]

variable [IsTotallyComplex K] {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Use `set L : Submodule (𝓞 K) V := Submodule.span (𝓞 K) ({x} : Set V) with hL`. Establish `hLfg : L.FG` using `Submodule.fg_span (Set.finite_singleton x)`. Establish `hL0 : L ≠ ⊥` using `fun h => hx ((Submodule.span_singleton_eq_bot).1 h)`. Establish `hrk : rkK (K` using `K) L = 1 := Formalism.ExtensionFiltration.rkK_span_singleton x hx`. Establish `hf : 0 < nPl K` using `Fintype.card_pos`.

Establish `hfR : (0 : ℝ) < (nPl K : ℝ)` using `by exact_mod_cast hf`. Take `⟨-, hmu, -⟩` from `size_maximal_slope K V ι b X hX L hLfg hL0`. Establish `hpos : 0 < ht b X L` using `(place_lattice_structure K V ι b X hX L hLfg).2.2`. Establish `hli : LinearIndependent K (fun _ : Fin 1 => x)` using `LinearIndependent.of_subsingleton (0 : Fin 1) hx`. Establish `hrange : Set.range (fun _ : Fin 1 => x) = {x}` using `Set.range_const`.

Establish `hg` using `(height_gram_determinant K V ι b X hX 1 (fun _ : Fin 1 => x) hli).1`. Rewrite `hg` using `[hrange]`. Establish `hht : c ^ (nPl K) ≤ ht b X L`. Rewrite using `[hL, hg]`. Establish `h1 : ∀ v : InfinitePlace K, c ≤ (gramPl b X v (fun _ : Fin 1 => x)).det.re`.

Introduce `v`. Rewrite using `[Matrix.det_fin_one]`. Simplify using `only [gramPl, Matrix.of_apply]`. Rewrite using `[Formalism.ExtensionFiltration.majAt_self_re]`. Conclude with `hn v`.

Combine the equalities or inequalities in the displayed calculation. Establish `hlog : (nPl K : ℝ) * Real.log c ≤ Real.log (ht b X L)`. Rewrite using `[← Real.log_pow]`. Conclude with `Real.log_le_log (by positivity) hht`. Rewrite using `[hmu]`.

Unfold `size`. Rewrite using `[Real.log_rpow hpos, hrk]`. Establish `: Real.log c / 2 ≤ (1 : ℝ) / (2 * (nPl K : ℝ) * ((1 : ℕ) : ℝ)) * Real.log (ht b X L)`. Rewrite using `[Nat.cast_one, mul_one, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem slope_line_le_neg_log (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) (x : V) (hx : x ≠ 0)
    (c : ℝ) (hc : 0 < c) (hn : ∀ v, c ≤ normAt b X v x ^ 2) :
    muDef b X (Submodule.span (𝓞 K) ({x} : Set V)) ≤ -Real.log c := by
  set L : Submodule (𝓞 K) V := Submodule.span (𝓞 K) ({x} : Set V) with hL
  have hLfg : L.FG := Submodule.fg_span (Set.finite_singleton x)
  have hL0 : L ≠ ⊥ := fun h => hx ((Submodule.span_singleton_eq_bot).1 h)
  have hrk : rkK (K := K) L = 1 := Formalism.ExtensionFiltration.rkK_span_singleton x hx
  have hf : 0 < nPl K := Fintype.card_pos
  have hfR : (0 : ℝ) < (nPl K : ℝ) := by exact_mod_cast hf
  obtain ⟨-, hmu, -⟩ := size_maximal_slope K V ι b X hX L hLfg hL0
  have hpos : 0 < ht b X L := (place_lattice_structure K V ι b X hX L hLfg).2.2
  have hli : LinearIndependent K (fun _ : Fin 1 => x) := LinearIndependent.of_subsingleton (0 : Fin 1) hx
  have hrange : Set.range (fun _ : Fin 1 => x) = {x} := Set.range_const
  have hg := (height_gram_determinant K V ι b X hX 1 (fun _ : Fin 1 => x) hli).1
  rw [hrange] at hg
  have hht : c ^ (nPl K) ≤ ht b X L := by
    rw [hL, hg]
    have h1 : ∀ v : InfinitePlace K, c ≤ (gramPl b X v (fun _ : Fin 1 => x)).det.re := by
      intro v
      rw [Matrix.det_fin_one]
      simp only [gramPl, Matrix.of_apply]
      rw [Formalism.ExtensionFiltration.majAt_self_re]
      exact hn v
    calc c ^ (nPl K) = ∏ _v : InfinitePlace K, c := by rw [Finset.prod_const, Finset.card_univ]; rfl
      _ ≤ ∏ v, (gramPl b X v (fun _ : Fin 1 => x)).det.re := Finset.prod_le_prod (fun v _ => hc.le) (fun v _ => h1 v)
  have hlog : (nPl K : ℝ) * Real.log c ≤ Real.log (ht b X L) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hht
  rw [hmu]
  unfold size
  rw [Real.log_rpow hpos, hrk]
  have : Real.log c / 2 ≤ (1 : ℝ) / (2 * (nPl K : ℝ) * ((1 : ℕ) : ℝ)) * Real.log (ht b X L) := by
    rw [Nat.cast_one, mul_one, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    nlinarith
  linarith

/- English proof (translation)
Establish `: Module.Finite K V` using `Module.Finite.of_basis b`. Use `set L : Submodule (𝓞 K) V := Submodule.span (𝓞 K) ({x} : Set V) with hL`. Establish `hLfg : L.FG` using `Submodule.fg_span (Set.finite_singleton x)`. Establish `hL0 : L ≠ ⊥` using `fun h => hx ((Submodule.span_singleton_eq_bot).1 h)`. Establish `hrk : rkK (K` using `K) L = 1 := Formalism.ExtensionFiltration.rkK_span_singleton x hx`.

Use `Formalism.LFunctionChainParameters.slopeLatticeData.muMaxDef_le b X hL0 fun Q hQ hQ0 => ?_` and prove the remaining obligations. Establish `h1 : rkK (K` using `K) Q ≤ 1 := by`. Rewrite using `[← hrk]`. Conclude with `Submodule.finrank_mono (Submodule.span_mono hQ)`. Establish `h2 : 0 < rkK (K` using `K) Q := Formalism.LFunctionChainParameters.slopeLatticeData.rkK_pos hQ0`.

Establish `hrkQ : rkK (K` using `K) Q = rkK (K := K) L := by omega`. Establish `hi` using `(Formalism.LFunctionChainParameters.LLcv.index_slope_formula K V ι b X hX L Q hLfg hQ hQ0 hrkQ).1`. Establish `hl : 0 ≤ Real.log (Q.toAddSubgroup.relIndex L.toAddSubgroup : ℝ)` using `Real.log_natCast_nonneg _`. Establish `hn' : (0 : ℝ) < (Module.finrank ℚ K : ℝ)` using `by exact_mod_cast Module.finrank_pos`. Establish `hd : 0 ≤ 2 * Real.log (Q.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) / ((Module.finrank ℚ K : ℝ) * (rkK L : ℝ))`.

Rewrite using `[hrk]`. Check the signs of the components of the expression. Use `slope_line_le_neg_log b X hX x hx c hc hn` as an intermediate fact. Rewrite using `[hi]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem max_slope_line_neg_log (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) (x : V) (hx : x ≠ 0)
    (c : ℝ) (hc : 0 < c) (hn : ∀ v, c ≤ normAt b X v x ^ 2) :
    muMaxDef b X (Submodule.span (𝓞 K) ({x} : Set V)) ≤ -Real.log c := by
  have : Module.Finite K V := Module.Finite.of_basis b
  set L : Submodule (𝓞 K) V := Submodule.span (𝓞 K) ({x} : Set V) with hL
  have hLfg : L.FG := Submodule.fg_span (Set.finite_singleton x)
  have hL0 : L ≠ ⊥ := fun h => hx ((Submodule.span_singleton_eq_bot).1 h)
  have hrk : rkK (K := K) L = 1 := Formalism.ExtensionFiltration.rkK_span_singleton x hx
  refine Formalism.LFunctionChainParameters.slopeLatticeData.muMaxDef_le b X hL0 fun Q hQ hQ0 => ?_
  have h1 : rkK (K := K) Q ≤ 1 := by
    rw [← hrk]
    exact Submodule.finrank_mono (Submodule.span_mono hQ)
  have h2 : 0 < rkK (K := K) Q := Formalism.LFunctionChainParameters.slopeLatticeData.rkK_pos hQ0
  have hrkQ : rkK (K := K) Q = rkK (K := K) L := by omega
  have hi := (Formalism.LFunctionChainParameters.LLcv.index_slope_formula K V ι b X hX L Q hLfg hQ hQ0 hrkQ).1
  have hl : 0 ≤ Real.log (Q.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) := Real.log_natCast_nonneg _
  have hn' : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  have hd : 0 ≤ 2 * Real.log (Q.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) / ((Module.finrank ℚ K : ℝ) * (rkK L : ℝ)) := by
    rw [hrk]
    positivity
  have := slope_line_le_neg_log b X hX x hx c hc hn
  rw [hi]
  linarith

end F3

section F3b

variable {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]

/- English proof (translation)
Use `set N : γ → Submodule (𝓞 K) A.V := fun c => Submodule.span (𝓞 K) ({e c} : Set A.V) with hN`. Establish `hfg : ∀ c, (N c).FG` using `fun c => Submodule.fg_span (Set.finite_singleton _)`. Establish `hne : ∀ c, N c ≠ ⊥` using `fun c h => he c ((Submodule.span_singleton_eq_bot).1 h)`. Establish `ho : ∀ c c', c ≠ c' → ∀ x ∈ N c, ∀ y ∈ N c', ∀ v, majAt A.b A.X v x y = 0`. Introduce `c c' hcc x hx y hy v`.

Establish `h1 : N c ≤ brzo_perp A (e c')` using `(Submodule.span_singleton_le_iff_mem _ _).2 fun v => horth c' c (Ne.symm hcc) v`. Establish `h2 : e c' ∈ brzo_perp A x` using `fun v => by`. Rewrite using `[majorant_conj_symm A v (e c') x, h1 hx v, star_zero]`. Conclude with `((Submodule.span_singleton_le_iff_mem _ _).2 h2) hy v`. Take `⟨-, h2⟩` from `hlat_orth_fin N hA hfg hne ho Finset.univ`.

Establish `hsup : (⨆ c, N c) = ⨆ c ∈ (Finset.univ : Finset γ), N c` using `by simp`. Rewrite using `[hsup]`. Establish `hb` using `(h2 Finset.univ_nonempty).2 ((-Real.log c0 + Real.log 2 - logDisc K / (Module.finrank ℚ K : ℝ)) / 2) fun c _ => by`. Use `max_slope_line_neg_log A.b A.X hA (e c) (he c) c0 hc0 (hn c)` as an intermediate fact. Unfold `muMaxDef at this`.

Combine the linear equalities and inequalities to obtain the conclusion. Unfold `muMaxDef`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem max_slope_orthogonal_neg_log (A : HLat K) (hA : FrameOK A) {γ : Type} [Fintype γ] [Nonempty γ] (e : γ → A.V) (he : ∀ c, e c ≠ 0)
    (horth : ∀ c c', c ≠ c' → ∀ v, majAt A.b A.X v (e c) (e c') = 0) (c0 : ℝ) (hc0 : 0 < c0)
    (hn : ∀ c v, c0 ≤ normAt A.b A.X v (e c) ^ 2) :
    muMaxDef A.b A.X (⨆ c, Submodule.span (𝓞 K) ({e c} : Set A.V)) ≤ -Real.log c0 := by
  classical
  set N : γ → Submodule (𝓞 K) A.V := fun c => Submodule.span (𝓞 K) ({e c} : Set A.V) with hN
  have hfg : ∀ c, (N c).FG := fun c => Submodule.fg_span (Set.finite_singleton _)
  have hne : ∀ c, N c ≠ ⊥ := fun c h => he c ((Submodule.span_singleton_eq_bot).1 h)
  have ho : ∀ c c', c ≠ c' → ∀ x ∈ N c, ∀ y ∈ N c', ∀ v, majAt A.b A.X v x y = 0 := by
    intro c c' hcc x hx y hy v
    have h1 : N c ≤ brzo_perp A (e c') :=
      (Submodule.span_singleton_le_iff_mem _ _).2 fun v => horth c' c (Ne.symm hcc) v
    have h2 : e c' ∈ brzo_perp A x := fun v => by
      rw [majorant_conj_symm A v (e c') x, h1 hx v, star_zero]
    exact ((Submodule.span_singleton_le_iff_mem _ _).2 h2) hy v
  obtain ⟨-, h2⟩ := hlat_orth_fin N hA hfg hne ho Finset.univ
  have hsup : (⨆ c, N c) = ⨆ c ∈ (Finset.univ : Finset γ), N c := by simp
  rw [hsup]
  have hb := (h2 Finset.univ_nonempty).2 ((-Real.log c0 + Real.log 2 - logDisc K / (Module.finrank ℚ K : ℝ)) / 2) fun c _ => by
    have := max_slope_line_neg_log A.b A.X hA (e c) (he c) c0 hc0 (hn c)
    unfold muMaxDef at this
    linarith
  unfold muMaxDef
  linarith

end F3b

end Formalism.L2.Col
