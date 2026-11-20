import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MatchSmulAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.RootEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniHolds

open ValuativeRel UpperTheory.ConvolutionTheory.Loc

/- English proof (translation)
Introduce `k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ _ r hr0 hr1`. Establish `hc : Continuous (algebraMap k E)` using `(UpperTheory.V.Z.Tf.Orb.extCont_holds k E).1`. Establish `hS : {z : E | valuation E (z - 1) < r} ∈ nhds (algebraMap k E 1)`. Rewrite using `[map_one]`. Conclude with `(IsValuativeTopology.hasBasis_nhds' (1 : E)).mem_of_mem hr0.ne'`.

Take `⟨γ, hγ0, hγ⟩` from `(IsValuativeTopology.hasBasis_nhds' (1 : k)).mem_iff.mp (hc.continuousAt.preimage_mem_nhds hS)`. Use `set d := Module.finrank k E with hd`. Establish `hdpos : 0 < d` using `Module.finrank_pos`. Establish `hdk : (d : k) ≠ 0` using `Nat.cast_ne_zero.mpr hdpos.ne'`. Use `set δ := valuation k (d : k) with hδ`.

Establish `hδ0 : δ ≠ 0` using `by simpa [hδ] using hdk`. Establish `hδ1 : δ ≤ 1`. Rewrite using `[hδ]`. Use `clear hδ hδ0 hdk hdpos hd`. Proceed by induction on `d with`.

Consider the case `zero => simp`. Consider the case `succ n ih`. Use `push_cast`. Conclude with `((valuation k).map_add _ _).trans (max_le ih (by simp))`. Take `⟨t, ht0, ht1⟩` from `Valuation.IsNontrivial.exists_lt_one (v := valuation k)`.

Use `set ε := valuation k t with hεdef`. Use `set μ := min γ δ`. Establish `hμ0 : 0 < μ` using `lt_min (zero_lt_iff.mpr hγ0) (zero_lt_iff.mpr hδ0)`. Establish `hε0 : 0 < ε` using `zero_lt_iff.mpr (by simpa [hεdef] using ht0)`. Use `set r₂ := μ * ε`.

Establish `hr₂0 : 0 < r₂` using `mul_pos hμ0 hε0`. Establish `hr₂μ : r₂ < μ`. Combine the equalities or inequalities in the displayed calculation. Establish `hr₂γ : r₂ < γ` using `hr₂μ.trans_le (min_le_left _ _)`. Establish `hr₂δ : r₂ < δ` using `hr₂μ.trans_le (min_le_right _ _)`.

Establish `hr₀r₂ : r₂ * δ ≤ r₂`. Combine the equalities or inequalities in the displayed calculation. Use `⟨r₂ * δ, mul_pos hr₂0 (zero_lt_iff.mpr hδ0), hr₀r₂.trans_lt (hr₂δ.trans_le hδ1), ?_⟩` and prove the remaining obligations. Introduce `x hx`. Establish `hmem : ∀ y : k, valuation k (y - 1) ≤ r₂ → valuation E (algebraMap k E y - 1) ≤ r`.

Introduce `y hy`. Conclude with `le_of_lt (hγ (lt_of_le_of_lt hy hr₂γ))`. Use `⟨hmem x (hx.trans hr₀r₂), ?_⟩` and prove the remaining obligations. Establish `hg : Matrix.GeneralLinearGroup.scalar (Fin 1) x ∈ UpperTheory.ConvolutionTheory.Loc.ball 1 (r₂ * δ)`. Introduce `i j`.

Rewrite using `[Subsingleton.elim i 0, Subsingleton.elim j 0]`. Simplify `hx` using `[Matrix.GeneralLinearGroup.scalar]`. Take `⟨u, ⟨hu, hud⟩, -⟩` from `UpperTheory.ConvolutionTheory.Loc.rootEx k 1 d r₂ hr₂δ _ hg`. Establish `hpow : ∀ (M : Matrix (Fin 1) (Fin 1) k) (m : ℕ), (M ^ m) 0 0 = (M 0 0) ^ m`. Introduce `M m`.

Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih => rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_one, ih, pow_succ]`. Establish `hw : ((u : Matrix (Fin 1) (Fin 1) k) 0 0) ^ d = (x : k)`. Use `congrArg (fun g : GL (Fin 1) k => (g : Matrix (Fin 1) (Fin 1) k) 0 0) hud` as an intermediate fact.

Simplify using `only [Units.val_pow_eq_pow_val] at this`. Rewrite using `[← hpow, this]`. Simplify using `[Matrix.GeneralLinearGroup.scalar]`. Establish `hw1 : valuation k ((u : Matrix (Fin 1) (Fin 1) k) 0 0 - 1) ≤ r₂`. Simplify using `using hu 0 0`.

Establish `hw0 : (u : Matrix (Fin 1) (Fin 1) k) 0 0 ≠ 0`. Introduce `h`. Rewrite `hw` using `[h, zero_pow hdpos.ne']`. Conclude with `x.ne_zero hw.symm`. Use `⟨Units.mk0 (algebraMap k E ((u : Matrix (Fin 1) (Fin 1) k) 0 0)) ((map_ne_zero (algebraMap k E)).mpr hw0), hmem _ hw1, ?_⟩` and prove the remaining obligations.

Rewrite using `[Units.val_mk0, Algebra.norm_algebraMap, ← hd, hw]`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.L.normOpen :
    UpperTheory.Gal.InertialTypesAlt.L.NormOpen := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ _ r hr0 hr1
  have hc : Continuous (algebraMap k E) := (UpperTheory.V.Z.Tf.Orb.extCont_holds k E).1
  have hS : {z : E | valuation E (z - 1) < r} ∈ nhds (algebraMap k E 1) := by
    rw [map_one]
    exact (IsValuativeTopology.hasBasis_nhds' (1 : E)).mem_of_mem hr0.ne'
  obtain ⟨γ, hγ0, hγ⟩ :=
    (IsValuativeTopology.hasBasis_nhds' (1 : k)).mem_iff.mp (hc.continuousAt.preimage_mem_nhds hS)
  set d := Module.finrank k E with hd
  have hdpos : 0 < d := Module.finrank_pos
  have hdk : (d : k) ≠ 0 := Nat.cast_ne_zero.mpr hdpos.ne'
  set δ := valuation k (d : k) with hδ
  have hδ0 : δ ≠ 0 := by simpa [hδ] using hdk
  have hδ1 : δ ≤ 1 := by
    rw [hδ]
    clear hδ hδ0 hdk hdpos hd
    induction d with
    | zero => simp
    | succ n ih =>
      push_cast
      exact ((valuation k).map_add _ _).trans (max_le ih (by simp))
  obtain ⟨t, ht0, ht1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  set ε := valuation k t with hεdef
  set μ := min γ δ
  have hμ0 : 0 < μ := lt_min (zero_lt_iff.mpr hγ0) (zero_lt_iff.mpr hδ0)
  have hε0 : 0 < ε := zero_lt_iff.mpr (by simpa [hεdef] using ht0)
  set r₂ := μ * ε
  have hr₂0 : 0 < r₂ := mul_pos hμ0 hε0
  have hr₂μ : r₂ < μ := by
    calc r₂ = μ * ε := rfl
      _ < μ * 1 := mul_lt_mul_of_pos_left ht1 hμ0
      _ = μ := mul_one μ
  have hr₂γ : r₂ < γ := hr₂μ.trans_le (min_le_left _ _)
  have hr₂δ : r₂ < δ := hr₂μ.trans_le (min_le_right _ _)
  have hr₀r₂ : r₂ * δ ≤ r₂ := by
    calc r₂ * δ ≤ r₂ * 1 := mul_le_mul_of_nonneg_left hδ1 zero_le'
      _ = r₂ := mul_one r₂
  refine ⟨r₂ * δ, mul_pos hr₂0 (zero_lt_iff.mpr hδ0), hr₀r₂.trans_lt (hr₂δ.trans_le hδ1), ?_⟩
  intro x hx
  have hmem : ∀ y : k, valuation k (y - 1) ≤ r₂ → valuation E (algebraMap k E y - 1) ≤ r := by
    intro y hy
    exact le_of_lt (hγ (lt_of_le_of_lt hy hr₂γ))
  refine ⟨hmem x (hx.trans hr₀r₂), ?_⟩
  have hg : Matrix.GeneralLinearGroup.scalar (Fin 1) x ∈ UpperTheory.ConvolutionTheory.Loc.ball 1 (r₂ * δ) := by
    intro i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simpa [Matrix.GeneralLinearGroup.scalar] using hx
  obtain ⟨u, ⟨hu, hud⟩, -⟩ := UpperTheory.ConvolutionTheory.Loc.rootEx k 1 d r₂ hr₂δ _ hg
  have hpow : ∀ (M : Matrix (Fin 1) (Fin 1) k) (m : ℕ), (M ^ m) 0 0 = (M 0 0) ^ m := by
    intro M m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_one, ih, pow_succ]
  have hw : ((u : Matrix (Fin 1) (Fin 1) k) 0 0) ^ d = (x : k) := by
    have := congrArg (fun g : GL (Fin 1) k => (g : Matrix (Fin 1) (Fin 1) k) 0 0) hud
    simp only [Units.val_pow_eq_pow_val] at this
    rw [← hpow, this]
    simp [Matrix.GeneralLinearGroup.scalar]
  have hw1 : valuation k ((u : Matrix (Fin 1) (Fin 1) k) 0 0 - 1) ≤ r₂ := by
    simpa using hu 0 0
  have hw0 : (u : Matrix (Fin 1) (Fin 1) k) 0 0 ≠ 0 := by
    intro h
    rw [h, zero_pow hdpos.ne'] at hw
    exact x.ne_zero hw.symm
  refine ⟨Units.mk0 (algebraMap k E ((u : Matrix (Fin 1) (Fin 1) k) 0 0))
    ((map_ne_zero (algebraMap k E)).mpr hw0), hmem _ hw1, ?_⟩
  rw [Units.val_mk0, Algebra.norm_algebraMap, ← hd, hw]
