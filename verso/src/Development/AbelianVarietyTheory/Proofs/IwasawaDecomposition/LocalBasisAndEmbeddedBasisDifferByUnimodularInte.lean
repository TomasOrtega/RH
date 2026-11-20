import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominantWeightPolynomialFunctionalMinorsStatement
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.UnipotentAdelicQuotients.WeylLatDual
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsRBasisOfLocBasis
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ComplexPadicNormKappaSplitPrime
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.LocBasisBasR

open Matrix

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_` and prove the remaining obligations. Establish `hs : ‖(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : K)‖ ≤ 1`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]`. Rewrite using `[norm_mul, norm_prod]`.

Conclude with `mul_le_one₀ hs (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => hg _ _)`.
-/
theorem norm_det_le_one {K : Type*} [NormedField K] [IsUltrametricDist K] {N : ℕ}
    (g : Matrix (Fin N) (Fin N) K) (hg : ∀ a b, ‖g a b‖ ≤ 1) : ‖g.det‖ ≤ 1 := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  have hs : ‖(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : K)‖ ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [norm_mul, norm_prod]
  exact mul_le_one₀ hs (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => hg _ _)

/- English proof (translation)
Introduce `D p _ lam τ N L Bm M hL hM`. Take `⟨ρ, hρ⟩` from `GlobalTheory.JetTieCompare.exists_tauHom D lam τ`. Establish `hp : p.Prime` using `Fact.out`. Establish `hns : ∀ s : ℕ, ¬ p ∣ s → ‖ρ (s : D.host.E)‖ = 1` using `fun s hs => by`. Rewrite using `[map_natCast]`.

Conclude with `GlobalTheory.KapSplitNorm.norm_natCast_eq_one p s hs`. Use `set A : Matrix (Fin N) (Fin N) ℂ_[p] := (Bm : Matrix (Fin N) (Fin N) D.host.E).map ρ with hAdef`. Use `set Ai : Matrix (Fin N) (Fin N) ℂ_[p] := ((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E).map ρ with hAidef`. Establish `hAAi : A * Ai = 1`. Rewrite using `[hAdef, hAidef, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero ρ) (map_one ρ)]`.

Establish `hAiA : Ai * A = 1`. Rewrite using `[hAdef, hAidef, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero ρ) (map_one ρ)]`. Establish `hMu : IsUnit M.det` using `Ne.isUnit hM.1`. Establish `hcoord : ∀ x ∈ L, ∀ a, ‖(Ai *ᵥ fun i => ρ (x i)) a‖ ≤ 1`. Introduce `x hx a`.

Take `⟨s, hs, hint⟩` from `(hL x).1 ⟨1, hp.not_dvd_one, by simpa using hx⟩`. Take `⟨c, hc⟩` from `hint a`. Establish `e : (Ai *ᵥ fun i => ρ (x i)) a = ρ ((((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) *ᵥ x) a)`. Rewrite using `[RingHom.map_mulVec]`. Both sides reduce to the same expression.

Establish `hs1` using `hns s hs`. Establish `hs0 : ρ (s : D.host.E) ≠ 0` using `by intro h; rw [h, norm_zero] at hs1; exact zero_ne_one hs1`. Establish `e2 : ρ ((((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) *ᵥ x) a) = (ρ (s : D.host.E))⁻¹ * ρ (algebraMap (𝓞 D.host.E) D.host.E c)`. Rewrite using `[hc, map_mul]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e, e2, norm_mul, norm_inv, hs1, inv_one, one_mul]`. Conclude with `GlobalTheory.JetTieCompare.norm_int_le ρ c`. Establish `hg : ∀ a b, ‖(Ai * M) a b‖ ≤ 1`. Introduce `a b`. Take `⟨n, r, x, hr, hx, hcol⟩` from `hM.2.2 b`.

Establish `: (Ai * M) a b = ∑ k, r k * (Ai *ᵥ fun i => ρ (x k i)) a`. Simplify using `only [Matrix.mul_apply, Matrix.mulVec, dotProduct, hcol, hρ, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring`. Rewrite using `[this]`.

Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (hr k) (norm_nonneg _) (hcoord _ (hx k) a)`. Use `⟨Ai * M, hg, ?_, ?_⟩` and prove the remaining obligations. Establish `hh : ∀ b a, ‖(M⁻¹ * A) b a‖ ≤ 1`.

Introduce `b a`. Set `x : Fin N → D.host.E` to `fun j => (Bm : Matrix (Fin N) (Fin N) D.host.E) j a`. Establish `hxe : x = (Bm : Matrix (Fin N) (Fin N) D.host.E) *ᵥ Pi.single a 1`. Use function extensionality and compare the values at `j`. Simplify using `[x, Matrix.mulVec_single]`.

Establish `hrhs : ∃ s : ℕ, ¬ p ∣ s ∧ ∀ c, (s : D.host.E) * (((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) *ᵥ x) c ∈ (algebraMap (𝓞 D.host.E) D.host.E).range`. Use `⟨1, hp.not_dvd_one, fun c => ?_⟩` and prove the remaining obligations. Rewrite using `[hxe, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, Nat.cast_one, one_mul, Pi.single_apply]`. Use `split_ifs`. Conclude with `⟨1, map_one _⟩`.

Conclude with `⟨0, map_zero _⟩`. Take `⟨s, hs, hmem⟩` from `(hL x).2 hrhs`. Establish `h` using `hM.2.1 _ hmem b`. Rewrite `h` using `[hρ]`. Establish `e : (fun j => ρ (((s : D.host.E) • x) j)) = ρ (s : D.host.E) • fun j => ρ (x j)`.

Use function extensionality and compare the values at `j`. Express the relevant statement in the definitionally equal form `ρ ((s : D.host.E) * x j) = ρ (s : D.host.E) * ρ (x j)`. Rewrite using `[map_mul]`. Rewrite `h` using `[e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, norm_mul, hns s hs, one_mul]`. Use `h using 2` and compare the differences between its conclusion and the goal.

Simplify using `[A, x, Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Establish `hprod : (Ai * M) * (M⁻¹ * A) = 1`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc M, Matrix.mul_nonsing_inv _ hMu, Matrix.one_mul, hAiA]`. Establish `hd` using `congrArg Matrix.det hprod`. Rewrite `hd` using `[Matrix.det_mul, Matrix.det_one]`.

Establish `hn` using `congrArg norm hd`. Rewrite `hn` using `[norm_mul, norm_one]`. Establish `h1` using `norm_det_le_one _ hg`. Establish `h2` using `norm_det_le_one _ (fun b a => hh b a)`. Assume the negation of the conclusion as `hne`.

Establish `hlt : ‖(Ai * M).det‖ < 1` using `lt_of_le_of_ne h1 hne`. Establish `: ‖(Ai * M).det‖ * ‖(M⁻¹ * A).det‖ < 1` using `lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) h2) hlt`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hρ, ← Matrix.mul_assoc]`. Express the relevant statement in the definitionally equal form `M = A * Ai * M`.

Rewrite using `[hAAi, Matrix.one_mul]`.
-/
theorem main : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (Bm : GL (Fin N) D.host.E) (M : Matrix (Fin N) (Fin N) ℂ_[p]), Formalism.L2.Forms.IsLocBasis p (L : Set (Fin N → D.host.E)) Bm → GL3Columns.BasR D lam τ L M → ∃ g : Matrix (Fin N) (Fin N) ℂ_[p], (∀ a b, ‖g a b‖ ≤ 1) ∧ ‖g.det‖ = 1 ∧ M = (Bm : Matrix (Fin N) (Fin N) D.host.E).map (TaylorLogMetric.tauEmb D lam τ) * g := by
  intro D p _ lam τ N L Bm M hL hM
  obtain ⟨ρ, hρ⟩ := GlobalTheory.JetTieCompare.exists_tauHom D lam τ
  have hp : p.Prime := Fact.out
  have hns : ∀ s : ℕ, ¬ p ∣ s → ‖ρ (s : D.host.E)‖ = 1 := fun s hs => by
    rw [map_natCast]; exact GlobalTheory.KapSplitNorm.norm_natCast_eq_one p s hs
  set A : Matrix (Fin N) (Fin N) ℂ_[p] := (Bm : Matrix (Fin N) (Fin N) D.host.E).map ρ with hAdef
  set Ai : Matrix (Fin N) (Fin N) ℂ_[p] := ((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E).map ρ with hAidef
  have hAAi : A * Ai = 1 := by
    rw [hAdef, hAidef, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero ρ) (map_one ρ)]
  have hAiA : Ai * A = 1 := by
    rw [hAdef, hAidef, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero ρ) (map_one ρ)]
  have hMu : IsUnit M.det := Ne.isUnit hM.1

  have hcoord : ∀ x ∈ L, ∀ a, ‖(Ai *ᵥ fun i => ρ (x i)) a‖ ≤ 1 := by
    intro x hx a
    obtain ⟨s, hs, hint⟩ := (hL x).1 ⟨1, hp.not_dvd_one, by simpa using hx⟩
    obtain ⟨c, hc⟩ := hint a
    have e : (Ai *ᵥ fun i => ρ (x i)) a = ρ ((((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) *ᵥ x) a) := by
      rw [RingHom.map_mulVec]; rfl
    have hs1 := hns s hs
    have hs0 : ρ (s : D.host.E) ≠ 0 := by intro h; rw [h, norm_zero] at hs1; exact zero_ne_one hs1
    have e2 : ρ ((((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) *ᵥ x) a) =
        (ρ (s : D.host.E))⁻¹ * ρ (algebraMap (𝓞 D.host.E) D.host.E c) := by
      rw [hc, map_mul]; field_simp
    rw [e, e2, norm_mul, norm_inv, hs1, inv_one, one_mul]
    exact GlobalTheory.JetTieCompare.norm_int_le ρ c
  have hg : ∀ a b, ‖(Ai * M) a b‖ ≤ 1 := by
    intro a b
    obtain ⟨n, r, x, hr, hx, hcol⟩ := hM.2.2 b
    have : (Ai * M) a b = ∑ k, r k * (Ai *ᵥ fun i => ρ (x k i)) a := by
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, hcol, hρ, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (hr k) (norm_nonneg _) (hcoord _ (hx k) a)
  refine ⟨Ai * M, hg, ?_, ?_⟩
  · have hh : ∀ b a, ‖(M⁻¹ * A) b a‖ ≤ 1 := by
      intro b a
      let x : Fin N → D.host.E := fun j => (Bm : Matrix (Fin N) (Fin N) D.host.E) j a
      have hxe : x = (Bm : Matrix (Fin N) (Fin N) D.host.E) *ᵥ Pi.single a 1 := by
        funext j; simp [x, Matrix.mulVec_single]
      have hrhs : ∃ s : ℕ, ¬ p ∣ s ∧ ∀ c, (s : D.host.E) *
          (((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) *ᵥ x) c ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
        refine ⟨1, hp.not_dvd_one, fun c => ?_⟩
        rw [hxe, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
          Nat.cast_one, one_mul, Pi.single_apply]
        split_ifs
        · exact ⟨1, map_one _⟩
        · exact ⟨0, map_zero _⟩
      obtain ⟨s, hs, hmem⟩ := (hL x).2 hrhs
      have h := hM.2.1 _ hmem b
      rw [hρ] at h
      have e : (fun j => ρ (((s : D.host.E) • x) j)) = ρ (s : D.host.E) • fun j => ρ (x j) := by
        funext j
        change ρ ((s : D.host.E) * x j) = ρ (s : D.host.E) * ρ (x j)
        rw [map_mul]
      rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, norm_mul, hns s hs, one_mul] at h
      convert h using 2
      simp [A, x, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    have hprod : (Ai * M) * (M⁻¹ * A) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc M, Matrix.mul_nonsing_inv _ hMu, Matrix.one_mul, hAiA]
    have hd := congrArg Matrix.det hprod
    rw [Matrix.det_mul, Matrix.det_one] at hd
    have hn := congrArg norm hd
    rw [norm_mul, norm_one] at hn
    have h1 := norm_det_le_one _ hg
    have h2 := norm_det_le_one _ (fun b a => hh b a)
    by_contra hne
    have hlt : ‖(Ai * M).det‖ < 1 := lt_of_le_of_ne h1 hne
    have : ‖(Ai * M).det‖ * ‖(M⁻¹ * A).det‖ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) h2) hlt
    linarith
  · rw [hρ, ← Matrix.mul_assoc]
    change M = A * Ai * M
    rw [hAAi, Matrix.one_mul]

end GlobalTheory.LocBasisBasR
