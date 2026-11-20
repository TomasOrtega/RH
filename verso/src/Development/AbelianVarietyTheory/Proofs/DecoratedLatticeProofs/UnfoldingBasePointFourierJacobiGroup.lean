import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

variable {D : D7}

/- English proof (translation)
Use `show LinearIndependent D.host.E (fun i : Fin ρ => fun k : Fin W.rank => d.e k i)`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Establish `h1 : d.e *ᵥ g = 0`. Use function extensionality and compare the values at `k`.

Use `congrFun hg k` as an intermediate fact. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.zero_apply]`. Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`.

Establish `h2 : (d.e'ᴴ * W.gram * d.e) *ᵥ g = 0` using `by rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]`. Rewrite `h2` using `[d.e'e, Matrix.one_mulVec]`. Introduce `i`. Conclude with `congrFun h2 i`.
-/
theorem linInd_e {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) : LinearIndependent D.host.E d.e.transpose := by
  show LinearIndependent D.host.E (fun i : Fin ρ => fun k : Fin W.rank => d.e k i)
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h1 : d.e *ᵥ g = 0 := by
    funext k
    have := congrFun hg k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← this]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h2 : (d.e'ᴴ * W.gram * d.e) *ᵥ g = 0 := by rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]
  rw [d.e'e, Matrix.one_mulVec] at h2
  intro i; exact congrFun h2 i

/- English proof (translation)
Rewrite using `[gramQ, ← Matrix.mul_assoc]`. Conclude with `d.ee`.
-/
theorem gramQ_e {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) : gramQ W d.e = 0 := by
  rw [gramQ, ← Matrix.mul_assoc]; exact d.ee

/- English proof (translation)
Take `⟨u, -, b, c, rfl⟩` from `((flag_jacobi_structure D W W₀ ρ d).1 n).1 hn`. Rewrite using `[mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.nC_j0, d.nB_j0, Matrix.mul_add, d.wittDecomp_levi_inclAnisotropic, ← Matrix.mul_assoc (mt W (d.levi u)) d.jX, d.levi_jX, Matrix.mul_add, d.p0_j0, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.p0_jX, Matrix.zero_mul, Matrix.zero_m …`.
-/
theorem flagUnipotent_anisotropic_projection_eq_one {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) {n : GA D W} (hn : n ∈ flagN d) :
    d.p0 ⬝ (mt W n ⬝ d.j0) = 1 := by
  obtain ⟨u, -, b, c, rfl⟩ := ((flag_jacobi_structure D W W₀ ρ d).1 n).1 hn
  rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.nC_j0, d.nB_j0, Matrix.mul_add, d.wittDecomp_levi_inclAnisotropic,
    ← Matrix.mul_assoc (mt W (d.levi u)) d.jX, d.levi_jX, Matrix.mul_add, d.p0_j0, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, d.p0_jX, Matrix.zero_mul, Matrix.zero_mul, add_zero]

/- English proof (translation)
Establish `dec` using `flag_jacobi_structure D W W₀ ρ d`. Use extensionality with `r`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, hr⟩`. Establish `hs : d.levi u⁻¹ * r ∈ stabX d` using `by show mt W (d.levi u⁻¹ * r) ⬝ d.jX = d.jX`.

Rewrite using `[mt_mul, Matrix.mul_assoc, show mt W r ⬝ d.jX = d.jX ⬝ u.1 from hr, ← Matrix.mul_assoc, d.levi_jX, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]`. Take `⟨n, hn, h, he⟩` from `(dec.2.2.1 _).1 hs`. Establish `hl : d.levi u ∈ flagN d` using `(dec.1 _).2 ⟨u, hu, 0, 0, by rw [d.nB_zero, d.nC_zero, mul_one, mul_one]⟩`. Use `(dec.2.2.2.1 r).2 ⟨d.levi u * n, mul_mem hl (Subgroup.mem_inf.1 hn).1, h, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc, ← he, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]`.

Introduce `hr`. Take `⟨n, hn, h, rfl⟩` from `(dec.2.2.2.1 r).1 hr`. Take `⟨u, hu, b, c, rfl⟩` from `(dec.1 n).1 hn`. Use `⟨u, hu, ?_⟩` and prove the remaining obligations. Use `show mt W _ ⬝ d.jX = d.jX ⬝ u.1`.

Rewrite using `[mt_mul, mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, d.nC_jX, d.nB_jX, d.levi_jX]`.
-/
theorem Rgrp_eq {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) : Rgrp W (rat d.e) = jacGrp d := by
  have dec := flag_jacobi_structure D W W₀ ρ d
  ext r
  constructor
  · rintro ⟨u, hu, hr⟩
    have hs : d.levi u⁻¹ * r ∈ stabX d := by
      show mt W (d.levi u⁻¹ * r) ⬝ d.jX = d.jX
      rw [mt_mul, Matrix.mul_assoc, show mt W r ⬝ d.jX = d.jX ⬝ u.1 from hr, ← Matrix.mul_assoc, d.levi_jX,
        Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    obtain ⟨n, hn, h, he⟩ := (dec.2.2.1 _).1 hs
    have hl : d.levi u ∈ flagN d := (dec.1 _).2 ⟨u, hu, 0, 0, by rw [d.nB_zero, d.nC_zero, mul_one, mul_one]⟩
    refine (dec.2.2.2.1 r).2 ⟨d.levi u * n, mul_mem hl (Subgroup.mem_inf.1 hn).1, h, ?_⟩
    rw [mul_assoc, ← he, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  · intro hr
    obtain ⟨n, hn, h, rfl⟩ := (dec.2.2.2.1 r).1 hr
    obtain ⟨u, hu, b, c, rfl⟩ := (dec.1 n).1 hn
    refine ⟨u, hu, ?_⟩
    show mt W _ ⬝ d.jX = d.jX ⬝ u.1
    rw [mt_mul, mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, d.nC_jX, d.nB_jX,
      d.levi_jX]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hg`. Establish `hh : h ∈ GQ W₀`. Rewrite `hg`, the goal using `[mem_GQ_iff]`. Establish `e : mt W₀ h = d.p0 ⬝ (mt W (n * d.emb0 h) ⬝ d.j0)`.

Rewrite using `[mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc (mt W n), ← Matrix.mul_assoc, flagUnipotent_anisotropic_projection_eq_one d hn, Matrix.one_mul]`. Rewrite using `[e]`. Conclude with `ratMx_mul (rat_mem _) (ratMx_mul hg (rat_mem _))`. Use `⟨?_, hh⟩` and prove the remaining obligations. Establish `: n = n * d.emb0 h * (d.emb0 h)⁻¹` using `by rw [mul_inv_cancel_right]`.

Rewrite using `[this]`. Conclude with `mul_mem hg (inv_mem (d.wittDecomp_anisotropicEmbedding_mem_rationalPoints hh))`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `mul_mem h1 (d.wittDecomp_anisotropicEmbedding_mem_rationalPoints h2)`.
-/
theorem flagUnipotent_mul_emb_mem_rational_iff {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) {n : GA D W} (hn : n ∈ flagN d) (h : GA D W₀) :
    n * d.emb0 h ∈ GQ W ↔ n ∈ GQ W ∧ h ∈ GQ W₀ := by
  constructor
  · intro hg
    have hh : h ∈ GQ W₀ := by
      rw [mem_GQ_iff] at hg ⊢
      have e : mt W₀ h = d.p0 ⬝ (mt W (n * d.emb0 h) ⬝ d.j0) := by
        rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc (mt W n), ← Matrix.mul_assoc, flagUnipotent_anisotropic_projection_eq_one d hn,
          Matrix.one_mul]
      rw [e]
      exact ratMx_mul (rat_mem _) (ratMx_mul hg (rat_mem _))
    refine ⟨?_, hh⟩
    have : n = n * d.emb0 h * (d.emb0 h)⁻¹ := by rw [mul_inv_cancel_right]
    rw [this]
    exact mul_mem hg (inv_mem (d.wittDecomp_anisotropicEmbedding_mem_rationalPoints hh))
  · rintro ⟨h1, h2⟩
    exact mul_mem h1 (d.wittDecomp_anisotropicEmbedding_mem_rationalPoints h2)

/- English proof (translation)
Introduce `D W W₀ ρ d`. Use `⟨⟨linInd_e d, fun u _ => ?_⟩, gramQ_e d, rfl, Rgrp_eq d, d.continuous_embed, fun n hn h => flagUnipotent_mul_emb_mem_rational_iff d hn h⟩` and prove the remaining obligations. Rewrite using `[gramQ_e d, rat_zero, Matrix.zero_mul, Matrix.mul_zero]`.
-/
theorem base_point : ∀ (D : D7) (W W₀ : HSp D) (ρ : ℕ) (d : HypDec W W₀ ρ), IsBase W d.e ∧ gramQ W d.e = 0 ∧ xZero d = rat d.e ∧ Rgrp W (rat d.e) = jacGrp d ∧ Continuous d.emb0 ∧ ∀ n ∈ flagN d, ∀ h, n * d.emb0 h ∈ GQ W ↔ n ∈ GQ W ∧ h ∈ GQ W₀ := by
  intro D W W₀ ρ d
  refine ⟨⟨linInd_e d, fun u _ => ?_⟩, gramQ_e d, rfl, Rgrp_eq d, d.continuous_embed, fun n hn h => flagUnipotent_mul_emb_mem_rational_iff d hn h⟩
  rw [gramQ_e d, rat_zero, Matrix.zero_mul, Matrix.mul_zero]

end GlobalTheory.Unf
