import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.BesSemi

variable {D : D7}

/- English proof (translation)
Establish `h : (embA d o : GA D A → GA D S) = fun h => d.emb0 (o.emb (h, 1))` using `funext fun h => embA_apply d o h`. Rewrite using `[h]`. Conclude with `d.continuous_embed.comp (o.continuous_emb.comp (continuous_id.prodMk continuous_const))`.
-/
theorem continuous_embA {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) :
    Continuous (embA d o) := by
  have h : (embA d o : GA D A → GA D S) = fun h => d.emb0 (o.emb (h, 1)) := funext fun h => embA_apply d o h
  rw [h]
  exact d.continuous_embed.comp (o.continuous_emb.comp (continuous_id.prodMk continuous_const))

/- English proof (translation)
Rewrite `e` using `[embA_apply, embA_apply]`. Take `⟨h1, h2⟩` from `GlobalTheory.MixPer.Decomp.flag_unipotent_mul_embedded_anisotropic_unique d hn hn' e`. Conclude with `⟨h1, congrArg Prod.fst (o.emb_injective h2)⟩`.
-/
theorem unique {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) {n n' : GA D S}
    (hn : n ∈ flagN d) (hn' : n' ∈ flagN d) {h h' : GA D A} (e : n * embA d o h = n' * embA d o h') :
    n = n' ∧ h = h' := by
  rw [embA_apply, embA_apply] at e
  obtain ⟨h1, h2⟩ := GlobalTheory.MixPer.Decomp.flag_unipotent_mul_embedded_anisotropic_unique d hn hn' e
  exact ⟨h1, congrArg Prod.fst (o.emb_injective h2)⟩

/- English proof (translation)
Rewrite using `[mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic]`. Conclude with `GlobalTheory.MixPer.Decomp.witt_anisotropic_projection_flag_unipotent_inclusion d hn (mt S₀ k)`.
-/
theorem besselCompression_unipotent_mul_embedding {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {n : GA D S} (hn : n ∈ flagN d) (k : GA D S₀) :
    d.p0 ⬝ (mt S (n * d.emb0 k) ⬝ d.j0) = mt S₀ k := by
  rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic]
  exact GlobalTheory.MixPer.Decomp.witt_anisotropic_projection_flag_unipotent_inclusion d hn (mt S₀ k)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hg`. Establish `hk : o.emb (h, 1) ∈ GQ S₀`. Rewrite using `[mem_GQ_iff]`. Rewrite `hg` using `[embA_apply]`.

Rewrite using `[← besselCompression_unipotent_mul_embedding d hn]`. Conclude with `ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff S _).1 hg) (rat_mem _))`. Establish `hA : h ∈ GQ A`. Rewrite using `[mem_GQ_iff]`. Establish `e : o.pA ⬝ (mt S₀ (o.emb (h, 1)) ⬝ o.jA) = mt A h`.

Rewrite using `[o.emb_jA, ← Matrix.mul_assoc, o.pA_jA, Matrix.one_mul]`. Rewrite using `[← e]`. Conclude with `ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff S₀ _).1 hk) (rat_mem _))`. Establish `he : embA d o h ∈ GQ S` using `by rw [embA_apply]; exact d.wittDecomp_anisotropicEmbedding_mem_rationalPoints hk`. Use `⟨?_, hA⟩` and prove the remaining obligations.

Establish `: n = n * embA d o h * (embA d o h)⁻¹` using `(mul_inv_cancel_right n _).symm`. Rewrite using `[this]`. Conclude with `mul_mem hg (inv_mem he)`. Introduce and unpack `⟨hn', hA⟩`. Use `mul_mem hn' ?_` and prove the remaining obligations.

Rewrite using `[embA_apply]`. Conclude with `d.wittDecomp_anisotropicEmbedding_mem_rationalPoints (o.emb_mem_GQ hA (one_mem _))`.
-/
theorem rat_iff {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) {n : GA D S}
    (hn : n ∈ flagN d) (h : GA D A) : n * embA d o h ∈ GQ S ↔ n ∈ GQ S ∧ h ∈ GQ A := by
  constructor
  · intro hg
    have hk : o.emb (h, 1) ∈ GQ S₀ := by
      rw [mem_GQ_iff]
      rw [embA_apply] at hg
      rw [← besselCompression_unipotent_mul_embedding d hn]
      exact ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff S _).1 hg) (rat_mem _))
    have hA : h ∈ GQ A := by
      rw [mem_GQ_iff]
      have e : o.pA ⬝ (mt S₀ (o.emb (h, 1)) ⬝ o.jA) = mt A h := by
        rw [o.emb_jA, ← Matrix.mul_assoc, o.pA_jA, Matrix.one_mul]
      rw [← e]
      exact ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff S₀ _).1 hk) (rat_mem _))
    have he : embA d o h ∈ GQ S := by rw [embA_apply]; exact d.wittDecomp_anisotropicEmbedding_mem_rationalPoints hk
    refine ⟨?_, hA⟩
    have : n = n * embA d o h * (embA d o h)⁻¹ := (mul_inv_cancel_right n _).symm
    rw [this]
    exact mul_mem hg (inv_mem he)
  · rintro ⟨hn', hA⟩
    refine mul_mem hn' ?_
    rw [embA_apply]
    exact d.wittDecomp_anisotropicEmbedding_mem_rationalPoints (o.emb_mem_GQ hA (one_mem _))

end GlobalTheory.Unf.BesSemi

namespace GlobalTheory.Unf

/- English proof (translation)
Introduce `D σ B`. Use `⟨BesSemi.continuous_embA B.d B.o, GlobalTheory.Mem.TrueRecord.isClosed_NFlag B.V (isIsoSub_e B.d), fun n hn h => ?_, fun n hn n' hn' h h' e => BesSemi.unique B.d B.o hn hn' e, fun n hn h => BesSemi.rat_iff B.d B.o hn h⟩` and prove the remaining obligations. Rewrite using `[embA_apply]`. Conclude with `GlobalTheory.MixPer.Decomp.conj_mem B.d hn _`.
-/
theorem besSemi : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), Continuous (embA B.d B.o) ∧ IsClosed (flagN B.d : Set (GA D B.V)) ∧ (∀ n ∈ flagN B.d, ∀ h, embA B.d B.o h * n * (embA B.d B.o h)⁻¹ ∈ flagN B.d) ∧ (∀ n ∈ flagN B.d, ∀ n' ∈ flagN B.d, ∀ h h', n * embA B.d B.o h = n' * embA B.d B.o h' → n = n' ∧ h = h') ∧ ∀ n ∈ flagN B.d, ∀ h, n * embA B.d B.o h ∈ GQ B.V ↔ n ∈ GQ B.V ∧ h ∈ GQ B.A := by
  intro D σ B
  refine ⟨BesSemi.continuous_embA B.d B.o, GlobalTheory.Mem.TrueRecord.isClosed_NFlag B.V (isIsoSub_e B.d),
    fun n hn h => ?_, fun n hn n' hn' h h' e => BesSemi.unique B.d B.o hn hn' e,
    fun n hn h => BesSemi.rat_iff B.d B.o hn h⟩
  rw [embA_apply]
  exact GlobalTheory.MixPer.Decomp.conj_mem B.d hn _

end GlobalTheory.Unf
