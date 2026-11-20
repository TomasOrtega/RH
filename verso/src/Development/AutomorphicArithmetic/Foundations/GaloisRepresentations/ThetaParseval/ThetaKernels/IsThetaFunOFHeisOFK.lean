import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.HeisThetaF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
section Alg
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {xi0 : E}
end Alg
section Parts
end Parts
section Top
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {xi0 : E}
end Top
section Fin
end Fin
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB nS nT JS JT ξ₀ w₀ f hf`. Establish `hψ : Continuous B.ψ` using `hB.std.1`. Use `haveI := isTopologicalRing_AEF (F := F) (E := E)`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `γ w`.

Simplify using `only [heisOF]`. Rewrite using `[add_assoc, hf.quasi, symplOHF_add_left, symplOHF_add_right, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]`. Use `congr 2`. Normalize the expressions using the abelian group laws. Take `⟨U, hU, hUf⟩` from `hf.level`.

Take `⟨K, hK⟩` from `exists_openAddSubgroup_psi_fin B.ψ hψ`. Set `φ : WOF F E nS nT →+ AF F` to `{ toFun := fun u => symplOHF σ JS JT ξ₀ u w₀ - symplOHF σ JS JT ξ₀ w₀ u map_zero' := by simp only [symplOHF_zero_left, symplOHF_zero_right, sub_zero] map_add' := fun u v => by simp only [symplOHF_add_left, symplOHF_add_right]; abel }`. Establish `hφ : Continuous φ` using `(continuous_symplOHF_left w₀).sub (continuous_symplOHF_right w₀)`. Set `ρ : WOF F E nS nT →+ Af F` to `(sndA F).toRingHom.toAddMonoidHom.comp φ`. Establish `hρ : Continuous ρ` using `continuous_snd.comp hφ`.

Use `⟨U ⊓ K.toAddSubgroup.comap ρ, hU.inter (K.isOpen.preimage hρ), fun u hu h0 => ?_⟩` and prove the remaining obligations. Establish `h1 : pairA F 1 0 • u = 0` using `smul_eq_zero_of_map_infPartF h0`. Establish `hfst : fstA F (φ u) = 0`. Rewrite using `[← fstA_mul_idem]`. Use `show fstA F (pairA F 1 0 * (symplOHF σ JS JT ξ₀ u w₀ - symplOHF σ JS JT ξ₀ w₀ u)) = 0`.

Rewrite using `[mul_sub, ← symplOHF_smul_left, ← symplOHF_smul_right, h1, symplOHF_zero_left, symplOHF_zero_right, sub_zero, map_zero]`. Establish `hφu : φ u = pairA F 0 (ρ u)` using `Prod.ext hfst rfl`. Establish `hone : B.ψ (φ u) = 1` using `by rw [hφu]; exact hK _ hu.2`. Establish `hswap : B.ψ (symplOHF σ JS JT ξ₀ u w₀) = B.ψ (symplOHF σ JS JT ξ₀ w₀ u)`. Establish `: symplOHF σ JS JT ξ₀ u w₀ = φ u + symplOHF σ JS JT ξ₀ w₀ u` using `by show _ = (symplOHF σ JS JT ξ₀ u w₀ - symplOHF σ JS JT ξ₀ w₀ u) + _`.

Normalize the expressions using the abelian group laws. Rewrite using `[this, AddChar.map_add_eq_mul, hone, one_mul]`. Use function extensionality and compare the values at `w`. Establish `hw` using `congrFun (hUf u hu.1 h0) (w + w₀)`. Simplify using `only [heisOF] at hw ⊢`.

Rewrite using `[← hw, add_right_comm w u w₀, symplOHF_add_left w u w₀, symplOHF_add_left w w₀ u, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hswap]`. Expand and normalize the polynomial expressions, which then agree. Use `show Continuous fun w => B.ψ (symplOHF σ JS JT ξ₀ w w₀) * f (w + w₀)`. Conclude with `(hψ.comp (continuous_symplOHF_left w₀)).mul (hf.cont.comp (continuous_id.add continuous_const))`. Introduce `k L hL h0 w`.

Set `φ₁ : WOF F E nS nT →+ AF F` to `{ toFun := fun u => symplOHF σ JS JT ξ₀ u w₀ map_zero' := symplOHF_zero_left w₀ map_add' := fun u v => symplOHF_add_left u v w₀ }`. Set `ev : AF F →+ ℝ` to `(Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).toAddMonoidHom.comp ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toAddEquiv.toAddMonoidHom.comp (fstA F).toRingHom.toAddMonoidHom)`. Establish `hev : Continuous ev` using `(LinearMap.continuous_of_finiteDimensional (Algebra.trace ℝ (mixedEmbedding.mixedSpace F))).comp ((continuous_ringEquiv_mixedSpace F).comp continuous_fst)`. Set `g : (Fin k → ℝ) →+ ℝ` to `ev.comp (φ₁.comp L)`. Establish `hg : Continuous g` using `hev.comp ((continuous_symplOHF_left w₀).comp hL)`.

Set `gL` to `g.toRealLinearMap hg`. Establish `hval : ∀ t, B.ψ (symplOHF σ JS JT ξ₀ (L t) w₀) = Complex.exp (-(2 * Real.pi * Complex.I) * ((gL t : ℝ) : ℂ))`. Introduce `t`. Establish `hfin : sndA F (symplOHF σ JS JT ξ₀ (L t) w₀) = 0`. Establish `h1 : pairA F 0 1 • L t = 0` using `smul_eq_zero_of_map_finPartF (h0 t)`.

Rewrite using `[← sndA_mul_idem, ← symplOHF_smul_left, h1, symplOHF_zero_left, map_zero]`. Rewrite using `[hB.std.2.2 _ ?_]`. Both sides reduce to the same expression. Introduce `v hv`. Establish `hv1 : v.1 = 0` using `(InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.mp hv`.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show v.1 * (symplOHF σ JS JT ξ₀ (L t) w₀).1 = 0`. Rewrite using `[hv1, zero_mul]`. Use `show v.2 * (symplOHF σ JS JT ξ₀ (L t) w₀).2 = 0`. Rewrite using `[show (symplOHF σ JS JT ξ₀ (L t) w₀).2 = 0 from hfin, mul_zero]`.

Establish `hfun : (fun t => heisOF σ JS JT ξ₀ B.ψ w₀ f (w + L t)) = fun t => B.ψ (symplOHF σ JS JT ξ₀ w w₀) * Complex.exp (-(2 * Real.pi * Complex.I) * ((gL t : ℝ) : ℂ)) * f (w + w₀ + L t)`. Use function extensionality and compare the values at `t`. Simplify using `only [heisOF]`. Rewrite using `[symplOHF_add_left, AddChar.map_add_eq_mul, hval, add_right_comm]`. Rewrite using `[hfun]`.

Use `(contDiff_const.mul ?_).mul (hf.smooth k L hL h0 (w + w₀))` and prove the remaining obligations. Conclude with `(contDiff_const.mul (Complex.ofRealCLM.contDiff.comp gL.contDiff)).cexp`.
-/
theorem isThetaFunOF_heisOF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
      (w₀ : WOF F E nS nT) (f : WOF F E nS nT → ℂ), IsThetaFunOF σ JS JT ξ₀ B.ψ f →
        IsThetaFunOF σ JS JT ξ₀ B.ψ (heisOF σ JS JT ξ₀ B.ψ w₀ f) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT ξ₀ w₀ f hf
  have hψ : Continuous B.ψ := hB.std.1
  haveI := isTopologicalRing_AEF (F := F) (E := E)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro γ w
    simp only [heisOF]
    rw [add_assoc, hf.quasi, symplOHF_add_left, symplOHF_add_right, ← mul_assoc, ← mul_assoc,
      ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 2
    abel
  · obtain ⟨U, hU, hUf⟩ := hf.level
    obtain ⟨K, hK⟩ := exists_openAddSubgroup_psi_fin B.ψ hψ
    let φ : WOF F E nS nT →+ AF F :=
      { toFun := fun u => symplOHF σ JS JT ξ₀ u w₀ - symplOHF σ JS JT ξ₀ w₀ u
        map_zero' := by simp only [symplOHF_zero_left, symplOHF_zero_right, sub_zero]
        map_add' := fun u v => by simp only [symplOHF_add_left, symplOHF_add_right]; abel }
    have hφ : Continuous φ := (continuous_symplOHF_left w₀).sub (continuous_symplOHF_right w₀)
    let ρ : WOF F E nS nT →+ Af F := (sndA F).toRingHom.toAddMonoidHom.comp φ
    have hρ : Continuous ρ := continuous_snd.comp hφ
    refine ⟨U ⊓ K.toAddSubgroup.comap ρ, hU.inter (K.isOpen.preimage hρ), fun u hu h0 => ?_⟩
    have h1 : pairA F 1 0 • u = 0 := smul_eq_zero_of_map_infPartF h0
    have hfst : fstA F (φ u) = 0 := by
      rw [← fstA_mul_idem]
      show fstA F (pairA F 1 0 * (symplOHF σ JS JT ξ₀ u w₀ - symplOHF σ JS JT ξ₀ w₀ u)) = 0
      rw [mul_sub, ← symplOHF_smul_left, ← symplOHF_smul_right, h1, symplOHF_zero_left, symplOHF_zero_right,
        sub_zero, map_zero]
    have hφu : φ u = pairA F 0 (ρ u) := Prod.ext hfst rfl
    have hone : B.ψ (φ u) = 1 := by rw [hφu]; exact hK _ hu.2
    have hswap : B.ψ (symplOHF σ JS JT ξ₀ u w₀) = B.ψ (symplOHF σ JS JT ξ₀ w₀ u) := by
      have : symplOHF σ JS JT ξ₀ u w₀ = φ u + symplOHF σ JS JT ξ₀ w₀ u := by
        show _ = (symplOHF σ JS JT ξ₀ u w₀ - symplOHF σ JS JT ξ₀ w₀ u) + _
        abel
      rw [this, AddChar.map_add_eq_mul, hone, one_mul]
    funext w
    have hw := congrFun (hUf u hu.1 h0) (w + w₀)
    simp only [heisOF] at hw ⊢
    rw [← hw, add_right_comm w u w₀, symplOHF_add_left w u w₀, symplOHF_add_left w w₀ u, AddChar.map_add_eq_mul,
      AddChar.map_add_eq_mul, hswap]
    ring
  · show Continuous fun w => B.ψ (symplOHF σ JS JT ξ₀ w w₀) * f (w + w₀)
    exact (hψ.comp (continuous_symplOHF_left w₀)).mul (hf.cont.comp (continuous_id.add continuous_const))
  · intro k L hL h0 w
    let φ₁ : WOF F E nS nT →+ AF F :=
      { toFun := fun u => symplOHF σ JS JT ξ₀ u w₀
        map_zero' := symplOHF_zero_left w₀
        map_add' := fun u v => symplOHF_add_left u v w₀ }
    let ev : AF F →+ ℝ :=
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).toAddMonoidHom.comp
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toAddEquiv.toAddMonoidHom.comp (fstA F).toRingHom.toAddMonoidHom)
    have hev : Continuous ev :=
      (LinearMap.continuous_of_finiteDimensional (Algebra.trace ℝ (mixedEmbedding.mixedSpace F))).comp
        ((continuous_ringEquiv_mixedSpace F).comp continuous_fst)
    let g : (Fin k → ℝ) →+ ℝ := ev.comp (φ₁.comp L)
    have hg : Continuous g := hev.comp ((continuous_symplOHF_left w₀).comp hL)
    let gL := g.toRealLinearMap hg
    have hval : ∀ t, B.ψ (symplOHF σ JS JT ξ₀ (L t) w₀) =
        Complex.exp (-(2 * Real.pi * Complex.I) * ((gL t : ℝ) : ℂ)) := by
      intro t
      have hfin : sndA F (symplOHF σ JS JT ξ₀ (L t) w₀) = 0 := by
        have h1 : pairA F 0 1 • L t = 0 := smul_eq_zero_of_map_finPartF (h0 t)
        rw [← sndA_mul_idem, ← symplOHF_smul_left, h1, symplOHF_zero_left, map_zero]
      rw [hB.std.2.2 _ ?_]
      · rfl
      · intro v hv
        have hv1 : v.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.mp hv
        refine Prod.ext ?_ ?_
        · show v.1 * (symplOHF σ JS JT ξ₀ (L t) w₀).1 = 0
          rw [hv1, zero_mul]
        · show v.2 * (symplOHF σ JS JT ξ₀ (L t) w₀).2 = 0
          rw [show (symplOHF σ JS JT ξ₀ (L t) w₀).2 = 0 from hfin, mul_zero]
    have hfun : (fun t => heisOF σ JS JT ξ₀ B.ψ w₀ f (w + L t)) = fun t =>
        B.ψ (symplOHF σ JS JT ξ₀ w w₀) * Complex.exp (-(2 * Real.pi * Complex.I) * ((gL t : ℝ) : ℂ)) *
          f (w + w₀ + L t) := by
      funext t
      simp only [heisOF]
      rw [symplOHF_add_left, AddChar.map_add_eq_mul, hval, add_right_comm]
    rw [hfun]
    refine (contDiff_const.mul ?_).mul (hf.smooth k L hL h0 (w + w₀))
    exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp gL.contDiff)).cexp
end GlobalTheory.HeisThetaF
end
end
