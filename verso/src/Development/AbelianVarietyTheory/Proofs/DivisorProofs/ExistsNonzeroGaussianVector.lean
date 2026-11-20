import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesInsertZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchrodingerMapExistsOfArchHeisenbergDerivaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivatiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLawsStatement

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv

namespace GlobalTheory.FockVacuum

/- English proof (translation)
Introduce `h`. Set `l : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] ℂ` to `MvPolynomial.lcoeff ℂ 0`. Set `m : MultilinearMap ℂ (fun _ : ι => Formalism.BasicNotions.TH.Pol P Q R S) ℂ` to `(MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap (fun _ => l)`. Establish `h1` using `congrArg (PiTensorProduct.lift m) h`. Rewrite `h1` using `[PiTensorProduct.lift.tprod, map_zero]`.

Simplify using `[m, l] at h1`.
-/
theorem tprod_one_ne_zero (ι : Type) [Fintype ι] (P Q R S : ℕ) :
    (PiTensorProduct.tprod ℂ (fun _ : ι => (1 : Formalism.BasicNotions.TH.Pol P Q R S))) ≠ 0 := by
  intro h
  let l : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] ℂ := MvPolynomial.lcoeff ℂ 0
  let m : MultilinearMap ℂ (fun _ : ι => Formalism.BasicNotions.TH.Pol P Q R S) ℂ :=
    (MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap (fun _ => l)
  have h1 := congrArg (PiTensorProduct.lift m) h
  rw [PiTensorProduct.lift.tprod, map_zero] at h1
  simp [m, l] at h1

/- English proof (translation)
Introduce `r _ x`. Simplify using `[GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Model.heisLine, Darboux.rho, schr]`. Conclude with `hasDerivAt_const _ _`.
-/
theorem actsD_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    ActsD (evI F) (M.heisLine ψ u) (⇑(0 : SInf F (Fin n × Fin d))) (⇑(0 : SInf F (Fin n × Fin d))) := by
  intro r _ x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Model.heisLine, Darboux.rho, schr]
  exact hasDerivAt_const _ _

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d r s r' s' X W M hB hX hW hD hL`. Use `choose A hA hAθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists _ _ _ _ _ (hX.sig w) (hX.cartan w)`. Use `choose C hC hCθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists _ _ _ _ _ (hW.sig w) (hW.cartan w)`. Establish `fr : GlobalTheory.RealLift.Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C`. Use `⟨one_mul _, fun w => ?_, fun w => ?_⟩` and prove the remaining obligations.

Rewrite using `[incM_map_piInf_emb, one_smul]`. Conclude with `hA w`. Rewrite using `[incM_map_piInf_emb]`. Conclude with `hC w`. Take `⟨Φ, hΦ⟩` from `GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hD F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C hB.cm hB.std fr`.

Establish `hr` using `GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws hL hD (GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hD) F E σ n d _ _ _ _ X W M B.ψ B.emb A C Φ hB.cm hB.std fr hAθ hCθ hΦ`. Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Establish `hbot : M.Pol B.ψ B.emb = ⊥`. Use `eq_bot_iff.2 (sInf_le ⟨fun f₀ hf₀ => ?_, fun u _ f hf f₁ hf₁ => ?_⟩)` and prove the remaining obligations.

Rewrite using `[Submodule.mem_bot]`. Assume the negation of the conclusion as `h`. Conclude with `hno f₀ h hf₀`. Rewrite `hf`, the goal using `[Submodule.mem_bot]`. Substitute `hf` using the available equality.

Conclude with `(hL F _ 0 f₁ 0).2.2.1 _ hf₁ (actsD_zero M B.ψ u)`. Establish `hmem : Φ (PiTensorProduct.tprod ℂ fun _ => 1) ∈ M.Pol B.ψ B.emb` using `hr ▸ LinearMap.mem_range_self Φ _`. Rewrite `hmem` using `[hbot, Submodule.mem_bot]`. Conclude with `tprod_one_ne_zero _ _ _ _ _ (hΦ.1 (hmem.trans (map_zero Φ).symm))`.
-/
theorem exists_ne_zero_isGauss : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W), B.IsGood σ → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.ActsLaws →
    ∃ f₀ : SInf F (Fin n × Fin d), f₀ ≠ 0 ∧ M.IsGauss B.ψ B.emb f₀ := by
  intro F E _ _ _ _ _ σ B n d r s r' s' X W M hB hX hW hD hL
  choose A hA hAθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists _ _ _ _ _ (hX.sig w) (hX.cartan w)
  choose C hC hCθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists _ _ _ _ _ (hW.sig w) (hW.cartan w)
  have fr : GlobalTheory.RealLift.Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := by
    refine ⟨one_mul _, fun w => ?_, fun w => ?_⟩
    · rw [incM_map_piInf_emb, one_smul]; exact hA w
    · rw [incM_map_piInf_emb]; exact hC w
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hD F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C hB.cm hB.std fr
  have hr := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws hL hD (GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hD) F E σ n d _ _ _ _ X W M B.ψ B.emb A C Φ hB.cm hB.std fr hAθ hCθ hΦ
  by_contra hno
  push_neg at hno
  have hbot : M.Pol B.ψ B.emb = ⊥ := by
    refine eq_bot_iff.2 (sInf_le ⟨fun f₀ hf₀ => ?_, fun u _ f hf f₁ hf₁ => ?_⟩)
    · rw [Submodule.mem_bot]
      by_contra h
      exact hno f₀ h hf₀
    · rw [Submodule.mem_bot] at hf ⊢
      subst hf
      exact (hL F _ 0 f₁ 0).2.2.1 _ hf₁ (actsD_zero M B.ψ u)
  have hmem : Φ (PiTensorProduct.tprod ℂ fun _ => 1) ∈ M.Pol B.ψ B.emb := hr ▸ LinearMap.mem_range_self Φ _
  rw [hbot, Submodule.mem_bot] at hmem
  exact tprod_one_ne_zero _ _ _ _ _ (hΦ.1 (hmem.trans (map_zero Φ).symm))

end GlobalTheory.FockVacuum
