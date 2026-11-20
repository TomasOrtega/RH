import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBijectionRightInverseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenSurjectiveExtendsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenInjectiveExtendsStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.InvTame

open Filter
open scoped Classical

/- English proof (translation)
Introduce `_ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e hE hbij A hA g hg`. Take `⟨m, c, φ, hφ, hstd, rfl⟩` from `GlobalTheory.MixEvAdm.sb_decomp F (Fin n × Fin d) g hg`. Take `⟨ei, ev, -, hev, hloc⟩` from `hE.loc`. Establish `hbi : Function.Bijective ei` using `⟨GlobalTheory.T.weil_eigen_injective_extends F E σ B n d X W M M₁ hP.good e hbij.injOn ei ev (fun v => (hev v).1) hloc, GlobalTheory.T.weil_eigen_surjective_extends F E σ B n d X W M M₁ hP.good hM₁ e hbij.surjOn ei ev hev hloc⟩`. Take `⟨S, hS⟩` from `GlobalTheory.T.schwartz_bijection_right_inverse _ _ ei hbi`.

Establish `hpre : ∀ j v, ∃ ψ ∈ SB (Fin n × Fin d → Fv F v), ev v ψ = φ j v ∧ (φ j v = M₁.vac v → ψ = M.vac v)`. Introduce `j v`. Distinguish the cases in `h : φ j v = M₁.vac v`. Conclude with `⟨M.vac v, (hP.good.vac v).1, (hev v).1.trans h.symm, fun _ => rfl⟩`. Establish `h2 : φ j v ∈ (SB (Fin n × Fin d → Fv F v)).map (ev v)` using `(hev v).2.symm ▸ hφ j v`.

Take `⟨ψ, hψ, hψe⟩` from `Submodule.mem_map.1 h2`. Conclude with `⟨ψ, hψ, hψe, fun h' => (h h').elim⟩`. Use `choose ψ hψSB hψev hψvac using hpre`. Establish `hψfam : ∀ j, ∀ᶠ v in cofinite, ψ j v = M.vac v` using `fun j => ((hstd j).and hM₁.std).mono fun v hv => hψvac j v (hv.1.trans hv.2.symm)`. Establish `hψstd : ∀ j, ∀ᶠ v in cofinite, ψ j v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1` using `fun j => ((hψfam j).and hP.good.std).mono fun v hv => hv.1.trans hv.2`.

Establish `hG : ∀ j, (fun y : Fin n × Fin d → Af F => ∏ᶠ v, ψ j v fun i => evalV F v (y i)) ∈ SB (Fin n × Fin d → Af F)` using `fun j => ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ (hψSB j) (hψstd j), GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ (hψSB j) (hψstd j)⟩`. Use `⟨Fin m, inferInstance, fun j => c j • S, fun j y => ∏ᶠ v, ψ j v fun i => evalV F v (y i), hG, fun f => ?_⟩` and prove the remaining obligations. Establish `hsplit : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) (∑ j, c j • fun y => ∏ᶠ v, φ j v fun i => evalV F v (y i)) = ∑ j, c j • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j)`. Use function extensionality and compare the values at `x`. Simplify using `only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm]`. Both sides reduce to the same expression. Establish `hφe : ∀ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j) = e (pureA F ((S f : SInf F _) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) (fun y => ∏ᶠ v, ψ j v fun i => evalV F v (y i)))`. Introduce `j`.

Establish `h1` using `hloc (S f) (ψ j) (hψSB j) (hψfam j)`. Rewrite `h1` using `[hS]`. Establish `h2 : (fun v => ev v (ψ j v)) = φ j` using `funext fun v => hψev j v`. Rewrite `h1` using `[h2]`. Conclude with `h1.symm`.

Rewrite using `[hsplit, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hφe j, hA _ (Submodule.subset_span ⟨S f, _, hG j, rfl⟩)]`. Use function extensionality and compare the values at `x`. Simplify using `[pureA, mul_assoc]`.
-/
theorem isTame_inv : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ A : Fn F n d →ₗ[ℂ] Fn F n d, (∀ Φ ∈ schA F (Fin n × Fin d), A (e Φ) = Φ) → IsTame F A := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e hE hbij A hA g hg
  obtain ⟨m, c, φ, hφ, hstd, rfl⟩ := GlobalTheory.MixEvAdm.sb_decomp F (Fin n × Fin d) g hg
  obtain ⟨ei, ev, -, hev, hloc⟩ := hE.loc
  have hbi : Function.Bijective ei :=
    ⟨GlobalTheory.T.weil_eigen_injective_extends F E σ B n d X W M M₁ hP.good e hbij.injOn ei ev (fun v => (hev v).1) hloc,
      GlobalTheory.T.weil_eigen_surjective_extends F E σ B n d X W M M₁ hP.good hM₁ e hbij.surjOn ei ev hev hloc⟩
  obtain ⟨S, hS⟩ := GlobalTheory.T.schwartz_bijection_right_inverse _ _ ei hbi
  have hpre : ∀ j v, ∃ ψ ∈ SB (Fin n × Fin d → Fv F v), ev v ψ = φ j v ∧ (φ j v = M₁.vac v → ψ = M.vac v) := by
    intro j v
    by_cases h : φ j v = M₁.vac v
    · exact ⟨M.vac v, (hP.good.vac v).1, (hev v).1.trans h.symm, fun _ => rfl⟩
    · have h2 : φ j v ∈ (SB (Fin n × Fin d → Fv F v)).map (ev v) := (hev v).2.symm ▸ hφ j v
      obtain ⟨ψ, hψ, hψe⟩ := Submodule.mem_map.1 h2
      exact ⟨ψ, hψ, hψe, fun h' => (h h').elim⟩
  choose ψ hψSB hψev hψvac using hpre
  have hψfam : ∀ j, ∀ᶠ v in cofinite, ψ j v = M.vac v := fun j =>
    ((hstd j).and hM₁.std).mono fun v hv => hψvac j v (hv.1.trans hv.2.symm)
  have hψstd : ∀ j, ∀ᶠ v in cofinite,
      ψ j v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := fun j =>
    ((hψfam j).and hP.good.std).mono fun v hv => hv.1.trans hv.2
  have hG : ∀ j, (fun y : Fin n × Fin d → Af F => ∏ᶠ v, ψ j v fun i => evalV F v (y i)) ∈
      SB (Fin n × Fin d → Af F) := fun j =>
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ (hψSB j) (hψstd j),
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ (hψSB j) (hψstd j)⟩
  refine ⟨Fin m, inferInstance, fun j => c j • S, fun j y => ∏ᶠ v, ψ j v fun i => evalV F v (y i), hG, fun f => ?_⟩
  have hsplit : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
      (∑ j, c j • fun y => ∏ᶠ v, φ j v fun i => evalV F v (y i)) =
      ∑ j, c j • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j) := by
    funext x
    simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_left_comm]
    rfl
  have hφe : ∀ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j) =
      e (pureA F ((S f : SInf F _) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
        (fun y => ∏ᶠ v, ψ j v fun i => evalV F v (y i))) := by
    intro j
    have h1 := hloc (S f) (ψ j) (hψSB j) (hψfam j)
    rw [hS] at h1
    have h2 : (fun v => ev v (ψ j v)) = φ j := funext fun v => hψev j v
    rw [h2] at h1
    exact h1.symm
  rw [hsplit, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, hφe j, hA _ (Submodule.subset_span ⟨S f, _, hG j, rfl⟩)]
  funext x
  simp [pureA, mul_assoc]

end GlobalTheory.InvTame
