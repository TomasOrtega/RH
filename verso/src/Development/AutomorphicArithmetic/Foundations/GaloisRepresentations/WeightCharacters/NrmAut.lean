import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMatrixCoeffInfinitePlacesWeightRep
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

/- English proof (translation)
Introduce `hC E _ _ _ a τ C hCl n hn p hp`. Take `⟨hpc, A, hAf, hA⟩` from `hp`. Set `S : Submodule ℂ (UA E a → ℂ)` to `A.map (LinearMap.funLeft ℂ ℂ n)`. Establish `hSf : FiniteDimensional ℂ S` using `inferInstance`. Establish `hS : ∀ y, (fun g => p (n g * y)) ∈ S` using `fun y => ⟨_, hA y, rfl⟩`.

Use `⟨fun y => ?_, S, hSf, hS⟩` and prove the remaining obligations. Use `hC E a C hCl _ (fun γ hγ g => by simp only [hn.left γ hγ g]) (fun c hc g => by simp only [hn.lev c hc g]) (fun g => ?_) S hSf (fun x hx => ?_)` and prove the remaining obligations. Establish `he : (fun x : infU E a => p (n (g * x.1) * y)) = fun x : infU E a => p (n g * (cEmb τ x.1 * y))`. Use function extensionality and compare the values at `x`. Rewrite using `[hn.inf x.1 x.2 g, mul_assoc]`.

Rewrite using `[he]`. Conclude with `hpc.comp (continuous_const.mul (((GlobalTheory.AutRec.continuous_cEmb_emb τ).comp continuous_subtype_val).mul continuous_const))`. Establish `he : RU E a x (fun g => p (n g * y)) = fun g => p (n g * (cEmb τ x * y))`. Use function extensionality and compare the values at `g`. Express the relevant statement in the definitionally equal form `p (n (g * x) * y) = _`.

Rewrite using `[hn.inf x hx g, mul_assoc]`. Rewrite using `[he]`. Conclude with `hS _`.
-/
theorem UpperTheory.Gal.Wt.nrmAut_of :
    UpperTheory.Gal.Wt.AutCrit → UpperTheory.Gal.Wt.NrmAut := by
  intro hC E _ _ _ a τ C hCl n hn p hp
  obtain ⟨hpc, A, hAf, hA⟩ := hp
  let S : Submodule ℂ (UA E a → ℂ) := A.map (LinearMap.funLeft ℂ ℂ n)
  have hSf : FiniteDimensional ℂ S := inferInstance
  have hS : ∀ y, (fun g => p (n g * y)) ∈ S := fun y => ⟨_, hA y, rfl⟩
  refine ⟨fun y => ?_, S, hSf, hS⟩
  refine hC E a C hCl _ (fun γ hγ g => by simp only [hn.left γ hγ g])
    (fun c hc g => by simp only [hn.lev c hc g]) (fun g => ?_) S hSf (fun x hx => ?_)
  · have he : (fun x : infU E a => p (n (g * x.1) * y)) =
        fun x : infU E a => p (n g * (cEmb τ x.1 * y)) := by
      funext x
      rw [hn.inf x.1 x.2 g, mul_assoc]
    rw [he]
    exact hpc.comp (continuous_const.mul
      (((GlobalTheory.AutRec.continuous_cEmb_emb τ).comp continuous_subtype_val).mul continuous_const))
  · have he : RU E a x (fun g => p (n g * y)) = fun g => p (n g * (cEmb τ x * y)) := by
      funext g
      change p (n (g * x) * y) = _
      rw [hn.inf x hx g, mul_assoc]
    rw [he]
    exact hS _
