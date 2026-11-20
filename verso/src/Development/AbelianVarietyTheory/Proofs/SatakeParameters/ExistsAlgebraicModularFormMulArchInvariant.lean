import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
open GlobalTheory.DefU

namespace GlobalTheory.AlgMul

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem RU_mul (x : UA E n) (a b : UA E n → ℂ) : RU E n x (a * b) = RU E n x a * RU E n x b := rfl

/- English proof (translation)
Set `St : Subgroup (finU E n)` to `{ carrier := {k | RU E n k ψ = ψ} mul_mem' := fun {a b} ha hb => by`. Express the relevant statement in the definitionally equal form `RU E n ((a : UA E n) * b) ψ = ψ`. Rewrite using `[← RU_RU]`. Express the relevant statement in the definitionally equal form `RU E n a (RU E n b ψ) = ψ`. Rewrite using `[hb]`.

Conclude with `ha`. Use the proof step `one_mem' := by`. Express the relevant statement in the definitionally equal form `RU E n ((1 : finU E n) : UA E n) ψ = ψ`. Simplify using the standard rewrite rules. Use the proof step `inv_mem' := fun {a} ha => by`.

Express the relevant statement in the definitionally equal form `RU E n ((a : UA E n)⁻¹) ψ = ψ`. Use `conv_lhs => rw [← (show RU E n (a : UA E n) ψ = ψ from ha)]`. Rewrite using `[RU_RU, inv_mul_cancel, map_one, Module.End.one_apply] }`. Establish `: (St : Set (finU E n)) ∈ nhds (1 : finU E n)` using `Filter.mem_of_superset (hU.mem_nhds h1) hs`. Conclude with `Subgroup.isOpen_of_mem_nhds St this`.
-/
theorem isOpen_fix_of {ψ : UA E n → ℂ} (U : Set (finU E n)) (hU : IsOpen U) (h1 : (1 : finU E n) ∈ U)
    (hs : ∀ k ∈ U, RU E n k ψ = ψ) : IsOpen {k : finU E n | RU E n k ψ = ψ} := by
  let St : Subgroup (finU E n) :=
    { carrier := {k | RU E n k ψ = ψ}
      mul_mem' := fun {a b} ha hb => by
        change RU E n ((a : UA E n) * b) ψ = ψ
        rw [← RU_RU]
        change RU E n a (RU E n b ψ) = ψ
        rw [hb]; exact ha
      one_mem' := by
        change RU E n ((1 : finU E n) : UA E n) ψ = ψ
        simp
      inv_mem' := fun {a} ha => by
        change RU E n ((a : UA E n)⁻¹) ψ = ψ
        conv_lhs => rw [← (show RU E n (a : UA E n) ψ = ψ from ha)]
        rw [RU_RU, inv_mul_cancel, map_one, Module.End.one_apply] }
  have : (St : Set (finU E n)) ∈ nhds (1 : finU E n) :=
    Filter.mem_of_superset (hU.mem_nhds h1) hs
  exact Subgroup.isOpen_of_mem_nhds St this

/- English proof (translation)
Use `⟨he.cont.mul hφ.cont, fun γ hγ g => ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.mul_apply, he.left γ hγ g, hφ.left γ hγ g]`. Use `isOpen_fix_of _ (he.level.inter hφ.level) ⟨by simp, by simp⟩ ?_` and prove the remaining obligations. Introduce and unpack `k ⟨hk1, hk2⟩`. Rewrite using `[RU_mul, show RU E n k e = e from hk1, show RU E n k φ = φ from hk2]`.

Use `hφ.kfin` as an intermediate fact. Use `Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)).map (LinearMap.mulLeft ℂ e)) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Use `⟨RU E n k φ, Submodule.subset_span ⟨k, rfl⟩, ?_⟩` and prove the remaining obligations. Use `show e * RU E n k φ = RU E n k (e * φ)`.

Rewrite using `[RU_mul]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Conclude with `(hinv g k k.2).symm`.
-/
theorem isAutFormU_mul {e φ : UA E n → ℂ} (he : IsAutFormU e) (hinv : ∀ g, ∀ x ∈ infU E n, e (g * x) = e g)
    (hφ : IsAutFormU φ) : IsAutFormU (e * φ) := by
  refine ⟨he.cont.mul hφ.cont, fun γ hγ g => ?_, ?_, ?_⟩
  · simp only [Pi.mul_apply, he.left γ hγ g, hφ.left γ hγ g]
  · refine isOpen_fix_of _ (he.level.inter hφ.level) ⟨by simp, by simp⟩ ?_
    rintro k ⟨hk1, hk2⟩
    rw [RU_mul, show RU E n k e = e from hk1, show RU E n k φ = φ from hk2]
  · have := hφ.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)).map (LinearMap.mulLeft ℂ e))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    refine ⟨RU E n k φ, Submodule.subset_span ⟨k, rfl⟩, ?_⟩
    show e * RU E n k φ = RU E n k (e * φ)
    rw [RU_mul]
    congr 1
    funext g
    exact (hinv g k k.2).symm

end GlobalTheory.AlgMul

/- English proof (translation)
Introduce `E _ _ _ n W f e he hinv`. Establish `hmem : (LinearMap.mulLeft ℂ e).comp f.1 ∈ algForms W`. Use `⟨fun v => GlobalTheory.AlgMul.isAutFormU_mul he hinv (f.2.1 v), fun x v => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `e * f.1 (W.rep x v) = RU E n x (e * f.1 v)`. Rewrite using `[f.2.2 x v, GlobalTheory.AlgMul.RU_mul]`.

Use `congr 1`. Use function extensionality and compare the values at `g`. Conclude with `(hinv g x x.2).symm`. Conclude with `⟨⟨_, hmem⟩, fun v g => rfl⟩`.
-/
theorem GlobalTheory.AlgMul.exists_mul_algForms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Wt E n) (f : algForms W) (e : UA E n → ℂ), IsAutFormU e → (∀ g, ∀ x ∈ infU E n, e (g * x) = e g) → ∃ f' : algForms W, ∀ v g, f'.1 v g = e g * f.1 v g := by
  intro E _ _ _ n W f e he hinv
  have hmem : (LinearMap.mulLeft ℂ e).comp f.1 ∈ algForms W := by
    refine ⟨fun v => GlobalTheory.AlgMul.isAutFormU_mul he hinv (f.2.1 v), fun x v => ?_⟩
    change e * f.1 (W.rep x v) = RU E n x (e * f.1 v)
    rw [f.2.2 x v, GlobalTheory.AlgMul.RU_mul]
    congr 1
    funext g
    exact (hinv g x x.2).symm
  exact ⟨⟨_, hmem⟩, fun v g => rfl⟩
