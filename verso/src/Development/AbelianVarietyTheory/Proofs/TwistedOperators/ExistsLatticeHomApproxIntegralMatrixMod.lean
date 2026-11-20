import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHatMxHomLatIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FunObj.HatFrame

section General

open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P Formalism.L2.DIV GlobalTheory.NormSum.AdLattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m n : ℕ}

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => Formalism.L2.Herm.intAf F E
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

/- English proof (translation)
Introduce `w hw`. Proceed by induction on `hw using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨α, hα, x, hx, rfl⟩` from `hw`. Establish `hα' : (1 : E) ⊗ₜ[F] α ∈ 𝒮` using `Subring.subset_closure (Or.inr ⟨⟨α, hα⟩, rfl⟩)`.

Take `⟨q, hr⟩` from `cmpS_surj (F := F) I hI (Ideal.Quotient.mk _ ⟨_, hα'⟩)`. Take `⟨r, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Establish `hr' : oToS F E r - ⟨_, hα'⟩ ∈ idS F I`. Rewrite using `[← Ideal.Quotient.eq]`. Rewrite using `[← hr]`.

Both sides reduce to the same expression. Use `⟨r • x, H.smul_mem r hx, ?_⟩` and prove the remaining obligations. Establish `e : (r • x).map ι - (Matrix.of fun i j => x i j ⊗ₜ[F] α : Matrix (Fin m) (Fin n) 𝒜) = ((oToS F E r - ⟨_, hα'⟩ : 𝒮) : 𝒜) • x.map ι`. Use extensionality with `i j`. Use `show ((algebraMap (𝓞 E) E r * x i j) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) - x i j ⊗ₜ[F] α = ((algebraMap (𝓞 E) E r ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) - ((1 : E) ⊗ₜ[F] α)) * (x i j ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F))`.

Rewrite using `[sub_mul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_one]`. Rewrite using `[e]`. Conclude with `smul_mem_frGrp β β' hr' (fun i j => frame_int hβ hβ' (hH x hx) i j)`. Consider the case `zero => exact ⟨0, zero_mem _, by rw [Matrix.map_zero _ (map_zero _), sub_zero]; exact zero_mem _⟩`. Consider the case `add a b _ _ ha hb`.

Take `⟨x, hx, hxa⟩` from `ha`. Take `⟨y, hy, hyb⟩` from `hb`. Use `⟨x + y, add_mem hx hy, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.map_add _ (map_add _), add_sub_add_comm]`. Conclude with `add_mem hxa hyb`.

Consider the case `neg a _ ha`. Take `⟨x, hx, hxa⟩` from `ha`. Use `⟨-x, neg_mem hx, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.map_neg _ (map_neg _), neg_sub_neg, ← neg_sub]`. Conclude with `neg_mem hxa`.
-/
theorem approx_of_mem_genGrp {Λ : Submodule (𝓞 E) (Fin n → E)} {Λ' : Submodule (𝓞 E) (Fin m → E)}
    {β : GL (Fin n) 𝒜} {β' : GL (Fin m) 𝒜} (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ')
    {H : Submodule (𝓞 E) (Matrix (Fin m) (Fin n) E)} (hH : ∀ x ∈ H, ∀ y ∈ Λ, x *ᵥ y ∈ Λ')
    (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) :
    ∀ w ∈ genGrp F H, ∃ x₀ ∈ H, x₀.map ι - w ∈ frGrp β β' (idS F I) := by
  intro w hw
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hw
    have hα' : (1 : E) ⊗ₜ[F] α ∈ 𝒮 := Subring.subset_closure (Or.inr ⟨⟨α, hα⟩, rfl⟩)
    obtain ⟨q, hr⟩ := cmpS_surj (F := F) I hI (Ideal.Quotient.mk _ ⟨_, hα'⟩)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    have hr' : oToS F E r - ⟨_, hα'⟩ ∈ idS F I := by
      rw [← Ideal.Quotient.eq]
      rw [← hr]
      rfl
    refine ⟨r • x, H.smul_mem r hx, ?_⟩
    have e : (r • x).map ι - (Matrix.of fun i j => x i j ⊗ₜ[F] α : Matrix (Fin m) (Fin n) 𝒜) =
        ((oToS F E r - ⟨_, hα'⟩ : 𝒮) : 𝒜) • x.map ι := by
      ext i j
      show ((algebraMap (𝓞 E) E r * x i j) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) - x i j ⊗ₜ[F] α =
        ((algebraMap (𝓞 E) E r ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) - ((1 : E) ⊗ₜ[F] α)) *
          (x i j ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F))
      rw [sub_mul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_one]
    rw [e]
    exact smul_mem_frGrp β β' hr' (fun i j => frame_int hβ hβ' (hH x hx) i j)
  | zero => exact ⟨0, zero_mem _, by rw [Matrix.map_zero _ (map_zero _), sub_zero]; exact zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨x, hx, hxa⟩ := ha
    obtain ⟨y, hy, hyb⟩ := hb
    refine ⟨x + y, add_mem hx hy, ?_⟩
    rw [Matrix.map_add _ (map_add _), add_sub_add_comm]
    exact add_mem hxa hyb
  | neg a _ ha =>
    obtain ⟨x, hx, hxa⟩ := ha
    refine ⟨-x, neg_mem hx, ?_⟩
    rw [Matrix.map_neg _ (map_neg _), neg_sub_neg, ← neg_sub]
    exact neg_mem hxa

/- English proof (translation)
Use `set Nc : Matrix (Fin m) (Fin n) 𝒜 := Matrix.of fun i j => (N i j : 𝒜) with hNc`. Use `set z : Matrix (Fin m) (Fin n) 𝒜 := HMul.hMul (HMul.hMul β'.val Nc) (β⁻¹).val with hz`. Establish `hfr : HMul.hMul (HMul.hMul (β'⁻¹).val z) β.val = Nc`. Rewrite using `[hz, Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]`. Establish `hz1 : z ∈ frGrp β β' (idS F ⊤)`.

Introduce `i j`. Use `⟨N i j, by rw [idS, Ideal.map_top]; trivial, ?_⟩` and prove the remaining obligations. Rewrite using `[hfr]`. Both sides reduce to the same expression. Establish `hz2` using `frGrp_le_genGrp hβ hβ' hH' ⊤ hz1`.

Rewrite `hz2` using `[Submodule.top_smul]`. Take `⟨x₀, hx₀, hd⟩` from `approx_of_mem_genGrp hβ hβ' hH I hI z hz2`. Use `⟨x₀, hx₀, fun i j => ?_⟩` and prove the remaining obligations. Take `⟨s, hs, e⟩` from `hd i j`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations.

Rewrite using `[e, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply, hfr]`. Both sides reduce to the same expression.
-/
theorem approx_general {Λ : Submodule (𝓞 E) (Fin n → E)} {Λ' : Submodule (𝓞 E) (Fin m → E)}
    {β : GL (Fin n) 𝒜} {β' : GL (Fin m) 𝒜} (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ')
    {H : Submodule (𝓞 E) (Matrix (Fin m) (Fin n) E)} (hH : ∀ x ∈ H, ∀ y ∈ Λ, x *ᵥ y ∈ Λ')
    (hH' : ∀ x, (∀ y ∈ Λ, x *ᵥ y ∈ Λ') → x ∈ H) (I : Ideal (𝓞 E)) (hI : I ≠ ⊥)
    (N : Matrix (Fin m) (Fin n) 𝒮) :
    ∃ x₀ ∈ H, ∀ i j, ∃ s ∈ idS F I,
      (s : 𝒜) = HMul.hMul (HMul.hMul (β'⁻¹).val (x₀.map ι)) β.val i j - (N i j : 𝒜) := by
  set Nc : Matrix (Fin m) (Fin n) 𝒜 := Matrix.of fun i j => (N i j : 𝒜) with hNc
  set z : Matrix (Fin m) (Fin n) 𝒜 := HMul.hMul (HMul.hMul β'.val Nc) (β⁻¹).val with hz
  have hfr : HMul.hMul (HMul.hMul (β'⁻¹).val z) β.val = Nc := by
    rw [hz, Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul]
  have hz1 : z ∈ frGrp β β' (idS F ⊤) := by
    intro i j
    refine ⟨N i j, by rw [idS, Ideal.map_top]; trivial, ?_⟩
    rw [hfr]
    rfl
  have hz2 := frGrp_le_genGrp hβ hβ' hH' ⊤ hz1
  rw [Submodule.top_smul] at hz2
  obtain ⟨x₀, hx₀, hd⟩ := approx_of_mem_genGrp hβ hβ' hH I hI z hz2
  refine ⟨x₀, hx₀, fun i j => ?_⟩
  obtain ⟨s, hs, e⟩ := hd i j
  refine ⟨s, hs, ?_⟩
  rw [e, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply, hfr]
  rfl

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D m n Λ Λ' β β' hβ hβ' I hI N`. Conclude with `approx_general hβ hβ' (H := GlobalTheory.ChiGrid.homLat Λ Λ') (fun _ hx => hx) (fun _ hx => hx) I hI N`.
-/
theorem homLat_approx_mod : ∀ {D : D7} {m n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)) (β : GL (Fin n) (EAf D)) (β' : GL (Fin m) (EAf D)), Formalism.L2.DIV.IsFrame β Λ → Formalism.L2.DIV.IsFrame β' Λ' → ∀ (I : Ideal (𝓞 D.host.E)), I ≠ ⊥ → ∀ (N : Matrix (Fin m) (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)), ∃ x₀ ∈ GlobalTheory.ChiGrid.homLat Λ Λ', ∀ i j, ∃ s ∈ Formalism.L2.DIV.idS D.host.F I, (s : EAf D) = HMul.hMul (HMul.hMul (β'⁻¹).val (x₀.map (eToEAf D))) β.val i j - (N i j : EAf D) := by
  intro D m n Λ Λ' β β' hβ hβ' I hI N
  exact approx_general hβ hβ' (H := GlobalTheory.ChiGrid.homLat Λ Λ') (fun _ hx => hx) (fun _ hx => hx) I hI N

end GlobalTheory.FunObj.HatFrame

end
