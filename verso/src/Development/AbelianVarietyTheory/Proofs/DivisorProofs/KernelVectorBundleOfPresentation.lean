import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PresentationExtensionClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreChain
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain)
open GlobalTheory.ChainPts.PullHT (pullA)
open scoped TensorProduct
open GlobalTheory.ChainPts
open GlobalTheory.FrobFilt.ExtPres

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KerVB

/- English proof (translation)
Introduce `O _ _ _ B P₁ P₃ r F j hF ⟨e₃⟩`. Use `mono_ψ P₁` as an intermediate fact. Set `q : P₁.E ⟶ P₁.mod` to `cokernel.π P₁.ψ`. Use `haveI : Epi q := inferInstanceAs (Epi (cokernel.π P₁.ψ))`. Set `c : P₁.mod ⟶ cokernel j` to `cokernel.π j`.

Set `g : P₁.E ⟶ cokernel j` to `q ≫ c`. Use `haveI : Epi g := epi_comp q c`. Take `⟨hK, -⟩` from `kernel_step P₃ e₃ g P₁.vb`. Establish `hψq : P₁.ψ ≫ q = 0` using `cokernel.condition P₁.ψ`. Set `ψ' : P₁.E' ⟶ kernel g` to `kernel.lift g P₁.ψ (by`.

Express the relevant statement in the definitionally equal form `P₁.ψ ≫ q ≫ c = 0`. Rewrite using `[← Category.assoc, hψq, zero_comp])`. Establish `hψ' : ψ' ≫ kernel.ι g = P₁.ψ` using `kernel.lift_ι _ _ _`. Use `haveI : Mono ψ' := by`. Establish `: Mono (ψ' ≫ kernel.ι g)` using `by rw [hψ']; infer_instance`.

Conclude with `mono_of_mono ψ' (kernel.ι g)`. Establish `hkc : (kernel.ι g ≫ q) ≫ c = 0`. Rewrite using `[Category.assoc]`. Conclude with `kernel.condition g`. Set `k' : kernel g ⟶ Abelian.image j` to `kernel.lift (cokernel.π j) (kernel.ι g ≫ q) hkc`.

Establish `hk' : k' ≫ Abelian.image.ι j = kernel.ι g ≫ q` using `kernel.lift_ι _ _ _`. Establish `h0 : ψ' ≫ k' = 0`. Rewrite using `[← cancel_mono (Abelian.image.ι j), Category.assoc, hk', ← Category.assoc, hψ', hψq, zero_comp]`. Establish `hC : (ShortComplex.mk P₁.ψ q hψq).Exact` using `ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel P₁.ψ)`. Set `T : ShortComplex B.X.Modules` to `ShortComplex.mk ψ' k' h0`.

Establish `hT : T.Exact`. Rewrite using `[ShortComplex.exact_iff_exact_up_to_refinements]`. Introduce `A x hx`. Establish `hx' : x ≫ k' = 0` using `hx`. Establish `hxq : (x ≫ kernel.ι g) ≫ q = 0`.

Rewrite using `[Category.assoc, ← hk', ← Category.assoc, hx', zero_comp]`. Take `⟨A', π', hπ', x₁, hx₁⟩` from `hC.exact_up_to_refinements _ hxq`. Use `⟨A', π', hπ', x₁, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `π' ≫ x = x₁ ≫ ψ'`. Rewrite using `[← cancel_mono (kernel.ι g), Category.assoc, Category.assoc, hψ']`.

Conclude with `hx₁`. Use `haveI hk'e : Epi k' := by`. Rewrite using `[epi_iff_surjective_up_to_refinements]`. Introduce `A y`. Take `⟨A', π', hπ', x, hx⟩` from `surjective_up_to_refinements_of_epi q (y ≫ Abelian.image.ι j)`.

Establish `hxg : x ≫ g = 0`. Express the relevant statement in the definitionally equal form `x ≫ q ≫ c = 0`. Rewrite using `[← Category.assoc, ← hx, Category.assoc, Category.assoc]`. Rewrite using `[show Abelian.image.ι j ≫ c = 0 from kernel.condition _, comp_zero, comp_zero]`. Use `⟨A', π', hπ', kernel.lift g x hxg, ?_⟩` and prove the remaining obligations.

Rewrite using `[← cancel_mono (Abelian.image.ι j), Category.assoc, Category.assoc, hk', kernel.lift_ι_assoc, hx]`. Use `haveI : Epi T.g := hk'e`. Set `eI : cokernel ψ' ≅ Abelian.image j` to `IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hT.gIsCokernel`. Set `f : F ⟶ cokernel ψ'` to `Abelian.factorThruImage j ≫ eI.inv`. Use `haveI : Epi f := epi_comp _ _`.

Establish `h1 : GlobalTheory.VB.IsVB (kernel f) r` using `isVB_kernel ψ' f hF hK P₁.vb'`. Establish `e1 : kernel f ≅ kernel (Abelian.factorThruImage j)` using `kernelCompMono _ _`. Establish `e2 : kernel (Abelian.factorThruImage j ≫ Abelian.image.ι j) ≅ kernel (Abelian.factorThruImage j)` using `kernelCompMono _ _`. Establish `e3 : kernel j ≅ kernel (Abelian.factorThruImage j)` using `(kernelIsoOfEq (Abelian.image.fac j).symm) ≪≫ e2`. Conclude with `h1.of_iso (e1 ≪≫ e3.symm)`.
-/
theorem isVB_kernel_of_pres : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B : GlobalTheory.Vert.Model O) (P₁ P₃ : Pres B) (r : ℕ) (F : B.X.Modules) (j : F ⟶ P₁.mod), GlobalTheory.VB.IsVB F r → Nonempty (cokernel j ≅ P₃.mod) → GlobalTheory.VB.IsVB (kernel j) r := by
  intro O _ _ _ B P₁ P₃ r F j hF ⟨e₃⟩
  have := mono_ψ P₁
  let q : P₁.E ⟶ P₁.mod := cokernel.π P₁.ψ
  haveI : Epi q := inferInstanceAs (Epi (cokernel.π P₁.ψ))
  let c : P₁.mod ⟶ cokernel j := cokernel.π j
  let g : P₁.E ⟶ cokernel j := q ≫ c
  haveI : Epi g := epi_comp q c
  obtain ⟨hK, -⟩ := kernel_step P₃ e₃ g P₁.vb
  have hψq : P₁.ψ ≫ q = 0 := cokernel.condition P₁.ψ
  let ψ' : P₁.E' ⟶ kernel g := kernel.lift g P₁.ψ (by
    change P₁.ψ ≫ q ≫ c = 0
    rw [← Category.assoc, hψq, zero_comp])
  have hψ' : ψ' ≫ kernel.ι g = P₁.ψ := kernel.lift_ι _ _ _
  haveI : Mono ψ' := by
    have : Mono (ψ' ≫ kernel.ι g) := by rw [hψ']; infer_instance
    exact mono_of_mono ψ' (kernel.ι g)
  have hkc : (kernel.ι g ≫ q) ≫ c = 0 := by
    rw [Category.assoc]; exact kernel.condition g
  let k' : kernel g ⟶ Abelian.image j := kernel.lift (cokernel.π j) (kernel.ι g ≫ q) hkc
  have hk' : k' ≫ Abelian.image.ι j = kernel.ι g ≫ q := kernel.lift_ι _ _ _
  have h0 : ψ' ≫ k' = 0 := by
    rw [← cancel_mono (Abelian.image.ι j), Category.assoc, hk', ← Category.assoc, hψ', hψq, zero_comp]
  have hC : (ShortComplex.mk P₁.ψ q hψq).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel P₁.ψ)
  let T : ShortComplex B.X.Modules := ShortComplex.mk ψ' k' h0
  have hT : T.Exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro A x hx
    have hx' : x ≫ k' = 0 := hx
    have hxq : (x ≫ kernel.ι g) ≫ q = 0 := by
      rw [Category.assoc, ← hk', ← Category.assoc, hx', zero_comp]
    obtain ⟨A', π', hπ', x₁, hx₁⟩ := hC.exact_up_to_refinements _ hxq
    refine ⟨A', π', hπ', x₁, ?_⟩
    change π' ≫ x = x₁ ≫ ψ'
    rw [← cancel_mono (kernel.ι g), Category.assoc, Category.assoc, hψ']
    exact hx₁
  haveI hk'e : Epi k' := by
    rw [epi_iff_surjective_up_to_refinements]
    intro A y
    obtain ⟨A', π', hπ', x, hx⟩ := surjective_up_to_refinements_of_epi q (y ≫ Abelian.image.ι j)
    have hxg : x ≫ g = 0 := by
      change x ≫ q ≫ c = 0
      rw [← Category.assoc, ← hx, Category.assoc, Category.assoc]
      rw [show Abelian.image.ι j ≫ c = 0 from kernel.condition _, comp_zero, comp_zero]
    refine ⟨A', π', hπ', kernel.lift g x hxg, ?_⟩
    rw [← cancel_mono (Abelian.image.ι j), Category.assoc, Category.assoc, hk', kernel.lift_ι_assoc, hx]
  haveI : Epi T.g := hk'e
  let eI : cokernel ψ' ≅ Abelian.image j :=
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hT.gIsCokernel
  let f : F ⟶ cokernel ψ' := Abelian.factorThruImage j ≫ eI.inv
  haveI : Epi f := epi_comp _ _
  have h1 : GlobalTheory.VB.IsVB (kernel f) r := isVB_kernel ψ' f hF hK P₁.vb'
  have e1 : kernel f ≅ kernel (Abelian.factorThruImage j) := kernelCompMono _ _
  have e2 : kernel (Abelian.factorThruImage j ≫ Abelian.image.ι j) ≅ kernel (Abelian.factorThruImage j) :=
    kernelCompMono _ _
  have e3 : kernel j ≅ kernel (Abelian.factorThruImage j) :=
    (kernelIsoOfEq (Abelian.image.fac j).symm) ≪≫ e2
  exact h1.of_iso (e1 ≪≫ e3.symm)

end GlobalTheory.KerVB
