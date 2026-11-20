import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.JacNeZero
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CJDefs
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.FiniteDimensionalTranslationCoordinates

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Grp

variable {n : ℕ} (G : Grp k n)

/- English proof (translation)
Introduce `L V _ _ π hs hirr hy`. Take `⟨hsm, hfl⟩` from `hjF L V π hs hirr`. Take `⟨X, _, _, σ, hσs, hσi, hsq, hση⟩` from `hsub _ (jacU G.e π) hsm hfl hy`. Take `⟨Y, _, _, τ, hτs, hτi, hτd, ⟨eqv⟩⟩` from `hten L X σ hσs hσi hση`. Use `hsupp L V π hs hirr Y τ hτs hτi hτd ?_` and prove the remaining obligations.

Take `⟨S, f, hf⟩` from `hsq`. Conclude with `⟨S, (eqv.toIntertwiningMap).comp f, eqv.toLinearEquiv.surjective.comp hf⟩`.
-/
theorem jacProd_of (hjF : G.JacquetModuleFiniteProp) (hsub : G.SubquotientProp) (hten : G.TensorProductProp) (hsupp : G.SupportOfProductProp) :
    G.JacquetProductProp := by
  intro L V _ _ π hs hirr hy
  obtain ⟨hsm, hfl⟩ := hjF L V π hs hirr
  obtain ⟨X, _, _, σ, hσs, hσi, hsq, hση⟩ := hsub _ (jacU G.e π) hsm hfl hy
  obtain ⟨Y, _, _, τ, hτs, hτi, hτd, ⟨eqv⟩⟩ := hten L X σ hσs hσi hση
  refine hsupp L V π hs hirr Y τ hτs hτi hτd ?_
  obtain ⟨S, f, hf⟩ := hsq
  exact ⟨S, (eqv.toIntertwiningMap).comp f, eqv.toLinearEquiv.surjective.comp hf⟩

end Grp

def CSteps : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    Grp.CompactConductorBasicProp (k := k) ∧ Grp.UniformizerProp (k := k) ∧ Grp.ExistsGroupElementProp (k := k) ∧ ∀ (n : ℕ) (G : Grp k n),
    G.CompactConductorBoundProp ∧ G.JacquetOneProp ∧ G.JacquetMultiplicativeProp ∧ G.JacquetInverseProp ∧ G.CompactOpenKernelProp ∧ G.ModulusOnUnitsProp ∧ G.ModulusMultiplicativeProp ∧
    G.LambdaMultiplicativeProp ∧ G.LambdaBasicProp ∧ G.LambdaUnipotentProp ∧ G.IwahoriDecompositionProp ∧ G.FixedSubspaceStableProp ∧ G.FixedSubspaceFiniteProp ∧ G.NonzeroLeviEigenvectorExists ∧
    G.ParabolicJacquetProp ∧ G.AnnihilationProp ∧ G.NonIntegralProp ∧ G.TorusCentreEigenProp ∧ G.TorusPowerProp ∧ G.JacquetKernelProp ∧ G.TorusCentreInjectiveProp ∧
    G.JacquetImageProp ∧ G.JacquetModuleFiniteProp ∧ G.SubquotientProp ∧ G.TensorProductProp ∧ G.SupportOfProductProp

open UpperTheory.NonzeroTypeTheory in

/- English proof (translation)
Introduce `k _ _ _ _ n G V _ _ ρ hs hi hx`. Take `⟨hcb, hun, -, hG⟩` from `hC k`. Take `⟨hccB, hJone, hJmul, hJinv, hKC, hΔU, hΔM, hlM, hlB, hlU, hiw, -, -, -, hPJ, hkill, hni, hTE, hTp, hjK, hTI, hjI, hjF, hsub, hten, hsupp⟩` from `hG n G`. Conclude with `G.cMain hcb hccB hJone hJmul hJinv hKC hΔU hΔM hlM hlB hlU hiw hPJ hkill hni hTE hTp hjK hTI hun hlL hjI (G.jacProd_of hjF hsub hten hsupp) L V ρ hs hi hx`.
-/
theorem need_CMain (hC : CSteps) (hlL : LeviSubgroupRestriction) (L : GlobalTheory.Mem.LiteralAutomorphy.LitN) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (G : Grp k n)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V), IsSmooth ρ → ρ.IsIrreducible →
    (∃ x : V, x ≠ 0 ∧ ∀ g ∈ G.JSet, ρ g x = G.lam g • x) → IsTwSphProd ρ G.d G.hd G.μ := by
  intro k _ _ _ _ n G V _ _ ρ hs hi hx
  obtain ⟨hcb, hun, -, hG⟩ := hC k
  obtain ⟨hccB, hJone, hJmul, hJinv, hKC, hΔU, hΔM, hlM, hlB, hlU, hiw, -, -, -, hPJ, hkill, hni, hTE, hTp, hjK, hTI,
    hjI, hjF, hsub, hten, hsupp⟩ := hG n G
  exact G.cMain hcb hccB hJone hJmul hJinv hKC hΔU hΔM hlM hlB hlU hiw hPJ hkill hni hTE hTp hjK hTI hun hlL hjI
    (G.jacProd_of hjF hsub hten hsupp) L V ρ hs hi hx

open UpperTheory.NonzeroTypeTheory in

/- English proof (translation)
Introduce `k _ _ _ _ n G`. Take `⟨hcb, -, -, hG⟩` from `hC k`. Take `⟨hccB, hJone, hJmul, hJinv, hKC, hΔU, hΔM, hlM, hlB, -, -, hV0s, hV0f, hv0, -⟩` from `hG n G`. Establish `hK` using `hKC hccB G.lev`. Establish `hlB'` using `hlB hccB`.

Establish `hlM'` using `hlM hcb hΔU hΔM hccB`. Take `⟨h1, h2, h3⟩` from `hv0 hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC`. Use `⟨fun g hg => hg.1, hJone.1, fun g hg g' hg' => ⟨hJmul hcb hccB g hg g' hg', hlM' g hg g' hg'⟩, hJinv hcb hccB, fun g _ => hlB'.2.1 g, hK.2.2.1, ?_, hK.2.2.2.2 le_rfl, hlB'.2.2, fun φ hφ k' => hV0s hccB hKC k' φ hφ, hV0f hccB hKC, h1, h2, h3⟩` and prove the remaining obligations. Rewrite using `[← hK.1]`. Conclude with `(KCg k n G.lev).one_mem`.
-/
theorem need_CProps (hC : CSteps) : Need_CProps := by
  intro k _ _ _ _ n G
  obtain ⟨hcb, -, -, hG⟩ := hC k
  obtain ⟨hccB, hJone, hJmul, hJinv, hKC, hΔU, hΔM, hlM, hlB, -, -, hV0s, hV0f, hv0, -⟩ := hG n G
  have hK := hKC hccB G.lev
  have hlB' := hlB hccB
  have hlM' := hlM hcb hΔU hΔM hccB
  obtain ⟨h1, h2, h3⟩ := hv0 hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC
  refine ⟨fun g hg => hg.1, hJone.1, fun g hg g' hg' => ⟨hJmul hcb hccB g hg g' hg', hlM' g hg g' hg'⟩, hJinv hcb hccB,
    fun g _ => hlB'.2.1 g, hK.2.2.1, ?_, hK.2.2.2.2 le_rfl, hlB'.2.2, fun φ hφ k' => hV0s hccB hKC k' φ hφ, hV0f hccB hKC, h1, h2, h3⟩
  rw [← hK.1]
  exact (KCg k n G.lev).one_mem

open UpperTheory.NonzeroTypeTheory in

/- English proof (translation)
Introduce `k _ _ _ _ n μ hμ`. Take `⟨-, -, hex, -⟩` from `hC k`. Take `⟨G, σ, h⟩` from `hex n μ hμ`. Conclude with `⟨G, σ, fun i => (h i).symm⟩`.
-/
theorem need_Grp (hC : CSteps) : Need_Grp := by
  intro k _ _ _ _ n μ hμ
  obtain ⟨-, -, hex, -⟩ := hC k
  obtain ⟨G, σ, h⟩ := hex n μ hμ
  exact ⟨G, σ, fun i => (h i).symm⟩

end UpperTheory.TNZ
