import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceTensorRatFiniteAlgebraModuleTopology

noncomputable section

open IsDedekindDomain GlobalTheory.LKTrip
open scoped TensorProduct

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Use `letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)`. Use `haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (Qv v ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (Qv v) _`. Use `set b := basV G v`. Establish `hc : Continuous b.equivFun.symm` using `IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap`.

Establish `hbox : IsCompact (Set.univ.pi fun _ : Fin (Module.finrank ℚ G.C) ↦ (v.1.adicCompletionIntegers ℚ : Set (Qv v)))` using `isCompact_univ_pi fun _ ↦ LevelExists.isCompact_intCompl v.1`. Establish `hset : {y | IsIntV G v y} = b.equivFun.symm '' (Set.univ.pi fun _ ↦ (v.1.adicCompletionIntegers ℚ : Set (Qv v)))`. Rewrite using `[LinearEquiv.image_symm_eq_preimage]`. Use extensionality with `y`. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ_pi, Module.Basis.equivFun_apply]`.

Both sides reduce to the same expression. Rewrite using `[hset]`. Conclude with `hbox.image hc`.
-/
theorem isCompact_isIntV (G : HTGroup p) (v : AwayP p) :
    @IsCompact _ (moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)) {y | IsIntV G v y} := by
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (Qv v ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (Qv v) _
  set b := basV G v
  have hc : Continuous b.equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap
  have hbox : IsCompact (Set.univ.pi fun _ : Fin (Module.finrank ℚ G.C) ↦
      (v.1.adicCompletionIntegers ℚ : Set (Qv v))) :=
    isCompact_univ_pi fun _ ↦ LevelExists.isCompact_intCompl v.1
  have hset : {y | IsIntV G v y} = b.equivFun.symm '' (Set.univ.pi fun _ ↦
      (v.1.adicCompletionIntegers ℚ : Set (Qv v))) := by
    rw [LinearEquiv.image_symm_eq_preimage]
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ_pi, Module.Basis.equivFun_apply]
    rfl
  rw [hset]
  exact hbox.image hc

/- English proof (translation)
Introduce `p _ G v`. Use `letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)`. Use `haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (Qv v ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (Qv v) _`. Use `haveI : T2Space (Qv v ⊗[ℚ] G.C) := LevelExists.t2Space_tensor_rat_finite_algebra_moduleTopology (Qv v) G.C`.

Establish `hPc` using `isCompact_isIntV G v`. Establish `hOc` using `LevelExists.isCompact_intCompl v.1`. Use `set P : Set (Qv v ⊗[ℚ] G.C) := {y | IsIntV G v y}`. Use `set O : Set (Qv v) := (v.1.adicCompletionIntegers ℚ : Set (Qv v))`. Establish `hσ : Continuous (fun y : Qv v ⊗[ℚ] G.C ↦ (starT G.star (Qv v) y).unop)`.

Set `σl : (Qv v ⊗[ℚ] G.C) →ₗ[Qv v] (Qv v ⊗[ℚ] G.C)` to `{ toFun := fun y ↦ (starT G.star (Qv v) y).unop map_add' := fun x y ↦ by simp only [map_add, MulOpposite.unop_add] map_smul' := by`. Introduce `r x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a y`.

Simplify using `only [TensorProduct.smul_tmul', smul_eq_mul, starT_tmul, RingHom.id_apply]`. Consider the case `add x y hx hy => simp only [smul_add, map_add, MulOpposite.unop_add, hx, hy, RingHom.id_apply] }`. Conclude with `IsModuleTopology.continuous_of_linearMap σl`. Establish `hj : Continuous (algebraMap (Qv v) (Qv v ⊗[ℚ] G.C))` using `IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (Qv v) (Qv v ⊗[ℚ] G.C))`. Establish `hGcl : IsClosed (UPts G.star (Qv v) : Set ((Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ))`.

Apply `isClosed_eq` to reduce the goal to its premises. Conclude with `(Units.continuous_val.comp continuous_fst).mul (hσ.comp (Units.continuous_val.comp continuous_fst))`. Conclude with `hj.comp (Units.continuous_val.comp continuous_snd)`. Set `g : Gv G v → ((Qv v ⊗[ℚ] G.C) × (Qv v ⊗[ℚ] G.C)ᵐᵒᵖ) × (Qv v × (Qv v)ᵐᵒᵖ)` to `fun x ↦ (Units.embedProduct _ x.1.1, Units.embedProduct _ x.1.2)`. Establish `hg : Topology.IsClosedEmbedding g` using `(Units.isClosedEmbedding_embedProduct.prodMap Units.isClosedEmbedding_embedProduct).comp hGcl.isClosedEmbedding_subtypeVal`.

Set `K` to `(P ×ˢ (MulOpposite.opHomeomorph.symm ⁻¹' P)) ×ˢ (O ×ˢ (MulOpposite.opHomeomorph.symm ⁻¹' O))`. Establish `hKC : IntV G v = g ⁻¹' K`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, h3, h4⟩`.

Conclude with `⟨⟨h1, h2⟩, h3, h4⟩`. Introduce and unpack `⟨⟨h1, h2⟩, h3, h4⟩`. Conclude with `⟨h1, h2, h3, h4⟩`. Rewrite using `[hKC]`. Conclude with `hg.isCompact_preimage ((hPc.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hPc)).prod (hOc.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hOc)))`.
-/
theorem isCompact_IntV : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), IsCompact (IntV G v) := by
  intro p _ G v
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (Qv v ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (Qv v) _
  haveI : T2Space (Qv v ⊗[ℚ] G.C) := LevelExists.t2Space_tensor_rat_finite_algebra_moduleTopology (Qv v) G.C
  have hPc := isCompact_isIntV G v
  have hOc := LevelExists.isCompact_intCompl v.1
  set P : Set (Qv v ⊗[ℚ] G.C) := {y | IsIntV G v y}
  set O : Set (Qv v) := (v.1.adicCompletionIntegers ℚ : Set (Qv v))
  have hσ : Continuous (fun y : Qv v ⊗[ℚ] G.C ↦ (starT G.star (Qv v) y).unop) := by
    let σl : (Qv v ⊗[ℚ] G.C) →ₗ[Qv v] (Qv v ⊗[ℚ] G.C) :=
      { toFun := fun y ↦ (starT G.star (Qv v) y).unop
        map_add' := fun x y ↦ by simp only [map_add, MulOpposite.unop_add]
        map_smul' := by
          intro r x
          induction x using TensorProduct.induction_on with
          | zero => simp
          | tmul a y =>
            simp only [TensorProduct.smul_tmul', smul_eq_mul, starT_tmul, RingHom.id_apply]
          | add x y hx hy => simp only [smul_add, map_add, MulOpposite.unop_add, hx, hy, RingHom.id_apply] }
    exact IsModuleTopology.continuous_of_linearMap σl
  have hj : Continuous (algebraMap (Qv v) (Qv v ⊗[ℚ] G.C)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (Qv v) (Qv v ⊗[ℚ] G.C))
  have hGcl : IsClosed (UPts G.star (Qv v) : Set ((Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ)) := by
    apply isClosed_eq
    · exact (Units.continuous_val.comp continuous_fst).mul
        (hσ.comp (Units.continuous_val.comp continuous_fst))
    · exact hj.comp (Units.continuous_val.comp continuous_snd)
  let g : Gv G v → ((Qv v ⊗[ℚ] G.C) × (Qv v ⊗[ℚ] G.C)ᵐᵒᵖ) × (Qv v × (Qv v)ᵐᵒᵖ) :=
    fun x ↦ (Units.embedProduct _ x.1.1, Units.embedProduct _ x.1.2)
  have hg : Topology.IsClosedEmbedding g :=
    (Units.isClosedEmbedding_embedProduct.prodMap Units.isClosedEmbedding_embedProduct).comp
      hGcl.isClosedEmbedding_subtypeVal
  let K := (P ×ˢ (MulOpposite.opHomeomorph.symm ⁻¹' P)) ×ˢ (O ×ˢ (MulOpposite.opHomeomorph.symm ⁻¹' O))
  have hKC : IntV G v = g ⁻¹' K := by
    ext x
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2⟩, h3, h4⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h1, h2, h3, h4⟩
  rw [hKC]
  exact hg.isCompact_preimage ((hPc.prod
    (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hPc)).prod
    (hOc.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hOc)))

end GlobalTheory.OrbFinAf
