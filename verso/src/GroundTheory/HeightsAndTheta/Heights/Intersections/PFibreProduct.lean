import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreProduct
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

/- English proof (translation)
Use `MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)` and prove the remaining obligations. Simplify using `[T.multiConeMap]`. Break down `p with ⟨_ | _ | _, i⟩` into its components or cases. Simplify using `[T.multiConeMap, T.yyEmb, T.wwCoord, T.yyCoord, diagonalBlockIndex]`. Simplify using `[T.multiConeMap, T.yyEmb, T.wwCoord, T.yyCoord, diagonalBlockIndex]`.

Apply the tactic sequence `fin_cases j <;> simp [T.multiConeMap, T.yyEmb, T.wwCoord, T.yyCoord, diagonalBlockIndex]`.
-/
theorem multiConeMap_ww_comp_yyEmb {Ω : Type} [Field Ω] {ι ν κ : Type} {E : Type} [AddCommGroup E]
    [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E)
    (φ : κ → E →ₗ[Ω] Ω) (a : Fin 2 → Φ) (j : Fin 2) :
    (T.multiConeMap (T.wwCoord x δ e φ (a 0) (a 1))).comp
        (rename (T.yyEmb j) : MRing (T.yyIdx ι ν κ) →ₐ[ℤ] MRing (T.wwIdx ι ν κ)).toRingHom =
      (rename (diagonalBlockIndex j) : MvPolynomial T.YBlk Φ →ₐ[Φ] MvPolynomial T.WBlk Φ).toRingHom.comp
        (T.multiConeMap (T.yyCoord x δ e φ (a j))) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
  · simp [T.multiConeMap]
  · rcases p with ⟨_ | _ | _, i⟩
    · simp [T.multiConeMap, T.yyEmb, T.wwCoord, T.yyCoord, diagonalBlockIndex]
    · simp [T.multiConeMap, T.yyEmb, T.wwCoord, T.yyCoord, diagonalBlockIndex]
    · fin_cases j <;> simp [T.multiConeMap, T.yyEmb, T.wwCoord, T.yyCoord, diagonalBlockIndex]

/- English proof (translation)
Use extensionality with `f`. Rewrite using `[Ideal.mem_comap, T.wwIdeal, T.yyIdeal, RingHom.mem_ker, RingHom.mem_ker, ← RingHom.comp_apply, multiConeMap_ww_comp_yyEmb, RingHom.comp_apply]`. Conclude with `map_eq_zero_iff _ (rename_injective _ (segreBlockEmbedding_injective j))`.
-/
theorem comap_wwIdeal_yyEmb {Ω : Type} [Field Ω] {ι ν κ : Type} {E : Type} [AddCommGroup E]
    [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E)
    (φ : κ → E →ₗ[Ω] Ω) (a : Fin 2 → Φ) (j : Fin 2) :
    (T.wwIdeal x δ e φ (a 0) (a 1)).comap
        (rename (T.yyEmb j) : MRing (T.yyIdx ι ν κ) →ₐ[ℤ] MRing (T.wwIdx ι ν κ)).toRingHom =
      T.yyIdeal x δ e φ (a j) := by
  ext f
  rw [Ideal.mem_comap, T.wwIdeal, T.yyIdeal, RingHom.mem_ker, RingHom.mem_ker, ← RingHom.comp_apply,
    multiConeMap_ww_comp_yyEmb, RingHom.comp_apply]
  exact map_eq_zero_iff _ (rename_injective _ (segreBlockEmbedding_injective j))

/- English proof (translation)
Use function extensionality and compare the values at `k`. Apply the tactic sequence `cases k <;> simp [T.wwDeg, T.llDeg, T.unitDeg]`.
-/
theorem wwDeg_sub_eq_llDeg (n : ℕ) :
    (fun k => (T.wwDeg n 1 k : ℤ) - (T.wwDeg (n + 3) 0 k : ℤ)) = T.llDeg := by
  funext k
  cases k <;> simp [T.wwDeg, T.llDeg, T.unitDeg]

/- English proof (translation)
Introduce `Ω _ ι ν κ _ _ _ E _ _ Φ _ _ x B e φ δ D a hs hg hd hc hbase hind`. Take `⟨hY, hW, hΔ⟩` from `hWW Ω ι ν κ E Φ x B e φ δ hs hg hd D hbase a hind`. Take `⟨hex, hdiv⟩` from `hDD Ω ι ν κ E Φ x B e φ δ hs hg hd hc a hind`. Conclude with `⟨⟨hY, hW⟩, comap_wwIdeal_yyEmb x δ e φ a, hΔ, ⟨wwDeg_sub_eq_llDeg, T.two_llDeg⟩, hex, hdiv, (hDP Ω ι ν κ E Φ x e φ δ (a 0)).2.1⟩`.
-/
theorem FibreProduct.proof (hWW : WWArithVar.Statement) (hDD : DiagDiv.Statement)
    (hDP : DiagPull.Statement) : FibreProduct.Statement := by
  intro Ω _ ι ν κ _ _ _ E _ _ Φ _ _ x B e φ δ D a hs hg hd hc hbase hind
  obtain ⟨hY, hW, hΔ⟩ := hWW Ω ι ν κ E Φ x B e φ δ hs hg hd D hbase a hind
  obtain ⟨hex, hdiv⟩ := hDD Ω ι ν κ E Φ x B e φ δ hs hg hd hc a hind
  exact ⟨⟨hY, hW⟩, comap_wwIdeal_yyEmb x δ e φ a, hΔ, ⟨wwDeg_sub_eq_llDeg, T.two_llDeg⟩, hex, hdiv,
    (hDP Ω ι ν κ E Φ x e φ δ (a 0)).2.1⟩

end

end GroundTheory.Heights₂.Heights.Inter
