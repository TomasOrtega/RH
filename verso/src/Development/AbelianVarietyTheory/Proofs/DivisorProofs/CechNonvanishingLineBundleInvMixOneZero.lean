import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Tri
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsGermGIffExistsFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj

namespace GlobalTheory.AmpleGen

/- English proof (translation)
Introduce `i j`. Establish `hg : (LB.LinComb L (Y` using `Y) (K := PEmpty) PEmpty.elim PEmpty.elim).g i j = 1 := by`. Unfold `LB.LinComb`. Simplify using the standard rewrite rules. Simplify using `only [LB.oneGen, hg, map_one, one_mul]`.
-/
theorem isGen_oneGen {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen (Y := Y) L).IsGen := by
  intro i j
  have hg : (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim).g i j = 1 :=
    by
    unfold LB.LinComb; simp
  simp only [LB.oneGen, hg, map_one, one_mul]

/- English proof (translation)
Establish `hs : LB.SameSum (K` using `PEmpty) PEmpty.elim PEmpty.elim (Sum.elim (fun _ : Fin 1 => 𝟙 A.left) ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left]) (Sum.elim (fun _ => (1 : ℤ)) fun k => -(![1, 0] : Fin 2 → ℤ) k) := by`. Introduce `ψ`. Apply the tactic sequence `by_cases h : 𝟙 A.left = ψ <;> by_cases h' : (GrpObj.inv : A ⟶ A).left = ψ <;>`. Simplify using `[Fintype.sum_sum_type, Fin.sum_univ_two, h, h']`. Take `⟨t, ht, -⟩` from `ReciprocityTheory.ChartRestriction.G.DVR.gen_transport hL hs (LB.oneGen L) (isGen_oneGen L)`.

Establish `key` using `(GlobalTheory.GermSectionCompare.isGen_divEquiv ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left] ![1, 0] ((GlobalTheory.GermSectionCompare.divEquiv ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left] ![1, 0]).symm t)).1 (by rw [Equiv.apply_symm_apply]; exact ht)`. Conclude with `⟨_, key⟩`.
-/
theorem exists_iso_mix_one_zero {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (L : LB A.left)
    (hL : L.IsLB) : ∃ w : LB.Iso L (mix A L 1 0), w.IsGen := by
  have hs : LB.SameSum (K := PEmpty) PEmpty.elim PEmpty.elim
      (Sum.elim (fun _ : Fin 1 => 𝟙 A.left) ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left])
      (Sum.elim (fun _ => (1 : ℤ)) fun k => -(![1, 0] : Fin 2 → ℤ) k) := by
    intro ψ
    by_cases h : 𝟙 A.left = ψ <;> by_cases h' : (GrpObj.inv : A ⟶ A).left = ψ <;>
      simp [Fintype.sum_sum_type, Fin.sum_univ_two, h, h']
  obtain ⟨t, ht, -⟩ := ReciprocityTheory.ChartRestriction.G.DVR.gen_transport hL hs (LB.oneGen L) (isGen_oneGen L)
  have key := (GlobalTheory.GermSectionCompare.isGen_divEquiv ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left] ![1, 0]
    ((GlobalTheory.GermSectionCompare.divEquiv ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left] ![1, 0]).symm t)).1
    (by rw [Equiv.apply_symm_apply]; exact ht)
  exact ⟨_, key⟩

/- English proof (translation)
Introduce `K _ A _ L hL j ⟨κ, lo, ft, W, hW, hcov, hne⟩`. Take `⟨w, hw⟩` from `exists_iso_mix_one_zero A L hL`. Establish `hM : (mix A L 1 0).IsLB` using `LB.isLB_linComb hL _ _`. Conclude with `⟨κ, lo, ft, W, hW, hcov, fun h => hne (h.of_iso (GlobalTheory.AbLaw.cechLBCongr A.hom W hL hM w hw).symm)⟩`.
-/
theorem nv_mix_one_zero : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (L : LB A.left), L.IsLB →
    ∀ j : ℕ, NV A L j → NV A (mix A L 1 0) j := by
  intro K _ A _ L hL j ⟨κ, lo, ft, W, hW, hcov, hne⟩
  obtain ⟨w, hw⟩ := exists_iso_mix_one_zero A L hL
  have hM : (mix A L 1 0).IsLB := LB.isLB_linComb hL _ _
  exact ⟨κ, lo, ft, W, hW, hcov, fun h => hne (h.of_iso (GlobalTheory.AbLaw.cechLBCongr A.hom W hL hM w hw).symm)⟩

end GlobalTheory.AmpleGen
