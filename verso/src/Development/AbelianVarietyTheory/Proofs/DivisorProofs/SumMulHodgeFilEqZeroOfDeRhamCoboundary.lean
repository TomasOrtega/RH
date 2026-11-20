import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointCochainPullbackBaseChangeCocycleCoboundaryW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeBaseChangeSpecAlgebraProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangePullSumMulPointValueEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamFreeHodgeSequenceBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffPointwiseCoboundary

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

/- English proof (translation)
Introduce `H R _ B _ g hB hg y hy D _ _ J _ d β hβ hcob`. Take `⟨-, -, hBC⟩` from `GlobalTheory.abelianDeRham_free_hodge_baseChange H`. Take `⟨B', _, π, q, hpb, hB', hg', -, hq1, hq2⟩` from `GlobalTheory.exists_baseChange_spAlg_prod R D B g hB hg`. Establish `w : q ≫ (SpAlg R D ⊗ B).hom = B'.hom ≫ spMap (algebraMap R D)`. Rewrite using `[← Over.w (fst (SpAlg R D) B), ← Category.assoc, hq1]`.

Both sides reduce to the same expression. Set `m` to `GlobalTheory.Published.AbelianDeRham.bcMor hpb`. Take `⟨hm, hspan⟩` from `hBC R B g hB hg D B' π hpb`. Take `⟨y', hy'⟩` from `hm.exists y`. Establish `hFil : ∀ c ∈ PrimitiveSubmodule B', y' c = 0`.

Introduce `c hc`. Rewrite `hc` using `[hspan]`. Use `Submodule.span_induction (p := fun c _ ↦ y' c = 0) ?_ (by simp) (fun a b _ _ ha hb ↦ by simp [ha, hb]) (fun r a _ ha ↦ by simp [ha]) hc` and prove the remaining obligations. Introduce and unpack `_ ⟨c, hc, rfl⟩`. Rewrite using `[hy' c, (Submodule.mem_dualAnnihilator _).1 hy c hc, map_zero]`.

Take `⟨k, hk⟩` from `(GlobalTheory.PtExt.bcPull_keeps R D (algebraMap R D) (SpAlg R D ⊗ B) B' q w _).2 hcob`. Rewrite `hk` using `[GlobalTheory.PtExt.bcPull_sumMul_fv R D B B' q w π hq1 hq2 m.isMor J d β]`. Establish `hF1` using `(mem_hodgeFiltration_iff_pointwiseCoboundary D B' _).2 ⟨k, hk⟩`. Set `c' : primDR B'` to `∑ i, d i • m.pull ⟨_, hβ i⟩`. Establish `hc' : (c' : FirstDeRham (B'.hom ≫ 𝟙 _)) = CatCoh.H1.mk _ (∑ i, d i • m.isMor.coef.pullbackOneCocycle (β i))`.

Simplify using `only [c', Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]`. Both sides reduce to the same expression. Establish `h0 : y' c' = 0` using `hFil c' (Submodule.mem_comap.2 (by rw [Submodule.subtype_apply, hc']; exact hF1))`. Rewrite using `[← h0]`. Simplify using `only [c', map_sum, map_smul, smul_eq_mul]`.

Conclude with `Finset.sum_congr rfl fun i _ ↦ by rw [hy' _]`.
-/
theorem sum_mul_eq_zero_of_isCob : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (B : Over (Sp R)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ∀ y ∈ Fil B, ∀ (D : Type) [CommRing D] [Algebra R D] (J : Type) [Fintype J] (d : J → D) (β : J → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) (hβ : ∀ i, CatCoh.H1.mk _ (β i) ∈ primDR B), (∃ k, IsCob (whole _) (sumMul d fun i ↦ fv (β i)) k) → ∑ i, d i * algebraMap R D (y ⟨_, hβ i⟩) = 0 := by
  intro H R _ B _ g hB hg y hy D _ _ J _ d β hβ hcob
  obtain ⟨-, -, hBC⟩ := GlobalTheory.abelianDeRham_free_hodge_baseChange H
  obtain ⟨B', _, π, q, hpb, hB', hg', -, hq1, hq2⟩ := GlobalTheory.exists_baseChange_spAlg_prod R D B g hB hg
  have w : q ≫ (SpAlg R D ⊗ B).hom = B'.hom ≫ spMap (algebraMap R D) := by
    rw [← Over.w (fst (SpAlg R D) B), ← Category.assoc, hq1]
    rfl
  let m := GlobalTheory.Published.AbelianDeRham.bcMor hpb
  obtain ⟨hm, hspan⟩ := hBC R B g hB hg D B' π hpb
  obtain ⟨y', hy'⟩ := hm.exists y

  have hFil : ∀ c ∈ PrimitiveSubmodule B', y' c = 0 := by
    intro c hc
    rw [hspan] at hc
    refine Submodule.span_induction (p := fun c _ ↦ y' c = 0) ?_ (by simp) (fun a b _ _ ha hb ↦ by simp [ha, hb])
      (fun r a _ ha ↦ by simp [ha]) hc
    rintro _ ⟨c, hc, rfl⟩
    rw [hy' c, (Submodule.mem_dualAnnihilator _).1 hy c hc, map_zero]

  obtain ⟨k, hk⟩ := (GlobalTheory.PtExt.bcPull_keeps R D (algebraMap R D) (SpAlg R D ⊗ B) B' q w _).2 hcob
  rw [GlobalTheory.PtExt.bcPull_sumMul_fv R D B B' q w π hq1 hq2 m.isMor J d β] at hk
  have hF1 := (mem_hodgeFiltration_iff_pointwiseCoboundary D B' _).2 ⟨k, hk⟩
  let c' : primDR B' := ∑ i, d i • m.pull ⟨_, hβ i⟩
  have hc' : (c' : FirstDeRham (B'.hom ≫ 𝟙 _)) = CatCoh.H1.mk _ (∑ i, d i • m.isMor.coef.pullbackOneCocycle (β i)) := by
    simp only [c', Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
    rfl
  have h0 : y' c' = 0 := hFil c' (Submodule.mem_comap.2 (by rw [Submodule.subtype_apply, hc']; exact hF1))
  rw [← h0]
  simp only [c', map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [hy' _]

end GlobalTheory.PtExt
