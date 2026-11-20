import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SnocColumnsMovedByUpperUnitriangularIffStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryEmbeddingPreimageOfFixesAnisotropicStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselBasePointRationalWithRationalLeftInStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB

/- English proof (translation)
The claim follows from `GlobalTheory.T.snocColumns_moved_by_upperUnitriangular_iff`.
-/
theorem snocCols_uni_iff : ∀ (R : Type) [CommRing R] (n σ : ℕ) (M : Matrix (Fin n) (Fin σ) R) (w : Fin n → R) (Y : Matrix (Fin n) (Fin n) R), (∃ U ∈ GlobalTheory.UniIndexPrime.uniSub (σ + 1) R, Y * Matrix.of (fun k => Fin.snoc (α := fun _ => R) (M k) (w k)) = Matrix.of (fun k => Fin.snoc (α := fun _ => R) (M k) (w k)) * (U : Matrix (Fin (σ + 1)) (Fin (σ + 1)) R)) ↔ ∃ u ∈ GlobalTheory.UniIndexPrime.uniSub σ R, ∃ v : Fin σ → R, Y * M = M * (u : Matrix (Fin σ) (Fin σ) R) ∧ Y *ᵥ w = w + M *ᵥ v := GlobalTheory.T.snocColumns_moved_by_upperUnitriangular_iff

/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_unitaryEmbedding_preimage_of_fixes_anisotropicLine`.
-/
theorem fix_lineVec_emb : ∀ (D : D7) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ k : GA D S, mt S k *ᵥ ratV (o.iB *ᵥ ζ) = ratV (o.iB *ᵥ ζ) → ∃ h : GA D A, k = o.emb (h, 1) := GlobalTheory.T.exists_unitaryEmbedding_preimage_of_fixes_anisotropicLine

/- English proof (translation)
The claim follows from `GlobalTheory.T.x0_mem_ratMx_and_exists_rat_leftInverse`.
-/
theorem fourierBesselBasePoint_leftInverse_rational : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), (∃ P ∈ ratMx D (σ + 1) B.V.rank, P ⬝ x0 B = 1) ∧ x0 B ∈ ratMx D B.V.rank (σ + 1) := GlobalTheory.T.x0_mem_ratMx_and_exists_rat_leftInverse

variable {D : D7} {σ : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [ratV, rat, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]`.
-/
theorem ratV_mulVec_rat {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (v : Fin n → D.host.E) :
    ratV (M *ᵥ v) = rat M *ᵥ ratV v := by
  funext i; simp only [ratV, rat, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

def actUni (B : BesLev D σ) : Subgroup (GA D B.V) where
  carrier := {g | ∃ u ∈ UX D (σ + 1), mt B.V g ⬝ x0 B = x0 B ⬝ u.1}
  one_mem' := ⟨1, one_mem _, by rw [mt_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]⟩
  mul_mem' := by
    rintro a b ⟨u, hu, ha⟩ ⟨u', hu', hb⟩
    refine ⟨u * u', mul_mem hu hu', ?_⟩
    rw [mt_mul, Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Units.val_mul, Matrix.mul_assoc]
  inv_mem' := by
    rintro a ⟨u, hu, ha⟩
    refine ⟨u⁻¹, inv_mem hu, ?_⟩
    have h1 : mt B.V a⁻¹ ⬝ (x0 B ⬝ u.1) ⬝ (u⁻¹).1 = x0 B ⬝ (u⁻¹).1 := by
      rw [← ha, ← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul]
    rw [← h1, Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

/- English proof (translation)
The claim follows from `snocCols_uni_iff (AE D) B.V.rank σ B.d.jX _ (mt B.V g)`.
-/
theorem mem_actUni_iff (B : BesLev D σ) (g : GA D B.V) : g ∈ actUni B ↔ ∃ u ∈ UX D σ, ∃ v : Fin σ → AE D,
    mt B.V g ⬝ B.d.jX = B.d.jX ⬝ u.1 ∧
      mt B.V g *ᵥ (B.d.j0 *ᵥ ratV (vecB B.o B.ζ)) = B.d.j0 *ᵥ ratV (vecB B.o B.ζ) + B.d.jX *ᵥ v :=
  snocCols_uni_iff (AE D) B.V.rank σ B.d.jX _ (mt B.V g)

/- English proof (translation)
Introduce `n hn`. Take `⟨u, hu, b, c, rfl⟩` from `((flag_jacobi_structure D B.V B.V₀ σ B.d).1 n).1 hn`. Rewrite using `[mem_actUni_iff]`. Establish `hm : mt B.V (B.d.levi u * (B.d.nB b * B.d.nC c)) ⬝ B.d.j0 = B.d.j0 + B.d.jX ⬝ (u.1 ⬝ b)`. Rewrite using `[mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, B.d.nC_j0, B.d.nB_j0, Matrix.mul_add, B.d.wittDecomp_levi_inclAnisotropic, ← Matrix.mul_assoc, B.d.levi_jX, Matrix.mul_assoc]`.

Use `⟨u, hu, (u.1 ⬝ b) *ᵥ ratV (vecB B.o B.ζ), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, B.d.nC_jX, B.d.nB_jX, B.d.levi_jX]`. Rewrite using `[Matrix.mulVec_mulVec, hm, Matrix.add_mulVec, Matrix.mulVec_mulVec]`.
-/
theorem flagN_le_actUni (B : BesLev D σ) : flagN B.d ≤ actUni B := by
  intro n hn
  obtain ⟨u, hu, b, c, rfl⟩ := ((flag_jacobi_structure D B.V B.V₀ σ B.d).1 n).1 hn
  rw [mem_actUni_iff]
  have hm : mt B.V (B.d.levi u * (B.d.nB b * B.d.nC c)) ⬝ B.d.j0 = B.d.j0 + B.d.jX ⬝ (u.1 ⬝ b) := by
    rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, B.d.nC_j0, B.d.nB_j0, Matrix.mul_add, B.d.wittDecomp_levi_inclAnisotropic,
      ← Matrix.mul_assoc, B.d.levi_jX, Matrix.mul_assoc]
  refine ⟨u, hu, (u.1 ⬝ b) *ᵥ ratV (vecB B.o B.ζ), ?_, ?_⟩
  · rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, B.d.nC_jX, B.d.nB_jX, B.d.levi_jX]
  · rw [Matrix.mulVec_mulVec, hm, Matrix.add_mulVec, Matrix.mulVec_mulVec]

/- English proof (translation)
Rewrite using `[mem_actUni_iff]`. Use `⟨1, one_mem _, 0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[embA_apply, B.d.wittDecomp_anisotropicEmbedding_inclX, Units.val_one, Matrix.mul_one]`. Rewrite using `[Matrix.mulVec_zero, add_zero, Matrix.mulVec_mulVec, embA_apply, B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mulVec_mulVec, vecB, ratV_mulVec_rat]`. Express the relevant statement in the definitionally equal form `B.d.j0 *ᵥ (mt B.V₀ (B.o.emb (h, 1)) *ᵥ (B.o.jB *ᵥ ratV B.ζ)) = B.d.j0 *ᵥ (B.o.jB *ᵥ ratV B.ζ)`.

Use `congr 1`. Rewrite using `[Matrix.mulVec_mulVec, B.o.emb_jB, mt_one, Matrix.mul_one]`.
-/
theorem embA_mem_actUni (B : BesLev D σ) (h : GA D B.A) : embA B.d B.o h ∈ actUni B := by
  rw [mem_actUni_iff]
  refine ⟨1, one_mem _, 0, ?_, ?_⟩
  · rw [embA_apply, B.d.wittDecomp_anisotropicEmbedding_inclX, Units.val_one, Matrix.mul_one]
  · rw [Matrix.mulVec_zero, add_zero, Matrix.mulVec_mulVec, embA_apply, B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mulVec_mulVec,
      vecB, ratV_mulVec_rat]
    change B.d.j0 *ᵥ (mt B.V₀ (B.o.emb (h, 1)) *ᵥ (B.o.jB *ᵥ ratV B.ζ)) = B.d.j0 *ᵥ (B.o.jB *ᵥ ratV B.ζ)
    congr 1
    rw [Matrix.mulVec_mulVec, B.o.emb_jB, mt_one, Matrix.mul_one]

/- English proof (translation)
The claim follows from `sup_le (flagN_le_actUni B) (by rintro _ ⟨h, rfl⟩; exact embA_mem_actUni B h)`.
-/
theorem besGrp_le_actUni (B : BesLev D σ) : besGrp B.d B.o ≤ actUni B :=
  sup_le (flagN_le_actUni B) (by rintro _ ⟨h, rfl⟩; exact embA_mem_actUni B h)

/- English proof (translation)
Take `⟨u, hu, v, hX, h0⟩` from `(mem_actUni_iff B g).1 hg`. Establish `hst : B.d.levi u⁻¹ * g ∈ stabX B.d` using `by show mt B.V (B.d.levi u⁻¹ * g) ⬝ B.d.jX = B.d.jX`. Rewrite using `[mt_mul, Matrix.mul_assoc, hX, ← Matrix.mul_assoc, B.d.levi_jX, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]`. Take `⟨n, hn, k, hk⟩` from `((flag_jacobi_structure D B.V B.V₀ σ B.d).2.2.1 _).1 hst`. Take `⟨b, c, rfl⟩` from `((flag_jacobi_structure D B.V B.V₀ σ B.d).2.1 n).1 hn`.

Establish `hp : B.d.p0 ⬝ mt B.V (B.d.levi u⁻¹ * g) ⬝ B.d.j0 = mt B.V₀ k`. Rewrite using `[hk, mt_mul, mt_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, B.d.wittDecomp_projAnisotropic_unipotentMixed, Matrix.sub_mul, B.d.wittDecomp_projAnisotropic_unipotentSkew, Matrix.mul_assoc _ B.d.pY, B.d.pY_nC, Matrix.sub_mul, B.d.wittDecomp_projAnisotropic_anisotropicEmbedding, Mat …`. Establish `hz : mt B.V₀ k *ᵥ ratV (B.o.iB *ᵥ B.ζ) = ratV (B.o.iB *ᵥ B.ζ)`. Establish `e1 : B.d.p0 ⬝ mt B.V (B.d.levi u⁻¹ * g) = B.d.p0 ⬝ mt B.V g`. Rewrite using `[mt_mul, ← Matrix.mul_assoc, B.d.wittDecomp_projAnisotropic_levi]`.

Rewrite using `[← hp, e1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`. Express the relevant statement in the definitionally equal form `B.d.p0 *ᵥ (mt B.V g *ᵥ (B.d.j0 *ᵥ ratV (vecB B.o B.ζ))) = _`. Rewrite using `[h0, Matrix.mulVec_add, Matrix.mulVec_mulVec, B.d.p0_j0, Matrix.one_mulVec, Matrix.mulVec_mulVec, B.d.p0_jX, Matrix.zero_mulVec, add_zero]`. Both sides reduce to the same expression. Take `⟨h, rfl⟩` from `fix_lineVec_emb D B.V₀ B.A B.L B.o B.ζ B.line k hz`.

Establish `hg' : g = (B.d.levi u * (B.d.nB b * B.d.nC c)) * embA B.d B.o h`. Rewrite using `[embA_apply, mul_assoc, ← hk, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]`. Rewrite using `[hg']`. Conclude with `mul_mem (Subgroup.mem_sup_left (((flag_jacobi_structure D B.V B.V₀ σ B.d).1 _).2 ⟨u, hu, b, c, rfl⟩)) (Subgroup.mem_sup_right ⟨h, rfl⟩)`.
-/
theorem mem_besGrp_of_actUni (B : BesLev D σ) (g : GA D B.V) (hg : g ∈ actUni B) : g ∈ besGrp B.d B.o := by
  obtain ⟨u, hu, v, hX, h0⟩ := (mem_actUni_iff B g).1 hg
  have hst : B.d.levi u⁻¹ * g ∈ stabX B.d := by
    show mt B.V (B.d.levi u⁻¹ * g) ⬝ B.d.jX = B.d.jX
    rw [mt_mul, Matrix.mul_assoc, hX, ← Matrix.mul_assoc, B.d.levi_jX, Matrix.mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.mul_one]
  obtain ⟨n, hn, k, hk⟩ := ((flag_jacobi_structure D B.V B.V₀ σ B.d).2.2.1 _).1 hst
  obtain ⟨b, c, rfl⟩ := ((flag_jacobi_structure D B.V B.V₀ σ B.d).2.1 n).1 hn
  have hp : B.d.p0 ⬝ mt B.V (B.d.levi u⁻¹ * g) ⬝ B.d.j0 = mt B.V₀ k := by
    rw [hk, mt_mul, mt_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, B.d.wittDecomp_projAnisotropic_unipotentMixed, Matrix.sub_mul, B.d.wittDecomp_projAnisotropic_unipotentSkew,
      Matrix.mul_assoc _ B.d.pY, B.d.pY_nC, Matrix.sub_mul, B.d.wittDecomp_projAnisotropic_anisotropicEmbedding, Matrix.mul_assoc _ B.d.pY, B.d.wittDecomp_projY_anisotropicEmbedding,
      Matrix.sub_mul, Matrix.mul_assoc, B.d.p0_j0, Matrix.mul_one, Matrix.mul_assoc _ B.d.pY, B.d.pY_j0,
      Matrix.mul_zero, sub_zero]
  have hz : mt B.V₀ k *ᵥ ratV (B.o.iB *ᵥ B.ζ) = ratV (B.o.iB *ᵥ B.ζ) := by
    have e1 : B.d.p0 ⬝ mt B.V (B.d.levi u⁻¹ * g) = B.d.p0 ⬝ mt B.V g := by
      rw [mt_mul, ← Matrix.mul_assoc, B.d.wittDecomp_projAnisotropic_levi]
    rw [← hp, e1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    change B.d.p0 *ᵥ (mt B.V g *ᵥ (B.d.j0 *ᵥ ratV (vecB B.o B.ζ))) = _
    rw [h0, Matrix.mulVec_add, Matrix.mulVec_mulVec, B.d.p0_j0, Matrix.one_mulVec, Matrix.mulVec_mulVec, B.d.p0_jX,
      Matrix.zero_mulVec, add_zero]
    rfl
  obtain ⟨h, rfl⟩ := fix_lineVec_emb D B.V₀ B.A B.L B.o B.ζ B.line k hz
  have hg' : g = (B.d.levi u * (B.d.nB b * B.d.nC c)) * embA B.d B.o h := by
    rw [embA_apply, mul_assoc, ← hk, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  rw [hg']
  exact mul_mem (Subgroup.mem_sup_left (((flag_jacobi_structure D B.V B.V₀ σ B.d).1 _).2 ⟨u, hu, b, c, rfl⟩))
    (Subgroup.mem_sup_right ⟨h, rfl⟩)

/- English proof (translation)
Introduce `D σ B`. Take `⟨⟨P, hP, hPx⟩, hx⟩` from `fourierBesselBasePoint_leftInverse_rational D σ B`. Use `⟨fun g => ⟨fun hg => besGrp_le_actUni B hg, fun hg => mem_besGrp_of_actUni B g hg⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `a a' h`. Rewrite using `[← Matrix.one_mul a, ← Matrix.one_mul a', ← hPx, Matrix.mul_assoc, Matrix.mul_assoc, h]`.

Introduce `g hg u hgu`. Establish `hinv : mt B.V g⁻¹ ⬝ x0 B = x0 B ⬝ (u.1⁻¹).1`. Establish `h1 : mt B.V g⁻¹ ⬝ (x0 B ⬝ u.1.1) ⬝ (u.1⁻¹).1 = x0 B ⬝ (u.1⁻¹).1`. Rewrite using `[← hgu, ← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul]`. Rewrite using `[← h1, Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `e : u.1.1 = P ⬝ mt B.V g ⬝ x0 B`. Rewrite using `[Matrix.mul_assoc, hgu, ← Matrix.mul_assoc, hPx, Matrix.one_mul]`. Rewrite using `[e]`. Conclude with `ratMx_mul (ratMx_mul hP ((mem_GQ_iff _ _).1 hg)) hx`.

Establish `e : (u.1⁻¹).1 = P ⬝ mt B.V g⁻¹ ⬝ x0 B`. Rewrite using `[Matrix.mul_assoc, hinv, ← Matrix.mul_assoc, hPx, Matrix.one_mul]`. Rewrite using `[e]`. Conclude with `ratMx_mul (ratMx_mul hP ((mem_GQ_iff _ _).1 (inv_mem hg))) hx`.
-/
theorem besselGroup_action_fourierBesselBasePoint : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), (∀ g : GA D B.V, g ∈ besGrp B.d B.o ↔ ∃ u ∈ UX D (σ + 1), mt B.V g ⬝ x0 B = x0 B ⬝ u.1) ∧ (∀ a a' : Mx D (σ + 1) (σ + 1), x0 B ⬝ a = x0 B ⬝ a' → a = a') ∧ ∀ g ∈ GQ B.V, ∀ u : UX D (σ + 1), mt B.V g ⬝ x0 B = x0 B ⬝ u.1.1 → u ∈ UXQ D (σ + 1) := by
  intro D σ B
  obtain ⟨⟨P, hP, hPx⟩, hx⟩ := fourierBesselBasePoint_leftInverse_rational D σ B
  refine ⟨fun g => ⟨fun hg => besGrp_le_actUni B hg, fun hg => mem_besGrp_of_actUni B g hg⟩, ?_, ?_⟩
  · intro a a' h
    rw [← Matrix.one_mul a, ← Matrix.one_mul a', ← hPx, Matrix.mul_assoc, Matrix.mul_assoc, h]
  · intro g hg u hgu
    have hinv : mt B.V g⁻¹ ⬝ x0 B = x0 B ⬝ (u.1⁻¹).1 := by
      have h1 : mt B.V g⁻¹ ⬝ (x0 B ⬝ u.1.1) ⬝ (u.1⁻¹).1 = x0 B ⬝ (u.1⁻¹).1 := by
        rw [← hgu, ← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul]
      rw [← h1, Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    refine ⟨?_, ?_⟩
    · have e : u.1.1 = P ⬝ mt B.V g ⬝ x0 B := by
        rw [Matrix.mul_assoc, hgu, ← Matrix.mul_assoc, hPx, Matrix.one_mul]
      rw [e]; exact ratMx_mul (ratMx_mul hP ((mem_GQ_iff _ _).1 hg)) hx
    · have e : (u.1⁻¹).1 = P ⬝ mt B.V g⁻¹ ⬝ x0 B := by
        rw [Matrix.mul_assoc, hinv, ← Matrix.mul_assoc, hPx, Matrix.one_mul]
      rw [e]; exact ratMx_mul (ratMx_mul hP ((mem_GQ_iff _ _).1 (inv_mem hg))) hx

end GlobalTheory.Unf.FB

end
