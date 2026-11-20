import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.ThetaSumRationalInvariant
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdPlace

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Tauto
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open PositivityTheory.ThKF0.Resc in
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Establish `hσ : IsCMExt F E σ` using `d.cm`. Establish `hψ : IsStd d.B.ψ` using `d.std`. Establish `h2 : Module.finrank F E = 2` using `hσ.2.2.1`. Use `haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero`. Take `⟨δ, hq⟩` from `exists_isQuad hσ`.

Establish `h0 : δ ≠ 0` using `hq.unit.ne_zero`. Take `⟨-, hS, hR⟩` from `d.ok.dbl.weil`. Establish `hYd : d.Y.J.det ≠ 0`. Take `⟨⟨ε, hε⟩, -⟩` from `d.ok.frame`. Introduce `hz`.

Establish `hee : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1`. Rewrite using `[← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]`. Establish `hM : (Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) * Matrix.fromBlocks 0 (((ε : ℤ) : E) • 1) 1 0 = 1`. Rewrite using `[Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]`. Simplify using `[smul_smul, hee]`.

Establish `h1` using `congrArg Matrix.det hM`. Rewrite `h1` using `[Matrix.det_mul, ← hε, Matrix.det_mul, Matrix.det_mul, dbl, Matrix.det_fromBlocks_zero₂₁, hz]`. Simplify using `at h1`. Establish `hκ : Fintype.card d.κ = Fintype.card (Fin d.m) * Fintype.card (Fin d.n ⊕ Fin d.n)`. Establish `: Nontrivial (AF F)` using `(AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial`.

Set `bE : Module.Basis (Fin 2) F E` to `Module.finBasisOfFinrankEq F E h2`. Set `bA` to `Algebra.TensorProduct.basis (AF F) bE`. Use `haveI : Module.Free (AF F) (AE F E) := Module.Free.of_basis bA`. Use `haveI : Module.Finite (AF F) (AE F E) := Module.Finite.of_basis bA`. Establish `e` using `d.dd.e.finrank_eq`.

Rewrite `e` using `[Module.finrank_matrix, Module.finrank_eq_card_basis bA, Module.finrank_prod, Module.finrank_fintype_fun_eq_card]`. Simplify using `only [Fintype.card_fin, Fintype.card_sum] at e ⊢`. Use linear arithmetic over natural numbers and integers. Take `⟨d₀, hd₀⟩` from `exists_ratCoord h2 hκ d.dd.e d.ok.dbl.rat`. Choose the witnesses or unpack the hypotheses as in `⟨a, b, hab, hA, hB⟩ : ∃ a b : E, -1 = δ * a * b ∧ IsHerm σ (a • d.A.J) ∧ IsHerm σ (b • d.Y.J) := by`.

Break down `d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩` into its components or cases. Use `⟨1, -δ⁻¹, by field_simp, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[one_smul]`. Conclude with `⟨hA.herm, (herm_det hA).isUnit⟩`. Use `⟨fun i j => by simp [hY i j, hq.anti], Ne.isUnit ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.det_smul]`. Conclude with `mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero h0))) hYd`. Use `⟨-δ⁻¹, 1, by field_simp, ?_, ?_⟩` and prove the remaining obligations. Use `⟨fun i j => by simp [hA.skew i j, hq.anti], Ne.isUnit ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_smul]`.

Conclude with `mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero h0))) (skew_det hA)`. Rewrite using `[one_smul]`. Conclude with `⟨hY, hYd.isUnit⟩`. Establish `hb : b ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at hab`. Establish `hξ : (-1 : AE F E) = inclR (F` using `F) (AF F) δ * inclR (F := F) (AF F) a * inclR (F := F) (AF F) b := by`. Rewrite using `[← map_mul, ← map_mul, ← hab, map_neg, map_one]`. Establish `hJA : incM F (a • d.A.J) = inclR (F` using `F) (AF F) a • incM F d.A.J := by`. Use extensionality with `i j`.

Simplify using `[incM]`. Establish `hJB : incM F (dbl (b • d.Y.J)) = inclR (F` using `F) (AF F) b • dbl (incM F d.Y.J) := by`. Apply the tactic sequence `ext (i | i) (j | j) <;> simp [incM, dbl]`. Take `⟨d', om', he, hS', hR', hgg⟩` from `split_resc (c := cA σ) (C := adeleClass F) (ψ := d.B.ψ) (κ := d.κ) hξ (hb.isUnit.map (inclR (F := F) (AF F))) hJA hJB hS.toIsSplitting hR`. Establish `hd' : ∀ x, d'.e (incM F x) = (fun i => algebraMap F (AF F) ((d₀ x).1 i), fun i => algebraMap F (AF F) ((d₀ x).2 i))` using `fun x => by rw [he]; exact hd₀ x`.

Take `⟨g', hg'1, hg'2⟩` from `hgg γ`. Establish `hg : ∃ γ₀ : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E, ((g' : GL (Fin d.n ⊕ Fin d.n) (AE F E)) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) = incM F γ₀`. Take `⟨g₀, hg₀⟩` from `Subgroup.mem_subgroupOf.mp hγ`. Use `⟨g₀, ?_⟩` and prove the remaining obligations. Rewrite using `[hg'1, ← hg₀]`.

Both sides reduce to the same expression. Rewrite using `[← hg'2]`. Conclude with `split_core hψ hq (a • d.A.J) (b • d.Y.J) hA hB d' d₀ hd' d.χ d.ok.hecke om' hS' hR' g' hg Ψ hΨ`.
-/
theorem thetaSum_rational_invariant (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (γ : d.G) (hγ : γ ∈ rat2 σ d.Y) (Ψ : d.Fn) (hΨ : Ψ ∈ d.sch) :
    thetaSum F (d.om γ Ψ) = thetaSum F Ψ := by
  have hσ : IsCMExt F E σ := d.cm
  have hψ : IsStd d.B.ψ := d.std
  have h2 : Module.finrank F E = 2 := hσ.2.2.1
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  obtain ⟨δ, hq⟩ := exists_isQuad hσ
  have h0 : δ ≠ 0 := hq.unit.ne_zero
  obtain ⟨-, hS, hR⟩ := d.ok.dbl.weil
  have hYd : d.Y.J.det ≠ 0 := by
    obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
    intro hz
    have hee : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    have hM : (Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) *
        Matrix.fromBlocks 0 (((ε : ℤ) : E) • 1) 1 0 = 1 := by
      rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
      simp [smul_smul, hee]
    have h1 := congrArg Matrix.det hM
    rw [Matrix.det_mul, ← hε, Matrix.det_mul, Matrix.det_mul, dbl, Matrix.det_fromBlocks_zero₂₁, hz] at h1
    simp at h1
  have hκ : Fintype.card d.κ = Fintype.card (Fin d.m) * Fintype.card (Fin d.n ⊕ Fin d.n) := by
    have : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
    let bE : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E h2
    let bA := Algebra.TensorProduct.basis (AF F) bE
    haveI : Module.Free (AF F) (AE F E) := Module.Free.of_basis bA
    haveI : Module.Finite (AF F) (AE F E) := Module.Finite.of_basis bA
    have e := d.dd.e.finrank_eq
    rw [Module.finrank_matrix, Module.finrank_eq_card_basis bA, Module.finrank_prod,
      Module.finrank_fintype_fun_eq_card] at e
    simp only [Fintype.card_fin, Fintype.card_sum] at e ⊢
    omega
  obtain ⟨d₀, hd₀⟩ := exists_ratCoord h2 hκ d.dd.e d.ok.dbl.rat
  obtain ⟨a, b, hab, hA, hB⟩ : ∃ a b : E, -1 = δ * a * b ∧ IsHerm σ (a • d.A.J) ∧ IsHerm σ (b • d.Y.J) := by
    rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
    · refine ⟨1, -δ⁻¹, by field_simp, ?_, ?_⟩
      · rw [one_smul]; exact ⟨hA.herm, (herm_det hA).isUnit⟩
      · refine ⟨fun i j => by simp [hY i j, hq.anti], Ne.isUnit ?_⟩
        rw [Matrix.det_smul]
        exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero h0))) hYd
    · refine ⟨-δ⁻¹, 1, by field_simp, ?_, ?_⟩
      · refine ⟨fun i j => by simp [hA.skew i j, hq.anti], Ne.isUnit ?_⟩
        rw [Matrix.det_smul]
        exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero h0))) (skew_det hA)
      · rw [one_smul]; exact ⟨hY, hYd.isUnit⟩
  have hb : b ≠ 0 := by
    rintro rfl
    simp at hab
  have hξ : (-1 : AE F E) = inclR (F := F) (AF F) δ * inclR (F := F) (AF F) a * inclR (F := F) (AF F) b := by
    rw [← map_mul, ← map_mul, ← hab, map_neg, map_one]
  have hJA : incM F (a • d.A.J) = inclR (F := F) (AF F) a • incM F d.A.J := by
    ext i j; simp [incM]
  have hJB : incM F (dbl (b • d.Y.J)) = inclR (F := F) (AF F) b • dbl (incM F d.Y.J) := by
    ext (i | i) (j | j) <;> simp [incM, dbl]
  obtain ⟨d', om', he, hS', hR', hgg⟩ := split_resc (c := cA σ) (C := adeleClass F) (ψ := d.B.ψ) (κ := d.κ) hξ
    (hb.isUnit.map (inclR (F := F) (AF F))) hJA hJB hS.toIsSplitting hR
  have hd' : ∀ x, d'.e (incM F x) = (fun i => algebraMap F (AF F) ((d₀ x).1 i), fun i => algebraMap F (AF F) ((d₀ x).2 i)) :=
    fun x => by rw [he]; exact hd₀ x
  obtain ⟨g', hg'1, hg'2⟩ := hgg γ
  have hg : ∃ γ₀ : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E,
      ((g' : GL (Fin d.n ⊕ Fin d.n) (AE F E)) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) = incM F γ₀ := by
    obtain ⟨g₀, hg₀⟩ := Subgroup.mem_subgroupOf.mp hγ
    refine ⟨g₀, ?_⟩
    rw [hg'1, ← hg₀]
    rfl
  rw [← hg'2]
  exact split_core hψ hq (a • d.A.J) (b • d.Y.J) hA hB d' d₀ hd' d.χ d.ok.hecke om' hS' hR' g' hg Ψ hΨ
end PositivityTheory.SiegelWeilFormula.Tauto
end
end
