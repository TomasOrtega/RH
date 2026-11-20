import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EisLeftInv
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilActDefs

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
/- English proof (translation)
Introduce `p hp g`. Take `⟨t, ht⟩` from `mem_parabolic_GL2_iff.1 hp.1`. Take `⟨T, hT⟩` from `par_rat ht hp.2`. Take `⟨u, hu⟩` from `det_rat hT`. Establish `ha : d.a (p * g) = d.a g`.

Rewrite using `[IsHgt.mul d.ok.hgt ht, hu, GlobalTheory.Doubling.absE_inclR]`. Simplify using the standard rewrite rules. Establish `hfp : f (p * g) = f g` using `Law.rat (z := s₁ + (d.n : ℂ) / 2) hf.law d.ok.hecke hp.1 hp.2 g`. Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k, _root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht, ha, hfp]`.
-/
theorem phz_leftInv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (par2 σ d.Y ⊓ rat2 σ d.Y) (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) := by
  intro p hp g
  obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 hp.1
  obtain ⟨T, hT⟩ := par_rat ht hp.2
  obtain ⟨u, hu⟩ := det_rat hT
  have ha : d.a (p * g) = d.a g := by
    rw [IsHgt.mul d.ok.hgt ht, hu, GlobalTheory.Doubling.absE_inclR]; simp
  have hfp : f (p * g) = f g := Law.rat (z := s₁ + (d.n : ℂ) / 2) hf.law d.ok.hecke hp.1 hp.2 g
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k, _root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht, ha, hfp]
/- English proof (translation)
The claim follows from `GlobalTheory.Eis.leftInv_cosetSum (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.phz_leftInv_k d hf z)`.
-/
theorem eis_leftInv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) :
    ∀ γ ∈ rat2 σ d.Y, ∀ g, d.eis f s₁ z (γ * g) = d.eis f s₁ z g :=
  GlobalTheory.Eis.leftInv_cosetSum (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.phz_leftInv_k d hf z)
/- English proof (translation)
Unfold `fc`. Use `h.2.1` as an intermediate fact. Establish `: VAddInvariantMeasure (nF σ d.Y d.b) (nA σ d.Y d.b) lam` using `⟨fun c s _ => measure_preimage_add lam c.1 s⟩`. Use `h.2.2.1.setIntegral_eq h₀.2.2.1 fun β₀ β => ?_` and prove the remaining obligations. Establish `e1 : (β₀ +ᵥ β : nA σ d.Y d.b) = β₀.1 + β` using `rfl`.

Establish `e2 : ((β₀.1 + β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = β₀.1.1 + β.1` using `rfl`. Rewrite using `[e1, kunf.nb_add h.1, mul_assoc, hφ _ (kunf.nb_rat h.1 β₀.2), e2, Matrix.mul_add, Matrix.trace_add, map_add, neg_add, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, kunf.psi_rat d.ok.good.std T β₀, inv_one, one_mul]`.
-/
theorem fc_dom_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 𝓖₀ : Set (nA σ d.Y d.b)}
    (h : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (h₀ : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖₀)
    (φ : d.G → ℂ) (hφ : ∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) (T : nF σ d.Y d.b) (g : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 φ T g = fc d.B.ψ d.b nb lam 𝓖₀ φ T g := by
  unfold fc
  have := h.2.1
  have : VAddInvariantMeasure (nF σ d.Y d.b) (nA σ d.Y d.b) lam := ⟨fun c s _ => measure_preimage_add lam c.1 s⟩
  refine h.2.2.1.setIntegral_eq h₀.2.2.1 fun β₀ β => ?_
  have e1 : (β₀ +ᵥ β : nA σ d.Y d.b) = β₀.1 + β := rfl
  have e2 : ((β₀.1 + β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = β₀.1.1 + β.1 := rfl
  rw [e1, kunf.nb_add h.1, mul_assoc, hφ _ (kunf.nb_rat h.1 β₀.2), e2, Matrix.mul_add, Matrix.trace_add, map_add, neg_add,
    AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, kunf.psi_rat d.ok.good.std T β₀, inv_one, one_mul]
end PositivityTheory.SiegelWeilFormula.Act.C1
end
end
