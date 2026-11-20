import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFockOfThetaSquareIntegrable

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockIsometry

open Complex GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars GlobalTheory.VacuumFockLaws
open scoped Classical ComplexConjugate

variable {D : D7} {V W : HSp D}

/- English proof (translation)
Take `⟨τ, i, j⟩` from `k`. Take `⟨τ', i', j'⟩` from `l`. Distinguish the cases in `hτ : τ = τ'`. Substitute `hτ` using the available equality. Apply the tactic sequence `have htr := GlobalTheory.FockVecInj.trace_unitMap (G := gramAt D V τ) (G' := gramAt D W τ) (ε := fun a => ((ε τ a : ℝ) : ℂ)) (ε' := fun a => ((ε' τ a : ℝ) : ℂ)) (fun a => by rcases hε τ a with h | h <;> simp [h]) (hB τ) (hB' τ) i j i' j'`.

Establish `hh : hermAt V W τ (c • unitMap (B τ) (B' τ) i j) (c' • unitMap (B τ) (B' τ) i' j') = (c * conj c') * (if i = i' ∧ j = j' then ((ε' τ i : ℝ) : ℂ) * ((ε τ j : ℝ) : ℂ) else 0)`. Rewrite using `[← htr]`. Simplify using `only [hermAt, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [commScalar, symplAt, hh]`.

Distinguish the cases in `hij : i = i' ∧ j = j'`. Take `⟨rfl, rfl⟩` from `hij`. Simplify using the standard rewrite rules. Establish `hne : ¬ ((τ, i, j) : FVar D W.rank V.rank) = (τ, i', j')`. Introduce `h`.

Conclude with `hij ⟨congrArg (fun x => x.2.1) h, congrArg (fun x => x.2.2) h⟩`. Rewrite using `[if_neg hij, if_neg hne]`. Simplify using the standard rewrite rules. Establish `hne : ¬ ((τ, i, j) : FVar D W.rank V.rank) = (τ', i', j')` using `fun h => hτ (congrArg Prod.fst h)`. Simplify using `only [commScalar, if_neg hτ, if_neg hne]`.
-/
theorem commScalar_unitMap {B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {B' : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ} {ε : D.what₂.Tau → Fin V.rank → ℝ}
    {ε' : D.what₂.Tau → Fin W.rank → ℝ} (hε : ∀ τ a, ε τ a = 1 ∨ ε τ a = -1)
    (hB : ∀ τ, (B τ)ᴴ * gramAt D V τ * B τ = diagonal fun a => (ε τ a : ℂ))
    (hB' : ∀ τ, (B' τ)ᴴ * gramAt D W τ * B' τ = diagonal fun a => (ε' τ a : ℂ))
    (c c' : ℂ) (k l : FVar D W.rank V.rank) :
    commScalar V W k.1 l.1 (c • unitMap (B k.1) (B' k.1) k.2.1 k.2.2) (c' • unitMap (B l.1) (B' l.1) l.2.1 l.2.2) =
      if k = l then -(2 * Real.pi * I) *
        ((2 * (tauE D k.1 D.host.xi0 * (c * conj c' * ((ε' k.1 k.2.1 * ε k.1 k.2.2 : ℝ) : ℂ))).re : ℝ) : ℂ)
      else 0 := by
  obtain ⟨τ, i, j⟩ := k
  obtain ⟨τ', i', j'⟩ := l
  by_cases hτ : τ = τ'
  · subst hτ
    have htr := GlobalTheory.FockVecInj.trace_unitMap (G := gramAt D V τ) (G' := gramAt D W τ)
      (ε := fun a => ((ε τ a : ℝ) : ℂ)) (ε' := fun a => ((ε' τ a : ℝ) : ℂ))
      (fun a => by rcases hε τ a with h | h <;> simp [h]) (hB τ) (hB' τ) i j i' j'
    have hh : hermAt V W τ (c • unitMap (B τ) (B' τ) i j) (c' • unitMap (B τ) (B' τ) i' j') =
        (c * conj c') * (if i = i' ∧ j = j' then ((ε' τ i : ℝ) : ℂ) * ((ε τ j : ℝ) : ℂ) else 0) := by
      rw [← htr]
      simp only [hermAt, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
        smul_eq_mul, Complex.star_def]
      ring
    simp only [commScalar, symplAt, hh]
    by_cases hij : i = i' ∧ j = j'
    · obtain ⟨rfl, rfl⟩ := hij
      simp
    · have hne : ¬ ((τ, i, j) : FVar D W.rank V.rank) = (τ, i', j') := by
        intro h
        exact hij ⟨congrArg (fun x => x.2.1) h, congrArg (fun x => x.2.2) h⟩
      rw [if_neg hij, if_neg hne]
      simp
  · have hne : ¬ ((τ, i, j) : FVar D W.rank V.rank) = (τ', i', j') := fun h => hτ (congrArg Prod.fst h)
    simp only [commScalar, if_neg hτ, if_neg hne]

/- English proof (translation)
Establish `h` using `commScalar_unitMap (B := BS) (B' := BT) hεS hBS hBT c 1 k l`. Rewrite `h` using `[GlobalTheory.ThetaSquare.commScalar_eq, one_smul, map_one, mul_one]`. Establish `h2 : (-(2 * (Real.pi : ℂ) * I)) ≠ 0`. Simplify using `[Real.pi_ne_zero, Complex.I_ne_zero]`. Use `split_ifs at h ⊢ with hkl`.

Conclude with `mul_left_cancel₀ h2 h` after adjusting the coercions. Conclude with `mul_left_cancel₀ h2 (h.trans (mul_zero _).symm)` after adjusting the coercions.
-/
private theorem omDir_smul_unitMap_unitMap_eq_ite {S T : HSp D} {BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {εS : D.what₂.Tau → Fin S.rank → ℝ}
    {εT : D.what₂.Tau → Fin T.rank → ℝ} (hεS : ∀ τ a, εS τ a = 1 ∨ εS τ a = -1)
    (hBS : ∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = diagonal fun a => (εS τ a : ℂ))
    (hBT : ∀ τ, (BT τ)ᴴ * gramAt D T τ * BT τ = diagonal fun a => (εT τ a : ℂ))
    (c : ℂ) (k l : FVar D T.rank S.rank) :
    GlobalTheory.FockIndep.omDir S T k.1 (c • unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) l.1
                 (unitMap (BS l.1) (BT l.1) l.2.1 l.2.2) =
      if k = l then 2 * (tauE D k.1 D.host.xi0 * (c * ((εT k.1 k.2.1 * εS k.1 k.2.2 : ℝ) : ℂ))).re else 0 := by
  have h := commScalar_unitMap (B := BS) (B' := BT) hεS hBS hBT c 1 k l
  rw [GlobalTheory.ThetaSquare.commScalar_eq, one_smul, map_one, mul_one] at h
  have h2 : (-(2 * (Real.pi : ℂ) * I)) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  split_ifs at h ⊢ with hkl
  · exact_mod_cast mul_left_cancel₀ h2 h
  · exact_mod_cast mul_left_cancel₀ h2 (h.trans (mul_zero _).symm)

/- English proof (translation)
Establish `e1` using `omDir_smul_unitMap_unitMap_eq_ite hεS hBS hBT 1 k l`. Rewrite `e1` using `[one_smul]`. Establish `e2` using `omDir_smul_unitMap_unitMap_eq_ite hεS hBS hBT (I * ((εT k.1 k.2.1 : ℂ) * (εS k.1 k.2.2 : ℂ))) k l`. Establish `hc` using `GlobalTheory.FockVecInj.cplxO_unitMap (hdet k.1) (hsS k.1) (hsT k.1) k.2.1 k.2.2`. Rewrite `e2` using `[← hc]`.

Rewrite using `[e1, e2]`. Use `split_ifs with hkl`. Substitute `hkl` using the available equality. Establish `hx` using `GlobalTheory.OrientedRealForm.realPlace_imaginaryGenerator_re_eq_zero (D := D) k.1`. Establish `hs` using `GlobalTheory.VacuumFockLaws.fockScale_sq (D := D) k.1`.

Establish `hne` using `GlobalTheory.VacuumFockLaws.fockScale_ne (D := D) k.1`. Establish `hab : ((εT k.1 k.2.1 : ℂ) * (εS k.1 k.2.2 : ℂ)) * ((εT k.1 k.2.1 : ℂ) * (εS k.1 k.2.2 : ℂ)) = 1`. Apply the tactic sequence `rcases hεT k.1 k.2.1 with h | h <;> rcases hεS k.1 k.2.2 with h' | h' <;> simp [h, h']`. Establish `r1 : (tauE D k.1 D.host.xi0 * (1 * ((εT k.1 k.2.1 * εS k.1 k.2.2 : ℝ) : ℂ))).re = 0`. Simplify using `[Complex.mul_re, hx]`.

Establish `r2 : (tauE D k.1 D.host.xi0 * (I * ((εT k.1 k.2.1 : ℂ) * (εS k.1 k.2.2 : ℂ)) * ((εT k.1 k.2.1 * εS k.1 k.2.2 : ℝ) : ℂ))).re = -(tauE D k.1 D.host.xi0).im`. Establish `hI : I * ((εT k.1 k.2.1 : ℂ) * (εS k.1 k.2.2 : ℂ)) * ((εT k.1 k.2.1 * εS k.1 k.2.2 : ℝ) : ℂ) = I`. Use `push_cast`. Take the linear combination `I * hab`. Rewrite using `[hI]`.

Simplify using `[Complex.mul_re]`. Rewrite using `[r1, r2]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Take the linear combination `(-1 : ℂ) * hs + (-(8 * (Real.pi : ℂ) * ((tauE D k.1 D.host.xi0).im : ℂ))) * Complex.I_sq`.

Simplify using the standard rewrite rules.
-/
private theorem scal_lemma_2 {S T : HSp D} {sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {εS : D.what₂.Tau → Fin S.rank → ℝ}
    {εT : D.what₂.Tau → Fin T.rank → ℝ} (hεS : ∀ τ a, εS τ a = 1 ∨ εS τ a = -1)
    (hεT : ∀ τ a, εT τ a = 1 ∨ εT τ a = -1)
    (hBS : ∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = diagonal fun a => (εS τ a : ℂ))
    (hBT : ∀ τ, (BT τ)ᴴ * gramAt D T τ * BT τ = diagonal fun a => (εT τ a : ℂ))
    (hsS : ∀ τ, sS τ * BS τ = BS τ * diagonal fun a => (εS τ a : ℂ))
    (hsT : ∀ τ, sT τ * BT τ = BT τ * diagonal fun a => (εT τ a : ℂ))
    (hdet : ∀ τ, IsUnit (BS τ).det) (k l : FVar D T.rank S.rank) :
    (-(fockScale D k.1 : ℂ)⁻¹) * ((fockScale D l.1 : ℂ)⁻¹ * (-(4 * (Real.pi : ℂ) * I) *
      ((GlobalTheory.FockIndep.omDir S T k.1 (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) l.1
          (unitMap (BS l.1) (BT l.1) l.2.1 l.2.2) : ℝ) +
        I * (GlobalTheory.FockIndep.omDir S T k.1 (cplxO (sS k.1) (sT k.1) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2)) l.1
          (unitMap (BS l.1) (BT l.1) l.2.1 l.2.2) : ℝ)))) = if k = l then 1 else 0 := by
  have e1 := omDir_smul_unitMap_unitMap_eq_ite hεS hBS hBT 1 k l
  rw [one_smul] at e1
  have e2 := omDir_smul_unitMap_unitMap_eq_ite hεS hBS hBT (I * ((εT k.1 k.2.1 : ℂ) * (εS k.1 k.2.2 : ℂ))) k l
  have hc := GlobalTheory.FockVecInj.cplxO_unitMap (hdet k.1) (hsS k.1) (hsT k.1) k.2.1 k.2.2
  rw [← hc] at e2
  rw [e1, e2]
  split_ifs with hkl
  · subst hkl
    have hx := GlobalTheory.OrientedRealForm.realPlace_imaginaryGenerator_re_eq_zero (D := D) k.1
    have hs := GlobalTheory.VacuumFockLaws.fockScale_sq (D := D) k.1
    have hne := GlobalTheory.VacuumFockLaws.fockScale_ne (D := D) k.1
    have hab : ((εT k.1 k.2.1 : ℂ) * (εS k.1 k.2.2 : ℂ)) * ((εT k.1 k.2.1 : ℂ) * (εS k.1 k.2.2 : ℂ)) = 1 := by
      rcases hεT k.1 k.2.1 with h | h <;> rcases hεS k.1 k.2.2 with h' | h' <;> simp [h, h']
    have r1 : (tauE D k.1 D.host.xi0 * (1 * ((εT k.1 k.2.1 * εS k.1 k.2.2 : ℝ) : ℂ))).re = 0 := by
      simp [Complex.mul_re, hx]
    have r2 : (tauE D k.1 D.host.xi0 * (I * ((εT k.1 k.2.1 : ℂ) * (εS k.1 k.2.2 : ℂ)) *
        ((εT k.1 k.2.1 * εS k.1 k.2.2 : ℝ) : ℂ))).re = -(tauE D k.1 D.host.xi0).im := by
      have hI : I * ((εT k.1 k.2.1 : ℂ) * (εS k.1 k.2.2 : ℂ)) * ((εT k.1 k.2.1 * εS k.1 k.2.2 : ℝ) : ℂ) = I := by
        push_cast
        linear_combination I * hab
      rw [hI]
      simp [Complex.mul_re]
    rw [r1, r2]
    push_cast
    field_simp
    linear_combination (-1 : ℂ) * hs + (-(8 * (Real.pi : ℂ) * ((tauE D k.1 D.host.xi0).im : ℂ))) * Complex.I_sq
  · simp

/- English proof (translation)
Introduce `D ψ θ S T hψ hθ sS BS sT BT pS pT _ _ hcS hcT hoS hoT f hf hvac μ 𝓕 hcov P Q`. Take `⟨hHaar, hFD, -⟩` from `hcov`. Establish `hoS' : ∀ ρ, ∃ ε : Fin S.rank → ℝ, (∀ a, ε a = 1 ∧ (a : ℕ) < pS ρ ∨ ε a = -1 ∧ pS ρ ≤ (a : ℕ)) ∧ ((BS ρ)ᴴ * gramAt D S ρ * BS ρ = diagonal fun a => (ε a : ℂ)) ∧ sS ρ * BS ρ = BS ρ * diagonal fun a => (ε a : ℂ)` using `hoS`. Establish `hoT' : ∀ ρ, ∃ ε : Fin T.rank → ℝ, (∀ a, ε a = 1 ∧ (a : ℕ) < pT ρ ∨ ε a = -1 ∧ pT ρ ≤ (a : ℕ)) ∧ ((BT ρ)ᴴ * gramAt D T ρ * BT ρ = diagonal fun a => (ε a : ℂ)) ∧ sT ρ * BT ρ = BT ρ * diagonal fun a => (ε a : ℂ)` using `hoT`. Use `choose εS hεS using hoS'`.

Use `choose εT hεT using hoT'`. Establish `hεS1 : ∀ ρ a, εS ρ a = 1 ∨ εS ρ a = -1` using `fun ρ a => ((hεS ρ).1 a).imp And.left And.left`. Establish `hεT1 : ∀ ρ a, εT ρ a = 1 ∨ εT ρ a = -1` using `fun ρ a => ((hεT ρ).1 a).imp And.left And.left`. Establish `hdet : ∀ ρ, IsUnit (BS ρ).det`. Introduce `ρ`.

Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`. Establish `hd` using `congrArg Matrix.det (hεS ρ).2.1`. Rewrite `hd` using `[Matrix.det_mul, Matrix.det_mul, h0, mul_zero, Matrix.det_diagonal]`. Use `(Finset.prod_ne_zero_iff.mpr fun a _ => ?_) hd.symm` and prove the remaining obligations.

Apply the tactic sequence `rcases hεS1 ρ a with h | h <;> simp [h]`. Set `a : FVar D T.rank S.rank → Module.End ℂ (thetaSub S T ψ)` to `fun k => { toFun := fun g => ⟨aPlus (heisO ψ S T) θ k.1 (cplxO (sS k.1) (sT k.1)) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) g, GlobalTheory.FockIndep.aPlus_theta hψ hθ k.1 (cplxO (sS k.1) (sT k.1)) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) g.2⟩ map_add' := fun g g' => Subtype.ext (Gl …`. Set `e : FVar D T.rank S.rank → Module.End ℂ (thetaSub S T ψ)` to `fun k => { toFun := fun g => ⟨annih (heisO ψ S T) θ k.1 (cplxO (sS k.1) (sT k.1)) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) g, GlobalTheory.FockIndep.annih_theta hψ hθ k.1 (cplxO (sS k.1) (sT k.1)) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) g.2⟩ map_add' := fun g g' => Subtype.ext (Gl …`. Set `b : FVar D T.rank S.rank → Module.End ℂ (thetaSub S T ψ)` to `fun k => (-(fockScale D k.1 : ℂ)⁻¹) • e k`. Establish `haa : ∀ i j g, a i (a j g) = a j (a i g)` using `fun i j g => Subtype.ext (GlobalTheory.FockIndep.aPlus_comm' (hψ := hψ) (hθ := hθ) (hS := hcS) (hT := hcT) (τ := i.1) (z := unitMap (BS i.1) (BT i.1) i.2.1 i.2.2) (τ' := j.1) (z' := unitMap (BS j.1) (BT j.1) j.2.1 j.2.2) (hf := g.2))`.

Establish `hba : ∀ i j g, b i (a j g) = a j (b i g) + (if i = j then (1 : ℂ) else 0) • g`. Introduce `i j g`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `hg : IsThetaFunO ψ S T g` using `g.2`. Establish `hag` using `GlobalTheory.FockIndep.annih_theta hψ hθ i.1 (cplxO (sS i.1) (sT i.1)) (unitMap (BS i.1) (BT i.1) i.2.1 i.2.2) hg`.

Express the relevant statement in the definitionally equal form `(-(fockScale D i.1 : ℂ)⁻¹) • annih (heisO ψ S T) θ i.1 (cplxO (sS i.1) (sT i.1)) (unitMap (BS i.1) (BT i.1) i.2.1 i.2.2) (aPlus (heisO ψ S T) θ j.1 (cplxO (sS j.1) (sT j.1)) (unitMap (BS j.1) (BT j.1) j.2.1 j.2.2) g) = aPlus (heisO ψ S T) θ j.1 (cplxO (sS j.1) (sT j.1)) (unitMap …`. Rewrite using `[GlobalTheory.FockIndep.annih_aPlus (hψ := hψ) (hθ := hθ) (hS := hcS) (hT := hcT) (hf := hg), GlobalTheory.FockIndep.aPlus_smul hψ hθ j.1 (cplxO (sS j.1) (sT j.1)) (unitMap (BS j.1) (BT j.1) j.2.1 j.2.2) _ hag, smul_add, smul_smul, scal_lemma_2 hεS1 hεT1 (fun ρ => (hεS ρ).2.1) (f …`. Establish `hvac' : ∀ i, b i ⟨f, hf⟩ = 0` using `fun i => Subtype.ext (by`. Express the relevant statement in the definitionally equal form `(-(fockScale D i.1 : ℂ)⁻¹) • annih (heisO ψ S T) θ i.1 (cplxO (sS i.1) (sT i.1)) (unitMap (BS i.1) (BT i.1) i.2.1 i.2.2) f = 0`. Rewrite using `[hvac i.1 (unitMap (BS i.1) (BT i.1) i.2.1 i.2.2), smul_zero])`.

Take `⟨hmem, hip⟩` from `fock_of_ccr (thetaSub S T ψ) (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) a b (fun _ _ => rfl) haa (fun i j g => by convert hba i j g) ⟨f, hf⟩ hvac'`. Establish `thd : ∀ τ z (x : WO S T → ℂ), IsThetaFunO ψ S T x → IsThetaFunO ψ S T (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z x)` using `fun τ z x hx => (GlobalTheory.ThetaSquare.derSkew hψ hθ τ z).2.1 x hx`. Establish `sk : ∀ τ z (x y : WO S T → ℂ), IsThetaFunO ψ S T x → IsThetaFunO ψ S T y → GlobalTheory.Ker.ipO μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z x) y = -GlobalTheory.Ker.ipO μ 𝓕 x (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z y)` using `fun τ z x y hx hy => (GlobalTheory.ThetaSquare.derSkew hψ hθ τ z).2.2 μ 𝓕 hHaar hFD x y hx hy`. Establish `hann : ∀ τ z (g : WO S T → ℂ), annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z g = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g + I • Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ) z) g` using `fun _ _ _ => rfl`. Establish `hconj : ∀ τ, starRingEnd ℂ (-(fockScale D τ : ℂ)⁻¹) = -(fockScale D τ : ℂ)⁻¹` using `fun τ => by`.

Rewrite using `[map_neg, map_inv₀, Complex.conj_ofReal]`. Establish `hadj1 : ∀ i (x y : thetaSub S T ψ), GlobalTheory.Ker.ipO μ 𝓕 (a i x) y = GlobalTheory.Ker.ipO μ 𝓕 x (b i y)`. Introduce `i x y`. Establish `hx : IsThetaFunO ψ S T x` using `x.2`. Establish `hy : IsThetaFunO ψ S T y` using `y.2`.

Express the relevant statement in the definitionally equal form `GlobalTheory.Ker.ipO μ 𝓕 (aPlus (heisO ψ S T) θ i.1 (cplxO (sS i.1) (sT i.1)) (unitMap (BS i.1) (BT i.1) i.2.1 i.2.2) x) y = GlobalTheory.Ker.ipO μ 𝓕 x ((-(fockScale D i.1 : ℂ)⁻¹) • annih (heisO ψ S T) θ i.1 (cplxO (sS i.1) (sT i.1)) (unitMap (BS i.1) (BT i.1) i.2.1 i.2.2) y)`. Rewrite using `[GlobalTheory.FockIndep.aPlus_eq, hann, GlobalTheory.Size.ipO_smul_left, GlobalTheory.Size.ipO_add_left hψ hHaar hFD (thd _ _ _ hx) (GlobalTheory.OrientedHeis.theta_smul _ (thd _ _ _ hx)) hy, GlobalTheory.Size.ipO_smul_left, sk _ _ _ _ hx hy, sk _ _ _ _ hx hy, GlobalTheory.Size.i …`. Expand and normalize the polynomial expressions, which then agree. Establish `hadj2 : ∀ i (x y : thetaSub S T ψ), GlobalTheory.Ker.ipO μ 𝓕 x (a i y) = GlobalTheory.Ker.ipO μ 𝓕 (b i x) y`. Introduce `i x y`.

Establish `hx : IsThetaFunO ψ S T x` using `x.2`. Establish `hy : IsThetaFunO ψ S T y` using `y.2`. Express the relevant statement in the definitionally equal form `GlobalTheory.Ker.ipO μ 𝓕 x (aPlus (heisO ψ S T) θ i.1 (cplxO (sS i.1) (sT i.1)) (unitMap (BS i.1) (BT i.1) i.2.1 i.2.2) y) = GlobalTheory.Ker.ipO μ 𝓕 ((-(fockScale D i.1 : ℂ)⁻¹) • annih (heisO ψ S T) θ i.1 (cplxO (sS i.1) (sT i.1)) (unitMap (BS i.1) (BT i.1) i.2.1 i.2.2) x) y`. Rewrite using `[GlobalTheory.FockIndep.aPlus_eq, hann, GlobalTheory.Size.ipO_smul_right, GlobalTheory.Size.ipO_add_right hψ hHaar hFD hx (thd _ _ _ hy) (GlobalTheory.OrientedHeis.theta_smul _ (thd _ _ _ hy)), GlobalTheory.Size.ipO_smul_right, GlobalTheory.Size.ipO_smul_left, GlobalTheory.Size.i …`. Expand and normalize the polynomial expressions, which then agree.

Establish `hzero : ∀ x : WO S T → ℂ, GlobalTheory.Ker.ipO μ 𝓕 x 0 = 0` using `fun x => by`. Simplify using `[GlobalTheory.Ker.ipO]`. Establish `key : ∀ β R, GlobalTheory.Ker.ipO μ 𝓕 (pureTensorO ψ θ S T sS sT BS BT f R) (pureTensorO ψ θ S T sS sT BS BT f (MvPolynomial.monomial β 1)) = R.coeff β * ((GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.multiFact β : ℂ) * GlobalTheory.Ker.ipO μ 𝓕 f f)` using `hip (GlobalTheory.Ker.ipO μ 𝓕) (fun x y z => GlobalTheory.Size.ipO_add_left hψ hHaar hFD x.2 y.2 z.2) (fun c x z => GlobalTheory.Size.ipO_smul_left μ 𝓕 c x z) hzero hadj1 hadj2`. Establish `mem : ∀ R, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f R)` using `hmem`. Express the relevant statement in the definitionally equal form `GlobalTheory.Ker.ipO μ 𝓕 _ _ = _`.

Rewrite using `[← GlobalTheory.Size.ipO_self]`. Use `MvPolynomial.induction_on' Q (fun u c => ?_) (fun p q hp hq => ?_)` and prove the remaining obligations. Rewrite using `[show MvPolynomial.monomial u c = c • MvPolynomial.monomial u (1 : ℂ) by`. Rewrite using `[MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul, GlobalTheory.Size.ipO_smul_right, key]`. Establish `hF : fockIp P (c • MvPolynomial.monomial u (1 : ℂ)) = P.coeff u * starRingEnd ℂ c * (GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.multiFact u : ℂ)`.

Rewrite using `[MvPolynomial.smul_monomial, smul_eq_mul, mul_one]`. Unfold `fockIp`. Rewrite using `[Finset.sum_eq_single u]`. Simplify using `[MvPolynomial.coeff_monomial, GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.multiFact]`. Introduce `k _ hk`.

Simplify using `[MvPolynomial.coeff_monomial, Ne.symm hk]`. Introduce `hu`. Rewrite `hu` using `[MvPolynomial.mem_support_iff, not_not]`. Simplify using `[hu]`. Rewrite using `[hF]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_add, GlobalTheory.Size.ipO_add_right hψ hHaar hFD (mem P) (mem p) (mem q), hp, hq]`. Simplify using `only [fockIp, MvPolynomial.coeff_add, map_add, mul_add, add_mul, Finset.sum_add_distrib]`.
-/
theorem ipO_pureTensorO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ f, IsThetaFunO ψ S T f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ P Q, ipO μ 𝓕 (pureTensorO ψ θ S T sS sT BS BT f P) (pureTensorO ψ θ S T sS sT BS BT f Q) = fockIp P Q * (nrm2 μ 𝓕 f : ℂ) := by
  intro D ψ θ S T hψ hθ sS BS sT BT pS pT _ _ hcS hcT hoS hoT f hf hvac μ 𝓕 hcov P Q
  obtain ⟨hHaar, hFD, -⟩ := hcov
  have hoS' : ∀ ρ, ∃ ε : Fin S.rank → ℝ, (∀ a, ε a = 1 ∧ (a : ℕ) < pS ρ ∨ ε a = -1 ∧ pS ρ ≤ (a : ℕ)) ∧
      ((BS ρ)ᴴ * gramAt D S ρ * BS ρ = diagonal fun a => (ε a : ℂ)) ∧
      sS ρ * BS ρ = BS ρ * diagonal fun a => (ε a : ℂ) := hoS
  have hoT' : ∀ ρ, ∃ ε : Fin T.rank → ℝ, (∀ a, ε a = 1 ∧ (a : ℕ) < pT ρ ∨ ε a = -1 ∧ pT ρ ≤ (a : ℕ)) ∧
      ((BT ρ)ᴴ * gramAt D T ρ * BT ρ = diagonal fun a => (ε a : ℂ)) ∧
      sT ρ * BT ρ = BT ρ * diagonal fun a => (ε a : ℂ) := hoT
  choose εS hεS using hoS'
  choose εT hεT using hoT'
  have hεS1 : ∀ ρ a, εS ρ a = 1 ∨ εS ρ a = -1 := fun ρ a => ((hεS ρ).1 a).imp And.left And.left
  have hεT1 : ∀ ρ a, εT ρ a = 1 ∨ εT ρ a = -1 := fun ρ a => ((hεT ρ).1 a).imp And.left And.left
  have hdet : ∀ ρ, IsUnit (BS ρ).det := by
    intro ρ
    rw [isUnit_iff_ne_zero]
    intro h0
    have hd := congrArg Matrix.det (hεS ρ).2.1
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero, Matrix.det_diagonal] at hd
    refine (Finset.prod_ne_zero_iff.mpr fun a _ => ?_) hd.symm
    rcases hεS1 ρ a with h | h <;> simp [h]

  let a : FVar D T.rank S.rank → Module.End ℂ (thetaSub S T ψ) := fun k =>
    { toFun := fun g => ⟨aPlus (heisO ψ S T) θ k.1 (cplxO (sS k.1) (sT k.1)) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) g,
        GlobalTheory.FockIndep.aPlus_theta hψ hθ k.1 (cplxO (sS k.1) (sT k.1)) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) g.2⟩
      map_add' := fun g g' => Subtype.ext (GlobalTheory.FockIndep.aPlus_add hψ hθ k.1 (cplxO (sS k.1) (sT k.1))
        (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) g.2 g'.2)
      map_smul' := fun c g => Subtype.ext (GlobalTheory.FockIndep.aPlus_smul hψ hθ k.1 (cplxO (sS k.1) (sT k.1))
        (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) c g.2) }
  let e : FVar D T.rank S.rank → Module.End ℂ (thetaSub S T ψ) := fun k =>
    { toFun := fun g => ⟨annih (heisO ψ S T) θ k.1 (cplxO (sS k.1) (sT k.1)) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) g,
        GlobalTheory.FockIndep.annih_theta hψ hθ k.1 (cplxO (sS k.1) (sT k.1)) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) g.2⟩
      map_add' := fun g g' => Subtype.ext (GlobalTheory.FockIndep.annih_add hψ hθ k.1 (cplxO (sS k.1) (sT k.1))
        (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) g.2 g'.2)
      map_smul' := fun c g => Subtype.ext (GlobalTheory.FockIndep.annih_smul hψ hθ k.1 (cplxO (sS k.1) (sT k.1))
        (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) c g.2) }
  let b : FVar D T.rank S.rank → Module.End ℂ (thetaSub S T ψ) := fun k => (-(fockScale D k.1 : ℂ)⁻¹) • e k
  have haa : ∀ i j g, a i (a j g) = a j (a i g) := fun i j g => Subtype.ext
    (GlobalTheory.FockIndep.aPlus_comm' (hψ := hψ) (hθ := hθ) (hS := hcS) (hT := hcT) (τ := i.1)
      (z := unitMap (BS i.1) (BT i.1) i.2.1 i.2.2) (τ' := j.1) (z' := unitMap (BS j.1) (BT j.1) j.2.1 j.2.2) (hf := g.2))
  have hba : ∀ i j g, b i (a j g) = a j (b i g) + (if i = j then (1 : ℂ) else 0) • g := by
    intro i j g
    apply Subtype.ext
    have hg : IsThetaFunO ψ S T g := g.2
    have hag := GlobalTheory.FockIndep.annih_theta hψ hθ i.1 (cplxO (sS i.1) (sT i.1)) (unitMap (BS i.1) (BT i.1) i.2.1 i.2.2) hg
    change (-(fockScale D i.1 : ℂ)⁻¹) • annih (heisO ψ S T) θ i.1 (cplxO (sS i.1) (sT i.1))
        (unitMap (BS i.1) (BT i.1) i.2.1 i.2.2) (aPlus (heisO ψ S T) θ j.1 (cplxO (sS j.1) (sT j.1))
          (unitMap (BS j.1) (BT j.1) j.2.1 j.2.2) g) =
      aPlus (heisO ψ S T) θ j.1 (cplxO (sS j.1) (sT j.1)) (unitMap (BS j.1) (BT j.1) j.2.1 j.2.2)
        ((-(fockScale D i.1 : ℂ)⁻¹) • annih (heisO ψ S T) θ i.1 (cplxO (sS i.1) (sT i.1))
          (unitMap (BS i.1) (BT i.1) i.2.1 i.2.2) g) + (if i = j then (1 : ℂ) else 0) • (g : WO S T → ℂ)
    rw [GlobalTheory.FockIndep.annih_aPlus (hψ := hψ) (hθ := hθ) (hS := hcS) (hT := hcT) (hf := hg),
      GlobalTheory.FockIndep.aPlus_smul hψ hθ j.1 (cplxO (sS j.1) (sT j.1)) (unitMap (BS j.1) (BT j.1) j.2.1 j.2.2) _ hag,
      smul_add, smul_smul, scal_lemma_2 hεS1 hεT1 (fun ρ => (hεS ρ).2.1) (fun ρ => (hεT ρ).2.1) (fun ρ => (hεS ρ).2.2)
        (fun ρ => (hεT ρ).2.2) hdet i j]
  have hvac' : ∀ i, b i ⟨f, hf⟩ = 0 := fun i => Subtype.ext (by
    change (-(fockScale D i.1 : ℂ)⁻¹) • annih (heisO ψ S T) θ i.1 (cplxO (sS i.1) (sT i.1))
      (unitMap (BS i.1) (BT i.1) i.2.1 i.2.2) f = 0
    rw [hvac i.1 (unitMap (BS i.1) (BT i.1) i.2.1 i.2.2), smul_zero])
  obtain ⟨hmem, hip⟩ := fock_of_ccr (thetaSub S T ψ) (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT)
    a b (fun _ _ => rfl) haa (fun i j g => by convert hba i j g) ⟨f, hf⟩ hvac'

  have thd : ∀ τ z (x : WO S T → ℂ), IsThetaFunO ψ S T x →
      IsThetaFunO ψ S T (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z x) :=
    fun τ z x hx => (GlobalTheory.ThetaSquare.derSkew hψ hθ τ z).2.1 x hx
  have sk : ∀ τ z (x y : WO S T → ℂ), IsThetaFunO ψ S T x → IsThetaFunO ψ S T y →
      GlobalTheory.Ker.ipO μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z x) y =
        -GlobalTheory.Ker.ipO μ 𝓕 x (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z y) :=
    fun τ z x y hx hy => (GlobalTheory.ThetaSquare.derSkew hψ hθ τ z).2.2 μ 𝓕 hHaar hFD x y hx hy
  have hann : ∀ τ z (g : WO S T → ℂ), annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z g =
      Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g +
        I • Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ) z) g := fun _ _ _ => rfl
  have hconj : ∀ τ, starRingEnd ℂ (-(fockScale D τ : ℂ)⁻¹) = -(fockScale D τ : ℂ)⁻¹ := fun τ => by
    rw [map_neg, map_inv₀, Complex.conj_ofReal]
  have hadj1 : ∀ i (x y : thetaSub S T ψ), GlobalTheory.Ker.ipO μ 𝓕 (a i x) y = GlobalTheory.Ker.ipO μ 𝓕 x (b i y) := by
    intro i x y
    have hx : IsThetaFunO ψ S T x := x.2
    have hy : IsThetaFunO ψ S T y := y.2
    change GlobalTheory.Ker.ipO μ 𝓕 (aPlus (heisO ψ S T) θ i.1 (cplxO (sS i.1) (sT i.1))
        (unitMap (BS i.1) (BT i.1) i.2.1 i.2.2) x) y =
      GlobalTheory.Ker.ipO μ 𝓕 x ((-(fockScale D i.1 : ℂ)⁻¹) • annih (heisO ψ S T) θ i.1 (cplxO (sS i.1) (sT i.1))
        (unitMap (BS i.1) (BT i.1) i.2.1 i.2.2) y)
    rw [GlobalTheory.FockIndep.aPlus_eq, hann, GlobalTheory.Size.ipO_smul_left,
      GlobalTheory.Size.ipO_add_left hψ hHaar hFD (thd _ _ _ hx) (GlobalTheory.OrientedHeis.theta_smul _ (thd _ _ _ hx)) hy,
      GlobalTheory.Size.ipO_smul_left, sk _ _ _ _ hx hy, sk _ _ _ _ hx hy, GlobalTheory.Size.ipO_smul_right,
      GlobalTheory.Size.ipO_add_right hψ hHaar hFD hx (thd _ _ _ hy) (GlobalTheory.OrientedHeis.theta_smul _ (thd _ _ _ hy)),
      GlobalTheory.Size.ipO_smul_right, hconj, Complex.conj_I]
    ring
  have hadj2 : ∀ i (x y : thetaSub S T ψ), GlobalTheory.Ker.ipO μ 𝓕 x (a i y) = GlobalTheory.Ker.ipO μ 𝓕 (b i x) y := by
    intro i x y
    have hx : IsThetaFunO ψ S T x := x.2
    have hy : IsThetaFunO ψ S T y := y.2
    change GlobalTheory.Ker.ipO μ 𝓕 x (aPlus (heisO ψ S T) θ i.1 (cplxO (sS i.1) (sT i.1))
        (unitMap (BS i.1) (BT i.1) i.2.1 i.2.2) y) =
      GlobalTheory.Ker.ipO μ 𝓕 ((-(fockScale D i.1 : ℂ)⁻¹) • annih (heisO ψ S T) θ i.1 (cplxO (sS i.1) (sT i.1))
        (unitMap (BS i.1) (BT i.1) i.2.1 i.2.2) x) y
    rw [GlobalTheory.FockIndep.aPlus_eq, hann, GlobalTheory.Size.ipO_smul_right,
      GlobalTheory.Size.ipO_add_right hψ hHaar hFD hx (thd _ _ _ hy) (GlobalTheory.OrientedHeis.theta_smul _ (thd _ _ _ hy)),
      GlobalTheory.Size.ipO_smul_right, GlobalTheory.Size.ipO_smul_left,
      GlobalTheory.Size.ipO_add_left hψ hHaar hFD (thd _ _ _ hx) (GlobalTheory.OrientedHeis.theta_smul _ (thd _ _ _ hx)) hy,
      GlobalTheory.Size.ipO_smul_left, sk _ _ _ _ hx hy, sk _ _ _ _ hx hy, map_inv₀, Complex.conj_ofReal, map_neg,
      Complex.conj_I]
    ring
  have hzero : ∀ x : WO S T → ℂ, GlobalTheory.Ker.ipO μ 𝓕 x 0 = 0 := fun x => by
    simp [GlobalTheory.Ker.ipO]
  have key : ∀ β R, GlobalTheory.Ker.ipO μ 𝓕 (pureTensorO ψ θ S T sS sT BS BT f R)
      (pureTensorO ψ θ S T sS sT BS BT f (MvPolynomial.monomial β 1)) =
        R.coeff β * ((GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.multiFact β : ℂ) * GlobalTheory.Ker.ipO μ 𝓕 f f) :=
    hip (GlobalTheory.Ker.ipO μ 𝓕) (fun x y z => GlobalTheory.Size.ipO_add_left hψ hHaar hFD x.2 y.2 z.2)
      (fun c x z => GlobalTheory.Size.ipO_smul_left μ 𝓕 c x z) hzero hadj1 hadj2
  have mem : ∀ R, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f R) := hmem
  change GlobalTheory.Ker.ipO μ 𝓕 _ _ = _
  rw [← GlobalTheory.Size.ipO_self]
  refine MvPolynomial.induction_on' Q (fun u c => ?_) (fun p q hp hq => ?_)
  · rw [show MvPolynomial.monomial u c = c • MvPolynomial.monomial u (1 : ℂ) by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul, GlobalTheory.Size.ipO_smul_right, key]
    have hF : fockIp P (c • MvPolynomial.monomial u (1 : ℂ)) =
        P.coeff u * starRingEnd ℂ c * (GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.multiFact u : ℂ) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      unfold fockIp
      rw [Finset.sum_eq_single u]
      · simp [MvPolynomial.coeff_monomial, GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.multiFact]
      · intro k _ hk
        simp [MvPolynomial.coeff_monomial, Ne.symm hk]
      · intro hu
        rw [MvPolynomial.mem_support_iff, not_not] at hu
        simp [hu]
    rw [hF]
    ring
  · rw [map_add, GlobalTheory.Size.ipO_add_right hψ hHaar hFD (mem P) (mem p) (mem q), hp, hq]
    simp only [fockIp, MvPolynomial.coeff_add, map_add, mul_add, add_mul, Finset.sum_add_distrib]

end GlobalTheory.FockIsometry
