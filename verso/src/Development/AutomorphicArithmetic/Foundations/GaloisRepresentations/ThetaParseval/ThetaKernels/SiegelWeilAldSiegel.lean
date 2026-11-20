import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Siegel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelSmallK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldSiegelC

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F : Type} [Field F] [NumberField F]
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had' om1 hsp1 hsr1 φ₀ hφ₀ h0 om' hbox`. Introduce `l hl hinv p t hpt φ hφ`. Establish `hψ : IsStd d.B.ψ` using `d.ok.good.std`. Establish `hchar : ∀ (y : Fin d.m × Fin n × Fin 2 → AF F), ∀ φ ∈ schA F (Fin d.m × Fin n × Fin 2), l (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = l φ`. Introduce `y φ hφ`.

Take `⟨z, hz⟩` from `(hAC F E σ d.m n d.bs d.A Y b dd' had' hb).2 y`. Use `hinv z φ hφ` as an intermediate fact. Rewrite `this` using `[Darboux.rho, hz, schr_zero_fst]`. Conclude with `this`. Take `⟨c, hc⟩` from `GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F d.B.ψ hψ (Fin d.m × Fin n × Fin 2) l hl hchar`.

Establish `hbm : boxFun φ φ₀ ∈ schA F (K1 d.m n)` using `GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ hφ φ₀ hφ₀`. Establish `hb1` using `hbox p φ hφ`. Establish `hm1 : boxFun (om' p φ) φ₀ ∈ schA F (K1 d.m n)` using `hb1 ▸ hsp1.pres (j p) _ hbm`. Establish `hmem : om' p φ ∈ schA F (Fin d.m × Fin n × Fin 2)`. Use `(hF F _ _).1 _ hm1` as an intermediate fact.

Rewrite `this` using `[slice0_box_one _ h0]`. Then use the resulting hypothesis. Rewrite using `[hc _ hmem, hc _ hφ]`. Establish `hv : om' p φ 0 = ev0 (K1 d.m n) (om1 (j p) (boxFun φ φ₀))`. Rewrite using `[hb1]`. Simplify using `[ev0, boxFun, h0]`.

Take `⟨t', ht', hdet⟩` from `_root_.PositivityTheory.SiegelWeilFormula.Ald.jPar_k d h hb hj p t hpt`. Establish `hkill : ∀ (z : Matrix (Fin d.m) (Fin d.n) (AE F E)), ∀ Ψ ∈ schA F (K1 d.m n), ev0 (K1 d.m n) ((GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).rho d.B.ψ (z * (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E))ᵀ) Ψ) = ev0 (K1 d.m n) Ψ`. Introduce `z Ψ _`. Establish `h1` using `(hAC F E σ d.m d.n d.bs d.A d.Y d.b dd0 had0 d.ok.frame).1 z`. Rewrite using `[Darboux.rho, GlobalTheory.TowU.reindexD_e, h1]`.

Simplify using `[ev0, schr]`. Establish `key` using `hsr1 (ev0 (K1 d.m n)) (evalZero_mem_adelicSchwartzAdmittedForms _) hkill (j p) t' ht' (boxFun φ φ₀) hbm`. Rewrite using `[hv, key, hdet]`. Simplify using `[ev0, boxFun, h0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem siegelSmall_of_k (hF : SliceFacts) (hAC : AdaptedChar) : _root_.PositivityTheory.SiegelWeilFormula.Ald.SiegelSmall_k := by
  intro F E _ _ _ _ _ σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had' om1 hsp1 hsr1 φ₀ hφ₀ h0 om' hbox
  intro l hl hinv p t hpt φ hφ
  have hψ : IsStd d.B.ψ := d.ok.good.std
  have hchar : ∀ (y : Fin d.m × Fin n × Fin 2 → AF F), ∀ φ ∈ schA F (Fin d.m × Fin n × Fin 2),
      l (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = l φ := by
    intro y φ hφ
    obtain ⟨z, hz⟩ := (hAC F E σ d.m n d.bs d.A Y b dd' had' hb).2 y
    have := hinv z φ hφ
    rw [Darboux.rho, hz, schr_zero_fst] at this
    exact this
  obtain ⟨c, hc⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F d.B.ψ hψ (Fin d.m × Fin n × Fin 2) l hl hchar
  have hbm : boxFun φ φ₀ ∈ schA F (K1 d.m n) := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ hφ φ₀ hφ₀
  have hb1 := hbox p φ hφ
  have hm1 : boxFun (om' p φ) φ₀ ∈ schA F (K1 d.m n) := hb1 ▸ hsp1.pres (j p) _ hbm
  have hmem : om' p φ ∈ schA F (Fin d.m × Fin n × Fin 2) := by
    have := (hF F _ _).1 _ hm1
    rwa [slice0_box_one _ h0] at this
  rw [hc _ hmem, hc _ hφ]
  have hv : om' p φ 0 = ev0 (K1 d.m n) (om1 (j p) (boxFun φ φ₀)) := by
    rw [hb1]
    simp [ev0, boxFun, h0]
  obtain ⟨t', ht', hdet⟩ := _root_.PositivityTheory.SiegelWeilFormula.Ald.jPar_k d h hb hj p t hpt
  have hkill : ∀ (z : Matrix (Fin d.m) (Fin d.n) (AE F E)), ∀ Ψ ∈ schA F (K1 d.m n),
      ev0 (K1 d.m n) ((GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).rho d.B.ψ
        (z * (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E))ᵀ) Ψ) = ev0 (K1 d.m n) Ψ := by
    intro z Ψ _
    have h1 := (hAC F E σ d.m d.n d.bs d.A d.Y d.b dd0 had0 d.ok.frame).1 z
    rw [Darboux.rho, GlobalTheory.TowU.reindexD_e, h1]
    simp [ev0, schr]
  have key := hsr1 (ev0 (K1 d.m n)) (evalZero_mem_adelicSchwartzAdmittedForms _) hkill (j p) t' ht' (boxFun φ φ₀) hbm
  rw [hv, key, hdet]
  simp [ev0, boxFun, h0]
  ring
end PositivityTheory.SiegelWeilFormula.Ald
end
end
