import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PadZeroMemNilradical
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EpsEqK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PadMatrixLowerBlockZero

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
def padZeroAlt (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  fun i k => if h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k then β h.1.choose h.2.choose else 0
/- English proof (translation)
Establish `h : (∃ a', L.em a' = L.em a) ∧ ∃ c', L.em c' = L.em c` using `⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩`. Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt, dif_pos h]`. Rewrite using `[L.inj h.1.choose_spec, L.inj h.2.choose_spec]`.
-/
theorem pad_zero_embedding (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (a c : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt L β (L.em a) (L.em c) = β a c := by
  have h : (∃ a', L.em a' = L.em a) ∧ ∃ c', L.em c' = L.em c := ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt, dif_pos h]
  rw [L.inj h.1.choose_spec, L.inj h.2.choose_spec]
/- English proof (translation)
Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt, dif_neg h]`.
-/
theorem pad_zero_outside (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (i k : Fin d.n)
    (h : ¬ ((∃ a, L.em a = i) ∧ ∃ c, L.em c = k)) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt L β i k = 0 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt, dif_neg h]
/- English proof (translation)
Distinguish the cases in `h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k`. Take `⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩` from `h`. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_embedding, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_embedding]`. Conclude with `h1 a c`. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_outside L β i k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_outside L β k i (fun h' => h ⟨h'.2, h'.1⟩)]`.

Conclude with `h0`.
-/
theorem pad_zero_cases (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (P : AE F E → AE F E → Prop) (h0 : P 0 0)
    (h1 : ∀ a c, P (β a c) (β c a)) (i k : Fin d.n) : P (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt L β i k) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt L β k i) := by
  by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
  · obtain ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩ := h
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_embedding, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_embedding]
    exact h1 a c
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_outside L β i k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_outside L β k i (fun h' => h ⟨h'.2, h'.1⟩)]
    exact h0
/- English proof (translation)
Take `⟨⟨ε, hε⟩, -⟩` from `d.ok.frame`. Take `⟨⟨ε', hε'⟩, -⟩` from `L.ok.frame`. Establish `hee : ε = ε'` using `_root_.PositivityTheory.SiegelWeilFormula.Afc.eps_eq_k L hε hε'`. Substitute `hee` using the available equality. Conclude with `⟨ε, hε, hε'⟩`.
-/
theorem eps_common_k : ∃ ε : ℤˣ, d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 ∧
    L.b.1ᵀ * dbl L.Y.J * L.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨⟨ε', hε'⟩, -⟩ := L.ok.frame
  have hee : ε = ε' := _root_.PositivityTheory.SiegelWeilFormula.Afc.eps_eq_k L hε hε'
  subst hee
  exact ⟨ε, hε, hε'⟩
/- English proof (translation)
Take `⟨ε, hε, hε'⟩` from `_root_.PositivityTheory.SiegelWeilFormula.Act.C4.eps_common_k L`. Rewrite using `[kunf.mem_nA_iff hε]`. Establish `hβ` using `(kunf.mem_nA_iff hε' β.1).1 β.2`. Use extensionality with `i k`. Simplify using `only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply]`.

Use `_root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_cases L β.1 (fun u v => v = -((((ε : ℤ) : AE F E)) • cA σ u)) (by simp) (fun a c => ?_) i k` and prove the remaining obligations. Use `congrFun (congrFun hβ a) c` as an intermediate fact. Simplify `this` using `only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply]`.
-/
theorem pad_zero_mem_unipotent (β : nA σ L.Y L.b) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt L β.1 ∈ nA σ d.Y d.b := by
  obtain ⟨ε, hε, hε'⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.eps_common_k L
  rw [kunf.mem_nA_iff hε]
  have hβ := (kunf.mem_nA_iff hε' β.1).1 β.2
  ext i k
  simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply]
  refine _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_cases L β.1 (fun u v => v = -((((ε : ℤ) : AE F E)) • cA σ u)) (by simp) (fun a c => ?_) i k
  have := congrFun (congrFun hβ a) c
  simpa only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply] using this
def padN_k : nA σ L.Y L.b →+ nA σ d.Y d.b where
  toFun β := ⟨_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt L β.1, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_mem_unipotent L β⟩
  map_zero' := by
    apply Subtype.ext
    ext i k
    refine _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_cases L (0 : nA σ L.Y L.b).1 (fun u _ => u = (0 : Matrix (Fin d.n) (Fin d.n) (AE F E)) i k) rfl
      (fun a c => rfl) i k
  map_add' β β' := by
    apply Subtype.ext
    ext i k
    by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
    · obtain ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩ := h
      simp only [AddSubgroup.coe_add, Matrix.add_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_embedding]
    · simp only [AddSubgroup.coe_add, Matrix.add_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_outside L _ i k h, add_zero]
/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `a c`. Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_val_k, Matrix.submatrix_apply]`. Conclude with `_root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_embedding L β.1 a c`.
-/
theorem prj_padN_k (β : nA σ L.Y L.b) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padN_k L β) = β := by
  apply Subtype.ext
  ext a c
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_val_k, Matrix.submatrix_apply]
  exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_embedding L β.1 a c
/- English proof (translation)
Use `Continuous.subtype_mk ?_ _` and prove the remaining obligations. Use `continuous_pi fun i => continuous_pi fun k => ?_` and prove the remaining obligations. Distinguish the cases in `h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k`. Take `⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩` from `h`. Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_embedding]`.

Conclude with `(continuous_apply c).comp ((continuous_apply a).comp continuous_subtype_val)`. Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_outside L _ i k h]`. Conclude with `continuous_const`.
-/
theorem continuous_padN_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padN_k L) := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_pi fun i => continuous_pi fun k => ?_
  by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
  · obtain ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩ := h
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_embedding]
    exact (continuous_apply c).comp ((continuous_apply a).comp continuous_subtype_val)
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_outside L _ i k h]
    exact continuous_const
/- English proof (translation)
Take `⟨T, hT⟩` from `kunf.mem_nF_iff.1 h`. Use `kunf.mem_nF_iff.2 ⟨T.submatrix L.em L.em, ?_⟩` and prove the remaining obligations. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_val_k, hT]`. Both sides reduce to the same expression.
-/
theorem prj_nF_k {β : nA σ d.Y d.b} (h : β ∈ nF σ d.Y d.b) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β ∈ nF σ L.Y L.b := by
  obtain ⟨T, hT⟩ := kunf.mem_nF_iff.1 h
  refine kunf.mem_nF_iff.2 ⟨T.submatrix L.em L.em, ?_⟩
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_val_k, hT]
  rfl
/- English proof (translation)
Take `⟨T, hT⟩` from `kunf.mem_nF_iff.1 h`. Use `kunf.mem_nF_iff.2 ⟨Matrix.of fun i k => if h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k then T h.1.choose h.2.choose else 0, ?_⟩` and prove the remaining obligations. Use extensionality with `i k`. Use `show _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt L β.1 i k = _`. Distinguish the cases in `h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k`.

Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt, dif_pos h, hT]`. Simplify using `only [incM, Matrix.map_apply, Matrix.of_apply, dif_pos h]`. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt, dif_neg h]`. Simplify using `only [incM, Matrix.map_apply, Matrix.of_apply, dif_neg h, map_zero]`.
-/
theorem padN_nF_k {β : nA σ L.Y L.b} (h : β ∈ nF σ L.Y L.b) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padN_k L β ∈ nF σ d.Y d.b := by
  obtain ⟨T, hT⟩ := kunf.mem_nF_iff.1 h
  refine kunf.mem_nF_iff.2 ⟨Matrix.of fun i k => if h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k then
    T h.1.choose h.2.choose else 0, ?_⟩
  ext i k
  show _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt L β.1 i k = _
  by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt, dif_pos h, hT]
    simp only [incM, Matrix.map_apply, Matrix.of_apply, dif_pos h]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt, dif_neg h]
    simp only [incM, Matrix.map_apply, Matrix.of_apply, dif_neg h, map_zero]
/- English proof (translation)
Take `⟨ε, hε, hε'⟩` from `_root_.PositivityTheory.SiegelWeilFormula.Act.C4.eps_common_k L`. Take `⟨h1, h2⟩` from `nA_inst d.n d.Y d.b ε hε`. Take `⟨h3, h4⟩` from `nA_inst L.n L.Y L.b ε hε'`. Conclude with `GlobalTheory.T.haar_measure_split_exact_sequence (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padN_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.continuous_prj_k L) (_root_.PositivityTheory.SiegelWeilFormula …`.
-/
theorem fiber_k {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {nb' : nA σ L.Y L.b → G2 σ L.Y} {lam' : Measure (nA σ L.Y L.b)}
    {𝓖' : Set (nA σ L.Y L.b)} (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖')
    (G : nA σ L.Y L.b → ℂ) (hG : Continuous G) (hper : ∀ β₀ ∈ nF σ L.Y L.b, ∀ β', G (β₀ + β') = G β') :
    ∫ β in 𝓖, G (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β) ∂lam = ∫ β' in 𝓖', G β' ∂lam' := by
  obtain ⟨ε, hε, hε'⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.eps_common_k L
  obtain ⟨h1, h2⟩ := nA_inst d.n d.Y d.b ε hε
  obtain ⟨h3, h4⟩ := nA_inst L.n L.Y L.b ε hε'
  exact GlobalTheory.T.haar_measure_split_exact_sequence (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padN_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.continuous_prj_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.continuous_padN_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_padN_k L)
    (nF σ d.Y d.b) (nF σ L.Y L.b) (countable_nF _ _ _) (countable_nF _ _ _) (fun γ hγ => _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_nF_k L hγ)
    (fun γ hγ => _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padN_nF_k L hγ) lam lam' hc.2.1 hc'.2.1 𝓖 𝓖' hc.2.2.1 hc.2.2.2 hc'.2.2.1 hc'.2.2.2 G hG
    (fun γ hγ x => hper γ hγ x)
end PositivityTheory.SiegelWeilFormula.Act.C4
end
end
