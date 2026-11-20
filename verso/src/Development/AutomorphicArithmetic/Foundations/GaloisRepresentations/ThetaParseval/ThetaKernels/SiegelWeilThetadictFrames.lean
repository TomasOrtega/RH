import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.Frames
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.ThetaDictR
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem eps_of_form_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) (s : E)
    (hY : ∀ i j, σ (d.Y.J j i) = s * d.Y.J i j) : s * ((R.ε : ℤ) : E) = 1 := by
  have hσ := sig_invol hcm
  set i0 : Fin d.n := ⟨0, d.ok.hn⟩
  have key := conj_form hσ (GlobalTheory.WeilM.dbl d.Y.J) d.b.1 s (dbl_conj d.Y.J s hY) (Sum.inr i0) (Sum.inl i0)
  rw [R.hε] at key
  simpa using key.symm
/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem zeta_of_eps_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) :
    (((R.ε : ℤ) : E) = -1 → R.ζ = 1) ∧ (((R.ε : ℤ) : E) = 1 → R.ζ = Complex.I) := by
  have h2 : (1 : E) ≠ -1 := by
    intro h
    have : (2 : E) = 0 := by linear_combination h
    exact two_ne_zero this
  constructor
  · intro h
    rcases R.hζ with ⟨_, hz⟩ | ⟨he, _⟩
    · exact hz
    · rw [he] at h; exact absurd (by simpa using h) h2
  · intro h
    rcases R.hζ with ⟨he, _⟩ | ⟨_, hz⟩
    · rw [he] at h; exact absurd (by simpa using h.symm) h2
    · exact hz
/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_J_ne_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ i j, d.A.J i j ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hJ : d.A.J = 0 := Matrix.ext hcon
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hm := d.ok.hm
  have fin : ∀ (A : Matrix (Fin d.m) (Fin d.r ⊕ Fin d.s) ℂ),
      d.r + d.s = d.m → Aᵀ * (0 : Matrix (Fin d.m) (Fin d.m) ℂ) * A.map star = Matrix.fromBlocks 1 0 0 (-1) → False := by
    intro A hrs hA
    rw [Matrix.mul_zero, Matrix.zero_mul] at hA
    rcases Nat.eq_zero_or_pos d.r with hr | hr
    · have hs : 0 < d.s := by omega
      have := congrFun (congrFun hA (Sum.inr ⟨0, hs⟩)) (Sum.inr ⟨0, hs⟩)
      simp at this
    · have := congrFun (congrFun hA (Sum.inl ⟨0, hr⟩)) (Sum.inl ⟨0, hr⟩)
      simp at this
  rcases d.ok.sign with ⟨hA, _⟩ | ⟨hA, _⟩
  · obtain ⟨hrs, A, hA'⟩ := hA.sig (InfinitePlace.mk (φ.comp (algebraMap F E)))
    rw [hJ] at hA'
    exact fin A hrs (by simpa using hA')
  · obtain ⟨hrs, A, hA'⟩ := hA.sig (InfinitePlace.mk (φ.comp (algebraMap F E)))
    rw [hJ] at hA'
    exact fin A hrs (by simpa using hA')
/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem not_herm_skew_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (hA : d.A.IsHerm σ d.B d.r d.s) (hA' : d.A.IsSkew σ d.B d.r d.s) : False := by
  obtain ⟨i, j, hij⟩ := _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.exists_J_ne_k d
  have h1 := hA.herm i j
  have h2 := hA'.skew i j
  rw [h1] at h2
  have : (2 : E) * d.A.J i j = 0 := by linear_combination h2
  rcases mul_eq_zero.1 this with h | h
  · exact two_ne_zero h
  · exact hij h
/- English proof (translation)
Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem zeta_of_sign'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) :
    (d.A.IsHerm σ d.B d.r d.s → R.ζ = 1) ∧ (d.A.IsSkew σ d.B d.r d.s → R.ζ = Complex.I) := by
  have hcm := d.ok.good.cm
  constructor
  · intro hA
    rcases d.ok.sign with ⟨_, hY⟩ | ⟨hA', _⟩
    · refine (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.zeta_of_eps_k R).1 ?_
      have := _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.eps_of_form_k R hcm (-1) (fun i j => by rw [hY]; ring)
      linear_combination -this
    · exact (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.not_herm_skew_k d hA hA').elim
  · intro hA
    rcases d.ok.sign with ⟨hA', _⟩ | ⟨_, hY⟩
    · exact (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.not_herm_skew_k d hA' hA).elim
    · refine (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.zeta_of_eps_k R).2 ?_
      have := _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.eps_of_form_k R hcm 1 (fun i j => by rw [hY]; ring)
      linear_combination this
/- English proof (translation)
Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis.

Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem eta_zeta'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {η : E} (hη : η ≠ 0) (herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) :
    (σ η = η ∧ R.ζ = 1) ∨ (σ η = -η ∧ R.ζ = Complex.I) := by
  obtain ⟨i, j, hij⟩ := _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.exists_J_ne_k d
  rcases d.ok.sign with ⟨hA, _⟩ | ⟨hA, _⟩
  · left
    refine ⟨?_, (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.zeta_of_sign'_k R).1 hA⟩
    have h := herm i j
    rw [map_mul, hA.herm] at h
    exact mul_right_cancel₀ hij h
  · right
    refine ⟨?_, (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.zeta_of_sign'_k R).2 hA⟩
    have h := herm i j
    rw [map_mul, hA.skew] at h
    have : (σ η + η) * d.A.J i j = 0 := by linear_combination -h
    rcases mul_eq_zero.1 this with h' | h'
    · linear_combination h'
    · exact (hij h').elim
end PositivityTheory.SiegelWeilFormula.ThetaDictR
end
end
