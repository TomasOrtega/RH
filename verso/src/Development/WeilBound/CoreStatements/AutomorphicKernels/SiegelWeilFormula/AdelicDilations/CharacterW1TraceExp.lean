import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.DilExPf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.MatrixEqFrameConjugate
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.AesmOfContinuous

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Establish `hP : inFrame d.b (R.ι w xN) = Matrix.fromBlocks 1 (inFrame d.b (R.ι w xN)).toBlocks₁₂ 0 1`. Apply `Place.cw_ext d` to reduce the goal to its premises. Introduce `u`. Rewrite using `[KSing.UnitaryGroupBasics.cw_fromBlocks, KSing.UnitaryGroupBasics.cw_toBlocks₁₂]`. Distinguish the cases in `hu : u = w`.

Substitute `hu` using the available equality. Rewrite using `[KSing.UnitaryGroupBasics.cw_unip d R u xN _ hxN, Matrix.toBlocks_fromBlocks₁₂]`. Rewrite using `[R.off_w w u xN hu, KSing.UnitaryGroupBasics.toBlocks₁₂_one, Matrix.fromBlocks_one]`. Rewrite using `[Matrix.fromBlocks_smul, KSing.UnitaryGroupBasics.fin_toBlocks₁₂, R.off_f w xN, ← KSing.UnitaryGroupBasics.fin_toBlocks₁₂, KSing.UnitaryGroupBasics.toBlocks₁₂_one, smul_zero]`. Rewrite using `[← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero]`.

Set `β₁ : nA σ d.Y d.b` to `⟨(inFrame d.b (R.ι w xN)).toBlocks₁₂, AddSubgroup.subset_closure ⟨R.ι w xN, hP⟩⟩`. Establish `hB : inFrame d.b (R.ι w xN) = Matrix.fromBlocks 1 β₁.1 0 1` using `hP`. Use `⟨β₁, KSing.UnitaryGroupBasics.inFrame_inj d (by rw [hN]; exact hB), ?_, fun u hu => ?_, ?_⟩` and prove the remaining obligations. Establish `e` using `KSing.UnitaryGroupBasics.cw_unip d R w xN _ hxN`. Rewrite `e` using `[hB, KSing.UnitaryGroupBasics.cw_fromBlocks]`.

Conclude with `(Matrix.fromBlocks_inj.1 e).2.1`. Establish `e` using `R.off_w w u xN hu`. Rewrite `e` using `[hB, KSing.UnitaryGroupBasics.cw_fromBlocks, ← Matrix.fromBlocks_one]`. Conclude with `(Matrix.fromBlocks_inj.1 e).2.1`. Establish `e` using `R.off_f w xN`.

Rewrite `e` using `[hB, Matrix.fromBlocks_smul, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]`. Conclude with `(Matrix.fromBlocks_inj.1 e).2.1.trans (smul_zero _)`.
-/
theorem nbw1 (d : SD σ) (R : RD d) (w : InfinitePlace F) {nb : nA σ d.Y d.b → d.G} (hN : IsNMap d.b nb)
    (xN : GR d.n) (h : Matrix (Fin d.n) (Fin d.n) ℂ) (hxN : mR xN = nU h) :
    ∃ β₁ : nA σ d.Y d.b, R.ι w xN = nb β₁ ∧ d.cw w β₁.1 = R.ζ • h ∧ (∀ u, u ≠ w → d.cw u β₁.1 = 0) ∧
      finOne F • β₁.1 = 0 := by
  have hP : inFrame d.b (R.ι w xN) = Matrix.fromBlocks 1 (inFrame d.b (R.ι w xN)).toBlocks₁₂ 0 1 := by
    apply Place.cw_ext d
    · intro u
      rw [KSing.UnitaryGroupBasics.cw_fromBlocks, KSing.UnitaryGroupBasics.cw_toBlocks₁₂]
      by_cases hu : u = w
      · subst hu
        rw [KSing.UnitaryGroupBasics.cw_unip d R u xN _ hxN, Matrix.toBlocks_fromBlocks₁₂]
      · rw [R.off_w w u xN hu, KSing.UnitaryGroupBasics.toBlocks₁₂_one, Matrix.fromBlocks_one]
    · rw [Matrix.fromBlocks_smul, KSing.UnitaryGroupBasics.fin_toBlocks₁₂, R.off_f w xN, ← KSing.UnitaryGroupBasics.fin_toBlocks₁₂, KSing.UnitaryGroupBasics.toBlocks₁₂_one,
        smul_zero]
      rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero]
  let β₁ : nA σ d.Y d.b := ⟨(inFrame d.b (R.ι w xN)).toBlocks₁₂, AddSubgroup.subset_closure ⟨R.ι w xN, hP⟩⟩
  have hB : inFrame d.b (R.ι w xN) = Matrix.fromBlocks 1 β₁.1 0 1 := hP
  refine ⟨β₁, KSing.UnitaryGroupBasics.inFrame_inj d (by rw [hN]; exact hB), ?_, fun u hu => ?_, ?_⟩
  · have e := KSing.UnitaryGroupBasics.cw_unip d R w xN _ hxN
    rw [hB, KSing.UnitaryGroupBasics.cw_fromBlocks] at e
    exact (Matrix.fromBlocks_inj.1 e).2.1
  · have e := R.off_w w u xN hu
    rw [hB, KSing.UnitaryGroupBasics.cw_fromBlocks, ← Matrix.fromBlocks_one] at e
    exact (Matrix.fromBlocks_inj.1 e).2.1
  · have e := R.off_f w xN
    rw [hB, Matrix.fromBlocks_smul, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul] at e
    exact (Matrix.fromBlocks_inj.1 e).2.1.trans (smul_zero _)

def betaW (d : SD σ) (R : RD d) (w : InfinitePlace F) (T : nF σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) ℂ :=
  ((2 * Real.pi : ℝ) : ℂ) • (-(2 : ℂ) • (R.ζ • d.cw w T.1.1))

/- English proof (translation)
Establish `hT : (d.cw w T.1.1)ᵀ + ((R.ε : ℤ) : ℂ) • (d.cw w T.1.1).map star = 0`. Use `AddSubgroup.closure_induction (p := fun β _ => (d.cw w β)ᵀ + ((R.ε : ℤ) : ℂ) • (d.cw w β).map star = 0) ?_ ?_ ?_ ?_ T.1.2` and prove the remaining obligations. Introduce and unpack `β ⟨x, hx⟩`. Establish `e` using `KSing.UnitaryGroupBasics.form_w d R w x`. Rewrite `e` using `[hx, KSing.UnitaryGroupBasics.cw_fromBlocks]`.

Simplify using `[Krd.Qc, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply] at e`. Rewrite using `[add_comm]`. Conclude with `e`. Use extensionality with `i j`. Simplify using `[SD.cw]`.

Introduce `a b _ _ ha hb`. Use extensionality with `i j`. Establish `ea` using `congrFun (congrFun ha i) j`. Establish `eb` using `congrFun (congrFun hb i) j`. Simplify using `[SD.cw] at ea eb ⊢`.

Take the linear combination `ea + eb`. Introduce `a _ ha`. Use extensionality with `i j`. Establish `ea` using `congrFun (congrFun ha i) j`. Simplify using `[SD.cw] at ea ⊢`.

Take the linear combination `-ea`. Unfold `betaW`. Take `⟨Tw, hTw⟩ : ∃ Tw, Tw = d.cw w T.1.1` from `⟨_, rfl⟩`. Rewrite `hT`, the goal using `[← hTw]`. Establish `hAh : (R.ζ • Tw)ᴴ = R.ζ • Tw`.

Use extensionality with `i j`. Establish `e` using `congrFun (congrFun hT j) i`. Simplify using `only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply, smul_eq_mul] at e`. Rewrite using `[Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, star_mul']`. Break down `R.hζ with ⟨hε, hζ⟩ | ⟨hε, hζ⟩` into its components or cases.

Rewrite using `[hζ]`. Rewrite `e` using `[hε]`. Simplify using `at e ⊢`. Take the linear combination `-e`. Rewrite using `[hζ]`.

Rewrite `e` using `[hε]`. Simplify using `at e ⊢`. Take the linear combination `(-Complex.I) * e`. Establish `hf : finOne F • (T.1.1 * β₁.1).trace = 0`. Rewrite using `[← Matrix.trace_smul, ← Matrix.mul_smul, hBf, Matrix.mul_zero, Matrix.trace_zero]`.

Establish `hw : ∀ u, u ≠ w → piInf (d.B.emb u) (T.1.1 * β₁.1).trace = 0` using `fun u hu => by`. Rewrite using `[KSing.UnitaryGroupBasics.piInf_trace, KSing.UnitaryGroupBasics.cw_mul, hBu u hu, Matrix.mul_zero, Matrix.trace_zero]`. Establish `hz` using `Place.psi_trace_at d.std d.cm d.B.emb w (T.1.1 * β₁.1).trace hf hw`. Establish `hw' : piInf (d.B.emb w) (T.1.1 * β₁.1).trace = ((R.ζ • Tw) * h).trace`. Rewrite using `[KSing.UnitaryGroupBasics.piInf_trace, KSing.UnitaryGroupBasics.cw_mul, hBw, ← hTw, Matrix.mul_smul, Matrix.smul_mul]`.

Establish `hreal : ((((R.ζ • Tw) * h).trace).re : ℂ) = ((R.ζ • Tw) * h).trace`. Establish `hs : star (((R.ζ • Tw) * h).trace) = ((R.ζ • Tw) * h).trace`. Rewrite using `[← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hAh, hh.eq, Matrix.trace_mul_comm]`. Conclude with `Complex.conj_eq_iff_re.1 hs`. Establish `eR : ((((2 * Real.pi : ℝ) : ℂ) • (-(2 : ℂ) • (R.ζ • Tw))) * h).trace = ((2 * Real.pi : ℝ) : ℂ) * (-2 * (R.ζ • Tw * h).trace)`.

Rewrite using `[Matrix.smul_mul, Matrix.trace_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]`. Unfold `SD.tt`. Rewrite using `[hz, hw', eR]`. Generalize the expression as in `(R.ζ • Tw * h).trace = c at hreal ⊢`. Use `congr 1`.

Use `push_cast`. Rewrite using `[hreal]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem character_w1_trace_exp (d : SD σ) (R : RD d) (w : InfinitePlace F) (T : nF σ d.Y d.b) (β₁ : nA σ d.Y d.b)
    (h : Matrix (Fin d.n) (Fin d.n) ℂ) (hh : h.IsHermitian) (hBw : d.cw w β₁.1 = R.ζ • h)
    (hBu : ∀ u, u ≠ w → d.cw u β₁.1 = 0) (hBf : finOne F • β₁.1 = 0) :
    d.B.ψ (d.tt (T.1.1 * β₁.1)) = Complex.exp (Complex.I * (betaW d R w T * h).trace) := by
  have hT : (d.cw w T.1.1)ᵀ + ((R.ε : ℤ) : ℂ) • (d.cw w T.1.1).map star = 0 := by
    refine AddSubgroup.closure_induction
      (p := fun β _ => (d.cw w β)ᵀ + ((R.ε : ℤ) : ℂ) • (d.cw w β).map star = 0) ?_ ?_ ?_ ?_ T.1.2
    · rintro β ⟨x, hx⟩
      have e := KSing.UnitaryGroupBasics.form_w d R w x
      rw [hx, KSing.UnitaryGroupBasics.cw_fromBlocks] at e
      simp [Krd.Qc, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply] at e
      rw [add_comm]
      exact e
    · ext i j; simp [SD.cw]
    · intro a b _ _ ha hb
      ext i j
      have ea := congrFun (congrFun ha i) j
      have eb := congrFun (congrFun hb i) j
      simp [SD.cw] at ea eb ⊢
      linear_combination ea + eb
    · intro a _ ha
      ext i j
      have ea := congrFun (congrFun ha i) j
      simp [SD.cw] at ea ⊢
      linear_combination -ea
  unfold betaW
  obtain ⟨Tw, hTw⟩ : ∃ Tw, Tw = d.cw w T.1.1 := ⟨_, rfl⟩
  rw [← hTw] at hT ⊢
  have hAh : (R.ζ • Tw)ᴴ = R.ζ • Tw := by
    ext i j
    have e := congrFun (congrFun hT j) i
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply,
      smul_eq_mul] at e
    rw [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, star_mul']
    rcases R.hζ with ⟨hε, hζ⟩ | ⟨hε, hζ⟩
    · rw [hζ]; rw [hε] at e; simp at e ⊢; linear_combination -e
    · rw [hζ]; rw [hε] at e; simp at e ⊢; linear_combination (-Complex.I) * e
  have hf : finOne F • (T.1.1 * β₁.1).trace = 0 := by
    rw [← Matrix.trace_smul, ← Matrix.mul_smul, hBf, Matrix.mul_zero, Matrix.trace_zero]
  have hw : ∀ u, u ≠ w → piInf (d.B.emb u) (T.1.1 * β₁.1).trace = 0 := fun u hu => by
    rw [KSing.UnitaryGroupBasics.piInf_trace, KSing.UnitaryGroupBasics.cw_mul, hBu u hu, Matrix.mul_zero, Matrix.trace_zero]
  have hz := Place.psi_trace_at d.std d.cm d.B.emb w (T.1.1 * β₁.1).trace hf hw
  have hw' : piInf (d.B.emb w) (T.1.1 * β₁.1).trace = ((R.ζ • Tw) * h).trace := by
    rw [KSing.UnitaryGroupBasics.piInf_trace, KSing.UnitaryGroupBasics.cw_mul, hBw, ← hTw, Matrix.mul_smul, Matrix.smul_mul]
  have hreal : ((((R.ζ • Tw) * h).trace).re : ℂ) = ((R.ζ • Tw) * h).trace := by
    have hs : star (((R.ζ • Tw) * h).trace) = ((R.ζ • Tw) * h).trace := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hAh, hh.eq, Matrix.trace_mul_comm]
    exact Complex.conj_eq_iff_re.1 hs
  have eR : ((((2 * Real.pi : ℝ) : ℂ) • (-(2 : ℂ) • (R.ζ • Tw))) * h).trace =
      ((2 * Real.pi : ℝ) : ℂ) * (-2 * (R.ζ • Tw * h).trace) := by
    rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
  unfold SD.tt
  rw [hz, hw', eR]
  generalize (R.ζ • Tw * h).trace = c at hreal ⊢
  congr 1
  push_cast
  rw [hreal]
  ring

end PositivityTheory.SiegelWeilFormula.AStep

end
