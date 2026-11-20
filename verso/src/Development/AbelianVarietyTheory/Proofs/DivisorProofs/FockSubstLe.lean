import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PaddedWittNormSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnInclusionRenaming
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfUnitCoord
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMulOfApprox
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormLeOfCoord
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualWeylEqSpanColProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExtremalRowWeight
import Formalism.ThetaSupremumBounds.LiftOperatorBoundOfFockJet

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions Formalism.L2.DIV
open Formalism.REAL (fockF)
open GlobalTheory.SubstMem (padRows)
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.JetBlock

abbrev incl {a b : ℕ} (h : a ≤ b) : Fin a × Fin a → Fin b × Fin b := Prod.map (Fin.castLE h) (Fin.castLE h)

/- English proof (translation)
The claim follows from `(Fin.castLE_injective h).prodMap (Fin.castLE_injective h)`.
-/
theorem incl_injective {a b : ℕ} (h : a ≤ b) : Function.Injective (incl h) :=
  (Fin.castLE_injective h).prodMap (Fin.castLE_injective h)

/- English proof (translation)
Rewrite using `[GlobalTheory.LvT.PtNorm.fockF_eq, GlobalTheory.LvT.PtNorm.fockF_eq, fockL_apply, fockL_apply, GlobalTheory.Proof.ColumnInclusionRenaming.fockS_rename he]`.
-/
theorem fockF_rename {σ τ : Type} {e : σ → τ} (he : Function.Injective e) (f g : MvPolynomial σ ℂ) :
    fockF (rename e f) (rename e g) = fockF f g := by
  rw [GlobalTheory.LvT.PtNorm.fockF_eq, GlobalTheory.LvT.PtNorm.fockF_eq, fockL_apply, fockL_apply, GlobalTheory.Proof.ColumnInclusionRenaming.fockS_rename he]

/- English proof (translation)
Rewrite using `[fockRowAdj, ← rowActMul ℂ r n]`. Both sides reduce to the same expression.
-/
theorem fockF_rowAct {r n : ℕ} (g : Matrix (Fin r) (Fin r) ℂ) (f : MvPolynomial (Fin r × Fin n) ℂ) :
    fockF (rowAct ℂ g f) (rowAct ℂ g f) = fockF f (rowAct ℂ (g * gᴴ) f) := by
  rw [fockRowAdj, ← rowActMul ℂ r n]
  rfl

/- English proof (translation)
Use `symm`. Use `Finset.sum_of_injOn (Fin.castLE h) (fun _ _ _ _ e => Fin.castLE_injective h e) (fun _ _ => Finset.mem_univ _) ?_ (fun _ _ => rfl)` and prove the remaining obligations. Introduce `t _ ht`. Use `hF t ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h'`.

Conclude with `ht ⟨⟨t.val, by omega⟩, by simp, by ext; simp⟩`.
-/
theorem sum_castLE {M : Type} [AddCommMonoid M] {a b : ℕ} (h : a ≤ b) (F : Fin b → M)
    (hF : ∀ t : Fin b, a ≤ t.val → F t = 0) : ∑ t, F t = ∑ q : Fin a, F (Fin.castLE h q) := by
  symm
  refine Finset.sum_of_injOn (Fin.castLE h) (fun _ _ _ _ e => Fin.castLE_injective h e)
    (fun _ _ => Finset.mem_univ _) ?_ (fun _ _ => rfl)
  intro t _ ht
  refine hF t ?_
  by_contra h'
  exact ht ⟨⟨t.val, by omega⟩, by simp, by ext; simp⟩

/- English proof (translation)
Establish `e : (rowAct ℂ (padRows A * (padRows A)ᴴ)).comp (rename (incl h)) = (rename (incl h)).comp (rowAct ℂ (A * Aᴴ))`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨p, q⟩`. Simplify using `only [AlgHom.comp_apply, rename_X, rowAct, aeval_X, map_sum, map_mul, rename_C, Prod.map]`. Rewrite using `[sum_castLE h]`.

Use `Finset.sum_congr rfl fun β _ => ?_` and prove the remaining obligations. Simplify using `[Matrix.mul_apply, padRows]`. Introduce `t ht`. Simplify using `[Matrix.mul_apply, padRows, not_lt.mpr ht]`. Conclude with `DFunLike.congr_fun e f`.
-/
theorem rowAct_pad {a b : ℕ} (h : a ≤ b) (A : Matrix (Fin a) (Fin b) ℂ) (f : MvPolynomial (Fin a × Fin a) ℂ) :
    rowAct ℂ (padRows A * (padRows A)ᴴ) (rename (incl h) f) = rename (incl h) (rowAct ℂ (A * Aᴴ) f) := by
  have e : (rowAct ℂ (padRows A * (padRows A)ᴴ)).comp (rename (incl h)) =
      (rename (incl h)).comp (rowAct ℂ (A * Aᴴ)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨p, q⟩
    simp only [AlgHom.comp_apply, rename_X, rowAct, aeval_X, map_sum, map_mul, rename_C, Prod.map]
    rw [sum_castLE h]
    · refine Finset.sum_congr rfl fun β _ => ?_
      simp [Matrix.mul_apply, padRows]
    · intro t ht
      simp [Matrix.mul_apply, padRows, not_lt.mpr ht]
  exact DFunLike.congr_fun e f

/- English proof (translation)
Establish `hP : (A * Aᴴ).PosSemidef` using `Matrix.posSemidef_self_mul_conjTranspose A`. Establish `hH` using `hP.isHermitian`. Use `set ev := hH.eigenvalues with hev`. Establish `h0 : ∀ i, 0 ≤ ev i` using `hP.eigenvalues_nonneg`. Use `set σ := Tuple.sort (fun i => -ev i) with hσ`.

Establish `hm : Monotone ((fun i => -ev i) ∘ σ)` using `Tuple.monotone_sort _`. Use `set V : Matrix (Fin a) (Fin a) ℂ := hH.eigenvectorUnitary.1 with hV`. Establish `hVV : V * Vᴴ = 1` using `Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2`. Establish `hs : A * Aᴴ = V * Matrix.diagonal (fun i => (ev i : ℂ)) * Vᴴ`. Use `hH.spectral_theorem` as an intermediate fact.

Conclude with `this`. Use `⟨V.submatrix id σ, fun i => √(ev (σ i)), ?_, ?_, fun i => Real.sqrt_nonneg _, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hVV]`. Simplify using the standard rewrite rules. Introduce `i j hij`.

Use `hm hij` as an intermediate fact. Simplify using `only [Function.comp] at this`. Conclude with `Real.sqrt_le_sqrt (by linarith)`. Rewrite using `[hs]`. Use extensionality with `i j`.

Simplify using `only [Matrix.mul_apply (M := _ * _), Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id]`. Rewrite using `[← Equiv.sum_comp σ]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `: ((ev (σ k) : ℝ) : ℂ) = (√(ev (σ k)) : ℝ) * (√(ev (σ k)) : ℝ)`. Rewrite using `[← Complex.ofReal_mul, Real.mul_self_sqrt (h0 _)]`.

Rewrite using `[star_mul']`. Simplify using `only [Complex.star_def, Complex.conj_ofReal]`. Use `conv_lhs => rw [this]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Real.sq_sqrt (h0 _)]`.

Rewrite using `[Equiv.sum_comp σ ev]`. Establish `h1` using `hH.trace_eq_sum_eigenvalues`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Use `push_cast`. Rewrite using `[hev]`.

Use `erw [← h1]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj']`.
-/
theorem exists_sing {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) :
    ∃ (U : Matrix (Fin a) (Fin a) ℂ) (t : Fin a → ℝ), U * Uᴴ = 1 ∧ Antitone t ∧ (∀ i, 0 ≤ t i) ∧
      A * Aᴴ = (U * Matrix.diagonal fun i => (t i : ℂ)) * (U * Matrix.diagonal fun i => (t i : ℂ))ᴴ ∧
      ∑ i, t i ^ 2 = ∑ β, ∑ α, ‖A α β‖ ^ 2 := by
  have hP : (A * Aᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose A
  have hH := hP.isHermitian
  set ev := hH.eigenvalues with hev
  have h0 : ∀ i, 0 ≤ ev i := hP.eigenvalues_nonneg
  set σ := Tuple.sort (fun i => -ev i) with hσ
  have hm : Monotone ((fun i => -ev i) ∘ σ) := Tuple.monotone_sort _
  set V : Matrix (Fin a) (Fin a) ℂ := hH.eigenvectorUnitary.1 with hV
  have hVV : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
  have hs : A * Aᴴ = V * Matrix.diagonal (fun i => (ev i : ℂ)) * Vᴴ := by
    have := hH.spectral_theorem
    exact this
  refine ⟨V.submatrix id σ, fun i => √(ev (σ i)), ?_, ?_, fun i => Real.sqrt_nonneg _, ?_, ?_⟩
  · rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hVV]
    simp
  · intro i j hij
    have := hm hij
    simp only [Function.comp] at this
    exact Real.sqrt_le_sqrt (by linarith)
  · rw [hs]
    ext i j
    simp only [Matrix.mul_apply (M := _ * _), Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id]
    rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : ((ev (σ k) : ℝ) : ℂ) = (√(ev (σ k)) : ℝ) * (√(ev (σ k)) : ℝ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (h0 _)]
    rw [star_mul']
    simp only [Complex.star_def, Complex.conj_ofReal]
    conv_lhs => rw [this]
    ring
  · simp only [Real.sq_sqrt (h0 _)]
    rw [Equiv.sum_comp σ ev]
    have h1 := hH.trace_eq_sum_eigenvalues
    apply Complex.ofReal_injective
    push_cast
    rw [hev]
    erw [← h1]
    rw [Finset.sum_comm]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
      Complex.mul_conj']

/- English proof (translation)
Rewrite `hf` using `[standardMonomialSpanDomain ℂ n n ν]`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨K, sz, hsz, I, rfl, rfl⟩` from `hx`. Conclude with `fun m hm => bidetDominance ℂ n n K sz hsz I m hm`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Introduce `m hm`. Break down `Finset.mem_union.mp (support_add hm) with h | h` into its components or cases. Conclude with `hx m h`.

Conclude with `hy m h`. Consider the case `smul c x _ hx => exact fun m hm => hx m (support_smul hm)`.
-/
theorem dominance {n : ℕ} (ν : Fin n → ℕ) {f : MvPolynomial (Fin n × Fin n) ℂ} (hf : f ∈ dualWeyl ℂ n n ν) :
    ∀ m ∈ f.support, (∀ k : ℕ, (∑ a : Fin n with a.val < k, rowDeg m a) ≤ ∑ t : Fin n with t.val < k, ν t) ∧
      ∑ a : Fin n, rowDeg m a = ∑ t : Fin n, ν t := by
  classical
  rw [standardMonomialSpanDomain ℂ n n ν] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, rfl, rfl⟩ := hx
    exact fun m hm => bidetDominance ℂ n n K sz hsz I m hm
  | zero => simp
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.mp (support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx => exact fun m hm => hx m (support_smul hm)

/- English proof (translation)
Take `⟨U, t, hU, ht, h0, hA, hs⟩` from `exists_sing A`. Use `⟨t, h0, hs, fun ν f hf => ?_⟩` and prove the remaining obligations. Establish `hd` using `dominance ν (dualWeylRowStable ℂ a a ν U f hf)`. Establish `h1` using `fockDiagBound a a t ν h0 ht (rowAct ℂ U f) (fun m hm => (hd m hm).1) (fun m hm => (hd m hm).2)`. Rewrite `h1` using `[fockF_rowAct U, hU, ldlat_rowAct_one, ← AlgHom.comp_apply, rowActMul, fockF_rowAct, ← hA]`.

Rewrite using `[fockF_rowAct, rowAct_pad, fockF_rename (incl_injective h)]`. Conclude with `h1`.
-/
theorem fock_subst_le {a b : ℕ} (h : a ≤ b) (A : Matrix (Fin a) (Fin b) ℂ) :
    ∃ t : Fin a → ℝ, (∀ i, 0 ≤ t i) ∧ ∑ i, t i ^ 2 = ∑ β, ∑ α, ‖A α β‖ ^ 2 ∧
      ∀ (ν : Fin a → ℕ), ∀ f ∈ dualWeyl ℂ a a ν,
        (fockF (rowAct ℂ (padRows A) (rename (incl h) f)) (rowAct ℂ (padRows A) (rename (incl h) f))).re ≤
          (∏ i, t i ^ (2 * ν i)) * (fockF f f).re := by
  obtain ⟨U, t, hU, ht, h0, hA, hs⟩ := exists_sing A
  refine ⟨t, h0, hs, fun ν f hf => ?_⟩
  have hd := dominance ν (dualWeylRowStable ℂ a a ν U f hf)
  have h1 := fockDiagBound a a t ν h0 ht (rowAct ℂ U f) (fun m hm => (hd m hm).1) (fun m hm => (hd m hm).2)
  rw [fockF_rowAct U, hU, ldlat_rowAct_one, ← AlgHom.comp_apply, rowActMul, fockF_rowAct, ← hA] at h1
  rw [fockF_rowAct, rowAct_pad, fockF_rename (incl_injective h)]
  exact h1

/- English proof (translation)
Rewrite using `[← GlobalTheory.Proof.ColumnInclusionRenaming.rename_hw h]`. Unfold `hw`. Rewrite using `[map_prod, map_prod]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, map_pow]`.

Use `congr 1`. Unfold `lpMinor`. Rewrite using `[AlgHom.map_det, AlgHom.map_det]`. Use `congr 1`. Use extensionality with `p q : 2`.

Simplify using `[GlobalTheory.Proof.ColumnInclusionRenaming.colIncl]`.
-/
theorem rename_hw {a b : ℕ} (h : a ≤ b) (ν : Fin a → ℕ) :
    rename (incl h) (hw ℂ (le_refl a) ν) = hw ℂ (le_refl b) (rowNu (r := b) ν) := by
  rw [← GlobalTheory.Proof.ColumnInclusionRenaming.rename_hw h]
  unfold hw
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, map_pow]
  congr 1
  unfold lpMinor
  rw [AlgHom.map_det, AlgHom.map_det]
  congr 1
  ext p q : 2
  simp [GlobalTheory.Proof.ColumnInclusionRenaming.colIncl]

open GlobalTheory.DualWeyl GlobalTheory.WeylMinorDual in

/- English proof (translation)
Establish `hν : Antitone fun i => μ i + e` using `fun i j hij => Nat.add_le_add_right (hμ hij) e`. Establish `hm : f * gdet ℂ n ^ e ∈ dualWeyl ℂ n n fun i => μ i + e` using `(dualWeylMul ℂ n n _ _ _ _).1 hf (GlobalTheory.SubstMem.det_pow_mem n e)`. Establish `hn : ∀ (g : UN n) (p : Pol n ℂ), ‖evalAt g.1 (p * gdet ℂ n ^ e)‖ = ‖evalAt g.1 p‖`. Introduce `g p`. Establish `h1 : evalAt g.1 (gdet ℂ n) = g.1.det`.

Unfold `gdet`. Rewrite using `[AlgHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Rewrite using `[map_mul, map_pow, h1, norm_mul, norm_pow, CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary g.2), one_pow, mul_one]`. Establish `h1` using `(GlobalTheory.T.dualWeyl_extremal_reproducing_normSq_one n μ hμ).2`. Establish `h2` using `(GlobalTheory.T.dualWeyl_extremal_reproducing_normSq_one n _ hν).2`. Rewrite `h2` using `[GlobalTheory.DualWeyl.extremal, hw_add]`. Simplify using `only [GlobalTheory.DualWeyl.normSq, hn] at h2`.

Rewrite `h1` using `[GlobalTheory.DualWeyl.normSq, GlobalTheory.DualWeyl.extremal]`. Establish `hd : (dim (fun i => μ i + e) : ℝ) = dim μ`. Use `mul_right_cancel₀ (fun h0 => ?_) (h2.trans h1.symm)` and prove the remaining obligations. Rewrite `h1` using `[h0, mul_zero]`. Conclude with `zero_ne_one h1`.

Establish `e1` using `GlobalTheory.DualWeylFock.form_eq_fock_div n μ hμ f hf f hf`. Establish `e2` using `GlobalTheory.DualWeylFock.form_eq_fock_div n _ hν _ hm _ hm`. Rewrite `e1`, `e2` using `[form_self]`. Use `e2.symm.trans (Eq.trans ?_ e1)` and prove the remaining obligations. Simplify using `only [GlobalTheory.DualWeyl.normSq, hn, hd]`.
-/
theorem fock_mul_det {n : ℕ} (μ : Fin n → ℕ) (hμ : Antitone μ) (e : ℕ) {f : MvPolynomial (Fin n × Fin n) ℂ}
    (hf : f ∈ dualWeyl ℂ n n μ) :
    fockF (f * gdet ℂ n ^ e) (f * gdet ℂ n ^ e) /
        fockF (hw ℂ (le_refl n) fun i => μ i + e) (hw ℂ (le_refl n) fun i => μ i + e) =
      fockF f f / fockF (hw ℂ (le_refl n) μ) (hw ℂ (le_refl n) μ) := by
  have hν : Antitone fun i => μ i + e := fun i j hij => Nat.add_le_add_right (hμ hij) e
  have hm : f * gdet ℂ n ^ e ∈ dualWeyl ℂ n n fun i => μ i + e :=
    (dualWeylMul ℂ n n _ _ _ _).1 hf (GlobalTheory.SubstMem.det_pow_mem n e)
  have hn : ∀ (g : UN n) (p : Pol n ℂ), ‖evalAt g.1 (p * gdet ℂ n ^ e)‖ = ‖evalAt g.1 p‖ := by
    intro g p
    have h1 : evalAt g.1 (gdet ℂ n) = g.1.det := by
      unfold gdet
      rw [AlgHom.map_det]
      congr 1
      ext i j
      simp
    rw [map_mul, map_pow, h1, norm_mul, norm_pow,
      CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary g.2), one_pow, mul_one]
  have h1 := (GlobalTheory.T.dualWeyl_extremal_reproducing_normSq_one n μ hμ).2
  have h2 := (GlobalTheory.T.dualWeyl_extremal_reproducing_normSq_one n _ hν).2
  rw [GlobalTheory.DualWeyl.extremal, hw_add] at h2
  simp only [GlobalTheory.DualWeyl.normSq, hn] at h2
  rw [GlobalTheory.DualWeyl.normSq, GlobalTheory.DualWeyl.extremal] at h1
  have hd : (dim (fun i => μ i + e) : ℝ) = dim μ := by
    refine mul_right_cancel₀ (fun h0 => ?_) (h2.trans h1.symm)
    rw [h0, mul_zero] at h1
    exact zero_ne_one h1
  have e1 := GlobalTheory.DualWeylFock.form_eq_fock_div n μ hμ f hf f hf
  have e2 := GlobalTheory.DualWeylFock.form_eq_fock_div n _ hν _ hm _ hm
  rw [form_self] at e1 e2
  refine e2.symm.trans (Eq.trans ?_ e1)
  simp only [GlobalTheory.DualWeyl.normSq, hn, hd]

end GlobalTheory.JetBlock
