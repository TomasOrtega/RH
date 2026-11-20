import Mathlib
import Formalism.LocalToGlobal.Columns.CoefficientsModP
import Formalism.LocalToGlobal.HermitianForms.FormsTied
import Formalism.LocalToGlobal.Columns.TiedValLatG
import Formalism.LocalToGlobal.Columns.TiedValNorm
import Formalism.LocalToGlobal.Columns.TiedValRat
import Formalism.LocalToGlobal.Columns.CoefModAt
import Formalism.LocalRingCardinality.PosOfIsomEmb
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SlopeStepG
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HtPsiLeIffExists
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms
open scoped Matrix ComplexOrder

namespace GlobalTheory.Core.CoefGram

/- English proof (translation)
Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]`. Establish `h1 : (J.map f).det = f J.det` using `(RingHom.map_det f J).symm`. Establish `h2 : (J.map f).adjugate = J.adjugate.map f` using `(RingHom.map_adjugate f J).symm`. Rewrite using `[h1, h2, Matrix.map_apply]`. Conclude with `mul_mem (inv_mem (hf _)) (hf _)`.
-/
theorem map_inv_entry_mem {E K : Type} [Field E] [Field K] {n : ℕ} (f : E →+* K) (K0 : Subfield K) (hf : ∀ x, f x ∈ K0)
    (J : Matrix (Fin n) (Fin n) E) (a b : Fin n) : (J.map f)⁻¹ a b ∈ K0 := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  have h1 : (J.map f).det = f J.det := (RingHom.map_det f J).symm
  have h2 : (J.map f).adjugate = J.adjugate.map f := (RingHom.map_adjugate f J).symm
  rw [h1, h2, Matrix.map_apply]
  exact mul_mem (inv_mem (hf _)) (hf _)

/- English proof (translation)
Establish `h1 : (A.map f).det = f A.det` using `(RingHom.map_det f A).symm`. Establish `h2 : (A.map f).adjugate = A.adjugate.map f` using `(RingHom.map_adjugate f A).symm`. Use extensionality with `a b`. Rewrite using `[Matrix.map_apply, Matrix.inv_def, Matrix.inv_def, Ring.inverse_eq_inv', Ring.inverse_eq_inv', h1, h2, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_inv₀, Matrix.map_apply]`.
-/
theorem map_inv_eq {K L : Type} [Field K] [Field L] {n : ℕ} (f : K →+* L) (A : Matrix (Fin n) (Fin n) K) :
    A⁻¹.map f = (A.map f)⁻¹ := by
  have h1 : (A.map f).det = f A.det := (RingHom.map_det f A).symm
  have h2 : (A.map f).adjugate = A.adjugate.map f := (RingHom.map_adjugate f A).symm
  ext a b
  rw [Matrix.map_apply, Matrix.inv_def, Matrix.inv_def, Ring.inverse_eq_inv', Ring.inverse_eq_inv', h1, h2,
    Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_inv₀, Matrix.map_apply]

/- English proof (translation)
Take `⟨e, P, hP⟩` from `h`. Establish `hJ : Formalism.UG.Jpq n 0 = 1`. Use extensionality with `i j`. Break down `i with i | i` into its components or cases. Break down `j with j | j` into its components or cases.

Simplify using `[Formalism.UG.Jpq, Matrix.one_apply]`. Conclude with `j.elim0`. Conclude with `i.elim0`. Establish `hcT : Formalism.UG.cT (starRingEnd ℂ) P.val = P.valᴴ`. Use extensionality with `i j`.

Simplify using `[Formalism.UG.cT, Matrix.conjTranspose_apply]`. Rewrite `hP` using `[hcT, hJ]`. Establish `h1 : (P.valᴴ * G.reindex e e * P.val).PosDef` using `by rw [hP]; exact Matrix.PosDef.one`. Establish `h2 : (G.reindex e e).PosDef` using `(Matrix.IsUnit.posDef_star_left_conjugate_iff P.isUnit).1 h1`. Establish `h3 : G = (G.reindex e e).submatrix e e` using `by ext i j; simp`.

Rewrite using `[h3]`. Conclude with `h2.submatrix e.injective`.
-/
theorem posDef_of_hasSignature {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (h : Formalism.UG.HasSignature G n 0) : G.PosDef := by
  obtain ⟨e, P, hP⟩ := h
  have hJ : Formalism.UG.Jpq n 0 = 1 := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
    · exact i.elim0
  have hcT : Formalism.UG.cT (starRingEnd ℂ) P.val = P.valᴴ := by
    ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  rw [hcT, hJ] at hP
  have h1 : (P.valᴴ * G.reindex e e * P.val).PosDef := by rw [hP]; exact Matrix.PosDef.one
  have h2 : (G.reindex e e).PosDef := (Matrix.IsUnit.posDef_star_left_conjugate_iff P.isUnit).1 h1
  have h3 : G = (G.reindex e e).submatrix e e := by ext i j; simp
  rw [h3]
  exact h2.submatrix e.injective

/- English proof (translation)
Use `letI := D.host.cmStar`. Establish `hsig` using `D.sp.X'_sig σ`. Establish `h0 : D.sp.X'.sig σ = (D.sp.X'.rank, 0)` using `D.X'_posDef σ`. Rewrite `hsig` using `[h0]`. Establish `h1 : (D.sp.X'.gram.map σ).PosDef` using `posDef_of_hasSignature _ hsig`.

Conclude with `h1.submatrix (finCongr (rankP D)).symm.injective`.
-/
theorem gramP_posDef (D : D7) (σ : D.host.E →+* ℂ) : ((gramP D).map σ).PosDef := by
  letI := D.host.cmStar
  have hsig := D.sp.X'_sig σ
  have h0 : D.sp.X'.sig σ = (D.sp.X'.rank, 0) := D.X'_posDef σ
  rw [h0] at hsig
  have h1 : (D.sp.X'.gram.map σ).PosDef := posDef_of_hasSignature _ hsig
  exact h1.submatrix (finCongr (rankP D)).symm.injective

/- English proof (translation)
Introduce `σ`. Rewrite using `[← D.embE_conj]`. Conclude with `D.host.conjE_apply (σ.comp D.embE) x`.
-/
theorem embE_mem (D : D7) (x : D.host.E) : D.embE x ∈ Formalism.DivisionValues.cmMax D.what₂.LL := by
  intro σ
  rw [← D.embE_conj]
  exact D.host.conjE_apply (σ.comp D.embE) x

/- English proof (translation)
Introduce `D u`. Use `⟨fun i j => ?_, fun v => ?_⟩` and prove the remaining obligations. Conclude with `pairRat _ _ _ _ (Formalism.DivisionValues.cmMax D.what₂.LL) _ (fun τ a b => map_inv_entry_mem _ _ (fun x => embE_mem D _) _ b a) i j`. Use `pairPos _ _ _ (sgT u) _ v.embedding fun τ => ?_` and prove the remaining obligations. Unfold `gramKd`.

Rewrite using `[Matrix.transpose_map, map_inv_eq, Matrix.map_map, ← RingHom.coe_comp]`. Conclude with `(gramP_posDef D _).inv.transpose`.
-/
theorem pairVr_gramP_rat_posDef : ∀ (D : D7) (u : D.what₂.Word), (∀ i j, (Matrix.of fun i j => pairVr (fun τ : D.what₂.Tau => D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E)) (sgT u) (gramP D) (bVV D.what₂.LL (sgT u) i) (bVV D.what₂.LL (sgT u) j)) i j ∈ Formalism.DivisionValues.cmMax D.what₂.LL) ∧ ∀ v : InfinitePlace D.what₂.LL, ((Matrix.of fun i j => pairVr (fun τ : D.what₂.Tau => D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E)) (sgT u) (gramP D) (bVV D.what₂.LL (sgT u) i) (bVV D.what₂.LL (sgT u) j)).map v.embedding).PosDef := by
  intro D u
  refine ⟨fun i j => ?_, fun v => ?_⟩
  · exact pairRat _ _ _ _ (Formalism.DivisionValues.cmMax D.what₂.LL) _
      (fun τ a b => map_inv_entry_mem _ _ (fun x => embE_mem D _) _ b a) i j
  · refine pairPos _ _ _ (sgT u) _ v.embedding fun τ => ?_
    unfold gramKd
    rw [Matrix.transpose_map, map_inv_eq, Matrix.map_map, ← RingHom.coe_comp]
    exact (gramP_posDef D _).inv.transpose

end GlobalTheory.Core.CoefGram
