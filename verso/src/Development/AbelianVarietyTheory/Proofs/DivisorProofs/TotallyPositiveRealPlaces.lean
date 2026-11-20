import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RealPlaceNorms

open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField NumberField.InfinitePlace.Completion

/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp [add_mulVec, hp, hq, add_smul]`. Consider the case `monomial k a`. Establish `hk : (A ^ k) *ᵥ v = z ^ k • v`. Proceed by induction on `k with`.

Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ, ← mulVec_mulVec, h, mulVec_smul, ih, smul_smul, pow_succ, mul_comm]`. Rewrite using `[aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_mulVec, hk, smul_smul, eval_monomial]`.
-/
theorem aeval_mulVec_of_eigen {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (z : ℂ)
    (h : A *ᵥ v = z • v) (p : ℂ[X]) : (aeval A p) *ᵥ v = p.eval z • v := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [add_mulVec, hp, hq, add_smul]
  | monomial k a =>
    have hk : (A ^ k) *ᵥ v = z ^ k • v := by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ← mulVec_mulVec, h, mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_mulVec,
      hk, smul_smul, eval_monomial]

/- English proof (translation)
Establish `h1` using `hM.dotProduct_mulVec_pos hv`. Rewrite `h1` using `[h, dotProduct_smul, smul_eq_mul]`. Establish `h2 : 0 < star v ⬝ᵥ v` using `dotProduct_star_self_pos_iff.2 hv`. Rewrite `h1`, `h2`, the goal using `[Complex.lt_def]`. Take `⟨a1, a2⟩` from `h1`.

Take `⟨b1, b2⟩` from `h2`. Simplify using `only [Complex.zero_re, Complex.zero_im, Complex.mul_re, Complex.mul_im] at a1 a2 b1 b2 ⊢`. Rewrite `a1`, `a2` using `[← b2]`. Establish `hi : c.im = 0`. Establish `: c.im * (star v ⬝ᵥ v).re = 0` using `by linarith`.

Conclude with `(mul_eq_zero.1 this).resolve_right b1.ne'`. Use `⟨?_, hi.symm⟩` and prove the remaining obligations. Rewrite `a1` using `[hi]`. Establish `: 0 < c.re * (star v ⬝ᵥ v).re` using `by linarith`. Conclude with `(pos_iff_pos_of_mul_pos this).2 b1`.
-/
theorem pos_of_posDef {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosDef) {v : Fin n → ℂ}
    (hv : v ≠ 0) {c : ℂ} (h : M *ᵥ v = c • v) : 0 < c := by
  have h1 := hM.dotProduct_mulVec_pos hv
  rw [h, dotProduct_smul, smul_eq_mul] at h1
  have h2 : 0 < star v ⬝ᵥ v := dotProduct_star_self_pos_iff.2 hv
  rw [Complex.lt_def] at h1 h2 ⊢
  obtain ⟨a1, a2⟩ := h1
  obtain ⟨b1, b2⟩ := h2
  simp only [Complex.zero_re, Complex.zero_im, Complex.mul_re, Complex.mul_im] at a1 a2 b1 b2 ⊢
  rw [← b2] at a1 a2
  have hi : c.im = 0 := by
    have : c.im * (star v ⬝ᵥ v).re = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right b1.ne'
  refine ⟨?_, hi.symm⟩
  rw [hi] at a1
  have : 0 < c.re * (star v ⬝ᵥ v).re := by linarith
  exact (pos_iff_pos_of_mul_pos this).2 b1

/- English proof (translation)
Rewrite using `[← RingHom.mapMatrix_apply, aeval_def, hom_eval₂, aeval_def, eval₂_map]`. Use `congr 1`. Use extensionality with `a i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.algebraMap_matrix_apply, h]`.
-/
theorem map_aeval {E : Type} [Field E] {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) (m : E[X]) (τ : E →+* ℂ) :
    (aeval γ m).map τ = aeval (γ.map τ) (m.map τ) := by
  rw [← RingHom.mapMatrix_apply, aeval_def, hom_eval₂, aeval_def, eval₂_map]
  congr 1
  ext a i j
  by_cases h : i = j <;> simp [Matrix.algebraMap_matrix_apply, h]

section Fld

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Q : SelfRecip E r)

/- English proof (translation)
Use `letI : Algebra (plus Q) ℂ := φ.toAlgebra`. Use `haveI : Module.Finite (plus Q) (Fld Q) := Module.Finite.of_restrictScalars_finite (maximalRealSubfield E) (plus Q) (Fld Q)`. Use `haveI : Module.IsTorsionFree (plus Q) ℂ := DivisionSemiring.to_moduleIsTorsionFree`. Use `haveI : Module.IsTorsionFree (plus Q) (Fld Q) := DivisionSemiring.to_moduleIsTorsionFree`. Set `ρ : Fld Q →ₐ[plus Q] ℂ` to `IsAlgClosed.lift`.

Establish `hρx : ρ (x : Fld Q) = φ x` using `ρ.commutes x`. Set `τ : E →+* ℂ` to `(ρ : Fld Q →+* ℂ).comp (algebraMap E (Fld Q))`. Establish `hev : ∀ p : E[X], (p.map τ).eval (ρ (AdjoinRoot.root Q.1)) = ρ (AdjoinRoot.mk Q.1 p)`. Introduce `p`. Rewrite using `[eval_map, ← AdjoinRoot.aeval_eq, aeval_def]`.

Conclude with `(Polynomial.hom_eval₂ p (algebraMap E (Fld Q)) (ρ : Fld Q →+* ℂ) (AdjoinRoot.root Q.1)).symm`. Use `set z := ρ (AdjoinRoot.root Q.1)`. Establish `hroot : ((γ.map τ).charpoly).eval z = 0`. Take `⟨g, hg⟩` from `hdvd`. Establish `h0 : (AdjoinRoot.mk Q.1 Q.1 : Fld Q) = 0` using `AdjoinRoot.mk_self`.

Rewrite using `[Matrix.charpoly_map, hg, Polynomial.map_mul, eval_mul, hev, h0]`. Conclude with `mul_eq_zero_of_left (map_zero ρ) _`. Rewrite `hroot` using `[Matrix.eval_charpoly]`. Take `⟨v, hv, hv0⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 hroot`. Establish `hγv : (γ.map τ) *ᵥ v = z • v`.

Rewrite `hv0` using `[Matrix.sub_mulVec, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]`. Conclude with `hv0.symm`. Establish `hM : ((aeval γ m).map τ) *ᵥ v = φ x • v`. Rewrite using `[map_aeval, aeval_mulVec_of_eigen _ v z hγv, hev, ← hx, hρx]`. Conclude with `pos_of_posDef (hpos τ) hv hM`.
-/
theorem pos_at_embedding {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) (m : E[X])
    (hpos : ∀ τ : E →+* ℂ, ((aeval γ m).map τ).PosDef) (hdvd : Q.1 ∣ γ.charpoly)
    (x : plus Q) (hx : (x : Fld Q) = AdjoinRoot.mk Q.1 m) (φ : plus Q →+* ℂ) : 0 < φ x := by
  letI : Algebra (plus Q) ℂ := φ.toAlgebra
  haveI : Module.Finite (plus Q) (Fld Q) :=
    Module.Finite.of_restrictScalars_finite (maximalRealSubfield E) (plus Q) (Fld Q)
  haveI : Module.IsTorsionFree (plus Q) ℂ := DivisionSemiring.to_moduleIsTorsionFree
  haveI : Module.IsTorsionFree (plus Q) (Fld Q) := DivisionSemiring.to_moduleIsTorsionFree
  let ρ : Fld Q →ₐ[plus Q] ℂ := IsAlgClosed.lift
  have hρx : ρ (x : Fld Q) = φ x := ρ.commutes x
  let τ : E →+* ℂ := (ρ : Fld Q →+* ℂ).comp (algebraMap E (Fld Q))
  have hev : ∀ p : E[X], (p.map τ).eval (ρ (AdjoinRoot.root Q.1)) = ρ (AdjoinRoot.mk Q.1 p) := by
    intro p
    rw [eval_map, ← AdjoinRoot.aeval_eq, aeval_def]
    exact (Polynomial.hom_eval₂ p (algebraMap E (Fld Q)) (ρ : Fld Q →+* ℂ) (AdjoinRoot.root Q.1)).symm
  set z := ρ (AdjoinRoot.root Q.1)
  have hroot : ((γ.map τ).charpoly).eval z = 0 := by
    obtain ⟨g, hg⟩ := hdvd
    have h0 : (AdjoinRoot.mk Q.1 Q.1 : Fld Q) = 0 := AdjoinRoot.mk_self
    rw [Matrix.charpoly_map, hg, Polynomial.map_mul, eval_mul, hev, h0]
    exact mul_eq_zero_of_left (map_zero ρ) _
  rw [Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hroot
  have hγv : (γ.map τ) *ᵥ v = z • v := by
    rw [Matrix.sub_mulVec, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec,
      Matrix.one_mulVec, sub_eq_zero] at hv0
    exact hv0.symm
  have hM : ((aeval γ m).map τ) *ᵥ v = φ x • v := by
    rw [map_aeval, aeval_mulVec_of_eigen _ v z hγv, hev, ← hx, hρx]
  exact pos_of_posDef (hpos τ) hv hM

end Fld

/- English proof (translation)
Take `⟨h1, h2⟩` from `Complex.lt_def.1 ht`. Simplify using `only [Complex.zero_re, Complex.zero_im] at h1 h2`. Establish `hre : w.embedding t = ((w.embedding t).re : ℂ)` using `Complex.ext (by simp) (by simp [← h2])`. Establish `key : ∃ a : w.Completion, extensionEmbedding w a = (Real.sqrt (w.embedding t).re : ℂ)`. Distinguish the cases in `hw : w.IsReal`.

Use `⟨(ringEquivRealOfIsReal hw).symm (Real.sqrt (w.embedding t).re), ?_⟩` and prove the remaining obligations. Rewrite using `[← extensionEmbeddingOfIsReal_apply hw, ← ringEquivRealOfIsReal_apply, RingEquiv.apply_symm_apply]`. Conclude with `surjective_extensionEmbedding_of_isComplex (InfinitePlace.not_isReal_iff_isComplex.1 hw) _`. Take `⟨a, ha⟩` from `key`. Use `⟨a, (extensionEmbedding w).injective ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, ha, ← Complex.ofReal_mul, Real.mul_self_sqrt h1.le, ← hre]`. Simplify using the standard rewrite rules.
-/
theorem exists_mul_self_of_pos {K : Type} [Field K] [NumberField K] (w : InfinitePlace K) (t : K)
    (ht : 0 < w.embedding t) : ∃ a : w.Completion, a * a = algebraMap K w.Completion t := by
  obtain ⟨h1, h2⟩ := Complex.lt_def.1 ht
  simp only [Complex.zero_re, Complex.zero_im] at h1 h2
  have hre : w.embedding t = ((w.embedding t).re : ℂ) := Complex.ext (by simp) (by simp [← h2])
  have key : ∃ a : w.Completion, extensionEmbedding w a = (Real.sqrt (w.embedding t).re : ℂ) := by
    by_cases hw : w.IsReal
    · refine ⟨(ringEquivRealOfIsReal hw).symm (Real.sqrt (w.embedding t).re), ?_⟩
      rw [← extensionEmbeddingOfIsReal_apply hw, ← ringEquivRealOfIsReal_apply,
        RingEquiv.apply_symm_apply]
    · exact surjective_extensionEmbedding_of_isComplex (InfinitePlace.not_isReal_iff_isComplex.1 hw) _
  obtain ⟨a, ha⟩ := key
  refine ⟨a, (extensionEmbedding w).injective ?_⟩
  rw [map_mul, ha, ← Complex.ofReal_mul, Real.mul_self_sqrt h1.le, ← hre]
  simp

/- English proof (translation)
Introduce `E _ _ _ n γ _ _ m hpos r Q hdvd hfix v`. Set `x : plus Q` to `⟨AdjoinRoot.mk Q.1 m, hfix⟩`. Take `⟨ψ, h1, hb⟩` from `GlobalTheory.TraceClasses.exists_infinite_decomp (maximalRealSubfield E) (plus Q)`. Establish `hroot : ∀ w : {w : InfinitePlace (plus Q) // w.comap (algebraMap (maximalRealSubfield E) (plus Q)) = v}, ∃ a : w.1.Completion, a * a = algebraMap (plus Q) _ x` using `fun w => exists_mul_self_of_pos w.1 x (pos_at_embedding Q γ.val m hpos hdvd x rfl w.1.embedding)`. Use `choose a ha using hroot`.

Take `⟨b, hb'⟩` from `(hb v).2 a`. Establish `hb2 : b * b = 1 ⊗ₜ x` using `(hb v).1 (funext fun w => by`. Establish `hw : ψ v w b = a w` using `congrFun hb' w`. Simplify using `only`. Rewrite using `[map_mul, hw, ha, h1])`.

Use `⟨inclPlus Q _ b, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.TraceClasses.involBase_inclPlus, ← map_mul, hb2]`. Both sides reduce to the same expression.
-/
theorem exists_norm_at_infinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (γ : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → ∀ m : E[X],
    (∀ τ : E →+* ℂ, ((aeval γ.val m).map τ).PosDef) → ∀ (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r),
    Q.1 ∣ γ.val.charpoly →
    GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) =
      (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) →
    ∀ v : InfinitePlace (maximalRealSubfield E),
      ∃ z : v.Completion ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q,
        z * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q _ z = 1 ⊗ₜ (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) := by
  intro E _ _ _ n γ _ _ m hpos r Q hdvd hfix v
  let x : plus Q := ⟨AdjoinRoot.mk Q.1 m, hfix⟩
  obtain ⟨ψ, h1, hb⟩ := GlobalTheory.TraceClasses.exists_infinite_decomp (maximalRealSubfield E) (plus Q)
  have hroot : ∀ w : {w : InfinitePlace (plus Q) // w.comap (algebraMap (maximalRealSubfield E) (plus Q)) = v},
      ∃ a : w.1.Completion, a * a = algebraMap (plus Q) _ x := fun w =>
    exists_mul_self_of_pos w.1 x (pos_at_embedding Q γ.val m hpos hdvd x rfl w.1.embedding)
  choose a ha using hroot
  obtain ⟨b, hb'⟩ := (hb v).2 a
  have hb2 : b * b = 1 ⊗ₜ x := (hb v).1 (funext fun w => by
    have hw : ψ v w b = a w := congrFun hb' w
    simp only
    rw [map_mul, hw, ha, h1])
  refine ⟨inclPlus Q _ b, ?_⟩
  rw [GlobalTheory.TraceClasses.involBase_inclPlus, ← map_mul, hb2]
  rfl

end GlobalTheory.RealPlaceNorms
