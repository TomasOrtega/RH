import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.FrameGram

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

open scoped TensorProduct in
variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} in

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.GlobalTheory.FrameGram.hE_swap (hσ : ∀ x, σ (σ x) = x)
    (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → E) :
    σ (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J y x) = _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J x y := by
  simp only [_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, _root_.Formalism.UG.P.hform_eq_dot, dotProduct, Matrix.mulVec, Function.comp, Finset.mul_sum, map_sum,
    map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe, hσ, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. A detailed English derivation is pending.
-/
theorem linearIndependent_ratTup_of_det_ne_zero (R : Type) [CommRing R] [Algebra F R] {m : ℕ}
    (X : Fin m → Fin n → E) (hX : (gramE σ J X).det ≠ 0) :
    LinearIndependent (R ⊗[F] E) (ratTup (F := F) R X) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hcj : ∀ j, ∑ b, c b * inclR (F := F) R (X b j) = 0 := fun j => by
    simpa [Finset.sum_apply, ratTup] using congrFun hc j
  have hu : IsUnit ((gramE σ J X).map (inclR (F := F) R)).det := by
    have := (inclR (F := F) (E := E) R).map_det (gramE σ J X)
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]
    exact (IsUnit.mk0 _ hX).map _
  have h0 : ((gramE σ J X).map (inclR (F := F) R)).mulVec c = 0 := by
    funext a
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, gramE, hE, Formalism.UG.hform, map_sum,
      map_mul, Finset.sum_mul, Pi.zero_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    have := congrArg (fun t => inclR (F := F) R ((σ : E →+* E) (X a i)) * inclR (F := F) R (J i j) * t)
      (hcj j)
    simp only [Finset.mul_sum, mul_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hinj := Matrix.mulVec_injective_of_isUnit
    ((Matrix.isUnit_iff_isUnit_det _).2 hu)
  have : c = 0 := hinj (by rw [h0, Matrix.mulVec_zero])
  exact fun b => congrFun this b

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument.

Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem det_gram_append_ne_zero (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) {r : ℕ}
    (y : Fin (r + 1) → Fin n → E) (f : Fin r → Fin n → E) (t : E) (ht : t ≠ 0)
    (hy : ∀ i j, gramE σ J y i j = if i = Fin.last r ∧ j = Fin.last r then t else 0)
    (hf : ∀ a b : Fin r, hE σ J (y a.castSucc) (f b) = if a = b then 1 else 0) :
    (gramE σ J (Fin.append y f)).det ≠ 0 := by
  intro h
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  have hy' : ∀ i j, hE σ J (y i) (y j) = if i = Fin.last r ∧ j = Fin.last r then t else 0 := hy
  have hf' : ∀ a b : Fin r, hE σ J (f a) (y b.castSucc) = if a = b then 1 else 0 := fun a b => by
    rw [← hE_swap hσ hJ, hf]
    by_cases hab : a = b
    · simp [hab]
    · simp [hab, Ne.symm hab]
  have row : ∀ k, ∑ b : Fin r, hE σ J (Fin.append y f k) (y b.castSucc) * c (Fin.castAdd r b.castSucc)
      + hE σ J (Fin.append y f k) (y (Fin.last r)) * c (Fin.castAdd r (Fin.last r))
      + ∑ b : Fin r, hE σ J (Fin.append y f k) (f b) * c (Fin.natAdd (r + 1) b) = 0 := fun k => by
    have := congrFun hc k
    simp only [Matrix.mulVec, dotProduct, gramE, Pi.zero_apply] at this
    rw [Fin.sum_univ_add, Fin.sum_univ_castSucc] at this
    simpa only [Fin.append_left, Fin.append_right] using this
  have h1 : ∀ a : Fin r, c (Fin.natAdd (r + 1) a) = 0 := fun a => by
    have := row (Fin.castAdd r a.castSucc)
    simpa [Fin.append_left, hy', hf, Fin.castSucc_ne_last] using this
  have h2 : c (Fin.castAdd r (Fin.last r)) = 0 := by
    have := row (Fin.castAdd r (Fin.last r))
    simpa [Fin.append_left, hy', h1, Fin.castSucc_ne_last, ht] using this
  have h3 : ∀ a : Fin r, c (Fin.castAdd r a.castSucc) = 0 := fun a => by
    have := row (Fin.natAdd (r + 1) a)
    simp only [Fin.append_right, hf', h1, h2] at this
    simpa using this
  apply hc0
  funext k
  refine Fin.addCases (fun i => ?_) (fun a => h1 a) k
  exact Fin.lastCases h2 h3 i

/- English proof (translation)
Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
-/
theorem gram_snoc (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) {r : ℕ}
    (e : Fin r → Fin n → E) (z : Fin n → E) (t : E) (he : ∀ a b, hE σ J (e a) (e b) = 0)
    (hez : ∀ a, hE σ J (e a) z = 0) (hz : hE σ J z z = t) (i j : Fin (r + 1)) :
    gramE σ J (Fin.snoc (α := fun _ => Fin n → E) e z) i j =
      if i = Fin.last r ∧ j = Fin.last r then t else 0 := by
  have hze : ∀ a, hE σ J z (e a) = 0 := fun a => by rw [← hE_swap hσ hJ, hez, map_zero]
  refine Fin.lastCases ?_ (fun a => ?_) i <;> refine Fin.lastCases ?_ (fun b => ?_) j <;>
    simp [gramE, he, hez, hze, hz, Fin.castSucc_ne_last]

end Alg

open scoped TensorProduct in

/- English proof (translation)
Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem _root_.GlobalTheory.FrameGram.conj_invol {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, hτ⟩ := h
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  apply τ.injective
  rw [hτ, hτ, star_star]

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem frame_gram {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : IsHermND σ J) {r : ℕ} (y : Fin (r + 1) → Fin n → E) (f : Fin r → Fin n → E) (T : F)
    (hT : T ≠ 0)
    (hy : ∀ i j, gramE σ J y i j =
      if i = Fin.last r ∧ j = Fin.last r then algebraMap F E (-T) else 0)
    (hf : ∀ a b : Fin r, hE σ J (y a.castSucc) (f b) = if a = b then 1 else 0) :
    (gramE σ J (Fin.append y f)).det ≠ 0 ∧
      (∀ i j, σ (gramE σ J (Fin.append y f) j i) = gramE σ J (Fin.append y f) i j) ∧
      (∀ i j, σ (gramE σ J y j i) = gramE σ J y i j) ∧
      ∀ (R : Type) [CommRing R] [Algebra F R],
        LinearIndependent (R ⊗[F] E) (ratTup (F := F) R y) := by
  have hd := det_gram_append_ne_zero (conj_invol hσ) hJ.1 y f _
    ((map_ne_zero (algebraMap F E)).2 (neg_ne_zero.2 hT)) hy hf
  refine ⟨hd, fun i j => hE_swap (conj_invol hσ) hJ.1 _ _,
    fun i j => hE_swap (conj_invol hσ) hJ.1 _ _, fun R _ _ => ?_⟩
  have h := (linearIndependent_ratTup_of_det_ne_zero R _ hd).comp (Fin.castAdd r)
    (Fin.castAdd_injective _ _)
  have e : ratTup (F := F) R (Fin.append y f) ∘ Fin.castAdd r = ratTup (F := F) R y := by
    funext a i
    simp [ratTup, Fin.append_left]
  rwa [e] at h

/- English proof (translation)
Substitute using the available equality. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem frame_gram_snoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : IsHermND σ J) {r : ℕ} (e f : Fin r → Fin n → E) (z : Fin n → E) (T : F) (hT : T ≠ 0)
    (he : ∀ a b, hE σ J (e a) (e b) = 0) (hez : ∀ a, hE σ J (e a) z = 0)
    (hz : hE σ J z z = algebraMap F E (-T))
    (hf : ∀ a b, hE σ J (e a) (f b) = if a = b then 1 else 0)
    (y : Fin (r + 1) → Fin n → E) (hy : y = Fin.snoc (α := fun _ => Fin n → E) e z)
    (w : Fin (r + 1 + r) → Fin n → E) (hw : w = Fin.append y f) :
    (gramE σ J w).det ≠ 0 ∧ (∀ i j, σ (gramE σ J w j i) = gramE σ J w i j) ∧
      (∀ i j, σ (gramE σ J y j i) = gramE σ J y i j) ∧
      (∀ i j, gramE σ J y i j =
        if i = Fin.last r ∧ j = Fin.last r then algebraMap F E (-T) else 0) ∧
      ∀ (R : Type) [CommRing R] [Algebra F R],
        LinearIndependent (R ⊗[F] E) (ratTup (F := F) R y) := by
  subst hw hy
  have hg := gram_snoc (conj_invol hσ) hJ.1 e z _ he hez hz
  obtain ⟨h1, h2, h3, h4⟩ := frame_gram hσ hJ _ f T hT hg (fun a b => by simpa using hf a b)
  exact ⟨h1, h2, h3, hg, h4⟩

end GlobalTheory.FrameGram
