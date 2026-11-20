import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOfIsoX

noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

/- English proof (translation)
The claim follows from `(PI.OmLocU.Orb.oSub (E := E) v).1`.
-/
theorem one_mem_O : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := (PI.OmLocU.Orb.oSub (E := E) v).1

/- English proof (translation)
The claim follows from `Finset.prod_induction _ (· ∈ OEv (E := E) v) (fun _ _ => oEv_mul v) (one_mem_O v) (fun i _ => hf i)`.
-/
theorem prod_int {m : ℕ} (f : Fin m → Fv F v ⊗[F] E) (hf : ∀ i, f i ∈ OEv (E := E) v) :
    ∏ i, f i ∈ OEv (E := E) v :=
  Finset.prod_induction _ (· ∈ OEv (E := E) v) (fun _ _ => oEv_mul v) (one_mem_O v) (fun i _ => hf i)

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Use `oEv_sum v _ _ fun p _ => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h | h <;> rw [h]`. Rewrite using `[one_smul]`. Conclude with `prod_int v _ fun i => hA _ _`.

Rewrite using `[Units.neg_smul, one_smul]`. Conclude with `oEv_neg v (prod_int v _ fun i => hA _ _)`.
-/
theorem det_int {m : ℕ} (A : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) (hA : ∀ i j, A i j ∈ OEv (E := E) v) :
    A.det ∈ OEv (E := E) v := by
  rw [Matrix.det_apply]
  refine oEv_sum v _ _ fun p _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h | h <;> rw [h]
  · rw [one_smul]; exact prod_int v _ fun i => hA _ _
  · rw [Units.neg_smul, one_smul]; exact oEv_neg v (prod_int v _ fun i => hA _ _)

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.adjugate_apply]`. Use `det_int v _ fun k l => ?_` and prove the remaining obligations. Rewrite using `[Matrix.updateRow_apply]`. Use `split_ifs`.

Rewrite using `[Pi.single_apply]`. Use `split_ifs`. Conclude with `one_mem_O v`. Conclude with `oEv_zero v`. Conclude with `hA k l`.
-/
theorem adj_int {m : ℕ} (A : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) (hA : ∀ i j, A i j ∈ OEv (E := E) v) :
    ∀ i j, A.adjugate i j ∈ OEv (E := E) v := by
  intro i j
  rw [Matrix.adjugate_apply]
  refine det_int v _ fun k l => ?_
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]; split_ifs
    · exact one_mem_O v
    · exact oEv_zero v
  · exact hA k l

/- English proof (translation)
Use `⟨hX, fun c hc i => ?_⟩` and prove the remaining obligations. Establish `hGi : ∀ i j, gramR (Fv F v) σ J X i j ∈ OEv (E` using `E) v := fun i j => hR_mem_oEv σ J v Λ hSD (hX i) (hX j)`. Establish `hGc : ∀ j, Matrix.mulVec (gramR (Fv F v) σ J X) c j ∈ OEv (E` using `E) v := by`. Introduce `j`. Use `hR_mem_oEv σ J v Λ hSD (hX j) hc` as an intermediate fact.

Rewrite `this` using `[hR_sum_smul_right]`. Establish `e : Matrix.mulVec (gramR (Fv F v) σ J X) c j = ∑ i, c i * hR (Fv F v) σ J (X j) (X i)`. Simplify using `only [Matrix.mulVec, dotProduct, gramR]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`. Rewrite using `[e]`.

Conclude with `this`. Take `⟨u, huO, -, hdu⟩` from `hu`. Establish `key : c i = u * Matrix.mulVec (gramR (Fv F v) σ J X).adjugate (Matrix.mulVec (gramR (Fv F v) σ J X) c) i`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm u, hdu, one_mul]`. Rewrite using `[key]`.

Use `oEv_mul v huO ?_` and prove the remaining obligations. Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `oEv_sum v _ _ fun j _ => oEv_mul v (adj_int v _ hGi i j) (hGc j)`.
-/
theorem uniPrim {a : ℕ} (hSD : IsSDLoc σ J v Λ) (X : TupV (E := E) v n a)
    (hX : ∀ i, X i ∈ latLoc (E := E) v Λ)
    (hu : ∃ u ∈ OEv (E := E) v, (gramR (Fv F v) σ J X).det ∈ OEv (E := E) v ∧ (gramR (Fv F v) σ J X).det * u = 1) :
    IsPrim v Λ X := by
  refine ⟨hX, fun c hc i => ?_⟩
  have hGi : ∀ i j, gramR (Fv F v) σ J X i j ∈ OEv (E := E) v := fun i j => hR_mem_oEv σ J v Λ hSD (hX i) (hX j)
  have hGc : ∀ j, Matrix.mulVec (gramR (Fv F v) σ J X) c j ∈ OEv (E := E) v := by
    intro j
    have := hR_mem_oEv σ J v Λ hSD (hX j) hc
    rw [hR_sum_smul_right] at this
    have e : Matrix.mulVec (gramR (Fv F v) σ J X) c j = ∑ i, c i * hR (Fv F v) σ J (X j) (X i) := by
      simp only [Matrix.mulVec, dotProduct, gramR]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [e]; exact this
  obtain ⟨u, huO, -, hdu⟩ := hu
  have key : c i = u * Matrix.mulVec (gramR (Fv F v) σ J X).adjugate
      (Matrix.mulVec (gramR (Fv F v) σ J X) c) i := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply,
      smul_eq_mul, ← mul_assoc, mul_comm u, hdu, one_mul]
  rw [key]
  refine oEv_mul v huO ?_
  simp only [Matrix.mulVec, dotProduct]
  exact oEv_sum v _ _ fun j _ => oEv_mul v (adj_int v _ hGi i j) (hGc j)

def IsoW (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∃ T : Matrix (Fin (a + 1)) (Fin (a + 1)) (Fv F v ⊗[F] E),
    (∃ u ∈ OEv (E := E) v, T.det ∈ OEv (E := E) v ∧ T.det * u = 1) ∧
    ∀ X ∈ PrimT v Λ a, gramR (Fv F v) σ J X = gramR (Fv F v) σ J Y →
      ∃ w ∈ latLoc (E := E) v Λ, gramR (Fv F v) σ J (augT v X w) = T

/- English proof (translation)
Introduce `hG`. Take `⟨T, hTu, h⟩` from `hW hG`. Use `⟨T, hTu, fun X hX hXY => ?_⟩` and prove the remaining obligations. Take `⟨w, hw, hg⟩` from `h X hX hXY`. Use `⟨w, uniPrim σ J v Λ hG.2.2.1 _ (fun i => ?_) (by rw [hg]; exact hTu), hg⟩` and prove the remaining obligations.

Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => simp [augT]`. Conclude with `hw`. Consider the case `cast j => rw [augT_castSucc]`. Conclude with `hX.1 j`.
-/
theorem isoExt_of (a : ℕ) (Y : TupV (E := E) v n a) (hW : IsoW σ J ψ v Λ a Y) : IsoExt σ J ψ v Λ a Y := by
  intro hG
  obtain ⟨T, hTu, h⟩ := hW hG
  refine ⟨T, hTu, fun X hX hXY => ?_⟩
  obtain ⟨w, hw, hg⟩ := h X hX hXY
  refine ⟨w, uniPrim σ J v Λ hG.2.2.1 _ (fun i => ?_) (by rw [hg]; exact hTu), hg⟩
  induction i using Fin.lastCases with
  | last => simp [augT]; exact hw
  | cast j => rw [augT_castSucc]; exact hX.1 j

end PI.OmVd
