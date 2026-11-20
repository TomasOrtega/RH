import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.LeftInvOOf

noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Take `⟨h0, -, hint⟩` from `unif_spec v ϖ hϖ`. Use `set Mo : Matrix (Fin n) (Fin a) (Red.OR (E := E) v) := fun k i => ⟨M k i, hM k i⟩ with hMo`. Establish `hcoe : (Red.OR (E` using `E) v).subtype = (Red.OR (E := E) v).subtype := rfl`. Establish `hinj : Function.Injective (Mo.map π).mulVec`. Introduce `x y hxy`.

Establish `hz : (Mo.map π).mulVec (x - y) = 0` using `by rw [Matrix.mulVec_sub, hxy, sub_self]`. Take `⟨cO, hcO⟩ : ∃ cO : Fin a → Red.OR (E` from `E) v, ∀ i, π (cO i) = (x - y) i := ⟨fun i => (hsurj ((x - y) i)).choose, fun i => (hsurj ((x - y) i)).choose_spec⟩`. Establish `hred : ∀ k, π ((Mo.mulVec cO) k) = 0`. Introduce `k`. Rewrite using `[RingHom.map_mulVec]`.

Establish `: (π ∘ cO) = x - y` using `funext hcO`. Rewrite using `[this, hz]`. Both sides reduce to the same expression. Establish `hPO : ∀ k, ∃ m ∈ OEv (E` using `E) v, ((Mo.mulVec cO k : Red.OR (E := E) v) : Fv F v ⊗[F] E) = sc (E := E) v ϖ * m := fun k => (hker _).1 (hred k)`. Use `choose m hmO hm using hPO`.

Establish `hc : ∀ i, sc (E` using `E) v ϖ⁻¹ * (cO i : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by`. Use `hsat _ fun k => ?_` and prove the remaining obligations. Establish `e : Matrix.mulVec M (fun i => sc (E` using `E) v ϖ⁻¹ * (cO i : Fv F v ⊗[F] E)) k = sc (E := E) v ϖ⁻¹ * ((Mo.mulVec cO k : Red.OR (E := E) v) : Fv F v ⊗[F] E) := by`. Simplify using `only [Matrix.mulVec, dotProduct, Finset.mul_sum]`. Rewrite using `[show ((∑ i, Mo k i * cO i : Red.OR (E := E) v) : Fv F v ⊗[F] E) = ∑ i, ((Mo k i : Fv F v ⊗[F] E) * (cO i : Fv F v ⊗[F] E)) by push_cast; rfl]`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, hm k, ← mul_assoc, sc_mul, inv_mul_cancel₀ h0, sc_one, one_mul]`. Conclude with `hmO k`.

Use function extensionality and compare the values at `i`. Establish `: π (cO i) = 0`. Rewrite using `[hker]`. Use `⟨sc (E := E) v ϖ⁻¹ * (cO i : Fv F v ⊗[F] E), hc i, ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, sc_mul, mul_inv_cancel₀ h0, sc_one, one_mul]`.

Rewrite using `[← sub_eq_zero, ← Pi.sub_apply, ← hcO i, this]`. Take `⟨Nb, hNb⟩` from `hLK _ hinj`. Take `⟨NO, hNO⟩ : ∃ NO : Matrix (Fin a) (Fin n) (Red.OR (E` from `E) v), ∀ i k, π (NO i k) = Nb i k := ⟨fun i k => (hsurj (Nb i k)).choose, fun i k => (hsurj (Nb i k)).choose_spec⟩`. Establish `hmap : (NO * Mo).map π = 1`. Rewrite using `[Matrix.map_mul]`.

Establish `: NO.map π = Nb` using `by ext i k; exact hNO i k`. Rewrite using `[this, hNb]`. Use `set P : Matrix (Fin a) (Fin a) (Red.OR (E := E) v) := NO * Mo with hP`. Establish `hPO : ∀ i j, ∃ b ∈ OEv (E` using `E) v, (((P - 1 : Matrix (Fin a) (Fin a) (Red.OR (E := E) v)) i j : Red.OR (E := E) v) : Fv F v ⊗[F] E) = sc (E := E) v ϖ * b := by`. Introduce `i j`.

Use `(hker _).1 ?_` and prove the remaining obligations. Use `congrFun (congrFun hmap i) j` as an intermediate fact. Simplify using `only [Matrix.map_apply] at this`. Rewrite using `[Matrix.sub_apply, map_sub, this]`. Simplify using `[Matrix.one_apply]`.

Use `choose B hBO hB using hPO`. Use `⟨NO.map (Red.OR (E := E) v).subtype, fun i j => B i j, fun i k => (NO i k).2, hBO, ?_⟩` and prove the remaining obligations. Establish `hM' : M = Mo.map (Red.OR (E` using `E) v).subtype := by ext k i; rfl`. Rewrite using `[hM', ← Matrix.map_mul, ← hP]`. Use extensionality with `i j`.

Establish `h1` using `hB i j`. Rewrite `h1` using `[Matrix.sub_apply]`. Simplify using `only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`. Establish `e1 : (Red.OR (E` using `E) v).subtype (P i j) = (((P i j - (1 : Matrix (Fin a) (Fin a) (Red.OR (E := E) v)) i j : Red.OR (E := E) v) : Fv F v ⊗[F] E) + (((1 : Matrix (Fin a) (Fin a) (Red.OR (E := E) v)) i j : Red.OR (E := E) v) : Fv F v ⊗[F] E)) := by show (P i j : Fv F v ⊗[F] E) = _ push_cast; ring`. Rewrite using `[e1, h1, Matrix.one_apply, Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp [add_comm] <;> rfl`.
-/
theorem leftInvRes_gen {a : ℕ} {K : Type} [CommRing K] (ϖ : Fv F v) (hϖ : IsUnif v ϖ)
    (π : Red.OR (E := E) v →+* K) (hsurj : Function.Surjective π)
    (hker : ∀ x : Red.OR (E := E) v, π x = 0 ↔ (x : Fv F v ⊗[F] E) ∈ PO (E := E) v ϖ)
    (hLK : ∀ Mb : Matrix (Fin n) (Fin a) K, Function.Injective Mb.mulVec →
      ∃ Nb : Matrix (Fin a) (Fin n) K, Nb * Mb = 1)
    (M : Matrix (Fin n) (Fin a) (Fv F v ⊗[F] E)) (hM : ∀ k i, M k i ∈ OEv (E := E) v)
    (hsat : ∀ c : Fin a → Fv F v ⊗[F] E, (∀ k, Matrix.mulVec M c k ∈ OEv (E := E) v) → ∀ i, c i ∈ OEv (E := E) v) :
    ∃ N0 : Matrix (Fin a) (Fin n) (Fv F v ⊗[F] E), ∃ B : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E),
      (∀ i k, N0 i k ∈ OEv (E := E) v) ∧ (∀ i j, B i j ∈ OEv (E := E) v) ∧
      N0 * M = 1 + sc (E := E) v ϖ • B := by
  classical
  obtain ⟨h0, -, hint⟩ := unif_spec v ϖ hϖ
  set Mo : Matrix (Fin n) (Fin a) (Red.OR (E := E) v) := fun k i => ⟨M k i, hM k i⟩ with hMo
  have hcoe : (Red.OR (E := E) v).subtype = (Red.OR (E := E) v).subtype := rfl

  have hinj : Function.Injective (Mo.map π).mulVec := by
    intro x y hxy
    have hz : (Mo.map π).mulVec (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    obtain ⟨cO, hcO⟩ : ∃ cO : Fin a → Red.OR (E := E) v, ∀ i, π (cO i) = (x - y) i :=
      ⟨fun i => (hsurj ((x - y) i)).choose, fun i => (hsurj ((x - y) i)).choose_spec⟩
    have hred : ∀ k, π ((Mo.mulVec cO) k) = 0 := by
      intro k
      rw [RingHom.map_mulVec]
      have : (π ∘ cO) = x - y := funext hcO
      rw [this, hz]
      rfl
    have hPO : ∀ k, ∃ m ∈ OEv (E := E) v, ((Mo.mulVec cO k : Red.OR (E := E) v) : Fv F v ⊗[F] E) =
        sc (E := E) v ϖ * m := fun k => (hker _).1 (hred k)
    choose m hmO hm using hPO
    have hc : ∀ i, sc (E := E) v ϖ⁻¹ * (cO i : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
      refine hsat _ fun k => ?_
      have e : Matrix.mulVec M (fun i => sc (E := E) v ϖ⁻¹ * (cO i : Fv F v ⊗[F] E)) k =
          sc (E := E) v ϖ⁻¹ * ((Mo.mulVec cO k : Red.OR (E := E) v) : Fv F v ⊗[F] E) := by
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
        rw [show ((∑ i, Mo k i * cO i : Red.OR (E := E) v) : Fv F v ⊗[F] E) =
            ∑ i, ((Mo k i : Fv F v ⊗[F] E) * (cO i : Fv F v ⊗[F] E)) by push_cast; rfl]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [e, hm k, ← mul_assoc, sc_mul, inv_mul_cancel₀ h0, sc_one, one_mul]
      exact hmO k
    funext i
    have : π (cO i) = 0 := by
      rw [hker]
      refine ⟨sc (E := E) v ϖ⁻¹ * (cO i : Fv F v ⊗[F] E), hc i, ?_⟩
      rw [← mul_assoc, sc_mul, mul_inv_cancel₀ h0, sc_one, one_mul]
    rw [← sub_eq_zero, ← Pi.sub_apply, ← hcO i, this]
  obtain ⟨Nb, hNb⟩ := hLK _ hinj
  obtain ⟨NO, hNO⟩ : ∃ NO : Matrix (Fin a) (Fin n) (Red.OR (E := E) v), ∀ i k, π (NO i k) = Nb i k :=
    ⟨fun i k => (hsurj (Nb i k)).choose, fun i k => (hsurj (Nb i k)).choose_spec⟩
  have hmap : (NO * Mo).map π = 1 := by
    rw [Matrix.map_mul]
    have : NO.map π = Nb := by ext i k; exact hNO i k
    rw [this, hNb]
  set P : Matrix (Fin a) (Fin a) (Red.OR (E := E) v) := NO * Mo with hP
  have hPO : ∀ i j, ∃ b ∈ OEv (E := E) v, (((P - 1 : Matrix (Fin a) (Fin a) (Red.OR (E := E) v)) i j :
      Red.OR (E := E) v) : Fv F v ⊗[F] E) = sc (E := E) v ϖ * b := by
    intro i j
    refine (hker _).1 ?_
    have := congrFun (congrFun hmap i) j
    simp only [Matrix.map_apply] at this
    rw [Matrix.sub_apply, map_sub, this]
    simp [Matrix.one_apply]
  choose B hBO hB using hPO
  refine ⟨NO.map (Red.OR (E := E) v).subtype, fun i j => B i j, fun i k => (NO i k).2, hBO, ?_⟩
  have hM' : M = Mo.map (Red.OR (E := E) v).subtype := by ext k i; rfl
  rw [hM', ← Matrix.map_mul, ← hP]
  ext i j
  have h1 := hB i j
  rw [Matrix.sub_apply] at h1
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have e1 : (Red.OR (E := E) v).subtype (P i j) =
      (((P i j - (1 : Matrix (Fin a) (Fin a) (Red.OR (E := E) v)) i j : Red.OR (E := E) v) : Fv F v ⊗[F] E) +
        (((1 : Matrix (Fin a) (Fin a) (Red.OR (E := E) v)) i j : Red.OR (E := E) v) : Fv F v ⊗[F] E)) := by
    show (P i j : Fv F v ⊗[F] E) = _
    push_cast; ring
  rw [e1, h1, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp [add_comm] <;> rfl

end PI.OmVd
