import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact
open GlobalTheory.Orb (archMat)

namespace GlobalTheory.UAut.TorusLevi

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately.

Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Treat this case separately. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem prodTens_ext {F E A B : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] {z z' : (A × B) ⊗[F] E}
    (a : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z')
    (b : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z') : z = z' := by
  have key : ∀ x : (A × B) ⊗[F] E, TensorProduct.prodLeft F F A B E x =
      (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) x,
        Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp <;> rfl
    | tmul p e =>
      obtain ⟨p₁, p₂⟩ := p
      simp
    | add x y hx hy => simp [hx, hy]
  apply (TensorProduct.prodLeft F F A B E).injective
  rw [key, key, a, b]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

omit [NumberField E] in

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities.

Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem adele_ext {z z' : AF F ⊗[F] E} (a : ∀ w, compInf F E w z = compInf F E w z')
    (b : (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom z =
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom z') : z = z' := by
  classical
  have key : ∀ x : AF F ⊗[F] E, ∀ w : InfinitePlace F,
      TensorProduct.piLeft F E (fun w : InfinitePlace F => w.Completion)
        (Algebra.TensorProduct.map (AlgHom.fst F (Ainf F) (Af F)) (AlgHom.id F E) x) w = compInf F E w x := by
    intro x w
    induction x using TensorProduct.induction_on with
    | zero =>
      rw [map_zero (compInf F E w)]
      erw [map_zero]
      try erw [map_zero]
      try rfl
    | tmul p e => rfl
    | add x y hx hy =>
      rw [map_add (compInf F E w), ← hx, ← hy]
      erw [map_add, map_add]
      try rfl
  have hinf : Algebra.TensorProduct.map (AlgHom.fst F (Ainf F) (Af F)) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.fst F (Ainf F) (Af F)) (AlgHom.id F E) z' := by
    apply (TensorProduct.piLeft F E (fun w : InfinitePlace F => w.Completion)).injective
    funext w
    rw [key, key, a]
  exact prodTens_ext hinf b

/- English proof (translation)
Establish an intermediate fact. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem exists_diagonal (h : IsCMExt F E σ) {a : GAd σ J} (ha : a ∈ infPts σ J) (Z : Matrix (Fin n) (Fin r) E)
    (s : Fin r → ℝ) (hs : ∀ (w : InfinitePlace F) (τ : EmbOver E w),
      archMat σ J τ (projArch σ J w a) * Z.map τ.1 = Z.map τ.1 * diagonal (fun i => (s i : ℂ))) :
    ∃ δ : Fin r → AF F ⊗[F] E, (matHom _ σ J a).1 * adMat F Z = adMat F Z * diagonal δ := by
  classical
  have hR : ∀ w : InfinitePlace F, w.IsReal := fun w => h.1.isReal w
  let c : Fin r → Ainf F := fun i w => (InfinitePlace.Completion.ringEquivRealOfIsReal (hR w)).symm (s i)
  refine ⟨fun i => (pairA F (c i) 1 : AF F) ⊗ₜ[F] (1 : E), ?_⟩
  ext i j
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  refine adele_ext (fun w => ?_) ?_
  · obtain ⟨τ⟩ := (inferInstance : Nonempty (EmbOver E w))
    apply (infEmb_bijective h τ).1
    have harch : ∀ k l, archMat σ J τ (projArch σ J w a) k l =
        infEmb τ (compInf F E w ((matHom _ σ J a).1 k l)) := by
      intro k l
      show infEmb τ (((matHom _ σ J (projArch σ J w a)) : Matrix (Fin n) (Fin n) _) k l) = _
      rw [matHom_projArch]
      rfl
    have hZ : ∀ k l, infEmb τ (compInf F E w (inclR (F := F) (AF F) (Z k l))) = τ.1 (Z k l) := by
      intro k l
      simp [compInf, inclR, infEmb_tmul]
    have hev : evInf F w (pairA F (c j) 1) = c j w := rfl
    have hc : infEmb τ (compInf F E w ((pairA F (c j) 1 : AF F) ⊗ₜ[F] (1 : E))) = (s j : ℂ) := by
      simp only [compInf, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.coe_id, id_eq, hev, infEmb_tmul, map_one, mul_one]
      rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (hR w),
        ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply (hR w), RingEquiv.apply_symm_apply]
    have hij := congrFun (congrFun (hs w τ) i) j
    rw [Matrix.mul_apply, Matrix.mul_diagonal] at hij
    simp only [map_sum, map_mul, Matrix.map_apply, hZ, hc, ← harch]
    simpa only [Matrix.map_apply] using hij
  · have hfin : ∀ k l, (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom ((matHom _ σ J a).1 k l) =
        (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) k l := fun k l =>
      congrArg (fun g : GL (Fin n) (Af F ⊗[F] E) => (g : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) k l)
        (MonoidHom.mem_ker.mp ha)
    have hδ : (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
        ((pairA F (c j) 1 : AF F) ⊗ₜ[F] (1 : E)) = 1 := by
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
      rfl
    simp only [map_sum, map_mul, hfin, hδ, Matrix.one_apply, ite_mul, one_mul, zero_mul, mul_one,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem mem_parFlag (h : IsCMExt F E σ) {a : GAd σ J} (ha : a ∈ infPts σ J) (Z : Matrix (Fin n) (Fin r) E)
    (d : Fin r → ℕ) (s : Fin r → ℝ) (h0 : ∀ i, s i ≠ 0) (hs : ∀ (w : InfinitePlace F) (τ : EmbOver E w),
      archMat σ J τ (projArch σ J w a) * Z.map τ.1 = Z.map τ.1 * diagonal (fun i => (s i : ℂ))) :
    a ∈ parFlag σ J Z d := by
  have hinv : ∀ (w : InfinitePlace F) (τ : EmbOver E w),
      archMat σ J τ (projArch σ J w a⁻¹) * Z.map τ.1 = Z.map τ.1 * diagonal (fun i => (((s i)⁻¹ : ℝ) : ℂ)) := by
    intro w τ
    have h1 : archMat σ J τ (projArch σ J w a⁻¹) * archMat σ J τ (projArch σ J w a) = 1 := by
      rw [← map_mul (archMat σ J τ), ← map_mul (projArch σ J w), inv_mul_cancel, map_one, map_one]
    have h2 : diagonal (fun i => ((s i : ℝ) : ℂ)) * diagonal (fun i => (((s i)⁻¹ : ℝ) : ℂ)) = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      rw [Complex.ofReal_inv, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (h0 i))]
    calc archMat σ J τ (projArch σ J w a⁻¹) * Z.map τ.1
        = archMat σ J τ (projArch σ J w a⁻¹) * (Z.map τ.1 *
            (diagonal (fun i => ((s i : ℝ) : ℂ)) * diagonal (fun i => (((s i)⁻¹ : ℝ) : ℂ)))) := by
          rw [h2, Matrix.mul_one]
      _ = (archMat σ J τ (projArch σ J w a⁻¹) * (archMat σ J τ (projArch σ J w a) * Z.map τ.1)) *
            diagonal (fun i => (((s i)⁻¹ : ℝ) : ℂ)) := by
          rw [hs w τ]
          simp only [Matrix.mul_assoc]
      _ = Z.map τ.1 * diagonal (fun i => (((s i)⁻¹ : ℝ) : ℂ)) := by
          rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  obtain ⟨δ, hδ⟩ := exists_diagonal h ha Z s hs
  obtain ⟨δ', hδ'⟩ := exists_diagonal h (inv_mem ha) Z (fun i => (s i)⁻¹) hinv
  exact ⟨⟨diagonal δ, blockTriangular_diagonal δ, hδ⟩, diagonal δ', blockTriangular_diagonal δ', hδ'⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts.
-/
theorem torus_mem_leviFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ), Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → ∀ (t : Fin r → ℝ) (a : GAd σ J), (∀ i, t i ≠ 0) → IsTorusElt σ J X Y t a → a ∈ leviFlag σ J X Y d := by
  intro F E _ _ _ _ _ σ h n J _ r X Y d _ _ _ t a ht ha
  obtain ⟨ha1, ha2⟩ := ha
  refine ⟨mem_parFlag h ha1 X d t ht fun w τ => (ha2 w τ).1, ?_⟩
  refine mem_parFlag h ha1 Y d (fun i => (t i)⁻¹) (fun i => inv_ne_zero (ht i)) fun w τ => ?_
  simpa only [Complex.ofReal_inv] using (ha2 w τ).2.1

end GlobalTheory.UAut.TorusLevi

end
