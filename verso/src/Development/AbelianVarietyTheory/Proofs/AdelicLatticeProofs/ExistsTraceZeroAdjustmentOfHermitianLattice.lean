import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermHyperbolic
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ImportsTer
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNsmulMulVecMem
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

namespace GlobalTheory.TvAdjust

/- English proof (translation)
Proceed by induction. Treat this case separately. Consider separately whether the proposition holds or fails. Supply the required witnesses or components. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_split (b : ℕ) (N : ℕ) (hN : 0 < N) :
    ∃ A B e : ℕ, N = A * B ∧ A ∣ b ^ e ∧ B.Coprime b := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    by_cases hg : N.Coprime b
    · exact ⟨1, N, 0, by simp, by simp, hg⟩
    · obtain ⟨M, hM⟩ := Nat.gcd_dvd_left N b
      have hg0 : 0 < N.gcd b := Nat.gcd_pos_of_pos_left _ hN
      have hg1 : 1 < N.gcd b := by
        rcases Nat.lt_or_ge 1 (N.gcd b) with h | h
        · exact h
        · exact absurd (show N.gcd b = 1 by omega) hg
      have hM0 : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; omega)
      have hlt : M < N := by nlinarith
      obtain ⟨A, B, e, h1, h2, h3⟩ := ih M hlt hM0
      refine ⟨N.gcd b * A, B, e + 1, by rw [mul_assoc, ← h1]; exact hM, ?_, h3⟩
      rw [pow_succ']
      exact mul_dvd_mul (Nat.gcd_dvd_right N b) h2

/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
-/
theorem exists_nsmul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (y : Fin n → E) : ∃ N : ℕ, 0 < N ∧ N • y ∈ L := by
  first
  | exact @_root_.GlobalTheory.NatSmulIntegral.exists_nat_smul_mem
  | exact _root_.GlobalTheory.NatSmulIntegral.exists_nat_smul_mem
  | (apply _root_.GlobalTheory.NatSmulIntegral.exists_nat_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatSmulIntegral.exists_nat_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatSmulIntegral.exists_nat_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatSmulIntegral.exists_nat_smul_mem ..)

/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
-/
theorem exists_nsmul_mulVec_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (M : Matrix (Fin n) (Fin n) E) :
    ∃ N : ℕ, 0 < N ∧ ∀ v ∈ L, N • (M *ᵥ v) ∈ L := by
  first
  | exact @_root_.GlobalTheory.IntegralMultipleClearDenominators.exists_nsmul_mulVec_mem
  | exact _root_.GlobalTheory.IntegralMultipleClearDenominators.exists_nsmul_mulVec_mem
  | (apply _root_.GlobalTheory.IntegralMultipleClearDenominators.exists_nsmul_mulVec_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralMultipleClearDenominators.exists_nsmul_mulVec_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralMultipleClearDenominators.exists_nsmul_mulVec_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralMultipleClearDenominators.exists_nsmul_mulVec_mem ..)

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem tv_mul_mulVec {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R)
    (x v : Fin n → R) (t : R) (q : ℤ) :
    tv σ G x (q * t) *ᵥ v = v + q • ((tv σ G x t - 1) *ᵥ v) := by
  have : tv σ G x (q * t) = 1 + q • (tv σ G x t - 1) := by
    ext a b
    simp [tv, mul_assoc]
  rw [this, add_mulVec, one_mulVec, smul_mulVec]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Move the embeddings inside the algebraic operations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Replace the chosen expression with an arbitrary variable. Replace the chosen expression with an arbitrary variable. Substitute using the available equality. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion.

Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem exists_tv_adjust : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), Module.finrank F E = 2 → IsHerm (c : E →+* E) G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (x : Fin n → E) (t : E) (b : ℕ), 0 < b → t + c t = 0 → ∃ (t' : E) (k e : ℕ), t' + c t' = 0 ∧ k.Coprime b ∧ ∀ v ∈ L, (∃ w ∈ L, k • (tv (c : E →+* E) G x t' *ᵥ v - tv (c : E →+* E) G x t *ᵥ v) = b • w) ∧ b ^ e • (tv (c : E →+* E) G x t' *ᵥ v) ∈ L ∧ b ^ e • (tv (c : E →+* E) G x (-t') *ᵥ v) ∈ L := by
  intro F E _ _ _ _ _ c n G _ _ L hfg hL x t b _ ht
  obtain ⟨N, hN0, hN⟩ := exists_nsmul_mulVec_mem L hfg hL (tv (c : E →+* E) G x t - 1)
  obtain ⟨A, B, e, hAB, ⟨r, hr⟩, hB⟩ := exists_split b N hN0
  have hBA : B.Coprime (b * A) := by
    refine Nat.Coprime.mul_right hB ?_
    exact Nat.Coprime.coprime_dvd_right ⟨r, hr⟩ (hB.pow_right e)
  obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.mpr hBA
  push_cast at huw
  refine ⟨((u * B : ℤ) : E) * t, B, e, ?_, hB, fun v hv => ?_⟩
  · rw [map_mul, map_intCast, ← mul_add, ht, mul_zero]
  have hz := hN v hv
  have h1 : tv (c : E →+* E) G x t *ᵥ v = v + (tv (c : E →+* E) G x t - 1) *ᵥ v := by
    rw [sub_mulVec, one_mulVec]; abel
  have key : ∀ s : ℤ, b ^ e • (tv (c : E →+* E) G x (((s * B : ℤ) : E) * t) *ᵥ v) ∈ L := by
    intro s
    rw [tv_mul_mulVec, smul_add]
    refine L.add_mem (nsmul_mem hv _) ?_
    have := zsmul_mem hz (s * r)
    convert this using 1
    rw [hr, hAB, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul]
    congr 1
    push_cast
    ring
  refine ⟨⟨(-w) • N • ((tv (c : E →+* E) G x t - 1) *ᵥ v), zsmul_mem hz _, ?_⟩, key u, ?_⟩
  · rw [tv_mul_mulVec]
    generalize tv (c : E →+* E) G x t *ᵥ v = y at h1 ⊢
    generalize (tv (c : E →+* E) G x t - 1) *ᵥ v = z at h1 ⊢
    subst h1
    have : v + (u * B) • z - (v + z) = (u * B - 1) • z := by
      rw [sub_smul, one_smul]; abel
    rw [this, hAB, ← natCast_zsmul, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul,
      smul_smul]
    congr 1
    push_cast
    linear_combination (B : ℤ) * huw
  · have := key (-u)
    convert this using 4
    push_cast
    ring

end GlobalTheory.TvAdjust
