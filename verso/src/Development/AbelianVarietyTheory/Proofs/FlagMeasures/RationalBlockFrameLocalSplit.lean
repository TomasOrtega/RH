import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov.LocSplit

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem biorth_decomp {K : Type} [CommRing K] {n m : ℕ} {r : ℕ → ℕ}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) K} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) K}
    (h : Biorth r m T T') (y : Fin n → K) :
    y = ∑ b ∈ Finset.range m, T b *ᵥ (T' b *ᵥ y) := by
  have := congrArg (fun M : Matrix (Fin n) (Fin n) K => M *ᵥ y) h.2.2
  simp only [Matrix.one_mulVec, Matrix.sum_mulVec] at this
  simp only [Matrix.mulVec_mulVec]
  exact this.symm

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem biorth_map {E K : Type} [CommRing E] [CommRing K] {n m : ℕ} {r : ℕ → ℕ}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) E} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) E}
    (h : Biorth r m T T') (φ : E →+* K) {P : Matrix (Fin n) (Fin n) K} (hP : IsUnit P) :
    Biorth r m (fun b => P⁻¹ * (T b).map φ) (fun b => (T' b).map φ * P) := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hd
  have key : ∀ b b', (T' b).map φ * P * (P⁻¹ * (T b').map φ) = (T' b * T b').map φ := by
    intro b b'
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc P, h1, Matrix.one_mul, Matrix.map_mul]
  refine ⟨fun b => ?_, fun b b' hb => ?_, ?_⟩
  · rw [key, h.1 b, Matrix.map_one _ (map_zero φ) (map_one φ)]
  · rw [key, h.2.1 b b' hb, Matrix.map_zero _ (map_zero φ)]
  · have e : ∀ b, P⁻¹ * (T b).map φ * ((T' b).map φ * P)
        = P⁻¹ * φ.mapMatrix (T b * T' b) * P := by
      intro b
      rw [RingHom.mapMatrix_apply, Matrix.map_mul]
      simp only [Matrix.mul_assoc]
    simp only [e]
    rw [← Finset.sum_mul, ← Finset.mul_sum, ← map_sum, h.2.2, map_one, mul_one, h2]

/- English proof (translation)
By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
theorem map_mulVec_comp {E K : Type} [CommRing E] [CommRing K] {n p : ℕ} (φ : E →+* K)
    (A : Matrix (Fin n) (Fin p) E) (y : Fin p → E) :
    A.map φ *ᵥ (fun l => φ (y l)) = fun l => φ ((A *ᵥ y) l) := by
  ext i
  exact (RingHom.map_mulVec φ A y i).symm

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem block_mem {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {n m : ℕ} {r : ℕ → ℕ}
    {F : ℕ → Submodule R (Fin n → K)}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) K} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) K}
    {Λ : ∀ b, Submodule R (Fin (r b) → K)} (h : Biorth r m T T')
    (hF : ∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0))
    {b k : ℕ} (hb : b < k) {v : Fin (r b) → K} (hv : v ∈ Λ b) : T b *ᵥ v ∈ F k := by
  rw [hF]
  intro b'
  rw [Matrix.mulVec_mulVec]
  by_cases e : b' = b
  · subst e
    rw [h.1, Matrix.one_mulVec]
    exact ⟨hv, fun hk => absurd hk (by omega)⟩
  · rw [h.2.1 _ _ e, Matrix.zero_mulVec]
    exact ⟨zero_mem _, fun _ => rfl⟩

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions.

Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Treat this case separately. Treat this case separately. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Check the elementary cases of the proposition.

Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Treat this case separately.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem mem_locFlag_iff {E : Type} [Field E] [NumberField E] {n m : ℕ} {r : ℕ → ℕ}
    {F : ℕ → Submodule (𝓞 E) (Fin n → E)}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) E} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) E}
    {Λ : ∀ b, Submodule (𝓞 E) (Fin (r b) → E)} (h : Biorth r m T T')
    (hΛ : ∀ b, Submodule.IsLattice E (Λ b))
    (hF : ∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0))
    (φ : E →+* ℂ) {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (k : ℕ) (y : Fin n → ℂ) :
    y ∈ locFlag φ P F k ↔ ∀ b, k ≤ b → ((T' b).map φ * P) *ᵥ y = 0 := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  constructor
  · intro hy b hb
    unfold locFlag at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      have h0 := ((hF k z).1 hz b).2 hb
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, h1, Matrix.mul_one, map_mulVec_comp, h0]
      ext l
      simp
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy, add_zero]
    | smul c x _ hx => rw [Matrix.mulVec_smul, hx, smul_zero]
  · intro hy
    rw [biorth_decomp (biorth_map h φ hP) y]
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : k ≤ b
    · simp only [hy b hb, Matrix.mulVec_zero]
      exact zero_mem _
    have A : ∀ v : Fin (r b) → E,
        (P⁻¹ * (T b).map φ) *ᵥ (fun l => φ (v l)) ∈ locFlag φ P F k := by
      intro v
      have hv : v ∈ Submodule.span E (Λ b : Set (Fin (r b) → E)) := by
        rw [(hΛ b).span_eq_top]; trivial
      induction hv using Submodule.span_induction with
      | mem x hx =>
        rw [← Matrix.mulVec_mulVec, map_mulVec_comp]
        exact Submodule.subset_span ⟨_, block_mem h hF (by omega) hx, rfl⟩
      | zero =>
        have : (fun l => φ ((0 : Fin (r b) → E) l)) = 0 := by ext l; simp
        rw [this, Matrix.mulVec_zero]
        exact zero_mem _
      | add x y _ _ hx hy =>
        have : (fun l => φ ((x + y) l)) = (fun l => φ (x l)) + fun l => φ (y l) := by ext l; simp
        rw [this, Matrix.mulVec_add]
        exact add_mem hx hy
      | smul c x _ hx =>
        have : (fun l => φ ((c • x) l)) = φ c • fun l => φ (x l) := by ext l; simp
        rw [this, Matrix.mulVec_smul]
        exact Submodule.smul_mem _ _ hx
    have B : ∀ u : Fin (r b) → ℂ, (P⁻¹ * (T b).map φ) *ᵥ u ∈ locFlag φ P F k := by
      intro u
      have e : u = ∑ j, u j • fun l => φ ((Pi.single j (1 : E) : Fin (r b) → E) l) := by
        ext l
        simp [Finset.sum_apply, Pi.single_apply, apply_ite φ]
      rw [e, Matrix.mulVec_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [Matrix.mulVec_smul]
      exact Submodule.smul_mem _ _ (A _)
    exact B _

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem exists_lowers_blocks {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {n m : ℕ} {r : ℕ → ℕ}
    {F : ℕ → Submodule R (Fin n → K)}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) K} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) K}
    {Λ : ∀ b, Submodule R (Fin (r b) → K)} (h : Biorth r m T T')
    (hF : ∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0)) (c : ℕ)
    (Z : ∀ b : Fin m, Matrix (Fin (r b)) (Fin (r (b + c + 1))) K)
    (hZ : ∀ b : Fin m, ∀ y ∈ Λ (b + c + 1), Z b *ᵥ y ∈ Λ b) :
    ∃ Y ∈ lowers F c, ∀ b : Fin m, T' b * Y * T (b + c + 1) = Z b := by
  refine ⟨∑ b : Fin m, T b * Z b * T' (b + c + 1), fun a y hy => ?_, fun a => ?_⟩
  · rw [Matrix.sum_mulVec]
    refine Submodule.sum_mem _ fun b _ => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h1 := (hF _ y).1 hy (b + c + 1)
    by_cases hb : (b : ℕ) < a
    · exact block_mem h hF hb (hZ b _ h1.1)
    · rw [h1.2 (by omega), Matrix.mulVec_zero, Matrix.mulVec_zero]
      exact zero_mem _
  · rw [Matrix.mul_sum, Matrix.sum_mul, Finset.sum_eq_single a]
    · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h.1, Matrix.one_mul, Matrix.mul_assoc, h.1,
        Matrix.mul_one]
    · intro b _ hb
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h.2.1 _ _ (fun e => hb (Fin.ext e.symm)),
        Matrix.zero_mul, Matrix.zero_mul, Matrix.zero_mul]
    · intro ha
      exact absurd (Finset.mem_univ a) ha

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem locSplit : ∀ (E : Type) [Field E] [NumberField E] (n m : ℕ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (r : ℕ → ℕ) (T : ∀ b, Matrix (Fin n) (Fin (r b)) E) (T' : ∀ b, Matrix (Fin (r b)) (Fin n) E) (Λ : ∀ b, Submodule (𝓞 E) (Fin (r b) → E)), Biorth r m T T' → (∀ b, Submodule.IsLattice E (Λ b)) → (∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0)) → (∀ (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Biorth r m (fun b => P⁻¹ * (T b).map φ) (fun b => (T' b).map φ * P) ∧ ∀ k y, y ∈ locFlag φ P F k ↔ ∀ b, k ≤ b → ((T' b).map φ * P) *ᵥ y = 0) ∧ ∀ c, (∀ Y ∈ lowers F c, ∀ b, ∀ y ∈ Λ (b + c + 1), (T' b * Y * T (b + c + 1)) *ᵥ y ∈ Λ b) ∧ ∀ Z : ∀ b : Fin m, Matrix (Fin (r b)) (Fin (r (b + c + 1))) E, (∀ b : Fin m, ∀ y ∈ Λ (b + c + 1), Z b *ᵥ y ∈ Λ b) → ∃ Y ∈ lowers F c, ∀ b : Fin m, T' b * Y * T (b + c + 1) = Z b := by
  intro E _ _ n m F r T T' Λ h hΛ hF
  refine ⟨fun φ P hP => ⟨biorth_map h φ hP, mem_locFlag_iff h hΛ hF φ hP⟩, fun c => ⟨?_, ?_⟩⟩
  · intro Y hY b y hy
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact ((hF (b + 1) _).1 (hY (b + 1) _ (block_mem h hF (by omega) hy)) b).1
  · exact exists_lowers_blocks h hF c

end GlobalTheory.RadCov.LocSplit
