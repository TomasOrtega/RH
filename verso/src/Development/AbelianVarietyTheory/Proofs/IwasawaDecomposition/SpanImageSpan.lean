import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NatCastMemPrimeOf

open NumberField

noncomputable section

namespace GlobalTheory.Mem.R3.LiftForms

variable {K K' : Type} [Field K] [Field K'] [NumberField K] [NumberField K'] (φ : K →+* K')

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Assume the hypotheses and unpack their components.
-/
theorem relSet_eq {n : ℕ} (S : Set (Fin n → K)) :
    {x' : Fin n → K' | ∃ x ∈ S, ∀ (k k' : Fin n), (k : ℕ) = k' → x' k' = φ (x k)} = (fun x k => φ (x k)) '' S := by
  ext x'
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨x, hx, h⟩; exact ⟨x, hx, funext fun k => (h k k rfl).symm⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, fun k k' hk => by rw [Fin.ext hk]⟩

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Proceed by induction. Treat this case separately.

Treat this case separately. Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Treat this case separately. Rewrite the hypotheses and the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Treat this case separately. Rewrite the hypotheses and the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem span_image_span {n : ℕ} (S : Set (Fin n → K)) :
    Submodule.span (𝓞 K') ((fun x k => φ (x k)) '' (Submodule.span (𝓞 K) S : Set (Fin n → K))) =
      Submodule.span (𝓞 K') ((fun (x : Fin n → K) k => φ (x k)) '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero =>
      rw [SetLike.mem_coe]
      convert Submodule.zero_mem (Submodule.span (𝓞 K') ((fun (x : Fin n → K) k => φ (x k)) '' S)) using 1
      funext k; simp
    | add y z _ _ hy hz =>
      rw [SetLike.mem_coe] at hy hz ⊢
      convert Submodule.add_mem _ hy hz using 1; funext k; simp
    | smul a y _ hy =>
      rw [SetLike.mem_coe] at hy ⊢
      convert Submodule.smul_mem _ (RingOfIntegers.mapRingHom φ a) hy using 1
      funext k
      simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
      rfl
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Introduce a local definition for the expression. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Treat this case separately. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Equip the data with the indicated structure. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the indicated hypotheses using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem span_image_inf {n : ℕ} (X : Submodule (𝓞 K) (Fin n → K)) (V : Submodule K (Fin n → K)) :
    Submodule.span (𝓞 K') ((fun (x : Fin n → K) k => φ (x k)) '' (X : Set (Fin n → K))) ⊓
      (Submodule.span K' ((fun (x : Fin n → K) k => φ (x k)) '' (V : Set (Fin n → K)))).restrictScalars (𝓞 K') =
    Submodule.span (𝓞 K') ((fun (x : Fin n → K) k => φ (x k)) ''
      ((X ⊓ V.restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) := by
  classical
  set Φ : (Fin n → K) → (Fin n → K') := fun x k => φ (x k) with hΦ
  set ψ : 𝓞 K →+* 𝓞 K' := RingOfIntegers.mapRingHom φ with hψdef
  have hψ : ∀ a : 𝓞 K, ((ψ a : 𝓞 K') : K') = φ (a : K) := fun a => rfl
  apply le_antisymm
  · rintro y ⟨hyX, hyV⟩

    let bQ := Module.finBasis K ((Fin n → K) ⧸ V)
    let ℓ : Fin (Module.finrank K ((Fin n → K) ⧸ V)) → (Fin n → K) →ₗ[K] K := fun r => (bQ.coord r).comp V.mkQ
    have hℓV : ∀ x, x ∈ V ↔ ∀ r, ℓ r x = 0 := by
      intro x
      constructor
      · intro hx r
        simp [ℓ, (Submodule.Quotient.mk_eq_zero V).2 hx]
      · intro h
        have : V.mkQ x = 0 := bQ.ext_elem fun r => by simpa [ℓ] using h r
        exact (Submodule.Quotient.mk_eq_zero V).1 this
    let q : Fin (Module.finrank K ((Fin n → K) ⧸ V)) → Fin n → K := fun r k => ℓ r (Pi.single k 1)
    have hℓ : ∀ r x, ℓ r x = ∑ k, q r k * x k := by
      intro r x
      rw [LinearMap.pi_apply_eq_sum_univ (ℓ r) x]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_eq_mul, mul_comm]
      congr 2
      funext j
      simp [Pi.single_apply, eq_comm]
    have hyℓ : ∀ r, ∑ k, φ (q r k) * y k = 0 := by
      intro r
      have key : ∀ z ∈ Submodule.span K' (Φ '' V), ∑ k, φ (q r k) * z k = 0 := by
        intro z hz
        induction hz using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨x, hx, rfl⟩ := hw
          have h0 := (hℓV x).1 hx r
          rw [hℓ] at h0
          have := congrArg φ h0
          rw [map_sum, map_zero] at this
          rw [← this]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_mul]
        | zero => simp
        | add a b _ _ ha hb => simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ha, hb, add_zero]
        | smul a b _ hb =>
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [show ∑ k, φ (q r k) * (a * b k) = a * ∑ k, φ (q r k) * b k by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring, hb, mul_zero]
      exact key y hyV
    obtain ⟨m, r0, g, hg⟩ := Submodule.mem_span_set'.1 hyX
    choose x hxX hx using fun i => (g i).2
    have hy : ∀ k, y k = ∑ i, (r0 i : K') * φ (x i k) := by
      intro k
      rw [← hg, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, Algebra.smul_def, ← hx i]
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K))
      (fun z : Fin m × Fin (Module.finrank K ((Fin n → K) ⧸ V)) => ℓ z.2 (x z.1))
    choose b hb using hd
    have hd0 : ((d : 𝓞 K) : K) ≠ 0 := by
      have := nonZeroDivisors.coe_ne_zero d
      exact_mod_cast this
    have hb' : ∀ i r, ((b (i, r) : 𝓞 K) : K) = ((d : 𝓞 K) : K) * ℓ r (x i) := fun i r => by
      have := hb (i, r)
      rw [Algebra.smul_def] at this
      exact this
    letI : Algebra (𝓞 K) (𝓞 K') := ψ.toAlgebra
    have hinj : Function.Injective ψ := fun a a' h => by
      have := congrArg (fun z : 𝓞 K' => (z : K')) h
      simp only [hψ] at this
      exact RingOfIntegers.ext (φ.injective this)
    haveI : Module.Flat (𝓞 K) (𝓞 K') := by
      rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
      rintro z ⟨a, ha⟩
      have ha' : ψ a * z = 0 := ha
      rcases mul_eq_zero.1 ha' with h | h
      · exact absurd (hinj (h.trans (map_zero ψ).symm)) (nonZeroDivisors.coe_ne_zero a)
      · exact h
    obtain ⟨N, a, yv, hr, ha⟩ := GlobalTheory.Proof.IdempotentLatticeSequence.flat_system (fun i r => b (i, r)) r0 (fun r => by
      apply RingOfIntegers.ext
      have h1 : ((∑ i, b (i, r) • r0 i : 𝓞 K') : K') = ∑ i, φ (b (i, r) : K) * (r0 i : K') := by
        rw [show ((∑ i, b (i, r) • r0 i : 𝓞 K') : K') = ∑ i, ((b (i, r) • r0 i : 𝓞 K') : K') from
          map_sum (algebraMap (𝓞 K') K') _ _]
        rfl
      rw [h1]
      simp only [hb', map_mul]
      have h2 := hyℓ r
      simp only [hy, Finset.mul_sum] at h2
      rw [Finset.sum_comm] at h2
      change _ = (0 : K')
      rw [← mul_zero (φ ((d : 𝓞 K) : K)), ← h2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hℓ, map_sum]
      simp only [map_mul, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring)
    let u : Fin N → Fin n → K := fun l => ∑ i, a i l • x i
    have huX : ∀ l, u l ∈ X := fun l => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hxX i)
    have huV : ∀ l, u l ∈ V := by
      intro l
      rw [hℓV]
      intro r
      have h1 := congrArg (fun z : 𝓞 K => (z : K)) (ha l r)
      simp only [map_sum, map_mul, hb', map_zero] at h1
      apply mul_left_cancel₀ hd0
      rw [mul_zero, ← h1, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.map_smul_of_tower, Algebra.smul_def]
      ring
    have hyu : y = ∑ l, yv l • Φ (u l) := by
      funext k
      rw [hy, Finset.sum_apply]
      simp only [Pi.smul_apply, hΦ, u, Finset.sum_apply, map_sum, Algebra.smul_def]
      have h2 : ∀ i, ((r0 i : 𝓞 K') : K') = ∑ l, φ (a i l : K) * (yv l : K') := by
        intro i
        rw [hr i]
        rw [show ((∑ l, a i l • yv l : 𝓞 K') : K') = ∑ l, ((a i l • yv l : 𝓞 K') : K') from
          map_sum (algebraMap (𝓞 K') K') _ _]
        rfl
      simp only [h2, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
      change _ = (algebraMap (𝓞 K') K' (yv l)) * φ (((a i l) : K) * x i k)
      rw [map_mul]
      change φ (a i l : K) * (yv l : K') * φ (x i k) = (yv l : K') * (φ (a i l : K) * φ (x i k))
      ring
    rw [hyu]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨u l, ⟨huX l, huV l⟩, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨x, ⟨hxX, hxV⟩, rfl⟩
    exact ⟨Submodule.subset_span ⟨x, hxX, rfl⟩, Submodule.subset_span ⟨x, hxV, rfl⟩⟩

end GlobalTheory.Mem.R3.LiftForms

namespace GlobalTheory.Mem.R3.LiftForms
variable {K K' : Type} [Field K] [Field K'] [NumberField K] [NumberField K'] (φ : K →+* K')

/- English proof (translation)
Substitute using the available equality. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem span_rel_inf {n n' : ℕ} (hn : n = n') (S : Set (Fin n → K)) (V : Submodule K (Fin n → K))
    (S' : Set (Fin n' → K')) (V' : Submodule K' (Fin n' → K'))
    (hS : S' = {x' | ∃ x ∈ S, ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)})
    (hV : V' = Submodule.span K' {x' | ∃ x ∈ V, ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)}) :
    Submodule.span (𝓞 K') S' ⊓ V'.restrictScalars (𝓞 K') =
      Submodule.span (𝓞 K') {x' | ∃ x ∈ Submodule.span (𝓞 K) S ⊓ V.restrictScalars (𝓞 K),
        ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)} := by
  subst hn hS hV
  have e1 : {x' : Fin n → K' | ∃ x ∈ V, ∀ (k k' : Fin n), (k : ℕ) = k' → x' k' = φ (x k)} =
      (fun x k => φ (x k)) '' (V : Set (Fin n → K)) := relSet_eq φ (V : Set (Fin n → K))
  have e2 : {x' : Fin n → K' | ∃ x ∈ Submodule.span (𝓞 K) S ⊓ V.restrictScalars (𝓞 K),
      ∀ (k k' : Fin n), (k : ℕ) = k' → x' k' = φ (x k)} =
      (fun x k => φ (x k)) '' ((Submodule.span (𝓞 K) S ⊓ V.restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin n → K)) :
        Set (Fin n → K)) := relSet_eq φ _
  rw [relSet_eq, e1, e2, ← span_image_span φ S]
  exact span_image_inf φ _ V

end GlobalTheory.Mem.R3.LiftForms
