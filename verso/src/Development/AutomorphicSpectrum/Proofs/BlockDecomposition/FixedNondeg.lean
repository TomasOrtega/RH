import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo

noncomputable section
open PositivityTheory.PfSWUS.Loc
namespace GlobalTheory.CompanionTheory.SiegLoc

variable {R : Type} [CommRing R]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem psi_pow {σ : R →+* R} {ϖ : R} {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ}
    (hψ : IsLevelChars σ ϖ ψ) (k j : ℕ) (a : R) :
    ψ (k + j) (Ideal.Quotient.mk _ (ϖ ^ j * a)) = ψ k (Ideal.Quotient.mk _ a) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← ih, ← Nat.add_assoc, pow_succ', mul_assoc]
    exact hψ.compat (k + j) (ϖ ^ j * a)

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem mem_lev_iff {ϖ : R} {k : ℕ} {a : R} : a ∈ lev ϖ k ↔ ∃ c, a = ϖ ^ k * c := by
  rw [lev, Ideal.mem_span_singleton, dvd_def]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem fixed_nondeg {σ : R →+* R} {ϖ : R} {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ}
    (hψ : IsLevelChars σ ϖ ψ) (hfix : σ ϖ = ϖ) (hreg : IsSMulRegular R ϖ) (k : ℕ) (a : R)
    (ha : σ a = a) (h : ∀ b, σ b = b → ψ k (Ideal.Quotient.mk _ (a * b)) = 1) : a ∈ lev ϖ k := by
  induction k generalizing a with
  | zero => simp [lev]
  | succ k ih =>
    have ha' : a ∈ lev ϖ k := ih a ha (fun b hb => by
      have := h (ϖ * b) (by simp [hfix, hb])
      rw [show a * (ϖ * b) = ϖ * (a * b) by ring, hψ.compat] at this
      exact this)
    obtain ⟨c, rfl⟩ := mem_lev_iff.1 ha'
    have hregk : IsSMulRegular R (ϖ ^ k) := hreg.pow k
    have hc : σ c = c := by
      apply hregk
      simpa [map_mul, map_pow, hfix] using ha
    have hc1 : c ∈ lev ϖ 1 := hψ.prim c hc (fun b hb => by
      have h1 := h b hb
      have h2 := psi_pow hψ 1 k (c * b)
      rw [Nat.add_comm 1 k, ← mul_assoc] at h2
      rw [← h2]; exact h1)
    obtain ⟨d, rfl⟩ := mem_lev_iff.1 hc1
    exact mem_lev_iff.2 ⟨d, by ring⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem trace_nondeg {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ}
    (hR : IsUnrQuad R σ ϖ q ε) (hψ : IsLevelChars σ ϖ ψ) (k : ℕ) (y : R)
    (h : ∀ t, ψ k (Ideal.Quotient.mk _ (t * y + σ (t * y))) = 1) : y ∈ lev ϖ k := by
  obtain ⟨u, hu, -⟩ := hR.basis
  have key : ∀ t, t * y + σ (t * y) ∈ lev ϖ k := fun t => by
    refine fixed_nondeg hψ hR.fix_ϖ hR.reg k _ (by simp [hR.inv, add_comm]) (fun b hb => ?_)
    have := h (b * t)
    convert this using 3
    simp only [map_mul, hb]; ring
  have h1 := key 1
  have h2 := key u
  have h3 : (u - σ u) * y ∈ lev ϖ k := by
    have : (u - σ u) * y = (u * y + σ (u * y)) - σ u * (1 * y + σ (1 * y)) := by
      simp only [map_mul, map_one]; ring
    rw [this]
    exact Ideal.sub_mem _ h2 (Ideal.mul_mem_left _ _ h1)
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have : y = v * ((u - σ u) * y) := by rw [← mul_assoc, hv, one_mul]
  rw [this]
  exact Ideal.mul_mem_left _ _ h3

end GlobalTheory.CompanionTheory.SiegLoc
end
