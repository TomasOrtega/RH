import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo

noncomputable section
open PositivityTheory.PfSWUS.Loc
namespace GlobalTheory.CompanionTheory.SiegLoc

variable {R : Type} [CommRing R]

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Rewrite using `[← ih, ← Nat.add_assoc, pow_succ', mul_assoc]`. Conclude with `hψ.compat (k + j) (ϖ ^ j * a)`.
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
Rewrite using `[lev, Ideal.mem_span_singleton, dvd_def]`.
-/
theorem mem_lev_iff {ϖ : R} {k : ℕ} {a : R} : a ∈ lev ϖ k ↔ ∃ c, a = ϖ ^ k * c := by
  rw [lev, Ideal.mem_span_singleton, dvd_def]

/- English proof (translation)
Proceed by induction on `k generalizing a with`. Consider the case `zero => simp [lev]`. Consider the case `succ k ih`. Establish `ha' : a ∈ lev ϖ k` using `ih a ha (fun b hb => by`. Use `h (ϖ * b) (by simp [hfix, hb])` as an intermediate fact.

Rewrite `this` using `[show a * (ϖ * b) = ϖ * (a * b) by ring, hψ.compat]`. Conclude with `this)`. Take `⟨c, rfl⟩` from `mem_lev_iff.1 ha'`. Establish `hregk : IsSMulRegular R (ϖ ^ k)` using `hreg.pow k`. Establish `hc : σ c = c`.

Apply `hregk` to reduce the goal to its premises. Simplify `ha` using `[map_mul, map_pow, hfix]`. Establish `hc1 : c ∈ lev ϖ 1` using `hψ.prim c hc (fun b hb => by`. Establish `h1` using `h b hb`. Establish `h2` using `psi_pow hψ 1 k (c * b)`.

Rewrite `h2` using `[Nat.add_comm 1 k, ← mul_assoc]`. Rewrite using `[← h2]`. Conclude with `h1)`. Take `⟨d, rfl⟩` from `mem_lev_iff.1 hc1`. Conclude with `mem_lev_iff.2 ⟨d, by ring⟩`.
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
Take `⟨u, hu, -⟩` from `hR.basis`. Establish `key : ∀ t, t * y + σ (t * y) ∈ lev ϖ k` using `fun t => by`. Use `fixed_nondeg hψ hR.fix_ϖ hR.reg k _ (by simp [hR.inv, add_comm]) (fun b hb => ?_)` and prove the remaining obligations. Use `h (b * t)` as an intermediate fact. Use `this using 3` and compare the differences between its conclusion and the goal.

Simplify using `only [map_mul, hb]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `key 1`. Establish `h2` using `key u`. Establish `h3 : (u - σ u) * y ∈ lev ϖ k`.

Establish `: (u - σ u) * y = (u * y + σ (u * y)) - σ u * (1 * y + σ (1 * y))`. Simplify using `only [map_mul, map_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Ideal.sub_mem _ h2 (Ideal.mul_mem_left _ _ h1)`.

Take `⟨v, hv⟩` from `hu.exists_left_inv`. Establish `: y = v * ((u - σ u) * y)` using `by rw [← mul_assoc, hv, one_mul]`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_left _ _ h3`.
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
