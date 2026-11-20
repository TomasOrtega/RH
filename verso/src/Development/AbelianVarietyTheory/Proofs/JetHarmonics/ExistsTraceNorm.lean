import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ParabolicPointMembership
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterTrivialNearOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.ParabolicPointMembership GlobalTheory.QuadSubfield

namespace GlobalTheory.PlaceComponents

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem emb_mem (σ : D.host.E →+* ℂ) (x : D.host.E) : σ x ∈ Qbar :=
  mem_algebraicClosure_iff.2 ((Algebra.IsIntegral.isIntegral (R := ℚ) x).map σ.toRatAlgHom).isAlgebraic

def lamE (σ : D.host.E →+* ℂ) : D.host.E →+* ℂ_[p] := lam.comp (σ.codRestrict Qbar (emb_mem D σ))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lamC_emb (σ : D.host.E →+* ℂ) (x : D.host.E) : lamC lam (σ x) = lamE D lam σ x := dif_pos (emb_mem D σ x)

def homP : D.host.K →+* ℂ_[p] := (lamE D lam D.host.φ₀).comp (algebraMap D.host.K D.host.E)

def homPbar : D.host.K →+* ℂ_[p] := (homP D lam).comp (conjK D)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem atP₂ (c : D.host.K) : atP D lam c = homP D lam c := lamC_emb D lam _ _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem atPbar_eq (c : D.host.K) : atPbar D lam c = homPbar D lam c := lamC_emb D lam _ _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem conjK_conjK (c : D.host.K) : conjK D (conjK D c) = c := Subtype.ext (conj_conj D _)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem homP_conjK (c : D.host.K) : homP D lam (conjK D c) = homPbar D lam c := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem homPbar_conjK (c : D.host.K) : homPbar D lam (conjK D c) = homP D lam c := by
  show homP D lam (conjK D (conjK D c)) = _
  rw [conjK_conjK]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Use the resulting assumption.

Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Chain the equalities or inequalities of the calculation.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. A detailed English derivation is pending.
-/
theorem norm_int_le (ψ : D.host.K →+* ℂ_[p]) (a : 𝓞 D.host.K) : ‖ψ (a : D.host.K)‖ ≤ 1 := by
  obtain ⟨f, hf, h0'⟩ := RingOfIntegers.isIntegral_coe a
  have h0 : f.eval₂ (Int.castRingHom ℂ_[p]) (ψ (a : D.host.K)) = 0 := by
    have := congrArg ψ h0'
    rw [Polynomial.hom_eval₂, map_zero] at this
    rwa [Subsingleton.elim (Int.castRingHom ℂ_[p]) (ψ.comp (algebraMap ℤ D.host.K))]
  by_contra hlt
  rw [not_le] at hlt
  set x := ψ (a : D.host.K)
  rw [hf.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum, add_eq_zero_iff_eq_neg] at h0
  have h1 : ‖x ^ f.natDegree‖ ≤ ‖x‖ ^ f.natDegree / ‖x‖ := by
    rw [h0, norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, norm_mul, norm_pow, le_div_iff₀ (by linarith)]
    have h2 : ‖(Int.castRingHom ℂ_[p]) (f.coeff i)‖ ≤ 1 := by
      simpa using IsUltrametricDist.norm_intCast_le_one ℂ_[p] (f.coeff i)
    calc _ ≤ 1 * ‖x‖ ^ i * ‖x‖ := by gcongr
      _ = ‖x‖ ^ (i + 1) := by ring
      _ ≤ _ := pow_le_pow_right₀ hlt.le (Finset.mem_range.1 hi)
  rw [norm_pow, le_div_iff₀ (by linarith)] at h1
  have : 0 < ‖x‖ ^ f.natDegree := by positivity
  nlinarith

def conjO (a : 𝓞 D.host.K) : 𝓞 D.host.K :=
  ⟨conjK D (a : D.host.K), (RingOfIntegers.isIntegral_coe a).map (conjK D).toIntAlgHom⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_conjO (a : 𝓞 D.host.K) : ((conjO D a : 𝓞 D.host.K) : D.host.K) = conjK D (a : D.host.K) := rfl

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem exists_trace_norm (c : D.host.K) :
    ∃ t n : ℚ, c + conjK D c = (t : D.host.K) ∧ c * conjK D c = (n : D.host.K) := by
  obtain ⟨-, σ, θ, hσ, hθ, hσθ, hx, -⟩ := quadratic_subfield D
  have e : conjK D c = σ c := Subtype.ext (hσ c).symm
  obtain ⟨a, b, rfl⟩ := hx c
  rw [e]
  refine ⟨2 * a, a ^ 2 + D.host.d * b ^ 2, ?_, ?_⟩
  · simp [hσθ]; ring
  · simp [hσθ]; linear_combination (-(b : D.host.K) ^ 2) * hθ

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem isIdem_iff (m : ℕ) (ε : 𝓞 D.host.K) : IsIdem D lam m ε ↔
    ‖homP D lam (ε : D.host.K) - 1‖ ≤ (p : ℝ) ^ (-(m : ℤ)) ∧ ‖homPbar D lam (ε : D.host.K)‖ ≤ (p : ℝ) ^ (-(m : ℤ)) := by
  rw [← atP₂, ← atPbar_eq]; rfl

variable (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ}

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem vecOf_add (A A' : Matrix (Fin N') (Fin N) D.host.E) :
    vecOf D cc δ (A + A') = vecOf D cc δ A + vecOf D cc δ A' := by
  funext τ i j
  simp [vecOf, embV, tor0, mul_add]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vecOf_smul (c : D.host.K) (A : Matrix (Fin N') (Fin N) D.host.E) :
    vecOf D cc δ ((c : D.host.E) • A) = D.host.φ₀ (c : D.host.E) • vecOf D cc δ A := by
  funext τ i j
  have h := GlobalTheory.InducedType.restrict_K D
  simp only [vecOf, embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  rw [h τ c]
  ring

/- English proof (translation)
Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition.

Express the relevant assertion in an equivalent form by its definition. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Treat this case separately. Treat this case separately.

Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem int_smul_mem_La (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (a : 𝓞 D.host.K) {x : VC D N N'} (hx : x ∈ La D (tor0 D cc δ) L L') :
    D.host.φ₀ ((a : D.host.K) : D.host.E) • x ∈ La D (tor0 D cc δ) L L' := by
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨D.host.φ₀ ((a : D.host.K) : D.host.E) * w, ?_, A, hA, by rw [smul_smul]⟩
    change w ∈ lamOf D cc δ at hw
    change _ ∈ lamOf D cc δ
    induction hw using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨c, hc, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨a * c, cc.mul_mem_left a hc, ?_⟩
      push_cast
      rw [map_mul]; ring
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | neg x _ hx => rw [mul_neg]; exact neg_mem hx
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

end GlobalTheory.PlaceComponents
