import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

namespace GlobalTheory.TorusWtFin

open Complex

noncomputable abbrev dg {n : ℕ} (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff]`. Rewrite using `[Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Simplify using `only [Pi.star_apply]`. Rewrite using `[Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]`. Simplify using `[Complex.conj_ofReal]`. Unfold `Formalism.REAL.Jm`. Rewrite using `[Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`.

Use `congr 1`. Use function extensionality and compare the values at `a`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma diag_mem (n : ℕ) (ε : Fin n → Bool) (θ : Fin n → ℝ) : dg θ ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext a
    simp only [Pi.star_apply]
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    simp [Complex.conj_ofReal]
  · unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring

/- English proof (translation)
Simplify using `[Pi.single_apply]`.
-/
lemma sum_single {n : ℕ} (μ : Fin n → ℝ) (a : Fin n) (c : ℝ) :
    (∑ b, μ b * (Pi.single a c : Fin n → ℝ) b) = μ a * c := by
  simp [Pi.single_apply]

/- English proof (translation)
Establish `h1` using `hw (Pi.single a (2 * Real.pi)) (diag_mem n ε _)`. Establish `h0` using `hw 0 (diag_mem n ε _)`. Express the relevant statement in the definitionally equal form `ρ (dg _) v = _ at h1 h0`. Establish `hD : dg (Pi.single a (2 * Real.pi) : Fin n → ℝ) = dg (0 : Fin n → ℝ)`. Unfold `dg`.

Use `congr 1`. Use function extensionality and compare the values at `b`. Distinguish the cases in `hb : b = a`. Substitute `hb` using the available equality. Simplify using `only [Pi.single_eq_same, Pi.zero_apply, Complex.ofReal_zero, zero_mul, Complex.exp_zero]`.

Use `push_cast`. Conclude with `Complex.exp_two_pi_mul_I`. Simplify using `[Pi.single_apply, hb]`. Rewrite `h1` using `[sum_single]`. Rewrite `h1` using `[hD, h0]`.

Simplify using `only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul] at h1`. Establish `h2 : (Complex.exp (((μ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) - 1) • v = 0`. Rewrite using `[sub_smul, one_smul, ← h1, sub_self]`. Establish `h3 : Complex.exp (((μ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = 1`. Break down `smul_eq_zero.1 h2 with h | h` into its components or cases.

Conclude with `sub_eq_zero.1 h`. Conclude with `absurd h hv`. Take `⟨k, hk⟩` from `Complex.exp_eq_one_iff.1 h3`. Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`.

Establish `h4 : ((μ a : ℝ) : ℂ) = (k : ℂ)`. Use `hk` as an intermediate fact. Move the coercions through the operations in `at this`. Establish `hI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0` using `by simp [hpi, Complex.I_ne_zero]`. Apply `mul_right_cancel₀ hI` to reduce the goal to its premises.

Take the linear combination `this`. Conclude with `h4` after adjusting the coercions.
-/
lemma wt_int {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) {μ : Fin n → ℝ} {v : H} (hv : v ≠ 0)
    (hw : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ μ v) (a : Fin n) : ∃ k : ℤ, μ a = k := by
  have h1 := hw (Pi.single a (2 * Real.pi)) (diag_mem n ε _)
  have h0 := hw 0 (diag_mem n ε _)
  change ρ (dg _) v = _ at h1 h0
  have hD : dg (Pi.single a (2 * Real.pi) : Fin n → ℝ) = dg (0 : Fin n → ℝ) := by
    unfold dg
    congr 1
    funext b
    by_cases hb : b = a
    · subst hb
      simp only [Pi.single_eq_same, Pi.zero_apply, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
      push_cast
      exact Complex.exp_two_pi_mul_I
    · simp [Pi.single_apply, hb]
  rw [sum_single] at h1
  rw [hD, h0] at h1
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_smul] at h1
  have h2 : (Complex.exp (((μ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) - 1) • v = 0 := by
    rw [sub_smul, one_smul, ← h1, sub_self]
  have h3 : Complex.exp (((μ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = 1 := by
    rcases smul_eq_zero.1 h2 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hv
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 h3
  refine ⟨k, ?_⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h4 : ((μ a : ℝ) : ℂ) = (k : ℂ) := by
    have := hk
    push_cast at this
    have hI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [hpi, Complex.I_ne_zero]
    apply mul_right_cancel₀ hI
    linear_combination this
  exact_mod_cast h4

/- English proof (translation)
Introduce and unpack `x ⟨k, rfl⟩ y ⟨k', rfl⟩ h`. Simplify using `only at h`. Establish `h1 : Complex.exp ((((k - k' : ℤ) : ℝ) : ℂ) * Complex.I) = 1`. Establish `h' : Complex.exp ((k : ℂ) * Complex.I) = Complex.exp ((k' : ℂ) * Complex.I)`. Conclude with `h` after adjusting the coercions.

Use `push_cast`. Rewrite using `[sub_mul, Complex.exp_sub, h', div_self (Complex.exp_ne_zero _)]`. Take `⟨m, hm⟩` from `Complex.exp_eq_one_iff.1 h1`. Establish `hm' : (((k - k' : ℤ) : ℝ) : ℂ) = ((2 * m * Real.pi : ℝ) : ℂ)`. Use `push_cast`.

Apply `mul_right_cancel₀ Complex.I_ne_zero` to reduce the goal to its premises. Move the coercions through the operations in `at hm`. Take the linear combination `hm`. Establish `hm'' : ((k - k' : ℤ) : ℝ) = ((2 * m : ℤ) : ℝ) * Real.pi`. Use `Complex.ofReal_injective hm'` as an intermediate fact.

Move the coercions through the operations in `at this ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `h0 : (2 * m : ℤ) = 0`. Rewrite `hm''` using `[h0]`. Simplify using `only [Int.cast_zero, zero_mul] at hm''`.

Establish `: (k - k' : ℤ) = 0` using `by exact_mod_cast hm''`. Establish `: k = k'` using `by omega`. Rewrite using `[this]`. Conclude with `absurd hm''.symm ((irrational_pi.intCast_mul h0).ne_int _)`.
-/
lemma exp_injOn : Set.InjOn (fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I)) {x | ∃ k : ℤ, x = k} := by
  rintro x ⟨k, rfl⟩ y ⟨k', rfl⟩ h
  simp only at h
  have h1 : Complex.exp ((((k - k' : ℤ) : ℝ) : ℂ) * Complex.I) = 1 := by
    have h' : Complex.exp ((k : ℂ) * Complex.I) = Complex.exp ((k' : ℂ) * Complex.I) := by
      exact_mod_cast h
    push_cast
    rw [sub_mul, Complex.exp_sub, h', div_self (Complex.exp_ne_zero _)]
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 h1
  have hm' : (((k - k' : ℤ) : ℝ) : ℂ) = ((2 * m * Real.pi : ℝ) : ℂ) := by
    push_cast
    apply mul_right_cancel₀ Complex.I_ne_zero
    push_cast at hm
    linear_combination hm
  have hm'' : ((k - k' : ℤ) : ℝ) = ((2 * m : ℤ) : ℝ) * Real.pi := by
    have := Complex.ofReal_injective hm'
    push_cast at this ⊢
    linarith
  by_cases h0 : (2 * m : ℤ) = 0
  · rw [h0] at hm''
    simp only [Int.cast_zero, zero_mul] at hm''
    have : (k - k' : ℤ) = 0 := by exact_mod_cast hm''
    have : k = k' := by omega
    rw [this]
  · exact absurd hm''.symm ((irrational_pi.intCast_mul h0).ne_int _)

/- English proof (translation)
Introduce `n ε H _ _ ρ S hS`. Set `W : Set (Fin n → ℝ)` to `{μ | ∃ v ∈ S, v ≠ 0 ∧ Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ μ v}`. It suffices to establish `hW : W.Finite by`. Conclude with `⟨hW.toFinset, fun μ v hv h0 hw => hW.mem_toFinset.2 ⟨v, hv, h0, hw⟩⟩`. Set `T : Fin n → Module.End ℂ H` to `fun a => (ρ (dg (Pi.single a (1 : ℝ)))).toLinearMap`.

Set `C : Fin n → Set ℂ` to `fun a => {c | ∃ v ∈ S, v ≠ 0 ∧ T a v = c • v}`. Establish `hC : ∀ a, (C a).Finite`. Introduce `a`. Establish `hx : ∀ c : C a, ∃ v : S, (v : H) ≠ 0 ∧ T a v = (c : ℂ) • (v : H)` using `fun c => by`. Take `⟨v, hvS, hv0, hv⟩` from `c.2`.

Conclude with `⟨⟨v, hvS⟩, hv0, hv⟩`. Use `choose xs hxs using hx`. Establish `hli : LinearIndependent ℂ (fun c : C a => ((xs c : S) : H))` using `(T a).eigenvectors_linearIndependent (C a) (fun c => (xs c : H)) (fun c => ⟨Module.End.mem_eigenspace_iff.2 (hxs c).2, (hxs c).1⟩)`. Establish `hli' : LinearIndependent ℂ xs` using `LinearIndependent.of_comp S.subtype hli`. Use `hli'.finite` as an intermediate fact.

Conclude with `Set.finite_coe_iff.1 this`. Set `Z : Fin n → Set ℝ` to `fun a => {x | (∃ k : ℤ, x = k) ∧ Complex.exp ((x : ℂ) * Complex.I) ∈ C a}`. Establish `hZ : ∀ a, (Z a).Finite`. Introduce `a`. Use `Set.Finite.of_finite_image ((hC a).subset ?_) (exp_injOn.mono fun x hx => hx.1)` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `hx.2`. Use `(Set.Finite.pi hZ).subset ?_` and prove the remaining obligations. Introduce and unpack `μ ⟨v, hvS, hv0, hw⟩ a _`. Use `⟨wt_int ε ρ hv0 hw a, v, hvS, hv0, ?_⟩` and prove the remaining obligations.

Establish `h` using `hw (Pi.single a (1 : ℝ)) (diag_mem n ε _)`. Rewrite `h` using `[sum_single, mul_one]`. Conclude with `h`.
-/
theorem finite_weights : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H), FiniteDimensional ℂ S → ∃ F : Finset (Fin n → ℝ), ∀ (μ : Fin n → ℝ) (v : H), v ∈ S → v ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ μ v → μ ∈ F := by
  intro n ε H _ _ ρ S hS
  let W : Set (Fin n → ℝ) := {μ | ∃ v ∈ S, v ≠ 0 ∧ Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ μ v}
  suffices hW : W.Finite by
    exact ⟨hW.toFinset, fun μ v hv h0 hw => hW.mem_toFinset.2 ⟨v, hv, h0, hw⟩⟩

  let T : Fin n → Module.End ℂ H := fun a => (ρ (dg (Pi.single a (1 : ℝ)))).toLinearMap
  let C : Fin n → Set ℂ := fun a => {c | ∃ v ∈ S, v ≠ 0 ∧ T a v = c • v}
  have hC : ∀ a, (C a).Finite := by
    intro a
    have hx : ∀ c : C a, ∃ v : S, (v : H) ≠ 0 ∧ T a v = (c : ℂ) • (v : H) := fun c => by
      obtain ⟨v, hvS, hv0, hv⟩ := c.2
      exact ⟨⟨v, hvS⟩, hv0, hv⟩
    choose xs hxs using hx
    have hli : LinearIndependent ℂ (fun c : C a => ((xs c : S) : H)) :=
      (T a).eigenvectors_linearIndependent (C a) (fun c => (xs c : H))
        (fun c => ⟨Module.End.mem_eigenspace_iff.2 (hxs c).2, (hxs c).1⟩)
    have hli' : LinearIndependent ℂ xs := LinearIndependent.of_comp S.subtype hli
    have := hli'.finite
    exact Set.finite_coe_iff.1 this
  let Z : Fin n → Set ℝ := fun a => {x | (∃ k : ℤ, x = k) ∧ Complex.exp ((x : ℂ) * Complex.I) ∈ C a}
  have hZ : ∀ a, (Z a).Finite := by
    intro a
    refine Set.Finite.of_finite_image ((hC a).subset ?_) (exp_injOn.mono fun x hx => hx.1)
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  refine (Set.Finite.pi hZ).subset ?_
  rintro μ ⟨v, hvS, hv0, hw⟩ a _
  refine ⟨wt_int ε ρ hv0 hw a, v, hvS, hv0, ?_⟩
  have h := hw (Pi.single a (1 : ℝ)) (diag_mem n ε _)
  rw [sum_single, mul_one] at h
  exact h

end GlobalTheory.TorusWtFin
