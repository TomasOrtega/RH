import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts

open Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.GradFlag

open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.N.S

variable {n : ℕ} {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ}

def pM (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (A * A - A)

def qM (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (A * A + A)

/- English proof (translation)
Take `⟨hg, hH, -, -⟩` from `h`. Establish `h0 : Aᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * A = 0` using `hg`. Rewrite `h0` using `[hH]`. Conclude with `eq_neg_of_add_eq_zero_right h0`.
-/
theorem J_mul (h : IsGrad ε A) : Formalism.REAL.Jm ε * A = -(A * Formalism.REAL.Jm ε) := by
  obtain ⟨hg, hH, -, -⟩ := h
  have h0 : Aᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * A = 0 := hg
  rw [hH] at h0
  exact eq_neg_of_add_eq_zero_right h0

/- English proof (translation)
Rewrite using `[h]`.
-/
theorem A4 (h : A * A * A = A) : A * A * A * A = A * A := by rw [h]

/- English proof (translation)
Establish `h4` using `A4 h`. Unfold `pM`. Simplify using `only [smul_mul_assoc, mul_smul_comm, smul_smul, sub_mul, mul_sub, ← mul_assoc, h4, h]`. Use `module`.
-/
theorem pM_idem (h : A * A * A = A) : pM A * pM A = pM A := by
  have h4 := A4 h
  unfold pM
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, sub_mul, mul_sub, ← mul_assoc, h4, h]
  module

/- English proof (translation)
Establish `h4` using `A4 h`. Unfold `pM qM`. Simplify using `only [smul_mul_assoc, mul_smul_comm, smul_smul, sub_mul, mul_add, add_mul, mul_sub, ← mul_assoc, h4, h]`. Use `module`.
-/
theorem pM_mul_qM (h : A * A * A = A) : pM A * qM A = 0 := by
  have h4 := A4 h
  unfold pM qM
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, sub_mul, mul_add, add_mul, mul_sub, ← mul_assoc, h4, h]
  module

/- English proof (translation)
Establish `hJ` using `J_mul h`. Establish `h2 : Formalism.REAL.Jm ε * (A * A) = A * A * Formalism.REAL.Jm ε`. Rewrite using `[← mul_assoc, hJ, neg_mul, mul_assoc, hJ, mul_neg, neg_neg, mul_assoc]`. Unfold `pM qM`. Rewrite using `[mul_smul_comm, smul_mul_assoc, mul_sub, add_mul, h2, hJ, sub_neg_eq_add]`.
-/
theorem J_mul_pM (h : IsGrad ε A) : Formalism.REAL.Jm ε * pM A = qM A * Formalism.REAL.Jm ε := by
  have hJ := J_mul h
  have h2 : Formalism.REAL.Jm ε * (A * A) = A * A * Formalism.REAL.Jm ε := by
    rw [← mul_assoc, hJ, neg_mul, mul_assoc, hJ, mul_neg, neg_neg, mul_assoc]
  unfold pM qM
  rw [mul_smul_comm, smul_mul_assoc, mul_sub, add_mul, h2, hJ, sub_neg_eq_add]

/- English proof (translation)
Establish `hJJ` using `Formalism.REAL.Jm_mul_self ε`. Establish `: qM A = Formalism.REAL.Jm ε * pM A * Formalism.REAL.Jm ε`. Rewrite using `[J_mul_pM h, mul_assoc, hJJ, mul_one]`. Rewrite using `[this, Matrix.trace_mul_comm, ← mul_assoc, hJJ, one_mul]`.
-/
theorem trace_qM (h : IsGrad ε A) : Matrix.trace (qM A) = Matrix.trace (pM A) := by
  have hJJ := Formalism.REAL.Jm_mul_self ε
  have : qM A = Formalism.REAL.Jm ε * pM A * Formalism.REAL.Jm ε := by
    rw [J_mul_pM h, mul_assoc, hJJ, mul_one]
  rw [this, Matrix.trace_mul_comm, ← mul_assoc, hJJ, one_mul]

/- English proof (translation)
Unfold `pM`. Simplify using `[conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, h]`.
-/
theorem pM_conjTranspose (h : Aᴴ = A) : (pM A)ᴴ = pM A := by
  unfold pM
  simp [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, h]

/- English proof (translation)
Use `⟨fun x => ⟨x, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨y, rfl⟩`. Express the relevant statement in the definitionally equal form `Matrix.toLin' (pM A) (Matrix.toLin' (pM A) y) = Matrix.toLin' (pM A) y`. Rewrite using `[← LinearMap.comp_apply, ← Matrix.toLin'_mul, pM_idem h]`.
-/
theorem isProj (h : A * A * A = A) : LinearMap.IsProj (Vm A) (Matrix.toLin' (pM A)) := by
  refine ⟨fun x => ⟨x, rfl⟩, ?_⟩
  rintro _ ⟨y, rfl⟩
  change Matrix.toLin' (pM A) (Matrix.toLin' (pM A) y) = Matrix.toLin' (pM A) y
  rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, pM_idem h]

/- English proof (translation)
Use `(isProj h).trace` as an intermediate fact. Rewrite `this` using `[Matrix.trace_toLin'_eq]`. Conclude with `this`.
-/
theorem trace_pM (h : A * A * A = A) : Matrix.trace (pM A) = (rk A : ℂ) := by
  have := (isProj h).trace
  rw [Matrix.trace_toLin'_eq] at this
  exact this

/- English proof (translation)
Take `⟨-, -, h3, hA⟩` from `id h`. Assume the negation of the conclusion as `hc`. Establish `h0 : rk A = 0` using `by omega`. Establish `hb : Vm A = ⊥` using `Submodule.finrank_eq_zero.mp h0`. Establish `hP : pM A = 0`.

Establish `: Matrix.toLin' (pM A) = 0` using `LinearMap.range_eq_bot.mp hb`. Simplify using `using this`. Establish `hQ : qM A = 0`. Establish `hJJ` using `Formalism.REAL.Jm_mul_self ε`. Establish `: qM A = Formalism.REAL.Jm ε * pM A * Formalism.REAL.Jm ε`.

Rewrite using `[J_mul_pM h, mul_assoc, hJJ, mul_one]`. Rewrite using `[this, hP]`. Simplify using the standard rewrite rules. Apply `hA` to reduce the goal to its premises. Establish `: A = qM A - pM A` using `by unfold pM qM; module`.

Rewrite using `[this, hP, hQ, sub_zero]`.
-/
theorem one_le_rk (h : IsGrad ε A) : 1 ≤ rk A := by
  obtain ⟨-, -, h3, hA⟩ := id h
  by_contra hc
  have h0 : rk A = 0 := by omega
  have hb : Vm A = ⊥ := Submodule.finrank_eq_zero.mp h0
  have hP : pM A = 0 := by
    have : Matrix.toLin' (pM A) = 0 := LinearMap.range_eq_bot.mp hb
    simpa using this
  have hQ : qM A = 0 := by
    have hJJ := Formalism.REAL.Jm_mul_self ε
    have : qM A = Formalism.REAL.Jm ε * pM A * Formalism.REAL.Jm ε := by
      rw [J_mul_pM h, mul_assoc, hJJ, mul_one]
    rw [this, hP]; simp
  apply hA
  have : A = qM A - pM A := by unfold pM qM; module
  rw [this, hP, hQ, sub_zero]

/- English proof (translation)
Take `⟨-, hH, h3, -⟩` from `id h`. Take `⟨u, rfl⟩` from `hx`. Take `⟨v, rfl⟩` from `hy`. Express the relevant statement in the definitionally equal form `star (pM A *ᵥ u) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (pM A *ᵥ v)) = 0`. Establish `hz : pM A * (Formalism.REAL.Jm ε * pM A) = 0`.

Rewrite using `[J_mul_pM h, ← mul_assoc, pM_mul_qM h3, zero_mul]`. Rewrite using `[star_mulVec, pM_conjTranspose hH, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, hz]`. Simplify using the standard rewrite rules.
-/
theorem isotropic (h : IsGrad ε A) {x y : Fin n → ℂ} (hx : x ∈ Vm A) (hy : y ∈ Vm A) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0 := by
  obtain ⟨-, hH, h3, -⟩ := id h
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  change star (pM A *ᵥ u) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (pM A *ᵥ v)) = 0
  have hz : pM A * (Formalism.REAL.Jm ε * pM A) = 0 := by
    rw [J_mul_pM h, ← mul_assoc, pM_mul_qM h3, zero_mul]
  rw [star_mulVec, pM_conjTranspose hH, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, hz]
  simp

/- English proof (translation)
Introduce `n ε A h`. Take `⟨-, -, h3, -⟩` from `id h`. Use `⟨one_le_rk h, ⟨rfl, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `intro i j hij fin_cases i <;> fin_cases j <;> simp_all [W]`. Introduce `i`.

Establish `hi : i = 0` using `Subsingleton.elim _ _`. Substitute `hi` using the available equality. Establish `h0 : W A 0 = ⊥` using `rfl`. Establish `h1 : W A 1 = Vm A` using `rfl`. Express the relevant statement in the definitionally equal form `Module.finrank ℂ (W A 1) = Module.finrank ℂ (W A 0) + rk A`.

Rewrite using `[h0, h1, finrank_bot, zero_add]`. Both sides reduce to the same expression. Introduce `x hx y hy`. Conclude with `isotropic h hx hy`. Establish `hj : (Matrix.trace ((1 / 2 : ℂ) • (A * A + A))).re = (rk A : ℝ)`.

Express the relevant statement in the definitionally equal form `(Matrix.trace (qM A)).re = _`. Rewrite using `[trace_qM h, trace_pM h3]`. Simplify using the standard rewrite rules. Unfold `rhoA`. Simplify using `only [hj]`.
-/
theorem flagFacts : FlagFacts := by
  intro n ε A h
  obtain ⟨-, -, h3, -⟩ := id h
  refine ⟨one_le_rk h, ⟨rfl, ?_, ?_, ?_⟩, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [W]
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    have h0 : W A 0 = ⊥ := rfl
    have h1 : W A 1 = Vm A := rfl
    change Module.finrank ℂ (W A 1) = Module.finrank ℂ (W A 0) + rk A
    rw [h0, h1, finrank_bot, zero_add]
    rfl
  · intro x hx y hy
    exact isotropic h hx hy
  · have hj : (Matrix.trace ((1 / 2 : ℂ) • (A * A + A))).re = (rk A : ℝ) := by
      change (Matrix.trace (qM A)).re = _
      rw [trace_qM h, trace_pM h3]
      simp
    unfold rhoA
    simp only [hj]

end GlobalTheory.CompanionTheory.GradFlag
