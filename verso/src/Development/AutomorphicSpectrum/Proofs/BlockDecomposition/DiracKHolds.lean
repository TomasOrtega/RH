import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairStructureOnLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumMemOfStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CliffordHighestWeightVectorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParthasarathyRaoVaradarajanStatement

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCount.InjHw

namespace GlobalTheory.CompanionTheory.RealMult.DiracProof

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)} {Kf : Fin n → Fin n → Module.End ℂ V}

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use `show NormedSpace.exp (((s + t : ℝ) : ℂ) • X) = NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X)`. Rewrite using `[Complex.ofReal_add, add_smul, Matrix.exp_add_of_commute]`. Conclude with `((Commute.refl X).smul_left _).smul_right _`.
-/
theorem expU_add' (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s t : ℝ) :
    expU X hX (s + t) = expU X hX s * expU X hX t := by
  apply Subtype.ext
  show NormedSpace.exp (((s + t : ℝ) : ℂ) • X) = NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X)
  rw [Complex.ofReal_add, add_smul, Matrix.exp_add_of_commute]
  exact ((Commute.refl X).smul_left _).smul_right _

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use `show NormedSpace.exp (((2 * Real.pi : ℝ) : ℂ) • (Matrix.single a a Complex.I : Matrix (Fin n) (Fin n) ℂ)) = 1`. Establish `e : (((2 * Real.pi : ℝ) : ℂ)) • (Matrix.single a a Complex.I : Matrix (Fin n) (Fin n) ℂ) = diagonal (fun c => if c = a then ((2 * Real.pi : ℝ) : ℂ) * Complex.I else 0)`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Distinguish the cases in `hc : i = a`. Substitute `hc` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.single_apply, hc, Ne.symm hc]`.

Rewrite using `[Matrix.diagonal_apply_ne _ hij, Matrix.smul_apply, Matrix.single_apply, if_neg (fun hh => hij (hh.1.symm.trans hh.2)), smul_zero]`. Rewrite using `[e, Matrix.exp_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `c`. Apply the tactic sequence `have hh : NormedSpace.exp (fun c => if c = a then ((2 * Real.pi : ℝ) : ℂ) * Complex.I else 0) c = if c = a then Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) else 1 := by split_ifs with hc <;> simp [hc, Complex.exp_eq_exp_ℂ]`.

Rewrite using `[hh]`. Establish `h2 : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1`. Use `push_cast`. Conclude with `Complex.exp_two_pi_mul_I`. Rewrite using `[h2]`.

Simplify using the standard rewrite rules.
-/
theorem expU_two_pi (a : Fin n) (hX : (Matrix.single a a Complex.I)ᴴ = -(Matrix.single a a Complex.I)) :
    expU (Matrix.single a a Complex.I) hX (2 * Real.pi) = 1 := by
  apply Subtype.ext
  show NormedSpace.exp (((2 * Real.pi : ℝ) : ℂ) • (Matrix.single a a Complex.I : Matrix (Fin n) (Fin n) ℂ)) = 1
  have e : (((2 * Real.pi : ℝ) : ℂ)) • (Matrix.single a a Complex.I : Matrix (Fin n) (Fin n) ℂ) =
      diagonal (fun c => if c = a then ((2 * Real.pi : ℝ) : ℂ) * Complex.I else 0) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hc : i = a
      · subst hc
        simp
      · simp [Matrix.single_apply, hc, Ne.symm hc]
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.smul_apply, Matrix.single_apply,
        if_neg (fun hh => hij (hh.1.symm.trans hh.2)), smul_zero]
  rw [e, Matrix.exp_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext c
  have hh : NormedSpace.exp (fun c => if c = a then ((2 * Real.pi : ℝ) : ℂ) * Complex.I else 0) c =
      if c = a then Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) else 1 := by
    split_ifs with hc <;> simp [hc, Complex.exp_eq_exp_ℂ]
  rw [hh]
  have h2 : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
    push_cast
    exact Complex.exp_two_pi_mul_I
  rw [h2]
  simp

/- English proof (translation)
Establish `hX : (Matrix.single a a Complex.I)ᴴ = -(Matrix.single a a Complex.I)`. Rewrite using `[single_conjT, Complex.star_def, Complex.conj_I, single_negI]`. Use `set X : Matrix (Fin n) (Fin n) ℂ := Matrix.single a a Complex.I with hXdef`. Use `set φ : ℝ → V := fun s => σ (expU X hX s) v with hφ`. Establish `hd0 : HasDerivAt φ ((Complex.I * r) • v) 0`.

Use `deriv_expU (Kf := Kf) h X hX v` as an intermediate fact. Establish `e` using `sum_single (Kf := Kf) v a a Complex.I`. Rewrite `e` using `[← hXdef]`. Rewrite `this` using `[e, hr, smul_smul]`. Conclude with `this`.

Establish `hstep : ∀ s, HasDerivAt φ ((Complex.I * r) • φ s) s`. Introduce `s`. Set `L : V →L[ℝ] V` to `((LinearMap.isometryOfInner (σ (expU X hX s)) (h.1 _)).toContinuousLinearMap).restrictScalars ℝ`. Establish `hL : ∀ y, L y = σ (expU X hX s) y` using `fun _ => rfl`. Establish `h1 : HasDerivAt (fun t => L (φ t)) (L ((Complex.I * r) • v)) 0` using `L.hasFDerivAt.comp_hasDerivAt 0 hd0`.

Establish `h2 : HasDerivAt (fun t => L (φ t)) (L ((Complex.I * r) • v)) (s - s)`. Rewrite using `[sub_self]` and apply the resulting hypothesis. Establish `h3` using `h2.comp_sub_const s s`. Establish `e : (fun t => L (φ (t - s))) = φ`. Use function extensionality and compare the values at `t`.

Establish `: expU X hX t = expU X hX s * expU X hX (t - s)`. Rewrite using `[← expU_add']`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hL, hφ, this, map_mul, Module.End.mul_apply]`.

Rewrite `h3` using `[e]`. Establish `e2 : L ((Complex.I * r) • v) = (Complex.I * r) • φ s`. Rewrite using `[hL, map_smul]`. Rewrite `h3` using `[e2]`. Then use the resulting hypothesis. Use `set ψ : ℝ → V := fun s => Complex.exp ((s : ℂ) * (-(Complex.I * r))) • φ s with hψ`.

Establish `hψd : ∀ s, HasDerivAt ψ 0 s`. Introduce `s`. Establish `h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * (-(Complex.I * r))) (-(Complex.I * r)) s`. Simplify using `using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const (-(Complex.I * (r : ℂ)))`. Establish `h2` using `h1.cexp`.

Establish `h3` using `h2.smul (hstep s)`. Establish `: Complex.exp ((s : ℂ) * (-(Complex.I * r))) • (Complex.I * r) • φ s + (Complex.exp ((s : ℂ) * (-(Complex.I * r))) * -(Complex.I * r)) • φ s = 0`. Rewrite using `[smul_smul, ← add_smul]`. Simplify using the standard rewrite rules. Rewrite `h3` using `[this]`.

Conclude with `h3`. Establish `hconst : ψ (2 * Real.pi) = ψ 0` using `is_const_of_deriv_eq_zero (fun s => (hψd s).differentiableAt) (fun s => (hψd s).deriv) _ _`. Establish `h0 : φ 0 = v`. Establish `: expU X hX 0 = 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1`. Simplify using the standard rewrite rules. Simplify using `[hφ, this]`. Establish `h2π : φ (2 * Real.pi) = v` using `by show σ (expU X hX (2 * Real.pi)) v = v`. Rewrite using `[show expU X hX (2 * Real.pi) = 1 from expU_two_pi a hX, map_one, Module.End.one_apply]`.

Establish `hE : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) • v = v`. Establish `b : ψ 0 = v` using `by simp [hψ, h0]`. Establish `a' : ψ (2 * Real.pi) = Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) • v` using `by show Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) • φ (2 * Real.pi) = _`. Rewrite using `[h2π]`. Rewrite using `[← a', hconst, b]`.

Establish `hE1 : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) = 1`. Establish `: (Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) - 1) • v = 0`. Rewrite using `[sub_smul, hE, one_smul, sub_self]`. Break down `smul_eq_zero.1 this with h' | h'` into its components or cases. Conclude with `sub_eq_zero.1 h'`.

Conclude with `absurd h' hv`. Take `⟨m, hm⟩` from `Complex.exp_eq_one_iff.1 hE1`. Use `⟨-m, ?_⟩` and prove the remaining obligations. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Establish `h5 : (r : ℂ) = ((-m : ℤ) : ℂ)`.

Move the coercions through the operations in `at hm ⊢`. Establish `h6 : (2 * (Real.pi : ℂ) * Complex.I) * ((r : ℂ) + m) = 0`. Take the linear combination `-hm`. Establish `h7 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0`. Simplify using `[hpi, Complex.I_ne_zero]`.

Use `(mul_eq_zero.1 h6).resolve_left h7` as an intermediate fact. Take the linear combination `this`. Conclude with `h5` after adjusting the coercions.
-/
theorem weight_int (h : IsDerivK σ Kf) (a : Fin n) (r : ℝ) {v : V} (hv : v ≠ 0)
    (hr : Kf a a v = (r : ℂ) • v) : ∃ m : ℤ, r = m := by
  have hX : (Matrix.single a a Complex.I)ᴴ = -(Matrix.single a a Complex.I) := by
    rw [single_conjT, Complex.star_def, Complex.conj_I, single_negI]
  set X : Matrix (Fin n) (Fin n) ℂ := Matrix.single a a Complex.I with hXdef
  set φ : ℝ → V := fun s => σ (expU X hX s) v with hφ
  have hd0 : HasDerivAt φ ((Complex.I * r) • v) 0 := by
    have := deriv_expU (Kf := Kf) h X hX v
    have e := sum_single (Kf := Kf) v a a Complex.I
    rw [← hXdef] at e
    rw [e, hr, smul_smul] at this
    exact this
  have hstep : ∀ s, HasDerivAt φ ((Complex.I * r) • φ s) s := by
    intro s
    let L : V →L[ℝ] V :=
      ((LinearMap.isometryOfInner (σ (expU X hX s)) (h.1 _)).toContinuousLinearMap).restrictScalars ℝ
    have hL : ∀ y, L y = σ (expU X hX s) y := fun _ => rfl
    have h1 : HasDerivAt (fun t => L (φ t)) (L ((Complex.I * r) • v)) 0 :=
      L.hasFDerivAt.comp_hasDerivAt 0 hd0
    have h2 : HasDerivAt (fun t => L (φ t)) (L ((Complex.I * r) • v)) (s - s) := by
      rwa [sub_self]
    have h3 := h2.comp_sub_const s s
    have e : (fun t => L (φ (t - s))) = φ := by
      funext t
      have : expU X hX t = expU X hX s * expU X hX (t - s) := by
        rw [← expU_add']
        congr 1
        ring
      simp only [hL, hφ, this, map_mul, Module.End.mul_apply]
    rw [e] at h3
    have e2 : L ((Complex.I * r) • v) = (Complex.I * r) • φ s := by
      rw [hL, map_smul]
    rwa [e2] at h3
  set ψ : ℝ → V := fun s => Complex.exp ((s : ℂ) * (-(Complex.I * r))) • φ s with hψ
  have hψd : ∀ s, HasDerivAt ψ 0 s := by
    intro s
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * (-(Complex.I * r))) (-(Complex.I * r)) s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const (-(Complex.I * (r : ℂ)))
    have h2 := h1.cexp
    have h3 := h2.smul (hstep s)
    have : Complex.exp ((s : ℂ) * (-(Complex.I * r))) • (Complex.I * r) • φ s +
        (Complex.exp ((s : ℂ) * (-(Complex.I * r))) * -(Complex.I * r)) • φ s = 0 := by
      rw [smul_smul, ← add_smul]
      simp
    rw [this] at h3
    exact h3
  have hconst : ψ (2 * Real.pi) = ψ 0 :=
    is_const_of_deriv_eq_zero (fun s => (hψd s).differentiableAt) (fun s => (hψd s).deriv) _ _
  have h0 : φ 0 = v := by
    have : expU X hX 0 = 1 := by
      apply Subtype.ext
      show NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1
      simp
    simp [hφ, this]
  have h2π : φ (2 * Real.pi) = v := by
    show σ (expU X hX (2 * Real.pi)) v = v
    rw [show expU X hX (2 * Real.pi) = 1 from expU_two_pi a hX, map_one, Module.End.one_apply]
  have hE : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) • v = v := by
    have b : ψ 0 = v := by simp [hψ, h0]
    have a' : ψ (2 * Real.pi) = Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) • v := by
      show Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) • φ (2 * Real.pi) = _
      rw [h2π]
    rw [← a', hconst, b]
  have hE1 : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) = 1 := by
    have : (Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) - 1) • v = 0 := by
      rw [sub_smul, hE, one_smul, sub_self]
    rcases smul_eq_zero.1 this with h' | h'
    · exact sub_eq_zero.1 h'
    · exact absurd h' hv
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 hE1
  refine ⟨-m, ?_⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h5 : (r : ℂ) = ((-m : ℤ) : ℂ) := by
    push_cast at hm ⊢
    have h6 : (2 * (Real.pi : ℂ) * Complex.I) * ((r : ℂ) + m) = 0 := by
      linear_combination -hm
    have h7 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [hpi, Complex.I_ne_zero]
    have := (mul_eq_zero.1 h6).resolve_left h7
    linear_combination this
  exact_mod_cast h5

/- English proof (translation)
Introduce `a b c d`. Establish `h1` using `h.gl1 a b c d`. Establish `h2` using `h.gl2 a b c d`. Establish `e : kF E1 E2 a b * kF E1 E2 c d - kF E1 E2 c d * kF E1 E2 a b = (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b)`. Simplify using `only [kF, add_mul, mul_add]`.

Rewrite using `[h.comm a b c d, h.comm c d a b]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, h1, h2]`. Apply the tactic sequence `split_ifs <;> simp [kF] <;> abel`.
-/
theorem kF_gl {E1 E2 : Fin n → Fin n → Module.End ℂ V} (h : IsPair E1 E2) : Formalism.REAL.GlRel (kF E1 E2) := by
  intro a b c d
  have h1 := h.gl1 a b c d
  have h2 := h.gl2 a b c d
  have e : kF E1 E2 a b * kF E1 E2 c d - kF E1 E2 c d * kF E1 E2 a b =
      (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b) := by
    simp only [kF, add_mul, mul_add]
    rw [h.comm a b c d, h.comm c d a b]
    abel
  rw [e, h1, h2]
  split_ifs <;> simp [kF] <;> abel

end GlobalTheory.CompanionTheory.RealMult.DiracProof

namespace GlobalTheory.CompanionTheory.RealMult

end GlobalTheory.CompanionTheory.RealMult
