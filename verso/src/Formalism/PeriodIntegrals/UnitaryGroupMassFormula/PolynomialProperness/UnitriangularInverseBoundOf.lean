import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.NsqMulVecLe

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
open scoped ComplexConjugate

noncomputable section

namespace PI.PolynomialProperness.CA

/- English proof (translation)
Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[conjTranspose_apply, hu.1 j i hij, star_zero]`. Rewrite using `[conjTranspose_apply, hu.2 i, star_one]`.
-/
theorem ut_conjT {m : ℕ} {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ UTset m) : uᴴ ∈ LTset m := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [conjTranspose_apply, hu.1 j i hij, star_zero]
  · rw [conjTranspose_apply, hu.2 i, star_one]

/- English proof (translation)
Take `⟨w, d, hd, rfl⟩` from `h`. Use `⟨w.symm, fun a => star (d (w.symm a)), fun a => by simpa using hd (w.symm a), ?_⟩` and prove the remaining obligations. Use extensionality with `i a`. Simplify using `only [monoP, conjTranspose_apply, of_apply]`. Distinguish the cases in `h : a = w i`.

Establish `h' : i = w.symm a` using `by rw [h, Equiv.symm_apply_apply]`. Rewrite using `[if_pos h, if_pos h', h']`. Establish `h' : ¬ i = w.symm a`. Introduce `h'`. Apply `h` to reduce the goal to its premises.

Rewrite using `[h', Equiv.apply_symm_apply]`. Rewrite using `[if_neg h, if_neg h', star_zero]`.
-/
theorem isMonomial_conjT {m : ℕ} {P : Matrix (Fin m) (Fin m) ℂ} (h : IsMonomial P) : IsMonomial Pᴴ := by
  obtain ⟨w, d, hd, rfl⟩ := h
  refine ⟨w.symm, fun a => star (d (w.symm a)), fun a => by simpa using hd (w.symm a), ?_⟩
  ext i a
  simp only [monoP, conjTranspose_apply, of_apply]
  by_cases h : a = w i
  · have h' : i = w.symm a := by rw [h, Equiv.symm_apply_apply]
    rw [if_pos h, if_pos h', h']
  · have h' : ¬ i = w.symm a := by
      intro h'; apply h; rw [h', Equiv.apply_symm_apply]
    rw [if_neg h, if_neg h', star_zero]

/- English proof (translation)
Rewrite using `[← conjTranspose_nonsing_inv, GN.mx_conjTranspose]`.
-/
theorem mx_inv_conjT {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : mx (Mᴴ)⁻¹ = mx M⁻¹ := by
  rw [← conjTranspose_nonsing_inv, GN.mx_conjTranspose]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem finish_bound {M C0 X A G : ℝ} (e : ℕ) (hm : M ≤ C0 * X ^ e) (hX : 0 ≤ X) (hXY : X ≤ A * G) :
    M ≤ max C0 0 * A ^ e * G ^ e := by
  calc M ≤ C0 * X ^ e := hm
    _ ≤ max C0 0 * X ^ e := mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hX e)
    _ ≤ max C0 0 * (A * G) ^ e :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX hXY e) (le_max_right _ _)
    _ = max C0 0 * A ^ e * G ^ e := by rw [mul_pow]; ring

/- English proof (translation)
Rewrite using `[Nat.add_sub_cancel]`.
-/
theorem exp_eq (r : ℕ) : (r + 1 - 1) * (r + 1) = r * (r + 1) := by
  rw [Nat.add_sub_cancel]

end PI.PolynomialProperness.CA

namespace PI.PolynomialProperness

open CA in
/- English proof (translation)
Introduce `k r z z' γ hmono`. Take `⟨C1, h1⟩` from `h (r + 1) (Zhat k r z z' γ) hmono`. Take `⟨C2, h2⟩` from `h (r + 1) (Zhat k r z z' γ)ᴴ (isMonomial_conjT hmono)`. Take `⟨CZ, hCZ⟩` from `hZ k r z z'`. Use `set A : ℝ := 1 + max CZ 0 with hA`.

Use `set e : ℕ := r * (r + 1) with he`. Establish `hzg : ∀ g : B.Mat k r, 1 ≤ B.gN g → 1 + mx (Zhat k r z z' g) ≤ A * B.gN g`. Introduce `g hg`. Establish `h3` using `hCZ g`. Establish `h4 : CZ * B.gN g ≤ max CZ 0 * B.gN g` using `mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)`.

Rewrite using `[hA]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hX : ∀ g : B.Mat k r, 0 ≤ 1 + mx (Zhat k r z z' g)` using `fun g => by`. Use `GN.mx_nonneg (Zhat k r z z' g)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hApos : 0 ≤ A ^ e` using `pow_nonneg (by rw [hA]; have := le_max_right CZ 0; linarith) e`. Use `⟨max (max C1 0) (max C2 0) * A ^ e, ?_, ?_⟩` and prove the remaining obligations. Introduce `v hv hvl u' hu' g hg hZg`. Establish `hb` using `h1 vᴴ hvl u' hu'`. Rewrite `hb` using `[← hZg, exp_eq]`.

Establish `hmax : max C1 0 * A ^ e ≤ max (max C1 0) (max C2 0) * A ^ e` using `mul_le_mul_of_nonneg_right (le_max_left _ _) hApos`. Establish `hG : 0 ≤ B.gN g ^ e` using `pow_nonneg (by linarith) e`. Prove the components needed by the constructor for the conclusion. Rewrite using `[← mx_inv_conjT]`. Conclude with `(finish_bound e hb.2.2.1 (hX g) (hzg g hg)).trans (mul_le_mul_of_nonneg_right hmax hG)`.

Conclude with `(finish_bound e hb.2.2.2 (hX g) (hzg g hg)).trans (mul_le_mul_of_nonneg_right hmax hG)`. Introduce `u hu v' hv' hPv g hg hZg`. Establish `hl : v'ᴴ ∈ LPg (Zhat k r z z' γ)ᴴ`. Use `⟨ut_conjT hv', ?_⟩` and prove the remaining obligations. Establish `e1 : ((Zhat k r z z' γ)ᴴ)⁻¹ * v'ᴴ * (Zhat k r z z' γ)ᴴ = (Zhat k r z z' γ * v' * (Zhat k r z z' γ)⁻¹)ᴴ`.

Rewrite using `[conjTranspose_mul, conjTranspose_mul, conjTranspose_nonsing_inv, Matrix.mul_assoc]`. Rewrite using `[e1]`. Conclude with `ut_conjT hPv`. Establish `hb` using `h2 v'ᴴ hl u hu`. Establish `e2 : v'ᴴ * (Zhat k r z z' γ)ᴴ * u = (Zhat k r z z' g)ᴴ`.

Rewrite using `[hZg, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]`. Rewrite `hb` using `[e2, GN.mx_conjTranspose (Zhat k r z z' g), exp_eq]`. Establish `hmax : max C2 0 * A ^ e ≤ max (max C1 0) (max C2 0) * A ^ e` using `mul_le_mul_of_nonneg_right (le_max_right _ _) hApos`. Establish `hG : 0 ≤ B.gN g ^ e` using `pow_nonneg (by linarith) e`. Prove the components needed by the constructor for the conclusion.

Conclude with `(finish_bound e hb.2.2.2 (hX g) (hzg g hg)).trans (mul_le_mul_of_nonneg_right hmax hG)`. Rewrite using `[← mx_inv_conjT]`. Conclude with `(finish_bound e hb.2.2.1 (hX g) (hzg g hg)).trans (mul_le_mul_of_nonneg_right hmax hG)`.
-/
theorem unitriangular_inverse_bound_of (h : MonomialFactorizationBound) (hZ : ZhatBound) : UnitriangularInversePolynomialBound := by
  intro k r z z' γ hmono
  obtain ⟨C1, h1⟩ := h (r + 1) (Zhat k r z z' γ) hmono
  obtain ⟨C2, h2⟩ := h (r + 1) (Zhat k r z z' γ)ᴴ (isMonomial_conjT hmono)
  obtain ⟨CZ, hCZ⟩ := hZ k r z z'
  set A : ℝ := 1 + max CZ 0 with hA
  set e : ℕ := r * (r + 1) with he
  have hzg : ∀ g : B.Mat k r, 1 ≤ B.gN g → 1 + mx (Zhat k r z z' g) ≤ A * B.gN g := by
    intro g hg
    have h3 := hCZ g
    have h4 : CZ * B.gN g ≤ max CZ 0 * B.gN g :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    rw [hA]; nlinarith
  have hX : ∀ g : B.Mat k r, 0 ≤ 1 + mx (Zhat k r z z' g) := fun g => by
    have := GN.mx_nonneg (Zhat k r z z' g); linarith
  have hApos : 0 ≤ A ^ e := pow_nonneg (by rw [hA]; have := le_max_right CZ 0; linarith) e
  refine ⟨max (max C1 0) (max C2 0) * A ^ e, ?_, ?_⟩
  · intro v hv hvl u' hu' g hg hZg
    have hb := h1 vᴴ hvl u' hu'
    rw [← hZg, exp_eq] at hb
    have hmax : max C1 0 * A ^ e ≤ max (max C1 0) (max C2 0) * A ^ e :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hApos
    have hG : 0 ≤ B.gN g ^ e := pow_nonneg (by linarith) e
    constructor
    · rw [← mx_inv_conjT]
      exact (finish_bound e hb.2.2.1 (hX g) (hzg g hg)).trans (mul_le_mul_of_nonneg_right hmax hG)
    · exact (finish_bound e hb.2.2.2 (hX g) (hzg g hg)).trans (mul_le_mul_of_nonneg_right hmax hG)
  · intro u hu v' hv' hPv g hg hZg
    have hl : v'ᴴ ∈ LPg (Zhat k r z z' γ)ᴴ := by
      refine ⟨ut_conjT hv', ?_⟩
      have e1 : ((Zhat k r z z' γ)ᴴ)⁻¹ * v'ᴴ * (Zhat k r z z' γ)ᴴ =
          (Zhat k r z z' γ * v' * (Zhat k r z z' γ)⁻¹)ᴴ := by
        rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_nonsing_inv, Matrix.mul_assoc]
      rw [e1]
      exact ut_conjT hPv
    have hb := h2 v'ᴴ hl u hu
    have e2 : v'ᴴ * (Zhat k r z z' γ)ᴴ * u = (Zhat k r z z' g)ᴴ := by
      rw [hZg, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [e2, GN.mx_conjTranspose (Zhat k r z z' g), exp_eq] at hb
    have hmax : max C2 0 * A ^ e ≤ max (max C1 0) (max C2 0) * A ^ e :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hApos
    have hG : 0 ≤ B.gN g ^ e := pow_nonneg (by linarith) e
    constructor
    · exact (finish_bound e hb.2.2.2 (hX g) (hzg g hg)).trans (mul_le_mul_of_nonneg_right hmax hG)
    · rw [← mx_inv_conjT]
      exact (finish_bound e hb.2.2.1 (hX g) (hzg g hg)).trans (mul_le_mul_of_nonneg_right hmax hG)

/- English proof (translation)
The claim follows from `unitriangular_inverse_bound_of h zhatBound`.
-/
theorem unitriangular_inverse_bound (h : MonomialFactorizationBound) : UnitriangularInversePolynomialBound := unitriangular_inverse_bound_of h zhatBound

end PI.PolynomialProperness
