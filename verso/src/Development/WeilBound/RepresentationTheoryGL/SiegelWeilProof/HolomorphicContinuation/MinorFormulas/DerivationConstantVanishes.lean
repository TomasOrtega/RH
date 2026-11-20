import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.CayDivOf

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.SP

variable {n : ℕ}

namespace CommPf

def cc (s : ℂ) (b : Bool) : ℂ := if b then Complex.I * s else -(Complex.I * s)

def al (m : ℕ) (b : Bool) : Polynomial ℂ := if b then Polynomial.X else Polynomial.C (m : ℂ) + Polynomial.X

def k0 (s : ℂ) (b : Bool) : Fm n := MvPolynomial.C (Polynomial.C (-(cc s b)))

def mm (s : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) : Fm n := k0 s b * (MvPolynomial.C (al m b) * yv b l k)

def dl (s : ℂ) (b : Bool) (k l : Fin n) : Derivation (Polynomial ℂ) (Fm n) (Fm n) :=
  MvPolynomial.mkDerivation (Polynomial ℂ)
    (fun v => if v.1 = b then k0 s b * (yv b v.2.1 k * yv b l v.2.2) else 0)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem dl_X (s : ℂ) (b : Bool) (k l : Fin n) (v : Bool × Fin n × Fin n) :
    dl s b k l (X v) = if v.1 = b then k0 s b * (yv b v.2.1 k * yv b l v.2.2) else 0 := by
  simp [dl, MvPolynomial.mkDerivation_X]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem smul_eq (c : ℂ) (p : Fm n) : c • p = MvPolynomial.C (Polynomial.C c) * p := by
  rw [Algebra.smul_def, MvPolynomial.algebraMap_apply, Polynomial.algebraMap_apply]
  rfl

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sum_eq (s : ℂ) (b : Bool) (k l : Fin n) (p : Fm n) :
    (∑ a : Fin n, ∑ d : Fin n, (-(cc s b)) • (yv b a k * yv b l d * MvPolynomial.pderiv (b, a, d) p)) = dl s b k l p := by
  let D : Derivation (Polynomial ℂ) (Fm n) (Fm n) :=
    ∑ a : Fin n, ∑ d : Fin n, (k0 s b * (yv b a k * yv b l d)) • MvPolynomial.pderiv (b, a, d)
  have hD : ∀ q : Fm n, D q = ∑ a : Fin n, ∑ d : Fin n, (-(cc s b)) • (yv b a k * yv b l d * MvPolynomial.pderiv (b, a, d) q) := by
    intro q
    have : (D : Fm n → Fm n) = fun q => ∑ a : Fin n, ∑ d : Fin n, (k0 s b * (yv b a k * yv b l d)) * MvPolynomial.pderiv (b, a, d) q := by
      funext q
      simp only [D]
      rw [show ((∑ a : Fin n, ∑ d : Fin n, (k0 s b * (yv b a k * yv b l d)) • MvPolynomial.pderiv (b, a, d) :
          Derivation (Polynomial ℂ) (Fm n) (Fm n)) q) =
          Derivation.coeFnAddMonoidHom (∑ a : Fin n, ∑ d : Fin n, (k0 s b * (yv b a k * yv b l d)) • MvPolynomial.pderiv (b, a, d)) q from rfl]
      rw [map_sum]
      simp only [map_sum, Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply, smul_eq_mul]
    rw [this]
    simp only [smul_eq, k0]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  have hDl : D = dl s b k l := by
    apply MvPolynomial.derivation_ext
    intro v
    rw [dl_X]
    have : (D : Fm n → Fm n) (X v) = ∑ a : Fin n, ∑ d : Fin n, (k0 s b * (yv b a k * yv b l d)) * MvPolynomial.pderiv (b, a, d) (X v) := by
      rw [hD]
      simp only [smul_eq, k0]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
      ring
    rw [this]
    obtain ⟨b0, a0, d0⟩ := v
    simp only [MvPolynomial.pderiv_X, Pi.single_apply]
    by_cases hb : b0 = b
    · subst hb
      simp only [if_true]
      rw [Finset.sum_eq_single a0, Finset.sum_eq_single d0]
      · simp
      · intro d _ hd; simp [Prod.ext_iff, Ne.symm hd]
      · intro h; exact absurd (Finset.mem_univ _) h
      · intro a _ ha; apply Finset.sum_eq_zero; intro d _; simp [Prod.ext_iff, Ne.symm ha]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg hb]
      apply Finset.sum_eq_zero; intro a _; apply Finset.sum_eq_zero; intro d _
      have : ¬ ((b0, a0, d0) = (b, a, d)) := fun h => hb (congrArg Prod.fst h)
      simp only [Pi.single_apply, this, if_false, mul_zero]
  rw [← hD, hDl]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments.

Apply the first step, then apply the next step to every resulting obligation.
-/
theorem opH_apply (s : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) (p : Fm n) :
    opH s m b k l p = mm s m b k l * p + dl s b k l p := by
  rw [← sum_eq]
  simp only [opH, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.coe_restrictScalars, LinearMap.mulLeft_apply,
    LinearMap.sum_apply, LinearMap.comp_apply, Derivation.coeFn_coe]
  rw [smul_eq]
  simp only [mm, k0, cc, al]
  congr 1
  split_ifs <;> ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem dl_other (s : ℂ) (b b' : Bool) (h : b ≠ b') (k l a d : Fin n) : dl s b k l (yv b' a d) = 0 := by
  rw [yv, dl_X]; simp [Ne.symm h]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dl_C (s : ℂ) (b : Bool) (k l : Fin n) (r : Polynomial ℂ) : dl s b k l (MvPolynomial.C r) = 0 :=
  MvPolynomial.derivation_C _ r

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem derivation_constant_vanishes (s : ℂ) (b b' : Bool) (k l : Fin n) : dl s b k l (k0 s b' : Fm n) = 0 := dl_C _ _ _ _ _

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem dl_yv (s : ℂ) (b : Bool) (k l a d : Fin n) : dl s b k l (yv b a d) = k0 s b * (yv b a k * yv b l d) := by
  rw [yv, dl_X]; simp

/- English proof (translation)
Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem key1 (s : ℂ) (m : ℕ) (b b' : Bool) (k l k' l' : Fin n) :
    dl s b k l (mm s m b' k' l') = dl s b' k' l' (mm s m b k l) := by
  simp only [mm, Derivation.leibniz, derivation_constant_vanishes, dl_C, smul_zero, add_zero, smul_eq_mul]
  by_cases h : b = b'
  · subst h
    rw [dl_yv, dl_yv]; ring
  · rw [dl_other s b b' h, dl_other s b' b (Ne.symm h)]; ring

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Apply the first step, then apply the next step to every resulting obligation.

Substitute using the available equality. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Substitute using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem key2 (s : ℂ) (b b' : Bool) (k l k' l' : Fin n) : ⁅dl s b k l, dl s b' k' l'⁆ = 0 := by
  apply MvPolynomial.derivation_ext
  intro v
  rw [Derivation.commutator_apply, dl_X, dl_X]
  obtain ⟨b0, a0, d0⟩ := v
  by_cases h1 : b0 = b' <;> by_cases h2 : b0 = b
  · subst h1; subst h2
    simp only [if_true, Derivation.leibniz, derivation_constant_vanishes, dl_yv, smul_zero, add_zero, smul_eq_mul]
    simp
    ring
  · subst h1
    simp only [if_true, if_neg h2, Derivation.map_zero, Derivation.leibniz, derivation_constant_vanishes, smul_zero, add_zero, smul_eq_mul,
      dl_other s b b0 (Ne.symm h2)]
    simp
  · subst h2
    simp only [if_true, if_neg h1, Derivation.map_zero, Derivation.leibniz, derivation_constant_vanishes, smul_zero, add_zero, smul_eq_mul,
      dl_other s b' b0 (Ne.symm h1)]
    simp
  · simp [if_neg h1, if_neg h2]

end CommPf

open CommPf in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem comm : Comm := by
  intro n s m b b' k l k' l'
  apply LinearMap.ext
  intro p
  simp only [LinearMap.comp_apply, opH_apply, Derivation.leibniz, map_add, smul_eq_mul]
  have h2 : dl s b k l (dl s b' k' l' p) = dl s b' k' l' (dl s b k l p) := by
    have := congrArg (fun D : Derivation (Polynomial ℂ) (Fm n) (Fm n) => D p) (key2 s b b' k l k' l')
    simpa [Derivation.commutator_apply, sub_eq_zero] using this
  rw [h2, key1 s m b b' k l k' l']
  ring

end PositivityTheory.Rg.Sw.SP
