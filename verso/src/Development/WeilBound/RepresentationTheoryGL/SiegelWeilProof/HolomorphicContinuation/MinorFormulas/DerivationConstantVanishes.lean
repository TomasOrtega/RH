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
Simplify using `[dl, MvPolynomial.mkDerivation_X]`.
-/
theorem dl_X (s : ℂ) (b : Bool) (k l : Fin n) (v : Bool × Fin n × Fin n) :
    dl s b k l (X v) = if v.1 = b then k0 s b * (yv b v.2.1 k * yv b l v.2.2) else 0 := by
  simp [dl, MvPolynomial.mkDerivation_X]

/- English proof (translation)
Rewrite using `[Algebra.smul_def, MvPolynomial.algebraMap_apply, Polynomial.algebraMap_apply]`. Both sides reduce to the same expression.
-/
theorem smul_eq (c : ℂ) (p : Fm n) : c • p = MvPolynomial.C (Polynomial.C c) * p := by
  rw [Algebra.smul_def, MvPolynomial.algebraMap_apply, Polynomial.algebraMap_apply]
  rfl

/- English proof (translation)
Set `D : Derivation (Polynomial ℂ) (Fm n) (Fm n)` to `∑ a : Fin n, ∑ d : Fin n, (k0 s b * (yv b a k * yv b l d)) • MvPolynomial.pderiv (b, a, d)`. Establish `hD : ∀ q : Fm n, D q = ∑ a : Fin n, ∑ d : Fin n, (-(cc s b)) • (yv b a k * yv b l d * MvPolynomial.pderiv (b, a, d) q)`. Introduce `q`. Establish `: (D : Fm n → Fm n) = fun q => ∑ a : Fin n, ∑ d : Fin n, (k0 s b * (yv b a k * yv b l d)) * MvPolynomial.pderiv (b, a, d) q`. Use function extensionality and compare the values at `q`.

Simplify using `only [D]`. Rewrite using `[show ((∑ a : Fin n, ∑ d : Fin n, (k0 s b * (yv b a k * yv b l d)) • MvPolynomial.pderiv (b, a, d) : Derivation (Polynomial ℂ) (Fm n) (Fm n)) q) = Derivation.coeFnAddMonoidHom (∑ a : Fin n, ∑ d : Fin n, (k0 s b * (yv b a k * yv b l d)) • MvPolynomial.pderiv (b, a, d)) q from rfl]`. Rewrite using `[map_sum]`. Simplify using `only [map_sum, Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply, smul_eq_mul]`. Rewrite using `[this]`.

Simplify using `only [smul_eq, k0]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hDl : D = dl s b k l`. Apply `MvPolynomial.derivation_ext` to reduce the goal to its premises.

Introduce `v`. Rewrite using `[dl_X]`. Establish `: (D : Fm n → Fm n) (X v) = ∑ a : Fin n, ∑ d : Fin n, (k0 s b * (yv b a k * yv b l d)) * MvPolynomial.pderiv (b, a, d) (X v)`. Rewrite using `[hD]`. Simplify using `only [smul_eq, k0]`.

Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Take `⟨b0, a0, d0⟩` from `v`. Simplify using `only [MvPolynomial.pderiv_X, Pi.single_apply]`.

Distinguish the cases in `hb : b0 = b`. Substitute `hb` using the available equality. Simplify using `only [if_true]`. Rewrite using `[Finset.sum_eq_single a0, Finset.sum_eq_single d0]`. Simplify using the standard rewrite rules.

Introduce `d _ hd`. Simplify using `[Prod.ext_iff, Ne.symm hd]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Introduce `a _ ha`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `d _`. Simplify using `[Prod.ext_iff, Ne.symm ha]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Rewrite using `[if_neg hb]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `a _`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `d _`.

Establish `: ¬ ((b0, a0, d0) = (b, a, d))` using `fun h => hb (congrArg Prod.fst h)`. Simplify using `only [Pi.single_apply, this, if_false, mul_zero]`. Rewrite using `[← hD, hDl]`.
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
Rewrite using `[← sum_eq]`. Simplify using `only [opH, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.coe_restrictScalars, LinearMap.mulLeft_apply, LinearMap.sum_apply, LinearMap.comp_apply, Derivation.coeFn_coe]`. Rewrite using `[smul_eq]`. Simplify using `only [mm, k0, cc, al]`. Use `congr 1`.

Apply the tactic sequence `split_ifs <;> ring`.
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
Rewrite using `[yv, dl_X]`. Simplify using `[Ne.symm h]`.
-/
theorem dl_other (s : ℂ) (b b' : Bool) (h : b ≠ b') (k l a d : Fin n) : dl s b k l (yv b' a d) = 0 := by
  rw [yv, dl_X]; simp [Ne.symm h]

/- English proof (translation)
The claim follows from `MvPolynomial.derivation_C _ r`.
-/
theorem dl_C (s : ℂ) (b : Bool) (k l : Fin n) (r : Polynomial ℂ) : dl s b k l (MvPolynomial.C r) = 0 :=
  MvPolynomial.derivation_C _ r

/- English proof (translation)
The claim follows from `dl_C _ _ _ _ _`.
-/
theorem derivation_constant_vanishes (s : ℂ) (b b' : Bool) (k l : Fin n) : dl s b k l (k0 s b' : Fm n) = 0 := dl_C _ _ _ _ _

/- English proof (translation)
Rewrite using `[yv, dl_X]`. Simplify using the standard rewrite rules.
-/
theorem dl_yv (s : ℂ) (b : Bool) (k l a d : Fin n) : dl s b k l (yv b a d) = k0 s b * (yv b a k * yv b l d) := by
  rw [yv, dl_X]; simp

/- English proof (translation)
Simplify using `only [mm, Derivation.leibniz, derivation_constant_vanishes, dl_C, smul_zero, add_zero, smul_eq_mul]`. Distinguish the cases in `h : b = b'`. Substitute `h` using the available equality. Rewrite using `[dl_yv, dl_yv]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[dl_other s b b' h, dl_other s b' b (Ne.symm h)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem key1 (s : ℂ) (m : ℕ) (b b' : Bool) (k l k' l' : Fin n) :
    dl s b k l (mm s m b' k' l') = dl s b' k' l' (mm s m b k l) := by
  simp only [mm, Derivation.leibniz, derivation_constant_vanishes, dl_C, smul_zero, add_zero, smul_eq_mul]
  by_cases h : b = b'
  · subst h
    rw [dl_yv, dl_yv]; ring
  · rw [dl_other s b b' h, dl_other s b' b (Ne.symm h)]; ring

/- English proof (translation)
Apply `MvPolynomial.derivation_ext` to reduce the goal to its premises. Introduce `v`. Rewrite using `[Derivation.commutator_apply, dl_X, dl_X]`. Take `⟨b0, a0, d0⟩` from `v`. Apply the tactic sequence `by_cases h1 : b0 = b' <;> by_cases h2 : b0 = b`.

Substitute `h1` using the available equality. Substitute `h2` using the available equality. Simplify using `only [if_true, Derivation.leibniz, derivation_constant_vanishes, dl_yv, smul_zero, add_zero, smul_eq_mul]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Substitute `h1` using the available equality. Simplify using `only [if_true, if_neg h2, Derivation.map_zero, Derivation.leibniz, derivation_constant_vanishes, smul_zero, add_zero, smul_eq_mul, dl_other s b b0 (Ne.symm h2)]`. Simplify using the standard rewrite rules. Substitute `h2` using the available equality. Simplify using `only [if_true, if_neg h1, Derivation.map_zero, Derivation.leibniz, derivation_constant_vanishes, smul_zero, add_zero, smul_eq_mul, dl_other s b' b0 (Ne.symm h1)]`.

Simplify using the standard rewrite rules. Simplify using `[if_neg h1, if_neg h2]`.
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
Introduce `n s m b b' k l k' l'`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `p`. Simplify using `only [LinearMap.comp_apply, opH_apply, Derivation.leibniz, map_add, smul_eq_mul]`. Establish `h2 : dl s b k l (dl s b' k' l' p) = dl s b' k' l' (dl s b k l p)`.

Use `congrArg (fun D : Derivation (Polynomial ℂ) (Fm n) (Fm n) => D p) (key2 s b b' k l k' l')` as an intermediate fact. Simplify `this` using `[Derivation.commutator_apply, sub_eq_zero]`. Rewrite using `[h2, key1 s m b b' k l k' l']`. Expand and normalize the polynomial expressions, which then agree.
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
