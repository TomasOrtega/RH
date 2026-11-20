import Formalism.SharpRestriction.GrowthBounds.RootWeights.EBeta

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

/- English proof (translation)
Set `M : Matrix (Fin n) (Fin n) T` to `Matrix.of fun i j => ⟨N i j, h i j⟩`. Establish `hM : (T.val.toRingHom).mapMatrix M = N` using `by ext i j; rfl`. Rewrite using `[← hM, ← RingHom.map_det]`. Conclude with `M.det.2`.
-/
theorem det_mem_subalgebra_of_entries {R P : Type*} [CommRing R] [CommRing P] [Algebra R P] (T : Subalgebra R P) {n : ℕ}
    (N : Matrix (Fin n) (Fin n) P) (h : ∀ i j, N i j ∈ T) : N.det ∈ T := by
  let M : Matrix (Fin n) (Fin n) T := Matrix.of fun i j => ⟨N i j, h i j⟩
  have hM : (T.val.toRingHom).mapMatrix M = N := by ext i j; rfl
  rw [← hM, ← RingHom.map_det]
  exact M.det.2

/- English proof (translation)
Rewrite `hs`, the goal using `[mem_supported]`. Take `⟨g, rfl⟩` from `hq`. Establish `hq0 : q ≠ 0` using `by rintro rfl; simp at hf`. Establish `hg0 : g ≠ 0` using `by rintro rfl; simp at hf`. Introduce `v hv`.

Assume the negation of the conclusion as `hvs`. Establish `h1 : degreeOf v (q * g) = degreeOf v q + degreeOf v g` using `degreeOf_mul_eq hq0 hg0`. Establish `h2 : degreeOf v (q * g) = 0`. Rewrite using `[degreeOf_eq_sup]`. Use `Nat.le_zero.mp (Finset.sup_le fun m hm => ?_)` and prove the remaining obligations.

Assume the negation of the conclusion as `hmv`. Conclude with `hvs (hs ((mem_vars v).mpr ⟨m, hm, Finsupp.mem_support_iff.mpr (by omega)⟩))`. Establish `h3 : degreeOf v q ≠ 0`. Take `⟨m, hm, hvm⟩` from `(mem_vars v).mp hv`. Use `monomial_le_degreeOf v hm` as an intermediate fact.

Use `Finsupp.mem_support_iff.mp hvm` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers.
-/
theorem divisor_supported_of_supported {R σ : Type*} [CommRing R] [IsDomain R] {s : Set σ} {f q : MvPolynomial σ R}
    (hf : f ≠ 0) (hs : f ∈ supported R s) (hq : q ∣ f) : q ∈ supported R s := by
  rw [mem_supported] at hs ⊢
  obtain ⟨g, rfl⟩ := hq
  have hq0 : q ≠ 0 := by rintro rfl; simp at hf
  have hg0 : g ≠ 0 := by rintro rfl; simp at hf
  intro v hv
  by_contra hvs
  have h1 : degreeOf v (q * g) = degreeOf v q + degreeOf v g := degreeOf_mul_eq hq0 hg0
  have h2 : degreeOf v (q * g) = 0 := by
    rw [degreeOf_eq_sup]
    refine Nat.le_zero.mp (Finset.sup_le fun m hm => ?_)
    by_contra hmv
    exact hvs (hs ((mem_vars v).mpr ⟨m, hm, Finsupp.mem_support_iff.mpr (by omega)⟩))
  have h3 : degreeOf v q ≠ 0 := by
    obtain ⟨m, hm, hvm⟩ := (mem_vars v).mp hv
    have := monomial_le_degreeOf v hm
    have := Finsupp.mem_support_iff.mp hvm
    omega
  omega

/- English proof (translation)
Rewrite `hq` using `[supported_eq_adjoin_X]`. Establish `hle : Algebra.adjoin R (X '' s) ≤ AlgHom.equalizer φ (AlgHom.id R _)`. Rewrite using `[Algebra.adjoin_le_iff]`. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Conclude with `h v hv`.

Conclude with `hle hq`.
-/
theorem algHom_fixes_supported_polynomials {R σ : Type*} [CommRing R] {s : Set σ} (φ : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (h : ∀ v ∈ s, φ (X v) = X v) {q : MvPolynomial σ R} (hq : q ∈ supported R s) : φ q = q := by
  rw [supported_eq_adjoin_X] at hq
  have hle : Algebra.adjoin R (X '' s) ≤ AlgHom.equalizer φ (AlgHom.id R _) := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨v, hv, rfl⟩
    exact h v hv
  exact hle hq

def cofactorMatrix (R : Type) [CommRing R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι) (a : Fin r) :
    Matrix (Fin r) (Fin r) (MvPolynomial (ι × Fin r) R) :=
  (matA R A).updateRow (lastIdx r) (Pi.single a 1)

def cofactorMatrixColumnCleared (R : Type) [CommRing R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι) (a : Fin r) :
    Matrix (Fin r) (Fin r) (MvPolynomial (ι × Fin r) R) :=
  Matrix.of fun i j => if i = lastIdx r then (if j = a then 1 else 0) else (if j = a then 0 else X (A i, j))

/- English proof (translation)
Rewrite using `[Matrix.adjugate_apply]`. Both sides reduce to the same expression.
-/
theorem adjugate_last_row_eq_cofactor_det (R : Type) [CommRing R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι) (a : Fin r) :
    (matA R A).adjugate a (lastIdx r) = (cofactorMatrix R A a).det := by
  rw [Matrix.adjugate_apply]; rfl

/- English proof (translation)
Use `symm`. Use `Matrix.det_eq_of_forall_row_eq_smul_add_const (fun i => if i = lastIdx r then 0 else -X (A i, a)) (lastIdx r) (by simp) ?_` and prove the remaining obligations. Introduce `i j`. Distinguish the cases in `hi : i = lastIdx r`. Substitute `hi` using the available equality.

Simplify using `[cofactorMatrix, cofactorMatrixColumnCleared, Matrix.updateRow_self, Pi.single_apply]`. Distinguish the cases in `hj : j = a`. Substitute `hj` using the available equality. Simplify using `[cofactorMatrix, cofactorMatrixColumnCleared, hi, Matrix.updateRow_ne hi, Matrix.updateRow_self, matA]`. Simplify using `[cofactorMatrix, cofactorMatrixColumnCleared, hi, hj, Matrix.updateRow_ne hi, Matrix.updateRow_self, matA, Pi.single_apply]`.
-/
theorem cofactor_det_eq_cleared_det (R : Type) [CommRing R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι) (a : Fin r) :
    (cofactorMatrix R A a).det = (cofactorMatrixColumnCleared R A a).det := by
  symm
  classical
  refine Matrix.det_eq_of_forall_row_eq_smul_add_const
    (fun i => if i = lastIdx r then 0 else -X (A i, a)) (lastIdx r) (by simp) ?_
  intro i j
  by_cases hi : i = lastIdx r
  · subst hi
    simp [cofactorMatrix, cofactorMatrixColumnCleared, Matrix.updateRow_self, Pi.single_apply]
  · by_cases hj : j = a
    · subst hj
      simp [cofactorMatrix, cofactorMatrixColumnCleared, hi, Matrix.updateRow_ne hi, Matrix.updateRow_self, matA]
    · simp [cofactorMatrix, cofactorMatrixColumnCleared, hi, hj, Matrix.updateRow_ne hi, Matrix.updateRow_self, matA, Pi.single_apply]

def cofactorVariables {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι) (a : Fin r) : Set (ι × Fin r) :=
  {v | (∃ i, i ≠ lastIdx r ∧ v.1 = A i) ∧ v.2 ≠ a}

/- English proof (translation)
Rewrite using `[adjugate_last_row_eq_cofactor_det, cofactor_det_eq_cleared_det]`. Apply `det_mem_subalgebra_of_entries` to reduce the goal to its premises. Introduce `i j`. Simplify using `only [cofactorMatrixColumnCleared, Matrix.of_apply]`. Use `split_ifs with h1 h2 h3`.

Conclude with `Subalgebra.one_mem _`. Conclude with `Subalgebra.zero_mem _`. Conclude with `Subalgebra.zero_mem _`. Rewrite using `[supported_eq_adjoin_X]`. Conclude with `Algebra.subset_adjoin ⟨_, ⟨⟨i, h1, rfl⟩, h3⟩, rfl⟩`.
-/
theorem cofactor_last_row_supported (R : Type) [CommRing R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι) (a : Fin r) :
    (matA R A).adjugate a (lastIdx r) ∈ supported R (cofactorVariables A a) := by
  rw [adjugate_last_row_eq_cofactor_det, cofactor_det_eq_cleared_det]
  apply det_mem_subalgebra_of_entries
  intro i j
  simp only [cofactorMatrixColumnCleared, Matrix.of_apply]
  split_ifs with h1 h2 h3
  · exact Subalgebra.one_mem _
  · exact Subalgebra.zero_mem _
  · exact Subalgebra.zero_mem _
  · rw [supported_eq_adjoin_X]
    exact Algebra.subset_adjoin ⟨_, ⟨⟨i, h1, rfl⟩, h3⟩, rfl⟩

open Classical in

/- English proof (translation)
Rewrite using `[adjugate_last_row_eq_cofactor_det, cofactor_det_eq_cleared_det]`. Introduce `h0`. Use `set σ : Equiv.Perm (Fin r) := Equiv.swap a (lastIdx r) with hσ`. Set `g : ι × Fin r → R` to `fun v => if ∃ i, v = (A i, σ i) then 1 else 0`. Establish `hmap : (eval g).mapMatrix (cofactorMatrixColumnCleared R A a) = σ.permMatrix R`.

Use extensionality with `i j`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, cofactorMatrixColumnCleared, Matrix.of_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]`. Distinguish the cases in `hi : i = lastIdx r`. Substitute `hi` using the available equality. Distinguish the cases in `hj : j = a`.

Substitute `hj` using the available equality. Simplify using `[hσ, Equiv.swap_apply_right]`. Establish `: σ (lastIdx r) ≠ j` using `by rw [hσ, Equiv.swap_apply_right]; exact Ne.symm hj`. Simplify using `[hj, this]`. Establish `hσi : σ i ≠ a`.

Introduce `h`. Apply `hi` to reduce the goal to its premises. Use `congrArg σ h` as an intermediate fact. Rewrite `this` using `[hσ, Equiv.swap_apply_self, Equiv.swap_apply_left]`. Then use the resulting hypothesis. Establish `key : (∃ i', A i = A i' ∧ j = σ i') ↔ σ i = j`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i', h1, h2⟩`. Rewrite using `[hA h1]`. Conclude with `h2.symm`. Introduce `h`.

Conclude with `⟨i, rfl, h.symm⟩`. Distinguish the cases in `hj : j = a`. Substitute `hj` using the available equality. Simplify using `[hi, hσi]`. Simplify using `[hi, hj, g, key]`.

Establish `hdet` using `congrArg (eval g) h0`. Rewrite `hdet` using `[RingHom.map_det, hmap, Matrix.det_permutation, map_zero]`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs] at hdet`.
-/
theorem adjugate_last_row_ne_zero (R : Type) [CommRing R] [Nontrivial R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι)
    (hA : Function.Injective A) (a : Fin r) : (matA R A).adjugate a (lastIdx r) ≠ 0 := by
  rw [adjugate_last_row_eq_cofactor_det, cofactor_det_eq_cleared_det]
  intro h0
  set σ : Equiv.Perm (Fin r) := Equiv.swap a (lastIdx r) with hσ
  let g : ι × Fin r → R := fun v => if ∃ i, v = (A i, σ i) then 1 else 0
  have hmap : (eval g).mapMatrix (cofactorMatrixColumnCleared R A a) = σ.permMatrix R := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, cofactorMatrixColumnCleared, Matrix.of_apply,
      Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
      Option.some.injEq]
    by_cases hi : i = lastIdx r
    · subst hi
      by_cases hj : j = a
      · subst hj; simp [hσ, Equiv.swap_apply_right]
      · have : σ (lastIdx r) ≠ j := by rw [hσ, Equiv.swap_apply_right]; exact Ne.symm hj
        simp [hj, this]
    · have hσi : σ i ≠ a := by
        intro h
        apply hi
        have := congrArg σ h
        rwa [hσ, Equiv.swap_apply_self, Equiv.swap_apply_left] at this
      have key : (∃ i', A i = A i' ∧ j = σ i') ↔ σ i = j := by
        constructor
        · rintro ⟨i', h1, h2⟩
          rw [hA h1]; exact h2.symm
        · intro h; exact ⟨i, rfl, h.symm⟩
      by_cases hj : j = a
      · subst hj; simp [hi, hσi]
      · simp [hi, hj, g, key]
  have hdet := congrArg (eval g) h0
  rw [RingHom.map_det, hmap, Matrix.det_permutation, map_zero] at hdet
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs] at hdet

open Classical in

def lastRowSubstitution (R : Type) [CommRing R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι) (a : Fin r) :
    MvPolynomial (ι × Fin r) R →ₐ[R] MvPolynomial (ι × Fin r) R :=
  aeval fun v => if v.1 = A (lastIdx r) then (if v.2 = a then 1 else 0) else X v

/- English proof (translation)
Rewrite using `[adjugate_last_row_eq_cofactor_det]`. Unfold `detA`. Rewrite using `[AlgHom.map_det]`. Use `congr 1`. Use extensionality with `i j`.

Simplify using `only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, cofactorMatrix, lastRowSubstitution, aeval_X, matA]`. Distinguish the cases in `hi : i = lastIdx r`. Substitute `hi` using the available equality. Simplify using `[Matrix.updateRow_self, Pi.single_apply]`. Establish `: A i ≠ A (lastIdx r)` using `hA.ne hi`.

Simplify using `[this, Matrix.updateRow_ne hi, matA]`.
-/
theorem substitution_det_eq_adjugate (R : Type) [CommRing R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι)
    (hA : Function.Injective A) (a : Fin r) :
    lastRowSubstitution R A a (detA (R := R) A) = (matA R A).adjugate a (lastIdx r) := by
  rw [adjugate_last_row_eq_cofactor_det]
  unfold detA
  rw [AlgHom.map_det]
  congr 1
  ext i j
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, cofactorMatrix, lastRowSubstitution, aeval_X, matA]
  by_cases hi : i = lastIdx r
  · subst hi
    simp [Matrix.updateRow_self, Pi.single_apply]
  · have : A i ≠ A (lastIdx r) := hA.ne hi
    simp [this, Matrix.updateRow_ne hi, matA]

/- English proof (translation)
Introduce `R _ ι r _ A hA`. Establish `hC` using `adjugate_last_row_ne_zero R A hA (lastIdx r)`. Use `⟨hC, ?_⟩` and prove the remaining obligations. Introduce `d hd1 hd2`. Establish `hd0 : d ≠ 0` using `by rintro rfl; exact hC (zero_dvd_iff.mp hd2)`.

Establish `hsL : d ∈ supported R (cofactorVariables A (lastIdx r))` using `divisor_supported_of_supported hC (cofactor_last_row_supported R A _) hd2`. Establish `hall : ∀ a, d ∈ supported R (cofactorVariables A a)`. Introduce `a`. Establish `hfix : lastRowSubstitution R A a d = d`. Use `algHom_fixes_supported_polynomials _ ?_ hsL` and prove the remaining obligations.

Introduce and unpack `v ⟨⟨i, hi, hv⟩, -⟩`. Establish `: v.1 ≠ A (lastIdx r)` using `by rw [hv]; exact hA.ne hi`. Simplify using `[lastRowSubstitution, this]`. Establish `hdv : d ∣ (matA R A).adjugate a (lastIdx r)`. Rewrite using `[← substitution_det_eq_adjugate R A hA a, ← hfix]`.

Conclude with `map_dvd _ hd1`. Conclude with `divisor_supported_of_supported (adjugate_last_row_ne_zero R A hA a) (cofactor_last_row_supported R A a) hdv`. Establish `hsub : (d.vars : Set (ι × Fin r)) ⊆ ∅`. Introduce `v hv`. Conclude with `((mem_supported.mp (hall v.2)) hv).2 rfl`.

Establish `h0 : d ∈ supported R (∅ : Set (ι × Fin r))` using `mem_supported.mpr hsub`. Rewrite `h0` using `[supported_empty, Algebra.mem_bot]`. Take `⟨c, rfl⟩` from `h0`. Establish `hc : c ≠ 0` using `by rintro rfl; exact hd0 (map_zero _)`. Conclude with `(IsUnit.mk0 c hc).map (algebraMap R _)`.
-/
theorem hCop_proved : HCop := by
  intro R _ ι r _ A hA
  have hC := adjugate_last_row_ne_zero R A hA (lastIdx r)
  refine ⟨hC, ?_⟩
  intro d hd1 hd2
  have hd0 : d ≠ 0 := by rintro rfl; exact hC (zero_dvd_iff.mp hd2)
  have hsL : d ∈ supported R (cofactorVariables A (lastIdx r)) :=
    divisor_supported_of_supported hC (cofactor_last_row_supported R A _) hd2
  have hall : ∀ a, d ∈ supported R (cofactorVariables A a) := by
    intro a
    have hfix : lastRowSubstitution R A a d = d := by
      refine algHom_fixes_supported_polynomials _ ?_ hsL
      rintro v ⟨⟨i, hi, hv⟩, -⟩
      have : v.1 ≠ A (lastIdx r) := by rw [hv]; exact hA.ne hi
      simp [lastRowSubstitution, this]
    have hdv : d ∣ (matA R A).adjugate a (lastIdx r) := by
      rw [← substitution_det_eq_adjugate R A hA a, ← hfix]; exact map_dvd _ hd1
    exact divisor_supported_of_supported (adjugate_last_row_ne_zero R A hA a) (cofactor_last_row_supported R A a) hdv
  have hsub : (d.vars : Set (ι × Fin r)) ⊆ ∅ := by
    intro v hv
    exact ((mem_supported.mp (hall v.2)) hv).2 rfl
  have h0 : d ∈ supported R (∅ : Set (ι × Fin r)) := mem_supported.mpr hsub
  rw [supported_empty, Algebra.mem_bot] at h0
  obtain ⟨c, rfl⟩ := h0
  have hc : c ≠ 0 := by rintro rfl; exact hd0 (map_zero _)
  exact (IsUnit.mk0 c hc).map (algebraMap R _)

end Formalism.MainNotions.G.GLWeightTheory
