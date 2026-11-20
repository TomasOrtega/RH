import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms

open IsDedekindDomain NumberField Formalism.UG Formalism.IndefR.Mult GlobalTheory.SphPar Polynomial

namespace GlobalTheory.DualDivU

section Generic

variable {L : Type} [Field L] {n : ℕ}

/- English proof (translation)
Set `A0 : Matrix (Fin n) (Fin n) O` to `Matrix.of fun i j => ⟨A i j, hA i j⟩`. Set `B0 : Matrix (Fin n) (Fin n) O` to `Matrix.of fun i j => ⟨B i j, hB i j⟩`. Establish `eA : RingHom.mapMatrix (m` using `Fin n) O.subtype A0 = A := by ext i j; rfl`. Establish `eB : RingHom.mapMatrix (m` using `Fin n) O.subtype B0 = B := by ext i j; rfl`. Establish `inj : Function.Injective (RingHom.mapMatrix (m` using `Fin n) O.subtype) := by`.

Introduce `X Y h`. Use extensionality with `i j`. Simplify using `using congrFun (congrFun h i) j`. Establish `h1 : A0 * B0 = 1` using `inj (by rw [map_mul, map_one, eA, eB, hAB])`. Establish `h2 : B0 * A0 = 1` using `inj (by rw [map_mul, map_one, eA, eB, hBA])`.

Conclude with `⟨bc (n := Fin n) O.subtype ⟨A0, B0, h1, h2⟩, ⟨_, rfl⟩, eA⟩`.
-/
theorem exists_glint (O : Subring L) (A B : Matrix (Fin n) (Fin n) L) (hAB : A * B = 1) (hBA : B * A = 1)
    (hA : ∀ i j, A i j ∈ O) (hB : ∀ i j, B i j ∈ O) :
    ∃ U ∈ GLint (Fin n) O, (U : Matrix (Fin n) (Fin n) L) = A := by
  let A0 : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨A i j, hA i j⟩
  let B0 : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨B i j, hB i j⟩
  have eA : RingHom.mapMatrix (m := Fin n) O.subtype A0 = A := by ext i j; rfl
  have eB : RingHom.mapMatrix (m := Fin n) O.subtype B0 = B := by ext i j; rfl
  have inj : Function.Injective (RingHom.mapMatrix (m := Fin n) O.subtype) := by
    intro X Y h
    ext i j
    simpa using congrFun (congrFun h i) j
  have h1 : A0 * B0 = 1 := inj (by rw [map_mul, map_one, eA, eB, hAB])
  have h2 : B0 * A0 = 1 := inj (by rw [map_mul, map_one, eA, eB, hBA])
  exact ⟨bc (n := Fin n) O.subtype ⟨A0, B0, h1, h2⟩, ⟨_, rfl⟩, eA⟩

/- English proof (translation)
Take `⟨U0, rfl⟩` from `hU`. Conclude with `((U0 : Matrix (Fin n) (Fin n) O) i j).2`.
-/
theorem entry_mem (O : Subring L) {U : GL (Fin n) L} (hU : U ∈ GLint (Fin n) O) (i j : Fin n) :
    (U : Matrix (Fin n) (Fin n) L) i j ∈ O := by
  obtain ⟨U0, rfl⟩ := hU
  exact ((U0 : Matrix (Fin n) (Fin n) O) i j).2

/- English proof (translation)
Unfold `antiJ`. Use `congr 1`. Use `i.2` as an intermediate fact. Use `j.2` as an intermediate fact. Simplify using `only [Fin.ext_iff, Fin.val_rev, eq_iff_iff]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem antiJ_apply (i j : Fin n) : antiJ L n i j = if j = i.rev then 1 else 0 := by
  unfold antiJ
  congr 1
  have := i.2
  have := j.2
  simp only [Fin.ext_iff, Fin.val_rev, eq_iff_iff]
  omega

/- English proof (translation)
Simplify using `[Matrix.mul_apply, antiJ_apply]`.
-/
theorem antiJ_mul (A : Matrix (Fin n) (Fin n) L) (i j : Fin n) : (antiJ L n * A) i j = A i.rev j := by
  simp [Matrix.mul_apply, antiJ_apply]

/- English proof (translation)
Establish `: ∀ k : Fin n, (j = k.rev) = (k = j.rev)` using `fun k => by`. Rewrite using `[eq_iff_iff, eq_comm, Fin.rev_eq_iff]`. Simplify using `[Matrix.mul_apply, antiJ_apply, this]`.
-/
theorem mul_antiJ (A : Matrix (Fin n) (Fin n) L) (i j : Fin n) : (A * antiJ L n) i j = A i j.rev := by
  have : ∀ k : Fin n, (j = k.rev) = (k = j.rev) := fun k => by
    rw [eq_iff_iff, eq_comm, Fin.rev_eq_iff]
  simp [Matrix.mul_apply, antiJ_apply, this]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[antiJ_mul, antiJ_apply, Fin.rev_rev, Matrix.one_apply]`. Simplify using `[eq_comm]`.
-/
theorem antiJ_sq : antiJ L n * antiJ L n = 1 := by
  ext i j
  rw [antiJ_mul, antiJ_apply, Fin.rev_rev, Matrix.one_apply]
  simp [eq_comm]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[antiJ_sq, Matrix.mul_one, cT_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [h, cT_one, Matrix.mul_one, antiJ_sq]`.
-/
theorem dual_mul (σ : L →+* L) (A B : Matrix (Fin n) (Fin n) L) (h : A * B = 1) :
    antiJ L n * cT σ B * antiJ L n * (antiJ L n * cT σ A * antiJ L n) = 1 := by
  calc _ = antiJ L n * cT σ B * (antiJ L n * antiJ L n) * cT σ A * antiJ L n := by simp only [Matrix.mul_assoc]
    _ = antiJ L n * cT σ (A * B) * antiJ L n := by
      rw [antiJ_sq, Matrix.mul_one, cT_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, cT_one, Matrix.mul_one, antiJ_sq]

/- English proof (translation)
Substitute `hd` using the available equality. Establish `hi` using `i.2`. Establish `h1 : (i : ℕ) < (dualLab d).length` using `by simp [dualLab]`. Rewrite using `[List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ i.rev.2]`. Simplify using `only [dualLab, List.getElem_reverse, List.getElem_map, List.length_map, Fin.val_rev]`.

Use `congr 2`. Use linear arithmetic over natural numbers and integers.
-/
theorem getD_dualLab (d : List ℤ) (hd : d.length = n) (i : Fin n) :
    (dualLab d).getD i 0 = -(d.getD i.rev 0) := by
  subst hd
  have hi := i.2
  have h1 : (i : ℕ) < (dualLab d).length := by simp [dualLab]
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ i.rev.2]
  simp only [dualLab, List.getElem_reverse, List.getElem_map, List.length_map, Fin.val_rev]
  congr 2
  omega

end Generic

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

/- English proof (translation)
Establish `key : ∀ b ∈ GLint (Fin n) (intL L), ∀ i j, (antiJ L n * cT σ ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * antiJ L n) i j ∈ intL L`. Introduce `b hb i j`. Rewrite using `[mul_antiJ, antiJ_mul]`. Use `entry_mem (intL L) hb j.rev i.rev` as an intermediate fact. Use `show Valued.v (σ _) ≤ 1`.

Rewrite using `[hσ]`. Conclude with `this`. Conclude with `exists_glint (intL L) _ (antiJ L n * cT σ (a : Matrix (Fin n) (Fin n) L) * antiJ L n) (dual_mul σ _ _ (Units.mul_inv a)) (dual_mul σ _ _ (Units.inv_mul a)) (key _ (inv_mem ha)) (key _ ha)`.
-/
theorem exists_dual (σ : L →+* L) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {a : GL (Fin n) L}
    (ha : a ∈ GLint (Fin n) (intL L)) :
    ∃ U ∈ GLint (Fin n) (intL L), (U : Matrix (Fin n) (Fin n) L) =
      antiJ L n * cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * antiJ L n := by
  have key : ∀ b ∈ GLint (Fin n) (intL L), ∀ i j,
      (antiJ L n * cT σ ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * antiJ L n) i j ∈ intL L := by
    intro b hb i j
    rw [mul_antiJ, antiJ_mul]
    have := entry_mem (intL L) hb j.rev i.rev
    show Valued.v (σ _) ≤ 1
    rw [hσ]
    exact this
  exact exists_glint (intL L) _ (antiJ L n * cT σ (a : Matrix (Fin n) (Fin n) L) * antiJ L n)
    (dual_mul σ _ _ (Units.mul_inv a)) (dual_mul σ _ _ (Units.inv_mul a)) (key _ (inv_mem ha)) (key _ ha)

/- English proof (translation)
Introduce `L _ _ σ n d g hσ hd hg ⟨ϖ, hϖ, a, ha, b, hb, hab⟩`. Take `⟨a', ha', ea⟩` from `exists_dual σ hσ ha`. Take `⟨b', hb', eb⟩` from `exists_dual σ hσ hb`. Establish `hϖ0 : ϖ ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hϖ` using `[map_zero]`. Conclude with `WithZero.zero_ne_coe hϖ`. Use `⟨σ ϖ, by rw [hσ, hϖ], a', ha', b', hb', ?_⟩` and prove the remaining obligations. Establish `hg' : cT σ (g : Matrix (Fin n) (Fin n) L) * antiJ L n * (g : Matrix (Fin n) (Fin n) L) = antiJ L n` using `hg`. Establish `eD : Matrix.diagonal (fun i : Fin n => σ ϖ ^ (dualLab d).getD i 0) = antiJ L n * cT σ (Matrix.diagonal (fun i : Fin n => ϖ ^ (-d.getD i 0))) * antiJ L n`.

Use extensionality with `i j`. Rewrite using `[mul_antiJ, antiJ_mul]`. Simplify using `only [cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply, Fin.rev_inj]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using `only [if_true]`. Rewrite using `[getD_dualLab d hd, map_zpow₀]`. Rewrite using `[if_neg h, if_neg (Ne.symm h), map_zero]`. Establish `hDD : Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i 0) * Matrix.diagonal (fun i : Fin n => ϖ ^ (-d.getD i 0)) = 1`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero]`. Establish `hinv : (g : Matrix (Fin n) (Fin n) L) * (((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.diagonal (fun i : Fin n => ϖ ^ (-d.getD i 0)) * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) = 1`. Rewrite using `[hab]`.

Combine the equalities or inequalities in the displayed calculation. Establish `h1` using `dual_mul σ _ _ hinv`. Establish `h2 : antiJ L n * cT σ (g : Matrix (Fin n) (Fin n) L) * antiJ L n * (g : Matrix (Fin n) (Fin n) L) = 1`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ _), hg', antiJ_sq]`. Establish `h3 : (g : Matrix (Fin n) (Fin n) L) = antiJ L n * cT σ (((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.diagonal (fun i : Fin n => ϖ ^ (-d.getD i 0)) * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) * antiJ L n` using `by conv_rhs => rw [← Matrix.mul_one (_ * antiJ L n), ← h2, ← Matrix.mul_assoc, h1, Matrix.one_mul]`.

Rewrite using `[h3, ea, eb, eD, cT_mul, cT_mul]`. Establish `hJ : ∀ X : Matrix (Fin n) (Fin n) L, antiJ L n * (antiJ L n * X) = X` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, antiJ_sq, Matrix.one_mul]`. Simplify using `only [Matrix.mul_assoc, hJ]`.
-/
theorem hasDiv_dualLab : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (d : List ℤ) (g : GL (Fin n) L), (∀ x, Valued.v (σ x) = Valued.v x) → d.length = n → g ∈ GU σ n → HasDiv (intL L) d g → HasDiv (intL L) (dualLab d) g := by
  intro L _ _ σ n d g hσ hd hg ⟨ϖ, hϖ, a, ha, b, hb, hab⟩
  obtain ⟨a', ha', ea⟩ := exists_dual σ hσ ha
  obtain ⟨b', hb', eb⟩ := exists_dual σ hσ hb
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  refine ⟨σ ϖ, by rw [hσ, hϖ], a', ha', b', hb', ?_⟩
  have hg' : cT σ (g : Matrix (Fin n) (Fin n) L) * antiJ L n * (g : Matrix (Fin n) (Fin n) L) = antiJ L n := hg
  have eD : Matrix.diagonal (fun i : Fin n => σ ϖ ^ (dualLab d).getD i 0) =
      antiJ L n * cT σ (Matrix.diagonal (fun i : Fin n => ϖ ^ (-d.getD i 0))) * antiJ L n := by
    ext i j
    rw [mul_antiJ, antiJ_mul]
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply, Fin.rev_inj]
    by_cases h : i = j
    · subst h
      simp only [if_true]
      rw [getD_dualLab d hd, map_zpow₀]
    · rw [if_neg h, if_neg (Ne.symm h), map_zero]
  have hDD : Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i 0) *
      Matrix.diagonal (fun i : Fin n => ϖ ^ (-d.getD i 0)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero]
  have hinv : (g : Matrix (Fin n) (Fin n) L) * (((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      Matrix.diagonal (fun i : Fin n => ϖ ^ (-d.getD i 0)) * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) = 1 := by
    rw [hab]
    calc _ = (a : Matrix (Fin n) (Fin n) L) * (Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i 0) *
        ((b : Matrix (Fin n) (Fin n) L) * ((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) *
        Matrix.diagonal (fun i : Fin n => ϖ ^ (-d.getD i 0))) *
        ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Units.mul_inv, Matrix.mul_one, hDD, Matrix.mul_one, Units.mul_inv]
  have h1 := dual_mul σ _ _ hinv
  have h2 : antiJ L n * cT σ (g : Matrix (Fin n) (Fin n) L) * antiJ L n * (g : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ _), hg', antiJ_sq]
  have h3 : (g : Matrix (Fin n) (Fin n) L) = antiJ L n * cT σ (((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      Matrix.diagonal (fun i : Fin n => ϖ ^ (-d.getD i 0)) * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) *
      antiJ L n := by
    conv_rhs => rw [← Matrix.mul_one (_ * antiJ L n), ← h2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [h3, ea, eb, eD, cT_mul, cT_mul]
  have hJ : ∀ X : Matrix (Fin n) (Fin n) L, antiJ L n * (antiJ L n * X) = X := fun X => by
    rw [← Matrix.mul_assoc, antiJ_sq, Matrix.one_mul]
  simp only [Matrix.mul_assoc, hJ]

end GlobalTheory.DualDivU
