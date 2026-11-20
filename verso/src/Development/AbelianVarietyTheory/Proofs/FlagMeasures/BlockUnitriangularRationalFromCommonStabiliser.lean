import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianStabiliserRationalUnitriangularPairsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.RatPat

noncomputable def rhoL {R : Type} [CommRing R] : List (Rˣ × ℕ+) → ℕ → ℕ
  | [], a => a
  | (_, s) :: bs, a => if a < (s : ℕ) then (s : ℕ) - 1 - a else (s : ℕ) + rhoL bs (a - s)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem sum_cons' {R : Type} [CommRing R] (t : Rˣ) (s : ℕ+) (bs : List (Rˣ × ℕ+)) :
    (((t, s) :: bs).map (fun b => (b.2 : ℕ))).sum = (s : ℕ) + (bs.map (fun b => (b.2 : ℕ))).sum := by
  simp

/- English proof (translation)
Proceed by induction on `bs generalizing a with`. Consider the case `nil => simp at ha`. Consider the case `cons b bs ih`. Take `⟨t, s⟩` from `b`. Rewrite `ha`, the goal using `[sum_cons']`.

Simplify using `only [rhoL]`. Use `split_ifs with h`. Use linear arithmetic over natural numbers and integers. Use `ih (a - s) (by omega); omega` as an intermediate fact.
-/
theorem rhoL_lt {R : Type} [CommRing R] (bs : List (Rˣ × ℕ+)) (a : ℕ)
    (ha : a < (bs.map (fun b => (b.2 : ℕ))).sum) : rhoL bs a < (bs.map (fun b => (b.2 : ℕ))).sum := by
  induction bs generalizing a with
  | nil => simp at ha
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    rw [sum_cons'] at ha ⊢
    simp only [rhoL]
    split_ifs with h
    · omega
    · have := ih (a - s) (by omega); omega

/- English proof (translation)
Proceed by induction on `bs generalizing a with`. Consider the case `nil => rfl`. Consider the case `cons b bs ih`. Take `⟨t, s⟩` from `b`. Rewrite `ha` using `[sum_cons']`.

Distinguish the cases in `h : a < (s : ℕ)`. Establish `e : rhoL ((t, s) :: bs) a = (s : ℕ) - 1 - a` using `by simp [rhoL, h]`. Rewrite using `[e]; simp only [rhoL]; rw [if_pos (by omega)]; omega`. Establish `e : rhoL ((t, s) :: bs) a = (s : ℕ) + rhoL bs (a - s)` using `by simp [rhoL, h]`. Rewrite using `[e]`.

Simplify using `only [rhoL]`. Rewrite using `[if_neg (by omega), Nat.add_sub_cancel_left, ih (a - s) (by omega)]; omega`.
-/
theorem rhoL_rhoL {R : Type} [CommRing R] (bs : List (Rˣ × ℕ+)) (a : ℕ)
    (ha : a < (bs.map (fun b => (b.2 : ℕ))).sum) : rhoL bs (rhoL bs a) = a := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    rw [sum_cons'] at ha
    by_cases h : a < (s : ℕ)
    · have e : rhoL ((t, s) :: bs) a = (s : ℕ) - 1 - a := by simp [rhoL, h]
      rw [e]; simp only [rhoL]; rw [if_pos (by omega)]; omega
    · have e : rhoL ((t, s) :: bs) a = (s : ℕ) + rhoL bs (a - s) := by simp [rhoL, h]
      rw [e]; simp only [rhoL]
      rw [if_neg (by omega), Nat.add_sub_cancel_left, ih (a - s) (by omega)]; omega

/- English proof (translation)
Proceed by induction on `bs generalizing a b with`. Consider the case `nil => simp at ha`. Consider the case `cons c bs ih`. Take `⟨t, s⟩` from `c`. Rewrite `ha` using `[sum_cons']`.

Simplify using `only [ptEntryL, rhoL]`. Distinguish the cases in `h1 : a < (s : ℕ)`. Rewrite using `[if_pos h1]`. Distinguish the cases in `h2 : b < (s : ℕ)`. Rewrite using `[if_pos ⟨h1, h2⟩] split_ifs with h3`.

Simplify using `only [ne_eq, Units.ne_zero, not_false_eq_true, true_iff]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [ne_eq, not_true_eq_false, false_iff]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg (fun h => h2 h.2), if_neg (fun h => by omega)]`.

Simplify using `only [ne_eq, not_true_eq_false, false_iff]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg h1, if_neg (fun h => h1 h.1)]`. Distinguish the cases in `h2 : (s : ℕ) ≤ b`. Rewrite using `[if_pos ⟨by omega, h2⟩, ih (a - s) (b - s) (by omega)]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg (fun h => h2 h.2)]`. Simplify using `only [ne_eq, not_true_eq_false, false_iff]`. Use linear arithmetic over natural numbers and integers.
-/
theorem entry_ne_zero_iff {R : Type} [CommRing R] [Nontrivial R] (bs : List (Rˣ × ℕ+)) (a b : ℕ)
    (ha : a < (bs.map (fun b => (b.2 : ℕ))).sum) :
    ptEntryL bs a b ≠ 0 ↔ b = rhoL bs a := by
  induction bs generalizing a b with
  | nil => simp at ha
  | cons c bs ih =>
    obtain ⟨t, s⟩ := c
    rw [sum_cons'] at ha
    simp only [ptEntryL, rhoL]
    by_cases h1 : a < (s : ℕ)
    · rw [if_pos h1]
      by_cases h2 : b < (s : ℕ)
      · rw [if_pos ⟨h1, h2⟩]
        split_ifs with h3
        · simp only [ne_eq, Units.ne_zero, not_false_eq_true, true_iff]; omega
        · simp only [ne_eq, not_true_eq_false, false_iff]; omega
      · rw [if_neg (fun h => h2 h.2), if_neg (fun h => by omega)]
        simp only [ne_eq, not_true_eq_false, false_iff]; omega
    · rw [if_neg h1, if_neg (fun h => h1 h.1)]
      by_cases h2 : (s : ℕ) ≤ b
      · rw [if_pos ⟨by omega, h2⟩, ih (a - s) (b - s) (by omega)]
        omega
      · rw [if_neg (fun h => h2 h.2)]
        simp only [ne_eq, not_true_eq_false, false_iff]; omega

/- English proof (translation)
Proceed by induction on `bs generalizing x y with`. Consider the case `nil => simp at hy`. Consider the case `cons c bs ih`. Take `⟨t, s⟩` from `c`. Rewrite `hy` using `[sum_cons']`.

Simplify using `only [rhoL] at hB ⊢`. Distinguish the cases in `h1 : y < (s : ℕ)`. Rewrite using `[if_pos h1, if_pos (by omega)]; omega`. Distinguish the cases in `h2 : x < (s : ℕ)`. It suffices to derive a contradiction.

Use `hB s h2 (by omega) fun a ha => ?_` and prove the remaining obligations. Rewrite using `[if_pos ha]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg h1, if_neg h2]`. Use `ih (x - s) (y - s) (by omega) (by omega) fun l hl1 hl2 hcl => by` as an intermediate fact.

Use `hB (s + l) (by omega) (by omega) fun a ha => ?_` and prove the remaining obligations. Distinguish the cases in `h : a < (s : ℕ)`. Rewrite using `[if_pos h]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg h]; have := hcl (a - s) (by omega); omega`.

Use linear arithmetic over natural numbers and integers.
-/
theorem rhoL_rev {R : Type} [CommRing R] (bs : List (Rˣ × ℕ+)) (x y : ℕ) (hxy : x < y)
    (hy : y < (bs.map (fun b => (b.2 : ℕ))).sum)
    (hB : ∀ l : ℕ, x < l → l ≤ y → ¬ ∀ a, a < l → rhoL bs a < l) : rhoL bs y < rhoL bs x := by
  induction bs generalizing x y with
  | nil => simp at hy
  | cons c bs ih =>
    obtain ⟨t, s⟩ := c
    rw [sum_cons'] at hy
    simp only [rhoL] at hB ⊢
    by_cases h1 : y < (s : ℕ)
    · rw [if_pos h1, if_pos (by omega)]; omega
    · by_cases h2 : x < (s : ℕ)
      · exfalso
        refine hB s h2 (by omega) fun a ha => ?_
        rw [if_pos ha]; omega
      · rw [if_neg h1, if_neg h2]
        have := ih (x - s) (y - s) (by omega) (by omega) fun l hl1 hl2 hcl => by
          refine hB (s + l) (by omega) (by omega) fun a ha => ?_
          by_cases h : a < (s : ℕ)
          · rw [if_pos h]; omega
          · rw [if_neg h]; have := hcl (a - s) (by omega); omega
        omega

/- English proof (translation)
Establish `hn : ∀ a : Fin n, (a : ℕ) < (w.blocks.map (fun b => (b.2 : ℕ))).sum` using `fun a => by rw [w.size]; exact a.2`. Set `ρ : Fin n → Fin n` to `fun a => ⟨rhoL w.blocks a, by have := rhoL_lt _ _ (hn a); rwa [w.size] at this⟩`. Use `⟨ρ, fun a => Fin.ext (rhoL_rhoL _ _ (hn a)), fun a b => ?_, fun x y hxy hB => ?_⟩` and prove the remaining obligations. Use `show ptEntryL w.blocks a b ≠ 0 ↔ b = ρ a`. Rewrite using `[entry_ne_zero_iff _ _ _ (hn a), Fin.ext_iff]`.

Use `show rhoL w.blocks y < rhoL w.blocks x`. Use `rhoL_rev _ _ _ hxy (hn y) fun l h1 h2 hcl => hB l h1 h2 fun a ha => hcl a ha` and prove the remaining obligations.
-/
theorem pt_shape {R : Type} [CommRing R] [Nontrivial R] {n : ℕ} (w : Pt R n) :
    ∃ ρ : Fin n → Fin n, Function.Involutive ρ ∧ (∀ a b, w.mat a b ≠ 0 ↔ b = ρ a) ∧
      ∀ x y : Fin n, x < y → (∀ l : ℕ, (x : ℕ) < l → l ≤ (y : ℕ) →
        ¬ ∀ a : Fin n, (a : ℕ) < l → ((ρ a : Fin n) : ℕ) < l) → ρ y < ρ x := by
  have hn : ∀ a : Fin n, (a : ℕ) < (w.blocks.map (fun b => (b.2 : ℕ))).sum := fun a => by rw [w.size]; exact a.2
  let ρ : Fin n → Fin n := fun a => ⟨rhoL w.blocks a, by have := rhoL_lt _ _ (hn a); rwa [w.size] at this⟩
  refine ⟨ρ, fun a => Fin.ext (rhoL_rhoL _ _ (hn a)), fun a b => ?_, fun x y hxy hB => ?_⟩
  · show ptEntryL w.blocks a b ≠ 0 ↔ b = ρ a
    rw [entry_ne_zero_iff _ _ _ (hn a), Fin.ext_iff]
  · show rhoL w.blocks y < rhoL w.blocks x
    refine rhoL_rev _ _ _ hxy (hn y) fun l h1 h2 hcl => hB l h1 h2 fun a ha => hcl a ha

end GlobalTheory.HL.RatPat

namespace GlobalTheory.HL.RatPat

/- English proof (translation)
Rewrite using `[Matrix.det_apply, Finset.sum_eq_single σ⁻¹]`. Establish `hp : ∏ i, M ((σ⁻¹ : Equiv.Perm (Fin m)) i) i ≠ 0`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `i _`. Rewrite using `[hM]`.

Simplify using the standard rewrite rules. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ⁻¹) with h | h <;> rw [h] <;> simpa using hp`. Introduce `τ _ hτ`. Establish `: ∃ i, σ (τ i) ≠ i`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Apply `hτ` to reduce the goal to its premises. Use `Equiv.ext fun i => ?_` and prove the remaining obligations. Use `show τ i = σ⁻¹ i`. Rewrite using `[Equiv.Perm.eq_inv_iff_eq]`.

Conclude with `h i`. Take `⟨i, hi⟩` from `this`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ i), smul_zero]`. Assume the negation of the conclusion as `h`. Conclude with `hi ((hM _ _).1 h).symm`.

Simplify using the standard rewrite rules.
-/
theorem det_ne_zero_of_monomial {K : Type} [Field K] {m : ℕ} (M : Matrix (Fin m) (Fin m) K)
    (σ : Equiv.Perm (Fin m)) (hM : ∀ a b, M a b ≠ 0 ↔ b = σ a) : M.det ≠ 0 := by
  rw [Matrix.det_apply, Finset.sum_eq_single σ⁻¹]
  · have hp : ∏ i, M ((σ⁻¹ : Equiv.Perm (Fin m)) i) i ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro i _
      rw [hM]
      simp
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ⁻¹) with h | h <;> rw [h] <;> simpa using hp
  · intro τ _ hτ
    have : ∃ i, σ (τ i) ≠ i := by
      by_contra h
      push_neg at h
      apply hτ
      refine Equiv.ext fun i => ?_
      show τ i = σ⁻¹ i
      rw [Equiv.Perm.eq_inv_iff_eq]
      exact h i
    obtain ⟨i, hi⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ i), smul_zero]
    by_contra h
    exact hi ((hM _ _).1 h).symm
  · simp

/- English proof (translation)
Establish `hZd : ∀ a, Z a (ρ a) ≠ 0` using `fun a => (hZ a _).2 rfl`. Establish `hZd' : ∀ b, Z (ρ b) b ≠ 0` using `fun b => (hZ _ _).2 (hρ b).symm`. Set `M : Matrix (Fin n) (Fin n) K` to `fun a b => u (ρ a) (ρ b) * Z (ρ b) b / Z (ρ a) a`. Establish `hMup : M.BlockTriangular id`. Introduce `i j hij`.

Simplify using `only [id] at hij`. Use `show u (ρ i) (ρ j) * Z (ρ j) j / Z (ρ i) i = 0`. Rewrite using `[hu0 (ρ i) (ρ j) (fun h => (ne_of_gt hij) (hρ.injective h)) ?_]`. Simplify using the standard rewrite rules. Introduce and unpack `⟨h1, h2⟩`.

Use `hB _ _ h1 h2` as an intermediate fact. Rewrite `this` using `[hρ, hρ]`. Conclude with `absurd hij (not_lt.2 this.le)`. Establish `hMd : ∀ i, M i i = 1`. Introduce `i`.

Use `show u (ρ i) (ρ i) * Z (ρ i) i / Z (ρ i) i = 1`. Rewrite using `[hu1, one_mul, div_self (hZd' i)]`. Establish `hdet : M.det = 1`. Rewrite using `[Matrix.det_of_upperTriangular hMup]`. Simplify using `[hMd]`.

Establish `hZM : Z * M = u * Z`. Use extensionality with `a b`. Rewrite using `[Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (ρ a), Finset.sum_eq_single (ρ b)]`. Use `show Z a (ρ a) * (u (ρ (ρ a)) (ρ b) * Z (ρ b) b / Z (ρ (ρ a)) (ρ a)) = u a (ρ b) * Z (ρ b) b`. Rewrite using `[hρ a]`.

Clear denominators, using `[hZd a]` for the nonvanishing conditions. Introduce `c _ hc`. Establish `: Z c b = 0`. Assume the negation of the conclusion as `h`. Apply `hc` to reduce the goal to its premises.

Rewrite using `[(hZ c b).1 h, hρ]`. Rewrite using `[this, mul_zero]`. Simplify using the standard rewrite rules. Introduce `c _ hc`. Establish `: Z a c = 0`.

Assume the negation of the conclusion as `h`. Conclude with `hc ((hZ a c).1 h)`. Rewrite using `[this, zero_mul]`. Simplify using the standard rewrite rules. Use `haveI : Invertible M := Matrix.invertibleOfIsUnitDet M (by rw [hdet]; exact isUnit_one)`.

Use `⟨M⁻¹, ⟨fun i j hij => Matrix.blockTriangular_inv_of_blockTriangular hMup hij, fun i => ?_⟩, ?_⟩` and prove the remaining obligations. Establish `h1 : (M⁻¹ * M) i i = 1` using `by rw [Matrix.inv_mul_of_invertible]; simp`. Rewrite `h1` using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Rewrite `h1` using `[hMd, mul_one]`. Then use the resulting hypothesis. Introduce `c _ hc`.

Break down `lt_or_gt_of_ne hc with h | h` into its components or cases. Rewrite using `[Matrix.blockTriangular_inv_of_blockTriangular hMup h, zero_mul]`. Rewrite using `[hMup h, mul_zero]`. Simplify using the standard rewrite rules. Rewrite using `[← hZM, Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.mul_one]`.
-/
theorem exists_upper {K : Type} [Field K] {n : ℕ} (Z u : Matrix (Fin n) (Fin n) K) (ρ : Fin n → Fin n)
    (B : Fin n → Fin n → Prop) (hρ : Function.Involutive ρ) (hZ : ∀ a b, Z a b ≠ 0 ↔ b = ρ a)
    (hB : ∀ x y, x < y → B x y → ρ y < ρ x) (hu1 : ∀ a, u a a = 1)
    (hu0 : ∀ a b, a ≠ b → ¬ (b < a ∧ B b a) → u a b = 0) :
    ∃ s : Matrix (Fin n) (Fin n) K, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧ u * Z * s = Z := by
  have hZd : ∀ a, Z a (ρ a) ≠ 0 := fun a => (hZ a _).2 rfl
  have hZd' : ∀ b, Z (ρ b) b ≠ 0 := fun b => (hZ _ _).2 (hρ b).symm
  let M : Matrix (Fin n) (Fin n) K := fun a b => u (ρ a) (ρ b) * Z (ρ b) b / Z (ρ a) a
  have hMup : M.BlockTriangular id := by
    intro i j hij
    simp only [id] at hij
    show u (ρ i) (ρ j) * Z (ρ j) j / Z (ρ i) i = 0
    rw [hu0 (ρ i) (ρ j) (fun h => (ne_of_gt hij) (hρ.injective h)) ?_]
    · simp
    · rintro ⟨h1, h2⟩
      have := hB _ _ h1 h2
      rw [hρ, hρ] at this
      exact absurd hij (not_lt.2 this.le)
  have hMd : ∀ i, M i i = 1 := by
    intro i
    show u (ρ i) (ρ i) * Z (ρ i) i / Z (ρ i) i = 1
    rw [hu1, one_mul, div_self (hZd' i)]
  have hdet : M.det = 1 := by
    rw [Matrix.det_of_upperTriangular hMup]
    simp [hMd]
  have hZM : Z * M = u * Z := by
    ext a b
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (ρ a), Finset.sum_eq_single (ρ b)]
    · show Z a (ρ a) * (u (ρ (ρ a)) (ρ b) * Z (ρ b) b / Z (ρ (ρ a)) (ρ a)) = u a (ρ b) * Z (ρ b) b
      rw [hρ a]
      field_simp [hZd a]
    · intro c _ hc
      have : Z c b = 0 := by
        by_contra h
        apply hc
        rw [(hZ c b).1 h, hρ]
      rw [this, mul_zero]
    · simp
    · intro c _ hc
      have : Z a c = 0 := by
        by_contra h
        exact hc ((hZ a c).1 h)
      rw [this, zero_mul]
    · simp
  haveI : Invertible M := Matrix.invertibleOfIsUnitDet M (by rw [hdet]; exact isUnit_one)
  refine ⟨M⁻¹, ⟨fun i j hij => Matrix.blockTriangular_inv_of_blockTriangular hMup hij, fun i => ?_⟩, ?_⟩
  · have h1 : (M⁻¹ * M) i i = 1 := by rw [Matrix.inv_mul_of_invertible]; simp
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
    · rwa [hMd, mul_one] at h1
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [Matrix.blockTriangular_inv_of_blockTriangular hMup h, zero_mul]
      · rw [hMup h, mul_zero]
    · simp
  · rw [← hZM, Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.mul_one]

end GlobalTheory.HL.RatPat

namespace GlobalTheory.HL.RatPat

/- English proof (translation)
Unfold `hf`. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul, AlgEquiv.commutes, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hf_smul {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (α β : F) (x y : Fin n → E) :
    hf L Hm (algebraMap F E α • x) (algebraMap F E β • y) =
      algebraMap F E α * algebraMap F E β * hf L Hm x y := by
  unfold hf
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, AlgEquiv.commutes, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Take `⟨M, hM⟩` from `Ideal.exists_maximal (𝓞 F)`. Conclude with `⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩⟩`.
-/
theorem nonempty_places (F : Type) [Field F] [NumberField F] : Nonempty (HeightOneSpectrum (𝓞 F)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ sig A r k G t ht`. Take `⟨p⟩` from `nonempty_places F`. Use `haveI : Nontrivial (A.loc p).Ep := Module.nontrivial_of_finrank_pos (R := (A.loc p).Fp) (by rw [(A.loc p).rank]; norm_num)`. Establish `hinj : Function.Injective (A.loc p).ιE` using `(A.loc p).ιE.injective`. Establish `hZ : ∀ a b, (A.loc p).ιE (G.Zh a b) = algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (b : ℕ))) * algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (a : ℕ))) * ((G.S p).w.mat a b * (-1) ^ (r - (b : ℕ)))`.

Introduce `a b`. Establish `hform` using `(GlobalTheory.HL.RatExt.rational_extend A (k + 2 * r + 1) p).2.2.2.2.1 G.Hm (G.f' b) (G.f a)`. Establish `e1 : G.Zh a b = ∑ i, ∑ j, G.f' b i * G.Hm i j * sig (G.f a j)` using `rfl`. Rewrite using `[e1, ← hform, ← G.Hm_eq p, ← G.f_eq p a, ← G.f'_eq p b, hf_smul, ← (G.S p).relevant]`. Establish `hne : ∀ a b, G.Zh a b ≠ 0 ↔ (G.S p).w.mat a b ≠ 0`.

Introduce `a b`. Establish `hu : IsUnit (algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (b : ℕ))) * algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (a : ℕ))))` using `(((G.c p).isUnit.pow _).map _).mul (((G.c p).isUnit.pow _).map _)`. Establish `hs : IsUnit ((-1 : (A.loc p).Ep) ^ (r - (b : ℕ)))` using `(isUnit_one.neg).pow _`. Rewrite using `[ne_eq, ne_eq, ← map_eq_zero_iff _ hinj, hZ, hu.mul_right_eq_zero, hs.mul_left_eq_zero]`. Take `⟨ρ, hρ, hρw, hρB⟩` from `pt_shape (G.S p).w`.

Establish `hZρ : ∀ a b, G.Zh a b ≠ 0 ↔ b = ρ a` using `fun a b => (hne a b).trans (hρw a b)`. Establish `hD : ∀ l : Fin (r + 2), (∀ a : Fin (r + 1), (a : ℕ) < l → ((ρ a : Fin (r + 1)) : ℕ) < l) → G.D l ≠ 0`. Introduce `l hl`. Set `e : Fin l → Fin (r + 1)` to `Fin.castLE (Nat.lt_succ_iff.mp l.2)`. Set `σ' : Fin l → Fin l` to `fun i => ⟨ρ (e i), hl (e i) i.2⟩`.

Establish `he : ∀ i, ρ (e (σ' i)) = e i` using `fun i => by show ρ (ρ (e i)) = e i`. Conclude with `hρ _`. Establish `hσ : Function.Involutive σ'` using `fun i => Fin.ext (by show ((ρ (e (σ' i)) : Fin (r + 1)) : ℕ) = i`. Rewrite using `[he]`. Use the proof step `rfl)`.

Use `det_ne_zero_of_monomial _ hσ.toPerm fun a b => ?_` and prove the remaining obligations. Use `show G.Zh (e a) (e b) ≠ 0 ↔ b = σ' a`. Rewrite using `[hZρ]`. Prove the components needed by the constructor for the conclusion. Introduce `h; exact Fin.ext (by rw [show (b : ℕ) = (e b : ℕ) from rfl, h])`.

Introduce `h`. Substitute `h` using the available equality. Both sides reduce to the same expression. Take `⟨s', hs'up, hs'⟩` from `exists_upper G.Zh (t.map sig).transpose ρ (fun x y => ∀ l : Fin (r + 2), (x : ℕ) < l → (l : ℕ) ≤ (y : ℕ) → G.D l = 0) hρ hZρ (fun x y hxy hB => hρB x y hxy fun l h1 h2 hcl => hD ⟨l, by have := y.2; omega⟩ hcl (hB ⟨l, by have := y.2; omega⟩ h1 h2)) (fun a => by simp [ht a a (fun h …`. Simplify using `only [Matrix.transpose_apply, Matrix.map_apply]`.

Rewrite using `[ht b a hB, if_neg (Ne.symm hab), map_zero])`. Establish `htup : (∀ i j, j < i → t i j = 0) ∧ ∀ i, t i i = 1` using `⟨fun i j hij => by rw [ht i j (fun h => lt_asymm h.1 hij), if_neg (ne_of_gt hij)], fun i => by rw [ht i i (fun h => lt_irrefl _ h.1), if_pos rfl]⟩`. Take `⟨h, hh, hf1, -⟩` from `(GlobalTheory.T.hermitianStabiliser_rational_unitriangular_pairs A r k G t s' htup hs'up).1 hs'`. Conclude with `⟨h, hh, hf1⟩`.
-/
theorem main : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
    (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ t : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
    (∀ i j, ¬ (i < j ∧ ∀ l : Fin (r + 2), ((i : Fin (r + 1)) : ℕ) < l → (l : ℕ) ≤ ((j : Fin (r + 1)) : ℕ) →
      G.D l = 0) → t i j = if i = j then 1 else 0) →
    ∃ g ∈ G.St, ∀ j, g (G.f j) = ∑ i, t i j • G.f i := by
  intro F E _ _ _ _ _ sig A r k G t ht
  obtain ⟨p⟩ := nonempty_places F
  haveI : Nontrivial (A.loc p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (A.loc p).Fp) (by rw [(A.loc p).rank]; norm_num)
  have hinj : Function.Injective (A.loc p).ιE := (A.loc p).ιE.injective

  have hZ : ∀ a b, (A.loc p).ιE (G.Zh a b) =
      algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (b : ℕ))) *
      algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (a : ℕ))) *
      ((G.S p).w.mat a b * (-1) ^ (r - (b : ℕ))) := by
    intro a b
    have hform := (GlobalTheory.HL.RatExt.rational_extend A (k + 2 * r + 1) p).2.2.2.2.1 G.Hm (G.f' b) (G.f a)
    have e1 : G.Zh a b = ∑ i, ∑ j, G.f' b i * G.Hm i j * sig (G.f a j) := rfl
    rw [e1, ← hform, ← G.Hm_eq p, ← G.f_eq p a, ← G.f'_eq p b, hf_smul, ← (G.S p).relevant]
  have hne : ∀ a b, G.Zh a b ≠ 0 ↔ (G.S p).w.mat a b ≠ 0 := by
    intro a b
    have hu : IsUnit (algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (b : ℕ))) *
        algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (a : ℕ)))) :=
      (((G.c p).isUnit.pow _).map _).mul (((G.c p).isUnit.pow _).map _)
    have hs : IsUnit ((-1 : (A.loc p).Ep) ^ (r - (b : ℕ))) := (isUnit_one.neg).pow _
    rw [ne_eq, ne_eq, ← map_eq_zero_iff _ hinj, hZ, hu.mul_right_eq_zero, hs.mul_left_eq_zero]
  obtain ⟨ρ, hρ, hρw, hρB⟩ := pt_shape (G.S p).w
  have hZρ : ∀ a b, G.Zh a b ≠ 0 ↔ b = ρ a := fun a b => (hne a b).trans (hρw a b)

  have hD : ∀ l : Fin (r + 2), (∀ a : Fin (r + 1), (a : ℕ) < l → ((ρ a : Fin (r + 1)) : ℕ) < l) → G.D l ≠ 0 := by
    intro l hl
    let e : Fin l → Fin (r + 1) := Fin.castLE (Nat.lt_succ_iff.mp l.2)
    let σ' : Fin l → Fin l := fun i => ⟨ρ (e i), hl (e i) i.2⟩
    have he : ∀ i, ρ (e (σ' i)) = e i := fun i => by
      show ρ (ρ (e i)) = e i
      exact hρ _
    have hσ : Function.Involutive σ' := fun i => Fin.ext (by
      show ((ρ (e (σ' i)) : Fin (r + 1)) : ℕ) = i
      rw [he]; rfl)
    refine det_ne_zero_of_monomial _ hσ.toPerm fun a b => ?_
    show G.Zh (e a) (e b) ≠ 0 ↔ b = σ' a
    rw [hZρ]
    constructor
    · intro h; exact Fin.ext (by rw [show (b : ℕ) = (e b : ℕ) from rfl, h])
    · intro h; subst h; rfl
  obtain ⟨s', hs'up, hs'⟩ := exists_upper G.Zh (t.map sig).transpose ρ
    (fun x y => ∀ l : Fin (r + 2), (x : ℕ) < l → (l : ℕ) ≤ (y : ℕ) → G.D l = 0) hρ hZρ
    (fun x y hxy hB => hρB x y hxy fun l h1 h2 hcl =>
      hD ⟨l, by have := y.2; omega⟩ hcl (hB ⟨l, by have := y.2; omega⟩ h1 h2))
    (fun a => by simp [ht a a (fun h => lt_irrefl _ h.1)])
    (fun a b hab hB => by
      simp only [Matrix.transpose_apply, Matrix.map_apply]
      rw [ht b a hB, if_neg (Ne.symm hab), map_zero])
  have htup : (∀ i j, j < i → t i j = 0) ∧ ∀ i, t i i = 1 :=
    ⟨fun i j hij => by rw [ht i j (fun h => lt_asymm h.1 hij), if_neg (ne_of_gt hij)],
      fun i => by rw [ht i i (fun h => lt_irrefl _ h.1), if_pos rfl]⟩
  obtain ⟨h, hh, hf1, -⟩ := (GlobalTheory.T.hermitianStabiliser_rational_unitriangular_pairs A r k G t s' htup hs'up).1 hs'
  exact ⟨h, hh, hf1⟩

end GlobalTheory.HL.RatPat
