import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

open AlgebraicGeometry CategoryTheory

def locSub {F : Type} [Field F] (R : Subring F) (a : F) : Subring F :=
  Subring.closure ((R : Set F) ∪ {a⁻¹})

/- English proof (translation)
Introduce `_ h` and use `Subring.subset_closure (Or.inl h)`.
-/
theorem le_locSub {F : Type} [Field F] (R : Subring F) (a : F) : R ≤ locSub R a :=
  fun _ h => Subring.subset_closure (Or.inl h)

/- English proof (translation)
The claim follows from `Subring.subset_closure (Or.inr rfl)`.
-/
theorem inv_mem_locSub {F : Type} [Field F] (R : Subring F) (a : F) : a⁻¹ ∈ locSub R a :=
  Subring.subset_closure (Or.inr rfl)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hb`. Proceed by induction on `hb using Subring.closure_induction with`. Consider the case `mem x hx`. Break down `hx with hx | hx` into its components or cases.

Conclude with `⟨0, by simpa using hx⟩`. Rewrite using `[Set.mem_singleton_iff.1 hx]`. Conclude with `⟨1, by simpa [h0] using R.one_mem⟩`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `one => exact ⟨0, by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨k, hk⟩` from `hx`. Take `⟨l, hl⟩` from `hy`. Use `⟨k + l, ?_⟩` and prove the remaining obligations. Establish `e : a ^ (k + l) * (x + y) = a ^ l * (a ^ k * x) + a ^ k * (a ^ l * y)` using `by ring`.

Rewrite using `[e]`. Conclude with `R.add_mem (R.mul_mem (R.pow_mem ha _) hk) (R.mul_mem (R.pow_mem ha _) hl)`. Consider the case `neg x _ hx`. Take `⟨k, hk⟩` from `hx`. Conclude with `⟨k, by simpa using R.neg_mem hk⟩`.

Consider the case `mul x y _ _ hx hy`. Take `⟨k, hk⟩` from `hx`. Take `⟨l, hl⟩` from `hy`. Use `⟨k + l, ?_⟩` and prove the remaining obligations. Establish `e : a ^ (k + l) * (x * y) = (a ^ k * x) * (a ^ l * y)` using `by ring`.

Rewrite using `[e]`. Conclude with `R.mul_mem hk hl`. Introduce and unpack `⟨k, hk⟩`. Establish `e : b = (a⁻¹) ^ k * (a ^ k * b)`. Rewrite using `[inv_pow, ← _root_.mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ h0), _root_.one_mul]`.

Rewrite using `[e]`. Conclude with `(locSub R a).mul_mem ((locSub R a).pow_mem (inv_mem_locSub R a) _) (le_locSub R a hk)`.
-/
theorem mem_locSub_iff {F : Type} [Field F] {R : Subring F} {a : F} (ha : a ∈ R) (h0 : a ≠ 0) (b : F) :
    b ∈ locSub R a ↔ ∃ k : ℕ, a ^ k * b ∈ R := by
  constructor
  · intro hb
    induction hb using Subring.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact ⟨0, by simpa using hx⟩
      · rw [Set.mem_singleton_iff.1 hx]
        exact ⟨1, by simpa [h0] using R.one_mem⟩
    | zero => exact ⟨0, by simp⟩
    | one => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨k, hk⟩ := hx
      obtain ⟨l, hl⟩ := hy
      refine ⟨k + l, ?_⟩
      have e : a ^ (k + l) * (x + y) = a ^ l * (a ^ k * x) + a ^ k * (a ^ l * y) := by ring
      rw [e]
      exact R.add_mem (R.mul_mem (R.pow_mem ha _) hk) (R.mul_mem (R.pow_mem ha _) hl)
    | neg x _ hx =>
      obtain ⟨k, hk⟩ := hx
      exact ⟨k, by simpa using R.neg_mem hk⟩
    | mul x y _ _ hx hy =>
      obtain ⟨k, hk⟩ := hx
      obtain ⟨l, hl⟩ := hy
      refine ⟨k + l, ?_⟩
      have e : a ^ (k + l) * (x * y) = (a ^ k * x) * (a ^ l * y) := by ring
      rw [e]
      exact R.mul_mem hk hl
  · rintro ⟨k, hk⟩
    have e : b = (a⁻¹) ^ k * (a ^ k * b) := by
      rw [inv_pow, ← _root_.mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ h0), _root_.one_mul]
    rw [e]
    exact (locSub R a).mul_mem ((locSub R a).pow_mem (inv_mem_locSub R a) _) (le_locSub R a hk)

structure IsPiece {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens)
    (R : Subring Ω) : Prop where
  affine : IsAffineOpen U
  spec : ∀ q : X, q ∈ U → genPt ξ ⤳ q
  ring : ∀ a : Ω, a ∈ R ↔ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q

def stepMinor {F : Type} [CommRing F] {n r : ℕ} (A : Matrix (Fin n) (Fin r) F) (i : Fin r)
    (J : Fin ((i : ℕ) + 1) → Fin n) : F :=
  (A.submatrix J (Fin.castLE i.2)).det

variable {Ω : Type} [Field Ω] {S : Type} {r n : S → ℕ}

def flagB (M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω) (T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (s : S) :
    Matrix (Fin (n s)) (Fin (r s)) (GenField Ω r) :=
  (M s * T s).map (algebraMap Ω (GenField Ω r)) * genU Ω r s

def ratioRing (R : Subring Ω) (B : ∀ s, Matrix (Fin (n s)) (Fin (r s)) (GenField Ω r))
    (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) : Subring (GenField Ω r) :=
  Subring.closure (((R.map (algebraMap Ω (GenField Ω r)) : Subring _) : Set (GenField Ω r)) ∪
    {a | ∃ (q : Σ s, Fin (r s)) (J' : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)),
      a = stepMinor (B q.1) q.2 J' / stepMinor (B q.1) q.2 (J q)})

def chartSub {F : Type} [Field F] {κ : Type} (x : κ → F) (c : κ) : Subring F :=
  (Algebra.adjoin ℤ (Set.range fun j => x j / x c)).toSubring

/- English proof (translation)
Unfold `stepMinor`. Rewrite using `[Matrix.submatrix_smul]`. Simplify using `[Matrix.det_smul]`.
-/
theorem stepMinor_smul {F : Type} [CommRing F] {n r : ℕ} (b : F) (A : Matrix (Fin n) (Fin r) F) (i : Fin r)
    (J : Fin ((i : ℕ) + 1) → Fin n) : stepMinor (b • A) i J = b ^ ((i : ℕ) + 1) * stepMinor A i J := by
  unfold stepMinor
  rw [Matrix.submatrix_smul]
  simp [Matrix.det_smul]

/- English proof (translation)
Unfold `flagMat flagB`. Rewrite using `[← Matrix.smul_mul]`. Use `congr 1`. Use extensionality with `j l`. Simplify using `only [Matrix.of_apply, Matrix.smul_apply, Matrix.map_apply, h, map_mul, map_pow, smul_eq_mul]`.
-/
theorem flagMat_eq {E : Type} [AddCommGroup E] [Module Ω E] {m : S → ℕ}
    {φ : ∀ s, Fin (n s) → Module.Dual Ω E} {cc : ∀ s, Fin (r s) → E}
    {M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω} {T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω} {a : Ω}
    (h : ∀ s j l, φ s j (cc s l) = a ^ m s * (M s * T s) j l) (s : S) :
    flagMat φ cc s = (algebraMap Ω (GenField Ω r) a ^ m s) • flagB M T s := by
  unfold flagMat flagB
  rw [← Matrix.smul_mul]
  congr 1
  ext j l
  simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.map_apply, h, map_mul, map_pow, smul_eq_mul]

/- English proof (translation)
Unfold `flagCoord`. Use `congr 1`. Use `Finset.prod_congr rfl fun q _ => ?_` and prove the remaining obligations. Use `stepMinor_smul (algebraMap Ω (GenField Ω r) a ^ m q.1) (flagB M T q.1) q.2 (J q)` as an intermediate fact. Rewrite using `[← this, ← flagMat_eq h q.1]`.

Both sides reduce to the same expression.
-/
theorem flagCoord_eq [Fintype S] {E : Type} [AddCommGroup E] [Module Ω E] {κ : Type} (x : κ → Ω) {m : S → ℕ}
    {φ : ∀ s, Fin (n s) → Module.Dual Ω E} {cc : ∀ s, Fin (r s) → E}
    {M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω} {T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω} {a : Ω}
    (h : ∀ s j l, φ s j (cc s l) = a ^ m s * (M s * T s) j l) (k : κ)
    (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) :
    flagCoord κ x φ cc (k, J) = algebraMap Ω (GenField Ω r) (x k) *
      ∏ q : (Σ s, Fin (r s)), ((algebraMap Ω (GenField Ω r) a ^ m q.1) ^ ((q.2 : ℕ) + 1) *
        stepMinor (flagB M T q.1) q.2 (J q)) := by
  unfold flagCoord
  congr 1
  refine Finset.prod_congr rfl fun q _ => ?_
  have := stepMinor_smul (algebraMap Ω (GenField Ω r) a ^ m q.1) (flagB M T q.1) q.2 (J q)
  rw [← this, ← flagMat_eq h q.1]
  rfl

/- English proof (translation)
Establish `h1 : ∏ q', f q' (Function.update J q b q') = f q b * ∏ q' ∈ Finset.univ.erase q, f q' (J q')`. Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q)]`. Simplify using `only [Function.update_self]`. Use `congr 1`. Use `Finset.prod_congr rfl fun q' hq' => ?_` and prove the remaining obligations.

Rewrite using `[Function.update_of_ne (Finset.ne_of_mem_erase hq')]`. Establish `h2 : ∏ q', f q' (J q') = f q (J q) * ∏ q' ∈ Finset.univ.erase q, f q' (J q')` using `(Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q)).symm`. Establish `h3 : ∏ q' ∈ Finset.univ.erase q, f q' (J q') ≠ 0` using `Finset.prod_ne_zero_iff.2 fun q' _ => h q'`. Rewrite using `[h1, h2]`. Clear denominators, using `[h q, h3]` for the nonvanishing conditions.
-/
theorem prod_update_div {ι : Type} [Fintype ι] [DecidableEq ι] {β : ι → Type} {F : Type} [Field F]
    (f : ∀ q, β q → F) (J : ∀ q, β q) (h : ∀ q, f q (J q) ≠ 0) (q : ι) (b : β q) :
    (∏ q', f q' (Function.update J q b q')) / (∏ q', f q' (J q')) = f q b / f q (J q) := by
  have h1 : ∏ q', f q' (Function.update J q b q') =
      f q b * ∏ q' ∈ Finset.univ.erase q, f q' (J q') := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q)]
    simp only [Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun q' hq' => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hq')]
  have h2 : ∏ q', f q' (J q') = f q (J q) * ∏ q' ∈ Finset.univ.erase q, f q' (J q') :=
    (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q)).symm
  have h3 : ∏ q' ∈ Finset.univ.erase q, f q' (J q') ≠ 0 := Finset.prod_ne_zero_iff.2 fun q' _ => h q'
  rw [h1, h2]
  field_simp [h q, h3]

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
