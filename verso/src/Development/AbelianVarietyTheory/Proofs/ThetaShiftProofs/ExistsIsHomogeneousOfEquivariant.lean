import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.SectionOfLineBundleOne
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IrreducibleDetOfIsRelPrime

open MvPolynomial

namespace GlobalTheory.BorelAlg

/- English proof (translation)
Proceed by induction on `Q using MvPolynomial.induction_on' with`. Consider the case `monomial u r`. Establish `: eval₂Hom ((Polynomial.C : MvPolynomial σ L →+* _).comp C) (fun i => Polynomial.X * Polynomial.C (X i)) (monomial u r) = Polynomial.C (monomial u r) * Polynomial.X ^ u.degree`. Rewrite using `[eval₂Hom_monomial, monomial_eq, Finsupp.prod, Finsupp.prod, Finsupp.degree_apply]`. Simplify using `only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow, RingHom.comp_apply]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, Polynomial.coeff_C_mul_X_pow, homogeneousComponent_of_mem (isHomogeneous_monomial r rfl)]`. Consider the case `add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]`.
-/
theorem coeff_scale {σ L : Type*} [CommRing L] (Q : MvPolynomial σ L) (n : ℕ) :
    (eval₂Hom ((Polynomial.C : MvPolynomial σ L →+* _).comp C)
      (fun i => Polynomial.X * Polynomial.C (X i)) Q).coeff n = homogeneousComponent n Q := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial u r =>
    have : eval₂Hom ((Polynomial.C : MvPolynomial σ L →+* _).comp C)
        (fun i => Polynomial.X * Polynomial.C (X i)) (monomial u r) =
        Polynomial.C (monomial u r) * Polynomial.X ^ u.degree := by
      rw [eval₂Hom_monomial, monomial_eq, Finsupp.prod, Finsupp.prod, Finsupp.degree_apply]
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_mul, map_prod,
        map_pow, RingHom.comp_apply]
      ring
    rw [this, Polynomial.coeff_C_mul_X_pow,
      homogeneousComponent_of_mem (isHomogeneous_monomial r rfl)]
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]

/- English proof (translation)
Consider the cases of `k with`. Consider the case `zero => exact l.elim0`. Consider the case `succ n`. Take `rfl : l = Fin.last n` from `le_antisymm (Fin.le_last _) (hl _)`. Rewrite using `[RowDet.det_updateRow_single]`.

Conclude with `RowDet.minor_isRelPrime e he`.
-/
theorem minor_isRelPrime' {R σ : Type*} [CommRing R] [IsDomain R] {k : ℕ}
    (e : Fin k × Fin k → σ) (he : Function.Injective e) (l : Fin k) (hl : ∀ i, i ≤ l) :
    ((Matrix.of fun i j : Fin k => (X (e (i, j)) : MvPolynomial σ R)).updateRow l
      (Pi.single l 1)).det ≠ 0 ∧
    IsRelPrime ((Matrix.of fun i j : Fin k => (X (e (i, j)) : MvPolynomial σ R)).updateRow l
      (Pi.single l 1)).det
      (Matrix.of fun i j : Fin k => (X (e (i, j)) : MvPolynomial σ R)).det := by
  cases k with
  | zero => exact l.elim0
  | succ n =>
    obtain rfl : l = Fin.last n := le_antisymm (Fin.le_last _) (hl _)
    rw [RowDet.det_updateRow_single]
    exact RowDet.minor_isRelPrime e he

/- English proof (translation)
Consider the cases of `k with`. Consider the case `zero => exact absurd rfl hk`. Consider the case `succ n => exact RowDet.irreducible_det n e he`.
-/
theorem irreducible_det' {R σ : Type*} [CommRing R] [IsDomain R] {k : ℕ} (hk : k ≠ 0)
    (e : Fin k × Fin k → σ) (he : Function.Injective e) :
    Irreducible (Matrix.of fun i j : Fin k => (X (e (i, j)) : MvPolynomial σ R)).det := by
  cases k with
  | zero => exact absurd rfl hk
  | succ n => exact RowDet.irreducible_det n e he

section Blocks

variable {ι : Type} (m : ι → ℕ) (L : Type) [Field L]

abbrev Lt : Type := Σ τ : ι, Fin (m τ) × Fin (m τ)

noncomputable def gen (τ : ι) : Matrix (Fin (m τ)) (Fin (m τ)) (MvPolynomial (Lt m) L) :=
  Matrix.of fun i k => X ⟨τ, i, k⟩

/- English proof (translation)
The claim follows from `sigma_mk_injective (β := fun τ => Fin (m τ) × Fin (m τ))`.
-/
theorem inj_block (τ : ι) :
    Function.Injective (fun p : Fin (m τ) × Fin (m τ) => (⟨τ, p⟩ : Lt m)) :=
  sigma_mk_injective (β := fun τ => Fin (m τ) × Fin (m τ))

/- English proof (translation)
Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `[gen]`.
-/
theorem eval_det {T : Type*} [CommRing T] (c : L →+* T)
    (y : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) T) (τ : ι) :
    eval₂Hom c (fun p : Lt m => y p.1 p.2.1 p.2.2) (gen m L τ).det = (y τ).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [gen]

/- English proof (translation)
Introduce `h`. Use `eval_det m L (RingHom.id L) (fun _ => 1) τ` as an intermediate fact. Rewrite `this` using `[h]`. Simplify using `at this`.
-/
theorem gen_det_ne_zero (τ : ι) : (gen m L τ).det ≠ 0 := by
  intro h
  have := eval_det m L (RingHom.id L) (fun _ => 1) τ
  rw [h] at this
  simp at this

/- English proof (translation)
Distinguish the cases in `h0 : m τ = 0`. Use `haveI : IsEmpty (Fin (m τ)) := by rw [h0]; infer_instance`. Rewrite using `[Matrix.det_isEmpty]`. Conclude with `isRelPrime_one_left`. Establish `hi : Irreducible (gen m L τ).det` using `irreducible_det' h0 _ (inj_block m τ)`.

Rewrite using `[hi.isRelPrime_iff_not_dvd]`. Introduce `hd`. Use `haveI : Nonempty (Fin (m τ)) := ⟨⟨0, Nat.pos_of_ne_zero h0⟩⟩`. Use `map_dvd (eval₂Hom (RingHom.id L) (fun p : Lt m => (fun t => if t = τ then (0 : Matrix (Fin (m t)) (Fin (m t)) L) else 1) p.1 p.2.1 p.2.2)) hd` as an intermediate fact. Rewrite `this` using `[eval_det m L _ (fun t => if t = τ then 0 else 1), eval_det m L _ (fun t => if t = τ then 0 else 1)]`.

Simplify using `[h.symm] at this`.
-/
theorem gen_isRelPrime {τ τ' : ι} (h : τ ≠ τ') :
    IsRelPrime (gen m L τ).det (gen m L τ').det := by
  classical
  by_cases h0 : m τ = 0
  · haveI : IsEmpty (Fin (m τ)) := by rw [h0]; infer_instance
    rw [Matrix.det_isEmpty]; exact isRelPrime_one_left
  · have hi : Irreducible (gen m L τ).det := irreducible_det' h0 _ (inj_block m τ)
    rw [hi.isRelPrime_iff_not_dvd]
    intro hd
    haveI : Nonempty (Fin (m τ)) := ⟨⟨0, Nat.pos_of_ne_zero h0⟩⟩
    have := map_dvd (eval₂Hom (RingHom.id L)
      (fun p : Lt m => (fun t => if t = τ then (0 : Matrix (Fin (m t)) (Fin (m t)) L) else 1)
        p.1 p.2.1 p.2.2)) hd
    rw [eval_det m L _ (fun t => if t = τ then 0 else 1),
      eval_det m L _ (fun t => if t = τ then 0 else 1)] at this
    simp [h.symm] at this

variable [Fintype ι]

def Equivariant (S : Type) [CommRing S] [Algebra (MvPolynomial (Lt m) L) S]
    (a : ι × ℕ → ℕ) (f : S) : Prop :=
  ∀ (T : Type) [Field T] (φ ψ : S →+* T) (b : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) T),
    (∀ g : L, φ (algebraMap (MvPolynomial (Lt m) L) _ (C g)) =
      ψ (algebraMap (MvPolynomial (Lt m) L) _ (C g))) →
    (∀ τ i j, i < j → b τ i j = 0) →
    (∀ τ i k, ψ (algebraMap (MvPolynomial (Lt m) L) _ (X ⟨τ, i, k⟩)) =
      ∑ j, b τ i j * φ (algebraMap (MvPolynomial (Lt m) L) _ (X ⟨τ, j, k⟩))) →
    ψ f = (∏ τ, ∏ i, b τ i i ^ a (τ, (i : ℕ))) * φ f

variable {m L} {S : Type} [CommRing S] [Algebra (MvPolynomial (Lt m) L) S]
  [IsLocalization.Away (∏ τ, (gen m L τ).det) S]

/- English proof (translation)
Establish `hu : ∀ z : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) T, (∀ τ, (z τ).det ≠ 0) → IsUnit (eval₂Hom c (fun p : Lt m => z p.1 p.2.1 p.2.2) (∏ τ, (gen m L τ).det))`. Introduce `z hz`. Rewrite using `[map_prod, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]`. Introduce `τ _`. Rewrite using `[eval_det]`.

Conclude with `hz τ`. Set `φ : S →+* T` to `IsLocalization.Away.lift _ (hu x hx)`. Set `ψ : S →+* T` to `IsLocalization.Away.lift _ (hu y hy)`. Establish `hφ : ∀ q, φ (algebraMap _ S q) = eval₂Hom c (fun p : Lt m => x p.1 p.2.1 p.2.2) q` using `fun q => IsLocalization.Away.lift_eq _ _ q`. Establish `hψ : ∀ q, ψ (algebraMap _ S q) = eval₂Hom c (fun p : Lt m => y p.1 p.2.1 p.2.2) q` using `fun q => IsLocalization.Away.lift_eq _ _ q`.

Establish `key` using `hf T φ ψ b (fun g => by rw [hφ, hψ]; simp) hb (fun τ i k => by`. Simplify using `only [hφ, hψ, eval₂Hom_X']`. Rewrite using `[hxy, Matrix.mul_apply])`. Establish `h1` using `congrArg φ hP`. Establish `h2` using `congrArg ψ hP`.

Rewrite `h1` using `[map_mul, hφ, hφ, map_pow, map_prod]`. Rewrite `h2` using `[map_mul, hψ, hψ, map_pow, map_prod]`. Simplify using `only [eval_det] at h1 h2`. Rewrite using `[← h1, ← h2, key]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Equivariant.numer {a : ι × ℕ → ℕ} {f : S} (hf : Equivariant m L S a f)
    {P : MvPolynomial (Lt m) L} {N : ℕ}
    (hP : f * algebraMap _ S ((∏ τ, (gen m L τ).det) ^ N) = algebraMap _ S P)
    {T : Type} [Field T] (c : L →+* T) (x y b : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) T)
    (hx : ∀ τ, (x τ).det ≠ 0) (hy : ∀ τ, (y τ).det ≠ 0) (hb : ∀ τ i j, i < j → b τ i j = 0)
    (hxy : ∀ τ, y τ = b τ * x τ) :
    eval₂Hom c (fun p : Lt m => y p.1 p.2.1 p.2.2) P * (∏ τ, (x τ).det) ^ N =
      (∏ τ, ∏ i, b τ i i ^ a (τ, (i : ℕ))) *
        eval₂Hom c (fun p : Lt m => x p.1 p.2.1 p.2.2) P * (∏ τ, (y τ).det) ^ N := by
  have hu : ∀ z : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) T, (∀ τ, (z τ).det ≠ 0) →
      IsUnit (eval₂Hom c (fun p : Lt m => z p.1 p.2.1 p.2.2) (∏ τ, (gen m L τ).det)) := by
    intro z hz
    rw [map_prod, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro τ _
    rw [eval_det]; exact hz τ
  let φ : S →+* T := IsLocalization.Away.lift _ (hu x hx)
  let ψ : S →+* T := IsLocalization.Away.lift _ (hu y hy)
  have hφ : ∀ q, φ (algebraMap _ S q) = eval₂Hom c (fun p : Lt m => x p.1 p.2.1 p.2.2) q :=
    fun q => IsLocalization.Away.lift_eq _ _ q
  have hψ : ∀ q, ψ (algebraMap _ S q) = eval₂Hom c (fun p : Lt m => y p.1 p.2.1 p.2.2) q :=
    fun q => IsLocalization.Away.lift_eq _ _ q
  have key := hf T φ ψ b (fun g => by rw [hφ, hψ]; simp) hb (fun τ i k => by
    simp only [hφ, hψ, eval₂Hom_X']
    rw [hxy, Matrix.mul_apply])
  have h1 := congrArg φ hP
  have h2 := congrArg ψ hP
  rw [map_mul, hφ, hφ, map_pow, map_prod] at h1
  rw [map_mul, hψ, hψ, map_pow, map_prod] at h2
  simp only [eval_det] at h1 h2
  rw [← h1, ← h2, key]
  ring

/- English proof (translation)
Distinguish the cases in `h0 : m τ₀ = 0`. Use `haveI : IsEmpty (Fin (m τ₀)) := by rw [h0]; infer_instance`. Rewrite using `[Matrix.det_isEmpty, one_pow]`. Conclude with `one_dvd _`. Set `l : Fin (m τ₀)` to `⟨m τ₀ - 1, by omega⟩`.

Establish `hl : ∀ i, i ≤ l` using `fun i => by`. Use `i.2` as an intermediate fact. Simplify using `only [Fin.le_def, l]`. Use linear arithmetic over natural numbers and integers. Take `⟨hM0, hrel⟩` from `minor_isRelPrime' (R := L) _ (inj_block m τ₀) l hl`.

Express the relevant statement in the definitionally equal form `((gen m L τ₀).updateRow l (Pi.single l 1)).det ≠ 0 at hM0`. Express the relevant statement in the definitionally equal form `IsRelPrime ((gen m L τ₀).updateRow l (Pi.single l 1)).det (gen m L τ₀).det at hrel`. Use `set B := (gen m L τ₀).updateRow l (Pi.single l 1) with hB`. Set `T` to `FractionRing (MvPolynomial (Lt m) L)`. Set `g : MvPolynomial (Lt m) L →+* T` to `algebraMap _ _`.

Establish `hg : Function.Injective g` using `IsFractionRing.injective _ _`. Establish `hg0 : ∀ {q}, q ≠ 0 → g q ≠ 0` using `fun hq h => hq (hg (h.trans (map_zero _).symm))`. Set `x₀ : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) (MvPolynomial (Lt m) L)` to `Function.update (gen m L) τ₀ B`. Establish `hx₀ : ∀ τ, (x₀ τ).det ≠ 0`. Introduce `τ`.

Distinguish the cases in `h : τ = τ₀`. Substitute `h` using the available equality. Simplify `hM0` using `[x₀]`. Simplify `gen_det_ne_zero m L τ` using `[x₀, h]`. Set `x` to `fun τ => g.mapMatrix (x₀ τ)`.

Set `y` to `fun τ => g.mapMatrix (gen m L τ)`. Establish `hxd : ∀ τ, (x τ).det = g (x₀ τ).det` using `fun τ => (RingHom.map_det _ _).symm`. Establish `hyd : ∀ τ, (y τ).det = g (gen m L τ).det` using `fun τ => (RingHom.map_det _ _).symm`. Establish `hx : ∀ τ, (x τ).det ≠ 0` using `fun τ => hxd τ ▸ hg0 (hx₀ τ)`. Establish `hy : ∀ τ, (y τ).det ≠ 0` using `fun τ => hyd τ ▸ hg0 (gen_det_ne_zero m L τ)`.

Set `b` to `fun τ => y τ * (x τ)⁻¹`. Establish `hxy : ∀ τ, y τ = b τ * x τ` using `fun τ => by`. Simplify using `only [b]`. Rewrite using `[Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hx τ).isUnit, Matrix.mul_one]`. Establish `hrow : ∀ τ i, y τ i = x τ i → ∀ j, b τ i j = (1 : Matrix _ _ T) i j`.

Introduce `τ i h j`. Rewrite using `[← Matrix.mul_nonsing_inv _ (hx τ).isUnit]`. Simplify using `only [b, Matrix.mul_apply, h]`. Establish `hne : ∀ τ, τ ≠ τ₀ → y τ = x τ` using `fun τ h => by simp [x, y, x₀, h]`. Establish `hl' : ∀ i, i ≠ l → y τ₀ i = x τ₀ i` using `fun i h => by`.

Use extensionality with `j`. Simplify using `[x, y, x₀, B, Matrix.updateRow_ne h]`. Establish `hb : ∀ τ i j, i < j → b τ i j = 0`. Introduce `τ i j hij`. Rewrite using `[hrow τ i, Matrix.one_apply_ne hij.ne]`.

Distinguish the cases in `h : τ = τ₀`. Substitute `h` using the available equality. Conclude with `hl' i (hij.trans_le (hl j)).ne`. Rewrite using `[hne τ h]`. Establish `hdetb : (b τ₀).det = b τ₀ l l`.

Rewrite using `[Matrix.det_of_lowerTriangular _ (fun i j hij => hb τ₀ i j hij), Finset.prod_eq_single l]`. Introduce `i _ hi`. Rewrite using `[hrow _ _ (hl' i hi), Matrix.one_apply_eq]`. Simplify using the standard rewrite rules. Establish `hc : (∏ τ, ∏ i, b τ i i ^ a (τ, (i : ℕ))) = b τ₀ l l ^ a (τ₀, (l : ℕ))`.

Rewrite using `[Finset.prod_eq_single τ₀, Finset.prod_eq_single l]`. Introduce `i _ hi`. Rewrite using `[hrow _ _ (hl' i hi), Matrix.one_apply_eq, one_pow]`. Simplify using the standard rewrite rules. Introduce `τ _ h`.

Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hrow τ i (by rw [hne τ h]), Matrix.one_apply_eq, one_pow]`. Simplify using the standard rewrite rules. Establish `hs : (y τ₀).det = b τ₀ l l * (x τ₀).det`. Rewrite using `[← hdetb, ← Matrix.det_mul, ← hxy]`.

Establish `key` using `hf.numer hP (g.comp C) x y b hx hy hb hxy`. Establish `e1 : eval₂Hom (g.comp C) (fun p : Lt m => y p.1 p.2.1 p.2.2) = g`. Apply the tactic sequence `ext <;> simp [y, gen]`. Establish `e2 : eval₂Hom (g.comp C) (fun p : Lt m => x p.1 p.2.1 p.2.2) = g.comp (eval₂Hom C (fun p : Lt m => x₀ p.1 p.2.1 p.2.2))`. Apply the tactic sequence `ext <;> simp [x]`.

Establish `e3 : ∏ τ ∈ Finset.univ.erase τ₀, (y τ).det = ∏ τ ∈ Finset.univ.erase τ₀, (x τ).det` using `Finset.prod_congr rfl fun τ hτ => by rw [hne τ (Finset.ne_of_mem_erase hτ)]`. Establish `hO : ∏ τ ∈ Finset.univ.erase τ₀, (x τ).det ≠ 0` using `Finset.prod_ne_zero_iff.2 fun τ _ => hx τ`. Rewrite `key` using `[e1, e2, hc, ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ₀), ← Finset.mul_prod_erase _ (fun τ => (y τ).det) (Finset.mem_univ τ₀), e3, mul_pow, mul_pow, ← mul_assoc, ← mul_assoc]`. Establish `key2` using `mul_right_cancel₀ (pow_ne_zero N hO) key`. Establish `hxB : (x τ₀).det = g B.det` using `by rw [hxd]; simp [x₀]`.

Establish `k3 : P * B.det ^ (N + a (τ₀, (l : ℕ))) = (gen m L τ₀).det ^ N * ((gen m L τ₀).det ^ a (τ₀, (l : ℕ)) * eval₂Hom C (fun p : Lt m => x₀ p.1 p.2.1 p.2.2) P)`. Apply `hg` to reduce the goal to its premises. Rewrite `key2` using `[RingHom.comp_apply]`. Rewrite using `[map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, ← hxB, ← hyd, pow_add, ← mul_assoc, key2, hs]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `(hrel.symm.pow (m := N) (n := N + a (τ₀, (l : ℕ)))).dvd_of_dvd_mul_right ⟨_, k3⟩`.
-/
theorem Equivariant.det_pow_dvd {a : ι × ℕ → ℕ} {f : S} (hf : Equivariant m L S a f)
    {P : MvPolynomial (Lt m) L} {N : ℕ}
    (hP : f * algebraMap _ S ((∏ τ, (gen m L τ).det) ^ N) = algebraMap _ S P) (τ₀ : ι) :
    (gen m L τ₀).det ^ N ∣ P := by
  classical
  by_cases h0 : m τ₀ = 0
  · haveI : IsEmpty (Fin (m τ₀)) := by rw [h0]; infer_instance
    rw [Matrix.det_isEmpty, one_pow]; exact one_dvd _
  let l : Fin (m τ₀) := ⟨m τ₀ - 1, by omega⟩
  have hl : ∀ i, i ≤ l := fun i => by
    have := i.2
    simp only [Fin.le_def, l]; omega
  obtain ⟨hM0, hrel⟩ := minor_isRelPrime' (R := L) _ (inj_block m τ₀) l hl
  change ((gen m L τ₀).updateRow l (Pi.single l 1)).det ≠ 0 at hM0
  change IsRelPrime ((gen m L τ₀).updateRow l (Pi.single l 1)).det (gen m L τ₀).det at hrel
  set B := (gen m L τ₀).updateRow l (Pi.single l 1) with hB
  let T := FractionRing (MvPolynomial (Lt m) L)
  let g : MvPolynomial (Lt m) L →+* T := algebraMap _ _
  have hg : Function.Injective g := IsFractionRing.injective _ _
  have hg0 : ∀ {q}, q ≠ 0 → g q ≠ 0 := fun hq h => hq (hg (h.trans (map_zero _).symm))
  let x₀ : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) (MvPolynomial (Lt m) L) :=
    Function.update (gen m L) τ₀ B
  have hx₀ : ∀ τ, (x₀ τ).det ≠ 0 := by
    intro τ
    by_cases h : τ = τ₀
    · subst h; simpa [x₀] using hM0
    · simpa [x₀, h] using gen_det_ne_zero m L τ
  let x := fun τ => g.mapMatrix (x₀ τ)
  let y := fun τ => g.mapMatrix (gen m L τ)
  have hxd : ∀ τ, (x τ).det = g (x₀ τ).det := fun τ => (RingHom.map_det _ _).symm
  have hyd : ∀ τ, (y τ).det = g (gen m L τ).det := fun τ => (RingHom.map_det _ _).symm
  have hx : ∀ τ, (x τ).det ≠ 0 := fun τ => hxd τ ▸ hg0 (hx₀ τ)
  have hy : ∀ τ, (y τ).det ≠ 0 := fun τ => hyd τ ▸ hg0 (gen_det_ne_zero m L τ)
  let b := fun τ => y τ * (x τ)⁻¹
  have hxy : ∀ τ, y τ = b τ * x τ := fun τ => by
    simp only [b]
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hx τ).isUnit, Matrix.mul_one]
  have hrow : ∀ τ i, y τ i = x τ i → ∀ j, b τ i j = (1 : Matrix _ _ T) i j := by
    intro τ i h j
    rw [← Matrix.mul_nonsing_inv _ (hx τ).isUnit]
    simp only [b, Matrix.mul_apply, h]
  have hne : ∀ τ, τ ≠ τ₀ → y τ = x τ := fun τ h => by simp [x, y, x₀, h]
  have hl' : ∀ i, i ≠ l → y τ₀ i = x τ₀ i := fun i h => by
    ext j; simp [x, y, x₀, B, Matrix.updateRow_ne h]
  have hb : ∀ τ i j, i < j → b τ i j = 0 := by
    intro τ i j hij
    rw [hrow τ i, Matrix.one_apply_ne hij.ne]
    by_cases h : τ = τ₀
    · subst h; exact hl' i (hij.trans_le (hl j)).ne
    · rw [hne τ h]
  have hdetb : (b τ₀).det = b τ₀ l l := by
    rw [Matrix.det_of_lowerTriangular _ (fun i j hij => hb τ₀ i j hij), Finset.prod_eq_single l]
    · intro i _ hi; rw [hrow _ _ (hl' i hi), Matrix.one_apply_eq]
    · simp
  have hc : (∏ τ, ∏ i, b τ i i ^ a (τ, (i : ℕ))) = b τ₀ l l ^ a (τ₀, (l : ℕ)) := by
    rw [Finset.prod_eq_single τ₀, Finset.prod_eq_single l]
    · intro i _ hi; rw [hrow _ _ (hl' i hi), Matrix.one_apply_eq, one_pow]
    · simp
    · intro τ _ h
      refine Finset.prod_eq_one fun i _ => ?_
      rw [hrow τ i (by rw [hne τ h]), Matrix.one_apply_eq, one_pow]
    · simp
  have hs : (y τ₀).det = b τ₀ l l * (x τ₀).det := by
    rw [← hdetb, ← Matrix.det_mul, ← hxy]
  have key := hf.numer hP (g.comp C) x y b hx hy hb hxy
  have e1 : eval₂Hom (g.comp C) (fun p : Lt m => y p.1 p.2.1 p.2.2) = g := by
    ext <;> simp [y, gen]
  have e2 : eval₂Hom (g.comp C) (fun p : Lt m => x p.1 p.2.1 p.2.2) =
      g.comp (eval₂Hom C (fun p : Lt m => x₀ p.1 p.2.1 p.2.2)) := by
    ext <;> simp [x]
  have e3 : ∏ τ ∈ Finset.univ.erase τ₀, (y τ).det = ∏ τ ∈ Finset.univ.erase τ₀, (x τ).det :=
    Finset.prod_congr rfl fun τ hτ => by rw [hne τ (Finset.ne_of_mem_erase hτ)]
  have hO : ∏ τ ∈ Finset.univ.erase τ₀, (x τ).det ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => hx τ
  rw [e1, e2, hc, ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ₀),
    ← Finset.mul_prod_erase _ (fun τ => (y τ).det) (Finset.mem_univ τ₀), e3, mul_pow, mul_pow,
    ← mul_assoc, ← mul_assoc] at key
  have key2 := mul_right_cancel₀ (pow_ne_zero N hO) key
  have hxB : (x τ₀).det = g B.det := by rw [hxd]; simp [x₀]
  have k3 : P * B.det ^ (N + a (τ₀, (l : ℕ))) = (gen m L τ₀).det ^ N *
      ((gen m L τ₀).det ^ a (τ₀, (l : ℕ)) *
        eval₂Hom C (fun p : Lt m => x₀ p.1 p.2.1 p.2.2) P) := by
    apply hg
    rw [RingHom.comp_apply] at key2
    rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, ← hxB, ← hyd, pow_add, ← mul_assoc,
      key2, hs]
    ring
  exact (hrel.symm.pow (m := N) (n := N + a (τ₀, (l : ℕ)))).dvd_of_dvd_mul_right ⟨_, k3⟩

/- English proof (translation)
Set `T` to `FractionRing (Polynomial (MvPolynomial (Lt m) L))`. Set `g : Polynomial (MvPolynomial (Lt m) L) →+* T` to `algebraMap _ _`. Establish `hg : Function.Injective g` using `IsFractionRing.injective _ _`. Establish `hg0 : ∀ {q}, q ≠ 0 → g q ≠ 0` using `fun hq h => hq (hg (h.trans (map_zero _).symm))`. Set `g' : MvPolynomial (Lt m) L →+* T` to `g.comp Polynomial.C`.

Set `t : T` to `g Polynomial.X`. Establish `ht : t ≠ 0` using `hg0 Polynomial.X_ne_zero`. Set `x` to `fun τ => g'.mapMatrix (gen m L τ)`. Establish `hx : ∀ τ, (x τ).det ≠ 0` using `fun τ => by`. Rewrite using `[← RingHom.map_det]`.

Conclude with `hg0 (Polynomial.C_ne_zero.2 (gen_det_ne_zero m L τ))`. Establish `key` using `hf.numer (N := 0) (P := Q) (by simp) (g'.comp C) x (fun τ => t • x τ) (fun τ => t • 1) hx (fun τ => by rw [Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ ht) (hx τ)) (fun τ i j hij => by simp [Matrix.one_apply_ne hij.ne]) (fun τ => by simp)`. Establish `e1 : eval₂Hom (g'.comp C) (fun p : Lt m => x p.1 p.2.1 p.2.2) = g'`. Apply the tactic sequence `ext <;> simp [x, gen]`. Establish `e2 : eval₂Hom (g'.comp C) (fun p : Lt m => (t • x p.1) p.2.1 p.2.2) = g.comp (eval₂Hom ((Polynomial.C : MvPolynomial (Lt m) L →+* _).comp C) (fun i => Polynomial.X * Polynomial.C (X i)))`.

Use `ext`. Simplify using `[g']`. Simplify using `[x, gen, g', t]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `key` using `[e1, e2]`.

Simplify using `only [pow_zero, mul_one, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, Finset.prod_pow_eq_pow_sum] at key`. Establish `k2 : eval₂Hom ((Polynomial.C : MvPolynomial (Lt m) L →+* _).comp C) (fun i => Polynomial.X * Polynomial.C (X i)) Q = Polynomial.C Q * Polynomial.X ^ (∑ τ, ∑ i : Fin (m τ), a (τ, (i : ℕ)))`. Apply `hg` to reduce the goal to its premises. Rewrite using `[map_mul, map_pow, mul_comm]`. Conclude with `key`.

Establish `k3` using `coeff_scale Q (∑ τ, ∑ i : Fin (m τ), a (τ, (i : ℕ)))`. Rewrite `k3` using `[k2, Polynomial.coeff_C_mul_X_pow, if_pos rfl]`. Rewrite using `[k3]`. Conclude with `homogeneousComponent_isHomogeneous _ _`.
-/
theorem Equivariant.isHomogeneous {a : ι × ℕ → ℕ} {Q : MvPolynomial (Lt m) L}
    (hf : Equivariant m L S a (algebraMap _ S Q)) :
    Q.IsHomogeneous (∑ τ, ∑ i : Fin (m τ), a (τ, (i : ℕ))) := by
  let T := FractionRing (Polynomial (MvPolynomial (Lt m) L))
  let g : Polynomial (MvPolynomial (Lt m) L) →+* T := algebraMap _ _
  have hg : Function.Injective g := IsFractionRing.injective _ _
  have hg0 : ∀ {q}, q ≠ 0 → g q ≠ 0 := fun hq h => hq (hg (h.trans (map_zero _).symm))
  let g' : MvPolynomial (Lt m) L →+* T := g.comp Polynomial.C
  let t : T := g Polynomial.X
  have ht : t ≠ 0 := hg0 Polynomial.X_ne_zero
  let x := fun τ => g'.mapMatrix (gen m L τ)
  have hx : ∀ τ, (x τ).det ≠ 0 := fun τ => by
    rw [← RingHom.map_det]
    exact hg0 (Polynomial.C_ne_zero.2 (gen_det_ne_zero m L τ))
  have key := hf.numer (N := 0) (P := Q) (by simp) (g'.comp C) x (fun τ => t • x τ)
    (fun τ => t • 1) hx
    (fun τ => by rw [Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ ht) (hx τ))
    (fun τ i j hij => by simp [Matrix.one_apply_ne hij.ne]) (fun τ => by simp)
  have e1 : eval₂Hom (g'.comp C) (fun p : Lt m => x p.1 p.2.1 p.2.2) = g' := by
    ext <;> simp [x, gen]
  have e2 : eval₂Hom (g'.comp C) (fun p : Lt m => (t • x p.1) p.2.1 p.2.2) =
      g.comp (eval₂Hom ((Polynomial.C : MvPolynomial (Lt m) L →+* _).comp C)
        (fun i => Polynomial.X * Polynomial.C (X i))) := by
    ext
    · simp [g']
    · simp [x, gen, g', t]; ring
  rw [e1, e2] at key
  simp only [pow_zero, mul_one, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
    Finset.prod_pow_eq_pow_sum] at key
  have k2 : eval₂Hom ((Polynomial.C : MvPolynomial (Lt m) L →+* _).comp C)
        (fun i => Polynomial.X * Polynomial.C (X i)) Q =
      Polynomial.C Q * Polynomial.X ^ (∑ τ, ∑ i : Fin (m τ), a (τ, (i : ℕ))) := by
    apply hg
    rw [map_mul, map_pow, mul_comm]
    exact key
  have k3 := coeff_scale Q (∑ τ, ∑ i : Fin (m τ), a (τ, (i : ℕ)))
  rw [k2, Polynomial.coeff_C_mul_X_pow, if_pos rfl] at k3
  rw [k3]
  exact homogeneousComponent_isHomogeneous _ _

/- English proof (translation)
Take `⟨⟨P, ⟨_, N, rfl⟩⟩, hP⟩` from `IsLocalization.surj (Submonoid.powers (∏ τ, (gen m L τ).det)) f`. Simplify using `only at hP`. Establish `hd : (∏ τ, (gen m L τ).det) ^ N ∣ P`. Rewrite using `[← Finset.prod_pow]`. Conclude with `Finset.prod_dvd_of_isRelPrime (fun τ _ τ' _ h => (gen_isRelPrime m L h).pow) fun τ _ => hf.det_pow_dvd hP τ`.

Take `⟨Q, rfl⟩` from `hd`. Establish `hu : IsUnit (algebraMap _ S ((∏ τ, (gen m L τ).det) ^ N))`. Rewrite using `[map_pow]`. Conclude with `(IsLocalization.Away.algebraMap_isUnit _).pow N`. Rewrite `hP` using `[map_mul, mul_comm]`.

Take `rfl : f = algebraMap _ S Q` from `hu.mul_left_cancel hP`. Conclude with `⟨Q, rfl, hf.isHomogeneous⟩`.
-/
theorem Equivariant.exists_isHomogeneous {a : ι × ℕ → ℕ} {f : S} (hf : Equivariant m L S a f) :
    ∃ P : MvPolynomial (Lt m) L, algebraMap _ S P = f ∧
      P.IsHomogeneous (∑ τ, ∑ i : Fin (m τ), a (τ, (i : ℕ))) := by
  obtain ⟨⟨P, ⟨_, N, rfl⟩⟩, hP⟩ :=
    IsLocalization.surj (Submonoid.powers (∏ τ, (gen m L τ).det)) f
  simp only at hP
  have hd : (∏ τ, (gen m L τ).det) ^ N ∣ P := by
    rw [← Finset.prod_pow]
    exact Finset.prod_dvd_of_isRelPrime
      (fun τ _ τ' _ h => (gen_isRelPrime m L h).pow) fun τ _ => hf.det_pow_dvd hP τ
  obtain ⟨Q, rfl⟩ := hd
  have hu : IsUnit (algebraMap _ S ((∏ τ, (gen m L τ).det) ^ N)) := by
    rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit _).pow N
  rw [map_mul, mul_comm] at hP
  obtain rfl : f = algebraMap _ S Q := hu.mul_left_cancel hP
  exact ⟨Q, rfl, hf.isHomogeneous⟩

end Blocks

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj in

/- English proof (translation)
Introduce `E _ _ _ H Dw K _ a f hf`. Use `haveI : IsLocalization.Away (∏ τ, (gen Dw.mult (LaurentSeries K) τ).det) (ArcS Dw K) := (inferInstance : IsLocalization.Away (arcDet Dw K) (ArcS Dw K))`. Conclude with `Equivariant.exists_isHomogeneous (m := Dw.mult) (L := LaurentSeries K) hf`.
-/
theorem exists_isHomogeneous_of_equivariant :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (K : Type) [Field K] (a : (E →+* ℂ) × ℕ → ℕ) (f : ArcS Dw K), (∀ (T : Type) [Field T] (φ ψ : ArcS Dw K →+* T) (b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T), (∀ g : LaurentSeries K, φ (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) _ (MvPolynomial.C g)) = ψ (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) _ (MvPolynomial.C g))) → (∀ τ i j, i < j → b τ i j = 0) → (∀ τ i k, ψ (arcX Dw K τ i k) = ∑ j, b τ i j * φ (arcX Dw K τ j k)) → ψ f = (∏ τ, ∏ i, b τ i i ^ a (τ, (i : ℕ))) * φ f) → ∃ P : MvPolynomial (ArcLt Dw) (LaurentSeries K), algebraMap _ (ArcS Dw K) P = f ∧ P.IsHomogeneous (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, (i : ℕ))) := by
  intro E _ _ _ H Dw K _ a f hf
  haveI : IsLocalization.Away (∏ τ, (gen Dw.mult (LaurentSeries K) τ).det) (ArcS Dw K) :=
    (inferInstance : IsLocalization.Away (arcDet Dw K) (ArcS Dw K))
  exact Equivariant.exists_isHomogeneous (m := Dw.mult) (L := LaurentSeries K) hf

end GlobalTheory.BorelAlg
