import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.UnipLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Grp

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_mul (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_one : mat (1 : UA σ J) = 1 := rfl

/- English proof (translation)
Rewrite using `[← mat_mul, inv_mul_cancel, mat_one]`.
-/
theorem mat_inv_mul (g : UA σ J) : mat g⁻¹ * mat g = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]

/- English proof (translation)
Rewrite using `[mat_mul, Matrix.mulVec_mulVec]`.
-/
theorem mulVec_mul (g h : UA σ J) (v : Fin n → AE F E) : mat (g * h) *ᵥ v = mat g *ᵥ (mat h *ᵥ v) := by
  rw [mat_mul, Matrix.mulVec_mulVec]

/- English proof (translation)
Rewrite using `[← h, Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]`.
-/
theorem inv_mulVec_of_mulVec {g : UA σ J} {v w : Fin n → AE F E} (h : mat g *ᵥ v = w) : mat g⁻¹ *ᵥ w = v := by
  rw [← h, Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]

/- English proof (translation)
The claim follows from `Subtype.ext (Units.ext e)`.
-/
theorem ext_mat {g h : UA σ J} (e : mat g = mat h) : g = h := Subtype.ext (Units.ext e)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rw [pow_zero, mat_one, Matrix.one_mulVec]`. Consider the case `succ k ih => rw [pow_succ, mulVec_mul, h, ih]`.
-/
theorem pow_mulVec_fix {g : UA σ J} {v : Fin n → AE F E} (h : mat g *ᵥ v = v) (k : ℕ) : mat (g ^ k) *ᵥ v = v := by
  induction k with
  | zero => rw [pow_zero, mat_one, Matrix.one_mulVec]
  | succ k ih => rw [pow_succ, mulVec_mul, h, ih]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp [mat_one]`. Consider the case `succ k ih`. Rewrite using `[pow_succ, mulVec_mul, hy, Matrix.mulVec_add, Matrix.mulVec_smul, ih, pow_mulVec_fix hx, Nat.cast_succ, add_mul, one_mul, add_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem pow_mulVec_shear {g : UA σ J} {x y : Fin n → AE F E} {d : AE F E} (hx : mat g *ᵥ x = x)
    (hy : mat g *ᵥ y = y + d • x) (k : ℕ) : mat (g ^ k) *ᵥ y = y + ((k : AE F E) * d) • x := by
  induction k with
  | zero => simp [mat_one]
  | succ k ih =>
    rw [pow_succ, mulVec_mul, hy, Matrix.mulVec_add, Matrix.mulVec_smul, ih, pow_mulVec_fix hx, Nat.cast_succ,
      add_mul, one_mul, add_smul]
    abel

end Grp

/- English proof (translation)
Establish `: IsUnit (algebraMap F (AE F E) (k : F))` using `(isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hk)).map _`. Simplify using `using this`.
-/
theorem isUnit_natCast {k : ℕ} (hk : k ≠ 0) : IsUnit (k : AE F E) := by
  have : IsUnit (algebraMap F (AE F E) (k : F)) := (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hk)).map _
  simpa using this

/- English proof (translation)
Establish `h : ∀ w, P *ᵥ w = Q *ᵥ w`. Introduce `w`. Take `⟨a, b, z, rfl⟩` from `hs w`. Simplify using `only [Matrix.mulVec_add, Matrix.mulVec_smul, hx, hy, hi]`. Use extensionality with `i j`.

Simplify `congrFun (h (Pi.single j 1)) i` using `[Matrix.mulVec_single_one]`.
-/
theorem ext_of_span {n n₁ : ℕ} {x y : Fin n → AE F E} {ι : Matrix (Fin n) (Fin n₁) (AE F E)}
    (hs : ∀ w, ∃ (a b : AE F E) (z : Fin n₁ → AE F E), w = a • x + ι *ᵥ z + b • y)
    {P Q : Matrix (Fin n) (Fin n) (AE F E)} (hx : P *ᵥ x = Q *ᵥ x) (hy : P *ᵥ y = Q *ᵥ y)
    (hi : ∀ z, P *ᵥ (ι *ᵥ z) = Q *ᵥ (ι *ᵥ z)) : P = Q := by
  have h : ∀ w, P *ᵥ w = Q *ᵥ w := by
    intro w
    obtain ⟨a, b, z, rfl⟩ := hs w
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hx, hy, hi]
  ext i j
  simpa [Matrix.mulVec_single_one] using congrFun (h (Pi.single j 1)) i

/- English proof (translation)
Establish `h2 : IsUnit (2 : AE F E)` using `by exact_mod_cast isUnit_natCast (F := F) (E := E) two_ne_zero`. Establish `uix : mat u⁻¹ *ᵥ x = x` using `inv_mulVec_of_mulVec hux`. Establish `uii : ∀ z (a : AE F E), mat u *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x → mat u⁻¹ *ᵥ (ι *ᵥ z) = ι *ᵥ z - a • x`. Introduce `z a h`. Use `inv_mulVec_of_mulVec h` as an intermediate fact.

Rewrite `this` using `[Matrix.mulVec_add, Matrix.mulVec_smul, uix]`. Conclude with `eq_sub_of_add_eq this`. Take `⟨a₀, ha₀⟩` from `hui z₀`. Establish `uiz₀` using `uii z₀ a₀ ha₀`. Establish `uiy : mat u⁻¹ *ᵥ y = y - c • x - ι *ᵥ z₀ + a₀ • x`.

Use `inv_mulVec_of_mulVec huy` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, uix, uiz₀]`. Use extensionality with `i`. Use `congrFun this i` as an intermediate fact. Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢`.

Take the linear combination `this`. Establish `mix : (2 : AE F E) • (mat m⁻¹ *ᵥ x) = x`. Use `inv_mulVec_of_mulVec hmx` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_smul]`. Then use the resulting hypothesis. Establish `miy : mat m⁻¹ *ᵥ y = (2 : AE F E) • y`.

Use `congrArg (fun v => mat m⁻¹ *ᵥ v) hmy` as an intermediate fact. Simplify using `only [Matrix.mulVec_smul, Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec] at this`. Conclude with `this.symm`. Establish `mii : ∀ z, mat m⁻¹ *ᵥ (ι *ᵥ z) = ι *ᵥ z` using `fun z => inv_mulVec_of_mulVec (hmi z)`. Use `set w := m * u * m⁻¹ with hw`.

Establish `wx : mat w *ᵥ x = x`. Rewrite using `[← h2.smul_left_cancel, ← Matrix.mulVec_smul, hw, mulVec_mul, mulVec_mul, Matrix.mulVec_smul (mat m⁻¹), mix, hux, hmx]`. Establish `wi : ∀ z (a : AE F E), mat u *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x → mat w *ᵥ (ι *ᵥ z) = ι *ᵥ z + (2 * a) • x`. Introduce `z a h`. Rewrite using `[hw, mulVec_mul, mulVec_mul, mii, h, Matrix.mulVec_add, Matrix.mulVec_smul, hmi, hmx, smul_smul, mul_comm]`.

Establish `wy : mat w *ᵥ y = y + (4 * c) • x + (2 : AE F E) • (ι *ᵥ z₀)`. Rewrite using `[hw, mulVec_mul, mulVec_mul, miy, Matrix.mulVec_smul, huy, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, hmi, hmx, smul_add, smul_add, hmy]`. Use extensionality with `i`. Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Use `set v := u⁻¹ * u⁻¹ * w with hv`. Establish `vx : mat v *ᵥ x = x` using `by rw [hv, mulVec_mul, mulVec_mul, wx, uix, uix]`. Establish `vi : ∀ z, mat v *ᵥ (ι *ᵥ z) = ι *ᵥ z`. Introduce `z`. Take `⟨a, ha⟩` from `hui z`.

Rewrite using `[hv, mulVec_mul, mulVec_mul, wi z a ha, Matrix.mulVec_add, Matrix.mulVec_smul, uii z a ha, uix, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, uii z a ha, uix]`. Use extensionality with `i`. Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `vy : mat v *ᵥ y = y + (2 * c - a₀) • x`.

Rewrite using `[hv, mulVec_mul, mulVec_mul, wy]`. Simplify using `only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, uix, uiy, uiz₀]`. Use extensionality with `i`. Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Use `clear_value v w`. Establish `key : m' * v = v ^ (t ^ 2) * m'`. Apply `ext_mat` to reduce the goal to its premises. Apply `ext_of_span hs` to reduce the goal to its premises. Rewrite using `[mulVec_mul m' v, mulVec_mul _ m', vx, hm'x, Matrix.mulVec_smul, pow_mulVec_fix vx]`.

Distinguish the cases in `ht : t = 0`. Substitute `ht` using the available equality. Establish `hy0 : y = 0` using `by rw [← hm'y]; simp`. Rewrite using `[hy0, Matrix.mulVec_zero, Matrix.mulVec_zero]`. Establish `hu` using `isUnit_natCast (F := F) (E := E) ht`.

Rewrite using `[← hu.smul_left_cancel, mulVec_mul m' v, mulVec_mul _ m', ← Matrix.mulVec_smul (mat (v ^ (t ^ 2))), hm'y, pow_mulVec_shear vx vy, vy, Matrix.mulVec_add, Matrix.mulVec_smul, hm'x, smul_add, hm'y]`. Use `push_cast`. Use extensionality with `i`. Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `z`. Rewrite using `[mulVec_mul m' v, mulVec_mul _ m', vi, hm'i, pow_mulVec_fix (vi z)]`. Rewrite using `[key, mul_inv_cancel_right]`.
-/
theorem conj_eq_pow {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E} {x y : Fin n → AE F E}
    {ι : Matrix (Fin n) (Fin n₁) (AE F E)}
    (hs : ∀ w, ∃ (a b : AE F E) (z : Fin n₁ → AE F E), w = a • x + ι *ᵥ z + b • y)
    (u : UA σ J) (hux : mat u *ᵥ x = x) (hui : ∀ z, ∃ a : AE F E, mat u *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x)
    (c : AE F E) (z₀ : Fin n₁ → AE F E) (huy : mat u *ᵥ y = y + c • x + ι *ᵥ z₀)
    (m m' : UA σ J) (t : ℕ) (hmx : mat m *ᵥ x = (2 : AE F E) • x) (hmy : (2 : AE F E) • (mat m *ᵥ y) = y)
    (hmi : ∀ z, mat m *ᵥ (ι *ᵥ z) = ι *ᵥ z)
    (hm'x : mat m' *ᵥ x = (t : AE F E) • x) (hm'y : (t : AE F E) • (mat m' *ᵥ y) = y)
    (hm'i : ∀ z, mat m' *ᵥ (ι *ᵥ z) = ι *ᵥ z) :
    m' * (u⁻¹ * u⁻¹ * (m * u * m⁻¹)) * m'⁻¹ = (u⁻¹ * u⁻¹ * (m * u * m⁻¹)) ^ (t ^ 2) := by
  have h2 : IsUnit (2 : AE F E) := by exact_mod_cast isUnit_natCast (F := F) (E := E) two_ne_zero
  have uix : mat u⁻¹ *ᵥ x = x := inv_mulVec_of_mulVec hux
  have uii : ∀ z (a : AE F E), mat u *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x → mat u⁻¹ *ᵥ (ι *ᵥ z) = ι *ᵥ z - a • x := by
    intro z a h
    have := inv_mulVec_of_mulVec h
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, uix] at this
    exact eq_sub_of_add_eq this
  obtain ⟨a₀, ha₀⟩ := hui z₀
  have uiz₀ := uii z₀ a₀ ha₀
  have uiy : mat u⁻¹ *ᵥ y = y - c • x - ι *ᵥ z₀ + a₀ • x := by
    have := inv_mulVec_of_mulVec huy
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, uix, uiz₀] at this
    ext i; have := congrFun this i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢; linear_combination this
  have mix : (2 : AE F E) • (mat m⁻¹ *ᵥ x) = x := by
    have := inv_mulVec_of_mulVec hmx
    rwa [Matrix.mulVec_smul] at this
  have miy : mat m⁻¹ *ᵥ y = (2 : AE F E) • y := by
    have := congrArg (fun v => mat m⁻¹ *ᵥ v) hmy
    simp only [Matrix.mulVec_smul, Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec] at this
    exact this.symm
  have mii : ∀ z, mat m⁻¹ *ᵥ (ι *ᵥ z) = ι *ᵥ z := fun z => inv_mulVec_of_mulVec (hmi z)
  set w := m * u * m⁻¹ with hw
  have wx : mat w *ᵥ x = x := by
    rw [← h2.smul_left_cancel, ← Matrix.mulVec_smul, hw, mulVec_mul, mulVec_mul, Matrix.mulVec_smul (mat m⁻¹), mix, hux, hmx]
  have wi : ∀ z (a : AE F E), mat u *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x → mat w *ᵥ (ι *ᵥ z) = ι *ᵥ z + (2 * a) • x := by
    intro z a h
    rw [hw, mulVec_mul, mulVec_mul, mii, h, Matrix.mulVec_add, Matrix.mulVec_smul, hmi, hmx, smul_smul, mul_comm]
  have wy : mat w *ᵥ y = y + (4 * c) • x + (2 : AE F E) • (ι *ᵥ z₀) := by
    rw [hw, mulVec_mul, mulVec_mul, miy, Matrix.mulVec_smul, huy, Matrix.mulVec_smul, Matrix.mulVec_add,
      Matrix.mulVec_add, Matrix.mulVec_smul, hmi, hmx, smul_add, smul_add, hmy]
    ext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  set v := u⁻¹ * u⁻¹ * w with hv
  have vx : mat v *ᵥ x = x := by rw [hv, mulVec_mul, mulVec_mul, wx, uix, uix]
  have vi : ∀ z, mat v *ᵥ (ι *ᵥ z) = ι *ᵥ z := by
    intro z
    obtain ⟨a, ha⟩ := hui z
    rw [hv, mulVec_mul, mulVec_mul, wi z a ha, Matrix.mulVec_add, Matrix.mulVec_smul, uii z a ha, uix,
      Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, uii z a ha, uix]
    ext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  have vy : mat v *ᵥ y = y + (2 * c - a₀) • x := by
    rw [hv, mulVec_mul, mulVec_mul, wy]
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, uix, uiy, uiz₀]
    ext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  clear_value v w
  have key : m' * v = v ^ (t ^ 2) * m' := by
    apply ext_mat
    apply ext_of_span hs
    · rw [mulVec_mul m' v, mulVec_mul _ m', vx, hm'x, Matrix.mulVec_smul, pow_mulVec_fix vx]
    · by_cases ht : t = 0
      · subst ht
        have hy0 : y = 0 := by rw [← hm'y]; simp
        rw [hy0, Matrix.mulVec_zero, Matrix.mulVec_zero]
      · have hu := isUnit_natCast (F := F) (E := E) ht
        rw [← hu.smul_left_cancel, mulVec_mul m' v, mulVec_mul _ m', ← Matrix.mulVec_smul (mat (v ^ (t ^ 2))), hm'y,
          pow_mulVec_shear vx vy, vy, Matrix.mulVec_add, Matrix.mulVec_smul, hm'x, smul_add, hm'y]
        push_cast
        ext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    · intro z
      rw [mulVec_mul m' v, mulVec_mul _ m', vi, hm'i, pow_mulVec_fix (vi z)]
  rw [key, mul_inv_cancel_right]

end GlobalTheory.UnipLine

namespace GlobalTheory.UnipLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def spanSet {R : Type} [CommRing R] {n n₁ : ℕ} (x y : Fin n → R) (ι : Matrix (Fin n) (Fin n₁) R) :
    Submodule R (Fin n → R) where
  carrier := {w | ∃ (a b : R) (v : Fin n₁ → R), w = a • x + ι *ᵥ v + b • y}
  add_mem' := by
    rintro _ _ ⟨a, b, v, rfl⟩ ⟨a', b', v', rfl⟩
    exact ⟨a + a', b + b', v + v', by rw [Matrix.mulVec_add, add_smul, add_smul]; abel⟩
  zero_mem' := ⟨0, 0, 0, by simp⟩
  smul_mem' := by
    rintro c _ ⟨a, b, v, rfl⟩
    exact ⟨c * a, c * b, c • v, by simp only [Matrix.mulVec_smul, smul_add, smul_smul]⟩

/- English proof (translation)
Establish `hL : Submodule.span E (X.L : Set (Fin n → E)) ≤ spanSet H.x H.y H.ι`. Rewrite using `[Submodule.span_le]`. Introduce `z hz`. Take `⟨a, b, v, -, -, -, h⟩` from `hH.split z hz`. Conclude with `⟨a, b, v, h⟩`.

Rewrite `hL` using `[hX.lat.span_eq_top]`. Conclude with `hL (Submodule.mem_top (x := w))`.
-/
theorem span_E {n n₁ : ℕ} {B : Base F E} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁} {j₀ j₁ r s : ℕ}
    (hH : H.IsAdapted σ B X X₁ j₀ j₁) (hX : X.IsHerm σ B r s) (w : Fin n → E) :
    ∃ (a b : E) (v : Fin n₁ → E), w = a • H.x + H.ι *ᵥ v + b • H.y := by
  have hL : Submodule.span E (X.L : Set (Fin n → E)) ≤ spanSet H.x H.y H.ι := by
    rw [Submodule.span_le]
    intro z hz
    obtain ⟨a, b, v, -, -, -, h⟩ := hH.split z hz
    exact ⟨a, b, v, h⟩
  rw [hX.lat.span_eq_top] at hL
  exact hL (Submodule.mem_top (x := w))

/- English proof (translation)
It suffices to establish `h : w ∈ spanSet (incV F H.x) (incV F H.y) (incM F H.ι) from h`. Rewrite using `[pi_eq_sum_univ w]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Take `⟨a, b, v, h⟩` from `span_E hH hX (fun j => if i = j then 1 else 0)`. Use `⟨inclR (AF F) a, inclR (AF F) b, incV F v, funext fun j => ?_⟩` and prove the remaining obligations.

Establish `hj` using `congrArg (inclR (F := F) (AF F)) (congrFun h j)`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, RingHom.map_mulVec] at hj`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Use `hj using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `split_ifs <;> simp`.

Both sides reduce to the same expression.
-/
theorem span_A {n n₁ : ℕ} {B : Base F E} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁} {j₀ j₁ r s : ℕ}
    (hH : H.IsAdapted σ B X X₁ j₀ j₁) (hX : X.IsHerm σ B r s) (w : Fin n → AE F E) :
    ∃ (a b : AE F E) (z : Fin n₁ → AE F E), w = a • incV F H.x + incM F H.ι *ᵥ z + b • incV F H.y := by
  suffices h : w ∈ spanSet (incV F H.x) (incV F H.y) (incM F H.ι) from h
  rw [pi_eq_sum_univ w]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  obtain ⟨a, b, v, h⟩ := span_E hH hX (fun j => if i = j then 1 else 0)
  refine ⟨inclR (AF F) a, inclR (AF F) b, incV F v, funext fun j => ?_⟩
  have hj := congrArg (inclR (F := F) (AF F)) (congrFun h j)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, RingHom.map_mulVec] at hj
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  convert hj using 1
  · split_ifs <;> simp
  · rfl

end GlobalTheory.UnipLine

namespace GlobalTheory.UnipLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Simplify using `[cA, inclR]`.
-/
theorem cA_inclR (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (AF F) (σ e) := by simp [cA, inclR]

/- English proof (translation)
The claim follows from `funext fun i => ((inclR (AF F)).map_mulVec M v i).symm`.
-/
theorem incM_mulVec_incV {m k : ℕ} (M : Matrix (Fin m) (Fin k) E) (v : Fin k → E) :
    incM F M *ᵥ incV F v = incV F (M *ᵥ v) := funext fun i => ((inclR (AF F)).map_mulVec M v i).symm

/- English proof (translation)
The claim follows from `((inclR (AF F)).map_dotProduct a b).symm`.
-/
theorem incV_dot {m : ℕ} (a b : Fin m → E) : incV F a ⬝ᵥ incV F b = inclR (AF F) (a ⬝ᵥ b) :=
  ((inclR (AF F)).map_dotProduct a b).symm

/- English proof (translation)
Introduce `h0`. Use `set q := X.J *ᵥ fun i => σ (H.x i) with hq`. Establish `hall : ∀ w : Fin n → E, w ⬝ᵥ q = 0`. Introduce `w`. Take `⟨a, b, v, rfl⟩` from `span_E hH hX w`.

Establish `h1 : H.x ⬝ᵥ q = 0` using `hH.xx`. Establish `h2 : (H.ι *ᵥ v) ⬝ᵥ q = 0` using `(hH.orth v).2 ▸ (hH.orth v).1`. Establish `h3 : H.y ⬝ᵥ q = 0` using `h0`. Simplify using `only [add_dotProduct, smul_dotProduct, h1, h2, h3, smul_zero, add_zero]`. Establish `hq0 : q = 0` using `funext fun i => by simpa using hall (Pi.single i 1)`.

Take `⟨w₀⟩` from `(inferInstance : Nonempty (InfinitePlace F))`. Use `set τ := (B.emb w₀).1`. Use `set M := X.J.map τ`. Use `set v' : Fin n → ℂ := star fun i => τ (σ (H.x i))`. Establish `hMv : M *ᵥ star v' = 0`.

Use function extensionality and compare the values at `i`. Use `(τ.map_mulVec X.J (fun i => σ (H.x i)) i).symm` as an intermediate fact. Simplify using `only [star_star, v']`. Express the relevant statement in the definitionally equal form `(X.J.map τ *ᵥ (τ ∘ fun i => σ (H.x i))) i = 0`. Rewrite using `[this, ← hq, hq0]`.

Simplify using the standard rewrite rules. Establish `hv' : v' ≠ 0`. Introduce `hv`. Establish `hx : H.x = 0`. Use function extensionality and compare the values at `i`.

Use `congrFun hv i` as an intermediate fact. Simplify using `only [v', Pi.star_apply, star_eq_zero, Pi.zero_apply, map_eq_zero] at this`. Conclude with `this`. Use `hH.xy` as an intermediate fact. Simplify using `[form, hx] at this`.

Use `(hX.cartan w₀).2.2 v' hv'` as an intermediate fact. Rewrite `this` using `[hMv, dotProduct_zero, Complex.zero_re]`. Conclude with `lt_irrefl _ this`.
-/
theorem form_y_x_ne {n n₁ : ℕ} {B : Base F E} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁} {j₀ j₁ r s : ℕ}
    (hH : H.IsAdapted σ B X X₁ j₀ j₁) (hX : X.IsHerm σ B r s) : form σ X.J H.y H.x ≠ 0 := by
  intro h0
  set q := X.J *ᵥ fun i => σ (H.x i) with hq
  have hall : ∀ w : Fin n → E, w ⬝ᵥ q = 0 := by
    intro w
    obtain ⟨a, b, v, rfl⟩ := span_E hH hX w
    have h1 : H.x ⬝ᵥ q = 0 := hH.xx
    have h2 : (H.ι *ᵥ v) ⬝ᵥ q = 0 := (hH.orth v).2 ▸ (hH.orth v).1
    have h3 : H.y ⬝ᵥ q = 0 := h0
    simp only [add_dotProduct, smul_dotProduct, h1, h2, h3, smul_zero, add_zero]
  have hq0 : q = 0 := funext fun i => by simpa using hall (Pi.single i 1)
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
  set τ := (B.emb w₀).1
  set M := X.J.map τ
  set v' : Fin n → ℂ := star fun i => τ (σ (H.x i))
  have hMv : M *ᵥ star v' = 0 := by
    funext i
    have := (τ.map_mulVec X.J (fun i => σ (H.x i)) i).symm
    simp only [star_star, v']
    change (X.J.map τ *ᵥ (τ ∘ fun i => σ (H.x i))) i = 0
    rw [this, ← hq, hq0]
    simp
  have hv' : v' ≠ 0 := by
    intro hv
    have hx : H.x = 0 := by
      funext i
      have := congrFun hv i
      simp only [v', Pi.star_apply, star_eq_zero, Pi.zero_apply, map_eq_zero] at this
      exact this
    have := hH.xy
    simp [form, hx] at this
  have := (hX.cartan w₀).2.2 v' hv'
  rw [hMv, dotProduct_zero, Complex.zero_re] at this
  exact lt_irrefl _ this

/- English proof (translation)
Use `set q := X.J *ᵥ fun i => σ (H.x i) with hq`. Use `set g := incV F q`. Establish `hunit : (mat u)ᵀ * incM F X.J * (mat u).map (cA σ) = incM F X.J` using `u.2`. Establish `hg : g = incM F X.J *ᵥ fun i => cA σ (incV F H.x i)`. Simplify using `only [g, hq, ← incM_mulVec_incV]`.

Use `congr 1`. Establish `hcx : (mat u).map (cA σ) *ᵥ (fun i => cA σ (incV F H.x i)) = fun i => cA σ (incV F H.x i)`. Use function extensionality and compare the values at `i`. Use `((cA σ).toRingHom.map_mulVec (mat u) (incV F H.x) i).symm` as an intermediate fact. Rewrite `this` using `[hux]`.

Conclude with `this`. Establish `hinv : ∀ w, (mat u *ᵥ w) ⬝ᵥ g = w ⬝ᵥ g`. Introduce `w`. Establish `hT : (mat u)ᵀ *ᵥ g = g`. Rewrite using `[hg, ← hcx, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hunit, hcx]`.

Rewrite using `[dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]`. Establish `gx : incV F H.x ⬝ᵥ g = 0` using `by rw [incV_dot]; exact (congrArg _ hH.xx).trans (map_zero _)`. Establish `gy : incV F H.y ⬝ᵥ g = inclR (AF F) (form σ X.J H.y H.x)` using `incV_dot _ _`. Establish `hιq : H.ιᵀ *ᵥ q = 0`. Use function extensionality and compare the values at `j`.

Use `(hH.orth (Pi.single j 1)).1` as an intermediate fact. Simplify using `only [form, Matrix.mulVec_single_one] at this`. Rewrite using `[Matrix.mulVec_transpose, Pi.zero_apply, ← this, ← hq, dotProduct_comm]`. Both sides reduce to the same expression. Establish `gi : ∀ z, (incM F H.ι *ᵥ z) ⬝ᵥ g = 0`.

Introduce `z`. Rewrite using `[dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]`. Establish `: (incM F H.ι)ᵀ *ᵥ g = 0`. Rewrite using `[show (incM F H.ι)ᵀ = incM F H.ιᵀ from Matrix.transpose_map.symm, incM_mulVec_incV, hιq]`. Use function extensionality and compare the values at `i`.

Simplify using `[incV]`. Rewrite using `[this, zero_dotProduct]`. Take `⟨a, b, z, h⟩` from `span_A hH hX (mat u *ᵥ incV F H.y)`. Establish `hb : b = 1`. Establish `e1` using `hinv (incV F H.y)`.

Rewrite `e1` using `[h, add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, gx, gi, gy, smul_zero, zero_add, smul_eq_mul]`. Simplify using `only [zero_add] at e1`. Establish `hu : IsUnit (inclR (F` using `F) (AF F) (form σ X.J H.y H.x)) := (isUnit_iff_ne_zero.2 (form_y_x_ne hH hX)).map _`. Use `hu.mul_left_cancel (a := _) (b := b) (c := 1) (by rw [mul_one, mul_comm]; exact e1)` as an intermediate fact. Conclude with `this`.

Use `⟨a, z, ?_⟩` and prove the remaining obligations. Rewrite using `[h, hb, one_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem mulVec_y {n n₁ : ℕ} {B : Base F E} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁} {j₀ j₁ r s : ℕ}
    (hH : H.IsAdapted σ B X X₁ j₀ j₁) (hX : X.IsHerm σ B r s) (u : UA σ X.J)
    (hux : mat u *ᵥ incV F H.x = incV F H.x) :
    ∃ (c : AE F E) (z₀ : Fin n₁ → AE F E), mat u *ᵥ incV F H.y = incV F H.y + c • incV F H.x + incM F H.ι *ᵥ z₀ := by
  set q := X.J *ᵥ fun i => σ (H.x i) with hq
  set g := incV F q
  have hunit : (mat u)ᵀ * incM F X.J * (mat u).map (cA σ) = incM F X.J := u.2
  have hg : g = incM F X.J *ᵥ fun i => cA σ (incV F H.x i) := by
    simp only [g, hq, ← incM_mulVec_incV]
    congr 1
  have hcx : (mat u).map (cA σ) *ᵥ (fun i => cA σ (incV F H.x i)) = fun i => cA σ (incV F H.x i) := by
    funext i
    have := ((cA σ).toRingHom.map_mulVec (mat u) (incV F H.x) i).symm
    rw [hux] at this
    exact this
  have hinv : ∀ w, (mat u *ᵥ w) ⬝ᵥ g = w ⬝ᵥ g := by
    intro w
    have hT : (mat u)ᵀ *ᵥ g = g := by
      rw [hg, ← hcx, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hunit, hcx]
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]
  have gx : incV F H.x ⬝ᵥ g = 0 := by rw [incV_dot]; exact (congrArg _ hH.xx).trans (map_zero _)
  have gy : incV F H.y ⬝ᵥ g = inclR (AF F) (form σ X.J H.y H.x) := incV_dot _ _
  have hιq : H.ιᵀ *ᵥ q = 0 := by
    funext j
    have := (hH.orth (Pi.single j 1)).1
    simp only [form, Matrix.mulVec_single_one] at this
    rw [Matrix.mulVec_transpose, Pi.zero_apply, ← this, ← hq, dotProduct_comm]
    rfl
  have gi : ∀ z, (incM F H.ι *ᵥ z) ⬝ᵥ g = 0 := by
    intro z
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    have : (incM F H.ι)ᵀ *ᵥ g = 0 := by
      rw [show (incM F H.ι)ᵀ = incM F H.ιᵀ from Matrix.transpose_map.symm, incM_mulVec_incV, hιq]
      funext i; simp [incV]
    rw [this, zero_dotProduct]
  obtain ⟨a, b, z, h⟩ := span_A hH hX (mat u *ᵥ incV F H.y)
  have hb : b = 1 := by
    have e1 := hinv (incV F H.y)
    rw [h, add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, gx, gi, gy, smul_zero, zero_add,
      smul_eq_mul] at e1
    simp only [zero_add] at e1
    have hu : IsUnit (inclR (F := F) (AF F) (form σ X.J H.y H.x)) := (isUnit_iff_ne_zero.2 (form_y_x_ne hH hX)).map _
    have := hu.mul_left_cancel (a := _) (b := b) (c := 1) (by rw [mul_one, mul_comm]; exact e1)
    exact this
  refine ⟨a, z, ?_⟩
  rw [h, hb, one_smul]
  abel

end GlobalTheory.UnipLine

namespace GlobalTheory.UnipLine

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n n₁ X X₁ H j₀ j₁ r s r₁ s₁ hH hX _ u hux hui m m' t hmx hmy hmi hm'x hm'y hm'i`. Take `⟨c, z₀, huy⟩` from `mulVec_y hH hX u hux`. Conclude with `conj_eq_pow (span_A hH hX) u hux hui c z₀ huy m m' t hmx hmy hmi hm'x hm'y hm'i`.
-/
theorem conj_commutator_eq_pow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X : Spc F E n)
    (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ r s r₁ s₁ : ℕ), H.IsAdapted σ B X X₁ j₀ j₁ → X.IsHerm σ B r s → X₁.IsHerm σ B r₁ s₁ →
      ∀ u : UA σ X.J, mat u *ᵥ incV F H.x = incV F H.x →
      (∀ z : Fin n₁ → AE F E, ∃ a : AE F E, mat u *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x) →
      ∀ (m m' : UA σ X.J) (t : ℕ),
      mat m *ᵥ incV F H.x = (2 : AE F E) • incV F H.x → (2 : AE F E) • (mat m *ᵥ incV F H.y) = incV F H.y →
      (∀ z : Fin n₁ → AE F E, mat m *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z) →
      mat m' *ᵥ incV F H.x = (t : AE F E) • incV F H.x → (t : AE F E) • (mat m' *ᵥ incV F H.y) = incV F H.y →
      (∀ z : Fin n₁ → AE F E, mat m' *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z) →
      m' * (u⁻¹ * u⁻¹ * (m * u * m⁻¹)) * m'⁻¹ = (u⁻¹ * u⁻¹ * (m * u * m⁻¹)) ^ (t ^ 2) := by
  intro F E _ _ _ _ _ σ B n n₁ X X₁ H j₀ j₁ r s r₁ s₁ hH hX _ u hux hui m m' t hmx hmy hmi hm'x hm'y hm'i
  obtain ⟨c, z₀, huy⟩ := mulVec_y hH hX u hux
  exact conj_eq_pow (span_A hH hX) u hux hui c z₀ huy m m' t hmx hmy hmi hm'x hm'y hm'i

end GlobalTheory.UnipLine
