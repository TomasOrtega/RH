import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass

noncomputable section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm Matrix
open scoped Classical

namespace GlobalTheory.GLm.MirStep

variable {g : ℕ} [Fact g.Prime] {m : ℕ}

def Em (h : Mt g m) (v : Fin m → ZMod g) : Mt g (m + 1) := Matrix.of fun i j =>
  Fin.lastCases (motive := fun _ => ZMod g) (Fin.lastCases (motive := fun _ => ZMod g) 1 (fun _ => 0) j)
    (fun i' => Fin.lastCases (motive := fun _ => ZMod g) (v i') (h i') j) i

/- English proof (translation)
Simplify using `[Em]`.
-/
@[simp] theorem Em_cc (h : Mt g m) (v) (i j : Fin m) : Em h v i.castSucc j.castSucc = h i j := by simp [Em]
/- English proof (translation)
Simplify using `[Em]`.
-/
@[simp] theorem Em_cl (h : Mt g m) (v) (i : Fin m) : Em h v i.castSucc (Fin.last m) = v i := by simp [Em]
/- English proof (translation)
Simplify using `[Em]`.
-/
@[simp] theorem Em_lc (h : Mt g m) (v) (j : Fin m) : Em h v (Fin.last m) j.castSucc = 0 := by simp [Em]
/- English proof (translation)
Simplify using `[Em]`.
-/
@[simp] theorem Em_ll (h : Mt g m) (v) : Em h v (Fin.last m) (Fin.last m) = 1 := by simp [Em]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.mulVec, dotProduct]`.
-/
theorem Em_mul (h k : Mt g m) (v w) : Em h v * Em k w = Em (h * k) (h *ᵥ w + v) := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.mulVec, dotProduct]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>`. Simplify using `[Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]`.
-/
theorem Em_one : Em (1 : Mt g m) 0 = 1 := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

/- English proof (translation)
Establish `hi` using `i.2`. Establish `hj` using `j.2`. Simplify using `only [tl, entN]`. Rewrite using `[dif_pos ⟨by omega, by omega⟩]`. Both sides reduce to the same expression.
-/
theorem tl_apply (M : Mt g (m + 1)) (i j : Fin m) : tl m M i j = M i.castSucc j.castSucc := by
  have hi := i.2
  have hj := j.2
  simp only [tl, entN]
  rw [dif_pos ⟨by omega, by omega⟩]
  rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[tl_apply]`.
-/
@[simp] theorem tl_Em (h : Mt g m) (v) : tl m (Em h v) = h := by
  ext i j
  simp [tl_apply]

/- English proof (translation)
Rewrite using `[Matrix.single_one_vecMul]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `j`. Rewrite using `[Matrix.row_apply, h l j hl, Matrix.one_apply, Pi.single_apply]`.

Simplify using `[eq_comm]`. Introduce `h i j hi`. Establish `: i = l` using `Fin.ext (by omega)`. Substitute `this` using the available equality. Use `congrFun h j` as an intermediate fact.

Rewrite `this` using `[Matrix.row_apply]`. Rewrite using `[this, Matrix.one_apply, Pi.single_apply]`. Simplify using `[eq_comm]`.
-/
theorem inMir_iff_row {n : ℕ} (l : Fin n) (hl : (l : ℕ) + 1 = n) (M : Mt g n) :
    InMir M ↔ Pi.single l 1 ᵥ* M = Pi.single l 1 := by
  rw [Matrix.single_one_vecMul]
  constructor
  · intro h
    ext j
    rw [Matrix.row_apply, h l j hl, Matrix.one_apply, Pi.single_apply]
    simp [eq_comm]
  · intro h i j hi
    have : i = l := Fin.ext (by omega)
    subst this
    have := congrFun h j
    rw [Matrix.row_apply] at this
    rw [this, Matrix.one_apply, Pi.single_apply]
    simp [eq_comm]

/- English proof (translation)
Introduce `i j hi`. Establish `: i = Fin.last m` using `Fin.ext (by simp; omega)`. Substitute `this` using the available equality. Apply the tactic sequence `induction j using Fin.lastCases <;> simp [Matrix.one_apply, (Fin.castSucc_ne_last _).symm]`.
-/
theorem inMir_Em (h : Mt g m) (v) : InMir (Em h v) := by
  intro i j hi
  have : i = Fin.last m := Fin.ext (by simp; omega)
  subst this
  induction j using Fin.lastCases <;> simp [Matrix.one_apply, (Fin.castSucc_ne_last _).symm]

/- English proof (translation)
Use extensionality with `i j`. Proceed by induction on `i using Fin.lastCases`. Rewrite using `[hM _ j (by simp), inMir_Em _ _ _ j (by simp)]`. Apply the tactic sequence `induction j using Fin.lastCases <;> simp [tl_apply]`.
-/
theorem eq_Em {M : Mt g (m + 1)} (hM : InMir M) : M = Em (tl m M) fun i => M i.castSucc (Fin.last m) := by
  ext i j
  induction i using Fin.lastCases
  · rw [hM _ j (by simp), inMir_Em _ _ _ j (by simp)]
  · induction j using Fin.lastCases <;> simp [tl_apply]

def E (h : Gn g m) (v : Fin m → ZMod g) : Gn g (m + 1) where
  val := Em (h : Mt g m) v
  inv := Em ((h⁻¹ : Gn g m) : Mt g m) (-(((h⁻¹ : Gn g m) : Mt g m) *ᵥ v))
  val_inv := by
    rw [Em_mul, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Units.mul_inv]
    simp [Em_one]
  inv_val := by
    rw [Em_mul, Units.inv_mul]
    simp [Em_one]

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem E_coe (h : Gn g m) (v) : ((E h v : Gn g (m + 1)) : Mt g (m + 1)) = Em (h : Mt g m) v := rfl

/- English proof (translation)
Use `ext1`. Simplify using `[Em_mul]`.
-/
theorem E_mul (h k : Gn g m) (v w) : E h v * E k w = E (h * k) ((h : Mt g m) *ᵥ w + v) := by
  ext1
  simp [Em_mul]

/- English proof (translation)
Use `ext1`. Both sides reduce to the same expression.
-/
theorem E_inv (h : Gn g m) (v) : (E h v)⁻¹ = E h⁻¹ (-(((h⁻¹ : Gn g m) : Mt g m) *ᵥ v)) := by
  ext1
  rfl

/- English proof (translation)
Rewrite using `[E_inv, E_mul, E_mul]`. Use `congr 1`. Rewrite using `[Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_mulVec, Units.val_mul]`. Normalize the expressions using the abelian group laws.
-/
theorem E_conj (h k : Gn g m) (v w) : (E k w)⁻¹ * E h v * E k w =
    E (k⁻¹ * h * k) (((k⁻¹ : Gn g m) : Mt g m) *ᵥ ((h : Mt g m) *ᵥ w + v - w)) := by
  rw [E_inv, E_mul, E_mul]
  congr 1
  rw [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_mulVec, Units.val_mul]
  abel

/- English proof (translation)
Establish `hx' : InMir ((x⁻¹ : Gn g (m + 1)) : Mt g (m + 1))`. Rewrite `hx`, the goal using `[inMir_iff_row (Fin.last m) (by simp)]`. Use `conv_lhs => rw [← hx]`. Rewrite using `[Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]`. Establish `h1 : tl m (x : Mt g (m + 1)) * tl m ((x⁻¹ : Gn g (m + 1)) : Mt g (m + 1)) = 1`.

Use `x.mul_inv` as an intermediate fact. Rewrite `this` using `[eq_Em hx, eq_Em hx', Em_mul, ← Em_one]`. Simplify using `using congrArg (tl m) this`. Establish `hu : IsUnit (tl m (x : Mt g (m + 1)))` using `IsUnit.of_mul_eq_one _ h1`. Use `⟨hu.unit, fun i => (x : Mt g (m + 1)) i.castSucc (Fin.last m), ?_⟩` and prove the remaining obligations.

Use `ext1`. Rewrite using `[E_coe, hu.unit_spec]`. Conclude with `eq_Em hx`.
-/
theorem exists_E {x : Gn g (m + 1)} (hx : InMir (x : Mt g (m + 1))) : ∃ h v, x = E h v := by
  have hx' : InMir ((x⁻¹ : Gn g (m + 1)) : Mt g (m + 1)) := by
    rw [inMir_iff_row (Fin.last m) (by simp)] at hx ⊢
    conv_lhs => rw [← hx]
    rw [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
  have h1 : tl m (x : Mt g (m + 1)) * tl m ((x⁻¹ : Gn g (m + 1)) : Mt g (m + 1)) = 1 := by
    have := x.mul_inv
    rw [eq_Em hx, eq_Em hx', Em_mul, ← Em_one] at this
    simpa using congrArg (tl m) this
  have hu : IsUnit (tl m (x : Mt g (m + 1))) := IsUnit.of_mul_eq_one _ h1
  refine ⟨hu.unit, fun i => (x : Mt g (m + 1)) i.castSucc (Fin.last m), ?_⟩
  ext1
  rw [E_coe, hu.unit_spec]
  exact eq_Em hx

/- English proof (translation)
Rewrite using `[← Fintype.sum_prod_type']`. Use `symm`. Use `Finset.sum_of_injOn (fun p : Gn g m × (Fin m → ZMod g) => E p.1 p.2) ?_ (fun _ _ => by simp) ?_ (fun _ _ => rfl)` and prove the remaining obligations. Introduce and unpack `⟨h, v⟩ - ⟨k, w⟩ - hh`. Establish `h0 : Em (h : Mt g m) v = Em (k : Mt g m) w` using `congrArg Units.val hh`.

Use `Prod.ext (Units.ext ?_) ?_` and prove the remaining obligations. Simplify using `using congrArg (tl m) h0`. Use extensionality with `i`. Simplify using `using congrFun (congrFun h0 i.castSucc) (Fin.last m)`. Introduce `y _ hy`.

Apply `hΦ` to reduce the goal to its premises. Introduce `hy'`. Take `⟨h, v, rfl⟩` from `exists_E hy'`. Conclude with `hy ⟨(h, v), by simp, rfl⟩`.
-/
theorem sum_mir (Φ : Gn g (m + 1) → ℂ) (hΦ : ∀ y : Gn g (m + 1), ¬ InMir (y : Mt g (m + 1)) → Φ y = 0) :
    ∑ y, Φ y = ∑ h : Gn g m, ∑ v, Φ (E h v) := by
  rw [← Fintype.sum_prod_type']
  symm
  refine Finset.sum_of_injOn (fun p : Gn g m × (Fin m → ZMod g) => E p.1 p.2) ?_ (fun _ _ => by simp) ?_
    (fun _ _ => rfl)
  · rintro ⟨h, v⟩ - ⟨k, w⟩ - hh
    have h0 : Em (h : Mt g m) v = Em (k : Mt g m) w := congrArg Units.val hh
    refine Prod.ext (Units.ext ?_) ?_
    · simpa using congrArg (tl m) h0
    · ext i
      simpa using congrFun (congrFun h0 i.castSucc) (Fin.last m)
  · intro y _ hy
    apply hΦ
    intro hy'
    obtain ⟨h, v, rfl⟩ := exists_E hy'
    exact hy ⟨(h, v), by simp, rfl⟩

/- English proof (translation)
Simplify using `[toG]`.
-/
theorem toG_coe {n : ℕ} (h : Gn g n) : toG (h : Mt g n) = h := by
  simp [toG]

/- English proof (translation)
Substitute `hb` using the available equality. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `i j`. Rewrite using `[(h i j).2 (Subsingleton.elim _ _), Matrix.one_apply, if_pos (Subsingleton.elim _ _)]`.

Introduce and unpack `rfl a b`. Take `rfl : a = b` from `Subsingleton.elim _ _`. Simplify using the standard rewrite rules.
-/
theorem uni_iff {b : ℕ} (hb : b = 1) (M : Mt g b) : IsUniUp M ↔ M = 1 := by
  subst hb
  constructor
  · intro h
    ext i j
    rw [(h i j).2 (Subsingleton.elim _ _), Matrix.one_apply, if_pos (Subsingleton.elim _ _)]
  · rintro rfl a b
    obtain rfl : a = b := Subsingleton.elim _ _
    simp

/- English proof (translation)
Establish `hf : (Finset.univ.filter fun u : Gn g b => IsUniUp (u : Mt g b)) = {1}`. Use extensionality with `u`. Simplify using `[uni_iff hb]`. Substitute `hb` using the available equality. Simplify using `only [wh, tr, eU, eDat]`.

Establish `hf' : ∀ inst : DecidablePred fun u : Gn g 1 => IsUniUp (u : Mt g 1), @Finset.filter _ (fun u : Gn g 1 => IsUniUp (u : Mt g 1)) inst Finset.univ = {1}`. Introduce `inst`. Use `hf` and compare the differences between its conclusion and the goal. Rewrite using `[hf']`. Simplify using `[MonoidAlgebra.coeff_single, Finsupp.single_apply]`.
-/
theorem wh_one (ψ : AddChar (ZMod g) ℂ) {b : ℕ} (hb : b = 1) (χ : Gn g b → ℂ) : wh ψ χ = χ 1 := by
  have hf : (Finset.univ.filter fun u : Gn g b => IsUniUp (u : Mt g b)) = {1} := by
    ext u
    simp [uni_iff hb]
  subst hb
  simp only [wh, tr, eU, eDat]
  have hf' : ∀ inst : DecidablePred fun u : Gn g 1 => IsUniUp (u : Mt g 1), @Finset.filter _ (fun u : Gn g 1 => IsUniUp (u : Mt g 1)) inst Finset.univ = {1} := by
    intro inst
    convert hf
  rw [hf']
  simp [MonoidAlgebra.coeff_single, Finsupp.single_apply]

/- English proof (translation)
Rewrite using `[InR, uni_iff (by omega)]`. Establish `hb : br m (m + 1 - m) M = 1 ↔ M (Fin.last m) (Fin.last m) = 1`. Establish `: ∀ i j : Fin (m + 1 - m), br m (m + 1 - m) M i j = M (Fin.last m) (Fin.last m)`. Introduce `i j`. Establish `hi` using `i.2`.

Establish `hj` using `j.2`. Simplify using `only [br, entN]`. Rewrite using `[dif_pos ⟨by omega, by omega⟩]`. Apply the tactic sequence `congr 1 <;> exact Fin.ext (by simp; omega)`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Rewrite using `[← this ⟨0, by omega⟩ ⟨0, by omega⟩, h, Matrix.one_apply_eq]`. Introduce `h`. Use extensionality with `i j`. Establish `hi` using `i.2`.

Establish `hj` using `j.2`. Rewrite using `[this, h, Matrix.one_apply, if_pos (Fin.ext (by omega))]`. Rewrite using `[hb]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩ i j hi`.

Establish `: i = Fin.last m` using `Fin.ext (by simp; omega)`. Substitute `this` using the available equality. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => simpa using h2`. Consider the case `cast j => rw [h1 _ _ (by simp) (by simp), Matrix.one_apply_ne (Fin.castSucc_ne_last _).symm]`.

Introduce `h`. Use `⟨fun i j hj hi => ?_, by rw [h _ _ (by simp), Matrix.one_apply_eq]⟩` and prove the remaining obligations. Use `i.2` as an intermediate fact. Rewrite using `[h i j (by omega), Matrix.one_apply_ne (by intro e; subst e; omega)]`.
-/
theorem inR_iff (M : Mt g (m + 1)) : InR m M ↔ InMir M := by
  rw [InR, uni_iff (by omega)]
  have hb : br m (m + 1 - m) M = 1 ↔ M (Fin.last m) (Fin.last m) = 1 := by
    have : ∀ i j : Fin (m + 1 - m), br m (m + 1 - m) M i j = M (Fin.last m) (Fin.last m) := by
      intro i j
      have hi := i.2
      have hj := j.2
      simp only [br, entN]
      rw [dif_pos ⟨by omega, by omega⟩]
      congr 1 <;> exact Fin.ext (by simp; omega)
    constructor
    · intro h
      rw [← this ⟨0, by omega⟩ ⟨0, by omega⟩, h, Matrix.one_apply_eq]
    · intro h
      ext i j
      have hi := i.2
      have hj := j.2
      rw [this, h, Matrix.one_apply, if_pos (Fin.ext (by omega))]
  rw [hb]
  constructor
  · rintro ⟨h1, h2⟩ i j hi
    have : i = Fin.last m := Fin.ext (by simp; omega)
    subst this
    induction j using Fin.lastCases with
    | last => simpa using h2
    | cast j => rw [h1 _ _ (by simp) (by simp), Matrix.one_apply_ne (Fin.castSucc_ne_last _).symm]
  · intro h
    refine ⟨fun i j hj hi => ?_, by rw [h _ _ (by simp), Matrix.one_apply_eq]⟩
    have := i.2
    rw [h i j (by omega), Matrix.one_apply_ne (by intro e; subst e; omega)]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, r i ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hr (funext h)`. Establish `hd : (((1 : Mt g m).updateRow i r).submatrix (Equiv.swap i l) id).det ≠ 0`.

Rewrite using `[Matrix.det_permute, ← Matrix.cramer_transpose_apply, Matrix.transpose_one, Matrix.cramer_one]`. Use `mul_ne_zero ?_ hi` and prove the remaining obligations. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap i l)) with h | h <;> simp [h]`. Use `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.single_one_vecMul]`.

Use extensionality with `j`. Simplify using `[Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.row_apply]`.
-/
theorem exists_row (l : Fin m) (r : Fin m → ZMod g) (hr : r ≠ 0) :
    ∃ k : Gn g m, Pi.single l 1 ᵥ* (k : Mt g m) = r := by
  obtain ⟨i, hi⟩ : ∃ i, r i ≠ 0 := by
    by_contra h
    push Not at h
    exact hr (funext h)
  have hd : (((1 : Mt g m).updateRow i r).submatrix (Equiv.swap i l) id).det ≠ 0 := by
    rw [Matrix.det_permute, ← Matrix.cramer_transpose_apply, Matrix.transpose_one, Matrix.cramer_one]
    refine mul_ne_zero ?_ hi
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap i l)) with h | h <;> simp [h]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, ?_⟩
  rw [Matrix.single_one_vecMul]
  ext j
  simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.row_apply]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, u i ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hu (funext h)`. Take `⟨a, ha⟩` from `AddChar.ne_one_iff.1 hψ`.

Use `⟨Pi.single i (a / u i), ?_⟩` and prove the remaining obligations. Rewrite using `[dotProduct_single, mul_div_cancel₀ _ hi]` and apply the resulting hypothesis.
-/
theorem exists_psi_ne {ψ : AddChar (ZMod g) ℂ} (hψ : ψ ≠ 1) {u : Fin m → ZMod g} (hu : u ≠ 0) :
    ∃ r, ψ (u ⬝ᵥ r) ≠ 1 := by
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (funext h)
  obtain ⟨a, ha⟩ := AddChar.ne_one_iff.1 hψ
  refine ⟨Pi.single i (a / u i), ?_⟩
  rwa [dotProduct_single, mul_div_cancel₀ _ hi]

/- English proof (translation)
Introduce `h`. Use `ψ.map_add_eq_mul a (-a)` as an intermediate fact. Simplify using `[h] at this`.
-/
theorem psi_ne_zero (ψ : AddChar (ZMod g) ℂ) (a : ZMod g) : ψ a ≠ 0 := by
  intro h
  have := ψ.map_add_eq_mul a (-a)
  simp [h] at this

/- English proof (translation)
The claim follows from `pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero)`.
-/
theorem q_ne_zero : ((g : ℂ) ^ m) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero)

/- English proof (translation)
Use `split_ifs with hu`. Substitute `hu` using the available equality. Simplify using `[ZMod.card]`. Take `⟨r₀, h₀⟩` from `exists_psi_ne hψ hu`. Establish `h1 : ∑ r, ψ (r ⬝ᵥ u) = (∑ r, ψ (r ⬝ᵥ u)) * ψ (u ⬝ᵥ r₀)`.

Rewrite using `[Finset.sum_mul, ← Equiv.sum_comp (Equiv.addRight r₀)]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Simplify using `only [Equiv.coe_addRight]`. Rewrite using `[add_dotProduct, ψ.map_add_eq_mul, dotProduct_comm r₀]`. Establish `h2 : (∑ r, ψ (r ⬝ᵥ u)) * (1 - ψ (u ⬝ᵥ r₀)) = 0` using `by linear_combination h1`.

Conclude with `(mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 h₀.symm)`.
-/
theorem orth {ψ : AddChar (ZMod g) ℂ} (hψ : ψ ≠ 1) (u : Fin m → ZMod g) :
    ∑ r, ψ (r ⬝ᵥ u) = if u = 0 then (g : ℂ) ^ m else 0 := by
  split_ifs with hu
  · subst hu
    simp [ZMod.card]
  · obtain ⟨r₀, h₀⟩ := exists_psi_ne hψ hu
    have h1 : ∑ r, ψ (r ⬝ᵥ u) = (∑ r, ψ (r ⬝ᵥ u)) * ψ (u ⬝ᵥ r₀) := by
      rw [Finset.sum_mul, ← Equiv.sum_comp (Equiv.addRight r₀)]
      refine Finset.sum_congr rfl fun r _ => ?_
      simp only [Equiv.coe_addRight]
      rw [add_dotProduct, ψ.map_add_eq_mul, dotProduct_comm r₀]
    have h2 : (∑ r, ψ (r ⬝ᵥ u)) * (1 - ψ (u ⬝ᵥ r₀)) = 0 := by linear_combination h1
    exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 h₀.symm)

def fc (ψ : AddChar (ZMod g) ℂ) (F : Gn g (m + 1) → ℂ) (h : Gn g m) (r : Fin m → ZMod g) : ℂ :=
  ((g : ℂ) ^ m)⁻¹ * ∑ v, F (E h v) * (ψ (r ⬝ᵥ v))⁻¹

/- English proof (translation)
Establish `: ∀ r, fc ψ F h r * ψ (r ⬝ᵥ v) = ((g : ℂ) ^ m)⁻¹ * ∑ u, F (E h u) * ψ (r ⬝ᵥ (v - u))`. Introduce `r`. Rewrite using `[fc, mul_assoc, Finset.sum_mul]`. Use `congr 1`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations.

Rewrite using `[dotProduct_sub, AddChar.map_sub_eq_div]`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[this]`. Rewrite using `[← Finset.mul_sum, Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.mul_sum, orth hψ, sub_eq_zero]`.

Simplify using `only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Use `q_ne_zero (g := g) (m := m)` as an intermediate fact. Clear the denominators using the available nonvanishing facts.
-/
theorem inversion {ψ : AddChar (ZMod g) ℂ} (hψ : ψ ≠ 1) (F : Gn g (m + 1) → ℂ) (h : Gn g m) (v) :
    ∑ r, fc ψ F h r * ψ (r ⬝ᵥ v) = F (E h v) := by
  have : ∀ r, fc ψ F h r * ψ (r ⬝ᵥ v) = ((g : ℂ) ^ m)⁻¹ * ∑ u, F (E h u) * ψ (r ⬝ᵥ (v - u)) := by
    intro r
    rw [fc, mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [dotProduct_sub, AddChar.map_sub_eq_div]
    ring
  simp_rw [this]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, orth hψ, sub_eq_zero]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have := q_ne_zero (g := g) (m := m)
  field_simp

/- English proof (translation)
Rewrite using `[← E_conj]`. Use `hF (E k w)⁻¹ (E h v) (by rw [E_inv]; exact inMir_Em _ _) (inMir_Em _ _)` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis.
-/
theorem F_conj {F : Gn g (m + 1) → ℂ} (hF : IsMirClass F) (h k : Gn g m) (v w) :
    F (E (k⁻¹ * h * k) (((k⁻¹ : Gn g m) : Mt g m) *ᵥ ((h : Mt g m) *ᵥ w + v - w))) = F (E h v) := by
  rw [← E_conj]
  have := hF (E k w)⁻¹ (E h v) (by rw [E_inv]; exact inMir_Em _ _) (inMir_Em _ _)
  rwa [inv_inv] at this

/- English proof (translation)
Unfold `fc`. Use `congr 1`. Use `symm`. Use `Fintype.sum_bijective (fun v => ((k⁻¹ : Gn g m) : Mt g m) *ᵥ v) ?_ _ _ fun v => ?_` and prove the remaining obligations. Use `Finite.injective_iff_bijective.1 fun a b hab => ?_` and prove the remaining obligations.

Use `congrArg (fun v => (k : Mt g m) *ᵥ v) hab` as an intermediate fact. Simplify `this` using `only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Rewrite using `[← F_conj hF h k v 0, dotProduct_mulVec]`. Simplify using the standard rewrite rules.
-/
theorem fc_conj (ψ : AddChar (ZMod g) ℂ) {F : Gn g (m + 1) → ℂ} (hF : IsMirClass F) (h k : Gn g m) (r) :
    fc ψ F (k⁻¹ * h * k) r = fc ψ F h (r ᵥ* ((k⁻¹ : Gn g m) : Mt g m)) := by
  unfold fc
  congr 1
  symm
  refine Fintype.sum_bijective (fun v => ((k⁻¹ : Gn g m) : Mt g m) *ᵥ v) ?_ _ _ fun v => ?_
  · refine Finite.injective_iff_bijective.1 fun a b hab => ?_
    have := congrArg (fun v => (k : Mt g m) *ᵥ v) hab
    simpa only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] using this
  · rw [← F_conj hF h k v 0, dotProduct_mulVec]
    simp

/- English proof (translation)
Take `⟨w, hw⟩` from `exists_psi_ne hψ (sub_ne_zero.2 hr)`. Establish `h1 : ∑ v, F (E h v) * (ψ (r ⬝ᵥ v))⁻¹ = (∑ v, F (E h v) * (ψ (r ⬝ᵥ v))⁻¹) * (ψ ((r ᵥ* (h : Mt g m) - r) ⬝ᵥ w))⁻¹`. Rewrite using `[Finset.sum_mul, ← Equiv.sum_comp (Equiv.addRight ((h : Mt g m) *ᵥ w - w))]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Use `F_conj hF h 1 v w` as an intermediate fact.

Simplify using `only [inv_one, one_mul, mul_one, Units.val_one, Matrix.one_mulVec] at this`. Simplify using `only [Equiv.coe_addRight]`. Rewrite using `[show v + ((h : Mt g m) *ᵥ w - w) = (h : Mt g m) *ᵥ w + v - w by abel, this, show (h : Mt g m) *ᵥ w + v - w = v + ((h : Mt g m) *ᵥ w - w) by abel, dotProduct_add, ψ.map_add_eq_mul, dotProduct_sub, dotProduct_mulVec, sub_dotProduct]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : (∑ v, F (E h v) * (ψ (r ⬝ᵥ v))⁻¹) * (1 - (ψ ((r ᵥ* (h : Mt g m) - r) ⬝ᵥ w))⁻¹) = 0`.

Take the linear combination `h1`. Rewrite using `[fc, (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 (by simpa [eq_comm] using hw)), mul_zero]`.
-/
theorem fc_eq_zero {ψ : AddChar (ZMod g) ℂ} (hψ : ψ ≠ 1) {F : Gn g (m + 1) → ℂ} (hF : IsMirClass F)
    (h : Gn g m) (r) (hr : r ᵥ* (h : Mt g m) ≠ r) : fc ψ F h r = 0 := by
  obtain ⟨w, hw⟩ := exists_psi_ne hψ (sub_ne_zero.2 hr)
  have h1 : ∑ v, F (E h v) * (ψ (r ⬝ᵥ v))⁻¹ =
      (∑ v, F (E h v) * (ψ (r ⬝ᵥ v))⁻¹) * (ψ ((r ᵥ* (h : Mt g m) - r) ⬝ᵥ w))⁻¹ := by
    rw [Finset.sum_mul, ← Equiv.sum_comp (Equiv.addRight ((h : Mt g m) *ᵥ w - w))]
    refine Finset.sum_congr rfl fun v _ => ?_
    have := F_conj hF h 1 v w
    simp only [inv_one, one_mul, mul_one, Units.val_one, Matrix.one_mulVec] at this
    simp only [Equiv.coe_addRight]
    rw [show v + ((h : Mt g m) *ᵥ w - w) = (h : Mt g m) *ᵥ w + v - w by abel, this,
      show (h : Mt g m) *ᵥ w + v - w = v + ((h : Mt g m) *ᵥ w - w) by abel, dotProduct_add, ψ.map_add_eq_mul,
      dotProduct_sub, dotProduct_mulVec, sub_dotProduct]
    ring
  have h2 : (∑ v, F (E h v) * (ψ (r ⬝ᵥ v))⁻¹) * (1 - (ψ ((r ᵥ* (h : Mt g m) - r) ⬝ᵥ w))⁻¹) = 0 := by
    linear_combination h1
  rw [fc, (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 (by simpa [eq_comm] using hw)), mul_zero]

/- English proof (translation)
Rewrite using `[sum_mir _ fun y hy => if_neg fun hh => hy ((inR_iff _).1 hh.1)]`. Simplify using `only [E_coe, inR_iff, inMir_Em, tl_Em, true_and, Units.val_inj]`. Rewrite using `[Finset.sum_comm]`. Simplify using the standard rewrite rules.
-/
theorem sum_fib (Φ : Gn g (m + 1) → ℂ) (h : Gn g m) :
    (∑ x : Gn g (m + 1), if InR m (x : Mt g (m + 1)) ∧ tl m (x : Mt g (m + 1)) = (h : Mt g m) then Φ x else 0) =
      ∑ v, Φ (E h v) := by
  rw [sum_mir _ fun y hy => if_neg fun hh => hy ((inR_iff _).1 hh.1)]
  simp only [E_coe, inR_iff, inMir_Em, tl_Em, true_and, Units.val_inj]
  rw [Finset.sum_comm]
  simp

/- English proof (translation)
Rewrite using `[der, wh_one ψ (by omega), res, fc]`. Establish `e : m * (m + 1 - m) = m` using `by simp`. Rewrite using `[e]`. Use `congr 1`. Simplify using `only [zero_dotProduct, AddChar.map_zero_eq_one, inv_one, mul_one]`.

Rewrite using `[← sum_fib]`. Use `Finset.sum_congr rfl fun x _ => if_congr ?_ rfl rfl` and prove the remaining obligations. Rewrite using `[InR, uni_iff (by omega), Units.val_one]`. The claim follows by propositional logic.
-/
theorem der_eq (ψ : AddChar (ZMod g) ℂ) (F : Gn g (m + 1) → ℂ) (h : Gn g m) : der ψ m F h = fc ψ F h 0 := by
  rw [der, wh_one ψ (by omega), res, fc]
  have e : m * (m + 1 - m) = m := by simp
  rw [e]
  congr 1
  simp only [zero_dotProduct, AddChar.map_zero_eq_one, inv_one, mul_one]
  rw [← sum_fib]
  refine Finset.sum_congr rfl fun x _ => if_congr ?_ rfl rfl
  rw [InR, uni_iff (by omega), Units.val_one]
  tauto

/- English proof (translation)
Rewrite using `[single_dotProduct, one_mul, ← Em_cl h v l, entN, dif_pos ⟨by omega, by omega⟩]`. Use `congr 1`. Conclude with `Fin.ext (by simp; omega)`.
-/
theorem entN_Em (l : Fin m) (hl : (l : ℕ) + 1 = m) (h : Mt g m) (v) :
    entN (Em h v) (m - 1) m = Pi.single l 1 ⬝ᵥ v := by
  rw [single_dotProduct, one_mul, ← Em_cl h v l, entN, dif_pos ⟨by omega, by omega⟩]
  congr 1
  exact Fin.ext (by simp; omega)

/- English proof (translation)
Rewrite using `[tail, fc, sum_fib (fun x => F x * (ψ (supFrom (m - 1) (x : Mt g (m + 1))))⁻¹)]`. Establish `e : m * (m + 1 - m) + (m + 1 - m) * (m + 1 - m - 1) / 2 = m` using `by simp`. Rewrite using `[e]`. Use `congr 1`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations.

Rewrite using `[← entN_Em l hl (h : Mt g m) v, supFrom]`. Establish `: Finset.Ico (m - 1) (m + 1 - 1) = {m - 1}`. Use extensionality with `j`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Rewrite using `[this, Finset.sum_singleton, show m - 1 + 1 = m by omega, E_coe]`.
-/
theorem tail_eq (l : Fin m) (hl : (l : ℕ) + 1 = m) (ψ : AddChar (ZMod g) ℂ) (F : Gn g (m + 1) → ℂ) (h : Gn g m) :
    tail ψ m F h = fc ψ F h (Pi.single l 1) := by
  rw [tail, fc, sum_fib (fun x => F x * (ψ (supFrom (m - 1) (x : Mt g (m + 1))))⁻¹)]
  have e : m * (m + 1 - m) + (m + 1 - m) * (m + 1 - m - 1) / 2 = m := by simp
  rw [e]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← entN_Em l hl (h : Mt g m) v, supFrom]
  have : Finset.Ico (m - 1) (m + 1 - 1) = {m - 1} := by
    ext j
    simp
    omega
  rw [this, Finset.sum_singleton, show m - 1 + 1 = m by omega, E_coe]

/- English proof (translation)
Unfold `indR`. Rewrite using `[Finset.natCast_card_filter, sum_mir _ fun y hy => if_neg fun hh => hy ((inR_iff _).1 hh), sum_mir _ fun y hy => if_neg fun hh => hy hh.1]`. Simplify using `only [E_conj]`. Simplify using `only [E_coe, inR_iff, inMir_Em, tl_Em, true_and, if_true, toG_coe, der_eq, fc_conj ψ hF, supFrom, Nat.add_sub_cancel, Finset.Ico_self, Finset.sum_empty, AddChar.map_zero_eq_one, mul_one, Matrix.zero_vecMul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Establish `h1 : (Fintype.card (Gn g m) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`.

Establish `h2 : (Fintype.card (Fin m → ZMod g) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Clear the denominators using the available nonvanishing facts.
-/
theorem indR_eq (ψ : AddChar (ZMod g) ℂ) {F : Gn g (m + 1) → ℂ} (hF : IsMirClass F) (h : Gn g m) (v) :
    indR ψ m (m + 1) (der ψ m F) (E h v) = fc ψ F h 0 := by
  unfold indR
  rw [Finset.natCast_card_filter, sum_mir _ fun y hy => if_neg fun hh => hy ((inR_iff _).1 hh),
    sum_mir _ fun y hy => if_neg fun hh => hy hh.1]
  simp only [E_conj]
  simp only [E_coe, inR_iff, inMir_Em, tl_Em, true_and, if_true, toG_coe, der_eq, fc_conj ψ hF,
    supFrom, Nat.add_sub_cancel, Finset.Ico_self, Finset.sum_empty, AddChar.map_zero_eq_one, mul_one,
    Matrix.zero_vecMul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h1 : (Fintype.card (Gn g m) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h2 : (Fintype.card (Fin m → ZMod g) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp

/- English proof (translation)
Use `(Equiv.sum_comp (Equiv.inv (Gn g m)) fun k : Gn g m => φ (Pi.single l 1 ᵥ* (k : Mt g m))).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, ← Finset.sum_fiberwise Finset.univ fun k : Gn g m => Pi.single l 1 ᵥ* (k : Mt g m)]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Use `split_ifs with hr`. Substitute `hr` using the available equality.

Rewrite using `[mul_zero]`. Use `Finset.sum_eq_zero fun k hk => ?_` and prove the remaining obligations. Use `congrArg (fun v => v ᵥ* ((k⁻¹ : Gn g m) : Mt g m)) (Finset.mem_filter.1 hk).2` as an intermediate fact. Simplify using `only [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one, Matrix.zero_vecMul] at this`. Simplify using `using congrFun this l`.

Take `⟨k₀, rfl⟩` from `exists_row l r hr`. Rewrite using `[Finset.sum_filter, Finset.sum_mul, ← Equiv.sum_comp (Equiv.mulRight k₀)]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `: Pi.single l 1 ᵥ* ((k * k₀ : Gn g m) : Mt g m) = Pi.single l 1 ᵥ* (k₀ : Mt g m) ↔ InMir (k : Mt g m)`. Rewrite using `[inMir_iff_row l hl, Units.val_mul, ← Matrix.vecMul_vecMul]`.

Use `⟨fun e => ?_, fun e => by rw [e]⟩` and prove the remaining obligations. Use `congrArg (fun v => v ᵥ* ((k₀⁻¹ : Gn g m) : Mt g m)) e` as an intermediate fact. Simplify `this` using `only [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one, mul_assoc, mul_one]`. Distinguish the cases in `hk : InMir (k : Mt g m)`. Use `(if_pos (this.2 hk)).trans ?_` and prove the remaining obligations.

Rewrite using `[if_pos hk, one_mul]`. Conclude with `congrArg φ (this.2 hk)`. Use `(if_neg (fun e => hk (this.1 e))).trans ?_` and prove the remaining obligations. Rewrite using `[if_neg hk, zero_mul]`.
-/
theorem sum_rows (l : Fin m) (hl : (l : ℕ) + 1 = m) (φ : (Fin m → ZMod g) → ℂ) :
    ∑ k : Gn g m, φ (Pi.single l 1 ᵥ* ((k⁻¹ : Gn g m) : Mt g m)) =
      (∑ k : Gn g m, if InMir (k : Mt g m) then (1 : ℂ) else 0) * ∑ r, if r = 0 then 0 else φ r := by
  refine (Equiv.sum_comp (Equiv.inv (Gn g m)) fun k : Gn g m => φ (Pi.single l 1 ᵥ* (k : Mt g m))).trans ?_
  rw [Finset.mul_sum,
    ← Finset.sum_fiberwise Finset.univ fun k : Gn g m => Pi.single l 1 ᵥ* (k : Mt g m)]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs with hr
  · subst hr
    rw [mul_zero]
    refine Finset.sum_eq_zero fun k hk => ?_
    have := congrArg (fun v => v ᵥ* ((k⁻¹ : Gn g m) : Mt g m)) (Finset.mem_filter.1 hk).2
    simp only [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one, Matrix.zero_vecMul] at this
    simpa using congrFun this l
  · obtain ⟨k₀, rfl⟩ := exists_row l r hr
    rw [Finset.sum_filter, Finset.sum_mul, ← Equiv.sum_comp (Equiv.mulRight k₀)]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : Pi.single l 1 ᵥ* ((k * k₀ : Gn g m) : Mt g m) = Pi.single l 1 ᵥ* (k₀ : Mt g m) ↔ InMir (k : Mt g m) := by
      rw [inMir_iff_row l hl, Units.val_mul, ← Matrix.vecMul_vecMul]
      refine ⟨fun e => ?_, fun e => by rw [e]⟩
      have := congrArg (fun v => v ᵥ* ((k₀⁻¹ : Gn g m) : Mt g m)) e
      simpa only [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one, mul_assoc, mul_one] using this
    by_cases hk : InMir (k : Mt g m)
    · refine (if_pos (this.2 hk)).trans ?_
      rw [if_pos hk, one_mul]
      exact congrArg φ (this.2 hk)
    · refine (if_neg (fun e => hk (this.1 e))).trans ?_
      rw [if_neg hk, zero_mul]

/- English proof (translation)
Unfold `indV`. Rewrite using `[Finset.natCast_card_filter, sum_mir _ fun y hy => if_neg fun hh => hy hh.1, sum_mir _ fun y hy => if_neg fun hh => hy hh.1]`. Simplify using `only [E_conj]`. Simplify using `only [E_coe, inMir_Em, tl_Em, true_and, toG_coe, tail_eq l hl, fc_conj ψ hF, entN_Em l hl]`. Establish `key : ∀ (k : Gn g m) (w : Fin m → ZMod g), (if InMir ((k⁻¹ * h * k : Gn g m) : Mt g m) then fc ψ F h (Pi.single l 1 ᵥ* ((k⁻¹ : Gn g m) : Mt g m)) * ψ (Pi.single l 1 ⬝ᵥ ((k⁻¹ : Gn g m) : Mt g m) *ᵥ ((h : Mt g m) *ᵥ w + v - w)) else 0) = fc ψ F h (Pi.single l 1 ᵥ* ((k⁻¹ : Gn g m) : …`.

Introduce `k w`. Establish `hiff : InMir ((k⁻¹ * h * k : Gn g m) : Mt g m) ↔ (Pi.single l 1 ᵥ* ((k⁻¹ : Gn g m) : Mt g m)) ᵥ* (h : Mt g m) = Pi.single l 1 ᵥ* ((k⁻¹ : Gn g m) : Mt g m)`. Rewrite using `[inMir_iff_row l hl, Units.val_mul, Units.val_mul]`. Prove the components needed by the constructor for the conclusion. Introduce `e`.

Use `congrArg (fun v => v ᵥ* ((k⁻¹ : Gn g m) : Mt g m)) e` as an intermediate fact. Simplify `this` using `only [Matrix.vecMul_vecMul, Units.mul_inv, mul_assoc, mul_one]`. Introduce `e`. Use `congrArg (fun v => v ᵥ* (k : Mt g m)) e` as an intermediate fact. Simplify `this` using `only [Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]`.

Use `split_ifs with hk`. Rewrite using `[dotProduct_mulVec, dotProduct_sub, dotProduct_add, dotProduct_mulVec, hiff.1 hk, add_sub_cancel_left]`. Rewrite using `[fc_eq_zero hψ hF h _ (fun e => hk (hiff.2 e)), zero_mul]`. Simplify using `only [key, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Rewrite using `[← Finset.mul_sum, ← Finset.mul_sum, sum_rows l hl fun r => fc ψ F h r * ψ (r ⬝ᵥ v)]`.

Establish `h2 : (Fintype.card (Fin m → ZMod g) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Establish `h1 : (∑ k : Gn g m, if InMir (k : Mt g m) then (1 : ℂ) else 0) ≠ 0`. Rewrite using `[← Finset.natCast_card_filter, Nat.cast_ne_zero, Finset.card_ne_zero]`. Conclude with `⟨1, by simp [inMir_one]⟩`. Clear the denominators using the available nonvanishing facts.
-/
theorem indV_eq (l : Fin m) (hl : (l : ℕ) + 1 = m) {ψ : AddChar (ZMod g) ℂ} (hψ : ψ ≠ 1)
    {F : Gn g (m + 1) → ℂ} (hF : IsMirClass F) (h : Gn g m) (v) :
    indV ψ m (tail ψ m F) (E h v) = ∑ r, if r = 0 then 0 else fc ψ F h r * ψ (r ⬝ᵥ v) := by
  unfold indV
  rw [Finset.natCast_card_filter, sum_mir _ fun y hy => if_neg fun hh => hy hh.1,
    sum_mir _ fun y hy => if_neg fun hh => hy hh.1]
  simp only [E_conj]
  simp only [E_coe, inMir_Em, tl_Em, true_and, toG_coe, tail_eq l hl, fc_conj ψ hF, entN_Em l hl]
  have key : ∀ (k : Gn g m) (w : Fin m → ZMod g),
      (if InMir ((k⁻¹ * h * k : Gn g m) : Mt g m) then fc ψ F h (Pi.single l 1 ᵥ* ((k⁻¹ : Gn g m) : Mt g m)) *
        ψ (Pi.single l 1 ⬝ᵥ ((k⁻¹ : Gn g m) : Mt g m) *ᵥ ((h : Mt g m) *ᵥ w + v - w)) else 0) =
      fc ψ F h (Pi.single l 1 ᵥ* ((k⁻¹ : Gn g m) : Mt g m)) *
        ψ ((Pi.single l 1 ᵥ* ((k⁻¹ : Gn g m) : Mt g m)) ⬝ᵥ v) := by
    intro k w
    have hiff : InMir ((k⁻¹ * h * k : Gn g m) : Mt g m) ↔
        (Pi.single l 1 ᵥ* ((k⁻¹ : Gn g m) : Mt g m)) ᵥ* (h : Mt g m) =
          Pi.single l 1 ᵥ* ((k⁻¹ : Gn g m) : Mt g m) := by
      rw [inMir_iff_row l hl, Units.val_mul, Units.val_mul]
      constructor
      · intro e
        have := congrArg (fun v => v ᵥ* ((k⁻¹ : Gn g m) : Mt g m)) e
        simpa only [Matrix.vecMul_vecMul, Units.mul_inv, mul_assoc, mul_one] using this
      · intro e
        have := congrArg (fun v => v ᵥ* (k : Mt g m)) e
        simpa only [Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one] using this
    split_ifs with hk
    · rw [dotProduct_mulVec, dotProduct_sub, dotProduct_add, dotProduct_mulVec, hiff.1 hk, add_sub_cancel_left]
    · rw [fc_eq_zero hψ hF h _ (fun e => hk (hiff.2 e)), zero_mul]
  simp only [key, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum, sum_rows l hl fun r => fc ψ F h r * ψ (r ⬝ᵥ v)]
  have h2 : (Fintype.card (Fin m → ZMod g) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h1 : (∑ k : Gn g m, if InMir (k : Mt g m) then (1 : ℂ) else 0) ≠ 0 := by
    rw [← Finset.natCast_card_filter, Nat.cast_ne_zero, Finset.card_ne_zero]
    exact ⟨1, by simp [inMir_one]⟩
  field_simp

/- English proof (translation)
Introduce `g _ ψ hψ m F hm hF p hp`. Take `⟨h, v, rfl⟩` from `exists_E hp`. Rewrite using `[indR_eq ψ hF, indV_eq ⟨m - 1, by omega⟩ (by simp; omega) hψ hF, ← inversion hψ F h v]`. Establish `: fc ψ F h 0 = ∑ r, if r = 0 then fc ψ F h r * ψ (r ⬝ᵥ v) else 0` using `by simp`. Rewrite using `[this, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem mir_step : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) , ψ ≠ 1 → ∀ (m : ℕ) (F : Gn g (m + 1) → ℂ),
    1 ≤ m → IsMirClass F → ∀ p : Gn g (m + 1), InMir (p : Mt g (m + 1)) →
      F p = indR ψ m (m + 1) (der ψ m F) p + indV ψ m (tail ψ m F) p := by
  intro g _ ψ hψ m F hm hF p hp
  obtain ⟨h, v, rfl⟩ := exists_E hp
  rw [indR_eq ψ hF, indV_eq ⟨m - 1, by omega⟩ (by simp; omega) hψ hF, ← inversion hψ F h v]
  have : fc ψ F h 0 = ∑ r, if r = 0 then fc ψ F h r * ψ (r ⬝ᵥ v) else 0 := by simp
  rw [this, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> simp

end GlobalTheory.GLm.MirStep
