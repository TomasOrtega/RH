import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.HkC

def lA (g : Matrix (Fin 2) (Fin 2) ℤ) : ℂ[X] := C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)

def lB (g : Matrix (Fin 2) (Fin 2) ℤ) : ℂ[X] := C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)

/- English proof (translation)
Rewrite using `[slP, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, lcoeff_apply, LinearMap.toSpanSingleton_apply, ← C_mul']`. Both sides reduce to the same expression.
-/
theorem polySlash_apply (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p = ∑ i ∈ Finset.range (w + 1), C (p.coeff i) * (lA g ^ i * lB g ^ (w - i)) := by
  rw [slP, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.comp_apply, lcoeff_apply, LinearMap.toSpanSingleton_apply, ← C_mul']
  rfl

/- English proof (translation)
Rewrite using `[polySlash_apply, Finset.sum_eq_single k]`. Simplify using the standard rewrite rules. Introduce `i _ hik`. Simplify using `[coeff_monomial, Ne.symm hik]`. Introduce `h`.

Simplify using `at h`. Use linear arithmetic over natural numbers and integers.
-/
theorem polySlash_monomial (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (k : ℕ) (c : ℂ) (hk : k ≤ w) :
    slP w g (monomial k c) = C c * (lA g ^ k * lB g ^ (w - k)) := by
  rw [polySlash_apply, Finset.sum_eq_single k]
  · simp
  · intro i _ hik; simp [coeff_monomial, Ne.symm hik]
  · intro h; simp at h; omega

/- English proof (translation)
Rewrite using `[mem_degreeLT]`. Distinguish the cases in `hp : p = 0`. Substitute `hp` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[degree_eq_natDegree hp]`.

Use `norm_cast`. Use linear arithmetic over natural numbers and integers.
-/
theorem mem_degLT_iff {w : ℕ} {p : ℂ[X]} : p ∈ degreeLT ℂ (w + 1) ↔ p.natDegree ≤ w := by
  rw [mem_degreeLT]
  by_cases hp : p = 0
  · subst hp; simp
  · rw [degree_eq_natDegree hp]; norm_cast; omega

/- English proof (translation)
The claim follows from `natDegree_linear_le`.
-/
theorem natDegree_lA (g : Matrix (Fin 2) (Fin 2) ℤ) : (lA g).natDegree ≤ 1 := natDegree_linear_le
/- English proof (translation)
The claim follows from `natDegree_linear_le`.
-/
theorem natDegree_lB (g : Matrix (Fin 2) (Fin 2) ℤ) : (lB g).natDegree ≤ 1 := natDegree_linear_le

/- English proof (translation)
Rewrite using `[polySlash_apply]`. Apply `natDegree_sum_le_of_forall_le` to reduce the goal to its premises. Introduce `i hi`. Establish `hi' : i ≤ w` using `by simp at hi; omega`. Use `(natDegree_C_mul_le _ _).trans ?_` and prove the remaining obligations.

Use `natDegree_mul_le.trans ?_` and prove the remaining obligations. Establish `h1` using `natDegree_pow_le_of_le i (natDegree_lA g)`. Establish `h2` using `natDegree_pow_le_of_le (w - i) (natDegree_lB g)`. Use linear arithmetic over natural numbers and integers.
-/
theorem natDegree_slP_le (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) : (slP w g p).natDegree ≤ w := by
  rw [polySlash_apply]
  apply natDegree_sum_le_of_forall_le
  intro i hi
  have hi' : i ≤ w := by simp at hi; omega
  refine (natDegree_C_mul_le _ _).trans ?_
  refine natDegree_mul_le.trans ?_
  have h1 := natDegree_pow_le_of_le i (natDegree_lA g)
  have h2 := natDegree_pow_le_of_le (w - i) (natDegree_lB g)
  omega

/- English proof (translation)
Establish `eq` using `as_sum_range' q (m + 1) (by omega)`. Establish `er` using `as_sum_range' r (n + 1) (by omega)`. Rewrite using `[polySlash_apply m h q, polySlash_apply n h r, Finset.sum_mul_sum]`. Use `conv_lhs => rw [eq, er, Finset.sum_mul_sum]`. Simplify using `only [map_sum]`.

Use `Finset.sum_congr rfl fun s hs => Finset.sum_congr rfl fun t ht => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_range] at hs ht`. Rewrite using `[monomial_mul_monomial, polySlash_monomial _ _ _ _ (by omega)]`. Establish `e : m + n - (s + t) = (m - s) + (n - t)` using `by omega`. Rewrite using `[e, C_mul, pow_add, pow_add]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem polySlash_mul (h : Matrix (Fin 2) (Fin 2) ℤ) (m n : ℕ) (q r : ℂ[X]) (hq : q.natDegree ≤ m)
    (hr : r.natDegree ≤ n) : slP (m + n) h (q * r) = slP m h q * slP n h r := by
  have eq := as_sum_range' q (m + 1) (by omega)
  have er := as_sum_range' r (n + 1) (by omega)
  rw [polySlash_apply m h q, polySlash_apply n h r, Finset.sum_mul_sum]
  conv_lhs => rw [eq, er, Finset.sum_mul_sum]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun s hs => Finset.sum_congr rfl fun t ht => ?_
  simp only [Finset.mem_range] at hs ht
  rw [monomial_mul_monomial, polySlash_monomial _ _ _ _ (by omega)]
  have e : m + n - (s + t) = (m - s) + (n - t) := by omega
  rw [e, C_mul, pow_add, pow_add]; ring

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp [polySlash_apply]`. Consider the case `succ k ih`. Rewrite using `[pow_succ, pow_succ, Nat.mul_succ, polySlash_mul h (m * k) m (q ^ k) q ((natDegree_pow_le_of_le k hq).trans (le_of_eq (mul_comm _ _))) hq, ih]`.
-/
theorem polySlash_pow (h : Matrix (Fin 2) (Fin 2) ℤ) (m : ℕ) (q : ℂ[X]) (hq : q.natDegree ≤ m) :
    ∀ k : ℕ, slP (m * k) h (q ^ k) = (slP m h q) ^ k := by
  intro k
  induction k with
  | zero => simp [polySlash_apply]
  | succ k ih =>
    rw [pow_succ, pow_succ, Nat.mul_succ,
      polySlash_mul h (m * k) m (q ^ k) q ((natDegree_pow_le_of_le k hq).trans (le_of_eq (mul_comm _ _))) hq, ih]

/- English proof (translation)
Establish `c0 : (lA g).coeff 0 = ((g 0 1 : ℤ) : ℂ)` using `by rw [lA, coeff_add, coeff_C_mul_X, coeff_C]; simp`. Establish `c1 : (lA g).coeff 1 = ((g 0 0 : ℤ) : ℂ)` using `by rw [lA, coeff_add, coeff_C_mul_X, coeff_C]; simp`. Rewrite using `[polySlash_apply, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, c0, c1]`. Simplify using `only [lA, lB, Matrix.mul_apply, Fin.sum_univ_two]`. Use `push_cast`.

Simplify using `only [C_add, C_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem polySlash_one_num (g h : Matrix (Fin 2) (Fin 2) ℤ) : slP 1 h (lA g) = lA (g * h) := by
  have c0 : (lA g).coeff 0 = ((g 0 1 : ℤ) : ℂ) := by rw [lA, coeff_add, coeff_C_mul_X, coeff_C]; simp
  have c1 : (lA g).coeff 1 = ((g 0 0 : ℤ) : ℂ) := by rw [lA, coeff_add, coeff_C_mul_X, coeff_C]; simp
  rw [polySlash_apply, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, c0, c1]
  simp only [lA, lB, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  simp only [C_add, C_mul]
  ring

/- English proof (translation)
Establish `c0 : (lB g).coeff 0 = ((g 1 1 : ℤ) : ℂ)` using `by rw [lB, coeff_add, coeff_C_mul_X, coeff_C]; simp`. Establish `c1 : (lB g).coeff 1 = ((g 1 0 : ℤ) : ℂ)` using `by rw [lB, coeff_add, coeff_C_mul_X, coeff_C]; simp`. Rewrite using `[polySlash_apply, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, c0, c1]`. Simplify using `only [lA, lB, Matrix.mul_apply, Fin.sum_univ_two]`. Use `push_cast`.

Simplify using `only [C_add, C_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem polySlash_one_denom (g h : Matrix (Fin 2) (Fin 2) ℤ) : slP 1 h (lB g) = lB (g * h) := by
  have c0 : (lB g).coeff 0 = ((g 1 1 : ℤ) : ℂ) := by rw [lB, coeff_add, coeff_C_mul_X, coeff_C]; simp
  have c1 : (lB g).coeff 1 = ((g 1 0 : ℤ) : ℂ) := by rw [lB, coeff_add, coeff_C_mul_X, coeff_C]; simp
  rw [polySlash_apply, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, c0, c1]
  simp only [lA, lB, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  simp only [C_add, C_mul]
  ring

/- English proof (translation)
Use `conv_lhs => rw [as_sum_range' p (w + 1) (by omega)]`. Use `conv_rhs => rw [as_sum_range' p (w + 1) (by omega)]`. Simplify using `only [map_sum]`. Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_range] at hk`.

Rewrite using `[polySlash_monomial _ _ _ _ (by omega), polySlash_monomial _ _ _ _ (by omega), C_mul', map_smul, C_mul']`. Use `congr 1`. Take `⟨j, rfl⟩ : ∃ j, w = k + j` from `⟨w - k, by omega⟩`. Rewrite using `[Nat.add_sub_cancel_left, polySlash_mul h k j _ _ ((natDegree_pow_le_of_le k (natDegree_lA g)).trans (by omega)) ((natDegree_pow_le_of_le j (natDegree_lB g)).trans (by omega))]`. Establish `hA` using `polySlash_pow h 1 (lA g) (natDegree_lA g) k`.

Establish `hB` using `polySlash_pow h 1 (lB g) (natDegree_lB g) j`. Rewrite `hA`, `hB` using `[one_mul]`. Rewrite using `[hA, hB, polySlash_one_num, polySlash_one_denom]`.
-/
theorem polySlash_comp (w : ℕ) (g h : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) (hp : p.natDegree ≤ w) :
    slP w h (slP w g p) = slP w (g * h) p := by
  conv_lhs => rw [as_sum_range' p (w + 1) (by omega)]
  conv_rhs => rw [as_sum_range' p (w + 1) (by omega)]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hk
  rw [polySlash_monomial _ _ _ _ (by omega), polySlash_monomial _ _ _ _ (by omega), C_mul', map_smul, C_mul']
  congr 1
  obtain ⟨j, rfl⟩ : ∃ j, w = k + j := ⟨w - k, by omega⟩
  rw [Nat.add_sub_cancel_left,
    polySlash_mul h k j _ _ ((natDegree_pow_le_of_le k (natDegree_lA g)).trans (by omega))
      ((natDegree_pow_le_of_le j (natDegree_lB g)).trans (by omega))]
  have hA := polySlash_pow h 1 (lA g) (natDegree_lA g) k
  have hB := polySlash_pow h 1 (lB g) (natDegree_lB g) j
  rw [one_mul] at hA hB
  rw [hA, hB, polySlash_one_num, polySlash_one_denom]

/- English proof (translation)
Rewrite using `[polySlash_apply, polySlash_apply]`. Simplify using `[Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, lA, lB, coeff_map]`.
-/
theorem polySlash_map (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (q : ℂ[X]) :
    (slP w g q).map (starRingEnd ℂ) = slP w g (q.map (starRingEnd ℂ)) := by
  rw [polySlash_apply, polySlash_apply]
  simp [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, lA, lB, coeff_map]

end GlobalTheory.HeckeFamilyMatrices.HkC

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.HkC

variable {Γ : Subgroup SL(2, ℤ)} {α : Matrix (Fin 2) (Fin 2) ℤ} {ι : Type} {δ : ι → Matrix (Fin 2) (Fin 2) ℤ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem matm (a b : Γ) : mat ↑(a * b) = mat ↑a * mat ↑b := rfl

/- English proof (translation)
The claim follows from `γ.2`.
-/
theorem det_mat (γ : SL(2, ℤ)) : (mat γ).det = 1 := γ.2

/- English proof (translation)
Take `⟨γ1, γ2, h⟩` from `hD.1 i`. Rewrite using `[h, Matrix.det_mul, Matrix.det_mul, det_mat, det_mat]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_rep (hD : IsDCReps Γ α δ) (i : ι) : (δ i).det = α.det := by
  obtain ⟨γ1, γ2, h⟩ := hD.1 i
  rw [h, Matrix.det_mul, Matrix.det_mul, det_mat, det_mat]; ring

/- English proof (translation)
Establish `h2 : M * (D * D.adjugate) = N * (D * D.adjugate)` using `by rw [← mul_assoc, h, mul_assoc]`. Rewrite `h2` using `[Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_smul, mul_one, mul_one]`. Conclude with `smul_right_injective _ hD h2`.
-/
theorem cancel_right {M N D : Matrix (Fin 2) (Fin 2) ℤ} (hD : D.det ≠ 0) (h : M * D = N * D) : M = N := by
  have h2 : M * (D * D.adjugate) = N * (D * D.adjugate) := by rw [← mul_assoc, h, mul_assoc]
  rw [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_smul, mul_one, mul_one] at h2
  exact smul_right_injective _ hD h2

/- English proof (translation)
Take `⟨γ1, γ2, hj⟩` from `hD.1 j`. Take `⟨i, _, hi⟩` from `hD.2 (a * γ1) γ2`. Establish `e1 : mat ↑(a * γ1) * α * mat γ2 = mat a * δ j` using `by rw [hj, matm]; simp only [mul_assoc]`. Establish `hjk : j = k` using `(hi j ⟨a, e1⟩).trans (hi k ⟨b, e1.trans h⟩).symm`. Substitute `hjk` using the available equality.

Use `⟨rfl, ?_⟩` and prove the remaining obligations. Use `cancel_right (by rw [det_rep hD]; exact hα) h` as an intermediate fact. Conclude with `Subtype.ext (Subtype.ext this)`.
-/
theorem rep_uniq (hD : IsDCReps Γ α δ) (hα : α.det ≠ 0) {a b : Γ} {j k : ι}
    (h : mat a * δ j = mat b * δ k) : j = k ∧ a = b := by
  obtain ⟨γ1, γ2, hj⟩ := hD.1 j
  obtain ⟨i, _, hi⟩ := hD.2 (a * γ1) γ2
  have e1 : mat ↑(a * γ1) * α * mat γ2 = mat a * δ j := by rw [hj, matm]; simp only [mul_assoc]
  have hjk : j = k := (hi j ⟨a, e1⟩).trans (hi k ⟨b, e1.trans h⟩).symm
  subst hjk
  refine ⟨rfl, ?_⟩
  have := cancel_right (by rw [det_rep hD]; exact hα) h
  exact Subtype.ext (Subtype.ext this)

/- English proof (translation)
Establish `hx : ∀ i, ∃ j, ∃ g : Γ, δ i * mat γ = mat g * δ j`. Introduce `i`. Take `⟨γ1, γ2, hi⟩` from `hD.1 i`. Take `⟨j, ⟨g, hg⟩, _⟩` from `hD.2 γ1 (γ2 * γ)`. Conclude with `⟨j, g, by rw [hi, ← hg, matm]; simp only [mul_assoc]⟩`.

Use `choose f g hfg using hx`. Establish `hinj : Function.Injective f`. Introduce `i k hik`. Establish `h1` using `hfg i`. Establish `h2` using `hfg k`.

Rewrite `h1` using `[hik]`. Establish `hγ : (mat γ).det ≠ 0` using `by rw [det_mat]; norm_num`. Establish `e : mat ↑(g k * (g i)⁻¹) * δ i = mat ↑(1 : Γ) * δ k`. Apply `cancel_right hγ` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[matm]`. Simplify using `only [mul_assoc]`. Use `_ = mat (g k) * mat ↑(g i)⁻¹ * (mat (g i) * δ (f k)) := by rw [h1]`. Use `_ = mat (g k) * mat ↑((g i)⁻¹ * g i) * δ (f k) := by rw [matm]; simp only [mul_assoc]`. Use `_ = mat (g k) * δ (f k) := by simp`.

Use `_ = δ k * mat γ := h2.symm`. Use `_ = mat ↑(1 : Γ) * δ k * mat γ := by simp`. Conclude with `(rep_uniq hD hα e).1`. Conclude with `⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), g, hfg⟩`.
-/
theorem rep_exists [Fintype ι] (hD : IsDCReps Γ α δ) (hα : α.det ≠ 0) (γ : Γ) :
    ∃ π : Equiv.Perm ι, ∃ g : ι → Γ, ∀ i, δ i * mat γ = mat (g i) * δ (π i) := by
  have hx : ∀ i, ∃ j, ∃ g : Γ, δ i * mat γ = mat g * δ j := by
    intro i
    obtain ⟨γ1, γ2, hi⟩ := hD.1 i
    obtain ⟨j, ⟨g, hg⟩, _⟩ := hD.2 γ1 (γ2 * γ)
    exact ⟨j, g, by rw [hi, ← hg, matm]; simp only [mul_assoc]⟩
  choose f g hfg using hx
  have hinj : Function.Injective f := by
    intro i k hik
    have h1 := hfg i
    have h2 := hfg k
    rw [hik] at h1
    have hγ : (mat γ).det ≠ 0 := by rw [det_mat]; norm_num
    have e : mat ↑(g k * (g i)⁻¹) * δ i = mat ↑(1 : Γ) * δ k := by
      apply cancel_right hγ
      calc mat ↑(g k * (g i)⁻¹) * δ i * mat γ = mat (g k) * mat ↑(g i)⁻¹ * (δ i * mat γ) := by
              rw [matm]; simp only [mul_assoc]
        _ = mat (g k) * mat ↑(g i)⁻¹ * (mat (g i) * δ (f k)) := by rw [h1]
        _ = mat (g k) * mat ↑((g i)⁻¹ * g i) * δ (f k) := by rw [matm]; simp only [mul_assoc]
        _ = mat (g k) * δ (f k) := by simp
        _ = δ k * mat γ := h2.symm
        _ = mat ↑(1 : Γ) * δ k * mat γ := by simp
    exact (rep_uniq hD hα e).1
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), g, hfg⟩

/- English proof (translation)
Establish `hex : ∃ π : Equiv.Perm ι, ∀ i, ∃ γ' : Γ, δ i * mat γ = mat γ' * δ (π i)` using `⟨π, fun i => ⟨g i, hg i⟩⟩`. Rewrite using `[hk, LinearMap.pi_apply, dif_pos hex, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, LinearMap.proj_apply]`. Establish `e` using `((hex.choose_spec i).choose_spec).symm.trans (hg i)`.

Take `⟨h1, h2⟩` from `rep_uniq hD hα e`. Rewrite using `[h2, h1]`.
-/
theorem hk_apply [Fintype ι] (w : ℕ) (hD : IsDCReps Γ α δ) (hα : α.det ≠ 0) (z : Γ → ℂ[X]) (γ : Γ)
    (π : Equiv.Perm ι) (g : ι → Γ) (hg : ∀ i, δ i * mat γ = mat (g i) * δ (π i)) :
    hk Γ w δ z γ = ∑ i, slP w (δ (π i)) (z (g i)) := by
  have hex : ∃ π : Equiv.Perm ι, ∀ i, ∃ γ' : Γ, δ i * mat γ = mat γ' * δ (π i) :=
    ⟨π, fun i => ⟨g i, hg i⟩⟩
  rw [hk, LinearMap.pi_apply, dif_pos hex, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.comp_apply, LinearMap.proj_apply]
  have e := ((hex.choose_spec i).choose_spec).symm.trans (hg i)
  obtain ⟨h1, h2⟩ := rep_uniq hD hα e
  rw [h2, h1]

end GlobalTheory.HeckeFamilyMatrices.HkC

namespace GlobalTheory.HeckeFamilyMatrices.HkC

/- English proof (translation)
Introduce `Γ w ι _ α δ hpos hD`. Establish `hα : α.det ≠ 0` using `hpos.ne'`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `z ⟨hz1, hz2⟩`. Use `⟨fun γ => ?_, fun γ γ' => ?_⟩` and prove the remaining obligations.

Take `⟨π, g, hg⟩` from `rep_exists hD hα γ`. Rewrite using `[hk_apply w hD hα z γ π g hg]`. Conclude with `Submodule.sum_mem _ fun i _ => mem_degLT_iff.2 (natDegree_slP_le _ _ _)`. Take `⟨π1, g1, hg1⟩` from `rep_exists hD hα γ`. Take `⟨π2, g2, hg2⟩` from `rep_exists hD hα γ'`.

Establish `hg : ∀ i, δ i * mat ↑(γ * γ') = mat ↑(g1 i * g2 (π1 i)) * δ ((π1.trans π2) i)`. Introduce `i`. Rewrite using `[matm, matm, ← mul_assoc, hg1, mul_assoc, hg2, ← mul_assoc]`. Both sides reduce to the same expression. Rewrite using `[hk_apply w hD hα z _ _ _ hg, hk_apply w hD hα z γ π1 g1 hg1, hk_apply w hD hα z γ' π2 g2 hg2, map_sum]`.

Simplify using `only [hz2, map_add, Finset.sum_add_distrib, Equiv.trans_apply]`. Establish `hs` using `Equiv.sum_comp π1 (fun j => slP w (δ (π2 j)) (z (g2 j)))`. Rewrite using `[hs, add_left_inj]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[polySlash_comp _ _ _ _ (mem_degLT_iff.1 (hz1 _)), polySlash_comp _ _ _ _ (mem_degLT_iff.1 (hz1 _)), ← hg2 (π1 i)]`.

Introduce and unpack `z ⟨⟨p, hp⟩, rfl⟩`. Establish `hp' : p.natDegree ≤ w` using `mem_degLT_iff.1 hp`. Use `⟨⟨∑ i, slP w (δ i) p, Submodule.sum_mem _ fun i _ => mem_degLT_iff.2 (natDegree_slP_le _ _ _)⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `γ`. Take `⟨π, g, hg⟩` from `rep_exists hD hα γ`.

Rewrite using `[hk_apply w hD hα _ γ π g hg]`. Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub, Finset.sum_sub_distrib, map_sum]`. Establish `hs` using `Equiv.sum_comp π (fun j => slP w (δ j) p)`. Rewrite using `[hs, sub_left_inj]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[polySlash_comp _ _ _ _ hp', polySlash_comp _ _ _ _ hp', hg]`. Introduce `z`. Use function extensionality and compare the values at `γ`. Simplify using `only [cj, hk, LinearMap.pi_apply]`. Use `split_ifs with h`.

Simplify using `only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, Polynomial.map_sum, polySlash_map]`. Both sides reduce to the same expression. Simplify using the standard rewrite rules.
-/
theorem hk_cocycle_coboundary_conj : ∀ (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (ι : Type) [Fintype ι]
    (α : Matrix (Fin 2) (Fin 2) ℤ) (δ : ι → Matrix (Fin 2) (Fin 2) ℤ), 0 < α.det → IsDCReps Γ α δ →
    (∀ z ∈ Z1 Γ w, hk Γ w δ z ∈ Z1 Γ w) ∧ (∀ z ∈ B1 Γ w, hk Γ w δ z ∈ B1 Γ w) ∧
      ∀ z, cj (hk Γ w δ z) = hk Γ w δ (cj z) := by
  intro Γ w ι _ α δ hpos hD
  have hα : α.det ≠ 0 := hpos.ne'
  refine ⟨?_, ?_, ?_⟩
  · rintro z ⟨hz1, hz2⟩
    refine ⟨fun γ => ?_, fun γ γ' => ?_⟩
    · obtain ⟨π, g, hg⟩ := rep_exists hD hα γ
      rw [hk_apply w hD hα z γ π g hg]
      exact Submodule.sum_mem _ fun i _ => mem_degLT_iff.2 (natDegree_slP_le _ _ _)
    · obtain ⟨π1, g1, hg1⟩ := rep_exists hD hα γ
      obtain ⟨π2, g2, hg2⟩ := rep_exists hD hα γ'
      have hg : ∀ i, δ i * mat ↑(γ * γ') = mat ↑(g1 i * g2 (π1 i)) * δ ((π1.trans π2) i) := by
        intro i
        rw [matm, matm, ← mul_assoc, hg1, mul_assoc, hg2, ← mul_assoc]
        rfl
      rw [hk_apply w hD hα z _ _ _ hg, hk_apply w hD hα z γ π1 g1 hg1, hk_apply w hD hα z γ' π2 g2 hg2,
        map_sum]
      simp only [hz2, map_add, Finset.sum_add_distrib, Equiv.trans_apply]
      have hs := Equiv.sum_comp π1 (fun j => slP w (δ (π2 j)) (z (g2 j)))
      rw [hs, add_left_inj]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [polySlash_comp _ _ _ _ (mem_degLT_iff.1 (hz1 _)), polySlash_comp _ _ _ _ (mem_degLT_iff.1 (hz1 _)),
        ← hg2 (π1 i)]
  · rintro z ⟨⟨p, hp⟩, rfl⟩
    have hp' : p.natDegree ≤ w := mem_degLT_iff.1 hp
    refine ⟨⟨∑ i, slP w (δ i) p, Submodule.sum_mem _ fun i _ => mem_degLT_iff.2 (natDegree_slP_le _ _ _)⟩, ?_⟩
    funext γ
    obtain ⟨π, g, hg⟩ := rep_exists hD hα γ
    rw [hk_apply w hD hα _ γ π g hg]
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.pi_apply, LinearMap.sub_apply,
      LinearMap.id_apply, map_sub, Finset.sum_sub_distrib, map_sum]
    have hs := Equiv.sum_comp π (fun j => slP w (δ j) p)
    rw [hs, sub_left_inj]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [polySlash_comp _ _ _ _ hp', polySlash_comp _ _ _ _ hp', hg]
  · intro z
    funext γ
    simp only [cj, hk, LinearMap.pi_apply]
    split_ifs with h
    · simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, Polynomial.map_sum, polySlash_map]
      rfl
    · simp

end GlobalTheory.HeckeFamilyMatrices.HkC
