import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.InductiveHeisenbergInputs

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def iW (k : ℕ) : Fin (2 * 0 + k + 1) := wI k 0 0

def iK (k : ℕ) : Fin (2 * 0 + k + 1) := wI k 0 (Fin.last k)

def Pk (k : ℕ) : Mat k 0 := Matrix.single (iK k) (iK k) 1

def U0 (k : ℕ) : Set (Mat k 0) := UWset k 0 (bvec (iK k))

/- English proof (translation)
Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `[iW, iK, wI] at this`. Use linear arithmetic over natural numbers and integers.
-/
lemma iW_ne_iK {k : ℕ} (hk : 1 ≤ k) : iW k ≠ iK k := by
  intro h
  have := congrArg Fin.val h
  simp [iW, iK, wI] at this
  omega

/- English proof (translation)
Use extensionality with `i j`. Establish `hi` using `i.isLt`. Establish `hle : i.val ≤ k` using `by omega`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Distinguish the cases in `hik : i.val = k`. Simplify using `[Hpk, Pk, iK, wI, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff, hik]`. Evaluate the numerical expressions. Establish `hik' : k ≠ i.val` using `fun h => hik h.symm`. Simplify using `[Hpk, Pk, iK, wI, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff, hik, hik', hle]`.

Establish `hv : i.val ≠ j.val` using `fun h => hij (Fin.ext h)`. Simplify using `[Hpk, Pk, iK, wI, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff, hv]`. Use linear arithmetic over natural numbers and integers.
-/
lemma hpk0 (k : ℕ) : Hpk k 0 = 1 - 2 • Pk k := by
  ext i j
  have hi := i.isLt
  have hle : i.val ≤ k := by omega
  by_cases hij : i = j
  · subst hij
    by_cases hik : i.val = k
    · simp [Hpk, Pk, iK, wI, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff, hik]
      norm_num
    · have hik' : k ≠ i.val := fun h => hik h.symm
      simp [Hpk, Pk, iK, wI, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff, hik, hik', hle]
  · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp [Hpk, Pk, iK, wI, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff, hv]
    omega

/- English proof (translation)
Simplify using `[Pk]`.
-/
lemma Pk_mul_self (k : ℕ) : Pk k * Pk k = Pk k := by
  simp [Pk]

/- English proof (translation)
Simplify using `[Pk]`.
-/
lemma Pk_conjTranspose (k : ℕ) : (Pk k)ᴴ = Pk k := by
  simp [Pk]

/- English proof (translation)
Rewrite using `[sub_mul, one_mul, smul_mul_assoc, Pk_mul_self, two_smul]`. Normalize the expressions using the abelian group laws.
-/
lemma one_sub_mul_Pk (k : ℕ) : (1 - 2 • Pk k) * Pk k = -Pk k := by
  rw [sub_mul, one_mul, smul_mul_assoc, Pk_mul_self, two_smul]
  abel

/- English proof (translation)
Take `⟨hU, -, hv⟩` from `hh`. Establish `hU' : hᴴ * Hpk k 0 * h = Hpk k 0` using `hU`. Establish `hcol : ∀ i, h i (iK k) = if i = iK k then 1 else 0`. Introduce `i`. Use `congrFun hv i` as an intermediate fact.

Simplify `this` using `[Matrix.mulVec, dotProduct, bvec, Pi.single_apply]`. Establish `hP : h * Pk k = Pk k`. Use extensionality with `i j`. Distinguish the cases in `hj : iK k = j`. Substitute `hj` using the available equality.

Distinguish the cases in `hi : i = iK k`. Substitute `hi` using the available equality. Simplify using `[Pk, Matrix.mul_apply, Matrix.single_apply, hcol]`. Establish `hi' : iK k ≠ i` using `fun e => hi e.symm`. Simplify using `[Pk, Matrix.mul_apply, Matrix.single_apply, hcol, hi, hi']`.

Simplify using `[Pk, Matrix.mul_apply, Matrix.single_apply, hj]`. Establish `hsP : hᴴ * Pk k = Pk k`. Establish `e1 : hᴴ * Hpk k 0 * h * Pk k = Hpk k 0 * Pk k` using `by rw [hU']`. Rewrite `e1` using `[Matrix.mul_assoc, hP, hpk0, Matrix.mul_assoc, one_sub_mul_Pk, Matrix.mul_neg]`. Conclude with `neg_inj.mp e1`.

Establish `hPh : Pk k * h = Pk k`. Use `congrArg Matrix.conjTranspose hsP` as an intermediate fact. Simplify `this` using `[Matrix.conjTranspose_mul, Pk_conjTranspose]`. Use `⟨?_, hP, hsP, hPh⟩` and prove the remaining obligations. Establish `e2` using `hU'`.

Rewrite `e2` using `[hpk0, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, hsP, hPh]`. Conclude with `sub_left_inj.mp e2`.
-/
lemma fixedUnitary_projection_identities {k : ℕ} {h : Mat k 0} (hh : h ∈ U0 k) :
    hᴴ * h = 1 ∧ h * Pk k = Pk k ∧ hᴴ * Pk k = Pk k ∧ Pk k * h = Pk k := by
  obtain ⟨hU, -, hv⟩ := hh
  have hU' : hᴴ * Hpk k 0 * h = Hpk k 0 := hU
  have hcol : ∀ i, h i (iK k) = if i = iK k then 1 else 0 := by
    intro i
    have := congrFun hv i
    simpa [Matrix.mulVec, dotProduct, bvec, Pi.single_apply] using this
  have hP : h * Pk k = Pk k := by
    ext i j
    by_cases hj : iK k = j
    · subst hj
      by_cases hi : i = iK k
      · subst hi
        simp [Pk, Matrix.mul_apply, Matrix.single_apply, hcol]
      · have hi' : iK k ≠ i := fun e => hi e.symm
        simp [Pk, Matrix.mul_apply, Matrix.single_apply, hcol, hi, hi']
    · simp [Pk, Matrix.mul_apply, Matrix.single_apply, hj]
  have hsP : hᴴ * Pk k = Pk k := by
    have e1 : hᴴ * Hpk k 0 * h * Pk k = Hpk k 0 * Pk k := by rw [hU']
    rw [Matrix.mul_assoc, hP, hpk0, Matrix.mul_assoc, one_sub_mul_Pk, Matrix.mul_neg] at e1
    exact neg_inj.mp e1
  have hPh : Pk k * h = Pk k := by
    have := congrArg Matrix.conjTranspose hsP
    simpa [Matrix.conjTranspose_mul, Pk_conjTranspose] using this
  refine ⟨?_, hP, hsP, hPh⟩
  have e2 := hU'
  rw [hpk0, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
    hsP, hPh] at e2
  exact sub_left_inj.mp e2

/- English proof (translation)
Establish `hsP : Rᴴ * Pk k = Pk k`. Combine the equalities or inequalities in the displayed calculation. Establish `hPR : Pk k * R = Pk k`. Use `congrArg Matrix.conjTranspose hsP` as an intermediate fact. Simplify `this` using `[Matrix.conjTranspose_mul, Pk_conjTranspose]`.

Use `⟨?_, fun a => a.elim0, ?_⟩` and prove the remaining obligations. Use `show Rᴴ * Hpk k 0 * R = Hpk k 0`. Rewrite using `[hpk0, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hu, Matrix.mul_smul, Matrix.smul_mul, hsP, hPR]`. Use extensionality with `i`. Use `congrFun (congrFun hP i) (iK k)` as an intermediate fact.

Simplify `this` using `[Pk, Matrix.mul_apply, Matrix.single_apply, Matrix.mulVec, dotProduct, bvec, Pi.single_apply, eq_comm]`.
-/
lemma mem_fixedUnitary_of_unitary_fixes {k : ℕ} {R : Mat k 0} (hu : Rᴴ * R = 1) (hP : R * Pk k = Pk k) : R ∈ U0 k := by
  have hsP : Rᴴ * Pk k = Pk k := by
    calc Rᴴ * Pk k = Rᴴ * (R * Pk k) := by rw [hP]
      _ = Pk k := by rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
  have hPR : Pk k * R = Pk k := by
    have := congrArg Matrix.conjTranspose hsP
    simpa [Matrix.conjTranspose_mul, Pk_conjTranspose] using this
  refine ⟨?_, fun a => a.elim0, ?_⟩
  · show Rᴴ * Hpk k 0 * R = Hpk k 0
    rw [hpk0, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hu, Matrix.mul_smul, Matrix.smul_mul,
      hsP, hPR]
  · ext i
    have := congrFun (congrFun hP i) (iK k)
    simpa [Pk, Matrix.mul_apply, Matrix.single_apply, Matrix.mulVec, dotProduct, bvec,
      Pi.single_apply, eq_comm] using this

/- English proof (translation)
Take `⟨hu, -, hsP, -⟩` from `fixedUnitary_projection_identities hh`. Use `mem_fixedUnitary_of_unitary_fixes ?_ hsP` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_conjTranspose]`. Conclude with `mul_eq_one_comm.mp hu`.
-/
lemma fixedUnitary_conjTranspose_mem {k : ℕ} {h : Mat k 0} (hh : h ∈ U0 k) : hᴴ ∈ U0 k := by
  obtain ⟨hu, -, hsP, -⟩ := fixedUnitary_projection_identities hh
  refine mem_fixedUnitary_of_unitary_fixes ?_ hsP
  rw [Matrix.conjTranspose_conjTranspose]
  exact mul_eq_one_comm.mp hu

/- English proof (translation)
Use `congrFun (congrFun (fixedUnitary_projection_identities hh).2.2.2 (iK k)) j` as an intermediate fact. Simplify `this` using `[Pk, Matrix.mul_apply, Matrix.single_apply, eq_comm]`.
-/
lemma fixedUnitary_apply_fixedIndex_left {k : ℕ} {h : Mat k 0} (hh : h ∈ U0 k) (j : Fin (2 * 0 + k + 1)) :
    h (iK k) j = if j = iK k then 1 else 0 := by
  have := congrFun (congrFun (fixedUnitary_projection_identities hh).2.2.2 (iK k)) j
  simpa [Pk, Matrix.mul_apply, Matrix.single_apply, eq_comm] using this

/- English proof (translation)
Use `congrFun (congrFun (fixedUnitary_projection_identities hh).2.1 i) (iK k)` as an intermediate fact. Simplify `this` using `[Pk, Matrix.mul_apply, Matrix.single_apply, eq_comm]`.
-/
lemma fixedUnitary_apply_fixedIndex_right {k : ℕ} {h : Mat k 0} (hh : h ∈ U0 k) (i : Fin (2 * 0 + k + 1)) :
    h i (iK k) = if i = iK k then 1 else 0 := by
  have := congrFun (congrFun (fixedUnitary_projection_identities hh).2.1 i) (iK k)
  simpa [Pk, Matrix.mul_apply, Matrix.single_apply, eq_comm] using this

/- English proof (translation)
Simplify using `[Matrix.mulVec, dotProduct, fixedUnitary_apply_fixedIndex_left hh]`.
-/
lemma fixedUnitary_mulVec_fixedIndex {k : ℕ} {h : Mat k 0} (hh : h ∈ U0 k) (y : Fin (2 * 0 + k + 1) → ℂ) :
    (h *ᵥ y) (iK k) = y (iK k) := by
  simp [Matrix.mulVec, dotProduct, fixedUnitary_apply_fixedIndex_left hh]

/- English proof (translation)
Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, (fixedUnitary_projection_identities hh).1, Matrix.one_mulVec]`.
-/
lemma fixedUnitary_preserves_normSq {k : ℕ} {h : Mat k 0} (hh : h ∈ U0 k) (y : Fin (2 * 0 + k + 1) → ℂ) :
    star (h *ᵥ y) ⬝ᵥ (h *ᵥ y) = star y ⬝ᵥ y := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, (fixedUnitary_projection_identities hh).1,
    Matrix.one_mulVec]

/- English proof (translation)
Establish `hWK : iW k ≠ iK k` using `iW_ne_iK hk`. Choose the witnesses or unpack the hypotheses as in `⟨μ, hμ1, hμr⟩ : ∃ μ : ℂ, star μ * μ = 1 ∧ star (star μ * u (iW k)) = star μ * u (iW k) := by`. Distinguish the cases in `h0 : u (iW k) = 0`. Conclude with `⟨1, by simp, by simp [h0]⟩`. Establish `hn : ((‖u (iW k)‖ : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast norm_ne_zero_iff.mpr h0`.

Establish `hc : star (u (iW k)) * u (iW k) = ((‖u (iW k)‖ : ℝ) : ℂ) ^ 2` using `Complex.conj_mul' _`. Establish `hs : star ((‖u (iW k)‖ : ℝ) : ℂ) = ((‖u (iW k)‖ : ℝ) : ℂ)` using `Complex.conj_ofReal _`. Establish `hval : star (u (iW k) / ((‖u (iW k)‖ : ℝ) : ℂ)) * u (iW k) = ((‖u (iW k)‖ : ℝ) : ℂ)`. Rewrite using `[star_div₀, hs, div_mul_eq_mul_div, hc]`. Clear the denominators using the available nonvanishing facts.

Use `⟨u (iW k) / ((‖u (iW k)‖ : ℝ) : ℂ), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[star_div₀, hs, div_mul_div_comm, hc]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hval, hs]`. Take `⟨d, hd⟩ : ∃ d : Fin (2 * 0 + k + 1) → ℂ, d = Function.update (fun _ => 1) (iW k) μ` from `⟨_, rfl⟩`.

Establish `hdW : d (iW k) = μ` using `by simp [hd]`. Establish `hdo : ∀ i, i ≠ iW k → d i = 1`. Introduce `i hi`. Simplify using `[hd, hi]`. Establish `hDu : (Matrix.diagonal d)ᴴ * Matrix.diagonal d = 1`.

Rewrite using `[Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use extensionality with `i`. Distinguish the cases in `hi : i = iW k`. Substitute `hi` using the available equality.

Simplify using `[hdW]`. Conclude with `hμ1`. Simplify using `[hdo i hi]`. Establish `hDP : Matrix.diagonal d * Pk k = Pk k`. Use extensionality with `i j`.

Distinguish the cases in `hi : i = iK k`. Substitute `hi` using the available equality. Simplify using `[Matrix.diagonal_mul, hdo _ (Ne.symm hWK)]`. Simplify using `[Matrix.diagonal_mul, Pk, Matrix.single_apply, Ne.symm hi]`. Establish `hDe : Matrix.diagonal d *ᵥ bvec (iW k) = μ • bvec (iW k)`.

Use extensionality with `i`. Distinguish the cases in `hi : i = iW k`. Substitute `hi` using the available equality. Simplify using `[Matrix.mulVec_diagonal, hdW, bvec]`. Simplify using `[Matrix.mulVec_diagonal, bvec, Pi.single_apply, hi]`.

Take `⟨x, hx⟩ : ∃ x : Fin (2 * 0 + k + 1) → ℂ, x = μ • bvec (iW k)` from `⟨_, rfl⟩`. Distinguish the cases in `hxu : x = u`. Use `⟨Matrix.diagonal d, mem_fixedUnitary_of_unitary_fixes hDu hDP, ?_⟩` and prove the remaining obligations. Rewrite using `[hDe, ← hx, hxu]`. Take `⟨w, hw⟩ : ∃ w : Fin (2 * 0 + k + 1) → ℂ, w = x - u` from `⟨_, rfl⟩`.

Establish `hw0 : w ≠ 0`. Rewrite using `[hw]`. Conclude with `sub_ne_zero.mpr hxu`. Establish `hn : star w ⬝ᵥ w ≠ 0` using `fun h => hw0 (dotProduct_star_self_eq_zero.mp h)`. Take `⟨s, hs⟩ : ∃ s : ℂ, s = 2 * (star w ⬝ᵥ w)⁻¹` from `⟨_, rfl⟩`.

Take `⟨W, hW⟩ : ∃ W : Mat k 0, W = Matrix.vecMulVec w (star w)` from `⟨_, rfl⟩`. Establish `hWv : ∀ v, W *ᵥ v = (star w ⬝ᵥ v) • w`. Introduce `v`. Use extensionality with `i`. Simplify using `only [hW, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]`.

Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hWW : W * W = (star w ⬝ᵥ w) • W`. Use extensionality with `i j`. Simplify using `only [hW, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct, Finset.sum_mul]`.

Use `Finset.sum_congr rfl (fun l _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hWh : Wᴴ = W`. Use extensionality with `i j`. Simplify using `[hW, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, mul_comm]`.

Establish `hnr : star (star w ⬝ᵥ w) = star w ⬝ᵥ w`. Simplify using `[dotProduct, star_sum, mul_comm]`. Establish `hsr : star s = s`. Rewrite using `[hs, star_mul', star_inv₀, hnr, star_ofNat]`. Take `⟨Hh, hHh⟩ : ∃ Hh : Mat k 0, Hh = 1 - s • W` from `⟨_, rfl⟩`.

Establish `hHhs : Hhᴴ = Hh`. Rewrite using `[hHh, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hsr, hWh]`. Establish `hsn : s * (s * (star w ⬝ᵥ w)) = 2 * s`. Rewrite using `[hs]`. Clear the denominators using the available nonvanishing facts.

Establish `hHH : Hh * Hh = 1`. Rewrite using `[hHh]`. Simplify using `only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, smul_mul_assoc, mul_smul_comm, hWW, smul_smul, smul_sub]`. Establish `h2 : (s * (s * (star w ⬝ᵥ w))) • W = s • W + s • W`. Rewrite using `[hsn, ← add_smul, ← two_mul]`.

Rewrite using `[h2]`. Normalize the expressions using the abelian group laws. Take `⟨α, hα⟩ : ∃ α : ℂ, α = star μ * u (iW k)` from `⟨_, rfl⟩`. Establish `hxv : ∀ v, star x ⬝ᵥ v = star μ * v (iW k)`. Introduce `v`.

Rewrite using `[hx]`. Simplify using `only [dotProduct]`. Rewrite using `[Finset.sum_eq_single (iW k)]`. Simplify using `[bvec]`. Introduce `j _ hj`.

Simplify using `[bvec, Pi.single_apply, hj]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `hvx : ∀ v, star v ⬝ᵥ x = star (v (iW k)) * μ`. Introduce `v`.

Rewrite using `[hx]`. Simplify using `only [dotProduct]`. Rewrite using `[Finset.sum_eq_single (iW k)]`. Simplify using `[bvec]`. Introduce `j _ hj`.

Simplify using `[bvec, Pi.single_apply, hj]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `hxx : star x ⬝ᵥ x = 1`. Rewrite using `[hvx, hx]`.

Simplify `hμ1` using `[bvec, mul_comm]`. Establish `hxu' : star x ⬝ᵥ u = α` using `by rw [hxv, hα]`. Establish `hux : star u ⬝ᵥ x = α`. Establish `h1` using `hμr`. Rewrite `h1` using `[star_mul, star_star]`.

Rewrite using `[hvx, h1, ← hα]`. Establish `hwx : star w ⬝ᵥ x = 1 - α`. Rewrite using `[hw, star_sub, sub_dotProduct, hxx, hux]`. Establish `hwn : star w ⬝ᵥ w = 2 - 2 * α`. Rewrite using `[hw, star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hxx, hxu', hux, hu1]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hn' : (2 - 2 * α : ℂ) ≠ 0` using `hwn ▸ hn`. Establish `hs1 : s * (1 - α) = 1`. Rewrite using `[hs, hwn]`. Establish `: (1 - α : ℂ) ≠ 0`.

Introduce `h`. Apply `hn'` to reduce the goal to its premises. Take the linear combination `2 * h`. Clear the denominators using the available nonvanishing facts. Use `⟨Hh * Matrix.diagonal d, mem_fixedUnitary_of_unitary_fixes ?_ ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.conjTranspose_mul, hHhs, Matrix.mul_assoc, ← Matrix.mul_assoc Hh Hh, hHH, Matrix.one_mul, hDu]`. Establish `hwk : w (iK k) = 0`. Rewrite using `[hw, hx]`. Simplify using `[hu0, bvec, Pi.single_apply, Ne.symm hWK]`. Establish `hWP : W * Pk k = 0`.

Use extensionality with `i j`. Simplify using `[hW, Pk, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.single_apply]`. Use `Finset.sum_eq_zero (fun l _ => ?_)` and prove the remaining obligations. Use `split_ifs with hl`. Rewrite using `[← hl.1, hwk]`.

Simplify using the standard rewrite rules. Both sides reduce to the same expression. Rewrite using `[Matrix.mul_assoc, hDP, hHh, sub_mul, Matrix.one_mul, smul_mul_assoc, hWP, smul_zero, sub_zero]`. Establish `hsm : (s • W) *ᵥ x = s • (W *ᵥ x)`. Use extensionality with `i`.

Simplify using `[Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]`. Rewrite using `[← Matrix.mulVec_mulVec, hDe, ← hx, hHh, Matrix.sub_mulVec, Matrix.one_mulVec, hsm, hWv, hwx, smul_smul, hs1, one_smul, hw, sub_sub_cancel]`.
-/
lemma exists_fixedUnitary_sending_basis {k : ℕ} (hk : 1 ≤ k) (u : Fin (2 * 0 + k + 1) → ℂ) (hu0 : u (iK k) = 0)
    (hu1 : star u ⬝ᵥ u = 1) : ∃ R ∈ U0 k, R *ᵥ bvec (iW k) = u := by
  classical
  have hWK : iW k ≠ iK k := iW_ne_iK hk

  obtain ⟨μ, hμ1, hμr⟩ : ∃ μ : ℂ, star μ * μ = 1 ∧
      star (star μ * u (iW k)) = star μ * u (iW k) := by
    by_cases h0 : u (iW k) = 0
    · exact ⟨1, by simp, by simp [h0]⟩
    · have hn : ((‖u (iW k)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h0
      have hc : star (u (iW k)) * u (iW k) = ((‖u (iW k)‖ : ℝ) : ℂ) ^ 2 := Complex.conj_mul' _
      have hs : star ((‖u (iW k)‖ : ℝ) : ℂ) = ((‖u (iW k)‖ : ℝ) : ℂ) := Complex.conj_ofReal _
      have hval : star (u (iW k) / ((‖u (iW k)‖ : ℝ) : ℂ)) * u (iW k) = ((‖u (iW k)‖ : ℝ) : ℂ) := by
        rw [star_div₀, hs, div_mul_eq_mul_div, hc]
        field_simp
      refine ⟨u (iW k) / ((‖u (iW k)‖ : ℝ) : ℂ), ?_, ?_⟩
      · rw [star_div₀, hs, div_mul_div_comm, hc]
        field_simp
      · rw [hval, hs]

  obtain ⟨d, hd⟩ : ∃ d : Fin (2 * 0 + k + 1) → ℂ, d = Function.update (fun _ => 1) (iW k) μ :=
    ⟨_, rfl⟩
  have hdW : d (iW k) = μ := by simp [hd]
  have hdo : ∀ i, i ≠ iW k → d i = 1 := by
    intro i hi
    simp [hd, hi]
  have hDu : (Matrix.diagonal d)ᴴ * Matrix.diagonal d = 1 := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    by_cases hi : i = iW k
    · subst hi
      simp [hdW]
      exact hμ1
    · simp [hdo i hi]
  have hDP : Matrix.diagonal d * Pk k = Pk k := by
    ext i j
    by_cases hi : i = iK k
    · subst hi
      simp [Matrix.diagonal_mul, hdo _ (Ne.symm hWK)]
    · simp [Matrix.diagonal_mul, Pk, Matrix.single_apply, Ne.symm hi]
  have hDe : Matrix.diagonal d *ᵥ bvec (iW k) = μ • bvec (iW k) := by
    ext i
    by_cases hi : i = iW k
    · subst hi
      simp [Matrix.mulVec_diagonal, hdW, bvec]
    · simp [Matrix.mulVec_diagonal, bvec, Pi.single_apply, hi]
  obtain ⟨x, hx⟩ : ∃ x : Fin (2 * 0 + k + 1) → ℂ, x = μ • bvec (iW k) := ⟨_, rfl⟩
  by_cases hxu : x = u
  · refine ⟨Matrix.diagonal d, mem_fixedUnitary_of_unitary_fixes hDu hDP, ?_⟩
    rw [hDe, ← hx, hxu]

  obtain ⟨w, hw⟩ : ∃ w : Fin (2 * 0 + k + 1) → ℂ, w = x - u := ⟨_, rfl⟩
  have hw0 : w ≠ 0 := by
    rw [hw]
    exact sub_ne_zero.mpr hxu
  have hn : star w ⬝ᵥ w ≠ 0 := fun h => hw0 (dotProduct_star_self_eq_zero.mp h)
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = 2 * (star w ⬝ᵥ w)⁻¹ := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : Mat k 0, W = Matrix.vecMulVec w (star w) := ⟨_, rfl⟩
  have hWv : ∀ v, W *ᵥ v = (star w ⬝ᵥ v) • w := by
    intro v
    ext i
    simp only [hW, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hWW : W * W = (star w ⬝ᵥ w) • W := by
    ext i j
    simp only [hW, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul,
      dotProduct, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  have hWh : Wᴴ = W := by
    ext i j
    simp [hW, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, mul_comm]
  have hnr : star (star w ⬝ᵥ w) = star w ⬝ᵥ w := by
    simp [dotProduct, star_sum, mul_comm]
  have hsr : star s = s := by
    rw [hs, star_mul', star_inv₀, hnr, star_ofNat]
  obtain ⟨Hh, hHh⟩ : ∃ Hh : Mat k 0, Hh = 1 - s • W := ⟨_, rfl⟩
  have hHhs : Hhᴴ = Hh := by
    rw [hHh, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hsr, hWh]
  have hsn : s * (s * (star w ⬝ᵥ w)) = 2 * s := by
    rw [hs]
    field_simp
  have hHH : Hh * Hh = 1 := by
    rw [hHh]
    simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, smul_mul_assoc, mul_smul_comm,
      hWW, smul_smul, smul_sub]
    have h2 : (s * (s * (star w ⬝ᵥ w))) • W = s • W + s • W := by
      rw [hsn, ← add_smul, ← two_mul]
    rw [h2]
    abel
  obtain ⟨α, hα⟩ : ∃ α : ℂ, α = star μ * u (iW k) := ⟨_, rfl⟩
  have hxv : ∀ v, star x ⬝ᵥ v = star μ * v (iW k) := by
    intro v
    rw [hx]
    simp only [dotProduct]
    rw [Finset.sum_eq_single (iW k)]
    · simp [bvec]
    · intro j _ hj
      simp [bvec, Pi.single_apply, hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hvx : ∀ v, star v ⬝ᵥ x = star (v (iW k)) * μ := by
    intro v
    rw [hx]
    simp only [dotProduct]
    rw [Finset.sum_eq_single (iW k)]
    · simp [bvec]
    · intro j _ hj
      simp [bvec, Pi.single_apply, hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hxx : star x ⬝ᵥ x = 1 := by
    rw [hvx, hx]
    simpa [bvec, mul_comm] using hμ1
  have hxu' : star x ⬝ᵥ u = α := by rw [hxv, hα]
  have hux : star u ⬝ᵥ x = α := by
    have h1 := hμr
    rw [star_mul, star_star] at h1
    rw [hvx, h1, ← hα]
  have hwx : star w ⬝ᵥ x = 1 - α := by
    rw [hw, star_sub, sub_dotProduct, hxx, hux]
  have hwn : star w ⬝ᵥ w = 2 - 2 * α := by
    rw [hw, star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hxx, hxu', hux, hu1]
    ring
  have hn' : (2 - 2 * α : ℂ) ≠ 0 := hwn ▸ hn
  have hs1 : s * (1 - α) = 1 := by
    rw [hs, hwn]
    have : (1 - α : ℂ) ≠ 0 := by
      intro h
      apply hn'
      linear_combination 2 * h
    field_simp
  refine ⟨Hh * Matrix.diagonal d, mem_fixedUnitary_of_unitary_fixes ?_ ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, hHhs, Matrix.mul_assoc, ← Matrix.mul_assoc Hh Hh, hHH,
      Matrix.one_mul, hDu]
  · have hwk : w (iK k) = 0 := by
      rw [hw, hx]
      simp [hu0, bvec, Pi.single_apply, Ne.symm hWK]
    have hWP : W * Pk k = 0 := by
      ext i j
      simp [hW, Pk, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.single_apply]
      refine Finset.sum_eq_zero (fun l _ => ?_)
      split_ifs with hl
      · rw [← hl.1, hwk]
        simp
      · rfl
    rw [Matrix.mul_assoc, hDP, hHh, sub_mul, Matrix.one_mul, smul_mul_assoc, hWP, smul_zero,
      sub_zero]
  · have hsm : (s • W) *ᵥ x = s • (W *ᵥ x) := by
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    rw [← Matrix.mulVec_mulVec, hDe, ← hx, hHh, Matrix.sub_mulVec, Matrix.one_mulVec, hsm, hWv, hwx, smul_smul, hs1, one_smul, hw, sub_sub_cancel]

end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
