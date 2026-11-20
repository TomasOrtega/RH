import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.DetPbA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.DetPbB

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def dpbE (ε : Fin n → Bool) : (PCoord ε → ℂ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := pmat
  map_add' z w := by
    ext a b
    simp only [pmat, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c z := by
    ext a b
    simp only [pmat, Matrix.smul_apply, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

def dpbP (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (PCoord ε → ℂ) where
  toFun W ab := (1 / 2 : ℝ) • (W ab.1.1 ab.1.2 + star (W ab.1.2 ab.1.1))
  map_add' W W' := by
    ext ab
    simp only [Matrix.add_apply, Pi.add_apply, star_add]
    module
  map_smul' c W := by
    ext ab
    simp only [Matrix.smul_apply, Pi.smul_apply, RingHom.id_apply, star_smul, star_trivial]
    module

/- English proof (translation)
Establish `h : star (W ab.1.2 ab.1.1) = W ab.1.1 ab.1.2`. Use `congrFun (congrFun hW ab.1.1) ab.1.2` as an intermediate fact. Simplify `this` using `[Matrix.conjTranspose_apply]`. Simplify using `only [dpbP, LinearMap.coe_mk, AddHom.coe_mk]`. Rewrite using `[h, Complex.real_smul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dpbP_herm {ε : Fin n → Bool} {W : Matrix (Fin n) (Fin n) ℂ} (hW : Wᴴ = W) (ab : PCoord ε) :
    dpbP ε W ab = W ab.1.1 ab.1.2 := by
  have h : star (W ab.1.2 ab.1.1) = W ab.1.1 ab.1.2 := by
    have := congrFun (congrFun hW ab.1.1) ab.1.2
    simpa [Matrix.conjTranspose_apply] using this
  simp only [dpbP, LinearMap.coe_mk, AddHom.coe_mk]
  rw [h, Complex.real_smul]
  push_cast
  ring

/- English proof (translation)
Use function extensionality and compare the values at `ab`. Take `⟨⟨a, b⟩, hab, hne⟩` from `ab`. Establish `h1 : ¬ (a < b ∧ ε b ≠ ε a)` using `fun h => absurd h.1 (not_lt.mpr hab.le)`. Simplify using `only [dpbP, dpbE, LinearMap.coe_mk, AddHom.coe_mk, pmat, dif_pos (And.intro hab hne), dif_neg h1, star_star]`. Rewrite using `[Complex.real_smul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dpbP_E {ε : Fin n → Bool} (w : PCoord ε → ℂ) : dpbP ε (dpbE ε w) = w := by
  funext ab
  obtain ⟨⟨a, b⟩, hab, hne⟩ := ab
  have h1 : ¬ (a < b ∧ ε b ≠ ε a) := fun h => absurd h.1 (not_lt.mpr hab.le)
  simp only [dpbP, dpbE, LinearMap.coe_mk, AddHom.coe_mk, pmat, dif_pos (And.intro hab hne), dif_neg h1,
    star_star]
  rw [Complex.real_smul]
  push_cast
  ring

/- English proof (translation)
Simplify using `only [Jm, Matrix.diagonal_mul, Matrix.mul_diagonal]`. Apply the tactic sequence `cases ε a <;> cases ε b <;> simp`.
-/
theorem dpb_JWJ (ε : Fin n → Bool) (W : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (Jm ε * W * Jm ε) a b = if ε a = ε b then W a b else -W a b := by
  simp only [Jm, Matrix.diagonal_mul, Matrix.mul_diagonal]
  cases ε a <;> cases ε b <;> simp

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [dpbE, dpbP, LinearMap.coe_mk, AddHom.coe_mk, pmat, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.conjTranspose_apply, dpb_JWJ]`. Distinguish the cases in `hε : ε a = ε b`. Establish `h1 : ¬ (b < a ∧ ε a ≠ ε b)` using `fun h => h.2 hε`. Establish `h2 : ¬ (a < b ∧ ε b ≠ ε a)` using `fun h => h.2 hε.symm`.

Rewrite using `[dif_neg h1, dif_neg h2, if_pos hε, if_pos hε.symm]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg hε, if_neg (Ne.symm hε)]`. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Establish `h1 : ¬ (b < a ∧ ε a ≠ ε b)` using `fun h' => absurd h'.1 (not_lt.mpr h.le)`.

Rewrite using `[dif_neg h1, dif_pos (And.intro h (Ne.symm hε))]`. Simplify using `only [Complex.real_smul]`. Use `push_cast`. Simplify using `only [star_add, star_mul', star_star, star_div₀, star_one, star_ofNat, star_neg]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `absurd (h ▸ rfl) hε`. Rewrite using `[dif_pos (And.intro h hε)]`. Simplify using `only [star_neg, Complex.real_smul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dpbE_P {ε : Fin n → Bool} (W : Matrix (Fin n) (Fin n) ℂ) :
    dpbE ε (dpbP ε W) = (1 / 4 : ℝ) • (W + Wᴴ - Jm ε * W * Jm ε - (Jm ε * W * Jm ε)ᴴ) := by
  ext a b
  simp only [dpbE, dpbP, LinearMap.coe_mk, AddHom.coe_mk, pmat, Matrix.smul_apply, Matrix.add_apply,
    Matrix.sub_apply, Matrix.conjTranspose_apply, dpb_JWJ]
  by_cases hε : ε a = ε b
  · have h1 : ¬ (b < a ∧ ε a ≠ ε b) := fun h => h.2 hε
    have h2 : ¬ (a < b ∧ ε b ≠ ε a) := fun h => h.2 hε.symm
    rw [dif_neg h1, dif_neg h2, if_pos hε, if_pos hε.symm]
    simp
  · rw [if_neg hε, if_neg (Ne.symm hε)]
    rcases lt_trichotomy a b with h | h | h
    · have h1 : ¬ (b < a ∧ ε a ≠ ε b) := fun h' => absurd h'.1 (not_lt.mpr h.le)
      rw [dif_neg h1, dif_pos (And.intro h (Ne.symm hε))]
      simp only [Complex.real_smul]
      push_cast
      simp only [star_add, star_mul', star_star, star_div₀, star_one, star_ofNat, star_neg]
      ring
    · exact absurd (h ▸ rfl) hε
    · rw [dif_pos (And.intro h hε)]
      simp only [star_neg, Complex.real_smul]
      push_cast
      ring

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[dpb_JWJ]`. Use `split_ifs with h`. Establish `: pmat y a b = 0` using `by simp [pmat, h]`. Rewrite using `[Matrix.neg_apply, this, neg_zero]`.

Rewrite using `[Matrix.neg_apply]`.
-/
theorem dpb_JYJ {ε : Fin n → Bool} (y : PCoord ε → ℂ) : Jm ε * pmat y * Jm ε = -pmat y := by
  ext a b
  rw [dpb_JWJ]
  split_ifs with h
  · have : pmat y a b = 0 := by simp [pmat, h]
    rw [Matrix.neg_apply, this, neg_zero]
  · rw [Matrix.neg_apply]

/- English proof (translation)
Unfold `shc`. Distinguish the cases in `h : u = 0`. Simplify using `[h]`. Rewrite using `[if_neg (neg_ne_zero.mpr h), if_neg h, Real.sinh_neg, neg_div_neg_eq]`.
-/
theorem dpb_shc_neg (u : ℝ) : shc (-u) = shc u := by
  unfold shc
  by_cases h : u = 0
  · simp [h]
  · rw [if_neg (neg_ne_zero.mpr h), if_neg h, Real.sinh_neg, neg_div_neg_eq]

/- English proof (translation)
Use function extensionality and compare the values at `u`. Unfold `shc`. Distinguish the cases in `h : u = 0`. Simplify using `[h]`. Rewrite using `[if_neg h]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem dpb_shc_fac : (fun u : ℝ => u * ((shc u - 1) / u)) = fun u => shc u - 1 := by
  funext u
  unfold shc
  by_cases h : u = 0
  · simp [h]
  · rw [if_neg h]
    field_simp

/- English proof (translation)
Establish `key : ∀ A B : Matrix (Fin n) (Fin n) ℂ, (J * A * J) * (J * B * J) = J * (A * B) * J`. Introduce `A B`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, ← key Y W, ← key W Y, hY]`. Simplify using `only [neg_mul, mul_neg]`.

Normalize the expressions using the abelian group laws.
-/
theorem dpb_theta_ad {J Y : Matrix (Fin n) (Fin n) ℂ} (hJ : J * J = 1) (hY : J * Y * J = -Y)
    (W : Matrix (Fin n) (Fin n) ℂ) : J * (Y * W - W * Y) * J = -(Y * (J * W * J) - (J * W * J) * Y) := by
  have key : ∀ A B : Matrix (Fin n) (Fin n) ℂ, (J * A * J) * (J * B * J) = J * (A * B) * J := by
    intro A B
    calc (J * A * J) * (J * B * J) = J * A * (J * J) * B * J := by simp only [Matrix.mul_assoc]
      _ = J * (A * B) * J := by rw [hJ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [Matrix.mul_sub, Matrix.sub_mul, ← key Y W, ← key W Y, hY]
  simp only [neg_mul, mul_neg]
  abel

/- English proof (translation)
Establish `hJJ : Jm ε * Jm ε = 1`. Rewrite using `[Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs <;> norm_num`.

Establish `hJh : (Jm ε)ᴴ = Jm ε`. Rewrite using `[Jm, Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Simplify using `only [Pi.star_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hJJv : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, hJJ, Matrix.one_mul]`. Set `θ : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ)` to `{ toFun := fun W => Jm ε * W * Jm ε map_add' := fun W W' => by simp only [Matrix.mul_add, Matrix.add_mul] map_smul' := fun c W => by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }`. Set `α : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ)` to `{ toFun := fun W => Wᴴ map_add' := fun W W' => Matrix.conjTranspose_add W W' map_smul' := fun c W => by simp [Matrix.conjTranspose_smul] }`.

Set `ι : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ)` to `{ toFun := fun W => Complex.I • W map_add' := fun W W' => smul_add _ _ _ map_smul' := fun c W => by simp only [RingHom.id_apply]; exact smul_comm _ _ _ }`. Set `N : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ)` to `{ toFun := fun W => (U * dpbD x * Uᴴ) * W - W * (U * dpbD x * Uᴴ) map_add' := fun W W' => by simp only [Matrix.mul_add, Matrix.add_mul]; abel map_smul' := fun c W => by`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, smul_sub] }`. Set `C : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ)` to `dpbL U x (fun u => (shc u - 1) / u)`. Establish `hsub : dpbH U x (fun u => u * ((shc u - 1) / u)) = dpbH U x (fun u => shc u - 1)`.

Rewrite using `[dpb_shc_fac]`. Use `dpb_abs (dpbL U x shc) θ α ι N C (dpbE ε) (dpbP ε) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `v show Jm ε * (Jm ε * v * Jm ε) * Jm ε = v`. Simplify using `only [Matrix.mul_assoc, hJJ, Matrix.mul_one, hJJv]`. Introduce `v show (vᴴ)ᴴ = v`.

Conclude with `Matrix.conjTranspose_conjTranspose v`. Introduce `v show Jm ε * vᴴ * Jm ε = (Jm ε * v * Jm ε)ᴴ`. Simplify using `only [Matrix.conjTranspose_mul, hJh, Matrix.mul_assoc]`. Introduce `v show Jm ε * dpbH U x shc v * Jm ε = dpbH U x shc (Jm ε * v * Jm ε)`. Conclude with `dpbH_theta hU hU' hJJ hJh hY shc dpb_shc_neg v`.

Introduce `v show (dpbH U x shc v)ᴴ = dpbH U x shc vᴴ`. Conclude with `dpbH_conjTranspose U x shc dpb_shc_neg v`. Introduce `v show (U * dpbD x * Uᴴ) * dpbH U x (fun u => (shc u - 1) / u) v - dpbH U x (fun u => (shc u - 1) / u) v * (U * dpbD x * Uᴴ) = dpbH U x shc v - v`. Rewrite using `[dpbH_ad_left x hU, hsub, dpbH_sub_one x hU']`. Introduce `v show dpbH U x (fun u => (shc u - 1) / u) ((U * dpbD x * Uᴴ) * v - v * (U * dpbD x * Uᴴ)) = dpbH U x shc v - v`.

Rewrite using `[dpbH_ad_right x hU, hsub, dpbH_sub_one x hU']`. Introduce `v show Jm ε * ((U * dpbD x * Uᴴ) * v - v * (U * dpbD x * Uᴴ)) * Jm ε = -((U * dpbD x * Uᴴ) * (Jm ε * v * Jm ε) - (Jm ε * v * Jm ε) * (U * dpbD x * Uᴴ))`. Conclude with `dpb_theta_ad hJJ hY v`. Introduce `v show Complex.I • (Complex.I • v) = -v`. Rewrite using `[smul_smul, Complex.I_mul_I, neg_one_smul]`.

Introduce `v show Complex.I • dpbH U x shc v = dpbH U x shc (Complex.I • v)`. Conclude with `(dpbH_smul U x shc Complex.I v).symm`. Introduce `v show Jm ε * (Complex.I • v) * Jm ε = Complex.I • (Jm ε * v * Jm ε)`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul]`. Introduce `v show (Complex.I • v)ᴴ = -(Complex.I • vᴴ)`.

Rewrite using `[Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_I, neg_smul]`. Introduce `v`. Conclude with `dpbE_P v`. Introduce `w`. Conclude with `dpbP_E w`.
-/
theorem dpb_det {ε : Fin n → Bool} {U : Matrix (Fin n) (Fin n) ℂ} {x : Fin n → ℝ} (hU : Uᴴ * U = 1)
    (hU' : U * Uᴴ = 1) (hY : Jm ε * (U * dpbD x * Uᴴ) * Jm ε = -(U * dpbD x * Uᴴ)) :
    LinearMap.det (dpbL U x shc) = LinearMap.det (dpbP ε ∘ₗ dpbL U x shc ∘ₗ dpbE ε) ^ 4 := by
  have hJJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJh : (Jm ε)ᴴ = Jm ε := by
    rw [Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    simp only [Pi.star_apply]
    split_ifs <;> simp
  have hJJv : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  let θ : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun W => Jm ε * W * Jm ε
      map_add' := fun W W' => by simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c W => by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  let α : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun W => Wᴴ
      map_add' := fun W W' => Matrix.conjTranspose_add W W'
      map_smul' := fun c W => by simp [Matrix.conjTranspose_smul] }
  let ι : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun W => Complex.I • W
      map_add' := fun W W' => smul_add _ _ _
      map_smul' := fun c W => by simp only [RingHom.id_apply]; exact smul_comm _ _ _ }
  let N : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun W => (U * dpbD x * Uᴴ) * W - W * (U * dpbD x * Uᴴ)
      map_add' := fun W W' => by simp only [Matrix.mul_add, Matrix.add_mul]; abel
      map_smul' := fun c W => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, smul_sub] }
  let C : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) := dpbL U x (fun u => (shc u - 1) / u)
  have hsub : dpbH U x (fun u => u * ((shc u - 1) / u)) = dpbH U x (fun u => shc u - 1) := by
    rw [dpb_shc_fac]
  refine dpb_abs (dpbL U x shc) θ α ι N C (dpbE ε) (dpbP ε) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro v
    show Jm ε * (Jm ε * v * Jm ε) * Jm ε = v
    simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one, hJJv]
  · intro v
    show (vᴴ)ᴴ = v
    exact Matrix.conjTranspose_conjTranspose v
  · intro v
    show Jm ε * vᴴ * Jm ε = (Jm ε * v * Jm ε)ᴴ
    simp only [Matrix.conjTranspose_mul, hJh, Matrix.mul_assoc]
  · intro v
    show Jm ε * dpbH U x shc v * Jm ε = dpbH U x shc (Jm ε * v * Jm ε)
    exact dpbH_theta hU hU' hJJ hJh hY shc dpb_shc_neg v
  · intro v
    show (dpbH U x shc v)ᴴ = dpbH U x shc vᴴ
    exact dpbH_conjTranspose U x shc dpb_shc_neg v
  · intro v
    show (U * dpbD x * Uᴴ) * dpbH U x (fun u => (shc u - 1) / u) v -
      dpbH U x (fun u => (shc u - 1) / u) v * (U * dpbD x * Uᴴ) = dpbH U x shc v - v
    rw [dpbH_ad_left x hU, hsub, dpbH_sub_one x hU']
  · intro v
    show dpbH U x (fun u => (shc u - 1) / u) ((U * dpbD x * Uᴴ) * v - v * (U * dpbD x * Uᴴ)) =
      dpbH U x shc v - v
    rw [dpbH_ad_right x hU, hsub, dpbH_sub_one x hU']
  · intro v
    show Jm ε * ((U * dpbD x * Uᴴ) * v - v * (U * dpbD x * Uᴴ)) * Jm ε =
      -((U * dpbD x * Uᴴ) * (Jm ε * v * Jm ε) - (Jm ε * v * Jm ε) * (U * dpbD x * Uᴴ))
    exact dpb_theta_ad hJJ hY v
  · intro v
    show Complex.I • (Complex.I • v) = -v
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  · intro v
    show Complex.I • dpbH U x shc v = dpbH U x shc (Complex.I • v)
    exact (dpbH_smul U x shc Complex.I v).symm
  · intro v
    show Jm ε * (Complex.I • v) * Jm ε = Complex.I • (Jm ε * v * Jm ε)
    rw [Matrix.mul_smul, Matrix.smul_mul]
  · intro v
    show (Complex.I • v)ᴴ = -(Complex.I • vᴴ)
    rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_I, neg_smul]
  · intro v
    exact dpbE_P v
  · intro w
    exact dpbP_E w

end ReciprocityTheory.ChartRestriction.DS
