import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.KerPNonzero
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock

noncomputable section
open scoped BigOperators ComplexConjugate Nat

namespace Formalism.L2.Th1.H

section ExpSeries

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

def powForm (l : V →L[ℂ] ℂ) (n : ℕ) : ContinuousMultilinearMap ℂ (fun _ : Fin n => V) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compContinuousLinearMap (fun _ => l)

/- English proof (translation)
Simplify using `[powForm]`.
-/
theorem powForm_diag (l : V →L[ℂ] ℂ) (n : ℕ) (y : V) : powForm l n (fun _ => y) = l y ^ n := by
  simp [powForm]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_powForm_le (l : V →L[ℂ] ℂ) (n : ℕ) : ‖powForm l n‖ ≤ ‖l‖ ^ n := by
  calc ‖powForm l n‖ ≤ ‖ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ‖ * ∏ _i : Fin n, ‖l‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖l‖ ^ n := by rw [ContinuousMultilinearMap.norm_mkPiAlgebra]; simp

def expTerm {X : Type*} (c : X → ℂ) (l : X → V →L[ℂ] ℂ) (n : ℕ) (x : X) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => V) ℂ :=
  (c x / (n ! : ℂ)) • powForm (l x) n

/- English proof (translation)
Establish `hn : ‖((n ! : ℕ) : ℂ)‖ = (n ! : ℝ)` using `by simp`. Rewrite using `[expTerm, norm_smul, norm_div, hn]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_expTerm_le {X : Type*} (c : X → ℂ) (l : X → V →L[ℂ] ℂ) (n : ℕ) (x : X) :
    ‖expTerm c l n x‖ ≤ ‖c x‖ * (‖l x‖ ^ n / (n ! : ℝ)) := by
  have hn : ‖((n ! : ℕ) : ℂ)‖ = (n ! : ℝ) := by simp
  rw [expTerm, norm_smul, norm_div, hn]
  calc ‖c x‖ / (n ! : ℝ) * ‖powForm (l x) n‖ ≤ ‖c x‖ / (n ! : ℝ) * ‖l x‖ ^ n :=
        mul_le_mul_of_nonneg_left (norm_powForm_le _ _) (by positivity)
    _ = ‖c x‖ * (‖l x‖ ^ n / (n ! : ℝ)) := by ring

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_expTerm_mul_le {X : Type*} (c : X → ℂ) (l : X → V →L[ℂ] ℂ) (n : ℕ) (x : X) (r : ℝ)
    (hr : 0 ≤ r) : ‖expTerm c l n x‖ * r ^ n ≤ ‖c x‖ * Real.exp (r * ‖l x‖) := by
  calc ‖expTerm c l n x‖ * r ^ n ≤ ‖c x‖ * (‖l x‖ ^ n / (n ! : ℝ)) * r ^ n :=
        mul_le_mul_of_nonneg_right (norm_expTerm_le c l n x) (pow_nonneg hr n)
    _ = ‖c x‖ * ((r * ‖l x‖) ^ n / (n ! : ℝ)) := by ring
    _ ≤ ‖c x‖ * Real.exp (r * ‖l x‖) :=
        mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp _ (by positivity) n) (norm_nonneg _)

/- English proof (translation)
Use `Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_) (h 1)` and prove the remaining obligations. Use `norm_expTerm_mul_le c l n x 1 zero_le_one` as an intermediate fact. Simplify using `using this`.
-/
theorem summable_norm_expTerm {X : Type*} (c : X → ℂ) (l : X → V →L[ℂ] ℂ)
    (h : ∀ r : ℝ, Summable fun x => ‖c x‖ * Real.exp (r * ‖l x‖)) (n : ℕ) :
    Summable fun x => ‖expTerm c l n x‖ := by
  refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_) (h 1)
  have := norm_expTerm_mul_le c l n x 1 zero_le_one
  simpa using this

def expFPS {X : Type*} (c : X → ℂ) (l : X → V →L[ℂ] ℂ) : FormalMultilinearSeries ℂ V ℂ :=
  fun n => ∑' x, expTerm c l n x

/- English proof (translation)
Apply `FormalMultilinearSeries.radius_eq_top_of_summable_norm` to reduce the goal to its premises. Introduce `r`. Establish `hb : ∀ n, ‖expFPS c l n‖ * (r : ℝ) ^ n ≤ (∑' x, ‖c x‖ * Real.exp ((2 * (r : ℝ)) * ‖l x‖)) * (1 / 2 : ℝ) ^ n`. Introduce `n`. Establish `hs` using `summable_norm_expTerm c l h n`.

Establish `h1 : ‖expFPS c l n‖ ≤ ∑' x, ‖expTerm c l n x‖` using `norm_tsum_le_tsum_norm hs`. Establish `h2 : ∀ x, ‖expTerm c l n x‖ * (r : ℝ) ^ n ≤ ‖c x‖ * Real.exp ((2 * (r : ℝ)) * ‖l x‖) * (1 / 2 : ℝ) ^ n`. Introduce `x`. Establish `h3` using `norm_expTerm_mul_le c l n x (2 * (r : ℝ)) (by positivity)`. Establish `e : ‖expTerm c l n x‖ * (r : ℝ) ^ n = ‖expTerm c l n x‖ * (2 * (r : ℝ)) ^ n * (1 / 2 : ℝ) ^ n`.

Rewrite using `[mul_assoc, ← mul_pow]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `mul_le_mul_of_nonneg_right h3 (by positivity)`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `Summable.of_nonneg_of_le (fun n => by positivity) hb (summable_geometric_two.mul_left _)`.
-/
theorem expFPS_radius {X : Type*} (c : X → ℂ) (l : X → V →L[ℂ] ℂ)
    (h : ∀ r : ℝ, Summable fun x => ‖c x‖ * Real.exp (r * ‖l x‖)) : (expFPS c l).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  have hb : ∀ n, ‖expFPS c l n‖ * (r : ℝ) ^ n ≤
      (∑' x, ‖c x‖ * Real.exp ((2 * (r : ℝ)) * ‖l x‖)) * (1 / 2 : ℝ) ^ n := by
    intro n
    have hs := summable_norm_expTerm c l h n
    have h1 : ‖expFPS c l n‖ ≤ ∑' x, ‖expTerm c l n x‖ := norm_tsum_le_tsum_norm hs
    have h2 : ∀ x, ‖expTerm c l n x‖ * (r : ℝ) ^ n ≤
        ‖c x‖ * Real.exp ((2 * (r : ℝ)) * ‖l x‖) * (1 / 2 : ℝ) ^ n := by
      intro x
      have h3 := norm_expTerm_mul_le c l n x (2 * (r : ℝ)) (by positivity)
      have e : ‖expTerm c l n x‖ * (r : ℝ) ^ n =
          ‖expTerm c l n x‖ * (2 * (r : ℝ)) ^ n * (1 / 2 : ℝ) ^ n := by
        rw [mul_assoc, ← mul_pow]
        congr 2
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_right h3 (by positivity)
    calc ‖expFPS c l n‖ * (r : ℝ) ^ n ≤ (∑' x, ‖expTerm c l n x‖) * (r : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = ∑' x, ‖expTerm c l n x‖ * (r : ℝ) ^ n := tsum_mul_right.symm
      _ ≤ ∑' x, ‖c x‖ * Real.exp ((2 * (r : ℝ)) * ‖l x‖) * (1 / 2 : ℝ) ^ n :=
          Summable.tsum_le_tsum h2 (hs.mul_right _) ((h (2 * (r : ℝ))).mul_right _)
      _ = (∑' x, ‖c x‖ * Real.exp ((2 * (r : ℝ)) * ‖l x‖)) * (1 / 2 : ℝ) ^ n := tsum_mul_right
  exact Summable.of_nonneg_of_le (fun n => by positivity) hb (summable_geometric_two.mul_left _)

/- English proof (translation)
Establish `hterm : ∀ n x, expTerm c l n x (fun _ => y) = c x * (l x y) ^ n / (n ! : ℂ)`. Introduce `n x`. Rewrite using `[expTerm, ContinuousMultilinearMap.smul_apply, powForm_diag, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hev : ∀ n, expFPS c l n (fun _ => y) = ∑' x, c x * (l x y) ^ n / (n ! : ℂ)`.

Introduce `n`. Establish `hs : HasSum (fun x => expTerm c l n x) (expFPS c l n)` using `(Summable.of_norm (summable_norm_expTerm c l h n)).hasSum`. Establish `h1` using `hs.mapL (ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => V) ℂ (fun _ => y))`. Conclude with `h1.tsum_eq.symm.trans (tsum_congr fun x => hterm n x)`. Set `g : X × ℕ → ℂ` to `fun p => c p.1 * (l p.1 y) ^ p.2 / (p.2 ! : ℂ)`.

Establish `hfib : ∀ x, HasSum (fun n => g (x, n)) (c x * Complex.exp (l x y))`. Introduce `x`. Establish `h1` using `NormedSpace.expSeries_div_hasSum_exp (l x y)`. Rewrite `h1` using `[← Complex.exp_eq_exp_ℂ]`. Establish `h2` using `h1.mul_left (c x)`.

Simplify `h2` using `[g, mul_div_assoc]`. Establish `hg : ∀ p : X × ℕ, ‖g p‖ = ‖c p.1‖ * (‖l p.1 y‖ ^ p.2 / (p.2 ! : ℝ))`. Introduce `p`. Establish `hn : ‖((p.2 ! : ℕ) : ℂ)‖ = (p.2 ! : ℝ)` using `by simp`. Simplify using `only [g, norm_div, norm_mul, norm_pow, hn]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hnorm : Summable fun p : X × ℕ => ‖g p‖`. Repeatedly rewrite using `[hg]`. Rewrite using `[summable_prod_of_nonneg (fun _ => by positivity)]`. Use `⟨fun x => by simpa using (Real.summable_pow_div_factorial ‖l x y‖).mul_left ‖c x‖, ?_⟩` and prove the remaining obligations.

Use `Summable.of_nonneg_of_le (fun x => by positivity) (fun x => ?_) (h ‖y‖)` and prove the remaining obligations. Establish `he` using `NormedSpace.expSeries_div_hasSum_exp (‖l x y‖)`. Rewrite `he` using `[← Real.exp_eq_exp_ℝ]`. Simplify using `only`. Rewrite using `[tsum_mul_left, he.tsum_eq]`.

Use `mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)` and prove the remaining obligations. Use `(l x).le_opNorm y` as an intermediate fact. Combine the linear relations using `[mul_comm ‖y‖ ‖l x‖]`. Establish `hsum : Summable g` using `hnorm.of_norm`. Establish `htot : HasSum g (∑' x, c x * Complex.exp (l x y))`.

Establish `h1` using `hsum.hasSum`. Rewrite `h1` using `[hsum.tsum_prod' (fun x => (hfib x).summable)]`. Establish `e : (fun b => ∑' n, g (b, n)) = fun b => c b * Complex.exp (l b y)`. Use function extensionality and compare the values at `fun b => (hfib b).tsum_eq`. Rewrite `h1` using `[e]`.

Conclude with `h1`. Establish `hswap : HasSum (fun p : ℕ × X => g (p.2, p.1)) (∑' x, c x * Complex.exp (l x y))` using `(Equiv.prodComm ℕ X).hasSum_iff.2 htot`. Establish `hfin` using `hswap.prod_fiberwise (fun n => (hswap.summable.prod_factor n).hasSum)`. Use `hfin using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `n`.

Rewrite using `[hev n]`.
-/
theorem expFPS_hasSum {X : Type*} (c : X → ℂ) (l : X → V →L[ℂ] ℂ)
    (h : ∀ r : ℝ, Summable fun x => ‖c x‖ * Real.exp (r * ‖l x‖)) (y : V) :
    HasSum (fun n => expFPS c l n fun _ => y) (∑' x, c x * Complex.exp (l x y)) := by
  have hterm : ∀ n x, expTerm c l n x (fun _ => y) = c x * (l x y) ^ n / (n ! : ℂ) := by
    intro n x
    rw [expTerm, ContinuousMultilinearMap.smul_apply, powForm_diag, smul_eq_mul]
    ring
  have hev : ∀ n, expFPS c l n (fun _ => y) = ∑' x, c x * (l x y) ^ n / (n ! : ℂ) := by
    intro n
    have hs : HasSum (fun x => expTerm c l n x) (expFPS c l n) :=
      (Summable.of_norm (summable_norm_expTerm c l h n)).hasSum
    have h1 := hs.mapL (ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => V) ℂ (fun _ => y))
    exact h1.tsum_eq.symm.trans (tsum_congr fun x => hterm n x)
  let g : X × ℕ → ℂ := fun p => c p.1 * (l p.1 y) ^ p.2 / (p.2 ! : ℂ)
  have hfib : ∀ x, HasSum (fun n => g (x, n)) (c x * Complex.exp (l x y)) := by
    intro x
    have h1 := NormedSpace.expSeries_div_hasSum_exp (l x y)
    rw [← Complex.exp_eq_exp_ℂ] at h1
    have h2 := h1.mul_left (c x)
    simpa [g, mul_div_assoc] using h2
  have hg : ∀ p : X × ℕ, ‖g p‖ = ‖c p.1‖ * (‖l p.1 y‖ ^ p.2 / (p.2 ! : ℝ)) := by
    intro p
    have hn : ‖((p.2 ! : ℕ) : ℂ)‖ = (p.2 ! : ℝ) := by simp
    simp only [g, norm_div, norm_mul, norm_pow, hn]
    ring
  have hnorm : Summable fun p : X × ℕ => ‖g p‖ := by
    simp_rw [hg]
    rw [summable_prod_of_nonneg (fun _ => by positivity)]
    refine ⟨fun x => by simpa using (Real.summable_pow_div_factorial ‖l x y‖).mul_left ‖c x‖, ?_⟩
    refine Summable.of_nonneg_of_le (fun x => by positivity) (fun x => ?_) (h ‖y‖)
    have he := NormedSpace.expSeries_div_hasSum_exp (‖l x y‖)
    rw [← Real.exp_eq_exp_ℝ] at he
    dsimp only
    rw [tsum_mul_left, he.tsum_eq]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    have := (l x).le_opNorm y
    linarith [mul_comm ‖y‖ ‖l x‖]
  have hsum : Summable g := hnorm.of_norm
  have htot : HasSum g (∑' x, c x * Complex.exp (l x y)) := by
    have h1 := hsum.hasSum
    rw [hsum.tsum_prod' (fun x => (hfib x).summable)] at h1
    have e : (fun b => ∑' n, g (b, n)) = fun b => c b * Complex.exp (l b y) :=
      funext fun b => (hfib b).tsum_eq
    rw [e] at h1
    exact h1
  have hswap : HasSum (fun p : ℕ × X => g (p.2, p.1)) (∑' x, c x * Complex.exp (l x y)) :=
    (Equiv.prodComm ℕ X).hasSum_iff.2 htot
  have hfin := hswap.prod_fiberwise (fun n => (hswap.summable.prod_factor n).hasSum)
  convert hfin using 1
  funext n
  rw [hev n]

end ExpSeries

/- English proof (translation)
Unfold `ExpSeriesEntire`. Introduce `V _ _ X c ℓ h z _`. Establish `hfps : HasFPowerSeriesOnBall (fun z => ∑' x, c x * Complex.exp (ℓ x z)) (expFPS c ℓ) 0 ⊤` using `{ r_le := by rw [expFPS_radius c ℓ h] r_pos := ENNReal.zero_lt_top hasSum := fun {y} _ => by simpa using expFPS_hasSum c ℓ h y }`. Conclude with `hfps.analyticAt_of_mem (by simp)`.
-/
theorem exp_series_entire : ExpSeriesEntire := by
  unfold ExpSeriesEntire
  intro V _ _ X c ℓ h z _
  have hfps : HasFPowerSeriesOnBall (fun z => ∑' x, c x * Complex.exp (ℓ x z)) (expFPS c ℓ) 0 ⊤ :=
    { r_le := by rw [expFPS_radius c ℓ h]
      r_pos := ENNReal.zero_lt_top
      hasSum := fun {y} _ => by simpa using expFPS_hasSum c ℓ h y }
  exact hfps.analyticAt_of_mem (by simp)

section KerP

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

def flipR (H : Sesq V) : V →ₗ[ℝ] (V →L[ℂ] ℂ) where
  toFun u := LinearMap.toContinuousLinearMap (H.flip u)
  map_add' := by intro a b; ext z; simp
  map_smul' := by
    intro r u
    ext z
    show H z (r • u) = r • H z u
    rw [← Complex.coe_smul r u, map_smulₛₗ, Complex.conj_ofReal, smul_eq_mul, Complex.real_smul]

/- English proof (translation)
Set `T : V →L[ℝ] (V →L[ℂ] ℂ)` to `LinearMap.toContinuousLinearMap (flipR H)`. Conclude with `⟨‖T‖, norm_nonneg _, fun u => T.le_opNorm u⟩`.
-/
theorem exists_form_bound (H : Sesq V) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u, ‖LinearMap.toContinuousLinearMap (H.flip u)‖ ≤ K * ‖u‖ := by
  let T : V →L[ℝ] (V →L[ℂ] ℂ) := LinearMap.toContinuousLinearMap (flipR H)
  exact ⟨‖T‖, norm_nonneg _, fun u => T.le_opNorm u⟩

def kC (H : Sesq V) (α : V → ℂ) (w x : V) : ℂ :=
  α x * Complex.exp ((Real.pi : ℂ) * H x w - (Real.pi : ℂ) * H x x / 2)

def kL (H : Sesq V) (w x : V) : V →L[ℂ] ℂ :=
  (Real.pi : ℂ) • LinearMap.toContinuousLinearMap (H.flip (w - x))

/- English proof (translation)
Simplify using `only [opU, kerK, kC, kL, ContinuousLinearMap.smul_apply, LinearMap.coe_toContinuousLinearMap', LinearMap.flip_apply, smul_eq_mul, map_add, map_sub, LinearMap.add_apply]`. Rewrite using `[mul_assoc]`. Use `congr 1`. Rewrite using `[← Complex.exp_add, ← Complex.exp_add]`. Use `congr 1`.

Simplify using `only [ContinuousLinearMap.sub_apply, LinearMap.coe_toContinuousLinearMap', LinearMap.flip_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem term_eq (H : Sesq V) (α : V → ℂ) (w x z : V) :
    α x * opU H x (kerK H w) z = kC H α w x * Complex.exp (kL H w x z) := by
  simp only [opU, kerK, kC, kL, ContinuousLinearMap.smul_apply, LinearMap.coe_toContinuousLinearMap',
    LinearMap.flip_apply, smul_eq_mul, map_add, map_sub, LinearMap.add_apply]
  rw [mul_assoc]
  congr 1
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [ContinuousLinearMap.sub_apply, LinearMap.coe_toContinuousLinearMap', LinearMap.flip_apply]
  ring

/- English proof (translation)
Rewrite using `[← sub_nonneg]`. Establish `e : a * t ^ 2 + b ^ 2 / (4 * a) - b * t = (2 * a * t - b) ^ 2 / (4 * a)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Check the signs of the components of the expression.
-/
theorem quad_bound (a b t : ℝ) (ha : 0 < a) : b * t ≤ a * t ^ 2 + b ^ 2 / (4 * a) := by
  rw [← sub_nonneg]
  have e : a * t ^ 2 + b ^ 2 / (4 * a) - b * t = (2 * a * t - b) ^ 2 / (4 * a) := by
    field_simp
    ring
  rw [e]
  positivity

/- English proof (translation)
Take `⟨c0, C0, hc0, hC0, hn⟩` from `hN V H hH hP`. Take `⟨K, hK0, hK⟩` from `exists_form_bound H`. Establish `ha0 : 0 < Real.pi * c0 / 2` using `by positivity`. Take `⟨u, hu, hub⟩` from `hS V Λ hL (Real.pi * c0 / 2 / 2) 0 (by positivity)`. Use `Summable.of_nonneg_of_le (fun x => by positivity) (fun x => ?_) (hu.mul_left (Real.exp ((Real.pi * K * ‖w‖ + |r| * Real.pi * K) ^ 2 / (4 * (Real.pi * c0 / 2 / 2)) + |r| * Real.pi * K * ‖w‖)))` and prove the remaining obligations.

Establish `hux` using `hub x 0 (by simp)`. Simplify using `only [sub_zero] at hux`. Establish `hαx : ‖α x‖ = 1`. Apply the tactic sequence `rcases hα.1 x x.2 with h | h <;> simp [h]`. Establish `hxw : ‖H x w‖ ≤ K * ‖w‖ * ‖(x : V)‖`.

Establish `h1 : H x w = LinearMap.toContinuousLinearMap (H.flip w) x` using `rfl`. Rewrite using `[h1]`. Conclude with `((LinearMap.toContinuousLinearMap (H.flip w)).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hK w) (norm_nonneg _))`. Establish `hxx : c0 * ‖(x : V)‖ ^ 2 ≤ (H x x).re` using `(hn x).1`. Establish `hkL : ‖kL H w x‖ ≤ Real.pi * (K * (‖w‖ + ‖(x : V)‖))`.

Rewrite using `[kL, norm_smul]`. Establish `hpi : ‖(Real.pi : ℂ)‖ = Real.pi` using `by simp [Real.pi_pos.le]`. Rewrite using `[hpi]`. Apply `mul_le_mul_of_nonneg_left _ Real.pi_pos.le` to reduce the goal to its premises. Conclude with `(hK (w - x)).trans (mul_le_mul_of_nonneg_left (norm_sub_le _ _) hK0)`.

Establish `hre : (((Real.pi : ℂ) * H x w - (Real.pi : ℂ) * H x x / 2)).re ≤ Real.pi * (K * ‖w‖ * ‖(x : V)‖) - Real.pi * (c0 * ‖(x : V)‖ ^ 2) / 2`. Establish `e : (((Real.pi : ℂ) * H x w - (Real.pi : ℂ) * H x x / 2)).re = Real.pi * (H x w).re - Real.pi * (H x x).re / 2` using `by simp`. Rewrite using `[e]`. Establish `h1 : (H x w).re ≤ K * ‖w‖ * ‖(x : V)‖` using `(Complex.re_le_norm _).trans hxw`. Establish `h2` using `mul_le_mul_of_nonneg_left h1 Real.pi_pos.le`.

Establish `h3` using `mul_le_mul_of_nonneg_left hxx Real.pi_pos.le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hkC : ‖kC H α w x‖ = Real.exp ((((Real.pi : ℂ) * H x w - (Real.pi : ℂ) * H x x / 2)).re)`. Rewrite using `[kC, norm_mul, hαx, Complex.norm_exp, one_mul]`. Establish `hr : r * ‖kL H w x‖ ≤ |r| * (Real.pi * (K * (‖w‖ + ‖(x : V)‖)))` using `(mul_le_mul_of_nonneg_right (le_abs_self r) (norm_nonneg _)).trans (mul_le_mul_of_nonneg_left hkL (abs_nonneg r))`.

Establish `hq` using `quad_bound (Real.pi * c0 / 2 / 2) (Real.pi * K * ‖w‖ + |r| * Real.pi * K) ‖(x : V)‖ (by positivity)`. Rewrite using `[hkC, ← Real.exp_add]`. Combine the equalities or inequalities in the displayed calculation. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Use polynomial arithmetic with `[hre, hr, hq]`.

Use `_ = Real.exp ((Real.pi * K * ‖w‖ + |r| * Real.pi * K) ^ 2 / (4 * (Real.pi * c0 / 2 / 2)) + |r| * Real.pi * K * ‖w‖) * Real.exp (-(Real.pi * c0 / 2 / 2) * ‖(x : V)‖ ^ 2) := Real.exp_add _ _`. Use `_ ≤ _ := mul_le_mul_of_nonneg_left hux (Real.exp_pos _).le`.
-/
theorem kernel_summable_bound (hS : LatGaussSummable) (hN : FormNorm) (H : Sesq V) (Λ : AddSubgroup V)
    (α : V → ℂ) (hH : IsHerm H) (hP : IsPosDef H) (hL : IsLat Λ) (hα : IsSemiChar H Λ α) (w : V) (r : ℝ) :
    Summable fun x : Λ => ‖kC H α w x‖ * Real.exp (r * ‖kL H w x‖) := by
  obtain ⟨c0, C0, hc0, hC0, hn⟩ := hN V H hH hP
  obtain ⟨K, hK0, hK⟩ := exists_form_bound H
  have ha0 : 0 < Real.pi * c0 / 2 := by positivity
  obtain ⟨u, hu, hub⟩ := hS V Λ hL (Real.pi * c0 / 2 / 2) 0 (by positivity)
  refine Summable.of_nonneg_of_le (fun x => by positivity) (fun x => ?_)
    (hu.mul_left (Real.exp ((Real.pi * K * ‖w‖ + |r| * Real.pi * K) ^ 2 / (4 * (Real.pi * c0 / 2 / 2)) +
      |r| * Real.pi * K * ‖w‖)))
  have hux := hub x 0 (by simp)
  simp only [sub_zero] at hux
  have hαx : ‖α x‖ = 1 := by
    rcases hα.1 x x.2 with h | h <;> simp [h]
  have hxw : ‖H x w‖ ≤ K * ‖w‖ * ‖(x : V)‖ := by
    have h1 : H x w = LinearMap.toContinuousLinearMap (H.flip w) x := rfl
    rw [h1]
    exact ((LinearMap.toContinuousLinearMap (H.flip w)).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (hK w) (norm_nonneg _))
  have hxx : c0 * ‖(x : V)‖ ^ 2 ≤ (H x x).re := (hn x).1
  have hkL : ‖kL H w x‖ ≤ Real.pi * (K * (‖w‖ + ‖(x : V)‖)) := by
    rw [kL, norm_smul]
    have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by simp [Real.pi_pos.le]
    rw [hpi]
    apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
    exact (hK (w - x)).trans (mul_le_mul_of_nonneg_left (norm_sub_le _ _) hK0)
  have hre : (((Real.pi : ℂ) * H x w - (Real.pi : ℂ) * H x x / 2)).re ≤
      Real.pi * (K * ‖w‖ * ‖(x : V)‖) - Real.pi * (c0 * ‖(x : V)‖ ^ 2) / 2 := by
    have e : (((Real.pi : ℂ) * H x w - (Real.pi : ℂ) * H x x / 2)).re =
        Real.pi * (H x w).re - Real.pi * (H x x).re / 2 := by simp
    rw [e]
    have h1 : (H x w).re ≤ K * ‖w‖ * ‖(x : V)‖ := (Complex.re_le_norm _).trans hxw
    have h2 := mul_le_mul_of_nonneg_left h1 Real.pi_pos.le
    have h3 := mul_le_mul_of_nonneg_left hxx Real.pi_pos.le
    linarith
  have hkC : ‖kC H α w x‖ = Real.exp ((((Real.pi : ℂ) * H x w - (Real.pi : ℂ) * H x x / 2)).re) := by
    rw [kC, norm_mul, hαx, Complex.norm_exp, one_mul]
  have hr : r * ‖kL H w x‖ ≤ |r| * (Real.pi * (K * (‖w‖ + ‖(x : V)‖))) :=
    (mul_le_mul_of_nonneg_right (le_abs_self r) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hkL (abs_nonneg r))
  have hq := quad_bound (Real.pi * c0 / 2 / 2) (Real.pi * K * ‖w‖ + |r| * Real.pi * K) ‖(x : V)‖ (by positivity)
  rw [hkC, ← Real.exp_add]
  calc Real.exp ((((Real.pi : ℂ) * H x w - (Real.pi : ℂ) * H x x / 2)).re + r * ‖kL H w x‖)
      ≤ Real.exp (((Real.pi * K * ‖w‖ + |r| * Real.pi * K) ^ 2 / (4 * (Real.pi * c0 / 2 / 2)) +
          |r| * Real.pi * K * ‖w‖) + (-(Real.pi * c0 / 2 / 2) * ‖(x : V)‖ ^ 2)) := by
        apply Real.exp_le_exp.2
        nlinarith [hre, hr, hq]
    _ = Real.exp ((Real.pi * K * ‖w‖ + |r| * Real.pi * K) ^ 2 / (4 * (Real.pi * c0 / 2 / 2)) +
          |r| * Real.pi * K * ‖w‖) * Real.exp (-(Real.pi * c0 / 2 / 2) * ‖(x : V)‖ ^ 2) := Real.exp_add _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hux (Real.exp_pos _).le

end KerP

/- English proof (translation)
Unfold `KerPTh`. Introduce `V _ _ _ H Λ α hH hP hL hα w`. Use `⟨fun z => ?_, ?_⟩` and prove the remaining obligations. Establish `hb` using `kernel_summable_bound hS hN H Λ α hH hP hL hα w ‖z‖`. Use `Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => ?_) hb)` and prove the remaining obligations.

Rewrite using `[term_eq, norm_mul, Complex.norm_exp]`. Use `mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `show AnalyticOnNhd ℂ (fun z => kerP H α Λ z w) Set.univ ∧ (fun z => kerP H α Λ z w) ∈ fixedBy H α Λ`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Establish `hfun : (fun z => kerP H α Λ z w) = fun z => ∑' x : Λ, kC H α w x * Complex.exp (kL H w x z)`. Use function extensionality and compare the values at `fun z => tsum_congr fun x => term_eq H α w x z`. Rewrite using `[hfun]`. Conclude with `hE V Λ (fun x => kC H α w x) (fun x => kL H w x) (kernel_summable_bound hS hN H Λ α hH hP hL hα w)`. Introduce `y hy z`.

Establish `hmul` using `heisenbergMul V H hH`. Use `show α y * (kerP H α Λ (z + y) w * Complex.exp (-(Real.pi : ℂ) * H z y - (Real.pi : ℂ) * H y y / 2)) = kerP H α Λ z w`. Unfold `kerP`. Rewrite using `[← tsum_mul_right, ← tsum_mul_left]`. Establish `key : ∀ x : Λ, α y * (α x * opU H x (kerK H w) (z + y) * Complex.exp (-(Real.pi : ℂ) * H z y - (Real.pi : ℂ) * H y y / 2)) = α ((x : V) + y) * opU H ((x : V) + y) (kerK H w) z`.

Introduce `x`. Establish `h1 : opU H x (kerK H w) (z + y) * Complex.exp (-(Real.pi : ℂ) * H z y - (Real.pi : ℂ) * H y y / 2) = opU H y (opU H x (kerK H w)) z` using `rfl`. Establish `h2` using `hmul y x (kerK H w) z`. Establish `h3` using `hα.2 x x.2 y hy`. Establish `h4 : altE H y x = -altE H x y`.

Unfold `altE`. Rewrite using `[hH x y, Complex.conj_im]`. Establish `h5 : Complex.exp (-(Real.pi : ℂ) * Complex.I * ((altE H y x : ℝ) : ℂ)) = Complex.exp ((Real.pi : ℂ) * Complex.I * ((altE H x y : ℝ) : ℂ))`. Rewrite using `[h4]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[mul_assoc (α x), h1, h2, h5, h3, add_comm y (x : V)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[tsum_congr key]`.

Conclude with `(Equiv.addRight (⟨y, hy⟩ : Λ)).tsum_eq (fun x : Λ => α (x : V) * opU H (x : V) (kerK H w) z)`.
-/
theorem KerPTh_of (hE : ExpSeriesEntire) (hS : LatGaussSummable) (hN : FormNorm) : KerPTh := by
  unfold KerPTh
  intro V _ _ _ H Λ α hH hP hL hα w
  refine ⟨fun z => ?_, ?_⟩
  · have hb := kernel_summable_bound hS hN H Λ α hH hP hL hα w ‖z‖
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => ?_) hb)
    rw [term_eq, norm_mul, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    calc (kL H w x z).re ≤ ‖kL H w x z‖ := Complex.re_le_norm _
      _ ≤ ‖kL H w x‖ * ‖z‖ := (kL H w x).le_opNorm z
      _ = ‖z‖ * ‖kL H w x‖ := mul_comm _ _
  show AnalyticOnNhd ℂ (fun z => kerP H α Λ z w) Set.univ ∧ (fun z => kerP H α Λ z w) ∈ fixedBy H α Λ
  refine ⟨?_, ?_⟩
  · have hfun : (fun z => kerP H α Λ z w) = fun z => ∑' x : Λ, kC H α w x * Complex.exp (kL H w x z) :=
      funext fun z => tsum_congr fun x => term_eq H α w x z
    rw [hfun]
    exact hE V Λ (fun x => kC H α w x) (fun x => kL H w x) (kernel_summable_bound hS hN H Λ α hH hP hL hα w)
  · intro y hy z
    have hmul := heisenbergMul V H hH
    show α y * (kerP H α Λ (z + y) w *
      Complex.exp (-(Real.pi : ℂ) * H z y - (Real.pi : ℂ) * H y y / 2)) = kerP H α Λ z w
    unfold kerP
    rw [← tsum_mul_right, ← tsum_mul_left]
    have key : ∀ x : Λ, α y * (α x * opU H x (kerK H w) (z + y) *
        Complex.exp (-(Real.pi : ℂ) * H z y - (Real.pi : ℂ) * H y y / 2)) =
        α ((x : V) + y) * opU H ((x : V) + y) (kerK H w) z := by
      intro x
      have h1 : opU H x (kerK H w) (z + y) * Complex.exp (-(Real.pi : ℂ) * H z y - (Real.pi : ℂ) * H y y / 2) =
          opU H y (opU H x (kerK H w)) z := rfl
      have h2 := hmul y x (kerK H w) z
      have h3 := hα.2 x x.2 y hy
      have h4 : altE H y x = -altE H x y := by
        unfold altE
        rw [hH x y, Complex.conj_im]
      have h5 : Complex.exp (-(Real.pi : ℂ) * Complex.I * ((altE H y x : ℝ) : ℂ)) =
          Complex.exp ((Real.pi : ℂ) * Complex.I * ((altE H x y : ℝ) : ℂ)) := by
        rw [h4]
        congr 1
        push_cast
        ring
      rw [mul_assoc (α x), h1, h2, h5, h3, add_comm y (x : V)]
      ring
    rw [tsum_congr key]
    exact (Equiv.addRight (⟨y, hy⟩ : Λ)).tsum_eq (fun x : Λ => α (x : V) * opU H (x : V) (kerK H w) z)

end Formalism.L2.Th1.H
