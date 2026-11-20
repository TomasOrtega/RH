import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.SmoothCentral

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
Establish `h : (fun x : Matrix (Fin n) (Fin n) ℂ => x.det) = fun x => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, x (σ i) i`. Use function extensionality and compare the values at `x`. Rewrite using `[Matrix.det_apply]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Units.smul_def, zsmul_eq_mul]`.

Rewrite using `[h]`. Use `ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => ?_)` and prove the remaining obligations. Conclude with `contDiff_apply_apply (𝕜 := ℝ) (E := ℂ) (σ i) i`.
-/
theorem contDiff_det_real : ContDiff ℝ ∞ (fun x : Matrix (Fin n) (Fin n) ℂ => x.det) := by
  have h : (fun x : Matrix (Fin n) (Fin n) ℂ => x.det) =
      fun x => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, x (σ i) i := by
    funext x
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
  rw [h]
  refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => ?_)
  exact contDiff_apply_apply (𝕜 := ℝ) (E := ℂ) (σ i) i

/- English proof (translation)
Establish `h` using `congrArg Matrix.det hg`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]`. Establish `hJ : (Jm ε).det * (Jm ε).det = 1` using `by rw [← Matrix.det_mul, Jm_mul_self, Matrix.det_one]`. Establish `hJ0 : (Jm ε).det ≠ 0` using `left_ne_zero_of_mul_eq_one hJ`. Establish `h2 : star g.det * g.det = 1`.

Establish `: (star g.det * g.det) * (Jm ε).det = 1 * (Jm ε).det` using `by linear_combination h`. Conclude with `mul_right_cancel₀ hJ0 this`. Establish `h3 : ((Complex.normSq g.det : ℝ) : ℂ) = 1` using `by rw [Complex.normSq_eq_conj_mul_self]; exact h2`. Establish `h4 : Complex.normSq g.det = 1` using `by exact_mod_cast h3`. Establish `h5 : ‖g.det‖ ^ 2 = 1` using `by rw [← Complex.normSq_eq_norm_sq]; exact h4`.

Use `norm_nonneg g.det` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem norm_det_of_inUJ {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : ‖g.det‖ = 1 := by
  have h := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
  have hJ : (Jm ε).det * (Jm ε).det = 1 := by rw [← Matrix.det_mul, Jm_mul_self, Matrix.det_one]
  have hJ0 : (Jm ε).det ≠ 0 := left_ne_zero_of_mul_eq_one hJ
  have h2 : star g.det * g.det = 1 := by
    have : (star g.det * g.det) * (Jm ε).det = 1 * (Jm ε).det := by linear_combination h
    exact mul_right_cancel₀ hJ0 this
  have h3 : ((Complex.normSq g.det : ℝ) : ℂ) = 1 := by rw [Complex.normSq_eq_conj_mul_self]; exact h2
  have h4 : Complex.normSq g.det = 1 := by exact_mod_cast h3
  have h5 : ‖g.det‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact h4
  have := norm_nonneg g.det
  nlinarith

/- English proof (translation)
Unfold `inUJ at *`. Establish `hc2 : star c * c = 1`. Establish `: ((Complex.normSq c : ℝ) : ℂ) = 1`. Rewrite using `[Complex.normSq_eq_norm_sq, hc]`. Evaluate the numerical expressions.

Rewrite `this` using `[Complex.normSq_eq_conj_mul_self]`. Conclude with `this`. Rewrite using `[Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hg, mul_comm, hc2, one_smul]`.
-/
theorem inUJ_smul {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) {c : ℂ} (hc : ‖c‖ = 1) :
    inUJ ε (c • g) := by
  unfold inUJ at *
  have hc2 : star c * c = 1 := by
    have : ((Complex.normSq c : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hc]; norm_num
    rw [Complex.normSq_eq_conj_mul_self] at this; exact this
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hg, mul_comm, hc2, one_smul]

/- English proof (translation)
The claim follows from `(pow_eq_one_iff_of_nonneg (norm_nonneg w) hk).1 h`.
-/
theorem norm_eq_one_of_pow {w : ℂ} {k : ℕ} (hk : k ≠ 0) (h : ‖w‖ ^ k = 1) : ‖w‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg w) hk).1 h

/- English proof (translation)
Introduce `n hn ε m f f' hf hS g₀ hg₀`. Establish `hn0 : n ≠ 0` using `by omega`. Establish `hnC : (n : ℂ) ≠ 0` using `by exact_mod_cast hn0`. Use `set d₀ := g₀.det with hd₀def`. Establish `hd₀ : ‖d₀‖ = 1` using `norm_det_of_inUJ hg₀`.

Establish `hd₀ne : d₀ ≠ 0` using `by intro h; rw [h, norm_zero] at hd₀; exact zero_ne_one hd₀`. Use `set z₀ := Complex.exp (Complex.log d₀ / n) with hz₀def`. Establish `hz₀n : z₀ ^ n = d₀`. Rewrite using `[hz₀def, ← Complex.exp_nat_mul]`. Establish `: (n : ℂ) * (Complex.log d₀ / n) = Complex.log d₀` using `by field_simp`.

Rewrite using `[this, Complex.exp_log hd₀ne]`. Establish `hz₀ne : z₀ ≠ 0` using `Complex.exp_ne_zero _`. Establish `hz₀norm : ‖z₀‖ = 1` using `norm_eq_one_of_pow hn0 (by rw [← norm_pow, hz₀n, hd₀])`. Use `set L : Matrix (Fin n) (Fin n) ℂ → ℂ := fun x => Complex.log (x.det / d₀) with hLdef`. Use `set ζ : Matrix (Fin n) (Fin n) ℂ → ℂ := fun x => z₀ * Complex.exp (L x / n) with hζdef`.

Use `set ζi : Matrix (Fin n) (Fin n) ℂ → ℂ := fun x => z₀⁻¹ * Complex.exp (-(L x / n)) with hζidef`. Use `set U : Set (Matrix (Fin n) (Fin n) ℂ) := {x | x.det / d₀ ∈ Complex.slitPlane} with hUdef`. Establish `hUo : IsOpen U` using `Complex.isOpen_slitPlane.preimage ((contDiff_det_real.continuous).div_const _)`. Establish `hg₀U : g₀ ∈ U` using `by show g₀.det / d₀ ∈ Complex.slitPlane`. Rewrite using `[← hd₀def, div_self hd₀ne]`.

Conclude with `Complex.one_mem_slitPlane`. Establish `hL : ContDiffOn ℝ ∞ L U`. Introduce `x hx`. Establish `h1 : ContDiffAt ℝ ∞ (fun x : Matrix (Fin n) (Fin n) ℂ => x.det / d₀) x` using `(contDiff_det_real.div_const d₀).contDiffAt`. Establish `h2 : ContDiffAt ℝ ∞ Complex.log (x.det / d₀)` using `(Complex.contDiffAt_log hx).restrict_scalars ℝ`.

Conclude with `(h2.comp x h1).contDiffWithinAt`. Establish `hζi : ContDiffOn ℝ ∞ ζi U` using `contDiffOn_const.mul ((hL.div_const _).neg.cexp)`. Establish `hζ : ContDiffOn ℝ ∞ ζ U` using `contDiffOn_const.mul ((hL.div_const _).cexp)`. Establish `hh : ContDiffOn ℝ ∞ (fun x => ζi x • x) U` using `hζi.smul contDiffOn_id`. Establish `hζζi : ∀ x, ζ x * ζi x = 1`.

Introduce `x`. Simplify using `only [hζdef, hζidef]`. Rewrite using `[mul_mul_mul_comm, mul_inv_cancel₀ hz₀ne, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]`. Establish `hζne : ∀ x, ζ x ≠ 0` using `fun x => left_ne_zero_of_mul_eq_one (hζζi x)`. Establish `hζn : ∀ x ∈ U, ζ x ^ n = x.det`.

Introduce `x hx`. Establish `hx0 : x.det / d₀ ≠ 0` using `Complex.slitPlane_ne_zero hx`. Simplify using `only [hζdef]`. Rewrite using `[mul_pow, hz₀n, ← Complex.exp_nat_mul]`. Establish `: (n : ℂ) * (L x / n) = L x` using `by field_simp`.

Rewrite using `[this]`. Simplify using `only [hLdef]`. Rewrite using `[Complex.exp_log hx0]`. Clear the denominators using the available nonvanishing facts. Establish `hζig₀ : ζi g₀ = z₀⁻¹`.

Simplify using `only [hζidef, hLdef]`. Rewrite using `[← hd₀def, div_self hd₀ne, Complex.log_one, zero_div, neg_zero, Complex.exp_zero, mul_one]`. Establish `hinvnorm : ‖z₀⁻¹‖ = 1` using `by rw [norm_inv, hz₀norm, inv_one]`. Establish `hg₁ : z₀⁻¹ • g₀ ∈ SUset ε`. Use `⟨inUJ_smul hg₀ hinvnorm, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.det_smul, Fintype.card_fin, inv_pow, hz₀n, ← hd₀def, inv_mul_cancel₀ hd₀ne]`. Take `⟨U', F', hU'o, hg₁U', hF', hF'eq⟩` from `hS _ hg₁`. Establish `hzpow : ContDiffOn ℝ ∞ (fun x => ζ x ^ m) U`. Introduce `x hx`. Take `⟨k, rfl | rfl⟩` from `Int.eq_nat_or_neg m`.

Simplify `(hζ x hx).pow k` using `only [zpow_natCast]`. Apply the tactic sequence `refine (((hζ x hx).pow k).inv (pow_ne_zero k (hζne x))).congr (fun y _ => ?_) ?_ <;>`. Simplify using `[_root_.zpow_neg]`. Use `⟨U ∩ (fun x => ζi x • x) ⁻¹' U', fun x => ζ x ^ m * F' (ζi x • x), hh.continuousOn.isOpen_inter_preimage hUo hU'o, ⟨hg₀U, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show ζi g₀ • g₀ ∈ U'`.

Rewrite using `[hζig₀]`. Conclude with `hg₁U'`. Conclude with `(hzpow.mono Set.inter_subset_left).mul (hF'.comp (hh.mono Set.inter_subset_left) fun x hx => hx.2)`. Introduce `x hx hxU`. Establish `hxdet : ‖x.det‖ = 1` using `norm_det_of_inUJ hxU`.

Establish `hnorm : ‖ζ x‖ = 1` using `norm_eq_one_of_pow hn0 (by rw [← norm_pow, hζn x hx.1, hxdet])`. Establish `hζi_eq : ζi x = (ζ x)⁻¹` using `eq_inv_of_mul_eq_one_right (hζζi x)`. Establish `hinorm : ‖ζi x‖ = 1` using `by rw [hζi_eq, norm_inv, hnorm, inv_one]`. Establish `hdet0 : x.det ≠ 0` using `by intro h; rw [h, norm_zero] at hxdet; exact zero_ne_one hxdet`. Establish `hmem : ζi x • x ∈ SUset ε`.

Use `⟨inUJ_smul hxU hinorm, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_smul, Fintype.card_fin, hζi_eq, inv_pow, hζn x hx.1, inv_mul_cancel₀ hdet0]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem smooth_of_central : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (m : ℤ) (f f' : Matrix (Fin n) (Fin n) ℂ → ℂ),
    (∀ z : ℂ, ‖z‖ = 1 → ∀ g ∈ SUset ε, f (z • g) = z ^ m * f' g) → SmoothS ε f' → SmoothOnG ε f := by
  intro n hn ε m f f' hf hS g₀ hg₀
  have hn0 : n ≠ 0 := by omega
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  set d₀ := g₀.det with hd₀def
  have hd₀ : ‖d₀‖ = 1 := norm_det_of_inUJ hg₀
  have hd₀ne : d₀ ≠ 0 := by intro h; rw [h, norm_zero] at hd₀; exact zero_ne_one hd₀
  set z₀ := Complex.exp (Complex.log d₀ / n) with hz₀def
  have hz₀n : z₀ ^ n = d₀ := by
    rw [hz₀def, ← Complex.exp_nat_mul]
    have : (n : ℂ) * (Complex.log d₀ / n) = Complex.log d₀ := by field_simp
    rw [this, Complex.exp_log hd₀ne]
  have hz₀ne : z₀ ≠ 0 := Complex.exp_ne_zero _
  have hz₀norm : ‖z₀‖ = 1 := norm_eq_one_of_pow hn0 (by rw [← norm_pow, hz₀n, hd₀])
  set L : Matrix (Fin n) (Fin n) ℂ → ℂ := fun x => Complex.log (x.det / d₀) with hLdef
  set ζ : Matrix (Fin n) (Fin n) ℂ → ℂ := fun x => z₀ * Complex.exp (L x / n) with hζdef
  set ζi : Matrix (Fin n) (Fin n) ℂ → ℂ := fun x => z₀⁻¹ * Complex.exp (-(L x / n)) with hζidef
  set U : Set (Matrix (Fin n) (Fin n) ℂ) := {x | x.det / d₀ ∈ Complex.slitPlane} with hUdef
  have hUo : IsOpen U := Complex.isOpen_slitPlane.preimage ((contDiff_det_real.continuous).div_const _)
  have hg₀U : g₀ ∈ U := by
    show g₀.det / d₀ ∈ Complex.slitPlane
    rw [← hd₀def, div_self hd₀ne]; exact Complex.one_mem_slitPlane
  have hL : ContDiffOn ℝ ∞ L U := by
    intro x hx
    have h1 : ContDiffAt ℝ ∞ (fun x : Matrix (Fin n) (Fin n) ℂ => x.det / d₀) x :=
      (contDiff_det_real.div_const d₀).contDiffAt
    have h2 : ContDiffAt ℝ ∞ Complex.log (x.det / d₀) := (Complex.contDiffAt_log hx).restrict_scalars ℝ
    exact (h2.comp x h1).contDiffWithinAt
  have hζi : ContDiffOn ℝ ∞ ζi U := contDiffOn_const.mul ((hL.div_const _).neg.cexp)
  have hζ : ContDiffOn ℝ ∞ ζ U := contDiffOn_const.mul ((hL.div_const _).cexp)
  have hh : ContDiffOn ℝ ∞ (fun x => ζi x • x) U := hζi.smul contDiffOn_id
  have hζζi : ∀ x, ζ x * ζi x = 1 := by
    intro x
    simp only [hζdef, hζidef]
    rw [mul_mul_mul_comm, mul_inv_cancel₀ hz₀ne, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
  have hζne : ∀ x, ζ x ≠ 0 := fun x => left_ne_zero_of_mul_eq_one (hζζi x)
  have hζn : ∀ x ∈ U, ζ x ^ n = x.det := by
    intro x hx
    have hx0 : x.det / d₀ ≠ 0 := Complex.slitPlane_ne_zero hx
    simp only [hζdef]
    rw [mul_pow, hz₀n, ← Complex.exp_nat_mul]
    have : (n : ℂ) * (L x / n) = L x := by field_simp
    rw [this]
    simp only [hLdef]
    rw [Complex.exp_log hx0]
    field_simp
  have hζig₀ : ζi g₀ = z₀⁻¹ := by
    simp only [hζidef, hLdef]
    rw [← hd₀def, div_self hd₀ne, Complex.log_one, zero_div, neg_zero, Complex.exp_zero, mul_one]
  have hinvnorm : ‖z₀⁻¹‖ = 1 := by rw [norm_inv, hz₀norm, inv_one]
  have hg₁ : z₀⁻¹ • g₀ ∈ SUset ε := by
    refine ⟨inUJ_smul hg₀ hinvnorm, ?_⟩
    rw [Matrix.det_smul, Fintype.card_fin, inv_pow, hz₀n, ← hd₀def, inv_mul_cancel₀ hd₀ne]
  obtain ⟨U', F', hU'o, hg₁U', hF', hF'eq⟩ := hS _ hg₁
  have hzpow : ContDiffOn ℝ ∞ (fun x => ζ x ^ m) U := by
    intro x hx
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
    · simpa only [zpow_natCast] using (hζ x hx).pow k
    · refine (((hζ x hx).pow k).inv (pow_ne_zero k (hζne x))).congr (fun y _ => ?_) ?_ <;>
        simp [_root_.zpow_neg]
  refine ⟨U ∩ (fun x => ζi x • x) ⁻¹' U', fun x => ζ x ^ m * F' (ζi x • x),
    hh.continuousOn.isOpen_inter_preimage hUo hU'o, ⟨hg₀U, ?_⟩, ?_, ?_⟩
  · show ζi g₀ • g₀ ∈ U'
    rw [hζig₀]; exact hg₁U'
  · exact (hzpow.mono Set.inter_subset_left).mul
      (hF'.comp (hh.mono Set.inter_subset_left) fun x hx => hx.2)
  · intro x hx hxU
    have hxdet : ‖x.det‖ = 1 := norm_det_of_inUJ hxU
    have hnorm : ‖ζ x‖ = 1 := norm_eq_one_of_pow hn0 (by rw [← norm_pow, hζn x hx.1, hxdet])
    have hζi_eq : ζi x = (ζ x)⁻¹ := eq_inv_of_mul_eq_one_right (hζζi x)
    have hinorm : ‖ζi x‖ = 1 := by rw [hζi_eq, norm_inv, hnorm, inv_one]
    have hdet0 : x.det ≠ 0 := by intro h; rw [h, norm_zero] at hxdet; exact zero_ne_one hxdet
    have hmem : ζi x • x ∈ SUset ε := by
      refine ⟨inUJ_smul hxU hinorm, ?_⟩
      rw [Matrix.det_smul, Fintype.card_fin, hζi_eq, inv_pow, hζn x hx.1, inv_mul_cancel₀ hdet0]
    calc f x = f (ζ x • (ζi x • x)) := by rw [smul_smul, hζζi, one_smul]
      _ = ζ x ^ m * f' (ζi x • x) := hf _ hnorm _ hmem
      _ = ζ x ^ m * F' (ζi x • x) := by rw [hF'eq _ hx.2 hmem]

end GlobalTheory.SmoothCentral
