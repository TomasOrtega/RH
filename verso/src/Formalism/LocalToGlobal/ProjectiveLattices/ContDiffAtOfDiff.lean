import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ContDiffOfDifferentiableFd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor

noncomputable section

namespace Formalism.L2.Pj.I2FramePointLemmas

open ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.PullbackSections NumberField
open scoped ContDiff

section Deriv

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

/- English proof (translation)
Unfold `polyDeriv`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Use `congr 1`. Establish `hL : (((Finsupp.toMultiset m).toList.map u : List V) : Multiset V) = (Finsupp.toMultiset m).map u`. Rewrite using `[← Multiset.map_coe, Multiset.coe_toList]`.

Rewrite using `[← hL, mD_coe hθ, lD_eq θ x _ (n := Multiset.card (Finsupp.toMultiset m)) (by rw [List.length_map, Multiset.length_toList])]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Simplify using `[List.get_eq_getElem]`.
-/
theorem polyDeriv_eq_mD' {θ : V → ℂ} {x : V} (hθ : ContDiffAt ℂ ω θ x) {ι : Type} (P : MvPolynomial ι ℂ)
    (u : ι → V) :
    polyDeriv P u θ x = ∑ m ∈ P.support, P.coeff m * mD θ x ((Finsupp.toMultiset m).map u) := by
  unfold polyDeriv
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  have hL : (((Finsupp.toMultiset m).toList.map u : List V) : Multiset V) =
      (Finsupp.toMultiset m).map u := by
    rw [← Multiset.map_coe, Multiset.coe_toList]
  rw [← hL, mD_coe hθ, lD_eq θ x _ (n := Multiset.card (Finsupp.toMultiset m))
    (by rw [List.length_map, Multiset.length_toList])]
  congr 1
  funext k
  simp [List.get_eq_getElem]

/- English proof (translation)
Rewrite using `[polyDeriv_eq_mD' hθ, polyDeriv_eq_mD' hθ, MvPolynomial.support_rename_of_injective hρ, Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective hρ h)]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_rename_mapDomain ρ hρ, ← Finsupp.toMultiset_map, Multiset.map_map]`.
-/
theorem polyDeriv_rename {θ : V → ℂ} {x : V} (hθ : ContDiffAt ℂ ω θ x) {ι κ : Type} (ρ : ι → κ)
    (hρ : Function.Injective ρ) (P : MvPolynomial ι ℂ) (v : κ → V) :
    polyDeriv (MvPolynomial.rename ρ P) v θ x = polyDeriv P (v ∘ ρ) θ x := by
  classical
  rw [polyDeriv_eq_mD' hθ, polyDeriv_eq_mD' hθ, MvPolynomial.support_rename_of_injective hρ,
    Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective hρ h)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_rename_mapDomain ρ hρ, ← Finsupp.toMultiset_map, Multiset.map_map]

/- English proof (translation)
Set `e : W ≃L[ℂ] (Fin (Module.finrank ℂ W) → ℂ)` to `(Module.finBasis ℂ W).equivFun.toContinuousLinearEquiv`. Establish `h1 : Differentiable ℂ (F ∘ e.symm)` using `hF.comp e.symm.differentiable`. Establish `h2 : AnalyticOnNhd ℂ (F ∘ e.symm) Set.univ` using `ReciprocityTheory.AnForm.Osgood.osgood _ _ _ isOpen_univ h1.differentiableOn`. Establish `h3 : ContDiff ℂ ω (F ∘ e.symm)`. Rewrite using `[← contDiffOn_univ]`.

Conclude with `h2.contDiffOn uniqueDiffOn_univ`. Establish `: F = (F ∘ e.symm) ∘ e` using `by ext y; simp`. Rewrite using `[this]`. Conclude with `(h3.comp e.contDiff).contDiffAt`.
-/
theorem contDiffAt_of_diff {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {F : W → ℂ} (hF : Differentiable ℂ F) (x : W) : ContDiffAt ℂ ω F x := by
  let e : W ≃L[ℂ] (Fin (Module.finrank ℂ W) → ℂ) :=
    (Module.finBasis ℂ W).equivFun.toContinuousLinearEquiv
  have h1 : Differentiable ℂ (F ∘ e.symm) := hF.comp e.symm.differentiable
  have h2 : AnalyticOnNhd ℂ (F ∘ e.symm) Set.univ :=
    ReciprocityTheory.AnForm.Osgood.osgood _ _ _ isOpen_univ h1.differentiableOn
  have h3 : ContDiff ℂ ω (F ∘ e.symm) := by
    rw [← contDiffOn_univ]
    exact h2.contDiffOn uniqueDiffOn_univ
  have : F = (F ∘ e.symm) ∘ e := by ext y; simp
  rw [this]
  exact (h3.comp e.contDiff).contDiffAt

end Deriv

section Pi

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `h` using `X.eps_add 0 (zero_mem _) 0 (zero_mem _)`. Simplify using `only [add_zero] at h`. Break down `X.eps_pm 0 (zero_mem _) with h1 | h1` into its components or cases. Conclude with `h1`. Rewrite `h` using `[h1]`.

Evaluate the numerical expressions using `[Hf] at h`.
-/
theorem eps_zero (X : PT E) : X.eps 0 = 1 := by
  have h := X.eps_add 0 (zero_mem _) 0 (zero_mem _)
  simp only [add_zero] at h
  rcases X.eps_pm 0 (zero_mem _) with h1 | h1
  · exact h1
  · rw [h1] at h
    norm_num [Hf] at h

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp [eps_zero]`. Consider the case `succ k ih`. Establish `hkx : (k : ℂ) • x ∈ X.L`. Rewrite using `[Nat.cast_smul_eq_nsmul]`.

Conclude with `nsmul_mem hx k`. Establish `h` using `X.eps_add _ hkx x hx`. Establish `him : (Hf ((k : ℂ) • x) x).im = 0`. Unfold `Hf`. Rewrite using `[Complex.im_sum]`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Simplify using `[PiLp.smul_apply, mul_assoc, Complex.mul_conj]`. Rewrite using `[show ((k + 1 : ℕ) : ℂ) • x = (k : ℂ) • x + x by push_cast; rw [add_smul, one_smul], h, ih, him]`. Simplify using `[pow_succ]`.
-/
theorem eps_natSmul (X : PT E) {x : Vsp X.dim} (hx : x ∈ X.L) (k : ℕ) :
    (X.eps ((k : ℂ) • x) : ℝ) = (X.eps x : ℝ) ^ k := by
  induction k with
  | zero => simp [eps_zero]
  | succ k ih =>
    have hkx : (k : ℂ) • x ∈ X.L := by
      rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hx k
    have h := X.eps_add _ hkx x hx
    have him : (Hf ((k : ℂ) • x) x).im = 0 := by
      unfold Hf
      rw [Complex.im_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [PiLp.smul_apply, mul_assoc, Complex.mul_conj]
    rw [show ((k + 1 : ℕ) : ℂ) • x = (k : ℂ) • x + x by push_cast; rw [add_smul, one_smul], h, ih, him]
    simp [pow_succ]

/- English proof (translation)
Use `⟨fun α v => ?_, fun x hx => ?_, fun v w => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply]`. Use extensionality with `i`. Simplify using `[act]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply]`. Rewrite using `[Nat.cast_smul_eq_nsmul]`. Conclude with `nsmul_mem hx M`. Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply]`. Unfold `Hf`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply]`.

Establish `h` using `eps_natSmul X hx M`. Establish `h2 : (X.eps x : ℝ) ^ M = (X.eps x : ℝ) ^ (M ^ 2)`. Break down `X.eps_pm x hx with h1 | h1` into its components or cases. Simplify using `[h1]`. Rewrite using `[h1]`.

Use `push_cast`. Rewrite using `[sq, pow_mul]`. Apply the tactic sequence `rcases neg_one_pow_eq_or ℝ M with h3 | h3 <;> simp [h3]`. Conclude with `h.trans h2` after adjusting the coercions.
-/
theorem isPi_nat (X : PT E) (M : ℕ) : IsPi X (M ^ 2) ((M : ℂ) • LinearMap.id) := by
  refine ⟨fun α v => ?_, fun x hx => ?_, fun v w => ?_, fun x hx => ?_⟩
  · simp only [LinearMap.smul_apply, LinearMap.id_apply]
    ext i
    simp [act]
    ring
  · simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hx M
  · simp only [LinearMap.smul_apply, LinearMap.id_apply]
    unfold Hf
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
    ring
  · simp only [LinearMap.smul_apply, LinearMap.id_apply]
    have h := eps_natSmul X hx M
    have h2 : (X.eps x : ℝ) ^ M = (X.eps x : ℝ) ^ (M ^ 2) := by
      rcases X.eps_pm x hx with h1 | h1
      · simp [h1]
      · rw [h1]
        push_cast
        rw [sq, pow_mul]
        rcases neg_one_pow_eq_or ℝ M with h3 | h3 <;> simp [h3]
    exact_mod_cast h.trans h2

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Establish `h0 : n = 0` using `by omega`. Substitute `h0` using the available equality. Establish `: DF bs = 0`. Unfold `DF`.

Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Establish `: (bs j).i = 0`. Assume the negation of the conclusion as `hi`. Conclude with `Fin.elim0 ((bs j).col ⟨0, by omega⟩)`. Simplify using `[this]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem one_le_n_of_DF {n nb : ℕ} {dim : (E →+* ℂ) → ℕ} (bs : Fin nb → Block E n dim) (h : 1 ≤ DF bs) :
    1 ≤ n := by
  by_contra hn
  have h0 : n = 0 := by omega
  subst h0
  have : DF bs = 0 := by
    unfold DF
    refine Finset.sum_eq_zero fun j _ => ?_
    have : (bs j).i = 0 := by
      by_contra hi
      exact Fin.elim0 ((bs j).col ⟨0, by omega⟩)
    simp [this]
  omega

end Pi

section Log

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Unfold `dstar`. Establish `h1` using `P.hfr`. Establish `h2` using `P.hm1`. Establish `hf : 0 < PT.f E`. Break down `Nat.eq_zero_or_pos (PT.f E) with h | h` into its components or cases.

Rewrite `h1` using `[h]`. Simplify using `at h1`. Conclude with `h`. Conclude with `Nat.mul_pos (Nat.mul_pos two_pos hf) h2`.
-/
theorem dstar_pos (X : PT E) {dg : ℕ} (P : Par X dg) : 0 < dstar (E := E) P.m := by
  unfold dstar
  have h1 := P.hfr
  have h2 := P.hm1
  have hf : 0 < PT.f E := by
    rcases Nat.eq_zero_or_pos (PT.f E) with h | h
    · rw [h] at h1; simp at h1
    · exact h
  exact Nat.mul_pos (Nat.mul_pos two_pos hf) h2

/- English proof (translation)
Establish `hd0 : (0 : ℝ) < (dstar (E` using `E) P.m : ℝ) := by exact_mod_cast dstar_pos X P`. Establish `hd : (0 : ℝ) < 2 * (dstar (E` using `E) P.m : ℝ) := by linarith`. Establish `hB` using `Real.rpow_pos_of_pos hd ((dstar (E := E) P.m : ℝ) / 2)`. Establish `h6 : (0 : ℝ) < 6 * (2 * (dstar (E` using `E) P.m : ℝ)) ^ ((dstar (E := E) P.m : ℝ) / 2) := mul_pos (by norm_num) hB`. Unfold `Par.Jbound`.

Conclude with `mul_pos (mul_pos (mul_pos (pow_pos (by norm_num) _) (pow_pos (inv_pos.2 h6) _)) (pow_pos (by norm_num) _)) (Real.exp_pos _)`.
-/
theorem jbound_pos (X : PT E) {dg : ℕ} (P : Par X dg) (n : ℕ) : 0 < P.Jbound n := by
  have hd0 : (0 : ℝ) < (dstar (E := E) P.m : ℝ) := by exact_mod_cast dstar_pos X P
  have hd : (0 : ℝ) < 2 * (dstar (E := E) P.m : ℝ) := by linarith
  have hB := Real.rpow_pos_of_pos hd ((dstar (E := E) P.m : ℝ) / 2)
  have h6 : (0 : ℝ) < 6 * (2 * (dstar (E := E) P.m : ℝ)) ^ ((dstar (E := E) P.m : ℝ) / 2) :=
    mul_pos (by norm_num) hB
  unfold Par.Jbound
  exact mul_pos (mul_pos (mul_pos (pow_pos (by norm_num) _) (pow_pos (inv_pos.2 h6) _))
    (pow_pos (by norm_num) _)) (Real.exp_pos _)

/- English proof (translation)
Establish `hd0 : (1 : ℝ) ≤ (dstar (E` using `E) P.m : ℝ) := by exact_mod_cast dstar_pos X P`. Establish `hd : (0 : ℝ) < 2 * (dstar (E` using `E) P.m : ℝ) := by linarith`. Establish `hB` using `Real.rpow_pos_of_pos hd ((dstar (E := E) P.m : ℝ) / 2)`. Establish `h6 : (0 : ℝ) < 6 * (2 * (dstar (E` using `E) P.m : ℝ)) ^ ((dstar (E := E) P.m : ℝ) / 2) := mul_pos (by norm_num) hB`. Establish `hq1 : (1 : ℝ) ≤ P.q` using `by exact_mod_cast P.hq`.

Establish `hqpos : (0 : ℝ) < P.q` using `by linarith`. Establish `hlogM : Real.log M = Real.log P.q / 2`. Rewrite using `[hq]`. Use `push_cast`. Rewrite using `[Real.log_pow]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hph : 0 ≤ P.ph`. Unfold `Par.ph PT.ph`. Apply the tactic sequence `split_ifs <;> positivity`. Establish `hA : (4 : ℝ)⁻¹ ^ n ≠ 0` using `by positivity`.

Establish `hBn : (6 * (2 * (dstar (E` using `E) P.m : ℝ)) ^ ((dstar (E := E) P.m : ℝ) / 2))⁻¹ ^ n ≠ 0 := pow_ne_zero _ (inv_ne_zero h6.ne')`. Establish `hC : (2 : ℝ)⁻¹ ^ ((X.r + 2) * dg) ≠ 0` using `by positivity`. Establish `hJ : Real.log (P.Jbound n) = -(n * Real.log 4) - n * (Real.log 6 + (dstar (E` using `E) P.m : ℝ) / 2 * Real.log (2 * (dstar (E := E) P.m : ℝ))) - (((X.r + 2) * dg : ℕ) : ℝ) * Real.log 2 - 2 * Real.pi * n * Cchi (E := E) P.m * P.ph / P.q := by`. Unfold `Par.Jbound`. Rewrite using `[Real.log_mul (mul_ne_zero (mul_ne_zero hA hBn) hC) (Real.exp_pos _).ne', Real.log_mul (mul_ne_zero hA hBn) hC, Real.log_mul hA hBn, Real.log_exp, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_inv, Real.log_inv, Real.log_inv, Real.log_mul (by norm_num) hB.ne', Real.log_rpow …`.

Expand and normalize the polynomial expressions, which then agree. Establish `hdg : (1 : ℝ) ≤ dg` using `by exact_mod_cast P.hDF`. Establish `hlogq : 0 ≤ Real.log P.q` using `Real.log_nonneg hq1`. Establish `hfr : (2 : ℝ) ≤ (PT.f E : ℝ) * X.r` using `by exact_mod_cast P.hfr`. Establish `hn1 : (1 : ℝ) ≤ n` using `by exact_mod_cast hn`.

Establish `hfrn : (1 : ℝ) ≤ (PT.f E : ℝ) * X.r * n`. Use `mul_le_mul hfr hn1 (by norm_num) (by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h24 : Real.log 24 = Real.log 4 + Real.log 6`. Rewrite using `[← Real.log_mul (by norm_num) (by norm_num)]; norm_num`.

Establish `hl2d : 0 ≤ Real.log (2 * (dstar (E` using `E) P.m : ℝ)) := Real.log_nonneg (by linarith)`. Establish `hT : 0 ≤ Real.log 24 + (dstar (E` using `E) P.m : ℝ) / 2 * Real.log (2 * (dstar (E := E) P.m : ℝ)) := by`. Establish `: 0 < Real.log 24` using `Real.log_pos (by norm_num)`. Establish `: 0 ≤ (dstar (E` using `E) P.m : ℝ) / 2 * Real.log (2 * (dstar (E := E) P.m : ℝ)) := by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hRR : 0 ≤ RR (E` using `E) := by`. Unfold `RR`. Use `P.hrd` as an intermediate fact. Conclude with `pow_nonneg (by linarith) 7`. Establish `hPP0 : 0 ≤ PP` using `le_trans (by positivity) hPP`.

Establish `hdg2 : (1 : ℝ) ≤ (dg : ℝ) ^ 2` using `one_le_pow₀ hdg`. Establish `hk : 2 * Real.pi * n * Cchi (E` using `E) P.m ≤ 2 * (RR (E := E) * PP * (dg : ℝ) ^ 2) := by`. Unfold `Cchi`. Establish `e1 : 2 * Real.pi * n * (8100 * (P.m : ℝ) ^ 4 * (dstar (E` using `E) P.m : ℝ) ^ 4 * RR (E := E)) = RR (E := E) * (16200 * Real.pi * n * (P.m : ℝ) ^ 4 * (dstar (E := E) P.m : ℝ) ^ 4) := by ring`. Rewrite using `[e1]`.

Establish `e2` using `mul_le_mul_of_nonneg_left hPP hRR`. Establish `e3 : 0 ≤ RR (E` using `E) * PP := mul_nonneg hRR hPP0`. Establish `e4` using `mul_nonneg e3 (by linarith : (0 : ℝ) ≤ 2 * (dg : ℝ) ^ 2 - 1)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e3 : 2 * Real.pi * n * Cchi (E` using `E) P.m * P.ph / P.q ≤ 2 * (RR (E := E) * PP * (dg : ℝ) ^ 2 / P.q * P.ph) := by`.

Rewrite using `[show 2 * (RR (E := E) * PP * (dg : ℝ) ^ 2 / P.q * P.ph) = 2 * (RR (E := E) * PP * (dg : ℝ) ^ 2) * P.ph / P.q by ring]`. Conclude with `div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hk hph) hqpos.le`. Establish `e1 : (dg : ℝ) * (Real.log P.q / 2) ≤ (1 / 2) * ((PT.f E : ℝ) * X.r * n * Real.log P.q) * dg`. Use `mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ dg) hlogq) (sub_nonneg.2 hfrn)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `e2 : (1 / 2 : ℝ) * n * (Real.log 24 + (dstar (E` using `E) P.m : ℝ) / 2 * Real.log (2 * (dstar (E := E) P.m : ℝ))) ≤ (1 / 2) * (n * (Real.log 24 + (dstar (E := E) P.m : ℝ) / 2 * Real.log (2 * (dstar (E := E) P.m : ℝ)))) * dg := by`. Use `mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ n) hT) (sub_nonneg.2 hdg)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e4` using `mul_le_mul_of_nonneg_right hP14 (by linarith : (0 : ℝ) ≤ dg)`. Rewrite using `[hJ, hlogM, hcc]`.

Use `push_cast`. Rewrite `e2`, `e4` using `[h24]`. Combine the linear relations using `[e1, e2, e3, e4]`.
-/
theorem log_bound (X : PT E) {dg : ℕ} (P : Par X dg) (n : ℕ) (hn : 1 ≤ n) (M : ℕ) (hq : P.q = M ^ 2)
    (tableLineDegreeFive cc PP : ℝ)
    (hP14 : (1 / 2 : ℝ) * ((PT.f E : ℝ) * X.r * n * Real.log P.q +
      n * (Real.log 24 + (dstar (E := E) P.m : ℝ) / 2 * Real.log (2 * (dstar (E := E) P.m : ℝ))) +
      (X.r + 2) * Real.log 2) ≤ tableLineDegreeFive)
    (hPP : 16200 * Real.pi * n * (P.m : ℝ) ^ 4 * (dstar (E := E) P.m : ℝ) ^ 4 ≤ PP)
    (hcc : cc = RR (E := E) * PP * (dg : ℝ) ^ 2 / P.q) :
    dg * Real.log M - Real.log (P.Jbound n) / 2 ≤ tableLineDegreeFive * dg + cc * P.ph := by
  have hd0 : (1 : ℝ) ≤ (dstar (E := E) P.m : ℝ) := by exact_mod_cast dstar_pos X P
  have hd : (0 : ℝ) < 2 * (dstar (E := E) P.m : ℝ) := by linarith
  have hB := Real.rpow_pos_of_pos hd ((dstar (E := E) P.m : ℝ) / 2)
  have h6 : (0 : ℝ) < 6 * (2 * (dstar (E := E) P.m : ℝ)) ^ ((dstar (E := E) P.m : ℝ) / 2) :=
    mul_pos (by norm_num) hB
  have hq1 : (1 : ℝ) ≤ P.q := by exact_mod_cast P.hq
  have hqpos : (0 : ℝ) < P.q := by linarith
  have hlogM : Real.log M = Real.log P.q / 2 := by
    rw [hq]; push_cast; rw [Real.log_pow]; ring
  have hph : 0 ≤ P.ph := by
    unfold Par.ph PT.ph
    split_ifs <;> positivity
  have hA : (4 : ℝ)⁻¹ ^ n ≠ 0 := by positivity
  have hBn : (6 * (2 * (dstar (E := E) P.m : ℝ)) ^ ((dstar (E := E) P.m : ℝ) / 2))⁻¹ ^ n ≠ 0 :=
    pow_ne_zero _ (inv_ne_zero h6.ne')
  have hC : (2 : ℝ)⁻¹ ^ ((X.r + 2) * dg) ≠ 0 := by positivity
  have hJ : Real.log (P.Jbound n) = -(n * Real.log 4) -
      n * (Real.log 6 + (dstar (E := E) P.m : ℝ) / 2 * Real.log (2 * (dstar (E := E) P.m : ℝ))) -
      (((X.r + 2) * dg : ℕ) : ℝ) * Real.log 2 - 2 * Real.pi * n * Cchi (E := E) P.m * P.ph / P.q := by
    unfold Par.Jbound
    rw [Real.log_mul (mul_ne_zero (mul_ne_zero hA hBn) hC) (Real.exp_pos _).ne',
      Real.log_mul (mul_ne_zero hA hBn) hC, Real.log_mul hA hBn, Real.log_exp, Real.log_pow,
      Real.log_pow, Real.log_pow, Real.log_inv, Real.log_inv, Real.log_inv,
      Real.log_mul (by norm_num) hB.ne', Real.log_rpow hd]
    ring
  have hdg : (1 : ℝ) ≤ dg := by exact_mod_cast P.hDF
  have hlogq : 0 ≤ Real.log P.q := Real.log_nonneg hq1
  have hfr : (2 : ℝ) ≤ (PT.f E : ℝ) * X.r := by exact_mod_cast P.hfr
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hfrn : (1 : ℝ) ≤ (PT.f E : ℝ) * X.r * n := by
    have := mul_le_mul hfr hn1 (by norm_num) (by linarith)
    linarith
  have h24 : Real.log 24 = Real.log 4 + Real.log 6 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have hl2d : 0 ≤ Real.log (2 * (dstar (E := E) P.m : ℝ)) := Real.log_nonneg (by linarith)
  have hT : 0 ≤ Real.log 24 + (dstar (E := E) P.m : ℝ) / 2 * Real.log (2 * (dstar (E := E) P.m : ℝ)) := by
    have : 0 < Real.log 24 := Real.log_pos (by norm_num)
    have : 0 ≤ (dstar (E := E) P.m : ℝ) / 2 * Real.log (2 * (dstar (E := E) P.m : ℝ)) := by positivity
    linarith
  have hRR : 0 ≤ RR (E := E) := by
    unfold RR
    have := P.hrd
    exact pow_nonneg (by linarith) 7
  have hPP0 : 0 ≤ PP := le_trans (by positivity) hPP
  have hdg2 : (1 : ℝ) ≤ (dg : ℝ) ^ 2 := one_le_pow₀ hdg
  have hk : 2 * Real.pi * n * Cchi (E := E) P.m ≤ 2 * (RR (E := E) * PP * (dg : ℝ) ^ 2) := by
    unfold Cchi
    have e1 : 2 * Real.pi * n * (8100 * (P.m : ℝ) ^ 4 * (dstar (E := E) P.m : ℝ) ^ 4 * RR (E := E)) =
        RR (E := E) * (16200 * Real.pi * n * (P.m : ℝ) ^ 4 * (dstar (E := E) P.m : ℝ) ^ 4) := by ring
    rw [e1]
    have e2 := mul_le_mul_of_nonneg_left hPP hRR
    have e3 : 0 ≤ RR (E := E) * PP := mul_nonneg hRR hPP0
    have e4 := mul_nonneg e3 (by linarith : (0 : ℝ) ≤ 2 * (dg : ℝ) ^ 2 - 1)
    linarith
  have e3 : 2 * Real.pi * n * Cchi (E := E) P.m * P.ph / P.q ≤
      2 * (RR (E := E) * PP * (dg : ℝ) ^ 2 / P.q * P.ph) := by
    rw [show 2 * (RR (E := E) * PP * (dg : ℝ) ^ 2 / P.q * P.ph) =
      2 * (RR (E := E) * PP * (dg : ℝ) ^ 2) * P.ph / P.q by ring]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hk hph) hqpos.le
  have e1 : (dg : ℝ) * (Real.log P.q / 2) ≤ (1 / 2) * ((PT.f E : ℝ) * X.r * n * Real.log P.q) * dg := by
    have := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ dg) hlogq) (sub_nonneg.2 hfrn)
    linarith
  have e2 : (1 / 2 : ℝ) * n * (Real.log 24 + (dstar (E := E) P.m : ℝ) / 2 *
      Real.log (2 * (dstar (E := E) P.m : ℝ))) ≤
      (1 / 2) * (n * (Real.log 24 + (dstar (E := E) P.m : ℝ) / 2 *
        Real.log (2 * (dstar (E := E) P.m : ℝ)))) * dg := by
    have := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ n) hT) (sub_nonneg.2 hdg)
    linarith
  have e4 := mul_le_mul_of_nonneg_right hP14 (by linarith : (0 : ℝ) ≤ dg)
  rw [hJ, hlogM, hcc]
  push_cast
  rw [h24] at e2 e4
  linarith [e1, e2, e3, e4]

end Log

end Formalism.L2.Pj.I2FramePointLemmas
