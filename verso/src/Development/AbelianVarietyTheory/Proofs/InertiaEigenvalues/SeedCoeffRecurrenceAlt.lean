import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscToDiscInjectiveOfAdicBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinAinfDiscIsDomainNormBoundsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineDiscPeriodsFrobeniusEqMulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeFrobeniusInverseMatrixStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section
namespace GlobalTheory.BSP

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

/- English proof (translation)
Unfold `BK.ρ₀`. Conclude with `NNReal.rpow_pos (by exact_mod_cast hl.out.pos)`.
-/
theorem seedRec_ρ₀_pos (bk : BK K) : 0 < bk.ρ₀ := by
  unfold BK.ρ₀
  exact NNReal.rpow_pos (by exact_mod_cast hl.out.pos)

/- English proof (translation)
Unfold `BK.ρ₀`. Apply `NNReal.rpow_lt_one_of_one_lt_of_neg` to reduce the goal to its premises. Conclude with `hl.out.one_lt` after adjusting the coercions. Establish `: (0:ℝ) < bk.Ep.natDegree` using `by exact_mod_cast bk.deg_pos`. Establish `: 0 < 1 / (bk.Ep.natDegree : ℝ)` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem seedRec_ρ₀_lt_one (bk : BK K) : bk.ρ₀ < 1 := by
  unfold BK.ρ₀
  apply NNReal.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast hl.out.one_lt
  · have : (0:ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
    have : 0 < 1 / (bk.Ep.natDegree : ℝ) := by positivity
    linarith

/- English proof (translation)
Rewrite using `[frobS_X]`. Use `(norm_toDisc_pow_le (l := l) (u := (X : bk.S)) l (seedRec_ρ₀_pos bk)).trans ?_` and prove the remaining obligations. Conclude with `pow_le_of_le_one bk.ρ₀.coe_nonneg (by exact_mod_cast (seedRec_ρ₀_lt_one bk).le) hl.out.ne_zero`.
-/
theorem seedRec_frobS_norm (bk : BK K) :
    ‖toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a X)‖ ≤ bk.ρ₀ := by
  rw [frobS_X]
  refine (norm_toDisc_pow_le (l := l) (u := (X : bk.S)) l (seedRec_ρ₀_pos bk)).trans ?_
  exact pow_le_of_le_one bk.ρ₀.coe_nonneg (by exact_mod_cast (seedRec_ρ₀_lt_one bk).le) hl.out.ne_zero

/- English proof (translation)
Establish `h1 : IsDiscMap (bk.ev.comp (frobS l bk.a)) (Φ.comp j)` using `⟨fun a => by simp [hj.ext, hΦ.ext, bk.ev_frob], fun x => (hΦ.norm_le _).trans (hj.norm_le x)⟩`. Establish `h2 : IsDiscMap (bk.ev.comp (frobS l bk.a)) (j.comp ΦS)` using `⟨fun a => by simp [hj.ext, hΦS.ext], fun x => (hj.norm_le _).trans (hΦS.norm_le x)⟩`. Conclude with `RingHom.congr_fun (h1.unique h2) x`.
-/
theorem seedRec_comm (bk : BK K) (j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀) (hj : IsDiscMap bk.ev j)
    (Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (hΦ : IsDiscMap WittVector.frobenius Φ)
    (ΦS : bk.DS bk.ρ₀ →+* bk.DS bk.ρ₀) (hΦS : IsDiscMap (frobS l bk.a) ΦS) (x : bk.DS bk.ρ₀) :
    Φ (j x) = j (ΦS x) := by
  have h1 : IsDiscMap (bk.ev.comp (frobS l bk.a)) (Φ.comp j) :=
    ⟨fun a => by simp [hj.ext, hΦ.ext, bk.ev_frob], fun x => (hΦ.norm_le _).trans (hj.norm_le x)⟩
  have h2 : IsDiscMap (bk.ev.comp (frobS l bk.a)) (j.comp ΦS) :=
    ⟨fun a => by simp [hj.ext, hΦS.ext], fun x => (hj.norm_le _).trans (hΦS.norm_le x)⟩
  exact RingHom.congr_fun (h1.unique h2) x

/- English proof (translation)
Introduce `h`. Use `congrArg (PowerSeries.coeff (l * bk.Ep.natDegree)) h` as an intermediate fact. Simplify using `[frobS, BK.E, Polynomial.coeff_coe, bk.monic.coeff_natDegree] at this`.
-/
theorem seedRec_frobS_E_ne_zero (bk : BK K) : frobS l bk.a bk.E ≠ 0 := by
  intro h
  have := congrArg (PowerSeries.coeff (l * bk.Ep.natDegree)) h
  simp [frobS, BK.E, Polynomial.coeff_coe, bk.monic.coeff_natDegree] at this

/- English proof (translation)
Establish `hb : TB.c TB.i₀ 1 = 1` using `by rw [← TB.b_i₀]; exact TB.c_self _`. Establish `hev : ∀ x, TB.c TB.i₀ (bk.ev x) = x` using `fun x => by simpa [hb] using TB.c_mul TB.i₀ x 1`. Introduce `x y h`. Rewrite using `[← hev x, h, hev]`.
-/
theorem seedRec_ev_injective (bk : BK K) {ι : Type} (TB : TopBasis bk.ev bk.J ι) : Function.Injective bk.ev := by
  have hb : TB.c TB.i₀ 1 = 1 := by rw [← TB.b_i₀]; exact TB.c_self _
  have hev : ∀ x, TB.c TB.i₀ (bk.ev x) = x := fun x => by simpa [hb] using TB.c_mul TB.i₀ x 1
  intro x y h
  rw [← hev x, h, hev]

/- English proof (translation)
Introduce `l _ K bk τ hτ d ρ hρ s ι TB j hj cD hc hcm hsum hnorm Φ hΦ i₁ a b`. Establish `h0` using `seedRec_ρ₀_pos bk`. Establish `h1` using `seedRec_ρ₀_lt_one bk`. Take `⟨hdom, -, -⟩` from `GlobalTheory.T.breuilKisin_ainfDisc_isDomain_norm_bounds l K bk bk.ρ₀ h0 h1`. Set `ΦS` to `Disc.map (l := l) (u := (X : bk.S)) (ρ := bk.ρ₀) (u' := (X : bk.S)) (ρ' := bk.ρ₀) (frobS l bk.a) (seedRec_frobS_norm bk)`.

Establish `hΦS : IsDiscMap (frobS l bk.a) ΦS` using `isDiscMap_map _ _`. Establish `hcomm : ∀ x, Φ (j x) = j (ΦS x)` using `seedRec_comm bk j hj Φ hΦ ΦS hΦS`. Establish `hjS : ∀ t, j (toDisc l (X : bk.S) bk.ρ₀ t) = bk.iS t` using `fun t => hj.ext t`. Establish `hΦA : ∀ x, Φ (bk.iA x) = bk.iA (WittVector.frobenius x)` using `fun x => hΦ.ext x`. Establish `hcont : ∀ i, Continuous (cD i)` using `fun i => AddMonoidHomClass.continuous_of_bound (cD i) 1 (fun y => by rw [one_mul]; exact hnorm i y)`.

Establish `hΦc : Continuous Φ` using `AddMonoidHomClass.continuous_of_bound Φ 1 (fun y => by rw [one_mul]; exact hΦ.norm_le y)`. Establish `hjc : Continuous j` using `AddMonoidHomClass.continuous_of_bound j 1 (fun y => by rw [one_mul]; exact hj.norm_le y)`. Set `c : ι → bk.DA bk.ρ₀` to `fun i => bk.iS (TB.c i₁ (WittVector.frobenius (TB.b i)))`. Set `L : bk.DA bk.ρ₀ →+ bk.DA bk.ρ₀` to `(j : bk.DS bk.ρ₀ →+ bk.DA bk.ρ₀).comp (cD i₁)`. Establish `hLa : ∀ y, L y = j (cD i₁ y)` using `fun y => rfl`.

Establish `hLc : Continuous L` using `hjc.comp (hcont i₁)`. Establish `hL : ∀ t y, L (bk.iS t * y) = bk.iS t * L y`. Introduce `t y`. Rewrite using `[hLa, hLa, ← hjS, hcm, map_mul]`. Establish `key : ∀ y, HasSum (fun i => Φ (j (cD i y)) * c i) (L (Φ y))`.

Introduce `y`. Establish `h` using `((hsum y).map (Φ : bk.DA bk.ρ₀ →+ bk.DA bk.ρ₀) hΦc).map L hLc`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp_apply, AddMonoidHom.coe_coe]`.

Rewrite using `[map_mul Φ, hΦA, hcomm, hLa, hcm, hc, map_mul, hjS]`. Both sides reduce to the same expression. Establish `stepA : HasSum (fun i => Φ ((s.W * (s.W'.map (cD i)).map j) a b) * c i) ((s.W.map Φ * (s.W'.map Φ).map L) a b)`. Simplify using `only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul]`. Use `hasSum_sum fun k _ => ?_` and prove the remaining obligations.

Repeatedly rewrite using `[mul_assoc]`. Conclude with `(key (s.W' k b)).mul_left (Φ (s.W a k))`. Use `haveI := hdom`. Establish `hphi` using `GlobalTheory.T.discPeriods_map_frobenius_eq_mul l K bk τ hτ d ρ hρ s Φ hΦ`. Establish `hwp` using `GlobalTheory.T.crystallineLattice_frobenius_inverse_matrix l K bk τ hτ d ρ hρ s Φ hΦ`.

Establish `hmapL : ∀ (M : Matrix (Fin d) (Fin d) bk.S) (Y : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)), (M.map bk.iS * Y).map L = M.map bk.iS * Y.map L`. Introduce `M Y`. Use extensionality with `k m`. Simplify using `only [Matrix.map_apply, Matrix.mul_apply, map_sum, hL]`. Establish `hμ : (l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N * bk.iS bk.E ^ (2 * s.N) = bk.iS ((l : bk.S) ^ (s.c₁ + s.c₂) * frobS l bk.a bk.E ^ s.N * bk.E ^ (2 * s.N))`.

Simplify using `only [map_mul, map_pow, map_natCast]`. Establish `hBL : (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS * (s.W'.map Φ).map L = ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N * bk.iS bk.E ^ (2 * s.N)) • s.W'.map L`. Rewrite using `[← hmapL, hwp]`. Use extensionality with `k m`. Rewrite using `[Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, smul_eq_mul, hμ, hL]`.

Establish `hWJ : s.W'.map L = (s.W'.map (cD i₁)).map j` using `by ext; rfl`. Establish `heq : ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) • (s.W.map Φ * (s.W'.map Φ).map L) = ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) • (bk.iS bk.E ^ (2 * s.N) • (s.W * (s.W'.map (cD i₁)).map j))` using `by conv_lhs => rw [← Matrix.smul_mul, hphi, Matrix.mul_assoc, hBL, Matrix.mul_smul]`. Rewrite using `[smul_smul, hWJ]`. Establish `hE0 : bk.iS (frobS l bk.a bk.E) ≠ 0`. Introduce `h`.

Apply `seedRec_frobS_E_ne_zero bk` to reduce the goal to its premises. Apply `seedRec_ev_injective bk TB` to reduce the goal to its premises. Rewrite using `[map_zero]`. Apply `(toDisc_injective_of_topBasis l K bk (Ainf l) bk.ev ι TB bk.ρ₀ h0 h1).1` to reduce the goal to its premises. Rewrite using `[map_zero]`.

Conclude with `h`. Establish `hlam : (l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N ≠ 0` using `mul_ne_zero (pow_ne_zero _ (isUnit_l_disc l (bk.ev X) bk.ρ₀).ne_zero) (pow_ne_zero _ hE0)`. Establish `hab` using `congrFun (congrFun heq a) b`. Rewrite `hab` using `[Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]`. Establish `h2` using `mul_left_cancel₀ hlam hab`.

Rewrite `h2` using `[Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[← h2]`. Conclude with `stepA`.
-/
theorem seed_coeff_recurrence : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ (ι : Type) (TB : TopBasis bk.ev bk.J ι) (j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap bk.ev j → ∀ (cD : ι → (bk.DA bk.ρ₀ →+ bk.DS bk.ρ₀)), (∀ i a, cD i (bk.iA a) = toDisc l (X : bk.S) bk.ρ₀ (TB.c i a)) → (∀ i x y, cD i (j x * y) = x * cD i y) → (∀ y, HasSum (fun i => j (cD i y) * bk.iA (TB.b i)) y) → (∀ i y, ‖cD i y‖ ≤ ‖y‖) → ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap WittVector.frobenius Φ → ∀ (i₁ : ι) (a b : Fin d), HasSum (fun i => Φ ((s.W * (s.W'.map (cD i)).map j) a b) * bk.iS (TB.c i₁ (WittVector.frobenius (TB.b i)))) (bk.iS bk.E ^ (2 * s.N) * (s.W * (s.W'.map (cD i₁)).map j) a b) := by
  intro l _ K bk τ hτ d ρ hρ s ι TB j hj cD hc hcm hsum hnorm Φ hΦ i₁ a b
  have h0 := seedRec_ρ₀_pos bk
  have h1 := seedRec_ρ₀_lt_one bk
  obtain ⟨hdom, -, -⟩ := GlobalTheory.T.breuilKisin_ainfDisc_isDomain_norm_bounds l K bk bk.ρ₀ h0 h1
  let ΦS := Disc.map (l := l) (u := (X : bk.S)) (ρ := bk.ρ₀) (u' := (X : bk.S)) (ρ' := bk.ρ₀)
    (frobS l bk.a) (seedRec_frobS_norm bk)
  have hΦS : IsDiscMap (frobS l bk.a) ΦS := isDiscMap_map _ _
  have hcomm : ∀ x, Φ (j x) = j (ΦS x) := seedRec_comm bk j hj Φ hΦ ΦS hΦS
  have hjS : ∀ t, j (toDisc l (X : bk.S) bk.ρ₀ t) = bk.iS t := fun t => hj.ext t
  have hΦA : ∀ x, Φ (bk.iA x) = bk.iA (WittVector.frobenius x) := fun x => hΦ.ext x
  have hcont : ∀ i, Continuous (cD i) := fun i =>
    AddMonoidHomClass.continuous_of_bound (cD i) 1 (fun y => by rw [one_mul]; exact hnorm i y)
  have hΦc : Continuous Φ :=
    AddMonoidHomClass.continuous_of_bound Φ 1 (fun y => by rw [one_mul]; exact hΦ.norm_le y)
  have hjc : Continuous j :=
    AddMonoidHomClass.continuous_of_bound j 1 (fun y => by rw [one_mul]; exact hj.norm_le y)
  let c : ι → bk.DA bk.ρ₀ := fun i => bk.iS (TB.c i₁ (WittVector.frobenius (TB.b i)))
  let L : bk.DA bk.ρ₀ →+ bk.DA bk.ρ₀ := (j : bk.DS bk.ρ₀ →+ bk.DA bk.ρ₀).comp (cD i₁)
  have hLa : ∀ y, L y = j (cD i₁ y) := fun y => rfl
  have hLc : Continuous L := hjc.comp (hcont i₁)
  have hL : ∀ t y, L (bk.iS t * y) = bk.iS t * L y := by
    intro t y
    rw [hLa, hLa, ← hjS, hcm, map_mul]
  have key : ∀ y, HasSum (fun i => Φ (j (cD i y)) * c i) (L (Φ y)) := by
    intro y
    have h := ((hsum y).map (Φ : bk.DA bk.ρ₀ →+ bk.DA bk.ρ₀) hΦc).map L hLc
    convert h using 1
    · funext i
      simp only [Function.comp_apply, AddMonoidHom.coe_coe]
      rw [map_mul Φ, hΦA, hcomm, hLa, hcm, hc, map_mul, hjS]
    · rfl
  have stepA : HasSum (fun i => Φ ((s.W * (s.W'.map (cD i)).map j) a b) * c i)
      ((s.W.map Φ * (s.W'.map Φ).map L) a b) := by
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul]
    refine hasSum_sum fun k _ => ?_
    simp_rw [mul_assoc]
    exact (key (s.W' k b)).mul_left (Φ (s.W a k))
  haveI := hdom
  have hphi := GlobalTheory.T.discPeriods_map_frobenius_eq_mul l K bk τ hτ d ρ hρ s Φ hΦ
  have hwp := GlobalTheory.T.crystallineLattice_frobenius_inverse_matrix l K bk τ hτ d ρ hρ s Φ hΦ
  have hmapL : ∀ (M : Matrix (Fin d) (Fin d) bk.S) (Y : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)),
      (M.map bk.iS * Y).map L = M.map bk.iS * Y.map L := by
    intro M Y
    ext k m
    simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, hL]
  have hμ : (l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N * bk.iS bk.E ^ (2 * s.N) =
      bk.iS ((l : bk.S) ^ (s.c₁ + s.c₂) * frobS l bk.a bk.E ^ s.N * bk.E ^ (2 * s.N)) := by
    simp only [map_mul, map_pow, map_natCast]
  have hBL : (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS *
      (s.W'.map Φ).map L = ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N *
        bk.iS bk.E ^ (2 * s.N)) • s.W'.map L := by
    rw [← hmapL, hwp]
    ext k m
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, smul_eq_mul, hμ, hL]
  have hWJ : s.W'.map L = (s.W'.map (cD i₁)).map j := by ext; rfl
  have heq : ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) •
      (s.W.map Φ * (s.W'.map Φ).map L) = ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) •
      (bk.iS bk.E ^ (2 * s.N) • (s.W * (s.W'.map (cD i₁)).map j)) := by
    conv_lhs => rw [← Matrix.smul_mul, hphi, Matrix.mul_assoc, hBL, Matrix.mul_smul]
    rw [smul_smul, hWJ]
  have hE0 : bk.iS (frobS l bk.a bk.E) ≠ 0 := by
    intro h
    apply seedRec_frobS_E_ne_zero bk
    apply seedRec_ev_injective bk TB
    rw [map_zero]
    apply (toDisc_injective_of_topBasis l K bk (Ainf l) bk.ev ι TB bk.ρ₀ h0 h1).1
    rw [map_zero]
    exact h
  have hlam : (l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (isUnit_l_disc l (bk.ev X) bk.ρ₀).ne_zero) (pow_ne_zero _ hE0)
  have hab := congrFun (congrFun heq a) b
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul] at hab
  have h2 := mul_left_cancel₀ hlam hab
  rw [Matrix.smul_apply, smul_eq_mul] at h2
  rw [← h2]
  exact stepA

end GlobalTheory.BSP
