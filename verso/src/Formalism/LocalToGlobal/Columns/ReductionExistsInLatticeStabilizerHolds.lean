import Formalism.LocalToGlobal.Columns.OcbPhiFIdxFPos
import Formalism.LocalToGlobal.Columns.OcbTIntOfStab

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Rewrite using `[zero_add, pow_one]`. Conclude with `⟨ciIntAt_q, redP_natCast_eq_zero hq⟩`. Consider the case `succ k ih`.

Rewrite using `[pow_succ]`. Conclude with `⟨ih.1.mul ciIntAt_q, by rw [reduction_mul ih.1 ciIntAt_q, ih.2, zero_mul]⟩`.
-/
theorem ocbA_pow_red (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (k : ℕ) :
    IntAt P ((q : E) ^ (k + 1)) ∧ redP P ((q : E) ^ (k + 1)) = 0 := by
  induction k with
  | zero =>
    rw [zero_add, pow_one]
    exact ⟨ciIntAt_q, redP_natCast_eq_zero hq⟩
  | succ k ih =>
    rw [pow_succ]
    exact ⟨ih.1.mul ciIntAt_q, by rw [reduction_mul ih.1 ciIntAt_q, ih.2, zero_mul]⟩

/- English proof (translation)
Establish `hq0 : (q : E) ≠ 0` using `ciQ_ne_zero hu`. Establish `hex : ∃ z : ℤ, IsUnit (redP P (u / (q : E) ^ z))` using `⟨0, by rwa [zpow_zero, div_one]⟩`. Establish `hspec : IsUnit (redP P (u / (q : E) ^ LocE.vP P q u))`. Unfold `LocE.vP`. Conclude with `Classical.epsilon_spec hex`.

Assume the negation of the conclusion as `hne`. Take `⟨k, hk | hk⟩` from `Int.eq_nat_or_neg (LocE.vP P q u)`. Take `⟨k', rfl⟩ : ∃ k', k = k' + 1` from `⟨k - 1, by omega⟩`. Rewrite `hspec` using `[hk, zpow_natCast]`. Distinguish the cases in `hI' : IntAt P (u / (q : E) ^ (k' + 1))`.

Establish `e : u = (q : E) ^ (k' + 1) * (u / (q : E) ^ (k' + 1))` using `by field_simp`. Establish `h0 : redP P u = 0`. Rewrite using `[e, reduction_mul (ocbA_pow_red hq k').1 hI', (ocbA_pow_red hq k').2, zero_mul]`. Rewrite `hU` using `[h0]`. Conclude with `not_isUnit_zero hU`.

Rewrite `hspec` using `[reduction_eq_zero_of_not_integral P hI']`. Conclude with `not_isUnit_zero hspec`. Take `⟨k', rfl⟩ : ∃ k', k = k' + 1` from `⟨k - 1, by omega⟩`. Rewrite `hspec` using `[hk, zpow_neg, zpow_natCast, div_inv_eq_mul, reduction_mul hI (ocbA_pow_red hq k').1, (ocbA_pow_red hq k').2, mul_zero]`. Conclude with `not_isUnit_zero hspec`.
-/
theorem vP_eq_zero_of_isUnit_redP (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {u : E} (hI : IntAt P u)
    (hU : IsUnit (redP P u)) : LocE.vP P q u = 0 := by
  have hq0 : (q : E) ≠ 0 := ciQ_ne_zero hu
  have hex : ∃ z : ℤ, IsUnit (redP P (u / (q : E) ^ z)) := ⟨0, by rwa [zpow_zero, div_one]⟩
  have hspec : IsUnit (redP P (u / (q : E) ^ LocE.vP P q u)) := by
    unfold LocE.vP
    exact Classical.epsilon_spec hex
  by_contra hne
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg (LocE.vP P q u)
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hk, zpow_natCast] at hspec
    by_cases hI' : IntAt P (u / (q : E) ^ (k' + 1))
    · have e : u = (q : E) ^ (k' + 1) * (u / (q : E) ^ (k' + 1)) := by field_simp
      have h0 : redP P u = 0 := by
        rw [e, reduction_mul (ocbA_pow_red hq k').1 hI', (ocbA_pow_red hq k').2, zero_mul]
      rw [h0] at hU
      exact not_isUnit_zero hU
    · rw [reduction_eq_zero_of_not_integral P hI'] at hspec
      exact not_isUnit_zero hspec
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hk, zpow_neg, zpow_natCast, div_inv_eq_mul, reduction_mul hI (ocbA_pow_red hq k').1, (ocbA_pow_red hq k').2,
      mul_zero] at hspec
    exact not_isUnit_zero hspec

/- English proof (translation)
Establish `hinv : h₀.symm ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1))` using `Subgroup.inv_mem _ hh₀`. Set `e : Fin (n + c) → E` to `fun a => (q : E) ^ LocE.scE n (fun i => i + 1) a.1`. Set `B : (Sp E (n + c) →ₗ[E] Sp E (n + c)) → Matrix (Fin (n + c)) (Fin (n + c)) E` to `fun g => Matrix.of fun a b => ocbBEnt n n q g a.1 b.1`. Establish `hB : ∀ g, B g = Matrix.diagonal (fun a => (e a)⁻¹) * LinearMap.toMatrix' g * Matrix.diagonal e`. Introduce `g`.

Use extensionality with `a b`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul, ocbS_atN_toMatrix']`. Simplify using `only [B, e, Matrix.of_apply]`. Unfold `ocbBEnt`. Rewrite using `[zpow_sub₀ hq0]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hP : ∏ a, e a ≠ 0` using `Finset.prod_ne_zero_iff.2 fun a _ => zpow_ne_zero _ hq0`. Establish `hdet : ∀ g, (B g).det = LinearMap.det g`. Introduce `g`. Rewrite using `[hB, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, LinearMap.det_toMatrix', Finset.prod_inv_distrib, mul_comm ((∏ a, e a)⁻¹), mul_assoc, inv_mul_cancel₀ hP, mul_one]`.

Establish `hBB : B h₀.toLinearMap * B h₀.symm.toLinearMap = 1`. Use extensionality with `a b`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Simplify using `only [B, Matrix.of_apply]`. Rewrite using `[← ocbT_bEnt_comp (n' := n) (c' := c) hq0 h₀.toLinearMap h₀.symm.toLinearMap a.2 b.2]`.

Establish `hid : h₀.toLinearMap ∘ₗ h₀.symm.toLinearMap = LinearMap.id` using `LinearMap.ext fun x => h₀.apply_symm_apply x`. Rewrite using `[hid, ocbT_bEnt_id a.2]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl]`.

Rewrite using `[if_neg (fun h => hab (Fin.ext h)), if_neg hab]`. Establish `hI1 : IntAt P (B h₀.toLinearMap).det` using `ciIntAt_det _ fun a b => ocbT_int_of_stab hq0 hh₀ a.2 b.2`. Establish `hI2 : IntAt P (B h₀.symm.toLinearMap).det` using `ciIntAt_det _ fun a b => ocbT_int_of_stab hq0 hinv a.2 b.2`. Establish `hd : (LinearEquiv.det h₀ : E) = (B h₀.toLinearMap).det`. Rewrite using `[LinearEquiv.coe_det, hdet]`.

Rewrite using `[hd]`. Use `⟨hI1, isUnit_iff_exists_inv.2 ⟨redP P (B h₀.symm.toLinearMap).det, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← reduction_mul hI1 hI2, ← Matrix.det_mul, hBB, Matrix.det_one, redP_one]`.
-/
theorem ocbA_det_unit (hq0 : (q : E) ≠ 0) {n c : ℕ} {h₀ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hh₀ : h₀ ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1))) :
    IntAt P (LinearEquiv.det h₀ : E) ∧ IsUnit (redP P (LinearEquiv.det h₀ : E)) := by
  classical
  have hinv : h₀.symm ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1)) := Subgroup.inv_mem _ hh₀
  let e : Fin (n + c) → E := fun a => (q : E) ^ LocE.scE n (fun i => i + 1) a.1
  let B : (Sp E (n + c) →ₗ[E] Sp E (n + c)) → Matrix (Fin (n + c)) (Fin (n + c)) E :=
    fun g => Matrix.of fun a b => ocbBEnt n n q g a.1 b.1
  have hB : ∀ g, B g = Matrix.diagonal (fun a => (e a)⁻¹) * LinearMap.toMatrix' g * Matrix.diagonal e := by
    intro g
    ext a b
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, ocbS_atN_toMatrix']
    simp only [B, e, Matrix.of_apply]
    unfold ocbBEnt
    rw [zpow_sub₀ hq0]
    ring
  have hP : ∏ a, e a ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => zpow_ne_zero _ hq0
  have hdet : ∀ g, (B g).det = LinearMap.det g := by
    intro g
    rw [hB, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, LinearMap.det_toMatrix',
      Finset.prod_inv_distrib, mul_comm ((∏ a, e a)⁻¹), mul_assoc, inv_mul_cancel₀ hP, mul_one]
  have hBB : B h₀.toLinearMap * B h₀.symm.toLinearMap = 1 := by
    ext a b
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [B, Matrix.of_apply]
    rw [← ocbT_bEnt_comp (n' := n) (c' := c) hq0 h₀.toLinearMap h₀.symm.toLinearMap a.2 b.2]
    have hid : h₀.toLinearMap ∘ₗ h₀.symm.toLinearMap = LinearMap.id := LinearMap.ext fun x => h₀.apply_symm_apply x
    rw [hid, ocbT_bEnt_id a.2]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (fun h => hab (Fin.ext h)), if_neg hab]
  have hI1 : IntAt P (B h₀.toLinearMap).det := ciIntAt_det _ fun a b => ocbT_int_of_stab hq0 hh₀ a.2 b.2
  have hI2 : IntAt P (B h₀.symm.toLinearMap).det := ciIntAt_det _ fun a b => ocbT_int_of_stab hq0 hinv a.2 b.2
  have hd : (LinearEquiv.det h₀ : E) = (B h₀.toLinearMap).det := by
    rw [LinearEquiv.coe_det, hdet]
  rw [hd]
  refine ⟨hI1, isUnit_iff_exists_inv.2 ⟨redP P (B h₀.symm.toLinearMap).det, ?_⟩⟩
  rw [← reduction_mul hI1 hI2, ← Matrix.det_mul, hBB, Matrix.det_one, redP_one]

/- English proof (translation)
Unfold `Loc.om`. Rewrite using `[show h.symm.toLinearMap ∘ₗ x ∘ₗ (1 : (Fin a → k) ≃ₗ[k] (Fin a → k)).toLinearMap = h.symm.toLinearMap ∘ₗ x from LinearMap.ext fun _ => rfl]`. Simplify using `only [mul_one]`.
-/
theorem ocbA_om_one {k K : Type} [CommRing k] [Field K] {a b : ℕ} (mu : k → K) (v : k → ℤ) (sq : K)
    (h : (Fin b → k) ≃ₗ[k] (Fin b → k)) (Φ : Loc.SF k K a b) (x : (Fin a → k) →ₗ[k] (Fin b → k)) :
    Loc.om mu v sq 1 h Φ x = Loc.om (a := a) mu v sq 1 h (fun _ => 1) 0 * Φ (h.symm.toLinearMap ∘ₗ x) := by
  unfold Loc.om
  rw [show h.symm.toLinearMap ∘ₗ x ∘ₗ (1 : (Fin a → k) ≃ₗ[k] (Fin a → k)).toLinearMap = h.symm.toLinearMap ∘ₗ x from
    LinearMap.ext fun _ => rfl]
  simp only [mul_one]

/- English proof (translation)
Unfold `Loc.E1`. Simplify using `only [ocbA_om_one mu v sq h Φ]`. Rewrite using `[Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem firstUnfolding_omega_factor {k K : Type} [CommRing k] [Field K] {n' c' n c : ℕ} (mu : k → K) (v : k → ℤ) (sq : K)
    (h : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) (Φ : Loc.SF k K (n' + c') (n + c)) (psi : k → K) (vals : Finset k) (wt : K)
    (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) :
    Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi vals wt (Loc.om mu v sq 1 h Φ) xj =
      Loc.om (a := n' + c') mu v sq 1 h (fun _ => 1) 0 *
        Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi vals wt (fun x => Φ (h.symm.toLinearMap ∘ₗ x)) xj := by
  unfold Loc.E1
  simp only [ocbA_om_one mu v sq h Φ]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

/- English proof (translation)
Establish `hq0 : (q : E) ≠ 0` using `ciQ_ne_zero hu`. Establish `hd` using `ocbA_det_unit hq0 hh₀`. Establish `hd1 : IntAt P (((LinearEquiv.det (1 : (Fin a → E) ≃ₗ[E] (Fin a → E)) : Eˣ) : E)) ∧ IsUnit (redP P (((LinearEquiv.det (1 : (Fin a → E) ≃ₗ[E] (Fin a → E)) : Eˣ) : E)))`. Rewrite using `[map_one, Units.val_one, redP_one]`. Conclude with `⟨ciIntAt_one, isUnit_one⟩`.

Establish `hne : ∀ u : E, IntAt P u → IsUnit (redP P u) → LocE.locChar q cq χ u ≠ 0`. Introduce `u hI hU`. Unfold `LocE.locChar`. Rewrite using `[vP_eq_zero_of_isUnit_redP hq hu hI hU, zpow_zero, zpow_zero, one_mul, div_one]`. Unfold `LocE.unitV`.

Rewrite using `[dif_pos hU]`. Conclude with `Units.ne_zero _`. Unfold `Loc.om`. Rewrite using `[vP_eq_zero_of_isUnit_redP hq hu hd.1 hd.2, vP_eq_zero_of_isUnit_redP hq hu hd1.1 hd1.2]`. Simplify using `only [neg_zero, zero_mul, zpow_zero, mul_one]`.

Conclude with `mul_ne_zero (hne _ hd1.1 hd1.2) (inv_ne_zero (hne _ hd.1 hd.2))`.
-/
theorem ocbA_om_ne {K : Type} [Field K] (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
    (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (sq : K) {a n c : ℕ} {h₀ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hh₀ : h₀ ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1))) :
    Loc.om (a := a) (LocE.locChar q cq χ) (LocE.vP P q) sq 1 h₀ (fun _ => 1) 0 ≠ 0 := by
  have hq0 : (q : E) ≠ 0 := ciQ_ne_zero hu
  have hd := ocbA_det_unit hq0 hh₀
  have hd1 : IntAt P (((LinearEquiv.det (1 : (Fin a → E) ≃ₗ[E] (Fin a → E)) : Eˣ) : E)) ∧
      IsUnit (redP P (((LinearEquiv.det (1 : (Fin a → E) ≃ₗ[E] (Fin a → E)) : Eˣ) : E))) := by
    rw [map_one, Units.val_one, redP_one]
    exact ⟨ciIntAt_one, isUnit_one⟩
  have hne : ∀ u : E, IntAt P u → IsUnit (redP P u) → LocE.locChar q cq χ u ≠ 0 := by
    intro u hI hU
    unfold LocE.locChar
    rw [vP_eq_zero_of_isUnit_redP hq hu hI hU, zpow_zero, zpow_zero, one_mul, div_one]
    unfold LocE.unitV
    rw [dif_pos hU]
    exact Units.ne_zero _
  unfold Loc.om
  rw [vP_eq_zero_of_isUnit_redP hq hu hd.1 hd.2, vP_eq_zero_of_isUnit_redP hq hu hd1.1 hd1.2]
  simp only [neg_zero, zero_mul, zpow_zero, mul_one]
  exact mul_ne_zero (hne _ hd1.1 hd1.2) (inv_ne_zero (hne _ hd.1 hd.2))

/- English proof (translation)
Unfold `Loc.om`. Rewrite using `[show h.symm.toLinearMap ∘ₗ x ∘ₗ (LinearEquiv.refl k (Fin a → k)).toLinearMap = h.symm.toLinearMap ∘ₗ x from LinearMap.ext fun _ => rfl]`. Simplify using the standard rewrite rules.
-/
theorem ocbA_res_om {k L : Type} [CommRing k] [Field L] {a b : ℕ} (h : (Fin b → k) ≃ₗ[k] (Fin b → k)) (Φ : Loc.SF k L a b)
    (x : (Fin a → k) →ₗ[k] (Fin b → k)) :
    Loc.om (fun _ => (1 : L)) (fun _ => (0 : ℤ)) 1 (LinearEquiv.refl k (Fin a → k)) h Φ x = Φ (h.symm.toLinearMap ∘ₗ x) := by
  unfold Loc.om
  rw [show h.symm.toLinearMap ∘ₗ x ∘ₗ (LinearEquiv.refl k (Fin a → k)).toLinearMap = h.symm.toLinearMap ∘ₗ x from
    LinearMap.ext fun _ => rfl]
  simp

/- English proof (translation)
Establish `hinv : h₀.symm ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1))` using `Subgroup.inv_mem _ hh₀`. Set `M : (Sp E (n + c) →ₗ[E] Sp E (n + c)) → Matrix (Fin (n + c)) (Fin (n + c)) (𝓞 E ⧸ P.asIdeal)` to `fun g => Matrix.of fun a b => redP P (ocbBEnt n n q g a.1 b.1)`. Establish `hmul : ∀ g₁ g₂ : Sp E (n + c) ≃ₗ[E] Sp E (n + c), g₁ ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1)) → g₂ ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1)) → M g₁.toLinearMap * M g₂.toLinearMap = M (g₁.toLinearMap ∘ₗ g₂.toLinearMap)`. Introduce `g₁ g₂ h1 h2`. Use extensionality with `a b`.

Simplify using `only [M, Matrix.mul_apply, Matrix.of_apply]`. Rewrite using `[ocbT_bEnt_comp (n' := n) (c' := c) hq0 _ _ a.2 b.2, redP_sum _ _ (fun m _ => (ocbT_int_of_stab hq0 h1 a.2 m.2).mul (ocbT_int_of_stab hq0 h2 m.2 b.2))]`. Conclude with `Finset.sum_congr rfl fun m _ => (reduction_mul (ocbT_int_of_stab hq0 h1 a.2 m.2) (ocbT_int_of_stab hq0 h2 m.2 b.2)).symm`. Establish `hM1 : M LinearMap.id = 1`. Use extensionality with `a b`.

Simplify using `only [M, Matrix.of_apply, Matrix.one_apply]`. Rewrite using `[ocbT_bEnt_id a.2]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl, redP_one]`.

Rewrite using `[if_neg (fun h => hab (Fin.ext h)), if_neg hab, redP_zero]`. Establish `h1 : M h₀.toLinearMap * M h₀.symm.toLinearMap = 1`. Rewrite using `[hmul _ _ hh₀ hinv, ← hM1]`. Use `congr 1`. Conclude with `LinearMap.ext fun x => h₀.apply_symm_apply x`.

Establish `h2 : M h₀.symm.toLinearMap * M h₀.toLinearMap = 1`. Rewrite using `[hmul _ _ hinv hh₀, ← hM1]`. Use `congr 1`. Conclude with `LinearMap.ext fun x => h₀.symm_apply_apply x`. Set `hbar : (Fin (n + c) → 𝓞 E ⧸ P.asIdeal) ≃ₗ[𝓞 E ⧸ P.asIdeal] (Fin (n + c) → 𝓞 E ⧸ P.asIdeal)` to `LinearEquiv.ofLinear (Matrix.toLin' (M h₀.toLinearMap)) (Matrix.toLin' (M h₀.symm.toLinearMap)) (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])`.

Use `⟨hbar, fun l s hl hs => ⟨ocbT_int_of_stab hq0 hh₀ hl hs, ?_⟩⟩` and prove the remaining obligations. Use `show Loc.atN (Matrix.toLin' (M h₀.toLinearMap) (Loc.eN _ (n + c) s)) l = _`. Rewrite using `[ocbS_atN_toLin' _ hl hs]`. Both sides reduce to the same expression.
-/
theorem ocbA_red_exists (hq0 : (q : E) ≠ 0) {n c : ℕ} {h₀ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hh₀ : h₀ ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1))) : ∃ hbar, ocbIsRed P q n c h₀ hbar := by
  classical
  have hinv : h₀.symm ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1)) := Subgroup.inv_mem _ hh₀
  let M : (Sp E (n + c) →ₗ[E] Sp E (n + c)) → Matrix (Fin (n + c)) (Fin (n + c)) (𝓞 E ⧸ P.asIdeal) :=
    fun g => Matrix.of fun a b => redP P (ocbBEnt n n q g a.1 b.1)
  have hmul : ∀ g₁ g₂ : Sp E (n + c) ≃ₗ[E] Sp E (n + c), g₁ ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1)) →
      g₂ ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1)) →
      M g₁.toLinearMap * M g₂.toLinearMap = M (g₁.toLinearMap ∘ₗ g₂.toLinearMap) := by
    intro g₁ g₂ h1 h2
    ext a b
    simp only [M, Matrix.mul_apply, Matrix.of_apply]
    rw [ocbT_bEnt_comp (n' := n) (c' := c) hq0 _ _ a.2 b.2,
      redP_sum _ _ (fun m _ => (ocbT_int_of_stab hq0 h1 a.2 m.2).mul (ocbT_int_of_stab hq0 h2 m.2 b.2))]
    exact Finset.sum_congr rfl fun m _ => (reduction_mul (ocbT_int_of_stab hq0 h1 a.2 m.2) (ocbT_int_of_stab hq0 h2 m.2 b.2)).symm
  have hM1 : M LinearMap.id = 1 := by
    ext a b
    simp only [M, Matrix.of_apply, Matrix.one_apply]
    rw [ocbT_bEnt_id a.2]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, if_pos rfl, redP_one]
    · rw [if_neg (fun h => hab (Fin.ext h)), if_neg hab, redP_zero]
  have h1 : M h₀.toLinearMap * M h₀.symm.toLinearMap = 1 := by
    rw [hmul _ _ hh₀ hinv, ← hM1]
    congr 1
    exact LinearMap.ext fun x => h₀.apply_symm_apply x
  have h2 : M h₀.symm.toLinearMap * M h₀.toLinearMap = 1 := by
    rw [hmul _ _ hinv hh₀, ← hM1]
    congr 1
    exact LinearMap.ext fun x => h₀.symm_apply_apply x
  let hbar : (Fin (n + c) → 𝓞 E ⧸ P.asIdeal) ≃ₗ[𝓞 E ⧸ P.asIdeal] (Fin (n + c) → 𝓞 E ⧸ P.asIdeal) :=
    LinearEquiv.ofLinear (Matrix.toLin' (M h₀.toLinearMap)) (Matrix.toLin' (M h₀.symm.toLinearMap))
      (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])
  refine ⟨hbar, fun l s hl hs => ⟨ocbT_int_of_stab hq0 hh₀ hl hs, ?_⟩⟩
  show Loc.atN (Matrix.toLin' (M h₀.toLinearMap) (Loc.eN _ (n + c) s)) l = _
  rw [ocbS_atN_toLin' _ hl hs]
  rfl

end Gen

section Glob

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

/- English proof (translation)
Introduce `hB i hi P hP h₀ hh₀`. Establish `hq : ((qOf P.1 : ℕ) : 𝓞 X.E) ∈ P.1.asIdeal` using `ciQ_mem P.1`. Establish `hu` using `ciQ_notMem_sq hB.hX hB.hPr hP`. Establish `hp` using `ciQOf_prime hB.hPr hP`. Establish `hcard` using `ciCard P.1`.

Establish `hq0 : (qOf P.1 : X.E) ≠ 0` using `ciQ_ne_zero hu`. Establish `hlam : lamYat (Pr` using `Pr) (R := R) (i + 1) P.1 = LocE.lamY P.1 (qOf P.1) (R.N (i + 1)) (cOf R (i + 1)) (fun i => i + 1) := by`. Unfold `lamYat`. Rewrite using `[if_pos hP]`. Rewrite `hh₀` using `[hlam]`.

Use `⟨ocbA_red_exists hq0 hh₀, fun hbar hred₀ => ?_⟩` and prove the remaining obligations. Establish `hr` using `ocbRanks_step (R := R) hB.hm hi`. Establish `hc' : cOf R i = cOf R (i + 1) + 1`. Unfold `cOf`. Use `hB.hm` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hPhi : PhiAt Ch mu cst.sharp i P.1 = LocE.PhiGS (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k (R.m / 2 - 1) (R.k + R.m - 1) R.t (i + 1) (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1))`. Unfold `PhiAt`. Rewrite using `[if_pos hP, hB.sharp]`. Both sides reduce to the same expression.

Set `Φ : Loc.SF X.E X.K (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))` to `LocE.PhiGS (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k (R.m / 2 - 1) (R.k + R.m - 1) R.t (i + 1) (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1))`. Set `Φr` to `@ocbPhiS (𝓞 X.E ⧸ P.1.asIdeal) (resField P.1) (ocbPsiC Ch σ P.1) (ocbChiC Ch σ P.1) R.k R.m R.t (i + 1) (R.N i) (cOf R (i + 1)) (R.N (i + 1))`. Take `⟨htsupp, htred⟩` from `ocbT_trans hq0 σ hc' hh₀ hred₀ Φ Φr (fun y hy => ocbPhiGS_supp (psi0P Ch P.1) (chiP Ch P.1) hr hc' y hy) (fun y ybar hint hrd => ocbPhiGS_red hq hu σ (psi0P Ch P.1) (chiP Ch P.1) hr hc' y ybar hint hrd)`. Set `Ψ : Loc.SF X.E X.K (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))` to `fun x => Φ (h₀.symm.toLinearMap ∘ₗ x)`. Set `Ψr` to `Loc.om (fun _ => (1 : ℂ)) (fun _ => (0 : ℤ)) 1 (LinearEquiv.refl (𝓞 X.E ⧸ P.1.asIdeal) _) hbar Φr`.

Establish `hΨr : ∀ y ybar, (∀ l s, l < R.N (i + 1) + cOf R (i + 1) → s < R.N i + cOf R i → IntAt P.1 (ocbBEnt (R.N i) (R.N (i + 1)) (qOf P.1) y l s)) → (∀ l s, l < R.N (i + 1) + cOf R (i + 1) → s < R.N i + cOf R i → Loc.atN (ybar (Loc.eN _ _ s)) l = redP P.1 (ocbBEnt (R.N i) (R.N (i + 1)) ( …`. Introduce `y ybar hint hrd`. Conclude with `(htred y ybar hint hrd).trans (ocbA_res_om hbar Φr ybar).symm`. Establish `hpsi : ∀ a, IntAt P.1 a → σ (cst.psi P (a / (qOf P.1 : X.E))) = (fun u => ocbPsiC Ch σ P.1 u) (redP P.1 a)`. Introduce `a ha`.

Rewrite using `[hB.psi0 P a hP ha]`. Both sides reduce to the same expression. Establish `hE1 : ∀ A' B' xj, E1at Ch sel mu { cst with A` using `A', B := B' } i P 1 h₀ xj = Loc.om (muAt Ch sel mu cst i P) (LocE.vP P.1 (qOf P.1)) (cst.sq P) (1 : AutY X R i) h₀ (fun _ => (1 : X.K)) 0 * Loc.E1 (cst.psi P) (LocE.valsQ X.E (qOf P.1) A' B') (((qOf P.1 : X.K) ^ B')⁻¹) Ψ xj := by`. Introduce `A' B' xj`. Unfold `E1at omPhi`.

Rewrite using `[firstUnfolding_omega_factor, show PhiAt Ch mu ({ cst with A := A', B := B' } : LocCst X (rowSG Pr sel mu)).sharp i P.1 = Φ from hPhi]`. Both sides reduce to the same expression. Establish `hC : Loc.om (muAt Ch sel mu cst i P) (LocE.vP P.1 (qOf P.1)) (cst.sq P) (1 : AutY X R i) h₀ (fun _ => (1 : X.K)) 0 ≠ 0`. Unfold `muAt`. Conclude with `ocbA_om_ne hq hu _ _ _ hh₀`.

Unfold `FiniteSumNonzeroLargeDepth ocbNeAt ocbNe`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨A₀, B₀, hAB⟩`. Establish `h1` using `hAB (max A₀ (cOf R (i + 1) + 1)) (max B₀ 1) (le_max_left _ _) (le_max_left _ _)`. Take `⟨xj, hxj⟩` from `Function.ne_iff.1 h1`.

Rewrite `hxj` using `[Pi.zero_apply, hE1]`. Establish `hE` using `right_ne_zero_of_mul hxj`. Establish `hxI : ocbXInt P.1 xj`. Assume the negation of the conclusion as `hn`. Conclude with `hE (firstUnfolding_eq_zero_of_not_integral hc' Ψ htsupp _ _ _ xj hn)`.

Set `xbj : (Fin (R.N i) → 𝓞 X.E ⧸ P.1.asIdeal) →ₗ[𝓞 X.E ⧸ P.1.asIdeal] (Fin (R.N (i + 1)) → 𝓞 X.E ⧸ P.1.asIdeal)` to `Matrix.toLin' (Matrix.of fun l s => redP P.1 (Loc.atN (xj (Loc.eN X.E (R.N i) s.1)) l.1))`. Establish `hxR : ocbXRed P.1 xj xbj`. Introduce `l s hl hs`. Use `show Loc.atN (Matrix.toLin' _ (Loc.eN _ (R.N i) s)) l = _`. Rewrite using `[ocbS_atN_toLin' _ hl hs]`.

Both sides reduce to the same expression. Establish `heq` using `firstUnfolding_reduction_eq hq hu hp hcard hc' σ Ψ Ψr htsupp hΨr (cst.psi P) (fun u => ocbPsiC Ch σ P.1 u) hpsi (le_max_right A₀ (cOf R (i + 1) + 1)) (le_max_right B₀ 1) xj xbj hxI hxR`. Use `⟨xbj, fun h0 => hE (σ.injective ?_)⟩` and prove the remaining obligations. Rewrite using `[heq, map_zero]`. Conclude with `mul_eq_zero_of_right _ h0`.

Introduce and unpack `⟨xbj, hne⟩`. Use `⟨cOf R (i + 1) + 1, 1, fun A' B' hA hB' hzero => ?_⟩` and prove the remaining obligations. Set `xj : (Fin (R.N i) → X.E) →ₗ[X.E] (Fin (R.N (i + 1)) → X.E)` to `Matrix.toLin' (Matrix.of fun l s => algebraMap (𝓞 X.E) X.E (ciLift P.1 (Loc.atN (xbj (Loc.eN _ (R.N i) s.1)) l.1)))`. Establish `hxI : ocbXInt P.1 xj`. Introduce `l s hl hs`.

Use `show IntAt P.1 (Loc.atN (Matrix.toLin' _ (Loc.eN X.E (R.N i) s)) l)`. Rewrite using `[ocbS_atN_toLin' _ hl hs]`. Conclude with `IntAt.coe P.1 _`. Establish `hxR : ocbXRed P.1 xj xbj`. Introduce `l s hl hs`.

Use `show _ = redP P.1 (Loc.atN (Matrix.toLin' _ (Loc.eN X.E (R.N i) s)) l)`. Rewrite using `[ocbS_atN_toLin' _ hl hs, Matrix.of_apply, reduction_coe, ciLift_mk]`. Establish `heq` using `firstUnfolding_reduction_eq hq hu hp hcard hc' σ Ψ Ψr htsupp hΨr (cst.psi P) (fun u => ocbPsiC Ch σ P.1 u) hpsi hA hB' xj xbj hxI hxR`. Establish `h1` using `congrFun hzero xj`. Rewrite `h1` using `[hE1, Pi.zero_apply]`.

Establish `h2` using `(mul_eq_zero.1 h1).resolve_left hC`. Rewrite `heq` using `[h2, map_zero]`. Conclude with `hne ((mul_eq_zero.1 heq.symm).resolve_left (pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)))`.
-/
theorem reductionExistsInLatticeStabilizer_holds (σ : X.K →+* ℂ) (m2 : ℕ) : ReductionExistsInLatticeStabilizer Ch sel mu cst σ m2 := by
  intro hB i hi P hP h₀ hh₀
  classical
  have hq : ((qOf P.1 : ℕ) : 𝓞 X.E) ∈ P.1.asIdeal := ciQ_mem P.1
  have hu := ciQ_notMem_sq hB.hX hB.hPr hP
  have hp := ciQOf_prime hB.hPr hP
  have hcard := ciCard P.1
  have hq0 : (qOf P.1 : X.E) ≠ 0 := ciQ_ne_zero hu
  have hlam : lamYat (Pr := Pr) (R := R) (i + 1) P.1 =
      LocE.lamY P.1 (qOf P.1) (R.N (i + 1)) (cOf R (i + 1)) (fun i => i + 1) := by
    unfold lamYat
    rw [if_pos hP]
  rw [hlam] at hh₀
  refine ⟨ocbA_red_exists hq0 hh₀, fun hbar hred₀ => ?_⟩
  have hr := ocbRanks_step (R := R) hB.hm hi
  have hc' : cOf R i = cOf R (i + 1) + 1 := by
    unfold cOf
    have := hB.hm
    omega
  have hPhi : PhiAt Ch mu cst.sharp i P.1 = LocE.PhiGS (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k (R.m / 2 - 1)
      (R.k + R.m - 1) R.t (i + 1) (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1)) := by
    unfold PhiAt
    rw [if_pos hP, hB.sharp]
    rfl
  let Φ : Loc.SF X.E X.K (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1)) :=
    LocE.PhiGS (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k (R.m / 2 - 1) (R.k + R.m - 1) R.t (i + 1) (cOf R i) (R.N i)
      (cOf R (i + 1)) (R.N (i + 1))
  let Φr := @ocbPhiS (𝓞 X.E ⧸ P.1.asIdeal) (resField P.1) (ocbPsiC Ch σ P.1) (ocbChiC Ch σ P.1) R.k R.m R.t (i + 1) (R.N i)
    (cOf R (i + 1)) (R.N (i + 1))
  obtain ⟨htsupp, htred⟩ := ocbT_trans hq0 σ hc' hh₀ hred₀ Φ Φr
    (fun y hy => ocbPhiGS_supp (psi0P Ch P.1) (chiP Ch P.1) hr hc' y hy)
    (fun y ybar hint hrd => ocbPhiGS_red hq hu σ (psi0P Ch P.1) (chiP Ch P.1) hr hc' y ybar hint hrd)
  let Ψ : Loc.SF X.E X.K (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1)) := fun x => Φ (h₀.symm.toLinearMap ∘ₗ x)
  let Ψr := Loc.om (fun _ => (1 : ℂ)) (fun _ => (0 : ℤ)) 1 (LinearEquiv.refl (𝓞 X.E ⧸ P.1.asIdeal) _) hbar Φr
  have hΨr : ∀ y ybar, (∀ l s, l < R.N (i + 1) + cOf R (i + 1) → s < R.N i + cOf R i →
      IntAt P.1 (ocbBEnt (R.N i) (R.N (i + 1)) (qOf P.1) y l s)) →
      (∀ l s, l < R.N (i + 1) + cOf R (i + 1) → s < R.N i + cOf R i →
        Loc.atN (ybar (Loc.eN _ _ s)) l = redP P.1 (ocbBEnt (R.N i) (R.N (i + 1)) (qOf P.1) y l s)) → σ (Ψ y) = Ψr ybar := by
    intro y ybar hint hrd
    exact (htred y ybar hint hrd).trans (ocbA_res_om hbar Φr ybar).symm
  have hpsi : ∀ a, IntAt P.1 a → σ (cst.psi P (a / (qOf P.1 : X.E))) = (fun u => ocbPsiC Ch σ P.1 u) (redP P.1 a) := by
    intro a ha
    rw [hB.psi0 P a hP ha]
    rfl
  have hE1 : ∀ A' B' xj, E1at Ch sel mu { cst with A := A', B := B' } i P 1 h₀ xj =
      Loc.om (muAt Ch sel mu cst i P) (LocE.vP P.1 (qOf P.1)) (cst.sq P) (1 : AutY X R i) h₀ (fun _ => (1 : X.K)) 0 *
        Loc.E1 (cst.psi P) (LocE.valsQ X.E (qOf P.1) A' B') (((qOf P.1 : X.K) ^ B')⁻¹) Ψ xj := by
    intro A' B' xj
    unfold E1at omPhi
    rw [firstUnfolding_omega_factor, show PhiAt Ch mu ({ cst with A := A', B := B' } : LocCst X (rowSG Pr sel mu)).sharp i P.1 = Φ from hPhi]
    rfl
  have hC : Loc.om (muAt Ch sel mu cst i P) (LocE.vP P.1 (qOf P.1)) (cst.sq P) (1 : AutY X R i) h₀ (fun _ => (1 : X.K)) 0 ≠ 0 := by
    unfold muAt
    exact ocbA_om_ne hq hu _ _ _ hh₀
  unfold FiniteSumNonzeroLargeDepth ocbNeAt ocbNe
  constructor
  · rintro ⟨A₀, B₀, hAB⟩
    have h1 := hAB (max A₀ (cOf R (i + 1) + 1)) (max B₀ 1) (le_max_left _ _) (le_max_left _ _)
    obtain ⟨xj, hxj⟩ := Function.ne_iff.1 h1
    rw [Pi.zero_apply, hE1] at hxj
    have hE := right_ne_zero_of_mul hxj
    have hxI : ocbXInt P.1 xj := by
      by_contra hn
      exact hE (firstUnfolding_eq_zero_of_not_integral hc' Ψ htsupp _ _ _ xj hn)
    let xbj : (Fin (R.N i) → 𝓞 X.E ⧸ P.1.asIdeal) →ₗ[𝓞 X.E ⧸ P.1.asIdeal] (Fin (R.N (i + 1)) → 𝓞 X.E ⧸ P.1.asIdeal) :=
      Matrix.toLin' (Matrix.of fun l s => redP P.1 (Loc.atN (xj (Loc.eN X.E (R.N i) s.1)) l.1))
    have hxR : ocbXRed P.1 xj xbj := by
      intro l s hl hs
      show Loc.atN (Matrix.toLin' _ (Loc.eN _ (R.N i) s)) l = _
      rw [ocbS_atN_toLin' _ hl hs]
      rfl
    have heq := firstUnfolding_reduction_eq hq hu hp hcard hc' σ Ψ Ψr htsupp hΨr (cst.psi P) (fun u => ocbPsiC Ch σ P.1 u) hpsi
      (le_max_right A₀ (cOf R (i + 1) + 1)) (le_max_right B₀ 1) xj xbj hxI hxR
    refine ⟨xbj, fun h0 => hE (σ.injective ?_)⟩
    rw [heq, map_zero]
    exact mul_eq_zero_of_right _ h0
  · rintro ⟨xbj, hne⟩
    refine ⟨cOf R (i + 1) + 1, 1, fun A' B' hA hB' hzero => ?_⟩
    let xj : (Fin (R.N i) → X.E) →ₗ[X.E] (Fin (R.N (i + 1)) → X.E) :=
      Matrix.toLin' (Matrix.of fun l s => algebraMap (𝓞 X.E) X.E (ciLift P.1 (Loc.atN (xbj (Loc.eN _ (R.N i) s.1)) l.1)))
    have hxI : ocbXInt P.1 xj := by
      intro l s hl hs
      show IntAt P.1 (Loc.atN (Matrix.toLin' _ (Loc.eN X.E (R.N i) s)) l)
      rw [ocbS_atN_toLin' _ hl hs]
      exact IntAt.coe P.1 _
    have hxR : ocbXRed P.1 xj xbj := by
      intro l s hl hs
      show _ = redP P.1 (Loc.atN (Matrix.toLin' _ (Loc.eN X.E (R.N i) s)) l)
      rw [ocbS_atN_toLin' _ hl hs, Matrix.of_apply, reduction_coe, ciLift_mk]
    have heq := firstUnfolding_reduction_eq hq hu hp hcard hc' σ Ψ Ψr htsupp hΨr (cst.psi P) (fun u => ocbPsiC Ch σ P.1 u) hpsi
      hA hB' xj xbj hxI hxR
    have h1 := congrFun hzero xj
    rw [hE1, Pi.zero_apply] at h1
    have h2 := (mul_eq_zero.1 h1).resolve_left hC
    rw [h2, map_zero] at heq
    exact hne ((mul_eq_zero.1 heq.symm).resolve_left (pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)))

end Glob

end Formalism.L2.Col
