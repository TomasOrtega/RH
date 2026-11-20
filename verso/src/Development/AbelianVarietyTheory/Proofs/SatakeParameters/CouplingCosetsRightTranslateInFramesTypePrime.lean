import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopEqProd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteOrderValuation.WeakApprox
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseCosetRepIntegralAfterScalingAtBadPrimeStatement
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPDivOfUnit
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CplCosetPt

section Gen

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Take `⟨n, d, h⟩` from `P.exists_primeCompl_mul_eq_of_integer x h`. Conclude with `⟨n, d, d.2, by rw [mul_comm]; exact h⟩`.
-/
theorem intAt_of_val_le (P : HeightOneSpectrum (𝓞 E)) (x : E) (h : P.valuation E x ≤ 1) :
    Formalism.L2.Col.IntAt P x := by
  obtain ⟨n, d, h⟩ := P.exists_primeCompl_mul_eq_of_integer x h
  exact ⟨n, d, d.2, by rw [mul_comm]; exact h⟩

/- English proof (translation)
Use `conv_lhs => rw [LinearMap.pi_apply_eq_sum_univ g w]`. Rewrite using `[Finset.sum_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, smul_eq_mul]`. Rewrite using `[show (fun j => if k = j then (1 : E) else 0) = Pi.single k 1 by funext j; simp [Pi.single_apply, eq_comm]]`.
-/
theorem lin_apply_eq_sum {n : ℕ} (g : (Fin n → E) →ₗ[E] (Fin n → E)) (w : Fin n → E) (l : Fin n) :
    g w l = ∑ k, w k * g (Pi.single k 1) l := by
  conv_lhs => rw [LinearMap.pi_apply_eq_sum_univ g w]
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  rw [show (fun j => if k = j then (1 : E) else 0) = Pi.single k 1 by funext j; simp [Pi.single_apply, eq_comm]]

/- English proof (translation)
Establish `hb : ∀ P : T, ∃ b : WithZero (Multiplicative ℤ), 1 ≤ b ∧ ∀ l k, (P.1).valuation E (c P * g P (Pi.single k 1) l) ≤ b`. Introduce `P`. Take `⟨b, hb⟩` from `(Set.finite_range fun lk : Fin n × Fin n => (P.1).valuation E (c P * g P (Pi.single lk.2 1) lk.1)).bddAbove`. Conclude with `⟨max b 1, le_max_right _ _, fun l k => (hb ⟨(l, k), rfl⟩).trans (le_max_left _ _)⟩`. Use `choose B hB1 hBle using hb`.

Establish `hB0 : ∀ P, B P ≠ 0` using `fun P => (lt_of_lt_of_le zero_lt_one (hB1 P)).ne'`. Establish `hk : ∀ k : Fin n, ∃ a : E, ∀ P : T, (P.1).valuation E (a - t P k) < (B P)⁻¹`. Introduce `k`. Take `⟨a, -, ha, -⟩` from `PI.FinOrdValD.WA.weakApprox T (fun v => if h : v ∈ T then algebraMap E (v.adicCompletion E) (t ⟨v, h⟩ k) else 0) (fun v => if h : v ∈ T then (B ⟨v, h⟩)⁻¹ else 1) (fun v hv => by simp only [dif_pos hv]; exact inv_ne_zero (hB0 _))`. Use `⟨a, fun P => ?_⟩` and prove the remaining obligations.

Establish `h` using `ha P.1 P.2`. Simplify using `only [dif_pos P.2, Subtype.coe_eta] at h`. Rewrite `h` using `[← map_sub, PI.FinOrdValD.WA.val_alg]`. Conclude with `h`. Use `choose a ha using hk`.

Use `⟨a, fun P l => ?_⟩` and prove the remaining obligations. Rewrite using `[lin_apply_eq_sum, Finset.mul_sum]`. Use `Valuation.map_sum_le _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[show c P * ((a - t P) k * g P (Pi.single k 1) l) = (a - t P) k * (c P * g P (Pi.single k 1) l) by ring, map_mul, Pi.sub_apply]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_approx_at (T : Finset (HeightOneSpectrum (𝓞 E))) {n : ℕ} (g : T → (Fin n → E) →ₗ[E] (Fin n → E))
    (c : T → E) (t : T → Fin n → E) :
    ∃ d : Fin n → E, ∀ P : T, ∀ l, (P.1).valuation E (c P * g P (d - t P) l) ≤ 1 := by
  classical
  have hb : ∀ P : T, ∃ b : WithZero (Multiplicative ℤ), 1 ≤ b ∧
      ∀ l k, (P.1).valuation E (c P * g P (Pi.single k 1) l) ≤ b := by
    intro P
    obtain ⟨b, hb⟩ := (Set.finite_range fun lk : Fin n × Fin n =>
      (P.1).valuation E (c P * g P (Pi.single lk.2 1) lk.1)).bddAbove
    exact ⟨max b 1, le_max_right _ _, fun l k => (hb ⟨(l, k), rfl⟩).trans (le_max_left _ _)⟩
  choose B hB1 hBle using hb
  have hB0 : ∀ P, B P ≠ 0 := fun P => (lt_of_lt_of_le zero_lt_one (hB1 P)).ne'
  have hk : ∀ k : Fin n, ∃ a : E, ∀ P : T, (P.1).valuation E (a - t P k) < (B P)⁻¹ := by
    intro k
    obtain ⟨a, -, ha, -⟩ := PI.FinOrdValD.WA.weakApprox T
      (fun v => if h : v ∈ T then algebraMap E (v.adicCompletion E) (t ⟨v, h⟩ k) else 0)
      (fun v => if h : v ∈ T then (B ⟨v, h⟩)⁻¹ else 1)
      (fun v hv => by simp only [dif_pos hv]; exact inv_ne_zero (hB0 _))
    refine ⟨a, fun P => ?_⟩
    have h := ha P.1 P.2
    simp only [dif_pos P.2, Subtype.coe_eta] at h
    rw [← map_sub, PI.FinOrdValD.WA.val_alg] at h
    exact h
  choose a ha using hk
  refine ⟨a, fun P l => ?_⟩
  rw [lin_apply_eq_sum, Finset.mul_sum]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [show c P * ((a - t P) k * g P (Pi.single k 1) l) = (a - t P) k * (c P * g P (Pi.single k 1) l) by ring,
    map_mul, Pi.sub_apply]
  calc (P.1).valuation E (a k - t P k) * (P.1).valuation E (c P * g P (Pi.single k 1) l)
      ≤ (B P)⁻¹ * B P := mul_le_mul' (ha k P).le (hBle P l k)
    _ = 1 := inv_mul_cancel₀ (hB0 P)

end Gen

/- English proof (translation)
Take `⟨d, hd⟩` from `exists_approx_at (rowSG Pr sel mu) (fun P => ((f P).symm : Sp X.E n →ₗ[X.E] Sp X.E n)) (fun P => (((qOf P.1 : ℕ) : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹) (fun P => f P (y0 P))`. Use `⟨d, fun P l => intAt_of_val_le _ _ ?_⟩` and prove the remaining obligations. Establish `h` using `hd P l`. Establish `e : (f P).symm d - y0 P = (f P).symm (d - f P (y0 P))`. Rewrite using `[map_sub, LinearEquiv.symm_apply_apply]`.

Rewrite using `[e]`. Conclude with `h`.
-/
theorem exists_sameCoset_frames {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {n : ℕ} (f : rowSG Pr sel mu → (Sp X.E n ≃ₗ[X.E] Sp X.E n))
    (y0 : rowSG Pr sel mu → Sp X.E n) :
    ∃ y : Sp X.E n, ∀ P, SameCoset sel mu cst P ((f P).symm y) (y0 P) := by
  classical
  obtain ⟨d, hd⟩ := exists_approx_at (rowSG Pr sel mu) (fun P => ((f P).symm : Sp X.E n →ₗ[X.E] Sp X.E n))
    (fun P => (((qOf P.1 : ℕ) : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹) (fun P => f P (y0 P))
  refine ⟨d, fun P l => intAt_of_val_le _ _ ?_⟩
  have h := hd P l
  have e : (f P).symm d - y0 P = (f P).symm (d - f P (y0 P)) := by
    rw [map_sub, LinearEquiv.symm_apply_apply]
  rw [e]
  exact h

end GlobalTheory.CplCosetPt

namespace GlobalTheory.CplCosetPt

/- English proof (translation)
Establish `hq : ((qOf P : ℕ) : E) ≠ 0`. Establish `: qOf P ≠ 0` using `fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)`. Conclude with `this` after adjusting the coercions. Use `set q : E := ((qOf P : ℕ) : E) with hqdef`. Establish `hsm : ∀ (a : E) (v : Sp E n), (∀ l, IntAt P (a * v l)) ↔ a • v ∈ stdAt E n P`.

Introduce `a v`. Rewrite using `[GlobalTheory.TopStep.mem_stdAt]`. Both sides reduce to the same expression. Establish `hpow : ∀ (m : ℕ) (v : Sp E n), v ∈ stdAt E n P → q ^ m • v ∈ stdAt E n P`. Introduce `m v hv`.

Establish `: q ^ m • v = ((qOf P : 𝓞 E) ^ m) • v`. Rewrite using `[← algebraMap_smul E ((qOf P : 𝓞 E) ^ m) v]`. Apply the tactic sequence `congr 1 <;> simp [hqdef]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hv`.

Establish `hw : q ^ e • y₀ ∈ stdAt E n P` using `(hsm _ _).1 hy₀`. Establish `hkw` using `hk _ hw`. Establish `hky : (q ^ e₀)⁻¹ • (k.1 y₀ - y₀) ∈ stdAt E n P`. Take `⟨d, hd⟩ : ∃ d, D = d + e + e₀` from `⟨D - e - e₀, by omega⟩`. Establish `e1 : (q ^ e₀)⁻¹ • (k.1 y₀ - y₀) = q ^ d • ((q ^ D)⁻¹ • (k.1 (q ^ e • y₀) - q ^ e • y₀))`.

Rewrite using `[map_smul, ← smul_sub, smul_smul, smul_smul]`. Use `congr 1`. Rewrite using `[hd, pow_add, pow_add]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e1]`.

Conclude with `hpow _ _ hkw`. Establish `hcy : (q ^ e₀)⁻¹ • (c⁻¹ y₀ - y₀) ∈ stdAt E n P`. Establish `e2 : c⁻¹ y₀ - y₀ = g (k.1 y₀ - y₀) + (g y₀ - y₀)`. Rewrite using `[hck, LinearEquiv.mul_apply, map_sub]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e2, smul_add, ← map_smul]`. Conclude with `add_mem ((hg _).2 hky) ((hsm _ _).1 hgy)`. Establish `hcc : ∀ x, c (c⁻¹ x) = x` using `fun x => by`. Rewrite using `[← LinearEquiv.mul_apply, mul_inv_cancel]`. Both sides reduce to the same expression.

Rewrite using `[hsm, hsm]`. Establish `e3 : (q ^ e₀)⁻¹ • (c y - y₀) = c ((q ^ e₀)⁻¹ • (y - y₀) - (q ^ e₀)⁻¹ • (c⁻¹ y₀ - y₀))`. Rewrite using `[← smul_sub, map_smul]`. Simplify using `only [map_sub, hcc]`. Use `congr 1`.

Normalize the expressions using the abelian group laws. Rewrite using `[e3, hc]`. Conclude with `Submodule.sub_mem_iff_left _ hcy`.
-/
theorem sameCoset_loc {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (e₀ e D : ℕ) (c g : Sp E n ≃ₗ[E] Sp E n) (k : GLint E n P) (hc : c ∈ GLint E n P) (hg : g ∈ GLint E n P)
    (hk : k ∈ GlobalTheory.TopStep.prinCong n P D) (hck : c⁻¹ = g * k.1) (hD : e + e₀ ≤ D) (y₀ : Sp E n)
    (hy₀ : ∀ l, IntAt P ((qOf P : E) ^ e * y₀ l)) (hgy : ∀ l, IntAt P (((qOf P : E) ^ e₀)⁻¹ * (g y₀ - y₀) l)) (y : Sp E n) :
    (∀ l, IntAt P (((qOf P : E) ^ e₀)⁻¹ * (c y - y₀) l)) ↔ (∀ l, IntAt P (((qOf P : E) ^ e₀)⁻¹ * (y - y₀) l)) := by
  have hq : ((qOf P : ℕ) : E) ≠ 0 := by
    have : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  set q : E := ((qOf P : ℕ) : E) with hqdef
  have hsm : ∀ (a : E) (v : Sp E n), (∀ l, IntAt P (a * v l)) ↔ a • v ∈ stdAt E n P := by
    intro a v
    rw [GlobalTheory.TopStep.mem_stdAt]
    rfl
  have hpow : ∀ (m : ℕ) (v : Sp E n), v ∈ stdAt E n P → q ^ m • v ∈ stdAt E n P := by
    intro m v hv
    have : q ^ m • v = ((qOf P : 𝓞 E) ^ m) • v := by
      rw [← algebraMap_smul E ((qOf P : 𝓞 E) ^ m) v]
      congr 1 <;> simp [hqdef]
    rw [this]
    exact Submodule.smul_mem _ _ hv
  have hw : q ^ e • y₀ ∈ stdAt E n P := (hsm _ _).1 hy₀
  have hkw := hk _ hw
  have hky : (q ^ e₀)⁻¹ • (k.1 y₀ - y₀) ∈ stdAt E n P := by
    obtain ⟨d, hd⟩ : ∃ d, D = d + e + e₀ := ⟨D - e - e₀, by omega⟩
    have e1 : (q ^ e₀)⁻¹ • (k.1 y₀ - y₀) = q ^ d • ((q ^ D)⁻¹ • (k.1 (q ^ e • y₀) - q ^ e • y₀)) := by
      rw [map_smul, ← smul_sub, smul_smul, smul_smul]
      congr 1
      rw [hd, pow_add, pow_add]
      field_simp
    rw [e1]
    exact hpow _ _ hkw
  have hcy : (q ^ e₀)⁻¹ • (c⁻¹ y₀ - y₀) ∈ stdAt E n P := by
    have e2 : c⁻¹ y₀ - y₀ = g (k.1 y₀ - y₀) + (g y₀ - y₀) := by
      rw [hck, LinearEquiv.mul_apply, map_sub]
      abel
    rw [e2, smul_add, ← map_smul]
    exact add_mem ((hg _).2 hky) ((hsm _ _).1 hgy)
  have hcc : ∀ x, c (c⁻¹ x) = x := fun x => by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  rw [hsm, hsm]
  have e3 : (q ^ e₀)⁻¹ • (c y - y₀) = c ((q ^ e₀)⁻¹ • (y - y₀) - (q ^ e₀)⁻¹ • (c⁻¹ y₀ - y₀)) := by
    rw [← smul_sub, map_smul]
    simp only [map_sub, hcc]
    congr 1
    abel
  rw [e3, hc]
  exact Submodule.sub_mem_iff_left _ hcy

/- English proof (translation)
Introduce `x hx`. Rewrite using `[mem_stdAt]`. Introduce `i`. Establish `hjx` using `mem_stdAt.1 (glint_mem j hx) i`. Establish `hxi` using `mem_stdAt.1 hx i`.

Establish `hr : redP P (j.1 x i) = redP P (x i)`. Establish `h` using `congrFun (redV_redGL j hx) i`. Rewrite `h` using `[hj, Units.val_one, Matrix.one_mulVec]`. Conclude with `h`. Establish `hred : redP P (j.1 x i - x i) = 0`.

Rewrite using `[reduction_sub hjx hxi, hr, sub_self]`. Establish `h` using `intAt_div_of_redP hq (intAt_sub hjx hxi) hred`. Establish `e : (((qOf P : E) ^ 1)⁻¹ • (j.1 x - x)) i = (j.1 x i - x i) / (qOf P : E)`. Simplify using `[div_eq_inv_mul]`. Rewrite using `[e]`.

Conclude with `h`.
-/
theorem mem_prinCong_one_of_redGL {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (j : GLint E n P) (hj : redGL n P j = 1) : j ∈ prinCong n P 1 := by
  intro x hx
  rw [mem_stdAt]
  intro i
  have hjx := mem_stdAt.1 (glint_mem j hx) i
  have hxi := mem_stdAt.1 hx i
  have hr : redP P (j.1 x i) = redP P (x i) := by
    have h := congrFun (redV_redGL j hx) i
    rw [hj, Units.val_one, Matrix.one_mulVec] at h
    exact h
  have hred : redP P (j.1 x i - x i) = 0 := by
    rw [reduction_sub hjx hxi, hr, sub_self]
  have h := intAt_div_of_redP hq (intAt_sub hjx hxi) hred
  have e : (((qOf P : E) ^ 1)⁻¹ • (j.1 x - x)) i = (j.1 x i - x i) / (qOf P : E) := by
    simp [div_eq_inv_mul]
  rw [e]
  exact h

/- English proof (translation)
Introduce `D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin H hi β p p₁ P hP Gg k z hrel hred _hfr`. Establish `hne : ∀ q : ChPt (R` using `D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1), repY (cosetOf A (t.m2 + 1) hi β q) ∈ cosetOf A (t.m2 + 1) hi β q := by`. Introduce `q`. Take `⟨y, hy⟩` from `exists_sameCoset_frames t.sel (t.tup μ) (t.cst μ) (fun P => frsF t.sel (t.tup μ) q P) (fun P => y0At A (t.m2 + 1) hi β P)`. Conclude with `Classical.epsilon_spec (p := fun y => y ∈ cosetOf A (t.m2 + 1) hi β q) ⟨y, hy⟩`.

Establish `hyy : y0At A (t.m2 + 1) hi β P = A.y0 β P`. Unfold `y0At`. Rewrite using `[dif_pos rfl]`. Establish `hloc : ∀ q : ChPt (R` using `D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1), ∀ l, IntAt P.1 (((qOf P.1 : t.X.E) ^ 0)⁻¹ * ((frsF t.sel (t.tup μ) q P).symm (repY (cosetOf A (t.m2 + 1) hi β q)) - A.y0 β P) l) := by`. Introduce `q`.

Establish `h` using `hne q P`. Unfold `SameCoset at h`. Simplify `h` using `only [hP, if_true, hyy]`. Establish `hy₀ : ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) ^ 1 * A.y0 β P l)`. Introduce `l`.

Establish `h` using `GlobalTheory.T.intAt_scaled_baseCosetRep_of_adTie D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin H β P l`. Simplify `h` using `only [hP, if_true]`. Establish `hqI : IntAt P.1 (qOf P.1 : t.X.E)`. Simplify using `using IntAt.coe P.1 ((qOf P.1 : ℕ) : 𝓞 t.X.E)`. Establish `hint : ∀ q : ChPt (R` using `D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1), ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * (frsF t.sel (t.tup μ) q P).symm (repY (cosetOf A (t.m2 + 1) hi β q)) l) := by`.

Introduce `q l`. Establish `h1` using `hqI.mul (hloc q l)`. Establish `e : (qOf P.1 : t.X.E) * (frsF t.sel (t.tup μ) q P).symm (repY (cosetOf A (t.m2 + 1) hi β q)) l = (qOf P.1 : t.X.E) * (((qOf P.1 : t.X.E) ^ 0)⁻¹ * ((frsF t.sel (t.tup μ) q P).symm (repY (cosetOf A (t.m2 + 1) hi β q)) - A.y0 β P) l) + (qOf P.1 : t.X.E) ^ 1 * A.y0 β P l`. Simplify using `only [pow_zero, inv_one, one_mul, pow_one, Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `h1.add (hy₀ l)`. Use `⟨hint p, hint p₁, ?_⟩` and prove the remaining obligations. Establish `hgy : ∀ l, IntAt P.1 (((qOf P.1 : t.X.E) ^ 0)⁻¹ * (Gg.1 (A.y0 β P) - A.y0 β P) l)`. Establish `h` using `hrel.2`.

Unfold `SameCoset at h`. Simplify `h` using `only [hP, if_true]`. Establish `hj : Gg⁻¹ * k ∈ prinCong _ P.1 1`. Use `mem_prinCong_one_of_redGL (qOf_notMem_sq hPin.fields.ok t.pr_ok hP) _ ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_inv, hred, inv_mul_cancel]`.

Establish `hck : (k.1⁻¹)⁻¹ = Gg.1 * (Gg⁻¹ * k).1`. Rewrite using `[inv_inv, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]`. Establish `key` using `(sameCoset_loc P.1 0 1 1 k.1⁻¹ Gg.1 (Gg⁻¹ * k) (inv_mem k.2) Gg.2 hj hck (by omega) (A.y0 β P) hy₀ hgy (k.1 ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁))))).1 (by`. Introduce `l`. Establish `e : (k.1⁻¹) (k.1 ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)))) = (frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁))` using `k.1.symm_apply_apply _`.

Rewrite using `[e]`. Conclude with `hloc p₁ l)`. Rewrite using `[mem_stdAt]`. Introduce `l`. Establish `e : (k.1 ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁))) - (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p))) l = ((qOf P.1 : t.X.E) ^ 0)⁻¹ * (k.1 ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁))) - A.y0 β P) l - …`.

Simplify using `only [pow_zero, inv_one, one_mul, Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `intAt_sub (key l) (hloc p l)`.
-/
theorem cosetOf_frames_vG : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1))
    (P : SB t μ), P.1 ∈ t.Pr.vGs → ∀ (Gg k : GLint t.X.E (D.R.N (t.m2 + 1)) P.1) z, A.cplRel β P Gg.1 z →
    redGL _ P.1 k = redGL _ P.1 Gg → frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k.1 →
    (∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p)) l)) ∧
    (∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * (frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) l)) ∧
    k.1 ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁))) -
      (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p)) ∈ stdAt t.X.E _ P.1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin H hi β p p₁ P hP Gg k z hrel hred _hfr
  classical
  have hne : ∀ q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1),
      repY (cosetOf A (t.m2 + 1) hi β q) ∈ cosetOf A (t.m2 + 1) hi β q := by
    intro q
    obtain ⟨y, hy⟩ := exists_sameCoset_frames t.sel (t.tup μ) (t.cst μ) (fun P => frsF t.sel (t.tup μ) q P)
      (fun P => y0At A (t.m2 + 1) hi β P)
    exact Classical.epsilon_spec (p := fun y => y ∈ cosetOf A (t.m2 + 1) hi β q) ⟨y, hy⟩
  have hyy : y0At A (t.m2 + 1) hi β P = A.y0 β P := by
    unfold y0At
    rw [dif_pos rfl]
  have hloc : ∀ q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1), ∀ l,
      IntAt P.1 (((qOf P.1 : t.X.E) ^ 0)⁻¹ * ((frsF t.sel (t.tup μ) q P).symm (repY (cosetOf A (t.m2 + 1) hi β q)) - A.y0 β P) l) := by
    intro q
    have h := hne q P
    unfold SameCoset at h
    simpa only [hP, if_true, hyy] using h
  have hy₀ : ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) ^ 1 * A.y0 β P l) := by
    intro l
    have h := GlobalTheory.T.intAt_scaled_baseCosetRep_of_adTie D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin H β P l
    simpa only [hP, if_true] using h
  have hqI : IntAt P.1 (qOf P.1 : t.X.E) := by
    simpa using IntAt.coe P.1 ((qOf P.1 : ℕ) : 𝓞 t.X.E)
  have hint : ∀ q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1), ∀ l,
      IntAt P.1 ((qOf P.1 : t.X.E) * (frsF t.sel (t.tup μ) q P).symm (repY (cosetOf A (t.m2 + 1) hi β q)) l) := by
    intro q l
    have h1 := hqI.mul (hloc q l)
    have e : (qOf P.1 : t.X.E) * (frsF t.sel (t.tup μ) q P).symm (repY (cosetOf A (t.m2 + 1) hi β q)) l =
        (qOf P.1 : t.X.E) * (((qOf P.1 : t.X.E) ^ 0)⁻¹ * ((frsF t.sel (t.tup μ) q P).symm (repY (cosetOf A (t.m2 + 1) hi β q)) - A.y0 β P) l) +
          (qOf P.1 : t.X.E) ^ 1 * A.y0 β P l := by
      simp only [pow_zero, inv_one, one_mul, pow_one, Pi.sub_apply]
      ring
    rw [e]
    exact h1.add (hy₀ l)
  refine ⟨hint p, hint p₁, ?_⟩
  have hgy : ∀ l, IntAt P.1 (((qOf P.1 : t.X.E) ^ 0)⁻¹ * (Gg.1 (A.y0 β P) - A.y0 β P) l) := by
    have h := hrel.2
    unfold SameCoset at h
    simpa only [hP, if_true] using h
  have hj : Gg⁻¹ * k ∈ prinCong _ P.1 1 := by
    refine mem_prinCong_one_of_redGL (qOf_notMem_sq hPin.fields.ok t.pr_ok hP) _ ?_
    rw [map_mul, map_inv, hred, inv_mul_cancel]
  have hck : (k.1⁻¹)⁻¹ = Gg.1 * (Gg⁻¹ * k).1 := by
    rw [inv_inv, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  have key := (sameCoset_loc P.1 0 1 1 k.1⁻¹ Gg.1 (Gg⁻¹ * k) (inv_mem k.2) Gg.2 hj hck (by omega) (A.y0 β P) hy₀ hgy
    (k.1 ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁))))).1 (by
      intro l
      have e : (k.1⁻¹) (k.1 ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)))) =
          (frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) := k.1.symm_apply_apply _
      rw [e]
      exact hloc p₁ l)
  rw [mem_stdAt]
  intro l
  have e : (k.1 ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁))) -
      (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p))) l =
      ((qOf P.1 : t.X.E) ^ 0)⁻¹ * (k.1 ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁))) - A.y0 β P) l -
      ((qOf P.1 : t.X.E) ^ 0)⁻¹ * ((frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p)) - A.y0 β P) l := by
    simp only [pow_zero, inv_one, one_mul, Pi.sub_apply]
    ring
  rw [e]
  exact intAt_sub (key l) (hloc p l)

end GlobalTheory.CplCosetPt

end
