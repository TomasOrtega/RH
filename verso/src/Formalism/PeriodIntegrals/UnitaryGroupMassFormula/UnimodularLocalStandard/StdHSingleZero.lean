import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.SatStdOfAll

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
variable {m : Type*} [Fintype m] [DecidableEq m]

/- English proof (translation)
Rewrite using `[stdH_apply, stdH_apply, map_mul, map_inv₀, Complex.conj_ofReal, map_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, Complex.conj_conj, mul_comm]`.
-/
lemma stdH_symm (L : PeriodPair) (x y : m → ℂ) : stdH L m y x = conj (stdH L m x y) := by
  rw [stdH_apply, stdH_apply, map_mul, map_inv₀, Complex.conj_ofReal, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, Complex.conj_conj, mul_comm]

/- English proof (translation)
Rewrite using `[stdH_apply]`. Establish `hsum : ∑ i, (Pi.single j w : m → ℂ) i * conj (z i) = 0`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Rewrite using `[hz, map_zero, mul_zero]`. Simplify using `[h]`. Rewrite using `[hsum, zero_mul]`.
-/
lemma stdH_single_zero (L : PeriodPair) (j : m) (w : ℂ) {z : m → ℂ} (hz : z j = 0) :
    stdH L m (Pi.single j w) z = 0 := by
  rw [stdH_apply]
  have hsum : ∑ i, (Pi.single j w : m → ℂ) i * conj (z i) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h : i = j
    · subst h
      rw [hz, map_zero, mul_zero]
    · simp [h]
  rw [hsum, zero_mul]

/- English proof (translation)
Establish `h1 : PI.ULS.stdH L m v (v - f') = PI.ULS.stdH L m v v - PI.ULS.stdH L m v f'` using `map_sub (PI.ULS.stdH L m v) v f'`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `h2 : PI.ULS.stdH L m (v - f') (v - f') = PI.ULS.stdH L m v v - PI.ULS.stdH L m v f' - (PI.ULS.stdH L m f' v - PI.ULS.stdH L m f' f')`. Simplify using `only [map_sub, LinearMap.sub_apply]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h1, h2, map_sub, ← stdH_symm L v f', ← stdH_symm L v v, hvv]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem stdH_sub_eq_and_add_conj_eq_of_stdH_eq (L : PeriodPair) (v f' : m → ℂ)
    (hvv : PI.ULS.stdH L m v v = PI.ULS.stdH L m f' f') :
    PI.ULS.stdH L m v (v - f') = PI.ULS.stdH L m v v - PI.ULS.stdH L m v f' ∧
      PI.ULS.stdH L m v (v - f') + conj (PI.ULS.stdH L m v (v - f')) =
        PI.ULS.stdH L m (v - f') (v - f') := by
  have h1 : PI.ULS.stdH L m v (v - f') = PI.ULS.stdH L m v v - PI.ULS.stdH L m v f' :=
    map_sub (PI.ULS.stdH L m v) v f'
  refine ⟨h1, ?_⟩
  have h2 : PI.ULS.stdH L m (v - f') (v - f') =
      PI.ULS.stdH L m v v - PI.ULS.stdH L m v f' - (PI.ULS.stdH L m f' v - PI.ULS.stdH L m f' f') := by
    simp only [map_sub, LinearMap.sub_apply]
    ring
  rw [h1, h2, map_sub, ← stdH_symm L v f', ← stdH_symm L v v, hvv]
  ring

/- English proof (translation)
Take `⟨s, hs, hH⟩` from `isK_H hn L hl0 hw hz`. Rewrite using `[hH, mul_inv_rev, mul_assoc, inv_mul_cancel_left₀ (kappa_ne L hl0)]`. Conclude with `isKv_sub hw (isKv_smul hn (isK_mul hn (isK_inv hn ht) hs) hz)`.
-/
private theorem isKv_sub_stdH_smul {L : PeriodPair} {e : ℤ}
    (hn : PI.ULS.cmTheta b d * (b - PI.ULS.cmTheta b d) = (e : ℂ)) (hl0 : lam ≠ 0) {z w : m → ℂ} {t : ℂ}
    (ht : IsK b d t) (hz : IsKv b d lam z) (hw : IsKv b d lam w) :
    IsKv b d lam (w - ((kappa L lam * t)⁻¹ * PI.ULS.stdH L m w z) • z) := by
  obtain ⟨s, hs, hH⟩ := isK_H hn L hl0 hw hz
  rw [hH, mul_inv_rev, mul_assoc, inv_mul_cancel_left₀ (kappa_ne L hl0)]
  exact isKv_sub hw (isKv_smul hn (isK_mul hn (isK_inv hn ht) hs) hz)

/- English proof (translation)
Take `⟨hvz, hκ⟩` from `stdH_sub_eq_and_add_conj_eq_of_stdH_eq (PI.ULS.cmL a b d ha hd lam hlam) v f' hvv`. Establish `hκ0 : PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m v (v - f') ≠ 0`. Rewrite using `[hvz]`. Conclude with `hne`. Establish `hn : PI.ULS.cmTheta b d * (b - PI.ULS.cmTheta b d) = ((a * c : ℤ) : ℂ)`.

Rewrite using `[theta_norm hok.1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hzK : IsKv b d lam (v - f')` using `isKv_sub hvK hfK`. Take `⟨t, ht, htF⟩` from `isK_H hn (PI.ULS.cmL a b d ha hd lam hlam) hlam hvK hzK`.

Establish `htF' : conj (PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m v (v - f')) = kappa (PI.ULS.cmL a b d ha hd lam hlam) lam * conj t`. Rewrite using `[htF, map_mul, kappa_conj]`. Take `⟨σ, hσ⟩ : ∃ σ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ), σ = qequiv (PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m) (v - f') hκ0 hκ` from `⟨_, rfl⟩`. Establish `hσapp : ∀ x, σ x = x - ((PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m v (v - f'))⁻¹ * PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m x (v - f')) • (v - f')`. Introduce `x`.

Rewrite using `[hσ, qequiv_apply]`. Establish `hσsymm : ∀ x, σ.symm x = x - ((conj (PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m v (v - f')))⁻¹ * PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m x (v - f')) • (v - f')`. Introduce `x`. Rewrite using `[hσ, ← qmap_apply]`. Both sides reduce to the same expression.

Establish `hs1 : ∀ i : m, IsKv b d lam (Pi.single i (PI.ULS.cmL a b d ha hd lam hlam).ω₁ : m → ℂ)` using `fun i => isKv_single (by`. Rewrite using `[cmL_omega1, mul_div_cancel_left₀ _ hlam]`. Conclude with `isK_int (b := b) (d := d) (a : ℤ)) i` after adjusting the coercions. Establish `hs2 : ∀ i : m, IsKv b d lam (Pi.single i (PI.ULS.cmL a b d ha hd lam hlam).ω₂ : m → ℂ)` using `fun i => isKv_single (by`. Rewrite using `[cmL_omega2, mul_div_cancel_left₀ _ hlam]`.

Conclude with `isK_theta) i`. Establish `hφ : ∀ x, IsKv b d lam x → IsKv b d lam ((σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) x)`. Introduce `x hx`. Rewrite using `[LinearEquiv.coe_coe, hσapp, htF]`. Conclude with `isKv_sub_stdH_smul hn hlam ht hzK hx`.

Establish `hψ : ∀ x, IsKv b d lam x → IsKv b d lam ((σ.symm : (m → ℂ) →ₗ[ℂ] (m → ℂ)) x)`. Introduce `x hx`. Rewrite using `[LinearEquiv.coe_coe, hσsymm, htF']`. Conclude with `isKv_sub_stdH_smul hn hlam (isK_conj ht) hzK hx`. Take `⟨N, hN, hN1⟩` from `bounded_map (a := a) (b := b) (d := d) (ha := ha) (hd := hd) (lam := lam) (hlam := hlam) (σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (fun i => hφ _ (hs1 i)) (fun i => hφ _ (hs2 i))`.

Take `⟨N', hN', hN2⟩` from `bounded_map (a := a) (b := b) (d := d) (ha := ha) (hd := hd) (lam := lam) (hlam := hlam) (σ.symm : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (fun i => hψ _ (hs1 i)) (fun i => hψ _ (hs2 i))`. Establish `hidx` using `comm_of_bounded σ hN hN' (fun s hs => hN1 s hs) (fun s hs => hN2 s hs)`. Use `⟨σ, ?_, hidx.1, hidx.2, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hσ]`. Conclude with `qequiv_isom _ (fun x y => stdH_symm _ x y) _ hκ0 hκ`.

Rewrite using `[hσapp, inv_mul_cancel₀ hκ0, one_smul, sub_sub_cancel]`. Introduce `w hw`. Rewrite using `[hσapp, hw, mul_zero, zero_smul, sub_zero]`.
-/
lemma qrefl_to (hok : CmOK a b c d) (v f' : m → ℂ)
    (hvv : stdH (cmL a b d ha hd lam hlam) m v v = stdH (cmL a b d ha hd lam hlam) m f' f')
    (hne : stdH (cmL a b d ha hd lam hlam) m v v - stdH (cmL a b d ha hd lam hlam) m v f' ≠ 0)
    (hvK : IsKv b d lam v) (hfK : IsKv b d lam f') :
    ∃ σ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ),
      IsIsom (stdH (cmL a b d ha hd lam hlam) m) (stdH (cmL a b d ha hd lam hlam) m) (σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) ∧
      relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (stdLat (cmL a b d ha hd lam hlam) m)) ≠ 0 ∧
      relIdx (imgLat (σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (stdLat (cmL a b d ha hd lam hlam) m)) (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 ∧
      σ v = f' ∧ ∀ w, stdH (cmL a b d ha hd lam hlam) m w (v - f') = 0 → σ w = w := by
  obtain ⟨hvz, hκ⟩ := stdH_sub_eq_and_add_conj_eq_of_stdH_eq (PI.ULS.cmL a b d ha hd lam hlam) v f' hvv
  have hκ0 : PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m v (v - f') ≠ 0 := by
    rw [hvz]; exact hne
  have hn : PI.ULS.cmTheta b d * (b - PI.ULS.cmTheta b d) = ((a * c : ℤ) : ℂ) := by
    rw [theta_norm hok.1]; push_cast; ring
  have hzK : IsKv b d lam (v - f') := isKv_sub hvK hfK
  obtain ⟨t, ht, htF⟩ := isK_H hn (PI.ULS.cmL a b d ha hd lam hlam) hlam hvK hzK
  have htF' : conj (PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m v (v - f')) =
      kappa (PI.ULS.cmL a b d ha hd lam hlam) lam * conj t := by
    rw [htF, map_mul, kappa_conj]
  obtain ⟨σ, hσ⟩ : ∃ σ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ),
      σ = qequiv (PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m) (v - f') hκ0 hκ := ⟨_, rfl⟩
  have hσapp : ∀ x, σ x = x - ((PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m v (v - f'))⁻¹ *
      PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m x (v - f')) • (v - f') := by
    intro x; rw [hσ, qequiv_apply]
  have hσsymm : ∀ x, σ.symm x = x - ((conj (PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m v (v - f')))⁻¹ *
      PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m x (v - f')) • (v - f') := by
    intro x; rw [hσ, ← qmap_apply]; rfl
  have hs1 : ∀ i : m, IsKv b d lam (Pi.single i (PI.ULS.cmL a b d ha hd lam hlam).ω₁ : m → ℂ) := fun i =>
    isKv_single (by
      rw [cmL_omega1, mul_div_cancel_left₀ _ hlam]
      exact_mod_cast isK_int (b := b) (d := d) (a : ℤ)) i
  have hs2 : ∀ i : m, IsKv b d lam (Pi.single i (PI.ULS.cmL a b d ha hd lam hlam).ω₂ : m → ℂ) := fun i =>
    isKv_single (by
      rw [cmL_omega2, mul_div_cancel_left₀ _ hlam]
      exact isK_theta) i
  have hφ : ∀ x, IsKv b d lam x → IsKv b d lam ((σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) x) := by
    intro x hx
    rw [LinearEquiv.coe_coe, hσapp, htF]
    exact isKv_sub_stdH_smul hn hlam ht hzK hx
  have hψ : ∀ x, IsKv b d lam x →
      IsKv b d lam ((σ.symm : (m → ℂ) →ₗ[ℂ] (m → ℂ)) x) := by
    intro x hx
    rw [LinearEquiv.coe_coe, hσsymm, htF']
    exact isKv_sub_stdH_smul hn hlam (isK_conj ht) hzK hx
  obtain ⟨N, hN, hN1⟩ := bounded_map (a := a) (b := b) (d := d) (ha := ha) (hd := hd)
    (lam := lam) (hlam := hlam) (σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (fun i => hφ _ (hs1 i)) (fun i => hφ _ (hs2 i))
  obtain ⟨N', hN', hN2⟩ := bounded_map (a := a) (b := b) (d := d) (ha := ha) (hd := hd)
    (lam := lam) (hlam := hlam) (σ.symm : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (fun i => hψ _ (hs1 i)) (fun i => hψ _ (hs2 i))
  have hidx := comm_of_bounded σ hN hN' (fun s hs => hN1 s hs) (fun s hs => hN2 s hs)
  refine ⟨σ, ?_, hidx.1, hidx.2, ?_, ?_⟩
  · rw [hσ]
    exact qequiv_isom _ (fun x y => stdH_symm _ x y) _ hκ0 hκ
  · rw [hσapp, inv_mul_cancel₀ hκ0, one_smul, sub_sub_cancel]
  · intro w hw
    rw [hσapp, hw, mul_zero, zero_smul, sub_zero]

end PI.UnitaryGroupMassFormula.UnimodLocStd
