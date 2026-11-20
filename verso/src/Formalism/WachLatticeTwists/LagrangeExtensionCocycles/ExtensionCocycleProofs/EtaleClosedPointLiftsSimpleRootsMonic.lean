import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.LiftExistsSecondCase
import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.UnitLemmaCaseALevelZero

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

open Polynomial Formalism.CoboundaryTransfers

section

variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] {B : Base ℤ_[ℓ] A} {M : ℕ}
  {D₀ D₁ D₂ : Type}
  [AddCommGroup D₀] [Module A D₀] [Module ℤ_[ℓ] D₀] [IsScalarTower ℤ_[ℓ] A D₀]
  [AddCommGroup D₁] [Module A D₁] [Module ℤ_[ℓ] D₁] [IsScalarTower ℤ_[ℓ] A D₁]
  [AddCommGroup D₂] [Module A D₂] [Module ℤ_[ℓ] D₂] [IsScalarTower ℤ_[ℓ] A D₂]
  {W₀ : WachMod B M D₀} {W₁ : WachMod B M D₁} {W₂ : WachMod B M D₂}

/- English proof (translation)
Take `⟨d, rfl⟩` from `h`. Introduce `y z hyz`. Take `⟨y₁, z₁, hc, hy, hz⟩` from `hL y z hyz`. Use `⟨d • y₁, d • z₁, W₁.cocycle_smulO d hc, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.map_smul_of_tower, hy, smul_smul, mul_comm]`.

Rewrite using `[LinearMap.map_smul_of_tower, hz, smul_smul, mul_comm]`.
-/
theorem lifts_of_dvd (S : SES W₀ W₁ W₂) {c c' : ℤ_[ℓ]} (h : c ∣ c') (hL : Lifts S c) :
    Lifts S c' := by
  obtain ⟨d, rfl⟩ := h
  intro y z hyz
  obtain ⟨y₁, z₁, hc, hy, hz⟩ := hL y z hyz
  refine ⟨d • y₁, d • z₁, W₁.cocycle_smulO d hc, ?_, ?_⟩
  · rw [LinearMap.map_smul_of_tower, hy, smul_smul, mul_comm]
  · rw [LinearMap.map_smul_of_tower, hz, smul_smul, mul_comm]

/- English proof (translation)
Introduce `n hn`. Establish `hK' : (pairOfHom F u₁ h).Kills (B.X ^ ((H + (ℓ - 2)) / (ℓ - 1)))`. Introduce `n hn`. Take `⟨n₁, hn₁, he⟩` from `hK n hn`. Conclude with `⟨n₁, hn₁, he⟩`.

Establish `hW` using `(unit_lemma_case_a_level_zero ℓ hℓ A (gbase B u₁ h) D' (pairOfHom F u₁ h) H hv hK').2`. Take `⟨n₁, hn₁, he⟩` from `hW n hn`. Use `⟨n₁, hn₁, ?_⟩` and prove the remaining obligations. Rewrite using `[he, ← IsScalarTower.algebraMap_smul A ((ℓ : ℤ_[ℓ]) ^ eWA ℓ H) n, map_pow, map_natCast]`.
-/
theorem homKillsA (hℓ : ℓ ≠ 2) {D D' : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
    [IsScalarTower ℤ_[ℓ] A D] [AddCommGroup D'] [Module A D'] [Module ℤ_[ℓ] D']
    [IsScalarTower ℤ_[ℓ] A D'] {W : WachMod B M D} {W' : WachMod B M D'} (F : Hom W W')
    (u₁ : ℤ_[ℓ]ˣ) (h : B.GammaX (u₁ : ℤ_[ℓ])) (H : ℕ)
    (hv : PadicInt.valuation ((u₁ : ℤ_[ℓ]) - 1) = 1) (hK : XKills F ((H + (ℓ - 2)) / (ℓ - 1))) :
    ∀ n ∈ W'.N, ∃ n₁ ∈ W.N, F.f n₁ = ((ℓ : ℤ_[ℓ]) ^ eWA ℓ H) • n := by
  intro n hn
  have hK' : (pairOfHom F u₁ h).Kills (B.X ^ ((H + (ℓ - 2)) / (ℓ - 1))) := by
    intro n hn
    obtain ⟨n₁, hn₁, he⟩ := hK n hn
    exact ⟨n₁, hn₁, he⟩
  have hW := (unit_lemma_case_a_level_zero ℓ hℓ A (gbase B u₁ h) D' (pairOfHom F u₁ h) H hv hK').2
  obtain ⟨n₁, hn₁, he⟩ := hW n hn
  refine ⟨n₁, hn₁, ?_⟩
  rw [he, ← IsScalarTower.algebraMap_smul A ((ℓ : ℤ_[ℓ]) ^ eWA ℓ H) n, map_pow, map_natCast]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `y _ hy`. Simplify using `using hy`. Consider the case `succ k ih`.

Introduce `y hQ hy`. Apply `hZ y hQ` to reduce the goal to its premises. Apply `ih ((ℓ : ℤ_[ℓ]) • y)` to reduce the goal to its premises. Rewrite using `[← IsScalarTower.algebraMap_smul A (ℓ : ℤ_[ℓ]) y]`. Conclude with `W.qInv_smul _ hQ`.

Rewrite using `[smul_smul, ← pow_succ]`. Conclude with `hy`.
-/
theorem noTors_pow (W : WachMod B M D₀)
    (hZ : ∀ y, W.QInv y → (ℓ : ℤ_[ℓ]) • y ∈ W.N → y ∈ W.N) (k : ℕ) :
    ∀ y, W.QInv y → ((ℓ : ℤ_[ℓ]) ^ k) • y ∈ W.N → y ∈ W.N := by
  induction k with
  | zero =>
    intro y _ hy
    simpa using hy
  | succ k ih =>
    intro y hQ hy
    apply hZ y hQ
    apply ih ((ℓ : ℤ_[ℓ]) • y)
    · rw [← IsScalarTower.algebraMap_smul A (ℓ : ℤ_[ℓ]) y]
      exact W.qInv_smul _ hQ
    · rw [smul_smul, ← pow_succ]
      exact hy

end

/- English proof (translation)
Introduce `ℓ _ hℓ A _ _ B M u H jumps c hp hPhi hγX hv hc D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S δ H₁ H₂ _ _ _ _ cl₁ cl₂ Hf₁ Hf₂ g I _ hδ hQI hφI hRL hNT hXK hSemi hNat hC1 hC2 hInj hE1 hE2 hRO`. Establish `hprime : ℓ.Prime` using `Fact.out`. Establish `h3 : 3 ≤ ℓ` using `by have := hprime.two_le; omega`. Use `set eW := eWA ℓ H with heW`. Use `set u₁ : ℤ_[ℓ]ˣ := u ^ (ℓ - 1) with hu₁`.

Establish `hu₁c : (u₁ : ℤ_[ℓ]) = (u : ℤ_[ℓ]) ^ (ℓ - 1)` using `by rw [hu₁, Units.val_pow_eq_pow_val]`. Establish `hγX₁ : B.GammaX (u₁ : ℤ_[ℓ])` using `by rw [hu₁c]; exact hγX`. Establish `hv₁ : PadicInt.valuation ((u₁ : ℤ_[ℓ]) - 1) = 1`. Rewrite using `[hu₁c, Formalism.ResultantValuation.powSubOneValuation ℓ hℓ (u : ℤ_[ℓ]) hv (ℓ - 1) (by omega), padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))]`. Establish `hCK : CokerKilled S eW`.

Introduce `n hn`. Rewrite using `[hp]`. Conclude with `homKillsA hℓ S.π u₁ hγX₁ H hv₁ hXK n hn`. Establish `hInt₁ : ∀ κ ∈ Hf₁, ∃ pr : W₁.Z1, W₁.Cocycle (pr : D₁ × D₁).1 (pr : D₁ × D₁).2 ∧ cl₁ pr = ((ℓ : ℤ_[ℓ]) ^ eW) • κ`. Introduce `κ hκ`.

Take `⟨E, hEK, hED⟩` from `hE1 κ hκ`. Conclude with `extension_class_is_cocycle ℓ A B M D₁ W₁ H₁ cl₁ κ E eW hED (homKillsA hℓ E.S.π u₁ hγX₁ H hv₁ hEK)`. Establish `hInt₂ : ∀ κ ∈ Hf₂, ∃ pr : W₂.Z1, W₂.Cocycle (pr : D₂ × D₂).1 (pr : D₂ × D₂).2 ∧ cl₂ pr = ((ℓ : ℤ_[ℓ]) ^ eW) • κ`. Introduce `κ hκ`. Take `⟨E, hEK, hED⟩` from `hE2 κ hκ`.

Conclude with `extension_class_is_cocycle ℓ A B M D₂ W₂ H₂ cl₂ κ E eW hED (homKillsA hℓ E.S.π u₁ hγX₁ H hv₁ hEK)`. Establish `hRS : RatSurj S` using `rational_points_map_surjective ℓ A B M D₀ D₁ D₂ W₀ W₁ W₂ S H₁ H₂ cl₁ cl₂ Hf₁ Hf₂ g eW hp hNat hC2 hInj hRO hInt₁`. Use `set a := M / (ℓ - 1) with ha`. Establish `hMa : M + 1 ≤ (ℓ - 1) * (a + 1)` using `Nat.lt_mul_div_succ M (by omega)`. Establish `h1` using `phi_map_surjective ℤ_[ℓ] A B M D₀ W₀ I (ℓ - 1) (a + 1) hPhi hMa hQI hφI`.

Establish `hZ` using `regulator_bound_for_l ℓ A B M D₀ W₀ hRL hNT`. Establish `hℓ0 : (ℓ : ℤ_[ℓ]) ≠ 0` using `by exact_mod_cast hprime.ne_zero`. Establish `hc0 : c 0 = 0`. Use `hc 0` as an intermediate fact. Simplify using `only [neg_zero, zpow_zero, Units.val_one, sub_self, mul_eq_zero] at this`.

Conclude with `this.resolve_left hℓ0`. Establish `hstab : ∀ n ∈ W₀.N.restrictScalars ℤ_[ℓ], δ n ∈ W₀.N.restrictScalars ℤ_[ℓ]`. Introduce `n hn`. Take `⟨x', hx', h⟩` from `W₀.γ_N n hn`. Establish `: δ n = x'`.

Establish `h0 : B.X • (δ n - x') = 0` using `by rw [smul_sub, hδ, h, sub_self]`. Conclude with `sub_eq_zero.1 (W₀.X_inj _ h0)`. Rewrite using `[this]`. Conclude with `hx'`. Use `set R : ℤ_[ℓ][X] := ∏ j ∈ JSet jumps M, (X - C (c j)) with hRdef`.

Establish `hR : ∀ y, W₀.QInv y → aeval δ (X * R) y ∈ W₀.N`. Introduce `y hy`. Take `⟨R', hR'⟩` from `prod_eig_dvd jumps M (fun j => (X - C (c j)))`. Simplify using `only [hc0, map_zero, sub_zero] at hR'`. Rewrite using `[hRdef, hR', mul_comm, map_mul, Module.End.mul_apply]`.

Conclude with `aeval_mem _ δ hstab R' _ (hSemi y hy)`. Establish `hprod` using `prod_sub_one_dvd ℓ hℓ u₁ hv₁ a`. Establish `hZu : ∀ y, W₀.QInv y → (∏ i ∈ Finset.Icc 1 a, (1 - (u₁ : ℤ_[ℓ]) ^ i)) • y ∈ W₀.N → y ∈ W₀.N`. Introduce `y hy h`. Take `⟨w, hw⟩` from `hprod`.

Apply `noTors_pow W₀ hZ _ y hy` to reduce the goal to its premises. Rewrite using `[hw, mul_comm, mul_smul]`. Conclude with `W₀.smulO_mem w h`. Establish `hgr : ∀ i, 1 ≤ i → i ≤ a → ∀ n ∈ W₀.N, ∃ n' ∈ W₀.N, W₀.γ (B.X ^ i • n) = (u₁ : ℤ_[ℓ]) ^ i • (B.X ^ i • n) + B.X ^ (i + 1) • n'`. Introduce `i _ _ n hn`.

Take `⟨n', hn', h⟩` from `gammaGradedStep_holds ℤ_[ℓ] A B M D₀ W₀ (u₁ : ℤ_[ℓ]) hγX₁ i n hn`. Conclude with `⟨n', hn', by rw [← h]; abel⟩`. Establish `hL0` using `lift_wach ℤ_[ℓ] A B M D₀ D₁ D₂ W₀ W₁ W₂ S eW hCK hRS δ R a (ℓ - 1) (u₁ : ℤ_[ℓ]) hPhi (by omega) hδ hR (by rw [hp]; exact hZ) hZu hgr h1`. Establish `hcj : ∀ j ∈ JSet jumps M, (0 - c j) ∣ (ℓ : ℤ_[ℓ]) ^ padicValInt ℓ j`. Introduce `j hj`.

Establish `hj0 : j ≠ 0` using `fun h => zero_notMem_JSet jumps M (h ▸ hj)`. Take `⟨hne, hval⟩` from `Formalism.WindowSums.arc_ZpowVal ℓ u 1 le_rfl (fun h => absurd h hℓ) hv (-j) (neg_ne_zero.2 hj0)`. Establish `hneg : padicValInt ℓ (-j) = padicValInt ℓ j` using `by simp [padicValInt]`. Rewrite `hval` using `[hneg]`. Take `⟨w, hw⟩` from `dvd_pow_of_val hne hval`.

Use `⟨w, ?_⟩` and prove the remaining obligations. Apply `mul_left_cancel₀ hℓ0` to reduce the goal to its premises. Establish `e : (ℓ : ℤ_[ℓ]) * ((0 - c j) * w) = (((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) * w`. Use `hc j` as an intermediate fact. Take the linear combination `(-w) * this`.

Rewrite using `[e, ← hw, pow_add, pow_one]`. Establish `hR0 : R.eval 0 ∣ (ℓ : ℤ_[ℓ]) ^ (∑ j ∈ JSet jumps M, padicValInt ℓ j)`. Rewrite using `[hRdef, eval_prod, ← Finset.prod_pow_eq_pow_sum]`. Apply `Finset.prod_dvd_prod_of_dvd` to reduce the goal to its premises. Introduce `j hj`.

Simplify using `using hcj j hj`. Establish `hfac : a + padicValNat ℓ a.factorial ≤ aStar ℓ M + padicValNat ℓ (aStar ℓ M).factorial`. Establish `: padicValNat ℓ (a + 1).factorial = padicValNat ℓ (a + 1) + padicValNat ℓ a.factorial`. Rewrite using `[Nat.factorial_succ, padicValNat.mul (Nat.succ_ne_zero a) (Nat.factorial_ne_zero _)]`. Simplify using `only [aStar, ← ha]`.

Use linear arithmetic over natural numbers and integers. Establish `hL : Lifts S ((ℓ : ℤ_[ℓ]) ^ (eW + eUA ℓ M (JSet jumps M)))`. Use `lifts_of_dvd S ?_ hL0` and prove the remaining obligations. Rewrite using `[hp, pow_add]`. Apply `mul_dvd_mul_left` to reduce the goal to its premises.

Simplify using `only [eUA]`. Rewrite using `[add_assoc, pow_add]`. Conclude with `mul_dvd_mul hR0 (dvd_trans hprod (pow_dvd_pow _ hfac))`. Introduce `κ hκ`. Take `⟨κ₁, hκ₁, h⟩` from `finiteClassesLift_holds ℤ_[ℓ] A B M D₀ D₁ D₂ W₀ W₁ W₂ S H₁ H₂ cl₁ cl₂ Hf₁ Hf₂ g eW _ hNat hC1 ⟨hC2, by rw [hp]; exact hInt₂⟩ hL κ hκ`.

Use `⟨κ₁, hκ₁, ?_⟩` and prove the remaining obligations. Rewrite using `[h, hp, ← pow_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lift_exists_first_case : StatLiftA := by
  intro ℓ _ hℓ A _ _ B M u H jumps c hp hPhi hγX hv hc D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S δ
    H₁ H₂ _ _ _ _ cl₁ cl₂ Hf₁ Hf₂ g I _ hδ hQI hφI hRL hNT hXK hSemi hNat hC1 hC2 hInj hE1 hE2 hRO
  have hprime : ℓ.Prime := Fact.out
  have h3 : 3 ≤ ℓ := by have := hprime.two_le; omega
  set eW := eWA ℓ H with heW
  set u₁ : ℤ_[ℓ]ˣ := u ^ (ℓ - 1) with hu₁
  have hu₁c : (u₁ : ℤ_[ℓ]) = (u : ℤ_[ℓ]) ^ (ℓ - 1) := by rw [hu₁, Units.val_pow_eq_pow_val]
  have hγX₁ : B.GammaX (u₁ : ℤ_[ℓ]) := by rw [hu₁c]; exact hγX
  have hv₁ : PadicInt.valuation ((u₁ : ℤ_[ℓ]) - 1) = 1 := by
    rw [hu₁c, Formalism.ResultantValuation.powSubOneValuation ℓ hℓ (u : ℤ_[ℓ]) hv (ℓ - 1) (by omega),
      padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))]
  have hCK : CokerKilled S eW := by
    intro n hn
    rw [hp]
    exact homKillsA hℓ S.π u₁ hγX₁ H hv₁ hXK n hn
  have hInt₁ : ∀ κ ∈ Hf₁, ∃ pr : W₁.Z1, W₁.Cocycle (pr : D₁ × D₁).1 (pr : D₁ × D₁).2 ∧
      cl₁ pr = ((ℓ : ℤ_[ℓ]) ^ eW) • κ := by
    intro κ hκ
    obtain ⟨E, hEK, hED⟩ := hE1 κ hκ
    exact extension_class_is_cocycle ℓ A B M D₁ W₁ H₁ cl₁ κ E eW hED (homKillsA hℓ E.S.π u₁ hγX₁ H hv₁ hEK)
  have hInt₂ : ∀ κ ∈ Hf₂, ∃ pr : W₂.Z1, W₂.Cocycle (pr : D₂ × D₂).1 (pr : D₂ × D₂).2 ∧
      cl₂ pr = ((ℓ : ℤ_[ℓ]) ^ eW) • κ := by
    intro κ hκ
    obtain ⟨E, hEK, hED⟩ := hE2 κ hκ
    exact extension_class_is_cocycle ℓ A B M D₂ W₂ H₂ cl₂ κ E eW hED (homKillsA hℓ E.S.π u₁ hγX₁ H hv₁ hEK)
  have hRS : RatSurj S :=
    rational_points_map_surjective ℓ A B M D₀ D₁ D₂ W₀ W₁ W₂ S H₁ H₂ cl₁ cl₂ Hf₁ Hf₂ g eW hp hNat hC2 hInj hRO hInt₁
  set a := M / (ℓ - 1) with ha
  have hMa : M + 1 ≤ (ℓ - 1) * (a + 1) := Nat.lt_mul_div_succ M (by omega)
  have h1 := phi_map_surjective ℤ_[ℓ] A B M D₀ W₀ I (ℓ - 1) (a + 1) hPhi hMa hQI hφI
  have hZ := regulator_bound_for_l ℓ A B M D₀ W₀ hRL hNT
  have hℓ0 : (ℓ : ℤ_[ℓ]) ≠ 0 := by exact_mod_cast hprime.ne_zero
  have hc0 : c 0 = 0 := by
    have := hc 0
    simp only [neg_zero, zpow_zero, Units.val_one, sub_self, mul_eq_zero] at this
    exact this.resolve_left hℓ0
  have hstab : ∀ n ∈ W₀.N.restrictScalars ℤ_[ℓ], δ n ∈ W₀.N.restrictScalars ℤ_[ℓ] := by
    intro n hn
    obtain ⟨x', hx', h⟩ := W₀.γ_N n hn
    have : δ n = x' := by
      have h0 : B.X • (δ n - x') = 0 := by rw [smul_sub, hδ, h, sub_self]
      exact sub_eq_zero.1 (W₀.X_inj _ h0)
    rw [this]; exact hx'
  set R : ℤ_[ℓ][X] := ∏ j ∈ JSet jumps M, (X - C (c j)) with hRdef
  have hR : ∀ y, W₀.QInv y → aeval δ (X * R) y ∈ W₀.N := by
    intro y hy
    obtain ⟨R', hR'⟩ := prod_eig_dvd jumps M (fun j => (X - C (c j)))
    simp only [hc0, map_zero, sub_zero] at hR'
    rw [hRdef, hR', mul_comm, map_mul, Module.End.mul_apply]
    exact aeval_mem _ δ hstab R' _ (hSemi y hy)
  have hprod := prod_sub_one_dvd ℓ hℓ u₁ hv₁ a
  have hZu : ∀ y, W₀.QInv y → (∏ i ∈ Finset.Icc 1 a, (1 - (u₁ : ℤ_[ℓ]) ^ i)) • y ∈ W₀.N → y ∈ W₀.N := by
    intro y hy h
    obtain ⟨w, hw⟩ := hprod
    apply noTors_pow W₀ hZ _ y hy
    rw [hw, mul_comm, mul_smul]
    exact W₀.smulO_mem w h
  have hgr : ∀ i, 1 ≤ i → i ≤ a → ∀ n ∈ W₀.N, ∃ n' ∈ W₀.N,
      W₀.γ (B.X ^ i • n) = (u₁ : ℤ_[ℓ]) ^ i • (B.X ^ i • n) + B.X ^ (i + 1) • n' := by
    intro i _ _ n hn
    obtain ⟨n', hn', h⟩ := gammaGradedStep_holds ℤ_[ℓ] A B M D₀ W₀ (u₁ : ℤ_[ℓ]) hγX₁ i n hn
    exact ⟨n', hn', by rw [← h]; abel⟩
  have hL0 := lift_wach ℤ_[ℓ] A B M D₀ D₁ D₂ W₀ W₁ W₂ S eW hCK hRS δ R a (ℓ - 1) (u₁ : ℤ_[ℓ]) hPhi
    (by omega) hδ hR (by rw [hp]; exact hZ) hZu hgr h1

  have hcj : ∀ j ∈ JSet jumps M, (0 - c j) ∣ (ℓ : ℤ_[ℓ]) ^ padicValInt ℓ j := by
    intro j hj
    have hj0 : j ≠ 0 := fun h => zero_notMem_JSet jumps M (h ▸ hj)
    obtain ⟨hne, hval⟩ := Formalism.WindowSums.arc_ZpowVal ℓ u 1 le_rfl (fun h => absurd h hℓ) hv (-j)
      (neg_ne_zero.2 hj0)
    have hneg : padicValInt ℓ (-j) = padicValInt ℓ j := by simp [padicValInt]
    rw [hneg] at hval
    obtain ⟨w, hw⟩ := dvd_pow_of_val hne hval
    refine ⟨w, ?_⟩
    apply mul_left_cancel₀ hℓ0
    have e : (ℓ : ℤ_[ℓ]) * ((0 - c j) * w) = (((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) * w := by
      have := hc j
      linear_combination (-w) * this
    rw [e, ← hw, pow_add, pow_one]
  have hR0 : R.eval 0 ∣ (ℓ : ℤ_[ℓ]) ^ (∑ j ∈ JSet jumps M, padicValInt ℓ j) := by
    rw [hRdef, eval_prod, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_dvd_prod_of_dvd
    intro j hj
    simpa using hcj j hj
  have hfac : a + padicValNat ℓ a.factorial ≤ aStar ℓ M + padicValNat ℓ (aStar ℓ M).factorial := by
    have : padicValNat ℓ (a + 1).factorial = padicValNat ℓ (a + 1) + padicValNat ℓ a.factorial := by
      rw [Nat.factorial_succ, padicValNat.mul (Nat.succ_ne_zero a) (Nat.factorial_ne_zero _)]
    simp only [aStar, ← ha]
    omega
  have hL : Lifts S ((ℓ : ℤ_[ℓ]) ^ (eW + eUA ℓ M (JSet jumps M))) := by
    refine lifts_of_dvd S ?_ hL0
    rw [hp, pow_add]
    apply mul_dvd_mul_left
    simp only [eUA]
    rw [add_assoc, pow_add]
    exact mul_dvd_mul hR0 (dvd_trans hprod (pow_dvd_pow _ hfac))
  intro κ hκ
  obtain ⟨κ₁, hκ₁, h⟩ := finiteClassesLift_holds ℤ_[ℓ] A B M D₀ D₁ D₂ W₀ W₁ W₂ S H₁ H₂ cl₁ cl₂ Hf₁ Hf₂ g eW _
    hNat hC1 ⟨hC2, by rw [hp]; exact hInt₂⟩ hL κ hκ
  refine ⟨κ₁, hκ₁, ?_⟩
  rw [h, hp, ← pow_add]
  congr 2
  ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨lift_exists_second_case, lift_exists_first_case, lift_to_subgroup_exists⟩`.
-/
theorem etaleClosed_point_lifts_simple_roots_monic : StatLIFT := ⟨lift_exists_second_case, lift_exists_first_case, lift_to_subgroup_exists⟩

end Formalism.RepresentationBoundsCohomology.N2
