import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionPointsIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SubstFirstCoboundaryThree
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.EqZeroOfPowEqOne
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FinalS

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp torus)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog)
open MvPowerSeries

namespace InverseCommuting

section Letters

variable {d : ℕ} [NeZero d]

/- English proof (translation)
Establish `h2 : 2 ∣ d` using `hd.two_dvd`. Establish `hd2 : 2 ≤ d` using `Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne d)) h2`. Rewrite using `[ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_mod_of_dvd _ h2, Nat.mod_eq_of_lt hd2]`.
-/
lemma parity_add_one (hd : Even d) (s : ZMod d) : (s + 1).val % 2 = (s.val + 1) % 2 := by
  have h2 : 2 ∣ d := hd.two_dvd
  have hd2 : 2 ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne d)) h2
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_mod_of_dvd _ h2, Nat.mod_eq_of_lt hd2]

/- English proof (translation)
Establish `e : {s : ZMod d // s.val % 2 = 0} ≃ {s : ZMod d // ¬ s.val % 2 = 0}` using `(Equiv.addRight (1 : ZMod d)).subtypeEquiv (fun s => by`. Simplify using `only [Equiv.coe_addRight]`. Rewrite using `[parity_add_one hd]`. Use the proof step `omega)`. Establish `h1` using `Fintype.card_congr e`.

Establish `h2` using `Fintype.card_subtype_compl (fun s : ZMod d => s.val % 2 = 0)`. Establish `h3` using `Fintype.card_subtype_le (fun s : ZMod d => s.val % 2 = 0)`. Rewrite `h2`, `h3` using `[ZMod.card]`. Use linear arithmetic over natural numbers and integers.
-/
lemma card_even (hd : Even d) : 2 * Fintype.card {s : ZMod d // s.val % 2 = 0} = d := by
  have e : {s : ZMod d // s.val % 2 = 0} ≃ {s : ZMod d // ¬ s.val % 2 = 0} :=
    (Equiv.addRight (1 : ZMod d)).subtypeEquiv (fun s => by
      simp only [Equiv.coe_addRight]
      rw [parity_add_one hd]
      omega)
  have h1 := Fintype.card_congr e
  have h2 := Fintype.card_subtype_compl (fun s : ZMod d => s.val % 2 = 0)
  have h3 := Fintype.card_subtype_le (fun s : ZMod d => s.val % 2 = 0)
  rw [ZMod.card] at h2 h3
  omega

/- English proof (translation)
Rewrite using `[← Finset.sum_filter]`. Conclude with `Finset.sum_subtype _ (fun x => by simp) f`.
-/
lemma sum_even {M : Type} [AddCommMonoid M] (f : ZMod d → M) :
    (∑ s : ZMod d, if s.val % 2 = 0 then f s else 0) =
      ∑ s : {s : ZMod d // s.val % 2 = 0}, f s.1 := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun x => by simp) f

end Letters

/- English proof (translation)
Take `⟨m, rfl⟩ : ∃ m, k = 2 * m` from `⟨k / 2, by omega⟩`. Rewrite using `[Function.iterate_mul]`. Conclude with `Function.iterate_fixed h m`.
-/
lemma iter_even {α : Type} {f : α → α} {c : α} (h : f (f c) = c) {k : ℕ} (hk : k % 2 = 0) :
    f^[k] c = c := by
  obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m := ⟨k / 2, by omega⟩
  rw [Function.iterate_mul]
  exact Function.iterate_fixed h m

/- English proof (translation)
Take `⟨m, rfl⟩ : ∃ m, k = m + 1` from `⟨k - 1, by omega⟩`. Rewrite using `[Function.iterate_succ_apply]`. Conclude with `iter_even (by rw [h]) (by omega)`.
-/
lemma iter_odd {α : Type} {f : α → α} {c : α} (h : f (f c) = c) {k : ℕ} (hk : ¬ k % 2 = 0) :
    f^[k] c = f c := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [Function.iterate_succ_apply]
  exact iter_even (by rw [h]) (by omega)

section Sim

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {τ : Type}

/- English proof (translation)
The claim follows from `(Formalism.InvariantFactorPaths.G7.Top.simeqRules K τ).1 f`.
-/
lemma sim_refl (f : MvPowerSeries τ K) : Simeq f f := (Formalism.InvariantFactorPaths.G7.Top.simeqRules K τ).1 f

/- English proof (translation)
The claim follows from `(Formalism.InvariantFactorPaths.G7.Top.simeqRules K τ).2.1 f g h`.
-/
lemma sim_symm {f g : MvPowerSeries τ K} (h : Simeq f g) : Simeq g f :=
  (Formalism.InvariantFactorPaths.G7.Top.simeqRules K τ).2.1 f g h

/- English proof (translation)
The claim follows from `(Formalism.InvariantFactorPaths.G7.Top.simeqRules K τ).2.2.1 f g h h1 h2`.
-/
lemma sim_trans {f g h : MvPowerSeries τ K} (h1 : Simeq f g) (h2 : Simeq g h) : Simeq f h :=
  (Formalism.InvariantFactorPaths.G7.Top.simeqRules K τ).2.2.1 f g h h1 h2

/- English proof (translation)
The claim follows from `(Formalism.InvariantFactorPaths.G7.Top.simeqRules K τ).2.2.2.1 f g f' g' h1 h2`.
-/
lemma sim_add {f g f' g' : MvPowerSeries τ K} (h1 : Simeq f g) (h2 : Simeq f' g') :
    Simeq (f + f') (g + g') :=
  (Formalism.InvariantFactorPaths.G7.Top.simeqRules K τ).2.2.2.1 f g f' g' h1 h2

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using sim_refl (0 : MvPowerSeries τ K)`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Conclude with `sim_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
lemma sim_sum {α : Type} (s : Finset α) (f g : α → MvPowerSeries τ K)
    (h : ∀ i ∈ s, Simeq (f i) (g i)) : Simeq (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sim_refl (0 : MvPowerSeries τ K)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact sim_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Use `⟨by simpa using h0, ?_⟩` and prove the remaining obligations. Establish `h` using `hφ 0 0 h0 h0`. Rewrite `h` using `[add_zero]`.

Establish `h' : Simeq (0 : MvPowerSeries τ K) (φ 0)`. Unfold `Simeq at h ⊢`. Establish `e : (0 : MvPowerSeries τ K) - φ 0 = φ 0 - (φ 0 + φ 0)` using `by ring`. Rewrite using `[e]`. Conclude with `h`.

Simplify using `using sim_symm h'`. Consider the case `insert a s ha ih`. Take `⟨ih1, ih2⟩` from `ih fun i hi => hg i (Finset.mem_insert_of_mem hi)`. Establish `hga` using `hg a (Finset.mem_insert_self a s)`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`.

Conclude with `⟨hadd _ _ hga ih1, sim_trans (hφ _ _ hga ih1) (sim_add (sim_refl _) ih2)⟩`.
-/
lemma sum_rule {P : MvPowerSeries τ K → Prop} (h0 : P 0) (hadd : ∀ g g', P g → P g' → P (g + g'))
    (φ : MvPowerSeries τ K → MvPowerSeries τ K)
    (hφ : ∀ g g', P g → P g' → Simeq (φ (g + g')) (φ g + φ g'))
    {α : Type} (s : Finset α) (g : α → MvPowerSeries τ K) (hg : ∀ i ∈ s, P (g i)) :
    P (∑ i ∈ s, g i) ∧ Simeq (φ (∑ i ∈ s, g i)) (∑ i ∈ s, φ (g i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using h0, ?_⟩
    have h := hφ 0 0 h0 h0
    rw [add_zero] at h
    have h' : Simeq (0 : MvPowerSeries τ K) (φ 0) := by
      unfold Simeq at h ⊢
      have e : (0 : MvPowerSeries τ K) - φ 0 = φ 0 - (φ 0 + φ 0) := by ring
      rw [e]
      exact h
    simpa using sim_symm h'
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hga := hg a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨hadd _ _ hga ih1, sim_trans (hφ _ _ hga ih1) (sim_add (sim_refl _) ih2)⟩

end Sim

section Lin

variable {K : Type} [NormedField K] {τ : Type} {d : ℕ} [NeZero d]

/- English proof (translation)
Unfold `linEL`. Repeatedly rewrite using `[Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Distinguish the cases in `hs : s.val % 2 = 0`.

Simplify using `only [if_pos hs]`. Rewrite using `[← RingHom.coe_pow, map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, RingHom.coe_pow, iter_even (ha i) hs, map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [if_neg hs]`. Simplify using the standard rewrite rules.
-/
lemma linEL_sum (σ : K →+* K) {ι : Type} [Fintype ι] (a y : ι → K)
    (ha : ∀ i, σ (σ (a i)) = a i) (L : ZMod d → MvPowerSeries τ K) :
    linEL σ (∑ i, a i * y i) L = ∑ i, C (a i) * linEL σ (y i) L := by
  unfold linEL
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : s.val % 2 = 0
  · simp only [if_pos hs]
    rw [← RingHom.coe_pow, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, RingHom.coe_pow, iter_even (ha i) hs, map_mul]
    ring
  · simp only [if_neg hs]
    simp

/- English proof (translation)
Unfold `linOL`. Repeatedly rewrite using `[Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Distinguish the cases in `hs : s.val % 2 = 0`.

Simplify using `only [if_pos hs]`. Simplify using the standard rewrite rules. Simplify using `only [if_neg hs]`. Rewrite using `[← RingHom.coe_pow, map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, RingHom.coe_pow, iter_odd (ha i) hs, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma linOL_sum (σ : K →+* K) {ι : Type} [Fintype ι] (a y : ι → K)
    (ha : ∀ i, σ (σ (a i)) = a i) (L : ZMod d → MvPowerSeries τ K) :
    linOL σ (∑ i, a i * y i) L = ∑ i, C (σ (a i)) * linOL σ (y i) L := by
  unfold linOL
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : s.val % 2 = 0
  · simp only [if_pos hs]
    simp
  · simp only [if_neg hs]
    rw [← RingHom.coe_pow, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, RingHom.coe_pow, iter_odd (ha i) hs, map_mul]
    ring

end Lin
end InverseCommuting

open InverseCommuting

/- English proof (translation)
Introduce `K _ d _ σ hd ι _ _ om oms hfix hT x hx`. Take `⟨hcard, hdual⟩` from `hT`. Set `E` to `{s : ZMod d // s.val % 2 = 0}`. Set `A : Matrix ι E K` to `fun r s => σ^[s.1.val] (om r)`. Set `B : Matrix E ι K` to `fun s r => σ^[s.1.val] (oms r)`.

Establish `hAB : A * B = 1`. Use extensionality with `r r'`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply, ← hdual r r', sum_even]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Conclude with `(iterate_map_mul σ _ _ _).symm`.

Establish `hce : Fintype.card ι = Fintype.card E`. Establish `h` using `card_even (d := d) hd`. Use `show Fintype.card ι = Fintype.card {s : ZMod d // s.val % 2 = 0}`. Use linear arithmetic over natural numbers and integers. Establish `hBA : B * A = 1` using `(Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hce)).1 hAB`.

Establish `hBA' : ∀ s s' : E, ∑ r, σ^[s.1.val] (oms r) * σ^[s'.1.val] (om r) = if s = s' then 1 else 0`. Introduce `s s'`. Use `congrFun (congrFun hBA s) s'` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Matrix.one_apply]`. Conclude with `this`.

Set `z : E` to `⟨0, by simp⟩`. Establish `hz : ∀ y : K, σ^[z.1.val] y = y`. Introduce `y`. Establish `: z.1.val = 0` using `ZMod.val_zero`. Rewrite using `[this]`.

Both sides reduce to the same expression. Use `⟨fun r r' => ?_, fun r => ?_, fun r' => ?_⟩` and prove the remaining obligations. Establish `hc : σ^[d] (x * oms r * om r') = x * oms r * om r'`. Rewrite using `[iterate_map_mul, iterate_map_mul, hx, (hfix r).2, (hfix r').1]`. Rewrite using `[map_sum, map_sum]`.

Rewrite using `[← (Equiv.subRight (2 : ZMod d)).sum_comp (fun s : ZMod d => σ (σ (if s.val % 2 = 0 then σ^[s.val] (x * oms r * om r') else 0)))]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Simplify using `only [Equiv.subRight_apply]`. Rewrite using `[KernelCokernelKilling.parity_sub_two hd s]`. Use `split_ifs`.

Conclude with `KernelCokernelKilling.iter_sub_two σ hc s`. Simplify using the standard rewrite rules. Repeatedly rewrite using `[sum_even, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Establish `: ∀ s : E, ∑ r' : ι, σ^[s.1.val] (x * oms r * om r') * oms r' = σ^[s.1.val] (x * oms r) * if z = s then 1 else 0`.

Introduce `s`. Rewrite using `[← hBA' z s, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun r' _ => ?_` and prove the remaining obligations. Rewrite using `[hz, iterate_map_mul σ _ (x * oms r)]`. Expand and normalize the polynomial expressions, which then agree.

Repeatedly rewrite using `[this]`. Simplify using `[hz]`. Repeatedly rewrite using `[sum_even, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Establish `: ∀ s : E, ∑ r : ι, σ^[s.1.val] (x * oms r * om r') * om r = σ^[s.1.val] (x * om r') * if s = z then 1 else 0`.

Introduce `s`. Rewrite using `[← hBA' s z, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[hz, iterate_map_mul, iterate_map_mul, iterate_map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Repeatedly rewrite using `[this]`. Simplify using `[hz]`.
-/
theorem dual_expansion : DualExpand := by
  intro K _ d _ σ hd ι _ _ om oms hfix hT x hx
  obtain ⟨hcard, hdual⟩ := hT
  let E := {s : ZMod d // s.val % 2 = 0}
  let A : Matrix ι E K := fun r s => σ^[s.1.val] (om r)
  let B : Matrix E ι K := fun s r => σ^[s.1.val] (oms r)
  have hAB : A * B = 1 := by
    ext r r'
    rw [Matrix.mul_apply, Matrix.one_apply, ← hdual r r', sum_even]
    refine Finset.sum_congr rfl fun s _ => ?_
    exact (iterate_map_mul σ _ _ _).symm
  have hce : Fintype.card ι = Fintype.card E := by
    have h := card_even (d := d) hd
    show Fintype.card ι = Fintype.card {s : ZMod d // s.val % 2 = 0}
    omega
  have hBA : B * A = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hce)).1 hAB
  have hBA' : ∀ s s' : E, ∑ r, σ^[s.1.val] (oms r) * σ^[s'.1.val] (om r) =
      if s = s' then 1 else 0 := by
    intro s s'
    have := congrFun (congrFun hBA s) s'
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    exact this
  let z : E := ⟨0, by simp⟩
  have hz : ∀ y : K, σ^[z.1.val] y = y := by
    intro y
    have : z.1.val = 0 := ZMod.val_zero
    rw [this]
    rfl
  refine ⟨fun r r' => ?_, fun r => ?_, fun r' => ?_⟩
  · have hc : σ^[d] (x * oms r * om r') = x * oms r * om r' := by
      rw [iterate_map_mul, iterate_map_mul, hx, (hfix r).2, (hfix r').1]
    rw [map_sum, map_sum]
    rw [← (Equiv.subRight (2 : ZMod d)).sum_comp
      (fun s : ZMod d => σ (σ (if s.val % 2 = 0 then σ^[s.val] (x * oms r * om r') else 0)))]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Equiv.subRight_apply]
    rw [KernelCokernelKilling.parity_sub_two hd s]
    split_ifs
    · exact KernelCokernelKilling.iter_sub_two σ hc s
    · simp
  · simp_rw [sum_even, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ s : E, ∑ r' : ι, σ^[s.1.val] (x * oms r * om r') * oms r' =
        σ^[s.1.val] (x * oms r) * if z = s then 1 else 0 := by
      intro s
      rw [← hBA' z s, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r' _ => ?_
      rw [hz, iterate_map_mul σ _ (x * oms r)]
      ring
    simp_rw [this]
    simp [hz]
  · simp_rw [sum_even, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ s : E, ∑ r : ι, σ^[s.1.val] (x * oms r * om r') * om r =
        σ^[s.1.val] (x * om r') * if s = z then 1 else 0 := by
      intro s
      rw [← hBA' s z, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [hz, iterate_map_mul, iterate_map_mul, iterate_map_mul]
      ring
    simp_rw [this]
    simp [hz]

/- English proof (translation)
Introduce `hPR hST hTT hTS hSI hIC hDE hFS K _ _ _ l d _ σ hU hd2 hd F hF be0 hF1 hF2 ι _ _ om oms hOw hT u hu τ _ L hL`. Establish `hl2 : 2 ≤ l` using `hU.1.two_le`. Establish `hσ` using `(hFS K l σ hU).2`. Establish `h1 : 1 < l ^ d` using `Nat.one_lt_pow (by omega) hU.1.one_lt`. Establish `hN : l ^ d - 1 ≠ 0` using `by omega`.

Establish `hu0 : u ≠ 0`. Introduce `h`. Rewrite `hu` using `[h, zero_pow hN]`. Conclude with `zero_ne_one hu`. Establish `hnu : ‖u‖ = 1`.

Establish `h : ‖u‖ ^ (l ^ d - 1) = 1` using `by rw [← norm_pow, hu, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg u) hN).1 h`. Establish `hσu : σ u = u ^ l` using `hTS K l d σ hU (by omega) u hu`. Establish `hiter : ∀ k, σ^[k] u = u ^ (l ^ k)`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [Function.iterate_succ_apply', ih, map_pow, hσu, ← pow_mul, pow_succ']`. Establish `hud : σ^[d] u = u`. Establish `e : l ^ d = (l ^ d - 1) + 1` using `by omega`.

Rewrite using `[hiter, e, pow_succ, hu, one_mul]`. Establish `hui : σ^[d] u⁻¹ = u⁻¹`. Rewrite using `[← RingHom.coe_pow, map_inv₀, RingHom.coe_pow, hud]`. Establish `hnui : ‖u⁻¹‖ = 1` using `by rw [norm_inv, hnu, inv_one]`. Take `⟨hPR1, hPR2, hPR3⟩` from `hPR K l σ hU F hF be0 hF1 τ`.

Establish `hPR3` using `hPR3 hF2`. Take `⟨hI0, hIadd, hImul⟩` from `hIC K l σ τ`. Take `⟨hc1, hc2, hc3⟩` from `hDE K d σ hd ι om oms hOw.2 hT u hud`. Choose the witnesses or unpack the hypotheses as in `⟨c, hcn, hc1, hc2, hc3⟩ : ∃ c : ι → ι → K, (∀ r r', ‖c r r'‖ ≤ 1) ∧ (∀ r r', σ (σ (c r r')) = c r r') ∧ (∀ r, u * oms r = ∑ r', c r r' * oms r') ∧ (∀ r', u * om r' = ∑ r, c r r' * om r) := by`. Use `⟨fun r r' => ∑ s : ZMod d, if s.val % 2 = 0 then σ^[s.val] (u * oms r * om r') else 0, ?_, hc1, hc2, hc3⟩` and prove the remaining obligations.

Introduce `r r'`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun s _ => ?_` and prove the remaining obligations. Use `split_ifs`. Use `KernelCokernelKilling.norm_iter hσ ?_ _` and prove the remaining obligations. Rewrite using `[norm_mul, norm_mul, hnu, one_mul]`.

Conclude with `mul_le_one₀ (hOw.1 r).2 (norm_nonneg _) (hOw.1 r').1`. Simplify using the standard rewrite rules. Establish `hA : ∀ r, IP l σ (linEL σ (oms r) L)` using `fun r => (hSI K l d σ hU hd τ L hL (oms r) (hOw.1 r).2 (hOw.2 r).2).1`. Establish `hBu : ∀ r, IP l σ (linOL σ (u⁻¹ * om r) L)` using `fun r => (hSI K l d σ hU hd τ L hL (u⁻¹ * om r) (by rw [norm_mul, hnui, one_mul]; exact (hOw.1 r).1) (by rw [iterate_map_mul, hui, (hOw.2 r).1])).2`. Establish `hAu : ∀ r, linEL σ (u * oms r) L = ∑ r', C (c r r') * linEL σ (oms r') L`.

Introduce `r`. Rewrite using `[hc2 r, linEL_sum σ _ _ (hc1 r) L]`. Establish `hB : ∀ r', linOL σ (om r') L = ∑ r, C (σ (c r r')) * linOL σ (u⁻¹ * om r) L`. Introduce `r'`. Rewrite using `[← linOL_sum σ (fun r => c r r') (fun r => u⁻¹ * om r) (fun r => hc1 r r') L]`.

Use `congr 1`. Establish `e : ∑ r, c r r' * (u⁻¹ * om r) = u⁻¹ * ∑ r, c r r' * om r`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`. Rewrite using `[e, ← hc3 r', inv_mul_cancel_left₀ hu0]`.

Establish `hL0 : ∀ s, constantCoeff (L s) = 0` using `fun s => (hL s).1`. Rewrite using `[hTT K l d σ hl2 be0 ι om oms u hu0 hσu, hST K l d σ hl2 be0 ι _ _ τ L hL0, hST K l d σ hl2 be0 ι om oms τ L hL0]`. Use `show Simeq (∑ r, subst ![linEL σ (u * oms r) L, linOL σ (u⁻¹ * om r) L] (addC l be0)) (∑ r, subst ![linEL σ (oms r) L, linOL σ (om r) L] (addC l be0))`. Establish `s1 : ∀ r, Simeq (subst ![linEL σ (u * oms r) L, linOL σ (u⁻¹ * om r) L] (addC l be0)) (∑ r', subst ![C (c r r') * linEL σ (oms r') L, linOL σ (u⁻¹ * om r) L] (addC l be0))`. Introduce `r`.

Rewrite using `[hAu r]`. Conclude with `(sum_rule hI0 hIadd (fun G => subst ![G, linOL σ (u⁻¹ * om r) L] (addC l be0)) (fun g g' hg hg' => hPR1 g g' _ hg hg' (hBu r)) Finset.univ _ (fun r' _ => hImul _ _ (hcn r r') (hc1 r r') (hA r'))).2`. Establish `s2 : ∀ r r', Simeq (subst ![C (c r r') * linEL σ (oms r') L, linOL σ (u⁻¹ * om r) L] (addC l be0)) (subst ![linEL σ (oms r') L, C (σ (c r r')) * linOL σ (u⁻¹ * om r) L] (addC l be0))` using `fun r r' => hPR3 _ _ _ (hcn r r') (hc1 r r') (hA r') (hBu r)`. Establish `s3 : ∀ r', Simeq (subst ![linEL σ (oms r') L, linOL σ (om r') L] (addC l be0)) (∑ r, subst ![linEL σ (oms r') L, C (σ (c r r')) * linOL σ (u⁻¹ * om r) L] (addC l be0))`. Introduce `r'`.

Rewrite using `[hB r']`. Conclude with `(sum_rule hI0 hIadd (fun H => subst ![linEL σ (oms r') L, H] (addC l be0)) (fun g g' hg hg' => hPR2 _ g g' (hA r') hg hg') Finset.univ _ (fun r _ => hImul _ _ (hσ _ (hcn r r')) (by rw [hc1]) (hBu r))).2`. Use `sim_trans (sim_sum _ _ _ fun r _ => s1 r) ?_` and prove the remaining obligations. Use `sim_trans (sim_sum _ _ _ fun r _ => sim_sum _ _ _ fun r' _ => s2 r r') ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.

Conclude with `sim_symm (sim_sum _ _ _ fun r' _ => s3 r')`.
-/
theorem TilInvariantL_of : PairRules → SubstTil → TorusTil → TeichSigma → ShiftIP → IPClosure →
    DualExpand → FrobSq → TilInvariantL := by
  intro hPR hST hTT hTS hSI hIC hDE hFS K _ _ _ l d _ σ hU hd2 hd F hF be0 hF1 hF2 ι _ _ om oms
    hOw hT u hu τ _ L hL
  have hl2 : 2 ≤ l := hU.1.two_le
  have hσ := (hFS K l σ hU).2
  have h1 : 1 < l ^ d := Nat.one_lt_pow (by omega) hU.1.one_lt
  have hN : l ^ d - 1 ≠ 0 := by omega
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, zero_pow hN] at hu
    exact zero_ne_one hu
  have hnu : ‖u‖ = 1 := by
    have h : ‖u‖ ^ (l ^ d - 1) = 1 := by rw [← norm_pow, hu, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg u) hN).1 h
  have hσu : σ u = u ^ l := hTS K l d σ hU (by omega) u hu
  have hiter : ∀ k, σ^[k] u = u ^ (l ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply', ih, map_pow, hσu, ← pow_mul, pow_succ']
  have hud : σ^[d] u = u := by
    have e : l ^ d = (l ^ d - 1) + 1 := by omega
    rw [hiter, e, pow_succ, hu, one_mul]
  have hui : σ^[d] u⁻¹ = u⁻¹ := by
    rw [← RingHom.coe_pow, map_inv₀, RingHom.coe_pow, hud]
  have hnui : ‖u⁻¹‖ = 1 := by rw [norm_inv, hnu, inv_one]
  obtain ⟨hPR1, hPR2, hPR3⟩ := hPR K l σ hU F hF be0 hF1 τ
  have hPR3 := hPR3 hF2
  obtain ⟨hI0, hIadd, hImul⟩ := hIC K l σ τ
  obtain ⟨hc1, hc2, hc3⟩ := hDE K d σ hd ι om oms hOw.2 hT u hud
  obtain ⟨c, hcn, hc1, hc2, hc3⟩ : ∃ c : ι → ι → K, (∀ r r', ‖c r r'‖ ≤ 1) ∧
      (∀ r r', σ (σ (c r r')) = c r r') ∧ (∀ r, u * oms r = ∑ r', c r r' * oms r') ∧
      (∀ r', u * om r' = ∑ r, c r r' * om r) := by
    refine ⟨fun r r' => ∑ s : ZMod d, if s.val % 2 = 0 then σ^[s.val] (u * oms r * om r') else 0,
      ?_, hc1, hc2, hc3⟩
    intro r r'
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun s _ => ?_
    split_ifs
    · refine KernelCokernelKilling.norm_iter hσ ?_ _
      rw [norm_mul, norm_mul, hnu, one_mul]
      exact mul_le_one₀ (hOw.1 r).2 (norm_nonneg _) (hOw.1 r').1
    · simp
  have hA : ∀ r, IP l σ (linEL σ (oms r) L) := fun r =>
    (hSI K l d σ hU hd τ L hL (oms r) (hOw.1 r).2 (hOw.2 r).2).1
  have hBu : ∀ r, IP l σ (linOL σ (u⁻¹ * om r) L) := fun r =>
    (hSI K l d σ hU hd τ L hL (u⁻¹ * om r)
      (by rw [norm_mul, hnui, one_mul]; exact (hOw.1 r).1)
      (by rw [iterate_map_mul, hui, (hOw.2 r).1])).2
  have hAu : ∀ r, linEL σ (u * oms r) L = ∑ r', C (c r r') * linEL σ (oms r') L := by
    intro r
    rw [hc2 r, linEL_sum σ _ _ (hc1 r) L]
  have hB : ∀ r', linOL σ (om r') L = ∑ r, C (σ (c r r')) * linOL σ (u⁻¹ * om r) L := by
    intro r'
    rw [← linOL_sum σ (fun r => c r r') (fun r => u⁻¹ * om r) (fun r => hc1 r r') L]
    congr 1
    have e : ∑ r, c r r' * (u⁻¹ * om r) = u⁻¹ * ∑ r, c r r' * om r := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e, ← hc3 r', inv_mul_cancel_left₀ hu0]
  have hL0 : ∀ s, constantCoeff (L s) = 0 := fun s => (hL s).1
  rw [hTT K l d σ hl2 be0 ι om oms u hu0 hσu, hST K l d σ hl2 be0 ι _ _ τ L hL0,
    hST K l d σ hl2 be0 ι om oms τ L hL0]
  show Simeq (∑ r, subst ![linEL σ (u * oms r) L, linOL σ (u⁻¹ * om r) L] (addC l be0))
    (∑ r, subst ![linEL σ (oms r) L, linOL σ (om r) L] (addC l be0))
  have s1 : ∀ r, Simeq (subst ![linEL σ (u * oms r) L, linOL σ (u⁻¹ * om r) L] (addC l be0))
      (∑ r', subst ![C (c r r') * linEL σ (oms r') L, linOL σ (u⁻¹ * om r) L] (addC l be0)) := by
    intro r
    rw [hAu r]
    exact (sum_rule hI0 hIadd (fun G => subst ![G, linOL σ (u⁻¹ * om r) L] (addC l be0))
      (fun g g' hg hg' => hPR1 g g' _ hg hg' (hBu r)) Finset.univ _
      (fun r' _ => hImul _ _ (hcn r r') (hc1 r r') (hA r'))).2
  have s2 : ∀ r r',
      Simeq (subst ![C (c r r') * linEL σ (oms r') L, linOL σ (u⁻¹ * om r) L] (addC l be0))
        (subst ![linEL σ (oms r') L, C (σ (c r r')) * linOL σ (u⁻¹ * om r) L] (addC l be0)) :=
    fun r r' => hPR3 _ _ _ (hcn r r') (hc1 r r') (hA r') (hBu r)
  have s3 : ∀ r', Simeq (subst ![linEL σ (oms r') L, linOL σ (om r') L] (addC l be0))
      (∑ r, subst ![linEL σ (oms r') L, C (σ (c r r')) * linOL σ (u⁻¹ * om r) L]
        (addC l be0)) := by
    intro r'
    rw [hB r']
    exact (sum_rule hI0 hIadd (fun H => subst ![linEL σ (oms r') L, H] (addC l be0))
      (fun g g' hg hg' => hPR2 _ g g' (hA r') hg hg') Finset.univ _
      (fun r _ => hImul _ _ (hσ _ (hcn r r')) (by rw [hc1]) (hBu r))).2
  refine sim_trans (sim_sum _ _ _ fun r _ => s1 r) ?_
  refine sim_trans (sim_sum _ _ _ fun r _ => sim_sum _ _ _ fun r' _ => s2 r r') ?_
  rw [Finset.sum_comm]
  exact sim_symm (sim_sum _ _ _ fun r' _ => s3 r')

/- English proof (translation)
Introduce `hTI K _ _ _ l d _ σ hU hd2 hd F hF be0 hF1 hF2 ι _ _ om oms hOw hT ζ hζ τ _ L hL`. Establish `hLs : HasSubst L` using `hasSubst_of_constantCoeff_zero fun s => (hL s).1`. Establish `h1 : 1 < l ^ d` using `Nat.one_lt_pow (by omega) hU.1.one_lt`. Establish `hN0 : l ^ d - 1 ≠ 0` using `by omega`. Establish `hNK : ((l ^ d - 1 : ℕ) : K) ≠ 0` using `Nat.cast_ne_zero.2 hN0`.

Establish `hdiv : ¬ l ∣ l ^ d - 1`. Introduce `h`. Establish `h2 : l ∣ (l ^ d - 1) + 1`. Rewrite using `[show (l ^ d - 1) + 1 = l ^ d by omega]`. Conclude with `dvd_pow_self l (by omega)`.

Conclude with `hU.1.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 h2))`. Establish `hk : ∀ k : ℕ, Simeq (subst L (subst (torus l (ζ ^ k)) (beTil (d` using `d) l σ be0 om oms)) -`. Substitute `L (beTil (d := d) l σ be0 om oms)) 0 := by` using the available equality. Introduce `k`. Establish `h` using `hTI K l d σ hU hd2 hd F hF be0 hF1 hF2 ι om oms hOw hT (ζ ^ k) (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) τ L hL`.

Unfold `Simeq at h ⊢`. Rewrite using `[sub_zero]` and apply the resulting hypothesis. Establish `hsum` using `sim_sum (Finset.range (l ^ d - 1)) _ _ fun k _ => hk k`. Rewrite `hsum` using `[Finset.sum_const_zero]`. Establish `hlam` using `Formalism.InvariantFactorPaths.G7.Top.lamModule K τ l σ hU.1 hU.2.2.1 hU.2.2.2.2 _ (l ^ d - 1) hdiv hsum`.

Establish `e0 : (C (((l ^ d - 1 : ℕ) : K)⁻¹) : MvPowerSeries τ K) * ((l ^ d - 1) • subst L (beTil (d` using `d) l σ be0 om oms)) =`. Substitute `L (beTil (d := d) l σ be0 om oms) := by` using the available equality. Rewrite using `[nsmul_eq_mul, ← mul_assoc, ← map_natCast (C : K →+* MvPowerSeries τ K), ← map_mul, inv_mul_cancel₀ hNK, map_one, one_mul]`. Establish `e : subst L (beMean (d` using `d) l σ be0 om oms ζ) - subst L (beTil (d := d) l σ be0 om oms) = C (((l ^ d - 1 : ℕ) : K)⁻¹) * ∑ k ∈ Finset.range (l ^ d - 1), (subst L (subst (torus l (ζ ^ k)) (beTil (d := d) l σ be0 om oms)) -`. Substitute `L (beTil (d := d) l σ be0 om oms)) - 0 := by` using the available equality.

Unfold `beMean`. Rewrite using `[subst_mul hLs, subst_C, Pair.subst_sum hLs, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, mul_sub, sub_zero, e0]`. Unfold `Simeq`. Rewrite using `[e]`. Conclude with `hlam`.
-/
theorem MeanSimeqL_of : TilInvariantL → MeanSimeqL := by
  intro hTI K _ _ _ l d _ σ hU hd2 hd F hF be0 hF1 hF2 ι _ _ om oms hOw hT ζ hζ τ _ L hL
  have hLs : HasSubst L := hasSubst_of_constantCoeff_zero fun s => (hL s).1
  have h1 : 1 < l ^ d := Nat.one_lt_pow (by omega) hU.1.one_lt
  have hN0 : l ^ d - 1 ≠ 0 := by omega
  have hNK : ((l ^ d - 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 hN0
  have hdiv : ¬ l ∣ l ^ d - 1 := by
    intro h
    have h2 : l ∣ (l ^ d - 1) + 1 := by
      rw [show (l ^ d - 1) + 1 = l ^ d by omega]
      exact dvd_pow_self l (by omega)
    exact hU.1.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 h2))
  have hk : ∀ k : ℕ, Simeq (subst L (subst (torus l (ζ ^ k)) (beTil (d := d) l σ be0 om oms)) -
      subst L (beTil (d := d) l σ be0 om oms)) 0 := by
    intro k
    have h := hTI K l d σ hU hd2 hd F hF be0 hF1 hF2 ι om oms hOw hT (ζ ^ k)
      (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) τ L hL
    unfold Simeq at h ⊢
    rwa [sub_zero]
  have hsum := sim_sum (Finset.range (l ^ d - 1)) _ _ fun k _ => hk k
  rw [Finset.sum_const_zero] at hsum
  have hlam := Formalism.InvariantFactorPaths.G7.Top.lamModule K τ l σ hU.1 hU.2.2.1 hU.2.2.2.2 _ (l ^ d - 1) hdiv hsum
  have e0 : (C (((l ^ d - 1 : ℕ) : K)⁻¹) : MvPowerSeries τ K) *
      ((l ^ d - 1) • subst L (beTil (d := d) l σ be0 om oms)) =
      subst L (beTil (d := d) l σ be0 om oms) := by
    rw [nsmul_eq_mul, ← mul_assoc, ← map_natCast (C : K →+* MvPowerSeries τ K), ← map_mul,
      inv_mul_cancel₀ hNK, map_one, one_mul]
  have e : subst L (beMean (d := d) l σ be0 om oms ζ) - subst L (beTil (d := d) l σ be0 om oms) =
      C (((l ^ d - 1 : ℕ) : K)⁻¹) * ∑ k ∈ Finset.range (l ^ d - 1),
        (subst L (subst (torus l (ζ ^ k)) (beTil (d := d) l σ be0 om oms)) -
          subst L (beTil (d := d) l σ be0 om oms)) - 0 := by
    unfold beMean
    rw [subst_mul hLs, subst_C, Pair.subst_sum hLs, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, mul_sub, sub_zero, e0]
  unfold Simeq
  rw [e]
  exact hlam

/- English proof (translation)
Introduce `hTI hLS K _ _ _ l d _ σ hU hd2 hd F hF be0 hF1 hF2 ι _ _ om oms hOw hT u hu`. Conclude with `hTI K l d σ hU hd2 hd F hF be0 hF1 hF2 ι om oms hOw hT u hu (ZMod d) (letLog l) (hLS K l d σ hU.1).2.1`.
-/
theorem TilInvariant_of : TilInvariantL → LetterShift → TilInvariant := by
  intro hTI hLS K _ _ _ l d _ σ hU hd2 hd F hF be0 hF1 hF2 ι _ _ om oms hOw hT u hu
  exact hTI K l d σ hU hd2 hd F hF be0 hF1 hF2 ι om oms hOw hT u hu (ZMod d) (letLog l)
    (hLS K l d σ hU.1).2.1

end Formalism.L2.Th1.D
