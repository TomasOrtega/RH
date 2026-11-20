import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdditiveCharConductorExists

noncomputable section

open ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocLanglands

namespace DiscreteGroups.sglob.DzType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use `set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k`. Establish `hx : φ (valuation k (x : k)) ≠ 0` using `by simp`. Establish `hy : φ (valuation k (y : k)) ≠ 0` using `by simp`. Establish `ho : ∀ z : kˣ, ord k z = -WithZero.log (φ (valuation k (z : k)))` using `fun _ => rfl`. Rewrite using `[← φ.strictMono.le_iff_le, ← WithZero.exp_log hx, ← WithZero.exp_log hy, WithZero.exp_le_exp, ho x, ho y]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem valuation_le_iff_ord_le (x y : kˣ) :
    valuation k (x : k) ≤ valuation k (y : k) ↔ ord k y ≤ ord k x := by
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have hx : φ (valuation k (x : k)) ≠ 0 := by simp
  have hy : φ (valuation k (y : k)) ≠ 0 := by simp
  have ho : ∀ z : kˣ, ord k z = -WithZero.log (φ (valuation k (z : k))) := fun _ => rfl
  rw [← φ.strictMono.le_iff_le, ← WithZero.exp_log hx, ← WithZero.exp_log hy, WithZero.exp_le_exp, ho x, ho y]
  omega

/- English proof (translation)
Establish `h` using `ord_mul k x⁻¹ x`. Rewrite `h` using `[inv_mul_cancel, ord_eq_zero (by simp)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem ord_inv_eq_neg_ord (x : kˣ) : ord k x⁻¹ = -ord k x := by
  have h := ord_mul k x⁻¹ x
  rw [inv_mul_cancel, ord_eq_zero (by simp)] at h
  omega

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [ord_eq_zero]`. Consider the case `succ n ih => rw [pow_succ, ord_mul, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ord_pow_bis (x : kˣ) (n : ℕ) : ord k (x ^ n) = n * ord k x := by
  induction n with
  | zero => simp [ord_eq_zero]
  | succ n ih => rw [pow_succ, ord_mul, ih]; push_cast; ring

/- English proof (translation)
Take `⟨t, ht⟩` from `ValuativeRel.valuation_surjective (uniformizer k)`. Establish `h0 : t ≠ 0`. Introduce and unpack `rfl`. Rewrite `ht` using `[map_zero]`. Conclude with `absurd ht.symm (by simp)`.

Conclude with `⟨Units.mk0 t h0, ht⟩`.
-/
theorem exists_uniformizer_valuation : ∃ t : kˣ, valuation k (t : k) = uniformizer k := by
  obtain ⟨t, ht⟩ := ValuativeRel.valuation_surjective (uniformizer k)
  have h0 : t ≠ 0 := by
    rintro rfl
    rw [map_zero] at ht
    exact absurd ht.symm (by simp)
  exact ⟨Units.mk0 t h0, ht⟩

/- English proof (translation)
Establish `hU : {x : k | ‖(ψ x : ℂ) - 1‖ < 1 / 2} ∈ nhds (0 : k)`. Establish `hc : Continuous fun x : k => ‖(ψ x : ℂ) - 1‖` using `((continuous_subtype_val.comp hψ).sub continuous_const).norm`. Conclude with `(isOpen_lt hc continuous_const).mem_nhds (by simp)`. Take `⟨s, hs⟩` from `exists_cball_subset hU`. Use `⟨s, fun y hy => ?_⟩` and prove the remaining obligations.

Establish `hn : ∀ n : ℕ, n • y ∈ cball s`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp [cball]`. Consider the case `succ n ih => rw [succ_nsmul]`.

Conclude with `add_mem_cball ih hy`. Establish `h` using `GlobalTheory.CharConductor.eq_one_of_pow_near_one (z := (ψ y : ℂ)) fun n => by`. Use `hs (hn n)` as an intermediate fact. Simplify using `only [Set.mem_ofPred_eq, AddChar.map_nsmul_eq_pow] at this`. Simplify using `using this`.

Conclude with `Circle.ext (by rw [h, Circle.coe_one])`.
-/
theorem exists_ball_char_trivial (ψ : AddChar k Circle) (hψ : Continuous ψ) :
    ∃ s : kˣ, ∀ y ∈ cball s, ψ y = 1 := by
  have hU : {x : k | ‖(ψ x : ℂ) - 1‖ < 1 / 2} ∈ nhds (0 : k) := by
    have hc : Continuous fun x : k => ‖(ψ x : ℂ) - 1‖ :=
      ((continuous_subtype_val.comp hψ).sub continuous_const).norm
    exact (isOpen_lt hc continuous_const).mem_nhds (by simp)
  obtain ⟨s, hs⟩ := exists_cball_subset hU
  refine ⟨s, fun y hy => ?_⟩
  have hn : ∀ n : ℕ, n • y ∈ cball s := by
    intro n
    induction n with
    | zero => simp [cball]
    | succ n ih => rw [succ_nsmul]; exact add_mem_cball ih hy
  have h := GlobalTheory.CharConductor.eq_one_of_pow_near_one (z := (ψ y : ℂ)) fun n => by
    have := hs (hn n)
    simp only [Set.mem_ofPred_eq, AddChar.map_nsmul_eq_pow] at this
    simpa using this
  exact Circle.ext (by rw [h, Circle.coe_one])

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_ball_char_trivial ψ hψ`. Take `⟨t, ht⟩` from `exists_uniformizer_valuation (k := k)`. Establish `hot : ord k t = 1` using `ord_eq_one ht`. Set `b : ℕ → kˣ` to `fun n => s * t⁻¹ ^ n`. Establish `hb : ∀ n : ℕ, ord k (b n) = ord k s - n` using `fun n => by`.

Simplify using `only [b]`. Rewrite using `[ord_mul, ord_pow_bis, ord_inv_eq_neg_ord, hot]`. Expand and normalize the polynomial expressions, which then agree. Establish `hex : ∃ n : ℕ, ¬ ∀ y : k, valuation k y ≤ valuation k (b n : k) → ψ y = 1`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, ψ x ≠ 1 := by`.

Assume the negation of the conclusion as `h`. Simplify using `only [not_exists, ne_eq, not_not] at h`. Conclude with `hψ1 (by ext x; rw [h x, AddChar.one_apply])`. Establish `hx0 : x ≠ 0` using `by rintro rfl; exact hx (AddChar.map_zero_eq_one ψ)`. Use `⟨(ord k s - ord k (Units.mk0 x hx0)).toNat, fun h => hx (h x ?_)⟩` and prove the remaining obligations.

Use `(valuation_le_iff_ord_le (Units.mk0 x hx0) (b (ord k s - ord k (Units.mk0 x hx0)).toNat)).2 (by rw [hb]; omega)` as an intermediate fact. Simplify using `using this`. Use `set N := Nat.find hex with hNdef`. Establish `hN : ¬ ∀ y : k, valuation k y ≤ valuation k (b N : k) → ψ y = 1` using `Nat.find_spec hex`. Establish `hN0 : N ≠ 0`.

Introduce `h0`. Apply `hN` to reduce the goal to its premises. Introduce `y hy`. Rewrite `hy` using `[h0]`. Conclude with `hs y (by simpa [b, cball] using hy)`.

Establish `hP : ∀ y : k, valuation k y ≤ valuation k (b (N - 1) : k) → ψ y = 1` using `Classical.not_not.1 (Nat.find_min hex (show N - 1 < Nat.find hex by omega))`. Use `⟨b (N - 1), fun x => ⟨fun h => ?_, fun h y hy => hP y (hy.trans h)⟩⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Apply `hN` to reduce the goal to its premises. Introduce `y hy`.

Apply `h y` to reduce the goal to its premises. Use `hy.trans ?_` and prove the remaining obligations. Establish `hx0 : x ≠ 0` using `by rintro rfl; exact hlt (by simp)`. Establish `h2 : ¬ ord k (b (N - 1)) ≤ ord k (Units.mk0 x hx0)` using `fun h3 => hlt (by simpa using (valuation_le_iff_ord_le (Units.mk0 x hx0) (b (N - 1))).2 h3)`. Establish `e1` using `hb N`.

Establish `e2` using `hb (N - 1)`. Use `(valuation_le_iff_ord_le (b N) (Units.mk0 x hx0)).2 (by omega)` as an intermediate fact. Simplify using `using this`.
-/
theorem exists_hasConductor_of_continuous_ne_one (ψ : AddChar k Circle) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) :
    ∃ c : kˣ, HasConductor ψ c := by
  obtain ⟨s, hs⟩ := exists_ball_char_trivial ψ hψ
  obtain ⟨t, ht⟩ := exists_uniformizer_valuation (k := k)
  have hot : ord k t = 1 := ord_eq_one ht
  let b : ℕ → kˣ := fun n => s * t⁻¹ ^ n
  have hb : ∀ n : ℕ, ord k (b n) = ord k s - n := fun n => by
    simp only [b]
    rw [ord_mul, ord_pow_bis, ord_inv_eq_neg_ord, hot]
    ring
  have hex : ∃ n : ℕ, ¬ ∀ y : k, valuation k y ≤ valuation k (b n : k) → ψ y = 1 := by
    obtain ⟨x, hx⟩ : ∃ x, ψ x ≠ 1 := by
      by_contra h
      simp only [not_exists, ne_eq, not_not] at h
      exact hψ1 (by ext x; rw [h x, AddChar.one_apply])
    have hx0 : x ≠ 0 := by rintro rfl; exact hx (AddChar.map_zero_eq_one ψ)
    refine ⟨(ord k s - ord k (Units.mk0 x hx0)).toNat, fun h => hx (h x ?_)⟩
    have := (valuation_le_iff_ord_le (Units.mk0 x hx0) (b (ord k s - ord k (Units.mk0 x hx0)).toNat)).2
      (by rw [hb]; omega)
    simpa using this
  classical
  set N := Nat.find hex with hNdef
  have hN : ¬ ∀ y : k, valuation k y ≤ valuation k (b N : k) → ψ y = 1 := Nat.find_spec hex
  have hN0 : N ≠ 0 := by
    intro h0
    apply hN
    intro y hy
    rw [h0] at hy
    exact hs y (by simpa [b, cball] using hy)
  have hP : ∀ y : k, valuation k y ≤ valuation k (b (N - 1) : k) → ψ y = 1 :=
    Classical.not_not.1 (Nat.find_min hex (show N - 1 < Nat.find hex by omega))
  refine ⟨b (N - 1), fun x => ⟨fun h => ?_, fun h y hy => hP y (hy.trans h)⟩⟩
  by_contra hlt
  apply hN
  intro y hy
  apply h y
  refine hy.trans ?_
  have hx0 : x ≠ 0 := by rintro rfl; exact hlt (by simp)
  have h2 : ¬ ord k (b (N - 1)) ≤ ord k (Units.mk0 x hx0) := fun h3 =>
    hlt (by simpa using (valuation_le_iff_ord_le (Units.mk0 x hx0) (b (N - 1))).2 h3)
  have e1 := hb N
  have e2 := hb (N - 1)
  have := (valuation_le_iff_ord_le (b N) (Units.mk0 x hx0)).2 (by omega)
  simpa using this

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
The claim follows from `le_antisymm ((h' c).1 ((h c).2 le_rfl)) ((h c').1 ((h' c').2 le_rfl))`.
-/
theorem hasConductor_valuation_eq {ψ : AddChar k Circle} {c c' : kˣ} (h : HasConductor ψ c)
    (h' : HasConductor ψ c') : valuation k (c : k) = valuation k (c' : k) :=
  le_antisymm ((h' c).1 ((h c).2 le_rfl)) ((h c').1 ((h' c').2 le_rfl))

/- English proof (translation)
Establish `hv` using `Valuation.integer.integers (valuation k)`. Establish `h1 : valuation k (((a - b : 𝒪[k])) : k) ≤ 1` using `(Valuation.mem_integer_iff _ _).1 (a - b).2`. Establish `e : ∀ x : 𝒪[k], algebraMap 𝒪[k] k x = (x : k)` using `fun _ => rfl`. Rewrite using `[← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hv.isUnit_iff_valuation_eq_one, e]`. Move the coercions through the operations in `at h1 ⊢`.

Conclude with `⟨fun h => lt_of_le_of_ne h1 h, fun h => h.ne⟩`.
-/
theorem residue_eq_iff_valuation_lt (a b : 𝒪[k]) :
    IsLocalRing.residue 𝒪[k] a = IsLocalRing.residue 𝒪[k] b ↔ valuation k ((a : k) - b) < 1 := by
  have hv := Valuation.integer.integers (valuation k)
  have h1 : valuation k (((a - b : 𝒪[k])) : k) ≤ 1 := (Valuation.mem_integer_iff _ _).1 (a - b).2
  have e : ∀ x : 𝒪[k], algebraMap 𝒪[k] k x = (x : k) := fun _ => rfl
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, hv.isUnit_iff_valuation_eq_one, e]
  push_cast at h1 ⊢
  exact ⟨fun h => lt_of_le_of_ne h1 h, fun h => h.ne⟩

set_option linter.style.haveILetI false in
/- English proof (translation)
Take `⟨c0, hc0⟩` from `exists_hasConductor_of_continuous_ne_one ψ hψ hψ1`. Take `⟨t, ht⟩` from `exists_uniformizer_valuation (k := k)`. Establish `htriv : ∀ y : k, valuation k y ≤ valuation k (c0 : k) → ψ y = 1` using `(hc0 c0).2 le_rfl`. Set `c : kˣ` to `c0 * t⁻¹`. Establish `hcc : c * t = c0` using `by simp only [c]; rw [inv_mul_cancel_right]`.

Establish `hct : c⁻¹ * c0 = t` using `by simp only [c]; rw [mul_inv_rev, inv_inv, inv_mul_cancel_right]`. Establish `hvc : valuation k (c : k) * uniformizer k = valuation k (c0 : k)`. Rewrite using `[← ht, ← map_mul, ← Units.val_mul, hcc]`. Establish `hoc : ord k c = ord k c0 - 1`. Simplify using `only [c]`.

Rewrite using `[ord_mul, ord_inv_eq_neg_ord, ord_eq_one ht]`. Expand and normalize the polynomial expressions, which then agree. Establish `key : ∀ r : kˣ, c * (r * c⁻¹) = r` using `fun r => by rw [mul_comm, inv_mul_cancel_right]`. Establish `keyk : ∀ r : kˣ, (r : k) = (c : k) * ((r * c⁻¹ : kˣ) : k)` using `fun r => by`. Rewrite using `[← Units.val_mul, key]`.

Establish `hwd : ∀ a b : 𝒪[k], IsLocalRing.residue 𝒪[k] a = IsLocalRing.residue 𝒪[k] b → ψ ((c : k) * a) = ψ ((c : k) * b)`. Introduce `a b hab`. Establish `h1` using `(residue_eq_iff_valuation_lt a b).1 hab`. Establish `h2 : valuation k ((c : k) * ((a : k) - b)) ≤ valuation k (c0 : k)`. Rewrite using `[map_mul, ← hvc]`.

Establish `h1'` using `le_uniformizer_iff.2 h1`. Use `gcongr`. Establish `h3` using `htriv _ h2`. Establish `h4 : (c : k) * a = (c : k) * b + (c : k) * ((a : k) - b)` using `by ring`. Rewrite using `[h4, AddChar.map_add_eq_mul, h3, mul_one]`.

Establish `hsurj : Function.Surjective (IsLocalRing.residue 𝒪[k])` using `IsLocalRing.residue_surjective`. Set `lift : 𝓀[k] → 𝒪[k]` to `Function.surjInv hsurj`. Establish `hlift : ∀ z, IsLocalRing.residue 𝒪[k] (lift z) = z` using `Function.surjInv_eq hsurj`. Set `ψb : AddChar 𝓀[k] Circle` to `{ toFun := fun z => ψ ((c : k) * lift z) map_zero_eq_one' := by`. Rewrite using `[hwd (lift 0) 0 (by rw [hlift, map_zero])]`.

Simplify using the standard rewrite rules. Use the proof step `map_add_eq_mul' := fun z w => by`. Rewrite using `[hwd (lift (z + w)) (lift z + lift w) (by rw [map_add, hlift, hlift, hlift])]`. Use `push_cast`. Rewrite using `[mul_add, AddChar.map_add_eq_mul] }`.

Establish `hψb : ∀ a : 𝒪[k], ψb (IsLocalRing.residue 𝒪[k] a) = ψ ((c : k) * a)` using `fun a => hwd _ _ (hlift _)`. Establish `hψbne : ψb ≠ 1`. Introduce `h1`. Establish `hc_gt : ¬ valuation k (c : k) ≤ valuation k (c0 : k)`. Rewrite using `[valuation_le_iff_ord_le]`.

Use linear arithmetic over natural numbers and integers. Choose the witnesses or unpack the hypotheses as in `⟨y, hy, hy1⟩ : ∃ y, valuation k y ≤ valuation k (c : k) ∧ ψ y ≠ 1 := by`. Assume the negation of the conclusion as `hno`. Simplify using `only [not_exists, not_and, ne_eq, not_not] at hno`. Conclude with `hc_gt ((hc0 c).1 hno)`.

Establish `ha : y / (c : k) ∈ 𝒪[k]`. Rewrite using `[Valuation.mem_integer_iff, map_div₀, div_le_one₀ (zero_lt_iff.2 (by simp))]`. Conclude with `hy`. Apply `hy1` to reduce the goal to its premises. Establish `h2` using `hψb ⟨_, ha⟩`.

Rewrite `h2` using `[h1, AddChar.one_apply]`. Establish `h3 : (c : k) * (y / (c : k)) = y` using `by field_simp`. Conclude with `(h3 ▸ h2).symm`. Use `⟨c, ψb, hψbne, fun ζ ζb hζ hred e he => ?_⟩` and prove the remaining obligations. Take `⟨c', a, R, hc', ha, hR, rfl⟩` from `he`.

Take `rfl : a = 1` from `ha.unique hζ`. Establish `hvc' : valuation k (c' : k) = valuation k (c0 : k)` using `hasConductor_valuation_eq hc' hc0`. Establish `hoc' : ord k c' = ord k c0`. Establish `h1` using `(valuation_le_iff_ord_le c' c0).1 hvc'.le`. Establish `h2` using `(valuation_le_iff_ord_le c0 c').1 hvc'.ge`.

Use linear arithmetic over natural numbers and integers. Establish `hRv : ∀ r ∈ R, valuation k ((r * c⁻¹ : kˣ) : k) = 1`. Introduce `r hr`. Rewrite using `[← ord_eq_zero_iff, ord_mul, ord_inv_eq_neg_ord]`. Use `hR.1 r hr` as an intermediate fact.

Move the coercions through the operations in `at this`. Use linear arithmetic over natural numbers and integers. Establish `hres_ne : ∀ (r : kˣ) (hr : r ∈ R), IsLocalRing.residue 𝒪[k] ⟨((r * c⁻¹ : kˣ) : k), (Valuation.mem_integer_iff _ _).2 (hRv r hr).le⟩ ≠ 0`. Introduce `r hr h0`. Rewrite `h0` using `[← map_zero (IsLocalRing.residue 𝒪[k]), residue_eq_iff_valuation_lt]`.

Establish `h1 : valuation k ((r * c⁻¹ : kˣ) : k) < 1` using `by simpa using h0`. Rewrite `h1` using `[hRv r hr]`. Conclude with `lt_irrefl _ h1`. Set `i : ∀ r ∈ R, 𝓀[k]ˣ` to `fun r hr => Units.mk0 _ (hres_ne r hr)`. Establish `: Finite 𝓀[k]ˣ` using `Finite.of_injective (fun u : 𝓀[k]ˣ => (u : 𝓀[k])) fun _ _ h => Units.ext h`.

Use `letI : Fintype 𝓀[k]ˣ := Fintype.ofFinite _`. Rewrite using `[Nat.cast_one, mul_assoc]`. Use `congr 1`. Rewrite using `[finsum_eq_sum_of_fintype, Finset.mul_sum]`. Use `Finset.sum_bij i (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_` and prove the remaining obligations.

Introduce `r1 hr1 r2 hr2 h`. Establish `h'` using `congrArg Units.val h`. Simplify using `only [i, Units.val_mk0] at h'`. Rewrite `h'` using `[residue_eq_iff_valuation_lt]`. Establish `h5 : valuation k ((r1 : k) - r2) ≤ valuation k (c' : k)`.

Establish `hcalc : (r1 : k) - r2 = (c : k) * (((r1 * c⁻¹ : kˣ) : k) - ((r2 * c⁻¹ : kˣ) : k))`. Rewrite using `[mul_sub, ← keyk, ← keyk]`. Rewrite using `[hcalc, map_mul, hvc', ← hvc]`. Establish `h''` using `le_uniformizer_iff.2 h'`. Use `gcongr`.

Take `⟨r0, -, huniq⟩` from `hR.2 r1 (hR.1 r1 hr1)`. Establish `e1` using `huniq r1 ⟨hr1, by simp⟩`. Establish `e2` using `huniq r2 ⟨hr2, h5⟩`. Conclude with `e1.trans e2.symm`. Introduce `z _`.

Establish `hza : IsLocalRing.residue 𝒪[k] (lift (z : 𝓀[k])) = z` using `hlift _`. Establish `hva : valuation k ((lift (z : 𝓀[k]) : 𝒪[k]) : k) = 1`. Establish `h1 : valuation k ((lift (z : 𝓀[k]) : 𝒪[k]) : k) ≤ 1` using `(Valuation.mem_integer_iff _ _).1 (lift (z : 𝓀[k])).2`. Use `le_antisymm h1 (not_lt.1 fun h => z.ne_zero ?_)` and prove the remaining obligations. Rewrite using `[← hza, ← map_zero (IsLocalRing.residue 𝒪[k]), residue_eq_iff_valuation_lt]`.

Simplify using `using h`. Establish `ha0 : ((lift (z : 𝓀[k]) : 𝒪[k]) : k) ≠ 0`. Introduce `h`. Rewrite `hva` using `[h, map_zero]`. Conclude with `zero_ne_one hva`.

Set `y : kˣ` to `c * Units.mk0 _ ha0`. Establish `hoy : ord k y = ord k c' - ((1 : ℕ) : ℤ)`. Simplify using `only [y]`. Rewrite using `[ord_mul, ord_eq_zero (x := Units.mk0 _ ha0) (by rw [Units.val_mk0]; exact hva), hoc, hoc']`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨r, ⟨hr, hyr⟩, -⟩` from `hR.2 y hoy`. Use `⟨r, hr, Units.ext ?_⟩` and prove the remaining obligations. Simplify using `only [i, Units.val_mk0]`. Rewrite using `[← hza, residue_eq_iff_valuation_lt]`.

Use `show valuation k (((r * c⁻¹ : kˣ) : k) - ((lift (z : 𝓀[k]) : 𝒪[k]) : k)) < 1`. Establish `hcalc : ((r * c⁻¹ : kˣ) : k) - ((lift (z : 𝓀[k]) : 𝒪[k]) : k) = ((c⁻¹ : kˣ) : k) * ((r : k) - y)`. Simplify using `only [y, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hcalc, map_mul]`.

Establish `h4 : valuation k ((r : k) - y) ≤ valuation k (c0 : k)`. Rewrite using `[Valuation.map_sub_swap, ← hvc']`. Conclude with `hyr`. Combine the equalities or inequalities in the displayed calculation. Introduce `r hr`.

Establish `hmem : ((r * c⁻¹ : kˣ) : k) ∈ 𝒪[k]` using `(Valuation.mem_integer_iff _ _).2 (hRv r hr).le`. Establish `hunit : IsUnit (⟨_, hmem⟩ : 𝒪[k])` using `(Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 (hRv r hr)`. Establish `h1 : ζ (r * c⁻¹) = ζb (i r hr)`. Use `hred hunit.unit` as an intermediate fact. Apply the tactic sequence `convert this using 2 <;> ext <;> rfl`.

Establish `h2 : ψb ((i r hr : 𝓀[k]ˣ) : 𝓀[k]) = ψ (r : k)` using `by show ψb (IsLocalRing.residue 𝒪[k] ⟨_, hmem⟩) = ψ (r : k)`. Rewrite using `[hψb]`. Use `show ψ ((c : k) * ((r * c⁻¹ : kˣ) : k)) = ψ (r : k)`. Rewrite using `[← keyk]`. Establish `h3 : ζ r = ζ c * ζ (r * c⁻¹)` using `by rw [← map_mul, key]`.

Rewrite using `[h2, ← h1, h3, mul_inv, Units.val_mul, mul_assoc]`.
-/
theorem tate_exp_one (ψ : AddChar k Circle) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) :
    ∃ (c : kˣ) (ψb : AddChar 𝓀[k] Circle), ψb ≠ 1 ∧
      ∀ (ζ : kˣ →* ℂˣ) (ζb : 𝓀[k]ˣ →* ℂˣ), HasExponent ζ 1 →
        (∀ x : 𝒪[k]ˣ, ζ (Units.map (algebraMap 𝒪[k] k : 𝒪[k] →* k) x) =
          ζb (Units.map (IsLocalRing.residue 𝒪[k] : 𝒪[k] →* 𝓀[k]) x)) →
        ∀ e : ℂ, IsTateEps ψ ζ e →
          e = (resCard k : ℂ) ^ (-(1 : ℂ) / 2) * (((ζ c)⁻¹ : ℂˣ) : ℂ) *
            ∑ᶠ z : 𝓀[k]ˣ, (((ζb z)⁻¹ : ℂˣ) : ℂ) * (ψb (z : 𝓀[k]) : ℂ) := by
  obtain ⟨c0, hc0⟩ := exists_hasConductor_of_continuous_ne_one ψ hψ hψ1
  obtain ⟨t, ht⟩ := exists_uniformizer_valuation (k := k)
  have htriv : ∀ y : k, valuation k y ≤ valuation k (c0 : k) → ψ y = 1 := (hc0 c0).2 le_rfl
  let c : kˣ := c0 * t⁻¹
  have hcc : c * t = c0 := by simp only [c]; rw [inv_mul_cancel_right]
  have hct : c⁻¹ * c0 = t := by simp only [c]; rw [mul_inv_rev, inv_inv, inv_mul_cancel_right]
  have hvc : valuation k (c : k) * uniformizer k = valuation k (c0 : k) := by
    rw [← ht, ← map_mul, ← Units.val_mul, hcc]
  have hoc : ord k c = ord k c0 - 1 := by
    simp only [c]
    rw [ord_mul, ord_inv_eq_neg_ord, ord_eq_one ht]
    ring
  have key : ∀ r : kˣ, c * (r * c⁻¹) = r := fun r => by rw [mul_comm, inv_mul_cancel_right]
  have keyk : ∀ r : kˣ, (r : k) = (c : k) * ((r * c⁻¹ : kˣ) : k) := fun r => by
    rw [← Units.val_mul, key]
  have hwd : ∀ a b : 𝒪[k], IsLocalRing.residue 𝒪[k] a = IsLocalRing.residue 𝒪[k] b →
      ψ ((c : k) * a) = ψ ((c : k) * b) := by
    intro a b hab
    have h1 := (residue_eq_iff_valuation_lt a b).1 hab
    have h2 : valuation k ((c : k) * ((a : k) - b)) ≤ valuation k (c0 : k) := by
      rw [map_mul, ← hvc]
      have h1' := le_uniformizer_iff.2 h1
      gcongr
    have h3 := htriv _ h2
    have h4 : (c : k) * a = (c : k) * b + (c : k) * ((a : k) - b) := by ring
    rw [h4, AddChar.map_add_eq_mul, h3, mul_one]
  have hsurj : Function.Surjective (IsLocalRing.residue 𝒪[k]) := IsLocalRing.residue_surjective
  let lift : 𝓀[k] → 𝒪[k] := Function.surjInv hsurj
  have hlift : ∀ z, IsLocalRing.residue 𝒪[k] (lift z) = z := Function.surjInv_eq hsurj
  let ψb : AddChar 𝓀[k] Circle :=
    { toFun := fun z => ψ ((c : k) * lift z)
      map_zero_eq_one' := by
        rw [hwd (lift 0) 0 (by rw [hlift, map_zero])]
        simp
      map_add_eq_mul' := fun z w => by
        rw [hwd (lift (z + w)) (lift z + lift w) (by rw [map_add, hlift, hlift, hlift])]
        push_cast
        rw [mul_add, AddChar.map_add_eq_mul] }
  have hψb : ∀ a : 𝒪[k], ψb (IsLocalRing.residue 𝒪[k] a) = ψ ((c : k) * a) := fun a =>
    hwd _ _ (hlift _)
  have hψbne : ψb ≠ 1 := by
    intro h1
    have hc_gt : ¬ valuation k (c : k) ≤ valuation k (c0 : k) := by
      rw [valuation_le_iff_ord_le]
      omega
    obtain ⟨y, hy, hy1⟩ : ∃ y, valuation k y ≤ valuation k (c : k) ∧ ψ y ≠ 1 := by
      by_contra hno
      simp only [not_exists, not_and, ne_eq, not_not] at hno
      exact hc_gt ((hc0 c).1 hno)
    have ha : y / (c : k) ∈ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, map_div₀, div_le_one₀ (zero_lt_iff.2 (by simp))]
      exact hy
    apply hy1
    have h2 := hψb ⟨_, ha⟩
    rw [h1, AddChar.one_apply] at h2
    have h3 : (c : k) * (y / (c : k)) = y := by field_simp
    exact (h3 ▸ h2).symm
  refine ⟨c, ψb, hψbne, fun ζ ζb hζ hred e he => ?_⟩
  obtain ⟨c', a, R, hc', ha, hR, rfl⟩ := he
  obtain rfl : a = 1 := ha.unique hζ
  have hvc' : valuation k (c' : k) = valuation k (c0 : k) := hasConductor_valuation_eq hc' hc0
  have hoc' : ord k c' = ord k c0 := by
    have h1 := (valuation_le_iff_ord_le c' c0).1 hvc'.le
    have h2 := (valuation_le_iff_ord_le c0 c').1 hvc'.ge
    omega
  have hRv : ∀ r ∈ R, valuation k ((r * c⁻¹ : kˣ) : k) = 1 := by
    intro r hr
    rw [← ord_eq_zero_iff, ord_mul, ord_inv_eq_neg_ord]
    have := hR.1 r hr
    push_cast at this
    omega
  have hres_ne : ∀ (r : kˣ) (hr : r ∈ R), IsLocalRing.residue 𝒪[k]
      ⟨((r * c⁻¹ : kˣ) : k), (Valuation.mem_integer_iff _ _).2 (hRv r hr).le⟩ ≠ 0 := by
    intro r hr h0
    rw [← map_zero (IsLocalRing.residue 𝒪[k]), residue_eq_iff_valuation_lt] at h0
    have h1 : valuation k ((r * c⁻¹ : kˣ) : k) < 1 := by simpa using h0
    rw [hRv r hr] at h1
    exact lt_irrefl _ h1
  let i : ∀ r ∈ R, 𝓀[k]ˣ := fun r hr => Units.mk0 _ (hres_ne r hr)
  have : Finite 𝓀[k]ˣ := Finite.of_injective (fun u : 𝓀[k]ˣ => (u : 𝓀[k])) fun _ _ h => Units.ext h
  letI : Fintype 𝓀[k]ˣ := Fintype.ofFinite _
  rw [Nat.cast_one, mul_assoc]
  congr 1
  rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_bij i (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro r1 hr1 r2 hr2 h
    have h' := congrArg Units.val h
    simp only [i, Units.val_mk0] at h'
    rw [residue_eq_iff_valuation_lt] at h'
    have h5 : valuation k ((r1 : k) - r2) ≤ valuation k (c' : k) := by
      have hcalc : (r1 : k) - r2 = (c : k) * (((r1 * c⁻¹ : kˣ) : k) - ((r2 * c⁻¹ : kˣ) : k)) := by
        rw [mul_sub, ← keyk, ← keyk]
      rw [hcalc, map_mul, hvc', ← hvc]
      have h'' := le_uniformizer_iff.2 h'
      gcongr
    obtain ⟨r0, -, huniq⟩ := hR.2 r1 (hR.1 r1 hr1)
    have e1 := huniq r1 ⟨hr1, by simp⟩
    have e2 := huniq r2 ⟨hr2, h5⟩
    exact e1.trans e2.symm
  · intro z _
    have hza : IsLocalRing.residue 𝒪[k] (lift (z : 𝓀[k])) = z := hlift _
    have hva : valuation k ((lift (z : 𝓀[k]) : 𝒪[k]) : k) = 1 := by
      have h1 : valuation k ((lift (z : 𝓀[k]) : 𝒪[k]) : k) ≤ 1 :=
        (Valuation.mem_integer_iff _ _).1 (lift (z : 𝓀[k])).2
      refine le_antisymm h1 (not_lt.1 fun h => z.ne_zero ?_)
      rw [← hza, ← map_zero (IsLocalRing.residue 𝒪[k]), residue_eq_iff_valuation_lt]
      simpa using h
    have ha0 : ((lift (z : 𝓀[k]) : 𝒪[k]) : k) ≠ 0 := by
      intro h
      rw [h, map_zero] at hva
      exact zero_ne_one hva
    let y : kˣ := c * Units.mk0 _ ha0
    have hoy : ord k y = ord k c' - ((1 : ℕ) : ℤ) := by
      simp only [y]
      rw [ord_mul, ord_eq_zero (x := Units.mk0 _ ha0) (by rw [Units.val_mk0]; exact hva), hoc, hoc']
      push_cast
      ring
    obtain ⟨r, ⟨hr, hyr⟩, -⟩ := hR.2 y hoy
    refine ⟨r, hr, Units.ext ?_⟩
    simp only [i, Units.val_mk0]
    rw [← hza, residue_eq_iff_valuation_lt]
    show valuation k (((r * c⁻¹ : kˣ) : k) - ((lift (z : 𝓀[k]) : 𝒪[k]) : k)) < 1
    have hcalc : ((r * c⁻¹ : kˣ) : k) - ((lift (z : 𝓀[k]) : 𝒪[k]) : k) =
        ((c⁻¹ : kˣ) : k) * ((r : k) - y) := by
      simp only [y, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
      field_simp
    rw [hcalc, map_mul]
    have h4 : valuation k ((r : k) - y) ≤ valuation k (c0 : k) := by
      rw [Valuation.map_sub_swap, ← hvc']
      exact hyr
    calc valuation k ((c⁻¹ : kˣ) : k) * valuation k ((r : k) - y)
        ≤ valuation k ((c⁻¹ : kˣ) : k) * valuation k (c0 : k) := by gcongr
      _ = uniformizer k := by rw [← map_mul, ← Units.val_mul, hct, ht]
      _ < 1 := uniformizer_lt_one
  · intro r hr
    have hmem : ((r * c⁻¹ : kˣ) : k) ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 (hRv r hr).le
    have hunit : IsUnit (⟨_, hmem⟩ : 𝒪[k]) :=
      (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 (hRv r hr)
    have h1 : ζ (r * c⁻¹) = ζb (i r hr) := by
      have := hred hunit.unit
      convert this using 2 <;> ext <;> rfl
    have h2 : ψb ((i r hr : 𝓀[k]ˣ) : 𝓀[k]) = ψ (r : k) := by
      show ψb (IsLocalRing.residue 𝒪[k] ⟨_, hmem⟩) = ψ (r : k)
      rw [hψb]
      show ψ ((c : k) * ((r * c⁻¹ : kˣ) : k)) = ψ (r : k)
      rw [← keyk]
    have h3 : ζ r = ζ c * ζ (r * c⁻¹) := by rw [← map_mul, key]
    rw [h2, ← h1, h3, mul_inv, Units.val_mul, mul_assoc]

end DiscreteGroups.sglob.DzType
