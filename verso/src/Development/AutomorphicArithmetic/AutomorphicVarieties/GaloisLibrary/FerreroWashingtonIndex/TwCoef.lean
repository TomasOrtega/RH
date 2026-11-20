import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.HalfSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.EvenTot

open UpperTheory.V.FW

/- English proof (translation)
Unfold `push`. Use `symm`. Use `Finset.sum_bij_ne_zero (fun (u : (ZMod M)ˣ) _ _ => (u : ZMod M)) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `u hu _`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢`.

Rewrite using `[← hu]`. Both sides reduce to the same expression. Introduce `u₁ _ _ u₂ _ _ h12`. Conclude with `Units.ext h12`. Introduce `s hs hne`.

Establish `hu : IsUnit s`. Assume the negation of the conclusion as `hn`. Apply `hne` to reduce the goal to its premises. Use `show g s * (MulChar.ofUnitHom χ) s = 0`. Rewrite using `[MulChar.map_nonunit _ hn, mul_zero]`.

Use `⟨hu.unit, ?_, ?_, hu.unit_spec⟩` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢`. Rewrite using `[← hs]`. Use `show (ZMod.castHom h (ZMod m)) (hu.unit : ZMod M) = _`. Rewrite using `[hu.unit_spec]`.

Establish `hne' : g s * (MulChar.ofUnitHom χ) s ≠ 0` using `hne`. Rewrite `hne'` using `[← hu.unit_spec, MulChar.ofUnitHom_coe]`. Then use the resulting hypothesis. Introduce `u _ _ show g u * (χ u : k) = g u * (MulChar.ofUnitHom χ) u`. Rewrite using `[MulChar.ofUnitHom_coe]`.
-/
private theorem push_units {k : Type} [CommRing k] {M : ℕ} [NeZero M] {m : ℕ} (h : m ∣ M)
    (χ : (ZMod M)ˣ →* kˣ) (g : ZMod M → k) (z : ZMod m) :
    push h (fun s => g s * MulChar.ofUnitHom χ s) z =
      ∑ s : (ZMod M)ˣ with ((ZMod.unitsMap h s : (ZMod m)ˣ) : ZMod m) = z, g s * (χ s : k) := by
  classical
  unfold push
  symm
  refine Finset.sum_bij_ne_zero (fun (u : (ZMod M)ˣ) _ _ => (u : ZMod M)) ?_ ?_ ?_ ?_
  · intro u hu _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    rw [← hu]
    rfl
  · intro u₁ _ _ u₂ _ _ h12
    exact Units.ext h12
  · intro s hs hne
    have hu : IsUnit s := by
      by_contra hn
      apply hne
      show g s * (MulChar.ofUnitHom χ) s = 0
      rw [MulChar.map_nonunit _ hn, mul_zero]
    refine ⟨hu.unit, ?_, ?_, hu.unit_spec⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      rw [← hs]
      show (ZMod.castHom h (ZMod m)) (hu.unit : ZMod M) = _
      rw [hu.unit_spec]
    · have hne' : g s * (MulChar.ofUnitHom χ) s ≠ 0 := hne
      rwa [← hu.unit_spec, MulChar.ofUnitHom_coe] at hne'
  · intro u _ _
    show g u * (χ u : k) = g u * (MulChar.ofUnitHom χ) u
    rw [MulChar.ofUnitHom_coe]

/- English proof (translation)
Use `haveI : Fact (1 < M) := ⟨by omega⟩`. Establish `hs0 : (s : ZMod M) ≠ 0` using `s.ne_zero`. Establish `hv : (s : ZMod M).val < M` using `ZMod.val_lt _`. Establish `hne : 2 * (s : ZMod M).val ≠ M`. Introduce `h2`.

Establish `h3 : ((2 * (s : ZMod M).val : ℕ) : ZMod M) = 0`. Rewrite using `[h2]`. Conclude with `ZMod.natCast_self M`. Move the coercions through the operations in `at h3`. Rewrite `h3` using `[ZMod.natCast_zmod_val]`.

Establish `h4 : (2 : ZMod M) = 0`. Use `congrArg (· * ((s⁻¹ : (ZMod M)ˣ) : ZMod M)) h3` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Establish `h5 : ((2 : ℕ) : ZMod M) = 0` using `by exact_mod_cast h4`. Rewrite `h5` using `[ZMod.natCast_eq_zero_iff]`.

Use `Nat.le_of_dvd (by norm_num) h5` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[Units.val_neg, ZMod.neg_val, if_neg hs0]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem half_val {M : ℕ} [NeZero M] (hM : 2 < M) (s : (ZMod M)ˣ) :
    2 * ((-s : (ZMod M)ˣ) : ZMod M).val < M ↔ ¬ 2 * (s : ZMod M).val < M := by
  haveI : Fact (1 < M) := ⟨by omega⟩
  have hs0 : (s : ZMod M) ≠ 0 := s.ne_zero
  have hv : (s : ZMod M).val < M := ZMod.val_lt _
  have hne : 2 * (s : ZMod M).val ≠ M := by
    intro h2
    have h3 : ((2 * (s : ZMod M).val : ℕ) : ZMod M) = 0 := by
      rw [h2]
      exact ZMod.natCast_self M
    push_cast at h3
    rw [ZMod.natCast_zmod_val] at h3
    have h4 : (2 : ZMod M) = 0 := by
      have := congrArg (· * ((s⁻¹ : (ZMod M)ˣ) : ZMod M)) h3
      simpa [mul_assoc] using this
    have h5 : ((2 : ℕ) : ZMod M) = 0 := by exact_mod_cast h4
    rw [ZMod.natCast_eq_zero_iff] at h5
    have := Nat.le_of_dvd (by norm_num) h5
    omega
  rw [Units.val_neg, ZMod.neg_val, if_neg hs0]
  omega

/- English proof (translation)
Introduce `l _ M n₀ _ h k _ χ g R hn₀ hχ hg hRW hRneg hWR htw y`. Establish `hl : l.Prime` using `Fact.out`. Establish `hM : 2 < M`. Establish `h4 : 4 ≤ l ^ n₀`. Combine the equalities or inequalities in the displayed calculation.

Use `Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hneg1 : (-1 : ℤ_[l]ˣ) ∈ WW l` using `by show (-1 : ℤ_[l]ˣ) ∈ rootsOfUnity (l ^ ee l).totient ℤ_[l]`. Rewrite using `[mem_rootsOfUnity]`. Apply `Even.neg_one_pow` to reduce the goal to its premises.

Apply `Nat.totient_even` to reduce the goal to its premises. Establish `h2` using `hl.two_le`. Unfold `ee`. Use `split_ifs with h2'`. Substitute `h2'` using the available equality.

Evaluate the numerical expressions. Rewrite using `[pow_one]`. Use linear arithmetic over natural numbers and integers. Establish `hnegmem : ∀ v ∈ WW l, -v ∈ WW l` using `fun v hv => by`. Rewrite using `[← neg_one_mul v]`.

Conclude with `mul_mem hneg1 hv`. Take `⟨-, -, -, -, -, -, -, hinj⟩` from `reps l`. Establish `hredneg : ∀ v : ℤ_[l]ˣ, redU l n₀ (-v) = -redU l n₀ v` using `fun v => by`. Use `ext`. Simplify using `[redU]`.

Establish `hρneg : ∀ x : (ZMod M)ˣ, ZMod.unitsMap h (-x) = -ZMod.unitsMap h x` using `fun x => by`. Use `ext`. Simplify using `[ZMod.unitsMap_def]`. Establish `hredinj : ∀ v ∈ WW l, ∀ w ∈ WW l, redU l n₀ v = redU l n₀ w → v = w`. Introduce `v hv w hw hvw`.

Establish `h1 : redU l n₀ (v * w⁻¹) = 1` using `by rw [map_mul, map_inv, hvw, mul_inv_cancel]`. Conclude with `mul_inv_eq_one.mp (hinj n₀ hn₀ _ (mul_mem hv (inv_mem hw)) h1)`. Establish `hcoef : ∀ q, ∑ s ∈ (Finset.univ.filter fun s : (ZMod M)ˣ => 2 * (s : ZMod M).val < M).filter (fun s => piQ l n₀ h s = q), (g s : k) * (χ s : k) = 0`. Introduce `q`. Establish `h1` using `congrArg (fun x => MonoidAlgebra.coeff x q) htw`.

Simplify using `only [map_sum, toK, MonoidAlgebra.mapRingHom_single, eq_intCast, tw_single, MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply, MonoidAlgebra.single_apply, MonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at h1`. Rewrite using `[Finset.sum_filter]`. Conclude with `h1`. Establish `hpu : ∀ z, push h (fun s => (g s : k) * MulChar.ofUnitHom χ s) z = ∑ s : (ZMod M)ˣ with ((ZMod.unitsMap h s : (ZMod (l ^ n₀))ˣ) : ZMod (l ^ n₀)) = z, (g s : k) * (χ s : k)` using `fun z => push_units h χ (fun s => (g s : k)) z`. Simplify using `only [hpu]`.

Distinguish the cases in `hy : IsUnit y`. Use `swap`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `r _`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `s hs`. It suffices to derive a contradiction. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hs`. Apply `hy` to reduce the goal to its premises. Establish `: y = ((redU l n₀ r.1 : (ZMod (l ^ n₀))ˣ) : ZMod (l ^ n₀)) * ((ZMod.unitsMap h s : (ZMod (l ^ n₀))ˣ) : ZMod (l ^ n₀))`.

Rewrite using `[hs, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]`. Rewrite using `[this]`. Conclude with `(Units.isUnit _).mul (Units.isUnit _)`. Take `⟨u, rfl⟩` from `hy`. Set `t : R → Finset (ZMod M)ˣ` to `fun r => Finset.univ.filter fun s => ZMod.unitsMap h s = (redU l n₀ r.1)⁻¹ * u`.

Establish `hgoal : ∀ r : R, ∑ s ∈ Finset.univ.filter (fun s : (ZMod M)ˣ => ((ZMod.unitsMap h s : (ZMod (l ^ n₀))ˣ) : ZMod (l ^ n₀)) = (((redU l n₀ r.1)⁻¹ : (ZMod (l ^ n₀))ˣ) : ZMod (l ^ n₀)) * (u : ZMod (l ^ n₀))), (g s : k) * (χ s : k) = ∑ s ∈ t r, (g s : k) * (χ s : k)` using `fun r => Finset.sum_congr (Finset.filter_congr (fun s _ => by rw [Units.ext_iff, Units.val_mul])) (fun _ _ => rfl)`. Use `Eq.trans (Finset.sum_congr rfl (fun r _ => hgoal r)) ?_` and prove the remaining obligations. Establish `hdisj : (↑(Finset.univ : Finset R) : Set R).PairwiseDisjoint t`. Introduce `r₁ _ r₂ _ hne`. Simplify using `only [Function.onFun]`.

Rewrite using `[Finset.disjoint_left]`. Introduce `s hs1 hs2`. Simplify using `only [t, Finset.mem_filter, Finset.mem_univ, true_and] at hs1 hs2`. Apply `hne` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `hredinj _ (hRW _ r₁.2) _ (hRW _ r₂.2)` to reduce the goal to its premises. Establish `h12` using `hs1.symm.trans hs2`. Rewrite `h12` using `[mul_left_inj, inv_inj]`. Conclude with `h12`. Use `Eq.trans (Finset.sum_biUnion hdisj).symm ?_` and prove the remaining obligations.

Establish `hπ : ∀ v ∈ WW l, ∀ x : (ZMod M)ˣ, ZMod.unitsMap h x = (redU l n₀ v)⁻¹ * u → piQ l n₀ h x = QuotientGroup.mk' (Subgroup.map (redU l n₀) (WW l)) u`. Introduce `v hv x hx`. Establish `h1 : QuotientGroup.mk' (Subgroup.map (redU l n₀) (WW l)) (redU l n₀ v)⁻¹ = 1`. Rewrite using `[QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]`. Conclude with `inv_mem (Subgroup.mem_map_of_mem _ hv)`.

Use `show QuotientGroup.mk' _ (ZMod.unitsMap h x) = _`. Rewrite using `[hx, map_mul, h1, one_mul]`. Use `Eq.trans (halfSum (ZMod M)ˣ k Neg.neg _ _ (fun s => (g s : k) * (χ s : k)) ?_ ?_ ?_ ?_ ?_ ?_) (hcoef (QuotientGroup.mk' (Subgroup.map (redU l n₀) (WW l)) u))` and prove the remaining obligations. Conclude with `fun x => neg_neg x`. Introduce `x`.

Establish `hχx : (χ (-x) : k) = -(χ x : k)`. Rewrite using `[← neg_one_mul x, map_mul, hχ, Units.val_mul, Units.val_neg, Units.val_one, neg_one_mul]`. Use `show ((g ((-x : (ZMod M)ˣ) : ZMod M)) : k) * (χ (-x) : k) = (g x : k) * (χ x : k)`. Rewrite using `[hχx, Units.val_neg, hg x]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Introduce `x hx hnx`. Simplify using `only [t, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and] at hx hnx`. Take `⟨r, hr⟩` from `hx`. Take `⟨r', hr'⟩` from `hnx`.

Rewrite `hr'` using `[hρneg, hr, ← neg_mul]`. Establish `h2` using `mul_right_cancel hr'`. Establish `h3 : redU l n₀ r'.1 = redU l n₀ (-r.1)`. Rewrite using `[hredneg, ← inv_inj, ← h2, inv_neg]`. Establish `h4` using `hredinj _ (hRW _ r'.2) _ (hnegmem _ (hRW _ r.2)) h3`.

Conclude with `hRneg _ r.2 (h4 ▸ r'.2)`. Introduce `x hx hnx`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hnx`. Conclude with `((half_val hM x).mp hnx.1) hx.1`. Introduce `x hx`.

Simplify using `only [t, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and] at hx`. Take `⟨r, hr⟩` from `hx`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Distinguish the cases in `hh : 2 * (x : ZMod M).val < M`. Conclude with `Or.inl ⟨hh, hπ r.1 (hRW _ r.2) x hr⟩`.

Use `Or.inr ⟨(half_val hM x).mpr hh, hπ (-r.1) (hnegmem _ (hRW _ r.2)) (-x) ?_⟩` and prove the remaining obligations. Rewrite using `[hρneg, hr, hredneg, inv_neg, neg_mul]`. Introduce `x hx`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hx`. Take `⟨-, hq⟩` from `hx`.

Establish `hq' : QuotientGroup.mk' (Subgroup.map (redU l n₀) (WW l)) (ZMod.unitsMap h x) = QuotientGroup.mk' _ u` using `hq`. Rewrite `hq'` using `[QuotientGroup.mk'_eq_mk']`. Take `⟨z, hz, hxz⟩` from `hq'`. Take `⟨w, hw, rfl⟩` from `Subgroup.mem_map.mp hz`. Establish `hx' : ZMod.unitsMap h x = (redU l n₀ w)⁻¹ * u` using `eq_inv_mul_of_mul_eq ((mul_comm _ _).trans hxz)`.

Break down `hWR w hw with hR | hR` into its components or cases. Conclude with `Or.inl (Finset.mem_biUnion.mpr ⟨⟨w, hR⟩, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'⟩⟩)`. Use `Or.inr (Finset.mem_biUnion.mpr ⟨⟨-w, hR⟩, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩) show ZMod.unitsMap h (-x) = (redU l n₀ (-w))⁻¹ * u` and prove the remaining obligations. Rewrite using `[hρneg, hx', hredneg, inv_neg, neg_mul]`.
-/
theorem UpperTheory.V.FW.twCoef :
    ∀ (l : ℕ) [Fact l.Prime] (M n₀ : ℕ) [NeZero M] (h : l ^ n₀ ∣ M) (k : Type) [CommRing k] (χ : (ZMod M)ˣ →* kˣ) (g : ZMod M → ℤ) (R : Finset ℤ_[l]ˣ), 2 ≤ n₀ → χ (-1) = -1 → (∀ s : (ZMod M)ˣ, g (-(s : ZMod M)) = -g s) → (∀ r ∈ R, r ∈ WW l) → (∀ r ∈ R, -r ∉ R) → (∀ w ∈ WW l, w ∈ R ∨ -w ∈ R) → tw χ (piQ l n₀ h) (toK k _ (∑ s ∈ Finset.univ.filter fun s : (ZMod M)ˣ => 2 * (s : ZMod M).val < M, MonoidAlgebra.single s (g s))) = 0 → ∀ y : ZMod (l ^ n₀), ∑ r : R, push h (fun s => (g s : k) * MulChar.ofUnitHom χ s) (((redU l n₀ r.1)⁻¹ : (ZMod (l ^ n₀))ˣ) * y) = 0 := by
  intro l _ M n₀ _ h k _ χ g R hn₀ hχ hg hRW hRneg hWR htw y
  classical
  have hl : l.Prime := Fact.out
  have hM : 2 < M := by
    have h4 : 4 ≤ l ^ n₀ :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ l ^ 2 := Nat.pow_le_pow_left hl.two_le 2
        _ ≤ l ^ n₀ := Nat.pow_le_pow_right hl.pos hn₀
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) h
    omega
  have hneg1 : (-1 : ℤ_[l]ˣ) ∈ WW l := by
    show (-1 : ℤ_[l]ˣ) ∈ rootsOfUnity (l ^ ee l).totient ℤ_[l]
    rw [mem_rootsOfUnity]
    apply Even.neg_one_pow
    apply Nat.totient_even
    have h2 := hl.two_le
    unfold ee
    split_ifs with h2'
    · subst h2'
      norm_num
    · rw [pow_one]
      omega
  have hnegmem : ∀ v ∈ WW l, -v ∈ WW l := fun v hv => by
    rw [← neg_one_mul v]
    exact mul_mem hneg1 hv
  obtain ⟨-, -, -, -, -, -, -, hinj⟩ := reps l
  have hredneg : ∀ v : ℤ_[l]ˣ, redU l n₀ (-v) = -redU l n₀ v := fun v => by
    ext
    simp [redU]
  have hρneg : ∀ x : (ZMod M)ˣ, ZMod.unitsMap h (-x) = -ZMod.unitsMap h x := fun x => by
    ext
    simp [ZMod.unitsMap_def]
  have hredinj : ∀ v ∈ WW l, ∀ w ∈ WW l, redU l n₀ v = redU l n₀ w → v = w := by
    intro v hv w hw hvw
    have h1 : redU l n₀ (v * w⁻¹) = 1 := by rw [map_mul, map_inv, hvw, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hinj n₀ hn₀ _ (mul_mem hv (inv_mem hw)) h1)
  have hcoef : ∀ q, ∑ s ∈ (Finset.univ.filter fun s : (ZMod M)ˣ => 2 * (s : ZMod M).val < M).filter
      (fun s => piQ l n₀ h s = q), (g s : k) * (χ s : k) = 0 := by
    intro q
    have h1 := congrArg (fun x => MonoidAlgebra.coeff x q) htw
    simp only [map_sum, toK, MonoidAlgebra.mapRingHom_single, eq_intCast, tw_single,
      MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply, MonoidAlgebra.single_apply,
      MonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at h1
    rw [Finset.sum_filter]
    exact h1
  have hpu : ∀ z, push h (fun s => (g s : k) * MulChar.ofUnitHom χ s) z =
      ∑ s : (ZMod M)ˣ with ((ZMod.unitsMap h s : (ZMod (l ^ n₀))ˣ) : ZMod (l ^ n₀)) = z,
        (g s : k) * (χ s : k) := fun z => push_units h χ (fun s => (g s : k)) z
  simp only [hpu]
  by_cases hy : IsUnit y
  swap
  · apply Finset.sum_eq_zero
    intro r _
    apply Finset.sum_eq_zero
    intro s hs
    exfalso
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    apply hy
    have : y = ((redU l n₀ r.1 : (ZMod (l ^ n₀))ˣ) : ZMod (l ^ n₀)) *
        ((ZMod.unitsMap h s : (ZMod (l ^ n₀))ˣ) : ZMod (l ^ n₀)) := by
      rw [hs, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    rw [this]
    exact (Units.isUnit _).mul (Units.isUnit _)
  obtain ⟨u, rfl⟩ := hy
  let t : R → Finset (ZMod M)ˣ := fun r =>
    Finset.univ.filter fun s => ZMod.unitsMap h s = (redU l n₀ r.1)⁻¹ * u
  have hgoal : ∀ r : R, ∑ s ∈ Finset.univ.filter (fun s : (ZMod M)ˣ =>
      ((ZMod.unitsMap h s : (ZMod (l ^ n₀))ˣ) : ZMod (l ^ n₀)) =
        (((redU l n₀ r.1)⁻¹ : (ZMod (l ^ n₀))ˣ) : ZMod (l ^ n₀)) * (u : ZMod (l ^ n₀))),
      (g s : k) * (χ s : k) = ∑ s ∈ t r, (g s : k) * (χ s : k) := fun r =>
    Finset.sum_congr (Finset.filter_congr (fun s _ => by rw [Units.ext_iff, Units.val_mul]))
      (fun _ _ => rfl)
  refine Eq.trans (Finset.sum_congr rfl (fun r _ => hgoal r)) ?_
  have hdisj : (↑(Finset.univ : Finset R) : Set R).PairwiseDisjoint t := by
    intro r₁ _ r₂ _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro s hs1 hs2
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and] at hs1 hs2
    apply hne
    apply Subtype.ext
    apply hredinj _ (hRW _ r₁.2) _ (hRW _ r₂.2)
    have h12 := hs1.symm.trans hs2
    rw [mul_left_inj, inv_inj] at h12
    exact h12
  refine Eq.trans (Finset.sum_biUnion hdisj).symm ?_
  have hπ : ∀ v ∈ WW l, ∀ x : (ZMod M)ˣ, ZMod.unitsMap h x = (redU l n₀ v)⁻¹ * u →
      piQ l n₀ h x = QuotientGroup.mk' (Subgroup.map (redU l n₀) (WW l)) u := by
    intro v hv x hx
    have h1 : QuotientGroup.mk' (Subgroup.map (redU l n₀) (WW l)) (redU l n₀ v)⁻¹ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact inv_mem (Subgroup.mem_map_of_mem _ hv)
    show QuotientGroup.mk' _ (ZMod.unitsMap h x) = _
    rw [hx, map_mul, h1, one_mul]
  refine Eq.trans (halfSum (ZMod M)ˣ k Neg.neg _ _ (fun s => (g s : k) * (χ s : k))
    ?_ ?_ ?_ ?_ ?_ ?_) (hcoef (QuotientGroup.mk' (Subgroup.map (redU l n₀) (WW l)) u))
  · exact fun x => neg_neg x
  · intro x
    have hχx : (χ (-x) : k) = -(χ x : k) := by
      rw [← neg_one_mul x, map_mul, hχ, Units.val_mul, Units.val_neg, Units.val_one, neg_one_mul]
    show ((g ((-x : (ZMod M)ˣ) : ZMod M)) : k) * (χ (-x) : k) = (g x : k) * (χ x : k)
    rw [hχx, Units.val_neg, hg x]
    push_cast
    ring
  · intro x hx hnx
    simp only [t, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and] at hx hnx
    obtain ⟨r, hr⟩ := hx
    obtain ⟨r', hr'⟩ := hnx
    rw [hρneg, hr, ← neg_mul] at hr'
    have h2 := mul_right_cancel hr'
    have h3 : redU l n₀ r'.1 = redU l n₀ (-r.1) := by
      rw [hredneg, ← inv_inj, ← h2, inv_neg]
    have h4 := hredinj _ (hRW _ r'.2) _ (hnegmem _ (hRW _ r.2)) h3
    exact hRneg _ r.2 (h4 ▸ r'.2)
  · intro x hx hnx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hnx
    exact ((half_val hM x).mp hnx.1) hx.1
  · intro x hx
    simp only [t, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and] at hx
    obtain ⟨r, hr⟩ := hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hh : 2 * (x : ZMod M).val < M
    · exact Or.inl ⟨hh, hπ r.1 (hRW _ r.2) x hr⟩
    · refine Or.inr ⟨(half_val hM x).mpr hh, hπ (-r.1) (hnegmem _ (hRW _ r.2)) (-x) ?_⟩
      rw [hρneg, hr, hredneg, inv_neg, neg_mul]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨-, hq⟩ := hx
    have hq' : QuotientGroup.mk' (Subgroup.map (redU l n₀) (WW l)) (ZMod.unitsMap h x) =
        QuotientGroup.mk' _ u := hq
    rw [QuotientGroup.mk'_eq_mk'] at hq'
    obtain ⟨z, hz, hxz⟩ := hq'
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    have hx' : ZMod.unitsMap h x = (redU l n₀ w)⁻¹ * u :=
      eq_inv_mul_of_mul_eq ((mul_comm _ _).trans hxz)
    rcases hWR w hw with hR | hR
    · exact Or.inl (Finset.mem_biUnion.mpr ⟨⟨w, hR⟩, Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'⟩⟩)
    · refine Or.inr (Finset.mem_biUnion.mpr ⟨⟨-w, hR⟩, Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩)
      show ZMod.unitsMap h (-x) = (redU l n₀ (-w))⁻¹ * u
      rw [hρneg, hx', hredneg, inv_neg, neg_mul]
