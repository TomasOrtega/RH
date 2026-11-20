import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Gordan
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartSpan
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PartialFiltrationCoeff

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.PartialFiltrationCoeff.part_filt_coeff M`.
-/
private theorem UpperTheory.V.Alg.part_filt_coeff {O σ : Type} [CommRing O] [IsLocalRing O] (M : ℕ) :
    ∀ f ∈ maximalIdeal (MvPowerSeries σ O) ^ M, ∀ n : σ →₀ ℕ,
      coeff n f ∈ maximalIdeal O ^ (M - n.degree) :=
  _root_.UpperTheory.Reformulated.B.PartialFiltrationCoeff.part_filt_coeff M

/- English proof (translation)
Take `⟨g, hg, hcl, hj⟩` from `UpperTheory.V.Alg.gordan σ X wt`. Take `⟨μ, hμ, hμ'⟩` from `hj j`. Use `⟨(g ∪ μ).sup Finsupp.degree, fun n hn hD => ?_⟩` and prove the remaining obligations. Take `⟨m, hm, hmn⟩` from `hμ' n hn`. Take `⟨r, rfl⟩` from `exists_add_of_le hmn`.

Establish `hr : Finsupp.weight wt r = 0`. Rewrite `hn` using `[map_add, hμ m hm]`. Simplify using `using hn`. Establish `hr0 : r ≠ 0`. Introduce and unpack `rfl`.

Establish `: m.degree ≤ (g ∪ μ).sup Finsupp.degree` using `Finset.le_sup (f := Finsupp.degree) (Finset.mem_union_right _ hm)`. Rewrite `hD` using `[add_zero]`. Use linear arithmetic over natural numbers and integers. Establish `key : ∀ r ∈ AddSubmonoid.closure (g : Set (σ →₀ ℕ)), r = 0 ∨ ∃ a ∈ g, a ≤ r`. Introduce `r hr`.

Proceed by induction on `hr using AddSubmonoid.closure_induction with`. Consider the case `mem x hx => exact Or.inr ⟨x, hx, le_rfl⟩`. Consider the case `zero => exact Or.inl rfl`. Consider the case `add x y _ _ hx hy`. Break down `hx with rfl | ⟨a, ha, hax⟩` into its components or cases.

Simplify using `using hy`. Conclude with `Or.inr ⟨a, ha, hax.trans le_self_add⟩`. Take `⟨a, ha, har⟩` from `(key r (hcl r hr)).resolve_left hr0`. Take `⟨b, rfl⟩` from `exists_add_of_le har`. Conclude with `⟨a, m + b, (hg a ha).1, (hg a ha).2, Finset.le_sup (f := Finsupp.degree) (Finset.mem_union_left _ ha), by abel⟩`.
-/
private theorem UpperTheory.V.Alg.part_filt_split {σ X : Type} [Finite σ] [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (wt : σ → X) (j : X) :
    ∃ D : ℕ, ∀ n : σ →₀ ℕ, Finsupp.weight wt n = j → D < n.degree →
      ∃ g n' : σ →₀ ℕ, g ≠ 0 ∧ Finsupp.weight wt g = 0 ∧ g.degree ≤ D ∧ n = g + n' := by
  classical
  obtain ⟨g, hg, hcl, hj⟩ := UpperTheory.V.Alg.gordan σ X wt
  obtain ⟨μ, hμ, hμ'⟩ := hj j
  refine ⟨(g ∪ μ).sup Finsupp.degree, fun n hn hD => ?_⟩
  obtain ⟨m, hm, hmn⟩ := hμ' n hn
  obtain ⟨r, rfl⟩ := exists_add_of_le hmn
  have hr : Finsupp.weight wt r = 0 := by
    rw [map_add, hμ m hm] at hn
    simpa using hn
  have hr0 : r ≠ 0 := by
    rintro rfl
    have : m.degree ≤ (g ∪ μ).sup Finsupp.degree :=
      Finset.le_sup (f := Finsupp.degree) (Finset.mem_union_right _ hm)
    rw [add_zero] at hD
    omega
  have key : ∀ r ∈ AddSubmonoid.closure (g : Set (σ →₀ ℕ)), r = 0 ∨ ∃ a ∈ g, a ≤ r := by
    intro r hr
    induction hr using AddSubmonoid.closure_induction with
    | mem x hx => exact Or.inr ⟨x, hx, le_rfl⟩
    | zero => exact Or.inl rfl
    | add x y _ _ hx hy =>
      rcases hx with rfl | ⟨a, ha, hax⟩
      · simpa using hy
      · exact Or.inr ⟨a, ha, hax.trans le_self_add⟩
  obtain ⟨a, ha, har⟩ := (key r (hcl r hr)).resolve_left hr0
  obtain ⟨b, rfl⟩ := exists_add_of_le har
  exact ⟨a, m + b, (hg a ha).1, (hg a ha).2,
    Finset.le_sup (f := Finsupp.degree) (Finset.mem_union_left _ ha), by abel⟩

/- English proof (translation)
Introduce `m hm`. Rewrite using `[coeff_monomial, if_neg]`. Introduce and unpack `rfl`. Conclude with `hm hn`.
-/
private theorem UpperTheory.V.Alg.part_filt_monomial {O σ X : Type} [CommRing O] [AddCommGroup X] (wt : σ → X)
    {j : X} {n : σ →₀ ℕ} (hn : Finsupp.weight wt n = j) (c : O) : monomial n c ∈ wtPart O wt j := by
  classical
  intro m hm
  rw [coeff_monomial, if_neg]
  rintro rfl
  exact hm hn

/- English proof (translation)
Introduce `O _ _ _ _ X _ _ _ _ R _ _ _ W _ j k`. Use `set Q : Submodule O R := W.part 0 ⊓ (maximalIdeal R).restrictScalars O with hQ`. Establish `hloc : IsLocalHom (W.π : MvPowerSeries W.σ O →+* R)` using `IsLocalHom.of_surjective _ W.surj`. Establish `hone : (1 : R) ∈ W.part 0` using `⟨1, one_mem_wtPart O W.wt, map_one W.π⟩`. Establish `hmono : ∀ k : ℕ, ∃ N : ℕ, ∀ n : W.σ →₀ ℕ, Finsupp.weight W.wt n = j → N ≤ n.degree → W.π (monomial n 1) ∈ Q ^ k * W.part j`.

Take `⟨D, hD⟩` from `UpperTheory.V.Alg.part_filt_split W.wt j`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Use `⟨0, fun n hn _ => ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_zero, one_mul]`. Conclude with `⟨_, UpperTheory.V.Alg.part_filt_monomial W.wt hn 1, rfl⟩`. Consider the case `succ k ih`. Take `⟨N, hN⟩` from `ih`. Use `⟨N + D + 1, fun n hn hd => ?_⟩` and prove the remaining obligations.

Take `⟨g, n', hg0, hgw, hgd, rfl⟩` from `hD n hn (by omega)`. Rewrite `hd` using `[map_add]`. Rewrite `hn` using `[map_add, hgw, zero_add]`. Establish `h1` using `hN n' hn (by omega)`. Establish `h2 : W.π (monomial g 1) ∈ Q`.

Use `⟨⟨_, UpperTheory.V.Alg.part_filt_monomial W.wt hgw 1, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce `hu`. Establish `h3 : IsUnit (monomial g (1 : O))` using `hloc.map_nonunit _ hu`. Rewrite `h3` using `[MvPowerSeries.isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, coeff_monomial, if_neg hg0.symm]`. Conclude with `not_isUnit_zero h3`.

Establish `h4 : (monomial (g + n') (1 : O) : MvPowerSeries W.σ O) = monomial g 1 * monomial n' 1`. Rewrite using `[monomial_mul_monomial, one_mul]`. Rewrite using `[h4, map_mul, pow_succ', mul_assoc]`. Conclude with `Submodule.mul_mem_mul h2 h1`. Establish `hconst : ∀ k : ℕ, ∀ c ∈ maximalIdeal O ^ k, algebraMap O R c ∈ Q ^ k`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `c _`. Rewrite using `[pow_zero]`.

Conclude with `Submodule.algebraMap_mem c`. Consider the case `succ k ih`. Introduce `c hc`. Rewrite `hc` using `[pow_succ]`. Use `Submodule.mul_induction_on hc (fun a ha b hb => ?_) (fun a b ha hb => ?_)` and prove the remaining obligations.

Rewrite using `[map_mul, pow_succ]`. Use `Submodule.mul_mem_mul (ih a ha) ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.algebraMap_eq_smul_one]`. Conclude with `Submodule.smul_mem _ _ hone`. Conclude with `fun hu => hb (IsLocalHom.map_nonunit (f := algebraMap O R) b hu)`.

Rewrite using `[map_add]`. Conclude with `add_mem ha hb`. Take `⟨N, hN⟩` from `hmono k`. Use `⟨N + k, ?_⟩` and prove the remaining obligations. Introduce and unpack `x ⟨⟨f, hf, hfx⟩, hx⟩`.

Establish `hfx' : W.π f = x` using `hfx`. Establish `hle : maximalIdeal R ≤ (maximalIdeal (MvPowerSeries W.σ O)).map W.π`. Introduce `y hy`. Take `⟨g, rfl⟩` from `W.surj y`. Conclude with `Ideal.mem_map_of_mem _ fun hu => hy (hu.map W.π)`.

Establish `hx' : x ∈ (maximalIdeal (MvPowerSeries W.σ O) ^ (N + k)).map W.π`. Rewrite using `[Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono hle _ hx`. Take `⟨g, hg, hgx⟩` from `(Ideal.mem_map_iff_of_surjective W.π W.surj).1 hx'`. Use `set h := wcomp O W.wt j g with hh`.

Establish `hhx : W.π h = x`. Establish `h1 : f - g ∈ RingHom.ker W.π`. Rewrite using `[RingHom.mem_ker, map_sub, hfx', hgx, sub_self]`. Establish `h2` using `W.homog _ h1 j`. Establish `h3 : wcomp O W.wt j f = f`.

Use extensionality with `n`. Rewrite using `[coeff_wcomp]`. Use `split_ifs with hn`. Both sides reduce to the same expression. Conclude with `(hf n hn).symm`.

Rewrite `h2` using `[map_sub, h3, RingHom.mem_ker, map_sub, hfx', sub_eq_zero]`. Conclude with `h2.symm`. Establish `hhj : h ∈ wtPart O W.wt j` using `wcomp_mem O W.wt j g`. Establish `hhc : ∀ n : W.σ →₀ ℕ, n.degree < N → coeff n h ∈ maximalIdeal O ^ k`. Introduce `n hn`.

Rewrite using `[hh, coeff_wcomp]`. Use `split_ifs`. Conclude with `Ideal.pow_le_pow_right (by omega) (UpperTheory.V.Alg.part_filt_coeff _ g hg n)`. Conclude with `zero_mem _`. Establish `hfin : {n : W.σ →₀ ℕ | n.degree < N}.Finite` using `(Finsupp.finite_of_degree_le N).subset fun n (hn : n.degree < N) => hn.le`.

Use `set low : MvPowerSeries W.σ O := ∑ n ∈ hfin.toFinset, monomial n (coeff n h) with hlow`. Establish `hlowc : ∀ m, coeff m low = if m.degree < N then coeff m h else 0`. Introduce `m`. Rewrite using `[hlow, map_sum]`. Simplify using `only [coeff_monomial]`.

Rewrite using `[Finset.sum_ite_eq]`. Simplify using the standard rewrite rules. Take `⟨μ, hμ, hspan⟩` from `UpperTheory.V.Alg.part_span O R X W {n | Finsupp.weight W.wt n = j ∧ N ≤ n.degree} j fun n hn => hn.1`. Take `⟨b, hb, hhigh⟩` from `hspan (h - low) (by`. Introduce `n hn`.

Rewrite using `[map_sub, hlowc]`. Use `split_ifs with hd`. Conclude with `sub_self _`. Rewrite using `[sub_zero]`. Conclude with `hhj n fun hw => hn ⟨hw, not_lt.1 hd⟩)`.

Establish `hsum : x = W.π low + W.π (h - low)` using `by rw [← map_add, add_sub_cancel, hhx]`. Rewrite using `[hsum]`. Use `add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[hlow, map_sum]`. Use `Submodule.sum_mem _ fun n hn => ?_` and prove the remaining obligations.

Distinguish the cases in `hw : Finsupp.weight W.wt n = j`. Establish `h1 : W.π (monomial n (coeff n h)) = algebraMap O R (coeff n h) * 1 * W.π (monomial n 1)`. Rewrite using `[mul_one, ← Algebra.smul_def, ← map_smul, ← map_smul, smul_eq_mul, mul_one]`. Rewrite using `[h1]`. Conclude with `Submodule.mul_mem_mul (Submodule.mul_mem_mul (hconst k _ (hhc n (hfin.mem_toFinset.1 hn))) hone) ⟨_, UpperTheory.V.Alg.part_filt_monomial W.wt hw 1, rfl⟩`.

Rewrite using `[hhj n hw, map_zero, map_zero]`. Conclude with `zero_mem _`. Rewrite using `[hhigh, map_sum]`. Use `Submodule.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Rewrite using `[map_mul, mul_comm (Q ^ k), mul_assoc]`.

Conclude with `Submodule.mul_mem_mul ⟨_, hb m, rfl⟩ (hN m (hμ hm).1 (hμ hm).2)`.
-/
theorem UpperTheory.V.Alg.part_filt :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (j : X) (n : ℕ), ∃ M : ℕ, W.part j ⊓ (maximalIdeal R ^ M).restrictScalars O ≤ (W.part 0 ⊓ (maximalIdeal R).restrictScalars O) ^ n * W.part 0 * W.part j := by
  intro O _ _ _ _ X _ _ _ _ R _ _ _ W _ j k
  classical
  set Q : Submodule O R := W.part 0 ⊓ (maximalIdeal R).restrictScalars O with hQ
  have hloc : IsLocalHom (W.π : MvPowerSeries W.σ O →+* R) := IsLocalHom.of_surjective _ W.surj
  have hone : (1 : R) ∈ W.part 0 := ⟨1, one_mem_wtPart O W.wt, map_one W.π⟩

  have hmono : ∀ k : ℕ, ∃ N : ℕ, ∀ n : W.σ →₀ ℕ, Finsupp.weight W.wt n = j → N ≤ n.degree →
      W.π (monomial n 1) ∈ Q ^ k * W.part j := by
    obtain ⟨D, hD⟩ := UpperTheory.V.Alg.part_filt_split W.wt j
    intro k
    induction k with
    | zero =>
      refine ⟨0, fun n hn _ => ?_⟩
      rw [pow_zero, one_mul]
      exact ⟨_, UpperTheory.V.Alg.part_filt_monomial W.wt hn 1, rfl⟩
    | succ k ih =>
      obtain ⟨N, hN⟩ := ih
      refine ⟨N + D + 1, fun n hn hd => ?_⟩
      obtain ⟨g, n', hg0, hgw, hgd, rfl⟩ := hD n hn (by omega)
      rw [map_add] at hd
      rw [map_add, hgw, zero_add] at hn
      have h1 := hN n' hn (by omega)
      have h2 : W.π (monomial g 1) ∈ Q := by
        refine ⟨⟨_, UpperTheory.V.Alg.part_filt_monomial W.wt hgw 1, rfl⟩, ?_⟩
        intro hu
        have h3 : IsUnit (monomial g (1 : O)) := hloc.map_nonunit _ hu
        rw [MvPowerSeries.isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, coeff_monomial,
          if_neg hg0.symm] at h3
        exact not_isUnit_zero h3
      have h4 : (monomial (g + n') (1 : O) : MvPowerSeries W.σ O) = monomial g 1 * monomial n' 1 := by
        rw [monomial_mul_monomial, one_mul]
      rw [h4, map_mul, pow_succ', mul_assoc]
      exact Submodule.mul_mem_mul h2 h1

  have hconst : ∀ k : ℕ, ∀ c ∈ maximalIdeal O ^ k, algebraMap O R c ∈ Q ^ k := by
    intro k
    induction k with
    | zero =>
      intro c _
      rw [pow_zero]
      exact Submodule.algebraMap_mem c
    | succ k ih =>
      intro c hc
      rw [pow_succ] at hc
      refine Submodule.mul_induction_on hc (fun a ha b hb => ?_) (fun a b ha hb => ?_)
      · rw [map_mul, pow_succ]
        refine Submodule.mul_mem_mul (ih a ha) ⟨?_, ?_⟩
        · rw [Algebra.algebraMap_eq_smul_one]
          exact Submodule.smul_mem _ _ hone
        · exact fun hu => hb (IsLocalHom.map_nonunit (f := algebraMap O R) b hu)
      · rw [map_add]
        exact add_mem ha hb
  obtain ⟨N, hN⟩ := hmono k
  refine ⟨N + k, ?_⟩
  rintro x ⟨⟨f, hf, hfx⟩, hx⟩
  have hfx' : W.π f = x := hfx
  have hle : maximalIdeal R ≤ (maximalIdeal (MvPowerSeries W.σ O)).map W.π := by
    intro y hy
    obtain ⟨g, rfl⟩ := W.surj y
    exact Ideal.mem_map_of_mem _ fun hu => hy (hu.map W.π)
  have hx' : x ∈ (maximalIdeal (MvPowerSeries W.σ O) ^ (N + k)).map W.π := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hle _ hx
  obtain ⟨g, hg, hgx⟩ := (Ideal.mem_map_iff_of_surjective W.π W.surj).1 hx'
  set h := wcomp O W.wt j g with hh
  have hhx : W.π h = x := by
    have h1 : f - g ∈ RingHom.ker W.π := by
      rw [RingHom.mem_ker, map_sub, hfx', hgx, sub_self]
    have h2 := W.homog _ h1 j
    have h3 : wcomp O W.wt j f = f := by
      ext n
      rw [coeff_wcomp]
      split_ifs with hn
      · rfl
      · exact (hf n hn).symm
    rw [map_sub, h3, RingHom.mem_ker, map_sub, hfx', sub_eq_zero] at h2
    exact h2.symm
  have hhj : h ∈ wtPart O W.wt j := wcomp_mem O W.wt j g
  have hhc : ∀ n : W.σ →₀ ℕ, n.degree < N → coeff n h ∈ maximalIdeal O ^ k := by
    intro n hn
    rw [hh, coeff_wcomp]
    split_ifs
    · exact Ideal.pow_le_pow_right (by omega) (UpperTheory.V.Alg.part_filt_coeff _ g hg n)
    · exact zero_mem _
  have hfin : {n : W.σ →₀ ℕ | n.degree < N}.Finite :=
    (Finsupp.finite_of_degree_le N).subset fun n (hn : n.degree < N) => hn.le
  set low : MvPowerSeries W.σ O := ∑ n ∈ hfin.toFinset, monomial n (coeff n h) with hlow
  have hlowc : ∀ m, coeff m low = if m.degree < N then coeff m h else 0 := by
    intro m
    rw [hlow, map_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq]
    simp
  obtain ⟨μ, hμ, hspan⟩ := UpperTheory.V.Alg.part_span O R X W
    {n | Finsupp.weight W.wt n = j ∧ N ≤ n.degree} j fun n hn => hn.1
  obtain ⟨b, hb, hhigh⟩ := hspan (h - low) (by
    intro n hn
    rw [map_sub, hlowc]
    split_ifs with hd
    · exact sub_self _
    · rw [sub_zero]
      exact hhj n fun hw => hn ⟨hw, not_lt.1 hd⟩)
  have hsum : x = W.π low + W.π (h - low) := by rw [← map_add, add_sub_cancel, hhx]
  rw [hsum]
  refine add_mem ?_ ?_
  · rw [hlow, map_sum]
    refine Submodule.sum_mem _ fun n hn => ?_
    by_cases hw : Finsupp.weight W.wt n = j
    · have h1 : W.π (monomial n (coeff n h)) = algebraMap O R (coeff n h) * 1 * W.π (monomial n 1) := by
        rw [mul_one, ← Algebra.smul_def, ← map_smul, ← map_smul, smul_eq_mul, mul_one]
      rw [h1]
      exact Submodule.mul_mem_mul
        (Submodule.mul_mem_mul (hconst k _ (hhc n (hfin.mem_toFinset.1 hn))) hone)
        ⟨_, UpperTheory.V.Alg.part_filt_monomial W.wt hw 1, rfl⟩
    · rw [hhj n hw, map_zero, map_zero]
      exact zero_mem _
  · rw [hhigh, map_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    rw [map_mul, mul_comm (Q ^ k), mul_assoc]
    exact Submodule.mul_mem_mul ⟨_, hb m, rfl⟩ (hN m (hμ hm).1 (hμ hm).2)
