import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

open Classical in
/- English proof (translation)
Use extensionality with `n`. Rewrite using `[coeff_wcomp]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Rewrite using `[if_pos rfl]`.

Use `split_ifs with hn`. Both sides reduce to the same expression. Conclude with `(hf n hn).symm`. Rewrite using `[if_neg h, map_zero] split_ifs with hn`. Conclude with `hf n (fun hi => h (hi.symm.trans hn))`.

Both sides reduce to the same expression.
-/
private theorem wcomp_of_mem_ite {O : Type} [CommRing O] {σ X : Type} [AddCommGroup X] (wt : σ → X) {i j : X}
    {f : MvPowerSeries σ O} (hf : f ∈ wtPart O wt i) : wcomp O wt j f = if i = j then f else 0 := by
  ext n
  rw [coeff_wcomp]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl]
    split_ifs with hn
    · rfl
    · exact (hf n hn).symm
  · rw [if_neg h, map_zero]
    split_ifs with hn
    · exact hf n (fun hi => h (hi.symm.trans hn))
    · rfl

/- English proof (translation)
Introduce `O _ _ X _ A _ _ _ K hK W κ _ ε wf hε hspan hrel`. Establish `hεK : ∀ v, ε v ∈ K` using `fun v => by`. Rewrite using `[hspan]`. Conclude with `Ideal.subset_span ⟨v, rfl⟩`. Establish `hkill : ∀ (r : A) (y : A), r ∈ maximalIdeal A → y ∈ K → r * y = 0`.

Introduce `r y hr hy`. Establish `h1` using `Ideal.mul_mem_mul hr hy`. Rewrite `h1` using `[hK]`. Conclude with `(Ideal.mem_bot).1 h1`. Establish `hrep : ∀ x ∈ K, ∃ a : κ → O, x = ∑ v, a v • ε v`.

Introduce `x hx`. Rewrite `hx` using `[hspan]`. Take `⟨r, hr⟩` from `(Submodule.mem_span_range_iff_exists_fun A).1 hx`. Use `choose a ha using fun v => IsCO.res_surj (O := O) (r v)`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hr]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `v _`. Establish `h0` using `hkill _ _ (ha v) (hεK v)`. Rewrite using `[smul_eq_mul, Algebra.smul_def]`.

Take the linear combination `h0`. Set `co : κ → A → ResidueField O` to `fun u x => if h : ∃ a : κ → O, x = ∑ v, a v • ε v then residue O (h.choose u) else 0`. Establish `hco : ∀ x (a : κ → O), x = ∑ v, a v • ε v → ∀ u, co u x = residue O (a u)`. Introduce `x a hx u`. Establish `h : ∃ a : κ → O, x = ∑ v, a v • ε v` using `⟨a, hx⟩`.

Simplify using `only [co]`. Rewrite using `[dif_pos h]`. Establish `hd : ∑ v, (h.choose v - a v) • ε v = 0`. Simplify using `only [sub_smul, Finset.sum_sub_distrib]`. Rewrite using `[← h.choose_spec, ← hx, sub_self]`.

Rewrite using `[← sub_eq_zero, ← map_sub]`. Conclude with `(IsLocalRing.residue_eq_zero_iff _).2 (hrel _ hd u)`. Use `⟨co, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `u x hx y hy`. Take `⟨a, ha⟩` from `hrep x hx`.

Take `⟨b, hb⟩` from `hrep y hy`. Establish `hxy : x + y = ∑ v, (a + b) v • ε v`. Rewrite using `[ha, hb, ← Finset.sum_add_distrib]`. Simplify using `only [Pi.add_apply, add_smul]`. Rewrite using `[hco _ _ hxy u, hco _ _ ha u, hco _ _ hb u, Pi.add_apply, map_add]`.

Introduce `u a x hx`. Take `⟨b, hb⟩` from `hrep x hx`. Take `⟨c, hc⟩` from `IsCO.res_surj (O := O) a`. Establish `hax : a * x = ∑ v, (c * b v) • ε v`. Establish `h0` using `hkill _ _ hc hx`.

Establish `h1 : a * x = algebraMap O A c * x` using `by linear_combination h0`. Rewrite using `[h1, hb, Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `v _`. Rewrite using `[mul_smul, ← Algebra.smul_def]`.

Establish `hr : res O A a = residue O c`. Establish `h1` using `(res_eq_zero_iff O A _).2 hc`. Rewrite `h1` using `[map_sub, sub_eq_zero, AlgHom.commutes]`. Rewrite using `[h1]`. Both sides reduce to the same expression.

Rewrite using `[hco _ _ hax u, hco _ _ hb u, map_mul, hr]`. Introduce `u j hj x hxK hxP`. Take `⟨a, ha⟩` from `hrep x hxK`. Rewrite using `[hco x a ha u]`. Apply `(IsLocalRing.residue_eq_zero_iff _).2` to reduce the goal to its premises.

Establish `hε' : ∀ v, ε v ∈ Submodule.map W.π.toLinearMap (wtPart O W.wt (wf v))` using `hε`. Use `choose f hf hfε using fun v => Submodule.mem_map.1 (hε' v)`. Establish `hxP' : x ∈ Submodule.map W.π.toLinearMap (wtPart O W.wt j)` using `hxP`. Take `⟨g, hg, hgx⟩` from `Submodule.mem_map.1 hxP'`. Simplify using `only [AlgHom.toLinearMap_apply] at hfε hgx`.

Establish `hk : g - ∑ v, a v • f v ∈ RingHom.ker W.π`. Rewrite using `[RingHom.mem_ker, map_sub, map_sum]`. Simplify using `only [map_smul, hfε]`. Rewrite using `[hgx, ← ha, sub_self]`. Establish `hh` using `W.homog _ hk (wf u)`.

Establish `hfw : ∀ v, wcomp O W.wt (wf u) (f v) = if wf v = wf u then f v else 0` using `fun v => wcomp_of_mem_ite W.wt (hf v)`. Rewrite `hh` using `[map_sub, map_sum, wcomp_of_mem_ite W.wt hg, if_neg hj]`. Simplify using `only [map_smul, hfw] at hh`. Establish `hrel0 : ∑ v, (if wf v = wf u then a v else 0) • ε v = 0`. Establish `h2` using `RingHom.mem_ker.1 hh`.

Rewrite `h2` using `[map_sub, map_zero, map_sum, zero_sub, neg_eq_zero]`. Rewrite using `[← h2]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `v _`. Use `split_ifs with hv`.

Rewrite using `[map_smul, hfε]`. Rewrite using `[smul_zero, map_zero, zero_smul]`. Establish `h5` using `hrel _ hrel0 u`. Simplify using `using h5`. Introduce `x hx`.

Take `⟨a, ha⟩` from `hrep x hx`. Conclude with `⟨a, fun u => (hco x a ha u).symm, ha⟩`.
-/
theorem UpperTheory.V.Alg.ker_coef :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (X : Type) [AddCommGroup X] (A : Type) [CommRing A] [Algebra O A] [IsCO O A] (K : Ideal A), maximalIdeal A * K = ⊥ → ∀ (W : WPres O X A) (κ : Type) [Fintype κ] (ε : κ → A) (wf : κ → X), (∀ u, ε u ∈ W.part (wf u)) → K = Ideal.span (Set.range ε) → (∀ c : κ → O, ∑ u, c u • ε u = 0 → ∀ u, c u ∈ maximalIdeal O) →
          ∃ co : κ → A → ResidueField O, (∀ u, ∀ x ∈ K, ∀ y ∈ K, co u (x + y) = co u x + co u y) ∧ (∀ u (a : A), ∀ x ∈ K, co u (a * x) = res O A a * co u x) ∧
            (∀ u j, j ≠ wf u → ∀ x ∈ K, x ∈ W.part j → co u x = 0) ∧ ∀ x ∈ K, ∃ a : κ → O, (∀ u, residue O (a u) = co u x) ∧ x = ∑ u, a u • ε u := by
  intro O _ _ X _ A _ _ _ K hK W κ _ ε wf hε hspan hrel
  classical
  have hεK : ∀ v, ε v ∈ K := fun v => by
    rw [hspan]
    exact Ideal.subset_span ⟨v, rfl⟩
  have hkill : ∀ (r : A) (y : A), r ∈ maximalIdeal A → y ∈ K → r * y = 0 := by
    intro r y hr hy
    have h1 := Ideal.mul_mem_mul hr hy
    rw [hK] at h1
    exact (Ideal.mem_bot).1 h1
  have hrep : ∀ x ∈ K, ∃ a : κ → O, x = ∑ v, a v • ε v := by
    intro x hx
    rw [hspan] at hx
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hx
    choose a ha using fun v => IsCO.res_surj (O := O) (r v)
    refine ⟨a, ?_⟩
    rw [← hr]
    apply Finset.sum_congr rfl
    intro v _
    have h0 := hkill _ _ (ha v) (hεK v)
    rw [smul_eq_mul, Algebra.smul_def]
    linear_combination h0
  let co : κ → A → ResidueField O := fun u x =>
    if h : ∃ a : κ → O, x = ∑ v, a v • ε v then residue O (h.choose u) else 0
  have hco : ∀ x (a : κ → O), x = ∑ v, a v • ε v → ∀ u, co u x = residue O (a u) := by
    intro x a hx u
    have h : ∃ a : κ → O, x = ∑ v, a v • ε v := ⟨a, hx⟩
    simp only [co]
    rw [dif_pos h]
    have hd : ∑ v, (h.choose v - a v) • ε v = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← h.choose_spec, ← hx, sub_self]
    rw [← sub_eq_zero, ← map_sub]
    exact (IsLocalRing.residue_eq_zero_iff _).2 (hrel _ hd u)
  refine ⟨co, ?_, ?_, ?_, ?_⟩
  · intro u x hx y hy
    obtain ⟨a, ha⟩ := hrep x hx
    obtain ⟨b, hb⟩ := hrep y hy
    have hxy : x + y = ∑ v, (a + b) v • ε v := by
      rw [ha, hb, ← Finset.sum_add_distrib]
      simp only [Pi.add_apply, add_smul]
    rw [hco _ _ hxy u, hco _ _ ha u, hco _ _ hb u, Pi.add_apply, map_add]
  · intro u a x hx
    obtain ⟨b, hb⟩ := hrep x hx
    obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) a
    have hax : a * x = ∑ v, (c * b v) • ε v := by
      have h0 := hkill _ _ hc hx
      have h1 : a * x = algebraMap O A c * x := by linear_combination h0
      rw [h1, hb, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      rw [mul_smul, ← Algebra.smul_def]
    have hr : res O A a = residue O c := by
      have h1 := (res_eq_zero_iff O A _).2 hc
      rw [map_sub, sub_eq_zero, AlgHom.commutes] at h1
      rw [h1]
      rfl
    rw [hco _ _ hax u, hco _ _ hb u, map_mul, hr]
  · intro u j hj x hxK hxP
    obtain ⟨a, ha⟩ := hrep x hxK
    rw [hco x a ha u]
    apply (IsLocalRing.residue_eq_zero_iff _).2
    have hε' : ∀ v, ε v ∈ Submodule.map W.π.toLinearMap (wtPart O W.wt (wf v)) := hε
    choose f hf hfε using fun v => Submodule.mem_map.1 (hε' v)
    have hxP' : x ∈ Submodule.map W.π.toLinearMap (wtPart O W.wt j) := hxP
    obtain ⟨g, hg, hgx⟩ := Submodule.mem_map.1 hxP'
    simp only [AlgHom.toLinearMap_apply] at hfε hgx
    have hk : g - ∑ v, a v • f v ∈ RingHom.ker W.π := by
      rw [RingHom.mem_ker, map_sub, map_sum]
      simp only [map_smul, hfε]
      rw [hgx, ← ha, sub_self]
    have hh := W.homog _ hk (wf u)
    have hfw : ∀ v, wcomp O W.wt (wf u) (f v) = if wf v = wf u then f v else 0 :=
      fun v => wcomp_of_mem_ite W.wt (hf v)
    rw [map_sub, map_sum, wcomp_of_mem_ite W.wt hg, if_neg hj] at hh
    simp only [map_smul, hfw] at hh
    have hrel0 : ∑ v, (if wf v = wf u then a v else 0) • ε v = 0 := by
      have h2 := RingHom.mem_ker.1 hh
      rw [map_sub, map_zero, map_sum, zero_sub, neg_eq_zero] at h2
      rw [← h2]
      apply Finset.sum_congr rfl
      intro v _
      split_ifs with hv
      · rw [map_smul, hfε]
      · rw [smul_zero, map_zero, zero_smul]
    have h5 := hrel _ hrel0 u
    simpa using h5
  · intro x hx
    obtain ⟨a, ha⟩ := hrep x hx
    exact ⟨a, fun u => (hco x a ha u).symm, ha⟩
