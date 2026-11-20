import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresGrZeroIsCOOfMemMaximalIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GrGen

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

/- English proof (translation)
Introduce `O _ _ _ _ X _ _ _ _ R _ _ _ W hz`. Use `haveI := W.fin`. Use `haveI hco : IsCO O (W.gr 0) := wPres_gr_zero_isCO_of_mem_maximalIdeal O X R W hz`. Use `haveI : IsNoetherianRing (W.gr 0) := IsCO.toIsNoetherian O`. Establish `hgen : Algebra.adjoin (W.gr 0) (Set.range W.zA) = ⊤`.

Rewrite using `[eq_top_iff]`. Introduce and unpack `a -`. Establish `ha : a ∈ Algebra.adjoin O ((W.gr 0 : Set W.A) ∪ Set.range W.zA)`. Rewrite using `[gr_gen O R X W]`. Discharge the goal by the elementary cases of `trivial`.

Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Break down `hx with hx | ⟨i, rfl⟩` into its components or cases. Establish `e : algebraMap (W.gr 0) W.A ⟨x, hx⟩ = x` using `rfl`. Rewrite using `[← e]`.

Conclude with `Subalgebra.algebraMap_mem _ _`. Conclude with `Algebra.subset_adjoin ⟨i, rfl⟩`. Consider the case `algebraMap r`. Establish `hr : algebraMap O W.A r ∈ W.gr 0` using `SetLike.algebraMap_mem_graded W.gr r`. Establish `e : algebraMap (W.gr 0) W.A ⟨_, hr⟩ = algebraMap O W.A r` using `rfl`.

Rewrite using `[← e]`. Conclude with `Subalgebra.algebraMap_mem _ _`. Consider the case `add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy`. Consider the case `mul x y _ _ hx hy => exact Subalgebra.mul_mem _ hx hy`. Use `haveI hft : Algebra.FiniteType (W.gr 0) W.A := ⟨⟨Finset.univ.image W.zA, by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, hgen]⟩⟩`.

Use `⟨Algebra.FiniteType.isNoetherianRing (W.gr 0) W.A, hft, ?_⟩` and prove the remaining obligations. Introduce `j`. Establish `hmono : ∀ m : W.σ →₀ ℕ, monomial m (1 : O) ∈ wtPart O W.wt (Finsupp.weight W.wt m)`. Introduce `m n hn`. Rewrite using `[coeff_monomial, if_neg]`.

Introduce and unpack `rfl`. Conclude with `hn rfl`. Take `⟨μ, hμS, hμ⟩` from `part_span O R X W {n | Finsupp.weight W.wt n = j} j (fun n hn => hn)`. Set `mA : (W.σ →₀ ℕ) → W.A` to `fun m => ⟨W.π (monomial m 1), W.part_le_A (Submodule.mem_map_of_mem (hmono m))⟩`. Establish `hsj : ∀ a ∈ μ.image mA, a ∈ W.gr j`.

Introduce `a ha`. Take `⟨m, hm, rfl⟩` from `Finset.mem_image.mp ha`. Establish `hw : Finsupp.weight W.wt m = j` using `hμS hm`. Use `show (W.π (monomial m 1) : R) ∈ W.part j`. Rewrite using `[← hw]`.

Conclude with `Submodule.mem_map_of_mem (hmono m)`. Use `⟨μ.image mA, hsj, ?_⟩` and prove the remaining obligations. Apply `le_antisymm` to reduce the goal to its premises. Introduce `a ha`. Establish `ha' : (a : R) ∈ W.part j` using `ha`.

Take `⟨f, hf, hfa⟩` from `Submodule.mem_map.mp ha'`. Take `⟨b, hb, hfb⟩` from `hμ f (fun n hn => hf n hn)`. Set `bA : (W.σ →₀ ℕ) → W.A` to `fun m => ⟨W.π (b m), W.part_le_A (Submodule.mem_map_of_mem (hb m))⟩`. Establish `hsum : a = ∑ m ∈ μ, bA m * mA m`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[← hfa]`. Simplify using `[hfb, map_sum, map_mul, bA, mA]`. Rewrite using `[hsum]`. Use `Submodule.sum_mem _ fun m hm => Submodule.mul_mem_mul ?_ ?_` and prove the remaining obligations. Use `show (W.π (b m) : R) ∈ W.part 0`.

Conclude with `Submodule.mem_map_of_mem (hb m)`. Conclude with `Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem mA hm))`. Rewrite using `[Submodule.mul_le]`. Introduce `x hx y hy`. Establish `hy' : y ∈ W.gr j` using `(Submodule.span_le.mpr fun z hz => hsj z hz) hy`.

Simplify using `using SetLike.GradedMul.mul_mem hx hy'`.
-/
theorem UpperTheory.V.Alg.gr_noeth :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → IsNoetherianRing W.A ∧ Algebra.FiniteType (W.gr 0) W.A ∧ ∀ j, ∃ s : Finset W.A, (∀ a ∈ s, a ∈ W.gr j) ∧ W.gr j = W.gr 0 * Submodule.span O (s : Set W.A) := by
  intro O _ _ _ _ X _ _ _ _ R _ _ _ W hz
  classical
  haveI := W.fin
  haveI hco : IsCO O (W.gr 0) := wPres_gr_zero_isCO_of_mem_maximalIdeal O X R W hz
  haveI : IsNoetherianRing (W.gr 0) := IsCO.toIsNoetherian O
  have hgen : Algebra.adjoin (W.gr 0) (Set.range W.zA) = ⊤ := by
    rw [eq_top_iff]
    rintro a -
    have ha : a ∈ Algebra.adjoin O ((W.gr 0 : Set W.A) ∪ Set.range W.zA) := by
      rw [gr_gen O R X W]
      trivial
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with hx | ⟨i, rfl⟩
      · have e : algebraMap (W.gr 0) W.A ⟨x, hx⟩ = x := rfl
        rw [← e]
        exact Subalgebra.algebraMap_mem _ _
      · exact Algebra.subset_adjoin ⟨i, rfl⟩
    | algebraMap r =>
      have hr : algebraMap O W.A r ∈ W.gr 0 := SetLike.algebraMap_mem_graded W.gr r
      have e : algebraMap (W.gr 0) W.A ⟨_, hr⟩ = algebraMap O W.A r := rfl
      rw [← e]
      exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
    | mul x y _ _ hx hy => exact Subalgebra.mul_mem _ hx hy
  haveI hft : Algebra.FiniteType (W.gr 0) W.A :=
    ⟨⟨Finset.univ.image W.zA, by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, hgen]⟩⟩
  refine ⟨Algebra.FiniteType.isNoetherianRing (W.gr 0) W.A, hft, ?_⟩
  intro j
  have hmono : ∀ m : W.σ →₀ ℕ, monomial m (1 : O) ∈ wtPart O W.wt (Finsupp.weight W.wt m) := by
    intro m n hn
    rw [coeff_monomial, if_neg]
    rintro rfl
    exact hn rfl
  obtain ⟨μ, hμS, hμ⟩ := part_span O R X W {n | Finsupp.weight W.wt n = j} j (fun n hn => hn)
  let mA : (W.σ →₀ ℕ) → W.A := fun m =>
    ⟨W.π (monomial m 1), W.part_le_A (Submodule.mem_map_of_mem (hmono m))⟩
  have hsj : ∀ a ∈ μ.image mA, a ∈ W.gr j := by
    intro a ha
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ha
    have hw : Finsupp.weight W.wt m = j := hμS hm
    show (W.π (monomial m 1) : R) ∈ W.part j
    rw [← hw]
    exact Submodule.mem_map_of_mem (hmono m)
  refine ⟨μ.image mA, hsj, ?_⟩
  apply le_antisymm
  · intro a ha
    have ha' : (a : R) ∈ W.part j := ha
    obtain ⟨f, hf, hfa⟩ := Submodule.mem_map.mp ha'
    obtain ⟨b, hb, hfb⟩ := hμ f (fun n hn => hf n hn)
    let bA : (W.σ →₀ ℕ) → W.A := fun m =>
      ⟨W.π (b m), W.part_le_A (Submodule.mem_map_of_mem (hb m))⟩
    have hsum : a = ∑ m ∈ μ, bA m * mA m := by
      apply Subtype.ext
      rw [← hfa]
      simp [hfb, map_sum, map_mul, bA, mA]
    rw [hsum]
    refine Submodule.sum_mem _ fun m hm => Submodule.mul_mem_mul ?_ ?_
    · show (W.π (b m) : R) ∈ W.part 0
      exact Submodule.mem_map_of_mem (hb m)
    · exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem mA hm))
  · rw [Submodule.mul_le]
    intro x hx y hy
    have hy' : y ∈ W.gr j := (Submodule.span_le.mpr fun z hz => hsj z hz) hy
    simpa using SetLike.GradedMul.mul_mem hx hy'
