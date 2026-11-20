import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgebraMapRangeSpanEqTopOfFiniteGenerators
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FinrankStructMapYRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FinrankStructMapSRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FramePointFiberNonempty
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FramePointYCoordEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FramePointAlgCoordEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrameFiberEq

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Establish `hs : Function.Surjective (MvPolynomial.aeval (R` using `k) (fun t : T => (t : Q))) := by`. Rewrite using `[← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]`. Simplify using `using ht`. Use `(ringKrullDim_le_of_surjective (MvPolynomial.aeval (R := k) (fun t : T => (t : Q))).toRingHom hs).trans ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]`.

Simplify using `only [Nat.card_eq_fintype_card, Fintype.card_coe]`. Conclude with `h` after adjusting the coercions.
-/
private theorem dim_gen (k Q : Type) [Field k] [CommRing Q] [Algebra k Q] (T : Finset Q) (m : ℕ) (h : T.card ≤ m)
    (ht : Algebra.adjoin k (T : Set Q) = ⊤) : ringKrullDim Q ≤ (m : ℕ) := by
  have hs : Function.Surjective (MvPolynomial.aeval (R := k) (fun t : T => (t : Q))) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
    simpa using ht
  refine (ringKrullDim_le_of_surjective (MvPolynomial.aeval (R := k) (fun t : T => (t : Q))).toRingHom hs).trans ?_
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
  exact_mod_cast h

/- English proof (translation)
Establish `up : ∀ g i j, i < j → ρ.r g i j = 0` using `fun g i j h => by`. Establish `: ρ.r g i j ∈ ρ.triM` using `Ideal.subset_span ⟨g, i, j, h, rfl⟩`. Rewrite `this` using `[ht, Ideal.mem_bot]`. Then use the resulting hypothesis. Establish `red : ∀ U : Subalgebra k Q, (∀ g i j, j < i → ρ.r g i j ∈ U) → ∀ g i j, ρ.r g i j ∈ U` using `fun U h g i j => by`. Break down `lt_trichotomy i j with h1 | rfl | h1` into its components or cases.

Rewrite using `[up g i j h1]`. Conclude with `zero_mem _`. Rewrite using `[hb.1]`. Conclude with `U.algebraMap_mem _`. Conclude with `h g i j h1`.

Break down `hn with rfl | rfl` into its components or cases. Take `⟨T, h1, h2⟩` from `algebraMap_range_span_eq_top_of_finite_generators (F.strS k) C₀ _ (finrank_structMapS_range hF) fun f => Frame.strS_map f (framePoint_fiber_nonempty hF Q ρ hb ht hc)`. Use `⟨T, by omega, red _ fun g i j h => ?_⟩` and prove the remaining obligations. Take `⟨rfl, rfl⟩ : i = 1 ∧ j = 0` from `by omega`. Conclude with `Algebra.span_le_adjoin k _ (h2 g)`.

Take `⟨T, h1, h2⟩` from `algebraMap_range_span_eq_top_of_finite_generators (F.strY k) C₀ _ (finrank_structMapY_range hF) fun f => Frame.strY_map f (framePoint_y_coord_eq hF Q ρ hb ht hc)`. Establish `hy : ∀ g, ρ.r g 1 0 ∈ Algebra.adjoin k (T : Set Q)` using `fun g => Algebra.span_le_adjoin k _ (h2 g)`. Take `⟨T', h3, h4⟩` from `algebraMap_range_span_eq_top_of_finite_generators (F.strS k) C₀ _ (finrank_structMapS_range hF) fun f => Frame.strS_map f (framePoint_alg_coord_eq hF Q ρ hb ht hc _ hy)`. Take `⟨σ, hσ⟩` from `(Subalgebra.toSubmodule (Algebra.adjoin k (T : Set Q))).mkQ_surjective.hasRightInverse`. Establish `hle : Algebra.adjoin k (T : Set Q) ≤ Algebra.adjoin k ((T ∪ T'.image σ : Finset Q) : Set Q)` using `Algebra.adjoin_mono (by simp)`.

Use `⟨T ∪ T'.image σ, (Finset.card_union_le _ _).trans ?_, red _ fun g i j h => ?_⟩` and prove the remaining obligations. Use `Finset.card_image_le (s := T') (f := σ)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hij : (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 1) ∨ (i = 2 ∧ j = 0)` using `by omega`. Break down `hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩` into its components or cases.

Conclude with `hle (hy g)`. Establish `h5 : ρ.r (F.star g) 1 0 = ρ.r g 2 1` using `(UpperTheory.V.Fr.star hF).2.2.2.2 ρ g 1 0`. Rewrite using `[← h5]`. Conclude with `hle (hy _)`. Establish `h5 : Submodule.span k (T' : Set _) ≤ (Subalgebra.toSubmodule (Algebra.adjoin k ((T ∪ T'.image σ : Finset Q) : Set Q))).map (Subalgebra.toSubmodule (Algebra.adjoin k (T : Set Q))).mkQ` using `Submodule.span_le.2 fun t ht' => ⟨σ t, Algebra.subset_adjoin (by`.

Simplify using `only [Finset.coe_union, Finset.coe_image]`. Conclude with `Or.inr ⟨t, ht', rfl⟩), hσ t⟩`. Take `⟨x, hx, hx'⟩` from `h5 (h4 g)`. Establish `h6 : x - ρ.r g 2 0 ∈ Algebra.adjoin k (T : Set Q)` using `(Submodule.Quotient.eq _).1 hx'`. Establish `h7` using `sub_mem (show x ∈ Algebra.adjoin k ((T ∪ T'.image σ : Finset Q) : Set Q) from hx) (hle h6)`.

Rewrite `h7` using `[sub_sub_cancel]`. Then use the resulting hypothesis.
-/
private theorem point {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}
    (hF : F.Ok C₀) (hn : n = 2 ∨ n = 3) (Q : Type) [CommRing Q] [Algebra k Q] (ρ : NRep F n Q)
    (hb : ρ.IsBar (algebraMap k Q)) (ht : ρ.triM = ⊥) (hc : ∀ i j, IsLocallyConstant fun g => ρ.r g i j) :
    ∃ T : Finset Q, T.card ≤ 2 * C₀ ∧ ∀ g i j, ρ.r g i j ∈ Algebra.adjoin k (T : Set Q) := by
  classical
  have up : ∀ g i j, i < j → ρ.r g i j = 0 := fun g i j h => by
    have : ρ.r g i j ∈ ρ.triM := Ideal.subset_span ⟨g, i, j, h, rfl⟩
    rwa [ht, Ideal.mem_bot] at this
  have red : ∀ U : Subalgebra k Q, (∀ g i j, j < i → ρ.r g i j ∈ U) → ∀ g i j, ρ.r g i j ∈ U := fun U h g i j => by
    rcases lt_trichotomy i j with h1 | rfl | h1
    · rw [up g i j h1]; exact zero_mem _
    · rw [hb.1]; exact U.algebraMap_mem _
    · exact h g i j h1
  rcases hn with rfl | rfl
  · obtain ⟨T, h1, h2⟩ := algebraMap_range_span_eq_top_of_finite_generators (F.strS k) C₀ _ (finrank_structMapS_range hF)
      fun f => Frame.strS_map f (framePoint_fiber_nonempty hF Q ρ hb ht hc)
    refine ⟨T, by omega, red _ fun g i j h => ?_⟩
    obtain ⟨rfl, rfl⟩ : i = 1 ∧ j = 0 := by omega
    exact Algebra.span_le_adjoin k _ (h2 g)
  · obtain ⟨T, h1, h2⟩ := algebraMap_range_span_eq_top_of_finite_generators (F.strY k) C₀ _ (finrank_structMapY_range hF)
      fun f => Frame.strY_map f (framePoint_y_coord_eq hF Q ρ hb ht hc)
    have hy : ∀ g, ρ.r g 1 0 ∈ Algebra.adjoin k (T : Set Q) := fun g => Algebra.span_le_adjoin k _ (h2 g)
    obtain ⟨T', h3, h4⟩ := algebraMap_range_span_eq_top_of_finite_generators (F.strS k) C₀ _ (finrank_structMapS_range hF)
      fun f => Frame.strS_map f (framePoint_alg_coord_eq hF Q ρ hb ht hc _ hy)
    obtain ⟨σ, hσ⟩ := (Subalgebra.toSubmodule (Algebra.adjoin k (T : Set Q))).mkQ_surjective.hasRightInverse
    have hle : Algebra.adjoin k (T : Set Q) ≤ Algebra.adjoin k ((T ∪ T'.image σ : Finset Q) : Set Q) :=
      Algebra.adjoin_mono (by simp)
    refine ⟨T ∪ T'.image σ, (Finset.card_union_le _ _).trans ?_, red _ fun g i j h => ?_⟩
    · have := Finset.card_image_le (s := T') (f := σ)
      omega
    have hij : (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 1) ∨ (i = 2 ∧ j = 0) := by omega
    rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hle (hy g)
    · have h5 : ρ.r (F.star g) 1 0 = ρ.r g 2 1 := (UpperTheory.V.Fr.star hF).2.2.2.2 ρ g 1 0
      rw [← h5]
      exact hle (hy _)
    · have h5 : Submodule.span k (T' : Set _) ≤ (Subalgebra.toSubmodule (Algebra.adjoin k
          ((T ∪ T'.image σ : Finset Q) : Set Q))).map (Subalgebra.toSubmodule (Algebra.adjoin k (T : Set Q))).mkQ :=
        Submodule.span_le.2 fun t ht' => ⟨σ t, Algebra.subset_adjoin (by
          simp only [Finset.coe_union, Finset.coe_image]
          exact Or.inr ⟨t, ht', rfl⟩), hσ t⟩
      obtain ⟨x, hx, hx'⟩ := h5 (h4 g)
      have h6 : x - ρ.r g 2 0 ∈ Algebra.adjoin k (T : Set Q) := (Submodule.Quotient.eq _).1 hx'
      have h7 := sub_mem (show x ∈ Algebra.adjoin k ((T ∪ T'.image σ : Finset Q) : Set Q) from hx) (hle h6)
      rwa [sub_sub_cancel] at h7

/- English proof (translation)
Introduce `l _ O _ _ _ _ F C₀ n hF hn S`. Take `⟨f, h1, h2, h3⟩` from `frame_fiber_eq hF hn S (S.x0 ⊔ S.u.triM) le_sup_left`. Use `letI : Algebra (ResidueField O) (S.A ⧸ (S.x0 ⊔ S.u.triM)) := f.toAlgebra`. Establish `ht : (S.u.map (Ideal.Quotient.mk (S.x0 ⊔ S.u.triM))).triM = ⊥`. Use `Ideal.span_eq_bot.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨g, i, j, h, rfl⟩`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.subset_span ⟨g, i, j, h, rfl⟩))`. Take `⟨T, h4, h5⟩` from `point hF hn _ _ h1 ht h2`. Use `dim_gen (ResidueField O) _ T _ h4 (eq_top_iff.2 fun x _ => ?_)` and prove the remaining obligations. Establish `h6 : Subring.closure (Set.range f ∪ {x | ∃ g i j, x = (S.u.map (Ideal.Quotient.mk (S.x0 ⊔ S.u.triM))).r g i j}) ≤ (Algebra.adjoin (ResidueField O) (T : Set (S.A ⧸ (S.x0 ⊔ S.u.triM)))).toSubring`.

Use `Subring.closure_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ (⟨a, rfl⟩ | ⟨g, i, j, rfl⟩)`. Conclude with `Subalgebra.algebraMap_mem _ a`. Conclude with `h5 g i j`. Conclude with `h6 (h3 ▸ Subring.mem_top x)`.
-/
theorem UpperTheory.V.Fr.finrank_frameSpace_eq :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ringKrullDim (S.A ⧸ (S.x0 ⊔ S.u.triM)) ≤ (2 * C₀ : ℕ) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S
  obtain ⟨f, h1, h2, h3⟩ := frame_fiber_eq hF hn S (S.x0 ⊔ S.u.triM) le_sup_left
  letI : Algebra (ResidueField O) (S.A ⧸ (S.x0 ⊔ S.u.triM)) := f.toAlgebra
  have ht : (S.u.map (Ideal.Quotient.mk (S.x0 ⊔ S.u.triM))).triM = ⊥ := by
    refine Ideal.span_eq_bot.2 ?_
    rintro _ ⟨g, i, j, h, rfl⟩
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.subset_span ⟨g, i, j, h, rfl⟩))
  obtain ⟨T, h4, h5⟩ := point hF hn _ _ h1 ht h2
  refine dim_gen (ResidueField O) _ T _ h4 (eq_top_iff.2 fun x _ => ?_)
  have h6 : Subring.closure (Set.range f ∪ {x | ∃ g i j, x = (S.u.map (Ideal.Quotient.mk (S.x0 ⊔ S.u.triM))).r g i j}) ≤
      (Algebra.adjoin (ResidueField O) (T : Set (S.A ⧸ (S.x0 ⊔ S.u.triM)))).toSubring := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨a, rfl⟩ | ⟨g, i, j, rfl⟩)
    · exact Subalgebra.algebraMap_mem _ a
    · exact h5 g i j
  exact h6 (h3 ▸ Subring.mem_top x)
