import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSystemOfParametersInsert
open IsLocalRing UpperTheory.V.Alg

/- English proof (translation)
Establish `key : ∀ N : ℕ, ∃ F : Submodule A S, F.FG ∧ F ⊔ (I ^ N).restrictScalars A = ⊤`. Introduce `N`. Proceed by induction on `N with`. Consider the case `zero => exact ⟨⊥, Submodule.fg_bot, by simp⟩`. Consider the case `succ N ih`.

Take `⟨F, hF, hF'⟩` from `ih`. Take `⟨G, hG⟩ : (I ^ N).FG` from `IsNoetherian.noetherian _`. Use `⟨F ⊔ Submodule.span A (G : Set S), hF.sup (Submodule.fg_span G.finite_toSet), ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← hF', sup_assoc]`. Use `sup_le_sup_left (fun x hx => ?_) _` and prove the remaining obligations.

Establish `hx' : x ∈ Submodule.span S (G : Set S)` using `hG.ge hx`. Take `⟨c, -, rfl⟩` from `Submodule.mem_span_finset.1 hx'`. Use `sum_mem fun y hy => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `h (c y)`. Establish `: c y • y = a • y + y * (c y - algebraMap A S a)`.

Rewrite using `[Algebra.smul_def a, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Use `Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span hy)) ?_` and prove the remaining obligations. Rewrite using `[pow_succ]`.

Conclude with `Ideal.mul_mem_mul (hG.le (Ideal.subset_span hy)) ha`. Take `⟨F, hF, hF'⟩` from `key N`. Establish `: Module.Finite A F` using `Module.Finite.iff_fg.2 hF`. Use `Module.Finite.of_surjective ((Ideal.Quotient.mkₐ A J).toLinearMap ∘ₗ F.subtype) fun s => ?_` and prove the remaining obligations. Take `⟨s, rfl⟩` from `Ideal.Quotient.mk_surjective s`.

Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 (hF'.ge (Submodule.mem_top (x := s)))`. Conclude with `⟨⟨y, hy⟩, Ideal.Quotient.eq.2 (by simpa using hN hz)⟩`.
-/
private theorem finite_quotient_of_pow_le {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    [IsNoetherianRing S] {I J : Ideal S} (h : ∀ s : S, ∃ a : A, s - algebraMap A S a ∈ I) {N : ℕ}
    (hN : I ^ N ≤ J) : Module.Finite A (S ⧸ J) := by
  have key : ∀ N : ℕ, ∃ F : Submodule A S, F.FG ∧ F ⊔ (I ^ N).restrictScalars A = ⊤ := by
    intro N
    induction N with
    | zero => exact ⟨⊥, Submodule.fg_bot, by simp⟩
    | succ N ih =>
      obtain ⟨F, hF, hF'⟩ := ih
      obtain ⟨G, hG⟩ : (I ^ N).FG := IsNoetherian.noetherian _
      refine ⟨F ⊔ Submodule.span A (G : Set S), hF.sup (Submodule.fg_span G.finite_toSet), ?_⟩
      rw [eq_top_iff, ← hF', sup_assoc]
      refine sup_le_sup_left (fun x hx => ?_) _
      have hx' : x ∈ Submodule.span S (G : Set S) := hG.ge hx
      obtain ⟨c, -, rfl⟩ := Submodule.mem_span_finset.1 hx'
      refine sum_mem fun y hy => ?_
      obtain ⟨a, ha⟩ := h (c y)
      have : c y • y = a • y + y * (c y - algebraMap A S a) := by
        rw [Algebra.smul_def a, smul_eq_mul]; ring
      rw [this]
      refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span hy)) ?_
      rw [pow_succ]
      exact Ideal.mul_mem_mul (hG.le (Ideal.subset_span hy)) ha
  obtain ⟨F, hF, hF'⟩ := key N
  have : Module.Finite A F := Module.Finite.iff_fg.2 hF
  refine Module.Finite.of_surjective ((Ideal.Quotient.mkₐ A J).toLinearMap ∘ₗ F.subtype) fun s => ?_
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hF'.ge (Submodule.mem_top (x := s)))
  exact ⟨⟨y, hy⟩, Ideal.Quotient.eq.2 (by simpa using hN hz)⟩

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `r hr`. Assume the negation of the conclusion as `hr0`. Use `letI : Algebra (A ⧸ Ideal.span {r}) S := (Ideal.Quotient.lift (Ideal.span {r}) (algebraMap A S) (fun a ha => by`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton.1 ha`.

Rewrite using `[map_mul, hr, zero_mul])).toAlgebra`. Use `haveI : IsScalarTower A (A ⧸ Ideal.span {r}) S := .of_algebraMap_eq fun _ => rfl`. Use `haveI : Module.Finite (A ⧸ Ideal.span {r}) S := Module.Finite.of_restrictScalars_finite A _ _`. Establish `h1 : ringKrullDim S ≤ ringKrullDim (A ⧸ Ideal.span {r})` using `Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap (A ⧸ Ideal.span {r}) S)) fun _ _ hpq => Ideal.IsIntegral.comap_lt_comap (R := A ⧸ Ideal.span {r}) hpq`. Establish `h2` using `ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk (Ideal.span {r})) Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_of_ne_zero hr0) (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self r))`.

Establish `h3 : ringKrullDim S + 1 ≤ ringKrullDim A` using `(add_le_add_left h1 1).trans h2`. Rewrite `h3` using `[hA, hS]`. Normalize the coercions in `at h3`. Use linear arithmetic over natural numbers and integers.
-/
private theorem injective_of_ringKrullDim_eq {A S : Type} [CommRing A] [IsDomain A] [CommRing S]
    [Algebra A S] [Module.Finite A S] {n : ℕ} (hA : ringKrullDim A = n) (hS : ringKrullDim S = n) :
    Function.Injective (algebraMap A S) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra hr0
  letI : Algebra (A ⧸ Ideal.span {r}) S :=
    (Ideal.Quotient.lift (Ideal.span {r}) (algebraMap A S) (fun a ha => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 ha
      rw [map_mul, hr, zero_mul])).toAlgebra
  haveI : IsScalarTower A (A ⧸ Ideal.span {r}) S := .of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite (A ⧸ Ideal.span {r}) S := Module.Finite.of_restrictScalars_finite A _ _
  have h1 : ringKrullDim S ≤ ringKrullDim (A ⧸ Ideal.span {r}) :=
    Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap (A ⧸ Ideal.span {r}) S))
      fun _ _ hpq => Ideal.IsIntegral.comap_lt_comap (R := A ⧸ Ideal.span {r}) hpq
  have h2 := ringKrullDim_succ_le_of_surjective
    (Ideal.Quotient.mk (Ideal.span {r})) Ideal.Quotient.mk_surjective
    (mem_nonZeroDivisors_of_ne_zero hr0)
    (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self r))
  have h3 : ringKrullDim S + 1 ≤ ringKrullDim A := (add_le_add_left h1 1).trans h2
  rw [hA, hS] at h3
  norm_cast at h3
  omega

open MvPowerSeries GlobalTheory in
/- English proof (translation)
Introduce `O S _ _ _ _ _ _ _ hS x`. Establish `hc : IsAdicComplete (maximalIdeal S) S` using `IsCO.complete (O := O)`. Establish `hl : IsLocalHom (algebraMap O S)` using `IsCO.isLocalHom`. Establish `hn : IsNoetherianRing S` using `hS.toIsNoetherian`. Take `⟨p, hp⟩` from `IsDiscreteValuationRing.exists_irreducible O`.

Establish `hm` using `hp.maximalIdeal_eq`. Establish `hloc : ∀ a ∈ maximalIdeal O, algebraMap O S a ∈ maximalIdeal S` using `fun a ha h => ha (IsLocalHom.map_nonunit a h)`. Establish `hpm : p ∈ maximalIdeal O` using `hm ▸ Ideal.mem_span_singleton_self p`. Establish `hp0 : algebraMap O S p ≠ 0` using `fun h => hp.ne_zero (by simpa using congrArg x h)`. Establish `hx : ∀ s ∈ maximalIdeal S, x s ∈ maximalIdeal O` using `fun s hs => by`.

Rewrite using `[← res_eq_zero_iff O O, res_map, res_eq_zero_iff]`. Conclude with `hs`. Take `⟨n, y, hy, hd, N, hN⟩` from `GlobalTheory.exists_systemOfParameters_insert S _ hp0 (hloc p hpm)`. Set `z : Fin n → S` to `fun i => y i - algebraMap O S (x (y i))`. Establish `hz : ∀ i, z i ∈ maximalIdeal S` using `fun i => sub_mem (hy i) (hloc _ (hx _ (hy i)))`.

Set `A` to `MvPowerSeries (Fin n) O`. Set `φ : A →ₐ[O] S` to `mvEvalAdic O (maximalIdeal S) z hz`. Establish `hφX : ∀ i, φ (X i) = z i` using `fun i => mvEvalAdic_X _ z hz i`. Use `letI : Algebra A S := φ.toRingHom.toAlgebra`. Establish `: IsDomain A` using `NoZeroDivisors.to_isDomain _`.

Establish `hA : IsAdicComplete (maximalIdeal A) A` using `(co_mvps O O (Fin n)).complete`. Establish `hle : (maximalIdeal A).map (algebraMap A S) ≤ maximalIdeal S`. Use `Ideal.map_le_iff_le_comap.2 fun g hg => ?_` and prove the remaining obligations. Establish `h4` using `algHom_sub_constantCoeff_mem φ (K := maximalIdeal S) (fun j => hφX j ▸ hz j) g`. Establish `h5` using `FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hg`.

Establish `h7` using `add_mem h4 (hloc _ h5)`. Rewrite `h7` using `[sub_add_cancel]`. Then use the resulting hypothesis. Establish `hC : ∀ a : O, algebraMap A S (C a) = algebraMap O S a` using `fun a => mvEvalAdic_C _ z hz a`. Establish `hCm : ∀ a ∈ maximalIdeal O, algebraMap O S a ∈ (maximalIdeal A).map (algebraMap A S)` using `fun a ha => hC a ▸ Ideal.mem_map_of_mem (algebraMap A S) (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simpa using ha))`. Establish `hge : maximalIdeal S ^ N ≤ (maximalIdeal A).map (algebraMap A S)`.

Use `hN.trans (Ideal.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ (rfl | ⟨i, rfl⟩)`. Conclude with `hCm p hpm`. Establish `h1 : z i ∈ (maximalIdeal A).map (algebraMap A S)`. Rewrite using `[← hφX i]`.

Conclude with `Ideal.mem_map_of_mem (algebraMap A S) (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp))`. Establish `h2` using `add_mem h1 (hCm _ (hx _ (hy i)))`. Simplify `h2` using `[z]`. Establish `: IsHausdorff ((maximalIdeal A).map (algebraMap A S)) S` using `IsHausdorff.of_isLocalRing _ _ (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hle)`. Establish `: Module.Finite A (S ⧸ (maximalIdeal A).map (algebraMap A S))`.

Use `finite_quotient_of_pow_le (fun s => ?_) hge` and prove the remaining obligations. Take `⟨a, h⟩` from `IsCO.res_surj (O := O) s`. Conclude with `⟨C a, by rwa [hC]⟩`. Establish `hfin : Module.Finite A S` using `FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal A)`. Establish `hd' : ringKrullDim S = (n + 1 : ℕ)` using `by rw [hd]; norm_cast`.

Use `⟨n, φ, injective_of_ringKrullDim_eq (A := A) (n := n + 1) ?_ hd', hfin, hd', fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[FormalIsogeny.ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one, Nat.card_eq_fintype_card, Fintype.card_fin, add_comm]`. Use `norm_cast`. Establish `h` using `algHom_sub_constantCoeff_mem (x.comp φ) (K := ⊥) (fun j => by`. Simplify using `[hφX, z]) g`.

Simplify `h` using `[sub_eq_zero]`.
-/
theorem UpperTheory.exists_finite_injective_mvPowerSeries_compatible_section :
    ∀ (O S : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CommRing S] [IsDomain S] [Algebra O S] [IsCO O S] (x : S →ₐ[O] O), ∃ (d : ℕ) (F : MvPowerSeries (Fin d) O →ₐ[O] S), Function.Injective F ∧ F.toRingHom.Finite ∧ ringKrullDim S = (d + 1 : ℕ) ∧ ∀ g, x (F g) = MvPowerSeries.constantCoeff g := by
  intro O S _ _ _ _ _ _ _ hS x
  have hc : IsAdicComplete (maximalIdeal S) S := IsCO.complete (O := O)
  have hl : IsLocalHom (algebraMap O S) := IsCO.isLocalHom
  have hn : IsNoetherianRing S := hS.toIsNoetherian
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hm := hp.maximalIdeal_eq
  have hloc : ∀ a ∈ maximalIdeal O, algebraMap O S a ∈ maximalIdeal S :=
    fun a ha h => ha (IsLocalHom.map_nonunit a h)
  have hpm : p ∈ maximalIdeal O := hm ▸ Ideal.mem_span_singleton_self p
  have hp0 : algebraMap O S p ≠ 0 := fun h => hp.ne_zero (by simpa using congrArg x h)
  have hx : ∀ s ∈ maximalIdeal S, x s ∈ maximalIdeal O := fun s hs => by
    rw [← res_eq_zero_iff O O, res_map, res_eq_zero_iff]
    exact hs
  obtain ⟨n, y, hy, hd, N, hN⟩ := GlobalTheory.exists_systemOfParameters_insert S _ hp0 (hloc p hpm)
  let z : Fin n → S := fun i => y i - algebraMap O S (x (y i))
  have hz : ∀ i, z i ∈ maximalIdeal S := fun i => sub_mem (hy i) (hloc _ (hx _ (hy i)))
  let A := MvPowerSeries (Fin n) O
  let φ : A →ₐ[O] S := mvEvalAdic O (maximalIdeal S) z hz
  have hφX : ∀ i, φ (X i) = z i := fun i => mvEvalAdic_X _ z hz i
  letI : Algebra A S := φ.toRingHom.toAlgebra
  have : IsDomain A := NoZeroDivisors.to_isDomain _
  have hA : IsAdicComplete (maximalIdeal A) A := (co_mvps O O (Fin n)).complete
  have hle : (maximalIdeal A).map (algebraMap A S) ≤ maximalIdeal S := by
    refine Ideal.map_le_iff_le_comap.2 fun g hg => ?_
    have h4 := algHom_sub_constantCoeff_mem φ (K := maximalIdeal S)
      (fun j => hφX j ▸ hz j) g
    have h5 := FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hg
    have h7 := add_mem h4 (hloc _ h5)
    rwa [sub_add_cancel] at h7
  have hC : ∀ a : O, algebraMap A S (C a) = algebraMap O S a := fun a => mvEvalAdic_C _ z hz a
  have hCm : ∀ a ∈ maximalIdeal O, algebraMap O S a ∈ (maximalIdeal A).map (algebraMap A S) :=
    fun a ha => hC a ▸ Ideal.mem_map_of_mem (algebraMap A S)
      (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simpa using ha))
  have hge : maximalIdeal S ^ N ≤ (maximalIdeal A).map (algebraMap A S) := by
    refine hN.trans (Ideal.span_le.2 ?_)
    rintro _ (rfl | ⟨i, rfl⟩)
    · exact hCm p hpm
    · have h1 : z i ∈ (maximalIdeal A).map (algebraMap A S) := by
        rw [← hφX i]
        exact Ideal.mem_map_of_mem (algebraMap A S)
          (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp))
      have h2 := add_mem h1 (hCm _ (hx _ (hy i)))
      simpa [z] using h2
  have : IsHausdorff ((maximalIdeal A).map (algebraMap A S)) S :=
    IsHausdorff.of_isLocalRing _ _ (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hle)
  have : Module.Finite A (S ⧸ (maximalIdeal A).map (algebraMap A S)) := by
    refine finite_quotient_of_pow_le (fun s => ?_) hge
    obtain ⟨a, h⟩ := IsCO.res_surj (O := O) s
    exact ⟨C a, by rwa [hC]⟩
  have hfin : Module.Finite A S := FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal A)
  have hd' : ringKrullDim S = (n + 1 : ℕ) := by rw [hd]; norm_cast
  refine ⟨n, φ, injective_of_ringKrullDim_eq (A := A) (n := n + 1) ?_ hd', hfin, hd', fun g => ?_⟩
  · rw [FormalIsogeny.ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one,
      Nat.card_eq_fintype_card, Fintype.card_fin, add_comm]
    norm_cast
  · have h := algHom_sub_constantCoeff_mem (x.comp φ) (K := ⊥) (fun j => by
      simp [hφX, z]) g
    simpa [sub_eq_zero] using h
