import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ExistsIsRegularAppendOfModDepthGE
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bridge
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne

open IsLocalRing RingTheory.Sequence Pointwise

namespace GlobalTheory.AnnRegSeq

/- English proof (translation)
Establish `hF : IsField B` using `IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm`. Use `letI := hF.toField`. Conclude with `Module.Free.of_divisionRing B M`.
-/
theorem free_of_maximalIdeal_eq_bot {B M : Type} [CommRing B] [IsLocalRing B] [AddCommGroup M]
    [Module B M] (hm : maximalIdeal B = ⊥) : Module.Free B M := by
  have hF : IsField B := IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm
  letI := hF.toField
  exact Module.Free.of_divisionRing B M

/- English proof (translation)
The claim follows from `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal B) (maximalIdeal B) (maximalIdeal B).fg_of_isNoetherianRing (by rwa [smul_eq_mul, ← pow_two]) (maximalIdeal_le_jacobson ⊥)`.
-/
theorem maximalIdeal_eq_bot_of_le_sq {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (h : maximalIdeal B ≤ maximalIdeal B ^ 2) : maximalIdeal B = ⊥ :=
  Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal B) (maximalIdeal B)
    (maximalIdeal B).fg_of_isNoetherianRing (by rwa [smul_eq_mul, ← pow_two])
    (maximalIdeal_le_jacobson ⊥)

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hsub : ((maximalIdeal B : Ideal B) : Set B) ⊆ ⋃ p ∈ insert (maximalIdeal B ^ 2) (associatedPrimes B M), (id p : Set B)`. Introduce `z hz`. Rewrite using `[Set.biUnion_insert]`.

Distinguish the cases in `h2 : z ∈ maximalIdeal B ^ 2`. Conclude with `Or.inl h2`. Use `right`. Establish `: z ∈ ({r : B | IsSMulRegular M r}ᶜ)` using `hcon z hz h2`. Rewrite `this` using `[← biUnion_associatedPrimes_eq_compl_regular B M]`. Then use the resulting hypothesis.

Take `⟨p, hp, hle⟩` from `(Ideal.subset_union_prime_finite ((associatedPrimes.finite B M).insert _) (f := id) (maximalIdeal B ^ 2) (maximalIdeal B ^ 2) (fun i hi h1 _ => by`. Break down `hi with rfl | hi` into its components or cases. Conclude with `absurd rfl h1`. Conclude with `hi.isPrime)).mp hsub`. Break down `hp with rfl | hp` into its components or cases.

Conclude with `hsq hle`. Establish `: p = maximalIdeal B` using `le_antisymm (le_maximalIdeal hp.isPrime.ne_top) hle`. Conclude with `hass (this ▸ hp)`.
-/
theorem exists_isSMulRegular_notMem_sq {B M : Type} [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [AddCommGroup M] [Module B M] [Module.Finite B M]
    (hass : maximalIdeal B ∉ associatedPrimes B M) (hsq : ¬ maximalIdeal B ≤ maximalIdeal B ^ 2) :
    ∃ x ∈ maximalIdeal B, x ∉ maximalIdeal B ^ 2 ∧ IsSMulRegular M x := by
  by_contra hcon
  push_neg at hcon
  have hsub : ((maximalIdeal B : Ideal B) : Set B) ⊆
      ⋃ p ∈ insert (maximalIdeal B ^ 2) (associatedPrimes B M), (id p : Set B) := by
    intro z hz
    rw [Set.biUnion_insert]
    by_cases h2 : z ∈ maximalIdeal B ^ 2
    · exact Or.inl h2
    · right
      have : z ∈ ({r : B | IsSMulRegular M r}ᶜ) := hcon z hz h2
      rwa [← biUnion_associatedPrimes_eq_compl_regular B M] at this
  obtain ⟨p, hp, hle⟩ := (Ideal.subset_union_prime_finite ((associatedPrimes.finite B M).insert _)
    (f := id) (maximalIdeal B ^ 2) (maximalIdeal B ^ 2) (fun i hi h1 _ => by
      rcases hi with rfl | hi
      · exact absurd rfl h1
      · exact hi.isPrime)).mp hsub
  rcases hp with rfl | hp
  · exact hsq hle
  · have : p = maximalIdeal B := le_antisymm (le_maximalIdeal hp.isPrime.ne_top) hle
    exact hass (this ▸ hp)

/- English proof (translation)
Use `set I : Ideal B := Ideal.span {x} with hI`. Use `set P : Submodule B M := I • ⊤ with hP`. Establish `hIj : I ≤ (⊥ : Ideal B).jacobson`. Rewrite using `[hI, Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `maximalIdeal_le_jacobson _ hx`.

Use `haveI : IsLocalRing (B ⧸ I) := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isLocalRing_quotient_span_singleton hx`. Use `haveI : Module.Finite (B ⧸ I) (M ⧸ P) := Module.Finite.of_restrictScalars_finite B _ _`. Set `b` to `Module.finBasis (B ⧸ I) (M ⧸ P)`. Use `set r := Module.finrank (B ⧸ I) (M ⧸ P)`. Use `choose v hv using fun i => Submodule.Quotient.mk_surjective P (b i)`.

Set `φ : (Fin r → B) →ₗ[B] M` to `Fintype.linearCombination B v`. Establish `hφ : ∀ c, φ c = ∑ i, c i • v i` using `fun c => by simp [φ, Fintype.linearCombination_apply]`. Establish `hmk : ∀ c : Fin r → B, (Submodule.Quotient.mk (φ c) : M ⧸ P) = ∑ i, Ideal.Quotient.mk I (c i) • b i`. Introduce `c`. Rewrite using `[hφ]`.

Express the relevant statement in the definitionally equal form `Submodule.mkQ P (∑ i, c i • v i) = _`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_smul, hv i, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]`. Establish `hsurj : LinearMap.range φ = ⊤`.

Use `top_le_iff.mp (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hIj ?_)` and prove the remaining obligations. Introduce `m _`. Use `choose c' hc' using fun i => Ideal.Quotient.mk_surjective (b.repr (Submodule.Quotient.mk m) i)`. Establish `h1 : (Submodule.Quotient.mk (φ c') : M ⧸ P) = Submodule.Quotient.mk m`. Rewrite using `[hmk]`.

Simplify using `only [hc']`. Conclude with `b.sum_repr _`. Rewrite `h1` using `[Submodule.Quotient.eq]`. Establish `h2 : m = φ c' - (φ c' - m)` using `by abel`. Rewrite using `[h2]`.

Conclude with `Submodule.sub_mem _ (Submodule.mem_sup_left ⟨c', rfl⟩) (Submodule.mem_sup_right h1)`. Establish `hker : LinearMap.ker φ = ⊥`. Use `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I _ (IsNoetherian.noetherian _) ?_ hIj` and prove the remaining obligations. Introduce `k hk`. Rewrite `hk` using `[LinearMap.mem_ker]`.

Establish `h0 : ∑ i, Ideal.Quotient.mk I (k i) • b i = 0`. Rewrite using `[← hmk, hk]`. Both sides reduce to the same expression. Establish `hki : ∀ i, k i ∈ I` using `fun i => Ideal.Quotient.eq_zero_iff_mem.mp ((Fintype.linearIndependent_iff.mp b.linearIndependent) _ h0 i)`. Use `choose k' hk' using fun i => Ideal.mem_span_singleton'.mp (hki i)`.

Establish `hkx : k = x • k'`. Use extensionality with `i`. Simplify using `[← hk' i, mul_comm]`. Establish `hk'ker : k' ∈ LinearMap.ker φ`. Rewrite using `[LinearMap.mem_ker]`.

Apply `reg` to reduce the goal to its premises. Use `show x • φ k' = x • 0`. Rewrite using `[smul_zero, ← map_smul, ← hkx, hk]`. Rewrite using `[hkx]`. Conclude with `Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) hk'ker`.

Conclude with `Module.Free.of_equiv (LinearEquiv.ofBijective φ ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp hsurj⟩)`.
-/
theorem free_of_free_quotient {B M : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [AddCommGroup M] [Module B M] [Module.Finite B M] {x : B} (hx : x ∈ maximalIdeal B)
    (reg : IsSMulRegular M x)
    [Module.Free (B ⧸ Ideal.span {x}) (M ⧸ Ideal.span {x} • (⊤ : Submodule B M))] :
    Module.Free B M := by
  set I : Ideal B := Ideal.span {x} with hI
  set P : Submodule B M := I • ⊤ with hP
  have hIj : I ≤ (⊥ : Ideal B).jacobson := by
    rw [hI, Ideal.span_le, Set.singleton_subset_iff]
    exact maximalIdeal_le_jacobson _ hx
  haveI : IsLocalRing (B ⧸ I) :=
    ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isLocalRing_quotient_span_singleton hx
  haveI : Module.Finite (B ⧸ I) (M ⧸ P) := Module.Finite.of_restrictScalars_finite B _ _
  let b := Module.finBasis (B ⧸ I) (M ⧸ P)
  set r := Module.finrank (B ⧸ I) (M ⧸ P)
  choose v hv using fun i => Submodule.Quotient.mk_surjective P (b i)
  let φ : (Fin r → B) →ₗ[B] M := Fintype.linearCombination B v
  have hφ : ∀ c, φ c = ∑ i, c i • v i := fun c => by simp [φ, Fintype.linearCombination_apply]
  have hmk : ∀ c : Fin r → B, (Submodule.Quotient.mk (φ c) : M ⧸ P) =
      ∑ i, Ideal.Quotient.mk I (c i) • b i := by
    intro c
    rw [hφ]
    change Submodule.mkQ P (∑ i, c i • v i) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_smul, hv i, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
  have hsurj : LinearMap.range φ = ⊤ := by
    refine top_le_iff.mp (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hIj ?_)
    intro m _
    choose c' hc' using fun i => Ideal.Quotient.mk_surjective (b.repr (Submodule.Quotient.mk m) i)
    have h1 : (Submodule.Quotient.mk (φ c') : M ⧸ P) = Submodule.Quotient.mk m := by
      rw [hmk]
      simp only [hc']
      exact b.sum_repr _
    rw [Submodule.Quotient.eq] at h1
    have h2 : m = φ c' - (φ c' - m) := by abel
    rw [h2]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨c', rfl⟩) (Submodule.mem_sup_right h1)
  have hker : LinearMap.ker φ = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I _ (IsNoetherian.noetherian _) ?_ hIj
    intro k hk
    rw [LinearMap.mem_ker] at hk
    have h0 : ∑ i, Ideal.Quotient.mk I (k i) • b i = 0 := by
      rw [← hmk, hk]
      rfl
    have hki : ∀ i, k i ∈ I := fun i =>
      Ideal.Quotient.eq_zero_iff_mem.mp ((Fintype.linearIndependent_iff.mp b.linearIndependent) _ h0 i)
    choose k' hk' using fun i => Ideal.mem_span_singleton'.mp (hki i)
    have hkx : k = x • k' := by
      ext i
      simp [← hk' i, mul_comm]
    have hk'ker : k' ∈ LinearMap.ker φ := by
      rw [LinearMap.mem_ker]
      apply reg
      show x • φ k' = x • 0
      rw [smul_zero, ← map_smul, ← hkx, hk]
    rw [hkx]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) hk'ker
  exact Module.Free.of_equiv (LinearEquiv.ofBijective φ
    ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp hsurj⟩)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `B _ _ _ M _ _ _ _ hsp`. Conclude with `free_of_maximalIdeal_eq_bot ((Submodule.spanFinrank_eq_zero_iff_eq_bot (maximalIdeal B).fg_of_isNoetherianRing).mp (by omega))`. Consider the case `succ n ih`.

Introduce `B _ _ _ M _ _ _ hd hsp`. Distinguish the cases in `hsq : maximalIdeal B ≤ maximalIdeal B ^ 2`. Conclude with `free_of_maximalIdeal_eq_bot (maximalIdeal_eq_bot_of_le_sq hsq)`. Take `⟨rs, hlen, hmem, hreg⟩` from `hd`. Take `⟨y, ys, rfl⟩` from `List.exists_cons_of_length_eq_add_one hlen`.

Establish `hy : y ∈ maximalIdeal B` using `hmem y (by simp)`. Establish `hass` using `ReciprocityTheory.CA.max_not_mem_ass_of_reg hy ((isRegular_cons_iff M y ys).mp hreg).1`. Take `⟨x, hx, hx2, hxreg⟩` from `exists_isSMulRegular_notMem_sq hass hsq`. Establish `hd'` using `ReciprocityTheory.CA.ModDepthGE.quotSMulTop hx hxreg ⟨y :: ys, hlen, hmem, hreg⟩`. Use `haveI : IsLocalRing (B ⧸ Ideal.span {x}) := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isLocalRing_quotient_span_singleton hx`.

Use `haveI : Module.Finite (B ⧸ Ideal.span {x}) (M ⧸ Ideal.span {x} • (⊤ : Submodule B M)) := Module.Finite.of_restrictScalars_finite B _ _`. Establish `hsp' : (maximalIdeal (B ⧸ Ideal.span {x})).spanFinrank ≤ n`. Establish `h1` using `ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.spanFinrank_maximalIdeal_quotient_succ_le B hx hx2`. Rewrite `h1` using `[← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]`. Use linear arithmetic over natural numbers and integers.

Establish `hd'' : ReciprocityTheory.CA.ModDepthGE (B ⧸ Ideal.span {x}) (M ⧸ Ideal.span {x} • (⊤ : Submodule B M)) n`. Take `⟨zs, hzl, hzm, hzr⟩` from `hd'`. Set `e : QuotSMulTop x M ≃ₗ[B] M ⧸ Ideal.span {x} • (⊤ : Submodule B M)` to `Submodule.quotEquivOfEq _ _ (Submodule.ideal_span_singleton_smul x ⊤).symm`. Use `⟨zs.map (Ideal.Quotient.mk _), by simp [hzl], ?_, ?_⟩` and prove the remaining obligations. Introduce `r hr`.

Take `⟨z, hz, rfl⟩` from `List.mem_map.mp hr`. Conclude with `ReciprocityTheory.CA.mk_mem_maximalIdeal_quot _ (hzm z hz)`. Rewrite using `[← Ideal.Quotient.algebraMap_eq]`. Conclude with `(ReciprocityTheory.CA.isRegular_map_algebraMap_iff' zs).mpr ((e.isRegular_congr zs).mp hzr)`. Use `haveI := ih (B ⧸ Ideal.span {x}) (M ⧸ Ideal.span {x} • (⊤ : Submodule B M)) hd'' hsp'`.

Conclude with `free_of_free_quotient hx hxreg`.
-/
theorem free_of_modDepthGE (n : ℕ) : ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (M : Type) [AddCommGroup M] [Module B M] [Module.Finite B M],
    ReciprocityTheory.CA.ModDepthGE B M n → (maximalIdeal B).spanFinrank ≤ n → Module.Free B M := by
  induction n with
  | zero =>
    intro B _ _ _ M _ _ _ _ hsp
    exact free_of_maximalIdeal_eq_bot ((Submodule.spanFinrank_eq_zero_iff_eq_bot
      (maximalIdeal B).fg_of_isNoetherianRing).mp (by omega))
  | succ n ih =>
    intro B _ _ _ M _ _ _ hd hsp
    by_cases hsq : maximalIdeal B ≤ maximalIdeal B ^ 2
    · exact free_of_maximalIdeal_eq_bot (maximalIdeal_eq_bot_of_le_sq hsq)
    obtain ⟨rs, hlen, hmem, hreg⟩ := hd
    obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    have hy : y ∈ maximalIdeal B := hmem y (by simp)
    have hass := ReciprocityTheory.CA.max_not_mem_ass_of_reg hy ((isRegular_cons_iff M y ys).mp hreg).1
    obtain ⟨x, hx, hx2, hxreg⟩ := exists_isSMulRegular_notMem_sq hass hsq
    have hd' := ReciprocityTheory.CA.ModDepthGE.quotSMulTop hx hxreg ⟨y :: ys, hlen, hmem, hreg⟩
    haveI : IsLocalRing (B ⧸ Ideal.span {x}) :=
      ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isLocalRing_quotient_span_singleton hx
    haveI : Module.Finite (B ⧸ Ideal.span {x}) (M ⧸ Ideal.span {x} • (⊤ : Submodule B M)) :=
      Module.Finite.of_restrictScalars_finite B _ _
    have hsp' : (maximalIdeal (B ⧸ Ideal.span {x})).spanFinrank ≤ n := by
      have h1 :=
        ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.spanFinrank_maximalIdeal_quotient_succ_le B hx hx2
      rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace] at h1
      omega
    have hd'' : ReciprocityTheory.CA.ModDepthGE (B ⧸ Ideal.span {x})
        (M ⧸ Ideal.span {x} • (⊤ : Submodule B M)) n := by
      obtain ⟨zs, hzl, hzm, hzr⟩ := hd'
      let e : QuotSMulTop x M ≃ₗ[B] M ⧸ Ideal.span {x} • (⊤ : Submodule B M) :=
        Submodule.quotEquivOfEq _ _ (Submodule.ideal_span_singleton_smul x ⊤).symm
      refine ⟨zs.map (Ideal.Quotient.mk _), by simp [hzl], ?_, ?_⟩
      · intro r hr
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hr
        exact ReciprocityTheory.CA.mk_mem_maximalIdeal_quot _ (hzm z hz)
      · rw [← Ideal.Quotient.algebraMap_eq]
        exact (ReciprocityTheory.CA.isRegular_map_algebraMap_iff' zs).mpr ((e.isRegular_congr zs).mp hzr)
    haveI := ih (B ⧸ Ideal.span {x}) (M ⧸ Ideal.span {x} • (⊤ : Submodule B M)) hd'' hsp'
    exact free_of_free_quotient hx hxreg

end GlobalTheory.AnnRegSeq
