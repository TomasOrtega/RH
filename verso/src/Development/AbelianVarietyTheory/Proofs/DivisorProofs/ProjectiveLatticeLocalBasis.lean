import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiMapMemLocalSpan
open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent GlobalTheory.LatGlue
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (resG)

namespace GlobalTheory.LocFreeSub

/- English proof (translation)
Introduce `R _ _ h P hfin hproj c hc hcP q hq`. Use `haveI : Module.FinitePresentation R P := Module.finitePresentation_of_projective _ _`. Use `haveI : Module.Free (Localization.AtPrime q) (LocalizedModule q.primeCompl P) := Module.free_of_flat_of_isLocalRing`. Take `⟨r, hr, hfree, -⟩` from `Module.FinitePresentation.exists_free_localizedModule_powers q.primeCompl (LocalizedModule.mkLinearMap q.primeCompl P) (Localization.AtPrime q)`. Establish `hr0 : r ≠ 0` using `fun h0 => hr (h0 ▸ q.zero_mem)`.

Establish `hle : Submonoid.powers r ≤ nonZeroDivisors R` using `powers_le_nonZeroDivisors_of_noZeroDivisors hr0`. Set `L` to `Localization (Submonoid.powers r)`. Set `f` to `LocalizedModule.mkLinearMap (Submonoid.powers r) P`. Establish `hinj : Function.Injective (algebraMap R L)` using `IsLocalization.injective L hle`. Use `haveI : Nontrivial L := hinj.nontrivial`.

Use `haveI : Module.Finite L (LocalizedModule (Submonoid.powers r) P) := Module.Finite.of_isLocalizedModule (Submonoid.powers r) f`. Set `ι` to `Module.Free.ChooseBasisIndex L (LocalizedModule (Submonoid.powers r) P)`. Set `β` to `Module.Free.chooseBasis L (LocalizedModule (Submonoid.powers r) P)`. Establish `hlift : ∀ i, ∃ (m : P) (s : Submonoid.powers r), β i = LocalizedModule.mk m s` using `fun i => LocalizedModule.induction_on (fun m s => ⟨m, s, rfl⟩) (β i)`. Use `choose p s hps using hlift`.

Set `w : ι → Lˣ` to `fun i => (IsLocalization.map_units L (s i)).unit`. Set `β'` to `β.unitsSMul w`. Establish `hβ' : ∀ i, β' i = f (p i)`. Introduce `i`. Rewrite using `[Module.Basis.unitsSMul_apply, Units.smul_def, IsUnit.unit_spec, algebraMap_smul, hps i, LocalizedModule.smul'_mk, LocalizedModule.mkLinearMap_apply]`.

Conclude with `LocalizedModule.mk_cancel (s i) (p i)`. Use `haveI : Finite ι := Module.Finite.finite_basis β`. Use `letI : Fintype ι := Fintype.ofFinite ι`. Establish `hpR : LinearIndependent R p`. Establish `hL` using `β'.linearIndependent`.

Rewrite `hL`, the goal using `[linearIndependent_iff']`. Introduce `t g hg i hi`. Establish `h0` using `hL t (fun i => algebraMap R L (g i)) (by`. Establish `h1` using `congrArg f hg`. Rewrite `h1` using `[map_sum, map_zero]`.

Rewrite using `[← h1]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, algebraMap_smul, hβ' j]) i hi`. Conclude with `hinj (by rw [map_zero]; exact h0)`. Set `b₀ : ι → Fin h → R` to `fun i => (p i : Fin h → R)`.

Establish `hb₀ : LinearIndependent R b₀` using `hpR.map' P.subtype P.ker_subtype`. Establish `hspan : ∀ u ∈ P, ∃ n : ℕ, r ^ n • u ∈ Submodule.span R (Set.range b₀)`. Introduce `u hu`. Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples (Submonoid.powers r) (Finset.univ : Finset ι) (fun i => β'.repr (f ⟨u, hu⟩) i)`. Use `choose z hz using fun i => hd i (Finset.mem_univ i)`.

Establish `h1 : f ((d : R) • (⟨u, hu⟩ : P)) = f (∑ i, z i • p i)`. Rewrite using `[map_smul, map_sum]`. Use `conv_lhs => rw [← β'.sum_repr (f ⟨u, hu⟩)]`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, ← smul_assoc, ← hz i, algebraMap_smul, hβ' i]`. Take `⟨e, he⟩` from `IsLocalizedModule.exists_of_eq (S := Submonoid.powers r) h1`. Take `⟨k, hk⟩` from `(e * d).2`. Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `hk' : r ^ k = (e : R) * (d : R)` using `hk`.

Establish `he' : (e : R) • (d : R) • u = (e : R) • ∑ i, z i • b₀ i`. Establish `h2` using `congrArg P.subtype he`. Rewrite `h2` using `[Submonoid.smul_def, Submonoid.smul_def, map_smul, map_smul, map_smul, map_sum]`. Simplify `h2` using `only [map_smul, Submodule.subtype_apply]`. Rewrite using `[hk', mul_smul, he']`.

Conclude with `Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))`. Establish `hcard : Fintype.card ι = h`. Apply `le_antisymm` to reduce the goal to its premises. Simplify using `using hb₀.fintype_card_le_finrank`. Use `choose n hn using fun a : Fin h => hspan (c • Pi.basisFun R (Fin h) a) (hcP _)`.

Establish `hd0 : r ^ (∑ a, n a) * c ≠ 0` using `mul_ne_zero (pow_ne_zero _ hr0) hc`. Establish `hmem : ∀ a : Fin h, (r ^ (∑ a, n a) * c) • Pi.basisFun R (Fin h) a ∈ Submodule.span R (Set.range b₀)`. Introduce `a`. Take `⟨m, hm⟩` from `Nat.exists_eq_add_of_le (Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a))`. Rewrite using `[hm, add_comm, pow_add, mul_assoc, mul_smul, mul_smul]`.

Conclude with `Submodule.smul_mem _ _ (hn a)`. Establish `hli : LinearIndependent R (fun a : Fin h => (r ^ (∑ a, n a) * c) • Pi.basisFun R (Fin h) a)` using `(Pi.basisFun R (Fin h)).linearIndependent.map' ((r ^ (∑ a, n a) * c) • (LinearMap.id : (Fin h → R) →ₗ[R] (Fin h → R))) (LinearMap.ker_eq_bot.mpr (smul_right_injective (Fin h → R) hd0))`. Establish `hli' : LinearIndependent R (fun a : Fin h => (⟨_, hmem a⟩ : Submodule.span R (Set.range b₀)))` using `LinearIndependent.of_comp (Submodule.span R (Set.range b₀)).subtype hli`. Use `haveI : Module.Finite R (Submodule.span R (Set.range b₀)) := Module.Finite.span_of_finite R (Set.finite_range b₀)`. Establish `h3` using `hli'.fintype_card_le_finrank`.

Rewrite `h3` using `[finrank_span_eq_card hb₀, Fintype.card_fin]`. Then use the resulting hypothesis. Set `e : ι ≃ Fin h` to `Fintype.equivFinOfCardEq hcard`. Establish `hb : LinearIndependent R (b₀ ∘ e.symm)` using `hb₀.comp e.symm e.symm.injective`. Use `⟨r, hr, b₀ ∘ e.symm, fun l => (p (e.symm l)).2, ?_, ?_⟩` and prove the remaining obligations. Introduce `hdet`.

Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdet`. Use `hv0 (funext (Fintype.linearIndependent_iff.mp hb v ?_))` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Establish `h4` using `congrFun hv a`. Simplify `h4` using `[Matrix.mulVec, dotProduct, mul_comm]`.

Introduce `u hu`. Rewrite using `[e.symm.surjective.range_comp]`. Conclude with `hspan u hu`.
-/
theorem exists_basis_near_prime : ∀ (R : Type) [CommRing R] [IsDomain R] (h : ℕ) (P : Submodule R (Fin h → R)), Module.Finite R P → Module.Projective R P → ∀ c : R, c ≠ 0 → (∀ x : Fin h → R, c • x ∈ P) → ∀ q : Ideal R, q.IsPrime → ∃ g ∉ q, ∃ b : Fin h → Fin h → R, (∀ l, b l ∈ P) ∧ (Matrix.of fun a l => b l a).det ≠ 0 ∧ ∀ u ∈ P, ∃ n : ℕ, g ^ n • u ∈ Submodule.span R (Set.range b) := by
  intro R _ _ h P hfin hproj c hc hcP q hq
  classical
  haveI : Module.FinitePresentation R P := Module.finitePresentation_of_projective _ _
  haveI : Module.Free (Localization.AtPrime q) (LocalizedModule q.primeCompl P) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    q.primeCompl (LocalizedModule.mkLinearMap q.primeCompl P) (Localization.AtPrime q)
  have hr0 : r ≠ 0 := fun h0 => hr (h0 ▸ q.zero_mem)
  have hle : Submonoid.powers r ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hr0
  let L := Localization (Submonoid.powers r)
  let f := LocalizedModule.mkLinearMap (Submonoid.powers r) P
  have hinj : Function.Injective (algebraMap R L) := IsLocalization.injective L hle
  haveI : Nontrivial L := hinj.nontrivial
  haveI : Module.Finite L (LocalizedModule (Submonoid.powers r) P) :=
    Module.Finite.of_isLocalizedModule (Submonoid.powers r) f
  let ι := Module.Free.ChooseBasisIndex L (LocalizedModule (Submonoid.powers r) P)
  let β := Module.Free.chooseBasis L (LocalizedModule (Submonoid.powers r) P)
  have hlift : ∀ i, ∃ (m : P) (s : Submonoid.powers r), β i = LocalizedModule.mk m s := fun i =>
    LocalizedModule.induction_on (fun m s => ⟨m, s, rfl⟩) (β i)
  choose p s hps using hlift
  let w : ι → Lˣ := fun i => (IsLocalization.map_units L (s i)).unit
  let β' := β.unitsSMul w
  have hβ' : ∀ i, β' i = f (p i) := by
    intro i
    rw [Module.Basis.unitsSMul_apply, Units.smul_def, IsUnit.unit_spec, algebraMap_smul, hps i,
      LocalizedModule.smul'_mk, LocalizedModule.mkLinearMap_apply]
    exact LocalizedModule.mk_cancel (s i) (p i)
  haveI : Finite ι := Module.Finite.finite_basis β
  letI : Fintype ι := Fintype.ofFinite ι
  have hpR : LinearIndependent R p := by
    have hL := β'.linearIndependent
    rw [linearIndependent_iff'] at hL ⊢
    intro t g hg i hi
    have h0 := hL t (fun i => algebraMap R L (g i)) (by
      have h1 := congrArg f hg
      rw [map_sum, map_zero] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, algebraMap_smul, hβ' j]) i hi
    exact hinj (by rw [map_zero]; exact h0)
  let b₀ : ι → Fin h → R := fun i => (p i : Fin h → R)
  have hb₀ : LinearIndependent R b₀ := hpR.map' P.subtype P.ker_subtype
  have hspan : ∀ u ∈ P, ∃ n : ℕ, r ^ n • u ∈ Submodule.span R (Set.range b₀) := by
    intro u hu
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (Submonoid.powers r)
      (Finset.univ : Finset ι) (fun i => β'.repr (f ⟨u, hu⟩) i)
    choose z hz using fun i => hd i (Finset.mem_univ i)
    have h1 : f ((d : R) • (⟨u, hu⟩ : P)) = f (∑ i, z i • p i) := by
      rw [map_smul, map_sum]
      conv_lhs => rw [← β'.sum_repr (f ⟨u, hu⟩)]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, ← smul_assoc, ← hz i, algebraMap_smul, hβ' i]
    obtain ⟨e, he⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers r) h1
    obtain ⟨k, hk⟩ := (e * d).2
    refine ⟨k, ?_⟩
    have hk' : r ^ k = (e : R) * (d : R) := hk
    have he' : (e : R) • (d : R) • u = (e : R) • ∑ i, z i • b₀ i := by
      have h2 := congrArg P.subtype he
      rw [Submonoid.smul_def, Submonoid.smul_def, map_smul, map_smul, map_smul, map_sum] at h2
      simpa only [map_smul, Submodule.subtype_apply] using h2
    rw [hk', mul_smul, he']
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have hcard : Fintype.card ι = h := by
    apply le_antisymm
    · simpa using hb₀.fintype_card_le_finrank
    · choose n hn using fun a : Fin h => hspan (c • Pi.basisFun R (Fin h) a) (hcP _)
      have hd0 : r ^ (∑ a, n a) * c ≠ 0 := mul_ne_zero (pow_ne_zero _ hr0) hc
      have hmem : ∀ a : Fin h, (r ^ (∑ a, n a) * c) • Pi.basisFun R (Fin h) a ∈
          Submodule.span R (Set.range b₀) := by
        intro a
        obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le
          (Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a))
        rw [hm, add_comm, pow_add, mul_assoc, mul_smul, mul_smul]
        exact Submodule.smul_mem _ _ (hn a)
      have hli : LinearIndependent R
          (fun a : Fin h => (r ^ (∑ a, n a) * c) • Pi.basisFun R (Fin h) a) :=
        (Pi.basisFun R (Fin h)).linearIndependent.map'
          ((r ^ (∑ a, n a) * c) • (LinearMap.id : (Fin h → R) →ₗ[R] (Fin h → R)))
          (LinearMap.ker_eq_bot.mpr (smul_right_injective (Fin h → R) hd0))
      have hli' : LinearIndependent R
          (fun a : Fin h => (⟨_, hmem a⟩ : Submodule.span R (Set.range b₀))) :=
        LinearIndependent.of_comp (Submodule.span R (Set.range b₀)).subtype hli
      haveI : Module.Finite R (Submodule.span R (Set.range b₀)) :=
        Module.Finite.span_of_finite R (Set.finite_range b₀)
      have h3 := hli'.fintype_card_le_finrank
      rwa [finrank_span_eq_card hb₀, Fintype.card_fin] at h3
  let e : ι ≃ Fin h := Fintype.equivFinOfCardEq hcard
  have hb : LinearIndependent R (b₀ ∘ e.symm) := hb₀.comp e.symm e.symm.injective
  refine ⟨r, hr, b₀ ∘ e.symm, fun l => (p (e.symm l)).2, ?_, ?_⟩
  · intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    refine hv0 (funext (Fintype.linearIndependent_iff.mp hb v ?_))
    funext a
    have h4 := congrFun hv a
    simpa [Matrix.mulVec, dotProduct, mul_comm] using h4
  · intro u hu
    rw [e.symm.surjective.range_comp]
    exact hspan u hu

end GlobalTheory.LocFreeSub
