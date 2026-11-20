import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.FibreComp

/- English proof (translation)
Establish `hqp : q.IsPrime` using `hq.1.1`. Use `⟨⟨hqp, (Ideal.span_singleton_le_iff_mem q).2 hb⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `p ⟨hp, hbp⟩ hpq`. Assume the negation of the conclusion as `hne`. Establish `hlt : p < q` using `lt_of_le_of_ne hpq (fun h => hne (h ▸ le_rfl))`.

Establish `hbp' : b ∈ p` using `(Ideal.span_singleton_le_iff_mem p).1 hbp`. Establish `hbot : (⊥ : Ideal T) < p`. Use `bot_lt_iff_ne_bot.2 (fun h => hb0 ?_)` and prove the remaining obligations. Rewrite `hbp'` using `[h]`. Conclude with `(Submodule.mem_bot T).1 hbp'`.

Use `haveI : (Ideal.span {a}).IsPrincipal := ⟨⟨a, rfl⟩⟩`. Use `haveI := hqp`. Use `haveI := hp`. Establish `h1 : q.height ≤ ((1 : ℕ) : ℕ∞)`. Use `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {a}) q hq` as an intermediate fact.

Conclude with `this` after adjusting the coercions. Establish `hp1 : p.height < ((1 : ℕ) : ℕ∞)` using `(Ideal.height_le_iff.mp h1) p hp hlt`. Establish `hp0 : p.height ≤ ((0 : ℕ) : ℕ∞)`. Establish `h' : p.height < 1` using `by exact_mod_cast hp1`. Rewrite using `[Order.lt_one_iff.mp h']`.

Simplify using the standard rewrite rules. Establish `h2` using `(Ideal.height_le_iff.mp hp0) ⊥ Ideal.isPrime_bot hbot`. Simplify using `at h2`.
-/
theorem mem_minimalPrimes_span_of_mem {T : Type} [CommRing T] [IsDomain T] [IsNoetherianRing T]
    {q : Ideal T} {a b : T} (hq : q ∈ (Ideal.span {a}).minimalPrimes) (hb : b ∈ q) (hb0 : b ≠ 0) :
    q ∈ (Ideal.span {b}).minimalPrimes := by
  have hqp : q.IsPrime := hq.1.1
  refine ⟨⟨hqp, (Ideal.span_singleton_le_iff_mem q).2 hb⟩, ?_⟩
  rintro p ⟨hp, hbp⟩ hpq
  by_contra hne
  have hlt : p < q := lt_of_le_of_ne hpq (fun h => hne (h ▸ le_rfl))
  have hbp' : b ∈ p := (Ideal.span_singleton_le_iff_mem p).1 hbp
  have hbot : (⊥ : Ideal T) < p := by
    refine bot_lt_iff_ne_bot.2 (fun h => hb0 ?_)
    rw [h] at hbp'
    exact (Submodule.mem_bot T).1 hbp'
  haveI : (Ideal.span {a}).IsPrincipal := ⟨⟨a, rfl⟩⟩
  haveI := hqp
  haveI := hp
  have h1 : q.height ≤ ((1 : ℕ) : ℕ∞) := by
    have := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {a}) q hq
    exact_mod_cast this
  have hp1 : p.height < ((1 : ℕ) : ℕ∞) := (Ideal.height_le_iff.mp h1) p hp hlt
  have hp0 : p.height ≤ ((0 : ℕ) : ℕ∞) := by
    have h' : p.height < 1 := by exact_mod_cast hp1
    rw [Order.lt_one_iff.mp h']
    simp
  have h2 := (Ideal.height_le_iff.mp hp0) ⊥ Ideal.isPrime_bot hbot
  simp at h2

/- English proof (translation)
Establish `hπ : Function.Surjective (Ideal.Quotient.mk P)` using `Ideal.Quotient.mk_surjective`. Establish `hcomap : ∀ x : S, Ideal.comap (Ideal.Quotient.mk P) (Ideal.span {Ideal.Quotient.mk P x}) = P ⊔ Ideal.span {x}`. Introduce `x`. Establish `hx : Ideal.span {Ideal.Quotient.mk P x} = Ideal.map (Ideal.Quotient.mk P) (Ideal.span {x})`. Rewrite using `[Ideal.map_span, Set.image_singleton]`.

Rewrite using `[hx, Ideal.comap_map_of_surjective' _ hπ, Ideal.mk_ker, sup_comm]`. Rewrite `hW` using `[← hcomap f, Ideal.comap_minimalPrimes_eq_of_surjective hπ]`. Take `⟨W', hW', rfl⟩` from `hW`. Rewrite using `[← hcomap b, Ideal.comap_minimalPrimes_eq_of_surjective hπ]`. Use `⟨W', ?_, rfl⟩` and prove the remaining obligations.

Establish `hbW' : Ideal.Quotient.mk P b ∈ W'` using `hb`. Establish `hb0 : Ideal.Quotient.mk P b ≠ 0` using `fun h => hbP (Ideal.Quotient.eq_zero_iff_mem.mp h)`. Conclude with `mem_minimalPrimes_span_of_mem hW' hbW' hb0`.
-/
theorem mem_minimalPrimes_sup_of_mem {S : Type} [CommRing S] [IsNoetherianRing S] {P W : Ideal S}
    [P.IsPrime] {f b : S} (hW : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes) (hb : b ∈ W) (hbP : b ∉ P) :
    W ∈ (P ⊔ Ideal.span {b}).minimalPrimes := by
  have hπ : Function.Surjective (Ideal.Quotient.mk P) := Ideal.Quotient.mk_surjective
  have hcomap : ∀ x : S, Ideal.comap (Ideal.Quotient.mk P) (Ideal.span {Ideal.Quotient.mk P x}) =
      P ⊔ Ideal.span {x} := by
    intro x
    have hx : Ideal.span {Ideal.Quotient.mk P x} = Ideal.map (Ideal.Quotient.mk P) (Ideal.span {x}) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [hx, Ideal.comap_map_of_surjective' _ hπ, Ideal.mk_ker, sup_comm]
  rw [← hcomap f, Ideal.comap_minimalPrimes_eq_of_surjective hπ] at hW
  obtain ⟨W', hW', rfl⟩ := hW
  rw [← hcomap b, Ideal.comap_minimalPrimes_eq_of_surjective hπ]
  refine ⟨W', ?_, rfl⟩
  have hbW' : Ideal.Quotient.mk P b ∈ W' := hb
  have hb0 : Ideal.Quotient.mk P b ≠ 0 := fun h => hbP (Ideal.Quotient.eq_zero_iff_mem.mp h)
  exact mem_minimalPrimes_span_of_mem hW' hbW' hb0

/- English proof (translation)
Use `haveI : IsNoetherianRing (Localization.AtPrime W) := IsLocalization.isNoetherianRing W.primeCompl _ inferInstance`. Rewrite using `[Ne, ENat.toNat_eq_zero, not_or]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Module.length_eq_zero_iff]`. Introduce `hsub`.

Establish `h10 : (LocalizedModule.mk (1 : S ⧸ J) (1 : W.primeCompl) : LocalizedModule W.primeCompl (S ⧸ J)) = LocalizedModule.mk 0 1` using `Subsingleton.elim _ _`. Rewrite `h10` using `[LocalizedModule.mk_eq]`. Take `⟨u, hu⟩` from `h10`. Simplify using `only [one_smul, smul_zero] at hu`. Establish `hu' : (u : S) ∈ J`.

Rewrite `hu` using `[Submonoid.smul_def, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp hu`. Conclude with `u.2 (hW.1.2 hu')`. Use `set JA : Ideal (Localization.AtPrime W) := J.map (algebraMap S (Localization.AtPrime W)) with hJA`. Establish `hm : IsLocalRing.maximalIdeal (Localization.AtPrime W) ∈ JA.minimalPrimes`.

Rewrite using `[hJA, IsLocalization.minimalPrimes_map W.primeCompl (Localization.AtPrime W) J, Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]`. Conclude with `hW`. Use `haveI : Ring.KrullDimLE 0 (Localization.AtPrime W ⧸ JA) := by`. Rewrite using `[Ring.krullDimLE_zero_iff]`. Introduce `I hI`.

Establish `hQ : (I.comap (Ideal.Quotient.mk JA)).IsPrime` using `Ideal.comap_isPrime _ I`. Establish `hJQ : JA ≤ I.comap (Ideal.Quotient.mk JA)`. Introduce `x hx`. Rewrite using `[Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]`. Conclude with `I.zero_mem`.

Establish `hQm : I.comap (Ideal.Quotient.mk JA) ≤ IsLocalRing.maximalIdeal _` using `IsLocalRing.le_maximalIdeal hQ.ne_top`. Establish `hmQ` using `hm.2 ⟨hQ, hJQ⟩ hQm`. Establish `hIeq : I = Ideal.map (Ideal.Quotient.mk JA) (IsLocalRing.maximalIdeal _)`. Rewrite using `[← le_antisymm hQm hmQ, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]`. Break down `Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk JA) Ideal.Quotient.mk_surjective (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime W)) with h | h` into its components or cases.

Conclude with `absurd (hIeq.trans h) hI.ne_top`. Rewrite using `[hIeq]`. Conclude with `h`. Use `haveI : IsArtinianRing (Localization.AtPrime W ⧸ JA) := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero`. Establish `hlenQ : Module.length (Localization.AtPrime W) (Localization.AtPrime W ⧸ JA) ≠ ⊤`.

Rewrite using `[Module.length_eq_of_surjective (S := Localization.AtPrime W) (R := Localization.AtPrime W ⧸ JA) (M := Localization.AtPrime W ⧸ JA) (by rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective)]`. Conclude with `Module.length_ne_top`. Set `x : LocalizedModule W.primeCompl (S ⧸ J)` to `LocalizedModule.mk 1 1`. Set `g : Localization.AtPrime W →ₗ[Localization.AtPrime W] LocalizedModule W.primeCompl (S ⧸ J)` to `LinearMap.toSpanSingleton _ _ x`. Establish `hker : JA ≤ LinearMap.ker g`.

Rewrite using `[hJA, Ideal.map_le_iff_le_comap]`. Introduce `j hj`. Rewrite using `[Ideal.mem_comap, LinearMap.mem_ker]`. Use `show (algebraMap S (Localization.AtPrime W) j) • x = 0`. Rewrite using `[← Localization.mk_one_eq_algebraMap, LocalizedModule.mk_smul_mk, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hj, LocalizedModule.zero_mk]`.

Establish `hsurj : Function.Surjective (JA.liftQ g hker)`. Introduce `y`. Use `LocalizedModule.induction_on (fun m s => ?_) y` and prove the remaining obligations. Take `⟨t, rfl⟩` from `Ideal.Quotient.mk_surjective m`. Use `⟨Submodule.Quotient.mk (Localization.mk t s), ?_⟩` and prove the remaining obligations.

Rewrite using `[Submodule.liftQ_apply]`. Use `show Localization.mk t s • x = _`. Rewrite using `[LocalizedModule.mk_smul_mk, Algebra.smul_def, mul_one, mul_one, Ideal.Quotient.algebraMap_eq]`. Conclude with `ne_top_of_le_ne_top hlenQ (Module.length_le_of_surjective _ hsurj)`.
-/
theorem length_toNat_ne_zero {S : Type} [CommRing S] [IsNoetherianRing S] {J W : Ideal S}
    [hWp : W.IsPrime] (hW : W ∈ J.minimalPrimes) :
    (Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (S ⧸ J))).toNat ≠ 0 := by
  classical
  haveI : IsNoetherianRing (Localization.AtPrime W) :=
    IsLocalization.isNoetherianRing W.primeCompl _ inferInstance
  rw [Ne, ENat.toNat_eq_zero, not_or]
  refine ⟨?_, ?_⟩
  · rw [Module.length_eq_zero_iff]
    intro hsub
    have h10 : (LocalizedModule.mk (1 : S ⧸ J) (1 : W.primeCompl) :
        LocalizedModule W.primeCompl (S ⧸ J)) = LocalizedModule.mk 0 1 := Subsingleton.elim _ _
    rw [LocalizedModule.mk_eq] at h10
    obtain ⟨u, hu⟩ := h10
    simp only [one_smul, smul_zero] at hu
    have hu' : (u : S) ∈ J := by
      rw [Submonoid.smul_def, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq] at hu
      exact Ideal.Quotient.eq_zero_iff_mem.mp hu
    exact u.2 (hW.1.2 hu')
  · set JA : Ideal (Localization.AtPrime W) := J.map (algebraMap S (Localization.AtPrime W)) with hJA
    have hm : IsLocalRing.maximalIdeal (Localization.AtPrime W) ∈ JA.minimalPrimes := by
      rw [hJA, IsLocalization.minimalPrimes_map W.primeCompl (Localization.AtPrime W) J,
        Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]
      exact hW
    haveI : Ring.KrullDimLE 0 (Localization.AtPrime W ⧸ JA) := by
      rw [Ring.krullDimLE_zero_iff]
      intro I hI
      have hQ : (I.comap (Ideal.Quotient.mk JA)).IsPrime := Ideal.comap_isPrime _ I
      have hJQ : JA ≤ I.comap (Ideal.Quotient.mk JA) := by
        intro x hx
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
        exact I.zero_mem
      have hQm : I.comap (Ideal.Quotient.mk JA) ≤ IsLocalRing.maximalIdeal _ :=
        IsLocalRing.le_maximalIdeal hQ.ne_top
      have hmQ := hm.2 ⟨hQ, hJQ⟩ hQm
      have hIeq : I = Ideal.map (Ideal.Quotient.mk JA) (IsLocalRing.maximalIdeal _) := by
        rw [← le_antisymm hQm hmQ, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk JA)
          Ideal.Quotient.mk_surjective (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime W))
          with h | h
      · exact absurd (hIeq.trans h) hI.ne_top
      · rw [hIeq]
        exact h
    haveI : IsArtinianRing (Localization.AtPrime W ⧸ JA) :=
      IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
    have hlenQ : Module.length (Localization.AtPrime W) (Localization.AtPrime W ⧸ JA) ≠ ⊤ := by
      rw [Module.length_eq_of_surjective (S := Localization.AtPrime W)
        (R := Localization.AtPrime W ⧸ JA) (M := Localization.AtPrime W ⧸ JA)
        (by rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective)]
      exact Module.length_ne_top
    let x : LocalizedModule W.primeCompl (S ⧸ J) := LocalizedModule.mk 1 1
    let g : Localization.AtPrime W →ₗ[Localization.AtPrime W] LocalizedModule W.primeCompl (S ⧸ J) :=
      LinearMap.toSpanSingleton _ _ x
    have hker : JA ≤ LinearMap.ker g := by
      rw [hJA, Ideal.map_le_iff_le_comap]
      intro j hj
      rw [Ideal.mem_comap, LinearMap.mem_ker]
      show (algebraMap S (Localization.AtPrime W) j) • x = 0
      rw [← Localization.mk_one_eq_algebraMap, LocalizedModule.mk_smul_mk, Algebra.smul_def, mul_one,
        Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hj, LocalizedModule.zero_mk]
    have hsurj : Function.Surjective (JA.liftQ g hker) := by
      intro y
      refine LocalizedModule.induction_on (fun m s => ?_) y
      obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective m
      refine ⟨Submodule.Quotient.mk (Localization.mk t s), ?_⟩
      rw [Submodule.liftQ_apply]
      show Localization.mk t s • x = _
      rw [LocalizedModule.mk_smul_mk, Algebra.smul_def, mul_one, mul_one, Ideal.Quotient.algebraMap_eq]
    exact ne_top_of_le_ne_top hlenQ (Module.length_le_of_surjective _ hsurj)

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Apply `h` to reduce the goal to its premises. Unfold `divCycle`. Rewrite using `[dif_neg hc]`.
-/
theorem facts_of_divCycle_ne_zero {K : Type} {ι : K → Type} {R : Type} [CommRing R]
    {P W : Ideal (MRing ι R)} {f : MRing ι R} (h : divCycle P f W ≠ 0) :
    W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W := by
  by_contra hc
  apply h
  unfold divCycle
  rw [dif_neg hc]

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ P d hP`. Use `haveI : IsNoetherianRing (MRing ι O) := (inferInstance : IsNoetherianRing (MvPolynomial ((k : K) × ι k) O))`. Take `⟨⟨hPprime, -, -⟩, hnt, -⟩` from `hP`. Use `haveI := hPprime`. Establish `hmax : Ideal.map (C : O →+* MRing ι O) (IsLocalRing.maximalIdeal O) = Ideal.span {(C ϖ : MRing ι O)}`.

Rewrite using `[(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span, Set.image_singleton]`. Establish `hϖP : (C ϖ : MRing ι O) ∉ P`. Introduce `h`. Establish `h2 : ϖ ∈ Ideal.comap (C : O →+* MRing ι O) P` using `Ideal.mem_comap.mpr h`. Rewrite `h2` using `[hnt]`.

Conclude with `hϖ.ne_zero ((Submodule.mem_bot O).1 h2)`. Establish `key : ∀ f : MRing ι O, f ∉ P → ∀ W, divCycle P f W ≠ 0 → (C ϖ : MRing ι O) ∈ W → IsFibreComp P W`. Introduce `f _ W hW hϖW`. Take `⟨hWmin, hWrel⟩` from `facts_of_divCycle_ne_zero hW`. Unfold `IsFibreComp`.

Rewrite using `[hmax]`. Conclude with `⟨mem_minimalPrimes_sup_of_mem hWmin hϖW hϖP, hWrel⟩`. Use `⟨?_, fun a f _ hf W hW hϖW => key f hf W hW hϖW, ?_⟩` and prove the remaining obligations. Introduce `W`. Prove the components needed by the constructor for the conclusion.

Introduce `hF`. Unfold `IsFibreComp at hF`. Rewrite `hF` using `[hmax]`. Take `⟨hWmin, hWrel⟩` from `hF`. Use `haveI : W.IsPrime := hWmin.1.1`.

Unfold `divCycle`. Rewrite using `[dif_pos ⟨hWmin, hWrel⟩]`. Conclude with `Nat.cast_ne_zero.mpr (length_toNat_ne_zero hWmin)`. Introduce `hW`. Take `⟨hWmin, hWrel⟩` from `facts_of_divCycle_ne_zero hW`.

Unfold `IsFibreComp`. Rewrite using `[hmax]`. Conclude with `⟨hWmin, hWrel⟩`. Introduce `b f g hV W hW`. Take `⟨-, hfP, hgP, hvert, -⟩` from `hV`.

Establish `hϖW : (C ϖ : MRing ι O) ∈ W` using `hvert W hW`. Distinguish the cases in `hfW : divCycle P f W = 0`. Establish `hgW : divCycle P g W ≠ 0`. Introduce `hg`. Apply `hW` to reduce the goal to its premises.

Unfold `ratDiv`. Rewrite using `[hfW, hg, sub_zero]`. Conclude with `key g hgP W hgW hϖW`. Conclude with `key f hfP W hfW hϖW`.
-/
theorem fibre_comp : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → (∀ W, IsFibreComp P W ↔ divCycle P (C ϖ) W ≠ 0) ∧ (∀ (a : K → ℕ) (f : MRing ι O), IsMultiHomog f a → f ∉ P → ∀ W, divCycle P f W ≠ 0 → (C ϖ : MRing ι O) ∈ W → IsFibreComp P W) ∧ ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g → ∀ W, ratDiv P f g W ≠ 0 → IsFibreComp P W := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP
  classical
  haveI : IsNoetherianRing (MRing ι O) :=
    (inferInstance : IsNoetherianRing (MvPolynomial ((k : K) × ι k) O))
  obtain ⟨⟨hPprime, -, -⟩, hnt, -⟩ := hP
  haveI := hPprime
  have hmax : Ideal.map (C : O →+* MRing ι O) (IsLocalRing.maximalIdeal O) =
      Ideal.span {(C ϖ : MRing ι O)} := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton]
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h2 : ϖ ∈ Ideal.comap (C : O →+* MRing ι O) P := Ideal.mem_comap.mpr h
    rw [hnt] at h2
    exact hϖ.ne_zero ((Submodule.mem_bot O).1 h2)
  have key : ∀ f : MRing ι O, f ∉ P → ∀ W, divCycle P f W ≠ 0 → (C ϖ : MRing ι O) ∈ W →
      IsFibreComp P W := by
    intro f _ W hW hϖW
    obtain ⟨hWmin, hWrel⟩ := facts_of_divCycle_ne_zero hW
    unfold IsFibreComp
    rw [hmax]
    exact ⟨mem_minimalPrimes_sup_of_mem hWmin hϖW hϖP, hWrel⟩
  refine ⟨?_, fun a f _ hf W hW hϖW => key f hf W hW hϖW, ?_⟩
  · intro W
    constructor
    · intro hF
      unfold IsFibreComp at hF
      rw [hmax] at hF
      obtain ⟨hWmin, hWrel⟩ := hF
      haveI : W.IsPrime := hWmin.1.1
      unfold divCycle
      rw [dif_pos ⟨hWmin, hWrel⟩]
      exact Nat.cast_ne_zero.mpr (length_toNat_ne_zero hWmin)
    · intro hW
      obtain ⟨hWmin, hWrel⟩ := facts_of_divCycle_ne_zero hW
      unfold IsFibreComp
      rw [hmax]
      exact ⟨hWmin, hWrel⟩
  · intro b f g hV W hW
    obtain ⟨-, hfP, hgP, hvert, -⟩ := hV
    have hϖW : (C ϖ : MRing ι O) ∈ W := hvert W hW
    by_cases hfW : divCycle P f W = 0
    · have hgW : divCycle P g W ≠ 0 := by
        intro hg
        apply hW
        unfold ratDiv
        rw [hfW, hg, sub_zero]
      exact key g hgP W hgW hϖW
    · exact key f hfP W hfW hϖW

end GlobalTheory.CompanionTheory.Ar.Num.FibreComp
