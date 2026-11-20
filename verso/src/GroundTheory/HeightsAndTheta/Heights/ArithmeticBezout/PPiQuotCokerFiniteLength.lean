import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsPiQuotCokerFiniteLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

/- English proof (translation)
Introduce `B _ _ _ J hJ hQ`. Establish `: Finite J.minimalPrimes` using `(J.finite_minimalPrimes_of_isNoetherianRing B).to_subtype`. Set `: Fintype J.minimalPrimes` to `Fintype.ofFinite _`. Establish `hfac : ∀ (P : J.minimalPrimes) (x : B), quotToPiMinimalPrimes J (Submodule.Quotient.mk x) P = Ideal.Quotient.mk (P : Ideal B) x` using `fun _ _ => rfl`. Use `⟨(injective_iff_map_eq_zero _).mpr fun y hy => ?_, ?_⟩` and prove the remaining obligations.

Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Establish `hxP : ∀ P : J.minimalPrimes, x ∈ (P : Ideal B)` using `fun P => by`. Establish `h1` using `congrFun hy P`. Rewrite `h1` using `[hfac, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem]`. Then use the resulting hypothesis. Establish `hx : x ∈ sInf J.minimalPrimes` using `Submodule.mem_sInf.mpr fun p hp => hxP ⟨p, hp⟩`.

Rewrite `hx` using `[Ideal.sInf_minimalPrimes, hJ.radical]`. Conclude with `(Submodule.Quotient.mk_eq_zero _).mpr hx`. Establish `hkey : ∀ Q : Ideal B, Q.IsPrime → ∀ P P' : J.minimalPrimes, P ≠ P' → (P : Ideal B) ≤ Q → (P' : Ideal B) ≤ Q → Q = IsLocalRing.maximalIdeal B`. Introduce `Q hQp P P' hne hPQ hP'Q`. Break down `hQ Q hQp (P.2.1.2.trans hPQ) with hmin | hm` into its components or cases.

It suffices to derive a contradiction. Apply `hne` to reduce the goal to its premises. Establish `e1 : (P : Ideal B) = Q` using `le_antisymm hPQ (hmin.2 P.2.1 hPQ)`. Establish `e2 : (P' : Ideal B) = Q` using `le_antisymm hP'Q (hmin.2 P'.2.1 hP'Q)`. Conclude with `Subtype.ext (e1.trans e2.symm)`.

Conclude with `hm`. Set `IP : J.minimalPrimes → Ideal B` to `fun P => (Finset.univ.filter (· ≠ P)).inf fun P' : J.minimalPrimes => (P' : Ideal B)`. Set `I : Ideal B` to `Finset.univ.inf fun P => IP P ⊔ (P : Ideal B)`. Establish `hI : ∀ Q : Ideal B, Q.IsPrime → I ≤ Q → Q = IsLocalRing.maximalIdeal B`. Introduce `Q hQp hIQ`.

Take `⟨P, -, hPQ⟩` from `hQp.inf_le'.mp hIQ`. Take `⟨P', hP', hP'Q⟩` from `hQp.inf_le'.mp (le_sup_left.trans hPQ)`. Conclude with `hkey Q hQp P P' (Finset.mem_filter.mp hP').2.symm (le_sup_right.trans hPQ) hP'Q`. Establish `htors : Module.IsTorsionBySet B (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J)) (I : Set B)`. Introduce `c z`.

Take `⟨y, hy⟩` from `z`. Use `show y • c = 0`. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ c`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Establish `hyP : ∀ P, y ∈ IP P ⊔ (P : Ideal B)` using `fun P => Submodule.mem_finsetInf.mp hy P (Finset.mem_univ _)`.

Use `choose a ha b hb hab using fun P => Submodule.mem_sup.mp (hyP P)`. Use `choose x hx using fun P => Ideal.Quotient.mk_surjective (v P)`. Use `⟨Submodule.Quotient.mk (∑ P, a P * x P), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `Q`. Rewrite using `[hfac, Pi.smul_apply, ← hx Q, map_sum, Finset.sum_eq_single Q]`.

Rewrite using `[← hab Q, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (hb Q), add_zero]`. Introduce `P _ hPQ`. Establish `hle : IP P ≤ (Q : Ideal B)` using `Finset.inf_le (Finset.mem_filter.mpr ⟨Finset.mem_univ Q, hPQ.symm⟩)`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (hle (ha P)))`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ Q) h`. Distinguish the cases in `hItop : I = ⊤`. Use `haveI : Subsingleton (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J)) := ⟨fun c d => by`. Establish `hc` using `@htors c ⟨1, by rw [hItop]; trivial⟩`. Establish `hd` using `@htors d ⟨1, by rw [hItop]; trivial⟩`.

Rewrite `hc`, `hd` using `[one_smul]`. Rewrite using `[hc, hd]⟩`. Conclude with `IsFiniteLength.of_subsingleton`. Establish `hmax : IsLocalRing.maximalIdeal B ∈ I.minimalPrimes` using `⟨⟨inferInstance, IsLocalRing.le_maximalIdeal hItop⟩, fun q hq _ => (hI q hq.1 hq.2).ge⟩`. Establish `: IsArtinianRing (B ⧸ I)` using `IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hmax`.

Rewrite using `[isFiniteLength_iff_isNoetherian_isArtinian]`. Use `⟨inferInstance, ?_⟩` and prove the remaining obligations. Set `` to `htors.module`. Establish `: IsScalarTower B (B ⧸ I) (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J))` using `htors.isScalarTower`. Establish `: Module.Finite (B ⧸ I) (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J))` using `Module.Finite.of_restrictScalars_finite B _ _`.

Establish `: IsArtinian (B ⧸ I) (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J))` using `isArtinian_of_fg_of_artinian'`. Conclude with `isArtinian_of_surjective_algebraMap (R := B ⧸ I) Ideal.Quotient.mk_surjective`.
-/
theorem PiQuotCokerFiniteLength.proof : PiQuotCokerFiniteLength.Statement := by
  intro B _ _ _ J hJ hQ
  have : Finite J.minimalPrimes := (J.finite_minimalPrimes_of_isNoetherianRing B).to_subtype
  let : Fintype J.minimalPrimes := Fintype.ofFinite _
  classical
  have hfac : ∀ (P : J.minimalPrimes) (x : B),
      quotToPiMinimalPrimes J (Submodule.Quotient.mk x) P = Ideal.Quotient.mk (P : Ideal B) x :=
    fun _ _ => rfl
  refine ⟨(injective_iff_map_eq_zero _).mpr fun y hy => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hxP : ∀ P : J.minimalPrimes, x ∈ (P : Ideal B) := fun P => by
      have h1 := congrFun hy P
      rwa [hfac, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem] at h1
    have hx : x ∈ sInf J.minimalPrimes := Submodule.mem_sInf.mpr fun p hp => hxP ⟨p, hp⟩
    rw [Ideal.sInf_minimalPrimes, hJ.radical] at hx
    exact (Submodule.Quotient.mk_eq_zero _).mpr hx

  have hkey : ∀ Q : Ideal B, Q.IsPrime → ∀ P P' : J.minimalPrimes, P ≠ P' →
      (P : Ideal B) ≤ Q → (P' : Ideal B) ≤ Q → Q = IsLocalRing.maximalIdeal B := by
    intro Q hQp P P' hne hPQ hP'Q
    rcases hQ Q hQp (P.2.1.2.trans hPQ) with hmin | hm
    · exfalso
      apply hne
      have e1 : (P : Ideal B) = Q := le_antisymm hPQ (hmin.2 P.2.1 hPQ)
      have e2 : (P' : Ideal B) = Q := le_antisymm hP'Q (hmin.2 P'.2.1 hP'Q)
      exact Subtype.ext (e1.trans e2.symm)
    · exact hm
  let IP : J.minimalPrimes → Ideal B := fun P =>
    (Finset.univ.filter (· ≠ P)).inf fun P' : J.minimalPrimes => (P' : Ideal B)
  let I : Ideal B := Finset.univ.inf fun P => IP P ⊔ (P : Ideal B)
  have hI : ∀ Q : Ideal B, Q.IsPrime → I ≤ Q → Q = IsLocalRing.maximalIdeal B := by
    intro Q hQp hIQ
    obtain ⟨P, -, hPQ⟩ := hQp.inf_le'.mp hIQ
    obtain ⟨P', hP', hP'Q⟩ := hQp.inf_le'.mp (le_sup_left.trans hPQ)
    exact hkey Q hQp P P' (Finset.mem_filter.mp hP').2.symm (le_sup_right.trans hPQ) hP'Q
  have htors : Module.IsTorsionBySet B
      (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J))
      (I : Set B) := by
    intro c z
    obtain ⟨y, hy⟩ := z
    show y • c = 0
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    have hyP : ∀ P, y ∈ IP P ⊔ (P : Ideal B) := fun P =>
      Submodule.mem_finsetInf.mp hy P (Finset.mem_univ _)
    choose a ha b hb hab using fun P => Submodule.mem_sup.mp (hyP P)
    choose x hx using fun P => Ideal.Quotient.mk_surjective (v P)
    refine ⟨Submodule.Quotient.mk (∑ P, a P * x P), ?_⟩
    funext Q
    rw [hfac, Pi.smul_apply, ← hx Q, map_sum, Finset.sum_eq_single Q]
    · rw [← hab Q, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_add, map_mul,
        Ideal.Quotient.eq_zero_iff_mem.mpr (hb Q), add_zero]
    · intro P _ hPQ
      have hle : IP P ≤ (Q : Ideal B) :=
        Finset.inf_le (Finset.mem_filter.mpr ⟨Finset.mem_univ Q, hPQ.symm⟩)
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (hle (ha P)))
    · intro h
      exact absurd (Finset.mem_univ Q) h
  by_cases hItop : I = ⊤
  · haveI : Subsingleton
        (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J)) :=
      ⟨fun c d => by
        have hc := @htors c ⟨1, by rw [hItop]; trivial⟩
        have hd := @htors d ⟨1, by rw [hItop]; trivial⟩
        rw [one_smul] at hc hd
        rw [hc, hd]⟩
    exact IsFiniteLength.of_subsingleton
  have hmax : IsLocalRing.maximalIdeal B ∈ I.minimalPrimes :=
    ⟨⟨inferInstance, IsLocalRing.le_maximalIdeal hItop⟩, fun q hq _ => (hI q hq.1 hq.2).ge⟩
  have : IsArtinianRing (B ⧸ I) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hmax
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  refine ⟨inferInstance, ?_⟩
  let := htors.module
  have : IsScalarTower B (B ⧸ I)
      (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J)) :=
    htors.isScalarTower
  have : Module.Finite (B ⧸ I)
      (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J)) :=
    Module.Finite.of_restrictScalars_finite B _ _
  have : IsArtinian (B ⧸ I)
      (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J)) :=
    isArtinian_of_fg_of_artinian'
  exact isArtinian_of_surjective_algebraMap (R := B ⧸ I) Ideal.Quotient.mk_surjective

end GroundTheory.Heights₂.Heights
