import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

open IsLocalRing

/- English proof (translation)
Establish `: IsGalois K Ω` using `{}`. Establish `hc : SMulCommClass (Ω ≃ₐ[K] Ω) V Ω` using `⟨fun g v x => by`. Rewrite using `[← IsScalarTower.algebraMap_smul K v x, ← IsScalarTower.algebraMap_smul K v (g • x)]`. Conclude with `map_smul g _ _⟩`. Set `: TopologicalSpace (integralClosure V Ω)` to `⊥`.

Establish `: DiscreteTopology (integralClosure V Ω)` using `⟨rfl⟩`. Establish `: ContinuousSMul (Ω ≃ₐ[K] Ω) (integralClosure V Ω)`. Rewrite using `[continuousSMul_iff_stabilizer_isOpen]`. Introduce `x`. Use `stabilizer_isOpen_of_isIntegral (K := K) (x : Ω)` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `g`. Simplify using `only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]`. Conclude with `Subtype.ext_iff`. Establish `: Algebra.IsInvariant V (integralClosure V Ω) (Ω ≃ₐ[K] Ω)`.

Prove the components needed by the constructor for the conclusion. Introduce `b hb`. Take `⟨k, hk⟩` from `(InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (b : Ω)).2 fun g => congrArg Subtype.val (hb g)`. Establish `hint : IsIntegral V k`. Establish `h2 : IsIntegral V (algebraMap K Ω k)` using `hk ▸ b.2`.

Conclude with `(isIntegral_algebraMap_iff (algebraMap K Ω).injective).1 h2`. Take `⟨v, hv⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hint`. Use `⟨v, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[← hk, ← hv, ← IsScalarTower.algebraMap_apply]`. Both sides reduce to the same expression.

Establish `hinj : Function.Injective (algebraMap V Ω)`. Rewrite using `[IsScalarTower.algebraMap_eq V K Ω]`. Conclude with `(algebraMap K Ω).injective.comp (IsFractionRing.injective V K)`. Establish `: FaithfulSMul V (integralClosure V Ω)`. Rewrite using `[faithfulSMul_iff_algebraMap_injective]`.

Introduce `a b hab`. Conclude with `hinj (congrArg Subtype.val hab)`. Take `⟨Q, hQ, hQo⟩` from `Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := integralClosure V Ω) (maximalIdeal V)`. Set `: Field (V ⧸ maximalIdeal V)` to `Ideal.Quotient.field _`. Set `: Field (integralClosure V Ω ⧸ Q)` to `Ideal.Quotient.field _`.

Set `: Fintype (V ⧸ maximalIdeal V)` to `Fintype.ofFinite _`. Establish `: Algebra.IsAlgebraic (V ⧸ maximalIdeal V) (integralClosure V Ω ⧸ Q)`. Establish `hi : Algebra.IsIntegral (V ⧸ maximalIdeal V) (integralClosure V Ω ⧸ Q)` using `Ideal.Quotient.algebra_isIntegral_of_liesOver _ _`. Conclude with `hi.isAlgebraic`. Take `⟨σ, hσ⟩` from `Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := Ω ≃ₐ[K] Ω) (maximalIdeal V) Q (FiniteField.frobeniusAlgEquivOfAlgebraic (V ⧸ maximalIdeal V) _)`.

Establish `hu : Q.under V = maximalIdeal V` using `hQo.over.symm`. Establish `hF : IsArithFrobAt V σ.1 Q`. Introduce `x`. Establish `h` using `DFunLike.congr_fun hσ (Ideal.Quotient.mk _ x)`. Rewrite using `[← Ideal.Quotient.eq, map_pow, hu, Nat.card_eq_fintype_card]`.

Conclude with `h`. Use `⟨σ.1, fun x m hm hx => ?_⟩` and prove the remaining obligations. Establish `hm0 : 0 < m` using `Nat.pos_of_ne_zero (by rintro rfl; exact hm (by simp))`. Establish `hxi : IsIntegral V x` using `IsIntegral.of_pow hm0 (by rw [hx]; exact isIntegral_one)`. Establish `hmQ : ((m : ℕ) : integralClosure V Ω) ∉ Q`.

Introduce `h`. Apply `hm` to reduce the goal to its premises. Rewrite using `[← hu, Ideal.under_def, Ideal.mem_comap, map_natCast]`. Conclude with `h`. Establish `h` using `AlgHom.IsArithFrobAt.apply_of_pow_eq_one hF (ζ := ⟨x, hxi⟩) (m := m) (Subtype.ext hx) hmQ`.

Rewrite `h` using `[hu]`. Conclude with `congrArg Subtype.val h`.
-/
theorem exists_algEquiv_rootOfUnity_eq_pow (V K : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K]
    (hfin : Finite (V ⧸ maximalIdeal V)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [Algebra V Ω] [IsScalarTower V K Ω] :
    ∃ φ : Ω ≃ₐ[K] Ω, ∀ (x : Ω) (m : ℕ), (m : V) ∉ maximalIdeal V → x ^ m = 1 →
      φ x = x ^ Nat.card (V ⧸ maximalIdeal V) := by
  have : IsGalois K Ω := {}
  have hc : SMulCommClass (Ω ≃ₐ[K] Ω) V Ω := ⟨fun g v x => by
    rw [← IsScalarTower.algebraMap_smul K v x, ← IsScalarTower.algebraMap_smul K v (g • x)]
    exact map_smul g _ _⟩
  let : TopologicalSpace (integralClosure V Ω) := ⊥
  have : DiscreteTopology (integralClosure V Ω) := ⟨rfl⟩
  have : ContinuousSMul (Ω ≃ₐ[K] Ω) (integralClosure V Ω) := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    have := stabilizer_isOpen_of_isIntegral (K := K) (x : Ω)
    convert this using 1
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact Subtype.ext_iff
  have : Algebra.IsInvariant V (integralClosure V Ω) (Ω ≃ₐ[K] Ω) := by
    constructor
    intro b hb
    obtain ⟨k, hk⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (b : Ω)).2
      fun g => congrArg Subtype.val (hb g)
    have hint : IsIntegral V k := by
      have h2 : IsIntegral V (algebraMap K Ω k) := hk ▸ b.2
      exact (isIntegral_algebraMap_iff (algebraMap K Ω).injective).1 h2
    obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨v, Subtype.ext ?_⟩
    rw [← hk, ← hv, ← IsScalarTower.algebraMap_apply]
    rfl
  have hinj : Function.Injective (algebraMap V Ω) := by
    rw [IsScalarTower.algebraMap_eq V K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective V K)
  have : FaithfulSMul V (integralClosure V Ω) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    exact hinj (congrArg Subtype.val hab)
  obtain ⟨Q, hQ, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := integralClosure V Ω) (maximalIdeal V)
  let : Field (V ⧸ maximalIdeal V) := Ideal.Quotient.field _
  let : Field (integralClosure V Ω ⧸ Q) := Ideal.Quotient.field _
  let : Fintype (V ⧸ maximalIdeal V) := Fintype.ofFinite _
  have : Algebra.IsAlgebraic (V ⧸ maximalIdeal V) (integralClosure V Ω ⧸ Q) := by
    have hi : Algebra.IsIntegral (V ⧸ maximalIdeal V) (integralClosure V Ω ⧸ Q) :=
      Ideal.Quotient.algebra_isIntegral_of_liesOver _ _
    exact hi.isAlgebraic
  obtain ⟨σ, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := Ω ≃ₐ[K] Ω)
    (maximalIdeal V) Q
    (FiniteField.frobeniusAlgEquivOfAlgebraic (V ⧸ maximalIdeal V) _)
  have hu : Q.under V = maximalIdeal V := hQo.over.symm
  have hF : IsArithFrobAt V σ.1 Q := by
    intro x
    have h := DFunLike.congr_fun hσ (Ideal.Quotient.mk _ x)
    rw [← Ideal.Quotient.eq, map_pow, hu, Nat.card_eq_fintype_card]
    exact h
  refine ⟨σ.1, fun x m hm hx => ?_⟩
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (by simp))
  have hxi : IsIntegral V x := IsIntegral.of_pow hm0 (by rw [hx]; exact isIntegral_one)
  have hmQ : ((m : ℕ) : integralClosure V Ω) ∉ Q := by
    intro h
    apply hm
    rw [← hu, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact h
  have h := AlgHom.IsArithFrobAt.apply_of_pow_eq_one hF (ζ := ⟨x, hxi⟩) (m := m)
    (Subtype.ext hx) hmQ
  rw [hu] at h
  exact congrArg Subtype.val h

/- English proof (translation)
Establish `e : (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) ≃+* ZMod l` using `PadicInt.residueField`. Establish `: NeZero l` using `⟨(Fact.out : l.Prime).ne_zero⟩`. Establish `hcard : Nat.card (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) = l`. Rewrite using `[Nat.card_congr e.toEquiv, Nat.card_zmod]`. Take `⟨φ, hφ⟩` from `exists_algEquiv_rootOfUnity_eq_pow ℤ_[l] ℚ_[l] (Finite.of_equiv _ e.symm.toEquiv) (Om l)`.

Rewrite `hφ` using `[hcard]`. Establish `hφ' : ∀ (x : Om l) (m : ℕ), ¬ l ∣ m → x ^ m = 1 → φ x = x ^ l`. Introduce `x m hm hx`. Use `hφ x m (fun h => hm ?_) hx` and prove the remaining obligations. Rewrite `h` using `[← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast, ZMod.natCast_eq_zero_iff]`.

Conclude with `h`. Establish `hle : (MaximalUnramifiedExtension l).map (φ : Om l →ₐ[ℚ_[l]] Om l) ≤ MaximalUnramifiedExtension l`. Unfold `MaximalUnramifiedExtension`. Rewrite using `[IntermediateField.adjoin_map]`. Apply `IntermediateField.adjoin.mono` to reduce the goal to its premises.

Introduce and unpack `_ ⟨x, ⟨m, hm, hlm, hx⟩, rfl⟩`. Conclude with `⟨m, hm, hlm, by rw [← map_pow, hx, map_one]⟩`. Use `⟨((φ : Om l →ₐ[ℚ_[l]] Om l).comp (MaximalUnramifiedExtension l).val).codRestrict (MaximalUnramifiedExtension l).toSubalgebra (fun x => hle ⟨x, x.2, rfl⟩), fun c m _ hlm hc => Subtype.ext ?_⟩` and prove the remaining obligations. Conclude with `hφ' c m hlm (congrArg Subtype.val hc)`.
-/
theorem exists_frobenius_Kur (l : ℕ) [Fact l.Prime] :
    ∃ σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l),
      ∀ (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → σ c = c ^ l := by
  have e : (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) ≃+* ZMod l := PadicInt.residueField
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hcard : Nat.card (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) = l := by
    rw [Nat.card_congr e.toEquiv, Nat.card_zmod]
  obtain ⟨φ, hφ⟩ := exists_algEquiv_rootOfUnity_eq_pow ℤ_[l] ℚ_[l]
    (Finite.of_equiv _ e.symm.toEquiv) (Om l)
  rw [hcard] at hφ
  have hφ' : ∀ (x : Om l) (m : ℕ), ¬ l ∣ m → x ^ m = 1 → φ x = x ^ l := by
    intro x m hm hx
    refine hφ x m (fun h => hm ?_) hx
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast, ZMod.natCast_eq_zero_iff] at h
    exact h
  have hle : (MaximalUnramifiedExtension l).map (φ : Om l →ₐ[ℚ_[l]] Om l) ≤ MaximalUnramifiedExtension l := by
    unfold MaximalUnramifiedExtension
    rw [IntermediateField.adjoin_map]
    apply IntermediateField.adjoin.mono
    rintro _ ⟨x, ⟨m, hm, hlm, hx⟩, rfl⟩
    exact ⟨m, hm, hlm, by rw [← map_pow, hx, map_one]⟩
  refine ⟨((φ : Om l →ₐ[ℚ_[l]] Om l).comp (MaximalUnramifiedExtension l).val).codRestrict (MaximalUnramifiedExtension l).toSubalgebra
    (fun x => hle ⟨x, x.2, rfl⟩), fun c m _ hlm hc => Subtype.ext ?_⟩
  exact hφ' c m hlm (congrArg Subtype.val hc)

end GlobalTheory.MemLoc
