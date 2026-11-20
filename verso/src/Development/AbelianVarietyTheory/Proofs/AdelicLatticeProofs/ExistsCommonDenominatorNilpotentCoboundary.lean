import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeAlgebraMapOfIsNilpotentTmulSub
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory

/- English proof (translation)
Use `letI : Field (Localization M) := hF.toField`. Use `haveI : CharZero (Localization M) := algebraRat.charZero _`. Set `K` to `Localization M`. Set `A'` to `Localization (Algebra.algebraMapSubmonoid A M)`. Use `haveI : IsReduced A' := inferInstance`.

Use `haveI : Algebra.FiniteType K A' := by haveI : IsLocalization (Submonoid.map (algebraMap B A) M) A' := inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid A M) A')`. Establish `h` using `RingHom.finiteType_localizationPreserves (algebraMap B A) M K A' (RingHom.finiteType_algebraMap.mpr inferInstance)`. Conclude with `h`. Set `g : A →ₐ[B] A'` to `IsScalarTower.toAlgHom B A A'`. Set `φ : A ⊗[B] A →ₐ[B] A' ⊗[K] A'` to `Algebra.TensorProduct.lift (((Algebra.TensorProduct.includeLeft : A' →ₐ[K] A' ⊗[K] A').restrictScalars B).comp g) (((Algebra.TensorProduct.includeRight : A' →ₐ[K] A' ⊗[K] A').restrictScalars B).comp g) (fun _ _ => Commute.all _ _)`.

Establish `hn : IsNilpotent (g f ⊗ₜ[K] (1 : A') - (1 : A') ⊗ₜ[K] g f)`. Use `hf.map φ` as an intermediate fact. Simplify `this` using `[φ]`. Take `⟨k, hk⟩` from `GlobalTheory.ClassFin.mem_range_algebraMap_of_isNilpotent_tmul_sub K A' (g f) hn`. Take `⟨⟨β, t⟩, ht⟩` from `IsLocalization.surj M k`.

Establish `h1 : algebraMap A A' (algebraMap B A t * f) = algebraMap A A' (algebraMap B A β)`. Use `congrArg (algebraMap K A') ht` as an intermediate fact. Rewrite `this` using `[map_mul, hk, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]`. Rewrite using `[map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← this, mul_comm]`. Both sides reduce to the same expression.

Take `⟨⟨_, u, hu, rfl⟩, hc⟩` from `(IsLocalization.eq_iff_exists (Algebra.algebraMapSubmonoid A M) A').1 h1`. Use `⟨u * t, M.mul_mem hu t.2, u * β, ?_⟩` and prove the remaining obligations. Simplify `hc` using `[map_mul, mul_assoc]`.
-/
theorem exists_denominator_of_isField_localization (B A : Type) [CommRing B] [CommRing A]
    [Algebra ℚ B] [Algebra B A] [Algebra.FiniteType B A] [IsReduced A] (M : Submonoid B)
    (hF : IsField (Localization M)) (f : A)
    (hf : IsNilpotent (f ⊗ₜ[B] (1 : A) - (1 : A) ⊗ₜ[B] f)) :
    ∃ m ∈ M, ∃ b' : B, algebraMap B A m * f = algebraMap B A b' := by
  letI : Field (Localization M) := hF.toField
  haveI : CharZero (Localization M) := algebraRat.charZero _
  let K := Localization M
  let A' := Localization (Algebra.algebraMapSubmonoid A M)
  haveI : IsReduced A' := inferInstance
  haveI : Algebra.FiniteType K A' := by
    haveI : IsLocalization (Submonoid.map (algebraMap B A) M) A' :=
      inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid A M) A')
    have h := RingHom.finiteType_localizationPreserves (algebraMap B A) M K A'
      (RingHom.finiteType_algebraMap.mpr inferInstance)
    exact h
  let g : A →ₐ[B] A' := IsScalarTower.toAlgHom B A A'
  let φ : A ⊗[B] A →ₐ[B] A' ⊗[K] A' :=
    Algebra.TensorProduct.lift
      (((Algebra.TensorProduct.includeLeft : A' →ₐ[K] A' ⊗[K] A').restrictScalars B).comp g)
      (((Algebra.TensorProduct.includeRight : A' →ₐ[K] A' ⊗[K] A').restrictScalars B).comp g)
      (fun _ _ => Commute.all _ _)
  have hn : IsNilpotent (g f ⊗ₜ[K] (1 : A') - (1 : A') ⊗ₜ[K] g f) := by
    have := hf.map φ
    simpa [φ] using this
  obtain ⟨k, hk⟩ := GlobalTheory.ClassFin.mem_range_algebraMap_of_isNilpotent_tmul_sub K A' (g f) hn
  obtain ⟨⟨β, t⟩, ht⟩ := IsLocalization.surj M k
  have h1 : algebraMap A A' (algebraMap B A t * f) = algebraMap A A' (algebraMap B A β) := by
    have := congrArg (algebraMap K A') ht
    rw [map_mul, hk, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← this,
      mul_comm]
    rfl
  obtain ⟨⟨_, u, hu, rfl⟩, hc⟩ :=
    (IsLocalization.eq_iff_exists (Algebra.algebraMapSubmonoid A M) A').1 h1
  refine ⟨u * t, M.mul_mem hu t.2, u * β, ?_⟩
  simpa [map_mul, mul_assoc] using hc

/- English proof (translation)
Introduce `B A _ _ _ _ _ _ _ hinj s hs`. Use `haveI : IsReduced B := isReduced_of_injective (algebraMap B A) hinj`. Take `⟨m, hm⟩` from `Ideal.exists_maximal B`. Take `⟨p, hp, -⟩` from `Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal B)) (J := m) bot_le`. Use `haveI : p.IsPrime := hp.1.1`.

Use `haveI : Ring.KrullDimLE 0 (Localization.AtPrime p) := Ring.KrullDimLE.of_isLocalization p hp _`. Establish `hF : IsField (Localization.AtPrime p)` using `Ring.KrullDimLE.isField_of_isReduced`. Establish `key : ∃ b ∈ p.primeCompl, ∀ f ∈ s, ∃ b' : B, algebraMap B A b * f = algebraMap B A b'`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨1, one_mem _, by simp⟩`.

Consider the case `insert a s _ ih`. Take `⟨b, hb, h⟩` from `ih (fun f hf => hs f (Finset.mem_insert_of_mem hf))`. Take `⟨c, hc, c', hc'⟩` from `exists_denominator_of_isField_localization B A p.primeCompl hF a (hs a (Finset.mem_insert_self _ _))`. Use `⟨b * c, mul_mem hb hc, fun f hf => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hf with rfl | hf` into its components or cases.

Conclude with `⟨b * c', by rw [map_mul, map_mul, mul_assoc, hc']⟩`. Take `⟨b', hb'⟩` from `h f hf`. Conclude with `⟨c * b', by rw [map_mul, map_mul, ← hb']; ring⟩`. Take `⟨b, hb, h⟩` from `key`. Conclude with `⟨b, fun h0 => hb (h0 ▸ p.zero_mem), h⟩`.
-/
theorem exists_common_denominator_of_isNilpotent :
    ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra ℚ B] [Algebra B A] [Algebra.FiniteType B A] [IsReduced A] [Nontrivial B], Function.Injective (algebraMap B A) → ∀ s : Finset A, (∀ f ∈ s, IsNilpotent (f ⊗ₜ[B] (1 : A) - (1 : A) ⊗ₜ[B] f)) → ∃ b : B, b ≠ 0 ∧ ∀ f ∈ s, ∃ b' : B, algebraMap B A b * f = algebraMap B A b' := by
  intro B A _ _ _ _ _ _ _ hinj s hs
  classical
  haveI : IsReduced B := isReduced_of_injective (algebraMap B A) hinj
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal B)) (J := m) bot_le
  haveI : p.IsPrime := hp.1.1
  haveI : Ring.KrullDimLE 0 (Localization.AtPrime p) :=
    Ring.KrullDimLE.of_isLocalization p hp _
  have hF : IsField (Localization.AtPrime p) := Ring.KrullDimLE.isField_of_isReduced
  have key : ∃ b ∈ p.primeCompl, ∀ f ∈ s, ∃ b' : B, algebraMap B A b * f = algebraMap B A b' := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_mem _, by simp⟩
    | insert a s _ ih =>
      obtain ⟨b, hb, h⟩ := ih (fun f hf => hs f (Finset.mem_insert_of_mem hf))
      obtain ⟨c, hc, c', hc'⟩ := exists_denominator_of_isField_localization B A p.primeCompl hF a
        (hs a (Finset.mem_insert_self _ _))
      refine ⟨b * c, mul_mem hb hc, fun f hf => ?_⟩
      rcases Finset.mem_insert.1 hf with rfl | hf
      · exact ⟨b * c', by rw [map_mul, map_mul, mul_assoc, hc']⟩
      · obtain ⟨b', hb'⟩ := h f hf
        exact ⟨c * b', by rw [map_mul, map_mul, ← hb']; ring⟩
  obtain ⟨b, hb, h⟩ := key
  exact ⟨b, fun h0 => hb (h0 ▸ p.zero_mem), h⟩

end GlobalTheory
