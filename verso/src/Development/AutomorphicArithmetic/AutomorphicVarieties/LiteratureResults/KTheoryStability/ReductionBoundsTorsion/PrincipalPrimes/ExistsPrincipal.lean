import Mathlib
import GroundTheory.GlobalFields.ClassFieldConsequences.HilbertClassField
import GroundTheory.GlobalFields.TateThesis.Chebotarev
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.ExistsPrimeAbsNormOfHasDirichletDensity

open NumberField IsDedekindDomain

noncomputable section

namespace PositivityTheory.KB.PrincipalPrimes

/- English proof (translation)
Set `Ω` to `AlgebraicClosure L`. Set `H` to `GroundTheory.Global.hilbertClassField L Ω`. Establish `: NumberField H` using `NumberField.of_module_finite L H`. Establish `: IsGalois L H` using `inferInstance`. Establish `hd` using `GroundTheory.Global.hasDirichletDensity_setOf_exists_arithFrobAt_mem (K := L) (L := H) ({1} : Set (H ≃ₐ[L] H)) (by`.

Introduce `σ hσ τ`. Rewrite `hσ`, the goal using `[Set.mem_singleton_iff]`. Rewrite using `[hσ, mul_one, mul_inv_cancel])`. Establish `hpos : (0 : ℝ) < (Nat.card ({1} : Set (H ≃ₐ[L] H)) : ℝ) / Nat.card (H ≃ₐ[L] H)` using `div_pos (Nat.cast_pos.2 Nat.card_pos) (Nat.cast_pos.2 Nat.card_pos)`. Take `⟨v, ⟨-, w, hw, hF⟩, hvT, -⟩` from `ReciprocityTheory.Neutral.Bridge.exists_prime_absNorm_of_hasDirichletDensity hd hpos hT`.

Use `⟨v, hvT, ?_⟩` and prove the remaining obligations. Use `hw` as an intermediate fact. Establish `h1` using `GroundTheory.Global.hilbertClassFieldArtinEquiv_mk0 L Ω v w`. Rewrite `h1` using `[Set.mem_singleton_iff.1 hF, MulEquiv.map_eq_one_iff]`. Conclude with `(ClassGroup.mk0_eq_one_iff _).1 h1`.
-/
theorem exists_principal (L : Type) [Field L] [NumberField L] (T : Set (HeightOneSpectrum (𝓞 L)))
    (hT : T.Finite) : ∃ v : HeightOneSpectrum (𝓞 L), v ∉ T ∧ v.asIdeal.IsPrincipal := by
  let Ω := AlgebraicClosure L
  let H := GroundTheory.Global.hilbertClassField L Ω
  have : NumberField H := NumberField.of_module_finite L H
  have : IsGalois L H := inferInstance
  have hd := GroundTheory.Global.hasDirichletDensity_setOf_exists_arithFrobAt_mem (K := L) (L := H)
    ({1} : Set (H ≃ₐ[L] H)) (by
      intro σ hσ τ
      rw [Set.mem_singleton_iff] at hσ ⊢
      rw [hσ, mul_one, mul_inv_cancel])
  have hpos : (0 : ℝ) < (Nat.card ({1} : Set (H ≃ₐ[L] H)) : ℝ) / Nat.card (H ≃ₐ[L] H) :=
    div_pos (Nat.cast_pos.2 Nat.card_pos) (Nat.cast_pos.2 Nat.card_pos)
  obtain ⟨v, ⟨-, w, hw, hF⟩, hvT, -⟩ :=
    ReciprocityTheory.Neutral.Bridge.exists_prime_absNorm_of_hasDirichletDensity hd hpos hT
  refine ⟨v, hvT, ?_⟩
  have := hw
  have h1 := GroundTheory.Global.hilbertClassFieldArtinEquiv_mk0 L Ω v w
  rw [Set.mem_singleton_iff.1 hF, MulEquiv.map_eq_one_iff] at h1
  exact (ClassGroup.mk0_eq_one_iff _).1 h1

/- English proof (translation)
The claim follows from `Set.Finite.preimage (f := fun v : HeightOneSpectrum (𝓞 L) => v.asIdeal) (fun _ _ _ _ h => HeightOneSpectrum.ext h) (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 L) B)`.
-/
theorem finite_small (L : Type) [Field L] [NumberField L] (B : ℕ) :
    {v : HeightOneSpectrum (𝓞 L) | Ideal.absNorm v.asIdeal ≤ B}.Finite :=
  Set.Finite.preimage (f := fun v : HeightOneSpectrum (𝓞 L) => v.asIdeal)
    (fun _ _ _ _ h => HeightOneSpectrum.ext h) (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 L) B)

/- English proof (translation)
Take `⟨v, hv, π, hπ⟩` from `exists_principal L _ (finite_small L B)`. Establish `hπ' : v.asIdeal = Ideal.span {π}` using `hπ`. Establish `hne : π ≠ 0`. Introduce and unpack `rfl`. Conclude with `v.ne_bot (by rw [hπ', Ideal.span_singleton_eq_bot])`.

Use `⟨π, (Ideal.span_singleton_prime hne).1 (hπ' ▸ v.isPrime), ?_⟩` and prove the remaining obligations. Rewrite using `[← hπ']`. Simplify using `only [Set.mem_ofPred_eq, not_le] at hv`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_prime (L : Type) [Field L] [NumberField L] (B : ℕ) :
    ∃ π : 𝓞 L, Prime π ∧ B ≤ Ideal.absNorm (Ideal.span {π}) := by
  obtain ⟨v, hv, π, hπ⟩ := exists_principal L _ (finite_small L B)
  have hπ' : v.asIdeal = Ideal.span {π} := hπ
  have hne : π ≠ 0 := by
    rintro rfl
    exact v.ne_bot (by rw [hπ', Ideal.span_singleton_eq_bot])
  refine ⟨π, (Ideal.span_singleton_prime hne).1 (hπ' ▸ v.isPrime), ?_⟩
  rw [← hπ']
  simp only [Set.mem_ofPred_eq, not_le] at hv
  omega

end PositivityTheory.KB.PrincipalPrimes
