import Mathlib
import GroundTheory.GlobalFields.SecondInequality.PrimeDegree

namespace GroundTheory.Global

open NumberField Module IntermediateField

universe u

def SecondInequality.{v} : Prop :=
  ∀ (K L : Type v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)],
    ENat.card (IdeleClassGroup K ⧸ (ideleClassNorm K L).range) ≤ Module.finrank K L

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `K L _ _ _ _ _ _ _ hn`. Establish `hn0 : 0 < n` using `hn ▸ finrank_pos`. Distinguish the cases in `h1 : n = 1`.

Establish `htop : (ideleClassNorm K L).range = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `c _`. Use `pow_finrank_mem_range_ideleClassNorm (L := L) c` as an intermediate fact. Rewrite `this` using `[hn, h1, pow_one]`. Then use the resulting hypothesis.

Rewrite using `[htop, Subgroup.index_top]`. Use linear arithmetic over natural numbers and integers. Take `⟨q, hq, hqn⟩` from `Nat.exists_prime_and_dvd h1`. Establish `: Fact q.Prime` using `⟨hq⟩`. Establish `hcard : Nat.card (L ≃ₐ[K] L) = n` using `by rw [IsGalois.card_aut_eq_finrank, hn]`.

Take `⟨g, hg⟩` from `exists_prime_orderOf_dvd_card' q (hcard ▸ hqn)`. Set `H : Subgroup (L ≃ₐ[K] L)` to `Subgroup.zpowers g`. Establish `: H.Normal` using `⟨fun a ha b ↦ by rwa [mul_comm_of_isCyclic b a, mul_inv_cancel_right]⟩`. Set `M : IntermediateField K L` to `fixedField H`. Establish `hML : finrank M L = q`.

Rewrite using `[finrank_fixedField_eq_card, Nat.card_zpowers, hg]`. Establish `hKM : finrank K M * q = n` using `by rw [← hML, finrank_mul_finrank, hn]`. Establish `hm_lt : finrank K M < n`. Establish `: 0 < finrank K M` using `finrank_pos`. Combine the equalities or inequalities in the displayed calculation.

Establish `: IsGalois M L` using `IsGalois.tower_top_of_isGalois K M L`. Establish `: IsCyclic (L ≃ₐ[M] L)` using `isCyclic_of_prime_card (p := q) (by rw [IsGalois.card_aut_eq_finrank, hML])`. Establish `: IsGalois K M` using `IsGalois.of_fixedField_normal_subgroup H`. Establish `: IsCyclic (M ≃ₐ[K] M)` using `isCyclic_of_surjective _ (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) (E := L))`. Establish `hM` using `ih (finrank K M) hm_lt K M rfl`.

Establish `hL` using `hR.index_le_of_prime (K := M) (L := L) hq hML`. Establish `hcomp : (ideleClassNorm K M).comp (ideleClassNorm M L) = ideleClassNorm K L` using `MonoidHom.ext fun c ↦ ideleClassNorm_ideleClassNorm c`. Establish `hrange : (ideleClassNorm K L).range = (ideleClassNorm M L).range.map (ideleClassNorm K M)`. Rewrite using `[MonoidHom.map_range, hcomp]`. Use `index_map_le (ideleClassNorm K M) hL.1 hM.1` as an intermediate fact.

Rewrite using `[hrange]`. Use `⟨this.1, this.2.trans ?_⟩` and prove the remaining obligations. Rewrite using `[← hKM]`. Conclude with `Nat.mul_le_mul hM.2 hL.2`.
-/
theorem SecondInequalityRoots.index_le_of_finrank_eq (hR : SecondInequalityRoots.{u}) (n : ℕ) :
    ∀ (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)], finrank K L = n →
      (ideleClassNorm K L).range.index ≠ 0 ∧ (ideleClassNorm K L).range.index ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K L _ _ _ _ _ _ _ hn
  have hn0 : 0 < n := hn ▸ finrank_pos
  by_cases h1 : n = 1
  ·
    have htop : (ideleClassNorm K L).range = ⊤ := by
      rw [eq_top_iff]
      intro c _
      have := pow_finrank_mem_range_ideleClassNorm (L := L) c
      rwa [hn, h1, pow_one] at this
    rw [htop, Subgroup.index_top]
    omega
  obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd h1
  have : Fact q.Prime := ⟨hq⟩
  have hcard : Nat.card (L ≃ₐ[K] L) = n := by rw [IsGalois.card_aut_eq_finrank, hn]
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q (hcard ▸ hqn)

  let H : Subgroup (L ≃ₐ[K] L) := Subgroup.zpowers g
  have : H.Normal := ⟨fun a ha b ↦ by rwa [mul_comm_of_isCyclic b a, mul_inv_cancel_right]⟩
  let M : IntermediateField K L := fixedField H
  have hML : finrank M L = q := by
    rw [finrank_fixedField_eq_card, Nat.card_zpowers, hg]
  have hKM : finrank K M * q = n := by rw [← hML, finrank_mul_finrank, hn]
  have hm_lt : finrank K M < n := by
    have : 0 < finrank K M := finrank_pos
    calc finrank K M < finrank K M * 2 := by omega
      _ ≤ finrank K M * q := Nat.mul_le_mul_left _ hq.two_le
      _ = n := hKM

  have : IsGalois M L := IsGalois.tower_top_of_isGalois K M L
  have : IsCyclic (L ≃ₐ[M] L) :=
    isCyclic_of_prime_card (p := q) (by rw [IsGalois.card_aut_eq_finrank, hML])
  have : IsGalois K M := IsGalois.of_fixedField_normal_subgroup H
  have : IsCyclic (M ≃ₐ[K] M) :=
    isCyclic_of_surjective _ (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) (E := L))
  have hM := ih (finrank K M) hm_lt K M rfl
  have hL := hR.index_le_of_prime (K := M) (L := L) hq hML

  have hcomp : (ideleClassNorm K M).comp (ideleClassNorm M L) = ideleClassNorm K L :=
    MonoidHom.ext fun c ↦ ideleClassNorm_ideleClassNorm c
  have hrange : (ideleClassNorm K L).range =
      (ideleClassNorm M L).range.map (ideleClassNorm K M) := by
    rw [MonoidHom.map_range, hcomp]
  have := index_map_le (ideleClassNorm K M) hL.1 hM.1
  rw [hrange]
  refine ⟨this.1, this.2.trans ?_⟩
  rw [← hKM]
  exact Nat.mul_le_mul hM.2 hL.2

/- English proof (translation)
Introduce `K L _ _ _ _ _ _ _`. Conclude with `(enatCard_quotient_le_iff _ _).2 (hR.index_le_of_finrank_eq _ K L rfl)`.
-/
theorem SecondInequalityRoots.secondInequality (hR : SecondInequalityRoots.{u}) :
    SecondInequality.{u} := by
  intro K L _ _ _ _ _ _ _
  exact (enatCard_quotient_le_iff _ _).2 (hR.index_le_of_finrank_eq _ K L rfl)

end GroundTheory.Global
