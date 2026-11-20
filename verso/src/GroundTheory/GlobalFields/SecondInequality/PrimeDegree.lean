import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.InfiniteAdeleRingMapInfiniteAdeleRingMap
import GroundTheory.GlobalFields.SecondInequality.Statement

namespace GroundTheory.Global

open NumberField Module Polynomial IntermediateField

universe u

section PrimeDegree

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/- English proof (translation)
Establish `: Fact p.Prime` using `⟨hp⟩`. Establish `: NeZero p` using `⟨hp.ne_zero⟩`. Set `E` to `CyclotomicField p L`. Set `ζ : E` to `IsCyclotomicExtension.zeta p L E`. Establish `hζ : IsPrimitiveRoot ζ p` using `IsCyclotomicExtension.zeta_spec p L E`.

Set `K' : IntermediateField K E` to `K⟮ζ⟯`. Establish `hroot : aeval ζ (cyclotomic p K) = 0`. Rewrite using `[aeval_def, eval₂_eq_eval_map, map_cyclotomic]`. Conclude with `hζ.isRoot_cyclotomic hp.pos`. Establish `hd_lt : finrank K K' < p`.

Rewrite using `[adjoin.finrank (Algebra.IsIntegral.isIntegral ζ)]`. Establish `h1` using `minpoly.degree_le_of_ne_zero K ζ (cyclotomic_ne_zero p K) hroot`. Establish `h2 : (minpoly K ζ).natDegree ≤ (cyclotomic p K).natDegree` using `natDegree_le_natDegree h1`. Rewrite `h2` using `[natDegree_cyclotomic, Nat.totient_prime hp]`. Use `hp.two_le` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hd_pos : 0 < finrank K K'` using `finrank_pos`. Establish `hcop : (finrank K K').Coprime p` using `((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hd_pos hd_lt)).symm`. Set `ζ' : K'` to `⟨ζ, mem_adjoin_simple_self K ζ⟩`. Establish `hζ' : IsPrimitiveRoot ζ' p` using `(IsPrimitiveRoot.map_iff_of_injective (f := algebraMap K' E) (algebraMap K' E).injective).1 hζ`.

Establish `hroots : HasEnoughRootsOfUnity K' p` using `⟨⟨ζ', hζ'⟩, rootsOfUnity.isCyclic K' p⟩`. Take `⟨f, hfsep, hf⟩` from `IsGalois.is_separable_splitting_field (F := K) (E := L)`. Use `hf` as an intermediate fact. Establish `: IsSplittingField L E ((cyclotomic p K).map (algebraMap K L))`. Rewrite using `[map_cyclotomic]`.

Conclude with `IsCyclotomicExtension.splitting_field_cyclotomic p L E`. Establish `: IsSplittingField K E (f * cyclotomic p K)` using `IsSplittingField.mul (F := K) (K := L) (L := E) f (cyclotomic p K) hfsep.ne_zero (cyclotomic_ne_zero p K)`. Establish `: IsGalois K E` using `{ to_isSeparable := inferInstance, to_normal := Normal.of_isSplittingField (f * cyclotomic p K) }`. Establish `: IsGalois K' E` using `IsGalois.tower_top_of_isGalois K K' E`. Set `L' : IntermediateField K E` to `(IsScalarTower.toAlgHom K L E).fieldRange`.

Establish `hsup : K' ⊔ L' = ⊤`. Rewrite using `[eq_top_iff]`. Introduce and unpack `x -`. Establish `hx : x ∈ Algebra.adjoin L ({ζ} : Set E)`. Rewrite using `[IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ]`.

Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem y hy`. Rewrite using `[Set.mem_singleton_iff.1 hy]`. Conclude with `le_sup_left (a := K') (mem_adjoin_simple_self K ζ)`.

Consider the case `algebraMap l => exact le_sup_right (b := L') ⟨l, rfl⟩`. Consider the case `add _ _ _ _ h1 h2 => exact add_mem h1 h2`. Consider the case `mul _ _ _ _ h1 h2 => exact mul_mem h1 h2`. Establish `hL' : finrank K L' = p`. Conclude with `(AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L E)).toLinearEquiv.finrank_eq.symm.trans hL`.

Establish `htow1 : finrank K K' * finrank K' E = finrank K E` using `finrank_mul_finrank K K' E`. Establish `htow2 : finrank K L * finrank L E = finrank K E` using `finrank_mul_finrank K L E`. Establish `hle : finrank K E ≤ finrank K K' * p`. Use `finrank_sup_le K' L'` as an intermediate fact. Rewrite `this` using `[hsup, finrank_top', hL']`. Then use the resulting hypothesis.

Establish `hdeg : finrank K' E = p`. Establish `h1 : finrank K' E ≤ p`. Rewrite `hle` using `[← htow1]`. Conclude with `Nat.le_of_mul_le_mul_left hle hd_pos`. Establish `h2 : p ∣ finrank K K' * finrank K' E`.

Rewrite using `[htow1, ← htow2, hL]`. Conclude with `dvd_mul_right p _`. Establish `h3 : p ∣ finrank K' E` using `(Nat.Coprime.dvd_of_dvd_mul_left hcop.symm h2)`. Conclude with `le_antisymm h1 (Nat.le_of_dvd finrank_pos h3)`. Establish `: IsCyclic (E ≃ₐ[K'] E)` using `isCyclic_of_prime_card (p := p) (by rw [IsGalois.card_aut_eq_finrank, hdeg])`.

Establish `hE` using `(enatCard_quotient_le_iff _ p).1 (hR K' E p hp hroots hdeg)`. Establish `hcomap : (ideleClassNorm K' E).range.comap (ideleClassMap K K') ≤ (ideleClassNorm K L).range`. Introduce `c hc`. Take `⟨y, hy⟩` from `hc`. Use `mem_of_pow_mem_of_coprime hcop ?_ (hL ▸ pow_finrank_mem_range_ideleClassNorm c)` and prove the remaining obligations.

Use `⟨ideleClassNorm L E y, ?_⟩` and prove the remaining obligations. Rewrite using `[ideleClassNorm_ideleClassNorm, ← ideleClassNorm_ideleClassNorm (L := K'), hy, ideleClassNorm_ideleClassMap]`. Use `index_le_of_comap_le (ideleClassMap K K') hcomap hE.1` as an intermediate fact. Conclude with `⟨this.1, this.2.trans hE.2⟩`.
-/
theorem SecondInequalityRoots.index_le_of_prime (hR : SecondInequalityRoots.{u}) [IsGalois K L]
    {p : ℕ} (hp : p.Prime) (hL : finrank K L = p) :
    (ideleClassNorm K L).range.index ≠ 0 ∧ (ideleClassNorm K L).range.index ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  let E := CyclotomicField p L
  let ζ : E := IsCyclotomicExtension.zeta p L E
  have hζ : IsPrimitiveRoot ζ p := IsCyclotomicExtension.zeta_spec p L E
  let K' : IntermediateField K E := K⟮ζ⟯

  have hroot : aeval ζ (cyclotomic p K) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic hp.pos
  have hd_lt : finrank K K' < p := by
    rw [adjoin.finrank (Algebra.IsIntegral.isIntegral ζ)]
    have h1 := minpoly.degree_le_of_ne_zero K ζ (cyclotomic_ne_zero p K) hroot
    have h2 : (minpoly K ζ).natDegree ≤ (cyclotomic p K).natDegree := natDegree_le_natDegree h1
    rw [natDegree_cyclotomic, Nat.totient_prime hp] at h2
    have := hp.two_le
    omega
  have hd_pos : 0 < finrank K K' := finrank_pos
  have hcop : (finrank K K').Coprime p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hd_pos hd_lt)).symm

  let ζ' : K' := ⟨ζ, mem_adjoin_simple_self K ζ⟩
  have hζ' : IsPrimitiveRoot ζ' p :=
    (IsPrimitiveRoot.map_iff_of_injective (f := algebraMap K' E) (algebraMap K' E).injective).1 hζ
  have hroots : HasEnoughRootsOfUnity K' p := ⟨⟨ζ', hζ'⟩, rootsOfUnity.isCyclic K' p⟩

  obtain ⟨f, hfsep, hf⟩ := IsGalois.is_separable_splitting_field (F := K) (E := L)
  have := hf
  have : IsSplittingField L E ((cyclotomic p K).map (algebraMap K L)) := by
    rw [map_cyclotomic]
    exact IsCyclotomicExtension.splitting_field_cyclotomic p L E
  have : IsSplittingField K E (f * cyclotomic p K) :=
    IsSplittingField.mul (F := K) (K := L) (L := E) f (cyclotomic p K) hfsep.ne_zero (cyclotomic_ne_zero p K)
  have : IsGalois K E :=
    { to_isSeparable := inferInstance, to_normal := Normal.of_isSplittingField (f * cyclotomic p K) }
  have : IsGalois K' E := IsGalois.tower_top_of_isGalois K K' E

  let L' : IntermediateField K E := (IsScalarTower.toAlgHom K L E).fieldRange
  have hsup : K' ⊔ L' = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    have hx : x ∈ Algebra.adjoin L ({ζ} : Set E) := by
      rw [IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      rw [Set.mem_singleton_iff.1 hy]
      exact le_sup_left (a := K') (mem_adjoin_simple_self K ζ)
    | algebraMap l => exact le_sup_right (b := L') ⟨l, rfl⟩
    | add _ _ _ _ h1 h2 => exact add_mem h1 h2
    | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2
  have hL' : finrank K L' = p := by
    exact (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L E)).toLinearEquiv.finrank_eq.symm.trans hL

  have htow1 : finrank K K' * finrank K' E = finrank K E := finrank_mul_finrank K K' E
  have htow2 : finrank K L * finrank L E = finrank K E := finrank_mul_finrank K L E
  have hle : finrank K E ≤ finrank K K' * p := by
    have := finrank_sup_le K' L'
    rwa [hsup, finrank_top', hL'] at this
  have hdeg : finrank K' E = p := by
    have h1 : finrank K' E ≤ p := by
      rw [← htow1] at hle
      exact Nat.le_of_mul_le_mul_left hle hd_pos
    have h2 : p ∣ finrank K K' * finrank K' E := by
      rw [htow1, ← htow2, hL]
      exact dvd_mul_right p _
    have h3 : p ∣ finrank K' E := (Nat.Coprime.dvd_of_dvd_mul_left hcop.symm h2)
    exact le_antisymm h1 (Nat.le_of_dvd finrank_pos h3)
  have : IsCyclic (E ≃ₐ[K'] E) :=
    isCyclic_of_prime_card (p := p) (by rw [IsGalois.card_aut_eq_finrank, hdeg])

  have hE := (enatCard_quotient_le_iff _ p).1 (hR K' E p hp hroots hdeg)

  have hcomap : (ideleClassNorm K' E).range.comap (ideleClassMap K K') ≤
      (ideleClassNorm K L).range := by
    intro c hc
    obtain ⟨y, hy⟩ := hc
    refine mem_of_pow_mem_of_coprime hcop ?_ (hL ▸ pow_finrank_mem_range_ideleClassNorm c)
    refine ⟨ideleClassNorm L E y, ?_⟩
    rw [ideleClassNorm_ideleClassNorm, ← ideleClassNorm_ideleClassNorm (L := K'), hy,
      ideleClassNorm_ideleClassMap]
  have := index_le_of_comap_le (ideleClassMap K K') hcomap hE.1
  exact ⟨this.1, this.2.trans hE.2⟩

end PrimeDegree

end GroundTheory.Global
