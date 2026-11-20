import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange

namespace GroundTheory.Global

open NumberField

def FirstInequality.{u} : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)],
    (Module.finrank K L : ℕ∞) ≤ ENat.card (IdeleClassGroup K ⧸ (ideleClassNorm K L).range)

section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Take `⟨c, hc⟩` from `(MonoidHom.mem_range).1 (h ▸ Subgroup.mem_top (IdeleClassGroup.mk K x))`.

Take `⟨y, rfl⟩` from `IdeleClassGroup.mk_surjective L c`. Rewrite `hc` using `[ideleClassNorm_mk]`. Establish `hd : (ideleNorm K L y)⁻¹ * x ∈ (IdeleGroup.diagonal K).range` using `QuotientGroup.eq.1 hc`. Establish `: x = ideleNorm K L y * ((ideleNorm K L y)⁻¹ * x)` using `by group`. Rewrite using `[this]`.

Conclude with `Subgroup.mul_mem_sup ⟨y, rfl⟩ hd`. Introduce `h`. Rewrite using `[eq_top_iff]`. Introduce `c _`. Take `⟨x, rfl⟩` from `IdeleClassGroup.mk_surjective K c`.

Take `⟨_, ⟨y, rfl⟩, z, hz, hyz⟩` from `Subgroup.mem_sup.1 (h ▸ Subgroup.mem_top x)`. Use `⟨IdeleClassGroup.mk L y, ?_⟩` and prove the remaining obligations. Rewrite using `[ideleClassNorm_mk, ← hyz]`. Use `QuotientGroup.eq.2 ?_` and prove the remaining obligations. Simplify using `using hz`.
-/
theorem ideleClassNorm_range_eq_top_iff :
    (ideleClassNorm K L).range = ⊤ ↔
      (ideleNorm K L).range ⊔ (IdeleGroup.diagonal K).range = ⊤ := by
  constructor
  · intro h
    rw [eq_top_iff]
    intro x _
    obtain ⟨c, hc⟩ := (MonoidHom.mem_range).1 (h ▸ Subgroup.mem_top (IdeleClassGroup.mk K x))
    obtain ⟨y, rfl⟩ := IdeleClassGroup.mk_surjective L c
    rw [ideleClassNorm_mk] at hc
    have hd : (ideleNorm K L y)⁻¹ * x ∈ (IdeleGroup.diagonal K).range :=
      QuotientGroup.eq.1 hc
    have : x = ideleNorm K L y * ((ideleNorm K L y)⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem_sup ⟨y, rfl⟩ hd
  · intro h
    rw [eq_top_iff]
    intro c _
    obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
    obtain ⟨_, ⟨y, rfl⟩, z, hz, hyz⟩ := Subgroup.mem_sup.1 (h ▸ Subgroup.mem_top x)
    refine ⟨IdeleClassGroup.mk L y, ?_⟩
    rw [ideleClassNorm_mk, ← hyz]
    refine QuotientGroup.eq.2 ?_
    simpa using hz

end

section

universe u

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]

/- English proof (translation)
Establish `hle` using `hFI K L`. Rewrite `hle` using `[h]`. Use `QuotientGroup.subsingleton_quotient_top (G := IdeleClassGroup K)` as an intermediate fact. Establish `h1 : ENat.card (IdeleClassGroup K ⧸ (⊤ : Subgroup (IdeleClassGroup K))) ≤ 1` using `(ENat.card_le_one_iff_subsingleton _).2 inferInstance`. Establish `h2 : (Module.finrank K L : ℕ∞) ≤ 1` using `hle.trans h1`.

Establish `hpos : 0 < Module.finrank K L` using `Module.finrank_pos`. Establish `h3 : Module.finrank K L ≤ 1` using `by exact_mod_cast h2`. Use linear arithmetic over natural numbers and integers.
-/
theorem FirstInequality.finrank_eq_one_of_range_eq_top (hFI : FirstInequality.{u})
    (h : (ideleClassNorm K L).range = ⊤) : Module.finrank K L = 1 := by
  have hle := hFI K L
  rw [h] at hle
  have := QuotientGroup.subsingleton_quotient_top (G := IdeleClassGroup K)
  have h1 : ENat.card (IdeleClassGroup K ⧸ (⊤ : Subgroup (IdeleClassGroup K))) ≤ 1 :=
    (ENat.card_le_one_iff_subsingleton _).2 inferInstance
  have h2 : (Module.finrank K L : ℕ∞) ≤ 1 := hle.trans h1
  have hpos : 0 < Module.finrank K L := Module.finrank_pos
  have h3 : Module.finrank K L ≤ 1 := by exact_mod_cast h2
  omega

/- English proof (translation)
The claim follows from `hFI.finrank_eq_one_of_range_eq_top (ideleClassNorm_range_eq_top_iff.2 h)`.
-/
theorem FirstInequality.finrank_eq_one_of_sup_eq_top (hFI : FirstInequality.{u})
    (h : (ideleNorm K L).range ⊔ (IdeleGroup.diagonal K).range = ⊤) :
    Module.finrank K L = 1 :=
  hFI.finrank_eq_one_of_range_eq_top (ideleClassNorm_range_eq_top_iff.2 h)

end

end GroundTheory.Global
