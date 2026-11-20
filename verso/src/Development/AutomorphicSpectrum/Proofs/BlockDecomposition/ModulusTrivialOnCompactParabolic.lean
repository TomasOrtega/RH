import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsCompactIsOpen

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BCT ValuativeRel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.ModCompactParab

/- English proof (translation)
Introduce `k _ _ _ _ a b n e K hK p hp`. Set `χ : parab k (two e) →* ℂˣ` to `(deltaHalf k (Two (Fin a) (Fin b))).comp (leviProj k (two e))`. Establish `hχ : Continuous (leviProj k (two e))` using `GlobalTheory.ParabLevel.continuous_leviProj (R := k) (two e)`. Establish `hemb : Topology.IsClosedEmbedding (Subtype.val : parab k (two e) → GL (Fin n) k)` using `(GlobalTheory.ParabLevel.isClosed_parab_two (R := k) e).isClosedEmbedding_subtypeVal`. Set `H : Subgroup (parab k (two e))` to `K.subgroupOf (parab k (two e))`.

Establish `hH : IsCompact (H : Set (parab k (two e)))` using `hemb.isCompact_preimage hK`. Use `haveI : CompactSpace H := isCompact_iff_compactSpace.1 hH`. Establish `hopen : IsOpen ((χ.ker.subgroupOf H : Subgroup H) : Set H)` using `(isSmoothChar_deltaHalf k (m := Two (Fin a) (Fin b))).preimage (hχ.comp continuous_subtype_val)`. Use `haveI : Finite (H ⧸ χ.ker.subgroupOf H) := Subgroup.quotient_finite_of_isOpen _ hopen`. Establish `hidx : (χ.ker.subgroupOf H).index ≠ 0` using `Subgroup.index_ne_zero_of_finite`.

Take `⟨m, hm, -, hmem⟩` from `Subgroup.exists_pow_mem_of_index_ne_zero hidx (⟨p, hp⟩ : H)`. Establish `hpow : deltaHalf k (Two (Fin a) (Fin b)) (leviProj k (two e) p) ^ m = 1`. Establish `h` using `Subgroup.mem_subgroupOf.1 hmem`. Simplify `h` using `[χ, MonoidHom.mem_ker, map_pow]`. Establish `hreal : (√(modulus k (Two (Fin a) (Fin b)) (leviProj k (two e) p)) : ℝ) ^ m = 1`.

Establish `h` using `congrArg (fun u : ℂˣ => (u : ℂ)) hpow`. Simplify using `only [Units.val_pow_eq_pow_val, val_deltaHalf, Units.val_one] at h`. Conclude with `h` after adjusting the coercions. Establish `hone : (√(modulus k (Two (Fin a) (Fin b)) (leviProj k (two e) p)) : ℝ) = 1` using `(pow_eq_one_iff_of_nonneg (Real.sqrt_nonneg _) hm.ne').1 hreal`. Use `ext`.

Rewrite using `[val_deltaHalf, hone]`. Simplify using the standard rewrite rules.
-/
theorem deltaHalf_leviProj_eq_one_of_isCompact :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b n : ℕ)
      (e : Fin a ⊕ Fin b ≃ Fin n) (K : Subgroup (GL (Fin n) k)), IsCompact (K : Set (GL (Fin n) k)) →
      ∀ p : parab k (two e), (p : GL (Fin n) k) ∈ K →
        deltaHalf k (Two (Fin a) (Fin b)) (leviProj k (two e) p) = 1 := by
  intro k _ _ _ _ a b n e K hK p hp
  let χ : parab k (two e) →* ℂˣ := (deltaHalf k (Two (Fin a) (Fin b))).comp (leviProj k (two e))
  have hχ : Continuous (leviProj k (two e)) := GlobalTheory.ParabLevel.continuous_leviProj (R := k) (two e)
  have hemb : Topology.IsClosedEmbedding (Subtype.val : parab k (two e) → GL (Fin n) k) :=
    (GlobalTheory.ParabLevel.isClosed_parab_two (R := k) e).isClosedEmbedding_subtypeVal
  let H : Subgroup (parab k (two e)) := K.subgroupOf (parab k (two e))
  have hH : IsCompact (H : Set (parab k (two e))) := hemb.isCompact_preimage hK
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hH
  have hopen : IsOpen ((χ.ker.subgroupOf H : Subgroup H) : Set H) :=
    (isSmoothChar_deltaHalf k (m := Two (Fin a) (Fin b))).preimage (hχ.comp continuous_subtype_val)
  haveI : Finite (H ⧸ χ.ker.subgroupOf H) := Subgroup.quotient_finite_of_isOpen _ hopen
  have hidx : (χ.ker.subgroupOf H).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain ⟨m, hm, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hidx (⟨p, hp⟩ : H)
  have hpow : deltaHalf k (Two (Fin a) (Fin b)) (leviProj k (two e) p) ^ m = 1 := by
    have h := Subgroup.mem_subgroupOf.1 hmem
    simpa [χ, MonoidHom.mem_ker, map_pow] using h
  have hreal : (√(modulus k (Two (Fin a) (Fin b)) (leviProj k (two e) p)) : ℝ) ^ m = 1 := by
    have h := congrArg (fun u : ℂˣ => (u : ℂ)) hpow
    simp only [Units.val_pow_eq_pow_val, val_deltaHalf, Units.val_one] at h
    exact_mod_cast h
  have hone : (√(modulus k (Two (Fin a) (Fin b)) (leviProj k (two e) p)) : ℝ) = 1 :=
    (pow_eq_one_iff_of_nonneg (Real.sqrt_nonneg _) hm.ne').1 hreal
  ext
  rw [val_deltaHalf, hone]
  simp

end GlobalTheory.CompanionTheory.ModCompactParab
