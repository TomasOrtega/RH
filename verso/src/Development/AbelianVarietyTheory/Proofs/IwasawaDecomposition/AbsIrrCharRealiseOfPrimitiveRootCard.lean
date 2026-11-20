import Mathlib
import Formalism.LocalToGlobal.Columns.GoodXgFin
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharOfIsPrimitiveRoot
open Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.BrauerRealise

variable {G : Type} [Group G] [Fintype G]

omit [Fintype G] in

/- English proof (translation)
Establish `hcard : (Nat.card G : k) ≠ 0` using `Nat.cast_ne_zero.mpr Nat.card_pos.ne'`. Use `letI : Invertible (Nat.card G : k) := invertibleOfNonzero hcard`. Establish `h1` using `Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ`. Rewrite `h1` using `[h, inv_mul_cancel₀ hcard]`. Establish `hfr : Module.finrank k (ρ.IntertwiningMap ρ) = 1` using `by exact_mod_cast h1.symm`.

Establish `hnt : Nontrivial V`. Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[not_nontrivial_iff_subsingleton]`. Establish `h0 : ∀ g, ρ.character g = 0` using `fun g => by`. Rewrite using `[Representation.character, Subsingleton.elim (ρ g) 0, map_zero]`.

Simplify using `only [h0, zero_mul, Finset.sum_const_zero] at h`. Conclude with `hcard h.symm`. Set `idI : ρ.IntertwiningMap ρ` to `⟨LinearMap.id, fun g => by rw [LinearMap.id_comp, LinearMap.comp_id]⟩`. Establish `hid0 : idI ≠ 0`. Take `⟨v, hv⟩` from `exists_ne (0 : V)`.

Introduce `e`. Conclude with `hv (congrArg (fun φ : ρ.IntertwiningMap ρ => φ.toLinearMap v) e)`. Establish `hcG : (Fintype.card G : k) ≠ 0` using `by rw [← Nat.card_eq_fintype_card]; exact hcard`. Use `{ exists_pair_ne := ⟨⊥, ⊤, fun e => ?_⟩, eq_bot_or_eq_top := fun U => ?_ }` and prove the remaining obligations. Conclude with `(top_ne_bot : (⊤ : Submodule k V) ≠ ⊥) (congrArg Subrepresentation.toSubmodule e).symm`.

Distinguish the cases in `hU : U.toSubmodule = ⊥`. Conclude with `Or.inl (Subrepresentation.toSubmodule_injective hU)`. Use `right`. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Use `show U.toSubmodule = ⊤`.

Take `⟨W0, hW0⟩` from `Submodule.exists_isCompl U.toSubmodule`. Set `q : V →ₗ[k] V` to `U.toSubmodule.subtype ∘ₗ Submodule.projectionOnto U.toSubmodule W0 hW0`. Establish `hqU : ∀ u ∈ U.toSubmodule, q u = u` using `fun u hu => congrArg Subtype.val (Submodule.projectionOnto_apply_left hW0 ⟨u, hu⟩)`. Establish `hqR : ∀ v, q v ∈ U.toSubmodule` using `fun v => (Submodule.projectionOnto _ _ hW0 v).2`. Establish `hinv : ∀ g, ∀ v ∈ U.toSubmodule, ρ g v ∈ U.toSubmodule` using `fun g v hv => U.apply_mem_toSubmodule g hv`.

Establish `hρρ : ∀ g (v : V), ρ g (ρ g⁻¹ v) = v` using `fun g v => by`. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Set `P : V →ₗ[k] V` to `(Fintype.card G : k)⁻¹ • ∑ g : G, ρ g ∘ₗ q ∘ₗ ρ g⁻¹`. Establish `hPv : ∀ v, P v = (Fintype.card G : k)⁻¹ • ∑ g : G, ρ g (q (ρ g⁻¹ v))` using `fun v => by`. Simplify using `[P, LinearMap.sum_apply]`.

Establish `hPI : ∀ h, P ∘ₗ ρ h = ρ h ∘ₗ P`. Introduce `h`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, hPv, hPv, map_smul, map_sum]`.

Use `congr 1`. Use `Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ (fun g => ?_)` and prove the remaining obligations. Simplify using `only [Equiv.coe_mulLeft, mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]`. Rewrite using `[hρρ]`. Take `⟨c, hc⟩` from `(finrank_eq_one_iff_of_nonzero' idI hid0).mp hfr ⟨P, hPI⟩`.

Establish `hcv : ∀ v, c • v = P v` using `fun v => congrArg (fun φ : ρ.IntertwiningMap ρ => φ.toLinearMap v) hc`. Establish `hPU : ∀ u ∈ U.toSubmodule, P u = u` using `fun u hu => by`. Rewrite using `[hPv]`. Establish `: ∀ g : G, ρ g (q (ρ g⁻¹ u)) = u` using `fun g => by rw [hqU _ (hinv _ _ hu), hρρ]`. Simplify using `only [this, Finset.sum_const, Finset.card_univ]`.

Rewrite using `[← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hcG, one_smul]`. Take `⟨u, hu, hu0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hU`. Establish `hc1 : c = 1`. Establish `e1` using `hcv u`. Rewrite `e1` using `[hPU u hu]`.

Establish `: (c - 1) • u = 0` using `by rw [sub_smul, e1, one_smul, sub_self]`. Break down `smul_eq_zero.mp this with h2 | h2` into its components or cases. Conclude with `sub_eq_zero.mp h2`. Conclude with `absurd h2 hu0`. Rewrite using `[Submodule.eq_top_iff']`.

Introduce `v`. Establish `e2` using `hcv v`. Rewrite `e2` using `[hc1, one_smul]`. Rewrite using `[e2, hPv]`. Conclude with `Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g _ => hinv g _ (hqR _))`.
-/
theorem isIrreducible_of_sum_char_mul_char_inv [Fintype G] {k : Type} [Field k] [CharZero k] {V : Type}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V)
    (h : ∑ x, ρ.character x * ρ.character x⁻¹ = (Nat.card G : k)) : ρ.IsIrreducible := by
  classical
  have hcard : (Nat.card G : k) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : k) := invertibleOfNonzero hcard
  have h1 := Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ
  rw [h, inv_mul_cancel₀ hcard] at h1
  have hfr : Module.finrank k (ρ.IntertwiningMap ρ) = 1 := by exact_mod_cast h1.symm
  have hnt : Nontrivial V := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have h0 : ∀ g, ρ.character g = 0 := fun g => by
      rw [Representation.character, Subsingleton.elim (ρ g) 0, map_zero]
    simp only [h0, zero_mul, Finset.sum_const_zero] at h
    exact hcard h.symm
  let idI : ρ.IntertwiningMap ρ := ⟨LinearMap.id, fun g => by rw [LinearMap.id_comp, LinearMap.comp_id]⟩
  have hid0 : idI ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    intro e
    exact hv (congrArg (fun φ : ρ.IntertwiningMap ρ => φ.toLinearMap v) e)
  have hcG : (Fintype.card G : k) ≠ 0 := by rw [← Nat.card_eq_fintype_card]; exact hcard
  refine { exists_pair_ne := ⟨⊥, ⊤, fun e => ?_⟩, eq_bot_or_eq_top := fun U => ?_ }
  · exact (top_ne_bot : (⊤ : Submodule k V) ≠ ⊥) (congrArg Subrepresentation.toSubmodule e).symm
  · by_cases hU : U.toSubmodule = ⊥
    · exact Or.inl (Subrepresentation.toSubmodule_injective hU)
    · right
      apply Subrepresentation.toSubmodule_injective
      show U.toSubmodule = ⊤
      obtain ⟨W0, hW0⟩ := Submodule.exists_isCompl U.toSubmodule
      let q : V →ₗ[k] V := U.toSubmodule.subtype ∘ₗ Submodule.projectionOnto U.toSubmodule W0 hW0
      have hqU : ∀ u ∈ U.toSubmodule, q u = u := fun u hu =>
        congrArg Subtype.val (Submodule.projectionOnto_apply_left hW0 ⟨u, hu⟩)
      have hqR : ∀ v, q v ∈ U.toSubmodule := fun v => (Submodule.projectionOnto _ _ hW0 v).2
      have hinv : ∀ g, ∀ v ∈ U.toSubmodule, ρ g v ∈ U.toSubmodule := fun g v hv => U.apply_mem_toSubmodule g hv
      have hρρ : ∀ g (v : V), ρ g (ρ g⁻¹ v) = v := fun g v => by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      let P : V →ₗ[k] V := (Fintype.card G : k)⁻¹ • ∑ g : G, ρ g ∘ₗ q ∘ₗ ρ g⁻¹
      have hPv : ∀ v, P v = (Fintype.card G : k)⁻¹ • ∑ g : G, ρ g (q (ρ g⁻¹ v)) := fun v => by
        simp [P, LinearMap.sum_apply]
      have hPI : ∀ h, P ∘ₗ ρ h = ρ h ∘ₗ P := by
        intro h
        apply LinearMap.ext
        intro v
        rw [LinearMap.comp_apply, LinearMap.comp_apply, hPv, hPv, map_smul, map_sum]
        congr 1
        refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ (fun g => ?_)
        simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]
        rw [hρρ]
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' idI hid0).mp hfr ⟨P, hPI⟩
      have hcv : ∀ v, c • v = P v := fun v => congrArg (fun φ : ρ.IntertwiningMap ρ => φ.toLinearMap v) hc
      have hPU : ∀ u ∈ U.toSubmodule, P u = u := fun u hu => by
        rw [hPv]
        have : ∀ g : G, ρ g (q (ρ g⁻¹ u)) = u := fun g => by rw [hqU _ (hinv _ _ hu), hρρ]
        simp only [this, Finset.sum_const, Finset.card_univ]
        rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hcG, one_smul]
      obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
      have hc1 : c = 1 := by
        have e1 := hcv u
        rw [hPU u hu] at e1
        have : (c - 1) • u = 0 := by rw [sub_smul, e1, one_smul, sub_self]
        rcases smul_eq_zero.mp this with h2 | h2
        · exact sub_eq_zero.mp h2
        · exact absurd h2 hu0
      rw [Submodule.eq_top_iff']
      intro v
      have e2 := hcv v
      rw [hc1, one_smul] at e2
      rw [e2, hPv]
      exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g _ => hinv g _ (hqR _))

/- English proof (translation)
Rewrite using `[Representation.character, LinearMap.trace_eq_matrix_trace _ (Pi.basisFun _ (Fin n)), LinearMap.toMatrix_eq_toMatrix']`.
-/
theorem character_eq_trace_toMatrix' {k : Type} [Field k] {n : ℕ} (ρ : Representation k G (Fin n → k)) (g : G) :
    ρ.character g = Matrix.trace (LinearMap.toMatrix' (ρ g)) := by
  rw [Representation.character, LinearMap.trace_eq_matrix_trace _ (Pi.basisFun _ (Fin n)),
    LinearMap.toMatrix_eq_toMatrix']

def mapScalars {K k : Type} [Field K] [Field k] (f : K →+* k) {n : ℕ} (ρ : Representation K G (Fin n → K)) :
    Representation k G (Fin n → k) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] Module.End k (Fin n → k)).toRingEquiv.toMonoidHom.comp
    ((f.mapMatrix : Matrix (Fin n) (Fin n) K →+* Matrix (Fin n) (Fin n) k).toMonoidHom.comp
      ((LinearMap.toMatrixAlgEquiv' : Module.End K (Fin n → K) ≃ₐ[K] Matrix (Fin n) (Fin n) K).toRingEquiv.toMonoidHom.comp ρ))

/- English proof (translation)
Rewrite using `[character_eq_trace_toMatrix', character_eq_trace_toMatrix']`. Simplify using `[mapScalars, Matrix.trace, Matrix.diag, map_sum]`.
-/
theorem character_mapScalars {K k : Type} [Field K] [Field k] (f : K →+* k) {n : ℕ}
    (ρ : Representation K G (Fin n → K)) (g : G) : (mapScalars f ρ).character g = f (ρ.character g) := by
  rw [character_eq_trace_toMatrix', character_eq_trace_toMatrix']
  simp [mapScalars, Matrix.trace, Matrix.diag, map_sum]

/- English proof (translation)
Use `haveI : CharZero K := σ.charZero`. Use `letI : Algebra K ℂ := σ.toAlgebra`. Establish `hψC : GlobalTheory.BI.IsChar ℂ ℂ ψ`. Take `⟨n, ρ, -, hρ⟩` from `hψ`. Conclude with `⟨n, ρ, fun g => by rw [← hρ]; rfl⟩`.

Take `⟨m, τ, hτ⟩` from `GlobalTheory.BI.isChar_of_isPrimitiveRoot K ℂ (Fintype.card G) z Fintype.card_ne_zero hz G (fun g => pow_card_eq_one) ψ hψC`. Establish `hτσ : ∀ g, σ (τ.character g) = ψ g` using `fun g => (hτ g).symm`. Use `⟨τ.character, ?_, hτσ⟩` and prove the remaining obligations. Set `A` to `AlgebraicClosure K`. Set `ρ' : Representation A G (Fin m → A)` to `mapScalars (algebraMap K A) τ`.

Establish `hch : ∀ g, ρ'.character g = algebraMap K A (τ.character g)` using `character_mapScalars _ τ`. Use `⟨m, ρ', isIrreducible_of_sum_char_mul_char_inv ρ' ?_, hch⟩` and prove the remaining obligations. Establish `horth` using `Formalism.L2.Col.gx_orth (G := G) (k := ℂ) hψ hψ`. Rewrite `horth` using `[if_pos rfl]`. Establish `hcardC : (Nat.card G : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Nat.card_pos.ne'`.

Establish `hsumC : ∑ g, ψ g * ψ g⁻¹ = (Nat.card G : ℂ)`. Rewrite using `[← mul_one (Nat.card G : ℂ), ← horth, ← mul_assoc, mul_inv_cancel₀ hcardC, one_mul]`. Establish `hsumK : ∑ g, τ.character g * τ.character g⁻¹ = (Nat.card G : K)`. Apply `σ.injective` to reduce the goal to its premises. Rewrite using `[map_sum, map_natCast, ← hsumC]`.

Conclude with `Finset.sum_congr rfl fun g _ => by rw [map_mul, hτσ, hτσ]`. Simplify using `only [hch, ← map_mul, ← map_sum, hsumK, map_natCast]`.
-/
theorem absIrr_realise_of_isPrimitiveRoot {K : Type} [Field K] (σ : K →+* ℂ) (z : K)
    (hz : IsPrimitiveRoot z (Fintype.card G)) (ψ : G → ℂ) (hψ : ψ ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ) :
    ∃ χ : G → K, IsAbsIrrChar χ ∧ ∀ g, σ (χ g) = ψ g := by
  classical
  haveI : CharZero K := σ.charZero
  letI : Algebra K ℂ := σ.toAlgebra
  have hψC : GlobalTheory.BI.IsChar ℂ ℂ ψ := by
    obtain ⟨n, ρ, -, hρ⟩ := hψ
    exact ⟨n, ρ, fun g => by rw [← hρ]; rfl⟩
  obtain ⟨m, τ, hτ⟩ := GlobalTheory.BI.isChar_of_isPrimitiveRoot K ℂ (Fintype.card G) z Fintype.card_ne_zero hz G
    (fun g => pow_card_eq_one) ψ hψC
  have hτσ : ∀ g, σ (τ.character g) = ψ g := fun g => (hτ g).symm
  refine ⟨τ.character, ?_, hτσ⟩
  let A := AlgebraicClosure K
  let ρ' : Representation A G (Fin m → A) := mapScalars (algebraMap K A) τ
  have hch : ∀ g, ρ'.character g = algebraMap K A (τ.character g) := character_mapScalars _ τ
  refine ⟨m, ρ', isIrreducible_of_sum_char_mul_char_inv ρ' ?_, hch⟩
  have horth := Formalism.L2.Col.gx_orth (G := G) (k := ℂ) hψ hψ
  rw [if_pos rfl] at horth
  have hcardC : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hsumC : ∑ g, ψ g * ψ g⁻¹ = (Nat.card G : ℂ) := by
    rw [← mul_one (Nat.card G : ℂ), ← horth, ← mul_assoc, mul_inv_cancel₀ hcardC, one_mul]
  have hsumK : ∑ g, τ.character g * τ.character g⁻¹ = (Nat.card G : K) := by
    apply σ.injective
    rw [map_sum, map_natCast, ← hsumC]
    exact Finset.sum_congr rfl fun g _ => by rw [map_mul, hτσ, hτσ]
  simp only [hch, ← map_mul, ← map_sum, hsumK, map_natCast]

end GlobalTheory.BrauerRealise
