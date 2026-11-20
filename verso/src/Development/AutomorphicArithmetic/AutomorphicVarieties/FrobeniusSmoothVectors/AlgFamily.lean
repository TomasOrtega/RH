import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgLift

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Introduce `l _ O _ _ F n S C _ _ _ D _ _ _ _ 𝔪 ρ hV hM`. Use `choose hco hmax using alg_quot O C 𝔪 hV`. Establish `hex : ∀ N, ∃! f : S.R →ₐ[O] D ⧸ 𝔪 ^ (N + 1), S.ρ.map (f : S.R →+* D ⧸ 𝔪 ^ (N + 1)) = ρ.map (Ideal.Quotient.mk (𝔪 ^ (N + 1)))`. Introduce `N`. Use `letI := hco N`.

Conclude with `S.univ _ _ (alg_lift C 𝔪 ρ hM _ (Ideal.Quotient.mkₐ O (𝔪 ^ (N + 1))) (fun x hx => by`. Rewrite using `[hmax N]`. Conclude with `Ideal.mem_map_of_mem _ hx))`. Use `choose f hf huniq using hex`. Use `⟨f, hf, ?_, ?_⟩` and prove the remaining obligations.

Introduce `N x d hd`. Establish `hle : 𝔪 ^ (N + 1 + 1) ≤ 𝔪 ^ (N + 1)` using `Ideal.pow_le_pow_right (Nat.le_succ _)`. Establish `hcomp : (Ideal.Quotient.factorₐ O hle).comp (f (N + 1)) = f N`. Apply `huniq N` to reduce the goal to its premises. Establish `e : (((Ideal.Quotient.factorₐ O hle).comp (f (N + 1)) : S.R →ₐ[O] D ⧸ 𝔪 ^ (N + 1)) : S.R →+* D ⧸ 𝔪 ^ (N + 1)) = ((Ideal.Quotient.factorₐ O hle : D ⧸ 𝔪 ^ (N + 1 + 1) →ₐ[O] D ⧸ 𝔪 ^ (N + 1)) : D ⧸ 𝔪 ^ (N + 1 + 1) →+* D ⧸ 𝔪 ^ (N + 1)).comp (f (N + 1) : S.R →+* D ⧸ 𝔪 ^ (N + 1 + 1))` using `rfl`.

Rewrite using `[e, ← NRep.map_map, hf (N + 1), NRep.map_map]`. Both sides reduce to the same expression. Rewrite using `[← hcomp, AlgHom.comp_apply, ← hd]`. Both sides reduce to the same expression. Introduce `N x hx`.

Use `letI := hco N`. Establish `hm : ∀ y ∈ maximalIdeal S.R, f N y ∈ Ideal.map (Ideal.Quotient.mk (𝔪 ^ (N + 1))) 𝔪`. Introduce `y hy`. Rewrite using `[← hmax N, ← res_eq_zero_iff O, res_map, res_eq_zero_iff]`. Conclude with `hy`.

Establish `hle : Ideal.map (f N : S.R →+* D ⧸ 𝔪 ^ (N + 1)) (maximalIdeal S.R) ≤ Ideal.map (Ideal.Quotient.mk (𝔪 ^ (N + 1))) 𝔪`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Conclude with `hm`. Establish `hx'` using `Ideal.mem_map_of_mem (f N : S.R →+* D ⧸ 𝔪 ^ (N + 1)) hx`. Rewrite `hx'` using `[Ideal.map_pow]`.

Establish `h2` using `Ideal.pow_right_mono hle (N + 1) hx'`. Rewrite `h2` using `[← Ideal.map_pow, Ideal.map_quotient_self, Ideal.mem_bot]`. Conclude with `h2`.
-/
theorem UpperTheory.V.Fr.alg_family :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (S : Space O F n) (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {D : Type} [CommRing D] [Algebra O D] [Algebra C D] [IsScalarTower O C D] (𝔪 : Ideal D) (ρ : NRep F n D), IsVertexRing C 𝔪 → IsModel O C 𝔪 ρ → ∃ f : ∀ N : ℕ, S.R →ₐ[O] D ⧸ 𝔪 ^ (N + 1), (∀ N, S.ρ.map (f N : S.R →+* D ⧸ 𝔪 ^ (N + 1)) = ρ.map (Ideal.Quotient.mk (𝔪 ^ (N + 1)))) ∧ (∀ N x d, Ideal.Quotient.mk (𝔪 ^ (N + 1 + 1)) d = f (N + 1) x → Ideal.Quotient.mk (𝔪 ^ (N + 1)) d = f N x) ∧ ∀ N, ∀ x ∈ maximalIdeal S.R ^ (N + 1), f N x = 0 := by
  intro l _ O _ _ F n S C _ _ _ D _ _ _ _ 𝔪 ρ hV hM
  choose hco hmax using alg_quot O C 𝔪 hV
  have hex : ∀ N, ∃! f : S.R →ₐ[O] D ⧸ 𝔪 ^ (N + 1),
      S.ρ.map (f : S.R →+* D ⧸ 𝔪 ^ (N + 1)) = ρ.map (Ideal.Quotient.mk (𝔪 ^ (N + 1))) := by
    intro N
    letI := hco N
    exact S.univ _ _ (alg_lift C 𝔪 ρ hM _ (Ideal.Quotient.mkₐ O (𝔪 ^ (N + 1))) (fun x hx => by
      rw [hmax N]
      exact Ideal.mem_map_of_mem _ hx))
  choose f hf huniq using hex
  refine ⟨f, hf, ?_, ?_⟩
  · intro N x d hd
    have hle : 𝔪 ^ (N + 1 + 1) ≤ 𝔪 ^ (N + 1) := Ideal.pow_le_pow_right (Nat.le_succ _)
    have hcomp : (Ideal.Quotient.factorₐ O hle).comp (f (N + 1)) = f N := by
      apply huniq N
      have e : (((Ideal.Quotient.factorₐ O hle).comp (f (N + 1)) : S.R →ₐ[O] D ⧸ 𝔪 ^ (N + 1)) :
          S.R →+* D ⧸ 𝔪 ^ (N + 1)) =
          ((Ideal.Quotient.factorₐ O hle : D ⧸ 𝔪 ^ (N + 1 + 1) →ₐ[O] D ⧸ 𝔪 ^ (N + 1)) :
            D ⧸ 𝔪 ^ (N + 1 + 1) →+* D ⧸ 𝔪 ^ (N + 1)).comp (f (N + 1) : S.R →+* D ⧸ 𝔪 ^ (N + 1 + 1)) := rfl
      rw [e, ← NRep.map_map, hf (N + 1), NRep.map_map]
      rfl
    rw [← hcomp, AlgHom.comp_apply, ← hd]
    rfl
  · intro N x hx
    letI := hco N
    have hm : ∀ y ∈ maximalIdeal S.R,
        f N y ∈ Ideal.map (Ideal.Quotient.mk (𝔪 ^ (N + 1))) 𝔪 := by
      intro y hy
      rw [← hmax N, ← res_eq_zero_iff O, res_map, res_eq_zero_iff]
      exact hy
    have hle : Ideal.map (f N : S.R →+* D ⧸ 𝔪 ^ (N + 1)) (maximalIdeal S.R) ≤
        Ideal.map (Ideal.Quotient.mk (𝔪 ^ (N + 1))) 𝔪 := by
      rw [Ideal.map_le_iff_le_comap]
      exact hm
    have hx' := Ideal.mem_map_of_mem (f N : S.R →+* D ⧸ 𝔪 ^ (N + 1)) hx
    rw [Ideal.map_pow] at hx'
    have h2 := Ideal.pow_right_mono hle (N + 1) hx'
    rw [← Ideal.map_pow, Ideal.map_quotient_self, Ideal.mem_bot] at h2
    exact h2
