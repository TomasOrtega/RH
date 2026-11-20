import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt

namespace UpperTheory.Gal.Gen

/- English proof (translation)
Introduce `l _ H _ hH V _ _ _ ρ U hU hne`. Set `act : H → (V ⧸ U) →ₗ[ZMod l] (V ⧸ U)` to `fun h => U.mapQ U (ρ h) (fun u hu => hU h u hu)`. Establish `act_mk : ∀ (h : H) (v : V), act h (U.mkQ v) = U.mkQ (ρ h v)` using `fun h v => rfl`. Use `letI : MulAction H (V ⧸ U) := { smul := fun h x => act h x one_smul := by`. Introduce `x`.

Take `⟨v, rfl⟩` from `U.mkQ_surjective x`. Express the relevant statement in the definitionally equal form `act 1 (U.mkQ v) = U.mkQ v`. Rewrite using `[act_mk]`. Simplify using the standard rewrite rules. Use `mul_smul := by`.

Introduce `g h x`. Take `⟨v, rfl⟩` from `U.mkQ_surjective x`. Express the relevant statement in the definitionally equal form `act (g * h) (U.mkQ v) = act g (act h (U.mkQ v))`. Rewrite using `[act_mk, act_mk, act_mk]`. Simplify using `}`.

Establish `smul_def : ∀ (h : H) (x : V ⧸ U), h • x = act h x` using `fun h x => rfl`. Use `haveI : Nontrivial (V ⧸ U) := Submodule.Quotient.nontrivial_iff.2 hne`. Use `haveI : Finite (V ⧸ U) := Finite.of_surjective U.mkQ U.mkQ_surjective`. Establish `hcard : l ∣ Nat.card (V ⧸ U)`. Rewrite using `[Module.natCard_eq_pow_finrank (K := ZMod l), Nat.card_zmod]`.

Conclude with `dvd_pow_self l Module.finrank_pos.ne'`. Establish `h0 : (0 : V ⧸ U) ∈ MulAction.fixedPoints H (V ⧸ U)`. Introduce `h`. Rewrite using `[smul_def, map_zero]`. Take `⟨x, hx, hx0⟩` from `hH.exists_fixed_point_of_prime_dvd_card_of_fixed_point (V ⧸ U) hcard h0`.

Take `⟨v, rfl⟩` from `U.mkQ_surjective x`. Use `⟨v, ?_, ?_⟩` and prove the remaining obligations. Introduce `hv`. Apply `hx0` to reduce the goal to its premises. Rewrite using `[eq_comm]`.

Simplify using `using hv`. Introduce `h`. Establish `hfix` using `hx h`. Rewrite `hfix` using `[smul_def, act_mk]`. Conclude with `(Submodule.Quotient.eq U).1 hfix`.
-/
theorem fixVec_pf : FixVec := by
  intro l _ H _ hH V _ _ _ ρ U hU hne
  classical
  let act : H → (V ⧸ U) →ₗ[ZMod l] (V ⧸ U) :=
    fun h => U.mapQ U (ρ h) (fun u hu => hU h u hu)
  have act_mk : ∀ (h : H) (v : V), act h (U.mkQ v) = U.mkQ (ρ h v) := fun h v => rfl
  letI : MulAction H (V ⧸ U) :=
    { smul := fun h x => act h x
      one_smul := by
        intro x
        obtain ⟨v, rfl⟩ := U.mkQ_surjective x
        change act 1 (U.mkQ v) = U.mkQ v
        rw [act_mk]
        simp
      mul_smul := by
        intro g h x
        obtain ⟨v, rfl⟩ := U.mkQ_surjective x
        change act (g * h) (U.mkQ v) = act g (act h (U.mkQ v))
        rw [act_mk, act_mk, act_mk]
        simp }
  have smul_def : ∀ (h : H) (x : V ⧸ U), h • x = act h x := fun h x => rfl
  haveI : Nontrivial (V ⧸ U) := Submodule.Quotient.nontrivial_iff.2 hne
  haveI : Finite (V ⧸ U) := Finite.of_surjective U.mkQ U.mkQ_surjective
  have hcard : l ∣ Nat.card (V ⧸ U) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod l), Nat.card_zmod]
    exact dvd_pow_self l Module.finrank_pos.ne'
  have h0 : (0 : V ⧸ U) ∈ MulAction.fixedPoints H (V ⧸ U) := by
    intro h
    rw [smul_def, map_zero]
  obtain ⟨x, hx, hx0⟩ := hH.exists_fixed_point_of_prime_dvd_card_of_fixed_point (V ⧸ U) hcard h0
  obtain ⟨v, rfl⟩ := U.mkQ_surjective x
  refine ⟨v, ?_, ?_⟩
  · intro hv
    apply hx0
    rw [eq_comm]
    simpa using hv
  · intro h
    have hfix := hx h
    rw [smul_def, act_mk] at hfix
    exact (Submodule.Quotient.eq U).1 hfix

end UpperTheory.Gal.Gen
