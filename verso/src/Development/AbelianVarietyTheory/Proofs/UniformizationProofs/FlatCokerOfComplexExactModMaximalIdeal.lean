import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatCokerOfInjectiveModMaximalIdealStatement

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `V A _ _ _ _ _ _ _ _ D _ _ _ _ _ _ d hdd _ hex`. Use `set J : Ideal A := (IsLocalRing.maximalIdeal V).map (algebraMap V A) with hJ`. Establish `hle : LinearMap.range (d 1) ≤ LinearMap.ker (d 0)`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `hdd 0 x`.

Set `u : (D 1 ⧸ LinearMap.range (d 1)) →ₗ[A] D 0` to `(LinearMap.range (d 1)).liftQ (d 0) hle`. Establish `hr : LinearMap.range u = LinearMap.range (d 0)` using `Submodule.range_liftQ _ _ _`. Establish `h` using `GlobalTheory.T.flat_quotient_range_of_injective_mod_maximal V A (D 1 ⧸ LinearMap.range (d 1)) (D 0) u (by`. Introduce `x hx`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`.

Establish `hy : y ∈ LinearMap.range (d 1) ⊔ (J • ⊤ : Submodule A (D 1))` using `hex 0 y hx`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.mp hy`. Establish `ha0 : (Submodule.Quotient.mk a : D 1 ⧸ LinearMap.range (d 1)) = 0` using `(Submodule.Quotient.mk_eq_zero _).mpr ha`. Rewrite using `[Submodule.Quotient.mk_add, ha0, zero_add]`. Establish `: (LinearMap.range (d 1)).mkQ b ∈ (J • ⊤ : Submodule A (D 1)).map (LinearMap.range (d 1)).mkQ` using `Submodule.mem_map_of_mem hb`.

Rewrite `this` using `[Submodule.map_smul'']`. Conclude with `Submodule.smul_mono le_rfl le_top this)`. Rewrite `h` using `[hr]`. Then use the resulting hypothesis.
-/
theorem flat_coker_of_complex_exact_mod_maximalIdeal : ∀ (V A : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Algebra V A] [IsLocalHom (algebraMap V A)] (D : ℕ → Type) [∀ i, AddCommGroup (D i)] [∀ i, Module A (D i)] [∀ i, Module.Finite A (D i)] [∀ i, Module V (D i)] [∀ i, IsScalarTower V A (D i)] [∀ i, Module.Flat V (D i)] (d : ∀ i, D (i + 1) →ₗ[A] D i), (∀ i x, d i (d (i + 1) x) = 0) → (∃ n, ∀ i, n < i → Subsingleton (D i)) → (∀ i (x : D (i + 1)), d i x ∈ (((IsLocalRing.maximalIdeal V).map (algebraMap V A)) • ⊤ : Submodule A (D i)) → x ∈ LinearMap.range (d (i + 1)) ⊔ (((IsLocalRing.maximalIdeal V).map (algebraMap V A)) • ⊤ : Submodule A (D (i + 1)))) → Module.Flat V (D 0 ⧸ LinearMap.range (d 0)) := by
  intro V A _ _ _ _ _ _ _ _ D _ _ _ _ _ _ d hdd _ hex
  set J : Ideal A := (IsLocalRing.maximalIdeal V).map (algebraMap V A) with hJ
  have hle : LinearMap.range (d 1) ≤ LinearMap.ker (d 0) := by
    rintro _ ⟨x, rfl⟩
    exact hdd 0 x
  let u : (D 1 ⧸ LinearMap.range (d 1)) →ₗ[A] D 0 := (LinearMap.range (d 1)).liftQ (d 0) hle
  have hr : LinearMap.range u = LinearMap.range (d 0) := Submodule.range_liftQ _ _ _
  have h := GlobalTheory.T.flat_quotient_range_of_injective_mod_maximal V A (D 1 ⧸ LinearMap.range (d 1)) (D 0) u (by
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hy : y ∈ LinearMap.range (d 1) ⊔ (J • ⊤ : Submodule A (D 1)) := hex 0 y hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    have ha0 : (Submodule.Quotient.mk a : D 1 ⧸ LinearMap.range (d 1)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ha
    rw [Submodule.Quotient.mk_add, ha0, zero_add]
    have : (LinearMap.range (d 1)).mkQ b ∈ (J • ⊤ : Submodule A (D 1)).map (LinearMap.range (d 1)).mkQ :=
      Submodule.mem_map_of_mem hb
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this)
  rwa [hr] at h

end GlobalTheory
