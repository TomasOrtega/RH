import Mathlib
open NumberField

namespace GlobalTheory

/- English proof (translation)
Use `haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ)) E := IsIntegralClosure.isLocalization ℤ ℚ E (𝓞 E)`. Set `g : 𝓞 E →+* Matrix (Fin r) (Fin r) ℚ` to `(Int.castRingHom ℚ).mapMatrix.comp ρ`. Set `S : Subalgebra ℚ (Matrix (Fin r) (Fin r) ℚ)` to `Algebra.adjoin ℚ (Set.range g)`. Use `letI : CommRing S := Algebra.adjoinCommRingOfComm ℚ (by`. Introduce and unpack `_ ⟨a, rfl⟩ _ ⟨b, rfl⟩`.

Rewrite using `[← map_mul, mul_comm, map_mul])`. Set `g₁ : 𝓞 E →+* S` to `g.codRestrict S (fun a => Algebra.subset_adjoin ⟨a, rfl⟩)`. Establish `hg : ∀ y : Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ), IsUnit (g₁ y)`. Introduce and unpack `⟨_, m, hm, rfl⟩`. Establish `hm0 : (m : ℚ) ≠ 0`.

Conclude with `mem_nonZeroDivisors_iff_ne_zero.mp hm` after adjusting the coercions. Establish `: g₁ (algebraMap ℤ (𝓞 E) m) = algebraMap ℚ S (m : ℚ)`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[g₁, g, map_intCast]`. Rewrite using `[this]`.

Conclude with `(IsUnit.mk0 _ hm0).map _`. Set `ρ' : E →+* Matrix (Fin r) (Fin r) ℚ` to `S.val.toRingHom.comp (IsLocalization.lift hg)`. Use `letI : Module E (Fin r → ℚ) := Module.compHom (Fin r → ℚ) ((Matrix.toLinAlgEquiv' : Matrix (Fin r) (Fin r) ℚ ≃ₐ[ℚ] _).toRingEquiv.toRingHom.comp ρ')`. Establish `hq : ρ'.comp (algebraMap ℚ E) = algebraMap ℚ (Matrix (Fin r) (Fin r) ℚ)` using `RingHom.ext_rat _ _`. Use `haveI : IsScalarTower ℚ E (Fin r → ℚ) := by`.

Use `⟨fun q e v => ?_⟩` and prove the remaining obligations. Use `show Matrix.toLin' (ρ' (q • e)) v = q • Matrix.toLin' (ρ' e) v`. Rewrite using `[Algebra.smul_def, map_mul, ← RingHom.comp_apply, hq, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul]`. Both sides reduce to the same expression. Use `⟨Module.finrank E (Fin r → ℚ), ?_⟩` and prove the remaining obligations.

Use `Module.finrank_mul_finrank ℚ E (Fin r → ℚ)` as an intermediate fact. Rewrite `this` using `[Module.finrank_fin_fun]`. Rewrite `this` using `[mul_comm]`. Conclude with `this.symm`.
-/
theorem finrank_dvd_of_ringOfIntegers_to_matrix (E : Type) [Field E] [NumberField E] {r : ℕ}
    (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) : ∃ s : ℕ, r = s * Module.finrank ℚ E := by
  classical
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ)) E :=
    IsIntegralClosure.isLocalization ℤ ℚ E (𝓞 E)
  let g : 𝓞 E →+* Matrix (Fin r) (Fin r) ℚ := (Int.castRingHom ℚ).mapMatrix.comp ρ
  let S : Subalgebra ℚ (Matrix (Fin r) (Fin r) ℚ) := Algebra.adjoin ℚ (Set.range g)
  letI : CommRing S := Algebra.adjoinCommRingOfComm ℚ (by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, mul_comm, map_mul])
  let g₁ : 𝓞 E →+* S := g.codRestrict S (fun a => Algebra.subset_adjoin ⟨a, rfl⟩)
  have hg : ∀ y : Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ), IsUnit (g₁ y) := by
    rintro ⟨_, m, hm, rfl⟩
    have hm0 : (m : ℚ) ≠ 0 := by
      exact_mod_cast mem_nonZeroDivisors_iff_ne_zero.mp hm
    have : g₁ (algebraMap ℤ (𝓞 E) m) = algebraMap ℚ S (m : ℚ) := by
      apply Subtype.ext
      simp [g₁, g, map_intCast]
    rw [this]
    exact (IsUnit.mk0 _ hm0).map _
  let ρ' : E →+* Matrix (Fin r) (Fin r) ℚ := S.val.toRingHom.comp (IsLocalization.lift hg)
  letI : Module E (Fin r → ℚ) :=
    Module.compHom (Fin r → ℚ)
      ((Matrix.toLinAlgEquiv' : Matrix (Fin r) (Fin r) ℚ ≃ₐ[ℚ] _).toRingEquiv.toRingHom.comp ρ')
  have hq : ρ'.comp (algebraMap ℚ E) = algebraMap ℚ (Matrix (Fin r) (Fin r) ℚ) := RingHom.ext_rat _ _
  haveI : IsScalarTower ℚ E (Fin r → ℚ) := by
    refine ⟨fun q e v => ?_⟩
    show Matrix.toLin' (ρ' (q • e)) v = q • Matrix.toLin' (ρ' e) v
    rw [Algebra.smul_def, map_mul, ← RingHom.comp_apply, hq, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, map_smul]
    rfl
  refine ⟨Module.finrank E (Fin r → ℚ), ?_⟩
  have := Module.finrank_mul_finrank ℚ E (Fin r → ℚ)
  rw [Module.finrank_fin_fun] at this
  rw [mul_comm] at this
  exact this.symm

end GlobalTheory
