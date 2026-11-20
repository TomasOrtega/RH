import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DiscriminantEigenProjector
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.EigLat

/- English proof (translation)
Simplify using `[eigSp, sub_eq_zero]`.
-/
theorem mem_eigSp_iff' {k W O : Type} [Field k] [AddCommGroup W] [Module k W] [CommRing O]
    {ρ : O →+* Module.End k W} {τ : O →+* k} {x : W} : x ∈ eigSp ρ τ ↔ ∀ a, ρ a x = τ a • x := by
  simp [eigSp, sub_eq_zero]

/- English proof (translation)
Simplify using `only [hx, smul_smul, map_sum, map_mul, Finset.sum_smul]`.
-/
theorem sum_smul_of_eig {k W O : Type} [Field k] [AddCommGroup W] [Module k W] [CommRing O]
    {ρ : O →+* Module.End k W} {τ : O →+* k} {n : ℕ} (a c : Fin n → O) {x : W}
    (hx : ∀ b, ρ b x = τ b • x) :
    ∑ m, τ (c m) • ρ (a m) x = τ (∑ m, c m * a m) • x := by
  simp only [hx, smul_smul, map_sum, map_mul, Finset.sum_smul]

/- English proof (translation)
Introduce `F _ _ Ω Ω' _ _ _ i V V' _ _ _ _ j ρ ρ' σ R R' L hj hρ hiR hL hσ hd`. Take `⟨n, a, c, hsum, heq⟩` from `ScaledCasimir.exists_scaledCasimir F`. Establish `hd0 : ((NumberField.discr F : ℤ) : Ω) ≠ 0` using `Int.cast_ne_zero.2 (NumberField.discr_ne_zero F)`. Establish `hσd : σ (∑ m, c m * a m) = ((NumberField.discr F : ℤ) : Ω)` using `by rw [hsum, map_intCast]`. Establish `hiσd : (i.comp σ) (∑ m, c m * a m) = i ((NumberField.discr F : ℤ) : Ω)`.

Rewrite using `[RingHom.comp_apply, hσd]`. Establish `hid0 : i ((NumberField.discr F : ℤ) : Ω) ≠ 0` using `(map_ne_zero i).2 hd0`. Set `P : V → V` to `fun v => ((NumberField.discr F : ℤ) : Ω)⁻¹ • ∑ m, σ (c m) • ρ (a m) v`. Set `P' : Module.End Ω' V'` to `(i ((NumberField.discr F : ℤ) : Ω))⁻¹ • ∑ m, (i.comp σ) (c m) • ρ' (a m)`. Establish `hP'apply : ∀ x, P' x = (i ((NumberField.discr F : ℤ) : Ω))⁻¹ • ∑ m, (i.comp σ) (c m) • ρ' (a m) x`.

Introduce `x`. Simplify using `[P', LinearMap.sum_apply]`. Establish `hPeig : ∀ v, P v ∈ eigSp ρ σ`. Introduce `v`. Use `mem_eigSp_iff'.2 fun b => ?_` and prove the remaining obligations.

Simplify using `only [P]`. Rewrite using `[map_smul, heq Ω V ρ σ b v, smul_comm]`. Establish `hPL : ∀ v ∈ L, P v ∈ L`. Introduce `v hv`. Establish `h1 : (∑ m, σ (c m) • ρ (a m) v) ∈ L`.

Use `Submodule.sum_mem _ fun m _ => ?_` and prove the remaining obligations. Conclude with `L.smul_mem ⟨σ (c m), hσ _⟩ (hL _ _ hv)`. Conclude with `L.smul_mem ⟨_, hd⟩ h1`. Establish `hjP : ∀ v, P' (j v) = j (P v)`. Introduce `v`.

Rewrite using `[hP'apply]`. Simplify using `only [P]`. Rewrite using `[hj.1, map_inv₀, map_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[hj.1, hρ, RingHom.comp_apply]`. Establish `hP'id : ∀ x ∈ eigSp ρ' (i.comp σ), P' x = x`. Introduce `x hx`. Rewrite using `[hP'apply, sum_smul_of_eig a c (mem_eigSp_iff'.1 hx), hiσd, smul_smul, inv_mul_cancel₀ hid0, one_smul]`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce `x hx`. Take `⟨hx1, hx2⟩` from `Submodule.mem_inf.1 hx`. Establish `hx2' : x ∈ eigSp ρ' (i.comp σ)` using `hx2`. Establish `key : ∀ y ∈ Submodule.span R' (j '' (L : Set V)), P' y ∈ Submodule.span R' (j '' ((L ⊓ (eigSp ρ σ).restrictScalars R : Submodule R V) : Set V))`. Introduce `y hy`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨e, he, rfl⟩` from `hy`. Rewrite using `[hjP]`. Conclude with `Submodule.subset_span ⟨P e, Submodule.mem_inf.2 ⟨hPL e he, hPeig e⟩, rfl⟩`.

Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `Submodule.add_mem _ hy hz`. Consider the case `smul r y _ hy`.

Establish `h1 : P' (r • y) = r • P' y`. Rewrite using `[Subring.smul_def, Subring.smul_def, map_smul]`. Rewrite using `[h1]`. Conclude with `Submodule.smul_mem _ r hy`. Establish `h2` using `key x hx1`.

Rewrite `h2` using `[hP'id x hx2']`. Then use the resulting hypothesis. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨e, he, rfl⟩`. Take `⟨he1, he2⟩` from `Submodule.mem_inf.1 he`. Establish `he2' : e ∈ eigSp ρ σ` using `he2`.

Use `Submodule.mem_inf.2 ⟨Submodule.subset_span ⟨e, he1, rfl⟩, ?_⟩` and prove the remaining obligations. Use `show j e ∈ eigSp ρ' (i.comp σ)`. Use `mem_eigSp_iff'.2 fun b => ?_` and prove the remaining obligations. Rewrite using `[hρ, mem_eigSp_iff'.1 he2', hj.1, RingHom.comp_apply]`.
-/
theorem span_inf_eigSp : ∀ (F : Type) [Field F] [NumberField F] (Ω Ω' : Type) [Field Ω] [Field Ω'] [CharZero Ω] (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (ρ : 𝓞 F →+* Module.End Ω V) (ρ' : 𝓞 F →+* Module.End Ω' V') (σ : 𝓞 F →+* Ω) (R : Subring Ω) (R' : Subring Ω') (L : Submodule R V), IsExtOver i j → (∀ a e, ρ' a (j e) = j (ρ a e)) → (∀ a ∈ R, i a ∈ R') → (∀ a, ∀ e ∈ L, ρ a e ∈ L) → (∀ a, σ a ∈ R) → ((NumberField.discr F : ℤ) : Ω)⁻¹ ∈ R → Submodule.span R' (j '' (L : Set V)) ⊓ (eigSp ρ' (i.comp σ)).restrictScalars R' = Submodule.span R' (j '' ((L ⊓ (eigSp ρ σ).restrictScalars R : Submodule R V) : Set V)) := by
  intro F _ _ Ω Ω' _ _ _ i V V' _ _ _ _ j ρ ρ' σ R R' L hj hρ hiR hL hσ hd
  obtain ⟨n, a, c, hsum, heq⟩ := ScaledCasimir.exists_scaledCasimir F
  have hd0 : ((NumberField.discr F : ℤ) : Ω) ≠ 0 := Int.cast_ne_zero.2 (NumberField.discr_ne_zero F)
  have hσd : σ (∑ m, c m * a m) = ((NumberField.discr F : ℤ) : Ω) := by rw [hsum, map_intCast]
  have hiσd : (i.comp σ) (∑ m, c m * a m) = i ((NumberField.discr F : ℤ) : Ω) := by
    rw [RingHom.comp_apply, hσd]
  have hid0 : i ((NumberField.discr F : ℤ) : Ω) ≠ 0 := (map_ne_zero i).2 hd0

  let P : V → V := fun v => ((NumberField.discr F : ℤ) : Ω)⁻¹ • ∑ m, σ (c m) • ρ (a m) v

  let P' : Module.End Ω' V' := (i ((NumberField.discr F : ℤ) : Ω))⁻¹ • ∑ m, (i.comp σ) (c m) • ρ' (a m)
  have hP'apply : ∀ x, P' x = (i ((NumberField.discr F : ℤ) : Ω))⁻¹ • ∑ m, (i.comp σ) (c m) • ρ' (a m) x := by
    intro x
    simp [P', LinearMap.sum_apply]
  have hPeig : ∀ v, P v ∈ eigSp ρ σ := by
    intro v
    refine mem_eigSp_iff'.2 fun b => ?_
    simp only [P]
    rw [map_smul, heq Ω V ρ σ b v, smul_comm]
  have hPL : ∀ v ∈ L, P v ∈ L := by
    intro v hv
    have h1 : (∑ m, σ (c m) • ρ (a m) v) ∈ L := by
      refine Submodule.sum_mem _ fun m _ => ?_
      exact L.smul_mem ⟨σ (c m), hσ _⟩ (hL _ _ hv)
    exact L.smul_mem ⟨_, hd⟩ h1
  have hjP : ∀ v, P' (j v) = j (P v) := by
    intro v
    rw [hP'apply]
    simp only [P]
    rw [hj.1, map_inv₀, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hj.1, hρ, RingHom.comp_apply]
  have hP'id : ∀ x ∈ eigSp ρ' (i.comp σ), P' x = x := by
    intro x hx
    rw [hP'apply, sum_smul_of_eig a c (mem_eigSp_iff'.1 hx), hiσd, smul_smul,
      inv_mul_cancel₀ hid0, one_smul]
  apply le_antisymm
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    have hx2' : x ∈ eigSp ρ' (i.comp σ) := hx2
    have key : ∀ y ∈ Submodule.span R' (j '' (L : Set V)), P' y ∈ Submodule.span R'
        (j '' ((L ⊓ (eigSp ρ σ).restrictScalars R : Submodule R V) : Set V)) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨e, he, rfl⟩ := hy
        rw [hjP]
        exact Submodule.subset_span ⟨P e, Submodule.mem_inf.2 ⟨hPL e he, hPeig e⟩, rfl⟩
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
      | smul r y _ hy =>
        have h1 : P' (r • y) = r • P' y := by
          rw [Subring.smul_def, Subring.smul_def, map_smul]
        rw [h1]
        exact Submodule.smul_mem _ r hy
    have h2 := key x hx1
    rwa [hP'id x hx2'] at h2
  · rw [Submodule.span_le]
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨he1, he2⟩ := Submodule.mem_inf.1 he
    have he2' : e ∈ eigSp ρ σ := he2
    refine Submodule.mem_inf.2 ⟨Submodule.subset_span ⟨e, he1, rfl⟩, ?_⟩
    show j e ∈ eigSp ρ' (i.comp σ)
    refine mem_eigSp_iff'.2 fun b => ?_
    rw [hρ, mem_eigSp_iff'.1 he2', hj.1, RingHom.comp_apply]

end GlobalTheory.CompanionTheory.Ar.EigLat
