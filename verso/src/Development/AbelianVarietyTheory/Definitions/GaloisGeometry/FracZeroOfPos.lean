import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGaloisCover

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {d : ℕ}

def pw (f : Fin d → R) : Submonoid R := Submonoid.powers (∏ j, f j)

def omitted (f : Fin d → R) (M : Type) [AddCommGroup M] [Module R M] : Submodule R (LocalizedModule (pw f) M) :=
  Submodule.span R {z | ∃ (j : Fin d) (k : ℕ) (m : M), z = LocalizedModule.mk (f j ^ k • m) ⟨(∏ l, f l) ^ k, by exact ⟨k, rfl⟩⟩}

abbrev LC (f : Fin d → R) (M : Type) [AddCommGroup M] [Module R M] : Type :=
  LocalizedModule (pw f) M ⧸ omitted f M

def frac (f : Fin d → R) {M : Type} [AddCommGroup M] [Module R M] (m : M) (k : ℕ) : LC f M :=
  Submodule.Quotient.mk (LocalizedModule.mk m ⟨(∏ l, f l) ^ k, by exact ⟨k, rfl⟩⟩)

/- English proof (translation)
Extract witnesses or component facts from the available result. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem frac_surjective (f : Fin d → R) (x : LC f M) : ∃ (m : M) (k : ℕ), x = frac f m k := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  induction y using LocalizedModule.induction_on with
  | h m u =>
    obtain ⟨k, hk⟩ := u.2
    refine ⟨m, k, ?_⟩
    unfold frac
    congr 2
    exact Subtype.ext hk.symm

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem frac_prod_smul (f : Fin d → R) (m : M) (k : ℕ) : frac f ((∏ l, f l) • m) (k + 1) = frac f m k := by
  unfold frac
  congr 1
  rw [LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, smul_smul, pow_succ]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Supply the required witnesses or components.
-/
theorem frac_zero_of_pos (f : Fin d → R) (hd : 0 < d) (m : M) : frac f m 0 = 0 := by
  unfold frac
  rw [Submodule.Quotient.mk_eq_zero]
  apply Submodule.subset_span
  exact ⟨⟨0, hd⟩, 0, m, by simp⟩

def IsRes {B : Type} [CommRing B] [Algebra ℂ B] (s : Fin d → B) (e : B →ₐ[ℂ] MvPowerSeries (Fin d) ℂ)
    (ρ : LC s (Om ℂ B d) →ₗ[ℂ] ℂ) : Prop :=
  (∀ j, e (s j) = MvPowerSeries.X j) ∧
  (∀ ω : Om ℂ B d, ∃ h : B, ω = h • exteriorPower.ιMulti B d fun j => D ℂ B (s j)) ∧
  ∀ (k : ℕ) (h : B), ρ (frac s (h • exteriorPower.ιMulti B d fun j => D ℂ B (s j)) (k + 1)) =
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm fun _ => k) (e h)

namespace IsRes

variable {B : Type} [CommRing B] [Algebra ℂ B] {s : Fin d → B} {e : B →ₐ[ℂ] MvPowerSeries (Fin d) ℂ}
  {ρ : LC s (Om ℂ B d) →ₗ[ℂ] ℂ}

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem top_form (hρ : IsRes s e ρ) (ω : Om ℂ B d) :
    ∃ h : B, ω = h • exteriorPower.ιMulti B d fun j => D ℂ B (s j) := hρ.2.1 ω

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem apply_frac (hρ : IsRes s e ρ) (k : ℕ) (h : B) :
    ρ (frac s (h • exteriorPower.ιMulti B d fun j => D ℂ B (s j)) (k + 1)) =
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm fun _ => k) (e h) := hρ.2.2 k h

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.
-/
theorem unique {ρ' : LC s (Om ℂ B d) →ₗ[ℂ] ℂ} (hρ : IsRes s e ρ) (hρ' : IsRes s e ρ') : ρ = ρ' := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨ω, k, rfl⟩ := frac_surjective s x
  rw [← frac_prod_smul s ω k]
  obtain ⟨h, hh⟩ := hρ.top_form ((∏ l, s l) • ω)
  rw [hh, hρ.apply_frac, hρ'.apply_frac]

end IsRes

end GlobalTheory.W1

namespace GlobalTheory.W1.Ex

def rho0 (s : Fin 0 → ℂ) : LC s (Om ℂ ℂ 0) →ₗ[ℂ] ℂ :=
  (Submodule.liftQ (omitted s (Om ℂ ℂ 0))
    ((exteriorPower.zeroEquiv ℂ Ω[ℂ⁄ℂ]).toLinearMap ∘ₗ
      LocalizedModule.lift (pw s) LinearMap.id (fun u => by
        obtain ⟨n, hn⟩ := u.2
        have : (u : ℂ) = 1 := by simpa using hn.symm
        rw [this, map_one]; exact isUnit_one))
    (by
      have : omitted s (Om ℂ ℂ 0) = ⊥ := by
        unfold omitted
        rw [Submodule.span_eq_bot]
        rintro z ⟨j, _, _, _⟩
        exact j.elim0
      rw [this]; exact bot_le))

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
example (s : Fin 0 → ℂ) : IsRes s (Algebra.ofId ℂ (MvPowerSeries (Fin 0) ℂ)) (rho0 s) := by
  refine ⟨fun j => j.elim0, fun ω => ⟨exteriorPower.zeroEquiv ℂ Ω[ℂ⁄ℂ] ω, ?_⟩, fun k h => ?_⟩
  · apply (exteriorPower.zeroEquiv ℂ Ω[ℂ⁄ℂ]).injective
    rw [LinearEquiv.map_smul, exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one]
  · have hn : (Finsupp.equivFunOnFinite.symm fun _ : Fin 0 => k) = 0 := Subsingleton.elim _ _
    rw [hn, Algebra.ofId_apply, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      MvPowerSeries.coeff_zero_C]
    simp [rho0, frac, LocalizedModule.lift_mk, exteriorPower.zeroEquiv_ιMulti]

/- English proof (translation)
A detailed English derivation is pending.
-/
example : frac (fun _ : Fin 1 => (Polynomial.X : Polynomial ℂ)) (1 : Polynomial ℂ) 0 = 0 :=
  frac_zero_of_pos _ Nat.one_pos _

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
example : frac (fun _ : Fin 1 => (Polynomial.X : Polynomial ℂ)) (Polynomial.X : Polynomial ℂ) 2 =
    frac (fun _ : Fin 1 => (Polynomial.X : Polynomial ℂ)) (1 : Polynomial ℂ) 1 := by
  have := frac_prod_smul (fun _ : Fin 1 => (Polynomial.X : Polynomial ℂ)) (1 : Polynomial ℂ) 1
  simpa using this

end GlobalTheory.W1.Ex
