import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicModularFormMulArchInvariantStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

/- English proof (translation)
Introduce `hAlg hCod hPF E _ _ _ l _ ι a W C C' hCfin H _ _ hH lam hsurj hC'C hker ℓ hinf hright haut P hfd hcard f hf`. Use `letI : Fintype H := Fintype.ofFinite H`. Establish `hex : ∀ φ : H → ℂ, ∃ F : algForms W, ∀ v g, F.1 v g = φ (ℓ g) * f.1 v g` using `fun φ => GlobalTheory.T.exists_algebraicModularForm_mul_archInvariant E a W f (fun g => φ (ℓ g)) (haut φ) (fun g x hx => by simp only [hinf g x hx])`. Use `choose Ψ₀ hΨ₀ using hex`. Set `Ψ : (H → ℂ) →ₗ[ℂ] algForms W` to `{ toFun := Ψ₀ map_add' := fun φ ψ => Subtype.ext <| LinearMap.ext fun v => funext fun g => by`.

Simplify using `only [Submodule.coe_add, LinearMap.add_apply, Pi.add_apply, hΨ₀]`. Expand and normalize the polynomial expressions, which then agree. Use the proof step `map_smul' := fun c φ => Subtype.ext <| LinearMap.ext fun v => funext fun g => by`. Simplify using `only [Submodule.coe_smul, LinearMap.smul_apply, Pi.smul_apply, hΨ₀, RingHom.id_apply, smul_eq_mul]`. Use `ring }`.

Establish `hΨ : ∀ φ v g, (Ψ φ).1 v g = φ (ℓ g) * f.1 v g` using `hΨ₀`. Establish `hfix : ∀ φ, Ψ φ ∈ fixedBy W C'` using `fun φ k hk v g => by`. Establish `hkC : k ∈ C` using `hC'C hk`. Establish `h1 : lam ⟨k, hkC⟩ = 1` using `(hker ⟨k, hkC⟩).1 hk`. Establish `h2 : ℓ (g * k) = ℓ g`.

Use `hright g ⟨k, hkC⟩` as an intermediate fact. Rewrite `this` using `[h1, mul_one]`. Conclude with `this`. Rewrite using `[hΨ, hΨ, h2, hf k hkC v g]`. Take `⟨h1, -, -, h4, -⟩` from `hPF E a W C' P`.

Establish `hdim` using `hCod ℂ (H → ℂ) (algForms W) Ψ (part W C' P) (part W C' fun U => ¬ P U) (fun φ => h1 (hfix φ))`. Rewrite `hdim` using `[Module.finrank_fintype_fun_eq_card]`. Rewrite `hcard` using `[Nat.card_eq_fintype_card]`. Establish `hA : Fintype.card H ≤ 2 * Module.finrank ℂ ((part W C' P).comap Ψ)` using `by omega`. Establish `hstable : ∀ c ∈ (part W C' P).comap Ψ, ∀ u, (fun h => c (h * u)) ∈ (part W C' P).comap Ψ`.

Introduce `φ hφ u`. Take `⟨c, rfl⟩` from `hsurj u`. Establish `hnorm : ∀ c' ∈ C', (c.1 : UA E a)⁻¹ * c' * c.1 ∈ C'`. Introduce `c' hc'`. Establish `hc'C : c' ∈ C` using `hC'C hc'`.

Establish `hm : (c.1 : UA E a)⁻¹ * c' * c.1 ∈ C` using `C.mul_mem (C.mul_mem (C.inv_mem c.2) hc'C) c.2`. Use `(hker ⟨_, hm⟩).2 ?_` and prove the remaining obligations. Establish `e1 : (⟨_, hm⟩ : C) = c⁻¹ * ⟨c', hc'C⟩ * c` using `Subtype.ext rfl`. Rewrite using `[e1, map_mul, map_mul, (hker ⟨c', hc'C⟩).1 hc', mul_one, map_inv, inv_mul_cancel]`. Establish `hrep : Ψ (fun h => φ (h * lam c)) = algRep W ⟨c.1, hCfin c.2⟩ (Ψ φ)` using `Subtype.ext <| LinearMap.ext fun v => funext fun g => by`.

Establish `e2 : (algRep W ⟨c.1, hCfin c.2⟩ (Ψ φ)).1 v g = (Ψ φ).1 v (g * c.1)` using `rfl`. Rewrite using `[e2, hΨ, hΨ, hright g c, hf c.1 c.2 v g]`. Express the relevant statement in the definitionally equal form `Ψ _ ∈ part W C' P`. Rewrite using `[hrep]`. Conclude with `h4 ⟨c.1, hCfin c.2⟩ hnorm _ hφ`.

Take `⟨φ, hφ, hnorm⟩` from `hAlg l ι H hH _ hstable hA`. Conclude with `⟨Ψ φ, hφ, fun g => 1 - φ (ℓ g), fun g => hnorm (ℓ g), fun v g => by rw [hΨ]; ring⟩`.
-/
theorem UpperTheory.Gal.Gen.stepCore_pf :
    UpperTheory.Gal.Gen.AlgC → UpperTheory.Gal.Gen.Codim → UpperTheory.Gal.Gen.PartFacts → UpperTheory.Gal.Gen.StepCore := by
  intro hAlg hCod hPF E _ _ _ l _ ι a W C C' hCfin H _ _ hH lam hsurj hC'C hker ℓ hinf hright haut P hfd hcard f hf
  letI : Fintype H := Fintype.ofFinite H
  have hex : ∀ φ : H → ℂ, ∃ F : algForms W, ∀ v g, F.1 v g = φ (ℓ g) * f.1 v g := fun φ =>
    GlobalTheory.T.exists_algebraicModularForm_mul_archInvariant E a W f (fun g => φ (ℓ g)) (haut φ) (fun g x hx => by simp only [hinf g x hx])
  choose Ψ₀ hΨ₀ using hex
  let Ψ : (H → ℂ) →ₗ[ℂ] algForms W :=
    { toFun := Ψ₀
      map_add' := fun φ ψ => Subtype.ext <| LinearMap.ext fun v => funext fun g => by
        simp only [Submodule.coe_add, LinearMap.add_apply, Pi.add_apply, hΨ₀]
        ring
      map_smul' := fun c φ => Subtype.ext <| LinearMap.ext fun v => funext fun g => by
        simp only [Submodule.coe_smul, LinearMap.smul_apply, Pi.smul_apply, hΨ₀, RingHom.id_apply, smul_eq_mul]
        ring }
  have hΨ : ∀ φ v g, (Ψ φ).1 v g = φ (ℓ g) * f.1 v g := hΨ₀
  have hfix : ∀ φ, Ψ φ ∈ fixedBy W C' := fun φ k hk v g => by
    have hkC : k ∈ C := hC'C hk
    have h1 : lam ⟨k, hkC⟩ = 1 := (hker ⟨k, hkC⟩).1 hk
    have h2 : ℓ (g * k) = ℓ g := by
      have := hright g ⟨k, hkC⟩
      rw [h1, mul_one] at this
      exact this
    rw [hΨ, hΨ, h2, hf k hkC v g]
  obtain ⟨h1, -, -, h4, -⟩ := hPF E a W C' P
  have hdim := hCod ℂ (H → ℂ) (algForms W) Ψ (part W C' P) (part W C' fun U => ¬ P U) (fun φ => h1 (hfix φ))
  rw [Module.finrank_fintype_fun_eq_card] at hdim
  rw [Nat.card_eq_fintype_card] at hcard
  have hA : Fintype.card H ≤ 2 * Module.finrank ℂ ((part W C' P).comap Ψ) := by omega
  have hstable : ∀ c ∈ (part W C' P).comap Ψ, ∀ u, (fun h => c (h * u)) ∈ (part W C' P).comap Ψ := by
    intro φ hφ u
    obtain ⟨c, rfl⟩ := hsurj u
    have hnorm : ∀ c' ∈ C', (c.1 : UA E a)⁻¹ * c' * c.1 ∈ C' := by
      intro c' hc'
      have hc'C : c' ∈ C := hC'C hc'
      have hm : (c.1 : UA E a)⁻¹ * c' * c.1 ∈ C := C.mul_mem (C.mul_mem (C.inv_mem c.2) hc'C) c.2
      refine (hker ⟨_, hm⟩).2 ?_
      have e1 : (⟨_, hm⟩ : C) = c⁻¹ * ⟨c', hc'C⟩ * c := Subtype.ext rfl
      rw [e1, map_mul, map_mul, (hker ⟨c', hc'C⟩).1 hc', mul_one, map_inv, inv_mul_cancel]
    have hrep : Ψ (fun h => φ (h * lam c)) = algRep W ⟨c.1, hCfin c.2⟩ (Ψ φ) :=
      Subtype.ext <| LinearMap.ext fun v => funext fun g => by
        have e2 : (algRep W ⟨c.1, hCfin c.2⟩ (Ψ φ)).1 v g = (Ψ φ).1 v (g * c.1) := rfl
        rw [e2, hΨ, hΨ, hright g c, hf c.1 c.2 v g]
    change Ψ _ ∈ part W C' P
    rw [hrep]
    exact h4 ⟨c.1, hCfin c.2⟩ hnorm _ hφ
  obtain ⟨φ, hφ, hnorm⟩ := hAlg l ι H hH _ hstable hA
  exact ⟨Ψ φ, hφ, fun g => 1 - φ (ℓ g), fun g => hnorm (ℓ g), fun v g => by rw [hΨ]; ring⟩
