import Mathlib

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Classical

section Induced

@[instance_reducible] def productMulActionFirstFactor (G Y : Type) [CommGroup G] : MulAction G (G × Y) where
  smul g x := (g * x.1, x.2)
  one_smul x := by
    show ((1 : G) * x.1, x.2) = x
    rw [one_mul]
  mul_smul g h x := by
    show ((g * h) * x.1, x.2) = (g * (h * x.1), x.2)
    rw [mul_assoc]

variable {G : Type} [CommGroup G] [Fintype G] {Cl : Type} [Fintype Cl] [MulAction G Cl] {d : ℕ}
  {M : Type} [AddCommGroup M] [Module ℂ M]

def t2xE (Φ : M ≃ₗ[ℂ] (Cl → Fin d → ℂ)) (ρ : G →* (M →ₗ[ℂ] M)) :
    M →ₗ[ℂ] (G × (MulAction.orbitRel.Quotient G Cl × Fin d) → ℂ) where
  toFun φ x := Φ (ρ x.1 φ) (Quotient.out x.2.1) x.2.2
  map_add' φ ψ := by funext x; simp
  map_smul' a φ := by funext x; simp

/- English proof (translation)
Use `show Φ (ρ x.1 (ρ g φ)) (Quotient.out x.2.1) x.2.2 = Φ (ρ (g * x.1) φ) (Quotient.out x.2.1) x.2.2`. Rewrite using `[mul_comm g x.1, map_mul]`. Both sides reduce to the same expression.
-/
theorem coordMap_intertwines (Φ : M ≃ₗ[ℂ] (Cl → Fin d → ℂ)) (ρ : G →* (M →ₗ[ℂ] M)) (g : G) (φ : M)
    (x : G × (MulAction.orbitRel.Quotient G Cl × Fin d)) :
    t2xE Φ ρ (ρ g φ) x = t2xE Φ ρ φ (g * x.1, x.2) := by
  show Φ (ρ x.1 (ρ g φ)) (Quotient.out x.2.1) x.2.2 = Φ (ρ (g * x.1) φ) (Quotient.out x.2.1) x.2.2
  rw [mul_comm g x.1, map_mul]
  rfl

/- English proof (translation)
Establish `h` using `Quotient.mk_out (s := MulAction.orbitRel G Cl) c`. Take `⟨g, hg⟩` from `MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)`. Conclude with `⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩`.
-/
theorem exists_smul_out_eq (c : Cl) : ∃ g : G, g • Quotient.out (Quotient.mk (MulAction.orbitRel G Cl) c) = c := by
  have h := Quotient.mk_out (s := MulAction.orbitRel G Cl) c
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
  exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `φ hE`. Establish `h0 : ∀ (g : G) (q : MulAction.orbitRel.Quotient G Cl), Φ (ρ g φ) (Quotient.out q) = 0` using `fun g q => funext fun b => congrFun hE (g, q, b)`. Establish `h1 : Φ φ = 0`. Use function extensionality and compare the values at `c`.

Take `⟨g, hg⟩` from `exists_smul_out_eq (G := G) c`. Use `hmono g _ φ (h0 g (Quotient.mk (MulAction.orbitRel G Cl) c))` as an intermediate fact. Rewrite `this` using `[hg]`. Conclude with `this`. Conclude with `Φ.map_eq_zero_iff.1 h1`.
-/
theorem t2xE_injective_of_monomial (Φ : M ≃ₗ[ℂ] (Cl → Fin d → ℂ)) (ρ : G →* (M →ₗ[ℂ] M))
    (hmono : ∀ (g : G) (c : Cl) (φ : M), Φ (ρ g φ) c = 0 → Φ φ (g • c) = 0) :
    Function.Injective (t2xE Φ ρ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro φ hE
  have h0 : ∀ (g : G) (q : MulAction.orbitRel.Quotient G Cl), Φ (ρ g φ) (Quotient.out q) = 0 :=
    fun g q => funext fun b => congrFun hE (g, q, b)
  have h1 : Φ φ = 0 := by
    funext c
    obtain ⟨g, hg⟩ := exists_smul_out_eq (G := G) c
    have := hmono g _ φ (h0 g (Quotient.mk (MulAction.orbitRel G Cl) c))
    rw [hg] at this
    exact this
  exact Φ.map_eq_zero_iff.1 h1

/- English proof (translation)
Rewrite using `[← Fintype.card_prod]`. Use `Fintype.card_of_bijective (f := fun x : G × MulAction.orbitRel.Quotient G Cl => x.1 • Quotient.out x.2) ⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨g, q⟩ ⟨g', q'⟩ h`. Simplify using `only at h`. Establish `hq : ∀ (g0 : G) (q0 : MulAction.orbitRel.Quotient G Cl), (Quotient.mk (MulAction.orbitRel G Cl) (g0 • Quotient.out q0)) = q0`.

Introduce `g0 q0`. Use `conv_rhs => rw [← Quotient.out_eq q0]`. Conclude with `Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit _ g0))`. Establish `hqq : q = q'` using `by rw [← hq g q, ← hq g' q', h]`. Substitute `hqq` using the available equality.

Establish `h2 : (g'⁻¹ * g) • Quotient.out q = Quotient.out q` using `by rw [mul_smul, h, inv_smul_smul]`. Establish `h3` using `hfree _ _ h2`. Rewrite `h3` using `[inv_mul_eq_one]`. Rewrite using `[h3]`. Introduce `c`.

Take `⟨g, hg⟩` from `exists_smul_out_eq (G := G) c`. Conclude with `⟨(g, _), hg⟩`.
-/
theorem card_mul_card_orbits (hfree : ∀ (g : G) (c : Cl), g • c = c → g = 1) :
    Fintype.card G * Fintype.card (MulAction.orbitRel.Quotient G Cl) = Fintype.card Cl := by
  rw [← Fintype.card_prod]
  refine Fintype.card_of_bijective (f := fun x : G × MulAction.orbitRel.Quotient G Cl => x.1 • Quotient.out x.2) ⟨?_, ?_⟩
  · rintro ⟨g, q⟩ ⟨g', q'⟩ h
    simp only at h
    have hq : ∀ (g0 : G) (q0 : MulAction.orbitRel.Quotient G Cl),
        (Quotient.mk (MulAction.orbitRel G Cl) (g0 • Quotient.out q0)) = q0 := by
      intro g0 q0
      conv_rhs => rw [← Quotient.out_eq q0]
      exact Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit _ g0))
    have hqq : q = q' := by rw [← hq g q, ← hq g' q', h]
    subst hqq
    have h2 : (g'⁻¹ * g) • Quotient.out q = Quotient.out q := by rw [mul_smul, h, inv_smul_smul]
    have h3 := hfree _ _ h2
    rw [inv_mul_eq_one] at h3
    rw [h3]
  · intro c
    obtain ⟨g, hg⟩ := exists_smul_out_eq (G := G) c
    exact ⟨(g, _), hg⟩

/- English proof (translation)
Establish `: FiniteDimensional ℂ M` using `LinearEquiv.finiteDimensional Φ.symm`. Establish `hinj` using `t2xE_injective_of_monomial Φ ρ hmono`. Use `⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj⟩` and prove the remaining obligations. Rewrite using `[Φ.finrank_eq, Module.finrank_fintype_fun_eq_card, Module.finrank_pi_fintype]`. Simplify using `only [Module.finrank_fin_fun, Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_prod, Fintype.card_fin]`.

Rewrite using `[← card_mul_card_orbits hfree]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coordMap_bijective (Φ : M ≃ₗ[ℂ] (Cl → Fin d → ℂ)) (ρ : G →* (M →ₗ[ℂ] M))
    (hmono : ∀ (g : G) (c : Cl) (φ : M), Φ (ρ g φ) c = 0 → Φ φ (g • c) = 0)
    (hfree : ∀ (g : G) (c : Cl), g • c = c → g = 1) :
    Function.Bijective (t2xE Φ ρ) := by
  have : FiniteDimensional ℂ M := LinearEquiv.finiteDimensional Φ.symm
  have hinj := t2xE_injective_of_monomial Φ ρ hmono
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj⟩
  rw [Φ.finrank_eq, Module.finrank_fintype_fun_eq_card, Module.finrank_pi_fintype]
  simp only [Module.finrank_fin_fun, Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_prod,
    Fintype.card_fin]
  rw [← card_mul_card_orbits hfree]
  ring

def orbitDecompositionLinearEquiv (Φ : M ≃ₗ[ℂ] (Cl → Fin d → ℂ)) (ρ : G →* (M →ₗ[ℂ] M))
    (hmono : ∀ (g : G) (c : Cl) (φ : M), Φ (ρ g φ) c = 0 → Φ φ (g • c) = 0)
    (hfree : ∀ (g : G) (c : Cl), g • c = c → g = 1) :
    M ≃ₗ[ℂ] (G × (MulAction.orbitRel.Quotient G Cl × Fin d) → ℂ) :=
  LinearEquiv.ofBijective (t2xE Φ ρ) (coordMap_bijective Φ ρ hmono hfree)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem t2xEquiv_apply (Φ : M ≃ₗ[ℂ] (Cl → Fin d → ℂ)) (ρ : G →* (M →ₗ[ℂ] M))
    (hmono : ∀ (g : G) (c : Cl) (φ : M), Φ (ρ g φ) c = 0 → Φ φ (g • c) = 0)
    (hfree : ∀ (g : G) (c : Cl), g • c = c → g = 1) (φ : M) :
    orbitDecompositionLinearEquiv Φ ρ hmono hfree φ = t2xE Φ ρ φ := rfl

end Induced

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
