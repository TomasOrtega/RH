import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

/- English proof (translation)
Introduce `G H _ _ Γ C lam hyp`. Establish `key : ∀ (r γ₁ γ₂ : G), γ₁ ∈ Γ → γ₂ ∈ Γ → ∀ c₁ c₂ : C, γ₁ * r * c₁ = γ₂ * r * c₂ → lam c₁ = lam c₂`. Introduce `r γ₁ γ₂ h1 h2 c₁ c₂ h`. Establish `h' : γ₂⁻¹ * γ₁ * r = r * ((c₂ * c₁⁻¹ : C) : G)`. Rewrite using `[Subgroup.coe_mul, Subgroup.coe_inv]`.

Combine the equalities or inequalities in the displayed calculation. Establish `h3` using `hyp r _ (Γ.mul_mem (Γ.inv_mem h2) h1) _ h'`. Rewrite `h3` using `[map_mul, map_inv, mul_inv_eq_one]`. Conclude with `h3.symm`. Take `⟨R, hR⟩ : ∃ R : G → Set G, ∀ g x, x ∈ R g ↔ ∃ γ ∈ Γ, ∃ c : C, x = γ * g * c` from `⟨fun g => {x | ∃ γ ∈ Γ, ∃ c : C, x = γ * g * c}, fun _ _ => Iff.rfl⟩`.

Establish `hself : ∀ g, g ∈ R g` using `fun g => (hR g g).2 ⟨1, Γ.one_mem, 1, by simp⟩`. Establish `hsub : ∀ g g', g' ∈ R g → R g' ⊆ R g`. Introduce `g g' hg x hx`. Take `⟨γ, hγ, c, e⟩` from `(hR g g').1 hg`. Take `⟨γ', hγ', c', e'⟩` from `(hR g' x).1 hx`.

Conclude with `(hR g x).2 ⟨γ' * γ, Γ.mul_mem hγ' hγ, c * c', by rw [e', e, Subgroup.coe_mul]; group⟩`. Establish `hsymm : ∀ g g', g' ∈ R g → g ∈ R g'`. Introduce `g g' hg`. Take `⟨γ, hγ, c, e⟩` from `(hR g g').1 hg`. Conclude with `(hR g' g).2 ⟨γ⁻¹, Γ.inv_mem hγ, c⁻¹, by rw [e, Subgroup.coe_inv]; group⟩`.

Take `⟨rep, hrep⟩ : ∃ rep : G → G, ∀ g, rep g = Classical.epsilon (· ∈ R g)` from `⟨_, fun _ => rfl⟩`. Establish `hrepR : ∀ g g', g' ∈ R g → rep g' = rep g`. Introduce `g g' hg`. Establish `hRR : R g' = R g` using `Set.Subset.antisymm (hsub g g' hg) (hsub g' g (hsymm g g' hg))`. Rewrite using `[hrep, hrep, hRR]`.

Establish `hdec : ∀ g, ∃ c : C, ∃ γ ∈ Γ, g = γ * rep g * c`. Introduce `g`. Establish `hm : rep g ∈ R g`. Rewrite using `[hrep]`. Conclude with `Classical.epsilon_spec ⟨g, hself g⟩`.

Take `⟨γ, hγ, c, e⟩` from `(hR g _).1 hm`. Conclude with `⟨c⁻¹, γ⁻¹, Γ.inv_mem hγ, by rw [e, Subgroup.coe_inv]; group⟩`. Set `ℓ : G → H` to `fun g => lam (Classical.choose (hdec g))`. Establish `hℓ : ∀ g γ, γ ∈ Γ → ∀ c : C, g = γ * rep g * c → ℓ g = lam c`. Introduce `g γ hγ c e`.

Take `⟨γ0, h0, e0⟩` from `Classical.choose_spec (hdec g)`. Conclude with `key (rep g) γ0 γ h0 hγ _ _ (e0.symm.trans e)`. Use `⟨ℓ, ?_, ?_⟩` and prove the remaining obligations. Introduce `γ hγ g`. Take `⟨c0, γ0, h0, e0⟩` from `hdec g`.

Establish `hr : rep (γ * g) = rep g` using `hrepR g _ ((hR g _).2 ⟨γ, hγ, 1, by simp⟩)`. Rewrite using `[hℓ g γ0 h0 c0 e0]`. Apply `hℓ (γ * g) (γ * γ0) (Γ.mul_mem hγ h0) c0` to reduce the goal to its premises. Rewrite using `[hr]`. Use `conv_lhs => rw [e0]`.

Simplify using `only [mul_assoc]`. Introduce `g c`. Take `⟨c0, γ0, h0, e0⟩` from `hdec g`. Establish `hr : rep (g * c) = rep g` using `hrepR g _ ((hR g _).2 ⟨1, Γ.one_mem, c, by simp⟩)`. Rewrite using `[hℓ g γ0 h0 c0 e0, ← map_mul]`.

Apply `hℓ (g * c) γ0 h0 (c0 * c)` to reduce the goal to its premises. Rewrite using `[hr, Subgroup.coe_mul]`. Use `conv_lhs => rw [e0]`. Simplify using `only [mul_assoc]`.
-/
theorem UpperTheory.Gal.Gen.ellGrp_pf :
    UpperTheory.Gal.Gen.EllGrp := by
  classical
  intro G H _ _ Γ C lam hyp
  have key : ∀ (r γ₁ γ₂ : G), γ₁ ∈ Γ → γ₂ ∈ Γ → ∀ c₁ c₂ : C,
      γ₁ * r * c₁ = γ₂ * r * c₂ → lam c₁ = lam c₂ := by
    intro r γ₁ γ₂ h1 h2 c₁ c₂ h
    have h' : γ₂⁻¹ * γ₁ * r = r * ((c₂ * c₁⁻¹ : C) : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      calc γ₂⁻¹ * γ₁ * r = γ₂⁻¹ * (γ₁ * r * c₁) * (c₁ : G)⁻¹ := by group
        _ = γ₂⁻¹ * (γ₂ * r * c₂) * (c₁ : G)⁻¹ := by rw [h]
        _ = r * ((c₂ : G) * (c₁ : G)⁻¹) := by group
    have h3 := hyp r _ (Γ.mul_mem (Γ.inv_mem h2) h1) _ h'
    rw [map_mul, map_inv, mul_inv_eq_one] at h3
    exact h3.symm
  obtain ⟨R, hR⟩ : ∃ R : G → Set G, ∀ g x, x ∈ R g ↔ ∃ γ ∈ Γ, ∃ c : C, x = γ * g * c :=
    ⟨fun g => {x | ∃ γ ∈ Γ, ∃ c : C, x = γ * g * c}, fun _ _ => Iff.rfl⟩
  have hself : ∀ g, g ∈ R g := fun g => (hR g g).2 ⟨1, Γ.one_mem, 1, by simp⟩
  have hsub : ∀ g g', g' ∈ R g → R g' ⊆ R g := by
    intro g g' hg x hx
    obtain ⟨γ, hγ, c, e⟩ := (hR g g').1 hg
    obtain ⟨γ', hγ', c', e'⟩ := (hR g' x).1 hx
    exact (hR g x).2 ⟨γ' * γ, Γ.mul_mem hγ' hγ, c * c', by rw [e', e, Subgroup.coe_mul]; group⟩
  have hsymm : ∀ g g', g' ∈ R g → g ∈ R g' := by
    intro g g' hg
    obtain ⟨γ, hγ, c, e⟩ := (hR g g').1 hg
    exact (hR g' g).2 ⟨γ⁻¹, Γ.inv_mem hγ, c⁻¹, by rw [e, Subgroup.coe_inv]; group⟩
  obtain ⟨rep, hrep⟩ : ∃ rep : G → G, ∀ g, rep g = Classical.epsilon (· ∈ R g) :=
    ⟨_, fun _ => rfl⟩
  have hrepR : ∀ g g', g' ∈ R g → rep g' = rep g := by
    intro g g' hg
    have hRR : R g' = R g := Set.Subset.antisymm (hsub g g' hg) (hsub g' g (hsymm g g' hg))
    rw [hrep, hrep, hRR]
  have hdec : ∀ g, ∃ c : C, ∃ γ ∈ Γ, g = γ * rep g * c := by
    intro g
    have hm : rep g ∈ R g := by
      rw [hrep]
      exact Classical.epsilon_spec ⟨g, hself g⟩
    obtain ⟨γ, hγ, c, e⟩ := (hR g _).1 hm
    exact ⟨c⁻¹, γ⁻¹, Γ.inv_mem hγ, by rw [e, Subgroup.coe_inv]; group⟩
  let ℓ : G → H := fun g => lam (Classical.choose (hdec g))
  have hℓ : ∀ g γ, γ ∈ Γ → ∀ c : C, g = γ * rep g * c → ℓ g = lam c := by
    intro g γ hγ c e
    obtain ⟨γ0, h0, e0⟩ := Classical.choose_spec (hdec g)
    exact key (rep g) γ0 γ h0 hγ _ _ (e0.symm.trans e)
  refine ⟨ℓ, ?_, ?_⟩
  · intro γ hγ g
    obtain ⟨c0, γ0, h0, e0⟩ := hdec g
    have hr : rep (γ * g) = rep g := hrepR g _ ((hR g _).2 ⟨γ, hγ, 1, by simp⟩)
    rw [hℓ g γ0 h0 c0 e0]
    apply hℓ (γ * g) (γ * γ0) (Γ.mul_mem hγ h0) c0
    rw [hr]
    conv_lhs => rw [e0]
    simp only [mul_assoc]
  · intro g c
    obtain ⟨c0, γ0, h0, e0⟩ := hdec g
    have hr : rep (g * c) = rep g := hrepR g _ ((hR g _).2 ⟨1, Γ.one_mem, c, by simp⟩)
    rw [hℓ g γ0 h0 c0 e0, ← map_mul]
    apply hℓ (g * c) γ0 h0 (c0 * c)
    rw [hr, Subgroup.coe_mul]
    conv_lhs => rw [e0]
    simp only [mul_assoc]
