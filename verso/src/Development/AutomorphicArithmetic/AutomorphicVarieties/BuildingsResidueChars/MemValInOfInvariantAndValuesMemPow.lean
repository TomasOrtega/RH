import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SpStab
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IwahoriProUnipotentFiniteIndex
open IsLocalRing Matrix UpperTheory.V.Hi

/- English proof (translation)
Introduce `Γ Ga Gp _ _ _ X A _ _ m τ θ U k c N x hx f hf hy h0`. Establish `hv : ∀ F : X.Fn A m, F ∈ X.valIn A m k ↔ ∀ g i, F g i ∈ maximalIdeal A ^ k` using `fun F => by`. Simplify using `[Frame.valIn, Submodule.mem_pi]`. Establish `hrp : ∀ (b : Gp) (g : Ga × Gp), X.rp A m b f g = f (g * (1, b))` using `fun _ _ => rfl`. Take `⟨⟨h1, h2, h3, -⟩, h4⟩` from `hf`.

Rewrite using `[hv]`. Introduce `g`. Take `⟨γ, i, u, hu, b, hb, rfl⟩` from `hx g`. Take `⟨n, hn, t, ht, y, hy', rfl⟩` from `(iwMem Gp X.I c b).1.1 hb`. Establish `a1 : ∀ j, f (x i * ((u : Ga), 1)) j ∈ maximalIdeal A ^ k`.

Introduce `j`. Establish `e` using `congrFun (h4 u⁻¹ (inv_mem hu)) (x i * ((u : Ga), 1))`. Rewrite `e` using `[Frame.ra_apply]`. Establish `e2 : x i * ((u : Ga), (1 : Gp)) * (((u⁻¹ : X.Ub) : Ga), (1 : Gp)) = x i`. Apply the tactic sequence `ext <;> simp`.

Rewrite using `[← e, e2]`. Simplify using `only [mulVec, dotProduct]`. Conclude with `Submodule.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (h0 _ l)`. Establish `a2 : ∀ j, f (x i * ((u : Ga), 1) * (1, n)) j ∈ maximalIdeal A ^ k`. Introduce `j`.

Rewrite using `[← hrp, h2 n hn]`. Conclude with `a1 j`. Establish `a3 : ∀ j, f (x i * ((u : Ga), 1) * (1, n) * (1, t)) j ∈ maximalIdeal A ^ k`. Introduce `j`. Rewrite using `[← hrp, h3 ⟨t, ht⟩]`.

Conclude with `Ideal.mul_mem_left _ _ (a2 j)`. Introduce `j`. Establish `a4` using `add_mem ((hv _).1 (hy y hy') (x i * ((u : Ga), 1) * (1, n) * (1, t)) j) (a3 j)`. Rewrite `a4` using `[Pi.sub_apply, Pi.sub_apply, sub_add_cancel, hrp]`. Rewrite using `[mul_assoc, h1]`.

Use `a4 using 2` and compare the differences between its conclusion and the goal. Apply the tactic sequence `ext <;> simp [mul_assoc]`.
-/
theorem UpperTheory.mem_valIn_of_invariant_and_values_mem_pow :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (A : Type) [CommRing A] [IsCNL A] (m : ℕ) (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ) (U : Subgroup X.Ub) (k c N : ℕ) (x : Fin N → Ga × Gp), (∀ g, ∃ γ i, ∃ u ∈ U, ∃ b ∈ X.I.Iw c, g = X.glob γ * x i * ((u : Ga), b)) → ∀ f ∈ X.Sp τ θ U, (∀ y ∈ X.I.Nm c, X.rp A m y f - f ∈ X.valIn A m k) → (∀ i j, f (x i) j ∈ maximalIdeal A ^ k) → f ∈ X.valIn A m k := by
  intro Γ Ga Gp _ _ _ X A _ _ m τ θ U k c N x hx f hf hy h0
  have hv : ∀ F : X.Fn A m, F ∈ X.valIn A m k ↔ ∀ g i, F g i ∈ maximalIdeal A ^ k := fun F => by
    simp [Frame.valIn, Submodule.mem_pi]
  have hrp : ∀ (b : Gp) (g : Ga × Gp), X.rp A m b f g = f (g * (1, b)) := fun _ _ => rfl
  obtain ⟨⟨h1, h2, h3, -⟩, h4⟩ := hf
  rw [hv]
  intro g
  obtain ⟨γ, i, u, hu, b, hb, rfl⟩ := hx g
  obtain ⟨n, hn, t, ht, y, hy', rfl⟩ := (iwMem Gp X.I c b).1.1 hb
  have a1 : ∀ j, f (x i * ((u : Ga), 1)) j ∈ maximalIdeal A ^ k := by
    intro j
    have e := congrFun (h4 u⁻¹ (inv_mem hu)) (x i * ((u : Ga), 1))
    rw [Frame.ra_apply] at e
    have e2 : x i * ((u : Ga), (1 : Gp)) * (((u⁻¹ : X.Ub) : Ga), (1 : Gp)) = x i := by
      ext <;> simp
    rw [← e, e2]
    simp only [mulVec, dotProduct]
    exact Submodule.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (h0 _ l)
  have a2 : ∀ j, f (x i * ((u : Ga), 1) * (1, n)) j ∈ maximalIdeal A ^ k := by
    intro j
    rw [← hrp, h2 n hn]
    exact a1 j
  have a3 : ∀ j, f (x i * ((u : Ga), 1) * (1, n) * (1, t)) j ∈ maximalIdeal A ^ k := by
    intro j
    rw [← hrp, h3 ⟨t, ht⟩]
    exact Ideal.mul_mem_left _ _ (a2 j)
  intro j
  have a4 := add_mem ((hv _).1 (hy y hy') (x i * ((u : Ga), 1) * (1, n) * (1, t)) j) (a3 j)
  rw [Pi.sub_apply, Pi.sub_apply, sub_add_cancel, hrp] at a4
  rw [mul_assoc, h1]
  convert a4 using 2
  ext <;> simp [mul_assoc]
