import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteRepSetOfOrtho

open Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace OrbSum

variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]

/- English proof (translation)
Set `rep : X → X` to `fun x => (Quotient.mk (MulAction.orbitRel G X) x).out`. Establish `hrep : ∀ x, ∃ g : G, g • x = rep x` using `fun x => by`. Establish `h1 : Quotient.mk (MulAction.orbitRel G X) (rep x) = Quotient.mk _ x` using `Quotient.out_eq _`. Establish `h2 : rep x ∈ MulAction.orbit G x` using `Quotient.exact h1`. Conclude with `MulAction.mem_orbit_iff.1 h2`.

Establish `hrepA : ∀ x ∈ A, rep x ∈ A` using `fun x hx => by`. Take `⟨g, hg⟩` from `hrep x`. Rewrite using `[← hg]`. Conclude with `hA g x hx`. Establish `hrep_eq : ∀ x y : X, ∀ g : G, g • y = x → rep y = rep x` using `fun x y g hg => by show (Quotient.mk (MulAction.orbitRel G X) y).out = (Quotient.mk (MulAction.orbitRel G X) x).out`.

Use `congr 1`. Apply `Quotient.sound` to reduce the goal to its premises. Use `show y ∈ MulAction.orbit G x`. Rewrite using `[MulAction.mem_orbit_iff]`. Conclude with `⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩`.

Use `⟨hC.toFinset.image rep, ?_, ?_⟩` and prove the remaining obligations. Introduce `t ht`. Take `⟨c, hc, rfl⟩` from `Finset.mem_image.1 ht`. Conclude with `hrepA c (hCA c (hC.mem_toFinset.1 hc))`. Introduce `x hx`.

Take `⟨c, hc, g, hg⟩` from `hcov x hx`. Take `⟨g', hg'⟩` from `hrep c`. Use `⟨rep c, ⟨Finset.mem_image.2 ⟨c, hC.mem_toFinset.2 hc, rfl⟩, ⟨g * g'⁻¹, ?_⟩⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hg', mul_smul, inv_smul_smul, hg]`. Introduce and unpack `t ⟨ht, h, hh⟩`.

Take `⟨c', hc', rfl⟩` from `Finset.mem_image.1 ht`. Take `⟨g'', hg''⟩` from `hrep c'`. Establish `e1 : rep c' = rep x` using `(hrep_eq (rep c') c' g'' hg'').trans (hrep_eq x (rep c') h hh)`. Establish `e2 : rep c = rep x` using `hrep_eq x c g hg`. Rewrite using `[e1, e2]`.
-/
theorem exists_reps_of_cover (A : Set X) (hA : ∀ g : G, ∀ x ∈ A, g • x ∈ A) (C : Set X)
    (hC : C.Finite) (hCA : ∀ c ∈ C, c ∈ A) (hcov : ∀ x ∈ A, ∃ c ∈ C, ∃ g : G, g • c = x) :
    ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ ∀ x ∈ A, ∃! t, t ∈ T ∧ ∃ g : G, g • t = x := by
  classical
  let rep : X → X := fun x => (Quotient.mk (MulAction.orbitRel G X) x).out
  have hrep : ∀ x, ∃ g : G, g • x = rep x := fun x => by
    have h1 : Quotient.mk (MulAction.orbitRel G X) (rep x) = Quotient.mk _ x := Quotient.out_eq _
    have h2 : rep x ∈ MulAction.orbit G x := Quotient.exact h1
    exact MulAction.mem_orbit_iff.1 h2
  have hrepA : ∀ x ∈ A, rep x ∈ A := fun x hx => by
    obtain ⟨g, hg⟩ := hrep x
    rw [← hg]
    exact hA g x hx
  have hrep_eq : ∀ x y : X, ∀ g : G, g • y = x → rep y = rep x := fun x y g hg => by
    show (Quotient.mk (MulAction.orbitRel G X) y).out = (Quotient.mk (MulAction.orbitRel G X) x).out
    congr 1
    apply Quotient.sound
    show y ∈ MulAction.orbit G x
    rw [MulAction.mem_orbit_iff]
    exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩
  refine ⟨hC.toFinset.image rep, ?_, ?_⟩
  · intro t ht
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 ht
    exact hrepA c (hCA c (hC.mem_toFinset.1 hc))
  · intro x hx
    obtain ⟨c, hc, g, hg⟩ := hcov x hx
    obtain ⟨g', hg'⟩ := hrep c
    refine ⟨rep c, ⟨Finset.mem_image.2 ⟨c, hC.mem_toFinset.2 hc, rfl⟩, ⟨g * g'⁻¹, ?_⟩⟩, ?_⟩
    · rw [← hg', mul_smul, inv_smul_smul, hg]
    · rintro t ⟨ht, h, hh⟩
      obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 ht
      obtain ⟨g'', hg''⟩ := hrep c'
      have e1 : rep c' = rep x := (hrep_eq (rep c') c' g'' hg'').trans (hrep_eq x (rep c') h hh)
      have e2 : rep c = rep x := hrep_eq x c g hg
      rw [e1, e2]

/- English proof (translation)
Rewrite using `[MulAction.stabilizer_smul_eq_stabilizer_map_conj]`. Conclude with `Subgroup.card_map_of_injective (MulAut.conj g).injective`.
-/
theorem card_stab_smul (g : G) (x : X) :
    Nat.card (MulAction.stabilizer G (g • x)) = Nat.card (MulAction.stabilizer G x) := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

/- English proof (translation)
The claim follows from `Nat.card_congr { toFun := fun h => ⟨h.1.1, h.2⟩ invFun := fun g => ⟨⟨g.1, by show g.1 • π x = π x rw [← hπ] exact congrArg π g.2⟩, g.2⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl }`.
-/
theorem card_stab_sub (π : X → Y) (hπ : ∀ (g : G) x, π (g • x) = g • π x) (x : X) :
    Nat.card (MulAction.stabilizer (MulAction.stabilizer G (π x)) x) =
      Nat.card (MulAction.stabilizer G x) := Nat.card_congr
  { toFun := fun h => ⟨h.1.1, h.2⟩
    invFun := fun g => ⟨⟨g.1, by
      show g.1 • π x = π x
      rw [← hπ]
      exact congrArg π g.2⟩, g.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/- English proof (translation)
Establish `key : ∀ t : X, ∃ (u : Y) (g : G), t ∈ A → (u ∈ sY ∧ g • u = π t)`. Introduce `t`. Distinguish the cases in `ht : t ∈ A`. Take `⟨u, ⟨hu, g, hg⟩, -⟩` from `hY (π t) (hAB t ht)`. Conclude with `⟨u, g, fun _ => ⟨hu, hg⟩⟩`.

Conclude with `⟨π t, 1, fun h => absurd h ht⟩`. Use `choose U γ hU using key`. Establish `hπ' : ∀ t ∈ A, π ((γ t)⁻¹ • t) = U t`. Introduce `t ht`. Rewrite using `[hπ, ← (hU t ht).2, inv_smul_smul]`.

Rewrite using `[← Finset.sum_fiberwise_of_maps_to (s := sX) (t := sY) (g := U) (fun t ht => (hU t (hsX t ht)).1)]`. Use `Finset.sum_congr rfl fun u hu => ?_` and prove the remaining obligations. Use `set T : Finset X := (sX.filter (fun t => U t = u)).image (fun t => (γ t)⁻¹ • t) with hTdef`. Establish `hinj : Set.InjOn (fun t => (γ t)⁻¹ • t) (sX.filter (fun t => U t = u) : Set X)`. Introduce `t₁ h₁ t₂ h₂ e`.

Establish `h₁'` using `(Finset.mem_filter.mp h₁).1`. Establish `h₂'` using `(Finset.mem_filter.mp h₂).1`. Conclude with `(hX _ (hA (γ t₁)⁻¹ t₁ (hsX t₁ h₁'))).unique ⟨h₁', _, rfl⟩ ⟨h₂', _, e.symm⟩`. Establish `hstab : ∀ g : MulAction.stabilizer G u, ∀ x ∈ {x : X | x ∈ A ∧ π x = u}, g • x ∈ {x : X | x ∈ A ∧ π x = u}`. Introduce and unpack `⟨g, hg⟩ x ⟨hx1, hx2⟩`.

Use `⟨hA g x hx1, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `π (g • x) = u`. Rewrite using `[hπ, hx2]`. Conclude with `MulAction.mem_stabilizer_iff.mp hg`. Establish `hTA : ∀ t ∈ T, t ∈ {x : X | x ∈ A ∧ π x = u}`.

Introduce `t ht`. Take `⟨t₀, h₀, rfl⟩` from `Finset.mem_image.mp ht`. Take `⟨h₁, rfl⟩` from `Finset.mem_filter.mp h₀`. Conclude with `⟨hA _ _ (hsX t₀ h₁), hπ' t₀ (hsX t₀ h₁)⟩`. Establish `hT : ∀ x ∈ {x : X | x ∈ A ∧ π x = u}, ∃! t, t ∈ T ∧ ∃ g : MulAction.stabilizer G u, g • t = x`.

Introduce and unpack `x ⟨hx1, hx2⟩`. Take `⟨t, ⟨ht, g, hg⟩, huniq⟩` from `hX x hx1`. Establish `htA` using `hsX t ht`. Establish `e1 : (g * γ t) • U t = u`. Rewrite using `[mul_smul, (hU t htA).2, ← hπ, hg, hx2]`.

Establish `hUt : U t = u` using `(hY u (hsY u hu)).unique ⟨(hU t htA).1, _, e1⟩ ⟨hu, 1, one_smul _ _⟩`. Use `⟨(γ t)⁻¹ • t, ⟨Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, hUt⟩, rfl⟩, ⟨g * γ t, MulAction.mem_stabilizer_iff.mpr (by rw [← hUt] at e1 ⊢; exact e1)⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(g * γ t) • (γ t)⁻¹ • t = x`. Rewrite using `[mul_smul, smul_inv_smul, hg]`. Introduce and unpack `t' ⟨ht', ⟨g', hg'm⟩, hg'⟩`.

Take `⟨t₀, h₀, rfl⟩` from `Finset.mem_image.mp ht'`. Establish `h₀'` using `(Finset.mem_filter.mp h₀).1`. Establish `: t₀ = t` using `huniq t₀ ⟨h₀', g' * (γ t₀)⁻¹, by rw [mul_smul]; exact hg'⟩`. Rewrite using `[this]`. Establish `hfinG : Finite (MulAction.stabilizer G u)` using `(hfinY u (hsY u hu)).to_subtype`.

Establish `hfinA : Finite ↥{x : X | x ∈ A ∧ π x = u}`. Apply `Set.Finite.to_subtype` to reduce the goal to its premises. Use `((T : Set X).toFinite.biUnion (fun t _ => Set.finite_range (fun g : MulAction.stabilizer G u => g • t))).subset ?_` and prove the remaining obligations. Introduce `x hx`. Take `⟨t, ⟨ht, g, hg⟩, -⟩` from `hT x hx`.

Conclude with `Set.mem_biUnion (Finset.mem_coe.mpr ht) ⟨g, hg⟩`. Establish `main` using `sum_inv_card_stab (G := MulAction.stabilizer G u) {x : X | x ∈ A ∧ π x = u} hstab T hTA hT`. Establish `e0 : (Nat.card {x // x ∈ A ∧ π x = u} : ℝ) = (Nat.card ↥{x : X | x ∈ A ∧ π x = u} : ℝ)` using `rfl`. Rewrite using `[e0, main, hTdef, Finset.sum_image hinj]`. Use `Finset.sum_congr rfl fun t ht => ?_` and prove the remaining obligations.

Take `⟨ht1, rfl⟩` from `Finset.mem_filter.mp ht`. Use `card_stab_sub π hπ ((γ t)⁻¹ • t)` as an intermediate fact. Rewrite `this` using `[hπ' t (hsX t ht1)]`. Rewrite using `[this, card_stab_smul]`.
-/
theorem sum_orbits_on (π : X → Y) (hπ : ∀ (g : G) x, π (g • x) = g • π x) (A : Set X) (B : Set Y)
    (hA : ∀ g : G, ∀ x ∈ A, g • x ∈ A) (hAB : ∀ x ∈ A, π x ∈ B)
    (sX : Finset X) (sY : Finset Y) (hsX : ∀ t ∈ sX, t ∈ A) (hsY : ∀ u ∈ sY, u ∈ B)
    (hX : ∀ x ∈ A, ∃! t : X, t ∈ sX ∧ ∃ g : G, g • t = x)
    (hY : ∀ y ∈ B, ∃! t : Y, t ∈ sY ∧ ∃ g : G, g • t = y)
    (hfinY : ∀ y ∈ B, (MulAction.stabilizer G y : Set G).Finite) :
    ∑ t ∈ sX, ((Nat.card (MulAction.stabilizer G t) : ℕ) : ℝ)⁻¹ =
      ∑ u ∈ sY, (Nat.card {x // x ∈ A ∧ π x = u} : ℝ) /
        (Nat.card (MulAction.stabilizer G u) : ℝ) := by
  classical
  have key : ∀ t : X, ∃ (u : Y) (g : G), t ∈ A → (u ∈ sY ∧ g • u = π t) := by
    intro t
    by_cases ht : t ∈ A
    · obtain ⟨u, ⟨hu, g, hg⟩, -⟩ := hY (π t) (hAB t ht)
      exact ⟨u, g, fun _ => ⟨hu, hg⟩⟩
    · exact ⟨π t, 1, fun h => absurd h ht⟩
  choose U γ hU using key
  have hπ' : ∀ t ∈ A, π ((γ t)⁻¹ • t) = U t := by
    intro t ht
    rw [hπ, ← (hU t ht).2, inv_smul_smul]
  rw [← Finset.sum_fiberwise_of_maps_to (s := sX) (t := sY) (g := U)
    (fun t ht => (hU t (hsX t ht)).1)]
  refine Finset.sum_congr rfl fun u hu => ?_
  set T : Finset X := (sX.filter (fun t => U t = u)).image (fun t => (γ t)⁻¹ • t) with hTdef
  have hinj : Set.InjOn (fun t => (γ t)⁻¹ • t) (sX.filter (fun t => U t = u) : Set X) := by
    intro t₁ h₁ t₂ h₂ e
    have h₁' := (Finset.mem_filter.mp h₁).1
    have h₂' := (Finset.mem_filter.mp h₂).1
    exact (hX _ (hA (γ t₁)⁻¹ t₁ (hsX t₁ h₁'))).unique ⟨h₁', _, rfl⟩ ⟨h₂', _, e.symm⟩
  have hstab : ∀ g : MulAction.stabilizer G u, ∀ x ∈ {x : X | x ∈ A ∧ π x = u},
      g • x ∈ {x : X | x ∈ A ∧ π x = u} := by
    rintro ⟨g, hg⟩ x ⟨hx1, hx2⟩
    refine ⟨hA g x hx1, ?_⟩
    change π (g • x) = u
    rw [hπ, hx2]
    exact MulAction.mem_stabilizer_iff.mp hg
  have hTA : ∀ t ∈ T, t ∈ {x : X | x ∈ A ∧ π x = u} := by
    intro t ht
    obtain ⟨t₀, h₀, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨h₁, rfl⟩ := Finset.mem_filter.mp h₀
    exact ⟨hA _ _ (hsX t₀ h₁), hπ' t₀ (hsX t₀ h₁)⟩
  have hT : ∀ x ∈ {x : X | x ∈ A ∧ π x = u},
      ∃! t, t ∈ T ∧ ∃ g : MulAction.stabilizer G u, g • t = x := by
    rintro x ⟨hx1, hx2⟩
    obtain ⟨t, ⟨ht, g, hg⟩, huniq⟩ := hX x hx1
    have htA := hsX t ht
    have e1 : (g * γ t) • U t = u := by
      rw [mul_smul, (hU t htA).2, ← hπ, hg, hx2]
    have hUt : U t = u :=
      (hY u (hsY u hu)).unique ⟨(hU t htA).1, _, e1⟩ ⟨hu, 1, one_smul _ _⟩
    refine ⟨(γ t)⁻¹ • t, ⟨Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, hUt⟩, rfl⟩,
      ⟨g * γ t, MulAction.mem_stabilizer_iff.mpr (by rw [← hUt] at e1 ⊢; exact e1)⟩, ?_⟩, ?_⟩
    · change (g * γ t) • (γ t)⁻¹ • t = x
      rw [mul_smul, smul_inv_smul, hg]
    · rintro t' ⟨ht', ⟨g', hg'm⟩, hg'⟩
      obtain ⟨t₀, h₀, rfl⟩ := Finset.mem_image.mp ht'
      have h₀' := (Finset.mem_filter.mp h₀).1
      have : t₀ = t := huniq t₀ ⟨h₀', g' * (γ t₀)⁻¹, by rw [mul_smul]; exact hg'⟩
      rw [this]
  have hfinG : Finite (MulAction.stabilizer G u) := (hfinY u (hsY u hu)).to_subtype
  have hfinA : Finite ↥{x : X | x ∈ A ∧ π x = u} := by
    apply Set.Finite.to_subtype
    refine ((T : Set X).toFinite.biUnion
      (fun t _ => Set.finite_range (fun g : MulAction.stabilizer G u => g • t))).subset ?_
    intro x hx
    obtain ⟨t, ⟨ht, g, hg⟩, -⟩ := hT x hx
    exact Set.mem_biUnion (Finset.mem_coe.mpr ht) ⟨g, hg⟩
  have main := sum_inv_card_stab (G := MulAction.stabilizer G u) {x : X | x ∈ A ∧ π x = u}
    hstab T hTA hT
  have e0 : (Nat.card {x // x ∈ A ∧ π x = u} : ℝ) =
      (Nat.card ↥{x : X | x ∈ A ∧ π x = u} : ℝ) := rfl
  rw [e0, main, hTdef, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun t ht => ?_
  obtain ⟨ht1, rfl⟩ := Finset.mem_filter.mp ht
  have := card_stab_sub π hπ ((γ t)⁻¹ • t)
  rw [hπ' t (hsX t ht1)] at this
  rw [this, card_stab_smul]

end OrbSum

end Formalism.HermitianLattices.Ext.L3
