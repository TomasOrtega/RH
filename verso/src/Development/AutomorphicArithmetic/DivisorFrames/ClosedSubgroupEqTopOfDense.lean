import Mathlib
open Filter Topology

/- English proof (translation)
Establish `hne : (Additive.ofMul (a : G ⧸ H)) ≠ 0` using `fun h => ha ((QuotientGroup.eq_one_iff _).1 h)`. Take `⟨χ, hχ⟩` from `CharacterModule.exists_character_apply_ne_zero_of_ne_zero hne`. Set `e : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ)` to `QuotientAddGroup.map _ _ (Rat.castHom ℝ).toAddMonoidHom (by`. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `⟨k, by simp⟩)`.

Establish `he : ∀ a, e a = 0 → a = 0`. Introduce `a`. Proceed by induction on `a using QuotientAddGroup.induction_on with`. Consider the case `H q`. Introduce `h`.

Establish `h1 : (((q : ℝ)) : AddCircle (1 : ℝ)) = 0` using `h`. Rewrite `h1`, the goal using `[AddCircle.coe_eq_zero_iff]`. Take `⟨k, hk⟩` from `h1`. Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `: ((k : ℚ) : ℝ) = q` using `by simpa using hk`.

Establish `h5 : (k : ℚ) = q` using `by exact_mod_cast this`. Simplify using `using h5`. Set `f : G → AddCircle (1 : ℝ)` to `fun x => e (χ (Additive.ofMul (x : G ⧸ H)))`. Establish `hf1 : f 1 = 0` using `by show e (χ 0) = 0`. Rewrite using `[map_zero, map_zero]`.

Establish `hfm : ∀ a b, f (a * b) = f a + f b`. Introduce `a b`. Use `show e (χ (Additive.ofMul (a : G ⧸ H) + Additive.ofMul (b : G ⧸ H))) = _`. Rewrite using `[map_add, map_add]`. Set `ψ : G →* Circle` to `{ toFun := fun x => AddCircle.toCircle (f x) map_one' := by rw [hf1, AddCircle.toCircle_zero] map_mul' := fun a b => by rw [hfm, AddCircle.toCircle_add] }`.

Use `⟨ψ, fun u hu => ?_, ?_⟩` and prove the remaining obligations. Establish `h0 : (u : G ⧸ H) = 1` using `(QuotientGroup.eq_one_iff _).2 hu`. Establish `: f u = 0` using `by show e (χ (Additive.ofMul (u : G ⧸ H))) = 0`. Rewrite using `[h0, ofMul_one, map_zero, map_zero]`. Use `show AddCircle.toCircle (f u) = 1`.

Rewrite using `[this, AddCircle.toCircle_zero]`. Introduce `h`. Establish `h2 : AddCircle.toCircle (f a) = AddCircle.toCircle (0 : AddCircle (1 : ℝ))`. Rewrite using `[AddCircle.toCircle_zero]`. Conclude with `h`.

Conclude with `hχ (he _ (AddCircle.injective_toCircle (T := (1 : ℝ)) one_ne_zero h2))`.
-/
private theorem UpperTheory.exists_character_nontrivial_off {G : Type} [CommGroup G] (H : Subgroup G) {a : G} (ha : a ∉ H) :
    ∃ ψ : G →* Circle, (∀ u ∈ H, ψ u = 1) ∧ ψ a ≠ 1 := by
  have hne : (Additive.ofMul (a : G ⧸ H)) ≠ 0 := fun h => ha ((QuotientGroup.eq_one_iff _).1 h)
  obtain ⟨χ, hχ⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hne
  let e : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
    QuotientAddGroup.map _ _ (Rat.castHom ℝ).toAddMonoidHom (by
      rintro _ ⟨k, rfl⟩
      exact ⟨k, by simp⟩)
  have he : ∀ a, e a = 0 → a = 0 := by
    intro a
    induction a using QuotientAddGroup.induction_on with
    | H q =>
      intro h
      have h1 : (((q : ℝ)) : AddCircle (1 : ℝ)) = 0 := h
      rw [AddCircle.coe_eq_zero_iff] at h1 ⊢
      obtain ⟨k, hk⟩ := h1
      refine ⟨k, ?_⟩
      have : ((k : ℚ) : ℝ) = q := by simpa using hk
      have h5 : (k : ℚ) = q := by exact_mod_cast this
      simpa using h5
  let f : G → AddCircle (1 : ℝ) := fun x => e (χ (Additive.ofMul (x : G ⧸ H)))
  have hf1 : f 1 = 0 := by
    show e (χ 0) = 0
    rw [map_zero, map_zero]
  have hfm : ∀ a b, f (a * b) = f a + f b := by
    intro a b
    show e (χ (Additive.ofMul (a : G ⧸ H) + Additive.ofMul (b : G ⧸ H))) = _
    rw [map_add, map_add]
  let ψ : G →* Circle :=
    { toFun := fun x => AddCircle.toCircle (f x)
      map_one' := by rw [hf1, AddCircle.toCircle_zero]
      map_mul' := fun a b => by rw [hfm, AddCircle.toCircle_add] }
  refine ⟨ψ, fun u hu => ?_, ?_⟩
  · have h0 : (u : G ⧸ H) = 1 := (QuotientGroup.eq_one_iff _).2 hu
    have : f u = 0 := by
      show e (χ (Additive.ofMul (u : G ⧸ H))) = 0
      rw [h0, ofMul_one, map_zero, map_zero]
    show AddCircle.toCircle (f u) = 1
    rw [this, AddCircle.toCircle_zero]
  · intro h
    have h2 : AddCircle.toCircle (f a) = AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
      rw [AddCircle.toCircle_zero]; exact h
    exact hχ (he _ (AddCircle.injective_toCircle (T := (1 : ℝ)) one_ne_zero h2))

/- English proof (translation)
Introduce `G _ _ _ M hM hchar hsmall`. Establish `step1 : ∀ (O : OpenSubgroup G) (g : G), g ∈ M ⊔ O.toSubgroup`. Introduce `O g`. Assume the negation of the conclusion as `hg`. Take `⟨ψ, h1, h2⟩` from `UpperTheory.exists_character_nontrivial_off _ hg`.

Establish `hc : Continuous ψ`. Apply `continuous_of_continuousAt_one` to reduce the goal to its premises. Establish `hev : (fun _ : G => (1 : Circle)) =ᶠ[nhds (1 : G)] ψ` using `by filter_upwards [O.mem_nhds_one] with x hx`. Conclude with `(h1 x (Subgroup.mem_sup_right hx)).symm`. Conclude with `continuousAt_const.congr hev`.

Use `hchar ψ hc (fun m hm => h1 m (Subgroup.mem_sup_left hm))` as an intermediate fact. Conclude with `h2 (by rw [this]; rfl)`. Rewrite using `[eq_top_iff]`. Introduce `g _`. Establish `: g ∈ closure (M : Set G)`.

Rewrite using `[mem_closure_iff_nhds]`. Introduce `U hU`. Establish `hcont : Continuous (fun w : G => g * w⁻¹)` using `by fun_prop`. Establish `hW : (fun w : G => g * w⁻¹) ⁻¹' U ∈ nhds (1 : G)` using `hcont.continuousAt.preimage_mem_nhds (by simpa using hU)`. Take `⟨O, hO⟩` from `hsmall _ hW`.

Take `⟨m, hm, o, ho, hmo⟩` from `Subgroup.mem_sup.1 (step1 O g)`. Take `⟨m', hm', w, hw, rfl⟩` from `hO o ho`. Use `⟨g * w⁻¹, hw, ?_⟩` and prove the remaining obligations. Establish `: g * w⁻¹ = m * m'` using `by rw [← hmo]; group`. Rewrite using `[this]`.

Conclude with `M.mul_mem hm hm'`. Rewrite `this` using `[hM.closure_eq]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.closed_subgroup_eq_top_of_dense :
    ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] (M : Subgroup G), IsClosed (M : Set G) →
        (∀ μ : G →* Circle, Continuous μ → (∀ m ∈ M, μ m = 1) → μ = 1) →
        (∀ W ∈ nhds (1 : G), ∃ O : OpenSubgroup G, ∀ o ∈ O, ∃ m ∈ M, ∃ w ∈ W, o = m * w) → M = ⊤ := by
  intro G _ _ _ M hM hchar hsmall
  have step1 : ∀ (O : OpenSubgroup G) (g : G), g ∈ M ⊔ O.toSubgroup := by
    intro O g
    by_contra hg
    obtain ⟨ψ, h1, h2⟩ := UpperTheory.exists_character_nontrivial_off _ hg
    have hc : Continuous ψ := by
      apply continuous_of_continuousAt_one
      have hev : (fun _ : G => (1 : Circle)) =ᶠ[nhds (1 : G)] ψ := by
        filter_upwards [O.mem_nhds_one] with x hx
        exact (h1 x (Subgroup.mem_sup_right hx)).symm
      exact continuousAt_const.congr hev
    have := hchar ψ hc (fun m hm => h1 m (Subgroup.mem_sup_left hm))
    exact h2 (by rw [this]; rfl)
  rw [eq_top_iff]
  intro g _
  have : g ∈ closure (M : Set G) := by
    rw [mem_closure_iff_nhds]
    intro U hU
    have hcont : Continuous (fun w : G => g * w⁻¹) := by fun_prop
    have hW : (fun w : G => g * w⁻¹) ⁻¹' U ∈ nhds (1 : G) :=
      hcont.continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨O, hO⟩ := hsmall _ hW
    obtain ⟨m, hm, o, ho, hmo⟩ := Subgroup.mem_sup.1 (step1 O g)
    obtain ⟨m', hm', w, hw, rfl⟩ := hO o ho
    refine ⟨g * w⁻¹, hw, ?_⟩
    have : g * w⁻¹ = m * m' := by rw [← hmo]; group
    rw [this]
    exact M.mul_mem hm hm'
  rwa [hM.closure_eq] at this
