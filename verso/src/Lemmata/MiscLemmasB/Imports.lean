import Mathlib

open MeasureTheory Topology

namespace Bl.SecondBlockLemmaC

/- English proof (translation)
Take `⟨U, hUo, hU⟩` from `isOpen_induced_iff.mp (isOpen_discrete ({1} : Set Γ))`. Establish `h1U : (1 : G) ∈ U`. Establish `h : (1 : Γ) ∈ ((↑) : Γ → G) ⁻¹' U` using `by rw [hU]; rfl`. Simplify using `using h`. Take `⟨V, hVo, h1V, hV⟩` from `exists_open_nhds_one_split (hUo.mem_nhds h1U)`.

Use `set W : Set G := V ∩ V⁻¹ with hW`. Establish `hWo : IsOpen W` using `hVo.inter hVo.inv`. Establish `h1W : (1 : G) ∈ W` using `⟨h1V, by simpa using h1V⟩`. Establish `key : ∀ a ∈ W, ∀ b ∈ W, ∀ γ : Γ, (γ : G) = b * a⁻¹ → γ = 1`. Introduce `a ha b hb γ hγ`.

Establish `h2 : a⁻¹ ∈ V` using `by simpa using ha.2`. Establish `h3 : (γ : G) ∈ U` using `hγ ▸ hV b hb.1 a⁻¹ h2`. Establish `h4 : γ ∈ ((↑) : Γ → G) ⁻¹' U` using `h3`. Rewrite `h4` using `[hU]`. Conclude with `h4`.

Take `⟨u, hu⟩` from `TopologicalSpace.exists_dense_seq G`. Set `Q : G → ℕ → Prop` to `fun x n => ∃ γ : Γ, (γ : G) * x * (u n)⁻¹ ∈ W`. Establish `hQinv : ∀ (δ : Γ) (x : G) (n : ℕ), Q ((δ : G) * x) n ↔ Q x n`. Introduce `δ x n`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨γ, hγ⟩`. Conclude with `⟨γ * δ, by simpa [mul_assoc] using hγ⟩`. Introduce and unpack `⟨γ, hγ⟩`. Conclude with `⟨γ * δ⁻¹, by simpa [mul_assoc] using hγ⟩`. Establish `hQex : ∀ x, ∃ n, Q x n`.

Introduce `x`. Take `⟨n, hn⟩` from `hu.exists_mem_open (s := {g | x * g⁻¹ ∈ W}) (hWo.preimage (by fun_prop)) ⟨x, by simpa using h1W⟩`. Conclude with `⟨n, 1, by simpa using hn⟩`. Set `s : Set G` to `{x | ∃ n, x * (u n)⁻¹ ∈ W ∧ ∀ m < n, ¬ Q x m}`. Establish `hs : s = ⋃ n, ({x | x * (u n)⁻¹ ∈ W} ∩ ⋂ m, ⋂ (_ : m < n), (⋃ γ : Γ, {x | (γ : G) * x * (u m)⁻¹ ∈ W})ᶜ)`.

Use extensionality with `x`. Simplify using `[s, Q]`. Establish `hsm : MeasurableSet s`. Rewrite using `[hs]`. Use `MeasurableSet.iUnion fun n => ?_` and prove the remaining obligations.

Use `MeasurableSet.inter (hWo.preimage (by fun_prop)).measurableSet ?_` and prove the remaining obligations. Use `MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ => ?_` and prove the remaining obligations. Use `MeasurableSet.compl ?_` and prove the remaining obligations. Conclude with `(isOpen_iUnion fun γ => hWo.preimage (by fun_prop)).measurableSet`. Use `⟨s, hsm, fun μ => IsFundamentalDomain.mk' hsm.nullMeasurableSet fun x => ?_⟩` and prove the remaining obligations.

Take `⟨γ, hγ⟩` from `Nat.find_spec (hQex x)`. Use `⟨γ, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(γ : G) * x ∈ s`. Use `⟨Nat.find (hQex x), hγ, fun m hm => ?_⟩` and prove the remaining obligations. Rewrite using `[hQinv]`.

Conclude with `Nat.find_min (hQex x) hm`. Introduce `δ hδ`. Express the relevant statement in the definitionally equal form `(δ : G) * x ∈ s at hδ`. Take `⟨k, hk, hkmin⟩` from `hδ`. Establish `hQk : Q x k` using `⟨δ, by simpa [mul_assoc] using hk⟩`.

Establish `hle : Nat.find (hQex x) ≤ k` using `Nat.find_min' (hQex x) hQk`. Establish `hk' : k = Nat.find (hQex x)`. Break down `Nat.lt_or_ge (Nat.find (hQex x)) k with h | h` into its components or cases. Conclude with `absurd ((hQinv δ x _).mpr (Nat.find_spec (hQex x))) (hkmin _ h)`. Use linear arithmetic over natural numbers and integers.

Rewrite `hk` using `[hk']`. Establish `hd : ((δ * γ⁻¹ : Γ) : G) = ((δ : G) * x * (u (Nat.find (hQex x)))⁻¹) * ((γ : G) * x * (u (Nat.find (hQex x)))⁻¹)⁻¹`. Simplify using `[mul_assoc]`. Establish `h1` using `key _ hγ _ hk _ hd`. Conclude with `mul_inv_eq_one.mp h1`.
-/
theorem goal1 {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] :
    ∃ s : Set G, MeasurableSet s ∧ ∀ μ : Measure G, IsFundamentalDomain Γ s μ := by
  classical
  obtain ⟨U, hUo, hU⟩ := isOpen_induced_iff.mp (isOpen_discrete ({1} : Set Γ))
  have h1U : (1 : G) ∈ U := by
    have h : (1 : Γ) ∈ ((↑) : Γ → G) ⁻¹' U := by rw [hU]; rfl
    simpa using h
  obtain ⟨V, hVo, h1V, hV⟩ := exists_open_nhds_one_split (hUo.mem_nhds h1U)
  set W : Set G := V ∩ V⁻¹ with hW
  have hWo : IsOpen W := hVo.inter hVo.inv
  have h1W : (1 : G) ∈ W := ⟨h1V, by simpa using h1V⟩
  have key : ∀ a ∈ W, ∀ b ∈ W, ∀ γ : Γ, (γ : G) = b * a⁻¹ → γ = 1 := by
    intro a ha b hb γ hγ
    have h2 : a⁻¹ ∈ V := by simpa using ha.2
    have h3 : (γ : G) ∈ U := hγ ▸ hV b hb.1 a⁻¹ h2
    have h4 : γ ∈ ((↑) : Γ → G) ⁻¹' U := h3
    rw [hU] at h4
    exact h4
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq G
  let Q : G → ℕ → Prop := fun x n => ∃ γ : Γ, (γ : G) * x * (u n)⁻¹ ∈ W
  have hQinv : ∀ (δ : Γ) (x : G) (n : ℕ), Q ((δ : G) * x) n ↔ Q x n := by
    intro δ x n
    constructor
    · rintro ⟨γ, hγ⟩
      exact ⟨γ * δ, by simpa [mul_assoc] using hγ⟩
    · rintro ⟨γ, hγ⟩
      exact ⟨γ * δ⁻¹, by simpa [mul_assoc] using hγ⟩
  have hQex : ∀ x, ∃ n, Q x n := by
    intro x
    obtain ⟨n, hn⟩ := hu.exists_mem_open (s := {g | x * g⁻¹ ∈ W})
      (hWo.preimage (by fun_prop)) ⟨x, by simpa using h1W⟩
    exact ⟨n, 1, by simpa using hn⟩
  let s : Set G := {x | ∃ n, x * (u n)⁻¹ ∈ W ∧ ∀ m < n, ¬ Q x m}
  have hs : s = ⋃ n, ({x | x * (u n)⁻¹ ∈ W} ∩
      ⋂ m, ⋂ (_ : m < n), (⋃ γ : Γ, {x | (γ : G) * x * (u m)⁻¹ ∈ W})ᶜ) := by
    ext x
    simp [s, Q]
  have hsm : MeasurableSet s := by
    rw [hs]
    refine MeasurableSet.iUnion fun n => ?_
    refine MeasurableSet.inter (hWo.preimage (by fun_prop)).measurableSet ?_
    refine MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ => ?_
    refine MeasurableSet.compl ?_
    exact (isOpen_iUnion fun γ => hWo.preimage (by fun_prop)).measurableSet
  refine ⟨s, hsm, fun μ => IsFundamentalDomain.mk' hsm.nullMeasurableSet fun x => ?_⟩
  obtain ⟨γ, hγ⟩ := Nat.find_spec (hQex x)
  refine ⟨γ, ?_, ?_⟩
  · change (γ : G) * x ∈ s
    refine ⟨Nat.find (hQex x), hγ, fun m hm => ?_⟩
    rw [hQinv]
    exact Nat.find_min (hQex x) hm
  · intro δ hδ
    change (δ : G) * x ∈ s at hδ
    obtain ⟨k, hk, hkmin⟩ := hδ
    have hQk : Q x k := ⟨δ, by simpa [mul_assoc] using hk⟩
    have hle : Nat.find (hQex x) ≤ k := Nat.find_min' (hQex x) hQk
    have hk' : k = Nat.find (hQex x) := by
      rcases Nat.lt_or_ge (Nat.find (hQex x)) k with h | h
      · exact absurd ((hQinv δ x _).mpr (Nat.find_spec (hQex x))) (hkmin _ h)
      · omega
    rw [hk'] at hk
    have hd : ((δ * γ⁻¹ : Γ) : G) = ((δ : G) * x * (u (Nat.find (hQex x)))⁻¹) *
        ((γ : G) * x * (u (Nat.find (hQex x)))⁻¹)⁻¹ := by
      simp [mul_assoc]
    have h1 := key _ hγ _ hk _ hd
    exact mul_inv_eq_one.mp h1

end Bl.SecondBlockLemmaC
