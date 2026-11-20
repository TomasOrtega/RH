import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ClosedStep

noncomputable section

namespace PI.VolSemiDirect.W

open MeasureTheory

/- English proof (translation)
Take `⟨V, hVo, hV⟩` from `isOpen_induced_iff.mp (isOpen_discrete ({1} : Set Λ))`. Establish `hV1 : ∀ γ : Λ, (γ : G) ∈ V ↔ γ = 1` using `fun γ => Set.ext_iff.mp hV γ`. Establish `h1V : (1 : G) ∈ V` using `(hV1 1).mpr rfl`. Take `⟨W, hWo, hW1, hWV⟩` from `exists_open_nhds_one_split (hVo.mem_nhds h1V)`. Take `⟨U, hUo, hU1, hUinv, hUV⟩ : ∃ U : Set G, IsOpen U ∧ (1 : G) ∈ U ∧ (∀ g ∈ U, g⁻¹ ∈ U) ∧ ∀ a ∈ U, ∀ b ∈ U, a * b⁻¹ ∈ V` from `⟨W ∩ (fun g => g⁻¹) ⁻¹' W, hWo.inter (hWo.preimage continuous_inv), ⟨hW1, by simpa using hW1⟩, fun g hg => ⟨hg.2, by simpa using hg.1⟩, fun a ha b hb => hWV a ha.1 _ hb.2⟩`.

Take `⟨d, hd⟩` from `TopologicalSpace.exists_dense_seq G`. Establish `hB : ∀ x : G, ∃ n, x * (d n)⁻¹ ∈ U`. Introduce `x`. Take `⟨n, hn⟩` from `hd.exists_mem_open (hUo.preimage (continuous_id.mul continuous_const) : IsOpen ((fun y => y * x⁻¹) ⁻¹' U)) ⟨x, by simpa using hU1⟩`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Use `hUinv _ hn` as an intermediate fact. Simplify `this` using `[mul_inv_rev]`. Establish `hBu : ∀ (n : ℕ) (γ γ' : Λ) (x : G), (γ : G) * x * (d n)⁻¹ ∈ U → (γ' : G) * x * (d n)⁻¹ ∈ U → γ = γ'`. Introduce `n γ γ' x h h'`. Establish `hm` using `hUV _ h _ h'`.

Establish `: ((γ * γ'⁻¹ : Λ) : G) ∈ V`. Use `hm using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Use `group`. Rewrite `this` using `[hV1, mul_inv_eq_one]`.

Conclude with `this`. Take `⟨S, hS, hSo⟩ : ∃ S : ℕ → Set G, (∀ m x, x ∈ S m ↔ ∃ γ : Λ, (γ : G) * x * (d m)⁻¹ ∈ U) ∧ ∀ m, IsOpen (S m)` from `⟨fun m => ⋃ γ : Λ, (fun x => (γ : G) * x * (d m)⁻¹) ⁻¹' U, fun m x => by simp, fun m => isOpen_iUnion fun γ => hUo.preimage ((continuous_const.mul continuous_id).mul continuous_const)⟩`. Establish `hinv : ∀ (γ : Λ) (y : G) (m : ℕ), (γ : G) * y ∈ S m ↔ y ∈ S m`. Introduce `γ y m`. Rewrite using `[hS, hS]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨δ, hδ⟩`. Conclude with `⟨δ * γ, by push_cast; simpa [mul_assoc] using hδ⟩`. Introduce and unpack `⟨δ, hδ⟩`. Conclude with `⟨δ * γ⁻¹, by push_cast; simpa [mul_assoc] using hδ⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨F, hF, hFm⟩ : ∃ F : Set G, (∀ y, y ∈ F ↔ ∃ n, y * (d n)⁻¹ ∈ U ∧ ∀ m < n, y ∉ S m) ∧ MeasurableSet F := by`. Use `⟨⋃ n, ((fun x => x * (d n)⁻¹) ⁻¹' U \ ⋃ m, ⋃ (_ : m < n), S m), fun y => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_iUnion, Set.mem_diff, Set.mem_preimage, not_exists]`. Conclude with `MeasurableSet.iUnion fun n => (hUo.preimage (continuous_id.mul continuous_const)).measurableSet.diff (isOpen_iUnion fun m => isOpen_iUnion fun _ => hSo m).measurableSet`. Use `⟨F, hFm, fun x => ?_⟩` and prove the remaining obligations.

Establish `hex : ∃ n, x ∈ S n`. Take `⟨n, hn⟩` from `hB x`. Conclude with `⟨n, (hS n x).mpr ⟨1, by simpa using hn⟩⟩`. Take `⟨n0, hn0x, hmin⟩ : ∃ n0, x ∈ S n0 ∧ ∀ m < n0, x ∉ S m` from `⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩`. Take `⟨γ, hγ⟩` from `(hS n0 x).mp hn0x`.

Use `⟨γ, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(γ : G) * x ∈ F`. Rewrite using `[hF]`. Conclude with `⟨n0, hγ, fun m hm h => hmin m hm ((hinv γ x m).mp h)⟩`. Introduce `γ' hγ'`.

Express the relevant statement in the definitionally equal form `(γ' : G) * x ∈ F at hγ'`. Rewrite `hγ'` using `[hF]`. Take `⟨n, hn, hnmin⟩` from `hγ'`. Establish `hxn : x ∈ S n` using `(hS n x).mpr ⟨γ', hn⟩`. Establish `hn0 : n = n0`.

Apply `le_antisymm` to reduce the goal to its premises. Assume the negation of the conclusion as `hlt push_neg at hlt`. Conclude with `hnmin n0 hlt ((hinv γ' x n0).mpr hn0x)`. Conclude with `not_lt.mp fun h => hmin n h hxn`. Rewrite `hn` using `[hn0]`.

Conclude with `hBu n0 γ' γ x hn hγ`.
-/
theorem exists_sfd {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Λ : Subgroup G)
    [DiscreteTopology Λ] :
    ∃ 𝓕 : Set G, MeasurableSet 𝓕 ∧ ∀ x : G, ∃! γ : Λ, γ • x ∈ 𝓕 := by
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.mp (isOpen_discrete ({1} : Set Λ))
  have hV1 : ∀ γ : Λ, (γ : G) ∈ V ↔ γ = 1 := fun γ => Set.ext_iff.mp hV γ
  have h1V : (1 : G) ∈ V := (hV1 1).mpr rfl
  obtain ⟨W, hWo, hW1, hWV⟩ := exists_open_nhds_one_split (hVo.mem_nhds h1V)
  obtain ⟨U, hUo, hU1, hUinv, hUV⟩ : ∃ U : Set G, IsOpen U ∧ (1 : G) ∈ U ∧ (∀ g ∈ U, g⁻¹ ∈ U) ∧
      ∀ a ∈ U, ∀ b ∈ U, a * b⁻¹ ∈ V :=
    ⟨W ∩ (fun g => g⁻¹) ⁻¹' W, hWo.inter (hWo.preimage continuous_inv), ⟨hW1, by simpa using hW1⟩,
      fun g hg => ⟨hg.2, by simpa using hg.1⟩, fun a ha b hb => hWV a ha.1 _ hb.2⟩
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq G

  have hB : ∀ x : G, ∃ n, x * (d n)⁻¹ ∈ U := by
    intro x
    obtain ⟨n, hn⟩ := hd.exists_mem_open
      (hUo.preimage (continuous_id.mul continuous_const) : IsOpen ((fun y => y * x⁻¹) ⁻¹' U))
      ⟨x, by simpa using hU1⟩
    refine ⟨n, ?_⟩
    have := hUinv _ hn
    simpa [mul_inv_rev] using this

  have hBu : ∀ (n : ℕ) (γ γ' : Λ) (x : G), (γ : G) * x * (d n)⁻¹ ∈ U →
      (γ' : G) * x * (d n)⁻¹ ∈ U → γ = γ' := by
    intro n γ γ' x h h'
    have hm := hUV _ h _ h'
    have : ((γ * γ'⁻¹ : Λ) : G) ∈ V := by
      convert hm using 1
      push_cast
      group
    rw [hV1, mul_inv_eq_one] at this
    exact this

  obtain ⟨S, hS, hSo⟩ : ∃ S : ℕ → Set G, (∀ m x, x ∈ S m ↔ ∃ γ : Λ, (γ : G) * x * (d m)⁻¹ ∈ U) ∧
      ∀ m, IsOpen (S m) :=
    ⟨fun m => ⋃ γ : Λ, (fun x => (γ : G) * x * (d m)⁻¹) ⁻¹' U, fun m x => by simp,
      fun m => isOpen_iUnion fun γ =>
        hUo.preimage ((continuous_const.mul continuous_id).mul continuous_const)⟩
  have hinv : ∀ (γ : Λ) (y : G) (m : ℕ), (γ : G) * y ∈ S m ↔ y ∈ S m := by
    intro γ y m
    rw [hS, hS]
    constructor
    · rintro ⟨δ, hδ⟩
      exact ⟨δ * γ, by push_cast; simpa [mul_assoc] using hδ⟩
    · rintro ⟨δ, hδ⟩
      exact ⟨δ * γ⁻¹, by push_cast; simpa [mul_assoc] using hδ⟩
  obtain ⟨F, hF, hFm⟩ : ∃ F : Set G, (∀ y, y ∈ F ↔ ∃ n, y * (d n)⁻¹ ∈ U ∧ ∀ m < n, y ∉ S m) ∧
      MeasurableSet F := by
    refine ⟨⋃ n, ((fun x => x * (d n)⁻¹) ⁻¹' U \ ⋃ m, ⋃ (_ : m < n), S m), fun y => ?_, ?_⟩
    · simp only [Set.mem_iUnion, Set.mem_diff, Set.mem_preimage, not_exists]
    · exact MeasurableSet.iUnion fun n =>
        (hUo.preimage (continuous_id.mul continuous_const)).measurableSet.diff
          (isOpen_iUnion fun m => isOpen_iUnion fun _ => hSo m).measurableSet
  refine ⟨F, hFm, fun x => ?_⟩
  have hex : ∃ n, x ∈ S n := by
    obtain ⟨n, hn⟩ := hB x
    exact ⟨n, (hS n x).mpr ⟨1, by simpa using hn⟩⟩
  classical
  obtain ⟨n0, hn0x, hmin⟩ : ∃ n0, x ∈ S n0 ∧ ∀ m < n0, x ∉ S m :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  obtain ⟨γ, hγ⟩ := (hS n0 x).mp hn0x
  refine ⟨γ, ?_, ?_⟩
  · change (γ : G) * x ∈ F
    rw [hF]
    exact ⟨n0, hγ, fun m hm h => hmin m hm ((hinv γ x m).mp h)⟩
  · intro γ' hγ'
    change (γ' : G) * x ∈ F at hγ'
    rw [hF] at hγ'
    obtain ⟨n, hn, hnmin⟩ := hγ'
    have hxn : x ∈ S n := (hS n x).mpr ⟨γ', hn⟩
    have hn0 : n = n0 := by
      apply le_antisymm
      · by_contra hlt
        push_neg at hlt
        exact hnmin n0 hlt ((hinv γ' x n0).mpr hn0x)
      · exact not_lt.mp fun h => hmin n h hxn
    rw [hn0] at hn
    exact hBu n0 γ' γ x hn hγ

/- English proof (translation)
Take `⟨F, hF, hex⟩` from `exists_sfd Λ`. Conclude with `⟨F, hF, fun μ => IsFundamentalDomain.mk' hF.nullMeasurableSet hex⟩`.
-/
theorem exists_fd {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Λ : Subgroup G)
    [DiscreteTopology Λ] :
    ∃ 𝓕 : Set G, MeasurableSet 𝓕 ∧ ∀ μ : Measure G, IsFundamentalDomain Λ 𝓕 μ := by
  obtain ⟨F, hF, hex⟩ := exists_sfd Λ
  exact ⟨F, hF, fun μ => IsFundamentalDomain.mk' hF.nullMeasurableSet hex⟩

/- English proof (translation)
Unfold `FDExG`. Introduce `X _ _ _ _ Γ K hK hD`. Take `⟨hlc, hsc, ht2, htg⟩` from `hK`. Take `⟨hcount, hdisc⟩` from `hD`. Conclude with `exists_fd (ratG Γ K)`.
-/
theorem fundamental_domain_exists : FDExG := by
  unfold FDExG
  intro X _ _ _ _ Γ K hK hD
  obtain ⟨hlc, hsc, ht2, htg⟩ := hK
  obtain ⟨hcount, hdisc⟩ := hD
  exact exists_fd (ratG Γ K)

end PI.VolSemiDirect.W
