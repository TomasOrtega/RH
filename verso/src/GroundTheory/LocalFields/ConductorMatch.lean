import Mathlib
import GroundTheory.LocalFields.ConductorReciprocity

noncomputable section

open ValuativeRel

namespace GroundTheory.LocalField

section Def

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] (L : IntermediateField K Ω) [FiniteDimensional K L]

def conductor : ℕ :=
  sInf {n : ℕ | unitFiltrationUnits K n ≤ (normUnits K L).range}

/- English proof (translation)
Establish `hne : {n : ℕ | unitFiltrationUnits K n ≤ (normUnits K L).range}.Nonempty` using `exists_unitFiltrationUnits_le (isOpen_range_normUnits_and_finiteIndex L).1`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `(unitFiltrationUnits_antitone h).trans (Nat.sInf_mem hne)`. Introduce `h`.

Conclude with `Nat.sInf_le h`.
-/
theorem conductor_le_iff [IsSepClosure K Ω] (n : ℕ) :
    conductor L ≤ n ↔ unitFiltrationUnits K n ≤ (normUnits K L).range := by
  have hne : {n : ℕ | unitFiltrationUnits K n ≤ (normUnits K L).range}.Nonempty :=
    exists_unitFiltrationUnits_le (isOpen_range_normUnits_and_finiteIndex L).1
  constructor
  · intro h
    exact (unitFiltrationUnits_antitone h).trans (Nat.sInf_mem hne)
  · intro h
    exact Nat.sInf_le h

end Def

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]

section Conductor

variable (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]

/- English proof (translation)
Assume the negation of the conclusion as `hv`. Simplify using `only [not_exists] at hv`. Establish `hlt : v < ⌈v⌉` using `lt_of_le_of_ne (Int.le_ceil v) (hv ⌈v⌉)`. Apply `h _ hlt` to reduce the goal to its premises. Rewrite using `[upperRamificationGroup_eq_ceil L v, upperRamificationGroup_eq_ceil L (⌈v⌉ : ℝ), Int.ceil_intCast]`.
-/
theorem exists_int_eq_of_forall_upperRamificationGroup_ne {v : ℝ}
    (h : ∀ w, v < w → upperRamificationGroup K L w ≠ upperRamificationGroup K L v) :
    ∃ m : ℤ, v = m := by
  by_contra hv
  simp only [not_exists] at hv
  have hlt : v < ⌈v⌉ := lt_of_le_of_ne (Int.le_ceil v) (hv ⌈v⌉)
  apply h _ hlt
  rw [upperRamificationGroup_eq_ceil L v, upperRamificationGroup_eq_ceil L (⌈v⌉ : ℝ), Int.ceil_intCast]

/- English proof (translation)
Rewrite using `[← map_unitFiltrationUnits_restrictAb_localArtinMap L n, Subgroup.map_eq_bot_iff, ker_restrictAb_localArtinMap]`.
-/
theorem unitFiltrationUnits_le_range_normUnits_iff (n : ℕ) :
    unitFiltrationUnits K n ≤ (normUnits K L).range ↔ upperRamificationGroup K L n = ⊥ := by
  rw [← map_unitFiltrationUnits_restrictAb_localArtinMap L n, Subgroup.map_eq_bot_iff,
    ker_restrictAb_localArtinMap]

/- English proof (translation)
Rewrite using `[conductor_le_iff, unitFiltrationUnits_le_range_normUnits_iff]`.
-/
theorem upperRamificationGroup_natCast_eq_bot_iff (n : ℕ) :
    upperRamificationGroup K L n = ⊥ ↔ conductor L ≤ n := by
  rw [conductor_le_iff, unitFiltrationUnits_le_range_normUnits_iff]

/- English proof (translation)
Break down `le_or_gt v (-1) with hv | hv` into its components or cases. Establish `htop : upperRamificationGroup K L v = ⊤`. Rewrite using `[upperRamificationGroup_of_nonpos (by linarith), lowerRamificationGroupReal_eq_top hv]`. Establish `hG : (⊤ : Subgroup (L ≃ₐ[K] L)) ≠ ⊥`. Establish `h1 : Module.finrank K L ≠ 1` using `fun h => hL (IntermediateField.finrank_eq_one_iff.1 h)`.

Establish `h2 : 1 < Nat.card (L ≃ₐ[K] L)`. Rewrite using `[IsGalois.card_aut_eq_finrank]`. Use `Module.finrank_pos (R := K) (M := L)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `: Nontrivial (L ≃ₐ[K] L)` using `Finite.one_lt_card_iff_nontrivial.1 h2`.

Conclude with `top_ne_bot`. Rewrite using `[htop]`. Simplify using `only [hG, false_iff, not_lt]`. Use `(conductor L).cast_nonneg (α := ℝ)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hc : 0 ≤ ⌈v⌉` using `Int.le_ceil_iff.2 (by push_cast; linarith)`. Take `⟨k, hk⟩` from `Int.eq_ofNat_of_zero_le hc`. Rewrite using `[upperRamificationGroup_eq_ceil L v, hk, Int.cast_natCast, upperRamificationGroup_natCast_eq_bot_iff, ← Nat.cast_le (α := ℤ), ← hk, Int.le_ceil_iff]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem upperRamificationGroup_eq_bot_iff (hL : L ≠ ⊥) (v : ℝ) :
    upperRamificationGroup K L v = ⊥ ↔ (conductor L : ℝ) - 1 < v := by
  rcases le_or_gt v (-1) with hv | hv
  · have htop : upperRamificationGroup K L v = ⊤ := by
      rw [upperRamificationGroup_of_nonpos (by linarith), lowerRamificationGroupReal_eq_top hv]
    have hG : (⊤ : Subgroup (L ≃ₐ[K] L)) ≠ ⊥ := by
      have h1 : Module.finrank K L ≠ 1 := fun h => hL (IntermediateField.finrank_eq_one_iff.1 h)
      have h2 : 1 < Nat.card (L ≃ₐ[K] L) := by
        rw [IsGalois.card_aut_eq_finrank]
        have := Module.finrank_pos (R := K) (M := L)
        omega
      have : Nontrivial (L ≃ₐ[K] L) := Finite.one_lt_card_iff_nontrivial.1 h2
      exact top_ne_bot
    rw [htop]
    simp only [hG, false_iff, not_lt]
    have := (conductor L).cast_nonneg (α := ℝ)
    linarith
  · have hc : 0 ≤ ⌈v⌉ := Int.le_ceil_iff.2 (by push_cast; linarith)
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hc
    rw [upperRamificationGroup_eq_ceil L v, hk, Int.cast_natCast, upperRamificationGroup_natCast_eq_bot_iff,
      ← Nat.cast_le (α := ℤ), ← hk, Int.le_ceil_iff]
    push_cast
    rfl

/- English proof (translation)
Use `⟨?_, fun v hv => ?_⟩` and prove the remaining obligations. Use `show upperRamificationGroup K L _ ≠ ⊥`. Rewrite using `[Ne, upperRamificationGroup_eq_bot_iff L hL]`. Conclude with `lt_irrefl _`. Establish `hv' : ¬ ((conductor L : ℝ) - 1 < v)` using `fun h => hv ((upperRamificationGroup_eq_bot_iff L hL v).2 h)`.

Conclude with `not_lt.1 hv'`.
-/
theorem isGreatest_conductor_sub_one (hL : L ≠ ⊥) :
    IsGreatest {v : ℝ | upperRamificationGroup K L v ≠ ⊥} ((conductor L : ℝ) - 1) := by
  refine ⟨?_, fun v hv => ?_⟩
  · show upperRamificationGroup K L _ ≠ ⊥
    rw [Ne, upperRamificationGroup_eq_bot_iff L hL]
    exact lt_irrefl _
  · have hv' : ¬ ((conductor L : ℝ) - 1 < v) := fun h => hv ((upperRamificationGroup_eq_bot_iff L hL v).2 h)
    exact not_lt.1 hv'

end Conductor

section Ab

variable (K Ω) in

def upperRamificationGroupAb (v : ℝ) :
    Subgroup (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) :=
  ⨅ (L : IntermediateField K Ω) (_ : FiniteDimensional K L) (_ : IsAbelianGalois K L),
    (upperRamificationGroup K L v).comap (restrictAb L (le_maximalAbelianExtension L))

/- English proof (translation)
Simplify using `only [upperRamificationGroupAb, Subgroup.mem_iInf, Subgroup.mem_comap]`.
-/
theorem mem_upperRamificationGroupAb {v : ℝ}
    {g : maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω} :
    g ∈ upperRamificationGroupAb K Ω v ↔
      ∀ (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L],
        restrictAb L (le_maximalAbelianExtension L) g ∈ upperRamificationGroup K L v := by
  simp only [upperRamificationGroupAb, Subgroup.mem_iInf, Subgroup.mem_comap]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite using `[mem_upperRamificationGroupAb]`. Introduce `L _ _`. Rewrite using `[← map_unitFiltrationUnits_restrictAb_localArtinMap L n]`.

Conclude with `⟨x, hx, rfl⟩`. Introduce `g hg`. Rewrite `hg` using `[mem_upperRamificationGroupAb]`. Set `ι` to `{L : IntermediateField K Ω // FiniteDimensional K L ∧ IsAbelianGalois K L}`. Establish `hle : ∀ L : ι, L.1 ≤ maximalAbelianExtension K Ω` using `fun L => by`.

Use `L.2.1` as an intermediate fact. Use `L.2.2` as an intermediate fact. Conclude with `le_maximalAbelianExtension L.1`. Set `t : ι → Set Kˣ` to `fun L => {x | x ∈ unitFiltrationUnits K n ∧ ∀ (y : Ω) (hy : y ∈ L.1), localArtinMap K Ω x ⟨y, hle L hy⟩ = g ⟨y, hle L hy⟩}`. Establish `ht : ∀ L : ι, t L = (unitFiltrationUnits K n : Set Kˣ) ∩ (fun x => haveI` using `L.2.1; haveI := L.2.2 restrictAb L.1 (le_maximalAbelianExtension L.1) (localArtinMap K Ω x)) ⁻¹' {haveI := L.2.1; haveI := L.2.2; restrictAb L.1 (le_maximalAbelianExtension L.1) g} := by`.

Introduce `L`. Use `L.2.1` as an intermediate fact. Use `L.2.2` as an intermediate fact. Use extensionality with `x`. Simplify using `only [t, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]`.

Use `and_congr_right fun _ => ⟨fun h => ?_, fun h y hy => ?_⟩` and prove the remaining obligations. Use `AlgEquiv.ext fun y => Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[restrictAb_apply, restrictAb_apply]`. Conclude with `congrArg Subtype.val (h y.1 y.2)`. Use `congrArg (fun σ : L.1 ≃ₐ[K] L.1 => ((σ ⟨y, hy⟩ : L.1) : Ω)) h` as an intermediate fact.

Simplify using `only [restrictAb_apply] at this`. Conclude with `Subtype.ext this`. Establish `hι : Nonempty ι` using `⟨⟨⊥, inferInstance, isAbelianGalois_of_le_maximalAbelianExtension ⊥ bot_le⟩⟩`. Establish `hcl : ∀ L : ι, IsClosed ((fun x => haveI` using `L.2.1; haveI := L.2.2 restrictAb L.1 (le_maximalAbelianExtension L.1) (localArtinMap K Ω x)) ⁻¹' {haveI := L.2.1; haveI := L.2.2; restrictAb L.1 (le_maximalAbelianExtension L.1) g}) := by`. Introduce `L`.

Use `L.2.1` as an intermediate fact. Use `L.2.2` as an intermediate fact. Establish `: T2Space (L.1 ≃ₐ[K] L.1)` using `krullTopology_t2`. Conclude with `isClosed_singleton.preimage ((continuous_restrictAb L.1 _).comp continuous_localArtinMap)`. Establish `hdir : Directed (· ⊇ ·) t`.

Introduce `L₁ L₂`. Use `L₁.2.1` as an intermediate fact. Use `L₁.2.2` as an intermediate fact. Use `L₂.2.1` as an intermediate fact. Use `L₂.2.2` as an intermediate fact.

Establish `hab : IsAbelianGalois K (L₁.1 ⊔ L₂.1 : IntermediateField K Ω)` using `isAbelianGalois_of_le_maximalAbelianExtension _ (sup_le (hle L₁) (hle L₂))`. Use `⟨⟨L₁.1 ⊔ L₂.1, inferInstance, hab⟩, ?_, ?_⟩` and prove the remaining obligations. Conclude with `fun x hx => ⟨hx.1, fun y hy => hx.2 y (le_sup_left (b := L₂.1) hy)⟩`. Conclude with `fun x hx => ⟨hx.1, fun y hy => hx.2 y (le_sup_right (a := L₁.1) hy)⟩`. Establish `hnon : ∀ L, (t L).Nonempty`.

Introduce `L`. Use `L.2.1` as an intermediate fact. Use `L.2.2` as an intermediate fact. Establish `hgL` using `hg L.1`. Rewrite `hgL` using `[← map_unitFiltrationUnits_restrictAb_localArtinMap L.1 n]`.

Take `⟨x, hxn, hxg⟩` from `hgL`. Use `⟨x, ?_⟩` and prove the remaining obligations. Rewrite using `[ht L]`. Conclude with `⟨hxn, hxg⟩`. Take `⟨x, hx⟩` from `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir hnon (fun L => by rw [ht L]; exact (isCompact_unitFiltrationUnits n).inter_right (hcl L)) (fun L => by rw [ht L]; exact (isCompact_unitFiltrationUnits n).isClosed.inter (hcl L))`.

Rewrite `hx` using `[Set.mem_iInter]`. Take `⟨L₀⟩` from `hι`. Use `⟨x, (hx L₀).1, ?_⟩` and prove the remaining obligations. Use `AlgEquiv.ext fun y => Subtype.ext ?_` and prove the remaining obligations. Take `⟨L, hfin, hab, hyL⟩` from `exists_finite_abelian_mem y.2`.

Conclude with `congrArg Subtype.val ((hx ⟨L, hfin, hab⟩).2 y hyL)`.
-/
theorem map_unitFiltrationUnits_localArtinMap (n : ℕ) :
    (unitFiltrationUnits K n).map (localArtinMap K Ω) = upperRamificationGroupAb K Ω n := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_upperRamificationGroupAb]
    intro L _ _
    rw [← map_unitFiltrationUnits_restrictAb_localArtinMap L n]
    exact ⟨x, hx, rfl⟩
  intro g hg
  rw [mem_upperRamificationGroupAb] at hg
  let ι := {L : IntermediateField K Ω // FiniteDimensional K L ∧ IsAbelianGalois K L}
  have hle : ∀ L : ι, L.1 ≤ maximalAbelianExtension K Ω := fun L => by
    have := L.2.1
    have := L.2.2
    exact le_maximalAbelianExtension L.1
  let t : ι → Set Kˣ := fun L => {x | x ∈ unitFiltrationUnits K n ∧
    ∀ (y : Ω) (hy : y ∈ L.1), localArtinMap K Ω x ⟨y, hle L hy⟩ = g ⟨y, hle L hy⟩}

  have ht : ∀ L : ι, t L = (unitFiltrationUnits K n : Set Kˣ) ∩
      (fun x => haveI := L.2.1; haveI := L.2.2
        restrictAb L.1 (le_maximalAbelianExtension L.1) (localArtinMap K Ω x)) ⁻¹'
        {haveI := L.2.1; haveI := L.2.2; restrictAb L.1 (le_maximalAbelianExtension L.1) g} := by
    intro L
    have := L.2.1
    have := L.2.2
    ext x
    simp only [t, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      SetLike.mem_coe]
    refine and_congr_right fun _ => ⟨fun h => ?_, fun h y hy => ?_⟩
    · refine AlgEquiv.ext fun y => Subtype.ext ?_
      rw [restrictAb_apply, restrictAb_apply]
      exact congrArg Subtype.val (h y.1 y.2)
    · have := congrArg (fun σ : L.1 ≃ₐ[K] L.1 => ((σ ⟨y, hy⟩ : L.1) : Ω)) h
      simp only [restrictAb_apply] at this
      exact Subtype.ext this
  have hι : Nonempty ι := ⟨⟨⊥, inferInstance, isAbelianGalois_of_le_maximalAbelianExtension ⊥ bot_le⟩⟩
  have hcl : ∀ L : ι, IsClosed ((fun x => haveI := L.2.1; haveI := L.2.2
      restrictAb L.1 (le_maximalAbelianExtension L.1) (localArtinMap K Ω x)) ⁻¹'
        {haveI := L.2.1; haveI := L.2.2; restrictAb L.1 (le_maximalAbelianExtension L.1) g}) := by
    intro L
    have := L.2.1
    have := L.2.2
    have : T2Space (L.1 ≃ₐ[K] L.1) := krullTopology_t2
    exact isClosed_singleton.preimage ((continuous_restrictAb L.1 _).comp continuous_localArtinMap)
  have hdir : Directed (· ⊇ ·) t := by
    intro L₁ L₂
    have := L₁.2.1
    have := L₁.2.2
    have := L₂.2.1
    have := L₂.2.2
    have hab : IsAbelianGalois K (L₁.1 ⊔ L₂.1 : IntermediateField K Ω) :=
      isAbelianGalois_of_le_maximalAbelianExtension _ (sup_le (hle L₁) (hle L₂))
    refine ⟨⟨L₁.1 ⊔ L₂.1, inferInstance, hab⟩, ?_, ?_⟩
    · exact fun x hx => ⟨hx.1, fun y hy => hx.2 y (le_sup_left (b := L₂.1) hy)⟩
    · exact fun x hx => ⟨hx.1, fun y hy => hx.2 y (le_sup_right (a := L₁.1) hy)⟩
  have hnon : ∀ L, (t L).Nonempty := by
    intro L
    have := L.2.1
    have := L.2.2
    have hgL := hg L.1
    rw [← map_unitFiltrationUnits_restrictAb_localArtinMap L.1 n] at hgL
    obtain ⟨x, hxn, hxg⟩ := hgL
    refine ⟨x, ?_⟩
    rw [ht L]
    exact ⟨hxn, hxg⟩
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir hnon
    (fun L => by rw [ht L]; exact (isCompact_unitFiltrationUnits n).inter_right (hcl L))
    (fun L => by rw [ht L]; exact (isCompact_unitFiltrationUnits n).isClosed.inter (hcl L))
  rw [Set.mem_iInter] at hx
  obtain ⟨L₀⟩ := hι
  refine ⟨x, (hx L₀).1, ?_⟩
  refine AlgEquiv.ext fun y => Subtype.ext ?_
  obtain ⟨L, hfin, hab, hyL⟩ := exists_finite_abelian_mem y.2
  exact congrArg Subtype.val ((hx ⟨L, hfin, hab⟩).2 y hyL)

end Ab

end GroundTheory.LocalField
