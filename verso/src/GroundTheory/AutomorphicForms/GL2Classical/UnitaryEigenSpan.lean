import Mathlib

open scoped InnerProductSpace

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

variable {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module ℂ E]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section

variable (ρ : Representation ℂ G E) (ι : E →ₗ[ℂ] H) (T : Submodule ℂ E)

def orbitSum (K : Subgroup G) (v : E) (hv : (Set.range fun k : K => ρ k v).Finite) : E :=
  ∑ w ∈ hv.toFinset, w

variable {ρ}

/- English proof (translation)
Use `Submodule.sum_mem _ fun w hw => ?_` and prove the remaining obligations. Rewrite `hw` using `[Set.Finite.mem_toFinset]`. Take `⟨k, rfl⟩` from `hw`. Conclude with `hY _ _ hvY`.
-/
theorem orbitSum_mem {K : Subgroup G} {v : E} (hv : (Set.range fun k : K => ρ k v).Finite)
    {Y : Submodule ℂ E} (hY : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y) (hvY : v ∈ Y) : orbitSum ρ K v hv ∈ Y := by
  refine Submodule.sum_mem _ fun w hw => ?_
  rw [Set.Finite.mem_toFinset] at hw
  obtain ⟨k, rfl⟩ := hw
  exact hY _ _ hvY

/- English proof (translation)
Unfold `orbitSum`. Rewrite using `[map_sum]`. Use `Finset.sum_nbij' (fun w => ρ k w) (fun w => ρ (k⁻¹ : K) w) ?_ ?_ ?_ ?_ (fun _ _ => rfl)` and prove the remaining obligations. Introduce `w hw`. Simplify using `only [Set.Finite.mem_toFinset] at hw ⊢`.

Take `⟨k', rfl⟩` from `hw`. Conclude with `⟨k * k', by show ρ ((k * k' : K) : G) v = _; rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]⟩`. Introduce `w hw`. Simplify using `only [Set.Finite.mem_toFinset] at hw ⊢`. Take `⟨k', rfl⟩` from `hw`.

Conclude with `⟨k⁻¹ * k', by show ρ ((k⁻¹ * k' : K) : G) v = _; rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]⟩`. Introduce `w _`. Express the relevant statement in the definitionally equal form `ρ ((k⁻¹ : K) : G) (ρ k w) = w`. Rewrite using `[← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply]`. Introduce `w _`.

Express the relevant statement in the definitionally equal form `ρ (k : G) (ρ ((k⁻¹ : K) : G) w) = w`. Rewrite using `[← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, mul_inv_cancel, map_one, Module.End.one_apply]`.
-/
theorem orbitSum_fixed {K : Subgroup G} {v : E} (hv : (Set.range fun k : K => ρ k v).Finite)
    (k : K) : ρ k (orbitSum ρ K v hv) = orbitSum ρ K v hv := by
  unfold orbitSum
  rw [map_sum]
  refine Finset.sum_nbij' (fun w => ρ k w) (fun w => ρ (k⁻¹ : K) w) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro w hw
    simp only [Set.Finite.mem_toFinset] at hw ⊢
    obtain ⟨k', rfl⟩ := hw
    exact ⟨k * k', by show ρ ((k * k' : K) : G) v = _; rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]⟩
  · intro w hw
    simp only [Set.Finite.mem_toFinset] at hw ⊢
    obtain ⟨k', rfl⟩ := hw
    exact ⟨k⁻¹ * k', by show ρ ((k⁻¹ * k' : K) : G) v = _; rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]⟩
  · intro w _
    change ρ ((k⁻¹ : K) : G) (ρ k w) = w
    rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply]
  · intro w _
    change ρ (k : G) (ρ ((k⁻¹ : K) : G) w) = w
    rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, mul_inv_cancel, map_one, Module.End.one_apply]

/- English proof (translation)
The claim follows from `Finset.card_pos.2 ⟨v, by rw [Set.Finite.mem_toFinset]; exact ⟨1, by simp⟩⟩`.
-/
theorem card_orbit_pos {K : Subgroup G} {v : E} (hv : (Set.range fun k : K => ρ k v).Finite) :
    0 < hv.toFinset.card :=
  Finset.card_pos.2 ⟨v, by rw [Set.Finite.mem_toFinset]; exact ⟨1, by simp⟩⟩

end

variable {ρ : Representation ℂ G E} {ι : E →ₗ[ℂ] H} {T : Submodule ℂ E} {φ : E}

/- English proof (translation)
Establish `hφT : φ ∈ T` using `by rw [hT]; exact Submodule.subset_span ⟨1, by simp⟩`. Establish `hTg : ∀ g, ∀ v ∈ T, ρ g v ∈ T`. Introduce `g v hv`. Rewrite `hv`, the goal using `[hT]`. Proceed by induction on `hv using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨h, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨g * h, by show ρ (g * h) φ = _; rw [map_mul, Module.End.mul_apply]⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c hx`. Establish `hadj : ∀ g, ∀ v ∈ T, ∀ w ∈ T, ⟪ι v, ι (ρ g w)⟫_ℂ = ⟪ι (ρ g⁻¹ v), ι w⟫_ℂ`.

Introduce `g v hv w hw`. Rewrite using `[← hunit g⁻¹ v hv _ (hTg g w hw), ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Establish `havg : ∀ z ∈ T, (∀ k : K, ρ k z = z) → ∀ v (hv : v ∈ T), ⟪ι z, ι (orbitSum ρ K v (horb v hv))⟫_ℂ = ((horb v hv).toFinset.card : ℂ) * ⟪ι z, ι v⟫_ℂ`. Introduce `z hz hzK v hv`. Unfold `orbitSum`.

Rewrite using `[map_sum, inner_sum, ← nsmul_eq_mul, ← Finset.sum_const]`. Use `Finset.sum_congr rfl fun w hw => ?_` and prove the remaining obligations. Rewrite `hw` using `[Set.Finite.mem_toFinset]`. Take `⟨k, rfl⟩` from `hw`. Rewrite using `[hadj _ z hz v hv, ← Subgroup.coe_inv, hzK k⁻¹]`.

Take `⟨y, hyY, hy0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hY0`. Establish `hyT` using `hYT hyY`. Take `⟨g, hg⟩ : ∃ g : G, ⟪ι φ, ι (ρ g y)⟫_ℂ ≠ 0` from `by by_contra! hall`. Establish `horth : ∀ t ∈ T, ⟪ι t, ι y⟫_ℂ = 0`. Introduce `t ht`.

Rewrite `ht` using `[hT]`. Proceed by induction on `ht using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨h, rfl⟩` from `hx`. Use `hall h⁻¹` as an intermediate fact.

Rewrite `this` using `[hadj _ φ hφT y hyT, inv_inv]`. Conclude with `this`. Consider the case `zero => rw [map_zero, inner_zero_left]`. Consider the case `add x x' _ _ hx hx' => rw [map_add, inner_add_left, hx, hx', add_zero]`. Consider the case `smul c x _ hx => rw [map_smul, inner_smul_left, hx, mul_zero]`.

Conclude with `hy0 (hinj y hyT (inner_self_eq_zero.1 (horth y hyT)))`. Use `set y' := ρ g y`. Establish `hy'Y : y' ∈ Y` using `hY g y hyY`. Establish `hy'T : y' ∈ T` using `hYT hy'Y`. Use `set s := orbitSum ρ K y' (horb y' hy'T)`.

Establish `hsY : s ∈ Y` using `orbitSum_mem _ hY hy'Y`. Establish `hsK : ∀ k : K, ρ k s = s` using `orbitSum_fixed _`. Establish `hφs : ⟪ι φ, ι s⟫_ℂ ≠ 0`. Rewrite using `[havg φ hφT hφK y' hy'T]`. Conclude with `mul_ne_zero (Nat.cast_ne_zero.2 (card_orbit_pos _).ne') hg`.

Use `set M : Submodule ℂ E := Y ⊓ (T ⊓ Representation.invariants (ρ.comp K.subtype))`. Establish `hMfd : FiniteDimensional ℂ M` using `Submodule.finiteDimensional_of_le (inf_le_right : M ≤ T ⊓ Representation.invariants (ρ.comp K.subtype))`. Use `set Mι : Submodule ℂ H := M.map ι`. Establish `hMιfd : FiniteDimensional ℂ Mι` using `inferInstance`. Use `haveI : CompleteSpace Mι := FiniteDimensional.complete ℂ Mι`.

Take `⟨u, huM, w, hw, hφw⟩` from `Mι.exists_add_mem_mem_orthogonal (ι φ)`. Take `⟨m, hmM, hmP⟩` from `Submodule.mem_map.1 huM`. Establish `hmY : m ∈ Y` using `hmM.1`. Establish `hmT : m ∈ T` using `hmM.2.1`. Establish `hmK : ∀ k : K, ρ k m = m` using `fun k => hmM.2.2 k`.

Use `set z := φ - m`. Establish `hzT : z ∈ T` using `sub_mem hφT hmT`. Establish `hzK : ∀ k : K, ρ k z = z` using `fun k => by rw [map_sub, hφK, hmK]`. Establish `hzι : ι z ∈ Mιᗮ`. Rewrite using `[map_sub, hmP, hφw, add_sub_cancel_left]`.

Conclude with `hw`. Establish `hzY : ∀ v ∈ Y, ⟪ι z, ι v⟫_ℂ = 0`. Introduce `v hvY`. Establish `hvT` using `hYT hvY`. Establish `hsv : orbitSum ρ K v (horb v hvT) ∈ M` using `⟨orbitSum_mem _ hY hvY, orbitSum_mem _ hTg hvT, fun k => orbitSum_fixed _ k⟩`.

Establish `h0 : ⟪ι z, ι (orbitSum ρ K v (horb v hvT))⟫_ℂ = 0` using `Submodule.inner_left_of_mem_orthogonal (Submodule.mem_map_of_mem hsv) hzι`. Rewrite `h0` using `[havg z hzT hzK v hvT]`. Conclude with `(mul_eq_zero.1 h0).resolve_left (Nat.cast_ne_zero.2 (card_orbit_pos _).ne')`. Establish `hzE : ∀ j, ∑ g ∈ S j, ρ g z = ev j • z`. Introduce `j`.

Use `set D := ∑ g ∈ S j, ρ g z - ev j • z`. Establish `hDY : D ∈ Y`. Establish `e : D = -(∑ g ∈ S j, ρ g m - ev j • m)`. Simplify using `only [D, z, map_sub, Finset.sum_sub_distrib, hφS, smul_sub]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e]`. Conclude with `neg_mem (sub_mem (Submodule.sum_mem _ fun g _ => hY g m hmY) (Submodule.smul_mem _ _ hmY))`. Establish `hDT` using `hYT hDY`. Establish `hDorth : ∀ v ∈ Y, ⟪ι D, ι v⟫_ℂ = 0`. Introduce `v hvY`.

Establish `hvT` using `hYT hvY`. Simplify using `only [D, map_sub, map_sum, map_smul, inner_sub_left, sum_inner, inner_smul_left, hzY v hvY, mul_zero, sub_zero]`. Use `Finset.sum_eq_zero fun g _ => ?_` and prove the remaining obligations. Rewrite using `[← hunit g⁻¹ _ (hTg g z hzT) v hvT, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Conclude with `hzY _ (hY _ _ hvY)`.

Use `hinj D hDT (inner_self_eq_zero.1 (hDorth D hDY))` as an intermediate fact. Conclude with `sub_eq_zero.1 this`. Take `⟨c, hc⟩` from `hP z hzT hzK hzE`. Establish `hzs` using `hzY s hsY`. Rewrite `hzs` using `[hc, map_smul, inner_smul_left]`.

Establish `hc0 : c = 0`. Use `(mul_eq_zero.1 hzs).resolve_right hφs` as an intermediate fact. Simplify using `using this`. Establish `hz0 : z = 0` using `by rw [hc, hc0, zero_smul]`. Establish `: φ = m` using `sub_eq_zero.1 hz0`.

Rewrite using `[this]`. Conclude with `hmY`.
-/
theorem mem_of_stable_of_eigen
    (hT : T = Submodule.span ℂ (Set.range fun g : G => ρ g φ))
    (hinj : ∀ v ∈ T, ι v = 0 → v = 0)
    (hunit : ∀ g : G, ∀ v ∈ T, ∀ w ∈ T, ⟪ι (ρ g v), ι (ρ g w)⟫_ℂ = ⟪ι v, ι w⟫_ℂ)
    (K : Subgroup G) (hφK : ∀ k : K, ρ k φ = φ)
    (horb : ∀ v ∈ T, (Set.range fun k : K => ρ k v).Finite)
    (hfd : FiniteDimensional ℂ ↥(T ⊓ Representation.invariants (ρ.comp K.subtype)))
    {J : Type*} (S : J → Finset G) (ev : J → ℂ) (hφS : ∀ j, ∑ g ∈ S j, ρ g φ = ev j • φ)
    (hP : ∀ z ∈ T, (∀ k : K, ρ k z = z) → (∀ j, ∑ g ∈ S j, ρ g z = ev j • z) → ∃ c : ℂ, z = c • φ)
    (Y : Submodule ℂ E) (hYT : Y ≤ T) (hY : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y) (hY0 : Y ≠ ⊥) : φ ∈ Y := by
  have hφT : φ ∈ T := by rw [hT]; exact Submodule.subset_span ⟨1, by simp⟩
  have hTg : ∀ g, ∀ v ∈ T, ρ g v ∈ T := by
    intro g v hv
    rw [hT] at hv ⊢
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      exact Submodule.subset_span ⟨g * h, by show ρ (g * h) φ = _; rw [map_mul, Module.End.mul_apply]⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

  have hadj : ∀ g, ∀ v ∈ T, ∀ w ∈ T, ⟪ι v, ι (ρ g w)⟫_ℂ = ⟪ι (ρ g⁻¹ v), ι w⟫_ℂ := by
    intro g v hv w hw
    rw [← hunit g⁻¹ v hv _ (hTg g w hw), ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]

  have havg : ∀ z ∈ T, (∀ k : K, ρ k z = z) → ∀ v (hv : v ∈ T),
      ⟪ι z, ι (orbitSum ρ K v (horb v hv))⟫_ℂ = ((horb v hv).toFinset.card : ℂ) * ⟪ι z, ι v⟫_ℂ := by
    intro z hz hzK v hv
    unfold orbitSum
    rw [map_sum, inner_sum, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [Set.Finite.mem_toFinset] at hw
    obtain ⟨k, rfl⟩ := hw
    rw [hadj _ z hz v hv, ← Subgroup.coe_inv, hzK k⁻¹]

  obtain ⟨y, hyY, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY0
  have hyT := hYT hyY
  obtain ⟨g, hg⟩ : ∃ g : G, ⟪ι φ, ι (ρ g y)⟫_ℂ ≠ 0 := by
    by_contra! hall
    have horth : ∀ t ∈ T, ⟪ι t, ι y⟫_ℂ = 0 := by
      intro t ht
      rw [hT] at ht
      induction ht using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨h, rfl⟩ := hx
        have := hall h⁻¹
        rw [hadj _ φ hφT y hyT, inv_inv] at this
        exact this
      | zero => rw [map_zero, inner_zero_left]
      | add x x' _ _ hx hx' => rw [map_add, inner_add_left, hx, hx', add_zero]
      | smul c x _ hx => rw [map_smul, inner_smul_left, hx, mul_zero]
    exact hy0 (hinj y hyT (inner_self_eq_zero.1 (horth y hyT)))
  set y' := ρ g y
  have hy'Y : y' ∈ Y := hY g y hyY
  have hy'T : y' ∈ T := hYT hy'Y
  set s := orbitSum ρ K y' (horb y' hy'T)
  have hsY : s ∈ Y := orbitSum_mem _ hY hy'Y
  have hsK : ∀ k : K, ρ k s = s := orbitSum_fixed _
  have hφs : ⟪ι φ, ι s⟫_ℂ ≠ 0 := by
    rw [havg φ hφT hφK y' hy'T]
    exact mul_ne_zero (Nat.cast_ne_zero.2 (card_orbit_pos _).ne') hg

  set M : Submodule ℂ E := Y ⊓ (T ⊓ Representation.invariants (ρ.comp K.subtype))
  have hMfd : FiniteDimensional ℂ M :=
    Submodule.finiteDimensional_of_le (inf_le_right : M ≤ T ⊓ Representation.invariants (ρ.comp K.subtype))
  set Mι : Submodule ℂ H := M.map ι
  have hMιfd : FiniteDimensional ℂ Mι := inferInstance
  haveI : CompleteSpace Mι := FiniteDimensional.complete ℂ Mι
  obtain ⟨u, huM, w, hw, hφw⟩ := Mι.exists_add_mem_mem_orthogonal (ι φ)
  obtain ⟨m, hmM, hmP⟩ := Submodule.mem_map.1 huM
  have hmY : m ∈ Y := hmM.1
  have hmT : m ∈ T := hmM.2.1
  have hmK : ∀ k : K, ρ k m = m := fun k => hmM.2.2 k
  set z := φ - m
  have hzT : z ∈ T := sub_mem hφT hmT
  have hzK : ∀ k : K, ρ k z = z := fun k => by rw [map_sub, hφK, hmK]
  have hzι : ι z ∈ Mιᗮ := by
    rw [map_sub, hmP, hφw, add_sub_cancel_left]
    exact hw

  have hzY : ∀ v ∈ Y, ⟪ι z, ι v⟫_ℂ = 0 := by
    intro v hvY
    have hvT := hYT hvY
    have hsv : orbitSum ρ K v (horb v hvT) ∈ M :=
      ⟨orbitSum_mem _ hY hvY, orbitSum_mem _ hTg hvT, fun k => orbitSum_fixed _ k⟩
    have h0 : ⟪ι z, ι (orbitSum ρ K v (horb v hvT))⟫_ℂ = 0 :=
      Submodule.inner_left_of_mem_orthogonal (Submodule.mem_map_of_mem hsv) hzι
    rw [havg z hzT hzK v hvT] at h0
    exact (mul_eq_zero.1 h0).resolve_left (Nat.cast_ne_zero.2 (card_orbit_pos _).ne')

  have hzE : ∀ j, ∑ g ∈ S j, ρ g z = ev j • z := by
    intro j
    set D := ∑ g ∈ S j, ρ g z - ev j • z
    have hDY : D ∈ Y := by
      have e : D = -(∑ g ∈ S j, ρ g m - ev j • m) := by
        simp only [D, z, map_sub, Finset.sum_sub_distrib, hφS, smul_sub]
        abel
      rw [e]
      exact neg_mem (sub_mem (Submodule.sum_mem _ fun g _ => hY g m hmY) (Submodule.smul_mem _ _ hmY))
    have hDT := hYT hDY
    have hDorth : ∀ v ∈ Y, ⟪ι D, ι v⟫_ℂ = 0 := by
      intro v hvY
      have hvT := hYT hvY
      simp only [D, map_sub, map_sum, map_smul, inner_sub_left, sum_inner, inner_smul_left, hzY v hvY,
        mul_zero, sub_zero]
      refine Finset.sum_eq_zero fun g _ => ?_
      rw [← hunit g⁻¹ _ (hTg g z hzT) v hvT, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
      exact hzY _ (hY _ _ hvY)
    have := hinj D hDT (inner_self_eq_zero.1 (hDorth D hDY))
    exact sub_eq_zero.1 this

  obtain ⟨c, hc⟩ := hP z hzT hzK hzE
  have hzs := hzY s hsY
  rw [hc, map_smul, inner_smul_left] at hzs
  have hc0 : c = 0 := by
    have := (mul_eq_zero.1 hzs).resolve_right hφs
    simpa using this
  have hz0 : z = 0 := by rw [hc, hc0, zero_smul]
  have : φ = m := sub_eq_zero.1 hz0
  rw [this]
  exact hmY

end GL2Classical

end

end GroundTheory.Automorphic
