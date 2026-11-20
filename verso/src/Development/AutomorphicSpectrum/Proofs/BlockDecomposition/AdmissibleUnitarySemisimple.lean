import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OrbitFinite
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.UnitSemisimple

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty`. Introduce `v`. Use `⟨0, zero_mem _, fun s hs => ?_⟩` and prove the remaining obligations. Establish `: s = 0` using `by simpa using hs`.

Simplify using `[this]`. Consider the case `insert a t _ ih`. Introduce `v`. Take `⟨w₁, hw₁, h₁⟩` from `ih v`. Take `⟨a₁, ha₁, h₂⟩` from `ih a`.

Establish `hle : Submodule.span ℂ (t : Set V) ≤ Submodule.span ℂ ((insert a t : Finset V) : Set V)` using `Submodule.span_mono (by simp)`. Establish `ha : a ∈ Submodule.span ℂ ((insert a t : Finset V) : Set V)` using `Submodule.subset_span (by simp)`. Take `⟨x, hx⟩ : ∃ x, x = a - a₁` from `⟨_, rfl⟩`. Take `⟨u, hu⟩ : ∃ u, u = v - w₁` from `⟨_, rfl⟩`. Take `⟨c, hcdef⟩ : ∃ c, c = B u x / B x x` from `⟨_, rfl⟩`.

Establish `hc : B u x = c * B x x`. Distinguish the cases in `hx0 : x = 0`. Simplify using `[hx0]`. Establish `h0 : B x x ≠ 0` using `fun h => by simpa [h] using hp x hx0`. Rewrite using `[hcdef]`.

Clear the denominators using the available nonvanishing facts. Use `⟨w₁ + c • x, ?_, ?_⟩` and prove the remaining obligations. Use `add_mem (hle hw₁) (Submodule.smul_mem _ _ ?_)` and prove the remaining obligations. Rewrite using `[hx]`. Conclude with `sub_mem ha (hle ha₁)`.

Introduce `s hs`. Rewrite `hs` using `[Finset.coe_insert]`. Take `⟨b, z, hz, rfl⟩` from `Submodule.mem_span_insert.1 hs`. Establish `hz' : b • a₁ + z ∈ Submodule.span ℂ (t : Set V)` using `add_mem (Submodule.smul_mem _ _ ha₁) hz`. Establish `e1 : v - (w₁ + c • x) = u - c • x` using `by rw [hu]; abel`.

Establish `e2 : b • a + z = b • x + (b • a₁ + z)` using `by rw [hx, smul_sub]; abel`. Establish `k1 : B u (b • a₁ + z) = 0` using `by rw [hu]; exact h₁ _ hz'`. Establish `k2 : B x (b • a₁ + z) = 0` using `by rw [hx]; exact h₂ _ hz'`. Rewrite using `[e1, e2, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, (B u).map_add (b • x), (B x).map_add (b • x), k1, k2, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, hc]`. Simplify using `only [smul_eq_mul, add_zero]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_proj_finset (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hp : ∀ v, v ≠ 0 → 0 < (B v v).re) (t : Finset V) :
    ∀ v : V, ∃ w ∈ Submodule.span ℂ (t : Set V),
      ∀ s ∈ Submodule.span ℂ (t : Set V), B (v - w) s = 0 := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro v
    refine ⟨0, zero_mem _, fun s hs => ?_⟩
    have : s = 0 := by simpa using hs
    simp [this]
  | insert a t _ ih =>
    intro v
    obtain ⟨w₁, hw₁, h₁⟩ := ih v
    obtain ⟨a₁, ha₁, h₂⟩ := ih a
    have hle : Submodule.span ℂ (t : Set V) ≤ Submodule.span ℂ ((insert a t : Finset V) : Set V) :=
      Submodule.span_mono (by simp)
    have ha : a ∈ Submodule.span ℂ ((insert a t : Finset V) : Set V) :=
      Submodule.subset_span (by simp)
    obtain ⟨x, hx⟩ : ∃ x, x = a - a₁ := ⟨_, rfl⟩
    obtain ⟨u, hu⟩ : ∃ u, u = v - w₁ := ⟨_, rfl⟩
    obtain ⟨c, hcdef⟩ : ∃ c, c = B u x / B x x := ⟨_, rfl⟩
    have hc : B u x = c * B x x := by
      by_cases hx0 : x = 0
      · simp [hx0]
      · have h0 : B x x ≠ 0 := fun h => by simpa [h] using hp x hx0
        rw [hcdef]; field_simp
    refine ⟨w₁ + c • x, ?_, ?_⟩
    · refine add_mem (hle hw₁) (Submodule.smul_mem _ _ ?_)
      rw [hx]; exact sub_mem ha (hle ha₁)
    · intro s hs
      rw [Finset.coe_insert] at hs
      obtain ⟨b, z, hz, rfl⟩ := Submodule.mem_span_insert.1 hs
      have hz' : b • a₁ + z ∈ Submodule.span ℂ (t : Set V) :=
        add_mem (Submodule.smul_mem _ _ ha₁) hz
      have e1 : v - (w₁ + c • x) = u - c • x := by rw [hu]; abel
      have e2 : b • a + z = b • x + (b • a₁ + z) := by rw [hx, smul_sub]; abel
      have k1 : B u (b • a₁ + z) = 0 := by rw [hu]; exact h₁ _ hz'
      have k2 : B x (b • a₁ + z) = 0 := by rw [hx]; exact h₂ _ hz'
      rw [e1, e2, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
        (B u).map_add (b • x), (B x).map_add (b • x),
        k1, k2, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, hc]
      simp only [smul_eq_mul, add_zero]
      ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h k hk`. Simplify using `using h ⟨k, hk⟩`. Introduce `h k`. Simplify using `using h k k.2`.
-/
theorem mem_fixed_iff {G : Type} [Group G] (ρ : Representation ℂ G V) (K : Subgroup G) (v : V) :
    v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v := by
  constructor
  · intro h k hk
    simpa using h ⟨k, hk⟩
  · intro h k
    simpa using h k k.2

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qf32.orbit_finite ρ K hK w hS`.
-/
theorem orbit_finite {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (ρ : Representation ℂ G V) (K : Subgroup G) (hK : IsCompact (K : Set G)) (w : V)
    (hS : IsOpen {g : G | ρ g w = w}) : {x : V | ∃ k ∈ K, ρ k w = x}.Finite :=
  _root_.UpperTheory.Reformulated.B.Qf32.orbit_finite ρ K hK w hS

/- English proof (translation)
Establish `hO` using `orbit_finite ρ K hK w hS`. Use `set O : Finset V := hO.toFinset with hOdef`. Establish `hmem : ∀ x, x ∈ O ↔ ∃ k ∈ K, ρ k w = x` using `fun x => by simp [hOdef]`. Establish `hinv : ∀ k ∈ K, ∀ x, ρ k⁻¹ (ρ k x) = x` using `fun k _ x => by`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`.

Simplify using the standard rewrite rules. Establish `hinv' : ∀ k ∈ K, ∀ x, ρ k (ρ k⁻¹ x) = x` using `fun k _ x => by`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Simplify using the standard rewrite rules. Establish `hst : ∀ k ∈ K, ∀ x ∈ O, ρ k x ∈ O`.

Introduce `k hk x hx`. Take `⟨l, hl, rfl⟩` from `(hmem x).1 hx`. Use `(hmem _).2 ⟨k * l, K.mul_mem hk hl, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, Module.End.mul_apply]`. Establish `hsW : ∑ x ∈ O, x ∈ W.toSubmodule`.

Use `Submodule.sum_mem _ fun x hx => ?_` and prove the remaining obligations. Take `⟨l, _, rfl⟩` from `(hmem x).1 hx`. Conclude with `W.apply_mem_toSubmodule l hw`. Establish `hsF : ∑ x ∈ O, x ∈ fixed ρ K`. Rewrite using `[mem_fixed_iff]`.

Introduce `k hk`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_nbij' (ρ k) (ρ k⁻¹) (fun x hx => hst k hk x hx) (fun x hx => hst _ (K.inv_mem hk) x hx) (fun x _ => hinv k hk x) (fun x _ => hinv' k hk x) (fun x _ => rfl)`. Establish `h0` using `huW _ ⟨hsW, hsF⟩`. Establish `hterm : ∀ x ∈ O, B u x = B u w`.

Introduce `x hx`. Take `⟨l, hl, rfl⟩` from `(hmem x).1 hx`. Use `conv_lhs => rw [← hu l hl]`. Conclude with `hi l u w`. Rewrite `h0` using `[map_sum, Finset.sum_congr rfl hterm, Finset.sum_const]`.

Establish `hne : O.card ≠ 0` using `Finset.card_ne_zero.2 ⟨w, (hmem w).2 ⟨1, K.one_mem, by simp⟩⟩`. Rewrite `h0` using `[nsmul_eq_mul]`. Conclude with `(mul_eq_zero.1 h0).resolve_left (by exact_mod_cast hne)`.
-/
theorem orthogonal_of_fixed {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (ρ : Representation ℂ G V) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hi : ∀ g v w, B (ρ g v) (ρ g w) = B v w) (K : Subgroup G) (hK : IsCompact (K : Set G))
    (W : Subrepresentation ρ) (u : V) (hu : ∀ k ∈ K, ρ k u = u)
    (huW : ∀ s ∈ W.toSubmodule ⊓ fixed ρ K, B u s = 0)
    (w : V) (hw : w ∈ W.toSubmodule) (hS : IsOpen {g : G | ρ g w = w}) : B u w = 0 := by
  classical
  have hO := orbit_finite ρ K hK w hS
  set O : Finset V := hO.toFinset with hOdef
  have hmem : ∀ x, x ∈ O ↔ ∃ k ∈ K, ρ k w = x := fun x => by simp [hOdef]
  have hinv : ∀ k ∈ K, ∀ x, ρ k⁻¹ (ρ k x) = x := fun k _ x => by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  have hinv' : ∀ k ∈ K, ∀ x, ρ k (ρ k⁻¹ x) = x := fun k _ x => by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  have hst : ∀ k ∈ K, ∀ x ∈ O, ρ k x ∈ O := by
    intro k hk x hx
    obtain ⟨l, hl, rfl⟩ := (hmem x).1 hx
    refine (hmem _).2 ⟨k * l, K.mul_mem hk hl, ?_⟩
    rw [map_mul, Module.End.mul_apply]
  have hsW : ∑ x ∈ O, x ∈ W.toSubmodule := by
    refine Submodule.sum_mem _ fun x hx => ?_
    obtain ⟨l, _, rfl⟩ := (hmem x).1 hx
    exact W.apply_mem_toSubmodule l hw
  have hsF : ∑ x ∈ O, x ∈ fixed ρ K := by
    rw [mem_fixed_iff]
    intro k hk
    rw [map_sum]
    exact Finset.sum_nbij' (ρ k) (ρ k⁻¹) (fun x hx => hst k hk x hx)
      (fun x hx => hst _ (K.inv_mem hk) x hx) (fun x _ => hinv k hk x) (fun x _ => hinv' k hk x)
      (fun x _ => rfl)
  have h0 := huW _ ⟨hsW, hsF⟩
  have hterm : ∀ x ∈ O, B u x = B u w := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := (hmem x).1 hx
    conv_lhs => rw [← hu l hl]
    exact hi l u w
  rw [map_sum, Finset.sum_congr rfl hterm, Finset.sum_const] at h0
  have hne : O.card ≠ 0 := Finset.card_ne_zero.2 ⟨w, (hmem w).2 ⟨1, K.one_mem, by simp⟩⟩
  rw [nsmul_eq_mul] at h0
  exact (mul_eq_zero.1 h0).resolve_left (by exact_mod_cast hne)

def orth {G : Type} [Group G] (ρ : Representation ℂ G V) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hi : ∀ g v w, B (ρ g v) (ρ g w) = B v w) (W : Subrepresentation ρ) : Subrepresentation ρ where
  toSubmodule :=
    { carrier := {v | ∀ w ∈ W.toSubmodule, B v w = 0}
      add_mem' := fun {a b} ha hb w hw => by simp [ha w hw, hb w hw]
      zero_mem' := fun w _ => by simp
      smul_mem' := fun c v hv w hw => by simp [hv w hw] }
  apply_mem_toSubmodule := by
    intro g v hv w hw
    have e : ρ g (ρ g⁻¹ w) = w := by
      rw [← Module.End.mul_apply, ← map_mul]; simp
    have := hv _ (W.apply_mem_toSubmodule g⁻¹ hw)
    rw [← e, hi]; exact this

/- English proof (translation)
Introduce `G V _ _ _ _ _ ρ hbasis hadm hun W`. Take `⟨B, hh, hp, hi⟩` from `hun`. Use `⟨orth ρ B hi W, IsCompl.of_eq ?_ ?_⟩` and prove the remaining obligations. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Rewrite using `[Subrepresentation.toSubmodule_inf]`.

Use `(Submodule.eq_bot_iff _).2 fun v hv => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hv0`. Establish `h0 : B v v = 0` using `hv.2 v hv.1`. Simplify `hp v hv0` using `[h0]`. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises.

Rewrite using `[Subrepresentation.toSubmodule_sup]`. Use `(Submodule.eq_top_iff').2 fun v => ?_` and prove the remaining obligations. Take `⟨K, hKo, hKc, hKv⟩` from `hbasis {g | ρ g v = v} ((hadm.1 v).mem_nhds (by simp))`. Establish `hfd : FiniteDimensional ℂ (fixed ρ K)` using `hadm.2 K hKo hKc`. Establish `hfd' : FiniteDimensional ℂ (W.toSubmodule ⊓ fixed ρ K : Submodule ℂ V)` using `Submodule.finiteDimensional_inf_right _ _`.

Establish `hfg : (W.toSubmodule ⊓ fixed ρ K).FG` using `Module.Finite.iff_fg.1 hfd'`. Take `⟨t, ht⟩` from `hfg`. Take `⟨w, hw, hort⟩` from `exists_proj_finset B hp t v`. Rewrite `hw`, `hort` using `[ht]`. Establish `hfix : ∀ k ∈ K, ρ k (v - w) = v - w`.

Introduce `k hk`. Establish `h1 : ρ k v = v` using `hKv hk`. Establish `h2 : ρ k w = w` using `(mem_fixed_iff ρ K w).1 hw.2 k hk`. Rewrite using `[map_sub, h1, h2]`. Establish `hmem : v - w ∈ (orth ρ B hi W).toSubmodule` using `fun y hy => orthogonal_of_fixed ρ B hi K hKc W (v - w) hfix hort y hy (hadm.1 y)`.

Establish `: v = w + (v - w)` using `by abel`. Rewrite using `[this]`. Conclude with `Submodule.add_mem_sup hw.1 hmem`.
-/
theorem exists_isCompl : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → IsAdmissible ρ → IsUnitarisable ρ → ∀ W : Subrepresentation ρ, ∃ W' : Subrepresentation ρ, IsCompl W W' := by
  intro G V _ _ _ _ _ ρ hbasis hadm hun W
  obtain ⟨B, hh, hp, hi⟩ := hun
  refine ⟨orth ρ B hi W, IsCompl.of_eq ?_ ?_⟩
  · apply Subrepresentation.toSubmodule_injective
    rw [Subrepresentation.toSubmodule_inf]
    refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
    by_contra hv0
    have h0 : B v v = 0 := hv.2 v hv.1
    simpa [h0] using hp v hv0
  · apply Subrepresentation.toSubmodule_injective
    rw [Subrepresentation.toSubmodule_sup]
    refine (Submodule.eq_top_iff').2 fun v => ?_
    obtain ⟨K, hKo, hKc, hKv⟩ := hbasis {g | ρ g v = v} ((hadm.1 v).mem_nhds (by simp))
    have hfd : FiniteDimensional ℂ (fixed ρ K) := hadm.2 K hKo hKc
    have hfd' : FiniteDimensional ℂ (W.toSubmodule ⊓ fixed ρ K : Submodule ℂ V) :=
      Submodule.finiteDimensional_inf_right _ _
    have hfg : (W.toSubmodule ⊓ fixed ρ K).FG := Module.Finite.iff_fg.1 hfd'
    obtain ⟨t, ht⟩ := hfg
    obtain ⟨w, hw, hort⟩ := exists_proj_finset B hp t v
    rw [ht] at hw hort
    have hfix : ∀ k ∈ K, ρ k (v - w) = v - w := by
      intro k hk
      have h1 : ρ k v = v := hKv hk
      have h2 : ρ k w = w := (mem_fixed_iff ρ K w).1 hw.2 k hk
      rw [map_sub, h1, h2]
    have hmem : v - w ∈ (orth ρ B hi W).toSubmodule := fun y hy =>
      orthogonal_of_fixed ρ B hi K hKc W (v - w) hfix hort y hy (hadm.1 y)
    have : v = w + (v - w) := by abel
    rw [this]
    exact Submodule.add_mem_sup hw.1 hmem

end GlobalTheory.CompanionTheory.UnitSemisimple
