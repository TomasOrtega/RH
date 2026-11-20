import Formalism.SharpRestriction.GrowthBounds.RootWeights.EquivariantInjectiveOfCyclic

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

/- English proof (translation)
Establish `hP` using `prodRepresentation_isRep E E hE hE`. Establish `hg : IsHWV (prodRepresentation E E) lam (v0, v)`. Use `⟨fun h => hv0.1 (congrArg Prod.fst h), (prod_mem_weightSpace_iff E E lam _).2 ⟨hv0.2.1, hv.2.1⟩, fun a b hab => ?_⟩` and prove the remaining obligations. Rewrite using `[prodRepresentation_apply, hv0.2.2 a b hab, hv.2.2 a b hab]`. Both sides reduce to the same expression.

Establish `hΓ` using `cyclicSubmodule_isSubrepresentation (prodRepresentation E E) (v0, v)`. Establish `hEΓ` using `restrictRepresentation_isRep (prodRepresentation E E) hP _ hΓ`. Establish `hg'` using `highest_vector_restrict (prodRepresentation E E) _ hΓ lam (v0, v) (self_mem_cyclicSubmodule _ _) hg`. Establish `hcyc` using `cyclicSubmodule_restrict_eq_top (prodRepresentation E E) (v0, v) hΓ`. Set `F : cyclicSubmodule (prodRepresentation E E) (v0, v) →ₗ[K] V` to `(LinearMap.fst K V V) ∘ₗ (Submodule.subtype _)`.

Set `S2 : cyclicSubmodule (prodRepresentation E E) (v0, v) →ₗ[K] V` to `(LinearMap.snd K V V) ∘ₗ (Submodule.subtype _)`. Establish `hF : IsEquivariantMap (restrictRepresentation (prodRepresentation E E) _ hΓ) E F` using `fun a b x => rfl`. Establish `hS : IsEquivariantMap (restrictRepresentation (prodRepresentation E E) _ hΓ) E S2` using `fun a b x => rfl`. Establish `hker` using `equivariant_injective_of_cyclic D h2 _ hEΓ E lam _ hg' hcyc F hF hv0.1`. Establish `hinj : Function.Injective F` using `LinearMap.ker_eq_bot.1 hker`.

Establish `hrange : LinearMap.range F = cyclicSubmodule E v0`. Use `equivariant_map_cyclicSubmodule _ E F hF ⟨(v0, v), self_mem_cyclicSubmodule _ _⟩` as an intermediate fact. Rewrite `this` using `[hcyc, Submodule.map_top]`. Conclude with `this`. Establish `hmem : ∀ z, F z ∈ cyclicSubmodule E v0` using `fun z => by rw [← hrange]; exact ⟨z, rfl⟩`.

Set `e : cyclicSubmodule (prodRepresentation E E) (v0, v) ≃ₗ[K] cyclicSubmodule E v0` to `LinearEquiv.ofBijective (F.codRestrict _ hmem) ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), fun y => by`. Establish `hy : (y : V) ∈ LinearMap.range F` using `by rw [hrange]; exact y.2`. Take `⟨z, hz⟩` from `hy`. Conclude with `⟨z, Subtype.ext hz⟩⟩`. Establish `he : ∀ z, ((e z : cyclicSubmodule E v0) : V) = F z` using `fun z => rfl`.

Use `⟨S2 ∘ₗ e.symm.toLinearMap, fun a b y => ?_, ?_⟩` and prove the remaining obligations. Take `⟨z, rfl⟩` from `e.surjective y`. Establish `h1 : restrictRepresentation E _ hL a b (e z) = e (restrictRepresentation (prodRepresentation E E) _ hΓ a b z)` using `Subtype.ext rfl`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[h1, e.symm_apply_apply, e.symm_apply_apply]`.

Conclude with `hS a b z`. Establish `h1 : (⟨v0, self_mem_cyclicSubmodule E v0⟩ : cyclicSubmodule E v0) = e ⟨(v0, v), self_mem_cyclicSubmodule _ _⟩` using `Subtype.ext rfl`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[h1, e.symm_apply_apply]`. Both sides reduce to the same expression.
-/
theorem exists_equivariant_cyclic_to_hwv (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {n : ℕ} {K V : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (E : GLOps n K V) (hE : IsGLRep E) (lam : Fin n → ℤ)
    (v0 v : V) (hv0 : IsHWV E lam v0) (hv : IsHWV E lam v) (hL : IsSubrepresentation E (cyclicSubmodule E v0)) :
    ∃ φ : cyclicSubmodule E v0 →ₗ[K] V, IsEquivariantMap (restrictRepresentation E _ hL) E φ ∧ φ ⟨v0, self_mem_cyclicSubmodule E v0⟩ = v := by
  have hP := prodRepresentation_isRep E E hE hE
  have hg : IsHWV (prodRepresentation E E) lam (v0, v) := by
    refine ⟨fun h => hv0.1 (congrArg Prod.fst h), (prod_mem_weightSpace_iff E E lam _).2 ⟨hv0.2.1, hv.2.1⟩, fun a b hab => ?_⟩
    rw [prodRepresentation_apply, hv0.2.2 a b hab, hv.2.2 a b hab]; rfl
  have hΓ := cyclicSubmodule_isSubrepresentation (prodRepresentation E E) (v0, v)
  have hEΓ := restrictRepresentation_isRep (prodRepresentation E E) hP _ hΓ
  have hg' := highest_vector_restrict (prodRepresentation E E) _ hΓ lam (v0, v) (self_mem_cyclicSubmodule _ _) hg
  have hcyc := cyclicSubmodule_restrict_eq_top (prodRepresentation E E) (v0, v) hΓ
  let F : cyclicSubmodule (prodRepresentation E E) (v0, v) →ₗ[K] V := (LinearMap.fst K V V) ∘ₗ (Submodule.subtype _)
  let S2 : cyclicSubmodule (prodRepresentation E E) (v0, v) →ₗ[K] V := (LinearMap.snd K V V) ∘ₗ (Submodule.subtype _)
  have hF : IsEquivariantMap (restrictRepresentation (prodRepresentation E E) _ hΓ) E F := fun a b x => rfl
  have hS : IsEquivariantMap (restrictRepresentation (prodRepresentation E E) _ hΓ) E S2 := fun a b x => rfl
  have hker := equivariant_injective_of_cyclic D h2 _ hEΓ E lam _ hg' hcyc F hF hv0.1
  have hinj : Function.Injective F := LinearMap.ker_eq_bot.1 hker
  have hrange : LinearMap.range F = cyclicSubmodule E v0 := by
    have := equivariant_map_cyclicSubmodule _ E F hF ⟨(v0, v), self_mem_cyclicSubmodule _ _⟩
    rw [hcyc, Submodule.map_top] at this
    exact this
  have hmem : ∀ z, F z ∈ cyclicSubmodule E v0 := fun z => by rw [← hrange]; exact ⟨z, rfl⟩
  let e : cyclicSubmodule (prodRepresentation E E) (v0, v) ≃ₗ[K] cyclicSubmodule E v0 :=
    LinearEquiv.ofBijective (F.codRestrict _ hmem)
      ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), fun y => by
        have hy : (y : V) ∈ LinearMap.range F := by rw [hrange]; exact y.2
        obtain ⟨z, hz⟩ := hy
        exact ⟨z, Subtype.ext hz⟩⟩
  have he : ∀ z, ((e z : cyclicSubmodule E v0) : V) = F z := fun z => rfl
  refine ⟨S2 ∘ₗ e.symm.toLinearMap, fun a b y => ?_, ?_⟩
  · obtain ⟨z, rfl⟩ := e.surjective y
    have h1 : restrictRepresentation E _ hL a b (e z) = e (restrictRepresentation (prodRepresentation E E) _ hΓ a b z) := Subtype.ext rfl
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [h1, e.symm_apply_apply, e.symm_apply_apply]
    exact hS a b z
  · have h1 : (⟨v0, self_mem_cyclicSubmodule E v0⟩ : cyclicSubmodule E v0) = e ⟨(v0, v), self_mem_cyclicSubmodule _ _⟩ := Subtype.ext rfl
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [h1, e.symm_apply_apply]
    rfl

def trivialRepresentation (n : ℕ) (K : Type) [Field K] : GLOps n K K := fun _ _ => 0

/- English proof (translation)
Use `⟨?_, fun x => ⟨⊤, inferInstance, trivial, fun _ _ _ _ => trivial⟩, ?_⟩` and prove the remaining obligations. Introduce `a b c d`. Simplify using `only [trivialRepresentation]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[eq_top_iff]`.

Introduce `x _`. Conclude with `Submodule.mem_iSup_of_mem 0 ((mem_weightSp_iff_diagonal_apply _ _ _).2 fun a => by simp [trivialRepresentation])`.
-/
theorem trivialRepresentation_isRep (n : ℕ) (K : Type) [Field K] : IsGLRep (trivialRepresentation n K) := by
  refine ⟨?_, fun x => ⟨⊤, inferInstance, trivial, fun _ _ _ _ => trivial⟩, ?_⟩
  · intro a b c d
    simp only [trivialRepresentation]
    split_ifs <;> simp
  · rw [eq_top_iff]
    intro x _
    exact Submodule.mem_iSup_of_mem 0 ((mem_weightSp_iff_diagonal_apply _ _ _).2 fun a => by simp [trivialRepresentation])

/- English proof (translation)
Use `⟨fun x _ => rfl, fun mu hmu x hx => ?_⟩` and prove the remaining obligations. Establish `hle : isoSub (trivialRepresentation n K) mu ≤ ⊥`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `y ⟨u, _, v, hv, _⟩`. It suffices to derive a contradiction.

Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, mu i ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Conclude with `hmu (funext fun i => by_contra fun h => hcon ⟨i, h⟩)`. Establish `h1` using `(mem_weightSp_iff_diagonal_apply _ mu v).1 hv.2.1 i`. Simplify using `only [trivialRepresentation, LinearMap.zero_apply] at h1`.

Break down `smul_eq_zero.1 h1.symm with h | h` into its components or cases. Conclude with `hi (by exact_mod_cast h)`. Conclude with `hv.1 h`. Use `hle hx` as an intermediate fact. Rewrite `this` using `[Submodule.mem_bot]`.

Rewrite using `[this, map_zero]`.
-/
theorem trivialRep_invariant_projection (n : ℕ) (K : Type) [Field K] [CharZero K] : IsInvProj (trivialRepresentation n K) 1 := by
  refine ⟨fun x _ => rfl, fun mu hmu x hx => ?_⟩
  have hle : isoSub (trivialRepresentation n K) mu ≤ ⊥ := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨u, _, v, hv, _⟩
    exfalso
    obtain ⟨i, hi⟩ : ∃ i, mu i ≠ 0 := by
      by_contra hcon
      exact hmu (funext fun i => by_contra fun h => hcon ⟨i, h⟩)
    have h1 := (mem_weightSp_iff_diagonal_apply _ mu v).1 hv.2.1 i
    simp only [trivialRepresentation, LinearMap.zero_apply] at h1
    rcases smul_eq_zero.1 h1.symm with h | h
    · exact hi (by exact_mod_cast h)
    · exact hv.1 h
  have := hle hx
  rw [Submodule.mem_bot] at this
  rw [this, map_zero]

/- English proof (translation)
Introduce `a b x`. Establish `h` using `congrArg (fun f : V →ₗ[K] V' => f x) (invariant_projection_kills_operators D h2 n K _ (homRepresentation E E') (homRepresentation_isRep E E' hE hE') P hP g a b)`. Simplify using `only [homRepresentation_apply, LinearMap.zero_apply] at h`. Conclude with `(sub_eq_zero.1 h).symm`.
-/
theorem invariant_projection_equivariant (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {n : ℕ} {K V V' : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    (E : GLOps n K V) (E' : GLOps n K V') (hE : IsGLRep E) (hE' : IsGLRep E')
    (P : Module.End K (V →ₗ[K] V')) (hP : IsInvProj (homRepresentation E E') P) (g : V →ₗ[K] V') : IsEquivariantMap E E' (P g) := by
  intro a b x
  have h := congrArg (fun f : V →ₗ[K] V' => f x)
    (invariant_projection_kills_operators D h2 n K _ (homRepresentation E E') (homRepresentation_isRep E E' hE hE') P hP g a b)
  simp only [homRepresentation_apply, LinearMap.zero_apply] at h
  exact (sub_eq_zero.1 h).symm

/- English proof (translation)
Establish `hψ` using `invariant_projection_equivariant D h2 EL EL hEL hEL P0 hP0 g`. Establish `hw : P0 g v0 ∈ weightSp EL lam`. Rewrite using `[mem_weightSp_iff_diagonal_apply]`. Introduce `a`. Rewrite using `[← hψ, (mem_weightSp_iff_diagonal_apply EL lam v0).1 hv0.2.1 a, map_smul]`.

Take `⟨c, hc⟩` from `cyclic_highest_weightSpace_line EL hEL lam v0 hv0 (P0 g v0) (by rw [hcyc]; trivial) hw`. Establish `hid : P0 g = c • (LinearMap.id : L →ₗ[K] L)`. Establish `hT : IsEquivariantMap EL EL (P0 g - c • (LinearMap.id : L →ₗ[K] L))`. Introduce `a b x`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul]`.

Rewrite using `[hψ]`. Establish `h0 : (P0 g - c • (LinearMap.id : L →ₗ[K] L)) v0 = 0`. Simplify using `[hc]`. Use extensionality with `x`. Use `equivariant_kills_cyclic_of_zero EL EL _ hT v0 h0 x (by rw [hcyc]; trivial)` as an intermediate fact.

Conclude with `sub_eq_zero.1 this`. Establish `htr : IsEquivariantMap (homRepresentation EL EL) (trivialRepresentation n K) (LinearMap.trace K L)`. Introduce `a b f`. Establish `: homRepresentation EL EL a b f = EL a b * f - f * EL a b`. Use extensionality with `x`.

Simplify using the standard rewrite rules. Rewrite using `[this, map_sub, LinearMap.trace_mul_comm, sub_self]`. Both sides reduce to the same expression. Establish `h3` using `equivariant_commutes_isotypic D h2 n K _ K (homRepresentation EL EL) (trivialRepresentation n K) (homRepresentation_isRep EL EL hEL hEL) (trivialRepresentation_isRep n K) (LinearMap.trace K L) htr P0 1 hP0 (trivialRep_invariant_projection n K) g`. Rewrite `h3` using `[Module.End.one_apply, hid, map_smul, LinearMap.trace_id, smul_eq_mul]`.

Rewrite using `[hid, smul_smul, ← h3, mul_comm]`.
-/
theorem schur_invariant_projection_trace (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {n : ℕ} {K L : Type} [Field K] [CharZero K]
    [AddCommGroup L] [Module K L] [FiniteDimensional K L] (EL : GLOps n K L) (hEL : IsGLRep EL) (lam : Fin n → ℤ)
    (v0 : L) (hv0 : IsHWV EL lam v0) (hcyc : cyclicSubmodule EL v0 = ⊤)
    (P0 : Module.End K (L →ₗ[K] L)) (hP0 : IsInvProj (homRepresentation EL EL) P0) (g : L →ₗ[K] L) :
    (Module.finrank K L : K) • P0 g = (LinearMap.trace K L g) • (LinearMap.id : L →ₗ[K] L) := by
  have hψ := invariant_projection_equivariant D h2 EL EL hEL hEL P0 hP0 g
  have hw : P0 g v0 ∈ weightSp EL lam := by
    rw [mem_weightSp_iff_diagonal_apply]
    intro a
    rw [← hψ, (mem_weightSp_iff_diagonal_apply EL lam v0).1 hv0.2.1 a, map_smul]
  obtain ⟨c, hc⟩ := cyclic_highest_weightSpace_line EL hEL lam v0 hv0 (P0 g v0) (by rw [hcyc]; trivial) hw
  have hid : P0 g = c • (LinearMap.id : L →ₗ[K] L) := by
    have hT : IsEquivariantMap EL EL (P0 g - c • (LinearMap.id : L →ₗ[K] L)) := by
      intro a b x
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul]
      rw [hψ]
    have h0 : (P0 g - c • (LinearMap.id : L →ₗ[K] L)) v0 = 0 := by
      simp [hc]
    ext x
    have := equivariant_kills_cyclic_of_zero EL EL _ hT v0 h0 x (by rw [hcyc]; trivial)
    exact sub_eq_zero.1 this
  have htr : IsEquivariantMap (homRepresentation EL EL) (trivialRepresentation n K) (LinearMap.trace K L) := by
    intro a b f
    have : homRepresentation EL EL a b f = EL a b * f - f * EL a b := by
      ext x; simp
    rw [this, map_sub, LinearMap.trace_mul_comm, sub_self]
    rfl
  have h3 := equivariant_commutes_isotypic D h2 n K _ K (homRepresentation EL EL) (trivialRepresentation n K) (homRepresentation_isRep EL EL hEL hEL)
    (trivialRepresentation_isRep n K) (LinearMap.trace K L) htr P0 1 hP0 (trivialRep_invariant_projection n K) g
  rw [Module.End.one_apply, hid, map_smul, LinearMap.trace_id, smul_eq_mul] at h3
  rw [hid, smul_smul, ← h3, mul_comm]

end Formalism.MainNotions.G.GLWeightTheory
