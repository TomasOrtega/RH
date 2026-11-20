import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemTensSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorIrreducibleModules
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TensSpanIrr

open GlobalTheory.RealLift GlobalTheory.KFixIrr

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨v, hv, rfl⟩` from `hx`. Use `⟨{⟨v w, hv w⟩}, fun f g h => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.TensIrr.atPl_tprod, GlobalTheory.TensIrr.atPl_tprod, h ⟨v w, hv w⟩ (Finset.mem_singleton_self _)]`.

Consider the case `zero => exact ⟨∅, fun f g _ => by rw [map_zero, map_zero]⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨s, hs⟩` from `hx`. Take `⟨t, ht⟩` from `hy`. Use `⟨s ∪ t, fun f g h => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, map_add, hs f g (fun m hm => h m (Finset.mem_union_left _ hm)), ht f g (fun m hm => h m (Finset.mem_union_right _ hm))]`. Consider the case `smul a x _ hx`. Take `⟨s, hs⟩` from `hx`. Conclude with `⟨s, fun f g h => by rw [map_smul, map_smul, hs f g h]⟩`.
-/
theorem atPl_local_sub (H : ι → Submodule ℂ V) (w : ι) (y : ⨂[ℂ] _ : ι, V) (hy : y ∈ tensSpan H) :
    ∃ s : Finset (H w), ∀ f g : Module.End ℂ V, (∀ m ∈ s, f m = g m) →
      atPl (V := fun _ : ι => V) w f y = atPl (V := fun _ : ι => V) w g y := by
  classical
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    refine ⟨{⟨v w, hv w⟩}, fun f g h => ?_⟩
    rw [GlobalTheory.TensIrr.atPl_tprod, GlobalTheory.TensIrr.atPl_tprod, h ⟨v w, hv w⟩ (Finset.mem_singleton_self _)]
  | zero => exact ⟨∅, fun f g _ => by rw [map_zero, map_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    refine ⟨s ∪ t, fun f g h => ?_⟩
    rw [map_add, map_add, hs f g (fun m hm => h m (Finset.mem_union_left _ hm)),
      ht f g (fun m hm => h m (Finset.mem_union_right _ hm))]
  | smul a x _ hx =>
    obtain ⟨s, hs⟩ := hx
    exact ⟨s, fun f g h => by rw [map_smul, map_smul, hs f g h]⟩

/- English proof (translation)
Set `B : Z → Module.End ℂ (H w)` to `fun z => (A z).restrict (hA z)`. Establish `hBirr : ∀ M : Submodule ℂ (H w), (∀ z, ∀ y ∈ M, B z y ∈ M) → M = ⊥ ∨ M = ⊤`. Introduce `M hM`. Establish `hinj` using `Submodule.map_injective_of_injective (H w).injective_subtype`. Break down `hirr (M.map (H w).subtype) (by simp [Submodule.map_subtype_le]) (by` into its components or cases.

Introduce and unpack `z _ ⟨x, hx, rfl⟩`. Conclude with `⟨B z x, hM z x hx, rfl⟩) with h | h`. Use `left`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[h, Submodule.map_bot]`.

Use `right`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[h, Submodule.map_subtype_top]`. Establish `hBsch : ∀ T : H w →ₗ[ℂ] H w, (∀ z, T ∘ₗ B z = B z ∘ₗ T) → ∃ c : ℂ, T = c • LinearMap.id`. Introduce `T hT`.

Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue T`. Use `⟨c, ?_⟩` and prove the remaining obligations. Break down `hBirr (Module.End.eigenspace T c) (fun z y hy => by` into its components or cases. Rewrite `hy`, the goal using `[Module.End.mem_eigenspace_iff]`. Use `LinearMap.congr_fun (hT z) y` as an intermediate fact.

Simplify using `only [LinearMap.comp_apply] at this`. Rewrite using `[this, hy, map_smul]) with h | h`. Conclude with `absurd h (Module.End.hasEigenvalue_iff.1 hc)`. Use extensionality with `x`. Establish `hx : x ∈ Module.End.eigenspace T c` using `h ▸ Submodule.mem_top`.

Rewrite `hx` using `[Module.End.mem_eigenspace_iff]`. Simplify using `[hx]`. Establish `hadj : ∀ r ∈ Algebra.adjoin ℂ (Set.range A), ∀ y ∈ N, atPl (V` using `fun _ : ι => V) w r y ∈ N := by`. Introduce `r hr`. Proceed by induction on `hr using Algebra.adjoin_induction with`.

Consider the case `mem x hx => obtain ⟨z, rfl⟩ := hx`. Conclude with `hN z`. Consider the case `algebraMap c`. Introduce `y hy`. Rewrite using `[Algebra.algebraMap_eq_smul_one, GlobalTheory.TensIrr.atPl_smul, GlobalTheory.TensIrr.atPl_one]`.

Conclude with `N.smul_mem c hy`. Consider the case `add x y _ _ hx hy`. Introduce `z hz`. Rewrite using `[GlobalTheory.TensIrr.atPl_add]`. Conclude with `N.add_mem (hx z hz) (hy z hz)`.

Consider the case `mul x y _ _ hx hy`. Introduce `z hz`. Rewrite using `[GlobalTheory.TensIrr.atPl_mul]`. Conclude with `hx _ (hy z hz)`. Establish `hlift : ∀ r ∈ Algebra.adjoin ℂ (Set.range B), ∃ r' ∈ Algebra.adjoin ℂ (Set.range A), ∀ x : H w, r' x = (r x : V)`.

Introduce `r hr`. Proceed by induction on `hr using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨z, rfl⟩` from `hx`. Conclude with `⟨A z, Algebra.subset_adjoin ⟨z, rfl⟩, fun x => rfl⟩`.

Consider the case `algebraMap c`. Conclude with `⟨algebraMap ℂ _ c, Subalgebra.algebraMap_mem _ c, fun x => by`. Simplify using `[Algebra.algebraMap_eq_smul_one]⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, ha'⟩` from `hx`.

Take `⟨b, hb, hb'⟩` from `hy`. Conclude with `⟨a + b, add_mem ha hb, fun t => by simp [ha', hb']⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨a, ha, ha'⟩` from `hx`. Take `⟨b, hb, hb'⟩` from `hy`.

Conclude with `⟨a * b, mul_mem ha hb, fun t => by`. Rewrite using `[Module.End.mul_apply, Module.End.mul_apply, hb', ha']⟩`. Introduce `y hy`. Take `⟨s, hs⟩` from `atPl_local_sub H w y (hle hy)`. Set `g : Module.End ℂ (H w)` to `F.restrict (fun v _ => hF v)`.

Take `⟨r, hr, hrg⟩` from `GlobalTheory.IrrTensor.density B hBirr hBsch g s`. Take `⟨r', hr', hr'r⟩` from `hlift r hr`. Rewrite using `[hs F r' (fun m hm => by rw [hr'r m, ← hrg m hm]; rfl)]`. Conclude with `hadj r' hr' y hy`.
-/
theorem stable_of_range (H : ι → Submodule ℂ V) (w : ι) [FiniteDimensional ℂ (H w)] [Nontrivial (H w)]
    {Z : Type} (A : Z → Module.End ℂ V) (hA : ∀ z, ∀ v ∈ H w, A z v ∈ H w)
    (hirr : ∀ N : Submodule ℂ V, N ≤ H w → (∀ z, ∀ v ∈ N, A z v ∈ N) → N = ⊥ ∨ N = H w)
    (N : Submodule ℂ (⨂[ℂ] _ : ι, V)) (hle : N ≤ tensSpan H)
    (hN : ∀ z, ∀ T ∈ N, atPl (V := fun _ : ι => V) w (A z) T ∈ N)
    (F : Module.End ℂ V) (hF : ∀ v, F v ∈ H w) :
    ∀ y ∈ N, atPl (V := fun _ : ι => V) w F y ∈ N := by
  classical
  let B : Z → Module.End ℂ (H w) := fun z => (A z).restrict (hA z)
  have hBirr : ∀ M : Submodule ℂ (H w), (∀ z, ∀ y ∈ M, B z y ∈ M) → M = ⊥ ∨ M = ⊤ := by
    intro M hM
    have hinj := Submodule.map_injective_of_injective (H w).injective_subtype
    rcases hirr (M.map (H w).subtype) (by simp [Submodule.map_subtype_le]) (by
      rintro z _ ⟨x, hx, rfl⟩
      exact ⟨B z x, hM z x hx, rfl⟩) with h | h
    · left
      apply hinj
      rw [h, Submodule.map_bot]
    · right
      apply hinj
      rw [h, Submodule.map_subtype_top]
  have hBsch : ∀ T : H w →ₗ[ℂ] H w, (∀ z, T ∘ₗ B z = B z ∘ₗ T) → ∃ c : ℂ, T = c • LinearMap.id := by
    intro T hT
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
    refine ⟨c, ?_⟩
    rcases hBirr (Module.End.eigenspace T c) (fun z y hy => by
      rw [Module.End.mem_eigenspace_iff] at hy ⊢
      have := LinearMap.congr_fun (hT z) y
      simp only [LinearMap.comp_apply] at this
      rw [this, hy, map_smul]) with h | h
    · exact absurd h (Module.End.hasEigenvalue_iff.1 hc)
    · ext x
      have hx : x ∈ Module.End.eigenspace T c := h ▸ Submodule.mem_top
      rw [Module.End.mem_eigenspace_iff] at hx
      simp [hx]
  have hadj : ∀ r ∈ Algebra.adjoin ℂ (Set.range A), ∀ y ∈ N, atPl (V := fun _ : ι => V) w r y ∈ N := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨z, rfl⟩ := hx; exact hN z
    | algebraMap c =>
      intro y hy
      rw [Algebra.algebraMap_eq_smul_one, GlobalTheory.TensIrr.atPl_smul, GlobalTheory.TensIrr.atPl_one]
      exact N.smul_mem c hy
    | add x y _ _ hx hy =>
      intro z hz
      rw [GlobalTheory.TensIrr.atPl_add]
      exact N.add_mem (hx z hz) (hy z hz)
    | mul x y _ _ hx hy =>
      intro z hz
      rw [GlobalTheory.TensIrr.atPl_mul]
      exact hx _ (hy z hz)
  have hlift : ∀ r ∈ Algebra.adjoin ℂ (Set.range B),
      ∃ r' ∈ Algebra.adjoin ℂ (Set.range A), ∀ x : H w, r' x = (r x : V) := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨z, rfl⟩ := hx
      exact ⟨A z, Algebra.subset_adjoin ⟨z, rfl⟩, fun x => rfl⟩
    | algebraMap c =>
      exact ⟨algebraMap ℂ _ c, Subalgebra.algebraMap_mem _ c, fun x => by
        simp [Algebra.algebraMap_eq_smul_one]⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨b, hb, hb'⟩ := hy
      exact ⟨a + b, add_mem ha hb, fun t => by simp [ha', hb']⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨b, hb, hb'⟩ := hy
      exact ⟨a * b, mul_mem ha hb, fun t => by
        rw [Module.End.mul_apply, Module.End.mul_apply, hb', ha']⟩
  intro y hy
  obtain ⟨s, hs⟩ := atPl_local_sub H w y (hle hy)
  let g : Module.End ℂ (H w) := F.restrict (fun v _ => hF v)
  obtain ⟨r, hr, hrg⟩ := GlobalTheory.IrrTensor.density B hBirr hBsch g s
  obtain ⟨r', hr', hr'r⟩ := hlift r hr
  rw [hs F r' (fun m hm => by rw [hr'r m, ← hrg m hm]; rfl)]
  exact hadj r' hr' y hy

/- English proof (translation)
Introduce `ι _ _ V Z _ _ A H hfd hne hA hirr N hle hN`. Distinguish the cases in `h0 : N = ⊥`. Conclude with `Or.inl h0`. Use `right`. Take `⟨y, hy, hy0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h0`.

Take `⟨ℓ, hℓ⟩` from `GlobalTheory.TensIrr.exists_prodForm_ne (V := fun _ : ι => V) y hy0`. Use `le_antisymm hle ?_` and prove the remaining obligations. Rewrite using `[tensSpan, Submodule.span_le]`. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Establish `hst : ∀ w, ∀ x ∈ N, atPl (V` using `fun _ : ι => V) w ((ℓ w).smulRight (u w)) x ∈ N := by`.

Introduce `w`. Use `haveI : FiniteDimensional ℂ (H w) := hfd w`. Use `haveI : Nontrivial (H w) := Submodule.nontrivial_iff_ne_bot.2 (hne w)`. Conclude with `stable_of_range H w (A w) (hA w) (hirr w) N hle (hN w) _ (fun v => by simpa using (H w).smul_mem (ℓ w v) (hu w))`. Establish `key : ∀ s : Finset ι, ∀ x ∈ N, PiTensorProduct.map (fun i => if i ∈ s then (ℓ i).smulRight (u i) else LinearMap.id) x ∈ N`.

Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro x hx`. Simplify using `using hx`. Consider the case `insert a s ha ih`.

Introduce `x hx`. Establish `e : PiTensorProduct.map (fun i => if i ∈ insert a s then (ℓ i).smulRight (u i) else LinearMap.id) = atPl (V` using `fun _ : ι => V) a ((ℓ a).smulRight (u a)) ∘ₗ PiTensorProduct.map (fun i => if i ∈ s then (ℓ i).smulRight (u i) else LinearMap.id) := by`. Unfold `atPl`. Rewrite using `[← PiTensorProduct.map_comp]`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = a`. Substitute `h` using the available equality. Simplify using `[ha]`. Simplify using `[Function.update_of_ne h, Finset.mem_insert, h]`.

Rewrite using `[e]`. Conclude with `hst a _ (ih x hx)`. Establish `h1` using `key Finset.univ y hy`. Simplify using `only [Finset.mem_univ, if_true] at h1`. Rewrite `h1` using `[GlobalTheory.TensIrr.map_rankOne]`.

Establish `h2` using `N.smul_mem (GlobalTheory.TensIrr.prodForm ℓ y)⁻¹ h1`. Rewrite `h2` using `[smul_smul, inv_mul_cancel₀ hℓ, one_smul]`. Then use the resulting hypothesis.
-/
theorem tensSpan_irr : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (V Z : Type) [AddCommGroup V] [Module ℂ V]
    (A : ι → Z → Module.End ℂ V) (H : ι → Submodule ℂ V), (∀ w, FiniteDimensional ℂ (H w)) → (∀ w, H w ≠ ⊥) →
    (∀ w z, ∀ v ∈ H w, A w z v ∈ H w) →
    (∀ w (N : Submodule ℂ V), N ≤ H w → (∀ z, ∀ v ∈ N, A w z v ∈ N) → N = ⊥ ∨ N = H w) →
    ∀ N : Submodule ℂ (⨂[ℂ] _ : ι, V), N ≤ GlobalTheory.KFixIrr.tensSpan H →
      (∀ w z, ∀ T ∈ N, GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w (A w z) T ∈ N) →
      N = ⊥ ∨ N = GlobalTheory.KFixIrr.tensSpan H := by
  intro ι _ _ V Z _ _ A H hfd hne hA hirr N hle hN
  classical
  by_cases h0 : N = ⊥
  · exact Or.inl h0
  right
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  obtain ⟨ℓ, hℓ⟩ := GlobalTheory.TensIrr.exists_prodForm_ne (V := fun _ : ι => V) y hy0
  refine le_antisymm hle ?_
  rw [tensSpan, Submodule.span_le]
  rintro _ ⟨u, hu, rfl⟩
  have hst : ∀ w, ∀ x ∈ N, atPl (V := fun _ : ι => V) w ((ℓ w).smulRight (u w)) x ∈ N := by
    intro w
    haveI : FiniteDimensional ℂ (H w) := hfd w
    haveI : Nontrivial (H w) := Submodule.nontrivial_iff_ne_bot.2 (hne w)
    exact stable_of_range H w (A w) (hA w) (hirr w) N hle (hN w) _
      (fun v => by simpa using (H w).smul_mem (ℓ w v) (hu w))
  have key : ∀ s : Finset ι, ∀ x ∈ N,
      PiTensorProduct.map (fun i => if i ∈ s then (ℓ i).smulRight (u i) else LinearMap.id) x ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x hx; simpa using hx
    | insert a s ha ih =>
      intro x hx
      have e : PiTensorProduct.map (fun i => if i ∈ insert a s then (ℓ i).smulRight (u i) else LinearMap.id) =
          atPl (V := fun _ : ι => V) a ((ℓ a).smulRight (u a)) ∘ₗ
            PiTensorProduct.map (fun i => if i ∈ s then (ℓ i).smulRight (u i) else LinearMap.id) := by
        unfold atPl
        rw [← PiTensorProduct.map_comp]
        congr 1
        funext j
        by_cases h : j = a
        · subst h; simp [ha]
        · simp [Function.update_of_ne h, Finset.mem_insert, h]
      rw [e]
      exact hst a _ (ih x hx)
  have h1 := key Finset.univ y hy
  simp only [Finset.mem_univ, if_true] at h1
  rw [GlobalTheory.TensIrr.map_rankOne] at h1
  have h2 := N.smul_mem (GlobalTheory.TensIrr.prodForm ℓ y)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hℓ, one_smul] at h2

end GlobalTheory.TensSpanIrr

end
