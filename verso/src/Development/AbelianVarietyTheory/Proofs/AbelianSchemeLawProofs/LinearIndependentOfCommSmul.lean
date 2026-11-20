import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in

/- English proof (translation)
Rewrite using `[linearIndependent_iff']`. Introduce `s`. Proceed by induction on `s using Finset.strongInduction with`. Consider the case `H s ih`. Introduce `g hg i hi`.

Assume the negation of the conclusion as `hgi`. Establish `htwist : ∀ y, ∑ x ∈ s, (g x * (c x y - c i y)) • A x = 0`. Introduce `y`. Use extensionality with `v`. Establish `h0` using `LinearMap.congr_fun hg v`.

Establish `h1` using `LinearMap.congr_fun hg (A y v)`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply] at h0 h1 ⊢`. Establish `h2 : A y (∑ x ∈ s, (g x * c x y) • A x v) = 0`. Rewrite using `[map_sum, ← h1]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, h x y v, smul_smul]`. Establish `h3 : ∑ x ∈ s, (g x * c x y) • A x v = 0` using `hA y (by rw [h2, map_zero])`. Repeatedly rewrite using `[mul_sub, sub_smul, Finset.sum_sub_distrib, h3, zero_sub, neg_eq_zero]`. Establish `h4 : ∑ x ∈ s, (g x * c i y) • A x v = c i y • ∑ x ∈ s, g x • A x v`. Rewrite using `[Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, mul_comm]`. Rewrite using `[h4, h0, smul_zero]`. Establish `hothers : ∀ x ∈ s, x ≠ i → g x = 0`. Introduce `x hx hxi`.

Assume the negation of the conclusion as `hgx`. Apply `hxi` to reduce the goal to its premises. Apply `hc` to reduce the goal to its premises. Use function extensionality and compare the values at `y`. Establish `hrel : ∑ z ∈ s.erase i, (g z * (c z y - c i y)) • A z = 0`.

Rewrite using `[← htwist y, ← Finset.sum_erase_add s _ hi, sub_self, mul_zero, zero_smul, add_zero]`. Use `ih (s.erase i) (Finset.erase_ssubset hi) _ hrel x (Finset.mem_erase.2 ⟨hxi, hx⟩)` as an intermediate fact. Break down `mul_eq_zero.1 this with h5 | h5` into its components or cases. Conclude with `absurd h5 hgx`. Conclude with `sub_eq_zero.1 h5`.

Establish `hsingle : g i • A i = 0`. Rewrite using `[← hg, Finset.sum_eq_single_of_mem i hi]`. Introduce `x hx hxi`. Rewrite using `[hothers x hx hxi, zero_smul]`. Take `⟨v, hv⟩` from `exists_ne (0 : V)`.

Apply `hv` to reduce the goal to its premises. Apply `hA i` to reduce the goal to its premises. Use `LinearMap.congr_fun hsingle v` as an intermediate fact. Simplify using `only [LinearMap.smul_apply, LinearMap.zero_apply] at this`. Rewrite using `[map_zero]`.

Conclude with `(smul_eq_zero.1 this).resolve_left hgi`.
-/
theorem _root_.GlobalTheory.linearIndependent_of_comm_smul {K G V : Type} [Field K] [AddCommGroup V] [Module K V]
    [Nontrivial V] (A : G → V →ₗ[K] V) (c : G → G → K) (hA : ∀ x, Function.Injective (A x))
    (h : ∀ x y v, A x (A y v) = c x y • A y (A x v)) (hc : Function.Injective c) :
    LinearIndependent K A := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro g hg i hi
  by_contra hgi

  have htwist : ∀ y, ∑ x ∈ s, (g x * (c x y - c i y)) • A x = 0 := by
    intro y
    ext v
    have h0 := LinearMap.congr_fun hg v
    have h1 := LinearMap.congr_fun hg (A y v)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.zero_apply] at h0 h1 ⊢
    have h2 : A y (∑ x ∈ s, (g x * c x y) • A x v) = 0 := by
      rw [map_sum, ← h1]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_smul, h x y v, smul_smul]
    have h3 : ∑ x ∈ s, (g x * c x y) • A x v = 0 :=
      hA y (by rw [h2, map_zero])
    simp_rw [mul_sub, sub_smul, Finset.sum_sub_distrib, h3, zero_sub, neg_eq_zero]
    have h4 : ∑ x ∈ s, (g x * c i y) • A x v = c i y • ∑ x ∈ s, g x • A x v := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [smul_smul, mul_comm]
    rw [h4, h0, smul_zero]
  have hothers : ∀ x ∈ s, x ≠ i → g x = 0 := by
    intro x hx hxi
    by_contra hgx
    apply hxi
    apply hc
    funext y
    have hrel : ∑ z ∈ s.erase i, (g z * (c z y - c i y)) • A z = 0 := by
      rw [← htwist y, ← Finset.sum_erase_add s _ hi, sub_self, mul_zero, zero_smul, add_zero]
    have := ih (s.erase i) (Finset.erase_ssubset hi) _ hrel x (Finset.mem_erase.2 ⟨hxi, hx⟩)
    rcases mul_eq_zero.1 this with h5 | h5
    · exact absurd h5 hgx
    · exact sub_eq_zero.1 h5
  have hsingle : g i • A i = 0 := by
    rw [← hg, Finset.sum_eq_single_of_mem i hi]
    intro x hx hxi
    rw [hothers x hx hxi, zero_smul]
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  apply hv
  apply hA i
  have := LinearMap.congr_fun hsingle v
  simp only [LinearMap.smul_apply, LinearMap.zero_apply] at this
  rw [map_zero]
  exact (smul_eq_zero.1 this).resolve_left hgi

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in

/- English proof (translation)
Introduce `K G V _ _ _ _ _ _ U e hU he hcard W hW`. Break down `subsingleton_or_nontrivial V with hV | hV` into its components or cases. Conclude with `Or.inl (Submodule.eq_bot_of_subsingleton)`. Use `haveI : Fintype G := Fintype.ofFinite G`. Establish `hind : LinearIndependent K (fun x => (U x : V →ₗ[K] V))`.

Use `_root_.GlobalTheory.linearIndependent_of_comm_smul (fun x => (U x : V →ₗ[K] V)) (fun x y => (e x y : K)) (fun x => (U x).injective) (fun x y v => hU x y v) ?_` and prove the remaining obligations. Introduce `x x' hxx'`. Apply `he` to reduce the goal to its premises. Use extensionality with `y`. Conclude with `congr_fun hxx' y`.

Establish `hdim : Module.finrank K (V →ₗ[K] V) = Module.finrank K V ^ 2`. Rewrite using `[Module.finrank_linearMap, sq]`. Establish `hle` using `hind.fintype_card_le_finrank`. Rewrite `hle` using `[hdim]`. Rewrite `hcard` using `[Nat.card_eq_fintype_card]`.

Establish `hspan` using `hind.span_eq_top_of_card_eq_finrank (le_antisymm hle hcard |>.trans hdim.symm)`. Set `S : Submodule K (V →ₗ[K] V)` to `{ carrier := {f | ∀ w ∈ W, f w ∈ W} add_mem' := fun hf hg w hw => W.add_mem (hf w hw) (hg w hw) zero_mem' := fun w _ => by simp smul_mem' := fun a f hf w hw => W.smul_mem a (hf w hw) }`. Establish `hS : ∀ f : V →ₗ[K] V, ∀ w ∈ W, f w ∈ W`. Introduce `f`. Establish `: f ∈ Submodule.span K (Set.range fun x => (U x : V →ₗ[K] V))`.

Rewrite using `[hspan]`. Conclude with `Submodule.mem_top`. Establish `hsub : Submodule.span K (Set.range fun x => (U x : V →ₗ[K] V)) ≤ S`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩ w hw`.

Conclude with `hW x w hw`. Conclude with `hsub this`. Distinguish the cases in `hbot : W = ⊥`. Conclude with `Or.inl hbot`. Use `right`.

Take `⟨w, hwW, hw0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hbot`. Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : Module.Dual K V, φ w ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hw0 ((Module.forall_dual_apply_eq_zero_iff K w).1 hcon)`.

Rewrite using `[eq_top_iff]`. Introduce `v _`. Use `hS ((φ w)⁻¹ • φ.smulRight v) w hwW` as an intermediate fact. Simplify `this` using `[LinearMap.smulRight_apply, smul_smul, inv_mul_cancel₀ hφ]`.
-/
theorem _root_.GlobalTheory.heisenberg_family_irreducible : ∀ (K G V : Type) [Field K] [CommGroup G] [Finite G] [AddCommGroup V] [Module K V] [Module.Finite K V] (U : G → V ≃ₗ[K] V) (e : G → G →* Kˣ), (∀ x y v, U x (U y v) = (e x y : K) • U y (U x v)) → Function.Injective e → Module.finrank K V ^ 2 ≤ Nat.card G → ∀ W : Submodule K V, (∀ x v, v ∈ W → U x v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro K G V _ _ _ _ _ _ U e hU he hcard W hW
  classical
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact Or.inl (Submodule.eq_bot_of_subsingleton)
  haveI : Fintype G := Fintype.ofFinite G
  have hind : LinearIndependent K (fun x => (U x : V →ₗ[K] V)) := by
    refine _root_.GlobalTheory.linearIndependent_of_comm_smul (fun x => (U x : V →ₗ[K] V))
      (fun x y => (e x y : K)) (fun x => (U x).injective) (fun x y v => hU x y v) ?_
    intro x x' hxx'
    apply he
    ext y
    exact congr_fun hxx' y
  have hdim : Module.finrank K (V →ₗ[K] V) = Module.finrank K V ^ 2 := by
    rw [Module.finrank_linearMap, sq]
  have hle := hind.fintype_card_le_finrank
  rw [hdim] at hle
  rw [Nat.card_eq_fintype_card] at hcard
  have hspan := hind.span_eq_top_of_card_eq_finrank (le_antisymm hle hcard |>.trans hdim.symm)

  let S : Submodule K (V →ₗ[K] V) :=
    { carrier := {f | ∀ w ∈ W, f w ∈ W}
      add_mem' := fun hf hg w hw => W.add_mem (hf w hw) (hg w hw)
      zero_mem' := fun w _ => by simp
      smul_mem' := fun a f hf w hw => W.smul_mem a (hf w hw) }
  have hS : ∀ f : V →ₗ[K] V, ∀ w ∈ W, f w ∈ W := by
    intro f
    have : f ∈ Submodule.span K (Set.range fun x => (U x : V →ₗ[K] V)) := by
      rw [hspan]; exact Submodule.mem_top
    have hsub : Submodule.span K (Set.range fun x => (U x : V →ₗ[K] V)) ≤ S := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩ w hw
      exact hW x w hw
    exact hsub this
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K V, φ w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hw0 ((Module.forall_dual_apply_eq_zero_iff K w).1 hcon)
  rw [eq_top_iff]
  intro v _
  have := hS ((φ w)⁻¹ • φ.smulRight v) w hwW
  simpa [LinearMap.smulRight_apply, smul_smul, inv_mul_cancel₀ hφ] using this

end GlobalTheory
