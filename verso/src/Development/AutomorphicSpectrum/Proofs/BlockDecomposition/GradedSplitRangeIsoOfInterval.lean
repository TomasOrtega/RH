import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedSplittingTensorFiltrationStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GrPiece

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => rfl`. Consider the case `tmul n x => rw [Subsingleton.elim x 0, TensorProduct.tmul_zero]`. Consider the case `add a b ha hb => rw [ha, hb, add_zero]`.
-/
theorem subsingleton_tmul {O N M : Type} [CommRing O] [AddCommGroup N] [Module O N] [AddCommGroup M] [Module O M]
    [Subsingleton M] (y : N ⊗[O] M) : y = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rfl
  | tmul n x => rw [Subsingleton.elim x 0, TensorProduct.tmul_zero]
  | add a b ha hb => rw [ha, hb, add_zero]

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `O A G _ _ _ _ _ _ I γ m S u v M _ _ M' _ θ h0 π hπ hker f hf0 hf`. Take `⟨g₀, hs, hm⟩` from `GlobalTheory.T.graded_splitting_tensor_filtration (Γ := G) γ m S`. Set `t : ∀ i : Fin m, S.N i ⊗[O] M i →+ S.N i ⊗[O] G` to `fun i => if h : u ≤ (i : ℕ) ∧ (i : ℕ) < v then ((LinearEquiv.lTensor (S.N i) (θ i h.1 h.2)).symm : S.N i ⊗[O] M i ≃ₗ[O] S.N i ⊗[O] G).toLinearMap.toAddMonoidHom else 0`. Establish `t_act : ∀ (i : Fin m) (h : u ≤ (i : ℕ) ∧ (i : ℕ) < v) (a : S.N i ⊗[O] G), t i (LinearEquiv.lTensor (S.N i) (θ i h.1 h.2) a) = a`. Introduce `i h a`.

Simplify using `only [t, dif_pos h]`. Conclude with `(LinearEquiv.lTensor (S.N i) (θ i h.1 h.2)).symm_apply_apply a`. Establish `t_inact : ∀ (i : Fin m), ¬ (u ≤ (i : ℕ) ∧ (i : ℕ) < v) → t i = 0`. Introduce `i h`. Simplify using `only [t, dif_neg h]`.

Set `T : (∀ i, S.N i ⊗[O] M i) →+ (∀ i, S.N i ⊗[O] G)` to `{ toFun := fun w i => t i (w i) map_zero' := by funext i; simp map_add' := fun a b => by funext i; simp }`. Establish `T_apply : ∀ w i, T w i = t i (w i)` using `fun _ _ => rfl`. Establish `hT : ∀ w, g₀ (T w) ∈ (pdP γ u).map (Algebra.TensorProduct.includeLeftRingHom (R` using `O) (A := A) (B := G)) := by`. Introduce `w`. Use `(hm u _).2 fun i hi => ?_` and prove the remaining obligations.

Rewrite using `[T_apply, t_inact i (by omega)]`. Both sides reduce to the same expression. Set `φ : (∀ i, S.N i ⊗[O] M i) →+ M'` to `{ toFun := fun w => π ⟨g₀ (T w), hT w⟩ map_zero' := by`. Establish `: (⟨g₀ (T 0), hT 0⟩ : ((pdP γ u).map (Algebra.TensorProduct.includeLeftRingHom (R` using `O) (A := A) (B := G)) : Ideal (A ⊗[O] G))) = 0 := Subtype.ext (by simp)`. Rewrite using `[this, map_zero]`.

Use the proof step `map_add' := fun a b => by`. Rewrite using `[← map_add]`. Conclude with `congrArg π (Subtype.ext (by simp)) }`. Establish `φ_apply : ∀ w, φ w = π ⟨g₀ (T w), hT w⟩` using `fun _ => rfl`. Establish `inj : Function.Injective φ`.

Use `(injective_iff_map_eq_zero φ).2 fun w hw => ?_` and prove the remaining obligations. Rewrite `hw` using `[φ_apply]`. Establish `h1` using `(hm v _).1 ((hker _).1 hw)`. Use function extensionality and compare the values at `i`. Distinguish the cases in `h : u ≤ (i : ℕ) ∧ (i : ℕ) < v`.

Establish `h2` using `h1 i h.2`. Rewrite `h2` using `[T_apply]`. Take `⟨a, ha⟩` from `(LinearEquiv.lTensor (S.N i) (θ i h.1 h.2)).surjective (w i)`. Rewrite `h2` using `[← ha, t_act i h]`. Rewrite using `[← ha, h2, map_zero]`.

Both sides reduce to the same expression. Use `haveI := h0 i h`. Conclude with `subsingleton_tmul _`. Establish `surj : Function.Surjective φ`. Introduce `y`.

Take `⟨x, rfl⟩` from `hπ y`. Take `⟨z, hz⟩` from `g₀.surjective x.1`. Establish `hzu` using `(hm u z).1 (by rw [hz]; exact x.2)`. Set `w : ∀ i, S.N i ⊗[O] M i` to `fun i => if h : u ≤ (i : ℕ) ∧ (i : ℕ) < v then LinearEquiv.lTensor (S.N i) (θ i h.1 h.2) (z i) else 0`. Use `⟨w, ?_⟩` and prove the remaining obligations.

Rewrite using `[φ_apply, ← sub_eq_zero, ← map_sub, hker]`. Establish `: ((⟨g₀ (T w), hT w⟩ - x : ((pdP γ u).map (Algebra.TensorProduct.includeLeftRingHom (R` using `O) (A := A) (B := G)) : Ideal (A ⊗[O] G))) : A ⊗[O] G) = g₀ (T w - z) := by`. Rewrite using `[map_sub, hz]`. Both sides reduce to the same expression. Rewrite using `[this, hm]`.

Introduce `i hi`. Rewrite using `[Pi.sub_apply, T_apply, sub_eq_zero]`. Distinguish the cases in `h : u ≤ (i : ℕ)`. Establish `h' : u ≤ (i : ℕ) ∧ (i : ℕ) < v` using `⟨h, hi⟩`. Simplify using `only [w, dif_pos h']`.

Conclude with `t_act i h' _`. Rewrite using `[t_inact i (by omega), hzu i (by omega)]`. Both sides reduce to the same expression. Use `⟨AddEquiv.ofBijective φ ⟨inj, surj⟩, fun i n x => ?_⟩` and prove the remaining obligations. Rewrite using `[AddEquiv.ofBijective_apply]`.

Distinguish the cases in `h : u ≤ (i : ℕ) ∧ (i : ℕ) < v`. Take `⟨y, rfl⟩` from `(θ i h.1 h.2).surjective x`. Establish `hTs : T (Pi.single i (n ⊗ₜ[O] θ i h.1 h.2 y)) = Pi.single i (n ⊗ₜ[O] y)`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = i`.

Substitute `hj` using the available equality. Rewrite using `[T_apply, Pi.single_eq_same, Pi.single_eq_same]`. Conclude with `t_act j h (n ⊗ₜ[O] y)`. Rewrite using `[T_apply, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, map_zero]`. Establish `hx : S.ν i n ⊗ₜ[O] y ∈ (pdP γ u).map (Algebra.TensorProduct.includeLeftRingHom (R` using `O) (A := A) (B := G)) := by`.

Rewrite using `[← hs, ← hTs]`. Conclude with `hT _`. Rewrite using `[hf i n y h.1 h.2 hx, φ_apply]`. Conclude with `congrArg π (Subtype.ext (by simp only [hTs, hs]))`. Use `haveI := h0 i h`.

Rewrite using `[Subsingleton.elim x 0, TensorProduct.tmul_zero, Pi.single_zero, map_zero, hf0]`.
-/
theorem main : ∀ {O A G : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing G] [Algebra O G] [Module.Flat O G]
    {I : Ideal A} (γ : DividedPowers I) (m : ℕ) (S : GrSplit O γ m) (u v : ℕ)
    {M : Fin m → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module O (M i)] {M' : Type} [AddCommGroup M']
    (θ : ∀ i : Fin m, u ≤ (i : ℕ) → (i : ℕ) < v → (G ≃ₗ[O] M i))
    (h0 : ∀ i : Fin m, ¬ (u ≤ (i : ℕ) ∧ (i : ℕ) < v) → Subsingleton (M i))
    (π : ((pdP γ u).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G)) : Ideal (A ⊗[O] G)) →+ M'),
    Function.Surjective π →
    (∀ x, π x = 0 ↔ x.1 ∈ (pdP γ v).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G))) →
    ∀ f : ∀ i, S.N i → M i → M', (∀ i n, f i n 0 = 0) →
    (∀ (i : Fin m) n x (hu : u ≤ (i : ℕ)) (hv : (i : ℕ) < v) hx, f i n (θ i hu hv x) = π ⟨S.ν i n ⊗ₜ x, hx⟩) →
    Tens O f := by
  intro O A G _ _ _ _ _ _ I γ m S u v M _ _ M' _ θ h0 π hπ hker f hf0 hf
  classical
  obtain ⟨g₀, hs, hm⟩ := GlobalTheory.T.graded_splitting_tensor_filtration (Γ := G) γ m S
  let t : ∀ i : Fin m, S.N i ⊗[O] M i →+ S.N i ⊗[O] G := fun i =>
    if h : u ≤ (i : ℕ) ∧ (i : ℕ) < v then
      ((LinearEquiv.lTensor (S.N i) (θ i h.1 h.2)).symm : S.N i ⊗[O] M i ≃ₗ[O] S.N i ⊗[O] G).toLinearMap.toAddMonoidHom
    else 0
  have t_act : ∀ (i : Fin m) (h : u ≤ (i : ℕ) ∧ (i : ℕ) < v) (a : S.N i ⊗[O] G),
      t i (LinearEquiv.lTensor (S.N i) (θ i h.1 h.2) a) = a := by
    intro i h a
    simp only [t, dif_pos h]
    exact (LinearEquiv.lTensor (S.N i) (θ i h.1 h.2)).symm_apply_apply a
  have t_inact : ∀ (i : Fin m), ¬ (u ≤ (i : ℕ) ∧ (i : ℕ) < v) → t i = 0 := by
    intro i h
    simp only [t, dif_neg h]
  let T : (∀ i, S.N i ⊗[O] M i) →+ (∀ i, S.N i ⊗[O] G) :=
    { toFun := fun w i => t i (w i)
      map_zero' := by funext i; simp
      map_add' := fun a b => by funext i; simp }
  have T_apply : ∀ w i, T w i = t i (w i) := fun _ _ => rfl
  have hT : ∀ w, g₀ (T w) ∈ (pdP γ u).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G)) := by
    intro w
    refine (hm u _).2 fun i hi => ?_
    rw [T_apply, t_inact i (by omega)]
    rfl
  let φ : (∀ i, S.N i ⊗[O] M i) →+ M' :=
    { toFun := fun w => π ⟨g₀ (T w), hT w⟩
      map_zero' := by
        have : (⟨g₀ (T 0), hT 0⟩ : ((pdP γ u).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G)) : Ideal (A ⊗[O] G))) = 0 :=
          Subtype.ext (by simp)
        rw [this, map_zero]
      map_add' := fun a b => by
        rw [← map_add]
        exact congrArg π (Subtype.ext (by simp)) }
  have φ_apply : ∀ w, φ w = π ⟨g₀ (T w), hT w⟩ := fun _ => rfl
  have inj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun w hw => ?_
    rw [φ_apply] at hw
    have h1 := (hm v _).1 ((hker _).1 hw)
    funext i
    by_cases h : u ≤ (i : ℕ) ∧ (i : ℕ) < v
    · have h2 := h1 i h.2
      rw [T_apply] at h2
      obtain ⟨a, ha⟩ := (LinearEquiv.lTensor (S.N i) (θ i h.1 h.2)).surjective (w i)
      rw [← ha, t_act i h] at h2
      rw [← ha, h2, map_zero]
      rfl
    · haveI := h0 i h
      exact subsingleton_tmul _
  have surj : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := hπ y
    obtain ⟨z, hz⟩ := g₀.surjective x.1
    have hzu := (hm u z).1 (by rw [hz]; exact x.2)
    let w : ∀ i, S.N i ⊗[O] M i := fun i =>
      if h : u ≤ (i : ℕ) ∧ (i : ℕ) < v then LinearEquiv.lTensor (S.N i) (θ i h.1 h.2) (z i) else 0
    refine ⟨w, ?_⟩
    rw [φ_apply, ← sub_eq_zero, ← map_sub, hker]
    have : ((⟨g₀ (T w), hT w⟩ - x : ((pdP γ u).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G)) : Ideal (A ⊗[O] G))) : A ⊗[O] G)
        = g₀ (T w - z) := by
      rw [map_sub, hz]
      rfl
    rw [this, hm]
    intro i hi
    rw [Pi.sub_apply, T_apply, sub_eq_zero]
    by_cases h : u ≤ (i : ℕ)
    · have h' : u ≤ (i : ℕ) ∧ (i : ℕ) < v := ⟨h, hi⟩
      simp only [w, dif_pos h']
      exact t_act i h' _
    · rw [t_inact i (by omega), hzu i (by omega)]
      rfl
  refine ⟨AddEquiv.ofBijective φ ⟨inj, surj⟩, fun i n x => ?_⟩
  rw [AddEquiv.ofBijective_apply]
  by_cases h : u ≤ (i : ℕ) ∧ (i : ℕ) < v
  · obtain ⟨y, rfl⟩ := (θ i h.1 h.2).surjective x
    have hTs : T (Pi.single i (n ⊗ₜ[O] θ i h.1 h.2 y)) = Pi.single i (n ⊗ₜ[O] y) := by
      funext j
      by_cases hj : j = i
      · subst hj
        rw [T_apply, Pi.single_eq_same, Pi.single_eq_same]
        exact t_act j h (n ⊗ₜ[O] y)
      · rw [T_apply, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, map_zero]
    have hx : S.ν i n ⊗ₜ[O] y ∈ (pdP γ u).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G)) := by
      rw [← hs, ← hTs]
      exact hT _
    rw [hf i n y h.1 h.2 hx, φ_apply]
    exact congrArg π (Subtype.ext (by simp only [hTs, hs]))
  · haveI := h0 i h
    rw [Subsingleton.elim x 0, TensorProduct.tmul_zero, Pi.single_zero, map_zero, hf0]

end GlobalTheory.CompanionTheory.GrPiece
