import Development.AutomorphicSpectrum.Proofs.MembershipProofs.RationalUnitsHaarCharacterOne

open Matrix GlobalTheory.WeilM GlobalTheory.CompanionTheory.ThetaAvg
open scoped Classical

noncomputable section

namespace PositivityTheory.ThKF0.LagAlg

variable {F : Type} [Field F] {κ : Type} [Fintype κ]

/- English proof (translation)
Set `g` to `(LinearMap.fst F (κ → F) (κ → F)) ∘ₗ L.subtype`. Take `⟨r, hr⟩` from `g.rangeRestrict.exists_rightInverse_of_surjective g.range_rangeRestrict`. Take `⟨π', hπ'⟩` from `(LinearMap.range g).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)`. Set `s` to `L.subtype ∘ₗ r ∘ₗ π'`. Establish `hs : ∀ x, s x ∈ L` using `fun x => (r (π' x)).2`.

Establish `hs1 : ∀ x, (s x).1 = (π' x : κ → F)` using `fun x => congrArg Subtype.val (LinearMap.congr_fun hr (π' x))`. Establish `hfix : ∀ w ∈ L, (s w.1).1 = w.1` using `fun w hw => by`. Rewrite using `[hs1]`. Conclude with `congrArg Subtype.val (LinearMap.congr_fun hπ' ⟨w.1, ⟨w, hw⟩, rfl⟩)`. Set `P` to `LinearMap.toMatrix' (LinearMap.fst F _ _ ∘ₗ s)`.

Set `β` to `LinearMap.toMatrix' (LinearMap.snd F _ _ ∘ₗ s)`. Establish `hP : ∀ x, P *ᵥ x = (s x).1` using `fun x => LinearMap.toMatrix'_mulVec _ x`. Establish `hβ : ∀ x, β *ᵥ x = (s x).2` using `fun x => LinearMap.toMatrix'_mulVec _ x`. Establish `hPP : P * P = P`. Use `Matrix.toLin'.injective (LinearMap.ext fun x => ?_)` and prove the remaining obligations.

Simplify using `only [Matrix.toLin'_apply, ← mulVec_mulVec]`. Rewrite using `[hP x, hP, hfix _ (hs x)]`. Establish `hsym : ∀ x y, x ⬝ᵥ (Pᵀ * β) *ᵥ y = y ⬝ᵥ (Pᵀ * β) *ᵥ x` using `fun x y => by`. Simplify using `only [← mulVec_mulVec, dotProduct_mulVec _ Pᵀ, vecMul_transpose, hP, hβ]`. Conclude with `(hL _).1 (hs x) _ (hs y)`.

Establish `hd : ∀ y, ((0 : Matrix κ κ F) *ᵥ y, (1 - P)ᵀ *ᵥ y) ∈ L` using `fun y => (hL _).2 fun w hw => by`. Simplify using `only [zero_mulVec, zero_dotProduct, dotProduct_mulVec _ (1 - P)ᵀ, vecMul_transpose, sub_mulVec, one_mulVec, hP, hfix w hw, sub_self]`. Use `⟨P, Pᵀ * β, hPP, ?_, fun x => ?_, hd⟩` and prove the remaining obligations. Use extensionality with `i j`. Use `hsym (Pi.single j 1) (Pi.single i 1)` as an intermediate fact.

Simplify `this` using `[single_dotProduct, mulVec_single_one]`. Establish `h1` using `L.sub_mem (hs (P *ᵥ x)) (hd (β *ᵥ (P *ᵥ x)))`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Prod.fst_sub, ← hP, mulVec_mulVec, hPP, zero_mulVec, sub_zero]`.

Rewrite using `[Prod.snd_sub, ← hβ]`. Simplify using `[← mulVec_mulVec, sub_mulVec]`.
-/
theorem exists_mats (L : Submodule F ((κ → F) × (κ → F))) (hL : ∀ a, a ∈ L ↔ ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) :
    ∃ P b : Matrix κ κ F, P * P = P ∧ bᵀ = b ∧ (∀ x, (P *ᵥ x, (b * P) *ᵥ x) ∈ L) ∧
      ∀ y, ((0 : Matrix κ κ F) *ᵥ y, (1 - P)ᵀ *ᵥ y) ∈ L := by
  let g := (LinearMap.fst F (κ → F) (κ → F)) ∘ₗ L.subtype
  obtain ⟨r, hr⟩ := g.rangeRestrict.exists_rightInverse_of_surjective g.range_rangeRestrict
  obtain ⟨π', hπ'⟩ := (LinearMap.range g).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  let s := L.subtype ∘ₗ r ∘ₗ π'
  have hs : ∀ x, s x ∈ L := fun x => (r (π' x)).2
  have hs1 : ∀ x, (s x).1 = (π' x : κ → F) := fun x => congrArg Subtype.val (LinearMap.congr_fun hr (π' x))
  have hfix : ∀ w ∈ L, (s w.1).1 = w.1 := fun w hw => by
    rw [hs1]
    exact congrArg Subtype.val (LinearMap.congr_fun hπ' ⟨w.1, ⟨w, hw⟩, rfl⟩)
  let P := LinearMap.toMatrix' (LinearMap.fst F _ _ ∘ₗ s)
  let β := LinearMap.toMatrix' (LinearMap.snd F _ _ ∘ₗ s)
  have hP : ∀ x, P *ᵥ x = (s x).1 := fun x => LinearMap.toMatrix'_mulVec _ x
  have hβ : ∀ x, β *ᵥ x = (s x).2 := fun x => LinearMap.toMatrix'_mulVec _ x
  have hPP : P * P = P := by
    refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
    simp only [Matrix.toLin'_apply, ← mulVec_mulVec]
    rw [hP x, hP, hfix _ (hs x)]
  have hsym : ∀ x y, x ⬝ᵥ (Pᵀ * β) *ᵥ y = y ⬝ᵥ (Pᵀ * β) *ᵥ x := fun x y => by
    simp only [← mulVec_mulVec, dotProduct_mulVec _ Pᵀ, vecMul_transpose, hP, hβ]
    exact (hL _).1 (hs x) _ (hs y)
  have hd : ∀ y, ((0 : Matrix κ κ F) *ᵥ y, (1 - P)ᵀ *ᵥ y) ∈ L := fun y => (hL _).2 fun w hw => by
    simp only [zero_mulVec, zero_dotProduct, dotProduct_mulVec _ (1 - P)ᵀ, vecMul_transpose, sub_mulVec, one_mulVec, hP,
      hfix w hw, sub_self]
  refine ⟨P, Pᵀ * β, hPP, ?_, fun x => ?_, hd⟩
  · ext i j
    have := hsym (Pi.single j 1) (Pi.single i 1)
    simpa [single_dotProduct, mulVec_single_one] using this
  · have h1 := L.sub_mem (hs (P *ᵥ x)) (hd (β *ᵥ (P *ᵥ x)))
    convert h1 using 1
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sub, ← hP, mulVec_mulVec, hPP, zero_mulVec, sub_zero]
    · rw [Prod.snd_sub, ← hβ]
      simp [← mulVec_mulVec, sub_mulVec]

/- English proof (translation)
Set `u : κ → (κ → F) × (κ → F)` to `fun i => (C *ᵥ Pi.single i 1, D *ᵥ Pi.single i 1)`. Establish `e : (C.map (algebraMap F R) *ᵥ x, D.map (algebraMap F R) *ᵥ x) = ∑ i, x i • emb R (u i)`. Apply the tactic sequence `refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>`. Simplify using `[u, emb_apply, Prod.fst_sum, Prod.snd_sum, mulVec, dotProduct, mul_comm, Pi.single_apply]`. Rewrite using `[e]`.

Proceed by induction on `(Finset.univ : Finset κ) using Finset.induction_on with`. Consider the case `empty => intro φ _`. Rewrite using `[Finset.sum_empty, schr_zero]`. Consider the case `insert i s hi ih`. Introduce `φ hφ`.

Establish `h0 : omL R κ (x i • emb R (u i)) (∑ j ∈ s, x j • emb R (u j)) = 0`. Rewrite using `[map_sum]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, map_smul, LinearMap.smul_apply, omL_emb, omL_apply, hL (u i) (hCD _) (u j) (hCD _)]`. Simplify using the standard rewrite rules.

Establish `h1` using `schr_schr ψ (x i • emb R (u i)) (∑ j ∈ s, x j • emb R (u j)) φ`. Rewrite `h1` using `[h0, mul_zero, AddChar.map_zero_eq_one, one_smul]`. Rewrite using `[Finset.sum_insert hi, ← h1, hl _ _ (hCD _) _ (hS _ _ hφ), ih φ hφ]`.
-/
theorem inv_of_mem {R : Type} [CommRing R] [Algebra F R] [Invertible (2 : R)] (ψ : AddChar R ℂ)
    (S : Set ((κ → R) → ℂ)) (hS : ∀ w, ∀ φ ∈ S, schr ψ w φ ∈ S) (l : ((κ → R) → ℂ) →ₗ[ℂ] ℂ)
    (L : Submodule F ((κ → F) × (κ → F))) (hL : ∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2)
    (hl : ∀ (t : R), ∀ w ∈ L, ∀ φ ∈ S, l (schr ψ (t • emb R w) φ) = l φ)
    (C D : Matrix κ κ F) (hCD : ∀ x, (C *ᵥ x, D *ᵥ x) ∈ L) (x : κ → R) :
    ∀ φ ∈ S, l (schr ψ (C.map (algebraMap F R) *ᵥ x, D.map (algebraMap F R) *ᵥ x) φ) = l φ := by
  let u : κ → (κ → F) × (κ → F) := fun i => (C *ᵥ Pi.single i 1, D *ᵥ Pi.single i 1)
  have e : (C.map (algebraMap F R) *ᵥ x, D.map (algebraMap F R) *ᵥ x) = ∑ i, x i • emb R (u i) := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
      simp [u, emb_apply, Prod.fst_sum, Prod.snd_sum, mulVec, dotProduct, mul_comm, Pi.single_apply]
  rw [e]
  induction (Finset.univ : Finset κ) using Finset.induction_on with
  | empty => intro φ _; rw [Finset.sum_empty, schr_zero]
  | insert i s hi ih =>
    intro φ hφ
    have h0 : omL R κ (x i • emb R (u i)) (∑ j ∈ s, x j • emb R (u j)) = 0 := by
      rw [map_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_smul, map_smul, LinearMap.smul_apply, omL_emb, omL_apply, hL (u i) (hCD _) (u j) (hCD _)]
      simp
    have h1 := schr_schr ψ (x i • emb R (u i)) (∑ j ∈ s, x j • emb R (u j)) φ
    rw [h0, mul_zero, AddChar.map_zero_eq_one, one_smul] at h1
    rw [Finset.sum_insert hi, ← h1, hl _ _ (hCD _) _ (hS _ _ hφ), ih φ hφ]

end PositivityTheory.ThKF0.LagAlg
