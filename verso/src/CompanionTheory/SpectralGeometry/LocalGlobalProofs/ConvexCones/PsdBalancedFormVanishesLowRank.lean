import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellLeastDimVanishesWhereFormVanishesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkValEqZeroOrOne
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CellFaceRestrictionStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark GlobalTheory.CompanionTheory.Ar.Fan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fan.VanishingInRationalCone

/- English proof (translation)
Introduce `O _ _ _ _ bar hb q ψ lab hψ hlab X _ _ _ _ hX hdom m τ hτ β hβ hβp hβc hrk j y hy`. Set `P : Fin m → Prop` to `fun j => ∀ y, β y y = 0 → τ j y y = 0`. Establish `hw : ∀ j, ∃ y, β y y = 0 ∧ (¬ P j → 0 < τ j y y)`. Introduce `j`. Distinguish the cases in `hj : P j`.

Conclude with `⟨0, by simp, fun h => (h hj).elim⟩`. Simplify using `only [P, not_forall] at hj`. Take `⟨y, hy, hne⟩` from `hj`. Conclude with `⟨y, hy, fun _ => lt_of_le_of_ne (hτ.nonneg j y) (Ne.symm hne)⟩`. Use `choose w hw0 hwpos using hw`.

Set `T : Finset (Fin m)` to `Finset.univ.filter P`. Set `s : Fin T.card ↪ Fin m` to `(T.orderEmbOfFin rfl).toEmbedding`. Establish `hsr : Set.range s = ↑T` using `Finset.range_orderEmbOfFin T rfl`. Establish `hP : ∀ k, P k ↔ k ∈ Set.range s` using `fun k => by rw [hsr]; simp [T]`. Set `hf : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ` to `∑ i, LinearMap.applyₗ (w i) ∘ₗ LinearMap.applyₗ (w i)`.

Establish `hfa : ∀ x : LinearMap.BilinForm ℤ X, hf x = ∑ i, x (w i) (w i)` using `fun x => by`. Simplify using `[hf, LinearMap.sum_apply]`. Establish `hcut : IsFaceCut τ s hf`. Use `⟨fun k => ?_, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[hfa]`.

Conclude with `Finset.sum_nonneg fun i _ => hτ.nonneg k (w i)`. Rewrite using `[← hP, hfa]`. Prove the components needed by the constructor for the conclusion. Introduce `h0`. Assume the negation of the conclusion as `hk`.

Establish `h1 : τ k (w k) (w k) ≤ ∑ i, τ k (w i) (w i)` using `Finset.single_le_sum (f := fun i => τ k (w i) (w i)) (fun i _ => hτ.nonneg k (w i)) (Finset.mem_univ k)`. Establish `h2` using `hwpos k hk`. Use linear arithmetic over natural numbers and integers. Introduce `hk`. Conclude with `Finset.sum_eq_zero fun i _ => hk _ (hw0 i)`.

Establish `hcell : IsCell bar ψ (fun k => τ (s k))` using `GlobalTheory.T.cell_face_restriction O bar hb q ψ hψ X hX hdom m τ hτ _ s hf hcut`. Take `⟨c, hc, hce⟩` from `hβc`. Establish `hc0 : ∀ i, ¬ P i → c i = 0`. Introduce `i hi`. Establish `e : (β (w i) (w i) : ℝ) = ∑ k, c k * (τ k (w i) (w i) : ℝ)`.

Use `LinearMap.congr_fun₂ hce (w i) (w i)` as an intermediate fact. Simplify `this` using `[LinearMap.sum_apply]`. Rewrite `e` using `[hw0 i, Int.cast_zero]`. Establish `h1 : c i * (τ i (w i) (w i) : ℝ) ≤ ∑ k, c k * (τ k (w i) (w i) : ℝ)` using `Finset.single_le_sum (f := fun k => c k * (τ k (w i) (w i) : ℝ)) (fun k _ => mul_nonneg (hc k) (by exact_mod_cast hτ.nonneg k (w i))) (Finset.mem_univ i)`. Establish `h2 : (0 : ℝ) < τ i (w i) (w i)` using `by exact_mod_cast hwpos i hi`.

Rewrite `h1` using `[← e]`. Use polynomial arithmetic with `[hc i]`. Establish `hmap : Finset.univ.map s = T`. Use extensionality with `i`. Simplify using `only [Finset.mem_map, Finset.mem_univ, true_and]`.

Rewrite using `[← Set.mem_range, ← hP]`. Simplify using `[T]`. Establish `hcone : InRCone (fun k => τ (s k)) β`. Use `⟨fun k => c (s k), fun k => hc _, ?_⟩` and prove the remaining obligations. Rewrite using `[hce]`.

Establish `e1` using `Finset.sum_map Finset.univ s (fun i => c i • toReal (τ i))`. Rewrite `e1` using `[hmap]`. Rewrite using `[← e1]`. Use `(Finset.sum_subset (Finset.subset_univ T) fun i _ hi => ?_).symm` and prove the remaining obligations. Rewrite using `[hc0 i (by simpa [T] using hi), zero_smul]`.

Establish `hl` using `hlab X hX β hβ hβp`. Establish `hle : sInf {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ β ∧ genRank γ = k} ≤ genRank (fun k => τ (s k))` using `Nat.sInf_le ⟨_, _, hcell, hcone, rfl⟩`. Establish `hrk' : genRank τ ≤ genRank (fun k => τ (s k))`. Rewrite `hrk` using `[hl]`. Establish `h4 : ((genRank τ : ℕ) : ℝ) ≤ ((genRank (fun k => τ (s k)) : ℕ) : ℝ)` using `hrk.trans (Nat.cast_le.2 hle)`.

Conclude with `h4` after adjusting the coercions. Use `haveI : Module.Finite ℤ (Submodule.span ℤ (Set.range τ)) := Module.Finite.span_of_finite ℤ (Set.finite_range τ)`. Establish `hNL : Submodule.span ℤ (Set.range fun k => τ (s k)) ≤ Submodule.span ℤ (Set.range τ)` using `Submodule.span_mono (Set.range_comp_subset_range s τ)`. Take `⟨n, hn, hnmem⟩` from `exists_zsmul_mem_of_finrank_le_of_le hNL hrk' (Submodule.subset_span ⟨j, rfl⟩)`. Establish `key : ∀ x ∈ Submodule.span ℤ (Set.range fun k => τ (s k)), x y y = 0` using `fun x hx => by`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨k, rfl⟩` from `hx`. Conclude with `(hP (s k)).2 ⟨k, rfl⟩ y hy`. Consider the case `zero => simp`.

Consider the case `add x z _ _ h1 h2 => simp [h1, h2]`. Consider the case `smul a x _ h => simp [h]`. Establish `h3` using `key _ hnmem`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul] at h3`. Conclude with `(mul_eq_zero.1 h3).resolve_left hn`.
-/
theorem vanish_of_inRCone_of_genRank_le : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ lab : InvFun O), IsPolyFan bar q ψ → IsCarrierDim bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → Dominates bar X → ∀ (m : ℕ) (τ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ τ → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone τ β → (genRank τ : ℝ) ≤ lab.evalZ β → ∀ j y, β y y = 0 → τ j y y = 0 := by
  intro O _ _ _ _ bar hb q ψ lab hψ hlab X _ _ _ _ hX hdom m τ hτ β hβ hβp hβc hrk j y hy
  classical
  let P : Fin m → Prop := fun j => ∀ y, β y y = 0 → τ j y y = 0
  have hw : ∀ j, ∃ y, β y y = 0 ∧ (¬ P j → 0 < τ j y y) := by
    intro j
    by_cases hj : P j
    · exact ⟨0, by simp, fun h => (h hj).elim⟩
    · simp only [P, not_forall] at hj
      obtain ⟨y, hy, hne⟩ := hj
      exact ⟨y, hy, fun _ => lt_of_le_of_ne (hτ.nonneg j y) (Ne.symm hne)⟩
  choose w hw0 hwpos using hw
  let T : Finset (Fin m) := Finset.univ.filter P
  let s : Fin T.card ↪ Fin m := (T.orderEmbOfFin rfl).toEmbedding
  have hsr : Set.range s = ↑T := Finset.range_orderEmbOfFin T rfl
  have hP : ∀ k, P k ↔ k ∈ Set.range s := fun k => by rw [hsr]; simp [T]
  let hf : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := ∑ i, LinearMap.applyₗ (w i) ∘ₗ LinearMap.applyₗ (w i)
  have hfa : ∀ x : LinearMap.BilinForm ℤ X, hf x = ∑ i, x (w i) (w i) := fun x => by
    simp [hf, LinearMap.sum_apply]
  have hcut : IsFaceCut τ s hf := by
    refine ⟨fun k => ?_, fun k => ?_⟩
    · rw [hfa]; exact Finset.sum_nonneg fun i _ => hτ.nonneg k (w i)
    · rw [← hP, hfa]
      constructor
      · intro h0
        by_contra hk
        have h1 : τ k (w k) (w k) ≤ ∑ i, τ k (w i) (w i) :=
          Finset.single_le_sum (f := fun i => τ k (w i) (w i)) (fun i _ => hτ.nonneg k (w i)) (Finset.mem_univ k)
        have h2 := hwpos k hk
        omega
      · intro hk
        exact Finset.sum_eq_zero fun i _ => hk _ (hw0 i)
  have hcell : IsCell bar ψ (fun k => τ (s k)) :=
    GlobalTheory.T.cell_face_restriction O bar hb q ψ hψ X hX hdom m τ hτ _ s hf hcut
  obtain ⟨c, hc, hce⟩ := hβc
  have hc0 : ∀ i, ¬ P i → c i = 0 := by
    intro i hi
    have e : (β (w i) (w i) : ℝ) = ∑ k, c k * (τ k (w i) (w i) : ℝ) := by
      have := LinearMap.congr_fun₂ hce (w i) (w i)
      simpa [LinearMap.sum_apply] using this
    rw [hw0 i, Int.cast_zero] at e
    have h1 : c i * (τ i (w i) (w i) : ℝ) ≤ ∑ k, c k * (τ k (w i) (w i) : ℝ) :=
      Finset.single_le_sum (f := fun k => c k * (τ k (w i) (w i) : ℝ))
        (fun k _ => mul_nonneg (hc k) (by exact_mod_cast hτ.nonneg k (w i))) (Finset.mem_univ i)
    have h2 : (0 : ℝ) < τ i (w i) (w i) := by exact_mod_cast hwpos i hi
    rw [← e] at h1
    nlinarith [hc i]
  have hmap : Finset.univ.map s = T := by
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    rw [← Set.mem_range, ← hP]
    simp [T]
  have hcone : InRCone (fun k => τ (s k)) β := by
    refine ⟨fun k => c (s k), fun k => hc _, ?_⟩
    rw [hce]
    have e1 := Finset.sum_map Finset.univ s (fun i => c i • toReal (τ i))
    rw [hmap] at e1
    rw [← e1]
    refine (Finset.sum_subset (Finset.subset_univ T) fun i _ hi => ?_).symm
    rw [hc0 i (by simpa [T] using hi), zero_smul]
  have hl := hlab X hX β hβ hβp
  have hle : sInf {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ β ∧
      genRank γ = k} ≤ genRank (fun k => τ (s k)) := Nat.sInf_le ⟨_, _, hcell, hcone, rfl⟩
  have hrk' : genRank τ ≤ genRank (fun k => τ (s k)) := by
    rw [hl] at hrk
    have h4 : ((genRank τ : ℕ) : ℝ) ≤ ((genRank (fun k => τ (s k)) : ℕ) : ℝ) := hrk.trans (Nat.cast_le.2 hle)
    exact_mod_cast h4
  haveI : Module.Finite ℤ (Submodule.span ℤ (Set.range τ)) := Module.Finite.span_of_finite ℤ (Set.finite_range τ)
  have hNL : Submodule.span ℤ (Set.range fun k => τ (s k)) ≤ Submodule.span ℤ (Set.range τ) :=
    Submodule.span_mono (Set.range_comp_subset_range s τ)
  obtain ⟨n, hn, hnmem⟩ := exists_zsmul_mem_of_finrank_le_of_le hNL hrk' (Submodule.subset_span ⟨j, rfl⟩)
  have key : ∀ x ∈ Submodule.span ℤ (Set.range fun k => τ (s k)), x y y = 0 := fun x hx => by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact (hP (s k)).2 ⟨k, rfl⟩ y hy
    | zero => simp
    | add x z _ _ h1 h2 => simp [h1, h2]
    | smul a x _ h => simp [h]
  have h3 := key _ hnmem
  simp only [LinearMap.smul_apply, smul_eq_mul] at h3
  exact (mul_eq_zero.1 h3).resolve_left hn

end GlobalTheory.CompanionTheory.Ar.Fan.VanishingInRationalCone
