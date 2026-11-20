import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealConeCoveredByStarAtPointStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

noncomputable section

namespace GlobalTheory.PolFan

/- English proof (translation)
Take `⟨c, hc, hβ⟩` from `h`. Establish `hj : ∀ i, ∃ j, γ' j = γ i` using `fun i => hsub ⟨i, rfl⟩`. Use `choose j hj using hj`. Use `⟨fun k => ∑ i, if j i = k then c i else 0, fun k => Finset.sum_nonneg fun i _ => by split_ifs` and prove the remaining obligations. Conclude with `hc i`.

Conclude with `le_refl 0, ?_⟩`. Rewrite using `[hβ]`. Simplify using `only [Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_eq_single (j i) (fun k _ hk => by rw [if_neg (Ne.symm hk), zero_smul]) (by simp), if_pos rfl, hj]`.
-/
theorem inRCone_of_range_subset {X : Type} [AddCommGroup X] {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    {γ' : Fin m' → LinearMap.BilinForm ℤ X} (hsub : Set.range γ ⊆ Set.range γ') {β : LinearMap.BilinForm ℤ X}
    (h : InRCone γ β) : InRCone γ' β := by
  classical
  obtain ⟨c, hc, hβ⟩ := h
  have hj : ∀ i, ∃ j, γ' j = γ i := fun i => hsub ⟨i, rfl⟩
  choose j hj using hj
  refine ⟨fun k => ∑ i, if j i = k then c i else 0, fun k => Finset.sum_nonneg fun i _ => by
    split_ifs
    · exact hc i
    · exact le_refl 0, ?_⟩
  rw [hβ]
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (j i) (fun k _ hk => by rw [if_neg (Ne.symm hk), zero_smul]) (by simp), if_pos rfl, hj]

/- English proof (translation)
Rewrite using `[← evalR_toReal]`. Establish `: toReal (0 : LinearMap.BilinForm ℤ X) = 0` using `LinearMap.ext₂ fun a b => by simp`. Rewrite using `[this, evalR_zero]`.
-/
theorem evalZ_zero_form {O : Type} [CommRing O] (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] : φ.evalZ (0 : LinearMap.BilinForm ℤ X) = 0 := by
  rw [← evalR_toReal]
  have : toReal (0 : LinearMap.BilinForm ℤ X) = 0 := LinearMap.ext₂ fun a b => by simp
  rw [this, evalR_zero]

/- English proof (translation)
Introduce `E _ _ _ H q ψ w ψ' hψ hw hst X _ _ _ _ hX`. Take `⟨S, hS, hcov⟩` from `(hψ X hX).finite`. Take `⟨hw1, -, hw3⟩` from `hw X hX`. Set `C : Set (LinearMap.BilinForm ℤ X)` to `{v | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ (∀ i, γ i ∈ S) ∧ v ∈ balForms H.bar X ∧ (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ InRCone γ v}`. Set `CT : Set (LinearMap.BilinForm ℤ X) → Set (LinearMap.BilinForm ℤ X)` to `fun T => {v | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ Set.range γ = T ∧ v ∈ balForms H.bar X ∧ (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ InRCone γ v}`.

Establish `hCT : ∀ T, (CT T).Subsingleton`. Introduce and unpack `T v₁ ⟨m₁, γ₁, hγ₁, hr₁, hb₁, hp₁, hv₁, hi₁⟩ v₂ ⟨m₂, γ₂, hγ₂, hr₂, hb₂, hp₂, hv₂, hi₂⟩`. Conclude with `hw3 m₁ γ₁ hγ₁ v₁ hb₁ hp₁ v₂ hb₂ hp₂ hv₁ hv₂ hi₁ (inRCone_of_range_subset (by rw [hr₁, hr₂]) hi₂)`. Establish `hC : C.Finite`. Use `(hS.powerset.biUnion fun T _ => (hCT T).finite).subset ?_` and prove the remaining obligations.

Introduce and unpack `v ⟨m, γ, hγ, hγS, hb, hp, hv, hi⟩`. Use `Set.mem_biUnion (x := Set.range γ) ?_ ⟨m, γ, hγ, rfl, hb, hp, hv, hi⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hγS i`. Use `⟨S ∪ C, hS.union hC, fun B hB => ?_⟩` and prove the remaining obligations.

Take `⟨e, m, γ, c, hγ, hγS, hc, hBc⟩` from `hcov B hB`. Distinguish the cases in `hex : ∃ v ∈ balForms H.bar X, (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ InRCone γ v`. Take `⟨v, hb, hp, hv, hi⟩` from `hex`. Establish `hv0 : v ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hv` using `[evalZ_zero_form]`. Conclude with `zero_ne_one hv`. Take `⟨m', s, h, hcut, hpos, t, ht, hBt⟩` from `GlobalTheory.T.realCone_covered_by_star_at_point X m γ v (pullR e.toLinearMap B) (fun i y z => (hγ.mem i).1 y z) hγ.nonneg hv0 hi ⟨c, hc, hBc⟩`. Use `⟨e, m' + 1, Fin.cons v fun j => γ (s j), t, hst.2.1 X hX m γ hγ v hb hp hv hi m' s h hcut hpos, fun i => ?_, ht, hBt⟩` and prove the remaining obligations. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations.

Conclude with `Or.inr ⟨m, γ, hγ, hγS, hb, hp, hv, hi⟩`. Simplify using `only [Fin.cons_succ]`. Conclude with `Or.inl (hγS (s j))`. Use `⟨e, m, γ, c, hst.1 X hX m γ hγ fun β hb hp hi => ?_, fun i => Or.inl (hγS i), hc, hBc⟩` and prove the remaining obligations. Break down `hw1 β hb hp with h0 | h1` into its components or cases.

Conclude with `h0`. Conclude with `(hex ⟨β, hb, hp, h1, hi⟩).elim`.
-/
theorem isStarOf_finite_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (ψ w ψ' : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → IsStarOf H.bar q ψ w ψ' →
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
    Module.finrank (𝓞 E) X ≤ q → ∃ S : Set (LinearMap.BilinForm ℤ X), S.Finite ∧ ∀ B ∈ psdCone H.bar X,
      ∃ (e : X ≃ₗ[𝓞 E] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell H.bar ψ' γ ∧
        (∀ i, γ i ∈ S) ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i) := by
  intro E _ _ _ H q ψ w ψ' hψ hw hst X _ _ _ _ hX
  obtain ⟨S, hS, hcov⟩ := (hψ X hX).finite
  obtain ⟨hw1, -, hw3⟩ := hw X hX

  let C : Set (LinearMap.BilinForm ℤ X) := {v | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧
    (∀ i, γ i ∈ S) ∧ v ∈ balForms H.bar X ∧ (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ InRCone γ v}
  let CT : Set (LinearMap.BilinForm ℤ X) → Set (LinearMap.BilinForm ℤ X) := fun T =>
    {v | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ Set.range γ = T ∧
      v ∈ balForms H.bar X ∧ (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ InRCone γ v}
  have hCT : ∀ T, (CT T).Subsingleton := by
    rintro T v₁ ⟨m₁, γ₁, hγ₁, hr₁, hb₁, hp₁, hv₁, hi₁⟩ v₂ ⟨m₂, γ₂, hγ₂, hr₂, hb₂, hp₂, hv₂, hi₂⟩
    exact hw3 m₁ γ₁ hγ₁ v₁ hb₁ hp₁ v₂ hb₂ hp₂ hv₁ hv₂ hi₁
      (inRCone_of_range_subset (by rw [hr₁, hr₂]) hi₂)
  have hC : C.Finite := by
    refine (hS.powerset.biUnion fun T _ => (hCT T).finite).subset ?_
    rintro v ⟨m, γ, hγ, hγS, hb, hp, hv, hi⟩
    refine Set.mem_biUnion (x := Set.range γ) ?_ ⟨m, γ, hγ, rfl, hb, hp, hv, hi⟩
    rintro _ ⟨i, rfl⟩
    exact hγS i
  refine ⟨S ∪ C, hS.union hC, fun B hB => ?_⟩
  obtain ⟨e, m, γ, c, hγ, hγS, hc, hBc⟩ := hcov B hB
  by_cases hex : ∃ v ∈ balForms H.bar X, (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ InRCone γ v
  · obtain ⟨v, hb, hp, hv, hi⟩ := hex
    have hv0 : v ≠ 0 := by
      rintro rfl
      rw [evalZ_zero_form] at hv
      exact zero_ne_one hv
    obtain ⟨m', s, h, hcut, hpos, t, ht, hBt⟩ :=
      GlobalTheory.T.realCone_covered_by_star_at_point X m γ v (pullR e.toLinearMap B) (fun i y z => (hγ.mem i).1 y z) hγ.nonneg hv0 hi ⟨c, hc, hBc⟩
    refine ⟨e, m' + 1, Fin.cons v fun j => γ (s j), t,
      hst.2.1 X hX m γ hγ v hb hp hv hi m' s h hcut hpos, fun i => ?_, ht, hBt⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Or.inr ⟨m, γ, hγ, hγS, hb, hp, hv, hi⟩
    · simp only [Fin.cons_succ]
      exact Or.inl (hγS (s j))
  · refine ⟨e, m, γ, c, hst.1 X hX m γ hγ fun β hb hp hi => ?_, fun i => Or.inl (hγS i), hc, hBc⟩
    rcases hw1 β hb hp with h0 | h1
    · exact h0
    · exact (hex ⟨β, hb, hp, h1, hi⟩).elim

end GlobalTheory.PolFan
