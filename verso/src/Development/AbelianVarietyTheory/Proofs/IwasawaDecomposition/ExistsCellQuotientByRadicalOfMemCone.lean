import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullLinInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim

namespace GlobalTheory.PolFan.CarDim

section Descend

variable {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X]

/- English proof (translation)
Set `e` to `Submodule.Quotient.restrictScalarsEquiv ℤ K`. Set `g` to `LinearMap.liftQ₂ (K.restrictScalars ℤ) (K.restrictScalars ℤ) f (fun x hx => LinearMap.ext fun y => h1 x hx y) (fun y hy => LinearMap.ext fun x => h2 x y hy)`. Use `⟨g.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap, LinearMap.ext₂ fun a b => ?_⟩` and prove the remaining obligations. Simplify using `[pull_apply, e, g]`. Both sides reduce to the same expression.
-/
theorem exists_pull_mkQ_eq_of_vanish (K : Submodule O X) (f : LinearMap.BilinForm ℤ X)
    (h1 : ∀ x ∈ K, ∀ y, f x y = 0) (h2 : ∀ x, ∀ y ∈ K, f x y = 0) :
    ∃ δ : LinearMap.BilinForm ℤ (X ⧸ K), pull K.mkQ δ = f := by
  let e := Submodule.Quotient.restrictScalarsEquiv ℤ K
  let g := LinearMap.liftQ₂ (K.restrictScalars ℤ) (K.restrictScalars ℤ) f
    (fun x hx => LinearMap.ext fun y => h1 x hx y) (fun y hy => LinearMap.ext fun x => h2 x y hy)
  refine ⟨g.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap, LinearMap.ext₂ fun a b => ?_⟩
  simp [pull_apply, e, g]
  rfl

end Descend

/- English proof (translation)
Introduce `E _ _ _ H ψ X _ _ _ hface β hβ hβp m γ hγ hβγ`. Use `set K : Submodule (𝓞 E) X := orad β with hK`. Use `haveI : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X`. Take `⟨T, hT⟩` from `(IsNoetherian.noetherian (K.restrictScalars ℤ) : (K.restrictScalars ℤ).FG)`. Establish `hTK : ∀ k ∈ T, k ∈ K` using `fun k hk => by`.

Establish `: k ∈ K.restrictScalars ℤ` using `hT ▸ Submodule.subset_span hk`. Conclude with `this`. Set `hl : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ` to `∑ k ∈ T, LinearMap.applyₗ k ∘ₗ LinearMap.applyₗ k`. Establish `hl_apply : ∀ β', hl β' = ∑ k ∈ T, β' k k` using `fun β' => by simp [hl]`. Establish `hsym : ∀ i y z, γ i y z = γ i z y` using `fun i => (hγ.mem i).1`.

Establish `hvan : ∀ i, hl (γ i) = 0 ↔ ∀ x ∈ K, ∀ y, γ i x y = 0`. Introduce `i`. Rewrite using `[hl_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `h0`.

Establish `hkk : ∀ k ∈ T, γ i k k = 0` using `(Finset.sum_eq_zero_iff_of_nonneg fun k _ => hγ.nonneg i k).1 h0`. Establish `hle : K.restrictScalars ℤ ≤ LinearMap.ker (γ i)`. Rewrite using `[← hT, Submodule.span_le]`. Introduce `k hk`. Conclude with `LinearMap.ext fun w => ConeSub.eq_zero_of_self_eq_zero (γ i) (hsym i) (hγ.nonneg i) (hkk k hk) w`.

Introduce `x hx y`. Use `hle hx` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker]`. Rewrite using `[this]`. Both sides reduce to the same expression.

Introduce `h0`. Conclude with `Finset.sum_eq_zero fun k hk => h0 k (hTK k hk) k`. Establish `hnn : ∀ i, 0 ≤ hl (γ i)` using `fun i => by`. Rewrite using `[hl_apply]`. Conclude with `Finset.sum_nonneg fun k _ => hγ.nonneg i k`.

Use `set S : Finset (Fin m) := Finset.univ.filter fun i => hl (γ i) = 0 with hS`. Set `s : Fin S.card ↪ Fin m` to `(S.orderEmbOfFin rfl).toEmbedding`. Establish `hs : Set.range s = ↑S` using `Finset.range_orderEmbOfFin S rfl`. Establish `hcut : IsFaceCut γ s hl` using `⟨hnn, fun j => by`. Rewrite using `[hs]`.

Simplify using `[hS]⟩`. Establish `hcell` using `hface m S.card γ s hl hγ hcut`. Establish `hdesc : ∀ i : Fin S.card, ∃ δ : LinearMap.BilinForm ℤ (X ⧸ K), pull K.mkQ δ = γ (s i)`. Introduce `i`. Establish `hi : hl (γ (s i)) = 0`.

Establish `: s i ∈ (S : Set (Fin m))` using `hs ▸ Set.mem_range_self i`. Simplify `this` using `[hS]`. Establish `h1` using `(hvan (s i)).1 hi`. Conclude with `exists_pull_mkQ_eq_of_vanish K _ h1 fun x y hy => by rw [hsym]; exact h1 y hy x`. Use `choose δ hδ using hdesc`.

Establish `hδ' : (fun i => pull K.mkQ (δ i)) = fun i => γ (s i)` using `funext hδ`. Establish `hsurj : Function.Surjective K.mkQ` using `K.mkQ_surjective`. Use `⟨S.card, δ, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `⟨fun i => ?_, fun i y => ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hm` using `hcell.mem i`.

Rewrite `hm` using `[← hδ i]`. Use `⟨fun y z => ?_, fun a y z => ?_⟩` and prove the remaining obligations. Take `⟨y, rfl⟩` from `hsurj y`. Take `⟨z, rfl⟩` from `hsurj z`. Conclude with `hm.1 y z`.

Take `⟨y, rfl⟩` from `hsurj y`. Take `⟨z, rfl⟩` from `hsurj z`. Use `hm.2 a y z` as an intermediate fact. Simplify `this` using `[pull_apply, map_smul]`. Take `⟨y, rfl⟩` from `hsurj y`.

Use `hcell.nonneg i y` as an intermediate fact. Rewrite `this` using `[← hδ i]`. Conclude with `this`. Rewrite using `[← linearOn_pull_iff hsurj, hδ']`. Conclude with `hcell.linear`.

Apply `IsStrict.of_pull hsurj` to reduce the goal to its premises. Rewrite using `[hδ']`. Conclude with `hcell.strict`. Rewrite using `[hδ']`. Take `⟨c, hc0, hc⟩` from `hβγ`.

Establish `hzero : ∀ j, j ∉ S → c j = 0`. Introduce `j hj`. Establish `hj' : hl (γ j) ≠ 0` using `by simpa [hS] using hj`. Rewrite `hj'` using `[hl_apply]`. Take `⟨k, hkT, hk0⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hj'`.

Establish `hk` using `LinearMap.congr_fun₂ hc k k`. Simplify using `only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at hk`. Establish `hb : β k k = 0`. Use `(mem_orad.1 (hTK k hkT)) 1 k` as an intermediate fact. Simplify using `using this`.

Rewrite `hk` using `[hb, Int.cast_zero]`. Establish `hall` using `(Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hc0 i) (Int.cast_nonneg (hγ.nonneg i k))).1 hk.symm j (Finset.mem_univ _)`. Break down `mul_eq_zero.1 hall with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd (Int.cast_eq_zero.1 h) hk0`.

Use `⟨fun i => c (s i), fun i => hc0 _, ?_⟩` and prove the remaining obligations. Rewrite using `[hc]`. Conclude with `(Fintype.sum_of_injective s s.injective (fun i => c (s i) • toReal (γ (s i))) (fun j => c j • toReal (γ j)) (fun j hj => by`. Rewrite using `[hzero j (by rw [hs] at hj; simpa using hj), zero_smul]) (fun i => rfl)).symm`. Rewrite using `[← genRank_pull hsurj δ, hδ']`.

Unfold `genRank`. Use `haveI : Module.Finite ℤ (Submodule.span ℤ (Set.range γ)) := Module.Finite.span_of_finite ℤ (Set.finite_range γ)`. Conclude with `Submodule.finrank_mono (Submodule.span_mono (Set.range_comp_subset_range s γ))`.
-/
theorem exists_cell_quot_orad_of_inRCone : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ : InvFun (𝓞 E))
    (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X],
    (∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
      IsCell H.bar ψ γ → IsFaceCut γ s h → IsCell H.bar ψ (fun i => γ (s i))) →
    ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ →
      InRCone γ β → ∃ (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ (X ⧸ (orad β : Submodule (𝓞 E) X))),
        IsCell H.bar ψ δ ∧ InRCone (fun i => pull (orad β : Submodule (𝓞 E) X).mkQ (δ i)) β ∧ genRank δ ≤ genRank γ := by
  intro E _ _ _ H ψ X _ _ _ hface β hβ hβp m γ hγ hβγ
  classical
  set K : Submodule (𝓞 E) X := orad β with hK
  haveI : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  obtain ⟨T, hT⟩ := (IsNoetherian.noetherian (K.restrictScalars ℤ) : (K.restrictScalars ℤ).FG)
  have hTK : ∀ k ∈ T, k ∈ K := fun k hk => by
    have : k ∈ K.restrictScalars ℤ := hT ▸ Submodule.subset_span hk
    exact this
  let hl : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := ∑ k ∈ T, LinearMap.applyₗ k ∘ₗ LinearMap.applyₗ k
  have hl_apply : ∀ β', hl β' = ∑ k ∈ T, β' k k := fun β' => by simp [hl]
  have hsym : ∀ i y z, γ i y z = γ i z y := fun i => (hγ.mem i).1
  have hvan : ∀ i, hl (γ i) = 0 ↔ ∀ x ∈ K, ∀ y, γ i x y = 0 := by
    intro i
    rw [hl_apply]
    constructor
    · intro h0
      have hkk : ∀ k ∈ T, γ i k k = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hγ.nonneg i k).1 h0
      have hle : K.restrictScalars ℤ ≤ LinearMap.ker (γ i) := by
        rw [← hT, Submodule.span_le]
        intro k hk
        exact LinearMap.ext fun w => ConeSub.eq_zero_of_self_eq_zero (γ i) (hsym i) (hγ.nonneg i) (hkk k hk) w
      intro x hx y
      have := hle hx
      rw [LinearMap.mem_ker] at this
      rw [this]; rfl
    · intro h0
      exact Finset.sum_eq_zero fun k hk => h0 k (hTK k hk) k
  have hnn : ∀ i, 0 ≤ hl (γ i) := fun i => by
    rw [hl_apply]; exact Finset.sum_nonneg fun k _ => hγ.nonneg i k
  set S : Finset (Fin m) := Finset.univ.filter fun i => hl (γ i) = 0 with hS
  let s : Fin S.card ↪ Fin m := (S.orderEmbOfFin rfl).toEmbedding
  have hs : Set.range s = ↑S := Finset.range_orderEmbOfFin S rfl
  have hcut : IsFaceCut γ s hl := ⟨hnn, fun j => by
    rw [hs]; simp [hS]⟩
  have hcell := hface m S.card γ s hl hγ hcut
  have hdesc : ∀ i : Fin S.card, ∃ δ : LinearMap.BilinForm ℤ (X ⧸ K), pull K.mkQ δ = γ (s i) := by
    intro i
    have hi : hl (γ (s i)) = 0 := by
      have : s i ∈ (S : Set (Fin m)) := hs ▸ Set.mem_range_self i
      simpa [hS] using this
    have h1 := (hvan (s i)).1 hi
    exact exists_pull_mkQ_eq_of_vanish K _ h1 fun x y hy => by rw [hsym]; exact h1 y hy x
  choose δ hδ using hdesc
  have hδ' : (fun i => pull K.mkQ (δ i)) = fun i => γ (s i) := funext hδ
  have hsurj : Function.Surjective K.mkQ := K.mkQ_surjective
  refine ⟨S.card, δ, ?_, ?_, ?_⟩
  · refine ⟨fun i => ?_, fun i y => ?_, ?_, ?_⟩
    · have hm := hcell.mem i
      rw [← hδ i] at hm
      refine ⟨fun y z => ?_, fun a y z => ?_⟩
      · obtain ⟨y, rfl⟩ := hsurj y
        obtain ⟨z, rfl⟩ := hsurj z
        exact hm.1 y z
      · obtain ⟨y, rfl⟩ := hsurj y
        obtain ⟨z, rfl⟩ := hsurj z
        have := hm.2 a y z
        simpa [pull_apply, map_smul] using this
    · obtain ⟨y, rfl⟩ := hsurj y
      have := hcell.nonneg i y
      rw [← hδ i] at this
      exact this
    · rw [← linearOn_pull_iff hsurj, hδ']
      exact hcell.linear
    · apply IsStrict.of_pull hsurj
      rw [hδ']
      exact hcell.strict
  · rw [hδ']
    obtain ⟨c, hc0, hc⟩ := hβγ
    have hzero : ∀ j, j ∉ S → c j = 0 := by
      intro j hj
      have hj' : hl (γ j) ≠ 0 := by simpa [hS] using hj
      rw [hl_apply] at hj'
      obtain ⟨k, hkT, hk0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj'
      have hk := LinearMap.congr_fun₂ hc k k
      simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at hk
      have hb : β k k = 0 := by
        have := (mem_orad.1 (hTK k hkT)) 1 k
        simpa using this
      rw [hb, Int.cast_zero] at hk
      have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
        mul_nonneg (hc0 i) (Int.cast_nonneg (hγ.nonneg i k))).1 hk.symm j (Finset.mem_univ _)
      rcases mul_eq_zero.1 hall with h | h
      · exact h
      · exact absurd (Int.cast_eq_zero.1 h) hk0
    refine ⟨fun i => c (s i), fun i => hc0 _, ?_⟩
    rw [hc]
    exact (Fintype.sum_of_injective s s.injective (fun i => c (s i) • toReal (γ (s i))) (fun j => c j • toReal (γ j))
      (fun j hj => by
        rw [hzero j (by rw [hs] at hj; simpa using hj), zero_smul]) (fun i => rfl)).symm
  · rw [← genRank_pull hsurj δ, hδ']
    unfold genRank
    haveI : Module.Finite ℤ (Submodule.span ℤ (Set.range γ)) := Module.Finite.span_of_finite ℤ (Set.finite_range γ)
    exact Submodule.finrank_mono (Submodule.span_mono (Set.range_comp_subset_range s γ))

end GlobalTheory.PolFan.CarDim
