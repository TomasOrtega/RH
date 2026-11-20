import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV

namespace GlobalTheory.FlagEq
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

/- English proof (translation)
Introduce `α m g e Hm hpos h h' hH bv s hs hh hh'`. Establish `key : ∀ τ, ∀ i : Fin (m τ), h (Pi.single (e.symm ⟨τ, i⟩) 1) = h' (Pi.single (e.symm ⟨τ, i⟩) 1)`. Introduce `τ`. Set `ev : Fin (m τ) → (Fin g → ℂ)` to `fun j => Pi.single (e.symm ⟨τ, j⟩) 1`. Set `E : Fin (m τ) → Submodule ℂ (Fin g → ℂ)` to `fun i => Submodule.span ℂ (ev '' {j | j < i})`.

Establish `ha : ∀ i, Submodule.span ℂ (bv τ '' {j | j < i}) ≤ (E i).map h'.toLinearMap`. Introduce `i`. Proceed by induction on `i using WellFoundedLT.induction with`. Consider the case `_ i ih`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨j, hj, rfl⟩`. Establish `hj : j < i` using `hj`. Establish `h1 : h' (ev j) ∈ (E i).map h'.toLinearMap` using `Submodule.mem_map_of_mem (Submodule.subset_span ⟨j, hj, rfl⟩)`. Establish `h2 : h' (ev j) - s • bv τ j ∈ (E i).map h'.toLinearMap`. Use `ih j hj (hh' τ j)` as an intermediate fact.

Conclude with `Submodule.map_mono (Submodule.span_mono (Set.image_mono (fun k (hk : k < j) => (lt_trans hk hj : k < i)))) this`. Establish `h3 : s • bv τ j ∈ (E i).map h'.toLinearMap`. Use `Submodule.sub_mem _ h1 h2` as an intermediate fact. Simplify using `using this`. Use `Submodule.smul_mem _ s⁻¹ h3` as an intermediate fact.

Rewrite `this` using `[smul_smul, inv_mul_cancel₀ hs, one_smul]`. Conclude with `this`. Introduce `i`. Proceed by induction on `i using WellFoundedLT.induction with`. Consider the case `_ i ih`.

Establish `hon : Set.EqOn h.toLinearMap h'.toLinearMap (E i)`. Apply `LinearMap.eqOn_span'` to reduce the goal to its premises. Introduce and unpack `_ ⟨j, hj, rfl⟩`. Conclude with `ih j hj`. Use `set u := h (ev i) - h' (ev i) with hu`.

Establish `hu' : u = (h (ev i) - s • bv τ i) - (h' (ev i) - s • bv τ i)`. Rewrite using `[hu]`. Normalize the expressions using the abelian group laws. Establish `huB : u ∈ Submodule.span ℂ (bv τ '' {j | j < i})`. Rewrite using `[hu']`.

Conclude with `Submodule.sub_mem _ (hh τ i) (hh' τ i)`. Take `⟨v, hvE, hv⟩` from `ha i huB`. Establish `hv' : h' v = u` using `hv`. Establish `hhv : h v = u`. Rewrite using `[← hv']`.

Conclude with `hon hvE`. Establish `hx : h (ev i) = h' (ev i) + u` using `by rw [hu]; abel`. Establish `hE` using `hH (ev i) v`. Rewrite `hE` using `[hhv, hv', hx]`. Establish `h0 : hermForm Hm u u = 0`.

Unfold `hermForm at hE ⊢`. Rewrite `hE` using `[add_dotProduct]`. Simplify using `using hE`. Assume the negation of the conclusion as `hne`. Establish `hne' : u ≠ 0`.

Introduce `h0'`. Apply `hne` to reduce the goal to its premises. Rewrite `h0'` using `[hu]`. Conclude with `sub_eq_zero.mp h0'`. Use `hpos u hne'` as an intermediate fact.

Rewrite `this` using `[h0]`. Simplify using `at this`. Apply `LinearEquiv.toLinearMap_injective` to reduce the goal to its premises. Apply `(Pi.basisFun ℂ (Fin g)).ext` to reduce the goal to its premises. Introduce `n`.

Rewrite using `[Pi.basisFun_apply]`. Use `key (e n).1 (e n).2` as an intermediate fact. Simplify using `using this`.
-/
theorem eq_of_flag_of_hermForm : ∀ {α : Type} {m : α → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : α, Fin (m τ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) → ∀ (h h' : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ x y, ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h x) (h y) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h' x) (h' y)) → ∀ (bv : ∀ τ, Fin (m τ) → (Fin g → ℂ)) (s : ℂ), s ≠ 0 → (∀ τ i, h (Pi.single (e.symm ⟨τ, i⟩) 1) - s • bv τ i ∈ Submodule.span ℂ (bv τ '' {j | j < i})) → (∀ τ i, h' (Pi.single (e.symm ⟨τ, i⟩) 1) - s • bv τ i ∈ Submodule.span ℂ (bv τ '' {j | j < i})) → h = h' := by
  intro α m g e Hm hpos h h' hH bv s hs hh hh'
  have key : ∀ τ, ∀ i : Fin (m τ), h (Pi.single (e.symm ⟨τ, i⟩) 1) = h' (Pi.single (e.symm ⟨τ, i⟩) 1) := by
    intro τ
    let ev : Fin (m τ) → (Fin g → ℂ) := fun j => Pi.single (e.symm ⟨τ, j⟩) 1
    let E : Fin (m τ) → Submodule ℂ (Fin g → ℂ) := fun i => Submodule.span ℂ (ev '' {j | j < i})
    have ha : ∀ i, Submodule.span ℂ (bv τ '' {j | j < i}) ≤ (E i).map h'.toLinearMap := by
      intro i
      induction i using WellFoundedLT.induction with
      | _ i ih =>
        rw [Submodule.span_le]
        rintro _ ⟨j, hj, rfl⟩
        have hj : j < i := hj
        have h1 : h' (ev j) ∈ (E i).map h'.toLinearMap :=
          Submodule.mem_map_of_mem (Submodule.subset_span ⟨j, hj, rfl⟩)
        have h2 : h' (ev j) - s • bv τ j ∈ (E i).map h'.toLinearMap := by
          have := ih j hj (hh' τ j)
          exact Submodule.map_mono (Submodule.span_mono
            (Set.image_mono (fun k (hk : k < j) => (lt_trans hk hj : k < i)))) this
        have h3 : s • bv τ j ∈ (E i).map h'.toLinearMap := by
          have := Submodule.sub_mem _ h1 h2
          simpa using this
        have := Submodule.smul_mem _ s⁻¹ h3
        rw [smul_smul, inv_mul_cancel₀ hs, one_smul] at this
        exact this
    intro i
    induction i using WellFoundedLT.induction with
    | _ i ih =>
      have hon : Set.EqOn h.toLinearMap h'.toLinearMap (E i) := by
        apply LinearMap.eqOn_span'
        rintro _ ⟨j, hj, rfl⟩
        exact ih j hj
      set u := h (ev i) - h' (ev i) with hu
      have hu' : u = (h (ev i) - s • bv τ i) - (h' (ev i) - s • bv τ i) := by
        rw [hu]; abel
      have huB : u ∈ Submodule.span ℂ (bv τ '' {j | j < i}) := by
        rw [hu']; exact Submodule.sub_mem _ (hh τ i) (hh' τ i)
      obtain ⟨v, hvE, hv⟩ := ha i huB
      have hv' : h' v = u := hv
      have hhv : h v = u := by
        rw [← hv']; exact hon hvE
      have hx : h (ev i) = h' (ev i) + u := by rw [hu]; abel
      have hE := hH (ev i) v
      rw [hhv, hv', hx] at hE
      have h0 : hermForm Hm u u = 0 := by
        unfold hermForm at hE ⊢
        rw [add_dotProduct] at hE
        simpa using hE
      by_contra hne
      have hne' : u ≠ 0 := by
        intro h0'; apply hne; rw [hu] at h0'; exact sub_eq_zero.mp h0'
      have := hpos u hne'
      rw [h0] at this
      simp at this
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun ℂ (Fin g)).ext
  intro n
  rw [Pi.basisFun_apply]
  have := key (e n).1 (e n).2
  simpa using this

end GlobalTheory.FlagEq
