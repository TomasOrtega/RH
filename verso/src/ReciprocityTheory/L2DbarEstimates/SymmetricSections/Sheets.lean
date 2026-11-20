import ReciprocityTheory.L2DbarEstimates.SymmetricSections.HoloSectionStatement

namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

/- English proof (translation)
Introduce `n M _ z U u hcov w hw hfin`. Take `⟨_, W, hwW, hW, _, H, hH⟩` from `hcov w hw`. Establish `: Finite (z ⁻¹' {w})` using `hfin.to_subtype`. Set `e : Fin (Nat.card (z ⁻¹' {w})) ≃ (z ⁻¹' {w})` to `(Finite.equivFin _).symm`. Set `s : Fin (Nat.card (z ⁻¹' {w})) → V n → M` to `fun i v => if hv : v ∈ W then (H.symm (⟨v, hv⟩, e i)).1 else (e i).1`.

Establish `hs : ∀ i v (hv : v ∈ W), s i v = (H.symm (⟨v, hv⟩, e i)).1` using `fun i v hv => dif_pos hv`. Establish `hzs : ∀ i, ∀ v ∈ W, z (s i v) = v`. Introduce `i v hv`. Rewrite using `[hs i v hv]`. Use `hH (H.symm (⟨v, hv⟩, e i))` as an intermediate fact.

Rewrite `this` using `[Homeomorph.apply_symm_apply]`. Conclude with `this.symm`. Establish `hinj : ∀ v (hv : v ∈ W) i j, s i v = s j v → i = j`. Introduce `v hv i j hij`. Rewrite `hij` using `[hs i v hv, hs j v hv]`.

Establish `h2` using `congrArg (fun y => (H y).2) (Subtype.ext hij : H.symm (⟨v, hv⟩, e i) = H.symm (⟨v, hv⟩, e j))`. Simplify using `only [Homeomorph.apply_symm_apply] at h2`. Conclude with `e.injective h2`. Establish `hsurj : ∀ v (hv : v ∈ W) (y : M), z y = v → ∃ i, s i v = y`. Introduce `v hv y hy`.

Establish `hyW : y ∈ z ⁻¹' W` using `by show z y ∈ W`. Rewrite using `[hy]`. Conclude with `hv`. Use `⟨e.symm (H ⟨y, hyW⟩).2, ?_⟩` and prove the remaining obligations. Rewrite using `[hs _ v hv]`.

Simplify using `only [Equiv.apply_symm_apply]`. Establish `h1 : (H ⟨y, hyW⟩).1 = ⟨v, hv⟩` using `Subtype.ext (by rw [hH]; exact hy)`. Establish `h3 : H.symm (⟨v, hv⟩, (H ⟨y, hyW⟩).2) = ⟨y, hyW⟩`. Rewrite using `[← h1]`. Simplify using the standard rewrite rules.

Rewrite using `[h3]`. Use `⟨W, Nat.card (z ⁻¹' {w}), s, hW, hwW, ?_, hzs, ?_⟩` and prove the remaining obligations. Introduce `i`. Rewrite using `[continuousOn_iff_continuous_domRestrict]`. Establish `: W.domRestrict (s i) = fun v : W => (H.symm (v, e i)).1`.

Use function extensionality and compare the values at `v`. Conclude with `hs i v.1 v.2`. Rewrite using `[this]`. Conclude with `continuous_subtype_val.comp (H.symm.continuous.comp (continuous_id.prodMk continuous_const))`. Introduce `v hv`.

Establish `hfv : (z ⁻¹' {v}).Finite`. Use `(Set.finite_range fun i => s i v).subset ?_` and prove the remaining obligations. Introduce `y hy`. Take `⟨i, hi⟩` from `hsurj v hv y hy`. Conclude with `⟨i, hi⟩`.

Unfold `fiberVals`. Rewrite using `[dif_pos hfv]`. Establish `hF : hfv.toFinset = Finset.univ.map ⟨fun i => s i v, fun i j h => hinj v hv i j h⟩`. Use extensionality with `y`. Simplify using `only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_map, Finset.mem_univ, true_and]`.

Prove the components needed by the constructor for the conclusion. Introduce `hy`. Conclude with `hsurj v hv y hy`. Introduce and unpack `⟨i, rfl⟩`. Conclude with `hzs i v hv`.

Rewrite using `[hF, Finset.map_val, Multiset.map_map]`. Both sides reduce to the same expression.
-/
theorem sheets : sheetsStatement.{u} := by
  intro n M _ z U u hcov w hw hfin
  obtain ⟨_, W, hwW, hW, _, H, hH⟩ := hcov w hw
  have : Finite (z ⁻¹' {w}) := hfin.to_subtype
  let e : Fin (Nat.card (z ⁻¹' {w})) ≃ (z ⁻¹' {w}) := (Finite.equivFin _).symm
  classical
  let s : Fin (Nat.card (z ⁻¹' {w})) → V n → M :=
    fun i v => if hv : v ∈ W then (H.symm (⟨v, hv⟩, e i)).1 else (e i).1
  have hs : ∀ i v (hv : v ∈ W), s i v = (H.symm (⟨v, hv⟩, e i)).1 := fun i v hv => dif_pos hv
  have hzs : ∀ i, ∀ v ∈ W, z (s i v) = v := by
    intro i v hv
    rw [hs i v hv]
    have := hH (H.symm (⟨v, hv⟩, e i))
    rw [Homeomorph.apply_symm_apply] at this
    exact this.symm
  have hinj : ∀ v (hv : v ∈ W) i j, s i v = s j v → i = j := by
    intro v hv i j hij
    rw [hs i v hv, hs j v hv] at hij
    have h2 := congrArg (fun y => (H y).2)
      (Subtype.ext hij : H.symm (⟨v, hv⟩, e i) = H.symm (⟨v, hv⟩, e j))
    simp only [Homeomorph.apply_symm_apply] at h2
    exact e.injective h2
  have hsurj : ∀ v (hv : v ∈ W) (y : M), z y = v → ∃ i, s i v = y := by
    intro v hv y hy
    have hyW : y ∈ z ⁻¹' W := by
      show z y ∈ W
      rw [hy]; exact hv
    refine ⟨e.symm (H ⟨y, hyW⟩).2, ?_⟩
    rw [hs _ v hv]
    simp only [Equiv.apply_symm_apply]
    have h1 : (H ⟨y, hyW⟩).1 = ⟨v, hv⟩ := Subtype.ext (by rw [hH]; exact hy)
    have h3 : H.symm (⟨v, hv⟩, (H ⟨y, hyW⟩).2) = ⟨y, hyW⟩ := by
      rw [← h1]; simp
    rw [h3]
  refine ⟨W, Nat.card (z ⁻¹' {w}), s, hW, hwW, ?_, hzs, ?_⟩
  · intro i
    rw [continuousOn_iff_continuous_domRestrict]
    have : W.domRestrict (s i) = fun v : W => (H.symm (v, e i)).1 := by
      funext v
      exact hs i v.1 v.2
    rw [this]
    exact continuous_subtype_val.comp (H.symm.continuous.comp (continuous_id.prodMk continuous_const))
  · intro v hv
    have hfv : (z ⁻¹' {v}).Finite := by
      refine (Set.finite_range fun i => s i v).subset ?_
      intro y hy
      obtain ⟨i, hi⟩ := hsurj v hv y hy
      exact ⟨i, hi⟩
    unfold fiberVals
    rw [dif_pos hfv]
    have hF : hfv.toFinset = Finset.univ.map ⟨fun i => s i v, fun i j h => hinj v hv i j h⟩ := by
      ext y
      simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_map,
        Finset.mem_univ, true_and]
      constructor
      · intro hy; exact hsurj v hv y hy
      · rintro ⟨i, rfl⟩; exact hzs i v hv
    rw [hF, Finset.map_val, Multiset.map_map]
    rfl

end ReciprocityTheory.L2DbarEstimates.Norm
