import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses

open Module Function

namespace GlobalTheory

open Module Function in

/- English proof (translation)
Take `⟨r, v⟩` from `Submodule.basisOfPid (Module.Free.chooseBasis ℤ Λ) I`. Establish `htf : Module.IsTorsionFree ℤ (Λ ⧸ I)` using `(_root_.GlobalTheory.isTorsionFree_quotient_iff I).mpr hsat`. Establish `hle : I ≤ ω.orthogonal I` using `fun x hx => (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun y hy => hiso y hy x hx`. Take `⟨g, b, hb, hbv⟩` from `_root_.GlobalTheory.exists_isSymplecticBasis_extend hω hp htf hle v`. Use `set e : Fin r ⊕ Fin g ≃ Fin (r + g) := finSumFinEquiv`.

Use `set b' := b.reindex (e.sumCongr e) with hb'`. Establish `hsymp : _root_.GlobalTheory.IsSymplecticBasis ω b'` using `hb.reindex e`. Establish `hb'v : ∀ i, b' (Sum.inl (e (Sum.inl i))) = (v i : Λ)`. Introduce `i`. Rewrite using `[hb', Module.Basis.reindex_apply]`.

Simplify using `[hbv]`. Take `⟨u, hu⟩ : IsUnit ε` from `Int.isUnit_iff.mpr hε`. Set `D : (Fin (r + g) ⊕ Fin (r + g) → ℤ) ≃ₗ[ℤ] (Fin (r + g) ⊕ Fin (r + g) → ℤ)` to `LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfUnit (Sum.elim (fun _ => 1) (fun _ => u) i)`. Establish `hD : ∀ a i, D a i = Sum.elim (fun _ => (1 : ℤ)) (fun _ => ε) i * a i`. Introduce `a i`.

Apply the tactic sequence `rcases i with i | i <;> change (_ : ℤˣ) • a _ = _ <;> simp [Units.smul_def, hu]`. Use `⟨r + g, D.trans b'.equivFun.symm, Finset.univ.image fun i => e (Sum.inl i), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a c`. Rewrite using `[hsymp.apply_eq_sum hω]`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [LinearEquiv.trans_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, hD, Sum.elim_inl, Sum.elim_inr]`. Expand and normalize the polynomial expressions, which then agree. Establish `hspan : Submodule.span ℤ (Set.range fun i => (v i : Λ)) = I`.

Establish `h` using `congrArg (Submodule.map I.subtype) v.span_eq`. Rewrite `h` using `[Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]`. Conclude with `h`. Establish `hsingle : ∀ k, D (Pi.single (Sum.inl k) 1) = Pi.single (Sum.inl k) 1`. Introduce `k`.

Use function extensionality and compare the values at `i`. Rewrite using `[hD]`. Apply the tactic sequence `rcases i with i | i <;> simp [Pi.single_apply]`. Rewrite using `[← hspan]`. Use `congr 1`.

Use extensionality with `x`. Simplify using `only [Set.mem_image, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range, LinearEquiv.trans_apply, hsingle, _root_.Basis.equivFun_symm_single]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, rfl⟩`. Conclude with `⟨e (Sum.inl i), ⟨i, rfl⟩, hb'v i⟩`.

Introduce and unpack `⟨k, ⟨i, rfl⟩, rfl⟩`. Conclude with `⟨i, (hb'v i).symm⟩`. Rewrite using `[Module.finrank_eq_card_basis b']`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.GlobalTheory.exists_symplectic_coordinates_adapted {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ]
    [Module.Finite ℤ Λ] {ω : LinearMap.BilinForm ℤ Λ} (hω : ω.IsAlt) (hp : Bijective ω)
    {I : Submodule ℤ Λ} (hsat : ∀ (k : ℤ) (x : Λ), k ≠ 0 → k • x ∈ I → x ∈ I)
    (hiso : ∀ x ∈ I, ∀ y ∈ I, ω x y = 0) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    ∃ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] Λ) (S : Finset (Fin g)),
      (∀ a b, ω (bas a) (bas b) = ε * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd a b) ∧
      I = Submodule.span ℤ ((fun k => bas (Pi.single (Sum.inl k) 1)) '' (S : Set (Fin g))) ∧
      2 * g = finrank ℤ Λ := by
  obtain ⟨r, v⟩ := Submodule.basisOfPid (Module.Free.chooseBasis ℤ Λ) I
  have htf : Module.IsTorsionFree ℤ (Λ ⧸ I) := (_root_.GlobalTheory.isTorsionFree_quotient_iff I).mpr hsat
  have hle : I ≤ ω.orthogonal I := fun x hx =>
    (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun y hy => hiso y hy x hx
  obtain ⟨g, b, hb, hbv⟩ := _root_.GlobalTheory.exists_isSymplecticBasis_extend hω hp htf hle v
  set e : Fin r ⊕ Fin g ≃ Fin (r + g) := finSumFinEquiv
  set b' := b.reindex (e.sumCongr e) with hb'
  have hsymp : _root_.GlobalTheory.IsSymplecticBasis ω b' := hb.reindex e
  have hb'v : ∀ i, b' (Sum.inl (e (Sum.inl i))) = (v i : Λ) := by
    intro i
    rw [hb', Module.Basis.reindex_apply]
    simp [hbv]
  obtain ⟨u, hu⟩ : IsUnit ε := Int.isUnit_iff.mpr hε
  let D : (Fin (r + g) ⊕ Fin (r + g) → ℤ) ≃ₗ[ℤ] (Fin (r + g) ⊕ Fin (r + g) → ℤ) :=
    LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfUnit (Sum.elim (fun _ => 1) (fun _ => u) i)
  have hD : ∀ a i, D a i = Sum.elim (fun _ => (1 : ℤ)) (fun _ => ε) i * a i := by
    intro a i
    rcases i with i | i <;> change (_ : ℤˣ) • a _ = _ <;> simp [Units.smul_def, hu]
  refine ⟨r + g, D.trans b'.equivFun.symm, Finset.univ.image fun i => e (Sum.inl i), ?_, ?_, ?_⟩
  · intro a c
    rw [hsymp.apply_eq_sum hω]
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [LinearEquiv.trans_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, hD,
      Sum.elim_inl, Sum.elim_inr]
    ring
  · have hspan : Submodule.span ℤ (Set.range fun i => (v i : Λ)) = I := by
      have h := congrArg (Submodule.map I.subtype) v.span_eq
      rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at h
      exact h
    have hsingle : ∀ k, D (Pi.single (Sum.inl k) 1) = Pi.single (Sum.inl k) 1 := by
      intro k
      funext i
      rw [hD]
      rcases i with i | i <;> simp [Pi.single_apply]
    rw [← hspan]
    congr 1
    ext x
    simp only [Set.mem_image, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range,
      LinearEquiv.trans_apply, hsingle, _root_.Basis.equivFun_symm_single]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e (Sum.inl i), ⟨i, rfl⟩, hb'v i⟩
    · rintro ⟨k, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hb'v i).symm⟩
  · rw [Module.finrank_eq_card_basis b']
    simp
    ring

end GlobalTheory
