import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomExtOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAffineOpenRingOnEqAdjoinInv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsHomRangeSubset

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}
  {Ω' : Type} [Field Ω'] [Algebra o Ω'] {M' : RatModel o Ω'} {φ : Ω →ₐ[o] Ω'}

/- English proof (translation)
Establish `hc : ∀ (N : RatModel o Ω') (i : I) (k : K) (z : N.Z), t i ≠ 0 → (N.Div (fun k => pairing φ s fun j => v k j / t i ^ e) k z ↔ N.Div (fun k => pairing φ s (v k)) k z)`. Introduce `N i k z hi`. Simplify using `only [pairing_div]`. Conclude with `div_mul_iff (inv_ne_zero ((map_ne_zero φ).2 (pow_ne_zero _ hi)))`. Establish `h1 : ∀ z', f z' ∈ W → ∃ i, M'.Div (fun j => pairing φ s (B j)) i z'` using `fun z' hz' => by`.

Take `⟨i, hi⟩` from `ht (f z')`. Take `⟨k, hk⟩` from `hd z'`. Conclude with `hf.exists_div_pairing s ((hv _ i hi).symm.trans (hB _ hz')) ((hc M' i k z' hi.1).2 hk)`. Use `⟨h1, fun i hi => ?_⟩` and prove the remaining obligations. Use `set R := Algebra.adjoin o (φ '' (M.ringOn W : Set Ω) ∪ Set.range fun j => pairing φ s (B j) / pairing φ s (B i)) with hR`.

Establish `hR1 : ∀ x ∈ M.ringOn W, φ x ∈ R` using `fun x hx => Algebra.subset_adjoin (Or.inl ⟨x, hx, rfl⟩)`. Establish `hR2 : ∀ j, pairing φ s (B j) / pairing φ s (B i) ∈ R` using `fun j => Algebra.subset_adjoin (Or.inr ⟨j, rfl⟩)`. Establish `hfg : R.FG`. Rewrite using `[hR, Algebra.adjoin_union]`. Use `Subalgebra.FG.sup ?_ (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)` and prove the remaining obligations.

Rewrite using `[← AlgHom.map_adjoin, Algebra.adjoin_eq]`. Conclude with `(fg_ringOn hW hne).map φ`. Use `haveI : Algebra.FiniteType o R := (Subalgebra.fg_iff_finiteType _).1 hfg`. Use `haveI : IsFractionRing R Ω' := by`. Use `IsFractionRing.of_field _ _ fun x => ?_` and prove the remaining obligations.

Establish `hK : Subfield.closure (R : Set Ω') = ⊤` using `EE.eq_top_of_pairing_mem hs (hB _ hne.some_mem) hi (map_mem_of_ringOn hW hne fun x hx => Subfield.subset_closure (hR1 x hx)) fun j => Subfield.subset_closure (hR2 j)`. Take `⟨a, ha, b, hb, rfl⟩` from `Subfield.mem_closure_iff.1 (hK ▸ Subfield.mem_top x)`. Establish `hle : Subring.closure (R : Set Ω') ≤ R.toSubring` using `Subring.closure_le.2 le_rfl`. Conclude with `⟨⟨a, hle ha⟩, ⟨b, hle hb⟩, rfl⟩`. Establish `hN : ∀ x ∈ R, ∀ z, x ∈ (ofAffine o Ω' R).O z` using `fun x hx z => algebraMap_mem_O_ofAffine z (⟨x, hx⟩ : R)`.

Establish `hN1 : ∀ x ∈ M.ringOn W, φ x ∈ (ofAffine o Ω' R).ringOn (⊤ : (ofAffine o Ω' R).Z.Opens)` using `fun x hx => mem_ringOn.2 fun z _ => hN _ (hR1 x hx) z`. Take `⟨p, hp⟩ : ∃ p, M.IsHom (ofAffine o Ω' R) φ p` from `exists_isHom_of_local fun z => ⟨⊤, W, trivial, hW, hne, hN1⟩`. Establish `hpW : ∀ z, p z ∈ W` using `fun z => hp.map_mem_of_ringOn hW hne hN1 trivial`. Establish `hNd : ∀ z, (ofAffine o Ω' R).Div (fun j => pairing φ s (B j)) i z` using `fun z => ⟨hi, fun j => hN _ (hR2 j) z⟩`. Take `⟨g, hg⟩` from `hu (ofAffine o Ω' R) fun z => by`.

Take `⟨i', hi'⟩` from `ht (p z)`. Take `⟨k, hk⟩` from `hp.exists_div_pairing s ((hB _ (hpW z)).symm.trans (hv _ i' hi')) (hNd z)`. Conclude with `⟨(i', k), div_mul_prod_iff.2 ⟨hp.div hi', (hc _ i' k z hi'.1).1 hk⟩⟩`. Establish `hgf : g ≫ f = p` using `(hf.comp hg).unique hp`. Set `U : M'.Z.Opens` to `f ⁻¹ᵁ W ⊓ ⟨_, M'.isOpen_setOf_div (fun j => pairing φ s (B j)) i⟩`.

Use `isAffineOpen_of_isHom R (U := U) ?_ hg ?_` as an intermediate fact. Conclude with `⟨U, this.1, rfl, this.2⟩`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ (⟨x, hx, rfl⟩ | ⟨j, rfl⟩)`. Conclude with `mem_ringOn.2 fun z hz => hf.map_mem_O (mem_ringOn.1 hx _ hz.1)`.

Conclude with `mem_ringOn.2 fun z hz => hz.2.2 j`. Introduce and unpack `_ ⟨z, rfl⟩`. Establish `hz : f (g z) ∈ W`. Use `hpW z` as an intermediate fact. Rewrite `this` using `[← hgf]`. Then use the resulting hypothesis.

Take `⟨j, hj⟩` from `h1 _ hz`. Conclude with `⟨hz, hg.div_of_div hj (hNd z)⟩`.
-/
theorem charts_of_universal {J : Type} [Fintype J] [DecidableEq J] (EE : M.Lat J) {s : J → Ω'}
    (hs : Subfield.closure (Set.range φ ∪ {x | ∃ i j, x = s j / s i}) = ⊤) {I K : Type} [Fintype I] [Fintype K]
    {t : I → Ω} {e : ℕ} {v : K → J → Ω} (ht : M.HasDiv t)
    (hv : ∀ z i, M.Div t i z → EE.E z = Submodule.span (M.O z) (Set.range fun k j => v k j / t i ^ e))
    {f : M'.Z ⟶ M.Z} (hf : M.IsHom M' φ f) (hd : M'.HasDiv fun k => pairing φ s (v k))
    (hu : ∀ N : RatModel o Ω', N.HasDiv (fun q : I × K => φ (t q.1) * pairing φ s (v q.2)) →
      ∃ g, M'.IsHom N (AlgHom.id o Ω') g)
    (W : M.Z.Opens) (B : J → J → Ω) (hW : IsAffineOpen W) (hne : (W : Set M.Z).Nonempty)
    (hB : ∀ z ∈ W, EE.E z = Submodule.span (M.O z) (Set.range B)) :
    (∀ z', f z' ∈ W → ∃ i, M'.Div (fun j => pairing φ s (B j)) i z') ∧ ∀ i, pairing φ s (B i) ≠ 0 →
      ∃ U : M'.Z.Opens, IsAffineOpen U ∧ (U : Set M'.Z) = {z' | f z' ∈ W ∧ M'.Div (fun j => pairing φ s (B j)) i z'} ∧
        M'.ringOn U = Algebra.adjoin o (φ '' (M.ringOn W : Set Ω) ∪
          Set.range fun j => pairing φ s (B j) / pairing φ s (B i)) := by
  have hc : ∀ (N : RatModel o Ω') (i : I) (k : K) (z : N.Z), t i ≠ 0 →
      (N.Div (fun k => pairing φ s fun j => v k j / t i ^ e) k z ↔ N.Div (fun k => pairing φ s (v k)) k z) := by
    intro N i k z hi
    simp only [pairing_div]
    exact div_mul_iff (inv_ne_zero ((map_ne_zero φ).2 (pow_ne_zero _ hi)))
  have h1 : ∀ z', f z' ∈ W → ∃ i, M'.Div (fun j => pairing φ s (B j)) i z' := fun z' hz' => by
    obtain ⟨i, hi⟩ := ht (f z')
    obtain ⟨k, hk⟩ := hd z'
    exact hf.exists_div_pairing s ((hv _ i hi).symm.trans (hB _ hz')) ((hc M' i k z' hi.1).2 hk)
  refine ⟨h1, fun i hi => ?_⟩
  set R := Algebra.adjoin o (φ '' (M.ringOn W : Set Ω) ∪
    Set.range fun j => pairing φ s (B j) / pairing φ s (B i)) with hR
  have hR1 : ∀ x ∈ M.ringOn W, φ x ∈ R := fun x hx => Algebra.subset_adjoin (Or.inl ⟨x, hx, rfl⟩)
  have hR2 : ∀ j, pairing φ s (B j) / pairing φ s (B i) ∈ R := fun j => Algebra.subset_adjoin (Or.inr ⟨j, rfl⟩)
  have hfg : R.FG := by
    rw [hR, Algebra.adjoin_union]
    refine Subalgebra.FG.sup ?_ (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
    rw [← AlgHom.map_adjoin, Algebra.adjoin_eq]
    exact (fg_ringOn hW hne).map φ
  haveI : Algebra.FiniteType o R := (Subalgebra.fg_iff_finiteType _).1 hfg
  haveI : IsFractionRing R Ω' := by
    refine IsFractionRing.of_field _ _ fun x => ?_
    have hK : Subfield.closure (R : Set Ω') = ⊤ :=
      EE.eq_top_of_pairing_mem hs (hB _ hne.some_mem) hi
        (map_mem_of_ringOn hW hne fun x hx => Subfield.subset_closure (hR1 x hx))
        fun j => Subfield.subset_closure (hR2 j)
    obtain ⟨a, ha, b, hb, rfl⟩ := Subfield.mem_closure_iff.1 (hK ▸ Subfield.mem_top x)
    have hle : Subring.closure (R : Set Ω') ≤ R.toSubring := Subring.closure_le.2 le_rfl
    exact ⟨⟨a, hle ha⟩, ⟨b, hle hb⟩, rfl⟩
  have hN : ∀ x ∈ R, ∀ z, x ∈ (ofAffine o Ω' R).O z := fun x hx z => algebraMap_mem_O_ofAffine z (⟨x, hx⟩ : R)
  have hN1 : ∀ x ∈ M.ringOn W, φ x ∈ (ofAffine o Ω' R).ringOn (⊤ : (ofAffine o Ω' R).Z.Opens) :=
    fun x hx => mem_ringOn.2 fun z _ => hN _ (hR1 x hx) z
  obtain ⟨p, hp⟩ : ∃ p, M.IsHom (ofAffine o Ω' R) φ p :=
    exists_isHom_of_local fun z => ⟨⊤, W, trivial, hW, hne, hN1⟩
  have hpW : ∀ z, p z ∈ W := fun z => hp.map_mem_of_ringOn hW hne hN1 trivial
  have hNd : ∀ z, (ofAffine o Ω' R).Div (fun j => pairing φ s (B j)) i z := fun z => ⟨hi, fun j => hN _ (hR2 j) z⟩
  obtain ⟨g, hg⟩ := hu (ofAffine o Ω' R) fun z => by
    obtain ⟨i', hi'⟩ := ht (p z)
    obtain ⟨k, hk⟩ := hp.exists_div_pairing s ((hB _ (hpW z)).symm.trans (hv _ i' hi')) (hNd z)
    exact ⟨(i', k), div_mul_prod_iff.2 ⟨hp.div hi', (hc _ i' k z hi'.1).1 hk⟩⟩
  have hgf : g ≫ f = p := (hf.comp hg).unique hp
  let U : M'.Z.Opens := f ⁻¹ᵁ W ⊓ ⟨_, M'.isOpen_setOf_div (fun j => pairing φ s (B j)) i⟩
  have := isAffineOpen_of_isHom R (U := U) ?_ hg ?_
  · exact ⟨U, this.1, rfl, this.2⟩
  · refine Algebra.adjoin_le ?_
    rintro _ (⟨x, hx, rfl⟩ | ⟨j, rfl⟩)
    · exact mem_ringOn.2 fun z hz => hf.map_mem_O (mem_ringOn.1 hx _ hz.1)
    · exact mem_ringOn.2 fun z hz => hz.2.2 j
  · rintro _ ⟨z, rfl⟩
    have hz : f (g z) ∈ W := by
      have := hpW z
      rwa [← hgf] at this
    obtain ⟨j, hj⟩ := h1 _ hz
    exact ⟨hz, hg.div_of_div hj (hNd z)⟩

end GlobalTheory.ZH.RatModel
end
