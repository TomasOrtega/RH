import Development.EtaleCohomology.TateTwists.TwSecLocPfR

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct GlobalTheory.EtC GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec

namespace LateralTheory.EtaleFoundations.TwSecLocPf

def AlgPow : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ζ ξ : Prim q A),
  ∃ s : Set A, Ideal.span s = ⊤ ∧ ∀ f ∈ s, ∃ (a : (ZMod q)ˣ) (n : ℕ), f ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val) = 0

/- English proof (translation)
Introduce `q _ V ζ ξ`. Take `⟨s, hs, hf⟩` from `hA q Γ(V, ⊤) ζ ξ`. Set `U : s → V.Opens` to `fun f => V.basicOpen f.1`. Establish `hU : TopologicalSpace.IsOpenCover U`. Unfold `TopologicalSpace.IsOpenCover`.

Establish `h` using `iSup_basicOpen_of_span_eq_top ⊤ s hs`. Use `show ⨆ f : s, V.basicOpen f.1 = ⊤`. Rewrite using `[iSup_subtype]`. Conclude with `h`. Set `𝒰` to `V.openCoverOfIsOpenCover U hU`.

Use `⟨Sieve.generate (Presieve.ofArrows 𝒰.X 𝒰.f), Scheme.zariskiTopology_le_etaleTopology _ (Scheme.mem_grothendieckTopology_iff.2 ⟨𝒰, Sieve.le_generate _⟩), ?_⟩` and prove the remaining obligations. Introduce and unpack `W g ⟨Y, h, _, ⟨i⟩, rfl⟩`. Take `⟨a, n, hn⟩` from `hf i.1 i.2`. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `hle : (U i).ι ''ᵁ ⊤ ≤ V.basicOpen i.1` using `by simp [U]`.

Establish `hu : IsUnit ((U i).ι.appTop.hom i.1)`. Use `(V.toRingedSpace.isUnit_res_basicOpen i.1).map (V.presheaf.map (homOfLE hle).op).hom` as an intermediate fact. Establish `e : V.presheaf.map (homOfLE (x` using `(U i).ι ''ᵁ ⊤) (y := ⊤) le_top).op = V.presheaf.map (homOfLE (V.basicOpen_le i.1)).op ≫ V.presheaf.map (homOfLE hle).op := by`. Rewrite using `[← Functor.map_comp]`. Both sides reduce to the same expression.

Rewrite using `[Scheme.Opens.ι_appTop, e]`. Conclude with `this`. Establish `key : (U i).ι.appTop.hom ξ.1 = ((U i).ι.appTop.hom ζ.1) ^ (a : ZMod q).val`. Establish `h0 : (U i).ι.appTop.hom (i.1 ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val)) = 0` using `by rw [hn, map_zero]`. Rewrite `h0` using `[map_mul, map_pow, map_sub, map_pow]`.

Conclude with `sub_eq_zero.1 ((hu.pow n).mul_right_eq_zero.1 h0)`. Establish `hc : ∀ x, (h ≫ (U i).ι).appTop.hom x = h.appTop.hom ((U i).ι.appTop.hom x)` using `fun x => by`. Both sides reduce to the same expression. Use `show (h ≫ (U i).ι).appTop.hom ξ.1 = ((h ≫ (U i).ι).appTop.hom ζ.1) ^ _`. Rewrite using `[hc, hc, key]`.

Conclude with `map_pow _ _ _`.
-/
theorem ZarPow_of (hA : AlgPow) : ZarPow := by
  intro q _ V ζ ξ
  obtain ⟨s, hs, hf⟩ := hA q Γ(V, ⊤) ζ ξ
  let U : s → V.Opens := fun f => V.basicOpen f.1
  have hU : TopologicalSpace.IsOpenCover U := by
    unfold TopologicalSpace.IsOpenCover
    have h := iSup_basicOpen_of_span_eq_top ⊤ s hs
    show ⨆ f : s, V.basicOpen f.1 = ⊤
    rw [iSup_subtype]
    exact h
  let 𝒰 := V.openCoverOfIsOpenCover U hU
  refine ⟨Sieve.generate (Presieve.ofArrows 𝒰.X 𝒰.f),
    Scheme.zariskiTopology_le_etaleTopology _ (Scheme.mem_grothendieckTopology_iff.2 ⟨𝒰, Sieve.le_generate _⟩), ?_⟩
  rintro W g ⟨Y, h, _, ⟨i⟩, rfl⟩
  obtain ⟨a, n, hn⟩ := hf i.1 i.2
  refine ⟨a, ?_⟩
  have hle : (U i).ι ''ᵁ ⊤ ≤ V.basicOpen i.1 := by simp [U]
  have hu : IsUnit ((U i).ι.appTop.hom i.1) := by
    have := (V.toRingedSpace.isUnit_res_basicOpen i.1).map (V.presheaf.map (homOfLE hle).op).hom
    have e : V.presheaf.map (homOfLE (x := (U i).ι ''ᵁ ⊤) (y := ⊤) le_top).op =
        V.presheaf.map (homOfLE (V.basicOpen_le i.1)).op ≫ V.presheaf.map (homOfLE hle).op := by
      rw [← Functor.map_comp]; rfl
    rw [Scheme.Opens.ι_appTop, e]
    exact this
  have key : (U i).ι.appTop.hom ξ.1 = ((U i).ι.appTop.hom ζ.1) ^ (a : ZMod q).val := by
    have h0 : (U i).ι.appTop.hom (i.1 ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val)) = 0 := by rw [hn, map_zero]
    rw [map_mul, map_pow, map_sub, map_pow] at h0
    exact sub_eq_zero.1 ((hu.pow n).mul_right_eq_zero.1 h0)
  have hc : ∀ x, (h ≫ (U i).ι).appTop.hom x = h.appTop.hom ((U i).ι.appTop.hom x) := fun x => by
    rfl
  show (h ≫ (U i).ι).appTop.hom ξ.1 = ((h ≫ (U i).ι).appTop.hom ζ.1) ^ _
  rw [hc, hc, key]
  exact map_pow _ _ _

/- English proof (translation)
The claim follows from `TwSecLoc_of (ZarPow_of hA)`.
-/
theorem TwSecLoc_of_alg (hA : AlgPow) : LateralTheory.EtaleFoundations.TwLocPf.TwSecLoc := TwSecLoc_of (ZarPow_of hA)

end LateralTheory.EtaleFoundations.TwSecLocPf
