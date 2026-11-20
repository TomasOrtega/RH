import Development.EtaleCohomology.EtaleTrace.TwZeroPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Opposite

namespace LateralTheory.EtaleTrace

/- English proof (translation)
Establish `h` using `RingedSpace.isUnit_res_basicOpen X.toRingedSpace f`. Rewrite using `[Scheme.Opens.ι_appTop]`. Establish `e1 : (X.basicOpen f).ι ''ᵁ ⊤ = X.basicOpen f` using `by simp`. Establish `key : ∀ (W : X.Opens) (_ : W = X.basicOpen f) (hle : W ≤ ⊤), IsUnit ((X.presheaf.map (homOfLE hle).op).hom f)`. Introduce and unpack `W rfl hle`.

Conclude with `h`. Conclude with `key _ e1 _`.
-/
theorem tz_isUnit_ι (X : Scheme.{0}) (f : Γ(X, ⊤)) : IsUnit ((X.basicOpen f).ι.appTop.hom f) := by
  have h := RingedSpace.isUnit_res_basicOpen X.toRingedSpace f
  rw [Scheme.Opens.ι_appTop]
  have e1 : (X.basicOpen f).ι ''ᵁ ⊤ = X.basicOpen f := by simp
  have key : ∀ (W : X.Opens) (_ : W = X.basicOpen f) (hle : W ≤ ⊤), IsUnit ((X.presheaf.map (homOfLE hle).op).hom f) := by
    rintro W rfl hle
    exact h
  exact key _ e1 _

/- English proof (translation)
Take `⟨u, rfl⟩` from `hu`. Use `congrArg (· * ((u⁻¹ : Aˣ) : A)) h.eq` as an intermediate fact. Simplify `this` using `[mul_assoc]`.
-/
theorem tz_idem_one {A : Type} [CommRing A] {x : A} (h : IsIdempotentElem x) (hu : IsUnit x) : x = 1 := by
  obtain ⟨u, rfl⟩ := hu
  have := congrArg (· * ((u⁻¹ : Aˣ) : A)) h.eq
  simpa [mul_assoc] using this

/- English proof (translation)
Introduce `U n e he hs`. Set `W : Fin n → U.Opens` to `fun i => U.basicOpen (e i)`. Establish `hW : TopologicalSpace.IsOpenCover W`. Use `TopologicalSpace.IsOpenCover.mk (eq_top_iff.2 fun x _ => ?_)` and prove the remaining obligations. Rewrite using `[TopologicalSpace.Opens.mem_iSup]`.

Assume the negation of the conclusion as `hx`. Use `push Not at hx`. Establish `hm : ∀ i, U.presheaf.germ ⊤ x trivial (e i) ∈ IsLocalRing.maximalIdeal (U.presheaf.stalk x)` using `fun i => (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 ((Scheme.mem_basicOpen_top _ _ x).not.1 (hx i)))`. Establish `hsum` using `Ideal.sum_mem (IsLocalRing.maximalIdeal _) (t := Finset.univ) (fun i _ => hm i)`. Rewrite `hsum` using `[← map_sum, hs, map_one]`.

Conclude with `(IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 hsum)`. Set `𝒰` to `U.openCoverOfIsOpenCover W hW`. Use `⟨Sieve.ofArrows 𝒰.X 𝒰.f, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Scheme.zariskiTopology_le_etaleTopology _ (Scheme.Cover.mem_grothendieckTopology 𝒰)`. Introduce and unpack `V g ⟨Y, h, f, ⟨i⟩, rfl⟩`.

Set `j : Fin n` to `i`. Use `⟨j, ?_⟩` and prove the remaining obligations. Establish `h1 : (W j).ι.appTop.hom (e i) = 1` using `tz_idem_one ((he j).map _) (tz_isUnit_ι U (e j))`. Simplify using `only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]`. Express the relevant statement in the definitionally equal form `h.appTop.hom ((W j).ι.appTop.hom (e j)) = 1`.

Rewrite using `[h1]`. Conclude with `map_one _`.
-/
theorem splitLoc : SplitLoc := by
  intro U n e he hs
  let W : Fin n → U.Opens := fun i => U.basicOpen (e i)
  have hW : TopologicalSpace.IsOpenCover W := by
    refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.2 fun x _ => ?_)
    rw [TopologicalSpace.Opens.mem_iSup]
    by_contra hx
    push Not at hx
    have hm : ∀ i, U.presheaf.germ ⊤ x trivial (e i) ∈ IsLocalRing.maximalIdeal (U.presheaf.stalk x) := fun i =>
      (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 ((Scheme.mem_basicOpen_top _ _ x).not.1 (hx i)))
    have hsum := Ideal.sum_mem (IsLocalRing.maximalIdeal _) (t := Finset.univ) (fun i _ => hm i)
    rw [← map_sum, hs, map_one] at hsum
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 hsum)
  let 𝒰 := U.openCoverOfIsOpenCover W hW
  refine ⟨Sieve.ofArrows 𝒰.X 𝒰.f, ?_, ?_⟩
  · exact Scheme.zariskiTopology_le_etaleTopology _ (Scheme.Cover.mem_grothendieckTopology 𝒰)
  · rintro V g ⟨Y, h, f, ⟨i⟩, rfl⟩
    let j : Fin n := i
    refine ⟨j, ?_⟩
    have h1 : (W j).ι.appTop.hom (e i) = 1 := tz_idem_one ((he j).map _) (tz_isUnit_ι U (e j))
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    change h.appTop.hom ((W j).ι.appTop.hom (e j)) = 1
    rw [h1]; exact map_one _

/- English proof (translation)
The claim follows from `TwZero_of hTw hS splitLoc`.
-/
theorem TwZero_of_split (hTw : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc) (hS : PrimSplit) : TwZero :=
  TwZero_of hTw hS splitLoc

end LateralTheory.EtaleTrace
