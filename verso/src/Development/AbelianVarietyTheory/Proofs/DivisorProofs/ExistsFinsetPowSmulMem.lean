import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinSubRange
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.FinitePowerAnnihilation

/- English proof (translation)
Use `letI : Algebra Rf Af := ψ.toAlgebra`. Use `haveI : IsNoetherianRing Rf := IsLocalization.isNoetherianRing (Submonoid.powers f) Rf inferInstance`. Establish `hfg : (Algebra.adjoin Rf T).toSubmodule.FG` using `fg_adjoin_of_finite hT hI`. Establish `hle : Submodule.span Rf (ρ '' M) ≤ (Algebra.adjoin Rf T).toSubmodule`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `h` using `hM x hx`. Establish `: Subring.closure (Set.range ψ ∪ T) ≤ (Algebra.adjoin Rf T).toSubring`. Rewrite using `[Subring.closure_le]`. Introduce and unpack `y (⟨a, rfl⟩ | hy)`.

Conclude with `(Algebra.adjoin Rf T).algebraMap_mem a`. Conclude with `Algebra.subset_adjoin hy`. Conclude with `this h`. Establish `hfg2 : (Submodule.span Rf (ρ '' M)).FG` using `hfg.of_le hle`. Take `⟨u, hu, hsp⟩` from `(Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg2`.

Take `⟨s, hs, hsu⟩` from `Finset.subset_set_image_iff.1 hu`. Use `⟨s, hs, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hx1 : ρ x ∈ Submodule.span Rf (u : Set Af)` using `hsp ▸ Submodule.subset_span ⟨x, hx, rfl⟩`. Establish `key : ∀ z ∈ Submodule.span Rf (u : Set Af), ∃ n : ℕ, ∃ w ∈ Submodule.span R (s : Set A), ρ w = ρ (algebraMap R A f) ^ n * z`. Introduce `z hz`.

Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Rewrite `hz` using `[← hsu, Finset.coe_image]`. Take `⟨w, hw, rfl⟩` from `hz`. Conclude with `⟨0, w, Submodule.subset_span hw, by simp⟩`.

Consider the case `zero => exact ⟨0, 0, Submodule.zero_mem _, by simp⟩`. Consider the case `add a b _ _ ha hb`. Take `⟨n, w, hw, e⟩` from `ha`. Take `⟨m, v, hv, e'⟩` from `hb`. Use `⟨n + m, f ^ m • w + f ^ n • v, Submodule.add_mem _ (Submodule.smul_mem _ _ hw) (Submodule.smul_mem _ _ hv), ?_⟩` and prove the remaining obligations.

Simplify using `only [Algebra.smul_def, map_add, map_mul, map_pow, e, e']`. Expand and normalize the polynomial expressions, which then agree. Consider the case `smul c a _ ha`. Take `⟨n, w, hw, e⟩` from `ha`. Take `⟨⟨b, ⟨_, k, rfl⟩⟩, hb⟩` from `IsLocalization.surj (Submonoid.powers f) c`.

Use `⟨n + k, b • w, Submodule.smul_mem _ _ hw, ?_⟩` and prove the remaining obligations. Establish `hb' : ψ c * ρ (algebraMap R A f) ^ k = ρ (algebraMap R A b)`. Rewrite using `[hc, hc, ← map_pow, ← map_mul, ← map_pow]`. Conclude with `congrArg ψ hb`. Establish `hs' : c • a = ψ c * a` using `rfl`.

Rewrite using `[Algebra.smul_def, map_mul, e, ← hb', hs']`. Expand and normalize the polynomial expressions, which then agree. Take `⟨n, w, hw, e⟩` from `key _ hx1`. Take `⟨m, hm⟩` from `hk (f ^ n • x - w) (by rw [map_sub, e, Algebra.smul_def, map_mul, map_pow, map_pow, sub_self])`. Use `⟨m + n, ?_⟩` and prove the remaining obligations.

Rewrite `hm` using `[smul_sub, sub_eq_zero, ← mul_smul, ← pow_add]`. Rewrite using `[hm]`. Conclude with `Submodule.smul_mem _ _ hw`.
-/
theorem exists_finset_pow_smul_mem {R A Rf Af : Type} [CommRing R] [CommRing A] [CommRing Rf] [CommRing Af]
    [IsNoetherianRing R] [Algebra R A] [Algebra R Rf] (f : R) [IsLocalization.Away f Rf]
    (ψ : Rf →+* Af) (ρ : A →+* Af) (hc : ∀ a, ρ (algebraMap R A a) = ψ (algebraMap R Rf a))
    (hk : ∀ x, ρ x = 0 → ∃ n : ℕ, f ^ n • x = 0) (T : Set Af) (hT : T.Finite)
    (hI : ∀ y ∈ T, ψ.IsIntegralElem y) (M : Set A)
    (hM : ∀ x ∈ M, ρ x ∈ Subring.closure (Set.range ψ ∪ T)) :
    ∃ s : Finset A, (s : Set A) ⊆ M ∧ ∀ x ∈ M, ∃ n : ℕ, f ^ n • x ∈ Submodule.span R (s : Set A) := by
  classical
  letI : Algebra Rf Af := ψ.toAlgebra
  haveI : IsNoetherianRing Rf := IsLocalization.isNoetherianRing (Submonoid.powers f) Rf inferInstance
  have hfg : (Algebra.adjoin Rf T).toSubmodule.FG := fg_adjoin_of_finite hT hI
  have hle : Submodule.span Rf (ρ '' M) ≤ (Algebra.adjoin Rf T).toSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have h := hM x hx
    have : Subring.closure (Set.range ψ ∪ T) ≤ (Algebra.adjoin Rf T).toSubring := by
      rw [Subring.closure_le]
      rintro y (⟨a, rfl⟩ | hy)
      · exact (Algebra.adjoin Rf T).algebraMap_mem a
      · exact Algebra.subset_adjoin hy
    exact this h
  have hfg2 : (Submodule.span Rf (ρ '' M)).FG := hfg.of_le hle
  obtain ⟨u, hu, hsp⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg2
  obtain ⟨s, hs, hsu⟩ := Finset.subset_set_image_iff.1 hu
  refine ⟨s, hs, fun x hx => ?_⟩
  have hx1 : ρ x ∈ Submodule.span Rf (u : Set Af) := hsp ▸ Submodule.subset_span ⟨x, hx, rfl⟩
  have key : ∀ z ∈ Submodule.span Rf (u : Set Af), ∃ n : ℕ, ∃ w ∈ Submodule.span R (s : Set A),
      ρ w = ρ (algebraMap R A f) ^ n * z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      rw [← hsu, Finset.coe_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact ⟨0, w, Submodule.subset_span hw, by simp⟩
    | zero => exact ⟨0, 0, Submodule.zero_mem _, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨n, w, hw, e⟩ := ha
      obtain ⟨m, v, hv, e'⟩ := hb
      refine ⟨n + m, f ^ m • w + f ^ n • v,
        Submodule.add_mem _ (Submodule.smul_mem _ _ hw) (Submodule.smul_mem _ _ hv), ?_⟩
      simp only [Algebra.smul_def, map_add, map_mul, map_pow, e, e']
      ring
    | smul c a _ ha =>
      obtain ⟨n, w, hw, e⟩ := ha
      obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, hb⟩ := IsLocalization.surj (Submonoid.powers f) c
      refine ⟨n + k, b • w, Submodule.smul_mem _ _ hw, ?_⟩
      have hb' : ψ c * ρ (algebraMap R A f) ^ k = ρ (algebraMap R A b) := by
        rw [hc, hc, ← map_pow, ← map_mul, ← map_pow]
        exact congrArg ψ hb
      have hs' : c • a = ψ c * a := rfl
      rw [Algebra.smul_def, map_mul, e, ← hb', hs']
      ring
  obtain ⟨n, w, hw, e⟩ := key _ hx1
  obtain ⟨m, hm⟩ := hk (f ^ n • x - w) (by rw [map_sub, e, Algebra.smul_def, map_mul, map_pow, map_pow, sub_self])
  refine ⟨m + n, ?_⟩
  rw [smul_sub, sub_eq_zero, ← mul_smul, ← pow_add] at hm
  rw [hm]
  exact Submodule.smul_mem _ _ hw

/- English proof (translation)
Establish `hc : IsCompact ((gp ⁻¹ᵁ W : (Sp K).Opens) : Set (Sp K))` using `(Set.subsingleton_of_subsingleton (α := PrimeSpectrum K)).isCompact`. Use `exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact (Sp K) hc x ((gp.app W).hom f) ?_` and prove the remaining obligations. Establish `e : (Sp K).basicOpen ((gp.app W).hom f) ≤ gp ⁻¹ᵁ S.basicOpen f` using `(Scheme.preimage_basicOpen gp f).ge`. Establish `h` using `congrArg ((Sp K).presheaf.map (homOfLE e).op).hom hx`. Rewrite `h` using `[map_zero, resK, ← CommRingCat.comp_apply, ← Functor.map_comp]`.

Conclude with `h`.
-/
theorem pow_mul_eq_zero_of_res {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) (W : S.Opens) (f : Γ(S, W))
    (x : Γ(Sp K, gp ⁻¹ᵁ W)) (hx : resK gp (S.basicOpen_le f) x = 0) :
    ∃ n : ℕ, (gp.app W).hom f ^ n * x = 0 := by
  have hc : IsCompact ((gp ⁻¹ᵁ W : (Sp K).Opens) : Set (Sp K)) :=
    (Set.subsingleton_of_subsingleton (α := PrimeSpectrum K)).isCompact
  refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact (Sp K) hc x ((gp.app W).hom f) ?_
  have e : (Sp K).basicOpen ((gp.app W).hom f) ≤ gp ⁻¹ᵁ S.basicOpen f := (Scheme.preimage_basicOpen gp f).ge
  have h := congrArg ((Sp K).presheaf.map (homOfLE e).op).hom hx
  rw [map_zero, resK, ← CommRingCat.comp_apply, ← Functor.map_comp] at h
  exact h

/- English proof (translation)
Use `haveI : IsNoetherianRing Γ(S, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩`. Use `letI : Algebra Γ(S, W) Γ(Sp K, gp ⁻¹ᵁ W) := (gp.app W).hom.toAlgebra`. Establish `loc : ∀ f : Γ(S, W), (∃ i, S.basicOpen f ≤ V i) → ∃ s : Finset Γ(Sp K, gp ⁻¹ᵁ W), (s : Set Γ(Sp K, gp ⁻¹ᵁ W)) ⊆ (finFam gp V t W : Set Γ(Sp K, gp ⁻¹ᵁ W)) ∧ ∀ x ∈ (finFam gp V t W : Set Γ(Sp K, gp ⁻¹ᵁ W)), ∃ n : ℕ, f ^ n • x ∈ Submodule.span Γ(S, W) (s : Set Γ(Sp K, gp ⁻¹ᵁ W))`. Introduce and unpack `f ⟨i, hi⟩`. Use `haveI := hW.isLocalization_basicOpen f`.

Use `exists_finset_pow_smul_mem (Rf := Γ(S, S.basicOpen f)) f (gp.app (S.basicOpen f)).hom (resK gp (S.basicOpen_le f)) (fun a => resK_app gp _ a) ?_ (resK gp hi '' (t i : Set _)) ((t i).finite_toSet.image _) ?_ _ ?_` and prove the remaining obligations. Introduce `x hx`. Take `⟨n, hn⟩` from `pow_mul_eq_zero_of_res gp W f x hx`. Conclude with `⟨n, by rw [Algebra.smul_def, map_pow]; exact hn⟩`. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Take `⟨p, hp, hp0⟩` from `ht i y hy`. Use `⟨p.map (S.presheaf.map (homOfLE hi).op).hom, hp.map _, ?_⟩` and prove the remaining obligations. Establish `e : (gp.app (S.basicOpen f)).hom.comp (S.presheaf.map (homOfLE hi).op).hom = (resK gp hi).comp (gp.app (V i)).hom` using `RingHom.ext fun a => (resK_app gp hi a).symm`. Rewrite using `[Polynomial.eval₂_map, e, ← Polynomial.hom_eval₂, hp0, map_zero]`. Introduce `x hx`.

Establish `hii : S.basicOpen f ≤ W ⊓ V i` using `le_inf (S.basicOpen_le f) hi`. Establish `h1` using `(mem_finFam gp V t W x).1 hx i`. Establish `hm : resK gp hii (resK gp (inf_le_left : W ⊓ V i ≤ W) x) ∈ (Subring.closure _).map (resK gp hii)` using `⟨_, h1, rfl⟩`. Rewrite `hm` using `[RingHom.map_closure, resK_resK]`. Use `Subring.closure_mono ?_ hm` and prove the remaining obligations.

Introduce and unpack `_ ⟨y, ⟨a, rfl⟩ | ⟨z, hz, rfl⟩, rfl⟩`. Conclude with `Or.inl ⟨_, (resK_app gp hii a).symm⟩`. Conclude with `Or.inr ⟨z, hz, by rw [resK_resK]⟩`. Establish `hspan : Ideal.span {f : Γ(S, W) | ∃ i, S.basicOpen f ≤ V i} = ⊤`. Rewrite using `[← hW.self_le_iSup_basicOpen_iff]`.

Introduce `x hx`. Establish `hx2 : x ∈ ⨆ i, V i` using `by rw [hV]; trivial`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 hx2`. Take `⟨f, hf, hxf⟩` from `hW.exists_basicOpen_le ⟨x, hi⟩ hx`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, i, hf⟩, hxf⟩`.

Take `⟨F, hF, hFs⟩` from `(Submodule.fg_span_iff_fg_span_finset_subset {f : Γ(S, W) | ∃ i, S.basicOpen f ≤ V i}).1 (IsNoetherian.noetherian (R := Γ(S, W)) _)`. Establish `hF1 : Ideal.span (F : Set Γ(S, W)) = ⊤` using `hFs.symm.trans hspan`. Use `choose σ hσ using loc`. Set `s : Finset Γ(Sp K, gp ⁻¹ᵁ W)` to `F.attach.biUnion fun f => σ f.1 (hF f.2)`. Use `⟨s, fun y hy => ?_, fun x hx => ?_⟩` and prove the remaining obligations.

Take `⟨f, -, hf⟩` from `Finset.mem_biUnion.1 hy`. Conclude with `(hσ f.1 (hF f.2)).1 hf`. Establish `hxs : x ∈ Submodule.span Γ(S, W) (s : Set Γ(Sp K, gp ⁻¹ᵁ W))`. Use `Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (F : Set Γ(S, W)) hF1 x fun f => ?_` and prove the remaining obligations. Take `⟨n, hn⟩` from `(hσ f.1 (hF f.2)).2 x hx`.

Use `⟨n, Submodule.span_mono ?_ hn⟩` and prove the remaining obligations. Introduce `y hy`. Conclude with `Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨⟨f.1, f.2⟩, Finset.mem_attach _ _, hy⟩)`. Take `⟨c, hc⟩` from `Submodule.mem_span_finset.1 hxs`. Conclude with `⟨c, hc.2.symm⟩`.
-/
theorem finFam_finite {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) [IsLocallyNoetherian S] {r : ℕ}
    (V : Fin r → S.Opens) (t : ∀ i, Finset Γ(Sp K, gp ⁻¹ᵁ V i)) (hV : ⨆ i, V i = ⊤)
    (ht : ∀ i, ∀ y ∈ t i, (gp.app (V i)).hom.IsIntegralElem y) (W : S.Opens) (hW : IsAffineOpen W) :
    ∃ s : Finset Γ(Sp K, gp ⁻¹ᵁ W), (∀ y ∈ s, y ∈ finFam gp V t W) ∧
      ∀ x ∈ finFam gp V t W, ∃ c : Γ(Sp K, gp ⁻¹ᵁ W) → Γ(S, W), x = ∑ y ∈ s, (gp.app W).hom (c y) * y := by
  classical
  haveI : IsNoetherianRing Γ(S, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  letI : Algebra Γ(S, W) Γ(Sp K, gp ⁻¹ᵁ W) := (gp.app W).hom.toAlgebra
  have loc : ∀ f : Γ(S, W), (∃ i, S.basicOpen f ≤ V i) → ∃ s : Finset Γ(Sp K, gp ⁻¹ᵁ W),
      (s : Set Γ(Sp K, gp ⁻¹ᵁ W)) ⊆ (finFam gp V t W : Set Γ(Sp K, gp ⁻¹ᵁ W)) ∧
      ∀ x ∈ (finFam gp V t W : Set Γ(Sp K, gp ⁻¹ᵁ W)), ∃ n : ℕ,
        f ^ n • x ∈ Submodule.span Γ(S, W) (s : Set Γ(Sp K, gp ⁻¹ᵁ W)) := by
    rintro f ⟨i, hi⟩
    haveI := hW.isLocalization_basicOpen f
    refine exists_finset_pow_smul_mem (Rf := Γ(S, S.basicOpen f)) f (gp.app (S.basicOpen f)).hom
      (resK gp (S.basicOpen_le f)) (fun a => resK_app gp _ a) ?_ (resK gp hi '' (t i : Set _))
      ((t i).finite_toSet.image _) ?_ _ ?_
    · intro x hx
      obtain ⟨n, hn⟩ := pow_mul_eq_zero_of_res gp W f x hx
      exact ⟨n, by rw [Algebra.smul_def, map_pow]; exact hn⟩
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨p, hp, hp0⟩ := ht i y hy
      refine ⟨p.map (S.presheaf.map (homOfLE hi).op).hom, hp.map _, ?_⟩
      have e : (gp.app (S.basicOpen f)).hom.comp (S.presheaf.map (homOfLE hi).op).hom =
          (resK gp hi).comp (gp.app (V i)).hom := RingHom.ext fun a => (resK_app gp hi a).symm
      rw [Polynomial.eval₂_map, e, ← Polynomial.hom_eval₂, hp0, map_zero]
    · intro x hx
      have hii : S.basicOpen f ≤ W ⊓ V i := le_inf (S.basicOpen_le f) hi
      have h1 := (mem_finFam gp V t W x).1 hx i
      have hm : resK gp hii (resK gp (inf_le_left : W ⊓ V i ≤ W) x) ∈ (Subring.closure _).map (resK gp hii) :=
        ⟨_, h1, rfl⟩
      rw [RingHom.map_closure, resK_resK] at hm
      refine Subring.closure_mono ?_ hm
      rintro _ ⟨y, ⟨a, rfl⟩ | ⟨z, hz, rfl⟩, rfl⟩
      · exact Or.inl ⟨_, (resK_app gp hii a).symm⟩
      · exact Or.inr ⟨z, hz, by rw [resK_resK]⟩
  have hspan : Ideal.span {f : Γ(S, W) | ∃ i, S.basicOpen f ≤ V i} = ⊤ := by
    rw [← hW.self_le_iSup_basicOpen_iff]
    intro x hx
    have hx2 : x ∈ ⨆ i, V i := by rw [hV]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx2
    obtain ⟨f, hf, hxf⟩ := hW.exists_basicOpen_le ⟨x, hi⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, i, hf⟩, hxf⟩
  obtain ⟨F, hF, hFs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset
    {f : Γ(S, W) | ∃ i, S.basicOpen f ≤ V i}).1
    (IsNoetherian.noetherian (R := Γ(S, W)) _)
  have hF1 : Ideal.span (F : Set Γ(S, W)) = ⊤ := hFs.symm.trans hspan
  choose σ hσ using loc
  let s : Finset Γ(Sp K, gp ⁻¹ᵁ W) := F.attach.biUnion fun f => σ f.1 (hF f.2)
  refine ⟨s, fun y hy => ?_, fun x hx => ?_⟩
  · obtain ⟨f, -, hf⟩ := Finset.mem_biUnion.1 hy
    exact (hσ f.1 (hF f.2)).1 hf
  · have hxs : x ∈ Submodule.span Γ(S, W) (s : Set Γ(Sp K, gp ⁻¹ᵁ W)) := by
      refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (F : Set Γ(S, W)) hF1 x fun f => ?_
      obtain ⟨n, hn⟩ := (hσ f.1 (hF f.2)).2 x hx
      refine ⟨n, Submodule.span_mono ?_ hn⟩
      intro y hy
      exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨⟨f.1, f.2⟩, Finset.mem_attach _ _, hy⟩)
    obtain ⟨c, hc⟩ := Submodule.mem_span_finset.1 hxs
    exact ⟨c, hc.2.symm⟩

end GlobalTheory.FinitePowerAnnihilation
