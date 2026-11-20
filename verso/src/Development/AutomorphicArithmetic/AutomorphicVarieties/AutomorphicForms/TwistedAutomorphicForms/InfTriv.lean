import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HilbertClassFieldOfGlobalArtinReciprocity

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.NormCompat

namespace UpperTheory.V.Af.Tw

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Set `T : Set (w.Completion)ˣ` to `Units.val ⁻¹' S`. Establish `hT : IsPreconnected T`. Establish `himg : Units.val '' T = S`. Use extensionality with `a`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨u, hu, rfl⟩`. Conclude with `hu`. Introduce `ha`. Establish `ha0 : a ≠ 0` using `fun h => h0 (h ▸ ha)`. Conclude with `⟨Units.mk0 a ha0, ha, rfl⟩`.

Rewrite using `[← Units.isEmbedding_val₀.isInducing.isPreconnected_image, himg]`. Conclude with `hS`. Set `φ : (w.Completion)ˣ →* (InfiniteAdeleRing E)ˣ` to `Units.map (MonoidHom.mulSingle (fun v : InfinitePlace E => v.Completion) w)`. Establish `hφ : Continuous φ` using `Continuous.units_map _ (continuous_mulSingle w)`. Establish `hsub : φ '' T ⊆ connectedComponent (1 : (InfiniteAdeleRing E)ˣ)` using `(hT.image _ hφ.continuousOn).subset_connectedComponent ⟨1, h1, map_one φ⟩`.

Unfold `infConn`. Use `⟨φ x, hsub ⟨x, hx, rfl⟩, ?_⟩` and prove the remaining obligations. Conclude with `Units.ext rfl`.
-/
private theorem mem_infConn_of (w : InfinitePlace E) (x : (w.Completion)ˣ) (S : Set w.Completion)
    (hS : IsPreconnected S) (h0 : 0 ∉ S) (h1 : 1 ∈ S) (hx : (x : w.Completion) ∈ S) : infIdele E w x ∈ infConn E := by
  classical
  let T : Set (w.Completion)ˣ := Units.val ⁻¹' S
  have hT : IsPreconnected T := by
    have himg : Units.val '' T = S := by
      ext a
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact hu
      · intro ha
        have ha0 : a ≠ 0 := fun h => h0 (h ▸ ha)
        exact ⟨Units.mk0 a ha0, ha, rfl⟩
    rw [← Units.isEmbedding_val₀.isInducing.isPreconnected_image, himg]
    exact hS
  let φ : (w.Completion)ˣ →* (InfiniteAdeleRing E)ˣ :=
    Units.map (MonoidHom.mulSingle (fun v : InfinitePlace E => v.Completion) w)
  have hφ : Continuous φ := Continuous.units_map _ (continuous_mulSingle w)
  have hsub : φ '' T ⊆ connectedComponent (1 : (InfiniteAdeleRing E)ˣ) :=
    (hT.image _ hφ.continuousOn).subset_connectedComponent ⟨1, h1, map_one φ⟩
  unfold infConn
  refine ⟨φ x, hsub ⟨x, hx, rfl⟩, ?_⟩
  exact Units.ext rfl

/- English proof (translation)
Establish `key : ∀ (K : Type) [NormedField K] (e : w.Completion ≃ᵢ K), (∀ a, e a = 0 ↔ a = 0) → e 1 = 1 → ∀ T : Set K, IsPreconnected T → (0 : K) ∉ T → (1 : K) ∈ T → ∀ y : (w.Completion)ˣ, e y ∈ T → infIdele E w y ∈ N`. Introduce `K _ e he0 he1 T hT hT0 hT1 y hy`. Apply `hN` to reduce the goal to its premises. Use `mem_infConn_of w y (e.symm '' T) (hT.image _ e.symm.continuous.continuousOn) ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨b, hb, hb0⟩`.

Establish `hb' : b = e 0` using `by rw [← hb0, e.apply_symm_apply]`. Rewrite `hb` using `[hb', (he0 0).2 rfl]`. Conclude with `hT0 hb`. Use `⟨1, hT1, ?_⟩` and prove the remaining obligations. Rewrite using `[← he1]`.

Conclude with `e.symm_apply_apply 1`. Conclude with `⟨e y, hy, e.symm_apply_apply _⟩`. Break down `InfinitePlace.isReal_or_isComplex w with hr | hc` into its components or cases. Set `e` to `InfinitePlace.Completion.isometryEquivRealOfIsReal hr`. Establish `he0 : ∀ a, e a = 0 ↔ a = 0` using `fun a => map_eq_zero_iff (InfinitePlace.Completion.extensionEmbeddingOfIsReal hr) (InfinitePlace.Completion.extensionEmbeddingOfIsReal hr).injective`.

Establish `he1 : e 1 = 1` using `map_one (InfinitePlace.Completion.extensionEmbeddingOfIsReal hr)`. Establish `hneg : ∀ a, e (-a) = - e a` using `fun a => map_neg (InfinitePlace.Completion.extensionEmbeddingOfIsReal hr) a`. Establish `hx0 : e x ≠ 0` using `fun h => x.ne_zero ((he0 _).1 h)`. Break down `lt_or_gt_of_ne hx0 with hlt | hgt` into its components or cases. Establish `hm : infIdele E w (-x) ∈ N` using `key ℝ e he0 he1 (Set.Ioi 0) isPreconnected_Ioi (by simp) (by simp) (-x) (by show e (-(x : w.Completion)) ∈ Set.Ioi 0`.

Rewrite using `[hneg]`. Conclude with `neg_pos.2 hlt)`. Establish `hx : x = (-1) * (-x)` using `by simp`. Rewrite using `[hx, map_mul]`. Conclude with `N.mul_mem (hs w hr) hm`.

Conclude with `key ℝ e he0 he1 (Set.Ioi 0) isPreconnected_Ioi (by simp) (by simp) x hgt`. Set `e` to `InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc`. Establish `he0 : ∀ a, e a = 0 ↔ a = 0` using `fun a => map_eq_zero_iff (InfinitePlace.Completion.extensionEmbedding w) (InfinitePlace.Completion.extensionEmbedding w).injective`. Establish `he1 : e 1 = 1` using `map_one (InfinitePlace.Completion.extensionEmbedding w)`. Use `key ℂ e he0 he1 {0}ᶜ ?_ (by simp) (by simp) x ?_` and prove the remaining obligations.

Conclude with `(isConnected_compl_singleton_of_one_lt_rank (by simp [Complex.rank_real_complex]) 0).isPreconnected`. Conclude with `fun h => x.ne_zero ((he0 _).1 h)`.
-/
private theorem mem_of_sign (N : Subgroup (Ideles E)) (hN : infConn E ≤ N)
    (hs : ∀ w : InfinitePlace E, w.IsReal → infIdele E w (-1) ∈ N) (w : InfinitePlace E) (x : (w.Completion)ˣ) :
    infIdele E w x ∈ N := by
  have key : ∀ (K : Type) [NormedField K] (e : w.Completion ≃ᵢ K), (∀ a, e a = 0 ↔ a = 0) → e 1 = 1 →
      ∀ T : Set K, IsPreconnected T → (0 : K) ∉ T → (1 : K) ∈ T →
      ∀ y : (w.Completion)ˣ, e y ∈ T → infIdele E w y ∈ N := by
    intro K _ e he0 he1 T hT hT0 hT1 y hy
    apply hN
    refine mem_infConn_of w y (e.symm '' T) (hT.image _ e.symm.continuous.continuousOn) ?_ ?_ ?_
    · rintro ⟨b, hb, hb0⟩
      have hb' : b = e 0 := by rw [← hb0, e.apply_symm_apply]
      rw [hb', (he0 0).2 rfl] at hb
      exact hT0 hb
    · refine ⟨1, hT1, ?_⟩
      rw [← he1]
      exact e.symm_apply_apply 1
    · exact ⟨e y, hy, e.symm_apply_apply _⟩
  rcases InfinitePlace.isReal_or_isComplex w with hr | hc
  · let e := InfinitePlace.Completion.isometryEquivRealOfIsReal hr
    have he0 : ∀ a, e a = 0 ↔ a = 0 := fun a =>
      map_eq_zero_iff (InfinitePlace.Completion.extensionEmbeddingOfIsReal hr)
        (InfinitePlace.Completion.extensionEmbeddingOfIsReal hr).injective
    have he1 : e 1 = 1 := map_one (InfinitePlace.Completion.extensionEmbeddingOfIsReal hr)
    have hneg : ∀ a, e (-a) = - e a := fun a =>
      map_neg (InfinitePlace.Completion.extensionEmbeddingOfIsReal hr) a
    have hx0 : e x ≠ 0 := fun h => x.ne_zero ((he0 _).1 h)
    rcases lt_or_gt_of_ne hx0 with hlt | hgt
    · have hm : infIdele E w (-x) ∈ N := key ℝ e he0 he1 (Set.Ioi 0) isPreconnected_Ioi
        (by simp) (by simp) (-x) (by
          show e (-(x : w.Completion)) ∈ Set.Ioi 0
          rw [hneg]
          exact neg_pos.2 hlt)
      have hx : x = (-1) * (-x) := by simp
      rw [hx, map_mul]
      exact N.mul_mem (hs w hr) hm
    · exact key ℝ e he0 he1 (Set.Ioi 0) isPreconnected_Ioi (by simp) (by simp) x hgt
  · let e := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc
    have he0 : ∀ a, e a = 0 ↔ a = 0 := fun a =>
      map_eq_zero_iff (InfinitePlace.Completion.extensionEmbedding w)
        (InfinitePlace.Completion.extensionEmbedding w).injective
    have he1 : e 1 = 1 := map_one (InfinitePlace.Completion.extensionEmbedding w)
    refine key ℂ e he0 he1 {0}ᶜ ?_ (by simp) (by simp) x ?_
    · exact (isConnected_compl_singleton_of_one_lt_rank (by simp [Complex.rank_real_complex]) 0).isPreconnected
    · exact fun h => x.ne_zero ((he0 _).1 h)

/- English proof (translation)
Set `y : ∀ w : InfinitePlace E, (w.Completion)ˣ` to `fun w => ⟨z.val.1 w, z.inv.1 w, congrFun (congrArg Prod.fst z.val_inv) w, congrFun (congrArg Prod.fst z.inv_val) w⟩`. Use `⟨y, ?_⟩` and prove the remaining obligations. Use `ext1`. Rewrite using `[Units.coe_prod]`. Establish `h1` using `map_prod (MonoidHom.fst (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)) (fun i => ((infIdele E i (y i)).val : InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E)) Finset.univ`.

Establish `h2` using `map_prod (MonoidHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)) (fun i => ((infIdele E i (y i)).val : InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E)) Finset.univ`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `Eq.trans ?_ h1.symm` and prove the remaining obligations. Use function extensionality and compare the values at `v`. Establish `h3` using `map_prod (Pi.evalMonoidHom (fun w : InfinitePlace E => w.Completion) v) (fun i => (Pi.mulSingle i (z.val.1 i) : ∀ w : InfinitePlace E, w.Completion)) Finset.univ`.

Use `Eq.trans ?_ h3.symm` and prove the remaining obligations. Rewrite using `[Finset.prod_eq_single v]`. Use `show z.val.1 v = Pi.mulSingle v (z.val.1 v) v`. Rewrite using `[Pi.mulSingle_eq_same]`. Introduce `b _ hb show Pi.mulSingle b (z.val.1 b) v = 1`.

Conclude with `Pi.mulSingle_eq_of_ne hb.symm _`. Introduce `h`. Conclude with `absurd (Finset.mem_univ v) h`. Use `Eq.trans ?_ h2.symm` and prove the remaining obligations. Rewrite using `[hz]`.

Use `symm`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `i _`. Both sides reduce to the same expression.
-/
private theorem eq_prod_infIdele (z : Ideles E) (hz : z.val.2 = 1) :
    ∃ y : ∀ w : InfinitePlace E, (w.Completion)ˣ, z = ∏ w, infIdele E w (y w) := by
  classical
  let y : ∀ w : InfinitePlace E, (w.Completion)ˣ := fun w => ⟨z.val.1 w, z.inv.1 w,
    congrFun (congrArg Prod.fst z.val_inv) w, congrFun (congrArg Prod.fst z.inv_val) w⟩
  refine ⟨y, ?_⟩
  ext1
  rw [Units.coe_prod]
  have h1 := map_prod (MonoidHom.fst (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))
    (fun i => ((infIdele E i (y i)).val : InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E)) Finset.univ
  have h2 := map_prod (MonoidHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))
    (fun i => ((infIdele E i (y i)).val : InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E)) Finset.univ
  refine Prod.ext ?_ ?_
  · refine Eq.trans ?_ h1.symm
    funext v
    have h3 := map_prod (Pi.evalMonoidHom (fun w : InfinitePlace E => w.Completion) v)
      (fun i => (Pi.mulSingle i (z.val.1 i) : ∀ w : InfinitePlace E, w.Completion)) Finset.univ
    refine Eq.trans ?_ h3.symm
    rw [Finset.prod_eq_single v]
    · show z.val.1 v = Pi.mulSingle v (z.val.1 v) v
      rw [Pi.mulSingle_eq_same]
    · intro b _ hb
      show Pi.mulSingle b (z.val.1 b) v = 1
      exact Pi.mulSingle_eq_of_ne hb.symm _
    · intro h
      exact absurd (Finset.mem_univ v) h
  · refine Eq.trans ?_ h2.symm
    rw [hz]
    symm
    apply Finset.prod_eq_one
    intro i _
    rfl

end UpperTheory.V.Af.Tw

/- English proof (translation)
Introduce `F Ω B _ _ _ _ _ _ _ _ _ art ha ν hν hc z σ hz hσ`. Set `N : Subgroup (Ideles F)` to `((liftAb ν hν).comp art).ker`. Establish `hN : infConn F ≤ N` using `fun x hx => by`. Establish `h : x ∈ art.ker`. Rewrite using `[ha.ker]`.

Conclude with `Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_right hx)`. Use `show liftAb ν hν (art x) = 1`. Rewrite using `[show art x = 1 from h, map_one]`. Establish `hs : ∀ w : InfinitePlace F, w.IsReal → infIdele F w (-1) ∈ N` using `fun w hw => by`. Take `⟨j, c, hj, rfl⟩` from `GlobalTheory.HilbertFromArtin.exists_conj (Ω := Ω) w hw`.

Use `show liftAb ν hν (art _) = 1`. Rewrite using `[GlobalTheory.HilbertFromArtin.art_sign_eq ha j c hj, liftAb_toAb]`. Conclude with `hc c ⟨j, hj⟩`. Take `⟨y, hy⟩` from `eq_prod_infIdele z hz`. Establish `hm : z ∈ N` using `hy ▸ prod_mem fun w _ => mem_of_sign N hN hs w (y w)`.

Establish `hm' : liftAb ν hν (art z) = 1` using `hm`. Rewrite `hm'` using `[hσ, liftAb_toAb]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.Af.Tw.infTriv :
    UpperTheory.V.Af.Tw.InfTriv := by
  intro F Ω B _ _ _ _ _ _ _ _ _ art ha ν hν hc z σ hz hσ
  let N : Subgroup (Ideles F) := ((liftAb ν hν).comp art).ker
  have hN : infConn F ≤ N := fun x hx => by
    have h : x ∈ art.ker := by
      rw [ha.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_right hx)
    show liftAb ν hν (art x) = 1
    rw [show art x = 1 from h, map_one]
  have hs : ∀ w : InfinitePlace F, w.IsReal → infIdele F w (-1) ∈ N := fun w hw => by
    obtain ⟨j, c, hj, rfl⟩ := GlobalTheory.HilbertFromArtin.exists_conj (Ω := Ω) w hw
    show liftAb ν hν (art _) = 1
    rw [GlobalTheory.HilbertFromArtin.art_sign_eq ha j c hj, liftAb_toAb]
    exact hc c ⟨j, hj⟩
  obtain ⟨y, hy⟩ := eq_prod_infIdele z hz
  have hm : z ∈ N := hy ▸ prod_mem fun w _ => mem_of_sign N hN hs w (y w)
  have hm' : liftAb ν hν (art z) = 1 := hm
  rwa [hσ, liftAb_toAb] at hm'
