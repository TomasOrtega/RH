import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
import GroundTheory.AutomorphicForms.RestrictedProductMatrix

open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open Filter

namespace UpperTheory.ConvolutionTheory.T4.RPGroup

section
universe u
variable {W V : Type} {I : V → Type}

/- English proof (translation)
Establish `h : ∀ w, ∃ x : X w, ∀ v i (h : ι v i = w), h ▸ T v i = x`. Introduce `w`. Take `⟨v, i, rfl⟩` from `hs w`. Use `⟨T v i, fun v' i' h => ?_⟩` and prove the remaining obligations. Establish `hv : v' = v` using `by rw [← hb v' i', h, hb]`.

Substitute `hv` using the available equality. Establish `hi : i' = i` using `hinj v' h`. Substitute `hi` using the available equality. Both sides reduce to the same expression. Use `choose f hf using h`.

Conclude with `⟨f, fun v i => (hf _ v i rfl).symm⟩`.
-/
private theorem exists_fam (ι : ∀ v, I v → W) (b : W → V) (hb : ∀ v i, b (ι v i) = v)
    (hinj : ∀ v, Function.Injective (ι v)) (hs : ∀ w, ∃ v i, ι v i = w)
    {X : W → Type u} (T : ∀ v (i : I v), X (ι v i)) :
    ∃ f : ∀ w, X w, ∀ v i, f (ι v i) = T v i := by
  have h : ∀ w, ∃ x : X w, ∀ v i (h : ι v i = w), h ▸ T v i = x := by
    intro w
    obtain ⟨v, i, rfl⟩ := hs w
    refine ⟨T v i, fun v' i' h => ?_⟩
    have hv : v' = v := by rw [← hb v' i', h, hb]
    subst hv
    have hi : i' = i := hinj v' h
    subst hi
    rfl
  choose f hf using h
  exact ⟨f, fun v i => (hf _ v i rfl).symm⟩

/- English proof (translation)
Rewrite `h`, the goal using `[eventually_cofinite]`. Use `(h.image b).subset fun v hv => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq, not_forall] at hv`. Take `⟨i, hi⟩` from `hv`. Conclude with `⟨ι v i, hi, hb v i⟩`.
-/
private theorem ev_up [∀ v, Finite (I v)] (ι : ∀ v, I v → W) (b : W → V) (hb : ∀ v i, b (ι v i) = v)
    {P : W → Prop} (h : ∀ᶠ w in cofinite, P w) : ∀ᶠ v in cofinite, ∀ i, P (ι v i) := by
  rw [eventually_cofinite] at h ⊢
  refine (h.image b).subset fun v hv => ?_
  simp only [Set.mem_setOf_eq, not_forall] at hv
  obtain ⟨i, hi⟩ := hv
  exact ⟨ι v i, hi, hb v i⟩

/- English proof (translation)
Rewrite `h`, the goal using `[eventually_cofinite]`. Use `(h.biUnion fun v _ => Set.finite_range (ι v)).subset fun w hw => ?_` and prove the remaining obligations. Take `⟨v, i, rfl⟩` from `hs w`. Simplify using `only [Set.mem_setOf_eq, hb] at hw`. Conclude with `Set.mem_biUnion hw ⟨i, rfl⟩`.
-/
private theorem ev_down [∀ v, Finite (I v)] (ι : ∀ v, I v → W) (b : W → V) (hb : ∀ v i, b (ι v i) = v)
    (hs : ∀ w, ∃ v i, ι v i = w) {P : V → Prop} (h : ∀ᶠ v in cofinite, P v) :
    ∀ᶠ w in cofinite, P (b w) := by
  rw [eventually_cofinite] at h ⊢
  refine (h.biUnion fun v _ => Set.finite_range (ι v)).subset fun w hw => ?_
  obtain ⟨v, i, rfl⟩ := hs w
  simp only [Set.mem_setOf_eq, hb] at hw
  exact Set.mem_biUnion hw ⟨i, rfl⟩

variable {G Gi : Type} {H : W → Type} {Gv : V → Type} [Group G] [Group Gi] [∀ w, Group (H w)]
  [∀ v, Group (Gv v)] [TopologicalSpace G] [TopologicalSpace Gi] [∀ w, TopologicalSpace (H w)]
  [∀ v, TopologicalSpace (Gv v)] [T2Space Gi] [∀ v, T2Space (Gv v)]

/- English proof (translation)
Establish `hcp : ∀ v, Continuous (p' v)`. Introduce `v`. Establish `h : ⇑(p' v) = fun g => (e v).symm (fun i => p (ι v i) g)`. Use function extensionality and compare the values at `g`. Apply `(e v).injective` to reduce the goal to its premises.

Rewrite using `[ContinuousMulEquiv.apply_symm_apply]`. Conclude with `funext fun i => hp v i g`. Rewrite using `[h]`. Conclude with `(e v).symm.continuous.comp (continuous_pi fun i => hRP.cp _)`. Establish `hKset : ∀ v, (K' v : Set (Gv v)) = e v ⁻¹' Set.pi Set.univ fun i => (K (ι v i) : Set _)`.

Introduce `v`. Use extensionality with `x`. Simplify using `only [SetLike.mem_coe, hK, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff]`. Use `⟨hRP.cq, hcp, fun v => ?_, fun v => ?_, fun g => ?_, fun S => ?_, fun g g' hq h => ?_, fun gi gv hgv => ?_, fun Ci C hCi hC hev => ?_⟩` and prove the remaining obligations. Rewrite using `[hKset]`.

Conclude with `(isOpen_set_pi Set.finite_univ fun i _ => hRP.opn _).preimage (e v).continuous`. Establish `h : (K' v : Set (Gv v)) = (e v).symm '' Set.pi Set.univ fun i => (K (ι v i) : Set _)`. Rewrite using `[hKset]`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Conclude with `⟨e v x, hx, (e v).symm_apply_apply x⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Simplify `hy` using `[Set.mem_preimage]`. Rewrite using `[h]`.

Conclude with `(isCompact_univ_pi fun i => hRP.cpt _).image (e v).symm.continuous`. Use `(ev_up ι b hb (hRP.ae g)).mono fun v h => ?_` and prove the remaining obligations. Rewrite using `[hK]`. Introduce `i`. Rewrite using `[hp]`.

Conclude with `h i`. Establish `hfin : (⋃ v ∈ (S : Set V), Set.range (ι v)).Finite` using `S.finite_toSet.biUnion fun v _ => Set.finite_range (ι v)`. Establish `hmem : ∀ w, w ∈ hfin.toFinset ↔ b w ∈ S`. Introduce `w`. Rewrite using `[Set.Finite.mem_toFinset]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨v, hv, i, rfl⟩` from `Set.mem_iUnion₂.1 h`. Rewrite using `[hb]`. Conclude with `hv`.

Introduce `h`. Take `⟨v, i, rfl⟩` from `hs w`. Rewrite `h` using `[hb]`. Conclude with `Set.mem_biUnion h ⟨i, rfl⟩`. Establish `h : (US p' K' S : Set G) = US p K hfin.toFinset`.

Use extensionality with `g`. Simplify using `only [SetLike.mem_coe, mem_US]`. Prove the components needed by the constructor for the conclusion. Introduce `h w hw`. Take `⟨v, i, rfl⟩` from `hs w`.

Establish `hv : v ∉ S`. Rewrite `hw` using `[hmem, hb]`. Conclude with `hw`. Use `(hK v _).1 (h v hv) i` as an intermediate fact. Rewrite `this` using `[hp]`. Then use the resulting hypothesis.

Introduce `h v hv`. Rewrite using `[hK]`. Introduce `i`. Rewrite using `[hp]`. Conclude with `h _ (by rw [hmem, hb]; exact hv)`.

Rewrite using `[h]`. Conclude with `hRP.opnU _`. Use `hRP.ext g g' hq fun w => ?_` and prove the remaining obligations. Take `⟨v, i, rfl⟩` from `hs w`. Rewrite using `[← hp, ← hp, h]`.

Take `⟨gw, hgw⟩` from `exists_fam ι b hb hinj hs (X := H) fun v i => e v (gv v) i`. Establish `hae : ∀ᶠ w in cofinite, gw w ∈ K w`. Use `(ev_down ι b hb hs hgv).mono fun w h => ?_` and prove the remaining obligations. Take `⟨v, i, rfl⟩` from `hs w`. Rewrite `h` using `[hb]`.

Rewrite using `[hgw]`. Conclude with `(hK v _).1 h i`. Take `⟨g, hq, hpg⟩` from `hRP.surj gi gw hae`. Use `⟨g, hq, fun v => (e v).injective (funext fun i => ?_)⟩` and prove the remaining obligations. Rewrite using `[hp, hpg, hgw]`.

Take `⟨D, hD⟩` from `exists_fam ι b hb hinj hs (X := fun w => Set (H w)) fun v i => (fun x => e v x i) '' C v`. Establish `hDc : ∀ w, IsCompact (D w)`. Introduce `w`. Take `⟨v, i, rfl⟩` from `hs w`. Rewrite using `[hD]`.

Conclude with `(hC v).image ((continuous_apply i).comp (e v).continuous)`. Establish `hDe : ∀ᶠ w in cofinite, D w ⊆ K w`. Use `(ev_down ι b hb hs hev).mono fun w h => ?_` and prove the remaining obligations. Take `⟨v, i, rfl⟩` from `hs w`. Rewrite `h` using `[hb]`.

Rewrite using `[hD]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `(hK v x).1 (h hx) i`. Establish `hA` using `hRP.prop Ci D hCi hDc hDe`. Establish `hcl : IsClosed {g | q g ∈ Ci ∧ ∀ v, p' v g ∈ C v}`.

Establish `h : {g | q g ∈ Ci ∧ ∀ v, p' v g ∈ C v} = q ⁻¹' Ci ∩ ⋂ v, p' v ⁻¹' C v`. Use extensionality with `g`. Simplify using the standard rewrite rules. Rewrite using `[h]`. Conclude with `(hCi.isClosed.preimage hRP.cq).inter (isClosed_iInter fun v => (hC v).isClosed.preimage (hcp v))`.

Use `hA.of_isClosed_subset hcl ?_` and prove the remaining obligations. Introduce and unpack `g ⟨h1, h2⟩`. Use `⟨h1, fun w => ?_⟩` and prove the remaining obligations. Take `⟨v, i, rfl⟩` from `hs w`. Rewrite using `[hD, ← hp]`.

Conclude with `⟨_, h2 v, rfl⟩`.
-/
private theorem rp_group [∀ v, Finite (I v)] {q : G →* Gi} {p : ∀ w, G →* H w} {K : ∀ w, Subgroup (H w)}
    (hRP : RP q p K) (ι : ∀ v, I v → W) (b : W → V) (hb : ∀ v i, b (ι v i) = v)
    (hinj : ∀ v, Function.Injective (ι v)) (hs : ∀ w, ∃ v i, ι v i = w)
    (e : ∀ v, Gv v ≃ₜ* ∀ i : I v, H (ι v i)) (p' : ∀ v, G →* Gv v) (K' : ∀ v, Subgroup (Gv v))
    (hp : ∀ v i g, e v (p' v g) i = p (ι v i) g)
    (hK : ∀ v x, x ∈ K' v ↔ ∀ i, e v x i ∈ K (ι v i)) : RP q p' K' := by
  have hcp : ∀ v, Continuous (p' v) := by
    intro v
    have h : ⇑(p' v) = fun g => (e v).symm (fun i => p (ι v i) g) := by
      funext g
      apply (e v).injective
      rw [ContinuousMulEquiv.apply_symm_apply]
      exact funext fun i => hp v i g
    rw [h]
    exact (e v).symm.continuous.comp (continuous_pi fun i => hRP.cp _)
  have hKset : ∀ v, (K' v : Set (Gv v)) = e v ⁻¹' Set.pi Set.univ fun i => (K (ι v i) : Set _) := by
    intro v
    ext x
    simp only [SetLike.mem_coe, hK, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff]
  refine ⟨hRP.cq, hcp, fun v => ?_, fun v => ?_, fun g => ?_, fun S => ?_, fun g g' hq h => ?_,
    fun gi gv hgv => ?_, fun Ci C hCi hC hev => ?_⟩
  · rw [hKset]
    exact (isOpen_set_pi Set.finite_univ fun i _ => hRP.opn _).preimage (e v).continuous
  · have h : (K' v : Set (Gv v)) = (e v).symm '' Set.pi Set.univ fun i => (K (ι v i) : Set _) := by
      rw [hKset]
      ext x
      constructor
      · intro hx
        exact ⟨e v x, hx, (e v).symm_apply_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        simpa [Set.mem_preimage] using hy
    rw [h]
    exact (isCompact_univ_pi fun i => hRP.cpt _).image (e v).symm.continuous
  · refine (ev_up ι b hb (hRP.ae g)).mono fun v h => ?_
    rw [hK]
    intro i
    rw [hp]
    exact h i
  · have hfin : (⋃ v ∈ (S : Set V), Set.range (ι v)).Finite :=
      S.finite_toSet.biUnion fun v _ => Set.finite_range (ι v)
    have hmem : ∀ w, w ∈ hfin.toFinset ↔ b w ∈ S := by
      intro w
      rw [Set.Finite.mem_toFinset]
      constructor
      · intro h
        obtain ⟨v, hv, i, rfl⟩ := Set.mem_iUnion₂.1 h
        rw [hb]
        exact hv
      · intro h
        obtain ⟨v, i, rfl⟩ := hs w
        rw [hb] at h
        exact Set.mem_biUnion h ⟨i, rfl⟩
    have h : (US p' K' S : Set G) = US p K hfin.toFinset := by
      ext g
      simp only [SetLike.mem_coe, mem_US]
      constructor
      · intro h w hw
        obtain ⟨v, i, rfl⟩ := hs w
        have hv : v ∉ S := by
          rw [hmem, hb] at hw
          exact hw
        have := (hK v _).1 (h v hv) i
        rwa [hp] at this
      · intro h v hv
        rw [hK]
        intro i
        rw [hp]
        exact h _ (by rw [hmem, hb]; exact hv)
    rw [h]
    exact hRP.opnU _
  · refine hRP.ext g g' hq fun w => ?_
    obtain ⟨v, i, rfl⟩ := hs w
    rw [← hp, ← hp, h]
  · obtain ⟨gw, hgw⟩ := exists_fam ι b hb hinj hs (X := H) fun v i => e v (gv v) i
    have hae : ∀ᶠ w in cofinite, gw w ∈ K w := by
      refine (ev_down ι b hb hs hgv).mono fun w h => ?_
      obtain ⟨v, i, rfl⟩ := hs w
      rw [hb] at h
      rw [hgw]
      exact (hK v _).1 h i
    obtain ⟨g, hq, hpg⟩ := hRP.surj gi gw hae
    refine ⟨g, hq, fun v => (e v).injective (funext fun i => ?_)⟩
    rw [hp, hpg, hgw]
  · obtain ⟨D, hD⟩ := exists_fam ι b hb hinj hs (X := fun w => Set (H w))
      fun v i => (fun x => e v x i) '' C v
    have hDc : ∀ w, IsCompact (D w) := by
      intro w
      obtain ⟨v, i, rfl⟩ := hs w
      rw [hD]
      exact (hC v).image ((continuous_apply i).comp (e v).continuous)
    have hDe : ∀ᶠ w in cofinite, D w ⊆ K w := by
      refine (ev_down ι b hb hs hev).mono fun w h => ?_
      obtain ⟨v, i, rfl⟩ := hs w
      rw [hb] at h
      rw [hD]
      rintro _ ⟨x, hx, rfl⟩
      exact (hK v x).1 (h hx) i
    have hA := hRP.prop Ci D hCi hDc hDe
    have hcl : IsClosed {g | q g ∈ Ci ∧ ∀ v, p' v g ∈ C v} := by
      have h : {g | q g ∈ Ci ∧ ∀ v, p' v g ∈ C v} = q ⁻¹' Ci ∩ ⋂ v, p' v ⁻¹' C v := by
        ext g
        simp
      rw [h]
      exact (hCi.isClosed.preimage hRP.cq).inter
        (isClosed_iInter fun v => (hC v).isClosed.preimage (hcp v))
    refine hA.of_isClosed_subset hcl ?_
    rintro g ⟨h1, h2⟩
    refine ⟨h1, fun w => ?_⟩
    obtain ⟨v, i, rfl⟩ := hs w
    rw [hD, ← hp]
    exact ⟨_, h2 v, rfl⟩

end

end UpperTheory.ConvolutionTheory.T4.RPGroup

open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange GroundTheory.Automorphic in
/- English proof (translation)
Introduce `hF F E _ _ _ _ _ n`. Use `UpperTheory.ConvolutionTheory.T4.RPGroup.rp_group (I := fun v : Pl F => PlacesOver E v) (hF E n) (fun v i => i.1) (below F) (fun v i => (below_eq_iff i.1 v).2 i.2) (fun v => Subtype.val_injective) (fun w => ⟨below F w, ⟨w, (below_eq_iff w _).1 rfl⟩, rfl⟩) (fun v => glPiEquiv (Fin …` and prove the remaining obligations. Introduce `v i g`. Use `Units.ext ?_` and prove the remaining obligations. Use extensionality with `a b`.

Both sides reduce to the same expression. Introduce `v x`. Establish `h : ∀ w : PlacesOver E v, mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) x = glPiEquiv (Fin n) (fun w : PlacesOver E v => w.1.adicCompletion E) x w`. Introduce `w`. Use `Units.ext ?_` and prove the remaining obligations.

Use extensionality with `a b`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `(∀ w : PlacesOver E v, _ ∈ _) ↔ _`. Conclude with `forall_congr' fun w => by rw [h w]`.
-/
theorem UpperTheory.restrictedProduct_extension_of_base_regroup :
    RPF → RPE := by
  intro hF F E _ _ _ _ _ n
  refine UpperTheory.ConvolutionTheory.T4.RPGroup.rp_group (I := fun v : Pl F => PlacesOver E v) (hF E n)
    (fun v i => i.1) (below F) (fun v i => (below_eq_iff i.1 v).2 i.2)
    (fun v => Subtype.val_injective)
    (fun w => ⟨below F w, ⟨w, (below_eq_iff w _).1 rfl⟩, rfl⟩)
    (fun v => glPiEquiv (Fin n) fun w : PlacesOver E v => w.1.adicCompletion E)
    (fun v => pE E n v) (fun v => KE E n v) ?_ ?_
  · intro v i g
    refine Units.ext ?_
    ext a b
    rfl
  · intro v x
    have h : ∀ w : PlacesOver E v,
        mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) x =
          glPiEquiv (Fin n) (fun w : PlacesOver E v => w.1.adicCompletion E) x w := by
      intro w
      refine Units.ext ?_
      ext a b
      rfl
    change (∀ w : PlacesOver E v, _ ∈ _) ↔ _
    exact forall_congr' fun w => by rw [h w]
