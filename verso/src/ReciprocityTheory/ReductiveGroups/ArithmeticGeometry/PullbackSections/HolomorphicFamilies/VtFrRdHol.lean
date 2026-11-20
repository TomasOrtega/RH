import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetC

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt

/- English proof (translation)
Use `set R := Subring.closure (Set.range inl.hom ∪ Set.range inr.hom) with hR`. Set `l : B ⟶ CommRingCat.of R` to `CommRingCat.ofHom (inl.hom.codRestrict R fun b => Subring.subset_closure (Or.inl ⟨b, rfl⟩))`. Set `r : C ⟶ CommRingCat.of R` to `CommRingCat.ofHom (inr.hom.codRestrict R fun c => Subring.subset_closure (Or.inr ⟨c, rfl⟩))`. Establish `w : f ≫ l = g ≫ r`. Use extensionality with `a`.

Use `congrArg (fun q : A ⟶ P => q.hom a) h.w` as an intermediate fact. Simplify `this` using `[l, r]`. Set `i : CommRingCat.of R ⟶ P` to `CommRingCat.ofHom R.subtype`. Establish `hid : h.desc l r w ≫ i = 𝟙 P`. Apply `h.hom_ext` to reduce the goal to its premises.

Use extensionality with `b`. Simplify using `[l, i]`. Use extensionality with `c`. Simplify using `[r, i]`. Use `eq_top_iff.2 fun x _ => ?_` and prove the remaining obligations.

Establish `hx : (((h.desc l r w).hom x : R) : P) = x`. Use `congrArg (fun q : P ⟶ P => q.hom x) hid` as an intermediate fact. Simplify `this` using `[i]`. Rewrite using `[← hx]`. Conclude with `((h.desc l r w).hom x).2`.
-/
theorem vtf_closure_eq_top {A B C P : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {inl : B ⟶ P}
    {inr : C ⟶ P} (h : IsPushout f g inl inr) :
    Subring.closure (Set.range inl.hom ∪ Set.range inr.hom) = ⊤ := by
  set R := Subring.closure (Set.range inl.hom ∪ Set.range inr.hom) with hR
  let l : B ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (inl.hom.codRestrict R fun b => Subring.subset_closure (Or.inl ⟨b, rfl⟩))
  let r : C ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (inr.hom.codRestrict R fun c => Subring.subset_closure (Or.inr ⟨c, rfl⟩))
  have w : f ≫ l = g ≫ r := by
    ext a
    have := congrArg (fun q : A ⟶ P => q.hom a) h.w
    simpa [l, r] using this
  let i : CommRingCat.of R ⟶ P := CommRingCat.ofHom R.subtype
  have hid : h.desc l r w ≫ i = 𝟙 P := by
    apply h.hom_ext
    · ext b
      simp [l, i]
    · ext c
      simp [r, i]
  refine eq_top_iff.2 fun x _ => ?_
  have hx : (((h.desc l r w).hom x : R) : P) = x := by
    have := congrArg (fun q : P ⟶ P => q.hom x) hid
    simpa [i] using this
  rw [← hx]
  exact ((h.desc l r w).hom x).2

/- English proof (translation)
Establish `: Subsingleton (PrimeSpectrum ℂ)` using `inferInstance`. Conclude with `this.elim q cpt`.
-/
theorem vtf_pt_eq (q : Sp ℂ) : q = cpt := by
  have : Subsingleton (PrimeSpectrum ℂ) := inferInstance
  exact this.elim q cpt

/- English proof (translation)
The claim follows from `h trivial`.
-/
theorem vtf_mem {Z : Scheme.{0}} {x : Sp ℂ ⟶ Z} {U : Z.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) : x cpt ∈ U :=
  h trivial

/- English proof (translation)
Introduce and unpack `_ ⟨q, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι, vtf_pt_eq q]`. Conclude with `vtf_mem h`.
-/
theorem vtf_range {Z : Scheme.{0}} (x : Sp ℂ ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    Set.range x ⊆ Set.range U.ι := by
  rintro _ ⟨q, rfl⟩
  rw [Scheme.Opens.range_ι, vtf_pt_eq q]
  exact vtf_mem h

/- English proof (translation)
The claim follows from `le_top`.
-/
theorem vtf_top {Z : Scheme.{0}} (x : Sp ℂ ⟶ Z) : ⊤ ≤ x ⁻¹ᵁ (⊤ : Z.Opens) := le_top

section Fibre

variable {g : ℕ} {X Y : Scheme.{0}} (f : Y ⟶ X) (u : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y))
  (he : ∀ z, e z ≫ f = u)

def vtfLift (z : Fin g → ℂ) : Sp ℂ ⟶ pullback f u :=
  pullback.lift (e z) (𝟙 _) (by rw [he z, Category.id_comp])

set_option maxHeartbeats 800000 in
/- English proof (translation)
Take `⟨W, hW, huW, -⟩` from `exists_isAffineOpen_mem_and_subset (x := u cpt) (U := ⊤) trivial`. Establish `hfy : e z0 cpt ∈ f ⁻¹ᵁ W` using `by show f (e z0 cpt) ∈ W`. Rewrite using `[← Scheme.Hom.comp_apply, he]`. Conclude with `huW`. Take `⟨U, hU, hyU, hUW⟩` from `exists_isAffineOpen_mem_and_subset hfy`.

Establish `: IsAffine U` using `hU`. Establish `: IsAffine W` using `hW`. Establish `hUr : Set.range (U.ι ≫ f) ⊆ Set.range W.ι`. Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι, Scheme.Hom.comp_apply]`.

Conclude with `hUW y.2`. Set `fU : U.toScheme ⟶ W.toScheme` to `IsOpenImmersion.lift W.ι (U.ι ≫ f) hUr`. Set `uW : Sp ℂ ⟶ W.toScheme` to `IsOpenImmersion.lift W.ι u (vtf_range u W (top_le_of_mem huW))`. Establish `hSU : IsOpen {z | ⊤ ≤ e z ⁻¹ᵁ U}` using `(hol U 0).1`. Establish `h0U : ⊤ ≤ e z0 ⁻¹ᵁ U` using `top_le_of_mem hyU`.

Set `eU : (Fin g → ℂ) → (Sp ℂ ⟶ U.toScheme)` to `fun z => if h : ⊤ ≤ e z ⁻¹ᵁ U then IsOpenImmersion.lift U.ι (e z) (vtf_range (e z) U h) else IsOpenImmersion.lift U.ι (e z0) (vtf_range (e z0) U h0U)`. Establish `heU : ∀ z, ⊤ ≤ e z ⁻¹ᵁ U → eU z ≫ U.ι = e z` using `fun z h => by`. Simplify using `only [eU, dif_pos h, IsOpenImmersion.lift_fac]`. Establish `heU' : ∀ z, eU z ≫ fU = uW` using `fun z => by`. Rewrite using `[← cancel_mono W.ι]`.

Simplify using `only [fU, uW, Category.assoc, IsOpenImmersion.lift_fac]`. Distinguish the cases in `h : ⊤ ≤ e z ⁻¹ᵁ U`. Rewrite using `[← Category.assoc, heU z h, he]`. Simplify using `only [eU, dif_neg h, IsOpenImmersion.lift_fac_assoc, he]`. Establish `hpb : IsPullback (pullback.fst fU uW) (pullback.snd fU uW) fU uW` using `IsPullback.of_hasPullback fU uW`.

Establish `hgen` using `vtf_closure_eq_top (isPushout_appTop_of_isPullback hpb)`. Establish `hw' : (pullback.fst fU uW ≫ U.ι) ≫ f = pullback.snd fU uW ≫ u`. Rewrite using `[Category.assoc, ← IsOpenImmersion.lift_fac W.ι (U.ι ≫ f) hUr, ← Category.assoc, pullback.condition, Category.assoc, IsOpenImmersion.lift_fac]`. Set `ι' : pullback fU uW ⟶ pullback f u` to `pullback.lift (pullback.fst fU uW ≫ U.ι) (pullback.snd fU uW) hw'`. Set `pP : (Fin g → ℂ) → (Sp ℂ ⟶ pullback fU uW)` to `fun z => pullback.lift (eU z) (𝟙 _) (by rw [heU' z, Category.id_comp])`.

Establish `hpP : ∀ z, ⊤ ≤ e z ⁻¹ᵁ U → pP z ≫ ι' = vtfLift f u e he z` using `fun z h => by`. Apply `pullback.hom_ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `pullback.lift (eU z) (𝟙 _) _ ≫ pullback.lift (pullback.fst fU uW ≫ U.ι) (pullback.snd fU uW) hw' ≫ pullback.fst f u = pullback.lift (e z) (𝟙 _) _ ≫ pullback.fst f u`. Rewrite using `[pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc, heU z h]`. Express the relevant statement in the definitionally equal form `pullback.lift (eU z) (𝟙 _) _ ≫ pullback.lift (pullback.fst fU uW ≫ U.ι) (pullback.snd fU uW) hw' ≫ pullback.snd f u = pullback.lift (e z) (𝟙 _) _ ≫ pullback.snd f u`.

Rewrite using `[pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]`. Establish `hUimg : U ≤ U.ι ''ᵁ ⊤`. Rewrite using `[Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]`. Establish `hfst : ∀ b : Γ(U.toScheme, ⊤), DifferentiableOn ℂ (fun z => valAt' (pP z) ⊤ ((pullback.fst fU uW).appTop.hom b)) {z | ⊤ ≤ e z ⁻¹ᵁ U}`. Introduce `b`.

Take `⟨b', rfl⟩ : ∃ b', (U.ι.appIso ⊤).hom.hom b' = b` from `⟨(U.ι.appIso ⊤).inv.hom b, by exact congrArg (fun q => q.hom b) (U.ι.appIso ⊤).inv_hom_id⟩`. Establish `key : ∀ z, ⊤ ≤ e z ⁻¹ᵁ U → valAt' (pP z) ⊤ ((pullback.fst fU uW).appTop.hom ((U.ι.appIso ⊤).hom.hom b')) = valAt' (e z) (U.ι ''ᵁ ⊤) b'`. Introduce `z hz`. Establish `e1 : valAt' (pP z) ⊤ ((pullback.fst fU uW).appTop.hom ((U.ι.appIso ⊤).hom.hom b')) = valAt' (pP z ≫ pullback.fst fU uW) ⊤ ((U.ι.appIso ⊤).hom.hom b')`. Conclude with `valAt'_comp (pP z) (pullback.fst fU uW) ⊤ _`.

Establish `e2 : pP z ≫ pullback.fst fU uW = eU z` using `pullback.lift_fst _ _ _`. Rewrite using `[e1, e2, Scheme.Hom.appIso_hom', Scheme.Hom.appLE, CommRingCat.comp_apply, valAt'_res _ _ (vtf_top _), valAt'_comp, heU z hz]`. Use `((hol _ b').2.mono fun z hz => ?_).congr fun z hz => key z hz` and prove the remaining obligations. Conclude with `top_le_of_mem (hUimg (vtf_mem hz))`. Establish `hsnd : ∀ c : Γ(Sp ℂ, ⊤), DifferentiableOn ℂ (fun z => valAt' (pP z) ⊤ ((pullback.snd fU uW).appTop.hom c)) {z | ⊤ ≤ e z ⁻¹ᵁ U}`.

Introduce `c`. Use `(differentiableOn_const (valAt' (𝟙 (Sp ℂ)) ⊤ c)).congr fun z _ => ?_` and prove the remaining obligations. Establish `e1 : valAt' (pP z) ⊤ ((pullback.snd fU uW).appTop.hom c) = valAt' (pP z ≫ pullback.snd fU uW) ⊤ c`. Conclude with `valAt'_comp (pP z) (pullback.snd fU uW) ⊤ _`. Establish `e2 : pP z ≫ pullback.snd fU uW = 𝟙 _` using `pullback.lift_snd _ _ _`.

Rewrite using `[e1, e2]`. Establish `hv : ∀ (x : Sp ℂ ⟶ pullback fU uW) (a : Γ(pullback fU uW, ⊤)), valHom x ⊤ (vtf_top x) a = valAt' x ⊤ a` using `fun _ _ => rfl`. Establish `hall : ∀ a : Γ(pullback fU uW, ⊤), DifferentiableOn ℂ (fun z => valAt' (pP z) ⊤ a) {z | ⊤ ≤ e z ⁻¹ᵁ U}`. Introduce `a`. Establish `ha : a ∈ Subring.closure (Set.range (pullback.fst fU uW).appTop.hom ∪ Set.range (pullback.snd fU uW).appTop.hom)`.

Rewrite using `[hgen]`. Conclude with `Subring.mem_top a`. Proceed by induction on `ha using Subring.closure_induction with`. Consider the case `mem x hx`. Break down `hx with ⟨b, rfl⟩ | ⟨c, rfl⟩` into its components or cases.

Conclude with `hfst b`. Conclude with `hsnd c`. Consider the case `zero => exact (differentiableOn_const 0).congr fun z _ => (hv _ _).symm.trans (map_zero _)`. Consider the case `one => exact (differentiableOn_const 1).congr fun z _ => (hv _ _).symm.trans (map_one _)`. Consider the case `add x y _ _ hx hy`.

Conclude with `(hx.add hy).congr fun z _ => (hv _ _).symm.trans (map_add _ _ _)`. Consider the case `neg x _ hx => exact hx.neg.congr fun z _ => (hv _ _).symm.trans (map_neg _ _)`. Consider the case `mul x y _ _ hx hy`. Conclude with `(hx.mul hy).congr fun z _ => (hv _ _).symm.trans (map_mul _ _ _)`. Establish `hz0' : pP z0 cpt ∈ ι' ⁻¹ᵁ V` using `by show ι' (pP z0 cpt) ∈ V`.

Rewrite using `[← Scheme.Hom.comp_apply, hpP z0 h0U]`. Conclude with `vtf_mem hz0`. Take `⟨h, hle, hmem⟩` from `(isAffineOpen_top (pullback fU uW)).exists_basicOpen_le ⟨pP z0 cpt, hz0'⟩ trivial`. Use `haveI := (isAffineOpen_top (pullback fU uW)).isLocalization_basicOpen h`. Set `ψ : Γ(pullback fU uW, (pullback fU uW).basicOpen h)` to `((pullback fU uW).presheaf.map (homOfLE hle).op).hom ((ι'.app V).hom φ)`.

Take `⟨⟨a, s⟩, hs⟩` from `IsLocalization.surj (Submonoid.powers h) ψ`. Simplify using `only at hs`. Take `⟨n, hn⟩` from `s.2`. Establish `hpow : ∀ z, valAt' (pP z) ⊤ (h ^ n) = valAt' (pP z) ⊤ h ^ n` using `fun z => (hv _ _).symm.trans ((map_pow _ _ _).trans (congrArg (· ^ n) (hv _ _)))`. Establish `hal : ∀ q : Γ(pullback fU uW, ⊤), algebraMap Γ(pullback fU uW, ⊤) Γ(pullback fU uW, (pullback fU uW).basicOpen h) q = ((pullback fU uW).presheaf.map (homOfLE ((pullback fU uW).basicOpen_le h)).op).hom q` using `fun _ => rfl`.

Set `N : Set (Fin g → ℂ)` to `{z | ⊤ ≤ e z ⁻¹ᵁ U} ∩ (fun z => valAt' (pP z) ⊤ h) ⁻¹' {0}ᶜ`. Establish `hN : IsOpen N` using `(hall h).continuousOn.isOpen_inter_preimage hSU isOpen_compl_singleton`. Establish `hD : ∀ z ∈ N, ⊤ ≤ pP z ⁻¹ᵁ (pullback fU uW).basicOpen h` using `fun z hz => top_le_of_mem ((valAt'_ne_zero_iff (pP z) ⊤ (vtf_top _) h cpt).1 hz.2)`. Establish `hVz : ∀ z ∈ N, ⊤ ≤ vtfLift f u e he z ⁻¹ᵁ V` using `fun z hz => by`. Apply `top_le_of_mem` to reduce the goal to its premises.

Rewrite using `[← hpP z hz.1, Scheme.Hom.comp_apply]`. Conclude with `hle (vtf_mem (hD z hz))`. Establish `hval : ∀ z ∈ N, valAt' (vtfLift f u e he z) V φ = valAt' (pP z) ⊤ a * (valAt' (pP z) ⊤ (h ^ n))⁻¹`. Introduce `z hz`. Establish `hne : valAt' (pP z) ⊤ h ≠ 0` using `hz.2`.

Establish `e1 : valAt' (vtfLift f u e he z) V φ = valAt' (pP z) _ ψ`. Rewrite using `[← hpP z hz.1, ← valAt'_comp]`. Conclude with `(valAt'_res _ hle (hD z hz) _).symm`. Establish `e3 : valAt' (pP z) _ ψ * valAt' (pP z) ⊤ (h ^ n) = valAt' (pP z) ⊤ a`. Establish `e2` using `congrArg (valHom (pP z) _ (hD z hz)) hs`.

Rewrite `e2` using `[map_mul]`. Establish `ra : valHom (pP z) _ (hD z hz) (algebraMap Γ(pullback fU uW, ⊤) _ a) = valAt' (pP z) ⊤ a`. Conclude with `valAt'_res (pP z) ((pullback fU uW).basicOpen_le h) (hD z hz) a`. Establish `rs : valHom (pP z) _ (hD z hz) (algebraMap Γ(pullback fU uW, ⊤) _ (s : Γ(pullback fU uW, ⊤))) = valAt' (pP z) ⊤ (h ^ n)`. Rewrite using `[← hn]`.

Conclude with `valAt'_res (pP z) ((pullback fU uW).basicOpen_le h) (hD z hz) _`. Rewrite `e2` using `[ra, rs]`. Conclude with `e2`. Rewrite using `[e1, eq_mul_inv_iff_mul_eq₀ (by rw [hpow]; exact pow_ne_zero _ hne), e3]`. Use `⟨N, hN, ⟨h0U, ?_⟩, hVz, ?_⟩` and prove the remaining obligations.

Conclude with `(valAt'_ne_zero_iff (pP z0) ⊤ (vtf_top _) h cpt).2 hmem`. Use `(((hall a).mono Set.inter_subset_left).mul (((hall (h ^ n)).mono Set.inter_subset_left).inv fun z hz => ?_)).congr fun z hz => hval z hz` and prove the remaining obligations. Rewrite using `[hpow]`. Conclude with `pow_ne_zero _ hz.2`.
-/
theorem vtf_local (hol : IsHolFam e) (V : (pullback f u).Opens) (φ : Γ(pullback f u, V))
    (z0 : Fin g → ℂ) (hz0 : ⊤ ≤ vtfLift f u e he z0 ⁻¹ᵁ V) :
    ∃ N : Set (Fin g → ℂ), IsOpen N ∧ z0 ∈ N ∧ (∀ z ∈ N, ⊤ ≤ vtfLift f u e he z ⁻¹ᵁ V) ∧
      DifferentiableOn ℂ (fun z => valAt' (vtfLift f u e he z) V φ) N := by
  classical
  obtain ⟨W, hW, huW, -⟩ := exists_isAffineOpen_mem_and_subset (x := u cpt) (U := ⊤) trivial
  have hfy : e z0 cpt ∈ f ⁻¹ᵁ W := by
    show f (e z0 cpt) ∈ W
    rw [← Scheme.Hom.comp_apply, he]
    exact huW
  obtain ⟨U, hU, hyU, hUW⟩ := exists_isAffineOpen_mem_and_subset hfy
  have : IsAffine U := hU
  have : IsAffine W := hW
  have hUr : Set.range (U.ι ≫ f) ⊆ Set.range W.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact hUW y.2
  let fU : U.toScheme ⟶ W.toScheme := IsOpenImmersion.lift W.ι (U.ι ≫ f) hUr
  let uW : Sp ℂ ⟶ W.toScheme := IsOpenImmersion.lift W.ι u (vtf_range u W (top_le_of_mem huW))
  have hSU : IsOpen {z | ⊤ ≤ e z ⁻¹ᵁ U} := (hol U 0).1
  have h0U : ⊤ ≤ e z0 ⁻¹ᵁ U := top_le_of_mem hyU
  let eU : (Fin g → ℂ) → (Sp ℂ ⟶ U.toScheme) := fun z =>
    if h : ⊤ ≤ e z ⁻¹ᵁ U then IsOpenImmersion.lift U.ι (e z) (vtf_range (e z) U h)
    else IsOpenImmersion.lift U.ι (e z0) (vtf_range (e z0) U h0U)
  have heU : ∀ z, ⊤ ≤ e z ⁻¹ᵁ U → eU z ≫ U.ι = e z := fun z h => by
    simp only [eU, dif_pos h, IsOpenImmersion.lift_fac]
  have heU' : ∀ z, eU z ≫ fU = uW := fun z => by
    rw [← cancel_mono W.ι]
    simp only [fU, uW, Category.assoc, IsOpenImmersion.lift_fac]
    by_cases h : ⊤ ≤ e z ⁻¹ᵁ U
    · rw [← Category.assoc, heU z h, he]
    · simp only [eU, dif_neg h, IsOpenImmersion.lift_fac_assoc, he]
  have hpb : IsPullback (pullback.fst fU uW) (pullback.snd fU uW) fU uW := IsPullback.of_hasPullback fU uW
  have hgen := vtf_closure_eq_top (isPushout_appTop_of_isPullback hpb)
  have hw' : (pullback.fst fU uW ≫ U.ι) ≫ f = pullback.snd fU uW ≫ u := by
    rw [Category.assoc, ← IsOpenImmersion.lift_fac W.ι (U.ι ≫ f) hUr, ← Category.assoc, pullback.condition,
      Category.assoc, IsOpenImmersion.lift_fac]
  let ι' : pullback fU uW ⟶ pullback f u := pullback.lift (pullback.fst fU uW ≫ U.ι) (pullback.snd fU uW) hw'
  let pP : (Fin g → ℂ) → (Sp ℂ ⟶ pullback fU uW) := fun z =>
    pullback.lift (eU z) (𝟙 _) (by rw [heU' z, Category.id_comp])
  have hpP : ∀ z, ⊤ ≤ e z ⁻¹ᵁ U → pP z ≫ ι' = vtfLift f u e he z := fun z h => by
    apply pullback.hom_ext
    · change pullback.lift (eU z) (𝟙 _) _ ≫ pullback.lift (pullback.fst fU uW ≫ U.ι) (pullback.snd fU uW) hw' ≫
        pullback.fst f u = pullback.lift (e z) (𝟙 _) _ ≫ pullback.fst f u
      rw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc, heU z h]
    · change pullback.lift (eU z) (𝟙 _) _ ≫ pullback.lift (pullback.fst fU uW ≫ U.ι) (pullback.snd fU uW) hw' ≫
        pullback.snd f u = pullback.lift (e z) (𝟙 _) _ ≫ pullback.snd f u
      rw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
  have hUimg : U ≤ U.ι ''ᵁ ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  have hfst : ∀ b : Γ(U.toScheme, ⊤), DifferentiableOn ℂ
      (fun z => valAt' (pP z) ⊤ ((pullback.fst fU uW).appTop.hom b)) {z | ⊤ ≤ e z ⁻¹ᵁ U} := by
    intro b
    obtain ⟨b', rfl⟩ : ∃ b', (U.ι.appIso ⊤).hom.hom b' = b :=
      ⟨(U.ι.appIso ⊤).inv.hom b, by exact congrArg (fun q => q.hom b) (U.ι.appIso ⊤).inv_hom_id⟩
    have key : ∀ z, ⊤ ≤ e z ⁻¹ᵁ U →
        valAt' (pP z) ⊤ ((pullback.fst fU uW).appTop.hom ((U.ι.appIso ⊤).hom.hom b')) =
          valAt' (e z) (U.ι ''ᵁ ⊤) b' := by
      intro z hz
      have e1 : valAt' (pP z) ⊤ ((pullback.fst fU uW).appTop.hom ((U.ι.appIso ⊤).hom.hom b')) =
          valAt' (pP z ≫ pullback.fst fU uW) ⊤ ((U.ι.appIso ⊤).hom.hom b') := by
        exact valAt'_comp (pP z) (pullback.fst fU uW) ⊤ _
      have e2 : pP z ≫ pullback.fst fU uW = eU z := pullback.lift_fst _ _ _
      rw [e1, e2, Scheme.Hom.appIso_hom', Scheme.Hom.appLE, CommRingCat.comp_apply,
        valAt'_res _ _ (vtf_top _), valAt'_comp, heU z hz]
    refine ((hol _ b').2.mono fun z hz => ?_).congr fun z hz => key z hz
    exact top_le_of_mem (hUimg (vtf_mem hz))
  have hsnd : ∀ c : Γ(Sp ℂ, ⊤), DifferentiableOn ℂ
      (fun z => valAt' (pP z) ⊤ ((pullback.snd fU uW).appTop.hom c)) {z | ⊤ ≤ e z ⁻¹ᵁ U} := by
    intro c
    refine (differentiableOn_const (valAt' (𝟙 (Sp ℂ)) ⊤ c)).congr fun z _ => ?_
    have e1 : valAt' (pP z) ⊤ ((pullback.snd fU uW).appTop.hom c) =
        valAt' (pP z ≫ pullback.snd fU uW) ⊤ c := by
      exact valAt'_comp (pP z) (pullback.snd fU uW) ⊤ _
    have e2 : pP z ≫ pullback.snd fU uW = 𝟙 _ := pullback.lift_snd _ _ _
    rw [e1, e2]
  have hv : ∀ (x : Sp ℂ ⟶ pullback fU uW) (a : Γ(pullback fU uW, ⊤)),
      valHom x ⊤ (vtf_top x) a = valAt' x ⊤ a := fun _ _ => rfl
  have hall : ∀ a : Γ(pullback fU uW, ⊤), DifferentiableOn ℂ (fun z => valAt' (pP z) ⊤ a)
      {z | ⊤ ≤ e z ⁻¹ᵁ U} := by
    intro a
    have ha : a ∈ Subring.closure (Set.range (pullback.fst fU uW).appTop.hom ∪
        Set.range (pullback.snd fU uW).appTop.hom) := by
      rw [hgen]; exact Subring.mem_top a
    induction ha using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨b, rfl⟩ | ⟨c, rfl⟩
      · exact hfst b
      · exact hsnd c
    | zero => exact (differentiableOn_const 0).congr fun z _ => (hv _ _).symm.trans (map_zero _)
    | one => exact (differentiableOn_const 1).congr fun z _ => (hv _ _).symm.trans (map_one _)
    | add x y _ _ hx hy =>
      exact (hx.add hy).congr fun z _ => (hv _ _).symm.trans (map_add _ _ _)
    | neg x _ hx => exact hx.neg.congr fun z _ => (hv _ _).symm.trans (map_neg _ _)
    | mul x y _ _ hx hy =>
      exact (hx.mul hy).congr fun z _ => (hv _ _).symm.trans (map_mul _ _ _)
  have hz0' : pP z0 cpt ∈ ι' ⁻¹ᵁ V := by
    show ι' (pP z0 cpt) ∈ V
    rw [← Scheme.Hom.comp_apply, hpP z0 h0U]
    exact vtf_mem hz0
  obtain ⟨h, hle, hmem⟩ := (isAffineOpen_top (pullback fU uW)).exists_basicOpen_le ⟨pP z0 cpt, hz0'⟩ trivial
  haveI := (isAffineOpen_top (pullback fU uW)).isLocalization_basicOpen h
  let ψ : Γ(pullback fU uW, (pullback fU uW).basicOpen h) :=
    ((pullback fU uW).presheaf.map (homOfLE hle).op).hom ((ι'.app V).hom φ)
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers h) ψ
  dsimp only at hs
  obtain ⟨n, hn⟩ := s.2
  have hpow : ∀ z, valAt' (pP z) ⊤ (h ^ n) = valAt' (pP z) ⊤ h ^ n := fun z =>
    (hv _ _).symm.trans ((map_pow _ _ _).trans (congrArg (· ^ n) (hv _ _)))
  have hal : ∀ q : Γ(pullback fU uW, ⊤), algebraMap Γ(pullback fU uW, ⊤)
      Γ(pullback fU uW, (pullback fU uW).basicOpen h) q =
      ((pullback fU uW).presheaf.map (homOfLE ((pullback fU uW).basicOpen_le h)).op).hom q := fun _ => rfl
  let N : Set (Fin g → ℂ) := {z | ⊤ ≤ e z ⁻¹ᵁ U} ∩ (fun z => valAt' (pP z) ⊤ h) ⁻¹' {0}ᶜ
  have hN : IsOpen N := (hall h).continuousOn.isOpen_inter_preimage hSU isOpen_compl_singleton
  have hD : ∀ z ∈ N, ⊤ ≤ pP z ⁻¹ᵁ (pullback fU uW).basicOpen h := fun z hz =>
    top_le_of_mem ((valAt'_ne_zero_iff (pP z) ⊤ (vtf_top _) h cpt).1 hz.2)
  have hVz : ∀ z ∈ N, ⊤ ≤ vtfLift f u e he z ⁻¹ᵁ V := fun z hz => by
    apply top_le_of_mem
    rw [← hpP z hz.1, Scheme.Hom.comp_apply]
    exact hle (vtf_mem (hD z hz))
  have hval : ∀ z ∈ N, valAt' (vtfLift f u e he z) V φ =
      valAt' (pP z) ⊤ a * (valAt' (pP z) ⊤ (h ^ n))⁻¹ := by
    intro z hz
    have hne : valAt' (pP z) ⊤ h ≠ 0 := hz.2
    have e1 : valAt' (vtfLift f u e he z) V φ = valAt' (pP z) _ ψ := by
      rw [← hpP z hz.1, ← valAt'_comp]
      exact (valAt'_res _ hle (hD z hz) _).symm
    have e3 : valAt' (pP z) _ ψ * valAt' (pP z) ⊤ (h ^ n) = valAt' (pP z) ⊤ a := by
      have e2 := congrArg (valHom (pP z) _ (hD z hz)) hs
      rw [map_mul] at e2
      have ra : valHom (pP z) _ (hD z hz) (algebraMap Γ(pullback fU uW, ⊤) _ a) = valAt' (pP z) ⊤ a := by
        exact valAt'_res (pP z) ((pullback fU uW).basicOpen_le h) (hD z hz) a
      have rs : valHom (pP z) _ (hD z hz) (algebraMap Γ(pullback fU uW, ⊤) _ (s : Γ(pullback fU uW, ⊤))) =
          valAt' (pP z) ⊤ (h ^ n) := by
        rw [← hn]
        exact valAt'_res (pP z) ((pullback fU uW).basicOpen_le h) (hD z hz) _
      rw [ra, rs] at e2
      exact e2
    rw [e1, eq_mul_inv_iff_mul_eq₀ (by rw [hpow]; exact pow_ne_zero _ hne), e3]
  refine ⟨N, hN, ⟨h0U, ?_⟩, hVz, ?_⟩
  · exact (valAt'_ne_zero_iff (pP z0) ⊤ (vtf_top _) h cpt).2 hmem
  · refine (((hall a).mono Set.inter_subset_left).mul (((hall (h ^ n)).mono Set.inter_subset_left).inv
      fun z hz => ?_)).congr fun z hz => hval z hz
    rw [hpow]
    exact pow_ne_zero _ hz.2

/- English proof (translation)
Introduce `V φ`. Prove the components needed by the constructor for the conclusion. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `z0 hz0`. Take `⟨N, hN, hzN, hNS, -⟩` from `vtf_local f u e he hol V φ z0 hz0`.

Conclude with `Filter.mem_of_superset (hN.mem_nhds hzN) hNS`. Introduce `z0 hz0`. Take `⟨N, hN, hzN, -, hd⟩` from `vtf_local f u e he hol V φ z0 hz0`. Conclude with `((hd z0 hzN).differentiableAt (hN.mem_nhds hzN)).differentiableWithinAt`.
-/
theorem isHolFam_vtfLift (hol : IsHolFam e) : IsHolFam (vtfLift f u e he) := by
  intro V φ
  constructor
  · rw [isOpen_iff_mem_nhds]
    intro z0 hz0
    obtain ⟨N, hN, hzN, hNS, -⟩ := vtf_local f u e he hol V φ z0 hz0
    exact Filter.mem_of_superset (hN.mem_nhds hzN) hNS
  · intro z0 hz0
    obtain ⟨N, hN, hzN, -, hd⟩ := vtf_local f u e he hol V φ z0 hz0
    exact ((hd z0 hzN).differentiableAt (hN.mem_nhds hzN)).differentiableWithinAt

end Fibre

end ReciprocityTheory.ChartRestriction.G.PullbackSections
