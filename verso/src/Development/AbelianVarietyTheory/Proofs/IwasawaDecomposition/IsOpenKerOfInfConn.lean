import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenConnectedComponentOfOneInf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormEmbeddingIntegerLeOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousExtensionAdicCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceEqOfContEmbCompEq

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.HeckeGal

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Set `J : HeightOneSpectrum (𝓞 E) → Type` to `fun v => {j : v.adicCompletion E →+* Qbar l // Continuous j}`. Set `res : (Σ v, J v) → (E →+* ℂ)` to `fun p => (ι.toRingHom.comp p.2.1).comp (algebraMap E (p.1.adicCompletion E))`. Establish `hinj : Function.Injective res`. Introduce and unpack `⟨v, j⟩ ⟨v', j'⟩ h`. Establish `h1 : j.1.comp (algebraMap E (v.adicCompletion E)) = j'.1.comp (algebraMap E (v'.adicCompletion E))`.

Use extensionality with `a`. Conclude with `ι.injective (DFunLike.congr_fun h a)`. Take `rfl` from `GlobalTheory.HeckeGal.place_eq_of_contEmb_comp_eq E l v v' j.1 j'.1 j.2 j'.2 h1`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `DFunLike.coe_injective` to reduce the goal to its premises. Use `(HeightOneSpectrum.denseRange_algebraMap E v).equalizer j.2 j'.2 ?_` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Conclude with `DFunLike.congr_fun h1 a`. Establish `hsurj : Function.Surjective res`.

Introduce `φ`. Take `⟨v, hv⟩` from `GlobalTheory.LadicPlace.exists_place_of_embedding E l (ι.symm.toRingHom.comp φ)`. Take `⟨j, hj, e⟩` from `GlobalTheory.exists_continuous_extension_adicCompletion E l _ v hv`. Use `⟨⟨v, j, hj⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `a`.

Use `DFunLike.congr_fun e a` as an intermediate fact. Use `show ι (j (algebraMap E _ a)) = φ a`. Rewrite using `[show j (algebraMap E _ a) = ι.symm (φ a) from this, ι.apply_symm_apply]`. Use `haveI : Fintype (Σ v, J v) := Fintype.ofInjective res hinj`. Use `haveI : ∀ v, Fintype (J v) := fun v => @Fintype.ofFinite _ (finite_contEmb (l := l) v)`.

Set `F : (Σ v, J v) → Qbar l` to `fun p => ι.symm (res p (k : E)) ^ n (res p)`. Establish `h1 : ∏ φ : E →+* ℂ, ι.symm (φ (k : E)) ^ n φ = ∏ p, F p` using `(Fintype.prod_bijective res ⟨hinj, hsurj⟩ F _ fun _ => rfl).symm`. Establish `h2 : ∀ v, locPow ι n v (((diagUnits E k : Ideles E) : AdeleRing (𝓞 E) E).2 v) = ∏ j : J v, F ⟨v, j⟩`. Introduce `v`. Unfold `locPow`.

Rewrite using `[finprod_eq_prod_of_fintype]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `(ι.symm_apply_apply _).symm`. Rewrite using `[h1, ← Finset.prod_fiberwise_of_maps_to (t := Finset.univ.image Sigma.fst) (g := Sigma.fst) (fun p hp => Finset.mem_image_of_mem _ hp)]`.

Unfold `lPow`. Simplify using `only [h2]`. Rewrite using `[finprod_eq_prod_of_mulSupport_subset (s := Finset.univ.image (Sigma.fst : (Σ v, J v) → _))]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Use `Finset.prod_bij (fun j _ => (⟨v, j⟩ : Σ v, J v)) (fun j _ => by simp) (fun a _ b _ h => ?_) ?_ (fun _ _ => rfl)` and prove the remaining obligations.

Conclude with `eq_of_heq (Sigma.mk.inj h).2`. Introduce and unpack `⟨w, j⟩ hp`. Take `rfl : w = v` from `(Finset.mem_filter.mp hp).2`. Conclude with `⟨j, Finset.mem_univ _, rfl⟩`. Introduce `v hv`.

Take `⟨j, -, -⟩` from `Finset.exists_ne_one_of_prod_ne_one hv`. Conclude with `Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨v, j⟩, Finset.mem_univ _, rfl⟩)`.
-/
theorem lPow_diagUnits (ι : Qbar l ≃+* ℂ) (n : (E →+* ℂ) → ℤ) (k : Eˣ) :
    lPow ι n (diagUnits E k) = ∏ φ : E →+* ℂ, ι.symm (φ (k : E)) ^ n φ := by
  classical
  let J : HeightOneSpectrum (𝓞 E) → Type := fun v => {j : v.adicCompletion E →+* Qbar l // Continuous j}
  let res : (Σ v, J v) → (E →+* ℂ) := fun p =>
    (ι.toRingHom.comp p.2.1).comp (algebraMap E (p.1.adicCompletion E))
  have hinj : Function.Injective res := by
    rintro ⟨v, j⟩ ⟨v', j'⟩ h
    have h1 : j.1.comp (algebraMap E (v.adicCompletion E)) = j'.1.comp (algebraMap E (v'.adicCompletion E)) := by
      ext a
      exact ι.injective (DFunLike.congr_fun h a)
    obtain rfl := GlobalTheory.HeckeGal.place_eq_of_contEmb_comp_eq E l v v' j.1 j'.1 j.2 j'.2 h1
    congr 1
    apply Subtype.ext
    apply DFunLike.coe_injective
    refine (HeightOneSpectrum.denseRange_algebraMap E v).equalizer j.2 j'.2 ?_
    funext a
    exact DFunLike.congr_fun h1 a
  have hsurj : Function.Surjective res := by
    intro φ
    obtain ⟨v, hv⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding E l (ι.symm.toRingHom.comp φ)
    obtain ⟨j, hj, e⟩ := GlobalTheory.exists_continuous_extension_adicCompletion E l _ v hv
    refine ⟨⟨v, j, hj⟩, ?_⟩
    ext a
    have := DFunLike.congr_fun e a
    show ι (j (algebraMap E _ a)) = φ a
    rw [show j (algebraMap E _ a) = ι.symm (φ a) from this, ι.apply_symm_apply]
  haveI : Fintype (Σ v, J v) := Fintype.ofInjective res hinj
  haveI : ∀ v, Fintype (J v) := fun v => @Fintype.ofFinite _ (finite_contEmb (l := l) v)
  let F : (Σ v, J v) → Qbar l := fun p => ι.symm (res p (k : E)) ^ n (res p)
  have h1 : ∏ φ : E →+* ℂ, ι.symm (φ (k : E)) ^ n φ = ∏ p, F p :=
    (Fintype.prod_bijective res ⟨hinj, hsurj⟩ F _ fun _ => rfl).symm
  have h2 : ∀ v, locPow ι n v (((diagUnits E k : Ideles E) : AdeleRing (𝓞 E) E).2 v) = ∏ j : J v, F ⟨v, j⟩ := by
    intro v
    unfold locPow
    rw [finprod_eq_prod_of_fintype]
    refine Finset.prod_congr rfl fun j _ => ?_
    congr 1
    exact (ι.symm_apply_apply _).symm
  rw [h1, ← Finset.prod_fiberwise_of_maps_to (t := Finset.univ.image Sigma.fst) (g := Sigma.fst)
    (fun p hp => Finset.mem_image_of_mem _ hp)]
  unfold lPow
  simp only [h2]
  rw [finprod_eq_prod_of_mulSupport_subset (s := Finset.univ.image (Sigma.fst : (Σ v, J v) → _))]
  · refine Finset.prod_congr rfl fun v _ => ?_
    refine Finset.prod_bij (fun j _ => (⟨v, j⟩ : Σ v, J v)) (fun j _ => by simp) (fun a _ b _ h => ?_) ?_
      (fun _ _ => rfl)
    · exact eq_of_heq (Sigma.mk.inj h).2
    · rintro ⟨w, j⟩ hp
      obtain rfl : w = v := (Finset.mem_filter.mp hp).2
      exact ⟨j, Finset.mem_univ _, rfl⟩
  · intro v hv
    obtain ⟨j, -, -⟩ := Finset.exists_ne_one_of_prod_ne_one hv
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨v, j⟩, Finset.mem_univ _, rfl⟩)

abbrev inlInf (E : Type) [Field E] [NumberField E] : (InfiniteAdeleRing E)ˣ →* Ideles E :=
  Units.map (MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))

abbrev inrFin (E : Type) [Field E] [NumberField E] : (FiniteAdeleRing (𝓞 E) E)ˣ →* Ideles E :=
  Units.map (MonoidHom.inr (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))

/- English proof (translation)
The claim follows from `Continuous.units_map _ (continuous_id.prodMk continuous_const)`.
-/
theorem continuous_inlInf : Continuous (inlInf E) :=
  Continuous.units_map _ (continuous_id.prodMk continuous_const)

/- English proof (translation)
The claim follows from `Continuous.units_map _ (continuous_const.prodMk continuous_id)`.
-/
theorem continuous_inrFin : Continuous (inrFin E) :=
  Continuous.units_map _ (continuous_const.prodMk continuous_id)

/- English proof (translation)
Establish `h : ∀ y : (InfiniteAdeleRing E)ˣ, inlInf E y = ∏ w : InfinitePlace E, infIdele E w (Units.map (Pi.evalMonoidHom (fun w : InfinitePlace E => w.Completion) w) y)`. Introduce `y`. Establish `: y = ∏ w : InfinitePlace E, (Units.map (MonoidHom.mulSingle (fun w : InfinitePlace E => w.Completion) w) (Units.map (Pi.evalMonoidHom (fun w : InfinitePlace E => w.Completion) w) y) : (InfiniteAdeleRing E)ˣ)`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.coe_prod]`.

Conclude with `(Finset.univ_prod_mulSingle (y : InfiniteAdeleRing E)).symm`. Conclude with `(congrArg (inlInf E) this).trans (map_prod (inlInf E) _ _)`. Rewrite using `[h, infDiag, MonoidHom.finsetProd_apply]`. Both sides reduce to the same expression.
-/
theorem infDiag_eq (k : Eˣ) :
    infDiag k = inlInf E (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k) := by
  classical
  have h : ∀ y : (InfiniteAdeleRing E)ˣ, inlInf E y = ∏ w : InfinitePlace E,
      infIdele E w (Units.map (Pi.evalMonoidHom (fun w : InfinitePlace E => w.Completion) w) y) := by
    intro y
    have : y = ∏ w : InfinitePlace E, (Units.map (MonoidHom.mulSingle (fun w : InfinitePlace E => w.Completion) w)
        (Units.map (Pi.evalMonoidHom (fun w : InfinitePlace E => w.Completion) w) y) : (InfiniteAdeleRing E)ˣ) := by
      apply Units.ext
      rw [Units.coe_prod]
      exact (Finset.univ_prod_mulSingle (y : InfiniteAdeleRing E)).symm
    exact (congrArg (inlInf E) this).trans (map_prod (inlInf E) _ _)
  rw [h, infDiag, MonoidHom.finsetProd_apply]
  rfl

/- English proof (translation)
Take `⟨y, hy, rfl⟩` from `hx`. Take `⟨f, hf, hfe⟩` from `exists_infPow_hom E n`. Establish `hcl : IsClosed {y : (InfiniteAdeleRing E)ˣ | χ.1 (inlInf E y) = f (inlInf E y)}` using `isClosed_eq (χ.2.1.comp continuous_inlInf) (hf.comp continuous_inlInf)`. Establish `hmem` using `(denseRange_units_inf E).open_subset_closure_inter (isOpen_connectedComponentOfOne_inf E) hy`. Establish `: y ∈ {y : (InfiniteAdeleRing E)ˣ | χ.1 (inlInf E y) = f (inlInf E y)}`.

Use `closure_minimal ?_ hcl hmem` and prove the remaining obligations. Introduce and unpack `_ ⟨hk, k, rfl⟩`. Apply `Units.ext` to reduce the goal to its premises. Use `show ((χ.1 (inlInf E _) : ℂˣ) : ℂ) = ((f (inlInf E _) : ℂˣ) : ℂ)`. Rewrite using `[hfe, ← infDiag_eq]`.

Establish `h1` using `h k (pos_of_mem_connectedComponentOfOne E k hk)`. Rewrite `h1` using `[← infPow_diagUnits E n k]`. Use `Eq.trans h1 ?_` and prove the remaining obligations. Rewrite using `[infDiag_eq]`. Both sides reduce to the same expression.

Rewrite using `[← hfe]`. Conclude with `congrArg Units.val this`.
-/
theorem IsAlgPos.eq_infPow {χ : HChar E} {n : (E →+* ℂ) → ℤ} (h : IsAlgPos χ n) {x : Ideles E}
    (hx : x ∈ infConn E) : ((χ.1 x : ℂˣ) : ℂ) = infPow n x := by
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨f, hf, hfe⟩ := exists_infPow_hom E n
  have hcl : IsClosed {y : (InfiniteAdeleRing E)ˣ | χ.1 (inlInf E y) = f (inlInf E y)} :=
    isClosed_eq (χ.2.1.comp continuous_inlInf) (hf.comp continuous_inlInf)
  have hmem := (denseRange_units_inf E).open_subset_closure_inter (isOpen_connectedComponentOfOne_inf E) hy
  have : y ∈ {y : (InfiniteAdeleRing E)ˣ | χ.1 (inlInf E y) = f (inlInf E y)} := by
    refine closure_minimal ?_ hcl hmem
    rintro _ ⟨hk, k, rfl⟩
    apply Units.ext
    show ((χ.1 (inlInf E _) : ℂˣ) : ℂ) = ((f (inlInf E _) : ℂˣ) : ℂ)
    rw [hfe, ← infDiag_eq]
    have h1 := h k (pos_of_mem_connectedComponentOfOne E k hk)
    rw [← infPow_diagUnits E n k] at h1
    refine Eq.trans h1 ?_
    rw [infDiag_eq]
    rfl
  rw [← hfe]
  exact congrArg Units.val this

/- English proof (translation)
Set `p : Ideles E →* (InfiniteAdeleRing E)ˣ` to `Units.map (MonoidHom.fst (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))`. Set `q : Ideles E →* (FiniteAdeleRing (𝓞 E) E)ˣ` to `Units.map (MonoidHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))`. Establish `hp : Continuous p` using `Continuous.units_map _ continuous_fst`. Establish `hq : Continuous q` using `Continuous.units_map _ continuous_snd`. Establish `ho` using `((isOpen_connectedComponentOfOne_inf E).preimage hp).inter ((show IsOpen ((θ.comp (inrFin E)).ker : Set (FiniteAdeleRing (𝓞 E) E)ˣ) from GlobalTheory.CuspRep.isOpen_ker_finIdele E (θ.comp (inrFin E)) (hθ.comp continuous_inrFin)).preimage hq)`.

Use `θ.ker.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (ho.mem_nhds ⟨?_, ?_⟩) ?_)` and prove the remaining obligations. Rewrite using `[Set.mem_preimage, map_one]`. Conclude with `Subgroup.one_mem _`. Rewrite using `[Set.mem_preimage, map_one]`. Conclude with `Subgroup.one_mem _`.

Introduce and unpack `x ⟨h1, h2⟩`. Establish `e : x = inlInf E (p x) * inrFin E (q x)` using `Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)`. Establish `h3 : θ (inrFin E (q x)) = 1` using `h2`. Use `show θ x = 1`. Rewrite using `[e, map_mul, h3, mul_one]`.

Conclude with `h _ ⟨_, h1, rfl⟩`.
-/
theorem isOpen_ker_of_infConn (θ : Ideles E →* ℂˣ) (hθ : Continuous θ) (h : ∀ x ∈ infConn E, θ x = 1) :
    IsOpen (θ.ker : Set (Ideles E)) := by
  let p : Ideles E →* (InfiniteAdeleRing E)ˣ :=
    Units.map (MonoidHom.fst (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))
  let q : Ideles E →* (FiniteAdeleRing (𝓞 E) E)ˣ :=
    Units.map (MonoidHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))
  have hp : Continuous p := Continuous.units_map _ continuous_fst
  have hq : Continuous q := Continuous.units_map _ continuous_snd
  have ho := ((isOpen_connectedComponentOfOne_inf E).preimage hp).inter
    ((show IsOpen ((θ.comp (inrFin E)).ker : Set (FiniteAdeleRing (𝓞 E) E)ˣ) from
      GlobalTheory.CuspRep.isOpen_ker_finIdele E (θ.comp (inrFin E)) (hθ.comp continuous_inrFin)).preimage hq)
  refine θ.ker.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (ho.mem_nhds ⟨?_, ?_⟩) ?_)
  · rw [Set.mem_preimage, map_one]
    exact Subgroup.one_mem _
  · rw [Set.mem_preimage, map_one]
    exact Subgroup.one_mem _
  · rintro x ⟨h1, h2⟩
    have e : x = inlInf E (p x) * inrFin E (q x) :=
      Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
    have h3 : θ (inrFin E (q x)) = 1 := h2
    show θ x = 1
    rw [e, map_mul, h3, mul_one]
    exact h _ ⟨_, h1, rfl⟩

/- English proof (translation)
Take `⟨y, -, rfl⟩` from `hx`. Conclude with `finprod_eq_one_of_forall_eq_one fun v => locPow_one ι n v`.
-/
theorem lPow_of_mem_infConn (ι : Qbar l ≃+* ℂ) (n : (E →+* ℂ) → ℤ) {x : Ideles E} (hx : x ∈ infConn E) :
    lPow ι n x = 1 := by
  obtain ⟨y, -, rfl⟩ := hx
  exact finprod_eq_one_of_forall_eq_one fun v => locPow_one ι n v

/- English proof (translation)
Take `⟨f, hf, hfe⟩` from `exists_infPow_hom E n`. Take `⟨g, hg, hge⟩` from `exists_lPow_hom E l ι n`. Set `θ : Ideles E →* ℂˣ` to `χ.1 * f⁻¹`. Establish `hθ : Continuous θ` using `χ.2.1.mul hf.inv`. Establish `hθe : ∀ x, ((θ x : ℂˣ) : ℂ) = ((χ.1 x : ℂˣ) : ℂ) * (infPow n x)⁻¹` using `fun x => by`.

Rewrite using `[← hfe, ← Units.val_inv_eq_inv_val]`. Both sides reduce to the same expression. Establish `hθ1 : ∀ x ∈ infConn E, θ x = 1` using `fun x hx => by`. Establish `: χ.1 x = f x` using `Units.ext (by rw [hfe, h.eq_infPow hx])`. Use `show χ.1 x * (f x)⁻¹ = 1`.

Rewrite using `[this, mul_inv_cancel]`. Set `θ' : Ideles E →* (Qbar l)ˣ` to `(Units.map ι.symm.toRingHom.toMonoidHom).comp θ`. Establish `hθ' : Continuous θ'` using `continuous_of_isOpen_ker' θ' (Subgroup.isOpen_mono (fun x hx => by`. Rewrite `hx`, the goal using `[MonoidHom.mem_ker]`. Rewrite using `[MonoidHom.comp_apply, hx, map_one]) (isOpen_ker_of_infConn θ hθ hθ1))`.

Set `ψ : Ideles E →* (Qbar l)ˣ` to `θ' * g`. Establish `hψ : Continuous ψ` using `hθ'.mul hg`. Establish `hψe : ∀ x, ((ψ x : (Qbar l)ˣ) : Qbar l) = ι.symm (((χ.1 x : ℂˣ) : ℂ) * (infPow n x)⁻¹) * lPow ι n x` using `fun x => by`. Rewrite using `[← hθe, ← hge]`. Both sides reduce to the same expression.

Establish `hker : art.ker ≤ ψ.ker`. Rewrite using `[ha.ker]`. Use `Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) (isClosed_singleton.preimage hψ)` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[hψe, χ.2.2 k, infPow_diagUnits, lPow_diagUnits, Units.val_one, one_mul, map_inv₀, map_prod]`. Simplify using `only [map_zpow₀]`. Use `inv_mul_cancel₀ (Finset.prod_ne_zero_iff.mpr fun φ _ => zpow_ne_zero _ ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `x hx`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[hψe, ← hθe, hθ1 x hx, lPow_of_mem_infConn ι n hx]`. Simplify using the standard rewrite rules. Set `ρ : Gab E Ω →* (Qbar l)ˣ` to `art.liftOfSurjective ha.quot.surjective ⟨ψ, hker⟩`. Establish `hρ : ∀ x, ρ (art x) = ψ x` using `fun x => art.liftOfRightInverse_comp_apply _ _ ⟨ψ, hker⟩ x`.

Establish `hρc : Continuous ρ` using `ha.quot.isQuotientMap.continuous_iff.mpr (hψ.congr fun x => (hρ x).symm)`. Use `⟨ρ.comp (toAb E Ω), hρc.comp QuotientGroup.continuous_mk, fun x σ hx => ?_⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.comp_apply, ← hx, hρ, hψe]`.
-/
theorem IsGlobalArtin.exists_isLAdicOf {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) (ι : Qbar l ≃+* ℂ)
    {χ : HChar E} {n : (E →+* ℂ) → ℤ} (h : IsAlgPos χ n) :
    ∃ r : G E Ω →* (Qbar l)ˣ, Continuous r ∧ IsLAdicOf art ι χ n r := by
  obtain ⟨f, hf, hfe⟩ := exists_infPow_hom E n
  obtain ⟨g, hg, hge⟩ := exists_lPow_hom E l ι n
  let θ : Ideles E →* ℂˣ := χ.1 * f⁻¹
  have hθ : Continuous θ := χ.2.1.mul hf.inv
  have hθe : ∀ x, ((θ x : ℂˣ) : ℂ) = ((χ.1 x : ℂˣ) : ℂ) * (infPow n x)⁻¹ := fun x => by
    rw [← hfe, ← Units.val_inv_eq_inv_val]
    rfl
  have hθ1 : ∀ x ∈ infConn E, θ x = 1 := fun x hx => by
    have : χ.1 x = f x := Units.ext (by rw [hfe, h.eq_infPow hx])
    show χ.1 x * (f x)⁻¹ = 1
    rw [this, mul_inv_cancel]
  let θ' : Ideles E →* (Qbar l)ˣ := (Units.map ι.symm.toRingHom.toMonoidHom).comp θ
  have hθ' : Continuous θ' := continuous_of_isOpen_ker' θ' (Subgroup.isOpen_mono (fun x hx => by
      rw [MonoidHom.mem_ker] at hx ⊢
      rw [MonoidHom.comp_apply, hx, map_one]) (isOpen_ker_of_infConn θ hθ hθ1))
  let ψ : Ideles E →* (Qbar l)ˣ := θ' * g
  have hψ : Continuous ψ := hθ'.mul hg
  have hψe : ∀ x, ((ψ x : (Qbar l)ˣ) : Qbar l) =
      ι.symm (((χ.1 x : ℂˣ) : ℂ) * (infPow n x)⁻¹) * lPow ι n x := fun x => by
    rw [← hθe, ← hge]
    rfl
  have hker : art.ker ≤ ψ.ker := by
    rw [ha.ker]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) (isClosed_singleton.preimage hψ)
    · rintro _ ⟨k, rfl⟩
      apply Units.ext
      rw [hψe, χ.2.2 k, infPow_diagUnits, lPow_diagUnits, Units.val_one, one_mul, map_inv₀, map_prod]
      simp only [map_zpow₀]
      refine inv_mul_cancel₀ (Finset.prod_ne_zero_iff.mpr fun φ _ => zpow_ne_zero _ ?_)
      simp
    · intro x hx
      apply Units.ext
      rw [hψe, ← hθe, hθ1 x hx, lPow_of_mem_infConn ι n hx]
      simp
  let ρ : Gab E Ω →* (Qbar l)ˣ := art.liftOfSurjective ha.quot.surjective ⟨ψ, hker⟩
  have hρ : ∀ x, ρ (art x) = ψ x := fun x => art.liftOfRightInverse_comp_apply _ _ ⟨ψ, hker⟩ x
  have hρc : Continuous ρ := ha.quot.isQuotientMap.continuous_iff.mpr (hψ.congr fun x => (hρ x).symm)
  refine ⟨ρ.comp (toAb E Ω), hρc.comp QuotientGroup.continuous_mk, fun x σ hx => ?_⟩
  rw [MonoidHom.comp_apply, ← hx, hρ, hψe]

end GlobalTheory.HeckeGal

namespace GlobalTheory.Published

open GlobalTheory.HeckeGal

/- English proof (translation)
Introduce `H E Ω _ _ _ _ _`. Take `⟨art, ha⟩` from `H E Ω`. Use `⟨art, ha, fun l _ ι χ n h => ?_⟩` and prove the remaining obligations. Take `⟨r, hr, hf⟩` from `ha.exists_isLAdicOf ι h`. Conclude with `⟨r, ⟨hr, hf⟩, fun r' h' => h'.2.unique ha.quot.surjective hf⟩`.
-/
theorem GlobalArtinReciprocity.heckeLAdicCharacter : GlobalArtinReciprocity → HeckeLAdicCharacter := by
  intro H E Ω _ _ _ _ _
  obtain ⟨art, ha⟩ := H E Ω
  refine ⟨art, ha, fun l _ ι χ n h => ?_⟩
  obtain ⟨r, hr, hf⟩ := ha.exists_isLAdicOf ι h
  exact ⟨r, ⟨hr, hf⟩, fun r' h' => h'.2.unique ha.quot.surjective hf⟩

end GlobalTheory.Published

end
