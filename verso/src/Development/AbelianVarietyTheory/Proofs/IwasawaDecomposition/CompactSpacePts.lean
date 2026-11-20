import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsClosedEmbeddingOfAffine

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Topology Filter TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Points

namespace GlobalTheory.ProperPoints

section Ultrapower

variable {I F : Type} [NormedField F] (𝒰 : Ultrafilter I)

def bddRing (F : Type) [NormedField F] : ValuationSubring ((𝒰 : Filter I).Germ F) where
  carrier := {a | ∃ (M : ℝ) (f : I → F), a = (f : (𝒰 : Filter I).Germ F) ∧ ∀ᶠ i in (𝒰 : Filter I), ‖f i‖ ≤ M}
  mul_mem' := by
    rintro _ _ ⟨M, f, rfl, hf⟩ ⟨N, g, rfl, hg⟩
    refine ⟨M * N, f * g, rfl, ?_⟩
    filter_upwards [hf, hg] with i h1 h2
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  one_mem' := ⟨1, 1, rfl, Eventually.of_forall fun i => by simp⟩
  add_mem' := by
    rintro _ _ ⟨M, f, rfl, hf⟩ ⟨N, g, rfl, hg⟩
    refine ⟨M + N, f + g, rfl, ?_⟩
    filter_upwards [hf, hg] with i h1 h2
    exact (norm_add_le _ _).trans (add_le_add h1 h2)
  zero_mem' := ⟨0, 0, rfl, Eventually.of_forall fun i => by simp⟩
  neg_mem' := by
    rintro _ ⟨M, f, rfl, hf⟩
    refine ⟨M, -f, rfl, ?_⟩
    filter_upwards [hf] with i h1
    simpa using h1
  mem_or_inv_mem' := by
    intro a
    induction a using Germ.inductionOn with
    | h f =>
      by_cases h : ∀ᶠ i in (𝒰 : Filter I), ‖f i‖ ≤ 1
      · exact Or.inl ⟨1, f, rfl, h⟩
      · refine Or.inr ⟨1, f⁻¹, rfl, ?_⟩
        filter_upwards [Ultrafilter.eventually_not.2 h] with i hi
        rw [Pi.inv_apply, norm_inv]
        exact inv_le_one_of_one_le₀ (not_le.1 hi).le

def constBdd (F : Type) [NormedField F] : F →+* bddRing 𝒰 F where
  toFun a := ⟨((fun _ => a : I → F) : (𝒰 : Filter I).Germ F), ‖a‖, _, rfl, Eventually.of_forall fun _ => le_rfl⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable [ProperSpace F]

/- English proof (translation)
Take `⟨_, M, f, rfl, hf⟩` from `a`. Take `⟨c, -, hc⟩` from `(isCompact_closedBall (0 : F) M).ultrafilter_le_nhds (𝒰.map f) (by`. Rewrite using `[le_principal_iff]`. Conclude with `hf.mono fun i hi => by simpa using hi)`. Conclude with `⟨c, hc⟩`.
-/
theorem exists_tendsto (a : bddRing 𝒰 F) : ∃ c : F, (a : (𝒰 : Filter I).Germ F).Tendsto (𝓝 c) := by
  obtain ⟨_, M, f, rfl, hf⟩ := a
  obtain ⟨c, -, hc⟩ := (isCompact_closedBall (0 : F) M).ultrafilter_le_nhds (𝒰.map f) (by
    rw [le_principal_iff]
    exact hf.mono fun i hi => by simpa using hi)
  exact ⟨c, hc⟩

/- English proof (translation)
Establish `h` using `(exists_tendsto 𝒰 a).choose_spec`. Generalize the expression as in `(exists_tendsto 𝒰 a).choose = c at h ⊢`. Rewrite `h` using `[hf]`. Then use the resulting hypothesis.
-/
theorem tendsto_choose (a : bddRing 𝒰 F) (f : I → F) (hf : (a : (𝒰 : Filter I).Germ F) = f) :
    Tendsto f 𝒰 (𝓝 (exists_tendsto 𝒰 a).choose) := by
  have h := (exists_tendsto 𝒰 a).choose_spec
  generalize (exists_tendsto 𝒰 a).choose = c at h ⊢
  rwa [hf] at h

/- English proof (translation)
The claim follows from `tendsto_nhds_unique (tendsto_choose 𝒰 a f hf) hc`.
-/
theorem choose_eq (a : bddRing 𝒰 F) (f : I → F) (hf : (a : (𝒰 : Filter I).Germ F) = f) {c : F}
    (hc : Tendsto f 𝒰 (𝓝 c)) : (exists_tendsto 𝒰 a).choose = c :=
  tendsto_nhds_unique (tendsto_choose 𝒰 a f hf) hc

def stdPart (F : Type) [NormedField F] [ProperSpace F] : bddRing 𝒰 F →+* F where
  toFun a := (exists_tendsto 𝒰 a).choose
  map_one' := choose_eq 𝒰 1 (fun _ => 1) rfl tendsto_const_nhds
  map_zero' := choose_eq 𝒰 0 (fun _ => 0) rfl tendsto_const_nhds
  map_mul' := by
    rintro a b
    obtain ⟨_, f, hf, -⟩ := a.2
    obtain ⟨_, g, hg, -⟩ := b.2
    exact choose_eq 𝒰 _ (f * g) (by rw [Germ.coe_mul, ← hf, ← hg]; rfl)
      ((tendsto_choose 𝒰 a f hf).mul (tendsto_choose 𝒰 b g hg))
  map_add' := by
    rintro a b
    obtain ⟨_, f, hf, -⟩ := a.2
    obtain ⟨_, g, hg, -⟩ := b.2
    exact choose_eq 𝒰 _ (f + g) (by rw [Germ.coe_add, ← hf, ← hg]; rfl)
      ((tendsto_choose 𝒰 a f hf).add (tendsto_choose 𝒰 b g hg))

/- English proof (translation)
The claim follows from `tendsto_choose 𝒰 a f hf`.
-/
theorem tendsto_stdPart (a : bddRing 𝒰 F) (f : I → F) (hf : (a : (𝒰 : Filter I).Germ F) = f) :
    Tendsto f 𝒰 (𝓝 (stdPart 𝒰 F a)) := tendsto_choose 𝒰 a f hf

/- English proof (translation)
The claim follows from `choose_eq 𝒰 _ (fun _ => a) rfl tendsto_const_nhds`.
-/
theorem stdPart_constBdd (a : F) : stdPart 𝒰 F (constBdd 𝒰 F a) = a :=
  choose_eq 𝒰 _ (fun _ => a) rfl tendsto_const_nhds

end Ultrapower

/- English proof (translation)
Establish `h1` using `congrArg (valR y (X.basicOpen h)) ha`. Rewrite `h1` using `[valR_mul y _ hy, valR_pow y _ hy, valR_res y hV hy]`. Establish `h2 : ∀ t : Γ(X, U), valR y (X.basicOpen h) (algebraMap Γ(X, U) Γ(X, X.basicOpen h) t) = valR y U t` using `fun t => valR_res y (X.basicOpen_le h) hy t`. Rewrite `h1` using `[h2, h2]`. Then use the resulting hypothesis.
-/
theorem valR_mul_pow {C : Type} [CommRing C] {X : Scheme.{0}} {U V : X.Opens} (h : Γ(X, U))
    (hV : X.basicOpen h ≤ V) (f : Γ(X, V)) (n : ℕ) (a : Γ(X, U))
    (ha : (X.presheaf.map (homOfLE hV).op).hom f * algebraMap Γ(X, U) Γ(X, X.basicOpen h) h ^ n =
      algebraMap Γ(X, U) Γ(X, X.basicOpen h) a)
    (y : Sp C ⟶ X) (hy : ⊤ ≤ y ⁻¹ᵁ X.basicOpen h) : valR y V f * valR y U h ^ n = valR y U a := by
  have h1 := congrArg (valR y (X.basicOpen h)) ha
  rw [valR_mul y _ hy, valR_pow y _ hy, valR_res y hV hy] at h1
  have h2 : ∀ t : Γ(X, U), valR y (X.basicOpen h) (algebraMap Γ(X, U) Γ(X, X.basicOpen h) t) =
      valR y U t := fun t => valR_res y (X.basicOpen_le h) hy t
  rwa [h2, h2] at h1

section Limit

variable {I F : Type} [Field F] (𝒰 : Ultrafilter I) {X : Scheme.{0}} (e : I → (Sp F ⟶ X)) {U : X.Opens}

def germVal (hl : ∀ᶠ i in (𝒰 : Filter I), ⊤ ≤ e i ⁻¹ᵁ U) : Γ(X, U) →+* (𝒰 : Filter I).Germ F where
  toFun f := ((fun i => valR (e i) U f : I → F) : (𝒰 : Filter I).Germ F)
  map_one' := Germ.coe_eq.2 (hl.mono fun _ hi => valR_one _ U hi)
  map_mul' f g := Germ.coe_eq.2 (hl.mono fun _ hi => valR_mul _ U hi f g)
  map_zero' := Germ.coe_eq.2 (hl.mono fun _ hi => valR_zero _ U hi)
  map_add' f g := Germ.coe_eq.2 (hl.mono fun _ hi => valR_add _ U hi f g)

/- English proof (translation)
Take `⟨z, hz⟩ : ∃ z : X, Tendsto (fun i => e i (IsLocalRing.closedPoint F)) 𝒰 (𝓝 z)` from `⟨_, (𝒰.map fun i => e i (IsLocalRing.closedPoint F)).le_nhds_lim⟩`. Take `⟨U, hU, hzU, -⟩` from `exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := z) trivial`. Establish `hl : ∀ᶠ i in (𝒰 : Filter I), ⊤ ≤ e i ⁻¹ᵁ U` using `(hz.eventually (U.isOpen.mem_nhds hzU)).mono fun i hi => (le_preimage_iff _ _).2 hi`. Set `ξ : Sp ((𝒰 : Filter I).Germ F) ⟶ X` to `Spec.map (CommRingCat.ofHom (germVal 𝒰 e hl)) ≫ hU.fromSpec`. Establish `hξ : ⊤ ≤ ξ ⁻¹ᵁ U` using `le_preimage_specMap_fromSpec hU _`.

Establish `hval : ∀ f, valR ξ U f = germVal 𝒰 e hl f` using `fun f => by`. Rewrite using `[valR_eq ξ U hξ, valMap_specMap_fromSpec]`. Both sides reduce to the same expression. Use `⟨ξ, fun V hV => ?_⟩` and prove the remaining obligations. Take `⟨h, hhV, hh⟩` from `hU.exists_basicOpen_le (V := V) ⟨_, (le_preimage_iff ξ V).1 hV⟩ ((le_preimage_iff ξ U).1 hξ)`.

Establish `hξh : ⊤ ≤ ξ ⁻¹ᵁ X.basicOpen h` using `(le_preimage_iff ξ _).2 hh`. Establish `hne : germVal 𝒰 e hl h ≠ 0`. Rewrite using `[← hval]`. Conclude with `((le_preimage_basicOpen_iff ξ hξ h).1 hξh).ne_zero`. Establish `hl' : ∀ᶠ i in (𝒰 : Filter I), ⊤ ≤ e i ⁻¹ᵁ X.basicOpen h`.

Establish `h0 : ¬ ∀ᶠ i in (𝒰 : Filter I), valR (e i) U h = 0` using `fun h0 => hne (Germ.coe_eq.2 h0)`. Use `filter_upwards [hl, Ultrafilter.eventually_not.2 h0] with i h1 h2 using (le_preimage_basicOpen_iff _ h1 h).2 (Ne.isUnit h2)`. Use `⟨hl'.mono fun i hi => le_preimage_mono _ hhV hi, fun f => ?_⟩` and prove the remaining obligations. Use `hU.isLocalization_basicOpen h` as an intermediate fact. Take `⟨n, a, ha⟩` from `IsLocalization.Away.surj h ((X.presheaf.map (homOfLE hhV).op).hom f)`.

Establish `h1` using `valR_mul_pow h hhV f n a ha ξ hξh`. Rewrite `h1` using `[hval, hval]`. Apply `mul_right_cancel₀ (pow_ne_zero n hne)` to reduce the goal to its premises. Rewrite using `[h1, ← map_pow]`. Use `Germ.coe_eq.2 ?_` and prove the remaining obligations.

Use `filter_upwards [hl, hl'] with i h2 h3`. Use `valR_mul_pow h hhV f n a ha (e i) h3` as an intermediate fact. Rewrite `this` using `[← valR_pow _ _ h2]`. Conclude with `this.symm`.
-/
theorem exists_germPoint [CompactSpace X] : ∃ ξ : Sp ((𝒰 : Filter I).Germ F) ⟶ X, ∀ V : X.Opens, ⊤ ≤ ξ ⁻¹ᵁ V →
    (∀ᶠ i in (𝒰 : Filter I), ⊤ ≤ e i ⁻¹ᵁ V) ∧
      ∀ f : Γ(X, V), valR ξ V f = ((fun i => valR (e i) V f : I → F) : (𝒰 : Filter I).Germ F) := by
  obtain ⟨z, hz⟩ : ∃ z : X, Tendsto (fun i => e i (IsLocalRing.closedPoint F)) 𝒰 (𝓝 z) :=
    ⟨_, (𝒰.map fun i => e i (IsLocalRing.closedPoint F)).le_nhds_lim⟩
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := z) trivial
  have hl : ∀ᶠ i in (𝒰 : Filter I), ⊤ ≤ e i ⁻¹ᵁ U :=
    (hz.eventually (U.isOpen.mem_nhds hzU)).mono fun i hi => (le_preimage_iff _ _).2 hi
  let ξ : Sp ((𝒰 : Filter I).Germ F) ⟶ X := Spec.map (CommRingCat.ofHom (germVal 𝒰 e hl)) ≫ hU.fromSpec
  have hξ : ⊤ ≤ ξ ⁻¹ᵁ U := le_preimage_specMap_fromSpec hU _
  have hval : ∀ f, valR ξ U f = germVal 𝒰 e hl f := fun f => by
    rw [valR_eq ξ U hξ, valMap_specMap_fromSpec]
    rfl
  refine ⟨ξ, fun V hV => ?_⟩
  obtain ⟨h, hhV, hh⟩ := hU.exists_basicOpen_le (V := V) ⟨_, (le_preimage_iff ξ V).1 hV⟩
    ((le_preimage_iff ξ U).1 hξ)
  have hξh : ⊤ ≤ ξ ⁻¹ᵁ X.basicOpen h := (le_preimage_iff ξ _).2 hh
  have hne : germVal 𝒰 e hl h ≠ 0 := by
    rw [← hval]
    exact ((le_preimage_basicOpen_iff ξ hξ h).1 hξh).ne_zero
  have hl' : ∀ᶠ i in (𝒰 : Filter I), ⊤ ≤ e i ⁻¹ᵁ X.basicOpen h := by
    have h0 : ¬ ∀ᶠ i in (𝒰 : Filter I), valR (e i) U h = 0 := fun h0 => hne (Germ.coe_eq.2 h0)
    filter_upwards [hl, Ultrafilter.eventually_not.2 h0] with i h1 h2
      using (le_preimage_basicOpen_iff _ h1 h).2 (Ne.isUnit h2)
  refine ⟨hl'.mono fun i hi => le_preimage_mono _ hhV hi, fun f => ?_⟩
  have := hU.isLocalization_basicOpen h
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj h ((X.presheaf.map (homOfLE hhV).op).hom f)
  have h1 := valR_mul_pow h hhV f n a ha ξ hξh
  rw [hval, hval] at h1
  apply mul_right_cancel₀ (pow_ne_zero n hne)
  rw [h1, ← map_pow]
  refine Germ.coe_eq.2 ?_
  filter_upwards [hl, hl'] with i h2 h3
  have := valR_mul_pow h hhV f n a ha (e i) h3
  rw [← valR_pow _ _ h2] at this
  exact this.symm

end Limit

/- English proof (translation)
Establish `: CompactSpace X` using `QuasiCompact.compactSpace_of_compactSpace p`. Use `⟨isCompact_iff_ultrafilter_le_nhds.2 fun 𝒰 _ => ?_⟩` and prove the remaining obligations. Take `⟨ξ, hξ⟩` from `exists_germPoint 𝒰 (fun x : Pts p => x.1)`. Establish `hE : ValuativeCriterion.Existence p` using `(UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed p) : (ValuativeCriterion.Existence ⊓ @QuasiCompact) p).1`. Establish `hw : ξ ≫ p = Spec.map (CommRingCat.ofHom (algebraMap (bddRing 𝒰 F) ((𝒰 : Filter (Pts p)).Germ F))) ≫ spMap (constBdd 𝒰 F)`.

Rewrite using `[← Spec.map_comp, ← Spec.map_preimage (ξ ≫ p)]`. Use `congr 1`. Use extensionality with `a`. Use `(valR_constFn p ξ ⊤ (le_preimage_top _) a).symm.trans ?_` and prove the remaining obligations. Rewrite using `[(hξ ⊤ (le_preimage_top _)).2]`.

Conclude with `Germ.coe_eq.2 (Eventually.of_forall fun x => valR_constFn_of_section p x.1 x.2 ⊤ (le_preimage_top _) a)`. Choose the witnesses or unpack the hypotheses as in `⟨l, hl₁, hl₂⟩ : ∃ l : Sp (bddRing 𝒰 F) ⟶ X, spMap (algebraMap (bddRing 𝒰 F) ((𝒰 : Filter (Pts p)).Germ F)) ≫ l = ξ ∧ l ≫ p = spMap (constBdd 𝒰 F) := by`. Take `⟨⟨l, hl, hl'⟩⟩` from `(hE { R := bddRing 𝒰 F, K := (𝒰 : Filter (Pts p)).Germ F, i₁ := ξ, i₂ := spMap (constBdd 𝒰 F), commSq := ⟨hw⟩ }).exists_lift`. Conclude with `⟨l, hl, hl'⟩`. Establish `hx : (spMap (stdPart 𝒰 F) ≫ l) ≫ p = 𝟙 _`.

Rewrite using `[Category.assoc, hl₂, ← Spec.map_comp, ← Spec.map_id]`. Use `congr 1`. Use extensionality with `a`. Conclude with `stdPart_constBdd 𝒰 a`. Use `⟨⟨_, hx⟩, trivial, ?_⟩` and prove the remaining obligations.

Take `⟨V, hV, hlV, -⟩` from `exists_isAffineOpen_le (C := bddRing 𝒰 F) l (le_preimage_top _)`. Establish `hξV : ⊤ ≤ ξ ⁻¹ᵁ V` using `hl₁ ▸ le_preimage_comp _ l hlV (le_preimage_top _)`. Establish `H : Tendsto (fun x : Pts p => x.1) 𝒰 (𝓝 (spMap (stdPart 𝒰 F) ≫ l))`. Use `tendsto_of_isAffineOpen hV (le_preimage_comp _ l hlV (le_preimage_top _)) (hξ V hξV).1 fun f => ?_` and prove the remaining obligations. Rewrite using `[valR_spMap_comp _ l V hlV]`.

Use `tendsto_stdPart 𝒰 _ _ ?_` and prove the remaining obligations. Rewrite using `[← (hξ V hξV).2, ← hl₁, valR_spMap_comp _ l V hlV]`. Both sides reduce to the same expression. Conclude with `tendsto_id'.1 (tendsto_subtype_rng.2 H)`.
-/
theorem compactSpace_pts {F : Type} [NormedField F] [ProperSpace F] {X : Scheme.{0}} (p : X ⟶ Sp F)
    [UniversallyClosed p] : CompactSpace (Pts p) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  refine ⟨isCompact_iff_ultrafilter_le_nhds.2 fun 𝒰 _ => ?_⟩
  obtain ⟨ξ, hξ⟩ := exists_germPoint 𝒰 (fun x : Pts p => x.1)
  have hE : ValuativeCriterion.Existence p :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed p) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) p).1
  have hw : ξ ≫ p = Spec.map (CommRingCat.ofHom (algebraMap (bddRing 𝒰 F) ((𝒰 : Filter (Pts p)).Germ F))) ≫
      spMap (constBdd 𝒰 F) := by
    rw [← Spec.map_comp, ← Spec.map_preimage (ξ ≫ p)]
    congr 1
    ext a
    refine (valR_constFn p ξ ⊤ (le_preimage_top _) a).symm.trans ?_
    rw [(hξ ⊤ (le_preimage_top _)).2]
    exact Germ.coe_eq.2 (Eventually.of_forall fun x => valR_constFn_of_section p x.1 x.2 ⊤ (le_preimage_top _) a)
  obtain ⟨l, hl₁, hl₂⟩ : ∃ l : Sp (bddRing 𝒰 F) ⟶ X,
      spMap (algebraMap (bddRing 𝒰 F) ((𝒰 : Filter (Pts p)).Germ F)) ≫ l = ξ ∧ l ≫ p = spMap (constBdd 𝒰 F) := by
    obtain ⟨⟨l, hl, hl'⟩⟩ := (hE
      { R := bddRing 𝒰 F, K := (𝒰 : Filter (Pts p)).Germ F, i₁ := ξ, i₂ := spMap (constBdd 𝒰 F),
        commSq := ⟨hw⟩ }).exists_lift
    exact ⟨l, hl, hl'⟩
  have hx : (spMap (stdPart 𝒰 F) ≫ l) ≫ p = 𝟙 _ := by
    rw [Category.assoc, hl₂, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext a
    exact stdPart_constBdd 𝒰 a
  refine ⟨⟨_, hx⟩, trivial, ?_⟩
  obtain ⟨V, hV, hlV, -⟩ := exists_isAffineOpen_le (C := bddRing 𝒰 F) l (le_preimage_top _)
  have hξV : ⊤ ≤ ξ ⁻¹ᵁ V := hl₁ ▸ le_preimage_comp _ l hlV (le_preimage_top _)
  have H : Tendsto (fun x : Pts p => x.1) 𝒰 (𝓝 (spMap (stdPart 𝒰 F) ≫ l)) := by
    refine tendsto_of_isAffineOpen hV (le_preimage_comp _ l hlV (le_preimage_top _)) (hξ V hξV).1 fun f => ?_
    rw [valR_spMap_comp _ l V hlV]
    refine tendsto_stdPart 𝒰 _ _ ?_
    rw [← (hξ V hξV).2, ← hl₁, valR_spMap_comp _ l V hlV]
    rfl
  exact tendsto_id'.1 (tendsto_subtype_rng.2 H)

end GlobalTheory.ProperPoints
