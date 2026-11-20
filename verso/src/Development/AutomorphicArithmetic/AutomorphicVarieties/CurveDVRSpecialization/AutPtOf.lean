import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaHecke
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteEmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoCoefOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsIrrTwistAndRepIsoOfTwistRepIso

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr

/- English proof (translation)
Establish `hi : IsIntegral ℚ_[l] x` using `Algebra.IsIntegral.isIntegral x`. Establish `h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x)` using `rfl`. Rewrite using `[h0, spectralValue_le_one_iff (minpoly.monic hi)]`. Introduce `n`. Rewrite using `[minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]`.

Conclude with `PadicInt.norm_le_one _`.
-/
private theorem ap_norm {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) (h : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  intro n
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

/- English proof (translation)
Take `⟨s, hs⟩` from `Module.Finite.fg_top (R := ℤ_[l]) (M := R)`. Use `haveI := (s.finite_toSet.image φ).to_subtype`. Use `⟨IntermediateField.adjoin ℚ_[l] (φ '' (s : Set R)), IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x, fun x => ⟨?_, ap_norm _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map φ)⟩⟩` and prove the remaining obligations. Establish `hx : x ∈ Submodule.span ℤ_[l] (s : Set R)` using `hs ▸ Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `add_mem ha hb`.

Consider the case `smul a b _ hb`. Rewrite using `[map_smul, ← algebraMap_smul ℚ_[l] a]`. Conclude with `IntermediateField.smul_mem _ hb`.
-/
private theorem ap_field {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] [Algebra ℤ_[l] R] [Module.Finite ℤ_[l] R]
    (φ : R →ₐ[ℤ_[l]] PadicAlgCl l) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧ ∀ x, φ x ∈ E ∧ ‖φ x‖ ≤ 1 := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[l]) (M := R)
  haveI := (s.finite_toSet.image φ).to_subtype
  refine ⟨IntermediateField.adjoin ℚ_[l] (φ '' (s : Set R)),
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x, fun x =>
    ⟨?_, ap_norm _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map φ)⟩⟩
  have hx : x ∈ Submodule.span ℤ_[l] (s : Set R) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul a b _ hb =>
    rw [map_smul, ← algebraMap_smul ℚ_[l] a]
    exact IntermediateField.smul_mem _ hb

/- English proof (translation)
Use `haveI : Module.Finite ℤ_[l] A := Module.Finite.trans c.O A`. Take `⟨E₁, f₁, m₁⟩` from `ap_field c₁.O.val`. Take `⟨E₂, f₂, m₂⟩` from `ap_field (A.val.restrictScalars ℤ_[l])`. Take `⟨c₂, hc⟩` from `UpperTheory.V.X.So.coefOf l (E₁ ⊔ E₂)`. Conclude with `⟨c₂, fun x hx => (hc x).2 ⟨(le_sup_left : E₁ ≤ E₁ ⊔ E₂) (m₁ ⟨x, hx⟩).1, (m₁ ⟨x, hx⟩).2⟩, fun x hx => (hc x).2 ⟨(le_sup_right : E₂ ≤ E₁ ⊔ E₂) (m₂ ⟨x, hx⟩).1, (m₂ ⟨x, hx⟩).2⟩⟩`.
-/
private theorem ap_coef {l : ℕ} [Fact l.Prime] (c c₁ : Coef l) (A : Subalgebra c.O (PadicAlgCl l)) [Module.Finite c.O A] :
    ∃ c₂ : Coef l, c₁.O ≤ c₂.O ∧ ∀ x ∈ A, x ∈ c₂.O := by
  haveI : Module.Finite ℤ_[l] A := Module.Finite.trans c.O A
  obtain ⟨E₁, f₁, m₁⟩ := ap_field c₁.O.val
  obtain ⟨E₂, f₂, m₂⟩ := ap_field (A.val.restrictScalars ℤ_[l])
  obtain ⟨c₂, hc⟩ := UpperTheory.V.X.So.coefOf l (E₁ ⊔ E₂)
  exact ⟨c₂, fun x hx => (hc x).2 ⟨(le_sup_left : E₁ ≤ E₁ ⊔ E₂) (m₁ ⟨x, hx⟩).1, (m₁ ⟨x, hx⟩).2⟩,
    fun x hx => (hc x).2 ⟨(le_sup_right : E₂ ≤ E₁ ⊔ E₂) (m₂ ⟨x, hx⟩).1, (m₂ ⟨x, hx⟩).2⟩⟩

/- English proof (translation)
Establish `hint : φ.IsIntegral`. Use `RingHom.IsIntegral.tower_top (algebraMap ℤ_[l] R) φ ?_` and prove the remaining obligations. Rewrite using `[show φ.comp (algebraMap ℤ_[l] R) = algebraMap ℤ_[l] c.O from RingHom.ext h1]`. Conclude with `fun x => Algebra.IsIntegral.isIntegral x`. Conclude with `hint.isLocalHom hφ`.
-/
private theorem ap_local {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] [Algebra ℤ_[l] R] (c : Coef l)
    (φ : R →+* c.O) (h1 : ∀ a, φ (algebraMap ℤ_[l] R a) = algebraMap ℤ_[l] c.O a) (hφ : Function.Injective φ) :
    IsLocalHom φ := by
  have hint : φ.IsIntegral := by
    refine RingHom.IsIntegral.tower_top (algebraMap ℤ_[l] R) φ ?_
    rw [show φ.comp (algebraMap ℤ_[l] R) = algebraMap ℤ_[l] c.O from RingHom.ext h1]
    exact fun x => Algebra.IsIntegral.isIntegral x
  exact hint.isLocalHom hφ

/- English proof (translation)
Introduce `N` and use `by have hle : maximalIdeal R ^ N ≤ (maximalIdeal S ^ N).comap φ := by rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow] exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun x hx => Ideal.mem_comap.2 (map_nonunit φ x hx)) N exact (h N).comp (Ideal.quotientMap _ φ hle)`.
-/
private theorem ap_adic {Γ R S : Type} [TopologicalSpace Γ] [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (φ : R →+* S) [IsLocalHom φ] {f : Γ → R} (h : Alg.AdicCont (maximalIdeal R) f) :
    Alg.AdicCont (maximalIdeal S) fun g => φ (f g) := fun N => by
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal S ^ N).comap φ := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun x hx => Ideal.mem_comap.2 (map_nonunit φ x hx)) N
  exact (h N).comp (Ideal.quotientMap _ φ hle)

/- English proof (translation)
Use `W.GDet.ext fun C _ _ x => ?_` and prove the remaining obligations. Use `letI : Algebra A C := ((algebraMap B C).comp f).toAlgebra`. Express the relevant statement in the definitionally equal form `(W.GDet.repAlg ρ C (MonoidAlgebra.mapDomainRingHom C p x)).det = (W.GDet.repAlg τ C x).det`. Use `congr 1`. Proceed by induction on `x using MonoidAlgebra.induction_linear with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `single g r`. Use extensionality with `i j`. Simplify using `[W.GDet.repAlg, h]`.

Both sides reduce to the same expression.
-/
private theorem ap_det {n : ℕ} {A B G H : Type} [CommRing A] [CommRing B] [Group G] [Group H]
    (ρ : G →* Matrix (Fin n) (Fin n) A) (f : A →+* B) (p : H →* G) (τ : H →* Matrix (Fin n) (Fin n) B)
    (h : ∀ g, τ g = (ρ (p g)).map f) : ((W.GDet.ofRep ρ).map f).comap p = W.GDet.ofRep τ := by
  refine W.GDet.ext fun C _ _ x => ?_
  letI : Algebra A C := ((algebraMap B C).comp f).toAlgebra
  change (W.GDet.repAlg ρ C (MonoidAlgebra.mapDomainRingHom C p x)).det = (W.GDet.repAlg τ C x).det
  congr 1
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single g r =>
    ext i j
    simp [W.GDet.repAlg, h]
    rfl

/- English proof (translation)
Take `⟨-, art, Y, a, hart, -, hY⟩` from `hka`. Use `⟨fun τ => -a ((ι.toRingHom.comp τ.1).comp (algebraMap L (w.adicCompletion L))), fun m χ hχ κ hκ => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hl : ∃ b, GlobalTheory.LocLanglands.IsLocalArtin h b`. Use `swap`. Conclude with `⟨1, by simp, fun b hb => absurd ⟨b, hb⟩ hl⟩`.

Take `⟨ph, h1⟩` from `Loc.laHecke h art hart ι Y a ka hY hl`. Establish `h2` using `(Loc.laMul h).2.1 _ _ _ m (Loc.laCyc hG h hw)`. Establish `h3` using `(Loc.laMul h).2.2 (χ.comp (Dec (F := L) A).subtype) (χ.comp (Ine (F := L) A).subtype)⁻¹ (Subgroup.isOpen_mono (H₁ := χ.ker.comap (Ine (F := L) A).subtype) (fun x hx => inv_eq_one.2 hx) (hχ.preimage continuous_subtype_val)) fun s => mul_inv_cancel _`. Establish `h4` using `((Loc.laMul h).1 _ _ _ _ _ _ ((Loc.laMul h).1 _ _ _ _ _ _ h2 h3).1 h1).1`. Use `⟨_, h4.1, fun b hb s => ?_⟩` and prove the remaining obligations.

Establish `h5` using `h4.2 b hb s`. Rewrite using `[hκ _ s.2]`. Use `Eq.trans ?_ (h5.trans ?_)` and prove the remaining obligations. Both sides reduce to the same expression. Use `finprod_congr fun τ => ?_` and prove the remaining obligations.

Use `congr 1`. Simplify using `only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem ap_locAlg (hG : GlobalTheory.Published.GlobalArtinReciprocity) {L Ω : Type} [Field L] [NumberField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ka : G L Ω →* (Qbar l)ˣ)
    (hka : Sd.IsAlgChar ι ka) {A : ValuationSubring Ω} {w : W.Plc L} (h : IsPlaceOver A w)
    (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) :
    ∃ wt : W.Emb l w → ℤ, ∀ (m : ℤ) (χ : G L Ω →* (Qbar l)ˣ), IsOpen (χ.ker : Set (G L Ω)) →
      ∀ κ : Dec (F := L) A →* (Qbar l)ˣ,
        (∀ g : Dec (F := L) A, (g : G L Ω) ∈ Ine (F := L) A → κ g = cycBar L Ω l g ^ m * χ g * ka g) →
        W.IsLocAlg h κ fun τ => wt τ - m := by
  obtain ⟨-, art, Y, a, hart, -, hY⟩ := hka
  refine ⟨fun τ => -a ((ι.toRingHom.comp τ.1).comp (algebraMap L (w.adicCompletion L))), fun m χ hχ κ hκ => ?_⟩
  by_cases hl : ∃ b, GlobalTheory.LocLanglands.IsLocalArtin h b
  swap
  · exact ⟨1, by simp, fun b hb => absurd ⟨b, hb⟩ hl⟩
  obtain ⟨ph, h1⟩ := Loc.laHecke h art hart ι Y a ka hY hl
  have h2 := (Loc.laMul h).2.1 _ _ _ m (Loc.laCyc hG h hw)
  have h3 := (Loc.laMul h).2.2 (χ.comp (Dec (F := L) A).subtype) (χ.comp (Ine (F := L) A).subtype)⁻¹
    (Subgroup.isOpen_mono (H₁ := χ.ker.comap (Ine (F := L) A).subtype) (fun x hx => inv_eq_one.2 hx)
      (hχ.preimage continuous_subtype_val)) fun s => mul_inv_cancel _
  have h4 := ((Loc.laMul h).1 _ _ _ _ _ _ ((Loc.laMul h).1 _ _ _ _ _ _ h2 h3).1 h1).1
  refine ⟨_, h4.1, fun b hb s => ?_⟩
  have h5 := h4.2 b hb s
  rw [hκ _ s.2]
  refine Eq.trans ?_ (h5.trans ?_)
  · rfl
  · refine finprod_congr fun τ => ?_
    congr 1
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    ring

private def apExt {l : ℕ} [Fact l.Prime] {k k' : Type} [Field k] [Field k'] {Φ : Fr.Frame l k} {n : ℕ} {K : Type} [CommRing K]
    (f : k →+* k') (ρ : Fr.NRep Φ n K) : Fr.NRep (Φ.ext f) n K := ⟨ρ.r, ρ.ψ, ρ.pol, ρ.diag, ρ.ord⟩

/- English proof (translation)
Establish `h1 : ∀ (x : A) (y : ResidueField O), residue A x = ResidueField.map (algebraMap O A) y → residue A₁ (φ x) = ResidueField.map (algebraMap O₁ A₁) (f y)` using `fun x y e => by`. Take `⟨a, rfl⟩` from `residue_surjective y`. Rewrite using `[h, ← ResidueField.map_residue φ, e, ResidueField.map_residue, ResidueField.map_residue]`. Establish `h2 : ∀ (u : (ResidueField O)ˣ) (m : ℤ), f (u ^ m).val = (Units.map f.toMonoidHom u ^ m).val` using `fun u m => by`. Rewrite using `[← map_zpow]`.

Both sides reduce to the same expression. Use `⟨⟨fun i j => ap_adic φ (H.cont.1 i j), fun v i => ap_adic φ (H.cont.2 v i)⟩, ⟨fun g i => ?_, fun v i g => ?_⟩, fun g i j hij => ?_⟩` and prove the remaining obligations. Conclude with `(h1 _ _ (H.bar.1 g i)).trans (congrArg _ (h2 _ _))`. Conclude with `(h1 _ _ (H.bar.2 v i g)).trans (congrArg _ (h2 _ _))`. Use `h1 (ρ.r g i j) 0 ((H.diag g i j hij).trans (map_zero _).symm)` as an intermediate fact.

Rewrite `this` using `[map_zero, map_zero]`. Then use the resulting hypothesis.
-/
private theorem ap_lift {l : ℕ} [Fact l.Prime] {O O₁ A A₁ : Type} [CommRing O] [IsLocalRing O] [CommRing O₁] [IsLocalRing O₁]
    [CommRing A] [IsLocalRing A] [CommRing A₁] [IsLocalRing A₁] [Algebra O A] [Algebra O₁ A₁]
    [IsLocalHom (algebraMap O A)] [IsLocalHom (algebraMap O₁ A₁)] (f : ResidueField O →+* ResidueField O₁)
    (φ : A →+* A₁) [IsLocalHom φ]
    (h : ∀ a, ResidueField.map (algebraMap O₁ A₁) (f (residue O a)) = residue A₁ (φ (algebraMap O A a)))
    {Φ : Fr.Frame l (ResidueField O)} {n : ℕ} (ρ : Fr.NRep Φ n A) (H : IsLiftA O ρ) :
    IsLiftA O₁ (apExt f (ρ.map φ)) := by
  have h1 : ∀ (x : A) (y : ResidueField O), residue A x = ResidueField.map (algebraMap O A) y →
      residue A₁ (φ x) = ResidueField.map (algebraMap O₁ A₁) (f y) := fun x y e => by
    obtain ⟨a, rfl⟩ := residue_surjective y
    rw [h, ← ResidueField.map_residue φ, e, ResidueField.map_residue, ResidueField.map_residue]
  have h2 : ∀ (u : (ResidueField O)ˣ) (m : ℤ), f (u ^ m).val = (Units.map f.toMonoidHom u ^ m).val := fun u m => by
    rw [← map_zpow]; rfl
  refine ⟨⟨fun i j => ap_adic φ (H.cont.1 i j), fun v i => ap_adic φ (H.cont.2 v i)⟩, ⟨fun g i => ?_, fun v i g => ?_⟩,
    fun g i j hij => ?_⟩
  · exact (h1 _ _ (H.bar.1 g i)).trans (congrArg _ (h2 _ _))
  · exact (h1 _ _ (H.bar.2 v i g)).trans (congrArg _ (h2 _ _))
  · have := h1 (ρ.r g i j) 0 ((H.diag g i j hij).trans (map_zero _).symm)
    rwa [map_zero, map_zero] at this

/- English proof (translation)
Set `u : c.Oˣ →* (Qbar l)ˣ` to `Units.map c.O.val.toRingHom.toMonoidHom`. Use `⟨((u.comp (Chr.dirG ℚ Ω ψ)).comp (galEmb ℚ L Ω)) ^ m, ?_, fun g => ?_⟩` and prove the remaining obligations. Use `Subgroup.isOpen_mono (H₁ := (Chr.cls ℚ Ω N).ker.comap (galEmb ℚ L Ω)) (fun g hg => ?_) ((Chr.clsFacts ℚ Ω N).1.preimage (galEmbTop ℚ L Ω).1.continuous)` and prove the remaining obligations. Establish `h1 : Chr.cls ℚ Ω N (galEmb ℚ L Ω g) = 1` using `hg`. Rewrite using `[MonoidHom.mem_ker, MonoidHom.zpow_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, Chr.dirG, MonoidHom.comp_apply, h1, map_one, map_one, one_zpow]`.

Establish `h1 : u (chiO ℚ Ω l c.O (galEmb ℚ L Ω g)) = cycBar L Ω l g` using `Units.ext rfl`. Express the relevant statement in the definitionally equal form `(u _).val = _`. Rewrite using `[map_zpow, Chr.Psi, MonoidHom.mul_apply, map_mul, MonoidHom.zpow_apply, map_zpow, h1, mul_zpow, ← zpow_mul]`. Both sides reduce to the same expression.
-/
private theorem ap_psi {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l)
    {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (L : Type) [Field L] [NumberField L] [Algebra L Ω]
    [IsAlgClosure L Ω] (m : ℤ) :
    ∃ χ : G L Ω →* (Qbar l)ˣ, IsOpen (χ.ker : Set (G L Ω)) ∧ ∀ g : G L Ω,
      (Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ L Ω g) ^ m).val.1 = (cycBar L Ω l g ^ ((e : ℤ) * m) * χ g).val := by
  let u : c.Oˣ →* (Qbar l)ˣ := Units.map c.O.val.toRingHom.toMonoidHom
  refine ⟨((u.comp (Chr.dirG ℚ Ω ψ)).comp (galEmb ℚ L Ω)) ^ m, ?_, fun g => ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := (Chr.cls ℚ Ω N).ker.comap (galEmb ℚ L Ω)) (fun g hg => ?_)
      ((Chr.clsFacts ℚ Ω N).1.preimage (galEmbTop ℚ L Ω).1.continuous)
    have h1 : Chr.cls ℚ Ω N (galEmb ℚ L Ω g) = 1 := hg
    rw [MonoidHom.mem_ker, MonoidHom.zpow_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, Chr.dirG, MonoidHom.comp_apply,
      h1, map_one, map_one, one_zpow]
  · have h1 : u (chiO ℚ Ω l c.O (galEmb ℚ L Ω g)) = cycBar L Ω l g := Units.ext rfl
    change (u _).val = _
    rw [map_zpow, Chr.Psi, MonoidHom.mul_apply, map_mul, MonoidHom.zpow_apply, map_zpow, h1, mul_zpow, ← zpow_mul]
    rfl
