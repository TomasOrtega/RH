import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinEtSubgroup

variable {K : Type} [Field K]

/- English proof (translation)
Establish `: IsLocallyArtinian (Sp K)` using `inferInstanceAs (IsLocallyArtinian (Spec (CommRingCat.of K)))`. Establish `: IsLocallyArtinian X.left` using `IsLocallyArtinian.of_locallyQuasiFinite X.hom`. Use `infer_instance`.
-/
theorem discreteTopology_of_isFinite (X : Over (Sp K)) [IsFinite X.hom] : DiscreteTopology X.left := by
  have : IsLocallyArtinian (Sp K) := inferInstanceAs (IsLocallyArtinian (Spec (CommRingCat.of K)))
  have : IsLocallyArtinian X.left := IsLocallyArtinian.of_locallyQuasiFinite X.hom
  infer_instance

/- English proof (translation)
Set `Ω` to `AlgebraicClosure K`. Set `t : Sp Ω ⟶ Sp K` to `spMap (algebraMap K Ω)`. Take `⟨z, hz, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := X.hom) (g := t) x (IsLocalRing.closedPoint Ω) (Subsingleton.elim (α := PrimeSpectrum K) _ _)`. Take `⟨s, hs, -, hx⟩` from `(FinEt.isSplitOfRank_iff _ _).mp (FinEt.isSplitOfRank_of_isSepClosed (pullback.snd X.hom t) (pullback.snd X.hom t z))`. Take `⟨i, w, hw⟩` from `(hx z).exists`.

Use `⟨Over.homMk (s i ≫ pullback.fst X.hom t) ?_, w, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(s i ≫ pullback.fst X.hom t) ≫ X.hom = t`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]`. Express the relevant statement in the definitionally equal form `(s i ≫ pullback.fst X.hom t) w = x`. Rewrite using `[Scheme.Hom.comp_apply, hw, hz]`.
-/
theorem exists_pt_of_finiteEtale (X : Over (Sp K)) [IsFinite X.hom] [Etale X.hom] (x : X.left) :
    ∃ y : ptOver K (AlgebraicClosure K) ⟶ X, x ∈ Set.range y.left := by
  let Ω := AlgebraicClosure K
  let t : Sp Ω ⟶ Sp K := spMap (algebraMap K Ω)
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := X.hom) (g := t) x
    (IsLocalRing.closedPoint Ω) (Subsingleton.elim (α := PrimeSpectrum K) _ _)
  obtain ⟨s, hs, -, hx⟩ := (FinEt.isSplitOfRank_iff _ _).mp
    (FinEt.isSplitOfRank_of_isSepClosed (pullback.snd X.hom t) (pullback.snd X.hom t z))
  obtain ⟨i, w, hw⟩ := (hx z).exists
  refine ⟨Over.homMk (s i ≫ pullback.fst X.hom t) ?_, w, ?_⟩
  · change (s i ≫ pullback.fst X.hom t) ≫ X.hom = t
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]
  · change (s i ≫ pullback.fst X.hom t) w = x
    rw [Scheme.Hom.comp_apply, hw, hz]

/- English proof (translation)
Set `Ω` to `AlgebraicClosure K`. Take `⟨⟨q, φ⟩, ha⟩` from `(Scheme.SpecToEquivOfField Ω X.left).symm.surjective a.left`. Take `⟨⟨q', ψ⟩, hb⟩` from `(Scheme.SpecToEquivOfField Ω X.left).symm.surjective b.left`. Simplify using `only [Scheme.SpecToEquivOfField_symm_apply] at ha hb`. Establish `hq : q = q'`.

Establish `h1 : (Spec.map φ ≫ X.left.fromSpecResidueField q) p = (Spec.map ψ ≫ X.left.fromSpecResidueField q') p` using `by rw [ha, hb]; exact h`. Simplify `h1` using `only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]`. Substitute `hq` using the available equality. Set `c : CommRingCat.of K ⟶ X.left.residueField q` to `Spec.preimage (X.left.fromSpecResidueField q ≫ X.hom)`. Establish `hc : Spec.map c = X.left.fromSpecResidueField q ≫ X.hom` using `Spec.map_preimage _`.

Establish `key : ∀ (χ : X.left.residueField q ⟶ CommRingCat.of Ω) (u : ptOver K Ω ⟶ X), Spec.map χ ≫ X.left.fromSpecResidueField q = u.left → c ≫ χ = CommRingCat.ofHom (algebraMap K Ω)`. Introduce `χ u hu`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, hc, ← Category.assoc, hu]`. Conclude with `Over.w u`.

Establish `hφ` using `key φ a ha`. Establish `hψ` using `key ψ b hb`. Use `letI : Algebra K (X.left.residueField q) := c.hom.toAlgebra`. Use `letI : Algebra (X.left.residueField q) Ω := ψ.hom.toAlgebra`. Use `haveI : IsScalarTower K (X.left.residueField q) Ω := IsScalarTower.of_algebraMap_eq fun x => (congrArg (fun f => f.hom x) hψ).symm`.

Set `φ' : X.left.residueField q →ₐ[K] Ω` to `{ φ.hom with commutes' := fun x => congrArg (fun f => f.hom x) hφ }`. Set `σ₀ : Ω →ₐ[K] Ω` to `φ'.liftNormal Ω`. Establish `hσ₀ : ∀ x, σ₀ (ψ.hom x) = φ.hom x` using `fun x => φ'.liftNormal_commutes Ω x`. Set `σ : Ω ≃ₐ[K] Ω` to `AlgEquiv.ofBijective σ₀ (Algebra.IsAlgebraic.algHom_bijective σ₀)`. Use `⟨σ, Over.OverMorphism.ext ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `a.left = spMap (σ : Ω →+* Ω) ≫ b.left`. Rewrite using `[← ha, ← hb, ← Category.assoc]`. Use `congr 1`. Rewrite using `[spMap, ← Spec.map_comp]`. Use `congr 1`.

Use extensionality with `x`. Conclude with `(hσ₀ x).symm`.
-/
theorem exists_gal_of_apply_eq (X : Over (Sp K)) (a b : ptOver K (AlgebraicClosure K) ⟶ X)
    (p : Sp (AlgebraicClosure K)) (h : a.left p = b.left p) :
    ∃ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, a = specAut σ ≫ b := by
  let Ω := AlgebraicClosure K
  obtain ⟨⟨q, φ⟩, ha⟩ := (Scheme.SpecToEquivOfField Ω X.left).symm.surjective a.left
  obtain ⟨⟨q', ψ⟩, hb⟩ := (Scheme.SpecToEquivOfField Ω X.left).symm.surjective b.left
  simp only [Scheme.SpecToEquivOfField_symm_apply] at ha hb
  have hq : q = q' := by
    have h1 : (Spec.map φ ≫ X.left.fromSpecResidueField q) p =
        (Spec.map ψ ≫ X.left.fromSpecResidueField q') p := by rw [ha, hb]; exact h
    simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using h1
  subst hq
  let c : CommRingCat.of K ⟶ X.left.residueField q := Spec.preimage (X.left.fromSpecResidueField q ≫ X.hom)
  have hc : Spec.map c = X.left.fromSpecResidueField q ≫ X.hom := Spec.map_preimage _
  have key : ∀ (χ : X.left.residueField q ⟶ CommRingCat.of Ω)
      (u : ptOver K Ω ⟶ X), Spec.map χ ≫ X.left.fromSpecResidueField q = u.left →
      c ≫ χ = CommRingCat.ofHom (algebraMap K Ω) := by
    intro χ u hu
    apply Spec.map_injective
    rw [Spec.map_comp, hc, ← Category.assoc, hu]
    exact Over.w u
  have hφ := key φ a ha
  have hψ := key ψ b hb
  letI : Algebra K (X.left.residueField q) := c.hom.toAlgebra
  letI : Algebra (X.left.residueField q) Ω := ψ.hom.toAlgebra
  haveI : IsScalarTower K (X.left.residueField q) Ω := IsScalarTower.of_algebraMap_eq fun x =>
    (congrArg (fun f => f.hom x) hψ).symm
  let φ' : X.left.residueField q →ₐ[K] Ω :=
    { φ.hom with commutes' := fun x => congrArg (fun f => f.hom x) hφ }
  let σ₀ : Ω →ₐ[K] Ω := φ'.liftNormal Ω
  have hσ₀ : ∀ x, σ₀ (ψ.hom x) = φ.hom x := fun x => φ'.liftNormal_commutes Ω x
  let σ : Ω ≃ₐ[K] Ω := AlgEquiv.ofBijective σ₀ (Algebra.IsAlgebraic.algHom_bijective σ₀)
  refine ⟨σ, Over.OverMorphism.ext ?_⟩
  change a.left = spMap (σ : Ω →+* Ω) ≫ b.left
  rw [← ha, ← hb, ← Category.assoc]
  congr 1
  rw [spMap, ← Spec.map_comp]
  congr 1
  ext x
  exact (hσ₀ x).symm

/- English proof (translation)
Introduce `K _ A G _ hn hgal`. Set `Ω` to `AlgebraicClosure K`. Set `n` to `Nat.card G`. Establish `hu : IsUnit (n : Γ(Sp K, ⊤))`. Simplify using `using (isUnit_iff_ne_zero.2 hn).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom`.

Take `⟨-, hTf, hTe⟩` from `GrpTangent.finiteEtale_mulN_torsion A.X (hG := A.ab) hu`. Set `T` to `torsion A.X n`. Set `ι₀ : T ⟶ A.X` to `torsion.ι A.X n`. Establish `hι₀ : ι₀ ^ n = 1`. Rewrite using `[← GrpTangent.comp_mulN]`.

Use `pullback.condition.trans ?_` and prove the remaining obligations. Rewrite using `[Hom.one_def]`. Use `congr 1`. Conclude with `toUnit_unique _ _`. Use `haveI : IsSplitMono η[A.X] := IsSplitMono.mk' ⟨toUnit _, toUnit_unique _ _⟩`.

Use `haveI : Mono ι₀ := inferInstanceAs (Mono (pullback.fst _ _))`. Establish `hpow : ∀ x ∈ G, x ^ n = 1` using `fun x hx => congrArg Subtype.val (pow_card_eq_one' (G := G) (x := ⟨x, hx⟩))`. Set `lt : ∀ {S : Over (Sp K)} (x : S ⟶ A.X), x ^ n = 1 → (S ⟶ T)` to `fun x hx => pullback.lift x (toUnit _) (by rw [GrpTangent.comp_mulN, hx, Hom.one_def])`. Establish `hlt : ∀ {S : Over (Sp K)} (x : S ⟶ A.X) (hx : x ^ n = 1), lt x hx ≫ ι₀ = x` using `fun x hx => pullback.lift_fst _ _ _`. Set `U : Set T.left` to `{t | ∃ (x : A.Pt) (hx : x ∈ G) (p : Sp Ω), (lt x (hpow x hx)).left p = t}`.

Use `haveI := discreteTopology_of_isFinite T`. Set `V : T.left.Opens` to `⟨U, isOpen_discrete U⟩`. Set `H : Over (Sp K)` to `Over.mk (V.ι ≫ T.hom)`. Set `j : H ⟶ T` to `Over.homMk V.ι rfl`. Take `⟨ν, hνj⟩ : ∃ ν : H ⟶ A.X, ν = j ≫ ι₀` from `⟨_, rfl⟩`.

Use `haveI : IsClosedImmersion V.ι := .of_isPreimmersion _ (by`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `isClosed_discrete _)`. Use `haveI hHf : IsFinite H.hom := by change IsFinite (V.ι ≫ T.hom); infer_instance`. Use `haveI hHe : Etale H.hom := by change Etale (V.ι ≫ T.hom); infer_instance`.

Use `haveI : Mono j := (Over.forget _).mono_of_mono_map (by change Mono V.ι; infer_instance)`. Use `haveI : Mono ν := hνj ▸ mono_comp _ _`. Establish `hν : ν ^ n = 1`. Rewrite using `[hνj, ← MonObj.comp_pow, hι₀, MonObj.comp_one]`. Establish `lift : ∀ {S : Over (Sp K)} (f : S ⟶ A.X) (hf : f ^ n = 1), (∀ s : S.left, ∃ y : ptOver K Ω ⟶ S, s ∈ Set.range y.left) → (∀ y : ptOver K Ω ⟶ S, y ≫ f ∈ G) → ∃ g : S ⟶ H, g ≫ ν = f`.

Introduce `S f hf hS hG`. Establish `hr : Set.range (lt f hf).left ⊆ Set.range V.ι`. Introduce and unpack `_ ⟨s, rfl⟩`. Take `⟨y, p, rfl⟩` from `hS s`. Rewrite using `[Scheme.Opens.range_ι]`.

Establish `e : y ≫ lt f hf = lt (y ≫ f) (hpow _ (hG y))`. Rewrite using `[← cancel_mono ι₀, hlt (y ≫ f) (hpow _ (hG y)), Category.assoc, hlt f hf]`. Use `⟨y ≫ f, hG y, p, ?_⟩` and prove the remaining obligations. Rewrite using `[← e]`. Both sides reduce to the same expression.

Set `g : S ⟶ H` to `Over.homMk (IsOpenImmersion.lift V.ι (lt f hf).left hr) (by`. Express the relevant statement in the definitionally equal form `IsOpenImmersion.lift V.ι (lt f hf).left hr ≫ V.ι ≫ T.hom = S.hom`. Rewrite using `[← Category.assoc, IsOpenImmersion.lift_fac]`. Conclude with `Over.w _)`. Establish `hg : g ≫ j = lt f hf` using `Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)`.

Conclude with `⟨g, by rw [hνj, ← Category.assoc, hg, hlt f hf]⟩`. Establish `hP : ∀ y : ptOver K Ω ⟶ H, y ≫ ν ∈ G`. Introduce `y`. Take `⟨p⟩ : Nonempty (Sp Ω)` from `inferInstance`. Establish `hmem : (y ≫ j).left p ∈ U`.

Establish `h1 : V.ι (y.left p) ∈ Set.range V.ι` using `⟨_, rfl⟩`. Rewrite `h1` using `[Scheme.Opens.range_ι]`. Conclude with `h1`. Take `⟨x, hx, p', hp'⟩` from `hmem`. Rewrite `hp'` using `[Subsingleton.elim p' p]`.

Take `⟨σ, hσ⟩` from `exists_gal_of_apply_eq T (y ≫ j) (lt x (hpow x hx)) p hp'.symm`. Establish `e : y ≫ ν = galPts A.X σ x` using `by show y ≫ ν = specAut σ ≫ x`. Rewrite using `[hνj, ← Category.assoc, hσ, Category.assoc, hlt x (hpow x hx)]`. Rewrite using `[e]`. Conclude with `hgal σ x hx`.

Establish `hone : η[A.X] = 1`. Rewrite using `[Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]`. Take `⟨e, he⟩` from `lift η[A.X] (by rw [hone, one_pow]) (fun s => ⟨toUnit _, by`. Take `⟨p⟩ : Nonempty (Sp Ω)` from `inferInstance`. Conclude with `⟨p, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩)`.

Use the proof step `(fun y => by`. Establish `: y ≫ η[A.X] = 1` using `by rw [Hom.one_def, toUnit_unique (toUnit _) y]`. Rewrite using `[this]`. Conclude with `one_mem G)`. Establish `hmul : (ν ⊗ₘ ν) ≫ μ[A.X] = (fst H H ≫ ν) * (snd H H ≫ ν)`.

Rewrite using `[Hom.mul_def, ← lift_map, lift_fst_snd, Category.id_comp]`. Use `haveI : IsFinite (H ⊗ H).hom := by rw [Over.tensorObj_hom]; infer_instance`. Use `haveI : Etale (H ⊗ H).hom := by rw [Over.tensorObj_hom]; infer_instance`. Establish `hν' : ∀ {S : Over (Sp K)} (g : S ⟶ H), (g ≫ ν) ^ n = 1` using `fun g => by`. Rewrite using `[← MonObj.comp_pow ν n g, hν, MonObj.comp_one]`.

Take `⟨m, hm⟩` from `lift ((ν ⊗ₘ ν) ≫ μ[A.X]) (by rw [hmul, mul_pow, hν' (fst H H), hν' (snd H H), _root_.one_mul]) (exists_pt_of_finiteEtale _) (fun y => by`. Rewrite using `[hmul, MonObj.comp_mul, ← Category.assoc, ← Category.assoc]`. Conclude with `mul_mem (hP (y ≫ fst H H)) (hP (y ≫ snd H H)))`. Take `⟨i, hi⟩` from `lift (ν ≫ ι[A.X]) (by rw [← Hom.inv_def, inv_pow, hν, inv_one]) (exists_pt_of_finiteEtale _) (fun y => by`. Rewrite using `[← Hom.inv_def, GrpObj.comp_inv]`.

Conclude with `inv_mem (hP y))`. Take `⟨gH, hνH⟩` from `ReducedSubgroup.exists_grpObj_of_mono ν e m i he hm hi`. Use `⟨H, gH, ν, hνH, inferInstance, hHf, hHe, fun x => ⟨fun hx => ?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨g, hg⟩` from `lift x (hpow x hx) (fun s => ⟨𝟙 _, s, rfl⟩) (fun y => by`. Take `⟨p⟩ : Nonempty (Sp Ω)` from `inferInstance`.

Take `⟨σ, hσ⟩` from `exists_gal_of_apply_eq (ptOver K Ω) y (𝟙 _) p (Subsingleton.elim (α := PrimeSpectrum Ω) _ _)`. Rewrite using `[hσ, Category.comp_id]`. Conclude with `hgal σ x hx)`. Conclude with `⟨g, hg⟩`. Introduce and unpack `⟨y, rfl⟩`.

Conclude with `hP y`.
-/
theorem exists_finiteEtale_subgroup_of_points : ∀ (K : Type) [Field K] (A : AbVar K) (G : Subgroup A.Pt), Finite G → ((Nat.card G : ℕ) : K) ≠ 0 → (∀ (σ : Gal K) (x : A.Pt), x ∈ G → galPts A.X σ x ∈ G) → ∃ (H : Over (Sp K)) (_ : GrpObj H) (i : H ⟶ A.X), IsMonHom i ∧ Mono i ∧ IsFinite H.hom ∧ Etale H.hom ∧ ∀ x : A.Pt, x ∈ G ↔ ∃ y, y ≫ i = x := by
  intro K _ A G _ hn hgal
  classical
  let Ω := AlgebraicClosure K
  let n := Nat.card G
  have hu : IsUnit (n : Γ(Sp K, ⊤)) := by
    simpa using (isUnit_iff_ne_zero.2 hn).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  obtain ⟨-, hTf, hTe⟩ := GrpTangent.finiteEtale_mulN_torsion A.X (hG := A.ab) hu
  let T := torsion A.X n
  let ι₀ : T ⟶ A.X := torsion.ι A.X n
  have hι₀ : ι₀ ^ n = 1 := by
    rw [← GrpTangent.comp_mulN]
    refine pullback.condition.trans ?_
    rw [Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  haveI : IsSplitMono η[A.X] := IsSplitMono.mk' ⟨toUnit _, toUnit_unique _ _⟩
  haveI : Mono ι₀ := inferInstanceAs (Mono (pullback.fst _ _))
  have hpow : ∀ x ∈ G, x ^ n = 1 := fun x hx =>
    congrArg Subtype.val (pow_card_eq_one' (G := G) (x := ⟨x, hx⟩))
  let lt : ∀ {S : Over (Sp K)} (x : S ⟶ A.X), x ^ n = 1 → (S ⟶ T) := fun x hx =>
    pullback.lift x (toUnit _) (by rw [GrpTangent.comp_mulN, hx, Hom.one_def])
  have hlt : ∀ {S : Over (Sp K)} (x : S ⟶ A.X) (hx : x ^ n = 1), lt x hx ≫ ι₀ = x :=
    fun x hx => pullback.lift_fst _ _ _
  let U : Set T.left := {t | ∃ (x : A.Pt) (hx : x ∈ G) (p : Sp Ω), (lt x (hpow x hx)).left p = t}
  haveI := discreteTopology_of_isFinite T
  let V : T.left.Opens := ⟨U, isOpen_discrete U⟩
  let H : Over (Sp K) := Over.mk (V.ι ≫ T.hom)
  let j : H ⟶ T := Over.homMk V.ι rfl
  obtain ⟨ν, hνj⟩ : ∃ ν : H ⟶ A.X, ν = j ≫ ι₀ := ⟨_, rfl⟩
  haveI : IsClosedImmersion V.ι := .of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]; exact isClosed_discrete _)
  haveI hHf : IsFinite H.hom := by change IsFinite (V.ι ≫ T.hom); infer_instance
  haveI hHe : Etale H.hom := by change Etale (V.ι ≫ T.hom); infer_instance
  haveI : Mono j := (Over.forget _).mono_of_mono_map (by change Mono V.ι; infer_instance)
  haveI : Mono ν := hνj ▸ mono_comp _ _
  have hν : ν ^ n = 1 := by
    rw [hνj, ← MonObj.comp_pow, hι₀, MonObj.comp_one]
  have lift : ∀ {S : Over (Sp K)} (f : S ⟶ A.X) (hf : f ^ n = 1),
      (∀ s : S.left, ∃ y : ptOver K Ω ⟶ S, s ∈ Set.range y.left) →
      (∀ y : ptOver K Ω ⟶ S, y ≫ f ∈ G) → ∃ g : S ⟶ H, g ≫ ν = f := by
    intro S f hf hS hG
    have hr : Set.range (lt f hf).left ⊆ Set.range V.ι := by
      rintro _ ⟨s, rfl⟩
      obtain ⟨y, p, rfl⟩ := hS s
      rw [Scheme.Opens.range_ι]
      have e : y ≫ lt f hf = lt (y ≫ f) (hpow _ (hG y)) := by
        rw [← cancel_mono ι₀, hlt (y ≫ f) (hpow _ (hG y)), Category.assoc, hlt f hf]
      refine ⟨y ≫ f, hG y, p, ?_⟩
      rw [← e]
      rfl
    let g : S ⟶ H := Over.homMk (IsOpenImmersion.lift V.ι (lt f hf).left hr) (by
      change IsOpenImmersion.lift V.ι (lt f hf).left hr ≫ V.ι ≫ T.hom = S.hom
      rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact Over.w _)
    have hg : g ≫ j = lt f hf := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
    exact ⟨g, by rw [hνj, ← Category.assoc, hg, hlt f hf]⟩
  have hP : ∀ y : ptOver K Ω ⟶ H, y ≫ ν ∈ G := by
    intro y
    obtain ⟨p⟩ : Nonempty (Sp Ω) := inferInstance
    have hmem : (y ≫ j).left p ∈ U := by
      have h1 : V.ι (y.left p) ∈ Set.range V.ι := ⟨_, rfl⟩
      rw [Scheme.Opens.range_ι] at h1
      exact h1
    obtain ⟨x, hx, p', hp'⟩ := hmem
    rw [Subsingleton.elim p' p] at hp'
    obtain ⟨σ, hσ⟩ := exists_gal_of_apply_eq T (y ≫ j) (lt x (hpow x hx)) p hp'.symm
    have e : y ≫ ν = galPts A.X σ x := by
      show y ≫ ν = specAut σ ≫ x
      rw [hνj, ← Category.assoc, hσ, Category.assoc, hlt x (hpow x hx)]
    rw [e]
    exact hgal σ x hx

  have hone : η[A.X] = 1 := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  obtain ⟨e, he⟩ := lift η[A.X] (by rw [hone, one_pow])
    (fun s => ⟨toUnit _, by
      obtain ⟨p⟩ : Nonempty (Sp Ω) := inferInstance
      exact ⟨p, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩)
    (fun y => by
      have : y ≫ η[A.X] = 1 := by rw [Hom.one_def, toUnit_unique (toUnit _) y]
      rw [this]; exact one_mem G)
  have hmul : (ν ⊗ₘ ν) ≫ μ[A.X] = (fst H H ≫ ν) * (snd H H ≫ ν) := by
    rw [Hom.mul_def, ← lift_map, lift_fst_snd, Category.id_comp]
  haveI : IsFinite (H ⊗ H).hom := by rw [Over.tensorObj_hom]; infer_instance
  haveI : Etale (H ⊗ H).hom := by rw [Over.tensorObj_hom]; infer_instance
  have hν' : ∀ {S : Over (Sp K)} (g : S ⟶ H), (g ≫ ν) ^ n = 1 := fun g => by
    rw [← MonObj.comp_pow ν n g, hν, MonObj.comp_one]
  obtain ⟨m, hm⟩ := lift ((ν ⊗ₘ ν) ≫ μ[A.X])
    (by rw [hmul, mul_pow, hν' (fst H H), hν' (snd H H), _root_.one_mul])
    (exists_pt_of_finiteEtale _)
    (fun y => by
      rw [hmul, MonObj.comp_mul, ← Category.assoc, ← Category.assoc]
      exact mul_mem (hP (y ≫ fst H H)) (hP (y ≫ snd H H)))
  obtain ⟨i, hi⟩ := lift (ν ≫ ι[A.X]) (by rw [← Hom.inv_def, inv_pow, hν, inv_one])
    (exists_pt_of_finiteEtale _)
    (fun y => by
      rw [← Hom.inv_def, GrpObj.comp_inv]
      exact inv_mem (hP y))
  obtain ⟨gH, hνH⟩ := ReducedSubgroup.exists_grpObj_of_mono ν e m i he hm hi
  refine ⟨H, gH, ν, hνH, inferInstance, hHf, hHe, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨g, hg⟩ := lift x (hpow x hx) (fun s => ⟨𝟙 _, s, rfl⟩) (fun y => by
      obtain ⟨p⟩ : Nonempty (Sp Ω) := inferInstance
      obtain ⟨σ, hσ⟩ := exists_gal_of_apply_eq (ptOver K Ω) y (𝟙 _) p
        (Subsingleton.elim (α := PrimeSpectrum Ω) _ _)
      rw [hσ, Category.comp_id]
      exact hgal σ x hx)
    exact ⟨g, hg⟩
  · rintro ⟨y, rfl⟩
    exact hP y

end GlobalTheory.FinEtSubgroup
