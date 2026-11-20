import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceDecompositionInternalStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeBasic

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped TensorProduct

/- English proof (translation)
Introduce `K _ _ t hxt`. Take `⟨u, rfl⟩` from `hxt`. Establish `hp : IsProper (pullback.snd G'.hom (t ≫ f))` using `hx K (t ≫ f) ⟨u, by simp⟩`. Establish `sq : IsPullback (pullback.fst G.hom t ≫ φ) (pullback.snd G.hom t) G'.hom (t ≫ f)` using `(IsPullback.of_hasPullback G.hom t).paste_horiz h`. Rewrite using `[← sq.isoPullback_hom_snd]`.

Use `infer_instance`.
-/
theorem mem_abLocus_of_map {X Y : Scheme.{0}} {G : Over X} {G' : Over Y} {f : X ⟶ Y} {φ : G.left ⟶ G'.left}
    (h : IsPullback φ G.hom G'.hom f) {x : X} (hx : f x ∈ abLocus G') : x ∈ abLocus G := by
  intro K _ _ t hxt
  obtain ⟨u, rfl⟩ := hxt
  have hp : IsProper (pullback.snd G'.hom (t ≫ f)) := hx K (t ≫ f) ⟨u, by simp⟩
  have sq : IsPullback (pullback.fst G.hom t ≫ φ) (pullback.snd G.hom t) G'.hom (t ≫ f) :=
    (IsPullback.of_hasPullback G.hom t).paste_horiz h
  rw [← sq.isoPullback_hom_snd]
  infer_instance

/- English proof (translation)
Establish `hCi : IsIrreducible (irreducibleComponent y)` using `isIrreducible_irreducibleComponent`. Establish `hCc : IsClosed (irreducibleComponent y)` using `isClosed_irreducibleComponent`. Establish `hgen` using `hCi.isGenericPoint_genericPoint_closure`. Rewrite `hgen` using `[hCc.closure_eq]`. Establish `hη : hCi.genericPoint = y` using `hy _ (hgen.specializes mem_irreducibleComponent)`.

Rewrite `hgen` using `[hη]`. Establish `hmax` using `irreducibleComponent_mem_irreducibleComponents y`. Use `set D : Set P := ⋃₀ (irreducibleComponents P \ {irreducibleComponent y}) with hD`. Establish `hDc : IsClosed D`. Rewrite using `[hD, Set.sUnion_eq_biUnion]`.

Conclude with `Set.Finite.isClosed_biUnion (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset Set.diff_subset) fun C hC => isClosed_of_mem_irreducibleComponents C hC.1`. Establish `hyD : y ∉ D`. Introduce and unpack `⟨C, ⟨hC, hne⟩, hyC⟩`. Establish `hle : irreducibleComponent y ⊆ C`. Rewrite using `[← hgen.def]`.

Conclude with `(isClosed_of_mem_irreducibleComponents C hC).closure_subset_iff.2 (by simpa using hyC)`. Conclude with `hne (le_antisymm (hmax.2 hC.1 hle) hle)`. Take `⟨u, huD, huU⟩` from `hd.inter_open_nonempty Dᶜ hDc.isOpen_compl ⟨y, hyD⟩`. Establish `huC : u ∈ irreducibleComponent y`. Assume the negation of the conclusion as `hne`.

Use `huD ⟨irreducibleComponent u, ⟨irreducibleComponent_mem_irreducibleComponents u, ?_⟩, mem_irreducibleComponent⟩` and prove the remaining obligations. Introduce `e`. Conclude with `hne (by`. Establish `: u ∈ irreducibleComponent u` using `mem_irreducibleComponent`. Rewrite `this` using `[Set.mem_singleton_iff.1 e]`.

Conclude with `this)`. Conclude with `(hgen.specializes huC).mem_open hU huU`.
-/
theorem mem_of_dense_of_maximal {P : Type} [TopologicalSpace P] [TopologicalSpace.NoetherianSpace P] [QuasiSober P]
    {U : Set P} (hU : IsOpen U) (hd : Dense U) {y : P} (hy : ∀ y', y' ⤳ y → y' = y) : y ∈ U := by
  classical
  have hCi : IsIrreducible (irreducibleComponent y) := isIrreducible_irreducibleComponent
  have hCc : IsClosed (irreducibleComponent y) := isClosed_irreducibleComponent
  have hgen := hCi.isGenericPoint_genericPoint_closure
  rw [hCc.closure_eq] at hgen
  have hη : hCi.genericPoint = y := hy _ (hgen.specializes mem_irreducibleComponent)
  rw [hη] at hgen
  have hmax := irreducibleComponent_mem_irreducibleComponents y
  set D : Set P := ⋃₀ (irreducibleComponents P \ {irreducibleComponent y}) with hD
  have hDc : IsClosed D := by
    rw [hD, Set.sUnion_eq_biUnion]
    exact Set.Finite.isClosed_biUnion
      (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset Set.diff_subset)
      fun C hC => isClosed_of_mem_irreducibleComponents C hC.1
  have hyD : y ∉ D := by
    rintro ⟨C, ⟨hC, hne⟩, hyC⟩
    have hle : irreducibleComponent y ⊆ C := by
      rw [← hgen.def]
      exact (isClosed_of_mem_irreducibleComponents C hC).closure_subset_iff.2 (by simpa using hyC)
    exact hne (le_antisymm (hmax.2 hC.1 hle) hle)
  obtain ⟨u, huD, huU⟩ := hd.inter_open_nonempty Dᶜ hDc.isOpen_compl ⟨y, hyD⟩
  have huC : u ∈ irreducibleComponent y := by
    by_contra hne
    refine huD ⟨irreducibleComponent u, ⟨irreducibleComponent_mem_irreducibleComponents u, ?_⟩,
      mem_irreducibleComponent⟩
    intro e
    exact hne (by
      have : u ∈ irreducibleComponent u := mem_irreducibleComponent
      rw [Set.mem_singleton_iff.1 e] at this
      exact this)
  exact (hgen.specializes huC).mem_open hU huU

/- English proof (translation)
Take `⟨N, i, hi, rfl⟩` from `hs`. Use `isProper_str O N` as an intermediate fact. Establish `: IsProper (i ≫ PSpace.str O N)` using `inferInstance`. Establish `hl : LocallyOfFiniteType (pullback.snd (i ≫ PSpace.str O N) (spMap β))` using `inferInstance`. Establish `hq : QuasiCompact (pullback.snd (i ≫ PSpace.str O N) (spMap β))` using `inferInstance`.

Establish `: IsLocallyNoetherian (pullback (i ≫ PSpace.str O N) (spMap β))` using `LocallyOfFiniteType.isLocallyNoetherian (pullback.snd _ _)`. Establish `: CompactSpace ↥(pullback (i ≫ PSpace.str O N) (spMap β))` using `QuasiCompact.compactSpace_of_compactSpace (pullback.snd _ _)`. Establish `: IsNoetherian (pullback (i ≫ PSpace.str O N) (spMap β))` using `{}`. Use `infer_instance`.
-/
theorem noetherianSpace_pullback {X : Scheme.{0}} {O F : Type} [CommRing O] [Field F] {s : X ⟶ Sp O}
    (hs : IsProjOver s) (β : O →+* F) : TopologicalSpace.NoetherianSpace ↥(pullback s (spMap β)) := by
  obtain ⟨N, i, hi, rfl⟩ := hs
  have := isProper_str O N
  have : IsProper (i ≫ PSpace.str O N) := inferInstance
  have hl : LocallyOfFiniteType (pullback.snd (i ≫ PSpace.str O N) (spMap β)) := inferInstance
  have hq : QuasiCompact (pullback.snd (i ≫ PSpace.str O N) (spMap β)) := inferInstance
  have : IsLocallyNoetherian (pullback (i ≫ PSpace.str O N) (spMap β)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd _ _)
  have : CompactSpace ↥(pullback (i ≫ PSpace.str O N) (spMap β)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd _ _)
  have : IsNoetherian (pullback (i ≫ PSpace.str O N) (spMap β)) := {}
  infer_instance

/- English proof (translation)
Establish `h1 : ∀ u : F, _root_.IsIntegral Ω₀ ((1 : Ω₀) ⊗ₜ[O] u)`. Introduce `u`. Take `⟨a, ha, hi⟩` from `hF u`. Establish `h2 : _root_.IsIntegral O ((1 : Ω₀) ⊗ₜ[O] (a • u))` using `hi.map (Algebra.TensorProduct.includeRight : F →ₐ[O] Ω₀ ⊗[O] F)`. Establish `h3 : _root_.IsIntegral Ω₀ ((1 : Ω₀) ⊗ₜ[O] (a • u))` using `h2.tower_top`.

Establish `ha' : algebraMap O Ω₀ a ≠ 0` using `fun h => ha (hγ (by rw [h, map_zero]))`. Establish `e : (1 : Ω₀) ⊗ₜ[O] u = (algebraMap O Ω₀ a)⁻¹ • ((1 : Ω₀) ⊗ₜ[O] (a • u))`. Rewrite using `[TensorProduct.smul_tmul', ← TensorProduct.smul_tmul, smul_eq_mul, _root_.mul_one, Algebra.smul_def, mul_inv_cancel₀ ha']`. Rewrite using `[e]`. Conclude with `h3.smul _`.

Use `⟨fun x => ?_⟩` and prove the remaining obligations. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact isIntegral_zero`. Consider the case `tmul a u`. Establish `e : a ⊗ₜ[O] u = a • ((1 : Ω₀) ⊗ₜ[O] u)`.

Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]`. Rewrite using `[e]`. Conclude with `(h1 u).smul a`. Consider the case `add x y hx hy => exact hx.add hy`.
-/
theorem isIntegral_tensor {O Ω₀ F : Type} [CommRing O] [Field Ω₀] [Field F] [Algebra O Ω₀] [Algebra O F]
    (hγ : Function.Injective (algebraMap O Ω₀))
    (hF : ∀ u : F, ∃ a : O, a ≠ 0 ∧ _root_.IsIntegral O (a • u)) :
    Algebra.IsIntegral Ω₀ (Ω₀ ⊗[O] F) := by
  have h1 : ∀ u : F, _root_.IsIntegral Ω₀ ((1 : Ω₀) ⊗ₜ[O] u) := by
    intro u
    obtain ⟨a, ha, hi⟩ := hF u
    have h2 : _root_.IsIntegral O ((1 : Ω₀) ⊗ₜ[O] (a • u)) :=
      hi.map (Algebra.TensorProduct.includeRight : F →ₐ[O] Ω₀ ⊗[O] F)
    have h3 : _root_.IsIntegral Ω₀ ((1 : Ω₀) ⊗ₜ[O] (a • u)) := h2.tower_top
    have ha' : algebraMap O Ω₀ a ≠ 0 := fun h => ha (hγ (by rw [h, map_zero]))
    have e : (1 : Ω₀) ⊗ₜ[O] u = (algebraMap O Ω₀ a)⁻¹ • ((1 : Ω₀) ⊗ₜ[O] (a • u)) := by
      rw [TensorProduct.smul_tmul', ← TensorProduct.smul_tmul, smul_eq_mul, _root_.mul_one, Algebra.smul_def,
        mul_inv_cancel₀ ha']
    rw [e]
    exact h3.smul _
  refine ⟨fun x => ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => exact isIntegral_zero
  | tmul a u =>
    have e : a ⊗ₜ[O] u = a • ((1 : Ω₀) ⊗ₜ[O] u) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [e]
    exact (h1 u).smul a
  | add x y hx hy => exact hx.add hy

/- English proof (translation)
Use `letI := β.toAlgebra`. Establish `: CharZero O` using `β.charZero`. Establish `hQ : IsAlgebraic ℚ u` using `Algebra.IsAlgebraic.isAlgebraic u`. Establish `hZ : IsAlgebraic ℤ u` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 hQ`. Establish `hO : IsAlgebraic O u` using `hZ.extendScalars (Int.cast_injective)`.

Conclude with `hO.exists_integral_multiple`.
-/
theorem exists_integral_multiple_of_injective {O : Type} [CommRing O] {F : IntermediateField ℚ ℂ}
    [FiniteDimensional ℚ F] (β : O →+* F) (hβ : Function.Injective β) (u : F) :
    letI := β.toAlgebra
    ∃ a : O, a ≠ 0 ∧ _root_.IsIntegral O (a • u) := by
  letI := β.toAlgebra
  have : CharZero O := β.charZero
  have hQ : IsAlgebraic ℚ u := Algebra.IsAlgebraic.isAlgebraic u
  have hZ : IsAlgebraic ℤ u := (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 hQ
  have hO : IsAlgebraic O u := hZ.extendScalars (Int.cast_injective)
  exact hO.exists_integral_multiple

/- English proof (translation)
Use `letI := β.toAlgebra`. Use `letI := g₀.toAlgebra`. Establish `hy' : pullback.fst s (spMap β) y' = genPt ξ₀` using `GlobalTheory.CompanionTheory.Ar.CptInh.nogen ξ₀ h₀ _ (hy ▸ hyy.map (pullback.fst s (spMap β)).continuous)`. Establish `hsurj : SurjectiveOnStalks ξ₀`. Establish `: IsIso (Scheme.stalkClosedPointTo ξ₀)` using `(ConcreteCategory.isIso_iff_bijective _).2 h₀.bij`.

Rewrite using `[← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ₀]`. Use `infer_instance`. Establish `hemb` using `SurjectiveOnStalks.isEmbedding_pullback (pullback.fst s (spMap β)) ξ₀`. Take `⟨z, hz, hz₂⟩` from `Scheme.Pullback.exists_preimage_pullback (f := pullback.fst s (spMap β)) (g := ξ₀) y (IsLocalRing.closedPoint Ω₀) hy`. Take `⟨z', hz', hz₂'⟩` from `Scheme.Pullback.exists_preimage_pullback (f := pullback.fst s (spMap β)) (g := ξ₀) y' (IsLocalRing.closedPoint Ω₀) hy'`.

Establish `hzz : z' ⤳ z`. Rewrite using `[← hemb.isInducing.specializes_iff, specializes_prod]`. Simplify using `only [hz, hz', hz₂, hz₂']`. Conclude with `⟨hyy, specializes_rfl⟩`. Establish `sq : IsPullback (pullback.snd (pullback.fst s (spMap β)) ξ₀) (pullback.fst (pullback.fst s (spMap β)) ξ₀ ≫ pullback.snd s (spMap β)) (spMap g₀) (spMap β)`.

Rewrite using `[← hs]`. Conclude with `(IsPullback.of_hasPullback (pullback.fst s (spMap β)) ξ₀).flip.paste_vert (IsPullback.of_hasPullback s (spMap β))`. Set `e` to `sq.isoPullback ≪≫ pullbackSpecIso O Ω₀ F`. Establish `hint : Algebra.IsIntegral Ω₀ (Ω₀ ⊗[O] F)` using `isIntegral_tensor hγ hF`. Set `p' : PrimeSpectrum (Ω₀ ⊗[O] F)` to `e.hom z'`.

Set `p : PrimeSpectrum (Ω₀ ⊗[O] F)` to `e.hom z`. Establish `hle : p' ≤ p` using `(PrimeSpectrum.le_iff_specializes _ _).2 (hzz.map e.hom.continuous)`. Establish `hcm : (Ideal.comap (algebraMap Ω₀ (Ω₀ ⊗[O] F)) p'.asIdeal).IsMaximal` using `Ideal.IsPrime.isMaximal' (Ideal.comap_isPrime _ _)`. Establish `hmax : p'.asIdeal.IsMaximal` using `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := Ω₀) p'.asIdeal hcm`. Establish `heq : p' = p` using `PrimeSpectrum.ext (hmax.eq_of_le p.isPrime.ne_top hle)`.

Establish `hzeq : z' = z`. Establish `h` using `congrArg e.inv heq`. Simplify `h` using `[p, p']`. Rewrite using `[← hz, ← hz', hzeq]`.
-/
theorem eq_of_specializes_of_fst {X : Scheme.{0}} {O F Ω₀ : Type} [CommRing O] [Field F] [Field Ω₀] (s : X ⟶ Sp O)
    (β : O →+* F) (g₀ : O →+* Ω₀) (ξ₀ : Sp Ω₀ ⟶ X) (h₀ : IsCptGen ξ₀) (hs : ξ₀ ≫ s = spMap g₀)
    (hγ : Function.Injective g₀)
    (hF : letI := β.toAlgebra; ∀ u : F, ∃ a : O, a ≠ 0 ∧ _root_.IsIntegral O (a • u))
    {y y' : ↥(pullback s (spMap β))} (hy : pullback.fst s (spMap β) y = genPt ξ₀) (hyy : y' ⤳ y) : y' = y := by
  letI := β.toAlgebra
  letI := g₀.toAlgebra
  have hy' : pullback.fst s (spMap β) y' = genPt ξ₀ :=
    GlobalTheory.CompanionTheory.Ar.CptInh.nogen ξ₀ h₀ _ (hy ▸ hyy.map (pullback.fst s (spMap β)).continuous)
  have hsurj : SurjectiveOnStalks ξ₀ := by
    have : IsIso (Scheme.stalkClosedPointTo ξ₀) := (ConcreteCategory.isIso_iff_bijective _).2 h₀.bij
    rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ₀]
    infer_instance
  have hemb := SurjectiveOnStalks.isEmbedding_pullback (pullback.fst s (spMap β)) ξ₀
  obtain ⟨z, hz, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.fst s (spMap β)) (g := ξ₀) y
    (IsLocalRing.closedPoint Ω₀) hy
  obtain ⟨z', hz', hz₂'⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.fst s (spMap β)) (g := ξ₀) y'
    (IsLocalRing.closedPoint Ω₀) hy'
  have hzz : z' ⤳ z := by
    rw [← hemb.isInducing.specializes_iff, specializes_prod]
    simp only [hz, hz', hz₂, hz₂']
    exact ⟨hyy, specializes_rfl⟩
  have sq : IsPullback (pullback.snd (pullback.fst s (spMap β)) ξ₀)
      (pullback.fst (pullback.fst s (spMap β)) ξ₀ ≫ pullback.snd s (spMap β)) (spMap g₀) (spMap β) := by
    rw [← hs]
    exact (IsPullback.of_hasPullback (pullback.fst s (spMap β)) ξ₀).flip.paste_vert
      (IsPullback.of_hasPullback s (spMap β))
  let e := sq.isoPullback ≪≫ pullbackSpecIso O Ω₀ F
  have hint : Algebra.IsIntegral Ω₀ (Ω₀ ⊗[O] F) := isIntegral_tensor hγ hF
  let p' : PrimeSpectrum (Ω₀ ⊗[O] F) := e.hom z'
  let p : PrimeSpectrum (Ω₀ ⊗[O] F) := e.hom z
  have hle : p' ≤ p := (PrimeSpectrum.le_iff_specializes _ _).2 (hzz.map e.hom.continuous)
  have hcm : (Ideal.comap (algebraMap Ω₀ (Ω₀ ⊗[O] F)) p'.asIdeal).IsMaximal :=
    Ideal.IsPrime.isMaximal' (Ideal.comap_isPrime _ _)
  have hmax : p'.asIdeal.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := Ω₀) p'.asIdeal hcm
  have heq : p' = p := PrimeSpectrum.ext (hmax.eq_of_le p.isPrime.ne_top hle)
  have hzeq : z' = z := by
    have h := congrArg e.inv heq
    simpa [p, p'] using h
  rw [← hz, ← hz', hzeq]

/- English proof (translation)
Use `noetherianSpace_pullback Y.proj β` as an intermediate fact. Use `Y.jQ_open` as an intermediate fact. Use `c.fin` as an intermediate fact. Conclude with `mem_of_dense_of_maximal Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense fun y' h' => eq_of_specializes_of_fst Y.s β g₀ ξ₀ h₀ hs hg (exists_integral_multiple_of_injective β hβ) hy h'`.
-/
theorem mem_range_jQ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    (hβ : Function.Injective β) {Ω₀ : Type} [Field Ω₀] (ξ₀ : Sp Ω₀ ⟶ Y.X) (h₀ : IsCptGen ξ₀) (g₀ : O →+* Ω₀)
    (hs : ξ₀ ≫ Y.s = spMap g₀) (hg : Function.Injective g₀) (y : ↥(pullback Y.s (spMap β)))
    (hy : pullback.fst Y.s (spMap β) y = genPt ξ₀) : y ∈ Set.range Y.jQ := by
  have := noetherianSpace_pullback Y.proj β
  have := Y.jQ_open
  have := c.fin
  exact mem_of_dense_of_maximal Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense fun y' h' =>
    eq_of_specializes_of_fst Y.s β g₀ ξ₀ h₀ hs hg (exists_integral_multiple_of_injective β hβ) hy h'

/- English proof (translation)
Establish `hgen : IsGenericPoint (genPt ξ) (Set.univ : Set X)` using `Set.eq_univ_of_forall fun q => specializes_iff_mem_closure.1 (all q)`. Establish `: IrreducibleSpace X` using `{ isPreirreducible_univ := hgen.isIrreducible.2, toNonempty := ⟨genPt ξ⟩ }`. Establish `: ∀ x : X, _root_.IsReduced (X.presheaf.stalk x)` using `fun x => by`. Use `(hn x).1` as an intermediate fact. Use `infer_instance`.

Use `isReduced_of_isReduced_stalk X` as an intermediate fact. Establish `: AlgebraicGeometry.IsIntegral X` using `isIntegral_of_irreducibleSpace_of_isReduced X`. Establish `hgp : genericPoint X = genPt ξ` using `(genericPoint_spec X).eq hgen`. Establish `key : ∀ (x : X) (_ : x = genericPoint X) (hs : x ⤳ genericPoint X), IsIso (X.presheaf.stalkSpecializes hs)`. Introduce and unpack `x rfl hs`.

Establish `: X.presheaf.stalkSpecializes hs = 𝟙 _` using `TopCat.Presheaf.stalkSpecializes_refl _ _`. Rewrite using `[this]`. Use `infer_instance`. Establish `hsp : genPt ξ ⤳ genericPoint X` using `hgp ▸ specializes_rfl`. Use `key _ hgp.symm hsp` as an intermediate fact.

Set `e : X.functionField →+* Ω` to `(X.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo ξ).hom`. Establish `hs₁ : Function.Surjective (X.presheaf.stalkSpecializes hsp).hom` using `((ConcreteCategory.isIso_iff_bijective (X.presheaf.stalkSpecializes hsp)).1 inferInstance).2`. Establish `he : Function.Surjective e` using `hg.bij.2.comp hs₁`. Establish `hmap : ∀ x, genMap ξ q x = e (algebraMap (X.presheaf.stalk q.1) X.functionField x)`. Introduce `x`.

Establish `h` using `TopCat.Presheaf.stalkSpecializes_comp X.presheaf hsp (genericPoint_specializes q.1)`. Establish `h'` using `congrArg (fun m => (m ≫ Scheme.stalkClosedPointTo ξ).hom x) h`. Conclude with `h'.symm`. Take `⟨b, rfl⟩` from `he a`. Establish `hb : _root_.IsIntegral ℤ b`.

Use `(isIntegral_algHom_iff e.toIntAlgHom e.injective).1 ha` and prove the remaining obligations. Use `(hn q.1).2` as an intermediate fact. Establish `hb' : _root_.IsIntegral (X.presheaf.stalk q.1) b` using `hb.tower_top`. Take `⟨w, rfl⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hb'`. Conclude with `⟨w, hmap w⟩`.
-/
theorem mem_regAt_of_isIntegral {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hg : IsCptGen ξ) (all : ∀ q : X, genPt ξ ⤳ q) (hn : IsNormalScheme X) (q : Cpt ξ) {a : Ω}
    (ha : _root_.IsIntegral ℤ a) : a ∈ regAt ξ q := by
  have hgen : IsGenericPoint (genPt ξ) (Set.univ : Set X) :=
    Set.eq_univ_of_forall fun q => specializes_iff_mem_closure.1 (all q)
  have : IrreducibleSpace X :=
    { isPreirreducible_univ := hgen.isIrreducible.2, toNonempty := ⟨genPt ξ⟩ }
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have := (hn x).1
    infer_instance
  have := isReduced_of_isReduced_stalk X
  have : AlgebraicGeometry.IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  have hgp : genericPoint X = genPt ξ := (genericPoint_spec X).eq hgen
  have key : ∀ (x : X) (_ : x = genericPoint X) (hs : x ⤳ genericPoint X),
      IsIso (X.presheaf.stalkSpecializes hs) := by
    rintro x rfl hs
    have : X.presheaf.stalkSpecializes hs = 𝟙 _ := TopCat.Presheaf.stalkSpecializes_refl _ _
    rw [this]
    infer_instance
  have hsp : genPt ξ ⤳ genericPoint X := hgp ▸ specializes_rfl
  have := key _ hgp.symm hsp
  let e : X.functionField →+* Ω := (X.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo ξ).hom
  have hs₁ : Function.Surjective (X.presheaf.stalkSpecializes hsp).hom :=
    ((ConcreteCategory.isIso_iff_bijective (X.presheaf.stalkSpecializes hsp)).1 inferInstance).2
  have he : Function.Surjective e := hg.bij.2.comp hs₁
  have hmap : ∀ x, genMap ξ q x = e (algebraMap (X.presheaf.stalk q.1) X.functionField x) := by
    intro x
    have h := TopCat.Presheaf.stalkSpecializes_comp X.presheaf hsp (genericPoint_specializes q.1)
    have h' := congrArg (fun m => (m ≫ Scheme.stalkClosedPointTo ξ).hom x) h
    exact h'.symm
  obtain ⟨b, rfl⟩ := he a
  have hb : _root_.IsIntegral ℤ b := by
    refine (isIntegral_algHom_iff e.toIntAlgHom e.injective).1 ha
  have := (hn q.1).2
  have hb' : _root_.IsIntegral (X.presheaf.stalk q.1) b := hb.tower_top
  obtain ⟨w, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hb'
  exact ⟨w, hmap w⟩

section Labels

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Introduce `h`. Establish `h1` using `H.sqrt_neg_disc_sq`. Rewrite `h1` using `[h]`. Establish `h2 : (H.d : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 H.d_prime.ne_zero`. Conclude with `h2 (by simpa using h1.symm)`.
-/
theorem rt0_ne_zero (H : Host E) : H.rt0 ≠ 0 := by
  intro h
  have h1 := H.sqrt_neg_disc_sq
  rw [h] at h1
  have h2 : (H.d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
  exact h2 (by simpa using h1.symm)

/- English proof (translation)
Establish `h` using `H.sqrt_neg_disc_sq`. Establish `h1` using `congrArg Complex.re h`. Establish `h2` using `congrArg Complex.im h`. Simplify using `only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re, Complex.natCast_im, neg_zero] at h1 h2`. Establish `hd : (0 : ℝ) < H.d` using `Nat.cast_pos.2 H.d_prime.pos`.

Establish `hre : H.rt0.re = 0`. Assume the negation of the conclusion as `hne`. Establish `him : H.rt0.im = 0`. Establish `: H.rt0.re * H.rt0.im = 0` using `by linarith`. Conclude with `(mul_eq_zero.1 this).resolve_left hne`.

Rewrite `h1` using `[him]`. Use polynomial arithmetic with `[mul_self_nonneg H.rt0.re]`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[hre]`. Simplify using the standard rewrite rules.
-/
theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by
  have h := H.sqrt_neg_disc_sq
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im, neg_zero] at h1 h2
  have hd : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
  have hre : H.rt0.re = 0 := by
    by_contra hne
    have him : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [him] at h1
    nlinarith [mul_self_nonneg H.rt0.re]
  apply Complex.ext
  · simp [hre]
  · simp

def labelHom (H : Host E) : CMType H ⊕ CMType H → (E →+* ℂ)
  | .inl τ => τ.1
  | .inr τ => ComplexEmbedding.conjugate τ.1

/- English proof (translation)
Establish `h1 : ((H.rt : 𝓞 E) : E) ^ 2 = -(H.d : E)`. Use `congrArg (algebraMap (𝓞 E) E) H.rt_sq` as an intermediate fact. Simplify using `using this`. Establish `h2 : σ (H.rt : E) ^ 2 = H.rt0 ^ 2`. Rewrite using `[← map_pow, h1, H.sqrt_neg_disc_sq]`.

Simplify using the standard rewrite rules. Conclude with `sq_eq_sq_iff_eq_or_eq_neg.1 h2`.
-/
theorem embed_rt (H : Host E) (σ : E →+* ℂ) : σ (H.rt : E) = H.rt0 ∨ σ (H.rt : E) = -H.rt0 := by
  have h1 : ((H.rt : 𝓞 E) : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have h2 : σ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, h1, H.sqrt_neg_disc_sq]
    simp
  exact sq_eq_sq_iff_eq_or_eq_neg.1 h2

/- English proof (translation)
Establish `hval : ∀ τ : CMType H, ComplexEmbedding.conjugate τ.1 (H.rt : E) = -H.rt0` using `fun τ => by`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, τ.2, rt0_conj_neg_ne_zero]`. Establish `hne : H.rt0 ≠ -H.rt0` using `fun h => rt0_ne_zero H (self_eq_neg.1 h)`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(τ | τ) (τ' | τ') h`.

Conclude with `congrArg _ (Subtype.ext h)`. Conclude with `absurd (by simpa [labelHom, τ.2, hval τ'] using congrArg (· (H.rt : E)) h) hne`. Conclude with `absurd (by simpa [labelHom, τ'.2, hval τ] using (congrArg (· (H.rt : E)) h).symm) hne`. Conclude with `congrArg _ (Subtype.ext (star_injective h))`. Introduce `σ`.

Break down `embed_rt H σ with h | h` into its components or cases. Conclude with `⟨.inl ⟨σ, h⟩, rfl⟩`. Use `⟨.inr ⟨ComplexEmbedding.conjugate σ, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, h, map_neg, rt0_conj_neg_ne_zero, neg_neg]`. Conclude with `star_star σ`.
-/
theorem labelHom_bijective (H : Host E) : Function.Bijective (labelHom H) := by
  have hval : ∀ τ : CMType H, ComplexEmbedding.conjugate τ.1 (H.rt : E) = -H.rt0 := fun τ => by
    rw [ComplexEmbedding.conjugate_coe_eq, τ.2, rt0_conj_neg_ne_zero]
  have hne : H.rt0 ≠ -H.rt0 := fun h => rt0_ne_zero H (self_eq_neg.1 h)
  constructor
  · rintro (τ | τ) (τ' | τ') h
    · exact congrArg _ (Subtype.ext h)
    · exact absurd (by simpa [labelHom, τ.2, hval τ'] using congrArg (· (H.rt : E)) h) hne
    · exact absurd (by simpa [labelHom, τ'.2, hval τ] using (congrArg (· (H.rt : E)) h).symm) hne
    · exact congrArg _ (Subtype.ext (star_injective h))
  · intro σ
    rcases embed_rt H σ with h | h
    · exact ⟨.inl ⟨σ, h⟩, rfl⟩
    · refine ⟨.inr ⟨ComplexEmbedding.conjugate σ, ?_⟩, ?_⟩
      · rw [ComplexEmbedding.conjugate_coe_eq, h, map_neg, rt0_conj_neg_ne_zero, neg_neg]
      · exact star_star σ

/- English proof (translation)
Break down `s with τ | τ` into its components or cases. Both sides reduce to the same expression. Use `show τ.1 ((H.bar a : 𝓞 E) : E) = ComplexEmbedding.conjugate τ.1 (a : E)`. Rewrite using `[H.bar_eq, ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj]`.
-/
theorem coe_labelEmb {H : Host E} {l : Level H} (c : Coeff l) (s : CMType H ⊕ CMType H) (a : 𝓞 E) :
    ((labelEmb c s a : c.F) : ℂ) = labelHom H s (a : E) := by
  rcases s with τ | τ
  · rfl
  · show τ.1 ((H.bar a : 𝓞 E) : E) = ComplexEmbedding.conjugate τ.1 (a : E)
    rw [H.bar_eq, ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj]

/- English proof (translation)
Introduce `s s' h`. Use `(labelHom_bijective H).1 ?_` and prove the remaining obligations. Use `IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => ?_)` and prove the remaining obligations. Use `show labelHom H s (a : E) = labelHom H s' (a : E)`. Rewrite using `[← coe_labelEmb c, ← coe_labelEmb c, h]`.
-/
theorem labelEmb_injective {H : Host E} {l : Level H} (c : Coeff l) :
    Function.Injective (labelEmb (H := H) c) := by
  intro s s' h
  refine (labelHom_bijective H).1 ?_
  refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => ?_)
  show labelHom H s (a : E) = labelHom H s' (a : E)
  rw [← coe_labelEmb c, ← coe_labelEmb c, h]

end Labels

end GlobalTheory.CompanionTheory.Ar.HodgeBasic

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 hβ`. Establish `hcst : Function.Injective 𝔐.cst` using `𝔐.cst.injective`. Establish `hchar : CharZero Ω` using `charZero_of_injective_ringHom hcst`. Set `g₀ : O →+* 𝔐.Ω₀` to `(Spec.preimage (𝔐.ξ₀ ≫ Y.s)).hom`. Establish `hs : 𝔐.ξ₀ ≫ Y.s = spMap g₀` using `by show _ = Spec.map (CommRingCat.ofHom (Spec.preimage (𝔐.ξ₀ ≫ Y.s)).hom)`.

Rewrite using `[CommRingCat.ofHom_hom, Spec.map_preimage]`. Establish `hfn : 𝔐.ξ ≫ 𝔐.f = spMap 𝔐.fn ≫ 𝔐.ξ₀` using `𝔐.fn_over`. Establish `hcomp : 𝔐.fn.comp g₀ = 𝔐.cst.comp β`. Establish `h1 : spMap (𝔐.fn.comp g₀) = spMap (𝔐.cst.comp β)`. Rewrite using `[← 𝔐.cst_over, ← Category.assoc, hfn, Category.assoc, hs]`.

Simplify using `only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]`. Establish `h2` using `Spec.map_injective h1`. Conclude with `congrArg CommRingCat.Hom.hom h2`. Establish `hg : Function.Injective g₀`. Use `Function.Injective.of_comp (f := 𝔐.fn) ?_` and prove the remaining obligations.

Establish `: (𝔐.fn ∘ g₀) = 𝔐.cst ∘ β` using `congrArg DFunLike.coe hcomp`. Rewrite using `[this]`. Conclude with `hcst.comp hβ`. Establish `hw : (𝔐.ξ ≫ 𝔐.f) ≫ Y.s = spMap 𝔐.cst ≫ spMap β`. Rewrite using `[Category.assoc, 𝔐.cst_over]`.

Simplify using `only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]`. Set `g : Sp Ω ⟶ pullback Y.s (spMap β)` to `pullback.lift (𝔐.ξ ≫ 𝔐.f) (spMap 𝔐.cst) hw`. Establish `hgf : g ≫ pullback.fst _ _ = 𝔐.ξ ≫ 𝔐.f` using `pullback.lift_fst _ _ _`. Establish `hall : ∀ w : Sp Ω, pullback.fst Y.s (spMap β) (g w) = genPt 𝔐.ξ₀`. Introduce `w`.

Rewrite using `[← Scheme.Hom.comp_apply, hgf, hfn, Scheme.Hom.comp_apply]`. Conclude with `congrArg 𝔐.ξ₀ (Subsingleton.elim (α := PrimeSpectrum 𝔐.Ω₀) _ _)`. Establish `hran : Set.range g ⊆ Set.range Y.jQ`. Introduce and unpack `_ ⟨w, rfl⟩`. Conclude with `HodgeBasic.mem_range_jQ Y hβ 𝔐.ξ₀ 𝔐.gen₀ g₀ hs hg _ (hall w)`.

Use `Y.jQ_open` as an intermediate fact. Establish `hinj : Function.Injective 𝔐.emb`. Introduce `s s' h`. Use `HodgeBasic.labelEmb_injective c (RingHom.ext fun a => hcst ?_)` and prove the remaining obligations. Conclude with `congrArg (fun m : 𝓞 E →+* Ω => m a) h`.

Use `letI : Fintype (CMType H) := Fintype.ofFinite _`. Establish `hcard : Fintype.card (CMType H ⊕ CMType H) = Module.finrank ℚ E`. Rewrite using `[Fintype.card_of_bijective (HodgeBasic.labelHom_bijective H), Embeddings.card]`. Establish `hint` using `GlobalTheory.T.eigenspace_decomposition_internal Ω 𝔐.Li E 𝔐.ρ (CMType H ⊕ CMType H) 𝔐.emb hinj hcard`. Use `⟨?_, ⟨IsOpenImmersion.lift Y.jQ g hran, ?_⟩, hchar, hinj, ?_, hint.submodule_iSup_eq_top, hint.submodule_iSupIndep, ?_⟩` and prove the remaining obligations.

Use `HodgeBasic.mem_abLocus_of_map 𝔐.m.cart.1 ?_` and prove the remaining obligations. Establish `hf : ∀ w : Sp Ω, pullback.fst Y.s (spMap β) (g w) = 𝔐.f (𝔐.ξ w)`. Introduce `w`. Rewrite using `[← Scheme.Hom.comp_apply, hgf, Scheme.Hom.comp_apply]`. Establish `h2 : g (IsLocalRing.closedPoint Ω) ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G`.

Rewrite using `[Y.ab_gen]`. Conclude with `hran ⟨_, rfl⟩`. Conclude with `(congrArg (· ∈ abLocus Y.t.G) (hf (IsLocalRing.closedPoint Ω))).mp h2`. Rewrite using `[Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, hgf]`. Introduce `s`.

Take `⟨U, hU, b, hb, hfr⟩` from `𝔐.vb s ⟨genPt 𝔐.ξ, specializes_rfl⟩ (Set.mem_univ _)`. Establish `hli` using `(hfr ⟨genPt 𝔐.ξ, specializes_rfl⟩ (Set.mem_univ _) hU).1`. Use `show Module.finrank Ω (eigSp 𝔐.ρ (𝔐.cst.comp (labelEmb c s))) = _`. Rewrite using `[← hb, finrank_span_eq_card hli, Fintype.card_fin]`. Introduce `s a q`.

Use `HodgeBasic.mem_regAt_of_isIntegral 𝔐.tie.gen 𝔐.all 𝔐.normal q ?_` and prove the remaining obligations. Conclude with `(Algebra.IsIntegral.isIntegral (R := ℤ) a).map (𝔐.emb s).toIntAlgHom`.
-/
theorem HodgeCpt.basic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ)
    (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y), Function.Injective β → 𝔐.Interior 𝔐.ξ ∧
      (∃ x : Sp Ω ⟶ Xo.XF c, 𝔐.ξ ≫ 𝔐.f = x ≫ Y.j) ∧ CharZero Ω ∧ Function.Injective 𝔐.emb ∧
      (∀ s, Module.finrank Ω (𝔐.Vgen s) = labelRk D s) ∧ (⨆ s, 𝔐.Vgen s) = ⊤ ∧ iSupIndep 𝔐.Vgen ∧
      ∀ s a (q : Cpt 𝔐.ξ), 𝔐.emb s a ∈ regAt 𝔐.ξ q := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 hβ
  classical
  have hcst : Function.Injective 𝔐.cst := 𝔐.cst.injective
  have hchar : CharZero Ω := charZero_of_injective_ringHom hcst

  let g₀ : O →+* 𝔐.Ω₀ := (Spec.preimage (𝔐.ξ₀ ≫ Y.s)).hom
  have hs : 𝔐.ξ₀ ≫ Y.s = spMap g₀ := by
    show _ = Spec.map (CommRingCat.ofHom (Spec.preimage (𝔐.ξ₀ ≫ Y.s)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hfn : 𝔐.ξ ≫ 𝔐.f = spMap 𝔐.fn ≫ 𝔐.ξ₀ := 𝔐.fn_over
  have hcomp : 𝔐.fn.comp g₀ = 𝔐.cst.comp β := by
    have h1 : spMap (𝔐.fn.comp g₀) = spMap (𝔐.cst.comp β) := by
      rw [← 𝔐.cst_over, ← Category.assoc, hfn, Category.assoc, hs]
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2
  have hg : Function.Injective g₀ := by
    refine Function.Injective.of_comp (f := 𝔐.fn) ?_
    have : (𝔐.fn ∘ g₀) = 𝔐.cst ∘ β := congrArg DFunLike.coe hcomp
    rw [this]
    exact hcst.comp hβ

  have hw : (𝔐.ξ ≫ 𝔐.f) ≫ Y.s = spMap 𝔐.cst ≫ spMap β := by
    rw [Category.assoc, 𝔐.cst_over]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  let g : Sp Ω ⟶ pullback Y.s (spMap β) := pullback.lift (𝔐.ξ ≫ 𝔐.f) (spMap 𝔐.cst) hw
  have hgf : g ≫ pullback.fst _ _ = 𝔐.ξ ≫ 𝔐.f := pullback.lift_fst _ _ _
  have hall : ∀ w : Sp Ω, pullback.fst Y.s (spMap β) (g w) = genPt 𝔐.ξ₀ := by
    intro w
    rw [← Scheme.Hom.comp_apply, hgf, hfn, Scheme.Hom.comp_apply]
    exact congrArg 𝔐.ξ₀ (Subsingleton.elim (α := PrimeSpectrum 𝔐.Ω₀) _ _)
  have hran : Set.range g ⊆ Set.range Y.jQ := by
    rintro _ ⟨w, rfl⟩
    exact HodgeBasic.mem_range_jQ Y hβ 𝔐.ξ₀ 𝔐.gen₀ g₀ hs hg _ (hall w)
  have := Y.jQ_open
  have hinj : Function.Injective 𝔐.emb := by
    intro s s' h
    refine HodgeBasic.labelEmb_injective c (RingHom.ext fun a => hcst ?_)
    exact congrArg (fun m : 𝓞 E →+* Ω => m a) h
  letI : Fintype (CMType H) := Fintype.ofFinite _
  have hcard : Fintype.card (CMType H ⊕ CMType H) = Module.finrank ℚ E := by
    rw [Fintype.card_of_bijective (HodgeBasic.labelHom_bijective H), Embeddings.card]
  have hint := GlobalTheory.T.eigenspace_decomposition_internal Ω 𝔐.Li E 𝔐.ρ (CMType H ⊕ CMType H) 𝔐.emb hinj hcard
  refine ⟨?_, ⟨IsOpenImmersion.lift Y.jQ g hran, ?_⟩, hchar, hinj, ?_, hint.submodule_iSup_eq_top,
    hint.submodule_iSupIndep, ?_⟩
  · refine HodgeBasic.mem_abLocus_of_map 𝔐.m.cart.1 ?_
    have hf : ∀ w : Sp Ω, pullback.fst Y.s (spMap β) (g w) = 𝔐.f (𝔐.ξ w) := by
      intro w
      rw [← Scheme.Hom.comp_apply, hgf, Scheme.Hom.comp_apply]
    have h2 : g (IsLocalRing.closedPoint Ω) ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]
      exact hran ⟨_, rfl⟩
    exact (congrArg (· ∈ abLocus Y.t.G) (hf (IsLocalRing.closedPoint Ω))).mp h2
  · rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, hgf]
  · intro s
    obtain ⟨U, hU, b, hb, hfr⟩ := 𝔐.vb s ⟨genPt 𝔐.ξ, specializes_rfl⟩ (Set.mem_univ _)
    have hli := (hfr ⟨genPt 𝔐.ξ, specializes_rfl⟩ (Set.mem_univ _) hU).1
    show Module.finrank Ω (eigSp 𝔐.ρ (𝔐.cst.comp (labelEmb c s))) = _
    rw [← hb, finrank_span_eq_card hli, Fintype.card_fin]
  · intro s a q
    refine HodgeBasic.mem_regAt_of_isIntegral 𝔐.tie.gen 𝔐.all 𝔐.normal q ?_
    exact (Algebra.IsIntegral.isIntegral (R := ℤ) a).map (𝔐.emb s).toIntAlgHom

end GlobalTheory.CompanionTheory.Ar
