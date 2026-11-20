import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramSub
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointFixedOfChartValuesFixedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointCharacterValuesFixedLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiValueIsUnitOfPsiUnitOnLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientPointCharacterValuePowIsUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteKTorsionAbelianPartAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientPointsFiniteRepresentativesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedDvrAdjoiningUnitRootsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.UnramCharVals

attribute [local instance] GlobalTheory.TorusExt.gtGroup

open ReciprocityTheory.ChartRestriction.G.DVR in

/- English proof (translation)
Introduce `R _ _ D F _ _ t k h1 hk J hJ χ`. Use `letI := GlobalTheory.TorusExt.gtGroup D F`. Establish `C : IsCub (th D (T` using `TF (R := R) F) (closedPoint F) J) := isCub_cubV D.cub hJ`. Establish `key : ∀ i : ℕ, GlobalTheory.TorusExt.charVal (i • t) χ (closedPoint F) J = GlobalTheory.TorusExt.charVal t χ (closedPoint F) J ^ i`. Introduce `i`.

Proceed by induction on `i with`. Consider the case `zero => rw [zero_nsmul, GlobalTheory.TorusExt.zero_val χ hJ, pow_zero]`. Consider the case `succ i ih`. Establish `e` using `GlobalTheory.TorusExt.add_val (i • t) t χ hJ`. Rewrite `e` using `[h1, C.face₃, _root_.mul_one, ih]`.

Rewrite using `[succ_nsmul, e, pow_succ]`. Establish `e` using `key k`. Rewrite `e` using `[hk, GlobalTheory.TorusExt.zero_val χ hJ]`. Rewrite using `[← Units.val_pow_eq_pow_val, ← map_pow, ← e, map_one, Units.val_one]`.
-/
theorem tor_charVal_pow : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (t : GtPtF D F) (k : ℕ), t.b = 1 → (letI := GlobalTheory.TorusExt.gtGroup D F; k • t = 0) → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J → ∀ χ, (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal t χ (closedPoint F) J) : F) ^ k = 1 := by
  intro R _ _ D F _ _ t k h1 hk J hJ χ
  letI := GlobalTheory.TorusExt.gtGroup D F
  have C : IsCub (th D (T := TF (R := R) F) (closedPoint F) J) := isCub_cubV D.cub hJ
  have key : ∀ i : ℕ, GlobalTheory.TorusExt.charVal (i • t) χ (closedPoint F) J = GlobalTheory.TorusExt.charVal t χ (closedPoint F) J ^ i := by
    intro i
    induction i with
    | zero => rw [zero_nsmul, GlobalTheory.TorusExt.zero_val χ hJ, pow_zero]
    | succ i ih =>
      have e := GlobalTheory.TorusExt.add_val (i • t) t χ hJ
      rw [h1, C.face₃, _root_.mul_one, ih] at e
      rw [succ_nsmul, e, pow_succ]
  have e := key k
  rw [hk, GlobalTheory.TorusExt.zero_val χ hJ] at e
  rw [← Units.val_pow_eq_pow_val, ← map_pow, ← e, map_one, Units.val_one]

/- English proof (translation)
Introduce `R _ _ _ _ D W hW V _ _ _ φ hV _ hcl _ hc k hk T₁ hT₁ hbs`. Establish `hB` using `D.tau_bimult`. Use `haveI : IsDiscreteValuationRing V := hV.1`. Take `⟨hdvr, f, hf, hirr⟩` from `id hT₁`. Use `haveI := hdvr`.

Set `φ₁ : R →+* T₁` to `f.comp φ`. Establish `hφ₁ : ∀ r, (φ₁ r : AlgebraicClosure (FractionRing V)) = algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r)` using `fun r => (hf _).trans (hc r).symm`. Establish `hloc : IsLocalHom f` using `⟨fun v hv => by`. Assume the negation of the conclusion as `h`. Establish `hv0 : v ≠ 0` using `by rintro rfl; rw [map_zero] at hv; exact not_isUnit_zero hv`.

Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible V`. Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hv0 hπ`. Consider the cases of `n with`. Consider the case `zero => exact h (by simp)`. Consider the case `succ n`.

Rewrite `hv` using `[map_mul, map_pow, pow_succ]`. Conclude with `(hirr π hπ).not_isUnit (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right hv))⟩`. Establish `hcl' : spMap φ₁ (closedPoint T₁) ∈ W`. Establish `e : spMap φ₁ = spMap f ≫ spMap φ` using `by show Spec.map _ = Spec.map _ ≫ Spec.map _`. Rewrite using `[← Spec.map_comp]`.

Both sides reduce to the same expression. Establish `e' : spMap f (closedPoint T₁) = closedPoint V` using `PrimeSpectrum.ext (Ideal.ext fun r => ⟨fun h e => h (e.map f), fun h e => h (isUnit_of_map_unit f r e)⟩)`. Rewrite using `[e]`. Use `show (spMap φ) ((spMap f) (closedPoint T₁)) ∈ W`. Rewrite using `[e']`.

Conclude with `hcl`. Use `choose J₀ h₀ using fun x : D.toPre.P.A.left => exists_chart D.toPre.P.isLB x`. Use `D.toPre.P.isAb.proper` as an intermediate fact. Establish `: D.toPre.P.A.left.IsSeparated` using `⟨by rw [← terminal.comp_from D.toPre.P.A.hom]; infer_instance⟩`. Take `⟨J, hJ, eJ⟩` from `GlobalTheory.UnramTorsion.exists_good_ext D.toPre.P.isLB T₁.subtype Subtype.val_injective J₀ h₀`.

Establish `hψ` using `fun χ => GlobalTheory.T.psiValue_isUnit_of_psiUnitOn_localRing R D.toPre W χ (hW χ) _ T₁ φ₁ hφ₁ hcl' J₀ h₀ J eJ`. Establish `hbw : ∀ (x : TF (R` using `R) (AlgebraicClosure (FractionRing V)) ⟶ D.toPre.P.A) (b : Sp T₁ ⟶ D.toPre.P.A.left), spMap T₁.subtype ≫ b = x.left → b ≫ D.toPre.P.A.hom = spMap φ₁ := by`. Introduce `x b hb`. Establish `hd : IsDominant (spMap T₁.subtype)`. Prove the components needed by the constructor for the conclusion.

Conclude with `(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]; exact bot_le)`. Use `ext_of_isDominant (spMap T₁.subtype) ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, hb, Over.w x]`. Use `show jFK (R := R) (AlgebraicClosure (FractionRing V)) ≫ jK R = spMap T₁.subtype ≫ spMap φ₁`. Rewrite using `[jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]`.

Use `congr 2`. Conclude with `(RingHom.ext hφ₁).symm`. Use `choose bb hbb using hbs`. Establish `hk0 : k ≠ 0` using `by rintro rfl; exact not_isUnit_zero (M₀ := V) (by simpa using hk)`. Establish `fin` using `GlobalTheory.T.finite_kTorsion_abelianPart_algClosed R D.toPre (AlgebraicClosure (FractionRing V)) k (Nat.one_le_iff_ne_zero.2 hk0)`.

Take `⟨Rep, hRepf, hRep⟩` from `GlobalTheory.T.quotientPoints_finite_representatives R D.toPre hB (AlgebraicClosure (FractionRing V)) k hk0 fin`. Take `⟨s, hs⟩` from `Module.Finite.fg_top (R := ℤ) (M := D.toPre.X)`. Establish `hS : AddSubgroup.closure (s : Set D.toPre.X) = ⊤`. Rewrite using `[← Submodule.span_int_eq_addSubgroupClosure, hs]`. Both sides reduce to the same expression.

Use `choose uu huu using fun (p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k) χ => GlobalTheory.T.quotientPoint_characterValue_pow_isUnit R D.toPre hB _ T₁ φ₁ hφ₁ J₀ h₀ J hJ eJ hψ k p (bb p) (hbb p) (hbw _ _ (hbb p)) χ`. Set `U : Set T₁ˣ` to `insert 1 ((fun pc : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k × D.toPre.X => uu pc.1 pc.2) '' (Rep ×ˢ (s : Set D.toPre.X)))`. Establish `hU : U.Finite` using `((hRepf.prod s.finite_toSet).image _).insert 1`. Establish `hkT : IsUnit (k : T₁)` using `by simpa using hk.map f`. Take `⟨T', hT', hroot⟩` from `GlobalTheory.T.exists_unramified_dvr_adjoining_unit_roots _ T₁ k hkT U hU`.

Use `⟨T', hT', fun σ hσT' p q hq => ?_⟩` and prove the remaining obligations. Establish `hσT : ∀ t ∈ T₁, σ t = t` using `fun t ht => hσT' t (hT'.le ht)`. Establish `hσ : σ.toRingHom.comp (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V))) = algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V))` using `IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => by show σ (algebraMap (FractionRing R) _ (algebraMap R _ r)) = algebraMap (FractionRing R) _ (algebraMap R _ r)`. Rewrite using `[← hφ₁]`. Conclude with `hσT _ (φ₁ r).2)`.

Establish `hsub : spMap σ.toRingHom ≫ spMap T₁.subtype = spMap T₁.subtype` using `by show Spec.map _ ≫ Spec.map _ = Spec.map _`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Use extensionality with `t`. Conclude with `hσT t t.2`.

Establish `hfix : ∀ p' ∈ Rep, GlobalTheory.TorusExt.gtExt D.toPre σ.toRingHom hσ p'.g = p'.g`. Introduce `p' hp'`. Use `GlobalTheory.T.torusExtensionPoint_fixed_of_chartValues_fixed R D.toPre _ σ.toRingHom hσ p'.g ?_ J hJ ?_` and prove the remaining obligations. Rewrite using `[← hbb p', ← Category.assoc, hsub]`. Conclude with `GlobalTheory.T.torusExtensionPoint_characterValues_fixed_local R D.toPre _ T₁ φ₁ hφ₁ J₀ h₀ J hJ eJ σ.toRingHom hσT p'.g (bb p') (hbb p') (hbw _ _ (hbb p')) _ hS (fun χ hχ => hσT' _ (hroot _ ⟨uu p' χ, Set.mem_insert_of_mem _ ⟨(p', χ), ⟨hp', hχ⟩, rfl⟩, huu p' χ⟩))`.

Establish `hfixt : ∀ t : GtPtF D.toPre (AlgebraicClosure (FractionRing V)), t.b = 1 → k • t = 0 → GlobalTheory.TorusExt.gtExt D.toPre σ.toRingHom hσ t = t`. Introduce `t h1 hkt`. Use `GlobalTheory.T.torusExtensionPoint_fixed_of_chartValues_fixed R D.toPre _ σ.toRingHom hσ t ?_ J hJ (fun χ => hσT' _ (hroot _ ⟨1, Set.mem_insert _ _, ?_⟩))` and prove the remaining obligations. Rewrite using `[h1]`. Conclude with `congrArg (fun q => q.left) (MonObj.comp_one (GlobalTheory.TorusExt.extMap (R := R) σ.toRingHom hσ) : GlobalTheory.TorusExt.extMap (R := R) σ.toRingHom hσ ≫ (1 : TF (R := R) _ ⟶ D.toPre.P.A) = 1)`.

Rewrite using `[tor_charVal_pow R D.toPre _ t k h1 hkt J hJ χ]`. Simplify using the standard rewrite rules. Take `⟨p', hp', z, t, h1, hkt, hpg⟩` from `hRep p`. Establish `hg : GlobalTheory.TorusExt.gtExt D.toPre σ.toRingHom hσ p.g = p.g`. Rewrite using `[hpg, map_add, map_add, hfix p' hp', GlobalTheory.TorusExt.gtExt_iota, hfixt t h1 hkt]`.

Establish `hq'` using `(GlobalTheory.TorusExt.qkExt_iff hB σ.toRingHom hσ p q).1 hq`. Use `(GlobalTheory.TorusExt.equiv_iff hB p q).2 ⟨0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hq', smul_zero, add_zero]`. Both sides reduce to the same expression. Rewrite using `[hq', map_zero, add_zero]`.

Conclude with `hg`.
-/
theorem qk_fixed_of_unram : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (W : (Sp R).Opens), (∀ y, PsiUnitOn D.toPre y W) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V), GlobalTheory.LN.CDvr V → Function.Injective φ → spMap φ (closedPoint V) ∈ W → ∀ [Algebra (FractionRing R) (AlgebraicClosure (FractionRing V))], (∀ r, algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ (φ r))) → ∀ k : ℕ, IsUnit (k : V) → ∀ T₁ : Subring (AlgebraicClosure (FractionRing V)), GlobalTheory.UnramSub ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp (algebraMap V (FractionRing V))) T₁ → (∀ p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k, ∃ b : Sp T₁ ⟶ D.toPre.P.A.left, spMap T₁.subtype ≫ b = p.g.b.left) → ∃ T' : Subring (AlgebraicClosure (FractionRing V)), GlobalTheory.UnramSub T₁.subtype T' ∧ ∀ σ : (AlgebraicClosure (FractionRing V)) ≃+* (AlgebraicClosure (FractionRing V)), (∀ z ∈ T', σ z = z) → ∀ p q : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k, QkExt σ.toRingHom p q → QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing V)) p q := by
  intro R _ _ _ _ D W hW V _ _ _ φ hV _ hcl _ hc k hk T₁ hT₁ hbs
  have hB := D.tau_bimult
  haveI : IsDiscreteValuationRing V := hV.1
  obtain ⟨hdvr, f, hf, hirr⟩ := id hT₁
  haveI := hdvr
  let φ₁ : R →+* T₁ := f.comp φ
  have hφ₁ : ∀ r, (φ₁ r : AlgebraicClosure (FractionRing V)) =
      algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r) := fun r =>
    (hf _).trans (hc r).symm
  have hloc : IsLocalHom f := ⟨fun v hv => by
    by_contra h
    have hv0 : v ≠ 0 := by rintro rfl; rw [map_zero] at hv; exact not_isUnit_zero hv
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hv0 hπ
    cases n with
    | zero => exact h (by simp)
    | succ n =>
      rw [map_mul, map_pow, pow_succ] at hv
      exact (hirr π hπ).not_isUnit (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right hv))⟩
  have hcl' : spMap φ₁ (closedPoint T₁) ∈ W := by
    have e : spMap φ₁ = spMap f ≫ spMap φ := by
      show Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp]; rfl
    have e' : spMap f (closedPoint T₁) = closedPoint V := PrimeSpectrum.ext (Ideal.ext fun r =>
      ⟨fun h e => h (e.map f), fun h e => h (isUnit_of_map_unit f r e)⟩)
    rw [e]
    show (spMap φ) ((spMap f) (closedPoint T₁)) ∈ W
    rw [e']
    exact hcl
  choose J₀ h₀ using fun x : D.toPre.P.A.left => exists_chart D.toPre.P.isLB x
  have := D.toPre.P.isAb.proper
  have : D.toPre.P.A.left.IsSeparated := ⟨by rw [← terminal.comp_from D.toPre.P.A.hom]; infer_instance⟩
  obtain ⟨J, hJ, eJ⟩ := GlobalTheory.UnramTorsion.exists_good_ext D.toPre.P.isLB T₁.subtype Subtype.val_injective J₀ h₀
  have hψ := fun χ => GlobalTheory.T.psiValue_isUnit_of_psiUnitOn_localRing R D.toPre W χ (hW χ) _ T₁ φ₁ hφ₁ hcl' J₀ h₀ J eJ
  have hbw : ∀ (x : TF (R := R) (AlgebraicClosure (FractionRing V)) ⟶ D.toPre.P.A) (b : Sp T₁ ⟶ D.toPre.P.A.left),
      spMap T₁.subtype ≫ b = x.left → b ≫ D.toPre.P.A.hom = spMap φ₁ := by
    intro x b hb
    have hd : IsDominant (spMap T₁.subtype) := by
      constructor
      exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
        (by rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]; exact bot_le)
    refine ext_of_isDominant (spMap T₁.subtype) ?_
    rw [← Category.assoc, hb, Over.w x]
    show jFK (R := R) (AlgebraicClosure (FractionRing V)) ≫ jK R = spMap T₁.subtype ≫ spMap φ₁
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (RingHom.ext hφ₁).symm
  choose bb hbb using hbs
  have hk0 : k ≠ 0 := by rintro rfl; exact not_isUnit_zero (M₀ := V) (by simpa using hk)
  have fin := GlobalTheory.T.finite_kTorsion_abelianPart_algClosed R D.toPre (AlgebraicClosure (FractionRing V)) k (Nat.one_le_iff_ne_zero.2 hk0)
  obtain ⟨Rep, hRepf, hRep⟩ := GlobalTheory.T.quotientPoints_finite_representatives R D.toPre hB (AlgebraicClosure (FractionRing V)) k hk0 fin
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := D.toPre.X)
  have hS : AddSubgroup.closure (s : Set D.toPre.X) = ⊤ := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, hs]; rfl
  choose uu huu using fun (p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k) χ =>
    GlobalTheory.T.quotientPoint_characterValue_pow_isUnit R D.toPre hB _ T₁ φ₁ hφ₁ J₀ h₀ J hJ eJ hψ k p (bb p) (hbb p) (hbw _ _ (hbb p)) χ
  let U : Set T₁ˣ := insert 1 ((fun pc : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k × D.toPre.X => uu pc.1 pc.2) '' (Rep ×ˢ (s : Set D.toPre.X)))
  have hU : U.Finite := ((hRepf.prod s.finite_toSet).image _).insert 1
  have hkT : IsUnit (k : T₁) := by simpa using hk.map f
  obtain ⟨T', hT', hroot⟩ := GlobalTheory.T.exists_unramified_dvr_adjoining_unit_roots _ T₁ k hkT U hU
  refine ⟨T', hT', fun σ hσT' p q hq => ?_⟩
  have hσT : ∀ t ∈ T₁, σ t = t := fun t ht => hσT' t (hT'.le ht)
  have hσ : σ.toRingHom.comp (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V))) =
      algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => by
      show σ (algebraMap (FractionRing R) _ (algebraMap R _ r)) = algebraMap (FractionRing R) _ (algebraMap R _ r)
      rw [← hφ₁]; exact hσT _ (φ₁ r).2)
  have hsub : spMap σ.toRingHom ≫ spMap T₁.subtype = spMap T₁.subtype := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext t
    exact hσT t t.2
  have hfix : ∀ p' ∈ Rep, GlobalTheory.TorusExt.gtExt D.toPre σ.toRingHom hσ p'.g = p'.g := by
    intro p' hp'
    refine GlobalTheory.T.torusExtensionPoint_fixed_of_chartValues_fixed R D.toPre _ σ.toRingHom hσ p'.g ?_ J hJ ?_
    · rw [← hbb p', ← Category.assoc, hsub]
    · exact GlobalTheory.T.torusExtensionPoint_characterValues_fixed_local R D.toPre _ T₁ φ₁ hφ₁ J₀ h₀ J hJ eJ σ.toRingHom hσT p'.g (bb p') (hbb p') (hbw _ _ (hbb p')) _ hS
        (fun χ hχ => hσT' _ (hroot _ ⟨uu p' χ, Set.mem_insert_of_mem _ ⟨(p', χ), ⟨hp', hχ⟩, rfl⟩, huu p' χ⟩))
  have hfixt : ∀ t : GtPtF D.toPre (AlgebraicClosure (FractionRing V)), t.b = 1 → k • t = 0 →
      GlobalTheory.TorusExt.gtExt D.toPre σ.toRingHom hσ t = t := by
    intro t h1 hkt
    refine GlobalTheory.T.torusExtensionPoint_fixed_of_chartValues_fixed R D.toPre _ σ.toRingHom hσ t ?_ J hJ (fun χ => hσT' _ (hroot _ ⟨1, Set.mem_insert _ _, ?_⟩))
    · rw [h1]
      exact congrArg (fun q => q.left) (MonObj.comp_one (GlobalTheory.TorusExt.extMap (R := R) σ.toRingHom hσ) :
        GlobalTheory.TorusExt.extMap (R := R) σ.toRingHom hσ ≫ (1 : TF (R := R) _ ⟶ D.toPre.P.A) = 1)
    · rw [tor_charVal_pow R D.toPre _ t k h1 hkt J hJ χ]; simp
  obtain ⟨p', hp', z, t, h1, hkt, hpg⟩ := hRep p
  have hg : GlobalTheory.TorusExt.gtExt D.toPre σ.toRingHom hσ p.g = p.g := by
    rw [hpg, map_add, map_add, hfix p' hp', GlobalTheory.TorusExt.gtExt_iota, hfixt t h1 hkt]
  have hq' := (GlobalTheory.TorusExt.qkExt_iff hB σ.toRingHom hσ p q).1 hq
  refine (GlobalTheory.TorusExt.equiv_iff hB p q).2 ⟨0, ?_, ?_⟩
  · rw [hq', smul_zero, add_zero]; rfl
  · rw [hq', map_zero, add_zero]; exact hg

end GlobalTheory.UnramCharVals
