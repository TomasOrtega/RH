import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteLocalBaseAtClosedPointGroupImports
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFactorClassicalPointOfLargeTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.Poinc.LabIndex

/- English proof (translation)
Substitute `h` using the available equality. Rewrite using `[Over.OverMorphism.ext hx]`.
-/
theorem pow_left_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b)
    (x : Over.mk a ⟶ G) (x' : Over.mk b ⟶ G) (hx : x.left = x'.left) (n : ℕ) :
    (x ^ n).left = (x' ^ n).left := by
  subst h
  rw [Over.OverMorphism.ext hx]

/- English proof (translation)
The claim follows from `h.hom_ext e ((cancel_mono g).1 (by rw [Category.assoc, Category.assoc, ← h.w, ← Category.assoc, e, Category.assoc]))`.
-/
theorem eq_of_comp_fst {P X Y Z T : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) [Mono g] {a b : T ⟶ P} (e : a ≫ fst = b ≫ fst) : a = b :=
  h.hom_ext e ((cancel_mono g).1 (by rw [Category.assoc, Category.assoc, ← h.w, ← Category.assoc, e, Category.assoc]))

/- English proof (translation)
Use `⟨fun w => ?_⟩` and prove the remaining obligations. Set `w0 : Sp K` to `genericPoint (Sp K)`. Establish `h1 : eg w0 ⤳ w`. Rewrite using `[← W.ι.isOpenEmbedding.isInducing.specializes_iff, heg w0]`. Conclude with `genericPoint_specializes _`.

Conclude with `closure_mono (Set.singleton_subset_iff.2 (Set.mem_range_self w0)) (specializes_iff_mem_closure.1 h1)`.
-/
theorem isDominant_of_generic {R : Type} [CommRing R] [IsDomain R] (W : (Sp R).Opens) {K : Type} [Field K]
    (eg : Sp K ⟶ W.toScheme) (heg : ∀ w, W.ι (eg w) = genericPoint (Sp R)) : IsDominant eg := by
  refine ⟨fun w => ?_⟩
  let w0 : Sp K := genericPoint (Sp K)
  have h1 : eg w0 ⤳ w := by
    rw [← W.ι.isOpenEmbedding.isInducing.specializes_iff, heg w0]
    exact genericPoint_specializes _
  exact closure_mono (Set.singleton_subset_iff.2 (Set.mem_range_self w0)) (specializes_iff_mem_closure.1 h1)

/- English proof (translation)
Establish `hw : w = genericPoint (Sp (AlgebraicClosure (FractionRing R)))` using `Subsingleton.elim _ _`. Substitute `hw` using the available equality. Rewrite using `[genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Use `show Ideal.comap ((algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))).comp (algebraMap R (FractionRing R))) ⊥ = ⊥`.

Conclude with `Ideal.comap_bot_of_injective _ ((algebraMap (FractionRing R) _).injective.comp (IsFractionRing.injective R (FractionRing R)))`.
-/
theorem spMap_generic (R : Type) [CommRing R] [IsDomain R] (w : Sp (AlgebraicClosure (FractionRing R))) :
    spMap ((algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))).comp (algebraMap R (FractionRing R))) w =
      genericPoint (Sp R) := by
  have hw : w = genericPoint (Sp (AlgebraicClosure (FractionRing R))) := Subsingleton.elim _ _
  subst hw
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  show Ideal.comap ((algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))).comp
    (algebraMap R (FractionRing R))) ⊥ = ⊥
  exact Ideal.comap_bot_of_injective _
    ((algebraMap (FractionRing R) _).injective.comp (IsFractionRing.injective R (FractionRing R)))

end GlobalTheory.Poinc.LabIndex

namespace GlobalTheory.Poinc.LabIndex

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem one_left_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b) :
    (1 : Over.mk a ⟶ G).left = (1 : Over.mk b ⟶ G).left := by
  subst h
  rfl

/- English proof (translation)
Introduce `o' Ω _ _ _ _ S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R _ _ _ j hBase hcpl G _ _ gm hgm D A U hLB hpsi s hs`. Use `set ξ : Sp R ⟶ M.Z := spMap j ≫ M.Z.fromSpecStalk x with hξdef`. Set `W : (Sp R).Opens` to `ξ ⁻¹ᵁ U₀`. Establish `hrW : Set.range (W.ι ≫ ξ) ⊆ Set.range U₀.ι`. Rewrite using `[Scheme.Opens.range_ι]`.

Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `w.2`. Set `w₀ : W.toScheme ⟶ U₀.toScheme` to `IsOpenImmersion.lift U₀.ι (W.ι ≫ ξ) hrW`. Establish `hw₀ : w₀ ≫ U₀.ι = W.ι ≫ ξ` using `IsOpenImmersion.lift_fac _ _ _`.

Establish `hsG : s.left ≫ G.hom = 𝟙 _` using `Over.w s`. Establish `hσw : (W.ι ≫ s.left ≫ gm) ≫ FinalForm.G.hom = w₀ ≫ U₀.ι`. Rewrite using `[hw₀, Category.assoc, Category.assoc, hgm.1.w, ← Category.assoc s.left, hsG, Category.id_comp]`. Set `σ : W.toScheme ⟶ pullback ρ.P.A.hom FinalForm.u₀` to `FinalForm.cart.1.lift _ _ hσw`. Establish `hσ1 : σ ≫ FinalForm.φ = W.ι ≫ s.left ≫ gm` using `FinalForm.cart.1.lift_fst _ _ _`.

Establish `hσ2 : σ ≫ pullback.snd ρ.P.A.hom FinalForm.u₀ = w₀` using `FinalForm.cart.1.lift_snd _ _ _`. Establish `key : (W : Set (Sp R)).Nonempty → ∃ b : S.Gam, σ ≫ pullback.fst ρ.P.A.hom FinalForm.u₀ = (w₀ ≫ FinalForm.u₀) ≫ (ρ.pt b).left`. Introduce `hWne`. Set `K` to `AlgebraicClosure (FractionRing R)`. Set `e0 : Sp K ⟶ Sp R` to `spMap ((algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R)))`.

Establish `he0 : ∀ w, e0 w = genericPoint (Sp R)` using `spMap_generic R`. Establish `hgW : genericPoint (Sp R) ∈ W`. Take `⟨w, hw⟩` from `hWne`. Conclude with `(genericPoint_specializes w).mem_open W.isOpen hw`. Establish `hr : Set.range e0 ⊆ Set.range W.ι`.

Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[he0]`. Conclude with `hgW`. Set `eg : Sp K ⟶ W.toScheme` to `IsOpenImmersion.lift W.ι e0 hr`.

Establish `heg : eg ≫ W.ι = e0` using `IsOpenImmersion.lift_fac _ _ _`. Use `haveI : IsDominant eg := isDominant_of_generic W eg (fun w => by rw [← Scheme.Hom.comp_apply, heg, he0])`. Use `haveI : IsSeparated ρ.P.A.hom := by haveI := ρ.P.isAb.proper; infer_instance`. Set `T : Over (Sp R)` to `Over.mk e0`. Establish `htu : (toUnit T).left = e0` using `(Category.comp_id _).symm.trans (Over.w (toUnit T))`.

Set `x1 : T ⟶ G` to `toUnit T ≫ s`. Establish `hx1 : x1 ^ (S.r * S.N) = 1` using `by show ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom (toUnit T) s ^ (S.r * S.N) = 1`. Rewrite using `[← map_pow, hs, map_one]`. Set `x2` to `pushHom hgm T x1`. Establish `hx2 : x2 ^ (S.r * S.N) = 1` using `by show pushHom hgm T x1 ^ (S.r * S.N) = 1`.

Rewrite using `[← map_pow, hx1, map_one]`. Set `T' : Over U₀.toScheme` to `Over.mk (eg ≫ w₀)`. Set `x3 : T' ⟶ (Over.pullback FinalForm.u₀).obj ρ.P.A` to `Over.homMk (eg ≫ σ) (by show (eg ≫ σ) ≫ pullback.snd _ _ = eg ≫ w₀`. Rewrite using `[Category.assoc, hσ2])`. Establish `hbase : T'.hom ≫ U₀.ι = T.hom ≫ ξ` using `by show (eg ≫ w₀) ≫ U₀.ι = e0 ≫ ξ`.

Rewrite using `[Category.assoc, hw₀, ← Category.assoc, heg]`. Establish `hx3 : x3 ^ (S.r * S.N) = 1`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `eq_of_comp_fst FinalForm.cart.1` to reduce the goal to its premises. Establish `a1 : ((pushHom FinalForm.cart T') (x3 ^ (S.r * S.N))).left = ((pushHom FinalForm.cart T' x3) ^ (S.r * S.N)).left`.

Rewrite using `[map_pow]`. Establish `a2 : ((pushHom FinalForm.cart T') 1).left = (1 : Over.mk (T'.hom ≫ U₀.ι) ⟶ FinalForm.G).left`. Rewrite using `[map_one]`. Establish `a3` using `pow_left_congr hbase (pushHom FinalForm.cart T' x3) x2 (by show (eg ≫ σ) ≫ FinalForm.φ = (toUnit T ≫ s).left ≫ gm`. Rewrite using `[Over.comp_left, htu, Category.assoc, hσ1, ← Category.assoc eg, heg]`.

Simplify using `only [Category.assoc]) (S.r * S.N)`. Establish `a4` using `one_left_congr (G := FinalForm.G) hbase`. Use `a1.trans (a3.trans ?_)` and prove the remaining obligations. Rewrite using `[hx2, ← a4, ← a2]`. Both sides reduce to the same expression.

Set `x4` to `pushHom (isGrpPullback_pullback ρ.P.A FinalForm.u₀) T' x3`. Establish `hx4 : x4 ^ (S.r * S.N) = 1` using `by show pushHom (isGrpPullback_pullback ρ.P.A FinalForm.u₀) T' x3 ^ (S.r * S.N) = 1`. Rewrite using `[← map_pow, hx3, map_one]`. Take `⟨b, hb, -⟩` from `ρ.pt_bij K (T'.hom ≫ FinalForm.u₀) x4 hx4`. Use `⟨b, ext_of_isDominant_of_isSeparated ρ.P.A.hom ?_ eg ?_⟩` and prove the remaining obligations.

Establish `e1 : (ρ.pt b).left ≫ ρ.P.A.hom = 𝟙 _` using `Over.w (ρ.pt b)`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, hσ2, Category.assoc, e1]`. Conclude with `(Category.comp_id _).symm`. Establish `e2` using `congrArg (fun z => z.left) hb`. Simplify using `only [Over.comp_left, Over.homMk_left] at e2`.

Rewrite using `[← Category.assoc, ← Category.assoc]`. Conclude with `(e2.trans rfl).symm`. Distinguish the cases in `hWne : (W : Set (Sp R)).Nonempty`. Take `⟨b, hb⟩` from `key hWne`. Use `⟨b, fun p _ y ev hCen hev y₀ hAt t ht => ?_⟩` and prove the remaining obligations.

Set `c : Sp (PadicAlgCl p) ⟶ Sp R` to `spMap ((OO p).subtype.comp ev)`. Establish `hc : c ≫ ξ = gPt p ≫ y`. Rewrite using `[← hev]`. Simplify using `only [c, gPt, spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Establish `hcW : Set.range c ⊆ Set.range W.ι`.

Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨w, rfl⟩`. Use `show ξ (c w) ∈ U₀`. Rewrite using `[← Scheme.Hom.comp_apply, hc]`. Conclude with `hCen.2 ⟨w, rfl⟩`.

Set `c' : Sp (PadicAlgCl p) ⟶ W.toScheme` to `IsOpenImmersion.lift W.ι c hcW`. Establish `hc' : c' ≫ W.ι = c` using `IsOpenImmersion.lift_fac _ _ _`. Establish `htc : t = c' ≫ σ` using `eq_of_comp_fst FinalForm.cart.1 (by`. Rewrite using `[ht, Category.assoc, hσ1, ← Category.assoc c', hc'])`. Establish `hq : (c' ≫ w₀) ≫ U₀.ι = gPt p ≫ y`.

Rewrite using `[Category.assoc, hw₀, ← Category.assoc, hc', hc]`. Establish `hu : (c' ≫ w₀) ≫ FinalForm.u₀ = spMap y₀`. Rewrite using `[← Spec.map_preimage ((c' ≫ w₀) ≫ FinalForm.u₀)]`. Use `congr 1`. Use extensionality with `a`.

Rewrite using `[GlobalTheory.ZH.preimage_comp_eq_val M U₀ hAdm.1.ne S.R FinalForm.u₀ FinalForm.u₀_gen, hq, ← hAt a]`. Both sides reduce to the same expression. Rewrite using `[htc, Category.assoc, hb, ← Category.assoc, ← Category.assoc, hu]`. Use `⟨0, fun p _ y ev hCen hev y₀ hAt t ht => absurd ?_ hWne⟩` and prove the remaining obligations. Set `c : Sp (PadicAlgCl p) ⟶ Sp R` to `spMap ((OO p).subtype.comp ev)`.

Establish `hc : c ≫ ξ = gPt p ≫ y`. Rewrite using `[← hev]`. Simplify using `only [c, gPt, spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `⟨c (genericPoint _), ?_⟩` and prove the remaining obligations. Use `show ξ (c (genericPoint _)) ∈ U₀`.

Rewrite using `[← Scheme.Hom.comp_apply, hc]`. Conclude with `hCen.2 ⟨_, rfl⟩`.
-/
theorem torsion_section_label : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ s : 𝟙_ (Over (Sp R)) ⟶ G, s ^ (S.r * S.N) = 1 → ∃ b : S.Gam, ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ → ∀ t : Sp (PadicAlgCl p) ⟶ pullback ρ.P.A.hom FinalForm.u₀, t ≫ FinalForm.φ = spMap ((OO p).subtype.comp ev) ≫ s.left ≫ gm → t ≫ pullback.fst _ _ = spMap y₀ ≫ (ρ.pt b).left := by
  intro o' Ω _ _ _ _ S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R _ _ _ j hBase hcpl G _ _ gm hgm D A U hLB hpsi s hs
  set ξ : Sp R ⟶ M.Z := spMap j ≫ M.Z.fromSpecStalk x with hξdef
  let W : (Sp R).Opens := ξ ⁻¹ᵁ U₀
  have hrW : Set.range (W.ι ≫ ξ) ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact w.2
  let w₀ : W.toScheme ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι (W.ι ≫ ξ) hrW
  have hw₀ : w₀ ≫ U₀.ι = W.ι ≫ ξ := IsOpenImmersion.lift_fac _ _ _
  have hsG : s.left ≫ G.hom = 𝟙 _ := Over.w s
  have hσw : (W.ι ≫ s.left ≫ gm) ≫ FinalForm.G.hom = w₀ ≫ U₀.ι := by
    rw [hw₀, Category.assoc, Category.assoc, hgm.1.w, ← Category.assoc s.left, hsG, Category.id_comp]
  let σ : W.toScheme ⟶ pullback ρ.P.A.hom FinalForm.u₀ := FinalForm.cart.1.lift _ _ hσw
  have hσ1 : σ ≫ FinalForm.φ = W.ι ≫ s.left ≫ gm := FinalForm.cart.1.lift_fst _ _ _
  have hσ2 : σ ≫ pullback.snd ρ.P.A.hom FinalForm.u₀ = w₀ := FinalForm.cart.1.lift_snd _ _ _
  have key : (W : Set (Sp R)).Nonempty →
      ∃ b : S.Gam, σ ≫ pullback.fst ρ.P.A.hom FinalForm.u₀ = (w₀ ≫ FinalForm.u₀) ≫ (ρ.pt b).left := by
    intro hWne
    let K := AlgebraicClosure (FractionRing R)
    let e0 : Sp K ⟶ Sp R := spMap ((algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R)))
    have he0 : ∀ w, e0 w = genericPoint (Sp R) := spMap_generic R
    have hgW : genericPoint (Sp R) ∈ W := by
      obtain ⟨w, hw⟩ := hWne
      exact (genericPoint_specializes w).mem_open W.isOpen hw
    have hr : Set.range e0 ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      rw [he0]
      exact hgW
    let eg : Sp K ⟶ W.toScheme := IsOpenImmersion.lift W.ι e0 hr
    have heg : eg ≫ W.ι = e0 := IsOpenImmersion.lift_fac _ _ _
    haveI : IsDominant eg := isDominant_of_generic W eg (fun w => by rw [← Scheme.Hom.comp_apply, heg, he0])
    haveI : IsSeparated ρ.P.A.hom := by haveI := ρ.P.isAb.proper; infer_instance
    let T : Over (Sp R) := Over.mk e0
    have htu : (toUnit T).left = e0 := (Category.comp_id _).symm.trans (Over.w (toUnit T))
    let x1 : T ⟶ G := toUnit T ≫ s
    have hx1 : x1 ^ (S.r * S.N) = 1 := by
      show ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom (toUnit T) s ^ (S.r * S.N) = 1
      rw [← map_pow, hs, map_one]
    let x2 := pushHom hgm T x1
    have hx2 : x2 ^ (S.r * S.N) = 1 := by
      show pushHom hgm T x1 ^ (S.r * S.N) = 1
      rw [← map_pow, hx1, map_one]
    let T' : Over U₀.toScheme := Over.mk (eg ≫ w₀)
    let x3 : T' ⟶ (Over.pullback FinalForm.u₀).obj ρ.P.A := Over.homMk (eg ≫ σ) (by
      show (eg ≫ σ) ≫ pullback.snd _ _ = eg ≫ w₀
      rw [Category.assoc, hσ2])
    have hbase : T'.hom ≫ U₀.ι = T.hom ≫ ξ := by
      show (eg ≫ w₀) ≫ U₀.ι = e0 ≫ ξ
      rw [Category.assoc, hw₀, ← Category.assoc, heg]
    have hx3 : x3 ^ (S.r * S.N) = 1 := by
      apply Over.OverMorphism.ext
      apply eq_of_comp_fst FinalForm.cart.1
      have a1 : ((pushHom FinalForm.cart T') (x3 ^ (S.r * S.N))).left = ((pushHom FinalForm.cart T' x3) ^ (S.r * S.N)).left := by
        rw [map_pow]
      have a2 : ((pushHom FinalForm.cart T') 1).left = (1 : Over.mk (T'.hom ≫ U₀.ι) ⟶ FinalForm.G).left := by
        rw [map_one]
      have a3 := pow_left_congr hbase (pushHom FinalForm.cart T' x3) x2 (by
        show (eg ≫ σ) ≫ FinalForm.φ = (toUnit T ≫ s).left ≫ gm
        rw [Over.comp_left, htu, Category.assoc, hσ1, ← Category.assoc eg, heg]
        simp only [Category.assoc]) (S.r * S.N)
      have a4 := one_left_congr (G := FinalForm.G) hbase
      refine a1.trans (a3.trans ?_)
      rw [hx2, ← a4, ← a2]
      rfl
    let x4 := pushHom (isGrpPullback_pullback ρ.P.A FinalForm.u₀) T' x3
    have hx4 : x4 ^ (S.r * S.N) = 1 := by
      show pushHom (isGrpPullback_pullback ρ.P.A FinalForm.u₀) T' x3 ^ (S.r * S.N) = 1
      rw [← map_pow, hx3, map_one]
    obtain ⟨b, hb, -⟩ := ρ.pt_bij K (T'.hom ≫ FinalForm.u₀) x4 hx4
    refine ⟨b, ext_of_isDominant_of_isSeparated ρ.P.A.hom ?_ eg ?_⟩
    · have e1 : (ρ.pt b).left ≫ ρ.P.A.hom = 𝟙 _ := Over.w (ρ.pt b)
      rw [Category.assoc, pullback.condition, ← Category.assoc, hσ2, Category.assoc, e1]
      exact (Category.comp_id _).symm
    · have e2 := congrArg (fun z => z.left) hb
      simp only [Over.comp_left, Over.homMk_left] at e2
      rw [← Category.assoc, ← Category.assoc]
      exact (e2.trans rfl).symm
  by_cases hWne : (W : Set (Sp R)).Nonempty
  · obtain ⟨b, hb⟩ := key hWne
    refine ⟨b, fun p _ y ev hCen hev y₀ hAt t ht => ?_⟩
    let c : Sp (PadicAlgCl p) ⟶ Sp R := spMap ((OO p).subtype.comp ev)
    have hc : c ≫ ξ = gPt p ≫ y := by
      rw [← hev]
      simp only [c, gPt, spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hcW : Set.range c ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      show ξ (c w) ∈ U₀
      rw [← Scheme.Hom.comp_apply, hc]
      exact hCen.2 ⟨w, rfl⟩
    let c' : Sp (PadicAlgCl p) ⟶ W.toScheme := IsOpenImmersion.lift W.ι c hcW
    have hc' : c' ≫ W.ι = c := IsOpenImmersion.lift_fac _ _ _
    have htc : t = c' ≫ σ := eq_of_comp_fst FinalForm.cart.1 (by
      rw [ht, Category.assoc, hσ1, ← Category.assoc c', hc'])
    have hq : (c' ≫ w₀) ≫ U₀.ι = gPt p ≫ y := by
      rw [Category.assoc, hw₀, ← Category.assoc, hc', hc]
    have hu : (c' ≫ w₀) ≫ FinalForm.u₀ = spMap y₀ := by
      rw [← Spec.map_preimage ((c' ≫ w₀) ≫ FinalForm.u₀)]
      congr 1
      ext a
      rw [GlobalTheory.ZH.preimage_comp_eq_val M U₀ hAdm.1.ne S.R FinalForm.u₀ FinalForm.u₀_gen, hq, ← hAt a]
      rfl
    rw [htc, Category.assoc, hb, ← Category.assoc, ← Category.assoc, hu]
  · refine ⟨0, fun p _ y ev hCen hev y₀ hAt t ht => absurd ?_ hWne⟩
    let c : Sp (PadicAlgCl p) ⟶ Sp R := spMap ((OO p).subtype.comp ev)
    have hc : c ≫ ξ = gPt p ≫ y := by
      rw [← hev]
      simp only [c, gPt, spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    refine ⟨c (genericPoint _), ?_⟩
    show ξ (c (genericPoint _)) ∈ U₀
    rw [← Scheme.Hom.comp_apply, hc]
    exact hCen.2 ⟨_, rfl⟩

end GlobalTheory.Poinc.LabIndex
