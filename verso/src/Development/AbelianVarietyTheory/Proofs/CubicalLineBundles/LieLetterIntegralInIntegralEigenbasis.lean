import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFramesDifferByUnit
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralOfLocalGenerator
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieBasisLocalModelStatement

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.LetterInt

open GlobalTheory.IntLie

/- English proof (translation)
Set `δ : Over.mk (g ≫ T'.hom) ⟶ T'` to `Over.homMk g rfl`. Establish `h1` using `prod_push h (Over.mk (g ≫ T'.hom)) T (𝟙 _) ((Category.id_comp _).trans (hg.symm.trans (Category.assoc _ _ _).symm)) (fun j => δ ≫ a j) a₀ (fun j => (Category.assoc _ _ _).trans ((ha j).symm.trans (Category.id_comp _).symm))`. Establish `h2 : ∀ {m : ℕ} (a : Fin m → (T' ⟶ G')), (List.ofFn fun j => δ ≫ a j).prod = δ ≫ (List.ofFn a).prod`. Introduce `m a`. Proceed by induction on `m with`.

Consider the case `zero => simp [MonObj.comp_one]`. Consider the case `succ m ih => rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, MonObj.comp_mul, ih]`. Rewrite `h1` using `[h2]`. Conclude with `((Category.id_comp _).symm.trans h1.symm).trans (Category.assoc _ _ _)`.
-/
theorem prod_pull {S' S₀ : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S₀} [GrpObj G] {f : S' ⟶ S₀}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T' : Over S') (T : Over S₀) (g : T.left ⟶ T'.left)
    (hg : g ≫ T'.hom ≫ f = T.hom) {m : ℕ} (a : Fin m → (T' ⟶ G')) (a₀ : Fin m → (T ⟶ G))
    (ha : ∀ j, (a₀ j).left = g ≫ (a j).left ≫ φ) :
    ((List.ofFn a₀).prod).left = g ≫ ((List.ofFn a).prod).left ≫ φ := by
  let δ : Over.mk (g ≫ T'.hom) ⟶ T' := Over.homMk g rfl
  have h1 := prod_push h (Over.mk (g ≫ T'.hom)) T (𝟙 _)
    ((Category.id_comp _).trans (hg.symm.trans (Category.assoc _ _ _).symm)) (fun j => δ ≫ a j) a₀
    (fun j => (Category.assoc _ _ _).trans ((ha j).symm.trans (Category.id_comp _).symm))
  have h2 : ∀ {m : ℕ} (a : Fin m → (T' ⟶ G')), (List.ofFn fun j => δ ≫ a j).prod = δ ≫ (List.ofFn a).prod := by
    intro m a
    induction m with
    | zero => simp [MonObj.comp_one]
    | succ m ih => rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, MonObj.comp_mul, ih]
  rw [h2] at h1
  exact ((Category.id_comp _).symm.trans h1.symm).trans (Category.assoc _ _ _)

/- English proof (translation)
Take `⟨u₁, hu₁, rfl⟩` from `hw₁`. Take `⟨u₂, hu₂, rfl⟩` from `hw₂`. Set `T : Over X` to `Over.mk (spMap (algebraMap F (DualNumber F)) ≫ spMap α ≫ f₁)`. Establish `e₁ : spMap (dualMap α) ≫ spMap (algebraMap V (DualNumber V)) ≫ f₁ = spMap (algebraMap F (DualNumber F)) ≫ spMap α ≫ f₁`. Rewrite using `[← Category.assoc, ← Category.assoc, spMap_comp₂, spMap_comp₂, dualMap_alg]`.

Establish `e₂ : spMap (dualMap β) ≫ spMap (algebraMap K (DualNumber K)) ≫ f₂ = spMap (algebraMap F (DualNumber F)) ≫ spMap α ≫ f₁`. Rewrite using `[hf, ← Category.assoc, ← Category.assoc, spMap_comp₂, spMap_comp₂, dualMap_alg]`. Set `Z : Fin m → (T ⟶ B)` to `fun i => Over.homMk (spMap (dualMap α) ≫ (u₁ i).left ≫ φ₁) (by show (spMap (dualMap α) ≫ (u₁ i).left ≫ φ₁) ≫ B.hom = spMap (algebraMap F (DualNumber F)) ≫ spMap α ≫ f₁`. Rewrite using `[Category.assoc, Category.assoc, h₁.1.w, ← Category.assoc (u₁ i).left, Over.w (u₁ i)]`. Conclude with `e₁)`.

Establish `k₁` using `prod_pull h₁ (epsR V) T (spMap (dualMap α)) e₁ u₁ Z (fun _ => rfl)`. Establish `k₂` using `prod_pull h₂ (epsR K) T (spMap (dualMap β)) e₂ u₂ Z (fun i => by show spMap (dualMap α) ≫ (u₁ i).left ≫ φ₁ = _`. Establish `a₁ : spMap (dualMap α) ≫ spMap (epsScaleR (c₁ i)) = spMap (epsMul (α (c₁ i))) ≫ spMap (dualMap α)`. Rewrite using `[spMap_comp₂, spMap_comp₂, ← dualMap_epsMul]`. Both sides reduce to the same expression.

Establish `a₂ : spMap (dualMap β) ≫ spMap (epsScaleR (c₂ i)) = spMap (epsMul (β (c₂ i))) ≫ spMap (dualMap β)`. Rewrite using `[spMap_comp₂, spMap_comp₂, ← dualMap_epsMul]`. Both sides reduce to the same expression. Rewrite using `[hu₁ i, hu₂ i, Category.assoc, Category.assoc, reassoc_of% a₁, reassoc_of% a₂, hv i, hc i])`. Conclude with `k₁.symm.trans k₂`.
-/
theorem comb_match {V K F : Type} [CommRing V] [CommRing K] [CommRing F] {X : Scheme.{0}} {B : Over X} [GrpObj B]
    {G₁ : Over (Sp V)} [GrpObj G₁] {G₂ : Over (Sp K)} [GrpObj G₂] {f₁ : Sp V ⟶ X} {f₂ : Sp K ⟶ X}
    {φ₁ : G₁.left ⟶ B.left} {φ₂ : G₂.left ⟶ B.left} (h₁ : IsGrpPullback G₁ B f₁ φ₁) (h₂ : IsGrpPullback G₂ B f₂ φ₂)
    (α : V →+* F) (β : K →+* F) (hf : spMap α ≫ f₁ = spMap β ≫ f₂) {m : ℕ} {v₁ : Fin m → (epsR V ⟶ G₁)}
    {v₂ : Fin m → (epsR K ⟶ G₂)}
    (hv : ∀ i, spMap (dualMap α) ≫ (v₁ i).left ≫ φ₁ = spMap (dualMap β) ≫ (v₂ i).left ≫ φ₂)
    {c₁ : Fin m → V} {c₂ : Fin m → K} (hc : ∀ i, α (c₁ i) = β (c₂ i)) {w₁ : epsR V ⟶ G₁} {w₂ : epsR K ⟶ G₂}
    (hw₁ : IsLieComb c₁ v₁ w₁) (hw₂ : IsLieComb c₂ v₂ w₂) :
    spMap (dualMap α) ≫ w₁.left ≫ φ₁ = spMap (dualMap β) ≫ w₂.left ≫ φ₂ := by
  obtain ⟨u₁, hu₁, rfl⟩ := hw₁
  obtain ⟨u₂, hu₂, rfl⟩ := hw₂
  let T : Over X := Over.mk (spMap (algebraMap F (DualNumber F)) ≫ spMap α ≫ f₁)
  have e₁ : spMap (dualMap α) ≫ spMap (algebraMap V (DualNumber V)) ≫ f₁ =
      spMap (algebraMap F (DualNumber F)) ≫ spMap α ≫ f₁ := by
    rw [← Category.assoc, ← Category.assoc, spMap_comp₂, spMap_comp₂, dualMap_alg]
  have e₂ : spMap (dualMap β) ≫ spMap (algebraMap K (DualNumber K)) ≫ f₂ =
      spMap (algebraMap F (DualNumber F)) ≫ spMap α ≫ f₁ := by
    rw [hf, ← Category.assoc, ← Category.assoc, spMap_comp₂, spMap_comp₂, dualMap_alg]
  let Z : Fin m → (T ⟶ B) := fun i => Over.homMk (spMap (dualMap α) ≫ (u₁ i).left ≫ φ₁) (by
    show (spMap (dualMap α) ≫ (u₁ i).left ≫ φ₁) ≫ B.hom = spMap (algebraMap F (DualNumber F)) ≫ spMap α ≫ f₁
    rw [Category.assoc, Category.assoc, h₁.1.w, ← Category.assoc (u₁ i).left, Over.w (u₁ i)]
    exact e₁)
  have k₁ := prod_pull h₁ (epsR V) T (spMap (dualMap α)) e₁ u₁ Z (fun _ => rfl)
  have k₂ := prod_pull h₂ (epsR K) T (spMap (dualMap β)) e₂ u₂ Z (fun i => by
    show spMap (dualMap α) ≫ (u₁ i).left ≫ φ₁ = _
    have a₁ : spMap (dualMap α) ≫ spMap (epsScaleR (c₁ i)) = spMap (epsMul (α (c₁ i))) ≫ spMap (dualMap α) := by
      rw [spMap_comp₂, spMap_comp₂, ← dualMap_epsMul]; rfl
    have a₂ : spMap (dualMap β) ≫ spMap (epsScaleR (c₂ i)) = spMap (epsMul (β (c₂ i))) ≫ spMap (dualMap β) := by
      rw [spMap_comp₂, spMap_comp₂, ← dualMap_epsMul]; rfl
    rw [hu₁ i, hu₂ i, Category.assoc, Category.assoc, reassoc_of% a₁, reassoc_of% a₂, hv i, hc i])
  exact k₁.symm.trans k₂

/- English proof (translation)
Take `⟨h1, -, h3, -⟩` from `LieComb.lieComb_algebra K G n v hv`. Set `s' : epsR K ⟶ G` to `Over.homMk (spMap (epsMul cl) ≫ w.left) (by show (spMap (epsMul cl) ≫ w.left) ≫ G.hom = spMap (algebraMap K (DualNumber K))`. Rewrite using `[Category.assoc, Over.w w]`. Conclude with `(spMap_comp₂ _ _).trans (congrArg spMap (epsMul_alg cl)))`. Establish `a₁` using `h3 n A wK _ s hw hs`.

Establish `a₂` using `h3 1 (fun _ => U) (fun _ => w) (fun _ => cl) s' (fun _ => hU) ⟨fun _ => s', fun _ => rfl, by simp⟩`. Establish `e : ∑ i, Matrix.vecMul (cl • U) A⁻¹ i • A i = ∑ _i : Fin 1, cl • U`. Rewrite using `[← Matrix.vecMul_eq_sum, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (IsUnit.mk0 _ hA), Matrix.vecMul_one]`. Simplify using the standard rewrite rules. Rewrite `a₁` using `[e]`.

Rewrite using `[(h1 _).unique a₁ a₂]`. Both sides reduce to the same expression.
-/
theorem comb_eq_scale {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] [IsCommMonObj G] {n : ℕ}
    {v wK : Fin n → (epsR K ⟶ G)} (hv : ∀ i, IsTangent (v i)) {A : Matrix (Fin n) (Fin n) K} (hA : A.det ≠ 0)
    (hw : ∀ i, IsLieComb (A i) v (wK i)) {U : Fin n → K} {w : epsR K ⟶ G} (hU : IsLieComb U v w) (cl : K)
    {s : epsR K ⟶ G} (hs : IsLieComb (Matrix.vecMul (cl • U) A⁻¹) wK s) :
    s.left = spMap (epsMul cl) ≫ w.left := by
  obtain ⟨h1, -, h3, -⟩ := LieComb.lieComb_algebra K G n v hv
  let s' : epsR K ⟶ G := Over.homMk (spMap (epsMul cl) ≫ w.left) (by
    show (spMap (epsMul cl) ≫ w.left) ≫ G.hom = spMap (algebraMap K (DualNumber K))
    rw [Category.assoc, Over.w w]
    exact (spMap_comp₂ _ _).trans (congrArg spMap (epsMul_alg cl)))
  have a₁ := h3 n A wK _ s hw hs
  have a₂ := h3 1 (fun _ => U) (fun _ => w) (fun _ => cl) s' (fun _ => hU) ⟨fun _ => s', fun _ => rfl, by simp⟩
  have e : ∑ i, Matrix.vecMul (cl • U) A⁻¹ i • A i = ∑ _i : Fin 1, cl • U := by
    rw [← Matrix.vecMul_eq_sum, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (IsUnit.mk0 _ hA), Matrix.vecMul_one]
    simp
  rw [e] at a₁
  rw [(h1 _).unique a₁ a₂]
  rfl

/- English proof (translation)
Rewrite using `[spMap_comp₂, spMap_comp₂]`. Use `congr 1`. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `r`. Apply the tactic sequence `ext <;> simp [epsMul, mul_left_comm]`.
-/
theorem epsMul_comm {R : Type} [CommRing R] (a b : R) :
    spMap (epsMul a) ≫ spMap (epsMul b) = spMap (epsMul b) ≫ spMap (epsMul a) := by
  rw [spMap_comp₂, spMap_comp₂]
  congr 1
  apply RingHom.ext
  intro r
  ext <;> simp [epsMul, mul_left_comm]

/- English proof (translation)
Introduce `a b h`. Establish `h₁` using `congrArg TrivSqZeroExt.fst h`. Establish `h₂` using `congrArg TrivSqZeroExt.snd h`. Simplify using `[dualMap] at h₁ h₂`. Conclude with `TrivSqZeroExt.ext (hf h₁) (hf h₂)`.
-/
theorem dualMap_inj {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (dualMap f) := by
  intro a b h
  have h₁ := congrArg TrivSqZeroExt.fst h
  have h₂ := congrArg TrivSqZeroExt.snd h
  simp [dualMap] at h₁ h₂
  exact TrivSqZeroExt.ext (hf h₁) (hf h₂)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Take `⟨N, _, _, v, ρ, hinj, htan, hcomb, -, hsm⟩` from `GlobalTheory.TanMod.exists_tangent_module E H Dw l Xo S y.x`. Use `choose β hβ using fun i => (htan _).1 (y.tan b i)`. Establish `hy : y.u b = fun i => v (β i)` using `funext fun i => (hβ i).symm`. Establish `hu' : u' = fun i => v (∑ j, g i j • β j)` using `funext fun i => (hcomb _ β _ _).1 (hy ▸ hu i)`. Establish `hw : spMap (epsMul r) ≫ y.u b j = v (r • β j)` using `by rw [hsm, hβ]`.

Establish `ht : IsTanAt y.x (spMap (epsMul r) ≫ y.u b j)` using `(htan _).2 ⟨_, hw.symm⟩`. Establish `he : IsEigAt c b (spMap (epsMul r) ≫ y.u b j)` using `fun a => by`. Rewrite using `[Category.assoc, y.eig b j a, ← Category.assoc, epsMul_comm, Category.assoc]`. Establish `h1` using `(hcomb _ (fun i => ∑ j, g i j • β j) _ _).1 (hu' ▸ ha)`. Establish `h2 : IsCombAt y.x (y.u b) (Matrix.vecMul a g) (spMap (epsMul r) ≫ y.u b j)`.

Rewrite using `[hy]`. Use `(hcomb _ β _ _).2 ((hy ▸ h1).trans (congrArg v ?_))` and prove the remaining obligations. Simplify using `only [Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]`. Conclude with `Finset.sum_comm`. Establish `h3 : IsCombAt y.x (y.u b) (Pi.single j r) (spMap (epsMul r) ≫ y.u b j)`.

Rewrite using `[hw, hy]`. Use `(hcomb _ β _ _).2 (congrArg v ?_)` and prove the remaining obligations. Simplify using `[Pi.single_apply]`. Establish `h4` using `(y.basis b _ ht he).unique h2 h3`. Establish `h5 : a = Matrix.vecMul (Pi.single j r) g⁻¹`.

Rewrite using `[← h4, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hg, Matrix.vecMul_one]`. Rewrite using `[h5]`. Simplify using `[Matrix.vecMul, dotProduct, Pi.single_apply]`.
-/
theorem coord_eq {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (b : E →+* ℂ)
    (u' : Fin (Dw.mult b) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (g : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) S)
    (hg : IsUnit g.det) (hu : ∀ i, IsCombAt y.x (y.u b) (g i) (u' i)) (r : S) (j : Fin (Dw.mult b))
    (a : Fin (Dw.mult b) → S) (ha : IsCombAt y.x u' a (spMap (epsMul r) ≫ y.u b j)) (k : Fin (Dw.mult b)) :
    r * g⁻¹ j k = a k := by
  classical
  obtain ⟨N, _, _, v, ρ, hinj, htan, hcomb, -, hsm⟩ := GlobalTheory.TanMod.exists_tangent_module E H Dw l Xo S y.x
  choose β hβ using fun i => (htan _).1 (y.tan b i)
  have hy : y.u b = fun i => v (β i) := funext fun i => (hβ i).symm
  have hu' : u' = fun i => v (∑ j, g i j • β j) := funext fun i => (hcomb _ β _ _).1 (hy ▸ hu i)
  have hw : spMap (epsMul r) ≫ y.u b j = v (r • β j) := by rw [hsm, hβ]
  have ht : IsTanAt y.x (spMap (epsMul r) ≫ y.u b j) := (htan _).2 ⟨_, hw.symm⟩
  have he : IsEigAt c b (spMap (epsMul r) ≫ y.u b j) := fun a => by
    rw [Category.assoc, y.eig b j a, ← Category.assoc, epsMul_comm, Category.assoc]
  have h1 := (hcomb _ (fun i => ∑ j, g i j • β j) _ _).1 (hu' ▸ ha)
  have h2 : IsCombAt y.x (y.u b) (Matrix.vecMul a g) (spMap (epsMul r) ≫ y.u b j) := by
    rw [hy]
    refine (hcomb _ β _ _).2 ((hy ▸ h1).trans (congrArg v ?_))
    simp only [Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
    exact Finset.sum_comm
  have h3 : IsCombAt y.x (y.u b) (Pi.single j r) (spMap (epsMul r) ≫ y.u b j) := by
    rw [hw, hy]
    refine (hcomb _ β _ _).2 (congrArg v ?_)
    simp [Pi.single_apply]
  have h4 := (y.basis b _ ht he).unique h2 h3
  have h5 : a = Matrix.vecMul (Pi.single j r) g⁻¹ := by
    rw [← h4, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hg, Matrix.vecMul_one]
  rw [h5]
  simp [Matrix.vecMul, dotProduct, Pi.single_apply]

/- English proof (translation)
Introduce `a z hz`. Establish `h1 : w' ≫ (t.act.act a).left = spMap (epsMul (algebraMap V K z)) ≫ w'`. Apply `m₁.cart.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, m₁.act a, ← Category.assoc, he a, hz, Category.assoc]`. Rewrite using `[Category.assoc, Over.w, Category.assoc, ho, spMap_comp₂, epsMul_alg]`.

Use `ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom (dualMap (algebraMap V K))) (dualMap_inj _ (IsFractionRing.injective V K))` as an intermediate fact. Use `ExtUnique.hom_ext_of_dominant G.G.hom ?_ (spMap (dualMap (algebraMap V K))) ?_` and prove the remaining obligations. Rewrite using `[Over.w, Category.assoc, Over.w]`. Conclude with `((spMap_comp₂ _ _).trans (congrArg spMap (epsMul_alg z))).symm`. Establish `a₁ : spMap (dualMap (algebraMap V K)) ≫ spMap (epsMul z) = spMap (epsMul (algebraMap V K z)) ≫ spMap (dualMap (algebraMap V K))`.

Rewrite using `[spMap_comp₂, spMap_comp₂, ← dualMap_epsMul]`. Rewrite using `[Over.comp_left, ← reassoc_of% hw, ← m₂.act a, reassoc_of% h1, reassoc_of% a₁, ← hw]`.
-/
theorem isEigV_of_generic {V K : Type} [CommRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Algebra c.F K]
    {x : Sp K ⟶ Xo.X} {G : SAB H (Sp V)} [IsSeparated G.G.hom] {t : SAB H (Sp K)} (m₁ : SABMap t Xo.univ.t x)
    (m₂ : SABMap t G (spMap (algebraMap V K))) (b : E →+* ℂ) (w : epsOver V V ⟶ G.G)
    (w' : Sp (DualNumber K) ⟶ t.G.left) (hw : w' ≫ m₂.φ = spMap (dualMap (algebraMap V K)) ≫ w.left)
    (ho : w' ≫ t.G.hom = spMap (algebraMap K (DualNumber K))) (he : IsEigAt c b (w' ≫ m₁.φ)) :
    IsEigV c (algebraMap c.F K) G b w := by
  intro a z hz
  have h1 : w' ≫ (t.act.act a).left = spMap (epsMul (algebraMap V K z)) ≫ w' := by
    apply m₁.cart.1.hom_ext
    · rw [Category.assoc, m₁.act a, ← Category.assoc, he a, hz, Category.assoc]
    · rw [Category.assoc, Over.w, Category.assoc, ho, spMap_comp₂, epsMul_alg]
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom (dualMap (algebraMap V K)))
    (dualMap_inj _ (IsFractionRing.injective V K))
  refine ExtUnique.hom_ext_of_dominant G.G.hom ?_ (spMap (dualMap (algebraMap V K))) ?_
  · rw [Over.w, Category.assoc, Over.w]
    exact ((spMap_comp₂ _ _).trans (congrArg spMap (epsMul_alg z))).symm
  · have a₁ : spMap (dualMap (algebraMap V K)) ≫ spMap (epsMul z) =
        spMap (epsMul (algebraMap V K z)) ≫ spMap (dualMap (algebraMap V K)) := by
      rw [spMap_comp₂, spMap_comp₂, ← dualMap_epsMul]
    rw [Over.comp_left, ← reassoc_of% hw, ← m₂.act a, reassoc_of% h1, reassoc_of% a₁, ← hw]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c _ z f La hz p T iK M hval`. Use `letI := (iK.comp (algebraMap c.F z.K)).toAlgebra`. Introduce `φ yT y' g a hφ hmap hchg hg hint b j k cl hcl`. Take `⟨hobj, hlet, -, hx, -, hu⟩` from `hz`. Take `⟨A, hA, -⟩` from `hobj.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 p`.

Establish `hcint` using `LamF.letter_integral_of_isLocGen E H l c _ _ f z.obj La hobj z.letters hlet p A hA (z.e ⟨b, j⟩) cl hcl`. Take `⟨vV, hvV, hvw⟩` from `GlobalTheory.T.exists_lieBasis_local_model E H Dw l Xo c z p T iK M hval A hA`. Use `choose wK hwK hwV using hvw`. Establish `hdet : A.det ≠ 0`. Take `⟨_, _, _, _, _, _, _, _, _, _, -, -, -, h, -⟩` from `hA`.

Conclude with `h`. Use `choose cV hcV using fun m => (hval _).2 (hcint m)`. Take `⟨w, hw, hwu⟩` from `hu b j`. Take `⟨w₀, hw₀, hU⟩` from `hlet.2.2.1 (z.e ⟨b, j⟩)`. Choose the witnesses or unpack the hypotheses as in `rfl : w₀ = w := by`.

Use `Over.OverMorphism.ext (z.m'.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))` and prove the remaining obligations. Unfold `LamF.LamLetters.IsLetter at hw hw₀`. Generalize the expression as in `z.letters.src (z.e ⟨b, j⟩) = s at hw hw₀`. Break down `s with q | q` into its components or cases. Conclude with `hw₀.trans hw.symm`.

Conclude with `hw₀.trans hw.symm`. Establish `hK` using `LieComb.lieComb_algebra z.K z.Φ.T.t.G _ z.Φ.v z.Φ.basis.1`. Take `⟨s, hs, -⟩` from `(LieComb.lieComb_algebra z.K z.Φ.T.t.G _ wK (fun i => hK.2.1 _ _ (hwK i))).1 (Matrix.vecMul (cl • z.U (z.e ⟨b, j⟩)) A⁻¹)`. Establish `hV` using `LieComb.lieComb_algebra T.V M.G.t.G _ vV hvV.1`. Take `⟨W, hW, -⟩` from `hV.1 cV`.

Establish `hWt` using `hV.2.1 _ _ hW`. Establish `hbase : spMap (algebraMap T.V T.Fr) ≫ spMap M.ρ = spMap iK ≫ spMap (algebraMap (𝓞 z.K) z.K)`. Rewrite using `[spMap_comp₂, spMap_comp₂, M.hρ]`. Establish `hmatch` using `comb_match M.n.cart z.m'.cart (algebraMap T.V T.Fr) iK hbase hwV hcV hW hs`. Establish `hsl` using `comb_eq_scale z.Φ.basis.1 hdet hwK hU cl hs`.

Establish `hsq : (spMap (dualMap iK) ≫ s.left) ≫ z.Φ.T.t.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap iK`. Rewrite using `[Category.assoc, Over.w s]`. Conclude with `(spMap_comp₂ _ _).trans ((congrArg spMap (dualMap_alg iK)).trans (spMap_comp₂ _ _).symm)`. Set `s' : Sp (DualNumber T.Fr) ⟶ M.t'.t.G.left` to `M.n'.cart.1.lift _ _ hsq`. Establish `hs1 : s' ≫ M.n'.φ = spMap (dualMap iK) ≫ s.left` using `M.n'.cart.1.lift_fst _ _ _`.

Establish `hs2 : s' ≫ M.t'.t.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr))` using `M.n'.cart.1.lift_snd _ _ _`. Set `W' : epsOver T.V T.V ⟶ M.G.t.G` to `Over.homMk W.left (Over.w W)`. Establish `hm2 : s' ≫ M.m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ W'.left`. Apply `M.n.cart.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc]`.

Use `Eq.trans ?_ hmatch.symm` and prove the remaining obligations. Conclude with `(congrArg (s' ≫ ·) M.h2).trans (by rw [reassoc_of% hs1])`. Rewrite using `[Category.assoc, M.m2.cart.1.w, reassoc_of% hs2, Category.assoc, Over.w W']`. Conclude with `(spMap_comp₂ _ _).trans ((congrArg spMap (dualMap_alg _).symm).trans (spMap_comp₂ _ _).symm)`. Establish `hm1 : s' ≫ M.m1.φ = spMap (epsMul (iK cl)) ≫ yT.u b j`.

Establish `a₁ : spMap (dualMap iK) ≫ spMap (epsMul cl) = spMap (epsMul (iK cl)) ≫ spMap (dualMap iK)`. Rewrite using `[spMap_comp₂, spMap_comp₂, ← dualMap_epsMul]`. Rewrite using `[M.h1, reassoc_of% hs1, hsl, Category.assoc, reassoc_of% a₁, hmap.2.1 b j, hφ, hwu]`. Establish `hW't : IsTan W'`. Unfold `IsTan`.

Use `hWt.trans ?_` and prove the remaining obligations. Establish `e : (1 : ptOver T.V T.V ⟶ M.G.t.G) = toUnit _ ≫ η[M.G.t.G]` using `rfl`. Rewrite using `[e, Over.comp_left]`. Establish `e2 : (toUnit (ptOver T.V T.V)).left = 𝟙 (Sp T.V)`. Use `Over.w (toUnit (ptOver T.V T.V))` as an intermediate fact.

Conclude with `((Category.comp_id _).symm.trans this).trans (Spec.map_id _)`. Rewrite using `[e2]`. Conclude with `(Category.id_comp _).symm`. Use `M.G.ab.proper` as an intermediate fact. Establish `hW'e : IsEigV c (iK.comp (algebraMap c.F z.K)) M.G.t b W'` using `isEigV_of_generic M.m1 M.m2 b W' s' hm2 hs2 (fun a => by`.

Rewrite using `[hm1, Category.assoc, yT.eig b j a, ← Category.assoc, epsMul_comm, Category.assoc])`. Take `⟨ub, -, -, hb, hl⟩` from `hint`. Take `⟨aV, haV, -⟩` from `hb b W' hW't hW'e`. Use `choose u' hu1 hu2 using hl b`. Establish `hgen` using `comb_generic M.m1 M.m2 (ub b) u' hu2 W' s' hm2 aV haV`.

Establish `hxT : spMap iK ≫ z.x = yT.x` using `by rw [hmap.1, hφ, hx]`. Rewrite `hgen` using `[hm1, funext hu1]`. Establish `hgen' : IsCombAt yT.x (y'.u b) (fun j => algebraMap T.V T.Fr (aV j)) (spMap (epsMul (iK cl)) ≫ yT.u b j)` using `hxT ▸ hgen`. Conclude with `⟨aV k, (coord_eq yT b (y'.u b) (g b) (hg b) (hchg.2.1 b) (iK cl) j _ hgen' k).symm⟩`.
-/
theorem letter_integral_in_eigenbasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ (p : HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr) (M : LocMod z T iK), (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → letI := (iK.comp (algebraMap c.F z.K)).toAlgebra; ∀ (φ : z.K →ₐ[c.F] T.Fr) (yT y' : FrPt Xo c T.Fr) (g : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr)) (a : T.Fr), φ.toRingHom = iK → FrMap φ z.y yT → FrChg g a yT y' → (∀ b, IsUnit (g b).det) → LieInt T (iK.comp (algebraMap c.F z.K)) M.m1 M.m2 y'.u → ∀ (b : E →+* ℂ) (j k : Fin (Dw.mult b)) (cl : z.K), IsLocGen p cl (z.ℓ (z.e ⟨b, j⟩)).I → iK cl * (g b)⁻¹ j k ∈ Set.range (algebraMap T.V T.Fr) := by
  intro E _ _ _ H Dw l Xo c _ z f La hz p T iK M hval
  letI := (iK.comp (algebraMap c.F z.K)).toAlgebra
  intro φ yT y' g a hφ hmap hchg hg hint b j k cl hcl
  obtain ⟨hobj, hlet, -, hx, -, hu⟩ := hz
  obtain ⟨A, hA, -⟩ := hobj.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 p
  have hcint := LamF.letter_integral_of_isLocGen E H l c _ _ f z.obj La hobj z.letters hlet p A hA (z.e ⟨b, j⟩) cl hcl
  obtain ⟨vV, hvV, hvw⟩ := GlobalTheory.T.exists_lieBasis_local_model E H Dw l Xo c z p T iK M hval A hA
  choose wK hwK hwV using hvw
  have hdet : A.det ≠ 0 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, -, -, -, h, -⟩ := hA
    exact h
  choose cV hcV using fun m => (hval _).2 (hcint m)
  obtain ⟨w, hw, hwu⟩ := hu b j
  obtain ⟨w₀, hw₀, hU⟩ := hlet.2.2.1 (z.e ⟨b, j⟩)
  obtain rfl : w₀ = w := by
    refine Over.OverMorphism.ext (z.m'.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    unfold LamF.LamLetters.IsLetter at hw hw₀
    generalize z.letters.src (z.e ⟨b, j⟩) = s at hw hw₀
    rcases s with q | q
    · exact hw₀.trans hw.symm
    · exact hw₀.trans hw.symm
  have hK := LieComb.lieComb_algebra z.K z.Φ.T.t.G _ z.Φ.v z.Φ.basis.1
  obtain ⟨s, hs, -⟩ := (LieComb.lieComb_algebra z.K z.Φ.T.t.G _ wK (fun i => hK.2.1 _ _ (hwK i))).1
    (Matrix.vecMul (cl • z.U (z.e ⟨b, j⟩)) A⁻¹)
  have hV := LieComb.lieComb_algebra T.V M.G.t.G _ vV hvV.1
  obtain ⟨W, hW, -⟩ := hV.1 cV
  have hWt := hV.2.1 _ _ hW
  have hbase : spMap (algebraMap T.V T.Fr) ≫ spMap M.ρ = spMap iK ≫ spMap (algebraMap (𝓞 z.K) z.K) := by
    rw [spMap_comp₂, spMap_comp₂, M.hρ]
  have hmatch := comb_match M.n.cart z.m'.cart (algebraMap T.V T.Fr) iK hbase hwV hcV hW hs
  have hsl := comb_eq_scale z.Φ.basis.1 hdet hwK hU cl hs
  have hsq : (spMap (dualMap iK) ≫ s.left) ≫ z.Φ.T.t.G.hom =
      spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap iK := by
    rw [Category.assoc, Over.w s]
    exact (spMap_comp₂ _ _).trans ((congrArg spMap (dualMap_alg iK)).trans (spMap_comp₂ _ _).symm)
  let s' : Sp (DualNumber T.Fr) ⟶ M.t'.t.G.left := M.n'.cart.1.lift _ _ hsq
  have hs1 : s' ≫ M.n'.φ = spMap (dualMap iK) ≫ s.left := M.n'.cart.1.lift_fst _ _ _
  have hs2 : s' ≫ M.t'.t.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := M.n'.cart.1.lift_snd _ _ _
  let W' : epsOver T.V T.V ⟶ M.G.t.G := Over.homMk W.left (Over.w W)
  have hm2 : s' ≫ M.m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ W'.left := by
    apply M.n.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc]
      refine Eq.trans ?_ hmatch.symm
      exact (congrArg (s' ≫ ·) M.h2).trans (by rw [reassoc_of% hs1])
    · rw [Category.assoc, M.m2.cart.1.w, reassoc_of% hs2, Category.assoc, Over.w W']
      exact (spMap_comp₂ _ _).trans ((congrArg spMap (dualMap_alg _).symm).trans (spMap_comp₂ _ _).symm)
  have hm1 : s' ≫ M.m1.φ = spMap (epsMul (iK cl)) ≫ yT.u b j := by
    have a₁ : spMap (dualMap iK) ≫ spMap (epsMul cl) = spMap (epsMul (iK cl)) ≫ spMap (dualMap iK) := by
      rw [spMap_comp₂, spMap_comp₂, ← dualMap_epsMul]
    rw [M.h1, reassoc_of% hs1, hsl, Category.assoc, reassoc_of% a₁, hmap.2.1 b j, hφ, hwu]
  have hW't : IsTan W' := by
    unfold IsTan
    refine hWt.trans ?_
    have e : (1 : ptOver T.V T.V ⟶ M.G.t.G) = toUnit _ ≫ η[M.G.t.G] := rfl
    rw [e, Over.comp_left]
    have e2 : (toUnit (ptOver T.V T.V)).left = 𝟙 (Sp T.V) := by
      have := Over.w (toUnit (ptOver T.V T.V))
      exact ((Category.comp_id _).symm.trans this).trans (Spec.map_id _)
    rw [e2]
    exact (Category.id_comp _).symm
  have := M.G.ab.proper
  have hW'e : IsEigV c (iK.comp (algebraMap c.F z.K)) M.G.t b W' :=
    isEigV_of_generic M.m1 M.m2 b W' s' hm2 hs2 (fun a => by
      rw [hm1, Category.assoc, yT.eig b j a, ← Category.assoc, epsMul_comm, Category.assoc])
  obtain ⟨ub, -, -, hb, hl⟩ := hint
  obtain ⟨aV, haV, -⟩ := hb b W' hW't hW'e
  choose u' hu1 hu2 using hl b
  have hgen := comb_generic M.m1 M.m2 (ub b) u' hu2 W' s' hm2 aV haV
  have hxT : spMap iK ≫ z.x = yT.x := by rw [hmap.1, hφ, hx]
  rw [hm1, funext hu1] at hgen
  have hgen' : IsCombAt yT.x (y'.u b) (fun j => algebraMap T.V T.Fr (aV j))
      (spMap (epsMul (iK cl)) ≫ yT.u b j) := hxT ▸ hgen
  exact ⟨aV k, (coord_eq yT b (y'.u b) (g b) (hg b) (hchg.2.1 b) (iK cl) j _ hgen' k).symm⟩

end GlobalTheory.LamT.LetterInt
