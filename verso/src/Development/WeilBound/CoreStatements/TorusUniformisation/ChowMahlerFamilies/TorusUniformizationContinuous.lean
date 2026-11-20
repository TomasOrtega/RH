import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ToXQFst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionalSpecializes
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsClosureCoords
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCocharacterLieModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false

namespace PositivityTheory.Xgn.TorusUniformizationContinuity

open GlobalTheory.CompanionTheory.Ar.LieVB GlobalTheory.CompanionTheory.Ar.RootHt.ArchB GlobalTheory.CompanionTheory.Ar.RootHt.ArchC

/- English proof (translation)
Use `letI : NormedAddCommGroup V := @InnerProductSpace.Core.toNormedAddCommGroup ℂ V _ _ _ core`. Use `letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore core.toCore`. Express the relevant statement in the definitionally equal form `inner ℂ (∑ i, a i • x i) (∑ j, b j • x j) = ∑ i, ∑ j, starRingEnd ℂ (a i) * b j * inner ℂ (x i) (x j)`. Rewrite using `[sum_inner]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[inner_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[inner_smul_left, inner_smul_right, _root_.mul_assoc]`.
-/
theorem core_sum {V : Type} [AddCommGroup V] [Module ℂ V] (core : InnerProductSpace.Core ℂ V) {n : ℕ}
    (a b : Fin n → ℂ) (x : Fin n → V) :
    core.inner (∑ i, a i • x i) (∑ j, b j • x j) =
      ∑ i, ∑ j, starRingEnd ℂ (a i) * b j * core.inner (x i) (x j) := by
  letI : NormedAddCommGroup V := @InnerProductSpace.Core.toNormedAddCommGroup ℂ V _ _ _ core
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore core.toCore
  change inner ℂ (∑ i, a i • x i) (∑ j, b j • x j) = ∑ i, ∑ j, starRingEnd ℂ (a i) * b j * inner ℂ (x i) (x j)
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_smul_right, _root_.mul_assoc]

/- English proof (translation)
Simplify using `only [spMap, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_cmp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (d : A →+* B) (c : B →+* C) :
    spMap c ≫ spMap d = spMap (c.comp d) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

/- English proof (translation)
The claim follows from `congrArg (fun g => g.hom) (Spec.map_injective ((cancel_mono x).1 h))`.
-/
theorem ringHom_eq {R A : Type} [CommRing R] [CommRing A] {X : Scheme.{0}} (x : Sp R ⟶ X) [Mono x]
    {a b : R →+* A} (h : spMap a ≫ x = spMap b ≫ x) : a = b :=
  congrArg (fun g => g.hom) (Spec.map_injective ((cancel_mono x).1 h))

/- English proof (translation)
Rewrite using `[← Submodule.mem_span_range_iff_exists_fun]`. Use `RootHt.lie_transport_induction c h M M' j hj (P := fun e => e ∈ Submodule.span R' (Set.range fun i => j (s i))) (zero_mem _) (fun e => ?_) (fun r n hn => Submodule.smul_mem _ r hn) (fun n n' hn hn' => add_mem hn hn') e'` and prove the remaining obligations. Establish `he : e ∈ Submodule.span R (Set.range s)` using `hs ▸ Submodule.mem_top`. Take `⟨a, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 he`. Rewrite using `[map_sum]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[j.map_smulₛₗ]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem span_tr {X : Scheme.{0}} {G : Over X} [GrpObj G] [Smooth G.hom] {R R' : Type} [CommRing R] [CommRing R']
    {E E' : Type} [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E'] (c : R →+* R') {x : Sp R ⟶ X}
    {y : Sp R' ⟶ X} (h : spMap c ≫ x = y) (M : LieModel G x E) (M' : LieModel G y E') (j : E →ₛₗ[c] E')
    (hj : ∀ e, (M'.pt (j e)).left = spMap (dualMap c) ≫ (M.pt e).left) {n : ℕ} (s : Fin n → E)
    (hs : Submodule.span R (Set.range s) = ⊤) (e' : E') : ∃ a : Fin n → R', ∑ i, a i • j (s i) = e' := by
  rw [← Submodule.mem_span_range_iff_exists_fun]
  refine RootHt.lie_transport_induction c h M M' j hj
    (P := fun e => e ∈ Submodule.span R' (Set.range fun i => j (s i))) (zero_mem _) (fun e => ?_)
    (fun r n hn => Submodule.smul_mem _ r hn) (fun n n' hn hn' => add_mem hn hn') e'
  have he : e ∈ Submodule.span R (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he
  rw [map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [j.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Unfold `IsTanAt at hv ⊢`. Rewrite using `[Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, MonObj.one_comp]`.
-/
theorem isTan_comp {S : Scheme.{0}} {T G : Over S} [GrpObj T] [GrpObj G] (u : T ⟶ G) [IsMonHom u] {R : Type}
    [CommRing R] {x : Sp R ⟶ S} (v : epsAt x ⟶ T) (hv : IsTanAt T x v) : IsTanAt G x (v ≫ u) := by
  unfold IsTanAt at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, MonObj.one_comp]

/- English proof (translation)
Take `⟨j, hj⟩` from `exists_tr a b g h M M'`. Establish `hb : (epsAt b).hom = spMap (dualMap g) ≫ (epsAt a).hom`. Establish `h1` using `Over.w (M'.pt (j 0))`. Establish `h2` using `Over.w (M.pt 0)`. Rewrite using `[← h1, hj, Category.assoc, h2]`.

Establish `e : M'.pt ((Int.castAddHom B).comp δ) = TorusLie.pullPt (dualMap g) hb (M.pt ((Int.castAddHom A).comp δ))`. Use `TorusLie.ptOf_ext b _ _ fun χ => ?_` and prove the remaining obligations. Rewrite using `[TorusLie.charVal_pullPt, hM, hM']`. Apply the tactic sequence `ext <;> simp [dualMap]`. Conclude with `congrArg (fun t => t.left) e`.
-/
theorem torus_tr {S : Scheme.{0}} {Xc : Type} [AddCommGroup Xc] {A B : Type} [CommRing A] [CommRing B]
    (g : A →+* B) {a : Sp A ⟶ S} {b : Sp B ⟶ S} (h : spMap g ≫ a = b)
    (M : LieModel (splitTorus S Xc) a (Xc →+ A)) (hM : IsCocharLie M)
    (M' : LieModel (splitTorus S Xc) b (Xc →+ B)) (hM' : IsCocharLie M') (δ : Xc →+ ℤ) :
    (M'.pt ((Int.castAddHom B).comp δ)).left = spMap (dualMap g) ≫ (M.pt ((Int.castAddHom A).comp δ)).left := by
  obtain ⟨j, hj⟩ := exists_tr a b g h M M'
  have hb : (epsAt b).hom = spMap (dualMap g) ≫ (epsAt a).hom := by
    have h1 := Over.w (M'.pt (j 0))
    have h2 := Over.w (M.pt 0)
    rw [← h1, hj, Category.assoc, h2]
  have e : M'.pt ((Int.castAddHom B).comp δ) =
      TorusLie.pullPt (dualMap g) hb (M.pt ((Int.castAddHom A).comp δ)) := by
    refine TorusLie.ptOf_ext b _ _ fun χ => ?_
    rw [TorusLie.charVal_pullPt, hM, hM']
    ext <;> simp [dualMap]
  exact congrArg (fun t => t.left) e

/- English proof (translation)
Establish `hq : (X.fromSpecStalk (centre z)) (IsLocalRing.closedPoint (X.presheaf.stalk (centre z))) ∈ x.opensRange`. Rewrite using `[Scheme.fromSpecStalk_closedPoint, ← hg]`. Conclude with `⟨spMap g (IsLocalRing.closedPoint ℂ), rfl⟩`. Take `⟨κ, hκ⟩` from `exists_lift (A := X.presheaf.stalk (centre z)) x (X.fromSpecStalk (centre z)) hq`. Take `⟨Fq, _, _, ⟨Mq⟩⟩` from `lieModel_exists X G (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z))`.

Take `⟨β, hβ⟩` from `exists_tr (B := X.presheaf.stalk (centre z)) x (X.fromSpecStalk (centre z)) κ hκ MR Mq`. Establish `h1 : (genMap ξ ⟨centre z, hall _⟩).comp κ = ψ`. Use `ringHom_eq x ?_` and prove the remaining obligations. Rewrite using `[← spMap_cmp, Category.assoc, hκ, hψ]`. Conclude with `LieTangent.spec_genMap ξ ⟨centre z, hall _⟩`.

Establish `h2 : (Scheme.stalkClosedPointTo z).hom.comp κ = g`. Use `ringHom_eq x ?_` and prove the remaining obligations. Rewrite using `[← spMap_cmp, Category.assoc, hκ, hg]`. Conclude with `Scheme.Spec_stalkClosedPointTo_fromSpecStalk z`. Use `⟨hall _, Mq.pt (β e), ⟨Mq.tan _, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hf, ← h1, ← spMap_dual_comp, Category.assoc, ← hβ]`. Rewrite using `[hv, ← h2, ← spMap_dual_comp, Category.assoc, ← hβ]`.
-/
theorem lie_valAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} (hall : ∀ q : X, genPt ξ ⤳ q)
    {G : Over X} [GrpObj G] [IsCommMonObj G] {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li)
    {R : Type} [CommRing R] (x : Sp R ⟶ X) [IsOpenImmersion x] {E : Type} [AddCommGroup E] [Module R E]
    (MR : LieModel G x E) (ψ : R →+* Ω) (hψ : spMap ψ ≫ x = ξ) (e : E) (f : Li)
    (hf : (M.pt f).left = spMap (dualMap ψ) ≫ (MR.pt e).left) (z : Sp ℂ ⟶ X) (g : R →+* ℂ)
    (hg : spMap g ≫ x = z) (v : epsAt z ⟶ G) (hv : v.left = spMap (dualMap g) ≫ (MR.pt e).left) :
    M.ValAt z f v := by
  have hq : (X.fromSpecStalk (centre z)) (IsLocalRing.closedPoint (X.presheaf.stalk (centre z))) ∈ x.opensRange := by
    rw [Scheme.fromSpecStalk_closedPoint, ← hg]
    exact ⟨spMap g (IsLocalRing.closedPoint ℂ), rfl⟩
  obtain ⟨κ, hκ⟩ := exists_lift (A := X.presheaf.stalk (centre z)) x (X.fromSpecStalk (centre z)) hq
  obtain ⟨Fq, _, _, ⟨Mq⟩⟩ := lieModel_exists X G (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z))
  obtain ⟨β, hβ⟩ := exists_tr (B := X.presheaf.stalk (centre z)) x (X.fromSpecStalk (centre z)) κ hκ MR Mq
  have h1 : (genMap ξ ⟨centre z, hall _⟩).comp κ = ψ := by
    refine ringHom_eq x ?_
    rw [← spMap_cmp, Category.assoc, hκ, hψ]
    exact LieTangent.spec_genMap ξ ⟨centre z, hall _⟩
  have h2 : (Scheme.stalkClosedPointTo z).hom.comp κ = g := by
    refine ringHom_eq x ?_
    rw [← spMap_cmp, Category.assoc, hκ, hg]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk z
  refine ⟨hall _, Mq.pt (β e), ⟨Mq.tan _, ?_⟩, ?_⟩
  · rw [hf, ← h1, ← spMap_dual_comp, Category.assoc, ← hβ]
  · rw [hv, ← h2, ← spMap_dual_comp, Category.assoc, ← hβ]

/- English proof (translation)
Take `⟨E', _, _, ⟨M'⟩⟩` from `lieModel_exists X G B (xV ≫ ρ)`. Take `⟨j, hj⟩` from `exists_tr x (xV ≫ ρ) φ hφ MR M'`. Take `⟨MT, hMT⟩` from `TorusLie.exists_lieModel_splitTorus Z' Xc B xV`. Establish `hD : ∀ a, ∃ D : E', M'.pt D = LiePull.tanPts hΦ xV (MT.pt ((Int.castAddHom B).comp (β a)) ≫ u)` using `fun a => M'.onto _ ((LiePull.isTan_iff hΦ xV _).2 (isTan_comp u _ (MT.tan _)))`. Use `choose D hD using hD`.

Use `choose c hc using fun a => span_tr φ hφ MR M' j hj s hs (D a)`. Use `⟨c, fun g z hz => ?_⟩` and prove the remaining obligations. Take `⟨Mz, hMz⟩` from `TorusLie.exists_lieModel_splitTorus Z' Xc ℂ z`. Take `⟨Ec, _, _, ⟨Mc⟩⟩` from `lieModel_exists X G ℂ (z ≫ ρ)`. Take `⟨j', hj'⟩` from `exists_tr (xV ≫ ρ) (z ≫ ρ) g (by rw [← Category.assoc, hz]) M' Mc`.

Use `⟨fun i => Mc.pt (j' (j (s i))), fun i => ?_, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[hj', hj, ← Category.assoc, spMap_dual_comp]`. Establish `hv` using `hH z Mz hMz (fun a => Mc.pt (j' (D a))) (fun a => by`. Establish `e : (M'.pt (D a)).left = ((MT.pt ((Int.castAddHom B).comp (β a))).left ≫ u.left) ≫ Φ` using `congrArg (fun t => t.left) (hD a)`. Establish `e2 : (Mz.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left = (spMap (dualMap g) ≫ (MT.pt ((Int.castAddHom B).comp (β a))).left) ≫ u.left` using `congrArg (· ≫ u.left) (torus_tr g hz MT hMT Mz hMz (β a))`.

Rewrite using `[hj', e, e2]`. Simplify using `only [Category.assoc])`. Take `⟨core, hcore⟩` from `h.herm (z ≫ ρ) Ec Mc`. Establish `hDs : ∀ a, j' (D a) = ∑ i, g (c a i) • j' (j (s i))` using `fun a => by`. Rewrite using `[← hc a, map_sum]`.

Conclude with `Finset.sum_congr rfl fun i _ => j'.map_smulₛₗ _ _`. Rewrite using `[hv]`. Express the relevant statement in the definitionally equal form `h.ip (z ≫ ρ) (Mc.pt (j' (D a))) (Mc.pt (j' (D b))) = _`. Rewrite using `[← hcore, hDs, hDs, core_sum]`. Simplify using `only [hcore]`.
-/
theorem local_formula {X : Scheme.{0}} {Ω : Type} [Field Ω] {K : Type} {J : K → Type}
    {y : (Σ k, J k) → Ω} {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    {Li : Type} [AddCommGroup Li] [Module Ω Li] {M : LieModel G ξ Li} (h : LieMetric M y)
    {Z' : Scheme.{0}} {ρ : Z' ⟶ X} {G' : Over Z'} [GrpObj G'] {Φ : G'.left ⟶ G.left} (hΦ : IsGrpPullback G' G ρ Φ)
    {Xc : Type} [AddCommGroup Xc] (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] {r : ℕ}
    (β : Fin r → (Xc →+ ℤ)) (H : (Sp ℂ ⟶ Z') → Matrix (Fin r) (Fin r) ℂ)
    (hH : ∀ (zc : Sp ℂ ⟶ Z') (Mz : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)), IsCocharLie Mz →
      ∀ v : Fin r → (epsAt (zc ≫ ρ) ⟶ G), (∀ a, (v a).left = (Mz.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ) →
        H zc = RootHt.gramAt h (zc ≫ ρ) v)
    {R B : Type} [CommRing R] [CommRing B] (x : Sp R ⟶ X) (xV : Sp B ⟶ Z') (φ : R →+* B)
    (hφ : spMap φ ≫ x = xV ≫ ρ) {E : Type} [AddCommGroup E] [Module R E] (MR : LieModel G x E) {n : ℕ}
    (s : Fin n → E) (hs : Submodule.span R (Set.range s) = ⊤) :
    ∃ c : Fin r → Fin n → B, ∀ (g : B →+* ℂ) (z : Sp ℂ ⟶ Z'), spMap g ≫ xV = z →
      ∃ sv : Fin n → (epsAt (z ≫ ρ) ⟶ G), (∀ i, (sv i).left = spMap (dualMap (g.comp φ)) ≫ (MR.pt (s i)).left) ∧
        ∀ a b, H z a b = ∑ i, ∑ j, starRingEnd ℂ (g (c a i)) * g (c b j) * h.ip (z ≫ ρ) (sv i) (sv j) := by
  obtain ⟨E', _, _, ⟨M'⟩⟩ := lieModel_exists X G B (xV ≫ ρ)
  obtain ⟨j, hj⟩ := exists_tr x (xV ≫ ρ) φ hφ MR M'
  obtain ⟨MT, hMT⟩ := TorusLie.exists_lieModel_splitTorus Z' Xc B xV
  have hD : ∀ a, ∃ D : E', M'.pt D = LiePull.tanPts hΦ xV (MT.pt ((Int.castAddHom B).comp (β a)) ≫ u) :=
    fun a => M'.onto _ ((LiePull.isTan_iff hΦ xV _).2 (isTan_comp u _ (MT.tan _)))
  choose D hD using hD
  choose c hc using fun a => span_tr φ hφ MR M' j hj s hs (D a)
  refine ⟨c, fun g z hz => ?_⟩
  obtain ⟨Mz, hMz⟩ := TorusLie.exists_lieModel_splitTorus Z' Xc ℂ z
  obtain ⟨Ec, _, _, ⟨Mc⟩⟩ := lieModel_exists X G ℂ (z ≫ ρ)
  obtain ⟨j', hj'⟩ := exists_tr (xV ≫ ρ) (z ≫ ρ) g (by rw [← Category.assoc, hz]) M' Mc
  refine ⟨fun i => Mc.pt (j' (j (s i))), fun i => ?_, fun a b => ?_⟩
  · rw [hj', hj, ← Category.assoc, spMap_dual_comp]
  have hv := hH z Mz hMz (fun a => Mc.pt (j' (D a))) (fun a => by
    have e : (M'.pt (D a)).left = ((MT.pt ((Int.castAddHom B).comp (β a))).left ≫ u.left) ≫ Φ :=
      congrArg (fun t => t.left) (hD a)
    have e2 : (Mz.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left =
        (spMap (dualMap g) ≫ (MT.pt ((Int.castAddHom B).comp (β a))).left) ≫ u.left :=
      congrArg (· ≫ u.left) (torus_tr g hz MT hMT Mz hMz (β a))
    rw [hj', e, e2]
    simp only [Category.assoc])
  obtain ⟨core, hcore⟩ := h.herm (z ≫ ρ) Ec Mc
  have hDs : ∀ a, j' (D a) = ∑ i, g (c a i) • j' (j (s i)) := fun a => by
    rw [← hc a, map_sum]
    exact Finset.sum_congr rfl fun i _ => j'.map_smulₛₗ _ _
  rw [hv]
  change h.ip (z ≫ ρ) (Mc.pt (j' (D a))) (Mc.pt (j' (D b))) = _
  rw [← hcore, hDs, hDs, core_sum]
  simp only [hcore]

open Classical in

noncomputable def ev {S : Scheme.{0}} (U : S.Opens) (f : Γ(S, U)) (z : Sp ℂ ⟶ S) : ℂ :=
  if hz : centre z ∈ U then evalAt U f z hz else 0

/- English proof (translation)
Use `letI := anTop S`. Use `IsOpen.mem_nhds ?_ hz` and prove the remaining obligations. Use `TopologicalSpace.isOpen_generateFrom_of_mem ⟨U, 0, Set.univ, isOpen_univ, ?_⟩` and prove the remaining obligations. Use extensionality with `z'`. Simplify using the standard rewrite rules.
-/
theorem mem_nhds_centre {S : Scheme.{0}} (U : S.Opens) (z : Sp ℂ ⟶ S) (hz : centre z ∈ U) :
    {z' : Sp ℂ ⟶ S | centre z' ∈ U} ∈ @nhds _ (anTop S) z := by
  letI := anTop S
  refine IsOpen.mem_nhds ?_ hz
  refine TopologicalSpace.isOpen_generateFrom_of_mem ⟨U, 0, Set.univ, isOpen_univ, ?_⟩
  ext z'
  simp

/- English proof (translation)
Use `letI := anTop S`. Use `continuousAt_def.2 fun A hA => ?_` and prove the remaining obligations. Take `⟨O, hOA, hO, hzO⟩` from `mem_nhds_iff.1 hA`. Establish `ho : IsOpen {z' : Sp ℂ ⟶ S | ∃ hz : centre z' ∈ U, evalAt U f z' hz ∈ O}` using `TopologicalSpace.isOpen_generateFrom_of_mem ⟨U, f, O, hO, rfl⟩`. Use `mem_of_superset (ho.mem_nhds ⟨hz, ?_⟩) ?_` and prove the remaining obligations.

Simplify `hzO` using `[ev, hz]`. Introduce and unpack `z' ⟨hz', h'⟩`. Apply `hOA` to reduce the goal to its premises. Simplify `h'` using `[ev, hz']`.
-/
theorem ev_contAt {S : Scheme.{0}} (U : S.Opens) (f : Γ(S, U)) (z : Sp ℂ ⟶ S) (hz : centre z ∈ U) :
    @ContinuousAt _ _ (anTop S) _ (ev U f) z := by
  letI := anTop S
  refine continuousAt_def.2 fun A hA => ?_
  obtain ⟨O, hOA, hO, hzO⟩ := mem_nhds_iff.1 hA
  have ho : IsOpen {z' : Sp ℂ ⟶ S | ∃ hz : centre z' ∈ U, evalAt U f z' hz ∈ O} :=
    TopologicalSpace.isOpen_generateFrom_of_mem ⟨U, f, O, hO, rfl⟩
  refine mem_of_superset (ho.mem_nhds ⟨hz, ?_⟩) ?_
  · simpa [ev, hz] using hzO
  · rintro z' ⟨hz', h'⟩
    apply hOA
    simpa [ev, hz'] using h'

/- English proof (translation)
Use `haveI : IsOpenImmersion (hU.fromSpec : Sp Γ(S, U) ⟶ S) := inferInstanceAs (IsOpenImmersion hU.fromSpec)`. Take `⟨g, hg⟩` from `exists_lift (R := Γ(S, U)) hU.fromSpec z (by`. Rewrite using `[hU.opensRange_fromSpec]`. Conclude with `hz)`. Use `⟨g, hg, fun f => ?_⟩` and prove the remaining obligations.

Substitute `hg` using the available equality. Take `⟨_, h2⟩` from `point_of_ringHom hU g`. Rewrite using `[ev, dif_pos hz]`. Conclude with `h2 f`.
-/
theorem exists_ev {S : Scheme.{0}} {U : S.Opens} (hU : IsAffineOpen U) (z : Sp ℂ ⟶ S) (hz : centre z ∈ U) :
    ∃ g : Γ(S, U) →+* ℂ, spMap g ≫ (hU.fromSpec : Sp Γ(S, U) ⟶ S) = z ∧ ∀ f, ev U f z = g f := by
  haveI : IsOpenImmersion (hU.fromSpec : Sp Γ(S, U) ⟶ S) := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  obtain ⟨g, hg⟩ := exists_lift (R := Γ(S, U)) hU.fromSpec z (by
    rw [hU.opensRange_fromSpec]
    exact hz)
  refine ⟨g, hg, fun f => ?_⟩
  subst hg
  obtain ⟨_, h2⟩ := point_of_ringHom hU g
  rw [ev, dif_pos hz]
  exact h2 f

/- English proof (translation)
Take `⟨c, hc0, hc⟩` from `tie.cover ⟨p, hall p⟩`. Establish `hy : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k => (Finset.prod_ne_zero_iff.1 hc0) k (Finset.mem_univ k)`. Establish `hreg : ∀ q : Σ k, J k, ∃ (U : X.Opens) (hp : p ∈ U) (t : Γ(X, U)), genMap ξ ⟨p, hall p⟩ (X.presheaf.germ U p hp t) = y q / y ⟨q.1, c q.1⟩`. Introduce and unpack `⟨k, i⟩`. Establish `h` using `hc (Function.update c k i)`.

Simplify using `only at h`. Rewrite `h` using `[← Finset.prod_div_distrib]`. Establish `e1 : ∏ k', y ⟨k', Function.update c k i k'⟩ / y ⟨k', c k'⟩ = y ⟨k, i⟩ / y ⟨k, c k⟩`. Rewrite using `[Finset.prod_eq_single k]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Rewrite using `[Function.update_of_ne hb, div_self (hy b)]`. Simplify using the standard rewrite rules. Rewrite `h` using `[e1]`. Take `⟨σ, hσ⟩` from `h`.

Take `⟨U, hp, t, ht⟩` from `X.presheaf.germ_exist (x := p) σ`. Conclude with `⟨U, hp, t, by rw [ht]; exact hσ⟩`. Use `choose U hp t ht using hreg`. Take `⟨_, ⟨W, hW, rfl⟩, hpW, hWU⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (a := p) (u := ⋂ q, (U q : Set X)) (Set.mem_iInter.2 hp) (isOpen_iInter_of_finite fun q => (U q).2)`. Use `replace hW : IsAffineOpen W := hW`.

Establish `hle : ∀ q, W ≤ U q` using `fun q a ha => Set.mem_iInter.1 (hWU ha) q`. Use `⟨W, hW, hpW, fun q => X.presheaf.map (homOfLE (hle q)).op (t q), fun g z hz => ?_⟩` and prove the remaining obligations. Substitute `hz` using the available equality. Take `⟨hcz, hg⟩` from `point_of_ringHom hW g`. Establish `V : ∀ q : Σ k, J k, ValAt ξ (spMap g ≫ (hW.fromSpec : Sp Γ(X, W) ⟶ X)) (y q / y ⟨q.1, c q.1⟩) (g (X.presheaf.map (homOfLE (hle q)).op (t q)))`.

Introduce `q`. Use `⟨hall _, X.presheaf.germ W _ hcz (X.presheaf.map (homOfLE (hle q)).op (t q)), ?_, hg _⟩` and prove the remaining obligations. Rewrite using `[genMap_germ W (hall _) hcz, ← genMap_germ W (hall p) hpW, TopCat.Presheaf.germ_res_apply]`. Conclude with `ht q`. Establish `h1 : ∀ k, g (X.presheaf.map (homOfLE (hle ⟨k, c k⟩)).op (t ⟨k, c k⟩)) = 1`.

Introduce `k`. Use `V ⟨k, c k⟩` as an intermediate fact. Rewrite `this` using `[div_self (hy k)]`. Conclude with `val_unique tie.gen this (val_one (hall _))`. Use `coords_of_values tie.gen c (fun k => ?_) hy fun c' => ?_` and prove the remaining obligations.

Simplify using `only [h1]`. Conclude with `one_ne_zero`. Rewrite using `[← Finset.prod_div_distrib]`. Use `val_prod (hall _) _ _ _ fun k _ => ?_` and prove the remaining obligations. Simplify using `only [h1, div_one]`.

Conclude with `V ⟨k, c' k⟩`.
-/
theorem exists_coords {X : Scheme.{0}} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
    [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} {ξ : Sp Ω ⟶ X} (hall : ∀ q : X, genPt ξ ⤳ q)
    (tie : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (p : X) :
    ∃ (W : X.Opens) (hW : IsAffineOpen W), p ∈ W ∧ ∃ t : (Σ k, J k) → Γ(X, W), ∀ (g : Γ(X, W) →+* ℂ)
      (z : Sp ℂ ⟶ X), spMap g ≫ (hW.fromSpec : Sp Γ(X, W) ⟶ X) = z → CoordsAt ξ y z fun q => g (t q) := by
  classical
  obtain ⟨c, hc0, hc⟩ := tie.cover ⟨p, hall p⟩
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 hc0) k (Finset.mem_univ k)
  have hreg : ∀ q : Σ k, J k, ∃ (U : X.Opens) (hp : p ∈ U) (t : Γ(X, U)),
      genMap ξ ⟨p, hall p⟩ (X.presheaf.germ U p hp t) = y q / y ⟨q.1, c q.1⟩ := by
    rintro ⟨k, i⟩
    have h := hc (Function.update c k i)
    simp only at h
    rw [← Finset.prod_div_distrib] at h
    have e1 : ∏ k', y ⟨k', Function.update c k i k'⟩ / y ⟨k', c k'⟩ = y ⟨k, i⟩ / y ⟨k, c k⟩ := by
      rw [Finset.prod_eq_single k]
      · simp
      · intro b _ hb
        rw [Function.update_of_ne hb, div_self (hy b)]
      · simp
    rw [e1] at h
    obtain ⟨σ, hσ⟩ := h
    obtain ⟨U, hp, t, ht⟩ := X.presheaf.germ_exist (x := p) σ
    exact ⟨U, hp, t, by rw [ht]; exact hσ⟩
  choose U hp t ht using hreg
  obtain ⟨_, ⟨W, hW, rfl⟩, hpW, hWU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (a := p) (u := ⋂ q, (U q : Set X)) (Set.mem_iInter.2 hp) (isOpen_iInter_of_finite fun q => (U q).2)
  replace hW : IsAffineOpen W := hW
  have hle : ∀ q, W ≤ U q := fun q a ha => Set.mem_iInter.1 (hWU ha) q
  refine ⟨W, hW, hpW, fun q => X.presheaf.map (homOfLE (hle q)).op (t q), fun g z hz => ?_⟩
  subst hz
  obtain ⟨hcz, hg⟩ := point_of_ringHom hW g
  have V : ∀ q : Σ k, J k, ValAt ξ (spMap g ≫ (hW.fromSpec : Sp Γ(X, W) ⟶ X)) (y q / y ⟨q.1, c q.1⟩)
      (g (X.presheaf.map (homOfLE (hle q)).op (t q))) := by
    intro q
    refine ⟨hall _, X.presheaf.germ W _ hcz (X.presheaf.map (homOfLE (hle q)).op (t q)), ?_, hg _⟩
    rw [genMap_germ W (hall _) hcz, ← genMap_germ W (hall p) hpW, TopCat.Presheaf.germ_res_apply]
    exact ht q
  have h1 : ∀ k, g (X.presheaf.map (homOfLE (hle ⟨k, c k⟩)).op (t ⟨k, c k⟩)) = 1 := by
    intro k
    have := V ⟨k, c k⟩
    rw [div_self (hy k)] at this
    exact val_unique tie.gen this (val_one (hall _))
  refine coords_of_values tie.gen c (fun k => ?_) hy fun c' => ?_
  · simp only [h1]
    exact one_ne_zero
  · rw [← Finset.prod_div_distrib]
    refine val_prod (hall _) _ _ _ fun k _ => ?_
    simp only [h1, div_one]
    exact V ⟨k, c' k⟩

end PositivityTheory.Xgn.TorusUniformizationContinuity

open PositivityTheory.Xgn.TorusUniformizationContinuity GlobalTheory.CompanionTheory.Ar.LieVB in
/- English proof (translation)
Introduce `X Ω _ K _ J _ y ξ hall tie G _ _ _ Li _ _ M h Z' ρ G' _ Φ hΦ Xc _ _ _ u _ r β H hH`. Use `letI := anTop Z'`. Use `continuous_iff_continuousAt.2 fun z₀ => ?_` and prove the remaining obligations. Take `⟨W, hW, hpW, t, ht⟩` from `exists_coords hall tie (ρ (centre z₀))`. Take `⟨_, ⟨V, hV, rfl⟩, hzV, hVW⟩` from `Z'.isBasis_affineOpens.exists_subset_of_mem_open (a := centre z₀) (u := ((ρ ⁻¹ᵁ W : Z'.Opens) : Set Z')) hpW (ρ ⁻¹ᵁ W).2`.

Use `replace hV : IsAffineOpen V := hV`. Set `x : Sp Γ(X, W) ⟶ X` to `hW.fromSpec`. Use `haveI : IsOpenImmersion x := inferInstanceAs (IsOpenImmersion hW.fromSpec)`. Set `xV : Sp Γ(Z', V) ⟶ Z'` to `hV.fromSpec`. Set `φ : Γ(X, W) →+* Γ(Z', V)` to `(ρ.appLE W V hVW).hom`.

Establish `hφ : spMap φ ≫ x = xV ≫ ρ` using `IsAffineOpen.SpecMap_appLE_fromSpec ρ hW hV hVW`. Take `⟨E, _, _, ⟨MR⟩⟩` from `lieModel_exists X G Γ(X, W) x`. Use `haveI : Module.Finite Γ(X, W) E := (GlobalTheory.T.lie_model_finite_base_change X G Γ(X, W) x E MR).1`. Take `⟨n, s, hs⟩` from `Module.Finite.exists_fin (R := Γ(X, W)) (M := E)`. Take `⟨c, hc⟩` from `local_formula h hΦ u β H hH x xV φ hφ MR s hs`.

Take `⟨ψ, hψ⟩` from `exists_lift x ξ (by`. Establish `: x.opensRange = W` using `hW.opensRange_fromSpec`. Rewrite using `[this]`. Conclude with `(hall _).mem_open W.2 hpW)`. Take `⟨jξ, hjξ⟩` from `exists_tr x ξ ψ hψ MR M`.

Use `choose F hF hFip using fun i j => h.cont (jξ (s i)) (jξ (s j))`. Set `w : (Sp ℂ ⟶ Z') → (Σ k, J k) → ℂ` to `fun z q => ev V (φ (t q)) z`. Establish `key : ∀ z : Sp ℂ ⟶ Z', centre z ∈ V → (∀ i j, w z ∈ {w | ∃ (z : Sp ℂ ⟶ X) (va vb : epsAt z ⟶ G), CoordsAt ξ y z w ∧ M.ValAt z (jξ (s i)) va ∧ M.ValAt z (jξ (s j)) vb}) ∧ ∀ a b, H z a b = ∑ i, ∑ j, starRingEnd ℂ (ev V (c a i) z) * ev V (c b j) z * F i j (w z)`. Introduce `z hz`. Take `⟨g, hg, hgev⟩` from `exists_ev hV z hz`.

Take `⟨sv, hsv, hform⟩` from `hc g z hg`. Establish `hg' : spMap (g.comp φ) ≫ x = z ≫ ρ`. Rewrite using `[← spMap_cmp, Category.assoc, hφ, ← Category.assoc]`. Conclude with `congrArg (· ≫ ρ) hg`. Establish `hw : CoordsAt ξ y (z ≫ ρ) (w z)`.

Establish `e : w z = fun q => (g.comp φ) (t q)` using `funext fun q => hgev _`. Rewrite using `[e]`. Conclude with `ht _ _ hg'`. Establish `hval : ∀ i, M.ValAt (z ≫ ρ) (jξ (s i)) (sv i)` using `fun i => lie_valAt hall M x MR ψ hψ (s i) _ (hjξ _) _ _ hg' _ (hsv i)`. Use `⟨fun i j => ⟨_, sv i, sv j, hw, hval i, hval j⟩, fun a b => ?_⟩` and prove the remaining obligations.

Rewrite using `[hform]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hgev, hgev, hFip i j _ _ _ _ hw (hval i) (hval j)]`. Establish `hN` using `mem_nhds_centre V z₀ hzV`. Establish `hwc : ContinuousAt w z₀` using `continuousAt_pi.2 fun q => ev_contAt V _ z₀ hzV`.

Establish `hFc : ∀ i j, ContinuousAt (fun z => F i j (w z)) z₀` using `fun i j => (ContinuousWithinAt.comp (hF i j _ ((key z₀ hzV).1 i j)) hwc.continuousWithinAt (fun z hz => (key z hz).1 i j)).continuousAt hN`. Use `continuousAt_pi.2 fun a => continuousAt_pi.2 fun b => ?_` and prove the remaining obligations. Establish `hcont : ContinuousAt (fun z => ∑ i, ∑ j, starRingEnd ℂ (ev V (c a i) z) * ev V (c b j) z * F i j (w z)) z₀`. Use `tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ => ?_` and prove the remaining obligations. Conclude with `((Complex.continuous_conj.continuousAt.comp (ev_contAt V _ z₀ hzV)).mul (ev_contAt V _ z₀ hzV)).mul (hFc i j)`.

Use `hcont.congr ?_` and prove the remaining obligations. Use `filter_upwards [hN] with z hz`. Conclude with `((key z hz).2 a b).symm`.
-/
theorem PositivityTheory.Xgn.torus_uniformization_continuous : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y)
    (Z' : Scheme.{0}) (ρ : Z' ⟶ X) (G' : Over Z') [GrpObj G'] (Φ : G'.left ⟶ G.left), IsGrpPullback G' G ρ Φ →
    ∀ (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc] (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] (r : ℕ)
    (β : Fin r → (Xc →+ ℤ)) (H : (Sp ℂ ⟶ Z') → Matrix (Fin r) (Fin r) ℂ),
    (∀ (zc : Sp ℂ ⟶ Z') (Mz : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)), IsCocharLie Mz →
      ∀ v : Fin r → (epsAt (zc ≫ ρ) ⟶ G), (∀ a, (v a).left = (Mz.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ) →
        H zc = RootHt.gramAt h (zc ≫ ρ) v) →
    @Continuous _ _ (anTop Z') _ H := by
  intro X Ω _ K _ J _ y ξ hall tie G _ _ _ Li _ _ M h Z' ρ G' _ Φ hΦ Xc _ _ _ u _ r β H hH
  letI := anTop Z'
  refine continuous_iff_continuousAt.2 fun z₀ => ?_
  obtain ⟨W, hW, hpW, t, ht⟩ := exists_coords hall tie (ρ (centre z₀))
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVW⟩ := Z'.isBasis_affineOpens.exists_subset_of_mem_open
    (a := centre z₀) (u := ((ρ ⁻¹ᵁ W : Z'.Opens) : Set Z')) hpW (ρ ⁻¹ᵁ W).2
  replace hV : IsAffineOpen V := hV
  let x : Sp Γ(X, W) ⟶ X := hW.fromSpec
  haveI : IsOpenImmersion x := inferInstanceAs (IsOpenImmersion hW.fromSpec)
  let xV : Sp Γ(Z', V) ⟶ Z' := hV.fromSpec
  let φ : Γ(X, W) →+* Γ(Z', V) := (ρ.appLE W V hVW).hom
  have hφ : spMap φ ≫ x = xV ≫ ρ := IsAffineOpen.SpecMap_appLE_fromSpec ρ hW hV hVW
  obtain ⟨E, _, _, ⟨MR⟩⟩ := lieModel_exists X G Γ(X, W) x
  haveI : Module.Finite Γ(X, W) E := (GlobalTheory.T.lie_model_finite_base_change X G Γ(X, W) x E MR).1
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := Γ(X, W)) (M := E)
  obtain ⟨c, hc⟩ := local_formula h hΦ u β H hH x xV φ hφ MR s hs
  obtain ⟨ψ, hψ⟩ := exists_lift x ξ (by
    have : x.opensRange = W := hW.opensRange_fromSpec
    rw [this]
    exact (hall _).mem_open W.2 hpW)
  obtain ⟨jξ, hjξ⟩ := exists_tr x ξ ψ hψ MR M
  choose F hF hFip using fun i j => h.cont (jξ (s i)) (jξ (s j))
  let w : (Sp ℂ ⟶ Z') → (Σ k, J k) → ℂ := fun z q => ev V (φ (t q)) z
  have key : ∀ z : Sp ℂ ⟶ Z', centre z ∈ V →
      (∀ i j, w z ∈ {w | ∃ (z : Sp ℂ ⟶ X) (va vb : epsAt z ⟶ G), CoordsAt ξ y z w ∧ M.ValAt z (jξ (s i)) va ∧
        M.ValAt z (jξ (s j)) vb}) ∧
      ∀ a b, H z a b = ∑ i, ∑ j, starRingEnd ℂ (ev V (c a i) z) * ev V (c b j) z * F i j (w z) := by
    intro z hz
    obtain ⟨g, hg, hgev⟩ := exists_ev hV z hz
    obtain ⟨sv, hsv, hform⟩ := hc g z hg
    have hg' : spMap (g.comp φ) ≫ x = z ≫ ρ := by
      rw [← spMap_cmp, Category.assoc, hφ, ← Category.assoc]
      exact congrArg (· ≫ ρ) hg
    have hw : CoordsAt ξ y (z ≫ ρ) (w z) := by
      have e : w z = fun q => (g.comp φ) (t q) := funext fun q => hgev _
      rw [e]
      exact ht _ _ hg'
    have hval : ∀ i, M.ValAt (z ≫ ρ) (jξ (s i)) (sv i) := fun i =>
      lie_valAt hall M x MR ψ hψ (s i) _ (hjξ _) _ _ hg' _ (hsv i)
    refine ⟨fun i j => ⟨_, sv i, sv j, hw, hval i, hval j⟩, fun a b => ?_⟩
    rw [hform]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hgev, hgev, hFip i j _ _ _ _ hw (hval i) (hval j)]
  have hN := mem_nhds_centre V z₀ hzV
  have hwc : ContinuousAt w z₀ := continuousAt_pi.2 fun q => ev_contAt V _ z₀ hzV
  have hFc : ∀ i j, ContinuousAt (fun z => F i j (w z)) z₀ := fun i j =>
    (ContinuousWithinAt.comp (hF i j _ ((key z₀ hzV).1 i j)) hwc.continuousWithinAt
      (fun z hz => (key z hz).1 i j)).continuousAt hN
  refine continuousAt_pi.2 fun a => continuousAt_pi.2 fun b => ?_
  have hcont : ContinuousAt (fun z => ∑ i, ∑ j, starRingEnd ℂ (ev V (c a i) z) * ev V (c b j) z * F i j (w z)) z₀ := by
    refine tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ => ?_
    exact ((Complex.continuous_conj.continuousAt.comp (ev_contAt V _ z₀ hzV)).mul (ev_contAt V _ z₀ hzV)).mul (hFc i j)
  refine hcont.congr ?_
  filter_upwards [hN] with z hz
  exact ((key z hz).2 a b).symm
