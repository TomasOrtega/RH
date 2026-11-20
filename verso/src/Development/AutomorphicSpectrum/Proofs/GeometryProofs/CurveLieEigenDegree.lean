import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveFamilyFormalGermStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FamilyGivesConjugateLieDataStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermLieBasisStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalIsomorphismTransportStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj.TopH2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}

/- English proof (translation)
Use `show f ≫ (toUnit T ≫ η[G]) = toUnit T' ≫ η[G]`. Rewrite using `[← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]`.
-/
theorem comp_one_over {G T T' : Over X0} [GrpObj G] (f : T' ⟶ T) : f ≫ (1 : T ⟶ G) = 1 := by
  show f ≫ (toUnit T ≫ η[G]) = toUnit T' ≫ η[G]
  rw [← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]

/- English proof (translation)
The claim follows from `| 0, u => by simp only [List.ofFn_zero, List.prod_nil]; exact comp_one_over f | m + 1, u => by rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, MonObj.comp_mul, comp_prod_ofFn f (fun l => u l.succ)]`.
-/
theorem comp_prod_ofFn {G T T' : Over X0} [GrpObj G] (f : T' ⟶ T) :
    ∀ {m : ℕ} (u : Fin m → (T ⟶ G)), f ≫ (List.ofFn u).prod = (List.ofFn fun l => f ≫ u l).prod
  | 0, u => by simp only [List.ofFn_zero, List.prod_nil]; exact comp_one_over f
  | m + 1, u => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, MonObj.comp_mul,
      comp_prod_ofFn f (fun l => u l.succ)]

/- English proof (translation)
Simplify using `only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]`.
-/
theorem spMap_comp_eq {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (a : B →+* C) (b : A →+* B) (c : D →+* C) (d : A →+* D) (h : a.comp b = c.comp d) :
    spMap a ≫ spMap b = spMap c ≫ spMap d := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

section Rings

variable {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R')

/- English proof (translation)
Apply the tactic sequence `refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem dualMap_comp_algebraMap :
    (GlobalTheory.CompanionTheory.Ar.dualMap f).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp f := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Apply the tactic sequence `refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;>`. Simplify using `[GlobalTheory.CompanionTheory.Ar.dualMap, ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, mul_comm]`.
-/
theorem dualMap_comp_epsMul (c : R) :
    (GlobalTheory.CompanionTheory.Ar.dualMap f).comp (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul c) =
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (f c)).comp (GlobalTheory.CompanionTheory.Ar.dualMap f) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [GlobalTheory.CompanionTheory.Ar.dualMap, ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, mul_comm]

/- English proof (translation)
Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Simplify using `[GlobalTheory.CompanionTheory.Ar.dualMap]`.
-/
theorem fst_comp_dualMap :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (GlobalTheory.CompanionTheory.Ar.dualMap f) =
      f.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => ?_
  simp [GlobalTheory.CompanionTheory.Ar.dualMap]

end Rings

variable (t : SAB H X0)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => ⟨Over.w w, h⟩, fun h => h.2⟩`.
-/
theorem isTanAt_iff {S : Type} [CommRing S] (x : Sp S ⟶ X0) (w : GlobalTheory.CompanionTheory.Ar.epsAt x ⟶ t.G) :
    GlobalTheory.CompanionTheory.Ar.IsTanAt t.G x w ↔ IsTanAtG t x w.left :=
  ⟨fun h => ⟨Over.w w, h⟩, fun h => h.2⟩

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, h.1, ← Category.assoc, ← Category.assoc, spMap_comp_eq _ _ _ _ (dualMap_comp_algebraMap f)]`. Rewrite using `[← Category.assoc, spMap_comp_eq _ _ _ _ (fst_comp_dualMap f), Category.assoc, h.2]`. Use `comp_one_over (G := t.G) (Over.homMk (U := Over.mk (spMap f ≫ x)) (V := Over.mk x) (spMap f) rfl)` as an intermediate fact. Rewrite using `[← this, Over.comp_left]`.

Both sides reduce to the same expression.
-/
theorem isTanAtG_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {x : Sp R ⟶ X0}
    {v : Sp (DualNumber R) ⟶ t.G.left} (h : IsTanAtG t x v) :
    IsTanAtG t (spMap f ≫ x) (spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ v) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h.1, ← Category.assoc, ← Category.assoc,
      spMap_comp_eq _ _ _ _ (dualMap_comp_algebraMap f)]
  · rw [← Category.assoc, spMap_comp_eq _ _ _ _ (fst_comp_dualMap f), Category.assoc, h.2]
    have := comp_one_over (G := t.G) (Over.homMk (U := Over.mk (spMap f ≫ x)) (V := Over.mk x) (spMap f) rfl)
    rw [← this, Over.comp_left]
    rfl

/- English proof (translation)
Take `⟨u, hu, hw⟩` from `h`. Set `k : tEpsG (spMap f ≫ x) ⟶ tEpsG x` to `Over.homMk (spMap (GlobalTheory.CompanionTheory.Ar.dualMap f)) (by`. Simplify using `only [Over.mk_hom]`. Rewrite using `[← Category.assoc, ← Category.assoc, spMap_comp_eq _ _ _ _ (dualMap_comp_algebraMap f)])`. Use `⟨fun l => k ≫ u l, fun l => ?_, ?_⟩` and prove the remaining obligations.

Use `show spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ (u l).left = _`. Rewrite using `[hu l, ← Category.assoc, ← Category.assoc, spMap_comp_eq _ _ _ _ (dualMap_comp_epsMul f (cf l))]`. Rewrite using `[← comp_prod_ofFn, Over.comp_left, hw]`. Both sides reduce to the same expression.
-/
theorem isCombAtG_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {x : Sp R ⟶ X0} {m : ℕ}
    {v : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} {cf : Fin m → R} {w : Sp (DualNumber R) ⟶ t.G.left}
    (h : IsCombAtG t x v cf w) :
    IsCombAtG t (spMap f ≫ x) (fun l => spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ v l) (fun l => f (cf l))
      (spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ w) := by
  obtain ⟨u, hu, hw⟩ := h
  let k : tEpsG (spMap f ≫ x) ⟶ tEpsG x := Over.homMk (spMap (GlobalTheory.CompanionTheory.Ar.dualMap f)) (by
    simp only [Over.mk_hom]
    rw [← Category.assoc, ← Category.assoc, spMap_comp_eq _ _ _ _ (dualMap_comp_algebraMap f)])
  refine ⟨fun l => k ≫ u l, fun l => ?_, ?_⟩
  · show spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ (u l).left = _
    rw [hu l, ← Category.assoc, ← Category.assoc,
      spMap_comp_eq _ _ _ _ (dualMap_comp_epsMul f (cf l))]
  · rw [← comp_prod_ofFn, Over.comp_left, hw]
    rfl

/- English proof (translation)
The claim follows from `| 0, c => by simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty] have h := M.add 0 0 rw [add_zero] at h exact (mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)).symm | m + 1, c => by rw [List.ofFn_succ, List.prod_cons, pt_sum M (fun l => c l.su …`.
-/
theorem pt_sum {S : Type} [CommRing S] {x : Sp S ⟶ X0} {V : Type} [AddCommGroup V] [Module S V]
    (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G x V) :
    ∀ {m : ℕ} (c : Fin m → V), (List.ofFn fun l => M.pt (c l)).prod = M.pt (∑ l, c l)
  | 0, c => by
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
    have h := M.add 0 0
    rw [add_zero] at h
    exact (mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)).symm
  | m + 1, c => by
    rw [List.ofFn_succ, List.prod_cons, pt_sum M (fun l => c l.succ), Fin.sum_univ_succ, M.add]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, hw⟩`. Establish `hu' : u = fun l => M.pt (cf l • b l)`. Use function extensionality and compare the values at `fun l => Over.OverMorphism.ext (by rw [hu l, M.smul]; rfl)`. Rewrite using `[← hw, hu', pt_sum]`.

Introduce `hw`. Conclude with `⟨fun l => M.pt (cf l • b l), fun l => by rw [M.smul]; rfl, by rw [pt_sum, hw]⟩`.
-/
theorem isCombAtG_iff_lie {S : Type} [CommRing S] {x : Sp S ⟶ X0} {V : Type} [AddCommGroup V] [Module S V]
    (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G x V) {m : ℕ} (b : Fin m → V) (cf : Fin m → S)
    (w : Sp (DualNumber S) ⟶ t.G.left) :
    IsCombAtG t x (fun l => (M.pt (b l)).left) cf w ↔ w = (M.pt (∑ l, cf l • b l)).left := by
  constructor
  · rintro ⟨u, hu, hw⟩
    have hu' : u = fun l => M.pt (cf l • b l) :=
      funext fun l => Over.OverMorphism.ext (by rw [hu l, M.smul]; rfl)
    rw [← hw, hu', pt_sum]
  · intro hw
    exact ⟨fun l => M.pt (cf l • b l), fun l => by rw [M.smul]; rfl, by rw [pt_sum, hw]⟩

/- English proof (translation)
Introduce `E _ _ _ H _ hbar X0 t hPow K _ p _ _ C z Y hne hFib V _ _ M r hr`. Take `⟨d, F, g, hgB, hfam⟩` from `GlobalTheory.T.curve_family_formal_germ E H hbar X0 t hPow K p C z Y hFib`. Take `⟨D, hDρ, hDlie⟩` from `GlobalTheory.T.family_gives_conjugate_lie_data K C p d (𝓞 E) F hne`. Take `⟨e, hecomb, heact⟩` from `GlobalTheory.T.formal_germ_lie_basis E H hbar X0 t K z d g V M`. Use `⟨d, D, e, fun i v => ?_, fun a v => by rw [heact r hr a v, hDρ a, hgB]⟩` and prove the remaining obligations.

Take `⟨gi, hgi⟩` from `hfam i`. Take `⟨hΦΨ, hΨΦ, -⟩` from `GlobalTheory.T.formal_isomorphism_transport K d (𝓞 E) F.B (F.BK i) (F.φ i) (F.ψ i) (F.lam i) (F.iso i)`. Establish `hgen : spMap (C.v i).valuationSubring.subtype ≫ Y.x i = z` using `Y.gen i`. Establish `htan : ∀ l, IsTanAtG t z (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l)` using `fun l => by`. Establish `h0` using `isTanAtG_map t (C.v i).valuationSubring.subtype (gi.tan l)`.

Rewrite `h0` using `[hgen]`. Then use the resulting hypothesis. Use `choose c hc using fun l => M.onto (Over.homMk _ (htan l).1) ((isTanAt_iff t z _).2 (htan l))`. Establish `hcl : ∀ l, (M.pt (c l)).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l` using `fun l => by rw [hc l]; rfl`. Establish `hec : ∀ l j, e (c l) j = lin (F.φ i) 1 j l`. Introduce `l`.

Establish `hw : IsTanAtG t z (M.pt (c l)).left` using `(isTanAt_iff t z _).1 (M.tan _)`. Use `(g.basis _ hw).unique (hecomb (c l)) (by rw [hcl]; exact hgi l)` as an intermediate fact. Conclude with `fun j => congrFun this j`. Establish `key : ∀ (a : Fin d → (C.v i).valuationSubring) (w : Sp (DualNumber (C.v i).valuationSubring) ⟶ t.G.left), IsCombAtG t (Y.x i) gi.tg a w → spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ w = (M.pt (∑ l, (a l : K) • c l)).left ∧ e (∑ l, (a l : K) …`. Introduce `a w hw`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `isCombAtG_map t (C.v i).valuationSubring.subtype hw`. Rewrite `h1` using `[hgen]`. Establish `h2 : (fun l => spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l) = fun l => (M.pt (c l)).left` using `funext fun l => (hcl l).symm`. Rewrite `h1` using `[h2]`.

Conclude with `(isCombAtG_iff_lie t M c _ _).1 h1`. Use function extensionality and compare the values at `j`. Simplify using `[map_sum, Matrix.mulVec, dotProduct, hec, mul_comm]`. Prove the components needed by the constructor for the conclusion. Introduce `hv`.

Establish `hsub : Y.lieLat M i ≤ (D.lie i).comap e.toLinearMap.toAddMonoidHom`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `v ⟨w, hw, hvw⟩`. Take `⟨a, ha, -⟩` from `gi.basis w.left ((isTanAt_iff t (Y.x i) w).1 hw)`. Take `⟨hbc, hea⟩` from `key a w.left ha`.

Establish `hv' : v = ∑ l, (a l : K) • c l` using `M.inj (Over.OverMorphism.ext (hvw.trans hbc))`. Use `show e v ∈ D.lie i`. Rewrite using `[hDlie, hv', hea, Matrix.mulVec_mulVec, hΨΦ, Matrix.one_mulVec]`. Introduce `j`. Conclude with `(a j).2`.

Conclude with `hsub hv`. Introduce `hv`. Establish `hint : ∀ j, C.v i ((lin (F.ψ i) 1).mulVec (e v) j) ≤ 1` using `(hDlie i (e v)).1 hv`. Set `a : Fin d → (C.v i).valuationSubring` to `fun j => ⟨_, hint j⟩`. Take `⟨Vi, _, _, ⟨Mi⟩⟩` from `GlobalTheory.CompanionTheory.Ar.lieModel_exists X0 t.G (C.v i).valuationSubring (Y.x i)`.

Use `choose b hb using fun l => Mi.onto (Over.homMk (gi.tg l) (gi.tan l).1) ((isTanAt_iff t (Y.x i) _).2 (gi.tan l))`. Establish `hbl : ∀ l, (Mi.pt (b l)).left = gi.tg l` using `fun l => by rw [hb l]; rfl`. Establish `hcomb : IsCombAtG t (Y.x i) gi.tg a (Mi.pt (∑ l, a l • b l)).left`. Establish `h3` using `(isCombAtG_iff_lie t Mi b a (Mi.pt (∑ l, a l • b l)).left).2 rfl`. Establish `h2 : (fun l => (Mi.pt (b l)).left) = gi.tg` using `funext hbl`.

Rewrite `h3` using `[h2]`. Then use the resulting hypothesis. Take `⟨hbc, hea⟩` from `key a _ hcomb`. Establish `hsum : ∑ l, (a l : K) • c l = v`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[hea]`.

Use `show (lin (F.φ i) 1).mulVec ((lin (F.ψ i) 1).mulVec (e v)) = e v`. Rewrite using `[Matrix.mulVec_mulVec, hΦΨ, Matrix.one_mulVec]`. Use `AddSubgroup.subset_closure ⟨Mi.pt (∑ l, a l • b l), Mi.tan _, ?_⟩` and prove the remaining obligations. Rewrite using `[← hsum]`. Conclude with `hbc.symm`.
-/
theorem lieLat_conjData : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (C : ACurve K) (z : Sp K ⟶ X0) (Y : CurveIn C z), Nonempty C.I → (∀ i, FibPF t (GlobalTheory.CompanionTheory.Ar.centre (Y.x i))) → ∀ (V : Type) [AddCommGroup V] [Module K V] (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G z V) (r : 𝓞 E →+* Module.End K V), M.IsActOf t.act.act r → ∃ (d : ℕ) (D : ConjData C p (𝓞 E) d) (e : V ≃ₗ[K] (Fin d → K)), (∀ i v, v ∈ Y.lieLat M i ↔ e v ∈ D.lie i) ∧ ∀ a v, e (r a v) = (D.ρ a).mulVec (e v) := by
  intro E _ _ _ H _ hbar X0 t hPow K _ p _ _ C z Y hne hFib V _ _ M r hr
  obtain ⟨d, F, g, hgB, hfam⟩ := GlobalTheory.T.curve_family_formal_germ E H hbar X0 t hPow K p C z Y hFib
  obtain ⟨D, hDρ, hDlie⟩ := GlobalTheory.T.family_gives_conjugate_lie_data K C p d (𝓞 E) F hne
  obtain ⟨e, hecomb, heact⟩ := GlobalTheory.T.formal_germ_lie_basis E H hbar X0 t K z d g V M
  refine ⟨d, D, e, fun i v => ?_, fun a v => by rw [heact r hr a v, hDρ a, hgB]⟩
  obtain ⟨gi, hgi⟩ := hfam i
  obtain ⟨hΦΨ, hΨΦ, -⟩ := GlobalTheory.T.formal_isomorphism_transport K d (𝓞 E) F.B (F.BK i) (F.φ i) (F.ψ i) (F.lam i) (F.iso i)
  have hgen : spMap (C.v i).valuationSubring.subtype ≫ Y.x i = z := Y.gen i
  have htan : ∀ l, IsTanAtG t z (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l) :=
    fun l => by
      have h0 := isTanAtG_map t (C.v i).valuationSubring.subtype (gi.tan l)
      rwa [hgen] at h0
  choose c hc using fun l => M.onto (Over.homMk _ (htan l).1) ((isTanAt_iff t z _).2 (htan l))
  have hcl : ∀ l, (M.pt (c l)).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l :=
    fun l => by rw [hc l]; rfl
  have hec : ∀ l j, e (c l) j = lin (F.φ i) 1 j l := by
    intro l
    have hw : IsTanAtG t z (M.pt (c l)).left := (isTanAt_iff t z _).1 (M.tan _)
    have := (g.basis _ hw).unique (hecomb (c l)) (by rw [hcl]; exact hgi l)
    exact fun j => congrFun this j
  have key : ∀ (a : Fin d → (C.v i).valuationSubring)
      (w : Sp (DualNumber (C.v i).valuationSubring) ⟶ t.G.left), IsCombAtG t (Y.x i) gi.tg a w →
      spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ w = (M.pt (∑ l, (a l : K) • c l)).left ∧
        e (∑ l, (a l : K) • c l) = (lin (F.φ i) 1).mulVec (fun l => (a l : K)) := by
    intro a w hw
    refine ⟨?_, ?_⟩
    · have h1 := isCombAtG_map t (C.v i).valuationSubring.subtype hw
      rw [hgen] at h1
      have h2 : (fun l => spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l) =
          fun l => (M.pt (c l)).left := funext fun l => (hcl l).symm
      rw [h2] at h1
      exact (isCombAtG_iff_lie t M c _ _).1 h1
    · funext j
      simp [map_sum, Matrix.mulVec, dotProduct, hec, mul_comm]
  constructor
  · intro hv
    have hsub : Y.lieLat M i ≤ (D.lie i).comap e.toLinearMap.toAddMonoidHom := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro v ⟨w, hw, hvw⟩
      obtain ⟨a, ha, -⟩ := gi.basis w.left ((isTanAt_iff t (Y.x i) w).1 hw)
      obtain ⟨hbc, hea⟩ := key a w.left ha
      have hv' : v = ∑ l, (a l : K) • c l := M.inj (Over.OverMorphism.ext (hvw.trans hbc))
      show e v ∈ D.lie i
      rw [hDlie, hv', hea, Matrix.mulVec_mulVec, hΨΦ, Matrix.one_mulVec]
      intro j
      exact (a j).2
    exact hsub hv
  · intro hv
    have hint : ∀ j, C.v i ((lin (F.ψ i) 1).mulVec (e v) j) ≤ 1 := (hDlie i (e v)).1 hv
    let a : Fin d → (C.v i).valuationSubring := fun j => ⟨_, hint j⟩
    obtain ⟨Vi, _, _, ⟨Mi⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists X0 t.G (C.v i).valuationSubring (Y.x i)
    choose b hb using fun l =>
      Mi.onto (Over.homMk (gi.tg l) (gi.tan l).1) ((isTanAt_iff t (Y.x i) _).2 (gi.tan l))
    have hbl : ∀ l, (Mi.pt (b l)).left = gi.tg l := fun l => by rw [hb l]; rfl
    have hcomb : IsCombAtG t (Y.x i) gi.tg a (Mi.pt (∑ l, a l • b l)).left := by
      have h3 := (isCombAtG_iff_lie t Mi b a (Mi.pt (∑ l, a l • b l)).left).2 rfl
      have h2 : (fun l => (Mi.pt (b l)).left) = gi.tg := funext hbl
      rwa [h2] at h3
    obtain ⟨hbc, hea⟩ := key a _ hcomb
    have hsum : ∑ l, (a l : K) • c l = v := by
      apply e.injective
      rw [hea]
      show (lin (F.φ i) 1).mulVec ((lin (F.ψ i) 1).mulVec (e v)) = e v
      rw [Matrix.mulVec_mulVec, hΦΨ, Matrix.one_mulVec]
    refine AddSubgroup.subset_closure ⟨Mi.pt (∑ l, a l • b l), Mi.tan _, ?_⟩
    rw [← hsum]
    exact hbc.symm

end GlobalTheory.CompanionTheory.Ar.Conj.TopH2
