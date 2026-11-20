import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieCombIffProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PowChange

open GlobalTheory.PowLie

variable {R : Type} [CommRing R]

/- English proof (translation)
Establish `h : sc (0 : R) = toUnit _ ≫ zeroPt R`. Use `Over.OverMorphism.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Spec.map _ = Spec.map _ ≫ Spec.map _`. Rewrite using `[← Spec.map_comp]`. Use `congr 1`.

Apply the tactic sequence `ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]`. Rewrite using `[h, Category.assoc, (isTangent_iff v).1 hv, Hom.one_def]`.
-/
theorem sc_zero_comp {G : Over (Sp R)} [GrpObj G] {v : epsR R ⟶ G} (hv : IsTangent v) :
    sc 0 ≫ v = 1 := by
  have h : sc (0 : R) = toUnit _ ≫ zeroPt R := by
    refine Over.OverMorphism.ext ?_
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  rw [h, Category.assoc, (isTangent_iff v).1 hv, Hom.one_def]

/- English proof (translation)
Substitute `hg` using the available equality. Take `⟨w, hw, hw'⟩` from `isLieBasis_pow R G' G j g p v' hv'`. Set `e : Fin g × Fin j ≃ Fin (j * g)` to `(Equiv.prodComm _ _).trans finProdFinEquiv`. Use `⟨w, Matrix.reindex e e (Matrix.blockDiagonal fun _ => M), hw, hw', fun m => ?_, ?_⟩` and prove the remaining obligations. Take `⟨⟨i, k⟩, rfl⟩` from `finProdFinEquiv.surjective m`.

Rewrite using `[isLieComb_iff_prod]`. Use `p.lim.hom_ext fun ⟨i'⟩ => ?_` and prove the remaining obligations. Use `p.hom i'` as an intermediate fact. Express the relevant statement in the definitionally equal form `_ ≫ p.pr i' = _ ≫ p.pr i'`. Use `Eq.trans ?_ (map_prod (IsMonHom.monoidHom (p.pr i') (epsR R)) _ _).symm` and prove the remaining obligations.

Establish `hu' : ∀ (i : Fin j) (k : Fin g), u (finProdFinEquiv (i, k)) ≫ p.pr i' = if i = i' then v k else 1` using `fun i k => hu i i' k`. Rewrite using `[hw', ← finProdFinEquiv.prod_comp, Fintype.prod_prod_type, Finset.prod_eq_single i']`. Establish `h₁ : ∀ k', (IsMonHom.monoidHom (p.pr i') (epsR R)) (sc (Matrix.reindex e e (Matrix.blockDiagonal fun _ => M) (finProdFinEquiv (i, k)) (finProdFinEquiv (i', k'))) ≫ u (finProdFinEquiv (i', k'))) = sc (if i = i' then M k k' else 0) ≫ v k'` using `fun k' => by`. Express the relevant statement in the definitionally equal form `(sc _ ≫ u _) ≫ p.pr i' = _`. Rewrite using `[Category.assoc, hu', if_pos rfl]`.

Use `congr 2`. Simplify using `[e, Matrix.blockDiagonal_apply]`. Rewrite using `[Finset.prod_congr rfl fun k' _ => h₁ k']`. Use `split_ifs with h`. Conclude with `(isLieComb_iff_prod _ _ _).1 (hM k)`.

Conclude with `(Finset.prod_eq_one fun k' _ => sc_zero_comp (hv.1 k')).symm`. Introduce `i'' _ hi`. Use `Finset.prod_eq_one fun k' _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(sc _ ≫ u _) ≫ p.pr i' = _`. Rewrite using `[Category.assoc, hu', if_neg hi, comp_one]`.

Simplify using the standard rewrite rules. Rewrite using `[Matrix.det_reindex_self, Matrix.det_blockDiagonal]`. Simplify using the standard rewrite rules.
-/
theorem exists_block_basis {G' G : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    {j g n : ℕ} (p : Out.IsPowGrp G' G j) (hg : j * g = n) {v v' : Fin g → (epsR R ⟶ G)}
    (hv : IsLieBasis v) (hv' : IsLieBasis v') (M : Matrix (Fin g) (Fin g) R)
    (hM : ∀ i, IsLieComb (M i) v (v' i)) (u : Fin n → (epsR R ⟶ G'))
    (hu : ∀ (i i' : Fin j) (k : Fin g),
      u ((finProdFinEquiv (i, k)).cast hg) ≫ p.pr i' = if i = i' then v k else 1) :
    ∃ (w : Fin n → (epsR R ⟶ G')) (M' : Matrix (Fin n) (Fin n) R), IsLieBasis w ∧
      (∀ (i i' : Fin j) (k : Fin g),
        w ((finProdFinEquiv (i, k)).cast hg) ≫ p.pr i' = if i = i' then v' k else 1) ∧
      (∀ i, IsLieComb (M' i) u (w i)) ∧ M'.det = M.det ^ j := by
  subst hg
  obtain ⟨w, hw, hw'⟩ := isLieBasis_pow R G' G j g p v' hv'
  let e : Fin g × Fin j ≃ Fin (j * g) := (Equiv.prodComm _ _).trans finProdFinEquiv
  refine ⟨w, Matrix.reindex e e (Matrix.blockDiagonal fun _ => M), hw, hw', fun m => ?_, ?_⟩
  · obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective m
    rw [isLieComb_iff_prod]
    refine p.lim.hom_ext fun ⟨i'⟩ => ?_
    have := p.hom i'
    change _ ≫ p.pr i' = _ ≫ p.pr i'
    refine Eq.trans ?_ (map_prod (IsMonHom.monoidHom (p.pr i') (epsR R)) _ _).symm
    have hu' : ∀ (i : Fin j) (k : Fin g), u (finProdFinEquiv (i, k)) ≫ p.pr i' = if i = i' then v k else 1 :=
      fun i k => hu i i' k
    rw [hw', ← finProdFinEquiv.prod_comp, Fintype.prod_prod_type, Finset.prod_eq_single i']
    · have h₁ : ∀ k', (IsMonHom.monoidHom (p.pr i') (epsR R))
          (sc (Matrix.reindex e e (Matrix.blockDiagonal fun _ => M) (finProdFinEquiv (i, k))
            (finProdFinEquiv (i', k'))) ≫ u (finProdFinEquiv (i', k'))) =
          sc (if i = i' then M k k' else 0) ≫ v k' := fun k' => by
        change (sc _ ≫ u _) ≫ p.pr i' = _
        rw [Category.assoc, hu', if_pos rfl]
        congr 2
        simp [e, Matrix.blockDiagonal_apply]
      rw [Finset.prod_congr rfl fun k' _ => h₁ k']
      split_ifs with h
      · exact (isLieComb_iff_prod _ _ _).1 (hM k)
      · exact (Finset.prod_eq_one fun k' _ => sc_zero_comp (hv.1 k')).symm
    · intro i'' _ hi
      refine Finset.prod_eq_one fun k' _ => ?_
      change (sc _ ≫ u _) ≫ p.pr i' = _
      rw [Category.assoc, hu', if_neg hi, comp_one]
    · simp
  · rw [Matrix.det_reindex_self, Matrix.det_blockDiagonal]
    simp

/- English proof (translation)
Substitute `hf` using the available equality. Conclude with `congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) (Scheme.Hom.appLE_comp_appLE f q ⊤ U V (fun _ _ => trivial) h)`.
-/
theorem appLE_constFn {X Y : Scheme.{0}} (q : X ⟶ Sp R) (q' : Y ⟶ Sp R) (f : Y ⟶ X) (hf : f ≫ q = q')
    (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (a : R) :
    (f.appLE U V h).hom (constFn q U a) = constFn q' V a := by
  subst hf
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE f q ⊤ U V (fun _ _ => trivial) h)

/- English proof (translation)
The claim follows from `congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) (Scheme.Hom.appLE_map q (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)`.
-/
theorem res_constFn {X : Scheme.{0}} (q : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    (X.presheaf.map (homOfLE h).op).hom (constFn q U a) = constFn q V a :=
  congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map q (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

/- English proof (translation)
Simplify using `only [constFn, map_pow]`.
-/
theorem constFn_pow {X : Scheme.{0}} (q : X ⟶ Sp R) (U : X.Opens) (a : R) (n : ℕ) :
    constFn q U (a ^ n) = constFn q U a ^ n := by
  simp only [constFn, map_pow]

def constMul {X : Scheme.{0}} (q : X ⟶ Sp R) {L : LB X} (a : R) (s : L.Sec) : L.Sec where
  f i := constFn q _ a * s.f i
  compat i j := by
    rw [map_mul, map_mul, res_constFn, res_constFn, s.compat, mul_left_comm]

/- English proof (translation)
Use `iSup_congr fun i => ?_` and prove the remaining obligations. Establish `h : IsUnit (constFn q (L.U i) a)` using `(ha.map _).map _`. Express the relevant statement in the definitionally equal form `X.basicOpen (constFn q _ a * s.f i) = _`. Rewrite using `[Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ h]`. Conclude with `inf_eq_right.2 (X.basicOpen_le _)`.
-/
theorem nonzeroLocus_constMul {X : Scheme.{0}} (q : X ⟶ Sp R) {L : LB X} {a : R} (ha : IsUnit a) (s : L.Sec) :
    Out.nonzeroLocus (constMul q a s) = Out.nonzeroLocus s := by
  refine iSup_congr fun i => ?_
  have h : IsUnit (constFn q (L.U i) a) := (ha.map _).map _
  change X.basicOpen (constFn q _ a * s.f i) = _
  rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ h]
  exact inf_eq_right.2 (X.basicOpen_le _)

/- English proof (translation)
Introduce `K _ P hg rig hr th hth v hv th' hth' v' hv' a M j y ha hM ⟨p, hj, h₁, h₂, h₃⟩`. Establish `h0 : a ≠ 0`. Introduce and unpack `rfl`. Take `⟨x, -, hx⟩` from `hth' (default : PrimeSpectrum K)`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 hx`.

Rewrite `hi` using `[ha i, constFn, map_zero, map_zero, zero_mul, Scheme.basicOpen_zero]`. Conclude with `hi`. Use `haveI := y.P.isAb.comm`. Use `haveI := P.isAb.comm`. Take `⟨w, M', hw, hw', hM', hdet⟩` from `exists_block_basis p.toIsPowGrp hj hv hv' M hM y.v h₃`.

Use `⟨constMul y.P.A.hom (a ^ j) y.th, fun s => ?_, w, hw, M', ⟨p, hj, h₁, fun jj b h => ?_, hw'⟩, fun _ => rfl, hM', hdet⟩` and prove the remaining obligations. Rewrite using `[nonzeroLocus_constMul _ (pow_ne_zero j h0).isUnit]`. Conclude with `y.th_ne s`. Establish `h₄` using `h₂ jj b h`. Establish `h₅ : ∀ i, ((p.pr i).left.appLE _ _ (h i)).hom (th'.f (jj i)) = constFn y.P.A.hom _ a * ((p.pr i).left.appLE _ _ (h i)).hom (th.f (jj i))` using `fun i => by`.

Rewrite using `[ha, map_mul, appLE_constFn _ _ _ (Over.w (p.pr i))]`. Use `(Finset.prod_congr rfl fun i _ => h₅ i).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Use `(congrArg (_ * ·) h₄).trans ?_` and prove the remaining obligations. Establish `h₆ : resG _ (inf_le_right : (Out.boxLB P.L p.pr).U jj ⊓ y.P.L.U b ≤ _) ((constMul y.P.A.hom (a ^ j) y.th).f b) = constFn y.P.A.hom _ a ^ j * resG _ inf_le_right (y.th.f b)`.

Rewrite using `[← constFn_pow, ← res_constFn y.P.A.hom (inf_le_right : (Out.boxLB P.L p.pr).U jj ⊓ y.P.L.U b ≤ _)]`. Conclude with `map_mul _ _ _`. Conclude with `(mul_left_comm _ _ _).trans (congrArg (_ * ·) h₆.symm)`.
-/
theorem isKeyPow_change : ∀ (K : Type) [Field K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K) (M : Matrix (Fin P.g) (Fin P.g) K) (j : ℕ) (y : KeyIn K), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) → (∀ i, IsLieComb (M i) v (v' i)) → GlobalTheory.KeyPow.IsKeyPow y ⟨P, hg, rig, hr, th, hth, v, hv⟩ j → ∃ (t : y.P.L.Sec) (ht : _) (w : _) (hw : _) (M' : Matrix (Fin y.P.g) (Fin y.P.g) K), GlobalTheory.KeyPow.IsKeyPow ⟨y.P, y.g_pos, y.rig, y.rig_gen, t, ht, w, hw⟩ ⟨P, hg, rig, hr, th', hth', v', hv'⟩ j ∧ (∀ i, t.f i = constFn y.P.A.hom _ (a ^ j) * y.th.f i) ∧ (∀ i, IsLieComb (M' i) y.v (w i)) ∧ M'.det = M.det ^ j := by
  intro K _ P hg rig hr th hth v hv th' hth' v' hv' a M j y ha hM ⟨p, hj, h₁, h₂, h₃⟩
  have h0 : a ≠ 0 := by
    rintro rfl
    obtain ⟨x, -, hx⟩ := hth' (default : PrimeSpectrum K)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    rw [ha i, constFn, map_zero, map_zero, zero_mul, Scheme.basicOpen_zero] at hi
    exact hi
  haveI := y.P.isAb.comm
  haveI := P.isAb.comm
  obtain ⟨w, M', hw, hw', hM', hdet⟩ := exists_block_basis p.toIsPowGrp hj hv hv' M hM y.v h₃
  refine ⟨constMul y.P.A.hom (a ^ j) y.th, fun s => ?_, w, hw, M', ⟨p, hj, h₁, fun jj b h => ?_, hw'⟩,
    fun _ => rfl, hM', hdet⟩
  · rw [nonzeroLocus_constMul _ (pow_ne_zero j h0).isUnit]
    exact y.th_ne s
  · have h₄ := h₂ jj b h
    have h₅ : ∀ i, ((p.pr i).left.appLE _ _ (h i)).hom (th'.f (jj i)) =
        constFn y.P.A.hom _ a * ((p.pr i).left.appLE _ _ (h i)).hom (th.f (jj i)) := fun i => by
      rw [ha, map_mul, appLE_constFn _ _ _ (Over.w (p.pr i))]
    refine (Finset.prod_congr rfl fun i _ => h₅ i).trans ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine (congrArg (_ * ·) h₄).trans ?_
    have h₆ : resG _ (inf_le_right : (Out.boxLB P.L p.pr).U jj ⊓ y.P.L.U b ≤ _)
        ((constMul y.P.A.hom (a ^ j) y.th).f b) =
        constFn y.P.A.hom _ a ^ j * resG _ inf_le_right (y.th.f b) := by
      rw [← constFn_pow, ← res_constFn y.P.A.hom (inf_le_right : (Out.boxLB P.L p.pr).U jj ⊓ y.P.L.U b ≤ _)]
      exact map_mul _ _ _
    exact (mul_left_comm _ _ _).trans (congrArg (_ * ·) h₆.symm)

end GlobalTheory.PowChange
