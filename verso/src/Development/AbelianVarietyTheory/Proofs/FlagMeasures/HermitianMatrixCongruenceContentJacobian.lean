import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelVolMul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelativeLatticeVolumeOfDetValuationStatement

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical Kronecker

namespace GlobalTheory.HL.HermJacobian

section Alg
variable {E : Type} [CommRing E] {m : ℕ}

def coord (m : ℕ) (ω ω' e : E) (h : (ω - ω') * e = 1) :
    (Fin m × Fin m → E) ≃ₗ[E] Matrix (Fin m) (Fin m) E where
  toFun v := Matrix.of fun i j =>
    if i < j then v (i, j) + ω * v (j, i) else if j < i then v (j, i) + ω' * v (i, j) else v (i, j)
  invFun X := fun k =>
    if k.1 < k.2 then X k.1 k.2 - ω * (e * (X k.1 k.2 - X k.2 k.1))
    else if k.2 < k.1 then e * (X k.2 k.1 - X k.1 k.2) else X k.1 k.2
  map_add' v w := by
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c v := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring
  left_inv v := by
    funext ⟨i, j⟩
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp only [Matrix.of_apply, hij, hij.not_gt, if_true, if_false]
      linear_combination (-ω * v (j, i)) * h
    · simp
    · simp only [Matrix.of_apply, hij, hij.not_gt, if_true, if_false]
      linear_combination (v (i, j)) * h
  right_inv X := by
    ext i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp only [Matrix.of_apply, hij, hij.not_gt, if_true, if_false]
      ring
    · simp
    · simp only [Matrix.of_apply, hij, hij.not_gt, if_true, if_false]
      linear_combination (X i j - X j i) * h

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coord_apply (ω ω' e : E) (h : (ω - ω') * e = 1) (v : Fin m × Fin m → E) (i j : Fin m) :
    coord m ω ω' e h v i j =
      if i < j then v (i, j) + ω * v (j, i) else if j < i then v (j, i) + ω' * v (i, j)
      else v (i, j) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coord_symm_apply (ω ω' e : E) (h : (ω - ω') * e = 1) (X : Matrix (Fin m) (Fin m) E)
    (i j : Fin m) :
    (coord m ω ω' e h).symm X (i, j) =
      if i < j then X i j - ω * (e * (X i j - X j i))
      else if j < i then e * (X j i - X i j) else X i j := rfl

def sandwich (B A : Matrix (Fin m) (Fin m) E) :
    Matrix (Fin m) (Fin m) E →ₗ[E] Matrix (Fin m) (Fin m) E where
  toFun X := B * X * A
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

/- English proof (translation)
Set `c : (Fin m × Fin m → E) ≃ₗ[E] Matrix (Fin m) (Fin m) E` to `{ toFun := fun v => Matrix.of fun i j => v (i, j) invFun := fun X k => X k.1 k.2 map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl left_inv := fun _ => rfl right_inv := fun _ => rfl }`. Establish `h : sandwich B A = (c : _ →ₗ[E] _) ∘ₗ Matrix.toLin' (B ⊗ₖ A.transpose) ∘ₗ (c.symm : _ →ₗ[E] _)`. Use `LinearMap.ext fun X => ?_` and prove the remaining obligations. Use extensionality with `i j`. Use `show (B * X * A) i j = ∑ k : Fin m × Fin m, (B i k.1 * A k.2 j) * X k.1 k.2`.

Simplify using `only [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring` and prove the remaining obligations. Rewrite using `[h, LinearMap.det_conj, LinearMap.det_toLin', Matrix.det_kronecker, Matrix.det_transpose, Fintype.card_fin, mul_pow]`.
-/
theorem det_sandwich (B A : Matrix (Fin m) (Fin m) E) :
    LinearMap.det (sandwich B A) = (B.det * A.det) ^ m := by
  let c : (Fin m × Fin m → E) ≃ₗ[E] Matrix (Fin m) (Fin m) E :=
    { toFun := fun v => Matrix.of fun i j => v (i, j)
      invFun := fun X k => X k.1 k.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h : sandwich B A = (c : _ →ₗ[E] _) ∘ₗ Matrix.toLin' (B ⊗ₖ A.transpose) ∘ₗ (c.symm : _ →ₗ[E] _) := by
    refine LinearMap.ext fun X => ?_
    ext i j
    show (B * X * A) i j = ∑ k : Fin m × Fin m, (B i k.1 * A k.2 j) * X k.1 k.2
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [h, LinearMap.det_conj, LinearMap.det_toLin', Matrix.det_kronecker, Matrix.det_transpose,
    Fintype.card_fin, mul_pow]

/- English proof (translation)
Rewrite using `[← LinearMap.det_toMatrix' f, ← LinearMap.det_toMatrix' g, RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Use `congrFun (h (Pi.single j 1)) i` as an intermediate fact. Establish `h2 : (fun k => algebraMap F E ((Pi.single j 1 : ι → F) k)) = Pi.single j 1`.

Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hk]`.

Rewrite `this` using `[h2]`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix'_apply]`. Conclude with `this.symm`.
-/
theorem det_of_comm {F : Type} [Field F] [Algebra F E] {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → F) →ₗ[F] (ι → F)) (g : (ι → E) →ₗ[E] (ι → E))
    (h : ∀ v, g (fun k => algebraMap F E (v k)) = fun k => algebraMap F E (f v k)) :
    algebraMap F E (LinearMap.det f) = LinearMap.det g := by
  rw [← LinearMap.det_toMatrix' f, ← LinearMap.det_toMatrix' g, RingHom.map_det]
  congr 1
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  have h2 : (fun k => algebraMap F E ((Pi.single j 1 : ι → F) k)) = Pi.single j 1 := by
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  rw [h2] at this
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix'_apply]
  exact this.symm

end Alg

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h i j => congrFun (congrFun h i) j, fun h => funext fun i => funext fun j => h i j⟩`.
-/
theorem isHerm_iff (L : LocE F E) {m : ℕ} (X : Matrix (Fin m) (Fin m) E) :
    IsHerm L X ↔ ∀ i j, L.cj (X j i) = X i j :=
  ⟨fun h i j => congrFun (congrFun h i) j, fun h => funext fun i => funext fun j => h i j⟩

/- English proof (translation)
Use `⟨fun h => ?_, fun h => AddSubgroup.subset_closure h⟩` and prove the remaining obligations. Proceed by induction on `h using AddSubgroup.closure_induction with`. Consider the case `mem x hx => exact hx`. Consider the case `zero => exact ⟨(isHerm_iff L _).2 (by simp), fun i j => L.O.zero_mem⟩`. Consider the case `add x y _ _ hx hy`.

Use `⟨(isHerm_iff L _).2 fun i j => ?_, fun i j => L.O.add_mem (hx.2 i j) (hy.2 i j)⟩` and prove the remaining obligations. Rewrite using `[Matrix.add_apply, Matrix.add_apply, map_add, (isHerm_iff L _).1 hx.1, (isHerm_iff L _).1 hy.1]`. Consider the case `neg x _ hx`. Use `⟨(isHerm_iff L _).2 fun i j => ?_, fun i j => L.O.neg_mem (hx.2 i j)⟩` and prove the remaining obligations. Rewrite using `[Matrix.neg_apply, Matrix.neg_apply, map_neg, (isHerm_iff L _).1 hx.1]`.
-/
theorem mem_hermLat_iff (L : LocE F E) (m : ℕ) (X : Matrix (Fin m) (Fin m) E) :
    X ∈ hermLat L m ↔ IsHerm L X ∧ IsIntM L X := by
  refine ⟨fun h => ?_, fun h => AddSubgroup.subset_closure h⟩
  induction h using AddSubgroup.closure_induction with
  | mem x hx => exact hx
  | zero => exact ⟨(isHerm_iff L _).2 (by simp), fun i j => L.O.zero_mem⟩
  | add x y _ _ hx hy =>
    refine ⟨(isHerm_iff L _).2 fun i j => ?_, fun i j => L.O.add_mem (hx.2 i j) (hy.2 i j)⟩
    rw [Matrix.add_apply, Matrix.add_apply, map_add, (isHerm_iff L _).1 hx.1,
      (isHerm_iff L _).1 hy.1]
  | neg x _ hx =>
    refine ⟨(isHerm_iff L _).2 fun i j => ?_, fun i j => L.O.neg_mem (hx.2 i j)⟩
    rw [Matrix.neg_apply, Matrix.neg_apply, map_neg, (isHerm_iff L _).1 hx.1]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [cT, Matrix.mul_apply, map_sum, map_mul]`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`.
-/
theorem cT_mul (L : LocE F E) {m : ℕ} (X Y : Matrix (Fin m) (Fin m) E) :
    cT L (X * Y) = cT L Y * cT L X := by
  ext i j
  simp only [cT, Matrix.mul_apply, map_sum, map_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/- English proof (translation)
Use extensionality with `i j`. Conclude with `L.cj_cj _`.
-/
theorem cT_cT (L : LocE F E) {m : ℕ} (X : Matrix (Fin m) (Fin m) E) : cT L (cT L X) = X := by
  ext i j
  exact L.cj_cj _

/- English proof (translation)
Rewrite using `[AlgEquiv.map_det, ← Matrix.det_transpose]`. Both sides reduce to the same expression.
-/
theorem det_cT (L : LocE F E) {m : ℕ} (X : Matrix (Fin m) (Fin m) E) :
    (cT L X).det = L.cj X.det := by
  rw [AlgEquiv.map_det, ← Matrix.det_transpose]
  rfl

/- English proof (translation)
Unfold `IsHerm at hX ⊢`. Rewrite using `[cT_mul, cT_mul, cT_cT, hX, Matrix.mul_assoc]`.
-/
theorem isHerm_congr (L : LocE F E) {m : ℕ} (A X : Matrix (Fin m) (Fin m) E) (hX : IsHerm L X) :
    IsHerm L (cT L A * X * A) := by
  unfold IsHerm at hX ⊢
  rw [cT_mul, cT_mul, cT_cT, hX, Matrix.mul_assoc]

/- English proof (translation)
Use `(isHerm_iff L _).2 fun i j => ?_` and prove the remaining obligations. Break down `lt_trichotomy i j with hij | rfl | hij` into its components or cases. Simplify using `[coord_apply, hij, hij.not_gt, L.cj_cj]`. Simplify using `[coord_apply]`. Simplify using `[coord_apply, hij, hij.not_gt]`.
-/
theorem isHerm_coord (L : LocE F E) {m : ℕ} {ω e : E} (h : (ω - L.cj ω) * e = 1)
    (v : Fin m × Fin m → F) : IsHerm L (coord m ω (L.cj ω) e h fun k => algebraMap F E (v k)) := by
  refine (isHerm_iff L _).2 fun i j => ?_
  rcases lt_trichotomy i j with hij | rfl | hij
  · simp [coord_apply, hij, hij.not_gt, L.cj_cj]
  · simp [coord_apply]
  · simp [coord_apply, hij, hij.not_gt]

/- English proof (translation)
Establish `he' : (L.cj ω - ω) * L.cj e = 1` using `by simpa [L.cj_cj] using congrArg L.cj h`. Establish `hce : L.cj e = -e` using `by linear_combination (-e) * he' - (L.cj e) * h`. Rewrite using `[← L.cj_fix]`. Take `⟨i, j⟩` from `k`. Establish `h1` using `(isHerm_iff L X).1 hX i j`.

Establish `h2` using `(isHerm_iff L X).1 hX j i`. Rewrite using `[coord_symm_apply]`. Break down `lt_trichotomy i j with hij | rfl | hij` into its components or cases. Simplify using `only [hij, if_true, map_sub, map_mul, hce, h1, h2]`. Take the linear combination `(X i j - X j i) * h`.

Simplify using `[h1]`. Simplify using `only [hij, hij.not_gt, if_true, if_false, map_sub, map_mul, hce, h1, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_coord (L : LocE F E) {m : ℕ} {ω e : E} (h : (ω - L.cj ω) * e = 1)
    (X : Matrix (Fin m) (Fin m) E) (hX : IsHerm L X) (k : Fin m × Fin m) :
    ∃ a : F, algebraMap F E a = (coord m ω (L.cj ω) e h).symm X k := by
  have he' : (L.cj ω - ω) * L.cj e = 1 := by simpa [L.cj_cj] using congrArg L.cj h
  have hce : L.cj e = -e := by linear_combination (-e) * he' - (L.cj e) * h
  rw [← L.cj_fix]
  obtain ⟨i, j⟩ := k
  have h1 := (isHerm_iff L X).1 hX i j
  have h2 := (isHerm_iff L X).1 hX j i
  rw [coord_symm_apply]
  rcases lt_trichotomy i j with hij | rfl | hij
  · simp only [hij, if_true, map_sub, map_mul, hce, h1, h2]
    linear_combination (X i j - X j i) * h
  · simp [h1]
  · simp only [hij, hij.not_gt, if_true, if_false, map_sub, map_mul, hce, h1, h2]
    ring

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L ϖ hϖ m A hA`. Use `⟨mem_hermLat_iff L m, fun B hB => ?_⟩` and prove the remaining obligations. Take `⟨ω, hω, e, he, h⟩` from `GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L`. Establish `hinj` using `GlobalTheory.UnramOrder.algebraMap_inj L`. Establish `hA' : IsUnit (cT L A).det` using `by rw [det_cT]; exact hA.map L.cj`.

Set `φ : Matrix (Fin m) (Fin m) E ≃+ Matrix (Fin m) (Fin m) E` to `{ toFun := fun X => cT L A * X * A invFun := fun X => (cT L A)⁻¹ * X * A⁻¹ left_inv := fun X => by`. Simplify using `only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hA', Matrix.nonsing_inv_mul_cancel_left _ _ hA', Matrix.mul_nonsing_inv _ hA, Matrix.mul_one]`. Use `right_inv := fun X => by`. Simplify using `only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hA', Matrix.nonsing_inv_mul _ hA, Matrix.mul_one]`. Use the proof step `map_add' := fun X Y => by rw [Matrix.mul_add, Matrix.add_mul] }`.

Use `set T := coord m ω (L.cj ω) e h with hT`. Take `⟨r, hr⟩` from `LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F E) (LinearMap.ker_eq_bot.2 hinj)`. Establish `hr' : ∀ a : F, r (algebraMap F E a) = a` using `fun a => LinearMap.congr_fun hr a`. Set `g : (Fin m × Fin m → E) →ₗ[E] (Fin m × Fin m → E)` to `(T.symm : _ →ₗ[E] _) ∘ₗ sandwich (cT L A) A ∘ₗ (T.symm.symm : _ →ₗ[E] _)`. Set `ι : (Fin m × Fin m → F) →ₗ[F] (Fin m × Fin m → E)` to `(Algebra.linearMap F E).compLeft _`.

Set `f : (Fin m × Fin m → F) →ₗ[F] (Fin m × Fin m → F)` to `r.compLeft _ ∘ₗ g.restrictScalars F ∘ₗ ι`. Establish `hfg : ∀ v, g (fun k => algebraMap F E (v k)) = fun k => algebraMap F E (f v k)`. Introduce `v`. Use function extensionality and compare the values at `k`. Take `⟨a, ha⟩` from `exists_coord L h _ (isHerm_congr L A _ (isHerm_coord L h v)) k`.

Establish `h1 : g (fun k => algebraMap F E (v k)) k = algebraMap F E a` using `ha.symm`. Establish `h2 : f v k = r (g (fun k => algebraMap F E (v k)) k)` using `rfl`. Rewrite using `[h2, h1, hr']`. Take `⟨n, hn⟩` from `(L.cj_fix (A.det * L.cj A.det)).1 (by rw [map_mul, L.cj_cj, mul_comm])`. Establish `hn0 : n ≠ 0`.

Introduce and unpack `rfl`. Establish `: Nontrivial E` using `hinj.nontrivial`. Conclude with `(hA.mul (hA.map L.cj)).ne_zero (by rw [← hn, map_zero])`. Establish `hdet : LinearMap.det f = n ^ m`. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[det_of_comm f g hfg, LinearMap.det_conj, det_sandwich, det_cT, map_pow, hn, mul_comm]`. Take `⟨u, hu⟩` from `(GlobalTheory.UnramVal.vE_valuation L ϖ hϖ).2.2.2 n hn0`. Rewrite `hu` using `[hn]`. Set `f' : (Fin m × Fin m → F) ≃ₗ[F] (Fin m × Fin m → F)` to `LinearMap.equivOfIsUnitDet (f := f) (by rw [hdet]; exact (pow_ne_zero _ hn0).isUnit)`. Establish `hf' : (f' : _ →ₗ[F] _) = f` using `LinearMap.coe_equivOfIsUnitDet _`.

Set `W0 : AddSubgroup (Fin m × Fin m → F)` to `AddSubgroup.pi Set.univ fun _ => (𝒪[F]).toAddSubgroup`. Establish `hW0 : ∀ x, x ∈ W0 ↔ ∀ i, x i ∈ 𝒪[F]` using `fun x => by simp [W0, AddSubgroup.mem_pi]`. Take `⟨h1, h2, h3⟩` from `GlobalTheory.T.relative_lattice_volume_of_det_valuation ϖ hϖ (Pi.basisFun F (Fin m × Fin m)) f' (vE L ϖ (A.det * L.cj A.det) * m) (u ^ m) (by`. Rewrite using `[hf', hdet, zpow_mul, zpow_natCast]`. Use `conv_lhs => rw [hu]`.

Rewrite using `[mul_pow]`. Use the proof step `simp) W0 (fun x => by simpa using hW0 x)`. Set `j : (Fin m × Fin m → F) →+ Matrix (Fin m) (Fin m) E` to `T.toAddEquiv.toAddMonoidHom.comp ι.toAddMonoidHom`. Establish `hj : ∀ v, j v = T fun k => algebraMap F E (v k)` using `fun _ => rfl`. Establish `hjinj : Function.Injective j` using `fun v w hvw =>`.

Use function extensionality and compare the values at `fun k => hinj (congrFun (T.injective hvw) k)`. Establish `hcj` using `GlobalTheory.UnramOrder.cj_mem L hω`. Establish `hlat : hermLat L m = W0.map j`. Use extensionality with `X`. Rewrite using `[mem_hermLat_iff, AddSubgroup.mem_map]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hX, hI⟩ choose v hv using exists_coord L h X hX`. Use `⟨v, (hW0 v).2 fun ⟨a, b⟩ => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← GlobalTheory.UnramOrder.algebraMap_mem_iff L, hv, coord_symm_apply] split_ifs`. Conclude with `L.O.sub_mem (hI _ _) (L.O.mul_mem hω (L.O.mul_mem he (L.O.sub_mem (hI _ _) (hI _ _))))`.

Conclude with `L.O.mul_mem he (L.O.sub_mem (hI _ _) (hI _ _))`. Conclude with `hI _ _`. Rewrite using `[hj, funext hv]`. Conclude with `T.apply_symm_apply X`. Introduce and unpack `⟨v, hv, rfl⟩`.

Establish `hv' : ∀ k, algebraMap F E (v k) ∈ L.O` using `fun k => (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 ((hW0 v).1 hv k)`. Use `⟨isHerm_coord L h v, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[hj, coord_apply]`. Use `split_ifs`. Conclude with `L.O.add_mem (hv' _) (L.O.mul_mem hω (hv' _))`.

Conclude with `L.O.add_mem (hv' _) (L.O.mul_mem hcj (hv' _))`. Conclude with `hv' _`. Establish `hmap : (hermLat L m).map φ.toAddMonoidHom = (W0.map f'.toAddEquiv.toAddMonoidHom).map j`. Rewrite using `[hlat, AddSubgroup.map_map, AddSubgroup.map_map]`. Use `congr 1`.

Use `AddMonoidHom.ext fun v => ?_` and prove the remaining obligations. Establish `h4 : f' v = f v` using `LinearMap.congr_fun hf' v`. Use `show cT L A * j v * A = j (f' v)`. Rewrite using `[h4, hj, hj, ← hfg]`. Conclude with `(T.apply_symm_apply _).symm`.

Establish `e1 : ((hermLat L m).map φ.toAddMonoidHom).relIndex (hermLat L m) = (W0.map f'.toAddEquiv.toAddMonoidHom).relIndex W0`. Rewrite using `[hmap, hlat, AddSubgroup.relIndex_map_map_of_injective _ _ hjinj]`. Establish `e2 : (hermLat L m).relIndex ((hermLat L m).map φ.toAddMonoidHom) = W0.relIndex (W0.map f'.toAddEquiv.toAddMonoidHom)`. Rewrite using `[hmap, hlat, AddSubgroup.relIndex_map_map_of_injective _ _ hjinj]`. Take `⟨h5, h6⟩` from `GlobalTheory.HL.ContAut.cont_image (hermLat L m) φ (e1 ▸ h1) (e2 ▸ h2) B hB`.

Use `⟨h5, h6.trans ?_⟩` and prove the remaining obligations. Rewrite using `[← h3, relVol, relVol, e1, e2]`.
-/
theorem cont_congr : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) E), IsUnit A.det → (∀ X, X ∈ hermLat L m ↔ IsHerm L X ∧ IsIntM L X) ∧ ∀ B, IsCO (hermLat L m) B → IsCO (hermLat L m) ((fun X => cT L A * X * A) '' B) ∧ cont (hermLat L m) ((fun X => cT L A * X * A) '' B) = (resQ ϖ : ℝ) ^ (-(vE L ϖ (A.det * L.cj A.det) * m)) * cont (hermLat L m) B := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ m A hA
  refine ⟨mem_hermLat_iff L m, fun B hB => ?_⟩
  obtain ⟨ω, hω, e, he, h⟩ := GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L
  have hinj := GlobalTheory.UnramOrder.algebraMap_inj L
  have hA' : IsUnit (cT L A).det := by rw [det_cT]; exact hA.map L.cj
  let φ : Matrix (Fin m) (Fin m) E ≃+ Matrix (Fin m) (Fin m) E :=
    { toFun := fun X => cT L A * X * A
      invFun := fun X => (cT L A)⁻¹ * X * A⁻¹
      left_inv := fun X => by
        simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hA',
          Matrix.nonsing_inv_mul_cancel_left _ _ hA', Matrix.mul_nonsing_inv _ hA, Matrix.mul_one]
      right_inv := fun X => by
        simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hA',
          Matrix.nonsing_inv_mul _ hA, Matrix.mul_one]
      map_add' := fun X Y => by rw [Matrix.mul_add, Matrix.add_mul] }
  set T := coord m ω (L.cj ω) e h with hT
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F E)
    (LinearMap.ker_eq_bot.2 hinj)
  have hr' : ∀ a : F, r (algebraMap F E a) = a := fun a => LinearMap.congr_fun hr a
  let g : (Fin m × Fin m → E) →ₗ[E] (Fin m × Fin m → E) :=
    (T.symm : _ →ₗ[E] _) ∘ₗ sandwich (cT L A) A ∘ₗ (T.symm.symm : _ →ₗ[E] _)
  let ι : (Fin m × Fin m → F) →ₗ[F] (Fin m × Fin m → E) := (Algebra.linearMap F E).compLeft _
  let f : (Fin m × Fin m → F) →ₗ[F] (Fin m × Fin m → F) :=
    r.compLeft _ ∘ₗ g.restrictScalars F ∘ₗ ι
  have hfg : ∀ v, g (fun k => algebraMap F E (v k)) = fun k => algebraMap F E (f v k) := by
    intro v
    funext k
    obtain ⟨a, ha⟩ := exists_coord L h _ (isHerm_congr L A _ (isHerm_coord L h v)) k
    have h1 : g (fun k => algebraMap F E (v k)) k = algebraMap F E a := ha.symm
    have h2 : f v k = r (g (fun k => algebraMap F E (v k)) k) := rfl
    rw [h2, h1, hr']
  obtain ⟨n, hn⟩ := (L.cj_fix (A.det * L.cj A.det)).1 (by rw [map_mul, L.cj_cj, mul_comm])
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : Nontrivial E := hinj.nontrivial
    exact (hA.mul (hA.map L.cj)).ne_zero (by rw [← hn, map_zero])
  have hdet : LinearMap.det f = n ^ m := by
    apply hinj
    rw [det_of_comm f g hfg, LinearMap.det_conj, det_sandwich, det_cT, map_pow, hn, mul_comm]
  obtain ⟨u, hu⟩ := (GlobalTheory.UnramVal.vE_valuation L ϖ hϖ).2.2.2 n hn0
  rw [hn] at hu
  let f' : (Fin m × Fin m → F) ≃ₗ[F] (Fin m × Fin m → F) :=
    LinearMap.equivOfIsUnitDet (f := f) (by rw [hdet]; exact (pow_ne_zero _ hn0).isUnit)
  have hf' : (f' : _ →ₗ[F] _) = f := LinearMap.coe_equivOfIsUnitDet _
  let W0 : AddSubgroup (Fin m × Fin m → F) := AddSubgroup.pi Set.univ fun _ => (𝒪[F]).toAddSubgroup
  have hW0 : ∀ x, x ∈ W0 ↔ ∀ i, x i ∈ 𝒪[F] := fun x => by simp [W0, AddSubgroup.mem_pi]
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.relative_lattice_volume_of_det_valuation ϖ hϖ (Pi.basisFun F (Fin m × Fin m)) f'
    (vE L ϖ (A.det * L.cj A.det) * m) (u ^ m) (by
      rw [hf', hdet, zpow_mul, zpow_natCast]
      conv_lhs => rw [hu]
      rw [mul_pow]
      simp) W0 (fun x => by simpa using hW0 x)
  let j : (Fin m × Fin m → F) →+ Matrix (Fin m) (Fin m) E :=
    T.toAddEquiv.toAddMonoidHom.comp ι.toAddMonoidHom
  have hj : ∀ v, j v = T fun k => algebraMap F E (v k) := fun _ => rfl
  have hjinj : Function.Injective j := fun v w hvw =>
    funext fun k => hinj (congrFun (T.injective hvw) k)
  have hcj := GlobalTheory.UnramOrder.cj_mem L hω
  have hlat : hermLat L m = W0.map j := by
    ext X
    rw [mem_hermLat_iff, AddSubgroup.mem_map]
    constructor
    · rintro ⟨hX, hI⟩
      choose v hv using exists_coord L h X hX
      refine ⟨v, (hW0 v).2 fun ⟨a, b⟩ => ?_, ?_⟩
      · rw [← GlobalTheory.UnramOrder.algebraMap_mem_iff L, hv, coord_symm_apply]
        split_ifs
        · exact L.O.sub_mem (hI _ _) (L.O.mul_mem hω (L.O.mul_mem he (L.O.sub_mem (hI _ _) (hI _ _))))
        · exact L.O.mul_mem he (L.O.sub_mem (hI _ _) (hI _ _))
        · exact hI _ _
      · rw [hj, funext hv]
        exact T.apply_symm_apply X
    · rintro ⟨v, hv, rfl⟩
      have hv' : ∀ k, algebraMap F E (v k) ∈ L.O := fun k =>
        (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 ((hW0 v).1 hv k)
      refine ⟨isHerm_coord L h v, fun a b => ?_⟩
      rw [hj, coord_apply]
      split_ifs
      · exact L.O.add_mem (hv' _) (L.O.mul_mem hω (hv' _))
      · exact L.O.add_mem (hv' _) (L.O.mul_mem hcj (hv' _))
      · exact hv' _
  have hmap : (hermLat L m).map φ.toAddMonoidHom
      = (W0.map f'.toAddEquiv.toAddMonoidHom).map j := by
    rw [hlat, AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    refine AddMonoidHom.ext fun v => ?_
    have h4 : f' v = f v := LinearMap.congr_fun hf' v
    show cT L A * j v * A = j (f' v)
    rw [h4, hj, hj, ← hfg]
    exact (T.apply_symm_apply _).symm
  have e1 : ((hermLat L m).map φ.toAddMonoidHom).relIndex (hermLat L m)
      = (W0.map f'.toAddEquiv.toAddMonoidHom).relIndex W0 := by
    rw [hmap, hlat, AddSubgroup.relIndex_map_map_of_injective _ _ hjinj]
  have e2 : (hermLat L m).relIndex ((hermLat L m).map φ.toAddMonoidHom)
      = W0.relIndex (W0.map f'.toAddEquiv.toAddMonoidHom) := by
    rw [hmap, hlat, AddSubgroup.relIndex_map_map_of_injective _ _ hjinj]
  obtain ⟨h5, h6⟩ := GlobalTheory.HL.ContAut.cont_image (hermLat L m) φ (e1 ▸ h1) (e2 ▸ h2) B hB
  refine ⟨h5, h6.trans ?_⟩
  rw [← h3, relVol, relVol, e1, e2]

end GlobalTheory.HL.HermJacobian
