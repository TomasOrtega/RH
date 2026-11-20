import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PointsSumsEqProducts
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMulEquivPointsOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section

namespace GlobalTheory.LamF.Ind

open GlobalTheory.SqZero GlobalTheory.LieComb

section General

variable {R : Type} [CommRing R] {S : Scheme.{0}} (f : Sp R ⟶ S)

def scaleOver (c : R) : Over.mk ((epsR R).hom ≫ f) ⟶ Over.mk ((epsR R).hom ≫ f) :=
  (Over.map f).map (Chart.spMap (epsTo R (TrivSqZeroExt.inr c : DualNumber R)
    (TrivSqZeroExt.inr_mul_inr _ _ _)) : epsR R ⟶ epsR R)

variable {f} {G : Over S} {G' : Over (Sp R)} [GrpObj G] [GrpObj G'] [IsCommMonObj G]
  [IsCommMonObj G'] {φ : G'.left ⟶ G.left}

/- English proof (translation)
Use `(map_prod Φ _ _).trans (Finset.prod_congr rfl fun i _ => ?_)` and prove the remaining obligations. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[hΦ, Over.comp_left, Over.comp_left, hΦ, Category.assoc]`. Both sides reduce to the same expression.
-/
theorem push_tanExp (Φ : (epsR R ⟶ G') ≃* (Over.mk ((epsR R).hom ≫ f) ⟶ G))
    (hΦ : ∀ x, (Φ x).left = x.left ≫ φ) {n : ℕ} (v : Fin n → (epsR R ⟶ G')) (c : Fin n → R) :
    Φ (tanExp v c) = ∏ i, scaleOver f (c i) ≫ Φ (v i) := by
  refine (map_prod Φ _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
  apply Over.OverMorphism.ext
  rw [hΦ, Over.comp_left, Over.comp_left, hΦ, Category.assoc]
  rfl

/- English proof (translation)
The claim follows from `map_prod (MonoidHom.mk' (fun y : T ⟶ G => y ≫ F) fun a b => MonObj.mul_comp a b F) x s`.
-/
theorem prod_comp {T G₁ : Over S} [GrpObj G₁] [IsCommMonObj G₁] (F : G ⟶ G₁) [IsMonHom F]
    {J : Type} (s : Finset J) (x : J → (T ⟶ G)) : (∏ i ∈ s, x i) ≫ F = ∏ i ∈ s, x i ≫ F :=
  map_prod (MonoidHom.mk' (fun y : T ⟶ G => y ≫ F) fun a b => MonObj.mul_comp a b F) x s

omit [GrpObj G] [IsCommMonObj G] in

/- English proof (translation)
Establish `h₁ : tanExp v (N • c) = tanExp v 0`. Express the relevant statement in the definitionally equal form `(combHom hv.1 (N • c)).toMul = (combHom hv.1 0).toMul`. Rewrite using `[map_nsmul, map_zero, toMul_nsmul]`. Conclude with `h`. Establish `h₂` using `(isLieBasisOver_self hv).1 _ _ h₁`.

Use function extensionality and compare the values at `i`. Use `congrFun h₂ i` as an intermediate fact. Simplify `this` using `[hN.ne']`.
-/
theorem eq_zero_of_pow {K : Type} [Field K] [CharZero K] {A : Over (Sp K)} [GrpObj A]
    [IsCommMonObj A] {n : ℕ} {v : Fin n → (epsR K ⟶ A)} (hv : IsLieBasis v) {c : Fin n → K}
    {N : ℕ} (hN : 0 < N) (h : tanExp v c ^ N = 1) : c = 0 := by
  have h₁ : tanExp v (N • c) = tanExp v 0 := by
    change (combHom hv.1 (N • c)).toMul = (combHom hv.1 0).toMul
    rw [map_nsmul, map_zero, toMul_nsmul]
    exact h
  have h₂ := (isLieBasisOver_self hv).1 _ _ h₁
  funext i
  have := congrFun h₂ i
  simpa [hN.ne'] using this

end General

/- English proof (translation)
Introduce `E _ _ _ _ H l cf _ nΨ n' f o La hg L hL hdet`. Take `⟨-, -, -, hB, hΨ, h', -, -, -, -, -, -, -, ⟨hmΨ, hm', N, ψΨ, ψ', hN, -, hsum⟩, -⟩` from `hg`. Take `⟨hsrc, -, hw, -⟩` from `hL`. Take `⟨c, hc0, hc⟩` from `Matrix.exists_vecMul_eq_zero_iff.2 hdet`. Use `choose w hw hwc using hw`.

Take `⟨ΦB, hΦB⟩` from `exists_mulEquiv_points_of_isGrpPullback _ _ _ _ _ _ hB.1 (epsR o.K₁)`. Take `⟨ΦΨ, hΦΨ⟩` from `exists_mulEquiv_points_of_isGrpPullback _ _ _ _ _ _ hΨ.1 (epsR o.K₁)`. Take `⟨Φ', hΦ'⟩` from `exists_mulEquiv_points_of_isGrpPullback _ _ _ _ _ _ h'.1 (epsR o.K₁)`. Set `e` to `Equiv.ofBijective _ hsrc`. Establish `he : ∀ q, L.src (e.symm q) = q` using `fun q => e.apply_symm_apply q`.

Establish `hwl : ∀ j i, ΦB (w (e.symm (.inl (j, i)))) = ΦΨ (o.xΨ.v i) ≫ o.φΨ j` using `fun j i => by`. Use `hw (e.symm (.inl (j, i)))` as an intermediate fact. Rewrite `this` using `[LamLetters.IsLetter, he]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[hΦB, Over.comp_left, hΦΨ, Category.assoc]`.

Conclude with `this`. Establish `hwr : ∀ j i, ΦB (w (e.symm (.inr (j, i)))) = Φ' (o.x'.v i) ≫ o.φ' j` using `fun j i => by`. Use `hw (e.symm (.inr (j, i)))` as an intermediate fact. Rewrite `this` using `[LamLetters.IsLetter, he]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Rewrite using `[hΦB, Over.comp_left, hΦ', Category.assoc]`. Conclude with `this`. Establish `hone : tanExp w c = 1`. Choose the witnesses or unpack the hypotheses as in `rfl : w = fun k => tanExp o.xB.v (L.U k) :=`. Use function extensionality and compare the values at `fun k => (isLieComb_iff_tanExp _ _).1 (hwc k)`.

Use `(tanExp_tanExp o.xB.basis.1 (fun k => L.U k) c).trans ?_` and prove the remaining obligations. Rewrite using `[← Matrix.vecMul_eq_sum, hc]`. Conclude with `lieExp_eq_one o.xB.basis.1 _ (fun _ => rfl) _`. Take `⟨-, hpad, hpow, hps⟩ : _ ∧ (∀ a b : Over.mk ((epsR o.K₁).hom ≫ gmap o.K₁) ⟶ o.B.A, padd _ a b = a * b) ∧ _` from `points_sums_eq_products.1 _ _ _`. Set `a` to `fun j => ΦΨ (tanExp o.xΨ.v fun i => c (e.symm (.inl (j, i))))`.

Set `a'` to `fun j => Φ' (tanExp o.x'.v fun i => c (e.symm (.inr (j, i))))`. Establish `hs : padd o.B.A (psumPt fun k => a k ≫ o.φΨ k) (psumPt fun k => a' k ≫ o.φ' k) = 1`. Rewrite using `[hpad, hps, hps, List.prod_ofFn, List.prod_ofFn, ← map_one ΦB, ← hone, push_tanExp ΦB hΦB, ← e.symm.prod_comp, Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_prod_type]`. Apply the tactic sequence `congr 1 <;> refine Finset.prod_congr rfl fun j _ => ?_`. Use `hmΨ j` as an intermediate fact.

Simplify using `only [a, push_tanExp ΦΨ hΦΨ, prod_comp, hwl, Category.assoc]`. Use `hm' j` as an intermediate fact. Simplify using `only [a', push_tanExp Φ' hΦ', prod_comp, hwr, Category.assoc]`. Establish `hs₀ : padd o.B.A (psumPt fun k => (1 : Over.mk ((epsR o.K₁).hom ≫ gmap o.K₁) ⟶ _) ≫ o.φΨ k) (psumPt fun k => (1 : Over.mk ((epsR o.K₁).hom ≫ gmap o.K₁) ⟶ _) ≫ o.φ' k) = 1`. Rewrite using `[hpad, hps, hps, List.prod_ofFn, List.prod_ofFn, Finset.prod_eq_one, Finset.prod_eq_one, _root_.mul_one]`.

Introduce `j _`. Use `hm' j` as an intermediate fact. Conclude with `MonObj.one_comp _`. Introduce `j _`. Use `hmΨ j` as an intermediate fact.

Conclude with `MonObj.one_comp _`. Take `⟨p₁, p₂⟩` from `hsum _ a a'`. Take `⟨q₁, q₂⟩` from `hsum _ (fun _ => 1) (fun _ => 1)`. Rewrite `p₁`, `p₂` using `[hs]`. Rewrite `q₁`, `q₂` using `[hs₀]`.

Apply `hc0` to reduce the goal to its premises. Use function extensionality and compare the values at `k`. Take `⟨q, rfl⟩` from `e.symm.surjective k`. Break down `q with ⟨j, i⟩ | ⟨j, i⟩` into its components or cases. Establish `h` using `(p₁ j).symm.trans (q₁ j)`.

Rewrite `h` using `[(points_sums_eq_products.1 _ _ _).2.2.1, (points_sums_eq_products.1 _ _ _).2.2.1, one_pow, ← map_pow, map_eq_one_iff _ ΦΨ.injective]`. Conclude with `congrFun (eq_zero_of_pow o.xΨ.basis hN h) i`. Establish `h` using `(p₂ j).symm.trans (q₂ j)`. Rewrite `h` using `[(points_sums_eq_products.1 _ _ _).2.2.1, (points_sums_eq_products.1 _ _ _).2.2.1, one_pow, ← map_pow, map_eq_one_iff _ Φ'.injective]`. Conclude with `congrFun (eq_zero_of_pow o.x'.basis hN h) i`.
-/
theorem lamInd : LamIndSt := by
  intro E _ _ _ _ H l cf _ nΨ n' f o La hg L hL hdet
  obtain ⟨-, -, -, hB, hΨ, h', -, -, -, -, -, -, -, ⟨hmΨ, hm', N, ψΨ, ψ', hN, -, hsum⟩, -⟩ := hg
  obtain ⟨hsrc, -, hw, -⟩ := hL
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  choose w hw hwc using hw
  obtain ⟨ΦB, hΦB⟩ := exists_mulEquiv_points_of_isGrpPullback _ _ _ _ _ _ hB.1 (epsR o.K₁)
  obtain ⟨ΦΨ, hΦΨ⟩ := exists_mulEquiv_points_of_isGrpPullback _ _ _ _ _ _ hΨ.1 (epsR o.K₁)
  obtain ⟨Φ', hΦ'⟩ := exists_mulEquiv_points_of_isGrpPullback _ _ _ _ _ _ h'.1 (epsR o.K₁)
  let e := Equiv.ofBijective _ hsrc
  have he : ∀ q, L.src (e.symm q) = q := fun q => e.apply_symm_apply q
  have hwl : ∀ j i, ΦB (w (e.symm (.inl (j, i)))) = ΦΨ (o.xΨ.v i) ≫ o.φΨ j := fun j i => by
    have := hw (e.symm (.inl (j, i)))
    rw [LamLetters.IsLetter, he] at this
    apply Over.OverMorphism.ext
    rw [hΦB, Over.comp_left, hΦΨ, Category.assoc]
    exact this
  have hwr : ∀ j i, ΦB (w (e.symm (.inr (j, i)))) = Φ' (o.x'.v i) ≫ o.φ' j := fun j i => by
    have := hw (e.symm (.inr (j, i)))
    rw [LamLetters.IsLetter, he] at this
    apply Over.OverMorphism.ext
    rw [hΦB, Over.comp_left, hΦ', Category.assoc]
    exact this
  have hone : tanExp w c = 1 := by
    obtain rfl : w = fun k => tanExp o.xB.v (L.U k) :=
      funext fun k => (isLieComb_iff_tanExp _ _).1 (hwc k)
    refine (tanExp_tanExp o.xB.basis.1 (fun k => L.U k) c).trans ?_
    rw [← Matrix.vecMul_eq_sum, hc]
    exact lieExp_eq_one o.xB.basis.1 _ (fun _ => rfl) _
  obtain ⟨-, hpad, hpow, hps⟩ :
      _ ∧ (∀ a b : Over.mk ((epsR o.K₁).hom ≫ gmap o.K₁) ⟶ o.B.A, padd _ a b = a * b) ∧ _ :=
    points_sums_eq_products.1 _ _ _
  let a := fun j => ΦΨ (tanExp o.xΨ.v fun i => c (e.symm (.inl (j, i))))
  let a' := fun j => Φ' (tanExp o.x'.v fun i => c (e.symm (.inr (j, i))))
  have hs : padd o.B.A (psumPt fun k => a k ≫ o.φΨ k) (psumPt fun k => a' k ≫ o.φ' k) = 1 := by
    rw [hpad, hps, hps, List.prod_ofFn, List.prod_ofFn, ← map_one ΦB, ← hone,
      push_tanExp ΦB hΦB, ← e.symm.prod_comp, Fintype.prod_sum_type, Fintype.prod_prod_type,
      Fintype.prod_prod_type]
    congr 1 <;> refine Finset.prod_congr rfl fun j _ => ?_
    · have := hmΨ j
      simp only [a, push_tanExp ΦΨ hΦΨ, prod_comp, hwl, Category.assoc]
    · have := hm' j
      simp only [a', push_tanExp Φ' hΦ', prod_comp, hwr, Category.assoc]
  have hs₀ : padd o.B.A
      (psumPt fun k => (1 : Over.mk ((epsR o.K₁).hom ≫ gmap o.K₁) ⟶ _) ≫ o.φΨ k)
      (psumPt fun k => (1 : Over.mk ((epsR o.K₁).hom ≫ gmap o.K₁) ⟶ _) ≫ o.φ' k) = 1 := by
    rw [hpad, hps, hps, List.prod_ofFn, List.prod_ofFn, Finset.prod_eq_one, Finset.prod_eq_one,
      _root_.mul_one]
    · intro j _
      have := hm' j
      exact MonObj.one_comp _
    · intro j _
      have := hmΨ j
      exact MonObj.one_comp _
  obtain ⟨p₁, p₂⟩ := hsum _ a a'
  obtain ⟨q₁, q₂⟩ := hsum _ (fun _ => 1) (fun _ => 1)
  rw [hs] at p₁ p₂
  rw [hs₀] at q₁ q₂
  apply hc0
  funext k
  obtain ⟨q, rfl⟩ := e.symm.surjective k
  rcases q with ⟨j, i⟩ | ⟨j, i⟩
  · have h := (p₁ j).symm.trans (q₁ j)
    rw [(points_sums_eq_products.1 _ _ _).2.2.1, (points_sums_eq_products.1 _ _ _).2.2.1, one_pow,
      ← map_pow, map_eq_one_iff _ ΦΨ.injective] at h
    exact congrFun (eq_zero_of_pow o.xΨ.basis hN h) i
  · have h := (p₂ j).symm.trans (q₂ j)
    rw [(points_sums_eq_products.1 _ _ _).2.2.1, (points_sums_eq_products.1 _ _ _).2.2.1, one_pow,
      ← map_pow, map_eq_one_iff _ Φ'.injective] at h
    exact congrFun (eq_zero_of_pow o.x'.basis hN h) i

end GlobalTheory.LamF.Ind
