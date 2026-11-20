import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GrpObjOfDenseFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSectionOfDense
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjProperRelAmpleOfProjectiveCoordinateRep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

namespace GlobalTheory.ZM.NearBuild.Fibre

/- English proof (translation)
Use `⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), ?_⟩` and prove the remaining obligations. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Rewrite using `[← h]`. Both sides reduce to the same expression.
-/
theorem mem_range_spMap {R K : Type} [CommRing R] [Field K] (x : R →+* K) (p : Sp R)
    (h : RingHom.ker x = PrimeSpectrum.asIdeal (R := R) p) : p ∈ Set.range (spMap x) := by
  refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), ?_⟩
  apply PrimeSpectrum.ext
  rw [← h]
  rfl

/- English proof (translation)
Use `haveI : NeZero k := ⟨hk⟩`. Establish `red : ∀ e : Fin r → ℕ, ∏ i, y i ^ ((e i : ZMod (k * l))).val = ∏ i, y i ^ e i` using `fun e => Finset.prod_congr rfl fun i _ => by rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (hy i)]`. Establish `tor : ∀ e : Fin r → ℕ, (∏ i, y i ^ e i) ^ (k * l) = 1` using `fun e => by`. Rewrite using `[← Finset.prod_pow]`. Conclude with `Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]`.

Establish `inj : ∀ e e' : Fin r → ℕ, ∏ i, y i ^ e i = ∏ i, y i ^ e' i → ∀ i, e i ≡ e' i [MOD k * l]`. Introduce `e e' he i`. Use `(h _ (tor e)).unique (y₁ := fun i => (e i : ZMod (k * l))) (y₂ := fun i => (e' i : ZMod (k * l))) (red e) ((red e').trans he.symm)` as an intermediate fact. Conclude with `(ZMod.natCast_eq_natCast_iff _ _ _).1 (congrFun this i)`. Take `⟨c, hc, -⟩` from `h z (by rw [pow_mul, hz, one_pow])`.

Establish `hd : ∀ i, l ∣ (c i).val` using `fun i => by`. Use `inj (fun i => k * (c i).val) (fun _ => 0) (by` as an intermediate fact. Simplify using `only [pow_zero, Finset.prod_const_one]`. Rewrite using `[← hz, ← hc, ← Finset.prod_pow]`. Conclude with `Finset.prod_congr rfl fun i _ => by rw [← pow_mul, mul_comm]) i`.

Conclude with `Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hk) ((Nat.modEq_zero_iff_dvd).1 this)`. Use `choose d hd using hd`. Use `⟨fun i => (d i : ZMod k), ?_, fun c' hc' => funext fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[← hc]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[ZMod.val_natCast, ← pow_eq_pow_mod _ (by rw [← pow_mul, mul_comm, hy]), hd, pow_mul]`. Use `inj (fun i => l * (c' i).val) (fun i => l * d i) (by` as an intermediate fact. Simplify using `only [pow_mul, ← hd]`. Rewrite using `[hc, ← hc']) i`. Rewrite `this` using `[mul_comm k l]`.

Establish `h2` using `Nat.ModEq.mul_left_cancel' hl this`. Rewrite using `[← (ZMod.natCast_eq_natCast_iff _ _ _).2 h2, ZMod.natCast_zmod_val]`.
-/
theorem basis_pow {G : Type} [CommGroup G] {r k l : ℕ} (hk : k ≠ 0) (hl : l ≠ 0) (y : Fin r → G)
    (hy : ∀ i, y i ^ (k * l) = 1)
    (h : ∀ z : G, z ^ (k * l) = 1 → ∃! c : Fin r → ZMod (k * l), ∏ i, y i ^ (c i).val = z)
    (z : G) (hz : z ^ k = 1) : ∃! c : Fin r → ZMod k, ∏ i, (y i ^ l) ^ (c i).val = z := by
  haveI : NeZero k := ⟨hk⟩
  have red : ∀ e : Fin r → ℕ, ∏ i, y i ^ ((e i : ZMod (k * l))).val = ∏ i, y i ^ e i := fun e =>
    Finset.prod_congr rfl fun i _ => by rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (hy i)]
  have tor : ∀ e : Fin r → ℕ, (∏ i, y i ^ e i) ^ (k * l) = 1 := fun e => by
    rw [← Finset.prod_pow]
    exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]
  have inj : ∀ e e' : Fin r → ℕ, ∏ i, y i ^ e i = ∏ i, y i ^ e' i → ∀ i, e i ≡ e' i [MOD k * l] := by
    intro e e' he i
    have := (h _ (tor e)).unique (y₁ := fun i => (e i : ZMod (k * l))) (y₂ := fun i => (e' i : ZMod (k * l)))
      (red e) ((red e').trans he.symm)
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 (congrFun this i)
  obtain ⟨c, hc, -⟩ := h z (by rw [pow_mul, hz, one_pow])
  have hd : ∀ i, l ∣ (c i).val := fun i => by
    have := inj (fun i => k * (c i).val) (fun _ => 0) (by
      simp only [pow_zero, Finset.prod_const_one]
      rw [← hz, ← hc, ← Finset.prod_pow]
      exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul, mul_comm]) i
    exact Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hk) ((Nat.modEq_zero_iff_dvd).1 this)
  choose d hd using hd
  refine ⟨fun i => (d i : ZMod k), ?_, fun c' hc' => funext fun i => ?_⟩
  · rw [← hc]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (by rw [← pow_mul, mul_comm, hy]), hd, pow_mul]
  · have := inj (fun i => l * (c' i).val) (fun i => l * d i) (by
      simp only [pow_mul, ← hd]
      rw [hc, ← hc']) i
    rw [mul_comm k l] at this
    have h2 := Nat.ModEq.mul_left_cancel' hl this
    rw [← (ZMod.natCast_eq_natCast_iff _ _ _).2 h2, ZMod.natCast_zmod_val]

variable {S S' : Scheme.{0}}

/- English proof (translation)
Substitute `hN` using the available equality. Simplify using `only [Out.linComb, List.prod_ofFn, MonObj.comp_pow] at h ⊢`. Conclude with `basis_pow (left_ne_zero_of_mul hN0) (right_ne_zero_of_mul hN0) _ (fun i => by rw [← MonObj.comp_pow, hy, MonObj.comp_one]) h z hz`.
-/
theorem basis_pow_linComb {A T : Over S} [GrpObj A] [IsCommMonObj A] {r k l N : ℕ} (hN : N = k * l) (hN0 : N ≠ 0)
    (u : T ⟶ Out.baseOver S) (y : Fin r → (Out.baseOver S ⟶ A)) (hy : ∀ i, y i ^ N = 1)
    (h : ∀ z : T ⟶ A, z ^ N = 1 → ∃! c : Fin r → ZMod N, Out.linComb (fun i => u ≫ y i) (fun i => (c i).val) = z)
    (z : T ⟶ A) (hz : z ^ k = 1) :
    ∃! c : Fin r → ZMod k, Out.linComb (fun i => u ≫ y i ^ l) (fun i => (c i).val) = z := by
  subst hN
  simp only [Out.linComb, List.prod_ofFn, MonObj.comp_pow] at h ⊢
  exact basis_pow (left_ne_zero_of_mul hN0) (right_ne_zero_of_mul hN0) _
    (fun i => by rw [← MonObj.comp_pow, hy, MonObj.comp_one]) h z hz

variable {A : Over S'} {Z : Over S} {x : S' ⟶ S} {φ : A.left ⟶ Z.left}

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Establish `h1 : t.left = T.hom ≫ x` using `by simpa using Over.w t`. Establish `h2 : u.left = T.hom` using `by simpa using Over.w u`. Express the relevant statement in the definitionally equal form `t.left ≫ s.left = (u.left ≫ a.left) ≫ φ`. Rewrite using `[h1, h2, Category.assoc, Category.assoc, h]`.
-/
theorem comp_eq_pushPt (w : φ ≫ Z.hom = A.hom ≫ x) {a : Out.baseOver S' ⟶ A} {s : Out.baseOver S ⟶ Z}
    (h : a.left ≫ φ = x ≫ s.left) {T : Over S'} (u : T ⟶ Out.baseOver S')
    (t : Over.mk (T.hom ≫ x) ⟶ Out.baseOver S) : t ≫ s = pushPt w (u ≫ a) := by
  apply Over.OverMorphism.ext
  have h1 : t.left = T.hom ≫ x := by simpa using Over.w t
  have h2 : u.left = T.hom := by simpa using Over.w u
  change t.left ≫ s.left = (u.left ≫ a.left) ≫ φ
  rw [h1, h2, Category.assoc, Category.assoc, h]

/- English proof (translation)
Establish `inj : Function.Injective (pushHom hφ T)` using `fun y y' e => Over.OverMorphism.ext (hφ.1.hom_ext (congrArg (fun z => z.left) e) ((Over.w y).trans (Over.w y').symm))`. Take `⟨z, rfl⟩` from `GrpDense.pushPt_surjective hφ.1 T z`. Express the relevant statement in the definitionally equal form `pushHom hφ T z ^ k = 1 at hz`. Rewrite `hz` using `[← map_pow, map_eq_one_iff _ inj]`. Establish `key : ∀ e : Fin r → ℕ, Out.linComb (fun i => t ≫ s i) e = pushHom hφ T (Out.linComb (fun i => u ≫ a i) e)` using `fun e => by`.

Simplify using `only [Out.linComb, map_list_prod, List.map_ofFn]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp, map_pow]`. Rewrite using `[comp_eq_pushPt hφ.1.w (h i) u t]`.

Both sides reduce to the same expression. Simplify using `only [key]`. Express the relevant statement in the definitionally equal form `∃! c : Fin r → ZMod k, _ = pushHom hφ T z`. Simplify using `only [inj.eq_iff]`. Conclude with `hb z hz`.
-/
theorem basis_push [GrpObj A] [GrpObj Z] (hφ : IsGrpPullback A Z x φ) {r k : ℕ}
    {a : Fin r → (Out.baseOver S' ⟶ A)} {s : Fin r → (Out.baseOver S ⟶ Z)}
    (h : ∀ i, (a i).left ≫ φ = x ≫ (s i).left) {T : Over S'} (u : T ⟶ Out.baseOver S')
    (t : Over.mk (T.hom ≫ x) ⟶ Out.baseOver S)
    (hb : ∀ z : T ⟶ A, z ^ k = 1 → ∃! c : Fin r → ZMod k, Out.linComb (fun i => u ≫ a i) (fun i => (c i).val) = z)
    (z : Over.mk (T.hom ≫ x) ⟶ Z) (hz : z ^ k = 1) :
    ∃! c : Fin r → ZMod k, Out.linComb (fun i => t ≫ s i) (fun i => (c i).val) = z := by
  have inj : Function.Injective (pushHom hφ T) := fun y y' e =>
    Over.OverMorphism.ext (hφ.1.hom_ext (congrArg (fun z => z.left) e) ((Over.w y).trans (Over.w y').symm))
  obtain ⟨z, rfl⟩ := GrpDense.pushPt_surjective hφ.1 T z
  change pushHom hφ T z ^ k = 1 at hz
  rw [← map_pow, map_eq_one_iff _ inj] at hz
  have key : ∀ e : Fin r → ℕ, Out.linComb (fun i => t ≫ s i) e =
      pushHom hφ T (Out.linComb (fun i => u ≫ a i) e) := fun e => by
    simp only [Out.linComb, map_list_prod, List.map_ofFn]
    congr 2
    funext i
    simp only [Function.comp, map_pow]
    rw [comp_eq_pushPt hφ.1.w (h i) u t]
    rfl
  simp only [key]
  change ∃! c : Fin r → ZMod k, _ = pushHom hφ T z
  simp only [inj.eq_iff]
  exact hb z hz

/- English proof (translation)
Use `t.ab.comm` as an intermediate fact. Rewrite using `[TObj.lab, Out.linComb, List.prod_ofFn, Finset.prod_eq_single i]`. Rewrite using `[Pi.single_eq_same, ← Nat.cast_one, ZMod.val_natCast, ← pow_eq_pow_mod _ (t.torsion i), pow_one]`. Introduce `j _ hj`. Rewrite using `[Pi.single_eq_of_ne hj, ZMod.val_zero, pow_zero]`.

Simplify using the standard rewrite rules.
-/
theorem lab_single {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
    (t : TObj g k J b s) (i : Fin (2 * g)) : t.lab (Pi.single i 1) = t.pt i := by
  have := t.ab.comm
  rw [TObj.lab, Out.linComb, List.prod_ofFn, Finset.prod_eq_single i]
  · rw [Pi.single_eq_same, ← Nat.cast_one, ZMod.val_natCast, ← pow_eq_pow_mod _ (t.torsion i), pow_one]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, ZMod.val_zero, pow_zero]
  · simp

/- English proof (translation)
Use `t.ab.comm` as an intermediate fact. Rewrite using `[TObj.lab, Out.linComb, List.prod_ofFn]`. Simplify using the standard rewrite rules.
-/
theorem lab_zero {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
    (t : TObj g k J b s) : t.lab 0 = 1 := by
  have := t.ab.comm
  rw [TObj.lab, Out.linComb, List.prod_ofFn]
  simp

/- English proof (translation)
The claim follows from `Category.id_comp _`.
-/
theorem one_left {A : Over S} [GrpObj A] : (1 : Out.baseOver S ⟶ A).left = (η[A]).left :=
  Category.id_comp _

end GlobalTheory.ZM.NearBuild.Fibre

namespace GlobalTheory.ZM.NearBuild

open Fibre

/- English proof (translation)
Introduce `hL _ o _ g N' J b Mat κ R _ _ _ β v m Z M th sc mu F hN0 hden ⟨⟨I, p, hrep, _⟩, _, hfib⟩ hsm hgc hm hF`. Use `haveI : NeZero (N' ^ 2) := ⟨pow_ne_zero _ hN0⟩`. Establish `hun : IsUnit (N' : R)`. Use `b.unit.map β` as an intermediate fact. Rewrite `this` using `[map_natCast, Nat.cast_pow, isUnit_pow_iff two_ne_zero]`.

Conclude with `this`. Take `⟨-, hpr, hamp⟩` from `GlobalTheory.ZM.projRep_projective_ample R _ I Z M th hrep`. Establish `hD` using `dense_of_denseP hden`. Establish `hs : Smooth Z.hom` using `SmoothOfRelativeDimension.smooth g _`. Establish `s1 : Smooth (Out.baseOver (Sp R)).hom` using `inferInstanceAs (Smooth (𝟙 _))`.

Establish `h0 : ∀ {K : Type} [Field K] {x : R →+* K} {s : Sp K ⟶ Sp o} (t' : TObj g (N' ^ 2) J b s) {φ : t'.A.left ⟶ Z.left}, (∀ h, (t'.lab h ^ N').left ≫ φ = spMap x ≫ (sc h).left) → (1 : Out.baseOver _ ⟶ t'.A).left ≫ φ = spMap x ≫ (sc 0).left` using `fun t' φ h => by`. Use `h 0` as an intermediate fact. Rewrite `this` using `[lab_zero, one_pow]`. Then use the resulting hypothesis. Establish `h1 : ∀ {K : Type} [Field K] {x : R →+* K} {s : Sp K ⟶ Sp o} (t' : TObj g (N' ^ 2) J b s) {φ : t'.A.left ⟶ Z.left}, (∀ h, (t'.lab h ^ N').left ≫ φ = spMap x ≫ (sc h).left) → ∀ i, (t'.pt i ^ N').left ≫ φ = spMap x ≫ (sc (Pi.single i 1)).left` using `fun t' φ h i => by`. Use `h (Pi.single i 1)` as an intermediate fact.

Rewrite `this` using `[lab_single]`. Then use the resulting hypothesis. Take `⟨_, -, hη, -, hab, hgp⟩` from `grpObj_of_dense_fibres R Z mu (F none) (sc 0) _ hD hs hpr hgc (by`. Introduce `q hq`. Take `⟨K, _, _, x, s, t', hx, ht⟩` from `mem_objPrimes.1 hq`. Take `⟨φ, hφ⟩` from `hfib K x s t' ht`.

Use `⟨K, inferInstance, spMap x, t'.A, inferInstance, φ, mem_range_spMap x q hx, t'.ab.comm, hφ.1, hm K x s t' φ ht hφ, ?_, ?_⟩` and prove the remaining obligations. Use `hF none K x s t' φ ht hφ` as an intermediate fact. Rewrite `this` using `[Option.elim, Hom.inv_def, Category.id_comp]`. Then use the resulting hypothesis. Rewrite using `[← one_left, h0 t' hφ.2.2.2])`. Use `hab.comm` as an intermediate fact.

Establish `hhom : ∀ i, IsMonHom (F (some i))` using `fun i => hL.rigidity _ Z Z hab hab _ (by`. Rewrite using `[hη]`. Use `FibreGrp.hom_ext_of_fibres (X := Out.baseOver (Sp R)) hD ?_` and prove the remaining obligations. Introduce `q hq`. Take `⟨K, _, _, x, s, t', hx, ht⟩` from `mem_objPrimes.1 hq`.

Take `⟨φ, hφ⟩` from `hfib K x s t' ht`. Use `⟨_, spMap x, mem_range_spMap x q hx, fun T t => ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, comp_eq_pushPt hφ.1.w (h0 t' hφ.2.2.2) (toUnit T) t]`. Use `t'.hom i` as an intermediate fact. Establish `e : (toUnit T ≫ (1 : Out.baseOver _ ⟶ t'.A)) ≫ t'.act i = toUnit T ≫ (1 : Out.baseOver _ ⟶ t'.A)`.

Rewrite using `[Category.assoc, MonObj.one_comp]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(_ ≫ φ) ≫ (F (some i)).left = _ ≫ φ`. Rewrite using `[Category.assoc, hF (some i) K x s t' φ ht hφ, ← Category.assoc, ← Over.comp_left]`. Conclude with `congrArg (fun z => z.left ≫ φ) e)`.

Establish `htor : ∀ {K : Type} [Field K] {s : Sp K ⟶ Sp o} (t' : TObj g (N' ^ 2) J b s) (i), (t'.pt i ^ N') ^ N' = 1` using `fun t' i => by`. Establish `e : N' * N' = N' ^ 2` using `(pow_two _).symm`. Rewrite using `[← pow_mul (t'.pt i), e, t'.torsion]`. Establish `hQ : ∀ i, sc (Pi.single i 1) ^ N' = 1` using `fun i => by`. Use `FibreGrp.hom_ext_of_fibres (X := Out.baseOver (Sp R)) hD ?_` and prove the remaining obligations.

Introduce `q hq`. Take `⟨K, _, _, x, s, t', hx, ht⟩` from `mem_objPrimes.1 hq`. Take `⟨φ, hφ⟩` from `hfib K x s t' ht`. Use `⟨_, spMap x, mem_range_spMap x q hx, fun T t => ?_⟩` and prove the remaining obligations. Rewrite using `[MonObj.comp_pow, MonObj.comp_one, comp_eq_pushPt hφ.1.w (h1 t' hφ.2.2.2 i) (toUnit T) t]`.

Express the relevant statement in the definitionally equal form `pushHom (hgp _ _ _ φ hφ.1 (hm K x s t' φ ht hφ)) T _ ^ _ = 1`. Rewrite using `[← map_pow]`. Use `erw [← MonObj.comp_pow]`. Rewrite using `[htor]`. Use `erw [MonObj.comp_one]`.

Rewrite using `[map_one]`. Establish `hB` using `torsion_basis_of_dense (Sp R) Z N' (2 * g) (fun i => sc (Pi.single i 1)) _ hab (Nat.pos_of_ne_zero hN0) (by`. Use `hun.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom` as an intermediate fact. Simplify using `using this) hQ hD (by`. Introduce `q hq`.

Take `⟨K, _, _, x, s, t', hx, ht⟩` from `mem_objPrimes.1 hq`. Take `⟨φ, hφ⟩` from `hfib K x s t' ht`. Use `t'.ab.comm` as an intermediate fact. Use `⟨K, inferInstance, inferInstance, 𝟙 _ ≫ spMap x, by simpa using mem_range_spMap x q hx, ?_⟩` and prove the remaining obligations. Conclude with `basis_push (hgp _ _ _ φ hφ.1 (hm K x s t' φ ht hφ)) (h1 t' hφ.2.2.2) (T := Over.mk (𝟙 _)) _ _ (basis_pow_linComb (pow_two _) (NeZero.ne _) _ t'.pt t'.torsion (t'.bij K (𝟙 _))))`.

Use `⟨inferInstance, hab, hsm, hrep.1, hamp, ⟨hhom, hQ, hB⟩, fun K _ _ x s t' ht => ?_⟩` and prove the remaining obligations. Take `⟨φ, hφ⟩` from `hfib K x s t' ht`. Conclude with `⟨φ, ⟨hgp _ _ _ φ hφ.1 (hm K x s t' φ ht hφ), fun i => (hF (some i) K x s t' φ ht hφ).symm, h1 t' hφ.2.2.2⟩, hφ.2.2.1⟩`.
-/
theorem grpFam_of_dense_fibres :
    Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (m : ℕ) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g (N' ^ 2) → M.Sec) (sc : Ix g (N' ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (mu : Z ⊗ Z ⟶ Z) (F : Option J → (Z ⟶ Z)), N' ≠ 0 → DenseP (objPrimes b Mat κ β v) → Fam b Mat κ β v m M th sc → SmoothOfRelativeDimension g Z.hom → GeometricallyConnected Z.hom → AddAt b Mat κ β v m M th sc mu → (∀ i, EndAt b Mat κ β v m M th sc i (F i)) → ∃ _ : GrpObj Z, GrpFam b Mat κ β v m Z M (fun i => F (some i)) (fun i => sc (Pi.single i 1)) := by
  intro hL _ o _ g N' J b Mat κ R _ _ _ β v m Z M th sc mu F hN0 hden ⟨⟨I, p, hrep, _⟩, _, hfib⟩ hsm hgc hm hF
  haveI : NeZero (N' ^ 2) := ⟨pow_ne_zero _ hN0⟩
  have hun : IsUnit (N' : R) := by
    have := b.unit.map β
    rw [map_natCast, Nat.cast_pow, isUnit_pow_iff two_ne_zero] at this
    exact this
  obtain ⟨-, hpr, hamp⟩ := GlobalTheory.ZM.projRep_projective_ample R _ I Z M th hrep
  have hD := dense_of_denseP hden
  have hs : Smooth Z.hom := SmoothOfRelativeDimension.smooth g _
  have s1 : Smooth (Out.baseOver (Sp R)).hom := inferInstanceAs (Smooth (𝟙 _))
  have h0 : ∀ {K : Type} [Field K] {x : R →+* K} {s : Sp K ⟶ Sp o} (t' : TObj g (N' ^ 2) J b s)
      {φ : t'.A.left ⟶ Z.left}, (∀ h, (t'.lab h ^ N').left ≫ φ = spMap x ≫ (sc h).left) →
      (1 : Out.baseOver _ ⟶ t'.A).left ≫ φ = spMap x ≫ (sc 0).left := fun t' φ h => by
    have := h 0
    rwa [lab_zero, one_pow] at this
  have h1 : ∀ {K : Type} [Field K] {x : R →+* K} {s : Sp K ⟶ Sp o} (t' : TObj g (N' ^ 2) J b s)
      {φ : t'.A.left ⟶ Z.left}, (∀ h, (t'.lab h ^ N').left ≫ φ = spMap x ≫ (sc h).left) →
      ∀ i, (t'.pt i ^ N').left ≫ φ = spMap x ≫ (sc (Pi.single i 1)).left := fun t' φ h i => by
    have := h (Pi.single i 1)
    rwa [lab_single] at this
  obtain ⟨_, -, hη, -, hab, hgp⟩ := grpObj_of_dense_fibres R Z mu (F none) (sc 0) _ hD hs hpr hgc (by
    intro q hq
    obtain ⟨K, _, _, x, s, t', hx, ht⟩ := mem_objPrimes.1 hq
    obtain ⟨φ, hφ⟩ := hfib K x s t' ht
    refine ⟨K, inferInstance, spMap x, t'.A, inferInstance, φ, mem_range_spMap x q hx, t'.ab.comm, hφ.1,
      hm K x s t' φ ht hφ, ?_, ?_⟩
    · have := hF none K x s t' φ ht hφ
      rwa [Option.elim, Hom.inv_def, Category.id_comp] at this
    · rw [← one_left, h0 t' hφ.2.2.2])
  have := hab.comm
  have hhom : ∀ i, IsMonHom (F (some i)) := fun i => hL.rigidity _ Z Z hab hab _ (by
    rw [hη]
    refine FibreGrp.hom_ext_of_fibres (X := Out.baseOver (Sp R)) hD ?_
    intro q hq
    obtain ⟨K, _, _, x, s, t', hx, ht⟩ := mem_objPrimes.1 hq
    obtain ⟨φ, hφ⟩ := hfib K x s t' ht
    refine ⟨_, spMap x, mem_range_spMap x q hx, fun T t => ?_⟩
    rw [← Category.assoc, comp_eq_pushPt hφ.1.w (h0 t' hφ.2.2.2) (toUnit T) t]
    have := t'.hom i
    have e : (toUnit T ≫ (1 : Out.baseOver _ ⟶ t'.A)) ≫ t'.act i = toUnit T ≫ (1 : Out.baseOver _ ⟶ t'.A) := by
      rw [Category.assoc, MonObj.one_comp]
    apply Over.OverMorphism.ext
    change (_ ≫ φ) ≫ (F (some i)).left = _ ≫ φ
    rw [Category.assoc, hF (some i) K x s t' φ ht hφ, ← Category.assoc, ← Over.comp_left]
    exact congrArg (fun z => z.left ≫ φ) e)
  have htor : ∀ {K : Type} [Field K] {s : Sp K ⟶ Sp o} (t' : TObj g (N' ^ 2) J b s) (i),
      (t'.pt i ^ N') ^ N' = 1 := fun t' i => by
    have e : N' * N' = N' ^ 2 := (pow_two _).symm
    rw [← pow_mul (t'.pt i), e, t'.torsion]
  have hQ : ∀ i, sc (Pi.single i 1) ^ N' = 1 := fun i => by
    refine FibreGrp.hom_ext_of_fibres (X := Out.baseOver (Sp R)) hD ?_
    intro q hq
    obtain ⟨K, _, _, x, s, t', hx, ht⟩ := mem_objPrimes.1 hq
    obtain ⟨φ, hφ⟩ := hfib K x s t' ht
    refine ⟨_, spMap x, mem_range_spMap x q hx, fun T t => ?_⟩
    rw [MonObj.comp_pow, MonObj.comp_one, comp_eq_pushPt hφ.1.w (h1 t' hφ.2.2.2 i) (toUnit T) t]
    change pushHom (hgp _ _ _ φ hφ.1 (hm K x s t' φ ht hφ)) T _ ^ _ = 1
    rw [← map_pow]
    erw [← MonObj.comp_pow]
    rw [htor]
    erw [MonObj.comp_one]
    rw [map_one]
  have hB := torsion_basis_of_dense (Sp R) Z N' (2 * g) (fun i => sc (Pi.single i 1)) _ hab
    (Nat.pos_of_ne_zero hN0) (by
      have := hun.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      simpa using this) hQ hD (by
      intro q hq
      obtain ⟨K, _, _, x, s, t', hx, ht⟩ := mem_objPrimes.1 hq
      obtain ⟨φ, hφ⟩ := hfib K x s t' ht
      have := t'.ab.comm
      refine ⟨K, inferInstance, inferInstance, 𝟙 _ ≫ spMap x, by simpa using mem_range_spMap x q hx, ?_⟩
      exact basis_push (hgp _ _ _ φ hφ.1 (hm K x s t' φ ht hφ)) (h1 t' hφ.2.2.2) (T := Over.mk (𝟙 _)) _ _
        (basis_pow_linComb (pow_two _) (NeZero.ne _) _ t'.pt t'.torsion (t'.bij K (𝟙 _))))
  refine ⟨inferInstance, hab, hsm, hrep.1, hamp, ⟨hhom, hQ, hB⟩, fun K _ _ x s t' ht => ?_⟩
  obtain ⟨φ, hφ⟩ := hfib K x s t' ht
  exact ⟨φ, ⟨hgp _ _ _ φ hφ.1 (hm K x s t' φ ht hφ), fun i => (hF (some i) K x s t' φ ht hφ).symm,
    h1 t' hφ.2.2.2⟩, hφ.2.2.1⟩

end GlobalTheory.ZM.NearBuild
