import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsConst

/- English proof (translation)
The claim follows from `(Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm`.
-/
theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

/- English proof (translation)
Take `⟨⟨x, f, hf⟩, rfl⟩` from `(SpecToEquivOfLocalRing X (CommRingCat.of B)).symm.surjective a`. Take `⟨⟨y, g, hg⟩, rfl⟩` from `(SpecToEquivOfLocalRing X (CommRingCat.of B)).symm.surjective b`. Establish `l1 : ∀ (k : B →+* C) [IsLocalHom k] (φ : X.presheaf.stalk x ⟶ CommRingCat.of B), IsLocalHom φ.hom → IsLocalHom (φ ≫ CommRingCat.ofHom k).hom`. Introduce `k _ φ _`. Rewrite using `[CommRingCat.hom_comp]`.

Conclude with `RingHom.isLocalHom_comp k φ.hom`. Establish `l2 : ∀ (k : B →+* C) [IsLocalHom k] (φ : X.presheaf.stalk y ⟶ CommRingCat.of B), IsLocalHom φ.hom → IsLocalHom (φ ≫ CommRingCat.ofHom k).hom`. Introduce `k _ φ _`. Rewrite using `[CommRingCat.hom_comp]`. Conclude with `RingHom.isLocalHom_comp k φ.hom`.

Establish `key : ∀ (k : B →+* C) [IsLocalHom k], spMap k ≫ (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm ⟨x, f, hf⟩ = spMap k ≫ (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm ⟨y, g, hg⟩ → (⟨x, f ≫ CommRingCat.ofHom k, l1 k f hf⟩ : Σ z : X, {φ : X.presheaf.stalk z ⟶ CommRingCat.of C …`. Introduce `k _ h`. Apply `(SpecToEquivOfLocalRing X (CommRingCat.of C)).symm.injective` to reduce the goal to its premises. Simplify `h` using `[SpecToEquivOfLocalRing]`. Establish `k1` using `key d h1`.

Establish `k2` using `key e h2`. Take `rfl : x = y` from `congrArg Sigma.fst k1`. Establish `h5 : f ≫ CommRingCat.ofHom d = g ≫ CommRingCat.ofHom d` using `congrArg Subtype.val (eq_of_heq (Sigma.mk.inj k1).2)`. Establish `h6 : f ≫ CommRingCat.ofHom e = g ≫ CommRingCat.ofHom e` using `congrArg Subtype.val (eq_of_heq (Sigma.mk.inj k2).2)`. Choose the witnesses or unpack the hypotheses as in `rfl : f = g := by`.

Use extensionality with `s`. Conclude with `hde _ _ (congrArg (fun k => k.hom s) h5) (congrArg (fun k => k.hom s) h6)`. Both sides reduce to the same expression.
-/
theorem ext_of_two {B C : Type} [CommRing B] [CommRing C] [IsLocalRing B] [IsLocalRing C]
    (d e : B →+* C) [IsLocalHom d] [IsLocalHom e] (hde : ∀ x y, d x = d y → e x = e y → x = y)
    {X : Scheme.{0}} (a b : Sp B ⟶ X) (h1 : spMap d ≫ a = spMap d ≫ b) (h2 : spMap e ≫ a = spMap e ≫ b) :
    a = b := by
  obtain ⟨⟨x, f, hf⟩, rfl⟩ := (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm.surjective a
  obtain ⟨⟨y, g, hg⟩, rfl⟩ := (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm.surjective b
  have l1 : ∀ (k : B →+* C) [IsLocalHom k] (φ : X.presheaf.stalk x ⟶ CommRingCat.of B),
      IsLocalHom φ.hom → IsLocalHom (φ ≫ CommRingCat.ofHom k).hom := by
    intro k _ φ _
    rw [CommRingCat.hom_comp]; exact RingHom.isLocalHom_comp k φ.hom
  have l2 : ∀ (k : B →+* C) [IsLocalHom k] (φ : X.presheaf.stalk y ⟶ CommRingCat.of B),
      IsLocalHom φ.hom → IsLocalHom (φ ≫ CommRingCat.ofHom k).hom := by
    intro k _ φ _
    rw [CommRingCat.hom_comp]; exact RingHom.isLocalHom_comp k φ.hom
  have key : ∀ (k : B →+* C) [IsLocalHom k], spMap k ≫ (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm ⟨x, f, hf⟩ =
      spMap k ≫ (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm ⟨y, g, hg⟩ →
      (⟨x, f ≫ CommRingCat.ofHom k, l1 k f hf⟩ : Σ z : X, {φ : X.presheaf.stalk z ⟶ CommRingCat.of C // IsLocalHom φ.hom}) =
        ⟨y, g ≫ CommRingCat.ofHom k, l2 k g hg⟩ := by
    intro k _ h
    apply (SpecToEquivOfLocalRing X (CommRingCat.of C)).symm.injective
    simpa [SpecToEquivOfLocalRing] using h
  have k1 := key d h1
  have k2 := key e h2
  obtain rfl : x = y := congrArg Sigma.fst k1
  have h5 : f ≫ CommRingCat.ofHom d = g ≫ CommRingCat.ofHom d :=
    congrArg Subtype.val (eq_of_heq (Sigma.mk.inj k1).2)
  have h6 : f ≫ CommRingCat.ofHom e = g ≫ CommRingCat.ofHom e :=
    congrArg Subtype.val (eq_of_heq (Sigma.mk.inj k2).2)
  obtain rfl : f = g := by
    ext s
    exact hde _ _ (congrArg (fun k => k.hom s) h5) (congrArg (fun k => k.hom s) h6)
  rfl

variable {K : Type} [Field K]

/- English proof (translation)
The claim follows from `IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one] exact IsLocalRing.isUnit_or_isUnit_one_sub_self _`.
-/
theorem isLocalRing_tsze (M : Type) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M] :
    IsLocalRing (TrivSqZeroExt K M) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact IsLocalRing.isUnit_or_isUnit_one_sub_self _

attribute [local instance] isLocalRing_tsze

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a ha => by rw [TrivSqZeroExt.isUnit_iff_isUnit_fst] at ha ⊢ simpa using ha⟩`.
-/
theorem isLocalHom_map {M N : Type} [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M]
    [AddCommGroup N] [Module K N] [Module Kᵐᵒᵖ N] [IsCentralScalar K N] (l : M →ₗ[K] N) :
    IsLocalHom (TrivSqZeroExt.map l).toRingHom :=
  ⟨fun a ha => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst] at ha ⊢
    simpa using ha⟩

abbrev ovO (B : Type) [CommRing B] [Algebra K B] : Over (Sp K) := Over.mk (spMap (algebraMap K B))

def ovH {B C : Type} [CommRing B] [Algebra K B] [CommRing C] [Algebra K C] (φ : B →ₐ[K] C) :
    ovO (K := K) C ⟶ ovO B :=
  Over.homMk (spMap φ.toRingHom) (by
    simp only [ovO, Over.mk_hom]
    rw [sp_comp]
    congr 2
    exact φ.comp_algebraMap)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ovH_left {B C : Type} [CommRing B] [Algebra K B] [CommRing C] [Algebra K C] (φ : B →ₐ[K] C) :
    (ovH φ).left = spMap φ.toRingHom := rfl

/- English proof (translation)
Use `ext1`. Simplify using `only [Over.comp_left, ovH_left, sp_comp]`. Both sides reduce to the same expression.
-/
theorem ovH_comp {B C E : Type} [CommRing B] [Algebra K B] [CommRing C] [Algebra K C] [CommRing E] [Algebra K E]
    (φ : B →ₐ[K] C) (ψ : C →ₐ[K] E) : ovH (ψ.comp φ) = ovH ψ ≫ ovH φ := by
  ext1
  simp only [Over.comp_left, ovH_left, sp_comp]
  rfl

/- English proof (translation)
Use `ext1`. Simplify using `only [ovH_left, Over.id_left]`. Conclude with `Spec.map_id _`.
-/
theorem ovH_id {B : Type} [CommRing B] [Algebra K B] : ovH (AlgHom.id K B) = 𝟙 (ovO B) := by
  ext1
  simp only [ovH_left, Over.id_left]
  exact Spec.map_id _

abbrev sc (t : K) : DualNumber K →ₐ[K] DualNumber K := TrivSqZeroExt.map (t • LinearMap.id)

abbrev jj (s t : K) : DualNumber K →ₐ[K] TrivSqZeroExt K (K × K) :=
  TrivSqZeroExt.map (LinearMap.prod (s • LinearMap.id) (t • LinearMap.id))

abbrev r1 : TrivSqZeroExt K (K × K) →ₐ[K] DualNumber K := TrivSqZeroExt.map (LinearMap.fst K K K)
abbrev r2 : TrivSqZeroExt K (K × K) →ₐ[K] DualNumber K := TrivSqZeroExt.map (LinearMap.snd K K K)
abbrev dd : TrivSqZeroExt K (K × K) →ₐ[K] DualNumber K := TrivSqZeroExt.map (LinearMap.fst K K K + LinearMap.snd K K K)

/- English proof (translation)
Apply the tactic sequence `apply AlgHom.ext; intro x; ext <;> simp`.
-/
theorem dualNumberFirstProj_comp_twoEpsLinearComb (s t : K) : (r1 (K := K)).comp (jj s t) = sc s := by
  apply AlgHom.ext; intro x; ext <;> simp
/- English proof (translation)
Apply the tactic sequence `apply AlgHom.ext; intro x; ext <;> simp`.
-/
theorem dualNumberSecondProj_comp_twoEpsLinearComb (s t : K) : (r2 (K := K)).comp (jj s t) = sc t := by
  apply AlgHom.ext; intro x; ext <;> simp
/- English proof (translation)
Apply the tactic sequence `apply AlgHom.ext; intro x; ext <;> simp [add_mul]`.
-/
theorem dd_jj (s t : K) : (dd (K := K)).comp (jj s t) = sc (s + t) := by
  apply AlgHom.ext; intro x; ext <;> simp [add_mul]
/- English proof (translation)
Apply the tactic sequence `apply AlgHom.ext; intro x; ext <;> simp <;> ring`.
-/
theorem sc_sc (a b : K) : (sc a).comp (sc b) = sc (a * b) := by
  apply AlgHom.ext; intro x; ext <;> simp <;> ring
/- English proof (translation)
Apply the tactic sequence `apply AlgHom.ext; intro x; ext <;> simp`.
-/
theorem sc_one : sc (1 : K) = AlgHom.id K _ := by
  apply AlgHom.ext; intro x; ext <;> simp

section Pts
variable {A : Over (Sp K)} [GrpObj A]

/- English proof (translation)
Use `haveI := isLocalHom_map (K := K) (LinearMap.fst K K K)`. Use `haveI := isLocalHom_map (K := K) (LinearMap.snd K K K)`. Use `ext1`. Use `ext_of_two (r1 (K := K)).toRingHom (r2 (K := K)).toRingHom ?_ a.left b.left (by simpa only [Over.comp_left, ovH_left] using congrArg CommaMorphism.left h1) (by simpa only [Over.comp_left, ovH_left] using congrArg CommaMorphism.left h2)` and prove the remaining obligations. Introduce `x y hx hy`.

Establish `a1` using `congrArg TrivSqZeroExt.fst hx`. Establish `a2` using `congrArg TrivSqZeroExt.snd hx`. Establish `a3` using `congrArg TrivSqZeroExt.snd hy`. Simplify using `at a1 a2 a3`. Use `ext`.

Conclude with `a1`. Conclude with `a2`. Conclude with `a3`.
-/
theorem ext2 (a b : ovO (K := K) (TrivSqZeroExt K (K × K)) ⟶ A) (h1 : ovH r1 ≫ a = ovH r1 ≫ b)
    (h2 : ovH r2 ≫ a = ovH r2 ≫ b) : a = b := by
  haveI := isLocalHom_map (K := K) (LinearMap.fst K K K)
  haveI := isLocalHom_map (K := K) (LinearMap.snd K K K)
  ext1
  refine ext_of_two (r1 (K := K)).toRingHom (r2 (K := K)).toRingHom ?_ a.left b.left
    (by simpa only [Over.comp_left, ovH_left] using congrArg CommaMorphism.left h1)
    (by simpa only [Over.comp_left, ovH_left] using congrArg CommaMorphism.left h2)
  intro x y hx hy
  have a1 := congrArg TrivSqZeroExt.fst hx
  have a2 := congrArg TrivSqZeroExt.snd hx
  have a3 := congrArg TrivSqZeroExt.snd hy
  simp at a1 a2 a3
  ext
  · exact a1
  · exact a2
  · exact a3

/- English proof (translation)
Establish `e : ovH (jj s t) ≫ x * ovH (jj 0 0) ≫ x = ovH (jj s 0) ≫ x * ovH (jj 0 t) ≫ x`. Apply `ext2` to reduce the goal to its premises. Simplify using `only [MonObj.comp_mul, ← Category.assoc, ← ovH_comp, dualNumberFirstProj_comp_twoEpsLinearComb]`. Simplify using `only [MonObj.comp_mul, ← Category.assoc, ← ovH_comp, dualNumberSecondProj_comp_twoEpsLinearComb]`. Conclude with `hc _ _`.

Establish `e2` using `congrArg (fun z => ovH dd ≫ z) e`. Simplify using `only [MonObj.comp_mul, ← Category.assoc, ← ovH_comp, dd_jj, add_zero, zero_add] at e2`. Conclude with `e2`.
-/
theorem hadd (hc : ∀ x y : ovO (K := K) (DualNumber K) ⟶ A, x * y = y * x) (x : ovO (DualNumber K) ⟶ A) (s t : K) :
    ovH (sc (s + t)) ≫ x * ovH (sc 0) ≫ x = ovH (sc s) ≫ x * ovH (sc t) ≫ x := by
  have e : ovH (jj s t) ≫ x * ovH (jj 0 0) ≫ x = ovH (jj s 0) ≫ x * ovH (jj 0 t) ≫ x := by
    apply ext2
    · simp only [MonObj.comp_mul, ← Category.assoc, ← ovH_comp, dualNumberFirstProj_comp_twoEpsLinearComb]
    · simp only [MonObj.comp_mul, ← Category.assoc, ← ovH_comp, dualNumberSecondProj_comp_twoEpsLinearComb]
      exact hc _ _
  have e2 := congrArg (fun z => ovH dd ≫ z) e
  simp only [MonObj.comp_mul, ← Category.assoc, ← ovH_comp, dd_jj, add_zero, zero_add] at e2
  exact e2

end Pts

/- English proof (translation)
Use `letI : CommGroup G := { ‹Group G› with mul_comm := hc }`. Establish `hone : ∀ t, P t 1 = 1` using `fun t => mul_left_cancel (a := P t 1) (by rw [_root_.mul_one, ← hmul, _root_.one_mul])`. Establish `hpow : ∀ t x (m : ℕ), P t (x ^ m) = P t x ^ m`. Introduce `t x m`. Proceed by induction on `m with`.

Consider the case `zero => simp [hone]`. Consider the case `succ m ih => rw [pow_succ, hmul, ih, pow_succ]`. Establish `step : ∀ m : ℕ, P m u * P 0 u ^ m = u ^ m * P 0 u`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => simp`. Consider the case `succ m ih`. Establish `h` using `hadd m 1 u`. Rewrite `h` using `[h1]`. Rewrite using `[Nat.cast_succ, pow_succ', ← _root_.mul_assoc, h, mul_right_comm, ih, pow_succ]`.

Conclude with `mul_right_comm _ _ _`. Establish `e` using `step n`. Rewrite `e` using `[← hpow, hu, hone, _root_.mul_one, _root_.one_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem eq_zeroScale_of_pow_eq_one_of_affine_fieldAction {G : Type} [CharZero K] [Group G] (hc : ∀ x y : G, x * y = y * x) (P : K → G → G)
    (hmul : ∀ t x y, P t (x * y) = P t x * P t y) (hcomp : ∀ a b x, P a (P b x) = P (a * b) x)
    (h1 : ∀ x, P 1 x = x) (hadd : ∀ s t x, P (s + t) x * P 0 x = P s x * P t x)
    (u : G) (n : ℕ) (hn : 0 < n) (hu : u ^ n = 1) : u = P 0 u := by
  letI : CommGroup G := { ‹Group G› with mul_comm := hc }
  have hone : ∀ t, P t 1 = 1 := fun t => mul_left_cancel (a := P t 1) (by rw [_root_.mul_one, ← hmul, _root_.one_mul])
  have hpow : ∀ t x (m : ℕ), P t (x ^ m) = P t x ^ m := by
    intro t x m
    induction m with
    | zero => simp [hone]
    | succ m ih => rw [pow_succ, hmul, ih, pow_succ]
  have step : ∀ m : ℕ, P m u * P 0 u ^ m = u ^ m * P 0 u := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h := hadd m 1 u
      rw [h1] at h
      rw [Nat.cast_succ, pow_succ', ← _root_.mul_assoc, h, mul_right_comm, ih, pow_succ]
      exact mul_right_comm _ _ _
  have e := step n
  rw [← hpow, hu, hone, _root_.mul_one, _root_.one_mul] at e
  calc u = P 1 u := (h1 u).symm
    _ = P ((n : K)⁻¹ * n) u := by rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn.ne')]
    _ = P (n : K)⁻¹ (P n u) := (hcomp _ _ _).symm
    _ = P (n : K)⁻¹ (P 0 u) := by rw [e]
    _ = P 0 u := by rw [hcomp, mul_zero]

end GlobalTheory.TorsConst

/- English proof (translation)
Introduce `K _ _ A _ f hf hc u n hn hu`. Substitute `hf` using the available equality. Use `open GlobalTheory.TorsConst in`. Establish `key : u = ovH (sc 0) ≫ u` using `eq_zeroScale_of_pow_eq_one_of_affine_fieldAction hc (fun t x => ovH (sc t) ≫ x) (fun t x y => MonObj.comp_mul _ _ _) (fun a b x => by simp only [← Category.assoc, ← ovH_comp, sc_sc]) (fun x => by simp only [sc_one, ovH_id, Category.id_comp]) (fun s t x => hadd hc x s t) u n hn hu`. Establish `e : (algebraMap K (DualNumber K)).comp (TrivSqZeroExt.fstHom K K K).toRingHom = (GlobalTheory.TorsConst.sc (0 : K)).toRingHom`.

Apply the tactic sequence `ext x <;> simp [TrivSqZeroExt.algebraMap_eq_inl]`. Use `conv_lhs => rw [key]`. Rewrite using `[Over.comp_left, GlobalTheory.TorsConst.ovH_left, ← e, ← Category.assoc, GlobalTheory.TorsConst.sp_comp]`.
-/
theorem GlobalTheory.TorsConst.torsion_eq_const : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] (f : Sp (DualNumber K) ⟶ Sp K), f = spMap (algebraMap K (DualNumber K)) → (∀ x y : Over.mk f ⟶ A, x * y = y * x) → ∀ (u : Over.mk f ⟶ A) (n : ℕ), 0 < n → u ^ n = 1 → u.left = spMap (algebraMap K (DualNumber K)) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ u.left := by
  intro K _ _ A _ f hf hc u n hn hu
  subst hf
  open GlobalTheory.TorsConst in
  have key : u = ovH (sc 0) ≫ u :=
    eq_zeroScale_of_pow_eq_one_of_affine_fieldAction hc (fun t x => ovH (sc t) ≫ x) (fun t x y => MonObj.comp_mul _ _ _)
      (fun a b x => by simp only [← Category.assoc, ← ovH_comp, sc_sc])
      (fun x => by simp only [sc_one, ovH_id, Category.id_comp]) (fun s t x => hadd hc x s t) u n hn hu
  have e : (algebraMap K (DualNumber K)).comp (TrivSqZeroExt.fstHom K K K).toRingHom = (GlobalTheory.TorsConst.sc (0 : K)).toRingHom := by
    ext x <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  conv_lhs => rw [key]
  rw [Over.comp_left, GlobalTheory.TorsConst.ovH_left, ← e, ← Category.assoc, GlobalTheory.TorsConst.sp_comp]
