import Development.EtaleCohomology.EtaleSheaves.LeafVanBStalkPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafSHSysPf
open LateralTheory.E.E4 LateralTheory.E.LeafVanBStalkPf

def Cof {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D) : Prop :=
  ∃ (Ω : Type) (_ : Field Ω) (_ : IsSepClosed Ω) (ω : c.pt →+* Ω),
    ∀ (j : J) (E : Type) (_ : CommRing E) (_ : Algebra (D.obj j) E) (_ : Algebra.Etale (D.obj j) E) (ψ : E →+* Ω),
      ψ.comp (algebraMap (D.obj j) E) = ω.comp (c.ι.app j).hom →
      ∃ (j' : J) (g : j ⟶ j') (φ : E →+* D.obj j'), φ.comp (algebraMap (D.obj j) E) = (D.map g).hom ∧
        ω.comp ((c.ι.app j').hom.comp φ) = ψ

/- English proof (translation)
Take `⟨j, f, rfl⟩` from `Limits.Concrete.isColimit_exists_rep D hc a`. Establish `hu : IsUnit (ω ((c.ι.app j).hom f))` using `isUnit_iff_ne_zero.2 ha`. Establish `: Algebra.Etale (D.obj j) (Localization.Away f)` using `Algebra.Etale.of_isLocalizationAway f`. Take `⟨j', g, φ, h1, -⟩` from `H j (Localization.Away f) inferInstance inferInstance this (IsLocalization.Away.lift f (g := ω.comp (c.ι.app j).hom) hu) (IsLocalization.Away.lift_comp f hu)`. Establish `e1 : (c.ι.app j).hom f = (c.ι.app j').hom ((D.map g).hom f)`.

Rewrite using `[← CommRingCat.comp_apply, c.w g]`. Rewrite using `[e1, ← h1, RingHom.comp_apply]`. Conclude with `(IsLocalization.Away.algebraMap_isUnit f).map ((c.ι.app j').hom.comp φ)`.
-/
theorem unit_of_cof {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D)
    (hc : IsColimit c) {Ω : Type} [Field Ω] (ω : c.pt →+* Ω)
    (H : ∀ (j : J) (E : Type) (_ : CommRing E) (_ : Algebra (D.obj j) E) (_ : Algebra.Etale (D.obj j) E) (ψ : E →+* Ω),
      ψ.comp (algebraMap (D.obj j) E) = ω.comp (c.ι.app j).hom →
      ∃ (j' : J) (g : j ⟶ j') (φ : E →+* D.obj j'), φ.comp (algebraMap (D.obj j) E) = (D.map g).hom ∧
        ω.comp ((c.ι.app j').hom.comp φ) = ψ)
    (a : c.pt) (ha : ω a ≠ 0) : IsUnit a := by
  obtain ⟨j, f, rfl⟩ := Limits.Concrete.isColimit_exists_rep D hc a
  have hu : IsUnit (ω ((c.ι.app j).hom f)) := isUnit_iff_ne_zero.2 ha
  have : Algebra.Etale (D.obj j) (Localization.Away f) := Algebra.Etale.of_isLocalizationAway f
  obtain ⟨j', g, φ, h1, -⟩ := H j (Localization.Away f) inferInstance inferInstance this
    (IsLocalization.Away.lift f (g := ω.comp (c.ι.app j).hom) hu) (IsLocalization.Away.lift_comp f hu)
  have e1 : (c.ι.app j).hom f = (c.ι.app j').hom ((D.map g).hom f) := by
    rw [← CommRingCat.comp_apply, c.w g]
  rw [e1, ← h1, RingHom.comp_apply]
  exact (IsLocalization.Away.algebraMap_isUnit f).map ((c.ι.app j').hom.comp φ)

/- English proof (translation)
Take `⟨Ω, _, _, ω, H⟩` from `hC`. Establish `key : ∀ a : c.pt, a ∈ nonunits c.pt → ω a = 0` using `fun a ha => by`. Assume the negation of the conclusion as `h`. Conclude with `ha (unit_of_cof D c hc ω H a h)`. Establish `: Nontrivial c.pt` using `ω.domain_nontrivial`.

Use `IsLocalRing.of_nonunits_add (fun a b ha hb hab => ?_)` and prove the remaining obligations. Use `hab.map ω` as an intermediate fact. Rewrite `this` using `[map_add, key a ha, key b hb, add_zero]`. Conclude with `not_isUnit_zero this`.
-/
theorem isLocalRing_of_cof {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D)
    (hc : IsColimit c) (hC : Cof D c) : IsLocalRing c.pt := by
  obtain ⟨Ω, _, _, ω, H⟩ := hC
  have key : ∀ a : c.pt, a ∈ nonunits c.pt → ω a = 0 := fun a ha => by
    by_contra h; exact ha (unit_of_cof D c hc ω H a h)
  have : Nontrivial c.pt := ω.domain_nontrivial
  refine IsLocalRing.of_nonunits_add (fun a b ha hb hab => ?_)
  have := hab.map ω
  rw [map_add, key a ha, key b hb, add_zero] at this
  exact not_isUnit_zero this

open Polynomial in
/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Take `⟨j1, P1, rfl⟩` from `hp`. Take `⟨j2, P2, rfl⟩` from `hq`. Use `⟨IsFiltered.max j1 j2, P1.map (D.map (IsFiltered.leftToMax j1 j2)).hom + P2.map (D.map (IsFiltered.rightToMax j1 j2)).hom, ?_⟩` and prove the remaining obligations.

Rewrite using `[Polynomial.map_add, Polynomial.map_map, Polynomial.map_map, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, c.w, c.w]`. Consider the case `monomial n a`. Take `⟨j, f, rfl⟩` from `Limits.Concrete.isColimit_exists_rep D hc a`. Conclude with `⟨j, monomial n f, by simp⟩`.
-/
theorem poly_rep {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D)
    (hc : IsColimit c) (p : c.pt[X]) : ∃ (j : J) (P : (D.obj j)[X]), P.map (c.ι.app j).hom = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨j1, P1, rfl⟩ := hp
    obtain ⟨j2, P2, rfl⟩ := hq
    refine ⟨IsFiltered.max j1 j2, P1.map (D.map (IsFiltered.leftToMax j1 j2)).hom +
      P2.map (D.map (IsFiltered.rightToMax j1 j2)).hom, ?_⟩
    rw [Polynomial.map_add, Polynomial.map_map, Polynomial.map_map, ← CommRingCat.hom_comp,
      ← CommRingCat.hom_comp, c.w, c.w]
  | monomial n a =>
    obtain ⟨j, f, rfl⟩ := Limits.Concrete.isColimit_exists_rep D hc a
    exact ⟨j, monomial n f, by simp⟩

open Polynomial in
/- English proof (translation)
Take `⟨j, P, hP⟩` from `poly_rep D c hc p`. Use `haveI : Nontrivial (((Functor.const J).obj c.pt).obj j) := inferInstanceAs (Nontrivial c.pt)`. Take `⟨Q, hQ, -, hm⟩` from `lifts_and_degree_eq_and_monic (f := (c.ι.app j).hom) ⟨P, hP⟩ hp`. Conclude with `⟨j, Q, hQ, hm⟩`.
-/
theorem monic_rep {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D)
    (hc : IsColimit c) [Nontrivial c.pt] (p : c.pt[X]) (hp : p.Monic) :
    ∃ (j : J) (P : (D.obj j)[X]), P.map (c.ι.app j).hom = p ∧ P.Monic := by
  obtain ⟨j, P, hP⟩ := poly_rep D c hc p
  haveI : Nontrivial (((Functor.const J).obj c.pt).obj j) := inferInstanceAs (Nontrivial c.pt)
  obtain ⟨Q, hQ, -, hm⟩ := lifts_and_degree_eq_and_monic (f := (c.ι.app j).hom) ⟨P, hP⟩ hp
  exact ⟨j, Q, hQ, hm⟩

open Polynomial in

/- English proof (translation)
Set `Q : StandardEtalePair (D.obj j)` to `⟨P, hP, P.derivative, ⟨1, 0, 1, by ring⟩⟩`. Set `_ : Algebra (D.obj j) Ω` to `(ω.comp (c.ι.app j).hom).toAlgebra`. Establish `hm : Q.HasMap y`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show aeval y P = 0`.

Rewrite using `[aeval_def, eval₂_eq_eval_map]`. Conclude with `hy`. Use `show IsUnit (aeval y (derivative P))`. Rewrite using `[aeval_def, eval₂_eq_eval_map]`. Conclude with `isUnit_iff_ne_zero.2 hd`.

Take `⟨j', g, φ, h1, h2⟩` from `H j Q.Ring inferInstance inferInstance inferInstance (Q.lift y hm).toRingHom (Q.lift y hm).comp_algebraMap`. Use `⟨(c.ι.app j').hom (φ Q.X), ?_, ?_⟩` and prove the remaining obligations. Establish `h0 : aeval Q.X Q.f = 0` using `Q.hasMap_X.1`. Use `congrArg ((c.ι.app j').hom.comp φ) h0` as an intermediate fact. Rewrite `this` using `[map_zero]`.

Rewrite using `[← this, aeval_def, hom_eval₂, RingHom.comp_assoc, h1, ← CommRingCat.hom_comp, c.w, Polynomial.eval_map]`. Both sides reduce to the same expression. Use `RingHom.congr_fun h2 Q.X` as an intermediate fact. Conclude with `this.trans (Q.lift_X y hm)`.
-/
theorem root_of_cof {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D)
    {Ω : Type} [Field Ω] (ω : c.pt →+* Ω)
    (H : ∀ (j : J) (E : Type) (_ : CommRing E) (_ : Algebra (D.obj j) E) (_ : Algebra.Etale (D.obj j) E) (ψ : E →+* Ω),
      ψ.comp (algebraMap (D.obj j) E) = ω.comp (c.ι.app j).hom →
      ∃ (j' : J) (g : j ⟶ j') (φ : E →+* D.obj j'), φ.comp (algebraMap (D.obj j) E) = (D.map g).hom ∧
        ω.comp ((c.ι.app j').hom.comp φ) = ψ)
    (j : J) (P : (D.obj j)[X]) (hP : P.Monic) (y : Ω) (hy : (P.map (ω.comp (c.ι.app j).hom)).eval y = 0)
    (hd : (P.derivative.map (ω.comp (c.ι.app j).hom)).eval y ≠ 0) :
    ∃ b : c.pt, (P.map (c.ι.app j).hom).eval b = 0 ∧ ω b = y := by
  let Q : StandardEtalePair (D.obj j) := ⟨P, hP, P.derivative, ⟨1, 0, 1, by ring⟩⟩
  let _ : Algebra (D.obj j) Ω := (ω.comp (c.ι.app j).hom).toAlgebra
  have hm : Q.HasMap y := by
    refine ⟨?_, ?_⟩
    · show aeval y P = 0
      rw [aeval_def, eval₂_eq_eval_map]; exact hy
    · show IsUnit (aeval y (derivative P))
      rw [aeval_def, eval₂_eq_eval_map]; exact isUnit_iff_ne_zero.2 hd
  obtain ⟨j', g, φ, h1, h2⟩ := H j Q.Ring inferInstance inferInstance inferInstance (Q.lift y hm).toRingHom
    (Q.lift y hm).comp_algebraMap
  refine ⟨(c.ι.app j').hom (φ Q.X), ?_, ?_⟩
  · have h0 : aeval Q.X Q.f = 0 := Q.hasMap_X.1
    have := congrArg ((c.ι.app j').hom.comp φ) h0
    rw [map_zero] at this
    rw [← this, aeval_def, hom_eval₂, RingHom.comp_assoc, h1, ← CommRingCat.hom_comp, c.w, Polynomial.eval_map]; rfl
  · have := RingHom.congr_fun h2 Q.X
    exact this.trans (Q.lift_X y hm)

structure NSys {B : Scheme.{0}} (U : B.Etale) (x : U.left) where
  J : Type
  [cat : SmallCategory J]
  [filt : IsFiltered J]
  D : J ⥤ CommRingCat.{0}
  V : J → B.Etale
  a : ∀ j, V j ⟶ U
  e : ∀ j, (V j).left ≅ Spec (D.obj j)
  tr : ∀ {j j' : J} (_ : j ⟶ j'), V j' ⟶ V j
  tr_a : ∀ {j j' : J} (g : j ⟶ j'), tr g ≫ a j = a j'
  tr_spec : ∀ {j j' : J} (g : j ⟶ j'), (e j').inv ≫ (tr g).left ≫ (e j).hom = Spec.map (D.map g)
  hx : ∀ j, x ∈ Set.range (a j).left
  c : Cocone D
  hc : IsColimit c
  cof : Cof D c
  t : Spec c.pt ⟶ U.left
  ht : ∀ j, t = Spec.map (c.ι.app j) ≫ (e j).inv ≫ (a j).left

attribute [instance] NSys.cat NSys.filt

def LeafNSys : Prop := ∀ {B : Scheme.{0}} (U : B.Etale) (x : U.left), Nonempty (NSys U x)

def LeafSHofCof : Prop := ∀ {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D),
  IsColimit c → Cof D c → SH c.pt

open Polynomial IsLocalRing in
/- English proof (translation)
Introduce `J _ _ D c hc hC`. Establish `hL` using `isLocalRing_of_cof D c hc hC`. Take `⟨Ω, _, _, ω, H⟩` from `hC`. Establish `hmax : ∀ a : c.pt, a ∈ maximalIdeal c.pt ↔ ω a = 0` using `fun a => by`. Rewrite using `[mem_maximalIdeal, mem_nonunits_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `h'`. Conclude with `h (unit_of_cof D c hc ω H a h')`. Introduce `h hu`.

Use `hu.map ω` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `not_isUnit_zero this`. Establish `: Nontrivial c.pt` using `ω.domain_nontrivial`. Establish `hH : HenselianLocalRing c.pt`.

Use `{ toIsLocalRing := hL, is_henselian := ?_ }` and prove the remaining obligations. Introduce `f hf a₀ h1 h2`. Take `⟨j, P, hP, hPm⟩` from `monic_rep D c hc f hf`. Establish `e : P.map (ω.comp (c.ι.app j).hom) = f.map ω` using `by rw [← Polynomial.map_map, hP]`. Take `⟨b, hb, hbω⟩` from `root_of_cof D c ω H j P hPm (ω a₀) (by rw [e, Polynomial.eval_map, eval₂_at_apply, ← hmax]; exact h1) (by rw [← derivative_map, e, derivative_map, Polynomial.eval_map, eval₂_at_apply]`.

Introduce `h0`. Use `h2.map ω` as an intermediate fact. Rewrite `this` using `[h0]`. Conclude with `not_isUnit_zero this)`. Use `⟨b, ?_, ?_⟩` and prove the remaining obligations.

Rewrite `hb` using `[hP]`. Conclude with `hb`. Rewrite using `[hmax, map_sub, hbω, sub_self]`. Use `⟨hH, ?_⟩` and prove the remaining obligations. Establish `hk : RingHom.ker (residue c.pt) ≤ RingHom.ker ω` using `fun a ha => by`.

Rewrite `ha` using `[RingHom.mem_ker, residue_eq_zero_iff]`. Conclude with `(hmax a).1 ha`. Set `ωb : ResidueField c.pt →+* Ω` to `RingHom.liftOfSurjective (residue c.pt) residue_surjective ⟨ω, hk⟩`. Establish `hωb : ωb.comp (residue c.pt) = ω` using `RingHom.liftOfRightInverse_comp _ _ _ _`. Use `IsSepClosed.of_exists_root _ (fun p hpm hirr hsep => ?_)` and prove the remaining obligations.

Establish `hl : p ∈ lifts (residue c.pt)` using `(lifts_iff_coeff_lifts p).2 (fun n => residue_surjective _)`. Take `⟨pt, hpt, -, hptm⟩` from `lifts_and_degree_eq_and_monic hl hpm`. Take `⟨j, P, hP, hPm⟩` from `monic_rep D c hc pt hptm`. Establish `e : P.map (ω.comp (c.ι.app j).hom) = p.map ωb`. Rewrite using `[← Polynomial.map_map, hP, ← hpt, Polynomial.map_map, hωb]`.

Establish `hdeg : (p.map ωb).degree ≠ 0`. Rewrite using `[degree_map]`. Introduce `h0`. Conclude with `hirr.not_isUnit (by rw [hpm.natDegree_eq_zero.1 (natDegree_eq_zero_iff_degree_le_zero.2 h0.le)]; exact isUnit_one)`. Take `⟨y, hy⟩` from `IsSepClosed.exists_root (p.map ωb) hdeg hsep.map`.

Establish `hd` using `hsep.map (f := ωb) |>.aeval_derivative_ne_zero (x := y) (by rw [coe_aeval_eq_eval]; exact hy)`. Rewrite `hd` using `[coe_aeval_eq_eval]`. Take `⟨b, hb, -⟩` from `root_of_cof D c ω H j P hPm y (by rw [e]; exact hy) (by rw [← derivative_map, e]; exact hd)`. Use `⟨residue c.pt b, ?_⟩` and prove the remaining obligations. Rewrite using `[← hpt, Polynomial.eval_map, eval₂_at_apply, ← hP, hb, map_zero]`.
-/
theorem SHofCof : LeafSHofCof := by
  intro J _ _ D c hc hC
  have hL := isLocalRing_of_cof D c hc hC
  obtain ⟨Ω, _, _, ω, H⟩ := hC
  have hmax : ∀ a : c.pt, a ∈ maximalIdeal c.pt ↔ ω a = 0 := fun a => by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro h; by_contra h'; exact h (unit_of_cof D c hc ω H a h')
    · intro h hu; have := hu.map ω; rw [h] at this; exact not_isUnit_zero this
  have : Nontrivial c.pt := ω.domain_nontrivial
  have hH : HenselianLocalRing c.pt := by
    refine { toIsLocalRing := hL, is_henselian := ?_ }
    intro f hf a₀ h1 h2
    obtain ⟨j, P, hP, hPm⟩ := monic_rep D c hc f hf
    have e : P.map (ω.comp (c.ι.app j).hom) = f.map ω := by rw [← Polynomial.map_map, hP]
    obtain ⟨b, hb, hbω⟩ := root_of_cof D c ω H j P hPm (ω a₀)
      (by rw [e, Polynomial.eval_map, eval₂_at_apply, ← hmax]; exact h1)
      (by rw [← derivative_map, e, derivative_map, Polynomial.eval_map, eval₂_at_apply]
          intro h0; have := h2.map ω; rw [h0] at this; exact not_isUnit_zero this)
    refine ⟨b, ?_, ?_⟩
    · rw [hP] at hb; exact hb
    · rw [hmax, map_sub, hbω, sub_self]
  refine ⟨hH, ?_⟩
  have hk : RingHom.ker (residue c.pt) ≤ RingHom.ker ω := fun a ha => by
    rw [RingHom.mem_ker, residue_eq_zero_iff] at ha; exact (hmax a).1 ha
  let ωb : ResidueField c.pt →+* Ω := RingHom.liftOfSurjective (residue c.pt) residue_surjective ⟨ω, hk⟩
  have hωb : ωb.comp (residue c.pt) = ω := RingHom.liftOfRightInverse_comp _ _ _ _
  refine IsSepClosed.of_exists_root _ (fun p hpm hirr hsep => ?_)
  have hl : p ∈ lifts (residue c.pt) := (lifts_iff_coeff_lifts p).2 (fun n => residue_surjective _)
  obtain ⟨pt, hpt, -, hptm⟩ := lifts_and_degree_eq_and_monic hl hpm
  obtain ⟨j, P, hP, hPm⟩ := monic_rep D c hc pt hptm
  have e : P.map (ω.comp (c.ι.app j).hom) = p.map ωb := by
    rw [← Polynomial.map_map, hP, ← hpt, Polynomial.map_map, hωb]
  have hdeg : (p.map ωb).degree ≠ 0 := by
    rw [degree_map]; intro h0
    exact hirr.not_isUnit (by rw [hpm.natDegree_eq_zero.1 (natDegree_eq_zero_iff_degree_le_zero.2 h0.le)]; exact isUnit_one)
  obtain ⟨y, hy⟩ := IsSepClosed.exists_root (p.map ωb) hdeg hsep.map
  have hd := hsep.map (f := ωb) |>.aeval_derivative_ne_zero (x := y) (by rw [coe_aeval_eq_eval]; exact hy)
  rw [coe_aeval_eq_eval] at hd
  obtain ⟨b, hb, -⟩ := root_of_cof D c ω H j P hPm y (by rw [e]; exact hy)
    (by rw [← derivative_map, e]; exact hd)
  refine ⟨residue c.pt b, ?_⟩
  rw [← hpt, Polynomial.eval_map, eval₂_at_apply, ← hP, hb, map_zero]

/- English proof (translation)
Introduce `B U x`. Take `⟨S⟩` from `hN U x`. Conclude with `⟨{ J := S.J D := S.D V := S.V a := S.a e := S.e tr := fun g => S.tr g tr_a := fun g => S.tr_a g tr_spec := fun g => S.tr_spec g hx := S.hx c := S.c hc := S.hc sh := hA S.D S.c S.hc S.cof t := S.t ht := S.ht }⟩`.
-/
theorem LeafSHSys_of (hN : LeafNSys) (hA : LeafSHofCof) : LeafSHSys := by
  intro B U x
  obtain ⟨S⟩ := hN U x
  exact ⟨{
    J := S.J
    D := S.D
    V := S.V
    a := S.a
    e := S.e
    tr := fun g => S.tr g
    tr_a := fun g => S.tr_a g
    tr_spec := fun g => S.tr_spec g
    hx := S.hx
    c := S.c
    hc := S.hc
    sh := hA S.D S.c S.hc S.cof
    t := S.t
    ht := S.ht }⟩

def LeafRingSys : Prop := ∀ (R : CommRingCat.{0}) (p : PrimeSpectrum R),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (u : ∀ j, R ⟶ D.obj j),
    (∀ {j j' : J} (g : j ⟶ j'), u j ≫ D.map g = u j') ∧ (∀ j, (u j).hom.Etale) ∧
    (∀ j, ∃ q : PrimeSpectrum (D.obj j), q.comap (u j).hom = p) ∧
    ∃ (c : Cocone D), Nonempty (IsColimit c) ∧ Cof D c

def LeafNSysGlue : Prop := LeafRingSys → LeafNSys

/- English proof (translation)
The claim follows from `LeafSHSys_of (hG hR) SHofCof`.
-/
theorem LeafSHSys_of_glue (hR : LeafRingSys) (hG : LeafNSysGlue) : LeafSHSys :=
  LeafSHSys_of (hG hR) SHofCof

end LateralTheory.E.LeafSHSysPf
