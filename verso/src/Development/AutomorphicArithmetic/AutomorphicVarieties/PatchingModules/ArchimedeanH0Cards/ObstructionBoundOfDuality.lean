import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ExactMid
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.CokerBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.GenTrick
import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ContOfKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.OdKill
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.MapConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.OdSESInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.OdLam
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.AmMaps
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.OdCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.H0LocalCardBoundedOfClsKerLeKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.DualBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ImgCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ExistsCore
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.Transl

open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W IsLocalRing

namespace UpperTheory.V.Pa.B2

/- English proof (translation)
Establish `hq : ∀ w (q : (D.Q w).X), f.fq w (r.fq w q) = a • q`. Introduce `w q`. Take `⟨m, rfl⟩` from `D.surj w q`. Rewrite using `[r.comm, f.comm, h, map_smul]`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`.

Simplify using `only [Dat.Hom.h2, Submodule.mapQ_apply, ← Submodule.Quotient.mk_smul]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [LinearMap.restrict_apply, Submodule.coe_smul]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations.

Use function extensionality and compare the values at `s`. Conclude with `h _`. Use function extensionality and compare the values at `w g`. Conclude with `hq w _`.
-/
private theorem h2_comp_eq_smul_of_comp_eq_smul {A Γ : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] {P : Pl Γ} {D D' : Dat A P}
    (r : D.Hom D') (f : D'.Hom D) (a : A) (h : ∀ m, f.f (r.f m) = a • m) (y : D.H2LocalConditions) : f.h2 (r.h2 y) = a • y := by
  have hq : ∀ w (q : (D.Q w).X), f.fq w (r.fq w q) = a • q := by
    intro w q
    obtain ⟨m, rfl⟩ := D.surj w q
    rw [r.comm, f.comm, h, map_smul]
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  simp only [Dat.Hom.h2, Submodule.mapQ_apply, ← Submodule.Quotient.mk_smul]
  congr 1
  apply Subtype.ext
  simp only [LinearMap.restrict_apply, Submodule.coe_smul]
  refine Prod.ext ?_ ?_
  · funext s
    exact h _
  · funext w g
    exact hq w _

/- English proof (translation)
Establish `hq : ∀ w (q : (D.Q w).X), a • q = 0`. Introduce `w q`. Take `⟨m, rfl⟩` from `D.surj w q`. Rewrite using `[← map_smul, h, map_zero]`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`.

Rewrite using `[← Submodule.Quotient.mk_smul]`. Establish `hz : a • z = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use function extensionality and compare the values at `s`.

Conclude with `h _`. Use function extensionality and compare the values at `w g`. Conclude with `hq w _`. Rewrite using `[hz, Submodule.Quotient.mk_zero]`.
-/
private theorem smul_H2_local_eq_zero_of_smul_eq_zero {A Γ : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] {P : Pl Γ} (D : Dat A P)
    (a : A) (h : ∀ m : D.M.X, a • m = 0) (y : D.H2LocalConditions) : a • y = 0 := by
  have hq : ∀ w (q : (D.Q w).X), a • q = 0 := by
    intro w q
    obtain ⟨m, rfl⟩ := D.surj w q
    rw [← map_smul, h, map_zero]
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [← Submodule.Quotient.mk_smul]
  have hz : a • z = 0 := by
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · funext s
      exact h _
    · funext w g
      exact hq w _
  rw [hz, Submodule.Quotient.mk_zero]

/- English proof (translation)
Set `g : (Fin m → K) → PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ m}` to `fun c => Ideal.Quotient.mk _ (∑ i : Fin m, c i • (PowerSeries.X : PowerSeries K) ^ (i : ℕ))`. Use `Finite.of_surjective g ?_` and prove the remaining obligations. Introduce `q`. Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Use `⟨fun i => PowerSeries.coeff (i : ℕ) f, ?_⟩` and prove the remaining obligations.

Apply `Ideal.Quotient.eq.mpr` to reduce the goal to its premises. Rewrite using `[Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]`. Introduce `n hn`. Rewrite using `[map_sub, map_sum]`. Simplify using `only [PowerSeries.coeff_smul, PowerSeries.coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]`.

Rewrite using `[Finset.sum_eq_single ⟨n, hn⟩]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[if_neg]`. Introduce `e`.

Conclude with `hb (Fin.ext e.symm)`. Simplify using the standard rewrite rules.
-/
private theorem finAm (K : Type) [Field K] [Finite K] (m : ℕ) :
    Finite (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ m}) := by
  classical
  let g : (Fin m → K) → PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ m} :=
    fun c => Ideal.Quotient.mk _ (∑ i : Fin m, c i • (PowerSeries.X : PowerSeries K) ^ (i : ℕ))
  refine Finite.of_surjective g ?_
  intro q
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨fun i => PowerSeries.coeff (i : ℕ) f, ?_⟩
  apply Ideal.Quotient.eq.mpr
  rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
  intro n hn
  rw [map_sub, map_sum]
  simp only [PowerSeries.coeff_smul, PowerSeries.coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single ⟨n, hn⟩]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro e
    exact hb (Fin.ext e.symm)
  · simp

section
variable {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n}

/- English proof (translation)
Apply `o.e.injective` to reduce the goal to its premises. Rewrite using `[map_smul, map_zero]`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_smul, Submodule.coe_zero, ← algebraMap_smul X a, ha, zero_smul]`.
-/
private theorem smul_eq_zero_of_algebraMap_eq_zero_of_isOd {X : Type} [CommRing X] [Algebra x.A X] {D : Dat x.A (plOf G)} (o : IsOd h x X D) (a : x.A)
    (ha : algebraMap x.A X a = 0) (y : D.M.X) : a • y = 0 := by
  apply o.e.injective
  rw [map_smul, map_zero]
  apply Subtype.ext
  rw [Submodule.coe_smul, Submodule.coe_zero, ← algebraMap_smul X a, ha, zero_smul]

set_option maxHeartbeats 1600000 in
/- English proof (translation)
Take `⟨f1, hf1⟩` from `odHom _ _ _ _ h _ x _ _ _ _ o' o uf`. Take `⟨g1, hg1⟩` from `odHom _ _ _ _ h _ x _ _ _ _ o o'' ug`. Take `⟨k1, hk1⟩` from `odHom _ _ _ _ h _ x _ _ _ _ o'' o uk`. Take `⟨r1, hr1⟩` from `odHom _ _ _ _ h _ x _ _ _ _ o o' ur`. Establish `s1` using `odSES _ _ _ _ h _ x _ _ _ _ _ _ o' o o'' uf ug f1 g1 hf1 hg1 i1 i2 i3`.

Establish `s2` using `odSES _ _ _ _ h _ x _ _ _ _ _ _ o'' o o' uk ur k1 r1 hk1 hr1 i4 i5 i6`. Establish `hcomp : ∀ m, f1.f (r1.f m) = a • m`. Introduce `m`. Apply `o.e.injective` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[hf1, hr1, Matrix.map_map, map_smul, Submodule.coe_smul]`. Use extensionality with `i j`. Simplify using `[i7]`. Establish `hex : g1.h2.ker ≤ f1.h2.range` using `exactMid _ _ _ _ _ _ f1 g1 s1 (odLam _ _ _ _ h _ x _ _ _ _ o o'' g1 s1.surj hA.ur)`. Establish `hon : Function.Surjective (mapH2 D.M.ρ D'.M.ρ r1.f (by continuity) r1.equiv)` using `hA.onto _ D.M D'.M (odKill _ _ _ _ h _ x _ _ o).1 r1.f r1.equiv s2.surj`.

Take `⟨hfin, hcard⟩` from `cokerBound _ _ _ _ _ _ k1 r1 s2 hon hF`. Establish `hfr : ∀ y, f1.h2 (r1.h2 y) = a • y` using `h2_comp_eq_smul_of_comp_eq_smul r1 f1 a hcomp`. Use `set R := LinearMap.range (LinearMap.lsmul x.A D.H2LocalConditions a) with hRdef`. Establish `hRF : R ≤ LinearMap.range f1.h2`. Introduce and unpack `_ ⟨y, rfl⟩`.

Conclude with `⟨r1.h2 y, by rw [hfr]; rfl⟩`. Rewrite using `[← Submodule.card_quotient_mul_card_quotient (LinearMap.range f1.h2) R hRF, mul_comm]`. Apply `Nat.mul_le_mul` to reduce the goal to its premises. Establish `hfk : Finite (D.H2LocalConditions ⧸ LinearMap.ker g1.h2)` using `Finite.of_equiv _ (LinearMap.quotKerEquivRange g1.h2).toEquiv.symm`. Establish `hs : Function.Surjective ((LinearMap.ker g1.h2).liftQ (LinearMap.range f1.h2).mkQ (by rw [Submodule.ker_mkQ]; exact hex))`.

Introduce `q`. Take `⟨z, rfl⟩` from `Submodule.mkQ_surjective _ q`. Conclude with `⟨Submodule.Quotient.mk z, rfl⟩`. Combine the equalities or inequalities in the displayed calculation. Establish `hker : LinearMap.range r1.h2 ≤ LinearMap.ker (R.mkQ ∘ₗ f1.h2)`.

Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hfr]`. Conclude with `⟨y, rfl⟩`. Establish `hmap : (LinearMap.range f1.h2).map R.mkQ = LinearMap.range ((LinearMap.range r1.h2).liftQ _ hker)`. Rewrite using `[Submodule.range_liftQ, LinearMap.range_comp]`.

Rewrite using `[hmap]`. Use `le_trans ?_ hcard` and prove the remaining obligations. Conclude with `Nat.card_le_card_of_surjective _ (LinearMap.surjective_rangeRestrict _)`.
-/
private theorem step {X X' X'' : Type} [CommRing X] [Algebra x.A X] [CommRing X'] [Algebra x.A X'] [CommRing X'']
    [Algebra x.A X''] {D D' D'' : Dat x.A (plOf G)} (o : IsOd h x X D) (o' : IsOd h x X' D') (o'' : IsOd h x X'' D'')
    {d : ℕ} {dv : L.Vl → ℕ} (hA : CohAx G d dv) (a : x.A) [Finite D''.H2LocalConditions] (hF : Finite D''.Ck2)
    (uf : X' →ₗ[x.A] X) (ug : X →ₗ[x.A] X'') (uk : X'' →ₗ[x.A] X) (ur : X →ₗ[x.A] X')
    (i1 : Function.Injective uf) (i2 : Function.Exact uf ug) (i3 : Function.Surjective ug) (i4 : Function.Injective uk)
    (i5 : Function.Exact uk ur) (i6 : Function.Surjective ur) (i7 : ∀ y, uf (ur y) = a • y) :
    Nat.card (D.H2LocalConditions ⧸ LinearMap.range (LinearMap.lsmul x.A D.H2LocalConditions a)) ≤ Nat.card D''.H2LocalConditions * Nat.card D''.Ck2 := by
  obtain ⟨f1, hf1⟩ := odHom _ _ _ _ h _ x _ _ _ _ o' o uf
  obtain ⟨g1, hg1⟩ := odHom _ _ _ _ h _ x _ _ _ _ o o'' ug
  obtain ⟨k1, hk1⟩ := odHom _ _ _ _ h _ x _ _ _ _ o'' o uk
  obtain ⟨r1, hr1⟩ := odHom _ _ _ _ h _ x _ _ _ _ o o' ur
  have s1 := odSES _ _ _ _ h _ x _ _ _ _ _ _ o' o o'' uf ug f1 g1 hf1 hg1 i1 i2 i3
  have s2 := odSES _ _ _ _ h _ x _ _ _ _ _ _ o'' o o' uk ur k1 r1 hk1 hr1 i4 i5 i6
  have hcomp : ∀ m, f1.f (r1.f m) = a • m := by
    intro m
    apply o.e.injective
    apply Subtype.ext
    rw [hf1, hr1, Matrix.map_map, map_smul, Submodule.coe_smul]
    ext i j
    simp [i7]
  have hex : g1.h2.ker ≤ f1.h2.range :=
    exactMid _ _ _ _ _ _ f1 g1 s1 (odLam _ _ _ _ h _ x _ _ _ _ o o'' g1 s1.surj hA.ur)
  have hon : Function.Surjective (mapH2 D.M.ρ D'.M.ρ r1.f (by continuity) r1.equiv) :=
    hA.onto _ D.M D'.M (odKill _ _ _ _ h _ x _ _ o).1 r1.f r1.equiv s2.surj
  obtain ⟨hfin, hcard⟩ := cokerBound _ _ _ _ _ _ k1 r1 s2 hon hF
  have hfr : ∀ y, f1.h2 (r1.h2 y) = a • y := h2_comp_eq_smul_of_comp_eq_smul r1 f1 a hcomp
  set R := LinearMap.range (LinearMap.lsmul x.A D.H2LocalConditions a) with hRdef
  have hRF : R ≤ LinearMap.range f1.h2 := by
    rintro _ ⟨y, rfl⟩
    exact ⟨r1.h2 y, by rw [hfr]; rfl⟩
  rw [← Submodule.card_quotient_mul_card_quotient (LinearMap.range f1.h2) R hRF, mul_comm]
  apply Nat.mul_le_mul
  · have hfk : Finite (D.H2LocalConditions ⧸ LinearMap.ker g1.h2) :=
      Finite.of_equiv _ (LinearMap.quotKerEquivRange g1.h2).toEquiv.symm
    have hs : Function.Surjective ((LinearMap.ker g1.h2).liftQ (LinearMap.range f1.h2).mkQ
        (by rw [Submodule.ker_mkQ]; exact hex)) := by
      intro q
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ q
      exact ⟨Submodule.Quotient.mk z, rfl⟩
    calc Nat.card (D.H2LocalConditions ⧸ LinearMap.range f1.h2) ≤ Nat.card (D.H2LocalConditions ⧸ LinearMap.ker g1.h2) :=
          Nat.card_le_card_of_surjective _ hs
      _ = Nat.card (LinearMap.range g1.h2) := Nat.card_congr (LinearMap.quotKerEquivRange g1.h2).toEquiv
      _ ≤ Nat.card D''.H2LocalConditions := Nat.card_le_card_of_injective _ Subtype.val_injective
  · have hker : LinearMap.range r1.h2 ≤ LinearMap.ker (R.mkQ ∘ₗ f1.h2) := by
      rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hfr]
      exact ⟨y, rfl⟩
    have hmap : (LinearMap.range f1.h2).map R.mkQ = LinearMap.range ((LinearMap.range r1.h2).liftQ _ hker) := by
      rw [Submodule.range_liftQ, LinearMap.range_comp]
    rw [hmap]
    refine le_trans ?_ hcard
    exact Nat.card_le_card_of_surjective _ (LinearMap.surjective_rangeRestrict _)

end

set_option maxHeartbeats 800000 in
/- English proof (translation)
Introduce `l _ L G0 T n x k al d hl h0 hN hH hE`. Take `⟨dv0, hA0⟩` from `h0`. Take `⟨C0, hC0⟩` from `sel0 l L G0 n x k d dv0 hl hA0`. Take `⟨Cn, hCn⟩` from `selN l L G0 T n x al hH hE`. Take `⟨Ch, hCh⟩` from `H0_local_card_bounded_of_cls_ker_le_ker l L G0 n x`.

Take `⟨Cd, hCd⟩` from `dualBound l L G0 n x`. Establish `hres : Nat.card (ResidueField x.A) = Nat.card x.K` using `Nat.card_congr PowerSeries.residueFieldOfPowerSeries.toEquiv`. Use `haveI : Finite (ResidueField x.A) := Finite.of_equiv _ PowerSeries.residueFieldOfPowerSeries.toEquiv.symm`. Establish `hzero : ∀ e, algebraMap x.A (x.Am e) (x.t ^ e) = 0` using `fun e => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)`. Use `haveI : ∀ e, Finite (x.Am e) := fun e => finAm x.K e`.

Use `⟨C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd, fun m => ?_⟩` and prove the remaining obligations. Use `filter_upwards [hCn m] with N hNm`. Introduce `z hz`. Take `⟨dvN, hAN⟩` from `hN N`. Take `⟨D, ⟨o⟩⟩` from `odEx l L (T.GN N) G0 (T.h N) n x (x.Am m) ⟨m, hzero m⟩`.

Take `⟨ξ, hξ⟩` from `transl l L (T.GN N) G0 (T.h N) n x k (x.Am m) D (k.g + 1) z hl ⟨m, hzero m⟩ o hAN.ur hz`. Use `haveI : Finite D.H2LocalConditions := (odCount l L (T.GN N) G0 (T.h N) n x (x.Am m) D d dvN hl o hAN).1`. Establish `hbound : ∀ e ≤ m, Nat.card (D.H2LocalConditions ⧸ LinearMap.range (LinearMap.lsmul x.A D.H2LocalConditions (x.t ^ e))) ≤ Nat.card (ResidueField x.A) ^ (k.g * e + (C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd))`. Introduce `e he`. Rewrite using `[hres]`.

Take `⟨uf, ug, uk, ur, i1, i2, i3, i4, i5, i6, i7⟩` from `amMaps x.K e m he`. Take `⟨D1, ⟨o1⟩⟩` from `odEx l L (T.GN N) G0 (T.h N) n x (x.Am (m - e)) ⟨m - e, hzero (m - e)⟩`. Take `⟨D2, ⟨o2⟩⟩` from `odEx l L (T.GN N) G0 (T.h N) n x (x.Am e) ⟨e, hzero e⟩`. Take `⟨D0, ⟨o0⟩⟩` from `odEx l L G0 G0 (Glob.Hom.refl G0) n x (x.Am e) ⟨e, hzero e⟩`. Take `⟨hf2, hc2, hcnt⟩` from `odCount l L (T.GN N) G0 (T.h N) n x (x.Am e) D2 d dvN hl o2 hAN`.

Use `haveI := hf2`. Establish `hs` using `step o o1 o2 hAN (x.t ^ e) hc2 uf ug uk ur i1 i2 i3 i4 i5 i6 i7`. Establish `hck` using `hAN.ck _ D2 (odKill _ _ _ _ _ _ x _ _ o2).1`. Establish `hsel` using `hNm e he D2 D0 o2 o0 (hA0.fin _ D0.M (odKill _ _ _ _ _ _ x _ _ o0).1).1`. Establish `hs0` using `hC0 e D0 o0`.

Establish `hprod : ∏ v, Nat.card (H0 (D2.Q (inV (T.GN N) v)).ρ) ≤ (Nat.card x.K ^ Ch) ^ Fintype.card L.Vl`. Rewrite using `[← Finset.card_univ]`. Conclude with `Finset.prod_le_pow_card _ _ _ (fun v _ => hCh (T.GN N) (T.h N) e D2 o2 v)`. Establish `hd` using `hCd (T.GN N) (T.h N) e D2 o2`. Combine the equalities or inequalities in the displayed calculation.

Apply `Nat.mul_le_mul` to reduce the goal to its premises. Use `hcnt.trans ?_` and prove the remaining obligations. Apply `Nat.mul_le_mul _ hd` to reduce the goal to its premises. Apply `Nat.mul_le_mul _ hprod` to reduce the goal to its premises. Conclude with `hsel.trans (Nat.mul_le_mul_right _ hs0)`.

Conclude with `hck.trans hd`. Use `_ = Nat.card x.K ^ (k.g * e + (C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd)) := by`. Rewrite using `[← pow_mul]`. Simplify using `only [← pow_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `hkill : ∀ y : D.H2LocalConditions, x.t ^ m • y = 0` using `smul_H2_local_eq_zero_of_smul_eq_zero D _ (smul_eq_zero_of_algebraMap_eq_zero_of_isOd o _ (hzero m))`. Take `⟨c, hcu, hc⟩` from `genTrick x.A D.H2LocalConditions x.t k.g (C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd) m PowerSeries.X_irreducible hkill hbound (fun i => Submodule.Quotient.mk (ξ i))`. Use `⟨c, hcu, ?_⟩` and prove the remaining obligations. Establish `hmem : ↑(∑ i, (x.t ^ (C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd) * c i) • ξ i) ∈ D.selmerSecondCoboundaries`.

Establish `hsum : (∑ i, (x.t ^ (C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd) * c i) • ξ i) = x.t ^ (C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd) • ∑ i, c i • ξ i`. Rewrite using `[Finset.smul_sum]`. Simplify using `only [mul_smul]`. Rewrite using `[hsum]`. Simplify using `only [← Submodule.Quotient.mk_smul] at hc`.

Establish `h1 : Submodule.Quotient.mk (p` using `Submodule.comap D.selmerSecondCocycles.subtype D.selmerSecondCoboundaries) (x.t ^ (C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd) • ∑ i, c i • ξ i) = 0 := by`. Rewrite using `[Submodule.Quotient.mk_smul, ← Submodule.mkQ_apply, map_sum]`. Conclude with `hc`. Conclude with `Submodule.mem_comap.mp ((Submodule.Quotient.mk_eq_zero (Submodule.comap D.selmerSecondCocycles.subtype D.selmerSecondCoboundaries)).mp h1)`. Take `⟨Ψ, hΨ, hΨe⟩` from `hξ _ hmem`.

Use `⟨Ψ, hΨ, fun j γ a b => ?_⟩` and prove the remaining obligations. Rewrite using `[hΨe, Finset.smul_sum]`. Simplify using `only [mul_smul]`.
-/
theorem obstructionBound_of_duality : ObstructionBoundFromDuality := by
  intro l _ L G0 T n x k al d hl h0 hN hH hE
  obtain ⟨dv0, hA0⟩ := h0
  obtain ⟨C0, hC0⟩ := sel0 l L G0 n x k d dv0 hl hA0
  obtain ⟨Cn, hCn⟩ := selN l L G0 T n x al hH hE
  obtain ⟨Ch, hCh⟩ := H0_local_card_bounded_of_cls_ker_le_ker l L G0 n x
  obtain ⟨Cd, hCd⟩ := dualBound l L G0 n x
  have hres : Nat.card (ResidueField x.A) = Nat.card x.K :=
    Nat.card_congr PowerSeries.residueFieldOfPowerSeries.toEquiv
  haveI : Finite (ResidueField x.A) := Finite.of_equiv _ PowerSeries.residueFieldOfPowerSeries.toEquiv.symm
  have hzero : ∀ e, algebraMap x.A (x.Am e) (x.t ^ e) = 0 := fun e =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  haveI : ∀ e, Finite (x.Am e) := fun e => finAm x.K e
  refine ⟨C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd, fun m => ?_⟩
  filter_upwards [hCn m] with N hNm
  intro z hz
  obtain ⟨dvN, hAN⟩ := hN N
  obtain ⟨D, ⟨o⟩⟩ := odEx l L (T.GN N) G0 (T.h N) n x (x.Am m) ⟨m, hzero m⟩
  obtain ⟨ξ, hξ⟩ := transl l L (T.GN N) G0 (T.h N) n x k (x.Am m) D (k.g + 1) z hl ⟨m, hzero m⟩ o hAN.ur hz
  haveI : Finite D.H2LocalConditions := (odCount l L (T.GN N) G0 (T.h N) n x (x.Am m) D d dvN hl o hAN).1
  have hbound : ∀ e ≤ m, Nat.card (D.H2LocalConditions ⧸ LinearMap.range (LinearMap.lsmul x.A D.H2LocalConditions (x.t ^ e))) ≤
      Nat.card (ResidueField x.A) ^ (k.g * e + (C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd)) := by
    intro e he
    rw [hres]
    obtain ⟨uf, ug, uk, ur, i1, i2, i3, i4, i5, i6, i7⟩ := amMaps x.K e m he
    obtain ⟨D1, ⟨o1⟩⟩ := odEx l L (T.GN N) G0 (T.h N) n x (x.Am (m - e)) ⟨m - e, hzero (m - e)⟩
    obtain ⟨D2, ⟨o2⟩⟩ := odEx l L (T.GN N) G0 (T.h N) n x (x.Am e) ⟨e, hzero e⟩
    obtain ⟨D0, ⟨o0⟩⟩ := odEx l L G0 G0 (Glob.Hom.refl G0) n x (x.Am e) ⟨e, hzero e⟩
    obtain ⟨hf2, hc2, hcnt⟩ := odCount l L (T.GN N) G0 (T.h N) n x (x.Am e) D2 d dvN hl o2 hAN
    haveI := hf2
    have hs := step o o1 o2 hAN (x.t ^ e) hc2 uf ug uk ur i1 i2 i3 i4 i5 i6 i7
    have hck := hAN.ck _ D2 (odKill _ _ _ _ _ _ x _ _ o2).1
    have hsel := hNm e he D2 D0 o2 o0 (hA0.fin _ D0.M (odKill _ _ _ _ _ _ x _ _ o0).1).1
    have hs0 := hC0 e D0 o0
    have hprod : ∏ v, Nat.card (H0 (D2.Q (inV (T.GN N) v)).ρ) ≤ (Nat.card x.K ^ Ch) ^ Fintype.card L.Vl := by
      rw [← Finset.card_univ]
      exact Finset.prod_le_pow_card _ _ _ (fun v _ => hCh (T.GN N) (T.h N) e D2 o2 v)
    have hd := hCd (T.GN N) (T.h N) e D2 o2
    calc _ ≤ Nat.card D2.H2LocalConditions * Nat.card D2.Ck2 := hs
      _ ≤ ((Nat.card x.K ^ (k.g * e + C0) * Nat.card x.K ^ Cn) * (Nat.card x.K ^ Ch) ^ Fintype.card L.Vl
            * Nat.card x.K ^ Cd) * Nat.card x.K ^ Cd := by
          apply Nat.mul_le_mul
          · refine hcnt.trans ?_
            apply Nat.mul_le_mul _ hd
            apply Nat.mul_le_mul _ hprod
            exact hsel.trans (Nat.mul_le_mul_right _ hs0)
          · exact hck.trans hd
      _ = Nat.card x.K ^ (k.g * e + (C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd)) := by
          rw [← pow_mul]
          simp only [← pow_add]
          congr 1
          ring
  have hkill : ∀ y : D.H2LocalConditions, x.t ^ m • y = 0 := smul_H2_local_eq_zero_of_smul_eq_zero D _ (smul_eq_zero_of_algebraMap_eq_zero_of_isOd o _ (hzero m))
  obtain ⟨c, hcu, hc⟩ := genTrick x.A D.H2LocalConditions x.t k.g (C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd) m
    PowerSeries.X_irreducible hkill hbound (fun i => Submodule.Quotient.mk (ξ i))
  refine ⟨c, hcu, ?_⟩
  have hmem : ↑(∑ i, (x.t ^ (C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd) * c i) • ξ i) ∈ D.selmerSecondCoboundaries := by
    have hsum : (∑ i, (x.t ^ (C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd) * c i) • ξ i) =
        x.t ^ (C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd) • ∑ i, c i • ξ i := by
      rw [Finset.smul_sum]
      simp only [mul_smul]
    rw [hsum]
    simp only [← Submodule.Quotient.mk_smul] at hc
    have h1 : Submodule.Quotient.mk (p := Submodule.comap D.selmerSecondCocycles.subtype D.selmerSecondCoboundaries)
        (x.t ^ (C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd) • ∑ i, c i • ξ i) = 0 := by
      rw [Submodule.Quotient.mk_smul, ← Submodule.mkQ_apply, map_sum]
      exact hc
    exact Submodule.mem_comap.mp ((Submodule.Quotient.mk_eq_zero (Submodule.comap D.selmerSecondCocycles.subtype D.selmerSecondCoboundaries)).mp h1)
  obtain ⟨Ψ, hΨ, hΨe⟩ := hξ _ hmem
  refine ⟨Ψ, hΨ, fun j γ a b => ?_⟩
  rw [hΨe, Finset.smul_sum]
  simp only [mul_smul]

end UpperTheory.V.Pa.B2
