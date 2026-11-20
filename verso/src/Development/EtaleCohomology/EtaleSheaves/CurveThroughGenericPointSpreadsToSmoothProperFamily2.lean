import Development.EtaleCohomology.EtaleSheaves.LeafSpreadVCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGeoVCut

namespace LateralTheory.E.LeafGeoVV2Cut

def CurveThroughGenericPointSpreadsToSmoothProperFamily : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k)
  [IsProper p] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω], (∀ R : Subalgebra k Ω, R.FG → ringKrullDim R <
    topologicalKrullDim X) → ∀ {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 →
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) → genericPoint X ∈ Set.range e →
    ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
      Surjective γ1 → Surjective γ2 → FamilyVe (k := k) X c0 e γ1 γ2

def LeafDescendQF : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k)
  [IsProper p] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω], (∀ R : Subalgebra k Ω, R.FG → ringKrullDim R <
    topologicalKrullDim X) → ∀ {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 →
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) → genericPoint X ∈ Set.range e →
    ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
      Surjective γ1 → Surjective γ2 →
    ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D0 D1 D2 : Scheme.{0}) (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1)
      (f : D0 ⟶ X) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2)
      (hf : f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))),
      IsSeparated q ∧ QuasiCompact q ∧ SmoothOfRelativeDimension 1 q ∧
      IsSeparated (d1 ≫ q) ∧ QuasiCompact (d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d1 ≫ q) ∧
      IsSeparated (d2 ≫ d1 ≫ q) ∧ QuasiCompact (d2 ≫ d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d2 ≫ d1 ≫ q) ∧
      IsIntegral D0 ∧ IsIntegral D1 ∧ IsIntegral D2 ∧
      LocallyQuasiFinite (pullback.lift q f hf.symm) ∧ LocallyQuasiFinite d1 ∧ LocallyQuasiFinite d2 ∧
      topologicalKrullDim D0 ≤ ringKrullDim R + 1 ∧
      IsPullback v0 c0 q (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ∧
      IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ∧
      IsPullback v2 (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ∧
      γ1 ≫ v0 = v1 ≫ d1 ∧ γ2 ≫ v1 = v2 ≫ d2 ∧ v0 ≫ f = e

def LeafExtendZMT : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p]
  (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) (B : Scheme.{0}) (b : B ⟶ Sp k) [IsProper b]
  (ι : Sp R ⟶ B) [IsOpenImmersion ι], ι ≫ b = Spec.map (CommRingCat.ofHom (algebraMap k R)) →
  ∀ {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) (e : C0 ⟶ X),
    IsCurve c0 → IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) →
  ∀ {D0 D1 D2 : Scheme.{0}} (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1) (f : D0 ⟶ X) (v0 : C0 ⟶ D0)
    (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2) (hf : f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))),
    IsSeparated q → QuasiCompact q → SmoothOfRelativeDimension 1 q →
    IsSeparated (d1 ≫ q) → QuasiCompact (d1 ≫ q) → SmoothOfRelativeDimension 1 (d1 ≫ q) →
    IsSeparated (d2 ≫ d1 ≫ q) → QuasiCompact (d2 ≫ d1 ≫ q) → SmoothOfRelativeDimension 1 (d2 ≫ d1 ≫ q) →
    IsIntegral D0 → IsIntegral D1 → IsIntegral D2 →
    LocallyQuasiFinite (pullback.lift q f hf.symm) → LocallyQuasiFinite d1 → LocallyQuasiFinite d2 →
    IsPullback v0 c0 q (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) →
    IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) →
    IsPullback v2 (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) →
    γ1 ≫ v0 = v1 ≫ d1 → γ2 ≫ v1 = v2 ≫ d2 → v0 ≫ f = e →
    ∃ (Y0 Y1 Y2 : Scheme.{0}) (π : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1) (h : Y0 ⟶ X) (V : B.Opens)
      (u0 : C0 ⟶ Y0) (u1 : C1 ⟶ Y1) (u2 : C2 ⟶ Y2),
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι) ⊆ V ∧
      SmP π V ∧ SmP (g1 ≫ π) V ∧ SmP (g2 ≫ g1 ≫ π) V ∧ IsProper (g2 ≫ g1 ≫ h) ∧
      IrreducibleSpace Y0 ∧ topologicalKrullDim Y0 ≤ topologicalKrullDim D0 ∧
      IsPullback u0 c0 π (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι) ∧
      IsPullback u1 (γ1 ≫ c0) (g1 ≫ π) (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι) ∧
      IsPullback u2 (γ2 ≫ γ1 ≫ c0) (g2 ≫ g1 ≫ π) (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι) ∧
      γ1 ≫ u0 = u1 ≫ g1 ∧ γ2 ≫ u1 = u2 ≫ g2 ∧ u0 ≫ h = e

/- English proof (translation)
Introduce `k _ _ X _ p _ Ω _ _ _ hdim C0 c0 e hc0 he hη C1 C2 γ1 γ2 h1 h2 s1 s2`. Take `⟨R, hR, D0, D1, D2, q, d1, d2, f, v0, v1, v2, hf, sp0, qc0, sm0, sp1, qc1, sm1, sp2, qc2, sm2, i0, i1, i2, qf0, qf1, qf2, dD, P0, P1, P2, c1, c2, ve⟩` from `hD k p Ω hdim c0 e hc0 he hη C1 C2 γ1 γ2 h1 h2 s1 s2`. Establish `: Algebra.FiniteType k R` using `Subalgebra.fg_iff_finiteType R |>.mp hR`. Take `⟨B, b, ι, iB, pb, oι, hι, dB⟩` from `hB k R`. Take `⟨Y0, Y1, Y2, π, g1, g2, h, V, u0, u1, u2, hs, m0, m1, m2, f1, irrY, dY, Q0, Q1, Q2, e1, e2, ue⟩` from `hE k p Ω R B b ι hι c0 γ1 γ2 e hc0 h1 h2 he q d1 d2 f v0 v1 v2 hf sp0 qc0 sm0 sp1 qc1 sm1 sp2 qc2 sm2 i0 i1 i2 qf0 qf1 qf2 P0 P1 P2 c1 c2 ve`.

Establish `hR' : ringKrullDim R < topologicalKrullDim X` using `hdim R hR`. Take `⟨hle, hlt⟩` from `LateralTheory.E.LeafSpreadVCut.succ_le_of_lt hR'`. Use `hc0.1` as an intermediate fact. Take `⟨x⟩ : Nonempty C0` from `inferInstance`. Use `⟨B, Y0, Y1, Y2, b, V, π, g1, g2, h, Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι, u0, u1, u2, iB, pb, hs, m0, m1, m2, f1, lt_of_le_of_lt dB hR', irrY, dY.trans (dD.trans hle), lt_of_le_of_lt (dY.trans dD) hlt, ⟨u0 x, ?_⟩, Q0, Q1, Q2, e1, e2, ue⟩` and prove the remaining obligations.

Use `show π (u0 x) ∈ (V : Set B)`. Rewrite using `[← Scheme.Hom.comp_apply, Q0.w]`. Conclude with `hs ⟨c0 x, rfl⟩`.
-/
theorem spread_of (hD : LeafDescendQF) (hB : LateralTheory.E.LeafSpreadVCut.LeafCloseB) (hE : LeafExtendZMT) :
    CurveThroughGenericPointSpreadsToSmoothProperFamily := by
  intro k _ _ X _ p _ Ω _ _ _ hdim C0 c0 e hc0 he hη C1 C2 γ1 γ2 h1 h2 s1 s2
  obtain ⟨R, hR, D0, D1, D2, q, d1, d2, f, v0, v1, v2, hf, sp0, qc0, sm0, sp1, qc1, sm1, sp2, qc2, sm2, i0, i1, i2,
    qf0, qf1, qf2, dD, P0, P1, P2, c1, c2, ve⟩ := hD k p Ω hdim c0 e hc0 he hη C1 C2 γ1 γ2 h1 h2 s1 s2
  have : Algebra.FiniteType k R := Subalgebra.fg_iff_finiteType R |>.mp hR
  obtain ⟨B, b, ι, iB, pb, oι, hι, dB⟩ := hB k R
  obtain ⟨Y0, Y1, Y2, π, g1, g2, h, V, u0, u1, u2, hs, m0, m1, m2, f1, irrY, dY, Q0, Q1, Q2, e1, e2, ue⟩ :=
    hE k p Ω R B b ι hι c0 γ1 γ2 e hc0 h1 h2 he q d1 d2 f v0 v1 v2 hf sp0 qc0 sm0 sp1 qc1 sm1 sp2 qc2 sm2 i0 i1 i2
      qf0 qf1 qf2 P0 P1 P2 c1 c2 ve
  have hR' : ringKrullDim R < topologicalKrullDim X := hdim R hR
  obtain ⟨hle, hlt⟩ := LateralTheory.E.LeafSpreadVCut.succ_le_of_lt hR'
  have := hc0.1
  obtain ⟨x⟩ : Nonempty C0 := inferInstance
  refine ⟨B, Y0, Y1, Y2, b, V, π, g1, g2, h, Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι,
    u0, u1, u2, iB, pb, hs, m0, m1, m2, f1, lt_of_le_of_lt dB hR', irrY, dY.trans (dD.trans hle),
    lt_of_le_of_lt (dY.trans dD) hlt, ⟨u0 x, ?_⟩, Q0, Q1, Q2, e1, e2, ue⟩
  show π (u0 x) ∈ (V : Set B)
  rw [← Scheme.Hom.comp_apply, Q0.w]
  exact hs ⟨c0 x, rfl⟩

/- English proof (translation)
Introduce `k _ _ X _ p _ hd`. Take `⟨Ω, iF, iA, iK, C0, c0, e, hc0, he, hη, hdim⟩` from `hC k p hd`. Use `⟨Ω, iF, iA, iK, C0, c0, hc0, fun C1 C2 γ1 γ2 h1 h2 s1 s2 => ?_⟩` and prove the remaining obligations. Take `⟨B, Y0, Y1, Y2, b, V, π, g1, g2, h, s, u0, u1, u2, iB, pb, hs, m0, m1, m2, f1, dB, irr, dY, fin, ne, P0, P1, P2, w1, w2, ue⟩` from `hS k p Ω hdim c0 e hc0 he hη C1 C2 γ1 γ2 h1 h2 s1 s2`. Use `⟨B, Y0, Y1, Y2, b, V, π, g1, g2, h, s, u0, u1, u2, iB, pb, hs, m0, m1, m2, f1, ?_, dB, irr, dY, fin, ne, P0, P1, P2, w1, w2⟩` and prove the remaining obligations.

Take `⟨x0, hx0⟩` from `hη`. Take `⟨x1, rfl⟩` from `s1.surj x0`. Take `⟨x2, rfl⟩` from `s2.surj x1`. Establish `key : u2 ≫ g2 ≫ g1 ≫ h = γ2 ≫ γ1 ≫ e`. Rewrite using `[← ue, ← Category.assoc u2 g2, ← w2, Category.assoc, ← Category.assoc u1 g1, ← w1]`.

Simplify using `only [Category.assoc]`. Use `f1` as an intermediate fact. Use `surj_of_generic (g2 ≫ g1 ≫ h) ⟨u2 x2, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, key, ← hx0]`. Simplify using `only [Scheme.Hom.comp_apply]`.
-/
theorem geoV_of (hC : LeafCurveV) (hS : CurveThroughGenericPointSpreadsToSmoothProperFamily) : LateralTheory.E.LeafGeoCut.LeafGeoV := by
  intro k _ _ X _ p _ hd
  obtain ⟨Ω, iF, iA, iK, C0, c0, e, hc0, he, hη, hdim⟩ := hC k p hd
  refine ⟨Ω, iF, iA, iK, C0, c0, hc0, fun C1 C2 γ1 γ2 h1 h2 s1 s2 => ?_⟩
  obtain ⟨B, Y0, Y1, Y2, b, V, π, g1, g2, h, s, u0, u1, u2, iB, pb, hs, m0, m1, m2, f1, dB, irr, dY, fin, ne,
    P0, P1, P2, w1, w2, ue⟩ := hS k p Ω hdim c0 e hc0 he hη C1 C2 γ1 γ2 h1 h2 s1 s2
  refine ⟨B, Y0, Y1, Y2, b, V, π, g1, g2, h, s, u0, u1, u2, iB, pb, hs, m0, m1, m2, f1, ?_, dB, irr, dY, fin, ne,
    P0, P1, P2, w1, w2⟩
  obtain ⟨x0, hx0⟩ := hη
  obtain ⟨x1, rfl⟩ := s1.surj x0
  obtain ⟨x2, rfl⟩ := s2.surj x1
  have key : u2 ≫ g2 ≫ g1 ≫ h = γ2 ≫ γ1 ≫ e := by
    rw [← ue, ← Category.assoc u2 g2, ← w2, Category.assoc, ← Category.assoc u1 g1, ← w1]
    simp only [Category.assoc]
  have := f1
  refine surj_of_generic (g2 ≫ g1 ≫ h) ⟨u2 x2, ?_⟩
  rw [← Scheme.Hom.comp_apply, key, ← hx0]
  simp only [Scheme.Hom.comp_apply]

/- English proof (translation)
The claim follows from `geoV_of hC (spread_of hD hB hE)`.
-/
theorem goal_of (hC : LeafCurveV) (hD : LeafDescendQF) (hB : LateralTheory.E.LeafSpreadVCut.LeafCloseB)
    (hE : LeafExtendZMT) : LateralTheory.E.LeafGeoCut.LeafGeoV :=
  geoV_of hC (spread_of hD hB hE)

end LateralTheory.E.LeafGeoVV2Cut

end
