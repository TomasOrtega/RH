import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PolarisedAbelianVarietyPTorsionStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.OrderPSquaredExtremalColengthStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PolarisedAugmentationTheoremStatement
import ReciprocityTheory.DualLattices.MemAugIdeal
import ReciprocityTheory.DualLattices.IsLocalOfIntegers
import ReciprocityTheory.DualLattices.ProdDvdOfIso
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR.OrdCurve

/- English proof (translation)
Use `haveI := hc`. Establish `hd : ∀ n : ℕ, ringChar (R ⧸ (Ideal.span {(p : R)}) ^ n) ∣ p ^ n` using `fun n => by`. Apply `ringChar.dvd` to reduce the goal to its premises. Rewrite using `[← map_natCast (Ideal.Quotient.mk ((Ideal.span {(p : R)}) ^ n)), Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]`. Conclude with `Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n`.

Use `⟨IsAdicComplete.liftRingHom (Ideal.span {(p : R)}) (fun n => (ZMod.castHom (hd n) (R ⧸ (Ideal.span {(p : R)}) ^ n)).comp (PadicInt.toZModPow n)) ?_⟩` and prove the remaining obligations. Introduce `m n hle`. Rewrite using `[← PadicInt.zmod_cast_comp_toZModPow m n hle, ← RingHom.comp_assoc, ← RingHom.comp_assoc]`. Use `congr 1`. Conclude with `RingHom.ext_zmod _ _`.
-/
theorem nonempty_padicInt_hom (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (hc : IsAdicComplete (Ideal.span {(p : R)}) R) : Nonempty (ℤ_[p] →+* R) := by
  haveI := hc
  have hd : ∀ n : ℕ, ringChar (R ⧸ (Ideal.span {(p : R)}) ^ n) ∣ p ^ n := fun n => by
    apply ringChar.dvd
    rw [← map_natCast (Ideal.Quotient.mk ((Ideal.span {(p : R)}) ^ n)),
      Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
    exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n
  refine ⟨IsAdicComplete.liftRingHom (Ideal.span {(p : R)})
    (fun n => (ZMod.castHom (hd n) (R ⧸ (Ideal.span {(p : R)}) ^ n)).comp
      (PadicInt.toZModPow n)) ?_⟩
  intro m n hle
  rw [← PadicInt.zmod_cast_comp_toZModPow m n hle, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
  congr 1
  exact RingHom.ext_zmod _ _

variable {R : Type} [CommRing R]

/- English proof (translation)
The claim follows from `h.inj.comp e.injective add x y := by simpa using h.add (e x) (e y) range z := by rw [h.range z] exact ⟨fun ⟨x, hx⟩ => ⟨e.symm x, by simpa using hx⟩, fun ⟨x, hx⟩ => ⟨e x, hx⟩⟩`.
-/
theorem isTorsPts_comp {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {p : ℕ} {N N' : Type}
    [AddCommGroup N] [AddCommGroup N'] {pt : N → (sp (R₀ := R) R ⟶ G)}
    (h : IsTorsPts G p pt) (e : N' ≃+ N) : IsTorsPts G p (fun x => pt (e x)) where
  inj := h.inj.comp e.injective
  add x y := by simpa using h.add (e x) (e y)
  range z := by
    rw [h.range z]
    exact ⟨fun ⟨x, hx⟩ => ⟨e.symm x, by simpa using hx⟩, fun ⟨x, hx⟩ => ⟨e x, hx⟩⟩

/- English proof (translation)
Use extensionality with `f`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha⟩`. Use `⟨fun x => f (e.symm x), ⟨a, fun x φ h => ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `ha (e.symm x) φ (by simpa using h)`.

Use extensionality with `x`. Simplify using `[LinearMap.funLeft_apply]`. Introduce and unpack `⟨g, ⟨a, ha⟩, rfl⟩`. Conclude with `⟨a, fun x φ h => ha (e x) φ h⟩`.
-/
theorem torsFun_comp {C : Type} [Field C] [Algebra R C] {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] {p : ℕ} (T : TorsRep G p) {N N' : Type} [AddCommGroup N] [AddCommGroup N'] (pt : N → (sp (R₀ := R) R ⟶ G))
    (e : N' ≃+ N) :
    torsFun C T (fun x => pt (e x)) =
      (torsFun C T pt).map (LinearMap.funLeft R C (e : N' → N)) := by
  ext f
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fun x => f (e.symm x), ⟨a, fun x φ h => ?_⟩, ?_⟩
    · exact ha (e.symm x) φ (by simpa using h)
    · ext x
      simp [LinearMap.funLeft_apply]
  · rintro ⟨g, ⟨a, ha⟩, rfl⟩
    exact ⟨a, fun x φ h => ha (e x) φ h⟩

/- English proof (translation)
Use `h.add 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `left_eq_mul.mp this`.
-/
theorem pt_zero {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {p : ℕ} {N : Type}
    [AddCommGroup N] {pt : N → (sp (R₀ := R) R ⟶ G)} (h : IsTorsPts G p pt) : pt 0 = 1 := by
  have := h.add 0 0
  rw [add_zero] at this
  exact left_eq_mul.mp this

/- English proof (translation)
Use `haveI : IsLocalRing R := isLocal_of_integers hv`. Take `⟨t, rfl⟩` from `(hpt.range z).1 hz`. Establish `hex : ∀ x, ∃! φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt x` using `fun x => T.univ R (pt x) ((hpt.range _).2 ⟨x, rfl⟩)`. Use `choose φ hφ hφu using hex`. Set `k` to `IsLocalRing.ResidueField R`.

Establish `hne : (Algebra.ofId R k).comp (φ t) ≠ (Algebra.ofId R k).comp (φ 0)`. Introduce `e`. Apply `hk k` to reduce the goal to its premises. Rewrite using `[← hφ t, ← Category.assoc, Chart.spMap_comp, e, ← Chart.spMap_comp, Category.assoc, hφ 0, pt_zero hpt]`. Conclude with `MonObj.comp_one _`.

Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, (Algebra.ofId R k) (φ t a) ≠ (Algebra.ofId R k) (φ 0 a) := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hne (AlgHom.ext hcon)`. Use `⟨t, fun x => algebraMap R C (φ x a), ⟨a, fun x ψ h => ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hφu x ψ h]`. Establish `hu : IsUnit (φ t a - φ 0 a)`. Assume the negation of the conclusion as `hn`. Apply `ha` to reduce the goal to its premises. Establish `hm : φ t a - φ 0 a ∈ IsLocalRing.maximalIdeal R` using `hn`.

Use `(Ideal.Quotient.eq_zero_iff_mem).2 hm` as an intermediate fact. Rewrite `this` using `[map_sub, sub_eq_zero]`. Conclude with `this`. Rewrite using `[← map_sub]`. Conclude with `hv.one_of_isUnit hu`.
-/
theorem exists_far {p : ℕ} {C : Type} [Field C] [Algebra R C] {v : Valuation C NNReal}
    (hv : v.Integers R) {G : Over (Spec (CommRingCat.of R))} [GrpObj G] (T : TorsRep G p)
    {N : Type} [AddCommGroup N] {pt : N → (sp (R₀ := R) R ⟶ G)} (hpt : IsTorsPts G p pt)
    {z : sp (R₀ := R) R ⟶ G} (hz : z ^ p = 1)
    (hk : ∀ (k : Type) [Field k] [Algebra R k], spMap (Algebra.ofId R k) ≫ z ≠ 1) :
    ∃ t : N, ∃ g ∈ torsFun C T pt, v (g t - g 0) = 1 := by
  haveI : IsLocalRing R := isLocal_of_integers hv
  obtain ⟨t, rfl⟩ := (hpt.range z).1 hz
  have hex : ∀ x, ∃! φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt x := fun x =>
    T.univ R (pt x) ((hpt.range _).2 ⟨x, rfl⟩)
  choose φ hφ hφu using hex
  let k := IsLocalRing.ResidueField R
  have hne : (Algebra.ofId R k).comp (φ t) ≠ (Algebra.ofId R k).comp (φ 0) := by
    intro e
    apply hk k
    rw [← hφ t, ← Category.assoc, Chart.spMap_comp, e, ← Chart.spMap_comp, Category.assoc, hφ 0,
      pt_zero hpt]
    exact MonObj.comp_one _
  obtain ⟨a, ha⟩ : ∃ a, (Algebra.ofId R k) (φ t a) ≠ (Algebra.ofId R k) (φ 0 a) := by
    by_contra hcon
    push_neg at hcon
    exact hne (AlgHom.ext hcon)
  refine ⟨t, fun x => algebraMap R C (φ x a), ⟨a, fun x ψ h => ?_⟩, ?_⟩
  · rw [hφu x ψ h]
  · have hu : IsUnit (φ t a - φ 0 a) := by
      by_contra hn
      apply ha
      have hm : φ t a - φ 0 a ∈ IsLocalRing.maximalIdeal R := hn
      have := (Ideal.Quotient.eq_zero_iff_mem).2 hm
      rw [map_sub, sub_eq_zero] at this
      exact this
    rw [← map_sub]
    exact hv.one_of_isUnit hu

/- English proof (translation)
Establish `hall` using `hgp p 1 C v R ℤ_[p] AlgEquiv.refl cp hs H`. Simplify using `only at hall`. Take `⟨cA, cN, cO, -, hN, hO, -, hON⟩` from `hall.2.2.2.2.2.2.2.2`. Use `⟨cN, hN, ?_⟩` and prove the remaining obligations. Establish `hlen : HasLen v R (OmAA H.AA.carrier) (v (p : C))`.

Use `⟨1, fun _ => (p : R), ⟨?_⟩, by simp⟩` and prove the remaining obligations. Conclude with `(Submodule.quotEquivOfEq _ _ H.cotangent_ker_eq.symm).trans ((LinearMap.quotKerEquivOfSurjective H.φ H.cotangent_surjective).trans (PullbackHopfOrder.qPi p 1))`. Establish `hc : cO = v (p : C)` using `hasLen_unique hs.integers hO hlen`. Establish `hcard : Fintype.card (Nb p 1) = p ^ 2`. Simplify using `[Nb, Ix, ZMod.card]`.

Rewrite using `[← hON, hc, hcard]`.
-/
theorem exists_colen {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} [Algebra R C] [Algebra ℤ_[p] R] {cp : R}
    (hgp : PolarisedAFStatement) (hs : HodgeTateSetting p v R ℤ_[p] AlgEquiv.refl cp)
    (H : HodgeTateDatum p 1 v R ℤ_[p] AlgEquiv.refl cp) :
    ∃ cN, HasColen R v H.AA.carrier cN ∧ cN ^ 2 = v (p : C) ^ (p ^ 2) := by
  have hall := hgp p 1 C v R ℤ_[p] AlgEquiv.refl cp hs H
  dsimp only at hall
  obtain ⟨cA, cN, cO, -, hN, hO, -, hON⟩ := hall.2.2.2.2.2.2.2.2
  refine ⟨cN, hN, ?_⟩
  have hlen : HasLen v R (OmAA H.AA.carrier) (v (p : C)) := by
    refine ⟨1, fun _ => (p : R), ⟨?_⟩, by simp⟩
    exact (Submodule.quotEquivOfEq _ _ H.cotangent_ker_eq.symm).trans
      ((LinearMap.quotKerEquivOfSurjective H.φ H.cotangent_surjective).trans (PullbackHopfOrder.qPi p 1))
  have hc : cO = v (p : C) := hasLen_unique hs.integers hO hlen
  have hcard : Fintype.card (Nb p 1) = p ^ 2 := by
    simp [Nb, Ix, ZMod.card]
  rw [← hON, hc, hcard]

/- English proof (translation)
Substitute `hg` using the available equality. Take `⟨cN, hN, hcN⟩` from `exists_colen hgp hs H`. Establish `hfar : ∃ t : Nb p 1, ∃ f ∈ H.AA.carrier, v (f t - f 0) = 1`. Rewrite using `[hH]`. Conclude with `exists_far hs.integers T hpt hz hk`.

Establish `hcard : Fintype.card (Nb p 1) = p ^ 2`. Simplify using `[Nb, Ix, ZMod.card]`. Establish `hkill : ∀ x : Nb p 1, p • x = 0` using `fun x => by`. Use extensionality with `i`. Simplify using the standard rewrite rules.

Take `⟨e, he⟩` from `GlobalTheory.T.order_p_squared_extremal_colength p C v R hs.integers hlt (Nb p 1) hkill hcard H.AA cN hN hcN hfar`. Use `⟨fun x => pt (e x), isTorsPts_comp hpt e, ?_⟩` and prove the remaining obligations. Rewrite using `[torsFun_comp, ← hH, he]`.
-/
theorem reindex {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} [Algebra R C] [Algebra ℤ_[p] R] {cp : R}
    (hgp : PolarisedAFStatement) (hlt : v (p : C) < 1)
    (hs : HodgeTateSetting p v R ℤ_[p] AlgEquiv.refl cp)
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] (T : TorsRep G p) (g : ℕ) (hg : g = 1)
    (H : HodgeTateDatum p g v R ℤ_[p] AlgEquiv.refl cp) (pt : Nb p g → (sp (R₀ := R) R ⟶ G))
    (hpt : IsTorsPts G p pt) (hH : H.AA.carrier = torsFun C T pt)
    {z : sp (R₀ := R) R ⟶ G} (hz : z ^ p = 1)
    (hk : ∀ (k : Type) [Field k] [Algebra R k], spMap (Algebra.ofId R k) ≫ z ≠ 1) :
    ∃ pt' : ZMod p × ZMod p → (sp (R₀ := R) R ⟶ G), IsTorsPts G p pt' ∧ torsFun C T pt' =
      tens (Submodule.span R (Set.range fun (ψ : AddChar (ZMod p) C) (x : ZMod p) => ψ x))
        (intFun R (ZMod p)) := by
  subst hg
  obtain ⟨cN, hN, hcN⟩ := exists_colen hgp hs H
  have hfar : ∃ t : Nb p 1, ∃ f ∈ H.AA.carrier, v (f t - f 0) = 1 := by
    rw [hH]
    exact exists_far hs.integers T hpt hz hk
  have hcard : Fintype.card (Nb p 1) = p ^ 2 := by
    simp [Nb, Ix, ZMod.card]
  have hkill : ∀ x : Nb p 1, p • x = 0 := fun x => by
    ext i
    simp
  obtain ⟨e, he⟩ := GlobalTheory.T.order_p_squared_extremal_colength p C v R hs.integers hlt (Nb p 1) hkill hcard H.AA cN hN hcN hfar
  refine ⟨fun x => pt (e x), isTorsPts_comp hpt e, ?_⟩
  rw [torsFun_comp, ← hH, he]

end GlobalTheory.CompanionTheory.Ar.GR.OrdCurve

namespace GlobalTheory.CompanionTheory.Ar.GR

/- English proof (translation)
Introduce `hht p _ C _ _ _ v R _ _ hv hlt hc`. Take `⟨f⟩` from `OrdCurve.nonempty_padicInt_hom p R hc`. Use `letI : Algebra ℤ_[p] R := f.toAlgebra`. Take `⟨P, z, hg, hz, hk⟩` from `GlobalTheory.T.polarised_abelian_variety_p_torsion p C v R hv hlt hc`. Take `⟨⟨T⟩, cp, hs, H, pt, hpt, hH⟩` from `hht p C v R hv hlt hc P`.

Take `⟨pt', h1, h2⟩` from `OrdCurve.reindex GlobalTheory.T.polarised_augmentation_theorem hlt hs T P.g hg H pt hpt (hH T) hz hk`. Conclude with `⟨P.A, P.grp, P.L, P.isAb, P.isLB, P.ample, T, pt', h1, h2⟩`.
-/
theorem ordinaryCurve_of_hodgeTate : HodgeTateDatumStatement → OrdinaryCurveStatement := by
  intro hht p _ C _ _ _ v R _ _ hv hlt hc
  obtain ⟨f⟩ := OrdCurve.nonempty_padicInt_hom p R hc
  letI : Algebra ℤ_[p] R := f.toAlgebra
  obtain ⟨P, z, hg, hz, hk⟩ := GlobalTheory.T.polarised_abelian_variety_p_torsion p C v R hv hlt hc
  obtain ⟨⟨T⟩, cp, hs, H, pt, hpt, hH⟩ := hht p C v R hv hlt hc P
  obtain ⟨pt', h1, h2⟩ := OrdCurve.reindex GlobalTheory.T.polarised_augmentation_theorem hlt hs T P.g hg H pt hpt (hH T) hz hk
  exact ⟨P.A, P.grp, P.L, P.isAb, P.isLB, P.ample, T, pt', h1, h2⟩

end GlobalTheory.CompanionTheory.Ar.GR
