import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyUnitaryTorusOrbitalClassTrivialLocalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianIsometryBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormClassesIffConjUnitaryTorusEllipticElementsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalNormClassesEqLocalUnramifiedCMStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTorusClassOfIrreducibleCharpolyUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TorusElementCharpolyRegularCentralizerStatement

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TrEll.RatClasses

section General

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r n : ℕ} {P : PPol σ r}
  {J : Matrix (Fin n) (Fin n) E} {k k' : Type} [CommRing k] [Algebra F k] [CommRing k'] [Algebra F k']

/- English proof (translation)
Take `⟨x, x', hx, rfl, ex⟩` from `ha`. Take `⟨y, y', hy, rfl, ey⟩` from `hb`. Take `⟨c, hc⟩` from `Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 (hx.trans hy.symm))`. Set `m` to `Algebra.TensorProduct.map ψ (AlgHom.id F (Fld P))`. Establish `hm : ∀ z, sigR k' (star' P) (m z) = m (sigR k (star' P) z)` using `fun z => by`.

Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => simp [m, sigR]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Use `QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ⟨Units.map m.toMonoidHom c, ?_⟩)` and prove the remaining obligations.

Establish `hc' : x.1.1 * (c.1 * sigR k (star' P) c.1) = y.1.1`. Establish `: c.1 * sigR k (star' P) c.1 = (x.1⁻¹ * y.1).1` using `congrArg Units.val hc`. Rewrite using `[this, Units.val_mul, Units.mul_inv_cancel_left]`. Express the relevant statement in the definitionally equal form `_ = x'.1⁻¹ * y'.1`. Rewrite using `[eq_inv_mul_iff_mul_eq]`.

Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `x'.1.1 * (m c.1 * sigR k' (star' P) (m c.1)) = y'.1.1`. Rewrite using `[ex, ey, hm, ← hc', map_mul, map_mul]`.
-/
theorem mapsCls_unique {ψ : k →ₐ[F] k'} {q : Cls P k} {a b : Cls P k'} (ha : MapsCls P ψ q a)
    (hb : MapsCls P ψ q b) : a = b := by
  obtain ⟨x, x', hx, rfl, ex⟩ := ha
  obtain ⟨y, y', hy, rfl, ey⟩ := hb
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 (hx.trans hy.symm))
  let m := Algebra.TensorProduct.map ψ (AlgHom.id F (Fld P))
  have hm : ∀ z, sigR k' (star' P) (m z) = m (sigR k (star' P) z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [m, sigR]
    | add x y hx hy => simp only [map_add, hx, hy]
  refine QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ⟨Units.map m.toMonoidHom c, ?_⟩)
  have hc' : x.1.1 * (c.1 * sigR k (star' P) c.1) = y.1.1 := by
    have : c.1 * sigR k (star' P) c.1 = (x.1⁻¹ * y.1).1 := congrArg Units.val hc
    rw [this, Units.val_mul, Units.mul_inv_cancel_left]
  change _ = x'.1⁻¹ * y'.1
  rw [eq_inv_mul_iff_mul_eq]
  apply Units.ext
  change x'.1.1 * (m c.1 * sigR k' (star' P) (m c.1)) = y'.1.1
  rw [ex, ey, hm, ← hc', map_mul, map_mul]

/- English proof (translation)
The claim follows from `Subtype.ext (Units.ext (Matrix.ext fun r s => by change Algebra.TensorProduct.map ψ (AlgHom.id F E) ((1 : k) ⊗ₜ[F] (γ.1.1 r s)) = (1 : k') ⊗ₜ[F] (γ.1.1 r s) simp))`.
-/
theorem mapH_diagH (ψ : k →ₐ[F] k') (γ : Formalism.UG.UJ (σ : E →+* E) J) :
    mapH σ J ψ (diagH σ J k γ) = diagH σ J k' γ :=
  Subtype.ext (Units.ext (Matrix.ext fun r s => by
    change Algebra.TensorProduct.map ψ (AlgHom.id F E) ((1 : k) ⊗ₜ[F] (γ.1.1 r s)) = (1 : k') ⊗ₜ[F] (γ.1.1 r s)
    simp))

variable [NumberField F] [NumberField E] (hc : IsCMExt F E σ) (hJ : IsHermND σ J)
include hc hJ

/- English proof (translation)
Take `⟨x, φ, h, rfl, e⟩` from `h`. Take `⟨x', φ', h', rfl, e'⟩` from `h'`. Conclude with `(GlobalTheory.T.normClasses_iff_conj_unitaryTorusEllipticElements F E σ hc r n P J hJ k x φ h x' φ' h').2.1 (by rw [e, e'])`.
-/
theorem hasCls_unique {γ : HA k σ J} {q q' : Cls P k} (h : HasCls P k J γ q) (h' : HasCls P k J γ q') : q = q' := by
  obtain ⟨x, φ, h, rfl, e⟩ := h
  obtain ⟨x', φ', h', rfl, e'⟩ := h'
  exact (GlobalTheory.T.normClasses_iff_conj_unitaryTorusEllipticElements F E σ hc r n P J hJ k x φ h x' φ' h').2.1 (by rw [e, e'])

/- English proof (translation)
Take `⟨x, φ, h, rfl, rfl⟩` from `h`. Take `⟨g, rfl⟩` from `isConj_iff.1 e`. Conclude with `(GlobalTheory.T.normClasses_iff_conj_unitaryTorusEllipticElements F E σ hc r n P J hJ k x φ h x φ h).2.2.2 g`.
-/
theorem hasCls_of_isConj {γ γ' : HA k σ J} {q : Cls P k} (h : HasCls P k J γ q) (e : IsConj γ γ') :
    HasCls P k J γ' q := by
  obtain ⟨x, φ, h, rfl, rfl⟩ := h
  obtain ⟨g, rfl⟩ := isConj_iff.1 e
  exact (GlobalTheory.T.normClasses_iff_conj_unitaryTorusEllipticElements F E σ hc r n P J hJ k x φ h x φ h).2.2.2 g

/- English proof (translation)
Take `⟨x, φ, h, e, rfl⟩` from `h`. Take `⟨x', φ', h', e', rfl⟩` from `h'`. Take `⟨g, hg⟩` from `(GlobalTheory.T.normClasses_iff_conj_unitaryTorusEllipticElements F E σ hc r n P J hJ k x φ h x' φ' h').1 (e.trans e'.symm)`. Conclude with `isConj_iff.2 ⟨g, (hg _).symm⟩`.
-/
theorem isConj_of_hasCls {γ γ' : HA k σ J} {q : Cls P k} (h : HasCls P k J γ q) (h' : HasCls P k J γ' q) :
    IsConj γ γ' := by
  obtain ⟨x, φ, h, e, rfl⟩ := h
  obtain ⟨x', φ', h', e', rfl⟩ := h'
  obtain ⟨g, hg⟩ := (GlobalTheory.T.normClasses_iff_conj_unitaryTorusEllipticElements F E σ hc r n P J hJ k x φ h x' φ' h').1 (e.trans e'.symm)
  exact isConj_iff.2 ⟨g, (hg _).symm⟩

/- English proof (translation)
Take `⟨x, φ, h, rfl, rfl⟩` from `h`. Take `⟨x', φ', h', e1, e2, -⟩` from `GlobalTheory.T.hermitian_isometry_base_change F E σ hc r n P J hJ k k' ψ x φ h`. Conclude with `⟨_, ⟨x, x', rfl, rfl, e1⟩, x', φ', h', rfl, e2⟩`.
-/
theorem exists_mapsCls (ψ : k →ₐ[F] k') {γ : HA k σ J} {q : Cls P k} (h : HasCls P k J γ q) :
    ∃ q', MapsCls P ψ q q' ∧ HasCls P k' J (mapH σ J ψ γ) q' := by
  obtain ⟨x, φ, h, rfl, rfl⟩ := h
  obtain ⟨x', φ', h', e1, e2, -⟩ := GlobalTheory.T.hermitian_isometry_base_change F E σ hc r n P J hJ k k' ψ x φ h
  exact ⟨_, ⟨x, x', rfl, rfl, e1⟩, x', φ', h', rfl, e2⟩

/- English proof (translation)
Simplify `exists_mapsCls hc hJ (Algebra.ofId F k) h` using `only [mapH_diagH]`.
-/
theorem exists_mapsCls_rat (k : Type) [CommRing k] [Algebra F k] {γ : GRat σ J} {q : Cls P F}
    (h : HasCls P F J (diagH σ J F γ) q) :
    ∃ q', MapsCls P (k := F) (Algebra.ofId F k) q q' ∧ HasCls P k J (diagH σ J k γ) q' := by
  simpa only [mapH_diagH] using exists_mapsCls hc hJ (Algebra.ofId F k) h

/- English proof (translation)
Take `⟨P', e, hq⟩` from `(GlobalTheory.T.exists_torusClass_of_irreducible_charpoly_unitary F E σ hc n J hJ).2 γ (h ▸ P.2.2.1)`. Take `rfl : P' = P` from `Subtype.ext (e.symm.trans h)`. Conclude with `hq`.
-/
theorem exists_hasCls_rat {P : PPol σ n} (γ : GRat σ J) (h : γ.1.1.charpoly = P.1) :
    ∃ q, HasCls P F J (diagH σ J F γ) q := by
  obtain ⟨P', e, hq⟩ := (GlobalTheory.T.exists_torusClass_of_irreducible_charpoly_unitary F E σ hc n J hJ).2 γ (h ▸ P.2.2.1)
  obtain rfl : P' = P := Subtype.ext (e.symm.trans h)
  exact hq

/- English proof (translation)
Take `⟨x, φ, h, -, e⟩` from `h`. Establish `h1` using `(GlobalTheory.T.torusElement_charpoly_regular_centralizer F E σ hc r n P J hJ F x φ h).1`. Rewrite `h1` using `[e]`. Apply `Polynomial.map_injective (inclR (F := F) (E := E) F) (inclR (F := F) (E := E) F).injective` to reduce the goal to its premises. Rewrite using `[← h1, ← Matrix.charpoly_map]`.

Both sides reduce to the same expression.
-/
theorem charpoly_of_hasCls {γ : GRat σ J} {q : Cls P F} (h : HasCls P F J (diagH σ J F γ) q) :
    γ.1.1.charpoly = P.1 := by
  obtain ⟨x, φ, h, -, e⟩ := h
  have h1 := (GlobalTheory.T.torusElement_charpoly_regular_centralizer F E σ hc r n P J hJ F x φ h).1
  rw [e] at h1
  apply Polynomial.map_injective (inclR (F := F) (E := E) F) (inclR (F := F) (E := E) F).injective
  rw [← h1, ← Matrix.charpoly_map]
  rfl

/- English proof (translation)
Establish `hb` using `(GlobalTheory.T.exists_torusClass_of_irreducible_charpoly_unitary F E σ hc n J hJ).1`. Take `⟨g, e⟩` from `isConj_iff.1 h`. Take `⟨g, rfl⟩` from `hb.2 g`. Conclude with `isConj_iff.2 ⟨g, hb.1 (by simpa only [map_mul, map_inv] using e)⟩`.
-/
theorem isConj_of_diagH {γ γ' : GRat σ J} (h : IsConj (diagH σ J F γ) (diagH σ J F γ')) : IsConj γ γ' := by
  have hb := (GlobalTheory.T.exists_torusClass_of_irreducible_charpoly_unitary F E σ hc n J hJ).1
  obtain ⟨g, e⟩ := isConj_iff.1 h
  obtain ⟨g, rfl⟩ := hb.2 g
  exact isConj_iff.2 ⟨g, hb.1 (by simpa only [map_mul, map_inv] using e)⟩

/- English proof (translation)
Take `⟨q, hq⟩` from `exists_hasCls_rat hc hJ γ h`. Take `⟨q', -, hq'⟩` from `exists_mapsCls_rat hc hJ k hq`. Conclude with `⟨q', hq', fun _ h => hasCls_unique hc hJ h hq'⟩`.
-/
theorem existsUnique_hasCls_rat {P : PPol σ n} (k : Type) [CommRing k] [Algebra F k] (γ : GRat σ J)
    (h : γ.1.1.charpoly = P.1) : ∃! q, HasCls P k J (diagH σ J k γ) q := by
  obtain ⟨q, hq⟩ := exists_hasCls_rat hc hJ γ h
  obtain ⟨q', -, hq'⟩ := exists_mapsCls_rat hc hJ k hq
  exact ⟨q', hq', fun _ h => hasCls_unique hc hJ h hq'⟩

/- English proof (translation)
Take `⟨a, h1, h2⟩` from `exists_mapsCls_rat hc hJ k h`. Take `⟨b, h3, h4⟩` from `exists_mapsCls_rat hc hJ k h'`. Conclude with `⟨a, h1, hasCls_unique hc hJ h4 (H a h2) ▸ h3⟩`.
-/
theorem exists_common {γ γ' : GRat σ J} {q q' : Cls P F} (h : HasCls P F J (diagH σ J F γ) q)
    (h' : HasCls P F J (diagH σ J F γ') q')
    (H : ∀ a, HasCls P k J (diagH σ J k γ) a → HasCls P k J (diagH σ J k γ') a) :
    ∃ a, MapsCls P (k := F) (Algebra.ofId F k) q a ∧ MapsCls P (k := F) (Algebra.ofId F k) q' a := by
  obtain ⟨a, h1, h2⟩ := exists_mapsCls_rat hc hJ k h
  obtain ⟨b, h3, h4⟩ := exists_mapsCls_rat hc hJ k h'
  exact ⟨a, h1, hasCls_unique hc hJ h4 (H a h2) ▸ h3⟩

/- English proof (translation)
Take `⟨b, h1, h2⟩` from `exists_mapsCls_rat hc hJ k h`. Conclude with `mapsCls_unique h1 H ▸ h2`.
-/
theorem hasCls_of_mapsCls {γ : GRat σ J} {q : Cls P F} (h : HasCls P F J (diagH σ J F γ) q) {a : Cls P k}
    (H : MapsCls P (k := F) (Algebra.ofId F k) q a) : HasCls P k J (diagH σ J k γ) a := by
  obtain ⟨b, h1, h2⟩ := exists_mapsCls_rat hc hJ k h
  exact mapsCls_unique h1 H ▸ h2

end General

/- English proof (translation)
Establish `e1 : ∀ v γ, proj σ J v (ratEmb σ J γ) = diagH σ J (Fv F v) γ` using `proj_ratEmb σ J`. Establish `e2 : ∀ w γ, projArch σ J w (ratEmb σ J γ) = diagH σ J w.Completion γ` using `projArch_ratEmb σ J`. Take `⟨H1, H2⟩` from `GlobalTheory.T.rationalNormClasses_eq_local_unramifiedCM E F σ hc hu r P J hJ`. Use `⟨fun γ h => ⟨fun v => ?_, fun w => ?_, ?_⟩, fun γ γ' h h' => ⟨fun e => ⟨fun v q hq => ?_, fun w q hq => ?_⟩, fun H => ?_⟩, fun qf qa hf ha h1 => ?_⟩` and prove the remaining obligations. Rewrite using `[e1]`.

Conclude with `existsUnique_hasCls_rat hc hJ _ γ h`. Rewrite using `[e2]`. Conclude with `existsUnique_hasCls_rat hc hJ _ γ h`. Use `isLattice_stdLattice (E := E) (n := r) filter_upwards [GlobalTheory.T.eventually_unitaryTorus_orbitalClass_trivial_local F E σ hc r P J hJ (stdLattice E r), eventually_proj_mem_stabLoc σ J (stdLattice E r) (ratEmb σ J γ)] with v hv hm` as an intermediate fact. Take `⟨q, hq, -⟩` from `existsUnique_hasCls_rat hc hJ (Fv F v) γ h`.

Rewrite `hq` using `[← e1]`. Conclude with `hv.2.1 _ q hq ⟨1, by simpa only [inv_one, one_mul, mul_one] using hm⟩ ▸ hq`. Conclude with `hasCls_of_isConj hc hJ hq ((proj σ J v).map_isConj ((ratEmb σ J).map_isConj e))`. Conclude with `hasCls_of_isConj hc hJ hq ((projArch σ J w).map_isConj ((ratEmb σ J).map_isConj e))`. Simplify using `only [e1, e2] at H`.

Take `⟨q, hq⟩` from `exists_hasCls_rat hc hJ γ h`. Take `⟨q', hq'⟩` from `exists_hasCls_rat hc hJ γ' h'`. Take `rfl : q = q'` from `H1 q q' (hq.mem P) (hq'.mem P) (fun v => exists_common hc hJ hq hq' (H.1 v)) fun w => exists_common hc hJ hq hq' (H.2 w)`. Conclude with `isConj_of_diagH hc hJ (isConj_of_hasCls hc hJ hq hq')`. Take `⟨q, hq, h2, h3⟩` from `H2 qf qa hf ha h1`.

Take `⟨g, hg⟩` from `exists_hasCls P hq`. Take `⟨γ, rfl⟩` from `(GlobalTheory.T.exists_torusClass_of_irreducible_charpoly_unitary F E σ hc r J hJ).1.2 g`. Use `⟨γ, charpoly_of_hasCls hc hJ hg, fun v => ?_, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[e1]`. Conclude with `hasCls_of_mapsCls hc hJ hg (h2 v)`.

Rewrite using `[e2]`. Conclude with `hasCls_of_mapsCls hc hJ hg (h3 w)`.
-/
theorem rat_classes_iff_local (E : Type) [Field E] [NumberField E] (F : Subfield E) [NumberField F] (σ : E →ₐ[F] E)
    (hc : IsCMExt F E σ) (hu : Algebra.Unramified (𝓞 F) (𝓞 E)) (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E)
    (hJ : IsHermND σ J) :
    (∀ γ : GRat σ J, γ.1.1.charpoly = P.1 → (∀ v, ∃! q, HasCls P _ J (proj σ J v (ratEmb σ J γ)) q) ∧
      (∀ w, ∃! q, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) q) ∧
      ∀ᶠ v in cofinite, HasCls P _ J (proj σ J v (ratEmb σ J γ)) 1) ∧
    (∀ γ γ' : GRat σ J, γ.1.1.charpoly = P.1 → γ'.1.1.charpoly = P.1 → (IsConj γ γ' ↔
      (∀ v q, HasCls P _ J (proj σ J v (ratEmb σ J γ)) q → HasCls P _ J (proj σ J v (ratEmb σ J γ')) q) ∧
        ∀ w q, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) q → HasCls P _ J (projArch σ J w (ratEmb σ J γ')) q)) ∧
    ∀ (qf : ∀ v : HeightOneSpectrum (𝓞 F), Cls P (Fv F v)) (qa : ∀ w : InfinitePlace F, Cls P w.Completion),
      (∀ v, qf v ∈ XSet P _ J) → (∀ w, qa w ∈ XSet P _ J) → (∀ᶠ v in cofinite, qf v = 1) →
      ∃ γ : GRat σ J, γ.1.1.charpoly = P.1 ∧ (∀ v, HasCls P _ J (proj σ J v (ratEmb σ J γ)) (qf v)) ∧
        ∀ w, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) (qa w) := by
  have e1 : ∀ v γ, proj σ J v (ratEmb σ J γ) = diagH σ J (Fv F v) γ := proj_ratEmb σ J
  have e2 : ∀ w γ, projArch σ J w (ratEmb σ J γ) = diagH σ J w.Completion γ := projArch_ratEmb σ J
  obtain ⟨H1, H2⟩ := GlobalTheory.T.rationalNormClasses_eq_local_unramifiedCM E F σ hc hu r P J hJ
  refine ⟨fun γ h => ⟨fun v => ?_, fun w => ?_, ?_⟩, fun γ γ' h h' => ⟨fun e => ⟨fun v q hq => ?_, fun w q hq => ?_⟩,
    fun H => ?_⟩, fun qf qa hf ha h1 => ?_⟩
  · rw [e1]; exact existsUnique_hasCls_rat hc hJ _ γ h
  · rw [e2]; exact existsUnique_hasCls_rat hc hJ _ γ h
  · have := isLattice_stdLattice (E := E) (n := r)
    filter_upwards [GlobalTheory.T.eventually_unitaryTorus_orbitalClass_trivial_local F E σ hc r P J hJ (stdLattice E r),
      eventually_proj_mem_stabLoc σ J (stdLattice E r) (ratEmb σ J γ)] with v hv hm
    obtain ⟨q, hq, -⟩ := existsUnique_hasCls_rat hc hJ (Fv F v) γ h
    rw [← e1] at hq
    exact hv.2.1 _ q hq ⟨1, by simpa only [inv_one, one_mul, mul_one] using hm⟩ ▸ hq
  · exact hasCls_of_isConj hc hJ hq ((proj σ J v).map_isConj ((ratEmb σ J).map_isConj e))
  · exact hasCls_of_isConj hc hJ hq ((projArch σ J w).map_isConj ((ratEmb σ J).map_isConj e))
  · simp only [e1, e2] at H
    obtain ⟨q, hq⟩ := exists_hasCls_rat hc hJ γ h
    obtain ⟨q', hq'⟩ := exists_hasCls_rat hc hJ γ' h'
    obtain rfl : q = q' := H1 q q' (hq.mem P) (hq'.mem P) (fun v => exists_common hc hJ hq hq' (H.1 v))
      fun w => exists_common hc hJ hq hq' (H.2 w)
    exact isConj_of_diagH hc hJ (isConj_of_hasCls hc hJ hq hq')
  · obtain ⟨q, hq, h2, h3⟩ := H2 qf qa hf ha h1
    obtain ⟨g, hg⟩ := exists_hasCls P hq
    obtain ⟨γ, rfl⟩ := (GlobalTheory.T.exists_torusClass_of_irreducible_charpoly_unitary F E σ hc r J hJ).1.2 g
    refine ⟨γ, charpoly_of_hasCls hc hJ hg, fun v => ?_, fun w => ?_⟩
    · rw [e1]; exact hasCls_of_mapsCls hc hJ hg (h2 v)
    · rw [e2]; exact hasCls_of_mapsCls hc hJ hg (h3 w)

end GlobalTheory.TrEll.RatClasses
