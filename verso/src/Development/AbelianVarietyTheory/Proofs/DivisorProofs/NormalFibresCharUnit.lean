import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FibreRing

variable (R A K : Type) [CommRing R] [CommRing A] [CommRing K] [Algebra R A] [Algebra R K]
  (hR : ∀ f g : R →+* A ⊗[ℤ] K, f = g)

def inclK : K →ₐ[R] A ⊗[ℤ] K :=
  { (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := K)).toRingHom with
    commutes' := fun r => by
      have h : ((Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := K)).toRingHom.comp (algebraMap R K)) =
          algebraMap R (A ⊗[ℤ] K) :=
        hR _ _
      exact RingHom.congr_fun h r }

def toR : A ⊗[ℤ] K →+* A ⊗[R] K :=
  (Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := K)).toIntAlgHom
    (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := K)).toRingHom.toIntAlgHom
    (fun _ _ => Commute.all _ _)).toRingHom

def ofR : A ⊗[R] K →+* A ⊗[ℤ] K :=
  (Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft (R := ℤ) (S := R) (A := A) (B := K))
    (inclK R A K hR) (fun _ _ => Commute.all _ _)).toRingHom

/- English proof (translation)
Simplify using `[toR, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.tmul_mul_tmul]`.
-/
lemma toR_tmul (a : A) (k : K) : toR R A K (a ⊗ₜ[ℤ] k) = a ⊗ₜ[R] k := by
  simp [toR, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.tmul_mul_tmul]

/- English proof (translation)
Simplify using `[ofR, inclK, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.tmul_mul_tmul]`.
-/
lemma ofR_tmul (a : A) (k : K) : ofR R A K hR (a ⊗ₜ[R] k) = a ⊗ₜ[ℤ] k := by
  simp [ofR, inclK, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.tmul_mul_tmul]

def tensorIntEquiv : A ⊗[ℤ] K ≃+* A ⊗[R] K :=
  RingEquiv.ofRingHom (toR R A K) (ofR R A K hR)
    (by
      refine RingHom.ext fun x => ?_
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a k => simp [ofR_tmul, toR_tmul]
      | add x y hx hy => simp only [map_add, RingHom.comp_apply, RingHom.id_apply] at hx hy ⊢; rw [hx, hy])
    (by
      refine RingHom.ext fun x => ?_
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a k => simp [ofR_tmul, toR_tmul]
      | add x y hx hy => simp only [map_add, RingHom.comp_apply, RingHom.id_apply] at hx hy ⊢; rw [hx, hy])

/- English proof (translation)
The claim follows from `toR_tmul R A K a k`.
-/
lemma tensorIntEquiv_tmul (a : A) (k : K) : tensorIntEquiv R A K hR (a ⊗ₜ[ℤ] k) = a ⊗ₜ[R] k := toR_tmul R A K a k

end GlobalTheory.FibreRing

namespace GlobalTheory.RealMult

/- English proof (translation)
Introduce `N M s V hnorm hcodim K _ hNK W hW`. Establish `hu : IsUnit (Int.castRingHom K (N : ℤ))`. Rewrite using `[isUnit_iff_ne_zero]`. Simplify using `using hNK`. Set `φ : Localization.Away (N : ℤ) →+* K` to `IsLocalization.Away.lift (N : ℤ) hu`.

Use `letI : Algebra (Localization.Away (N : ℤ)) K := φ.toAlgebra`. Set `t : Sp K ⟶ Sp (Localization.Away (N : ℤ))` to `spMap φ`. Establish `H : IsPullback (pullback.fst s t) (pullback.snd s t) s (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away (N : ℤ)) K)))` using `IsPullback.of_hasPullback s t`. Use `letI : Algebra (Localization.Away (N : ℤ)) Γ(M, W) := (DVR.FlatBC.algX s W).toAlgebra`. Set `U'` to `pullback.fst s t ⁻¹ᵁ W ⊓ pullback.snd s t ⁻¹ᵁ ⊤`.

Set `E : Γ(M, W) ⊗[ℤ] K ≃+* Γ(pullback s t, U')` to `(GlobalTheory.FibreRing.tensorIntEquiv (Localization.Away (N : ℤ)) Γ(M, W) K (fun f g => IsLocalization.ringHom_ext (Submonoid.powers (N : ℤ)) (RingHom.ext_int _ _))).trans (DVR.FlatBC.eTens s (pullback.snd s t) (pullback.fst s t) H W hW)`. Establish `hE : ∀ a, E (a ⊗ₜ[ℤ] 1) = ((pullback.fst s t).appLE W U' inf_le_left).hom a`. Introduce `a`. Simplify using `only [E, RingEquiv.trans_apply, GlobalTheory.FibreRing.tensorIntEquiv_tmul]`. Use `erw [DVR.FlatBC.eTens_tmul]`.

Rewrite using `[map_one, _root_.mul_one]`. Establish `hU' : IsAffineOpen U'`. Establish `e : U' = pullback.fst s t ⁻¹ᵁ W` using `by simp [U']`. Rewrite using `[e]`. Use `haveI : IsAffineHom (pullback.fst s t) := MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback s t).flip inferInstance`.

Conclude with `hW.preimage _`. Establish `hst` using `hnorm K t`. Use `haveI : ∀ y : ↥(pullback s t), _root_.IsReduced ((pullback s t).presheaf.stalk y) := fun y => by haveI := (hst y).1; infer_instance`. Use `haveI : IsReduced (pullback s t) := isReduced_of_isReduced_stalk _`. Use `⟨isReduced_of_injective E.toRingHom E.injective, ?_⟩` and prove the remaining obligations.

Introduce `q hq`. Use `haveI : q.IsPrime := hq.1.1`. Set `q' : Ideal Γ(pullback s t, U')` to `q.comap E.symm.toRingHom`. Use `haveI hq'p : q'.IsPrime := Ideal.comap_isPrime _ _`. Establish `hq' : q' ∈ minimalPrimes Γ(pullback s t, U')`.

Use `⟨⟨hq'p, bot_le⟩, fun p hp hle => ?_⟩` and prove the remaining obligations. Use `haveI : p.IsPrime := hp.1`. Establish `h1 : p.comap E.toRingHom ≤ q`. Introduce `x hx`. Use `hle hx` as an intermediate fact.

Simplify `this` using `[q']`. Establish `h2` using `hq.2 ⟨Ideal.comap_isPrime _ _, bot_le⟩ h1`. Introduce `x hx`. Establish `h3 : E.symm x ∈ p.comap E.toRingHom` using `h2 hx`. Rewrite `h3` using `[Ideal.mem_comap]`.

Simplify using `using h3`. Set `y' : PrimeSpectrum Γ(pullback s t, U')` to `⟨q', hq'p⟩`. Establish `hmem : hU'.fromSpec y' ∈ U'`. Establish `h` using `hU'.range_fromSpec`. Use `show hU'.fromSpec y' ∈ (U' : Set ↥(pullback s t))`.

Rewrite using `[← h]`. Conclude with `⟨y', rfl⟩`. Use `letI algSt : Algebra Γ(pullback s t, U') ((pullback s t).presheaf.stalk (hU'.fromSpec y')) := TopCat.Presheaf.algebra_section_stalk (pullback s t).presheaf ⟨hU'.fromSpec y', hmem⟩`. Establish `hst'` using `hU'.isLocalization_stalk' y' hmem`. Establish `hd` using `@IsLocalization.AtPrime.ringKrullDim_eq_height _ _ q' _ ((pullback s t).presheaf.stalk (hU'.fromSpec y')) _ algSt hst'`.

Establish `hdim : ringKrullDim ((pullback s t).presheaf.stalk (hU'.fromSpec y')) = 0`. Rewrite using `[hd, Ideal.height_eq_zero_iff.mpr hq']`. Both sides reduce to the same expression. Establish `hV : pullback.fst s t (hU'.fromSpec y') ∈ V`. Assume the negation of the conclusion as `hn`.

Use `hcodim K t _ hn` as an intermediate fact. Rewrite `this` using `[hdim]`. Conclude with `absurd this (by decide)`. Establish `e` using `IsAffineOpen.SpecMap_appLE_fromSpec (pullback.fst s t) hW hU' inf_le_left`. Establish `hpt : pullback.fst s t (hU'.fromSpec y') = hW.fromSpec (PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom (R` using `ℤ) (A := Γ(M, W)) (B := K)) ⟨q, hq.1.1⟩) := by`.

Express the relevant statement in the definitionally equal form `(hU'.fromSpec ≫ pullback.fst s t) y' = _`. Rewrite using `[← e]`. Express the relevant statement in the definitionally equal form `hW.fromSpec ((Spec.map ((pullback.fst s t).appLE W U' inf_le_left)) y') = _`. Use `congr 1`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises.

Use extensionality with `x`. Use `show x ∈ Ideal.comap ((pullback.fst s t).appLE W U' inf_le_left).hom q' ↔ _`. Simplify using `only [Ideal.mem_comap, q', PrimeSpectrum.comap_asIdeal]`. Rewrite using `[← hE]`. Simplify using the standard rewrite rules.

Rewrite using `[← hpt]`. Conclude with `hV`.
-/
theorem fibre_tensor_reduced_minimalPrimes : ∀ (N : ℕ) (M : Scheme.{0}) (s : M ⟶ Sp (Localization.Away (N : ℤ))) (V : M.Opens),
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))), Geo.Tor.IsNormalScheme (pullback s t)) →
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))) (y : ↥(pullback s t)),
      pullback.fst s t y ∉ V → 2 ≤ ringKrullDim ((pullback s t).presheaf.stalk y)) →
    ∀ (K : Type) [Field K], (N : K) ≠ 0 → ∀ (W : M.Opens) (hW : IsAffineOpen W),
      IsReduced (Γ(M, W) ⊗[ℤ] K) ∧ ∀ q (hq : q ∈ minimalPrimes (Γ(M, W) ⊗[ℤ] K)),
        hW.fromSpec (PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := Γ(M, W)) (B := K)) ⟨q, hq.1.1⟩) ∈ V := by
  intro N M s V hnorm hcodim K _ hNK W hW
  classical
  have hu : IsUnit (Int.castRingHom K (N : ℤ)) := by
    rw [isUnit_iff_ne_zero]; simpa using hNK
  let φ : Localization.Away (N : ℤ) →+* K := IsLocalization.Away.lift (N : ℤ) hu
  letI : Algebra (Localization.Away (N : ℤ)) K := φ.toAlgebra
  let t : Sp K ⟶ Sp (Localization.Away (N : ℤ)) := spMap φ
  have H : IsPullback (pullback.fst s t) (pullback.snd s t) s
      (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away (N : ℤ)) K))) :=
    IsPullback.of_hasPullback s t
  letI : Algebra (Localization.Away (N : ℤ)) Γ(M, W) := (DVR.FlatBC.algX s W).toAlgebra
  let U' := pullback.fst s t ⁻¹ᵁ W ⊓ pullback.snd s t ⁻¹ᵁ ⊤
  let E : Γ(M, W) ⊗[ℤ] K ≃+* Γ(pullback s t, U') :=
    (GlobalTheory.FibreRing.tensorIntEquiv (Localization.Away (N : ℤ)) Γ(M, W) K
      (fun f g => IsLocalization.ringHom_ext (Submonoid.powers (N : ℤ)) (RingHom.ext_int _ _))).trans
      (DVR.FlatBC.eTens s (pullback.snd s t) (pullback.fst s t) H W hW)
  have hE : ∀ a, E (a ⊗ₜ[ℤ] 1) = ((pullback.fst s t).appLE W U' inf_le_left).hom a := by
    intro a
    simp only [E, RingEquiv.trans_apply, GlobalTheory.FibreRing.tensorIntEquiv_tmul]
    erw [DVR.FlatBC.eTens_tmul]
    rw [map_one, _root_.mul_one]
  have hU' : IsAffineOpen U' := by
    have e : U' = pullback.fst s t ⁻¹ᵁ W := by simp [U']
    rw [e]
    haveI : IsAffineHom (pullback.fst s t) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback s t).flip inferInstance
    exact hW.preimage _
  have hst := hnorm K t
  haveI : ∀ y : ↥(pullback s t), _root_.IsReduced ((pullback s t).presheaf.stalk y) := fun y => by
    haveI := (hst y).1; infer_instance
  haveI : IsReduced (pullback s t) := isReduced_of_isReduced_stalk _
  refine ⟨isReduced_of_injective E.toRingHom E.injective, ?_⟩
  intro q hq
  haveI : q.IsPrime := hq.1.1
  let q' : Ideal Γ(pullback s t, U') := q.comap E.symm.toRingHom
  haveI hq'p : q'.IsPrime := Ideal.comap_isPrime _ _
  have hq' : q' ∈ minimalPrimes Γ(pullback s t, U') := by
    refine ⟨⟨hq'p, bot_le⟩, fun p hp hle => ?_⟩
    haveI : p.IsPrime := hp.1
    have h1 : p.comap E.toRingHom ≤ q := by
      intro x hx
      have := hle hx
      simpa [q'] using this
    have h2 := hq.2 ⟨Ideal.comap_isPrime _ _, bot_le⟩ h1
    intro x hx
    have h3 : E.symm x ∈ p.comap E.toRingHom := h2 hx
    rw [Ideal.mem_comap] at h3
    simpa using h3
  let y' : PrimeSpectrum Γ(pullback s t, U') := ⟨q', hq'p⟩
  have hmem : hU'.fromSpec y' ∈ U' := by
    have h := hU'.range_fromSpec
    show hU'.fromSpec y' ∈ (U' : Set ↥(pullback s t))
    rw [← h]; exact ⟨y', rfl⟩
  letI algSt : Algebra Γ(pullback s t, U') ((pullback s t).presheaf.stalk (hU'.fromSpec y')) :=
    TopCat.Presheaf.algebra_section_stalk (pullback s t).presheaf ⟨hU'.fromSpec y', hmem⟩
  have hst' := hU'.isLocalization_stalk' y' hmem
  have hd := @IsLocalization.AtPrime.ringKrullDim_eq_height _ _ q' _
    ((pullback s t).presheaf.stalk (hU'.fromSpec y')) _ algSt hst'
  have hdim : ringKrullDim ((pullback s t).presheaf.stalk (hU'.fromSpec y')) = 0 := by
    rw [hd,
      Ideal.height_eq_zero_iff.mpr hq']
    rfl
  have hV : pullback.fst s t (hU'.fromSpec y') ∈ V := by
    by_contra hn
    have := hcodim K t _ hn
    rw [hdim] at this
    exact absurd this (by decide)
  have e := IsAffineOpen.SpecMap_appLE_fromSpec (pullback.fst s t) hW hU' inf_le_left
  have hpt : pullback.fst s t (hU'.fromSpec y') =
      hW.fromSpec (PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := Γ(M, W)) (B := K))
        ⟨q, hq.1.1⟩) := by
    change (hU'.fromSpec ≫ pullback.fst s t) y' = _
    rw [← e]
    change hW.fromSpec ((Spec.map ((pullback.fst s t).appLE W U' inf_le_left)) y') = _
    congr 1
    apply PrimeSpectrum.ext
    ext x
    show x ∈ Ideal.comap ((pullback.fst s t).appLE W U' inf_le_left).hom q' ↔ _
    simp only [Ideal.mem_comap, q', PrimeSpectrum.comap_asIdeal]
    rw [← hE]
    simp
  rw [← hpt]; exact hV

end GlobalTheory.RealMult
