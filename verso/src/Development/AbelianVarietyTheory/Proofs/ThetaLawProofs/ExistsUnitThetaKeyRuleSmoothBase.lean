import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ValueAtNormalForm
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.StalkOfAppLEEq
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeySmoothBase

section Tangent

/- English proof (translation)
Set `pt : (𝟙_ (Over (Sp ℂ))).left` to `(default : PrimeSpectrum ℂ)`. Establish `hsub : ∀ q : (𝟙_ (Over (Sp ℂ))).left, q = pt` using `fun q => Subsingleton.elim (α := PrimeSpectrum ℂ) q pt`. Take `⟨U, hU, hx, -⟩` from `exists_isAffineOpen_mem_and_subset (X := A.left) (x := (u.ex 0).left pt) (U := ⊤) trivial`. Establish `h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U`. Introduce `q _`.

Rewrite using `[hsub q]`. Conclude with `hx`. Establish `h₁` using `(GlobalTheory.TangentOrigin.tangent_mem_iff (u := u) hv U).2 h0`. Establish `h₂` using `(GlobalTheory.TangentOrigin.tangent_mem_iff (u := u) hv' U).2 h0`. Rewrite `h` using `[GlobalTheory.TangentOrigin.isDiff_iff hv hU h₁ h0]`.

Rewrite `h'` using `[GlobalTheory.TangentOrigin.isDiff_iff hv' hU h₂ h0]`. Conclude with `Over.OverMorphism.ext (GlobalTheory.TangentOrigin.ext_evalPt hU h₁ h₂ (h.trans h'.symm))`.
-/
theorem eq_of_isDiff {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) {w : Fin g → ℂ}
    {v v' : epsR ℂ ⟶ A} (hv : IsTangent v) (hv' : IsTangent v') (h : u.IsDiff w v) (h' : u.IsDiff w v') : v = v' := by
  let pt : (𝟙_ (Over (Sp ℂ))).left := (default : PrimeSpectrum ℂ)
  have hsub : ∀ q : (𝟙_ (Over (Sp ℂ))).left, q = pt := fun q =>
    Subsingleton.elim (α := PrimeSpectrum ℂ) q pt
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := A.left) (x := (u.ex 0).left pt) (U := ⊤) trivial
  have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
    intro q _
    rw [hsub q]
    exact hx
  have h₁ := (GlobalTheory.TangentOrigin.tangent_mem_iff (u := u) hv U).2 h0
  have h₂ := (GlobalTheory.TangentOrigin.tangent_mem_iff (u := u) hv' U).2 h0
  rw [GlobalTheory.TangentOrigin.isDiff_iff hv hU h₁ h0] at h
  rw [GlobalTheory.TangentOrigin.isDiff_iff hv' hU h₂ h0] at h'
  exact Over.OverMorphism.ext (GlobalTheory.TangentOrigin.ext_evalPt hU h₁ h₂ (h.trans h'.symm))

/- English proof (translation)
Take `⟨u, -, -, -, -, -, h⟩` from `h`. Use `haveI := x.P.isAb.comm`. Take `⟨ex, tan, -⟩` from `GlobalTheory.LieComb.lieComb_algebra ℂ x.P.A x.P.g x.v x.basis.1`. Establish `hi : Function.Injective M.vecMul` using `fun c c' e => by`. Take `⟨w, hw⟩` from `(ex c).exists`.

Take `⟨w', hw'⟩` from `(ex c').exists`. Establish `d` using `GlobalTheory.UnifDifferential.isDiff_of_isLieComb x.P.A x.P.L _ _ u _ x.v c w x.basis.1 h hw`. Establish `d'` using `GlobalTheory.UnifDifferential.isDiff_of_isLieComb x.P.A x.P.L _ _ u _ x.v c' w' x.basis.1 h hw'`. Establish `e' : ∀ c : Fin x.P.g → ℂ, ∑ i, c i • ((2 * Real.pi * Complex.I : ℂ)⁻¹ • M i) = (2 * Real.pi * Complex.I : ℂ)⁻¹ • M.vecMul c` using `fun c => by`. Simplify using `only [smul_comm (c _) (2 * Real.pi * Complex.I : ℂ)⁻¹]`.

Rewrite using `[← Finset.smul_sum, ← Matrix.vecMul_eq_sum]`. Rewrite `d`, `d'` using `[e']`. Rewrite `d` using `[show Matrix.vecMul c M = Matrix.vecMul c' M from e]`. Take `rfl` from `eq_of_isDiff u (tan _ _ hw) (tan _ _ hw') d d'`. Conclude with `(x.basis.2 w (tan _ _ hw)).unique hw hw'`.

Conclude with `((Matrix.isUnit_iff_isUnit_det M).1 (Matrix.vecMul_injective_iff_isUnit.1 hi)).ne_zero`.
-/
theorem det_ne_zero_of_normalAt {x : KeyIn ℂ} {τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ} {a b : Fin x.P.g → ℂ} {c : ℂ}
    (h : NormalAt x τ M a b c) : M.det ≠ 0 := by
  obtain ⟨u, -, -, -, -, -, h⟩ := h
  haveI := x.P.isAb.comm
  obtain ⟨ex, tan, -⟩ := GlobalTheory.LieComb.lieComb_algebra ℂ x.P.A x.P.g x.v x.basis.1
  have hi : Function.Injective M.vecMul := fun c c' e => by
    obtain ⟨w, hw⟩ := (ex c).exists
    obtain ⟨w', hw'⟩ := (ex c').exists
    have d := GlobalTheory.UnifDifferential.isDiff_of_isLieComb x.P.A x.P.L _ _ u _ x.v c w x.basis.1 h hw
    have d' := GlobalTheory.UnifDifferential.isDiff_of_isLieComb x.P.A x.P.L _ _ u _ x.v c' w' x.basis.1 h hw'
    have e' : ∀ c : Fin x.P.g → ℂ, ∑ i, c i • ((2 * Real.pi * Complex.I : ℂ)⁻¹ • M i) =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ • M.vecMul c := fun c => by
      simp only [smul_comm (c _) (2 * Real.pi * Complex.I : ℂ)⁻¹]
      rw [← Finset.smul_sum, ← Matrix.vecMul_eq_sum]
    rw [e'] at d d'
    rw [show Matrix.vecMul c M = Matrix.vecMul c' M from e] at d
    obtain rfl := eq_of_isDiff u (tan _ _ hw) (tan _ _ hw') d d'
    exact (x.basis.2 w (tan _ _ hw)).unique hw hw'
  exact ((Matrix.isUnit_iff_isUnit_det M).1 (Matrix.vecMul_injective_iff_isUnit.1 hi)).ne_zero

end Tangent

section Rule

variable (κ : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ)

def FieldClause : Prop :=
  ∀ (K K' : Type) [Field K] [CharZero K] [Field K'] [CharZero K'] (f : K →+* K') (x : KeyIn K) (x' : KeyIn K'),
    KeyPB x' x f → (κ K' x' : K') = f (κ K x)

def UnitClause : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K]
    [IsFractionRing R K] (x : KeyIn R) (xK : KeyIn K), KeyPB xK x (algebraMap R K) →
    ∃ u : Rˣ, (κ K xK : K) = algebraMap R K u ∧
      ∀ (k : Type) [Field k] [CharZero k] (r : R →+* k) (xk : KeyIn k), Function.Surjective r → KeyPB xk x r →
        (κ k xk : k) = r u

def ValueAt {R : Type} [CommRing R] (y : KeyIn R) (u : R) (p : Ideal R) : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (f : R →+* K) (x : KeyIn K), RingHom.ker f = p → KeyPB x y f →
    (κ K x : K) = f u

variable {κ}

/- English proof (translation)
Introduce `K' _ _ f x hf hx`. Establish `hf' : Function.Injective f` using `(RingHom.injective_iff_ker_eq_bot f).2 hf`. Establish `e : (IsFractionRing.lift (K` using `K) hf').comp (algebraMap R K) = f := RingHom.ext fun a => IsFractionRing.lift_algebraMap hf' a`. Rewrite using `[hF K K' (IsFractionRing.lift hf') xK x (GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y xK x _ _ h (e.symm ▸ hx)), hu, IsFractionRing.lift_algebraMap]`.
-/
theorem valueAt_bot (hF : FieldClause κ) {R K : Type} [CommRing R] [Field K] [CharZero K] [Algebra R K]
    [IsFractionRing R K] {y : KeyIn R} {xK : KeyIn K} (h : KeyPB xK y (algebraMap R K)) {u : R}
    (hu : (κ K xK : K) = algebraMap R K u) : ValueAt κ y u ⊥ := by
  intro K' _ _ f x hf hx
  have hf' : Function.Injective f := (RingHom.injective_iff_ker_eq_bot f).2 hf
  have e : (IsFractionRing.lift (K := K) hf').comp (algebraMap R K) = f :=
    RingHom.ext fun a => IsFractionRing.lift_algebraMap hf' a
  rw [hF K K' (IsFractionRing.lift hf') xK x
    (GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y xK x _ _ h (e.symm ▸ hx)), hu, IsFractionRing.lift_algebraMap]

/- English proof (translation)
Take `⟨xK, hK⟩` from `exists_keyPB_ring y (algebraMap R (FractionRing R))`. Take `⟨u, hu, hsp⟩` from `hU R (FractionRing R) y xK hK`. Use `⟨u, fun p => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hp : p = ⊥`. Conclude with `hp ▸ valueAt_bot hF hK hu`.

Introduce `K _ _ f x hf hx`. Substitute `hf` using the available equality. Use `haveI := RingHom.ker_isPrime f`. Use `haveI : (RingHom.ker f).IsMaximal := Ring.DimensionLEOne.maximalOfPrime hp inferInstance`. Use `letI := Ideal.Quotient.field (RingHom.ker f)`.

Use `haveI : CharZero (R ⧸ RingHom.ker f) := (RingHom.kerLift f).charZero`. Take `⟨xk, hk⟩` from `exists_keyPB_ring y (Ideal.Quotient.mk (RingHom.ker f))`. Establish `e : (RingHom.kerLift f).comp (Ideal.Quotient.mk (RingHom.ker f)) = f` using `RingHom.ext fun a => RingHom.kerLift_mk f a`. Rewrite using `[hF _ K (RingHom.kerLift f) xk x (GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y xk x _ _ hk (e.symm ▸ hx)), hsp _ _ xk Ideal.Quotient.mk_surjective hk, RingHom.kerLift_mk]`.
-/
theorem exists_unit_dvr (hF : FieldClause κ) (hU : UnitClause κ) (R : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CharZero R] (y : KeyIn R) : ∃ u : Rˣ, ∀ p, ValueAt κ y u p := by
  obtain ⟨xK, hK⟩ := exists_keyPB_ring y (algebraMap R (FractionRing R))
  obtain ⟨u, hu, hsp⟩ := hU R (FractionRing R) y xK hK
  refine ⟨u, fun p => ?_⟩
  by_cases hp : p = ⊥
  · exact hp ▸ valueAt_bot hF hK hu
  intro K _ _ f x hf hx
  subst hf
  haveI := RingHom.ker_isPrime f
  haveI : (RingHom.ker f).IsMaximal := Ring.DimensionLEOne.maximalOfPrime hp inferInstance
  letI := Ideal.Quotient.field (RingHom.ker f)
  haveI : CharZero (R ⧸ RingHom.ker f) := (RingHom.kerLift f).charZero
  obtain ⟨xk, hk⟩ := exists_keyPB_ring y (Ideal.Quotient.mk (RingHom.ker f))
  have e : (RingHom.kerLift f).comp (Ideal.Quotient.mk (RingHom.ker f)) = f :=
    RingHom.ext fun a => RingHom.kerLift_mk f a
  rw [hF _ K (RingHom.kerLift f) xk x (GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y xk x _ _ hk (e.symm ▸ hx)),
    hsp _ _ xk Ideal.Quotient.mk_surjective hk, RingHom.kerLift_mk]

/- English proof (translation)
Introduce `K _ _ f x hf hx`. Use `h K (f.comp j) x ?_ (GlobalTheory.keyPB_trans _ _ _ y y' x j f hy hx)` and prove the remaining obligations. Rewrite using `[← RingHom.comap_ker, hf, ← hj]`. Both sides reduce to the same expression.
-/
theorem ValueAt.map_bot {R R' : Type} [CommRing R] [CommRing R'] {y : KeyIn R} {u : R} {p : Ideal R}
    (h : ValueAt κ y u p) (j : R →+* R') (hj : RingHom.ker j = p) {y' : KeyIn R'} (hy : KeyPB y' y j) :
    ValueAt κ y' (j u) ⊥ := by
  intro K _ _ f x hf hx
  refine h K (f.comp j) x ?_ (GlobalTheory.keyPB_trans _ _ _ y y' x j f hy hx)
  rw [← RingHom.comap_ker, hf, ← hj]
  rfl

/- English proof (translation)
Take `⟨x, hx⟩` from `exists_keyPB_ring y (algebraMap R (FractionRing R))`. Establish `hi` using `IsFractionRing.injective R (FractionRing R)`. Establish `hk` using `(RingHom.injective_iff_ker_eq_bot _).1 hi`. Conclude with `hi ((h _ _ x hk hx).symm.trans (h' _ _ x hk hx))`.
-/
theorem ValueAt.unique {R : Type} [CommRing R] [IsDomain R] [CharZero R] {y : KeyIn R} {u u' : R}
    (h : ValueAt κ y u ⊥) (h' : ValueAt κ y u' ⊥) : u = u' := by
  obtain ⟨x, hx⟩ := exists_keyPB_ring y (algebraMap R (FractionRing R))
  have hi := IsFractionRing.injective R (FractionRing R)
  have hk := (RingHom.injective_iff_ker_eq_bot _).1 hi
  exact hi ((h _ _ x hk hx).symm.trans (h' _ _ x hk hx))

/- English proof (translation)
Introduce `K _ _ f x hf hx`. Establish `hs : ∀ s : p.primeCompl, IsUnit (f s)` using `fun s => Ne.isUnit fun h0 => s.2 (show (s : R) ∈ p from hf ▸ h0)`. Set `g : Localization.AtPrime p →+* K` to `IsLocalization.lift hs`. Establish `e : g.comp (algebraMap _ _) = f` using `IsLocalization.lift_comp hs`. Take `⟨y', hy⟩` from `exists_keyPB_ring y (algebraMap R (Localization.AtPrime p))`.

Establish `hk : RingHom.ker g = IsLocalRing.maximalIdeal _`. Use `le_antisymm (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top g)) ?_` and prove the remaining obligations. Rewrite using `[← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap, RingHom.comap_ker, e, hf]`. Rewrite using `[h g.charZero y' hy K g x hk (GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y y' x _ _ hy (e.symm ▸ hx))]`. Conclude with `IsLocalization.lift_eq hs u`.
-/
theorem valueAt_of_localization {R : Type} [CommRing R] {y : KeyIn R} {u : R} (p : Ideal R) [p.IsPrime]
    (h : CharZero (Localization.AtPrime p) → ∀ y' : KeyIn (Localization.AtPrime p),
      KeyPB y' y (algebraMap _ _) → ValueAt κ y' (algebraMap _ _ u) (IsLocalRing.maximalIdeal _)) :
    ValueAt κ y u p := by
  intro K _ _ f x hf hx
  have hs : ∀ s : p.primeCompl, IsUnit (f s) := fun s =>
    Ne.isUnit fun h0 => s.2 (show (s : R) ∈ p from hf ▸ h0)
  let g : Localization.AtPrime p →+* K := IsLocalization.lift hs
  have e : g.comp (algebraMap _ _) = f := IsLocalization.lift_comp hs
  obtain ⟨y', hy⟩ := exists_keyPB_ring y (algebraMap R (Localization.AtPrime p))
  have hk : RingHom.ker g = IsLocalRing.maximalIdeal _ := by
    refine le_antisymm (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top g)) ?_
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap, RingHom.comap_ker, e, hf]
  rw [h g.charZero y' hy K g x hk (GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y y' x _ _ hy (e.symm ▸ hx))]
  exact IsLocalization.lift_eq hs u

/- English proof (translation)
The claim follows from `(RingHom.injective_iff_ker_eq_bot _).1 (IsLocalization.injective _ p.primeCompl_le_nonZeroDivisors)`.
-/
theorem ker_algebraMap_atPrime {R : Type} [CommRing R] [IsDomain R] (p : Ideal R) [p.IsPrime] :
    RingHom.ker (algebraMap R (Localization.AtPrime p)) = ⊥ :=
  (RingHom.injective_iff_ker_eq_bot _).1 (IsLocalization.injective _ p.primeCompl_le_nonZeroDivisors)

/- English proof (translation)
Use `valueAt_of_localization p fun _ y' hy => ?_` and prove the remaining obligations. Take `⟨u', hu'⟩` from `exists_unit_dvr hF hU _ y'`. Rewrite using `[(h.map_bot _ (ker_algebraMap_atPrime p) hy).unique (hu' ⊥)]`. Conclude with `hu' _`.
-/
theorem ValueAt.specialize (hF : FieldClause κ) (hU : UnitClause κ) {R : Type} [CommRing R] [IsDomain R]
    {y : KeyIn R} {u : R} (h : ValueAt κ y u ⊥) (p : Ideal R) [p.IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime p)] : ValueAt κ y u p := by
  refine valueAt_of_localization p fun _ y' hy => ?_
  obtain ⟨u', hu'⟩ := exists_unit_dvr hF hU _ y'
  rw [(h.map_bot _ (ker_algebraMap_atPrime p) hy).unique (hu' ⊥)]
  exact hu' _

/- English proof (translation)
Establish `hm : IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.span {π})) = Ideal.span {algebraMap R _ π}`. Rewrite using `[← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]`. Establish `hnf : ¬ IsField (Localization.AtPrime (Ideal.span {π}))` using `fun hf => by`. Rewrite `hf` using `[IsLocalRing.isField_iff_maximalIdeal_eq, hm, Ideal.span_singleton_eq_bot]`. Conclude with `h0 ((Ideal.mem_bot).1 (ker_algebraMap_atPrime (Ideal.span {π}) ▸ hf))`.

Establish `hp : (IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.span {π}))).IsPrincipal` using `⟨_, hm⟩`. Conclude with `((IsDiscreteValuationRing.TFAE _ hnf).out 0 4).2 hp`.
-/
theorem isDiscreteValuationRing_atPrime_span {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {π : R}
    (h0 : π ≠ 0) [(Ideal.span {π}).IsPrime] : IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {π})) := by
  have hm : IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.span {π})) = Ideal.span {algebraMap R _ π} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]
  have hnf : ¬ IsField (Localization.AtPrime (Ideal.span {π})) := fun hf => by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hm, Ideal.span_singleton_eq_bot] at hf
    exact h0 ((Ideal.mem_bot).1 (ker_algebraMap_atPrime (Ideal.span {π}) ▸ hf))
  have hp : (IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.span {π}))).IsPrincipal := ⟨_, hm⟩
  exact ((IsDiscreteValuationRing.TFAE _ hnf).out 0 4).2 hp

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `R _ _ y u hn h`. Distinguish the cases in `hsq : IsLocalRing.maximalIdeal R ≤ IsLocalRing.maximalIdeal R ^ 2`. Rewrite using `[ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.maximalIdeal_eq_bot_of_le_sq R hsq]` and apply the resulting hypothesis.

Take `⟨π, hπ, hπ2⟩` from `SetLike.not_le_iff_exists.1 hsq`. Use `haveI := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain R`. Use `haveI := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.quotient_span_singleton hπ hπ2`. Use `haveI := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain (R ⧸ Ideal.span {π})`. Use `haveI : (Ideal.span {π}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).1 inferInstance`.

Use `haveI := isDiscreteValuationRing_atPrime_span (π := π) (fun h0 => hπ2 (h0 ▸ Ideal.zero_mem _))`. Establish `hd` using `ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.ringKrullDim_quotient_span_singleton_add_one hπ hπ2`. Rewrite `hd` using `[← IsRegularLocalRing.spanFinrank_maximalIdeal, ← IsRegularLocalRing.spanFinrank_maximalIdeal, hn]`. Establish `hd' : (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {π})).spanFinrank + 1 = n` using `by exact_mod_cast hd`. Take `⟨y', hy⟩` from `exists_keyPB_ring y (Ideal.Quotient.mk (Ideal.span {π}))`.

Establish `h'` using `ih _ (by omega) (R ⧸ Ideal.span {π}) y' _ rfl ((h.specialize hF hU (Ideal.span {π})).map_bot _ Ideal.mk_ker hy)`. Introduce `K _ _ f x hf hx`. Establish `hz : ∀ a ∈ Ideal.span {π}, f a = 0` using `fun a ha => (show Ideal.span {π} ≤ RingHom.ker f from hf ▸ (Ideal.span_singleton_le_iff_mem _).2 hπ) ha`. Set `g` to `Ideal.Quotient.lift (Ideal.span {π}) f hz`. Establish `e : g.comp (Ideal.Quotient.mk _) = f` using `RingHom.ext fun a => Ideal.Quotient.lift_mk (Ideal.span {π}) f hz`.

Establish `hk : RingHom.ker g = IsLocalRing.maximalIdeal _`. Use `le_antisymm (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top g)) fun a ha => ?_` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Establish `: a ∈ RingHom.ker f`. Rewrite using `[hf]`.

Conclude with `fun hu => ha (hu.map _)`. Conclude with `this`. Conclude with `h' K g x hk (GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y y' x _ _ hy (e.symm ▸ hx))`.
-/
theorem valueAt_maximalIdeal (hF : FieldClause κ) (hU : UnitClause κ) (n : ℕ) :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (y : KeyIn R) (u : R),
      (IsLocalRing.maximalIdeal R).spanFinrank = n → ValueAt κ y u ⊥ →
      ValueAt κ y u (IsLocalRing.maximalIdeal R) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro R _ _ y u hn h
  by_cases hsq : IsLocalRing.maximalIdeal R ≤ IsLocalRing.maximalIdeal R ^ 2
  · rwa [ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.maximalIdeal_eq_bot_of_le_sq R hsq]
  obtain ⟨π, hπ, hπ2⟩ := SetLike.not_le_iff_exists.1 hsq
  haveI := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain R
  haveI := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.quotient_span_singleton hπ hπ2
  haveI := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain (R ⧸ Ideal.span {π})
  haveI : (Ideal.span {π}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).1 inferInstance
  haveI := isDiscreteValuationRing_atPrime_span (π := π) (fun h0 => hπ2 (h0 ▸ Ideal.zero_mem _))
  have hd := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.ringKrullDim_quotient_span_singleton_add_one hπ hπ2
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, ← IsRegularLocalRing.spanFinrank_maximalIdeal, hn] at hd
  have hd' : (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {π})).spanFinrank + 1 = n := by exact_mod_cast hd
  obtain ⟨y', hy⟩ := exists_keyPB_ring y (Ideal.Quotient.mk (Ideal.span {π}))
  have h' := ih _ (by omega) (R ⧸ Ideal.span {π}) y' _ rfl
    ((h.specialize hF hU (Ideal.span {π})).map_bot _ Ideal.mk_ker hy)
  intro K _ _ f x hf hx
  have hz : ∀ a ∈ Ideal.span {π}, f a = 0 := fun a ha =>
    (show Ideal.span {π} ≤ RingHom.ker f from hf ▸ (Ideal.span_singleton_le_iff_mem _).2 hπ) ha
  let g := Ideal.Quotient.lift (Ideal.span {π}) f hz
  have e : g.comp (Ideal.Quotient.mk _) = f := RingHom.ext fun a => Ideal.Quotient.lift_mk (Ideal.span {π}) f hz
  have hk : RingHom.ker g = IsLocalRing.maximalIdeal _ := by
    refine le_antisymm (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top g)) fun a ha => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : a ∈ RingHom.ker f := by
      rw [hf]
      exact fun hu => ha (hu.map _)
    exact this
  exact h' K g x hk (GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y y' x _ _ hy (e.symm ▸ hx))

/- English proof (translation)
Set `K` to `FractionRing S`. Take `⟨xK, hK⟩` from `exists_keyPB_ring y (algebraMap S K)`. Take `⟨h₁, h₂, -⟩` from `GlobalTheory.normal_domain_height_one.{0, 0, 0} S K`. Establish `key : ∀ (p : Ideal S) [p.IsPrime], p.height = 1 → (κ K xK : K) ∈ primeLocalSubalgebra K p ∧ ((κ K xK)⁻¹ : Kˣ).val ∈ primeLocalSubalgebra K p`. Introduce `p _ hp`.

Take `⟨-, _, -⟩` from `h₁ p hp`. Take `⟨y', hy⟩` from `exists_keyPB_ring y (algebraMap S (primeLocalSubalgebra K p))`. Use `haveI : CharZero (primeLocalSubalgebra K p) := (primeLocalSubalgebra K p).val.toRingHom.charZero`. Take `⟨u, hu⟩` from `exists_unit_dvr hF hU _ y'`. Establish `e` using `hu _ K (primeLocalSubalgebra K p).val.toRingHom xK rfl (GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y y' xK _ _ hy hK)`.

Establish `e' : κ K xK = Units.map (primeLocalSubalgebra K p).val.toRingHom.toMonoidHom u` using `Units.ext e`. Rewrite using `[e', ← map_inv]`. Conclude with `⟨u.val.2, u⁻¹.val.2⟩`. Take `⟨a, ha⟩` from `(h₂ _).2 fun p _ hp => (key p hp).1`. Take `⟨b, hb⟩` from `(h₂ _).2 fun p _ hp => (key p hp).2`.

Establish `hab : a * b = 1` using `IsFractionRing.injective S K (by rw [map_mul, ha, hb, map_one, Units.mul_inv])`. Conclude with `⟨Units.mkOfMulEqOne a b hab, valueAt_bot hF hK ha.symm⟩`.
-/
theorem exists_unit_normal (hF : FieldClause κ) (hU : UnitClause κ) (S : Type) [CommRing S] [IsDomain S]
    [IsNoetherianRing S] [IsIntegrallyClosed S] [CharZero S] (y : KeyIn S) : ∃ u : Sˣ, ValueAt κ y u ⊥ := by
  let K := FractionRing S
  obtain ⟨xK, hK⟩ := exists_keyPB_ring y (algebraMap S K)
  obtain ⟨h₁, h₂, -⟩ := GlobalTheory.normal_domain_height_one.{0, 0, 0} S K
  have key : ∀ (p : Ideal S) [p.IsPrime], p.height = 1 →
      (κ K xK : K) ∈ primeLocalSubalgebra K p ∧ ((κ K xK)⁻¹ : Kˣ).val ∈ primeLocalSubalgebra K p := by
    intro p _ hp
    obtain ⟨-, _, -⟩ := h₁ p hp
    obtain ⟨y', hy⟩ := exists_keyPB_ring y (algebraMap S (primeLocalSubalgebra K p))
    haveI : CharZero (primeLocalSubalgebra K p) := (primeLocalSubalgebra K p).val.toRingHom.charZero
    obtain ⟨u, hu⟩ := exists_unit_dvr hF hU _ y'
    have e := hu _ K (primeLocalSubalgebra K p).val.toRingHom xK rfl
      (GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y y' xK _ _ hy hK)
    have e' : κ K xK = Units.map (primeLocalSubalgebra K p).val.toRingHom.toMonoidHom u := Units.ext e
    rw [e', ← map_inv]
    exact ⟨u.val.2, u⁻¹.val.2⟩
  obtain ⟨a, ha⟩ := (h₂ _).2 fun p _ hp => (key p hp).1
  obtain ⟨b, hb⟩ := (h₂ _).2 fun p _ hp => (key p hp).2
  have hab : a * b = 1 := IsFractionRing.injective S K (by rw [map_mul, ha, hb, map_one, Units.mul_inv])
  exact ⟨Units.mkOfMulEqOne a b hab, valueAt_bot hF hK ha.symm⟩

/- English proof (translation)
Take `⟨u, hu⟩` from `exists_unit_normal hF hU S y`. Use `⟨u, fun K _ _ f x hx => ?_⟩` and prove the remaining obligations. Use `haveI := RingHom.ker_isPrime f`. Use `haveI := isRegularRing_iff.mp ‹IsRegularRing S› (RingHom.ker f)`. Conclude with `valueAt_of_localization (RingHom.ker f) (fun _ y' hy => valueAt_maximalIdeal hF hU _ _ y' _ rfl (hu.map_bot _ (ker_algebraMap_atPrime _) hy)) K f x rfl hx`.
-/
theorem exists_unit_regular (hF : FieldClause κ) (hU : UnitClause κ) (S : Type) [CommRing S] [IsDomain S]
    [IsRegularRing S] [IsIntegrallyClosed S] [CharZero S] (y : KeyIn S) :
    ∃ u : Sˣ, ∀ (K : Type) [Field K] [CharZero K] (f : S →+* K) (x : KeyIn K), KeyPB x y f → (κ K x : K) = f u := by
  obtain ⟨u, hu⟩ := exists_unit_normal hF hU S y
  refine ⟨u, fun K _ _ f x hx => ?_⟩
  haveI := RingHom.ker_isPrime f
  haveI := isRegularRing_iff.mp ‹IsRegularRing S› (RingHom.ker f)
  exact valueAt_of_localization (RingHom.ker f) (fun _ y' hy => valueAt_maximalIdeal hF hU _ _ y' _ rfl
    (hu.map_bot _ (ker_algebraMap_atPrime _) hy)) K f x rfl hx

end Rule

/- English proof (translation)
Introduce and unpack `- - N ⟨κ, hH, hF, hU, hN⟩ k S _ _ _ _ _ _ y`. Use `haveI : CharZero S := charZero_of_injective_algebraMap (algebraMap k S).injective`. Use `haveI : IsRegularRing S := GlobalTheory.isRegularRing_of_smooth k S`. Use `haveI : IsIntegrallyClosed S := IsIntegrallyClosed.of_localization_maximal fun p _ hp => (GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_smooth k p (Localization.AtPrime p)).2`. Take `⟨u, hu⟩` from `exists_unit_regular (κ := κ) (fun K K' _ _ _ _ f x x' => hF K K' f x x' x.g_pos) (fun R K _ _ _ _ _ _ _ x xK => hU R K x xK x.g_pos) S y`.

Use `⟨u, ?_⟩` and prove the remaining obligations. Introduce and unpack `s x t hx ⟨τ, M, a, b, c, hab, hc, hn, rfl⟩`. Establish `hg : x.P.g = y.P.g`. Take `⟨_, _, _, hg, -⟩` from `hx`. Conclude with `hg`.

Rewrite using `[← hu ℂ s x hx, ← hg]`. Conclude with `(value_at_normalForm N 1 (κ ℂ) x.P.g a b x.g_pos (hH ℂ) (fun y h τ' hy => hN y τ' _ _ y.g_pos ⟨fun i => hab.1 _, fun i => hab.2 _⟩ hy) x rfl τ M c hc (det_ne_zero_of_normalAt hn) hn).symm`.
-/
theorem exists_unit_of_smooth : ThetaUnifAV → Out.PolBaseChangeSt → ∀ N : ℕ → ℕ, KeyRule N 1 charHalf → ∀ (k S : Type) [Field k] [CharZero k] [CommRing S] [IsDomain S] [Algebra k S] [Algebra.Smooth k S] (y : KeyIn S), ∃ κ : Sˣ, ∀ (s : S →+* ℂ) (x : KeyIn ℂ) (t : ℂ), KeyPB x y s → (∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t = M.det ^ 4 / c ^ 8) → t ^ N y.P.g = s κ := by
  rintro - - N ⟨κ, hH, hF, hU, hN⟩ k S _ _ _ _ _ _ y
  haveI : CharZero S := charZero_of_injective_algebraMap (algebraMap k S).injective
  haveI : IsRegularRing S := GlobalTheory.isRegularRing_of_smooth k S
  haveI : IsIntegrallyClosed S := IsIntegrallyClosed.of_localization_maximal fun p _ hp =>
    (GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_smooth k p (Localization.AtPrime p)).2
  obtain ⟨u, hu⟩ := exists_unit_regular (κ := κ) (fun K K' _ _ _ _ f x x' => hF K K' f x x' x.g_pos)
    (fun R K _ _ _ _ _ _ _ x xK => hU R K x xK x.g_pos) S y
  refine ⟨u, ?_⟩
  rintro s x t hx ⟨τ, M, a, b, c, hab, hc, hn, rfl⟩
  have hg : x.P.g = y.P.g := by
    obtain ⟨_, _, _, hg, -⟩ := hx
    exact hg
  rw [← hu ℂ s x hx, ← hg]
  exact (value_at_normalForm N 1 (κ ℂ) x.P.g a b x.g_pos (hH ℂ)
    (fun y h τ' hy => hN y τ' _ _ y.g_pos ⟨fun i => hab.1 _, fun i => hab.2 _⟩ hy) x rfl τ M c hc
    (det_ne_zero_of_normalAt hn) hn).symm

end GlobalTheory.KeySmoothBase
end
