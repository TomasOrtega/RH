import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCommonMultiple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecValEqIff

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FiniteCover

variable {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X']

/- English proof (translation)
Establish `h : (⊥ : PrimeSpectrum A).asIdeal.primeCompl ≤ nonZeroDivisors A` using `fun x hx => mem_nonZeroDivisors_of_ne_zero fun h0 => hx (h0 ▸ Ideal.zero_mem _)`. Rewrite using `[Module.rankAtStalk, IsLocalization.finrank_eq _ _ h]`. Conclude with `IsLocalizedModule.finrank_eq _ (LocalizedModule.mkLinearMap _ C) h`.
-/
theorem rankAtStalk_bot {A C : Type} [CommRing A] [IsDomain A] [AddCommGroup C] [Module A C] :
    Module.rankAtStalk (R := A) C ⊥ = Module.finrank A C := by
  have h : (⊥ : PrimeSpectrum A).asIdeal.primeCompl ≤ nonZeroDivisors A := fun x hx =>
    mem_nonZeroDivisors_of_ne_zero fun h0 => hx (h0 ▸ Ideal.zero_mem _)
  rw [Module.rankAtStalk, IsLocalization.finrank_eq _ _ h]
  exact IsLocalizedModule.finrank_eq _ (LocalizedModule.mkLinearMap _ C) h

/- English proof (translation)
Take `⟨y, hy⟩` from `φ.surjective (genericPoint X)`. Conclude with `generic_mem (x := y) (show φ y ∈ U from hy ▸ h)`.
-/
theorem generic_mem_preimage (φ : X' ⟶ X) [Surjective φ] {U : X.Opens} (h : genericPoint X ∈ U) :
    genericPoint X' ∈ φ ⁻¹ᵁ U := by
  obtain ⟨y, hy⟩ := φ.surjective (genericPoint X)
  exact generic_mem (x := y) (show φ y ∈ U from hy ▸ h)

/- English proof (translation)
Establish `h'` using `generic_mem_preimage φ h`. Use `haveI : Nonempty D := ⟨⟨_, h⟩⟩`. Use `haveI : Nonempty (φ ⁻¹ᵁ D) := ⟨⟨_, h'⟩⟩`. Use `letI := (φ.app D).hom.toAlgebra`. Use `haveI : Module.Finite Γ(X, D) Γ(X', φ ⁻¹ᵁ D) := φ.finite_app D hD`.

Use `haveI : Module.Flat Γ(X, D) Γ(X', φ ⁻¹ᵁ D) := by`. Use `φ.flat_appLE hD (hD.preimage φ) le_rfl` as an intermediate fact. Rewrite `this` using `[Scheme.Hom.appLE_eq_app]`. Then use the resulting hypothesis. Use `haveI := functionField_isFractionRing_of_isAffineOpen X D hD`. Use `haveI := functionField_isFractionRing_of_isAffineOpen X' _ (hD.preimage φ)`.

Use `letI : Algebra Γ(X, D) X'.functionField := ((algebraMap X.functionField X'.functionField).comp (algebraMap Γ(X, D) X.functionField)).toAlgebra`. Use `haveI : IsScalarTower Γ(X, D) X.functionField X'.functionField := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : IsScalarTower Γ(X, D) Γ(X', φ ⁻¹ᵁ D) X'.functionField := IsScalarTower.of_algebraMap_eq fun a => by`. Establish `e` using `toField_appLE φ le_rfl h h' a`. Rewrite `e` using `[Scheme.Hom.appLE_eq_app]`.

Conclude with `(hF _).trans e.symm`. Use `⟨⟨hD.fromSpec (⊥ : PrimeSpectrum Γ(X, D)), ?_⟩, fun e => ?_⟩` and prove the remaining obligations. Establish `hp : IsPullback (hD.preimage φ).fromSpec (Spec.map (φ.app D)) φ hD.fromSpec` using `(IsOpenImmersion.isPullback _ _ _ _ (by`. Rewrite using `[Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec φ hD (hD.preimage φ)])`. Use the proof step `(by simp)).flip`.

Rewrite using `[IsFractionRing.finrank_eq Γ(X, D) X.functionField Γ(X', φ ⁻¹ᵁ D) X'.functionField, ← rankAtStalk_bot]`. Use `Eq.trans ?_ (Scheme.Hom.finrank_of_isPullback _ _ _ _ hp _)` and prove the remaining obligations. Conclude with `(Scheme.Hom.finrank_SpecMap_algebraMap Γ(X, D) Γ(X', φ ⁻¹ᵁ D) _).symm`. Take `⟨c, hc, h₁, h₂⟩` from `exists_denominator (A := Γ(X, D)) (C := Γ(X', φ ⁻¹ᵁ D)) e`. Use `⟨toField h c, ⟨c, rfl⟩, fun h0 => hc (toField_injective h (h0.trans (map_zero _).symm)), ?_, h₂⟩` and prove the remaining obligations.

Introduce and unpack `j _ ⟨y, rfl⟩`. Conclude with `h₁ j y`.
-/
theorem chart_data (φ : X' ⟶ X) [IsFinite φ] [Flat φ] [Surjective φ]
    [Algebra X.functionField X'.functionField]
    (hF : ∀ x, algebraMap X.functionField X'.functionField x = functionFieldMap φ x)
    {D : X.Opens} (hD : IsAffineOpen D) (h : genericPoint X ∈ D) :
    (∃ x, Module.finrank X.functionField X'.functionField = φ.finrank x) ∧
    ∀ {d : ℕ} (e : Module.Basis (Fin d) X.functionField X'.functionField),
      ∃ c ∈ (toField h).range, c ≠ 0 ∧
        (∀ j, ∀ y ∈ (toField (generic_mem_preimage φ h)).range, c * e.repr y j ∈ (toField h).range) ∧
        ∀ j, c • e j ∈ (toField (generic_mem_preimage φ h)).range := by
  have h' := generic_mem_preimage φ h
  haveI : Nonempty D := ⟨⟨_, h⟩⟩
  haveI : Nonempty (φ ⁻¹ᵁ D) := ⟨⟨_, h'⟩⟩
  letI := (φ.app D).hom.toAlgebra
  haveI : Module.Finite Γ(X, D) Γ(X', φ ⁻¹ᵁ D) := φ.finite_app D hD
  haveI : Module.Flat Γ(X, D) Γ(X', φ ⁻¹ᵁ D) := by
    have := φ.flat_appLE hD (hD.preimage φ) le_rfl
    rwa [Scheme.Hom.appLE_eq_app] at this
  haveI := functionField_isFractionRing_of_isAffineOpen X D hD
  haveI := functionField_isFractionRing_of_isAffineOpen X' _ (hD.preimage φ)
  letI : Algebra Γ(X, D) X'.functionField :=
    ((algebraMap X.functionField X'.functionField).comp (algebraMap Γ(X, D) X.functionField)).toAlgebra
  haveI : IsScalarTower Γ(X, D) X.functionField X'.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower Γ(X, D) Γ(X', φ ⁻¹ᵁ D) X'.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => by
      have e := toField_appLE φ le_rfl h h' a
      rw [Scheme.Hom.appLE_eq_app] at e
      exact (hF _).trans e.symm
  refine ⟨⟨hD.fromSpec (⊥ : PrimeSpectrum Γ(X, D)), ?_⟩, fun e => ?_⟩
  · have hp : IsPullback (hD.preimage φ).fromSpec (Spec.map (φ.app D)) φ hD.fromSpec :=
      (IsOpenImmersion.isPullback _ _ _ _ (by
        rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec φ hD (hD.preimage φ)])
        (by simp)).flip
    rw [IsFractionRing.finrank_eq Γ(X, D) X.functionField Γ(X', φ ⁻¹ᵁ D) X'.functionField,
      ← rankAtStalk_bot]
    refine Eq.trans ?_ (Scheme.Hom.finrank_of_isPullback _ _ _ _ hp _)
    exact (Scheme.Hom.finrank_SpecMap_algebraMap Γ(X, D) Γ(X', φ ⁻¹ᵁ D) _).symm
  · obtain ⟨c, hc, h₁, h₂⟩ := exists_denominator (A := Γ(X, D)) (C := Γ(X', φ ⁻¹ᵁ D)) e
    refine ⟨toField h c, ⟨c, rfl⟩, fun h0 => hc (toField_injective h (h0.trans (map_zero _).symm)),
      ?_, h₂⟩
    rintro j _ ⟨y, rfl⟩
    exact h₁ j y

/- English proof (translation)
Establish `hb : genericPoint X ∈ X.basicOpen r` using `(Scheme.mem_basicOpen X r _ h).2 (isUnit_iff_ne_zero.2 hr)`. Use `hD.isLocalization_basicOpen r` as an intermediate fact. Take `⟨m, b, e⟩` from `IsLocalization.Away.surj r (rs X hle c)`. Establish `e' : toField hb (rs X hle c * rs X (X.basicOpen_le r) r ^ m) = toField hb (rs X (X.basicOpen_le r) b)` using `congrArg (toField hb) e`. Rewrite `e'` using `[map_mul, map_pow, toField_rs, toField_rs, toField_rs]`.

Conclude with `⟨m, b, e'.symm⟩`.
-/
theorem exists_mul_pow_mem {D D' : X.Opens} (hD : IsAffineOpen D) (h : genericPoint X ∈ D)
    (h' : genericPoint X ∈ D') (r : Γ(X, D)) (hr : toField h r ≠ 0) (hle : X.basicOpen r ≤ D')
    (c : Γ(X, D')) : ∃ m : ℕ, toField h' c * toField h r ^ m ∈ (toField h).range := by
  have hb : genericPoint X ∈ X.basicOpen r :=
    (Scheme.mem_basicOpen X r _ h).2 (isUnit_iff_ne_zero.2 hr)
  have := hD.isLocalization_basicOpen r
  obtain ⟨m, b, e⟩ := IsLocalization.Away.surj r (rs X hle c)
  have e' : toField hb (rs X hle c * rs X (X.basicOpen_le r) r ^ m) =
      toField hb (rs X (X.basicOpen_le r) b) := congrArg (toField hb) e
  rw [map_mul, map_pow, toField_rs, toField_rs, toField_rs] at e'
  exact ⟨m, b, e'.symm⟩

omit [IsIntegral X] in

/- English proof (translation)
Introduce `x hx`. Establish `hs : x ∈ nonzeroLocus s` using `X.basicOpen_le r hx`. Take `⟨l, hl⟩` from `TopologicalSpace.Opens.mem_iSup.1 hs`. Establish `e` using `congrArg X.basicOpen (h l)`. Rewrite `e` using `[Scheme.basicOpen_mul]`.

Use `erw [Scheme.basicOpen_res, Scheme.basicOpen_res, Scheme.basicOpen_res] at e`. Establish `hx' : x ∈ nonzeroLocus s ⊓ H.U l` using `⟨hs, X.basicOpen_le _ hl⟩`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨l, (e.ge ⟨⟨hx', hx⟩, hx', hl⟩).2⟩`.
-/
theorem basicOpen_le_nonzeroLocus {H : LB X} (s s' : LB.Sec H) (r : Γ(X, nonzeroLocus s))
    (h : ∀ k, rs X (inf_le_right : nonzeroLocus s ⊓ H.U k ≤ H.U k) (s'.f k) =
      rs X (inf_le_left : nonzeroLocus s ⊓ H.U k ≤ nonzeroLocus s) r *
        rs X (inf_le_right : nonzeroLocus s ⊓ H.U k ≤ H.U k) (s.f k)) :
    X.basicOpen r ≤ nonzeroLocus s' := by
  intro x hx
  have hs : x ∈ nonzeroLocus s := X.basicOpen_le r hx
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hs
  have e := congrArg X.basicOpen (h l)
  rw [Scheme.basicOpen_mul] at e
  erw [Scheme.basicOpen_res, Scheme.basicOpen_res, Scheme.basicOpen_res] at e
  have hx' : x ∈ nonzeroLocus s ⊓ H.U l := ⟨hs, X.basicOpen_le _ hl⟩
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨l, (e.ge ⟨⟨hx', hx⟩, hx', hl⟩).2⟩

def powSec {X : Scheme.{0}} {H : LB X} (s : LB.Sec H) (t : ℕ) : LB.Sec (pw H t) where
  f k := (s.f k : Γ(X, H.U k)) ^ t
  compat i j := by
    have e := congrArg (· ^ t) (s.compat i j)
    simp only [mul_pow, ← map_pow] at e
    refine e.trans ?_
    congr 1

end GlobalTheory.FiniteCover

namespace GlobalTheory

open FiniteCover

/- English proof (translation)
Introduce `K _ X X' _ _ f φ _ _ H n s hH hs d hd hV hW`. Establish `hd1 : 1 ≤ d` using `hd _ ▸ φ.one_le_finrank_map (genericPoint X')`. Use `haveI : Surjective φ := φ.one_le_finrank_iff_surjective.1 fun x => (hd x).symm ▸ hd1`. Use `letI : Algebra X.functionField X'.functionField := (functionFieldMap φ).toAlgebra`. Use `letI : Algebra K X.functionField := ((toField generic_top).comp (cst f ⊤)).toAlgebra`.

Use `letI : Algebra K X'.functionField := ((toField generic_top).comp (cst (φ ≫ f) ⊤)).toAlgebra`. Use `haveI : IsScalarTower K X.functionField X'.functionField := IsScalarTower.of_algebraMap_eq fun r => by`. Establish `w : φ ≫ f = (φ ≫ f) ≫ Spec.map (CommRingCat.ofHom (RingHom.id K))` using `by simp`. Establish `e` using `toField_appLE φ (U := ⊤) (V := ⊤) le_top generic_top generic_top (cst f ⊤ r)`. Conclude with `(congrArg (toField generic_top) (appLE_cst w (V := ⊤) (V' := ⊤) le_top r)).symm.trans e`.

Take `⟨hcov, hs⟩` from `hs`. Use `choose haff r hr _ using hs`. Set `I` to `{i // genericPoint X ∈ nonzeroLocus (s i)}`. Use `haveI : Fintype I := Fintype.ofFinite I`. Set `D : I → X.Opens` to `fun i => nonzeroLocus (s i.1)`.

Establish `hη : ∀ i, genericPoint X ∈ D i` using `fun i => i.2`. Establish `hc : ⊤ ≤ ⨆ i, D i` using `fun x hx => by`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 (hcov.ge hx)`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, generic_mem hi⟩, hi⟩`. Establish `hc' : ⊤ ≤ ⨆ i, φ ⁻¹ᵁ D i` using `fun x _ => by`.

Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 (hc (trivial : φ x ∈ ⊤))`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩`. Take `⟨i₀, -⟩` from `TopologicalSpace.Opens.mem_iSup.1 (hc generic_top)`. Take `⟨k₀, h₀⟩` from `TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge generic_top)`. Take `⟨x, hx⟩` from `(chart_data φ (fun _ => rfl) (haff i₀.1) (hη i₀)).1`.

Rewrite `hx` using `[hd]`. Use `haveI : Module.Finite X.functionField X'.functionField := Module.finite_of_finrank_pos (by omega)`. Set `e` to `Module.finBasisOfFinrankEq _ _ hx`. Use `choose c hcm hc0 hc₁ hc₂ using fun i : I => (chart_data φ (fun _ => rfl) (haff i.1) (hη i)).2 e`. Set `ρ : I → X.functionField` to `fun i => toField h₀ ((s i.1).f k₀)`.

Establish `hu : ∀ (i : I) k, IsUnit (rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k) ((s i.1).f k))` using `fun i k => SecOn.isUnit_rs_of_le_nonzeroLocus _ k _ inf_le_left`. Establish `hρ : ∀ i, ρ i ≠ 0` using `fun i => by`. Use `((hu i k₀).map (toField (generic_inf (hη i) h₀))).ne_zero` as an intermediate fact. Rewrite `this` using `[toField_rs]`. Then use the resulting hypothesis. Establish `hρr : ∀ i k : I, ρ i / ρ k = toField (hη k) (r k.1 i.1)` using `fun i k => by`.

Use `congrArg (toField (generic_inf (hη k) h₀)) (hr k.1 i.1 k₀)` as an intermediate fact. Rewrite `this` using `[map_mul, toField_rs, toField_rs, toField_rs]`. Conclude with `(div_eq_iff (hρ k)).2 this`. Set `τ : ∀ (t : ℕ) (i : I), SecOn (pw H t) (D i)` to `fun t i => GlobalTheory.LB.ofSec (powSec (s i.1) t) (D i)`. Establish `hτc : ∀ (t : ℕ) (i : I) (k : H.ι), GlobalTheory.LB.coord (τ t i) k = rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k) ((s i.1).f k) ^ t` using `fun t i k => (GlobalTheory.LB.coord_ofSec _ _ _).trans (map_pow (rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k)) _ _)`.

Establish `hτ : ∀ (t : ℕ) (i : I) (k : H.ι), IsUnit (GlobalTheory.LB.coord (τ t i) k)` using `fun t i k => (hτc t i k).symm ▸ (hu i k).pow t`. Establish `hτv : ∀ (t : ℕ) (i : I), secVal (M` using `pw H t) (k₀ := k₀) h₀ (hη i) (τ t i) = ρ i ^ t := fun t i => (congrArg (toField (generic_inf (hη i) h₀)) (hτc t i k₀)).trans (by`. Rewrite using `[map_pow, toField_rs])`. Establish `h₀' : ∀ t : ℕ, genericPoint X' ∈ ((pw H t).pull φ).U fun _ => k₀` using `fun t => le_pull (pw H t) φ (i := k₀) le_rfl (generic_mem_preimage φ h₀)`. Use `finrank_sandwich e (fun i => (toField (hη i)).range) (fun i => (toField (generic_mem_preimage φ (hη i))).range) ρ c hρ hc0 (fun i k => ⟨_, (hρr i k).symm⟩) (fun i k => ?_) ?_ hc₁ hc₂ (fun t => SecOnR f (pw H t) ⊤) (fun t => SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) hV hW (fun t => secV …` and prove the remaining obligations.

Take `⟨a, ha⟩` from `hcm i`. Rewrite using `[← ha, hρr]`. Conclude with `exists_mul_pow_mem (haff k.1) (hη k) (hη i) _ (hρr i k ▸ div_ne_zero (hρ i) (hρ k)) (basicOpen_le_nonzeroLocus _ _ _ (hr k.1 i.1)) a`. Introduce and unpack `i _ ⟨a, rfl⟩`. Conclude with `⟨_, toField_appLE φ le_rfl (hη i) _ a⟩`.

Use `(exists_secVal_eq_iff (M := pw H t) (k₀ := k₀) h₀ (isLB_pw hH t) D hc hη (τ t) (hτ t) x).trans ?_` and prove the remaining obligations. Simplify using `only [hτv]`. Use `(exists_secVal_eq_iff (h₀' t) (LB.isLB_pull (isLB_pw hH t) φ) (fun i => φ ⁻¹ᵁ D i) hc' (fun i => generic_mem_preimage φ (hη i)) (fun i => SecOn.pull (pw H t) φ (D i) (τ t i)) (fun i k => (hτ t i (k PUnit.unit)).map _) y).trans ?_` and prove the remaining obligations. Use `forall_congr' fun i => ?_` and prove the remaining obligations. Rewrite using `[secVal_pull (M := pw H t) (k₀ := k₀) h₀ φ (hη i), hτv]`.

Both sides reduce to the same expression.
-/
theorem finrank_sec_pull_sandwich : ∀ (K : Type) [Field K] (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (f : X ⟶ Spec (CommRingCat.of K)) (φ : X' ⟶ X) [IsFinite φ] [Etale φ] (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ d : ℕ, (∀ x : X, φ.finrank x = d) → (∀ t : ℕ, Module.Finite K (SecOnR f (pw H t) ⊤)) → (∀ t : ℕ, Module.Finite K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤)) → ∃ a : ℕ, ∀ t : ℕ, d * Module.finrank K (SecOnR (f) (pw H t) ⊤) ≤ Module.finrank K (SecOnR (φ ≫ f) ((pw H (t + a : ℕ)).pull φ) ⊤) ∧ Module.finrank K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) ≤ d * Module.finrank K (SecOnR (f) (pw H (t + a : ℕ)) ⊤) := by
  intro K _ X X' _ _ f φ _ _ H n s hH hs d hd hV hW
  have hd1 : 1 ≤ d := hd _ ▸ φ.one_le_finrank_map (genericPoint X')
  haveI : Surjective φ := φ.one_le_finrank_iff_surjective.1 fun x => (hd x).symm ▸ hd1
  letI : Algebra X.functionField X'.functionField := (functionFieldMap φ).toAlgebra
  letI : Algebra K X.functionField := ((toField generic_top).comp (cst f ⊤)).toAlgebra
  letI : Algebra K X'.functionField := ((toField generic_top).comp (cst (φ ≫ f) ⊤)).toAlgebra
  haveI : IsScalarTower K X.functionField X'.functionField :=
    IsScalarTower.of_algebraMap_eq fun r => by
      have w : φ ≫ f = (φ ≫ f) ≫ Spec.map (CommRingCat.ofHom (RingHom.id K)) := by simp
      have e := toField_appLE φ (U := ⊤) (V := ⊤) le_top generic_top generic_top (cst f ⊤ r)
      exact (congrArg (toField generic_top)
        (appLE_cst w (V := ⊤) (V' := ⊤) le_top r)).symm.trans e
  obtain ⟨hcov, hs⟩ := hs
  choose haff r hr _ using hs
  let I := {i // genericPoint X ∈ nonzeroLocus (s i)}
  haveI : Fintype I := Fintype.ofFinite I
  let D : I → X.Opens := fun i => nonzeroLocus (s i.1)
  have hη : ∀ i, genericPoint X ∈ D i := fun i => i.2
  have hc : ⊤ ≤ ⨆ i, D i := fun x hx => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, generic_mem hi⟩, hi⟩
  have hc' : ⊤ ≤ ⨆ i, φ ⁻¹ᵁ D i := fun x _ => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc (trivial : φ x ∈ ⊤))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  obtain ⟨i₀, -⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc generic_top)
  obtain ⟨k₀, h₀⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge generic_top)
  obtain ⟨x, hx⟩ := (chart_data φ (fun _ => rfl) (haff i₀.1) (hη i₀)).1
  rw [hd] at hx
  haveI : Module.Finite X.functionField X'.functionField :=
    Module.finite_of_finrank_pos (by omega)
  let e := Module.finBasisOfFinrankEq _ _ hx
  choose c hcm hc0 hc₁ hc₂ using fun i : I =>
    (chart_data φ (fun _ => rfl) (haff i.1) (hη i)).2 e
  let ρ : I → X.functionField := fun i => toField h₀ ((s i.1).f k₀)
  have hu : ∀ (i : I) k, IsUnit (rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k) ((s i.1).f k)) :=
    fun i k => SecOn.isUnit_rs_of_le_nonzeroLocus _ k _ inf_le_left
  have hρ : ∀ i, ρ i ≠ 0 := fun i => by
    have := ((hu i k₀).map (toField (generic_inf (hη i) h₀))).ne_zero
    rwa [toField_rs] at this
  have hρr : ∀ i k : I, ρ i / ρ k = toField (hη k) (r k.1 i.1) := fun i k => by
    have := congrArg (toField (generic_inf (hη k) h₀)) (hr k.1 i.1 k₀)
    rw [map_mul, toField_rs, toField_rs, toField_rs] at this
    exact (div_eq_iff (hρ k)).2 this
  let τ : ∀ (t : ℕ) (i : I), SecOn (pw H t) (D i) := fun t i => GlobalTheory.LB.ofSec (powSec (s i.1) t) (D i)
  have hτc : ∀ (t : ℕ) (i : I) (k : H.ι), GlobalTheory.LB.coord (τ t i) k =
      rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k) ((s i.1).f k) ^ t := fun t i k =>
    (GlobalTheory.LB.coord_ofSec _ _ _).trans (map_pow (rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k)) _ _)
  have hτ : ∀ (t : ℕ) (i : I) (k : H.ι), IsUnit (GlobalTheory.LB.coord (τ t i) k) := fun t i k =>
    (hτc t i k).symm ▸ (hu i k).pow t
  have hτv : ∀ (t : ℕ) (i : I), secVal (M := pw H t) (k₀ := k₀) h₀ (hη i) (τ t i) = ρ i ^ t :=
    fun t i => (congrArg (toField (generic_inf (hη i) h₀)) (hτc t i k₀)).trans (by
      rw [map_pow, toField_rs])
  have h₀' : ∀ t : ℕ, genericPoint X' ∈ ((pw H t).pull φ).U fun _ => k₀ := fun t =>
    le_pull (pw H t) φ (i := k₀) le_rfl (generic_mem_preimage φ h₀)
  refine finrank_sandwich e (fun i => (toField (hη i)).range)
    (fun i => (toField (generic_mem_preimage φ (hη i))).range) ρ c hρ hc0
    (fun i k => ⟨_, (hρr i k).symm⟩) (fun i k => ?_) ?_ hc₁ hc₂
    (fun t => SecOnR f (pw H t) ⊤) (fun t => SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) hV hW
    (fun t => secValLin (M := pw H t) (k₀ := k₀) h₀ f fun _ => rfl)
    (fun t => secValLin (h₀' t) (φ ≫ f) fun _ => rfl)
    (fun t => secVal_injective (M := pw H t) (k₀ := k₀) h₀ generic_top)
    (fun t => secVal_injective (h₀' t) generic_top) (fun t x => ?_) fun t y => ?_
  · obtain ⟨a, ha⟩ := hcm i
    rw [← ha, hρr]
    exact exists_mul_pow_mem (haff k.1) (hη k) (hη i) _
      (hρr i k ▸ div_ne_zero (hρ i) (hρ k)) (basicOpen_le_nonzeroLocus _ _ _ (hr k.1 i.1)) a
  · rintro i _ ⟨a, rfl⟩
    exact ⟨_, toField_appLE φ le_rfl (hη i) _ a⟩
  · refine (exists_secVal_eq_iff (M := pw H t) (k₀ := k₀) h₀ (isLB_pw hH t) D hc hη (τ t) (hτ t)
      x).trans ?_
    simp only [hτv]
  · refine (exists_secVal_eq_iff (h₀' t) (LB.isLB_pull (isLB_pw hH t) φ) (fun i => φ ⁻¹ᵁ D i) hc'
      (fun i => generic_mem_preimage φ (hη i)) (fun i => SecOn.pull (pw H t) φ (D i) (τ t i))
      (fun i k => (hτ t i (k PUnit.unit)).map _) y).trans ?_
    refine forall_congr' fun i => ?_
    rw [secVal_pull (M := pw H t) (k₀ := k₀) h₀ φ (hη i), hτv]
    rfl

end GlobalTheory
