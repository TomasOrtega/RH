import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionPrechartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPrechartGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionKernelFinitePresentationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartIsLocalizationAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfEvalEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionMemOpenShrink
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsGlueAway
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff.LevelOpen

variable {R : Type} [CommRing R]

/- English proof (translation)
Use `letI := α.toRingHom.toAlgebra`. Conclude with `IsLocalization.Away.algebraMap_isUnit (S := C) e`.
-/
theorem alg_away_unit {A C : Type} [CommRing A] [CommRing C] [Algebra R A] [Algebra R C] (α : A →ₐ[R] C) (e : A)
    (h : @IsLocalization.Away A _ e C _ α.toRingHom.toAlgebra) : IsUnit (α e) := by
  letI := α.toRingHom.toAlgebra
  exact IsLocalization.Away.algebraMap_isUnit (S := C) e

/- English proof (translation)
Use `letI := α.toRingHom.toAlgebra`. Establish `hU : ∀ y : Submonoid.powers e, IsUnit ((φ : A →+* B) y)`. Introduce and unpack `⟨_, n, rfl⟩`. Simplify using `using hu.pow n`. Set `g : C →+* B` to `IsLocalization.lift (M := Submonoid.powers e) hU`.

Establish `hg : ∀ a, g (α a) = φ a` using `fun a => IsLocalization.lift_eq hU a`. Use `⟨{ g with commutes' := fun r => ?_ }, AlgHom.ext hg⟩` and prove the remaining obligations. Use `show g (algebraMap R C r) = algebraMap R B r`. Rewrite using `[← α.commutes r, hg, φ.commutes]`.
-/
theorem alg_away_lift {A C B : Type} [CommRing A] [CommRing C] [CommRing B] [Algebra R A] [Algebra R C] [Algebra R B]
    (α : A →ₐ[R] C) (e : A) (h : @IsLocalization.Away A _ e C _ α.toRingHom.toAlgebra) (φ : A →ₐ[R] B)
    (hu : IsUnit (φ e)) : ∃ ψ : C →ₐ[R] B, ψ.comp α = φ := by
  letI := α.toRingHom.toAlgebra
  have hU : ∀ y : Submonoid.powers e, IsUnit ((φ : A →+* B) y) := by
    rintro ⟨_, n, rfl⟩
    simpa using hu.pow n
  let g : C →+* B := IsLocalization.lift (M := Submonoid.powers e) hU
  have hg : ∀ a, g (α a) = φ a := fun a => IsLocalization.lift_eq hU a
  refine ⟨{ g with commutes' := fun r => ?_ }, AlgHom.ext hg⟩
  show g (algebraMap R C r) = algebraMap R B r
  rw [← α.commutes r, hg, φ.commutes]

/- English proof (translation)
Use `letI := α.toRingHom.toAlgebra`. Establish `: (ψ : C →+* B) = ψ'` using `IsLocalization.ringHom_ext (Submonoid.powers e) (RingHom.ext fun a => congrArg (· a) hψ)`. Conclude with `AlgHom.ext fun x => congrArg (· x) this`.
-/
theorem alg_away_ext {A C B : Type} [CommRing A] [CommRing C] [CommRing B] [Algebra R A] [Algebra R C] [Algebra R B]
    (α : A →ₐ[R] C) (e : A) (h : @IsLocalization.Away A _ e C _ α.toRingHom.toAlgebra) (ψ ψ' : C →ₐ[R] B)
    (hψ : ψ.comp α = ψ'.comp α) : ψ = ψ' := by
  letI := α.toRingHom.toAlgebra
  have : (ψ : C →+* B) = ψ' := IsLocalization.ringHom_ext (Submonoid.powers e) (RingHom.ext fun a => congrArg (· a) hψ)
  exact AlgHom.ext fun x => congrArg (· x) this

/- English proof (translation)
Establish `hn : ∀ i, ∃ n : ℕ, b i ^ n * x = 0` using `fun i => by`. Take `⟨⟨_, n, rfl⟩, h⟩` from `(IsLocalization.map_eq_zero_iff (Submonoid.powers (b i)) (Localization.Away (b i)) x).1 (hx i)`. Conclude with `⟨n, h⟩`. Use `choose n hn using hn`. Establish `hle : Ideal.span (Set.range fun i => b i ^ n i) ≤ (Submodule.span B {x}).annihilator`.

Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `(Submodule.mem_annihilator_span_singleton x _).2 (by simpa [smul_eq_mul] using hn i)`. Assume the negation of the conclusion as `hx0`. Establish `hJ : (Submodule.span B {x}).annihilator ≠ ⊤` using `fun h => hx0 (by`.

Establish `h1` using `(Submodule.mem_annihilator_span_singleton x (1 : B)).1 (h ▸ Submodule.mem_top)`. Rewrite using `[one_smul] at h1)` and apply the resulting hypothesis. Take `⟨M, hM, hJM⟩` from `Ideal.exists_le_maximal _ hJ`. Establish `hbM : Ideal.span (Set.range b) ≤ M`. Rewrite using `[Ideal.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hM.isPrime.mem_of_pow_mem (n i) (hJM (hle (Ideal.subset_span ⟨i, rfl⟩)))`. Conclude with `hM.ne_top (top_le_iff.1 (hb ▸ hbM))`.
-/
theorem eq_zero_of_away_span {B : Type} [CommRing B] {Idx : Type} (b : Idx → B) (hb : Ideal.span (Set.range b) = ⊤) (x : B)
    (hx : ∀ i, algebraMap B (Localization.Away (b i)) x = 0) : x = 0 := by
  have hn : ∀ i, ∃ n : ℕ, b i ^ n * x = 0 := fun i => by
    obtain ⟨⟨_, n, rfl⟩, h⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (b i)) (Localization.Away (b i)) x).1 (hx i)
    exact ⟨n, h⟩
  choose n hn using hn
  have hle : Ideal.span (Set.range fun i => b i ^ n i) ≤ (Submodule.span B {x}).annihilator := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact (Submodule.mem_annihilator_span_singleton x _).2 (by simpa [smul_eq_mul] using hn i)
  by_contra hx0
  have hJ : (Submodule.span B {x}).annihilator ≠ ⊤ := fun h =>
    hx0 (by
      have h1 := (Submodule.mem_annihilator_span_singleton x (1 : B)).1 (h ▸ Submodule.mem_top)
      rwa [one_smul] at h1)
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal _ hJ
  have hbM : Ideal.span (Set.range b) ≤ M := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hM.isPrime.mem_of_pow_mem (n i) (hJM (hle (Ideal.subset_span ⟨i, rfl⟩)))
  exact hM.ne_top (top_le_iff.1 (hb ▸ hbM))

end GlobalTheory.GroupBplus.Aff.LevelOpen

open GlobalTheory.GroupBplus.Aff.LevelOpen in

/- English proof (translation)
Introduce `R K _ _ _ _ _ _ _ _ G _ _ hG N hN A _ _ _ _ _ io θ hθ`. Establish `hc : ∀ q : PrimeSpectrum R, PreChart G N q` using `fun q => (GlobalTheory.T.exists_torsion_prechart R K G hG N hN q).some`. Use `choose e he using fun q => GlobalTheory.ChartLocAway.chart_isLocalization_away R K G hG N hN A io θ hθ q (hc q) (GlobalTheory.T.torsion_prechart_group R K G hG N hN q (hc q))`. Establish `hker : ∀ (B : Type) [CommRing B] [Algebra R B] (P : PrimeSpectrum B), RingHom.ker (algebraMap R P.asIdeal.ResidueField) = (PrimeSpectrum.comap (algebraMap R B) P).asIdeal`. Introduce `B _ _ P`.

Use extensionality with `x`. Rewrite using `[RingHom.mem_ker, IsScalarTower.algebraMap_apply R B P.asIdeal.ResidueField, Ideal.algebraMap_residueField_eq_zero]`. Both sides reduce to the same expression. Establish `hmaps : ∀ (B : Type) [CommRing B] [Algebra R B] (z : Tors G N B) (P : PrimeSpectrum B), θ.pt B z (e (PrimeSpectrum.comap (algebraMap R B) P)) ∉ P.asIdeal`. Introduce `B _ _ z P hmem`.

Use `set q := PrimeSpectrum.comap (algebraMap R B) P`. Use `set k := P.asIdeal.ResidueField`. Use `set t := IsScalarTower.toAlgHom R B k`. Take `⟨ψ, -, hψ⟩` from `((hc q).bij k).2.2 ((hc q).fibre k (hker B P) (torsMap t z))`. Establish `e1 : t.comp (θ.pt B z) = ψ.comp (θ.pt (hc q).C (hc q).j)` using `(θ.nat B k t z).symm.trans ((congrArg (θ.pt k) hψ.symm).trans (θ.nat _ k ψ _))`.

Establish `h0 : t (θ.pt B z (e q)) = 0` using `Ideal.algebraMap_residueField_eq_zero.2 hmem`. Rewrite `h0` using `[← AlgHom.comp_apply, e1, AlgHom.comp_apply]`. Conclude with `((alg_away_unit _ _ (he q)).map ψ).ne_zero h0`. Establish `hinj : ∀ (B : Type) [CommRing B] [Algebra R B] (z z' : Tors G N B), θ.pt B z = θ.pt B z' → z = z'`. Introduce `B _ _ z z' h`.

Use `GlobalTheory.T.torsion_points_eq_of_local R G N B z z' fun P => ?_` and prove the remaining obligations. Use `set q := PrimeSpectrum.comap (algebraMap R B) P`. Take `⟨f1, hf1, h1⟩` from `GlobalTheory.GroupBplus.Aff.torsion_mem_open_shrink R G N B z (hc q).W P ((hc q).fibre _ (hker B P) _)`. Take `⟨f2, hf2, h2⟩` from `GlobalTheory.GroupBplus.Aff.torsion_mem_open_shrink R G N B z' (hc q).W P ((hc q).fibre _ (hker B P) _)`. Use `⟨f1 * f2, fun hm => (P.isPrime.mem_or_mem hm).elim hf1 hf2, ?_⟩` and prove the remaining obligations.

Use `set L := Localization.Away (f1 * f2)`. Use `set t := IsScalarTower.toAlgHom R B L`. Take `⟨ψ, -, hψ⟩` from `((hc q).bij L).2.2 (h1 _ (dvd_mul_right f1 f2))`. Take `⟨ψ', -, hψ'⟩` from `((hc q).bij L).2.2 (h2 _ (dvd_mul_left f2 f1))`. Establish `hcomp : ψ.comp (θ.pt (hc q).C (hc q).j) = ψ'.comp (θ.pt (hc q).C (hc q).j)` using `(θ.nat _ L ψ _).symm.trans ((congrArg (θ.pt L) hψ).trans ((θ.nat B L t z).trans ((congrArg (AlgHom.comp t) h).trans ((θ.nat B L t z').symm.trans ((congrArg (θ.pt L) hψ'.symm).trans (θ.nat _ L ψ' _))))))`.

Rewrite using `[← hψ, ← hψ', alg_away_ext _ _ (he q) ψ ψ' hcomp]`. Establish `hsurj : ∀ (B : Type) [CommRing B] [Algebra R B] (φ : A →ₐ[R] B), (∀ P : PrimeSpectrum B, ∃ q, φ (e q) ∉ P.asIdeal) → ∃ z : Tors G N B, θ.pt B z = φ`. Introduce `B _ _ φ hφ`. Establish `hspan : Ideal.span (Set.range fun q => φ (e q)) = ⊤`. Assume the negation of the conclusion as `hne`.

Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal _ hne`. Take `⟨q, hq⟩` from `hφ ⟨M, hM.isPrime⟩`. Conclude with `hq (hle (Ideal.subset_span ⟨q, rfl⟩))`. Establish `hl : ∀ q, ∃ ψ : (hc q).C →ₐ[R] Localization.Away (φ (e q)), ψ.comp (θ.pt (hc q).C (hc q).j) = (IsScalarTower.toAlgHom R B _).comp φ` using `fun q => alg_away_lift _ _ (he q) _ (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (φ (e q))) (φ (e q)))`. Use `choose ψ hψ using hl`.

Take `⟨w, hw⟩` from `GlobalTheory.GroupBplus.Aff.tors_glue_away R G N B (PrimeSpectrum R) (fun q => φ (e q)) hspan (fun q => torsMap (ψ q) (hc q).j) (by`. Introduce `q q' D _ _ u v huv`. Apply `hinj` to reduce the goal to its premises. Simplify using `only [θ.nat, hψ]`. Rewrite using `[← AlgHom.comp_assoc, ← AlgHom.comp_assoc, huv])`.

Use `⟨w, AlgHom.ext fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_away_span _ hspan _ fun q => ?_` and prove the remaining obligations. Establish `hq : (IsScalarTower.toAlgHom R B (Localization.Away (φ (e q)))).comp (θ.pt B w) = (IsScalarTower.toAlgHom R B (Localization.Away (φ (e q)))).comp φ` using `(θ.nat B _ _ w).symm.trans ((congrArg (θ.pt _) (hw q)).trans ((θ.nat _ _ (ψ q) _).trans (hψ q)))`. Rewrite using `[map_sub, sub_eq_zero]`.

Conclude with `congrArg (· a) hq`. Set `V : (Sp A).Opens` to `⨆ q, PrimeSpectrum.basicOpen (e q)`. Establish `hV : ∀ (B : Type) [CommRing B] [Algebra R B] (φ : A →ₐ[R] B), Set.range (spMap (φ : A →+* B)) ⊆ (V : Set (Sp A)) ↔ ∀ P : PrimeSpectrum B, ∃ q, φ (e q) ∉ P.asIdeal`. Introduce `B _ _ φ`. Prove the components needed by the constructor for the conclusion.

Introduce `h P`. Take `⟨q, hq⟩` from `TopologicalSpace.Opens.mem_iSup.1 (h ⟨P, rfl⟩)`. Conclude with `⟨q, hq⟩`. Introduce and unpack `h _ ⟨P, rfl⟩`. Take `⟨q, hq⟩` from `h P`.

Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨q, hq⟩`. Use `⟨⟨V, fun B _ _ => ⟨fun z _ => (hV B _).2 fun P => ⟨_, hmaps B z P⟩, fun z _ z' _ h => hinj B z z' h, fun φ hφ => ?_⟩⟩, ⟨fun x y h => hinj K x y h, (GlobalTheory.GroupBplus.Aff.OrdGen.pt_bijective R K G hG N hN A io θ hθ).2⟩⟩` and prove the remaining obligations. Take `⟨z, hz⟩` from `hsurj B φ ((hV B φ).1 hφ)`. Conclude with `⟨z, trivial, hz⟩`.
-/
theorem GlobalTheory.GroupBplus.Aff.isLevel_of_ord : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → ∀ (A : Type) [CommRing A] [HopfAlgebra R A] [IsCocomm R A] [Module.Finite R A] [Module.Projective R A] (io : A ≃ₐ[R] ord G N K) (θ : TorsPt G N A), (∀ (x : Tors G N K) (a : A), θ.pt K x a = (io a : Tors G N K → K) x) → IsLevel K θ := by
  intro R K _ _ _ _ _ _ _ _ G _ _ hG N hN A _ _ _ _ _ io θ hθ
  have hc : ∀ q : PrimeSpectrum R, PreChart G N q := fun q => (GlobalTheory.T.exists_torsion_prechart R K G hG N hN q).some
  choose e he using fun q => GlobalTheory.ChartLocAway.chart_isLocalization_away R K G hG N hN A io θ hθ q (hc q) (GlobalTheory.T.torsion_prechart_group R K G hG N hN q (hc q))
  have hker : ∀ (B : Type) [CommRing B] [Algebra R B] (P : PrimeSpectrum B),
      RingHom.ker (algebraMap R P.asIdeal.ResidueField) = (PrimeSpectrum.comap (algebraMap R B) P).asIdeal := by
    intro B _ _ P
    ext x
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply R B P.asIdeal.ResidueField, Ideal.algebraMap_residueField_eq_zero]
    rfl
  have hmaps : ∀ (B : Type) [CommRing B] [Algebra R B] (z : Tors G N B) (P : PrimeSpectrum B),
      θ.pt B z (e (PrimeSpectrum.comap (algebraMap R B) P)) ∉ P.asIdeal := by
    intro B _ _ z P hmem
    set q := PrimeSpectrum.comap (algebraMap R B) P
    set k := P.asIdeal.ResidueField
    set t := IsScalarTower.toAlgHom R B k
    obtain ⟨ψ, -, hψ⟩ := ((hc q).bij k).2.2 ((hc q).fibre k (hker B P) (torsMap t z))
    have e1 : t.comp (θ.pt B z) = ψ.comp (θ.pt (hc q).C (hc q).j) :=
      (θ.nat B k t z).symm.trans ((congrArg (θ.pt k) hψ.symm).trans (θ.nat _ k ψ _))
    have h0 : t (θ.pt B z (e q)) = 0 := Ideal.algebraMap_residueField_eq_zero.2 hmem
    rw [← AlgHom.comp_apply, e1, AlgHom.comp_apply] at h0
    exact ((alg_away_unit _ _ (he q)).map ψ).ne_zero h0
  have hinj : ∀ (B : Type) [CommRing B] [Algebra R B] (z z' : Tors G N B), θ.pt B z = θ.pt B z' → z = z' := by
    intro B _ _ z z' h
    refine GlobalTheory.T.torsion_points_eq_of_local R G N B z z' fun P => ?_
    set q := PrimeSpectrum.comap (algebraMap R B) P
    obtain ⟨f1, hf1, h1⟩ := GlobalTheory.GroupBplus.Aff.torsion_mem_open_shrink R G N B z (hc q).W P ((hc q).fibre _ (hker B P) _)
    obtain ⟨f2, hf2, h2⟩ := GlobalTheory.GroupBplus.Aff.torsion_mem_open_shrink R G N B z' (hc q).W P ((hc q).fibre _ (hker B P) _)
    refine ⟨f1 * f2, fun hm => (P.isPrime.mem_or_mem hm).elim hf1 hf2, ?_⟩
    set L := Localization.Away (f1 * f2)
    set t := IsScalarTower.toAlgHom R B L
    obtain ⟨ψ, -, hψ⟩ := ((hc q).bij L).2.2 (h1 _ (dvd_mul_right f1 f2))
    obtain ⟨ψ', -, hψ'⟩ := ((hc q).bij L).2.2 (h2 _ (dvd_mul_left f2 f1))
    have hcomp : ψ.comp (θ.pt (hc q).C (hc q).j) = ψ'.comp (θ.pt (hc q).C (hc q).j) :=
      (θ.nat _ L ψ _).symm.trans ((congrArg (θ.pt L) hψ).trans ((θ.nat B L t z).trans
        ((congrArg (AlgHom.comp t) h).trans ((θ.nat B L t z').symm.trans
        ((congrArg (θ.pt L) hψ'.symm).trans (θ.nat _ L ψ' _))))))
    rw [← hψ, ← hψ', alg_away_ext _ _ (he q) ψ ψ' hcomp]
  have hsurj : ∀ (B : Type) [CommRing B] [Algebra R B] (φ : A →ₐ[R] B),
      (∀ P : PrimeSpectrum B, ∃ q, φ (e q) ∉ P.asIdeal) → ∃ z : Tors G N B, θ.pt B z = φ := by
    intro B _ _ φ hφ
    have hspan : Ideal.span (Set.range fun q => φ (e q)) = ⊤ := by
      by_contra hne
      obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
      obtain ⟨q, hq⟩ := hφ ⟨M, hM.isPrime⟩
      exact hq (hle (Ideal.subset_span ⟨q, rfl⟩))
    have hl : ∀ q, ∃ ψ : (hc q).C →ₐ[R] Localization.Away (φ (e q)),
        ψ.comp (θ.pt (hc q).C (hc q).j) = (IsScalarTower.toAlgHom R B _).comp φ := fun q =>
      alg_away_lift _ _ (he q) _ (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (φ (e q))) (φ (e q)))
    choose ψ hψ using hl
    obtain ⟨w, hw⟩ := GlobalTheory.GroupBplus.Aff.tors_glue_away R G N B (PrimeSpectrum R) (fun q => φ (e q)) hspan
      (fun q => torsMap (ψ q) (hc q).j) (by
        intro q q' D _ _ u v huv
        apply hinj
        simp only [θ.nat, hψ]
        rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, huv])
    refine ⟨w, AlgHom.ext fun a => ?_⟩
    rw [← sub_eq_zero]
    refine eq_zero_of_away_span _ hspan _ fun q => ?_
    have hq : (IsScalarTower.toAlgHom R B (Localization.Away (φ (e q)))).comp (θ.pt B w) =
        (IsScalarTower.toAlgHom R B (Localization.Away (φ (e q)))).comp φ :=
      (θ.nat B _ _ w).symm.trans ((congrArg (θ.pt _) (hw q)).trans ((θ.nat _ _ (ψ q) _).trans (hψ q)))
    rw [map_sub, sub_eq_zero]
    exact congrArg (· a) hq
  let V : (Sp A).Opens := ⨆ q, PrimeSpectrum.basicOpen (e q)
  have hV : ∀ (B : Type) [CommRing B] [Algebra R B] (φ : A →ₐ[R] B),
      Set.range (spMap (φ : A →+* B)) ⊆ (V : Set (Sp A)) ↔ ∀ P : PrimeSpectrum B, ∃ q, φ (e q) ∉ P.asIdeal := by
    intro B _ _ φ
    constructor
    · intro h P
      obtain ⟨q, hq⟩ := TopologicalSpace.Opens.mem_iSup.1 (h ⟨P, rfl⟩)
      exact ⟨q, hq⟩
    · rintro h _ ⟨P, rfl⟩
      obtain ⟨q, hq⟩ := h P
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨q, hq⟩
  refine ⟨⟨V, fun B _ _ => ⟨fun z _ => (hV B _).2 fun P => ⟨_, hmaps B z P⟩,
    fun z _ z' _ h => hinj B z z' h, fun φ hφ => ?_⟩⟩, ⟨fun x y h => hinj K x y h, (GlobalTheory.GroupBplus.Aff.OrdGen.pt_bijective R K G hG N hN A io θ hθ).2⟩⟩
  obtain ⟨z, hz⟩ := hsurj B φ ((hV B φ).1 hφ)
  exact ⟨z, trivial, hz⟩
