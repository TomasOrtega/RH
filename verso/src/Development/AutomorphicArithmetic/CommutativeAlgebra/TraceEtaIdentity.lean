import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSimilitudeOfLevel

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open scoped TensorProduct

/- English proof (translation)
Establish `key : ∀ q : X, ∃ V : X.Opens, q ∈ V ∧ V.ι ≫ σ.left = V.ι ≫ σ'.left`. Introduce `q`. Take `⟨k, hk, y, ⟨z, hz⟩, he⟩` from `hpt q`. Take `⟨V, hV, hVe⟩` from `GlobalTheory.UPel.LocSim.exists_open_eq_of_torsion_point X A hA n hn σ σ' h₁ h₂ k y he`. Conclude with `⟨V, hV ⟨z, hz⟩, hVe⟩`.

Use `choose V hV hVe using key`. Establish `hcov : TopologicalSpace.IsOpenCover V`. Use `TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr fun q _ => ?_)` and prove the remaining obligations. Conclude with `TopologicalSpace.Opens.mem_iSup.mpr ⟨q, hV q⟩`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Conclude with `Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover V hcov) _ _ fun q => hVe q`.
-/
private theorem sec_eq_of_points {X : Scheme.{0}} (A : Over X) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (n : ℕ) (hn : IsUnit (n : Γ(X, ⊤))) (σ σ' : 𝟙_ (Over X) ⟶ A) (h₁ : σ ^ n = 1) (h₂ : σ' ^ n = 1)
    (hpt : ∀ q : X, ∃ (k : Type) (_ : Field k) (y : Sp k ⟶ X), q ∈ Set.range y ∧
      toUnit (Over.mk y) ≫ σ = toUnit (Over.mk y) ≫ σ') : σ = σ' := by
  have key : ∀ q : X, ∃ V : X.Opens, q ∈ V ∧ V.ι ≫ σ.left = V.ι ≫ σ'.left := by
    intro q
    obtain ⟨k, hk, y, ⟨z, hz⟩, he⟩ := hpt q
    obtain ⟨V, hV, hVe⟩ := GlobalTheory.UPel.LocSim.exists_open_eq_of_torsion_point X A hA n hn σ σ' h₁ h₂ k y he
    exact ⟨V, hV ⟨z, hz⟩, hVe⟩
  choose V hV hVe using key
  have hcov : TopologicalSpace.IsOpenCover V := by
    refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr fun q _ => ?_)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨q, hV q⟩
  apply Over.OverMorphism.ext
  exact Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover V hcov) _ _ fun q => hVe q

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Rewrite using `[zero_nsmul, pow_zero]`. Establish `h` using `hf 0 0`. Rewrite `h` using `[add_zero]`.

Conclude with `mul_left_cancel (a := f 0) (by rw [_root_.mul_one]; exact h.symm)`. Consider the case `succ m ih`. Rewrite using `[succ_nsmul, hf, ih, pow_succ]`.
-/
private theorem map_nsmul_pow {M Q : Type} [AddCommGroup M] [Group Q] (f : M → Q) (hf : ∀ a b, f (a + b) = f a * f b)
    (m : ℕ) (a : M) : f (m • a) = f a ^ m := by
  induction m with
  | zero =>
    rw [zero_nsmul, pow_zero]
    have h := hf 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := f 0) (by rw [_root_.mul_one]; exact h.symm)
  | succ m ih =>
    rw [succ_nsmul, hf, ih, pow_succ]

/- English proof (translation)
The claim follows from `(map_pow (IsMonHom.monoidHom ψ T) a m).symm`.
-/
private theorem pow_comp_hom {C : Type*} [Category C] [CartesianMonoidalCategory C] {T A B : C} [GrpObj A] [GrpObj B]
    (a : T ⟶ A) (ψ : A ⟶ B) [IsMonHom ψ] (m : ℕ) : (a ≫ ψ) ^ m = (a ^ m) ≫ ψ := (map_pow (IsMonHom.monoidHom ψ T) a m).symm

/- English proof (translation)
Substitute `hM` using the available equality. Rewrite using `[map_nsmul_pow (I.ev _) (I.add _)]`. Conclude with `I.tower n c hn hc z`.
-/
private theorem ev_tower {G : GDatum} {k Q : Type} [Field k] [Group Q] {act : G.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (I : GTateIso G k Q act e) {M n c : ℕ} (hM : M = n * c) (hn : 0 < n) (hc : 0 < c) (z : G.La) :
    I.ev M (c • z) = I.ev n z := by
  subst hM
  rw [map_nsmul_pow (I.ev _) (I.add _)]
  exact I.tower n c hn hc z

/- English proof (translation)
Introduce `p _ D G L R _ _ gb h X s N' N o' o ψ hT n c' c hN' hN x y hxy`. Use `haveI : IsMonHom ψ := hT.1`. Establish `h3'` using `N'.2.1`. Establish `h3` using `N.2.1`. Establish `hn : 0 < n` using `Nat.pos_of_ne_zero (by rintro rfl; rw [zero_mul] at hN'; omega)`.

Establish `hc' : 0 < c'` using `Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hN'; omega)`. Establish `hc : 0 < c` using `Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hN; omega)`. Establish `hcop : n.Coprime p` using `Nat.Coprime.coprime_dvd_left ⟨c', hN'⟩ N'.2.2`. Establish `hunit : IsUnit (n : Γ(X, ⊤))`. Establish `hR : IsUnit (n : R)`.

Establish `hq : IsUnit (n : ℚ)` using `(Nat.cast_ne_zero.mpr hn.ne').isUnit`. Simplify using `using hq.map (algebraMap ℚ R)`. Use `hR.map ((s.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)` as an intermediate fact. Simplify using `using this`. Establish `ex' : (n • c' • x : D.La) = (↑N' : ℕ) • x` using `by rw [smul_smul, ← hN']`.

Establish `ex : (n • c • y : D.La) = (↑N : ℕ) • y` using `by rw [smul_smul, ← hN]`. Establish `e1 : (o'.eta (c' • x)) ^ n = 1` using `(map_nsmul_pow o'.eta o'.eta_add n (c' • x)).symm.trans ((congrArg o'.eta ex').trans (o'.eta_ker x))`. Establish `hpow1 : (o'.eta (c' • x) ≫ ψ) ^ n = 1` using `(pow_comp_hom _ _ _).trans ((congrArg (· ≫ ψ) e1).trans (map_one (IsMonHom.monoidHom ψ _)))`. Establish `hpow2 : (o.eta (c • y)) ^ n = 1` using `(map_nsmul_pow o.eta o.eta_add n (c • y)).symm.trans ((congrArg o.eta ex).trans (o.eta_ker y))`. Use `sec_eq_of_points o.A o.ab n hunit _ _ hpow1 hpow2 (fun q => ?_)` and prove the remaining obligations.

Set `κ` to `X.residueField q`. Set `k` to `AlgebraicClosure κ`. Set `y0 : Sp k ⟶ X` to `spMap (algebraMap κ k) ≫ X.fromSpecResidueField q`. Set `β : R →+* k` to `(Spec.preimage (y0 ≫ s)).hom`. Establish `hβ : y0 ≫ s = spMap β` using `by show _ = Spec.map (CommRingCat.ofHom (Spec.preimage (y0 ≫ s)).hom)`.

Rewrite using `[CommRingCat.ofHom_hom, Spec.map_preimage]`. Take `⟨I', I'', hI', hI'', hiff⟩` from `hT.2.2.2.2 k y0 β hβ`. Use `⟨k, inferInstance, y0, ⟨IsLocalRing.closedPoint k, Scheme.fromSpecResidueField_apply q _⟩, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.trace_eta_identity : UpperTheory.Gal.Int.Geo.TrEta := by
  intro p _ D G L R _ _ gb h X s N' N o' o ψ hT n c' c hN' hN x y hxy
  haveI : IsMonHom ψ := hT.1
  have h3' := N'.2.1
  have h3 := N.2.1
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; rw [zero_mul] at hN'; omega)
  have hc' : 0 < c' := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hN'; omega)
  have hc : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hN; omega)
  have hcop : n.Coprime p := Nat.Coprime.coprime_dvd_left ⟨c', hN'⟩ N'.2.2
  have hunit : IsUnit (n : Γ(X, ⊤)) := by
    have hR : IsUnit (n : R) := by
      have hq : IsUnit (n : ℚ) := (Nat.cast_ne_zero.mpr hn.ne').isUnit
      simpa using hq.map (algebraMap ℚ R)
    have := hR.map ((s.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    simpa using this
  have ex' : (n • c' • x : D.La) = (↑N' : ℕ) • x := by rw [smul_smul, ← hN']
  have ex : (n • c • y : D.La) = (↑N : ℕ) • y := by rw [smul_smul, ← hN]
  have e1 : (o'.eta (c' • x)) ^ n = 1 :=
    (map_nsmul_pow o'.eta o'.eta_add n (c' • x)).symm.trans ((congrArg o'.eta ex').trans (o'.eta_ker x))
  have hpow1 : (o'.eta (c' • x) ≫ ψ) ^ n = 1 :=
    (pow_comp_hom _ _ _).trans ((congrArg (· ≫ ψ) e1).trans (map_one (IsMonHom.monoidHom ψ _)))
  have hpow2 : (o.eta (c • y)) ^ n = 1 :=
    (map_nsmul_pow o.eta o.eta_add n (c • y)).symm.trans ((congrArg o.eta ex).trans (o.eta_ker y))
  refine sec_eq_of_points o.A o.ab n hunit _ _ hpow1 hpow2 (fun q => ?_)
  let κ := X.residueField q
  let k := AlgebraicClosure κ
  let y0 : Sp k ⟶ X := spMap (algebraMap κ k) ≫ X.fromSpecResidueField q
  let β : R →+* k := (Spec.preimage (y0 ≫ s)).hom
  have hβ : y0 ≫ s = spMap β := by
    show _ = Spec.map (CommRingCat.ofHom (Spec.preimage (y0 ≫ s)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  obtain ⟨I', I'', hI', hI'', hiff⟩ := hT.2.2.2.2 k y0 β hβ
  refine ⟨k, inferInstance, y0, ⟨IsLocalRing.closedPoint k, Scheme.fromSpecResidueField_apply q _⟩, ?_⟩
  calc toUnit (Over.mk y0) ≫ (o'.eta (c' • x) ≫ ψ)
      = (toUnit (Over.mk y0) ≫ o'.eta (c' • x)) ≫ ψ := (Category.assoc _ _ _).symm
    _ = I'.ev (↑N') (c' • x) ≫ ψ := congrArg (· ≫ ψ) (hI' _)
    _ = I'.ev n x ≫ ψ := congrArg (· ≫ ψ) (ev_tower I' hN' hn hc' x)
    _ = I''.ev n y := (hiff n hn hcop x y).mpr hxy
    _ = I''.ev (↑N) (c • y) := (ev_tower I'' hN hn hc y).symm
    _ = toUnit (Over.mk y0) ≫ o.eta (c • y) := (hI'' _).symm
