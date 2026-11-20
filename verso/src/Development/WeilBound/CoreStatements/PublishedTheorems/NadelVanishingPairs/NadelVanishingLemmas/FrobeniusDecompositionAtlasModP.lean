import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSubsingletonCohTwistTensLbPow
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EtaleCoordinatesLogChartStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FrobeniusDecompositionOfLiftStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LiftedStalkMapGermAppLE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesOnOpenBaseChangePreimage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncChartBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

namespace GlobalTheory.LogAtlas

/- English proof (translation)
Introduce `h0`. Establish `h1 : t j = 0` using `fnOf_injective U h (h0.trans (map_zero _).symm)`. Use `letI := (MvPolynomial.eval₂Hom (cstOn f U) t).toAlgebra`. Establish `: Algebra.Etale (MvPolynomial (Fin n) R) Γ(X, U)` using `ht`. Establish `: Nonempty U` using `⟨⟨_, h⟩⟩`.

Establish `h2` using `Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(X, U)) (mem_nonZeroDivisors_of_ne_zero (MvPolynomial.X_ne_zero (R := R) j))`. Establish `h3 : (MvPolynomial.X j : MvPolynomial (Fin n) R) • (1 : Γ(X, U)) = (MvPolynomial.X j : MvPolynomial (Fin n) R) • (0 : Γ(X, U))`. Rewrite using `[smul_zero, Algebra.smul_def, mul_one]`. Conclude with `(MvPolynomial.eval₂Hom_X' _ _ j).trans h1`. Conclude with `one_ne_zero (h2 h3)`.
-/
theorem fnOf_coord_ne_zero {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} [IsIntegral X]
    {f : X ⟶ Sp R} {U : X.Opens} (h : genericPoint X ∈ U) {n : ℕ} {t : Fin n → Γ(X, U)}
    (ht : IsEtCoord f U t) (j : Fin n) : fnOf U h (t j) ≠ 0 := by
  intro h0
  have h1 : t j = 0 := fnOf_injective U h (h0.trans (map_zero _).symm)
  letI := (MvPolynomial.eval₂Hom (cstOn f U) t).toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin n) R) Γ(X, U) := ht
  have : Nonempty U := ⟨⟨_, h⟩⟩
  have h2 := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(X, U))
      (mem_nonZeroDivisors_of_ne_zero (MvPolynomial.X_ne_zero (R := R) j))
  have h3 : (MvPolynomial.X j : MvPolynomial (Fin n) R) • (1 : Γ(X, U)) =
      (MvPolynomial.X j : MvPolynomial (Fin n) R) • (0 : Γ(X, U)) := by
    rw [smul_zero, Algebra.smul_def, mul_one]
    exact (MvPolynomial.eval₂Hom_X' _ _ j).trans h1
  exact one_ne_zero (h2 h3)

/- English proof (translation)
Establish `P` using `presents_ofLB hM c₀ h₀`. Establish `hr : P.rat τ ≠ 0` using `fun e => hτ (by rw [← P.rat_mul τ c₀ h₀, e, zero_mul])`. Establish `Q` using `P.add_principal (Units.mk0 _ hr)`. Use `⟨_, Q.toPic_eq, fun c y hy g hg => ?_⟩` and prove the remaining obligations. Establish `e : g = frameRat M c₀ h₀ c * Units.mk0 _ hr` using `Units.ext (by`.

Rewrite using `[hg, ← P.rat_mul τ c (gen_mem hy), Units.val_mul, Units.val_mk0, mul_comm])`. Conclude with `e ▸ Q.isEqn c y hy`.
-/
theorem exists_div_of_sec {X : Scheme.{0}} [IsIntegral X] {M : LB X} (hM : M.IsLB) (τ : M.Sec) (c₀ : M.ι)
    (h₀ : genericPoint X ∈ M.U c₀) (hτ : fnOf _ h₀ (τ.f c₀) ≠ 0) :
    ∃ E : CartierDiv X, toPic E = cls M hM ∧ ∀ (c : M.ι) (y : X) (hy : y ∈ M.U c)
      (g : X.functionFieldˣ), (g : X.functionField) = fnOf _ (gen_mem hy) (τ.f c) → E.IsEqn y g := by
  have P := presents_ofLB hM c₀ h₀
  have hr : P.rat τ ≠ 0 := fun e => hτ (by rw [← P.rat_mul τ c₀ h₀, e, zero_mul])
  have Q := P.add_principal (Units.mk0 _ hr)
  refine ⟨_, Q.toPic_eq, fun c y hy g hg => ?_⟩
  have e : g = frameRat M c₀ h₀ c * Units.mk0 _ hr := Units.ext (by
    rw [hg, ← P.rat_mul τ c (gen_mem hy), Units.val_mul, Units.val_mk0, mul_comm])
  exact e ▸ Q.isEqn c y hy

/- English proof (translation)
Establish `key (C : SncChart f d M τ) (h : genericPoint X ∈ C.U) (i : Fin s) : fnOf _ (C.le i h) ((τ i).f (C.c i)) = fnOf C.U h (C.u i) * fnOf C.U h ((C.e i).elim 1 C.t)`. Rewrite using `[← fnOf_resG (C.le i) h, C.eq i, map_mul]`. Establish `H (i : Fin s)` using `exists_div_of_sec (hM i) (τ i) (C₀.c i) (C₀.le i h₀) (by`. Rewrite using `[key C₀ h₀ i]`. Use `mul_ne_zero (unitAt_fnOf h₀ h₀ _).ne_zero ?_` and prove the remaining obligations.

Break down `C₀.e i with _ | a` into its components or cases. Simplify using the standard rewrite rules. Conclude with `fnOf_coord_ne_zero h₀ C₀.etale a)`. Use `choose E hE hE' using H`. Use `⟨E, hE, fun C h x hx i y hy => ?_⟩` and prove the remaining obligations.

Establish `hu` using `unitAt_fnOf hy h (C.u i)`. Establish `e : (((C.e i).elim 1 x : X.functionFieldˣ) : X.functionField) = fnOf C.U h ((C.e i).elim 1 C.t)`. Break down `C.e i with _ | a` into its components or cases. Simplify using the standard rewrite rules. Conclude with `hx a`.

Establish `h1` using `hE' i (C.c i) y (C.le i hy) (Units.mk0 _ hu.ne_zero * (C.e i).elim 1 x) (by`. Rewrite using `[Units.val_mul, Units.val_mk0, e]`. Conclude with `(key C h i).symm)`. Rewrite using `[h1.iff_unitAt, Units.val_mul, Units.val_mk0, div_mul_eq_div_div_swap, div_self (Units.ne_zero _), one_div]`. Conclude with `hu.inv`.
-/
theorem exists_div_of_chart {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} [IsIntegral X]
    {f : X ⟶ Sp R} {d s : ℕ} {M : Fin s → LB X} (hM : ∀ i, (M i).IsLB) {τ : ∀ i, (M i).Sec}
    (C₀ : SncChart f d M τ) (h₀ : genericPoint X ∈ C₀.U) :
    ∃ E : Fin s → CartierDiv X, (∀ i, toPic (E i) = cls (M i) (hM i)) ∧
      ∀ (C : SncChart f d M τ) (h : genericPoint X ∈ C.U) (x : Fin d → X.functionFieldˣ),
        (∀ j, (x j : X.functionField) = fnOf C.U h (C.t j)) →
        ∀ i, ∀ y ∈ C.U, (E i).IsEqn y ((C.e i).elim 1 x) := by
  have key (C : SncChart f d M τ) (h : genericPoint X ∈ C.U) (i : Fin s) :
      fnOf _ (C.le i h) ((τ i).f (C.c i)) = fnOf C.U h (C.u i) * fnOf C.U h ((C.e i).elim 1 C.t) := by
    rw [← fnOf_resG (C.le i) h, C.eq i, map_mul]
  have H (i : Fin s) := exists_div_of_sec (hM i) (τ i) (C₀.c i) (C₀.le i h₀) (by
    rw [key C₀ h₀ i]
    refine mul_ne_zero (unitAt_fnOf h₀ h₀ _).ne_zero ?_
    rcases C₀.e i with _ | a
    · simp
    · exact fnOf_coord_ne_zero h₀ C₀.etale a)
  choose E hE hE' using H
  refine ⟨E, hE, fun C h x hx i y hy => ?_⟩
  have hu := unitAt_fnOf hy h (C.u i)
  have e : (((C.e i).elim 1 x : X.functionFieldˣ) : X.functionField) =
      fnOf C.U h ((C.e i).elim 1 C.t) := by
    rcases C.e i with _ | a
    · simp
    · exact hx a
  have h1 := hE' i (C.c i) y (C.le i hy) (Units.mk0 _ hu.ne_zero * (C.e i).elim 1 x) (by
    rw [Units.val_mul, Units.val_mk0, e]; exact (key C h i).symm)
  rw [h1.iff_unitAt, Units.val_mul, Units.val_mk0, div_mul_eq_div_div_swap, div_self (Units.ne_zero _),
    one_div]
  exact hu.inv

noncomputable def pullChart {R R' : Type} [CommRing R] [CommRing R'] {φ : R →+* R'} {X X' : Scheme.{0}}
    {f : X ⟶ Sp R} {f' : X' ⟶ Sp R'} {π : X' ⟶ X} (hP : IsPullback π f' f (spMap φ)) {d s : ℕ}
    {L : Fin s → LB X} {σ : ∀ i, (L i).Sec} (C : SncChart f d L σ) :
    SncChart f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π) where
  U := π ⁻¹ᵁ C.U
  affine := (isEtCoord_baseChange R R' φ X X' f f' π C.U d C.t hP C.affine C.etale).1
  t := fun a => (π.app C.U).hom (C.t a)
  etale := (isEtCoord_baseChange R R' φ X X' f f' π C.U d C.t hP C.affine C.etale).2
  c := fun i => fun _ => C.c i
  le := fun i => (π.preimage_mono (C.le i)).trans (Cartier.pull_U (L i) π fun _ => C.c i).ge
  e := C.e
  inj := C.inj
  u := fun i => Units.map (π.app C.U).hom (C.u i)
  eq := fun i => by
    show resG X' _ (resG X' _ ((π.app _).hom ((σ i).f (C.c i)))) = _
    rw [Cartier.resG_resG, ← Cartier.app_resG π (C.le i), C.eq i, map_mul]
    rcases h : C.e i with _ | a
    · simp
    · simp

/- English proof (translation)
Introduce `p _ Y X _ g f π d _ hP hf hd s L σ h`. Use `choose D hD using fun x : X => h.chart (π x)`. Establish `hpr` using `(isProper_and_exists_isAmpleLB_of_isProjOver hf).1`. Establish `: CompactSpace X` using `QuasiCompact.compactSpace_of_compactSpace f`. Take `⟨T, hT⟩` from `isCompact_univ.elim_finite_subcover (fun x : X => ((π ⁻¹ᵁ (D x).U : X.Opens) : Set X)) (fun x => (π ⁻¹ᵁ (D x).U).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hD x⟩)`.

Set `ε` to `T.equivFin.symm`. Set `C : Fin T.card → SncChart g d L σ` to `fun k => D (ε k)`. Establish `hgen (k) : genericPoint X ∈ (pullChart hP (C k)).U` using `gen_mem (x := ε k) (hD _)`. Establish `hcov (y : X) : ∃ k, y ∈ (pullChart hP (C k)).U`. Take `⟨z, hz, hy⟩` from `Set.mem_iUnion₂.1 (hT (Set.mem_univ y))`.

Take `⟨k, hk⟩` from `ε.surjective ⟨z, hz⟩`. Take `rfl : (ε k : X) = z` from `congrArg Subtype.val hk`. Conclude with `⟨k, hy⟩`. Take `⟨k₀, -⟩` from `hcov (genericPoint X)`. Establish `: Nonempty (Fin T.card)` using `⟨k₀⟩`.

Take `⟨E, hE, hE'⟩` from `exists_div_of_chart (fun i => pull_isLB (h.isLB i) π) (pullChart hP (C k₀)) (hgen k₀)`. Set `x : Fin T.card → Fin d → X.functionFieldˣ` to `fun k j => Units.mk0 _ (fnOf_coord_ne_zero (hgen k) (pullChart hP (C k)).etale j)`. Set `J : Fin T.card → Finset (Fin d)` to `fun k => Finset.univ.filter fun j => ∃ c, (C k).e c = some j`. Establish `hJ (k j) : j ∈ J k ↔ ∃ c, (C k).e c = some j` using `by simp [J]`. Establish `heq (k)` using `hE' (pullChart hP (C k)) (hgen k) (x k) (fun _ => rfl)`.

Establish `hlog (k) : IsLogChart (suppAll E) (pullChart hP (C k)).U (x k) (J k)`. Use `GlobalTheory.T.etale_coordinates_log_chart p X f _ (hgen k) (pullChart hP (C k)).t (x k) (J k) _ (pullChart hP (C k)).affine (pullChart hP (C k)).etale (fun _ => rfl) fun y hy => ?_` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `hy'`. Take `⟨c, hc⟩` from `Set.mem_iUnion.1 hy'`.

Establish `h1` using `(heq k c y hy).mem_supp_iff.1 hc`. Express the relevant statement in the definitionally equal form `¬ UnitAt y ((((C k).e c).elim 1 (x k) : X.functionFieldˣ) : X.functionField) at h1`. Break down `he : (C k).e c with _ | a` into its components or cases. Rewrite `h1` using `[he]`. Conclude with `(h1 (unitAt_one y)).elim`.

Rewrite `h1` using `[he]`. Conclude with `⟨a, (hJ k a).2 ⟨c, he⟩, h1⟩`. Introduce and unpack `⟨j, hj, hu⟩`. Take `⟨c, hc⟩` from `(hJ k j).1 hj`. Use `Set.mem_iUnion.2 ⟨c, (heq k c y hy).mem_supp_iff.2 ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `¬ UnitAt y ((((C k).e c).elim 1 (x k) : X.functionFieldˣ) : X.functionField)`. Rewrite using `[hc]`. Conclude with `hu`. Set `𝒜 : SncAtlas E d (Fin T.card)` to `{ U := fun k => (pullChart hP (C k)).U x := x J := J affine := fun k => (pullChart hP (C k)).affine gen := hgen cover := eq_top_iff.2 fun y _ => Opens.mem_iSup.2 (hcov y) chart := hlog snc := fun k => ⟨(C k).e, (C k).inj, hJ k, heq k⟩ }`. Establish `: CharP X.functionField p` using `charP_of_injective_ringHom (Cartier.constFn f).injective p`.

Use `⟨T.card, E, 𝒜, GlobalTheory.T.frobenius_decomposition_of_lift p 𝒜 hd ?_, fun i => (hE i).trans (CechPic.cls_pull (h.isLB i) π _)⟩` and prove the remaining obligations. Use `DI.isLifted_of_sncCharts p Y X g f π hP L σ h.isLB C _ _ (fun _ => le_rfl) hgen x J (fun k l => ?_) (fun k l => (hJ k l).1) hlog` and prove the remaining obligations. Conclude with `congrArg (fun ψ : Γ(Y, (C k).U) ⟶ Γ(X, π ⁻¹ᵁ (C k).U) => fnOf _ (hgen k) (ψ.hom ((C k).t l))) (π.app_eq_appLE)`.
-/
theorem exists_atlas_decomp : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0}) [IsIntegral X] (g : Y ⟶ Sp (ZMod (p ^ 2))) (f : X ⟶ Sp (ZMod p)) (π : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f], IsPullback π f g (spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) → IsProjOver f → d < p → ∀ (s : ℕ) (L : Fin s → LB Y) (σ : ∀ i, (L i).Sec) (h : RelSnc g d L σ), ∃ (m : ℕ) (E : Fin s → CartierDiv X) (𝒜 : SncAtlas E d (Fin m)), Decomp p 𝒜 ∧ ∀ i, toPic (E i) = CechPic.pull π (cls (L i) (h.isLB i)) := by
  classical
  intro p _ Y X _ g f π d _ hP hf hd s L σ h
  choose D hD using fun x : X => h.chart (π x)
  have hpr := (isProper_and_exists_isAmpleLB_of_isProjOver hf).1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun x : X => ((π ⁻¹ᵁ (D x).U : X.Opens) : Set X))
    (fun x => (π ⁻¹ᵁ (D x).U).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hD x⟩)
  let ε := T.equivFin.symm
  let C : Fin T.card → SncChart g d L σ := fun k => D (ε k)
  have hgen (k) : genericPoint X ∈ (pullChart hP (C k)).U := gen_mem (x := ε k) (hD _)
  have hcov (y : X) : ∃ k, y ∈ (pullChart hP (C k)).U := by
    obtain ⟨z, hz, hy⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ y))
    obtain ⟨k, hk⟩ := ε.surjective ⟨z, hz⟩
    obtain rfl : (ε k : X) = z := congrArg Subtype.val hk
    exact ⟨k, hy⟩
  obtain ⟨k₀, -⟩ := hcov (genericPoint X)
  have : Nonempty (Fin T.card) := ⟨k₀⟩
  obtain ⟨E, hE, hE'⟩ := exists_div_of_chart (fun i => pull_isLB (h.isLB i) π) (pullChart hP (C k₀)) (hgen k₀)
  let x : Fin T.card → Fin d → X.functionFieldˣ := fun k j =>
    Units.mk0 _ (fnOf_coord_ne_zero (hgen k) (pullChart hP (C k)).etale j)
  let J : Fin T.card → Finset (Fin d) := fun k => Finset.univ.filter fun j => ∃ c, (C k).e c = some j
  have hJ (k j) : j ∈ J k ↔ ∃ c, (C k).e c = some j := by simp [J]
  have heq (k) := hE' (pullChart hP (C k)) (hgen k) (x k) (fun _ => rfl)
  have hlog (k) : IsLogChart (suppAll E) (pullChart hP (C k)).U (x k) (J k) := by
    refine GlobalTheory.T.etale_coordinates_log_chart p X f _ (hgen k) (pullChart hP (C k)).t (x k) (J k) _ (pullChart hP (C k)).affine
      (pullChart hP (C k)).etale (fun _ => rfl) fun y hy => ?_
    constructor
    · intro hy'
      obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hy'
      have h1 := (heq k c y hy).mem_supp_iff.1 hc
      change ¬ UnitAt y ((((C k).e c).elim 1 (x k) : X.functionFieldˣ) : X.functionField) at h1
      rcases he : (C k).e c with _ | a
      · rw [he] at h1
        exact (h1 (unitAt_one y)).elim
      · rw [he] at h1
        exact ⟨a, (hJ k a).2 ⟨c, he⟩, h1⟩
    · rintro ⟨j, hj, hu⟩
      obtain ⟨c, hc⟩ := (hJ k j).1 hj
      refine Set.mem_iUnion.2 ⟨c, (heq k c y hy).mem_supp_iff.2 ?_⟩
      change ¬ UnitAt y ((((C k).e c).elim 1 (x k) : X.functionFieldˣ) : X.functionField)
      rw [hc]
      exact hu
  let 𝒜 : SncAtlas E d (Fin T.card) :=
    { U := fun k => (pullChart hP (C k)).U
      x := x
      J := J
      affine := fun k => (pullChart hP (C k)).affine
      gen := hgen
      cover := eq_top_iff.2 fun y _ => Opens.mem_iSup.2 (hcov y)
      chart := hlog
      snc := fun k => ⟨(C k).e, (C k).inj, hJ k, heq k⟩ }
  have : CharP X.functionField p := charP_of_injective_ringHom (Cartier.constFn f).injective p
  refine ⟨T.card, E, 𝒜, GlobalTheory.T.frobenius_decomposition_of_lift p 𝒜 hd ?_, fun i => (hE i).trans (CechPic.cls_pull (h.isLB i) π _)⟩
  refine DI.isLifted_of_sncCharts p Y X g f π hP L σ h.isLB C _ _ (fun _ => le_rfl) hgen x J
    (fun k l => ?_) (fun k l => (hJ k l).1) hlog
  exact congrArg (fun ψ : Γ(Y, (C k).U) ⟶ Γ(X, π ⁻¹ᵁ (C k).U) => fnOf _ (hgen k) (ψ.hom ((C k).t l)))
    (π.app_eq_appLE)

end GlobalTheory.LogAtlas
