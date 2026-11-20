import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinatesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FilteredCohomologyRestrictionBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingAlongIdealFiltrationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteModulesSerreClassStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverCohomologyFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverHigherCohomologyVanishesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechVanishingFromCoverStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmoothCoordinateCoverStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGoodStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDividedPowersGradedConstantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationPropertyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeCohomologyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenOfThickeningMorphismStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenFiniteInfIffStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormCocycleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormExistsOfCocycleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormAddStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormSmulStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormRestrictStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormActionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormFrameStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormLocalOfFrameStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormVanishOfFrameStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormCoverStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

/- English proof (translation)
Use function extensionality and compare the values at `T`. Establish `h` using `GlobalTheory.T.inOpen_finite_inf_iff (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (U ∘ i) Finset.univ T`. Establish `e : (⨅ α ∈ (Finset.univ : Finset (Fin (n + 1))), (U ∘ i) α) = capO U i` using `by simp [capO]`. Rewrite `h` using `[e]`. Use `propext ⟨fun hT => ?_, fun hT a => ?_⟩` and prove the remaining obligations.

Use `⟨(hT 0).1, capO U i, rfl, h.2 fun a _ => ?_⟩` and prove the remaining obligations. Take `⟨-, V, hV, hI⟩` from `hT a`. Rewrite `hV` using `[Set.mem_singleton_iff]`. Substitute `hV` using the available equality. Conclude with `hI`.

Take `⟨h1, V, hV, hI⟩` from `hT`. Rewrite `hV` using `[Set.mem_singleton_iff]`. Substitute `hV` using the available equality. Conclude with `⟨h1, _, rfl, h.1 hI a (Finset.mem_univ _)⟩`.
-/
theorem capT_eq {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {ι : Type}
    (Q : ObjectProperty (Thick (LL q))) (U : ι → X.Opens) {n : ℕ} (i : Fin (n + 1) → ι) :
    capT (fun α => St Q {U α}) i = St Q {capO U i} := by
  funext T
  have h := GlobalTheory.T.inOpen_finite_inf_iff (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (U ∘ i) Finset.univ T
  have e : (⨅ α ∈ (Finset.univ : Finset (Fin (n + 1))), (U ∘ i) α) = capO U i := by simp [capO]
  rw [e] at h
  refine propext ⟨fun hT => ?_, fun hT a => ?_⟩
  · refine ⟨(hT 0).1, capO U i, rfl, h.2 fun a _ => ?_⟩
    obtain ⟨-, V, hV, hI⟩ := hT a
    rw [Set.mem_singleton_iff] at hV
    subst hV
    exact hI
  · obtain ⟨h1, V, hV, hI⟩ := hT
    rw [Set.mem_singleton_iff] at hV
    subst hV
    exact ⟨h1, _, rfl, h.1 hI a (Finset.mem_univ _)⟩

/- English proof (translation)
Use `le_bot_iff.1 (Ideal.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨l, hl, hr, rfl⟩`. Establish `: ∃ p ∈ l, p.1 ≠ 0`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Establish `: (l.map Prod.fst).sum = 0` using `List.sum_eq_zero (by`. Introduce `x hx`. Take `⟨p, hp, rfl⟩` from `List.mem_map.1 hx`. Conclude with `hc p hp)`. Use linear arithmetic over natural numbers and integers.

Take `⟨p, hp, hp0⟩` from `this`. Establish `h0 : (dividedPowersBot K).dpow p.1 p.2 = 0`. Establish `: p.2 = 0` using `hl p hp`. Rewrite using `[this]`. Conclude with `(dividedPowersBot K).dpow_eval_zero hp0`.

Simplify using `only [SetLike.mem_coe]`. Rewrite using `[List.prod_eq_zero (List.mem_map.2 ⟨p, hp, h0⟩)]`. Conclude with `Ideal.zero_mem _`.
-/
theorem dividedPowerFiltration_bot {K : Type} [CommRing K] {s : ℕ} (hs : 0 < s) : pdP (dividedPowersBot K) s = ⊥ := by
  refine le_bot_iff.1 (Ideal.span_le.2 ?_)
  rintro _ ⟨l, hl, hr, rfl⟩
  have : ∃ p ∈ l, p.1 ≠ 0 := by
    by_contra hc
    push_neg at hc
    have : (l.map Prod.fst).sum = 0 := List.sum_eq_zero (by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      exact hc p hp)
    omega
  obtain ⟨p, hp, hp0⟩ := this
  have h0 : (dividedPowersBot K).dpow p.1 p.2 = 0 := by
    have : p.2 = 0 := hl p hp
    rw [this]
    exact (dividedPowersBot K).dpow_eval_zero hp0
  simp only [SetLike.mem_coe]
  rw [List.prod_eq_zero (List.mem_map.2 ⟨p, hp, h0⟩)]
  exact Ideal.zero_mem _

/- English proof (translation)
The claim follows from `dividedPowerFiltration_bot hs tf r x h := by simpa using h dv n hn := ⟨0, (n : K)⁻¹, by simp; exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn)⟩`.
-/
theorem tfBase {K : Type} [Field K] [CharZero K] {s : ℕ} (hs : 0 < s) : TFBase (dividedPowersBot K) 1 s where
  nil := dividedPowerFiltration_bot hs
  tf r x h := by simpa using h
  dv n hn := ⟨0, (n : K)⁻¹, by simp; exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn)⟩

def zeroSerre (K : Type) [CommRing K] : Serre.{1} K where
  P M _ _ := Subsingleton M
  zero _ _ _ h := h
  mid M₁ M₂ M₃ _ _ _ _ _ _ f g hfg h₁ h₃ := ⟨fun a b => by
    have key : ∀ x : M₂, x = 0 := fun x => by
      obtain ⟨y, rfl⟩ := (hfg x).1 (Subsingleton.elim _ _)
      rw [Subsingleton.elim y 0, map_zero]
    rw [key a, key b]⟩

/- English proof (translation)
Use `⟨fun a b => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective _ a`. Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective _ b`. Rewrite using `[Subsingleton.elim a b]`.
-/
theorem subsingleton_H {K : Type} [CommRing K] (C : Cx.{1} K) (n : ℕ) (h : Subsingleton (C.X n)) : Subsingleton (C.H n) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [Subsingleton.elim a b]

/- English proof (translation)
Use `subsingleton_H _ a ?_` and prove the remaining obligations. Use `⟨fun x y => funext fun i => ?_⟩` and prove the remaining obligations. Establish `e` using `capT_eq (q := q) (TF l s) U i`. Take `⟨c', -⟩` from `GlobalTheory.T.coordinates_restrict_affine_open (c (i 0)) (capO_le U i 0) (ha _ i)`. Establish `: Subsingleton (HU (GF q r) (capT (fun α => SS q l s (U α)) i) b)`.

Rewrite using `[e]`. Conclude with `hV l s hb q c' r b hr hbr`. Conclude with `Subsingleton.elim _ _`.
-/
theorem cech_van (hV : StVan) {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) {ι : Type} (U : ι → X.Opens) (d : ι → ℕ)
    (c : ∀ α, Coord q (U α) (d α)) (ha : ∀ n (i : Fin (n + 1) → ι), IsAffineOpen (capO U i)) (r b a : ℕ) (hr : r < s)
    (hbr : b ≠ r) : Subsingleton ((CrystallineSemistableComparison.Pb.cechH (GF q r) (fun α => SS q l s (U α)) b).cx.H a) := by
  refine subsingleton_H _ a ?_
  refine ⟨fun x y => funext fun i => ?_⟩
  have e := capT_eq (q := q) (TF l s) U i
  obtain ⟨c', -⟩ := GlobalTheory.T.coordinates_restrict_affine_open (c (i 0)) (capO_le U i 0) (ha _ i)
  have : Subsingleton (HU (GF q r) (capT (fun α => SS q l s (U α)) i) b) := by
    rw [e]
    exact hV l s hb q c' r b hr hbr
  exact Subsingleton.elim _ _

/- English proof (translation)
Take `⟨vb⟩` from `hB l s hb q U d c ha r hr`. Conclude with `GlobalTheory.T.affine_cover_higher_cohomology_vanishes (strV q) V hV U hU ha (CrystallineSemistableComparison.Pb.cechH (GF q r) (fun α => SS q l s (U α)) r) vb p`.
-/
theorem cech_pos (hB : StVB) {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) {ι : Type} [Fintype ι] (U : ι → X.Opens) (d : ι → ℕ) (V : X.Opens) (hV : IsAffineOpen V)
    (hU : (⨆ α, U α) = V)
    (c : ∀ α, Coord q (U α) (d α)) (ha : ∀ n (i : Fin (n + 1) → ι), IsAffineOpen (capO U i)) (r p : ℕ) (hr : r < s) :
    Subsingleton ((CrystallineSemistableComparison.Pb.cechH (GF q r) (fun α => SS q l s (U α)) r).cx.H (p + 1)) := by
  obtain ⟨vb⟩ := hB l s hb q U d c ha r hr
  exact GlobalTheory.T.affine_cover_higher_cohomology_vanishes (strV q) V hV U hU ha (CrystallineSemistableComparison.Pb.cechH (GF q r) (fun α => SS q l s (U α)) r) vb p

set_option maxHeartbeats 2000000 in
/- English proof (translation)
Introduce `hS K _ _ X q _ V hVa s r j hr hj`. Establish `hs : 0 < s` using `by omega`. Establish `hb : TFBase (dividedPowersBot K) 1 s` using `tfBase hs`. Take `⟨ι, _, U, d, c, hU, ha⟩` from `hC q V hVa`. Establish `hle : ∀ α, U α ≤ V` using `fun α => hU ▸ le_iSup U α`.

Establish `hinc : St (γ` using `dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF 1 s) (Set.range U) ≤ St (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF 1 s) {V} := by`. Introduce and unpack `T ⟨h1, W, ⟨α, rfl⟩, hI⟩`. Conclude with `⟨h1, V, rfl, fun x hx => hle α (hI hx)⟩`. Establish `hz` using `GlobalTheory.T.cech_refinement_cohomology_bijective (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF 1 s) (Or.inl ⟨rfl, 1, s, rfl⟩) (Set.range U) {V} hinc (by`. Introduce and unpack `W rfl`.

Rewrite using `[← hU, sSup_range]) j`. Establish `hcech : ∀ a b, a + b = j → (zeroSerre K).P ((CrystallineSemistableComparison.Pb.cechH (GF q r) (fun α => SS q 1 s (U α)) b).cx.H a)`. Introduce `a b hab`. Distinguish the cases in `hbr : b = r`. Substitute `hbr` using the available equality.

Consider the cases of `a with`. Consider the case `zero => exact absurd (by omega) hj`. Consider the case `succ p => exact cech_pos hB 1 s hb q U d V hVa hU c ha b p hr`. Conclude with `cech_van hV 1 s hb q U d c ha r b a hr hbr`. Establish `hG` using `hS (O := K) (R := K) (I := ⊥) (γ := dividedPowersBot K) (p := 0) (X := X) (q := q) (κ := Ideal.Quotient.mk ⊥) (Λ := K) (GF q r) (TF 1 s) U (zeroSerre K) j hcech`.

Conclude with `@Function.Injective.subsingleton _ _ _ (hz.1 r ((r : ℤ) + 1)).1 hG`.
-/
theorem main (hV : StVan) (hB : StVB) (hC : StCover) : KH.GlobSerreSt → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q]
    (V : X.Opens) (hV : IsAffineOpen V) (s r j : ℕ), r < s → j ≠ r → Subsingleton (HQ (KS q s {V}) r ((r : ℤ) + 1) j) := by
  intro hS K _ _ X q _ V hVa s r j hr hj
  have hs : 0 < s := by omega
  have hb : TFBase (dividedPowersBot K) 1 s := tfBase hs
  obtain ⟨ι, _, U, d, c, hU, ha⟩ := hC q V hVa
  have hle : ∀ α, U α ≤ V := fun α => hU ▸ le_iSup U α
  have hinc : St (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF 1 s) (Set.range U) ≤
      St (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF 1 s) {V} := by
    rintro T ⟨h1, W, ⟨α, rfl⟩, hI⟩
    exact ⟨h1, V, rfl, fun x hx => hle α (hI hx)⟩
  have hz := GlobalTheory.T.cech_refinement_cohomology_bijective (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF 1 s) (Or.inl ⟨rfl, 1, s, rfl⟩) (Set.range U) {V} hinc
    (by
      rintro W rfl
      rw [← hU, sSup_range]) j
  have hcech : ∀ a b, a + b = j → (zeroSerre K).P ((CrystallineSemistableComparison.Pb.cechH (GF q r) (fun α => SS q 1 s (U α)) b).cx.H a) := by
    intro a b hab
    by_cases hbr : b = r
    · subst hbr
      cases a with
      | zero => exact absurd (by omega) hj
      | succ p => exact cech_pos hB 1 s hb q U d V hVa hU c ha b p hr
    · exact cech_van hV 1 s hb q U d c ha r b a hr hbr
  have hG := hS (O := K) (R := K) (I := ⊥) (γ := dividedPowersBot K) (p := 0) (X := X) (q := q) (κ := Ideal.Quotient.mk ⊥) (Λ := K)
    (GF q r) (TF 1 s) U (zeroSerre K) j hcech
  exact @Function.Injective.subsingleton _ _ _ (hz.1 r ((r : ℤ) + 1)).1 hG

end GlobalTheory.CompanionTheory.GrForm

namespace GlobalTheory.CompanionTheory.GrForm

/- English proof (translation)
Introduce `hL _ hP hS _` and use `main (GlobalTheory.T.graded_form_vanish_of_frame GlobalTheory.T.graded_form_frame hL hP) (GlobalTheory.T.graded_form_vector_bundle (GlobalTheory.T.graded_form_exists_of_cocycle GlobalTheory.T.graded_form_cocycle) GlobalTheory.T.graded_form_add GlobalTheory.T.graded_form_smul Glob …`.
-/
theorem gr_aff : KH.LocGr → KH.LocVan → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q]
    (V : X.Opens) (hV : IsAffineOpen V) (s r j : ℕ), r < s → j ≠ r → Subsingleton (HQ (KS q s {V}) r ((r : ℤ) + 1) j) := fun hL _ hP hS _ =>
  main (GlobalTheory.T.graded_form_vanish_of_frame GlobalTheory.T.graded_form_frame hL hP)
    (GlobalTheory.T.graded_form_vector_bundle (GlobalTheory.T.graded_form_exists_of_cocycle GlobalTheory.T.graded_form_cocycle) GlobalTheory.T.graded_form_add GlobalTheory.T.graded_form_smul GlobalTheory.T.graded_form_restrict GlobalTheory.T.graded_form_action (GlobalTheory.T.graded_form_local_of_frame GlobalTheory.T.graded_form_frame hL hP))
    GlobalTheory.T.graded_form_cover hS
end GlobalTheory.CompanionTheory.GrForm
