import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationsSamePointDifferByIsometryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteMarkedLatticePeriodRepresentativesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasePointAndExponentialHolomorphicInPeriodsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicMapLiftsLocallyToPeriodFamiliesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationAtTransportIsometryStatement

noncomputable section

namespace GlobalTheory.PELU

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

/- English proof (translation)
Take `⟨hlin, hinj, hdisc, hspan, Hm, hH, hpos, him⟩` from `hP`. Establish `hrange : (P.comp w.symm.toLinearMap.toAddMonoidHom).range = P.range`. Use extensionality with `v`. Simplify using `only [AddMonoidHom.mem_range, AddMonoidHom.comp_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, rfl⟩`. Conclude with `⟨_, rfl⟩`. Introduce and unpack `⟨x, rfl⟩; exact ⟨w x, by simp⟩`. Establish `hrange' : Set.range (P.comp w.symm.toLinearMap.toAddMonoidHom) = Set.range P`. Use `congrArg (fun S : AddSubgroup (Fin g → ℂ) => (S : Set (Fin g → ℂ))) hrange` as an intermediate fact.

Simplify `this` using `[AddMonoidHom.coe_range]`. Use `⟨fun a x => ?_, ?_, ?_, ?_, Hm, hH, hpos, fun x y => ?_⟩` and prove the remaining obligations. Simplify using `[hlin]`. Introduce `x y hxy`. Use `hinj hxy` as an intermediate fact.

Simplify using `using this`. Rewrite using `[hrange]`. Conclude with `hdisc`. Rewrite using `[hrange']`. Conclude with `hspan`.

Use `hw (w.symm x) (w.symm y)` as an intermediate fact. Simplify using `only [LinearEquiv.apply_symm_apply] at this`. Simplify using `[him, this]`.
-/
theorem isPeriod_comp_isometry_symm {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ}
    (D D' : PLat O bar) (w : D.La ≃ₗ[O] D'.La) (hw : IsIsom D D' w) (P : D.La →+ (Fin g → ℂ))
    (hP : IsPeriod D ρ P) : IsPeriod D' ρ (P.comp w.symm.toLinearMap.toAddMonoidHom) := by
  obtain ⟨hlin, hinj, hdisc, hspan, Hm, hH, hpos, him⟩ := hP
  have hrange : (P.comp w.symm.toLinearMap.toAddMonoidHom).range = P.range := by
    ext v
    simp only [AddMonoidHom.mem_range, AddMonoidHom.comp_apply]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩; exact ⟨w x, by simp⟩
  have hrange' : Set.range (P.comp w.symm.toLinearMap.toAddMonoidHom) = Set.range P := by
    have := congrArg (fun S : AddSubgroup (Fin g → ℂ) => (S : Set (Fin g → ℂ))) hrange
    simpa [AddMonoidHom.coe_range] using this
  refine ⟨fun a x => ?_, ?_, ?_, ?_, Hm, hH, hpos, fun x y => ?_⟩
  · simp [hlin]
  · intro x y hxy
    have := hinj hxy
    simpa using this
  · rw [hrange]; exact hdisc
  · rw [hrange']; exact hspan
  · have := hw (w.symm x) (w.symm y)
    simp only [LinearEquiv.apply_symm_apply] at this
    simp [him, this]

/- English proof (translation)
Introduce `O _ bar g ρ Λ F N C d hN heta hsm hqc hfull hF`. Establish `hN0 : 0 < N` using `by omega`. Establish `hlft : LocallyOfFiniteType F.s` using `by haveI := hsm haveI : Smooth F.s := SmoothOfRelativeDimension.smooth d F.s infer_instance`. Take `⟨n, Di, t, hmem, hall, hdist⟩` from `GlobalTheory.T.exists_finite_markedLattice_period_representatives O bar g ρ Λ F N C d hN0 heta hsm hqc hF`. Establish `hQ : ∀ i (P : (Di i).La →+ (Fin g → ℂ)), ∃ Q, IsPeriod (Di i) ρ Q ∧ (IsPeriod (Di i) ρ P → Q = P)`.

Introduce `i P`. Distinguish the cases in `hP : IsPeriod (Di i) ρ P`. Conclude with `⟨P, hP, fun _ => rfl⟩`. Take `⟨Q, hQ⟩` from `(hmem i).2`. Conclude with `⟨Q, hQ, fun h => absurd h hP⟩`.

Use `choose Q hQp hQe using hQ`. Establish `hex : ∀ i P, ∃ y e, UnifAt F (RingHom.id ℂ) ρ N (Di i) (t i) (Q i P) y e` using `fun i P => hF.occ _ _ _ (hmem i).1 (hQp i P)`. Use `choose u ex hu using hex`. Establish `hunif : ∀ i P, IsPeriod (Di i) ρ P → UnifAt F (RingHom.id ℂ) ρ N (Di i) (t i) P (u i P) (ex i P)`. Introduce `i P hP`.

Use `hu i P` as an intermediate fact. Rewrite `this` using `[hQe i P hP]`. Then use the resulting hypothesis. Establish `hrefl : ∀ i, IsMarkedIsom N (Di i) (Di i) (t i) (t i) (LinearEquiv.refl O _)` using `fun i => ⟨fun x y => rfl, fun a => ⟨0, by simp⟩⟩`. Establish `cmpEq : ∀ (D' D'' : PLat O bar) (t' : Λ → D'.La) (t'' : Λ → D''.La) (P : D'.La →+ (Fin g → ℂ)) (P' : D''.La →+ (Fin g → ℂ)) (y y' : Sp ℂ ⟶ F.X) (e : (Fin g → ℂ) → (Over.mk y ⟶ F.A)) (e' : (Fin g → ℂ) → (Over.mk y' ⟶ F.A)), y = y' → UnifAt F (RingHom.id ℂ) ρ N D' t' P y e → UnifAt …`. Introduce `D' D'' t' t'' P P' y y' e e' hy h1 h2`.

Substitute `hy` using the available equality. Apply the tactic sequence `obtain ⟨w, h, hw, hP, -⟩ := GlobalTheory.T.complexUniformisations_same_point_differ_by_isometry O bar g ρ ℂ (RingHom.id ℂ) Λ F N D' D'' t' t'' P P' y e e' hN0 h1 h2`. Conclude with `⟨w, h, hw, hP⟩`. Use `⟨{ n := n Di := Di t := t mem := fun i => (hmem i).1 ne := fun i => (hmem i).2 all := hall distinct := hdist u := u ex := ex unif := hunif onto := ?_ disj := ?_ fibre := ?_ hol := ?_ lift := ?_ }⟩` and prove the remaining obligations. Introduce `y hy`.

Take `⟨D', t', P, e, hC, hU⟩` from `hF.pts y hy`. Take `⟨i, w, hw⟩` from `hall D' t' hC ⟨P, hU.2.1⟩`. Establish `hP'` using `isPeriod_comp_isometry_symm D' (Di i) w hw.1 P hU.2.1`. Use `⟨i, _, hP', ?_⟩` and prove the remaining obligations. Conclude with `(hF.sep D' (Di i) t' (t i) P _ y _ e (ex i _) hU (hunif i _ hP') w (LinearEquiv.refl ℂ _) hw (fun x => by simp)).symm`.

Introduce `i j P P' hP hP' huu`. Take `⟨w, h, hw, -⟩` from `cmpEq _ _ _ _ _ _ _ _ _ _ huu (hunif i P hP) (hunif j P' hP')`. Conclude with `hdist i j w hw`. Introduce `i P P' hP hP'`. Prove the components needed by the constructor for the conclusion.

Introduce `huu`. Conclude with `cmpEq _ _ _ _ _ _ _ _ _ _ huu (hunif i P hP) (hunif i P' hP')`. Introduce and unpack `⟨w, h, hw, hPw⟩`. Conclude with `hF.sep _ _ _ _ _ _ _ _ _ _ (hunif i P hP) (hunif i P' hP') w h hw hPw`. Introduce `i m B P hB hHol`.

Conclude with `GlobalTheory.T.basePoint_and_exponential_holomorphic_in_periods O bar g ρ Λ F N C d (Di i) (t i) m B P (fun b => u i (P b)) (fun b => ex i (P b)) hN heta hsm hqc hF (hmem i).1 (hfull _ _ (hmem i).1) hB hHol (fun b hb => hunif i (P b) (hHol.1 b hb))`. Introduce `m B y hB hy hhol b₀ hb₀`. Take `⟨D', t', P, e, hC, hU⟩` from `hF.pts (y b₀) (hy b₀ hb₀)`. Take `⟨i, w, hw⟩` from `hall D' t' hC ⟨P, hU.2.1⟩`. Establish `hP'` using `isPeriod_comp_isometry_symm D' (Di i) w hw.1 P hU.2.1`.

Apply the tactic sequence `have hU' := GlobalTheory.T.uniformisationAt_transport_isometry O bar g ρ ℂ (RingHom.id ℂ) Λ F N D' (Di i) t' (t i) P _ (y b₀) e w (LinearEquiv.refl ℂ _) hN0 hU hw (fun x => by simp) hP'`. Take `⟨B', P₁, e₁, hB', hb₀', hBB, -, hHol, -, hU₁⟩` from `GlobalTheory.T.holomorphicMap_lifts_locally_to_periodFamilies O bar g ρ Λ F N (Di i) (t i) m B y b₀ _ _ hN0 heta hlft hB hb₀ hy hhol hU'`. Use `⟨B', i, P₁, hB', hb₀', hBB, hHol, fun b hb => ?_⟩` and prove the remaining obligations. Conclude with `hF.sep _ _ _ _ _ _ _ _ _ _ (hunif i (P₁ b) (hHol.1 b hb)) (hU₁ b hb) (LinearEquiv.refl O _) (LinearEquiv.refl ℂ _) (hrefl i) (fun x => rfl)`.
-/
theorem unif_of_fineAt : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (Λ : Type)
    (F : Fam ℂ O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (d : ℕ), 3 ≤ N → (∀ a, F.eta a ^ N = 1) →
    SmoothOfRelativeDimension d F.s → QuasiCompact F.s → (∀ D' t, C D' t → FullMark N D' t) →
    FineAt F (RingHom.id ℂ) ρ N C → Nonempty (Unif F (RingHom.id ℂ) ρ N C) := by
  intro O _ bar g ρ Λ F N C d hN heta hsm hqc hfull hF
  have hN0 : 0 < N := by omega
  have hlft : LocallyOfFiniteType F.s := by
    haveI := hsm
    haveI : Smooth F.s := SmoothOfRelativeDimension.smooth d F.s
    infer_instance
  obtain ⟨n, Di, t, hmem, hall, hdist⟩ := GlobalTheory.T.exists_finite_markedLattice_period_representatives O bar g ρ Λ F N C d hN0 heta hsm hqc hF
  have hQ : ∀ i (P : (Di i).La →+ (Fin g → ℂ)), ∃ Q, IsPeriod (Di i) ρ Q ∧ (IsPeriod (Di i) ρ P → Q = P) := by
    intro i P
    by_cases hP : IsPeriod (Di i) ρ P
    · exact ⟨P, hP, fun _ => rfl⟩
    · obtain ⟨Q, hQ⟩ := (hmem i).2
      exact ⟨Q, hQ, fun h => absurd h hP⟩
  choose Q hQp hQe using hQ
  have hex : ∀ i P, ∃ y e, UnifAt F (RingHom.id ℂ) ρ N (Di i) (t i) (Q i P) y e :=
    fun i P => hF.occ _ _ _ (hmem i).1 (hQp i P)
  choose u ex hu using hex
  have hunif : ∀ i P, IsPeriod (Di i) ρ P → UnifAt F (RingHom.id ℂ) ρ N (Di i) (t i) P (u i P) (ex i P) := by
    intro i P hP
    have := hu i P
    rwa [hQe i P hP] at this
  have hrefl : ∀ i, IsMarkedIsom N (Di i) (Di i) (t i) (t i) (LinearEquiv.refl O _) :=
    fun i => ⟨fun x y => rfl, fun a => ⟨0, by simp⟩⟩
  have cmpEq : ∀ (D' D'' : PLat O bar) (t' : Λ → D'.La) (t'' : Λ → D''.La) (P : D'.La →+ (Fin g → ℂ))
      (P' : D''.La →+ (Fin g → ℂ)) (y y' : Sp ℂ ⟶ F.X) (e : (Fin g → ℂ) → (Over.mk y ⟶ F.A))
      (e' : (Fin g → ℂ) → (Over.mk y' ⟶ F.A)), y = y' →
      UnifAt F (RingHom.id ℂ) ρ N D' t' P y e → UnifAt F (RingHom.id ℂ) ρ N D'' t'' P' y' e' →
      ∃ (w : D'.La ≃ₗ[O] D''.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
        IsMarkedIsom N D' D'' t' t'' w ∧ ∀ x, P' (w x) = h (P x) := by
    intro D' D'' t' t'' P P' y y' e e' hy h1 h2
    subst hy
    obtain ⟨w, h, hw, hP, -⟩ := GlobalTheory.T.complexUniformisations_same_point_differ_by_isometry O bar g ρ ℂ (RingHom.id ℂ) Λ F N D' D'' t' t'' P P' y e e' hN0 h1 h2
    exact ⟨w, h, hw, hP⟩
  refine ⟨{
      n := n
      Di := Di
      t := t
      mem := fun i => (hmem i).1
      ne := fun i => (hmem i).2
      all := hall
      distinct := hdist
      u := u
      ex := ex
      unif := hunif
      onto := ?_
      disj := ?_
      fibre := ?_
      hol := ?_
      lift := ?_ }⟩
  · intro y hy
    obtain ⟨D', t', P, e, hC, hU⟩ := hF.pts y hy
    obtain ⟨i, w, hw⟩ := hall D' t' hC ⟨P, hU.2.1⟩
    have hP' := isPeriod_comp_isometry_symm D' (Di i) w hw.1 P hU.2.1
    refine ⟨i, _, hP', ?_⟩
    exact (hF.sep D' (Di i) t' (t i) P _ y _ e (ex i _) hU (hunif i _ hP') w (LinearEquiv.refl ℂ _) hw
      (fun x => by simp)).symm
  · intro i j P P' hP hP' huu
    obtain ⟨w, h, hw, -⟩ := cmpEq _ _ _ _ _ _ _ _ _ _ huu (hunif i P hP) (hunif j P' hP')
    exact hdist i j w hw
  · intro i P P' hP hP'
    constructor
    · intro huu
      exact cmpEq _ _ _ _ _ _ _ _ _ _ huu (hunif i P hP) (hunif i P' hP')
    · rintro ⟨w, h, hw, hPw⟩
      exact hF.sep _ _ _ _ _ _ _ _ _ _ (hunif i P hP) (hunif i P' hP') w h hw hPw
  · intro i m B P hB hHol
    exact GlobalTheory.T.basePoint_and_exponential_holomorphic_in_periods O bar g ρ Λ F N C d (Di i) (t i) m B P (fun b => u i (P b)) (fun b => ex i (P b)) hN heta hsm
      hqc hF (hmem i).1 (hfull _ _ (hmem i).1) hB hHol (fun b hb => hunif i (P b) (hHol.1 b hb))
  · intro m B y hB hy hhol b₀ hb₀
    obtain ⟨D', t', P, e, hC, hU⟩ := hF.pts (y b₀) (hy b₀ hb₀)
    obtain ⟨i, w, hw⟩ := hall D' t' hC ⟨P, hU.2.1⟩
    have hP' := isPeriod_comp_isometry_symm D' (Di i) w hw.1 P hU.2.1
    have hU' := GlobalTheory.T.uniformisationAt_transport_isometry O bar g ρ ℂ (RingHom.id ℂ) Λ F N D' (Di i) t' (t i) P _ (y b₀) e w
      (LinearEquiv.refl ℂ _) hN0 hU hw (fun x => by simp) hP'
    obtain ⟨B', P₁, e₁, hB', hb₀', hBB, -, hHol, -, hU₁⟩ :=
      GlobalTheory.T.holomorphicMap_lifts_locally_to_periodFamilies O bar g ρ Λ F N (Di i) (t i) m B y b₀ _ _ hN0 heta hlft hB hb₀ hy hhol hU'
    refine ⟨B', i, P₁, hB', hb₀', hBB, hHol, fun b hb => ?_⟩
    exact hF.sep _ _ _ _ _ _ _ _ _ _ (hunif i (P₁ b) (hHol.1 b hb)) (hU₁ b hb) (LinearEquiv.refl O _)
      (LinearEquiv.refl ℂ _) (hrefl i) (fun x => rfl)

end GlobalTheory.PELU
