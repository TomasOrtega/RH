import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFunctorialMap
import Development.WeilBound.CoreStatements.SesquilinearFractions.GLieInt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

open PositivityTheory.Xgf.isogeny_decomposition_product in
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `R V _ _ _ f n N C v B ψ χ G _ π hg hv hψ hχ hpc hpo hN hpb`. Take `⟨EBR, _, _, ⟨MBR⟩⟩` from `lieModel_exists (Sp R) B.A R (𝟙 (Sp R))`. Take `⟨EBV, _, _, ⟨MBV⟩⟩` from `lieModel_exists (Sp R) B.A V (spMap f ≫ 𝟙 (Sp R))`. Take `⟨j, hj, -⟩` from `GlobalTheory.T.lie_model_existsUnique_semilinear (Sp R) B.A R V f (𝟙 _) EBR EBV MBR MBV`. Establish `hx : spMap f ≫ 𝟙 (Sp R) = 𝟙 (Sp V) ≫ spMap f` using `by simp`.

Take `⟨MG, hMG⟩` from `(GlobalTheory.T.lie_model_pullback_equivalence (Sp R) (Sp V) B.A G (spMap f) π hpb V (𝟙 (Sp V)) EBV).1 (castM hx MBV)`. Establish `hMG' : ∀ e, (MG.pt e).left ≫ π = (MBV.pt e).left` using `fun e => (hMG e).trans (castM_left hx MBV e)`. Establish `hvt : ∀ k, IsTanAt B.A (𝟙 (Sp R)) (toAt (v k) ≫ ψ k)` using `fun k => by haveI := hψ k; exact tan_comp _ (toAt_tan (v k) ((hv k).1 0)) (ψ k)`. Use `choose eR heR using fun k => MBR.onto _ (hvt k)`. Set `EV : Fin n → EBV` to `fun k => j (eR k)`.

Establish `hlift : ∀ e, (MBV.pt (j e)).left = spMap (dualMap f) ≫ (MBR.pt e).left` using `fun e => (Category.comp_id (MBV.pt (j e)).left).symm.trans (hj e)`. Establish `hEV : ∀ k, (MBV.pt (EV k)).left = spMap (dualMap f) ≫ (v k).left ≫ (ψ k).left` using `fun k => by show (MBV.pt (j (eR k))).left = _`. Rewrite using `[hlift, heR, Over.comp_left, toAt_left]`. Use `choose EC iC mC MC bC hbC using fun k => lc (C k) (v k) (hv k) V f`. Establish `hd : ∀ k, ∃ A : EBV →ₗ[V] EC k, ∀ e, (MC k).pt (A e) = MBV.pt e ≫ χ k` using `fun k => by haveI := hχ k`.

Conclude with `(GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_diff (Sp R) B.A (C k).A V (spMap f ≫ 𝟙 (Sp R)) EBV (EC k) MBV (MC k) (χ k)).exists`. Use `choose dχ hdχ using hd`. Set `fV : Fin n → (EBV →ₗ[V] V)` to `fun k => ((bC k).coord 0).comp (dχ k)`. Establish `hval : ∀ i k, fV k (EV i) = if i = k then (N : V) else 0`. Introduce `i k`.

Establish `hleft : ((MC k).pt (dχ k (EV i))).left = spMap (dualMap f) ≫ (v i).left ≫ (ψ i ≫ χ k).left`. Rewrite using `[hdχ, Over.comp_left, hEV, Over.comp_left]`. Simplify using `only [Category.assoc]`. Use `split_ifs with hik`. Substitute `hik` using the available equality.

Establish `e2 : dχ i (EV i) = (N : V) • bC i 0`. Apply `(MC i).inj` to reduce the goal to its premises. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[hleft, hpc, (MC i).smul, hbC, pow_left (v i) (hv i) N, ← Category.assoc, bc_eps, Category.assoc]`. Simplify using `[fV, e2]`.

Establish `e2 : dχ k (EV i) = 0`. Apply `(MC k).inj` to reduce the goal to its premises. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[hleft, hpo i k hik, pt_zero, ← bc_one f]`. Use `congr 1`.

Rewrite using `[← Over.comp_left, MonObj.comp_one]`. Simplify using `[fV, e2]`. Take `⟨bB⟩` from `GlobalTheory.T.lie_model_free_of_smooth (Sp R) B.A n (hg ▸ B.smoothDim) V (spMap f ≫ 𝟙 (Sp R)) EBV MBV`. Take `⟨hli, hsp⟩` from `GlobalTheory.T.dual_family_is_basis V EBV n bB EV fV (N : V) hN hval`. Establish `bridge` using `(GlobalTheory.T.lie_model_eigenvectors_action (Sp V) V G (𝟙 (Sp V)) EBV MG).1 n`.

Use `⟨fun k => MG.pt (EV k), fun k => hMG' (EV k) ▸ hEV k, fun k => MG.tan _, fun w hw => ?_⟩` and prove the remaining obligations. Take `⟨e, rfl⟩` from `MG.onto w hw`. Establish `hmem : e ∈ Submodule.span V (Set.range EV)` using `hsp ▸ Submodule.mem_top`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun V).1 hmem`. Use `⟨c, (bridge c EV _).2 (by rw [hc]), fun c' hc' => ?_⟩` and prove the remaining obligations.

Establish `h1` using `MG.inj ((bridge c' EV _).1 hc')`. Rewrite `h1` using `[← hc]`. Establish `h2` using `Fintype.linearIndependent_iff.1 hli (c' - c) (by`. Simplify using `only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h1, sub_self])`. Use function extensionality and compare the values at `i`.

Use `h2 i` as an intermediate fact. Rewrite `this` using `[Pi.sub_apply, sub_eq_zero]`. Conclude with `this`.
-/
theorem _root_.GlobalTheory.CompanionTheory.Relay.isogeny_decomposition_product : ∀ (R V : Type) [CommRing R] [CommRing V] [IsLocalRing V] (f : R →+* V) (n N : ℕ) (C : Fin n → Out.PolAV (Sp R)) (v : ∀ k, epsR R ⟶ (C k).A) (B : Out.PolAV (Sp R)) (ψ : ∀ k, (C k).A ⟶ B.A) (χ : ∀ k, B.A ⟶ (C k).A) (G : Over (Sp V)) [GrpObj G] (π : G.left ⟶ B.A.left), B.g = n → (∀ k, IsLieBasis ![v k]) → (∀ k, IsMonHom (ψ k)) → (∀ k, IsMonHom (χ k)) → (∀ k, ψ k ≫ χ k = 𝟙 (C k).A ^ N) → (∀ k k', k ≠ k' → ψ k ≫ χ k' = 1) → IsUnit (N : V) → IsGrpPullback G B.A (spMap f) π → ∃ u : Fin n → (epsAt (𝟙 (Sp V)) ⟶ G), (∀ k, (u k).left ≫ π = spMap (dualMap f) ≫ (v k).left ≫ (ψ k).left) ∧ (∀ k, IsTanAt G _ (u k)) ∧ ∀ w, IsTanAt G _ w → ∃! cc : Fin n → V, IsComb cc u w := by
  intro R V _ _ _ f n N C v B ψ χ G _ π hg hv hψ hχ hpc hpo hN hpb
  obtain ⟨EBR, _, _, ⟨MBR⟩⟩ := lieModel_exists (Sp R) B.A R (𝟙 (Sp R))
  obtain ⟨EBV, _, _, ⟨MBV⟩⟩ := lieModel_exists (Sp R) B.A V (spMap f ≫ 𝟙 (Sp R))
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.lie_model_existsUnique_semilinear (Sp R) B.A R V f (𝟙 _) EBR EBV MBR MBV
  have hx : spMap f ≫ 𝟙 (Sp R) = 𝟙 (Sp V) ≫ spMap f := by simp
  obtain ⟨MG, hMG⟩ := (GlobalTheory.T.lie_model_pullback_equivalence (Sp R) (Sp V) B.A G (spMap f) π hpb V (𝟙 (Sp V)) EBV).1 (castM hx MBV)
  have hMG' : ∀ e, (MG.pt e).left ≫ π = (MBV.pt e).left := fun e => (hMG e).trans (castM_left hx MBV e)

  have hvt : ∀ k, IsTanAt B.A (𝟙 (Sp R)) (toAt (v k) ≫ ψ k) := fun k => by
    haveI := hψ k; exact tan_comp _ (toAt_tan (v k) ((hv k).1 0)) (ψ k)
  choose eR heR using fun k => MBR.onto _ (hvt k)
  let EV : Fin n → EBV := fun k => j (eR k)
  have hlift : ∀ e, (MBV.pt (j e)).left = spMap (dualMap f) ≫ (MBR.pt e).left := fun e =>
    (Category.comp_id (MBV.pt (j e)).left).symm.trans (hj e)
  have hEV : ∀ k, (MBV.pt (EV k)).left = spMap (dualMap f) ≫ (v k).left ≫ (ψ k).left := fun k => by
    show (MBV.pt (j (eR k))).left = _
    rw [hlift, heR, Over.comp_left, toAt_left]

  choose EC iC mC MC bC hbC using fun k => lc (C k) (v k) (hv k) V f
  have hd : ∀ k, ∃ A : EBV →ₗ[V] EC k, ∀ e, (MC k).pt (A e) = MBV.pt e ≫ χ k := fun k => by
    haveI := hχ k
    exact (GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_diff (Sp R) B.A (C k).A V (spMap f ≫ 𝟙 (Sp R)) EBV (EC k) MBV (MC k) (χ k)).exists
  choose dχ hdχ using hd
  let fV : Fin n → (EBV →ₗ[V] V) := fun k => ((bC k).coord 0).comp (dχ k)
  have hval : ∀ i k, fV k (EV i) = if i = k then (N : V) else 0 := by
    intro i k
    have hleft : ((MC k).pt (dχ k (EV i))).left = spMap (dualMap f) ≫ (v i).left ≫ (ψ i ≫ χ k).left := by
      rw [hdχ, Over.comp_left, hEV, Over.comp_left]; simp only [Category.assoc]
    split_ifs with hik
    · subst hik
      have e2 : dχ i (EV i) = (N : V) • bC i 0 := by
        apply (MC i).inj
        apply Over.OverMorphism.ext
        rw [hleft, hpc, (MC i).smul, hbC, pow_left (v i) (hv i) N, ← Category.assoc, bc_eps, Category.assoc]
      simp [fV, e2]
    · have e2 : dχ k (EV i) = 0 := by
        apply (MC k).inj
        apply Over.OverMorphism.ext
        rw [hleft, hpo i k hik, pt_zero, ← bc_one f]
        congr 1
        rw [← Over.comp_left, MonObj.comp_one]
      simp [fV, e2]
  obtain ⟨bB⟩ := GlobalTheory.T.lie_model_free_of_smooth (Sp R) B.A n (hg ▸ B.smoothDim) V (spMap f ≫ 𝟙 (Sp R)) EBV MBV
  obtain ⟨hli, hsp⟩ := GlobalTheory.T.dual_family_is_basis V EBV n bB EV fV (N : V) hN hval
  have bridge := (GlobalTheory.T.lie_model_eigenvectors_action (Sp V) V G (𝟙 (Sp V)) EBV MG).1 n
  refine ⟨fun k => MG.pt (EV k), fun k => hMG' (EV k) ▸ hEV k, fun k => MG.tan _, fun w hw => ?_⟩
  obtain ⟨e, rfl⟩ := MG.onto w hw
  have hmem : e ∈ Submodule.span V (Set.range EV) := hsp ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun V).1 hmem
  refine ⟨c, (bridge c EV _).2 (by rw [hc]), fun c' hc' => ?_⟩
  have h1 := MG.inj ((bridge c' EV _).1 hc')
  rw [← hc] at h1
  have h2 := Fintype.linearIndependent_iff.1 hli (c' - c) (by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h1, sub_self])
  funext i
  have := h2 i
  rw [Pi.sub_apply, sub_eq_zero] at this
  exact this
