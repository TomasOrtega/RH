import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselThetaContractionExtendByZeroVacuumSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapPreservesVacuumProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumOfVacuaIsVacuumBothStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesConsecutiveStep
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AddCharSymplecticFinitePartRestEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianAdjointSymplecticActionThetaHeisenberg
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumIsTwoVariableThetaFunction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopOrthAtEmb
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowLatticesGoodPositionLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedVacuaOfShapeProof
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct
namespace GlobalTheory.VacRealPf

variable {D : D7}

/- English proof (translation)
Establish `h0 : infPart D (e + cA D e) = 0`. Establish `h1` using `GlobalTheory.FinRestComm.infPart_of_idemSum he`. Rewrite using `[RingHom.map_add, h1, GlobalTheory.AdjointPair.infPart_zero e h1, add_zero]`. Use `show g ∈ (infHom V).ker`. Rewrite using `[MonoidHom.mem_ker]`.

Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Establish `h1` using `congrArg (infPart D) (hs i j)`. Rewrite `h1` using `[map_mul, h0, zero_mul]`. Establish `e : (infHom V g).1 i j = infPart D (mt V g i j)` using `rfl`.

Express the relevant statement in the definitionally equal form `(infHom V g).1 i j = (1 : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)).1 i j`. Rewrite using `[e, Units.val_one]`. Establish `h2 : infPart D ((mt V g - 1) i j) = infPart D (mt V g i j) - (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j`. Rewrite using `[Matrix.sub_apply, RingHom.map_sub]`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Rewrite using `[Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]`. Rewrite using `[Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, RingHom.map_zero]`. Rewrite `h1` using `[h2]`. Conclude with `sub_eq_zero.1 h1.symm`.
-/
theorem mem_GfC_of_idemSum {e : AE D} {Q : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e Q) {V : HSp D} {g : GA D V}
    (hs : SuppAt e V g) : g ∈ GfC V := by
  have h0 : infPart D (e + cA D e) = 0 := by
    have h1 := GlobalTheory.FinRestComm.infPart_of_idemSum he
    rw [RingHom.map_add, h1, GlobalTheory.AdjointPair.infPart_zero e h1, add_zero]
  show g ∈ (infHom V).ker
  rw [MonoidHom.mem_ker]
  apply Units.ext
  ext i j
  have h1 := congrArg (infPart D) (hs i j)
  rw [map_mul, h0, zero_mul] at h1
  have e : (infHom V g).1 i j = infPart D (mt V g i j) := rfl
  change (infHom V g).1 i j = (1 : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)).1 i j
  rw [e, Units.val_one]
  have h2 : infPart D ((mt V g - 1) i j) = infPart D (mt V g i j) - (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j := by
    rw [Matrix.sub_apply, RingHom.map_sub]
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, RingHom.map_zero]
  rw [h2] at h1
  exact sub_eq_zero.1 h1.symm

/- English proof (translation)
Introduce `y _`. Rewrite using `[show mt S 1 = 1 from rfl, Matrix.one_mulVec]`.
-/
theorem moves_one (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (P : GlobalTheory.FinPl.Pl D → Prop) : GlobalTheory.FinPl.Moves S 1 L L P := by
  intro y _
  rw [show mt S 1 = 1 from rfl, Matrix.one_mulVec]

/- English proof (translation)
Use `D.R.two_le_m` as an intermediate fact. Simplify using `only [idx, List.mem_range'_1]`. Use linear arithmetic over natural numbers and integers.
-/
theorem mem_idx {j : ℕ} : j ∈ idx D ↔ 1 ≤ j ∧ j + 2 ≤ D.R.m := by
  have := D.R.two_le_m
  simp only [idx, List.mem_range'_1]
  omega

section
variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

/- English proof (translation)
Distinguish the cases in `h0 : j = 0`. Substitute `h0` using the available equality. Take `⟨e, he, hs, -⟩` from `hb.1`. Conclude with `mem_GfC_of_idemSum he hs`. Distinguish the cases in `hj : j ∈ idx D`.

Take `⟨δ, -, hδ⟩` from `hb.2.1 j hj`. Conclude with `hδ.1`. Rewrite using `[hb.2.2 j h0 hj]`. Conclude with `one_mem _`.
-/
theorem base_fin {t : T} {b : Pts ch.G} (hb : IsBase t ch.S.B b) (j : ℕ) : b j ∈ GfC _ := by
  by_cases h0 : j = 0
  · subst h0
    obtain ⟨e, he, hs, -⟩ := hb.1
    exact mem_GfC_of_idemSum he hs
  · by_cases hj : j ∈ idx D
    · obtain ⟨δ, -, hδ⟩ := hb.2.1 j hj
      exact hδ.1
    · rw [hb.2.2 j h0 hj]; exact one_mem _

/- English proof (translation)
The claim follows from `(ch.G.isV (X := .grid D.R.m j) ⟨le_rfl, hj⟩ fun i e => by have := D.R.two_le_m injection e with e1 omega).sd`.
-/
theorem sd_grid (j : ℕ) (hj : j ≤ D.R.m) : IsSelfDualC _ (ch.G.Λ (.grid D.R.m j)) :=
  (ch.G.isV (X := .grid D.R.m j) ⟨le_rfl, hj⟩ fun i e => by
    have := D.R.two_le_m
    injection e with e1
    omega).sd

/- English proof (translation)
The claim follows from `(ch.G.isV (X := .top j) hj fun i e => by cases e).sd`.
-/
theorem sd_top (j : ℕ) (hj : j ≤ D.R.m) : IsSelfDualC _ (ch.G.Λ (.top j)) :=
  (ch.G.isV (X := .top j) hj fun i e => by cases e).sd

/- English proof (translation)
The claim follows from `(GlobalTheory.StepMove.gen (ch.W.om_is (.mu t D.R.m j) ⟨le_rfl, hj⟩) (sd_grid ch j hj.le) hM (sd_grid ch (j + 1) hj) hM' hg hh mg mh _ _ (ch.rm.vT_is t D.R.m j le_rfl hj)).1 _ x hx y hy`.
-/
theorem fock_vac (t : T) (j : ℕ) (hj : j < D.R.m) (P : PolDown ch.G) {M : GlobalTheory.FinPl.Lat (ch.G.V (.grid D.R.m j))}
    {M' : GlobalTheory.FinPl.Lat (ch.G.V (.grid D.R.m (j + 1)))} (hM : IsSelfDualC _ M) (hM' : IsSelfDualC _ M')
    {g : GA D (ch.G.V (.grid D.R.m j))} {h : GA D (ch.G.V (.grid D.R.m (j + 1)))} (hg : g ∈ GfC _) (hh : h ∈ GfC _)
    (mg : GlobalTheory.FinPl.Moves _ g (ch.G.Λ (.grid D.R.m j)) M fun _ => True)
    (mh : GlobalTheory.FinPl.Moves _ h (ch.G.Λ (.grid D.R.m (j + 1))) M' fun _ => True)
    {x : GA D (ch.G.V (.grid D.R.m j))} {y : GA D (ch.G.V (.grid D.R.m (j + 1)))} (hx : x ∈ GinfC _) (hy : y ∈ GinfC _) :
    GlobalTheory.FinPl.Vac ch.W.ψ (ch.G.V (.grid D.R.m j)) (ch.G.V (.grid D.R.m (j + 1))) M M' (fun _ => True)
      (ch.W.om (.mu t D.R.m j) (x * g, y * h) (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P ⟨j, hj⟩)) :=
  (GlobalTheory.StepMove.gen (ch.W.om_is (.mu t D.R.m j) ⟨le_rfl, hj⟩) (sd_grid ch j hj.le) hM (sd_grid ch (j + 1) hj) hM' hg hh mg mh _ _
    (ch.rm.vT_is t D.R.m j le_rfl hj)).1 _ x hx y hy

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨h.cont, h'.1, h'.2⟩, h.smooth⟩`.
-/
theorem real_of {ψ : AddChar (AF D.host.F) ℂ} {X S X' : HSp D} {LA : GlobalTheory.FinPl.Lat X} {LS : GlobalTheory.FinPl.Lat S}
    {LA' : GlobalTheory.FinPl.Lat X'} {C : WO X S → WO S X' → ℂ} (h : IsBiTheta ψ X S X' C)
    (h' : GlobalTheory.FinPl.BiVacAt ψ LA LS LA' (fun _ => True) C) :
    IsBiVac ψ X S X' (LA : Set _) (LS : Set _) (LA' : Set _) C ∧ IsBiSmooth C :=
  ⟨⟨h.cont, h'.1, h'.2⟩, h.smooth⟩

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `hf`.
-/
theorem vac_cast {V : HSp D} {LV : GlobalTheory.FinPl.Lat V} {n n' : ℕ} (h : n = n') {f : WO V (ch.G.V (.grid D.R.m n)) → ℂ}
    (hf : GlobalTheory.FinPl.Vac ch.W.ψ V _ LV (ch.G.Λ (.grid D.R.m n)) (fun _ => True) f) :
    GlobalTheory.FinPl.Vac ch.W.ψ V _ LV (ch.G.Λ (.grid D.R.m n')) (fun _ => True) (castSch ch.G h f) := by
  subst h
  exact hf

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `hor`.
-/
theorem orth_cast {LZ : GlobalTheory.FinPl.Lat (pLine D)} {v : GlobalTheory.FinPl.Pl D}
    (hor : GlobalTheory.FinPl.OrthAt (topOrth ch.G) (ch.G.Λ (.top D.R.m)) (ch.G.Λ (.grid D.R.m D.R.m)) LZ v) {n : ℕ} (h : D.R.m = n) :
    GlobalTheory.FinPl.OrthAt (topOrthAt ch.G h) (ch.G.Λ (.top n)) (ch.G.Λ (.grid D.R.m D.R.m)) LZ v := by
  subst h
  exact hor

/- English proof (translation)
Take `⟨N, N₀, LL, LZ, hmv, hLZ, hor, hall⟩` from `hsh`. Introduce `t M hM b hb P p hp j hje hjm`. Establish `hm2` using `D.R.two_le_m`. Take `⟨a, ha⟩` from `D.R.m_even`. Take `⟨c, hc⟩` from `hje`.

Establish `hψ : IsStdChar D ch.W.ψ (-1)` using `ch.W.ψ_std`. Take `⟨x₀⟩` from `GlobalTheory.SeeSaw.VacShape.nonempty_pl D`. Establish `hFV` using `GlobalTheory.T.flatMapPreservesVacuum_proof D ch.W.ψ (fun _ => True)`. Establish `hbf` using `base_fin ch hb`. Establish `hpi : ∀ k, p k ∈ GinfC _` using `hp.1`.

Unfold `conAt`. Distinguish the cases in `h0 : j + 2 * 0 + 2 = D.R.m`. Rewrite using `[dif_pos h0]`. Establish `hb1 : b (j + 1) = 1` using `hb.2.2 (j + 1) (by omega) fun h => by`. Use `(mem_idx.1 h).2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hs` using `hall t M hM j 0 h0 (GlobalTheory.Unf.Inhab.nonempty_volN _).some`. Establish `hg0` using `(hs x₀).2.2.1`. Establish `hmv1` using `hmv t b hb (j + 1) (by omega)`. Rewrite `hmv1` using `[hb1]`.

Establish `v₁` using `fock_vac ch t j (by omega) P (M := N j) (M' := N (j + 1)) hg0.sdV hg0.sdW (hbf j) (one_mem _) (hmv t b hb j (by omega)) hmv1 (hpi j) (one_mem _)`. Rewrite `v₁` using `[one_mul]`. Establish `v₂` using `fock_vac ch t (j + 1) (by omega) P (M := N (j + 1)) (M' := ch.G.Λ (.grid D.R.m (j + 1 + 1))) hg0.sdW (sd_grid ch _ (by omega)) (one_mem _) (one_mem _) hmv1 (moves_one _ _ _) (one_mem _) (one_mem _)`. Rewrite `v₂` using `[one_mul, one_mul, Prod.mk_one_one, map_one, Module.End.one_apply]`. Establish `v₃` using `vac_cast ch (show j + 1 + 1 = D.R.m by omega) v₂`.

Establish `f₁` using `hFV.1 0 _ _ (lastAt ch.G ch.W t hM j h0 (GlobalTheory.Unf.Inhab.nonempty_volN _).some).s (N j) (N₀ j) (N (j + 1)) (ch.G.Λ (.top (j + 1))) (fun x _ => (hs x).2.2.1) _ v₁`. Establish `f₂` using `hFV.2.2 _ _ _ (rowJac ch.G (j + 1) (by omega) 0 (by omega)) (N (j + 1)) (ch.G.Λ (.top (j + 1))) (ch.G.Λ (.grid D.R.m D.R.m)) hg0.sdW hg0.sdW₀ (sd_grid ch _ le_rfl) (fun x _ => (hs x).2.2.1.monoW) _ v₃`. Use `real_of ?_ ?_` and prove the remaining obligations. Conclude with `GlobalTheory.LastBiTheta.isBiTheta_lastBi D _ hψ _ _ _ _ _ _ _ _ _ _ GlobalTheory.RowChain.LastSeeSawStep.lastTau_gram _ _ f₁.1 f₂.1`. Conclude with `GlobalTheory.T.lastSeeSawDatum_of_vacua_is_vacuum_both D _ hψ _ _ _ _ _ _ _ _ _ _ rfl rfl GlobalTheory.RowChain.LastSeeSawStep.lastTau_gram (fun _ => True) (N₀ j) (ch.G.Λ (.top j)) (ch.G.Λ (.top (j + 1))) (ch.G.Λ (.top (j + 1 + 1))) (ch.G.Λ (.grid D.R.m D.R.m)) hg0.sdV₀ (sd_top c …`.

Establish `h1 : j + 2 * ((D.R.m - 4 - j) / 2 + 1) + 2 = D.R.m` using `by omega`. Rewrite using `[dif_neg h0]`. Use `erw [dif_pos h1]`. Establish `hs` using `hall t M hM j _ h1 (GlobalTheory.Unf.Inhab.nonempty_volN _).some`. Establish `hs'` using `hall t M hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some`.

Establish `had` using `fun x => (hs' x).2.2.2.1 (j + 1) rfl (by omega)`. Establish `hg0` using `(hs x₀).2.2.1`. Establish `hg1` using `had x₀`. Establish `v₁` using `fock_vac ch t j (by omega) P (M := N j) (M' := N (j + 1)) hg0.sdV hg0.sdW (hbf j) (hbf (j + 1)) (hmv t b hb j (by omega)) (hmv t b hb (j + 1) (by omega)) (hpi j) (hpi (j + 1))`. Establish `v₂` using `fock_vac ch t (j + 1) (by omega) P (M := N (j + 1)) (M' := N (j + 1 + 1)) hg0.sdW hg1.sdW (hbf (j + 1)) (hbf (j + 1 + 1)) (hmv t b hb (j + 1) (by omega)) (hmv t b hb (j + 1 + 1) (by omega)) (hpi (j + 1)) (hpi (j + 1 + 1))`.

Establish `f₁` using `hFV.1 _ (besAt ch.G hM j _ h1 (GlobalTheory.Unf.Inhab.nonempty_volN _).some) (jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega)) (stepAt ch.G ch.W t hM j (by omega) (besDecAt ch.G j _ h1) (rowJac ch.G (j + 1) (by omega) ((D.R.m - 4 - j) / 2 + 1) (by omega))) (N j) (N₀ j) …`. Establish `f₂` using `hFV.2.1 _ (jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega)) (besAt ch.G hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) (stepAt ch.G ch.W t hM (j + 1) (by omega) (rowJac ch.G (j + 1) (by omega) ((D.R.m - 4 - j) / 2 + 1) (b …`. Establish `hCC` using `GlobalTheory.T.besselThetaContraction_extendByZero_vacuum_smooth D _ hψ _ _ _ _ (linkAt hM j _ h1 (GlobalTheory.Unf.Inhab.nonempty_volN _).some (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) (ch.G.V (.top (j + 1))) ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some) _ …`. Conclude with `real_of hCC.1 (hCC.2.2 (fun _ => True) (ch.G.Λ (.top j)) (ch.G.Λ (.top (j + 1))) (ch.G.Λ (.top (j + 1 + 1))) (N₀ j) (N₀ (j + 1 + 1)) (sd_top ch _ (by omega)) hg0.sdW₀ (sd_top ch _ (by omega)) hg0.sdV₀ hg1.sdW₀ (fun x _ => ⟨⟨_, (hs x).2.1⟩, ⟨_, (hs' x).2.1⟩⟩) f₁ f₂)`.
-/
theorem vacReal_of_shape (hsh : ShapeAt ch) : VacReal ch := by
  obtain ⟨N, N₀, LL, LZ, hmv, hLZ, hor, hall⟩ := hsh
  intro t M hM b hb P p hp j hje hjm
  have hm2 := D.R.two_le_m
  obtain ⟨a, ha⟩ := D.R.m_even
  obtain ⟨c, hc⟩ := hje
  have hψ : IsStdChar D ch.W.ψ (-1) := ch.W.ψ_std
  obtain ⟨x₀⟩ := GlobalTheory.SeeSaw.VacShape.nonempty_pl D
  have hFV := GlobalTheory.T.flatMapPreservesVacuum_proof D ch.W.ψ (fun _ => True)
  have hbf := base_fin ch hb
  have hpi : ∀ k, p k ∈ GinfC _ := hp.1
  unfold conAt
  by_cases h0 : j + 2 * 0 + 2 = D.R.m
  · rw [dif_pos h0]
    have hb1 : b (j + 1) = 1 := hb.2.2 (j + 1) (by omega) fun h => by
      have := (mem_idx.1 h).2
      omega
    have hs := hall t M hM j 0 h0 (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    have hg0 := (hs x₀).2.2.1
    have hmv1 := hmv t b hb (j + 1) (by omega)
    rw [hb1] at hmv1
    have v₁ := fock_vac ch t j (by omega) P (M := N j) (M' := N (j + 1)) hg0.sdV hg0.sdW (hbf j) (one_mem _)
      (hmv t b hb j (by omega)) hmv1 (hpi j) (one_mem _)
    rw [one_mul] at v₁
    have v₂ := fock_vac ch t (j + 1) (by omega) P (M := N (j + 1)) (M' := ch.G.Λ (.grid D.R.m (j + 1 + 1))) hg0.sdW
      (sd_grid ch _ (by omega)) (one_mem _) (one_mem _) hmv1 (moves_one _ _ _) (one_mem _) (one_mem _)
    rw [one_mul, one_mul, Prod.mk_one_one, map_one, Module.End.one_apply] at v₂
    have v₃ := vac_cast ch (show j + 1 + 1 = D.R.m by omega) v₂
    have f₁ := hFV.1 0 _ _ (lastAt ch.G ch.W t hM j h0 (GlobalTheory.Unf.Inhab.nonempty_volN _).some).s (N j) (N₀ j) (N (j + 1))
      (ch.G.Λ (.top (j + 1))) (fun x _ => (hs x).2.2.1) _ v₁
    have f₂ := hFV.2.2 _ _ _ (rowJac ch.G (j + 1) (by omega) 0 (by omega)) (N (j + 1)) (ch.G.Λ (.top (j + 1)))
      (ch.G.Λ (.grid D.R.m D.R.m)) hg0.sdW hg0.sdW₀ (sd_grid ch _ le_rfl) (fun x _ => (hs x).2.2.1.monoW) _ v₃
    refine real_of ?_ ?_
    · exact GlobalTheory.LastBiTheta.isBiTheta_lastBi D _ hψ _ _ _ _ _ _ _ _ _ _ GlobalTheory.RowChain.LastSeeSawStep.lastTau_gram _ _ f₁.1 f₂.1
    · exact GlobalTheory.T.lastSeeSawDatum_of_vacua_is_vacuum_both D _ hψ _ _ _ _ _ _ _ _ _ _ rfl rfl GlobalTheory.RowChain.LastSeeSawStep.lastTau_gram (fun _ => True) (N₀ j)
        (ch.G.Λ (.top j)) (ch.G.Λ (.top (j + 1))) (ch.G.Λ (.top (j + 1 + 1))) (ch.G.Λ (.grid D.R.m D.R.m)) hg0.sdV₀
        (sd_top ch _ (by omega)) hg0.sdW₀ (sd_top ch _ (by omega)) (sd_grid ch _ le_rfl)
        (fun x _ => ⟨(hs x).2.2.1.tame, LL j, LZ, (hs x).1, hLZ, (hs x).2.1, orth_cast ch (hor x) _, (hs x).2.2.2.2.1 rfl⟩)
        _ _ f₁ f₂
  · have h1 : j + 2 * ((D.R.m - 4 - j) / 2 + 1) + 2 = D.R.m := by omega
    rw [dif_neg h0]
    erw [dif_pos h1]
    have hs := hall t M hM j _ h1 (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    have hs' := hall t M hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    have had := fun x => (hs' x).2.2.2.1 (j + 1) rfl (by omega)
    have hg0 := (hs x₀).2.2.1
    have hg1 := had x₀
    have v₁ := fock_vac ch t j (by omega) P (M := N j) (M' := N (j + 1)) hg0.sdV hg0.sdW (hbf j) (hbf (j + 1))
      (hmv t b hb j (by omega)) (hmv t b hb (j + 1) (by omega)) (hpi j) (hpi (j + 1))
    have v₂ := fock_vac ch t (j + 1) (by omega) P (M := N (j + 1)) (M' := N (j + 1 + 1)) hg0.sdW hg1.sdW (hbf (j + 1))
      (hbf (j + 1 + 1)) (hmv t b hb (j + 1) (by omega)) (hmv t b hb (j + 1 + 1) (by omega)) (hpi (j + 1)) (hpi (j + 1 + 1))
    have f₁ := hFV.1 _ (besAt ch.G hM j _ h1 (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      (jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega)) (stepAt ch.G ch.W t hM j (by omega) (besDecAt ch.G j _ h1)
      (rowJac ch.G (j + 1) (by omega) ((D.R.m - 4 - j) / 2 + 1) (by omega))) (N j) (N₀ j) (N (j + 1))
      (ch.G.Λ (.top (j + 1))) (fun x _ => (hs x).2.2.1) _ v₁
    have f₂ := hFV.2.1 _ (jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega))
      (besAt ch.G hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) (stepAt ch.G ch.W t hM (j + 1) (by omega)
      (rowJac ch.G (j + 1) (by omega) ((D.R.m - 4 - j) / 2 + 1) (by omega))
      (besDecAt ch.G (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega))) (N (j + 1)) (ch.G.Λ (.top (j + 1))) (N (j + 1 + 1))
      (N₀ (j + 1 + 1)) (fun x _ => had x) _ v₂
    have hCC := GlobalTheory.T.besselThetaContraction_extendByZero_vacuum_smooth D _ hψ _ _ _ _
      (linkAt hM j _ h1 (GlobalTheory.Unf.Inhab.nonempty_volN _).some (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      (ch.G.V (.top (j + 1))) ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some) _ _ f₁.1 f₂.1
    exact real_of hCC.1 (hCC.2.2 (fun _ => True) (ch.G.Λ (.top j)) (ch.G.Λ (.top (j + 1))) (ch.G.Λ (.top (j + 1 + 1)))
      (N₀ j) (N₀ (j + 1 + 1)) (sd_top ch _ (by omega)) hg0.sdW₀ (sd_top ch _ (by omega)) hg0.sdV₀ hg1.sdW₀
      (fun x _ => ⟨⟨_, (hs x).2.1⟩, ⟨_, (hs' x).2.1⟩⟩) f₁ f₂)

end

/- English proof (translation)
Use `GlobalTheory.RowReal.big_mono ?_ GlobalTheory.T.lastRowLatticesGoodPosition_large_depth` and prove the remaining obligations. Introduce `D Γ _ _ Pl0 T A Ks _ _ _ R ch hsh`. Conclude with `vacReal_of_shape ch hsh`.
-/
theorem vacReal : Big fun ch => VacReal ch := by
  refine GlobalTheory.RowReal.big_mono ?_ GlobalTheory.T.lastRowLatticesGoodPosition_large_depth
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch hsh
  exact vacReal_of_shape ch hsh

end GlobalTheory.VacRealPf
