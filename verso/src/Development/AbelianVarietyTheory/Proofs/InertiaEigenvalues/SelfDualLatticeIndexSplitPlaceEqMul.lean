import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdxAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexUpLatEqSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralTensorAdelesEqAdelicCompletionOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU

noncomputable section
namespace GlobalTheory.SplitLatIdx

/- English proof (translation)
Rewrite using `[← AddSubgroup.relIndex_comap ((A.map φ).map pr) pr A, ← AddSubgroup.inf_relIndex_right (A.map φ) A, ← AddSubgroup.inf_relIndex_right (((A.map φ).map pr).comap pr) A]`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [AddSubgroup.mem_inf, AddSubgroup.mem_comap]`. Use `⟨fun h => ⟨⟨x, h.1, rfl⟩, h.2⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨⟨y, ⟨a, ha, rfl⟩, hy⟩, hx⟩`. Use `⟨⟨a + (x - φ a), ?_, ?_⟩, hx⟩` and prove the remaining obligations. Establish `hPz : P (x - φ a) = 0` using `hK _ (by rw [map_sub, hy, sub_self])`. Establish `hz : x - φ a = (x - P x) - (a - P a)`. Combine the equalities or inequalities in the displayed calculation.

Use `add_mem ha ?_` and prove the remaining obligations. Rewrite using `[hz]`. Conclude with `sub_mem (sub_mem hx (hPA x hx)) (sub_mem ha (hPA a ha))`. Establish `hPz : P (x - φ a) = 0` using `hK _ (by rw [map_sub, hy, sub_self])`. Establish `h1` using `hφ (x - φ a)`.

Simplify using `only [hc, hPz, map_zero, sub_zero] at h1`. Rewrite using `[map_add, h1]`. Normalize the expressions using the abelian group laws.
-/
theorem relIndex_map_of_proj {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (A : AddSubgroup X) (φ P : X →+ X)
    (pr : X →+ Y) (hK : ∀ x, pr x = 0 → P x = 0) (hPA : ∀ a ∈ A, P a ∈ A)
    (hφ : ∀ x, φ x - P (φ x) = x - P x) (hc : ∀ x, P (φ x) = φ (P x)) :
    (A.map φ).relIndex A = ((A.map φ).map pr).relIndex (A.map pr) := by
  rw [← AddSubgroup.relIndex_comap ((A.map φ).map pr) pr A, ← AddSubgroup.inf_relIndex_right (A.map φ) A,
    ← AddSubgroup.inf_relIndex_right (((A.map φ).map pr).comap pr) A]
  congr 1
  ext x
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_comap]
  refine ⟨fun h => ⟨⟨x, h.1, rfl⟩, h.2⟩, ?_⟩
  rintro ⟨⟨y, ⟨a, ha, rfl⟩, hy⟩, hx⟩
  refine ⟨⟨a + (x - φ a), ?_, ?_⟩, hx⟩
  · have hPz : P (x - φ a) = 0 := hK _ (by rw [map_sub, hy, sub_self])
    have hz : x - φ a = (x - P x) - (a - P a) := by
      calc x - φ a = (x - φ a) - P (x - φ a) := by rw [hPz, sub_zero]
        _ = (x - P x) - (φ a - P (φ a)) := by rw [map_sub]; abel
        _ = _ := by rw [hφ a]
    refine add_mem ha ?_
    rw [hz]
    exact sub_mem (sub_mem hx (hPA x hx)) (sub_mem ha (hPA a ha))
  · have hPz : P (x - φ a) = 0 := hK _ (by rw [map_sub, hy, sub_self])
    have h1 := hφ (x - φ a)
    simp only [hc, hPz, map_zero, sub_zero] at h1
    rw [map_add, h1]
    abel

end GlobalTheory.SplitLatIdx

namespace GlobalTheory.SplitLatIdx

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `D T v w w' h h' hv hne g`. Take `⟨w'', -, hu, -⟩` from `GlobalTheory.LFun.SplitChart.exists_conj_place (isCMExt_host D) h hv`. Establish `hover : ∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v → u = w ∨ u = w'`. Introduce `u hu0`. Break down `(hu u).1 hu0 with e | e` into its components or cases.

Conclude with `Or.inl e`. Break down `(hu w').1 h' with e' | e'` into its components or cases. Conclude with `absurd e'.symm hne`. Conclude with `Or.inr (e.trans e'.symm)`. Use `set M := finMat D.sp.cm.sig T.gram (GlobalTheory.FinZeta.embV T v g) with hMdef`.

Establish `hcomp : ∀ (u : HeightOneSpectrum (𝓞 D.host.E)) (y : Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) (i : Fin T.rank), GlobalTheory.LFun.compAt D.host.F u ((M *ᵥ y) i) = (M.map (GlobalTheory.LFun.compAt D.host.F u) *ᵥ fun j …` using `fun u y i => RingHom.map_mulVec _ M y i`. Establish `hMw : ∀ (u : HeightOneSpectrum (𝓞 D.host.E)) (hh : u.under (𝓞 D.host.F) = v), M.map (GlobalTheory.LFun.compAt D.host.F u) = (GlobalTheory.LFun.locMat D.sp.cm.sig T.gram hh g).1`. Introduce `u hh`. Establish `e` using `GlobalTheory.LFun.finMat_map_compAt D.sp.cm.sig T.gram hh (GlobalTheory.FinZeta.embV T v g)`. Rewrite `e` using `[proj_emb_self]`.

Conclude with `e`. Establish `hMu : ∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) ≠ v → M.map (GlobalTheory.LFun.compAt D.host.F u) = 1`. Introduce `u hh`. Establish `e` using `GlobalTheory.LFun.finMat_map_compAt D.sp.cm.sig T.gram (rfl : u.under (𝓞 D.host.F) = _) (GlobalTheory.FinZeta.embV T v g)`. Rewrite `e` using `[proj_emb_ne _ _ hh, map_one, Units.val_one]`.

Conclude with `e`. Use `set ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E := GlobalTheory.LFun.singleAt D.host.F w 1 + GlobalTheory.LFun.singleAt D.host.F w' 1 with hεdef`. Establish `hεw : GlobalTheory.LFun.compAt D.host.F w ε = 1`. Rewrite using `[hεdef, map_add, GlobalTheory.LFun.compAt_singleAt, GlobalTheory.LFun.compAt_singleAt_ne hne, add_zero]`. Establish `hεw' : GlobalTheory.LFun.compAt D.host.F w' ε = 1`.

Rewrite using `[hεdef, map_add, GlobalTheory.LFun.compAt_singleAt, GlobalTheory.LFun.compAt_singleAt_ne (Ne.symm hne), zero_add]`. Establish `hεu : ∀ u, u ≠ w → u ≠ w' → GlobalTheory.LFun.compAt D.host.F u ε = 0`. Introduce `u h1 h2`. Rewrite using `[hεdef, map_add, GlobalTheory.LFun.compAt_singleAt_ne h1, GlobalTheory.LFun.compAt_singleAt_ne h2, add_zero]`. Establish `hεint : ε ∈ intAE D` using `add_mem (GlobalTheory.LFun.singleAt_mem_intAE (one_mem _)) (GlobalTheory.LFun.singleAt_mem_intAE (one_mem _))`.

Apply the tactic sequence `let pr : (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin T.rank → w.adicCompletion D.host.E) × (Fin T.rank → w'.adicCompletion D.host.E) := AddMonoidHom.mk' (fun x => (fun i => GlobalTheory.LFun.compAt D.host.F w ( …`. Set `P : (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)` to `AddMonoidHom.mk' (fun x i => ε * x i) (fun x y => by funext i; simp [mul_add])`. Set `φ` to `M.mulVecLin.toAddMonoidHom`. Establish `hφa : ∀ x, φ x = M *ᵥ x` using `fun x => rfl`. Establish `hK : ∀ x, pr x = 0 → P x = 0`.

Introduce `x hx`. Establish `h1 : ∀ i, GlobalTheory.LFun.compAt D.host.F w (x i) = 0` using `fun i => congrFun (congrArg Prod.fst hx) i`. Establish `h2 : ∀ i, GlobalTheory.LFun.compAt D.host.F w' (x i) = 0` using `fun i => congrFun (congrArg Prod.snd hx) i`. Use function extensionality and compare the values at `i`. Use `GlobalTheory.LFun.compAt_ext fun u => ?_` and prove the remaining obligations.

Use `show GlobalTheory.LFun.compAt D.host.F u (ε * x i) = GlobalTheory.LFun.compAt D.host.F u 0`. Rewrite using `[map_mul, map_zero]`. Distinguish the cases in `e1 : u = w`. Substitute `e1` using the available equality. Rewrite using `[h1 i, mul_zero]`.

Distinguish the cases in `e2 : u = w'`. Substitute `e2` using the available equality. Rewrite using `[h2 i, mul_zero]`. Rewrite using `[hεu u e1 e2, zero_mul]`. Establish `hPA : ∀ a ∈ Formalism.L2.NTheta.LamHat T, P a ∈ Formalism.L2.NTheta.LamHat T` using `fun a ha => (GlobalTheory.LatDual.lamHat_selfDual_and_module T).2 ε hεint a ha`.

Establish `hφ : ∀ x, φ x - P (φ x) = x - P x`. Introduce `x`. Use function extensionality and compare the values at `i`. Use `GlobalTheory.LFun.compAt_ext fun u => ?_` and prove the remaining obligations. Use `show GlobalTheory.LFun.compAt D.host.F u ((M *ᵥ x) i - ε * (M *ᵥ x) i) = GlobalTheory.LFun.compAt D.host.F u (x i - ε * x i)`.

Rewrite using `[map_sub, map_sub, map_mul, map_mul]`. Distinguish the cases in `e : u = w ∨ u = w'`. Establish `: GlobalTheory.LFun.compAt D.host.F u ε = 1` using `by rcases e with rfl | rfl; exacts [hεw, hεw']`. Rewrite using `[this, one_mul, one_mul, sub_self, sub_self]`. Use `push_neg at e`.

Apply the tactic sequence `have hv' : u.under (𝓞 D.host.F) ≠ v := fun hh => by rcases hover u hh with e' | e' <;> [exact e.1 e'; exact e.2 e']`. Rewrite using `[hεu u e.1 e.2, zero_mul, zero_mul, hcomp, hMu u hv', Matrix.one_mulVec]`. Establish `hc : ∀ x, P (φ x) = φ (P x)`. Introduce `x`. Use `show (fun i => ε * (M *ᵥ x) i) = M *ᵥ (fun j => ε * x j)`.

Establish `e : (fun j => ε * x j) = ε • x` using `rfl`. Rewrite using `[e, Matrix.mulVec_smul]`. Both sides reduce to the same expression. Establish `hprφ : ∀ y, pr (φ y) = ((GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g).1 *ᵥ fun i => GlobalTheory.LFun.compAt D.host.F w (y i), (GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h' g).1 *ᵥ fun i => GlobalTheory.LFun.compAt D.host.F w' (y i))`. Introduce `y`.

Use `Prod.ext (funext fun i => ?_) (funext fun i => ?_)` and prove the remaining obligations. Use `show GlobalTheory.LFun.compAt D.host.F w ((M *ᵥ y) i) = _`. Rewrite using `[hcomp, hMw w h]`. Use `show GlobalTheory.LFun.compAt D.host.F w' ((M *ᵥ y) i) = _`. Rewrite using `[hcomp, hMw w' h']`.

Establish `hsg : ∀ (x : Fin T.rank → w.adicCompletion D.host.E) (x' : Fin T.rank → w'.adicCompletion D.host.E), pr (fun i => GlobalTheory.LFun.singleAt D.host.F w (x i) + GlobalTheory.LFun.singleAt D.host.F w' (x' i)) = (x, x')`. Introduce `x x'`. Use `Prod.ext (funext fun i => ?_) (funext fun i => ?_)` and prove the remaining obligations. Use `show GlobalTheory.LFun.compAt D.host.F w (GlobalTheory.LFun.singleAt D.host.F w (x i) + GlobalTheory.LFun.singleAt D.host.F w' (x' i)) = x i`. Rewrite using `[map_add, GlobalTheory.LFun.compAt_singleAt, GlobalTheory.LFun.compAt_singleAt_ne hne, add_zero]`.

Use `show GlobalTheory.LFun.compAt D.host.F w' (GlobalTheory.LFun.singleAt D.host.F w (x i) + GlobalTheory.LFun.singleAt D.host.F w' (x' i)) = x' i`. Rewrite using `[map_add, GlobalTheory.LFun.compAt_singleAt, GlobalTheory.LFun.compAt_singleAt_ne (Ne.symm hne), zero_add]`. Establish `hsgm : ∀ (x : Fin T.rank → w.adicCompletion D.host.E) (x' : Fin T.rank → w'.adicCompletion D.host.E), x ∈ GlobalTheory.LFun.latAt w (frameLat T) → x' ∈ GlobalTheory.LFun.latAt w' (frameLat T) → (fun i => GlobalTheory.LFun.singleAt D.host.F w (x i) + GlobalTheory.LFun.singleAt D.h …` using `fun x x' hx hx' => add_mem (GlobalTheory.LFun.singleAt_mem_lamHat hx) (GlobalTheory.LFun.singleAt_mem_lamHat hx')`. Establish `hmem : ∀ (u : HeightOneSpectrum (𝓞 D.host.E)) y, y ∈ Formalism.L2.NTheta.LamHat T → (fun i => GlobalTheory.LFun.compAt D.host.F u (y i)) ∈ GlobalTheory.LFun.latAt u (frameLat T)` using `fun u y hy => GlobalTheory.LFun.compAt_mem_latAt u (hermitianSpaceBaseLattice_eq_frameLattice T ▸ hy)`. Establish `hA : (Formalism.L2.NTheta.LamHat T).map pr = (GlobalTheory.LFun.latAt w (frameLat T)).toAddSubgroup.prod (GlobalTheory.LFun.latAt w' (frameLat T)).toAddSubgroup`.

Use extensionality with `⟨x, x'⟩`. Simplify using `only [AddSubgroup.mem_map, AddSubgroup.mem_prod, Submodule.mem_toAddSubgroup]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hxy⟩`. Establish `e1 : (fun i => GlobalTheory.LFun.compAt D.host.F w (y i)) = x` using `congrArg Prod.fst hxy`.

Establish `e2 : (fun i => GlobalTheory.LFun.compAt D.host.F w' (y i)) = x'` using `congrArg Prod.snd hxy`. Substitute `e1 e2` using the available equality. Conclude with `⟨hmem w y hy, hmem w' y hy⟩`. Introduce and unpack `⟨hx, hx'⟩`. Conclude with `⟨_, hsgm x x' hx hx', hsg x x'⟩`.

Establish `hB : ((Formalism.L2.NTheta.LamHat T).map φ).map pr = ((GlobalTheory.LFun.latAt w (frameLat T)).toAddSubgroup.map (GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g).1.mulVecLin.toAddMonoidHom).prod ((GlobalTheory.LFun.latAt w' (frameLat T)).toAddSubgroup.map (GlobalTheory.LFun.locM …`. Use extensionality with `⟨x, x'⟩`. Simplify using `only [AddSubgroup.mem_map, AddSubgroup.mem_prod, Submodule.mem_toAddSubgroup]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, ⟨a, ha, rfl⟩, hxy⟩`.

Rewrite `hxy` using `[hprφ]`. Take `⟨rfl, rfl⟩` from `Prod.mk.inj hxy`. Conclude with `⟨⟨_, hmem w a ha, rfl⟩, ⟨_, hmem w' a ha, rfl⟩⟩`. Introduce and unpack `⟨⟨b, hb, rfl⟩, ⟨b', hb', rfl⟩⟩`. Use `⟨φ _, ⟨_, hsgm b b' hb hb', rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hprφ]`. Establish `e` using `hsg b b'`. Simplify using `only [pr, AddMonoidHom.mk'_apply, Prod.mk.injEq] at e`. Rewrite using `[e.1, e.2]`. Both sides reduce to the same expression.

Use `show ((Formalism.L2.NTheta.LamHat T).map φ).relIndex (Formalism.L2.NTheta.LamHat T) = _`. Rewrite using `[relIndex_map_of_proj _ φ P pr hK hPA hφ hc, hA, hB, GlobalTheory.BorelUMod.relIndex_prod_prod]`. Both sides reduce to the same expression.
-/
theorem latIndex_split : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w w' : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (h' : w'.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → w ≠ w' → ∀ g : GlobalTheory.FinZeta.Gv T v, latIndex T (GlobalTheory.FinZeta.embV T v g) = GlobalTheory.LocKerMod.idxAt T w h g * GlobalTheory.LocKerMod.idxAt T w' h' g := by
  intro D T v w w' h h' hv hne g
  classical
  obtain ⟨w'', -, hu, -⟩ := GlobalTheory.LFun.SplitChart.exists_conj_place (isCMExt_host D) h hv
  have hover : ∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v → u = w ∨ u = w' := by
    intro u hu0
    rcases (hu u).1 hu0 with e | e
    · exact Or.inl e
    · rcases (hu w').1 h' with e' | e'
      · exact absurd e'.symm hne
      · exact Or.inr (e.trans e'.symm)
  set M := finMat D.sp.cm.sig T.gram (GlobalTheory.FinZeta.embV T v g) with hMdef
  have hcomp : ∀ (u : HeightOneSpectrum (𝓞 D.host.E)) (y : Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) (i : Fin T.rank),
      GlobalTheory.LFun.compAt D.host.F u ((M *ᵥ y) i) = (M.map (GlobalTheory.LFun.compAt D.host.F u) *ᵥ fun j => GlobalTheory.LFun.compAt D.host.F u (y j)) i :=
    fun u y i => RingHom.map_mulVec _ M y i
  have hMw : ∀ (u : HeightOneSpectrum (𝓞 D.host.E)) (hh : u.under (𝓞 D.host.F) = v),
      M.map (GlobalTheory.LFun.compAt D.host.F u) = (GlobalTheory.LFun.locMat D.sp.cm.sig T.gram hh g).1 := by
    intro u hh
    have e := GlobalTheory.LFun.finMat_map_compAt D.sp.cm.sig T.gram hh (GlobalTheory.FinZeta.embV T v g)
    rw [proj_emb_self] at e
    exact e
  have hMu : ∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) ≠ v → M.map (GlobalTheory.LFun.compAt D.host.F u) = 1 := by
    intro u hh
    have e := GlobalTheory.LFun.finMat_map_compAt D.sp.cm.sig T.gram (rfl : u.under (𝓞 D.host.F) = _) (GlobalTheory.FinZeta.embV T v g)
    rw [proj_emb_ne _ _ hh, map_one, Units.val_one] at e
    exact e
  set ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E := GlobalTheory.LFun.singleAt D.host.F w 1 + GlobalTheory.LFun.singleAt D.host.F w' 1 with hεdef
  have hεw : GlobalTheory.LFun.compAt D.host.F w ε = 1 := by
    rw [hεdef, map_add, GlobalTheory.LFun.compAt_singleAt, GlobalTheory.LFun.compAt_singleAt_ne hne, add_zero]
  have hεw' : GlobalTheory.LFun.compAt D.host.F w' ε = 1 := by
    rw [hεdef, map_add, GlobalTheory.LFun.compAt_singleAt, GlobalTheory.LFun.compAt_singleAt_ne (Ne.symm hne), zero_add]
  have hεu : ∀ u, u ≠ w → u ≠ w' → GlobalTheory.LFun.compAt D.host.F u ε = 0 := by
    intro u h1 h2
    rw [hεdef, map_add, GlobalTheory.LFun.compAt_singleAt_ne h1, GlobalTheory.LFun.compAt_singleAt_ne h2, add_zero]
  have hεint : ε ∈ intAE D :=
    add_mem (GlobalTheory.LFun.singleAt_mem_intAE (one_mem _)) (GlobalTheory.LFun.singleAt_mem_intAE (one_mem _))
  let pr : (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+
      (Fin T.rank → w.adicCompletion D.host.E) × (Fin T.rank → w'.adicCompletion D.host.E) :=
    AddMonoidHom.mk' (fun x => (fun i => GlobalTheory.LFun.compAt D.host.F w (x i), fun i => GlobalTheory.LFun.compAt D.host.F w' (x i)))
      (fun x y => by ext i <;> simp)
  let P : (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    AddMonoidHom.mk' (fun x i => ε * x i) (fun x y => by funext i; simp [mul_add])
  let φ := M.mulVecLin.toAddMonoidHom
  have hφa : ∀ x, φ x = M *ᵥ x := fun x => rfl
  have hK : ∀ x, pr x = 0 → P x = 0 := by
    intro x hx
    have h1 : ∀ i, GlobalTheory.LFun.compAt D.host.F w (x i) = 0 := fun i => congrFun (congrArg Prod.fst hx) i
    have h2 : ∀ i, GlobalTheory.LFun.compAt D.host.F w' (x i) = 0 := fun i => congrFun (congrArg Prod.snd hx) i
    funext i
    refine GlobalTheory.LFun.compAt_ext fun u => ?_
    show GlobalTheory.LFun.compAt D.host.F u (ε * x i) = GlobalTheory.LFun.compAt D.host.F u 0
    rw [map_mul, map_zero]
    by_cases e1 : u = w
    · subst e1; rw [h1 i, mul_zero]
    by_cases e2 : u = w'
    · subst e2; rw [h2 i, mul_zero]
    rw [hεu u e1 e2, zero_mul]
  have hPA : ∀ a ∈ Formalism.L2.NTheta.LamHat T, P a ∈ Formalism.L2.NTheta.LamHat T :=
    fun a ha => (GlobalTheory.LatDual.lamHat_selfDual_and_module T).2 ε hεint a ha
  have hφ : ∀ x, φ x - P (φ x) = x - P x := by
    intro x
    funext i
    refine GlobalTheory.LFun.compAt_ext fun u => ?_
    show GlobalTheory.LFun.compAt D.host.F u ((M *ᵥ x) i - ε * (M *ᵥ x) i) = GlobalTheory.LFun.compAt D.host.F u (x i - ε * x i)
    rw [map_sub, map_sub, map_mul, map_mul]
    by_cases e : u = w ∨ u = w'
    · have : GlobalTheory.LFun.compAt D.host.F u ε = 1 := by rcases e with rfl | rfl; exacts [hεw, hεw']
      rw [this, one_mul, one_mul, sub_self, sub_self]
    · push_neg at e
      have hv' : u.under (𝓞 D.host.F) ≠ v := fun hh => by rcases hover u hh with e' | e' <;> [exact e.1 e'; exact e.2 e']
      rw [hεu u e.1 e.2, zero_mul, zero_mul, hcomp, hMu u hv', Matrix.one_mulVec]
  have hc : ∀ x, P (φ x) = φ (P x) := by
    intro x
    show (fun i => ε * (M *ᵥ x) i) = M *ᵥ (fun j => ε * x j)
    have e : (fun j => ε * x j) = ε • x := rfl
    rw [e, Matrix.mulVec_smul]
    rfl
  have hprφ : ∀ y, pr (φ y) = ((GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g).1 *ᵥ fun i => GlobalTheory.LFun.compAt D.host.F w (y i),
      (GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h' g).1 *ᵥ fun i => GlobalTheory.LFun.compAt D.host.F w' (y i)) := by
    intro y
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · show GlobalTheory.LFun.compAt D.host.F w ((M *ᵥ y) i) = _
      rw [hcomp, hMw w h]
    · show GlobalTheory.LFun.compAt D.host.F w' ((M *ᵥ y) i) = _
      rw [hcomp, hMw w' h']
  have hsg : ∀ (x : Fin T.rank → w.adicCompletion D.host.E) (x' : Fin T.rank → w'.adicCompletion D.host.E),
      pr (fun i => GlobalTheory.LFun.singleAt D.host.F w (x i) + GlobalTheory.LFun.singleAt D.host.F w' (x' i)) = (x, x') := by
    intro x x'
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · show GlobalTheory.LFun.compAt D.host.F w (GlobalTheory.LFun.singleAt D.host.F w (x i) + GlobalTheory.LFun.singleAt D.host.F w' (x' i)) = x i
      rw [map_add, GlobalTheory.LFun.compAt_singleAt, GlobalTheory.LFun.compAt_singleAt_ne hne, add_zero]
    · show GlobalTheory.LFun.compAt D.host.F w' (GlobalTheory.LFun.singleAt D.host.F w (x i) + GlobalTheory.LFun.singleAt D.host.F w' (x' i)) = x' i
      rw [map_add, GlobalTheory.LFun.compAt_singleAt, GlobalTheory.LFun.compAt_singleAt_ne (Ne.symm hne), zero_add]
  have hsgm : ∀ (x : Fin T.rank → w.adicCompletion D.host.E) (x' : Fin T.rank → w'.adicCompletion D.host.E),
      x ∈ GlobalTheory.LFun.latAt w (frameLat T) → x' ∈ GlobalTheory.LFun.latAt w' (frameLat T) →
      (fun i => GlobalTheory.LFun.singleAt D.host.F w (x i) + GlobalTheory.LFun.singleAt D.host.F w' (x' i)) ∈ Formalism.L2.NTheta.LamHat T :=
    fun x x' hx hx' => add_mem (GlobalTheory.LFun.singleAt_mem_lamHat hx) (GlobalTheory.LFun.singleAt_mem_lamHat hx')
  have hmem : ∀ (u : HeightOneSpectrum (𝓞 D.host.E)) y, y ∈ Formalism.L2.NTheta.LamHat T →
      (fun i => GlobalTheory.LFun.compAt D.host.F u (y i)) ∈ GlobalTheory.LFun.latAt u (frameLat T) :=
    fun u y hy => GlobalTheory.LFun.compAt_mem_latAt u (hermitianSpaceBaseLattice_eq_frameLattice T ▸ hy)
  have hA : (Formalism.L2.NTheta.LamHat T).map pr =
      (GlobalTheory.LFun.latAt w (frameLat T)).toAddSubgroup.prod (GlobalTheory.LFun.latAt w' (frameLat T)).toAddSubgroup := by
    ext ⟨x, x'⟩
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_prod, Submodule.mem_toAddSubgroup]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have e1 : (fun i => GlobalTheory.LFun.compAt D.host.F w (y i)) = x := congrArg Prod.fst hxy
      have e2 : (fun i => GlobalTheory.LFun.compAt D.host.F w' (y i)) = x' := congrArg Prod.snd hxy
      subst e1 e2
      exact ⟨hmem w y hy, hmem w' y hy⟩
    · rintro ⟨hx, hx'⟩
      exact ⟨_, hsgm x x' hx hx', hsg x x'⟩
  have hB : ((Formalism.L2.NTheta.LamHat T).map φ).map pr =
      ((GlobalTheory.LFun.latAt w (frameLat T)).toAddSubgroup.map
        (GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g).1.mulVecLin.toAddMonoidHom).prod
      ((GlobalTheory.LFun.latAt w' (frameLat T)).toAddSubgroup.map
        (GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h' g).1.mulVecLin.toAddMonoidHom) := by
    ext ⟨x, x'⟩
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_prod, Submodule.mem_toAddSubgroup]
    constructor
    · rintro ⟨y, ⟨a, ha, rfl⟩, hxy⟩
      rw [hprφ] at hxy
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxy
      exact ⟨⟨_, hmem w a ha, rfl⟩, ⟨_, hmem w' a ha, rfl⟩⟩
    · rintro ⟨⟨b, hb, rfl⟩, ⟨b', hb', rfl⟩⟩
      refine ⟨φ _, ⟨_, hsgm b b' hb hb', rfl⟩, ?_⟩
      rw [hprφ]
      have e := hsg b b'
      simp only [pr, AddMonoidHom.mk'_apply, Prod.mk.injEq] at e
      rw [e.1, e.2]
      rfl
  show ((Formalism.L2.NTheta.LamHat T).map φ).relIndex (Formalism.L2.NTheta.LamHat T) = _
  rw [relIndex_map_of_proj _ φ P pr hK hPA hφ hc, hA, hB, GlobalTheory.BorelUMod.relIndex_prod_prod]
  rfl

end GlobalTheory.SplitLatIdx
