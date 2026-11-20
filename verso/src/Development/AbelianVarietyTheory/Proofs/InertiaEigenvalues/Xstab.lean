import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot

noncomputable section

namespace GlobalTheory.NL.XStab

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

/- English proof (translation)
Use `W.γD_smul T g (algebraMap (LetA O n) W.EE a) x` as an intermediate fact. Rewrite `this` using `[algebraMap_smul, W.γE_ext, algebraMap_smul]`. Conclude with `this`.
-/
theorem γD_smulA (T : LocLat G Qp LL O) (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ', AlgHom.mul_apply, AlgHom.mul_apply, ih, W.φA_γA]`.
-/
theorem φpow_γA (k : ℕ) (g : W.Gam) (a : LetA O n) :
    (W.φA ^ k) (W.γA g a) = W.γA g ((W.φA ^ k) a) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', AlgHom.mul_apply, AlgHom.mul_apply, ih, W.φA_γA]

/- English proof (translation)
Take `⟨c, hc⟩ : (PowerSeries.X : PowerSeries O) ∣ W.γ₀ g PowerSeries.X` from `PowerSeries.X_dvd_iff.2 (W.γ₀_X g).1`. Establish `h1 : W.γA g letπ = letπ * (fun _ => c)`. Use function extensionality and compare the values at `i`. Simplify using `[LocWach.γA, letγ, letπ, hc]`. Use `⟨(W.φA ^ (W.s - 1)) (fun _ => c), ?_⟩` and prove the remaining obligations.

Rewrite using `[LocWach.X, ← φpow_γA, h1, map_mul]`.
-/
theorem X_dvd_γX (g : W.Gam) : W.X ∣ W.γA g W.X := by
  obtain ⟨c, hc⟩ : (PowerSeries.X : PowerSeries O) ∣ W.γ₀ g PowerSeries.X :=
    PowerSeries.X_dvd_iff.2 (W.γ₀_X g).1
  have h1 : W.γA g letπ = letπ * (fun _ => c) := by
    funext i
    simp [LocWach.γA, letγ, letπ, hc]
  refine ⟨(W.φA ^ (W.s - 1)) (fun _ => c), ?_⟩
  rw [LocWach.X, ← φpow_γA, h1, map_mul]

/- English proof (translation)
Take `⟨y, hy, rfl⟩` from `hx`. Take `⟨c, hc⟩` from `X_dvd_γX W δ`. Use `⟨c • W.γD T δ y, (W.N T).smul_mem _ (W.N_Γ T δ y hy), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `W.X • c • W.γD T δ y = W.γD T δ (W.X • y)`. Rewrite using `[γD_smulA, hc, mul_smul]`.
-/
theorem γD_mem_aN_X (T : LocLat G Qp LL O) (δ : W.Gam) (x : W.DD T) (hx : x ∈ aN W T W.X) :
    W.γD T δ x ∈ aN W T W.X := by
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨c, hc⟩ := X_dvd_γX W δ
  refine ⟨c • W.γD T δ y, (W.N T).smul_mem _ (W.N_Γ T δ y hy), ?_⟩
  change W.X • c • W.γD T δ y = W.γD T δ (W.X • y)
  rw [γD_smulA, hc, mul_smul]

end Generic

/- English proof (translation)
Introduce `_ HW l _ K s LL h T δ x hx` and use `γD_mem_aN_X ((HW l).W K s LL h) T δ x hx`.
-/
theorem xstab : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (δ : ((HW l).W K s LL h).Gam) (x : ((HW l).W K s LL h).DD T), x ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X → ((HW l).W K s LL h).γD T δ x ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X :=
  fun _ HW l _ K s LL h T δ x hx => γD_mem_aN_X ((HW l).W K s LL h) T δ x hx

end GlobalTheory.NL.XStab
