import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsumCoeffOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicPowerSeriesDataLevIsExpansionAtZetaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxUnramifiedActsOnLetterIdempotentImageStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenDiscConvergentRingWithExpansionsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachModulePeriodMapToBcrisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachLatticeMatricesGammaPhiStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesEqCOfSubstFixedNotRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiltrationEstimateExpansionTensorBdRComponentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantBasisConvergingOpenDiscStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEvaluationConvergentSeriesBcrisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeFreeOfCrystallineStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeAinfSandwichInvertPiStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBeta
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGammaLayerPadicCoordinates

noncomputable section

namespace GlobalTheory.HWL.Cmp

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : WGam PD LL O v n s}

variable {R : WSer Γ} {b₀ : LetA O n →+* LL ⊗[Qp] B} {tS zS : BdR}
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {I : WIo R (O ⊗[Zl] Ai) RW inclR φR gR πA} {E : WEt I} {zl : PowerSeries Zl →+* LetA O n}

open Classical in

def levOf {Dc : Disc R b₀ tS zS} {Mo : WN E zl} (bT : ∀ T : LocLat G Qp LL O, ↥(Mo.N T) →+ T.V ⊗[Qp] B)
    (Fr : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Frame Dc Mo T) (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) :
    ↥(Mo.N T) →+ (ℤ → T.V ⊗[Qp] B) :=
  if h : IsCrys PD T.ρ then (Fr T h).lev bT i ζ else 0

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Establish `pos : ∀ (T : LocLat G Qp LL O) (h : IsCrys PD T.ρ) (i : ZMod n) (ζ : LL), levOf bT Fr T i ζ = Frame.lev bT (Fr T h) i ζ` using `fun T h i ζ => dif_pos h`. Establish `neg : ∀ (T : LocLat G Qp LL O) (_ : ¬ IsCrys PD T.ρ) (i : ZMod n) (ζ : LL), levOf bT Fr T i ζ = 0` using `fun T h i ζ => dif_neg h`. Establish `hmem : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(Mo.N T)) (k : ℤ), levOf bT Fr T i ζ x k ∈ DcrisL PD T.ρ (Γ.emb i)`. Introduce `T i ζ x k`. Distinguish the cases in `h : IsCrys PD T.ρ`.

Rewrite using `[pos T h]`. Conclude with `Frame.lev_mem hP h _ i ζ x k`. Rewrite using `[neg T h]`. Conclude with `Submodule.zero_mem _`. Establish `hsupp : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(Mo.N T)), ∃ m : ℤ, ∀ k < m, levOf bT Fr T i ζ x k = 0`.

Introduce `T i ζ x`. Distinguish the cases in `h : IsCrys PD T.ρ`. Rewrite using `[pos T h]`. Conclude with `⟨_, Frame.lev_supp bT _ i ζ x⟩`. Rewrite using `[neg T h]`.

Conclude with `⟨0, fun _ _ => rfl⟩`. Establish `hneg : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (x : ↥(Mo.N T)) (k : ℤ), k < 0 → levOf bT Fr T i 1 x k = 0`. Introduce `T i x k hk`. Distinguish the cases in `h : IsCrys PD T.ρ`. Rewrite using `[pos T h]`.

Conclude with `Frame.lev_one_neg bT _ i x k hk`. Rewrite using `[neg T h]`. Both sides reduce to the same expression. Establish `hsmul : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (α : LetA O n) (x : ↥(Mo.N T)) (k : ℤ), levOf bT Fr T i ζ (α • x) k = ∑ᶠ j : ℕ, PowerSeries.coeff j (R.lev i ζ α) • levOf bT Fr T i ζ x (k - (j : ℤ))`. Introduce `T i ζ α x k`.

Distinguish the cases in `h : IsCrys PD T.ρ`. Rewrite using `[pos T h]`. Conclude with `Frame.lev_smul bT _ i ζ α x k`. Rewrite using `[neg T h]`. Simplify using the standard rewrite rules.

Establish `hsmul0 : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (α : LetA O n) (x : ↥(Mo.N T)), levOf bT Fr T i 1 (α • x) 0 = PowerSeries.constantCoeff (R.lev i 1 α) • levOf bT Fr T i 1 x 0`. Introduce `T i α x`. Rewrite using `[hsmul, finsum_eq_single _ 0]`. Simplify using the standard rewrite rules. Introduce `j hj`.

Rewrite using `[hneg T i x _ (by omega), smul_zero]`. Set `cmp : ∀ T : LocLat G Qp LL O, ↥(Mo.N T) →+ T.V ⊗[Qp] B` to `fun T => ∑ i : ZMod n, (Pi.evalAddMonoidHom (fun _ : ℤ => T.V ⊗[Qp] B) 0).comp (levOf bT Fr T i 1)`. Establish `hcmp : ∀ (T : LocLat G Qp LL O) (x : ↥(Mo.N T)), cmp T x = ∑ i : ZMod n, levOf bT Fr T i 1 x 0`. Introduce `T x`. Simplify using `[cmp, AddMonoidHom.finset_sum_apply]`.

Establish `hcmpE : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (x : ↥(Mo.N T)), cmp T ((letE i : LetA O n) • x) = levOf bT Fr T i 1 x 0`. Introduce `T i x`. Rewrite using `[hcmp, Finset.sum_eq_single i]`. Rewrite using `[hsmul0, Dc.lev_letE]`. Simplify using the standard rewrite rules.

Introduce `j _ hj`. Rewrite using `[hsmul0, Dc.lev_letE]`. Simplify using `[hj]`. Simplify using the standard rewrite rules. Establish `hmap : ∀ {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L), IsCrys PD T.ρ → IsCrys PD T'.ρ → ∀ (i : ZMod n) (ζ : LL) (x : ↥(Mo.N T)) (hx : E.map f (x : E.DD T) ∈ Mo.N T') (k : ℤ), levOf bT Fr T' i ζ ⟨E.map f (x : E.DD T), hx⟩ k = AlgebraTensorModule.map f.f (LinearMap.id : B →ₗ[Qp] …`.

Introduce `T T' f h h' i ζ x hx k`. Rewrite using `[pos T h, pos T' h']`. Conclude with `Frame.lev_map hP hinv f h h' _ _ i ζ x hx k`. Set `levN : ∀ T : LocLat G Qp LL O, ZMod n → LL → ↥(Mo.N T) →+ (ℤ → T.V ⊗[Qp] BdR)` to `fun T i ζ => ((ιV PD (LL := LL) (V := T.V)).toAddMonoidHom.compLeft ℤ).comp (levOf bT Fr T i ζ)`. Establish `hN : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(Mo.N T)) (k : ℤ), levN T i ζ x k = ιV PD (LL` using `LL) (V := T.V) (levOf bT Fr T i ζ x k) := fun _ _ _ _ _ => rfl`.

Use `⟨{ cmp := cmp cmp_smul := fun T c x => ?_ cmp_π := fun T x => ?_ cmp_mem := fun T x => ?_ cmp_letter := fun T i x => by rw [hcmpE]; exact hmem T i 1 x 0 cmp_map := fun f h h' x hx => by simp only [hcmp, hmap f h h', map_sum] levN := levN levN_supp := fun T i ζ x => ?_ levN_smul : …` and prove the remaining obligations. Simplify using `only [pos T h]`. Conclude with `Frame.lev_φ hP h _ i ζ hζ x m hx k`. Use `levB_Γ := fun T h g i ζ ζ' j a h1 h2 h3 x hx k => by`. Simplify using `only [pos T h]`.

Conclude with `Frame.lev_Γ bT _ g i ζ ζ' j a h1 h2 h3 x hx k`. Use `βdR := βdR`. Use `βdR_tmul := hP.tmul`. Use `levN_dR := fun T h i ζ ι h1 h2 x k y hy a ha => ?_ }⟩`. Establish `: c • x = algebraMap O (LetA O n) c • x` using `Subtype.ext (algebraMap_smul (LetA O n) c (x : E.DD T)).symm`.

Rewrite using `[this, hcmp, hcmp, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hsmul0, AlgHom.commutes]`. Simplify using `[PowerSeries.algebraMap_apply]`. Rewrite using `[hcmp]`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Take `⟨e, he, -, h3⟩` from `R.lev_π i 1 ⟨0, by simp⟩`. Establish `h4` using `congrArg PowerSeries.constantCoeff h3`. Rewrite `h4` using `[map_add, map_mul, he]`. Establish `h5 : PowerSeries.constantCoeff (R.lev i 1 letπ) = 0` using `by simpa using h4`.

Rewrite using `[hsmul0, h5, zero_smul]`. Rewrite using `[hcmp]`. Conclude with `Submodule.sum_mem _ fun i _ => (hmem T i 1 x 0).1`. Take `⟨m, hm⟩` from `hsupp T i ζ x`. Conclude with `⟨m, fun k hk => by rw [hN, hm k hk, map_zero]⟩`.

Take `⟨m, hm⟩` from `hsupp T i ζ x`. Establish `hz : ∀ j : ℕ, j ∉ Finset.range ((k - m).toNat + 1) → levOf bT Fr T i ζ x (k - (j : ℤ)) = 0`. Introduce `j hj`. Establish `: (k - m).toNat + 1 ≤ j` using `by simpa using hj`. Conclude with `hm _ (by omega)`.

Rewrite using `[hN, hsmul, finsum_eq_sum_of_support_subset (s := Finset.range ((k - m).toNat + 1)), finsum_eq_sum_of_support_subset (s := Finset.range ((k - m).toNat + 1)), map_sum]`. Simplify using `only [map_smul, hN]`. Introduce `j hj`. Assume the negation of the conclusion as `hc`. Conclude with `hj (by simp only [hN, hz j hc, map_zero, smul_zero])`.

Introduce `j hj`. Assume the negation of the conclusion as `hc`. Conclude with `hj (by simp only [hz j hc, smul_zero])`. Rewrite using `[hN, hN, hmap f h h']`. Proceed by induction on `levOf bT Fr T i ζ x k using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul a b => simp [ιV]`. Rewrite using `[hP.dR T h x k y hy]`. Use `GlobalTheory.T.filtration_estimate_expansion_tensorBdR_component PD T ι tS (ιdR p1 ^ k) (Dc.ι_tb ▸ Dc.tb_unit.map PD.ι) Dc.tS_mem (Fr T h).r (Fr T h).w _ (fun j => ιV PD (LL := LL) (V := T.V) ((Fr T h).d bT j)) _ (fun j => Dc.ex i ζ ((Fr T h).a x j)) _ (Frame.dR_basis hP h (Fr T …` and prove the remaining obligations.

Rewrite using `[hN, pos T h]`. Conclude with `Frame.dR_lev (Fr T h) i ζ ι h1 h2 x k`.
-/
theorem nonempty_wCmp [NeZero n] (Dc : Disc R b₀ tS zS) (Mo : WN E zl) {ιdR : Ai →+* BdR} {p1 : Ai}
    {βdR : ∀ T : LocLat G Qp LL O, TW (O ⊗[Zl] Ai) T →+ T.V ⊗[Qp] BdR}
    {bT : ∀ T : LocLat G Qp LL O, ↥(Mo.N T) →+ T.V ⊗[Qp] B} (hP : IsPer Mo b₀ ιdR p1 βdR bT)
    (Fr : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Frame Dc Mo T)
    (hinv : ∀ a : LetA LL n, γL R Γ.gam a = a → ∃ c, a = cst c) : Nonempty (WCmp Mo ιdR p1 tS zS) := by
  have pos : ∀ (T : LocLat G Qp LL O) (h : IsCrys PD T.ρ) (i : ZMod n) (ζ : LL), levOf bT Fr T i ζ = Frame.lev bT (Fr T h) i ζ :=
    fun T h i ζ => dif_pos h
  have neg : ∀ (T : LocLat G Qp LL O) (_ : ¬ IsCrys PD T.ρ) (i : ZMod n) (ζ : LL), levOf bT Fr T i ζ = 0 := fun T h i ζ => dif_neg h
  have hmem : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(Mo.N T)) (k : ℤ), levOf bT Fr T i ζ x k ∈ DcrisL PD T.ρ (Γ.emb i) := by
    intro T i ζ x k
    by_cases h : IsCrys PD T.ρ
    · rw [pos T h]; exact Frame.lev_mem hP h _ i ζ x k
    · rw [neg T h]; exact Submodule.zero_mem _
  have hsupp : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(Mo.N T)), ∃ m : ℤ, ∀ k < m, levOf bT Fr T i ζ x k = 0 := by
    intro T i ζ x
    by_cases h : IsCrys PD T.ρ
    · rw [pos T h]; exact ⟨_, Frame.lev_supp bT _ i ζ x⟩
    · rw [neg T h]; exact ⟨0, fun _ _ => rfl⟩
  have hneg : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (x : ↥(Mo.N T)) (k : ℤ), k < 0 → levOf bT Fr T i 1 x k = 0 := by
    intro T i x k hk
    by_cases h : IsCrys PD T.ρ
    · rw [pos T h]; exact Frame.lev_one_neg bT _ i x k hk
    · rw [neg T h]; rfl
  have hsmul : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (α : LetA O n) (x : ↥(Mo.N T)) (k : ℤ), levOf bT Fr T i ζ (α • x) k =
      ∑ᶠ j : ℕ, PowerSeries.coeff j (R.lev i ζ α) • levOf bT Fr T i ζ x (k - (j : ℤ)) := by
    intro T i ζ α x k
    by_cases h : IsCrys PD T.ρ
    · rw [pos T h]; exact Frame.lev_smul bT _ i ζ α x k
    · rw [neg T h]; simp
  have hsmul0 : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (α : LetA O n) (x : ↥(Mo.N T)), levOf bT Fr T i 1 (α • x) 0 =
      PowerSeries.constantCoeff (R.lev i 1 α) • levOf bT Fr T i 1 x 0 := by
    intro T i α x
    rw [hsmul, finsum_eq_single _ 0]
    · simp
    · intro j hj
      rw [hneg T i x _ (by omega), smul_zero]
  let cmp : ∀ T : LocLat G Qp LL O, ↥(Mo.N T) →+ T.V ⊗[Qp] B := fun T =>
    ∑ i : ZMod n, (Pi.evalAddMonoidHom (fun _ : ℤ => T.V ⊗[Qp] B) 0).comp (levOf bT Fr T i 1)
  have hcmp : ∀ (T : LocLat G Qp LL O) (x : ↥(Mo.N T)), cmp T x = ∑ i : ZMod n, levOf bT Fr T i 1 x 0 := by
    intro T x
    simp [cmp, AddMonoidHom.finset_sum_apply]
  have hcmpE : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (x : ↥(Mo.N T)), cmp T ((letE i : LetA O n) • x) = levOf bT Fr T i 1 x 0 := by
    intro T i x
    rw [hcmp, Finset.sum_eq_single i]
    · rw [hsmul0, Dc.lev_letE]; simp
    · intro j _ hj
      rw [hsmul0, Dc.lev_letE]; simp [hj]
    · simp
  have hmap : ∀ {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L), IsCrys PD T.ρ → IsCrys PD T'.ρ →
      ∀ (i : ZMod n) (ζ : LL) (x : ↥(Mo.N T)) (hx : E.map f (x : E.DD T) ∈ Mo.N T') (k : ℤ),
      levOf bT Fr T' i ζ ⟨E.map f (x : E.DD T), hx⟩ k =
        AlgebraTensorModule.map f.f (LinearMap.id : B →ₗ[Qp] B) (levOf bT Fr T i ζ x k) := by
    intro T T' f h h' i ζ x hx k
    rw [pos T h, pos T' h']
    exact Frame.lev_map hP hinv f h h' _ _ i ζ x hx k
  let levN : ∀ T : LocLat G Qp LL O, ZMod n → LL → ↥(Mo.N T) →+ (ℤ → T.V ⊗[Qp] BdR) := fun T i ζ =>
    ((ιV PD (LL := LL) (V := T.V)).toAddMonoidHom.compLeft ℤ).comp (levOf bT Fr T i ζ)
  have hN : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(Mo.N T)) (k : ℤ), levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (levOf bT Fr T i ζ x k) :=
    fun _ _ _ _ _ => rfl
  refine ⟨{
    cmp := cmp
    cmp_smul := fun T c x => ?_
    cmp_π := fun T x => ?_
    cmp_mem := fun T x => ?_
    cmp_letter := fun T i x => by rw [hcmpE]; exact hmem T i 1 x 0
    cmp_map := fun f h h' x hx => by simp only [hcmp, hmap f h h', map_sum]
    levN := levN
    levN_supp := fun T i ζ x => ?_
    levN_smul := fun T i ζ α x k => ?_
    levN_map := fun {T T'} f h h' i ζ x hx k => ?_
    levB := levOf bT Fr
    levB_mem := hmem
    levB_supp := hsupp
    levN_eq := hN
    cmp_eq := fun T _ => hcmpE T
    levB_φ := fun T h i ζ hζ x m hx k => by
      simp only [pos T h]; exact Frame.lev_φ hP h _ i ζ hζ x m hx k
    levB_Γ := fun T h g i ζ ζ' j a h1 h2 h3 x hx k => by
      simp only [pos T h]; exact Frame.lev_Γ bT _ g i ζ ζ' j a h1 h2 h3 x hx k
    βdR := βdR
    βdR_tmul := hP.tmul
    levN_dR := fun T h i ζ ι h1 h2 x k y hy a ha => ?_ }⟩
  · have : c • x = algebraMap O (LetA O n) c • x := Subtype.ext (algebraMap_smul (LetA O n) c (x : E.DD T)).symm
    rw [this, hcmp, hcmp, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsmul0, AlgHom.commutes]
    simp [PowerSeries.algebraMap_apply]
  · rw [hcmp]
    refine Finset.sum_eq_zero fun i _ => ?_
    obtain ⟨e, he, -, h3⟩ := R.lev_π i 1 ⟨0, by simp⟩
    have h4 := congrArg PowerSeries.constantCoeff h3
    rw [map_add, map_mul, he] at h4
    have h5 : PowerSeries.constantCoeff (R.lev i 1 letπ) = 0 := by simpa using h4
    rw [hsmul0, h5, zero_smul]
  · rw [hcmp]
    exact Submodule.sum_mem _ fun i _ => (hmem T i 1 x 0).1
  · obtain ⟨m, hm⟩ := hsupp T i ζ x
    exact ⟨m, fun k hk => by rw [hN, hm k hk, map_zero]⟩
  · obtain ⟨m, hm⟩ := hsupp T i ζ x
    have hz : ∀ j : ℕ, j ∉ Finset.range ((k - m).toNat + 1) → levOf bT Fr T i ζ x (k - (j : ℤ)) = 0 := by
      intro j hj
      have : (k - m).toNat + 1 ≤ j := by simpa using hj
      exact hm _ (by omega)
    rw [hN, hsmul, finsum_eq_sum_of_support_subset (s := Finset.range ((k - m).toNat + 1)),
      finsum_eq_sum_of_support_subset (s := Finset.range ((k - m).toNat + 1)), map_sum]
    · simp only [map_smul, hN]
    · intro j hj
      by_contra hc
      exact hj (by simp only [hN, hz j hc, map_zero, smul_zero])
    · intro j hj
      by_contra hc
      exact hj (by simp only [hz j hc, smul_zero])
  · rw [hN, hN, hmap f h h']
    induction levOf bT Fr T i ζ x k using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b => simp [ιV]
  · rw [hP.dR T h x k y hy]
    refine GlobalTheory.T.filtration_estimate_expansion_tensorBdR_component PD T ι tS (ιdR p1 ^ k) (Dc.ι_tb ▸ Dc.tb_unit.map PD.ι) Dc.tS_mem (Fr T h).r (Fr T h).w _
      (fun j => ιV PD (LL := LL) (V := T.V) ((Fr T h).d bT j)) _ (fun j => Dc.ex i ζ ((Fr T h).a x j)) _
      (Frame.dR_basis hP h (Fr T h) ι x) (fun j m => Dc.taylor i ζ ι h1 h2 _ m) (fun k => ?_) a ha
    rw [hN, pos T h]
    exact Frame.dR_lev (Fr T h) i ζ ι h1 h2 x k

end Generic

/- English proof (translation)
Introduce `h`. Take `⟨⟨lam, -, h1, h2, ⟨g, hg⟩, -⟩, -⟩` from `GlobalTheory.HWL.Coord.exists_gamma_coordinates l P K s LL hG Γ`. Establish `h3 : Γ.gam ^ k = 1`. Apply `Γ.χΓ_inj` to reduce the goal to its premises. Rewrite using `[map_pow, map_one]`.

Apply `Units.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using h`. Establish `h4 : lam (g ^ k) = 1`. Rewrite using `[h1, Subgroup.coe_pow, map_pow, (h2 g).mp hg, h3]`.

Rewrite `h4` using `[map_pow, hg, ← ofAdd_nsmul, ofAdd_eq_one]`. Simplify using `at h4`. Use linear arithmetic over natural numbers and integers.
-/
theorem chi_gam_pow_ne_one {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K : FinExt l} {s : ℕ} {LL : FinExt l}
    (hG : Good K s LL) (Γ : GamS P K s LL) (k : ℕ) (hk : 0 < k) :
    algebraMap ↥(OL LL) ↥LL.1 (Γ.χΓ Γ.gam : ↥(OL LL)) ^ k ≠ 1 := by
  intro h
  obtain ⟨⟨lam, -, h1, h2, ⟨g, hg⟩, -⟩, -⟩ := GlobalTheory.HWL.Coord.exists_gamma_coordinates l P K s LL hG Γ
  have h3 : Γ.gam ^ k = 1 := by
    apply Γ.χΓ_inj
    rw [map_pow, map_one]
    apply Units.ext
    apply Subtype.ext
    simpa using h
  have h4 : lam (g ^ k) = 1 := by
    rw [h1, Subgroup.coe_pow, map_pow, (h2 g).mp hg, h3]
  rw [map_pow, hg, ← ofAdd_nsmul, ofAdd_eq_one] at h4
  simp at h4
  omega

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `l _ P AI hT K s LL hG Γ R I hI E Mo`. Use `haveI := (P.PD K).finK₀`. Use `haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩`. Take `⟨β, hβ⟩` from `GlobalTheory.HWLBeta.exists_beta l P AI hT LL`. Take `⟨J, hJ⟩` from `GlobalTheory.T.exists_evaluation_convergent_series_Bcris l P AI hT K s LL hG Γ R I hI β hβ`.

Take `⟨Dc, hC, ht⟩` from `GlobalTheory.T.exists_openDiscConvergentRing_with_expansions l P AI hT K s LL hG Γ R I hI β hβ J hJ (GlobalTheory.T.cyclotomicPowerSeriesData_lev_isExpansionAtZeta l P K s LL Γ R) (GlobalTheory.T.maxUnramified_acts_on_letterIdempotent_image l P AI hT K s LL hG Γ R I hI β hβ)`. Take `⟨βdR, bT, hP⟩` from `GlobalTheory.T.exists_wachModule_periodMap_to_bcris l P AI hT K s LL hG Γ R I hI β hβ E Mo (GlobalTheory.T.wachLattice_ainf_sandwich_invert_pi l P AI K s LL hG Γ R I hI E Mo)`. Establish `hF : ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), IsCrys (P.PD K) T.ρ → Nonempty (Frame Dc Mo T)`. Introduce `T h`. Take `⟨nb⟩` from `GlobalTheory.T.wach_lattice_free_of_crystalline l P AI K s LL hG Γ R I hI E Mo T h`.

Take `⟨m, m', Gm, Pm, Pm', h1, h2, h3, h4, h5, h6⟩` from `GlobalTheory.T.exists_wachLattice_matrices_gamma_phi Mo T _ nb`. Take `⟨U, V, w, k1, -, k3, k4, Cm, k5⟩` from `GlobalTheory.T.exists_invariant_basis_converging_open_disc l P K s LL hG Γ R _ m m' Gm Pm Pm' h1 h2 h3 h4`. Use `⟨{ r := _, w := w, m := m, nb := nb, U := U, V := V, UV := k1 U_mem := fun i j => hC _ fun k => by rw [ht]; exact (k3 i j k).1 V_mem := fun i j => hC _ fun k => by rw [ht]; exact (k3 i j k).2 Gm := Gm, Gm_def := h5 GU := fun g => ?_ Pm := Pm, Pm_def := h6, Cm := Cm PU := ?_ }⟩` and prove the remaining obligations. Rewrite using `[funext (γL_apply R g)]`. Conclude with `k4 g`.

Establish `e1 : ⇑(φL ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K)) (P.PD K).p) = fun a k => PowerSeries.subst ((1 + PowerSeries.X) ^ l - 1 : PowerSeries ↥LL.1) (a (k - 1))`. Use function extensionality and compare the values at `a`. Rewrite using `[φL_apply, P.PD_p]`. Establish `e2 : toL ↥(OL LL) ↥LL.1 _ (R.Q ^ m) = toLL R.Q ^ m` using `(toL ↥(OL LL) ↥LL.1 _).map_pow R.Q m`. Rewrite using `[e1]`.

Conclude with `k5.trans (congrArg (fun q : LetA ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K)) => q • (U * Cm.map cst)) e2.symm)`. Use `nonempty_wCmp Dc Mo hP (fun T h => (hF T h).some) fun a ha => ?_` and prove the remaining obligations. Use `⟨fun i => PowerSeries.constantCoeff (a i), funext fun i => ?_⟩` and prove the remaining obligations. Use `GlobalTheory.T.powerSeries_eq_C_of_subst_fixed_not_root_of_unity _ (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1) (R.γ₀ Γ.gam PowerSeries.X)) ?_ ?_ (a i) ?_` and prove the remaining obligations. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, (R.γ₀_X _).1, map_zero]`.

Introduce `k hk`. Rewrite using `[PowerSeries.coeff_map, (R.γ₀_X _).2]`. Conclude with `chi_gam_pow_ne_one hG Γ k hk`. Rewrite `ha` using `[γL_apply]`. Conclude with `congrFun ha i`.
-/
theorem nonempty_cmpS : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R),
    IoW I → ∀ (E : WEt I) (Mo : NS E), Nonempty (CmpS Mo) := by
  intro l _ P AI hT K s LL hG Γ R I hI E Mo
  haveI := (P.PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨β, hβ⟩ := GlobalTheory.HWLBeta.exists_beta l P AI hT LL
  obtain ⟨J, hJ⟩ := GlobalTheory.T.exists_evaluation_convergent_series_Bcris l P AI hT K s LL hG Γ R I hI β hβ
  obtain ⟨Dc, hC, ht⟩ := GlobalTheory.T.exists_openDiscConvergentRing_with_expansions l P AI hT K s LL hG Γ R I hI β hβ J hJ (GlobalTheory.T.cyclotomicPowerSeriesData_lev_isExpansionAtZeta l P K s LL Γ R)
    (GlobalTheory.T.maxUnramified_acts_on_letterIdempotent_image l P AI hT K s LL hG Γ R I hI β hβ)
  obtain ⟨βdR, bT, hP⟩ := GlobalTheory.T.exists_wachModule_periodMap_to_bcris l P AI hT K s LL hG Γ R I hI β hβ E Mo
    (GlobalTheory.T.wachLattice_ainf_sandwich_invert_pi l P AI K s LL hG Γ R I hI E Mo)
  have hF : ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), IsCrys (P.PD K) T.ρ → Nonempty (Frame Dc Mo T) := by
    intro T h
    obtain ⟨nb⟩ := GlobalTheory.T.wach_lattice_free_of_crystalline l P AI K s LL hG Γ R I hI E Mo T h
    obtain ⟨m, m', Gm, Pm, Pm', h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.exists_wachLattice_matrices_gamma_phi Mo T _ nb
    obtain ⟨U, V, w, k1, -, k3, k4, Cm, k5⟩ := GlobalTheory.T.exists_invariant_basis_converging_open_disc l P K s LL hG Γ R _ m m' Gm Pm Pm' h1 h2 h3 h4
    refine ⟨{
      r := _, w := w, m := m, nb := nb, U := U, V := V, UV := k1
      U_mem := fun i j => hC _ fun k => by rw [ht]; exact (k3 i j k).1
      V_mem := fun i j => hC _ fun k => by rw [ht]; exact (k3 i j k).2
      Gm := Gm, Gm_def := h5
      GU := fun g => ?_
      Pm := Pm, Pm_def := h6, Cm := Cm
      PU := ?_ }⟩
    · rw [funext (γL_apply R g)]
      exact k4 g
    · have e1 : ⇑(φL ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K)) (P.PD K).p) = fun a k =>
          PowerSeries.subst ((1 + PowerSeries.X) ^ l - 1 : PowerSeries ↥LL.1) (a (k - 1)) := by
        funext a
        rw [φL_apply, P.PD_p]
      have e2 : toL ↥(OL LL) ↥LL.1 _ (R.Q ^ m) = toLL R.Q ^ m := (toL ↥(OL LL) ↥LL.1 _).map_pow R.Q m
      rw [e1]
      exact k5.trans (congrArg (fun q : LetA ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K)) => q • (U * Cm.map cst)) e2.symm)
  refine nonempty_wCmp Dc Mo hP (fun T h => (hF T h).some) fun a ha => ?_
  refine ⟨fun i => PowerSeries.constantCoeff (a i), funext fun i => ?_⟩
  refine GlobalTheory.T.powerSeries_eq_C_of_subst_fixed_not_root_of_unity _ (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1) (R.γ₀ Γ.gam PowerSeries.X)) ?_ ?_ (a i) ?_
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, (R.γ₀_X _).1, map_zero]
  · intro k hk
    rw [PowerSeries.coeff_map, (R.γ₀_X _).2]
    exact chi_gam_pow_ne_one hG Γ k hk
  · rw [γL_apply] at ha
    exact congrFun ha i

end GlobalTheory.HWL.Cmp
