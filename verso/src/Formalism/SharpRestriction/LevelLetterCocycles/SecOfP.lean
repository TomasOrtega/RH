import Formalism.SharpRestriction.LevelLetterCocycles.HorTrExists

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O]

/- English proof (translation)
Establish `hl : 2 ≤ PD.p` using `PD.hp.two_le`. Take `⟨yP, hyP, hyx⟩` from `hx`. Rewrite `hyx` using `[one_smul]`. Take `⟨β₀, hβ₀, hyβ⟩` from `Formalism.MainNotions.UnusedSlot80.ArcF.Pp_repr W T c' e b hb.1 yP hyP`. Establish `hbl : ∀ m, (letE c' : LetA O n) • b m = b m` using `fun m => Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T c' (hb.1.1 m).2`.

Establish `hφl : ∀ m, (letE (c' + (e : ZMod n)) : LetA O n) • ((W.φD T) ^ e) (b m) = ((W.φD T) ^ e) (b m)` using `fun m => φD_pow_letter W T c' (b m) (hbl m) e`. Use `set Λ : LetA O n := abelian₂ W A (c' + (e : ZMod n)) e with hΛdef`. Set `β : Fin d → LetA O n` to `fun m => letE (c' + (e : ZMod n)) * β₀ m`. Establish `hβ : ∀ m, β m ∈ W.AΔ` using `fun m => W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W _) (hβ₀ m)`. Establish `hΛx : Λ • x = ∑ m, β m • ((W.φD T) ^ e) (b m)`.

Rewrite using `[hyx, hyβ]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Simplify using `only [β, mul_smul]`. Rewrite using `[smul_comm, hφl]`. Establish `hHc` using `hH hCA T hTc c'`.

Establish `hH5` using `hHc.2.2.2.2 d b hb.1 sol hb.2`. Establish `h4` using `hHc.2.2.2.1`. Use `choose g hg using fun k r m => Formalism.MainNotions.UnusedSlot80.Relay2.int_of_bd W hO2 r (h4 r) _ (hH5.1 k r m)`. Use `choose g' hg' using fun r k m => Formalism.MainNotions.UnusedSlot80.Relay2.int_of_bd W hO2 r (h4 r) _ (hH5.2 k m r)`. Use `set M : ℕ := A.M PD.p with hMdef`.

Set `κ : ℕ` to `Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M`. Set `yy : Fin d → ℕ → Fin d → O` to `fun k r m => ((PD.p : ℕ) : O) ^ (κ - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * g k r m`. Set `zz : ℕ → Fin d → Fin d → O` to `fun r k m => ((PD.p : ℕ) : O) ^ (κ - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * g' r k m`. Establish `hyy : ∀ k, ∀ r < M, ∀ m, algebraMap O LL (yy k r m) = (PD.p : LL) ^ κ * sol k r m`. Introduce `k r hr m`.

Establish `hle` using `Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl hr.le`. Simplify using `only [yy, map_mul, map_pow, map_natCast, hg]`. Rewrite using `[← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]`. Establish `hzz : ∀ r < M, ∀ k m, algebraMap O LL (zz r k m) = (PD.p : LL) ^ κ * PowerSeries.coeff r ((Matrix.of fun m' k' => PowerSeries.mk fun r' => sol k' r' m' : Matrix (Fin d) (Fin d) (PowerSeries LL))⁻¹ k m)`. Introduce `r hr k m`.

Establish `hle` using `Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl hr.le`. Simplify using `only [zz, map_mul, map_pow, map_natCast, hg']`. Rewrite using `[← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]`. Use `set Y : LetA O n := (W.φA ^ e) W.π₀ with hYdef`. Establish `hY : Y ∈ W.AΔ` using `φA_pow_mem_AΔ W hR.1 e`.

Use `set D : LetA O n := W.π₀ * Λ ^ 2 with hDdef`. Take `⟨ν, hν, hYM⟩` from `yM_gen W hTr hCA hR.1 h5p A hA (c' + (e : ZMod n)) e`. Establish `hYM' : Y ^ M = D * ν` using `by rw [hYdef, hMdef, hYM]`. Use `choose ρ hρ using fun m m' => Formalism.MainNotions.UnusedSlot80.ArcF.frame_inv_poly hinj sol (fun k => (hb.2 k).2) M κ yy hyy zz hzz Y m m'`. Set `HY : Fin d → Fin d → LetA O n` to `fun m k => ∑ r ∈ Finset.range M, algebraMap O (LetA O n) (yy k r m) * Y ^ r`.

Set `GY : Fin d → Fin d → LetA O n` to `fun k m' => ∑ r ∈ Finset.range M, algebraMap O (LetA O n) (zz r k m') * Y ^ r`. Establish `hGY : ∀ k m', GY k m' ∈ W.AΔ` using `fun k m' => W.AΔ.sum_mem fun r _ => W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (W.AΔ.pow_mem hY r)`. Set `aa : Fin d → LetA O n` to `fun k => ∑ m', GY k m' * β m'`. Establish `haa : ∀ k, aa k ∈ W.AΔ` using `fun k => W.AΔ.sum_mem fun m' _ => W.AΔ.mul_mem (hGY k m') (hβ m')`. Establish `haal : ∀ k, letE (c' + (e : ZMod n)) * 1 * aa k = aa k`.

Introduce `k`. Simplify using `only [aa, mul_one, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m' _ => ?_` and prove the remaining obligations. Simplify using `only [β]`. Take the linear combination `(GY k m' * β₀ m') * (letE_mul_self (O := O) (c' + (e : ZMod n)))`.

Take `⟨U, hU⟩` from `lam_unit W hR A (c' + (e : ZMod n)) e`. Establish `hcoef : ∀ k, algebraMap (LetA O n) W.EE Λ * (((U⁻¹ : W.EEˣ) : W.EE) * algebraMap (LetA O n) W.EE (aa k)) = algebraMap (LetA O n) W.EE (aa k)`. Introduce `k`. Rewrite using `[← hU, ← mul_assoc, Units.mul_inv, one_mul]`. Set `w : Fin d → LetA O n` to `fun m => -(ν * ∑ m', Polynomial.aeval Y (ρ m m') * β m')`.

Establish `hw : ∀ m, w m ∈ W.AΔ` using `fun m => W.AΔ.neg_mem (W.AΔ.mul_mem hν (W.AΔ.sum_mem fun m' _ => W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.ArcF.aeval_mem_AΔ W hY _) (hβ m')))`. Establish `hkey : ∀ m, lA W ^ κ * lA W ^ κ * β m - ∑ k, aa k * HY m k = D * w m`. Introduce `m`. Establish `A2 : ∑ k, aa k * HY m k = ∑ m', (∑ k, HY m k * GY k m') * β m'`. Simplify using `only [aa, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun m' _ => Finset.sum_congr rfl fun k _ => by ring`. Establish `h1 : ∀ m', (∑ k, HY m k * GY k m') * β m' = lA W ^ κ * lA W ^ κ * ((if m = m' then 1 else 0) * β m') + Y ^ M * (Polynomial.aeval Y (ρ m m') * β m')`. Introduce `m'`. Use `hρ m m'` as an intermediate fact.

Simplify using `only [HY, GY] at this ⊢`. Rewrite using `[this, map_mul, map_pow, map_natCast, apply_ite (algebraMap O (LetA O n)), map_one, map_zero]`. Unfold `lA`. Apply the tactic sequence `split_ifs <;> ring`. Rewrite using `[A2, Finset.sum_congr rfl fun m' _ => h1 m', Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]`.

Simplify using `only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, w]`. Rewrite using `[hYM']`. Expand and normalize the polynomial expressions, which then agree. Use `⟨κ, fun k => ((U⁻¹ : W.EEˣ) : W.EE) * algebraMap (LetA O n) W.EE (aa k), ⟨κ, 0, fun k => ∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r), aa, fun k => ⟨yy k, hyy k, rfl⟩, fun k => ⟨haa k, hcoef k⟩, ?_⟩, fun k => ⟨aa k, haa k, by rw [hcoef …` and prove the remaining obligations. Establish `hsum : ∑ k, aa k • ((W.φD T) ^ e) (∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r)) = ∑ m, (∑ k, aa k * HY m k) • ((W.φD T) ^ e) (b m)`.

Simplify using `only [Formalism.MainNotions.UnusedSlot80.ArcF.phi_trunc, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_smul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Use `congr 1`. Simplify using `only [HY, ← hYdef]`. Use `congr 1`. Use `Finset.sum_congr rfl fun r _ => mul_comm _ _` and prove the remaining obligations. Establish `hfin : lA W ^ 0 • (lA W ^ κ • Λ • (lA W ^ κ • x) - ∑ k, aa k • ((W.φD T) ^ e) (∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r))) = D • ∑ m, w m • ((W.φD T) ^ e) (b m)`.

Rewrite using `[pow_zero, one_smul, hsum, smul_comm Λ, hΛx]`. Simplify using `only [Finset.smul_sum]`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Simplify using `only [smul_smul]`.

Rewrite using `[← sub_smul, ← hkey m]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfin]`. Conclude with `Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_of_mem W T c' e _ (AddSubgroup.sum_mem _ fun m _ => Formalism.MainNotions.UnusedSlot80.Relay2.Pp_gen W T c' e (hw m) (hb.1.1 m))`.
-/
theorem secOfP' (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W) (hH : Formalism.MainNotions.LiftingTheory.coreH W)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5p : 5 ≤ PD.p) (A : ArcP n) (hA : A.OK)
    (c' : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) (hTc : IsCrys PD T.ρ) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T c' b sol) (x : W.DD T)
    (hx : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • x)) :
    ∃ (κ : ℕ) (f : Fin d → W.EE), RepVV W T c' e (A.M PD.p) (abelian₂ W A (c' + (e : ZMod n)) e) b sol
      (lA W ^ κ • x) f ∧ ∀ k, InFr W (c' + (e : ZMod n)) 1 (abelian₂ W A (c' + (e : ZMod n)) e) (f k) := by
  have hl : 2 ≤ PD.p := PD.hp.two_le
  obtain ⟨yP, hyP, hyx⟩ := hx
  rw [one_smul] at hyx
  obtain ⟨β₀, hβ₀, hyβ⟩ := Formalism.MainNotions.UnusedSlot80.ArcF.Pp_repr W T c' e b hb.1 yP hyP
  have hbl : ∀ m, (letE c' : LetA O n) • b m = b m := fun m =>
    Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T c' (hb.1.1 m).2
  have hφl : ∀ m, (letE (c' + (e : ZMod n)) : LetA O n) • ((W.φD T) ^ e) (b m) = ((W.φD T) ^ e) (b m) :=
    fun m => φD_pow_letter W T c' (b m) (hbl m) e
  set Λ : LetA O n := abelian₂ W A (c' + (e : ZMod n)) e with hΛdef
  let β : Fin d → LetA O n := fun m => letE (c' + (e : ZMod n)) * β₀ m
  have hβ : ∀ m, β m ∈ W.AΔ := fun m => W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W _) (hβ₀ m)
  have hΛx : Λ • x = ∑ m, β m • ((W.φD T) ^ e) (b m) := by
    rw [hyx, hyβ]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [β, mul_smul]
    rw [smul_comm, hφl]
  have hHc := hH hCA T hTc c'
  have hH5 := hHc.2.2.2.2 d b hb.1 sol hb.2
  have h4 := hHc.2.2.2.1
  choose g hg using fun k r m => Formalism.MainNotions.UnusedSlot80.Relay2.int_of_bd W hO2 r (h4 r) _ (hH5.1 k r m)
  choose g' hg' using fun r k m => Formalism.MainNotions.UnusedSlot80.Relay2.int_of_bd W hO2 r (h4 r) _ (hH5.2 k m r)
  set M : ℕ := A.M PD.p with hMdef
  let κ : ℕ := Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M
  let yy : Fin d → ℕ → Fin d → O := fun k r m =>
    ((PD.p : ℕ) : O) ^ (κ - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * g k r m
  let zz : ℕ → Fin d → Fin d → O := fun r k m =>
    ((PD.p : ℕ) : O) ^ (κ - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * g' r k m
  have hyy : ∀ k, ∀ r < M, ∀ m, algebraMap O LL (yy k r m) = (PD.p : LL) ^ κ * sol k r m := by
    intro k r hr m
    have hle := Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl hr.le
    simp only [yy, map_mul, map_pow, map_natCast, hg]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  have hzz : ∀ r < M, ∀ k m, algebraMap O LL (zz r k m) = (PD.p : LL) ^ κ *
      PowerSeries.coeff r ((Matrix.of fun m' k' => PowerSeries.mk fun r' => sol k' r' m' :
        Matrix (Fin d) (Fin d) (PowerSeries LL))⁻¹ k m) := by
    intro r hr k m
    have hle := Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl hr.le
    simp only [zz, map_mul, map_pow, map_natCast, hg']
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  set Y : LetA O n := (W.φA ^ e) W.π₀ with hYdef
  have hY : Y ∈ W.AΔ := φA_pow_mem_AΔ W hR.1 e
  set D : LetA O n := W.π₀ * Λ ^ 2 with hDdef
  obtain ⟨ν, hν, hYM⟩ := yM_gen W hTr hCA hR.1 h5p A hA (c' + (e : ZMod n)) e
  have hYM' : Y ^ M = D * ν := by rw [hYdef, hMdef, hYM]
  choose ρ hρ using fun m m' =>
    Formalism.MainNotions.UnusedSlot80.ArcF.frame_inv_poly hinj sol (fun k => (hb.2 k).2) M κ yy hyy zz hzz Y m m'
  let HY : Fin d → Fin d → LetA O n := fun m k =>
    ∑ r ∈ Finset.range M, algebraMap O (LetA O n) (yy k r m) * Y ^ r
  let GY : Fin d → Fin d → LetA O n := fun k m' =>
    ∑ r ∈ Finset.range M, algebraMap O (LetA O n) (zz r k m') * Y ^ r
  have hGY : ∀ k m', GY k m' ∈ W.AΔ := fun k m' => W.AΔ.sum_mem fun r _ =>
    W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (W.AΔ.pow_mem hY r)
  let aa : Fin d → LetA O n := fun k => ∑ m', GY k m' * β m'
  have haa : ∀ k, aa k ∈ W.AΔ := fun k => W.AΔ.sum_mem fun m' _ => W.AΔ.mul_mem (hGY k m') (hβ m')
  have haal : ∀ k, letE (c' + (e : ZMod n)) * 1 * aa k = aa k := by
    intro k
    simp only [aa, mul_one, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    simp only [β]
    linear_combination (GY k m' * β₀ m') * (letE_mul_self (O := O) (c' + (e : ZMod n)))
  obtain ⟨U, hU⟩ := lam_unit W hR A (c' + (e : ZMod n)) e
  have hcoef : ∀ k, algebraMap (LetA O n) W.EE Λ *
      (((U⁻¹ : W.EEˣ) : W.EE) * algebraMap (LetA O n) W.EE (aa k)) = algebraMap (LetA O n) W.EE (aa k) := by
    intro k
    rw [← hU, ← mul_assoc, Units.mul_inv, one_mul]
  let w : Fin d → LetA O n := fun m => -(ν * ∑ m', Polynomial.aeval Y (ρ m m') * β m')
  have hw : ∀ m, w m ∈ W.AΔ := fun m => W.AΔ.neg_mem (W.AΔ.mul_mem hν (W.AΔ.sum_mem fun m' _ =>
      W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.ArcF.aeval_mem_AΔ W hY _) (hβ m')))
  have hkey : ∀ m, lA W ^ κ * lA W ^ κ * β m - ∑ k, aa k * HY m k = D * w m := by
    intro m
    have A2 : ∑ k, aa k * HY m k = ∑ m', (∑ k, HY m k * GY k m') * β m' := by
      simp only [aa, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m' _ => Finset.sum_congr rfl fun k _ => by ring
    have h1 : ∀ m', (∑ k, HY m k * GY k m') * β m' =
        lA W ^ κ * lA W ^ κ * ((if m = m' then 1 else 0) * β m') +
          Y ^ M * (Polynomial.aeval Y (ρ m m') * β m') := by
      intro m'
      have := hρ m m'
      simp only [HY, GY] at this ⊢
      rw [this, map_mul, map_pow, map_natCast, apply_ite (algebraMap O (LetA O n)), map_one, map_zero]
      unfold lA
      split_ifs <;> ring
    rw [A2, Finset.sum_congr rfl fun m' _ => h1 m', Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, w]
    rw [hYM']
    ring
  refine ⟨κ, fun k => ((U⁻¹ : W.EEˣ) : W.EE) * algebraMap (LetA O n) W.EE (aa k),
    ⟨κ, 0, fun k => ∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r), aa,
      fun k => ⟨yy k, hyy k, rfl⟩, fun k => ⟨haa k, hcoef k⟩, ?_⟩,
    fun k => ⟨aa k, haa k, by rw [hcoef k, haal k]⟩⟩
  have hsum : ∑ k, aa k • ((W.φD T) ^ e)
      (∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r)) =
      ∑ m, (∑ k, aa k * HY m k) • ((W.φD T) ^ e) (b m) := by
    simp only [Formalism.MainNotions.UnusedSlot80.ArcF.phi_trunc, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    simp only [HY, ← hYdef]
    congr 1
    refine Finset.sum_congr rfl fun r _ => mul_comm _ _
  have hfin : lA W ^ 0 • (lA W ^ κ • Λ • (lA W ^ κ • x) - ∑ k, aa k • ((W.φD T) ^ e)
        (∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r))) =
      D • ∑ m, w m • ((W.φD T) ^ e) (b m) := by
    rw [pow_zero, one_smul, hsum, smul_comm Λ, hΛx]
    simp only [Finset.smul_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [smul_smul]
    rw [← sub_smul, ← hkey m]
    congr 1
    ring
  rw [hfin]
  exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_of_mem W T c' e _ (AddSubgroup.sum_mem _ fun m _ =>
    Formalism.MainNotions.UnusedSlot80.Relay2.Pp_gen W T c' e (hw m) (hb.1.1 m))

/- English proof (translation)
Take `⟨κ, Hh, hHh⟩` from `horTr_exists W hO2 hH hCA T hTc c' b sol hb M`. Use `choose u hu hfu using hf`. Use `set Λ : LetA O n := abelian₂ W A (c' + (e : ZMod n)) e with hΛdef`. Take `⟨U, hU⟩` from `lam_unit W hR A (c' + (e : ZMod n)) e`. Set `aa : Fin d → LetA O n` to `fun k => letE (c' + (e : ZMod n)) * 1 * u k`.

Establish `haa : ∀ k, aa k ∈ W.AΔ` using `fun k => W.AΔ.mul_mem (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W _) W.AΔ.one_mem) (hu k)`. Use `set z : W.DD T := ∑ k, aa k • ((W.φD T) ^ e) (Hh k) with hz`. Establish `hzP : z ∈ Pp W T c' e` using `AddSubgroup.sum_mem _ fun k _ => Formalism.MainNotions.UnusedSlot80.Relay2.Pp_smul W T c' e (haa k) _ (horTr_mem W T c' b sol hb.1 hR.1 M κ e k (hHh k))`. Establish `hΛz : Λ • (((U⁻¹ : W.EEˣ) : W.EE) • z) = z`. Rewrite using `[← algebraMap_smul W.EE Λ, ← hU, smul_smul, Units.mul_inv, one_smul]`.

Use `⟨κ, ((U⁻¹ : W.EEˣ) : W.EE) • z, ⟨z, hzP, by rw [hΛz, one_smul]⟩, κ, 0, Hh, fun k => lA W ^ κ * aa k, hHh, fun k => ⟨W.AΔ.mul_mem (lA_mem W κ) (haa k), ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_left_comm, hfu k] show lE W κ * _ = algebraMap (LetA O n) W.EE (lA W ^ κ * aa k)`. Rewrite using `[map_mul (algebraMap (LetA O n) W.EE) (lA W ^ κ), map_pow]`. Unfold `lE lA`. Rewrite using `[map_natCast]`.

Rewrite using `[hΛz, pow_zero, one_smul, hz]`. Simplify using `only [Finset.smul_sum, mul_smul, sub_self]`. Conclude with `Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_zero W T c' e _`.
-/
theorem pOfSec' (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hCA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (A : ArcP n) (c' : ZMod n) (e M : ℕ) (T : LocLat G Qp LL O) (hTc : IsCrys PD T.ρ) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T c' b sol) (f : Fin d → W.EE)
    (hf : ∀ k, InFr W (c' + (e : ZMod n)) 1 (abelian₂ W A (c' + (e : ZMod n)) e) (f k)) :
    ∃ (κ : ℕ) (x : W.DD T), InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • x) ∧
      RepVV W T c' e M (abelian₂ W A (c' + (e : ZMod n)) e) b sol x (fun k => lE W κ * f k) := by
  obtain ⟨κ, Hh, hHh⟩ := horTr_exists W hO2 hH hCA T hTc c' b sol hb M
  choose u hu hfu using hf
  set Λ : LetA O n := abelian₂ W A (c' + (e : ZMod n)) e with hΛdef
  obtain ⟨U, hU⟩ := lam_unit W hR A (c' + (e : ZMod n)) e
  let aa : Fin d → LetA O n := fun k => letE (c' + (e : ZMod n)) * 1 * u k
  have haa : ∀ k, aa k ∈ W.AΔ := fun k =>
    W.AΔ.mul_mem (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W _) W.AΔ.one_mem) (hu k)
  set z : W.DD T := ∑ k, aa k • ((W.φD T) ^ e) (Hh k) with hz
  have hzP : z ∈ Pp W T c' e := AddSubgroup.sum_mem _ fun k _ =>
    Formalism.MainNotions.UnusedSlot80.Relay2.Pp_smul W T c' e (haa k) _ (horTr_mem W T c' b sol hb.1 hR.1 M κ e k (hHh k))
  have hΛz : Λ • (((U⁻¹ : W.EEˣ) : W.EE) • z) = z := by
    rw [← algebraMap_smul W.EE Λ, ← hU, smul_smul, Units.mul_inv, one_smul]
  refine ⟨κ, ((U⁻¹ : W.EEˣ) : W.EE) • z, ⟨z, hzP, by rw [hΛz, one_smul]⟩, κ, 0, Hh,
    fun k => lA W ^ κ * aa k, hHh, fun k => ⟨W.AΔ.mul_mem (lA_mem W κ) (haa k), ?_⟩, ?_⟩
  · rw [mul_left_comm, hfu k]
    show lE W κ * _ = algebraMap (LetA O n) W.EE (lA W ^ κ * aa k)
    rw [map_mul (algebraMap (LetA O n) W.EE) (lA W ^ κ), map_pow]
    unfold lE lA
    rw [map_natCast]
  · rw [hΛz, pow_zero, one_smul, hz]
    simp only [Finset.smul_sum, mul_smul, sub_self]
    exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_zero W T c' e _

end Formalism.MainNotions.UnusedSlot80.LevC
