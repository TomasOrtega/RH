import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatementStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFirst
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticSecond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto

section Scale

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ}

def normScale (M : FlagModel y Ψ N j) (c : NonPluckerBlocks M.blk → ℂ) : Option K → ℂ
  | some k => if h : ∀ p, M.blk p ≠ some k then c ⟨k, h⟩ else 1
  | none => 1

/- English proof (translation)
Consider the cases of `o with`. Consider the case `none => exact one_ne_zero`. Consider the case `some k`. Distinguish the cases in `h : ∀ p, M.blk p ≠ some k`. Use `show dite _ _ _ ≠ 0`.

Rewrite using `[dif_pos h]`. Conclude with `hc ⟨k, h⟩`. Use `show dite _ _ _ ≠ 0`. Rewrite using `[dif_neg h]`. Conclude with `one_ne_zero`.
-/
theorem normScale_ne (M : FlagModel y Ψ N j) {c : NonPluckerBlocks M.blk → ℂ} (hc : ∀ k, c k ≠ 0) (o : Option K) :
    normScale M c o ≠ 0 := by
  cases o with
  | none => exact one_ne_zero
  | some k =>
    by_cases h : ∀ p, M.blk p ≠ some k
    · show dite _ _ _ ≠ 0
      rw [dif_pos h]
      exact hc ⟨k, h⟩
    · show dite _ _ _ ≠ 0
      rw [dif_neg h]
      exact one_ne_zero

/- English proof (translation)
Simplify using `[normScale, k.2]`.
-/
theorem normScale_base (M : FlagModel y Ψ N j) (c : NonPluckerBlocks M.blk → ℂ) (k : NonPluckerBlocks M.blk) :
    normScale M c (some k.1) = c k := by
  simp [normScale, k.2]

/- English proof (translation)
Establish `h : ¬ ∀ p, M.blk p ≠ some k` using `fun h => h p hp`. Use `show dite _ _ _ = 1`. Rewrite using `[dif_neg h]`.
-/
theorem normScale_step (M : FlagModel y Ψ N j) (c : NonPluckerBlocks M.blk → ℂ) {p : Ψ × Fin N} {k : K}
    (hp : M.blk p = some k) : normScale M c (some k) = 1 := by
  have h : ¬ ∀ p, M.blk p ≠ some k := fun h => h p hp
  show dite _ _ _ = 1
  rw [dif_neg h]

end Scale

/- English proof (translation)
Introduce `K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h hctx z hzO`. Take `⟨hb, hba, hk₀, hca, hcb, hAV, hF, hBC, hr, -, -⟩` from `hctx`. Take `⟨hz, hsrc, hV₀, -, -⟩` from `hzO`. Establish `z₀ : fstPt k₀ z ∈ mcPts (mCoordIdeal y)` using `CPts.comp_mem_mcPts (Pts.isBlockMap_v₀ k₀) (algebraMap Φ (RatFunc Φ)) (funext fun _ => rfl) hz`. Establish `hbm : baseOf M k₀ z ∈ mcPts (mCoordIdeal M.x)` using `CPts.base_mem M z₀`.

Take `⟨hblm, hbl1, hblG, horb⟩` from `hBC.2.2.2.2 _ hV₀`. Rewrite `horb` using `[(Rb.A.chart kb).left_inv hsrc]`. Establish `horbit : SameOrbit (bl (Rb.A.chart kb (r (baseOf M k₀ z)))) (baseOf M k₀ z)` using `orbit_trans (orbit_symm horb) (hr _ hbm)`. Establish `hG : M.GoodAt F (mCoordIdeal (baseOf M k₀ z))`. Rewrite using `[← CovMap.mCoordIdeal_eq_of_sameOrbit horbit]` and apply the resulting hypothesis.

Use `⟨hbm, hG, horbit, ?_⟩` and prove the remaining obligations. Take `⟨c, hc, hce⟩` from `id horbit`. Set `z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ` to `fun q => normScale M c q.1 * z q`. Establish `hz' : z' ∈ mcPts (wP M τ a k₀ ca cb)` using `mcPts_smul (CoordinateConeArithVar.isMultiHomogIdeal _) _ (normScale_ne M hc) hz`. Establish `hbase : basePart M.blk (fstPt k₀ z') = bl (Rb.A.chart kb (r (baseOf M k₀ z)))`.

Rewrite using `[hce]`. Use function extensionality and compare the values at `q`. Use `show normScale M c (some q.1.1) * z _ = c q.1 * z _`. Rewrite using `[normScale_base]`. Establish `hval : ∀ s : M.Ω, valAt M.x s (basePart M.blk (fstPt k₀ z')) = valAt M.x s (baseOf M k₀ z)` using `fun s => by`.

Rewrite using `[hbase]`. Conclude with `CovMap.LocImg.valAt_orbit horbit hbm s`. Take `⟨h', t', H, H'⟩` from `(GlobalTheory.T.log_period_statement K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hba hk₀ hca hcb hAV F z' hF (by rw [hbase]; exact hblm) (by rw [hbase]; exact hblG) (by rw [hbase]; exact hbl1)).1 hz'`. Use `⟨h', t', H.2.1, fun p k hp => ?_, ?_⟩` and prove the remaining obligations. Take `⟨α, hα, e⟩` from `H.2.2 p k hp`.

Use `⟨α, hα, fun m => ?_⟩` and prove the remaining obligations. Establish `e'` using `e m`. Simplify using `only [hval] at e'`. Rewrite using `[← e']`. Use `show z _ = normScale M c (some k) * z _`.

Rewrite using `[normScale_step M c hp, one_mul]`. Take `⟨α, hα, e⟩` from `H'.2.2 (τ, a) k₀ hk₀`. Use `⟨α, hα, fun m => ?_⟩` and prove the remaining obligations. Establish `e'` using `e m`. Rewrite `e'` using `[Pts.basePart_snd M hk₀]`.

Simplify using `only [hval, Function.update_self] at e'`. Rewrite using `[← e', Pts.snd_self, Pts.snd_self]`. Use `show z _ = 1 * z _`. Rewrite using `[one_mul]`.
-/
theorem norm : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, baseOf M k₀ z ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt F (mCoordIdeal (baseOf M k₀ z)) ∧ SameOrbit (bl (Rb.A.chart kb (r (baseOf M k₀ z)))) (baseOf M k₀ z) ∧ ∃ (h' : Ψ → Matrix (Fin N) (Fin N) ℂ) (t' : ℂ), (∀ τ', IsBlockDiag j (h' τ') ∧ (h' τ').det ≠ 0) ∧ (∀ p k, M.blk p = some k → ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k, fstPt k₀ z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z) * minorIJ (h' p.1) I (stepCols N j p.2)) ∧ ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k₀, sndPt k₀ z ⟨k₀, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z) * minorIJ (h' τ * (1 + Matrix.single cb ca t')) I (stepCols N j a) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h hctx z hzO
  obtain ⟨hb, hba, hk₀, hca, hcb, hAV, hF, hBC, hr, -, -⟩ := hctx
  obtain ⟨hz, hsrc, hV₀, -, -⟩ := hzO
  have z₀ : fstPt k₀ z ∈ mcPts (mCoordIdeal y) :=
    CPts.comp_mem_mcPts (Pts.isBlockMap_v₀ k₀) (algebraMap Φ (RatFunc Φ)) (funext fun _ => rfl) hz
  have hbm : baseOf M k₀ z ∈ mcPts (mCoordIdeal M.x) := CPts.base_mem M z₀
  obtain ⟨hblm, hbl1, hblG, horb⟩ := hBC.2.2.2.2 _ hV₀
  rw [(Rb.A.chart kb).left_inv hsrc] at horb
  have horbit : SameOrbit (bl (Rb.A.chart kb (r (baseOf M k₀ z)))) (baseOf M k₀ z) :=
    orbit_trans (orbit_symm horb) (hr _ hbm)
  have hG : M.GoodAt F (mCoordIdeal (baseOf M k₀ z)) := by
    rwa [← CovMap.mCoordIdeal_eq_of_sameOrbit horbit]
  refine ⟨hbm, hG, horbit, ?_⟩
  obtain ⟨c, hc, hce⟩ := id horbit
  let z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ := fun q => normScale M c q.1 * z q
  have hz' : z' ∈ mcPts (wP M τ a k₀ ca cb) :=
    mcPts_smul (CoordinateConeArithVar.isMultiHomogIdeal _) _ (normScale_ne M hc) hz
  have hbase : basePart M.blk (fstPt k₀ z') = bl (Rb.A.chart kb (r (baseOf M k₀ z))) := by
    rw [hce]
    funext q
    show normScale M c (some q.1.1) * z _ = c q.1 * z _
    rw [normScale_base]
  have hval : ∀ s : M.Ω, valAt M.x s (basePart M.blk (fstPt k₀ z')) = valAt M.x s (baseOf M k₀ z) := fun s => by
    rw [hbase]
    exact CovMap.LocImg.valAt_orbit horbit hbm s
  obtain ⟨h', t', H, H'⟩ := (GlobalTheory.T.log_period_statement K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hba hk₀ hca hcb hAV F z' hF
    (by rw [hbase]; exact hblm) (by rw [hbase]; exact hblG) (by rw [hbase]; exact hbl1)).1 hz'
  refine ⟨h', t', H.2.1, fun p k hp => ?_, ?_⟩
  · obtain ⟨α, hα, e⟩ := H.2.2 p k hp
    refine ⟨α, hα, fun m => ?_⟩
    have e' := e m
    simp only [hval] at e'
    rw [← e']
    show z _ = normScale M c (some k) * z _
    rw [normScale_step M c hp, one_mul]
  · obtain ⟨α, hα, e⟩ := H'.2.2 (τ, a) k₀ hk₀
    refine ⟨α, hα, fun m => ?_⟩
    have e' := e m
    rw [Pts.basePart_snd M hk₀] at e'
    simp only [hval, Function.update_self] at e'
    rw [← e', Pts.snd_self, Pts.snd_self]
    show z _ = 1 * z _
    rw [one_mul]

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto
