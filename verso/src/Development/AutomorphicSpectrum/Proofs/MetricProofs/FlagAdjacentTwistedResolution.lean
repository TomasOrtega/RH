import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsLocSec
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverTwoFramesComparison
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryTwistMinorScalarStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedAtlasCompatibilityStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

/- English proof (translation)
Introduce `r s hrs`. Establish `h1 : (1 : Matrix (Fin N) (Fin N) ℂ) r s = 0` using `Matrix.one_apply_ne fun e => hrs (by rw [e])`. Establish `h2 : (Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) r s = 0`. Rewrite using `[Matrix.single_apply, if_neg]`. Introduce and unpack `⟨rfl, rfl⟩`.

Conclude with `hrs hs.symm`. Rewrite using `[Matrix.add_apply, h1, h2, add_zero]`.
-/
theorem isBlockDiag_one_add_single {N j : ℕ} {ca cb : Fin N} (hs : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) (t : ℂ) :
    IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) := by
  intro r s hrs
  have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) r s = 0 := Matrix.one_apply_ne fun e => hrs (by rw [e])
  have h2 : (Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) r s = 0 := by
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hrs hs.symm
  rw [Matrix.add_apply, h1, h2, add_zero]

/- English proof (translation)
Introduce `K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a b k₀ ca cb hb hab hk hca hcb RW pr hW x z₀ z₁ F h t hP hOrb`. Take `⟨hF, hG, h0, h1, hbd, hdet, ht, hE0, hE1⟩` from `hP`. Take `⟨hb0, -, -, -⟩` from `GlobalTheory.T.twisted_atlas_compatibility K ι Φ y Ψ N j M n e Rb τ a k₀ ca cb RW pr hk hW x z₀ z₁ h0 h1`. Take `⟨c, hc, hcz⟩ : SameOrbit z₁ z₀` from `orbit_trans (orbit_trans h1 (orbit_symm hOrb)) (orbit_symm h0)`. Establish `hz : ∀ q, z₁ q = c q.1 * z₀ q` using `fun q => congrFun hcz q`.

Establish `hbase : basePart M.blk z₁ = basePart M.blk z₀`. Use function extensionality and compare the values at `q`. Establish `e₀ : z₀ ⟨q.1.1, F.c q.1⟩ = 1` using `(hE0 a).1 q.1`. Establish `e₁ : z₁ ⟨q.1.1, F.c q.1⟩ = 1` using `(hE1 a).1 q.1`. Establish `hc1 : c q.1.1 = 1`.

Use `hz ⟨q.1.1, F.c q.1⟩` as an intermediate fact. Rewrite `this` using `[e₀, e₁, mul_one]`. Conclude with `this.symm`. Use `show z₁ ⟨q.1.1, q.2⟩ = z₀ ⟨q.1.1, q.2⟩`. Rewrite using `[hz, show c (Sigma.fst (⟨q.1.1, q.2⟩ : Σ k, ι k)) = 1 from hc1, one_mul]`.

Establish `hs : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j`. Establish `hN` using `M.j_le`. Establish `ha` using `a.2`. Establish `hb'` using `b.2`. Unfold `lastCol at hca`.

Apply the tactic sequence `split_ifs at hca with hl <;> omega`. Establish `hbd₁ : IsBlockDiag j (h * (1 + Matrix.single cb ca t))` using `hbd.mul (isBlockDiag_one_add_single hs t)`. Establish `hplk : ∀ m : ι k₀, plk M F (basePart M.blk z₀) (τ, a).2 ⟨k₀, m⟩ (h * (1 + Matrix.single cb ca t)) = c k₀ * plk M F (basePart M.blk z₀) (τ, a).2 ⟨k₀, m⟩ h` using `fun m => by`. Establish `e₀` using `(hE0 a).2 k₀ hk m`. Establish `e₁` using `(hE1 a).2 k₀ hk m`.

Rewrite `e₁` using `[hbase]`. Establish `e₂` using `hz ⟨k₀, m⟩`. Rewrite `e₂` using `[e₁, e₀]`. Conclude with `e₂`. Establish `hmin` using `Ind.minor_eq_of_plk M hb0 hF hG hk hbd₁ hbd hplk`.

Establish `hpl` using `GlobalTheory.T.elementary_twist_minor_scalar N j a b ca cb M.j_le hb hab hca hcb h 1 0 t (c k₀) hdet isBlockDiag_one Matrix.blockTriangular_one (fun I => by`. Establish `e : (1 + Matrix.single cb ca (0 : ℂ) : Matrix (Fin N) (Fin N) ℂ) = 1` using `by simp`. Rewrite using `[e, Matrix.mul_one]`. Conclude with `hmin I)`. Establish `h2` using `hpl.2`.

Simplify using `only [mul_zero, Matrix.one_apply_eq, mul_one, Finset.prod_const_one, one_mul] at h2`. Conclude with `ht h2.symm`.
-/
theorem not_sameOrbit_of_ptData : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ (x : RW.X) (z₀ z₁ : (Σ k, ι k) → ℂ) (F : FrameData ι Ψ N M.Ω M.blk) (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), IsPtData M τ a k₀ ca cb RW x z₀ z₁ F h t → ¬ SameOrbit (fstPt k₀ (RW.lift x x)) (sndPt k₀ (RW.lift x x)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a b k₀ ca cb hb hab hk hca hcb RW pr hW x z₀ z₁ F h t hP hOrb
  obtain ⟨hF, hG, h0, h1, hbd, hdet, ht, hE0, hE1⟩ := hP
  obtain ⟨hb0, -, -, -⟩ := GlobalTheory.T.twisted_atlas_compatibility K ι Φ y Ψ N j M n e Rb τ a k₀ ca cb RW pr hk hW x z₀ z₁ h0 h1
  obtain ⟨c, hc, hcz⟩ : SameOrbit z₁ z₀ := orbit_trans (orbit_trans h1 (orbit_symm hOrb)) (orbit_symm h0)
  have hz : ∀ q, z₁ q = c q.1 * z₀ q := fun q => congrFun hcz q

  have hbase : basePart M.blk z₁ = basePart M.blk z₀ := by
    funext q
    have e₀ : z₀ ⟨q.1.1, F.c q.1⟩ = 1 := (hE0 a).1 q.1
    have e₁ : z₁ ⟨q.1.1, F.c q.1⟩ = 1 := (hE1 a).1 q.1
    have hc1 : c q.1.1 = 1 := by
      have := hz ⟨q.1.1, F.c q.1⟩
      rw [e₀, e₁, mul_one] at this
      exact this.symm
    show z₁ ⟨q.1.1, q.2⟩ = z₀ ⟨q.1.1, q.2⟩
    rw [hz, show c (Sigma.fst (⟨q.1.1, q.2⟩ : Σ k, ι k)) = 1 from hc1, one_mul]
  have hs : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j := by
    have hN := M.j_le
    have ha := a.2
    have hb' := b.2
    unfold lastCol at hca
    split_ifs at hca with hl <;> omega
  have hbd₁ : IsBlockDiag j (h * (1 + Matrix.single cb ca t)) := hbd.mul (isBlockDiag_one_add_single hs t)
  have hplk : ∀ m : ι k₀, plk M F (basePart M.blk z₀) (τ, a).2 ⟨k₀, m⟩ (h * (1 + Matrix.single cb ca t)) =
      c k₀ * plk M F (basePart M.blk z₀) (τ, a).2 ⟨k₀, m⟩ h := fun m => by
    have e₀ := (hE0 a).2 k₀ hk m
    have e₁ := (hE1 a).2 k₀ hk m
    rw [hbase] at e₁
    have e₂ := hz ⟨k₀, m⟩
    rw [e₁, e₀] at e₂
    exact e₂
  have hmin := Ind.minor_eq_of_plk M hb0 hF hG hk hbd₁ hbd hplk
  have hpl := GlobalTheory.T.elementary_twist_minor_scalar N j a b ca cb M.j_le hb hab hca hcb h 1 0 t (c k₀) hdet isBlockDiag_one
    Matrix.blockTriangular_one (fun I => by
      have e : (1 + Matrix.single cb ca (0 : ℂ) : Matrix (Fin N) (Fin N) ℂ) = 1 := by simp
      rw [e, Matrix.mul_one]
      exact hmin I)
  have h2 := hpl.2
  simp only [mul_zero, Matrix.one_apply_eq, mul_one, Finset.prod_const_one, one_mul] at h2
  exact ht h2.symm

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
