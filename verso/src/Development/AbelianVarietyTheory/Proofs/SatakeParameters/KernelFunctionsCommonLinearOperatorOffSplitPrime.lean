import Mathlib
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesLaw
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepComb
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCommonScaleLatticePairsSplitPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommonRepresentativesPeriodLatticeHalvesStatement

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct
open Formalism.L2.Th1.H Formalism.L2.KerInert.RepComb

namespace GlobalTheory.KerCommon

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_common_scale_lattice_pairs_split_prime`.
-/
theorem exists_scale : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), P ∉ SS → Formalism.L2.Col.conjPrime₂ P ∉ SS → ((cl : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ∀ (ι : Type) [Fintype ι] (a b : ℕ) (N : ι → Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N₀ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : ι → Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (N₀' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), (∀ i, GL3Theta.EqOff D P (N i) N₀ ∧ GL3Theta.EqOff D P (N' i) N₀') → ∃ g : 𝓞 D.host.E, (∃ k : 𝓞 D.host.E, g = 1 + (cl : 𝓞 D.host.E) * k) ∧ (∀ Q ∈ SS, g ∉ Q.asIdeal) ∧ ∀ i, ((∀ x ∈ N i, g • x ∈ N₀) ∧ ∀ x ∈ N₀, g • x ∈ N i) ∧ ((∀ x ∈ N' i, g • x ∈ N₀') ∧ ∀ x ∈ N₀', g • x ∈ N' i) := GlobalTheory.T.exists_common_scale_lattice_pairs_split_prime

/- English proof (translation)
Introduce `E _ _ _ a b AA0 N₁ N₂ N₁' N₂' w h2 h1 x hx`. Unfold `perO at hx ⊢`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨r, hr, y, hy, rfl⟩` from `hz`.

Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨r, hr, (w * w) • y, ?_, ?_⟩` and prove the remaining obligations. Introduce `v hv`. Establish `h3` using `h1 _ (hy _ (h2 v hv))`. Establish `e : ((w * w) • y) v = w • y (w • v)`.

Rewrite using `[LinearMap.smul_apply, mul_smul, LinearMap.map_smul_of_tower]`. Rewrite using `[e]`. Conclude with `h3`. Rewrite using `[smul_comm]`. Consider the case `zero => rw [smul_zero]`.

Conclude with `zero_mem _`. Consider the case `add _ _ _ _ ha hb => rw [smul_add]`. Conclude with `add_mem ha hb`. Consider the case `smul o z _ h => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ o h`.
-/
theorem perO_scale : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (AA0 : Submodule (𝓞 E) E) (N₁ N₂ : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N₁' N₂' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (w : 𝓞 E), (∀ y ∈ N₂, w • y ∈ N₁) → (∀ y ∈ N₁', w • y ∈ N₂') → ∀ x ∈ perO AA0 N₁ N₁', (w * w) • x ∈ perO AA0 N₂ N₂' := by
  intro E _ _ _ a b AA0 N₁ N₂ N₁' N₂' w h2 h1 x hx
  unfold perO at hx ⊢
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, hr, y, hy, rfl⟩ := hz
    apply Submodule.subset_span
    refine ⟨r, hr, (w * w) • y, ?_, ?_⟩
    · intro v hv
      have h3 := h1 _ (hy _ (h2 v hv))
      have e : ((w * w) • y) v = w • y (w • v) := by
        rw [LinearMap.smul_apply, mul_smul, LinearMap.map_smul_of_tower]
      rw [e]
      exact h3
    · rw [smul_comm]
  | zero => rw [smul_zero]; exact zero_mem _
  | add _ _ _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul o z _ h => rw [smul_comm]; exact Submodule.smul_mem _ o h

/- English proof (translation)
The claim follows from `GlobalTheory.T.common_representatives_period_lattice_halves`.
-/
theorem common_reps : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι κ : Type) [Fintype ι] [Nonempty ι] [Fintype κ] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (AA0 : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E))) (cl : ℕ) (N₀ : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N₀' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (N : κ → Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : κ → Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (g : 𝓞 E), δ ≠ 0 → (∃ k : 𝓞 E, g = 1 + (cl : 𝓞 E) * k) → (∀ i, (∀ x ∈ perO AA0 (N i) (N' i), g • x ∈ perO AA0 N₀ N₀') ∧ ∀ x ∈ perO AA0 N₀ N₀', g • x ∈ perO AA0 (N i) (N' i)) → relIdx (LamC emb δ AA0 N₀ N₀') (AC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → relIdx (BC emb δ AA0 SS N₀ N₀' cl) (LamC emb δ AA0 N₀ N₀' ⊓ AC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → relIdx (LamC emb δ AA0 N₀ N₀') (BC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → ∃ SX SA SB : Finset (VV ι a b), ∀ i, IsReps (LamC emb δ AA0 (N i) (N' i)) (AC emb δ AA0 SS (N i) (N' i) cl) SX ∧ IsReps (BC emb δ AA0 SS (N i) (N' i) cl) (LamC emb δ AA0 (N i) (N' i) ⊓ AC emb δ AA0 SS (N i) (N' i) cl) SA ∧ IsReps (LamC emb δ AA0 (N i) (N' i)) (BC emb δ AA0 SS (N i) (N' i) cl) SB := GlobalTheory.T.common_representatives_period_lattice_halves

/- English proof (translation)
Assemble the required witnesses or components as `⟨D.eTau.symm (Classical.arbitrary _)⟩`.
-/
theorem tau_nonempty (D : D7) : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩

/- English proof (translation)
Establish `hm : ∀ y, y ∈ Formalism.HermitianLatticesTheory.dual (Formalism.L2.Col.hStd D.host.E n) L ↔ ∀ x ∈ L, Formalism.BasicNotions.stdH D.host.E n x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range`. Introduce `y`. Simplify using `only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars, Submodule.mem_one, RingHom.mem_range]`. Both sides reduce to the same expression. Unfold `Formalism.HermitianLatticesTheory.IsUnimodular`.

Prove the components needed by the constructor for the conclusion. Introduce `h y`. Rewrite using `[← hm y, h]`. Introduce `h`. Use extensionality with `y`.

Rewrite using `[hm y]`. Conclude with `(h y).symm`.
-/
theorem unimod_iff {D : D7} {n : ℕ} (L : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E n)) :
    Formalism.HermitianLatticesTheory.IsUnimodular (Formalism.L2.Col.hStd D.host.E n) L ↔
      ∀ y, y ∈ L ↔ ∀ x ∈ L, Formalism.BasicNotions.stdH D.host.E n x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  have hm : ∀ y, y ∈ Formalism.HermitianLatticesTheory.dual (Formalism.L2.Col.hStd D.host.E n) L ↔
      ∀ x ∈ L, Formalism.BasicNotions.stdH D.host.E n x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    intro y
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars,
      Submodule.mem_one, RingHom.mem_range]
    rfl
  unfold Formalism.HermitianLatticesTheory.IsUnimodular
  constructor
  · intro h y
    rw [← hm y, h]
  · intro h
    ext y
    rw [hm y]
    exact (h y).symm

/- English proof (translation)
Establish `hl` using `hh_tw_lattice N' ⟨hA.2.2.2.1, hA.2.2.2.2.1⟩ hcl ex h01`. Conclude with `⟨hA.1, hA.2.1, hA.2.2.1, hl.fg, hl.span_eq_top, (unimod_iff _).1 (twist_selfDual D.host.E b N' cl ex hA.2.2.2.1 hcl hc ((unimod_iff _).2 hA.2.2.2.2.2))⟩`.
-/
theorem admissible_pair_twist {D : D7} {a b : ℕ} (cl : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E))
    (hA : TaylorLogMetric.admitted D a b N N') (hcl : 0 < cl) (ex : HeightOneSpectrum (𝓞 D.host.E) → ℤ)
    (h01 : ∀ Q, ex Q = 1 ∨ ex Q = 0 ∨ ex Q = -1) (hc : ∀ Q, ex (Formalism.L2.Col.conjPrime₂ Q) = -ex Q) :
    TaylorLogMetric.admitted D a b N (twist₂ N' cl ex) := by
  have hl := hh_tw_lattice N' ⟨hA.2.2.2.1, hA.2.2.2.2.1⟩ hcl ex h01
  exact ⟨hA.1, hA.2.1, hA.2.2.1, hl.fg, hl.span_eq_top,
    (unimod_iff _).1 (twist_selfDual D.host.E b N' cl ex hA.2.2.2.1 hcl hc ((unimod_iff _).2 hA.2.2.2.2.2))⟩

/- English proof (translation)
Use `tau_nonempty D` as an intermediate fact. Establish `he1 : ∀ Q, expS SS Q = 1 ∨ expS SS Q = 0 ∨ expS SS Q = -1` using `expS_cases SS`. Establish `he2 : ∀ Q, (fun Q => -expS SS Q) Q = 1 ∨ (fun Q => -expS SS Q) Q = 0 ∨ (fun Q => -expS SS Q) Q = -1`. Introduce `Q`. Use `he1 Q` as an intermediate fact.

Use `show -expS SS Q = 1 ∨ -expS SS Q = 0 ∨ -expS SS Q = -1`. Use linear arithmetic over natural numbers and integers. Establish `hconj1 : ∀ Q, expS SS (Formalism.L2.Col.conjPrime₂ Q) = -expS SS Q` using `exponent_set_conjugate D.host.E SS hSS`. Establish `hconj2 : ∀ Q, (fun Q => -expS SS Q) (Formalism.L2.Col.conjPrime₂ Q) = -(fun Q => -expS SS Q) Q`. Introduce `Q`.

Use `show -expS SS (Formalism.L2.Col.conjPrime₂ Q) = - -expS SS Q`. Rewrite using `[hconj1 Q]`. Conclude with `half_periods_of_lattice D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (aaOf D cc) SS N N' cl (KS.Lat.delta_ne hcc hδ) hcl hSS hA.2.2.1.1 (laFacts_of_adm B hcc hδ hA) (laFacts_of_adm B hcc hδ (admiss …`.
-/
theorem split_of_adm {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E))
    (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : TaylorLogMetric.admitted D a b N N') (hcl : 0 < cl)
    (hSS : ∀ P ∈ SS, Formalism.L2.Col.conjPrime₂ P ∉ SS) :
    SplitHyp (hK D cc δ a b) (alK D cc δ a b) (halfA cc δ SS cl N N') (halfB cc δ SS cl N N') (lamK cc δ N N') := by
  have := tau_nonempty D
  have he1 : ∀ Q, expS SS Q = 1 ∨ expS SS Q = 0 ∨ expS SS Q = -1 := expS_cases SS
  have he2 : ∀ Q, (fun Q => -expS SS Q) Q = 1 ∨ (fun Q => -expS SS Q) Q = 0 ∨ (fun Q => -expS SS Q) Q = -1 := by
    intro Q
    have := he1 Q
    show -expS SS Q = 1 ∨ -expS SS Q = 0 ∨ -expS SS Q = -1
    omega
  have hconj1 : ∀ Q, expS SS (Formalism.L2.Col.conjPrime₂ Q) = -expS SS Q := exponent_set_conjugate D.host.E SS hSS
  have hconj2 : ∀ Q, (fun Q => -expS SS Q) (Formalism.L2.Col.conjPrime₂ Q) = -(fun Q => -expS SS Q) Q := by
    intro Q
    show -expS SS (Formalism.L2.Col.conjPrime₂ Q) = - -expS SS Q
    rw [hconj1 Q]
  exact half_periods_of_lattice D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (aaOf D cc) SS N N' cl
    (KS.Lat.delta_ne hcc hδ) hcl hSS hA.2.2.1.1 (laFacts_of_adm B hcc hδ hA)
    (laFacts_of_adm B hcc hδ (admissible_pair_twist cl N N' hA hcl _ he1 hconj1)) (laFacts_of_adm B hcc hδ (admissible_pair_twist cl N N' hA hcl _ he2 hconj2))

/- English proof (translation)
The claim follows from `finite_index_of_fg D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ (aaOf D cc) SS N N' cl hcl (period_lattice_finitely_generated D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ (aaOf D cc) N N' hA.2.2.2.1 hA.2.2.1.2.1 (aaOf_fg cc))`.
-/
theorem finIdx_of_adm {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E))
    (hA : TaylorLogMetric.admitted D a b N N') (hcl : 0 < cl) : FinIdx cc δ SS cl N N' :=
  finite_index_of_fg D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ (aaOf D cc) SS N N' cl hcl
    (period_lattice_finitely_generated D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ (aaOf D cc) N N' hA.2.2.2.1 hA.2.2.1.2.1 (aaOf_fg cc))

/- English proof (translation)
Establish `hm` using `(hV a b N N' hA).1`. Introduce `x hx z`. Establish `hx' : x ∈ TaylorLogMetric.La D B.tor N N'` using `by rw [← lamK_eq cc δ N N']; exact hx`. Establish `h1` using `hm.2 x hx' z`. Rewrite `h1` using `[U_eq_opU]`.

Establish `hal : alK D cc δ a b x = TaylorLogMetric.al D B.tor x`. Rewrite using `[KS.Lat.al_eq_La B hcc hδ hA x hx']`. Unfold `alK alV`. Rewrite using `[HV_eq_formV]`. Rewrite using `[hal]`.

Conclude with `h1`.
-/
theorem eNat_fixed_of_vec {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hV : B.VecP χ) {a b : ℕ}
    {N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)} (hA : TaylorLogMetric.admitted D a b N N') :
    B.eNat χ a b N N' ∈ fixedBy (hK D cc δ a b) (alK D cc δ a b) (lamK cc δ N N') := by
  have hm := (hV a b N N' hA).1
  intro x hx z
  have hx' : x ∈ TaylorLogMetric.La D B.tor N N' := by rw [← lamK_eq cc δ N N']; exact hx
  have h1 := hm.2 x hx' z
  rw [U_eq_opU] at h1
  have hal : alK D cc δ a b x = TaylorLogMetric.al D B.tor x := by
    rw [KS.Lat.al_eq_La B hcc hδ hA x hx']
    unfold alK alV
    rw [HV_eq_formV]
  rw [hal]
  exact h1

/- English proof (translation)
Establish `hg' : g ∈ Q.asIdeal.primeCompl` using `hg`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, hx⟩`. Conclude with `⟨g * s, Q.asIdeal.primeCompl.mul_mem hg' hs, by rw [mul_smul]; exact h1 _ hx⟩`.

Introduce and unpack `⟨s, hs, hx⟩`. Conclude with `⟨g * s, Q.asIdeal.primeCompl.mul_mem hg' hs, by rw [mul_smul]; exact h2 _ hx⟩`.
-/
theorem locP_eq_of_scale {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module (𝓞 E) W]
    (M M₀ : Submodule (𝓞 E) W) (g : 𝓞 E) (Q : HeightOneSpectrum (𝓞 E)) (hg : g ∉ Q.asIdeal)
    (h1 : ∀ x ∈ M, g • x ∈ M₀) (h2 : ∀ x ∈ M₀, g • x ∈ M) :
    Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M = Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M₀ := by
  have hg' : g ∈ Q.asIdeal.primeCompl := hg
  ext x
  constructor
  · rintro ⟨s, hs, hx⟩
    exact ⟨g * s, Q.asIdeal.primeCompl.mul_mem hg' hs, by rw [mul_smul]; exact h1 _ hx⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨g * s, Q.asIdeal.primeCompl.mul_mem hg' hs, by rw [mul_smul]; exact h2 _ hx⟩

/- English proof (translation)
Introduce `D cc δ B χ hcc hδ hδ0 _hL hV SS cl hcl hSS a b P _hP hPS hPS' hcP _hcP' N₀ N₀' Ξ hA0 hD ι _ N N' hN`. Use `tau_nonempty D` as an intermediate fact. Take `⟨g, ⟨k, hk⟩, hgQ, hg⟩` from `exists_scale D P SS cl hPS hPS' hcP ι a b N N₀ N' N₀' fun i => (hN i).2`. Establish `hsc : ∀ i, (∀ x ∈ perO (aaOf D cc) (N i) (N' i), (g * g) • x ∈ perO (aaOf D cc) N₀ N₀') ∧ ∀ x ∈ perO (aaOf D cc) N₀ N₀', (g * g) • x ∈ perO (aaOf D cc) (N i) (N' i)` using `fun i => ⟨perO_scale D.host.E a b (aaOf D cc) (N i) N₀ (N' i) N₀' g (hg i).1.2 (hg i).2.1, perO_scale D.host.E a b (aaOf D cc) N₀ (N i) N₀' (N' i) g (hg i).1.1 (hg i).2.2⟩`. Establish `hI0` using `finIdx_of_adm (cc := cc) (δ := δ) SS cl N₀ N₀' hA0 hcl`.

Take `⟨SX, SA, SB, hR⟩` from `common_reps D.host.E D.what₂.Tau ι a b (fun τ => TaylorLogMetric.embT D τ) δ (aaOf D cc) SS cl N₀ N₀' N N' (g * g) hδ0 ⟨k + k + (cl : 𝓞 D.host.E) * k * k, by rw [hk]; ring⟩ hsc hI0.1 hI0.2.1 hI0.2.2`. Establish `hxi0 : ∀ z, xiL (hK D cc δ a b) (alK D cc δ a b) 1 SX SA SB (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ) 0 z = 0`. Introduce `z`. Establish `h` using `(twist_linear _ (hK D cc δ a b) (alK D cc δ a b) 1 SX SA SB 1 (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ) (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ) 0 0 z).2.2.2`. Establish `e : (fun v : TaylorLogMetric.VC D a b => (1 : ℂ) * (0 : TaylorLogMetric.VC D a b → ℂ) v + (0 : TaylorLogMetric.VC D a b → ℂ) v) = 0`.

Use function extensionality and compare the values at `v`. Simplify using the standard rewrite rules. Rewrite `h` using `[e, one_mul]`. Take the linear combination `-h`. Use `⟨{ toFun := fun θ => xiL (hK D cc δ a b) (alK D cc δ a b) 1 SX SA SB (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ) θ, map_add' := ?_, map_smul' := ?_ }, fun i => ?_⟩` and prove the remaining obligations.

Introduce `x y`. Use function extensionality and compare the values at `z`. Establish `h` using `(twist_linear _ (hK D cc δ a b) (alK D cc δ a b) 1 SX SA SB 1 (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ) (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ) x y z).2.2.2`. Establish `e : (fun v => (1 : ℂ) * x v + y v) = x + y` using `by funext v; simp`. Rewrite `h` using `[e, one_mul]`.

Simplify using `using h`. Introduce `c x`. Use function extensionality and compare the values at `z`. Establish `h` using `(twist_linear _ (hK D cc δ a b) (alK D cc δ a b) 1 SX SA SB c (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ) (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ) x 0 z).2.2.2`. Establish `e : (fun v => c * x v + (0 : TaylorLogMetric.VC D a b → ℂ) v) = c • x` using `by funext v; simp`.

Rewrite `h` using `[e, hxi0, add_zero]`. Simplify using `using h`. Take `⟨hAi, -, -⟩` from `hN i`. Establish `hyp` using `split_of_adm B SS cl (N i) (N' i) hcc hδ hAi hcl hSS`. Establish `hIi` using `finIdx_of_adm (cc := cc) (δ := δ) SS cl (N i) (N' i) hAi hcl`.

Establish `hθ` using `eNat_fixed_of_vec B χ hcc hδ hV hAi`. Establish `hg2 : ∀ Q ∈ SS, g * g ∉ Q.asIdeal` using `fun Q hQ h => (Q.isPrime.mem_or_mem h).elim (hgQ Q hQ) (hgQ Q hQ)`. Establish `hDi : DatLoc D cc SS cl (N i) (N' i) Ξ` using `hD.of_locP_eq fun Q hQ => locP_eq_of_scale _ _ (g * g) Q (hg2 Q hQ) (hsc i).1 (hsc i).2`. Establish `hinv` using `hDi.invOn (fun τ => TaylorLogMetric.embT D τ) δ (embH_inj _ hδ0)`. Use function extensionality and compare the values at `z`.

Conclude with `twist_representatives _ (hK D cc δ a b) (alK D cc δ a b) _ _ _ hyp SX SA SB _ _ _ (hR i).1 (hR i).2.1 (hR i).2.2 (repsOf_spec _ _ hIi.1) (repsOf_spec _ _ hIi.2.1) (repsOf_spec _ _ hIi.2.2) 1 _ hθ _ hinv z`.
-/
theorem kerTh_common_op : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → B.LatAll → B.VecP χ → ∀ (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), 0 < cl → (∀ Q ∈ SS, Formalism.L2.Col.conjPrime₂ Q ∉ SS) → ∀ (a b : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)), GL3Theta.SplitP D P → P ∉ SS → Formalism.L2.Col.conjPrime₂ P ∉ SS → ((cl : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((cl : ℕ) : 𝓞 D.host.E) ∉ (Formalism.L2.Col.conjPrime₂ P).asIdeal → ∀ (N₀ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N₀' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), TaylorLogMetric.admitted D a b N₀ N₀' → DatLoc D cc SS cl N₀ N₀' Ξ → ∀ (ι : Type) [Fintype ι] (N : ι → Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : ι → Submodule (𝓞 D.host.E) (Fin b → D.host.E)), (∀ i, TaylorLogMetric.admitted D a b (N i) (N' i) ∧ GL3Theta.EqOff D P (N i) N₀ ∧ GL3Theta.EqOff D P (N' i) N₀') → ∃ T : (TaylorLogMetric.VC D a b → ℂ) →ₗ[ℂ] (TaylorLogMetric.VC D a b → ℂ), ∀ i, kerTh B χ SS cl (N i) (N' i) Ξ = T (B.eNat χ a b (N i) (N' i)) := by
  intro D cc δ B χ hcc hδ hδ0 _hL hV SS cl hcl hSS a b P _hP hPS hPS' hcP _hcP' N₀ N₀' Ξ hA0 hD ι _ N N' hN
  have := tau_nonempty D
  obtain ⟨g, ⟨k, hk⟩, hgQ, hg⟩ := exists_scale D P SS cl hPS hPS' hcP ι a b N N₀ N' N₀' fun i => (hN i).2
  have hsc : ∀ i, (∀ x ∈ perO (aaOf D cc) (N i) (N' i), (g * g) • x ∈ perO (aaOf D cc) N₀ N₀') ∧
      ∀ x ∈ perO (aaOf D cc) N₀ N₀', (g * g) • x ∈ perO (aaOf D cc) (N i) (N' i) := fun i =>
    ⟨perO_scale D.host.E a b (aaOf D cc) (N i) N₀ (N' i) N₀' g (hg i).1.2 (hg i).2.1,
      perO_scale D.host.E a b (aaOf D cc) N₀ (N i) N₀' (N' i) g (hg i).1.1 (hg i).2.2⟩
  have hI0 := finIdx_of_adm (cc := cc) (δ := δ) SS cl N₀ N₀' hA0 hcl
  obtain ⟨SX, SA, SB, hR⟩ := common_reps D.host.E D.what₂.Tau ι a b (fun τ => TaylorLogMetric.embT D τ) δ (aaOf D cc) SS cl N₀ N₀' N N' (g * g) hδ0
    ⟨k + k + (cl : 𝓞 D.host.E) * k * k, by rw [hk]; ring⟩ hsc hI0.1 hI0.2.1 hI0.2.2
  have hxi0 : ∀ z, xiL (hK D cc δ a b) (alK D cc δ a b) 1 SX SA SB (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ) 0 z = 0 := by
    intro z
    have h := (twist_linear _ (hK D cc δ a b) (alK D cc δ a b) 1 SX SA SB 1 (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ)
      (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ) 0 0 z).2.2.2
    have e : (fun v : TaylorLogMetric.VC D a b => (1 : ℂ) * (0 : TaylorLogMetric.VC D a b → ℂ) v + (0 : TaylorLogMetric.VC D a b → ℂ) v) = 0 := by
      funext v; simp
    rw [e, one_mul] at h
    linear_combination -h
  refine ⟨{ toFun := fun θ => xiL (hK D cc δ a b) (alK D cc δ a b) 1 SX SA SB (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ) θ,
            map_add' := ?_, map_smul' := ?_ }, fun i => ?_⟩
  · intro x y
    funext z
    have h := (twist_linear _ (hK D cc δ a b) (alK D cc δ a b) 1 SX SA SB 1 (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ)
      (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ) x y z).2.2.2
    have e : (fun v => (1 : ℂ) * x v + y v) = x + y := by funext v; simp
    rw [e, one_mul] at h
    simpa using h
  · intro c x
    funext z
    have h := (twist_linear _ (hK D cc δ a b) (alK D cc δ a b) 1 SX SA SB c (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ)
      (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ) x 0 z).2.2.2
    have e : (fun v => c * x v + (0 : TaylorLogMetric.VC D a b → ℂ) v) = c • x := by funext v; simp
    rw [e, hxi0, add_zero] at h
    simpa using h
  · obtain ⟨hAi, -, -⟩ := hN i
    have hyp := split_of_adm B SS cl (N i) (N' i) hcc hδ hAi hcl hSS
    have hIi := finIdx_of_adm (cc := cc) (δ := δ) SS cl (N i) (N' i) hAi hcl
    have hθ := eNat_fixed_of_vec B χ hcc hδ hV hAi
    have hg2 : ∀ Q ∈ SS, g * g ∉ Q.asIdeal := fun Q hQ h =>
      (Q.isPrime.mem_or_mem h).elim (hgQ Q hQ) (hgQ Q hQ)
    have hDi : DatLoc D cc SS cl (N i) (N' i) Ξ :=
      hD.of_locP_eq fun Q hQ => locP_eq_of_scale _ _ (g * g) Q (hg2 Q hQ) (hsc i).1 (hsc i).2
    have hinv := hDi.invOn (fun τ => TaylorLogMetric.embT D τ) δ (embH_inj _ hδ0)
    funext z
    exact twist_representatives _ (hK D cc δ a b) (alK D cc δ a b) _ _ _ hyp SX SA SB _ _ _ (hR i).1 (hR i).2.1 (hR i).2.2
      (repsOf_spec _ _ hIi.1) (repsOf_spec _ _ hIi.2.1) (repsOf_spec _ _ hIi.2.2) 1 _ hθ _ hinv z

end GlobalTheory.KerCommon
