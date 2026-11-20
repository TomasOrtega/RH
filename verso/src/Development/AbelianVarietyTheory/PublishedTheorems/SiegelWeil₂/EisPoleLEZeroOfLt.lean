import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Eis.SimplePoleModel

open GlobalTheory.Eis

/- English proof (translation)
Assemble the required witnesses or components as `⟨GlobalTheory.VolHeckeCompare.exists_isEta D, fun η h x => by rw [pow_mul, pow_two, GlobalTheory.VolHeckeCompare.IsEta_mul_self h x, one_pow]; rfl⟩`.
-/
theorem resEta_one_two_mul (D : D7) (k : ℕ) : ResEta D 1 (2 * k) :=
  ⟨GlobalTheory.VolHeckeCompare.exists_isEta D, fun η h x => by
    rw [pow_mul, pow_two, GlobalTheory.VolHeckeCompare.IsEta_mul_self h x, one_pow]; rfl⟩

open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in

/- English proof (translation)
Take `⟨a, ha⟩` from `exists_isMaj V`. Establish `hI` using `GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D V a ha`. Use `⟨a, sph V a s₁, ha, hI, ⟨continuous_const, fun _ => rfl⟩, resEta_one_two_mul D k, sph_mem hI s₁, fun g => ?_⟩` and prove the remaining obligations. Simplify using `only [sph, npow_eq_exp (hgtH_pos _)]`. Conclude with `Complex.exp_ne_zero _`.
-/
theorem hypotheses_hold (D : D7) (V : HSp D) (k : ℕ) (s₁ : ℂ) :
    ∃ (a : GL (Fin V.rank) (AE D)) (φ : GA D (dblSp V) → ℂ), IsMaj V a ∧
      HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) ∧ IsHeckeChar D 1 ∧ ResEta D 1 (2 * k) ∧
      φ ∈ degPS V a 1 s₁ ∧ ∀ g, φ g ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_isMaj V
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D V a ha
  refine ⟨a, sph V a s₁, ha, hI, ⟨continuous_const, fun _ => rfl⟩, resEta_one_two_mul D k, sph_mem hI s₁, fun g => ?_⟩
  simp only [sph, npow_eq_exp (hgtH_pos _)]
  exact Complex.exp_ne_zero _

/- English proof (translation)
The claim follows from `a.imp fun _ b => ⟨b.1, le_trans (by exact_mod_cast (by omega : (-((k + 1 : ℕ) : ℤ)) ≤ -(k : ℤ))) b.2⟩`.
-/
theorem poleLE_succ {h : ℂ → ℂ} {s₀ : ℂ} {k : ℕ} (a : PoleLE h s₀ k) : PoleLE h s₀ (k + 1) :=
  a.imp fun _ b => ⟨b.1, le_trans (by exact_mod_cast (by omega : (-((k + 1 : ℕ) : ℤ)) ≤ -(k : ℤ))) b.2⟩

/- English proof (translation)
Establish `h1` using `(sphConv D V a hI).isEisFamily_flat hI hφ hμ`. Use `(eisValueAt_iff_eisPoleLE.1 (h1.eisValueAt h1.analyticOnNhd_flat ?_)).1` and prove the remaining obligations. Establish `: (2 * V.rank : ℝ) < b` using `by exact_mod_cast hb`. Simplify using `only [Complex.div_ofNat_re, Complex.sub_re, Complex.natCast_re]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eisPoleLE_zero_of_lt {D : D7} {V : HSp D} {a : GL (Fin V.rank) (AE D)}
    (hI : HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a)) {μ : (AE D)ˣ →* Circle} {b : ℕ} (hμ : IsHeckeChar D μ)
    {s₁ : ℂ} {φ : GA D (dblSp V) → ℂ} (hφ : φ ∈ degPS V a μ s₁) (hb : 2 * V.rank < b) :
    EisPoleLE V (flat V a φ s₁) (((b : ℂ) - V.rank) / 2) 0 := by
  have h1 := (sphConv D V a hI).isEisFamily_flat hI hφ hμ
  refine (eisValueAt_iff_eisPoleLE.1 (h1.eisValueAt h1.analyticOnNhd_flat ?_)).1
  have : (2 * V.rank : ℝ) < b := by exact_mod_cast hb
  simp only [Complex.div_ofNat_re, Complex.sub_re, Complex.natCast_re]
  linarith

/- English proof (translation)
Use `⟨fun h D V a ha μ b hμ hb s₁ φ hφ h1 h2 => h D V (by omega) a ha (GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D V a ha) μ b hμ hb s₁ φ hφ h1, fun h D V _ a ha hI μ b hμ hb s₁ φ hφ h1 => ?_⟩` and prove the remaining obligations. Break down `le_or_gt b (2 * V.rank) with h2 | h2` into its components or cases. Conclude with `h D V a ha μ b hμ hb s₁ φ hφ h1 h2`. Use `eisPoleLE_zero_of_lt hI hμ hφ h2` as an intermediate fact. Conclude with `⟨this.1, fun g => poleLE_succ (this.2 g)⟩`.
-/
theorem simplePole_iff : Published.SiegelEisensteinSimplePole ↔
    ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a →
    ∀ (μ : (AE D)ˣ →* Circle) (b : ℕ), IsHeckeChar D μ → ResEta D μ b →
    ∀ (s₁ : ℂ) (φ : GA D (dblSp V) → ℂ), φ ∈ degPS V a μ s₁ →
      V.rank < b → b ≤ 2 * V.rank → EisPoleLE V (flat V a φ s₁) (((b : ℂ) - V.rank) / 2) 1 := by
  refine ⟨fun h D V a ha μ b hμ hb s₁ φ hφ h1 h2 => h D V (by omega) a ha (GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D V a ha)
    μ b hμ hb s₁ φ hφ h1, fun h D V _ a ha hI μ b hμ hb s₁ φ hφ h1 => ?_⟩
  rcases le_or_gt b (2 * V.rank) with h2 | h2
  · exact h D V a ha μ b hμ hb s₁ φ hφ h1 h2
  · have := eisPoleLE_zero_of_lt hI hμ hφ h2
    exact ⟨this.1, fun g => poleLE_succ (this.2 g)⟩

/- English proof (translation)
The claim follows from `have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D V a ha let ⟨_, h⟩ := (hc D V h0 a ha hI μ b hμ hb s₁ φ hφ).2 (((b : ℂ) - V.rank) / 2) h.of_poleLE (hp D V h0 a ha hI μ b hμ hb s₁ φ hφ hab)`.
-/
theorem eisRegularAt_one (hc : Published.SiegelEisensteinContinuation) (hp : Published.SiegelEisensteinSimplePole)
    {D : D7} {V : HSp D} (h0 : 0 < V.rank) {a : GL (Fin V.rank) (AE D)} (ha : IsMaj V a)
    {μ : (AE D)ˣ →* Circle} {b : ℕ} (hμ : IsHeckeChar D μ) (hb : ResEta D μ b)
    {s₁ : ℂ} {φ : GA D (dblSp V) → ℂ} (hφ : φ ∈ degPS V a μ s₁) (hab : V.rank < b) :
    EisRegularAt V (flat V a φ s₁) (((b : ℂ) - V.rank) / 2) 1 :=
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D V a ha
  let ⟨_, h⟩ := (hc D V h0 a ha hI μ b hμ hb s₁ φ hφ).2 (((b : ℂ) - V.rank) / 2)
  h.of_poleLE (hp D V h0 a ha hI μ b hμ hb s₁ φ hφ hab)

end GlobalTheory.Eis.SimplePoleModel

end
