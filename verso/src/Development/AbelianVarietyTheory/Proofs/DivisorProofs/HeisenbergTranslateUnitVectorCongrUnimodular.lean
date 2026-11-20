import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerStandardToSkewMemThetaSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitSupportedUnitaryMovingToSelfDualSkewLStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.HeisTranslate

/- English proof (translation)
Establish `hJ0 : (J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0`. Simplify using `using hJ`. Establish `key : ∀ y ∈ (J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹, ∀ w ∈ hatId D J, w * inc D y ∈ OhE D`. Introduce `y hy w hw`. Proceed by induction on `hw using AddSubgroup.closure_induction with`.

Consider the case `mem z hz`. Take `⟨b, hb, s, hs, rfl⟩` from `hz`. Establish `hby : (b : D.host.E) * y ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)`. Rewrite using `[← mul_inv_cancel₀ hJ0]`. Conclude with `FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hb) hy`.

Take `⟨c, hc⟩` from `(FractionalIdeal.mem_one_iff _).1 hby`. Establish `e1 : inc D (b : D.host.E) * s * inc D y = inc D ((c : 𝓞 D.host.E) : D.host.E) * s`. Rewrite using `[show ((c : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E c from rfl, hc, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`.

Conclude with `mul_mem (VacMove.inc_int D c) hs`. Consider the case `zero => simpa using (OhE D).zero_mem`. Consider the case `add x z _ _ hx hz => rw [add_mul]`. Conclude with `add_mem hx hz`. Consider the case `neg x _ hx => rw [neg_mul]`.

Conclude with `neg_mem hx`. Rewrite using `[← inv_inv (J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), FractionalIdeal.inv_eq, FractionalIdeal.mem_div_iff_of_ne_zero (inv_ne_zero hJ0)]`. Introduce `y hy`. Rewrite using `[FractionalIdeal.mem_one_iff]`. Establish `hint : e * y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range`.

Use `HeightOneSpectrum.mem_integers_of_valuation_le_one D.host.E _ fun v => ?_` and prove the remaining obligations. Rewrite using `[← GlobalTheory.Mem.Col2.SplitChar.vl_inc, map_mul]`. Conclude with `GlobalTheory.Mem.Col2.SplitChar.vl_le (key y hy _ he) v`. Conclude with `hint`.
-/
theorem mem_of_inc_mem_hatId {D : D7} {J : Ideal (𝓞 D.host.E)} (hJ : J ≠ ⊥) {e : D.host.E}
    (he : inc D e ∈ hatId D J) : e ∈ (J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
  have hJ0 : (J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    simpa using hJ
  have key : ∀ y ∈ (J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹, ∀ w ∈ hatId D J, w * inc D y ∈ OhE D := by
    intro y hy w hw
    induction hw using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨b, hb, s, hs, rfl⟩ := hz
      have hby : (b : D.host.E) * y ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
        rw [← mul_inv_cancel₀ hJ0]
        exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hb) hy
      obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 hby
      have e1 : inc D (b : D.host.E) * s * inc D y = inc D ((c : 𝓞 D.host.E) : D.host.E) * s := by
        rw [show ((c : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E c from rfl, hc, map_mul]
        ring
      rw [e1]
      exact mul_mem (VacMove.inc_int D c) hs
    | zero => simpa using (OhE D).zero_mem
    | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
    | neg x _ hx => rw [neg_mul]; exact neg_mem hx
  rw [← inv_inv (J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), FractionalIdeal.inv_eq,
    FractionalIdeal.mem_div_iff_of_ne_zero (inv_ne_zero hJ0)]
  intro y hy
  rw [FractionalIdeal.mem_one_iff]
  have hint : e * y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    refine HeightOneSpectrum.mem_integers_of_valuation_le_one D.host.E _ fun v => ?_
    rw [← GlobalTheory.Mem.Col2.SplitChar.vl_inc, map_mul]
    exact GlobalTheory.Mem.Col2.SplitChar.vl_le (key y hy _ he) v
  exact hint

end GlobalTheory.HeisTranslate

namespace GlobalTheory.HeisTranslate

/- English proof (translation)
Use `AddSubgroup.subset_closure ⟨δ, AddSubgroup.subset_closure ⟨1, trivial, by simp⟩, _, ?_, rfl⟩` and prove the remaining obligations. Use `Submodule.subset_span ⟨1, ?_, _, Submodule.subset_span fun x hx i _ => ?_, (one_smul _ _).symm⟩` and prove the remaining obligations. Use `FractionalIdeal.one_mem_inv_coe_ideal fun h => ?_` and prove the remaining obligations. Establish `h2` using `D.host.𝔟_spec.2`. Rewrite `h2` using `[h, Ideal.smul_bot, sup_bot_eq]`.

Conclude with `bot_ne_top h2`. Establish `hx' : ∀ j, x j ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)` using `fun j => by`. Simplify using `only [stdL, Submodule.mem_pi, Set.mem_univ, true_implies] at hx`. Conclude with `hx j`. Use `show ∑ j, z i j * x j ∈ _`.

Use `sum_mem fun j _ => ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `Submodule.mem_one.1 (hx' j)`. Rewrite using `[← hc, mul_comm, ← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ c (hz i j)`.
-/
theorem pt_mem_La_skew {D : D7} (δ : ℂ) (𝔫 : Ideal (𝓞 D.host.E)) {a d : ℕ} (z : Matrix (Fin d) (Fin a) D.host.E)
    (hz : ∀ i j, z i j ∈ (((𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
      ((D.host.conj • 𝔫 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
        FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E)) :
    pt D (tor0 D ⊤ δ) δ z ∈ La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔫 d) := by
  refine AddSubgroup.subset_closure ⟨δ, AddSubgroup.subset_closure ⟨1, trivial, by simp⟩, _, ?_, rfl⟩
  refine Submodule.subset_span ⟨1, ?_, _, Submodule.subset_span fun x hx i _ => ?_, (one_smul _ _).symm⟩
  · refine FractionalIdeal.one_mem_inv_coe_ideal fun h => ?_
    have h2 := D.host.𝔟_spec.2
    rw [h, Ideal.smul_bot, sup_bot_eq] at h2
    exact bot_ne_top h2
  · have hx' : ∀ j, x j ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := fun j => by
      simp only [stdL, Submodule.mem_pi, Set.mem_univ, true_implies] at hx
      exact hx j
    show ∑ j, z i j * x j ∈ _
    refine sum_mem fun j _ => ?_
    obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hx' j)
    rw [← hc, mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ c (hz i j)

end GlobalTheory.HeisTranslate

namespace GlobalTheory.HeisTranslate

/- English proof (translation)
Simplify using `only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]`. Use `congr 1`. Use `Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hf_swap (D : D7) (T : Tor D) {N N' : ℕ} (a b : VC D N N') :
    Hf D T b a = starRingEnd ℂ (Hf D T a b) := by
  simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `[wdPh, ee, Complex.norm_exp]`.
-/
theorem norm_wdPh (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') : ‖wdPh D T x‖ = 1 := by
  simp [wdPh, ee, Complex.norm_exp]

/- English proof (translation)
Establish `h0 : wdPh D T (a + b) ≠ 0` using `Complex.exp_ne_zero _`. Use `⟨wdPh D T a * wdPh D T b / wdPh D T (a + b) * Complex.exp ((Real.pi : ℂ) * (Hf D T b a - Hf D T a b) / 2), ?_, fun F => ?_⟩` and prove the remaining obligations. Establish `hre : ((Real.pi : ℂ) * (Hf D T b a - Hf D T a b) / 2).re = 0`. Rewrite using `[hf_swap D T a b]`. Simplify using `[Complex.div_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]`.

Rewrite using `[norm_mul, norm_div, norm_mul, norm_wdPh, norm_wdPh, norm_wdPh, Complex.norm_exp, hre]`. Simplify using the standard rewrite rules. Use function extensionality and compare the values at `z`. Simplify using `only [Wd, U, Pi.smul_apply, smul_eq_mul, VacMove.hf_add_left, VacMove.hf_add_right, add_assoc]`. Establish `: Complex.exp (-(Real.pi : ℂ) * (Hf D T z b + Hf D T a b) - (Real.pi : ℂ) * Hf D T b b / 2) * Complex.exp (-(Real.pi : ℂ) * Hf D T z a - (Real.pi : ℂ) * Hf D T a a / 2) = Complex.exp ((Real.pi : ℂ) * (Hf D T b a - Hf D T a b) / 2) * Complex.exp (-(Real.pi : ℂ) * (Hf D T z a + Hf …`.

Rewrite using `[← Complex.exp_add, ← Complex.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Clear the denominators using the available nonvanishing facts. Clear denominators, using `at this` for the nonvanishing conditions.

Take the linear combination `(wdPh D T a * wdPh D T b * F (z + (a + b))) * this`.
-/
theorem wd_wd_unimod (D : D7) (T : Tor D) {N N' : ℕ} (a b : VC D N N') :
    ∃ φ : ℂ, ‖φ‖ = 1 ∧ ∀ F, Wd D T a (Wd D T b F) = φ • Wd D T (a + b) F := by
  have h0 : wdPh D T (a + b) ≠ 0 := Complex.exp_ne_zero _
  refine ⟨wdPh D T a * wdPh D T b / wdPh D T (a + b) *
    Complex.exp ((Real.pi : ℂ) * (Hf D T b a - Hf D T a b) / 2), ?_, fun F => ?_⟩
  · have hre : ((Real.pi : ℂ) * (Hf D T b a - Hf D T a b) / 2).re = 0 := by
      rw [hf_swap D T a b]
      simp [Complex.div_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    rw [norm_mul, norm_div, norm_mul, norm_wdPh, norm_wdPh, norm_wdPh, Complex.norm_exp, hre]
    simp
  funext z
  simp only [Wd, U, Pi.smul_apply, smul_eq_mul, VacMove.hf_add_left, VacMove.hf_add_right, add_assoc]
  have : Complex.exp (-(Real.pi : ℂ) * (Hf D T z b + Hf D T a b) - (Real.pi : ℂ) * Hf D T b b / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z a - (Real.pi : ℂ) * Hf D T a a / 2) =
      Complex.exp ((Real.pi : ℂ) * (Hf D T b a - Hf D T a b) / 2) *
      Complex.exp (-(Real.pi : ℂ) * (Hf D T z a + Hf D T z b) -
        (Real.pi : ℂ) * (Hf D T a a + (Hf D T b a + (Hf D T a b + Hf D T b b))) / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  field_simp
  field_simp at this
  linear_combination (wdPh D T a * wdPh D T b * F (z + (a + b))) * this

end GlobalTheory.HeisTranslate

namespace GlobalTheory.HeisTranslate

/- English proof (translation)
Introduce `D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho y y' hyy`. Establish `hm' : D.host.conj • 𝔪 ≠ ⊥` using `GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm`. Establish `hcc : D.host.conj • D.host.conj • 𝔪 = 𝔪`. Establish `h : D.host.conj * D.host.conj = 1` using `AlgEquiv.ext fun x => VacMove.conj_conj D x`. Rewrite using `[smul_smul, h, one_smul]`.

Establish `hcop' : IsCoprime (D.host.conj • 𝔪) (D.host.conj • D.host.conj • 𝔪)`. Rewrite using `[hcc, Ideal.isCoprime_iff_sup_eq, sup_comm]`. Conclude with `hcop`. Take `⟨g', x', -, hg'm, -, -⟩` from `GlobalTheory.T.exists_splitSupported_unitary_moving_to_selfDualSkewLattice D (D.host.conj • 𝔪) hm' hcop' d`. Establish `hsd : SD D (skewLat D (D.host.conj • 𝔪) d)` using `VacMove.sd_of_moves hg'm`.

Establish `hK : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d))` using `Or.inr ⟨_, _, GlobalTheory.FinWeil.RatTransl.sd_std D a, hsd, rfl⟩`. Establish `hF` using `GlobalTheory.SkewTheta.iop_mem_thSp D δ hc e0 hv.1 (D.host.conj • 𝔪) hsd`. Establish `h1` using `(GlobalTheory.InducedType.induced_type D).1`. Establish `hne : ((D.host.conj • D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0`. Rewrite using `[hcc]`.

Simplify using `using hm`. Establish `hx : pt D (tor0 D ⊤ δ) δ (y - y') ∈ La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)`. Use `pt_mem_La_skew δ (D.host.conj • 𝔪) (y - y') fun i j => ?_` and prove the remaining obligations. Establish `hmem` using `mem_of_inc_mem_hatId hm' (hyy i j)`. Rewrite using `[Matrix.sub_apply, FractionalIdeal.mem_coe, FractionalIdeal.mem_div_iff_of_ne_zero hne]`.

Introduce `w hw`. Take `⟨c, -, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).1 hw`. Rewrite using `[mul_comm, ← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ c hmem`. Establish `hfix` using `VacMove.wd_fix h1 hc hK hF hx`.

Take `⟨φ, hφ1, hφ⟩` from `wd_wd_unimod D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ y') (pt D (tor0 D ⊤ δ) δ (y - y'))`. Establish `e` using `hφ (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0)`. Rewrite `e` using `[hfix, ← VacMove.pt_add, add_sub_cancel]`. Establish `hφ0 : φ ≠ 0`. Introduce `h`.

Rewrite `hφ1` using `[h, norm_zero]`. Conclude with `zero_ne_one hφ1`. Use `⟨φ⁻¹, by rw [norm_inv, hφ1, inv_one], ?_⟩` and prove the remaining obligations. Rewrite using `[e, smul_smul, inv_mul_cancel₀ hφ0, one_smul]`.
-/
theorem wd_unitVec_congr : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), ∀ y y' : Matrix (Fin d) (Fin a) D.host.E, (∀ i l, inc D (y i l - y' i l) ∈ hatId D (D.host.conj • 𝔪)) → ∃ c : ℂ, ‖c‖ = 1 ∧ Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ y) (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) = c • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ y') (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) := by
  intro D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho y y' hyy
  have hm' : D.host.conj • 𝔪 ≠ ⊥ := GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm
  have hcc : D.host.conj • D.host.conj • 𝔪 = 𝔪 := by
    have h : D.host.conj * D.host.conj = 1 := AlgEquiv.ext fun x => VacMove.conj_conj D x
    rw [smul_smul, h, one_smul]
  have hcop' : IsCoprime (D.host.conj • 𝔪) (D.host.conj • D.host.conj • 𝔪) := by
    rw [hcc, Ideal.isCoprime_iff_sup_eq, sup_comm]; exact hcop
  obtain ⟨g', x', -, hg'm, -, -⟩ := GlobalTheory.T.exists_splitSupported_unitary_moving_to_selfDualSkewLattice D (D.host.conj • 𝔪) hm' hcop' d
  have hsd : SD D (skewLat D (D.host.conj • 𝔪) d) := VacMove.sd_of_moves hg'm
  have hK : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) :=
    Or.inr ⟨_, _, GlobalTheory.FinWeil.RatTransl.sd_std D a, hsd, rfl⟩
  have hF := GlobalTheory.SkewTheta.iop_mem_thSp D δ hc e0 hv.1 (D.host.conj • 𝔪) hsd
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have hne : ((D.host.conj • D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [hcc]; simpa using hm
  have hx : pt D (tor0 D ⊤ δ) δ (y - y') ∈ La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d) := by
    refine pt_mem_La_skew δ (D.host.conj • 𝔪) (y - y') fun i j => ?_
    have hmem := mem_of_inc_mem_hatId hm' (hyy i j)
    rw [Matrix.sub_apply, FractionalIdeal.mem_coe, FractionalIdeal.mem_div_iff_of_ne_zero hne]
    intro w hw
    obtain ⟨c, -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hw
    rw [mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ c hmem
  have hfix := VacMove.wd_fix h1 hc hK hF hx
  obtain ⟨φ, hφ1, hφ⟩ := wd_wd_unimod D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ y') (pt D (tor0 D ⊤ δ) δ (y - y'))
  have e := hφ (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d)
    (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0)
  rw [hfix, ← VacMove.pt_add, add_sub_cancel] at e
  have hφ0 : φ ≠ 0 := by
    intro h; rw [h, norm_zero] at hφ1; exact zero_ne_one hφ1
  refine ⟨φ⁻¹, by rw [norm_inv, hφ1, inv_one], ?_⟩
  rw [e, smul_smul, inv_mul_cancel₀ hφ0, one_smul]

end GlobalTheory.HeisTranslate
