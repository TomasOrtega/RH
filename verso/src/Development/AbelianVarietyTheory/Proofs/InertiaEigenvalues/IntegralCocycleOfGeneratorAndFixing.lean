import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicTowerLevelGeneratorProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUnitPowSubOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLeOfQBMemLatStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntAddFilClosedInDeRhamPeriodRingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedAndEventuallySubMemLatStatement

noncomputable section

namespace GlobalTheory.ExpImage.IntCoc

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage Filter Topology
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `hα : IsIntegral ℚ_[l] α` using `Algebra.IsIntegral.isIntegral α`. Take `⟨K, hK⟩ : ∃ K : FinExt l, α ∈ K.1` from `⟨⟨IntermediateField.adjoin ℚ_[l] {α}, IntermediateField.adjoin.finiteDimensional hα⟩, IntermediateField.mem_adjoin_simple_self _ α⟩`. Establish `h` using `((P.PD K).Fil 0).smul_mem (⟨α, hK⟩ : ↥K.1) (P.PD K).one_mem`. Rewrite `h` using `[Algebra.smul_def, mul_one, IsScalarTower.algebraMap_apply ↥K.1 (Om l) P.R.BdR]`. Conclude with `(T.fil _ _ _).2 ((T.fil K _ _).1 h)`.
-/
theorem oB_mem {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (α : Om l) :
    oB P α ∈ FilB P 0 := by
  have hα : IsIntegral ℚ_[l] α := Algebra.IsIntegral.isIntegral α
  obtain ⟨K, hK⟩ : ∃ K : FinExt l, α ∈ K.1 :=
    ⟨⟨IntermediateField.adjoin ℚ_[l] {α}, IntermediateField.adjoin.finiteDimensional hα⟩,
      IntermediateField.mem_adjoin_simple_self _ α⟩
  have h := ((P.PD K).Fil 0).smul_mem (⟨α, hK⟩ : ↥K.1) (P.PD K).one_mem
  rw [Algebra.smul_def, mul_one, IsScalarTower.algebraMap_apply ↥K.1 (Om l) P.R.BdR] at h
  exact (T.fil _ _ _).2 ((T.fil K _ _).1 h)

/- English proof (translation)
The claim follows from `AlgEquiv.commutes _ c`.
-/
theorem act_qB (P : LocPrime l) (g : GQ l) (c : ℚ_[l]) : P.actQdR g (qB P c) = qB P c :=
  AlgEquiv.commutes _ c

def tw (LT : LocTheory) (e : ℕ) (σ : GQ l) : ℚ_[l] :=
  (((LT l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l])

def coc (LT : LocTheory) (e : ℕ) (x b : (LT l).R.BdR) (σ : GQ l) : (LT l).R.BdR :=
  qB (LT l) ((logChi LT σ : ℤ_[l]) : ℚ_[l]) * x +
    (qB (LT l) (tw LT e σ) * (LT l).actQdR σ b - b)

variable (LT : LocTheory)

/- English proof (translation)
The claim follows from `(cyc_basic l _ (LT l).χQ_cyc).1 σ`.
-/
theorem norm_chi (σ : GQ l) : ‖((LT l).χQ σ : ℚ_[l])‖ = 1 :=
  (cyc_basic l _ (LT l).χQ_cyc).1 σ

/- English proof (translation)
Conclude with `congrArg Subtype.val (dif_pos ((GlobalTheory.PadicLogUnits.logZl_hom l).2.2.1 _ (norm_chi LT σ)))`.
-/
theorem logChi_coe (σ : GQ l) :
    ((logChi LT σ : ℤ_[l]) : ℚ_[l]) = logZl l ((LT l).χQ σ : ℚ_[l]) := by
  exact congrArg Subtype.val (dif_pos ((GlobalTheory.PadicLogUnits.logZl_hom l).2.2.1 _ (norm_chi LT σ)))

/- English proof (translation)
Rewrite using `[logChi_coe, logChi_coe, logChi_coe, map_mul, Units.val_mul, (GlobalTheory.PadicLogUnits.logZl_hom l).1 _ _ (norm_chi LT σ) (norm_chi LT τ)]`.
-/
theorem logChi_mul (σ τ : GQ l) : ((logChi LT (σ * τ) : ℤ_[l]) : ℚ_[l]) =
    ((logChi LT σ : ℤ_[l]) : ℚ_[l]) + ((logChi LT τ : ℤ_[l]) : ℚ_[l]) := by
  rw [logChi_coe, logChi_coe, logChi_coe, map_mul, Units.val_mul,
    (GlobalTheory.PadicLogUnits.logZl_hom l).1 _ _ (norm_chi LT σ) (norm_chi LT τ)]

/- English proof (translation)
Establish `h` using `(GlobalTheory.PadicLogUnits.logZl_hom l).1 1 1 norm_one norm_one`. Rewrite `h` using `[mul_one]`. Conclude with `left_eq_add.1 h`.
-/
theorem logZl_one : logZl l 1 = 0 := by
  have h := (GlobalTheory.PadicLogUnits.logZl_hom l).1 1 1 norm_one norm_one
  rw [mul_one] at h
  exact left_eq_add.1 h

/- English proof (translation)
Simplify using `only [logChi_coe]`. Conclude with `(GlobalTheory.PadicLogUnits.logZl_hom l).2.1.comp_continuous (cyc_basic l _ (LT l).χQ_cyc).2.1 (norm_chi LT)`.
-/
theorem continuous_logChi : Continuous fun σ : GQ l => ((logChi LT σ : ℤ_[l]) : ℚ_[l]) := by
  simp only [logChi_coe]
  exact (GlobalTheory.PadicLogUnits.logZl_hom l).2.1.comp_continuous (cyc_basic l _ (LT l).χQ_cyc).2.1
    (norm_chi LT)

/- English proof (translation)
Simplify using `[tw]`.
-/
theorem tw_eq (e : ℕ) (σ : GQ l) : tw LT e σ = (((LT l).χQ σ : ℚ_[l]) ^ e)⁻¹ := by
  simp [tw]

/- English proof (translation)
Simplify using `[tw_eq, norm_chi]`.
-/
theorem norm_tw (e : ℕ) (σ : GQ l) : ‖tw LT e σ‖ = 1 := by
  simp [tw_eq, norm_chi]

/- English proof (translation)
Rewrite using `[tw, tw, tw, map_mul, mul_zpow, Units.val_mul]`.
-/
theorem tw_mul (e : ℕ) (σ τ : GQ l) : tw LT e (σ * τ) = tw LT e σ * tw LT e τ := by
  rw [tw, tw, tw, map_mul, mul_zpow, Units.val_mul]

/- English proof (translation)
Establish `: tw (l` using `l) LT e = fun σ => (((LT l).χQ σ : ℚ_[l]) ^ e)⁻¹ := funext (tw_eq LT e)`. Rewrite using `[this]`. Conclude with `((cyc_basic l _ (LT l).χQ_cyc).2.1.pow e).inv₀ fun σ => pow_ne_zero _ (Units.ne_zero _)`.
-/
theorem continuous_tw (e : ℕ) : Continuous (tw (l := l) LT e) := by
  have : tw (l := l) LT e = fun σ => (((LT l).χQ σ : ℚ_[l]) ^ e)⁻¹ := funext (tw_eq LT e)
  rw [this]
  exact ((cyc_basic l _ (LT l).χQ_cyc).2.1.pow e).inv₀ fun σ => pow_ne_zero _ (Units.ne_zero _)

/- English proof (translation)
Establish `h1 : qB (LT l) (tw LT e σ) * qB (LT l) ((LT l).χQ σ : ℚ_[l]) ^ e = 1`. Rewrite using `[← map_pow, ← map_mul, tw_eq, inv_mul_cancel₀ (pow_ne_zero _ (Units.ne_zero _)), map_one]`. Rewrite using `[map_mul, map_pow, act_tD, (LT l).actQdR_Om, h, mul_pow]`. Take the linear combination `(oB (LT l) α * tD (LT l) ^ e) * h1`.
-/
theorem tw_act (e : ℕ) (σ : GQ l) (α : Om l) (h : σ α = α) :
    qB (LT l) (tw LT e σ) * (LT l).actQdR σ (oB (LT l) α * tD (LT l) ^ e) =
      oB (LT l) α * tD (LT l) ^ e := by
  have h1 : qB (LT l) (tw LT e σ) * qB (LT l) ((LT l).χQ σ : ℚ_[l]) ^ e = 1 := by
    rw [← map_pow, ← map_mul, tw_eq, inv_mul_cancel₀ (pow_ne_zero _ (Units.ne_zero _)), map_one]
  rw [map_mul, map_pow, act_tD, (LT l).actQdR_Om, h, mul_pow]
  linear_combination (oB (LT l) α * tD (LT l) ^ e) * h1

/- English proof (translation)
Simplify using `only [coc, logChi_mul, tw_mul, map_add, map_mul, map_sub, act_qB, AlgEquiv.mul_apply]`. Take the linear combination `(-qB (LT l) ((logChi LT τ : ℤ_[l]) : ℚ_[l])) * h`.
-/
theorem coc_mul (e : ℕ) (x b : (LT l).R.BdR) (σ τ : GQ l)
    (h : qB (LT l) (tw LT e σ) * (LT l).actQdR σ x = x) :
    coc LT e x b (σ * τ) =
      coc LT e x b σ + qB (LT l) (tw LT e σ) * (LT l).actQdR σ (coc LT e x b τ) := by
  simp only [coc, logChi_mul, tw_mul, map_add, map_mul, map_sub, act_qB, AlgEquiv.mul_apply]
  linear_combination (-qB (LT l) ((logChi LT τ : ℤ_[l]) : ℚ_[l])) * h

/- English proof (translation)
Establish `h0 : ((l : ℚ_[l]) ^ k) ≠ 0` using `pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)`. Establish `h1 : ‖c / (l : ℚ_[l]) ^ k‖ ≤ 1`. Rewrite using `[norm_div, div_le_one (norm_pos_iff.2 h0), Padic.norm_p_pow]`. Conclude with `hc`. Use `qB_mul_mem_Lat AI T ⟨_, h1⟩ hx` as an intermediate fact.

Rewrite `this` using `[← mul_assoc, ← map_natCast (qB P), ← map_pow, ← map_mul, div_mul_cancel₀ _ h0]`. Then use the resulting hypothesis.
-/
theorem small_mul {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {M n k : ℕ} {c : ℚ_[l]}
    {x : P.R.BdR} (hc : ‖c‖ ≤ (l : ℝ) ^ (-(k : ℤ))) (hx : (l : P.R.BdR) ^ k * x ∈ Lat AI M n) :
    qB P c * x ∈ Lat AI M n := by
  have h0 : ((l : ℚ_[l]) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  have h1 : ‖c / (l : ℚ_[l]) ^ k‖ ≤ 1 := by
    rw [norm_div, div_le_one (norm_pos_iff.2 h0), Padic.norm_p_pow]
    exact hc
  have := qB_mul_mem_Lat AI T ⟨_, h1⟩ hx
  rwa [← mul_assoc, ← map_natCast (qB P), ← map_pow, ← map_mul, div_mul_cancel₀ _ h0] at this

/- English proof (translation)
Establish `hl : (0 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).pos`. Use `hf.norm.continuousAt.eventually_le_const ?_` and prove the remaining obligations. Use `show ‖f 1‖ < _`. Rewrite using `[h1, norm_zero]`. Conclude with `zpow_pos hl _`.
-/
theorem ev_small {f : GQ l → ℚ_[l]} (hf : Continuous f) (h1 : f 1 = 0) (k : ℕ) :
    ∀ᶠ τ in 𝓝 (1 : GQ l), ‖f τ‖ ≤ (l : ℝ) ^ (-(k : ℤ)) := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  refine hf.norm.continuousAt.eventually_le_const ?_
  show ‖f 1‖ < _
  rw [h1, norm_zero]
  exact zpow_pos hl _

/- English proof (translation)
Take `⟨⟨k, hk⟩, -⟩` from `GlobalTheory.T.bounded_and_eventually_sub_mem_Lat_alt l _ AI T x hx M n`. Take `⟨⟨k', hk'⟩, h3⟩` from `GlobalTheory.T.bounded_and_eventually_sub_mem_Lat_alt l _ AI T b hb M n`. Establish `h1` using `ev_small (continuous_logChi (l := l) LT) (by rw [logChi_coe, map_one, Units.val_one, logZl_one]) k`. Establish `h2` using `ev_small (f := fun τ : GQ l => tw LT e τ - 1) ((continuous_tw LT e).sub continuous_const) (by simp [tw]) k'`. Use `filter_upwards [h1, h2, h3] with τ a1 a2 a3`.

Use `add_mem (small_mul T a1 hk) (add_mem (small_mul T a2 hk') (qB_mul_mem_Lat AI T ⟨_, (norm_tw LT e τ).le⟩ a3))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [coc, map_sub, map_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coc_small {AI : LocAinf l (LT l)} (T : LocTied l (LT l) AI) (e M n : ℕ)
    {x b : (LT l).R.BdR} (hx : x ∈ FilB (LT l) 0) (hb : b ∈ FilB (LT l) 0) :
    ∀ᶠ τ in 𝓝 (1 : GQ l), coc LT e x b τ ∈ Lat AI M n := by
  obtain ⟨⟨k, hk⟩, -⟩ := GlobalTheory.T.bounded_and_eventually_sub_mem_Lat_alt l _ AI T x hx M n
  obtain ⟨⟨k', hk'⟩, h3⟩ := GlobalTheory.T.bounded_and_eventually_sub_mem_Lat_alt l _ AI T b hb M n
  have h1 := ev_small (continuous_logChi (l := l) LT)
    (by rw [logChi_coe, map_one, Units.val_one, logZl_one]) k
  have h2 := ev_small (f := fun τ : GQ l => tw LT e τ - 1) ((continuous_tw LT e).sub continuous_const)
    (by simp [tw]) k'
  filter_upwards [h1, h2, h3] with τ a1 a2 a3
  have := add_mem (small_mul T a1 hk) (add_mem (small_mul T a2 hk')
    (qB_mul_mem_Lat AI T ⟨_, (norm_tw LT e τ).le⟩ a3))
  convert this using 1
  simp only [coc, map_sub, map_one]
  ring

/- English proof (translation)
Establish `ht : Tendsto (fun τ : GQ l => σ⁻¹ * τ) (𝓝 σ) (𝓝 1)`. Use `(continuous_mul_left σ⁻¹).tendsto σ` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel]`. Then use the resulting hypothesis. Use `filter_upwards [ht.eventually (coc_small LT T e M n hx hb)] with τ hτ`. Establish `h1` using `coc_mul LT e x b σ (σ⁻¹ * τ) h`.

Rewrite `h1` using `[mul_inv_cancel_left]`. Rewrite using `[h1, add_sub_cancel_left]`. Conclude with `qB_mul_mem_Lat AI T ⟨_, (norm_tw LT e σ).le⟩ (act_mem_Lat AI σ hτ)`.
-/
theorem coc_near {AI : LocAinf l (LT l)} (T : LocTied l (LT l) AI) (e M n : ℕ)
    {x b : (LT l).R.BdR} (hx : x ∈ FilB (LT l) 0) (hb : b ∈ FilB (LT l) 0) (σ : GQ l)
    (h : qB (LT l) (tw LT e σ) * (LT l).actQdR σ x = x) :
    ∀ᶠ τ in 𝓝 σ, coc LT e x b τ - coc LT e x b σ ∈ Lat AI M n := by
  have ht : Tendsto (fun τ : GQ l => σ⁻¹ * τ) (𝓝 σ) (𝓝 1) := by
    have := (continuous_mul_left σ⁻¹).tendsto σ
    rwa [inv_mul_cancel] at this
  filter_upwards [ht.eventually (coc_small LT T e M n hx hb)] with τ hτ
  have h1 := coc_mul LT e x b σ (σ⁻¹ * τ) h
  rw [mul_inv_cancel_left] at h1
  rw [h1, add_sub_cancel_left]
  exact qB_mul_mem_Lat AI T ⟨_, (norm_tw LT e σ).le⟩ (act_mem_Lat AI σ hτ)

/- English proof (translation)
Use `add_mem hy (qB_mul_mem (tw LT e σ) (act_mem σ hz))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[coc_mul LT e x b σ τ h, map_add, map_mul, map_sub, act_qB]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fil_mul (e : ℕ) {M : ℤ} {x b : (LT l).R.BdR} {σ τ : GQ l}
    (h : qB (LT l) (tw LT e σ) * (LT l).actQdR σ x = x) {y z : ℚ_[l]}
    (hy : qB (LT l) y - coc LT e x b σ ∈ FilB (LT l) M)
    (hz : qB (LT l) z - coc LT e x b τ ∈ FilB (LT l) M) :
    qB (LT l) (y + tw LT e σ * z) - coc LT e x b (σ * τ) ∈ FilB (LT l) M := by
  have := add_mem hy (qB_mul_mem (tw LT e σ) (act_mem σ hz))
  convert this using 1
  rw [coc_mul LT e x b σ τ h, map_add, map_mul, map_sub, act_qB]
  ring

/- English proof (translation)
Take `⟨y, hy⟩` from `hy`. Take `⟨z, hz⟩` from `hz`. Set `u : ℤ_[l]` to `⟨tw LT e σ, (norm_tw LT e σ).le⟩`. Use `⟨y + u * z, ?_⟩` and prove the remaining obligations. Rewrite using `[PadicInt.coe_add, PadicInt.coe_mul]`.

Conclude with `fil_mul LT e h hy hz`.
-/
theorem nearZ_mul (e M : ℕ) {x b : (LT l).R.BdR} {σ τ : GQ l}
    (h : qB (LT l) (tw LT e σ) * (LT l).actQdR σ x = x)
    (hy : NearZ (LT l) M (coc LT e x b σ)) (hz : NearZ (LT l) M (coc LT e x b τ)) :
    NearZ (LT l) M (coc LT e x b (σ * τ)) := by
  obtain ⟨y, hy⟩ := hy
  obtain ⟨z, hz⟩ := hz
  let u : ℤ_[l] := ⟨tw LT e σ, (norm_tw LT e σ).le⟩
  refine ⟨y + u * z, ?_⟩
  rw [PadicInt.coe_add, PadicInt.coe_mul]
  exact fil_mul LT e h hy hz

/- English proof (translation)
Establish `hl : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hl)`. Conclude with `⟨n, by rwa [zpow_neg, zpow_natCast, ← inv_pow]⟩`.
-/
theorem exists_pow_lt {ε : ℝ} (hε : 0 < ε) : ∃ n : ℕ, (l : ℝ) ^ (-(n : ℤ)) < ε := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hl)
  exact ⟨n, by rwa [zpow_neg, zpow_natCast, ← inv_pow]⟩

/- English proof (translation)
Assume the negation of the conclusion as `h`. Take `⟨n, hn⟩` from `exists_pow_lt (l := l) (norm_pos_iff.2 h)`. Conclude with `absurd (GlobalTheory.T.norm_le_of_qB_mem_Lat_alt l P AI T M n hM c (FilB_le_Lat AI hc)) (not_le.2 hn)`.
-/
theorem eq_zero_of_fil {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {M : ℕ}
    (hM : 1 ≤ M) {c : ℚ_[l]} (hc : qB P c ∈ FilB P (M : ℤ)) : c = 0 := by
  by_contra h
  obtain ⟨n, hn⟩ := exists_pow_lt (l := l) (norm_pos_iff.2 h)
  exact absurd (GlobalTheory.T.norm_le_of_qB_mem_Lat_alt l P AI T M n hM c (FilB_le_Lat AI hc)) (not_le.2 hn)

end GlobalTheory.ExpImage.IntCoc

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage Filter Topology IntCoc

/- English proof (translation)
Introduce `LT l _ AI T K s hs e g hg α hα b hb hH hgz`. Use `set x := oB (LT l) α * tD (LT l) ^ e with hxdef`. Establish `hM : 1 ≤ e + 1` using `Nat.le_add_left 1 e`. Establish `hx : x ∈ FilB (LT l) 0` using `FilB_zero_mul (oB_mem T α) (FilB_anti (by positivity) (FilB_pow tD_mem e))`. Establish `hfix : ∀ σ ∈ Gj K s, qB (LT l) (tw LT e σ) * (LT l).actQdR σ x = x` using `fun σ hσ => tw_act LT e σ α (hσ ⟨α, hα⟩)`.

Establish `hχ : IsCyc (LT l).χQ` using `(LT l).χQ_cyc`. Establish `hact : IsActC AI.actC` using `⟨AI.actC_ext, AI.actC_norm⟩`. Establish `hH1 : ∀ h ∈ Hinf K, (LT l).χQ h = 1` using `fun h hh => ((cyc_basic l _ hχ).2.2 K h (Hinf_le_fix hh)).2.1 hh`. Establish `hHG : ∀ h ∈ Hinf K, h ∈ Gj K s` using `fun h hh => (((cyc_basic l _ hχ).2.2 K h (Hinf_le_fix hh)).1 s).2 (by`. Rewrite using `[hH1 h hh, Units.val_one, sub_self, norm_zero]`.

Use the proof step `positivity)`. Establish `hHz : ∀ h ∈ Hinf K, NearZ (LT l) (e + 1) (coc LT e x b h)` using `fun h hh => by`. Use `hH h hh` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `[coc, tw, logChi_coe, hH1 h hh, logZl_one]`.

Establish `hpow : ∀ a : ℕ, NearZ (LT l) (e + 1) (coc LT e x b (g ^ a))` using `fun a => by`. Proceed by induction on `a with`. Consider the case `zero => rw [pow_zero]`. Conclude with `hHz 1 (one_mem _)`. Consider the case `succ a ih => rw [pow_succ']`.

Conclude with `nearZ_mul LT e _ (hfix g hg.1) hgz ih`. Establish `hall : ∀ σ ∈ Gj K s, NearZ (LT l) (e + 1) (coc LT e x b σ)` using `fun σ hσ => by`. Use `GlobalTheory.T.padicInt_add_fil_closed_in_deRhamPeriodRing l _ AI T _ hM _ fun n => ?_` and prove the remaining obligations. Establish `hcl` using `((gen_dense l _ _ hact hχ K s hs).2 g hg).2.2 hσ`. Take `⟨τ, ⟨h, hh, a, rfl⟩, hτ⟩` from `((mem_closure_iff_frequently.1 hcl).and_eventually (coc_near LT T e (e + 1) n hx hb σ (hfix σ hσ))).exists`.

Take `⟨z, hz⟩` from `nearZ_mul LT e _ (hfix h (hHG h hh)) (hHz h hh) (hpow a)`. Use `⟨z, ?_⟩` and prove the remaining obligations. Use `add_mem (FilB_le_Lat AI (n := n) hz) hτ` as an intermediate fact. Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis. Use `choose! z hz using hall`.

Use `⟨fun σ => (z σ : ℚ_[l]), fun σ _ => (z σ).2, ⟨?_, fun _ _ => Set.mem_univ _, ?_⟩, b, hb, ?_⟩` and prove the remaining obligations. Introduce `σ hσ`. Rewrite using `[ContinuousWithinAt, Metric.tendsto_nhds]`. Introduce `ε hε`. Take `⟨n, hn⟩` from `exists_pow_lt (l := l) hε`.

Use `filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (coc_near LT T e (e + 1) n hx hb σ (hfix σ hσ))] with τ hτ h1`. Rewrite using `[dist_eq_norm]`. Use `lt_of_le_of_lt (GlobalTheory.T.norm_le_of_qB_mem_Lat_alt l _ AI T _ n hM _ ?_) hn` and prove the remaining obligations. Use `sub_mem (add_mem (FilB_le_Lat AI (n := n) (hz τ hτ)) h1) (FilB_le_Lat AI (hz σ hσ))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[map_sub]`. Expand and normalize the polynomial expressions, which then agree. Introduce `σ hσ τ hτ`. Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_fil T hM ?_` and prove the remaining obligations.

Use `sub_mem (hz _ (mul_mem hσ hτ)) (fil_mul LT e (hfix σ hσ) (hz σ hσ) (hz τ hτ))` as an intermediate fact. Rewrite `this` using `[sub_sub_sub_cancel_right, ← map_sub]`. Then use the resulting hypothesis. Introduce `σ hσ`. Use `hz σ hσ` as an intermediate fact. Rewrite `this` using `[coc, ← sub_sub, Nat.cast_add_one]`.

Conclude with `this`.
-/
theorem integral_cocycle_of_gen : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ) (g : GQ l), IsGen (LT l).χQ K s g → ∀ α ∈ Ks K s, ∀ b ∈ FilB (LT l) 0, (∀ h ∈ Hinf K, NearZ (LT l) (e + 1) ((LT l).actQdR h b - b)) → NearZ (LT l) (e + 1) (qB (LT l) ((logChi LT g : ℤ_[l]) : ℚ_[l]) * (oB (LT l) α * tD (LT l) ^ e) + (qB (LT l) (((LT l).χQ g ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * (LT l).actQdR g b - b)) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (α) := by
  intro LT l _ AI T K s hs e g hg α hα b hb hH hgz
  set x := oB (LT l) α * tD (LT l) ^ e with hxdef
  have hM : 1 ≤ e + 1 := Nat.le_add_left 1 e
  have hx : x ∈ FilB (LT l) 0 :=
    FilB_zero_mul (oB_mem T α) (FilB_anti (by positivity) (FilB_pow tD_mem e))
  have hfix : ∀ σ ∈ Gj K s, qB (LT l) (tw LT e σ) * (LT l).actQdR σ x = x :=
    fun σ hσ => tw_act LT e σ α (hσ ⟨α, hα⟩)
  have hχ : IsCyc (LT l).χQ := (LT l).χQ_cyc
  have hact : IsActC AI.actC := ⟨AI.actC_ext, AI.actC_norm⟩
  have hH1 : ∀ h ∈ Hinf K, (LT l).χQ h = 1 := fun h hh =>
    ((cyc_basic l _ hχ).2.2 K h (Hinf_le_fix hh)).2.1 hh
  have hHG : ∀ h ∈ Hinf K, h ∈ Gj K s := fun h hh =>
    (((cyc_basic l _ hχ).2.2 K h (Hinf_le_fix hh)).1 s).2 (by
      rw [hH1 h hh, Units.val_one, sub_self, norm_zero]; positivity)
  have hHz : ∀ h ∈ Hinf K, NearZ (LT l) (e + 1) (coc LT e x b h) := fun h hh => by
    have := hH h hh
    convert this using 1
    simp [coc, tw, logChi_coe, hH1 h hh, logZl_one]
  have hpow : ∀ a : ℕ, NearZ (LT l) (e + 1) (coc LT e x b (g ^ a)) := fun a => by
    induction a with
    | zero => rw [pow_zero]; exact hHz 1 (one_mem _)
    | succ a ih => rw [pow_succ']; exact nearZ_mul LT e _ (hfix g hg.1) hgz ih
  have hall : ∀ σ ∈ Gj K s, NearZ (LT l) (e + 1) (coc LT e x b σ) := fun σ hσ => by
    refine GlobalTheory.T.padicInt_add_fil_closed_in_deRhamPeriodRing l _ AI T _ hM _ fun n => ?_
    have hcl := ((gen_dense l _ _ hact hχ K s hs).2 g hg).2.2 hσ
    obtain ⟨τ, ⟨h, hh, a, rfl⟩, hτ⟩ := ((mem_closure_iff_frequently.1 hcl).and_eventually
      (coc_near LT T e (e + 1) n hx hb σ (hfix σ hσ))).exists
    obtain ⟨z, hz⟩ := nearZ_mul LT e _ (hfix h (hHG h hh)) (hHz h hh) (hpow a)
    refine ⟨z, ?_⟩
    have := add_mem (FilB_le_Lat AI (n := n) hz) hτ
    rwa [sub_add_sub_cancel] at this
  choose! z hz using hall
  refine ⟨fun σ => (z σ : ℚ_[l]), fun σ _ => (z σ).2, ⟨?_, fun _ _ => Set.mem_univ _, ?_⟩, b, hb, ?_⟩
  · intro σ hσ
    rw [ContinuousWithinAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt (l := l) hε
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds
      (coc_near LT T e (e + 1) n hx hb σ (hfix σ hσ))] with τ hτ h1
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (GlobalTheory.T.norm_le_of_qB_mem_Lat_alt l _ AI T _ n hM _ ?_) hn
    have := sub_mem (add_mem (FilB_le_Lat AI (n := n) (hz τ hτ)) h1) (FilB_le_Lat AI (hz σ hσ))
    convert this using 1
    rw [map_sub]
    ring
  · intro σ hσ τ hτ
    rw [← sub_eq_zero]
    refine eq_zero_of_fil T hM ?_
    have := sub_mem (hz _ (mul_mem hσ hτ)) (fil_mul LT e (hfix σ hσ) (hz σ hσ) (hz τ hτ))
    rwa [sub_sub_sub_cancel_right, ← map_sub] at this
  · intro σ hσ
    have := hz σ hσ
    rw [coc, ← sub_sub, Nat.cast_add_one] at this
    exact this

end GlobalTheory.ExpImage
