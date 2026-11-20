import Mathlib
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB

noncomputable section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.MomentPinned

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Establish `hq : (0 : ℝ) < (p : ℝ) ^ (-(n : ℤ))` using `zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _`. Use `filter_upwards [Metric.ball_mem_nhds x hq] with y hy`. Rewrite using `[← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]`.

Rewrite `hy` using `[Metric.mem_ball, dist_eq_norm]`. Conclude with `hy.le`.
-/
theorem isLocallyConstant_toZModPow {p : ℕ} [Fact p.Prime] (n : ℕ) :
    IsLocallyConstant (PadicInt.toZModPow (p := p) n) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hq : (0 : ℝ) < (p : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  filter_upwards [Metric.ball_mem_nhds x hq] with y hy
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
  rw [Metric.mem_ball, dist_eq_norm] at hy
  exact hy.le

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Establish `: ∀ i, ∀ᶠ y in nhds x, PadicInt.toZModPow n (y i) = PadicInt.toZModPow n (x i)` using `fun i => ((isLocallyConstant_toZModPow n).comp_continuous (continuous_apply i)).eventually_eq x`. Use `filter_upwards [Filter.eventually_all.2 this] with y hy using funext hy`.
-/
theorem isLocallyConstant_red {p : ℕ} [Fact p.Prime] (r n : ℕ) :
    IsLocallyConstant (fun a : Fin r → ℤ_[p] => fun i => PadicInt.toZModPow n (a i)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have : ∀ i, ∀ᶠ y in nhds x, PadicInt.toZModPow n (y i) = PadicInt.toZModPow n (x i) := fun i =>
    ((isLocallyConstant_toZModPow n).comp_continuous (continuous_apply i)).eventually_eq x
  filter_upwards [Filter.eventually_all.2 this] with y hy using funext hy

/- English proof (translation)
Unfold `JMB.zc`. Conclude with `(continuous_algebraMap ℚ_[p] ℂ_[p]).comp continuous_subtype_val`.
-/
theorem continuous_zc {p : ℕ} [Fact p.Prime] : Continuous (JMB.zc : ℤ_[p] → ℂ_[p]) := by
  unfold JMB.zc
  exact (continuous_algebraMap ℚ_[p] ℂ_[p]).comp continuous_subtype_val

/- English proof (translation)
Unfold `JMB.pairD`. Use `continuous_zc (p := p)` as an intermediate fact. Use `fun_prop`.
-/
theorem continuous_pairD {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Ω : ℂ_[p]) {g : ℕ} (d : ℕ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) {r : ℕ} (b : Fin r → Fin g → ℂ) (y : Fin g → ℂ) :
    Continuous (JMB.pairD lam Ω d Hm b y) := by
  unfold JMB.pairD
  have := continuous_zc (p := p)
  fun_prop

/- English proof (translation)
The claim follows from `((isLocallyConstant_red (p := p) r n).comp (fun s : Fin r → ZMod (p ^ n) => JMB.lamA lam (JMB.kap Hm (∑ i, (((s i).val : ℕ) : ℂ) • b i) Y))).continuous`.
-/
theorem continuous_charPart {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {g : ℕ}
    (Hm : Matrix (Fin g) (Fin g) ℂ) {r : ℕ} (n : ℕ) (b : Fin r → Fin g → ℂ) (Y : Fin g → ℂ) :
    Continuous fun a : Fin r → ℤ_[p] => JMB.lamA lam (JMB.kap Hm (JMB.vecA n b a) Y) :=
  ((isLocallyConstant_red (p := p) r n).comp (fun s : Fin r → ZMod (p ^ n) =>
    JMB.lamA lam (JMB.kap Hm (∑ i, (((s i).val : ℕ) : ℂ) • b i) Y))).continuous

/- English proof (translation)
Introduce `p _ lam Ω g S r n k bS Y ys f h a`. Establish `hR : Continuous fun a : Fin r → ℤ_[p] => JMB.lamA lam (JMB.kap S.Hm (JMB.vecA n bS a) Y) * ∏ j, JMB.pairD lam Ω S.d S.Hm bS (ys j) a` using `(continuous_charPart lam S.Hm n bS Y).mul (continuous_finsetProd Finset.univ fun j _ => continuous_pairD lam Ω S.d S.Hm bS (ys j))`. Establish `hd : DenseRange (fun a : Fin r → ℕ => fun i => (a i : ℤ_[p]))` using `DenseRange.piMap fun _ : Fin r => PadicInt.denseRange_natCast (p := p)`. Conclude with `congr_fun (hd.equalizer f.continuous hR (funext h)) a`.
-/
theorem eq_of_natCast : ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Ω : ℂ_[p]) (g : ℕ) (S : JMB.Setup g) (r n k : ℕ) (bS : Fin r → Fin g → ℂ) (Y : Fin g → ℂ) (ys : Fin k → Fin g → ℂ) (f : C(Fin r → ℤ_[p], ℂ_[p])), (∀ a : Fin r → ℕ, f (fun i => (a i : ℤ_[p])) = JMB.lamA lam (JMB.kap S.Hm (JMB.vecA n bS (fun i => (a i : ℤ_[p]))) Y) * ∏ j, JMB.pairD lam Ω S.d S.Hm bS (ys j) (fun i => (a i : ℤ_[p]))) → ∀ a, f a = JMB.lamA lam (JMB.kap S.Hm (JMB.vecA n bS a) Y) * ∏ j, JMB.pairD lam Ω S.d S.Hm bS (ys j) a := by
  intro p _ lam Ω g S r n k bS Y ys f h a
  have hR : Continuous fun a : Fin r → ℤ_[p] =>
      JMB.lamA lam (JMB.kap S.Hm (JMB.vecA n bS a) Y) * ∏ j, JMB.pairD lam Ω S.d S.Hm bS (ys j) a :=
    (continuous_charPart lam S.Hm n bS Y).mul
      (continuous_finsetProd Finset.univ fun j _ => continuous_pairD lam Ω S.d S.Hm bS (ys j))
  have hd : DenseRange (fun a : Fin r → ℕ => fun i => (a i : ℤ_[p])) :=
    DenseRange.piMap fun _ : Fin r => PadicInt.denseRange_natCast (p := p)
  exact congr_fun (hd.equalizer f.continuous hR (funext h)) a

end GlobalTheory.MomentPinned
