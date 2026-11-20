import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleZTwistSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleZFamilySt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleTwistLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace VeryAmpleZTwist

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem chart_smul_eq {I : Chart x} (c : chartRing S x I) (z : E) : c • z = (c : Ω) • z := rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `z ∈ Submodule.span _ _ at hz`. Use `Submodule.span_induction (p := fun z _ => q • z ∈ ((G.twist P).twist Q).sub I) ?_ ?_ ?_ ?_ hz` and prove the remaining obligations. Introduce and unpack `_ ⟨q', hq', y, hy, rfl⟩`. Use `Submodule.subset_span ⟨q', hq', q • y, Submodule.subset_span ⟨q, hq, y, hy, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul, smul_smul, mul_comm]`.

Rewrite using `[smul_zero]`. Conclude with `Submodule.zero_mem _`. Introduce `b c _ _ hb hc`. Rewrite using `[smul_add]`. Conclude with `Submodule.add_mem _ hb hc`.

Introduce `c z _ hz`. Rewrite using `[chart_smul_eq, smul_smul, mul_comm, ← smul_smul, ← chart_smul_eq]`. Conclude with `Submodule.smul_mem _ c hz`.
-/
theorem smul_mem_twist_twist (G : SubSystem S x E) (P Q : SubSystem S x Ω) (I : Chart x) {q : Ω}
    (hq : q ∈ P.sub I) {z : E} (hz : z ∈ (G.twist Q).sub I) : q • z ∈ ((G.twist P).twist Q).sub I := by
  change z ∈ Submodule.span _ _ at hz
  refine Submodule.span_induction (p := fun z _ => q • z ∈ ((G.twist P).twist Q).sub I) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨q', hq', y, hy, rfl⟩
    refine Submodule.subset_span ⟨q', hq', q • y, Submodule.subset_span ⟨q, hq, y, hy, rfl⟩, ?_⟩
    rw [smul_smul, smul_smul, mul_comm]
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro b c _ _ hb hc; rw [smul_add]; exact Submodule.add_mem _ hb hc
  · intro c z _ hz
    rw [chart_smul_eq, smul_smul, mul_comm, ← smul_smul, ← chart_smul_eq]
    exact Submodule.smul_mem _ c hz

/- English proof (translation)
Express the relevant statement in the definitionally equal form `z ∈ Submodule.span _ _ at hz`. Use `Submodule.span_induction (p := fun z _ => w • z ∈ (G.twist (H.pow (d + c))).sub I) ?_ ?_ ?_ ?_ hz` and prove the remaining obligations. Introduce and unpack `_ ⟨q, hq, y, hy, rfl⟩`. Use `Submodule.subset_span ⟨q * w, AmpleTwistLocal.mul_mem_pow H I hq c hw, y, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul, mul_comm]`.

Rewrite using `[smul_zero]`. Conclude with `Submodule.zero_mem _`. Introduce `b e _ _ hb he`. Rewrite using `[smul_add]`. Conclude with `Submodule.add_mem _ hb he`.

Introduce `c' z _ hz`. Rewrite using `[chart_smul_eq, smul_smul, mul_comm, ← smul_smul, ← chart_smul_eq]`. Conclude with `Submodule.smul_mem _ c' hz`.
-/
theorem smul_mem_twist_pow (G : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x) {c d : ℕ} {w : Ω}
    (hw : w ∈ (H.pow c).sub I) {z : E} (hz : z ∈ (G.twist (H.pow d)).sub I) :
    w • z ∈ (G.twist (H.pow (d + c))).sub I := by
  change z ∈ Submodule.span _ _ at hz
  refine Submodule.span_induction (p := fun z _ => w • z ∈ (G.twist (H.pow (d + c))).sub I) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨q, hq, y, hy, rfl⟩
    refine Submodule.subset_span ⟨q * w, AmpleTwistLocal.mul_mem_pow H I hq c hw, y, hy, ?_⟩
    rw [smul_smul, mul_comm]
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro b e _ _ hb he; rw [smul_add]; exact Submodule.add_mem _ hb he
  · intro c' z _ hz
    rw [chart_smul_eq, smul_smul, mul_comm, ← smul_smul, ← chart_smul_eq]
    exact Submodule.smul_mem _ c' hz

/- English proof (translation)
Express the relevant statement in the definitionally equal form `z ∈ Submodule.span _ _ at hz`. Use `Submodule.span_induction (p := fun z _ => z ∈ (G.twist (H.pow (a + b))).sub I) ?_ ?_ ?_ ?_ hz` and prove the remaining obligations. Introduce and unpack `_ ⟨q, hq, y, hy, rfl⟩`. Conclude with `smul_mem_twist_pow G H I hq hy`. Conclude with `Submodule.zero_mem _`.

Introduce `b e _ _ hb he`. Conclude with `Submodule.add_mem _ hb he`. Introduce `c z _ hz`. Conclude with `Submodule.smul_mem _ c hz`.
-/
theorem mem_twist_pow_add (G : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x) {a b : ℕ} {z : E}
    (hz : z ∈ ((G.twist (H.pow a)).twist (H.pow b)).sub I) : z ∈ (G.twist (H.pow (a + b))).sub I := by
  change z ∈ Submodule.span _ _ at hz
  refine Submodule.span_induction (p := fun z _ => z ∈ (G.twist (H.pow (a + b))).sub I) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨q, hq, y, hy, rfl⟩
    exact smul_mem_twist_pow G H I hq hy
  · exact Submodule.zero_mem _
  · intro b e _ _ hb he; exact Submodule.add_mem _ hb he
  · intro c z _ hz; exact Submodule.smul_mem _ c hz

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => exact one_mem_twistMod_zero I`. Consider the case `insert l T hl ih`. Rewrite using `[Finset.prod_insert hl, Finset.card_insert_of_notMem hl]`. Conclude with `Submodule.subset_span ⟨h l, hh l, _, ih, rfl⟩`.
-/
theorem prod_mem_pow (H : SubSystem S x Ω) (I : Chart x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hh : ∀ l, h l ∈ H.sub I) (T : Finset (Fin (r + 1))) : ∏ l ∈ T, h l ∈ (H.pow T.card).sub I := by
  classical
  induction T using Finset.induction_on with
  | empty => exact one_mem_twistMod_zero I
  | insert l T hl ih =>
    rw [Finset.prod_insert hl, Finset.card_insert_of_notMem hl]
    exact Submodule.subset_span ⟨h l, hh l, _, ih, rfl⟩

/- English proof (translation)
Introduce `S _ Ω _ _ N x E _ _ _ _ F H r h hH a J`. Take `⟨F', hF'⟩` from `hFam S Ω N x E F H r h hH`. Take `⟨j, hj⟩` from `J.2.1`. Establish `hj0 : h j ≠ 0` using `(mem_support h).mp (J.2.2 hj)`. Establish `hmem : ∀ l I, h l ∈ H.sub I` using `fun l I => (Submodule.mem_iInf _).mp (hH.mem_secs l) I`.

Establish `hpow : ∀ I, h j ^ a ∈ (H.pow a).sub I` using `fun I => by`. Establish `h1 : h j ∈ (H.pow 1).sub I` using `by rw [SubSystem.pow_sub, pow_one]; exact hmem j I`. Simplify using `using AmpleTwistLocal.pow_mem_pow H.toSubSystem I h1 a`. Establish `fwd : ∀ y ∈ secsOnZ F.toSubSystem H.toSubSystem h J, h j ^ a • y ∈ secsOnZ (F.twist (H.pow a)) H.toSubSystem h J`. Introduce `y hy`.

Use `(Submodule.mem_iInf _).mpr fun I => ?_` and prove the remaining obligations. Establish `hyI : y ∈ secsOnZChart F.toSubSystem H.toSubSystem h I J` using `(Submodule.mem_iInf _).mp hy I`. Use `Submodule.span_induction (p := fun y _ => h j ^ a • y ∈ secsOnZChart (F.twist (H.pow a)) H.toSubSystem h I J) ?_ ?_ ?_ ?_ hyI` and prove the remaining obligations. Introduce and unpack `y ⟨n, hn⟩`. Use `Submodule.subset_span ⟨n, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_smul, mul_comm (xProd J ^ n), ← smul_smul]`. Conclude with `smul_mem_twist_twist _ _ _ I (hpow I) hn`. Rewrite using `[smul_zero]`. Conclude with `Submodule.zero_mem _`. Introduce `b e _ _ hb he`.

Rewrite using `[smul_add]`. Conclude with `Submodule.add_mem _ hb he`. Introduce `s e _ he`. Rewrite using `[smul_comm]`. Conclude with `Submodule.smul_mem _ s he`.

Establish `bwd : ∀ e ∈ secsOnZ (F.twist (H.pow a)) H.toSubSystem h J, (h j ^ a)⁻¹ • e ∈ secsOnZ F.toSubSystem H.toSubSystem h J` using `by classical`. Introduce `e he`. Use `(Submodule.mem_iInf _).mpr fun I => ?_` and prove the remaining obligations. Establish `heI : e ∈ secsOnZChart (F.twist (H.pow a)) H.toSubSystem h I J` using `(Submodule.mem_iInf _).mp he I`. Use `set u := ∏ l ∈ J.1.erase j, h l with hu`.

Establish `hxu : xProd J = h j * u` using `(Finset.mul_prod_erase J.1 h hj).symm`. Establish `hk : J.1.card = (J.1.erase j).card + 1`. Rewrite using `[Finset.card_erase_of_mem hj]`. Use `Finset.card_pos.mpr ⟨j, hj⟩` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hua : u ^ a ∈ (H.pow ((J.1.erase j).card * a)).sub I` using `AmpleTwistLocal.pow_mem_pow H.toSubSystem I (prod_mem_pow H.toSubSystem I (fun l => hmem l I) _) a`. Use `Submodule.span_induction (p := fun e _ => (h j ^ a)⁻¹ • e ∈ secsOnZChart F.toSubSystem H.toSubSystem h I J) ?_ ?_ ?_ ?_ heI` and prove the remaining obligations. Introduce and unpack `e ⟨n, hn⟩`. Use `Submodule.subset_span ⟨n + a, ?_⟩` and prove the remaining obligations. Establish `heq : xProd J ^ (n + a) • (h j ^ a)⁻¹ • e = u ^ a • (xProd J ^ n • e)`.

Rewrite using `[smul_smul, smul_smul, hxu]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hdeg : a + J.1.card * n + (J.1.erase j).card * a = J.1.card * (n + a)`.

Rewrite using `[hk]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq, ← hdeg]`. Conclude with `smul_mem_twist_pow _ _ I hua (mem_twist_pow_add _ _ I hn)`. Rewrite using `[smul_zero]`.

Conclude with `Submodule.zero_mem _`. Introduce `b e _ _ hb he`. Rewrite using `[smul_add]`. Conclude with `Submodule.add_mem _ hb he`. Introduce `s e _ he`.

Rewrite using `[smul_comm]`. Conclude with `Submodule.smul_mem _ s he`. Establish `hq : h j ^ a ∈ twistMod S h (a : ℤ) J`. Rewrite using `[twistMod_eq_span (a : ℤ) J hj, zpow_natCast]`. Conclude with `Submodule.mem_span_singleton_self _`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce `z hz`. Rewrite `hz` using `[Submodule.restrictScalars_mem]`. It suffices to establish `H1 : ∀ c : chartRing S h J, c • z ∈ secsOnZ (F.twist (H.pow a)) H.toSubSystem h J by`. Simplify using `using H1 1`.

Use `Submodule.span_induction (p := fun z _ => ∀ c : chartRing S h J, c • z ∈ secsOnZ (F.twist (H.pow a)) H.toSubSystem h J) ?_ ?_ ?_ ?_ hz` and prove the remaining obligations. Introduce and unpack `_ ⟨q, hq, y, hy, rfl⟩ c`. Rewrite `hq` using `[twistMod_eq_span (a : ℤ) J hj, Submodule.mem_span_singleton]`. Take `⟨d, rfl⟩` from `hq`. Establish `hy' : y ∈ F'.sub J`.

Establish `: y ∈ (F'.sub J).restrictScalars S` using `by rw [hF' J]; exact hy`. Conclude with `this`. Establish `hcd : (c * d) • y ∈ secsOnZ F.toSubSystem H.toSubSystem h J`. Rewrite using `[← hF' J]`. Conclude with `Submodule.smul_mem _ (c * d) hy'`.

Establish `heq : c • ((d • h j ^ (a : ℤ)) • y) = h j ^ a • ((c * d) • y)`. Rewrite using `[chart_smul_eq, chart_smul_eq, smul_eq_mul, zpow_natCast, smul_smul, chart_smul_eq (c * d), smul_smul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[heq]`. Conclude with `fwd _ hcd`. Introduce `c`. Rewrite using `[smul_zero]`. Conclude with `Submodule.zero_mem _`.

Introduce `b e _ _ hb he c`. Rewrite using `[smul_add]`. Conclude with `Submodule.add_mem _ (hb c) (he c)`. Introduce `c' e _ he c`. Rewrite using `[smul_smul]`.

Conclude with `he (c * c')`. Introduce `e he`. Establish `heq : e = h j ^ a • ((h j ^ a)⁻¹ • e)`. Rewrite using `[smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hj0), one_smul]`. Rewrite using `[Submodule.restrictScalars_mem, heq]`.

Conclude with `Submodule.subset_span ⟨h j ^ a, by exact_mod_cast hq, _, bwd e he, rfl⟩`.
-/
theorem proof (hFam : VeryAmpleZFamily.Statement.{u, v, w}) : VeryAmpleZTwist.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F H r h hH a J
  obtain ⟨F', hF'⟩ := hFam S Ω N x E F H r h hH
  obtain ⟨j, hj⟩ := J.2.1
  have hj0 : h j ≠ 0 := (mem_support h).mp (J.2.2 hj)
  have hmem : ∀ l I, h l ∈ H.sub I := fun l I => (Submodule.mem_iInf _).mp (hH.mem_secs l) I
  have hpow : ∀ I, h j ^ a ∈ (H.pow a).sub I := fun I => by
    have h1 : h j ∈ (H.pow 1).sub I := by rw [SubSystem.pow_sub, pow_one]; exact hmem j I
    simpa using AmpleTwistLocal.pow_mem_pow H.toSubSystem I h1 a

  have fwd : ∀ y ∈ secsOnZ F.toSubSystem H.toSubSystem h J,
      h j ^ a • y ∈ secsOnZ (F.twist (H.pow a)) H.toSubSystem h J := by
    intro y hy
    refine (Submodule.mem_iInf _).mpr fun I => ?_
    have hyI : y ∈ secsOnZChart F.toSubSystem H.toSubSystem h I J := (Submodule.mem_iInf _).mp hy I
    refine Submodule.span_induction (p := fun y _ =>
      h j ^ a • y ∈ secsOnZChart (F.twist (H.pow a)) H.toSubSystem h I J) ?_ ?_ ?_ ?_ hyI
    · rintro y ⟨n, hn⟩
      refine Submodule.subset_span ⟨n, ?_⟩
      rw [smul_smul, mul_comm (xProd J ^ n), ← smul_smul]
      exact smul_mem_twist_twist _ _ _ I (hpow I) hn
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro b e _ _ hb he; rw [smul_add]; exact Submodule.add_mem _ hb he
    · intro s e _ he; rw [smul_comm]; exact Submodule.smul_mem _ s he

  have bwd : ∀ e ∈ secsOnZ (F.twist (H.pow a)) H.toSubSystem h J,
      (h j ^ a)⁻¹ • e ∈ secsOnZ F.toSubSystem H.toSubSystem h J := by
    classical
    intro e he
    refine (Submodule.mem_iInf _).mpr fun I => ?_
    have heI : e ∈ secsOnZChart (F.twist (H.pow a)) H.toSubSystem h I J := (Submodule.mem_iInf _).mp he I
    set u := ∏ l ∈ J.1.erase j, h l with hu
    have hxu : xProd J = h j * u := (Finset.mul_prod_erase J.1 h hj).symm
    have hk : J.1.card = (J.1.erase j).card + 1 := by
      rw [Finset.card_erase_of_mem hj]
      have := Finset.card_pos.mpr ⟨j, hj⟩
      omega
    have hua : u ^ a ∈ (H.pow ((J.1.erase j).card * a)).sub I :=
      AmpleTwistLocal.pow_mem_pow H.toSubSystem I (prod_mem_pow H.toSubSystem I (fun l => hmem l I) _) a
    refine Submodule.span_induction (p := fun e _ =>
      (h j ^ a)⁻¹ • e ∈ secsOnZChart F.toSubSystem H.toSubSystem h I J) ?_ ?_ ?_ ?_ heI
    · rintro e ⟨n, hn⟩
      refine Submodule.subset_span ⟨n + a, ?_⟩
      have heq : xProd J ^ (n + a) • (h j ^ a)⁻¹ • e = u ^ a • (xProd J ^ n • e) := by
        rw [smul_smul, smul_smul, hxu]
        congr 1
        field_simp
        ring
      have hdeg : a + J.1.card * n + (J.1.erase j).card * a = J.1.card * (n + a) := by
        rw [hk]; ring
      rw [heq, ← hdeg]
      exact smul_mem_twist_pow _ _ I hua (mem_twist_pow_add _ _ I hn)
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro b e _ _ hb he; rw [smul_add]; exact Submodule.add_mem _ hb he
    · intro s e _ he; rw [smul_comm]; exact Submodule.smul_mem _ s he
  have hq : h j ^ a ∈ twistMod S h (a : ℤ) J := by
    rw [twistMod_eq_span (a : ℤ) J hj, zpow_natCast]
    exact Submodule.mem_span_singleton_self _
  apply le_antisymm
  · intro z hz
    rw [Submodule.restrictScalars_mem] at hz
    suffices H1 : ∀ c : chartRing S h J, c • z ∈ secsOnZ (F.twist (H.pow a)) H.toSubSystem h J by
      simpa using H1 1
    refine Submodule.span_induction (p := fun z _ => ∀ c : chartRing S h J,
      c • z ∈ secsOnZ (F.twist (H.pow a)) H.toSubSystem h J) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨q, hq, y, hy, rfl⟩ c
      rw [twistMod_eq_span (a : ℤ) J hj, Submodule.mem_span_singleton] at hq
      obtain ⟨d, rfl⟩ := hq
      have hy' : y ∈ F'.sub J := by
        have : y ∈ (F'.sub J).restrictScalars S := by rw [hF' J]; exact hy
        exact this
      have hcd : (c * d) • y ∈ secsOnZ F.toSubSystem H.toSubSystem h J := by
        rw [← hF' J]; exact Submodule.smul_mem _ (c * d) hy'
      have heq : c • ((d • h j ^ (a : ℤ)) • y) = h j ^ a • ((c * d) • y) := by
        rw [chart_smul_eq, chart_smul_eq, smul_eq_mul, zpow_natCast, smul_smul, chart_smul_eq (c * d),
          smul_smul]
        congr 1
        push_cast
        ring
      rw [heq]
      exact fwd _ hcd
    · intro c; rw [smul_zero]; exact Submodule.zero_mem _
    · intro b e _ _ hb he c; rw [smul_add]; exact Submodule.add_mem _ (hb c) (he c)
    · intro c' e _ he c; rw [smul_smul]; exact he (c * c')
  · intro e he
    have heq : e = h j ^ a • ((h j ^ a)⁻¹ • e) := by
      rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hj0), one_smul]
    rw [Submodule.restrictScalars_mem, heq]
    exact Submodule.subset_span ⟨h j ^ a, by exact_mod_cast hq, _, bwd e he, rfl⟩

end VeryAmpleZTwist

end

end GroundTheory.Heights₂.Heights.Kleiman
