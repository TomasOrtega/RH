import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepTwo
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section JProper

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨q, hq, y, hy, rfl⟩`. Conclude with `Submodule.mul_mem_mul hq hy`. Use `Submodule.mul_le.mpr fun q hq y hy => Submodule.subset_span ⟨q, hq, y, hy, rfl⟩` and prove the remaining obligations.
-/
theorem twist_sub_eq_mul (F Q : SubSystem S x Ω) (I : Chart x) :
    (F.twist Q).sub I = Q.sub I * F.sub I := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    exact Submodule.mul_mem_mul hq hy
  · refine Submodule.mul_le.mpr fun q hq y hy => Submodule.subset_span ⟨q, hq, y, hy, rfl⟩

def ChartInvertible {I : Chart x} (P : Submodule (chartRing S x I) Ω) : Prop :=
  ∃ Q' : Submodule (chartRing S x I) Ω, P * Q' = 1

/- English proof (translation)
Take `⟨Q, hQ⟩` from `h`. Take `⟨Q', hQ'⟩` from `h'`. Conclude with `⟨Q * Q', by rw [mul_mul_mul_comm, hQ, hQ', one_mul]⟩`.
-/
theorem ChartInvertible.mul {I : Chart x} {P P' : Submodule (chartRing S x I) Ω}
    (h : ChartInvertible P) (h' : ChartInvertible P') : ChartInvertible (P * P') := by
  obtain ⟨Q, hQ⟩ := h
  obtain ⟨Q', hQ'⟩ := h'
  exact ⟨Q * Q', by rw [mul_mul_mul_comm, hQ, hQ', one_mul]⟩

/- English proof (translation)
The claim follows from `(twistBundle S x c).invertible I`.
-/
theorem chartInvertible_twistSys (c : ℤ) (I : Chart x) :
    ChartInvertible ((twistSys S x c).sub I) :=
  (twistBundle S x c).invertible I

/- English proof (translation)
Establish `hpow : ∀ n : ℕ, ChartInvertible ((M.toSubSystem.pow n).sub I)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => exact chartInvertible_twistSys 0 I`. Consider the case `succ n ih`.

Express the relevant statement in the definitionally equal form `ChartInvertible (((M.toSubSystem.pow n).twist M.toSubSystem).sub I)`. Rewrite using `[twist_sub_eq_mul]`. Conclude with `ChartInvertible.mul (M.invertible I) ih`. Rewrite using `[twistMul, twist_sub_eq_mul]`. Conclude with `ChartInvertible.mul (chartInvertible_twistSys m I) (hpow p)`.
-/
theorem chartInvertible_twistMul (M : LineBundle S x) (p : ℕ) (m : ℤ) (I : Chart x) :
    ChartInvertible ((twistMul M.toSubSystem p m).sub I) := by
  have hpow : ∀ n : ℕ, ChartInvertible ((M.toSubSystem.pow n).sub I) := by
    intro n
    induction n with
    | zero => exact chartInvertible_twistSys 0 I
    | succ n ih =>
      change ChartInvertible (((M.toSubSystem.pow n).twist M.toSubSystem).sub I)
      rw [twist_sub_eq_mul]
      exact ChartInvertible.mul (M.invertible I) ih
  rw [twistMul, twist_sub_eq_mul]
  exact ChartInvertible.mul (chartInvertible_twistSys m I) (hpow p)

/- English proof (translation)
Use `Submodule.span_induction (p := fun o _ => aeval x G * o ∈ twistMod S x (a + b) I) ?_ ?_ ?_ ?_ ho` and prove the remaining obligations. Introduce and unpack `_ ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩`. Use `Submodule.subset_span ⟨G * f, s, e, b + e', hs, hG.mul hf, hse, by push_cast; omega, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, mul_div_assoc]`. Rewrite using `[mul_zero]`.

Conclude with `Submodule.zero_mem _`. Introduce `y z _ _ hy hz`. Rewrite using `[mul_add]`. Conclude with `Submodule.add_mem _ hy hz`. Introduce `r z _ hz`.

Rewrite using `[chartRing_smul_def, mul_left_comm, ← chartRing_smul_def]`. Conclude with `Submodule.smul_mem _ r hz`.
-/
theorem aeval_mul_mem_twistMod {I : Chart x} {G : Poly S N} {b : ℕ} (hG : G.IsHomogeneous b) {a : ℤ}
    {o : Ω} (ho : o ∈ twistMod S x a I) : aeval x G * o ∈ twistMod S x (a + b) I := by
  refine Submodule.span_induction (p := fun o _ => aeval x G * o ∈ twistMod S x (a + b) I)
    ?_ ?_ ?_ ?_ ho
  · rintro _ ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩
    refine Submodule.subset_span ⟨G * f, s, e, b + e', hs, hG.mul hf, hse, by push_cast; omega, ?_⟩
    rw [map_mul, mul_div_assoc]
  · rw [mul_zero]; exact Submodule.zero_mem _
  · intro y z _ _ hy hz; rw [mul_add]; exact Submodule.add_mem _ hy hz
  · intro r z _ hz
    rw [chartRing_smul_def, mul_left_comm, ← chartRing_smul_def]
    exact Submodule.smul_mem _ r hz

/- English proof (translation)
Take `⟨Q', hQ'⟩` from `hP`. Establish `hq : ∃ q ∈ Q', q ≠ 0`. Assume the negation of the conclusion as `hcon`. Simplify using `only [not_exists, not_and, not_not] at hcon`. Establish `hbot : Q' = ⊥` using `(Submodule.eq_bot_iff _).mpr hcon`.

Establish `h1 : (1 : Ω) ∈ (1 : Submodule (chartRing S x I) Ω)` using `Submodule.mem_one.mpr ⟨1, map_one _⟩`. Rewrite `h1` using `[← hQ', hbot, Submodule.mul_bot, Submodule.mem_bot]`. Conclude with `one_ne_zero h1`. Take `⟨q, hqQ, hq0⟩` from `hq`. Take `⟨b, hb⟩` from `Submodule.mem_one.mp (hQ' ▸ Submodule.mul_mem_mul hσ hqQ : σ * q ∈ (1 : Submodule (chartRing S x I) Ω))`.

Take `⟨g, s, e, hs, hg, hse, hbg⟩` from `b.2`. Establish `hs0` using `eval_ne_zero_of_mem_monos I hs`. Establish `hb' : (b : Ω) = σ * q` using `hb`. Establish `hgx : aeval x g = σ * q * aeval x s`. Rewrite using `[← hb', hbg, div_mul_cancel₀ _ hs0]`.

Use `⟨g, e, hg, by rw [hgx]; exact mul_ne_zero (mul_ne_zero hσ0 hq0) hs0, fun δ hδ => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `Submodule.mem_one.mp (hQ' ▸ Submodule.mul_mem_mul hδ hqQ : δ * q ∈ (1 : Submodule (chartRing S x I) Ω))`. Take `⟨h, t, e', ht, hh, hte, hah⟩` from `a.2`. Establish `ha' : aeval x h / aeval x t = δ * q` using `by rw [← hah]; exact ha`. Use `⟨aeval x (s * h) / aeval x t, Submodule.subset_span ⟨s * h, t, e', e + e', ht, hse.mul hh, hte, by push_cast; ring, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, mul_div_assoc, ha', hgx]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_form_chart {I : Chart x} {P : Submodule (chartRing S x I) Ω} (hP : ChartInvertible P)
    {σ : Ω} (hσ : σ ∈ P) (hσ0 : σ ≠ 0) : ∃ (g : Poly S N) (e : ℕ), g.IsHomogeneous e ∧
      aeval x g ≠ 0 ∧ ∀ δ ∈ P, ∃ o ∈ twistMod S x (e : ℤ) I, aeval x g * δ = σ * o := by
  obtain ⟨Q', hQ'⟩ := hP
  have hq : ∃ q ∈ Q', q ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hbot : Q' = ⊥ := (Submodule.eq_bot_iff _).mpr hcon
    have h1 : (1 : Ω) ∈ (1 : Submodule (chartRing S x I) Ω) := Submodule.mem_one.mpr ⟨1, map_one _⟩
    rw [← hQ', hbot, Submodule.mul_bot, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  obtain ⟨q, hqQ, hq0⟩ := hq
  obtain ⟨b, hb⟩ := Submodule.mem_one.mp (hQ' ▸ Submodule.mul_mem_mul hσ hqQ :
    σ * q ∈ (1 : Submodule (chartRing S x I) Ω))
  obtain ⟨g, s, e, hs, hg, hse, hbg⟩ := b.2
  have hs0 := eval_ne_zero_of_mem_monos I hs
  have hb' : (b : Ω) = σ * q := hb
  have hgx : aeval x g = σ * q * aeval x s := by
    rw [← hb', hbg, div_mul_cancel₀ _ hs0]
  refine ⟨g, e, hg, by rw [hgx]; exact mul_ne_zero (mul_ne_zero hσ0 hq0) hs0, fun δ hδ => ?_⟩
  obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hQ' ▸ Submodule.mul_mem_mul hδ hqQ :
    δ * q ∈ (1 : Submodule (chartRing S x I) Ω))
  obtain ⟨h, t, e', ht, hh, hte, hah⟩ := a.2
  have ha' : aeval x h / aeval x t = δ * q := by rw [← hah]; exact ha
  refine ⟨aeval x (s * h) / aeval x t,
    Submodule.subset_span ⟨s * h, t, e', e + e', ht, hse.mul hh, hte, by push_cast; ring, rfl⟩, ?_⟩
  rw [map_mul, mul_div_assoc, ha', hgx]
  ring

end JProper

/- English proof (translation)
Introduce `k _ Ω _ _ N x T`. Establish `hloc : ∀ I : Chart x, ∃ (g : Poly k N) (e : ℕ), g.IsHomogeneous e ∧ aeval x g ≠ 0 ∧ ∀ δ ∈ T.D.sub I, ∃ o ∈ twistMod k x (e : ℤ) I, aeval x g * δ = T.si * o` using `fun I => exists_form_chart (chartInvertible_twistMul T.M T.p (T.m - T.c₁) I) ((Submodule.mem_iInf _).mp T.si_mem I) T.si_ne`. Use `choose g e hg hg0 hgD using hloc`. Use `⟨∏ I, g I, ∑ I, e I, Ideal.subset_span ⟨∑ I, e I, IsHomogeneous.prod _ _ _ fun I _ => hg I, fun I δ hδ => ?_⟩, IsHomogeneous.prod _ _ _ fun I _ => hg I, ?_⟩` and prove the remaining obligations. Take `⟨o, ho, hδo⟩` from `hgD I δ hδ`.

Establish `hrest : (∏ J ∈ Finset.univ.erase I, g J).IsHomogeneous (∑ J ∈ Finset.univ.erase I, e J)` using `IsHomogeneous.prod _ _ _ fun J _ => hg J`. Use `⟨aeval x (∏ J ∈ Finset.univ.erase I, g J) * o, ?_, ?_⟩` and prove the remaining obligations. Establish `hm` using `aeval_mul_mem_twistMod hrest ho`. Establish `hdeg : ((e I : ℕ) : ℤ) + ((∑ J ∈ Finset.univ.erase I, e J : ℕ) : ℤ) = ((∑ J, e J : ℕ) : ℤ)`. Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_univ I)]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hm` using `[hdeg]`. Then use the resulting hypothesis. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ I), map_mul, mul_comm (aeval x (g I)), mul_assoc, hδo]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[mem_primeOf_of_isHomogeneous x (IsHomogeneous.prod _ _ _ fun I _ => hg I), map_prod]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun I _ => hg0 I`.
-/
theorem StepData.JProper.proof : StepData.JProper.Statement.{u, w} := by
  classical
  intro k _ Ω _ _ N x T
  have hloc : ∀ I : Chart x, ∃ (g : Poly k N) (e : ℕ), g.IsHomogeneous e ∧ aeval x g ≠ 0 ∧
      ∀ δ ∈ T.D.sub I, ∃ o ∈ twistMod k x (e : ℤ) I, aeval x g * δ = T.si * o := fun I =>
    exists_form_chart (chartInvertible_twistMul T.M T.p (T.m - T.c₁) I)
      ((Submodule.mem_iInf _).mp T.si_mem I) T.si_ne
  choose g e hg hg0 hgD using hloc
  refine ⟨∏ I, g I, ∑ I, e I, Ideal.subset_span ⟨∑ I, e I, IsHomogeneous.prod _ _ _
    fun I _ => hg I, fun I δ hδ => ?_⟩, IsHomogeneous.prod _ _ _ fun I _ => hg I, ?_⟩
  · obtain ⟨o, ho, hδo⟩ := hgD I δ hδ
    have hrest : (∏ J ∈ Finset.univ.erase I, g J).IsHomogeneous (∑ J ∈ Finset.univ.erase I, e J) :=
      IsHomogeneous.prod _ _ _ fun J _ => hg J
    refine ⟨aeval x (∏ J ∈ Finset.univ.erase I, g J) * o, ?_, ?_⟩
    · have hm := aeval_mul_mem_twistMod hrest ho
      have hdeg : ((e I : ℕ) : ℤ) + ((∑ J ∈ Finset.univ.erase I, e J : ℕ) : ℤ) =
          ((∑ J, e J : ℕ) : ℤ) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ I)]; push_cast; ring
      rwa [hdeg] at hm
    · rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ I), map_mul, mul_comm (aeval x (g I)),
        mul_assoc, hδo]
      ring
  · rw [mem_primeOf_of_isHomogeneous x (IsHomogeneous.prod _ _ _ fun I _ => hg I), map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun I _ => hg0 I

end

end GroundTheory.Heights₂.Heights.Kleiman
