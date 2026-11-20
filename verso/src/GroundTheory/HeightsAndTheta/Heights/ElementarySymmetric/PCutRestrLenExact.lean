import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StCutRestrLenExact
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionMulInj
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThreeAway
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSurjectiveClosed
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDropFiltStep
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PZeroIdealChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace CutRestrLenExact

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

/- English proof (translation)
Take `⟨f, s, n, hs, hf, hsn, hz⟩` from `hy _ hσ`. Establish `hs0` using `eval_ne_zero_of_mem_monos I hs`. Establish `hfz : y * σ * aeval x s = aeval x f` using `(eq_div_iff hs0).mp hz`. Establish `hyU` using `mul_mem_chartRing_union L.toSubFamily I`. Use `choose G hG using fun K => L.fg K`.

Establish `hgen : ∀ p : Σ K : Chart x, (G K : Set Ω), y * (p.2 : Ω) ∈ chartRing S x (chartUnion I p.1)` using `fun p => hyU p.1 y hy _ (L.mono p.1 (chartUnion I p.1) (show p.1.1 ⊆ (chartUnion I p.1).1 from Finset.subset_union_right) _ (by rw [← hG p.1]; exact Submodule.subset_span p.2.2))`. Use `choose u hu d hd hud using fun p : (Σ K : Chart x, (G K : Set Ω)) => exists_monos_mul_mem_twistMod (S := S) I p.1 (y * (p.2 : Ω)) (hgen p)`. Take `⟨U, hUdef⟩ : ∃ U : Poly S N, U = ∏ p, u p` from `⟨_, rfl⟩`. Take `⟨dU, hdUdef⟩ : ∃ dU : ℕ, dU = ∑ p, d p` from `⟨_, rfl⟩`. Establish `hUm : U ∈ monos (S` using `S) I.1 := hUdef ▸ prod_mem fun p _ => hu p`.

Establish `hUh : U.IsHomogeneous dU` using `hUdef ▸ hdUdef ▸ IsHomogeneous.prod _ _ _ fun p _ => hd p`. Establish `key : ∀ p : Σ K : Chart x, (G K : Set Ω), aeval x U * (y * (p.2 : Ω)) ∈ twistMod S x (dU : ℤ) p.1`. Introduce `p`. Establish `hsplit : U = u p * ∏ q ∈ Finset.univ.erase p, u q`. Rewrite using `[hUdef, Finset.mul_prod_erase _ _ (Finset.mem_univ p)]`.

Establish `hdsplit : dU = d p + ∑ q ∈ Finset.univ.erase p, d q`. Rewrite using `[hdUdef, Finset.add_sum_erase _ _ (Finset.mem_univ p)]`. Establish `h2` using `aeval_mem_twistMod (x := x) (IsHomogeneous.prod _ _ _ fun q _ => hd q : (∏ q ∈ Finset.univ.erase p, u q).IsHomogeneous _) p.1`. Establish `h3` using `twistMod_mul_mem (hud p) h2`. Rewrite using `[hsplit, hdsplit, map_mul, Nat.cast_add]`.

Use `h3 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `hUK : ∀ (K : Chart x), ∀ δ ∈ L.sub K, aeval x U * (y * δ) ∈ twistMod S x (dU : ℤ) K`. Introduce `K δ hδ`. Rewrite `hδ` using `[← hG K]`.

Proceed by induction on `hδ using Submodule.span_induction with`. Consider the case `mem δ hδ => exact key ⟨K, ⟨δ, hδ⟩⟩`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [mul_add, mul_add]`. Conclude with `add_mem ha hb`.

Consider the case `smul a b _ hb`. Rewrite using `[chartRing_smul_def, show aeval x U * (y * ((a : Ω) * b)) = (a : Ω) * (aeval x U * (y * b)) by ring, ← chartRing_smul_def]`. Conclude with `Submodule.smul_mem _ a hb`. Establish `hU0` using `eval_ne_zero_of_mem_monos I hUm`. Establish `hfU : f * U ∈ zeroIdeal L.toSubSystem σ`.

Use `Ideal.subset_span ⟨n + dU, hf.mul hUh, fun K δ hδ => ?_⟩` and prove the remaining obligations. Use `⟨aeval x s * (aeval x U * (y * δ)), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_add]`. Conclude with `twistMod_mul_mem (aeval_mem_twistMod hsn K) (hUK K δ hδ)`. Rewrite using `[map_mul, ← hfz]`.

Expand and normalize the polynomial expressions, which then agree. Use `Submodule.subset_span ⟨f * U, s * U, n + dU, hfU, mul_mem hs hUm, hf.mul hUh, hsn.mul hUh, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, ← hfz]`. Clear the denominators using the available nonvanishing facts.
-/
theorem mul_mem_idealMod_zeroIdeal (L : LineBundle S x) {σ : Ω} (I : Chart x) (hσ : σ ∈ L.sub I) (y : Ω)
    (hy : ∀ δ ∈ L.sub I, y * δ ∈ chartRing S x I) :
    σ * y ∈ idealMod (zeroIdeal L.toSubSystem σ) I := by
  classical
  obtain ⟨f, s, n, hs, hf, hsn, hz⟩ := hy _ hσ
  have hs0 := eval_ne_zero_of_mem_monos I hs
  have hfz : y * σ * aeval x s = aeval x f := (eq_div_iff hs0).mp hz
  have hyU := mul_mem_chartRing_union L.toSubFamily I
  choose G hG using fun K => L.fg K
  have hgen : ∀ p : Σ K : Chart x, (G K : Set Ω),
      y * (p.2 : Ω) ∈ chartRing S x (chartUnion I p.1) := fun p =>
    hyU p.1 y hy _ (L.mono p.1 (chartUnion I p.1)
      (show p.1.1 ⊆ (chartUnion I p.1).1 from Finset.subset_union_right) _
      (by rw [← hG p.1]; exact Submodule.subset_span p.2.2))
  choose u hu d hd hud using fun p : (Σ K : Chart x, (G K : Set Ω)) =>
    exists_monos_mul_mem_twistMod (S := S) I p.1 (y * (p.2 : Ω)) (hgen p)
  obtain ⟨U, hUdef⟩ : ∃ U : Poly S N, U = ∏ p, u p := ⟨_, rfl⟩
  obtain ⟨dU, hdUdef⟩ : ∃ dU : ℕ, dU = ∑ p, d p := ⟨_, rfl⟩
  have hUm : U ∈ monos (S := S) I.1 := hUdef ▸ prod_mem fun p _ => hu p
  have hUh : U.IsHomogeneous dU := hUdef ▸ hdUdef ▸ IsHomogeneous.prod _ _ _ fun p _ => hd p
  have key : ∀ p : Σ K : Chart x, (G K : Set Ω),
      aeval x U * (y * (p.2 : Ω)) ∈ twistMod S x (dU : ℤ) p.1 := by
    intro p
    have hsplit : U = u p * ∏ q ∈ Finset.univ.erase p, u q := by
      rw [hUdef, Finset.mul_prod_erase _ _ (Finset.mem_univ p)]
    have hdsplit : dU = d p + ∑ q ∈ Finset.univ.erase p, d q := by
      rw [hdUdef, Finset.add_sum_erase _ _ (Finset.mem_univ p)]
    have h2 := aeval_mem_twistMod (x := x)
      (IsHomogeneous.prod _ _ _ fun q _ => hd q : (∏ q ∈ Finset.univ.erase p, u q).IsHomogeneous _) p.1
    have h3 := twistMod_mul_mem (hud p) h2
    rw [hsplit, hdsplit, map_mul, Nat.cast_add]
    convert h3 using 1
    ring
  have hUK : ∀ (K : Chart x), ∀ δ ∈ L.sub K, aeval x U * (y * δ) ∈ twistMod S x (dU : ℤ) K := by
    intro K δ hδ
    rw [← hG K] at hδ
    induction hδ using Submodule.span_induction with
    | mem δ hδ => exact key ⟨K, ⟨δ, hδ⟩⟩
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add, mul_add]; exact add_mem ha hb
    | smul a b _ hb =>
      rw [chartRing_smul_def, show aeval x U * (y * ((a : Ω) * b)) = (a : Ω) * (aeval x U * (y * b)) by ring,
        ← chartRing_smul_def]
      exact Submodule.smul_mem _ a hb
  have hU0 := eval_ne_zero_of_mem_monos I hUm
  have hfU : f * U ∈ zeroIdeal L.toSubSystem σ := by
    refine Ideal.subset_span ⟨n + dU, hf.mul hUh, fun K δ hδ => ?_⟩
    refine ⟨aeval x s * (aeval x U * (y * δ)), ?_, ?_⟩
    · rw [Nat.cast_add]
      exact twistMod_mul_mem (aeval_mem_twistMod hsn K) (hUK K δ hδ)
    · rw [map_mul, ← hfz]
      ring
  refine Submodule.subset_span ⟨f * U, s * U, n + dU, hfU, mul_mem hs hUm, hf.mul hUh, hsn.mul hUh, ?_⟩
  rw [map_mul, map_mul, ← hfz]
  field_simp

/- English proof (translation)
Take `⟨L', hL'⟩` from `L.invertible I`. Establish `h1 : (1 : Ω) ∈ L.sub I * L'` using `by rw [hL']; exact Submodule.mem_one.mpr ⟨1, map_one _⟩`. Establish `hle : L.sub I * L' ≤ (idealMod (zeroIdeal L.toSubSystem σ) I * L.sub I).comap (LinearMap.mulLeft (chartRing S x I) σ)`. Use `Submodule.mul_le.mpr fun a ha b hb => ?_` and prove the remaining obligations. Rewrite using `[Submodule.mem_comap, LinearMap.mulLeft_apply]`.

Establish `hb' : ∀ δ ∈ L.sub I, b * δ ∈ chartRing S x I`. Introduce `δ hδ`. Establish `h2 : b * δ ∈ (1 : Submodule (chartRing S x I) Ω)`. Rewrite using `[← hL', mul_comm b]`. Conclude with `Submodule.mul_mem_mul hδ hb`.

Take `⟨r, hr⟩` from `Submodule.mem_one.mp h2`. Rewrite using `[← hr]`. Conclude with `r.2`. Establish `h3` using `Submodule.mul_mem_mul (mul_mem_idealMod_zeroIdeal L I hσ b hb') ha`. Use `h3 using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Use `hle h1` as an intermediate fact. Rewrite `this` using `[Submodule.mem_comap, LinearMap.mulLeft_apply, mul_one]`. Then use the resulting hypothesis.
-/
theorem mem_idealMod_zeroIdeal_mul (L : LineBundle S x) {σ : Ω} (I : Chart x) (hσ : σ ∈ L.sub I) :
    σ ∈ idealMod (zeroIdeal L.toSubSystem σ) I * L.sub I := by
  obtain ⟨L', hL'⟩ := L.invertible I
  have h1 : (1 : Ω) ∈ L.sub I * L' := by rw [hL']; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  have hle : L.sub I * L' ≤ (idealMod (zeroIdeal L.toSubSystem σ) I * L.sub I).comap
      (LinearMap.mulLeft (chartRing S x I) σ) := by
    refine Submodule.mul_le.mpr fun a ha b hb => ?_
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
    have hb' : ∀ δ ∈ L.sub I, b * δ ∈ chartRing S x I := by
      intro δ hδ
      have h2 : b * δ ∈ (1 : Submodule (chartRing S x I) Ω) := by
        rw [← hL', mul_comm b]; exact Submodule.mul_mem_mul hδ hb
      obtain ⟨r, hr⟩ := Submodule.mem_one.mp h2
      rw [← hr]; exact r.2
    have h3 := Submodule.mul_mem_mul (mul_mem_idealMod_zeroIdeal L I hσ b hb') ha
    convert h3 using 1
    ring
  have := hle h1
  rwa [Submodule.mem_comap, LinearMap.mulLeft_apply, mul_one] at this

/- English proof (translation)
Take `⟨i, hi⟩` from `I.2.1`. Establish `hxi : x i ≠ 0` using `(mem_support x).mp (I.2.2 hi)`. Use `Submodule.mul_le.mpr fun m hm δ hδ => ?_` and prove the remaining obligations. Proceed by induction on `hm using Submodule.span_induction with`. Consider the case `mem z hz`.

Take `⟨f, t, d, hf, ht, hfd, htd, rfl⟩` from `hz`. Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.mp hf`. Establish `hf' : f = homogeneousComponent d a + homogeneousComponent d b`. Rewrite using `[← map_add, hab, homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hfd), if_pos rfl]`. Rewrite using `[hf', map_add, add_div, add_mul]`.

Use `Submodule.add_mem_sup (Submodule.mul_mem_mul (Submodule.subset_span ⟨_, t, d, hpp a ha d, ht, homogeneousComponent_isHomogeneous d a, htd, rfl⟩) hδ) ?_` and prove the remaining obligations. Take `⟨r, hr⟩` from `Submodule.mem_span_singleton.mp (StepThree.Away.homogeneousComponent_mul_mem L.toSubSystem σ I hi hb d δ hδ)`. Establish `hq : x i ^ d / aeval x t ∈ chartRing S x I` using `⟨X i ^ d, t, d, ht, isHomogeneous_X_pow i d, htd, by rw [map_pow, aeval_X]⟩`. Establish `ht0` using `eval_ne_zero_of_mem_monos I ht`. Use `Submodule.mem_span_singleton.mpr ⟨⟨_, hq⟩ * r, ?_⟩` and prove the remaining obligations.

Rewrite `hr` using `[chartRing_smul_def]`. Rewrite using `[chartRing_smul_def, Subalgebra.coe_mul, div_mul_eq_mul_div (aeval x (homogeneousComponent d b)), ← hr]`. Clear the denominators using the available nonvanishing facts. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [add_mul]`.

Conclude with `add_mem ha hb`. Consider the case `smul a z _ hz`. Rewrite using `[chartRing_smul_def, mul_assoc, ← chartRing_smul_def]`. Conclude with `Submodule.smul_mem _ a hz`.
-/
theorem idealMod_sup_mul_le (L : LineBundle S x) (σ : Ω) {pp : Ideal (Poly S N)}
    (hpp : ∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) (I : Chart x) :
    idealMod (pp ⊔ zeroIdeal L.toSubSystem σ) I * L.sub I ≤
      idealMod pp I * L.sub I ⊔ Submodule.span (chartRing S x I) {σ} := by
  classical
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  refine Submodule.mul_le.mpr fun m hm δ hδ => ?_
  induction hm using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨f, t, d, hf, ht, hfd, htd, rfl⟩ := hz
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hf
    have hf' : f = homogeneousComponent d a + homogeneousComponent d b := by
      rw [← map_add, hab, homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hfd),
        if_pos rfl]
    rw [hf', map_add, add_div, add_mul]
    refine Submodule.add_mem_sup (Submodule.mul_mem_mul (Submodule.subset_span ⟨_, t, d, hpp a ha d, ht,
      homogeneousComponent_isHomogeneous d a, htd, rfl⟩) hδ) ?_
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp
      (StepThree.Away.homogeneousComponent_mul_mem L.toSubSystem σ I hi hb d δ hδ)
    have hq : x i ^ d / aeval x t ∈ chartRing S x I :=
      ⟨X i ^ d, t, d, ht, isHomogeneous_X_pow i d, htd, by rw [map_pow, aeval_X]⟩
    have ht0 := eval_ne_zero_of_mem_monos I ht
    refine Submodule.mem_span_singleton.mpr ⟨⟨_, hq⟩ * r, ?_⟩
    rw [chartRing_smul_def] at hr
    rw [chartRing_smul_def, Subalgebra.coe_mul, div_mul_eq_mul_div (aeval x (homogeneousComponent d b)), ← hr]
    field_simp
  | zero => simp
  | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
  | smul a z _ hz =>
    rw [chartRing_smul_def, mul_assoc, ← chartRing_smul_def]
    exact Submodule.smul_mem _ a hz

/- English proof (translation)
Introduce `k _ Ω _ _ N x e pp Lc s hW hs ⟨I₀, hI₀⟩ Q`. Take `⟨c₀, hc₀⟩` from `hSC k Ω N x Q pp hW.homog`. Use `filter_upwards [eventually_ge_atTop c₀.toNat] with c hc`. Establish `hcc : c₀ ≤ (c : ℤ)`. Use `Int.toNat_le.mp hc` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Use `set J := zeroIdeal Lc.toSubSystem s with hJ`. Use `set F : SubSystem k x Ω := (Q.toSubSystem.twist Lc.toSubSystem).twist (twistSys k x (c : ℤ)) with hF`. Use `set F' : SubSystem k x Ω := Q.toSubSystem.twist (twistSys k x (c : ℤ)) with hF'`. Establish `hFI : ∀ I, F.sub I = Lc.sub I * F'.sub I` using `fun I => by`.

Simplify using `only [hF, hF', SubSystem.twist_sub_eq_mul_of_line]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsub : ∀ (K : Ideal (Poly k N)) (G : SubSystem k x Ω) (I : Chart x), (G.twist (idealSys x K)).sub I = idealMod K I * G.sub I` using `fun K G I => SubSystem.twist_sub_eq_mul_of_line _ _ I`. Establish `hsL : ∀ I, s ∈ Lc.sub I` using `fun I => SectionCount.Drop.Filt.Step.mem_secs_iff'.mp hs I`. Establish `hsI : ∀ I, s ∈ idealMod J I * Lc.sub I` using `fun I => mem_idealMod_zeroIdeal_mul Lc I (hsL I)`.

Establish `hmono : ∀ {K₁ K₂ : Ideal (Poly k N)}, K₁ ≤ K₂ → ∀ I, idealMod (x` using `x) K₁ I ≤ idealMod K₂ I := by`. Introduce `K₁ K₂ h I`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨f, t, d, hf, ht, hfd, htd, rfl⟩`. Conclude with `⟨f, t, d, h hf, ht, hfd, htd, rfl⟩`.

Establish `hgK' : ∀ I, ∀ y ∈ F'.sub I, s * y ∈ (F.twist (idealSys x (pp ⊔ J))).sub I`. Introduce `I y hy`. Rewrite using `[hsub, hFI, ← mul_assoc]`. Conclude with `mul_le_mul' (mul_le_mul' (hmono le_sup_right I) le_rfl) le_rfl (Submodule.mul_mem_mul (hsI I) hy)`. Establish `hJp : ∃ f ∈ J, f ∉ pp`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Apply `hI₀` to reduce the goal to its premises. Rewrite using `[hsub]`. Conclude with `mul_le_mul' (hmono (fun f hf => hcon f hf) I₀) le_rfl (hsI I₀)`.

Establish `hU : ∀ I, ∀ y ∈ F'.sub I, s * y ∈ (F.twist (idealSys x pp)).sub I → y ∈ (F'.twist (idealSys x pp)).sub I`. Introduce `I y hy hsy`. Use `SectionMulInj.proof k Ω N x pp hW.isPrime hW.homog hW.le Lc (Q.tensorProd (twistBundle k x (c : ℤ))) s hJp I y hy ?_` and prove the remaining obligations. Rewrite using `[hsub, SubSystem.twist_sub_eq_mul_of_line]`. Rewrite `hsy` using `[hsub, hFI]`.

Conclude with `hsy`. Establish `hC : ∀ I, ∀ y ∈ (F'.twist (idealSys x pp)).sub I, s * y ∈ (F.twist (idealSys x pp)).sub I`. Introduce `I y hy`. Rewrite `hy` using `[hsub]`. Rewrite using `[hsub, hFI, mul_left_comm]`.

Conclude with `Submodule.mul_mem_mul (hsL I) hy`. Establish `hE : ∀ z ∈ (F.twist (idealSys x (pp ⊔ J))).secs, ∀ I, ∃ y ∈ F'.sub I, z - s * y ∈ (F.twist (idealSys x pp)).sub I`. Introduce `z hz I`. Establish `hzI` using `SectionCount.Drop.Filt.Step.mem_secs_iff'.mp hz I`. Rewrite `hzI` using `[hsub, hFI, ← mul_assoc]`.

Establish `h1` using `mul_le_mul' (idealMod_sup_mul_le Lc s hW.homog I) le_rfl hzI`. Rewrite `h1` using `[Submodule.sup_mul]`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.mp h1`. Take `⟨q, hq, rfl⟩` from `Submodule.mem_span_singleton_mul.mp hb`. Use `⟨q, hq, ?_⟩` and prove the remaining obligations.

Rewrite using `[add_sub_cancel_right, hsub, hFI, ← mul_assoc]`. Conclude with `ha`. Establish `hWV : ∀ z, z ∈ (F.twist (idealSys x pp)).secs → z ∈ (F.twist (idealSys x (pp ⊔ J))).secs`. Introduce `z hz`. Use `SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I => ?_` and prove the remaining obligations.

Establish `h1` using `SectionCount.Drop.Filt.Step.mem_secs_iff'.mp hz I`. Rewrite `h1`, the goal using `[hsub]`. Conclude with `mul_le_mul' (hmono le_sup_left I) le_rfl h1`. Establish `hVH : ∀ z, z ∈ (F.twist (idealSys x (pp ⊔ J))).secs → z ∈ F.secs` using `fun z hz => SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I => SurjectiveClosed.twist_idealSys_le F _ I (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp hz I)`. Establish `hgsec : ∀ y ∈ F'.secs, s * y ∈ (F.twist (idealSys x (pp ⊔ J))).secs` using `fun y hy => SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I => hgK' I y (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp hy I)`.

Establish `hlift : ∀ z ∈ (F.twist (idealSys x (pp ⊔ J))).secs, ∃ t ∈ F'.secs, z - s * t ∈ (F.twist (idealSys x pp)).secs`. Introduce `z hz`. Use `choose y hy hys using hE z hz`. Establish `hcomp : ∀ (I₁ I₂ : Chart x), I₁.1 ⊆ I₂.1 → y I₁ - y I₂ ∈ (F'.twist (idealSys x pp)).sub I₂`. Introduce `I₁ I₂ h`.

Use `hU I₂ _ (sub_mem (F'.mono I₁ I₂ h _ (hy I₁)) (hy I₂)) ?_` and prove the remaining obligations. Establish `h1` using `sub_mem (hys I₂) ((F.twist (idealSys x pp)).mono I₁ I₂ h _ (hys I₁))`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Take `⟨t, ht, htI⟩` from `hc₀ _ hcc y hy hcomp`.

Use `⟨t, ht, SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I => ?_⟩` and prove the remaining obligations. Establish `h1` using `add_mem (hys I) (hC I _ (neg_mem (htI I)))`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Use `set H := F.secs with hH`.

Use `set H' := F'.secs with hH'`. Use `set A := ((F.twist (idealSys x pp)).secs).comap H.subtype with hA`. Use `set B := ((F.twist (idealSys x (pp ⊔ J))).secs).comap H.subtype with hB`. Use `set P := ((F'.twist (idealSys x pp)).secs).comap H'.subtype with hP`. Establish `hAB : A ≤ B` using `fun z hz => Submodule.mem_comap.mpr (hWV _ (Submodule.mem_comap.mp hz))`.

Set `μ0 : H' →ₗ[k] H` to `(LinearMap.mulLeft k s).restrict (p := H') (q := H) (fun y hy => hVH _ (hgsec y hy))`. Set `μ : H' →ₗ[k] H ⧸ A` to `A.mkQ ∘ₗ μ0`. Establish `hμ : ∀ y : H', y ∈ P ↔ μ y = 0`. Introduce `y`. Rewrite using `[LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_comap]`.

Express the relevant statement in the definitionally equal form `(y : Ω) ∈ _ ↔ s * (y : Ω) ∈ _`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I => hC I _ (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp h I)`. Introduce `h`.

Conclude with `SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I => hU I _ (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp y.2 I) (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp h I)`. Set `μb : (H' ⧸ P) →ₗ[k] H ⧸ A` to `P.liftQ μ (fun y hy => (hμ y).mp hy)`. Establish `hinj : Function.Injective μb`. Rewrite using `[← LinearMap.ker_eq_bot]`. Conclude with `Submodule.ker_liftQ_eq_bot _ _ _ (fun y hy => (hμ y).mpr hy)`.

Set `π : (H ⧸ A) →ₗ[k] H ⧸ B` to `Submodule.factor hAB`. Establish `hsurj : Function.Surjective π`. Introduce `z`. Take `⟨m, rfl⟩` from `Submodule.mkQ_surjective B z`. Conclude with `⟨A.mkQ m, rfl⟩`.

Establish `hex : Function.Exact μb π`. Introduce `z`. Take `⟨m, rfl⟩` from `Submodule.mkQ_surjective A z`. Express the relevant statement in the definitionally equal form `B.mkQ m = 0 ↔ _`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`.

Prove the components needed by the constructor for the conclusion. Introduce `hm`. Take `⟨t, ht, hst⟩` from `hlift _ hm`. Use `⟨P.mkQ ⟨t, ht⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `A.mkQ (μ0 ⟨t, ht⟩) = A.mkQ m`.

Rewrite using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap]`. Express the relevant statement in the definitionally equal form `s * t - (m : Ω) ∈ _`. Establish `h1` using `neg_mem hst`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[neg_sub]`.

Both sides reduce to the same expression. Introduce and unpack `⟨v, hv⟩`. Take `⟨y, rfl⟩` from `Submodule.mkQ_surjective P v`. Express the relevant statement in the definitionally equal form `A.mkQ (μ0 y) = A.mkQ m at hv`. Rewrite `hv` using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap]`.

Express the relevant statement in the definitionally equal form `s * (y : Ω) - m ∈ _ at hv`. Express the relevant statement in the definitionally equal form `(m : Ω) ∈ _`. Establish `h1` using `sub_mem (hgsec _ y.2) (hWV _ hv)`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Establish `hlen` using `Module.length_eq_add_of_exact μb π hinj hsurj hex`. Establish `hx : x ≠ 0`. Take `⟨i, hi⟩` from `I₀.2.1`. Introduce `h0`. Conclude with `(mem_support x).mp (I₀.2.2 hi) (by simp [h0])`.

Establish `hfin : Module.length k (H ⧸ A) ≠ ⊤`. Establish `: Module.Finite k H` using `(hFS k Ω N x ((Q.tensorProd Lc).tensorProd (twistBundle k x (c : ℤ))) hx).1`. Conclude with `Module.length_ne_top`. Establish `hB' : Module.length k (H ⧸ B) ≠ ⊤` using `fun h => hfin (by rw [hlen, h, add_top])`. Establish `hP' : Module.length k (H' ⧸ P) ≠ ⊤` using `fun h => hfin (by rw [hlen, h, top_add])`.

Express the relevant statement in the definitionally equal form `((Module.length k (H ⧸ A)).toNat : ℤ) - ((Module.length k (H' ⧸ P)).toNat : ℤ) = ((Module.length k (H ⧸ B)).toNat : ℤ)`. Rewrite using `[hlen, ENat.toNat_add hP' hB']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem proof (hSC : SurjectiveClosed.Statement.{u, w}) (hFS : FiniteSections.Statement.{u, w}) :
    CutRestrLenExact.Statement.{u, w} := by
  classical
  intro k _ Ω _ _ N x e pp Lc s hW hs ⟨I₀, hI₀⟩ Q
  obtain ⟨c₀, hc₀⟩ := hSC k Ω N x Q pp hW.homog
  filter_upwards [eventually_ge_atTop c₀.toNat] with c hc
  have hcc : c₀ ≤ (c : ℤ) := by
    have := Int.toNat_le.mp hc
    omega
  set J := zeroIdeal Lc.toSubSystem s with hJ
  set F : SubSystem k x Ω := (Q.toSubSystem.twist Lc.toSubSystem).twist (twistSys k x (c : ℤ)) with hF
  set F' : SubSystem k x Ω := Q.toSubSystem.twist (twistSys k x (c : ℤ)) with hF'
  have hFI : ∀ I, F.sub I = Lc.sub I * F'.sub I := fun I => by
    simp only [hF, hF', SubSystem.twist_sub_eq_mul_of_line]
    ring
  have hsub : ∀ (K : Ideal (Poly k N)) (G : SubSystem k x Ω) (I : Chart x),
      (G.twist (idealSys x K)).sub I = idealMod K I * G.sub I :=
    fun K G I => SubSystem.twist_sub_eq_mul_of_line _ _ I
  have hsL : ∀ I, s ∈ Lc.sub I := fun I => SectionCount.Drop.Filt.Step.mem_secs_iff'.mp hs I
  have hsI : ∀ I, s ∈ idealMod J I * Lc.sub I := fun I => mem_idealMod_zeroIdeal_mul Lc I (hsL I)
  have hmono : ∀ {K₁ K₂ : Ideal (Poly k N)}, K₁ ≤ K₂ → ∀ I, idealMod (x := x) K₁ I ≤ idealMod K₂ I := by
    intro K₁ K₂ h I
    refine Submodule.span_mono ?_
    rintro _ ⟨f, t, d, hf, ht, hfd, htd, rfl⟩
    exact ⟨f, t, d, h hf, ht, hfd, htd, rfl⟩

  have hgK' : ∀ I, ∀ y ∈ F'.sub I, s * y ∈ (F.twist (idealSys x (pp ⊔ J))).sub I := by
    intro I y hy
    rw [hsub, hFI, ← mul_assoc]
    exact mul_le_mul' (mul_le_mul' (hmono le_sup_right I) le_rfl) le_rfl
      (Submodule.mul_mem_mul (hsI I) hy)

  have hJp : ∃ f ∈ J, f ∉ pp := by
    by_contra hcon
    push Not at hcon
    apply hI₀
    rw [hsub]
    exact mul_le_mul' (hmono (fun f hf => hcon f hf) I₀) le_rfl (hsI I₀)

  have hU : ∀ I, ∀ y ∈ F'.sub I, s * y ∈ (F.twist (idealSys x pp)).sub I →
      y ∈ (F'.twist (idealSys x pp)).sub I := by
    intro I y hy hsy
    refine SectionMulInj.proof k Ω N x pp hW.isPrime hW.homog hW.le Lc
      (Q.tensorProd (twistBundle k x (c : ℤ))) s hJp I y hy ?_
    rw [hsub, SubSystem.twist_sub_eq_mul_of_line]
    rw [hsub, hFI] at hsy
    exact hsy
  have hC : ∀ I, ∀ y ∈ (F'.twist (idealSys x pp)).sub I, s * y ∈ (F.twist (idealSys x pp)).sub I := by
    intro I y hy
    rw [hsub] at hy
    rw [hsub, hFI, mul_left_comm]
    exact Submodule.mul_mem_mul (hsL I) hy
  have hE : ∀ z ∈ (F.twist (idealSys x (pp ⊔ J))).secs, ∀ I,
      ∃ y ∈ F'.sub I, z - s * y ∈ (F.twist (idealSys x pp)).sub I := by
    intro z hz I
    have hzI := SectionCount.Drop.Filt.Step.mem_secs_iff'.mp hz I
    rw [hsub, hFI, ← mul_assoc] at hzI
    have h1 := mul_le_mul' (idealMod_sup_mul_le Lc s hW.homog I) le_rfl hzI
    rw [Submodule.sup_mul] at h1
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp h1
    obtain ⟨q, hq, rfl⟩ := Submodule.mem_span_singleton_mul.mp hb
    refine ⟨q, hq, ?_⟩
    rw [add_sub_cancel_right, hsub, hFI, ← mul_assoc]
    exact ha

  have hWV : ∀ z, z ∈ (F.twist (idealSys x pp)).secs → z ∈ (F.twist (idealSys x (pp ⊔ J))).secs := by
    intro z hz
    refine SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I => ?_
    have h1 := SectionCount.Drop.Filt.Step.mem_secs_iff'.mp hz I
    rw [hsub] at h1 ⊢
    exact mul_le_mul' (hmono le_sup_left I) le_rfl h1
  have hVH : ∀ z, z ∈ (F.twist (idealSys x (pp ⊔ J))).secs → z ∈ F.secs := fun z hz =>
    SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I =>
      SurjectiveClosed.twist_idealSys_le F _ I (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp hz I)
  have hgsec : ∀ y ∈ F'.secs, s * y ∈ (F.twist (idealSys x (pp ⊔ J))).secs := fun y hy =>
    SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I =>
      hgK' I y (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp hy I)

  have hlift : ∀ z ∈ (F.twist (idealSys x (pp ⊔ J))).secs,
      ∃ t ∈ F'.secs, z - s * t ∈ (F.twist (idealSys x pp)).secs := by
    intro z hz
    choose y hy hys using hE z hz
    have hcomp : ∀ (I₁ I₂ : Chart x), I₁.1 ⊆ I₂.1 →
        y I₁ - y I₂ ∈ (F'.twist (idealSys x pp)).sub I₂ := by
      intro I₁ I₂ h
      refine hU I₂ _ (sub_mem (F'.mono I₁ I₂ h _ (hy I₁)) (hy I₂)) ?_
      have h1 := sub_mem (hys I₂) ((F.twist (idealSys x pp)).mono I₁ I₂ h _ (hys I₁))
      convert h1 using 1
      ring
    obtain ⟨t, ht, htI⟩ := hc₀ _ hcc y hy hcomp
    refine ⟨t, ht, SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I => ?_⟩
    have h1 := add_mem (hys I) (hC I _ (neg_mem (htI I)))
    convert h1 using 1
    ring

  set H := F.secs with hH
  set H' := F'.secs with hH'
  set A := ((F.twist (idealSys x pp)).secs).comap H.subtype with hA
  set B := ((F.twist (idealSys x (pp ⊔ J))).secs).comap H.subtype with hB
  set P := ((F'.twist (idealSys x pp)).secs).comap H'.subtype with hP
  have hAB : A ≤ B := fun z hz => Submodule.mem_comap.mpr (hWV _ (Submodule.mem_comap.mp hz))
  let μ0 : H' →ₗ[k] H := (LinearMap.mulLeft k s).restrict (p := H') (q := H)
    (fun y hy => hVH _ (hgsec y hy))
  let μ : H' →ₗ[k] H ⧸ A := A.mkQ ∘ₗ μ0
  have hμ : ∀ y : H', y ∈ P ↔ μ y = 0 := by
    intro y
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, Submodule.mem_comap]
    change (y : Ω) ∈ _ ↔ s * (y : Ω) ∈ _
    constructor
    · intro h
      exact SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I =>
        hC I _ (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp h I)
    · intro h
      exact SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I =>
        hU I _ (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp y.2 I)
          (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp h I)
  let μb : (H' ⧸ P) →ₗ[k] H ⧸ A := P.liftQ μ (fun y hy => (hμ y).mp hy)
  have hinj : Function.Injective μb := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ (fun y hy => (hμ y).mpr hy)
  let π : (H ⧸ A) →ₗ[k] H ⧸ B := Submodule.factor hAB
  have hsurj : Function.Surjective π := by
    intro z
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective B z
    exact ⟨A.mkQ m, rfl⟩
  have hex : Function.Exact μb π := by
    intro z
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective A z
    change B.mkQ m = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    constructor
    · intro hm
      obtain ⟨t, ht, hst⟩ := hlift _ hm
      refine ⟨P.mkQ ⟨t, ht⟩, ?_⟩
      change A.mkQ (μ0 ⟨t, ht⟩) = A.mkQ m
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap]
      change s * t - (m : Ω) ∈ _
      have h1 := neg_mem hst
      convert h1 using 1
      rw [neg_sub]
      rfl
    · rintro ⟨v, hv⟩
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective P v
      change A.mkQ (μ0 y) = A.mkQ m at hv
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap] at hv
      change s * (y : Ω) - m ∈ _ at hv
      change (m : Ω) ∈ _
      have h1 := sub_mem (hgsec _ y.2) (hWV _ hv)
      convert h1 using 1
      ring
  have hlen := Module.length_eq_add_of_exact μb π hinj hsurj hex

  have hx : x ≠ 0 := by
    obtain ⟨i, hi⟩ := I₀.2.1
    intro h0
    exact (mem_support x).mp (I₀.2.2 hi) (by simp [h0])
  have hfin : Module.length k (H ⧸ A) ≠ ⊤ := by
    have : Module.Finite k H :=
      (hFS k Ω N x ((Q.tensorProd Lc).tensorProd (twistBundle k x (c : ℤ))) hx).1
    exact Module.length_ne_top
  have hB' : Module.length k (H ⧸ B) ≠ ⊤ := fun h => hfin (by rw [hlen, h, add_top])
  have hP' : Module.length k (H' ⧸ P) ≠ ⊤ := fun h => hfin (by rw [hlen, h, top_add])
  change ((Module.length k (H ⧸ A)).toNat : ℤ) - ((Module.length k (H' ⧸ P)).toNat : ℤ) =
    ((Module.length k (H ⧸ B)).toNat : ℤ)
  rw [hlen, ENat.toNat_add hP' hB']
  push_cast
  ring

end CutRestrLenExact

end

end GroundTheory.Heights₂.Heights.Kleiman
