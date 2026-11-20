import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.LocalQuotientRank
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.LocalLengthFraction

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthAverage

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FreeQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.QuotShiftPfH
  ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthFraction
open scoped TensorProduct

variable {K K₁ V : Type} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Establish `h1 : algebraMap K K₁ (algebraMap (𝓞 K) K a) = algebraMap (𝓞 K₁) K₁ (algebraMap (𝓞 K) (𝓞 K₁) a)` using `by first`. Consider the case `rfl`. Consider the case `simp [← IsScalarTower.algebraMap_apply]`. Rewrite using `[h1]`. Use `first`.

Consider the case `exact w.valuation_le_one _`. Consider the case `exact w.valuation_le_one K₁ _`. Consider the case `simp [Rv, HeightOneSpectrum.valuationSubringAtPrime, HeightOneSpectrum.valuation_le_one]`.
-/
lemma algebraMap_mem_Rv (w : HeightOneSpectrum (𝓞 K₁)) (a : 𝓞 K) :
    algebraMap K K₁ (algebraMap (𝓞 K) K a) ∈ Rv K₁ w := by
  have h1 : algebraMap K K₁ (algebraMap (𝓞 K) K a) =
      algebraMap (𝓞 K₁) K₁ (algebraMap (𝓞 K) (𝓞 K₁) a) := by
    first
      | rfl
      | simp [← IsScalarTower.algebraMap_apply]
  rw [h1]
  first
    | exact w.valuation_le_one _
    | exact w.valuation_le_one K₁ _
    | simp [Rv, HeightOneSpectrum.valuationSubringAtPrime, HeightOneSpectrum.valuation_le_one]

/- English proof (translation)
Set `inst : Module (Rv K₁ w) (K₁ ⊗[K] V)` to `Module.compHom _ (Rv K₁ w).subtype`. Establish `hst : IsScalarTower (Rv K₁ w) K₁ (K₁ ⊗[K] V)` using `⟨fun r a x => mul_smul (r : K₁) a x⟩`. Establish `hsmul : ∀ (r : Rv K₁ w) (x : K₁ ⊗[K] V), r • x = (r : K₁) • x` using `fun r x => rfl`. Use `set Mw : Submodule (Rv K₁ w) (K₁ ⊗[K] V) := Submodule.span (Rv K₁ w) ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (M.restrictScalars ℤ : Set V)) with hMwdef`. Establish `hgen : ∀ m ∈ M, (1 : K₁) ⊗ₜ[K] m ∈ Mw` using `fun m hm => Submodule.subset_span ⟨m, hm, rfl⟩`.

Establish `hsc : ∀ (a : 𝓞 K) (m : V), (1 : K₁) ⊗ₜ[K] (a • m) = (⟨algebraMap K K₁ (algebraMap (𝓞 K) K a), algebraMap_mem_Rv w a⟩ : Rv K₁ w) • ((1 : K₁) ⊗ₜ[K] m)`. Introduce `a m`. Rewrite using `[hsmul, ← algebraMap_smul K a m, TensorProduct.tmul_smul, ← algebraMap_smul K₁ (algebraMap (𝓞 K) K a)]`. Establish `hMwFG : Mw.FG`. Take `⟨G, hG⟩` from `hM`.

Use `⟨G.image (fun a : V => (1 : K₁) ⊗ₜ[K] a), ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.coe_image]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨g, hg, rfl⟩`.

Conclude with `hgen g (hG ▸ Submodule.subset_span hg)`. Rewrite using `[hMwdef, Submodule.span_le]`. Introduce and unpack `_ ⟨m, hm, rfl⟩`. Establish `hm' : m ∈ Submodule.span (𝓞 K) (G : Set V)` using `by rw [hG]; exact hm`. Use `clear hm`.

Use `show (1 : K₁) ⊗ₜ[K] m ∈ _`. Proceed by induction on `hm' using Submodule.span_induction with`. Consider the case `mem g hg => exact Submodule.subset_span ⟨g, hg, rfl⟩`. Consider the case `zero => rw [TensorProduct.tmul_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add a b _ _ ha hb => rw [TensorProduct.tmul_add]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul a b _ hb => rw [hsc]`. Conclude with `Submodule.smul_mem _ _ hb`. Establish `hMspan : Submodule.span K₁ (Mw : Set (K₁ ⊗[K] V)) = ⊤`.

Rewrite using `[eq_top_iff, ← span_tmul_one (K := K) (K₁ := K₁) (V := V), Submodule.span_le]`. Introduce and unpack `_ ⟨v, rfl⟩`. Establish `hr : (Set.range fun m : M => (m : V)) = (M : Set V)` using `Subtype.range_coe`. Establish `hv : v ∈ Submodule.span K (Set.range fun m : M => (m : V))`. Rewrite using `[hr, hspan]`.

Discharge the goal by the elementary cases of `trivial`. Establish `h1` using `tmul_mem_span (K₁ := K₁) (fun m : M => (m : V)) hv`. Use `Submodule.span_le.mpr ?_ h1` and prove the remaining obligations. Introduce and unpack `_ ⟨m, rfl⟩`. Conclude with `Submodule.subset_span (hgen m m.2)`.

Establish `hint' : ∀ i, ∀ y ∈ Mw, c i y ≠ 0 → -β ≤ (ordAt w (c i y) : ℝ) + s i`. Introduce `i y hy hne`. Establish `hball : w.valuation K₁ (c i y) ≤ WithZero.exp (-⌈-β - s i⌉)` using `by clear hne`. Rewrite `hy` using `[hMwdef]`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem z hz`. Take `⟨m, hm, rfl⟩` from `hz`. Distinguish the cases in `h0 : c i ((1 : K₁) ⊗ₜ[K] m) = 0`. Rewrite using `[h0, map_zero]`. Conclude with `zero_le`.

Establish `h1` using `hint i m hm h0`. Rewrite using `[val_eq_exp w h0, WithZero.exp_le_exp, neg_le_neg_iff, Int.ceil_le]`. Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `zero => rw [map_zero, map_zero]`. Conclude with `zero_le`.

Consider the case `add a b _ _ ha hb`. Rewrite using `[map_add]`. Conclude with `le_trans (Valuation.map_add _ _ _) (max_le ha hb)`. Consider the case `smul r a _ ha => show w.valuation K₁ (c i ((r : K₁) • a)) ≤ _`. Rewrite using `[map_smul, smul_eq_mul, map_mul]`.

Conclude with `le_trans (mul_le_of_le_one_left' ((mem_Rv_iff w _).mp r.2)) ha`. Rewrite `hball` using `[val_eq_exp w hne, WithZero.exp_le_exp, neg_le_neg_iff, Int.ceil_le]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcP : ∀ i, ∀ x ∈ Submodule.span K₁ ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (W : Set V)), c i x = 0` using `fun i x hx => (hc x).mpr hx i`. Take `⟨n, hn1, hn2⟩` from `@local_len K₁ _ _ w (K₁ ⊗[K] V) _ _ _ inst hst hL _ Mw hMwFG hMspan _ (quot_finrank M hM hspan W θ hθ) (fun j => (1 : K₁) ⊗ₜ[K] ((θ j : M) : V)) (fun j => hgen _ (θ j).2) (fun i => c i) hcP s β hint' (detCT_ne_zero M hM hspan W θ hθ c hc)`.

Conclude with `⟨n, hn1, hn2⟩`.
-/
theorem lenW_bound (hL : QuotLocalStatement) (M : Submodule (𝓞 K) V) (hM : M.FG)
    (hspan : Submodule.span K (M : Set V) = ⊤) (W : Submodule K V)
    (θ : Fin (finrank (𝓞 K) (QuotMW M W)) → M)
    (hθ : Submodule.span K (Set.range fun j => ((θ j : M) : V)) ⊔ W = ⊤)
    (c : Fin (finrank (𝓞 K) (QuotMW M W)) → Module.Dual K₁ (K₁ ⊗[K] V))
    (hc : ∀ x : K₁ ⊗[K] V, (∀ i, c i x = 0) ↔
      x ∈ Submodule.span K₁ ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (W : Set V)))
    (w : HeightOneSpectrum (𝓞 K₁)) (s : Fin (finrank (𝓞 K) (QuotMW M W)) → ℝ) (β : ℝ)
    (hint : ∀ i, ∀ m ∈ M, c i ((1 : K₁) ⊗ₜ[K] m) ≠ 0 →
      -β ≤ (ordAt w (c i ((1 : K₁) ⊗ₜ[K] m)) : ℝ) + s i) :
    ∃ n : ℕ, lenW w M W θ = n ∧
      (n : ℝ) ≤ (ordAt w (detCT c θ) : ℝ) + ∑ i, s i +
        (finrank (𝓞 K) (QuotMW M W) : ℝ) * β := by
  classical
  let inst : Module (Rv K₁ w) (K₁ ⊗[K] V) := Module.compHom _ (Rv K₁ w).subtype
  have hst : IsScalarTower (Rv K₁ w) K₁ (K₁ ⊗[K] V) :=
    ⟨fun r a x => mul_smul (r : K₁) a x⟩
  have hsmul : ∀ (r : Rv K₁ w) (x : K₁ ⊗[K] V), r • x = (r : K₁) • x := fun r x => rfl
  set Mw : Submodule (Rv K₁ w) (K₁ ⊗[K] V) := Submodule.span (Rv K₁ w)
    ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (M.restrictScalars ℤ : Set V)) with hMwdef
  have hgen : ∀ m ∈ M, (1 : K₁) ⊗ₜ[K] m ∈ Mw := fun m hm => Submodule.subset_span ⟨m, hm, rfl⟩
  have hsc : ∀ (a : 𝓞 K) (m : V), (1 : K₁) ⊗ₜ[K] (a • m) =
      (⟨algebraMap K K₁ (algebraMap (𝓞 K) K a), algebraMap_mem_Rv w a⟩ : Rv K₁ w) •
        ((1 : K₁) ⊗ₜ[K] m) := by
    intro a m
    rw [hsmul, ← algebraMap_smul K a m, TensorProduct.tmul_smul,
      ← algebraMap_smul K₁ (algebraMap (𝓞 K) K a)]
  have hMwFG : Mw.FG := by
    obtain ⟨G, hG⟩ := hM
    refine ⟨G.image (fun a : V => (1 : K₁) ⊗ₜ[K] a), ?_⟩
    rw [Finset.coe_image]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨g, hg, rfl⟩
      exact hgen g (hG ▸ Submodule.subset_span hg)
    · rw [hMwdef, Submodule.span_le]
      rintro _ ⟨m, hm, rfl⟩
      have hm' : m ∈ Submodule.span (𝓞 K) (G : Set V) := by rw [hG]; exact hm
      clear hm
      show (1 : K₁) ⊗ₜ[K] m ∈ _
      induction hm' using Submodule.span_induction with
      | mem g hg => exact Submodule.subset_span ⟨g, hg, rfl⟩
      | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
      | add a b _ _ ha hb => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ ha hb
      | smul a b _ hb => rw [hsc]; exact Submodule.smul_mem _ _ hb
  have hMspan : Submodule.span K₁ (Mw : Set (K₁ ⊗[K] V)) = ⊤ := by
    rw [eq_top_iff, ← span_tmul_one (K := K) (K₁ := K₁) (V := V), Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    have hr : (Set.range fun m : M => (m : V)) = (M : Set V) := Subtype.range_coe
    have hv : v ∈ Submodule.span K (Set.range fun m : M => (m : V)) := by
      rw [hr, hspan]; trivial
    have h1 := tmul_mem_span (K₁ := K₁) (fun m : M => (m : V)) hv
    refine Submodule.span_le.mpr ?_ h1
    rintro _ ⟨m, rfl⟩
    exact Submodule.subset_span (hgen m m.2)
  have hint' : ∀ i, ∀ y ∈ Mw, c i y ≠ 0 → -β ≤ (ordAt w (c i y) : ℝ) + s i := by
    intro i y hy hne
    have hball : w.valuation K₁ (c i y) ≤ WithZero.exp (-⌈-β - s i⌉) := by
      clear hne
      rw [hMwdef] at hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨m, hm, rfl⟩ := hz
        by_cases h0 : c i ((1 : K₁) ⊗ₜ[K] m) = 0
        · rw [h0, map_zero]; exact zero_le
        · have h1 := hint i m hm h0
          rw [val_eq_exp w h0, WithZero.exp_le_exp, neg_le_neg_iff, Int.ceil_le]
          linarith
      | zero => rw [map_zero, map_zero]; exact zero_le
      | add a b _ _ ha hb =>
        rw [map_add]
        exact le_trans (Valuation.map_add _ _ _) (max_le ha hb)
      | smul r a _ ha =>
        show w.valuation K₁ (c i ((r : K₁) • a)) ≤ _
        rw [map_smul, smul_eq_mul, map_mul]
        exact le_trans (mul_le_of_le_one_left' ((mem_Rv_iff w _).mp r.2)) ha
    rw [val_eq_exp w hne, WithZero.exp_le_exp, neg_le_neg_iff, Int.ceil_le] at hball
    linarith
  have hcP : ∀ i, ∀ x ∈ Submodule.span K₁ ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (W : Set V)),
      c i x = 0 := fun i x hx => (hc x).mpr hx i
  obtain ⟨n, hn1, hn2⟩ := @local_len K₁ _ _ w (K₁ ⊗[K] V) _ _ _ inst hst hL _ Mw hMwFG hMspan _ (quot_finrank M hM hspan W θ hθ)
    (fun j => (1 : K₁) ⊗ₜ[K] ((θ j : M) : V)) (fun j => hgen _ (θ j).2) (fun i => c i) hcP s β
    hint' (detCT_ne_zero M hM hspan W θ hθ c hc)
  exact ⟨n, hn1, hn2⟩

/- English proof (translation)
Set `S` to `la.asIdeal.primesOver (𝓞 K₁)`. Establish `hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 K₁))` using `FaithfulSMul.algebraMap_injective _ _`. Set `E : {w : HeightOneSpectrum (𝓞 K₁) // LiesOver w la} ≃ S` to `{ toFun := fun w => ⟨w.1.asIdeal, w.1.isPrime, ⟨w.2.symm⟩⟩ invFun := fun q => ⟨⟨q.1, q.2.1, fun h0 => la.ne_bot (by`. Establish `h1 : la.asIdeal = q.1.comap (algebraMap (𝓞 K) (𝓞 K₁))` using `q.2.2.over`. Rewrite using `[h1, h0]`.

Conclude with `Ideal.comap_bot_of_injective _ hinj)⟩, q.2.2.over.symm⟩`. Use `left_inv := fun w => rfl`. Use `right_inv := fun q => rfl }`. Establish `hsumN : ∑ q : S, q.1.ramificationIdx (𝓞 K) * q.1.inertiaDeg (𝓞 K) = Module.finrank K K₁`. Rewrite using `[Ideal.sum_ramification_inertia_eq_finrank, IsFractionRing.finrank_eq (𝓞 K) K (𝓞 K₁) K₁]`.

Establish `hn : 0 < Module.finrank K K₁` using `Module.finrank_pos`. Establish `hne : Nonempty S`. Assume the negation of the conclusion as `hS`. Rewrite `hS` using `[not_nonempty_iff]`. Rewrite `hsumN` using `[Finset.univ_eq_empty, Finset.sum_empty]`.

Use linear arithmetic over natural numbers and integers. Take `⟨q0⟩` from `hne`. Take `⟨n0, hn0, -⟩` from `h (E.symm q0).1 (E.symm q0).2`. Establish `he0 : 0 < (E.symm q0).1.asIdeal.ramificationIdx (𝓞 K)` using `Ideal.ramificationIdx_pos _ _`. Choose the witnesses or unpack the hypotheses as in `⟨ℓ, rfl⟩ : ∃ ℓ : ℕ, L = ℓ := by`.

Proceed by induction on `L using ENat.recTopCoe with`. Consider the case `top`. It suffices to derive a contradiction. Rewrite `hn0` using `[ENat.mul_top (by exact_mod_cast he0.ne')]`. Conclude with `ENat.top_ne_natCast n0 hn0`.

Consider the case `coe ℓ => exact ⟨ℓ, rfl⟩`. Use `⟨ℓ, rfl, ?_⟩` and prove the remaining obligations. Establish `hq : ∀ q : S, (q.1.ramificationIdx (𝓞 K) : ℝ) * ℓ ≤ (ordAt (E.symm q).1 D : ℝ) + t (E.symm q).1 + ρ * ((q.1.ramificationIdx (𝓞 K) : ℝ) * B)`. Introduce `q`. Take `⟨n, hn1, hn2⟩` from `h (E.symm q).1 (E.symm q).2`.

Establish `h1 : ((q.1.ramificationIdx (𝓞 K) * ℓ : ℕ) : ℕ∞) = n` using `by push_cast; exact hn1`. Establish `h2 : q.1.ramificationIdx (𝓞 K) * ℓ = n` using `by exact_mod_cast h1`. Establish `h3 : (q.1.ramificationIdx (𝓞 K) : ℝ) * ℓ = n` using `by exact_mod_cast h2`. Rewrite using `[h3]`. Conclude with `hn2`.

Establish `hsum : ∑ q : S, (q.1.inertiaDeg (𝓞 K) : ℝ) * ((q.1.ramificationIdx (𝓞 K) : ℝ) * ℓ) ≤ ∑ q : S, (q.1.inertiaDeg (𝓞 K) : ℝ) * ((ordAt (E.symm q).1 D : ℝ) + t (E.symm q).1 + ρ * ((q.1.ramificationIdx (𝓞 K) : ℝ) * B))` using `Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (hq q) (Nat.cast_nonneg _)`. Establish `hN : ∑ q : S, (q.1.ramificationIdx (𝓞 K) : ℝ) * (q.1.inertiaDeg (𝓞 K) : ℝ) = Module.finrank K K₁` using `by exact_mod_cast hsumN`. Establish `hfs : (∑ᶠ w : {w : HeightOneSpectrum (𝓞 K₁) // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * ((ordAt w.1 D : ℝ) + t w.1)) = ∑ q : S, (q.1.inertiaDeg (𝓞 K) : ℝ) * ((ordAt (E.symm q).1 D : ℝ) + t (E.symm q).1)`. Rewrite using `[← finsum_comp_equiv E.symm, finsum_eq_sum_of_fintype]`. Both sides reduce to the same expression.

Establish `hLsum : ∑ q : S, (q.1.inertiaDeg (𝓞 K) : ℝ) * ((q.1.ramificationIdx (𝓞 K) : ℝ) * ℓ) = ℓ * Module.finrank K K₁`. Rewrite using `[← hN, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun q _ => by ring`. Establish `hRsum : ∑ q : S, (q.1.inertiaDeg (𝓞 K) : ℝ) * ((ordAt (E.symm q).1 D : ℝ) + t (E.symm q).1 + ρ * ((q.1.ramificationIdx (𝓞 K) : ℝ) * B)) = ∑ q : S, (q.1.inertiaDeg (𝓞 K) : ℝ) * ((ordAt (E.symm q).1 D : ℝ) + t (E.symm q).1) + ρ * B * Module.finrank K K₁`. Rewrite using `[← hN, Finset.mul_sum, ← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl fun q _ => by ring`. Rewrite `hsum` using `[hLsum, hRsum]`. Establish `hnpos : (0 : ℝ) < Module.finrank K K₁` using `by exact_mod_cast hn`. Rewrite using `[hfs, div_add' _ _ _ hnpos.ne', le_div_iff₀ hnpos]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem average (la : HeightOneSpectrum (𝓞 K)) (L : ℕ∞) (D : K₁)
    (t : HeightOneSpectrum (𝓞 K₁) → ℝ) (ρ : ℕ) (B : ℝ)
    (h : ∀ w : HeightOneSpectrum (𝓞 K₁), LiesOver w la → ∃ n : ℕ,
      (w.asIdeal.ramificationIdx (𝓞 K) : ℕ∞) * L = n ∧
      (n : ℝ) ≤ (ordAt w D : ℝ) + t w + ρ * ((w.asIdeal.ramificationIdx (𝓞 K) : ℝ) * B)) :
    ∃ ℓ : ℕ, L = ℓ ∧ (ℓ : ℝ) ≤ (∑ᶠ w : {w : HeightOneSpectrum (𝓞 K₁) // LiesOver w la},
        (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * ((ordAt w.1 D : ℝ) + t w.1)) /
        (Module.finrank K K₁ : ℝ) + ρ * B := by
  classical
  let S := la.asIdeal.primesOver (𝓞 K₁)
  have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 K₁)) :=
    FaithfulSMul.algebraMap_injective _ _
  let E : {w : HeightOneSpectrum (𝓞 K₁) // LiesOver w la} ≃ S :=
    { toFun := fun w => ⟨w.1.asIdeal, w.1.isPrime, ⟨w.2.symm⟩⟩
      invFun := fun q => ⟨⟨q.1, q.2.1, fun h0 => la.ne_bot (by
          have h1 : la.asIdeal = q.1.comap (algebraMap (𝓞 K) (𝓞 K₁)) := q.2.2.over
          rw [h1, h0]
          exact Ideal.comap_bot_of_injective _ hinj)⟩, q.2.2.over.symm⟩
      left_inv := fun w => rfl
      right_inv := fun q => rfl }
  have hsumN : ∑ q : S, q.1.ramificationIdx (𝓞 K) * q.1.inertiaDeg (𝓞 K) =
      Module.finrank K K₁ := by
    rw [Ideal.sum_ramification_inertia_eq_finrank, IsFractionRing.finrank_eq (𝓞 K) K (𝓞 K₁) K₁]
  have hn : 0 < Module.finrank K K₁ := Module.finrank_pos
  have hne : Nonempty S := by
    by_contra hS
    rw [not_nonempty_iff] at hS
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hsumN
    omega
  obtain ⟨q0⟩ := hne
  obtain ⟨n0, hn0, -⟩ := h (E.symm q0).1 (E.symm q0).2
  have he0 : 0 < (E.symm q0).1.asIdeal.ramificationIdx (𝓞 K) :=
    Ideal.ramificationIdx_pos _ _
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ : ℕ, L = ℓ := by
    induction L using ENat.recTopCoe with
    | top =>
      exfalso
      rw [ENat.mul_top (by exact_mod_cast he0.ne')] at hn0
      exact ENat.top_ne_natCast n0 hn0
    | coe ℓ => exact ⟨ℓ, rfl⟩
  refine ⟨ℓ, rfl, ?_⟩
  have hq : ∀ q : S, (q.1.ramificationIdx (𝓞 K) : ℝ) * ℓ ≤ (ordAt (E.symm q).1 D : ℝ) +
      t (E.symm q).1 + ρ * ((q.1.ramificationIdx (𝓞 K) : ℝ) * B) := by
    intro q
    obtain ⟨n, hn1, hn2⟩ := h (E.symm q).1 (E.symm q).2
    have h1 : ((q.1.ramificationIdx (𝓞 K) * ℓ : ℕ) : ℕ∞) = n := by push_cast; exact hn1
    have h2 : q.1.ramificationIdx (𝓞 K) * ℓ = n := by exact_mod_cast h1
    have h3 : (q.1.ramificationIdx (𝓞 K) : ℝ) * ℓ = n := by exact_mod_cast h2
    rw [h3]
    exact hn2
  have hsum : ∑ q : S, (q.1.inertiaDeg (𝓞 K) : ℝ) * ((q.1.ramificationIdx (𝓞 K) : ℝ) * ℓ) ≤
      ∑ q : S, (q.1.inertiaDeg (𝓞 K) : ℝ) * ((ordAt (E.symm q).1 D : ℝ) + t (E.symm q).1 +
        ρ * ((q.1.ramificationIdx (𝓞 K) : ℝ) * B)) :=
    Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (hq q) (Nat.cast_nonneg _)
  have hN : ∑ q : S, (q.1.ramificationIdx (𝓞 K) : ℝ) * (q.1.inertiaDeg (𝓞 K) : ℝ) =
      Module.finrank K K₁ := by exact_mod_cast hsumN
  have hfs : (∑ᶠ w : {w : HeightOneSpectrum (𝓞 K₁) // LiesOver w la},
      (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * ((ordAt w.1 D : ℝ) + t w.1)) =
      ∑ q : S, (q.1.inertiaDeg (𝓞 K) : ℝ) * ((ordAt (E.symm q).1 D : ℝ) + t (E.symm q).1) := by
    rw [← finsum_comp_equiv E.symm, finsum_eq_sum_of_fintype]
    rfl
  have hLsum : ∑ q : S, (q.1.inertiaDeg (𝓞 K) : ℝ) * ((q.1.ramificationIdx (𝓞 K) : ℝ) * ℓ) =
      ℓ * Module.finrank K K₁ := by
    rw [← hN, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  have hRsum : ∑ q : S, (q.1.inertiaDeg (𝓞 K) : ℝ) * ((ordAt (E.symm q).1 D : ℝ) +
      t (E.symm q).1 + ρ * ((q.1.ramificationIdx (𝓞 K) : ℝ) * B)) =
      ∑ q : S, (q.1.inertiaDeg (𝓞 K) : ℝ) * ((ordAt (E.symm q).1 D : ℝ) + t (E.symm q).1) +
        ρ * B * Module.finrank K K₁ := by
    rw [← hN, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [hLsum, hRsum] at hsum
  have hnpos : (0 : ℝ) < Module.finrank K K₁ := by exact_mod_cast hn
  rw [hfs, div_add' _ _ _ hnpos.ne', le_div_iff₀ hnpos]
  linarith

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthAverage
