import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitO
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitR
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitV

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex
open scoped InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Simplify using `[IR]`.
-/
theorem IR_bot {dim : (E →+* ℂ) → ℕ} : IR (⊥ : Submodule ℤ (Vsp dim)) = ⊥ := by
  simp [IR]

/- English proof (translation)
Establish `hIR : IR (⊥ : Submodule ℤ (Vsp X.dim)) = ⊥` using `IR_bot`. Establish `h0 : Module.finrank ℝ (IR (⊥ : Submodule ℤ (Vsp X.dim))) = 0`. Rewrite using `[hIR]`. Conclude with `finrank_bot ℝ (Vsp X.dim)`. Establish `h' : ¬ X.la1 < th (E` using `E) P.q P.R0 := h`.

Establish `hph : P.ph = 0`. Unfold `Par.ph PT.ph`. Rewrite using `[if_neg h']`. Use `{ le := bot_le sat := ?_ stable := ?_ iso := ?_ eps := ?_ rank := ⟨0, Nat.zero_le _, by rw [h0, mul_zero]⟩ ne_bot := iff_of_false (fun h'' => h'' rfl) h thick := ?_ sep := ?_ u1 := ?_ u2 := ?_ }` and prove the remaining obligations. Introduce `x _ k hk hx`.

Rewrite `hx`, the goal using `[Submodule.mem_bot]`. Rewrite `hx` using `[← Int.cast_smul_eq_zsmul ℂ]`. Conclude with `(smul_eq_zero.mp hx).resolve_left (by exact_mod_cast hk)`. Introduce `α x hx`. Rewrite `hx`, the goal using `[Submodule.mem_bot]`.

Substitute `hx` using the available equality. Use extensionality with `i`. Simplify using `[act]`. Introduce `x hx y hy`. Rewrite `hx`, `hy` using `[Submodule.mem_bot]`.

Substitute `hx hy` using the available equality. Simplify using `[Hf]`. Introduce `x hx`. Rewrite `hx` using `[Submodule.mem_bot]`. Substitute `hx` using the available equality.

Conclude with `X.eps_iso 0 (Submodule.zero_mem _) (fun α => by simp [Hf])`. Introduce `x hxL _ hx`. Rewrite `hx` using `[Submodule.mem_bot]`. Rewrite using `[hIR]`. Establish `hinf : Metric.infDist x ((⊥ : Submodule ℝ (Vsp X.dim)) : Set (Vsp X.dim)) = ‖x‖`.

Rewrite using `[Submodule.bot_coe, Metric.infDist_singleton, dist_zero_right]`. Rewrite using `[hinf]`. Establish `hle : X.la1 ≤ ‖x‖`. Unfold `PT.la1`. Apply `csInf_le` to reduce the goal to its premises.

Conclude with `⟨0, fun t ⟨y, _, _, ht⟩ => by rw [ht]; exact norm_nonneg y⟩`. Conclude with `⟨x, hxL, hx, rfl⟩`. Conclude with `(not_lt.mp h).trans hle`. Introduce `x _ u hu hu0`. It suffices to derive a contradiction.

Apply `hu0` to reduce the goal to its premises. Unfold `IsU at hu`. Establish `hu1` using `hu.1`. Rewrite `hu1` using `[hIR, Submodule.mem_bot]`. Conclude with `hu1`.

Use `haveI : IsEmpty (Fin (Module.finrank ℝ (IR (⊥ : Submodule ℤ (Vsp X.dim))))) := by`. Rewrite using `[h0]`. Use `infer_instance`. Conclude with `⟨fun _ => 0, fun _ => 0, fun j => isEmptyElim j, linearIndependent_empty_type, fun j => isEmptyElim j⟩`. Introduce `k x u _ _`.

Rewrite using `[hph]`. Conclude with `Finset.sum_nonneg fun j _ => by positivity`.
-/
theorem split_bot (X : PT E) {DF : ℕ} (P : Par X DF) (h : ¬ X.la1 < P.th) : IsSplit P ⊥ := by
  have hIR : IR (⊥ : Submodule ℤ (Vsp X.dim)) = ⊥ := IR_bot
  have h0 : Module.finrank ℝ (IR (⊥ : Submodule ℤ (Vsp X.dim))) = 0 := by
    rw [hIR]; exact finrank_bot ℝ (Vsp X.dim)
  have h' : ¬ X.la1 < th (E := E) P.q P.R0 := h
  have hph : P.ph = 0 := by
    unfold Par.ph PT.ph
    rw [if_neg h']
  refine
    { le := bot_le
      sat := ?_
      stable := ?_
      iso := ?_
      eps := ?_
      rank := ⟨0, Nat.zero_le _, by rw [h0, mul_zero]⟩
      ne_bot := iff_of_false (fun h'' => h'' rfl) h
      thick := ?_
      sep := ?_
      u1 := ?_
      u2 := ?_ }
  · intro x _ k hk hx
    rw [Submodule.mem_bot] at hx ⊢
    rw [← Int.cast_smul_eq_zsmul ℂ] at hx
    exact (smul_eq_zero.mp hx).resolve_left (by exact_mod_cast hk)
  · intro α x hx
    rw [Submodule.mem_bot] at hx ⊢
    subst hx
    ext i
    simp [act]
  · intro x hx y hy
    rw [Submodule.mem_bot] at hx hy
    subst hx hy
    simp [Hf]
  · intro x hx
    rw [Submodule.mem_bot] at hx
    subst hx
    exact X.eps_iso 0 (Submodule.zero_mem _) (fun α => by simp [Hf])
  · intro x hxL _ hx
    rw [Submodule.mem_bot] at hx
    rw [hIR]
    have hinf : Metric.infDist x ((⊥ : Submodule ℝ (Vsp X.dim)) : Set (Vsp X.dim)) = ‖x‖ := by
      rw [Submodule.bot_coe, Metric.infDist_singleton, dist_zero_right]
    rw [hinf]
    have hle : X.la1 ≤ ‖x‖ := by
      unfold PT.la1
      apply csInf_le
      · exact ⟨0, fun t ⟨y, _, _, ht⟩ => by rw [ht]; exact norm_nonneg y⟩
      · exact ⟨x, hxL, hx, rfl⟩
    exact (not_lt.mp h).trans hle
  · intro x _ u hu hu0
    exfalso
    apply hu0
    unfold IsU at hu
    have hu1 := hu.1
    rw [hIR, Submodule.mem_bot] at hu1
    exact hu1
  · haveI : IsEmpty (Fin (Module.finrank ℝ (IR (⊥ : Submodule ℤ (Vsp X.dim))))) := by
      rw [h0]; infer_instance
    exact ⟨fun _ => 0, fun _ => 0, fun j => isEmptyElim j, linearIndependent_empty_type,
      fun j => isEmptyElim j⟩
  · intro k x u _ _
    rw [hph]
    exact Finset.sum_nonneg fun j _ => by positivity

/- English proof (translation)
Establish `hcont : ContinuousAt (fun ε : ℝ => c / (a + ε) ^ 2) 0`. Apply `ContinuousAt.div continuousAt_const` to reduce the goal to its premises. Conclude with `((continuous_const.add continuous_id).pow 2).continuousAt`. Simplify using `using ha.ne'`. Establish `ht : Filter.Tendsto (fun ε : ℝ => c / (a + ε) ^ 2) (nhdsWithin 0 (Set.Ioi 0)) (nhds (c / a ^ 2))`.

Use `hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))` as an intermediate fact. Simplify using `using this`. Apply `le_of_tendsto ht` to reduce the goal to its premises. Use `filter_upwards [self_mem_nhdsWithin] with ε hε using h ε hε`.
-/
theorem le_of_forall_pos_div_sq {a c S : ℝ} (ha : 0 < a) (hc : 0 < c) (h : ∀ ε > 0, c / (a + ε) ^ 2 ≤ S) :
    c / a ^ 2 ≤ S := by
  have hcont : ContinuousAt (fun ε : ℝ => c / (a + ε) ^ 2) 0 := by
    apply ContinuousAt.div continuousAt_const
    · exact ((continuous_const.add continuous_id).pow 2).continuousAt
    · simpa using ha.ne'
  have ht : Filter.Tendsto (fun ε : ℝ => c / (a + ε) ^ 2) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (c / a ^ 2)) := by
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa using this
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε using h ε hε

/- English proof (translation)
Establish `key : u * la ≤ N + 1`. Establish `e : N / la + 1 / la = (N + 1) / la` using `by ring`. Rewrite `hu` using `[e]`. Establish `e2 : (N + 1) / la * la = N + 1` using `by field_simp`. Combine the equalities or inequalities in the displayed calculation.

Establish `hla2 : 0 < la ^ 2` using `by positivity`. Rewrite using `[le_div_iff₀ hla2]`. Establish `h2 : u * la ≤ d ^ 2` using `by nlinarith`. Establish `h3 : 0 ≤ u * la` using `mul_nonneg hu0 hla.le`. Use polynomial arithmetic with `[mul_le_mul h2 h2 h3 (by positivity : (0:ℝ) ≤ d ^ 2)]`.
-/
theorem sq_le_pow_four_div_sq {d N la u : ℝ} (hd : 2 ≤ d) (hN : N ≤ d) (hla : 0 < la) (hu0 : 0 ≤ u)
    (hu : u ≤ N / la + 1 / la) : u ^ 2 ≤ d ^ 4 / la ^ 2 := by
  have key : u * la ≤ N + 1 := by
    have e : N / la + 1 / la = (N + 1) / la := by ring
    rw [e] at hu
    have e2 : (N + 1) / la * la = N + 1 := by field_simp
    calc u * la ≤ (N + 1) / la * la := mul_le_mul_of_nonneg_right hu hla.le
      _ = N + 1 := e2
  have hla2 : 0 < la ^ 2 := by positivity
  rw [le_div_iff₀ hla2]
  have h2 : u * la ≤ d ^ 2 := by nlinarith
  have h3 : 0 ≤ u * la := mul_nonneg hu0 hla.le
  nlinarith [mul_le_mul h2 h2 h3 (by positivity : (0:ℝ) ≤ d ^ 2)]

/- English proof (translation)
Take `⟨n, ω, hω, hsp⟩` from `omega_exists' (E := E)`. Establish `hf1n : 1 ≤ PT.f E` using `le_trans (Nat.one_le_pow _ _ P.hm1) P.hmf`. Establish `hf1 : (1 : ℝ) ≤ PT.f E` using `by exact_mod_cast hf1n`. Establish `hrd` using `P.hrd`. Establish `hRR : (0 : ℝ) < RR (E` using `E) := by rw [RR]; positivity`.

Establish `hq : (0 : ℝ) < P.q` using `by exact_mod_cast P.hq`. Establish `hR0 : (0 : ℝ) < P.R0 ^ 2` using `by linarith [P.hR0.1]`. Use `set Ω := omStar (E := E) with hΩdef`. Establish `hΩ : 0 < Ω` using `by rw [hΩdef, omStar]; positivity`. Establish `hΩ2 : Ω ^ 2 = 4 * (PT.f E : ℝ) ^ 3 * PT.rd E ^ 2`.

Rewrite using `[hΩdef, omStar, mul_pow, mul_pow, ← Real.rpow_natCast ((PT.f E : ℝ) ^ ((3 : ℝ) / 2)), ← Real.rpow_mul (by positivity)]`. Evaluate the numerical expressions. Establish `hth2 : P.th ^ 2 = PT.f E * P.R0 ^ 2 * RR (E` using `E) ^ 3 / P.q := by`. Rewrite using `[Par.th, th, Real.sq_sqrt]`. Check the signs of the components of the expression.

Establish `hth : 0 < P.th`. Rewrite using `[Par.th, th]`. Apply `Real.sqrt_pos.2` to reduce the goal to its premises. Check the signs of the components of the expression. Establish `hd2n : 2 ≤ dstar (E` using `E) P.m := by`.

Rewrite using `[dstar]`. Use `P.hm1` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hd2 : (2 : ℝ) ≤ dstar (E` using `E) P.m := by exact_mod_cast hd2n`. Establish `hC1 : (dstar (E` using `E) P.m : ℝ) ^ 2 * Ω * P.th ^ 2 < 1 := P.C1`.

Establish `hΩth : Ω * P.th ^ 2 ≤ 1` using `by nlinarith [sq_nonneg P.th, hΩ]`. Take `⟨I, hI, hmax⟩` from `exists_maximal X ω hΩ hth hΩth hω hsp`. Take `⟨τ, hτ⟩` from `P.hm`. Establish `hr : 1 ≤ X.r`. Use `P.hfr` as an intermediate fact.

Break down `Nat.eq_zero_or_pos X.r with h0 | h0` into its components or cases. Rewrite `this` using `[h0]`. Simplify using `at this`. Conclude with `h0`. Establish `hne` using `L_ne_zero X hr τ`.

Establish `hla` using `first_minimum_pos X hne`. Establish `h' : X.la1 < th (E` using `E) P.q P.R0 := h`. Establish `hph : P.ph = 2 * PT.f E / (PT.rd E ^ 2 * X.la1 ^ 2)` using `by rw [Par.ph, PT.ph, if_pos h']`. Take `⟨ρ, hρ, hfr⟩` from `rank_iso X I hI.le hI.stable hI.iso`. Establish `hin : ∀ x ∈ X.L, ‖x‖ < P.th → x ∈ I`.

Introduce `x hx hxs`. Assume the negation of the conclusion as `hxI`. Establish `h1` using `hmax x hx hxI`. Establish `h2 : Metric.infDist x (IR I) ≤ ‖x‖`. Rewrite using `[← dist_zero_right]`.

Conclude with `Metric.infDist_le_dist_of_mem (IR I).zero_mem`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨I, hI.le, sat_of_IR hI.sat, hI.stable, hI.iso, ?_, ⟨ρ, le_trans (hρ τ) hτ, hfr⟩, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Conclude with `X.eps_iso x (hI.le hx) (fun α => hI.iso _ (hI.stable α x hx) x hx)`.

Use `⟨fun _ => h, fun _ hbot => ?_⟩` and prove the remaining obligations. Take `⟨x, hx, hx0, hxs⟩` from `exists_short X hne h`. Use `hin x hx hxs` as an intermediate fact. Rewrite `this` using `[hbot, Submodule.mem_bot]`. Conclude with `hx0 this`.

Introduce `x hx _ hxI`. Conclude with `hmax x hx hxI`. Introduce `x hx u hu hne`. Establish `h1` using `hI.sep x hx u hu hne`. Establish `key : b0 (E` using `E) P.q P.R0 * (Ω ^ 2 * P.th ^ 2) = 4 * (PT.f E : ℝ) ^ 4 * PT.rd E ^ 2 / RR (E := E) := by`.

Establish `hR0ne : P.R0 ≠ 0` using `fun h0 => by rw [h0] at hR0; simp at hR0`. Rewrite using `[hΩ2, hth2, b0]`. Clear the denominators using the available nonvanishing facts. Establish `hf4 : (PT.f E : ℝ) ^ 4 ≤ PT.rd E ^ 2`. Use `P.hf2` as an intermediate fact.

Combine the equalities or inequalities in the displayed calculation. Establish `hb : b0 (E` using `E) P.q P.R0 * (Ω ^ 2 * P.th ^ 2) ≤ 1 := by`. Rewrite using `[key, div_le_one hRR, RR]`. Establish `: 4 * PT.rd E ^ 4 ≤ PT.rd E ^ 7`. Establish `h3 : (4 : ℝ) ≤ PT.rd E ^ 3` using `by nlinarith`.

Combine the equalities or inequalities in the displayed calculation. Use polynomial arithmetic with `[pow_pos (show (0:ℝ) < PT.rd E by linarith) 2]`. Establish `hb' : b0 (E` using `E) P.q P.R0 ≤ (1 / (Ω * P.th)) ^ 2 := by`. Rewrite using `[div_pow, one_pow, mul_pow, le_div_iff₀ (by positivity)]`. Conclude with `hb`.

Conclude with `hb'.trans (pow_le_pow_left₀ (by positivity) h1.le 2)`. Take `⟨x, u, hxu, hli, hb⟩` from `exists_short_vectors_realSpan X I hI.le hI.sat hla (ε := 1 / X.la1) (by positivity)`. Use `⟨x, u, hxu, hli, fun j => ?_⟩` and prove the remaining obligations. Establish `hN : (Module.finrank ℝ (IR I) : ℝ) ≤ dstar (E` using `E) P.m := by`. Establish `: Module.finrank ℝ (IR I) ≤ dstar (E` using `E) P.m := by`.

Rewrite using `[hfr, dstar]`. Conclude with `Nat.mul_le_mul_left _ (le_trans (hρ τ) hτ)`. Conclude with `this` after adjusting the coercions. Use `set d : ℝ := (dstar (E := E) P.m : ℝ)`. Establish `hR : PT.rd E ^ 2 * d ^ 4 * P.ph / (2 * PT.f E) = d ^ 4 / X.la1 ^ 2`.

Rewrite using `[hph]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hR]`. Conclude with `sq_le_pow_four_div_sq hd2 hN hla (norm_nonneg _) (hb j)`. Introduce `k x u hxu hspan`.

Rewrite using `[hph]`. Use `set S := ∑ j, ‖u j‖ ^ 2 / 2`. Use `set c : ℝ := 2 * PT.f E / PT.rd E ^ 2 with hc`. Establish `hcpos : 0 < c` using `by rw [hc]; positivity`. Establish `hbound : ∀ ε > 0, c / (X.la1 + ε) ^ 2 ≤ S`.

Introduce `ε hε`. Take `⟨ξ, hξ, hξ0, hξs⟩` from `exists_short X hne (lt_min h (by linarith : X.la1 < X.la1 + ε))`. Establish `hξI` using `hin ξ hξ (lt_of_lt_of_le hξs (min_le_left _ _))`. Establish `h1` using `sum_sq_norm_ge_of_span X I hI.le hI.stable hξI hξ0 k x u hxu hspan`. Establish `h2 : c / (X.la1 + ε) ^ 2 ≤ c / ‖ξ‖ ^ 2`.

Apply `div_le_div_of_nonneg_left hcpos.le (by positivity)` to reduce the goal to its premises. Conclude with `pow_le_pow_left₀ (norm_nonneg _) (le_of_lt (lt_of_lt_of_le hξs (min_le_right _ _))) 2`. Use `h2.trans (le_of_eq_of_le ?_ h1)` and prove the remaining obligations. Rewrite using `[hc]`. Clear the denominators using the available nonvanishing facts.

Establish `hl` using `le_of_forall_pos_div_sq hla hcpos hbound`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem split_pos (X : PT E) {DF : ℕ} (P : Par X DF) (h : X.la1 < P.th) : ∃ I, IsSplit P I := by
  obtain ⟨n, ω, hω, hsp⟩ := omega_exists' (E := E)
  have hf1n : 1 ≤ PT.f E := le_trans (Nat.one_le_pow _ _ P.hm1) P.hmf
  have hf1 : (1 : ℝ) ≤ PT.f E := by exact_mod_cast hf1n
  have hrd := P.hrd
  have hRR : (0 : ℝ) < RR (E := E) := by rw [RR]; positivity
  have hq : (0 : ℝ) < P.q := by exact_mod_cast P.hq
  have hR0 : (0 : ℝ) < P.R0 ^ 2 := by linarith [P.hR0.1]
  set Ω := omStar (E := E) with hΩdef
  have hΩ : 0 < Ω := by rw [hΩdef, omStar]; positivity
  have hΩ2 : Ω ^ 2 = 4 * (PT.f E : ℝ) ^ 3 * PT.rd E ^ 2 := by
    rw [hΩdef, omStar, mul_pow, mul_pow, ← Real.rpow_natCast ((PT.f E : ℝ) ^ ((3 : ℝ) / 2)),
      ← Real.rpow_mul (by positivity)]
    norm_num
  have hth2 : P.th ^ 2 = PT.f E * P.R0 ^ 2 * RR (E := E) ^ 3 / P.q := by
    rw [Par.th, th, Real.sq_sqrt]; positivity
  have hth : 0 < P.th := by
    rw [Par.th, th]; apply Real.sqrt_pos.2; positivity
  have hd2n : 2 ≤ dstar (E := E) P.m := by
    rw [dstar]; have := P.hm1; nlinarith
  have hd2 : (2 : ℝ) ≤ dstar (E := E) P.m := by exact_mod_cast hd2n
  have hC1 : (dstar (E := E) P.m : ℝ) ^ 2 * Ω * P.th ^ 2 < 1 := P.C1
  have hΩth : Ω * P.th ^ 2 ≤ 1 := by nlinarith [sq_nonneg P.th, hΩ]
  obtain ⟨I, hI, hmax⟩ := exists_maximal X ω hΩ hth hΩth hω hsp
  obtain ⟨τ, hτ⟩ := P.hm
  have hr : 1 ≤ X.r := by
    have := P.hfr
    rcases Nat.eq_zero_or_pos X.r with h0 | h0
    · rw [h0] at this; simp at this
    · exact h0
  have hne := L_ne_zero X hr τ
  have hla := first_minimum_pos X hne
  have h' : X.la1 < th (E := E) P.q P.R0 := h
  have hph : P.ph = 2 * PT.f E / (PT.rd E ^ 2 * X.la1 ^ 2) := by rw [Par.ph, PT.ph, if_pos h']
  obtain ⟨ρ, hρ, hfr⟩ := rank_iso X I hI.le hI.stable hI.iso
  have hin : ∀ x ∈ X.L, ‖x‖ < P.th → x ∈ I := by
    intro x hx hxs
    by_contra hxI
    have h1 := hmax x hx hxI
    have h2 : Metric.infDist x (IR I) ≤ ‖x‖ := by
      rw [← dist_zero_right]; exact Metric.infDist_le_dist_of_mem (IR I).zero_mem
    linarith
  refine ⟨I, hI.le, sat_of_IR hI.sat, hI.stable, hI.iso, ?_, ⟨ρ, le_trans (hρ τ) hτ, hfr⟩, ?_,
    ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact X.eps_iso x (hI.le hx) (fun α => hI.iso _ (hI.stable α x hx) x hx)
  · refine ⟨fun _ => h, fun _ hbot => ?_⟩
    obtain ⟨x, hx, hx0, hxs⟩ := exists_short X hne h
    have := hin x hx hxs
    rw [hbot, Submodule.mem_bot] at this
    exact hx0 this
  · intro x hx _ hxI
    exact hmax x hx hxI
  · intro x hx u hu hne
    have h1 := hI.sep x hx u hu hne
    have key : b0 (E := E) P.q P.R0 * (Ω ^ 2 * P.th ^ 2) = 4 * (PT.f E : ℝ) ^ 4 * PT.rd E ^ 2 / RR (E := E) := by
      have hR0ne : P.R0 ≠ 0 := fun h0 => by rw [h0] at hR0; simp at hR0
      rw [hΩ2, hth2, b0]; field_simp
    have hf4 : (PT.f E : ℝ) ^ 4 ≤ PT.rd E ^ 2 := by
      have := P.hf2
      calc (PT.f E : ℝ) ^ 4 = ((PT.f E : ℝ) ^ 2) ^ 2 := by ring
        _ ≤ PT.rd E ^ 2 := pow_le_pow_left₀ (by positivity) this 2
    have hb : b0 (E := E) P.q P.R0 * (Ω ^ 2 * P.th ^ 2) ≤ 1 := by
      rw [key, div_le_one hRR, RR]
      have : 4 * PT.rd E ^ 4 ≤ PT.rd E ^ 7 := by
        have h3 : (4 : ℝ) ≤ PT.rd E ^ 3 := by nlinarith
        calc 4 * PT.rd E ^ 4 ≤ PT.rd E ^ 3 * PT.rd E ^ 4 :=
              mul_le_mul_of_nonneg_right h3 (by positivity)
          _ = PT.rd E ^ 7 := by ring
      nlinarith [pow_pos (show (0:ℝ) < PT.rd E by linarith) 2]
    have hb' : b0 (E := E) P.q P.R0 ≤ (1 / (Ω * P.th)) ^ 2 := by
      rw [div_pow, one_pow, mul_pow, le_div_iff₀ (by positivity)]
      exact hb
    exact hb'.trans (pow_le_pow_left₀ (by positivity) h1.le 2)
  · obtain ⟨x, u, hxu, hli, hb⟩ := exists_short_vectors_realSpan X I hI.le hI.sat hla (ε := 1 / X.la1) (by positivity)
    refine ⟨x, u, hxu, hli, fun j => ?_⟩
    have hN : (Module.finrank ℝ (IR I) : ℝ) ≤ dstar (E := E) P.m := by
      have : Module.finrank ℝ (IR I) ≤ dstar (E := E) P.m := by
        rw [hfr, dstar]; exact Nat.mul_le_mul_left _ (le_trans (hρ τ) hτ)
      exact_mod_cast this
    set d : ℝ := (dstar (E := E) P.m : ℝ)
    have hR : PT.rd E ^ 2 * d ^ 4 * P.ph / (2 * PT.f E) = d ^ 4 / X.la1 ^ 2 := by
      rw [hph]; field_simp
    rw [hR]
    exact sq_le_pow_four_div_sq hd2 hN hla (norm_nonneg _) (hb j)
  · intro k x u hxu hspan
    rw [hph]
    set S := ∑ j, ‖u j‖ ^ 2 / 2
    set c : ℝ := 2 * PT.f E / PT.rd E ^ 2 with hc
    have hcpos : 0 < c := by rw [hc]; positivity
    have hbound : ∀ ε > 0, c / (X.la1 + ε) ^ 2 ≤ S := by
      intro ε hε
      obtain ⟨ξ, hξ, hξ0, hξs⟩ := exists_short X hne (lt_min h (by linarith : X.la1 < X.la1 + ε))
      have hξI := hin ξ hξ (lt_of_lt_of_le hξs (min_le_left _ _))
      have h1 := sum_sq_norm_ge_of_span X I hI.le hI.stable hξI hξ0 k x u hxu hspan
      have h2 : c / (X.la1 + ε) ^ 2 ≤ c / ‖ξ‖ ^ 2 := by
        apply div_le_div_of_nonneg_left hcpos.le (by positivity)
        exact pow_le_pow_left₀ (norm_nonneg _) (le_of_lt (lt_of_lt_of_le hξs (min_le_right _ _))) 2
      refine h2.trans (le_of_eq_of_le ?_ h1)
      rw [hc]; field_simp
    have hl := le_of_forall_pos_div_sq hla hcpos hbound
    calc 2 * PT.f E / (PT.rd E ^ 2 * X.la1 ^ 2) = c / X.la1 ^ 2 := by rw [hc]; field_simp
      _ ≤ S := hl

end

end ReciprocityTheory.ChartRestriction.G.I2
