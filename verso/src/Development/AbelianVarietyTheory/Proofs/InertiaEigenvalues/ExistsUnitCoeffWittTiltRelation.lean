import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.ResidueUnitCoeff

/- English proof (translation)
Use `⟨fun he => ?_⟩` and prove the remaining obligations. Substitute `he` using the available equality. Establish `h` using `ϖ.seq_zero`. Rewrite `h` using `[pow_zero, eq_neg_iff_add_eq_zero, add_comm]`. Conclude with `Nat.cast_add_one_ne_zero l h`.
-/
theorem neZero_of_piSys {l : ℕ} [Fact l.Prime] {e : ℕ} (ϖ : PiSys l e) : NeZero e := by
  refine ⟨fun he => ?_⟩
  subst he
  have h := ϖ.seq_zero
  rw [pow_zero, eq_neg_iff_add_eq_zero, add_comm] at h
  exact Nat.cast_add_one_ne_zero l h

/- English proof (translation)
Establish `: IsNoetherianRing O` using `isNoetherian_of_tower ℤ_[l] inferInstance`. Set `m : Ideal O` to `{ carrier := {c | ‖algebraMap O K c‖ < 1} add_mem' := fun {x y} hx hy => by`. Simplify using `only [Set.mem_setOf_eq, map_add] at *`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx hy)`. Use the proof step `zero_mem' := by simp`.

Use the proof step `smul_mem' := fun r x hx => by`. Simplify using `only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at *`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) (norm_algebraMap_le r)).trans_lt hx }`. Take `⟨s, hs⟩` from `(IsNoetherian.noetherian m : m.FG)`. Use `⟨(s.sup fun g => ‖algebraMap O K g‖₊ : NNReal), NNReal.coe_nonneg _, ?_, fun c hc => ?_⟩` and prove the remaining obligations.

Establish `: s.sup (fun g => ‖algebraMap O K g‖₊) < 1`. Use `(Finset.sup_lt_iff zero_lt_one).2 fun g hg => ?_` and prove the remaining obligations. Establish `: g ∈ m` using `hs ▸ Ideal.subset_span hg`. Conclude with `(by exact_mod_cast this : ‖algebraMap O K g‖ < 1)`. Conclude with `this` after adjusting the coercions.

Establish `key : ∀ c ∈ Submodule.span O (s : Set O), ‖algebraMap O K c‖ ≤ (s.sup fun g => ‖algebraMap O K g‖₊ : NNReal)`. Introduce `c hc'`. Proceed by induction on `hc' using Submodule.span_induction with`. Consider the case `mem x hx`. Conclude with `Finset.le_sup (f := fun g => ‖algebraMap O K g‖₊) hx` after adjusting the coercions.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)`. Consider the case `smul r x _ hx`.

Rewrite using `[smul_eq_mul, map_mul, norm_mul]`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) (norm_algebraMap_le r)).trans hx`. Conclude with `key c (by rw [hs]; exact hc)`.
-/
theorem exists_bound {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ c : O, ‖algebraMap O K c‖ < 1 → ‖algebraMap O K c‖ ≤ ρ := by
  have : IsNoetherianRing O := isNoetherian_of_tower ℤ_[l] inferInstance
  let m : Ideal O :=
    { carrier := {c | ‖algebraMap O K c‖ < 1}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_add] at *
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx hy)
      zero_mem' := by simp
      smul_mem' := fun r x hx => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at *
        exact (mul_le_of_le_one_left (norm_nonneg _) (norm_algebraMap_le r)).trans_lt hx }
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian m : m.FG)
  refine ⟨(s.sup fun g => ‖algebraMap O K g‖₊ : NNReal), NNReal.coe_nonneg _, ?_, fun c hc => ?_⟩
  · have : s.sup (fun g => ‖algebraMap O K g‖₊) < 1 := by
      refine (Finset.sup_lt_iff zero_lt_one).2 fun g hg => ?_
      have : g ∈ m := hs ▸ Ideal.subset_span hg
      exact (by exact_mod_cast this : ‖algebraMap O K g‖ < 1)
    exact_mod_cast this
  · have key : ∀ c ∈ Submodule.span O (s : Set O),
        ‖algebraMap O K c‖ ≤ (s.sup fun g => ‖algebraMap O K g‖₊ : NNReal) := by
      intro c hc'
      induction hc' using Submodule.span_induction with
      | mem x hx =>
        exact_mod_cast Finset.le_sup (f := fun g => ‖algebraMap O K g‖₊) hx
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
      | smul r x _ hx =>
        rw [smul_eq_mul, map_mul, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (norm_algebraMap_le r)).trans hx
    exact key c (by rw [hs]; exact hc)

end GlobalTheory.ResidueUnitCoeff

namespace GlobalTheory.ResidueUnitCoeff

/- English proof (translation)
Proceed by induction on `m generalizing n with`. Consider the case `zero => rw [pow_zero, pow_zero, coeff_one]; split_ifs <;> simp`. Consider the case `succ m ih`. Rewrite using `[pow_succ, pow_succ]`. Simplify `ih) (by simpa using hf) n` using `using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp) (pow_nonneg h0 m) h0 (f := f ^ m) (g := f) (by simpa`.
-/
theorem norm_coeff_pow_le {K : Type} [NormedField K] [IsUltrametricDist K] {f : K⟦X⟧} {ρ : ℝ}
    (h0 : 0 ≤ ρ) (hf : ∀ n, ‖coeff n f‖ ≤ ρ) (m n : ℕ) : ‖coeff n (f ^ m)‖ ≤ ρ ^ m := by
  induction m generalizing n with
  | zero => rw [pow_zero, pow_zero, coeff_one]; split_ifs <;> simp
  | succ m ih =>
    rw [pow_succ, pow_succ]
    simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp)
      (pow_nonneg h0 m) h0 (f := f ^ m) (g := f) (by simpa using ih) (by simpa using hf) n

/- English proof (translation)
Introduce `l _ a _ e O K _ _ _ _ _ _ _ _ _ t ϖ S _ y c h τ`. Use `neZero_of_piSys ϖ` as an intermediate fact. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Take `⟨ρ, hρ0, hρ1, hρ⟩` from `exists_bound (l := l) (O := O) (K := K)`.

Establish `hco : ∀ s k, ‖coeff k (y s τ : K⟦X⟧)‖ ≤ ρ` using `fun s k => by`. Take `⟨o, ho⟩` from `(IsUnitBall.mem_range_iff (O := O) _).2 (mem_A.1 (y s τ).2 k)`. Establish `h1 : ‖coeff k (y s τ : K⟦X⟧)‖ < 1` using `lt_of_le_of_ne (mem_A.1 (y s τ).2 k) (hne s k)`. Rewrite `h1`, the goal using `[← ho]`. Conclude with `hρ o h1`.

Establish `hl0 : (l : K) ≠ 0`. Rewrite using `[← map_natCast (algebraMap ℚ_[l] K)]`. Conclude with `(map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)`. Establish `hlpos : 0 < ‖(l : K)‖` using `norm_pos_iff.2 hl0`. Take `⟨N0, hN0⟩` from `exists_pow_lt_of_lt_one hlpos hρ1`.

Use `set N := N0 + 1 with hN`. Establish `hρN : ρ ^ N ≤ ‖(l : K)‖` using `(pow_le_pow_of_le_one hρ0 hρ1.le (Nat.le_succ N0)).trans hN0.le`. Establish `hzmem : ∀ s, C (l : K)⁻¹ * (y s τ : K⟦X⟧) ^ N ∈ A O K` using `fun s n => by`. Rewrite using `[coeff_C_mul, norm_mul, norm_inv, inv_mul_le_iff₀ hlpos, mul_one]`. Conclude with `(norm_coeff_pow_le hρ0 (hco s) N n).trans hρN`.

Set `z : S → A O K` to `fun s => ⟨_, hzmem s⟩`. Establish `hz : ∀ s, y s τ ^ N = (l : A O K) * z s` using `fun s => Subtype.ext (by`. Simplify using `only [SubmonoidClass.coe_pow, MulMemClass.coe_mul, SubringClass.coe_natCast, z]`. Rewrite using `[← map_natCast (C : K →+* K⟦X⟧), ← mul_assoc, ← map_mul, mul_inv_cancel₀ hl0, map_one, one_mul])`. Set `ε : ZMod a → A O K` to `Pi.single τ 1`.

Establish `hpow : ∀ s, (ε * y s) ^ N = (l : ZMod a → A O K) * Pi.single τ (z s)` using `fun s => by`. Use function extensionality and compare the values at `σ`. Break down `eq_or_ne σ τ with rfl | hσ` into its components or cases. Simplify using `[ε, hz]`. Simplify using `[ε, hσ, hN]`.

Take `⟨Φ, hΦi, hΦ⟩ : ∃ Φ : (ZMod a → A O K) →ₐ[O] OW l O, Function.Injective Φ ∧ ∀ s, inclO l O (ϖ.iTot t K (y s)) = Φ (y s)` from `⟨(inclO l O).comp (ϖ.iTot t K), inclO_injective.comp (ϖ.iTot_injective t K), fun _ => rfl⟩`. Simplify using `only [hΦ] at h`. Establish `hidem : IsIdempotentElem (Φ ε)` using `by show Φ ε * Φ ε = Φ ε`. Rewrite using `[← map_mul]`. Use `congr 1`.

Simplify using `only [ε, ← Pi.single_mul, one_mul]`. Establish `hne0 : Φ ε ≠ 0` using `fun h0 => by`. Establish `h1` using `congrFun (hΦi (h0.trans (map_zero Φ).symm)) τ`. Simplify using `[ε] at h1`. Set `I : Ideal (OW l O)` to `Ideal.span {((l : ℕ) : OW l O)}`.

Establish `hnil : ∀ s, IsNilpotent (Ideal.Quotient.mk I (Φ ε * Φ (y s)))` using `fun s => by`. Use `⟨N, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow, ← map_mul, ← map_pow, hpow, map_mul, map_natCast, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`. Establish `hsum : Φ ε = ∑ s, c s * (Φ ε * Φ (y s))`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun s _ => by ring`. Establish `hmk : Ideal.Quotient.mk I (Φ ε) = 0`. Use `IsIdempotentElem.eq_zero_of_isNilpotent ?_ ?_` and prove the remaining obligations.

Use `show _ * _ = _`. Rewrite using `[← map_mul, hidem.eq]`. Rewrite using `[hsum, map_sum]`. Use `isNilpotent_sum fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`.

Conclude with `(Commute.all _ _).isNilpotent_mul_left (hnil s)`. Take `⟨x, hx⟩` from `Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hmk)`. Establish `hdvd : ∀ n, Φ ε ∈ Ideal.span {((l : ℕ) : OW l O) ^ n}` using `fun n => by`. Rewrite using `[Ideal.mem_span_singleton]`. Consider the cases of `n with`.

Consider the case `zero => exact one_dvd _`. Consider the case `succ n`. Rewrite using `[← hidem.pow_succ_eq n, ← hx, mul_pow]`. Conclude with `dvd_mul_left _ _`. Establish `hcpl` using `GlobalTheory.HWL.TensorWitt.complete_tensor (Module.Free.chooseBasis ℤ_[l] O) ((l : ℕ) : WCb l)`.

Establish `e1 : (1 : O) ⊗ₜ[ℤ_[l]] ((l : ℕ) : WCb l) = ((l : ℕ) : OW l O)` using `map_natCast (Algebra.TensorProduct.includeRight : WCb l →ₐ[ℤ_[l]] OW l O) l`. Rewrite `hcpl` using `[e1]`. Conclude with `hne0 (GlobalTheory.Per.AinfComplete.eq_zero_of_haus ((l : ℕ) : OW l O) (Φ ε) hdvd)`.
-/
theorem exists_norm_coeff_eq_one : ∀ {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {S : Type} [Fintype S] (y : S → ZMod a → A O K) (c : S → OW l O) (h : ∑ s, c s * inclO l O (ϖ.iTot t K (y s)) = 1) (τ : ZMod a), ∃ s k, ‖coeff k (y s τ : K⟦X⟧)‖ = 1 := by
  intro l _ a _ e O K _ _ _ _ _ _ _ _ _ t ϖ S _ y c h τ
  have := neZero_of_piSys ϖ
  by_contra hne
  push_neg at hne
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := exists_bound (l := l) (O := O) (K := K)
  have hco : ∀ s k, ‖coeff k (y s τ : K⟦X⟧)‖ ≤ ρ := fun s k => by
    obtain ⟨o, ho⟩ := (IsUnitBall.mem_range_iff (O := O) _).2 (mem_A.1 (y s τ).2 k)
    have h1 : ‖coeff k (y s τ : K⟦X⟧)‖ < 1 := lt_of_le_of_ne (mem_A.1 (y s τ).2 k) (hne s k)
    rw [← ho] at h1 ⊢
    exact hρ o h1
  have hl0 : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] K)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hlpos : 0 < ‖(l : K)‖ := norm_pos_iff.2 hl0
  obtain ⟨N0, hN0⟩ := exists_pow_lt_of_lt_one hlpos hρ1
  set N := N0 + 1 with hN
  have hρN : ρ ^ N ≤ ‖(l : K)‖ :=
    (pow_le_pow_of_le_one hρ0 hρ1.le (Nat.le_succ N0)).trans hN0.le
  have hzmem : ∀ s, C (l : K)⁻¹ * (y s τ : K⟦X⟧) ^ N ∈ A O K := fun s n => by
    rw [coeff_C_mul, norm_mul, norm_inv, inv_mul_le_iff₀ hlpos, mul_one]
    exact (norm_coeff_pow_le hρ0 (hco s) N n).trans hρN
  let z : S → A O K := fun s => ⟨_, hzmem s⟩
  have hz : ∀ s, y s τ ^ N = (l : A O K) * z s := fun s => Subtype.ext (by
    simp only [SubmonoidClass.coe_pow, MulMemClass.coe_mul, SubringClass.coe_natCast, z]
    rw [← map_natCast (C : K →+* K⟦X⟧), ← mul_assoc, ← map_mul, mul_inv_cancel₀ hl0, map_one, one_mul])
  let ε : ZMod a → A O K := Pi.single τ 1
  have hpow : ∀ s, (ε * y s) ^ N = (l : ZMod a → A O K) * Pi.single τ (z s) := fun s => by
    funext σ
    rcases eq_or_ne σ τ with rfl | hσ
    · simp [ε, hz]
    · simp [ε, hσ, hN]
  obtain ⟨Φ, hΦi, hΦ⟩ : ∃ Φ : (ZMod a → A O K) →ₐ[O] OW l O, Function.Injective Φ ∧
      ∀ s, inclO l O (ϖ.iTot t K (y s)) = Φ (y s) :=
    ⟨(inclO l O).comp (ϖ.iTot t K), inclO_injective.comp (ϖ.iTot_injective t K), fun _ => rfl⟩
  simp only [hΦ] at h
  have hidem : IsIdempotentElem (Φ ε) := by
    show Φ ε * Φ ε = Φ ε
    rw [← map_mul]
    congr 1
    simp only [ε, ← Pi.single_mul, one_mul]
  have hne0 : Φ ε ≠ 0 := fun h0 => by
    have h1 := congrFun (hΦi (h0.trans (map_zero Φ).symm)) τ
    simp [ε] at h1
  let I : Ideal (OW l O) := Ideal.span {((l : ℕ) : OW l O)}
  have hnil : ∀ s, IsNilpotent (Ideal.Quotient.mk I (Φ ε * Φ (y s))) := fun s => by
    refine ⟨N, ?_⟩
    rw [← map_pow, ← map_mul, ← map_pow, hpow, map_mul, map_natCast, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hsum : Φ ε = ∑ s, c s * (Φ ε * Φ (y s)) := by
    calc Φ ε = Φ ε * ∑ s, c s * Φ (y s) := by rw [h, mul_one]
      _ = ∑ s, c s * (Φ ε * Φ (y s)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring
  have hmk : Ideal.Quotient.mk I (Φ ε) = 0 := by
    refine IsIdempotentElem.eq_zero_of_isNilpotent ?_ ?_
    · show _ * _ = _
      rw [← map_mul, hidem.eq]
    · rw [hsum, map_sum]
      refine isNilpotent_sum fun s _ => ?_
      rw [map_mul]
      exact (Commute.all _ _).isNilpotent_mul_left (hnil s)
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hmk)
  have hdvd : ∀ n, Φ ε ∈ Ideal.span {((l : ℕ) : OW l O) ^ n} := fun n => by
    rw [Ideal.mem_span_singleton]
    cases n with
    | zero => exact one_dvd _
    | succ n =>
      rw [← hidem.pow_succ_eq n, ← hx, mul_pow]
      exact dvd_mul_left _ _
  have hcpl := GlobalTheory.HWL.TensorWitt.complete_tensor (Module.Free.chooseBasis ℤ_[l] O) ((l : ℕ) : WCb l)
  have e1 : (1 : O) ⊗ₜ[ℤ_[l]] ((l : ℕ) : WCb l) = ((l : ℕ) : OW l O) :=
    map_natCast (Algebra.TensorProduct.includeRight : WCb l →ₐ[ℤ_[l]] OW l O) l
  rw [e1] at hcpl
  exact hne0 (GlobalTheory.Per.AinfComplete.eq_zero_of_haus ((l : ℕ) : OW l O) (Φ ε) hdvd)

end GlobalTheory.ResidueUnitCoeff
