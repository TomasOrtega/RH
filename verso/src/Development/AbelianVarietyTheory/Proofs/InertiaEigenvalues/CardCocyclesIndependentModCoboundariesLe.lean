import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeSmulMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaMinusOneDivVariablePolarKernelLeSenWeightsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarPartFinrankAddSenWeightsLeRankStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaNablaMemOfKillingPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleLetterDataWindowArithmeticStatement

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models.PolarBound

/- English proof (translation)
Set `f` to `LinearMap.pi fun i => ((N i).submoduleOf (LinearMap.range (Fintype.linearCombination k (c i)))).mkQ ∘ₗ (Fintype.linearCombination k (c i)).rangeRestrict`. Establish `hf : Function.Injective f`. Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`. Introduce `t ht`. Use `hinj t fun i => ?_` and prove the remaining obligations.

Establish `h1 : f t i = 0` using `congrFun ht i`. Conclude with `(Submodule.Quotient.mk_eq_zero ((N i).submoduleOf (LinearMap.range (Fintype.linearCombination k (c i))))).1 h1`. Establish `h2` using `LinearMap.finrank_le_finrank_of_injective hf`. Rewrite `h2` using `[Module.finrank_fin_fun, Module.finrank_pi_fintype]`. Conclude with `h2.trans (Finset.sum_le_sum fun i _ => hd i)`.
-/
theorem card_le_sum {k V ι : Type} [Field k] [AddCommGroup V] [Module k V] [Fintype ι] {s : ℕ}
    (c : ι → Fin s → V) (N : ι → Submodule k V) (d : ι → ℕ)
    (hd : ∀ i, Module.finrank k (↥(LinearMap.range (Fintype.linearCombination k (c i))) ⧸
      (N i).submoduleOf (LinearMap.range (Fintype.linearCombination k (c i)))) ≤ d i)
    (hinj : ∀ t : Fin s → k, (∀ i, ∑ a, t a • c i a ∈ N i) → t = 0) : s ≤ ∑ i, d i := by
  let f := LinearMap.pi fun i => ((N i).submoduleOf (LinearMap.range (Fintype.linearCombination k (c i)))).mkQ ∘ₗ
    (Fintype.linearCombination k (c i)).rangeRestrict
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro t ht
    refine hinj t fun i => ?_
    have h1 : f t i = 0 := congrFun ht i
    exact (Submodule.Quotient.mk_eq_zero ((N i).submoduleOf
      (LinearMap.range (Fintype.linearCombination k (c i))))).1 h1
  have h2 := LinearMap.finrank_le_finrank_of_injective hf
  rw [Module.finrank_fin_fun, Module.finrank_pi_fintype] at h2
  exact h2.trans (Finset.sum_le_sum fun i _ => hd i)

variable {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l}

omit [Fact l.Prime] [CharP k l] [NeZero n] in

/- English proof (translation)
Assemble the required witnesses or components as `⟨y, rfl⟩`.
-/
theorem cob_mem (D : ModPG R n (Vc k m)) (y : ZMod n → Vc k m) :
    ((fun i => D.φ i (y (i - 1)) - y i, fun i => D.γ i (y i) - y i) :
      (ZMod n → Vc k m) × (ZMod n → Vc k m)) ∈ herrB D := ⟨y, rfl⟩

/- English proof (translation)
Take `⟨b, g⟩` from `z`. Take `⟨hL, hAB, hC⟩` from `hN`. Establish `hl2 : (2 : ℤ) ≤ l` using `by exact_mod_cast (Fact.out : l.Prime).two_le`. Take `⟨y, hy, hy'⟩` from `(Gauge.main R D Dt.w Dt.wst (Dt.sg l) N hL hAB hC (fun i => by have := hI i; have := (hw i).2; unfold TopData.wst at this; omega) hsen b g (fun i => (hz i).1) (fun i => (hz i).2.1)).1`. Establish `hx : ∀ i, ∃ x ∈ N i, (Dt.ty i = LType.G → x = y i) ∧ (Dt.ty i = LType.Bd → g i - (D.γ i x - x) ∈ sh (Dt.wst i + 2) (N i))`.

Introduce `i`. Consider the cases of `h : Dt.ty i with`. Consider the case `G => exact ⟨y i, hy i, fun _ => rfl, fun h => by cases h⟩`. Consider the case `Bd`. Take `⟨x, hx, hx'⟩` from `((hz i).2.2.2 h).2`.

Conclude with `⟨x, hx, fun h => (by cases h), fun _ => hx'⟩`. Use `choose x hx hxG hxB using hx`. Use `⟨(fun i => b i - (D.φ i (y (i - 1)) - y i), fun i => g i - (D.γ i (y i) - y i)), fun i => b i - D.φ i (y (i - 1)) + x i, ?_, fun i => ?_⟩` and prove the remaining obligations. Use `cob_mem D y using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `ext i : 2 <;> simp`.

Establish `h0 : D.γ i (b i) - b i = D.φ i (g (i - 1)) - g i` using `(hz i).1`. Establish `hφ : D.φ i (y (i - 1)) ∈ pull (D.φ i) (N (i - 1))` using `Submodule.subset_span ⟨_, hy _, rfl⟩`. Establish `hdeep : D.φ i (g (i - 1) - (D.γ (i - 1) (y (i - 1)) - y (i - 1))) ∈ sh (Dt.wst i + 2) (N i)`. Establish `h1` using `Gauge.phi_sh R _ (D.φ_semi i) _ _ _ (hAB i).1 (Dt.sg l (i - 1) + 3) (x := g (i - 1) - (D.γ (i - 1) (y (i - 1)) - y (i - 1))) (by simpa using hy' (i - 1))`. Use `sh_le_sh_of_le ?_ _ h1` and prove the remaining obligations.

Use `hI i` as an intermediate fact. Unfold `TopData.wst`. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities. Establish `hc : D.γ i (b i - D.φ i (y (i - 1)) + x i) - (b i - D.φ i (y (i - 1)) + x i) = D.φ i (g (i - 1) - (D.γ (i - 1) (y (i - 1)) - y (i - 1))) - (g i - (D.γ i (x i) - x i))`.

Simplify using `only [map_sub, map_add, D.comm]`. Take the linear combination `(norm := module) h0`. Establish `hsh : ∀ (a : ℤ) (P : Submodule k⟦X⟧ (Vc k m)), 0 ≤ a → P ≤ sh (-a) P` using `fun a P ha => by`. Simplify `sh_le_sh_of_le (a := 0) (b := -a) (by omega) P` using `[sh_zero_eq]`. Use `⟨?_, hy' i, ?_, fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Simplify using `only [map_sub, D.comm]`. Take the linear combination `(norm := module) h0`. Use `(N i).sub_mem (hx i) (hy i) using 1` and compare the differences between its conclusion and the goal. Simplify using `only []`. Normalize the expressions using the abelian group laws.

Conclude with `Submodule.add_mem _ (Submodule.sub_mem _ ((hz i).2.2.1 h) ((hAB i).1 hφ)) (hsh _ _ (hw i).1 (hx i))`. Use `beta_reduce`. Rewrite using `[hc, hxG i h]`. Use `Submodule.sub_mem _ (sh_le_sh_of_le ?_ _ hdeep) (sh_le_sh_of_le ?_ _ (hy' i))` and prove the remaining obligations. Use `(hw i).2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Use `Submodule.add_mem _ (Submodule.sub_mem _ ((hz i).2.2.2 h).1 (hsh _ _ (hw i).2 hφ)) ?_` and prove the remaining obligations. Use `sh_le_sh (-Dt.wst i) (hAB i).2` as an intermediate fact. Rewrite `this` using `[sh_sh_eq, neg_add_cancel, sh_zero_eq]`.

Conclude with `this (hx i)`. Use `beta_reduce`. Rewrite using `[hc]`. Conclude with `Submodule.sub_mem _ hdeep (hxB i h)`.
-/
theorem gauge_one (D : ModPG R n (Vc k m)) (Dt : TopData n m) (N : Lats k n m)
    (hI : ∀ i, (Dt.sg l i : ℤ) + 1 ≤ l * (Dt.sg l (i - 1) + 1) - Dt.h i)
    (hw : ∀ i, 0 ≤ Dt.w i ∧ 0 ≤ Dt.wst i) (hN : ABC D Dt.w Dt.wst N)
    (hsen : ∀ i (a : ℕ), a ≤ Dt.sg l i + 1 → sen (D.γ i) (N i) (a : k) = 0)
    (z : (ZMod n → Vc k m) × (ZMod n → Vc k m)) (hz : InZZ D Dt N z.1 z.2) :
    ∃ (z' : (ZMod n → Vc k m) × (ZMod n → Vc k m)) (c : ZMod n → Vc k m), z - z' ∈ herrB D ∧
      ∀ i, D.γ i (z'.1 i) - z'.1 i = D.φ i (z'.2 (i - 1)) - z'.2 i ∧ z'.2 i ∈ sh (Dt.sg l i + 3) (N i) ∧
        c i - z'.1 i ∈ N i ∧
        (Dt.ty i = LType.G → c i ∈ sh (-Dt.w i) (N i) ∧ D.γ i (c i) - c i ∈ sh 1 (N i)) ∧
        (Dt.ty i = LType.Bd → c i ∈ sh (-Dt.wst i) (pull (D.φ i) (N (i - 1))) ∧
          D.γ i (c i) - c i ∈ sh (Dt.wst i + 2) (N i)) := by
  obtain ⟨b, g⟩ := z
  obtain ⟨hL, hAB, hC⟩ := hN
  have hl2 : (2 : ℤ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  obtain ⟨y, hy, hy'⟩ := (Gauge.main R D Dt.w Dt.wst (Dt.sg l) N hL hAB hC
    (fun i => by have := hI i; have := (hw i).2; unfold TopData.wst at this; omega) hsen b g
    (fun i => (hz i).1) (fun i => (hz i).2.1)).1
  have hx : ∀ i, ∃ x ∈ N i, (Dt.ty i = LType.G → x = y i) ∧
      (Dt.ty i = LType.Bd → g i - (D.γ i x - x) ∈ sh (Dt.wst i + 2) (N i)) := by
    intro i
    cases h : Dt.ty i with
    | G => exact ⟨y i, hy i, fun _ => rfl, fun h => by cases h⟩
    | Bd =>
      obtain ⟨x, hx, hx'⟩ := ((hz i).2.2.2 h).2
      exact ⟨x, hx, fun h => (by cases h), fun _ => hx'⟩
  choose x hx hxG hxB using hx
  refine ⟨(fun i => b i - (D.φ i (y (i - 1)) - y i), fun i => g i - (D.γ i (y i) - y i)),
    fun i => b i - D.φ i (y (i - 1)) + x i, ?_, fun i => ?_⟩
  · convert cob_mem D y using 1
    ext i : 2 <;> simp
  have h0 : D.γ i (b i) - b i = D.φ i (g (i - 1)) - g i := (hz i).1
  have hφ : D.φ i (y (i - 1)) ∈ pull (D.φ i) (N (i - 1)) := Submodule.subset_span ⟨_, hy _, rfl⟩
  have hdeep : D.φ i (g (i - 1) - (D.γ (i - 1) (y (i - 1)) - y (i - 1))) ∈ sh (Dt.wst i + 2) (N i) := by
    have h1 := Gauge.phi_sh R _ (D.φ_semi i) _ _ _ (hAB i).1 (Dt.sg l (i - 1) + 3)
      (x := g (i - 1) - (D.γ (i - 1) (y (i - 1)) - y (i - 1))) (by simpa using hy' (i - 1))
    refine sh_le_sh_of_le ?_ _ h1
    have := hI i
    unfold TopData.wst
    push_cast; nlinarith
  have hc : D.γ i (b i - D.φ i (y (i - 1)) + x i) - (b i - D.φ i (y (i - 1)) + x i) =
      D.φ i (g (i - 1) - (D.γ (i - 1) (y (i - 1)) - y (i - 1))) - (g i - (D.γ i (x i) - x i)) := by
    simp only [map_sub, map_add, D.comm]
    linear_combination (norm := module) h0
  have hsh : ∀ (a : ℤ) (P : Submodule k⟦X⟧ (Vc k m)), 0 ≤ a → P ≤ sh (-a) P := fun a P ha => by
    simpa [sh_zero_eq] using sh_le_sh_of_le (a := 0) (b := -a) (by omega) P
  refine ⟨?_, hy' i, ?_, fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩
  · simp only [map_sub, D.comm]
    linear_combination (norm := module) h0
  · convert (N i).sub_mem (hx i) (hy i) using 1
    simp only []
    abel
  · exact Submodule.add_mem _ (Submodule.sub_mem _ ((hz i).2.2.1 h) ((hAB i).1 hφ)) (hsh _ _ (hw i).1 (hx i))
  · beta_reduce
    rw [hc, hxG i h]
    refine Submodule.sub_mem _ (sh_le_sh_of_le ?_ _ hdeep) (sh_le_sh_of_le ?_ _ (hy' i))
    · have := (hw i).2; omega
    · omega
  · refine Submodule.add_mem _ (Submodule.sub_mem _ ((hz i).2.2.2 h).1 (hsh _ _ (hw i).2 hφ)) ?_
    have := sh_le_sh (-Dt.wst i) (hAB i).2
    rw [sh_sh_eq, neg_add_cancel, sh_zero_eq] at this
    exact this (hx i)
  · beta_reduce
    rw [hc]
    exact Submodule.sub_mem _ hdeep (hxB i h)

omit [Fact l.Prime] [CharP k l] [NeZero n] in

/- English proof (translation)
Introduce and unpack `_ ⟨t, rfl⟩`. Rewrite using `[Fintype.linearCombination_apply, map_sum, ← Finset.sum_sub_distrib]`. Use `⟨Submodule.sum_mem _ fun a _ => Submodule.smul_of_tower_mem _ _ (h a).1, Submodule.sum_mem _ fun a _ => ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, ← smul_sub]`. Conclude with `Submodule.smul_of_tower_mem _ _ (h a).2`.
-/
theorem span_prop {s : ℕ} (c : Fin s → Vc k m) (g : Vc k m →ₗ[k] Vc k m) (P Q : Submodule k⟦X⟧ (Vc k m))
    (h : ∀ a, c a ∈ P ∧ g (c a) - c a ∈ Q) :
    ∀ x ∈ LinearMap.range (Fintype.linearCombination k c), x ∈ P ∧ g x - x ∈ Q := by
  rintro _ ⟨t, rfl⟩
  rw [Fintype.linearCombination_apply, map_sum, ← Finset.sum_sub_distrib]
  refine ⟨Submodule.sum_mem _ fun a _ => Submodule.smul_of_tower_mem _ _ (h a).1,
    Submodule.sum_mem _ fun a _ => ?_⟩
  rw [map_smul, ← smul_sub]
  exact Submodule.smul_of_tower_mem _ _ (h a).2

/- English proof (translation)
Introduce `hΨ k _ l n m _ _ _ R D ι Dt N hι T1 T2 T3 hN hs s z hz hli`. Establish `hW` using `GlobalTheory.T.admissibleLetterData_window_arithmetic (k := k) Dt T1 T2 T3`. Establish `hw : ∀ i, 0 ≤ Dt.w i ∧ 0 ≤ Dt.wst i` using `fun i => by`. Establish `h1` using `Dt.one_le_letterBlockLength`. Use `Dt.range i (Dt.w i) (Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨le_rfl, by omega⟩)))` as an intermediate fact.

Unfold `TopData.wst`. Use linear arithmetic over natural numbers and integers. Use `choose z' c hz' hc using fun a => gauge_one D Dt N (fun i => (hW i).1) hw hN (fun i => (hs i).1) (z a) (hz a)`. Take `⟨hL, hAB, hC⟩` from `hN`. Establish `hl5 : 5 ≤ l` using `by have := T1 0; omega`.

Take `⟨ψ, -, ⟨p1, p2, -, p4⟩, hmod⟩` from `hΨ.modPG l k hl5 R ι hι`. Use `choose Ψ hΨ1 hΨ2 hΨ3 using fun i => hmod n (Vc k m) D i`. Use `card_le_sum (fun i a => c a i) (fun i => (N i).restrictScalars k) Dt.d (fun i => ?_) (fun t ht => ?_)` and prove the remaining obligations. Consider the cases of `h : Dt.ty i with`. Consider the case `G`.

Establish `e : ((Dt.w i).toNat : ℤ) = Dt.w i` using `Int.toNat_of_nonneg (hw i).1`. Use `GlobalTheory.T.gammaMinusOneDivVariable_polar_kernel_le_senWeights R (D.γ i) (D.γ_semi i) (N i) (hL i) (hC i) (Dt.w i).toNat (LinearMap.range (Fintype.linearCombination k fun a => c a i)) (fun x hx => by` as an intermediate fact. Use `span_prop _ (D.γ i) _ _ (fun a => (hc a i).2.2.2.1 h) x hx` as an intermediate fact. Rewrite using `[e]`. Use `⟨this.1, ?_⟩` and prove the remaining obligations.

Establish `h2` using `mem_sh_iff_smul_mem.1 this.2`. Rewrite using `[zpow_neg_one] at h2)` and apply the resulting hypothesis. Rewrite `this` using `[e, (hs i).2.1 h]`. Conclude with `this`. Consider the case `Bd`.

Establish `e : ((Dt.wst i).toNat : ℤ) = Dt.wst i` using `Int.toNat_of_nonneg (hw i).2`. Take `⟨-, -, w1, w2⟩` from `(hW i).2.2.2 h`. Establish `h1` using `Dt.one_le_letterBlockLength`. Establish `h2` using `T1 i`. Establish `h3` using `(hW i).1`.

Take `⟨s1, s2⟩` from `(hs i).2.2 h`. Use `GlobalTheory.T.polarPart_finrank_add_senWeights_le_rank R D Ψ ψ hΨ1 p1 (by simpa using p2 1) hΨ2 (fun a ha ha' => by rw [p4 a ha ha']; ext x; simp [eq_comm]) i (N (i - 1)) (N i) (Dt.wst i).toNat (Dt.sg l (i - 1)) (Dt.w i) (hL _) (hL _) (hC _) (hC _) (by omega) (by omega) (by rw [ …` as an intermediate fact. Rewrite `hy`, the goal using `[e]`. Establish `h4` using `(hΨ3 i _ (hL (i - 1))).2 (hC _) (-Dt.wst i) (by omega) (by omega)`. Establish `h5 : y ∈ GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.kerPsi (Ψ i) (pull (D.φ i) (N (i - 1))) (-Dt.wst i + 1)` using `⟨by rwa [neg_add_eq_sub], hy0⟩`.

Rewrite `h5` using `[← h4]`. Take `⟨x, ⟨hx, hx0⟩, hxy⟩` from `h5`. Conclude with `⟨x, hx, hx0, hxy⟩)`. Use the proof step `(by rw [e]; exact GlobalTheory.T.gammaNabla_mem_of_killing_polynomial D i (N i) _ (hC i) s2)`. Use the proof step `(LinearMap.range (Fintype.linearCombination k fun a => c a i)) (by`.

Rewrite using `[e]`. Conclude with `span_prop _ (D.γ i) _ _ (fun a => (hc a i).2.2.2.2 h))`. Rewrite `this` using `[Module.finrank_fin_fun]`. Use linear arithmetic over natural numbers and integers. Establish `hg : ∀ i, (∑ a, t a • z' a).2 i ∈ sh (Dt.sg l i + 3) (N i)` using `fun i => by`.

Simplify using `only [Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply]`. Conclude with `Submodule.sum_mem _ fun a _ => Submodule.smul_of_tower_mem _ _ (hc a i).2.1`. Take `⟨y, -, hy⟩` from `(Gauge.main R D Dt.w Dt.wst (Dt.sg l) N hL hAB hC (fun i => by have := (hW i).1; have := (hw i).2; unfold TopData.wst at this; omega) (fun i => (hs i).1) (∑ a, t a • z' a).1 (∑ a, t a • z' a).2 (fun i => by`. Simplify using `only [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, map_sum, map_smul, ← Finset.sum_sub_distrib, ← smul_sub]`. Conclude with `Finset.sum_congr rfl fun a _ => by rw [(hc a i).1])`.

Use the proof step `(fun i => sh_le_sh_of_le (by omega) _ (hg i))).2 hg (fun i => by`. Establish `h1 : ∑ a, t a • (c a i - (z' a).1 i) ∈ N i` using `Submodule.sum_mem _ fun a _ => Submodule.smul_of_tower_mem _ _ (hc a i).2.2.1`. Establish `h2 : ∑ a, t a • c a i ∈ N i` using `ht i`. Use `(N i).sub_mem h2 h1 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Prod.fst_sum, Finset.sum_apply, Prod.smul_fst, Pi.smul_apply, ← Finset.sum_sub_distrib, ← smul_sub, sub_sub_cancel])`.

Establish `h1 : ∑ a, t a • z' a ∈ herrB D`. Use `cob_mem D y using 1` and compare the differences between its conclusion and the goal. Conclude with `Prod.ext (funext fun i => (hy i).1) (funext fun i => (hy i).2)`. Establish `h2 : ∑ a, t a • (z a - z' a) ∈ herrB D` using `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hz' a)`. Establish `h3 : ∑ a, t a • z a ∈ herrB D`.

Use `(herrB D).add_mem h1 h2 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [← Finset.sum_add_distrib, ← smul_add, add_sub_cancel]`. Use function extensionality and compare the values at `a`. Use `Fintype.linearIndependent_iff.1 hli t ?_ a` and prove the remaining obligations. Establish `h4 : (herrB D).mkQ (∑ a, t a • z a) = 0` using `(Submodule.Quotient.mk_eq_zero _).2 h3`.

Simplify `h4` using `only [map_sum, map_smul]`.
-/
theorem main : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi → ∀ {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (Dt : TopData n m) (N : Lats k n m), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → Dt.T1 l → Dt.T2 l → Dt.T3 l → ABC D Dt.w Dt.wst N → (∀ i, (∀ a : ℕ, a ≤ Dt.sg l i + 1 → sen (D.γ i) (N i) (a : k) = 0) ∧ (Dt.ty i = LType.G → ∑ j ∈ Finset.range (Dt.w i).toNat, sen (D.γ i) (N i) ((-Dt.w i + j : ℤ) : k) = Dt.d i) ∧ (Dt.ty i = LType.Bd → Dt.d i + ∑ a ∈ Finset.range ((Dt.wst i).toNat + 1), sen (D.γ i) (N i) (a : k) = m ∧ EPoly (D.γ i) (N i) (Dt.wst i + 1))) → ∀ (s : ℕ) (z : Fin s → (ZMod n → Vc k m) × (ZMod n → Vc k m)), (∀ a, InZZ D Dt N (z a).1 (z a).2) → LinearIndependent k (fun a => (herrB D).mkQ (z a)) → s ≤ Dt.dsum := by
  intro hΨ k _ l n m _ _ _ R D ι Dt N hι T1 T2 T3 hN hs s z hz hli
  have hW := GlobalTheory.T.admissibleLetterData_window_arithmetic (k := k) Dt T1 T2 T3
  have hw : ∀ i, 0 ≤ Dt.w i ∧ 0 ≤ Dt.wst i := fun i => by
    have h1 := Dt.one_le_letterBlockLength
    have := Dt.range i (Dt.w i) (Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨le_rfl, by omega⟩)))
    unfold TopData.wst
    omega
  choose z' c hz' hc using fun a => gauge_one D Dt N (fun i => (hW i).1) hw hN (fun i => (hs i).1) (z a) (hz a)
  obtain ⟨hL, hAB, hC⟩ := hN
  have hl5 : 5 ≤ l := by have := T1 0; omega
  obtain ⟨ψ, -, ⟨p1, p2, -, p4⟩, hmod⟩ := hΨ.modPG l k hl5 R ι hι
  choose Ψ hΨ1 hΨ2 hΨ3 using fun i => hmod n (Vc k m) D i
  refine card_le_sum (fun i a => c a i) (fun i => (N i).restrictScalars k) Dt.d (fun i => ?_) (fun t ht => ?_)
  · cases h : Dt.ty i with
    | G =>
      have e : ((Dt.w i).toNat : ℤ) = Dt.w i := Int.toNat_of_nonneg (hw i).1
      have := GlobalTheory.T.gammaMinusOneDivVariable_polar_kernel_le_senWeights R (D.γ i) (D.γ_semi i) (N i) (hL i) (hC i) (Dt.w i).toNat
        (LinearMap.range (Fintype.linearCombination k fun a => c a i)) (fun x hx => by
          have := span_prop _ (D.γ i) _ _ (fun a => (hc a i).2.2.2.1 h) x hx
          rw [e]
          refine ⟨this.1, ?_⟩
          have h2 := mem_sh_iff_smul_mem.1 this.2
          rwa [zpow_neg_one] at h2)
      rw [e, (hs i).2.1 h] at this
      exact this
    | Bd =>
      have e : ((Dt.wst i).toNat : ℤ) = Dt.wst i := Int.toNat_of_nonneg (hw i).2
      obtain ⟨-, -, w1, w2⟩ := (hW i).2.2.2 h
      have h1 := Dt.one_le_letterBlockLength
      have h2 := T1 i
      have h3 := (hW i).1
      obtain ⟨s1, s2⟩ := (hs i).2.2 h
      have := GlobalTheory.T.polarPart_finrank_add_senWeights_le_rank R D Ψ ψ hΨ1 p1 (by simpa using p2 1) hΨ2
        (fun a ha ha' => by rw [p4 a ha ha']; ext x; simp [eq_comm]) i (N (i - 1)) (N i) (Dt.wst i).toNat
        (Dt.sg l (i - 1)) (Dt.w i) (hL _) (hL _) (hC _) (hC _) (by omega) (by omega) (by rw [e]; exact (hAB i).2)
        (hAB i).1 (by rw [e]; unfold TopData.wst; nlinarith) (hs _).1
        (fun y hy hy0 => by
          rw [e] at hy ⊢
          have h4 := (hΨ3 i _ (hL (i - 1))).2 (hC _) (-Dt.wst i) (by omega) (by omega)
          have h5 : y ∈ GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.kerPsi (Ψ i) (pull (D.φ i) (N (i - 1))) (-Dt.wst i + 1) :=
            ⟨by rwa [neg_add_eq_sub], hy0⟩
          rw [← h4] at h5
          obtain ⟨x, ⟨hx, hx0⟩, hxy⟩ := h5
          exact ⟨x, hx, hx0, hxy⟩)
        (by rw [e]; exact GlobalTheory.T.gammaNabla_mem_of_killing_polynomial D i (N i) _ (hC i) s2)
        (LinearMap.range (Fintype.linearCombination k fun a => c a i)) (by
          rw [e]; exact span_prop _ (D.γ i) _ _ (fun a => (hc a i).2.2.2.2 h))
      rw [Module.finrank_fin_fun] at this
      omega
  · have hg : ∀ i, (∑ a, t a • z' a).2 i ∈ sh (Dt.sg l i + 3) (N i) := fun i => by
      simp only [Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_of_tower_mem _ _ (hc a i).2.1
    obtain ⟨y, -, hy⟩ := (Gauge.main R D Dt.w Dt.wst (Dt.sg l) N hL hAB hC
      (fun i => by have := (hW i).1; have := (hw i).2; unfold TopData.wst at this; omega) (fun i => (hs i).1)
      (∑ a, t a • z' a).1 (∑ a, t a • z' a).2 (fun i => by
        simp only [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Prod.smul_snd, Prod.smul_fst, Pi.smul_apply,
          map_sum, map_smul, ← Finset.sum_sub_distrib, ← smul_sub]
        exact Finset.sum_congr rfl fun a _ => by rw [(hc a i).1])
      (fun i => sh_le_sh_of_le (by omega) _ (hg i))).2 hg (fun i => by
        have h1 : ∑ a, t a • (c a i - (z' a).1 i) ∈ N i :=
          Submodule.sum_mem _ fun a _ => Submodule.smul_of_tower_mem _ _ (hc a i).2.2.1
        have h2 : ∑ a, t a • c a i ∈ N i := ht i
        convert (N i).sub_mem h2 h1 using 1
        simp only [Prod.fst_sum, Finset.sum_apply, Prod.smul_fst, Pi.smul_apply, ← Finset.sum_sub_distrib,
          ← smul_sub, sub_sub_cancel])
    have h1 : ∑ a, t a • z' a ∈ herrB D := by
      convert cob_mem D y using 1
      exact Prod.ext (funext fun i => (hy i).1) (funext fun i => (hy i).2)
    have h2 : ∑ a, t a • (z a - z' a) ∈ herrB D :=
      Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hz' a)
    have h3 : ∑ a, t a • z a ∈ herrB D := by
      convert (herrB D).add_mem h1 h2 using 1
      simp only [← Finset.sum_add_distrib, ← smul_add, add_sub_cancel]
    funext a
    refine Fintype.linearIndependent_iff.1 hli t ?_ a
    have h4 : (herrB D).mkQ (∑ a, t a • z a) = 0 := (Submodule.Quotient.mk_eq_zero _).2 h3
    simpa only [map_sum, map_smul] using h4

end GlobalTheory.Models.PolarBound
