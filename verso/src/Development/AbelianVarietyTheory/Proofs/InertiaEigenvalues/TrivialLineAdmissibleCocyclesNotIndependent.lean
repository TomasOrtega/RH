import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPhiGammaModelCharacterEqStandardStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPhiGammaModelExtensionCocyclePairStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmulAddStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCoboundariesOfHerrPairCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobSubOneBij
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleLetterDataWindowArithmetic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NabBijectiveWindow

noncomputable section
namespace GlobalTheory.TopSteps.TrivLine
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

/- English proof (translation)
Take `⟨n, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)`. Use `⟨fun i => -∑ j ∈ Finset.range (i.val + 1), c (j : ZMod (n + 1)), fun i => ?_⟩` and prove the remaining obligations. Establish `hall : ∑ j ∈ Finset.range (n + 1), c (j : ZMod (n + 1)) = 0`. Rewrite using `[← hc, Finset.sum_range]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Use `congr 1`. Conclude with `ZMod.natCast_zmod_val (n := n + 1) x`. Distinguish the cases in `hi : i = 0`. Substitute `hi` using the available equality. Establish `h1 : ((0 : ZMod (n + 1)) - 1).val = n`.

Rewrite using `[zero_sub]`. Conclude with `ZMod.val_neg_one n`. Simplify using `only [h1, ZMod.val_zero, hall]`. Simplify using the standard rewrite rules. Take `⟨j, hj⟩` from `Nat.exists_eq_succ_of_ne_zero (fun h => hi ((ZMod.val_eq_zero i).1 h))`.

Establish `hlt` using `ZMod.val_lt i`. Establish `hi' : i = ((j + 1 : ℕ) : ZMod (n + 1))`. Rewrite using `[show j + 1 = i.val from hj.symm, ZMod.natCast_zmod_val]`. Establish `h1 : (i - 1).val = j`. Establish `: i - 1 = (j : ZMod (n + 1))` using `by rw [hi']; push_cast; ring`.

Rewrite using `[this, ZMod.val_natCast_of_lt (by omega)]`. Simplify using `only [h1, hj, Nat.succ_eq_add_one]`. Rewrite using `[Finset.sum_range_succ _ (j + 1), ← hi']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_diff_of_sum_eq_zero {k : Type} [Field k] {n : ℕ} [NeZero n] (c : ZMod n → k) (hc : ∑ i, c i = 0) :
    ∃ d : ZMod n → k, ∀ i, c i = d (i - 1) - d i := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  refine ⟨fun i => -∑ j ∈ Finset.range (i.val + 1), c (j : ZMod (n + 1)), fun i => ?_⟩
  have hall : ∑ j ∈ Finset.range (n + 1), c (j : ZMod (n + 1)) = 0 := by
    rw [← hc, Finset.sum_range]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    exact ZMod.natCast_zmod_val (n := n + 1) x
  by_cases hi : i = 0
  · subst hi
    have h1 : ((0 : ZMod (n + 1)) - 1).val = n := by
      rw [zero_sub]; exact ZMod.val_neg_one n
    simp only [h1, ZMod.val_zero, hall]
    simp
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (fun h => hi ((ZMod.val_eq_zero i).1 h))
    have hlt := ZMod.val_lt i
    have hi' : i = ((j + 1 : ℕ) : ZMod (n + 1)) := by
      rw [show j + 1 = i.val from hj.symm, ZMod.natCast_zmod_val]
    have h1 : (i - 1).val = j := by
      have : i - 1 = (j : ZMod (n + 1)) := by rw [hi']; push_cast; ring
      rw [this, ZMod.val_natCast_of_lt (by omega)]
    simp only [h1, hj, Nat.succ_eq_add_one]
    rw [Finset.sum_range_succ _ (j + 1), ← hi']
    ring

variable {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l}

/- English proof (translation)
Establish `hω : M.ω ^ (-(0 : ℤ)) = 1` using `by simp`. Establish `ht : (0 : ℤ) < Dt.t` using `by exact_mod_cast Dt.one_le_letterBlockLength`. Establish `hlat` using `M.χ_lat 0 (by norm_num) ht i`. Rewrite `hlat` using `[hω]`. Take `⟨hL, hC, hP, hS⟩` from `hlat`.

Rewrite `hP` using `[sh_zero_eq]`. Take `⟨z0, z1, zG, zB⟩` from `hZ i`. Establish `hv` using `vv_ne_zero k`. Establish `hφ : (F.D (chr 1)).φ i (g (i - 1)) ∈ sh 1 (M.Nχ 0 i)`. Take `⟨y, hy, e⟩` from `mem_sh_iff_exists.1 (hZ (i - 1)).2.1`.

Take `⟨u, hu⟩` from `R.φ_v`. Take `⟨l', hl'⟩` from `Nat.exists_eq_add_of_le (Fact.out : l.Prime).one_le`. Establish `hy' : (F.D (chr 1)).φ i y ∈ M.Nχ 0 i`. Rewrite using `[← hP]`. Conclude with `Submodule.subset_span ⟨y, hy, rfl⟩`.

Use `mem_sh_iff_exists.2 ⟨((u : k⟦X⟧) * PowerSeries.X ^ l') • (F.D (chr 1)).φ i y, Submodule.smul_mem _ _ hy', ?_⟩` and prove the remaining obligations. Rewrite using `[← e, (F.D (chr 1)).φ_semi i, zpow_one, hu, ← algebraMap_smul k⸨X⸩ ((u : k⟦X⟧) * PowerSeries.X ^ l'), smul_smul]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `_ * (((u : k⟦X⟧) * PowerSeries.X ^ l' : k⟦X⟧) : k⸨X⸩) = _`. Rewrite using `[map_mul, map_pow, ← vv_eq_coe_X, hl']`.

Expand and normalize the polynomial expressions, which then agree. Establish `hnab : nab ((F.D (chr 1)).γ i) (b i) ∈ M.Nχ 0 i`. Use `mem_sh_iff_smul_mem.1 (Submodule.sub_mem _ hφ z1)` as an intermediate fact. Rewrite `this` using `[← z0, zpow_neg_one]`. Conclude with `this`.

Establish `key : ∀ J : ℤ, 0 ≤ J → J ≤ Dt.η i → b i ∈ sh (-J) (M.Nχ 0 i) → b i ∈ M.Nχ 0 i`. Introduce `J hJ hJ' hb`. Take `⟨m, rfl⟩` from `Int.eq_ofNat_of_zero_le hJ`. Establish `hl` using `h1 i`. Use `(GlobalTheory.PhiGam.Window.nab_bijective_window R _ ((F.D (chr 1)).γ_semi i) _ hL hC (-(m : ℤ)) m (by` as an intermediate fact.

Introduce `j hj`. Rewrite using `[hS, resCount, Multiset.card_eq_zero]`. Use `(@Multiset.filter_eq_nil _ _ (_) _).2 ?_` and prove the remaining obligations. Introduce `a ha e`. Rewrite `ha` using `[Multiset.mem_singleton]`.

Substitute `ha` using the available equality. Establish `e' : ((m - j : ℕ) : k) = 0`. Rewrite using `[Nat.cast_sub hj.le]`. Move the coercions through the operations in `at e`. Take the linear combination `e`.

Use `Nat.le_of_dvd (by omega) ((CharP.cast_eq_zero_iff k l _).1 e')` as an intermediate fact. Use the proof step `omega)).1 (b i) hb (by rw [neg_add_cancel, sh_zero_eq]; exact hnab)`. Rewrite `this` using `[neg_add_cancel, sh_zero_eq]`. Then use the resulting hypothesis. Take `⟨-, -, wG, wB⟩` from `GlobalTheory.WindowArith.windows (k := k) Dt h1 h2 h3 i`. Consider the cases of `hty : Dt.ty i with`.

Consider the case `G`. Take `⟨-, -, a1, a2⟩` from `wG hty`. Conclude with `key _ (by omega) (by omega) (zG hty)`. Consider the case `Bd`. Take `⟨-, -, a1, a2⟩` from `wB hty`.

Use `(zB hty).1` as an intermediate fact. Rewrite `this` using `[hP]`. Conclude with `key _ (by omega) a2 this`.
-/
theorem mem_of_inZZ (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (h1 : Dt.T1 l) (h2 : Dt.T2 l)
    (h3 : Dt.T3 l) (b g : ZMod n → Vc k 1) (hZ : InZZ (F.D (chr 1)) Dt (M.Nχ 0) b g) (i : ZMod n) :
    b i ∈ M.Nχ 0 i := by
  have hω : M.ω ^ (-(0 : ℤ)) = 1 := by simp
  have ht : (0 : ℤ) < Dt.t := by exact_mod_cast Dt.one_le_letterBlockLength
  have hlat := M.χ_lat 0 (by norm_num) ht i
  rw [hω] at hlat
  obtain ⟨hL, hC, hP, hS⟩ := hlat
  rw [sh_zero_eq] at hP
  obtain ⟨z0, z1, zG, zB⟩ := hZ i
  have hv := vv_ne_zero k
  have hφ : (F.D (chr 1)).φ i (g (i - 1)) ∈ sh 1 (M.Nχ 0 i) := by
    obtain ⟨y, hy, e⟩ := mem_sh_iff_exists.1 (hZ (i - 1)).2.1
    obtain ⟨u, hu⟩ := R.φ_v
    obtain ⟨l', hl'⟩ := Nat.exists_eq_add_of_le (Fact.out : l.Prime).one_le
    have hy' : (F.D (chr 1)).φ i y ∈ M.Nχ 0 i := by
      rw [← hP]; exact Submodule.subset_span ⟨y, hy, rfl⟩
    refine mem_sh_iff_exists.2 ⟨((u : k⟦X⟧) * PowerSeries.X ^ l') • (F.D (chr 1)).φ i y,
      Submodule.smul_mem _ _ hy', ?_⟩
    rw [← e, (F.D (chr 1)).φ_semi i, zpow_one, hu, ← algebraMap_smul k⸨X⸩ ((u : k⟦X⟧) * PowerSeries.X ^ l'),
      smul_smul]
    congr 1
    change _ * (((u : k⟦X⟧) * PowerSeries.X ^ l' : k⟦X⟧) : k⸨X⸩) = _
    rw [map_mul, map_pow, ← vv_eq_coe_X, hl']
    ring
  have hnab : nab ((F.D (chr 1)).γ i) (b i) ∈ M.Nχ 0 i := by
    have := mem_sh_iff_smul_mem.1 (Submodule.sub_mem _ hφ z1)
    rw [← z0, zpow_neg_one] at this
    exact this
  have key : ∀ J : ℤ, 0 ≤ J → J ≤ Dt.η i → b i ∈ sh (-J) (M.Nχ 0 i) → b i ∈ M.Nχ 0 i := by
    intro J hJ hJ' hb
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hJ
    have hl := h1 i
    have := (GlobalTheory.PhiGam.Window.nab_bijective_window R _ ((F.D (chr 1)).γ_semi i) _ hL hC (-(m : ℤ)) m (by
      intro j hj
      rw [hS, resCount, Multiset.card_eq_zero]
      refine (@Multiset.filter_eq_nil _ _ (_) _).2 ?_
      intro a ha e
      rw [Multiset.mem_singleton] at ha
      subst ha
      have e' : ((m - j : ℕ) : k) = 0 := by
        rw [Nat.cast_sub hj.le]
        push_cast at e
        linear_combination e
      have := Nat.le_of_dvd (by omega) ((CharP.cast_eq_zero_iff k l _).1 e')
      omega)).1 (b i) hb (by rw [neg_add_cancel, sh_zero_eq]; exact hnab)
    rwa [neg_add_cancel, sh_zero_eq] at this
  obtain ⟨-, -, wG, wB⟩ := GlobalTheory.WindowArith.windows (k := k) Dt h1 h2 h3 i
  cases hty : Dt.ty i with
  | G =>
    obtain ⟨-, -, a1, a2⟩ := wG hty
    exact key _ (by omega) (by omega) (zG hty)
  | Bd =>
    obtain ⟨-, -, a1, a2⟩ := wB hty
    have := (zB hty).1
    rw [hP] at this
    exact key _ (by omega) a2 this

/- English proof (translation)
Take `⟨N, b, g, hN, hR, hZ⟩` from `GlobalTheory.T.exists_phiGammaModel_extension_cocycle_pair F M h1 h2 h3 (chr 1) z hz`. Establish `hω : M.ω ^ (-(0 : ℤ)) = 1` using `by simp`. Establish `ht : (0 : ℤ) < Dt.t` using `by exact_mod_cast Dt.one_le_letterBlockLength`. Establish `hCH` using `GlobalTheory.T.twistedPhiGammaModel_character_eq_standard F M h1 h2 h3 0 le_rfl ht N`. Rewrite `hCH` using `[hω]`.

Take `rfl` from `hCH hN`. Establish `hb : ∀ i, ∃ β : k⟦X⟧, b i = (β : k⸨X⸩) • F.unit i` using `fun i => by`. Use `mem_of_inZZ F M h1 h2 h3 b g hZ i` as an intermediate fact. Rewrite `this` using `[M.χ_zero, Submodule.mem_span_singleton]`. Take `⟨β, e⟩` from `this`.

Conclude with `⟨β, by rw [← e, ← algebraMap_smul k⸨X⸩ β]; rfl⟩`. Establish `hg : ∀ i, ∃ β : k⟦X⟧, PowerSeries.constantCoeff β = 0 ∧ g i = (β : k⸨X⸩) • F.unit i` using `fun i => by`. Take `⟨y, hy, e⟩` from `mem_sh_iff_exists.1 (hZ i).2.1`. Rewrite `hy` using `[M.χ_zero, Submodule.mem_span_singleton]`. Take `⟨β, rfl⟩` from `hy`.

Use `⟨PowerSeries.X * β, by simp, ?_⟩` and prove the remaining obligations. Rewrite using `[← e, ← algebraMap_smul k⸨X⸩ β, zpow_one, smul_smul, map_mul, ← vv_eq_coe_X]`. Both sides reduce to the same expression. Use `choose β hβ using hb`. Use `choose δ hδ0 hδ using hg`.

Establish `eφ : ∀ i (a : k⸨X⸩), (F.D (chr 1)).φ i (a • F.unit (i - 1)) = R.φ a • F.unit i` using `fun i a => by`. Rewrite using `[(F.D (chr 1)).φ_semi i, F.unit_φ]`. Establish `eγ : ∀ i (a : k⸨X⸩), (F.D (chr 1)).γ i (a • F.unit i) = R.γ a • F.unit i` using `fun i a => by`. Rewrite using `[(F.D (chr 1)).γ_semi i, F.unit_γ]`. Take `⟨m, c, hm⟩` from `GlobalTheory.PhiGam.TrivCocycle.main R β δ hδ0 (fun i => by`.

Establish `e` using `(hZ i).1`. Rewrite `e` using `[hβ i, hδ i, hδ (i - 1), eφ, eγ, ← sub_smul, ← sub_smul]`. Conclude with `smul_left_injective _ (F.unit_ne i) e)`. Use `⟨b, g, fun i => (m i : k⸨X⸩) • F.unit i, c, hR, fun i => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hβ, (hm i).1, eφ, add_smul, sub_smul]`.

Use `congr 1`. Use function extensionality and compare the values at `j`. Simplify using `only [Pi.smul_apply, smul_eq_mul, const_smul_eq]`. Rewrite using `[hδ, (hm i).2, eγ, sub_smul]`.
-/
theorem exists_const_pair (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (h1 : Dt.T1 l)
    (h2 : Dt.T2 l) (h3 : Dt.T3 l) (z : G → Fin 1 → k) (hz : z ∈ M.twistedModelAdmissibleCocycles (chr 1)) :
    ∃ (b g m : ZMod n → Vc k 1) (c : ZMod n → k), Repr F (chr 1) z b g ∧
      ∀ i, b i = (F.D (chr 1)).φ i (m (i - 1)) - m i + c i • F.unit i ∧ g i = (F.D (chr 1)).γ i (m i) - m i := by
  obtain ⟨N, b, g, hN, hR, hZ⟩ := GlobalTheory.T.exists_phiGammaModel_extension_cocycle_pair F M h1 h2 h3 (chr 1) z hz
  have hω : M.ω ^ (-(0 : ℤ)) = 1 := by simp
  have ht : (0 : ℤ) < Dt.t := by exact_mod_cast Dt.one_le_letterBlockLength
  have hCH := GlobalTheory.T.twistedPhiGammaModel_character_eq_standard F M h1 h2 h3 0 le_rfl ht N
  rw [hω] at hCH
  obtain rfl := hCH hN
  have hb : ∀ i, ∃ β : k⟦X⟧, b i = (β : k⸨X⸩) • F.unit i := fun i => by
    have := mem_of_inZZ F M h1 h2 h3 b g hZ i
    rw [M.χ_zero, Submodule.mem_span_singleton] at this
    obtain ⟨β, e⟩ := this
    exact ⟨β, by rw [← e, ← algebraMap_smul k⸨X⸩ β]; rfl⟩
  have hg : ∀ i, ∃ β : k⟦X⟧, PowerSeries.constantCoeff β = 0 ∧ g i = (β : k⸨X⸩) • F.unit i := fun i => by
    obtain ⟨y, hy, e⟩ := mem_sh_iff_exists.1 (hZ i).2.1
    rw [M.χ_zero, Submodule.mem_span_singleton] at hy
    obtain ⟨β, rfl⟩ := hy
    refine ⟨PowerSeries.X * β, by simp, ?_⟩
    rw [← e, ← algebraMap_smul k⸨X⸩ β, zpow_one, smul_smul, map_mul, ← vv_eq_coe_X]; rfl
  choose β hβ using hb
  choose δ hδ0 hδ using hg
  have eφ : ∀ i (a : k⸨X⸩), (F.D (chr 1)).φ i (a • F.unit (i - 1)) = R.φ a • F.unit i := fun i a => by
    rw [(F.D (chr 1)).φ_semi i, F.unit_φ]
  have eγ : ∀ i (a : k⸨X⸩), (F.D (chr 1)).γ i (a • F.unit i) = R.γ a • F.unit i := fun i a => by
    rw [(F.D (chr 1)).γ_semi i, F.unit_γ]
  obtain ⟨m, c, hm⟩ := GlobalTheory.PhiGam.TrivCocycle.main R β δ hδ0 (fun i => by
    have e := (hZ i).1
    rw [hβ i, hδ i, hδ (i - 1), eφ, eγ, ← sub_smul, ← sub_smul] at e
    exact smul_left_injective _ (F.unit_ne i) e)
  refine ⟨b, g, fun i => (m i : k⸨X⸩) • F.unit i, c, hR, fun i => ⟨?_, ?_⟩⟩
  · rw [hβ, (hm i).1, eφ, add_smul, sub_smul]
    congr 1
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, const_smul_eq]
  · rw [hδ, (hm i).2, eγ, sub_smul]

/- English proof (translation)
Introduce `k G _ _ l n _ _ _ R F r Dt M h1 h2 h3 z hz hli`. Use `choose b g m c hR hm using fun a => exists_const_pair F M h1 h2 h3 (z a) (hz a)`. Establish `key : ∀ (p q : Fin 2) (x : k), x * ∑ i, c p i + ∑ i, c q i = 0 → x • (cob (chr (1 : G →* kˣ))).mkQ (z p) + (cob (chr (1 : G →* kˣ))).mkQ (z q) = 0`. Introduce `p q x hx`. Take `⟨d, hd⟩` from `exists_diff_of_sum_eq_zero (fun i => x * c p i + c q i) (by rw [Finset.sum_add_distrib, ← Finset.mul_sum, hx])`.

Establish `hr` using `GlobalTheory.T.repr_smul_add F (chr 1) x (z p) (z q) _ _ _ _ (hR p) (hR q)`. Establish `h0` using `GlobalTheory.T.mem_coboundaries_of_herrPair_coboundary F (chr 1) _ _ _ hr (by`. Use `⟨fun i => x • m p i + m q i + d i • F.unit i, Prod.ext (funext fun i => ?_) (funext fun i => ?_)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(F.D (chr 1)).φ i (x • m p (i - 1) + m q (i - 1) + d (i - 1) • F.unit (i - 1)) - (x • m p i + m q i + d i • F.unit i) = x • b p i + b q i`. Establish `e : d (i - 1) = x * c p i + c q i + d i` using `by rw [hd i]; ring`.

Rewrite using `[map_add, map_add, map_smul, map_smul, F.unit_φ, (hm p i).1, (hm q i).1, e]`. Use `module`. Express the relevant statement in the definitionally equal form `(F.D (chr 1)).γ i (x • m p i + m q i + d i • F.unit i) - (x • m p i + m q i + d i • F.unit i) = x • g p i + g q i`. Rewrite using `[map_add, map_add, map_smul, map_smul, F.unit_γ, (hm p i).2, (hm q i).2]`. Use the proof step `module)`.

Rewrite using `[← map_smul, ← map_add]`. Conclude with `(Submodule.Quotient.mk_eq_zero _).2 h0`. Rewrite `hli` using `[Fintype.linearIndependent_iff]`. Distinguish the cases in `hs : ∑ i, c 0 i = 0`. Use `hli ![1, 0] (by` as an intermediate fact.

Rewrite using `[Fin.sum_univ_two, add_comm]`. Use `key 1 0 0 (by rw [hs]; ring)` as an intermediate fact. Simplify using `using this) 0`. Simplify using `at this`. Use `hli ![-(∑ i, c 1 i) / ∑ i, c 0 i, 1] (by` as an intermediate fact.

Rewrite using `[Fin.sum_univ_two]`. Use `key 0 1 (-(∑ i, c 1 i) / ∑ i, c 0 i) (by field_simp; ring)` as an intermediate fact. Simplify using `using this) 1`. Simplify using `at this`.
-/
theorem main : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ z : Fin 2 → G → Fin 1 → k, (∀ a, z a ∈ M.twistedModelAdmissibleCocycles (chr 1)) → ¬ LinearIndependent k (fun a => (cob (chr (1 : G →* kˣ))).mkQ (z a)) := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 h2 h3 z hz hli
  choose b g m c hR hm using fun a => exists_const_pair F M h1 h2 h3 (z a) (hz a)
  have key : ∀ (p q : Fin 2) (x : k), x * ∑ i, c p i + ∑ i, c q i = 0 →
      x • (cob (chr (1 : G →* kˣ))).mkQ (z p) + (cob (chr (1 : G →* kˣ))).mkQ (z q) = 0 := by
    intro p q x hx
    obtain ⟨d, hd⟩ := exists_diff_of_sum_eq_zero (fun i => x * c p i + c q i)
      (by rw [Finset.sum_add_distrib, ← Finset.mul_sum, hx])
    have hr := GlobalTheory.T.repr_smul_add F (chr 1) x (z p) (z q) _ _ _ _ (hR p) (hR q)
    have h0 := GlobalTheory.T.mem_coboundaries_of_herrPair_coboundary F (chr 1) _ _ _ hr (by
      refine ⟨fun i => x • m p i + m q i + d i • F.unit i, Prod.ext (funext fun i => ?_) (funext fun i => ?_)⟩
      · change (F.D (chr 1)).φ i (x • m p (i - 1) + m q (i - 1) + d (i - 1) • F.unit (i - 1)) -
          (x • m p i + m q i + d i • F.unit i) = x • b p i + b q i
        have e : d (i - 1) = x * c p i + c q i + d i := by rw [hd i]; ring
        rw [map_add, map_add, map_smul, map_smul, F.unit_φ, (hm p i).1, (hm q i).1, e]
        module
      · change (F.D (chr 1)).γ i (x • m p i + m q i + d i • F.unit i) -
          (x • m p i + m q i + d i • F.unit i) = x • g p i + g q i
        rw [map_add, map_add, map_smul, map_smul, F.unit_γ, (hm p i).2, (hm q i).2]
        module)
    rw [← map_smul, ← map_add]
    exact (Submodule.Quotient.mk_eq_zero _).2 h0
  rw [Fintype.linearIndependent_iff] at hli
  by_cases hs : ∑ i, c 0 i = 0
  · have := hli ![1, 0] (by
      rw [Fin.sum_univ_two, add_comm]
      have := key 1 0 0 (by rw [hs]; ring)
      simpa using this) 0
    simp at this
  · have := hli ![-(∑ i, c 1 i) / ∑ i, c 0 i, 1] (by
      rw [Fin.sum_univ_two]
      have := key 0 1 (-(∑ i, c 1 i) / ∑ i, c 0 i) (by field_simp; ring)
      simpa using this) 1
    simp at this

end GlobalTheory.TopSteps.TrivLine
