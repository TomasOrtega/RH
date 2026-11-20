import Mathlib
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatDRSubsetLatHT
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.GrNormPos

/- English proof (translation)
Take `⟨l, hl⟩` from `LinearMap.exists_leftInverse_of_injective (Fintype.linearCombination C U) (LinearMap.ker_eq_bot.2 (linearIndependent_iff_injective_fintypeLinearCombination.1 hU))`. Establish `hl' : ∀ cf : Fin m → C, l (∑ k, cf k • U k) = cf` using `fun cf => by`. Use `LinearMap.congr_fun hl cf` as an intermediate fact. Rewrite `this` using `[LinearMap.comp_apply, Fintype.linearCombination_apply]`. Then use the resulting hypothesis. Use `set B : ℝ := ∑ j, ‖l (V j) i‖ + 1 with hB`.

Establish `hB0 : 0 < B` using `by positivity`. Establish `ha0 : 0 < ‖a‖` using `norm_pos_iff.2 ha`. Use `lt_of_lt_of_le (div_pos ha0 hB0) (le_csInf ?_ ?_)` and prove the remaining obligations. Take `⟨c, hc⟩` from `h1 (U i)`. Take `⟨e, he⟩` from `NormedField.exists_lt_norm C ‖c‖`.

Establish `he0 : 0 < ‖e‖` using `(norm_nonneg c).trans_lt he`. Establish `he1 : e ≠ 0` using `norm_pos_iff.1 he0`. Use `⟨_, Pi.single i e⁻¹, by simpa using he1, fun k hk => Pi.single_eq_of_ne hk.ne' _, ?_, rfl⟩` and prove the remaining obligations. Establish `: ∑ k, (Pi.single i e⁻¹ : Fin m → C) k • U k = ∑ j, (e⁻¹ * c j) • V j`. Rewrite using `[Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp), Pi.single_eq_same, hc, Finset.smul_sum]`.

Conclude with `Finset.sum_congr rfl fun j _ => smul_smul _ _ _`. Rewrite using `[this]`. Use `h2 _ fun j => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_inv, inv_mul_le_iff₀ he0, mul_one]`. Conclude with `(norm_le_pi_norm c j).trans he.le`.

Introduce and unpack `r ⟨cf, h0, -, hL, rfl⟩`. Take `⟨c, hc, e⟩` from `h3 _ hL`. Establish `e2 : a * cf i = ∑ j, c j * l (V j) i`. Use `congrArg (fun z => l z i) e` as an intermediate fact. Simplify `this` using `[map_smul, hl', map_sum, Finset.sum_apply]`.

Establish `e3 : ‖a‖ * ‖cf i‖ ≤ B`. Rewrite using `[← norm_mul, e2]`. Use `(norm_sum_le _ _).trans ((Finset.sum_le_sum fun j _ => ?_).trans (le_add_of_nonneg_right zero_le_one))` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (hc j)`.

Establish `h0' : 0 < ‖cf i‖` using `norm_pos_iff.2 h0`. Rewrite using `[div_le_iff₀ hB0, le_inv_mul_iff₀ h0', mul_comm]`. Conclude with `e3`.
-/
theorem sInf_pos {C M : Type} [NontriviallyNormedField C] [AddCommGroup M] [Module C M] {g m : ℕ} (V : Fin g → M)
    (U : Fin m → M) (hU : LinearIndependent C U) (L : Set M) (a : C) (ha : a ≠ 0)
    (h1 : ∀ w, ∃ c : Fin g → C, w = ∑ j, c j • V j)
    (h2 : ∀ c : Fin g → C, (∀ j, ‖c j‖ ≤ 1) → ∑ j, c j • V j ∈ L)
    (h3 : ∀ w ∈ L, ∃ c : Fin g → C, (∀ j, ‖c j‖ ≤ 1) ∧ a • w = ∑ j, c j • V j) (i : Fin m) :
    0 < sInf {r | ∃ cf : Fin m → C, cf i ≠ 0 ∧ (∀ k, i < k → cf k = 0) ∧ (∑ k, cf k • U k ∈ L) ∧
      r = ‖cf i‖⁻¹} := by
  classical
  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective (Fintype.linearCombination C U)
    (LinearMap.ker_eq_bot.2 (linearIndependent_iff_injective_fintypeLinearCombination.1 hU))
  have hl' : ∀ cf : Fin m → C, l (∑ k, cf k • U k) = cf := fun cf => by
    have := LinearMap.congr_fun hl cf
    rwa [LinearMap.comp_apply, Fintype.linearCombination_apply] at this
  set B : ℝ := ∑ j, ‖l (V j) i‖ + 1 with hB
  have hB0 : 0 < B := by positivity
  have ha0 : 0 < ‖a‖ := norm_pos_iff.2 ha
  refine lt_of_lt_of_le (div_pos ha0 hB0) (le_csInf ?_ ?_)
  · obtain ⟨c, hc⟩ := h1 (U i)
    obtain ⟨e, he⟩ := NormedField.exists_lt_norm C ‖c‖
    have he0 : 0 < ‖e‖ := (norm_nonneg c).trans_lt he
    have he1 : e ≠ 0 := norm_pos_iff.1 he0
    refine ⟨_, Pi.single i e⁻¹, by simpa using he1, fun k hk => Pi.single_eq_of_ne hk.ne' _, ?_, rfl⟩
    have : ∑ k, (Pi.single i e⁻¹ : Fin m → C) k • U k = ∑ j, (e⁻¹ * c j) • V j := by
      rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp), Pi.single_eq_same, hc,
        Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_smul _ _ _
    rw [this]
    refine h2 _ fun j => ?_
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ he0, mul_one]
    exact (norm_le_pi_norm c j).trans he.le
  · rintro r ⟨cf, h0, -, hL, rfl⟩
    obtain ⟨c, hc, e⟩ := h3 _ hL
    have e2 : a * cf i = ∑ j, c j * l (V j) i := by
      have := congrArg (fun z => l z i) e
      simpa [map_smul, hl', map_sum, Finset.sum_apply] using this
    have e3 : ‖a‖ * ‖cf i‖ ≤ B := by
      rw [← norm_mul, e2]
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun j _ => ?_).trans (le_add_of_nonneg_right zero_le_one))
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hc j)
    have h0' : 0 < ‖cf i‖ := norm_pos_iff.2 h0
    rw [div_le_iff₀ hB0, le_inv_mul_iff₀ h0', mul_comm]
    exact e3

open GlobalTheory.LieMet ReciprocityTheory.ChartRestriction.G.PullbackSections MonObj

attribute [local instance] Over.cartesianMonoidalCategory

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {S : Type} [CommRing S] {x : Sp S ⟶ X}

/- English proof (translation)
Establish `h0 : IsCombAtG t x u a (tv (∑ i, a i • tanOf (hu i))).left` using `(isComb_iff (fun i => tanOf (hu i)) a _).2 rfl`. Use `⟨fun h => ?_, fun h => h ▸ h0⟩` and prove the remaining obligations. Take `⟨v, hv, e⟩` from `h`. Take `⟨v', hv', e'⟩` from `h0`. Establish `: v = v'` using `funext fun i => Over.OverMorphism.ext ((hv i).trans (hv' i).symm)`.

Rewrite using `[← e, ← e', this]`.
-/
theorem isComb_iff_eq {m : ℕ} {u : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hu : ∀ i, IsTanAtG t x (u i))
    (a : Fin m → S) (w : Sp (DualNumber S) ⟶ t.G.left) :
    IsCombAtG t x u a w ↔ w = (tv (∑ i, a i • tanOf (hu i))).left := by
  have h0 : IsCombAtG t x u a (tv (∑ i, a i • tanOf (hu i))).left := (isComb_iff (fun i => tanOf (hu i)) a _).2 rfl
  refine ⟨fun h => ?_, fun h => h ▸ h0⟩
  obtain ⟨v, hv, e⟩ := h
  obtain ⟨v', hv', e'⟩ := h0
  have : v = v' := funext fun i => Over.OverMorphism.ext ((hv i).trans (hv' i).symm)
  rw [← e, ← e', this]

end

/- English proof (translation)
Introduce `hHT E _ _ _ H X t p C b xO hp huniq m u hu hinj i`. Use `haveI : Fact p.Prime := Fact.mk hp`. Take `⟨g, v, hv, hb, hL⟩` from `GlobalTheory.LatDRFree.latDR_free E H X t C.S xO huniq`. Establish `hp0 : (0 : ℝ) < p` using `Nat.cast_pos.2 hp.pos`. Establish `hp2 : (2 : ℝ) ≤ p` using `by exact_mod_cast hp.two_le`.

Establish `hpa : ‖(p : C.S)‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - 1)))`. Rewrite using `[C.norm_p, ← Real.rpow_neg_one]`. Use `Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg ?_)` and prove the remaining obligations. Rewrite using `[div_le_one (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hsub : latDR t (spMap (intO ↥C.S).subtype ≫ xO) ⊆ lat t p (spMap (intO ↥C.S).subtype ≫ xO) b`. Consider the cases of `b`. Conclude with `subset_rfl`. Conclude with `latDR_subset_latHT E H X t C.S p _`. Establish `hsup : lat t p (spMap (intO ↥C.S).subtype ≫ xO) b ⊆ latHT t p (spMap (intO ↥C.S).subtype ≫ xO)`.

Consider the cases of `b`. Conclude with `latDR_subset_latHT E H X t C.S p _`. Conclude with `subset_rfl`. Establish `h1 : ∀ w : TanM (spMap (intO ↥C.S).subtype ≫ xO) t.G, ∃ c : Fin g → C.S, w = ∑ j, c j • tanOf (hv j)` using `fun w => by`. Take `⟨c, hc, -⟩` from `hb _ (isTan_tv w)`.

Conclude with `⟨c, tan_ext ((isComb_iff_eq hv c _).1 hc)⟩`. Establish `key` using `sInf_pos (fun j => tanOf (hv j)) (fun k => tanOf (hu k)) ?_ {w | (tv w).left ∈ lat t p (spMap (intO ↥C.S).subtype ≫ xO) b} (p : C.S) (Nat.cast_ne_zero.2 hp.ne_zero) h1 ?_ ?_ i`. Unfold `GlobalTheory.ShFam.Pad.grNorm`. Use `key.trans_eq (congrArg sInf (Set.ext fun r => exists_congr fun cf => and_congr_right fun _ => and_congr_right fun _ => and_congr_left fun _ => Iff.symm ?_))` and prove the remaining obligations. Use `⟨?_, fun h => ⟨_, h, (isComb_iff_eq hu cf _).2 rfl⟩⟩` and prove the remaining obligations.

Introduce and unpack `⟨w, hw, hc⟩`. Rewrite `hw` using `[(isComb_iff_eq hu cf _).1 hc]`. Conclude with `hw`. Use `Fintype.linearIndependent_iff.2 fun c hc k => ?_` and prove the remaining obligations. Use `hinj c 0 _ ((isComb_iff_eq hu c _).2 rfl) ((isComb_iff_eq hu 0 _).2 (by rw [hc]; simp))` as an intermediate fact.

Conclude with `congrFun this k`. Introduce `c hc`. Conclude with `hsub ((hL c _ ((isComb_iff_eq hv c _).2 rfl)).2 hc)`. Introduce `w hw`. Establish `h` using `hHT E H X t p C.S C.norm_p xO huniq _ (hsup hw) (p : C.S) hpa`.

Take `⟨c, hc⟩` from `h1 ((p : C.S) • w)`. Use `⟨c, (hL c _ ((isComb_iff_eq hv c _).2 rfl)).1 ?_, hc⟩` and prove the remaining obligations. Rewrite using `[← hc]`. Conclude with `h`.
-/
theorem grNorm_pos : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (p : ℕ) (C : Formalism.MainNotions.DIV.Cons.SCF p) (b : Bool) (xO : Sp ↥(intO ↥C.S) ⟶ X), p.Prime → (∀ y : Sp ↥(intO ↥C.S) ⟶ X, spMap (intO ↥C.S).subtype ≫ y = spMap (intO ↥C.S).subtype ≫ xO → y = xO) → ∀ (m : ℕ) (u : Fin m → (Sp (DualNumber ↥C.S) ⟶ t.G.left)), (∀ i, IsTanAtG t (spMap (intO ↥C.S).subtype ≫ xO) (u i)) → (∀ cf cf' w, IsCombAtG t (spMap (intO ↥C.S).subtype ≫ xO) u cf w → IsCombAtG t (spMap (intO ↥C.S).subtype ≫ xO) u cf' w → cf = cf') → ∀ i, 0 < GlobalTheory.ShFam.Pad.grNorm t (spMap (intO ↥C.S).subtype ≫ xO) (lat t p (spMap (intO ↥C.S).subtype ≫ xO) b) u i := by
  intro hHT E _ _ _ H X t p C b xO hp huniq m u hu hinj i
  haveI : Fact p.Prime := Fact.mk hp
  obtain ⟨g, v, hv, hb, hL⟩ := GlobalTheory.LatDRFree.latDR_free E H X t C.S xO huniq
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.2 hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpa : ‖(p : C.S)‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) := by
    rw [C.norm_p, ← Real.rpow_neg_one]
    refine Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg ?_)
    rw [div_le_one (by linarith)]
    linarith
  have hsub : latDR t (spMap (intO ↥C.S).subtype ≫ xO) ⊆ lat t p (spMap (intO ↥C.S).subtype ≫ xO) b := by
    cases b
    · exact subset_rfl
    · exact latDR_subset_latHT E H X t C.S p _
  have hsup : lat t p (spMap (intO ↥C.S).subtype ≫ xO) b ⊆ latHT t p (spMap (intO ↥C.S).subtype ≫ xO) := by
    cases b
    · exact latDR_subset_latHT E H X t C.S p _
    · exact subset_rfl
  have h1 : ∀ w : TanM (spMap (intO ↥C.S).subtype ≫ xO) t.G, ∃ c : Fin g → C.S, w = ∑ j, c j • tanOf (hv j) :=
    fun w => by
      obtain ⟨c, hc, -⟩ := hb _ (isTan_tv w)
      exact ⟨c, tan_ext ((isComb_iff_eq hv c _).1 hc)⟩
  have key := sInf_pos (fun j => tanOf (hv j)) (fun k => tanOf (hu k)) ?_
    {w | (tv w).left ∈ lat t p (spMap (intO ↥C.S).subtype ≫ xO) b} (p : C.S) (Nat.cast_ne_zero.2 hp.ne_zero) h1
    ?_ ?_ i
  · unfold GlobalTheory.ShFam.Pad.grNorm
    refine key.trans_eq (congrArg sInf (Set.ext fun r => exists_congr fun cf => and_congr_right fun _ =>
      and_congr_right fun _ => and_congr_left fun _ => Iff.symm ?_))
    refine ⟨?_, fun h => ⟨_, h, (isComb_iff_eq hu cf _).2 rfl⟩⟩
    rintro ⟨w, hw, hc⟩
    rw [(isComb_iff_eq hu cf _).1 hc] at hw
    exact hw
  · refine Fintype.linearIndependent_iff.2 fun c hc k => ?_
    have := hinj c 0 _ ((isComb_iff_eq hu c _).2 rfl) ((isComb_iff_eq hu 0 _).2 (by rw [hc]; simp))
    exact congrFun this k
  · intro c hc
    exact hsub ((hL c _ ((isComb_iff_eq hv c _).2 rfl)).2 hc)
  · intro w hw
    have h := hHT E H X t p C.S C.norm_p xO huniq _ (hsup hw) (p : C.S) hpa
    obtain ⟨c, hc⟩ := h1 ((p : C.S) • w)
    refine ⟨c, (hL c _ ((isComb_iff_eq hv c _).2 rfl)).1 ?_, hc⟩
    rw [← hc]
    exact h

end GlobalTheory.GrNormPos
