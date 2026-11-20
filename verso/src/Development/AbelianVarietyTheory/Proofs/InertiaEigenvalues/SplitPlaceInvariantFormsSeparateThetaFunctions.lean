import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasShape
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepsLatticeQuotientConjugateHalfOrthogonalStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaCoefficientIsSchwartzBruhatUniformSplitStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmVacuumEqSplitFacSmulSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

namespace GlobalTheory.DownLift.SplitSep

open GlobalTheory.SplitScalar

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rw [zero_nsmul, zero_nsmul, symplO_zero_left]`. Consider the case `succ n ih => rw [succ_nsmul, succ_nsmul, GlobalTheory.LatVac.symplO_add_left, ih]`.
-/
theorem symplO_nsmul_left (k : ℕ) (x y : WO S T) : symplO S T (k • x) y = k • symplO S T x y := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, symplO_zero_left]
  | succ n ih => rw [succ_nsmul, succ_nsmul, GlobalTheory.LatVac.symplO_add_left, ih]

/- English proof (translation)
Rewrite using `[symplO_nsmul_left, symplO_skew S T (k • y) x, symplO_nsmul_left, symplO_skew S T x y, neg_nsmul, neg_neg]`.
-/
theorem symplO_nsmul_swap (k : ℕ) (x y : WO S T) : symplO S T (k • x) y = symplO S T x (k • y) := by
  rw [symplO_nsmul_left, symplO_skew S T (k • y) x, symplO_nsmul_left, symplO_skew S T x y, neg_nsmul, neg_neg]

/- English proof (translation)
Establish `h` using `symplO_sub_left S T 0 x y`. Rewrite `h` using `[zero_sub, symplO_zero_left, zero_sub]`. Then use the resulting hypothesis.
-/
theorem symplO_neg_left (x y : WO S T) : symplO S T (-x) y = -symplO S T x y := by
  have h := symplO_sub_left S T 0 x y
  rwa [zero_sub, symplO_zero_left, zero_sub] at h

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rw [zero_nsmul, zero_nsmul, smul_zero]`. Consider the case `succ n ih => rw [succ_nsmul, succ_nsmul, smul_add, ih]`.
-/
theorem nsmul_smul_comm (k : ℕ) (a : AE D) (v : WO S T) : k • (a • v) = a • (k • v) := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, smul_zero]
  | succ n ih => rw [succ_nsmul, succ_nsmul, smul_add, ih]

/- English proof (translation)
Rewrite `*` using `[isHalf_iff]`. Rewrite using `[smul_neg, hu]`.
-/
theorem isHalf_neg' {m n : ℕ} {e : AE D} {u : Mx D m n} (hu : IsHalf e u) : IsHalf e (-u) := by
  rw [isHalf_iff] at *
  rw [smul_neg, hu]

/- English proof (translation)
Rewrite using `[← (isHalf_iff _ _).1 hu, smul_smul, ha.2.1, zero_smul]`.
-/
theorem smul_eq_zero_of_half_conj {a : AE D} (ha : IsSplitIdem D a) {u : WO S T} (hu : IsHalf (cA D a) u) :
    a • u = 0 := by
  rw [← (isHalf_iff _ _).1 hu, smul_smul, ha.2.1, zero_smul]

/- English proof (translation)
Rewrite using `[← (isHalf_iff _ _).1 hu, smul_smul, mul_comm, ha.2.1, zero_smul]`.
-/
theorem conj_smul_eq_zero_of_half {a : AE D} (ha : IsSplitIdem D a) {u : WO S T} (hu : IsHalf a u) :
    cA D a • u = 0 := by
  rw [← (isHalf_iff _ _).1 hu, smul_smul, mul_comm, ha.2.1, zero_smul]

/- English proof (translation)
Use `⟨{ carrier := {d | ∃ v ∈ Λ, d = k • v} add_mem' := ?_, zero_mem' := ?_, neg_mem' := ?_ }, fun d => Iff.rfl⟩` and prove the remaining obligations. Introduce and unpack `u w ⟨v, hv, rfl⟩ ⟨v', hv', rfl⟩`. Conclude with `⟨v + v', add_mem hv hv', by rw [nsmul_add]⟩`. Conclude with `⟨0, zero_mem _, by rw [nsmul_zero]⟩`. Introduce and unpack `u ⟨v, hv, rfl⟩`.

Conclude with `⟨-v, neg_mem hv, by rw [neg_nsmul]⟩`.
-/
theorem exists_nsmul_subgroup (Λ : AddSubgroup (WO S T)) (k : ℕ) :
    ∃ K : AddSubgroup (WO S T), ∀ d, d ∈ K ↔ ∃ v ∈ Λ, d = k • v := by
  refine ⟨{ carrier := {d | ∃ v ∈ Λ, d = k • v}
            add_mem' := ?_, zero_mem' := ?_, neg_mem' := ?_ }, fun d => Iff.rfl⟩
  · rintro u w ⟨v, hv, rfl⟩ ⟨v', hv', rfl⟩
    exact ⟨v + v', add_mem hv hv', by rw [nsmul_add]⟩
  · exact ⟨0, zero_mem _, by rw [nsmul_zero]⟩
  · rintro u ⟨v, hv, rfl⟩
    exact ⟨-v, neg_mem hv, by rw [neg_nsmul]⟩

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨Λ', hΛ'⟩ : ∃ Λ' : AddSubgroup (WO S T), ∀ u, u ∈ Λ' ↔ (∃ v ∈ Λ, a • u = k • v) ∧ k • (cA D a • u) ∈ Λ := by`. Use `⟨{ carrier := {u | (∃ v ∈ Λ, a • u = k • v) ∧ k • (cA D a • u) ∈ Λ} add_mem' := ?_, zero_mem' := ?_, neg_mem' := ?_ }, fun u => Iff.rfl⟩` and prove the remaining obligations. Introduce and unpack `u w ⟨⟨v, hv, huv⟩, hu⟩ ⟨⟨v', hv', hwv⟩, hw⟩`. Use `⟨⟨v + v', add_mem hv hv', by rw [smul_add, huv, hwv, nsmul_add]⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, nsmul_add]`.

Conclude with `add_mem hu hw`. Use `⟨⟨0, zero_mem _, by rw [smul_zero, nsmul_zero]⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_zero, nsmul_zero]`. Conclude with `zero_mem _`. Introduce and unpack `u ⟨⟨v, hv, huv⟩, hu⟩`.

Use `⟨⟨-v, neg_mem hv, by rw [smul_neg, huv, neg_nsmul]⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_neg, neg_nsmul]`. Conclude with `neg_mem hu`. Use `⟨Λ', fun u hu => ?_, fun u hu => ?_⟩` and prove the remaining obligations. Rewrite using `[hΛ', (isHalf_iff _ _).1 hu, conj_smul_eq_zero_of_half ha hu, nsmul_zero]`.

Conclude with `⟨fun h => h.1, fun h => ⟨h, zero_mem _⟩⟩`. Establish `h0 : a • u = 0` using `smul_eq_zero_of_half_conj ha hu`. Establish `h1 : cA D a • u = u` using `(isHalf_iff _ _).1 hu`. Rewrite using `[hΛ']`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨-, h⟩`. Rewrite `h` using `[h1]`. Then use the resulting hypothesis. Introduce `h`. Conclude with `⟨⟨0, zero_mem _, by rw [h0, nsmul_zero]⟩, by rwa [h1]⟩`.
-/
theorem exists_mixed_subgroup {a : AE D} (ha : IsSplitIdem D a) (Λ : AddSubgroup (WO S T)) (k : ℕ) :
    ∃ Λ' : AddSubgroup (WO S T), (∀ u, IsHalf a u → (u ∈ Λ' ↔ ∃ v ∈ Λ, u = k • v)) ∧
      ∀ u, IsHalf (cA D a) u → (u ∈ Λ' ↔ k • u ∈ Λ) := by
  obtain ⟨Λ', hΛ'⟩ : ∃ Λ' : AddSubgroup (WO S T),
      ∀ u, u ∈ Λ' ↔ (∃ v ∈ Λ, a • u = k • v) ∧ k • (cA D a • u) ∈ Λ := by
    refine ⟨{ carrier := {u | (∃ v ∈ Λ, a • u = k • v) ∧ k • (cA D a • u) ∈ Λ}
              add_mem' := ?_, zero_mem' := ?_, neg_mem' := ?_ }, fun u => Iff.rfl⟩
    · rintro u w ⟨⟨v, hv, huv⟩, hu⟩ ⟨⟨v', hv', hwv⟩, hw⟩
      refine ⟨⟨v + v', add_mem hv hv', by rw [smul_add, huv, hwv, nsmul_add]⟩, ?_⟩
      rw [smul_add, nsmul_add]
      exact add_mem hu hw
    · refine ⟨⟨0, zero_mem _, by rw [smul_zero, nsmul_zero]⟩, ?_⟩
      rw [smul_zero, nsmul_zero]
      exact zero_mem _
    · rintro u ⟨⟨v, hv, huv⟩, hu⟩
      refine ⟨⟨-v, neg_mem hv, by rw [smul_neg, huv, neg_nsmul]⟩, ?_⟩
      rw [smul_neg, neg_nsmul]
      exact neg_mem hu
  refine ⟨Λ', fun u hu => ?_, fun u hu => ?_⟩
  · rw [hΛ', (isHalf_iff _ _).1 hu, conj_smul_eq_zero_of_half ha hu, nsmul_zero]
    exact ⟨fun h => h.1, fun h => ⟨h, zero_mem _⟩⟩
  · have h0 : a • u = 0 := smul_eq_zero_of_half_conj ha hu
    have h1 : cA D a • u = u := (isHalf_iff _ _).1 hu
    rw [hΛ']
    constructor
    · rintro ⟨-, h⟩
      rwa [h1] at h
    · intro h
      exact ⟨⟨0, zero_mem _, by rw [h0, nsmul_zero]⟩, by rwa [h1]⟩

/- English proof (translation)
Take `⟨v, hv, h⟩` from `h`. Conclude with `⟨e • v, hstab v hv, isHalf_smul he v, by rw [nsmul_smul_comm, ← h, (isHalf_iff _ _).1 hd]⟩`.
-/
theorem rep_half {e : AE D} (he : e * e = e) {Λ : AddSubgroup (WO S T)} (hstab : ∀ u ∈ Λ, e • u ∈ Λ) {k : ℕ}
    {d : WO S T} (hd : IsHalf e d) (h : ∃ v ∈ Λ, d = k • v) : ∃ v ∈ Λ, IsHalf e v ∧ d = k • v := by
  obtain ⟨v, hv, h⟩ := h
  exact ⟨e • v, hstab v hv, isHalf_smul he v, by rw [nsmul_smul_comm, ← h, (isHalf_iff _ _).1 hd]⟩

/- English proof (translation)
Establish `e1 : ∀ x ∈ X, heisO ψ S T (-x) (∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f)) = ∑ y ∈ Y, ψ (symplO S T y x) • heisO ψ S T y f`. Introduce `x hx`. Rewrite using `[heisO_sum]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[heisO_comm, ← heisO_add_of_orth ψ S T (half_orth ha (isHalf_neg' (hX x hx)) (hX x hx)), neg_add_cancel, heisO_zero, symplO_neg_left, ← symplO_skew]`.

Rewrite using `[Finset.sum_congr rfl e1, Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.sum_smul]`. Take `⟨y₀, ⟨hy₀Y, u₀, hu₀, hu₀h, hy₀⟩, huniq⟩` from `hYu 0 (isHalf_zero _) (by rw [nsmul_zero]; exact zero_mem _)`. Rewrite using `[Finset.sum_eq_single_of_mem y₀ hy₀Y]`. Establish `hy₀' : y₀ = k • (-u₀)` using `by rw [neg_nsmul, ← hy₀, zero_sub, neg_neg]`.

Establish `hyy : ∃ u ∈ Λ, IsHalf (cA D a) u ∧ y₀ = k • u` using `⟨-u₀, neg_mem hu₀, isHalf_neg' hu₀h, hy₀'⟩`. Rewrite using `[Finset.sum_congr rfl ((hXo y₀ (hY y₀ hy₀Y).1 (hY y₀ hy₀Y).2).1 hyy), Finset.sum_const, nsmul_eq_mul, mul_one, hy₀', hfix _ (neg_mem hu₀) (isHalf_neg' hu₀h)]`. Introduce `y hy hne`. Establish `hnot : ¬ ∃ u ∈ Λ, IsHalf (cA D a) u ∧ y = k • u`. Introduce and unpack `⟨u, hu, huh, rfl⟩`.

Conclude with `hne (huniq _ ⟨hy, -u, neg_mem hu, isHalf_neg' huh, by rw [zero_sub, neg_nsmul]⟩)`. Rewrite using `[(hXo y (hY y hy).1 (hY y hy).2).2 hnot, zero_smul]`.
-/
theorem sum_average {a : AE D} (ha : IsSplitIdem D a) {Λ : AddSubgroup (WO S T)} {k : ℕ} {f : WO S T → ℂ}
    (hfix : ∀ u ∈ Λ, IsHalf (cA D a) u → heisO ψ S T (k • u) f = f)
    {Y X : Finset (WO S T)}
    (hY : ∀ y ∈ Y, IsHalf (cA D a) y ∧ k • y ∈ Λ)
    (hYu : ∀ y', IsHalf (cA D a) y' → k • y' ∈ Λ →
      ∃! y, y ∈ Y ∧ ∃ u ∈ Λ, IsHalf (cA D a) u ∧ y' - y = k • u)
    (hX : ∀ x ∈ X, IsHalf a x)
    (hXo : ∀ y, IsHalf (cA D a) y → k • y ∈ Λ →
      ((∃ u ∈ Λ, IsHalf (cA D a) u ∧ y = k • u) → ∀ x ∈ X, ψ (symplO S T y x) = 1) ∧
      ((¬ ∃ u ∈ Λ, IsHalf (cA D a) u ∧ y = k • u) → ∑ x ∈ X, ψ (symplO S T y x) = 0)) :
    ∑ x ∈ X, heisO ψ S T (-x) (∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f)) = (X.card : ℂ) • f := by
  have e1 : ∀ x ∈ X, heisO ψ S T (-x) (∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f)) =
      ∑ y ∈ Y, ψ (symplO S T y x) • heisO ψ S T y f := by
    intro x hx
    rw [heisO_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [heisO_comm, ← heisO_add_of_orth ψ S T (half_orth ha (isHalf_neg' (hX x hx)) (hX x hx)),
      neg_add_cancel, heisO_zero, symplO_neg_left, ← symplO_skew]
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  obtain ⟨y₀, ⟨hy₀Y, u₀, hu₀, hu₀h, hy₀⟩, huniq⟩ :=
    hYu 0 (isHalf_zero _) (by rw [nsmul_zero]; exact zero_mem _)
  rw [Finset.sum_eq_single_of_mem y₀ hy₀Y]
  · have hy₀' : y₀ = k • (-u₀) := by rw [neg_nsmul, ← hy₀, zero_sub, neg_neg]
    have hyy : ∃ u ∈ Λ, IsHalf (cA D a) u ∧ y₀ = k • u := ⟨-u₀, neg_mem hu₀, isHalf_neg' hu₀h, hy₀'⟩
    rw [Finset.sum_congr rfl ((hXo y₀ (hY y₀ hy₀Y).1 (hY y₀ hy₀Y).2).1 hyy), Finset.sum_const, nsmul_eq_mul,
      mul_one, hy₀', hfix _ (neg_mem hu₀) (isHalf_neg' hu₀h)]
  · intro y hy hne
    have hnot : ¬ ∃ u ∈ Λ, IsHalf (cA D a) u ∧ y = k • u := by
      rintro ⟨u, hu, huh, rfl⟩
      exact hne (huniq _ ⟨hy, -u, neg_mem hu, isHalf_neg' huh, by rw [zero_sub, neg_nsmul]⟩)
    rw [(hXo y (hY y hy).1 (hY y hy).2).2 hnot, zero_smul]

/- English proof (translation)
Establish `ha'` using `isSplitIdem_conj ha`. Establish `hcc : cA D (cA D a) = a` using `GlobalTheory.DualPairCheck.cA_cA a`. Take `⟨K, hK⟩` from `exists_nsmul_subgroup Λ k`. Take `⟨Λ', memA, memC⟩` from `exists_mixed_subgroup ha Λ k`. Establish `hYK : ∀ u', IsHalf (cA D a) u' → k • u' ∈ Λ → ∃! v, v ∈ Y ∧ u' - v ∈ K`.

Introduce `u' hu' hku'`. Take `⟨y, ⟨hyY, w, hw, -, hyw⟩, huniq⟩` from `hYu u' hu' hku'`. Use `⟨y, ⟨hyY, (hK _).2 ⟨w, hw, hyw⟩⟩, fun y' hy' => huniq y' ⟨hy'.1, ?_⟩⟩` and prove the remaining obligations. Conclude with `rep_half ha'.1 (hstab _ ha'.1) (isHalf_sub hu' (hY y' hy'.1).1) ((hK _).1 hy'.2)`. Assume the negation of the conclusion as `hn`.

Establish `hfx : IsThetaFunO ψ S T (heisO ψ S T x f)` using `GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf x`. Establish `hGx : ∀ d, IsHalf (cA D a) d → d ∈ K → heisO ψ S T d (heisO ψ S T x f) = heisO ψ S T x f`. Introduce `d hdh hdK`. Take `⟨v, hv, hvh, rfl⟩` from `rep_half ha'.1 (hstab _ ha'.1) hdh ((hK d).1 hdK)`. Rewrite using `[heisO_comm, symplO_nsmul_swap, hpair v hv _ hkx, one_smul, hfix v hv (Or.inr hvh)]`.

Establish `hd : ∀ y, IsHalf (cA D a) y → y ∉ Λ' → ∃ l ∈ Λ', IsHalf (cA D (cA D a)) l ∧ ψ (symplO S T l y) ≠ 1`. Introduce `y hy hyΛ'`. Establish `hky : k • y ∉ Λ` using `fun h => hyΛ' ((memC y hy).2 h)`. Take `⟨l, hl, hlh, hne⟩` from `exists_dual_half ha' hdual (hstab _ (by rw [hcc]; exact ha.1)) (isHalf_nsmul hy k) hky`. Use `⟨k • l, ?_, isHalf_nsmul hlh k, by rwa [symplO_nsmul_swap]⟩` and prove the remaining obligations.

Rewrite `hlh` using `[hcc]`. Conclude with `(memA _ (isHalf_nsmul hlh k)).2 ⟨l, hl, rfl⟩`. Establish `h1 : ∀ u ∈ Λ', IsHalf (cA D a) u → heisO ψ S T u (∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f)) = ∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f)` using `fun u hu huh => sum_reps_invariant (ψ := ψ) (Λ := K) (Λ' := Λ') ha' (fun y hy => ⟨(memC y (hY y hy).1).2 (hY y hy).2, (hY y hy).1⟩) (fun u' hu' hu'h => hYK u' hu'h ((memC u' hu'h).1 hu')) (fun d hdK _ hdh => hGx d hdh hdK) hu huh`. Establish `h2 : ∀ u ∈ Λ', IsHalf (cA D (cA D a)) u → heisO ψ S T u (∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f)) = ∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f)`. Introduce `u hu huh`.

Rewrite `huh` using `[hcc]`. Take `⟨v, hv, hvh, rfl⟩` from `rep_half ha.1 (hstab _ ha.1) huh ((memA u huh).1 hu)`. Rewrite using `[heisO_sum]`. Use `Finset.sum_congr rfl fun y hy => ?_` and prove the remaining obligations. Rewrite using `[heisO_comm, symplO_nsmul_swap, hpair v hv _ (hY y hy).2, one_smul, heisO_comm ψ S T (k • v) x, half_orth ha (isHalf_nsmul hvh k) hxa, AddChar.map_zero_eq_one, one_smul, hfix v hv (Or.inl hvh)]`.

Take `⟨ℓ, hℓ0, hℓinv⟩` from `GlobalTheory.SplitHecke.exists_invariant_form' (Λ := Λ') (ψ := ψ) ha' hd hn h1 h2`. Apply `hℓ0` to reduce the goal to its premises. Rewrite using `[map_sum, Finset.sum_congr rfl fun y hy => hℓinv y (hY y hy).1 _ hfx, hℓ ℓ hℓinv x hxa, Finset.sum_const_zero]`.
-/
theorem sum_translates_eq_zero {a : AE D} (ha : IsSplitIdem D a) (hψ : IsStdChar D ψ (-1)) {Λ : AddSubgroup (WO S T)}
    (hdual : ∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ Λ ↔ ∀ u' ∈ Λ, ψ (symplO S T u u') = 1))
    (hpair : ∀ u ∈ Λ, ∀ u' ∈ Λ, ψ (symplO S T u u') = 1)
    (hstab : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ)
    {k : ℕ} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hfix : ∀ u ∈ Λ, IsHalf a u ∨ IsHalf (cA D a) u → heisO ψ S T (k • u) f = f)
    {Y : Finset (WO S T)}
    (hY : ∀ y ∈ Y, IsHalf (cA D a) y ∧ k • y ∈ Λ)
    (hYu : ∀ y', IsHalf (cA D a) y' → k • y' ∈ Λ →
      ∃! y, y ∈ Y ∧ ∃ u ∈ Λ, IsHalf (cA D a) u ∧ y' - y = k • u)
    (hℓ : ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x f) = 0)
    {x : WO S T} (hxa : IsHalf a x) (hkx : k • x ∈ Λ) :
    ∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f) = 0 := by
  have ha' := isSplitIdem_conj ha
  have hcc : cA D (cA D a) = a := GlobalTheory.DualPairCheck.cA_cA a
  obtain ⟨K, hK⟩ := exists_nsmul_subgroup Λ k
  obtain ⟨Λ', memA, memC⟩ := exists_mixed_subgroup ha Λ k
  have hYK : ∀ u', IsHalf (cA D a) u' → k • u' ∈ Λ → ∃! v, v ∈ Y ∧ u' - v ∈ K := by
    intro u' hu' hku'
    obtain ⟨y, ⟨hyY, w, hw, -, hyw⟩, huniq⟩ := hYu u' hu' hku'
    refine ⟨y, ⟨hyY, (hK _).2 ⟨w, hw, hyw⟩⟩, fun y' hy' => huniq y' ⟨hy'.1, ?_⟩⟩
    exact rep_half ha'.1 (hstab _ ha'.1) (isHalf_sub hu' (hY y' hy'.1).1) ((hK _).1 hy'.2)
  by_contra hn
  have hfx : IsThetaFunO ψ S T (heisO ψ S T x f) := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf x
  have hGx : ∀ d, IsHalf (cA D a) d → d ∈ K → heisO ψ S T d (heisO ψ S T x f) = heisO ψ S T x f := by
    intro d hdh hdK
    obtain ⟨v, hv, hvh, rfl⟩ := rep_half ha'.1 (hstab _ ha'.1) hdh ((hK d).1 hdK)
    rw [heisO_comm, symplO_nsmul_swap, hpair v hv _ hkx, one_smul, hfix v hv (Or.inr hvh)]
  have hd : ∀ y, IsHalf (cA D a) y → y ∉ Λ' → ∃ l ∈ Λ', IsHalf (cA D (cA D a)) l ∧ ψ (symplO S T l y) ≠ 1 := by
    intro y hy hyΛ'
    have hky : k • y ∉ Λ := fun h => hyΛ' ((memC y hy).2 h)
    obtain ⟨l, hl, hlh, hne⟩ := exists_dual_half ha' hdual (hstab _ (by rw [hcc]; exact ha.1))
      (isHalf_nsmul hy k) hky
    refine ⟨k • l, ?_, isHalf_nsmul hlh k, by rwa [symplO_nsmul_swap]⟩
    rw [hcc] at hlh
    exact (memA _ (isHalf_nsmul hlh k)).2 ⟨l, hl, rfl⟩
  have h1 : ∀ u ∈ Λ', IsHalf (cA D a) u →
      heisO ψ S T u (∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f)) = ∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f) :=
    fun u hu huh => sum_reps_invariant (ψ := ψ) (Λ := K) (Λ' := Λ') ha'
      (fun y hy => ⟨(memC y (hY y hy).1).2 (hY y hy).2, (hY y hy).1⟩)
      (fun u' hu' hu'h => hYK u' hu'h ((memC u' hu'h).1 hu')) (fun d hdK _ hdh => hGx d hdh hdK) hu huh
  have h2 : ∀ u ∈ Λ', IsHalf (cA D (cA D a)) u →
      heisO ψ S T u (∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f)) = ∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f) := by
    intro u hu huh
    rw [hcc] at huh
    obtain ⟨v, hv, hvh, rfl⟩ := rep_half ha.1 (hstab _ ha.1) huh ((memA u huh).1 hu)
    rw [heisO_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [heisO_comm, symplO_nsmul_swap, hpair v hv _ (hY y hy).2, one_smul, heisO_comm ψ S T (k • v) x,
      half_orth ha (isHalf_nsmul hvh k) hxa, AddChar.map_zero_eq_one, one_smul, hfix v hv (Or.inl hvh)]
  obtain ⟨ℓ, hℓ0, hℓinv⟩ := GlobalTheory.SplitHecke.exists_invariant_form' (Λ := Λ') (ψ := ψ) ha' hd hn h1 h2
  apply hℓ0
  rw [map_sum, Finset.sum_congr rfl fun y hy => hℓinv y (hY y hy).1 _ hfx, hℓ ℓ hℓinv x hxa,
    Finset.sum_const_zero]

/- English proof (translation)
Establish `hS` using `GlobalTheory.PlaceModel.isSelfDualC_latFrame S`. Establish `hT` using `GlobalTheory.PlaceModel.isSelfDualC_latFrame T`. Establish `ha'` using `isSplitIdem_conj ha`. Take `⟨k, hk, hfix, -⟩` from `(GlobalTheory.T.thetaCoefficient_isSchwartzBruhat_uniform_split D ψ S T hψ _ _ hS hT a ha f hf).1`. Take `⟨Y, -, hY, hYu, -⟩` from `GlobalTheory.T.exists_reps_latticeQuotient_conjugateHalf_orthogonal D ψ S T hψ _ _ hS hT a ha.1 (infPart_splitIdem ha) k hk`.

Take `⟨X, hXne, hX, -, hXo⟩` from `GlobalTheory.T.exists_reps_latticeQuotient_conjugateHalf_orthogonal D ψ S T hψ _ _ hS hT (cA D a) ha'.1 (infPart_splitIdem ha') k hk`. Rewrite `hX` using `[GlobalTheory.DualPairCheck.cA_cA]`. Establish `hdual : ∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T) ↔ ∀ u' ∈ latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T), ψ (symplO S T u u') = 1)` using `(GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1`. Establish `hfinΛ : ∀ u ∈ latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T), u.map (infPart D) = 0` using `fun u hu => latO_fin hu`. Establish `hstab : ∀ e : AE D, e * e = e → ∀ u ∈ latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T), e • u ∈ latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T)` using `fun e he => idem_smul_mem he`.

Generalize the expression as in `latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T) = Λ at *`. Establish `hpair : ∀ u ∈ Λ, ∀ u' ∈ Λ, ψ (symplO S T u u') = 1` using `fun u hu => (hdual u (hfinΛ u hu)).1 hu`. Establish `hB : ∀ x ∈ X, ∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f) = 0` using `fun x hx => sum_translates_eq_zero ha hψ hdual hpair hstab hf hfix hY hYu hℓ (hX x hx).1 (hX x hx).2`. Establish `hA` using `sum_average (ψ := ψ) ha (fun u hu huh => hfix u hu (Or.inr huh)) hY hYu (fun x hx => (hX x hx).1) hXo`. Establish `h0 : ∑ x ∈ X, heisO ψ S T (-x) (∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f)) = 0`.

Use `Finset.sum_eq_zero fun x hx => ?_` and prove the remaining obligations. Rewrite using `[hB x hx]`. Conclude with `(heisL ψ S T (-x)).map_zero`. Rewrite `hA` using `[h0]`. Establish `hc : (X.card : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 hXne)`.

Conclude with `(smul_eq_zero.1 hA.symm).resolve_left hc`.
-/
theorem invForms_separate (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (hψ : IsStdChar D ψ (-1)) (a : AE D)
    (ha : IsSplitIdem D a) (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f)
    (hℓ : ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x f) = 0) : f = 0 := by
  have hS := GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  have hT := GlobalTheory.PlaceModel.isSelfDualC_latFrame T
  have ha' := isSplitIdem_conj ha
  obtain ⟨k, hk, hfix, -⟩ := (GlobalTheory.T.thetaCoefficient_isSchwartzBruhat_uniform_split D ψ S T hψ _ _ hS hT a ha f hf).1
  obtain ⟨Y, -, hY, hYu, -⟩ := GlobalTheory.T.exists_reps_latticeQuotient_conjugateHalf_orthogonal D ψ S T hψ _ _ hS hT a ha.1 (infPart_splitIdem ha) k hk
  obtain ⟨X, hXne, hX, -, hXo⟩ := GlobalTheory.T.exists_reps_latticeQuotient_conjugateHalf_orthogonal D ψ S T hψ _ _ hS hT (cA D a) ha'.1 (infPart_splitIdem ha') k hk
  rw [GlobalTheory.DualPairCheck.cA_cA] at hX
  have hdual : ∀ u : WO S T, u.map (infPart D) = 0 →
      (u ∈ latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T) ↔
        ∀ u' ∈ latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T), ψ (symplO S T u u') = 1) :=
    (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfinΛ : ∀ u ∈ latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T), u.map (infPart D) = 0 :=
    fun u hu => latO_fin hu
  have hstab : ∀ e : AE D, e * e = e → ∀ u ∈ latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T),
      e • u ∈ latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T) :=
    fun e he => idem_smul_mem he
  generalize latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T) = Λ at *
  have hpair : ∀ u ∈ Λ, ∀ u' ∈ Λ, ψ (symplO S T u u') = 1 := fun u hu => (hdual u (hfinΛ u hu)).1 hu
  have hB : ∀ x ∈ X, ∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f) = 0 := fun x hx =>
    sum_translates_eq_zero ha hψ hdual hpair hstab hf hfix hY hYu hℓ (hX x hx).1 (hX x hx).2
  have hA := sum_average (ψ := ψ) ha (fun u hu huh => hfix u hu (Or.inr huh)) hY hYu (fun x hx => (hX x hx).1) hXo
  have h0 : ∑ x ∈ X, heisO ψ S T (-x) (∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f)) = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [hB x hx]
    exact (heisL ψ S T (-x)).map_zero
  rw [h0] at hA
  have hc : (X.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 hXne)
  exact (smul_eq_zero.1 hA.symm).resolve_left hc

end GlobalTheory.DownLift.SplitSep
