import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.RegularClassTraces.RegClassFin
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.IwahoriSubgroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelLocallyFiniteContinuous
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableDescendOfCover
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelCompactTranslateBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIsoFrameFirstCols
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLatticePointsInSiegelSetBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularSemisimpleConjugateUnipotentTranslateStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemParabolicOfFlagPreservingStatement
import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DecayFinal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeIntegralFiniteLargeExponentStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Matrix
open scoped Pointwise

noncomputable section
open GlobalTheory.CompanionTheory.RegInt
namespace MainStatements.WeightKernel.RegInt

variable {D : D7} {V : HSp D} {r : ℕ}

/- English proof (translation)
Use `set d := min c 1 with hd`. Establish `hd0 : 0 < d` using `lt_min hc one_pos`. Establish `hd1 : d ≤ 1` using `min_le_right _ _`. Use `⟨d ^ r, pow_pos hd0 _, fun t ht i => ?_⟩` and prove the remaining obligations. Establish `key : ∀ k : ℕ, ∀ i : Fin r, r - i.val = k + 1 → d ^ (k + 1) ≤ t i`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `i hi`. Establish `: i.val + 1 = r` using `by have := i.2; omega`.

Rewrite using `[zero_add, pow_one]`. Conclude with `(min_le_left c 1).trans (ht.2.2 i this)`. Consider the case `succ k ih`. Introduce `i hi`. Establish `hlt : i.val + 1 < r` using `by have := i.2; omega`.

Establish `h1` using `ih ⟨i.val + 1, hlt⟩ (by simp only; omega)`. Establish `h2` using `ht.2.1 i ⟨i.val + 1, hlt⟩ rfl`. Establish `h3` using `ht.1 ⟨i.val + 1, hlt⟩`. Combine the equalities or inequalities in the displayed calculation. Establish `hi` using `i.2`.

Take `⟨k, hk⟩ : ∃ k, r - i.val = k + 1` from `⟨r - i.val - 1, by omega⟩`. Conclude with `(pow_le_pow_of_le_one hd0.le hd1 (by omega)).trans (key k i hk)`.
-/
theorem cone_lower {c : ℝ} (hc : 0 < c) : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ i, c₀ ≤ t i := by
  set d := min c 1 with hd
  have hd0 : 0 < d := lt_min hc one_pos
  have hd1 : d ≤ 1 := min_le_right _ _
  refine ⟨d ^ r, pow_pos hd0 _, fun t ht i => ?_⟩
  have key : ∀ k : ℕ, ∀ i : Fin r, r - i.val = k + 1 → d ^ (k + 1) ≤ t i := by
    intro k
    induction k with
    | zero =>
      intro i hi
      have : i.val + 1 = r := by have := i.2; omega
      rw [zero_add, pow_one]
      exact (min_le_left c 1).trans (ht.2.2 i this)
    | succ k ih =>
      intro i hi
      have hlt : i.val + 1 < r := by have := i.2; omega
      have h1 := ih ⟨i.val + 1, hlt⟩ (by simp only; omega)
      have h2 := ht.2.1 i ⟨i.val + 1, hlt⟩ rfl
      have h3 := ht.1 ⟨i.val + 1, hlt⟩
      calc d ^ (k + 1 + 1) = d * d ^ (k + 1) := by ring
        _ ≤ d * t ⟨i.val + 1, hlt⟩ := by gcongr
        _ ≤ c * t ⟨i.val + 1, hlt⟩ := by gcongr; exact min_le_left _ _
        _ ≤ t i := h2
  have hi := i.2
  obtain ⟨k, hk⟩ : ∃ k, r - i.val = k + 1 := ⟨r - i.val - 1, by omega⟩
  exact (pow_le_pow_of_le_one hd0.le hd1 (by omega)).trans (key k i hk)

/- English proof (translation)
Establish `key : ∀ k : ℕ, ∀ i : Fin r, r - i.val = k + 1 → t i ≤ ρ ^ (k + 1)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `i hi`.

Establish `h1` using `h i`. Rewrite `h1` using `[root, dif_neg (by have := i.2; omega)]`. Simplify using `using h1`. Consider the case `succ k ih`. Introduce `i hi`.

Establish `hlt : i.val + 1 < r` using `by have := i.2; omega`. Establish `h1` using `ih ⟨i.val + 1, hlt⟩ (by simp only; omega)`. Establish `h2` using `h i`. Rewrite `h2` using `[root, dif_pos hlt, div_le_iff₀ (ht _)]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hi` using `i.2`. Take `⟨k, hk⟩ : ∃ k, r - i.val = k + 1` from `⟨r - i.val - 1, by omega⟩`. Conclude with `(key k i hk).trans (pow_le_pow_right₀ hρ (by omega))`.
-/
theorem le_pow_of_root {t : Fin r → ℝ} (ht : ∀ i, 0 < t i) {ρ : ℝ} (hρ : 1 ≤ ρ) (h : ∀ j, root t j ≤ ρ) (i : Fin r) :
    t i ≤ ρ ^ r := by
  have key : ∀ k : ℕ, ∀ i : Fin r, r - i.val = k + 1 → t i ≤ ρ ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      intro i hi
      have h1 := h i
      rw [root, dif_neg (by have := i.2; omega)] at h1
      simpa using h1
    | succ k ih =>
      intro i hi
      have hlt : i.val + 1 < r := by have := i.2; omega
      have h1 := ih ⟨i.val + 1, hlt⟩ (by simp only; omega)
      have h2 := h i
      rw [root, dif_pos hlt, div_le_iff₀ (ht _)] at h2
      calc t i ≤ ρ * t ⟨i.val + 1, hlt⟩ := h2
        _ ≤ ρ * ρ ^ (k + 1) := by gcongr
        _ = ρ ^ (k + 1 + 1) := by ring
  have hi := i.2
  obtain ⟨k, hk⟩ : ∃ k, r - i.val = k + 1 := ⟨r - i.val - 1, by omega⟩
  exact (key k i hk).trans (pow_le_pow_right₀ hρ (by omega))

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem prod_max_le {t : Fin r → ℝ} (ht : ∀ i, 0 < t i) {ρ : ℝ} (hρ : 1 ≤ ρ) (h : ∀ j, root t j ≤ ρ) :
    ∏ i, max (t i) 1 ≤ ρ ^ (r * r) := by
  calc ∏ i, max (t i) 1 ≤ ∏ _i : Fin r, ρ ^ r :=
        Finset.prod_le_prod (fun i _ => by positivity) fun i _ =>
          max_le (le_pow_of_root ht hρ h i) (one_le_pow₀ hρ)
    _ = ρ ^ (r * r) := by simp [pow_mul]

/- English proof (translation)
Use `Finset.prod_le_prod (s := Finset.univ) (f := fun _ : Fin r => (1 : ℝ)) (g := fun i => max (t i) 1) (fun _ _ => zero_le_one) fun i _ => le_max_right _ _` as an intermediate fact. Simplify using `using this`.
-/
theorem one_le_prod_max (t : Fin r → ℝ) : 1 ≤ ∏ i, max (t i) 1 := by
  have := Finset.prod_le_prod (s := Finset.univ) (f := fun _ : Fin r => (1 : ℝ)) (g := fun i => max (t i) 1)
    (fun _ _ => zero_le_one) fun i _ => le_max_right _ _
  simpa using this

/- English proof (translation)
Establish `hρ0 : 0 < ρ` using `by linarith`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow, ← pow_mul]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ ∏ i, (t i)⁻¹ ^ m := Finset.prod_le_prod (fun i _ => by positivity) fun i _ => by gcongr`. Conclude with `ht i`. Conclude with `le_pow_of_root ht hρ h i`.
-/
theorem inv_pow_le_prod {t : Fin r → ℝ} (ht : ∀ i, 0 < t i) {ρ : ℝ} (hρ : 1 ≤ ρ) (h : ∀ j, root t j ≤ ρ) (m : ℕ) :
    ρ⁻¹ ^ (r * r * m) ≤ ∏ i, (t i)⁻¹ ^ m := by
  have hρ0 : 0 < ρ := by linarith
  calc ρ⁻¹ ^ (r * r * m) = ∏ _i : Fin r, ((ρ ^ r)⁻¹) ^ m := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow, ← pow_mul]
        congr 2; ring
    _ ≤ ∏ i, (t i)⁻¹ ^ m := Finset.prod_le_prod (fun i _ => by positivity) fun i _ => by
        gcongr
        · exact ht i
        · exact le_pow_of_root ht hρ h i

/- English proof (translation)
Use `set S := hfin.toFinset with hS`. Establish `hSm : ∀ δ, δ ∈ S ↔ h δ ≠ 0 ∧ δ ∈ Cl` using `fun δ => by simp [hS]`. Establish `e0 : ∑' δ : Cl, h δ = ∑ δ ∈ S, h δ`. Rewrite using `[tsum_subtype Cl h]`. Use `(tsum_eq_sum (s := S) fun δ hδ => ?_).trans (Finset.sum_congr rfl fun δ hδ => ?_)` and prove the remaining obligations.

Distinguish the cases in `hc : δ ∈ Cl`. Rewrite using `[Set.indicator_of_mem hc]`. Assume the negation of the conclusion as `hne`. Conclude with `hδ ((hSm δ).2 ⟨hne, hc⟩)`. Rewrite using `[Set.indicator_of_notMem hc]`.

Rewrite using `[Set.indicator_of_mem ((hSm δ).1 hδ).2]`. Set `q : G → G ⧸ N` to `QuotientGroup.mk`. Establish `e1 : ∑ δ ∈ S, h δ = ∑ b ∈ S.image q, ∑ δ ∈ S with q δ = b, h δ` using `(Finset.sum_fiberwise_of_maps_to (fun δ hδ => Finset.mem_image_of_mem q hδ) _).symm`. Establish `e2 : ∀ b ∈ S.image q, ‖∑ δ ∈ S with q δ = b, h δ‖ ≤ β`. Introduce `b hb`.

Take `⟨δ₀, hδ₀, rfl⟩` from `Finset.mem_image.1 hb`. Take `⟨hne, hcl⟩` from `(hSm δ₀).1 hδ₀`. Use `le_trans (le_of_eq ?_) (h3 δ₀ hcl hne)` and prove the remaining obligations. Use `congr 1`. Establish `hinj : Function.Injective fun ν : N => δ₀ * (ν : G)` using `fun a b e => Subtype.ext (mul_left_cancel e)`.

Use `set u : G → ℂ := fun δ => if q δ = q δ₀ then h δ else 0 with hu`. Establish `hq : ∀ ν : N, q (δ₀ * ν) = q δ₀` using `fun ν => by`. Conclude with `QuotientGroup.eq.2 (by simp)`. Establish `e3 : ∑' ν : N, h (δ₀ * ν) = ∑' ν : N, u (δ₀ * ν)` using `tsum_congr fun ν => by simp only [hu, hq ν, if_true]`. Establish `hsupp : Function.support u ⊆ Set.range fun ν : N => δ₀ * (ν : G)`.

Introduce `δ hδ`. Establish `hδ' : q δ = q δ₀`. Assume the negation of the conclusion as `hn; exact hδ (by simp only [hu, if_neg hn])`. Establish `: δ₀⁻¹ * δ ∈ N` using `QuotientGroup.eq.1 hδ'.symm`. Conclude with `⟨⟨_, this⟩, by simp⟩`.

Rewrite using `[e3, hinj.tsum_eq hsupp]`. Establish `e4 : ∑' δ, u δ = ∑ δ ∈ S with q δ = q δ₀, u δ`. Use `tsum_eq_sum fun δ hδ => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne'`. Establish `hq' : q δ = q δ₀`.

Assume the negation of the conclusion as `hn; exact hne' (by simp only [hu, if_neg hn])`. Establish `hhδ : h δ ≠ 0`. Introduce `h0; exact hne' (by simp only [hu, if_pos hq', h0])`. Establish `hN : δ₀⁻¹ * δ ∈ N` using `QuotientGroup.eq.1 hq'.symm`. Establish `hc` using `h1 δ₀ hcl hne _ hN`.

Rewrite `hc` using `[mul_inv_cancel_left]`. Conclude with `hδ (Finset.mem_filter.2 ⟨(hSm δ).2 ⟨hhδ, hc⟩, hq'⟩)`. Rewrite using `[e4]`. Conclude with `Finset.sum_congr rfl fun δ hδ => by simp only [hu, if_pos (Finset.mem_filter.1 hδ).2]`. Establish `hcardS : ((S.image q).card : ℝ) ≤ κ`.

Use `le_trans ?_ hcard` and prove the remaining obligations. Rewrite using `[Set.ncard_eq_toFinset_card _ hfin]`. Conclude with `Finset.card_image_le` after adjusting the coercions. Rewrite using `[e0, e1]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `using norm_sum_le_of_le (S.image q) e2`. Use `_ ≤ κ * β := by gcongr`.
-/
theorem coset_sum {G : Type} [Group G] (N : Subgroup G) (Cl : Set G) (h : G → ℂ) {β : ℝ} (hβ : 0 ≤ β) {κ : ℝ}
    (hfin : (Function.support h ∩ Cl).Finite) (hcard : (((Function.support h ∩ Cl).ncard : ℕ) : ℝ) ≤ κ)
    (h1 : ∀ δ ∈ Cl, h δ ≠ 0 → ∀ ν ∈ N, δ * ν ∈ Cl)
    (h3 : ∀ δ ∈ Cl, h δ ≠ 0 → ‖∑' ν : N, h (δ * ν)‖ ≤ β) :
    ‖∑' δ : Cl, h δ‖ ≤ κ * β := by
  classical
  set S := hfin.toFinset with hS
  have hSm : ∀ δ, δ ∈ S ↔ h δ ≠ 0 ∧ δ ∈ Cl := fun δ => by simp [hS]
  have e0 : ∑' δ : Cl, h δ = ∑ δ ∈ S, h δ := by
    rw [tsum_subtype Cl h]
    refine (tsum_eq_sum (s := S) fun δ hδ => ?_).trans (Finset.sum_congr rfl fun δ hδ => ?_)
    · by_cases hc : δ ∈ Cl
      · rw [Set.indicator_of_mem hc]; by_contra hne; exact hδ ((hSm δ).2 ⟨hne, hc⟩)
      · rw [Set.indicator_of_notMem hc]
    · rw [Set.indicator_of_mem ((hSm δ).1 hδ).2]
  let q : G → G ⧸ N := QuotientGroup.mk
  have e1 : ∑ δ ∈ S, h δ = ∑ b ∈ S.image q, ∑ δ ∈ S with q δ = b, h δ :=
    (Finset.sum_fiberwise_of_maps_to (fun δ hδ => Finset.mem_image_of_mem q hδ) _).symm
  have e2 : ∀ b ∈ S.image q, ‖∑ δ ∈ S with q δ = b, h δ‖ ≤ β := by
    intro b hb
    obtain ⟨δ₀, hδ₀, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨hne, hcl⟩ := (hSm δ₀).1 hδ₀
    refine le_trans (le_of_eq ?_) (h3 δ₀ hcl hne)
    congr 1
    have hinj : Function.Injective fun ν : N => δ₀ * (ν : G) := fun a b e =>
      Subtype.ext (mul_left_cancel e)
    set u : G → ℂ := fun δ => if q δ = q δ₀ then h δ else 0 with hu
    have hq : ∀ ν : N, q (δ₀ * ν) = q δ₀ := fun ν => by
      exact QuotientGroup.eq.2 (by simp)
    have e3 : ∑' ν : N, h (δ₀ * ν) = ∑' ν : N, u (δ₀ * ν) :=
      tsum_congr fun ν => by simp only [hu, hq ν, if_true]
    have hsupp : Function.support u ⊆ Set.range fun ν : N => δ₀ * (ν : G) := by
      intro δ hδ
      have hδ' : q δ = q δ₀ := by
        by_contra hn; exact hδ (by simp only [hu, if_neg hn])
      have : δ₀⁻¹ * δ ∈ N := QuotientGroup.eq.1 hδ'.symm
      exact ⟨⟨_, this⟩, by simp⟩
    rw [e3, hinj.tsum_eq hsupp]
    have e4 : ∑' δ, u δ = ∑ δ ∈ S with q δ = q δ₀, u δ := by
      refine tsum_eq_sum fun δ hδ => ?_
      by_contra hne'
      have hq' : q δ = q δ₀ := by
        by_contra hn; exact hne' (by simp only [hu, if_neg hn])
      have hhδ : h δ ≠ 0 := by
        intro h0; exact hne' (by simp only [hu, if_pos hq', h0])
      have hN : δ₀⁻¹ * δ ∈ N := QuotientGroup.eq.1 hq'.symm
      have hc := h1 δ₀ hcl hne _ hN
      rw [mul_inv_cancel_left] at hc
      exact hδ (Finset.mem_filter.2 ⟨(hSm δ).2 ⟨hhδ, hc⟩, hq'⟩)
    rw [e4]
    exact Finset.sum_congr rfl fun δ hδ => by simp only [hu, if_pos (Finset.mem_filter.1 hδ).2]
  have hcardS : ((S.image q).card : ℝ) ≤ κ := by
    refine le_trans ?_ hcard
    rw [Set.ncard_eq_toFinset_card _ hfin]
    exact_mod_cast Finset.card_image_le
  rw [e0, e1]
  calc ‖∑ b ∈ S.image q, ∑ δ ∈ S with q δ = b, h δ‖ ≤ ((S.image q).card : ℝ) * β := by
        simpa using norm_sum_le_of_le (S.image q) e2
    _ ≤ κ * β := by gcongr

/- English proof (translation)
Use `set S := hfin.toFinset with hS`. Establish `hSm : ∀ δ, δ ∈ S ↔ h δ ≠ 0 ∧ δ ∈ Cl` using `fun δ => by simp [hS]`. Establish `e0 : ∑' δ : Cl, h δ = ∑ δ ∈ S, h δ`. Rewrite using `[tsum_subtype Cl h]`. Use `(tsum_eq_sum (s := S) fun δ hδ => ?_).trans (Finset.sum_congr rfl fun δ hδ => ?_)` and prove the remaining obligations.

Distinguish the cases in `hc : δ ∈ Cl`. Rewrite using `[Set.indicator_of_mem hc]`. Assume the negation of the conclusion as `hne`. Conclude with `hδ ((hSm δ).2 ⟨hne, hc⟩)`. Rewrite using `[Set.indicator_of_notMem hc]`.

Rewrite using `[Set.indicator_of_mem ((hSm δ).1 hδ).2]`. Establish `hcardS : (S.card : ℝ) ≤ κ`. Use `le_trans ?_ hcard` and prove the remaining obligations. Rewrite using `[Set.ncard_eq_toFinset_card _ hfin]`. Rewrite using `[e0]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `using norm_sum_le_of_le S (fun δ _ => hM δ)`. Use `_ ≤ κ * M := by gcongr`.
-/
theorem set_sum_le {G : Type} (Cl : Set G) (h : G → ℂ) {M : ℝ} (hM : ∀ g, ‖h g‖ ≤ M) (hM0 : 0 ≤ M) {κ : ℝ}
    (hfin : (Function.support h ∩ Cl).Finite) (hcard : (((Function.support h ∩ Cl).ncard : ℕ) : ℝ) ≤ κ) :
    ‖∑' δ : Cl, h δ‖ ≤ κ * M := by
  classical
  set S := hfin.toFinset with hS
  have hSm : ∀ δ, δ ∈ S ↔ h δ ≠ 0 ∧ δ ∈ Cl := fun δ => by simp [hS]
  have e0 : ∑' δ : Cl, h δ = ∑ δ ∈ S, h δ := by
    rw [tsum_subtype Cl h]
    refine (tsum_eq_sum (s := S) fun δ hδ => ?_).trans (Finset.sum_congr rfl fun δ hδ => ?_)
    · by_cases hc : δ ∈ Cl
      · rw [Set.indicator_of_mem hc]; by_contra hne; exact hδ ((hSm δ).2 ⟨hne, hc⟩)
      · rw [Set.indicator_of_notMem hc]
    · rw [Set.indicator_of_mem ((hSm δ).1 hδ).2]
  have hcardS : (S.card : ℝ) ≤ κ := by
    refine le_trans ?_ hcard
    rw [Set.ncard_eq_toFinset_card _ hfin]
  rw [e0]
  calc ‖∑ δ ∈ S, h δ‖ ≤ (S.card : ℝ) * M := by
        simpa using norm_sum_le_of_le S (fun δ _ => hM δ)
    _ ≤ κ * M := by gcongr

/- English proof (translation)
Establish `hmem : ∀ δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass (GQ V) γ, (δ : GA D V) ∈ GQ V` using `fun ⟨δ, k, hk, e⟩ => e ▸ mul_mem (mul_mem (inv_mem hk) hγ) hk`. Set `ι : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass (GQ V) γ → GQ V` to `fun δ => ⟨δ, hmem δ⟩`. Establish `hι : Function.Injective ι` using `fun a b e => Subtype.ext (congrArg (fun z : GQ V => (z : GA D V)) e)`. Establish `hlf : LocallyFinite fun δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass (GQ V) γ => Function.support fun x : GA D V => f (x⁻¹ * δ * x)`. Introduce `x`.

Take `⟨C, hC, hx⟩` from `exists_compact_mem_nhds x`. Use `⟨C, hx, ((GlobalTheory.AutomorphicL2KernelContinuous.finite_contributing (Γ := GQ V) hc hC hC).preimage hι.injOn).subset ?_⟩` and prove the remaining obligations. Introduce and unpack `δ ⟨y, h, h1⟩`. Conclude with `⟨y, h1, y, h1, h⟩`. Establish `h : Continuous fun x : GA D V => ∑ᶠ δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass (GQ V) γ, f (x⁻¹ * δ * x)` using `continuous_finsum (fun δ => by fun_prop) hlf`.

Use `h.congr fun x => ?_` and prove the remaining obligations. Use `(tsum_eq_finsum ?_).symm` and prove the remaining obligations. Conclude with `((GlobalTheory.AutomorphicL2Unitary.finite_support_kernel (Γ := GQ V) hc x x).preimage hι.injOn).subset fun δ hδ => hδ`.
-/
theorem continuous_classKernel {f : GA D V → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) {γ : GA D V}
    (hγ : γ ∈ GQ V) : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) γ f) := by
  have hmem : ∀ δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass (GQ V) γ, (δ : GA D V) ∈ GQ V :=
    fun ⟨δ, k, hk, e⟩ => e ▸ mul_mem (mul_mem (inv_mem hk) hγ) hk
  let ι : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass (GQ V) γ → GQ V := fun δ => ⟨δ, hmem δ⟩
  have hι : Function.Injective ι := fun a b e => Subtype.ext (congrArg (fun z : GQ V => (z : GA D V)) e)
  have hlf : LocallyFinite fun δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass (GQ V) γ =>
      Function.support fun x : GA D V => f (x⁻¹ * δ * x) := by
    intro x
    obtain ⟨C, hC, hx⟩ := exists_compact_mem_nhds x
    refine ⟨C, hx, ((GlobalTheory.AutomorphicL2KernelContinuous.finite_contributing (Γ := GQ V) hc hC hC).preimage hι.injOn).subset ?_⟩
    rintro δ ⟨y, h, h1⟩
    exact ⟨y, h1, y, h1, h⟩
  have h : Continuous fun x : GA D V => ∑ᶠ δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass (GQ V) γ, f (x⁻¹ * δ * x) :=
    continuous_finsum (fun δ => by fun_prop) hlf
  refine h.congr fun x => ?_
  refine (tsum_eq_finsum ?_).symm
  exact ((GlobalTheory.AutomorphicL2Unitary.finite_support_kernel (Γ := GQ V) hc x x).preimage hι.injOn).subset fun δ hδ => hδ

/- English proof (translation)
Rewrite using `[show GQ V = (rat V).range from (range_ratEmb ..).symm]`. Conclude with `⟨g, rfl⟩`.
-/
theorem rat_mem (g : GF V) : rat V g ∈ GQ V := by
  rw [show GQ V = (rat V).range from (range_ratEmb ..).symm]; exact ⟨g, rfl⟩

def classEquiv (γ : GF V) : {δ : GF V | IsConj γ δ} ≃ GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass (GQ V) (rat V γ) :=
  Equiv.ofBijective (fun δ => ⟨rat V δ, by
      obtain ⟨c, hc⟩ := isConj_iff.1 δ.2
      refine ⟨rat V c⁻¹, rat_mem _, ?_⟩
      rw [← hc]; simp only [map_mul, map_inv, inv_inv]⟩)
    ⟨fun a b h => Subtype.ext (ratEmb_injective _ _ (congrArg Subtype.val h)), fun δ => by
      obtain ⟨δ, g, hg, rfl⟩ := δ
      rw [show GQ V = (rat V).range from (range_ratEmb ..).symm] at hg
      obtain ⟨c, rfl⟩ := hg
      refine ⟨⟨c⁻¹ * γ * c, isConj_iff.2 ⟨c⁻¹, by group⟩⟩, Subtype.ext ?_⟩
      simp only [map_mul, map_inv]⟩

/- English proof (translation)
The claim follows from `((classEquiv γ).tsum_eq fun δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass (GQ V) (rat V γ) => f (x⁻¹ * δ * x)).symm`.
-/
theorem classKernel_eq (γ : GF V) (f : GA D V → ℂ) (x : GA D V) :
    GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f x = ∑' δ : {δ : GF V | IsConj γ δ}, f (x⁻¹ * rat V δ * x) :=
  ((classEquiv γ).tsum_eq fun δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass (GQ V) (rat V γ) => f (x⁻¹ * δ * x)).symm

/- English proof (translation)
Take `⟨g, rfl⟩` from `isConj_iff.1 h`. Use `show IsRegSS ((g.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * γ.1.1 * ((g.1)⁻¹ : GL (Fin V.rank) D.host.E).1)`. Unfold `IsRegSS`. Rewrite using `[Matrix.coe_units_inv, Matrix.charpoly_units_conj]`. Conclude with `hγ`.
-/
theorem regSS_of_conj {γ δ : GF V} (h : IsConj γ δ) (hγ : IsRegSS γ.1.1) : IsRegSS δ.1.1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 h
  show IsRegSS ((g.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * γ.1.1 * ((g.1)⁻¹ : GL (Fin V.rank) D.host.E).1)
  unfold IsRegSS
  rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj]
  exact hγ

/- English proof (translation)
Use `group`.
-/
theorem conj_id {G : Type} [Group G] (a ω d n : G) :
    (a * ω)⁻¹ * (d * n) * (a * ω) = ω⁻¹ * (a⁻¹ * d * a) * (a⁻¹ * n * a) * ω := by group

set_option maxHeartbeats 1000000 in
open GlobalTheory.SiegelSet in

/- English proof (translation)
Take `⟨C₀, hC₀, hC₀m⟩` from `hconj`. Take `⟨hfc, hfs⟩` from `GlobalTheory.Orb.continuous_of_mem_ccAd hf`. Establish `hS : IsCompact (tsupport f)` using `hfs.isCompact`. Use `set W : Set (GA D V) := C₀ * (K : Set (GA D V)) with hWdef`. Establish `hWc : IsCompact W` using `hC₀.mul hK`.

Use `set C₁ : Set (GA D V) := W * tsupport f * W⁻¹ with hC₁`. Establish `hC₁c : IsCompact C₁` using `(hWc.mul hS).mul hWc.inv`. Take `⟨A₁, B₁, hcnt⟩` from `GlobalTheory.T.finite_lattice_points_in_siegel_set_bound D V r X Y hW c hc C₁ hC₁c`. Establish `hdec` using `fun j : Fin r => MainStatements.WeightKernel.Dec.decay_holds D V r X Y hW c hc j f hf (hcusp _ (IsoFlag.proper_single _)) (W⁻¹ * C₁) W (hWc.inv.mul hC₁c) hWc`. Use `choose A hA using hdec`.

Take `⟨t1, ht1⟩` from `GlobalTheory.CompanionTheory.FlagKey.flag_key _ _ D.sp.cm.sig (isCMExt_host D) V.rank V.gram (GlobalTheory.Doubling.isHermND_gram V) r X Y hW Ω hΩ hΩP K hK c hc (tsupport f) hS`. Take `⟨c₀, hc₀, hlow⟩` from `cone_lower (r := r) hc`. Take `⟨M, hM⟩` from `hfc.bounded_above_of_compact_support hfs`. Establish `hM0 : 0 ≤ M` using `(norm_nonneg _).trans (hM 1)`. Use `set R₀ : ℝ := max 1 (max t1 (t1 / c₀)) with hR₀`.

Establish `hR1 : 1 ≤ R₀` using `le_max_left _ _`. Establish `hRt : t1 ≤ R₀` using `(le_max_left _ _).trans (le_max_right _ _)`. Establish `hRt' : t1 / c₀ ≤ R₀` using `(le_max_right _ _).trans (le_max_right _ _)`. Use `set A₂ : ℕ := ∑ j, A j with hA₂`. Use `set m' : ℕ := r * r * (A₁ + A₂ + m) with hm'`.

Use `choose Bj hBj using fun j => hA j m'`. Use `set B₂ : ℝ := ∑ j, |Bj j| with hB₂`. Establish `hB₂0 : 0 ≤ B₂` using `Finset.sum_nonneg fun _ _ => abs_nonneg _`. Use `set B₁' : ℝ := |B₁| with hB₁'`. Establish `hB₁0 : 0 ≤ B₁'` using `abs_nonneg _`.

Use `⟨B₁' * M * R₀ ^ (r * r * (A₁ + m)) + B₁' * B₂, by positivity, ?_⟩` and prove the remaining obligations. Introduce `p hp t ht a ha k hk`. Establish `tpos` using `ht.1`. Use `set T : ℝ := ∏ i, max (t i) 1 with hT`. Establish `hT1 : 1 ≤ T` using `one_le_prod_max t`.

Use `set ω : GA D V := a⁻¹ * p * a * k with hω`. Establish `hωW : ω ∈ W` using `Set.mul_mem_mul (hC₀m p hp t ht a ha) hk`. Establish `hx : p * a * k = a * ω` using `by rw [hω]; group`. Use `set x : GA D V := p * a * k with hxdef`. Use `set h : GF V → ℂ := fun δ => f (x⁻¹ * rat V δ * x) with hh`.

Use `set Cl : Set (GF V) := {δ | IsConj γ δ} with hCl`. Establish `hsub : ∀ δ, h δ ≠ 0 → a⁻¹ * rat V δ * a ∈ C₁`. Introduce `δ hδ`. Establish `h1 : x⁻¹ * rat V δ * x ∈ tsupport f` using `subset_tsupport f hδ`. Establish `e : a⁻¹ * rat V δ * a = ω * (x⁻¹ * rat V δ * x) * ω⁻¹` using `by rw [hx]; group`.

Rewrite using `[e]`. Conclude with `Set.mul_mem_mul (Set.mul_mem_mul hωW h1) (Set.inv_mem_inv.2 hωW)`. Take `⟨hfin0, hcard0⟩` from `hcnt t ht a ha`. Establish `hss : Function.support h ∩ Cl ⊆ {δ : GF V | a⁻¹ * rat V δ * a ∈ C₁}` using `fun δ hδ => hsub δ hδ.1`. Establish `hfin : (Function.support h ∩ Cl).Finite` using `hfin0.subset hss`.

Establish `hcard : (((Function.support h ∩ Cl).ncard : ℕ) : ℝ) ≤ B₁' * T ^ A₁`. Establish `h1 : (Function.support h ∩ Cl).ncard ≤ {δ : GF V | a⁻¹ * rat V δ * a ∈ C₁}.ncard` using `Set.ncard_le_ncard hss hfin0`. Establish `h2 : B₁ * T ^ A₁ ≤ B₁' * T ^ A₁` using `by gcongr; exact le_abs_self _`. Conclude with `le_trans (by exact_mod_cast h1) (hcard0.trans h2)`. Rewrite using `[classKernel_eq]`.

Distinguish the cases in `hsh : ∀ j, root t j ≤ R₀`. Establish `h1` using `set_sum_le Cl h (fun _ => hM _) hM0 hfin hcard`. Establish `h2 : T ≤ R₀ ^ (r * r)` using `prod_max_le tpos hR1 hsh`. Establish `h3` using `inv_pow_le_prod tpos hR1 hsh m`. Establish `hR0 : 0 < R₀` using `by linarith`.

Establish `h4 : T ^ A₁ ≤ R₀ ^ (r * r * A₁)`. Rewrite using `[pow_mul]`. Use `gcongr`. Establish `hP : 0 ≤ ∏ i, (t i)⁻¹ ^ m` using `Finset.prod_nonneg fun i _ => by have := tpos i; positivity`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_add, pow_add, inv_pow]`. Clear the denominators using the available nonvanishing facts. Use `_ ≤ B₁' * M * R₀ ^ (r * r * (A₁ + m)) * ∏ i, (t i)⁻¹ ^ m := by gcongr`. Use `_ ≤ _ := by`. Rewrite using `[add_mul]`.

Establish `: 0 ≤ B₁' * B₂ * ∏ i, (t i)⁻¹ ^ m` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Use `push_neg at hsh`. Take `⟨j₁, hj₁⟩` from `hsh`. Take `⟨j, -, hjmax⟩` from `Finset.exists_max_image Finset.univ (root t) ⟨j₁, Finset.mem_univ _⟩`.

Use `set ρ : ℝ := root t j with hρ`. Establish `hρR : R₀ < ρ` using `hj₁.trans_le (hjmax j₁ (Finset.mem_univ _))`. Establish `hρ1 : 1 ≤ ρ` using `hR1.trans hρR.le`. Establish `hρ0 : 0 < ρ` using `by linarith`. Establish `hall : ∀ i, root t i ≤ ρ` using `fun i => hjmax i (Finset.mem_univ _)`.

Establish `hc1 : t1 < t j`. Distinguish the cases in `hl : j.val + 1 < r`. Establish `e : ρ = t j / t ⟨j.val + 1, hl⟩` using `by rw [hρ, root, dif_pos hl]`. Establish `hp` using `tpos ⟨j.val + 1, hl⟩`. Establish `h2 : R₀ * t ⟨j.val + 1, hl⟩ < t j`.

Rewrite `hρR` using `[e, lt_div_iff₀ hp]`. Conclude with `hρR`. Establish `h3` using `hlow t ht ⟨j.val + 1, hl⟩`. Establish `h4 : t1 / c₀ * c₀ ≤ R₀ * t ⟨j.val + 1, hl⟩`. Establish `: 0 ≤ R₀` using `by linarith`.

Conclude with `mul_le_mul hRt' h3 hc₀.le this`. Rewrite `h4` using `[div_mul_cancel₀ _ hc₀.ne']`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e : ρ = t j` using `by rw [hρ, root, dif_neg hl]`. Rewrite using `[← e]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc2 : ∀ j' : Fin r, j'.val = j.val + 1 → t1 * t j' < t j`. Introduce `j' hj'`. Establish `hl : j.val + 1 < r` using `hj' ▸ j'.2`. Establish `e : ρ = t j / t ⟨j.val + 1, hl⟩` using `by rw [hρ, root, dif_pos hl]`.

Establish `e' : j' = ⟨j.val + 1, hl⟩` using `Fin.ext hj'`. Establish `hp` using `tpos j'`. Rewrite `hp`, the goal using `[e', ]`. Rewrite `hρR` using `[e, lt_div_iff₀ hp]`. Conclude with `lt_of_le_of_lt (by gcongr) hρR`.

Establish `hstab : ∀ δ, h δ ≠ 0 → δ ∈ (frameFlag (isIsoFrame_firstCols hW j)).parRat D.sp.cm`. Introduce `δ hδ`. Conclude with `GlobalTheory.T.mem_parabolic_of_flag_preserving D V r X Y hW j δ (ht1 p hp t ht a ha k hk δ (subset_tsupport f hδ) j hc1 hc2)`. Establish `hmul : ∀ δ ∈ Cl, h δ ≠ 0 → ∀ ν ∈ (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm, δ * ν ∈ Cl`. Introduce `δ hδ hne ν hν`.

Take `⟨g, hg⟩` from `GlobalTheory.T.regular_semisimple_conjugate_unipotent_translate D V _ _ (isIsoFrame_firstCols hW j) δ (regSS_of_conj hδ hreg) (hstab δ hne) ν hν`. Conclude with `IsConj.trans hδ (isConj_iff.2 ⟨g, hg⟩)`. Establish `hT' : T ≤ ρ ^ (r * r)` using `prod_max_le tpos hρ1 hall`. Use `set β : ℝ := B₂ * T ^ A₂ * ρ⁻¹ ^ m' with hβ`. Establish `hβ0 : 0 ≤ β` using `by positivity`.

Establish `hsum : ∀ δ ∈ Cl, h δ ≠ 0 → ‖∑' ν : (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm, h (δ * ν)‖ ≤ β`. Introduce `δ hδ hne`. Establish `hy` using `hsub δ hne`. Establish `hb` using `hBj j t ht a ha (ω⁻¹ * (a⁻¹ * rat V δ * a)) (Set.mul_mem_mul (Set.inv_mem_inv.2 hωW) hy) ω hωW`. Establish `e : ∀ ν : (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm, h (δ * ν) = f (ω⁻¹ * (a⁻¹ * rat V δ * a) * (a⁻¹ * rat V ν * a) * ω)` using `fun ν => by`.

Establish `e1 : (rat V) (δ * (ν : GF V)) = rat V δ * rat V ν` using `map_mul _ _ _`. Simplify using `only [hh, e1, hx]`. Rewrite using `[conj_id]`. Simplify using `only [e]`. Use `hb.trans ?_` and prove the remaining obligations.

Establish `h1 : Bj j ≤ B₂` using `(le_abs_self _).trans (Finset.single_le_sum (f := fun j => |Bj j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j))`. Establish `h2 : T ^ A j ≤ T ^ A₂` using `pow_le_pow_right₀ hT1 (Finset.single_le_sum (f := A) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))`. Establish `h3 : (0 : ℝ) ≤ ρ⁻¹ ^ m'` using `by positivity`. Establish `h4 : (0 : ℝ) ≤ T ^ A j` using `by positivity`. Rewrite using `[hβ]`.

Use `gcongr`. Establish `h1` using `coset_sum _ Cl h hβ0 hfin hcard hmul hsum`. Establish `hP` using `inv_pow_le_prod tpos hρ1 hall m`. Establish `hP0 : 0 ≤ ∏ i, (t i)⁻¹ ^ m` using `le_trans (by positivity) hP`. Establish `h5 : T ^ A₁ ≤ ρ ^ (r * r * A₁)` using `by rw [pow_mul]; gcongr`.

Establish `h6 : T ^ A₂ ≤ ρ ^ (r * r * A₂)` using `by rw [pow_mul]; gcongr`. Establish `h7 : ρ ^ (r * r * A₁) * ρ ^ (r * r * A₂) * ρ⁻¹ ^ m' = ρ⁻¹ ^ (r * r * m)`. Establish `ha : ρ ^ (r * r * A₁) ≠ 0` using `by positivity`. Establish `hb : ρ ^ (r * r * A₂) ≠ 0` using `by positivity`. Rewrite using `[hm', mul_add, mul_add, pow_add, pow_add, inv_pow, inv_pow]`.

Clear the denominators using the available nonvanishing facts. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[add_mul]`. Establish `: 0 ≤ B₁' * M * R₀ ^ (r * r * (A₁ + m)) * ∏ i, (t i)⁻¹ ^ m`. Establish `: 0 < R₀` using `by linarith`.

Check the signs of the components of the expression. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem class_bound {X Y : Matrix (Fin V.rank) (Fin r) D.host.E} (hW : IsWittFrame D.sp.cm.sig V.gram X Y)
    {K : Subgroup (GA D V)} {Ω : Set (GA D V)} {c : ℝ} (hK : IsCompact (K : Set (GA D V))) (hΩ : IsCompact Ω)
    (hΩP : Ω ⊆ minParOne D.sp.cm.sig V.gram X) (hc : 0 < c)
    (hconj : ∃ C : Set (GA D V), IsCompact C ∧ ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a,
      IsTorusElt D.sp.cm.sig V.gram X Y t a → a⁻¹ * p * a ∈ C)
    {f : GA D V → ℂ} (hf : f ∈ CcGA V) (hcusp : MainStatements.RegularCuspidalTrace.IsCuspFn f) {γ : GF V} (hreg : IsRegSS γ.1.1) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt D.sp.cm.sig V.gram X Y t a → ∀ k ∈ K,
      ‖GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f (p * a * k)‖ ≤ B * ∏ i, (t i)⁻¹ ^ m := by
  obtain ⟨C₀, hC₀, hC₀m⟩ := hconj
  obtain ⟨hfc, hfs⟩ := GlobalTheory.Orb.continuous_of_mem_ccAd hf
  have hS : IsCompact (tsupport f) := hfs.isCompact
  set W : Set (GA D V) := C₀ * (K : Set (GA D V)) with hWdef
  have hWc : IsCompact W := hC₀.mul hK
  set C₁ : Set (GA D V) := W * tsupport f * W⁻¹ with hC₁
  have hC₁c : IsCompact C₁ := (hWc.mul hS).mul hWc.inv
  obtain ⟨A₁, B₁, hcnt⟩ := GlobalTheory.T.finite_lattice_points_in_siegel_set_bound D V r X Y hW c hc C₁ hC₁c
  have hdec := fun j : Fin r => MainStatements.WeightKernel.Dec.decay_holds D V r X Y hW c hc j f hf
    (hcusp _ (IsoFlag.proper_single _)) (W⁻¹ * C₁) W (hWc.inv.mul hC₁c) hWc
  choose A hA using hdec
  obtain ⟨t1, ht1⟩ := GlobalTheory.CompanionTheory.FlagKey.flag_key _ _ D.sp.cm.sig (isCMExt_host D) V.rank V.gram (GlobalTheory.Doubling.isHermND_gram V) r X Y hW
    Ω hΩ hΩP K hK c hc (tsupport f) hS
  obtain ⟨c₀, hc₀, hlow⟩ := cone_lower (r := r) hc
  obtain ⟨M, hM⟩ := hfc.bounded_above_of_compact_support hfs
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  set R₀ : ℝ := max 1 (max t1 (t1 / c₀)) with hR₀
  have hR1 : 1 ≤ R₀ := le_max_left _ _
  have hRt : t1 ≤ R₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hRt' : t1 / c₀ ≤ R₀ := (le_max_right _ _).trans (le_max_right _ _)
  set A₂ : ℕ := ∑ j, A j with hA₂
  set m' : ℕ := r * r * (A₁ + A₂ + m) with hm'
  choose Bj hBj using fun j => hA j m'
  set B₂ : ℝ := ∑ j, |Bj j| with hB₂
  have hB₂0 : 0 ≤ B₂ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set B₁' : ℝ := |B₁| with hB₁'
  have hB₁0 : 0 ≤ B₁' := abs_nonneg _
  refine ⟨B₁' * M * R₀ ^ (r * r * (A₁ + m)) + B₁' * B₂, by positivity, ?_⟩
  intro p hp t ht a ha k hk
  have tpos := ht.1
  set T : ℝ := ∏ i, max (t i) 1 with hT
  have hT1 : 1 ≤ T := one_le_prod_max t
  set ω : GA D V := a⁻¹ * p * a * k with hω
  have hωW : ω ∈ W := Set.mul_mem_mul (hC₀m p hp t ht a ha) hk
  have hx : p * a * k = a * ω := by rw [hω]; group
  set x : GA D V := p * a * k with hxdef
  set h : GF V → ℂ := fun δ => f (x⁻¹ * rat V δ * x) with hh
  set Cl : Set (GF V) := {δ | IsConj γ δ} with hCl
  have hsub : ∀ δ, h δ ≠ 0 → a⁻¹ * rat V δ * a ∈ C₁ := by
    intro δ hδ
    have h1 : x⁻¹ * rat V δ * x ∈ tsupport f := subset_tsupport f hδ
    have e : a⁻¹ * rat V δ * a = ω * (x⁻¹ * rat V δ * x) * ω⁻¹ := by rw [hx]; group
    rw [e]
    exact Set.mul_mem_mul (Set.mul_mem_mul hωW h1) (Set.inv_mem_inv.2 hωW)
  obtain ⟨hfin0, hcard0⟩ := hcnt t ht a ha
  have hss : Function.support h ∩ Cl ⊆ {δ : GF V | a⁻¹ * rat V δ * a ∈ C₁} := fun δ hδ => hsub δ hδ.1
  have hfin : (Function.support h ∩ Cl).Finite := hfin0.subset hss
  have hcard : (((Function.support h ∩ Cl).ncard : ℕ) : ℝ) ≤ B₁' * T ^ A₁ := by
    have h1 : (Function.support h ∩ Cl).ncard ≤ {δ : GF V | a⁻¹ * rat V δ * a ∈ C₁}.ncard := Set.ncard_le_ncard hss hfin0
    have h2 : B₁ * T ^ A₁ ≤ B₁' * T ^ A₁ := by gcongr; exact le_abs_self _
    exact le_trans (by exact_mod_cast h1) (hcard0.trans h2)
  rw [classKernel_eq]
  by_cases hsh : ∀ j, root t j ≤ R₀
  ·
    have h1 := set_sum_le Cl h (fun _ => hM _) hM0 hfin hcard
    have h2 : T ≤ R₀ ^ (r * r) := prod_max_le tpos hR1 hsh
    have h3 := inv_pow_le_prod tpos hR1 hsh m
    have hR0 : 0 < R₀ := by linarith
    have h4 : T ^ A₁ ≤ R₀ ^ (r * r * A₁) := by
      rw [pow_mul]; gcongr
    have hP : 0 ≤ ∏ i, (t i)⁻¹ ^ m := Finset.prod_nonneg fun i _ => by have := tpos i; positivity
    calc ‖∑' δ : Cl, h δ‖ ≤ B₁' * T ^ A₁ * M := h1
      _ ≤ B₁' * R₀ ^ (r * r * A₁) * M := by gcongr
      _ = B₁' * M * R₀ ^ (r * r * (A₁ + m)) * R₀⁻¹ ^ (r * r * m) := by
          rw [mul_add, pow_add, inv_pow]; field_simp
      _ ≤ B₁' * M * R₀ ^ (r * r * (A₁ + m)) * ∏ i, (t i)⁻¹ ^ m := by gcongr
      _ ≤ _ := by
          rw [add_mul]
          have : 0 ≤ B₁' * B₂ * ∏ i, (t i)⁻¹ ^ m := by positivity
          linarith
  ·
    push_neg at hsh
    obtain ⟨j₁, hj₁⟩ := hsh
    obtain ⟨j, -, hjmax⟩ := Finset.exists_max_image Finset.univ (root t) ⟨j₁, Finset.mem_univ _⟩
    set ρ : ℝ := root t j with hρ
    have hρR : R₀ < ρ := hj₁.trans_le (hjmax j₁ (Finset.mem_univ _))
    have hρ1 : 1 ≤ ρ := hR1.trans hρR.le
    have hρ0 : 0 < ρ := by linarith
    have hall : ∀ i, root t i ≤ ρ := fun i => hjmax i (Finset.mem_univ _)
    have hc1 : t1 < t j := by
      by_cases hl : j.val + 1 < r
      · have e : ρ = t j / t ⟨j.val + 1, hl⟩ := by rw [hρ, root, dif_pos hl]
        have hp := tpos ⟨j.val + 1, hl⟩
        have h2 : R₀ * t ⟨j.val + 1, hl⟩ < t j := by
          rw [e, lt_div_iff₀ hp] at hρR; exact hρR
        have h3 := hlow t ht ⟨j.val + 1, hl⟩
        have h4 : t1 / c₀ * c₀ ≤ R₀ * t ⟨j.val + 1, hl⟩ := by
          have : 0 ≤ R₀ := by linarith
          exact mul_le_mul hRt' h3 hc₀.le this
        rw [div_mul_cancel₀ _ hc₀.ne'] at h4
        linarith
      · have e : ρ = t j := by rw [hρ, root, dif_neg hl]
        rw [← e]; linarith
    have hc2 : ∀ j' : Fin r, j'.val = j.val + 1 → t1 * t j' < t j := by
      intro j' hj'
      have hl : j.val + 1 < r := hj' ▸ j'.2
      have e : ρ = t j / t ⟨j.val + 1, hl⟩ := by rw [hρ, root, dif_pos hl]
      have e' : j' = ⟨j.val + 1, hl⟩ := Fin.ext hj'
      have hp := tpos j'
      rw [e', ] at hp ⊢
      rw [e, lt_div_iff₀ hp] at hρR
      exact lt_of_le_of_lt (by gcongr) hρR
    have hstab : ∀ δ, h δ ≠ 0 → δ ∈ (frameFlag (isIsoFrame_firstCols hW j)).parRat D.sp.cm := by
      intro δ hδ
      exact GlobalTheory.T.mem_parabolic_of_flag_preserving D V r X Y hW j δ
        (ht1 p hp t ht a ha k hk δ (subset_tsupport f hδ) j hc1 hc2)
    have hmul : ∀ δ ∈ Cl, h δ ≠ 0 → ∀ ν ∈ (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm, δ * ν ∈ Cl := by
      intro δ hδ hne ν hν
      obtain ⟨g, hg⟩ := GlobalTheory.T.regular_semisimple_conjugate_unipotent_translate D V _ _ (isIsoFrame_firstCols hW j) δ (regSS_of_conj hδ hreg) (hstab δ hne) ν hν
      exact IsConj.trans hδ (isConj_iff.2 ⟨g, hg⟩)
    have hT' : T ≤ ρ ^ (r * r) := prod_max_le tpos hρ1 hall
    set β : ℝ := B₂ * T ^ A₂ * ρ⁻¹ ^ m' with hβ
    have hβ0 : 0 ≤ β := by positivity
    have hsum : ∀ δ ∈ Cl, h δ ≠ 0 →
        ‖∑' ν : (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm, h (δ * ν)‖ ≤ β := by
      intro δ hδ hne
      have hy := hsub δ hne
      have hb := hBj j t ht a ha (ω⁻¹ * (a⁻¹ * rat V δ * a)) (Set.mul_mem_mul (Set.inv_mem_inv.2 hωW) hy) ω hωW
      have e : ∀ ν : (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm,
          h (δ * ν) = f (ω⁻¹ * (a⁻¹ * rat V δ * a) * (a⁻¹ * rat V ν * a) * ω) := fun ν => by
        have e1 : (rat V) (δ * (ν : GF V)) = rat V δ * rat V ν := map_mul _ _ _
        simp only [hh, e1, hx]
        rw [conj_id]
      simp only [e]
      refine hb.trans ?_
      have h1 : Bj j ≤ B₂ := (le_abs_self _).trans
        (Finset.single_le_sum (f := fun j => |Bj j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j))
      have h2 : T ^ A j ≤ T ^ A₂ := pow_le_pow_right₀ hT1
        (Finset.single_le_sum (f := A) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
      have h3 : (0 : ℝ) ≤ ρ⁻¹ ^ m' := by positivity
      have h4 : (0 : ℝ) ≤ T ^ A j := by positivity
      rw [hβ]
      gcongr
    have h1 := coset_sum _ Cl h hβ0 hfin hcard hmul hsum
    have hP := inv_pow_le_prod tpos hρ1 hall m
    have hP0 : 0 ≤ ∏ i, (t i)⁻¹ ^ m := le_trans (by positivity) hP
    have h5 : T ^ A₁ ≤ ρ ^ (r * r * A₁) := by rw [pow_mul]; gcongr
    have h6 : T ^ A₂ ≤ ρ ^ (r * r * A₂) := by rw [pow_mul]; gcongr
    have h7 : ρ ^ (r * r * A₁) * ρ ^ (r * r * A₂) * ρ⁻¹ ^ m' = ρ⁻¹ ^ (r * r * m) := by
      have ha : ρ ^ (r * r * A₁) ≠ 0 := by positivity
      have hb : ρ ^ (r * r * A₂) ≠ 0 := by positivity
      rw [hm', mul_add, mul_add, pow_add, pow_add, inv_pow, inv_pow]
      field_simp
    calc ‖∑' δ : Cl, h δ‖ ≤ B₁' * T ^ A₁ * β := h1
      _ = B₁' * B₂ * (T ^ A₁ * T ^ A₂ * ρ⁻¹ ^ m') := by rw [hβ]; ring
      _ ≤ B₁' * B₂ * (ρ ^ (r * r * A₁) * ρ ^ (r * r * A₂) * ρ⁻¹ ^ m') := by gcongr
      _ = B₁' * B₂ * ρ⁻¹ ^ (r * r * m) := by rw [h7]
      _ ≤ B₁' * B₂ * ∏ i, (t i)⁻¹ ^ m := by gcongr
      _ ≤ _ := by
          rw [add_mul]
          have : 0 ≤ B₁' * M * R₀ ^ (r * r * (A₁ + m)) * ∏ i, (t i)⁻¹ ^ m := by
            have : 0 < R₀ := by linarith
            positivity
          linarith

end MainStatements.WeightKernel.RegInt

namespace MainStatements.WeightKernel.RegInt
open GlobalTheory.SiegelSet in

/- English proof (translation)
Introduce `hcore D V μ _ f hf hcusp γ hreg`. Establish `hknown` using `PositivityTheory.ThKR.siegel_of_core hcore`. Establish `hcm` using `isCMExt_host D`. Establish `hJ` using `GlobalTheory.Doubling.isHermND_gram V`. Take `⟨r, X, Y, hWF⟩` from `exists_isWittFrame hcm hJ`.

Take `⟨K, Ω, c, hK, hΩ, hΩP, hc, -, hcl, hcov, hconj, hmeas, -, -⟩` from `hknown _ _ D.sp.cm.sig hcm _ _ hJ r X Y hWF`. Take `⟨-, Cm, hbd⟩` from `hmeas μ inferInstance`. Take `⟨hfc, hfs⟩` from `GlobalTheory.Orb.continuous_of_mem_ccAd hf`. Establish `hcont : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f)` using `continuous_classKernel hfc hfs (rat_mem γ)`. Use `GlobalTheory.CompanionTheory.AutCover.integrable_descend_of_cover D V μ _ hcl.measurableSet hcov _ (fun δ hδ x => GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel_mul _ _ hδ x) hcont.measurable ?_` and prove the remaining obligations.

Take `⟨m₀, hm₀⟩` from `GlobalTheory.T.cone_integral_finite_large_exponent D.host.F V.rank r c hc`. Take `⟨B, hB0, hB⟩` from `class_bound hWF hK hΩ hΩP hc hconj hf hcusp hreg m₀`. Use `⟨hcont.aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Establish `hm` using `hm₀ m₀ le_rfl`. Use `set w : (Fin r → ℝ) → ENNReal := fun t => ENNReal.ofReal ((modulus D.host.F V.rank t * ∏ i, t i)⁻¹) with hw`.

Use `set q : (Fin r → ℝ) → ENNReal := fun t => ENNReal.ofReal (∏ i, (t i)⁻¹ ^ m₀) with hq`. Establish `hqm : Measurable q`. Use `ENNReal.measurable_ofReal.comp ?_` and prove the remaining obligations. Use `Finset.measurable_prod _ fun i _ => ?_` and prove the remaining obligations. Conclude with `((measurable_pi_apply i).inv).pow_const _`.

Establish `h1` using `hbd (fun g => ‖GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f g‖ₑ) (fun t => ENNReal.ofReal B * q t) (hqm.const_mul _) (fun p hp t ht a ha k hk => by`. Rewrite using `[← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul hB0]`. Conclude with `ENNReal.ofReal_le_ofReal (hB p hp t ht a ha k hk))`. Establish `h2 : ∫⁻ t in cone r c, ENNReal.ofReal B * q t * w t = ENNReal.ofReal B * ∫⁻ t in cone r c, q t * w t`. Rewrite using `[← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`.

Conclude with `lintegral_congr fun t => mul_assoc _ _ _`. Rewrite using `[HasFiniteIntegral]`. Use `lt_of_le_of_lt h1 ?_` and prove the remaining obligations. Rewrite using `[h2]`. Conclude with `ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hm)`.
-/
theorem regClassInt : PositivityTheory.ThKR.SiegelCore → MainStatements.RegularCuspidalTrace.RegClassInt := by
  intro hcore D V μ _ f hf hcusp γ hreg
  have hknown := PositivityTheory.ThKR.siegel_of_core hcore
  have hcm := isCMExt_host D
  have hJ := GlobalTheory.Doubling.isHermND_gram V
  obtain ⟨r, X, Y, hWF⟩ := exists_isWittFrame hcm hJ
  obtain ⟨K, Ω, c, hK, hΩ, hΩP, hc, -, hcl, hcov, hconj, hmeas, -, -⟩ := hknown _ _ D.sp.cm.sig hcm _ _ hJ r X Y hWF
  obtain ⟨-, Cm, hbd⟩ := hmeas μ inferInstance
  obtain ⟨hfc, hfs⟩ := GlobalTheory.Orb.continuous_of_mem_ccAd hf
  have hcont : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f) :=
    continuous_classKernel hfc hfs (rat_mem γ)
  refine GlobalTheory.CompanionTheory.AutCover.integrable_descend_of_cover D V μ _ hcl.measurableSet hcov _ (fun δ hδ x => GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel_mul _ _ hδ x)
    hcont.measurable ?_
  obtain ⟨m₀, hm₀⟩ := GlobalTheory.T.cone_integral_finite_large_exponent D.host.F V.rank r c hc
  obtain ⟨B, hB0, hB⟩ := class_bound hWF hK hΩ hΩP hc hconj hf hcusp hreg m₀
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  have hm := hm₀ m₀ le_rfl
  set w : (Fin r → ℝ) → ENNReal := fun t => ENNReal.ofReal ((modulus D.host.F V.rank t * ∏ i, t i)⁻¹) with hw
  set q : (Fin r → ℝ) → ENNReal := fun t => ENNReal.ofReal (∏ i, (t i)⁻¹ ^ m₀) with hq
  have hqm : Measurable q := by
    refine ENNReal.measurable_ofReal.comp ?_
    refine Finset.measurable_prod _ fun i _ => ?_
    exact ((measurable_pi_apply i).inv).pow_const _
  have h1 := hbd (fun g => ‖GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f g‖ₑ)
    (fun t => ENNReal.ofReal B * q t) (hqm.const_mul _) (fun p hp t ht a ha k hk => by
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul hB0]
      exact ENNReal.ofReal_le_ofReal (hB p hp t ht a ha k hk))
  have h2 : ∫⁻ t in cone r c, ENNReal.ofReal B * q t * w t =
      ENNReal.ofReal B * ∫⁻ t in cone r c, q t * w t := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_congr fun t => mul_assoc _ _ _
  rw [HasFiniteIntegral]
  refine lt_of_le_of_lt h1 ?_
  rw [h2]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hm)

end MainStatements.WeightKernel.RegInt
