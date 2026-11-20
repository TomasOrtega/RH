import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumLocallyUniformlyOnTerm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ProdTermAddPeriodTranslationLattice

noncomputable section

namespace GlobalTheory.SpanFrame

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped LaurentSeries PowerSeries

/- English proof (translation)
Take `⟨π, hπ⟩` from `(Algebra.linearMap F K).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 (algebraMap F K).injective)`. Establish `h1 : π 1 = 1` using `by simpa using LinearMap.congr_fun hπ 1`. Use `⟨fun a i => π (c a i), fun a i => (π _).2, fun a l => ?_⟩` and prove the remaining obligations. Establish `e` using `congrArg (fun x => (π x : K)) (h a l)`. Establish `e' : ∀ i, π (c a i * r i l) = (⟨r i l, hr i l⟩ : F) * π (c a i)` using `fun i => by`.

Rewrite using `[mul_comm (c a i)]`. Conclude with `map_smul π (⟨r i l, hr i l⟩ : F) (c a i)`. Simplify using `only [map_sum, e', apply_ite π, h1, map_zero] at e`. Rewrite `e` using `[IntermediateField.coe_sum]`. Use `Eq.trans (Finset.sum_congr rfl fun i _ => mul_comm _ _) (e.trans ?_)` and prove the remaining obligations.

Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem exists_inverse_mem {k K : Type} [Field k] [Field K] [Algebra k K] (F : IntermediateField k K) {ι κ : Type}
    [Fintype ι] [DecidableEq κ] (c : κ → ι → K) (r : ι → κ → K) (hr : ∀ i l, r i l ∈ F)
    (h : ∀ a l, ∑ i, c a i * r i l = if a = l then 1 else 0) :
    ∃ c' : κ → ι → K, (∀ a i, c' a i ∈ F) ∧ ∀ a l, ∑ i, c' a i * r i l = if a = l then 1 else 0 := by
  obtain ⟨π, hπ⟩ := (Algebra.linearMap F K).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (algebraMap F K).injective)
  have h1 : π 1 = 1 := by simpa using LinearMap.congr_fun hπ 1
  refine ⟨fun a i => π (c a i), fun a i => (π _).2, fun a l => ?_⟩
  have e := congrArg (fun x => (π x : K)) (h a l)
  have e' : ∀ i, π (c a i * r i l) = (⟨r i l, hr i l⟩ : F) * π (c a i) := fun i => by
    rw [mul_comm (c a i)]; exact map_smul π (⟨r i l, hr i l⟩ : F) (c a i)
  simp only [map_sum, e', apply_ite π, h1, map_zero] at e
  rw [IntermediateField.coe_sum] at e
  refine Eq.trans (Finset.sum_congr rfl fun i _ => mul_comm _ _) (e.trans ?_)
  split_ifs <;> rfl

variable {O : Type} [CommRing O] [StarRing O] {A : AnArc O} {N : ℕ} [NeZero N]

/- English proof (translation)
The claim follows from `let ⟨n, r, α, th, h1, h2⟩ := hf ⟨n, r, α, th, fun i => ⟨h (h1 i).1, (h1 i).2⟩, h2⟩`.
-/
theorem IsComb.mono {B B' : Set ℂ⸨X⸩} (h : B ⊆ B') {f : A.V → ℂ⸨X⸩} (hf : IsComb A N B f) : IsComb A N B' f :=
  let ⟨n, r, α, th, h1, h2⟩ := hf
  ⟨n, r, α, th, fun i => ⟨h (h1 i).1, (h1 i).2⟩, h2⟩

/- English proof (translation)
Use `choose T₁ hT₁ hT₁' using hf`. Use `choose ρ hρ hρ' using hsp`. Establish `hR : ∀ i, ∃ R : Fin n → ℂ⸨X⸩, (∀ l, R l ∈ Conv.convLaurent) ∧ ∀ v, f i v = ∑ l, R l * A.FSum N (α l) (th l) v` using `fun i => by`. Take `⟨p, r, β, t, h1, h2⟩` from `hT₁ i`. Use `⟨fun l => ∑ a, r a * ρ (β a) (t a) (h1 a).2 l, fun l => sum_mem fun a _ => mul_mem (Conv.halfRing_le_convLaurent _ (h1 a).1) (Conv.halfRing_le_convLaurent 0 (hρ _ _ _ l 0)), fun v => ?_⟩` and prove the remaining obligations.

Rewrite using `[h2]`. Simplify using `only [Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[hρ' _ _ (h1 a).2 v, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun l _ => (mul_assoc _ _ _).symm`. Use `choose R hR hR' using hR`. Use `choose c hc using fun a => hs (α a) (th a) (hth a)`. Establish `key : ∀ (c : Fin m → ℂ⸨X⸩) v, ∑ i, c i * f i v = ∑ l, (∑ i, c i * R i l) * A.FSum N (α l) (th l) v` using `fun c v => by`. Simplify using `only [hR', Finset.mul_sum, Finset.sum_mul, mul_assoc]`.

Conclude with `Finset.sum_comm`. Take `⟨c', hc', hc''⟩` from `exists_inverse_mem Conv.convLaurent c R hR fun a l => Fintype.linearIndependent_iffₛ.1 hli (fun l => ∑ i, c a i * R i l) (fun l => if a = l then 1 else 0) (by`. Use function extensionality and compare the values at `v`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← key, ← hc]`.

Use the proof step `simp) l`. Establish `hF : ∀ a v, A.FSum N (α a) (th a) v = ∑ i, c' a i * f i v` using `fun a v => by`. Rewrite using `[key]`. Simplify using `[hc'']`. Use `choose T₂ hT₂ using fun a i => Conv.mem_convLaurent_iff_halfRing.1 (hc' a i)`.

Take `⟨T₀, h₀⟩` from `A.exists_isConvLine`. Take `⟨B₁, hB₁⟩` from `Finite.exists_le T₁`. Take `⟨B₂, hB₂⟩` from `Finite.exists_le (fun p : Fin n × Fin m => T₂ p.1 p.2)`. Establish `l₀ : T₀ ≤ max T₀ (max B₁ B₂)` using `le_max_left _ _`. Establish `l₁ : ∀ i, T₁ i ≤ max T₀ (max B₁ B₂)` using `fun i => (hB₁ i).trans ((le_max_left _ _).trans (le_max_right _ _))`.

Establish `l₂ : ∀ a i, T₂ a i ≤ max T₀ (max B₁ B₂)` using `fun a i => (hB₂ (a, i)).trans ((le_max_right _ _).trans (le_max_right _ _))`. Generalize the expression as in `max T₀ (max B₁ B₂) = T at l₀ l₁ l₂`. Establish `hT` using `h₀.mono l₀`. Use `⟨T, fun i v => Conv.halfRing_mono (l₁ i) (hT₁' i v), fun i => IsComb.mono (Conv.halfRing_mono (l₁ i)) (hT₁ i), fun w hw v => ?_⟩` and prove the remaining obligations. Take `⟨t₁, ht₁, ht₁'⟩` from `hA.2`.

Take `⟨β, t, ht, hne⟩` from `A.exists_Sum_ne_zero_at hT ht₁ ht₁' hw hN v`. Assume the negation of the conclusion as `hz`. Use `push Not at hz`. Establish `hm : A.FSum N β t v ∈ Conv.halfRing T` using `fun _ hw => (AnArc.hasSum_coeff_FSum hT ht hw v).summable`. Establish `e : (⟨_, hm⟩ : Conv.halfRing T) = ∑ a, ⟨_, hρ β t ht a T⟩ * ∑ i, (⟨_, Conv.halfRing_mono (l₂ a i) (hT₂ a i)⟩ : Conv.halfRing T) * ⟨f i v, Conv.halfRing_mono (l₁ i) (hT₁' i v)⟩`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, ← hF]`. Conclude with `hρ' β t ht v`. Use `hne ((Conv.ev_eq_of_hasSum hw ⟨_, hm⟩ (AnArc.hasSum_coeff_FSum hT ht hw v)).symm.trans ?_)` and prove the remaining obligations. Rewrite using `[e]`.

Simplify using `only [map_sum, map_mul, hz, mul_zero, Finset.sum_const_zero]`.
-/
theorem exists_no_common_zero (hA : AnFin A) (hN : 2 ≤ N) {n : ℕ} {α : Fin n → A.X}
    {th : Fin n → (Fin A.gB → ℂ) → ℂ} (hth : ∀ i, th i ∈ A.Theta N (α i))
    (hli : LinearIndependent ℂ⸨X⸩ (fun i v => A.FSum N (α i) (th i) v))
    (hsp : ∀ α', ∀ th' ∈ A.Theta N α', ∃ r : Fin n → ℂ⸨X⸩, (∀ i T, r i ∈ Conv.halfRing T) ∧
      ∀ v, A.FSum N α' th' v = ∑ i, r i * A.FSum N (α i) (th i) v)
    {m : ℕ} (f : Fin m → A.V → ℂ⸨X⸩)
    (hf : ∀ i, ∃ T : ℝ, IsComb A N (Conv.halfRing T) (f i) ∧ ∀ v, f i v ∈ Conv.halfRing T)
    (hs : ∀ α', ∀ th' ∈ A.Theta N α', ∃ c : Fin m → ℂ⸨X⸩, ∀ v, A.FSum N α' th' v = ∑ i, c i * f i v) :
    ∃ (T : ℝ) (hm : ∀ i v, f i v ∈ Conv.halfRing T), (∀ i, IsComb A N (Conv.halfRing T) (f i)) ∧
      ∀ (w : ℂ) (hw : T < w.im) v, ∃ i, Conv.ev T w hw ⟨f i v, hm i v⟩ ≠ 0 := by
  classical
  choose T₁ hT₁ hT₁' using hf
  choose ρ hρ hρ' using hsp
  have hR : ∀ i, ∃ R : Fin n → ℂ⸨X⸩, (∀ l, R l ∈ Conv.convLaurent) ∧
      ∀ v, f i v = ∑ l, R l * A.FSum N (α l) (th l) v := fun i => by
    obtain ⟨p, r, β, t, h1, h2⟩ := hT₁ i
    refine ⟨fun l => ∑ a, r a * ρ (β a) (t a) (h1 a).2 l, fun l => sum_mem fun a _ => mul_mem
      (Conv.halfRing_le_convLaurent _ (h1 a).1) (Conv.halfRing_le_convLaurent 0 (hρ _ _ _ l 0)), fun v => ?_⟩
    rw [h2]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hρ' _ _ (h1 a).2 v, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => (mul_assoc _ _ _).symm
  choose R hR hR' using hR
  choose c hc using fun a => hs (α a) (th a) (hth a)
  have key : ∀ (c : Fin m → ℂ⸨X⸩) v, ∑ i, c i * f i v = ∑ l, (∑ i, c i * R i l) * A.FSum N (α l) (th l) v :=
    fun c v => by
      simp only [hR', Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm
  obtain ⟨c', hc', hc''⟩ := exists_inverse_mem Conv.convLaurent c R hR fun a l =>
    Fintype.linearIndependent_iffₛ.1 hli (fun l => ∑ i, c a i * R i l) (fun l => if a = l then 1 else 0) (by
      funext v
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [← key, ← hc]
      simp) l
  have hF : ∀ a v, A.FSum N (α a) (th a) v = ∑ i, c' a i * f i v := fun a v => by
    rw [key]
    simp [hc'']
  choose T₂ hT₂ using fun a i => Conv.mem_convLaurent_iff_halfRing.1 (hc' a i)
  obtain ⟨T₀, h₀⟩ := A.exists_isConvLine
  obtain ⟨B₁, hB₁⟩ := Finite.exists_le T₁
  obtain ⟨B₂, hB₂⟩ := Finite.exists_le (fun p : Fin n × Fin m => T₂ p.1 p.2)
  have l₀ : T₀ ≤ max T₀ (max B₁ B₂) := le_max_left _ _
  have l₁ : ∀ i, T₁ i ≤ max T₀ (max B₁ B₂) := fun i => (hB₁ i).trans ((le_max_left _ _).trans (le_max_right _ _))
  have l₂ : ∀ a i, T₂ a i ≤ max T₀ (max B₁ B₂) := fun a i =>
    (hB₂ (a, i)).trans ((le_max_right _ _).trans (le_max_right _ _))
  generalize max T₀ (max B₁ B₂) = T at l₀ l₁ l₂
  have hT := h₀.mono l₀
  refine ⟨T, fun i v => Conv.halfRing_mono (l₁ i) (hT₁' i v),
    fun i => IsComb.mono (Conv.halfRing_mono (l₁ i)) (hT₁ i), fun w hw v => ?_⟩
  obtain ⟨t₁, ht₁, ht₁'⟩ := hA.2
  obtain ⟨β, t, ht, hne⟩ := A.exists_Sum_ne_zero_at hT ht₁ ht₁' hw hN v
  by_contra hz
  push Not at hz
  have hm : A.FSum N β t v ∈ Conv.halfRing T := fun _ hw => (AnArc.hasSum_coeff_FSum hT ht hw v).summable
  have e : (⟨_, hm⟩ : Conv.halfRing T) = ∑ a, ⟨_, hρ β t ht a T⟩ * ∑ i,
      (⟨_, Conv.halfRing_mono (l₂ a i) (hT₂ a i)⟩ : Conv.halfRing T) *
        ⟨f i v, Conv.halfRing_mono (l₁ i) (hT₁' i v)⟩ := by
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, ← hF]
    exact hρ' β t ht v
  refine hne ((Conv.ev_eq_of_hasSum hw ⟨_, hm⟩ (AnArc.hasSum_coeff_FSum hT ht hw v)).symm.trans ?_)
  rw [e]
  simp only [map_sum, map_mul, hz, mul_zero, Finset.sum_const_zero]

end GlobalTheory.SpanFrame
