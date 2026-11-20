import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSeparatedSmallCount
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionLatticeFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLocalRep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPacking
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open scoped ENNReal

noncomputable section

namespace SeparatedSmallCount

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [Fintype K] in

/- English proof (translation)
Introduce `m hm k`. Break down `Finset.mem_union.mp (MvPolynomial.support_sub _ f g hm) with h | h` into its components or cases. Conclude with `hf m h k`. Conclude with `hg m h k`.
-/
theorem isMultiHomog_sub {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_sub _ f g hm) with h | h
  · exact hf m h k
  · exact hg m h k

/- English proof (translation)
Establish `hdeg : dg' + dh = dg + dh'` using `funext fun k => by`. Establish `e1` using `hd k`. Establish `e2` using `hd' k`. Establish `: ((dg' k + dh k : ℕ) : ℤ) = ((dg k + dh' k : ℕ) : ℤ)` using `by push_cast; linarith`. Simplify `(Nat.cast_inj.mp this)` using `only [Pi.add_apply]`.

Establish `hm : IsMultiHomog (g * h' - g' * h) (dg + dh')` using `isMultiHomog_sub (LocalRep.isMultiHomog_mul hg hh') (by rw [← hdeg]; exact LocalRep.isMultiHomog_mul hg' hh)`. Establish `h0 : aeval y (g * h' - g' * h) = 0`. Rewrite using `[map_sub, map_mul, map_mul, he, he']`. Expand and normalize the polynomial expressions, which then agree. Establish `hmem : g * h' - g' * h ∈ mCoordIdeal y` using `by show g * h' - g' * h ∈ RingHom.ker (mConeMap y)`.

Rewrite using `[RingHom.mem_ker, ProjLine.mConeMap_eq_of_isMultiHomog y hm, h0, map_zero, zero_mul]`. Use `hz.2 _ hmem` as an intermediate fact. Rewrite `this` using `[map_sub, map_sub, map_mul, map_mul, map_mul, map_mul, sub_eq_zero]`. Conclude with `this`.
-/
theorem eval_cross {y : (Σ k, ι k) → Ω} {a : K → ℤ} {τ : ℕ} {s : Ω} {dg dh dg' dh' : K → ℕ}
    {g h g' h' : MRing ι} (hg : IsMultiHomog g dg) (hh : IsMultiHomog h dh)
    (hg' : IsMultiHomog g' dg') (hh' : IsMultiHomog h' dh')
    (hd : ∀ k, (dg k : ℤ) = dh k + τ * a k) (hd' : ∀ k, (dg' k : ℤ) = dh' k + τ * a k)
    (he : aeval y g = s * aeval y h) (he' : aeval y g' = s * aeval y h')
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) :
    eval z (map (Int.castRingHom ℂ) g) * eval z (map (Int.castRingHom ℂ) h') =
      eval z (map (Int.castRingHom ℂ) g') * eval z (map (Int.castRingHom ℂ) h) := by
  have hdeg : dg' + dh = dg + dh' := funext fun k => by
    have e1 := hd k
    have e2 := hd' k
    have : ((dg' k + dh k : ℕ) : ℤ) = ((dg k + dh' k : ℕ) : ℤ) := by push_cast; linarith
    simpa only [Pi.add_apply] using (Nat.cast_inj.mp this)
  have hm : IsMultiHomog (g * h' - g' * h) (dg + dh') :=
    isMultiHomog_sub (LocalRep.isMultiHomog_mul hg hh') (by rw [← hdeg]; exact LocalRep.isMultiHomog_mul hg' hh)
  have h0 : aeval y (g * h' - g' * h) = 0 := by
    rw [map_sub, map_mul, map_mul, he, he']
    ring
  have hmem : g * h' - g' * h ∈ mCoordIdeal y := by
    show g * h' - g' * h ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker, ProjLine.mConeMap_eq_of_isMultiHomog y hm, h0, map_zero, zero_mul]
  have := hz.2 _ hmem
  rw [map_sub, map_sub, map_mul, map_mul, map_mul, map_mul, sub_eq_zero] at this
  exact this

def IsSectionValue (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) (s : Ω) (z : (Σ k, ι k) → ℂ) (v : ℂ) : Prop :=
  ∃ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
    (∀ k, (dg k : ℤ) = dh k + τ * a k) ∧ aeval y g = s * aeval y h ∧
    eval z (map (Int.castRingHom ℂ) h) ≠ 0 ∧
    v = eval z (map (Int.castRingHom ℂ) g) / eval z (map (Int.castRingHom ℂ) h)

open Classical in

def sectionValue (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) (s : Ω) (z : (Σ k, ι k) → ℂ) : ℂ :=
  if h : ∃ v, IsSectionValue y a τ s z v then h.choose else 0

/- English proof (translation)
Take `⟨dg, dh, g, h, hg, hh, hd, he, hz0, rfl⟩` from `hv`. Take `⟨dg', dh', g', h', hg', hh', hd', he', hz0', rfl⟩` from `hw`. Rewrite using `[div_eq_div_iff hz0 hz0']`. Conclude with `eval_cross hg hh hg' hh' hd hd' he he' hz`.
-/
theorem isSectionValue_unique {y : (Σ k, ι k) → Ω} {a : K → ℤ} {τ : ℕ} {s : Ω} {z : (Σ k, ι k) → ℂ} {v w : ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) (hv : IsSectionValue y a τ s z v) (hw : IsSectionValue y a τ s z w) :
    v = w := by
  obtain ⟨dg, dh, g, h, hg, hh, hd, he, hz0, rfl⟩ := hv
  obtain ⟨dg', dh', g', h', hg', hh', hd', he', hz0', rfl⟩ := hw
  rw [div_eq_div_iff hz0 hz0']
  exact eval_cross hg hh hg' hh' hd hd' he he' hz

/- English proof (translation)
Establish `hex : ∃ v, IsSectionValue y a τ s z v` using `⟨v, hv⟩`. Unfold `sectionValue`. Rewrite using `[dif_pos hex]`. Conclude with `isSectionValue_unique hz hex.choose_spec hv`.
-/
theorem sectionValue_eq {y : (Σ k, ι k) → Ω} {a : K → ℤ} {τ : ℕ} {s : Ω} {z : (Σ k, ι k) → ℂ} {v : ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) (hv : IsSectionValue y a τ s z v) : sectionValue y a τ s z = v := by
  have hex : ∃ v, IsSectionValue y a τ s z v := ⟨v, hv⟩
  unfold sectionValue
  rw [dif_pos hex]
  exact isSectionValue_unique hz hex.choose_spec hv

/- English proof (translation)
Take `⟨dg, dh, g, h, hg, hh, hd, he, hz0⟩` from `LocalRep.proof K ι Ω y a τ s z hs hz`. Conclude with `⟨_, dg, dh, g, h, hg, hh, hd, he, hz0, rfl⟩`.
-/
theorem exists_isSectionValue {y : (Σ k, ι k) → Ω} {a : K → ℤ} {τ : ℕ} {s : Ω} {z : (Σ k, ι k) → ℂ}
    (hs : s ∈ chartLat y a τ) (hz : z ∈ mcPts (mCoordIdeal y)) : ∃ v, IsSectionValue y a τ s z v := by
  obtain ⟨dg, dh, g, h, hg, hh, hd, he, hz0⟩ := LocalRep.proof K ι Ω y a τ s z hs hz
  exact ⟨_, dg, dh, g, h, hg, hh, hd, he, hz0, rfl⟩

omit [Fintype K] in

/- English proof (translation)
Take `⟨dg, dh, g, h, hg, hh, hd, he, hz0, rfl⟩` from `hv`. Take `⟨dg', dh', g', h', hg', hh', hd', he', hz0', rfl⟩` from `hw`. Establish `hdeg : dg' + dh = dg + dh'` using `funext fun k => by`. Establish `e1` using `hd k`. Establish `e2` using `hd' k`.

Establish `: ((dg' k + dh k : ℕ) : ℤ) = ((dg k + dh' k : ℕ) : ℤ)` using `by push_cast; linarith`. Simplify `(Nat.cast_inj.mp this)` using `only [Pi.add_apply]`. Use `⟨dg + dh', dh + dh', g * h' + g' * h, h * h', LocalRep.isMultiHomog_add (LocalRep.isMultiHomog_mul hg hh') (by rw [← hdeg]; exact LocalRep.isMultiHomog_mul hg' hh), LocalRep.isMultiHomog_mul hh hh', fun k => ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply, Nat.cast_add]`. Combine the linear relations using `[hd k]`.

Rewrite using `[map_add, map_mul, map_mul, map_mul, he, he']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_mul, map_mul]`. Conclude with `mul_ne_zero hz0 hz0'`. Simplify using `only [map_add, map_mul]`.

Rewrite using `[div_add_div _ _ hz0 hz0']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isSectionValue_add {y : (Σ k, ι k) → Ω} {a : K → ℤ} {τ : ℕ} {s t : Ω} {z : (Σ k, ι k) → ℂ} {v w : ℂ}
    (hv : IsSectionValue y a τ s z v) (hw : IsSectionValue y a τ t z w) :
    IsSectionValue y a τ (s + t) z (v + w) := by
  obtain ⟨dg, dh, g, h, hg, hh, hd, he, hz0, rfl⟩ := hv
  obtain ⟨dg', dh', g', h', hg', hh', hd', he', hz0', rfl⟩ := hw
  have hdeg : dg' + dh = dg + dh' := funext fun k => by
    have e1 := hd k
    have e2 := hd' k
    have : ((dg' k + dh k : ℕ) : ℤ) = ((dg k + dh' k : ℕ) : ℤ) := by push_cast; linarith
    simpa only [Pi.add_apply] using (Nat.cast_inj.mp this)
  refine ⟨dg + dh', dh + dh', g * h' + g' * h, h * h',
    LocalRep.isMultiHomog_add (LocalRep.isMultiHomog_mul hg hh')
      (by rw [← hdeg]; exact LocalRep.isMultiHomog_mul hg' hh),
    LocalRep.isMultiHomog_mul hh hh', fun k => ?_, ?_, ?_, ?_⟩
  · simp only [Pi.add_apply, Nat.cast_add]
    linarith [hd k]
  · rw [map_add, map_mul, map_mul, map_mul, he, he']
    ring
  · rw [map_mul, map_mul]
    exact mul_ne_zero hz0 hz0'
  · simp only [map_add, map_mul]
    rw [div_add_div _ _ hz0 hz0']
    ring

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_isSectionValue hs hz`. Take `⟨w, hw⟩` from `exists_isSectionValue ht hz`. Rewrite using `[sectionValue_eq hz hv, sectionValue_eq hz hw, sectionValue_eq hz (isSectionValue_add hv hw)]`.
-/
theorem sectionValue_add {y : (Σ k, ι k) → Ω} {a : K → ℤ} {τ : ℕ} {s t : Ω} {z : (Σ k, ι k) → ℂ}
    (hs : s ∈ chartLat y a τ) (ht : t ∈ chartLat y a τ) (hz : z ∈ mcPts (mCoordIdeal y)) :
    sectionValue y a τ (s + t) z = sectionValue y a τ s z + sectionValue y a τ t z := by
  obtain ⟨v, hv⟩ := exists_isSectionValue hs hz
  obtain ⟨w, hw⟩ := exists_isSectionValue ht hz
  rw [sectionValue_eq hz hv, sectionValue_eq hz hw, sectionValue_eq hz (isSectionValue_add hv hw)]

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_isSectionValue hs hz`. Rewrite using `[sectionValue_eq hz hv]`. Take `⟨dg, dh, g, h, hg, hh, hd, he, hz0, rfl⟩` from `hv`. Establish `hle` using `hsm dg dh g h z hg hh hd he hz`. Rewrite using `[norm_div, div_le_iff₀ (norm_pos_iff.2 hz0)]`.

Conclude with `hle.trans_eq (mul_comm _ _)`.
-/
theorem norm_sectionValue_le_of_isSmallH {y : (Σ k, ι k) → Ω} {A : HermLine ι} {τ : ℕ} {s : Ω}
    {z : (Σ k, ι k) → ℂ} (hs : s ∈ chartLat y A.a τ) (hz : z ∈ mcPts (mCoordIdeal y))
    (hsm : IsSmallH (mCoordIdeal y) y A τ s) : ‖sectionValue y A.a τ s z‖ ≤ A.h z ^ τ := by
  obtain ⟨v, hv⟩ := exists_isSectionValue hs hz
  rw [sectionValue_eq hz hv]
  obtain ⟨dg, dh, g, h, hg, hh, hd, he, hz0, rfl⟩ := hv
  have hle := hsm dg dh g h z hg hh hd he hz
  rw [norm_div, div_le_iff₀ (norm_pos_iff.2 hz0)]
  exact hle.trans_eq (mul_comm _ _)

/- English proof (translation)
Introduce `dg dh g h z hg hh hd he hz`. Distinguish the cases in `hz0 : eval z (map (Int.castRingHom ℂ) h) = 0`. Take `⟨v, dg1, dh1, g1, h1, hg1, hh1, hd1, he1, hz1, -⟩` from `exists_isSectionValue hs hz`. Establish `hx` using `eval_cross hg hh hg1 hh1 hd hd1 he he1 hz`. Rewrite `hx` using `[hz0, mul_zero]`.

Establish `hg0 : eval z (map (Int.castRingHom ℂ) g) = 0` using `(mul_eq_zero.1 hx).resolve_right hz1`. Rewrite using `[hg0, hz0]`. Simplify using the standard rewrite rules. Establish `hv` using `sectionValue_eq hz ⟨dg, dh, g, h, hg, hh, hd, he, hz0, rfl⟩`. Establish `h1` using `hc z hz`.

Rewrite `h1` using `[hv, norm_div, div_le_iff₀ (norm_pos_iff.2 hz0)]`. Conclude with `h1.trans_eq (by ring)`.
-/
theorem isBoundedH_of_sectionValue {y : (Σ k, ι k) → Ω} {A : HermLine ι} {τ : ℕ} {s : Ω} {c : ℝ}
    (hs : s ∈ chartLat y A.a τ)
    (hc : ∀ z ∈ mcPts (mCoordIdeal y), ‖sectionValue y A.a τ s z‖ ≤ c * A.h z ^ τ) :
    IsBoundedH (mCoordIdeal y) y A τ c s := by
  intro dg dh g h z hg hh hd he hz
  by_cases hz0 : eval z (map (Int.castRingHom ℂ) h) = 0
  · obtain ⟨v, dg1, dh1, g1, h1, hg1, hh1, hd1, he1, hz1, -⟩ := exists_isSectionValue hs hz
    have hx := eval_cross hg hh hg1 hh1 hd hd1 he he1 hz
    rw [hz0, mul_zero] at hx
    have hg0 : eval z (map (Int.castRingHom ℂ) g) = 0 := (mul_eq_zero.1 hx).resolve_right hz1
    rw [hg0, hz0]
    simp
  · have hv := sectionValue_eq hz ⟨dg, dh, g, h, hg, hh, hd, he, hz0, rfl⟩
    have h1 := hc z hz
    rw [hv, norm_div, div_le_iff₀ (norm_pos_iff.2 hz0)] at h1
    exact h1.trans_eq (by ring)

end SeparatedSmallCount

open SeparatedSmallCount in

/- English proof (translation)
Introduce `K _ ι _ Ω _ y D A τ b hV _hB hb hsep`. Establish `hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0`. Introduce `k`. Take `⟨i, hi⟩` from `hV.2.1.2.2 k`. Use `⟨i, fun h0 => hi ?_⟩` and prove the remaining obligations.

Use `show (X ⟨k, i⟩ : MRing ι) ∈ RingHom.ker (mConeMap y)`. Rewrite using `[RingHom.mem_ker]`. Simplify using `[mConeMap, h0]`. Establish `hLfin : Module.Finite ℤ (chartLat y A.a τ)` using `Module.Finite.iff_addGroup_fg.2 ((AddGroup.fg_iff_addSubgroup_fg _).2 (hfin K ι Ω y A.a τ hy))`. Establish `hl3 : 0 ≤ b + Real.log 3` using `add_nonneg hb (Real.log_nonneg (by norm_num))`.

Distinguish the cases in `hS : {s : chartLat y A.a τ | IsSmallH (mCoordIdeal y) y A τ (s : Ω)}.Finite`. Use `swap`. Establish `: Infinite {s : chartLat y A.a τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)}` using `Set.infinite_coe_iff.2 hS`. Unfold `smallSectionCount`. Rewrite using `[Nat.card_eq_zero_of_infinite, Nat.cast_zero, Real.log_zero]`.

Conclude with `mul_nonneg (Nat.cast_nonneg _) hl3`. Establish `hpos : ∀ z : mcPts (mCoordIdeal y), 0 < A.h z` using `fun z => A.pos _ z.2.1`. Set `ψ : chartLat y A.a τ →+ (mcPts (mCoordIdeal y) → ℂ)` to `AddMonoidHom.mk' (fun s z => sectionValue y A.a τ (s : Ω) z / ((A.h z : ℂ) ^ τ)) (by`. Introduce `s t`. Use function extensionality and compare the values at `z`.

Simplify using `only [AddSubgroup.coe_add, Pi.add_apply]`. Rewrite using `[sectionValue_add s.2 t.2 z.2, add_div])`. Establish `hψ : ∀ s z, ‖ψ s z‖ = ‖sectionValue y A.a τ (s : Ω) z‖ / A.h z ^ τ` using `fun s z => by`. Simplify using `[ψ, norm_pow, abs_of_pos (hpos z)]`. Establish `hsmallψ : ∀ s : chartLat y A.a τ, IsSmallH (mCoordIdeal y) y A τ (s : Ω) → ∀ z, ‖ψ s z‖ ≤ 1`.

Introduce `s hs z`. Rewrite using `[hψ, div_le_one (pow_pos (hpos z) τ)]`. Conclude with `norm_sectionValue_le_of_isSmallH s.2 z.2 hs`. Set `W : AddSubgroup (chartLat y A.a τ)` to `{ carrier := {s | Memℓp (ψ s) ∞} zero_mem' := by show Memℓp (ψ 0) ∞`. Rewrite using `[map_zero]`.

Conclude with `zero_memℓp`. Use the proof step `add_mem' := fun {s t} hs ht => by show Memℓp (ψ (s + t)) ∞`. Rewrite using `[map_add]`. Conclude with `Memℓp.add hs ht`. Use the proof step `neg_mem' := fun {s} hs => by show Memℓp (ψ (-s)) ∞`.

Rewrite using `[map_neg]`. Conclude with `Memℓp.neg hs }`. Establish `hmemW : ∀ s : chartLat y A.a τ, IsSmallH (mCoordIdeal y) y A τ (s : Ω) → s ∈ W` using `fun s hs => memℓp_infty_iff.2 ⟨1, by rintro _ ⟨z, rfl⟩; exact hsmallψ s hs z⟩`. Set `φ : W →+ lp (fun _ : mcPts (mCoordIdeal y) => ℂ) ∞` to `AddMonoidHom.mk' (fun w => ⟨ψ w, w.2⟩) (fun v w => lp.ext (by show ψ ((v + w : W) : chartLat y A.a τ) = ψ v + ψ w`. Rewrite using `[AddSubgroup.coe_add, map_add]))`.

Set `F : chartLat y A.a τ → lp (fun _ : mcPts (mCoordIdeal y) => ℂ) ∞` to `fun s => if h : s ∈ W then φ ⟨s, h⟩ else 0`. Establish `hF : ∀ s (h : s ∈ W), F s = φ ⟨s, h⟩` using `fun s h => dif_pos h`. Establish `hFz : ∀ s (h : s ∈ W) z, F s z = ψ s z` using `fun s h z => by rw [hF s h]; rfl`. Establish `hnormF : ∀ s : chartLat y A.a τ, IsSmallH (mCoordIdeal y) y A τ (s : Ω) → ‖F s‖ ≤ 1`. Introduce `s hs`.

Use `lp.norm_le_of_forall_le zero_le_one fun z => ?_` and prove the remaining obligations. Rewrite using `[hFz s (hmemW s hs)]`. Conclude with `hsmallψ s hs z`. Establish `hdist : ∀ s t : chartLat y A.a τ, IsSmallH (mCoordIdeal y) y A τ (s : Ω) → IsSmallH (mCoordIdeal y) y A τ (t : Ω) → s ≠ t → Real.exp (-b) ≤ ‖F s - F t‖`. Introduce `s t hs ht hst`.

Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Use `hsep ((s - t : chartLat y A.a τ) : Ω) (s - t).2 (fun h0 => hst (sub_eq_zero.1 (Subtype.ext h0))) _ hlt (isBoundedH_of_sectionValue (s - t).2 fun z hz => ?_)` and prove the remaining obligations. Establish `h1 : ‖ψ (s - t) ⟨z, hz⟩‖ ≤ ‖F s - F t‖`. Use `lp.norm_apply_le_norm (by simp) (F s - F t) ⟨z, hz⟩` as an intermediate fact.

Rewrite `this` using `[lp.coeFn_sub, Pi.sub_apply, hFz s (hmemW s hs), hFz t (hmemW t ht)]`. Rewrite using `[map_sub, Pi.sub_apply]`. Conclude with `this`. Rewrite `h1` using `[hψ, div_le_iff₀ (pow_pos (hpos _) τ)]`. Conclude with `h1`.

Establish `hinj : Set.InjOn F hS.toFinset`. Introduce `s hs t ht hst`. Assume the negation of the conclusion as `hne`. Use `hdist s t (hS.mem_toFinset.1 hs) (hS.mem_toFinset.1 ht) hne` as an intermediate fact. Rewrite `this` using `[hst, sub_self, norm_zero]`.

Conclude with `absurd this (not_le.2 (Real.exp_pos _))`. Establish `hWfin : Module.Finite ℤ W`. Establish `h1 : (AddSubgroup.toIntSubmodule W).FG` using `IsNoetherian.noetherian _`. Establish `h2 : W.FG`. Use `(Submodule.fg_iff_addSubgroup_fg _).1 h1` as an intermediate fact.

Simplify using `using this`. Conclude with `Module.Finite.iff_addGroup_fg.2 ((AddGroup.fg_iff_addSubgroup_fg W).2 h2)`. Establish `hP` using `Packing.proof (lp (fun _ : mcPts (mCoordIdeal y) => ℂ) ∞) (LinearMap.range φ.toIntLinearMap) (hS.toFinset.image F) b hb (by`. Introduce `v hv`. Take `⟨s, hs, rfl⟩` from `Finset.mem_image.1 hv`.

Conclude with `LinearMap.mem_range.2 ⟨⟨s, hmemW s (hS.mem_toFinset.1 hs)⟩, (hF s _).symm⟩)`. Use the proof step `(by`. Introduce `v hv`. Take `⟨s, hs, rfl⟩` from `Finset.mem_image.1 hv`. Conclude with `hnormF s (hS.mem_toFinset.1 hs))`.

Use the proof step `(by`. Introduce `v hv w hw hvw`. Take `⟨s, hs, rfl⟩` from `Finset.mem_image.1 hv`. Take `⟨t, ht, rfl⟩` from `Finset.mem_image.1 hw`. Conclude with `hdist s t (hS.mem_toFinset.1 hs) (hS.mem_toFinset.1 ht) fun h => hvw (by rw [h]))`.

Rewrite `hP` using `[Finset.card_image_of_injOn hinj]`. Establish `hrank : (Module.finrank ℤ (LinearMap.range φ.toIntLinearMap) : ℝ) ≤ Module.finrank ℤ (chartLat y A.a τ)`. Establish `h1` using `LinearMap.finrank_range_le φ.toIntLinearMap`. Establish `h2 : Module.finrank ℤ W ≤ Module.finrank ℤ (chartLat y A.a τ)` using `LinearMap.finrank_le_finrank_of_injective (f := W.subtype.toIntLinearMap) fun a b h => Subtype.ext h`. Conclude with `h1.trans h2` after adjusting the coercions.

Unfold `smallSectionCount`. Rewrite using `[show Nat.card {s : chartLat y A.a τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)} = hS.toFinset.card from Nat.card_eq_card_finite_toFinset hS]`. Conclude with `hP.trans (mul_le_mul_of_nonneg_right hrank hl3)`.
-/
theorem SeparatedSmallCount.proof (hfin : SectionLatticeFinite.Statement) : SeparatedSmallCount.Statement := by
  classical
  intro K _ ι _ Ω _ y D A τ b hV _hB hb hsep
  have hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hV.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    show (X ⟨k, i⟩ : MRing ι) ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker]
    simp [mConeMap, h0]
  have hLfin : Module.Finite ℤ (chartLat y A.a τ) :=
    Module.Finite.iff_addGroup_fg.2 ((AddGroup.fg_iff_addSubgroup_fg _).2 (hfin K ι Ω y A.a τ hy))
  have hl3 : 0 ≤ b + Real.log 3 := add_nonneg hb (Real.log_nonneg (by norm_num))
  by_cases hS : {s : chartLat y A.a τ | IsSmallH (mCoordIdeal y) y A τ (s : Ω)}.Finite
  swap
  · have : Infinite {s : chartLat y A.a τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)} :=
      Set.infinite_coe_iff.2 hS
    unfold smallSectionCount
    rw [Nat.card_eq_zero_of_infinite, Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hl3
  have hpos : ∀ z : mcPts (mCoordIdeal y), 0 < A.h z := fun z => A.pos _ z.2.1

  let ψ : chartLat y A.a τ →+ (mcPts (mCoordIdeal y) → ℂ) :=
    AddMonoidHom.mk' (fun s z => sectionValue y A.a τ (s : Ω) z / ((A.h z : ℂ) ^ τ)) (by
      intro s t
      funext z
      simp only [AddSubgroup.coe_add, Pi.add_apply]
      rw [sectionValue_add s.2 t.2 z.2, add_div])
  have hψ : ∀ s z, ‖ψ s z‖ = ‖sectionValue y A.a τ (s : Ω) z‖ / A.h z ^ τ := fun s z => by
    simp [ψ, norm_pow, abs_of_pos (hpos z)]
  have hsmallψ : ∀ s : chartLat y A.a τ, IsSmallH (mCoordIdeal y) y A τ (s : Ω) → ∀ z, ‖ψ s z‖ ≤ 1 := by
    intro s hs z
    rw [hψ, div_le_one (pow_pos (hpos z) τ)]
    exact norm_sectionValue_le_of_isSmallH s.2 z.2 hs

  let W : AddSubgroup (chartLat y A.a τ) :=
    { carrier := {s | Memℓp (ψ s) ∞}
      zero_mem' := by
        show Memℓp (ψ 0) ∞
        rw [map_zero]
        exact zero_memℓp
      add_mem' := fun {s t} hs ht => by
        show Memℓp (ψ (s + t)) ∞
        rw [map_add]
        exact Memℓp.add hs ht
      neg_mem' := fun {s} hs => by
        show Memℓp (ψ (-s)) ∞
        rw [map_neg]
        exact Memℓp.neg hs }
  have hmemW : ∀ s : chartLat y A.a τ, IsSmallH (mCoordIdeal y) y A τ (s : Ω) → s ∈ W := fun s hs =>
    memℓp_infty_iff.2 ⟨1, by rintro _ ⟨z, rfl⟩; exact hsmallψ s hs z⟩
  let φ : W →+ lp (fun _ : mcPts (mCoordIdeal y) => ℂ) ∞ :=
    AddMonoidHom.mk' (fun w => ⟨ψ w, w.2⟩) (fun v w => lp.ext (by
      show ψ ((v + w : W) : chartLat y A.a τ) = ψ v + ψ w
      rw [AddSubgroup.coe_add, map_add]))
  let F : chartLat y A.a τ → lp (fun _ : mcPts (mCoordIdeal y) => ℂ) ∞ := fun s =>
    if h : s ∈ W then φ ⟨s, h⟩ else 0
  have hF : ∀ s (h : s ∈ W), F s = φ ⟨s, h⟩ := fun s h => dif_pos h
  have hFz : ∀ s (h : s ∈ W) z, F s z = ψ s z := fun s h z => by rw [hF s h]; rfl
  have hnormF : ∀ s : chartLat y A.a τ, IsSmallH (mCoordIdeal y) y A τ (s : Ω) → ‖F s‖ ≤ 1 := by
    intro s hs
    refine lp.norm_le_of_forall_le zero_le_one fun z => ?_
    rw [hFz s (hmemW s hs)]
    exact hsmallψ s hs z
  have hdist : ∀ s t : chartLat y A.a τ, IsSmallH (mCoordIdeal y) y A τ (s : Ω) →
      IsSmallH (mCoordIdeal y) y A τ (t : Ω) → s ≠ t → Real.exp (-b) ≤ ‖F s - F t‖ := by
    intro s t hs ht hst
    by_contra hlt
    rw [not_le] at hlt
    refine hsep ((s - t : chartLat y A.a τ) : Ω) (s - t).2
      (fun h0 => hst (sub_eq_zero.1 (Subtype.ext h0))) _ hlt
      (isBoundedH_of_sectionValue (s - t).2 fun z hz => ?_)
    have h1 : ‖ψ (s - t) ⟨z, hz⟩‖ ≤ ‖F s - F t‖ := by
      have := lp.norm_apply_le_norm (by simp) (F s - F t) ⟨z, hz⟩
      rw [lp.coeFn_sub, Pi.sub_apply, hFz s (hmemW s hs), hFz t (hmemW t ht)] at this
      rw [map_sub, Pi.sub_apply]
      exact this
    rw [hψ, div_le_iff₀ (pow_pos (hpos _) τ)] at h1
    exact h1

  have hinj : Set.InjOn F hS.toFinset := by
    intro s hs t ht hst
    by_contra hne
    have := hdist s t (hS.mem_toFinset.1 hs) (hS.mem_toFinset.1 ht) hne
    rw [hst, sub_self, norm_zero] at this
    exact absurd this (not_le.2 (Real.exp_pos _))
  have hWfin : Module.Finite ℤ W := by
    have h1 : (AddSubgroup.toIntSubmodule W).FG := IsNoetherian.noetherian _
    have h2 : W.FG := by
      have := (Submodule.fg_iff_addSubgroup_fg _).1 h1
      simpa using this
    exact Module.Finite.iff_addGroup_fg.2 ((AddGroup.fg_iff_addSubgroup_fg W).2 h2)
  have hP := Packing.proof (lp (fun _ : mcPts (mCoordIdeal y) => ℂ) ∞) (LinearMap.range φ.toIntLinearMap)
    (hS.toFinset.image F) b hb
    (by
      intro v hv
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hv
      exact LinearMap.mem_range.2 ⟨⟨s, hmemW s (hS.mem_toFinset.1 hs)⟩, (hF s _).symm⟩)
    (by
      intro v hv
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hv
      exact hnormF s (hS.mem_toFinset.1 hs))
    (by
      intro v hv w hw hvw
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hv
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hw
      exact hdist s t (hS.mem_toFinset.1 hs) (hS.mem_toFinset.1 ht) fun h => hvw (by rw [h]))
  rw [Finset.card_image_of_injOn hinj] at hP
  have hrank : (Module.finrank ℤ (LinearMap.range φ.toIntLinearMap) : ℝ) ≤
      Module.finrank ℤ (chartLat y A.a τ) := by
    have h1 := LinearMap.finrank_range_le φ.toIntLinearMap
    have h2 : Module.finrank ℤ W ≤ Module.finrank ℤ (chartLat y A.a τ) :=
      LinearMap.finrank_le_finrank_of_injective (f := W.subtype.toIntLinearMap) fun a b h => Subtype.ext h
    exact_mod_cast h1.trans h2
  unfold smallSectionCount
  rw [show Nat.card {s : chartLat y A.a τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)} = hS.toFinset.card from
    Nat.card_eq_card_finite_toFinset hS]
  exact hP.trans (mul_le_mul_of_nonneg_right hrank hl3)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
