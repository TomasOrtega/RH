import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl

open IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.FinPl

section General

variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, hax⟩` from `hx`.

Take `⟨b, hb, hby⟩` from `hy`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations. Establish `h1 : (a * b) • x = b • (a • x)` using `by rw [mul_comm, mul_smul]`. Establish `h2 : (a * b) • y = a • (b • y)` using `by rw [mul_smul]`. Rewrite using `[smul_add, h1, h2]`.

Conclude with `M.add_mem (zsmul_mem hax b) (zsmul_mem hby a)`. Consider the case `smul e x _ hx`. Take `⟨a, ha, hax⟩` from `hx`. Take `⟨c, hc, hint⟩` from `exists_integral_multiples ℤ ℚ ({e} : Finset E)`. Establish `he : IsIntegral ℤ (c • e)` using `hint e (by simp)`.

Use `⟨c * a, mul_ne_zero hc ha, ?_⟩` and prove the remaining obligations. Take `⟨o, ho⟩ : ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = c • e` from `⟨⟨c • e, he⟩, rfl⟩`. Establish `h : (c * a) • (e • x) = o • (a • x)`. Rewrite using `[← algebraMap_smul E o (a • x), ho, mul_smul, smul_comm a e x, smul_assoc]`. Rewrite using `[h]`.

Conclude with `M.smul_mem o hax`.
-/
theorem exists_int_smul_mem_of_mem_span (M : Submodule (𝓞 E) V) {y : V}
    (hy : y ∈ Submodule.span E (M : Set V)) : ∃ c : ℤ, c ≠ 0 ∧ c • y ∈ M := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • x = b • (a • x) := by rw [mul_comm, mul_smul]
    have h2 : (a * b) • y = a • (b • y) := by rw [mul_smul]
    rw [smul_add, h1, h2]
    exact M.add_mem (zsmul_mem hax b) (zsmul_mem hby a)
  | smul e x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨c, hc, hint⟩ := exists_integral_multiples ℤ ℚ ({e} : Finset E)
    have he : IsIntegral ℤ (c • e) := hint e (by simp)
    refine ⟨c * a, mul_ne_zero hc ha, ?_⟩
    obtain ⟨o, ho⟩ : ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = c • e := ⟨⟨c • e, he⟩, rfl⟩
    have h : (c * a) • (e • x) = o • (a • x) := by
      rw [← algebraMap_smul E o (a • x), ho, mul_smul, smul_comm a e x, smul_assoc]
    rw [h]
    exact M.smul_mem o hax

/- English proof (translation)
Take `⟨G, rfl⟩` from `hL`. Establish `hg : ∀ g ∈ G, ∃ c : ℤ, c ≠ 0 ∧ c • g ∈ M` using `fun g _ => exists_int_smul_mem_of_mem_span M (by rw [hM]; trivial)`. Use `choose! c hc0 hcM using hg`. Use `⟨∏ g ∈ G, c g, Finset.prod_ne_zero_iff.2 hc0, fun x hx => ?_⟩` and prove the remaining obligations. Set `N : Submodule (𝓞 E) V` to `{ carrier := {y | (∏ g ∈ G, c g) • y ∈ M} add_mem' := fun {a b} ha hb => by`.

Simplify using `only [Set.mem_setOf_eq, smul_add] at *`. Conclude with `M.add_mem ha hb`. Use the proof step `zero_mem' := by simp`. Use the proof step `smul_mem' := fun r y hy => by`. Simplify using `only [Set.mem_setOf_eq] at *`.

Rewrite using `[smul_comm]`. Conclude with `M.smul_mem r hy }`. Establish `hle : Submodule.span (𝓞 E) (G : Set V) ≤ N`. Rewrite using `[Submodule.span_le]`. Introduce `g hg`.

Use `show (∏ g ∈ G, c g) • g ∈ M`. Rewrite using `[← Finset.mul_prod_erase G c hg, mul_comm, mul_smul]`. Conclude with `zsmul_mem (hcM g hg) _`. Conclude with `hle hx`.
-/
theorem exists_int_smul_le (L M : Submodule (𝓞 E) V) (hL : L.FG)
    (hM : Submodule.span E (M : Set V) = ⊤) : ∃ d : ℤ, d ≠ 0 ∧ ∀ x ∈ L, d • x ∈ M := by
  classical
  obtain ⟨G, rfl⟩ := hL
  have hg : ∀ g ∈ G, ∃ c : ℤ, c ≠ 0 ∧ c • g ∈ M := fun g _ =>
    exists_int_smul_mem_of_mem_span M (by rw [hM]; trivial)
  choose! c hc0 hcM using hg
  refine ⟨∏ g ∈ G, c g, Finset.prod_ne_zero_iff.2 hc0, fun x hx => ?_⟩
  let N : Submodule (𝓞 E) V :=
    { carrier := {y | (∏ g ∈ G, c g) • y ∈ M}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, smul_add] at *; exact M.add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun r y hy => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_comm]; exact M.smul_mem r hy }
  have hle : Submodule.span (𝓞 E) (G : Set V) ≤ N := by
    rw [Submodule.span_le]
    intro g hg
    show (∏ g ∈ G, c g) • g ∈ M
    rw [← Finset.mul_prod_erase G c hg, mul_comm, mul_smul]
    exact zsmul_mem (hcM g hg) _
  exact hle hx

end General

variable {D : D7}

/- English proof (translation)
Establish `h0 : Ideal.span {((d : 𝓞 D.host.F))} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hd` after adjusting the coercions. Use `(Ideal.finite_factors h0).subset fun v hv => ?_` and prove the remaining obligations. Use `show v.asIdeal ∣ _`.

Rewrite using `[Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`. Conclude with `hv`.
-/
theorem finite_places_int (d : ℤ) (hd : d ≠ 0) :
    {v : Pl D | ((d : 𝓞 D.host.F)) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((d : 𝓞 D.host.F))} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hd
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

/- English proof (translation)
Establish `hdF : (d : F) ≠ 0` using `Int.cast_ne_zero.2 hd`. Establish `h : (d : F) • pairA F 0 ((d : F)⁻¹ • α) = pairA F 0 α`. Establish `h1 : (d : F) • pairA F 0 ((d : F)⁻¹ • α) = pairA F 0 ((d : F) • (d : F)⁻¹ • α)` using `Prod.ext (smul_zero (d : F)) rfl`. Rewrite using `[h1, smul_smul, mul_inv_cancel₀ hdF, one_smul]`. Rewrite using `[one_mul, one_mul, ← Int.cast_smul_eq_zsmul F, ← TensorProduct.smul_tmul, h]`.
-/
theorem pairA_tmul_int_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (d : ℤ) (hd : d ≠ 0)
    (α : Af F) (e : E) :
    pairA F 0 α ⊗ₜ[F] (1 * e) = pairA F 0 ((d : F)⁻¹ • α) ⊗ₜ[F] (1 * (d • e)) := by
  have hdF : (d : F) ≠ 0 := Int.cast_ne_zero.2 hd
  have h : (d : F) • pairA F 0 ((d : F)⁻¹ • α) = pairA F 0 α := by
    have h1 : (d : F) • pairA F 0 ((d : F)⁻¹ • α) = pairA F 0 ((d : F) • (d : F)⁻¹ • α) :=
      Prod.ext (smul_zero (d : F)) rfl
    rw [h1, smul_smul, mul_inv_cancel₀ hdF, one_smul]
  rw [one_mul, one_mul, ← Int.cast_smul_eq_zsmul F, ← TensorProduct.smul_tmul, h]

/- English proof (translation)
Rewrite using `[latV, latMul, AddSubgroup.closure_le]`. Introduce and unpack `y ⟨α, hα, hsupp, a, ha, x, hx, rfl⟩`. Rewrite `ha` using `[Set.mem_singleton_iff]`. Substitute `ha` using the available equality. Establish `hval : Valued.v (algebraMap D.host.F (v.adicCompletion D.host.F) (d : D.host.F)) = 1`.

Establish `h1` using `(v.valuation_eq_one_iff_notMem (K := D.host.F)).mpr hv`. Establish `h2` using `v.valuedAdicCompletion_eq_valuation' (K := D.host.F) ((d : D.host.F))`. Establish `h4 : (((d : 𝓞 D.host.F)) : D.host.F) = ((d : D.host.F))` using `map_intCast (algebraMap (𝓞 D.host.F) D.host.F) _`. Conclude with `h2.trans (h4 ▸ h1)`. Apply `AddSubgroup.subset_closure` to reduce the goal to its premises.

Use `⟨((d : D.host.F))⁻¹ • α, ?_, ?_, 1, rfl, d • x, hLM x hx, ?_⟩` and prove the remaining obligations. Introduce `w`. Rewrite using `[map_smul]`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality.

Establish `hαw` using `hα w`. Rewrite `hαw`, the goal using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Rewrite using `[Algebra.smul_def, map_mul, map_inv₀, map_inv₀, hval, inv_one, one_mul]`. Conclude with `hαw`. Rewrite using `[hsupp w hw, smul_zero]`.

Conclude with `zero_mem _`. Introduce `w hw`. Rewrite using `[map_smul, hsupp w hw, smul_zero]`. Use function extensionality and compare the values at `i`. Conclude with `pairA_tmul_int_gen d hd α (x i)`.
-/
theorem latV_le_of_int_smul (S : HSp D) (L M : Lat S) (d : ℤ) (hd : d ≠ 0)
    (hLM : ∀ x ∈ L, d • x ∈ M) (v : Pl D) (hv : ((d : 𝓞 D.host.F)) ∉ v.asIdeal) :
    latV S L (· = v) ≤ latV S M (· = v) := by
  rw [latV, latMul, AddSubgroup.closure_le]
  rintro y ⟨α, hα, hsupp, a, ha, x, hx, rfl⟩
  rw [Set.mem_singleton_iff] at ha
  subst ha
  have hval : Valued.v (algebraMap D.host.F (v.adicCompletion D.host.F) (d : D.host.F)) = 1 := by
    have h1 := (v.valuation_eq_one_iff_notMem (K := D.host.F)).mpr hv
    have h2 := v.valuedAdicCompletion_eq_valuation' (K := D.host.F) ((d : D.host.F))
    have h4 : (((d : 𝓞 D.host.F)) : D.host.F) = ((d : D.host.F)) :=
      map_intCast (algebraMap (𝓞 D.host.F) D.host.F) _
    exact h2.trans (h4 ▸ h1)
  apply AddSubgroup.subset_closure
  refine ⟨((d : D.host.F))⁻¹ • α, ?_, ?_, 1, rfl, d • x, hLM x hx, ?_⟩
  · intro w
    rw [map_smul]
    by_cases hw : w = v
    · subst hw
      have hαw := hα w
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hαw ⊢
      rw [Algebra.smul_def, map_mul, map_inv₀, map_inv₀, hval, inv_one, one_mul]
      exact hαw
    · rw [hsupp w hw, smul_zero]
      exact zero_mem _
  · intro w hw
    rw [map_smul, hsupp w hw, smul_zero]
  · funext i
    exact pairA_tmul_int_gen d hd α (x i)

/- English proof (translation)
Introduce `D S L M hL hM`. Take `⟨d₁, hd₁, h₁⟩` from `exists_int_smul_le L M hL.fg hM.span_eq_top`. Take `⟨d₂, hd₂, h₂⟩` from `exists_int_smul_le M L hM.fg hL.span_eq_top`. Establish `hd : d₁ * d₂ ≠ 0` using `mul_ne_zero hd₁ hd₂`. Use `⟨(finite_places_int (D := D) (d₁ * d₂) hd).toFinset, fun v hv => ?_⟩` and prove the remaining obligations.

Rewrite `hv` using `[Set.Finite.mem_toFinset, Set.mem_setOf_eq, Int.cast_mul]`. Establish `hv₁ : ((d₁ : 𝓞 D.host.F)) ∉ v.asIdeal` using `fun h => hv (v.asIdeal.mul_mem_right _ h)`. Establish `hv₂ : ((d₂ : 𝓞 D.host.F)) ∉ v.asIdeal` using `fun h => hv (v.asIdeal.mul_mem_left _ h)`. Conclude with `le_antisymm (latV_le_of_int_smul S L M d₁ hd₁ h₁ v hv₁) (latV_le_of_int_smul S M L d₂ hd₂ h₂ v hv₂)`.
-/
theorem latV_eq_off_finite : ∀ (D : D7) (S : HSp D) (L M : Lat S), Submodule.IsLattice D.host.E L →
    Submodule.IsLattice D.host.E M → ∃ T : Finset (Pl D), ∀ v, v ∉ T → latV S L (· = v) = latV S M (· = v) := by
  intro D S L M hL hM
  obtain ⟨d₁, hd₁, h₁⟩ := exists_int_smul_le L M hL.fg hM.span_eq_top
  obtain ⟨d₂, hd₂, h₂⟩ := exists_int_smul_le M L hM.fg hL.span_eq_top
  have hd : d₁ * d₂ ≠ 0 := mul_ne_zero hd₁ hd₂
  refine ⟨(finite_places_int (D := D) (d₁ * d₂) hd).toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Int.cast_mul] at hv
  have hv₁ : ((d₁ : 𝓞 D.host.F)) ∉ v.asIdeal := fun h => hv (v.asIdeal.mul_mem_right _ h)
  have hv₂ : ((d₂ : 𝓞 D.host.F)) ∉ v.asIdeal := fun h => hv (v.asIdeal.mul_mem_left _ h)
  exact le_antisymm (latV_le_of_int_smul S L M d₁ hd₁ h₁ v hv₁) (latV_le_of_int_smul S M L d₂ hd₂ h₂ v hv₂)

end GlobalTheory.FinPl
