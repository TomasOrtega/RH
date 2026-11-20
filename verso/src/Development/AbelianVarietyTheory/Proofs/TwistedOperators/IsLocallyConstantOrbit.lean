import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TwistedKernelFixed

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory

namespace GlobalTheory.IwahoriInj

section Abstract

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun hv h hh => by simpa using hv ⟨h, hh⟩, fun hv h => by simpa using hv h h.2⟩`.
-/
theorem mem_fixed {H : Subgroup G} {v : V} : v ∈ fixed π H ↔ ∀ h ∈ H, π h v = v :=
  ⟨fun hv h hh => by simpa using hv ⟨h, hh⟩, fun hv h => by simpa using hv h h.2⟩

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨⟨h, hh⟩, v, by simp⟩`.
-/
theorem sub_mem_twKer {H : Subgroup G} {h : G} (hh : h ∈ H) (v : V) : π h v - v ∈ twKer π H 1 :=
  Submodule.subset_span ⟨⟨h, hh⟩, v, by simp⟩

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨h, v, rfl⟩`. Simplify using `using sub_mem_twKer (hle h.2) v`.
-/
theorem twKer_mono {H K : Subgroup G} (hle : H ≤ K) : twKer π H 1 ≤ twKer π K 1 := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨h, v, rfl⟩
  simpa using sub_mem_twKer (hle h.2) v

/- English proof (translation)
Simplify using `using add_mem (sub_mem_twKer hh v) hv`.
-/
theorem apply_mem_twKer {H : Subgroup G} {h : G} (hh : h ∈ H) {v : V} (hv : v ∈ twKer π H 1) :
    π h v ∈ twKer π H 1 := by
  simpa using add_mem (sub_mem_twKer hh v) hv

variable [TopologicalSpace G] [IsTopologicalGroup G]

/- English proof (translation)
Use `(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_` and prove the remaining obligations. Establish `h : IsOpen ((fun g : G => x⁻¹ * g) ⁻¹' {g : G | π g v = v})` using `(hπ v).preimage (by fun_prop)`. Use `filter_upwards [h.mem_nhds (show x ∈ _ by simp)] with g hg`. Establish `hg' : π (x⁻¹ * g) v = v` using `hg`. Use `conv_rhs => rw [← hg']`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]`.
-/
theorem isLocallyConstant_orbit (hπ : IsSmooth π) (v : V) : IsLocallyConstant fun g : G => π g v := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have h : IsOpen ((fun g : G => x⁻¹ * g) ⁻¹' {g : G | π g v = v}) := (hπ v).preimage (by fun_prop)
  filter_upwards [h.mem_nhds (show x ∈ _ by simp)] with g hg
  have hg' : π (x⁻¹ * g) v = v := hg
  conv_rhs => rw [← hg']
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.TwistedKernelFixed.eq_zero_of_fixed hπ hH hv hv'`.
-/
theorem eq_zero_of_fixed (hπ : IsSmooth π) {H : Subgroup G} (hH : IsCompact (H : Set G)) {v : V}
    (hv : v ∈ fixed π H) (hv' : v ∈ twKer π H 1) : v = 0 :=
  _root_.UpperTheory.Reformulated.B.TwistedKernelFixed.eq_zero_of_fixed hπ hH hv hv'

/- English proof (translation)
Use `haveI : CompactSpace H := isCompact_iff_compactSpace.1 hH`. Establish `hf` using `((isLocallyConstant_orbit hπ v).comp_continuous (f := fun h : H => (h : G)) continuous_subtype_val).range_finite`. Establish `hS : ∀ u, u ∈ hf.toFinset ↔ ∃ h ∈ H, π h v = u` using `fun u => by simp`. Use `⟨hf.toFinset, hS, mem_fixed.2 fun g hg => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum]`.

Establish `key : ∀ g ∈ H, ∀ u ∈ hf.toFinset, π g u ∈ hf.toFinset` using `fun g hg u hu => by`. Take `⟨h, hh, rfl⟩` from `(hS u).1 hu`. Conclude with `(hS _).2 ⟨g * h, mul_mem hg hh, by simp⟩`. Use `Finset.sum_nbij' (fun u => π g u) (fun u => π g⁻¹ u) (key g hg) (key _ (inv_mem hg)) (fun u _ => ?_) (fun u _ => ?_) fun _ _ => rfl` and prove the remaining obligations. Rewrite using `[← Module.End.mul_apply, ← map_mul]`.

Simplify using the standard rewrite rules. Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Simplify using the standard rewrite rules.
-/
theorem exists_orbit (hπ : IsSmooth π) {H : Subgroup G} (hH : IsCompact (H : Set G)) (v : V) :
    ∃ S : Finset V, (∀ u, u ∈ S ↔ ∃ h ∈ H, π h v = u) ∧ ∑ u ∈ S, u ∈ fixed π H := by
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hH
  have hf := ((isLocallyConstant_orbit hπ v).comp_continuous (f := fun h : H => (h : G))
    continuous_subtype_val).range_finite
  have hS : ∀ u, u ∈ hf.toFinset ↔ ∃ h ∈ H, π h v = u := fun u => by simp
  refine ⟨hf.toFinset, hS, mem_fixed.2 fun g hg => ?_⟩
  rw [map_sum]
  have key : ∀ g ∈ H, ∀ u ∈ hf.toFinset, π g u ∈ hf.toFinset := fun g hg u hu => by
    obtain ⟨h, hh, rfl⟩ := (hS u).1 hu
    exact (hS _).2 ⟨g * h, mul_mem hg hh, by simp⟩
  refine Finset.sum_nbij' (fun u => π g u) (fun u => π g⁻¹ u) (key g hg) (key _ (inv_mem hg))
    (fun u _ => ?_) (fun u _ => ?_) fun _ _ => rfl
  · rw [← Module.End.mul_apply, ← map_mul]; simp
  · rw [← Module.End.mul_apply, ← map_mul]; simp

variable (π) in

def Inj (I J : Subgroup G) : Prop := ∀ v ∈ fixed π I, v ∈ twKer π J 1 → v = 0

/- English proof (translation)
Introduce `v hv hv'`. Take `⟨S, hS, hz⟩` from `exists_orbit hπ hJ v`. Establish `hz0 : ∑ u ∈ S, u = 0` using `h2 _ hz (Submodule.sum_mem _ fun u hu => by`. Take `⟨x, hx, rfl⟩` from `(hS u).1 hu`. Take `⟨a, ha, b, hb, rfl⟩` from `hfac x hx`.

Rewrite using `[map_mul, Module.End.mul_apply, mem_fixed.1 hv b hb]`. Conclude with `apply_mem_twKer ha hv')`. Establish `h3 : ∑ u ∈ S, (u - v) ∈ twKer π J 1` using `Submodule.sum_mem _ fun u hu => by`. Take `⟨x, hx, rfl⟩` from `(hS u).1 hu`. Conclude with `sub_mem_twKer hx v`.

Rewrite `h3` using `[Finset.sum_sub_distrib, hz0, zero_sub, neg_mem_iff, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]`. Establish `hne : (S.card : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨v, (hS v).2 ⟨1, one_mem _, by simp⟩⟩)`. Conclude with `h1 v hv ((Submodule.smul_mem_iff _ hne).1 h3)`.
-/
theorem Inj.trans (hπ : IsSmooth π) {I J K : Subgroup G} (hJ : IsCompact (J : Set G))
    (hfac : ∀ x ∈ J, ∃ a ∈ K, ∃ b ∈ I, x = a * b) (h1 : Inj π I J) (h2 : Inj π J K) : Inj π I K := by
  intro v hv hv'
  obtain ⟨S, hS, hz⟩ := exists_orbit hπ hJ v
  have hz0 : ∑ u ∈ S, u = 0 := h2 _ hz (Submodule.sum_mem _ fun u hu => by
    obtain ⟨x, hx, rfl⟩ := (hS u).1 hu
    obtain ⟨a, ha, b, hb, rfl⟩ := hfac x hx
    rw [map_mul, Module.End.mul_apply, mem_fixed.1 hv b hb]
    exact apply_mem_twKer ha hv')
  have h3 : ∑ u ∈ S, (u - v) ∈ twKer π J 1 := Submodule.sum_mem _ fun u hu => by
    obtain ⟨x, hx, rfl⟩ := (hS u).1 hu
    exact sub_mem_twKer hx v
  rw [Finset.sum_sub_distrib, hz0, zero_sub, neg_mem_iff, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ] at h3
  have hne : (S.card : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨v, (hS v).2 ⟨1, one_mem _, by simp⟩⟩)
  exact h1 v hv ((Submodule.smul_mem_iff _ hne).1 h3)

/- English proof (translation)
Introduce `v hv hv'`. Take `⟨S, hS, hz⟩` from `exists_orbit hπ hP v`. Establish `hz0 : ∑ u ∈ S, u = 0` using `eq_zero_of_fixed hπ hP hz (Submodule.sum_mem _ fun u hu => by`. Take `⟨x, hx, rfl⟩` from `(hS u).1 hu`. Conclude with `apply_mem_twKer hx (twKer_mono hJP hv'))`.

Establish `hw : π s v ∈ S` using `(hS _).2 ⟨s, hs, rfl⟩`. Establish `h3 : ∑ u ∈ S.erase (π s v), u ∈ twKer π J 1` using `Submodule.sum_mem _ fun u hu => by`. Take `⟨hne, hu⟩` from `Finset.mem_erase.1 hu`. Take `⟨x, hx, rfl⟩` from `(hS u).1 hu`. Break down `hdec x hx with ⟨a, ha, b, hb, rfl⟩ | h` into its components or cases.

Rewrite using `[map_mul, Module.End.mul_apply, mem_fixed.1 hv b hb]`. Conclude with `apply_mem_twKer ha hv'`. Use `absurd ?_ hne conv_rhs => rw [← mem_fixed.1 hv _ h]` and prove the remaining obligations. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]`. Rewrite `hz0` using `[← Finset.add_sum_erase _ _ hw, add_eq_zero_iff_eq_neg]`.

Establish `h4 : π s v = 0` using `eq_zero_of_fixed hπ hJ (mem_fixed.2 fun x hx => by conv_rhs => rw [← mem_fixed.1 hv _ (hconj x hx)]`. Simplify using `only [← Module.End.mul_apply, ← map_mul]`. Use `congr 2`. Use the proof step `group) (by rw [hz0]; exact neg_mem h3)`. Use `congrArg (π s⁻¹) h4` as an intermediate fact.

Rewrite `this` using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero, Module.End.one_apply]`. Then use the resulting hypothesis.
-/
theorem inj_of_rank_one (hπ : IsSmooth π) {I J P : Subgroup G} (hJ : IsCompact (J : Set G))
    (hP : IsCompact (P : Set G)) (hJP : J ≤ P) {s : G} (hs : s ∈ P) (hconj : ∀ x ∈ J, s⁻¹ * x * s ∈ I)
    (hdec : ∀ p ∈ P, (∃ a ∈ J, ∃ b ∈ I, p = a * b) ∨ s⁻¹ * p ∈ I) : Inj π I J := by
  classical
  intro v hv hv'
  obtain ⟨S, hS, hz⟩ := exists_orbit hπ hP v
  have hz0 : ∑ u ∈ S, u = 0 := eq_zero_of_fixed hπ hP hz (Submodule.sum_mem _ fun u hu => by
    obtain ⟨x, hx, rfl⟩ := (hS u).1 hu
    exact apply_mem_twKer hx (twKer_mono hJP hv'))
  have hw : π s v ∈ S := (hS _).2 ⟨s, hs, rfl⟩
  have h3 : ∑ u ∈ S.erase (π s v), u ∈ twKer π J 1 := Submodule.sum_mem _ fun u hu => by
    obtain ⟨hne, hu⟩ := Finset.mem_erase.1 hu
    obtain ⟨x, hx, rfl⟩ := (hS u).1 hu
    rcases hdec x hx with ⟨a, ha, b, hb, rfl⟩ | h
    · rw [map_mul, Module.End.mul_apply, mem_fixed.1 hv b hb]
      exact apply_mem_twKer ha hv'
    · refine absurd ?_ hne
      conv_rhs => rw [← mem_fixed.1 hv _ h]
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  rw [← Finset.add_sum_erase _ _ hw, add_eq_zero_iff_eq_neg] at hz0
  have h4 : π s v = 0 := eq_zero_of_fixed hπ hJ (mem_fixed.2 fun x hx => by
    conv_rhs => rw [← mem_fixed.1 hv _ (hconj x hx)]
    simp only [← Module.End.mul_apply, ← map_mul]
    congr 2
    group) (by rw [hz0]; exact neg_mem h3)
  have := congrArg (π s⁻¹) h4
  rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero, Module.End.one_apply] at this

end Abstract

section Depth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Deep (a : ℤ) (x : k) : Prop := valuation k x ≤ uniformizer k ^ a

/- English proof (translation)
The claim follows from `uniformizer_pos`.
-/
theorem unif_pos : 0 < uniformizer k := uniformizer_pos

/- English proof (translation)
Simplify using `[Deep]`.
-/
theorem deep_zero (a : ℤ) : Deep a (0 : k) := by simp [Deep]

/- English proof (translation)
Simplify using `[Deep]`.
-/
theorem deep_zero_iff {x : k} : Deep 0 x ↔ valuation k x ≤ 1 := by simp [Deep]

/- English proof (translation)
Simplify using `[Deep, le_uniformizer_iff]`.
-/
theorem deep_one_iff {x : k} : Deep 1 x ↔ valuation k x < 1 := by simp [Deep, le_uniformizer_iff]

/- English proof (translation)
The claim follows from `le_trans h (zpow_le_zpow_right_of_le_one₀ unif_pos uniformizer_lt_one.le hab)`.
-/
theorem Deep.mono {a b : ℤ} {x : k} (h : Deep a x) (hab : b ≤ a) : Deep b x :=
  le_trans h (zpow_le_zpow_right_of_le_one₀ unif_pos uniformizer_lt_one.le hab)

/- English proof (translation)
Unfold `Deep at *`. Rewrite using `[map_mul, zpow_add₀ unif_pos.ne']`. Conclude with `mul_le_mul' hx hy`.
-/
theorem Deep.mul {a b : ℤ} {x y : k} (hx : Deep a x) (hy : Deep b y) : Deep (a + b) (x * y) := by
  unfold Deep at *
  rw [map_mul, zpow_add₀ unif_pos.ne']
  exact mul_le_mul' hx hy

/- English proof (translation)
Simplify `hx` using `[Deep]`.
-/
theorem Deep.neg {a : ℤ} {x : k} (hx : Deep a x) : Deep a (-x) := by simpa [Deep] using hx

/- English proof (translation)
The claim follows from `Valuation.map_sum_le _ h`.
-/
theorem Deep.sum {ι : Type} {s : Finset ι} {a : ℤ} {x : ι → k} (h : ∀ i ∈ s, Deep a (x i)) :
    Deep a (∑ i ∈ s, x i) := Valuation.map_sum_le _ h

/- English proof (translation)
Rewrite `h1` using `[deep_one_iff, not_lt]`. Use `⟨fun h => by simp [h] at h1, ?_⟩` and prove the remaining obligations. Rewrite using `[deep_zero_iff, map_inv₀]`. Conclude with `inv_le_one_of_one_le₀ h1`.
-/
theorem deep_inv {u : k} (h1 : ¬ Deep 1 u) : u ≠ 0 ∧ Deep 0 u⁻¹ := by
  rw [deep_one_iff, not_lt] at h1
  refine ⟨fun h => by simp [h] at h1, ?_⟩
  rw [deep_zero_iff, map_inv₀]
  exact inv_le_one_of_one_le₀ h1

/- English proof (translation)
Take `⟨c, hc⟩` from `valuation_surjective (uniformizer k ^ a)`. Use `⟨c, fun h => ?_, hc.le, ?_⟩` and prove the remaining obligations. Rewrite `hc` using `[h, map_zero]`. Conclude with `(zpow_pos unif_pos a).ne hc`. Simplify using `[Deep, hc]`.
-/
theorem exists_deep (a : ℤ) : ∃ c : k, c ≠ 0 ∧ Deep a c ∧ Deep (-a) c⁻¹ := by
  obtain ⟨c, hc⟩ := valuation_surjective (uniformizer k ^ a)
  refine ⟨c, fun h => ?_, hc.le, ?_⟩
  · rw [h, map_zero] at hc
    exact (zpow_pos unif_pos a).ne hc
  · simp [Deep, hc]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m : ℕ, valuation k x ≤ (uniformizer k)⁻¹ ^ m := by`. Conclude with `MulArchimedean.arch _ ((one_lt_inv₀ unif_pos).2 uniformizer_lt_one)`. Use `filter_upwards [Filter.eventually_ge_atTop m] with m' hm'`. Establish `: Deep (-(m : ℤ)) x` using `by simpa [Deep] using hm`. Conclude with `this.mono (by omega)`.
-/
theorem eventually_deep (x : k) : ∀ᶠ m : ℕ in Filter.atTop, Deep (-(m : ℤ)) x := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, valuation k x ≤ (uniformizer k)⁻¹ ^ m := by
    exact MulArchimedean.arch _ ((one_lt_inv₀ unif_pos).2 uniformizer_lt_one)
  filter_upwards [Filter.eventually_ge_atTop m] with m' hm'
  have : Deep (-(m : ℤ)) x := by simpa [Deep] using hm
  exact this.mono (by omega)

end Depth

section Chambers

variable {n : Type}

def Conc (f : n → n → ℤ) : Prop := (∀ i, f i i = 0) ∧ ∀ i j l, f i j ≤ f i l + f l j

def Chamber (f : n → n → ℤ) : Prop := Conc f ∧ ∀ i j, i ≠ j → f i j + f j i = 1

/- English proof (translation)
Set `ht : n × n → ℤ` to `fun p => ∑ l, (f p.1 p.2 + f p.2 l - f p.1 l)`. Establish `hpos : ∀ a b, a ≠ b → 0 < ht (a, b)` using `fun a b hab => Finset.sum_pos' (fun l _ => by have := hf.1.2 a l b; simp only; omega) ⟨a, Finset.mem_univ _, by have := hf.2 a b hab; have := hf.1.1 a; simp only; omega⟩`. Establish `hdiag : ∀ a b, f a b < F a b → a ≠ b`. Introduce and unpack `a _ h rfl`. Rewrite `h` using `[hf.1.1, hF.1.1]`.

Conclude with `lt_irrefl _ h`. Establish `hex : (Finset.univ.filter fun p : n × n => f p.1 p.2 < F p.1 p.2).Nonempty`. Assume the negation of the conclusion as `hc`. Apply `hne` to reduce the goal to its premises. Establish `hle : ∀ a b, F a b ≤ f a b` using `fun a b => by`.

Assume the negation of the conclusion as `h`. Conclude with `hc ⟨(a, b), by simpa using h⟩`. Use function extensionality and compare the values at `a b`. Distinguish the cases in `hab : a = b`. Rewrite using `[hab, hf.1.1, hF.1.1]`.

Use `hle a b` as an intermediate fact. Use `hle b a` as an intermediate fact. Use `hf.2 a b hab` as an intermediate fact. Use `hF.2 a b hab` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Take `⟨⟨j, i⟩, hp, hmin⟩` from `Finset.exists_min_image _ ht hex`. Establish `hp' : f j i < F j i` using `by simpa using hp`. Use `⟨i, j, (hdiag _ _ hp').symm, hp', fun l hli hlj => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Establish `he : f j i = f j l + f l i` using `le_antisymm (hf.1.2 _ _ _) (not_lt.1 hc)`.

Establish `hadd : ht (j, i) = ht (j, l) + ht (l, i)`. Simplify using `only [ht, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun x _ => by omega`. Establish `h1` using `hpos j l hlj.symm`. Establish `h2` using `hpos l i hli`.

Establish `h3` using `hF.1.2 j i l`. Distinguish the cases in `h : f j l < F j l`. Use `hmin (j, l) (by simpa using h); omega` as an intermediate fact. Use `hmin (l, i) (by simp; omega); omega` as an intermediate fact.
-/
theorem exists_wall [Fintype n] {f F : n → n → ℤ} (hf : Chamber f) (hF : Chamber F) (hne : f ≠ F) :
    ∃ i j, i ≠ j ∧ f j i < F j i ∧ ∀ l, l ≠ i → l ≠ j → f j i < f j l + f l i := by
  classical
  let ht : n × n → ℤ := fun p => ∑ l, (f p.1 p.2 + f p.2 l - f p.1 l)
  have hpos : ∀ a b, a ≠ b → 0 < ht (a, b) := fun a b hab =>
    Finset.sum_pos' (fun l _ => by have := hf.1.2 a l b; simp only; omega)
      ⟨a, Finset.mem_univ _, by have := hf.2 a b hab; have := hf.1.1 a; simp only; omega⟩
  have hdiag : ∀ a b, f a b < F a b → a ≠ b := by
    rintro a _ h rfl
    rw [hf.1.1, hF.1.1] at h
    exact lt_irrefl _ h
  have hex : (Finset.univ.filter fun p : n × n => f p.1 p.2 < F p.1 p.2).Nonempty := by
    by_contra hc
    apply hne
    have hle : ∀ a b, F a b ≤ f a b := fun a b => by
      by_contra h
      exact hc ⟨(a, b), by simpa using h⟩
    funext a b
    by_cases hab : a = b
    · rw [hab, hf.1.1, hF.1.1]
    · have := hle a b; have := hle b a; have := hf.2 a b hab; have := hF.2 a b hab; omega
  obtain ⟨⟨j, i⟩, hp, hmin⟩ := Finset.exists_min_image _ ht hex
  have hp' : f j i < F j i := by simpa using hp
  refine ⟨i, j, (hdiag _ _ hp').symm, hp', fun l hli hlj => ?_⟩
  by_contra hc
  have he : f j i = f j l + f l i := le_antisymm (hf.1.2 _ _ _) (not_lt.1 hc)
  have hadd : ht (j, i) = ht (j, l) + ht (l, i) := by
    simp only [ht, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by omega
  have h1 := hpos j l hlj.symm
  have h2 := hpos l i hli
  have h3 := hF.1.2 j i l
  by_cases h : f j l < F j l
  · have := hmin (j, l) (by simpa using h); omega
  · have := hmin (l, i) (by simp; omega); omega

/- English proof (translation)
Set `g : n → n → ℤ` to `fun a b => if a = i ∧ b = j then f a b - 1 else f a b`. Set `f' : n → n → ℤ` to `fun a b => if a = j ∧ b = i then g a b + 1 else g a b`. Establish `g1 : f i j = g i j + 1` using `by simp [g]`. Establish `g2 : ∀ a b, ¬ (a = i ∧ b = j) → f a b = g a b` using `fun a b h => by simp only [g, if_neg h]`. Establish `f1 : f' j i = g j i + 1` using `by simp [f']`.

Establish `f2 : ∀ a b, ¬ (a = j ∧ b = i) → f' a b = g a b` using `fun a b h => by simp only [f', if_neg h]`. Apply the tactic sequence `have gle : ∀ a b, g a b ≤ f a b := fun a b => by simp only [g]; split_ifs <;> omega`. Apply the tactic sequence `have fle : ∀ a b, g a b ≤ f' a b := fun a b => by simp only [f']; split_ifs <;> omega`. Use `clear_value f' g`. Take `⟨⟨h0, h1⟩, h2⟩` from `hf`.

Establish `h3` using `h2 i j hij`. Establish `hg0 : ∀ a, g a a = 0` using `fun a => by rw [← g2 a a (by grind), h0]`. Establish `hg : Conc g`. Use `⟨hg0, fun a b l => ?_⟩` and prove the remaining obligations. Distinguish the cases in `c1 : a = i ∧ l = j`.

Take `⟨rfl, rfl⟩` from `c1`. Use `g2 l b (by grind)` as an intermediate fact. Distinguish the cases in `c : b = l`. Substitute `c` using the available equality. Use `hg0 b` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Distinguish the cases in `c' : b = a`. Substitute `c'` using the available equality. Use `hg0 b` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `hw b c' c` as an intermediate fact. Use `h2 b a c'` as an intermediate fact. Use `gle a b` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `c2 : l = i ∧ b = j`.

Take `⟨rfl, rfl⟩` from `c2`. Use `g2 a l (by grind)` as an intermediate fact. Distinguish the cases in `c : a = l`. Substitute `c` using the available equality. Use `hg0 a` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Distinguish the cases in `c' : a = b`. Substitute `c'` using the available equality. Use `hg0 a` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `hw a c c'` as an intermediate fact. Use `h2 a b c'` as an intermediate fact. Use `gle a b` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `g2 a l c1` as an intermediate fact.

Use `g2 l b c2` as an intermediate fact. Use `gle a b` as an intermediate fact. Use `h1 a b l` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hf0 : ∀ a, f' a a = 0` using `fun a => by rw [f2 a a (by grind), hg0]`.

Use `⟨g, f', hg, ⟨⟨hf0, fun a b l => ?_⟩, fun a b hab => ?_⟩, g1, g2, f1, f2⟩` and prove the remaining obligations. Distinguish the cases in `c1 : a = j ∧ b = i`. Take `⟨rfl, rfl⟩` from `c1`. Distinguish the cases in `c : l = b`. Substitute `c` using the available equality.

Use `hf0 l` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `c' : l = a`. Substitute `c'` using the available equality. Use `hf0 l` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Use `hw l c c'` as an intermediate fact. Use `fle a l` as an intermediate fact. Use `fle l b` as an intermediate fact. Use `g2 a b (by grind); have := g2 a l (by grind); have := g2 l b (by grind); omega` as an intermediate fact.

Use `f2 a b c1` as an intermediate fact. Use `hg.2 a b l` as an intermediate fact. Use `fle a l` as an intermediate fact. Use `fle l b` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `g2 j i (by grind)` as an intermediate fact. Use `f2 i j (by grind)` as an intermediate fact. Distinguish the cases in `c1 : a = j ∧ b = i`. Take `⟨rfl, rfl⟩` from `c1`. Use linear arithmetic over natural numbers and integers.

Distinguish the cases in `c2 : a = i ∧ b = j`. Take `⟨rfl, rfl⟩` from `c2`. Use linear arithmetic over natural numbers and integers. Use `f2 a b c1; have := f2 b a (by grind); have := g2 a b c2; have := g2 b a (by grind)` as an intermediate fact. Use `h2 a b hab` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem exists_flip {f : n → n → ℤ} (hf : Chamber f) {i j : n} (hij : i ≠ j)
    (hw : ∀ l, l ≠ i → l ≠ j → f j i < f j l + f l i) :
    ∃ g f' : n → n → ℤ, Conc g ∧ Chamber f' ∧ f i j = g i j + 1 ∧
      (∀ a b, ¬ (a = i ∧ b = j) → f a b = g a b) ∧ f' j i = g j i + 1 ∧
      (∀ a b, ¬ (a = j ∧ b = i) → f' a b = g a b) := by
  classical
  let g : n → n → ℤ := fun a b => if a = i ∧ b = j then f a b - 1 else f a b
  let f' : n → n → ℤ := fun a b => if a = j ∧ b = i then g a b + 1 else g a b
  have g1 : f i j = g i j + 1 := by simp [g]
  have g2 : ∀ a b, ¬ (a = i ∧ b = j) → f a b = g a b := fun a b h => by simp only [g, if_neg h]
  have f1 : f' j i = g j i + 1 := by simp [f']
  have f2 : ∀ a b, ¬ (a = j ∧ b = i) → f' a b = g a b := fun a b h => by simp only [f', if_neg h]
  have gle : ∀ a b, g a b ≤ f a b := fun a b => by simp only [g]; split_ifs <;> omega
  have fle : ∀ a b, g a b ≤ f' a b := fun a b => by simp only [f']; split_ifs <;> omega
  clear_value f' g
  obtain ⟨⟨h0, h1⟩, h2⟩ := hf
  have h3 := h2 i j hij
  have hg0 : ∀ a, g a a = 0 := fun a => by rw [← g2 a a (by grind), h0]
  have hg : Conc g := by
    refine ⟨hg0, fun a b l => ?_⟩
    by_cases c1 : a = i ∧ l = j
    · obtain ⟨rfl, rfl⟩ := c1
      have := g2 l b (by grind)
      by_cases c : b = l
      · subst c; have := hg0 b; omega
      by_cases c' : b = a
      · subst c'; have := hg0 b; omega
      have := hw b c' c; have := h2 b a c'; have := gle a b; omega
    by_cases c2 : l = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := c2
      have := g2 a l (by grind)
      by_cases c : a = l
      · subst c; have := hg0 a; omega
      by_cases c' : a = b
      · subst c'; have := hg0 a; omega
      have := hw a c c'; have := h2 a b c'; have := gle a b; omega
    have := g2 a l c1; have := g2 l b c2; have := gle a b; have := h1 a b l; omega
  have hf0 : ∀ a, f' a a = 0 := fun a => by rw [f2 a a (by grind), hg0]
  refine ⟨g, f', hg, ⟨⟨hf0, fun a b l => ?_⟩, fun a b hab => ?_⟩, g1, g2, f1, f2⟩
  · by_cases c1 : a = j ∧ b = i
    · obtain ⟨rfl, rfl⟩ := c1
      by_cases c : l = b
      · subst c; have := hf0 l; omega
      by_cases c' : l = a
      · subst c'; have := hf0 l; omega
      have := hw l c c'; have := fle a l; have := fle l b
      have := g2 a b (by grind); have := g2 a l (by grind); have := g2 l b (by grind); omega
    have := f2 a b c1; have := hg.2 a b l; have := fle a l; have := fle l b; omega
  · have := g2 j i (by grind)
    have := f2 i j (by grind)
    by_cases c1 : a = j ∧ b = i
    · obtain ⟨rfl, rfl⟩ := c1; omega
    by_cases c2 : a = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := c2; omega
    have := f2 a b c1; have := f2 b a (by grind); have := g2 a b c2; have := g2 b a (by grind)
    have := h2 a b hab; omega

end Chambers

section Groups

open Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

variable (k) in

def grp {f : n → n → ℤ} (hf : Conc f) : Subgroup (GL n k) where
  carrier := {g | (∀ i j, Deep (f i j) (g.val i j)) ∧ ∀ i j, Deep (f i j) ((g⁻¹).val i j)}
  one_mem' := by
    have : ∀ i j, Deep (f i j) ((1 : Matrix n n k) i j) := fun i j => by
      by_cases h : i = j
      · subst h; simp [hf.1, deep_zero_iff]
      · simp [one_apply_ne h, deep_zero]
    exact ⟨this, this⟩
  mul_mem' := by
    have : ∀ A B : Matrix n n k, (∀ i j, Deep (f i j) (A i j)) → (∀ i j, Deep (f i j) (B i j)) →
        ∀ i j, Deep (f i j) ((A * B) i j) := fun A B hA hB i j => by
      rw [mul_apply]
      exact Deep.sum fun l _ => ((hA i l).mul (hB l j)).mono (hf.2 i j l)
    intro a b ha hb
    refine ⟨this _ _ ha.1 hb.1, ?_⟩
    rw [_root_.mul_inv_rev]
    exact this _ _ hb.2 ha.2
  inv_mem' := fun h => ⟨h.2, by simpa using h.1⟩

/- English proof (translation)
Introduce `_ hx` and use `⟨fun i j => (hx.1 i j).mono (h i j), fun i j => (hx.2 i j).mono (h i j)⟩`.
-/
theorem grp_mono {f g : n → n → ℤ} (hf : Conc f) (hg : Conc g) (h : ∀ a b, g a b ≤ f a b) :
    grp k hf ≤ grp k hg := fun _ hx =>
  ⟨fun i j => (hx.1 i j).mono (h i j), fun i j => (hx.2 i j).mono (h i j)⟩

/- English proof (translation)
Take `⟨_, _⟩` from `GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)`. Establish `hK : IsCompact {A : Matrix n n k | ∀ i j, Deep (f i j) (A i j)}`. Establish `h : IsCompact (Set.pi Set.univ fun i : n => Set.pi Set.univ fun j : n => {x : k | Deep (f i j) x})` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k _`. Establish `e : {A : Matrix n n k | ∀ i j, Deep (f i j) (A i j)} = (Set.pi Set.univ fun i : n => Set.pi Set.univ fun j : n => {x : k | Deep (f i j) x})` using `Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩`. Rewrite using `[e]`.

Conclude with `h`. Establish `h` using `(Units.isClosedEmbedding_embedProduct (α := Matrix n n k)).isCompact_preimage (hK.prod (hK.image MulOpposite.continuous_op))`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `g`. Simplify using `only [SetLike.mem_coe, Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod, (MulOpposite.op_injective).mem_set_image]`.

Both sides reduce to the same expression.
-/
theorem isCompact_grp {f : n → n → ℤ} (hf : Conc f) : IsCompact (grp k hf : Set (GL n k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hK : IsCompact {A : Matrix n n k | ∀ i j, Deep (f i j) (A i j)} := by
    have h : IsCompact (Set.pi Set.univ fun i : n => Set.pi Set.univ fun j : n => {x : k | Deep (f i j) x}) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k _
    have e : {A : Matrix n n k | ∀ i j, Deep (f i j) (A i j)} =
        (Set.pi Set.univ fun i : n => Set.pi Set.univ fun j : n => {x : k | Deep (f i j) x}) :=
      Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩
    rw [e]; exact h
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix n n k)).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  simp only [SetLike.mem_coe, Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply,
    Set.mem_prod, (MulOpposite.op_injective).mem_set_image]
  rfl

def elem {i j : n} (h : i ≠ j) (y : k) : GL n k :=
  ⟨transvection i j y, transvection i j (-y), by rw [transvection_mul_transvection_same _ _ h]; simp,
    by rw [transvection_mul_transvection_same _ _ h]; simp⟩

/- English proof (translation)
Establish `: ∀ y : k, Deep (f i j) y → ∀ a b, Deep (f a b) (transvection i j y a b)` using `fun y hy a b => by`. Establish `h1` using `(grp k hf).one_mem.1 a b`. Distinguish the cases in `c : i = a ∧ j = b`. Take `⟨rfl, rfl⟩` from `c`. Simplify `hy` using `[transvection, one_apply_ne h]`.

Simplify `h1` using `[transvection, single_apply, c]`. Conclude with `⟨this y hy, this _ hy.neg⟩`.
-/
theorem elem_mem {f : n → n → ℤ} (hf : Conc f) {i j : n} (h : i ≠ j) {y : k} (hy : Deep (f i j) y) :
    elem h y ∈ grp k hf := by
  have : ∀ y : k, Deep (f i j) y → ∀ a b, Deep (f a b) (transvection i j y a b) := fun y hy a b => by
    have h1 := (grp k hf).one_mem.1 a b
    by_cases c : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := c
      simpa [transvection, one_apply_ne h] using hy
    · simpa [transvection, single_apply, c] using h1
  exact ⟨this y hy, this _ hy.neg⟩

/- English proof (translation)
Introduce `h`. Establish `h3 : Deep 1 ((p.val * (p⁻¹).val) i i)`. Rewrite using `[mul_apply]`. Use `Deep.sum fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `c : l = i`.

Substitute `c` using the available equality. Conclude with `(h.mul (h2 l)).mono (by rw [hf.1.1]; omega)`. Conclude with `((h1 l).mul (h2 l)).mono (hf.2 i l (Ne.symm c)).ge`. Simplify using `[deep_one_iff] at h3`.
-/
theorem diag_unit {f : n → n → ℤ} (hf : Chamber f) {p : GL n k} {i : n}
    (h1 : ∀ l, Deep (f i l) (p.val i l)) (h2 : ∀ l, Deep (f l i) ((p⁻¹).val l i)) :
    ¬ Deep 1 (p.val i i) := by
  intro h
  have h3 : Deep 1 ((p.val * (p⁻¹).val) i i) := by
    rw [mul_apply]
    refine Deep.sum fun l _ => ?_
    by_cases c : l = i
    · subst c
      exact (h.mul (h2 l)).mono (by rw [hf.1.1]; omega)
    · exact ((h1 l).mul (h2 l)).mono (hf.2 i l (Ne.symm c)).ge
  simp [deep_one_iff] at h3

variable {g f f' : n → n → ℤ} {i j : n}

/- English proof (translation)
Establish `h1 : ∀ a b, Deep (f a b) (p.val a b)` using `fun a b => by`. Distinguish the cases in `c : a = i ∧ b = j`. Rewrite using `[c.1, c.2]`. Conclude with `h`. Rewrite using `[hfg a b c]`.

Conclude with `hp.1 a b`. Establish `h2 : ∀ a b, ¬ (a = i ∧ b = j) → Deep (f a b) ((p⁻¹).val a b)` using `fun a b c => by`. Rewrite using `[hfg a b c]`. Conclude with `hp.2 a b`. Use `⟨h1, fun a b => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `c : a = i ∧ b = j`. Use `swap`. Conclude with `h2 a b c`. Rewrite using `[c.1, c.2]`. Take `⟨hu0, hu⟩` from `deep_inv (diag_unit hf (h1 i) fun l => h2 l i (by grind))`.

Establish `h3 : (p.val * (p⁻¹).val) i j = 0` using `by simp [one_apply_ne hij]`. Rewrite `h3` using `[mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_eq_zero_iff_eq_neg]`. Establish `h4 : Deep (f i j) (p.val i i * (p⁻¹).val i j)`. Rewrite using `[h3]`. Conclude with `(Deep.sum fun l hl => ((h1 i l).mul (h2 l j (by grind))).mono (hf.1.2 i j l)).neg`.

Simplify `hu.mul h4` using `only [zero_add, inv_mul_cancel_left₀ hu0]`.
-/
theorem mem_of_entry (hg : Conc g) (hf : Chamber f) (hij : i ≠ j)
    (hfg : ∀ a b, ¬ (a = i ∧ b = j) → f a b = g a b) {p : GL n k} (hp : p ∈ grp k hg)
    (h : Deep (f i j) (p.val i j)) : p ∈ grp k hf.1 := by
  have h1 : ∀ a b, Deep (f a b) (p.val a b) := fun a b => by
    by_cases c : a = i ∧ b = j
    · rw [c.1, c.2]; exact h
    · rw [hfg a b c]; exact hp.1 a b
  have h2 : ∀ a b, ¬ (a = i ∧ b = j) → Deep (f a b) ((p⁻¹).val a b) := fun a b c => by
    rw [hfg a b c]; exact hp.2 a b
  refine ⟨h1, fun a b => ?_⟩
  by_cases c : a = i ∧ b = j
  swap
  · exact h2 a b c
  rw [c.1, c.2]
  obtain ⟨hu0, hu⟩ := deep_inv (diag_unit hf (h1 i) fun l => h2 l i (by grind))
  have h3 : (p.val * (p⁻¹).val) i j = 0 := by simp [one_apply_ne hij]
  rw [mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_eq_zero_iff_eq_neg] at h3
  have h4 : Deep (f i j) (p.val i i * (p⁻¹).val i j) := by
    rw [h3]
    exact (Deep.sum fun l hl => ((h1 i l).mul (h2 l j (by grind))).mono (hf.1.2 i j l)).neg
  simpa only [zero_add, inv_mul_cancel_left₀ hu0] using hu.mul h4

/- English proof (translation)
Take `⟨hu0, hu⟩` from `deep_inv h`. Establish `hy : Deep (g i j) (p.val i j * (p.val j j)⁻¹)` using `by simpa using (hp.1 i j).mul hu`. Apply the tactic sequence `refine ⟨_, hy, (elem hij _)⁻¹ * p, mem_of_entry hg hf hij hfg (mul_mem (inv_mem (elem_mem hg hij hy)) hp) ?_, (mul_inv_cancel_left _ _).symm⟩`. Establish `: ((elem hij (p.val i j * (p.val j j)⁻¹))⁻¹ * p).val i j = 0` using `by show (transvection i j (-(p.val i j * (p.val j j)⁻¹)) * p.val) i j = 0`. Rewrite using `[transvection_mul_apply_same]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `deep_zero _`.
-/
theorem exists_factor (hg : Conc g) (hf : Chamber f) (hij : i ≠ j)
    (hfg : ∀ a b, ¬ (a = i ∧ b = j) → f a b = g a b) {p : GL n k} (hp : p ∈ grp k hg)
    (h : ¬ Deep 1 (p.val j j)) : ∃ y : k, Deep (g i j) y ∧ ∃ b ∈ grp k hf.1, p = elem hij y * b := by
  obtain ⟨hu0, hu⟩ := deep_inv h
  have hy : Deep (g i j) (p.val i j * (p.val j j)⁻¹) := by simpa using (hp.1 i j).mul hu
  refine ⟨_, hy, (elem hij _)⁻¹ * p, mem_of_entry hg hf hij hfg
    (mul_mem (inv_mem (elem_mem hg hij hy)) hp) ?_, (mul_inv_cancel_left _ _).symm⟩
  have : ((elem hij (p.val i j * (p.val j j)⁻¹))⁻¹ * p).val i j = 0 := by
    show (transvection i j (-(p.val i j * (p.val j j)⁻¹)) * p.val) i j = 0
    rw [transvection_mul_apply_same]
    field_simp
    ring
  rw [this]
  exact deep_zero _

variable {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL n k) V}

/- English proof (translation)
Establish `hle : grp k hf'.1 ≤ grp k hg` using `grp_mono _ _ fun a b => by`. Distinguish the cases in `c : a = j ∧ b = i`. Rewrite using `[c.1, c.2]`. Use linear arithmetic over natural numbers and integers. Conclude with `(h4 a b c).ge`.

Establish `h5` using `h2 j i (by grind)`. Establish `h6` using `hf.2 i j hij`. Establish `h7` using `h4 i j (by grind)`. Take `⟨c, hc0, hc, hc'⟩` from `exists_deep (k := k) (g i j)`. Set `s : GL n k` to `elem hij.symm c⁻¹ * elem hij (-c)`.

Establish `hs : s ∈ grp k hg` using `mul_mem (elem_mem hg _ (hc'.mono (by omega))) (elem_mem hg _ hc.neg)`. Establish `hl : ∀ (p : GL n k) (b : n), (s⁻¹ * p).val i b = c * p.val j b` using `fun p b => by`. Rewrite using `[_root_.mul_inv_rev, mul_assoc]`. Use `show (transvection i j (-(-c)) * (transvection j i (-c⁻¹) * p.val)) i b = _`. Rewrite using `[transvection_mul_apply_same, transvection_mul_apply_same, transvection_mul_apply_of_ne _ _ _ _ hij]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hr : ∀ (p : GL n k) (a : n), (p * s).val a j = -c * p.val a i` using `fun p a => by`. Rewrite using `[← mul_assoc]`. Use `show (p.val * transvection j i c⁻¹ * transvection i j (-c)) a j = _`.

Rewrite using `[mul_transvection_apply_same, mul_transvection_apply_same, mul_transvection_apply_of_ne _ _ _ _ hij.symm]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `inj_of_rank_one hπ (isCompact_grp _) (isCompact_grp hg) hle hs (fun x hx => ?_) fun p hp => ?_` and prove the remaining obligations. Apply the tactic sequence `refine mem_of_entry hg hf hij h2 (mul_mem (mul_mem (inv_mem hs) (hle hx)) hs) ?_`.

Rewrite using `[mul_assoc, hl, hr]`. Conclude with `(hc.mul (hc.neg.mul (hx.1 j i))).mono (by omega)`. Distinguish the cases in `hu : Deep 1 (p.val j j)`. Apply the tactic sequence `refine Or.inr (mem_of_entry hg hf hij h2 (mul_mem (inv_mem hs) hp) ?_)`. Rewrite using `[hl]`.

Conclude with `(hc.mul hu).mono (by omega)`. Take `⟨y, hy, b, hb, e⟩` from `exists_factor hg hf hij h2 hp hu`. Conclude with `Or.inl ⟨_, elem_mem hf'.1 hij (by rwa [h7]), b, hb, e⟩`.
-/
theorem inj_adjacent (hπ : IsSmooth π) (hg : Conc g) (hf : Chamber f) (hf' : Chamber f') (hij : i ≠ j)
    (h1 : f i j = g i j + 1) (h2 : ∀ a b, ¬ (a = i ∧ b = j) → f a b = g a b)
    (h3 : f' j i = g j i + 1) (h4 : ∀ a b, ¬ (a = j ∧ b = i) → f' a b = g a b) :
    Inj π (grp k hf.1) (grp k hf'.1) := by
  have hle : grp k hf'.1 ≤ grp k hg := grp_mono _ _ fun a b => by
    by_cases c : a = j ∧ b = i
    · rw [c.1, c.2]; omega
    · exact (h4 a b c).ge
  have h5 := h2 j i (by grind)
  have h6 := hf.2 i j hij
  have h7 := h4 i j (by grind)
  obtain ⟨c, hc0, hc, hc'⟩ := exists_deep (k := k) (g i j)
  let s : GL n k := elem hij.symm c⁻¹ * elem hij (-c)
  have hs : s ∈ grp k hg :=
    mul_mem (elem_mem hg _ (hc'.mono (by omega))) (elem_mem hg _ hc.neg)
  have hl : ∀ (p : GL n k) (b : n), (s⁻¹ * p).val i b = c * p.val j b := fun p b => by
    rw [_root_.mul_inv_rev, mul_assoc]
    show (transvection i j (-(-c)) * (transvection j i (-c⁻¹) * p.val)) i b = _
    rw [transvection_mul_apply_same, transvection_mul_apply_same, transvection_mul_apply_of_ne _ _ _ _ hij]
    field_simp
    ring
  have hr : ∀ (p : GL n k) (a : n), (p * s).val a j = -c * p.val a i := fun p a => by
    rw [← mul_assoc]
    show (p.val * transvection j i c⁻¹ * transvection i j (-c)) a j = _
    rw [mul_transvection_apply_same, mul_transvection_apply_same,
      mul_transvection_apply_of_ne _ _ _ _ hij.symm]
    field_simp
    ring
  refine inj_of_rank_one hπ (isCompact_grp _) (isCompact_grp hg) hle hs (fun x hx => ?_) fun p hp => ?_
  · refine mem_of_entry hg hf hij h2 (mul_mem (mul_mem (inv_mem hs) (hle hx)) hs) ?_
    rw [mul_assoc, hl, hr]
    exact (hc.mul (hc.neg.mul (hx.1 j i))).mono (by omega)
  · by_cases hu : Deep 1 (p.val j j)
    · refine Or.inr (mem_of_entry hg hf hij h2 (mul_mem (inv_mem hs) hp) ?_)
      rw [hl]
      exact (hc.mul hu).mono (by omega)
    · obtain ⟨y, hy, b, hb, e⟩ := exists_factor hg hf hij h2 hp hu
      exact Or.inl ⟨_, elem_mem hf'.1 hij (by rwa [h7]), b, hb, e⟩

/- English proof (translation)
Generalize the expression as in `hd : ∑ p : n × n, (f p.1 p.2 - F p.1 p.2).toNat = d`. Proceed by induction on `d using Nat.strong_induction_on generalizing f with`. Consider the case `_ d ih`. Distinguish the cases in `hne : f = F`. Substitute `hne` using the available equality.

Conclude with `fun v hv hv' => eq_zero_of_fixed hπ (isCompact_grp _) hv hv'`. Take `⟨i, j, hij, hlt, hw⟩` from `exists_wall hf hF hne`. Take `⟨g, f', hg, hf', h1, h2, h3, h4⟩` from `exists_flip hf hij hw`. Establish `h5` using `h2 j i (by grind)`. Establish `h6` using `hf.2 i j hij`.

Establish `h7` using `h4 i j (by grind)`. Establish `h8` using `hF.2 i j hij`. Use `(inj_adjacent hπ hg hf hf' hij h1 h2 h3 h4).trans hπ (isCompact_grp _) (fun x hx => ?_) (ih _ ?_ hf' rfl)` and prove the remaining obligations. Establish `hle : grp k hf'.1 ≤ grp k hg` using `grp_mono _ _ fun a b => by`. Distinguish the cases in `c : a = j ∧ b = i`.

Rewrite using `[c.1, c.2]`. Use linear arithmetic over natural numbers and integers. Conclude with `(h4 a b c).ge`. Take `⟨y, hy, b, hb, e⟩` from `exists_factor hg hf hij h2 (hle hx) (diag_unit hf' (hx.1 j) fun l => hx.2 l j)`. Conclude with `⟨_, elem_mem hF.1 hij (hy.mono (by omega)), b, hb, e⟩`.

Rewrite using `[← hd]`. Use `Finset.sum_lt_sum (fun p _ => ?_) ⟨(i, j), Finset.mem_univ _, by simp only; omega⟩` and prove the remaining obligations. Take `⟨a, b⟩` from `p`. Simplify using `only`. Distinguish the cases in `c : a = j ∧ b = i`.

Rewrite using `[c.1, c.2]`. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `c' : a = i ∧ b = j`. Rewrite using `[c'.1, c'.2]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[h4 a b c, h2 a b c']`.
-/
theorem inj_chambers (hπ : IsSmooth π) {f F : n → n → ℤ} (hf : Chamber f) (hF : Chamber F) :
    Inj π (grp k hf.1) (grp k hF.1) := by
  generalize hd : ∑ p : n × n, (f p.1 p.2 - F p.1 p.2).toNat = d
  induction d using Nat.strong_induction_on generalizing f with
  | _ d ih =>
  by_cases hne : f = F
  · subst hne
    exact fun v hv hv' => eq_zero_of_fixed hπ (isCompact_grp _) hv hv'
  obtain ⟨i, j, hij, hlt, hw⟩ := exists_wall hf hF hne
  obtain ⟨g, f', hg, hf', h1, h2, h3, h4⟩ := exists_flip hf hij hw
  have h5 := h2 j i (by grind)
  have h6 := hf.2 i j hij
  have h7 := h4 i j (by grind)
  have h8 := hF.2 i j hij
  refine (inj_adjacent hπ hg hf hf' hij h1 h2 h3 h4).trans hπ (isCompact_grp _) (fun x hx => ?_)
    (ih _ ?_ hf' rfl)
  · have hle : grp k hf'.1 ≤ grp k hg := grp_mono _ _ fun a b => by
      by_cases c : a = j ∧ b = i
      · rw [c.1, c.2]; omega
      · exact (h4 a b c).ge
    obtain ⟨y, hy, b, hb, e⟩ := exists_factor hg hf hij h2 (hle hx)
      (diag_unit hf' (hx.1 j) fun l => hx.2 l j)
    exact ⟨_, elem_mem hF.1 hij (hy.mono (by omega)), b, hb, e⟩
  · rw [← hd]
    refine Finset.sum_lt_sum (fun p _ => ?_) ⟨(i, j), Finset.mem_univ _, by simp only; omega⟩
    obtain ⟨a, b⟩ := p
    simp only
    by_cases c : a = j ∧ b = i
    · rw [c.1, c.2]; omega
    by_cases c' : a = i ∧ b = j
    · rw [c'.1, c'.2]; omega
    rw [h4 a b c, h2 a b c']

variable [LinearOrder n]

def ray (m : ℕ) (i j : n) : ℤ :=
  (if j < i then 1 else 0) + m * (((Finset.univ.filter (· < i)).card : ℤ) - (Finset.univ.filter (· < j)).card)

/- English proof (translation)
Use `⟨⟨fun i => by simp [ray], fun i j l => ?_⟩, fun i j h => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `have : (if j < i then 1 else 0 : ℤ) ≤ (if l < i then 1 else 0) + if j < l then 1 else 0 := by split_ifs <;> first | omega | (exfalso; order)`. Simplify using `only [ray]`. Combine the linear equalities and inequalities to obtain the conclusion. Apply the tactic sequence `have : (if j < i then 1 else 0 : ℤ) + (if i < j then 1 else 0) = 1 := by split_ifs <;> first | omega | (exfalso; order)`.

Simplify using `only [ray]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem chamber_ray (m : ℕ) : Chamber (ray (n := n) m) := by
  refine ⟨⟨fun i => by simp [ray], fun i j l => ?_⟩, fun i j h => ?_⟩
  · have : (if j < i then 1 else 0 : ℤ) ≤ (if l < i then 1 else 0) + if j < l then 1 else 0 := by
      split_ifs <;> first | omega | (exfalso; order)
    simp only [ray]
    linarith
  · have : (if j < i then 1 else 0 : ℤ) + (if i < j then 1 else 0) = 1 := by
      split_ifs <;> first | omega | (exfalso; order)
    simp only [ray]
    linarith

/- English proof (translation)
Introduce `x hx` and use `by have h0 : ∀ i j : n, 0 ≤ ray 0 i j := fun i j => by simp only [ray]; split_ifs <;> simp refine mem_iwahori.2 ⟨(GlobalTheory.SplitFlip.mem_KO_iff x).2 ⟨fun i j => deep_zero_iff.1 ((hx.1 i j).mono (h0 i j)), fun i j => deep_zero_iff.1 ((hx.2 i j).mono (h0 i j))⟩, fun i j h => ?_ …`.
-/
theorem grp_ray_zero_le : grp k (chamber_ray (n := n) 0).1 ≤ iwahori k n := fun x hx => by
  have h0 : ∀ i j : n, 0 ≤ ray 0 i j := fun i j => by simp only [ray]; split_ifs <;> simp
  refine mem_iwahori.2 ⟨(GlobalTheory.SplitFlip.mem_KO_iff x).2
    ⟨fun i j => deep_zero_iff.1 ((hx.1 i j).mono (h0 i j)),
      fun i j => deep_zero_iff.1 ((hx.2 i j).mono (h0 i j))⟩, fun i j h => ?_⟩
  exact deep_one_iff.1 ((hx.1 i j).mono (by simp [ray, h]))

/- English proof (translation)
Establish `key : ∀ u ∈ unipB k n, ∀ᶠ m : ℕ in Filter.atTop, ∀ i j, Deep (ray m i j) (u.val i j)`. Introduce `u hu`. Simplify using `only [Filter.eventually_all]`. Introduce `i j`. Break down `lt_trichotomy i j with h | rfl | h` into its components or cases.

Use `filter_upwards [eventually_deep (u.val i j)] with m hm`. Use `hm.mono ?_` and prove the remaining obligations. Establish `h1 : ((Finset.univ.filter (· < i)).card : ℤ) < (Finset.univ.filter (· < j)).card`. Use `Int.ofNat_lt.2 (Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun a ha => ?_).2 ⟨i, by simpa using h, by simp⟩))` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢`.

Conclude with `ha.trans h`. Simplify using `only [ray, if_neg h.not_gt]`. Use the polynomial consequences of the given equalities and inequalities. Simplify using `[((mem_unipB k).1 hu).2, ray, deep_zero_iff]`. Simplify using `[((mem_unipB k).1 hu).1 i j h, deep_zero]`.

Conclude with `(key u hu).and (key _ (inv_mem hu))`.
-/
theorem eventually_mem_ray {u : GL n k} (hu : u ∈ unipB k n) :
    ∀ᶠ m : ℕ in Filter.atTop, u ∈ grp k (chamber_ray (n := n) m).1 := by
  have key : ∀ u ∈ unipB k n, ∀ᶠ m : ℕ in Filter.atTop, ∀ i j, Deep (ray m i j) (u.val i j) := by
    intro u hu
    simp only [Filter.eventually_all]
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · filter_upwards [eventually_deep (u.val i j)] with m hm
      refine hm.mono ?_
      have h1 : ((Finset.univ.filter (· < i)).card : ℤ) < (Finset.univ.filter (· < j)).card := by
        refine Int.ofNat_lt.2 (Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun a ha => ?_).2
          ⟨i, by simpa using h, by simp⟩))
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
        exact ha.trans h
      simp only [ray, if_neg h.not_gt]
      nlinarith
    · simp [((mem_unipB k).1 hu).2, ray, deep_zero_iff]
    · simp [((mem_unipB k).1 hu).1 i j h, deep_zero]
  exact (key u hu).and (key _ (inv_mem hu))

/- English proof (translation)
Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨u, w, rfl⟩` from `hx`. Use `filter_upwards [eventually_mem_ray u.2] with m hm`. Simplify using `using sub_mem_twKer hm w`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => filter_upwards [hx, hy] with m h1 h2 using add_mem h1 h2`. Consider the case `smul a x _ hx => filter_upwards [hx] with m h1 using Submodule.smul_mem _ a h1`.
-/
theorem eventually_mem_twKer {v : V} (hv : v ∈ twKer π (unipB k n) 1) :
    ∀ᶠ m : ℕ in Filter.atTop, v ∈ twKer π (grp k (chamber_ray (n := n) m).1) 1 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, w, rfl⟩ := hx
    filter_upwards [eventually_mem_ray u.2] with m hm
    simpa using sub_mem_twKer hm w
  | zero => simp
  | add x y _ _ hx hy =>
    filter_upwards [hx, hy] with m h1 h2 using add_mem h1 h2
  | smul a x _ hx =>
    filter_upwards [hx] with m h1 using Submodule.smul_mem _ a h1

end Groups

/- English proof (translation)
Use `(injective_iff_map_eq_zero _).2 fun v hv => Subtype.ext ?_` and prove the remaining obligations. Establish `h1 : v.1 ∈ twKer π (unipB k n) 1` using `(Submodule.Quotient.mk_eq_zero _).1 (congrArg Subtype.val hv)`. Take `⟨m, hm⟩` from `(eventually_mem_twKer h1).exists`. Conclude with `inj_chambers hπ (chamber_ray 0) (chamber_ray m) v.1 (mem_fixed.2 fun h hh => mem_fixed.1 v.2 h (grp_ray_zero_le hh)) hm`.
-/
theorem iwahoriProj_injective (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V) (hπ : IsSmooth π) :
    Function.Injective (iwahoriProj π) := by
  refine (injective_iff_map_eq_zero _).2 fun v hv => Subtype.ext ?_
  have h1 : v.1 ∈ twKer π (unipB k n) 1 := (Submodule.Quotient.mk_eq_zero _).1 (congrArg Subtype.val hv)
  obtain ⟨m, hm⟩ := (eventually_mem_twKer h1).exists
  exact inj_chambers hπ (chamber_ray 0) (chamber_ray m) v.1
    (mem_fixed.2 fun h hh => mem_fixed.1 v.2 h (grp_ray_zero_le hh)) hm

end GlobalTheory.IwahoriInj
