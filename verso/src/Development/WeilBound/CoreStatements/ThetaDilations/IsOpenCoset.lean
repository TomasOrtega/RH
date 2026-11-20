import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData

open MeasureTheory Topology Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

open GlobalTheory.CompanionTheory.SW.Core

variable {V : Type} [AddCommGroup V] [TopologicalSpace V]

def CO (L : AddSubgroup V) : Prop := IsCompact (L : Set V) ∧ IsOpen (L : Set V)

def ind (a : V) (L : AddSubgroup V) : V → ℂ := Set.indicator {x | x - a ∈ L} fun _ => (1 : ℂ)

omit [TopologicalSpace V] in
/- English proof (translation)
The claim follows from `Set.indicator_of_mem (s := {x | x - a ∈ L}) h _`.
-/
theorem ind_of_mem {a x : V} {L : AddSubgroup V} (h : x - a ∈ L) : ind a L x = 1 :=
  Set.indicator_of_mem (s := {x | x - a ∈ L}) h _

omit [TopologicalSpace V] in
/- English proof (translation)
The claim follows from `Set.indicator_of_notMem (s := {x | x - a ∈ L}) h _`.
-/
theorem ind_of_not {a x : V} {L : AddSubgroup V} (h : x - a ∉ L) : ind a L x = 0 :=
  Set.indicator_of_notMem (s := {x | x - a ∈ L}) h _

omit [TopologicalSpace V] in
/- English proof (translation)
Distinguish the cases in `hx : x - a ∈ L`. Rewrite using `[ind_of_mem hx, ind_of_mem (h.1 hx)]`. Rewrite using `[ind_of_not hx, ind_of_not (mt h.2 hx)]`.
-/
theorem ind_congr {a b x y : V} {L L' : AddSubgroup V} (h : x - a ∈ L ↔ y - b ∈ L') : ind a L x = ind b L' y := by
  by_cases hx : x - a ∈ L
  · rw [ind_of_mem hx, ind_of_mem (h.1 hx)]
  · rw [ind_of_not hx, ind_of_not (mt h.2 hx)]

omit [TopologicalSpace V] in
/- English proof (translation)
The claim follows from `ind_congr (by rw [add_sub_right_comm, L.add_mem_cancel_right hl])`.
-/
theorem ind_add {a l : V} {L : AddSubgroup V} (x : V) (hl : l ∈ L) : ind a L (x + l) = ind a L x :=
  ind_congr (by rw [add_sub_right_comm, L.add_mem_cancel_right hl])

section top

variable [IsTopologicalAddGroup V]

/- English proof (translation)
Assemble the required witnesses or components as `⟨by rw [AddSubgroup.add_normal]; exact h.1.add h'.1, AddSubgroup.isOpen_mono le_sup_left h.2⟩`.
-/
theorem CO.sup {L L' : AddSubgroup V} (h : CO L) (h' : CO L') : CO (L ⊔ L') :=
  ⟨by rw [AddSubgroup.add_normal]; exact h.1.add h'.1, AddSubgroup.isOpen_mono le_sup_left h.2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1.inter_right (L'.isClosed_of_isOpen h'), h.2.inter h'⟩`.
-/
theorem CO.inf {L L' : AddSubgroup V} (h : CO L) (h' : IsOpen (L' : Set V)) : CO (L ⊓ L') :=
  ⟨h.1.inter_right (L'.isClosed_of_isOpen h'), h.2.inter h'⟩

/- English proof (translation)
The claim follows from `h.preimage (continuous_id.sub continuous_const)`.
-/
theorem isOpen_coset (a : V) {L : AddSubgroup V} (h : IsOpen (L : Set V)) : IsOpen {x | x - a ∈ L} :=
  h.preimage (continuous_id.sub continuous_const)

/- English proof (translation)
The claim follows from `(IsLocallyConstant.iff_exists_open f).2 fun x => ⟨{y | y - x ∈ L}, isOpen_coset x h, by simp, fun y hy => by have := hf x _ hy rwa [add_sub_cancel] at this⟩`.
-/
theorem lc_of_inv {f : V → ℂ} {L : AddSubgroup V} (h : IsOpen (L : Set V)) (hf : ∀ x, ∀ l ∈ L, f (x + l) = f x) :
    IsLocallyConstant f :=
  (IsLocallyConstant.iff_exists_open f).2 fun x => ⟨{y | y - x ∈ L}, isOpen_coset x h, by simp, fun y hy => by
    have := hf x _ hy
    rwa [add_sub_cancel] at this⟩

/- English proof (translation)
Use `⟨lc_of_inv h.2 fun x l hl => ?_, HasCompactSupport.intro (K := (fun y => y + a) '' L) (h.1.image (continuous_id.add continuous_const)) fun x hx => ind_of_not fun h' => hx ⟨_, h', by simp⟩⟩` and prove the remaining obligations. Distinguish the cases in `hx : x - a ∈ L`. Rewrite using `[ind_of_mem hx, ind_of_mem (by rw [add_sub_right_comm]; exact L.add_mem hx hl)]`. Rewrite using `[ind_of_not hx, ind_of_not fun h' => hx (by`. Rewrite `h'` using `[add_sub_right_comm]`.

Conclude with `(L.add_mem_cancel_right hl).1 h')]`.
-/
theorem sb_ind [T2Space V] (a : V) {L : AddSubgroup V} (h : CO L) : SB (ind a L) := by
  refine ⟨lc_of_inv h.2 fun x l hl => ?_, HasCompactSupport.intro (K := (fun y => y + a) '' L)
    (h.1.image (continuous_id.add continuous_const)) fun x hx => ind_of_not fun h' => hx ⟨_, h', by simp⟩⟩
  by_cases hx : x - a ∈ L
  · rw [ind_of_mem hx, ind_of_mem (by rw [add_sub_right_comm]; exact L.add_mem hx hl)]
  · rw [ind_of_not hx, ind_of_not fun h' => hx (by
      rw [add_sub_right_comm] at h'; exact (L.add_mem_cancel_right hl).1 h')]

end top

omit [AddCommGroup V] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨hf.1.add hg.1, hf.2.add hg.2⟩`.
-/
theorem sb_add {f g : V → ℂ} (hf : SB f) (hg : SB g) : SB (f + g) := ⟨hf.1.add hg.1, hf.2.add hg.2⟩

omit [AddCommGroup V] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨hf.mul hg.1, hg.2.mul_left⟩`.
-/
theorem sb_mul {f g : V → ℂ} (hf : IsLocallyConstant f) (hg : SB g) : SB fun x => f x * g x :=
  ⟨hf.mul hg.1, hg.2.mul_left⟩

omit [AddCommGroup V] in
/- English proof (translation)
The claim follows from `sb_mul (IsLocallyConstant.const c) hg`.
-/
theorem sb_smul (c : ℂ) {g : V → ℂ} (hg : SB g) : SB (c • g) := sb_mul (IsLocallyConstant.const c) hg

omit [AddCommGroup V] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩`.
-/
theorem sb_zero : SB (0 : V → ℂ) := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩

omit [AddCommGroup V] in
/- English proof (translation)
The claim follows from `Finset.sum_induction _ SB (fun _ _ => sb_add) sb_zero h`.
-/
theorem sb_sum {α : Type} (s : Finset α) {f : α → V → ℂ} (h : ∀ a ∈ s, SB (f a)) : SB (∑ a ∈ s, f a) :=
  Finset.sum_induction _ SB (fun _ _ => sb_add) sb_zero h

omit [AddCommGroup V] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩`.
-/
theorem sb_homeo {f : V → ℂ} (hf : SB f) (e : V ≃ₜ V) : SB (f ∘ e) :=
  ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩

/- English proof (translation)
Use `QuotientAddGroup.discreteTopology hL` as an intermediate fact. Establish `hfin : ((QuotientAddGroup.mk : V → V ⧸ L) '' tsupport φ).Finite` using `(hφ.2.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete`. Use `⟨hfin.toFinset.image Quotient.out, funext fun x => ?_⟩` and prove the remaining obligations. Establish `hq : ∀ c : V ⧸ L, x - c.out ∈ L ↔ c = QuotientAddGroup.mk x` using `fun c => by`. Rewrite using `[← QuotientAddGroup.eq_iff_sub_mem, QuotientAddGroup.out_eq', eq_comm]`.

Rewrite using `[Finset.sum_apply, Finset.sum_image fun a _ b _ h => Quotient.out_injective h]`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Use `Eq.trans ?_ (Finset.sum_eq_single (QuotientAddGroup.mk x : V ⧸ L) (fun c _ hc => ?_) fun hx => ?_).symm` and prove the remaining obligations. Use `hinv (QuotientAddGroup.mk x : V ⧸ L).out _ ((hq _).2 rfl)` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`.

Rewrite using `[ind_of_mem ((hq _).2 rfl), mul_one, this]`. Rewrite using `[ind_of_not (mt (hq c).1 hc), mul_zero]`. Establish `h0 : φ (QuotientAddGroup.mk x : V ⧸ L).out = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hx (hfin.mem_toFinset.2 ⟨_, subset_tsupport _ hne, QuotientAddGroup.out_eq' _⟩)`.

Rewrite using `[h0, zero_mul]`.
-/
theorem sb_span [IsTopologicalAddGroup V] {φ : V → ℂ} (hφ : SB φ) {L : AddSubgroup V} (hL : IsOpen (L : Set V))
    (hinv : ∀ x, ∀ l ∈ L, φ (x + l) = φ x) : ∃ s : Finset V, φ = ∑ a ∈ s, φ a • ind a L := by
  classical
  have := QuotientAddGroup.discreteTopology hL
  have hfin : ((QuotientAddGroup.mk : V → V ⧸ L) '' tsupport φ).Finite :=
    (hφ.2.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  refine ⟨hfin.toFinset.image Quotient.out, funext fun x => ?_⟩
  have hq : ∀ c : V ⧸ L, x - c.out ∈ L ↔ c = QuotientAddGroup.mk x := fun c => by
    rw [← QuotientAddGroup.eq_iff_sub_mem, QuotientAddGroup.out_eq', eq_comm]
  rw [Finset.sum_apply, Finset.sum_image fun a _ b _ h => Quotient.out_injective h]
  simp only [Pi.smul_apply, smul_eq_mul]
  refine Eq.trans ?_ (Finset.sum_eq_single (QuotientAddGroup.mk x : V ⧸ L) (fun c _ hc => ?_) fun hx => ?_).symm
  · have := hinv (QuotientAddGroup.mk x : V ⧸ L).out _ ((hq _).2 rfl)
    rw [add_sub_cancel] at this
    rw [ind_of_mem ((hq _).2 rfl), mul_one, this]
  · rw [ind_of_not (mt (hq c).1 hc), mul_zero]
  · have h0 : φ (QuotientAddGroup.mk x : V ⧸ L).out = 0 := by
      by_contra hne
      exact hx (hfin.mem_toFinset.2 ⟨_, subset_tsupport _ hne, QuotientAddGroup.out_eq' _⟩)
    rw [h0, zero_mul]

variable [MeasurableSpace V] {χ : V → V → ℂ} {μ : Measure V}

/- English proof (translation)
Take `⟨_, -, -, -, -, -, -, hbig, -⟩` from `h`. Use `hK.induction_on (p := fun s => ∃ L : AddSubgroup V, CO L ∧ s ⊆ L) ?_ ?_ ?_ ?_` and prove the remaining obligations. Take `⟨L, h1, h2, -⟩` from `hbig 0`. Conclude with `⟨L, ⟨h1, h2⟩, empty_subset _⟩`. Introduce and unpack `s t hst ⟨L, h1, h2⟩`.

Conclude with `⟨L, h1, hst.trans h2⟩`. Introduce and unpack `s t ⟨L, h1, h2⟩ ⟨L', h1', h2'⟩`. Conclude with `⟨L ⊔ L', h1.sup h1', union_subset (h2.trans (SetLike.coe_subset_coe.2 le_sup_left)) (h2'.trans (SetLike.coe_subset_coe.2 le_sup_right))⟩`. Introduce `x _`. Take `⟨L, h1, h2, h3⟩` from `hbig x`.

Conclude with `⟨L, mem_nhdsWithin_of_mem_nhds (h2.mem_nhds h3), L, ⟨h1, h2⟩, le_rfl⟩`.
-/
theorem co_cpt (h : NADual V χ μ) {K : Set V} (hK : IsCompact K) : ∃ L : AddSubgroup V, CO L ∧ K ⊆ L := by
  obtain ⟨_, -, -, -, -, -, -, hbig, -⟩ := h
  refine hK.induction_on (p := fun s => ∃ L : AddSubgroup V, CO L ∧ s ⊆ L) ?_ ?_ ?_ ?_
  · obtain ⟨L, h1, h2, -⟩ := hbig 0
    exact ⟨L, ⟨h1, h2⟩, empty_subset _⟩
  · rintro s t hst ⟨L, h1, h2⟩
    exact ⟨L, h1, hst.trans h2⟩
  · rintro s t ⟨L, h1, h2⟩ ⟨L', h1', h2'⟩
    exact ⟨L ⊔ L', h1.sup h1', union_subset (h2.trans (SetLike.coe_subset_coe.2 le_sup_left))
      (h2'.trans (SetLike.coe_subset_coe.2 le_sup_right))⟩
  · intro x _
    obtain ⟨L, h1, h2, h3⟩ := hbig x
    exact ⟨L, mem_nhdsWithin_of_mem_nhds (h2.mem_nhds h3), L, ⟨h1, h2⟩, le_rfl⟩

/- English proof (translation)
Take `⟨L, hL, hKL⟩` from `co_cpt h hφ.2.isCompact`. Take `⟨_, -, -, -, -, -, hsmall, -⟩` from `h`. Establish `h0 : ∀ x, x ∉ L → φ x = 0` using `fun x hx => image_eq_zero_of_notMem_tsupport fun h' => hx (hKL h')`. Establish `key : ∃ L' : AddSubgroup V, IsOpen (L' : Set V) ∧ ∀ x ∈ (L : Set V), ∀ l ∈ L', φ (x + l) = φ x`. Use `hL.1.induction_on (p := fun s => ∃ L' : AddSubgroup V, IsOpen (L' : Set V) ∧ ∀ x ∈ s, ∀ l ∈ L', φ (x + l) = φ x) ?_ ?_ ?_ ?_` and prove the remaining obligations.

Conclude with `⟨⊤, isOpen_univ, fun _ h => absurd h (notMem_empty _)⟩`. Introduce and unpack `s t hst ⟨L', h1, h2⟩`. Conclude with `⟨L', h1, fun x hx => h2 x (hst hx)⟩`. Introduce and unpack `s t ⟨L₁, h1, h2⟩ ⟨L₂, h1', h2'⟩`. Conclude with `⟨L₁ ⊓ L₂, h1.inter h1', fun x hx l hl => hx.elim (fun h => h2 x h l hl.1) fun h => h2' x h l hl.2⟩`.

Introduce `x _`. Establish `hU : {y | φ (x + y) = φ x} ∈ 𝓝 (0 : V)`. Establish `h1 : ContinuousAt (fun y => x + y) 0` using `(continuous_const.add continuous_id).continuousAt`. Conclude with `h1.preimage_mem_nhds (by rw [add_zero]; exact hφ.1.eventually_eq x)`. Take `⟨L₀, -, h2, h3⟩` from `hsmall _ hU`.

Use `⟨{y | y - x ∈ L₀}, mem_nhdsWithin_of_mem_nhds ((isOpen_coset x h2).mem_nhds (by simp)), L₀, h2, fun y hy l hl => ?_⟩` and prove the remaining obligations. Establish `e1 : φ (x + (y - x + l)) = φ x` using `h3 (L₀.add_mem hy hl)`. Establish `e2 : φ (x + (y - x)) = φ x` using `h3 hy`. Rewrite `e2` using `[add_sub_cancel]`. Rewrite `e1` using `[← add_assoc, add_sub_cancel]`.

Rewrite using `[e1, e2]`. Take `⟨L', h1, h2⟩` from `key`. Use `⟨L, L ⊓ L', hL, hL.inf h1, inf_le_left, h0, fun x l hl => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ L`. Conclude with `h2 x hx l hl.2`.

Rewrite using `[h0 x hx, h0 _ fun h' => hx ((L.add_mem_cancel_right hl.1).1 h')]`.
-/
theorem sb_level (h : NADual V χ μ) {φ : V → ℂ} (hφ : SB φ) :
    ∃ L L' : AddSubgroup V, CO L ∧ CO L' ∧ L' ≤ L ∧ (∀ x, x ∉ L → φ x = 0) ∧ ∀ x, ∀ l ∈ L', φ (x + l) = φ x := by
  obtain ⟨L, hL, hKL⟩ := co_cpt h hφ.2.isCompact
  obtain ⟨_, -, -, -, -, -, hsmall, -⟩ := h
  have h0 : ∀ x, x ∉ L → φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport fun h' => hx (hKL h')
  have key : ∃ L' : AddSubgroup V, IsOpen (L' : Set V) ∧ ∀ x ∈ (L : Set V), ∀ l ∈ L', φ (x + l) = φ x := by
    refine hL.1.induction_on
      (p := fun s => ∃ L' : AddSubgroup V, IsOpen (L' : Set V) ∧ ∀ x ∈ s, ∀ l ∈ L', φ (x + l) = φ x) ?_ ?_ ?_ ?_
    · exact ⟨⊤, isOpen_univ, fun _ h => absurd h (notMem_empty _)⟩
    · rintro s t hst ⟨L', h1, h2⟩
      exact ⟨L', h1, fun x hx => h2 x (hst hx)⟩
    · rintro s t ⟨L₁, h1, h2⟩ ⟨L₂, h1', h2'⟩
      exact ⟨L₁ ⊓ L₂, h1.inter h1', fun x hx l hl => hx.elim (fun h => h2 x h l hl.1) fun h => h2' x h l hl.2⟩
    · intro x _
      have hU : {y | φ (x + y) = φ x} ∈ 𝓝 (0 : V) := by
        have h1 : ContinuousAt (fun y => x + y) 0 := (continuous_const.add continuous_id).continuousAt
        exact h1.preimage_mem_nhds (by rw [add_zero]; exact hφ.1.eventually_eq x)
      obtain ⟨L₀, -, h2, h3⟩ := hsmall _ hU
      refine ⟨{y | y - x ∈ L₀}, mem_nhdsWithin_of_mem_nhds ((isOpen_coset x h2).mem_nhds (by simp)), L₀, h2,
        fun y hy l hl => ?_⟩
      have e1 : φ (x + (y - x + l)) = φ x := h3 (L₀.add_mem hy hl)
      have e2 : φ (x + (y - x)) = φ x := h3 hy
      rw [add_sub_cancel] at e2
      rw [← add_assoc, add_sub_cancel] at e1
      rw [e1, e2]
  obtain ⟨L', h1, h2⟩ := key
  refine ⟨L, L ⊓ L', hL, hL.inf h1, inf_le_left, h0, fun x l hl => ?_⟩
  by_cases hx : x ∈ L
  · exact h2 x hx l hl.2
  · rw [h0 x hx, h0 _ fun h' => hx ((L.add_mem_cancel_right hl.1).1 h')]

section chi

variable (h : NADual V χ μ)
include h

/- English proof (translation)
The claim follows from `h.2.2.2.2.2.2.2.2.2.1 x y`.
-/
theorem chi_sym (x y : V) : χ x y = χ y x := h.2.2.2.2.2.2.2.2.2.1 x y
/- English proof (translation)
The claim follows from `h.2.2.2.2.2.2.2.2.2.2.1 x y`.
-/
theorem chi_norm (x y : V) : ‖χ x y‖ = 1 := h.2.2.2.2.2.2.2.2.2.2.1 x y
/- English proof (translation)
The claim follows from `h.2.2.2.2.2.2.2.2.2.2.2.1 x x' y`.
-/
theorem chi_add (x x' y : V) : χ (x + x') y = χ x y * χ x' y := h.2.2.2.2.2.2.2.2.2.2.2.1 x x' y
/- English proof (translation)
The claim follows from `h.2.2.2.2.2.2.2.2.1`.
-/
theorem chi_cont : Continuous fun p : V × V => χ p.1 p.2 := h.2.2.2.2.2.2.2.2.1
/- English proof (translation)
The claim follows from `norm_ne_zero_iff.1 (by rw [chi_norm h]; exact one_ne_zero)`.
-/
theorem chi_ne (x y : V) : χ x y ≠ 0 := norm_ne_zero_iff.1 (by rw [chi_norm h]; exact one_ne_zero)
/- English proof (translation)
Rewrite using `[chi_sym h, chi_add h, chi_sym h y, chi_sym h y']`.
-/
theorem chi_add' (x y y' : V) : χ x (y + y') = χ x y * χ x y' := by
  rw [chi_sym h, chi_add h, chi_sym h y, chi_sym h y']
/- English proof (translation)
The claim follows from `mul_left_cancel₀ (chi_ne h 0 y) (by rw [← chi_add h, add_zero, mul_one])`.
-/
theorem chi_zero (y : V) : χ 0 y = 1 :=
  mul_left_cancel₀ (chi_ne h 0 y) (by rw [← chi_add h, add_zero, mul_one])
/- English proof (translation)
Use `mul_left_cancel₀ (chi_ne h x y) ?_` and prove the remaining obligations. Rewrite using `[← chi_add h, add_neg_cancel, chi_zero h, Complex.mul_conj', chi_norm h]`. Simplify using the standard rewrite rules.
-/
theorem chi_neg (x y : V) : χ (-x) y = conj (χ x y) := by
  refine mul_left_cancel₀ (chi_ne h x y) ?_
  rw [← chi_add h, add_neg_cancel, chi_zero h, Complex.mul_conj', chi_norm h]; simp

def perpG (L : AddSubgroup V) : AddSubgroup V where
  carrier := perp χ L
  zero_mem' := fun x _ => by rw [chi_sym h, chi_zero h]
  add_mem' := fun ha hb x hx => by rw [chi_add' h, ha x hx, hb x hx, one_mul]
  neg_mem' := fun {y} hy x hx => by rw [chi_sym h, chi_neg h, chi_sym h, hy x hx, map_one]

/- English proof (translation)
Assemble the required witnesses or components as `⟨(h.2.2.2.2.2.2.2.2.2.2.2.2 L hL.1 hL.2).1, (h.2.2.2.2.2.2.2.2.2.2.2.2 L hL.1 hL.2).2.1⟩`.
-/
theorem co_perp {L : AddSubgroup V} (hL : CO L) : CO (perpG h L) :=
  ⟨(h.2.2.2.2.2.2.2.2.2.2.2.2 L hL.1 hL.2).1, (h.2.2.2.2.2.2.2.2.2.2.2.2 L hL.1 hL.2).2.1⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun hx => (h.2.2.2.2.2.2.2.2.2.2.2.2 L hL.1 hL.2).2.2.1 hx, fun hx y hy => by rw [chi_sym h]; exact hy x hx⟩`.
-/
theorem perp_perp {L : AddSubgroup V} (hL : CO L) (x : V) : x ∈ perpG h (perpG h L) ↔ x ∈ L :=
  ⟨fun hx => (h.2.2.2.2.2.2.2.2.2.2.2.2 L hL.1 hL.2).2.2.1 hx, fun hx y hy => by rw [chi_sym h]; exact hy x hx⟩

/- English proof (translation)
Rewrite using `[← ENNReal.toReal_mul]`. Conclude with `(congrArg ENNReal.toReal (h.2.2.2.2.2.2.2.2.2.2.2.2 L hL.1 hL.2).2.2.2).trans ENNReal.toReal_one`.
-/
theorem meas_perp {L : AddSubgroup V} (hL : CO L) : (μ L).toReal * (μ (perpG h L)).toReal = 1 := by
  rw [← ENNReal.toReal_mul]
  exact (congrArg ENNReal.toReal (h.2.2.2.2.2.2.2.2.2.2.2.2 L hL.1 hL.2).2.2.2).trans ENNReal.toReal_one

/- English proof (translation)
Use `h.1` as an intermediate fact. Take `⟨L, hL, ha⟩` from `co_cpt h (isCompact_singleton (x := a))`. Conclude with `lc_of_inv (co_perp h hL).2 fun x l hl => by rw [chi_add' h, hl a (ha rfl), mul_one]`.
-/
theorem chi_lc (a : V) : IsLocallyConstant fun y => χ a y := by
  have := h.1
  obtain ⟨L, hL, ha⟩ := co_cpt h (isCompact_singleton (x := a))
  exact lc_of_inv (co_perp h hL).2 fun x l hl => by rw [chi_add' h, hl a (ha rfl), mul_one]

/- English proof (translation)
Take `⟨_, _, _, _, _, _, -⟩` from `h`. Conclude with `hφ.1.continuous.integrable_of_hasCompactSupport hφ.2`.
-/
theorem sb_int {φ : V → ℂ} (hφ : SB φ) : Integrable φ μ := by
  obtain ⟨_, _, _, _, _, _, -⟩ := h
  exact hφ.1.continuous.integrable_of_hasCompactSupport hφ.2

/- English proof (translation)
Simplify `sb_mul (chi_lc h y) hφ` using `only [mul_comm, chi_sym h y]`.
-/
theorem sb_chi {φ : V → ℂ} (hφ : SB φ) (y : V) : SB fun x => φ x * χ x y := by
  simpa only [mul_comm, chi_sym h y] using sb_mul (chi_lc h y) hφ

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `only [fou, Pi.add_apply, add_mul]`. Conclude with `integral_add (sb_int h (sb_chi h hf y)) (sb_int h (sb_chi h hg y))`.
-/
theorem fou_add {f g : V → ℂ} (hf : SB f) (hg : SB g) : fou χ μ (f + g) = fou χ μ f + fou χ μ g := by
  funext y
  simp only [fou, Pi.add_apply, add_mul]
  exact integral_add (sb_int h (sb_chi h hf y)) (sb_int h (sb_chi h hg y))

omit h in
/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `only [fou, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]`.
-/
theorem fou_smul (c : ℂ) (f : V → ℂ) : fou χ μ (c • f) = c • fou χ μ f := by
  funext y
  simp only [fou, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

omit h [AddCommGroup V] [MeasurableSpace V] in
/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using hsm 0 0 sb_zero`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, hadd _ _ (sb_smul _ (hf a)) (sb_sum _ fun b _ => sb_smul _ (hf b)), hsm _ _ (hf a), ih]`.
-/
theorem map_sum_sb {T : (V → ℂ) → (V → ℂ)} (hadd : ∀ φ φ', SB φ → SB φ' → T (φ + φ') = T φ + T φ')
    (hsm : ∀ (c : ℂ) φ, SB φ → T (c • φ) = c • T φ) {α : Type} (s : Finset α) (c : α → ℂ) {f : α → V → ℂ}
    (hf : ∀ a, SB (f a)) : T (∑ a ∈ s, c a • f a) = ∑ a ∈ s, c a • T (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hsm 0 0 sb_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd _ _ (sb_smul _ (hf a)) (sb_sum _ fun b _ => sb_smul _ (hf b)),
      hsm _ _ (hf a), ih]

/- English proof (translation)
Establish `hh` using `h`. Take `⟨_, _, _, _, _, _, -⟩` from `hh`. Establish `e1 : fou χ μ (ind a L) y = χ a y * ∫ x, ind 0 L x * χ x y ∂μ`. Rewrite using `[fou, ← integral_add_right_eq_self _ a, ← integral_const_mul]`. Use `integral_congr_ae (ae_of_all _ fun x => ?_)` and prove the remaining obligations.

Simplify using `only [chi_add h]`. Rewrite using `[ind_congr (b := 0) (y := x) (L' := L) (by rw [add_sub_cancel_right, sub_zero])]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Distinguish the cases in `hy : y ∈ perpG h L`.

Rewrite using `[ind_of_mem (by simpa using hy)]`. Establish `e2 : (fun x => ind 0 L x * χ x y) = Set.indicator (L : Set V) fun _ => (1 : ℂ)`. Use function extensionality and compare the values at `x`. Distinguish the cases in `hx : x ∈ L`. Rewrite using `[ind_of_mem (by simpa using hx), hy x hx, Set.indicator_of_mem (s := (L : Set V)) hx, one_mul]`.

Rewrite using `[ind_of_not (by simpa using hx), Set.indicator_of_notMem (s := (L : Set V)) hx, zero_mul]`. Rewrite using `[e2, integral_indicator_const _ hL.2.measurableSet]`. Simplify using `[Measure.real, mul_comm]`. Rewrite using `[ind_of_not (by simpa using hy), mul_zero]`. Choose the witnesses or unpack the hypotheses as in `⟨l, hl, hne⟩ : ∃ l ∈ L, χ l y ≠ 1 := by`.

Assume the negation of the conclusion as `h'`. Use `push Not at h'`. Conclude with `hy h'`. Establish `e2 : ∫ x, ind 0 L x * χ x y ∂μ = χ l y * ∫ x, ind 0 L x * χ x y ∂μ` using `by conv_lhs => rw [← integral_add_right_eq_self _ l]`. Rewrite using `[← integral_const_mul]`.

Use `integral_congr_ae (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Simplify using `only [chi_add h, ind_add x hl]`. Expand and normalize the polynomial expressions, which then agree. Establish `e3 : (1 - χ l y) * ∫ x, ind 0 L x * χ x y ∂μ = 0` using `by rw [sub_mul, one_mul, ← e2, sub_self]`. Rewrite using `[(mul_eq_zero.1 e3).resolve_left (sub_ne_zero.2 hne.symm), mul_zero]`.
-/
theorem fou_ind {L : AddSubgroup V} (hL : CO L) (a y : V) :
    fou χ μ (ind a L) y = ((μ L).toReal : ℂ) * χ a y * ind 0 (perpG h L) y := by
  have hh := h
  obtain ⟨_, _, _, _, _, _, -⟩ := hh
  have e1 : fou χ μ (ind a L) y = χ a y * ∫ x, ind 0 L x * χ x y ∂μ := by
    rw [fou, ← integral_add_right_eq_self _ a, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [chi_add h]
    rw [ind_congr (b := 0) (y := x) (L' := L) (by rw [add_sub_cancel_right, sub_zero])]
    ring
  rw [e1]
  by_cases hy : y ∈ perpG h L
  · rw [ind_of_mem (by simpa using hy)]
    have e2 : (fun x => ind 0 L x * χ x y) = Set.indicator (L : Set V) fun _ => (1 : ℂ) := by
      funext x
      by_cases hx : x ∈ L
      · rw [ind_of_mem (by simpa using hx), hy x hx, Set.indicator_of_mem (s := (L : Set V)) hx, one_mul]
      · rw [ind_of_not (by simpa using hx), Set.indicator_of_notMem (s := (L : Set V)) hx, zero_mul]
    rw [e2, integral_indicator_const _ hL.2.measurableSet]
    simp [Measure.real, mul_comm]
  · rw [ind_of_not (by simpa using hy), mul_zero]
    obtain ⟨l, hl, hne⟩ : ∃ l ∈ L, χ l y ≠ 1 := by
      by_contra h'
      push Not at h'
      exact hy h'
    have e2 : ∫ x, ind 0 L x * χ x y ∂μ = χ l y * ∫ x, ind 0 L x * χ x y ∂μ := by
      conv_lhs => rw [← integral_add_right_eq_self _ l]
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [chi_add h, ind_add x hl]
      ring
    have e3 : (1 - χ l y) * ∫ x, ind 0 L x * χ x y ∂μ = 0 := by rw [sub_mul, one_mul, ← e2, sub_self]
    rw [(mul_eq_zero.1 e3).resolve_left (sub_ne_zero.2 hne.symm), mul_zero]

/- English proof (translation)
Establish `hh` using `h`. Take `⟨_, _, -⟩` from `hh`. Take `⟨-, L, -, hL, -, -, hinv⟩` from `sb_level h hφ`. Take `⟨s, hs⟩` from `sb_span hφ hL.2 hinv`. Establish `hP` using `co_perp h hL`.

Establish `e1 : ∀ a, fou χ μ (ind a L) = ((μ L).toReal : ℂ) • fun y => ind 0 (perpG h L) y * χ y a` using `fun a => by`. Use function extensionality and compare the values at `y`. Rewrite using `[fou_ind h hL, Pi.smul_apply, smul_eq_mul, chi_sym h y]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ∀ a, SB (fou χ μ (ind a L))` using `fun a => e1 a ▸ sb_smul _ (sb_chi h (sb_ind 0 hP) a)`.

Establish `e3 : fou χ μ φ = ∑ a ∈ s, φ a • fou χ μ (ind a L)` using `by conv_lhs => rw [hs]`. Conclude with `map_sum_sb (fun _ _ => fou_add h) (fun c f _ => fou_smul c f) s φ fun a => sb_ind a hL`. Use `⟨e3 ▸ sb_sum _ fun a _ => sb_smul _ (e2 a), fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[e3, map_sum_sb (fun _ _ => fou_add h) (fun c f _ => fou_smul c f) s φ e2]`. Use `conv_rhs => rw [hs]`.

Simplify using `only [Finset.sum_apply, Pi.smul_apply]`. Use `Finset.sum_congr rfl fun a _ => congrArg _ ?_` and prove the remaining obligations. Establish `e4 : fou χ μ (fun y => ind 0 (perpG h L) y * χ y a) x = fou χ μ (ind 0 (perpG h L)) (a + x)`. Simplify using `only [fou, chi_add' h, mul_assoc]`. Rewrite using `[e1, fou_smul, Pi.smul_apply, e4, fou_ind h hP, chi_zero h, mul_one, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul, meas_perp h hL, Complex.ofReal_one, one_mul]`.

Establish `e5 : a + x - 0 ∈ perpG h (perpG h L) ↔ -x - a ∈ L`. Rewrite using `[perp_perp h hL, ← L.neg_mem_iff, sub_zero, neg_add_rev, sub_eq_add_neg]`. Distinguish the cases in `hx : -x - a ∈ L`. Rewrite using `[ind_of_mem hx, ind_of_mem (e5.2 hx)]`. Rewrite using `[ind_of_not hx, ind_of_not (mt e5.1 hx)]`.
-/
theorem fou_sb {φ : V → ℂ} (hφ : SB φ) : SB (fou χ μ φ) ∧ ∀ x, fou χ μ (fou χ μ φ) x = φ (-x) := by
  have hh := h
  obtain ⟨_, _, -⟩ := hh
  obtain ⟨-, L, -, hL, -, -, hinv⟩ := sb_level h hφ
  obtain ⟨s, hs⟩ := sb_span hφ hL.2 hinv
  have hP := co_perp h hL
  have e1 : ∀ a, fou χ μ (ind a L) = ((μ L).toReal : ℂ) • fun y => ind 0 (perpG h L) y * χ y a := fun a => by
    funext y
    rw [fou_ind h hL, Pi.smul_apply, smul_eq_mul, chi_sym h y]; ring
  have e2 : ∀ a, SB (fou χ μ (ind a L)) := fun a => e1 a ▸ sb_smul _ (sb_chi h (sb_ind 0 hP) a)
  have e3 : fou χ μ φ = ∑ a ∈ s, φ a • fou χ μ (ind a L) := by
    conv_lhs => rw [hs]
    exact map_sum_sb (fun _ _ => fou_add h) (fun c f _ => fou_smul c f) s φ fun a => sb_ind a hL
  refine ⟨e3 ▸ sb_sum _ fun a _ => sb_smul _ (e2 a), fun x => ?_⟩
  rw [e3, map_sum_sb (fun _ _ => fou_add h) (fun c f _ => fou_smul c f) s φ e2]
  conv_rhs => rw [hs]
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun a _ => congrArg _ ?_
  have e4 : fou χ μ (fun y => ind 0 (perpG h L) y * χ y a) x = fou χ μ (ind 0 (perpG h L)) (a + x) := by
    simp only [fou, chi_add' h, mul_assoc]
  rw [e1, fou_smul, Pi.smul_apply, e4, fou_ind h hP, chi_zero h, mul_one, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul,
    meas_perp h hL, Complex.ofReal_one, one_mul]
  have e5 : a + x - 0 ∈ perpG h (perpG h L) ↔ -x - a ∈ L := by
    rw [perp_perp h hL, ← L.neg_mem_iff, sub_zero, neg_add_rev, sub_eq_add_neg]
  by_cases hx : -x - a ∈ L
  · rw [ind_of_mem hx, ind_of_mem (e5.2 hx)]
  · rw [ind_of_not hx, ind_of_not (mt e5.1 hx)]

/- English proof (translation)
Establish `hh` using `h`. Take `⟨_, _, _, _, _, _, -⟩` from `hh`. Take `⟨hF, hinv⟩` from `fou_sb h hφ`. Establish `hc : Integrable (fun x => conj (φ x)) μ` using `(Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp (sb_int h hφ)`. Establish `hint : Integrable (Function.uncurry fun y x => fou χ μ φ y * conj (φ x) * χ y (-x)) (μ.prod μ)` using `((sb_int h hF).mul_prod hc).mul_bdd (c := 1) ((chi_cont h).comp (continuous_fst.prodMk continuous_snd.neg)).aestronglyMeasurable (ae_of_all _ fun p => (chi_norm h _ _).le)`.

Establish `e` using `integral_integral_swap hint`. Establish `e1 : ∀ y, ∫ x, fou χ μ φ y * conj (φ x) * χ y (-x) ∂μ = ((‖fou χ μ φ y‖ ^ 2 : ℝ) : ℂ)` using `fun y => by`. Simplify using `only [mul_assoc, integral_const_mul]`. Rewrite using `[Complex.ofReal_pow, ← Complex.mul_conj', fou, ← integral_conj]`. Use `congr 2`.

Use function extensionality and compare the values at `x`. Rewrite using `[map_mul, chi_sym h y, chi_neg h]`. Establish `e2 : ∀ x, ∫ y, fou χ μ φ y * conj (φ x) * χ y (-x) ∂μ = ((‖φ x‖ ^ 2 : ℝ) : ℂ)` using `fun x => by`. Use `hinv (-x)` as an intermediate fact. Rewrite `this` using `[neg_neg, fou]`.

Simplify using `only [mul_right_comm _ (conj (φ x)), integral_mul_const]`. Rewrite using `[this, Complex.ofReal_pow, Complex.mul_conj']`. Simplify using `only [e1, e2, integral_ofReal] at e`. Conclude with `e` after adjusting the coercions.
-/
theorem planch {φ : V → ℂ} (hφ : SB φ) : ∫ y, ‖fou χ μ φ y‖ ^ 2 ∂μ = ∫ x, ‖φ x‖ ^ 2 ∂μ := by
  have hh := h
  obtain ⟨_, _, _, _, _, _, -⟩ := hh
  obtain ⟨hF, hinv⟩ := fou_sb h hφ
  have hc : Integrable (fun x => conj (φ x)) μ := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp (sb_int h hφ)
  have hint : Integrable (Function.uncurry fun y x => fou χ μ φ y * conj (φ x) * χ y (-x)) (μ.prod μ) :=
    ((sb_int h hF).mul_prod hc).mul_bdd (c := 1)
      ((chi_cont h).comp (continuous_fst.prodMk continuous_snd.neg)).aestronglyMeasurable
      (ae_of_all _ fun p => (chi_norm h _ _).le)
  have e := integral_integral_swap hint
  have e1 : ∀ y, ∫ x, fou χ μ φ y * conj (φ x) * χ y (-x) ∂μ = ((‖fou χ μ φ y‖ ^ 2 : ℝ) : ℂ) := fun y => by
    simp only [mul_assoc, integral_const_mul]
    rw [Complex.ofReal_pow, ← Complex.mul_conj', fou, ← integral_conj]
    congr 2
    funext x
    rw [map_mul, chi_sym h y, chi_neg h]
  have e2 : ∀ x, ∫ y, fou χ μ φ y * conj (φ x) * χ y (-x) ∂μ = ((‖φ x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    have := hinv (-x)
    rw [neg_neg, fou] at this
    simp only [mul_right_comm _ (conj (φ x)), integral_mul_const]
    rw [this, Complex.ofReal_pow, Complex.mul_conj']
  simp only [e1, e2, integral_ofReal] at e
  exact_mod_cast e

/- English proof (translation)
Establish `hh` using `h`. Take `⟨_, _, -⟩` from `hh`. Establish `h1 : ∀ L : AddSubgroup V, CO L → ∀ a, T (ind a L) = T (ind 0 L) 0 • ind a L`. Introduce `L hL a`. Establish `e : ind a L = fun u => ind 0 L (u + -a)` using `funext fun u => ind_congr (by rw [sub_zero, sub_eq_add_neg])`.

Rewrite using `[e, htr _ _ (sb_ind 0 hL)]`. Use function extensionality and compare the values at `u`. Use `generalize_proofs`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Generalize the expression as in `u + -a = v`.

Distinguish the cases in `hv : v ∈ L`. Establish `e2 : (fun u => ind 0 L (u + v)) = ind 0 L` using `funext fun u => ind_add u hv`. Use `congrFun (htr v _ (sb_ind 0 hL)) 0` as an intermediate fact. Rewrite `this` using `[e2, zero_add]`. Rewrite using `[ind_of_mem (by simpa using hv), mul_one, this]`.

Rewrite using `[ind_of_not (by simpa using hv), mul_zero]`. Assume the negation of the conclusion as `hne`. Use `hv ((perp_perp h hL v).1 fun y hy => ?_)` and prove the remaining obligations. Establish `e2 : (fun u => χ u y * ind 0 L u) = ind 0 L`. Use function extensionality and compare the values at `u`.

Distinguish the cases in `hu : u ∈ L`. Rewrite using `[hy u hu, one_mul]`. Rewrite using `[ind_of_not (by simpa using hu), mul_zero]`. Use `congrFun (hch y _ (sb_ind 0 hL)) v` as an intermediate fact. Rewrite `this` using `[e2]`.

Rewrite using `[chi_sym h]`. Conclude with `mul_right_cancel₀ hne (this.symm.trans (one_mul _).symm)`. Establish `h2 : ∀ L : AddSubgroup V, CO L → ∀ φ, SB φ → (∀ x, ∀ l ∈ L, φ (x + l) = φ x) → T φ = T (ind 0 L) 0 • φ`. Introduce `L hL φ hφ hinv`. Take `⟨s, hs⟩` from `sb_span hφ hL.2 hinv`.

Use `conv_lhs => rw [hs]`. Use `conv_rhs => rw [hs]`. Rewrite using `[map_sum_sb hadd hsm s φ fun a => sb_ind a hL, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => by rw [h1 L hL a, smul_comm]`. Take `⟨L₀, hL₀, -⟩` from `co_cpt h isCompact_empty`.

Use `⟨T (ind 0 L₀) 0, fun φ hφ => ?_⟩` and prove the remaining obligations. Take `⟨-, L, -, hL, -, -, hinv⟩` from `sb_level h hφ`. Establish `h3` using `congrFun (h2 _ (hL₀.inf hL.2) (ind 0 L₀) (sb_ind 0 hL₀) fun x l hl => ind_add x hl.1) 0`. Rewrite `h3` using `[Pi.smul_apply, ind_of_mem (by simp), smul_eq_mul, mul_one]`. Rewrite using `[h3]`.

Conclude with `h2 _ (hL₀.inf hL.2) φ hφ fun x l hl => hinv x l hl.2`.
-/
theorem schur {T : (V → ℂ) → (V → ℂ)} (hadd : ∀ φ φ', SB φ → SB φ' → T (φ + φ') = T φ + T φ')
    (hsm : ∀ (c : ℂ) φ, SB φ → T (c • φ) = c • T φ)
    (hch : ∀ y φ, SB φ → T (fun u => χ u y * φ u) = fun u => χ u y * T φ u)
    (htr : ∀ x φ, SB φ → T (fun u => φ (u + x)) = fun u => T φ (u + x)) : ∃ c : ℂ, ∀ φ, SB φ → T φ = c • φ := by
  have hh := h
  obtain ⟨_, _, -⟩ := hh
  have h1 : ∀ L : AddSubgroup V, CO L → ∀ a, T (ind a L) = T (ind 0 L) 0 • ind a L := by
    intro L hL a
    have e : ind a L = fun u => ind 0 L (u + -a) := funext fun u => ind_congr (by rw [sub_zero, sub_eq_add_neg])
    rw [e, htr _ _ (sb_ind 0 hL)]
    funext u
    generalize_proofs
    simp only [Pi.smul_apply, smul_eq_mul]
    generalize u + -a = v
    by_cases hv : v ∈ L
    · have e2 : (fun u => ind 0 L (u + v)) = ind 0 L := funext fun u => ind_add u hv
      have := congrFun (htr v _ (sb_ind 0 hL)) 0
      rw [e2, zero_add] at this
      rw [ind_of_mem (by simpa using hv), mul_one, this]
    · rw [ind_of_not (by simpa using hv), mul_zero]
      by_contra hne
      refine hv ((perp_perp h hL v).1 fun y hy => ?_)
      have e2 : (fun u => χ u y * ind 0 L u) = ind 0 L := by
        funext u
        by_cases hu : u ∈ L
        · rw [hy u hu, one_mul]
        · rw [ind_of_not (by simpa using hu), mul_zero]
      have := congrFun (hch y _ (sb_ind 0 hL)) v
      rw [e2] at this
      rw [chi_sym h]
      exact mul_right_cancel₀ hne (this.symm.trans (one_mul _).symm)
  have h2 : ∀ L : AddSubgroup V, CO L → ∀ φ, SB φ → (∀ x, ∀ l ∈ L, φ (x + l) = φ x) → T φ = T (ind 0 L) 0 • φ := by
    intro L hL φ hφ hinv
    obtain ⟨s, hs⟩ := sb_span hφ hL.2 hinv
    conv_lhs => rw [hs]
    conv_rhs => rw [hs]
    rw [map_sum_sb hadd hsm s φ fun a => sb_ind a hL, Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [h1 L hL a, smul_comm]
  obtain ⟨L₀, hL₀, -⟩ := co_cpt h isCompact_empty
  refine ⟨T (ind 0 L₀) 0, fun φ hφ => ?_⟩
  obtain ⟨-, L, -, hL, -, -, hinv⟩ := sb_level h hφ
  have h3 := congrFun (h2 _ (hL₀.inf hL.2) (ind 0 L₀) (sb_ind 0 hL₀) fun x l hl => ind_add x hl.1) 0
  rw [Pi.smul_apply, ind_of_mem (by simp), smul_eq_mul, mul_one] at h3
  rw [h3]
  exact h2 _ (hL₀.inf hL.2) φ hφ fun x l hl => hinv x l hl.2

end chi

end PositivityTheory.PlacePermOperatorBicommutantSpan
