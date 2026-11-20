import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal

open RingTheory.Sequence

namespace GlobalTheory

section Split

variable {ι : Type*}

noncomputable def MonoDeg.mulVar (i : ι) {a : ℕ} (γ : MonoDeg ι a) : MonoDeg ι (a + 1) :=
  ⟨γ.1 + Finsupp.single i 1, by simp [γ.2]⟩

/- English proof (translation)
Introduce `_ _ h` and use `Subtype.ext (add_right_cancel (congrArg Subtype.val h))`.
-/
theorem MonoDeg.mulVar_injective (i : ι) (a : ℕ) :
    Function.Injective (MonoDeg.mulVar i : MonoDeg ι a → MonoDeg ι (a + 1)) :=
  fun _ _ h => Subtype.ext (add_right_cancel (congrArg Subtype.val h))

noncomputable def MonoDeg.toOption {a : ℕ} (β : MonoDeg ι a) : MonoDeg (Option ι) a :=
  ⟨β.1.mapDomain some, by simp [Finsupp.degree_mapDomain, β.2]⟩

noncomputable def MonoDeg.optionEquiv (ι : Type*) (a : ℕ) :
    MonoDeg ι (a + 1) ⊕ MonoDeg (Option ι) a ≃ MonoDeg (Option ι) (a + 1) :=
  Equiv.ofBijective (Sum.elim MonoDeg.toOption (MonoDeg.mulVar none)) <| by
    have hne : ∀ (β : MonoDeg ι (a + 1)) (γ : MonoDeg (Option ι) a),
        β.toOption ≠ MonoDeg.mulVar none γ := by
      intro β γ h
      have := DFunLike.congr_fun (congrArg Subtype.val h) none
      simp only [MonoDeg.toOption, MonoDeg.mulVar] at this
      rw [Finsupp.mapDomain_of_notMem_range _ _ (by simp)] at this
      simp at this
    constructor
    · refine Function.Injective.sumElim ?_ (MonoDeg.mulVar_injective _ _) hne
      intro β β' h
      exact Subtype.ext (Finsupp.mapDomain_injective (Option.some_injective _)
        (congrArg Subtype.val h))
    · rintro ⟨α, hα⟩
      by_cases h0 : α none = 0
      · have h1 : α.some.mapDomain some = α := by
          ext o
          cases o with
          | none => rw [Finsupp.mapDomain_of_notMem_range _ _ (by simp), h0]
          | some i => rw [Finsupp.mapDomain_apply (Option.some_injective _), Finsupp.some_apply]
        refine ⟨Sum.inl ⟨α.some, ?_⟩, Subtype.ext h1⟩
        rw [← hα, ← h1, Finsupp.degree_mapDomain, h1]
      · have h1 : α - Finsupp.single none 1 + Finsupp.single none 1 = α :=
          tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.pos_of_ne_zero h0))
        refine ⟨Sum.inr ⟨α - Finsupp.single none 1, ?_⟩, Subtype.ext h1⟩
        rw [← h1, map_add, Finsupp.degree_single] at hα
        omega

variable {R : Type*} [CommRing R]

/- English proof (translation)
Simplify using `[MonoDeg.mulVar, monoVal_add, mul_comm]`.
-/
theorem monoVal_mulVar (f : ι → R) (i : ι) {a : ℕ} (γ : MonoDeg ι a) :
    monoVal f (MonoDeg.mulVar i γ).1 = f i * monoVal f γ.1 := by
  simp [MonoDeg.mulVar, monoVal_add, mul_comm]

/- English proof (translation)
The claim follows from `Finsupp.prod_mapDomain_index_inj (Option.some_injective _)`.
-/
theorem monoVal_toOption (f : Option ι → R) {a : ℕ} (β : MonoDeg ι a) :
    monoVal f β.toOption.1 = monoVal (f ∘ some) β.1 :=
  Finsupp.prod_mapDomain_index_inj (Option.some_injective _)

variable [Finite ι] {M : Type*} [AddCommGroup M] [Module R M]

/- English proof (translation)
Rewrite using `[← (MonoDeg.optionEquiv ι a).sum_comp, Fintype.sum_sum_type, Finset.smul_sum]`. Apply the tactic sequence `congr 1 <;> refine Finset.sum_congr rfl fun _ _ => ?_`. Rewrite using `[← monoVal_toOption]`. Both sides reduce to the same expression. Rewrite using `[smul_smul, ← monoVal_mulVar]`.

Both sides reduce to the same expression.
-/
theorem sum_monoVal_smul_option (f : Option ι → R) (a : ℕ) (c : MonoDeg (Option ι) (a + 1) → M) :
    ∑ α, monoVal f α.1 • c α = ∑ β : MonoDeg ι (a + 1), monoVal (f ∘ some) β.1 • c β.toOption +
      f none • ∑ γ : MonoDeg (Option ι) a, monoVal f γ.1 • c (MonoDeg.mulVar none γ) := by
  rw [← (MonoDeg.optionEquiv ι a).sum_comp, Fintype.sum_sum_type, Finset.smul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun _ _ => ?_
  · rw [← monoVal_toOption]
    rfl
  · rw [smul_smul, ← monoVal_mulVar]
    rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `Submodule.smul_induction_on hx ?_ ?_` and prove the remaining obligations. Introduce `r hr m hm`. Rewrite `hr` using `[span_range_pow_eq_span_monoVal, Ideal.mem_span_range_iff_exists_fun]`.

Take `⟨b, rfl⟩` from `hr`. Conclude with `⟨fun α => b α • m, fun α => N.smul_mem _ hm, by simp [Finset.sum_smul, mul_comm, smul_smul]⟩`. Introduce and unpack `_ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩`. Conclude with `⟨c + d, fun α => N.add_mem (hc α) (hd α), by simp [Finset.sum_add_distrib]⟩`. Introduce and unpack `⟨c, hc, rfl⟩`.

Conclude with `Submodule.sum_mem _ fun α _ => Submodule.smul_mem_smul (monoVal_mem_pow f α) (hc α)`.
-/
theorem mem_pow_smul_iff (f : ι → R) (a : ℕ) (N : Submodule R M) (x : M) :
    x ∈ Ideal.span (Set.range f) ^ a • N ↔
      ∃ c : MonoDeg ι a → M, (∀ α, c α ∈ N) ∧ ∑ α, monoVal f α.1 • c α = x := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr m hm
      rw [span_range_pow_eq_span_monoVal, Ideal.mem_span_range_iff_exists_fun] at hr
      obtain ⟨b, rfl⟩ := hr
      exact ⟨fun α => b α • m, fun α => N.smul_mem _ hm,
        by simp [Finset.sum_smul, mul_comm, smul_smul]⟩
    · rintro _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
      exact ⟨c + d, fun α => N.add_mem (hc α) (hd α), by simp [Finset.sum_add_distrib]⟩
  · rintro ⟨c, hc, rfl⟩
    exact Submodule.sum_mem _ fun α _ => Submodule.smul_mem_smul (monoVal_mem_pow f α) (hc α)

/- English proof (translation)
Rewrite using `[pow_succ, mul_smul]`. Conclude with `(mem_pow_smul_iff f a _ _).mpr ⟨c, hc, rfl⟩`.
-/
theorem sum_monoVal_smul_mem_pow_succ (f : ι → R) {a : ℕ} {c : MonoDeg ι a → M}
    (hc : ∀ α, c α ∈ (Ideal.span (Set.range f) • ⊤ : Submodule R M)) :
    ∑ α, monoVal f α.1 • c α ∈ (Ideal.span (Set.range f) ^ (a + 1) • ⊤ : Submodule R M) := by
  rw [pow_succ, mul_smul]
  exact (mem_pow_smul_iff f a _ _).mpr ⟨c, hc, rfl⟩

/- English proof (translation)
Use `⟨fun h a c hc => h a c (by rw [hc]; exact zero_mem _), fun h a c hc α => ?_⟩` and prove the remaining obligations. Rewrite `hc` using `[pow_succ, mul_smul]`. Take `⟨d, hd, hdc⟩` from `(mem_pow_smul_iff f a _ _).mp hc`. Use `h a (c - d) (by simp [smul_sub, Finset.sum_sub_distrib, hdc]) α` as an intermediate fact. Simplify using `using Submodule.add_mem _ this (hd α)`.
-/
theorem isQuasiRegularSeq_iff_eq_zero (f : ι → R) :
    IsQuasiRegularSeq M f ↔ ∀ (a : ℕ) (c : MonoDeg ι a → M), ∑ α, monoVal f α.1 • c α = 0 →
      ∀ α, c α ∈ (Ideal.span (Set.range f) • ⊤ : Submodule R M) := by
  refine ⟨fun h a c hc => h a c (by rw [hc]; exact zero_mem _), fun h a c hc α => ?_⟩
  rw [pow_succ, mul_smul] at hc
  obtain ⟨d, hd, hdc⟩ := (mem_pow_smul_iff f a _ _).mp hc
  have := h a (c - d) (by simp [smul_sub, Finset.sum_sub_distrib, hdc]) α
  simpa using Submodule.add_mem _ this (hd α)

end Split

section Step

variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
variable {M : Type*} [AddCommGroup M] [Module R M]

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero => simp`. Consider the case `succ a ih`. Take `⟨c, rfl⟩` from `(mem_pow_smul_top_iff f a m).mp (ih (powGr.pow_succ_smul_le _ M a hm))`. Use `sum_monoVal_smul_mem_pow_succ f fun α => ?_` and prove the remaining obligations.

Use `h a (fun α => x • c α) (by` as an intermediate fact. Simplify `hm) α` using `only [Finset.smul_sum, smul_comm x]`. Rewrite `this`, the goal using `[← Submodule.Quotient.mk_eq_zero]`. Conclude with `hx.right_eq_zero_of_smul this`.
-/
private theorem mem_pow_of_regular {f : ι → R} (h : IsQuasiRegularSeq M f) {x : R}
    (hx : IsSMulRegular (M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)) x) (a : ℕ) (m : M)
    (hm : x • m ∈ (Ideal.span (Set.range f) ^ a • ⊤ : Submodule R M)) :
    m ∈ (Ideal.span (Set.range f) ^ a • ⊤ : Submodule R M) := by
  induction a with
  | zero => simp
  | succ a ih =>
    obtain ⟨c, rfl⟩ := (mem_pow_smul_top_iff f a m).mp (ih (powGr.pow_succ_smul_le _ M a hm))
    refine sum_monoVal_smul_mem_pow_succ f fun α => ?_
    have := h a (fun α => x • c α) (by
      simpa only [Finset.smul_sum, smul_comm x] using hm) α
    rw [← Submodule.Quotient.mk_eq_zero] at this ⊢
    exact hx.right_eq_zero_of_smul this

/- English proof (translation)
Establish `hJI : Ideal.span (Set.range (f ∘ some)) ≤ Ideal.span (Set.range f)` using `Ideal.span_mono (Set.range_comp_subset_range _ _)`. Introduce `a`. Proceed by induction on `a with`. Consider the case `zero`. Introduce `c hc α`.

Establish `hs : ∀ β : MonoDeg (Option ι) 0, β.1 = 0` using `fun β => (Finsupp.degree_eq_zero_iff _).mp β.2`. Rewrite `hc` using `[Finset.sum_eq_single α (fun β _ hβ => absurd (Subtype.ext ((hs β).trans (hs α).symm)) hβ) (by simp), hs α]`. Simplify using `using hc`. Consider the case `succ a ih`. It suffices to establish `key : ∀ c : MonoDeg (Option ι) (a + 1) → M, ∑ α, monoVal f α.1 • c α = 0 → ∀ α, c α ∈ (Ideal.span (Set.range f) • ⊤ : Submodule R M) by`.

Introduce `c hc α`. Rewrite `hc` using `[pow_succ, mul_smul]`. Take `⟨d, hd, hdc⟩` from `(mem_pow_smul_iff f _ _ _).mp hc`. Use `key (c - d) (by simp [smul_sub, Finset.sum_sub_distrib, hdc]) α` as an intermediate fact. Simplify using `using Submodule.add_mem _ this (hd α)`.

Introduce `c hc α`. Rewrite `hc` using `[sum_monoVal_smul_option]`. Establish `hH : ∑ γ : MonoDeg (Option ι) a, monoVal f γ.1 • c (MonoDeg.mulVar none γ) ∈ (Ideal.span (Set.range (f ∘ some)) ^ (a + 1) • ⊤ : Submodule R M)`. Use `mem_pow_of_regular h hx _ _ ?_` and prove the remaining obligations. Rewrite using `[eq_neg_of_add_eq_zero_right hc, neg_mem_iff]`.

Conclude with `(mem_pow_smul_top_iff _ _ _).mpr ⟨_, rfl⟩`. Take `⟨β | γ, rfl⟩` from `(MonoDeg.optionEquiv ι a).surjective α`. Take `⟨d, hd⟩` from `(mem_pow_smul_top_iff _ _ _).mp hH`. Use `(isQuasiRegularSeq_iff_eq_zero _).mp h (a + 1) (fun β => c β.toOption + f none • d β) (by` as an intermediate fact. Rewrite using `[← hc, ← hd, Finset.smul_sum, ← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl fun β _ => by rw [smul_add, smul_comm (f none)]) β`. Conclude with `(Submodule.add_mem_iff_left _ (Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_range_self none)) Submodule.mem_top)).mp (Submodule.smul_mono_left hJI this)`. Conclude with `ih (fun γ => c (MonoDeg.mulVar none γ)) (Submodule.smul_mono_left (Ideal.pow_right_mono hJI _) hH) γ`.
-/
theorem IsQuasiRegularSeq.option {f : Option ι → R} (h : IsQuasiRegularSeq M (f ∘ some))
    (hx : IsSMulRegular (M ⧸ (Ideal.span (Set.range (f ∘ some)) • ⊤ : Submodule R M)) (f none)) :
    IsQuasiRegularSeq M f := by
  have hJI : Ideal.span (Set.range (f ∘ some)) ≤ Ideal.span (Set.range f) :=
    Ideal.span_mono (Set.range_comp_subset_range _ _)
  intro a
  induction a with
  | zero =>
    intro c hc α
    have hs : ∀ β : MonoDeg (Option ι) 0, β.1 = 0 := fun β =>
      (Finsupp.degree_eq_zero_iff _).mp β.2
    rw [Finset.sum_eq_single α (fun β _ hβ => absurd (Subtype.ext ((hs β).trans (hs α).symm)) hβ)
      (by simp), hs α] at hc
    simpa using hc
  | succ a ih =>
    suffices key : ∀ c : MonoDeg (Option ι) (a + 1) → M, ∑ α, monoVal f α.1 • c α = 0 →
        ∀ α, c α ∈ (Ideal.span (Set.range f) • ⊤ : Submodule R M) by
      intro c hc α
      rw [pow_succ, mul_smul] at hc
      obtain ⟨d, hd, hdc⟩ := (mem_pow_smul_iff f _ _ _).mp hc
      have := key (c - d) (by simp [smul_sub, Finset.sum_sub_distrib, hdc]) α
      simpa using Submodule.add_mem _ this (hd α)
    intro c hc α
    rw [sum_monoVal_smul_option] at hc
    have hH : ∑ γ : MonoDeg (Option ι) a, monoVal f γ.1 • c (MonoDeg.mulVar none γ) ∈
        (Ideal.span (Set.range (f ∘ some)) ^ (a + 1) • ⊤ : Submodule R M) := by
      refine mem_pow_of_regular h hx _ _ ?_
      rw [eq_neg_of_add_eq_zero_right hc, neg_mem_iff]
      exact (mem_pow_smul_top_iff _ _ _).mpr ⟨_, rfl⟩
    obtain ⟨β | γ, rfl⟩ := (MonoDeg.optionEquiv ι a).surjective α
    · obtain ⟨d, hd⟩ := (mem_pow_smul_top_iff _ _ _).mp hH
      have := (isQuasiRegularSeq_iff_eq_zero _).mp h (a + 1)
        (fun β => c β.toOption + f none • d β) (by
          rw [← hc, ← hd, Finset.smul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun β _ => by rw [smul_add, smul_comm (f none)]) β
      exact (Submodule.add_mem_iff_left _
        (Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_range_self none))
          Submodule.mem_top)).mp
          (Submodule.smul_mono_left hJI this)
    · exact ih (fun γ => c (MonoDeg.mulVar none γ))
        (Submodule.smul_mono_left (Ideal.pow_right_mono hJI _) hH) γ

/- English proof (translation)
Take `⟨c, rfl⟩` from `(mem_pow_smul_top_iff f a m).mp hm`. Use `sum_monoVal_smul_mem_pow_succ f fun γ => ?_` and prove the remaining obligations. Establish `hinj` using `MonoDeg.mulVar_injective i a`. Use `h (a + 1) (Function.extend (MonoDeg.mulVar i) c 0) (by` as an intermediate fact. Rewrite using `[← Fintype.sum_of_injective _ hinj (fun γ => f i • monoVal f γ.1 • c γ)]`.

Rewrite `hfm` using `[Finset.smul_sum]`. Then use the resulting hypothesis. Introduce `α hα`. Rewrite using `[Function.extend_apply' _ _ _ hα]`. Simplify using the standard rewrite rules. Introduce `γ`.

Rewrite using `[hinj.extend_apply, monoVal_mulVar, mul_smul]) (MonoDeg.mulVar i γ)`. Rewrite `this` using `[hinj.extend_apply]`. Then use the resulting hypothesis.
-/
theorem IsQuasiRegularSeq.mem_pow_succ_smul_of_smul_mem {f : ι → R} (h : IsQuasiRegularSeq M f)
    (i : ι) {a : ℕ} {m : M} (hm : m ∈ (Ideal.span (Set.range f) ^ a • ⊤ : Submodule R M))
    (hfm : f i • m ∈ (Ideal.span (Set.range f) ^ (a + 2) • ⊤ : Submodule R M)) :
    m ∈ (Ideal.span (Set.range f) ^ (a + 1) • ⊤ : Submodule R M) := by
  obtain ⟨c, rfl⟩ := (mem_pow_smul_top_iff f a m).mp hm
  refine sum_monoVal_smul_mem_pow_succ f fun γ => ?_
  have hinj := MonoDeg.mulVar_injective i a
  have := h (a + 1) (Function.extend (MonoDeg.mulVar i) c 0) (by
    rw [← Fintype.sum_of_injective _ hinj (fun γ => f i • monoVal f γ.1 • c γ)]
    · rwa [Finset.smul_sum] at hfm
    · intro α hα
      rw [Function.extend_apply' _ _ _ hα]
      simp
    · intro γ
      rw [hinj.extend_apply, monoVal_mulVar, mul_smul]) (MonoDeg.mulVar i γ)
  rwa [hinj.extend_apply] at this

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero => simp`. Consider the case `succ a ih`. Conclude with `h.mem_pow_succ_smul_of_smul_mem i (ih (powGr.pow_succ_smul_le _ M _ hfm)) hfm`.
-/
theorem IsQuasiRegularSeq.mem_pow_smul_of_smul_mem {f : ι → R} (h : IsQuasiRegularSeq M f)
    (i : ι) {a : ℕ} {m : M}
    (hfm : f i • m ∈ (Ideal.span (Set.range f) ^ (a + 1) • ⊤ : Submodule R M)) :
    m ∈ (Ideal.span (Set.range f) ^ a • ⊤ : Submodule R M) := by
  induction a with
  | zero => simp
  | succ a ih =>
    exact h.mem_pow_succ_smul_of_smul_mem i (ih (powGr.pow_succ_smul_le _ M _ hfm)) hfm

/- English proof (translation)
Use `.of_right_eq_zero_of_smul fun m hm => ?_` and prove the remaining obligations. Rewrite using `[← Submodule.mem_bot R, ← hsep, Submodule.mem_iInf]`. Conclude with `fun a => h.mem_pow_smul_of_smul_mem i (by rw [hm]; exact zero_mem _)`.
-/
theorem IsQuasiRegularSeq.isSMulRegular_of_iInf_eq_bot {f : ι → R} (h : IsQuasiRegularSeq M f)
    (hsep : (⨅ a : ℕ, Ideal.span (Set.range f) ^ a • ⊤ : Submodule R M) = ⊥) (i : ι) :
    IsSMulRegular M (f i) := by
  refine .of_right_eq_zero_of_smul fun m hm => ?_
  rw [← Submodule.mem_bot R, ← hsep, Submodule.mem_iInf]
  exact fun a => h.mem_pow_smul_of_smul_mem i (by rw [hm]; exact zero_mem _)

/- English proof (translation)
Establish `hJI : Ideal.span (Set.range (f ∘ some)) ≤ Ideal.span (Set.range f)` using `Ideal.span_mono (Set.range_comp_subset_range _ _)`. Establish `hI : ∀ m : M, m ∈ (Ideal.span (Set.range f) • ⊤ : Submodule R M) → (Submodule.Quotient.mk m : QuotSMulTop (f none) M) ∈ (Ideal.span (Set.range (f ∘ some)) • ⊤ : Submodule R (QuotSMulTop (f none) M))`. Introduce `m hm`. Use `Submodule.smul_induction_on hm ?_ ?_` and prove the remaining obligations. Introduce `r hr n _`.

Rewrite using `[Submodule.Quotient.mk_smul]`. Proceed by induction on `hr using Submodule.span_induction with`. Consider the case `mem r hr`. Take `⟨_ | i, rfl⟩` from `hr`. Rewrite using `[← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)]`.

Conclude with `zero_mem _`. Conclude with `Submodule.smul_mem_smul (Ideal.subset_span ⟨i, rfl⟩) trivial`. Consider the case `zero => simp`. Consider the case `add r s _ _ hr hs => rw [add_smul]`. Conclude with `add_mem hr hs`.

Consider the case `smul t r _ hr => rw [smul_assoc]`. Conclude with `Submodule.smul_mem _ _ hr`. Introduce `x y hx hy`. Rewrite using `[Submodule.Quotient.mk_add]`. Conclude with `add_mem hx hy`.

Rewrite using `[isQuasiRegularSeq_iff_eq_zero]`. Introduce `a c hc β`. Use `choose d hd using fun α => Submodule.Quotient.mk_surjective _ (c α)`. Take `rfl : c = fun α => Submodule.Quotient.mk (d α)` from `funext fun α => (hd α).symm`. Establish `hc' : (Submodule.Quotient.mk (∑ α, monoVal (f ∘ some) α.1 • d α) : QuotSMulTop (f none) M) = 0`.

Rewrite using `[← hc, ← Submodule.mkQ_apply, map_sum]`. Both sides reduce to the same expression. Take `⟨ω, -, hω⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).mp ((Submodule.Quotient.mk_eq_zero _).mp hc')`. Consider the cases of `a with`. Consider the case `zero`.

Establish `hs : ∀ β : MonoDeg ι 0, β.1 = 0` using `fun β => (Finsupp.degree_eq_zero_iff _).mp β.2`. Rewrite `hc` using `[Finset.sum_eq_single β (fun γ _ hγ => absurd (Subtype.ext ((hs γ).trans (hs β).symm)) hγ) (by simp), hs β, monoVal_zero, one_smul]`. Rewrite using `[hc]`. Conclude with `zero_mem _`. Consider the case `succ a`.

Establish `h1 : ω ∈ (Ideal.span (Set.range f) ^ a • ⊤ : Submodule R M)`. Use `h.mem_pow_smul_of_smul_mem none ?_` and prove the remaining obligations. Rewrite using `[hω]`. Conclude with `Submodule.smul_mono_left (Ideal.pow_right_mono hJI _) ((mem_pow_smul_top_iff _ _ _).mpr ⟨_, rfl⟩)`. Take `⟨g, rfl⟩` from `(mem_pow_smul_top_iff f a ω).mp h1`.

Set `e` to `MonoDeg.optionEquiv ι a`. Establish `he₁ : ∀ β : MonoDeg ι (a + 1), e.symm β.toOption = Sum.inl β` using `fun β => e.symm_apply_apply (Sum.inl β)`. Establish `he₂ : ∀ γ : MonoDeg (Option ι) a, e.symm (MonoDeg.mulVar none γ) = Sum.inr γ` using `fun γ => e.symm_apply_apply (Sum.inr γ)`. Use `(isQuasiRegularSeq_iff_eq_zero f).mp h (a + 1) (fun α => Sum.elim d (-g) (e.symm α)) (by` as an intermediate fact. Rewrite using `[sum_monoVal_smul_option]`.

Simplify using `only [he₁, he₂, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, smul_neg, Finset.sum_neg_distrib, hω, add_neg_cancel]) β.toOption`. Rewrite `this` using `[he₁]`. Conclude with `hI _ this`.
-/
theorem IsQuasiRegularSeq.quotSMulTop {f : Option ι → R} (h : IsQuasiRegularSeq M f) :
    IsQuasiRegularSeq (QuotSMulTop (f none) M) (f ∘ some) := by
  have hJI : Ideal.span (Set.range (f ∘ some)) ≤ Ideal.span (Set.range f) :=
    Ideal.span_mono (Set.range_comp_subset_range _ _)
  have hI : ∀ m : M, m ∈ (Ideal.span (Set.range f) • ⊤ : Submodule R M) →
      (Submodule.Quotient.mk m : QuotSMulTop (f none) M) ∈
        (Ideal.span (Set.range (f ∘ some)) • ⊤ : Submodule R (QuotSMulTop (f none) M)) := by
    intro m hm
    refine Submodule.smul_induction_on hm ?_ ?_
    · intro r hr n _
      rw [Submodule.Quotient.mk_smul]
      induction hr using Submodule.span_induction with
      | mem r hr =>
        obtain ⟨_ | i, rfl⟩ := hr
        · rw [← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero _).mpr
            (Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)]
          exact zero_mem _
        · exact Submodule.smul_mem_smul (Ideal.subset_span ⟨i, rfl⟩) trivial
      | zero => simp
      | add r s _ _ hr hs => rw [add_smul]; exact add_mem hr hs
      | smul t r _ hr => rw [smul_assoc]; exact Submodule.smul_mem _ _ hr
    · intro x y hx hy
      rw [Submodule.Quotient.mk_add]
      exact add_mem hx hy
  rw [isQuasiRegularSeq_iff_eq_zero]
  intro a c hc β
  choose d hd using fun α => Submodule.Quotient.mk_surjective _ (c α)
  obtain rfl : c = fun α => Submodule.Quotient.mk (d α) := funext fun α => (hd α).symm
  have hc' : (Submodule.Quotient.mk (∑ α, monoVal (f ∘ some) α.1 • d α) :
      QuotSMulTop (f none) M) = 0 := by
    rw [← hc, ← Submodule.mkQ_apply, map_sum]
    rfl
  obtain ⟨ω, -, hω⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp
    ((Submodule.Quotient.mk_eq_zero _).mp hc')
  cases a with
  | zero =>
    have hs : ∀ β : MonoDeg ι 0, β.1 = 0 := fun β => (Finsupp.degree_eq_zero_iff _).mp β.2
    rw [Finset.sum_eq_single β (fun γ _ hγ => absurd (Subtype.ext ((hs γ).trans (hs β).symm)) hγ)
      (by simp), hs β, monoVal_zero, one_smul] at hc
    rw [hc]
    exact zero_mem _
  | succ a =>
    have h1 : ω ∈ (Ideal.span (Set.range f) ^ a • ⊤ : Submodule R M) := by
      refine h.mem_pow_smul_of_smul_mem none ?_
      rw [hω]
      exact Submodule.smul_mono_left (Ideal.pow_right_mono hJI _)
        ((mem_pow_smul_top_iff _ _ _).mpr ⟨_, rfl⟩)
    obtain ⟨g, rfl⟩ := (mem_pow_smul_top_iff f a ω).mp h1
    let e := MonoDeg.optionEquiv ι a
    have he₁ : ∀ β : MonoDeg ι (a + 1), e.symm β.toOption = Sum.inl β :=
      fun β => e.symm_apply_apply (Sum.inl β)
    have he₂ : ∀ γ : MonoDeg (Option ι) a, e.symm (MonoDeg.mulVar none γ) = Sum.inr γ :=
      fun γ => e.symm_apply_apply (Sum.inr γ)
    have := (isQuasiRegularSeq_iff_eq_zero f).mp h (a + 1) (fun α => Sum.elim d (-g) (e.symm α))
      (by
        rw [sum_monoVal_smul_option]
        simp only [he₁, he₂, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, smul_neg,
          Finset.sum_neg_distrib, hω, add_neg_cancel]) β.toOption
    rw [he₁] at this
    exact hI _ this

end Step

section Main

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/- English proof (translation)
Rewrite using `[Ideal.ofList]`. Use `congr 1`. Use extensionality with `x`. Simplify using `[List.mem_ofFn']`.
-/
theorem ofList_ofFn_eq_span_range {n : ℕ} (f : Fin n → R) :
    Ideal.ofList (List.ofFn f) = Ideal.span (Set.range f) := by
  rw [Ideal.ofList]
  congr 1
  ext x
  simp [List.mem_ofFn']

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `a c hc α`. Establish `hs : ∀ β : MonoDeg (Fin 0) a, β.1 = 0` using `fun β => Subsingleton.elim _ _`. Take `rfl : a = 0` from `by rw [← α.2, hs α, map_zero]`.

Rewrite `hc` using `[Finset.sum_eq_single α (fun β _ hβ => absurd (Subtype.ext ((hs β).trans (hs α).symm)) hβ) (by simp), hs α]`. Simplify using `using hc`. Consider the case `succ n ih`. Rewrite `h` using `[List.ofFn_succ', List.concat_eq_append, isWeaklyRegular_append_iff, isWeaklyRegular_singleton_iff, ofList_ofFn_eq_span_range]`. Rewrite using `[← isQuasiRegularSeq_comp_equiv_iff f finSuccEquivLast.symm]`.

Establish `h1 : (f ∘ finSuccEquivLast.symm) ∘ some = fun i : Fin n => f i.castSucc`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Establish `h2 : (f ∘ finSuccEquivLast.symm) none = f (Fin.last n)` using `by simp`. Use `IsQuasiRegularSeq.option (f := f ∘ finSuccEquivLast.symm) ?_ ?_` and prove the remaining obligations.

Rewrite using `[h1]`. Conclude with `ih h.1`. Rewrite using `[h1, h2]`. Conclude with `h.2`.
-/
theorem isQuasiRegularSeq_of_isWeaklyRegular {n : ℕ} {f : Fin n → R}
    (h : IsWeaklyRegular M (List.ofFn f)) : IsQuasiRegularSeq M f := by
  induction n with
  | zero =>
    intro a c hc α
    have hs : ∀ β : MonoDeg (Fin 0) a, β.1 = 0 := fun β => Subsingleton.elim _ _
    obtain rfl : a = 0 := by rw [← α.2, hs α, map_zero]
    rw [Finset.sum_eq_single α (fun β _ hβ => absurd (Subtype.ext ((hs β).trans (hs α).symm)) hβ)
      (by simp), hs α] at hc
    simpa using hc
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, isWeaklyRegular_append_iff,
      isWeaklyRegular_singleton_iff, ofList_ofFn_eq_span_range] at h
    rw [← isQuasiRegularSeq_comp_equiv_iff f finSuccEquivLast.symm]
    have h1 : (f ∘ finSuccEquivLast.symm) ∘ some = fun i : Fin n => f i.castSucc := by
      funext i
      simp
    have h2 : (f ∘ finSuccEquivLast.symm) none = f (Fin.last n) := by simp
    refine IsQuasiRegularSeq.option (f := f ∘ finSuccEquivLast.symm) ?_ ?_
    · rw [h1]
      exact ih h.1
    · rw [h1, h2]
      exact h.2

/- English proof (translation)
The claim follows from `isQuasiRegularSeq_of_isWeaklyRegular (by rwa [List.ofFn_get])`.
-/
theorem isQuasiRegularSeq_get_of_isWeaklyRegular {rs : List R} (h : IsWeaklyRegular M rs) :
    IsQuasiRegularSeq M rs.get :=
  isQuasiRegularSeq_of_isWeaklyRegular (by rwa [List.ofFn_get])

/- English proof (translation)
The claim follows from `isQuasiRegularSeq_of_isWeaklyRegular h.toIsWeaklyRegular`.
-/
theorem isQuasiRegularSeq_of_isRegular {n : ℕ} {f : Fin n → R}
    (h : RingTheory.Sequence.IsRegular M (List.ofFn f)) : IsQuasiRegularSeq M f :=
  isQuasiRegularSeq_of_isWeaklyRegular h.toIsWeaklyRegular

/- English proof (translation)
The claim follows from `(h.comp_equiv (finSuccEquiv n).symm).quotSMulTop`.
-/
theorem IsQuasiRegularSeq.quotSMulTop_tail {n : ℕ} {f : Fin (n + 1) → R}
    (h : IsQuasiRegularSeq M f) :
    IsQuasiRegularSeq (QuotSMulTop (f 0) M) fun i : Fin n => f i.succ :=
  (h.comp_equiv (finSuccEquiv n).symm).quotSMulTop

/- English proof (translation)
Proceed by induction on `n generalizing M with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[List.ofFn_succ, isWeaklyRegular_cons_iff]`. Use `⟨h.isSMulRegular_of_iInf_eq_bot (Ideal.iInf_pow_smul_eq_bot_of_le_jacobson _ ?_) 0, ih h.quotSMulTop_tail fun i => hf _⟩` and prove the remaining obligations.

Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hf i`.
-/
theorem IsQuasiRegularSeq.isWeaklyRegular [IsNoetherianRing R] [Module.Finite R M] {n : ℕ}
    {f : Fin n → R} (h : IsQuasiRegularSeq M f) (hf : ∀ i, f i ∈ (⊥ : Ideal R).jacobson) :
    IsWeaklyRegular M (List.ofFn f) := by
  induction n generalizing M with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, isWeaklyRegular_cons_iff]
    refine ⟨h.isSMulRegular_of_iInf_eq_bot (Ideal.iInf_pow_smul_eq_bot_of_le_jacobson _ ?_) 0,
      ih h.quotSMulTop_tail fun i => hf _⟩
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hf i

/- English proof (translation)
The claim follows from `isQuasiRegularSeq_of_isWeaklyRegular (by simpa using IsSMulRegular.of_ne_zero (M := ℤ) (two_ne_zero (α := ℤ)))`.
-/
example : IsQuasiRegularSeq ℤ ![(2 : ℤ)] :=
  isQuasiRegularSeq_of_isWeaklyRegular (by
    simpa using IsSMulRegular.of_ne_zero (M := ℤ) (two_ne_zero (α := ℤ)))

end Main

end GlobalTheory
