import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.SchurChar

section Basic

variable {V : Type} [TopologicalSpace V]

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1.add h'.1, h.2.add h'.2⟩`.
-/
theorem sb_add {φ φ' : V → ℂ} (h : SB φ) (h' : SB φ') : SB (φ + φ') :=
  ⟨h.1.add h'.1, h.2.add h'.2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨hm.mul h.1, h.2.mul_left⟩`.
-/
theorem sb_mul {m φ : V → ℂ} (hm : IsLocallyConstant m) (h : SB φ) :
    SB (fun u => m u * φ u) :=
  ⟨hm.mul h.1, h.2.mul_left⟩

/- English proof (translation)
The claim follows from `sb_mul (m := fun _ => c) (IsLocallyConstant.const c) h`.
-/
theorem sb_smul (c : ℂ) {φ : V → ℂ} (h : SB φ) : SB (c • φ) :=
  sb_mul (m := fun _ => c) (IsLocallyConstant.const c) h

def Comm (T : (V → ℂ) → (V → ℂ)) (m : V → ℂ) : Prop :=
  IsLocallyConstant m ∧ ∀ φ, SB φ → T (fun u => m u * φ u) = fun u => m u * T φ u

/- English proof (translation)
Assemble the required witnesses or components as `⟨IsLocallyConstant.const 1, fun φ _ => by simp⟩`.
-/
theorem comm_one (T : (V → ℂ) → (V → ℂ)) : Comm T (fun _ => 1) :=
  ⟨IsLocallyConstant.const 1, fun φ _ => by simp⟩

/- English proof (translation)
Use `⟨h.1.mul h'.1, fun φ hφ => ?_⟩` and prove the remaining obligations. Establish `e : (fun u => m u * m' u * φ u) = fun u => m u * (m' u * φ u)`. Use function extensionality and compare the values at `u`. Conclude with `mul_assoc _ _ _`. Rewrite using `[e, h.2 _ (sb_mul h'.1 hφ), h'.2 φ hφ]`.

Use function extensionality and compare the values at `u`. Conclude with `(mul_assoc _ _ _).symm`.
-/
theorem comm_mul {T : (V → ℂ) → (V → ℂ)} {m m' : V → ℂ} (h : Comm T m) (h' : Comm T m') :
    Comm T (fun u => m u * m' u) := by
  refine ⟨h.1.mul h'.1, fun φ hφ => ?_⟩
  have e : (fun u => m u * m' u * φ u) = fun u => m u * (m' u * φ u) := by
    funext u; exact mul_assoc _ _ _
  rw [e, h.2 _ (sb_mul h'.1 hφ), h'.2 φ hφ]
  funext u; exact (mul_assoc _ _ _).symm

/- English proof (translation)
Use `⟨h.1.sub (IsLocallyConstant.const c), fun φ hφ => ?_⟩` and prove the remaining obligations. Establish `e : (fun u => (f u - c) * φ u) = (fun u => f u * φ u) + (-c) • φ`. Use function extensionality and compare the values at `u`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, hadd _ _ (sb_mul h.1 hφ) (sb_smul _ hφ), hsmul _ _ hφ, h.2 φ hφ]`. Use function extensionality and compare the values at `u`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem comm_sub_const {T : (V → ℂ) → (V → ℂ)}
    (hadd : ∀ φ φ', SB φ → SB φ' → T (φ + φ') = T φ + T φ')
    (hsmul : ∀ (c : ℂ) φ, SB φ → T (c • φ) = c • T φ)
    {f : V → ℂ} (h : Comm T f) (c : ℂ) : Comm T (fun u => f u - c) := by
  refine ⟨h.1.sub (IsLocallyConstant.const c), fun φ hφ => ?_⟩
  have e : (fun u => (f u - c) * φ u) = (fun u => f u * φ u) + (-c) • φ := by
    funext u; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [e, hadd _ _ (sb_mul h.1 hφ) (sb_smul _ hφ), hsmul _ _ hφ, h.2 φ hφ]
  funext u; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

end Basic

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
  {χ : V → V → ℂ} {μ : Measure V}

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, -, -, -, hnorm, hadd, -⟩` from `h`. Establish `h1` using `hadd 0 0 y`. Rewrite `h1` using `[add_zero]`. Establish `h2 : χ 0 y ≠ 0`. Introduce `h0`.

Use `hnorm 0 y` as an intermediate fact. Rewrite `this` using `[h0]`. Simplify using `at this`. Conclude with `(mul_eq_left₀ h2).mp h1.symm`.
-/
theorem char_zero (h : NADual V χ μ) (y : V) : χ 0 y = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hnorm, hadd, -⟩ := h
  have h1 := hadd 0 0 y
  rw [add_zero] at h1
  have h2 : χ 0 y ≠ 0 := by
    intro h0; have := hnorm 0 y; rw [h0] at this; simp at this
  exact (mul_eq_left₀ h2).mp h1.symm

/- English proof (translation)
Establish `h0` using `char_zero h`. Take `⟨hTG, -, -, -, -, -, -, hcover, -, hsymm, -, hadd, hperp⟩` from `h`. Use `haveI := hTG`. Take `⟨L, hLc, hLo, hy⟩` from `hcover y`. Take `⟨-, hPo, -, -⟩` from `hperp L hLc hLo`.

Establish `h0P : (0 : V) ∈ perp χ L` using `fun x _ => by rw [hsymm]; exact h0 x`. Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `u`. Use `⟨(fun v => v - u) ⁻¹' perp χ L, hPo.preimage (continuous_sub_right u), by simpa using h0P, ?_⟩` and prove the remaining obligations. Introduce `v hv`.

Establish `h1 : χ (v - u) y = 1` using `by rw [hsymm]; exact hv y hy`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem char_locConst (h : NADual V χ μ) (y : V) : IsLocallyConstant (fun u => χ u y) := by
  have h0 := char_zero h
  obtain ⟨hTG, -, -, -, -, -, -, hcover, -, hsymm, -, hadd, hperp⟩ := h
  haveI := hTG
  obtain ⟨L, hLc, hLo, hy⟩ := hcover y
  obtain ⟨-, hPo, -, -⟩ := hperp L hLc hLo
  have h0P : (0 : V) ∈ perp χ L := fun x _ => by rw [hsymm]; exact h0 x
  rw [IsLocallyConstant.iff_exists_open]
  intro u
  refine ⟨(fun v => v - u) ⁻¹' perp χ L, hPo.preimage (continuous_sub_right u), by simpa using h0P, ?_⟩
  intro v hv
  have h1 : χ (v - u) y = 1 := by rw [hsymm]; exact hv y hy
  calc χ v y = χ ((v - u) + u) y := by simp
    _ = χ u y := by rw [hadd, h1, one_mul]

/- English proof (translation)
Establish `hcomm : ∀ y, Comm T (fun u => χ u y)` using `fun y => ⟨char_locConst h y, fun φ hφ => hchar y φ hφ⟩`. Take `⟨hTG, -, -, -, -, -, hsmall, -, -, hsymm, hnorm, hχadd, hperp⟩` from `h`. Use `haveI := hTG`. Establish `hS : IsCompact (tsupport φ)` using `hφ.2`. Establish `hxS : x ∉ tsupport φ`.

Rewrite using `[notMem_tsupport_iff_eventuallyEq]`. Use `filter_upwards [hφ.1.eventually_eq x] with u hu`. Simplify using `[hu, hx]`. Establish `hnb : {w : V | x + w ∈ (tsupport φ)ᶜ} ∈ 𝓝 (0 : V)`. Establish `hc : ContinuousAt (fun w : V => x + w) 0` using `by fun_prop`.

Apply `hc.preimage_mem_nhds` to reduce the goal to its premises. Simplify using `using (isClosed_tsupport φ).isOpen_compl.mem_nhds hxS`. Take `⟨L, hLc, hLo, hLU⟩` from `hsmall _ hnb`. Take `⟨-, -, hpp, -⟩` from `hperp L hLc hLo`. Establish `key : ∃ m, Comm T m ∧ m x ≠ 0 ∧ ∀ u ∈ tsupport φ, m u = 0`.

Use `hS.induction_on (p := fun A => ∃ m, Comm T m ∧ m x ≠ 0 ∧ ∀ u ∈ A, m u = 0) ?_ ?_ ?_ ?_` and prove the remaining obligations. Conclude with `⟨fun _ => 1, comm_one T, one_ne_zero, by simp⟩`. Introduce and unpack `A B hAB ⟨m, hm, hmx, hm0⟩`. Conclude with `⟨m, hm, hmx, fun u hu => hm0 u (hAB hu)⟩`. Introduce and unpack `A B ⟨m, hm, hmx, hm0⟩ ⟨m', hm', hmx', hm0'⟩`.

Use `⟨_, comm_mul hm hm', mul_ne_zero hmx hmx', ?_⟩` and prove the remaining obligations. Introduce and unpack `u (hu | hu)`. Simplify using `[hm0 u hu]`. Simplify using `[hm0' u hu]`. Introduce `s hs`.

Establish `hsL : s - x ∉ (L : Set V)`. Introduce `hmem`. Use `hLU hmem` as an intermediate fact. Simplify using `only [Set.mem_setOf_eq, Set.mem_compl_iff, add_sub_cancel] at this`. Conclude with `this hs`.

Establish `hz : ∃ z ∈ perp χ L, χ z (s - x) ≠ 1`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hsL (hpp fun z hz => hcon z hz)`. Take `⟨z, hzL, hzne⟩` from `hz`.

Establish `hzne' : χ (s - x) z ≠ 1` using `by rwa [hsymm]`. Establish `hxz : χ x z ≠ 0`. Introduce `h0`. Use `hnorm x z` as an intermediate fact. Rewrite `this` using `[h0]`.

Simplify using `at this`. Establish `hopen : {u : V | u - s ∈ (L : Set V)} ∈ 𝓝 s`. Establish `hc : ContinuousAt (fun u : V => u - s) s` using `by fun_prop`. Apply `hc.preimage_mem_nhds` to reduce the goal to its premises. Simplify using `using hLo.mem_nhds L.zero_mem`.

Use `⟨{u : V | u - s ∈ (L : Set V)}, mem_nhdsWithin_of_mem_nhds hopen, fun u => χ u z - χ s z, comm_sub_const hadd hsmul (hcomm z) _, ?_, ?_⟩` and prove the remaining obligations. Introduce `hzero`. Apply `hzne'` to reduce the goal to its premises. Establish `e : χ s z = χ (s - x) z * χ x z`. Rewrite using `[← hχadd]`.

Simplify using the standard rewrite rules. Establish `e2 : χ x z = χ (s - x) z * χ x z`. Rewrite using `[← e]`. Conclude with `sub_eq_zero.mp hzero`. Conclude with `(mul_eq_right₀ hxz).mp e2.symm`.

Introduce `u hu`. Establish `h1 : χ (u - s) z = 1` using `hzL _ hu`. Establish `e : χ u z = χ (u - s) z * χ s z`. Rewrite using `[← hχadd]`. Simplify using the standard rewrite rules.

Use `show χ u z - χ s z = 0`. Rewrite using `[e, h1, one_mul, sub_self]`. Take `⟨m, hm, hmx, hm0⟩` from `key`. Establish `e : (fun u => m u * φ u) = (0 : ℂ) • φ`. Use function extensionality and compare the values at `u`.

Distinguish the cases in `hu : u ∈ tsupport φ`. Simplify using `[hm0 u hu]`. Simplify using `[image_eq_zero_of_notMem_tsupport hu]`. Establish `h2` using `hm.2 φ hφ`. Rewrite `h2` using `[e, hsmul 0 φ hφ]`.

Establish `h3` using `congrFun h2 x`. Simplify using `only [Pi.smul_apply, Pi.zero_apply, zero_smul, smul_eq_mul, zero_mul] at h3`. Conclude with `(mul_eq_zero.mp h3.symm).resolve_left hmx`.
-/
theorem apply_eq_zero (h : NADual V χ μ) {T : (V → ℂ) → (V → ℂ)}
    (hadd : ∀ φ φ', SB φ → SB φ' → T (φ + φ') = T φ + T φ')
    (hsmul : ∀ (c : ℂ) φ, SB φ → T (c • φ) = c • T φ)
    (hchar : ∀ y φ, SB φ → T (fun u => χ u y * φ u) = fun u => χ u y * T φ u)
    {φ : V → ℂ} (hφ : SB φ) {x : V} (hx : φ x = 0) : T φ x = 0 := by
  have hcomm : ∀ y, Comm T (fun u => χ u y) := fun y => ⟨char_locConst h y, fun φ hφ => hchar y φ hφ⟩
  obtain ⟨hTG, -, -, -, -, -, hsmall, -, -, hsymm, hnorm, hχadd, hperp⟩ := h
  haveI := hTG
  have hS : IsCompact (tsupport φ) := hφ.2
  have hxS : x ∉ tsupport φ := by
    rw [notMem_tsupport_iff_eventuallyEq]
    filter_upwards [hφ.1.eventually_eq x] with u hu
    simp [hu, hx]
  have hnb : {w : V | x + w ∈ (tsupport φ)ᶜ} ∈ 𝓝 (0 : V) := by
    have hc : ContinuousAt (fun w : V => x + w) 0 := by fun_prop
    apply hc.preimage_mem_nhds
    simpa using (isClosed_tsupport φ).isOpen_compl.mem_nhds hxS
  obtain ⟨L, hLc, hLo, hLU⟩ := hsmall _ hnb
  obtain ⟨-, -, hpp, -⟩ := hperp L hLc hLo
  have key : ∃ m, Comm T m ∧ m x ≠ 0 ∧ ∀ u ∈ tsupport φ, m u = 0 := by
    refine hS.induction_on (p := fun A => ∃ m, Comm T m ∧ m x ≠ 0 ∧ ∀ u ∈ A, m u = 0) ?_ ?_ ?_ ?_
    · exact ⟨fun _ => 1, comm_one T, one_ne_zero, by simp⟩
    · rintro A B hAB ⟨m, hm, hmx, hm0⟩
      exact ⟨m, hm, hmx, fun u hu => hm0 u (hAB hu)⟩
    · rintro A B ⟨m, hm, hmx, hm0⟩ ⟨m', hm', hmx', hm0'⟩
      refine ⟨_, comm_mul hm hm', mul_ne_zero hmx hmx', ?_⟩
      rintro u (hu | hu)
      · simp [hm0 u hu]
      · simp [hm0' u hu]
    · intro s hs
      have hsL : s - x ∉ (L : Set V) := by
        intro hmem
        have := hLU hmem
        simp only [Set.mem_setOf_eq, Set.mem_compl_iff, add_sub_cancel] at this
        exact this hs
      have hz : ∃ z ∈ perp χ L, χ z (s - x) ≠ 1 := by
        by_contra hcon
        push_neg at hcon
        exact hsL (hpp fun z hz => hcon z hz)
      obtain ⟨z, hzL, hzne⟩ := hz
      have hzne' : χ (s - x) z ≠ 1 := by rwa [hsymm]
      have hxz : χ x z ≠ 0 := by
        intro h0; have := hnorm x z; rw [h0] at this; simp at this
      have hopen : {u : V | u - s ∈ (L : Set V)} ∈ 𝓝 s := by
        have hc : ContinuousAt (fun u : V => u - s) s := by fun_prop
        apply hc.preimage_mem_nhds
        simpa using hLo.mem_nhds L.zero_mem
      refine ⟨{u : V | u - s ∈ (L : Set V)}, mem_nhdsWithin_of_mem_nhds hopen,
        fun u => χ u z - χ s z, comm_sub_const hadd hsmul (hcomm z) _, ?_, ?_⟩
      · intro hzero
        apply hzne'
        have e : χ s z = χ (s - x) z * χ x z := by
          rw [← hχadd]; simp
        have e2 : χ x z = χ (s - x) z * χ x z := by
          rw [← e]; exact sub_eq_zero.mp hzero
        exact (mul_eq_right₀ hxz).mp e2.symm
      · intro u hu
        have h1 : χ (u - s) z = 1 := hzL _ hu
        have e : χ u z = χ (u - s) z * χ s z := by
          rw [← hχadd]; simp
        show χ u z - χ s z = 0
        rw [e, h1, one_mul, sub_self]
  obtain ⟨m, hm, hmx, hm0⟩ := key
  have e : (fun u => m u * φ u) = (0 : ℂ) • φ := by
    funext u
    by_cases hu : u ∈ tsupport φ
    · simp [hm0 u hu]
    · simp [image_eq_zero_of_notMem_tsupport hu]
  have h2 := hm.2 φ hφ
  rw [e, hsmul 0 φ hφ] at h2
  have h3 := congrFun h2 x
  simp only [Pi.smul_apply, Pi.zero_apply, zero_smul, smul_eq_mul, zero_mul] at h3
  exact (mul_eq_zero.mp h3.symm).resolve_left hmx

/- English proof (translation)
Establish `hloc` using `fun {φ : V → ℂ} (hφ : SB φ) {x : V} (hx : φ x = 0) => apply_eq_zero h hadd hsmul hchar hφ hx`. Take `⟨hTG, hT2, -, -, -, -, -, hcover, -⟩` from `h`. Use `haveI := hTG`. Use `haveI := hT2`. Take `⟨L, hLc, hLo, -⟩` from `hcover 0`.

Use `set φ₀ : V → ℂ := (L : Set V).indicator (fun _ => 1) with hφ₀`. Establish `hφ₀lc : IsLocallyConstant φ₀`. Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `u`. Distinguish the cases in `hu : u ∈ (L : Set V)`.

Conclude with `⟨L, hLo, hu, fun v hv => by`. Rewrite using `[hφ₀, Set.indicator_of_mem hv, Set.indicator_of_mem hu]⟩`. Conclude with `⟨(L : Set V)ᶜ, hLc.isClosed.isOpen_compl, hu, fun v hv => by`. Rewrite using `[hφ₀, Set.indicator_of_notMem hv, Set.indicator_of_notMem hu]⟩`. Establish `hφ₀SB : SB φ₀` using `⟨hφ₀lc, HasCompactSupport.intro hLc fun u hu => Set.indicator_of_notMem hu _⟩`.

Establish `hφ₀0 : φ₀ 0 = 1` using `Set.indicator_of_mem L.zero_mem _`. Use `⟨T φ₀ 0, fun φ hφ => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Use `set φ₁ : V → ℂ := fun u => φ₀ (u + -x) with hφ₁`. Establish `hφ₁SB : SB φ₁` using `⟨hφ₀SB.1.comp_continuous (continuous_add_right _), hφ₀SB.2.comp_homeomorph (Homeomorph.addRight (-x))⟩`.

Establish `hψ` using `sb_add hφ (sb_smul (-φ x) hφ₁SB)`. Establish `hz : (φ + (-φ x) • φ₁) x = 0`. Simplify using `[hφ₁, hφ₀0]`. Establish `h1` using `hloc hψ hz`. Rewrite `h1` using `[hadd _ _ hφ (sb_smul _ hφ₁SB), hsmul _ _ hφ₁SB, htr (-x) φ₀ hφ₀SB]`.

Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_neg_cancel] at h1`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Take the linear combination `h1`.
-/
theorem schur_translations_characters (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
    (χ : V → V → ℂ) (μ : Measure V) (h : NADual V χ μ) (T : (V → ℂ) → (V → ℂ))
    (hSB : ∀ φ, SB φ → SB (T φ))
    (hadd : ∀ φ φ', SB φ → SB φ' → T (φ + φ') = T φ + T φ')
    (hsmul : ∀ (c : ℂ) φ, SB φ → T (c • φ) = c • T φ)
    (hchar : ∀ y φ, SB φ → T (fun u => χ u y * φ u) = fun u => χ u y * T φ u)
    (htr : ∀ x φ, SB φ → T (fun u => φ (u + x)) = fun u => T φ (u + x)) :
    ∃ c : ℂ, ∀ φ, SB φ → T φ = c • φ := by
  have hloc := fun {φ : V → ℂ} (hφ : SB φ) {x : V} (hx : φ x = 0) =>
    apply_eq_zero h hadd hsmul hchar hφ hx
  obtain ⟨hTG, hT2, -, -, -, -, -, hcover, -⟩ := h
  haveI := hTG
  haveI := hT2
  obtain ⟨L, hLc, hLo, -⟩ := hcover 0
  classical
  set φ₀ : V → ℂ := (L : Set V).indicator (fun _ => 1) with hφ₀
  have hφ₀lc : IsLocallyConstant φ₀ := by
    rw [IsLocallyConstant.iff_exists_open]
    intro u
    by_cases hu : u ∈ (L : Set V)
    · exact ⟨L, hLo, hu, fun v hv => by
        rw [hφ₀, Set.indicator_of_mem hv, Set.indicator_of_mem hu]⟩
    · exact ⟨(L : Set V)ᶜ, hLc.isClosed.isOpen_compl, hu, fun v hv => by
        rw [hφ₀, Set.indicator_of_notMem hv, Set.indicator_of_notMem hu]⟩
  have hφ₀SB : SB φ₀ :=
    ⟨hφ₀lc, HasCompactSupport.intro hLc fun u hu => Set.indicator_of_notMem hu _⟩
  have hφ₀0 : φ₀ 0 = 1 := Set.indicator_of_mem L.zero_mem _
  refine ⟨T φ₀ 0, fun φ hφ => ?_⟩
  funext x
  set φ₁ : V → ℂ := fun u => φ₀ (u + -x) with hφ₁
  have hφ₁SB : SB φ₁ :=
    ⟨hφ₀SB.1.comp_continuous (continuous_add_right _),
      hφ₀SB.2.comp_homeomorph (Homeomorph.addRight (-x))⟩
  have hψ := sb_add hφ (sb_smul (-φ x) hφ₁SB)
  have hz : (φ + (-φ x) • φ₁) x = 0 := by
    simp [hφ₁, hφ₀0]
  have h1 := hloc hψ hz
  rw [hadd _ _ hφ (sb_smul _ hφ₁SB), hsmul _ _ hφ₁SB, htr (-x) φ₀ hφ₀SB] at h1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_neg_cancel] at h1
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination h1

end GlobalTheory.CompanionTheory.SW.SchurChar
