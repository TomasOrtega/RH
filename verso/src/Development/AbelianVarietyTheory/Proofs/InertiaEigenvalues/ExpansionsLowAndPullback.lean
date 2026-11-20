import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionAtRootOfUnity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedSubfieldLeCyclotomicExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeExpansionsStdBelowLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineFrobeniusBijOnLettersDirectSumStatement

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.LowLevel

section Series

variable {LL M : Type} [Field LL] [AddCommGroup M] [Module LL M]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Unfold `conv`. Rewrite using `[finsum_eq_single _ 0]`. Simplify using the standard rewrite rules. Introduce `j hj`.

Simplify using `[PowerSeries.coeff_one, hj]`.
-/
theorem conv_one (f : ℤ → M) : conv (1 : PowerSeries LL) f = f := by
  funext k
  unfold conv
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    simp [PowerSeries.coeff_one, hj]

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨1, x, (conv_one _).symm⟩`.
-/
theorem mem_latSpan {ι : Type} (e : ι → ℤ → M) (x : ι) : e x ∈ latSpan (LL := LL) e :=
  Submodule.subset_span ⟨1, x, (conv_one _).symm⟩

/- English proof (translation)
The claim follows from `((h _).1 (mem_latSpan e x)).2 k hk`.
-/
theorem neg_eq_zero {ι : Type} {e : ι → ℤ → M} {D : Submodule LL M} (h : Std D (latSpan e))
    (x : ι) (k : ℤ) (hk : k < 0) : e x k = 0 :=
  ((h _).1 (mem_latSpan e x)).2 k hk

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `((h _).1 (mem_latSpan e x)).1 0`. Introduce `d hd`.

Establish `key : ∀ f ∈ latSpan (LL` using `LL) e, f 0 ∈ Submodule.span LL (Set.range fun x => e x 0) := by`. Introduce `f hf`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem f hf`. Take `⟨a, x, rfl⟩` from `hf`.

Unfold `conv`. Rewrite using `[finsum_eq_single _ 0]`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, ?_⟩)` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `j hj`.

Rewrite using `[neg_eq_zero h x _ (by omega), smul_zero]`. Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `add f g _ _ hf hg => exact Submodule.add_mem _ hf hg`. Consider the case `smul c f _ hf => exact Submodule.smul_mem _ c hf`. Establish `hmem : (Pi.single (0 : ℤ) d : ℤ → M) ∈ latSpan (LL` using `LL) e := by`.

Use `(h _).2 ⟨fun k => ?_, fun k hk => Pi.single_eq_of_ne hk.ne _⟩` and prove the remaining obligations. Distinguish the cases in `hk : k = 0`. Substitute `hk` using the available equality. Simplify using `using hd`. Rewrite using `[Pi.single_eq_of_ne hk]`.

Conclude with `D.zero_mem`. Simplify using `using key _ hmem`.
-/
theorem span_const {ι : Type} {e : ι → ℤ → M} {D : Submodule LL M} (h : Std D (latSpan e)) :
    Submodule.span LL (Set.range fun x => e x 0) = D := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ((h _).1 (mem_latSpan e x)).1 0
  · intro d hd
    have key : ∀ f ∈ latSpan (LL := LL) e, f 0 ∈ Submodule.span LL (Set.range fun x => e x 0) := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem f hf =>
        obtain ⟨a, x, rfl⟩ := hf
        unfold conv
        rw [finsum_eq_single _ 0]
        · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, ?_⟩)
          simp
        · intro j hj
          rw [neg_eq_zero h x _ (by omega), smul_zero]
      | zero => exact Submodule.zero_mem _
      | add f g _ _ hf hg => exact Submodule.add_mem _ hf hg
      | smul c f _ hf => exact Submodule.smul_mem _ c hf
    have hmem : (Pi.single (0 : ℤ) d : ℤ → M) ∈ latSpan (LL := LL) e := by
      refine (h _).2 ⟨fun k => ?_, fun k hk => Pi.single_eq_of_ne hk.ne _⟩
      by_cases hk : k = 0
      · subst hk
        simpa using hd
      · rw [Pi.single_eq_of_ne hk]
        exact D.zero_mem
    simpa using key _ hmem

/- English proof (translation)
Rewrite using `[← span_const h, Submodule.map_span, ← Set.range_comp]`. Use `congr 2`. Use function extensionality and compare the values at `x`. Conclude with `hg x`.
-/
theorem span_const_map {M' ι : Type} [AddCommGroup M'] [Module LL M'] {e : ι → ℤ → M}
    {D : Submodule LL M} (h : Std D (latSpan e)) (L : M →ₗ[LL] M') (g : ι → M')
    (hg : ∀ x, g x = L (e x 0)) : Submodule.span LL (Set.range g) = D.map L := by
  rw [← span_const h, Submodule.map_span, ← Set.range_comp]
  congr 2
  funext x
  exact hg x

/- English proof (translation)
Unfold `conv`. Apply `finsum_eq_zero_of_forall_eq_zero` to reduce the goal to its premises. Introduce `m`. Distinguish the cases in `hm : m < k`. Rewrite using `[mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega), zero_smul]`.

Rewrite using `[hf _ (by omega), smul_zero]`.
-/
theorem conv_low (w : PowerSeries LL) (k : ℕ) (f : ℤ → M) (hf : ∀ j < 0, f j = 0) (j : ℤ)
    (hj : j < k) : conv ((PowerSeries.X * w) ^ k) f j = 0 := by
  unfold conv
  apply finsum_eq_zero_of_forall_eq_zero
  intro m
  by_cases hm : m < k
  · rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega), zero_smul]
  · rw [hf _ (by omega), smul_zero]

/- English proof (translation)
Unfold `conv`. Rewrite using `[finsum_eq_single _ k]`. Rewrite using `[mul_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl]`. Simplify using the standard rewrite rules. Introduce `m hmk`.

Distinguish the cases in `hm : m < k`. Rewrite using `[mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega), zero_smul]`. Rewrite using `[hf _ (by omega), smul_zero]`.
-/
theorem conv_lead (w : PowerSeries LL) (k : ℕ) (f : ℤ → M) (hf : ∀ j < 0, f j = 0) :
    conv ((PowerSeries.X * w) ^ k) f k = PowerSeries.constantCoeff w ^ k • f 0 := by
  unfold conv
  rw [finsum_eq_single _ k]
  · rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl]
    simp
  · intro m hmk
    by_cases hm : m < k
    · rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega), zero_smul]
    · rw [hf _ (by omega), smul_zero]

/- English proof (translation)
Take `⟨w, hw, rfl⟩` from `hq`. Establish `hm : ∀ x k, lN x k ∈ D.map L` using `fun x k => by`. Rewrite using `[hN]`. Conclude with `Submodule.mem_map_of_mem (hmem x k)`. Establish `hg0 : ∀ x, ∀ j < (0 : ℤ), c ^ j • φ (e' x j) = 0`.

Introduce `x j hj`. Rewrite using `[neg_eq_zero hS x j hj, map_zero, smul_zero]`. Establish `hc : PowerSeries.constantCoeff w ≠ 0` using `(hw.map PowerSeries.constantCoeff).ne_zero`. Use `⟨fun x k hk j => ⟨hm _ _, fun hj => ?_⟩, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[hN, hφ, conv_low w k _ (hg0 x) j hj, map_zero]`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, k, hk, rfl⟩`. Conclude with `hm _ _`. Introduce and unpack `_ ⟨d, hd, rfl⟩`. Take `⟨d', hd', rfl⟩` from `hsurj hd`.

Establish `hd'' : d' ∈ Submodule.span LL (Set.range fun x => e' x 0)`. Rewrite using `[span_const hS]`. Conclude with `hd'`. Use `clear hd hd'`. Proceed by induction on `hd'' using Submodule.span_induction with`.

Consider the case `mem z hz`. Take `⟨x, rfl⟩` from `hz`. Take `⟨k, hk⟩` from `hex x`. Establish `h2 : L (φ (e' x 0)) = (PowerSeries.constantCoeff w ^ k)⁻¹ • lN (y x k hk) k`. Rewrite using `[hN, hφ, conv_lead w k _ (hg0 x), map_smul, inv_smul_smul₀ (pow_ne_zero _ hc)]`.

Simplify using `only [zpow_zero, one_smul]`. Rewrite using `[h2]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, k, hk, rfl⟩)`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb`.

Rewrite using `[map_add, map_add]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul c a _ ha`. Rewrite using `[map_smul, map_smul]`. Conclude with `Submodule.smul_mem _ c ha`.
-/
theorem pullback_span {M' ι : Type} [AddCommGroup M'] [Module LL M'] {P : ι → ℕ → Prop}
    (y : ∀ x k, P x k → ι) (lN : ι → ℤ → M') (e e' : ι → ℤ → M) {D D' : Submodule LL M}
    (L : M →ₗ[LL] M') (φ : M →ₗ[LL] M) (c : LL) (q : PowerSeries LL)
    (hq : ∃ w, IsUnit w ∧ q = PowerSeries.X * w)
    (hN : ∀ x k, lN x k = L (e x k)) (hmem : ∀ x k, e x k ∈ D) (hS : Std D' (latSpan e'))
    (hφ : ∀ x k hk j, e (y x k hk) j = conv (q ^ k) (fun j => c ^ j • φ (e' x j)) j)
    (hsurj : Set.SurjOn φ D' D) (hex : ∀ x, ∃ k, P x k) :
    (∀ x k hk (j : ℤ), lN (y x k hk) j ∈ D.map L ∧ (j < k → lN (y x k hk) j = 0)) ∧
      Submodule.span LL {z | ∃ x k hk, z = lN (y x k hk) (k : ℕ)} = D.map L := by
  obtain ⟨w, hw, rfl⟩ := hq
  have hm : ∀ x k, lN x k ∈ D.map L := fun x k => by
    rw [hN]
    exact Submodule.mem_map_of_mem (hmem x k)
  have hg0 : ∀ x, ∀ j < (0 : ℤ), c ^ j • φ (e' x j) = 0 := by
    intro x j hj
    rw [neg_eq_zero hS x j hj, map_zero, smul_zero]
  have hc : PowerSeries.constantCoeff w ≠ 0 := (hw.map PowerSeries.constantCoeff).ne_zero
  refine ⟨fun x k hk j => ⟨hm _ _, fun hj => ?_⟩, le_antisymm ?_ ?_⟩
  · rw [hN, hφ, conv_low w k _ (hg0 x) j hj, map_zero]
  · rw [Submodule.span_le]
    rintro _ ⟨x, k, hk, rfl⟩
    exact hm _ _
  · rintro _ ⟨d, hd, rfl⟩
    obtain ⟨d', hd', rfl⟩ := hsurj hd
    have hd'' : d' ∈ Submodule.span LL (Set.range fun x => e' x 0) := by
      rw [span_const hS]
      exact hd'
    clear hd hd'
    induction hd'' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      obtain ⟨k, hk⟩ := hex x
      have h2 : L (φ (e' x 0)) = (PowerSeries.constantCoeff w ^ k)⁻¹ • lN (y x k hk) k := by
        rw [hN, hφ, conv_lead w k _ (hg0 x), map_smul, inv_smul_smul₀ (pow_ne_zero _ hc)]
        simp only [zpow_zero, one_smul]
      rw [h2]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, k, hk, rfl⟩)
    | zero => simp
    | add a b _ _ ha hb =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      rw [map_smul, map_smul]
      exact Submodule.smul_mem _ c ha

/- English proof (translation)
Substitute `hq` using the available equality. Simplify using `only [conv_one] at ha`. Use `⟨fun x k => ⟨?_, fun hk => ?_⟩, span_const_map hS L _ fun x => by rw [ha, hN]⟩` and prove the remaining obligations. Rewrite using `[hN]`. Conclude with `Submodule.mem_map_of_mem (((hS _).1 (mem_latSpan e _)).1 k)`.

Rewrite using `[hN, neg_eq_zero hS x k hk, map_zero]`.
-/
theorem low_span {M' ι : Type} [AddCommGroup M'] [Module LL M'] (a : ι → ι) (lN : ι → ℤ → M')
    (e : ι → ℤ → M) {D : Submodule LL M} (L : M →ₗ[LL] M') (q : PowerSeries LL) (hq : q = 1)
    (ha : ∀ x k, lN (a x) k = conv q (lN x) k)
    (hN : ∀ x k, lN x k = L (e x k)) (hS : Std D (latSpan e)) :
    (∀ x (k : ℤ), lN (a x) k ∈ D.map L ∧ (k < 0 → lN x k = 0)) ∧
      Submodule.span LL (Set.range fun x => lN (a x) 0) = D.map L := by
  subst hq
  simp only [conv_one] at ha
  refine ⟨fun x k => ⟨?_, fun hk => ?_⟩, span_const_map hS L _ fun x => by rw [ha, hN]⟩
  · rw [hN]
    exact Submodule.mem_map_of_mem (((hS _).1 (mem_latSpan e _)).1 k)
  · rw [hN, neg_eq_zero hS x k hk, map_zero]

end Series

/- English proof (translation)
Take `⟨j, -, hj⟩` from `(Nat.dvd_prime_pow hl).1 (orderOf_dvd_of_pow_eq_one h)`. Conclude with `⟨j, hj ▸ IsPrimitiveRoot.orderOf ζ⟩`.
-/
theorem exists_primitive {L : Type} [Field L] {l : ℕ} (hl : l.Prime) {ζ : L} {m : ℕ}
    (h : ζ ^ (l ^ m) = 1) : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hl).1 (orderOf_dvd_of_pow_eq_one h)
  exact ⟨j, hj ▸ IsPrimitiveRoot.orderOf ζ⟩

/- English proof (translation)
Rewrite using `[← pow_mul, ← pow_succ', Nat.sub_add_cancel hs]`. Conclude with `h.pow_eq_one`.
-/
theorem pow_pow_pred {L : Type} [Field L] {l s : ℕ} (hs : 1 ≤ s) {ζ : L}
    (h : IsPrimitiveRoot ζ (l ^ s)) : (ζ ^ l) ^ (l ^ (s - 1)) = 1 := by
  rw [← pow_mul, ← pow_succ', Nat.sub_add_cancel hs]
  exact h.pow_eq_one

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D HW F Cm l _ K s LL h W E C T hT`. Establish `hp : ((D.loc l).PD K).p = l` using `(D.loc l).PD_p K`. Establish `hstd : ∀ (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ (s - 1)) = 1 → Std (Di (HW l) h T i) (latSpan (ex C h T i ζ))` using `GlobalTheory.T.wachLattice_expansions_std_below_level D HW F Cm l K s LL h T hT`. Use `⟨fun i ζ hζ hX => ?_, fun i ζ τ hτ => ?_⟩` and prove the remaining obligations. Establish `hm : ζ ^ (l ^ hζ.choose) = 1`.

Use `hζ.choose_spec` as an intermediate fact. Rewrite `this` using `[show ((D.loc l).PD K).p ^ hζ.choose = l ^ hζ.choose from congrArg (· ^ _) hp]`. Then use the resulting hypothesis. Establish `hl` using `GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h i ζ (exists_primitive Fact.out hm)`. Conclude with `low_span (fun x => (letE i : AA K LL) • x) (W.levN T i ζ) (ex C h T i ζ) _ (W.lev i ζ (letE i)) hl.2.1 (W.levN_smul T i ζ (letE i)) ((C.C K s LL h).tie.levN_eq T i ζ) (hstd i ζ (hl.2.2.2.2.1.1 hX))`. Establish `hprim : IsPrimitiveRoot ζ (l ^ s)` using `((GlobalTheory.NL.Points.points D HW l K s LL h).2.1 i ζ τ hτ).1`.

Establish `hl` using `GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h i ζ ⟨s, hprim⟩`. Establish `hφ : ∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T) (j : ℤ), ex C h T i ζ ⟨_, hk⟩ j = conv ((W.lev i ζ W.Q) ^ k) (fun j => (l : ↥LL.1) ^ j • φVB ((D.loc l).PD K) (LL` using `↥LL.1) (V := T.V) (ex C h T (i - 1) (ζ ^ l) x j)) j := by`. Introduce `x k hk j`. Establish `h1` using `(C.C K s LL h).tie.levB_φ T hT i ζ ⟨s, by rw [hp]; exact hprim⟩ x k hk j`. Rewrite `h1` using `[map_pow, hp]`.

Conclude with `h1`. Conclude with `pullback_span (P := fun (x : ↥(W.N T)) k => W.Q ^ k • W.φD T x ∈ W.N T) (fun _ _ hk => ⟨_, hk⟩) (W.levN T i ζ) (ex C h T i ζ) (ex C h T (i - 1) (ζ ^ l)) _ _ _ _ (hl.2.2.2.1 hprim).1 ((C.C K s LL h).tie.levN_eq T i ζ) ((C.C K s LL h).tie.levB_mem T i ζ) (hstd (i - 1) (ζ ^ l) (pow_ …`.
-/
theorem expansions_low_and_pullback : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → (∀ (i : Let K) (ζ : ↥LL.1), (∃ m : ℕ, ζ ^ (((D.loc l).PD K).p ^ m) = 1) → PowerSeries.constantCoeff (W.lev i ζ W.X) = 0 → (∀ (x : ↥(W.N T)) (k : ℤ), W.levN T i ζ ((letE i : AA K LL) • x) k ∈ (Di (HW l) h T i).map (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) ∧ (k < 0 → W.levN T i ζ x k = 0)) ∧ Submodule.span ↥LL.1 (Set.range fun x : ↥(W.N T) => W.levN T i ζ ((letE i : AA K LL) • x) 0) = (Di (HW l) h T i).map (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V))) ∧ ∀ (i : Let K) (ζ : ↥LL.1) τ, Pt (HW l) h i ζ τ → (∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T) (j : ℤ), W.levN T i ζ ⟨_, hk⟩ j ∈ (Di (HW l) h T i).map (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) ∧ (j < k → W.levN T i ζ ⟨_, hk⟩ j = 0)) ∧ Submodule.span ↥LL.1 {w | ∃ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T), w = W.levN T i ζ ⟨_, hk⟩ k} = (Di (HW l) h T i).map (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) := by
  intro D HW F Cm l _ K s LL h W E C T hT
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hstd : ∀ (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ (s - 1)) = 1 →
      Std (Di (HW l) h T i) (latSpan (ex C h T i ζ)) := GlobalTheory.T.wachLattice_expansions_std_below_level D HW F Cm l K s LL h T hT
  refine ⟨fun i ζ hζ hX => ?_, fun i ζ τ hτ => ?_⟩
  · have hm : ζ ^ (l ^ hζ.choose) = 1 := by
      have := hζ.choose_spec
      rwa [show ((D.loc l).PD K).p ^ hζ.choose = l ^ hζ.choose from congrArg (· ^ _) hp] at this
    have hl := GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h i ζ (exists_primitive Fact.out hm)
    exact low_span (fun x => (letE i : AA K LL) • x) (W.levN T i ζ) (ex C h T i ζ) _
      (W.lev i ζ (letE i)) hl.2.1 (W.levN_smul T i ζ (letE i))
      ((C.C K s LL h).tie.levN_eq T i ζ) (hstd i ζ (hl.2.2.2.2.1.1 hX))
  · have hprim : IsPrimitiveRoot ζ (l ^ s) :=
      ((GlobalTheory.NL.Points.points D HW l K s LL h).2.1 i ζ τ hτ).1
    have hl := GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h i ζ ⟨s, hprim⟩
    have hφ : ∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T) (j : ℤ),
        ex C h T i ζ ⟨_, hk⟩ j = conv ((W.lev i ζ W.Q) ^ k) (fun j => (l : ↥LL.1) ^ j •
          φVB ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) (ex C h T (i - 1) (ζ ^ l) x j)) j := by
      intro x k hk j
      have h1 := (C.C K s LL h).tie.levB_φ T hT i ζ ⟨s, by rw [hp]; exact hprim⟩ x k hk j
      rw [map_pow, hp] at h1
      exact h1
    exact pullback_span (P := fun (x : ↥(W.N T)) k => W.Q ^ k • W.φD T x ∈ W.N T)
      (fun _ _ hk => ⟨_, hk⟩) (W.levN T i ζ) (ex C h T i ζ) (ex C h T (i - 1) (ζ ^ l)) _ _ _ _
      (hl.2.2.2.1 hprim).1 ((C.C K s LL h).tie.levN_eq T i ζ) ((C.C K s LL h).tie.levB_mem T i ζ)
      (hstd (i - 1) (ζ ^ l) (pow_pow_pred h.1 hprim)) hφ
      ((GlobalTheory.T.crystallineFrobenius_bijOn_letters_directSum D HW l K s LL h T hT).1 i).surjOn (fun x => W.N_φ T x x.2)

end GlobalTheory.NL.LowLevel
