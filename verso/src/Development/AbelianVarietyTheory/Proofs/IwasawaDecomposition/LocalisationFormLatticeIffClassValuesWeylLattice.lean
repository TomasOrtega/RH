import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.LocW

/- English proof (translation)
Proceed by induction on `x using WithTop.recTopCoe with`. Consider the case `top => simp`. Consider the case `coe m`. Proceed by induction on `y using WithTop.recTopCoe with`. Consider the case `top => simp`.

Consider the case `coe k`. Establish `h1 : (0:ℤ) ≤ m` using `by exact_mod_cast hx`. Establish `h2 : (0:ℤ) < k` using `by exact_mod_cast hy`. Conclude with `(by omega : (0:ℤ) < m + k)` after adjusting the coercions.
-/
theorem pos_add {x y : WithTop ℤ} (hx : 0 ≤ x) (hy : 0 < y) : 0 < x + y := by
  induction x using WithTop.recTopCoe with
  | top => simp
  | coe m =>
    induction y using WithTop.recTopCoe with
    | top => simp
    | coe k =>
      have h1 : (0:ℤ) ≤ m := by exact_mod_cast hx
      have h2 : (0:ℤ) < k := by exact_mod_cast hy
      exact_mod_cast (by omega : (0:ℤ) < m + k)

variable {K : Type} [Field K] [NumberField K] (Pl : Rows.Places K) (w : Pl.Pl)

/- English proof (translation)
Set `v : Valuation K (Multiplicative (WithTop ℤ)ᵒᵈ)` to `Pl.val w`. Establish `hi : IsIntegral ℤ (a : K)` using `RingOfIntegers.isIntegral_coe a`. Establish `h2 : IsIntegral v.integer (a : K)` using `hi.tower_top`. Conclude with `(Valuation.integer.integers v).mem_of_integral h2`.
-/
theorem val_nonneg_int (a : 𝓞 K) : (0 : WithTop ℤ) ≤ Pl.val w (a : K) := by
  let v : Valuation K (Multiplicative (WithTop ℤ)ᵒᵈ) := Pl.val w
  have hi : IsIntegral ℤ (a : K) := RingOfIntegers.isIntegral_coe a
  have h2 : IsIntegral v.integer (a : K) := hi.tower_top
  exact (Valuation.integer.integers v).mem_of_integral h2

def primeW : Ideal (𝓞 K) where
  carrier := {a | (0 : WithTop ℤ) < Pl.val w (a : K)}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact lt_of_lt_of_le (lt_min ha hb) (AddValuation.map_add _ _ _)
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, AddValuation.map_mul] at *
    exact pos_add (val_nonneg_int Pl w c) ha

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_primeW (a : 𝓞 K) : a ∈ primeW Pl w ↔ (0 : WithTop ℤ) < Pl.val w (a : K) := Iff.rfl

/- English proof (translation)
Rewrite `ha` using `[mem_primeW, not_lt]`. Conclude with `le_antisymm ha (val_nonneg_int Pl w a)`.
-/
theorem val_eq_zero_of_not_mem (a : 𝓞 K) (ha : a ∉ primeW Pl w) : Pl.val w (a : K) = 0 := by
  rw [mem_primeW, not_lt] at ha
  exact le_antisymm ha (val_nonneg_int Pl w a)

instance primeW_isPrime : (primeW Pl w).IsPrime where
  ne_top' := by
    intro h
    have : (1 : 𝓞 K) ∈ primeW Pl w := h ▸ Submodule.mem_top
    rw [mem_primeW] at this
    simp at this
  mem_or_mem' := by
    intro a b hab
    by_contra hn
    push Not at hn
    have ha := val_eq_zero_of_not_mem Pl w a hn.1
    have hb := val_eq_zero_of_not_mem Pl w b hn.2
    rw [mem_primeW] at hab
    simp only [map_mul, AddValuation.map_mul, ha, hb, add_zero] at hab
    exact lt_irrefl _ hab

/- English proof (translation)
Introduce `h`. Establish `hl : ((Pl.resChar w : ℕ) : 𝓞 K) ∈ primeW Pl w`. Rewrite using `[mem_primeW]`. Use `push_cast`. Rewrite using `[Pl.val_resChar w]`.

Conclude with `WithTop.coe_lt_coe.mpr (by have := Pl.ramIdx_pos w; omega)`. Rewrite `hl` using `[h, Submodule.mem_bot]`. Use `(Pl.resChar_prime w).ne_zero` as an intermediate fact. Conclude with `this (by exact_mod_cast hl)`.
-/
theorem primeW_ne_bot : primeW Pl w ≠ ⊥ := by
  intro h
  have hl : ((Pl.resChar w : ℕ) : 𝓞 K) ∈ primeW Pl w := by
    rw [mem_primeW]
    push_cast
    rw [Pl.val_resChar w]
    exact WithTop.coe_lt_coe.mpr (by have := Pl.ramIdx_pos w; omega)
  rw [h, Submodule.mem_bot] at hl
  have := (Pl.resChar_prime w).ne_zero
  exact this (by exact_mod_cast hl)

/- English proof (translation)
Establish `hS : (primeW Pl w).primeCompl ≤ nonZeroDivisors (𝓞 K)` using `Ideal.primeCompl_le_nonZeroDivisors _`. Set `R` to `Localization.subalgebra.ofField K (primeW Pl w).primeCompl hS`. Establish `: IsLocalization.AtPrime R (primeW Pl w)` using `Localization.subalgebra.isLocalization_ofField K _ hS`. Establish `: IsDiscreteValuationRing R` using `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) (primeW_ne_bot Pl w) R`. Establish `memR : ∀ r : R, ∃ a s : 𝓞 K, s ∉ primeW Pl w ∧ (r : K) = (a : K) * (s : K)⁻¹`.

Introduce `r`. Take `⟨a, s, hs, e⟩` from `r.2`. Conclude with `⟨a, s, hs, e⟩`. Break down `eq_or_ne t 0 with h0 | h0` into its components or cases. Conclude with `⟨0, 1, by simp, by simp [h0]⟩`.

Break down `ValuationRing.isInteger_or_isInteger R t with ⟨r, hr⟩ | ⟨r, hr⟩` into its components or cases. Take `⟨a, s, hs, e⟩` from `memR r`. Establish `hs0 : (s : K) ≠ 0`. Introduce `h`. Apply `hs` to reduce the goal to its premises.

Rewrite using `[mem_primeW, h]`. Simplify using the standard rewrite rules. Use `⟨a, s, val_eq_zero_of_not_mem Pl w s hs, ?_⟩` and prove the remaining obligations. Establish `: (r : K) = t` using `hr`. Rewrite using `[← this, e]`.

Clear the denominators using the available nonvanishing facts. Take `⟨a, s, hs, e⟩` from `memR r`. Establish `hs0 : (s : K) ≠ 0`. Introduce `h`. Apply `hs` to reduce the goal to its premises.

Rewrite using `[mem_primeW, h]`. Simplify using the standard rewrite rules. Establish `hrt : (r : K) = t⁻¹` using `hr`. Distinguish the cases in `ha : a ∈ primeW Pl w`. It suffices to derive a contradiction.

Establish `hat : (a : K) = t⁻¹ * s` using `by rw [← hrt, e]; field_simp`. Establish `h1 : Pl.val w (a : K) = Pl.val w t⁻¹`. Rewrite using `[hat, AddValuation.map_mul, val_eq_zero_of_not_mem Pl w s hs, add_zero]`. Establish `h2 : Pl.val w t + Pl.val w t⁻¹ = 0`. Rewrite using `[← AddValuation.map_mul, mul_inv_cancel₀ h0, AddValuation.map_one]`.

Rewrite `ha` using `[mem_primeW, h1]`. Use `pos_add ht ha` as an intermediate fact. Rewrite `this` using `[h2]`. Conclude with `lt_irrefl _ this`. Establish `ha0 : (a : K) ≠ 0`.

Introduce `h`. Apply `ha` to reduce the goal to its premises. Rewrite using `[mem_primeW, h]`. Simplify using the standard rewrite rules. Use `⟨s, a, val_eq_zero_of_not_mem Pl w a ha, ?_⟩` and prove the remaining obligations.

Establish `: t = (s : K) * (a : K)⁻¹`. Rewrite using `[← inv_inv t, ← hrt, e]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_den (t : K) (ht : (0 : WithTop ℤ) ≤ Pl.val w t) :
    ∃ a s : 𝓞 K, Pl.val w (s : K) = 0 ∧ (s : K) * t = a := by
  have hS : (primeW Pl w).primeCompl ≤ nonZeroDivisors (𝓞 K) :=
    Ideal.primeCompl_le_nonZeroDivisors _
  let R := Localization.subalgebra.ofField K (primeW Pl w).primeCompl hS
  have : IsLocalization.AtPrime R (primeW Pl w) :=
    Localization.subalgebra.isLocalization_ofField K _ hS
  have : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) (primeW_ne_bot Pl w) R
  have memR : ∀ r : R, ∃ a s : 𝓞 K, s ∉ primeW Pl w ∧ (r : K) = (a : K) * (s : K)⁻¹ := by
    intro r
    obtain ⟨a, s, hs, e⟩ := r.2
    exact ⟨a, s, hs, e⟩
  rcases eq_or_ne t 0 with h0 | h0
  · exact ⟨0, 1, by simp, by simp [h0]⟩
  rcases ValuationRing.isInteger_or_isInteger R t with ⟨r, hr⟩ | ⟨r, hr⟩
  · obtain ⟨a, s, hs, e⟩ := memR r
    have hs0 : (s : K) ≠ 0 := by
      intro h; apply hs; rw [mem_primeW, h]; simp
    refine ⟨a, s, val_eq_zero_of_not_mem Pl w s hs, ?_⟩
    have : (r : K) = t := hr
    rw [← this, e]; field_simp
  · obtain ⟨a, s, hs, e⟩ := memR r
    have hs0 : (s : K) ≠ 0 := by
      intro h; apply hs; rw [mem_primeW, h]; simp
    have hrt : (r : K) = t⁻¹ := hr
    by_cases ha : a ∈ primeW Pl w
    · exfalso
      have hat : (a : K) = t⁻¹ * s := by rw [← hrt, e]; field_simp
      have h1 : Pl.val w (a : K) = Pl.val w t⁻¹ := by
        rw [hat, AddValuation.map_mul, val_eq_zero_of_not_mem Pl w s hs, add_zero]
      have h2 : Pl.val w t + Pl.val w t⁻¹ = 0 := by
        rw [← AddValuation.map_mul, mul_inv_cancel₀ h0, AddValuation.map_one]
      rw [mem_primeW, h1] at ha
      have := pos_add ht ha
      rw [h2] at this
      exact lt_irrefl _ this
    · have ha0 : (a : K) ≠ 0 := by
        intro h; apply ha; rw [mem_primeW, h]; simp
      refine ⟨s, a, val_eq_zero_of_not_mem Pl w a ha, ?_⟩
      have : t = (s : K) * (a : K)⁻¹ := by
        rw [← inv_inv t, ← hrt, e]; field_simp
      rw [this]; field_simp

end GlobalTheory.LocW

open GlobalTheory.LocW in

/- English proof (translation)
Introduce `E K ι _ _ _ _ _ _ _ n S emb lam h Pl w p _ iL _ x`. Use `letI : Fintype S.Cl := h.fintypeCl`. Establish `smulK : ∀ (b : 𝓞 K) (v : VV K lam), b • v = (b : K) • v` using `fun b v => (algebraMap_smul K b v).symm`. Prove the components needed by the constructor for the conclusion. Introduce `hx c`.

Unfold `locW at hx ⊢`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact Submodule.subset_span (hy c)`. Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `add y z _ _ hy hz => exact Submodule.add_mem _ hy hz`.

Consider the case `smul t y _ hy => exact Submodule.smul_mem _ t hy`. Introduce `hall`. Establish `gen : ∀ (M : Submodule (𝓞 K) (VV K lam)) (y : VV K lam), y ∈ Submodule.span (intW Pl w) (M : Set (VV K lam)) → ∃ s : 𝓞 K, Pl.val w (s : K) = 0 ∧ s • y ∈ M`. Introduce `M y hy`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem v hv => exact ⟨1, by simp, by rw [smulK]; push_cast; rw [one_smul]; exact hv⟩`. Consider the case `zero => exact ⟨1, by simp, by rw [smulK, smul_zero]; exact Submodule.zero_mem _⟩`. Consider the case `add u v _ _ hu hv`. Take `⟨s1, h1, m1⟩` from `hu`. Take `⟨s2, h2, m2⟩` from `hv`.

Use `⟨s1 * s2, by push_cast; rw [AddValuation.map_mul, h1, h2, add_zero], ?_⟩` and prove the remaining obligations. Establish `e0 : (s1 * s2) • (u + v) = (s1 * s2) • u + (s1 * s2) • v`. Rewrite using `[smulK, smulK, smulK, smul_add]`. Rewrite using `[e0]`. Establish `e1 : (s1 * s2) • u = s2 • (s1 • u)`.

Rewrite using `[smulK, smulK, smulK, smul_smul]`. Use `push_cast`. Rewrite using `[mul_comm]`. Establish `e2 : (s1 * s2) • v = s1 • (s2 • v)`. Rewrite using `[smulK, smulK, smulK, smul_smul]`.

Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[e1, e2]`. Conclude with `Submodule.add_mem _ (Submodule.smul_mem _ s2 m1) (Submodule.smul_mem _ s1 m2)`. Consider the case `smul t u _ hu`.

Take `⟨s, hs, m⟩` from `hu`. Take `⟨a, s', hs', e⟩` from `exists_den Pl w (t : K) t.2`. Use `⟨s' * s, by push_cast; rw [AddValuation.map_mul, hs, hs', add_zero], ?_⟩` and prove the remaining obligations. Establish `: (s' * s) • (t • u) = a • (s • u)`. Rewrite using `[smulK, smulK, smulK, Subring.smul_def, smul_smul, smul_smul, ← e]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ a m`.

Establish `key : ∀ c, ∃ s : 𝓞 K, Pl.val w (s : K) = 0 ∧ s • x.1 c ∈ delAtr emb lam (S.Lsh c.1 (S.rep c))` using `fun c => gen _ _ (hall c)`. Establish `common : ∀ F : Finset S.Cl, ∃ s : 𝓞 K, Pl.val w (s : K) = 0 ∧ ∀ c ∈ F, s • x.1 c ∈ delAtr emb lam (S.Lsh c.1 (S.rep c))`. Introduce `F`. Proceed by induction on `F using Finset.induction_on with`. Consider the case `empty => exact ⟨1, by simp, by simp⟩`.

Consider the case `insert c F _ ih`. Take `⟨s1, h1, m1⟩` from `ih`. Take `⟨s2, h2, m2⟩` from `key c`. Use `⟨s1 * s2, by push_cast; rw [AddValuation.map_mul, h1, h2, add_zero], ?_⟩` and prove the remaining obligations. Introduce `c' hc'`.

Break down `Finset.mem_insert.mp hc' with rfl | hc'` into its components or cases. Establish `e : (s1 * s2) • x.1 c' = s1 • (s2 • x.1 c')`. Rewrite using `[smulK, smulK, smulK, smul_smul]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ s1 m2`. Establish `e : (s1 * s2) • x.1 c' = s2 • (s1 • x.1 c')`. Rewrite using `[smulK, smulK, smulK, smul_smul]`. Use `push_cast`.

Rewrite using `[mul_comm]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ s2 (m1 c' hc')`. Take `⟨s, hs, hsm⟩` from `common Finset.univ`. Establish `hsx : s • x ∈ S.latOf emb lam h (fun c => delAtr emb lam (S.Lsh c.1 (S.rep c)))`.

Introduce `c`. Conclude with `hsm c (Finset.mem_univ c)`. Establish `hs0 : (s : K) ≠ 0`. Introduce `h0`. Rewrite `hs` using `[h0, AddValuation.map_zero]`.

Conclude with `WithTop.top_ne_zero hs`. Establish `hinv : Pl.val w (s : K)⁻¹ = 0`. Use `AddValuation.map_mul (Pl.val w) (s : K) (s : K)⁻¹` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel₀ hs0, AddValuation.map_one, hs, zero_add]`. Conclude with `this.symm`.

Set `u : intW Pl w` to `⟨(s : K)⁻¹, by show (0 : WithTop ℤ) ≤ _; rw [hinv]⟩`. Establish `hx : x = u • (s • x)`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `c`. Use `show x.1 c = (s : K)⁻¹ • (s • x.1 c)`.

Rewrite using `[smulK, smul_smul, inv_mul_cancel₀ hs0, one_smul]`. Rewrite using `[hx]`. Unfold `locW`. Conclude with `Submodule.smul_mem _ u (Submodule.subset_span hsx)`.
-/
theorem GlobalTheory.Mem.Col2.GStep.locW_latOf_iff : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok) (Pl : Rows.Places K) (w : Pl.Pl) (p : ℕ) [Fact p.Prime] (iL : K →+* ℂ_[p]), (∀ x, x ∈ intW Pl w ↔ ‖iL x‖ ≤ 1) → ∀ x : S.FormsK emb lam h, x ∈ locW Pl w (S.latOf emb lam h fun c => delAtr emb lam (S.Lsh c.1 (S.rep c))) ↔ ∀ c, x.1 c ∈ locW Pl w (delAtr emb lam (S.Lsh c.1 (S.rep c))) := by
  intro E K ι _ _ _ _ _ _ _ n S emb lam h Pl w p _ iL _ x
  classical
  letI : Fintype S.Cl := h.fintypeCl
  have smulK : ∀ (b : 𝓞 K) (v : VV K lam), b • v = (b : K) • v := fun b v =>
    (algebraMap_smul K b v).symm
  constructor
  · intro hx c
    unfold locW at hx ⊢
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (hy c)
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul t y _ hy => exact Submodule.smul_mem _ t hy
  · intro hall
    have gen : ∀ (M : Submodule (𝓞 K) (VV K lam)) (y : VV K lam),
        y ∈ Submodule.span (intW Pl w) (M : Set (VV K lam)) →
        ∃ s : 𝓞 K, Pl.val w (s : K) = 0 ∧ s • y ∈ M := by
      intro M y hy
      induction hy using Submodule.span_induction with
      | mem v hv => exact ⟨1, by simp, by rw [smulK]; push_cast; rw [one_smul]; exact hv⟩
      | zero => exact ⟨1, by simp, by rw [smulK, smul_zero]; exact Submodule.zero_mem _⟩
      | add u v _ _ hu hv =>
        obtain ⟨s1, h1, m1⟩ := hu
        obtain ⟨s2, h2, m2⟩ := hv
        refine ⟨s1 * s2, by push_cast; rw [AddValuation.map_mul, h1, h2, add_zero], ?_⟩
        have e0 : (s1 * s2) • (u + v) = (s1 * s2) • u + (s1 * s2) • v := by
          rw [smulK, smulK, smulK, smul_add]
        rw [e0]
        have e1 : (s1 * s2) • u = s2 • (s1 • u) := by
          rw [smulK, smulK, smulK, smul_smul]; push_cast; rw [mul_comm]
        have e2 : (s1 * s2) • v = s1 • (s2 • v) := by
          rw [smulK, smulK, smulK, smul_smul]; push_cast; rfl
        rw [e1, e2]
        exact Submodule.add_mem _ (Submodule.smul_mem _ s2 m1) (Submodule.smul_mem _ s1 m2)
      | smul t u _ hu =>
        obtain ⟨s, hs, m⟩ := hu
        obtain ⟨a, s', hs', e⟩ := exists_den Pl w (t : K) t.2
        refine ⟨s' * s, by push_cast; rw [AddValuation.map_mul, hs, hs', add_zero], ?_⟩
        have : (s' * s) • (t • u) = a • (s • u) := by
          rw [smulK, smulK, smulK, Subring.smul_def, smul_smul, smul_smul, ← e]
          congr 1
          push_cast
          ring
        rw [this]
        exact Submodule.smul_mem _ a m
    have key : ∀ c, ∃ s : 𝓞 K, Pl.val w (s : K) = 0 ∧
        s • x.1 c ∈ delAtr emb lam (S.Lsh c.1 (S.rep c)) := fun c => gen _ _ (hall c)
    have common : ∀ F : Finset S.Cl, ∃ s : 𝓞 K, Pl.val w (s : K) = 0 ∧
        ∀ c ∈ F, s • x.1 c ∈ delAtr emb lam (S.Lsh c.1 (S.rep c)) := by
      intro F
      induction F using Finset.induction_on with
      | empty => exact ⟨1, by simp, by simp⟩
      | insert c F _ ih =>
        obtain ⟨s1, h1, m1⟩ := ih
        obtain ⟨s2, h2, m2⟩ := key c
        refine ⟨s1 * s2, by push_cast; rw [AddValuation.map_mul, h1, h2, add_zero], ?_⟩
        intro c' hc'
        rcases Finset.mem_insert.mp hc' with rfl | hc'
        · have e : (s1 * s2) • x.1 c' = s1 • (s2 • x.1 c') := by
            rw [smulK, smulK, smulK, smul_smul]; push_cast; rfl
          rw [e]; exact Submodule.smul_mem _ s1 m2
        · have e : (s1 * s2) • x.1 c' = s2 • (s1 • x.1 c') := by
            rw [smulK, smulK, smulK, smul_smul]; push_cast; rw [mul_comm]
          rw [e]; exact Submodule.smul_mem _ s2 (m1 c' hc')
    obtain ⟨s, hs, hsm⟩ := common Finset.univ
    have hsx : s • x ∈ S.latOf emb lam h (fun c => delAtr emb lam (S.Lsh c.1 (S.rep c))) := by
      intro c
      exact hsm c (Finset.mem_univ c)
    have hs0 : (s : K) ≠ 0 := by
      intro h0; rw [h0, AddValuation.map_zero] at hs; exact WithTop.top_ne_zero hs
    have hinv : Pl.val w (s : K)⁻¹ = 0 := by
      have := AddValuation.map_mul (Pl.val w) (s : K) (s : K)⁻¹
      rw [mul_inv_cancel₀ hs0, AddValuation.map_one, hs, zero_add] at this
      exact this.symm
    let u : intW Pl w := ⟨(s : K)⁻¹, by show (0 : WithTop ℤ) ≤ _; rw [hinv]⟩
    have hx : x = u • (s • x) := by
      apply Subtype.ext
      funext c
      show x.1 c = (s : K)⁻¹ • (s • x.1 c)
      rw [smulK, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [hx]
    unfold locW
    exact Submodule.smul_mem _ u (Submodule.subset_span hsx)
