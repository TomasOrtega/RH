import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalSectionAngehrnSiuInductiveStepStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilQDivisorAvoidsPointCartierIffNotMemSupp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberCurveOfClassEqSmulAdd
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AmpleStep

variable {X : Scheme.{0}} [IsIntegral X]

/- English proof (translation)
Take `⟨e, he⟩` from `D.exists_isEqn x`. Rewrite `hf`, the goal using `[he.generatesAt_iff]`. Rewrite `hu` using `[he.vanishesAt_iff]`. Take `⟨a, ha, hae⟩` from `hf`. Take `⟨b, hb, hbe⟩` from `hu`.

Use `⟨a + b, ?_, by rw [map_add, hae, hbe, add_mul]⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Establish `h1 : a + b ∈ IsLocalRing.maximalIdeal _` using `(IsLocalRing.mem_maximalIdeal _).2 hn`. Establish `h2 : a ∈ IsLocalRing.maximalIdeal _`. Use `Ideal.sub_mem _ h1 hb` as an intermediate fact.

Simplify using `using this`. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 h2 ha`.
-/
theorem generatesAt_add_vanishesAt {D : CartierDiv X} {x : X} {f u : X.functionField}
    (hf : D.GeneratesAt x f) (hu : D.VanishesAt x u) : D.GeneratesAt x (f + u) := by
  obtain ⟨e, he⟩ := D.exists_isEqn x
  rw [he.generatesAt_iff] at hf ⊢
  rw [he.vanishesAt_iff] at hu
  obtain ⟨a, ha, hae⟩ := hf
  obtain ⟨b, hb, hbe⟩ := hu
  refine ⟨a + b, ?_, by rw [map_add, hae, hbe, add_mul]⟩
  by_contra hn
  have h1 : a + b ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.mem_maximalIdeal _).2 hn
  have h2 : a ∈ IsLocalRing.maximalIdeal _ := by
    have := Ideal.sub_mem _ h1 hb
    simpa using this
  exact (IsLocalRing.mem_maximalIdeal _).1 h2 ha

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => rw [zero_nsmul]`. Conclude with `CartierDiv.eff_zero`. Consider the case `succ r ih => rw [succ_nsmul]`. Conclude with `ih.add hD`.
-/
theorem eff_nsmul {D : CartierDiv X} (hD : D.Eff) (r : ℕ) : (r • D).Eff := by
  induction r with
  | zero => rw [zero_nsmul]; exact CartierDiv.eff_zero
  | succ r ih => rw [succ_nsmul]; exact ih.add hD

variable [IsLocallyNoetherian X]

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero`. Establish `h₀` using `CartierDiv.mult_add (0 : CartierDiv X) 0 z`. Rewrite `h₀` using `[add_zero]`. Rewrite using `[zero_nsmul]`.

Use `push_cast`. Use linear arithmetic over natural numbers and integers. Consider the case `succ r ih => rw [succ_nsmul, CartierDiv.mult_add, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mult_nsmul (E : CartierDiv X) (r : ℕ) (z : X) : (r • E).mult z = r * E.mult z := by
  induction r with
  | zero =>
    have h₀ := CartierDiv.mult_add (0 : CartierDiv X) 0 z
    rw [add_zero] at h₀
    rw [zero_nsmul]
    push_cast
    omega
  | succ r ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

end GlobalTheory.AmpleStep

open GlobalTheory.AmpleStep in

/- English proof (translation)
Introduce `hP X _ _ _ p n hp hn Δ m G A D P z k h hΔ hklt hm hG hA hD hPz hk hdim hz hh hnum`. Take `⟨l₁, hl₁⟩` from `GlobalTheory.GeneralLift.exists_lift_klt hP X p n hp hn Δ D m G A z hm hG hD hA`. Take `⟨l, hll, hhl, f₀, hf₀, hgen, δ₀, hδ0, hδ1, hnk⟩` from `GlobalTheory.T.exists_global_section_angehrnSiu_inductive_step hP X p n hp hn Δ m G A D P z k h hΔ hklt hm hG hA hD hPz hk hdim hz hh hnum l₁`. Take `⟨u, hu, huz, hukl⟩` from `hl₁ l hll f₀ hf₀`. Establish `hgz : (l • A).GeneratesAt z (f₀ + u)` using `generatesAt_add_vanishesAt hgen huz`.

Set `g : X.functionFieldˣ` to `Units.mk0 (f₀ + u) hgz.ne_zero`. Establish `hgv : (g : X.functionField) = f₀ + u` using `rfl`. Establish `hEeff : (CartierDiv.principal g + l • A).Eff` using `CartierDiv.mem_sections_iff_eff.1 (hgv ▸ Submodule.add_mem _ hf₀ hu)`. Establish `hl0 : (0 : ℚ) < l` using `hh.trans hhl`. Establish `hlpos : 0 < l` using `by exact_mod_cast hl0`.

Use `⟨(h / l) • qWeil (CartierDiv.principal g + l • A) 1, δ₀, hδ0, hδ1, ?_, ?_, fun δ hδ hδ' x hx => hnk u hu huz g hgv δ hδ hδ' x hx, ?_⟩` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨a, b, ha0, hb0, hab⟩ : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ h = a / b := by`. Establish `hnum0 : 0 < h.num` using `Rat.num_pos.2 hh`. Use `⟨h.num.toNat, h.den, by omega, h.den_pos, ?_⟩` and prove the remaining obligations. Establish `e1 : ((h.num.toNat : ℕ) : ℚ) = (h.num : ℚ)`.

Establish `: ((h.num.toNat : ℕ) : ℤ) = h.num` using `Int.toNat_of_nonneg hnum0.le`. Conclude with `this` after adjusting the coercions. Rewrite using `[e1, Rat.num_div_den]`. Use `⟨b * l, a • (CartierDiv.principal g + l • A), Nat.mul_pos hb0 hlpos, eff_nsmul hEeff a, ?_, fun C hC => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, qWeil, mult_nsmul, hab]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `hcls : cls (toLB (a • (CartierDiv.principal g + l • A))) (isLB_toLB _) = (a * l) • cls (toLB A) (isLB_toLB A) + 0 • cls (toLB A) (isLB_toLB A)`. Rewrite using `[← toPic_apply, ← toPic_apply]`.

Simplify using `[map_nsmul, toPic_principal, smul_smul, mul_comm]`. Establish `e` using `interNumRed_of_cls_eq_nsmul_add ℂ X p hp _ _ _ (isLB_toLB _) (isLB_toLB A) (isLB_toLB A) (a * l) 0 C hC hcls`. Rewrite using `[e, hab]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `hoff : Off (qWeil (CartierDiv.principal g + l • A) 1) z` using `(off_qWeil_iff_notMem_supp X _ 1 z hEeff one_pos).2 (by`. Take `⟨e, he⟩` from `(l • A).exists_isEqn z`. Rewrite using `[CartierDiv.notMem_supp_iff, ((CartierDiv.isEqn_principal g z).add he).generatesAt_iff, one_mul, Units.val_mul, hgv]`. Conclude with `(he.generatesAt_iff).1 hgz)`.

Introduce `w hw`. Simplify using `[hoff w hw]`. Introduce `y hy a ha hk'`. Conclude with `hukl g hgv y hy a (h / l) ha ((div_lt_one hl0).2 hhl) hk'`.
-/
theorem GlobalTheory.AmpleStep.exists_divisor : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p;
    ∀ (Δ : X → ℚ) (m : ℕ) (G A : CartierDiv X) (D : X → ℚ) (P : Finset X) (z : X) (k : ℕ) (h : ℚ),
      IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB (toLB A) →
      IsQCart D → (∀ x ∈ P, IsClosed ({x} : Set X) ∧ z ⤳ x) → 1 ≤ k →
      topologicalKrullDim (closure ({z} : Set X)) = k → (z = genericPoint X ∨ IsNkltCentre p n (Δ + D) z) → 0 < h →
      (P.card : ℚ) * (k : ℚ) ^ k < h ^ k * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => toLB A : ℤ) →
      ∃ (B : X → ℚ) (δ₀ : ℚ), 0 < δ₀ ∧ δ₀ ≤ 1 ∧ QNum p (toLB A) h B ∧ Off B z ∧
        (∀ δ : ℚ, 0 ≤ δ → δ ≤ δ₀ → ∀ x ∈ P, ¬ KltAt p n (Δ + (1 - δ) • D + B) x) ∧
        (∀ y, ¬ z ⤳ y → ∀ a : ℚ, 0 ≤ a → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + B) y) := by
  intro hP X _ _ _ p n hp hn Δ m G A D P z k h hΔ hklt hm hG hA hD hPz hk hdim hz hh hnum
  obtain ⟨l₁, hl₁⟩ := GlobalTheory.GeneralLift.exists_lift_klt hP X p n hp hn Δ D m G A z hm hG hD hA
  obtain ⟨l, hll, hhl, f₀, hf₀, hgen, δ₀, hδ0, hδ1, hnk⟩ :=
    GlobalTheory.T.exists_global_section_angehrnSiu_inductive_step hP X p n hp hn Δ m G A D P z k h hΔ hklt hm hG hA hD hPz hk hdim hz hh hnum l₁
  obtain ⟨u, hu, huz, hukl⟩ := hl₁ l hll f₀ hf₀
  have hgz : (l • A).GeneratesAt z (f₀ + u) := generatesAt_add_vanishesAt hgen huz
  let g : X.functionFieldˣ := Units.mk0 (f₀ + u) hgz.ne_zero
  have hgv : (g : X.functionField) = f₀ + u := rfl
  have hEeff : (CartierDiv.principal g + l • A).Eff :=
    CartierDiv.mem_sections_iff_eff.1 (hgv ▸ Submodule.add_mem _ hf₀ hu)
  have hl0 : (0 : ℚ) < l := hh.trans hhl
  have hlpos : 0 < l := by exact_mod_cast hl0
  refine ⟨(h / l) • qWeil (CartierDiv.principal g + l • A) 1, δ₀, hδ0, hδ1, ?_, ?_,
    fun δ hδ hδ' x hx => hnk u hu huz g hgv δ hδ hδ' x hx, ?_⟩
  · obtain ⟨a, b, ha0, hb0, hab⟩ : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ h = a / b := by
      have hnum0 : 0 < h.num := Rat.num_pos.2 hh
      refine ⟨h.num.toNat, h.den, by omega, h.den_pos, ?_⟩
      have e1 : ((h.num.toNat : ℕ) : ℚ) = (h.num : ℚ) := by
        have : ((h.num.toNat : ℕ) : ℤ) = h.num := Int.toNat_of_nonneg hnum0.le
        exact_mod_cast this
      rw [e1, Rat.num_div_den]
    refine ⟨b * l, a • (CartierDiv.principal g + l • A), Nat.mul_pos hb0 hlpos, eff_nsmul hEeff a,
      ?_, fun C hC => ?_⟩
    · funext x
      simp only [Pi.smul_apply, smul_eq_mul, qWeil, mult_nsmul, hab]
      push_cast
      field_simp
    · have hcls : cls (toLB (a • (CartierDiv.principal g + l • A))) (isLB_toLB _) =
          (a * l) • cls (toLB A) (isLB_toLB A) + 0 • cls (toLB A) (isLB_toLB A) := by
        rw [← toPic_apply, ← toPic_apply]
        simp [map_nsmul, toPic_principal, smul_smul, mul_comm]
      have e := interNumRed_of_cls_eq_nsmul_add ℂ X p hp _ _ _ (isLB_toLB _) (isLB_toLB A)
        (isLB_toLB A) (a * l) 0 C hC hcls
      rw [e, hab]
      push_cast
      field_simp
      ring
  · have hoff : Off (qWeil (CartierDiv.principal g + l • A) 1) z :=
      (off_qWeil_iff_notMem_supp X _ 1 z hEeff one_pos).2 (by
        obtain ⟨e, he⟩ := (l • A).exists_isEqn z
        rw [CartierDiv.notMem_supp_iff, ((CartierDiv.isEqn_principal g z).add he).generatesAt_iff,
          one_mul, Units.val_mul, hgv]
        exact (he.generatesAt_iff).1 hgz)
    intro w hw
    simp [hoff w hw]
  · intro y hy a ha hk'
    exact hukl g hgv y hy a (h / l) ha ((div_lt_one hl0).2 hhl) hk'
