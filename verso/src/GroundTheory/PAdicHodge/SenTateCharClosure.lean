import Mathlib
import GroundTheory.PAdicHodge.SenTateCharUnits
import GroundTheory.PAdicHodge.NormalizedTraceClosure
import GroundTheory.PAdicHodge.NormalizedTrace
import GroundTheory.PAdicHodge.AxLemma
import GroundTheory.PAdicHodge.TateCpTwist
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open IntermediateField

variable {p : ℕ} [hp : Fact p.Prime]

def inertiaGal (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : Subgroup Gal(PadicAlgCl p/K) where
  carrier := {σ | ∀ y : PadicAlgCl p, ‖y‖ ≤ 1 → ‖σ y - y‖ < 1}
  one_mem' := fun y _ => by simp
  mul_mem' := fun {σ τ} hσ hτ y hy => by
    have hτy : ‖τ y‖ ≤ 1 := by rwa [norm_gal_apply]
    have e : (σ * τ) y - y = (σ (τ y) - τ y) + (τ y - y) := by
      rw [AlgEquiv.mul_apply]; ring
    rw [e]
    exact lt_of_le_of_lt ((PadicAlgCl.isNonarchimedean p) _ _) (max_lt (hσ _ hτy) (hτ y hy))
  inv_mem' := fun {σ} hσ y hy => by
    have e : σ (σ⁻¹ y - y) = -(σ y - y) := by
      rw [map_sub, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]; ring
    rw [← norm_gal_apply σ, e, norm_neg]
    exact hσ y hy

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_inertiaGal {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {σ : Gal(PadicAlgCl p/K)} :
    σ ∈ inertiaGal K ↔ ∀ y : PadicAlgCl p, ‖y‖ ≤ 1 → ‖σ y - y‖ < 1 := Iff.rfl

namespace SenTateChar

open SenTateChar

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Apply `hinf` to reduce the goal to its premises. Use `set U : Subgroup Gal(PadicAlgCl p/K) := (unitsOneAdd p 2).comap η`. Establish `hU : IsOpen (U : Set Gal(PadicAlgCl p/K))` using `(isOpen_unitsOneAdd 2).preimage hη`.

Establish `hfin : Finite (Gal(PadicAlgCl p/K) ⧸ U)` using `Subgroup.quotient_finite_of_isOpen U hU`. Set `f : Gal(PadicAlgCl p/K) ⧸ U → ℤ_[p]ˣ` to `fun c => if h : ∃ τ ∈ inertiaGal K, (τ : Gal(PadicAlgCl p/K) ⧸ U) = c then η h.choose else 1`. Use `(Set.finite_range f).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨τ, hτ, rfl⟩`. Use `⟨(τ : Gal(PadicAlgCl p/K) ⧸ U), ?_⟩` and prove the remaining obligations.

Establish `h : ∃ τ' ∈ inertiaGal K, (τ' : Gal(PadicAlgCl p/K) ⧸ U) = τ` using `⟨τ, hτ, rfl⟩`. Simplify using `only [f, dif_pos h]`. Take `⟨hτ', hτ'U⟩` from `h.choose_spec`. Establish `hq : (h.choose)⁻¹ * τ ∈ U` using `QuotientGroup.eq.1 hτ'U`. Establish `hI : (h.choose)⁻¹ * τ ∈ inertiaGal K` using `mul_mem (inv_mem hτ') hτ`.

Establish `h1 : η ((h.choose)⁻¹ * τ) = 1` using `hne _ hI hq`. Rewrite `h1` using `[map_mul, map_inv, inv_mul_eq_one]`. Conclude with `h1`.
-/
theorem exists_mem_inertiaGal_unitsOneAdd_two (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (η : Gal(PadicAlgCl p/K) →* ℤ_[p]ˣ) (hη : Continuous η)
    (hinf : (η '' (inertiaGal K : Set Gal(PadicAlgCl p/K))).Infinite) :
    ∃ τ ∈ inertiaGal K, η τ ∈ unitsOneAdd p 2 ∧ η τ ≠ 1 := by
  by_contra hne
  push Not at hne
  apply hinf
  set U : Subgroup Gal(PadicAlgCl p/K) := (unitsOneAdd p 2).comap η
  have hU : IsOpen (U : Set Gal(PadicAlgCl p/K)) := (isOpen_unitsOneAdd 2).preimage hη
  have hfin : Finite (Gal(PadicAlgCl p/K) ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  classical

  let f : Gal(PadicAlgCl p/K) ⧸ U → ℤ_[p]ˣ := fun c =>
    if h : ∃ τ ∈ inertiaGal K, (τ : Gal(PadicAlgCl p/K) ⧸ U) = c then η h.choose else 1
  refine (Set.finite_range f).subset ?_
  rintro _ ⟨τ, hτ, rfl⟩
  refine ⟨(τ : Gal(PadicAlgCl p/K) ⧸ U), ?_⟩
  have h : ∃ τ' ∈ inertiaGal K, (τ' : Gal(PadicAlgCl p/K) ⧸ U) = τ := ⟨τ, hτ, rfl⟩
  simp only [f, dif_pos h]
  obtain ⟨hτ', hτ'U⟩ := h.choose_spec
  have hq : (h.choose)⁻¹ * τ ∈ U := QuotientGroup.eq.1 hτ'U
  have hI : (h.choose)⁻¹ * τ ∈ inertiaGal K := mul_mem (inv_mem hτ') hτ
  have h1 : η ((h.choose)⁻¹ * τ) = 1 := hne _ hI hq
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

/- English proof (translation)
Use `set Ms : IntermediateField K (PadicAlgCl p) := ⨆ k, M k with hMs`. Use `set E : IntermediateField ℚ_[p] (PadicAlgCl p) := Ms.restrictScalars ℚ_[p] with hE`. Establish `hdir : Directed (· ≤ ·) M` using `hM.directed_le`. Establish `hmemE : ∀ {y : PadicAlgCl p}, y ∈ E → ∃ m, y ∈ M m` using `fun {y} hy => by`. Establish `h : y ∈ ((⨆ k, M k : IntermediateField K (PadicAlgCl p)) : Set (PadicAlgCl p))` using `(mem_restrictScalars _).1 hy`.

Rewrite `h` using `[coe_iSup_of_directed hdir, Set.mem_iUnion]`. Conclude with `h`. Establish `hME : ∀ {m} {y : PadicAlgCl p}, y ∈ M m → y ∈ E` using `fun {m} {y} hy => (mem_restrictScalars _).2 (le_iSup M m hy)`. Establish `hxc : x ∈ closureInCp E`. Establish `hfixed : ∀ σ ∈ Ms.fixingSubgroup, σ • x = x`.

Introduce `σ hσ`. Establish `h1 : η σ = 1` using `hker σ fun k => by`. Rewrite `hσ`, the goal using `[IntermediateField.mem_fixingSubgroup_iff]`. Conclude with `fun y hy => hσ y (le_iSup M k hy)`. Use `hx σ` as an intermediate fact.

Rewrite `this` using `[h1, Units.val_one, PadicInt.coe_one, map_one, one_mul]`. Then use the resulting hypothesis. Establish `h` using `fixedPoints_closedSubgroup_eq_closure Ms.fixingSubgroup (InfiniteGalois.fixingSubgroup_isClosed Ms)`. Establish `hx' : x ∈ {x : ℂ_[p] | ∀ σ ∈ Ms.fixingSubgroup, σ • x = x}` using `hfixed`. Rewrite `hx'` using `[h, InfiniteGalois.fixedField_fixingSubgroup]`. Conclude with `hx'`.

Establish `hC1 : 1 ≤ C`. Establish `h` using `hbound n₁ le_rfl n₁ 1 (one_mem _)`. Rewrite `h` using `[normTrace_of_mem _ (one_mem _), norm_one, mul_one]`. Then use the resulting hypothesis. Establish `hC0 : 0 ≤ C` using `zero_le_one.trans hC1`. Establish `hadd : ∀ n, ∀ y ∈ E, ∀ z ∈ E, normTrace (M n) (y + z) = normTrace (M n) y + normTrace (M n) z` using `fun n y _ z _ => normTrace_add _ y z`.

Establish `hbd : ∀ n, n₁ ≤ n → ∀ y ∈ E, ‖normTrace (M n) y‖ ≤ C * ‖y‖`. Introduce `n hn y hy`. Take `⟨m, hm⟩` from `hmemE hy`. Conclude with `hbound n hn m y hm`. Establish `hmapsE : ∀ (σ : Gal(PadicAlgCl p/K)), ∀ y ∈ E, σ y ∈ E`.

Introduce `σ y hy`. Take `⟨m, hm⟩` from `hmemE hy`. Conclude with `hME (hstab σ m y hm)`. Establish `hcomm : ∀ (σ : Gal(PadicAlgCl p/K)) (n : ℕ) (y : PadicAlgCl p), normTrace (M n) (σ y) = σ (normTrace (M n) y)`. Introduce `σ n y`.

Use `normTrace_map_of_map_eq (M n) σ ?_ y` and prove the remaining obligations. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Conclude with `hstab σ n z hz`. Introduce `z hz`.

Use `⟨σ⁻¹ z, hstab σ⁻¹ n z hz, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `σ (σ⁻¹ z) = z`. Rewrite using `[← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]`. Establish `hR : ∀ n, n₁ ≤ n → extendToClosure E (normTrace (M n)) x = 0`. Introduce `n hn`.

Use `set k' : IntermediateField ℚ_[p] (PadicAlgCl p) := (M n).restrictScalars ℚ_[p]`. Establish `: FiniteDimensional ℚ_[p] (M n)` using `Module.Finite.trans K (M n)`. Establish `: FiniteDimensional ℚ_[p] k'` using `(inferInstance : FiniteDimensional ℚ_[p] (M n))`. Establish `hkE : k' ≤ E` using `fun y hy => hME ((mem_restrictScalars _).1 hy)`. Establish `hmaps : ∀ y ∈ E, normTrace (M n) y ∈ k'` using `fun y _ => (mem_restrictScalars _).2 (normTrace_mem _ y)`.

Establish `hfix : ∀ a ∈ k', normTrace (M n) a = a` using `fun a ha => normTrace_of_mem _ ((mem_restrictScalars _).1 ha)`. Establish `hmul : ∀ a ∈ k', ∀ y ∈ E, normTrace (M n) (a * y) = a * normTrace (M n) y` using `fun a ha y _ => normTrace_mul_of_mem _ ((mem_restrictScalars _).1 ha) y`. Take `⟨γ, hγ, hγη⟩` from `hgen n hn`. Take `⟨b, hb, hbx⟩` from `extendToClosure_mem (hadd n) (hbd n hn) hmaps hxc`. Use `set q : ℚ_[p] := ((η γ : ℤ_[p]) : ℚ_[p])`.

Establish `hq : algebraMap ℚ_[p] ℂ_[p] q = ((algebraMap ℚ_[p] (PadicAlgCl p) q : PadicAlgCl p) : ℂ_[p])`. Both sides reduce to the same expression. Establish `hqk : algebraMap ℚ_[p] (PadicAlgCl p) q ∈ k'` using `k'.algebraMap_mem q`. Establish `hγx : γ • x ∈ closureInCp E` using `smul_mem_closureInCp γ (hmapsE γ) hxc`. Establish `key : extendToClosure E (normTrace (M n)) x = algebraMap ℚ_[p] ℂ_[p] q * extendToClosure E (normTrace (M n)) x` using `by conv_lhs => rw [← hx γ]`.

Rewrite using `[hq, extendToClosure_mul (hadd n) (hbd n hn) hkE hmul hqk hγx, extendToClosure_smul (hadd n) (hbd n hn) γ (hmapsE γ) (fun y _ => hcomm γ n y) hxc, ← hbx, gal_smul_coe, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hγ b ((mem_restrictScalars _).1 hb)]`. Establish `hq1 : algebraMap ℚ_[p] ℂ_[p] q ≠ 1`. Rewrite using `[Ne, ← map_one (algebraMap ℚ_[p] ℂ_[p]), (algebraMap ℚ_[p] ℂ_[p]).injective.eq_iff]`. Introduce `h`. Apply `hγη` to reduce the goal to its premises.

Establish `h' : (η γ : ℤ_[p]) = 1` using `Subtype.ext (by simpa [q] using h)`. Conclude with `Units.ext h'`. Establish `h2 : (algebraMap ℚ_[p] ℂ_[p] q - 1) * extendToClosure E (normTrace (M n)) x = 0`. Rewrite using `[sub_mul, one_mul, ← key, sub_self]`. Conclude with `(mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hq1)`.

Establish `hbound' : ∀ ε > 0, ‖x‖ ≤ (1 + C) * ε`. Introduce `ε hε`. Take `⟨_, ⟨y, hy, rfl⟩, hxy⟩` from `Metric.mem_closure_iff.1 hxc ε hε`. Take `⟨m, hm⟩` from `hmemE hy`. Use `set m' := max m n₁`.

Establish `hym : y ∈ M m'` using `hM (le_max_left _ _) hm`. Establish `hyc : (y : ℂ_[p]) ∈ closureInCp E` using `coe_mem_closureInCp hy`. Establish `hsub : (y : ℂ_[p]) - x ∈ closureInCp E` using `sub_mem_closureInCp hyc hxc`. Establish `hadd'` using `hadd m'`. Establish `hbd'` using `hbd m' (le_max_right _ _)`.

Establish `h1 : extendToClosure E (normTrace (M m')) (y : ℂ_[p]) = extendToClosure E (normTrace (M m')) ((y : ℂ_[p]) - x) + extendToClosure E (normTrace (M m')) x`. Rewrite using `[extendToClosure_sub hadd' hbd' hyc hxc]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[extendToClosure_coe hadd' hbd' hy, normTrace_of_mem _ hym, hR m' (le_max_right _ _), add_zero]`. Establish `h2 : ‖(y : ℂ_[p])‖ ≤ C * ε`.

Rewrite using `[h1]`. Use `(norm_extendToClosure_le hadd' hbd' hsub).trans ?_` and prove the remaining obligations. Rewrite using `[← dist_eq_norm, dist_comm]`. Conclude with `mul_le_mul_of_nonneg_left hxy.le hC0`. Combine the equalities or inequalities in the displayed calculation.

Assume the negation of the conclusion as `hx0`. Establish `hpos : 0 < ‖x‖` using `norm_pos_iff.2 hx0`. Establish `h` using `hbound' (‖x‖ / (2 * (1 + C))) (by positivity)`. Establish `h' : (1 + C) * (‖x‖ / (2 * (1 + C))) = ‖x‖ / 2`. Clear the denominators using the available nonvanishing facts.

Rewrite `h` using `[h']`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eq_zero_of_tower (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (η : Gal(PadicAlgCl p/K) →* ℤ_[p]ˣ)
    (M : ℕ → IntermediateField K (PadicAlgCl p)) (hM : Monotone M)
    [∀ k, FiniteDimensional K (M k)]
    (hstab : ∀ (σ : Gal(PadicAlgCl p/K)) (k : ℕ), ∀ y ∈ M k, σ y ∈ M k)
    (hker : ∀ σ : Gal(PadicAlgCl p/K), (∀ k, σ ∈ (M k).fixingSubgroup) → η σ = 1)
    (C : ℝ) (n₁ : ℕ)
    (hbound : ∀ n, n₁ ≤ n → ∀ m, ∀ y ∈ M m, ‖normTrace (M n) y‖ ≤ C * ‖y‖)
    (hgen : ∀ n, n₁ ≤ n → ∃ γ ∈ (M n).fixingSubgroup, η γ ≠ 1)
    {x : ℂ_[p]}
    (hx : ∀ σ : Gal(PadicAlgCl p/K), algebraMap ℚ_[p] ℂ_[p] ((η σ : ℤ_[p]) : ℚ_[p]) * (σ • x) = x) :
    x = 0 := by
  classical
  set Ms : IntermediateField K (PadicAlgCl p) := ⨆ k, M k with hMs
  set E : IntermediateField ℚ_[p] (PadicAlgCl p) := Ms.restrictScalars ℚ_[p] with hE
  have hdir : Directed (· ≤ ·) M := hM.directed_le
  have hmemE : ∀ {y : PadicAlgCl p}, y ∈ E → ∃ m, y ∈ M m := fun {y} hy => by
    have h : y ∈ ((⨆ k, M k : IntermediateField K (PadicAlgCl p)) : Set (PadicAlgCl p)) :=
      (mem_restrictScalars _).1 hy
    rw [coe_iSup_of_directed hdir, Set.mem_iUnion] at h
    exact h
  have hME : ∀ {m} {y : PadicAlgCl p}, y ∈ M m → y ∈ E := fun {m} {y} hy =>
    (mem_restrictScalars _).2 (le_iSup M m hy)

  have hxc : x ∈ closureInCp E := by
    have hfixed : ∀ σ ∈ Ms.fixingSubgroup, σ • x = x := by
      intro σ hσ
      have h1 : η σ = 1 := hker σ fun k => by
        rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
        exact fun y hy => hσ y (le_iSup M k hy)
      have := hx σ
      rwa [h1, Units.val_one, PadicInt.coe_one, map_one, one_mul] at this
    have h := fixedPoints_closedSubgroup_eq_closure Ms.fixingSubgroup
      (InfiniteGalois.fixingSubgroup_isClosed Ms)
    have hx' : x ∈ {x : ℂ_[p] | ∀ σ ∈ Ms.fixingSubgroup, σ • x = x} := hfixed
    rw [h, InfiniteGalois.fixedField_fixingSubgroup] at hx'
    exact hx'

  have hC1 : 1 ≤ C := by
    have h := hbound n₁ le_rfl n₁ 1 (one_mem _)
    rwa [normTrace_of_mem _ (one_mem _), norm_one, mul_one] at h
  have hC0 : 0 ≤ C := zero_le_one.trans hC1

  have hadd : ∀ n, ∀ y ∈ E, ∀ z ∈ E, normTrace (M n) (y + z) = normTrace (M n) y + normTrace (M n) z :=
    fun n y _ z _ => normTrace_add _ y z
  have hbd : ∀ n, n₁ ≤ n → ∀ y ∈ E, ‖normTrace (M n) y‖ ≤ C * ‖y‖ := by
    intro n hn y hy
    obtain ⟨m, hm⟩ := hmemE hy
    exact hbound n hn m y hm
  have hmapsE : ∀ (σ : Gal(PadicAlgCl p/K)), ∀ y ∈ E, σ y ∈ E := by
    intro σ y hy
    obtain ⟨m, hm⟩ := hmemE hy
    exact hME (hstab σ m y hm)
  have hcomm : ∀ (σ : Gal(PadicAlgCl p/K)) (n : ℕ) (y : PadicAlgCl p),
      normTrace (M n) (σ y) = σ (normTrace (M n) y) := by
    intro σ n y
    refine normTrace_map_of_map_eq (M n) σ ?_ y
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hstab σ n z hz
    · intro z hz
      refine ⟨σ⁻¹ z, hstab σ⁻¹ n z hz, ?_⟩
      change σ (σ⁻¹ z) = z
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

  have hR : ∀ n, n₁ ≤ n → extendToClosure E (normTrace (M n)) x = 0 := by
    intro n hn
    set k' : IntermediateField ℚ_[p] (PadicAlgCl p) := (M n).restrictScalars ℚ_[p]
    have : FiniteDimensional ℚ_[p] (M n) := Module.Finite.trans K (M n)
    have : FiniteDimensional ℚ_[p] k' := (inferInstance : FiniteDimensional ℚ_[p] (M n))
    have hkE : k' ≤ E := fun y hy => hME ((mem_restrictScalars _).1 hy)
    have hmaps : ∀ y ∈ E, normTrace (M n) y ∈ k' := fun y _ =>
      (mem_restrictScalars _).2 (normTrace_mem _ y)
    have hfix : ∀ a ∈ k', normTrace (M n) a = a := fun a ha =>
      normTrace_of_mem _ ((mem_restrictScalars _).1 ha)
    have hmul : ∀ a ∈ k', ∀ y ∈ E, normTrace (M n) (a * y) = a * normTrace (M n) y :=
      fun a ha y _ => normTrace_mul_of_mem _ ((mem_restrictScalars _).1 ha) y
    obtain ⟨γ, hγ, hγη⟩ := hgen n hn
    obtain ⟨b, hb, hbx⟩ := extendToClosure_mem (hadd n) (hbd n hn) hmaps hxc

    set q : ℚ_[p] := ((η γ : ℤ_[p]) : ℚ_[p])
    have hq : algebraMap ℚ_[p] ℂ_[p] q = ((algebraMap ℚ_[p] (PadicAlgCl p) q : PadicAlgCl p) : ℂ_[p]) :=
      rfl
    have hqk : algebraMap ℚ_[p] (PadicAlgCl p) q ∈ k' := k'.algebraMap_mem q
    have hγx : γ • x ∈ closureInCp E := smul_mem_closureInCp γ (hmapsE γ) hxc
    have key : extendToClosure E (normTrace (M n)) x =
        algebraMap ℚ_[p] ℂ_[p] q * extendToClosure E (normTrace (M n)) x := by
      conv_lhs => rw [← hx γ]
      rw [hq, extendToClosure_mul (hadd n) (hbd n hn) hkE hmul hqk hγx,
        extendToClosure_smul (hadd n) (hbd n hn) γ (hmapsE γ) (fun y _ => hcomm γ n y) hxc, ← hbx,
        gal_smul_coe, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hγ b ((mem_restrictScalars _).1 hb)]
    have hq1 : algebraMap ℚ_[p] ℂ_[p] q ≠ 1 := by
      rw [Ne, ← map_one (algebraMap ℚ_[p] ℂ_[p]), (algebraMap ℚ_[p] ℂ_[p]).injective.eq_iff]
      intro h
      apply hγη
      have h' : (η γ : ℤ_[p]) = 1 := Subtype.ext (by simpa [q] using h)
      exact Units.ext h'
    have h2 : (algebraMap ℚ_[p] ℂ_[p] q - 1) * extendToClosure E (normTrace (M n)) x = 0 := by
      rw [sub_mul, one_mul, ← key, sub_self]
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hq1)

  have hbound' : ∀ ε > 0, ‖x‖ ≤ (1 + C) * ε := by
    intro ε hε
    obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := Metric.mem_closure_iff.1 hxc ε hε
    obtain ⟨m, hm⟩ := hmemE hy
    set m' := max m n₁
    have hym : y ∈ M m' := hM (le_max_left _ _) hm
    have hyc : (y : ℂ_[p]) ∈ closureInCp E := coe_mem_closureInCp hy
    have hsub : (y : ℂ_[p]) - x ∈ closureInCp E := sub_mem_closureInCp hyc hxc
    have hadd' := hadd m'
    have hbd' := hbd m' (le_max_right _ _)
    have h1 : extendToClosure E (normTrace (M m')) (y : ℂ_[p]) =
        extendToClosure E (normTrace (M m')) ((y : ℂ_[p]) - x) +
          extendToClosure E (normTrace (M m')) x := by
      rw [extendToClosure_sub hadd' hbd' hyc hxc]
      ring
    rw [extendToClosure_coe hadd' hbd' hy, normTrace_of_mem _ hym, hR m' (le_max_right _ _),
      add_zero] at h1
    have h2 : ‖(y : ℂ_[p])‖ ≤ C * ε := by
      rw [h1]
      refine (norm_extendToClosure_le hadd' hbd' hsub).trans ?_
      rw [← dist_eq_norm, dist_comm]
      exact mul_le_mul_of_nonneg_left hxy.le hC0
    calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - (y : ℂ_[p])‖ + ‖(y : ℂ_[p])‖ := norm_add_le _ _
      _ ≤ ε + C * ε := add_le_add (by rw [← dist_eq_norm]; exact hxy.le) h2
      _ = (1 + C) * ε := by ring
  by_contra hx0
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have h := hbound' (‖x‖ / (2 * (1 + C))) (by positivity)
  have h' : (1 + C) * (‖x‖ / (2 * (1 + C))) = ‖x‖ / 2 := by
    field_simp
  rw [h'] at h
  linarith

end SenTateChar

end GroundTheory.PAdicHodge
