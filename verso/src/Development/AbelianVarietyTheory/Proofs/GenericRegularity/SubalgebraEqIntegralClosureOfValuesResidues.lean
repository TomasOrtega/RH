import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.LocRingPf
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
import ReciprocityTheory.SemistableReduction.AlgAll
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.RApprox

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj

namespace GlobalTheory.LocStructNak

variable {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A]

/- English proof (translation)
Establish `h0 : ∀ ζ : Pts O A, algebraMap ↥(As O A) (Loc ζ) b ∈ Ideal.map (algebraMap ↥(As O A) (Loc ζ)) (Ideal.span {c})`. Introduce `ζ`. Establish `h1` using `h ζ`. Rewrite `h1` using `[vL_eq_addVal, vL_eq_addVal, IsDiscreteValuationRing.addVal_le_iff_dvd]`. Rewrite using `[Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]`.

Conclude with `h1`. Conclude with `Ideal.mem_span_singleton.1 (Ideal.mem_of_localization_maximal (fun P hP => h0 ⟨P, hP⟩))`.
-/
theorem dvd_of_vL_le [∀ ζ : Pts O A, IsDVRAt ζ] (c b : ↥(As O A))
    (h : ∀ ζ : Pts O A, vL ζ c ≤ vL ζ b) : c ∣ b := by
  have h0 : ∀ ζ : Pts O A, algebraMap ↥(As O A) (Loc ζ) b ∈
      Ideal.map (algebraMap ↥(As O A) (Loc ζ)) (Ideal.span {c}) := by
    intro ζ
    have h1 := h ζ
    rw [vL_eq_addVal, vL_eq_addVal, IsDiscreteValuationRing.addVal_le_iff_dvd] at h1
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    exact h1
  exact Ideal.mem_span_singleton.1 (Ideal.mem_of_localization_maximal (fun P hP => h0 ⟨P, hP⟩))

omit [IsDomain O] [IsDiscreteValuationRing O] in

/- English proof (translation)
Use `haveI : Algebra.IsIntegral ↥C ↥(As O A) := Algebra.IsIntegral.tower_top O`. Use `haveI := ζ.isMaximal`. Establish `hmax : (ζ.asIdeal.comap (algebraMap ↥C ↥(As O A))).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal ζ.asIdeal`. Take `⟨y, z, hz, hyz⟩` from `hmax.exists_inv (x := ⟨d, hd⟩) (by simpa [Ideal.mem_comap] using hd0)`. Establish `hz' : (z : ↥(As O A)) ∈ ζ.asIdeal` using `hz`.

Establish `hyz' : (y : ↥(As O A)) * d + z = 1` using `congrArg Subtype.val hyz`. Use `⟨y * c, C.mul_mem y.2 hc, ?_⟩` and prove the remaining obligations. Establish `e : b - y * c = y * (d * b - c) + b * z`. Take the linear combination `(-b) * hyz'`. Rewrite using `[e]`.

Conclude with `ζ.asIdeal.add_mem (ζ.asIdeal.mul_mem_left _ h) (ζ.asIdeal.mul_mem_left _ hz')`.
-/
theorem exists_residue (C : Subalgebra O ↥(As O A)) (ζ : Pts O A) (b c d : ↥(As O A))
    (hc : c ∈ C) (hd : d ∈ C) (hd0 : d ∉ ζ.asIdeal) (h : d * b - c ∈ ζ.asIdeal) :
    ∃ c' ∈ C, b - c' ∈ ζ.asIdeal := by
  haveI : Algebra.IsIntegral ↥C ↥(As O A) := Algebra.IsIntegral.tower_top O
  haveI := ζ.isMaximal
  have hmax : (ζ.asIdeal.comap (algebraMap ↥C ↥(As O A))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal ζ.asIdeal
  obtain ⟨y, z, hz, hyz⟩ := hmax.exists_inv (x := ⟨d, hd⟩) (by simpa [Ideal.mem_comap] using hd0)
  have hz' : (z : ↥(As O A)) ∈ ζ.asIdeal := hz
  have hyz' : (y : ↥(As O A)) * d + z = 1 := congrArg Subtype.val hyz
  refine ⟨y * c, C.mul_mem y.2 hc, ?_⟩
  have e : b - y * c = y * (d * b - c) + b * z := by
    linear_combination (-b) * hyz'
  rw [e]
  exact ζ.asIdeal.add_mem (ζ.asIdeal.mul_mem_left _ h) (ζ.asIdeal.mul_mem_left _ hz')

/- English proof (translation)
Use `letI := Fintype.ofFinite (Pts O A)`. Take `⟨N, hN⟩ : ∃ N, ∑ ζ, n ζ = N` from `⟨_, rfl⟩`. Proceed by induction on `N generalizing n with`. Consider the case `zero`. Use `⟨0, C.zero_mem, fun ζ => ?_⟩` and prove the remaining obligations.

Rewrite using `[(Finset.sum_eq_zero_iff.1 hN) ζ (Finset.mem_univ _)]`. Simplify using the standard rewrite rules. Consider the case `succ N ih`. Take `⟨ζ₀, -, h0⟩` from `Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := n) (by rw [hN]; omega)`. Establish `hsum : ∑ ζ, Function.update n ζ₀ (n ζ₀ - 1) ζ = N`.

Rewrite using `[Finset.sum_update_of_mem (Finset.mem_univ _)]`. Rewrite `hN` using `[← Finset.add_sum_erase _ _ (Finset.mem_univ ζ₀), ← Finset.sdiff_singleton_eq_erase]`. Use linear arithmetic over natural numbers and integers. Take `⟨c₁, hc₁, h₁⟩` from `ih _ hsum`. Take `⟨c, hc, hv⟩` from `hval (Function.update n ζ₀ (n ζ₀ - 1))`.

Take `⟨b', hb'⟩` from `dvd_of_vL_le c (b - c₁) (fun ζ => by rw [hv]; exact h₁ ζ)`. Take `⟨c', hc', hm⟩` from `hres ζ₀ b'`. Use `⟨c₁ + c * c', C.add_mem hc₁ (C.mul_mem hc hc'), fun ζ => ?_⟩` and prove the remaining obligations. Establish `e : b - (c₁ + c * c') = c * (b' - c')` using `by linear_combination hb'`. Rewrite using `[e, vL_mul, hv]`.

Distinguish the cases in `hζ : ζ = ζ₀`. Substitute `hζ` using the available equality. Establish `h1 : 1 ≤ vL ζ (b' - c')`. Rewrite using `[Order.one_le_iff_ne_zero, Ne, vL_eq_zero_iff]`. Conclude with `not_not.2 hm`.

Rewrite using `[Function.update_self]`. Combine the equalities or inequalities in the displayed calculation. Establish `: n ζ = (n ζ - 1) + 1` using `by omega`. Use `conv_lhs => rw [this]`. Use `push_cast`.

Both sides reduce to the same expression. Use `_ ≤ _ := add_le_add le_rfl h1`. Rewrite using `[Function.update_of_ne hζ]`. Conclude with `le_self_add`.
-/
theorem exists_approx [∀ ζ : Pts O A, IsDVRAt ζ] [Finite (Pts O A)] (C : Subalgebra O ↥(As O A))
    (hval : ∀ n : Pts O A → ℕ, ∃ c ∈ C, ∀ ζ, vL ζ c = (n ζ : ℕ∞))
    (hres : ∀ (ζ : Pts O A) (b : ↥(As O A)), ∃ c ∈ C, b - c ∈ ζ.asIdeal)
    (n : Pts O A → ℕ) (b : ↥(As O A)) : ∃ c ∈ C, ∀ ζ, (n ζ : ℕ∞) ≤ vL ζ (b - c) := by
  classical
  letI := Fintype.ofFinite (Pts O A)
  obtain ⟨N, hN⟩ : ∃ N, ∑ ζ, n ζ = N := ⟨_, rfl⟩
  induction N generalizing n with
  | zero =>
    refine ⟨0, C.zero_mem, fun ζ => ?_⟩
    rw [(Finset.sum_eq_zero_iff.1 hN) ζ (Finset.mem_univ _)]
    simp
  | succ N ih =>
    obtain ⟨ζ₀, -, h0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := n)
      (by rw [hN]; omega)
    have hsum : ∑ ζ, Function.update n ζ₀ (n ζ₀ - 1) ζ = N := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ _)]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ζ₀), ← Finset.sdiff_singleton_eq_erase] at hN
      omega
    obtain ⟨c₁, hc₁, h₁⟩ := ih _ hsum
    obtain ⟨c, hc, hv⟩ := hval (Function.update n ζ₀ (n ζ₀ - 1))
    obtain ⟨b', hb'⟩ := dvd_of_vL_le c (b - c₁) (fun ζ => by rw [hv]; exact h₁ ζ)
    obtain ⟨c', hc', hm⟩ := hres ζ₀ b'
    refine ⟨c₁ + c * c', C.add_mem hc₁ (C.mul_mem hc hc'), fun ζ => ?_⟩
    have e : b - (c₁ + c * c') = c * (b' - c') := by linear_combination hb'
    rw [e, vL_mul, hv]
    by_cases hζ : ζ = ζ₀
    · subst hζ
      have h1 : 1 ≤ vL ζ (b' - c') := by
        rw [Order.one_le_iff_ne_zero, Ne, vL_eq_zero_iff]
        exact not_not.2 hm
      rw [Function.update_self]
      calc (n ζ : ℕ∞) = ((n ζ - 1 : ℕ) : ℕ∞) + 1 := by
            have : n ζ = (n ζ - 1) + 1 := by omega
            conv_lhs => rw [this]
            push_cast
            rfl
        _ ≤ _ := add_le_add le_rfl h1
    · rw [Function.update_of_ne hζ]
      exact le_self_add

/- English proof (translation)
Use `set C' : Subalgebra O ↥(As O A) := C.comap (As O A).val with hC'`. Establish `hinj : Function.Injective (ENat.map (Nat.cast : ℕ → ℤ))` using `(ENat.strictMono_map_iff.2 Nat.strictMono_cast).injective`. Establish `hzero : ∀ (ζ : Pts O A) (a : ↥(As O A)), ord ϖ ζ (a : A) = 0 ↔ a ∉ ζ.asIdeal`. Introduce `ζ a`. Rewrite using `[ord_of_mem ζ hU a.2, ← vL_eq_zero_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `hinj h`. Introduce `h`. Express the relevant statement in the definitionally equal form `(vL ζ a).map (Nat.cast : ℕ → ℤ) = 0`.

Rewrite using `[h]`. Both sides reduce to the same expression. Establish `hval' : ∀ n : Pts O A → ℕ, ∃ c ∈ C', ∀ ζ, vL ζ c = (n ζ : ℕ∞)`. Introduce `n`. Take `⟨c, hc, h⟩` from `hval n`.

Use `⟨⟨c, hC hc⟩, hc, fun ζ => hinj ?_⟩` and prove the remaining obligations. Rewrite using `[← ord_of_mem ζ hU (hC hc), h ζ, ENat.map_natCast]`. Establish `hres' : ∀ (ζ : Pts O A) (b : ↥(As O A)), ∃ c ∈ C', b - c ∈ ζ.asIdeal`. Introduce `ζ b`. Take `⟨c, hc, d, hd, hd0, h⟩` from `hres ζ b b.2`.

Use `exists_residue C' ζ b ⟨c, hC hc⟩ ⟨d, hC hd⟩ hc hd ((hzero ζ ⟨d, hC hd⟩).1 hd0) ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Conclude with `h.ne' ((hzero ζ _).2 hn)`. Establish `key : (⊤ : Submodule O ↥(As O A)) ≤ Subalgebra.toSubmodule C'`. Use `Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal O) Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson _) ?_` and prove the remaining obligations.

Introduce `b _`. Take `⟨c, hc, h⟩` from `exists_approx C' hval' hres' (ep ϖ) b`. Take `⟨b', hb'⟩` from `dvd_of_vL_le (algebraMap O ↥(As O A) ϖ) (b - c) (fun ζ => by rw [← coe_ep ζ hU]; exact h ζ)`. Establish `e : b = c + ϖ • b'` using `by rw [Algebra.smul_def, ← hb']; ring`. Rewrite using `[e]`.

Conclude with `Submodule.add_mem_sup hc (Submodule.smul_mem_smul ((IsLocalRing.mem_maximalIdeal ϖ).2 hU.irreducible.not_isUnit) Submodule.mem_top)`. Introduce `x hx`. Conclude with `key (Submodule.mem_top (x := (⟨x, hx⟩ : ↥(As O A))))`.
-/
theorem as_le_of_val_of_residue (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing A] [Algebra O A] (ϖ : O) (hU : IsUnif A ϖ) [∀ ζ : Pts O A, IsDVRAt ζ] [Finite (Pts O A)]
    [Module.Finite O ↥(As O A)] (C : Subalgebra O A) (hC : C ≤ As O A)
    (hval : ∀ n : Pts O A → ℕ, ∃ c ∈ C, ∀ ζ, ord ϖ ζ c = (((n ζ : ℕ) : ℤ) : WithTop ℤ))
    (hres : ∀ (ζ : Pts O A), ∀ b ∈ As O A, ∃ c ∈ C, ∃ d ∈ C,
      ord ϖ ζ d = 0 ∧ 0 < ord ϖ ζ (d * b - c)) : As O A ≤ C := by
  set C' : Subalgebra O ↥(As O A) := C.comap (As O A).val with hC'
  have hinj : Function.Injective (ENat.map (Nat.cast : ℕ → ℤ)) :=
    (ENat.strictMono_map_iff.2 Nat.strictMono_cast).injective
  have hzero : ∀ (ζ : Pts O A) (a : ↥(As O A)), ord ϖ ζ (a : A) = 0 ↔ a ∉ ζ.asIdeal := by
    intro ζ a
    rw [ord_of_mem ζ hU a.2, ← vL_eq_zero_iff]
    constructor
    · intro h
      exact hinj h
    · intro h
      change (vL ζ a).map (Nat.cast : ℕ → ℤ) = 0
      rw [h]
      rfl
  have hval' : ∀ n : Pts O A → ℕ, ∃ c ∈ C', ∀ ζ, vL ζ c = (n ζ : ℕ∞) := by
    intro n
    obtain ⟨c, hc, h⟩ := hval n
    refine ⟨⟨c, hC hc⟩, hc, fun ζ => hinj ?_⟩
    rw [← ord_of_mem ζ hU (hC hc), h ζ, ENat.map_natCast]
  have hres' : ∀ (ζ : Pts O A) (b : ↥(As O A)), ∃ c ∈ C', b - c ∈ ζ.asIdeal := by
    intro ζ b
    obtain ⟨c, hc, d, hd, hd0, h⟩ := hres ζ b b.2
    refine exists_residue C' ζ b ⟨c, hC hc⟩ ⟨d, hC hd⟩ hc hd ((hzero ζ ⟨d, hC hd⟩).1 hd0) ?_
    by_contra hn
    exact h.ne' ((hzero ζ _).2 hn)
  have key : (⊤ : Submodule O ↥(As O A)) ≤ Subalgebra.toSubmodule C' := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal O)
      Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson _) ?_
    intro b _
    obtain ⟨c, hc, h⟩ := exists_approx C' hval' hres' (ep ϖ) b
    obtain ⟨b', hb'⟩ := dvd_of_vL_le (algebraMap O ↥(As O A) ϖ) (b - c)
      (fun ζ => by rw [← coe_ep ζ hU]; exact h ζ)
    have e : b = c + ϖ • b' := by rw [Algebra.smul_def, ← hb']; ring
    rw [e]
    exact Submodule.add_mem_sup hc (Submodule.smul_mem_smul
      ((IsLocalRing.mem_maximalIdeal ϖ).2 hU.irreducible.not_isUnit) Submodule.mem_top)
  intro x hx
  exact key (Submodule.mem_top (x := (⟨x, hx⟩ : ↥(As O A))))

end GlobalTheory.LocStructNak
