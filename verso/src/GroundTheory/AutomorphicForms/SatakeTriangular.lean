import Mathlib
import GroundTheory.AutomorphicForms.SatakeNormalized

noncomputable section

namespace GroundTheory.Automorphic

open MeasureTheory GLnLocal Iwasawa HeckeAlgebra AddMonoidAlgebra

namespace Spherical

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

/- English proof (translation)
Rewrite using `[tailSum]`. Use `Finset.sum_congr rfl fun j _ => congrArg l (Fin.ext ?_)` and prove the remaining obligations. Simplify using `[tailEmb]`.
-/
theorem tailSum_self (l : Fin n → ℤ) : tailSum l (le_refl n) = ∑ i, l i := by
  rw [tailSum]
  refine Finset.sum_congr rfl fun j _ => congrArg l (Fin.ext ?_)
  simp [tailEmb]

def DomLE (l ν : Fin n → ℤ) : Prop :=
  (∀ m (hm : m ≤ n), tailSum ν hm ≤ tailSum l hm) ∧ ∑ i, l i = ∑ i, ν i

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ _ => le_rfl, rfl⟩`.
-/
theorem DomLE.refl (l : Fin n → ℤ) : DomLE l l :=
  ⟨fun _ _ => le_rfl, rfl⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun m hm => (h₂.1 m hm).trans (h₁.1 m hm), h₁.2.trans h₂.2⟩`.
-/
theorem DomLE.trans {l ν ν' : Fin n → ℤ} (h₁ : DomLE l ν) (h₂ : DomLE ν ν') : DomLE l ν' :=
  ⟨fun m hm => (h₂.1 m hm).trans (h₁.1 m hm), h₁.2.trans h₂.2⟩

/- English proof (translation)
The claim follows from `Finset.sum_le_sum fun _ _ => h.1 _ _`.
-/
theorem DomLE.ell_le {l ν : Fin n → ℤ} (h : DomLE l ν) : ell ν ≤ ell l :=
  Finset.sum_le_sum fun _ _ => h.1 _ _

/- English proof (translation)
Establish `hall` using `(Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun m _ => h.1 _ (Nat.lt_succ_iff.1 m.2))).1 he.symm`. Use `eq_of_tailSum_eq fun m hm => ?_` and prove the remaining obligations. Conclude with `(hall ⟨m, Nat.lt_succ_iff.2 hm⟩ (Finset.mem_univ _)).symm`.
-/
theorem DomLE.eq_of_ell_eq {l ν : Fin n → ℤ} (h : DomLE l ν) (he : ell l = ell ν) : l = ν := by
  have hall := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
    (fun m _ => h.1 _ (Nat.lt_succ_iff.1 m.2))).1 he.symm
  refine eq_of_tailSum_eq fun m hm => ?_
  exact (hall ⟨m, Nat.lt_succ_iff.2 hm⟩ (Finset.mem_univ _)).symm

/- English proof (translation)
The claim follows from `h₁.eq_of_ell_eq (le_antisymm h₂.ell_le h₁.ell_le)`.
-/
theorem DomLE.antisymm {l ν : Fin n → ℤ} (h₁ : DomLE l ν) (h₂ : DomLE ν l) : l = ν :=
  h₁.eq_of_ell_eq (le_antisymm h₂.ell_le h₁.ell_le)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ hm => tailSum_le_iwasawaExponent hν hg hm, sum_iwasawaExponent hg⟩`.
-/
theorem domLE_iwasawaExponent {ν : Fin n → ℤ} (hν : Cartan.IsDominant ν) {g : GL (Fin n) F}
    (hg : g ∈ DoubleCoset.doubleCoset (Cartan.diagPow F n ν)
      (integralGL F n : Set (GL (Fin n) F)) (integralGL F n)) :
    DomLE (iwasawaExponent F n g) ν :=
  ⟨fun _ hm => tailSum_le_iwasawaExponent hν hg hm, sum_iwasawaExponent hg⟩

/- English proof (translation)
The claim follows from `domLE_iwasawaExponent (cartanType_spec g).1 (cartanType_spec g).2`.
-/
theorem domLE_cartanType (g : GL (Fin n) F) : DomLE (iwasawaExponent F n g) (cartanType F n g) :=
  domLE_iwasawaExponent (cartanType_spec g).1 (cartanType_spec g).2

def defect (ν : Fin n → ℤ) : ℤ :=
  ∑ m : Fin (n + 1), (((m : ℕ) : ℤ) * ∑ i, ν i - n * tailSum ν (Nat.lt_succ_iff.1 m.2))

/- English proof (translation)
Establish `key : ∀ k (hmk : m ≤ k), ∀ hk : k ≤ n, (k : ℤ) * tailSum ν hm ≤ m * tailSum ν hk`. Introduce `k hmk`. Proceed by induction on `k, hmk using Nat.le_induction with`. Consider the case `base => intro _`. Rewrite using `[mul_comm]`.

Consider the case `succ k hmk ih`. Introduce `hk1`. Establish `hk : k ≤ n` using `by omega`. Establish `ih'` using `ih hk`. Rewrite using `[tailSum_succ ν hk1]`.

Use `set v := ν ⟨n - (k + 1), by omega⟩`. Establish `hbound : tailSum ν hm ≤ m * v`. Establish `: ∀ j : Fin m, ν (tailEmb hm j) ≤ v` using `fun j => hν (show (⟨n - (k + 1), by omega⟩ : Fin n) ≤ tailEmb hm j by`. Simplify using `only [tailEmb, Fin.le_def]`. Use the proof step `omega)`.

Combine the equalities or inequalities in the displayed calculation. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities. Use `key n hm le_rfl` as an intermediate fact. Rewrite `this` using `[tailSum_self]`. Then use the resulting hypothesis.
-/
theorem mul_tailSum_le {ν : Fin n → ℤ} (hν : Antitone ν) {m : ℕ} (hm : m ≤ n) :
    (n : ℤ) * tailSum ν hm ≤ m * ∑ i, ν i := by
  have key : ∀ k (hmk : m ≤ k), ∀ hk : k ≤ n, (k : ℤ) * tailSum ν hm ≤ m * tailSum ν hk := by
    intro k hmk
    induction k, hmk using Nat.le_induction with
    | base => intro _; rw [mul_comm]
    | succ k hmk ih =>
      intro hk1
      have hk : k ≤ n := by omega
      have ih' := ih hk
      rw [tailSum_succ ν hk1]
      set v := ν ⟨n - (k + 1), by omega⟩
      have hbound : tailSum ν hm ≤ m * v := by
        have : ∀ j : Fin m, ν (tailEmb hm j) ≤ v := fun j =>
          hν (show (⟨n - (k + 1), by omega⟩ : Fin n) ≤ tailEmb hm j by
            simp only [tailEmb, Fin.le_def]
            omega)
        calc tailSum ν hm = ∑ j : Fin m, ν (tailEmb hm j) := rfl
          _ ≤ ∑ _j : Fin m, v := Finset.sum_le_sum fun j _ => this j
          _ = m * v := by simp
      push_cast
      nlinarith
  have := key n hm le_rfl
  rwa [tailSum_self] at this

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun m _ => by have := mul_tailSum_le hν (Nat.lt_succ_iff.1 m.2) linarith`.
-/
theorem defect_nonneg {ν : Fin n → ℤ} (hν : Antitone ν) : 0 ≤ defect ν :=
  Finset.sum_nonneg fun m _ => by
    have := mul_tailSum_le hν (Nat.lt_succ_iff.1 m.2)
    linarith

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨m, hm, hlt⟩ : ∃ m, ∃ hm : m ≤ n, tailSum ν hm < tailSum l hm := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `hne (eq_of_tailSum_eq fun m hm => le_antisymm (hcon m hm) (h.1 m hm))`. Establish `hn : (0 : ℤ) < n`.

Break down `Nat.eq_zero_or_pos n with h0 | h0` into its components or cases. Substitute `h0` using the available equality. Conclude with `absurd (funext fun i => i.elim0) hne`. Conclude with `h0` after adjusting the coercions. Use `Finset.sum_lt_sum (fun m _ => ?_) ⟨⟨m, Nat.lt_succ_iff.2 hm⟩, Finset.mem_univ _, ?_⟩` and prove the remaining obligations.

Rewrite using `[h.2]`. Use `h.1 _ (Nat.lt_succ_iff.1 m.2)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[h.2]`. Establish `: tailSum ν (Nat.lt_succ_iff.1 (Nat.lt_succ_iff.2 hm)) < tailSum l (Nat.lt_succ_iff.1 (Nat.lt_succ_iff.2 hm))` using `hlt`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem defect_lt {l ν : Fin n → ℤ} (h : DomLE l ν) (hne : l ≠ ν) : defect l < defect ν := by
  obtain ⟨m, hm, hlt⟩ : ∃ m, ∃ hm : m ≤ n, tailSum ν hm < tailSum l hm := by
    by_contra hcon
    push Not at hcon
    exact hne (eq_of_tailSum_eq fun m hm => le_antisymm (hcon m hm) (h.1 m hm))
  have hn : (0 : ℤ) < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      exact absurd (funext fun i => i.elim0) hne
    · exact_mod_cast h0
  refine Finset.sum_lt_sum (fun m _ => ?_) ⟨⟨m, Nat.lt_succ_iff.2 hm⟩, Finset.mem_univ _, ?_⟩
  · rw [h.2]
    have := h.1 _ (Nat.lt_succ_iff.1 m.2)
    nlinarith
  · rw [h.2]
    have : tailSum ν (Nat.lt_succ_iff.1 (Nat.lt_succ_iff.2 hm)) <
        tailSum l (Nat.lt_succ_iff.1 (Nat.lt_succ_iff.2 hm)) := hlt
    nlinarith

/- English proof (translation)
Use `cartanType_eq (cartanType_spec g).1 ?_` and prove the remaining obligations. Take `⟨k₁, hk₁, k₂, hk₂, hg⟩` from `(Cartan.mem_doubleCoset_diagPow F n).1 (cartanType_spec g).2`. Use `(Cartan.mem_doubleCoset_diagPow F n).2 ⟨k₁, hk₁, k₂ * k, mul_mem hk₂ hk, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [hg]`. Use `group`.
-/
theorem cartanType_mul_right (g : GL (Fin n) F) {k : GL (Fin n) F} (hk : k ∈ integralGL F n) :
    cartanType F n (g * k) = cartanType F n g := by
  refine cartanType_eq (cartanType_spec g).1 ?_
  obtain ⟨k₁, hk₁, k₂, hk₂, hg⟩ := (Cartan.mem_doubleCoset_diagPow F n).1 (cartanType_spec g).2
  refine (Cartan.mem_doubleCoset_diagPow F n).2 ⟨k₁, hk₁, k₂ * k, mul_mem hk₂ hk, ?_⟩
  conv_lhs => rw [hg]
  group

/- English proof (translation)
Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul (integralGL F n) g`. Rewrite using `[hk, cartanType_mul_right _ k.2]`.
-/
theorem cartanType_out (g : GL (Fin n) F) :
    cartanType F n (QuotientGroup.mk g : GL (Fin n) F ⧸ integralGL F n).out = cartanType F n g := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (integralGL F n) g
  rw [hk, cartanType_mul_right _ k.2]

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Conclude with `hg (by rw [← apply_out h g]; exact apply_out_eq_zero hx)`.
-/
theorem mk_mem_cosetSupport {h : SphericalHecke μ (F := F) (n := n)} {g : GL (Fin n) F}
    (hg : (h : HeckeAlgebra μ) g ≠ 0) :
    (QuotientGroup.mk g : GL (Fin n) F ⧸ integralGL F n) ∈ cosetSupport h := by
  by_contra hx
  exact hg (by rw [← apply_out h g]; exact apply_out_eq_zero hx)

/- English proof (translation)
Rewrite using `[satake_coeff]`. Use `set c := (h : HeckeAlgebra μ) (Cartan.diagPow F n ν)`. Establish `hclaim : ∀ x ∈ cosetSupport h, (if iwasawaExponent F n x.out = ν then (h : HeckeAlgebra μ) x.out else 0) = if iwasawaExponent F n x.out = ν ∧ (h : HeckeAlgebra μ) x.out ≠ 0 then c else 0`. Introduce `x _`. Distinguish the cases in `hxz : (h : HeckeAlgebra μ) x.out = 0`.

Simplify using `[hxz]`. Distinguish the cases in `hi : iwasawaExponent F n x.out = ν`. Rewrite using `[if_pos hi, if_pos ⟨hi, hxz⟩]`. Establish `hd` using `domLE_cartanType x.out`. Rewrite `hd` using `[hi]`.

Rewrite using `[apply_eq_apply_cartanType, hmax x.out hxz hd]`. Rewrite using `[if_neg hi, if_neg fun h' => hi h'.1]`. Rewrite using `[Finset.sum_congr rfl hclaim, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]`. Establish `hν : iwasawaExponent F n (Cartan.diagPow F n ν) = ν`. Rewrite using `[diagPow_eq_torusPow, iwasawaExponent_torusPow]`.

Establish `hmem : (QuotientGroup.mk (Cartan.diagPow F n ν) : GL (Fin n) F ⧸ integralGL F n) ∈ (cosetSupport h).filter (fun x => iwasawaExponent F n x.out = ν ∧ (h : HeckeAlgebra μ) x.out ≠ 0)`. Use `Finset.mem_filter.2 ⟨mk_mem_cosetSupport hc, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[iwasawaExponent_out, hν]`. Rewrite using `[apply_out]`. Conclude with `hc`.

Establish `hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'`. Conclude with `mul_ne_zero hK (mul_ne_zero (Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨_, hmem⟩)) hc)`.
-/
theorem coeff_satake_ne_zero_of_maximal {h : SphericalHecke μ (F := F) (n := n)} {ν : Fin n → ℤ}
    (hc : (h : HeckeAlgebra μ) (Cartan.diagPow F n ν) ≠ 0)
    (hmax : ∀ g, (h : HeckeAlgebra μ) g ≠ 0 → DomLE ν (cartanType F n g) → cartanType F n g = ν) :
    (satake μ h).coeff ν ≠ 0 := by
  classical
  rw [satake_coeff]
  set c := (h : HeckeAlgebra μ) (Cartan.diagPow F n ν)
  have hclaim : ∀ x ∈ cosetSupport h,
      (if iwasawaExponent F n x.out = ν then (h : HeckeAlgebra μ) x.out else 0) =
        if iwasawaExponent F n x.out = ν ∧ (h : HeckeAlgebra μ) x.out ≠ 0 then c else 0 := by
    intro x _
    by_cases hxz : (h : HeckeAlgebra μ) x.out = 0
    · simp [hxz]
    by_cases hi : iwasawaExponent F n x.out = ν
    · rw [if_pos hi, if_pos ⟨hi, hxz⟩]
      have hd := domLE_cartanType x.out
      rw [hi] at hd
      rw [apply_eq_apply_cartanType, hmax x.out hxz hd]
    · rw [if_neg hi, if_neg fun h' => hi h'.1]
  rw [Finset.sum_congr rfl hclaim, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hν : iwasawaExponent F n (Cartan.diagPow F n ν) = ν := by
    rw [diagPow_eq_torusPow, iwasawaExponent_torusPow]
  have hmem : (QuotientGroup.mk (Cartan.diagPow F n ν) : GL (Fin n) F ⧸ integralGL F n) ∈
      (cosetSupport h).filter (fun x => iwasawaExponent F n x.out = ν ∧
        (h : HeckeAlgebra μ) x.out ≠ 0) := by
    refine Finset.mem_filter.2 ⟨mk_mem_cosetSupport hc, ?_, ?_⟩
    · rw [iwasawaExponent_out, hν]
    · rw [apply_out]
      exact hc
  have hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'
  exact mul_ne_zero hK (mul_ne_zero (Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨_, hmem⟩)) hc)

/- English proof (translation)
Use `set X := (cosetSupport h).filter fun x => (h : HeckeAlgebra μ) x.out ≠ 0 ∧ DomLE (cartanType F n g₀) (cartanType F n x.out)`. Establish `hX : ∀ g, (h : HeckeAlgebra μ) g ≠ 0 → DomLE (cartanType F n g₀) (cartanType F n g) → (QuotientGroup.mk g : GL (Fin n) F ⧸ integralGL F n) ∈ X` using `fun g hg hd => Finset.mem_filter.2 ⟨mk_mem_cosetSupport hg, by rw [apply_out]; exact hg, by rw [cartanType_out]; exact hd⟩`. Take `⟨x₁, hx₁, hmin⟩` from `X.exists_min_image (fun x => ell (cartanType F n x.out)) ⟨_, hX g₀ h₀ (DomLE.refl _)⟩`. Take `⟨-, hx₁h, hx₁d⟩` from `Finset.mem_filter.1 hx₁`. Use `⟨x₁.out, hx₁h, hx₁d, fun g hg hd => ?_⟩` and prove the remaining obligations.

Establish `h1` using `hmin _ (hX g hg (hx₁d.trans hd))`. Rewrite `h1` using `[cartanType_out]`. Conclude with `(hd.eq_of_ell_eq (le_antisymm h1 hd.ell_le)).symm`.
-/
theorem exists_maximal {h : SphericalHecke μ (F := F) (n := n)} {g₀ : GL (Fin n) F}
    (h₀ : (h : HeckeAlgebra μ) g₀ ≠ 0) :
    ∃ g₁, (h : HeckeAlgebra μ) g₁ ≠ 0 ∧ DomLE (cartanType F n g₀) (cartanType F n g₁) ∧
      ∀ g, (h : HeckeAlgebra μ) g ≠ 0 → DomLE (cartanType F n g₁) (cartanType F n g) →
        cartanType F n g = cartanType F n g₁ := by
  classical
  set X := (cosetSupport h).filter fun x =>
    (h : HeckeAlgebra μ) x.out ≠ 0 ∧ DomLE (cartanType F n g₀) (cartanType F n x.out)
  have hX : ∀ g, (h : HeckeAlgebra μ) g ≠ 0 → DomLE (cartanType F n g₀) (cartanType F n g) →
      (QuotientGroup.mk g : GL (Fin n) F ⧸ integralGL F n) ∈ X := fun g hg hd =>
    Finset.mem_filter.2 ⟨mk_mem_cosetSupport hg, by rw [apply_out]; exact hg,
      by rw [cartanType_out]; exact hd⟩
  obtain ⟨x₁, hx₁, hmin⟩ := X.exists_min_image (fun x => ell (cartanType F n x.out))
    ⟨_, hX g₀ h₀ (DomLE.refl _)⟩
  obtain ⟨-, hx₁h, hx₁d⟩ := Finset.mem_filter.1 hx₁
  refine ⟨x₁.out, hx₁h, hx₁d, fun g hg hd => ?_⟩
  have h1 := hmin _ (hX g hg (hx₁d.trans hd))
  rw [cartanType_out] at h1
  exact (hd.eq_of_ell_eq (le_antisymm h1 hd.ell_le)).symm

/- English proof (translation)
Assume the negation of the conclusion as `hall`. Use `push Not at hall`. Conclude with `hne (HeckeAlgebraLevel.ext _ _ (HeckeAlgebra.ext fun x => by`. Rewrite using `[hall x, HeckeAlgebraLevel.val_zero, HeckeAlgebra.coe_zero, Pi.zero_apply]))`.
-/
theorem exists_apply_ne_zero {h : SphericalHecke μ (F := F) (n := n)} (hne : h ≠ 0) :
    ∃ g, (h : HeckeAlgebra μ) g ≠ 0 := by
  by_contra hall
  push Not at hall
  exact hne (HeckeAlgebraLevel.ext _ _ (HeckeAlgebra.ext fun x => by
    rw [hall x, HeckeAlgebraLevel.val_zero, HeckeAlgebra.coe_zero, Pi.zero_apply]))

/- English proof (translation)
Take `⟨h, hh⟩` from `(AlgHom.mem_range _).1 (symmetricLaurent_le_range (μ := μ) (orbitSum_mem ν))`. Establish `key : ∀ g₁, (h : HeckeAlgebra μ) g₁ ≠ 0 → (∀ g, (h : HeckeAlgebra μ) g ≠ 0 → DomLE (cartanType F n g₁) (cartanType F n g) → cartanType F n g = cartanType F n g₁) → cartanType F n g₁ = ν`. Introduce `g₁ h1 hmax`. Establish `hc : (h : HeckeAlgebra μ) (Cartan.diagPow F n (cartanType F n g₁)) ≠ 0`. Rewrite using `[← apply_eq_apply_cartanType]` and apply the resulting hypothesis.

Establish `hco` using `coeff_satake_ne_zero_of_maximal hc hmax`. Establish `hco' : (orbitSum ν).coeff (cartanType F n g₁) ≠ 0`. Rewrite using `[← hh, coeff_satakeTransform]`. Conclude with `mul_ne_zero (halfModulus_ne_zero _) hco`. Take `⟨σ, hσ⟩` from `exists_of_coeff_orbitSum_ne_zero hco'`.

Establish `ha : Antitone (ν ∘ σ.symm)`. Rewrite using `[hσ]`. Conclude with `(cartanType_spec g₁).1`. Rewrite using `[← hσ]`. Conclude with `comp_eq_of_antitone hν σ.symm ha`.

Use `⟨h, hh, fun g hg => ?_, ?_⟩` and prove the remaining obligations. Take `⟨g₁, h1, hd, hmax⟩` from `exists_maximal hg`. Rewrite using `[← key g₁ h1 hmax]`. Conclude with `hd`. Establish `hne : h ≠ 0` using `fun h0 => orbitSum_ne_zero ν (by rw [← hh, h0, map_zero])`.

Take `⟨g, hg⟩` from `exists_apply_ne_zero hne`. Take `⟨g₁, h1, -, hmax⟩` from `exists_maximal hg`. Use `key g₁ h1 hmax` as an intermediate fact. Rewrite `h1` using `[apply_eq_apply_cartanType, this]`. Then use the resulting hypothesis.
-/
theorem exists_orbitSum_preimage {ν : Fin n → ℤ} (hν : Cartan.IsDominant ν) :
    ∃ h : SphericalHecke μ (F := F) (n := n), satakeTransform μ h = orbitSum ν ∧
      (∀ g, (h : HeckeAlgebra μ) g ≠ 0 → DomLE (cartanType F n g) ν) ∧
      (h : HeckeAlgebra μ) (Cartan.diagPow F n ν) ≠ 0 := by
  obtain ⟨h, hh⟩ := (AlgHom.mem_range _).1 (symmetricLaurent_le_range (μ := μ) (orbitSum_mem ν))
  have key : ∀ g₁, (h : HeckeAlgebra μ) g₁ ≠ 0 →
      (∀ g, (h : HeckeAlgebra μ) g ≠ 0 → DomLE (cartanType F n g₁) (cartanType F n g) →
        cartanType F n g = cartanType F n g₁) → cartanType F n g₁ = ν := by
    intro g₁ h1 hmax
    have hc : (h : HeckeAlgebra μ) (Cartan.diagPow F n (cartanType F n g₁)) ≠ 0 := by
      rwa [← apply_eq_apply_cartanType]
    have hco := coeff_satake_ne_zero_of_maximal hc hmax
    have hco' : (orbitSum ν).coeff (cartanType F n g₁) ≠ 0 := by
      rw [← hh, coeff_satakeTransform]
      exact mul_ne_zero (halfModulus_ne_zero _) hco
    obtain ⟨σ, hσ⟩ := exists_of_coeff_orbitSum_ne_zero hco'
    have ha : Antitone (ν ∘ σ.symm) := by
      rw [hσ]
      exact (cartanType_spec g₁).1
    rw [← hσ]
    exact comp_eq_of_antitone hν σ.symm ha
  refine ⟨h, hh, fun g hg => ?_, ?_⟩
  · obtain ⟨g₁, h1, hd, hmax⟩ := exists_maximal hg
    rw [← key g₁ h1 hmax]
    exact hd
  · have hne : h ≠ 0 := fun h0 => orbitSum_ne_zero ν (by rw [← hh, h0, map_zero])
    obtain ⟨g, hg⟩ := exists_apply_ne_zero hne
    obtain ⟨g₁, h1, -, hmax⟩ := exists_maximal hg
    have := key g₁ h1 hmax
    rwa [apply_eq_apply_cartanType, this] at h1

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih => simp [Finset.sum_insert ha, ih]`.
-/
theorem apply_sum {ι : Type*} (s : Finset ι) (f : ι → SphericalHecke μ (F := F) (n := n))
    (g : GL (Fin n) F) :
    ((∑ i ∈ s, f i : SphericalHecke μ (F := F) (n := n)) : HeckeAlgebra μ) g =
      ∑ i ∈ s, (f i : HeckeAlgebra μ) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

/- English proof (translation)
It suffices to establish `H : ∀ k : ℕ, ∀ h : SphericalHecke μ (F` using `F) (n := n), (∀ g, (h : HeckeAlgebra μ) g ≠ 0 → defect (cartanType F n g) < k) → satakeTransform μ h ∈ symmetricLaurent n by`. Use `H (((cosetSupport h).sup fun x => (defect (cartanType F n x.out)).toNat) + 1) h fun g hg => ?_` and prove the remaining obligations. Establish `h1` using `Finset.le_sup (f := fun x : GL (Fin n) F ⧸ integralGL F n => (defect (cartanType F n x.out)).toNat) (mk_mem_cosetSupport hg)`. Simplify using `only [cartanType_out] at h1`. Establish `h2` using `Int.self_le_toNat (defect (cartanType F n g))`.

Use linear arithmetic over natural numbers and integers. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `h hh`.

Establish `h0 : h = 0`. Assume the negation of the conclusion as `hne`. Take `⟨g, hg⟩` from `exists_apply_ne_zero hne`. Use `hh g hg` as an intermediate fact. Use `defect_nonneg (cartanType_spec g).1` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite using `[h0, map_zero]`. Conclude with `Subalgebra.zero_mem _`. Consider the case `succ k ih`. Introduce `h hh`.

Use `set Top : Finset (Fin n → ℤ) := ((cosetSupport h).filter fun x => (h : HeckeAlgebra μ) x.out ≠ 0 ∧ defect (cartanType F n x.out) = k).image fun x => cartanType F n x.out`. Establish `hTop : ∀ ν ∈ Top, Cartan.IsDominant ν ∧ defect ν = k`. Introduce `ν hν`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.1 hν`. Conclude with `⟨(cartanType_spec x.out).1, (Finset.mem_filter.1 hx).2.2⟩`.

Use `choose! H hHs hHle hHne using fun ν (hν : ν ∈ Top) => exists_orbitSum_preimage (μ := μ) (hTop ν hν).1`. Use `set c : (Fin n → ℤ) → ℂ := fun ν => (h : HeckeAlgebra μ) (Cartan.diagPow F n ν) / (H ν : HeckeAlgebra μ) (Cartan.diagPow F n ν)`. Use `set h' := h - ∑ ν ∈ Top, c ν • H ν`. Establish `hsum : satakeTransform μ (∑ ν ∈ Top, c ν • H ν) ∈ symmetricLaurent n`. Rewrite using `[map_sum]`.

Use `Subalgebra.sum_mem _ fun ν hν => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hHs ν hν]`. Conclude with `Subalgebra.smul_mem _ (orbitSum_mem ν) _`. Establish `hh' : ∀ g, (h' : HeckeAlgebra μ) g ≠ 0 → defect (cartanType F n g) < k`. Introduce `g hg`.

Assume the negation of the conclusion as `hge`. Use `push Not at hge`. Apply `hg` to reduce the goal to its premises. Establish `happ : (h' : HeckeAlgebra μ) g = (h : HeckeAlgebra μ) g - ∑ ν ∈ Top, c ν * (H ν : HeckeAlgebra μ) g`. Simplify using `only [h', HeckeAlgebraLevel.val_sub, HeckeAlgebra.coe_sub, Pi.sub_apply, apply_sum, HeckeAlgebraLevel.val_smul, HeckeAlgebra.coe_smul, Pi.smul_apply, smul_eq_mul]`.

Rewrite using `[happ]`. Establish `hzero : ∀ ν ∈ Top, ν ≠ cartanType F n g → (H ν : HeckeAlgebra μ) g = 0`. Introduce `ν hν hne`. Assume the negation of the conclusion as `hH`. Use `defect_lt (hHle ν hν g hH) (Ne.symm hne)` as an intermediate fact.

Rewrite `this` using `[(hTop ν hν).2]`. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `hmem : cartanType F n g ∈ Top`. Rewrite using `[Finset.sum_eq_single_of_mem _ hmem fun ν hν hne => by rw [hzero ν hν hne, mul_zero]]`. Rewrite using `[apply_eq_apply_cartanType h g, apply_eq_apply_cartanType (H (cartanType F n g)) g]`.

Simplify using `only [c]`. Rewrite using `[div_mul_cancel₀ _ (hHne _ hmem), sub_self]`. Rewrite using `[Finset.sum_eq_zero fun ν hν => by`. Rewrite using `[hzero ν hν fun he => hmem (he ▸ hν), mul_zero], sub_zero]`. Assume the negation of the conclusion as `hg0`.

Establish `hdef : defect (cartanType F n g) = k`. Use `hh g hg0` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `hmem (Finset.mem_image.2 ⟨QuotientGroup.mk g, Finset.mem_filter.2 ⟨mk_mem_cosetSupport hg0, by rw [apply_out]; exact hg0, by rw [cartanType_out]; exact hdef⟩, cartanType_out g⟩)`. Establish `heq : h = h' + ∑ ν ∈ Top, c ν • H ν`.

Simplify using `only [h', sub_add_cancel]`. Rewrite using `[heq, map_add]`. Conclude with `Subalgebra.add_mem _ (ih h' hh') hsum`.
-/
theorem satakeTransform_mem_symmetric (h : SphericalHecke μ (F := F) (n := n)) :
    satakeTransform μ h ∈ symmetricLaurent n := by
  classical
  suffices H : ∀ k : ℕ, ∀ h : SphericalHecke μ (F := F) (n := n),
      (∀ g, (h : HeckeAlgebra μ) g ≠ 0 → defect (cartanType F n g) < k) →
        satakeTransform μ h ∈ symmetricLaurent n by
    refine H (((cosetSupport h).sup fun x => (defect (cartanType F n x.out)).toNat) + 1) h
      fun g hg => ?_
    have h1 := Finset.le_sup (f := fun x : GL (Fin n) F ⧸ integralGL F n =>
      (defect (cartanType F n x.out)).toNat) (mk_mem_cosetSupport hg)
    simp only [cartanType_out] at h1
    have h2 := Int.self_le_toNat (defect (cartanType F n g))
    omega
  intro k
  induction k with
  | zero =>
    intro h hh
    have h0 : h = 0 := by
      by_contra hne
      obtain ⟨g, hg⟩ := exists_apply_ne_zero hne
      have := hh g hg
      have := defect_nonneg (cartanType_spec g).1
      omega
    rw [h0, map_zero]
    exact Subalgebra.zero_mem _
  | succ k ih =>
    intro h hh
    set Top : Finset (Fin n → ℤ) := ((cosetSupport h).filter fun x =>
      (h : HeckeAlgebra μ) x.out ≠ 0 ∧ defect (cartanType F n x.out) = k).image
        fun x => cartanType F n x.out
    have hTop : ∀ ν ∈ Top, Cartan.IsDominant ν ∧ defect ν = k := by
      intro ν hν
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hν
      exact ⟨(cartanType_spec x.out).1, (Finset.mem_filter.1 hx).2.2⟩
    choose! H hHs hHle hHne using fun ν (hν : ν ∈ Top) =>
      exists_orbitSum_preimage (μ := μ) (hTop ν hν).1
    set c : (Fin n → ℤ) → ℂ := fun ν =>
      (h : HeckeAlgebra μ) (Cartan.diagPow F n ν) / (H ν : HeckeAlgebra μ) (Cartan.diagPow F n ν)
    set h' := h - ∑ ν ∈ Top, c ν • H ν
    have hsum : satakeTransform μ (∑ ν ∈ Top, c ν • H ν) ∈ symmetricLaurent n := by
      rw [map_sum]
      refine Subalgebra.sum_mem _ fun ν hν => ?_
      rw [map_smul, hHs ν hν]
      exact Subalgebra.smul_mem _ (orbitSum_mem ν) _
    have hh' : ∀ g, (h' : HeckeAlgebra μ) g ≠ 0 → defect (cartanType F n g) < k := by
      intro g hg
      by_contra hge
      push Not at hge
      apply hg
      have happ : (h' : HeckeAlgebra μ) g =
          (h : HeckeAlgebra μ) g - ∑ ν ∈ Top, c ν * (H ν : HeckeAlgebra μ) g := by
        simp only [h', HeckeAlgebraLevel.val_sub, HeckeAlgebra.coe_sub, Pi.sub_apply, apply_sum,
          HeckeAlgebraLevel.val_smul, HeckeAlgebra.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [happ]
      have hzero : ∀ ν ∈ Top, ν ≠ cartanType F n g → (H ν : HeckeAlgebra μ) g = 0 := by
        intro ν hν hne
        by_contra hH
        have := defect_lt (hHle ν hν g hH) (Ne.symm hne)
        rw [(hTop ν hν).2] at this
        omega
      by_cases hmem : cartanType F n g ∈ Top
      · rw [Finset.sum_eq_single_of_mem _ hmem fun ν hν hne => by rw [hzero ν hν hne, mul_zero]]
        rw [apply_eq_apply_cartanType h g, apply_eq_apply_cartanType (H (cartanType F n g)) g]
        simp only [c]
        rw [div_mul_cancel₀ _ (hHne _ hmem), sub_self]
      · rw [Finset.sum_eq_zero fun ν hν => by
          rw [hzero ν hν fun he => hmem (he ▸ hν), mul_zero], sub_zero]
        by_contra hg0
        have hdef : defect (cartanType F n g) = k := by
          have := hh g hg0
          omega
        exact hmem (Finset.mem_image.2 ⟨QuotientGroup.mk g, Finset.mem_filter.2
          ⟨mk_mem_cosetSupport hg0, by rw [apply_out]; exact hg0, by rw [cartanType_out]; exact hdef⟩,
          cartanType_out g⟩)
    have heq : h = h' + ∑ ν ∈ Top, c ν • H ν := by
      simp only [h', sub_add_cancel]
    rw [heq, map_add]
    exact Subalgebra.add_mem _ (ih h' hh') hsum

end Spherical

end GroundTheory.Automorphic
