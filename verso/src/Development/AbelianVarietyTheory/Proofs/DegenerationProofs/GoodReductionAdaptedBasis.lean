import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CoeffSymmSum
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPartPartSec
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueIsRatio
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdaptedBasisTermsAtOtherClassMembersStatement
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.RedGood

/- English proof (translation)
Rewrite using `[← WtLin.weight_sum Φ F a α l, ← h l]`. Both sides reduce to the same expression.
-/
theorem wt_lin {k : Type} [Field k] (Φ : FibPre k) {d : ℕ} {J : Type} [Fintype J]
    {F : J → (Φ.H d).Sec} {a : J → k} {φ : (Φ.H d).Sec} (h : IsLin Φ.G.hom F a φ) (α : Φ.E.X)
    (l : Φ.N₀.ι) : Φ.wt φ α l = ∑ i, constFn Φ.E.B.hom _ (a i) * Φ.wt (F i) α l := by
  rw [← WtLin.weight_sum Φ F a α l, ← h l]
  rfl

/- English proof (translation)
Simplify using `only [constFn, map_zero]`.
-/
theorem constFn_zero {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) (U : X.Opens) :
    constFn f U 0 = 0 := by
  simp only [constFn, map_zero]

/- English proof (translation)
Establish `hcls : ∀ i₀ i α, (∃ m, α = cls i₀ + N • m) → (∃ m, α = cls i + N • m) → cls i = cls i₀`. Introduce and unpack `i₀ i α ⟨m, hm⟩ ⟨m', hm'⟩`. Use `uniq i i₀ ⟨m - m', ?_⟩` and prove the remaining obligations. Rewrite using `[smul_sub, ← add_sub_assoc, ← hm, hm', add_sub_cancel_right]`. Establish `hsum : ∀ (i₀ : J) (α : Φ.E.X) (a : J → k), (∀ i, a i ≠ 0 → cls i = cls i₀) → ∀ l, ∑ i, constFn Φ.E.B.hom _ (a i) * Φ.wt (F i) α l = ∑ i : {i // cls i = cls i₀}, constFn Φ.E.B.hom _ (a i) * Φ.wt (R i α) α l`.

Introduce `i₀ α a ha l`. Rewrite using `[← Finset.sum_subtype (Finset.univ.filter fun i => cls i = cls i₀) (by simp) (fun i => constFn Φ.E.B.hom _ (a i) * Φ.wt (R i α) α l), Finset.sum_filter]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `split_ifs with hi`. Rewrite using `[(part i α).2 l]`.

Establish `: a i = 0`. Assume the negation of the conclusion as `h`. Conclude with `hi (ha i h)`. Rewrite using `[this, constFn_zero, zero_mul]`. Use `⟨pos, short, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `i β ⟨l, hl⟩`. Assume the negation of the conclusion as `h`. Conclude with `hl (((part i β).2 l).symm.trans (zero i β h l))`. Introduce `α hα φ hφ`. Take `⟨i₀, hm⟩` from `cover α`.

Take `⟨a, ha, -⟩` from `basis i₀ α hα hm φ hφ`. Establish `key : ∀ i, (if h : cls i = cls i₀ then a ⟨i, h⟩ else 0) ≠ 0 → cls i = cls i₀`. Introduce `i hi`. Assume the negation of the conclusion as `h`. Conclude with `hi (dif_neg h)`.

Use `⟨fun i => if h : cls i = cls i₀ then a ⟨i, h⟩ else 0, fun i hi => ?_, fun l => ?_⟩` and prove the remaining obligations. Rewrite using `[key i hi]`. Conclude with `hm`. Rewrite using `[hsum i₀ α _ key l, wt_lin Φ ha α l]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[dif_pos i.2]`. Introduce `α hα a ha h0`. Take `⟨i₀, hm⟩` from `cover α`. Establish `key : ∀ i, a i ≠ 0 → cls i = cls i₀` using `fun i hi => hcls i₀ i α hm (ha i hi)`. Establish `hl` using `(GlobalTheory.SecRatio.ratio_and_lin _ _ (Φ.H_isLB 1)).2 k Φ.G.hom {i // cls i = cls i₀} (fun i => R i α)`.

Take `⟨φ, hφ, -⟩` from `hl (fun i => a i)`. Take `⟨φ₀, hφ₀, -⟩` from `hl 0`. Establish `hz₀ : ∀ β l, Φ.wt φ₀ β l = 0` using `fun β l => by`. Rewrite using `[wt_lin Φ hφ₀ β l]`. Conclude with `Finset.sum_eq_zero fun i _ => by rw [Pi.zero_apply, constFn_zero, zero_mul]`.

Establish `hz : ∀ β l, Φ.wt φ β l = 0` using `fun β l => by`. Rewrite using `[wt_lin Φ hφ β l]`. Distinguish the cases in `hβ : β = α`. Substitute `hβ` using the available equality. Rewrite using `[← hsum i₀ β a key l, h0 l]`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Establish `: Φ.wt (R i α) β l = 0`. Assume the negation of the conclusion as `h`. Conclude with `hβ ((part i α).1 ⟨l, h⟩)`. Rewrite using `[this, mul_zero]`.

Establish `e : φ = φ₀` using `WtPart.sec_ext Φ φ φ₀ fun β l => (hz β l).trans (hz₀ β l).symm`. Substitute `e` using the available equality. Establish `hu` using `(basis i₀ α hα hm φ (by rintro β ⟨l, hl⟩; exact absurd (hz β l) hl)).unique hφ hφ₀`. Use function extensionality and compare the values at `i`. Assume the negation of the conclusion as `h`.

Conclude with `h (congrFun hu ⟨i, key i h⟩)`.
-/
theorem good_of_parts {k : Type} [Field k] (Φ : FibPre k) (N : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ)
    {J : Type} [Fintype J] (cls : J → Φ.E.X) (F : J → (Φ.H 1).Sec) (R : J → Φ.E.X → (Φ.H 1).Sec)
    (pos : Filter.Tendsto q Filter.cofinite Filter.atTop) (short : ∀ i, Short q N (cls i))
    (uniq : ∀ i i', (∃ m, cls i = cls i' + N • m) → cls i = cls i')
    (cover : ∀ α, ∃ i m, α = cls i + N • m)
    (part : ∀ i α, Φ.IsPart α (F i) (R i α))
    (zero : ∀ i α, ¬ (Short q N α ∧ ∃ m, α = cls i + N • m) → ∀ l, Φ.wt (R i α) α l = 0)
    (basis : ∀ i₀ α, Short q N α → (∃ m, α = cls i₀ + N • m) → ∀ φ : (Φ.H 1).Sec, Φ.Pure α φ →
      ∃! a : {i // cls i = cls i₀} → k, IsLin Φ.G.hom (fun i : {i // cls i = cls i₀} => R i α) a φ) :
    Φ.Good N q cls F := by
  have hcls : ∀ i₀ i α, (∃ m, α = cls i₀ + N • m) → (∃ m, α = cls i + N • m) → cls i = cls i₀ := by
    rintro i₀ i α ⟨m, hm⟩ ⟨m', hm'⟩
    refine uniq i i₀ ⟨m - m', ?_⟩
    rw [smul_sub, ← add_sub_assoc, ← hm, hm', add_sub_cancel_right]
  have hsum : ∀ (i₀ : J) (α : Φ.E.X) (a : J → k), (∀ i, a i ≠ 0 → cls i = cls i₀) → ∀ l,
      ∑ i, constFn Φ.E.B.hom _ (a i) * Φ.wt (F i) α l =
        ∑ i : {i // cls i = cls i₀}, constFn Φ.E.B.hom _ (a i) * Φ.wt (R i α) α l := by
    intro i₀ α a ha l
    rw [← Finset.sum_subtype (Finset.univ.filter fun i => cls i = cls i₀) (by simp)
      (fun i => constFn Φ.E.B.hom _ (a i) * Φ.wt (R i α) α l), Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hi
    · rw [(part i α).2 l]
    · have : a i = 0 := by
        by_contra h
        exact hi (ha i h)
      rw [this, constFn_zero, zero_mul]
  refine ⟨pos, short, ?_, ?_, ?_⟩
  · rintro i β ⟨l, hl⟩
    by_contra h
    exact hl (((part i β).2 l).symm.trans (zero i β h l))
  · intro α hα φ hφ
    obtain ⟨i₀, hm⟩ := cover α
    obtain ⟨a, ha, -⟩ := basis i₀ α hα hm φ hφ
    have key : ∀ i, (if h : cls i = cls i₀ then a ⟨i, h⟩ else 0) ≠ 0 → cls i = cls i₀ := by
      intro i hi
      by_contra h
      exact hi (dif_neg h)
    refine ⟨fun i => if h : cls i = cls i₀ then a ⟨i, h⟩ else 0, fun i hi => ?_, fun l => ?_⟩
    · rw [key i hi]
      exact hm
    · rw [hsum i₀ α _ key l, wt_lin Φ ha α l]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [dif_pos i.2]
  · intro α hα a ha h0
    obtain ⟨i₀, hm⟩ := cover α
    have key : ∀ i, a i ≠ 0 → cls i = cls i₀ := fun i hi => hcls i₀ i α hm (ha i hi)
    have hl := (GlobalTheory.SecRatio.ratio_and_lin _ _ (Φ.H_isLB 1)).2 k Φ.G.hom {i // cls i = cls i₀}
      (fun i => R i α)
    obtain ⟨φ, hφ, -⟩ := hl (fun i => a i)
    obtain ⟨φ₀, hφ₀, -⟩ := hl 0
    have hz₀ : ∀ β l, Φ.wt φ₀ β l = 0 := fun β l => by
      rw [wt_lin Φ hφ₀ β l]
      exact Finset.sum_eq_zero fun i _ => by rw [Pi.zero_apply, constFn_zero, zero_mul]
    have hz : ∀ β l, Φ.wt φ β l = 0 := fun β l => by
      rw [wt_lin Φ hφ β l]
      by_cases hβ : β = α
      · subst hβ
        rw [← hsum i₀ β a key l, h0 l]
      · refine Finset.sum_eq_zero fun i _ => ?_
        have : Φ.wt (R i α) β l = 0 := by
          by_contra h
          exact hβ ((part i α).1 ⟨l, h⟩)
        rw [this, mul_zero]
    have e : φ = φ₀ := WtPart.sec_ext Φ φ φ₀ fun β l => (hz β l).trans (hz₀ β l).symm
    subst e
    have hu := (basis i₀ α hα hm φ (by rintro β ⟨l, hl⟩; exact absurd (hz β l) hl)).unique hφ hφ₀
    funext i
    by_contra h
    exact h (congrFun hu ⟨i, key i h⟩)

/- English proof (translation)
Rewrite using `[IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Take `⟨b, hb⟩` from `hu.exists_right_inv`. Establish `hb' : algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) a) * (b : PadicAlgCl p) = 1` using `congrArg Subtype.val hb`. Establish `h0 : algebraMap u.V (FractionRing u.V) a ≠ 0`.

Introduce `h`. Rewrite `hb'` using `[h, map_zero, zero_mul]`. Conclude with `zero_ne_one hb'`. Establish `hn : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) a)⁻¹‖ ≤ 1`. Rewrite using `[map_inv₀, ← eq_inv_of_mul_eq_one_right hb']`.

Conclude with `(mem_OO_iff _).1 b.2`. Take `⟨c, hc⟩` from `(u.norm_le _).1 hn`. Use `ha (IsUnit.of_mul_eq_one c (IsFractionRing.injective u.V (FractionRing u.V) ?_))` and prove the remaining obligations. Rewrite using `[map_mul, hc, map_one, mul_inv_cancel₀ h0]`.
-/
theorem residue_j_eq_zero {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
    {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) {a : u.V}
    (ha : a ∈ IsLocalRing.maximalIdeal u.V) : IsLocalRing.residue (OO p) (u.j a) = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨b, hb⟩ := hu.exists_right_inv
  have hb' : algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) a) *
      (b : PadicAlgCl p) = 1 := congrArg Subtype.val hb
  have h0 : algebraMap u.V (FractionRing u.V) a ≠ 0 := by
    intro h
    rw [h, map_zero, zero_mul] at hb'
    exact zero_ne_one hb'
  have hn : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) a)⁻¹‖ ≤ 1 := by
    rw [map_inv₀, ← eq_inv_of_mul_eq_one_right hb']
    exact (mem_OO_iff _).1 b.2
  obtain ⟨c, hc⟩ := (u.norm_le _).1 hn
  refine ha (IsUnit.of_mul_eq_one c (IsFractionRing.injective u.V (FractionRing u.V) ?_))
  rw [map_mul, hc, map_one, mul_inv_cancel₀ h0]

/- English proof (translation)
Introduce `hL o Ω _ _ _ _ S ρ p _ y₀ u l N fb hN J _ σ cls f hB F hF`. Establish `hsh` using `GlobalTheory.T.adaptedBasis_terms_at_other_class_members hL o Ω S ρ p y₀ u l N hN J σ cls f hB`. Take `⟨hshort, huniq, hcover, -, -, hzero, -⟩` from `hB`. Establish `hS : ∀ α : fb.Φ.E.X, Short (l.q.comp fb.xe.toIntLinearEquiv.toLinearMap) N α ↔ Short l.q N (fb.xe α)`. Introduce `α`.

Prove the components needed by the constructor for the conclusion. Introduce `h m`. Simplify using `using h (fb.xe.symm m)`. Introduce `h m`. Simplify using `using h (fb.xe m)`.

Establish `hC : ∀ (α : fb.Φ.E.X) (c : u.D.toPre.X), (∃ m, α = fb.xe.symm c + N • m) ↔ ∃ m, fb.xe α = c + N • m`. Introduce `α c`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, rfl⟩`. Conclude with `⟨fb.xe m, by simp⟩`.

Introduce and unpack `⟨m, hm⟩`. Conclude with `⟨fb.xe.symm m, fb.xe.injective (by simp [hm])⟩`. Use `good_of_parts fb.Φ N _ _ F (fun i α => fb.red (fb.xe α) (f i (fb.xe α))) ?_ ?_ ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Conclude with `l.pos.comp fb.xe.injective.tendsto_cofinite`. Introduce `i`.

Rewrite using `[hS, fb.xe.apply_symm_apply]`. Conclude with `hshort i`. Introduce `i i' h`. Rewrite `h` using `[hC, fb.xe.apply_symm_apply]`. Rewrite using `[huniq i i' h]`.

Introduce `α`. Take `⟨i, h⟩` from `hcover (fb.xe α)`. Conclude with `⟨i, (hC _ _).2 h⟩`. Introduce `i α`. Use `hF i (fb.xe α)` as an intermediate fact.

Rewrite `this` using `[fb.xe.symm_apply_apply]`. Then use the resulting hypothesis. Introduce `i α h j`. Rewrite `h` using `[hS, hC]`. Distinguish the cases in `hc : ∃ m, fb.xe α = cls i + N • m`. Take `⟨a, β, ha, hβ⟩` from `(hsh i _ hc).2 fun hs => h ⟨hs, hc⟩`.

Use `fb.lin _ Unit (fun _ => β) (fun _ => a) (f i (fb.xe α)) (fun j => by` as an intermediate fact. Rewrite using `[hβ j, Fintype.sum_unique])`. Rewrite using `[wt_lin fb.Φ this α j, Fintype.sum_unique, residue_j_eq_zero u ha, constFn_zero, zero_mul]`. Use `fb.lin _ Empty Empty.elim Empty.elim (f i (fb.xe α)) (fun j => by` as an intermediate fact. Rewrite using `[hzero i _ (fun m e => hc ⟨m, e⟩) j, Fintype.sum_empty])`.

Rewrite using `[wt_lin fb.Φ this α j, Fintype.sum_empty]`. Introduce `i₀ α hα hc φ hφ`. Rewrite `hα` using `[hS]`. Rewrite `hc` using `[hC]`. Establish `hb` using `fb.basis _ _ _ ((hsh i₀ _ hc).1 hα) φ (by rwa [fb.xe.symm_apply_apply])`.

Set `e : {i // cls i = cls i₀} ≃ {i // fb.xe.symm (cls i) = fb.xe.symm (cls i₀)}` to `Equiv.subtypeEquivRight fun i => fb.xe.symm.injective.eq_iff.symm`. Establish `hlin : ∀ a : {i // fb.xe.symm (cls i) = fb.xe.symm (cls i₀)} → kb p, IsLin fb.Φ.G.hom (fun i : {i // fb.xe.symm (cls i) = fb.xe.symm (cls i₀)} => fb.red (fb.xe α) (f i (fb.xe α))) a φ ↔ IsLin fb.Φ.G.hom (fun i : {i // cls i = cls i₀} => fb.red (fb.xe α) (f i (fb.xe α))) (a ∘ e) φ`. Introduce `a`. Use `forall_congr' fun j => ?_` and prove the remaining obligations. Rewrite using `[← e.sum_comp]`.

Both sides reduce to the same expression. Take `⟨a, ha, hu⟩` from `hb`. Use `⟨a ∘ e.symm, (hlin _).2 ?_, fun b hb => ?_⟩` and prove the remaining obligations. Establish `: (a ∘ e.symm) ∘ e = a`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `ha`. Rewrite using `[← hu _ ((hlin b).1 hb)]`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules.
-/
theorem good_reduction : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (N : ℕ) (fb : u.FibOf N), 1 ≤ N → ∀ (J : Type) [Fintype J] (σ : J → (u.H N).Sec) (cls : J → u.D.toPre.X) (f : J → ∀ α, u.D.toPre.SecB N α), u.Basis l N σ cls f → ∀ F : J → (fb.Φ.H 1).Sec, (∀ i α, fb.Φ.IsPart (fb.xe.symm α) (F i) (fb.red α (f i α))) → fb.Φ.Good N (l.q.comp fb.xe.toIntLinearEquiv.toLinearMap) (fun i => fb.xe.symm (cls i)) F := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u l N fb hN J _ σ cls f hB F hF
  have hsh := GlobalTheory.T.adaptedBasis_terms_at_other_class_members hL o Ω S ρ p y₀ u l N hN J σ cls f hB
  obtain ⟨hshort, huniq, hcover, -, -, hzero, -⟩ := hB
  have hS : ∀ α : fb.Φ.E.X, Short (l.q.comp fb.xe.toIntLinearEquiv.toLinearMap) N α ↔ Short l.q N (fb.xe α) := by
    intro α
    constructor
    · intro h m
      simpa using h (fb.xe.symm m)
    · intro h m
      simpa using h (fb.xe m)
  have hC : ∀ (α : fb.Φ.E.X) (c : u.D.toPre.X),
      (∃ m, α = fb.xe.symm c + N • m) ↔ ∃ m, fb.xe α = c + N • m := by
    intro α c
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨fb.xe m, by simp⟩
    · rintro ⟨m, hm⟩
      exact ⟨fb.xe.symm m, fb.xe.injective (by simp [hm])⟩
  refine good_of_parts fb.Φ N _ _ F (fun i α => fb.red (fb.xe α) (f i (fb.xe α))) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact l.pos.comp fb.xe.injective.tendsto_cofinite
  · intro i
    rw [hS, fb.xe.apply_symm_apply]
    exact hshort i
  · intro i i' h
    rw [hC, fb.xe.apply_symm_apply] at h
    rw [huniq i i' h]
  · intro α
    obtain ⟨i, h⟩ := hcover (fb.xe α)
    exact ⟨i, (hC _ _).2 h⟩
  · intro i α
    have := hF i (fb.xe α)
    rwa [fb.xe.symm_apply_apply] at this
  · intro i α h j
    rw [hS, hC] at h
    by_cases hc : ∃ m, fb.xe α = cls i + N • m
    · obtain ⟨a, β, ha, hβ⟩ := (hsh i _ hc).2 fun hs => h ⟨hs, hc⟩
      have := fb.lin _ Unit (fun _ => β) (fun _ => a) (f i (fb.xe α)) (fun j => by
        rw [hβ j, Fintype.sum_unique])
      rw [wt_lin fb.Φ this α j, Fintype.sum_unique, residue_j_eq_zero u ha, constFn_zero, zero_mul]
    · have := fb.lin _ Empty Empty.elim Empty.elim (f i (fb.xe α)) (fun j => by
        rw [hzero i _ (fun m e => hc ⟨m, e⟩) j, Fintype.sum_empty])
      rw [wt_lin fb.Φ this α j, Fintype.sum_empty]
  · intro i₀ α hα hc φ hφ
    rw [hS] at hα
    rw [hC] at hc
    have hb := fb.basis _ _ _ ((hsh i₀ _ hc).1 hα) φ (by rwa [fb.xe.symm_apply_apply])
    let e : {i // cls i = cls i₀} ≃ {i // fb.xe.symm (cls i) = fb.xe.symm (cls i₀)} :=
      Equiv.subtypeEquivRight fun i => fb.xe.symm.injective.eq_iff.symm
    have hlin : ∀ a : {i // fb.xe.symm (cls i) = fb.xe.symm (cls i₀)} → kb p,
        IsLin fb.Φ.G.hom (fun i : {i // fb.xe.symm (cls i) = fb.xe.symm (cls i₀)} =>
          fb.red (fb.xe α) (f i (fb.xe α))) a φ ↔
        IsLin fb.Φ.G.hom (fun i : {i // cls i = cls i₀} => fb.red (fb.xe α) (f i (fb.xe α))) (a ∘ e) φ := by
      intro a
      refine forall_congr' fun j => ?_
      rw [← e.sum_comp]
      rfl
    obtain ⟨a, ha, hu⟩ := hb
    refine ⟨a ∘ e.symm, (hlin _).2 ?_, fun b hb => ?_⟩
    · have : (a ∘ e.symm) ∘ e = a := by
        funext i
        simp
      rw [this]
      exact ha
    · rw [← hu _ ((hlin b).1 hb)]
      funext i
      simp

end GlobalTheory.ZH.RedGood
end
