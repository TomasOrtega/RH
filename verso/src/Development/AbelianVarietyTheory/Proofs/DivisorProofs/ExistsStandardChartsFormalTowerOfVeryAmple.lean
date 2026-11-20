import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsAffineOpenPreimageEqOfIsNilpotent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg.ChartsEx

section Level0

variable {X : Scheme.{0}} {H : LB X}

/- English proof (translation)
Take `⟨l, hl⟩` from `TopologicalSpace.Opens.mem_iSup.1 hx`. Conclude with `⟨l, X.basicOpen_le _ hl⟩`.
-/
theorem exists_chart_of_mem_nonzeroLocus (s : LB.Sec H) {x : X} (hx : x ∈ nonzeroLocus s) :
    ∃ k, x ∈ H.U k := by
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  exact ⟨l, X.basicOpen_le _ hl⟩

/- English proof (translation)
Use `⟨fun hx => ?_, fun hx => TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx⟩⟩` and prove the remaining obligations. Take `⟨l, hl⟩` from `TopologicalSpace.Opens.mem_iSup.1 hx`. Establish `e` using `congrArg X.basicOpen (s.compat k l)`. Rewrite `e` using `[Scheme.basicOpen_mul, X.basicOpen_of_isUnit (H.g k l).isUnit]`. Use `erw [Scheme.basicOpen_res, Scheme.basicOpen_res] at e`.

Establish `hx' : x ∈ H.U k ⊓ H.U l` using `⟨hk, X.basicOpen_le _ hl⟩`. Conclude with `(e.ge ⟨hx', hx', hl⟩).2`.
-/
theorem mem_nonzeroLocus_iff_basicOpen (s : LB.Sec H) (k : H.ι) {x : X} (hk : x ∈ H.U k) :
    x ∈ nonzeroLocus s ↔ x ∈ X.basicOpen (s.f k) := by
  refine ⟨fun hx => ?_, fun hx => TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx⟩⟩
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have e := congrArg X.basicOpen (s.compat k l)
  rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit (H.g k l).isUnit] at e
  erw [Scheme.basicOpen_res, Scheme.basicOpen_res] at e
  have hx' : x ∈ H.U k ⊓ H.U l := ⟨hk, X.basicOpen_le _ hl⟩
  exact (e.ge ⟨hx', hx', hl⟩).2

/- English proof (translation)
Establish `hb : O ≤ X.basicOpen (s.f k)` using `fun x hx => (mem_nonzeroLocus_iff_basicOpen s k (hk hx)).1 (h hx)`. Establish `hu : IsUnit (rs X (X.basicOpen_le (s.f k)) (s.f k))` using `X.toRingedSpace.isUnit_res_basicOpen (s.f k)`. Simplify `hu.map (rs X hb)` using `only [rs_rs]`.
-/
theorem isUnit_rs (s : LB.Sec H) (k : H.ι) {O : X.Opens} (hk : O ≤ H.U k)
    (h : O ≤ nonzeroLocus s) : IsUnit (rs X hk (s.f k)) := by
  have hb : O ≤ X.basicOpen (s.f k) := fun x hx => (mem_nonzeroLocus_iff_basicOpen s k (hk hx)).1 (h hx)
  have hu : IsUnit (rs X (X.basicOpen_le (s.f k)) (s.f k)) :=
    X.toRingedSpace.isUnit_res_basicOpen (s.f k)
  simpa only [rs_rs] using hu.map (rs X hb)

/- English proof (translation)
Use `X.sheaf.eq_of_locally_eq' (fun k : H.ι => V ⊓ H.U k) V (fun k => homOfLE inf_le_left) (fun x hx => ?_) _ _ fun k => ?_` and prove the remaining obligations. Take `⟨l, hl⟩` from `exists_chart_of_mem_nonzeroLocus s (h hx)`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨l, hx, hl⟩`. Express the relevant statement in the definitionally equal form `rs X inf_le_left r = rs X inf_le_left 1`. Rewrite using `[map_one]`.

Conclude with `(isUnit_rs s k inf_le_right (inf_le_left.trans h)).mul_right_cancel ((hr k).symm.trans (_root_.one_mul _).symm)`.
-/
theorem ratio_self (s : LB.Sec H) {V : X.Opens} (h : V ≤ nonzeroLocus s) (r : Γ(X, V))
    (hr : ∀ k, rs X (inf_le_right : V ⊓ H.U k ≤ H.U k) (s.f k) =
      rs X (inf_le_left : V ⊓ H.U k ≤ V) r * rs X (inf_le_right : V ⊓ H.U k ≤ H.U k) (s.f k)) :
    r = 1 := by
  refine X.sheaf.eq_of_locally_eq' (fun k : H.ι => V ⊓ H.U k) V (fun k => homOfLE inf_le_left)
    (fun x hx => ?_) _ _ fun k => ?_
  · obtain ⟨l, hl⟩ := exists_chart_of_mem_nonzeroLocus s (h hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨l, hx, hl⟩
  · change rs X inf_le_left r = rs X inf_le_left 1
    rw [map_one]
    exact (isUnit_rs s k inf_le_right (inf_le_left.trans h)).mul_right_cancel
      ((hr k).symm.trans (_root_.one_mul _).symm)

variable {n : ℕ} (s : Fin (n + 1) → LB.Sec H) (r : ∀ i, Fin (n + 1) → Γ(X, nonzeroLocus (s i)))
  (hr : ∀ i j k, rs X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s j).f k) =
    rs X (inf_le_left : nonzeroLocus (s i) ⊓ H.U k ≤ nonzeroLocus (s i)) (r i j) *
      rs X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s i).f k))

include hr in

/- English proof (translation)
Establish `key : ∀ k, (nonzeroLocus (s i) ⊓ H.U k) ⊓ X.basicOpen ((s j).f k) = (nonzeroLocus (s i) ⊓ H.U k) ⊓ X.basicOpen (r i j)`. Introduce `k`. Establish `e` using `congrArg X.basicOpen (hr i j k)`. Rewrite `e` using `[Scheme.basicOpen_mul, X.basicOpen_of_isUnit (isUnit_rs (s i) k inf_le_right inf_le_left)]`. Use `erw [Scheme.basicOpen_res, Scheme.basicOpen_res] at e`.

Rewrite using `[e, inf_assoc, inf_comm (X.basicOpen (r i j)), ← inf_assoc, inf_idem]`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `hxi : x ∈ nonzeroLocus (s i)` using `X.basicOpen_le _ hx`.

Take `⟨k, hk⟩` from `exists_chart_of_mem_nonzeroLocus (s i) hxi`. Establish `hm : x ∈ (nonzeroLocus (s i) ⊓ H.U k) ⊓ X.basicOpen (r i j)` using `⟨⟨hxi, hk⟩, hx⟩`. Rewrite `hm` using `[← key k]`. Conclude with `⟨hxi, TopologicalSpace.Opens.mem_iSup.2 ⟨k, hm.2⟩⟩`. Introduce and unpack `⟨hxi, hxj⟩`.

Take `⟨k, hk⟩` from `exists_chart_of_mem_nonzeroLocus (s i) hxi`. Establish `hm : x ∈ (nonzeroLocus (s i) ⊓ H.U k) ⊓ X.basicOpen ((s j).f k)` using `⟨⟨hxi, hk⟩, (mem_nonzeroLocus_iff_basicOpen (s j) k hk).1 hxj⟩`. Rewrite `hm` using `[key k]`. Conclude with `hm.2`.
-/
theorem basicOpen_ratio (i j : Fin (n + 1)) :
    X.basicOpen (r i j) = nonzeroLocus (s i) ⊓ nonzeroLocus (s j) := by
  have key : ∀ k, (nonzeroLocus (s i) ⊓ H.U k) ⊓ X.basicOpen ((s j).f k) =
      (nonzeroLocus (s i) ⊓ H.U k) ⊓ X.basicOpen (r i j) := by
    intro k
    have e := congrArg X.basicOpen (hr i j k)
    rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit (isUnit_rs (s i) k inf_le_right inf_le_left)] at e
    erw [Scheme.basicOpen_res, Scheme.basicOpen_res] at e
    rw [e, inf_assoc, inf_comm (X.basicOpen (r i j)), ← inf_assoc, inf_idem]
  ext x
  constructor
  · intro hx
    have hxi : x ∈ nonzeroLocus (s i) := X.basicOpen_le _ hx
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus (s i) hxi
    have hm : x ∈ (nonzeroLocus (s i) ⊓ H.U k) ⊓ X.basicOpen (r i j) := ⟨⟨hxi, hk⟩, hx⟩
    rw [← key k] at hm
    exact ⟨hxi, TopologicalSpace.Opens.mem_iSup.2 ⟨k, hm.2⟩⟩
  · rintro ⟨hxi, hxj⟩
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus (s i) hxi
    have hm : x ∈ (nonzeroLocus (s i) ⊓ H.U k) ⊓ X.basicOpen ((s j).f k) :=
      ⟨⟨hxi, hk⟩, (mem_nonzeroLocus_iff_basicOpen (s j) k hk).1 hxj⟩
    rw [key k] at hm
    exact hm.2

include hr in

/- English proof (translation)
Use `X.sheaf.eq_of_locally_eq' (fun k : H.ι => (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) ⊓ H.U k) (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) (fun k => homOfLE inf_le_left) (fun x hx => ?_) _ _ fun k => ?_` and prove the remaining obligations. Take `⟨l', hl⟩` from `exists_chart_of_mem_nonzeroLocus (s i) hx.1`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨l', hx, hl⟩`. Express the relevant statement in the definitionally equal form `rs X inf_le_left _ = rs X inf_le_left _`. Establish `hi : (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) ⊓ H.U k ≤ nonzeroLocus (s i) ⊓ H.U k` using `inf_le_inf_right _ inf_le_left`.

Establish `hj : (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) ⊓ H.U k ≤ nonzeroLocus (s j) ⊓ H.U k` using `inf_le_inf_right _ inf_le_right`. Establish `e1` using `congrArg (rs X hi) (hr i l k)`. Establish `e2` using `congrArg (rs X hi) (hr i j k)`. Establish `e3` using `congrArg (rs X hj) (hr j l k)`. Simplify using `only [map_mul, rs_rs] at e1 e2 e3 ⊢`.

Establish `hu` using `isUnit_rs (s i) k (inf_le_right : (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) ⊓ H.U k ≤ H.U k) (inf_le_left.trans inf_le_left)`. Use `hu.mul_right_cancel ?_` and prove the remaining obligations. Rewrite using `[← e1, e3, e2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ratio_cocycle (i j l : Fin (n + 1)) :
    rs X (inf_le_left : nonzeroLocus (s i) ⊓ nonzeroLocus (s j) ≤ nonzeroLocus (s i)) (r i l) =
      rs X (inf_le_left : nonzeroLocus (s i) ⊓ nonzeroLocus (s j) ≤ nonzeroLocus (s i)) (r i j) *
        rs X (inf_le_right : nonzeroLocus (s i) ⊓ nonzeroLocus (s j) ≤ nonzeroLocus (s j)) (r j l) := by
  refine X.sheaf.eq_of_locally_eq' (fun k : H.ι => (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) ⊓ H.U k)
    (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) (fun k => homOfLE inf_le_left) (fun x hx => ?_) _ _
    fun k => ?_
  · obtain ⟨l', hl⟩ := exists_chart_of_mem_nonzeroLocus (s i) hx.1
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨l', hx, hl⟩
  · change rs X inf_le_left _ = rs X inf_le_left _
    have hi : (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) ⊓ H.U k ≤ nonzeroLocus (s i) ⊓ H.U k :=
      inf_le_inf_right _ inf_le_left
    have hj : (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) ⊓ H.U k ≤ nonzeroLocus (s j) ⊓ H.U k :=
      inf_le_inf_right _ inf_le_right
    have e1 := congrArg (rs X hi) (hr i l k)
    have e2 := congrArg (rs X hi) (hr i j k)
    have e3 := congrArg (rs X hj) (hr j l k)
    simp only [map_mul, rs_rs] at e1 e2 e3 ⊢
    have hu := isUnit_rs (s i) k (inf_le_right : (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) ⊓ H.U k ≤ H.U k)
      (inf_le_left.trans inf_le_left)
    refine hu.mul_right_cancel ?_
    rw [← e1, e3, e2]
    ring

end Level0

end GlobalTheory.FormalAlg.ChartsEx

namespace GlobalTheory.FormalAlg.ChartsEx

section Tower

variable {R : Type} [CommRing R] {I : Ideal R}

/- English proof (translation)
Use `⟨fun x => ?_⟩` and prove the remaining obligations. Establish `h : I ^ (e + 1 + 1) ≤ I ^ (e + 1)` using `Ideal.pow_le_pow_right (by omega)`. Establish `hx : (x : PrimeSpectrum (R ⧸ I ^ (e + 1 + 1))) ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.factor h))`. Rewrite using `[_root_.range_comap_of_surjective _ _ (Ideal.Quotient.factor_surjective h)]`. Introduce `a ha`.

Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Establish `ha' : a ∈ I ^ (e + 1)`. Simplify `ha` using `[RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]`. Use `x.2.mem_of_pow_mem 2 ?_` and prove the remaining obligations. Establish `: Ideal.Quotient.mk (I ^ (e + 1 + 1)) a ^ 2 = 0`.

Rewrite using `[← map_pow, Ideal.Quotient.eq_zero_iff_mem]`. Use `Ideal.pow_le_pow_right (show e + 1 + 1 ≤ (e + 1) * 2 by omega) ?_` and prove the remaining obligations. Rewrite using `[pow_mul]`. Conclude with `Ideal.pow_mem_pow ha' 2`. Rewrite using `[this]`.

Conclude with `Ideal.zero_mem _`. Conclude with `hx`.
-/
theorem surjective_thickTrans (e : ℕ) : Surjective (thickTrans R I e) := by
  refine ⟨fun x => ?_⟩
  have h : I ^ (e + 1 + 1) ≤ I ^ (e + 1) := Ideal.pow_le_pow_right (by omega)
  have hx : (x : PrimeSpectrum (R ⧸ I ^ (e + 1 + 1))) ∈
      Set.range (PrimeSpectrum.comap (Ideal.Quotient.factor h)) := by
    rw [_root_.range_comap_of_surjective _ _ (Ideal.Quotient.factor_surjective h)]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have ha' : a ∈ I ^ (e + 1) := by
      simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using ha
    refine x.2.mem_of_pow_mem 2 ?_
    have : Ideal.Quotient.mk (I ^ (e + 1 + 1)) a ^ 2 = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      refine Ideal.pow_le_pow_right (show e + 1 + 1 ≤ (e + 1) * 2 by omega) ?_
      rw [pow_mul]
      exact Ideal.pow_mem_pow ha' 2
    rw [this]
    exact Ideal.zero_mem _
  exact hx

/- English proof (translation)
Use `⟨2, le_bot_iff.1 ?_⟩` and prove the remaining obligations. Rewrite using `[pow_two, Ideal.mul_le]`. Introduce `x hx y hy`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective y`.

Establish `ha : a ∈ I ^ (e + 1)` using `by simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using hx`. Establish `hb : b ∈ I ^ (e + 1)` using `by simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using hy`. Rewrite using `[← map_mul, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem]`. Use `Ideal.pow_le_pow_right (show e + 1 + 1 ≤ (e + 1) + (e + 1) by omega) ?_` and prove the remaining obligations. Rewrite using `[pow_add]`.

Conclude with `Ideal.mul_mem_mul ha hb`.
-/
theorem isNilpotent_ker_factor (e : ℕ) (h : I ^ (e + 1 + 1) ≤ I ^ (e + 1)) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factor h)) := by
  refine ⟨2, le_bot_iff.1 ?_⟩
  rw [pow_two, Ideal.mul_le]
  intro x hx y hy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  have ha : a ∈ I ^ (e + 1) := by simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using hx
  have hb : b ∈ I ^ (e + 1) := by simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using hy
  rw [← map_mul, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
  refine Ideal.pow_le_pow_right (show e + 1 + 1 ≤ (e + 1) + (e + 1) by omega) ?_
  rw [pow_add]
  exact Ideal.mul_mem_mul ha hb

variable {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
  {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left} {n : ℕ}

variable (Y n) in

abbrev Lvl (e : ℕ) : Type :=
  {p : (Σ D : Fin (n + 1) → (Y e).left.Opens, ∀ i, Fin (n + 1) → Γ((Y e).left, D i)) //
    ∀ i, IsAffineOpen (p.1 i)}

variable (β) in

def Lifts (e : ℕ) (q : Lvl Y n e) (q' : Lvl Y n (e + 1)) : Prop :=
  ∃ h : ∀ i, β e ⁻¹ᵁ q'.1.1 i = q.1.1 i,
    ∀ i j, ((β e).appLE (q'.1.1 i) (q.1.1 i) (h i).ge).hom (q'.1.2 i j) = q.1.2 i j

/- English proof (translation)
Establish `hle : I ^ (e + 1 + 1) ≤ I ^ (e + 1)` using `Ideal.pow_le_pow_right (by omega)`. Establish `hsurj : Function.Surjective (Ideal.Quotient.factor hle)` using `Ideal.Quotient.factor_surjective hle`. Establish `hD` using `fun i => GlobalTheory.AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent _ _ (Ideal.Quotient.factor hle) hsurj (isNilpotent_ker_factor e hle) _ _ (Y (e + 1)).hom (Y e).hom (β e) hsq (q.1.1 i) (q.2 i)`. Use `choose D' hD' hpre using hD`. Use `haveI : IsClosedImmersion (β e) := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip (IsClosedImmersion.spec_of_surjective _ hsurj)`.

Establish `hs : ∀ i, Function.Surjective ((β e).appLE (D' i) (q.1.1 i) (hpre i).ge).hom`. Introduce `i y`. Take `⟨x, hx⟩` from `(β e).app_surjective (D' i) (hD' i) (rs _ (hpre i).le y)`. Use `⟨x, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `rs _ (hpre i).ge (((β e).app (D' i)).hom x) = y`.

Rewrite using `[hx, rs_rs, rs_self]`. Use `choose ρ' hρ' using fun i j => hs i (q.1.2 i j)`. Conclude with `⟨⟨⟨D', ρ'⟩, hD'⟩, hpre, hρ'⟩`.
-/
theorem exists_lifts {e : ℕ} (hsq : IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (q : Lvl Y n e) : ∃ q' : Lvl Y n (e + 1), Lifts β e q q' := by
  have hle : I ^ (e + 1 + 1) ≤ I ^ (e + 1) := Ideal.pow_le_pow_right (by omega)
  have hsurj : Function.Surjective (Ideal.Quotient.factor hle) := Ideal.Quotient.factor_surjective hle
  have hD := fun i => GlobalTheory.AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent _ _
    (Ideal.Quotient.factor hle) hsurj (isNilpotent_ker_factor e hle) _ _ (Y (e + 1)).hom (Y e).hom
    (β e) hsq (q.1.1 i) (q.2 i)
  choose D' hD' hpre using hD
  haveI : IsClosedImmersion (β e) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip
      (IsClosedImmersion.spec_of_surjective _ hsurj)
  have hs : ∀ i, Function.Surjective ((β e).appLE (D' i) (q.1.1 i) (hpre i).ge).hom := by
    intro i y
    obtain ⟨x, hx⟩ := (β e).app_surjective (D' i) (hD' i) (rs _ (hpre i).le y)
    refine ⟨x, ?_⟩
    change rs _ (hpre i).ge (((β e).app (D' i)).hom x) = y
    rw [hx, rs_rs, rs_self]
  choose ρ' hρ' using fun i j => hs i (q.1.2 i j)
  exact ⟨⟨⟨D', ρ'⟩, hD'⟩, hpre, hρ'⟩

variable (β) in

def seq (hsq : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (q₀ : Lvl Y n 0) (e : ℕ) : Lvl Y n e :=
  Nat.rec (motive := Lvl Y n) q₀ (fun e q => Classical.choose (exists_lifts (hsq e) q)) e

/- English proof (translation)
The claim follows from `Classical.choose_spec (exists_lifts (hsq e) (seq β hsq q₀ e))`.
-/
theorem seq_lifts (hsq : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (q₀ : Lvl Y n 0) (e : ℕ) : Lifts β e (seq β hsq q₀ e) (seq β hsq q₀ (e + 1)) :=
  Classical.choose_spec (exists_lifts (hsq e) (seq β hsq q₀ e))

end Tower

end GlobalTheory.FormalAlg.ChartsEx

open GlobalTheory.FormalAlg.ChartsEx in

/- English proof (translation)
Introduce `R _ I Y β hsq H₀ n s₀ _ hva`. Take `⟨hcov, hloc⟩` from `hva`. Use `choose haff r hrel hsurj using hloc`. Set `q₀ : Lvl Y n 0` to `⟨⟨fun i => nonzeroLocus (s₀ i), r⟩, haff⟩`. Establish `hsurjβ : ∀ e, Surjective (β e)` using `fun e => MorphismProperty.of_isPullback (P := @Surjective) (hsq e).flip (surjective_thickTrans e)`.

Establish `hcover : ∀ e, ⨆ i, (seq β hsq q₀ e).1.1 i = ⊤`. Introduce `e`. Proceed by induction on `e with`. Consider the case `zero => exact hcov`. Consider the case `succ e ih`.

Take `⟨hpre, -⟩` from `seq_lifts hsq q₀ e`. Use `top_unique fun y _ => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `(hsurjβ e).surj y`. Establish `hx : x ∈ β e ⁻¹ᵁ (⨆ i, (seq β hsq q₀ (e + 1)).1.1 i)`. Rewrite using `[Scheme.Hom.preimage_iSup]`.

Simplify using `only [hpre]`. Rewrite using `[ih]`. Discharge the goal by the elementary cases of `trivial`. Conclude with `hx`. Use `⟨{ D := fun e => (seq β hsq q₀ e).1.1 aff := fun e => (seq β hsq q₀ e).2 cover := hcover pre := fun e => (seq_lifts hsq q₀ e).1 ρ := fun e => (seq β hsq q₀ e).1.2 ρ_pull := fun e => (seq_lifts hsq q₀ e).2 ρ_self := fun i => ratio_self (s₀ i) le_rfl (r i i) (hrel i i) basic := fun …` and prove the remaining obligations.
-/
theorem GlobalTheory.FormalAlg.exists_charts_of_veryAmpleBy : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H₀ : LB (Y 0).left) (n : ℕ) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → VeryAmpleBy (Y 0).hom H₀ s₀ → ∃ C : Charts I Y β n, (∀ i, C.D 0 i = nonzeroLocus (s₀ i)) ∧ ∀ i j (m : H₀.ι), rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ j).f m) = rs (Y 0).left (inf_le_left : C.D 0 i ⊓ H₀.U m ≤ C.D 0 i) (C.ρ 0 i j) * rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ i).f m) := by
  intro R _ I Y β hsq H₀ n s₀ _ hva
  obtain ⟨hcov, hloc⟩ := hva
  choose haff r hrel hsurj using hloc
  let q₀ : Lvl Y n 0 := ⟨⟨fun i => nonzeroLocus (s₀ i), r⟩, haff⟩
  have hsurjβ : ∀ e, Surjective (β e) := fun e =>
    MorphismProperty.of_isPullback (P := @Surjective) (hsq e).flip (surjective_thickTrans e)
  have hcover : ∀ e, ⨆ i, (seq β hsq q₀ e).1.1 i = ⊤ := by
    intro e
    induction e with
    | zero => exact hcov
    | succ e ih =>
      obtain ⟨hpre, -⟩ := seq_lifts hsq q₀ e
      refine top_unique fun y _ => ?_
      obtain ⟨x, rfl⟩ := (hsurjβ e).surj y
      have hx : x ∈ β e ⁻¹ᵁ (⨆ i, (seq β hsq q₀ (e + 1)).1.1 i) := by
        rw [Scheme.Hom.preimage_iSup]
        simp only [hpre]
        rw [ih]
        trivial
      exact hx
  refine ⟨{ D := fun e => (seq β hsq q₀ e).1.1
            aff := fun e => (seq β hsq q₀ e).2
            cover := hcover
            pre := fun e => (seq_lifts hsq q₀ e).1
            ρ := fun e => (seq β hsq q₀ e).1.2
            ρ_pull := fun e => (seq_lifts hsq q₀ e).2
            ρ_self := fun i => ratio_self (s₀ i) le_rfl (r i i) (hrel i i)
            basic := fun i j => basicOpen_ratio s₀ r hrel i j
            cocycle := fun i j l => ratio_cocycle s₀ r hrel i j l
            surj := hsurj }, fun i => rfl, hrel⟩
