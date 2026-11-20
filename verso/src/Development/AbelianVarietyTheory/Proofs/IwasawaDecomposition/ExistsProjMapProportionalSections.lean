import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratesAlong
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ProjSpace GlobalTheory.Cartier

namespace GlobalTheory.ProjBlowup

variable {X W : Scheme.{0}} {L : LB X} {m : ℕ}

/- English proof (translation)
Establish `hT : T ≤ g ⁻¹ᵁ (L.U k ⊓ L.U l)` using `le_inf hk hl`. Use `⟨Units.map (g.appLE (L.U k ⊓ L.U l) T hT).hom.toMonoidHom (L.g k l), fun j => ?_⟩` and prove the remaining obligations. Use `congrArg (g.appLE (L.U k ⊓ L.U l) T hT).hom (sec_compat (σ j) k l (inf_le_left : L.U k ⊓ L.U l ≤ _) inf_le_right)` as an intermediate fact. Rewrite `this` using `[map_mul, appLE_resG, appLE_resG, appLE_resG]`. Conclude with `this`.
-/
theorem exists_unit_appLE_sec (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (k l : L.ι) {T : W.Opens}
    (hk : T ≤ g ⁻¹ᵁ L.U k) (hl : T ≤ g ⁻¹ᵁ L.U l) : ∃ u : Γ(W, T)ˣ, ∀ j,
      (g.appLE (L.U k) T hk).hom ((σ j).f k) = u * (g.appLE (L.U l) T hl).hom ((σ j).f l) := by
  have hT : T ≤ g ⁻¹ᵁ (L.U k ⊓ L.U l) := le_inf hk hl
  refine ⟨Units.map (g.appLE (L.U k ⊓ L.U l) T hT).hom.toMonoidHom (L.g k l), fun j => ?_⟩
  have := congrArg (g.appLE (L.U k ⊓ L.U l) T hT).hom
    (sec_compat (σ j) k l (inf_le_left : L.U k ⊓ L.U l ≤ _) inf_le_right)
  rw [map_mul, appLE_resG, appLE_resG, appLE_resG] at this
  exact this

/- English proof (translation)
Establish `h1 : ∀ j, ∃ a, a * f = s j` using `fun j => Ideal.mem_span_singleton'.1 (h ▸ Ideal.subset_span ⟨j, rfl⟩)`. Use `choose a ha using h1`. Take `⟨c, hc⟩` from `Ideal.mem_span_range_iff_exists_fun.1 (h ▸ Ideal.mem_span_singleton_self f)`. Use `⟨a, c, fun j => (ha j).symm, (mul_cancel_right_mem_nonZeroDivisors hf).1 ?_⟩` and prove the remaining obligations. Rewrite using `[one_mul, Finset.sum_mul]`.

Use `Eq.trans (Finset.sum_congr rfl fun j _ => ?_) hc` and prove the remaining obligations. Rewrite using `[mul_assoc, ha]`.
-/
theorem exists_quot_of_span_eq {B : Type} [CommRing B] {ι : Type} [Fintype ι] {f : B} (hf : f ∈ nonZeroDivisors B)
    {s : ι → B} (h : Ideal.span {f} = Ideal.span (Set.range s)) :
    ∃ a c : ι → B, (∀ j, s j = a j * f) ∧ ∑ j, c j * a j = 1 := by
  have h1 : ∀ j, ∃ a, a * f = s j := fun j =>
    Ideal.mem_span_singleton'.1 (h ▸ Ideal.subset_span ⟨j, rfl⟩)
  choose a ha using h1
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 (h ▸ Ideal.mem_span_singleton_self f)
  refine ⟨a, c, fun j => (ha j).symm, (mul_cancel_right_mem_nonZeroDivisors hf).1 ?_⟩
  rw [one_mul, Finset.sum_mul]
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) hc
  rw [mul_assoc, ha]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `h1 : (W.presheaf.germ A y hy).hom (∑ j, c j * a j) ∈ IsLocalRing.maximalIdeal (W.presheaf.stalk y)`. Rewrite using `[map_sum]`. Use `Ideal.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`.

Conclude with `Ideal.mul_mem_left _ _ fun hu => hne ⟨j, (W.mem_basicOpen _ y hy).2 hu⟩`. Rewrite `h1` using `[h, map_one]`. Conclude with `h1 isUnit_one`.
-/
theorem exists_mem_basicOpen_of_sum {A : W.Opens} {a c : Fin (m + 1) → Γ(W, A)} (h : ∑ j, c j * a j = 1)
    {y : W} (hy : y ∈ A) : ∃ j, y ∈ W.basicOpen (a j) := by
  by_contra hne
  have h1 : (W.presheaf.germ A y hy).hom (∑ j, c j * a j) ∈ IsLocalRing.maximalIdeal (W.presheaf.stalk y) := by
    rw [map_sum]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ fun hu => hne ⟨j, (W.mem_basicOpen _ y hy).2 hu⟩
  rw [h, map_one] at h1
  exact h1 isUnit_one

/- English proof (translation)
Take `⟨D, rfl⟩` from `EffCartierData.exists_idealSheaf_eq hI`. Establish `loc : ∀ y : W, ∃ (A : W.Opens) (k : L.ι) (hk : A ≤ g ⁻¹ᵁ L.U k) (i : D.ι) (hi : A ≤ D.U i) (a c : Fin (m + 1) → Γ(W, A)), y ∈ A ∧ (∀ j, (g.appLE (L.U k) A hk).hom ((σ j).f k) = a j * resG W hi (D.f i)) ∧ ∑ j, c j * a j = 1`. Introduce `y`. Take `⟨k, hk⟩` from `Opens.mem_iSup.1 (hσ.1.ge (Set.mem_univ y))`. Take `⟨i, hi⟩` from `D.exists_mem y`.

Take `⟨A, hy, hA⟩` from `EffCartierData.exists_affine_le (V := g ⁻¹ᵁ L.U k ⊓ D.U i) (x := y) ⟨hk, hi⟩`. Take `⟨a, c, h⟩` from `exists_quot_of_span_eq (D.regular i _ (hA.trans inf_le_right)) ((D.ideal_idealSheaf A i (hA.trans inf_le_right)).symm.trans (hσ.2 k A (hA.trans inf_le_left)))`. Conclude with `⟨A.1, k, _, i, _, a, c, hy, h⟩`. Use `choose A k hk i hi a c hy ha hc using loc`. Establish `ha' : ∀ y {T : W.Opens} (hT : T ≤ A y) j, (g.appLE (L.U (k y)) T (hT.trans (hk y))).hom ((σ j).f (k y)) = resG W hT (a y j) * resG W (hT.trans (hi y)) (D.f (i y))` using `fun y T hT j => by`.

Use `congrArg (resG W hT) (ha y j)` as an intermediate fact. Rewrite `this` using `[map_mul, resG_appLE, resG_resG]`. Then use the resulting hypothesis. Establish `tr : ∀ y z, ∃ u : Γ(W, A y ⊓ A z)ˣ, ∀ j, resG W (inf_le_left : A y ⊓ A z ≤ A y) (a y j) = (u : Γ(W, A y ⊓ A z)) * resG W (inf_le_right : A y ⊓ A z ≤ A z) (a z j)` using `fun y z => by`. Take `⟨u, hu⟩` from `exists_unit_appLE_sec σ g (k y) (k z) (T := A y ⊓ A z) (inf_le_left.trans (hk y)) (inf_le_right.trans (hk z))`. Establish `hy' : A y ⊓ A z ≤ D.U (i y)` using `inf_le_left.trans (hi y)`.

Establish `hz' : A y ⊓ A z ≤ D.U (i z)` using `inf_le_right.trans (hi z)`. Use `⟨u * Units.map (resG W (le_inf hz' hy')).toMonoidHom (D.trans (i z) (i y)), fun j => ?_⟩` and prove the remaining obligations. Use `((D.regular (i y)).resG hy').mul_right_cancel ?_` and prove the remaining obligations. Establish `e` using `hu j`. Rewrite `e` using `[ha' y inf_le_left, ha' z inf_le_right, D.trans_spec_on (i z) (i y) hz' hy']`.

Rewrite using `[e]`. Express the relevant statement in the definitionally equal form `_ = (u : Γ(W, A y ⊓ A z)) * resG W (le_inf hz' hy') (D.trans (i z) (i y)) * _ * _`. Expand and normalize the polynomial expressions, which then agree. Use `choose u hu using tr`. Set `B : LB W` to `{ ι := W, U := A, g := u }`.

Set `t : Fin (m + 1) → B.Sec` to `fun j => { f := fun y => a y j, compat := fun y z => hu y z j }`. Establish `ht : ⨆ j, Out.nonzeroLocus (t j) = ⊤`. Use `eq_top_iff.2 fun y _ => ?_` and prove the remaining obligations. Take `⟨j, hj⟩` from `exists_mem_basicOpen_of_sum (hc y) (hy y)`. Conclude with `Opens.mem_iSup.2 ⟨j, (mem_nonzeroLocus_iff (t j) y (hy y)).2 hj⟩`.

Use `⟨toProj q t ht, toProj_str q t ht, fun V l hl p hp j => ext_germ fun y hyV => ?_⟩` and prove the remaining obligations. Establish `hm : y ∈ V ⊓ A y` using `⟨hyV, hy y⟩`. Establish `key : resG W (inf_le_left : V ⊓ A y ≤ V) ((g.appLE (L.U l) V hl).hom ((σ j).f l)) = resG W inf_le_left (pullRatio (toProj q t ht) V p hp j * (g.appLE (L.U l) V hl).hom ((σ p).f l))`. Take `⟨v, hv⟩` from `exists_unit_appLE_sec σ g l (k y) (T := V ⊓ A y) (inf_le_left.trans hl) (inf_le_right.trans (hk y))`. Establish `e : resG W inf_le_right (a y j) = _ * resG W inf_le_right (a y p)` using `sec_eq_pullRatio_toProj_mul q t ht p j y (W := V ⊓ A y) (inf_le_left.trans hp) inf_le_right`.

Rewrite using `[map_mul, resG_appLE, resG_appLE, resG_pullRatio, hv, hv, ha' y inf_le_right, ha' y inf_le_right, e]`. Expand and normalize the polynomial expressions, which then agree. Use `congrArg (W.presheaf.germ _ y hm).hom key` as an intermediate fact. Rewrite `this` using `[germ_resG, germ_resG]`. Then use the resulting hypothesis.
-/
theorem exists_proportional (R : Type) [CommRing R] (X W : Scheme.{0}) (I : W.IdealSheafData) (L : LB X) (m : ℕ)
    (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (q : W ⟶ Sp R) (hσ : GeneratesAlong I σ g) (hI : FinalTheorems.EffCartier I) :
    ∃ ψ : W ⟶ PSpace R m, ψ ≫ PSpace.str R m = q ∧ Proportional σ g ψ := by
  obtain ⟨D, rfl⟩ := EffCartierData.exists_idealSheaf_eq hI
  have loc : ∀ y : W, ∃ (A : W.Opens) (k : L.ι) (hk : A ≤ g ⁻¹ᵁ L.U k) (i : D.ι) (hi : A ≤ D.U i)
      (a c : Fin (m + 1) → Γ(W, A)), y ∈ A ∧
      (∀ j, (g.appLE (L.U k) A hk).hom ((σ j).f k) = a j * resG W hi (D.f i)) ∧ ∑ j, c j * a j = 1 := by
    intro y
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hσ.1.ge (Set.mem_univ y))
    obtain ⟨i, hi⟩ := D.exists_mem y
    obtain ⟨A, hy, hA⟩ := EffCartierData.exists_affine_le (V := g ⁻¹ᵁ L.U k ⊓ D.U i) (x := y) ⟨hk, hi⟩
    obtain ⟨a, c, h⟩ := exists_quot_of_span_eq (D.regular i _ (hA.trans inf_le_right))
      ((D.ideal_idealSheaf A i (hA.trans inf_le_right)).symm.trans (hσ.2 k A (hA.trans inf_le_left)))
    exact ⟨A.1, k, _, i, _, a, c, hy, h⟩
  choose A k hk i hi a c hy ha hc using loc
  have ha' : ∀ y {T : W.Opens} (hT : T ≤ A y) j, (g.appLE (L.U (k y)) T (hT.trans (hk y))).hom ((σ j).f (k y)) =
      resG W hT (a y j) * resG W (hT.trans (hi y)) (D.f (i y)) := fun y T hT j => by
    have := congrArg (resG W hT) (ha y j)
    rwa [map_mul, resG_appLE, resG_resG] at this
  have tr : ∀ y z, ∃ u : Γ(W, A y ⊓ A z)ˣ, ∀ j,
      resG W (inf_le_left : A y ⊓ A z ≤ A y) (a y j) =
        (u : Γ(W, A y ⊓ A z)) * resG W (inf_le_right : A y ⊓ A z ≤ A z) (a z j) := fun y z => by
    obtain ⟨u, hu⟩ := exists_unit_appLE_sec σ g (k y) (k z) (T := A y ⊓ A z)
      (inf_le_left.trans (hk y)) (inf_le_right.trans (hk z))
    have hy' : A y ⊓ A z ≤ D.U (i y) := inf_le_left.trans (hi y)
    have hz' : A y ⊓ A z ≤ D.U (i z) := inf_le_right.trans (hi z)
    refine ⟨u * Units.map (resG W (le_inf hz' hy')).toMonoidHom (D.trans (i z) (i y)), fun j => ?_⟩
    refine ((D.regular (i y)).resG hy').mul_right_cancel ?_
    have e := hu j
    rw [ha' y inf_le_left, ha' z inf_le_right, D.trans_spec_on (i z) (i y) hz' hy'] at e
    rw [e]
    change _ = (u : Γ(W, A y ⊓ A z)) * resG W (le_inf hz' hy') (D.trans (i z) (i y)) * _ * _
    ring
  choose u hu using tr
  let B : LB W := { ι := W, U := A, g := u }
  let t : Fin (m + 1) → B.Sec := fun j => { f := fun y => a y j, compat := fun y z => hu y z j }
  have ht : ⨆ j, Out.nonzeroLocus (t j) = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨j, hj⟩ := exists_mem_basicOpen_of_sum (hc y) (hy y)
    exact Opens.mem_iSup.2 ⟨j, (mem_nonzeroLocus_iff (t j) y (hy y)).2 hj⟩
  refine ⟨toProj q t ht, toProj_str q t ht, fun V l hl p hp j => ext_germ fun y hyV => ?_⟩
  have hm : y ∈ V ⊓ A y := ⟨hyV, hy y⟩
  have key : resG W (inf_le_left : V ⊓ A y ≤ V) ((g.appLE (L.U l) V hl).hom ((σ j).f l)) =
      resG W inf_le_left (pullRatio (toProj q t ht) V p hp j * (g.appLE (L.U l) V hl).hom ((σ p).f l)) := by
    obtain ⟨v, hv⟩ := exists_unit_appLE_sec σ g l (k y) (T := V ⊓ A y)
      (inf_le_left.trans hl) (inf_le_right.trans (hk y))
    have e : resG W inf_le_right (a y j) = _ * resG W inf_le_right (a y p) :=
      sec_eq_pullRatio_toProj_mul q t ht p j y (W := V ⊓ A y) (inf_le_left.trans hp) inf_le_right
    rw [map_mul, resG_appLE, resG_appLE, resG_pullRatio, hv, hv, ha' y inf_le_right, ha' y inf_le_right, e]
    ring
  have := congrArg (W.presheaf.germ _ y hm).hom key
  rwa [germ_resG, germ_resG] at this

end GlobalTheory.ProjBlowup
