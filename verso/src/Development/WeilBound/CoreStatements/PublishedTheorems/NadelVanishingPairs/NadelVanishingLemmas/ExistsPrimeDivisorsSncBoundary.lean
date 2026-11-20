import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RegularSequenceStalkSncStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierDivisorMultCharacterize
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FiniteCodimOnePointsClosed
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RegularSequencePrimeDivisors
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsPrimeCartierDivisorStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.SncComp

variable {Y : Scheme.{0}}

/- English proof (translation)
Establish `h1` using `(Scheme.IdealSheafData.mem_support_iff_of_mem (I := Scheme.IdealSheafData.vanishingIdeal B) hyU).1 (by`. Rewrite using `[← SetLike.mem_coe]`. Simplify using `using hyB)`. Conclude with `(Scheme.mem_zeroLocus_iff _ _ _).1 h1 a ha`.
-/
theorem notMem_basicOpen_of_mem_vanishingIdeal (B : Closeds Y) (U : Y.affineOpens) {a : Γ(Y, U.1)}
    (ha : a ∈ (Scheme.IdealSheafData.vanishingIdeal B).ideal U) {y : Y} (hyU : y ∈ U.1)
    (hyB : y ∈ B) : y ∉ Y.basicOpen a := by
  have h1 := (Scheme.IdealSheafData.mem_support_iff_of_mem
    (I := Scheme.IdealSheafData.vanishingIdeal B) hyU).1 (by
      rw [← SetLike.mem_coe]; simpa using hyB)
  exact (Scheme.mem_zeroLocus_iff _ _ _).1 h1 a ha

/- English proof (translation)
Proceed by induction on `J using Finset.induction_on with`. Consider the case `empty`. Rewrite `h` using `[Finset.prod_empty, Scheme.basicOpen_of_isUnit _ isUnit_one]`. Conclude with `(h hy).elim`. Consider the case `insert a J ha ih`.

Rewrite `h` using `[Finset.prod_insert ha, Scheme.basicOpen_mul]`. Distinguish the cases in `h' : y ∈ Y.basicOpen (f a)`. Take `⟨i, hi, hi'⟩` from `ih fun h'' => h ⟨h', h''⟩`. Conclude with `⟨i, Finset.mem_insert_of_mem hi, hi'⟩`. Conclude with `⟨a, Finset.mem_insert_self a J, h'⟩`.
-/
theorem exists_notMem_basicOpen_of_prod {U : Y.Opens} {ι : Type} (J : Finset ι) (f : ι → Γ(Y, U))
    {y : Y} (hy : y ∈ U) (h : y ∉ Y.basicOpen (∏ i ∈ J, f i)) : ∃ i ∈ J, y ∉ Y.basicOpen (f i) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Scheme.basicOpen_of_isUnit _ isUnit_one] at h
    exact (h hy).elim
  | insert a J ha ih =>
    rw [Finset.prod_insert ha, Scheme.basicOpen_mul] at h
    by_cases h' : y ∈ Y.basicOpen (f a)
    · obtain ⟨i, hi, hi'⟩ := ih fun h'' => h ⟨h', h''⟩
      exact ⟨i, Finset.mem_insert_of_mem hi, hi'⟩
    · exact ⟨a, Finset.mem_insert_self a J, h'⟩

end GlobalTheory.SncComp

namespace GlobalTheory.SncComp

variable {Y : Scheme.{0}}

/- English proof (translation)
Introduce `hBt`. Take `⟨-, U, hU, m, f, J, hrsp, hid⟩` from `hB (genericPoint Y)`. Establish `hm : m = 0`. Establish `h` using `hrsp.2`. Establish `h0 : ringKrullDim Y.functionField = 0` using `ringKrullDim_eq_zero_of_field Y.functionField`.

Rewrite `h` using `[show ringKrullDim (Y.presheaf.stalk (genericPoint Y)) = ringKrullDim Y.functionField from rfl, h0]`. Conclude with `h` after adjusting the coercions. Substitute `hm` using the available equality. Establish `hJ : J = ∅` using `Finset.eq_empty_of_isEmpty J`. Substitute `hJ` using the available equality.

Rewrite `hid` using `[Finset.prod_empty]`. Establish `h1` using `notMem_basicOpen_of_mem_vanishingIdeal B U (a := 1) (hid ▸ Ideal.mem_span_singleton_self _) hU (by rw [hBt]; trivial)`. Conclude with `h1 (by rw [Scheme.basicOpen_of_isUnit _ isUnit_one]; exact hU)`.
-/
theorem ne_top_of_snc [IsIntegral Y] (B : Closeds Y)
    (hB : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B)) : B ≠ ⊤ := by
  intro hBt
  obtain ⟨-, U, hU, m, f, J, hrsp, hid⟩ := hB (genericPoint Y)
  have hm : m = 0 := by
    have h := hrsp.2
    have h0 : ringKrullDim Y.functionField = 0 := ringKrullDim_eq_zero_of_field Y.functionField
    rw [show ringKrullDim (Y.presheaf.stalk (genericPoint Y)) = ringKrullDim Y.functionField from rfl,
      h0] at h
    exact_mod_cast h
  subst hm
  have hJ : J = ∅ := Finset.eq_empty_of_isEmpty J
  subst hJ
  rw [Finset.prod_empty] at hid
  have h1 := notMem_basicOpen_of_mem_vanishingIdeal B U (a := 1)
    (hid ▸ Ideal.mem_span_singleton_self _) hU (by rw [hBt]; trivial)
  exact h1 (by rw [Scheme.basicOpen_of_isUnit _ isUnit_one]; exact hU)

variable [IsIntegral Y]

/- English proof (translation)
Take `⟨V, hxV, hV⟩` from `h.exists_nhds`. Set `c : (toLB D).ι` to `⟨(V, g), gen_mem hxV, hV⟩`. Use `⟨c, hxV, ?_⟩` and prove the remaining obligations. Establish `e` using `(presents_toLB D).rat_mul σ c (gen_mem hxV)`. Rewrite `e` using `[hσ, one_mul]`.

Conclude with `(algebraMap_germ (X := Y) (U := V) hxV (σ.f c)).trans e.symm`.
-/
theorem exists_chart_germ_eq {D : CartierDiv Y} {σ : (toLB D).Sec}
    (hσ : (presents_toLB D).rat σ = 1) {x : Y} {g : Y.functionFieldˣ} (h : D.IsEqn x g) :
    ∃ (c : (toLB D).ι) (hc : x ∈ (toLB D).U c), algebraMap (Y.presheaf.stalk x) Y.functionField
      ((Y.presheaf.germ _ x hc).hom (σ.f c)) = g := by
  obtain ⟨V, hxV, hV⟩ := h.exists_nhds
  let c : (toLB D).ι := ⟨(V, g), gen_mem hxV, hV⟩
  refine ⟨c, hxV, ?_⟩
  have e := (presents_toLB D).rat_mul σ c (gen_mem hxV)
  rw [hσ, one_mul] at e
  exact (algebraMap_germ (X := Y) (U := V) hxV (σ.f c)).trans e.symm

end GlobalTheory.SncComp

namespace GlobalTheory.SncComp

variable {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]

/- English proof (translation)
Take `⟨hreg, U, hxU, m, f, J, hrsp, hid⟩` from `hB x`. Take `⟨w₀, u, hw₀, hu⟩` from `GlobalTheory.T.regular_sequence_prime_divisors Y x U.1 hxU m f hreg hrsp`. Set `t : Fin m → Y.presheaf.stalk x` to `fun j => Y.presheaf.germ U.1 x hxU (f j)`. Set `e : Fin s → Option (Fin m)` to `fun i => if h : ∃ j, j ∈ J ∧ w i = w₀ j then some h.choose else none`. Establish `he : ∀ i a, e i = some a → w i = w₀ a`.

Introduce `i a h`. Simplify using `only [e] at h`. Use `split_ifs at h with h'`. Consider the cases of `h`. Conclude with `h'.choose_spec.2`.

Establish `key : ∀ i, ∃ g : Y.functionFieldˣ, (D i).IsEqn x g ∧ algebraMap (Y.presheaf.stalk x) Y.functionField ((e i).elim 1 t) = g`. Introduce `i`. Distinguish the cases in `h : ∃ j, j ∈ J ∧ w i = w₀ j`. Take `⟨j, hei, hwj⟩ : ∃ j, e i = some j ∧ w i = w₀ j` from `⟨h.choose, dif_pos h, h.choose_spec.2⟩`. Take `⟨hu1, -, -, -, hord, hoth⟩` from `hu j`.

Use `⟨u j, ?_, ?_⟩` and prove the remaining obligations. Use `(GlobalTheory.T.cartier_divisor_mult_characterize Y (D i)).2.2.2 x (u j) fun z hz => ?_` and prove the remaining obligations. Distinguish the cases in `hzw : z = w i`. Rewrite using `[hzw, (hmult i).1, hwj, hord]`. Rewrite using `[(hmult i).2 z hzw]`.

Distinguish the cases in `hz1 : Order.coheight z = 1`. Establish `hzb` using `hoth z hz hz1 (hwj ▸ hzw)`. Establish `hzU : z ∈ U.1` using `hz.mem_open U.1.isOpen hxU`. Rewrite using `[hu1]`. Conclude with `((unitAt_fnOf_iff hzU _ _).2 hzb).ord_eq_zero`.

Conclude with `Scheme.ord_eq_zero_of_coheight_neq_one hz1 _`. Rewrite using `[hei, hu1]`. Conclude with `algebraMap_germ hxU (f j)`. Establish `hei : e i = none` using `dif_neg h`. Use `⟨1, ?_, by rw [hei]; simp⟩` and prove the remaining obligations.

Use `(GlobalTheory.T.cartier_divisor_mult_characterize Y (D i)).2.2.2 x 1 fun z hz => ?_` and prove the remaining obligations. Rewrite using `[(hmult i).2 z ?_, Units.val_one, (unitAt_one z).ord_eq_zero]`. Introduce and unpack `rfl`. Establish `hzU : w i ∈ U.1` using `hz.mem_open U.1.isOpen hxU`. Establish `h0 : w i ∉ Y.basicOpen (∏ j ∈ J, f j)` using `notMem_basicOpen_of_mem_vanishingIdeal B U (hid ▸ Ideal.mem_span_singleton_self _) hzU (hwB i)`.

Take `⟨j, hj, hjb⟩` from `exists_notMem_basicOpen_of_prod J f hzU h0`. Use `h ⟨j, hj, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Conclude with `hjb ((hu j).2.2.2.2.2 (w i) hz (hw1 i) hne)`. Use `choose g hg hga using key`.

Use `choose c hc hcg using fun i => exists_chart_germ_eq (hσ i) (hg i)`. Use `⟨m, t, c, hc, e, hrsp, fun i i' a hi hi' => hw ((he i a hi).trans (he i' a hi').symm), fun i => ?_⟩` and prove the remaining obligations. Establish `: (Y.presheaf.germ _ x (hc i)).hom ((σ i).f (c i)) = (e i).elim 1 t` using `IsFractionRing.injective (Y.presheaf.stalk x) Y.functionField ((hcg i).trans (hga i).symm)`. Rewrite using `[this]`.
-/
theorem exists_local_data [GlobalTheory.IsNormalScheme Y] (B : Closeds Y)
    (hB : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B)) {s : ℕ} (w : Fin s → Y)
    (hw : Function.Injective w) (hw1 : ∀ i, Order.coheight (w i) = 1) (hwB : ∀ i, w i ∈ B)
    (D : Fin s → CartierDiv Y) (hmult : ∀ i, (D i).mult (w i) = 1 ∧ ∀ v, v ≠ w i → (D i).mult v = 0)
    (σ : ∀ i, (toLB (D i)).Sec) (hσ : ∀ i, (presents_toLB (D i)).rat (σ i) = 1) (x : Y) :
    ∃ (n : ℕ) (t : Fin n → Y.presheaf.stalk x) (c : ∀ i, (toLB (D i)).ι)
      (hc : ∀ i, x ∈ (toLB (D i)).U (c i)) (e : Fin s → Option (Fin n)),
      FinalTheorems.Rsp (Y.presheaf.stalk x) n t ∧ (∀ i j a, e i = some a → e j = some a → i = j) ∧
        ∀ i, Associated ((Y.presheaf.germ _ x (hc i)).hom ((σ i).f (c i))) ((e i).elim 1 t) := by
  classical
  obtain ⟨hreg, U, hxU, m, f, J, hrsp, hid⟩ := hB x
  obtain ⟨w₀, u, hw₀, hu⟩ := GlobalTheory.T.regular_sequence_prime_divisors Y x U.1 hxU m f hreg hrsp
  let t : Fin m → Y.presheaf.stalk x := fun j => Y.presheaf.germ U.1 x hxU (f j)
  let e : Fin s → Option (Fin m) := fun i =>
    if h : ∃ j, j ∈ J ∧ w i = w₀ j then some h.choose else none
  have he : ∀ i a, e i = some a → w i = w₀ a := by
    intro i a h
    simp only [e] at h
    split_ifs at h with h'
    cases h
    exact h'.choose_spec.2
  have key : ∀ i, ∃ g : Y.functionFieldˣ, (D i).IsEqn x g ∧
      algebraMap (Y.presheaf.stalk x) Y.functionField ((e i).elim 1 t) = g := by
    intro i
    by_cases h : ∃ j, j ∈ J ∧ w i = w₀ j
    · obtain ⟨j, hei, hwj⟩ : ∃ j, e i = some j ∧ w i = w₀ j := ⟨h.choose, dif_pos h, h.choose_spec.2⟩
      obtain ⟨hu1, -, -, -, hord, hoth⟩ := hu j
      refine ⟨u j, ?_, ?_⟩
      · refine (GlobalTheory.T.cartier_divisor_mult_characterize Y (D i)).2.2.2 x (u j) fun z hz => ?_
        by_cases hzw : z = w i
        · rw [hzw, (hmult i).1, hwj, hord]
        · rw [(hmult i).2 z hzw]
          by_cases hz1 : Order.coheight z = 1
          · have hzb := hoth z hz hz1 (hwj ▸ hzw)
            have hzU : z ∈ U.1 := hz.mem_open U.1.isOpen hxU
            rw [hu1]
            exact ((unitAt_fnOf_iff hzU _ _).2 hzb).ord_eq_zero
          · exact Scheme.ord_eq_zero_of_coheight_neq_one hz1 _
      · rw [hei, hu1]
        exact algebraMap_germ hxU (f j)
    · have hei : e i = none := dif_neg h
      refine ⟨1, ?_, by rw [hei]; simp⟩
      refine (GlobalTheory.T.cartier_divisor_mult_characterize Y (D i)).2.2.2 x 1 fun z hz => ?_
      rw [(hmult i).2 z ?_, Units.val_one, (unitAt_one z).ord_eq_zero]
      rintro rfl
      have hzU : w i ∈ U.1 := hz.mem_open U.1.isOpen hxU
      have h0 : w i ∉ Y.basicOpen (∏ j ∈ J, f j) := notMem_basicOpen_of_mem_vanishingIdeal B U
        (hid ▸ Ideal.mem_span_singleton_self _) hzU (hwB i)
      obtain ⟨j, hj, hjb⟩ := exists_notMem_basicOpen_of_prod J f hzU h0
      refine h ⟨j, hj, ?_⟩
      by_contra hne
      exact hjb ((hu j).2.2.2.2.2 (w i) hz (hw1 i) hne)
  choose g hg hga using key
  choose c hc hcg using fun i => exists_chart_germ_eq (hσ i) (hg i)
  refine ⟨m, t, c, hc, e, hrsp, fun i i' a hi hi' => hw ((he i a hi).trans (he i' a hi').symm),
    fun i => ?_⟩
  have : (Y.presheaf.germ _ x (hc i)).hom ((σ i).f (c i)) = (e i).elim 1 t :=
    IsFractionRing.injective (Y.presheaf.stalk x) Y.functionField ((hcg i).trans (hga i).symm)
  rw [this]

end GlobalTheory.SncComp

namespace GlobalTheory.SncComp

/- English proof (translation)
Introduce `k _ _ Y _ _ q n _ hP B hB`. Establish `: Smooth q` using `SmoothOfRelativeDimension.smooth n q`. Establish `: GlobalTheory.IsNormalScheme Y` using `isNormalScheme_of_smooth q`. Establish `: IsNoetherian Y`. Take `⟨N, i, hi, e⟩` from `hP`.

Use `isProper_str k N` as an intermediate fact. Establish `: QuasiCompact q` using `e ▸ inferInstance`. Use `QuasiCompact.compactSpace_of_compactSpace q` as an intermediate fact. Conclude with `{}`. Establish `hfin` using `GlobalTheory.T.finite_codim_one_points_closed Y B (ne_top_of_snc B hB)`.

Set `S` to `hfin.toFinset`. Set `w : Fin S.card → Y` to `fun i => (S.equivFin.symm i).1`. Establish `hw : Function.Injective w` using `fun i j h => S.equivFin.symm.injective (Subtype.ext h)`. Establish `hwS : ∀ i, Order.coheight (w i) = 1 ∧ w i ∈ B` using `fun i => hfin.mem_toFinset.1 (S.equivFin.symm i).2`. Establish `hSw : ∀ v, Order.coheight v = 1 → v ∈ B → ∃ i, v = w i` using `fun v h1 h2 => ⟨S.equivFin ⟨v, hfin.mem_toFinset.2 ⟨h1, h2⟩⟩, by simp [w]⟩`.

Establish `hufd : ∀ x : Y, UniqueFactorizationMonoid (Y.presheaf.stalk x)` using `AbelianProjective.ufd_stalk q`. Use `choose D hD using fun i => GlobalTheory.T.exists_prime_cartier_divisor Y hufd (w i) (hwS i).1`. Establish `heff : ∀ i, (D i).Eff` using `fun i => ((GlobalTheory.T.cartier_divisor_mult_characterize Y (D i)).1).2 fun z => by`. Distinguish the cases in `hz : z = w i`. Rewrite using `[hz, (hD i).1]`.

Evaluate the numerical expressions. Rewrite using `[(hD i).2 z hz]`. Use `choose σ hσ using fun i => (presents_toLB (D i)).exists_rat_eq (CartierDiv.mem_sections.2 (heff i))`. Use `⟨S.card, w, D, σ, hw, hD, hSw, ?_⟩` and prove the remaining obligations. Use `GlobalTheory.T.regular_sequence_stalk_snc k Y q n S.card (fun i => toLB (D i)) σ (fun i => isLB_toLB _) fun x _ => ?_` and prove the remaining obligations.

Conclude with `exists_local_data B hB w hw (fun i => (hwS i).1) (fun i => (hwS i).2) D hD σ hσ x`.
-/
theorem relSnc_components : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y]
    [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q], IsProjOver q →
    ∀ B : Closeds Y, FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) →
      ∃ (r : ℕ) (w : Fin r → Y) (D : Fin r → CartierDiv Y) (σ : ∀ i, (toLB (D i)).Sec),
        Function.Injective w ∧ (∀ i, (D i).mult (w i) = 1 ∧ ∀ v, v ≠ w i → (D i).mult v = 0) ∧
        (∀ v, Order.coheight v = 1 → v ∈ B → ∃ i, v = w i) ∧
        RelSnc q n (fun i => toLB (D i)) σ := by
  intro k _ _ Y _ _ q n _ hP B hB
  classical
  have : Smooth q := SmoothOfRelativeDimension.smooth n q
  have : GlobalTheory.IsNormalScheme Y := isNormalScheme_of_smooth q
  have : IsNoetherian Y := by
    obtain ⟨N, i, hi, e⟩ := hP
    have := isProper_str k N
    have : QuasiCompact q := e ▸ inferInstance
    have := QuasiCompact.compactSpace_of_compactSpace q
    exact {}
  have hfin := GlobalTheory.T.finite_codim_one_points_closed Y B (ne_top_of_snc B hB)
  let S := hfin.toFinset
  let w : Fin S.card → Y := fun i => (S.equivFin.symm i).1
  have hw : Function.Injective w := fun i j h => S.equivFin.symm.injective (Subtype.ext h)
  have hwS : ∀ i, Order.coheight (w i) = 1 ∧ w i ∈ B := fun i =>
    hfin.mem_toFinset.1 (S.equivFin.symm i).2
  have hSw : ∀ v, Order.coheight v = 1 → v ∈ B → ∃ i, v = w i := fun v h1 h2 =>
    ⟨S.equivFin ⟨v, hfin.mem_toFinset.2 ⟨h1, h2⟩⟩, by simp [w]⟩
  have hufd : ∀ x : Y, UniqueFactorizationMonoid (Y.presheaf.stalk x) :=
    AbelianProjective.ufd_stalk q
  choose D hD using fun i => GlobalTheory.T.exists_prime_cartier_divisor Y hufd (w i) (hwS i).1
  have heff : ∀ i, (D i).Eff := fun i => ((GlobalTheory.T.cartier_divisor_mult_characterize Y (D i)).1).2 fun z => by
    by_cases hz : z = w i
    · rw [hz, (hD i).1]; norm_num
    · rw [(hD i).2 z hz]
  choose σ hσ using fun i => (presents_toLB (D i)).exists_rat_eq (CartierDiv.mem_sections.2 (heff i))
  refine ⟨S.card, w, D, σ, hw, hD, hSw, ?_⟩
  refine GlobalTheory.T.regular_sequence_stalk_snc k Y q n S.card (fun i => toLB (D i)) σ (fun i => isLB_toLB _) fun x _ => ?_
  exact exists_local_data B hB w hw (fun i => (hwS i).1) (fun i => (hwS i).2) D hD σ hσ x

end GlobalTheory.SncComp
