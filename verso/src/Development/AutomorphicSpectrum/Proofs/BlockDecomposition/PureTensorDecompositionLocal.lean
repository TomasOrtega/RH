import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.PureTensor

def LCC {X : Type*} [TopologicalSpace X] (f : X → ℂ) : Prop := IsLocallyConstant f ∧ HasCompactSupport f

def pureSpan (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] : Submodule ℂ (X × Y → ℂ) :=
  Submodule.span ℂ {h | ∃ (f : X → ℂ) (g : Y → ℂ), LCC f ∧ LCC g ∧ h = fun p => f p.1 * g p.2}

/- English proof (translation)
Assemble the required witnesses or components as `⟨hf.1.mul hg.1, hf.2.mul_right⟩`.
-/
theorem LCC.mul {X : Type*} [TopologicalSpace X] {f g : X → ℂ} (hf : LCC f) (hg : LCC g) :
    LCC (fun x => f x * g x) :=
  ⟨hf.1.mul hg.1, hf.2.mul_right⟩

/- English proof (translation)
Use `⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_, HasCompactSupport.intro hU fun x hx => Set.indicator_of_notMem hx _⟩` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ U`. Use `filter_upwards [hO.mem_nhds hx] with y hy`. Simplify using `[hx, hy]`. Use `filter_upwards [hU.isClosed.isOpen_compl.mem_nhds hx] with y hy`.

Establish `hy' : y ∉ U` using `hy`. Simplify using `[hx, hy']`.
-/
theorem lcc_indicator {X : Type*} [TopologicalSpace X] [T2Space X] {U : Set X} (hU : IsCompact U)
    (hO : IsOpen U) : LCC (U.indicator (fun _ => (1 : ℂ))) := by
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_,
    HasCompactSupport.intro hU fun x hx => Set.indicator_of_notMem hx _⟩
  by_cases hx : x ∈ U
  · filter_upwards [hO.mem_nhds hx] with y hy
    simp [hx, hy]
  · filter_upwards [hU.isClosed.isOpen_compl.mem_nhds hx] with y hy
    have hy' : y ∉ U := hy
    simp [hx, hy']

/- English proof (translation)
Take `⟨K, hK, hKW, hKc⟩` from `local_compact_nhds hW`. Establish `hb` using `loc_compact_Haus_tot_disc_of_zero_dim (H := X)`. Take `⟨V, hV, hxV, hVK⟩` from `hb.mem_nhds_iff.1 hK`. Conclude with `⟨V, hKc.of_isClosed_subset hV.1 hVK, hV.2, hxV, hVK.trans hKW⟩`.
-/
theorem exists_compact_open {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [TotallyDisconnectedSpace X] {x : X} {W : Set X} (hW : W ∈ nhds x) :
    ∃ U, IsCompact U ∧ IsOpen U ∧ x ∈ U ∧ U ⊆ W := by
  obtain ⟨K, hK, hKW, hKc⟩ := local_compact_nhds hW
  have hb := loc_compact_Haus_tot_disc_of_zero_dim (H := X)
  obtain ⟨V, hV, hxV, hVK⟩ := hb.mem_nhds_iff.1 hK
  exact ⟨V, hKc.of_isClosed_subset hV.1 hVK, hV.2, hxV, hVK.trans hKW⟩

/- English proof (translation)
Proceed by induction on `hh using Submodule.span_induction with`. Consider the case `mem h hh`. Take `⟨f, g, hf, hg, rfl⟩` from `hh`. Use `Submodule.subset_span ⟨_, _, hf.mul ha, hg.mul hb, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `zero`. Use `(pureSpan X Y).zero_mem using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`. Simplify using the standard rewrite rules.

Consider the case `add u v _ _ hu hv`. Use `(pureSpan X Y).add_mem hu hv using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`. Simplify using `[add_mul]`. Consider the case `smul c u _ hu`.

Use `(pureSpan X Y).smul_mem c hu using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`. Simplify using `[mul_assoc]`.
-/
theorem mul_mem_pureSpan {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {a : X → ℂ}
    {b : Y → ℂ} (ha : LCC a) (hb : LCC b) {h : X × Y → ℂ} (hh : h ∈ pureSpan X Y) :
    (fun p => h p * (a p.1 * b p.2)) ∈ pureSpan X Y := by
  induction hh using Submodule.span_induction with
  | mem h hh =>
    obtain ⟨f, g, hf, hg, rfl⟩ := hh
    refine Submodule.subset_span ⟨_, _, hf.mul ha, hg.mul hb, ?_⟩
    funext p
    ring
  | zero =>
    convert (pureSpan X Y).zero_mem using 1
    funext p
    simp
  | add u v _ _ hu hv =>
    convert (pureSpan X Y).add_mem hu hv using 1
    funext p
    simp [add_mul]
  | smul c u _ hu =>
    convert (pureSpan X Y).smul_mem c hu using 1
    funext p
    simp [mul_assoc]

/- English proof (translation)
Establish `hbox : ∀ p : X × Y, ∃ U V, IsCompact U ∧ IsOpen U ∧ IsCompact V ∧ IsOpen V ∧ p.1 ∈ U ∧ p.2 ∈ V ∧ ∀ q ∈ U ×ˢ V, Φ q = Φ p`. Introduce `p`. Establish `hp` using `(IsLocallyConstant.iff_eventually_eq Φ).1 h p`. Establish `hp' : {q | Φ q = Φ p} ∈ nhds ((p.1, p.2) : X × Y)` using `hp`. Take `⟨u, hu, v, hv, huv⟩` from `mem_nhds_prod_iff.1 hp'`.

Take `⟨U, hUc, hUo, hxU, hUu⟩` from `exists_compact_open hu`. Take `⟨V, hVc, hVo, hyV, hVv⟩` from `exists_compact_open hv`. Conclude with `⟨U, V, hUc, hUo, hVc, hVo, hxU, hyV, fun q hq => huv ⟨hUu hq.1, hVv hq.2⟩⟩`. Use `choose U V hUc hUo hVc hVo hxU hyV hconst using hbox`. Take `⟨t, -, ht⟩` from `IsCompact.elim_nhds_subcover hc (fun p => U p ×ˢ V p) fun p _ => ((hUo p).prod (hVo p)).mem_nhds ⟨hxU p, hyV p⟩`.

Establish `key : ∀ t : Finset (X × Y), (⋃ q ∈ t, U q ×ˢ V q).indicator Φ ∈ pureSpan X Y` using `by classical`. Introduce `t`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty`. Use `(pureSpan X Y).zero_mem using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `p`. Simplify using the standard rewrite rules. Consider the case `insert q t _ ih`. Establish `ha` using `lcc_indicator (hUc q) (hUo q)`. Establish `hb` using `lcc_indicator (hVc q) (hVo q)`.

Establish `hbox : (fun p : X × Y => (U q).indicator (fun _ => (1 : ℂ)) p.1 * (V q).indicator (fun _ => (1 : ℂ)) p.2) ∈ pureSpan X Y` using `Submodule.subset_span ⟨_, _, ha, hb, rfl⟩`. Establish `hm` using `mul_mem_pureSpan ha hb ih`. Use `(pureSpan X Y).sub_mem ((pureSpan X Y).add_mem ((pureSpan X Y).smul_mem (Φ q) hbox) ih) hm using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`. Distinguish the cases in `h1 : p ∈ U q ×ˢ V q`.

Establish `h1a : p.1 ∈ U q` using `h1.1`. Establish `h1b : p.2 ∈ V q` using `h1.2`. Establish `hmem : p ∈ ⋃ r ∈ insert q t, U r ×ˢ V r`. Simplify using `only [Set.mem_iUnion]`. Conclude with `⟨q, Finset.mem_insert_self _ _, h1⟩`.

Simplify using `[Set.indicator_of_mem hmem, h1a, h1b, hconst q p h1]`. Establish `h0 : (U q).indicator (fun _ => (1 : ℂ)) p.1 * (V q).indicator (fun _ => (1 : ℂ)) p.2 = 0`. Distinguish the cases in `h1a : p.1 ∈ U q`. Establish `h1b : p.2 ∉ V q` using `fun hb' => h1 ⟨h1a, hb'⟩`. Simplify using `[h1b]`.

Simplify using `[h1a]`. Establish `hiff : p ∈ ⋃ r ∈ insert q t, U r ×ˢ V r ↔ p ∈ ⋃ r ∈ t, U r ×ˢ V r`. Simplify using `only [Set.mem_iUnion, Finset.mem_insert, exists_prop]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, rfl | hr, hp⟩`.

Conclude with `absurd hp h1`. Conclude with `⟨r, hr, hp⟩`. Introduce and unpack `⟨r, hr, hp⟩`. Conclude with `⟨r, Or.inr hr, hp⟩`. Distinguish the cases in `h2 : p ∈ ⋃ r ∈ t, U r ×ˢ V r`.

Simplify using `only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[Set.indicator_of_mem (hiff.2 h2), Set.indicator_of_mem h2, h0]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[Set.indicator_of_notMem (fun hh => h2 (hiff.1 hh)), Set.indicator_of_notMem h2, h0]`.

Expand and normalize the polynomial expressions, which then agree. Use `key t using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`. Distinguish the cases in `hp : p ∈ ⋃ q ∈ t, U q ×ˢ V q`. Rewrite using `[Set.indicator_of_mem hp]`.

Rewrite using `[Set.indicator_of_notMem hp]`. Assume the negation of the conclusion as `hne`. Conclude with `hp (ht (subset_tsupport _ hne))`.
-/
theorem mem_pureSpan {X Y : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [TotallyDisconnectedSpace X] [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    [TotallyDisconnectedSpace Y] {Φ : X × Y → ℂ} (h : IsLocallyConstant Φ)
    (hc : HasCompactSupport Φ) : Φ ∈ pureSpan X Y := by
  have hbox : ∀ p : X × Y, ∃ U V, IsCompact U ∧ IsOpen U ∧ IsCompact V ∧ IsOpen V ∧ p.1 ∈ U ∧
      p.2 ∈ V ∧ ∀ q ∈ U ×ˢ V, Φ q = Φ p := by
    intro p
    have hp := (IsLocallyConstant.iff_eventually_eq Φ).1 h p
    have hp' : {q | Φ q = Φ p} ∈ nhds ((p.1, p.2) : X × Y) := hp
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 hp'
    obtain ⟨U, hUc, hUo, hxU, hUu⟩ := exists_compact_open hu
    obtain ⟨V, hVc, hVo, hyV, hVv⟩ := exists_compact_open hv
    exact ⟨U, V, hUc, hUo, hVc, hVo, hxU, hyV, fun q hq => huv ⟨hUu hq.1, hVv hq.2⟩⟩
  choose U V hUc hUo hVc hVo hxU hyV hconst using hbox
  obtain ⟨t, -, ht⟩ := IsCompact.elim_nhds_subcover hc (fun p => U p ×ˢ V p)
    fun p _ => ((hUo p).prod (hVo p)).mem_nhds ⟨hxU p, hyV p⟩
  have key : ∀ t : Finset (X × Y), (⋃ q ∈ t, U q ×ˢ V q).indicator Φ ∈ pureSpan X Y := by
    classical
    intro t
    induction t using Finset.induction_on with
    | empty =>
      convert (pureSpan X Y).zero_mem using 1
      funext p
      simp
    | insert q t _ ih =>
      have ha := lcc_indicator (hUc q) (hUo q)
      have hb := lcc_indicator (hVc q) (hVo q)
      have hbox : (fun p : X × Y => (U q).indicator (fun _ => (1 : ℂ)) p.1 *
          (V q).indicator (fun _ => (1 : ℂ)) p.2) ∈ pureSpan X Y :=
        Submodule.subset_span ⟨_, _, ha, hb, rfl⟩
      have hm := mul_mem_pureSpan ha hb ih
      convert (pureSpan X Y).sub_mem ((pureSpan X Y).add_mem ((pureSpan X Y).smul_mem (Φ q) hbox) ih) hm
        using 1
      funext p
      by_cases h1 : p ∈ U q ×ˢ V q
      · have h1a : p.1 ∈ U q := h1.1
        have h1b : p.2 ∈ V q := h1.2
        have hmem : p ∈ ⋃ r ∈ insert q t, U r ×ˢ V r := by
          simp only [Set.mem_iUnion]
          exact ⟨q, Finset.mem_insert_self _ _, h1⟩
        simp [Set.indicator_of_mem hmem, h1a, h1b, hconst q p h1]
      · have h0 : (U q).indicator (fun _ => (1 : ℂ)) p.1 * (V q).indicator (fun _ => (1 : ℂ)) p.2 = 0 := by
          by_cases h1a : p.1 ∈ U q
          · have h1b : p.2 ∉ V q := fun hb' => h1 ⟨h1a, hb'⟩
            simp [h1b]
          · simp [h1a]
        have hiff : p ∈ ⋃ r ∈ insert q t, U r ×ˢ V r ↔ p ∈ ⋃ r ∈ t, U r ×ˢ V r := by
          simp only [Set.mem_iUnion, Finset.mem_insert, exists_prop]
          constructor
          · rintro ⟨r, rfl | hr, hp⟩
            · exact absurd hp h1
            · exact ⟨r, hr, hp⟩
          · rintro ⟨r, hr, hp⟩
            exact ⟨r, Or.inr hr, hp⟩
        by_cases h2 : p ∈ ⋃ r ∈ t, U r ×ˢ V r
        · simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          rw [Set.indicator_of_mem (hiff.2 h2), Set.indicator_of_mem h2, h0]
          ring
        · simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          rw [Set.indicator_of_notMem (fun hh => h2 (hiff.1 hh)), Set.indicator_of_notMem h2, h0]
          ring
  convert key t using 1
  funext p
  by_cases hp : p ∈ ⋃ q ∈ t, U q ×ˢ V q
  · rw [Set.indicator_of_mem hp]
  · rw [Set.indicator_of_notMem hp]
    by_contra hne
    exact hp (ht (subset_tsupport _ hne))

/- English proof (translation)
Take `⟨n, c, e, he⟩` from `Submodule.mem_span_set'.1 (mem_pureSpan h hc)`. Use `choose f g hf hg hfg using fun i => (e i).2`. Establish `hcf : ∀ i, LCC (fun x => c i * f i x)` using `fun i => ⟨(IsLocallyConstant.const (c i)).mul (hf i).1, (hf i).2.mul_left⟩`. Use `⟨n, fun i x => c i * f i x, g, hcf, hg, fun x y => ?_⟩` and prove the remaining obligations. Rewrite using `[← he]`.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hfg i]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_pure_sum {X Y : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [TotallyDisconnectedSpace X] [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    [TotallyDisconnectedSpace Y] {Φ : X × Y → ℂ} (h : IsLocallyConstant Φ)
    (hc : HasCompactSupport Φ) :
    ∃ (n : ℕ) (f : Fin n → X → ℂ) (g : Fin n → Y → ℂ), (∀ i, LCC (f i)) ∧ (∀ i, LCC (g i)) ∧
      ∀ x y, Φ (x, y) = ∑ i, f i x * g i y := by
  obtain ⟨n, c, e, he⟩ := Submodule.mem_span_set'.1 (mem_pureSpan h hc)
  choose f g hf hg hfg using fun i => (e i).2
  have hcf : ∀ i, LCC (fun x => c i * f i x) := fun i =>
    ⟨(IsLocallyConstant.const (c i)).mul (hf i).1, (hf i).2.mul_left⟩
  refine ⟨n, fun i x => c i * f i x, g, hcf, hg, fun x y => ?_⟩
  rw [← he]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hfg i]
  ring

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def cat3Homeo : (Matrix (Fin 2) (Fin 2) F × (Fin 2 → F)) ≃ₜ Matrix (Fin 2) (Fin 3) F where
  toFun p := cat3 p.1 p.2
  invFun M := (!![M 0 0, M 0 1; M 1 0, M 1 1], ![M 0 2, M 1 2])
  left_inv := by
    rintro ⟨A, y⟩
    refine Prod.ext ?_ ?_
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [cat3]
    · ext i
      fin_cases i <;> simp [cat3]
  right_inv := by
    intro M
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cat3]
  continuous_toFun := by
    refine continuous_matrix fun i j => ?_
    have h1 : ∀ a b, Continuous fun p : Matrix (Fin 2) (Fin 2) F × (Fin 2 → F) => p.1 a b :=
      fun a b => continuous_fst.matrix_elem a b
    have h2 : ∀ a, Continuous fun p : Matrix (Fin 2) (Fin 2) F × (Fin 2 → F) => p.2 a :=
      fun a => (continuous_apply a).comp continuous_snd
    fin_cases i <;> fin_cases j <;> simp [cat3, h1, h2]
  continuous_invFun := by
    have h1 : ∀ a b, Continuous fun M : Matrix (Fin 2) (Fin 3) F => M a b :=
      fun a b => continuous_id.matrix_elem a b
    refine Continuous.prodMk (continuous_matrix fun i j => ?_) (continuous_pi fun i => ?_)
    · fin_cases i <;> fin_cases j <;> simp [h1]
    · fin_cases i <;> simp [h1]

instance : TotallyDisconnectedSpace (Matrix (Fin 2) (Fin 2) F) :=
  inferInstanceAs (TotallyDisconnectedSpace (Fin 2 → Fin 2 → F))

/- English proof (translation)
Take `⟨n, f, g, hf, hg, hfg⟩` from `exists_pure_sum (Φ := Φ ∘ cat3Homeo) (h.comp_continuous cat3Homeo.continuous) (hc.comp_homeomorph cat3Homeo)`. Conclude with `⟨n, f, g, hf, hg, fun A y => hfg A y⟩`.
-/
theorem schwartzBruhat_pure_tensor_sum (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (h : IsLocallyConstant Φ)
    (hc : HasCompactSupport Φ) :
    ∃ (n : ℕ) (f : Fin n → Matrix (Fin 2) (Fin 2) F → ℂ) (g : Fin n → (Fin 2 → F) → ℂ),
      (∀ i, SB2 (f i)) ∧ (∀ i, IsLocallyConstant (g i) ∧ HasCompactSupport (g i)) ∧
      ∀ A y, Φ (cat3 A y) = ∑ i, f i A * g i y := by
  obtain ⟨n, f, g, hf, hg, hfg⟩ := exists_pure_sum (Φ := Φ ∘ cat3Homeo)
    (h.comp_continuous cat3Homeo.continuous) (hc.comp_homeomorph cat3Homeo)
  exact ⟨n, f, g, hf, hg, fun A y => hfg A y⟩

/- English proof (translation)
Introduce `F _ _ _ _ _ _ ψ _ Φ hΦ`. Take `⟨n, f, g, hf, hg, hfg⟩` from `schwartzBruhat_pure_tensor_sum Φ hΦ.1 hΦ.2`. Conclude with `⟨n, f, g, hf, fun i => GodementSectionLocal.mem_schwartzBruhat2.2 (hg i), hfg⟩`.
-/
theorem k2pt : Ad3.K.GL2LocalData.SchwartzBruhatProductDecomposition := by
  intro F _ _ _ _ _ _ ψ _ Φ hΦ
  obtain ⟨n, f, g, hf, hg, hfg⟩ := schwartzBruhat_pure_tensor_sum Φ hΦ.1 hΦ.2
  exact ⟨n, f, g, hf, fun i => GodementSectionLocal.mem_schwartzBruhat2.2 (hg i), hfg⟩

end GlobalTheory.CompanionTheory.PureTensor
