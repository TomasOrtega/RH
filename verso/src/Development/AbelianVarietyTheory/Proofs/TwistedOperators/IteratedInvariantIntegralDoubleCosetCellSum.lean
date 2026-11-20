import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuotientIntegralFinitelyManyCellsWeightedSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVal

open GlobalTheory.CellInt

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr, a, ha, k, hk, rfl⟩`. Rewrite `ha` using `[Subgroup.mem_bot]`. Substitute `ha` using the available equality. Conclude with `⟨r, hr, k, hk, by simp⟩`.

Introduce and unpack `⟨r, hr, k, hk, rfl⟩`. Conclude with `⟨r, hr, 1, Subgroup.one_mem _, k, hk, by simp⟩`.
-/
theorem cellBot_iff {G : Type} [Group G] {R K : Subgroup G} {b x : G} :
    (∃ r ∈ R, ∃ a ∈ (⊥ : Subgroup G), ∃ k ∈ K, x = r * a * b * k) ↔ ∃ r ∈ R, ∃ k ∈ K, x = r * b * k := by
  constructor
  · rintro ⟨r, hr, a, ha, k, hk, rfl⟩
    rw [Subgroup.mem_bot] at ha
    subst ha
    exact ⟨r, hr, k, hk, by simp⟩
  · rintro ⟨r, hr, k, hk, rfl⟩
    exact ⟨r, hr, 1, Subgroup.one_mem _, k, hk, by simp⟩

/- English proof (translation)
Simplify using `only [cellWt, cellSet, measureReal_def, mul_assoc]`.
-/
theorem cellWt_eq {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (R K : Subgroup G) (ρ : Measure R) (μ : Measure G) (b : G) :
    cellWt ρ μ K b = (((μ (K : Set G)).toReal / (ρ (cellSet R K b b)).toReal : ℝ) : ℂ) := by
  simp only [cellWt, cellSet, measureReal_def, mul_assoc]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil`. Introduce `X S b q h hb hd _ hs`. Simplify using `only [NIter, List.map_nil, List.prod_nil, one_mul]`. Establish `hbh : ∀ β ∈ S, b β = h` using `fun β hβ => funext fun i => hb β hβ i (by simp)`.

Establish `hsub : ∀ β ∈ S, ∀ β' ∈ S, β = β'` using `fun β hβ β' hβ' => hd β hβ β' hβ' (fun i hi => by simp at hi)`. Distinguish the cases in `hq : q h = 0`. Rewrite using `[hq]`. Conclude with `Finset.sum_eq_zero fun β hβ => by rw [hbh β hβ, hq]`. Take `⟨β, hβ, -⟩` from `hs h (fun _ _ => rfl) hq`.

Rewrite using `[Finset.sum_eq_single β (fun β' hβ' hne => absurd (hsub β' hβ' β hβ) hne) (fun h' => absurd hβ h'), hbh β hβ]`. Consider the case `cons i l' ih`. Introduce `X S b q h hb hd hq hs`. Take `⟨hi, hl'⟩` from `List.nodup_cons.1 hl`. Take `⟨hcl, hkc, hko, hρ, hρi, hμ, hμr⟩` from `hyp i (by simp)`.

Establish `hyp' : ∀ j ∈ l', _` using `fun j hj => hyp j (List.mem_cons_of_mem _ hj)`. Establish `hq' : BiInv R K l' q` using `fun j hj => hq j (List.mem_cons_of_mem _ hj)`. Establish `hne : ∀ j ∈ l', j ≠ i` using `fun j hj hji => hi (hji ▸ hj)`. Use `set Wt' : X → ℂ := fun β => (l'.map fun j => cellWt (ρ j) (μ j) (K j) (b β j)).prod with hWt'`. Establish `qinv : ∀ β g, g ∈ dcos (R i) (K i) (b β i) → q (Function.update (b β) i g) = q (b β)`.

Introduce and unpack `β g ⟨r, hr, k, hk, rfl⟩`. Establish `h1` using `(hq i (by simp) (b β)).1 r hr`. Establish `h2` using `(hq i (by simp) (Function.update (b β) i (r * b β i))).2 k hk`. Simplify using `only [Function.update_self, Function.update_idem] at h2`. Rewrite using `[h2, h1]`.

Use `⟨fun g => ∑ β ∈ S, Wt' β * q (b β) * (if g ∈ dcos (R i) (K i) (b β i) then 1 else 0), ?_, ?_⟩` and prove the remaining obligations. Use `haveI := hρ`. Use `haveI := hρi`. Use `haveI := hμ`. Establish `hS` using `quotient_integral_finset_sum S (fun β g => Wt' β * q (b β) * (if g ∈ dcos (R i) (K i) (b β i) then (1 : ℂ) else 0)) (fun β => Wt' β * q (b β) * (((μ i (K i : Set (H i))).toReal / (ρ i (cellSet (R i) (K i) (b β i) (b β i))).toReal : ℝ) : ℂ)) (fun β _ => by`.

Use `(isQuotientIntegral_indicator_doubleCoset (R i) (K i) hcl hkc hko (ρ i) (μ i) (b β i)).smul (Wt' β * q (b β))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Simplify using `[smul_eq_mul])`. Use `hS using 1` and compare the differences between its conclusion and the goal.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `β _`. Rewrite using `[List.map_cons, List.prod_cons, cellWt_eq (R i)]`. Expand and normalize the polynomial expressions, which then agree. Introduce `g`.

Establish `key` using `ih hl' hyp' X (S.filter fun β => g ∈ dcos (R i) (K i) (b β i)) (fun β => Function.update (b β) i g) q (Function.update h i g) ?base ?dist hq' ?supp`. Use `key using 1` and compare the differences between its conclusion and the goal. Rewrite using `[Finset.sum_filter]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `β _`.

Use `split_ifs with hg`. Establish `e : (l'.map fun j => cellWt (ρ j) (μ j) (K j) (Function.update (b β) i g j)).prod = Wt' β`. Rewrite using `[hWt']`. Use `congr 1`. Apply `List.map_congr_left` to reduce the goal to its premises.

Introduce `j hj`. Rewrite using `[Function.update_of_ne (hne j hj)]`. Rewrite using `[e, qinv β g hg, mul_one]`. Simplify using the standard rewrite rules. Use `case base =>`.

Introduce `β hβ j hj`. Distinguish the cases in `hji : j = i`. Substitute `hji` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne hji, Function.update_of_ne hji]`.

Conclude with `hb β (Finset.mem_filter.1 hβ).1 j (by simp [hji, hj])`. Use `case dist =>`. Introduce `β hβ β' hβ' hc`. Take `⟨hβS, hgβ⟩` from `Finset.mem_filter.1 hβ`. Take `⟨hβS', hgβ'⟩` from `Finset.mem_filter.1 hβ'`.

Use `hd β hβS β' hβS' ?_` and prove the remaining obligations. Introduce `j hj`. Break down `List.mem_cons.1 hj with rfl | hj'` into its components or cases. Rewrite using `[cellBot_iff]`. Establish `e1` using `dcos_eq_of_mem hgβ`.

Establish `e2` using `dcos_eq_of_mem hgβ'`. Establish `hm : b β' j ∈ dcos (R j) (K j) (b β' j)` using `⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩`. Rewrite `hm` using `[← e2, e1]`. Conclude with `hm`. Take `⟨r, hr, a, ha, k, hk, e⟩` from `hc j hj'`.

Use `⟨r, hr, a, ha, k, hk, ?_⟩` and prove the remaining obligations. Simplify `e` using `[Function.update_of_ne (hne j hj')]`. Use `case supp =>`. Introduce `g' hg' hq0`. Establish `hgi : g' i = g` using `by simpa using hg' i hi`.

Take `⟨β, hβ, hc⟩` from `hs g' (fun j hj => by`. Establish `hji : j ≠ i` using `fun e => hj (e ▸ List.mem_cons_self ..)`. Use `hg' j (fun hj' => hj (List.mem_cons_of_mem _ hj'))` as an intermediate fact. Rewrite using `[Function.update_of_ne hji] at this) hq0` and apply the resulting hypothesis. Use `⟨β, Finset.mem_filter.2 ⟨hβ, ?_⟩, ?_⟩` and prove the remaining obligations.

Use `hc i (by simp)` as an intermediate fact. Rewrite `this` using `[cellBot_iff, hgi]`. Conclude with `this`. Introduce `j hj`. Take `⟨r, hr, a, ha, k, hk, e⟩` from `hc j (List.mem_cons_of_mem _ hj)`.

Use `⟨r, hr, a, ha, k, hk, ?_⟩` and prove the remaining obligations. Simplify `e` using `[Function.update_of_ne (hne j hj)]`.
-/
theorem niter_cellSum_at (ι : Type) [DecidableEq ι] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
    [∀ i, IsTopologicalGroup (H i)] [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)]
    (R K : ∀ i, Subgroup (H i)) (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)) (l : List ι) (hl : l.Nodup)
    (hyp : ∀ i ∈ l, IsClosed (R i : Set (H i)) ∧ IsCompact (K i : Set (H i)) ∧ IsOpen (K i : Set (H i)) ∧
      (ρ i).IsHaarMeasure ∧ (ρ i).IsInvInvariant ∧ (μ i).IsHaarMeasure ∧ (μ i).IsMulRightInvariant) :
    ∀ (X : Type) (S : Finset X) (b : X → ∀ i, H i) (q : (∀ i, H i) → ℂ) (h : ∀ i, H i),
      (∀ β ∈ S, ∀ i, i ∉ l → b β i = h i) →
      (∀ β ∈ S, ∀ β' ∈ S, InCells (fun _ => ⊥) R K l (b β) (b β') → β = β') → BiInv R K l q →
      (∀ g, (∀ i, i ∉ l → g i = h i) → q g ≠ 0 → ∃ β ∈ S, InCells (fun _ => ⊥) R K l (b β) g) →
      NIter ρ μ q l h (∑ β ∈ S, (l.map fun i => cellWt (ρ i) (μ i) (K i) (b β i)).prod * q (b β)) := by
  induction l with
  | nil =>
    intro X S b q h hb hd _ hs
    simp only [NIter, List.map_nil, List.prod_nil, one_mul]
    have hbh : ∀ β ∈ S, b β = h := fun β hβ => funext fun i => hb β hβ i (by simp)
    have hsub : ∀ β ∈ S, ∀ β' ∈ S, β = β' := fun β hβ β' hβ' => hd β hβ β' hβ' (fun i hi => by simp at hi)
    by_cases hq : q h = 0
    · rw [hq]
      exact Finset.sum_eq_zero fun β hβ => by rw [hbh β hβ, hq]
    · obtain ⟨β, hβ, -⟩ := hs h (fun _ _ => rfl) hq
      rw [Finset.sum_eq_single β (fun β' hβ' hne => absurd (hsub β' hβ' β hβ) hne) (fun h' => absurd hβ h'), hbh β hβ]
  | cons i l' ih =>
    intro X S b q h hb hd hq hs
    classical
    obtain ⟨hi, hl'⟩ := List.nodup_cons.1 hl
    obtain ⟨hcl, hkc, hko, hρ, hρi, hμ, hμr⟩ := hyp i (by simp)
    have hyp' : ∀ j ∈ l', _ := fun j hj => hyp j (List.mem_cons_of_mem _ hj)
    have hq' : BiInv R K l' q := fun j hj => hq j (List.mem_cons_of_mem _ hj)
    have hne : ∀ j ∈ l', j ≠ i := fun j hj hji => hi (hji ▸ hj)
    set Wt' : X → ℂ := fun β => (l'.map fun j => cellWt (ρ j) (μ j) (K j) (b β j)).prod with hWt'
    have qinv : ∀ β g, g ∈ dcos (R i) (K i) (b β i) → q (Function.update (b β) i g) = q (b β) := by
      rintro β g ⟨r, hr, k, hk, rfl⟩
      have h1 := (hq i (by simp) (b β)).1 r hr
      have h2 := (hq i (by simp) (Function.update (b β) i (r * b β i))).2 k hk
      simp only [Function.update_self, Function.update_idem] at h2
      rw [h2, h1]
    refine ⟨fun g => ∑ β ∈ S, Wt' β * q (b β) * (if g ∈ dcos (R i) (K i) (b β i) then 1 else 0), ?_, ?_⟩
    · haveI := hρ; haveI := hρi; haveI := hμ
      have hS := quotient_integral_finset_sum S (fun β g => Wt' β * q (b β) * (if g ∈ dcos (R i) (K i) (b β i) then (1 : ℂ) else 0))
        (fun β => Wt' β * q (b β) * (((μ i (K i : Set (H i))).toReal / (ρ i (cellSet (R i) (K i) (b β i) (b β i))).toReal : ℝ) : ℂ))
        (fun β _ => by
          have := (isQuotientIntegral_indicator_doubleCoset (R i) (K i) hcl hkc hko (ρ i) (μ i) (b β i)).smul (Wt' β * q (b β))
          convert this using 1
          funext g
          simp [smul_eq_mul])
      convert hS using 1
      apply Finset.sum_congr rfl
      intro β _
      rw [List.map_cons, List.prod_cons, cellWt_eq (R i)]
      ring
    · intro g
      have key := ih hl' hyp' X (S.filter fun β => g ∈ dcos (R i) (K i) (b β i)) (fun β => Function.update (b β) i g) q
        (Function.update h i g) ?base ?dist hq' ?supp
      · convert key using 1
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro β _
        split_ifs with hg
        · have e : (l'.map fun j => cellWt (ρ j) (μ j) (K j) (Function.update (b β) i g j)).prod = Wt' β := by
            rw [hWt']
            congr 1
            apply List.map_congr_left
            intro j hj
            rw [Function.update_of_ne (hne j hj)]
          rw [e, qinv β g hg, mul_one]
        · simp
      case base =>
        intro β hβ j hj
        by_cases hji : j = i
        · subst hji; simp
        · rw [Function.update_of_ne hji, Function.update_of_ne hji]
          exact hb β (Finset.mem_filter.1 hβ).1 j (by simp [hji, hj])
      case dist =>
        intro β hβ β' hβ' hc
        obtain ⟨hβS, hgβ⟩ := Finset.mem_filter.1 hβ
        obtain ⟨hβS', hgβ'⟩ := Finset.mem_filter.1 hβ'
        refine hd β hβS β' hβS' ?_
        intro j hj
        rcases List.mem_cons.1 hj with rfl | hj'
        · rw [cellBot_iff]
          have e1 := dcos_eq_of_mem hgβ
          have e2 := dcos_eq_of_mem hgβ'
          have hm : b β' j ∈ dcos (R j) (K j) (b β' j) := ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩
          rw [← e2, e1] at hm
          exact hm
        · obtain ⟨r, hr, a, ha, k, hk, e⟩ := hc j hj'
          refine ⟨r, hr, a, ha, k, hk, ?_⟩
          simpa [Function.update_of_ne (hne j hj')] using e
      case supp =>
        intro g' hg' hq0
        have hgi : g' i = g := by simpa using hg' i hi
        obtain ⟨β, hβ, hc⟩ := hs g' (fun j hj => by
          have hji : j ≠ i := fun e => hj (e ▸ List.mem_cons_self ..)
          have := hg' j (fun hj' => hj (List.mem_cons_of_mem _ hj'))
          rwa [Function.update_of_ne hji] at this) hq0
        refine ⟨β, Finset.mem_filter.2 ⟨hβ, ?_⟩, ?_⟩
        · have := hc i (by simp)
          rw [cellBot_iff, hgi] at this
          exact this
        · intro j hj
          obtain ⟨r, hr, a, ha, k, hk, e⟩ := hc j (List.mem_cons_of_mem _ hj)
          refine ⟨r, hr, a, ha, k, hk, ?_⟩
          simpa [Function.update_of_ne (hne j hj)] using e

/- English proof (translation)
Introduce `ι _ H _ _ _ _ _ _ _ _ R K l hl ρ μ hyp X S b q hb hd hq hs`. Conclude with `niter_cellSum_at ι H R K ρ μ l hl hyp X S b q 1 (fun β hβ i hi => by simpa using hb β hβ i hi) hd hq (fun g hg => hs g (fun i hi => by simpa using hg i hi))`.
-/
theorem niter_cellSum : ∀ (ι : Type) [DecidableEq ι] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, SecondCountableTopology (H i)] [∀ i, LocallyCompactSpace (H i)] [∀ i, T2Space (H i)] [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)] (R K : ∀ i, Subgroup (H i)) (l : List ι), l.Nodup → ∀ (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)), (∀ i ∈ l, IsClosed (R i : Set (H i)) ∧ IsCompact (K i : Set (H i)) ∧ IsOpen (K i : Set (H i)) ∧ (ρ i).IsHaarMeasure ∧ (ρ i).IsInvInvariant ∧ (μ i).IsHaarMeasure ∧ (μ i).IsMulRightInvariant) → ∀ (X : Type) (S : Finset X) (b : X → ∀ i, H i) (q : (∀ i, H i) → ℂ), (∀ β ∈ S, ∀ i, i ∉ l → b β i = 1) → (∀ β ∈ S, ∀ β' ∈ S, InCells (fun _ => ⊥) R K l (b β) (b β') → β = β') → BiInv R K l q → (∀ h, (∀ i, i ∉ l → h i = 1) → q h ≠ 0 → ∃ β ∈ S, InCells (fun _ => ⊥) R K l (b β) h) → NIter ρ μ q l 1 (∑ β ∈ S, (l.map fun i => cellWt (ρ i) (μ i) (K i) (b β i)).prod * q (b β)) := by
  intro ι _ H _ _ _ _ _ _ _ _ R K l hl ρ μ hyp X S b q hb hd hq hs
  exact niter_cellSum_at ι H R K ρ μ l hl hyp X S b q 1 (fun β hβ i hi => by simpa using hb β hβ i hi) hd hq
    (fun g hg => hs g (fun i hi => by simpa using hg i hi))

end GlobalTheory.RowVal
