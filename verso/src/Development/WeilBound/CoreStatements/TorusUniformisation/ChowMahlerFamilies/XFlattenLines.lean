import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsLatticeFamily
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XChartNoethFrac
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XCoherentGens
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.X_join_model

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace PositivityTheory.Xgn.A_flatten_lines

/- English proof (translation)
Set `L : AddSubgroup Ω` to `{ carrier := {w | ∃ r ∈ R', w = r * (m * v l₀)} add_mem' := by`. Introduce and unpack `_ _ ⟨r, hr, rfl⟩ ⟨s, hs, rfl⟩`. Conclude with `⟨r + s, R'.add_mem hr hs, by ring⟩`. Use the proof step `zero_mem' := ⟨0, R'.zero_mem, by simp⟩`. Use the proof step `neg_mem' := by`.

Introduce and unpack `_ ⟨r, hr, rfl⟩`. Conclude with `⟨-r, R'.neg_mem hr, by ring⟩ }`. Establish `hin : spanOver R (Set.range fun l => m • v l) ≤ L`. Unfold `spanOver`. Rewrite using `[AddSubgroup.closure_le]`.

Introduce and unpack `_ ⟨a, ha, e, ⟨l, rfl⟩, rfl⟩`. Use `⟨a * (v l / v l₀), R'.mul_mem (hle ha) (hq l), ?_⟩` and prove the remaining obligations. Simplify using `only [smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Establish `hout : spanOver R' (spanOver R (Set.range fun l => m • v l) : Set Ω) ≤ L`.

Unfold `spanOver`. Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `_ ⟨a, ha, e, he, rfl⟩`. Take `⟨r, hr, rfl⟩` from `hin he`. Conclude with `⟨a * r, R'.mul_mem ha hr, by simp only [smul_eq_mul]; ring⟩`.

Prove the components needed by the constructor for the conclusion. Introduce `hw`. Conclude with `hout hw`. Introduce and unpack `⟨r, hr, rfl⟩`. Establish `hm : m • v l₀ ∈ spanOver R (Set.range fun l => m • v l)` using `AddSubgroup.subset_closure ⟨1, R.one_mem, m • v l₀, ⟨l₀, rfl⟩, by simp⟩`.

Conclude with `AddSubgroup.subset_closure ⟨r, hr, m • v l₀, hm, by simp⟩`.
-/
theorem span_line {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] (R R' : Subalgebra O Ω) (hle : R ≤ R')
    {M : ℕ} (v : Fin M → Ω) (m : Ω) (l₀ : Fin M) (h0 : v l₀ ≠ 0) (hq : ∀ l, v l / v l₀ ∈ R') (w : Ω) :
    w ∈ spanOver R' (spanOver R (Set.range fun l => m • v l) : Set Ω) ↔ ∃ r ∈ R', w = r * (m * v l₀) := by
  let L : AddSubgroup Ω :=
    { carrier := {w | ∃ r ∈ R', w = r * (m * v l₀)}
      add_mem' := by
        rintro _ _ ⟨r, hr, rfl⟩ ⟨s, hs, rfl⟩
        exact ⟨r + s, R'.add_mem hr hs, by ring⟩
      zero_mem' := ⟨0, R'.zero_mem, by simp⟩
      neg_mem' := by
        rintro _ ⟨r, hr, rfl⟩
        exact ⟨-r, R'.neg_mem hr, by ring⟩ }
  have hin : spanOver R (Set.range fun l => m • v l) ≤ L := by
    unfold spanOver
    rw [AddSubgroup.closure_le]
    rintro _ ⟨a, ha, e, ⟨l, rfl⟩, rfl⟩
    refine ⟨a * (v l / v l₀), R'.mul_mem (hle ha) (hq l), ?_⟩
    simp only [smul_eq_mul]
    field_simp
  have hout : spanOver R' (spanOver R (Set.range fun l => m • v l) : Set Ω) ≤ L := by
    unfold spanOver
    rw [AddSubgroup.closure_le]
    rintro _ ⟨a, ha, e, he, rfl⟩
    obtain ⟨r, hr, rfl⟩ := hin he
    exact ⟨a * r, R'.mul_mem ha hr, by simp only [smul_eq_mul]; ring⟩
  constructor
  · intro hw
    exact hout hw
  · rintro ⟨r, hr, rfl⟩
    have hm : m • v l₀ ∈ spanOver R (Set.range fun l => m • v l) :=
      AddSubgroup.subset_closure ⟨1, R.one_mem, m • v l₀, ⟨l₀, rfl⟩, by simp⟩
    exact AddSubgroup.subset_closure ⟨r, hr, m • v l₀, hm, by simp⟩

/- English proof (translation)
Unfold `chartMon restrictChart`. Rewrite using `[Fintype.prod_sum_type]`. Simplify using `only [joinCoord, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]`. Use `congr 1`. Rewrite using `[Finset.prod_eq_single j]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Pi.single_apply, hb]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ j) h`.
-/
theorem chartMon_join {Ω : Type} [Field Ω] {K K' : Type} [Fintype K] [Fintype K'] [DecidableEq K']
    {ι : K → Type} {ι' : K' → Type} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    (c : ∀ k : K ⊕ K', Sum.elim ι ι' k) (a : K → ℤ) (j : K') :
    chartMon (joinCoord x z) c (Sum.elim (-a) (Pi.single j 1)) =
      (chartMon x (restrictChart c) a)⁻¹ * z ⟨j, c (.inr j)⟩ := by
  unfold chartMon restrictChart
  rw [Fintype.prod_sum_type]
  simp only [joinCoord, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]
  congr 1
  rw [Finset.prod_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ j) h

end PositivityTheory.Xgn.A_flatten_lines

/- English proof (translation)
Introduce `O _ _ _ Ω _ _ K _ _ ι _ x d hmod hfn I _ Γ hΓ`. Take `⟨_, hx0, _, _⟩` from `(PositivityTheory.Xgn.A_join_model.isModelOver_iff x d).mp hmod`. Use `choose c0 hc0 using hx0`. Establish `hm0 : mseg x c0 ≠ 0`. Unfold `mseg`.

Conclude with `Finset.prod_ne_zero_iff.mpr fun k _ => hc0 k`. Establish `key : ∀ j, ∃ (a : K → ℤ) (M : ℕ) (v : Fin M → Ω), ∀ c, mseg x c ≠ 0 → Γ j c = spanOver (chartRing O (mseg x) c) (Set.range fun l => (chartMon x c a)⁻¹ • v l)`. Introduce `j`. Take `⟨a₁, ha₁⟩` from `PositivityTheory.Xgn.t_coherent_gens O Ω K ι x Ω (Γ j) (hΓ j).1 (fun c hc => ((hΓ j).2 c hc).2)`. Take `⟨M, v, hv⟩` from `ha₁ a₁ le_rfl`.

Conclude with `⟨a₁, M, v, hv⟩`. Use `choose a M v hv using key`. Establish `hnz : ∀ j, ∃ l, v j l ≠ 0`. Introduce `j`. Assume the negation of the conclusion as `hall`.

Use `push_neg at hall`. Apply `((hΓ j).2 c0 hm0).1` to reduce the goal to its premises. Rewrite using `[hv j c0 hm0, eq_bot_iff]`. Unfold `spanOver`. Rewrite using `[AddSubgroup.closure_le]`.

Introduce and unpack `_ ⟨r, _, e, ⟨l, rfl⟩, rfl⟩`. Simplify using `[hall l]`. Set `z : (Σ j : I, Fin (M j)) → Ω` to `fun p => v p.1 p.2`. Establish `hJ` using `(PositivityTheory.Xgn.t_chart_noeth_frac O Ω K ι x).2.2 I (fun j => Fin (M j)) z`. Use `⟨I, inferInstance, inferInstance, fun j => Fin (M j), fun _ => inferInstance, z, ?_, ?_⟩` and prove the remaining obligations.

Establish `hmodJ` using `PositivityTheory.Xgn.t_join_model O Ω K ι x d 0 hmod I (fun j => Fin (M j)) z hnz Fin.elim0 algebraicIndependent_empty_type (fun i => Fin.elim0 i) ?_`. Simplify using `using hmodJ`. Introduce `w _`. Establish `hw : w ∈ fnField O x`. Rewrite using `[hfn]`.

Conclude with `Subfield.mem_top w`. Conclude with `isAlgebraic_algebraMap (⟨w, IntermediateField.algebraMap_mem _ (⟨w, hw⟩ : fnField O x)⟩ : IntermediateField.adjoin (fnField O x) (Set.range (Fin.elim0 : Fin 0 → Ω)))`. Introduce `j`. Use `⟨Sum.elim (-a j) (Pi.single j 1), ?_⟩` and prove the remaining obligations. Introduce `c hc w`.

Take `⟨hrc, hle⟩` from `hJ.2 c hc`. Establish `hmz` using `PositivityTheory.Xgn.A_chart_noeth_frac.mseg_join x z c`. Establish `hz0 : z ⟨j, c (Sum.inr j)⟩ ≠ 0`. Rewrite `hc` using `[hmz]`. Establish `h2` using `right_ne_zero_of_mul hc`.

Unfold `mseg at h2`. Conclude with `Finset.prod_ne_zero_iff.mp h2 j (Finset.mem_univ _)`. Use `show w ∈ spanOver (chartRing O (mseg (joinCoord x z)) c) (Γ j (restrictChart c) : Set Ω) ↔ _`. Rewrite using `[hv j _ hrc, one_mul, PositivityTheory.Xgn.A_flatten_lines.chartMon_join]`. Use `PositivityTheory.Xgn.A_flatten_lines.span_line _ _ hle _ _ (c (Sum.inr j)) hz0 ?_ w` and prove the remaining obligations.

Introduce `l`. Establish `h` using `PositivityTheory.Xgn.A_chart_noeth_frac.ratio_eq (joinCoord x z) c hc (Sum.inr j) l`. Establish `hmem : mseg (joinCoord x z) (Function.update c (Sum.inr j) l) / mseg (joinCoord x z) c ∈ chartRing O (mseg (joinCoord x z)) c` using `Algebra.subset_adjoin ⟨_, rfl⟩`. Rewrite `hmem` using `[h]`. Conclude with `hmem`.
-/
theorem PositivityTheory.Xgn.t_flatten_lines : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ (I : Type) [Fintype I] (Γ : I → (∀ k, ι k) → AddSubgroup Ω), (∀ j, IsLatFamily O x (Γ j) ∧ ∀ c, mseg x c ≠ 0 → Γ j c ≠ ⊥ ∧ ∃ S : Finset Ω, Γ j c = spanOver (chartRing O (mseg x) c) (S : Set Ω)) → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ ∀ j, ∃ a : K ⊕ K' → ℤ, IsLine O (joinCoord x z) 1 a fun c => spanOver (chartRing O (mseg (joinCoord x z)) c) (Γ j (restrictChart c) : Set Ω) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hmod hfn I _ Γ hΓ
  classical
  obtain ⟨_, hx0, _, _⟩ := (PositivityTheory.Xgn.A_join_model.isModelOver_iff x d).mp hmod
  choose c0 hc0 using hx0
  have hm0 : mseg x c0 ≠ 0 := by
    unfold mseg
    exact Finset.prod_ne_zero_iff.mpr fun k _ => hc0 k
  have key : ∀ j, ∃ (a : K → ℤ) (M : ℕ) (v : Fin M → Ω), ∀ c, mseg x c ≠ 0 →
      Γ j c = spanOver (chartRing O (mseg x) c) (Set.range fun l => (chartMon x c a)⁻¹ • v l) := by
    intro j
    obtain ⟨a₁, ha₁⟩ := PositivityTheory.Xgn.t_coherent_gens O Ω K ι x Ω (Γ j) (hΓ j).1
      (fun c hc => ((hΓ j).2 c hc).2)
    obtain ⟨M, v, hv⟩ := ha₁ a₁ le_rfl
    exact ⟨a₁, M, v, hv⟩
  choose a M v hv using key
  have hnz : ∀ j, ∃ l, v j l ≠ 0 := by
    intro j
    by_contra hall
    push_neg at hall
    apply ((hΓ j).2 c0 hm0).1
    rw [hv j c0 hm0, eq_bot_iff]
    unfold spanOver
    rw [AddSubgroup.closure_le]
    rintro _ ⟨r, _, e, ⟨l, rfl⟩, rfl⟩
    simp [hall l]
  let z : (Σ j : I, Fin (M j)) → Ω := fun p => v p.1 p.2
  have hJ := (PositivityTheory.Xgn.t_chart_noeth_frac O Ω K ι x).2.2 I (fun j => Fin (M j)) z
  refine ⟨I, inferInstance, inferInstance, fun j => Fin (M j), fun _ => inferInstance, z, ?_, ?_⟩
  · have hmodJ := PositivityTheory.Xgn.t_join_model O Ω K ι x d 0 hmod I (fun j => Fin (M j)) z hnz
      Fin.elim0 algebraicIndependent_empty_type (fun i => Fin.elim0 i) ?_
    · simpa using hmodJ
    · intro w _
      have hw : w ∈ fnField O x := by
        rw [hfn]
        exact Subfield.mem_top w
      exact isAlgebraic_algebraMap
        (⟨w, IntermediateField.algebraMap_mem _ (⟨w, hw⟩ : fnField O x)⟩ :
          IntermediateField.adjoin (fnField O x) (Set.range (Fin.elim0 : Fin 0 → Ω)))
  · intro j
    refine ⟨Sum.elim (-a j) (Pi.single j 1), ?_⟩
    intro c hc w
    obtain ⟨hrc, hle⟩ := hJ.2 c hc
    have hmz := PositivityTheory.Xgn.A_chart_noeth_frac.mseg_join x z c
    have hz0 : z ⟨j, c (Sum.inr j)⟩ ≠ 0 := by
      rw [hmz] at hc
      have h2 := right_ne_zero_of_mul hc
      unfold mseg at h2
      exact Finset.prod_ne_zero_iff.mp h2 j (Finset.mem_univ _)
    show w ∈ spanOver (chartRing O (mseg (joinCoord x z)) c) (Γ j (restrictChart c) : Set Ω) ↔ _
    rw [hv j _ hrc, one_mul, PositivityTheory.Xgn.A_flatten_lines.chartMon_join]
    refine PositivityTheory.Xgn.A_flatten_lines.span_line _ _ hle _ _ (c (Sum.inr j)) hz0 ?_ w
    intro l
    have h := PositivityTheory.Xgn.A_chart_noeth_frac.ratio_eq (joinCoord x z) c hc (Sum.inr j) l
    have hmem : mseg (joinCoord x z) (Function.update c (Sum.inr j) l) / mseg (joinCoord x z) c ∈
        chartRing O (mseg (joinCoord x z)) c := Algebra.subset_adjoin ⟨_, rfl⟩
    rw [h] at hmem
    exact hmem
