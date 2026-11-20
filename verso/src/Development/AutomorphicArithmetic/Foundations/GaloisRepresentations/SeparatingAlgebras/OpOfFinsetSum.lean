import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

/- English proof (translation)
Unfold `opOf`. Simplify using `only [Finsupp.sum, map_sum, Finset.smul_sum]`. Conclude with `Finset.sum_comm`.
-/
private theorem opOf_finset_sum {Γ V ι : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V)
    (f : Γ →₀ ℂ) (I : Finset ι) (u : ι → V) : opOf ρ f (∑ i ∈ I, u i) = ∑ i ∈ I, opOf ρ f (u i) := by
  unfold opOf
  simp only [Finsupp.sum, map_sum, Finset.smul_sum]
  exact Finset.sum_comm

/- English proof (translation)
Use `haveI : CompactSpace A := isCompact_iff_compactSpace.1 hA`. Establish `ho : IsOpen ((B.subgroupOf A : Subgroup A) : Set A)` using `hB.preimage continuous_subtype_val`. Conclude with `Subgroup.quotient_finite_of_isOpen _ ho`.
-/
private theorem finite_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {A B : Subgroup G}
    (hA : IsCompact (A : Set G)) (hB : IsOpen (B : Set G)) : Finite (A ⧸ B.subgroupOf A) := by
  haveI : CompactSpace A := isCompact_iff_compactSpace.1 hA
  have ho : IsOpen ((B.subgroupOf A : Subgroup A) : Set A) := hB.preimage continuous_subtype_val
  exact Subgroup.quotient_finite_of_isOpen _ ho

/- English proof (translation)
Establish `hd : 0 < M * s + 1` using `by positivity`. Establish `h1 : M * s * t ≤ ε`. Establish `hMs : 0 ≤ M * s` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem bound_arith {M s ε c t : ℝ} (hM : 0 ≤ M) (hs : 0 ≤ s) (hε : 0 < ε) (hc : 0 ≤ c) (ht : t ≤ ε / (M * s + 1)) :
    M * (s * c) * t ≤ ε * c := by
  have hd : 0 < M * s + 1 := by positivity
  have h1 : M * s * t ≤ ε := by
    have hMs : 0 ≤ M * s := by positivity
    calc M * s * t ≤ M * s * (ε / (M * s + 1)) := mul_le_mul_of_nonneg_left ht hMs
      _ = ε * (M * s / (M * s + 1)) := by ring
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left ((div_le_one hd).2 (by linarith)) hε.le
      _ = ε := mul_one ε
  calc M * (s * c) * t = (M * s * t) * c := by ring
    _ ≤ ε * c := mul_le_mul_of_nonneg_right h1 hc

/- English proof (translation)
Introduce `hCore hCover hSep hPart E _ _ _ a w₀ hs K hK J hJ W B hB ε hε`. Take `⟨M, hM0, hM⟩` from `hCore E a W`. Take `⟨S, hS⟩` from `hCover E a w₀ hs K hK J hJ`. Establish `hδ : 0 < ε / (M * (S.card : ℝ) + 1)` using `by positivity`. Take `⟨h, h1, h2, h3, h4⟩` from `hB _ hδ`.

Take `⟨n₀, hn₀⟩` from `hSep E a w₀ hs K hK J hJ S h.support h1 h2`. Use `⟨n₀, fun n hn => ?_⟩` and prove the remaining obligations. Use `haveI : Finite (J 0 ⧸ (J n).subgroupOf (J 0)) := finite_quot (hJ.compact 0) (hJ.isOpen n)`. Use `letI : Fintype (J 0 ⧸ (J n).subgroupOf (J 0)) := Fintype.ofFinite _`. Take `⟨r, hr, hcov⟩` from `hS n`.

Establish `hsep : Separates (lev K w₀ (J n)) (fun y : S × (J 0 ⧸ (J n).subgroupOf (J 0)) => y.1.1 * r y.2) h.support` using `fun y g hg g' hg' γ hγ x hx c hc e => hn₀ n hn (y.1, ⟨r y.2, hr y.2⟩) g hg g' hg' γ hγ x hx c hc e`. Establish `hfix : ∀ f ∈ part W (lev K w₀ (J n)) B, ∀ v, opOf (RU E a) h (f.1 v) = f.1 v`. Introduce `f hf v`. Take `⟨I, F, hF, rfl⟩` from `(hPart E a W (lev K w₀ (J n)) B).2.2.2.2 f hf`. Establish `e : (∑ π ∈ I, F π : algForms W).1 v = ∑ π ∈ I, (F π).1 v`.

Simplify using `[Submodule.coe_sum, LinearMap.sum_apply]`. Rewrite using `[e, opOf_finset_sum]`. Use `Finset.sum_congr rfl fun π hπ => ?_` and prove the remaining obligations. Take `⟨hP, hfin, hfx, -⟩` from `hF π hπ`. Use `h4 π.V π.isAut hP _ (AutSub.mem_finPart.1 hfin v) fun x hx => funext fun g => ?_` and prove the remaining obligations.

Rewrite using `[RU_apply]`. Conclude with `hfx x ((le_sup_left : K ≤ lev K w₀ (J n)) hx) v g`. Take `⟨hfd, hle⟩` from `hM (lev K w₀ (J n)) _ _ hcov h hsep (part W (lev K w₀ (J n)) B) (hPart E a W (lev K w₀ (J n)) B).2.1 hfix`. Use `⟨hfd, hle.trans ?_⟩` and prove the remaining obligations. Establish `hcard : (Fintype.card (S × (J 0 ⧸ (J n).subgroupOf (J 0))) : ℝ) = (S.card : ℝ) * (Nat.card (J 0 ⧸ (J n).subgroupOf (J 0)) : ℝ)`.

Rewrite using `[Fintype.card_prod, Fintype.card_coe, Nat.card_eq_fintype_card]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[hcard]`. Conclude with `bound_arith hM0 (Nat.cast_nonneg _) hε (Nat.cast_nonneg _) h3`.
-/
theorem UpperTheory.Gal.Gen.count_pf :
    UpperTheory.Gal.Gen.CountCore → UpperTheory.Gal.Gen.Cover → UpperTheory.Gal.Gen.Sep → UpperTheory.Gal.Gen.PartFacts → UpperTheory.Gal.Gen.Count := by
  intro hCore hCover hSep hPart E _ _ _ a w₀ hs K hK J hJ W B hB ε hε
  obtain ⟨M, hM0, hM⟩ := hCore E a W
  obtain ⟨S, hS⟩ := hCover E a w₀ hs K hK J hJ
  have hδ : 0 < ε / (M * (S.card : ℝ) + 1) := by positivity
  obtain ⟨h, h1, h2, h3, h4⟩ := hB _ hδ
  obtain ⟨n₀, hn₀⟩ := hSep E a w₀ hs K hK J hJ S h.support h1 h2
  refine ⟨n₀, fun n hn => ?_⟩
  haveI : Finite (J 0 ⧸ (J n).subgroupOf (J 0)) := finite_quot (hJ.compact 0) (hJ.isOpen n)
  letI : Fintype (J 0 ⧸ (J n).subgroupOf (J 0)) := Fintype.ofFinite _
  obtain ⟨r, hr, hcov⟩ := hS n
  have hsep : Separates (lev K w₀ (J n)) (fun y : S × (J 0 ⧸ (J n).subgroupOf (J 0)) => y.1.1 * r y.2) h.support :=
    fun y g hg g' hg' γ hγ x hx c hc e =>
      hn₀ n hn (y.1, ⟨r y.2, hr y.2⟩) g hg g' hg' γ hγ x hx c hc e
  have hfix : ∀ f ∈ part W (lev K w₀ (J n)) B, ∀ v, opOf (RU E a) h (f.1 v) = f.1 v := by
    intro f hf v
    obtain ⟨I, F, hF, rfl⟩ := (hPart E a W (lev K w₀ (J n)) B).2.2.2.2 f hf
    have e : (∑ π ∈ I, F π : algForms W).1 v = ∑ π ∈ I, (F π).1 v := by
      simp [Submodule.coe_sum, LinearMap.sum_apply]
    rw [e, opOf_finset_sum]
    refine Finset.sum_congr rfl fun π hπ => ?_
    obtain ⟨hP, hfin, hfx, -⟩ := hF π hπ
    refine h4 π.V π.isAut hP _ (AutSub.mem_finPart.1 hfin v) fun x hx => funext fun g => ?_
    rw [RU_apply]
    exact hfx x ((le_sup_left : K ≤ lev K w₀ (J n)) hx) v g
  obtain ⟨hfd, hle⟩ := hM (lev K w₀ (J n)) _ _ hcov h hsep (part W (lev K w₀ (J n)) B)
    (hPart E a W (lev K w₀ (J n)) B).2.1 hfix
  refine ⟨hfd, hle.trans ?_⟩
  have hcard : (Fintype.card (S × (J 0 ⧸ (J n).subgroupOf (J 0))) : ℝ) =
      (S.card : ℝ) * (Nat.card (J 0 ⧸ (J n).subgroupOf (J 0)) : ℝ) := by
    rw [Fintype.card_prod, Fintype.card_coe, Nat.card_eq_fintype_card]
    push_cast
    rfl
  rw [hcard]
  exact bound_arith hM0 (Nat.cast_nonneg _) hε (Nat.cast_nonneg _) h3
