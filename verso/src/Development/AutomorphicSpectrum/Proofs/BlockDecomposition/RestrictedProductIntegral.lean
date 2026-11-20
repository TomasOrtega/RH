import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFamInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPairProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisExtra
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteRestrictedProductQuotientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedProductHeckeSumStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

noncomputable section

namespace GlobalTheory.CompanionTheory.FinActCore

/- English proof (translation)
Establish `hmem : ∀ c : K ⧸ L.subgroupOf K, (((c.out : K) : G) : G ⧸ L).out ∈ K`. Introduce `c`. Take `⟨t, ht⟩` from `QuotientGroup.mk_out_eq_mul L ((c.out : K) : G)`. Rewrite using `[ht]`. Conclude with `mul_mem (c.out).2 (hLK t.2)`.

Establish `hinj : Function.Injective (fun c : K ⧸ L.subgroupOf K => (⟨(((c.out : K) : G) : G ⧸ L), hmem c⟩ : {q : G ⧸ L | q.out ∈ K}))`. Introduce `a b hab`. Establish `h1 : (((a.out : K) : G) : G ⧸ L) = (((b.out : K) : G) : G ⧸ L)` using `congrArg Subtype.val hab`. Establish `h2 : ((a.out : K) : G)⁻¹ * ((b.out : K) : G) ∈ L` using `QuotientGroup.eq.1 h1`. Rewrite using `[← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b]`.

Use `QuotientGroup.eq.2 ?_` and prove the remaining obligations. Rewrite using `[Subgroup.mem_subgroupOf]`. Simplify using `using h2`. Use `haveI := h.to_subtype`. Use `haveI : Finite (K ⧸ L.subgroupOf K) := Finite.of_injective _ hinj`.

Conclude with `Subgroup.index_ne_zero_of_finite`.
-/
theorem relIndex_ne_of_out {G : Type} [Group G] (L K : Subgroup G) (hLK : L ≤ K)
    (h : {q : G ⧸ L | q.out ∈ K}.Finite) : L.relIndex K ≠ 0 := by
  have hmem : ∀ c : K ⧸ L.subgroupOf K, (((c.out : K) : G) : G ⧸ L).out ∈ K := by
    intro c
    obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul L ((c.out : K) : G)
    rw [ht]
    exact mul_mem (c.out).2 (hLK t.2)
  have hinj : Function.Injective (fun c : K ⧸ L.subgroupOf K =>
      (⟨(((c.out : K) : G) : G ⧸ L), hmem c⟩ : {q : G ⧸ L | q.out ∈ K})) := by
    intro a b hab
    have h1 : (((a.out : K) : G) : G ⧸ L) = (((b.out : K) : G) : G ⧸ L) :=
      congrArg Subtype.val hab
    have h2 : ((a.out : K) : G)⁻¹ * ((b.out : K) : G) ∈ L := QuotientGroup.eq.1 h1
    rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b]
    refine QuotientGroup.eq.2 ?_
    rw [Subgroup.mem_subgroupOf]
    simpa using h2
  haveI := h.to_subtype
  haveI : Finite (K ⧸ L.subgroupOf K) := Finite.of_injective _ hinj
  exact Subgroup.index_ne_zero_of_finite

/- English proof (translation)
Establish `hm : Nat.card (K ⧸ V.subgroupOf K) ≠ 0` using `hi`. Use `haveI : Finite (K ⧸ V.subgroupOf K) := Nat.finite_of_card_ne_zero hm`. Establish `hinj : Function.Injective (fun q : {q : H ⧸ V | q.out ∈ K} => (((⟨q.1.out, q.2⟩ : K)) : K ⧸ V.subgroupOf K))`. Introduce `a b hab`. Establish `h1` using `QuotientGroup.eq.1 hab`.

Rewrite `h1` using `[Subgroup.mem_subgroupOf]`. Establish `h2 : (a.1.out)⁻¹ * b.1.out ∈ V` using `by simpa using h1`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← QuotientGroup.out_eq' a.1, ← QuotientGroup.out_eq' b.1]`. Conclude with `QuotientGroup.eq.2 h2`.

Use `haveI : Finite {q : H ⧸ V | q.out ∈ K} := Finite.of_injective _ hinj`. Conclude with `Set.toFinite _`.
-/
theorem out_finite_of_relIndex {H : Type} [Group H] (V K : Subgroup H) (hi : V.relIndex K ≠ 0) :
    {q : H ⧸ V | q.out ∈ K}.Finite := by
  have hm : Nat.card (K ⧸ V.subgroupOf K) ≠ 0 := hi
  haveI : Finite (K ⧸ V.subgroupOf K) := Nat.finite_of_card_ne_zero hm
  have hinj : Function.Injective (fun q : {q : H ⧸ V | q.out ∈ K} =>
      (((⟨q.1.out, q.2⟩ : K)) : K ⧸ V.subgroupOf K)) := by
    intro a b hab
    have h1 := QuotientGroup.eq.1 hab
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : (a.1.out)⁻¹ * b.1.out ∈ V := by simpa using h1
    apply Subtype.ext
    rw [← QuotientGroup.out_eq' a.1, ← QuotientGroup.out_eq' b.1]
    exact QuotientGroup.eq.2 h2
  haveI : Finite {q : H ⧸ V | q.out ∈ K} := Finite.of_injective _ hinj
  exact Set.toFinite _

/- English proof (translation)
Introduce `ι Γ _ Hl _ p e K KH V f hpe hpe' hsep hev hK hVK hVi hVe hfV hfs g hg l hl hfix`. Establish `hmemL : ∀ u, u ∈ (⨅ i, (V i).comap (p i)) ↔ ∀ i, p i u ∈ V i`. Introduce `u`. Simplify using `[Subgroup.mem_iInf]`. Generalize the expression as in `hLdef : (⨅ i, (V i).comap (p i)) = L at hmemL`.

Establish `hLK : L ≤ K` using `fun u hu => (hK u).2 fun i => hVK i ((hmemL u).1 hu i)`. Establish `hfinKH : ∀ i, {q : Hl i ⧸ V i | q.out ∈ KH i}.Finite` using `fun i => out_finite_of_relIndex (V i) (KH i) (hVi i)`. Establish `hVe1 : ∀ᶠ i in cofinite, V i = KH i` using `hVe.mono fun i h => h.1`. Establish `hidx : L.relIndex K ≠ 0`. Use `relIndex_ne_of_out L K hLK ?_` and prove the remaining obligations.

Establish `h0` using `GlobalTheory.T.finite_restricted_product_quotient p V (fun i => (KH i : Set (Hl i))) (fun i x hx u hu => mul_mem hx (hVK i hu)) hfinKH (hVe1.mono fun i h x hx => by`. Rewrite using `[SetLike.mem_coe, h]`. Conclude with `hx)`. Rewrite `h0` using `[hLdef]`. Conclude with `h0.subset fun q hq => (hK _).1 hq`.

Establish `hB` using `Filter.eventually_cofinite.1 hVe`. Choose the witnesses or unpack the hypotheses as in `⟨extra, hextra, hend, hcov⟩ : ∃ extra : List ι, (∀ i ∈ extra, i ∉ l) ∧ extra.Nodup ∧ ∀ j, j ∉ l ++ extra → V j = KH j ∧ f j = (KH j : Set (Hl j)).indicator 1 := by`. Use `⟨(hB.toFinset.filter (· ∉ l)).toList, ?_, Finset.nodup_toList _, ?_⟩` and prove the remaining obligations. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_toList, Finset.mem_filter]`.

Conclude with `hi.2`. Introduce `j hj`. Assume the negation of the conclusion as `hc`. Apply `hj` to reduce the goal to its premises. Rewrite using `[List.mem_append]`.

Distinguish the cases in `hjl : j ∈ l`. Conclude with `Or.inl hjl`. Use `Or.inr ?_` and prove the remaining obligations. Rewrite using `[Finset.mem_toList, Finset.mem_filter]`. Conclude with `⟨hB.mem_toFinset.2 hc, hjl⟩`.

Establish `hnd : (l ++ extra).Nodup` using `List.Nodup.append hl hend fun a ha hb => hextra a hb ha`. Generalize the expression as in `hT : l ++ extra = T at hnd hcov`. Establish `hfoldE : ∀ m : List ι, (∀ i ∈ m, i ∉ l) → m.foldr (fun i g' x => hint (KH i) fun m => f i m * g' (x * e i m)) g = g`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `nil => intro _`. Both sides reduce to the same expression. Consider the case `cons a t ih`. Introduce `hm`. Rewrite using `[List.foldr_cons, ih fun i hi => hm i (List.mem_cons_of_mem _ hi)]`.

Conclude with `hfix a (hm a List.mem_cons_self)`. Establish `hfold : T.foldr (fun i g' x => hint (KH i) fun m => f i m * g' (x * e i m)) g = l.foldr (fun i g' x => hint (KH i) fun m => f i m * g' (x * e i m)) g`. Rewrite using `[← hT, List.foldr_append, hfoldE extra hextra]`. Establish `hsum` using `GlobalTheory.T.restricted_product_hecke_sum p e KH V f hpe hpe' hsep hev hVK hVi hVe1 hfV hfs T hnd g hg 1`. Rewrite `hsum` using `[hLdef]`.

Simplify using `only [one_mul] at hsum`. Establish `hF : ∀ x, (∏ᶠ j, if j ∈ T then f j (p j x) else (V j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j x)) = ∏ᶠ i, f i (p i x)`. Introduce `x`. Use `finprod_congr fun j => ?_` and prove the remaining obligations. Use `split_ifs with hj`.

Both sides reduce to the same expression. Take `⟨h1, h2⟩` from `hcov j hj`. Rewrite using `[h2, h1]`. Simplify using `only [hF] at hsum`. Establish `hlev : L ≤ rStab (fun x => (∏ᶠ i, f i (p i x)) * g x)`.

Introduce `r hr`. Use `GlobalTheory.CompanionTheory.FamClP.mem_rStab'.2 fun x => ?_` and prove the remaining obligations. Establish `h1 : (∏ᶠ i, f i (p i (x * r))) = ∏ᶠ i, f i (p i x)`. Use `finprod_congr fun i => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`.

Conclude with `hfV i _ ((hmemL r).1 hr i) _`. Use `show (∏ᶠ i, f i (p i (x * r))) * g (x * r) = (∏ᶠ i, f i (p i x)) * g x`. Rewrite using `[h1, hg r ((hmemL r).1 hr) x]`. Establish `h1` using `GlobalTheory.CompanionTheory.HintLevel.hint_eq_level Γ K L (fun x => (∏ᶠ i, f i (p i x)) * g x) hLK hlev hidx`. Establish `hfVI : ∀ i, ∀ u ∈ V i, ∀ x, (KH i : Set (Hl i)).indicator (1 : Hl i → ℂ) (x * u) = (KH i : Set (Hl i)).indicator (1 : Hl i → ℂ) x`.

Introduce `i u hu x`. Establish `h0 : u ∈ rStab ((KH i : Set (Hl i)).indicator (1 : Hl i → ℂ))`. Rewrite using `[GlobalTheory.CompanionTheory.FamClP.rStab_ind]`. Conclude with `hVK i hu`. Conclude with `GlobalTheory.CompanionTheory.FamClP.mem_rStab'.1 h0 x`.

Establish `hfsI : ∀ i, {q : Hl i ⧸ V i | (KH i : Set (Hl i)).indicator (1 : Hl i → ℂ) q.out ≠ 0}.Finite`. Introduce `i`. Use `(hfinKH i).subset fun q hq => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Conclude with `hq (Set.indicator_of_notMem (s := (KH i : Set (Hl i))) (show q.out ∉ (KH i : Set (Hl i)) from hn) _)`.

Establish `hsum2` using `GlobalTheory.T.restricted_product_hecke_sum p e KH V (fun i => (KH i : Set (Hl i)).indicator (1 : Hl i → ℂ)) hpe hpe' hsep hev hVK hVi hVe1 hfVI hfsI T hnd (fun _ => 1) (fun _ _ _ => rfl) 1`. Rewrite `hsum2` using `[hLdef]`. Establish `hfold2 : ∀ m : List ι, m.foldr (fun i g' x => hint (KH i) fun m => (KH i : Set (Hl i)).indicator (1 : Hl i → ℂ) m * g' (x * e i m)) (fun _ => (1 : ℂ)) = fun _ => 1`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `nil => rfl`. Consider the case `cons a t ih`. Rewrite using `[List.foldr_cons, ih]`. Use function extensionality and compare the values at `x`. Simplify using `only [mul_one]`.

Conclude with `GlobalTheory.CompanionTheory.FamClP.hint_ind _`. Rewrite `hsum2` using `[hfold2 T]`. Establish `hF2 : ∀ x, (∏ᶠ j, if j ∈ T then (KH j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j x) else (V j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j x)) = (K : Set Γ).indicator (1 : Γ → ℂ) x`. Introduce `x`. Establish `h0 : (∏ᶠ j, if j ∈ T then (KH j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j x) else (V j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j x)) = ∏ᶠ j, (KH j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j x)`.

Use `finprod_congr fun j => ?_` and prove the remaining obligations. Use `split_ifs with hj`. Both sides reduce to the same expression. Rewrite using `[(hcov j hj).1]`. Rewrite using `[h0]`.

Distinguish the cases in `hx : x ∈ K`. Establish `h2 : (K : Set Γ).indicator (1 : Γ → ℂ) x = 1` using `Set.indicator_of_mem hx _`. Rewrite using `[h2]`. Establish `h3 : ∀ j, (KH j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j x) = 1` using `fun j => Set.indicator_of_mem ((hK x).1 hx j) _`. Simplify using `only [h3, finprod_one]`.

Establish `h2 : (K : Set Γ).indicator (1 : Γ → ℂ) x = 0` using `Set.indicator_of_notMem hx _`. Rewrite using `[h2]`. Establish `h3 : ∃ j, p j x ∉ KH j`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Conclude with `hx ((hK x).2 hc)`. Take `⟨j, hj⟩` from `h3`. Use `finprod_eq_zero _ j (Set.indicator_of_notMem hj _) ?_` and prove the remaining obligations. Use `(Filter.eventually_cofinite.1 (hev x)).subset fun i hi hin => hi ?_` and prove the remaining obligations. Conclude with `Set.indicator_of_mem hin _`.

Simplify using `only [hF2, mul_one] at hsum2`. Establish `h2` using `GlobalTheory.CompanionTheory.HintLevel.hint_eq_level Γ K L ((K : Set Γ).indicator (1 : Γ → ℂ)) hLK (by rw [GlobalTheory.CompanionTheory.FamClP.rStab_ind]; exact hLK) hidx`. Rewrite `h2` using `[GlobalTheory.CompanionTheory.FamClP.hint_ind, hsum2]`. Establish `hC : ((L.relIndex K : ℕ) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hidx`. Establish `hCeq : (T.map fun i => (((V i).relIndex (KH i) : ℕ) : ℂ)).prod = ((L.relIndex K : ℕ) : ℂ)`.

Establish `h3 : ((L.relIndex K : ℕ) : ℂ) * (((L.relIndex K : ℕ) : ℂ)⁻¹ * (T.map fun i => (((V i).relIndex (KH i) : ℕ) : ℂ)).prod) = ((L.relIndex K : ℕ) : ℂ) * 1`. Rewrite using `[← h2]`. Rewrite `h3` using `[← mul_assoc, mul_inv_cancel₀ hC, one_mul, mul_one]`. Then use the resulting hypothesis. Rewrite using `[h1, hsum, hCeq, ← mul_assoc, inv_mul_cancel₀ hC, one_mul, hfold]`.
-/
theorem hint_prod_eq_foldr : ∀ {ι Γ : Type} [Group Γ] {Hl : ι → Type} [∀ i, Group (Hl i)] (p : ∀ i, Γ →* Hl i) (e : ∀ i, Hl i →* Γ) (K : Subgroup Γ) (KH V : ∀ i, Subgroup (Hl i))
    (f : ∀ i, Hl i → ℂ)
    (hpe : ∀ i m, p i (e i m) = m) (hpe' : ∀ i j m, i ≠ j → p j (e i m) = 1)
    (hsep : ∀ x y : Γ, (∀ i, p i x = p i y) → x = y)
    (hev : ∀ x, ∀ᶠ i in cofinite, p i x ∈ KH i)
    (hK : ∀ x, x ∈ K ↔ ∀ i, p i x ∈ KH i)
    (hVK : ∀ i, V i ≤ KH i) (hVi : ∀ i, (V i).relIndex (KH i) ≠ 0)
    (hVe : ∀ᶠ i in cofinite, V i = KH i ∧ f i = (KH i : Set (Hl i)).indicator 1)
    (hfV : ∀ i, ∀ u ∈ V i, ∀ x, f i (x * u) = f i x)
    (hfs : ∀ i, {q : Hl i ⧸ V i | f i q.out ≠ 0}.Finite)
    (g : Γ → ℂ) (hg : ∀ u, (∀ i, p i u ∈ V i) → ∀ x, g (x * u) = g x)
    (l : List ι) (hl : l.Nodup)
    (hfix : ∀ i, i ∉ l → (fun x => hint (KH i) fun m => f i m * g (x * e i m)) = g),
    hint K (fun x => (∏ᶠ i, f i (p i x)) * g x) =
      l.foldr (fun i g' x => hint (KH i) fun m => f i m * g' (x * e i m)) g 1 := by
  intro ι Γ _ Hl _ p e K KH V f hpe hpe' hsep hev hK hVK hVi hVe hfV hfs g hg l hl hfix
  have hmemL : ∀ u, u ∈ (⨅ i, (V i).comap (p i)) ↔ ∀ i, p i u ∈ V i := by
    intro u
    simp [Subgroup.mem_iInf]
  generalize hLdef : (⨅ i, (V i).comap (p i)) = L at hmemL
  have hLK : L ≤ K := fun u hu => (hK u).2 fun i => hVK i ((hmemL u).1 hu i)
  have hfinKH : ∀ i, {q : Hl i ⧸ V i | q.out ∈ KH i}.Finite :=
    fun i => out_finite_of_relIndex (V i) (KH i) (hVi i)
  have hVe1 : ∀ᶠ i in cofinite, V i = KH i := hVe.mono fun i h => h.1
  have hidx : L.relIndex K ≠ 0 := by
    refine relIndex_ne_of_out L K hLK ?_
    have h0 := GlobalTheory.T.finite_restricted_product_quotient p V (fun i => (KH i : Set (Hl i)))
      (fun i x hx u hu => mul_mem hx (hVK i hu)) hfinKH
      (hVe1.mono fun i h x hx => by
        rw [SetLike.mem_coe, h]
        exact hx)
    rw [hLdef] at h0
    exact h0.subset fun q hq => (hK _).1 hq
  have hB := Filter.eventually_cofinite.1 hVe
  obtain ⟨extra, hextra, hend, hcov⟩ : ∃ extra : List ι, (∀ i ∈ extra, i ∉ l) ∧ extra.Nodup ∧
      ∀ j, j ∉ l ++ extra → V j = KH j ∧ f j = (KH j : Set (Hl j)).indicator 1 := by
    refine ⟨(hB.toFinset.filter (· ∉ l)).toList, ?_, Finset.nodup_toList _, ?_⟩
    · intro i hi
      rw [Finset.mem_toList, Finset.mem_filter] at hi
      exact hi.2
    · intro j hj
      by_contra hc
      apply hj
      rw [List.mem_append]
      by_cases hjl : j ∈ l
      · exact Or.inl hjl
      · refine Or.inr ?_
        rw [Finset.mem_toList, Finset.mem_filter]
        exact ⟨hB.mem_toFinset.2 hc, hjl⟩
  have hnd : (l ++ extra).Nodup :=
    List.Nodup.append hl hend fun a ha hb => hextra a hb ha
  generalize hT : l ++ extra = T at hnd hcov
  have hfoldE : ∀ m : List ι, (∀ i ∈ m, i ∉ l) →
      m.foldr (fun i g' x => hint (KH i) fun m => f i m * g' (x * e i m)) g = g := by
    intro m
    induction m with
    | nil => intro _; rfl
    | cons a t ih =>
      intro hm
      rw [List.foldr_cons, ih fun i hi => hm i (List.mem_cons_of_mem _ hi)]
      exact hfix a (hm a List.mem_cons_self)
  have hfold : T.foldr (fun i g' x => hint (KH i) fun m => f i m * g' (x * e i m)) g =
      l.foldr (fun i g' x => hint (KH i) fun m => f i m * g' (x * e i m)) g := by
    rw [← hT, List.foldr_append, hfoldE extra hextra]
  have hsum := GlobalTheory.T.restricted_product_hecke_sum p e KH V f hpe hpe' hsep hev hVK hVi hVe1 hfV hfs T hnd g hg 1
  rw [hLdef] at hsum
  simp only [one_mul] at hsum
  have hF : ∀ x, (∏ᶠ j, if j ∈ T then f j (p j x)
      else (V j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j x)) = ∏ᶠ i, f i (p i x) := by
    intro x
    refine finprod_congr fun j => ?_
    split_ifs with hj
    · rfl
    · obtain ⟨h1, h2⟩ := hcov j hj
      rw [h2, h1]
  simp only [hF] at hsum
  have hlev : L ≤ rStab (fun x => (∏ᶠ i, f i (p i x)) * g x) := by
    intro r hr
    refine GlobalTheory.CompanionTheory.FamClP.mem_rStab'.2 fun x => ?_
    have h1 : (∏ᶠ i, f i (p i (x * r))) = ∏ᶠ i, f i (p i x) := by
      refine finprod_congr fun i => ?_
      rw [map_mul]
      exact hfV i _ ((hmemL r).1 hr i) _
    show (∏ᶠ i, f i (p i (x * r))) * g (x * r) = (∏ᶠ i, f i (p i x)) * g x
    rw [h1, hg r ((hmemL r).1 hr) x]
  have h1 := GlobalTheory.CompanionTheory.HintLevel.hint_eq_level Γ K L (fun x => (∏ᶠ i, f i (p i x)) * g x) hLK hlev hidx

  have hfVI : ∀ i, ∀ u ∈ V i, ∀ x, (KH i : Set (Hl i)).indicator (1 : Hl i → ℂ) (x * u) =
      (KH i : Set (Hl i)).indicator (1 : Hl i → ℂ) x := by
    intro i u hu x
    have h0 : u ∈ rStab ((KH i : Set (Hl i)).indicator (1 : Hl i → ℂ)) := by
      rw [GlobalTheory.CompanionTheory.FamClP.rStab_ind]
      exact hVK i hu
    exact GlobalTheory.CompanionTheory.FamClP.mem_rStab'.1 h0 x
  have hfsI : ∀ i, {q : Hl i ⧸ V i | (KH i : Set (Hl i)).indicator (1 : Hl i → ℂ) q.out ≠ 0}.Finite := by
    intro i
    refine (hfinKH i).subset fun q hq => ?_
    by_contra hn
    exact hq (Set.indicator_of_notMem (s := (KH i : Set (Hl i))) (show q.out ∉ (KH i : Set (Hl i)) from hn) _)
  have hsum2 := GlobalTheory.T.restricted_product_hecke_sum p e KH V (fun i => (KH i : Set (Hl i)).indicator (1 : Hl i → ℂ))
    hpe hpe' hsep hev hVK hVi hVe1 hfVI hfsI T hnd (fun _ => 1) (fun _ _ _ => rfl) 1
  rw [hLdef] at hsum2
  have hfold2 : ∀ m : List ι, m.foldr (fun i g' x => hint (KH i) fun m =>
      (KH i : Set (Hl i)).indicator (1 : Hl i → ℂ) m * g' (x * e i m)) (fun _ => (1 : ℂ)) =
      fun _ => 1 := by
    intro m
    induction m with
    | nil => rfl
    | cons a t ih =>
      rw [List.foldr_cons, ih]
      funext x
      simp only [mul_one]
      exact GlobalTheory.CompanionTheory.FamClP.hint_ind _
  rw [hfold2 T] at hsum2
  have hF2 : ∀ x, (∏ᶠ j, if j ∈ T then (KH j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j x)
      else (V j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j x)) =
      (K : Set Γ).indicator (1 : Γ → ℂ) x := by
    intro x
    have h0 : (∏ᶠ j, if j ∈ T then (KH j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j x)
        else (V j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j x)) =
        ∏ᶠ j, (KH j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j x) := by
      refine finprod_congr fun j => ?_
      split_ifs with hj
      · rfl
      · rw [(hcov j hj).1]
    rw [h0]
    by_cases hx : x ∈ K
    · have h2 : (K : Set Γ).indicator (1 : Γ → ℂ) x = 1 := Set.indicator_of_mem hx _
      rw [h2]
      have h3 : ∀ j, (KH j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j x) = 1 :=
        fun j => Set.indicator_of_mem ((hK x).1 hx j) _
      simp only [h3, finprod_one]
    · have h2 : (K : Set Γ).indicator (1 : Γ → ℂ) x = 0 := Set.indicator_of_notMem hx _
      rw [h2]
      have h3 : ∃ j, p j x ∉ KH j := by
        by_contra hc
        push_neg at hc
        exact hx ((hK x).2 hc)
      obtain ⟨j, hj⟩ := h3
      refine finprod_eq_zero _ j (Set.indicator_of_notMem hj _) ?_
      refine (Filter.eventually_cofinite.1 (hev x)).subset fun i hi hin => hi ?_
      exact Set.indicator_of_mem hin _
  simp only [hF2, mul_one] at hsum2
  have h2 := GlobalTheory.CompanionTheory.HintLevel.hint_eq_level Γ K L ((K : Set Γ).indicator (1 : Γ → ℂ)) hLK
    (by rw [GlobalTheory.CompanionTheory.FamClP.rStab_ind]; exact hLK) hidx
  rw [GlobalTheory.CompanionTheory.FamClP.hint_ind, hsum2] at h2
  have hC : ((L.relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hidx
  have hCeq : (T.map fun i => (((V i).relIndex (KH i) : ℕ) : ℂ)).prod = ((L.relIndex K : ℕ) : ℂ) := by
    have h3 : ((L.relIndex K : ℕ) : ℂ) * (((L.relIndex K : ℕ) : ℂ)⁻¹ *
        (T.map fun i => (((V i).relIndex (KH i) : ℕ) : ℂ)).prod) = ((L.relIndex K : ℕ) : ℂ) * 1 := by
      rw [← h2]
    rwa [← mul_assoc, mul_inv_cancel₀ hC, one_mul, mul_one] at h3
  rw [h1, hsum, hCeq, ← mul_assoc, inv_mul_cancel₀ hC, one_mul, hfold]

end GlobalTheory.CompanionTheory.FinActCore

end
