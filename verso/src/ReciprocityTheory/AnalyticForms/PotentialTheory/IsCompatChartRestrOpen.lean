import ReciprocityTheory.AnalyticForms.PotentialTheory.MIntSumCont
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential

namespace ReciprocityTheory.AnForm.M.PLAux

open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]

omit [T2Space X] [CompactSpace X] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem restrOpen_source' (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) {V : Set X} (hV : IsOpen V) :
    (ψ.restrOpen V hV).source = ψ.source ∩ V := by
  rfl

omit [T2Space X] [CompactSpace X] in
/- English proof (translation)
Introduce `j`. Take `⟨h1, h2⟩` from `hψ j`. Use `⟨h1.mono ?_, h2.mono ?_⟩` and prove the remaining obligations. Introduce and unpack `y ⟨hy1, hy2⟩`. Establish `h' : (A.chart j).symm y ∈ ψ.source ∩ V` using `hy2`.

Conclude with `⟨hy1, h'.1⟩`. Introduce and unpack `y ⟨hy1, hy2⟩`. Establish `h' : y ∈ ψ.target ∩ ψ.symm ⁻¹' V` using `hy1`. Conclude with `⟨h'.1, hy2⟩`.
-/
theorem isCompatChart_restrOpen {A : FinHolAtlas e X} {ψ : OpenPartialHomeomorph X (Fin e → ℂ)}
    (hψ : IsCompatChart A ψ) {V : Set X} (hV : IsOpen V) : IsCompatChart A (ψ.restrOpen V hV) := by
  intro j
  obtain ⟨h1, h2⟩ := hψ j
  refine ⟨h1.mono ?_, h2.mono ?_⟩
  · rintro y ⟨hy1, hy2⟩
    have h' : (A.chart j).symm y ∈ ψ.source ∩ V := hy2
    exact ⟨hy1, h'.1⟩
  · rintro y ⟨hy1, hy2⟩
    have h' : y ∈ ψ.target ∩ ψ.symm ⁻¹' V := hy1
    exact ⟨h'.1, hy2⟩

/- English proof (translation)
Take `⟨ψ, hψ, hx, hψL, σ, -, hWψ, u, hu, hu0, hsu⟩` from `hSNC x`. Establish `hsu' : ∀ y ∈ ψ.source, s x y = u y * ∏ k, (σ k).elim 1 (fun i => ψ y i ^ m k)`. Introduce `y hy`. Rewrite using `[hsu y hy]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases σ k with _ | i <;> rfl`. Take `⟨V, hVdef⟩ : ∃ V : Set X, V = ψ.source ∩ (⋂ k, (Φ k).U x) ∩ ⋂ k, (if x ∈ W k then Set.univ else (W k)ᶜ)` from `⟨_, rfl⟩`. Establish `hVo : IsOpen V`. Rewrite using `[hVdef]`.

Use `(ψ.open_source.inter (isOpen_iInter_of_finite fun k => (Φ k).isOpen_U x)).inter (isOpen_iInter_of_finite fun k => ?_)` and prove the remaining obligations. Use `split_ifs`. Conclude with `isOpen_univ`. Conclude with `(sncClosed A L s m W hSNC k).isOpen_compl`. Establish `hxV : x ∈ V`.

Rewrite using `[hVdef]`. Use `⟨⟨hx, Set.mem_iInter.2 fun k => (Φ k).mem_U x⟩, Set.mem_iInter.2 fun k => ?_⟩` and prove the remaining obligations. Use `split_ifs with h`. Conclude with `Set.mem_univ _`. Conclude with `h`.

Use `⟨ψ.restrOpen V hVo, isCompatChart_restrOpen hψ hVo, ?_, fun v hv hvV => ?_⟩` and prove the remaining obligations. Rewrite using `[restrOpen_source']`. Conclude with `⟨hx, hxV⟩`. Establish `hvV' : tsupport v ⊆ V` using `hvV.trans (by rw [restrOpen_source']; exact Set.inter_subset_right)`. Use `pl_good A L s m W B hL hs hSNC hB Φ hΦ x ψ hψ hψL σ hWψ u hu hu0 hsu' hVo (fun p hp => by rw [hVdef] at hp; exact hp.1.1) (fun k p hp => by rw [hVdef] at hp; exact Set.mem_iInter.1 hp.1.2 k) (fun k hk => ?_) hv hvV'` and prove the remaining obligations.

Use extensionality with `p`. Simplify using `only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]`. Introduce `hp hpW`. Rewrite `hp` using `[hVdef]`. Use `Set.mem_iInter.1 hp.2 k` as an intermediate fact.

Rewrite `this` using `[if_neg hk]`. Conclude with `this hpW`.
-/
theorem pl_exists_chart (A : FinHolAtlas (e + 1) X) (L : LocPot X) (s : X → X → ℂ) {r : ℕ}
    (m : Fin r → ℕ) (W : Fin r → Set X) (B : ∀ k, FinHolAtlas e (W k)) (hL : IsPotential A L)
    (hs : IsSection A L s) (hSNC : IsSNC A L s m W) (hB : ∀ k, HoloMap (B k) A Subtype.val)
    (Φ : Fin e → LocPot X) (hΦ : ∀ k, IsPotential A (Φ k)) (x : X) :
    ∃ ψ' : OpenPartialHomeomorph X (Fin (e + 1) → ℂ), IsCompatChart A ψ' ∧ x ∈ ψ'.source ∧
      ∀ v : X → ℝ, A.Smooth v → tsupport v ⊆ ψ'.source →
        mInt A (Fin.cons (LocPot.ofFun v) Φ) (logNormSec L s) =
          ∑ k, (m k : ℝ) * mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val)
            (v ∘ Subtype.val) - mInt A (Fin.cons L Φ) v := by
  classical
  obtain ⟨ψ, hψ, hx, hψL, σ, -, hWψ, u, hu, hu0, hsu⟩ := hSNC x
  have hsu' : ∀ y ∈ ψ.source, s x y = u y * ∏ k, (σ k).elim 1 (fun i => ψ y i ^ m k) := by
    intro y hy
    rw [hsu y hy]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rcases σ k with _ | i <;> rfl
  obtain ⟨V, hVdef⟩ : ∃ V : Set X, V = ψ.source ∩ (⋂ k, (Φ k).U x) ∩
      ⋂ k, (if x ∈ W k then Set.univ else (W k)ᶜ) := ⟨_, rfl⟩
  have hVo : IsOpen V := by
    rw [hVdef]
    refine (ψ.open_source.inter (isOpen_iInter_of_finite fun k => (Φ k).isOpen_U x)).inter
      (isOpen_iInter_of_finite fun k => ?_)
    split_ifs
    · exact isOpen_univ
    · exact (sncClosed A L s m W hSNC k).isOpen_compl
  have hxV : x ∈ V := by
    rw [hVdef]
    refine ⟨⟨hx, Set.mem_iInter.2 fun k => (Φ k).mem_U x⟩, Set.mem_iInter.2 fun k => ?_⟩
    split_ifs with h
    · exact Set.mem_univ _
    · exact h
  refine ⟨ψ.restrOpen V hVo, isCompatChart_restrOpen hψ hVo, ?_, fun v hv hvV => ?_⟩
  · rw [restrOpen_source']
    exact ⟨hx, hxV⟩
  · have hvV' : tsupport v ⊆ V := hvV.trans (by rw [restrOpen_source']; exact Set.inter_subset_right)
    refine pl_good A L s m W B hL hs hSNC hB Φ hΦ x ψ hψ hψL σ hWψ u hu hu0 hsu' hVo
      (fun p hp => by rw [hVdef] at hp; exact hp.1.1)
      (fun k p hp => by rw [hVdef] at hp; exact Set.mem_iInter.1 hp.1.2 k) (fun k hk => ?_) hv hvV'
    ext p
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hp hpW
    rw [hVdef] at hp
    have := Set.mem_iInter.1 hp.2 k
    rw [if_neg hk] at this
    exact this hpW

/- English proof (translation)
Introduce `e X _ _ _ A L s r m W B hL hs hSNC hB v hv Φ hΦ`. Use `choose ψ hψ hxψ hpl using fun x => pl_exists_chart A L s m W B hL hs hSNC hB Φ hΦ x`. Take `⟨t, ht⟩` from `isCompact_univ.elim_finite_subcover (fun x => (ψ x).source) (fun x => (ψ x).open_source) (fun x _ => Set.mem_iUnion.2 ⟨x, hxψ x⟩)`. Establish `hcov : ∀ y, ∃ i, y ∈ (ψ (t.equivFin.symm i : X)).source`. Introduce `y`.

Take `⟨x, hxt, hy⟩` from `Set.mem_iUnion₂.1 (ht (Set.mem_univ y))`. Conclude with `⟨t.equivFin ⟨x, hxt⟩, by simpa using hy⟩`. Take `⟨AC, hAC, -, hAC2⟩` from `atlasOfCompat A (fun i => ψ (t.equivFin.symm i : X)) (fun i => hψ _) hcov`. Take `⟨P⟩` from `existsPartition AC`. Take `⟨f, hf⟩ : ∃ f : Fin AC.n → X → ℝ, f = fun j p => P.χ j p * v p` from `⟨_, rfl⟩`.

Establish `hfs : ∀ j, A.Smooth (f j)`. Introduce `j`. Establish `h1 : A.Smooth (P.χ j)` using `smoothOn_of_compatible ⟨hAC.2, hAC.1⟩ isOpen_univ (P.smooth j)`. Rewrite using `[hf]`. Conclude with `smoothOn_mul h1 hv`.

Establish `hfpl : ∀ j, mInt A (Fin.cons (LocPot.ofFun (f j)) Φ) (logNormSec L s) = ∑ k, (m k : ℝ) * mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val) (f j ∘ Subtype.val) - mInt A (Fin.cons L Φ) (f j)`. Introduce `j`. Take `⟨i, hi⟩` from `hAC2 j`. Use `hpl (t.equivFin.symm i : X) (f j) (hfs j) ?_` and prove the remaining obligations. Establish `h2` using `P.tsupport_subset j`.

Rewrite `h2` using `[hi]`. Rewrite using `[hf]`. Conclude with `tsupport_mul_subset_left.trans h2`. Establish `hvsum : v = fun p => ∑ j ∈ Finset.univ, f j p`. Use function extensionality and compare the values at `p`.

Rewrite using `[hf]`. Simplify using `only [← Finset.sum_mul, P.sum_eq_one, one_mul]`. Establish `hpot : ∀ i, IsPotential A ((Fin.cons L Φ : Fin (e + 1) → LocPot X) i)`. Introduce `i`. Use `Fin.cases ?_ (fun k => ?_) i` and prove the remaining obligations.

Conclude with `hL`. Conclude with `hΦ k`. Establish `: ∀ k, CompactSpace (W k)` using `fun k => isCompact_iff_compactSpace.1 (sncClosed A L s m W hSNC k).isCompact`. Establish `hΦB : ∀ k i, IsPotential (B k) ((Φ i).pullback Subtype.val continuous_subtype_val)` using `fun k i => isPotentialPullback A (B k) Subtype.val (hB k) (Φ i) (hΦ i)`. Establish `hc : ∀ j, Continuous (f j)` using `fun j => smooth_continuous (hfs j)`.

Establish `hk : ∀ k, mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val) ((fun p => ∑ j ∈ Finset.univ, f j p) ∘ Subtype.val) = ∑ j, mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val) (f j ∘ Subtype.val)` using `fun k => mInt_sum_cont (B k) _ (hΦB k) Finset.univ (fun j => f j ∘ Subtype.val) (fun j => (hc j).comp continuous_subtype_val)`. Rewrite using `[hvsum, lhs_sum A L s (fun Φ' hΦ' => logNormIntegrable A L s m W hL hs hSNC Φ' hΦ') Φ hΦ Finset.univ f hfs, mInt_sum_cont A (Fin.cons L Φ) hpot Finset.univ f hc, Finset.sum_congr rfl fun j _ => hfpl j, Finset.sum_sub_distrib]`. Use `congr 1`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[hk k, Finset.mul_sum]`.
-/
theorem pl_global : PoincareLelongStatement := by
  intro e X _ _ _ A L s r m W B hL hs hSNC hB v hv Φ hΦ
  classical
  choose ψ hψ hxψ hpl using fun x => pl_exists_chart A L s m W B hL hs hSNC hB Φ hΦ x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (ψ x).source)
    (fun x => (ψ x).open_source) (fun x _ => Set.mem_iUnion.2 ⟨x, hxψ x⟩)
  have hcov : ∀ y, ∃ i, y ∈ (ψ (t.equivFin.symm i : X)).source := by
    intro y
    obtain ⟨x, hxt, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact ⟨t.equivFin ⟨x, hxt⟩, by simpa using hy⟩
  obtain ⟨AC, hAC, -, hAC2⟩ :=
    atlasOfCompat A (fun i => ψ (t.equivFin.symm i : X)) (fun i => hψ _) hcov
  obtain ⟨P⟩ := existsPartition AC
  obtain ⟨f, hf⟩ : ∃ f : Fin AC.n → X → ℝ, f = fun j p => P.χ j p * v p := ⟨_, rfl⟩
  have hfs : ∀ j, A.Smooth (f j) := by
    intro j
    have h1 : A.Smooth (P.χ j) := smoothOn_of_compatible ⟨hAC.2, hAC.1⟩ isOpen_univ (P.smooth j)
    rw [hf]
    exact smoothOn_mul h1 hv
  have hfpl : ∀ j, mInt A (Fin.cons (LocPot.ofFun (f j)) Φ) (logNormSec L s) =
      ∑ k, (m k : ℝ) * mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val)
        (f j ∘ Subtype.val) - mInt A (Fin.cons L Φ) (f j) := by
    intro j
    obtain ⟨i, hi⟩ := hAC2 j
    refine hpl (t.equivFin.symm i : X) (f j) (hfs j) ?_
    have h2 := P.tsupport_subset j
    rw [hi] at h2
    rw [hf]
    exact tsupport_mul_subset_left.trans h2
  have hvsum : v = fun p => ∑ j ∈ Finset.univ, f j p := by
    funext p
    rw [hf]
    simp only [← Finset.sum_mul, P.sum_eq_one, one_mul]
  have hpot : ∀ i, IsPotential A ((Fin.cons L Φ : Fin (e + 1) → LocPot X) i) := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · exact hL
    · exact hΦ k
  have : ∀ k, CompactSpace (W k) := fun k =>
    isCompact_iff_compactSpace.1 (sncClosed A L s m W hSNC k).isCompact
  have hΦB : ∀ k i, IsPotential (B k) ((Φ i).pullback Subtype.val continuous_subtype_val) :=
    fun k i => isPotentialPullback A (B k) Subtype.val (hB k) (Φ i) (hΦ i)
  have hc : ∀ j, Continuous (f j) := fun j => smooth_continuous (hfs j)
  have hk : ∀ k, mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val)
      ((fun p => ∑ j ∈ Finset.univ, f j p) ∘ Subtype.val) =
      ∑ j, mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val)
        (f j ∘ Subtype.val) := fun k =>
    mInt_sum_cont (B k) _ (hΦB k) Finset.univ (fun j => f j ∘ Subtype.val)
      (fun j => (hc j).comp continuous_subtype_val)
  rw [hvsum, lhs_sum A L s (fun Φ' hΦ' => logNormIntegrable A L s m W hL hs hSNC Φ' hΦ') Φ hΦ
    Finset.univ f hfs, mInt_sum_cont A (Fin.cons L Φ) hpot Finset.univ f hc,
    Finset.sum_congr rfl fun j _ => hfpl j, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hk k, Finset.mul_sum]

end

end ReciprocityTheory.AnForm.M.PLAux
