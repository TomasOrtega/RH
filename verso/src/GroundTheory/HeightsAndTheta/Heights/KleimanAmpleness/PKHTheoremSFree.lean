import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHFreeEmbedSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHFreeDecompSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHFreeIndepSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHCombContractSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHCombCyclicSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHFreeBadFiniteSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.CechHcSubsingletonOfBij
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

set_option linter.unusedSectionVars false

namespace KHTheoremSFree

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

def Bad (a : (Σ k, ι k) → ℤ) : Prop :=
  ∀ k, negSet a k = ∅ ∨ negSet a k = Finset.univ

omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in
/- English proof (translation)
Simplify using `[embed, h]`. Both sides reduce to the same expression.
-/
theorem embed_apply (a : (Σ k, ι k) → ℤ) (n : ℕ) (f : CombC S (negSet a) n) (I : KH.Cell K ι n)
    (h : ∀ k, negSet a k ⊆ I.1 k) : embed S a n f I = f ⟨I, h⟩ • monoFrac S I.1 a := by
  simp [embed, h]
  rfl

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero`. Establish `hb0 : b = 0` using `(Submodule.mem_bot S).mp hb`. Substitute `hb0` using the available equality. Rewrite using `[map_zero]`.

Conclude with `Submodule.zero_mem _`. Consider the case `succ m`. Take `⟨g, rfl⟩` from `LinearMap.mem_range.mp hb`. Conclude with `⟨embed S a m g, (hE S K ι a).2.1 c d ha m g, (hE S K ι a).1 m g⟩`.
-/
theorem embed_mem_cechBc (hE : KHFreeEmbed.Statement) {a : (Σ k, ι k) → ℤ} {c d : K → ℤ}
    (ha : blockSum a = c + d) {n : ℕ} {b : CombC S (negSet a) n} (hb : b ∈ combB S (negSet a) n) :
    embed S a n b ∈ KH.cechBc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n := by
  cases n with
  | zero =>
    have hb0 : b = 0 := (Submodule.mem_bot S).mp hb
    subst hb0
    rw [map_zero]
    exact Submodule.zero_mem _
  | succ m =>
    obtain ⟨g, rfl⟩ := LinearMap.mem_range.mp hb
    exact ⟨embed S a m g, (hE S K ι a).2.1 c d ha m g, (hE S K ι a).1 m g⟩

/- English proof (translation)
Take `⟨A, f, hA, rfl⟩` from `hD S K ι c d n z hz.1`. Use `⟨A, f, hA, rfl, hI S K ι (n + 1) A (fun a => combD S (negSet a) n (f a)) ?_⟩` and prove the remaining obligations. Establish `h0 : KH.cechD S ι _ n (∑ a ∈ A, embed S a n (f a)) = 0` using `hz.2`. Rewrite `h0` using `[map_sum]`. Simplify `h0` using `only [(hE S K ι _).1]`.
-/
theorem cocycle_decomp (hE : KHFreeEmbed.Statement) (hD : KHFreeDecomp.Statement) (hI : KHFreeIndep.Statement)
    {c d : K → ℤ} {n : ℕ} {z : KH.CechC S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n}
    (hz : z ∈ KH.cechZc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n) :
    ∃ (A : Finset ((Σ k, ι k) → ℤ)) (f : ∀ a : (Σ k, ι k) → ℤ, CombC S (negSet a) n),
      (∀ a ∈ A, blockSum a = c + d) ∧ z = ∑ a ∈ A, embed S a n (f a) ∧
        ∀ a ∈ A, combD S (negSet a) n (f a) = 0 := by
  obtain ⟨A, f, hA, rfl⟩ := hD S K ι c d n z hz.1
  refine ⟨A, f, hA, rfl, hI S K ι (n + 1) A (fun a => combD S (negSet a) n (f a)) ?_⟩
  have h0 : KH.cechD S ι _ n (∑ a ∈ A, embed S a n (f a)) = 0 := hz.2
  rw [map_sum] at h0
  simpa only [(hE S K ι _).1] using h0

/- English proof (translation)
Distinguish the cases in `hb : Bad a`. Take `⟨s, hs⟩` from `(hY S K ι (negSet a) n hb).2 g hg`. Conclude with `⟨s, hs, fun _ => hb⟩`. Simplify using `only [Bad, not_forall, not_or] at hb`. Take `⟨k, hk0, hku⟩` from `hb`.

Choose the witnesses or unpack the hypotheses as in `⟨i₀, hi₀⟩ : ∃ i₀, i₀ ∉ negSet a k := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hku (Finset.eq_univ_of_forall h)`. Take `⟨g', hg', hg'I⟩` from `hC S K ι (negSet a) n k i₀ hi₀ g hg`.

Establish `h0 : g' = 0` using `funext fun I => (hg'I I).2 fun h => hk0 h.1`. Use `⟨0, ?_, fun h => absurd rfl h⟩` and prove the remaining obligations. Rewrite using `[zero_smul, sub_zero]`. Rewrite `hg'` using `[h0, sub_zero]`. Then use the resulting hypothesis.
-/
theorem part_cyclic (hC : KHCombContract.Statement) (hY : KHCombCyclic.Statement) (a : (Σ k, ι k) → ℤ) {n : ℕ}
    {g : CombC S (negSet a) n} (hg : combD S (negSet a) n g = 0) :
    ∃ s : S, g - s • singOne S (negSet a) n ∈ combB S (negSet a) n ∧ (s ≠ 0 → Bad a) := by
  by_cases hb : Bad a
  · obtain ⟨s, hs⟩ := (hY S K ι (negSet a) n hb).2 g hg
    exact ⟨s, hs, fun _ => hb⟩
  · simp only [Bad, not_forall, not_or] at hb
    obtain ⟨k, hk0, hku⟩ := hb
    obtain ⟨i₀, hi₀⟩ : ∃ i₀, i₀ ∉ negSet a k := by
      by_contra h
      push Not at h
      exact hku (Finset.eq_univ_of_forall h)
    obtain ⟨g', hg', hg'I⟩ := hC S K ι (negSet a) n k i₀ hi₀ g hg
    have h0 : g' = 0 := funext fun I => (hg'I I).2 fun h => hk0 h.1
    refine ⟨0, ?_, fun h => absurd rfl h⟩
    rw [zero_smul, sub_zero]
    rwa [h0, sub_zero] at hg'

omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in

/- English proof (translation)
Break down `hb k with h | h` into its components or cases. Conclude with `h`. Use `Finset.eq_empty_of_forall_notMem fun i _ => ?_` and prove the remaining obligations. Establish `hall : ∀ j, a ⟨k, j⟩ < 0` using `fun j => by`. Establish `hj : j ∈ negSet a k` using `h ▸ Finset.mem_univ j`.

Simplify `hj` using `[negSet]`. Establish `hneg : ∑ j, a ⟨k, j⟩ < 0` using `Finset.sum_neg (fun j _ => hall j) ⟨i, Finset.mem_univ _⟩`. Establish `hk : ∑ j, a ⟨k, j⟩ = e k` using `congrFun ha k`. Combine the linear relations using `[he k]`.
-/
theorem negSet_empty {a : (Σ k, ι k) → ℤ} {e : K → ℤ} (ha : blockSum a = e) (he : ∀ k, 0 ≤ e k) (hb : Bad a)
    (k : K) : negSet a k = ∅ := by
  rcases hb k with h | h
  · exact h
  refine Finset.eq_empty_of_forall_notMem fun i _ => ?_
  have hall : ∀ j, a ⟨k, j⟩ < 0 := fun j => by
    have hj : j ∈ negSet a k := h ▸ Finset.mem_univ j
    simpa [negSet] using hj
  have hneg : ∑ j, a ⟨k, j⟩ < 0 := Finset.sum_neg (fun j _ => hall j) ⟨i, Finset.mem_univ _⟩
  have hk : ∑ j, a ⟨k, j⟩ = e k := congrFun ha k
  linarith [he k]

omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in
/- English proof (translation)
Assume the negation of the conclusion as `hp`. Establish `hm : p.2 ∈ negSet a p.1` using `by simp [negSet]; omega`. Rewrite `hm` using `[h p.1]`. Conclude with `Finset.notMem_empty _ hm`.
-/
theorem nonneg_of_negSet_empty {a : (Σ k, ι k) → ℤ} (h : ∀ k, negSet a k = ∅) (p : Σ k, ι k) : 0 ≤ a p := by
  by_contra hp
  have hm : p.2 ∈ negSet a p.1 := by simp [negSet]; omega
  rw [h p.1] at hm
  exact Finset.notMem_empty _ hm

omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in

/- English proof (translation)
Use function extensionality and compare the values at `I`. Simplify using `only [singOne, Pi.zero_apply]`. Rewrite using `[if_neg]`. Introduce `h`. Establish `h1 : ∀ k, (I.1.1 k).card - 1 = 0` using `fun k => by rw [h k (hJ k)]`.

Establish `hs` using `I.1.2.2`. Simplify using `only [h1, Finset.sum_const_zero] at hs`. Use linear arithmetic over natural numbers and integers.
-/
theorem singOne_eq_zero {J : ∀ k, Finset (ι k)} (hJ : ∀ k, J k = ∅) {n : ℕ} (hn : 1 ≤ n) :
    singOne S J n = 0 := by
  funext I
  simp only [singOne, Pi.zero_apply]
  rw [if_neg]
  intro h
  have h1 : ∀ k, (I.1.1 k).card - 1 = 0 := fun k => by rw [h k (hJ k)]
  have hs := I.1.2.2
  simp only [h1, Finset.sum_const_zero] at hs
  omega

omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in

/- English proof (translation)
Simplify using `only [singOne]`. Rewrite using `[if_pos]`. Introduce `k _`. Establish `hs` using `I.1.2.2`. Establish `hk` using `(Finset.sum_eq_zero_iff.mp hs) k (Finset.mem_univ k)`.

Establish `hpos` using `Finset.card_pos.mpr (I.1.2.1 k)`. Use linear arithmetic over natural numbers and integers.
-/
theorem singOne_zero {J : ∀ k, Finset (ι k)} (I : CombCell ι J 0) : singOne S J 0 I = 1 := by
  simp only [singOne]
  rw [if_pos]
  intro k _
  have hs := I.1.2.2
  have hk := (Finset.sum_eq_zero_iff.mp hs) k (Finset.mem_univ k)
  have hpos := Finset.card_pos.mpr (I.1.2.1 k)
  omega

/- English proof (translation)
Use `set Z := KH.cechZc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n`. Use `set Bf := (hF K ι (c + d)).toFinset`. Establish `hBf : ∀ a ∈ Bf, blockSum a = c + d ∧ Bad a` using `fun a ha => (hF K ι (c + d)).mem_toFinset.mp ha`. Set `gen : ((Σ k, ι k) → ℤ) → KH.CechC S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n` to `fun a => embed S a n (singOne S (negSet a) n)`. Establish `hgen : ∀ a ∈ Bf, gen a ∈ Z` using `fun a ha => ⟨(hE S K ι a).2.1 c d (hBf a ha).1 n _, by`.

Express the relevant statement in the definitionally equal form `KH.cechD S ι _ n (embed S a n _) = 0`. Rewrite using `[(hE S K ι a).1, (hY S K ι (negSet a) n (hBf a ha).2).1, map_zero]⟩`. Set `Ψ : (Bf → S) →ₗ[S] Z` to `LinearMap.codRestrict Z (∑ x : Bf, (LinearMap.proj x : (Bf → S) →ₗ[S] S).smulRight (gen x.1)) (fun s => by`. Simplify using `only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]`. Conclude with `Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (hgen x.1 x.2))`.

Establish `hΨ : ∀ t, (Ψ t : KH.CechC S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n) = ∑ x : Bf, t x • gen x.1` using `fun t => by`. Simplify using `only [Ψ, LinearMap.codRestrict_apply, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]`. Use `Module.Finite.of_surjective ((Submodule.mkQ _).comp Ψ) ?_` and prove the remaining obligations. Introduce `x`. Take `⟨⟨z, hz⟩, rfl⟩` from `Submodule.mkQ_surjective _ x`.

Take `⟨A, f, hA, rfl, hcoc⟩` from `cocycle_decomp hE hD hI hz`. Use `choose! s hs hsb using fun a (ha : a ∈ A) => part_cyclic hC hY a (hcoc a ha)`. Use `⟨fun x => if x.1 ∈ A then s x.1 else 0, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, eq_comm, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, hΨ]`. Establish `hsum : ∑ x : Bf, (if x.1 ∈ A then s x.1 else 0) • gen x.1 = ∑ a ∈ A, s a • gen a`.

Rewrite using `[Finset.sum_coe_sort Bf (fun a => (if a ∈ A then s a else 0) • gen a)]`. Simplify using `only [ite_smul, zero_smul]`. Rewrite using `[Finset.sum_ite_mem, Finset.inter_comm]`. Use `Finset.sum_subset Finset.inter_subset_left fun a ha hna => ?_` and prove the remaining obligations. Establish `hs0 : s a = 0`.

Assume the negation of the conclusion as `h0`. Conclude with `hna (Finset.mem_inter.mpr ⟨ha, (hF K ι (c + d)).mem_toFinset.mpr ⟨hA a ha, hsb a ha h0⟩⟩)`. Rewrite using `[hs0, zero_smul]`. Rewrite using `[hsum, ← Finset.sum_sub_distrib]`. Use `Submodule.sum_mem _ fun a ha => ?_` and prove the remaining obligations.

Establish `he : embed S a n (f a) - s a • gen a = embed S a n (f a - s a • singOne S (negSet a) n)`. Rewrite using `[map_sub, map_smul]`. Rewrite using `[he]`. Conclude with `embed_mem_cechBc hE (hA a ha) (hs a ha)`.
-/
theorem finite (hE : KHFreeEmbed.Statement) (hD : KHFreeDecomp.Statement) (hI : KHFreeIndep.Statement)
    (hC : KHCombContract.Statement) (hY : KHCombCyclic.Statement) (hF : KHFreeBadFinite.Statement)
    (d c : K → ℤ) (n : ℕ) :
    Module.Finite S (KH.cechHc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n) := by
  classical
  set Z := KH.cechZc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n
  set Bf := (hF K ι (c + d)).toFinset
  have hBf : ∀ a ∈ Bf, blockSum a = c + d ∧ Bad a := fun a ha => (hF K ι (c + d)).mem_toFinset.mp ha
  let gen : ((Σ k, ι k) → ℤ) → KH.CechC S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n :=
    fun a => embed S a n (singOne S (negSet a) n)
  have hgen : ∀ a ∈ Bf, gen a ∈ Z := fun a ha =>
    ⟨(hE S K ι a).2.1 c d (hBf a ha).1 n _, by
      change KH.cechD S ι _ n (embed S a n _) = 0
      rw [(hE S K ι a).1, (hY S K ι (negSet a) n (hBf a ha).2).1, map_zero]⟩

  let Ψ : (Bf → S) →ₗ[S] Z :=
    LinearMap.codRestrict Z (∑ x : Bf, (LinearMap.proj x : (Bf → S) →ₗ[S] S).smulRight (gen x.1))
      (fun s => by
        simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
        exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (hgen x.1 x.2))
  have hΨ : ∀ t, (Ψ t : KH.CechC S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n) =
      ∑ x : Bf, t x • gen x.1 := fun t => by
    simp only [Ψ, LinearMap.codRestrict_apply, LinearMap.sum_apply, LinearMap.smulRight_apply,
      LinearMap.proj_apply]
  refine Module.Finite.of_surjective ((Submodule.mkQ _).comp Ψ) ?_
  intro x
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.mkQ_surjective _ x
  obtain ⟨A, f, hA, rfl, hcoc⟩ := cocycle_decomp hE hD hI hz
  choose! s hs hsb using fun a (ha : a ∈ A) => part_cyclic hC hY a (hcoc a ha)
  refine ⟨fun x => if x.1 ∈ A then s x.1 else 0, ?_⟩
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, eq_comm, Submodule.Quotient.eq,
    Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, hΨ]
  have hsum : ∑ x : Bf, (if x.1 ∈ A then s x.1 else 0) • gen x.1 = ∑ a ∈ A, s a • gen a := by
    rw [Finset.sum_coe_sort Bf (fun a => (if a ∈ A then s a else 0) • gen a)]
    simp only [ite_smul, zero_smul]
    rw [Finset.sum_ite_mem, Finset.inter_comm]
    refine Finset.sum_subset Finset.inter_subset_left fun a ha hna => ?_
    have hs0 : s a = 0 := by
      by_contra h0
      exact hna (Finset.mem_inter.mpr ⟨ha, (hF K ι (c + d)).mem_toFinset.mpr ⟨hA a ha, hsb a ha h0⟩⟩)
    rw [hs0, zero_smul]
  rw [hsum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun a ha => ?_
  have he : embed S a n (f a) - s a • gen a = embed S a n (f a - s a • singOne S (negSet a) n) := by
    rw [map_sub, map_smul]
  rw [he]
  exact embed_mem_cechBc hE (hA a ha) (hs a ha)

/- English proof (translation)
Rewrite using `[GroundTheory.Heights₂.Heights.HilbertSamuel.H1VanishingDevissage.cechHc_subsingleton_iff]`. Introduce `z hz`. Take `⟨A, f, hA, rfl, hcoc⟩` from `cocycle_decomp hE hD hI hz`. Use `Submodule.sum_mem _ fun a ha => embed_mem_cechBc hE (hA a ha) ?_` and prove the remaining obligations. Take `⟨s, hs, hsb⟩` from `part_cyclic hC hY a (hcoc a ha)`.

Distinguish the cases in `h0 : s = 0`. Rewrite `hs` using `[h0, zero_smul, sub_zero]`. Then use the resulting hypothesis. Establish `hJ` using `negSet_empty (hA a ha) (fun k => by simpa using hcd k) (hsb h0)`. Rewrite `hs` using `[singOne_eq_zero hJ hn, smul_zero, sub_zero]`. Then use the resulting hypothesis.
-/
theorem vanish (hE : KHFreeEmbed.Statement) (hD : KHFreeDecomp.Statement) (hI : KHFreeIndep.Statement)
    (hC : KHCombContract.Statement) (hY : KHCombCyclic.Statement)
    (d c : K → ℤ) (n : ℕ) (hn : 1 ≤ n) (hcd : ∀ k, 0 ≤ c k + d k) :
    Subsingleton (KH.cechHc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n) := by
  rw [GroundTheory.Heights₂.Heights.HilbertSamuel.H1VanishingDevissage.cechHc_subsingleton_iff]
  intro z hz
  obtain ⟨A, f, hA, rfl, hcoc⟩ := cocycle_decomp hE hD hI hz
  refine Submodule.sum_mem _ fun a ha => embed_mem_cechBc hE (hA a ha) ?_
  obtain ⟨s, hs, hsb⟩ := part_cyclic hC hY a (hcoc a ha)
  by_cases h0 : s = 0
  · rwa [h0, zero_smul, sub_zero] at hs
  · have hJ := negSet_empty (hA a ha) (fun k => by simpa using hcd k) (hsb h0)
    rwa [singOne_eq_zero hJ hn, smul_zero, sub_zero] at hs

/- English proof (translation)
Take `⟨A, f, hA, rfl, hcoc⟩` from `cocycle_decomp hE hD hI hz`. Establish `hpart : ∀ a ∈ A, ∃ m ∈ KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d), ∀ I, embed S a 0 (f a) I = LocalizedModule.mk m 1`. Introduce `a ha`. Take `⟨s, hs, hsb⟩` from `part_cyclic hC hY a (hcoc a ha)`. Establish `hfa : f a = s • singOne S (negSet a) 0` using `sub_eq_zero.mp ((Submodule.mem_bot S).mp hs)`.

Distinguish the cases in `h0 : s = 0`. Use `⟨0, Submodule.zero_mem _, fun I => ?_⟩` and prove the remaining obligations. Rewrite using `[hfa, h0, zero_smul, map_zero, LocalizedModule.zero_mk]`. Both sides reduce to the same expression. Establish `hJ` using `negSet_empty (hA a ha) (fun k => by simpa using hcd k) (hsb h0)`.

Take `⟨m, hm, hmI⟩` from `(hE S K ι a).2.2 (nonneg_of_negSet_empty hJ)`. Rewrite `hm` using `[hA a ha]`. Use `⟨s • m, Submodule.smul_mem _ _ hm, fun I => ?_⟩` and prove the remaining obligations. Establish `hsub : ∀ k, negSet a k ⊆ I.1 k` using `fun k => by rw [hJ k]; exact Finset.empty_subset _`. Establish `hval : (s • singOne S (negSet a) 0) ⟨I, hsub⟩ = s`.

Express the relevant statement in the definitionally equal form `s * singOne S (negSet a) 0 ⟨I, hsub⟩ = s`. Conclude with `(congrArg (s * ·) (singOne_zero _)).trans (mul_one s)`. Rewrite using `[embed_apply a 0 (f a) I hsub, hfa, hval, hmI, LocalizedModule.smul'_mk]`. Use `choose! m hm hmI using hpart`. Use `⟨∑ a ∈ A, m a, Submodule.sum_mem _ hm, fun I => ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.sum_apply]`. Rewrite using `[← LocalizedModule.mkLinearMap_apply, map_sum]`. Conclude with `Finset.sum_congr rfl fun a ha => by rw [hmI a ha, LocalizedModule.mkLinearMap_apply]`.
-/
theorem sections (hE : KHFreeEmbed.Statement) (hD : KHFreeDecomp.Statement) (hI : KHFreeIndep.Statement)
    (hC : KHCombContract.Statement) (hY : KHCombCyclic.Statement)
    (d c : K → ℤ) (hcd : ∀ k, 0 ≤ c k + d k)
    (z : KH.CechC S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) 0)
    (hz : z ∈ KH.cechZc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c 0) :
    ∃ m ∈ KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d), ∀ I, z I = LocalizedModule.mk m 1 := by
  classical
  obtain ⟨A, f, hA, rfl, hcoc⟩ := cocycle_decomp hE hD hI hz
  have hpart : ∀ a ∈ A, ∃ m ∈ KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d),
      ∀ I, embed S a 0 (f a) I = LocalizedModule.mk m 1 := by
    intro a ha
    obtain ⟨s, hs, hsb⟩ := part_cyclic hC hY a (hcoc a ha)
    have hfa : f a = s • singOne S (negSet a) 0 := sub_eq_zero.mp ((Submodule.mem_bot S).mp hs)
    by_cases h0 : s = 0
    · refine ⟨0, Submodule.zero_mem _, fun I => ?_⟩
      rw [hfa, h0, zero_smul, map_zero, LocalizedModule.zero_mk]
      rfl
    · have hJ := negSet_empty (hA a ha) (fun k => by simpa using hcd k) (hsb h0)
      obtain ⟨m, hm, hmI⟩ := (hE S K ι a).2.2 (nonneg_of_negSet_empty hJ)
      rw [hA a ha] at hm
      refine ⟨s • m, Submodule.smul_mem _ _ hm, fun I => ?_⟩
      have hsub : ∀ k, negSet a k ⊆ I.1 k := fun k => by rw [hJ k]; exact Finset.empty_subset _
      have hval : (s • singOne S (negSet a) 0) ⟨I, hsub⟩ = s := by
        change s * singOne S (negSet a) 0 ⟨I, hsub⟩ = s
        exact (congrArg (s * ·) (singOne_zero _)).trans (mul_one s)
      rw [embed_apply a 0 (f a) I hsub, hfa, hval, hmI, LocalizedModule.smul'_mk]
  choose! m hm hmI using hpart
  refine ⟨∑ a ∈ A, m a, Submodule.sum_mem _ hm, fun I => ?_⟩
  rw [Finset.sum_apply]
  rw [← LocalizedModule.mkLinearMap_apply, map_sum]
  exact Finset.sum_congr rfl fun a ha => by rw [hmI a ha, LocalizedModule.mkLinearMap_apply]

end KHTheoremSFree

/- English proof (translation)
Introduce `S _ K _ _ ι _ _ d`. Conclude with `⟨fun c n => KHTheoremSFree.finite hE hD hI hC hY hF d c n, fun c n hn hcd => KHTheoremSFree.vanish hE hD hI hC hY d c n hn hcd, fun c hcd z hz => KHTheoremSFree.sections hE hD hI hC hY d c hcd z hz⟩`.
-/
theorem KHTheoremSFree.proof (hE : KHFreeEmbed.Statement) (hD : KHFreeDecomp.Statement) (hI : KHFreeIndep.Statement)
    (hC : KHCombContract.Statement) (hY : KHCombCyclic.Statement) (hF : KHFreeBadFinite.Statement) :
    KH.TheoremSFreeStatement := by
  intro S _ K _ _ ι _ _ d
  exact ⟨fun c n => KHTheoremSFree.finite hE hD hI hC hY hF d c n,
    fun c n hn hcd => KHTheoremSFree.vanish hE hD hI hC hY d c n hn hcd,
    fun c hcd z hz => KHTheoremSFree.sections hE hD hI hC hY d c hcd z hz⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
