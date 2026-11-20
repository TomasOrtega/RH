import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ConvRight

noncomputable section

namespace PositivityTheory.Rg.Sw.Glob

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => simpa using GlobalTheory.Cont.holValueAt_const 0 s₀`. Consider the case `insert a T ha ih`. Simplify using `only [Finset.sum_insert ha]`. Conclude with `(h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem holValueAt_finsum {ι : Type} (T : Finset ι) {f : ι → ℂ → ℂ} {c : ι → ℂ} {s₀ : ℂ}
    (h : ∀ i ∈ T, GlobalTheory.Cont.HolValueAt (f i) s₀ (c i)) :
    GlobalTheory.Cont.HolValueAt (fun s => ∑ i ∈ T, f i s) s₀ (∑ i ∈ T, c i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using GlobalTheory.Cont.holValueAt_const 0 s₀
  | insert a T ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Unfold `GlobalTheory.Eis.cosetSum GlobalTheory.Eis.term`. Conclude with `Summable.tsum_finsetSum fun i hi => (h i hi).of_norm`.
-/
theorem cosetSum_finsum {G : Type} [Group G] (Pp Γ : Subgroup G) {ι : Type} (T : Finset ι) (f : ι → G → ℂ) (g : G)
    (h : ∀ i ∈ T, GlobalTheory.Eis.CosetConv Pp Γ (f i) g) :
    GlobalTheory.Eis.cosetSum Pp Γ (fun x => ∑ i ∈ T, f i x) g = ∑ i ∈ T, GlobalTheory.Eis.cosetSum Pp Γ (f i) g := by
  unfold GlobalTheory.Eis.cosetSum GlobalTheory.Eis.term
  exact Summable.tsum_finsetSum fun i hi => (h i hi).of_norm

end PositivityTheory.Rg.Sw.Glob
