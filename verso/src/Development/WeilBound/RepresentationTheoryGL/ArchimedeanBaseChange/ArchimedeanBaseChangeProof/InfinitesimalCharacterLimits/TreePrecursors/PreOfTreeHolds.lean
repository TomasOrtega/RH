import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TreeParts
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ExistsHasInfCharGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponent
import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.PreOfTreePf

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
The claim follows from `| _, .leaf V z => by simp [Tr.leafList] | _, .node t₁ t₂ => by simp only [Tr.leafList, List.map_append, List.sum_append, leafList_sum t₁, leafList_sum t₂]`.
-/
theorem leafList_sum : ∀ {N : ℕ} (t : Tr E N), (t.leafList.map Sigma.fst).sum = N
  | _, .leaf V z => by simp [Tr.leafList]
  | _, .node t₁ t₂ => by
    simp only [Tr.leafList, List.map_append, List.sum_append, leafList_sum t₁, leafList_sum t₂]

/- English proof (translation)
The claim follows from `| _, .leaf V z, h, x, hx => by simp only [Tr.leafList, List.mem_singleton] at hx subst hx simp only [Tr.Good] at h rcases h with ⟨h0, -, -⟩ | ⟨-, hd, -⟩ · exact Or.inl h0 · exact Or.inr hd | _, .node t₁ t₂, h, x, hx => by simp only [Tr.Good] at h simp only [Tr.leafList, List.mem_ …`.
-/
theorem leafList_good : ∀ {N : ℕ} (t : Tr E N), t.Good → ∀ x ∈ t.leafList, x.1 = 0 ∨ IsDiscrete x.2
  | _, .leaf V z, h, x, hx => by
    simp only [Tr.leafList, List.mem_singleton] at hx
    subst hx
    simp only [Tr.Good] at h
    rcases h with ⟨h0, -, -⟩ | ⟨-, hd, -⟩
    · exact Or.inl h0
    · exact Or.inr hd
  | _, .node t₁ t₂, h, x, hx => by
    simp only [Tr.Good] at h
    simp only [Tr.leafList, List.mem_append] at hx
    rcases hx with hx | hx
    · exact leafList_good t₁ h.1 x hx
    · exact leafList_good t₂ h.2 x hx

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons x l ih`. Distinguish the cases in `hx : 0 < x.1`. Simplify using `[List.filter_cons, hx, ih]`.

Establish `h0 : x.1 = 0` using `by omega`. Simplify using `[List.filter_cons, hx, ih, h0]`.
-/
theorem sum_filter_pos (l : List (Σ M : ℕ, Submodule ℂ (Sm E M))) :
    ((l.filter fun x => 0 < x.1).map Sigma.fst).sum = (l.map Sigma.fst).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases hx : 0 < x.1
    · simp [List.filter_cons, hx, ih]
    · have h0 : x.1 = 0 := by omega
      simp [List.filter_cons, hx, ih, h0]

/- English proof (translation)
Introduce `E _ _ _ N t ht _ _`. Establish `hpos : ∀ x ∈ t.leafList.filter (fun x => 0 < x.1), 0 < x.1 ∧ IsDiscrete x.2`. Introduce `x hx`. Rewrite `hx` using `[List.mem_filter]`. Establish `hp : 0 < x.1` using `by simpa using hx.2`.

Break down `leafList_good t ht x hx.1 with h0 | hd` into its components or cases. Use linear arithmetic over natural numbers and integers. Conclude with `⟨hp, hd⟩`. Take `⟨l, hl⟩ : ∃ l, l = t.leafList.filter (fun x => 0 < x.1)` from `⟨_, rfl⟩`. Rewrite `hpos` using `[← hl]`.

Establish `hsum : (l.map Sigma.fst).sum = N` using `by rw [hl, sum_filter_pos, leafList_sum]`. Establish `hg : ∀ i : Fin l.length, 0 < (l.get i).1 ∧ IsDiscrete (l.get i).2` using `fun i => hpos _ (List.get_mem l i)`. Establish `hloc : ∀ (i : Fin l.length) (w : HeightOneSpectrum (𝓞 E)), ∃ σ, IsLocCompGL (l.get i).2 w σ` using `fun i w => GlobalTheory.DiscLocEx.exists_isLocCompGL CuspFormAutomorphicBounds.automorphicFormsFiniteGL E _ _ (hg i).2 w`. Use `choose σ hσ using hloc`. Establish `hinf : ∀ (i : Fin l.length) (τ : E →+* ℂ), ∃ m, HasInfCharGL (l.get i).2 τ m` using `fun i τ => PInfInd2A.exists_hasInfCharGL (hg i).2 τ`.

Use `choose m hm using hinf`. Establish `hN : ∑ i : Fin l.length, (l.get i).1 = N`. Establish `h1 : (List.ofFn fun i : Fin l.length => (l.get i).1) = l.map Sigma.fst`. Apply the tactic sequence `apply List.ext_get <;> simp`. Rewrite using `[← List.sum_ofFn, h1, hsum]`.

Use `⟨⟨l.length, fun i => (l.get i).1, hN, fun i => (l.get i).2, σ, m, fun i => (hg i).1, fun i => (hg i).2, hσ, hm⟩, ?_⟩` and prove the remaining obligations. Use `show (List.ofFn fun i : Fin l.length => (⟨(l.get i).1, (l.get i).2⟩ : Σ M : ℕ, Submodule ℂ (Sm E M))) = t.leafList.filter fun x => 0 < x.1`. Rewrite using `[← hl]`. Conclude with `List.ofFn_get l`.
-/
theorem preOfTree : PreOfTree := by
  intro E _ _ _ N t ht _ _
  have hpos : ∀ x ∈ t.leafList.filter (fun x => 0 < x.1), 0 < x.1 ∧ IsDiscrete x.2 := by
    intro x hx
    rw [List.mem_filter] at hx
    have hp : 0 < x.1 := by simpa using hx.2
    rcases leafList_good t ht x hx.1 with h0 | hd
    · omega
    · exact ⟨hp, hd⟩
  obtain ⟨l, hl⟩ : ∃ l, l = t.leafList.filter (fun x => 0 < x.1) := ⟨_, rfl⟩
  rw [← hl] at hpos
  have hsum : (l.map Sigma.fst).sum = N := by rw [hl, sum_filter_pos, leafList_sum]
  have hg : ∀ i : Fin l.length, 0 < (l.get i).1 ∧ IsDiscrete (l.get i).2 :=
    fun i => hpos _ (List.get_mem l i)
  have hloc : ∀ (i : Fin l.length) (w : HeightOneSpectrum (𝓞 E)), ∃ σ, IsLocCompGL (l.get i).2 w σ :=
    fun i w => GlobalTheory.DiscLocEx.exists_isLocCompGL CuspFormAutomorphicBounds.automorphicFormsFiniteGL E _ _ (hg i).2 w
  choose σ hσ using hloc
  have hinf : ∀ (i : Fin l.length) (τ : E →+* ℂ), ∃ m, HasInfCharGL (l.get i).2 τ m :=
    fun i τ => PInfInd2A.exists_hasInfCharGL (hg i).2 τ
  choose m hm using hinf
  have hN : ∑ i : Fin l.length, (l.get i).1 = N := by
    have h1 : (List.ofFn fun i : Fin l.length => (l.get i).1) = l.map Sigma.fst := by
      apply List.ext_get <;> simp
    rw [← List.sum_ofFn, h1, hsum]
  refine ⟨⟨l.length, fun i => (l.get i).1, hN, fun i => (l.get i).2, σ, m, fun i => (hg i).1,
    fun i => (hg i).2, hσ, hm⟩, ?_⟩
  show (List.ofFn fun i : Fin l.length => (⟨(l.get i).1, (l.get i).2⟩ : Σ M : ℕ, Submodule ℂ (Sm E M))) =
    t.leafList.filter fun x => 0 < x.1
  rw [← hl]
  exact List.ofFn_get l

end PositivityTheory.Rg.BcB.SpectralAccumulation.PreOfTreePf

/- English proof (translation)
The claim follows from `PositivityTheory.Rg.BcB.SpectralAccumulation.PreOfTreePf.preOfTree`.
-/
theorem PositivityTheory.Rg.BcB.SpectralAccumulation.preOfTree_holds : PositivityTheory.Rg.BcB.SpectralAccumulation.PreOfTree := PositivityTheory.Rg.BcB.SpectralAccumulation.PreOfTreePf.preOfTree

end
