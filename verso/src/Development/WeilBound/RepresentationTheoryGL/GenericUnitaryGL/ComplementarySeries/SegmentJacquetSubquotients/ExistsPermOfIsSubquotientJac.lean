import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegTwo
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.MultOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquivOfMultiplicityOneUniqueFactor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetQuotientEigenvector
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLength
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.WeilBound.CoreStatements.PublishedTheorems.SegmentRepresentations.IsIrreduciblePiTensorSegTerm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiProductSingleFactorEquiv
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSubquotientCompMulSingle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace PositivityTheory.Pf1.SegRepC.Perm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Introduce `i j`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Take `⟨h0, hdj⟩` from `hne`. Establish `hcusp : IsCuspidal (segTerm σ.ρ l i)` using `GlobalTheory.LocGL.isCuspidal_twist hσ (GlobalTheory.LocGL.isSmoothChar_absPow _)`.

Establish `hsum` using `b.2.1 i`. Simplify using `only [Fintype.card_fin] at hsum`. Choose the witnesses or unpack the hypotheses as in `⟨j', hj'ne, hj'0⟩ : ∃ j', j' ≠ j ∧ b.1 i j' ≠ 0 := by`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`.

Apply `hdj` to reduce the goal to its premises. Rewrite `hsum` using `[Finset.sum_eq_single j (fun j' _ hj' => hall j' hj') (by simp)]`. Conclude with `hsum`. Establish `hpos : 0 < b.1 i j` using `Nat.pos_of_ne_zero h0`. Establish `hpos' : 0 < b.1 i j'` using `Nat.pos_of_ne_zero hj'0`.

Establish `hbot : unipRad k (f i) ≠ ⊥`. Rewrite using `[GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff]`. Break down `lt_or_gt_of_ne hj'ne with h | h` into its components or cases. Conclude with `⟨f i ⟨j', ⟨0, hpos'⟩⟩, f i ⟨j, ⟨0, hpos⟩⟩, by rw [blk_apply, blk_apply]; exact h⟩`. Conclude with `⟨f i ⟨j, ⟨0, hpos⟩⟩, f i ⟨j', ⟨0, hpos'⟩⟩, by rw [blk_apply, blk_apply]; exact h⟩`.

Establish `hsub` using `hcusp.2 l (b.1 i) (f i) hbot`. Take `⟨S, g, hg⟩` from `hs i`. Establish `hnt : ∀ j, Nontrivial (s i j).V`. Introduce `j`. Use `haveI := (s i j).irr`.

Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nontrivial_iff_subsingleton]`. Apply `(bot_ne_top : (⊥ : Subrepresentation (s i j).ρ) ≠ ⊤)` to reduce the goal to its premises. Use extensionality with `x`. Rewrite using `[Subsingleton.elim x 0]`.

Conclude with `⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩`. Use `haveI := GlobalTheory.ProdSupport.nontrivial_piTensor (fun j => (s i j).V) hnt`. Take `⟨x, y, hxy⟩` from `exists_pair_ne (PiTensorProduct ℂ fun j => (s i j).V)`. Take `⟨x', rfl⟩` from `hg x`. Take `⟨y', rfl⟩` from `hg y`.

Apply `hxy` to reduce the goal to its premises. Establish `: x' = y'` using `Subtype.ext (Subsingleton.elim _ _)`. Rewrite using `[this]`.
-/
theorem entries_zero_or_d {d l : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    (b : SizeMatrix (fun _ : Fin l => Fin d) (fun _ : Fin l => Fin d))
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin d)
    (s : ∀ i j, IrrRep (GL (Fin (b.1 i j)) k))
    (hs : ∀ i, IsSubquotient (piTensor fun j => (s i j).ρ) (jac (f i) (segTerm σ.ρ l i))) :
    ∀ i j, b.1 i j = 0 ∨ b.1 i j = d := by
  intro i j
  by_contra hne
  push_neg at hne
  obtain ⟨h0, hdj⟩ := hne
  have hcusp : IsCuspidal (segTerm σ.ρ l i) :=
    GlobalTheory.LocGL.isCuspidal_twist hσ (GlobalTheory.LocGL.isSmoothChar_absPow _)
  have hsum := b.2.1 i
  simp only [Fintype.card_fin] at hsum
  obtain ⟨j', hj'ne, hj'0⟩ : ∃ j', j' ≠ j ∧ b.1 i j' ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hdj
    rw [Finset.sum_eq_single j (fun j' _ hj' => hall j' hj') (by simp)] at hsum
    exact hsum
  have hpos : 0 < b.1 i j := Nat.pos_of_ne_zero h0
  have hpos' : 0 < b.1 i j' := Nat.pos_of_ne_zero hj'0
  have hbot : unipRad k (f i) ≠ ⊥ := by
    rw [GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff]
    rcases lt_or_gt_of_ne hj'ne with h | h
    · exact ⟨f i ⟨j', ⟨0, hpos'⟩⟩, f i ⟨j, ⟨0, hpos⟩⟩, by rw [blk_apply, blk_apply]; exact h⟩
    · exact ⟨f i ⟨j, ⟨0, hpos⟩⟩, f i ⟨j', ⟨0, hpos'⟩⟩, by rw [blk_apply, blk_apply]; exact h⟩
  have hsub := hcusp.2 l (b.1 i) (f i) hbot
  obtain ⟨S, g, hg⟩ := hs i
  have hnt : ∀ j, Nontrivial (s i j).V := by
    intro j
    haveI := (s i j).irr
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply (bot_ne_top : (⊥ : Subrepresentation (s i j).ρ) ≠ ⊤)
    ext x
    rw [Subsingleton.elim x 0]
    exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
  haveI := GlobalTheory.ProdSupport.nontrivial_piTensor (fun j => (s i j).V) hnt
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (PiTensorProduct ℂ fun j => (s i j).V)
  obtain ⟨x', rfl⟩ := hg x
  obtain ⟨y', rfl⟩ := hg y
  apply hxy
  have : x' = y' := Subtype.ext (Subsingleton.elim _ _)
  rw [this]

open GlobalTheory.LocGL in

/- English proof (translation)
Substitute `hcd` using the available equality. Establish `h1` using `GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun j => (s j).ρ) (fun j => (s j).irr) j₀`. Establish `h2` using `h1.trans (SupportUnique.isSubquotient_comp hs (MonoidHom.mulSingle (fun j => GL (Fin (c j)) k) j₀))`. Establish `h3` using `h2.trans (SupportUnique.isSubquotient_jac_single j₀ h0 f τ)`. Take `⟨φ⟩` from `SupportUnique.nonempty_equiv_of_isSubquotient (s j₀).irr hτ h3`.

Conclude with `IrrGL.of_eq_of.2 ⟨φ.symm⟩`.
-/
theorem row_of_eq {d r : ℕ} (c : Fin r → ℕ) (j₀ : Fin r) (h0 : ∀ j, j ≠ j₀ → c j = 0) (hcd : c j₀ = d)
    (f : (Σ j, Fin (c j)) ≃ Fin d) {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GL (Fin d) k) V) (hτs : IsSmooth τ) (hτ : τ.IsIrreducible)
    (s : ∀ j, IrrRep (GL (Fin (c j)) k)) (hs : IsSubquotient (piTensor fun j => (s j).ρ) (jac f τ)) :
    IrrGL.of (s j₀).ρ (s j₀).smooth (s j₀).irr = IrrGL.of τ hτs hτ := by
  subst hcd
  have h1 := GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun j => (s j).ρ) (fun j => (s j).irr) j₀
  have h2 := h1.trans (SupportUnique.isSubquotient_comp hs
    (MonoidHom.mulSingle (fun j => GL (Fin (c j)) k) j₀))
  have h3 := h2.trans (SupportUnique.isSubquotient_jac_single j₀ h0 f τ)
  obtain ⟨φ⟩ := SupportUnique.nonempty_equiv_of_isSubquotient (s j₀).irr hτ h3
  exact IrrGL.of_eq_of.2 ⟨φ.symm⟩

open GlobalTheory.LocGL in

/- English proof (translation)
Establish `hcd : c i₀ = d` using `congrArg Sigma.fst h`. Substitute `hcd` using the available equality. Take `⟨φ⟩` from `IrrGL.of_eq_of.1 h`. Take `⟨ψ⟩` from `GlobalTheory.CompanionTheory.WordProd.OneBlockProd.multiProd_single c i₀ h0 t g`. Conclude with `⟨ψ.trans φ⟩`.
-/
theorem col_of_eq {d r : ℕ} (c : Fin r → ℕ) (i₀ : Fin r) (h0 : ∀ i, i ≠ i₀ → c i = 0)
    (g : (Σ i, Fin (c i)) ≃ Fin d) (t : ∀ i, IrrRep (GL (Fin (c i)) k)) {V : Type} [AddCommGroup V]
    [Module ℂ V] (τ : Representation ℂ (GL (Fin d) k) V) (hτs : IsSmooth τ) (hτ : τ.IsIrreducible)
    (h : IrrGL.of (t i₀).ρ (t i₀).smooth (t i₀).irr = IrrGL.of τ hτs hτ) :
    Nonempty ((multiProd g fun i => (t i).ρ).Equiv τ) := by
  have hcd : c i₀ = d := congrArg Sigma.fst h
  subst hcd
  obtain ⟨φ⟩ := IrrGL.of_eq_of.1 h
  obtain ⟨ψ⟩ := GlobalTheory.CompanionTheory.WordProd.OneBlockProd.multiProd_single c i₀ h0 t g
  exact ⟨ψ.trans φ⟩

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `h` using `Finset.sum_le_sum_of_subset (f := c) (Finset.subset_univ {j, j'})`. Rewrite `h` using `[Finset.sum_pair hne, hsum, hj, hj']`. Use linear arithmetic over natural numbers and integers.
-/
theorem eq_of_eq_d {d l : ℕ} (hd : 0 < d) (c : Fin l → ℕ) (hsum : ∑ j, c j = d) {j j' : Fin l}
    (hj : c j = d) (hj' : c j' = d) : j = j' := by
  classical
  by_contra hne
  have h := Finset.sum_le_sum_of_subset (f := c) (Finset.subset_univ {j, j'})
  rw [Finset.sum_pair hne, hsum, hj, hj'] at h
  omega

/- English proof (translation)
Take `⟨j, -, hj⟩` from `Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := c) (by omega)`. Conclude with `⟨j, (h01 j).resolve_left hj⟩`.
-/
theorem exists_eq_d {d l : ℕ} (hd : 0 < d) (c : Fin l → ℕ) (hsum : ∑ j, c j = d)
    (h01 : ∀ j, c j = 0 ∨ c j = d) : ∃ j, c j = d := by
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := c) (by omega)
  exact ⟨j, (h01 j).resolve_left hj⟩

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Establish `hr : ∀ i, ∑ j, b.1 i j = d` using `fun i => by simpa using b.2.1 i`. Establish `hc : ∀ j, ∑ i, b.1 i j = d` using `fun j => by simpa using b.2.2 j`. Use `choose v hv using fun j => exists_eq_d hd (fun i => b.1 i j) (hc j) (fun i => h01 i j)`. Establish `hvinj : Function.Injective v` using `fun j j' e => eq_of_eq_d hd (b.1 (v j)) (hr (v j)) (hv j) (e ▸ hv j')`. Set `w : Equiv.Perm (Fin l)` to `Equiv.ofBijective v (Finite.injective_iff_bijective.1 hvinj)`.

Use `⟨w, ?_⟩` and prove the remaining obligations. Establish `hE : ∀ j, Nonempty ((multiProd (g j) fun i => (s i j).ρ).Equiv (segTerm σ.ρ l (v j)))`. Introduce `j`. Use `col_of_eq (fun i => b.1 i j) (v j) (fun i hi => ?_) (g j) (fun i => s i j) _ (MultOne.isSmooth_segTerm σ _) (MultOne.isIrreducible_segTerm σ _) ?_` and prove the remaining obligations. Conclude with `(h01 i j).resolve_right fun h => hi (eq_of_eq_d hd (fun i => b.1 i j) (hc j) h (hv j))`.

Conclude with `row_of_eq (b.1 (v j)) j (fun j' hj' => (h01 (v j) j').resolve_right fun h => hj' (eq_of_eq_d hd _ (hr (v j)) h (hv j))) (hv j) (f (v j)) _ _ _ (s (v j)) (hs (v j))`. Set `E` to `GlobalTheory.LocGL.piTensorEquiv fun j => (hE j).some`. Establish `hT : (piTensor fun j => segTerm σ.ρ l (v j)).IsIrreducible` using `GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => MultOne.isIrreducible_segTerm σ _) fun a φ hφ => GlobalTheory.CompanionTheory.SocleFrob.exists_eq_smul_id _ (MultOne.isSmooth_segTerm σ _) (MultOne.isIrreducible_segTerm σ _) φ hφ`. Establish `h'` using `h.trans (IsSubquotient.of_injective E.toIntertwiningMap E.toLinearEquiv.injective)`. Take `⟨φ⟩` from `GlobalTheory.LocGL.SupportUnique.nonempty_equiv_of_isSubquotient hπ hT h'`.

Conclude with `⟨φ.symm⟩`.
-/
theorem exists_perm_of_cell {d l : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    (b : SizeMatrix (fun _ : Fin l => Fin d) (fun _ : Fin l => Fin d))
    (h01 : ∀ i j, b.1 i j = 0 ∨ b.1 i j = d)
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin d) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin d)
    (s : ∀ i j, IrrRep (GL (Fin (b.1 i j)) k))
    (hs : ∀ i, IsSubquotient (piTensor fun j => (s i j).ρ) (jac (f i) (segTerm σ.ρ l i)))
    {X : Type} [AddCommGroup X] [Module ℂ X] (π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X)
    (hπ : π.IsIrreducible)
    (h : IsSubquotient π (piTensor fun j => multiProd (g j) fun i => (s i j).ρ)) :
    ∃ w : Equiv.Perm (Fin l), Nonempty (π.Equiv (piTensor fun a => segTerm σ.ρ l (w a))) := by
  classical
  have hr : ∀ i, ∑ j, b.1 i j = d := fun i => by simpa using b.2.1 i
  have hc : ∀ j, ∑ i, b.1 i j = d := fun j => by simpa using b.2.2 j
  choose v hv using fun j => exists_eq_d hd (fun i => b.1 i j) (hc j) (fun i => h01 i j)
  have hvinj : Function.Injective v := fun j j' e =>
    eq_of_eq_d hd (b.1 (v j)) (hr (v j)) (hv j) (e ▸ hv j')
  let w : Equiv.Perm (Fin l) := Equiv.ofBijective v (Finite.injective_iff_bijective.1 hvinj)
  refine ⟨w, ?_⟩
  have hE : ∀ j, Nonempty ((multiProd (g j) fun i => (s i j).ρ).Equiv (segTerm σ.ρ l (v j))) := by
    intro j
    refine col_of_eq (fun i => b.1 i j) (v j) (fun i hi => ?_) (g j) (fun i => s i j) _
      (MultOne.isSmooth_segTerm σ _) (MultOne.isIrreducible_segTerm σ _) ?_
    · exact (h01 i j).resolve_right fun h => hi (eq_of_eq_d hd (fun i => b.1 i j) (hc j) h (hv j))
    · exact row_of_eq (b.1 (v j)) j
        (fun j' hj' => (h01 (v j) j').resolve_right fun h => hj' (eq_of_eq_d hd _ (hr (v j)) h (hv j)))
        (hv j) (f (v j)) _ _ _ (s (v j)) (hs (v j))
  let E := GlobalTheory.LocGL.piTensorEquiv fun j => (hE j).some
  have hT : (piTensor fun j => segTerm σ.ρ l (v j)).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => MultOne.isIrreducible_segTerm σ _)
      fun a φ hφ => GlobalTheory.CompanionTheory.SocleFrob.exists_eq_smul_id _ (MultOne.isSmooth_segTerm σ _)
        (MultOne.isIrreducible_segTerm σ _) φ hφ
  have h' := h.trans (IsSubquotient.of_injective E.toIntertwiningMap E.toLinearEquiv.injective)
  obtain ⟨φ⟩ := GlobalTheory.LocGL.SupportUnique.nonempty_equiv_of_isSubquotient hπ hT h'
  exact ⟨φ.symm⟩

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Take `⟨b, f, g, s, hs, hπs⟩` from `exists_cell_of_isSubquotient (hG k).1 (hG k).2 (consecBlocks l d) (consecBlocks l d) (MultOne.isSmooth_segTerm σ) (MultOne.hasFiniteLength_segTerm σ) hπ h`. Conclude with `exists_perm_of_cell hd σ hσ b (entries_zero_or_d hd σ hσ b f s hs) f g s hs π hπ hπs`.
-/
theorem exists_perm_of_isSubquotient_jac (hG : GeometricLemma) {d l : ℕ} (hd : 0 < d) (hl : 0 < l)
    (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    {X : Type} [AddCommGroup X] [Module ℂ X] (π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X)
    (hπ : π.IsIrreducible)
    (h : IsSubquotient π (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l)))) :
    ∃ w : Equiv.Perm (Fin l), Nonempty (π.Equiv (piTensor fun a => segTerm σ.ρ l (w a))) := by
  obtain ⟨b, f, g, s, hs, hπs⟩ := exists_cell_of_isSubquotient (hG k).1 (hG k).2
    (consecBlocks l d) (consecBlocks l d) (MultOne.isSmooth_segTerm σ)
    (MultOne.hasFiniteLength_segTerm σ) hπ h
  exact exists_perm_of_cell hd σ hσ b (entries_zero_or_d hd σ hσ b f s hs) f g s hs π hπ hπs

end PositivityTheory.Pf1.SegRepC.Perm

end
