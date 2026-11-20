import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellUnipotentUniquenessClosedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorCompactUnipotentFixer

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.Rodier.OpenBump
open GroundTheory.Automorphic.GLnLocal

namespace PositivityTheory.RgUd.CellA

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
private theorem perm_matrix_conj_apply {k : Type} [Field k] {N : ℕ} (w : Equiv.Perm (Fin N)) (z : GL (Fin N) k)
    (i j : Fin N) :
    (((pm k w)⁻¹ * z * pm k w : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j =
      (z : Matrix (Fin N) (Fin N) k) (w i) (w j) := by
  have h := GlobalTheory.Parabolic.conj_permGL_apply (k := k) w ((pm k w)⁻¹ * z * pm k w) i j
  have e : GlobalTheory.Parabolic.permGL k w * ((pm k w)⁻¹ * z * pm k w) * (GlobalTheory.Parabolic.permGL k w)⁻¹ = z := by
    change pm k w * ((pm k w)⁻¹ * z * pm k w) * (pm k w)⁻¹ = z
    group
  rw [e] at h
  exact h.symm

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Substitute using the available equality. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem pm_wOpen_conj_mem_unipB_of_mem_unipRadLower {k : Type} [Field k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)
    {z : GL (Fin N) k} (hz : z ∈ unipRadLower k (stdBlocks d hd)) :
    (pm k (wOpen d hd))⁻¹ * z * pm k (wOpen d hd) ∈ unipB k (Fin N) := by
  rw [mem_unipB]
  rw [mem_unipRadLower] at hz
  obtain ⟨hlow, hdiag⟩ := hz
  rw [mem_parabLower_iff] at hlow
  have hmono := Tuple.monotone_sort (wKey d hd)
  have hanti : ∀ i j : Fin N, j ≤ i →
      blk (stdBlocks d hd) (wOpen d hd i) ≤ blk (stdBlocks d hd) (wOpen d hd j) := by
    intro i j hji
    have := Prod.Lex.monotone_fst _ _ (hmono hji)
    simpa [wKey, wOpen] using this
  constructor
  · intro i j hji
    rw [perm_matrix_conj_apply]
    obtain ⟨⟨a, p⟩, hp⟩ : ∃ x, stdBlocks d hd x = wOpen d hd i := ⟨_, Equiv.apply_symm_apply _ _⟩
    obtain ⟨⟨b, q⟩, hq⟩ : ∃ x, stdBlocks d hd x = wOpen d hd j := ⟨_, Equiv.apply_symm_apply _ _⟩
    have hab := hanti i j hji.le
    rw [← hp, ← hq] at hab
    simp only [blk, Equiv.symm_apply_apply] at hab
    rw [← hp, ← hq]
    rcases lt_or_eq_of_le hab with hlt | rfl
    · exact hlow a b p q hlt
    · rw [hdiag]
      have hpq : p ≠ q := by
        intro hpq
        subst hpq
        have hij : wOpen d hd i = wOpen d hd j := by rw [← hp, ← hq]
        exact absurd ((wOpen d hd).injective hij) (ne_of_gt hji)
      exact Matrix.one_apply_ne hpq
  · intro i
    rw [perm_matrix_conj_apply]
    obtain ⟨⟨a, p⟩, hp⟩ : ∃ x, stdBlocks d hd x = wOpen d hd i := ⟨_, Equiv.apply_symm_apply _ _⟩
    rw [← hp, hdiag]
    exact Matrix.one_apply_eq p

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Assume the negation of the conclusion and derive a contradiction.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_bump (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (hψ : Continuous ψ) (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type}
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (hρ : IsSmooth ρ) (v : W) :
    ∃ n : ℕ, 1 ≤ n ∧
      (∀ (l : GL (Fin N) k) (hl : l ∈ unipB k (Fin N)), l ∈ congruenceSubgroup k N n → whitChar ψ N ⟨l, hl⟩ = 1) ∧
      IsCompact ((unipU k d hd ⊓ (congruenceSubgroup k N n).comap
        (MulAut.conj (pm k (wOpen d hd))).toMonoidHom : Subgroup (GL (Fin N) k)) : Set (GL (Fin N) k)) ∧
      (∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) =
        ((unipU k d hd ⊓ (congruenceSubgroup k N n).comap
          (MulAut.conj (pm k (wOpen d hd))).toMonoidHom : Subgroup (GL (Fin N) k)) : Set (GL (Fin N) k))) ∧
      ∃ f ∈ openFns d hd ρ,
        (∀ u ∈ (unipU k d hd ⊓ (congruenceSubgroup k N n).comap
          (MulAut.conj (pm k (wOpen d hd))).toMonoidHom : Subgroup (GL (Fin N) k)),
            f.1.1 (pm k (wOpen d hd) * u) = v) ∧
        ∀ u ∈ unipU k d hd, u ∉ (unipU k d hd ⊓ (congruenceSubgroup k N n).comap
          (MulAut.conj (pm k (wOpen d hd))).toMonoidHom : Subgroup (GL (Fin N) k)) →
            f.1.1 (pm k (wOpen d hd) * u) = 0 := by
  classical
  obtain ⟨m, hm1, hfix, hwhit⟩ := GlobalTheory.CompanionTheory.Rodier.OpenBump.exists_level ψ hψ d hd ρ hρ v
  have hKo : IsOpen (congruenceSubgroup k N m : Set (GL (Fin N) k)) := isOpen_congruenceSubgroup k N m
  obtain ⟨f, hsupp, hfK⟩ := GlobalTheory.CompanionTheory.Rodier.OpenBump.exists_smInd_bump (parab k (stdBlocks d hd))
    (congruenceSubgroup k N m) hKo _ v hfix
  let f' : IndSp (stdBlocks d hd) ρ :=
    ⟨(ind (parab k (stdBlocks d hd)) ((twist ρ (deltaHalf k fun a => Fin (d a))).comp
      (leviProj k (stdBlocks d hd)))) (pm k (wOpen d hd))⁻¹ f.1,
      smoothPart_stable _ _ _ f.2⟩
  have hf' : ∀ x, f'.1.1 x = f.1.1 (x * (pm k (wOpen d hd))⁻¹) := fun x => rfl
  have hconj : Continuous fun g : GL (Fin N) k => pm k (wOpen d hd) * g * (pm k (wOpen d hd))⁻¹ :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hmemL : ∀ u : GL (Fin N) k, u ∈ (unipU k d hd ⊓ (congruenceSubgroup k N m).comap
      (MulAut.conj (pm k (wOpen d hd))).toMonoidHom : Subgroup (GL (Fin N) k)) ↔
      u ∈ unipU k d hd ∧ pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹ ∈ congruenceSubgroup k N m := by
    intro u
    simp [Subgroup.mem_inf, Subgroup.mem_comap, MulAut.conj_apply]
  have hUcl : IsClosed (unipU k d hd : Set (GL (Fin N) k)) := by
    have h1 : IsClosed (unipB k (Fin N) : Set (GL (Fin N) k)) :=
      GlobalTheory.JacInj.isClosed_unipRad (points (Fin N))
    have h2 : IsClosed (unipRadLower k (stdBlocks d hd) : Set (GL (Fin N) k)) :=
      GlobalTheory.JacInj.isClosed_unipRad (opp (stdBlocks d hd))
    have h3 := h2.preimage hconj
    have : (unipU k d hd : Set (GL (Fin N) k)) = (unipB k (Fin N) : Set (GL (Fin N) k)) ∩
        ((fun g : GL (Fin N) k => pm k (wOpen d hd) * g * (pm k (wOpen d hd))⁻¹) ⁻¹'
          (unipRadLower k (stdBlocks d hd) : Set (GL (Fin N) k))) := by
      ext u
      simp [unipU, Subgroup.mem_inf, Subgroup.mem_comap, MulAut.conj_apply]
    rw [this]
    exact h1.inter h3
  have hOeq : ((fun g : GL (Fin N) k => pm k (wOpen d hd) * g * (pm k (wOpen d hd))⁻¹) ⁻¹'
      (congruenceSubgroup k N m : Set (GL (Fin N) k))) =
      (fun g : GL (Fin N) k => (pm k (wOpen d hd))⁻¹ * g * pm k (wOpen d hd)) ''
        (congruenceSubgroup k N m : Set (GL (Fin N) k)) := by
    ext u
    constructor
    · intro hu
      exact ⟨_, hu, by group⟩
    · rintro ⟨y, hy, rfl⟩
      show pm k (wOpen d hd) * ((pm k (wOpen d hd))⁻¹ * y * pm k (wOpen d hd)) *
        (pm k (wOpen d hd))⁻¹ ∈ (congruenceSubgroup k N m : Set (GL (Fin N) k))
      have hy' : pm k (wOpen d hd) * ((pm k (wOpen d hd))⁻¹ * y * pm k (wOpen d hd)) *
          (pm k (wOpen d hd))⁻¹ = y := by group
      rw [hy']
      exact hy
  have hLset : ((unipU k d hd ⊓ (congruenceSubgroup k N m).comap
      (MulAut.conj (pm k (wOpen d hd))).toMonoidHom : Subgroup (GL (Fin N) k)) : Set (GL (Fin N) k)) =
      ((fun g : GL (Fin N) k => pm k (wOpen d hd) * g * (pm k (wOpen d hd))⁻¹) ⁻¹'
        (congruenceSubgroup k N m : Set (GL (Fin N) k))) ∩ (unipU k d hd : Set (GL (Fin N) k)) := by
    ext u
    rw [SetLike.mem_coe, hmemL]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  refine ⟨m, hm1, hwhit, ?_, ?_, f', ?_, ?_, ?_⟩
  · rw [hLset, hOeq]
    exact ((isCompact_congruenceSubgroup k N m).image
      ((continuous_const.mul continuous_id).mul continuous_const)).inter_right hUcl
  · exact ⟨_, hKo.preimage hconj, hLset.symm⟩
  · show ∀ g : GL (Fin N) k, f'.1.1 g ≠ 0 → g ∈ cell k d hd (wOpen d hd)
    intro g hg
    rw [hf'] at hg
    obtain ⟨p, hp, κ, hκ, hpk⟩ := hsupp _ hg
    obtain ⟨q, hq, z, _, hzL, hκqz⟩ :=
      GlobalTheory.CompanionTheory.Rodier.OpenBump.exists_parab_mul_lower d hd hm1 hκ
    refine ⟨p * q, Subgroup.mul_mem _ hp hq, _, pm_wOpen_conj_mem_unipB_of_mem_unipRadLower d hd hzL, ?_⟩
    have hg' : g = g * (pm k (wOpen d hd))⁻¹ * pm k (wOpen d hd) := by group
    rw [hg', hpk, hκqz]
    group
  · intro u hu
    rw [hmemL] at hu
    rw [hf']
    exact hfK _ hu.2
  · intro u hu hnot
    rw [hf']
    by_contra hne
    obtain ⟨p, hp, κ, hκ, hpk⟩ := hsupp _ hne
    obtain ⟨q, hq, z, hzK, hzL, hκqz⟩ :=
      GlobalTheory.CompanionTheory.Rodier.OpenBump.exists_parab_mul_lower d hd hm1 hκ
    have hlow : pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹ ∈ unipRadLower k (stdBlocks d hd) := by
      have := hu
      simp only [unipU, Subgroup.mem_inf, Subgroup.mem_comap] at this
      simpa [MulAut.conj_apply] using this.2
    have hpq : p * q = (pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹) * z⁻¹ := by
      rw [hpk, hκqz]
      group
    have h1 : p * q = 1 := by
      apply GlobalTheory.CompanionTheory.Rodier.OpenBump.eq_one_of_mem_parab_of_mem_lower (stdBlocks d hd)
      · exact Subgroup.mul_mem _ hp hq
      · rw [hpq]
        exact Subgroup.mul_mem _ hlow (Subgroup.inv_mem _ hzL)
    apply hnot
    rw [hmemL]
    refine ⟨hu, ?_⟩
    have : pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹ = z := by
      have := hpq.symm.trans h1
      rw [mul_inv_eq_one] at this
      exact this
    rw [this]
    exact hzK

end PositivityTheory.RgUd.CellA
