import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.KernelSumOfClassData
import Formalism.SharpRestriction.GrowthBounds.LatticeSystems

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset Formalism.MainNotions.G.LatticeSystems

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Gen

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

/- English proof (translation)
Establish `hres` using `(P.setting v).res_card`. Establish `hfin : Finite (P.W v ⧸ Ideal.span {(p : P.W v)})`. Apply `Nat.finite_of_card_ne_zero` to reduce the goal to its premises. Rewrite using `[hres]`. Conclude with `pow_ne_zero _ (P.setting v).prime.ne_zero`.

Conclude with `ef_edges_finite_gen p (P.n' v) i (P.m + 1) hfin L`.
-/
theorem tm_fin (v : Fin P.nV) (i : ℕ) (L : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :
    {L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v) | IsEdge p (P.n' v) i ⟨L'', L⟩}.Finite := by
  have hres := (P.setting v).res_card
  have hfin : Finite (P.W v ⧸ Ideal.span {(p : P.W v)}) := by
    apply Nat.finite_of_card_ne_zero
    rw [hres]
    exact pow_ne_zero _ (P.setting v).prime.ne_zero
  exact ef_edges_finite_gen p (P.n' v) i (P.m + 1) hfin L

def tmE (v : Fin P.nV) (i : ℕ) (L : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :
    Finset (Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :=
  (tm_fin P v i L).toFinset

/- English proof (translation)
Use `show (∑ᶠ (L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) (_ : L'' ∈ {L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v) | IsEdge p (P.n' v) i ⟨L'', L v⟩}), F (Function.update L v L'')) = _`. Conclude with `finsum_mem_eq_finite_toFinset_sum _ (tm_fin P v i (L v))`.
-/
theorem tm_eq (v : Fin P.nV) (i : ℕ) (F : P.Tup → P.Xsp) (L : P.Tup) :
    P.Tminus v i F L = ∑ L'' ∈ tmE P v i (L v), F (Function.update L v L'') := by
  show (∑ᶠ (L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v))
      (_ : L'' ∈ {L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v) | IsEdge p (P.n' v) i ⟨L'', L v⟩}),
      F (Function.update L v L'')) = _
  exact finsum_mem_eq_finite_toFinset_sum _ (tm_fin P v i (L v))

/- English proof (translation)
Rewrite using `[tm_eq]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `L'' hL''`. Apply `hF` to reduce the goal to its premises. Introduce `hlat`.

Apply `hL` to reduce the goal to its premises. Use `show ∀ w, IsLattice (P.W w) (L w)`. Introduce `w`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality.

Establish `he : IsEdge p (P.n' w) i ⟨L'', L w⟩` using `(tm_fin P w i (L w)).mem_toFinset.mp hL''`. Conclude with `he.2.1`. Simplify `hlat w` using `[Function.update, hw]`.
-/
theorem tm_zero (v : Fin P.nV) (i : ℕ) (F : P.Tup → P.Xsp) (hF : ∀ L, ¬ P.IsLatTup L → F L = 0) (L : P.Tup)
    (hL : ¬ P.IsLatTup L) : P.Tminus v i F L = 0 := by
  rw [tm_eq]
  apply Finset.sum_eq_zero
  intro L'' hL''
  apply hF
  intro hlat
  apply hL
  show ∀ w, IsLattice (P.W w) (L w)
  intro w
  by_cases hw : w = v
  · subst hw
    have he : IsEdge p (P.n' w) i ⟨L'', L w⟩ := (tm_fin P w i (L w)).mem_toFinset.mp hL''
    exact he.2.1
  · simpa [Function.update, hw] using hlat w

/- English proof (translation)
Use function extensionality and compare the values at `w`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Simplify using `[Function.update, Level.smul, nt_phi]`. Simplify using `[Function.update, hw, Level.smul, nt_phi]`.
-/
theorem smul_update (C : Level P) (γ : C.Γ) (v : Fin P.nV) (L : P.Tup)
    (A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :
    C.smul γ (Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v A) =
    Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) (C.smul γ L) v (A.map (nt_phi (P.W v) (C.act v γ))) := by
  funext w
  by_cases hw : w = v
  · subst hw
    simp [Function.update, Level.smul, nt_phi]
  · simp [Function.update, hw, Level.smul, nt_phi]

/- English proof (translation)
Rewrite using `[tm_eq, tm_eq, map_sum, Finset.smul_sum]`. Use `symm`. Apply `Finset.sum_nbij' (fun A => A.map (nt_phi (P.W v) (C.act v γ))) (fun A => A.map (nt_phi (P.W v) (C.act v γ)⁻¹))` to reduce the goal to its premises. Introduce `A hA`. Establish `hA' : IsEdge p (P.n' v) i ⟨A, L v⟩` using `(tm_fin P v i (L v)).mem_toFinset.mp hA`.

Conclude with `(tm_fin P v i (C.smul γ L v)).mem_toFinset.mpr (nt_edge_map p (P.n' v) i (C.act v γ) A (L v) hA')`. Introduce `B hB`. Establish `hB' : IsEdge p (P.n' v) i ⟨B, (L v).map (nt_phi (P.W v) (C.act v γ))⟩` using `(tm_fin P v i (C.smul γ L v)).mem_toFinset.mp hB`. Establish `h2` using `nt_edge_map p (P.n' v) i (C.act v γ)⁻¹ B ((L v).map (nt_phi (P.W v) (C.act v γ))) hB'`. Rewrite `h2` using `[nt_map_inv]`.

Conclude with `(tm_fin P v i (L v)).mem_toFinset.mpr h2`. Introduce `A _`. Conclude with `nt_map_inv _ _`. Introduce `B _`. Conclude with `nt_map_inv' _ _`.

Introduce `A _`. Establish `h` using `hF' γ (Function.update L v A)`. Rewrite `h` using `[smul_update]`. Conclude with `h.symm`.
-/
theorem tm_equiv (C : Level P) (v : Fin P.nV) (i : ℕ) (F : P.Tup → P.Xsp)
    (hF' : ∀ (γ : C.Γ) (L : P.Tup), F (C.smul γ L) = (C.χ γ : O) • C.actX γ (F L)) (γ : C.Γ) (L : P.Tup) :
    P.Tminus v i F (C.smul γ L) = (C.χ γ : O) • C.actX γ (P.Tminus v i F L) := by
  rw [tm_eq, tm_eq, map_sum, Finset.smul_sum]
  symm
  apply Finset.sum_nbij' (fun A => A.map (nt_phi (P.W v) (C.act v γ)))
    (fun A => A.map (nt_phi (P.W v) (C.act v γ)⁻¹))
  · intro A hA
    have hA' : IsEdge p (P.n' v) i ⟨A, L v⟩ := (tm_fin P v i (L v)).mem_toFinset.mp hA
    exact (tm_fin P v i (C.smul γ L v)).mem_toFinset.mpr (nt_edge_map p (P.n' v) i (C.act v γ) A (L v) hA')
  · intro B hB
    have hB' : IsEdge p (P.n' v) i ⟨B, (L v).map (nt_phi (P.W v) (C.act v γ))⟩ :=
      (tm_fin P v i (C.smul γ L v)).mem_toFinset.mp hB
    have h2 := nt_edge_map p (P.n' v) i (C.act v γ)⁻¹ B ((L v).map (nt_phi (P.W v) (C.act v γ))) hB'
    rw [nt_map_inv] at h2
    exact (tm_fin P v i (L v)).mem_toFinset.mpr h2
  · intro A _
    exact nt_map_inv _ _
  · intro B _
    exact nt_map_inv' _ _
  · intro A _
    have h := hF' γ (Function.update L v A)
    rw [smul_update] at h
    exact h.symm

end Gen

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Introduce `J v i F hF`. Use `⟨fun c L hL => ?_, fun c γ L => ?_⟩` and prove the remaining obligations. Conclude with `tm_zero (X.Pj J) (X.vJ J v) i (F c) (fun L' hL' => hF.1 c L' hL') L hL`. Conclude with `tm_equiv (X.Pj J) (X.Lv.lev J c) (X.vJ J v) i (F c) (fun γ' L' => hF.2 c γ' L') γ L`.
-/
theorem restTmEquiv (X : Sys p) : RestTmEquiv X := by
  intro J v i F hF
  refine ⟨fun c L hL => ?_, fun c γ L => ?_⟩
  · exact tm_zero (X.Pj J) (X.vJ J v) i (F c) (fun L' hL' => hF.1 c L' hL') L hL
  · exact tm_equiv (X.Pj J) (X.Lv.lev J c) (X.vJ J v) i (F c) (fun γ' L' => hF.2 c γ' L') γ L

/- English proof (translation)
The claim follows from `formB_of D Y hA (restTmEquiv X)`.
-/
theorem formB (D : Formalism.BasicNotions.D7) (X : Sys p) (Y : Pend X) (hA : admitted D X Y) : FormB X Y :=
  formB_of D Y hA (restTmEquiv X)

end Formalism.MainNotions.FormalGroupSystem.Pf
