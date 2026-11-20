import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import GroundTheory.AutomorphicForms.GeometricLemma
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviRefinementBlockOrderStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviRefinementParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviEquivContinuousStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviDoubleCosetIntersectionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RefinedBlockOrderCompatStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockCountReindexEquivsStatement
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

noncomputable section

namespace GlobalTheory.CompanionTheory.GeomCell

open GroundTheory.Automorphic.Parabolic (leviPar normLeviParSqrtModular normLeviParInvSqrtModular innerJacquetSpace leviUnipotent cellLeviSubIncl cellInnerHom leviInfIncl levJacquetAction innerJacquetRep)

/- English proof (translation)
Establish `hTs : ∀ (p : P) (v : V'), T.symm (τ p v) = σ ⟨Φ p, (hHP p.1).1 p.2⟩ (T.symm v)`. Introduce `p v`. Apply `T.injective` to reduce the goal to its premises. Rewrite using `[hT, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`. Set `A : GroundTheory.Automorphic.indSpace H σ ≃ₗ[ℂ] GlobalTheory.PRep.smoothPart (GlobalTheory.PRep.ind P τ)` to `{ toFun := fun φ => ⟨⟨fun l => T ((φ : G → V) (Φ l)), fun p x => by`.

Take `⟨h1, -⟩` from `GroundTheory.Automorphic.mem_indSpace.1 φ.2`. Use `h1 ⟨Φ p, (hHP p.1).1 p.2⟩ (Φ x)` as an intermediate fact. Use `show T ((φ : G → V) (Φ (p * x))) = _`. Rewrite using `[map_mul]`. Conclude with `(congrArg T this).trans (hT p _)⟩, by`.

Take `⟨-, K, hK, hKφ⟩` from `GroundTheory.Automorphic.mem_indSpace.1 φ.2`. Use `mem_smoothPart_of_nhds (Filter.mem_of_superset ((hK.preimage hΦ).mem_nhds (by simp [one_mem])) fun l hl => ?_)` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Use `show T ((φ : G → V) (Φ (x * l))) = T ((φ : G → V) (Φ x))`.

Rewrite using `[map_mul, hKφ _ hl]⟩`. Use `invFun := fun ψ => ⟨fun x => T.symm (ψ.1.1 (Φ.symm x)), by`. Use `GroundTheory.Automorphic.mem_indSpace.2 ⟨fun h x => ?_, ?_⟩` and prove the remaining obligations. Establish `hp : Φ.symm h ∈ P` using `(hHP _).2 (by simp)`. Establish `h1` using `ψ.1.2 ⟨Φ.symm h, hp⟩ (Φ.symm x)`.

Establish `h2 : Φ.symm ((h : G) * x) = Φ.symm h * Φ.symm x` using `map_mul _ _ _`. Use `show T.symm (ψ.1.1 (Φ.symm ((h : G) * x))) = σ h (T.symm (ψ.1.1 (Φ.symm x)))`. Rewrite using `[h2]`. Use `(congrArg T.symm h1).trans ((hTs _ _).trans ?_)` and prove the remaining obligations. Use `congr 2`.

Conclude with `Subtype.ext (by simp)`. Set `S : Subgroup L` to `{ carrier := {l | GlobalTheory.PRep.ind P τ l ψ.1 = ψ.1} mul_mem' := by`. Introduce `a b ha hb`. Simplify using `only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at *`. Rewrite using `[hb, ha]`.

Use the proof step `one_mem' := by simp`. Use the proof step `inv_mem' := by`. Introduce `a ha`. Simplify using `only [Set.mem_ofPred_eq] at *`. Use `conv_lhs => rw [← ha]`.

Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Simplify using `}`. Use `⟨S.comap Φ.symm.toMonoidHom, ?_, fun g hg x => ?_⟩` and prove the remaining obligations. Conclude with `IsOpen.preimage hΦ' ψ.2`. Establish `h3 : GlobalTheory.PRep.ind P τ (Φ.symm g) ψ.1 = ψ.1` using `hg`.

Establish `h4` using `congrFun (congrArg Subtype.val h3) (Φ.symm x)`. Establish `h5 : Φ.symm (x * g) = Φ.symm x * Φ.symm g` using `map_mul _ _ _`. Use `show T.symm (ψ.1.1 (Φ.symm (x * g))) = T.symm (ψ.1.1 (Φ.symm x))`. Rewrite using `[h5]`. Conclude with `congrArg T.symm h4⟩`.

Use the proof step `map_add' := fun a b => Subtype.ext (Subtype.ext (funext fun l => map_add T _ _))`. Use the proof step `map_smul' := fun c a => Subtype.ext (Subtype.ext (funext fun l => map_smul T _ _))`. Use `left_inv := fun a => Subtype.ext (funext fun x => by simp)`. Use `right_inv := fun a => Subtype.ext (Subtype.ext (funext fun x => by simp)) }`. Use `⟨.mk A fun l => ?_⟩` and prove the remaining obligations.

Use `LinearMap.ext fun a => Subtype.ext (Subtype.ext (funext fun x => ?_))` and prove the remaining obligations. Use `show T ((a : G → V) (Φ x * Φ l)) = T ((a : G → V) (Φ (x * l)))`. Rewrite using `[map_mul]`.
-/
theorem nonempty_indRep_comp_equiv {G L : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group L] [TopologicalSpace L] [IsTopologicalGroup L] (Φ : L ≃* G) (hΦ : Continuous Φ)
    (hΦ' : Continuous Φ.symm) (H : Subgroup G) (P : Subgroup L) (hHP : ∀ p, p ∈ P ↔ Φ p ∈ H)
    {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (σ : Representation ℂ H V) (τ : Representation ℂ P V') (T : V ≃ₗ[ℂ] V')
    (hT : ∀ (p : P) (v : V), T (σ ⟨Φ p, (hHP p.1).1 p.2⟩ v) = τ p (T v)) :
    Nonempty (Representation.Equiv ((indRep H σ).comp Φ.toMonoidHom) (GlobalTheory.PRep.smInd P τ)) := by
  have hTs : ∀ (p : P) (v : V'), T.symm (τ p v) = σ ⟨Φ p, (hHP p.1).1 p.2⟩ (T.symm v) := by
    intro p v
    apply T.injective
    rw [hT, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  let A : GroundTheory.Automorphic.indSpace H σ ≃ₗ[ℂ] GlobalTheory.PRep.smoothPart (GlobalTheory.PRep.ind P τ) :=
    { toFun := fun φ => ⟨⟨fun l => T ((φ : G → V) (Φ l)), fun p x => by
          obtain ⟨h1, -⟩ := GroundTheory.Automorphic.mem_indSpace.1 φ.2
          have := h1 ⟨Φ p, (hHP p.1).1 p.2⟩ (Φ x)
          show T ((φ : G → V) (Φ (p * x))) = _
          rw [map_mul]
          exact (congrArg T this).trans (hT p _)⟩, by
          obtain ⟨-, K, hK, hKφ⟩ := GroundTheory.Automorphic.mem_indSpace.1 φ.2
          refine mem_smoothPart_of_nhds (Filter.mem_of_superset
            ((hK.preimage hΦ).mem_nhds (by simp [one_mem])) fun l hl => ?_)
          apply Subtype.ext
          funext x
          show T ((φ : G → V) (Φ (x * l))) = T ((φ : G → V) (Φ x))
          rw [map_mul, hKφ _ hl]⟩
      invFun := fun ψ => ⟨fun x => T.symm (ψ.1.1 (Φ.symm x)), by
          refine GroundTheory.Automorphic.mem_indSpace.2 ⟨fun h x => ?_, ?_⟩
          · have hp : Φ.symm h ∈ P := (hHP _).2 (by simp)
            have h1 := ψ.1.2 ⟨Φ.symm h, hp⟩ (Φ.symm x)
            have h2 : Φ.symm ((h : G) * x) = Φ.symm h * Φ.symm x := map_mul _ _ _
            show T.symm (ψ.1.1 (Φ.symm ((h : G) * x))) = σ h (T.symm (ψ.1.1 (Φ.symm x)))
            rw [h2]
            refine (congrArg T.symm h1).trans ((hTs _ _).trans ?_)
            congr 2
            exact Subtype.ext (by simp)
          · let S : Subgroup L :=
              { carrier := {l | GlobalTheory.PRep.ind P τ l ψ.1 = ψ.1}
                mul_mem' := by
                  intro a b ha hb
                  simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at *
                  rw [hb, ha]
                one_mem' := by simp
                inv_mem' := by
                  intro a ha
                  simp only [Set.mem_ofPred_eq] at *
                  conv_lhs => rw [← ha]
                  rw [← Module.End.mul_apply, ← map_mul]
                  simp }
            refine ⟨S.comap Φ.symm.toMonoidHom, ?_, fun g hg x => ?_⟩
            · exact IsOpen.preimage hΦ' ψ.2
            · have h3 : GlobalTheory.PRep.ind P τ (Φ.symm g) ψ.1 = ψ.1 := hg
              have h4 := congrFun (congrArg Subtype.val h3) (Φ.symm x)
              have h5 : Φ.symm (x * g) = Φ.symm x * Φ.symm g := map_mul _ _ _
              show T.symm (ψ.1.1 (Φ.symm (x * g))) = T.symm (ψ.1.1 (Φ.symm x))
              rw [h5]
              exact congrArg T.symm h4⟩
      map_add' := fun a b => Subtype.ext (Subtype.ext (funext fun l => map_add T _ _))
      map_smul' := fun c a => Subtype.ext (Subtype.ext (funext fun l => map_smul T _ _))
      left_inv := fun a => Subtype.ext (funext fun x => by simp)
      right_inv := fun a => Subtype.ext (Subtype.ext (funext fun x => by simp)) }
  refine ⟨.mk A fun l => ?_⟩
  refine LinearMap.ext fun a => Subtype.ext (Subtype.ext (funext fun x => ?_))
  show T ((a : G → V) (Φ x * Φ l)) = T ((a : G → V) (Φ (x * l)))
  rw [map_mul]

def coinvEquiv {M G W : Type} [Group M] [Group G] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ M W) (φ : M ≃* G) (U : Subgroup M) (U' : Subgroup G)
    (hU : ∀ u, u ∈ U ↔ φ u ∈ U') :
    Representation.Coinvariants ((ρ.comp φ.symm.toMonoidHom).comp U'.subtype) ≃ₗ[ℂ]
      GlobalTheory.PRep.Jacquet ρ U :=
  Submodule.quotEquivOfEq _ _ (by
    refine congrArg (Submodule.span ℂ) (Set.ext fun y => ⟨?_, ?_⟩)
    · rintro ⟨⟨u', v⟩, rfl⟩
      have hu : φ.symm (u' : G) ∈ U := (hU _).2 (by simp)
      exact ⟨⟨_, hu⟩, v, by simp⟩
    · rintro ⟨u, v, rfl⟩
      exact ⟨⟨⟨φ u, (hU _).1 u.2⟩, v⟩, by simp⟩)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coinvEquiv_mk {M G W : Type} [Group M] [Group G] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ M W) (φ : M ≃* G) (U : Subgroup M) (U' : Subgroup G)
    (hU : ∀ u, u ∈ U ↔ φ u ∈ U') (x : W) :
    coinvEquiv ρ φ U U' hU (Representation.Coinvariants.mk _ x) = Submodule.Quotient.mk x := rfl

section
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {N : ℕ}
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)]
  {c : α → β' → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `leviProj_leviEmb k (f i) (q i)`.
-/
theorem relProj_relEmb (f : ∀ i, (Σ j, c i j) ≃ m i) (q : ∀ i, Levi k (c i))
    (hq : relEmb k f q ∈ relParab k f) : relProj k f ⟨relEmb k f q, hq⟩ = q := by
  funext i
  exact leviProj_leviEmb k (f i) (q i)

/- English proof (translation)
Introduce `i _` and use `leviEmb_mem_parab k (f i) (q i)`.
-/
theorem relEmb_mem_relParab (f : ∀ i, (Σ j, c i j) ≃ m i) (q : ∀ i, Levi k (c i)) :
    relEmb k f q ∈ relParab k f := fun i _ => leviEmb_mem_parab k (f i) (q i)

variable {k}

/- English proof (translation)
Establish `hδg : ∀ j i i' (t : c i j) (t' : c i' j), (β ∘ w) (e' ⟨j, g j ⟨i, t⟩⟩) < (β ∘ w) (e' ⟨j, g j ⟨i', t'⟩⟩) ↔ i < i'`. Introduce `j i i' t t'`. Simplify using `only [Function.comp, hcell, hβ, blk_apply]`. Establish `hδf : ∀ i j j' (t : c i j) (t' : c i j'), (γ ∘ ⇑w⁻¹) (e ⟨i, f i ⟨j, t⟩⟩) < (γ ∘ ⇑w⁻¹) (e ⟨i, f i ⟨j', t'⟩⟩) ↔ j < j'`. Introduce `i j j' t t'`.

Simplify using `only [Function.comp, ← hcell, Equiv.Perm.inv_def, Equiv.symm_apply_apply, hγ, blk_apply]`. Establish `hP : ∀ p, p ∈ relParab k g ↔ φ' p ∈ cellLeviSub k β γ w`. Introduce `p`. Rewrite using `[GlobalTheory.T.levi_refinement_block_order k e' g (β ∘ w) hδg p, Subgroup.mem_subgroupOf]`. Use `⟨fun h => ⟨(φ' p).2, by rw [hφ']; exact h⟩, fun h => ?_⟩` and prove the remaining obligations.

Use `h.2` as an intermediate fact. Rewrite `this` using `[hφ']`. Then use the resulting hypothesis. Establish `hU : ∀ u, u ∈ relUnip k f ↔ φ u ∈ leviUnipotent k N β (γ ∘ ⇑w⁻¹)`. Introduce `u`. Rewrite using `[GlobalTheory.T.levi_refinement_parabolic k e f (γ ∘ ⇑w⁻¹) hδf u, leviUnipotent, Subgroup.mem_subgroupOf, hφ]`.

Take `⟨hc, hc'⟩` from `GlobalTheory.T.levi_equiv_continuous k e' γ φ' hφ'`. Use `nonempty_indRep_comp_equiv φ' hc hc' (cellLeviSub k β γ w) (relParab k g) hP _ _ (coinvEquiv ρ φ (relUnip k f) (leviUnipotent k N β (γ ∘ ⇑w⁻¹)) hU) ?_` and prove the remaining obligations. Introduce `p v`. Take `⟨x, rfl⟩` from `Representation.Coinvariants.mk_surjective _ v`. Use `set b : cellLeviSub k β γ w := ⟨φ' p, (hP p.1).1 p.2⟩ with hbdef`.

Use `set q := relProj k g p with hq`. Use `set sq := swapBlocks k c q with hsq`. Establish `hbG : (((b : levi k N γ)) : GL (Fin N) k) = leviEmb k e' p.1` using `hφ' _`. Establish `hxm : permGL k w * leviEmb k e' p.1 * (permGL k w)⁻¹ ∈ blockUpper k N β`. Rewrite using `[← hbG]`.

Conclude with `(GroundTheory.Automorphic.Parabolic.permConj k β w ⟨_, b.2.2⟩).2`. Establish `hin : GroundTheory.Automorphic.Parabolic.leviInfIncl β (γ ∘ ⇑w⁻¹) (cellInnerHom β γ w (cellLeviSubIncl k β γ w b)) = φ (relEmb k f sq)`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hφ, ← GlobalTheory.T.levi_double_coset_intersection k e β hβ e' f g w hcell p.1 p.2 hxm]`. Use `show ((GroundTheory.Automorphic.Parabolic.leviProj k N β _ : levi k N β) : GL (Fin N) k) = _`.

Use `congr 2`. Conclude with `Subtype.ext (show permGL k w * (((b : levi k N γ)) : GL (Fin N) k) * (permGL k w)⁻¹ = _ by`. Rewrite using `[hbG])`. Establish `h4 : normLeviParSqrtModular k γ (β ∘ w) (cellLeviSubIncl k β γ w b) = ((relDeltaHalf k (fun j i => c i j) q : ℂˣ) : ℂ)` using `GlobalTheory.T.refined_block_order_compat k e' g γ (β ∘ w) hγ hδg (GlobalTheory.T.levi_refinement_block_order k e' g (β ∘ w) hδg) φ' hφ' p.1 p.2 b.2`. Establish `hmemh : ((φ (relEmb k f sq) : levi k N β) : GL (Fin N) k) ∈ leviPar k N β (γ ∘ ⇑w⁻¹)`.

Rewrite using `[← hin]`. Conclude with `(cellInnerHom β γ w (cellLeviSubIncl k β γ w b)).2`. Establish `h5 : normLeviParInvSqrtModular k β (γ ∘ ⇑w⁻¹) (cellInnerHom β γ w (cellLeviSubIncl k β γ w b)) = (((relDeltaHalf k c sq)⁻¹ : ℂˣ) : ℂ)`. Establish `h6` using `GlobalTheory.T.refined_block_order_compat k e f β (γ ∘ ⇑w⁻¹) hβ hδf (GlobalTheory.T.levi_refinement_block_order k e f (γ ∘ ⇑w⁻¹) hδf) φ hφ (relEmb k f sq) (relEmb_mem_relParab k f sq) hmemh`. Rewrite `h6` using `[relProj_relEmb]`.

Establish `h7 : cellInnerHom β γ w (cellLeviSubIncl k β γ w b) = ⟨((φ (relEmb k f sq) : levi k N β) : GL (Fin N) k), hmemh⟩` using `Subtype.ext (congrArg (fun z : levi k N β => (z : GL (Fin N) k)) hin)`. Use `show (normLeviParSqrtModular k β (γ ∘ ⇑w⁻¹) _)⁻¹ = _`. Rewrite using `[h7, h6, Units.val_inv_eq_inv_val]`. Establish `hact : (ρ.comp φ.symm.toMonoidHom) (GroundTheory.Automorphic.Parabolic.leviInfIncl β (γ ∘ ⇑w⁻¹) (cellInnerHom β γ w (cellLeviSubIncl k β γ w b))) x = ρ (relEmb k f sq) x`. Rewrite using `[hin]`.

Simplify using the standard rewrite rules. Establish `hL : (normInducing (ρ.comp φ.symm.toMonoidHom) γ w) b (Representation.Coinvariants.mk _ x) = normLeviParSqrtModular k γ (β ∘ w) (cellLeviSubIncl k β γ w b) • normLeviParInvSqrtModular k β (γ ∘ ⇑w⁻¹) (cellInnerHom β γ w (cellLeviSubIncl k β γ w b)) • Representation.Coinvariants.mk …` using `rfl`. Rewrite using `[hL, h4, h5, hact, map_smul, map_smul, coinvEquiv_mk]`. Both sides reduce to the same expression.
-/
theorem cell_equiv (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ m' j)
    (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ) (hβ : ∀ x y, β x < β y ↔ blk e x < blk e y)
    (φ : Levi k m ≃* levi k N β)
    (hφ : ∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g)
    (e' : (Σ j, m' j) ≃ Fin N) (γ : Fin N → ℕ) (hγ : ∀ x y, γ x < γ y ↔ blk e' x < blk e' y)
    (φ' : Levi k m' ≃* levi k N γ)
    (hφ' : ∀ g, ((φ' g : levi k N γ) : GL (Fin N) k) = leviEmb k e' g)
    {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W)
    (w : Equiv.Perm (Fin N))
    (hcell : ∀ i j (t : c i j), w (e' ⟨j, g j ⟨i, t⟩⟩) = e ⟨i, f i ⟨j, t⟩⟩) :
    Nonempty (Representation.Equiv
      ((indRep (cellLeviSub k β γ w) (normInducing (ρ.comp φ.symm.toMonoidHom) γ w)).comp
        φ'.toMonoidHom) (cellFunctor f g ρ)) := by
  have hδg : ∀ j i i' (t : c i j) (t' : c i' j),
      (β ∘ w) (e' ⟨j, g j ⟨i, t⟩⟩) < (β ∘ w) (e' ⟨j, g j ⟨i', t'⟩⟩) ↔ i < i' := by
    intro j i i' t t'
    simp only [Function.comp, hcell, hβ, blk_apply]
  have hδf : ∀ i j j' (t : c i j) (t' : c i j'),
      (γ ∘ ⇑w⁻¹) (e ⟨i, f i ⟨j, t⟩⟩) < (γ ∘ ⇑w⁻¹) (e ⟨i, f i ⟨j', t'⟩⟩) ↔ j < j' := by
    intro i j j' t t'
    simp only [Function.comp, ← hcell, Equiv.Perm.inv_def, Equiv.symm_apply_apply, hγ, blk_apply]
  have hP : ∀ p, p ∈ relParab k g ↔ φ' p ∈ cellLeviSub k β γ w := by
    intro p
    rw [GlobalTheory.T.levi_refinement_block_order k e' g (β ∘ w) hδg p, Subgroup.mem_subgroupOf]
    refine ⟨fun h => ⟨(φ' p).2, by rw [hφ']; exact h⟩, fun h => ?_⟩
    have := h.2
    rwa [hφ'] at this
  have hU : ∀ u, u ∈ relUnip k f ↔ φ u ∈ leviUnipotent k N β (γ ∘ ⇑w⁻¹) := by
    intro u
    rw [GlobalTheory.T.levi_refinement_parabolic k e f (γ ∘ ⇑w⁻¹) hδf u, leviUnipotent, Subgroup.mem_subgroupOf, hφ]
  obtain ⟨hc, hc'⟩ := GlobalTheory.T.levi_equiv_continuous k e' γ φ' hφ'
  refine nonempty_indRep_comp_equiv φ' hc hc' (cellLeviSub k β γ w) (relParab k g) hP _ _
    (coinvEquiv ρ φ (relUnip k f) (leviUnipotent k N β (γ ∘ ⇑w⁻¹)) hU) ?_
  intro p v
  obtain ⟨x, rfl⟩ := Representation.Coinvariants.mk_surjective _ v
  set b : cellLeviSub k β γ w := ⟨φ' p, (hP p.1).1 p.2⟩ with hbdef
  set q := relProj k g p with hq
  set sq := swapBlocks k c q with hsq
  have hbG : (((b : levi k N γ)) : GL (Fin N) k) = leviEmb k e' p.1 := hφ' _
  have hxm : permGL k w * leviEmb k e' p.1 * (permGL k w)⁻¹ ∈ blockUpper k N β := by
    rw [← hbG]
    exact (GroundTheory.Automorphic.Parabolic.permConj k β w ⟨_, b.2.2⟩).2
  have hin : GroundTheory.Automorphic.Parabolic.leviInfIncl β (γ ∘ ⇑w⁻¹)
      (cellInnerHom β γ w (cellLeviSubIncl k β γ w b)) = φ (relEmb k f sq) := by
    apply Subtype.ext
    rw [hφ, ← GlobalTheory.T.levi_double_coset_intersection k e β hβ e' f g w hcell p.1 p.2 hxm]
    show ((GroundTheory.Automorphic.Parabolic.leviProj k N β _ : levi k N β) : GL (Fin N) k) = _
    congr 2
    exact Subtype.ext (show permGL k w * (((b : levi k N γ)) : GL (Fin N) k) * (permGL k w)⁻¹ = _ by
      rw [hbG])
  have h4 : normLeviParSqrtModular k γ (β ∘ w) (cellLeviSubIncl k β γ w b) =
      ((relDeltaHalf k (fun j i => c i j) q : ℂˣ) : ℂ) :=
    GlobalTheory.T.refined_block_order_compat k e' g γ (β ∘ w) hγ hδg (GlobalTheory.T.levi_refinement_block_order k e' g (β ∘ w) hδg) φ' hφ'
      p.1 p.2 b.2
  have hmemh : ((φ (relEmb k f sq) : levi k N β) : GL (Fin N) k) ∈ leviPar k N β (γ ∘ ⇑w⁻¹) := by
    rw [← hin]
    exact (cellInnerHom β γ w (cellLeviSubIncl k β γ w b)).2
  have h5 : normLeviParInvSqrtModular k β (γ ∘ ⇑w⁻¹)
      (cellInnerHom β γ w (cellLeviSubIncl k β γ w b)) =
      (((relDeltaHalf k c sq)⁻¹ : ℂˣ) : ℂ) := by
    have h6 := GlobalTheory.T.refined_block_order_compat k e f β (γ ∘ ⇑w⁻¹) hβ hδf
      (GlobalTheory.T.levi_refinement_block_order k e f (γ ∘ ⇑w⁻¹) hδf) φ hφ (relEmb k f sq) (relEmb_mem_relParab k f sq)
      hmemh
    rw [relProj_relEmb] at h6
    have h7 : cellInnerHom β γ w (cellLeviSubIncl k β γ w b) =
        ⟨((φ (relEmb k f sq) : levi k N β) : GL (Fin N) k), hmemh⟩ :=
      Subtype.ext (congrArg (fun z : levi k N β => (z : GL (Fin N) k)) hin)
    show (normLeviParSqrtModular k β (γ ∘ ⇑w⁻¹) _)⁻¹ = _
    rw [h7, h6, Units.val_inv_eq_inv_val]
  have hact : (ρ.comp φ.symm.toMonoidHom) (GroundTheory.Automorphic.Parabolic.leviInfIncl β (γ ∘ ⇑w⁻¹)
      (cellInnerHom β γ w (cellLeviSubIncl k β γ w b))) x = ρ (relEmb k f sq) x := by
    rw [hin]
    simp
  have hL : (normInducing (ρ.comp φ.symm.toMonoidHom) γ w) b
      (Representation.Coinvariants.mk _ x) =
      normLeviParSqrtModular k γ (β ∘ w) (cellLeviSubIncl k β γ w b) •
        normLeviParInvSqrtModular k β (γ ∘ ⇑w⁻¹) (cellInnerHom β γ w (cellLeviSubIncl k β γ w b)) •
          Representation.Coinvariants.mk _ ((ρ.comp φ.symm.toMonoidHom)
            (GroundTheory.Automorphic.Parabolic.leviInfIncl β (γ ∘ ⇑w⁻¹)
              (cellInnerHom β γ w (cellLeviSubIncl k β γ w b))) x) := rfl
  rw [hL, h4, h5, hact, map_smul, map_smul, coinvEquiv_mk]
  rfl

end

/- English proof (translation)
Introduce `k _ _ _ _ α _ _ N m _ _ β' _ _ m' _ _ e β hβ φ hφ e' γ hγ φ' hφ' W _ _ ρ w`. Take `⟨f, g, hcell⟩` from `GlobalTheory.T.block_count_reindex_equivs e e' w`. Conclude with `⟨f, g, cell_equiv f g e β hβ φ hφ e' γ hγ φ' hφ' ρ w hcell⟩`.
-/
theorem cell_iso : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β), (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) → ∀ (e' : (Σ j, m' j) ≃ Fin N) (γ : Fin N → ℕ), (∀ x y, γ x < γ y ↔ blk e' x < blk e' y) → ∀ (φ' : Levi k m' ≃* levi k N γ), (∀ g, ((φ' g : levi k N γ) : GL (Fin N) k) = leviEmb k e' g) → ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W) (w : Equiv.Perm (Fin N)), ∃ (f : ∀ i, (Σ j, Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card)) ≃ m i) (g : ∀ j, (Σ i, Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card)) ≃ m' j), Nonempty (Representation.Equiv ((indRep (cellLeviSub k β γ w) (normInducing (ρ.comp φ.symm.toMonoidHom) γ w)).comp φ'.toMonoidHom) (cellFunctor f g ρ)) := by
  intro k _ _ _ _ α _ _ N m _ _ β' _ _ m' _ _ e β hβ φ hφ e' γ hγ φ' hφ' W _ _ ρ w
  obtain ⟨f, g, hcell⟩ := GlobalTheory.T.block_count_reindex_equivs e e' w
  exact ⟨f, g, cell_equiv f g e β hβ φ hφ e' γ hγ φ' hφ' ρ w hcell⟩

end GlobalTheory.CompanionTheory.GeomCell
