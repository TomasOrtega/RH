import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDetResMat
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.FrobeniusFixedBasis

variable {F K M : Type} [Field F] [Field K] [Algebra F K] [AddCommGroup M] [Module K M] [Module F M]
  [IsScalarTower F K M]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun q e m => by show ((q • e : E) : K) • m = q • ((e : K) • m) rw [IntermediateField.coe_smul, smul_assoc]⟩`.
-/
theorem isScalarTower_sub (E : IntermediateField F K) : IsScalarTower F E M :=
  ⟨fun q e m => by
    show ((q • e : E) : K) • m = q • ((e : K) • m)
    rw [IntermediateField.coe_smul, smul_assoc]⟩

/- English proof (translation)
Use `haveI := isScalarTower_sub (M := M) E`. Use `set V := Submodule.span F (Set.range v) with hVdef`. Establish `hstab : ∀ e ∈ E, ∀ x ∈ V, e • x ∈ V`. Introduce `e he x hx`. Establish `hle : V ≤ V.comap ((LinearMap.lsmul K M e).restrictScalars F)`.

Rewrite using `[hVdef, Submodule.span_le]`. Introduce and unpack `_ ⟨c, rfl⟩`. Conclude with `hst e he c`. Conclude with `hle hx`. Set `VE : Submodule E M` to `{ carrier := V add_mem' := fun hx hy => V.add_mem hx hy zero_mem' := V.zero_mem smul_mem' := fun e x hx => hstab (e : K) e.2 x hx }`.

Establish `hfinV : Module.finrank F V = Fintype.card n * r`. Rewrite using `[hVdef, finrank_span_eq_card hv, Fintype.card_prod, Fintype.card_fin]`. Set `e1 : VE ≃ₗ[F] V` to `{ toFun := fun x => ⟨x.1, x.2⟩ invFun := fun x => ⟨x.1, x.2⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl left_inv := fun _ => rfl right_inv := fun _ => rfl }`. Establish `hfinVE : Module.finrank F VE = Fintype.card n * r`. Rewrite using `[← hfinV]`.

Conclude with `e1.finrank_eq`. Use `haveI : Module.Finite F V := by`. Rewrite using `[hVdef]`. Conclude with `FiniteDimensional.span_of_finite F (Set.finite_range v)`. Use `haveI : Module.Finite F VE := Module.Finite.equiv e1.symm`.

Use `haveI : Module.Finite E VE := Module.Finite.of_restrictScalars_finite F E VE`. Establish `hE : Module.finrank F E = r`. Rewrite using `[Module.finrank_eq_card_basis bω, Fintype.card_fin]`. Use `haveI : Module.Finite F E := Module.Finite.of_basis bω`. Establish `hrpos : 0 < r`.

Rewrite using `[← hE]`. Conclude with `Module.finrank_pos`. Establish `htower` using `Module.finrank_mul_finrank F E VE`. Rewrite `htower` using `[hE, hfinVE]`. Establish `hnE : Module.finrank E VE = Fintype.card n`.

Establish `: Module.finrank E VE * r = Fintype.card n * r` using `by rw [mul_comm]; exact htower`. Conclude with `Nat.eq_of_mul_eq_mul_right hrpos this`. Set `b : Module.Basis n E VE` to `(Module.finBasisOfFinrankEq E VE hnE).reindex (Fintype.equivFin n).symm`. Set `bt : Module.Basis (Fin r × n) F VE` to `bω.smulTower b`. Set `f : VE →ₗ[F] M` to `(VE.subtype).restrictScalars F`.

Establish `hf : Function.Injective f` using `Subtype.val_injective`. Use `⟨fun j => (b j : M), fun j => (b j).2, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : LinearIndependent F (f ∘ bt)` using `bt.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)`. Establish `h2` using `h1.comp (Equiv.prodComm n (Fin r)) (Equiv.injective _)`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `jk`. Simplify using `only [Function.comp_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, bt, Module.Basis.smulTower_apply, f]`. Both sides reduce to the same expression. Establish `hli : LinearIndependent F (fun jk : n × Fin r => ((bω jk.2 : E) : K) • (b jk.1 : M))`. Establish `h1 : LinearIndependent F (f ∘ bt)` using `bt.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)`.

Establish `h2` using `h1.comp (Equiv.prodComm n (Fin r)) (Equiv.injective _)`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `jk`. Simplify using `only [Function.comp_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, bt, Module.Basis.smulTower_apply, f]`. Both sides reduce to the same expression.

Apply `Submodule.eq_of_le_of_finrank_eq` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨jk, rfl⟩`. Conclude with `hstab _ (bω jk.2).2 _ (b jk.1).2`. Rewrite using `[finrank_span_eq_card hli, hfinV, Fintype.card_prod, Fintype.card_fin]`.
-/
theorem exists_tower_basis (E : IntermediateField F K) {r : ℕ} (bω : Module.Basis (Fin r) F E)
    (n : Type) [Fintype n] [DecidableEq n] (v : n × Fin r → M) (hv : LinearIndependent F v)
    (hst : ∀ e ∈ E, ∀ c, e • v c ∈ Submodule.span F (Set.range v)) :
    ∃ a : n → M, (∀ j, a j ∈ Submodule.span F (Set.range v)) ∧
      LinearIndependent F (fun jk : n × Fin r => ((bω jk.2 : E) : K) • a jk.1) ∧
      Submodule.span F (Set.range fun jk : n × Fin r => ((bω jk.2 : E) : K) • a jk.1) =
        Submodule.span F (Set.range v) := by
  haveI := isScalarTower_sub (M := M) E
  set V := Submodule.span F (Set.range v) with hVdef
  have hstab : ∀ e ∈ E, ∀ x ∈ V, e • x ∈ V := by
    intro e he x hx
    have hle : V ≤ V.comap ((LinearMap.lsmul K M e).restrictScalars F) := by
      rw [hVdef, Submodule.span_le]
      rintro _ ⟨c, rfl⟩
      exact hst e he c
    exact hle hx
  let VE : Submodule E M :=
    { carrier := V
      add_mem' := fun hx hy => V.add_mem hx hy
      zero_mem' := V.zero_mem
      smul_mem' := fun e x hx => hstab (e : K) e.2 x hx }
  have hfinV : Module.finrank F V = Fintype.card n * r := by
    rw [hVdef, finrank_span_eq_card hv, Fintype.card_prod, Fintype.card_fin]
  let e1 : VE ≃ₗ[F] V :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hfinVE : Module.finrank F VE = Fintype.card n * r := by
    rw [← hfinV]; exact e1.finrank_eq
  haveI : Module.Finite F V := by
    rw [hVdef]; exact FiniteDimensional.span_of_finite F (Set.finite_range v)
  haveI : Module.Finite F VE := Module.Finite.equiv e1.symm
  haveI : Module.Finite E VE := Module.Finite.of_restrictScalars_finite F E VE
  have hE : Module.finrank F E = r := by
    rw [Module.finrank_eq_card_basis bω, Fintype.card_fin]
  haveI : Module.Finite F E := Module.Finite.of_basis bω
  have hrpos : 0 < r := by
    rw [← hE]; exact Module.finrank_pos
  have htower := Module.finrank_mul_finrank F E VE
  rw [hE, hfinVE] at htower
  have hnE : Module.finrank E VE = Fintype.card n := by
    have : Module.finrank E VE * r = Fintype.card n * r := by rw [mul_comm]; exact htower
    exact Nat.eq_of_mul_eq_mul_right hrpos this
  let b : Module.Basis n E VE := (Module.finBasisOfFinrankEq E VE hnE).reindex (Fintype.equivFin n).symm
  let bt : Module.Basis (Fin r × n) F VE := bω.smulTower b
  let f : VE →ₗ[F] M := (VE.subtype).restrictScalars F
  have hf : Function.Injective f := Subtype.val_injective
  refine ⟨fun j => (b j : M), fun j => (b j).2, ?_, ?_⟩
  · have h1 : LinearIndependent F (f ∘ bt) := bt.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
    have h2 := h1.comp (Equiv.prodComm n (Fin r)) (Equiv.injective _)
    convert h2 using 1
    funext jk
    simp only [Function.comp_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, bt, Module.Basis.smulTower_apply, f]
    rfl
  · have hli : LinearIndependent F (fun jk : n × Fin r => ((bω jk.2 : E) : K) • (b jk.1 : M)) := by
      have h1 : LinearIndependent F (f ∘ bt) := bt.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
      have h2 := h1.comp (Equiv.prodComm n (Fin r)) (Equiv.injective _)
      convert h2 using 1
      funext jk
      simp only [Function.comp_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, bt, Module.Basis.smulTower_apply, f]
      rfl
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨jk, rfl⟩
      exact hstab _ (bω jk.2).2 _ (b jk.1).2
    · rw [finrank_span_eq_card hli, hfinV, Fintype.card_prod, Fintype.card_fin]

end GlobalTheory.FrobeniusFixedBasis

namespace GlobalTheory.FrobeniusFixedBasis

def frFixed (l : ℕ) [Fact l.Prime] (r : ℕ) : IntermediateField ℚ_[l] ↥(MaximalUnramifiedExtension l) where
  carrier := {c | fr l r c = c}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, ha, hb]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_add, ha, hb]
  algebraMap_mem' := fun q => by
    show (frobUr l ^ r) (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q) = _
    exact AlgHom.commutes _ q
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at *
    rw [map_inv₀, hx]

end GlobalTheory.FrobeniusFixedBasis

namespace GlobalTheory

open GlobalTheory.FrobeniusFixedBasis in

/- English proof (translation)
Introduce `l _ r ω hω hli hsp M _ _ _ _ n _ _ v hv hst`. Set `E` to `frFixed l r`. Set `ω' : Fin r → E` to `fun k => ⟨ω k, hω k⟩`. Establish `hli' : LinearIndependent ℚ_[l] ω'`. Apply `LinearIndependent.of_comp (E.val.toLinearMap)` to reduce the goal to its premises.

Conclude with `hli`. Establish `hsp' : ⊤ ≤ Submodule.span ℚ_[l] (Set.range ω')`. Introduce and unpack `⟨c, hc⟩ _`. Take `⟨a, ha⟩` from `hsp c hc`. Establish `: (⟨c, hc⟩ : E) = ∑ k, a k • ω' k`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show c = ((∑ k, a k • ω' k : E) : ↥(MaximalUnramifiedExtension l))`. Rewrite using `[ha]`. Simplify using `[ω']`. Rewrite using `[this]`.

Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`. Set `bω : Module.Basis (Fin r) ℚ_[l] E` to `Module.Basis.mk hli' hsp'`. Take `⟨a, ha1, ha2, ha3⟩` from `exists_tower_basis E bω n v hv (fun e he c => hst e he c)`. Establish `hb : ∀ k, ((bω k : E) : ↥(MaximalUnramifiedExtension l)) = ω k` using `fun k => by`. Simplify using `[bω, ω', Module.Basis.mk_apply]`.

Simplify using `only [hb] at ha2 ha3`. Conclude with `⟨a, ha1, ha2, ha3⟩`.
-/
theorem exists_frFixed_tower_basis : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) →
    LinearIndependent ℚ_[l] ω → (∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → ∃ a : Fin r → ℚ_[l], c = ∑ k, a k • ω k) →
    ∀ (M : Type) [AddCommGroup M] [Module ↥(MaximalUnramifiedExtension l) M] [Module ℚ_[l] M] [IsScalarTower ℚ_[l] ↥(MaximalUnramifiedExtension l) M] (n : Type)
      [Fintype n] [DecidableEq n] (v : n × Fin r → M), LinearIndependent ℚ_[l] v →
      (∀ e : ↥(MaximalUnramifiedExtension l), fr l r e = e → ∀ c, e • v c ∈ Submodule.span ℚ_[l] (Set.range v)) →
      ∃ a : n → M, (∀ j, a j ∈ Submodule.span ℚ_[l] (Set.range v)) ∧
        LinearIndependent ℚ_[l] (fun jk : n × Fin r => ω jk.2 • a jk.1) ∧
        Submodule.span ℚ_[l] (Set.range fun jk : n × Fin r => ω jk.2 • a jk.1) = Submodule.span ℚ_[l] (Set.range v) := by
  intro l _ r ω hω hli hsp M _ _ _ _ n _ _ v hv hst
  let E := frFixed l r
  let ω' : Fin r → E := fun k => ⟨ω k, hω k⟩
  have hli' : LinearIndependent ℚ_[l] ω' := by
    apply LinearIndependent.of_comp (E.val.toLinearMap)
    exact hli
  have hsp' : ⊤ ≤ Submodule.span ℚ_[l] (Set.range ω') := by
    rintro ⟨c, hc⟩ _
    obtain ⟨a, ha⟩ := hsp c hc
    have : (⟨c, hc⟩ : E) = ∑ k, a k • ω' k := by
      apply Subtype.ext
      show c = ((∑ k, a k • ω' k : E) : ↥(MaximalUnramifiedExtension l))
      rw [ha]
      simp [ω']
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let bω : Module.Basis (Fin r) ℚ_[l] E := Module.Basis.mk hli' hsp'
  obtain ⟨a, ha1, ha2, ha3⟩ := exists_tower_basis E bω n v hv (fun e he c => hst e he c)
  have hb : ∀ k, ((bω k : E) : ↥(MaximalUnramifiedExtension l)) = ω k := fun k => by
    simp [bω, ω', Module.Basis.mk_apply]
  simp only [hb] at ha2 ha3
  exact ⟨a, ha1, ha2, ha3⟩

end GlobalTheory
