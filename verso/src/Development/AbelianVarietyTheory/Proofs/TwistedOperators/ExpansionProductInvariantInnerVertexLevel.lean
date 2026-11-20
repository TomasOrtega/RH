import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColMapEqColMapV
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmEqSumLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaAtOfVac
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdPartialEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnArrowRealAverageHoweDualityFockComponentStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacMoveHigh
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingExpansionProductFunctionLocalInvariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance

/- English proof (translation)
Introduce `D T L sc G W U S t Φ β τ μ₀ hL₀ hde hcc ht hβ hexp hvec j hj k hk w z`. Establish `hexp'` using `hexp`. Take `⟨e, he, hsupp, -⟩` from `hexp`. Distinguish the cases in `hτ : τ = 0`. Substitute `hτ` using the available equality.

Simplify using the standard rewrite rules. Choose the witnesses or unpack the hypotheses as in `⟨d₀, hd₀⟩ : ∃ d, d ∈ τ.support := by`. Take `⟨d, hd⟩` from `Finsupp.ne_iff.1 hτ`. Conclude with `⟨d, Finsupp.mem_support_iff.2 (by simpa using hd)⟩`. Establish `hmc : ∀ j' : Fin D.R.m, ∃ Tm, IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t j')) 1 (S.Z.vac (.top t j')) Tm` using `fun j' => by`.

Take `⟨f, hf⟩` from `(hvec d₀ hd₀).1 j'`. Take `⟨Tm, hTm⟩` from `hf.1`. Use `⟨Tm, ?_⟩` and prove the remaining obligations. Rewrite using `[← ((hsupp d₀ hd₀).1 j').2.1]`. Conclude with `hTm`.

Establish `hmr : ∀ i : Fin D.R.m, ∃ Tm, IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.chi i D.R.m)) 1 (S.Z.vac (.chi i D.R.m)) Tm` using `fun i => by`. Take `⟨f, hf⟩` from `(hvec d₀ hd₀).2 i`. Take `⟨Tm, hTm⟩` from `hf.1`. Use `⟨Tm, ?_⟩` and prove the remaining obligations. Rewrite using `[← ((hsupp d₀ hd₀).2 i).2.1]`.

Conclude with `hTm`. Use `choose Tc hTc using hmc`. Use `choose Tr hTr using hmr`. Establish `hvc : ∀ d ∈ τ.support, ∀ j', S.Z.vec (d.1 j') = Tc j' (d.1 j').fn` using `fun d hd j' => vec_eq_model S _ ((hsupp d hd).1 j').2.2 ((hvec d hd).1 j') _ (by rw [((hsupp d hd).1 j').2.1]; exact hTc j')`. Establish `hvr : ∀ d ∈ τ.support, ∀ i, S.Z.vec (d.2 i) = Tr i (d.2 i).fn` using `fun d hd i => vec_eq_model S _ ((hsupp d hd).2 i).2.2 ((hvec d hd).2 i) _ (by rw [((hsupp d hd).2 i).2.1]; exact hTr i)`.

Use `set g : FinPt G (.top (j + 1)) := (S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) with hg`. Take `⟨c₁, hc₁⟩` from `GlobalTheory.T.columnArrow_realAverage_howeDuality_fockComponent S ht j hj k hk e he (Tc ⟨j, by omega⟩) (hTc ⟨j, by omega⟩)`. Take `⟨c₂, hc₂⟩` from `vac_move_high S ht j hj k hk e he (Tc ⟨j + 1, hj⟩) (hTc ⟨j + 1, hj⟩)`. Establish `hla : ∀ X : Node, DefNode D.R.m X → (∀ i, X ≠ .grid 0 i) → X.InRange D.R.m → Submodule.IsLattice D.host.E (G.Λ X)` using `fun X _ h0 hX => (G.isV hX h0).sd.1`. Establish `hsb : ∀ d ∈ τ.support, ∀ j' : Fin D.R.m, IsSBHalf e (stdLatO S (.top t j')) (d.1 j').fn` using `fun d hd j' => by`.

Establish `h1` using `(d.1 j').sb`. Rewrite `h1` using `[((hsupp d hd).1 j').2.1]`. Conclude with `VecEx.isSBHalf_of_lattices (hla (.top j') (by show (j' : ℕ) ≤ D.R.m; omega) (by simp) (by show (j' : ℕ) ≤ D.R.m; omega)) (hla (.top (j' + 1)) (by show (j' : ℕ) + 1 ≤ D.R.m; omega) (by simp) (by show (j' : ℕ) + 1 ≤ D.R.m; omega)) (S.N.selfDual (X := .top j') (by show (j' : ℕ) ≤ D. …`. Establish `hmv : ∀ d ∈ τ.support, ∀ j', movedCol S d j hj g j' = (Function.update (Function.update (1 : Fin D.R.m → ℂ) ⟨j, by omega⟩ c₁) ⟨j + 1, hj⟩ c₂ j') • Tc j' (movedFn S d j hj g j')` using `fun d hd j' => by`. Break down `eq_or_ne j' ⟨j + 1, hj⟩ with rfl | h1` into its components or cases.

Simplify using `only [movedCol, movedFn, Function.update_self]`. Rewrite using `[hvc d hd]`. Conclude with `GlobalTheory.SplitLinear.om_model_of_base D W.ψ _ _ _ _ _ (S.N.latS (.top t (j + 1))) (S.N.latT (.top t (j + 1))) e (S.Z.vac (.top t (j + 1))) _ (W.om_is (.top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega)) (S.N.selfDual (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega)) (S.N.self …`. Break down `eq_or_ne j' ⟨j, by omega⟩ with rfl | h2` into its components or cases. Simplify using `only [movedCol, movedFn, Function.update_of_ne h1, Function.update_self]`.

Rewrite using `[hvc d hd]`. Conclude with `GlobalTheory.SplitLinear.om_model_of_base D W.ψ _ _ _ _ _ (S.N.latS (.top t j)) (S.N.latT (.top t j)) e (S.Z.vac (.top t j)) _ (W.om_is (.top t j) (show j + 1 ≤ D.R.m by omega)) (S.N.selfDual (X := .top j) (show j ≤ D.R.m by omega)) (S.N.selfDual (X := .top (j + 1)) (show j + 1 ≤ …`. Simplify using `only [movedCol, movedFn, Function.update_of_ne h1, Function.update_of_ne h2, Pi.one_apply, one_smul]`. Conclude with `hvc d hd j'`. Establish `hprod : ∏ j' : Fin D.R.m, Function.update (Function.update (1 : Fin D.R.m → ℂ) ⟨j, by omega⟩ c₁) ⟨j + 1, hj⟩ c₂ j' = c₁ * c₂`.

Establish `hne : (⟨j, by omega⟩ : Fin D.R.m) ≠ ⟨j + 1, hj⟩` using `fun h => by simp [Fin.ext_iff] at h`. Rewrite using `[Finset.prod_update_of_mem (Finset.mem_univ _), Finset.prod_update_of_mem (by simp [hne])]`. Simplify using `only [Pi.one_apply, Finset.prod_const_one, mul_one]`. Expand and normalize the polynomial expressions, which then agree. Set `X : Fin D.R.m ⊕ Fin D.R.m → Type` to `Sum.elim (fun j' => WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T))) fun i => WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))`.

Set `Tt : ∀ a, (X a → ℂ) →ₗ[ℂ] (X a → ℂ)` to `fun a => match a with`. Consider the case `.inl j' => Tc j'`. Consider the case `.inr i => Tr i`. Set `F : PureDat G t → ∀ a, X a → ℂ` to `fun d a => match a with`. Consider the case `.inl j' => (d.1 j').fn`.

Consider the case `.inr i => (d.2 i).fn`. Set `F' : PureDat G t → ∀ a, X a → ℂ` to `fun d a => match a with`. Consider the case `.inl j' => movedFn S d j hj g j'`. Consider the case `.inr i => (d.2 i).fn`. Set `yy : ∀ a, X a` to `fun a => match a with`.

Consider the case `.inl j' => w j'`. Consider the case `.inr i => z i`. Establish `key` using `sum_prod_map_congr Tt τ.support τ.support (fun d => τ d) (fun d => τ d * (c₁ * c₂)) F F' (fun x => by`. Use `GlobalTheory.T.unfoldingExpansion_productFunction_localInvariant S hL₀ hde hcc ht hβ hexp' j hj k hk e he (fun d hd j' => ((hsupp d hd).1 j').2.1) _ _ (hTc ⟨j, by omega⟩) (hTc ⟨j + 1, hj⟩) c₁ c₂ hc₁ hc₂ (fun j' => x (.inl j')) (fun i => x (.inr i))` as an intermediate fact. Simplify using `only [Finsupp.sum] at this`.

Simplify using `only [Fintype.prod_sum_type]`. Use `(Finset.sum_congr rfl fun d _ => ?_).trans (this.trans (Finset.sum_congr rfl fun d _ => ?_))` and prove the remaining obligations. Conclude with `(mul_assoc _ _ _).symm`. Conclude with `mul_assoc _ _ _) yy`. Simplify using `only [Fintype.prod_sum_type] at key`.

Establish `hL : (∑ d ∈ τ.support, τ d * (∏ j', movedCol S d j hj g j' (w j')) * ∏ i, S.Z.vec (d.2 i) (z i)) = ∑ d ∈ τ.support, τ d * (c₁ * c₂) * ((∏ j', Tc j' (movedFn S d j hj g j') (w j')) * ∏ i, Tr i (d.2 i).fn (z i))` using `Finset.sum_congr rfl fun d hd => by`. Simplify using `only [hmv d hd, hvr d hd, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, hprod]`. Expand and normalize the polynomial expressions, which then agree. Establish `hR : (∑ d ∈ τ.support, τ d * (∏ j', S.Z.vec (d.1 j') (w j')) * ∏ i, S.Z.vec (d.2 i) (z i)) = ∑ d ∈ τ.support, τ d * ((∏ j', Tc j' (d.1 j').fn (w j')) * ∏ i, Tr i (d.2 i).fn (z i))` using `Finset.sum_congr rfl fun d hd => by simp only [hvc d hd, hvr d hd]; ring`. Simplify using `only [Finsupp.sum]`.

Rewrite using `[hL, hR]`. Conclude with `key`.
-/
theorem product_invariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}
    {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) →
    (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))), finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj →
    ∀ (w : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)))
      (z : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (τ.sum fun d a => a * (∏ j', movedCol S d j hj ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))) j' (w j')) *
          ∏ i, S.Z.vec (d.2 i) (z i)) =
        τ.sum fun d a => a * (∏ j', S.Z.vec (d.1 j') (w j')) * ∏ i, S.Z.vec (d.2 i) (z i) := by
  intro D T L sc G W U S t Φ β τ μ₀ hL₀ hde hcc ht hβ hexp hvec j hj k hk w z
  classical
  have hexp' := hexp
  obtain ⟨e, he, hsupp, -⟩ := hexp
  by_cases hτ : τ = 0
  · subst hτ; simp
  obtain ⟨d₀, hd₀⟩ : ∃ d, d ∈ τ.support := by
    obtain ⟨d, hd⟩ := Finsupp.ne_iff.1 hτ
    exact ⟨d, Finsupp.mem_support_iff.2 (by simpa using hd)⟩
  have hmc : ∀ j' : Fin D.R.m, ∃ Tm, IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t j')) 1
      (S.Z.vac (.top t j')) Tm := fun j' => by
    obtain ⟨f, hf⟩ := (hvec d₀ hd₀).1 j'
    obtain ⟨Tm, hTm⟩ := hf.1
    refine ⟨Tm, ?_⟩
    rw [← ((hsupp d₀ hd₀).1 j').2.1]
    exact hTm
  have hmr : ∀ i : Fin D.R.m, ∃ Tm, IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.chi i D.R.m)) 1
      (S.Z.vac (.chi i D.R.m)) Tm := fun i => by
    obtain ⟨f, hf⟩ := (hvec d₀ hd₀).2 i
    obtain ⟨Tm, hTm⟩ := hf.1
    refine ⟨Tm, ?_⟩
    rw [← ((hsupp d₀ hd₀).2 i).2.1]
    exact hTm
  choose Tc hTc using hmc
  choose Tr hTr using hmr
  have hvc : ∀ d ∈ τ.support, ∀ j', S.Z.vec (d.1 j') = Tc j' (d.1 j').fn := fun d hd j' =>
    vec_eq_model S _ ((hsupp d hd).1 j').2.2 ((hvec d hd).1 j') _ (by rw [((hsupp d hd).1 j').2.1]; exact hTc j')
  have hvr : ∀ d ∈ τ.support, ∀ i, S.Z.vec (d.2 i) = Tr i (d.2 i).fn := fun d hd i =>
    vec_eq_model S _ ((hsupp d hd).2 i).2.2 ((hvec d hd).2 i) _ (by rw [((hsupp d hd).2 i).2.1]; exact hTr i)
  set g : FinPt G (.top (j + 1)) := (S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) with hg
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.columnArrow_realAverage_howeDuality_fockComponent S ht j hj k hk e he (Tc ⟨j, by omega⟩) (hTc ⟨j, by omega⟩)
  obtain ⟨c₂, hc₂⟩ := vac_move_high S ht j hj k hk e he (Tc ⟨j + 1, hj⟩) (hTc ⟨j + 1, hj⟩)
  have hla : ∀ X : Node, DefNode D.R.m X → (∀ i, X ≠ .grid 0 i) → X.InRange D.R.m →
      Submodule.IsLattice D.host.E (G.Λ X) := fun X _ h0 hX => (G.isV hX h0).sd.1
  have hsb : ∀ d ∈ τ.support, ∀ j' : Fin D.R.m, IsSBHalf e (stdLatO S (.top t j')) (d.1 j').fn := fun d hd j' => by
    have h1 := (d.1 j').sb
    rw [((hsupp d hd).1 j').2.1] at h1
    exact VecEx.isSBHalf_of_lattices (hla (.top j') (by show (j' : ℕ) ≤ D.R.m; omega) (by simp)
        (by show (j' : ℕ) ≤ D.R.m; omega))
      (hla (.top (j' + 1)) (by show (j' : ℕ) + 1 ≤ D.R.m; omega) (by simp) (by show (j' : ℕ) + 1 ≤ D.R.m; omega))
      (S.N.selfDual (X := .top j') (by show (j' : ℕ) ≤ D.R.m; omega)).1
      (S.N.selfDual (X := .top (j' + 1)) (by show (j' : ℕ) + 1 ≤ D.R.m; omega)).1
      (GlobalTheory.PlaceDatum.infPart_idemSum he) h1
  have hmv : ∀ d ∈ τ.support, ∀ j', movedCol S d j hj g j' =
      (Function.update (Function.update (1 : Fin D.R.m → ℂ) ⟨j, by omega⟩ c₁) ⟨j + 1, hj⟩ c₂ j') •
        Tc j' (movedFn S d j hj g j') := fun d hd j' => by
    rcases eq_or_ne j' ⟨j + 1, hj⟩ with rfl | h1
    · simp only [movedCol, movedFn, Function.update_self]
      rw [hvc d hd]
      exact GlobalTheory.SplitLinear.om_model_of_base D W.ψ _ _ _ _ _ (S.N.latS (.top t (j + 1))) (S.N.latT (.top t (j + 1))) e
        (S.Z.vac (.top t (j + 1))) _ (W.om_is (.top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega))
        (S.N.selfDual (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega))
        (S.N.selfDual (X := .top (j + 1 + 1)) (show j + 1 + 1 ≤ D.R.m by omega))
        (GlobalTheory.PlaceDatum.idemSum_mul_self he) (GlobalTheory.PlaceDatum.infPart_idemSum he)
        (S.Z.vac_is (.top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega)).2.theta (hTc ⟨j + 1, hj⟩) _ _ c₂ hc₂ _ (hsb d hd ⟨j + 1, hj⟩)
    rcases eq_or_ne j' ⟨j, by omega⟩ with rfl | h2
    · simp only [movedCol, movedFn, Function.update_of_ne h1, Function.update_self]
      rw [hvc d hd]
      exact GlobalTheory.SplitLinear.om_model_of_base D W.ψ _ _ _ _ _ (S.N.latS (.top t j)) (S.N.latT (.top t j)) e
        (S.Z.vac (.top t j)) _ (W.om_is (.top t j) (show j + 1 ≤ D.R.m by omega))
        (S.N.selfDual (X := .top j) (show j ≤ D.R.m by omega))
        (S.N.selfDual (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega))
        (GlobalTheory.PlaceDatum.idemSum_mul_self he) (GlobalTheory.PlaceDatum.infPart_idemSum he)
        (S.Z.vac_is (.top t j) (show j + 1 ≤ D.R.m by omega)).2.theta (hTc ⟨j, by omega⟩) _ _ c₁ hc₁ _ (hsb d hd ⟨j, by omega⟩)
    · simp only [movedCol, movedFn, Function.update_of_ne h1, Function.update_of_ne h2, Pi.one_apply, one_smul]
      exact hvc d hd j'
  have hprod : ∏ j' : Fin D.R.m, Function.update (Function.update (1 : Fin D.R.m → ℂ) ⟨j, by omega⟩ c₁) ⟨j + 1, hj⟩ c₂ j' =
      c₁ * c₂ := by
    have hne : (⟨j, by omega⟩ : Fin D.R.m) ≠ ⟨j + 1, hj⟩ := fun h => by simp [Fin.ext_iff] at h
    rw [Finset.prod_update_of_mem (Finset.mem_univ _), Finset.prod_update_of_mem (by simp [hne])]
    simp only [Pi.one_apply, Finset.prod_const_one, mul_one]
    ring
  let X : Fin D.R.m ⊕ Fin D.R.m → Type := Sum.elim (fun j' => WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)))
    fun i => WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))
  let Tt : ∀ a, (X a → ℂ) →ₗ[ℂ] (X a → ℂ) := fun a => match a with
    | .inl j' => Tc j'
    | .inr i => Tr i
  let F : PureDat G t → ∀ a, X a → ℂ := fun d a => match a with
    | .inl j' => (d.1 j').fn
    | .inr i => (d.2 i).fn
  let F' : PureDat G t → ∀ a, X a → ℂ := fun d a => match a with
    | .inl j' => movedFn S d j hj g j'
    | .inr i => (d.2 i).fn
  let yy : ∀ a, X a := fun a => match a with
    | .inl j' => w j'
    | .inr i => z i
  have key := sum_prod_map_congr Tt τ.support τ.support (fun d => τ d) (fun d => τ d * (c₁ * c₂)) F F' (fun x => by
    have := GlobalTheory.T.unfoldingExpansion_productFunction_localInvariant S hL₀ hde hcc ht hβ hexp' j hj k hk e he (fun d hd j' => ((hsupp d hd).1 j').2.1) _ _ (hTc ⟨j, by omega⟩)
      (hTc ⟨j + 1, hj⟩) c₁ c₂ hc₁ hc₂ (fun j' => x (.inl j')) (fun i => x (.inr i))
    simp only [Finsupp.sum] at this
    simp only [Fintype.prod_sum_type]
    refine (Finset.sum_congr rfl fun d _ => ?_).trans (this.trans (Finset.sum_congr rfl fun d _ => ?_))
    · exact (mul_assoc _ _ _).symm
    · exact mul_assoc _ _ _) yy
  simp only [Fintype.prod_sum_type] at key
  have hL : (∑ d ∈ τ.support, τ d * (∏ j', movedCol S d j hj g j' (w j')) * ∏ i, S.Z.vec (d.2 i) (z i)) =
      ∑ d ∈ τ.support, τ d * (c₁ * c₂) * ((∏ j', Tc j' (movedFn S d j hj g j') (w j')) * ∏ i, Tr i (d.2 i).fn (z i)) :=
    Finset.sum_congr rfl fun d hd => by
      simp only [hmv d hd, hvr d hd, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, hprod]; ring
  have hR : (∑ d ∈ τ.support, τ d * (∏ j', S.Z.vec (d.1 j') (w j')) * ∏ i, S.Z.vec (d.2 i) (z i)) =
      ∑ d ∈ τ.support, τ d * ((∏ j', Tc j' (d.1 j').fn (w j')) * ∏ i, Tr i (d.2 i).fn (z i)) :=
    Finset.sum_congr rfl fun d hd => by simp only [hvc d hd, hvr d hd]; ring
  simp only [Finsupp.sum]
  rw [hL, hR]
  exact key

end GlobalTheory.ExpansionInvariance

end
