import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MultiProdCompCongr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MultiProdHeadComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTwoBlocksEmptyProductLeftStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InducedProductCommutesFamilyProductStatement
import BuildAid.D3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ProdReorder

section Eqv

variable {G V W U : Type} [Monoid G] [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]
  [AddCommMonoid U] [Module ℂ U] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {τ : Representation ℂ G U}

/- English proof (translation)
The claim follows from `h₁.elim fun a => h₂.elim fun b => ⟨a.trans b⟩`.
-/
theorem eqvT (h₁ : Nonempty (ρ.Equiv σ)) (h₂ : Nonempty (σ.Equiv τ)) : Nonempty (ρ.Equiv τ) :=
  h₁.elim fun a => h₂.elim fun b => ⟨a.trans b⟩

/- English proof (translation)
The claim follows from `h.map Representation.Equiv.symm`.
-/
theorem eqvS (h : Nonempty (ρ.Equiv σ)) : Nonempty (σ.Equiv ρ) := h.map Representation.Equiv.symm

end Eqv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
The claim follows from `isSmooth_parInd _ _`.
-/
theorem isSmooth_multiProd' {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {X : α → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (m a) k) (X a)) :
    IsSmooth (multiProd e π) := isSmooth_parInd _ _

/- English proof (translation)
Consider the cases of `u with`. Consider the case `zero`. Establish `hT : T = 0` using `by simpa using (Fintype.card_congr e).symm`. Substitute `hT` using the available equality. Establish `hN : p = N` using `by omega`.

Substitute `hN` using the available equality. Establish `A` using `ind₂_unit_right h₁ x.π x.smooth (fun a => (τ a).π) e`. Establish `B` using `GlobalTheory.T.parabolicInductionTwoBlocks_empty_product_left k p 0 h₂ _ x.π x.smooth _ _ (fun a => (τ a).π) e`. Conclude with `eqvT A (eqvS B)`. Consider the case `succ u => exact GlobalTheory.T.inducedProductCommutes_familyProduct k p u x dτ τ hC T N e h₁ h₂`.
-/
theorem commutes_multiProd' {p u : ℕ} (x : Irr k p) {dτ : Fin u → ℕ} (τ : ∀ a, Irr k (dτ a))
    (hC : ∀ a, Commutes x (τ a)) {T N : ℕ} (e : (Σ a, Fin (dτ a)) ≃ Fin T) (h₁ : p + T = N) (h₂ : T + p = N) :
    Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (multiProd e fun a => (τ a).π))).Equiv
      (ind₂ (stdSum h₂) (extTensor (multiProd e fun a => (τ a).π) x.π))) := by
  cases u with
  | zero =>
    have hT : T = 0 := by simpa using (Fintype.card_congr e).symm
    subst hT
    have hN : p = N := by omega
    subst hN
    have A := ind₂_unit_right h₁ x.π x.smooth (fun a => (τ a).π) e
    have B := GlobalTheory.T.parabolicInductionTwoBlocks_empty_product_left k p 0 h₂ _ x.π x.smooth _ _ (fun a => (τ a).π) e
    exact eqvT A (eqvS B)
  | succ u => exact GlobalTheory.T.inducedProductCommutes_familyProduct k p u x dτ τ hC T N e h₁ h₂

def ReorderClaim (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) : Prop :=
  ∀ (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)) (s₁ s₂ : ℕ) (ι₁ : Fin s₁ → Fin s) (ι₂ : Fin s₂ → Fin s),
    StrictMono ι₁ → StrictMono ι₂ → Function.Bijective (Sum.elim ι₁ ι₂) →
    (∀ i j, Commutes (σ (ι₁ i)) (σ (ι₂ j))) → ∀ (r t N : ℕ) (h : r + t = N) (e : (Σ a, Fin (d a)) ≃ Fin N)
    (e₁ : (Σ i, Fin (d (ι₁ i))) ≃ Fin r) (e₂ : (Σ j, Fin (d (ι₂ j))) ≃ Fin t),
    Nonempty ((multiProd e fun a => (σ a).π).Equiv (ind₂ (stdSum h)
      (extTensor (multiProd e₁ fun i => (σ (ι₁ i)).π) (multiProd e₂ fun j => (σ (ι₂ j)).π))))

/- English proof (translation)
Introduce `d σ s₁ s₂ ι₁ ι₂ _ _ _ _ r t N h e e₁ e₂`. Consider the cases of `s₁ with`. Consider the case `succ s₁ => exact (ι₁ 0).elim0`. Consider the case `zero`. Consider the cases of `s₂ with`.

Consider the case `succ s₂ => exact (ι₂ 0).elim0`. Consider the case `zero`. Establish `hr : r = 0` using `by simpa using (Fintype.card_congr e₁).symm`. Establish `ht : t = 0` using `by simpa using (Fintype.card_congr e₂).symm`. Substitute `hr ht` using the available equality.

Establish `hN : N = 0` using `by omega`. Substitute `hN` using the available equality. Establish `A : Nonempty ((multiProd e fun a => (σ a).π).Equiv (multiProd e₂ fun j => (σ (ι₂ j)).π))` using `multiProd_empty (k := k) _ _ e e₂`. Establish `B` using `GlobalTheory.T.parabolicInductionTwoBlocks_empty_product_left k 0 0 h _ _ (isSmooth_multiProd' e₂ fun j => (σ (ι₂ j)).π) _ _ (fun i => (σ (ι₁ i)).π) e₁`. Conclude with `eqvT A (eqvS B)`.
-/
theorem reorderClaim_zero : ReorderClaim k 0 := by
  intro d σ s₁ s₂ ι₁ ι₂ _ _ _ _ r t N h e e₁ e₂
  cases s₁ with
  | succ s₁ => exact (ι₁ 0).elim0
  | zero =>
  cases s₂ with
  | succ s₂ => exact (ι₂ 0).elim0
  | zero =>
  have hr : r = 0 := by simpa using (Fintype.card_congr e₁).symm
  have ht : t = 0 := by simpa using (Fintype.card_congr e₂).symm
  subst hr ht
  have hN : N = 0 := by omega
  subst hN
  have A : Nonempty ((multiProd e fun a => (σ a).π).Equiv (multiProd e₂ fun j => (σ (ι₂ j)).π)) :=
    multiProd_empty (k := k) _ _ e e₂
  have B := GlobalTheory.T.parabolicInductionTwoBlocks_empty_product_left k 0 0 h _ _ (isSmooth_multiProd' e₂ fun j => (σ (ι₂ j)).π) _ _
    (fun i => (σ (ι₁ i)).π) e₁
  exact eqvT A (eqvS B)

/- English proof (translation)
Establish `hc' : ∀ i j, Commutes (σ (f i).succ) (σ (g j).succ)` using `fun i j => by`. Use `hc i.succ j` as an intermediate fact. Rewrite `this` using `[hf i, hg j]`. Conclude with `this`. Establish `Hr : ∃ (r' : ℕ) (_ : (Σ i : Fin s₁, Fin (d (f i).succ)) ≃ Fin r'), d 0 + r' = r`.

Use `⟨_, finSigmaFinEquiv, ?_⟩` and prove the remaining obligations. Use `Fintype.card_congr e₁` as an intermediate fact. Simplify using `only [Fintype.card_sigma, Fintype.card_fin, Fin.sum_univ_succ, h0, hf] at this`. Conclude with `this`. Take `⟨r', e₁', hr⟩` from `Hr`.

Establish `Ht : Nonempty ((Σ j : Fin s₂, Fin (d (g j).succ)) ≃ Fin t)`. Use `⟨(finSigmaFinEquiv).trans (finCongr ?_)⟩` and prove the remaining obligations. Use `Fintype.card_congr e₂` as an intermediate fact. Simplify using `only [Fintype.card_sigma, Fintype.card_fin, hg] at this`. Conclude with `this`.

Take `⟨e₂'⟩` from `Ht`. Establish `HT : Nonempty ((Σ a : Fin s, Fin (d a.succ)) ≃ Fin (r' + t))` using `⟨(sigmaPart (fun a => d a.succ) f g hb).trans ((e₁'.sumCongr e₂').trans finSumFinEquiv)⟩`. Take `⟨eT⟩` from `HT`. Establish `IH` using `ih (fun a => d a.succ) (fun a => σ a.succ) s₁ s₂ f g m₁ m₂ hb hc' r' t (r' + t) rfl eT e₁' e₂'`. Establish `hA : d 0 + (r' + t) = N` using `by omega`.

Establish `S1` using `multiProd_head (k := k) (fun a => (σ a).π) e hA eT`. Establish `S2` using `ind₂_congr_right_prod hA rfl (σ 0).π (multiProd e₁' fun i => (σ (f i).succ).π) (multiProd e₂' fun j => (σ (g j).succ).π) (multiProd eT fun a => (σ a.succ).π) IH`. Establish `S3` using `ind₂_assoc' (k := k) hr h rfl hA (σ 0).π (multiProd e₁' fun i => (σ (f i).succ).π) (multiProd e₂' fun j => (σ (g j).succ).π) (σ 0).smooth (isSmooth_multiProd' _ _) (isSmooth_multiProd' _ _)`. Establish `S4` using `multiProd_head_comp σ ι₁ 0 (fun i => (f i).succ) h0 hf e₁ hr e₁'`. Establish `S5` using `ind₂_congr_left_prod h hr (σ 0).π (multiProd e₁' fun i => (σ (f i).succ).π) (multiProd e₂' fun j => (σ (g j).succ).π) (multiProd e₁ fun i => (σ (ι₁ i)).π) S4`.

Establish `S6` using `ind₂_congr h (eqv_refl (multiProd e₁ fun i => (σ (ι₁ i)).π)) (multiProd_comp_congr σ (funext hg).symm e₂' e₂)`. Conclude with `eqvT S1 (eqvT S2 (eqvT (eqvS S3) (eqvT (eqvS S5) S6)))`.
-/
theorem reorderClaim_succ_first {s : ℕ} (ih : ReorderClaim k s) (d : Fin (s + 1) → ℕ) (σ : ∀ a, Irr k (d a))
    {s₁ s₂ : ℕ} (ι₁ : Fin (s₁ + 1) → Fin (s + 1)) (ι₂ : Fin s₂ → Fin (s + 1)) (f : Fin s₁ → Fin s)
    (g : Fin s₂ → Fin s) (h0 : ι₁ 0 = 0) (hf : ∀ i, ι₁ i.succ = (f i).succ) (hg : ∀ j, ι₂ j = (g j).succ)
    (m₁ : StrictMono f) (m₂ : StrictMono g) (hb : Function.Bijective (Sum.elim f g))
    (hc : ∀ i j, Commutes (σ (ι₁ i)) (σ (ι₂ j))) (r t N : ℕ) (h : r + t = N) (e : (Σ a, Fin (d a)) ≃ Fin N)
    (e₁ : (Σ i, Fin (d (ι₁ i))) ≃ Fin r) (e₂ : (Σ j, Fin (d (ι₂ j))) ≃ Fin t) :
    Nonempty ((multiProd e fun a => (σ a).π).Equiv (ind₂ (stdSum h)
      (extTensor (multiProd e₁ fun i => (σ (ι₁ i)).π) (multiProd e₂ fun j => (σ (ι₂ j)).π)))) := by
  have hc' : ∀ i j, Commutes (σ (f i).succ) (σ (g j).succ) := fun i j => by
    have := hc i.succ j
    rw [hf i, hg j] at this
    exact this
  have Hr : ∃ (r' : ℕ) (_ : (Σ i : Fin s₁, Fin (d (f i).succ)) ≃ Fin r'), d 0 + r' = r := by
    refine ⟨_, finSigmaFinEquiv, ?_⟩
    have := Fintype.card_congr e₁
    simp only [Fintype.card_sigma, Fintype.card_fin, Fin.sum_univ_succ, h0, hf] at this
    exact this
  obtain ⟨r', e₁', hr⟩ := Hr
  have Ht : Nonempty ((Σ j : Fin s₂, Fin (d (g j).succ)) ≃ Fin t) := by
    refine ⟨(finSigmaFinEquiv).trans (finCongr ?_)⟩
    have := Fintype.card_congr e₂
    simp only [Fintype.card_sigma, Fintype.card_fin, hg] at this
    exact this
  obtain ⟨e₂'⟩ := Ht
  have HT : Nonempty ((Σ a : Fin s, Fin (d a.succ)) ≃ Fin (r' + t)) :=
    ⟨(sigmaPart (fun a => d a.succ) f g hb).trans ((e₁'.sumCongr e₂').trans finSumFinEquiv)⟩
  obtain ⟨eT⟩ := HT
  have IH := ih (fun a => d a.succ) (fun a => σ a.succ) s₁ s₂ f g m₁ m₂ hb hc' r' t (r' + t) rfl eT e₁' e₂'
  have hA : d 0 + (r' + t) = N := by omega
  have S1 := multiProd_head (k := k) (fun a => (σ a).π) e hA eT
  have S2 := ind₂_congr_right_prod hA rfl (σ 0).π (multiProd e₁' fun i => (σ (f i).succ).π)
    (multiProd e₂' fun j => (σ (g j).succ).π) (multiProd eT fun a => (σ a.succ).π) IH
  have S3 := ind₂_assoc' (k := k) hr h rfl hA (σ 0).π (multiProd e₁' fun i => (σ (f i).succ).π)
    (multiProd e₂' fun j => (σ (g j).succ).π) (σ 0).smooth (isSmooth_multiProd' _ _) (isSmooth_multiProd' _ _)
  have S4 := multiProd_head_comp σ ι₁ 0 (fun i => (f i).succ) h0 hf e₁ hr e₁'
  have S5 := ind₂_congr_left_prod h hr (σ 0).π (multiProd e₁' fun i => (σ (f i).succ).π)
    (multiProd e₂' fun j => (σ (g j).succ).π) (multiProd e₁ fun i => (σ (ι₁ i)).π) S4
  have S6 := ind₂_congr h (eqv_refl (multiProd e₁ fun i => (σ (ι₁ i)).π))
    (multiProd_comp_congr σ (funext hg).symm e₂' e₂)
  exact eqvT S1 (eqvT S2 (eqvT (eqvS S3) (eqvT (eqvS S5) S6)))

/- English proof (translation)
Establish `hc' : ∀ i j, Commutes (σ (f i).succ) (σ (g j).succ)` using `fun i j => by`. Use `hc i j.succ` as an intermediate fact. Rewrite `this` using `[hf i, hg j]`. Conclude with `this`. Establish `hcomm : ∀ i, Commutes (σ 0) (σ (f i).succ)` using `fun i => by`.

Use `(hc i 0).symm` as an intermediate fact. Rewrite `this` using `[h0, hf i]`. Conclude with `this`. Establish `Ht : ∃ (t' : ℕ) (_ : (Σ j : Fin s₂, Fin (d (g j).succ)) ≃ Fin t'), d 0 + t' = t`. Use `⟨_, finSigmaFinEquiv, ?_⟩` and prove the remaining obligations.

Use `Fintype.card_congr e₂` as an intermediate fact. Simplify using `only [Fintype.card_sigma, Fintype.card_fin, Fin.sum_univ_succ, h0, hg] at this`. Conclude with `this`. Take `⟨t', e₂', ht⟩` from `Ht`. Establish `Hr : Nonempty ((Σ i : Fin s₁, Fin (d (f i).succ)) ≃ Fin r)`.

Use `⟨(finSigmaFinEquiv).trans (finCongr ?_)⟩` and prove the remaining obligations. Use `Fintype.card_congr e₁` as an intermediate fact. Simplify using `only [Fintype.card_sigma, Fintype.card_fin, hf] at this`. Conclude with `this`. Take `⟨e₁'⟩` from `Hr`.

Establish `HT : Nonempty ((Σ a : Fin s, Fin (d a.succ)) ≃ Fin (r + t'))` using `⟨(sigmaPart (fun a => d a.succ) f g hb).trans ((e₁'.sumCongr e₂').trans finSumFinEquiv)⟩`. Take `⟨eT⟩` from `HT`. Establish `IH` using `ih (fun a => d a.succ) (fun a => σ a.succ) s₁ s₂ f g m₁ m₂ hb hc' r t' (r + t') rfl eT e₁' e₂'`. Establish `hA : d 0 + (r + t') = N` using `by omega`. Establish `hB : d 0 + r + t' = N` using `by omega`.

Establish `hr' : r + d 0 = d 0 + r` using `Nat.add_comm _ _`. Establish `S1` using `multiProd_head (k := k) (fun a => (σ a).π) e hA eT`. Establish `S2` using `ind₂_congr_right_prod hA rfl (σ 0).π (multiProd e₁' fun i => (σ (f i).succ).π) (multiProd e₂' fun j => (σ (g j).succ).π) (multiProd eT fun a => (σ a.succ).π) IH`. Establish `S3` using `ind₂_assoc' (k := k) rfl hB rfl hA (σ 0).π (multiProd e₁' fun i => (σ (f i).succ).π) (multiProd e₂' fun j => (σ (g j).succ).π) (σ 0).smooth (isSmooth_multiProd' _ _) (isSmooth_multiProd' _ _)`. Establish `S4` using `commutes_multiProd' (σ 0) (fun i => σ (f i).succ) hcomm e₁' rfl hr'`.

Establish `S5` using `ind₂_congr_left_prod₂ hB rfl hr' (σ 0).π (multiProd e₁' fun i => (σ (f i).succ).π) (multiProd e₁' fun i => (σ (f i).succ).π) (σ 0).π (multiProd e₂' fun j => (σ (g j).succ).π) S4`. Establish `S6` using `ind₂_assoc' (k := k) hr' hB ht h (multiProd e₁' fun i => (σ (f i).succ).π) (σ 0).π (multiProd e₂' fun j => (σ (g j).succ).π) (isSmooth_multiProd' _ _) (σ 0).smooth (isSmooth_multiProd' _ _)`. Establish `S7` using `multiProd_head_comp σ ι₂ 0 (fun j => (g j).succ) h0 hg e₂ ht e₂'`. Establish `S8` using `ind₂_congr_right_prod h ht (multiProd e₁' fun i => (σ (f i).succ).π) (σ 0).π (multiProd e₂' fun j => (σ (g j).succ).π) (multiProd e₂ fun j => (σ (ι₂ j)).π) S7`. Establish `S9` using `ind₂_congr h (multiProd_comp_congr σ (funext hf).symm e₁' e₁) (eqv_refl (multiProd e₂ fun j => (σ (ι₂ j)).π))`.

Conclude with `eqvT S1 (eqvT S2 (eqvT (eqvS S3) (eqvT S5 (eqvT S6 (eqvT (eqvS S8) S9)))))`.
-/
theorem reorderClaim_succ_second {s : ℕ} (ih : ReorderClaim k s) (d : Fin (s + 1) → ℕ) (σ : ∀ a, Irr k (d a))
    {s₁ s₂ : ℕ} (ι₁ : Fin s₁ → Fin (s + 1)) (ι₂ : Fin (s₂ + 1) → Fin (s + 1)) (f : Fin s₁ → Fin s)
    (g : Fin s₂ → Fin s) (h0 : ι₂ 0 = 0) (hf : ∀ i, ι₁ i = (f i).succ) (hg : ∀ j, ι₂ j.succ = (g j).succ)
    (m₁ : StrictMono f) (m₂ : StrictMono g) (hb : Function.Bijective (Sum.elim f g))
    (hc : ∀ i j, Commutes (σ (ι₁ i)) (σ (ι₂ j))) (r t N : ℕ) (h : r + t = N) (e : (Σ a, Fin (d a)) ≃ Fin N)
    (e₁ : (Σ i, Fin (d (ι₁ i))) ≃ Fin r) (e₂ : (Σ j, Fin (d (ι₂ j))) ≃ Fin t) :
    Nonempty ((multiProd e fun a => (σ a).π).Equiv (ind₂ (stdSum h)
      (extTensor (multiProd e₁ fun i => (σ (ι₁ i)).π) (multiProd e₂ fun j => (σ (ι₂ j)).π)))) := by
  have hc' : ∀ i j, Commutes (σ (f i).succ) (σ (g j).succ) := fun i j => by
    have := hc i j.succ
    rw [hf i, hg j] at this
    exact this
  have hcomm : ∀ i, Commutes (σ 0) (σ (f i).succ) := fun i => by
    have := (hc i 0).symm
    rw [h0, hf i] at this
    exact this
  have Ht : ∃ (t' : ℕ) (_ : (Σ j : Fin s₂, Fin (d (g j).succ)) ≃ Fin t'), d 0 + t' = t := by
    refine ⟨_, finSigmaFinEquiv, ?_⟩
    have := Fintype.card_congr e₂
    simp only [Fintype.card_sigma, Fintype.card_fin, Fin.sum_univ_succ, h0, hg] at this
    exact this
  obtain ⟨t', e₂', ht⟩ := Ht
  have Hr : Nonempty ((Σ i : Fin s₁, Fin (d (f i).succ)) ≃ Fin r) := by
    refine ⟨(finSigmaFinEquiv).trans (finCongr ?_)⟩
    have := Fintype.card_congr e₁
    simp only [Fintype.card_sigma, Fintype.card_fin, hf] at this
    exact this
  obtain ⟨e₁'⟩ := Hr
  have HT : Nonempty ((Σ a : Fin s, Fin (d a.succ)) ≃ Fin (r + t')) :=
    ⟨(sigmaPart (fun a => d a.succ) f g hb).trans ((e₁'.sumCongr e₂').trans finSumFinEquiv)⟩
  obtain ⟨eT⟩ := HT
  have IH := ih (fun a => d a.succ) (fun a => σ a.succ) s₁ s₂ f g m₁ m₂ hb hc' r t' (r + t') rfl eT e₁' e₂'
  have hA : d 0 + (r + t') = N := by omega
  have hB : d 0 + r + t' = N := by omega
  have hr' : r + d 0 = d 0 + r := Nat.add_comm _ _
  have S1 := multiProd_head (k := k) (fun a => (σ a).π) e hA eT
  have S2 := ind₂_congr_right_prod hA rfl (σ 0).π (multiProd e₁' fun i => (σ (f i).succ).π)
    (multiProd e₂' fun j => (σ (g j).succ).π) (multiProd eT fun a => (σ a.succ).π) IH
  have S3 := ind₂_assoc' (k := k) rfl hB rfl hA (σ 0).π (multiProd e₁' fun i => (σ (f i).succ).π)
    (multiProd e₂' fun j => (σ (g j).succ).π) (σ 0).smooth (isSmooth_multiProd' _ _) (isSmooth_multiProd' _ _)
  have S4 := commutes_multiProd' (σ 0) (fun i => σ (f i).succ) hcomm e₁' rfl hr'
  have S5 := ind₂_congr_left_prod₂ hB rfl hr' (σ 0).π (multiProd e₁' fun i => (σ (f i).succ).π)
    (multiProd e₁' fun i => (σ (f i).succ).π) (σ 0).π (multiProd e₂' fun j => (σ (g j).succ).π) S4
  have S6 := ind₂_assoc' (k := k) hr' hB ht h (multiProd e₁' fun i => (σ (f i).succ).π) (σ 0).π
    (multiProd e₂' fun j => (σ (g j).succ).π) (isSmooth_multiProd' _ _) (σ 0).smooth (isSmooth_multiProd' _ _)
  have S7 := multiProd_head_comp σ ι₂ 0 (fun j => (g j).succ) h0 hg e₂ ht e₂'
  have S8 := ind₂_congr_right_prod h ht (multiProd e₁' fun i => (σ (f i).succ).π) (σ 0).π
    (multiProd e₂' fun j => (σ (g j).succ).π) (multiProd e₂ fun j => (σ (ι₂ j)).π) S7
  have S9 := ind₂_congr h (multiProd_comp_congr σ (funext hf).symm e₁' e₁)
    (eqv_refl (multiProd e₂ fun j => (σ (ι₂ j)).π))
  exact eqvT S1 (eqvT S2 (eqvT (eqvS S3) (eqvT S5 (eqvT S6 (eqvT (eqvS S8) S9)))))

/- English proof (translation)
Introduce `d σ s₁ s₂ ι₁ ι₂ m₁ m₂ hb hc r t N h e e₁ e₂`. Establish `hcard : s₁ + s₂ = s + 1`. Use `Fintype.card_of_bijective hb` as an intermediate fact. Simplify using `using this`. Establish `H0` using `hb.2 0`.

Take `⟨x, hx⟩` from `H0`. Consider the cases of `x with`. Consider the case `inl i₀`. Simplify using `only [Sum.elim_inl] at hx`. Consider the cases of `s₁ with`.

Consider the case `zero => exact i₀.elim0`. Consider the case `succ s₁`. Establish `h0 : ι₁ 0 = 0` using `Fin.le_zero_iff.1 ((m₁.monotone (Fin.zero_le i₀)).trans hx.le)`. Establish `hne1 : ∀ i : Fin s₁, ι₁ i.succ ≠ 0` using `fun i hi => Fin.succ_ne_zero i (m₁.injective (hi.trans h0.symm))`. Establish `hne2 : ∀ j, ι₂ j ≠ 0` using `fun j hj => by`.

Use `hb.1 (a₁ := Sum.inr j) (a₂ := Sum.inl 0) (by simp [hj, h0])` as an intermediate fact. Conclude with `Sum.inr_ne_inl this`. Establish `Hf : ∃ f : Fin s₁ → Fin s, ∀ i, ι₁ i.succ = (f i).succ` using `⟨fun i => (ι₁ i.succ).pred (hne1 i), fun i => (Fin.succ_pred _ _).symm⟩`. Establish `Hg : ∃ g : Fin s₂ → Fin s, ∀ j, ι₂ j = (g j).succ` using `⟨fun j => (ι₂ j).pred (hne2 j), fun j => (Fin.succ_pred _ _).symm⟩`. Take `⟨f, hf⟩` from `Hf`.

Take `⟨g, hg⟩` from `Hg`. Establish `m₁' : StrictMono f` using `fun i j hij => by`. Use `m₁ (Fin.succ_lt_succ_iff.2 hij)` as an intermediate fact. Rewrite `this` using `[hf, hf]`. Conclude with `Fin.succ_lt_succ_iff.1 this`.

Establish `m₂' : StrictMono g` using `fun i j hij => by`. Use `m₂ hij` as an intermediate fact. Rewrite `this` using `[hg, hg]`. Conclude with `Fin.succ_lt_succ_iff.1 this`. Establish `hb' : Function.Bijective (Sum.elim f g)`.

Establish `key : Fin.succ ∘ Sum.elim f g = Sum.elim ι₁ ι₂ ∘ Sum.map Fin.succ id`. Use function extensionality and compare the values at `x`. Apply the tactic sequence `cases x <;> simp [hf, hg]`. Establish `h1` using `hb.1.comp (Sum.map_injective.2 ⟨Fin.succ_injective _, Function.injective_id⟩)`. Rewrite `h1` using `[← key]`.

Use `(Fintype.bijective_iff_injective_and_card _).2 ⟨h1.of_comp, ?_⟩` and prove the remaining obligations. Simplify using `only [Fintype.card_sum, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers. Conclude with `reorderClaim_succ_first ih d σ ι₁ ι₂ f g h0 hf hg m₁' m₂' hb' hc r t N h e e₁ e₂`. Consider the case `inr j₀`.

Simplify using `only [Sum.elim_inr] at hx`. Consider the cases of `s₂ with`. Consider the case `zero => exact j₀.elim0`. Consider the case `succ s₂`. Establish `h0 : ι₂ 0 = 0` using `Fin.le_zero_iff.1 ((m₂.monotone (Fin.zero_le j₀)).trans hx.le)`.

Establish `hne2 : ∀ j : Fin s₂, ι₂ j.succ ≠ 0` using `fun j hj => Fin.succ_ne_zero j (m₂.injective (hj.trans h0.symm))`. Establish `hne1 : ∀ i, ι₁ i ≠ 0` using `fun i hi => by`. Use `hb.1 (a₁ := Sum.inl i) (a₂ := Sum.inr 0) (by simp [hi, h0])` as an intermediate fact. Conclude with `Sum.inl_ne_inr this`. Establish `Hf : ∃ f : Fin s₁ → Fin s, ∀ i, ι₁ i = (f i).succ` using `⟨fun i => (ι₁ i).pred (hne1 i), fun i => (Fin.succ_pred _ _).symm⟩`.

Establish `Hg : ∃ g : Fin s₂ → Fin s, ∀ j, ι₂ j.succ = (g j).succ` using `⟨fun j => (ι₂ j.succ).pred (hne2 j), fun j => (Fin.succ_pred _ _).symm⟩`. Take `⟨f, hf⟩` from `Hf`. Take `⟨g, hg⟩` from `Hg`. Establish `m₁' : StrictMono f` using `fun i j hij => by`. Use `m₁ hij` as an intermediate fact.

Rewrite `this` using `[hf, hf]`. Conclude with `Fin.succ_lt_succ_iff.1 this`. Establish `m₂' : StrictMono g` using `fun i j hij => by`. Use `m₂ (Fin.succ_lt_succ_iff.2 hij)` as an intermediate fact. Rewrite `this` using `[hg, hg]`.

Conclude with `Fin.succ_lt_succ_iff.1 this`. Establish `hb' : Function.Bijective (Sum.elim f g)`. Establish `key : Fin.succ ∘ Sum.elim f g = Sum.elim ι₁ ι₂ ∘ Sum.map id Fin.succ`. Use function extensionality and compare the values at `x`. Apply the tactic sequence `cases x <;> simp [hf, hg]`.

Establish `h1` using `hb.1.comp (Sum.map_injective.2 ⟨Function.injective_id, Fin.succ_injective _⟩)`. Rewrite `h1` using `[← key]`. Use `(Fintype.bijective_iff_injective_and_card _).2 ⟨h1.of_comp, ?_⟩` and prove the remaining obligations. Simplify using `only [Fintype.card_sum, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers.

Conclude with `reorderClaim_succ_second ih d σ ι₁ ι₂ f g h0 hf hg m₁' m₂' hb' hc r t N h e e₁ e₂`.
-/
theorem reorderClaim_succ {s : ℕ} (ih : ReorderClaim k s) : ReorderClaim k (s + 1) := by
  intro d σ s₁ s₂ ι₁ ι₂ m₁ m₂ hb hc r t N h e e₁ e₂
  have hcard : s₁ + s₂ = s + 1 := by
    have := Fintype.card_of_bijective hb
    simpa using this
  have H0 := hb.2 0
  obtain ⟨x, hx⟩ := H0
  cases x with
  | inl i₀ =>
    simp only [Sum.elim_inl] at hx
    cases s₁ with
    | zero => exact i₀.elim0
    | succ s₁ =>
    have h0 : ι₁ 0 = 0 := Fin.le_zero_iff.1 ((m₁.monotone (Fin.zero_le i₀)).trans hx.le)
    have hne1 : ∀ i : Fin s₁, ι₁ i.succ ≠ 0 := fun i hi =>
      Fin.succ_ne_zero i (m₁.injective (hi.trans h0.symm))
    have hne2 : ∀ j, ι₂ j ≠ 0 := fun j hj => by
      have := hb.1 (a₁ := Sum.inr j) (a₂ := Sum.inl 0) (by simp [hj, h0])
      exact Sum.inr_ne_inl this
    have Hf : ∃ f : Fin s₁ → Fin s, ∀ i, ι₁ i.succ = (f i).succ :=
      ⟨fun i => (ι₁ i.succ).pred (hne1 i), fun i => (Fin.succ_pred _ _).symm⟩
    have Hg : ∃ g : Fin s₂ → Fin s, ∀ j, ι₂ j = (g j).succ :=
      ⟨fun j => (ι₂ j).pred (hne2 j), fun j => (Fin.succ_pred _ _).symm⟩
    obtain ⟨f, hf⟩ := Hf
    obtain ⟨g, hg⟩ := Hg
    have m₁' : StrictMono f := fun i j hij => by
      have := m₁ (Fin.succ_lt_succ_iff.2 hij)
      rw [hf, hf] at this
      exact Fin.succ_lt_succ_iff.1 this
    have m₂' : StrictMono g := fun i j hij => by
      have := m₂ hij
      rw [hg, hg] at this
      exact Fin.succ_lt_succ_iff.1 this
    have hb' : Function.Bijective (Sum.elim f g) := by
      have key : Fin.succ ∘ Sum.elim f g = Sum.elim ι₁ ι₂ ∘ Sum.map Fin.succ id := by
        funext x
        cases x <;> simp [hf, hg]
      have h1 := hb.1.comp (Sum.map_injective.2 ⟨Fin.succ_injective _, Function.injective_id⟩)
      rw [← key] at h1
      refine (Fintype.bijective_iff_injective_and_card _).2 ⟨h1.of_comp, ?_⟩
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    exact reorderClaim_succ_first ih d σ ι₁ ι₂ f g h0 hf hg m₁' m₂' hb' hc r t N h e e₁ e₂
  | inr j₀ =>
    simp only [Sum.elim_inr] at hx
    cases s₂ with
    | zero => exact j₀.elim0
    | succ s₂ =>
    have h0 : ι₂ 0 = 0 := Fin.le_zero_iff.1 ((m₂.monotone (Fin.zero_le j₀)).trans hx.le)
    have hne2 : ∀ j : Fin s₂, ι₂ j.succ ≠ 0 := fun j hj =>
      Fin.succ_ne_zero j (m₂.injective (hj.trans h0.symm))
    have hne1 : ∀ i, ι₁ i ≠ 0 := fun i hi => by
      have := hb.1 (a₁ := Sum.inl i) (a₂ := Sum.inr 0) (by simp [hi, h0])
      exact Sum.inl_ne_inr this
    have Hf : ∃ f : Fin s₁ → Fin s, ∀ i, ι₁ i = (f i).succ :=
      ⟨fun i => (ι₁ i).pred (hne1 i), fun i => (Fin.succ_pred _ _).symm⟩
    have Hg : ∃ g : Fin s₂ → Fin s, ∀ j, ι₂ j.succ = (g j).succ :=
      ⟨fun j => (ι₂ j.succ).pred (hne2 j), fun j => (Fin.succ_pred _ _).symm⟩
    obtain ⟨f, hf⟩ := Hf
    obtain ⟨g, hg⟩ := Hg
    have m₁' : StrictMono f := fun i j hij => by
      have := m₁ hij
      rw [hf, hf] at this
      exact Fin.succ_lt_succ_iff.1 this
    have m₂' : StrictMono g := fun i j hij => by
      have := m₂ (Fin.succ_lt_succ_iff.2 hij)
      rw [hg, hg] at this
      exact Fin.succ_lt_succ_iff.1 this
    have hb' : Function.Bijective (Sum.elim f g) := by
      have key : Fin.succ ∘ Sum.elim f g = Sum.elim ι₁ ι₂ ∘ Sum.map id Fin.succ := by
        funext x
        cases x <;> simp [hf, hg]
      have h1 := hb.1.comp (Sum.map_injective.2 ⟨Function.injective_id, Fin.succ_injective _⟩)
      rw [← key] at h1
      refine (Fintype.bijective_iff_injective_and_card _).2 ⟨h1.of_comp, ?_⟩
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    exact reorderClaim_succ_second ih d σ ι₁ ι₂ f g h0 hf hg m₁' m₂' hb' hc r t N h e e₁ e₂

/- English proof (translation)
The claim follows from `| 0 => reorderClaim_zero | s + 1 => reorderClaim_succ (reorderClaim_all s)`.
-/
theorem reorderClaim_all : ∀ s, ReorderClaim k s
  | 0 => reorderClaim_zero
  | s + 1 => reorderClaim_succ (reorderClaim_all s)

/- English proof (translation)
Substitute `hN` using the available equality. Conclude with `eqvT (multiProd_placing f (stdBlocks D (Fin.sum_univ_two D)) P) (eqvS (GlobalTheory.LocGL.nonempty_prod₂_equiv_multiProd (Fin.sum_univ_two D) P))`.
-/
theorem multiProd_two_eqv {D : Fin 2 → ℕ} {X : Fin 2 → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (P : ∀ i, Representation ℂ (GL (Fin (D i)) k) (X i)) {N : ℕ} (f : (Σ i, Fin (D i)) ≃ Fin N)
    (hN : D 0 + D 1 = N) : Nonempty ((multiProd f P).Equiv (ind₂ (stdSum hN) (extTensor (P 0) (P 1)))) := by
  subst hN
  exact eqvT (multiProd_placing f (stdBlocks D (Fin.sum_univ_two D)) P)
    (eqvS (GlobalTheory.LocGL.nonempty_prod₂_equiv_multiProd (Fin.sum_univ_two D) P))

/- English proof (translation)
Substitute `ha hb` using the available equality. Conclude with `⟨Representation.Equiv.refl _⟩`.
-/
theorem ind₂_index_congr {s : ℕ} {d : Fin s → ℕ} (σ : ∀ a, Irr k (d a)) {a a' b b' : Fin s} (ha : a = a')
    (hb : b = b') {N : ℕ} (h : d a + d b = N) (h' : d a' + d b' = N) :
    Nonempty ((ind₂ (stdSum h) (extTensor (σ a).π (σ b).π)).Equiv
      (ind₂ (stdSum h') (extTensor (σ a').π (σ b').π))) := by
  subst ha hb
  exact ⟨Representation.Equiv.refl _⟩

/- English proof (translation)
Introduce `N h₁ h₂`. Establish `ha0 : (![a, b] 0 : Fin s) = a` using `by simp`. Establish `hb1 : (![a, b] 1 : Fin s) = b` using `by simp`. Establish `hD0 : (![a, b] (Equiv.swap 0 1 0) : Fin s) = b` using `by simp`. Establish `hD1 : (![a, b] (Equiv.swap 0 1 1) : Fin s) = a` using `by simp`.

Establish `h₁' : d (![a, b] 0) + d (![a, b] 1) = N` using `by rw [ha0, hb1]; exact h₁`. Establish `h₂' : d (![a, b] (Equiv.swap 0 1 0)) + d (![a, b] (Equiv.swap 0 1 1)) = N`. Rewrite using `[hD0, hD1]`. Conclude with `h₂`. Establish `F₁ : Nonempty ((Σ i : Fin 2, Fin (d (![a, b] i))) ≃ Fin N)` using `⟨stdBlocks _ ((Fin.sum_univ_two _).trans h₁')⟩`.

Establish `F₂ : Nonempty ((Σ i : Fin 2, Fin (d (![a, b] (Equiv.swap 0 1 i)))) ≃ Fin N)` using `⟨stdBlocks _ ((Fin.sum_univ_two _).trans h₂')⟩`. Take `⟨f₁⟩` from `F₁`. Take `⟨f₂⟩` from `F₂`. Establish `K0` using `ind₂_index_congr σ ha0 hb1 h₁' h₁`. Establish `K1` using `multiProd_two_eqv (fun i => (σ (![a, b] i)).π) f₁ h₁'`.

Establish `K2` using `multiProd_two_eqv (fun i => (σ (![a, b] (Equiv.swap 0 1 i))).π) f₂ h₂'`. Establish `K3` using `H (Fin N) f₁ f₂`. Establish `K4` using `ind₂_index_congr σ hD0 hD1 h₂' h₂`. Conclude with `eqvT (eqvS K0) (eqvT (eqvS K1) (eqvT K3 (eqvT K2 K4)))`.
-/
theorem commutes_of_pair {s : ℕ} {d : Fin s → ℕ} (σ : ∀ a, Irr k (d a)) (a b : Fin s)
    (H : ∀ (n : Type) [Fintype n] [DecidableEq n] (f : (Σ i : Fin 2, Fin (d (![a, b] i))) ≃ n)
      (f' : (Σ i : Fin 2, Fin (d (![a, b] (Equiv.swap 0 1 i)))) ≃ n),
      Nonempty ((multiProd f fun i => (σ (![a, b] i)).π).Equiv
        (multiProd f' fun i => (σ (![a, b] (Equiv.swap 0 1 i))).π))) :
    Commutes (σ a) (σ b) := by
  intro N h₁ h₂
  have ha0 : (![a, b] 0 : Fin s) = a := by simp
  have hb1 : (![a, b] 1 : Fin s) = b := by simp
  have hD0 : (![a, b] (Equiv.swap 0 1 0) : Fin s) = b := by simp
  have hD1 : (![a, b] (Equiv.swap 0 1 1) : Fin s) = a := by simp
  have h₁' : d (![a, b] 0) + d (![a, b] 1) = N := by rw [ha0, hb1]; exact h₁
  have h₂' : d (![a, b] (Equiv.swap 0 1 0)) + d (![a, b] (Equiv.swap 0 1 1)) = N := by
    rw [hD0, hD1]; exact h₂
  have F₁ : Nonempty ((Σ i : Fin 2, Fin (d (![a, b] i))) ≃ Fin N) :=
    ⟨stdBlocks _ ((Fin.sum_univ_two _).trans h₁')⟩
  have F₂ : Nonempty ((Σ i : Fin 2, Fin (d (![a, b] (Equiv.swap 0 1 i)))) ≃ Fin N) :=
    ⟨stdBlocks _ ((Fin.sum_univ_two _).trans h₂')⟩
  obtain ⟨f₁⟩ := F₁
  obtain ⟨f₂⟩ := F₂
  have K0 := ind₂_index_congr σ ha0 hb1 h₁' h₁
  have K1 := multiProd_two_eqv (fun i => (σ (![a, b] i)).π) f₁ h₁'
  have K2 := multiProd_two_eqv (fun i => (σ (![a, b] (Equiv.swap 0 1 i))).π) f₂ h₂'
  have K3 := H (Fin N) f₁ f₂
  have K4 := ind₂_index_congr σ hD0 hD1 h₂' h₂
  exact eqvT (eqvS K0) (eqvT (eqvS K1) (eqvT K3 (eqvT K2 K4)))

/- English proof (translation)
Introduce `k _ _ _ _ s d σ S r t e e₁ e₂ hyp`. Establish `hm1 : ∀ i, Sᶜ.orderEmbOfFin rfl i ∉ S` using `fun i => Finset.mem_compl.1 (Finset.orderEmbOfFin_mem Sᶜ rfl i)`. Establish `hm2 : ∀ j, S.orderEmbOfFin rfl j ∈ S` using `fun j => Finset.orderEmbOfFin_mem S rfl j`. Establish `hb : Function.Bijective (Sum.elim (⇑(Sᶜ.orderEmbOfFin rfl)) (⇑(S.orderEmbOfFin rfl)))`. Use `⟨?_, fun a => ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `rintro (i | i) (j | j) hij <;> simp only [Sum.elim_inl, Sum.elim_inr] at hij`. Conclude with `congrArg Sum.inl ((Sᶜ.orderEmbOfFin rfl).injective hij)`. Conclude with `absurd (hij ▸ hm2 j) (hm1 i)`. Conclude with `absurd (hij ▸ hm2 i) (hm1 j)`. Conclude with `congrArg Sum.inr ((S.orderEmbOfFin rfl).injective hij)`.

Distinguish the cases in `ha : a ∈ S`. Establish `hr : a ∈ Set.range (S.orderEmbOfFin rfl)`. Rewrite using `[Finset.range_orderEmbOfFin]`. Conclude with `ha`. Take `⟨j, hj⟩` from `hr`.

Conclude with `⟨Sum.inr j, hj⟩`. Establish `hr : a ∈ Set.range (Sᶜ.orderEmbOfFin rfl)`. Rewrite using `[Finset.range_orderEmbOfFin]`. Simplify using `using ha`. Take `⟨i, hi⟩` from `hr`.

Conclude with `⟨Sum.inl i, hi⟩`. Conclude with `reorderClaim_all s d σ _ _ (⇑(Sᶜ.orderEmbOfFin rfl)) (⇑(S.orderEmbOfFin rfl)) (Sᶜ.orderEmbOfFin rfl).strictMono (S.orderEmbOfFin rfl).strictMono hb (fun i j => commutes_of_pair σ _ _ (hyp _ _ (hm1 i) (hm2 j))) r t (r + t) rfl e e₁ e₂`.
-/
theorem reorder_split : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)) (S : Finset (Fin s)) (r t : ℕ) (e : (Σ a, Fin (d a)) ≃ Fin (r + t)) (e₁ : (Σ a : Fin Sᶜ.card, Fin (d (Sᶜ.orderEmbOfFin rfl a))) ≃ Fin r) (e₂ : (Σ b : Fin S.card, Fin (d (S.orderEmbOfFin rfl b))) ≃ Fin t), (∀ a b, a ∉ S → b ∈ S → ∀ (n : Type) [Fintype n] [DecidableEq n] (f : (Σ i : Fin 2, Fin (d (![a, b] i))) ≃ n) (f' : (Σ i : Fin 2, Fin (d (![a, b] (Equiv.swap 0 1 i)))) ≃ n), Nonempty ((multiProd f fun i => (σ (![a, b] i)).π).Equiv (multiProd f' fun i => (σ (![a, b] (Equiv.swap 0 1 i))).π))) → Nonempty ((multiProd e fun a => (σ a).π).Equiv (prod₂ (multiProd e₁ fun a => (σ (Sᶜ.orderEmbOfFin rfl a)).π) (multiProd e₂ fun b => (σ (S.orderEmbOfFin rfl b)).π))) := by
  intro k _ _ _ _ s d σ S r t e e₁ e₂ hyp
  have hm1 : ∀ i, Sᶜ.orderEmbOfFin rfl i ∉ S := fun i => Finset.mem_compl.1 (Finset.orderEmbOfFin_mem Sᶜ rfl i)
  have hm2 : ∀ j, S.orderEmbOfFin rfl j ∈ S := fun j => Finset.orderEmbOfFin_mem S rfl j
  have hb : Function.Bijective (Sum.elim (⇑(Sᶜ.orderEmbOfFin rfl)) (⇑(S.orderEmbOfFin rfl))) := by
    refine ⟨?_, fun a => ?_⟩
    · rintro (i | i) (j | j) hij <;> simp only [Sum.elim_inl, Sum.elim_inr] at hij
      · exact congrArg Sum.inl ((Sᶜ.orderEmbOfFin rfl).injective hij)
      · exact absurd (hij ▸ hm2 j) (hm1 i)
      · exact absurd (hij ▸ hm2 i) (hm1 j)
      · exact congrArg Sum.inr ((S.orderEmbOfFin rfl).injective hij)
    · by_cases ha : a ∈ S
      · have hr : a ∈ Set.range (S.orderEmbOfFin rfl) := by
          rw [Finset.range_orderEmbOfFin]; exact ha
        obtain ⟨j, hj⟩ := hr
        exact ⟨Sum.inr j, hj⟩
      · have hr : a ∈ Set.range (Sᶜ.orderEmbOfFin rfl) := by
          rw [Finset.range_orderEmbOfFin]; simpa using ha
        obtain ⟨i, hi⟩ := hr
        exact ⟨Sum.inl i, hi⟩
  exact reorderClaim_all s d σ _ _ (⇑(Sᶜ.orderEmbOfFin rfl)) (⇑(S.orderEmbOfFin rfl))
    (Sᶜ.orderEmbOfFin rfl).strictMono (S.orderEmbOfFin rfl).strictMono hb
    (fun i j => commutes_of_pair σ _ _ (hyp _ _ (hm1 i) (hm2 j))) r t (r + t) rfl e e₁ e₂

end GlobalTheory.ProdReorder
