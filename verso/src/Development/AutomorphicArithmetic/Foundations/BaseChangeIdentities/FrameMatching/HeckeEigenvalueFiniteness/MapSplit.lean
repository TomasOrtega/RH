import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.PowEigAlt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ShuffleChoices.ChoiceT
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ShuffleChoices.ShufStd

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcN.F2
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Take `⟨hdisj, hcov⟩` from `hE n a s h`. Set `f : Fin a ⊕ Fin (n - a) → Fin n` to `Sum.elim ((symIdx n (a % 2 = 1) s).orderEmbOfFin h.2.1) ((symIdx n ((n - a) % 2 = 1) sᶜ).orderEmbOfFin h.2.2)`. Establish `hf : Function.Bijective f`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(i | i) (j | j) hij`.

Simplify using `only [f, Sum.elim_inl] at hij`. Conclude with `congrArg Sum.inl (((symIdx n (a % 2 = 1) s).orderEmbOfFin h.2.1).injective hij)`. It suffices to derive a contradiction. Simplify using `only [f, Sum.elim_inl, Sum.elim_inr] at hij`. Conclude with `Finset.disjoint_left.1 hdisj (Finset.orderEmbOfFin_mem _ h.2.1 i) (hij ▸ Finset.orderEmbOfFin_mem _ h.2.2 j)`.

It suffices to derive a contradiction. Simplify using `only [f, Sum.elim_inl, Sum.elim_inr] at hij`. Conclude with `Finset.disjoint_left.1 hdisj (Finset.orderEmbOfFin_mem _ h.2.1 j) (hij ▸ Finset.orderEmbOfFin_mem _ h.2.2 i)`. Simplify using `only [f, Sum.elim_inr] at hij`. Conclude with `congrArg Sum.inr (((symIdx n ((n - a) % 2 = 1) sᶜ).orderEmbOfFin h.2.2).injective hij)`.

Introduce `k`. Establish `hk : k ∈ symIdx n (a % 2 = 1) s ∪ symIdx n ((n - a) % 2 = 1) sᶜ` using `hcov ▸ Finset.mem_univ k`. Break down `Finset.mem_union.1 hk with hk | hk` into its components or cases. Establish `hr : k ∈ Set.range ((symIdx n (a % 2 = 1) s).orderEmbOfFin h.2.1)`. Rewrite using `[Finset.range_orderEmbOfFin]`.

Conclude with `hk`. Take `⟨i, hi⟩` from `hr`. Conclude with `⟨.inl i, hi⟩`. Establish `hr : k ∈ Set.range ((symIdx n ((n - a) % 2 = 1) sᶜ).orderEmbOfFin h.2.2)`. Rewrite using `[Finset.range_orderEmbOfFin]`.

Conclude with `hk`. Take `⟨j, hj⟩` from `hr`. Conclude with `⟨.inr j, hj⟩`. Conclude with `⟨Equiv.ofBijective f hf, fun i => rfl, fun j => rfl⟩`.
-/
private theorem exists_ex (hE : ShufEx) (n a : ℕ) (s : Finset (Fin (n / 2))) (h : LocData.admitted n a s) :
    ∃ e : Fin a ⊕ Fin (n - a) ≃ Fin n,
      (∀ i, e (.inl i) = (symIdx n (a % 2 = 1) s).orderEmbOfFin h.2.1 i) ∧
      ∀ j, e (.inr j) = (symIdx n ((n - a) % 2 = 1) sᶜ).orderEmbOfFin h.2.2 j := by
  obtain ⟨hdisj, hcov⟩ := hE n a s h
  let f : Fin a ⊕ Fin (n - a) → Fin n :=
    Sum.elim ((symIdx n (a % 2 = 1) s).orderEmbOfFin h.2.1) ((symIdx n ((n - a) % 2 = 1) sᶜ).orderEmbOfFin h.2.2)
  have hf : Function.Bijective f := by
    constructor
    · rintro (i | i) (j | j) hij
      · simp only [f, Sum.elim_inl] at hij
        exact congrArg Sum.inl (((symIdx n (a % 2 = 1) s).orderEmbOfFin h.2.1).injective hij)
      · exfalso
        simp only [f, Sum.elim_inl, Sum.elim_inr] at hij
        exact Finset.disjoint_left.1 hdisj (Finset.orderEmbOfFin_mem _ h.2.1 i)
          (hij ▸ Finset.orderEmbOfFin_mem _ h.2.2 j)
      · exfalso
        simp only [f, Sum.elim_inl, Sum.elim_inr] at hij
        exact Finset.disjoint_left.1 hdisj (Finset.orderEmbOfFin_mem _ h.2.1 j)
          (hij ▸ Finset.orderEmbOfFin_mem _ h.2.2 i)
      · simp only [f, Sum.elim_inr] at hij
        exact congrArg Sum.inr (((symIdx n ((n - a) % 2 = 1) sᶜ).orderEmbOfFin h.2.2).injective hij)
    · intro k
      have hk : k ∈ symIdx n (a % 2 = 1) s ∪ symIdx n ((n - a) % 2 = 1) sᶜ := hcov ▸ Finset.mem_univ k
      rcases Finset.mem_union.1 hk with hk | hk
      · have hr : k ∈ Set.range ((symIdx n (a % 2 = 1) s).orderEmbOfFin h.2.1) := by
          rw [Finset.range_orderEmbOfFin]
          exact hk
        obtain ⟨i, hi⟩ := hr
        exact ⟨.inl i, hi⟩
      · have hr : k ∈ Set.range ((symIdx n ((n - a) % 2 = 1) sᶜ).orderEmbOfFin h.2.2) := by
          rw [Finset.range_orderEmbOfFin]
          exact hk
        obtain ⟨j, hj⟩ := hr
        exact ⟨.inr j, hj⟩
  exact ⟨Equiv.ofBijective f hf, fun i => rfl, fun j => rfl⟩

/- English proof (translation)
Rewrite using `[← Multiset.map_univ_val_equiv e, Multiset.map_map, ← Finset.univ_disjSum_univ]`. Simplify using `[Finset.disjSum, Multiset.disjSum, Multiset.map_add, Multiset.map_map, Function.comp_def]`.
-/
private theorem map_split {α β : Type} [Fintype α] [Fintype β] {n : ℕ} (e : α ⊕ β ≃ Fin n) (f : Fin n → ℂˣ) :
    Finset.univ.val.map (fun i => f (e (.inl i))) + Finset.univ.val.map (fun j => f (e (.inr j))) =
      Finset.univ.val.map f := by
  rw [← Multiset.map_univ_val_equiv e, Multiset.map_map, ← Finset.univ_disjSum_univ]
  simp [Finset.disjSum, Multiset.disjSum, Multiset.map_add, Multiset.map_map, Function.comp_def]

/- English proof (translation)
Take `⟨hA, hB⟩` from `hT E n w (shufOf w n a s h e he ((-1) ^ (n - a)) ((-1) ^ a)) _ ξ ξa ξb hstd hchi`. Establish `hnorm : ∀ k : Fin n, ‖((Sum.elim (fun _ => ((-1) ^ (n - a) : ℂˣ)) (fun _ => (-1) ^ a) (e.symm k) : ℂˣ) : ℂ)‖ = 1`. Introduce `k`. Apply the tactic sequence `cases e.symm k <;> simp`. Take `⟨mA, mB⟩` from `hM n (shufOf w n a s h e he ((-1) ^ (n - a)) ((-1) ^ a)) _ ξ hmono hnorm`.

Establish `e1 : ξa = fun i => _` using `funext hA`. Establish `e2 : ξb = fun j => _` using `funext hB`. Use `⟨by rw [e1]; exact mA, by rw [e2]; exact mB, ?_⟩` and prove the remaining obligations. Rewrite using `[Multiset.map_map, Multiset.map_map, ← map_split e ξ]`. Use `congr 1`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[Function.comp_apply, hA i]`. Use `show ξ (e (.inl i)) * (Sum.elim (fun _ => ((-1) ^ (n - a) : ℂˣ)) (fun _ => (-1) ^ a) (e.symm (e (.inl i))))⁻¹ * (-1) ^ (n - a) = ξ (e (.inl i))`. Rewrite using `[Equiv.symm_apply_apply, Sum.elim_inl, inv_mul_cancel_right]`.

Use `congr 1`. Use function extensionality and compare the values at `j`. Rewrite using `[Function.comp_apply, hB j]`. Use `show ξ (e (.inr j)) * (Sum.elim (fun _ => ((-1) ^ (n - a) : ℂˣ)) (fun _ => (-1) ^ a) (e.symm (e (.inr j))))⁻¹ * (-1) ^ a = ξ (e (.inr j))`. Rewrite using `[Equiv.symm_apply_apply, Sum.elim_inr, inv_mul_cancel_right]`.
-/
private theorem finish (hT : TargetAlg) (hM : MonoRes) {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E)
    (n a : ℕ) (s : Finset (Fin (n / 2))) (h : LocData.admitted n a s) (e : Fin a ⊕ Fin (n - a) ≃ Fin n)
    (he : (∀ i, e (.inl i) = (symIdx n (a % 2 = 1) s).orderEmbOfFin h.2.1 i) ∧
      ∀ j, e (.inr j) = (symIdx n ((n - a) % 2 = 1) sᶜ).orderEmbOfFin h.2.2 j)
    (ξ : Fin n → ℂˣ) (ξa : Fin a → ℂˣ) (ξb : Fin (n - a) → ℂˣ) (hmono : PositivityTheory.Rg.BcB.N3.Mono ξ)
    (hstd : IsStd w (shufOf w n a s h e he ((-1) ^ (n - a)) ((-1) ^ a))
      (fun k => Sum.elim (fun _ => ((-1) ^ (n - a) : ℂˣ)) (fun _ => (-1) ^ a) (e.symm k)))
    (hchi : chiOf w (shufOf w n a s h e he ((-1) ^ (n - a)) ((-1) ^ a)) ξa ξb = chiN w ξ) :
    PositivityTheory.Rg.BcB.N3.Mono ξa ∧ PositivityTheory.Rg.BcB.N3.Mono ξb ∧
      (Finset.univ.val.map ξa).map (· * (-1 : ℂˣ) ^ (n - a)) + (Finset.univ.val.map ξb).map (· * (-1 : ℂˣ) ^ a) =
        Finset.univ.val.map ξ := by
  obtain ⟨hA, hB⟩ := hT E n w (shufOf w n a s h e he ((-1) ^ (n - a)) ((-1) ^ a)) _ ξ ξa ξb hstd hchi
  have hnorm : ∀ k : Fin n,
      ‖((Sum.elim (fun _ => ((-1) ^ (n - a) : ℂˣ)) (fun _ => (-1) ^ a) (e.symm k) : ℂˣ) : ℂ)‖ = 1 := by
    intro k
    cases e.symm k <;> simp
  obtain ⟨mA, mB⟩ := hM n (shufOf w n a s h e he ((-1) ^ (n - a)) ((-1) ^ a)) _ ξ hmono hnorm
  have e1 : ξa = fun i => _ := funext hA
  have e2 : ξb = fun j => _ := funext hB
  refine ⟨by rw [e1]; exact mA, by rw [e2]; exact mB, ?_⟩
  rw [Multiset.map_map, Multiset.map_map, ← map_split e ξ]
  congr 1
  · congr 1
    funext i
    rw [Function.comp_apply, hA i]
    show ξ (e (.inl i)) * (Sum.elim (fun _ => ((-1) ^ (n - a) : ℂˣ)) (fun _ => (-1) ^ a) (e.symm (e (.inl i))))⁻¹ *
      (-1) ^ (n - a) = ξ (e (.inl i))
    rw [Equiv.symm_apply_apply, Sum.elim_inl, inv_mul_cancel_right]
  · congr 1
    funext j
    rw [Function.comp_apply, hB j]
    show ξ (e (.inr j)) * (Sum.elim (fun _ => ((-1) ^ (n - a) : ℂˣ)) (fun _ => (-1) ^ a) (e.symm (e (.inr j))))⁻¹ *
      (-1) ^ a = ξ (e (.inr j))
    rw [Equiv.symm_apply_apply, Sum.elim_inr, inv_mul_cancel_right]

/- English proof (translation)
Introduce `hE hV hS hT hM E _ _ _ n w ι _ a Z ξ ha hZ hmono`. Set `J` to `Σ i : ι, {s : Finset (Fin (n / 2)) // LocData.admitted n (a i) s}`. Set `ee : (j : J) → Fin (a j.1) ⊕ Fin (n - a j.1) ≃ Fin n` to `fun j => Classical.choose (exists_ex hE n (a j.1) j.2.1 j.2.2)`. Establish `hee` using `fun j : J => Classical.choose_spec (exists_ex hE n (a j.1) j.2.1 j.2.2)`. Set `S : J → Shuf n` to `fun j => shufOf w n (a j.1) j.2.1 j.2.2 (ee j) (hee j) ((-1) ^ (n - a j.1)) ((-1) ^ a j.1)`.

Set `Z' : (j : J) → Set ((Fin (S j).a → ℂˣ) × (Fin (S j).b → ℂˣ))` to `fun j => Z j.1`. Take `⟨c, hc1, hc2, hc3⟩` from `choiceT E n w J S Z' (chiN w ξ) (fun j => hZ j.1)`. Use `⟨c, hc1, hc2, ?_⟩` and prove the remaining obligations. Introduce `i s h ξa ξb hmem hne`. Set `j : J` to `⟨i, s, h⟩`.

Establish `hchi : chiOf w (S j) ξa ξb = chiN w ξ`. Use `hc3 j (ξa, ξb) hmem ?_` and prove the remaining obligations. Use `hne using 1` and compare the differences between its conclusion and the goal. Unfold `Finsupp.sum`. Use `Finset.sum_congr rfl (fun x hx => ?_)` and prove the remaining obligations.

Take `⟨h1, h2, h3⟩` from `hV E w n (a i) s h (ee j) (hee j) x (hc1 hx)`. Simplify using `only`. Rewrite using `[h1, h2, h3]`. Both sides reduce to the same expression. Conclude with `finish hT hM w n (a i) s h (ee j) (hee j) ξ ξa ξb hmono (hS E w n (a i) s h (ee j) (hee j)) hchi`.
-/
theorem UpperTheory.HeckeLevelFrameExistence.locC :
    PositivityTheory.Rg.BcB.F.Choice.ShufEx → PositivityTheory.Rg.BcB.F.Choice.VResStd → PositivityTheory.Rg.BcB.F.Choice.ShufStd → PositivityTheory.Rg.BcB.F.Tail.TargetAlg → PositivityTheory.Rg.BcB.F.Tail.MonoRes → UpperTheory.HeckeLevelFrameExistence.LocC := by
  intro hE hV hS hT hM E _ _ _ n w ι _ a Z ξ ha hZ hmono
  let J := Σ i : ι, {s : Finset (Fin (n / 2)) // LocData.admitted n (a i) s}
  let ee : (j : J) → Fin (a j.1) ⊕ Fin (n - a j.1) ≃ Fin n :=
    fun j => Classical.choose (exists_ex hE n (a j.1) j.2.1 j.2.2)
  have hee := fun j : J => Classical.choose_spec (exists_ex hE n (a j.1) j.2.1 j.2.2)
  let S : J → Shuf n := fun j =>
    shufOf w n (a j.1) j.2.1 j.2.2 (ee j) (hee j) ((-1) ^ (n - a j.1)) ((-1) ^ a j.1)
  let Z' : (j : J) → Set ((Fin (S j).a → ℂˣ) × (Fin (S j).b → ℂˣ)) := fun j => Z j.1
  obtain ⟨c, hc1, hc2, hc3⟩ := choiceT E n w J S Z' (chiN w ξ) (fun j => hZ j.1)
  refine ⟨c, hc1, hc2, ?_⟩
  intro i s h ξa ξb hmem hne
  let j : J := ⟨i, s, h⟩
  have hchi : chiOf w (S j) ξa ξb = chiN w ξ := by
    refine hc3 j (ξa, ξb) hmem ?_
    convert hne using 1
    unfold Finsupp.sum
    refine Finset.sum_congr rfl (fun x hx => ?_)
    obtain ⟨h1, h2, h3⟩ := hV E w n (a i) s h (ee j) (hee j) x (hc1 hx)
    dsimp only
    rw [h1, h2, h3]
    rfl
  exact finish hT hM w n (a i) s h (ee j) (hee j) ξ ξa ξb hmono (hS E w n (a i) s h (ee j) (hee j)) hchi
