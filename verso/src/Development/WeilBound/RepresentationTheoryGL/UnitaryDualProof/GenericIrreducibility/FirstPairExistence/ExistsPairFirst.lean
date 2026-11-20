import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.CentralProd2

noncomputable section

set_option synthInstance.maxHeartbeats 400000

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

namespace PositivityTheory.RgUd.Exp.Move2

open PositivityTheory.RgUd.Exp

section Lemmas

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Take `⟨e⟩` from `E`. Conclude with `hF r t V W A B hA hB (GlobalTheory.Parabolic.isIrreducible_of_equiv e.symm hπ)`.
-/
theorem factor_of_equiv (hF : FactorIrr k) {r t : ℕ} {V W U : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U] {A : Representation ℂ (GL (Fin r) k) V}
    {B : Representation ℂ (GL (Fin t) k) W} {π : Representation ℂ (GL (Fin (r + t)) k) U}
    (E : Nonempty ((prod₂ A B).Equiv π)) (hπ : π.IsIrreducible) (hA : IsSmooth A) (hB : IsSmooth B) :
    A.IsIrreducible ∧ B.IsIrreducible := by
  obtain ⟨e⟩ := E
  exact hF r t V W A B hA hB (GlobalTheory.Parabolic.isIrreducible_of_equiv e.symm hπ)

/- English proof (translation)
Rewrite using `[Fin.sum_univ_add]`. Simplify using `only [Fin.append_left, Fin.append_right]`.
-/
private theorem sum_fst_fin_append {k : Type} [Field k] [TopologicalSpace k] {m n : ℕ}
    (f : Fin m → IrrGL k) (g : Fin n → IrrGL k) :
    ∑ a, (Fin.append f g a).1 = (∑ a, (f a).1) + ∑ a, (g a).1 := by
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/- English proof (translation)
Substitute `e` using the available equality. Establish `hfg' : f = g`. Rewrite using `[hfg]`. Use function extensionality and compare the values at `a`. Simplify using the standard rewrite rules.

Substitute `hfg'` using the available equality. Conclude with `⟨Representation.Equiv.refl _⟩`.
-/
private theorem nonempty_prodIrr_equiv_of_eq_comp_cast {m n N : ℕ} (e : m = n) (f : Fin m → IrrGL k) (g : Fin n → IrrGL k)
    (hfg : f = g ∘ Fin.cast e) (hf : ∑ a, (f a).1 = N) (hg : ∑ a, (g a).1 = N) :
    Nonempty ((prodIrr f hf).Equiv (prodIrr g hg)) := by
  subst e
  have hfg' : f = g := by
    rw [hfg]
    funext a
    simp
  subst hfg'
  exact ⟨Representation.Equiv.refl _⟩

set_option maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in

/- English proof (translation)
Substitute `hq` using the available equality. Take `⟨s, hs⟩ : ∃ s, (i : ℕ) + (2 + s) = h` from `⟨h - i - 2, by have := j.2; omega⟩`. Take `⟨P, hP⟩ : ∃ P : Fin i → IrrGL k, ∀ a, P a = y ⟨a, by have` from `a.2; have := i.2; omega⟩ := ⟨_, fun _ => rfl⟩`. Take `⟨S, hS⟩ : ∃ S : Fin s → IrrGL k, ∀ b, S b = y ⟨i + 2 + b, by have` from `b.2; omega⟩ := ⟨_, fun _ => rfl⟩`. Establish `hcomp : Fin.append P (Fin.append ![y i, y j] S) = y ∘ Fin.cast hs`.

Use function extensionality and compare the values at `a`. Use `Fin.addCases (fun a => ?_) (fun b => ?_) a` and prove the remaining obligations. Rewrite using `[Fin.append_left, hP]`. Simplify using `only [Function.comp_apply]`. Use `congr 1`.

Rewrite using `[Fin.append_right]`. Use `Fin.addCases (fun c => ?_) (fun d => ?_) b` and prove the remaining obligations. Rewrite using `[Fin.append_left] fin_cases c`. Simplify using `only [Function.comp_apply] show y i = _`. Apply the tactic sequence `congr 1 <;> ext <;> simp`.

Simplify using `only [Function.comp_apply] show y j = _`. Apply the tactic sequence `congr 1 <;> ext <;> simp [hij]`. Rewrite using `[Fin.append_right, hS]`. Simplify using `only [Function.comp_apply]`. Apply the tactic sequence `congr 1 <;> ext <;> simp <;> omega`.

Establish `hQS : ∑ a, (Fin.append ![y i, y j] S a).1 = (∑ a, (![y i, y j] a).1) + ∑ a, (S a).1` using `sum_fst_fin_append _ _`. Establish `hAll : ∑ a, (Fin.append P (Fin.append ![y i, y j] S) a).1 = (∑ a, (P a).1) + ((∑ a, (![y i, y j] a).1) + ∑ a, (S a).1)`. Rewrite using `[sum_fst_fin_append, hQS]`. Establish `hsumY : ∑ a, (y a).1 = ∑ a, (Fin.append P (Fin.append ![y i, y j] S) a).1`. Rewrite using `[hcomp]`.

Conclude with `(Fintype.sum_equiv (finCongr hs) _ _ (fun _ => rfl)).symm`. Establish `hN : N = (∑ a, (P a).1) + ((∑ a, (![y i, y j] a).1) + ∑ a, (S a).1)`. Rewrite using `[← hd, hsumY, hAll]`. Substitute `hN` using the available equality. Take `⟨eC⟩` from `nonempty_prodIrr_equiv_of_eq_comp_cast hs _ y hcomp hAll hd`.

Establish `irrA` using `GlobalTheory.Parabolic.isIrreducible_of_equiv eC.symm hirr`. Take `⟨e2⟩` from `GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append k i (2 + s) _ _ P (Fin.append ![y i, y j] S) rfl hQS hAll`. Establish `irrQS` using `(factor_of_equiv hF ⟨e2⟩ irrA (isSmooth_prodIrr _ _) (isSmooth_prodIrr _ _)).2`. Take `⟨e3⟩` from `GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append k 2 s _ _ ![y i, y j] S rfl rfl hQS`. Conclude with `(factor_of_equiv hF ⟨e3⟩ irrQS (isSmooth_prodIrr _ _) (isSmooth_prodIrr _ _)).1`.
-/
theorem pair_irr (hF : FactorIrr k) {h N : ℕ} (y : Fin h → IrrGL k) (i j : Fin h) (hij : (j : ℕ) = i + 1)
    (hd : ∑ a, (y a).1 = N) (hirr : (prodIrr y hd).IsIrreducible) (q : ℕ) (hq : ∑ t, (![y i, y j] t).1 = q) :
    (prodIrr ![y i, y j] hq).IsIrreducible := by
  subst hq
  obtain ⟨s, hs⟩ : ∃ s, (i : ℕ) + (2 + s) = h := ⟨h - i - 2, by have := j.2; omega⟩
  obtain ⟨P, hP⟩ : ∃ P : Fin i → IrrGL k, ∀ a, P a = y ⟨a, by have := a.2; have := i.2; omega⟩ :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Fin s → IrrGL k, ∀ b, S b = y ⟨i + 2 + b, by have := b.2; omega⟩ :=
    ⟨_, fun _ => rfl⟩
  have hcomp : Fin.append P (Fin.append ![y i, y j] S) = y ∘ Fin.cast hs := by
    funext a
    refine Fin.addCases (fun a => ?_) (fun b => ?_) a
    · rw [Fin.append_left, hP]
      simp only [Function.comp_apply]
      congr 1
    · rw [Fin.append_right]
      refine Fin.addCases (fun c => ?_) (fun d => ?_) b
      · rw [Fin.append_left]
        fin_cases c
        · simp only [Function.comp_apply]
          show y i = _
          congr 1 <;> ext <;> simp
        · simp only [Function.comp_apply]
          show y j = _
          congr 1 <;> ext <;> simp [hij]
      · rw [Fin.append_right, hS]
        simp only [Function.comp_apply]
        congr 1 <;> ext <;> simp <;> omega
  have hQS : ∑ a, (Fin.append ![y i, y j] S a).1 = (∑ a, (![y i, y j] a).1) + ∑ a, (S a).1 :=
    sum_fst_fin_append _ _
  have hAll : ∑ a, (Fin.append P (Fin.append ![y i, y j] S) a).1 =
      (∑ a, (P a).1) + ((∑ a, (![y i, y j] a).1) + ∑ a, (S a).1) := by
    rw [sum_fst_fin_append, hQS]
  have hsumY : ∑ a, (y a).1 = ∑ a, (Fin.append P (Fin.append ![y i, y j] S) a).1 := by
    rw [hcomp]
    exact (Fintype.sum_equiv (finCongr hs) _ _ (fun _ => rfl)).symm
  have hN : N = (∑ a, (P a).1) + ((∑ a, (![y i, y j] a).1) + ∑ a, (S a).1) := by
    rw [← hd, hsumY, hAll]
  subst hN
  obtain ⟨eC⟩ := nonempty_prodIrr_equiv_of_eq_comp_cast hs _ y hcomp hAll hd
  have irrA := GlobalTheory.Parabolic.isIrreducible_of_equiv eC.symm hirr
  obtain ⟨e2⟩ := GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append k i (2 + s) _ _ P (Fin.append ![y i, y j] S) rfl hQS hAll
  have irrQS := (factor_of_equiv hF ⟨e2⟩ irrA (isSmooth_prodIrr _ _) (isSmooth_prodIrr _ _)).2
  obtain ⟨e3⟩ := GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append k 2 s _ _ ![y i, y j] S rfl rfl hQS
  exact (factor_of_equiv hF ⟨e3⟩ irrQS (isSmooth_prodIrr _ _) (isSmooth_prodIrr _ _)).1

def PR {h : ℕ} (f g : Fin h → IrrGL k) : Prop :=
  ∑ a, (f a).1 = ∑ a, (g a).1 ∧
    ∀ (N : ℕ) (hf : ∑ a, (f a).1 = N) (hg : ∑ a, (g a).1 = N),
      (prodIrr f hf).IsIrreducible → Nonempty ((prodIrr f hf).Equiv (prodIrr g hg))

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Use `⟨(Equiv.sum_comp (Equiv.swap i j) (fun a => (f a).1)).symm, ?_⟩` and prove the remaining obligations. Introduce `N hf hg hirr`. Use `GlobalTheory.CompanionTheory.ReorderRev.prodIrr_swap_adj f i j hij ?_ hf hg` and prove the remaining obligations. Introduce `q hq hq'`. Establish `hp` using `pair_irr hF f i j hij hf hirr q hq`.

Establish `hp'` using `hC (f i) (f j) q hq hq' hp`. Conclude with `GlobalTheory.CompanionTheory.BZSegComm.prodIrr_swap_of_isIrreducible PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top ![f i, f j] ![f j, f i] rfl rfl hq hq' hp hp'`.
-/
theorem pr_swap (hF : FactorIrr k) (hC : Comm2Irr k) {h : ℕ} (f : Fin h → IrrGL k) (i j : Fin h)
    (hij : (j : ℕ) = i + 1) : PR f (f ∘ Equiv.swap i j) := by
  refine ⟨(Equiv.sum_comp (Equiv.swap i j) (fun a => (f a).1)).symm, ?_⟩
  intro N hf hg hirr
  refine GlobalTheory.CompanionTheory.ReorderRev.prodIrr_swap_adj f i j hij ?_ hf hg
  intro q hq hq'
  have hp := pair_irr hF f i j hij hf hirr q hq
  have hp' := hC (f i) (f j) q hq hq' hp
  exact GlobalTheory.CompanionTheory.BZSegComm.prodIrr_swap_of_isIrreducible PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
    ![f i, f j] ![f j, f i] rfl rfl hq hq' hp hp'

/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl, fun _ _ _ _ => ⟨Representation.Equiv.refl _⟩⟩`.
-/
private theorem PR_refl {h : ℕ} (f : Fin h → IrrGL k) : PR f f :=
  ⟨rfl, fun _ _ _ _ => ⟨Representation.Equiv.refl _⟩⟩

/- English proof (translation)
Use `set_option maxHeartbeats 1600000 in`. Use `⟨h1.1.trans h2.1, fun N hf hg' hirr => ?_⟩` and prove the remaining obligations. Establish `hg : ∑ a, (g a).1 = N` using `h1.1.symm.trans hf`. Take `⟨e1⟩` from `h1.2 N hf hg hirr`. Establish `hirr2 : (prodIrr g hg).IsIrreducible` using `GlobalTheory.Parabolic.isIrreducible_of_equiv e1 hirr`.

Take `⟨e2⟩` from `h2.2 N hg hg' hirr2`. Conclude with `⟨e1.trans e2⟩`.
-/
private theorem PR_trans {h : ℕ} {f g g' : Fin h → IrrGL k} (h1 : PR f g) (h2 : PR g g') : PR f g' := by
  set_option maxHeartbeats 1600000 in
  refine ⟨h1.1.trans h2.1, fun N hf hg' hirr => ?_⟩
  have hg : ∑ a, (g a).1 = N := h1.1.symm.trans hf
  obtain ⟨e1⟩ := h1.2 N hf hg hirr
  have hirr2 : (prodIrr g hg).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv e1 hirr
  obtain ⟨e2⟩ := h2.2 N hg hg' hirr2
  exact ⟨e1.trans e2⟩

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Consider the cases of `h with`. Consider the case `zero`. Establish `hc : f ∘ σ = f` using `funext (fun a => a.elim0)`. Rewrite using `[hc]`. Conclude with `PR_refl f`.

Consider the case `succ n`. Establish `hmem : σ ∈ Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ)`. Rewrite using `[Equiv.Perm.mclosure_swap_castSucc_succ]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hmem using Submonoid.closure_induction generalizing f with`.

Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`. Conclude with `pr_swap hF hC f _ _ (by simp)`. Consider the case `one`. Rewrite using `[Equiv.Perm.coe_one, Function.comp_id]`.

Conclude with `PR_refl f`. Consider the case `mul x y _ _ ihx ihy`. Rewrite using `[Equiv.Perm.coe_mul]`. Conclude with `PR_trans (ihx f) (ihy (f ∘ x))`.
-/
theorem pr_perm (hF : FactorIrr k) (hC : Comm2Irr k) {h : ℕ} (f : Fin h → IrrGL k) (σ : Equiv.Perm (Fin h)) :
    PR f (f ∘ σ) := by
  cases h with
  | zero =>
    have hc : f ∘ σ = f := funext (fun a => a.elim0)
    rw [hc]
    exact PR_refl f
  | succ n =>
    have hmem : σ ∈ Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    induction hmem using Submonoid.closure_induction generalizing f with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact pr_swap hF hC f _ _ (by simp)
    | one =>
      rw [Equiv.Perm.coe_one, Function.comp_id]
      exact PR_refl f
    | mul x y _ _ ihx ihy =>
      rw [Equiv.Perm.coe_mul]
      exact PR_trans (ihx f) (ihy (f ∘ x))

/- English proof (translation)
Substitute `e` using the available equality. Establish `hfg' : f = g`. Rewrite using `[hfg]`. Use function extensionality and compare the values at `a`. Simplify using the standard rewrite rules.

Substitute `hfg'` using the available equality. Conclude with `⟨Representation.Equiv.refl _⟩`.
-/
theorem prodIrr_cast {m n N : ℕ} (e : m = n) (f : Fin m → IrrGL k) (g : Fin n → IrrGL k)
    (hfg : f = g ∘ Fin.cast e) (hf : ∑ a, (f a).1 = N) (hg : ∑ a, (g a).1 = N) :
    Nonempty ((prodIrr f hf).Equiv (prodIrr g hg)) := by
  subst e
  have hfg' : f = g := by
    rw [hfg]
    funext a
    simp
  subst hfg'
  exact ⟨Representation.Equiv.refl _⟩

def lastPerm {r : ℕ} (j : Fin (r + 1)) : Equiv.Perm (Fin (r + 1)) :=
  finSuccEquivLast.trans (finSuccEquiv' j).symm

def firstPerm {r : ℕ} (j : Fin (r + 1)) : Equiv.Perm (Fin (r + 1)) :=
  (finSuccEquiv r).trans (finSuccEquiv' j).symm

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `Fin.addCases (fun i => ?_) (fun i => ?_) i` and prove the remaining obligations. Rewrite using `[Fin.append_left]`. Establish `e : (Fin.castAdd 1 i : Fin (r + 1)) = Fin.castSucc i` using `rfl`. Simplify using `[lastPerm, e]`.

Rewrite using `[Fin.append_right]`. Establish `hi : i = 0` using `Subsingleton.elim _ _`. Substitute `hi` using the available equality. Establish `e : (Fin.natAdd r (0 : Fin 1) : Fin (r + 1)) = Fin.last r` using `rfl`. Simplify using `[lastPerm, e]`.
-/
theorem comp_lastPerm {r : ℕ} {α : Type*} (x : Fin (r + 1) → α) (j : Fin (r + 1)) :
    x ∘ lastPerm j = Fin.append (x ∘ j.succAbove) (fun _ : Fin 1 => x j) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [Fin.append_left]
    have e : (Fin.castAdd 1 i : Fin (r + 1)) = Fin.castSucc i := rfl
    simp [lastPerm, e]
  · rw [Fin.append_right]
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    have e : (Fin.natAdd r (0 : Fin 1) : Fin (r + 1)) = Fin.last r := rfl
    simp [lastPerm, e]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify using `[firstPerm]`. Simplify using `[firstPerm]`.
-/
theorem comp_firstPerm {r : ℕ} {α : Type*} (x : Fin (r + 1) → α) (j : Fin (r + 1)) :
    x ∘ firstPerm j = Fin.cons (x j) (x ∘ j.succAbove) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [firstPerm]
  · simp [firstPerm]

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Take `⟨e⟩` from `E`. Take `⟨eB⟩` from `EB`. Establish `hp : ∑ a, (![IrrGL.of A hAs hAi, x₀] a).1 = (IrrGL.of A hAs hAi).1 + x₀.1`. Simplify using `[Fin.sum_univ_two]`. Take `⟨e3⟩` from `nonempty_prod₂_equiv_prodIrr_pair (IrrGL.of A hAs hAi) x₀ hp`.

Conclude with `⟨IrrGL.of A hAs hAi, hp, ⟨e.symm.trans ((prod₂Equiv (IrrGL.equivOf A hAs hAi) eB.symm).trans e3)⟩⟩`.
-/
theorem exists_pair_last (x₀ : IrrGL k) {M : ℕ} {V W U : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U] (A : Representation ℂ (GL (Fin M) k) V)
    (B : Representation ℂ (GL (Fin x₀.1) k) W) (π : Representation ℂ (GL (Fin (M + x₀.1)) k) U)
    (hAs : IsSmooth A) (hAi : A.IsIrreducible) (E : Nonempty ((prod₂ A B).Equiv π))
    (EB : Nonempty (x₀.rep.Equiv B)) :
    ∃ (y : IrrGL k) (hd2 : ∑ a, (![y, x₀] a).1 = M + x₀.1), Nonempty (π.Equiv (prodIrr ![y, x₀] hd2)) := by
  obtain ⟨e⟩ := E
  obtain ⟨eB⟩ := EB
  have hp : ∑ a, (![IrrGL.of A hAs hAi, x₀] a).1 = (IrrGL.of A hAs hAi).1 + x₀.1 := by
    simp [Fin.sum_univ_two]
  obtain ⟨e3⟩ := nonempty_prod₂_equiv_prodIrr_pair (IrrGL.of A hAs hAi) x₀ hp
  exact ⟨IrrGL.of A hAs hAi, hp, ⟨e.symm.trans ((prod₂Equiv (IrrGL.equivOf A hAs hAi) eB.symm).trans e3)⟩⟩

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Take `⟨e⟩` from `E`. Take `⟨eA⟩` from `EA`. Establish `hp : ∑ a, (![x₀, IrrGL.of B hBs hBi] a).1 = x₀.1 + (IrrGL.of B hBs hBi).1`. Simplify using `[Fin.sum_univ_two]`. Take `⟨e3⟩` from `nonempty_prod₂_equiv_prodIrr_pair x₀ (IrrGL.of B hBs hBi) hp`.

Conclude with `⟨IrrGL.of B hBs hBi, hp, ⟨e.symm.trans ((prod₂Equiv eA.symm (IrrGL.equivOf B hBs hBi)).trans e3)⟩⟩`.
-/
theorem exists_pair_first (x₀ : IrrGL k) {M : ℕ} {V W U : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U] (A : Representation ℂ (GL (Fin x₀.1) k) V)
    (B : Representation ℂ (GL (Fin M) k) W) (π : Representation ℂ (GL (Fin (x₀.1 + M)) k) U)
    (hBs : IsSmooth B) (hBi : B.IsIrreducible) (E : Nonempty ((prod₂ A B).Equiv π))
    (EA : Nonempty (x₀.rep.Equiv A)) :
    ∃ (y : IrrGL k) (hd2 : ∑ a, (![x₀, y] a).1 = x₀.1 + M), Nonempty (π.Equiv (prodIrr ![x₀, y] hd2)) := by
  obtain ⟨e⟩ := E
  obtain ⟨eA⟩ := EA
  have hp : ∑ a, (![x₀, IrrGL.of B hBs hBi] a).1 = x₀.1 + (IrrGL.of B hBs hBi).1 := by
    simp [Fin.sum_univ_two]
  obtain ⟨e3⟩ := nonempty_prod₂_equiv_prodIrr_pair x₀ (IrrGL.of B hBs hBi) hp
  exact ⟨IrrGL.of B hBs hBi, hp, ⟨e.symm.trans ((prod₂Equiv eA.symm (IrrGL.equivOf B hBs hBi)).trans e3)⟩⟩

end Lemmas

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option maxHeartbeats 1600000 in
/- English proof (translation)
Introduce `hF hC h N x hd hirr j`. Consider the cases of `h with`. Consider the case `zero => exact j.elim0`. Consider the case `succ r`. Establish `hcomp` using `comp_lastPerm x j`.

Establish `hy : ∑ _a : Fin 1, (x j).1 = (x j).1` using `by simp`. Establish `hApp : ∑ a, (Fin.append (x ∘ j.succAbove) (fun _ : Fin 1 => x j) a).1 = (∑ a, ((x ∘ j.succAbove) a).1) + (x j).1`. Rewrite using `[Fin.sum_univ_add]`. Simplify using `only [Fin.append_left, Fin.append_right]`. Rewrite using `[hy]`.

Establish `hsumPerm : ∑ a, ((x ∘ lastPerm j) a).1 = ∑ a, (x a).1` using `Equiv.sum_comp (lastPerm j) (fun a => (x a).1)`. Establish `hN : N = (∑ a, ((x ∘ j.succAbove) a).1) + (x j).1`. Rewrite using `[← hd, ← hsumPerm, hcomp, hApp]`. Substitute `hN` using the available equality. Take `⟨e1⟩` from `(pr_perm hF hC x (lastPerm j)).2 _ hd (hsumPerm.trans hd) hirr`.

Take `⟨eC⟩` from `prodIrr_cast rfl (x ∘ lastPerm j) (Fin.append (x ∘ j.succAbove) (fun _ : Fin 1 => x j)) (by rw [hcomp]; rfl) (hsumPerm.trans hd) hApp`. Take `⟨e2⟩` from `GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append k r 1 _ _ (x ∘ j.succAbove) (fun _ : Fin 1 => x j) rfl hy hApp`. Take `⟨eB⟩` from `nonempty_equiv_prodIrr_one (x j) hy`. Establish `E` using `e2.trans (eC.symm.trans e1.symm)`. Establish `hAi` using `(factor_of_equiv hF ⟨E⟩ hirr (isSmooth_prodIrr _ _) (isSmooth_prodIrr _ _)).1`.

Conclude with `exists_pair_last (x j) _ _ _ (isSmooth_prodIrr _ _) hAi ⟨E⟩ ⟨eB⟩`.
-/
theorem moveLast : FactorIrr k → Comm2Irr k → MoveLast k := by
  intro hF hC h N x hd hirr j
  cases h with
  | zero => exact j.elim0
  | succ r =>
    have hcomp := comp_lastPerm x j
    have hy : ∑ _a : Fin 1, (x j).1 = (x j).1 := by simp
    have hApp : ∑ a, (Fin.append (x ∘ j.succAbove) (fun _ : Fin 1 => x j) a).1 =
        (∑ a, ((x ∘ j.succAbove) a).1) + (x j).1 := by
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [hy]
    have hsumPerm : ∑ a, ((x ∘ lastPerm j) a).1 = ∑ a, (x a).1 :=
      Equiv.sum_comp (lastPerm j) (fun a => (x a).1)
    have hN : N = (∑ a, ((x ∘ j.succAbove) a).1) + (x j).1 := by
      rw [← hd, ← hsumPerm, hcomp, hApp]
    subst hN
    obtain ⟨e1⟩ := (pr_perm hF hC x (lastPerm j)).2 _ hd (hsumPerm.trans hd) hirr
    obtain ⟨eC⟩ := prodIrr_cast rfl (x ∘ lastPerm j) (Fin.append (x ∘ j.succAbove) (fun _ : Fin 1 => x j))
      (by rw [hcomp]; rfl) (hsumPerm.trans hd) hApp
    obtain ⟨e2⟩ := GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append k r 1 _ _ (x ∘ j.succAbove) (fun _ : Fin 1 => x j) rfl hy hApp
    obtain ⟨eB⟩ := nonempty_equiv_prodIrr_one (x j) hy
    have E := e2.trans (eC.symm.trans e1.symm)
    have hAi := (factor_of_equiv hF ⟨E⟩ hirr (isSmooth_prodIrr _ _) (isSmooth_prodIrr _ _)).1
    exact exists_pair_last (x j) _ _ _ (isSmooth_prodIrr _ _) hAi ⟨E⟩ ⟨eB⟩

set_option maxHeartbeats 1600000 in
/- English proof (translation)
Introduce `hF hC h N x hd hirr j`. Consider the cases of `h with`. Consider the case `zero => exact j.elim0`. Consider the case `succ r`. Establish `hfg : Fin.append (fun _ : Fin 1 => x j) (x ∘ j.succAbove) = (x ∘ firstPerm j) ∘ Fin.cast (Nat.add_comm 1 r)`.

Rewrite using `[comp_firstPerm]`. Use function extensionality and compare the values at `a`. Use `Fin.addCases (fun a => ?_) (fun b => ?_) a` and prove the remaining obligations. Rewrite using `[Fin.append_left]`. Establish `e0 : Fin.cast (Nat.add_comm 1 r) (Fin.castAdd r a) = 0`.

Use `ext`. Use `a.2` as an intermediate fact. Apply the tactic sequence `simp <;> omega`. Simplify using `only [Function.comp_apply, e0, Fin.cons_zero]`. Rewrite using `[Fin.append_right]`.

Establish `e1 : Fin.cast (Nat.add_comm 1 r) (Fin.natAdd 1 b) = b.succ`. Use `ext`. Simplify using `[Nat.add_comm]`. Simplify using `only [Function.comp_apply, e1, Fin.cons_succ]`. Establish `hy : ∑ _a : Fin 1, (x j).1 = (x j).1` using `by simp`.

Establish `hApp : ∑ a, (Fin.append (fun _ : Fin 1 => x j) (x ∘ j.succAbove) a).1 = (x j).1 + ∑ a, ((x ∘ j.succAbove) a).1`. Rewrite using `[Fin.sum_univ_add]`. Simplify using `only [Fin.append_left, Fin.append_right]`. Rewrite using `[hy]`. Establish `hsumPerm : ∑ a, ((x ∘ firstPerm j) a).1 = ∑ a, (x a).1` using `Equiv.sum_comp (firstPerm j) (fun a => (x a).1)`.

Establish `hsumC : ∑ a, (Fin.append (fun _ : Fin 1 => x j) (x ∘ j.succAbove) a).1 = ∑ a, ((x ∘ firstPerm j) a).1`. Rewrite using `[hfg]`. Conclude with `Fintype.sum_equiv (finCongr (Nat.add_comm 1 r)) _ _ (fun _ => rfl)`. Establish `hN : N = (x j).1 + ∑ a, ((x ∘ j.succAbove) a).1`. Rewrite using `[← hd, ← hsumPerm, ← hsumC, hApp]`.

Substitute `hN` using the available equality. Take `⟨e1⟩` from `(pr_perm hF hC x (firstPerm j)).2 _ hd (hsumPerm.trans hd) hirr`. Take `⟨eC⟩` from `prodIrr_cast (Nat.add_comm 1 r) (Fin.append (fun _ : Fin 1 => x j) (x ∘ j.succAbove)) (x ∘ firstPerm j) hfg hApp (hsumPerm.trans hd)`. Take `⟨e2⟩` from `GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append k 1 r _ _ (fun _ : Fin 1 => x j) (x ∘ j.succAbove) hy rfl hApp`. Take `⟨eA⟩` from `nonempty_equiv_prodIrr_one (x j) hy`.

Establish `E` using `e2.trans (eC.trans e1.symm)`. Establish `hBi` using `(factor_of_equiv hF ⟨E⟩ hirr (isSmooth_prodIrr _ _) (isSmooth_prodIrr _ _)).2`. Conclude with `exists_pair_first (x j) _ _ _ (isSmooth_prodIrr _ _) hBi ⟨E⟩ ⟨eA⟩`.
-/
theorem moveFirst : FactorIrr k → Comm2Irr k → MoveFirst k := by
  intro hF hC h N x hd hirr j
  cases h with
  | zero => exact j.elim0
  | succ r =>
    have hfg : Fin.append (fun _ : Fin 1 => x j) (x ∘ j.succAbove) =
        (x ∘ firstPerm j) ∘ Fin.cast (Nat.add_comm 1 r) := by
      rw [comp_firstPerm]
      funext a
      refine Fin.addCases (fun a => ?_) (fun b => ?_) a
      · rw [Fin.append_left]
        have e0 : Fin.cast (Nat.add_comm 1 r) (Fin.castAdd r a) = 0 := by
          ext
          have := a.2
          simp <;> omega
        simp only [Function.comp_apply, e0, Fin.cons_zero]
      · rw [Fin.append_right]
        have e1 : Fin.cast (Nat.add_comm 1 r) (Fin.natAdd 1 b) = b.succ := by
          ext
          simp [Nat.add_comm]
        simp only [Function.comp_apply, e1, Fin.cons_succ]
    have hy : ∑ _a : Fin 1, (x j).1 = (x j).1 := by simp
    have hApp : ∑ a, (Fin.append (fun _ : Fin 1 => x j) (x ∘ j.succAbove) a).1 =
        (x j).1 + ∑ a, ((x ∘ j.succAbove) a).1 := by
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [hy]
    have hsumPerm : ∑ a, ((x ∘ firstPerm j) a).1 = ∑ a, (x a).1 :=
      Equiv.sum_comp (firstPerm j) (fun a => (x a).1)
    have hsumC : ∑ a, (Fin.append (fun _ : Fin 1 => x j) (x ∘ j.succAbove) a).1 =
        ∑ a, ((x ∘ firstPerm j) a).1 := by
      rw [hfg]
      exact Fintype.sum_equiv (finCongr (Nat.add_comm 1 r)) _ _ (fun _ => rfl)
    have hN : N = (x j).1 + ∑ a, ((x ∘ j.succAbove) a).1 := by
      rw [← hd, ← hsumPerm, ← hsumC, hApp]
    subst hN
    obtain ⟨e1⟩ := (pr_perm hF hC x (firstPerm j)).2 _ hd (hsumPerm.trans hd) hirr
    obtain ⟨eC⟩ := prodIrr_cast (Nat.add_comm 1 r) (Fin.append (fun _ : Fin 1 => x j) (x ∘ j.succAbove))
      (x ∘ firstPerm j) hfg hApp (hsumPerm.trans hd)
    obtain ⟨e2⟩ := GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append k 1 r _ _ (fun _ : Fin 1 => x j) (x ∘ j.succAbove) hy rfl hApp
    obtain ⟨eA⟩ := nonempty_equiv_prodIrr_one (x j) hy
    have E := e2.trans (eC.trans e1.symm)
    have hBi := (factor_of_equiv hF ⟨E⟩ hirr (isSmooth_prodIrr _ _) (isSmooth_prodIrr _ _)).2
    exact exists_pair_first (x j) _ _ _ (isSmooth_prodIrr _ _) hBi ⟨E⟩ ⟨eA⟩

end PositivityTheory.RgUd.Exp.Move2

end
