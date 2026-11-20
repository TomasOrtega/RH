import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicProductEquivProductOfPartition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTwoBlocksEmptyProductLeft
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw

set_option synthInstance.maxHeartbeats 400000
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.ProdReorder

namespace PositivityTheory.Rg.BcB.F.RS.JB

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

structure RB (N : ℕ) : Type 1 where
  V : Type
  [ag : AddCommGroup V]
  [md : Module ℂ V]
  ρ : Representation ℂ (GL (Fin N) k) V
  sm : IsSmooth ρ

attribute [instance] RB.ag RB.md

def Iso {N : ℕ} (A B : RB k N) : Prop := Nonempty (A.ρ.Equiv B.ρ)

/- English proof (translation)
Assemble the required witnesses or components as `⟨.refl _⟩`.
-/
theorem Iso.refl {N : ℕ} (A : RB k N) : Iso A A := ⟨.refl _⟩

/- English proof (translation)
The claim follows from `h.elim fun a => ⟨a.symm⟩`.
-/
theorem Iso.symm {N : ℕ} {A B : RB k N} (h : Iso A B) : Iso B A := h.elim fun a => ⟨a.symm⟩

/- English proof (translation)
Conclude with `eqv_trans h h'`.
-/
theorem Iso.trans {N : ℕ} {A B C : RB k N} (h : Iso A B) (h' : Iso B C) : Iso A C := by
  exact eqv_trans h h'

def one (u : IrrGL k) : RB k u.1 := ⟨_, u.rep, u.2.rep.smooth⟩

def mp {c N : ℕ} (z : Fin c → IrrGL k) (e : (Σ a, Fin (z a).1) ≃ Fin N) : RB k N :=
  ⟨_, multiProd e fun a => (z a).rep, isSmooth_parInd _ _⟩

def i2 {r t N : ℕ} (h : r + t = N) (A : RB k r) (B : RB k t) : RB k N :=
  ⟨_, ind₂ (stdSum h) (extTensor A.ρ B.ρ), isSmooth_parInd _ _⟩

/- English proof (translation)
The claim follows from `ind₂_congr h (π₁ := A.ρ) (σ₁ := A'.ρ) (π₂ := B.ρ) (σ₂ := B'.ρ) a b`.
-/
theorem parabolic_induction_congr {r t N : ℕ} (h : r + t = N) {A A' : RB k r} {B B' : RB k t} (a : Iso A A') (b : Iso B B') :
    Iso (i2 h A B) (i2 h A' B') := ind₂_congr h (π₁ := A.ρ) (σ₁ := A'.ρ) (π₂ := B.ρ) (σ₂ := B'.ρ) a b

/- English proof (translation)
The claim follows from `ind₂_assoc' h₁ h₂ h₃ h₄ A.ρ B.ρ C.ρ A.sm B.sm C.sm`.
-/
theorem parabolic_induction_assoc {r s t M M' N : ℕ} (h₁ : r + s = M) (h₂ : M + t = N) (h₃ : s + t = M') (h₄ : r + M' = N)
    (A : RB k r) (B : RB k s) (C : RB k t) : Iso (i2 h₂ (i2 h₁ A B) C) (i2 h₄ A (i2 h₃ B C)) :=
  ind₂_assoc' h₁ h₂ h₃ h₄ A.ρ B.ρ C.ρ A.sm B.sm C.sm

/- English proof (translation)
The claim follows from `multiProd_placing e e' fun a => (z a).rep`.
-/
theorem mp_placing {c N : ℕ} (z : Fin c → IrrGL k) (e e' : (Σ a, Fin (z a).1) ≃ Fin N) : Iso (mp z e) (mp z e') :=
  multiProd_placing e e' fun a => (z a).rep

/- English proof (translation)
The claim follows from `multiProd_head (k := k) (fun a => (z a).rep) e h e'`.
-/
theorem mp_head {c T N : ℕ} (z : Fin (c + 1) → IrrGL k) (e : (Σ a, Fin (z a).1) ≃ Fin N) (h : (z 0).1 + T = N)
    (e' : (Σ a : Fin c, Fin (z a.succ).1) ≃ Fin T) : Iso (mp z e) (i2 h (one (z 0)) (mp (fun a => z a.succ) e')) :=
  multiProd_head (k := k) (fun a => (z a).rep) e h e'

/- English proof (translation)
The claim follows from `ind₂_unit_left k r t h A.V A.ρ A.sm (fun a => (x a).1) _ (fun a => (x a).rep) e`.
-/
theorem parabolic_induction_unit {r t : ℕ} (h : t + r = r) (A : RB k r) (x : Fin 0 → IrrGL k) (e : (Σ a, Fin (x a).1) ≃ Fin t) :
    Iso (i2 h (mp x e) A) A :=
  ind₂_unit_left k r t h A.V A.ρ A.sm (fun a => (x a).1) _ (fun a => (x a).rep) e

/- English proof (translation)
Simplify using `using Fintype.card_congr e`.
-/
theorem card_eq {c N : ℕ} (z : Fin c → IrrGL k) (e : (Σ a, Fin (z a).1) ≃ Fin N) : ∑ a, (z a).1 = N := by
  simpa using Fintype.card_congr e

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, ⟨finSigmaFinEquiv⟩⟩`.
-/
theorem ex_e {c : ℕ} (z : Fin c → IrrGL k) : ∃ N, Nonempty ((Σ a, Fin (z a).1) ≃ Fin N) := ⟨_, ⟨finSigmaFinEquiv⟩⟩

attribute [irreducible] Iso one mp i2

/- English proof (translation)
Substitute `hu` using the available equality. Conclude with `Iso.refl _`.
-/
theorem head_congr {u u' : IrrGL k} (hu : u = u') {T N : ℕ} (h : u.1 + T = N) (h' : u'.1 + T = N) (B : RB k T) :
    Iso (i2 h (one u) B) (i2 h' (one u') B) := by
  subst hu
  exact Iso.refl _

/- English proof (translation)
Introduce `s₁`. Proceed by induction on `s₁ with`. Consider the case `zero`. Introduce `s₂ c z x y hz N r t h e e₁ e₂`. Establish `hr : r = 0`.

Use `Fintype.card_congr e₁` as an intermediate fact. Simplify using `using this.symm`. Substitute `hr` using the available equality. Establish `hN : N = t` using `by omega`. Substitute `hN` using the available equality.

Establish `hzy : List.ofFn z = List.ofFn y` using `by simpa using hz`. Rewrite `hzy` using `[List.ofFn_inj']`. Consider the cases of `hzy`. Conclude with `Iso.trans (mp_placing _ e e₂) (Iso.symm (parabolic_induction_unit h _ x e₁))`. Consider the case `succ n ih`.

Introduce `s₂ c z x y hz N r t h e e₁ e₂`. Choose the witnesses or unpack the hypotheses as in `⟨c', rfl⟩ : ∃ c', c = c' + 1 := by`. Consider the cases of `c with`. Consider the case `zero => simp [List.ofFn_succ] at hz`. Consider the case `succ c' => exact ⟨c', rfl⟩`.

Rewrite `hz` using `[List.ofFn_succ, List.ofFn_succ, List.cons_append]`. Take `⟨h0, htail⟩` from `List.cons.inj hz`. Take `⟨T, ⟨e'⟩⟩` from `ex_e (fun a : Fin c' => z a.succ)`. Take `⟨r', ⟨e₁'⟩⟩` from `ex_e (fun a : Fin n => x a.succ)`. Establish `hT : (z 0).1 + T = N`.

Establish `h1` using `card_eq z e`. Establish `h2` using `card_eq _ e'`. Rewrite `h1` using `[Fin.sum_univ_succ]`. Use linear arithmetic over natural numbers and integers. Establish `hr' : (x 0).1 + r' = r`.

Establish `h1` using `card_eq x e₁`. Establish `h2` using `card_eq _ e₁'`. Rewrite `h1` using `[Fin.sum_univ_succ]`. Use linear arithmetic over natural numbers and integers. Establish `hT' : r' + t = T`.

Rewrite `hT` using `[h0]`. Use linear arithmetic over natural numbers and integers. Establish `h₁ : (z 0).1 + r' = r`. Rewrite using `[h0]`. Conclude with `hr'`.

Establish `s1` using `mp_head z e hT e'`. Establish `s2` using `parabolic_induction_congr hT (Iso.refl (one (z 0))) (ih s₂ c' (fun a => z a.succ) (fun a => x a.succ) y htail hT' e' e₁' e₂)`. Establish `s3` using `Iso.symm (parabolic_induction_assoc h₁ h hT' hT (one (z 0)) (mp (fun a => x a.succ) e₁') (mp y e₂))`. Establish `s4 : Iso (i2 h₁ (one (z 0)) (mp (fun a => x a.succ) e₁')) (mp x e₁)` using `Iso.trans (head_congr h0 h₁ hr' _) (Iso.symm (mp_head x e₁ hr' e₁'))`. Establish `s5` using `parabolic_induction_congr h s4 (Iso.refl (mp y e₂))`.

Conclude with `Iso.trans s1 (Iso.trans s2 (Iso.trans s3 s5))`.
-/
theorem stagesB : ∀ (s₁ s₂ c : ℕ) (z : Fin c → IrrGL k) (x : Fin s₁ → IrrGL k) (y : Fin s₂ → IrrGL k),
    List.ofFn z = List.ofFn x ++ List.ofFn y → ∀ {N r t : ℕ} (h : r + t = N) (e : (Σ a, Fin (z a).1) ≃ Fin N)
      (e₁ : (Σ a, Fin (x a).1) ≃ Fin r) (e₂ : (Σ a, Fin (y a).1) ≃ Fin t), Iso (mp z e) (i2 h (mp x e₁) (mp y e₂)) := by
  intro s₁
  induction s₁ with
  | zero =>
    intro s₂ c z x y hz N r t h e e₁ e₂
    have hr : r = 0 := by
      have := Fintype.card_congr e₁
      simpa using this.symm
    subst hr
    have hN : N = t := by omega
    subst hN
    have hzy : List.ofFn z = List.ofFn y := by simpa using hz
    rw [List.ofFn_inj'] at hzy
    cases hzy
    exact Iso.trans (mp_placing _ e e₂) (Iso.symm (parabolic_induction_unit h _ x e₁))
  | succ n ih =>
    intro s₂ c z x y hz N r t h e e₁ e₂
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := by
      cases c with
      | zero => simp [List.ofFn_succ] at hz
      | succ c' => exact ⟨c', rfl⟩
    rw [List.ofFn_succ, List.ofFn_succ, List.cons_append] at hz
    obtain ⟨h0, htail⟩ := List.cons.inj hz
    obtain ⟨T, ⟨e'⟩⟩ := ex_e (fun a : Fin c' => z a.succ)
    obtain ⟨r', ⟨e₁'⟩⟩ := ex_e (fun a : Fin n => x a.succ)
    have hT : (z 0).1 + T = N := by
      have h1 := card_eq z e
      have h2 := card_eq _ e'
      rw [Fin.sum_univ_succ] at h1
      omega
    have hr' : (x 0).1 + r' = r := by
      have h1 := card_eq x e₁
      have h2 := card_eq _ e₁'
      rw [Fin.sum_univ_succ] at h1
      omega
    have hT' : r' + t = T := by
      rw [h0] at hT
      omega
    have h₁ : (z 0).1 + r' = r := by
      rw [h0]
      exact hr'
    have s1 := mp_head z e hT e'
    have s2 := parabolic_induction_congr hT (Iso.refl (one (z 0))) (ih s₂ c' (fun a => z a.succ) (fun a => x a.succ) y htail hT' e' e₁' e₂)
    have s3 := Iso.symm (parabolic_induction_assoc h₁ h hT' hT (one (z 0)) (mp (fun a => x a.succ) e₁') (mp y e₂))
    have s4 : Iso (i2 h₁ (one (z 0)) (mp (fun a => x a.succ) e₁')) (mp x e₁) :=
      Iso.trans (head_congr h0 h₁ hr' _) (Iso.symm (mp_head x e₁ hr' e₁'))
    have s5 := parabolic_induction_congr h s4 (Iso.refl (mp y e₂))
    exact Iso.trans s1 (Iso.trans s2 (Iso.trans s3 s5))

end PositivityTheory.Rg.BcB.F.RS.JB

end
