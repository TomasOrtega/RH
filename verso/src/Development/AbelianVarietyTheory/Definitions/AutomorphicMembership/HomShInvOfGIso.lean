import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap

set_option maxHeartbeats 800000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.BoundaryLocalData GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM.Check

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

/- English proof (translation)
Use `Real.sSup_nonneg ?_` and prove the remaining obligations. Introduce and unpack `r ⟨U, -, h, k, g, lam, -, rfl⟩`. Check the signs of the components of the expression.
-/
theorem nrm_nonneg (ct : At S κ p) {Z : ct.Mdl} (F : ct.Sh Z) (f : ct.Sec F) (y : ct.Pt Z) : 0 ≤ ct.nrm F f y := by
  refine Real.sSup_nonneg ?_
  rintro r ⟨U, -, h, k, g, lam, -, rfl⟩
  positivity

/- English proof (translation)
Establish `h1 : ∀ x, IsCMField.complexConj D.host.E x = D.host.conj x` using `fun x => by`. Apply `D.host.φ₀.injective` to reduce the goal to its premises. Rewrite using `[IsCMField.complexEmbedding_complexConj]`. Conclude with `(D.host.conjE_apply _ x).symm`. Establish `h2 : c' = A.H.bar c` using `Subtype.ext (by`.

Express the relevant statement in the definitionally equal form `(c' : D.host.E) = ((A.H.bar c : 𝓞 D.host.E) : D.host.E)`. Rewrite using `[A.H.bar_eq, h1, h])`. Substitute `h2` using the available equality. Both sides reduce to the same expression.
-/
theorem phi_conj (ct : At S κ p) {Z : ct.Mdl} (y : ct.Pt Z) (c c' : 𝓞 D.host.E)
    (h : (c' : D.host.E) = D.host.conj (c : D.host.E)) (a : ct.Ylat y) : ct.phi y (c' • a) = c • ct.phi y a := by
  have h1 : ∀ x, IsCMField.complexConj D.host.E x = D.host.conj x := fun x => by
    apply D.host.φ₀.injective
    rw [IsCMField.complexEmbedding_complexConj]
    exact (D.host.conjE_apply _ x).symm
  have h2 : c' = A.H.bar c := Subtype.ext (by
    change (c' : D.host.E) = ((A.H.bar c : 𝓞 D.host.E) : D.host.E)
    rw [A.H.bar_eq, h1, h])
  subst h2
  rfl

/- English proof (translation)
Simplify using `[Datum.mult, A.cm t, S.p_eq]`.
-/
theorem mult_tau (t : D.what₂.Tau) : S.Dw.mult (DV.tauEmb D t) = j := by
  simp [Datum.mult, A.cm t, S.p_eq]

def zeroSh (ct : At S κ p) (Z : ct.Mdl) : ct.Sh Z := ⟨0, 0, 0, 0, 𝟙 _⟩

/- English proof (translation)
The claim follows from `isZero_cokernel_of_epi (𝟙 _)`.
-/
theorem zeroSh_isZero (ct : At S κ p) (Z : ct.Mdl) : IsZero (zeroSh ct Z).toMod :=
  isZero_cokernel_of_epi (𝟙 _)

/- English proof (translation)
Use `le_antisymm (Real.sSup_nonpos ?_) (nrm_nonneg ct G f y)` and prove the remaining obligations. Introduce and unpack `r ⟨U, -, h, k, g, lam, -, rfl⟩`. Establish `hg : g = 0`. Establish `e : (𝟙 G.toMod : G.toMod ⟶ G.toMod) = 0` using `hG.eq_of_src _ _`. Use `congrArg (fun φ : G.toMod ⟶ G.toMod => (φ.app U).hom g) e` as an intermediate fact.

Simplify using `using this`. Rewrite using `[hg, map_zero]`. Simplify using the standard rewrite rules.
-/
theorem nrm_of_isZero (ct : At S κ p) {Z : ct.Mdl} (G : ct.Sh Z) (hG : IsZero G.toMod) (f : ct.Sec G) (y : ct.Pt Z) :
    ct.nrm G f y = 0 := by
  refine le_antisymm (Real.sSup_nonpos ?_) (nrm_nonneg ct G f y)
  rintro r ⟨U, -, h, k, g, lam, -, rfl⟩
  have hg : g = 0 := by
    have e : (𝟙 G.toMod : G.toMod ⟶ G.toMod) = 0 := hG.eq_of_src _ _
    have := congrArg (fun φ : G.toMod ⟶ G.toMod => (φ.app U).hom g) e
    simpa using this
  rw [hg, map_zero]
  simp

/- English proof (translation)
The claim follows from `D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))`.
-/
theorem tau_inj {t t' : D.what₂.Tau} (h : DV.tauEmb D t = DV.tauEmb D t') : t = t' :=
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

/- English proof (translation)
Introduce `h`. Establish `h1 : starRingEnd ℂ A.H.rt0 = A.H.rt0`. Establish `h0 : DV.tauEmb D t (A.H.rt : D.host.E) = A.H.rt0` using `A.cm t`. Rewrite `h`, the goal using `[← h0]`. Conclude with `h`.

Establish `hd : (0 : ℝ) < A.H.d` using `by exact_mod_cast A.H.d_prime.pos`. Establish `h2` using `congrArg Complex.re A.H.sqrt_neg_disc_sq`. Establish `h3 : A.H.rt0.im = 0` using `Complex.conj_eq_iff_im.1 h1`. Simplify using `[pow_two, h3] at h2`. Use polynomial arithmetic with `[sq_nonneg A.H.rt0.re]`.
-/
theorem conj_not_cm (A : Amb D) (t : D.what₂.Tau) : conjEmb (DV.tauEmb D t) (A.H.rt : D.host.E) ≠ A.H.rt0 := by
  intro h
  have h1 : starRingEnd ℂ A.H.rt0 = A.H.rt0 := by
    have h0 : DV.tauEmb D t (A.H.rt : D.host.E) = A.H.rt0 := A.cm t
    rw [← h0] at h ⊢
    exact h
  have hd : (0 : ℝ) < A.H.d := by exact_mod_cast A.H.d_prime.pos
  have h2 := congrArg Complex.re A.H.sqrt_neg_disc_sq
  have h3 : A.H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h1
  simp [pow_two, h3] at h2
  nlinarith [sq_nonneg A.H.rt0.re]

/- English proof (translation)
Introduce `h` and use `conj_not_cm A t' (h ▸ A.cm t)`.
-/
theorem tau_ne_conj (A : Amb D) (t t' : D.what₂.Tau) : DV.tauEmb D t ≠ conjEmb (DV.tauEmb D t') := fun h =>
  conj_not_cm A t' (h ▸ A.cm t)

/- English proof (translation)
Use `S.p_eq` as an intermediate fact. Use `S.rank_eq` as an intermediate fact. Rewrite using `[Datum.mult, if_neg (conj_not_cm A t)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem mult_conj (t : D.what₂.Tau) : S.Dw.mult (conjEmb (DV.tauEmb D t)) + j = N := by
  have := S.p_eq
  have := S.rank_eq
  rw [Datum.mult, if_neg (conj_not_cm A t)]
  omega

/- English proof (translation)
Unfold `At.expo`. Rewrite using `[Finset.sum_eq_single t]`. Rewrite using `[if_pos rfl, if_neg (tau_ne_conj A t t), add_zero]`. Introduce `s _ hs`. Rewrite using `[if_neg fun h => hs (tau_inj h).symm, if_neg (tau_ne_conj A t s), add_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ t) h`.
-/
theorem expo_tau (ct : At S κ p) (l : PsiT D → ℕ → ℤ) (t : D.what₂.Tau) (i : Fin (S.Dw.mult (DV.tauEmb D t))) :
    ct.expo l (DV.tauEmb D t) i = l (D.eTau t) ((i : ℕ) + 1) := by
  classical
  unfold At.expo
  rw [Finset.sum_eq_single t]
  · rw [if_pos rfl, if_neg (tau_ne_conj A t t), add_zero]
  · intro s _ hs
    rw [if_neg fun h => hs (tau_inj h).symm, if_neg (tau_ne_conj A t s), add_zero]
  · intro h; exact absurd (Finset.mem_univ t) h

/- English proof (translation)
Unfold `At.expo`. Rewrite using `[Finset.sum_eq_single t]`. Rewrite using `[if_pos rfl, if_neg (tau_ne_conj A t t).symm, zero_add]`. Introduce `s _ hs`. Rewrite using `[if_neg (tau_ne_conj A s t).symm, if_neg, add_zero]`.

Introduce `h`. Use `hs (tau_inj (RingHom.ext fun x => ?_)).symm` and prove the remaining obligations. Use `congrArg (fun φ : D.host.E →+* ℂ => starRingEnd ℂ (φ x)) h` as an intermediate fact. Simplify `this` using `[conjEmb]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ t) h`.
-/
theorem expo_conj (ct : At S κ p) (l : PsiT D → ℕ → ℤ) (t : D.what₂.Tau)
    (i : Fin (S.Dw.mult (conjEmb (DV.tauEmb D t)))) :
    ct.expo l (conjEmb (DV.tauEmb D t)) i = -l (D.eTau t) (N - (i : ℕ)) := by
  classical
  unfold At.expo
  rw [Finset.sum_eq_single t]
  · rw [if_pos rfl, if_neg (tau_ne_conj A t t).symm, zero_add]
  · intro s _ hs
    rw [if_neg (tau_ne_conj A s t).symm, if_neg, add_zero]
    intro h
    refine hs (tau_inj (RingHom.ext fun x => ?_)).symm
    have := congrArg (fun φ : D.host.E →+* ℂ => starRingEnd ℂ (φ x)) h
    simpa [conjEmb] using this
  · intro h; exact absurd (Finset.mem_univ t) h

/- English proof (translation)
Use `⟨fun i => ?_, fun i => ?_⟩` and prove the remaining obligations. Establish `h1` using `i.2`. Establish `h2` using `mult_tau (S := S) t`. Rewrite using `[expo_tau, if_pos (by omega)]`. Establish `h1` using `i.2`.

Establish `h2` using `mult_conj (S := S) t`. Rewrite using `[expo_conj, if_neg (by omega), neg_neg]`.
-/
theorem expo_hodge (ct : At S κ p) (t : D.what₂.Tau) :
    (∀ i, ct.expo (fun _ k => if k ≤ j then 1 else -1) (DV.tauEmb D t) i = 1) ∧
    ∀ i, ct.expo (fun _ k => if k ≤ j then 1 else -1) (conjEmb (DV.tauEmb D t)) i = 1 := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have h1 := i.2
    have h2 := mult_tau (S := S) t
    rw [expo_tau, if_pos (by omega)]
  · have h1 := i.2
    have h2 := mult_conj (S := S) t
    rw [expo_conj, if_neg (by omega), neg_neg]

/- English proof (translation)
Use `⟨fun φ => ?_⟩` and prove the remaining obligations. Take `⟨η⟩` from `(SharedLaws.lawSt D A N j S κ p ct).genNe Z`. Use `haveI : Nonempty Z.X := ⟨η.1⟩`. Establish `h0 : GlobalTheory.VB.IsVB (zeroSh ct Z).toMod 0` using `GlobalTheory.VB.isVB_zero_iff.2 (zeroSh_isZero ct Z)`. Conclude with `absurd (GlobalTheory.VB.IsVB.rank_unique h0 φ.isInv_left) zero_ne_one`.
-/
theorem isEmpty_gIso_zero (ct : At S κ p) (Z : ct.Mdl) (F : ct.Sh Z) : IsEmpty (ct.GIso (zeroSh ct Z) F) := by
  refine ⟨fun φ => ?_⟩
  obtain ⟨η⟩ := (SharedLaws.lawSt D A N j S κ p ct).genNe Z
  haveI : Nonempty Z.X := ⟨η.1⟩
  have h0 : GlobalTheory.VB.IsVB (zeroSh ct Z).toMod 0 := GlobalTheory.VB.isVB_zero_iff.2 (zeroSh_isZero ct Z)
  exact absurd (GlobalTheory.VB.IsVB.rank_unique h0 φ.isInv_left) zero_ne_one

/- English proof (translation)
Assemble the required witnesses or components as `⟨At.GIso.refl ((SharedLaws.lawSt D A N j S κ p ct).Lb_inv l)⟩`.
-/
theorem nonempty_gIso_Lb (ct : At S κ p) (l : PsiT D → ℕ → ℤ) : Nonempty (ct.GIso (ct.Lb l) (ct.Lb l)) :=
  ⟨At.GIso.refl ((SharedLaws.lawSt D A N j S κ p ct).Lb_inv l)⟩

/- English proof (translation)
Rewrite using `[sh.nrm_isoSec, sh.nrm_isoSec, sh.vrat_symm, ← Real.rpow_add (by exact_mod_cast ct.hp.pos)]`. Simplify using the standard rewrite rules.
-/
theorem nrm_mul_nrm_symm (ct : At S κ p) (sh : ShfSt ct) {Z : ct.Mdl} {F₁ F₂ : ct.Sh Z} (φ : ct.GIso F₁ F₂)
    (y : ct.Pt Z) :
    ct.nrm (sh.homSh F₁ F₂) (sh.isoSec φ) y * ct.nrm (sh.homSh F₂ F₁) (sh.isoSec (sh.isoSymm φ)) y = 1 := by
  rw [sh.nrm_isoSec, sh.nrm_isoSec, sh.vrat_symm, ← Real.rpow_add (by exact_mod_cast ct.hp.pos)]
  simp

/- English proof (translation)
Rewrite using `[sh.nrm_secOf, sh.nrm_isoSec, sh.vrat_symm, ← Real.rpow_add (by exact_mod_cast ct.hp.pos)]`. Simplify using the standard rewrite rules.
-/
theorem nrm_secOf_mul (ct : At S κ p) (sh : ShfSt ct) {F : ct.Sh ct.Xm} (φ : ct.GIso sh.oX F) (y : ct.Pt ct.Xm) :
    ct.nrm F (sh.secOf φ) y * ct.nrm (sh.homSh F sh.oX) (sh.isoSec (sh.isoSymm φ)) y = 1 := by
  rw [sh.nrm_secOf, sh.nrm_isoSec, sh.vrat_symm, ← Real.rpow_add (by exact_mod_cast ct.hp.pos)]
  simp

/- English proof (translation)
The claim follows from `sh.homSh_inv _ _ φ.isInv_left φ.isInv_right`.
-/
theorem homSh_inv_of_gIso (ct : At S κ p) (sh : ShfSt ct) {Z : ct.Mdl} {F₁ F₂ : ct.Sh Z} (φ : ct.GIso F₁ F₂) :
    ct.IsInv (sh.homSh F₁ F₂) := sh.homSh_inv _ _ φ.isInv_left φ.isInv_right

/- English proof (translation)
Introduce `n m h`. Establish `h1` using `(ct.B.lvl (some n)).2.2.1`. Establish `h2` using `(ct.B.lvl (some m)).2.2.1`. Establish `h3 : (ct.B.X (some n)).i.l.A = (ct.B.X (some m)).i.l.A` using `congrArg (fun Z : ct.Mdl => Z.i.l.A) h`. Rewrite `h3` using `[h1, h2]`.

Conclude with `Nat.pow_right_injective ct.hp.two_le (Nat.eq_of_mul_eq_mul_left κ.l.A_pos h3)`.
-/
theorem xn_injective (ct : At S κ p) : Function.Injective ct.Xn := by
  intro n m h
  have h1 := (ct.B.lvl (some n)).2.2.1
  have h2 := (ct.B.lvl (some m)).2.2.1
  have h3 : (ct.B.X (some n)).i.l.A = (ct.B.X (some m)).i.l.A := congrArg (fun Z : ct.Mdl => Z.i.l.A) h
  rw [h1, h2] at h3
  exact Nat.pow_right_injective ct.hp.two_le (Nat.eq_of_mul_eq_mul_left κ.l.A_pos h3)

/- English proof (translation)
Unfold `At.blowUp GlobalTheory.LocM.blowUp`. Use `split_ifs with h`. Conclude with `h.choose_spec.1`. Both sides reduce to the same expression.
-/
theorem blowUp_i (ct : At S κ p) (Z : ct.Mdl) (J : ct.Idl Z) : (ct.blowUp Z J).i = Z.i := by
  unfold At.blowUp GlobalTheory.LocM.blowUp
  split_ifs with h
  · exact h.choose_spec.1
  · rfl

/- English proof (translation)
Take `⟨a, -, ha⟩` from `(hm.IsHTBlowup_def n Z hn).1 h₁`. Take `⟨b, -, hb⟩` from `(hm.IsHTBlowup_def m Z hm').1 h₂`. Establish `e : (ct.Xn n).i = (ct.Xn m).i` using `by rw [← blowUp_i ct _ (hm.htIdl a), ← ha, hb, blowUp_i]`. Establish `h1` using `(ct.B.lvl (some n)).2.2.1`. Establish `h2` using `(ct.B.lvl (some m)).2.2.1`.

Establish `h3 : (ct.B.X (some n)).i.l.A = (ct.B.X (some m)).i.l.A` using `congrArg (fun i : Idx A.H p => i.l.A) e`. Rewrite `h3` using `[h1, h2]`. Conclude with `Nat.pow_right_injective ct.hp.two_le (Nat.eq_of_mul_eq_mul_left κ.l.A_pos h3)`.
-/
theorem htBlowup_level (ct : At S κ p) {sh : ShfSt ct} {hq : HTpSt ct} (hm : HTmSt ct sh hq) {n m : ℕ} (hn : 3 ≤ n)
    (hm' : 3 ≤ m) {Z : ct.Mdl} (h₁ : hm.IsHTBlowup Z (ct.Xn n)) (h₂ : hm.IsHTBlowup Z (ct.Xn m)) : n = m := by
  obtain ⟨a, -, ha⟩ := (hm.IsHTBlowup_def n Z hn).1 h₁
  obtain ⟨b, -, hb⟩ := (hm.IsHTBlowup_def m Z hm').1 h₂
  have e : (ct.Xn n).i = (ct.Xn m).i := by rw [← blowUp_i ct _ (hm.htIdl a), ← ha, hb, blowUp_i]
  have h1 := (ct.B.lvl (some n)).2.2.1
  have h2 := (ct.B.lvl (some m)).2.2.1
  have h3 : (ct.B.X (some n)).i.l.A = (ct.B.X (some m)).i.l.A := congrArg (fun i : Idx A.H p => i.l.A) e
  rw [h1, h2] at h3
  exact Nat.pow_right_injective ct.hp.two_le (Nat.eq_of_mul_eq_mul_left κ.l.A_pos h3)

/- English proof (translation)
Assemble the required witnesses or components as `⟨ct.isYY.2.2.2 Z' h.2.1 h.2.2.1, h.2.2.2 _ ct.isYY.2.1 ct.isYY.2.2.1⟩`.
-/
theorem drFlag_unique (ct : At S κ p) {Z' : ct.Mdl} (h : IsDRFlag ct.Xm Z') :
    (∃ f, IsMap Z' ct.YY f) ∧ ∃ g, IsMap ct.YY Z' g :=
  ⟨ct.isYY.2.2.2 Z' h.2.1 h.2.2.1, h.2.2.2 _ ct.isYY.2.1 ct.isYY.2.2.1⟩

end GlobalTheory.LocM.Check
