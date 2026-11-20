import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelatedPairsOrbitalTermEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrbitFibreSwap

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKDef.Regroup

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

/- English proof (translation)
Simplify using `only [sh, map_mul, MulOpposite.unop_mul]`.
-/
theorem sh_mul' (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

/- English proof (translation)
Use `⟨fun P => ?_, fun {P Q} h => ?_, fun {P Q R} h h' => ?_⟩` and prove the remaining obligations. Use `⟨1, 1, one_pos, ?_⟩` and prove the remaining obligations. Simplify using `[sh_one_eq]`. Take `⟨y, s, hs, hβ⟩` from `h`. Use `⟨y⁻¹, s⁻¹, inv_pos.mpr hs, ?_⟩` and prove the remaining obligations.

Establish `e : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1`. Rewrite using `[← sh_mul', Units.inv_mul, sh_one_eq]`. Rewrite using `[hβ]`. Simplify using `only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, e, mul_one, inv_mul_cancel₀ hs.ne', mul_inv_cancel₀ hs.ne', one_smul, Units.inv_mul_cancel_left]`. Take `⟨y, s, hs, hβ⟩` from `h`.

Take `⟨y', s', hs', hβ'⟩` from `h'`. Use `⟨y' * y, s' * s, mul_pos hs' hs, ?_⟩` and prove the remaining obligations. Rewrite using `[hβ', hβ, Units.val_mul, sh_mul']`. Simplify using `only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, mul_comm s]`.
-/
theorem dform_rel_equivalence : Equivalence (DForm.Rel (G := G)) := by
  refine ⟨fun P => ?_, fun {P Q} h => ?_, fun {P Q R} h h' => ?_⟩
  · refine ⟨1, 1, one_pos, ?_⟩
    simp [sh_one_eq]
  · obtain ⟨y, s, hs, hβ⟩ := h
    refine ⟨y⁻¹, s⁻¹, inv_pos.mpr hs, ?_⟩
    have e : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
      rw [← sh_mul', Units.inv_mul, sh_one_eq]
    rw [hβ]
    simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, e, mul_one,
      inv_mul_cancel₀ hs.ne', mul_inv_cancel₀ hs.ne', one_smul, Units.inv_mul_cancel_left]
  · obtain ⟨y, s, hs, hβ⟩ := h
    obtain ⟨y', s', hs', hβ'⟩ := h'
    refine ⟨y' * y, s' * s, mul_pos hs' hs, ?_⟩
    rw [hβ', hβ, Units.val_mul, sh_mul']
    simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, mul_comm s]

/- English proof (translation)
The claim follows from `minpoly.algEquiv_eq (Pair.innerAlgEquiv G.F y) x`.
-/
theorem minpoly_conj (y : G.Cˣ) (x : G.C) : minpoly G.F ((y : G.C) * x * ((y⁻¹ : G.Cˣ) : G.C)) = minpoly G.F x :=
  minpoly.algEquiv_eq (Pair.innerAlgEquiv G.F y) x

def mkPair (B : DForm G) (y : GlobalTheory.LKCx.grp G B.β)
    (h : (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).Separable) :
    DPair G where
  β := B.β
  γ := y.1.1
  c := y.1.2
  sym := B.sym
  sim := y.2.1
  reg := h
  trivAf := B.trivAf
  posR := B.posR

/- English proof (translation)
Substitute `hw` using the available equality. Establish `hz` using `z.2.1`. Establish `hs : (0 : ℚ) < (z.1.2 : ℚ)` using `z.2.2`. Use `⟨z.1.1, ((z.1.2 : ℚ))⁻¹, inv_pos.mpr hs, ?_, ?_⟩` and prove the remaining obligations. Use `show (B.β : G.C) = algebraMap ℚ G.C ((z.1.2 : ℚ))⁻¹ * ((z.1.1 : G.C) * B.β * sh G (z.1.1 : G.C))`.

Rewrite using `[hz, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hs.ne', map_one, one_mul]`. Both sides reduce to the same expression.
-/
theorem mkPair_rel_conj (B : DForm G) (w z w' : GlobalTheory.LKCx.grp G B.β) (hw : z * w * z⁻¹ = w') (h h') :
    (mkPair B w h).Rel (mkPair B w' h') := by
  subst hw
  have hz := z.2.1
  have hs : (0 : ℚ) < (z.1.2 : ℚ) := z.2.2
  refine ⟨z.1.1, ((z.1.2 : ℚ))⁻¹, inv_pos.mpr hs, ?_, ?_⟩
  · show (B.β : G.C) = algebraMap ℚ G.C ((z.1.2 : ℚ))⁻¹ * ((z.1.1 : G.C) * B.β * sh G (z.1.1 : G.C))
    rw [hz, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hs.ne', map_one, one_mul]
  · rfl

/- English proof (translation)
Establish `e : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1`. Rewrite using `[← sh_mul', Units.inv_mul, sh_one_eq]`. Establish `e' : ∀ X : G.C, sh G (y : G.C) * (sh G ((y⁻¹ : G.Cˣ) : G.C) * X) = X`. Introduce `X`. Rewrite using `[← mul_assoc, e, one_mul]`.

Establish `h' : ∀ X : G.C, (γ : G.C) * (β * (sh G (γ : G.C) * X)) = c • (β * X)`. Introduce `X`. Rewrite using `[← mul_assoc β, ← mul_assoc, ← mul_assoc, h, Algebra.smul_def, mul_assoc]`. Simplify using `only [Units.val_mul, sh_mul', ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, mul_assoc, e', Units.inv_mul_cancel_left, h', smul_smul, mul_comm s c]`.
-/
theorem transport_sim (β : G.C) (y γ : G.Cˣ) (s c : ℚ) (h : (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c * β) :
    ((y * γ * y⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C s * (y * β * sh G y)) * sh G ((y * γ * y⁻¹ : G.Cˣ) : G.C) =
      algebraMap ℚ G.C c * (algebraMap ℚ G.C s * (y * β * sh G y)) := by
  have e : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
    rw [← sh_mul', Units.inv_mul, sh_one_eq]
  have e' : ∀ X : G.C, sh G (y : G.C) * (sh G ((y⁻¹ : G.Cˣ) : G.C) * X) = X := by
    intro X; rw [← mul_assoc, e, one_mul]
  have h' : ∀ X : G.C, (γ : G.C) * (β * (sh G (γ : G.C) * X)) = c • (β * X) := by
    intro X; rw [← mul_assoc β, ← mul_assoc, ← mul_assoc, h, Algebra.smul_def, mul_assoc]
  simp only [Units.val_mul, sh_mul', ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, mul_assoc, e',
    Units.inv_mul_cancel_left, h', smul_smul, mul_comm s c]

/- English proof (translation)
Rewrite using `[← finsum_mem_inter_support, Set.inter_eq_right.2 h, finsum_mem_support]`.
-/
theorem finsum_eq_mem_of_supp {α : Type} (F : α → ℂ) (s : Set α) (h : Function.support F ⊆ s) :
    ∑ᶠ i ∈ s, F i = ∑ᶠ i, F i := by
  rw [← finsum_mem_inter_support, Set.inter_eq_right.2 h, finsum_mem_support]

section Sum

variable (G)

abbrev Idx : Type := Σ q : DFCls G, ConjClasses (GlobalTheory.LKCx.grp G (Quot.out q).β)

def RegAt (x : Idx G) : Prop :=
  RegIrr G (((Quotient.out x.2 : GlobalTheory.LKCx.grp G (Quot.out x.1).β).1.1 : G.Cˣ) : G.C)

def toCls (x : {x : Idx G // RegAt G x}) : DCls G :=
  Quot.mk _ (mkPair (Quot.out x.1.1) (Quotient.out x.1.2) ⟨x.2.1, x.2.2.1⟩)

variable {G}

/- English proof (translation)
Introduce and unpack `⟨⟨q, c⟩, h⟩ ⟨⟨q', c'⟩, h'⟩ e`. Take `⟨y, s, hs, hβ, hγ⟩` from `(DPair.mk_eq_iff _ _).1 e`. Establish `hq : q = q'`. Rewrite using `[← Quot.out_eq q, ← Quot.out_eq q']`. Conclude with `Quot.sound ⟨y, s, hs, hβ⟩`.

Substitute `hq` using the available equality. Establish `hc : (Quotient.out c).1.2 = (Quotient.out c').1.2` using `(DPair.rel_pol_c_term p G _ _ ⟨y, s, hs, hβ, hγ⟩).2.1`. Express the relevant statement in the definitionally equal form `((Quot.out q).β : G.C) = algebraMap ℚ G.C s * ((y : G.C) * (Quot.out q).β * sh G y) at hβ`. Establish `hz : (y : G.C) * (Quot.out q).β * sh G y = algebraMap ℚ G.C ((Units.mk0 s⁻¹ (inv_ne_zero hs.ne') : ℚˣ) : ℚ) * (Quot.out q).β`. Rewrite using `[Units.val_mk0]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, ← map_mul, inv_mul_cancel₀ hs.ne', map_one, one_mul]`. Use `_ = _ := by rw [← hβ]`. Set `z : GlobalTheory.LKCx.grp G (Quot.out q).β` to `⟨(y, Units.mk0 s⁻¹ (inv_ne_zero hs.ne')), hz, by show (0 : ℚ) < ((Units.mk0 s⁻¹ (inv_ne_zero hs.ne') : ℚˣ) : ℚ)`. Rewrite using `[Units.val_mk0]`.

Conclude with `inv_pos.mpr hs⟩`. Establish `hzc : z * Quotient.out c * z⁻¹ = Quotient.out c'`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Prod.ext` to reduce the goal to its premises. Conclude with `hγ.symm`.

Use `show Units.mk0 s⁻¹ (inv_ne_zero hs.ne') * (Quotient.out c).1.2 * (Units.mk0 s⁻¹ (inv_ne_zero hs.ne'))⁻¹ = (Quotient.out c').1.2`. Rewrite using `[mul_comm, inv_mul_cancel_left, hc]`. Establish `hcc : c = c'`. Rewrite using `[← Quotient.out_eq c, ← Quotient.out_eq c']`. Conclude with `Quotient.sound (isConj_iff.2 ⟨z, hzc⟩)`.

Substitute `hcc` using the available equality. Both sides reduce to the same expression.
-/
theorem toCls_injective : Function.Injective (toCls G) := by
  rintro ⟨⟨q, c⟩, h⟩ ⟨⟨q', c'⟩, h'⟩ e
  obtain ⟨y, s, hs, hβ, hγ⟩ := (DPair.mk_eq_iff _ _).1 e
  have hq : q = q' := by
    rw [← Quot.out_eq q, ← Quot.out_eq q']
    exact Quot.sound ⟨y, s, hs, hβ⟩
  subst hq
  have hc : (Quotient.out c).1.2 = (Quotient.out c').1.2 :=
    (DPair.rel_pol_c_term p G _ _ ⟨y, s, hs, hβ, hγ⟩).2.1
  change ((Quot.out q).β : G.C) = algebraMap ℚ G.C s * ((y : G.C) * (Quot.out q).β * sh G y) at hβ
  have hz : (y : G.C) * (Quot.out q).β * sh G y =
      algebraMap ℚ G.C ((Units.mk0 s⁻¹ (inv_ne_zero hs.ne') : ℚˣ) : ℚ) * (Quot.out q).β := by
    rw [Units.val_mk0]
    calc (y : G.C) * (Quot.out q).β * sh G y
        = algebraMap ℚ G.C s⁻¹ * (algebraMap ℚ G.C s * ((y : G.C) * (Quot.out q).β * sh G y)) := by
          rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hs.ne', map_one, one_mul]
      _ = _ := by rw [← hβ]
  let z : GlobalTheory.LKCx.grp G (Quot.out q).β := ⟨(y, Units.mk0 s⁻¹ (inv_ne_zero hs.ne')), hz, by
    show (0 : ℚ) < ((Units.mk0 s⁻¹ (inv_ne_zero hs.ne') : ℚˣ) : ℚ)
    rw [Units.val_mk0]; exact inv_pos.mpr hs⟩
  have hzc : z * Quotient.out c * z⁻¹ = Quotient.out c' := by
    apply Subtype.ext
    apply Prod.ext
    · exact hγ.symm
    · show Units.mk0 s⁻¹ (inv_ne_zero hs.ne') * (Quotient.out c).1.2 * (Units.mk0 s⁻¹ (inv_ne_zero hs.ne'))⁻¹ =
        (Quotient.out c').1.2
      rw [mul_comm, inv_mul_cancel_left, hc]
  have hcc : c = c' := by
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    exact Quotient.sound (isConj_iff.2 ⟨z, hzc⟩)
  subst hcc
  rfl

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨y, s, hs, hβ⟩ : DForm.Rel (DForm.ofDPair (Quot.out d)) (Quot.out (Quot.mk _ (DForm.ofDPair (Quot.out d)) : DFCls G)) := by`. Establish `h` using `Quot.eq.1 (Quot.out_eq (Quot.mk DForm.Rel (DForm.ofDPair (Quot.out d))))`. Conclude with `dform_rel_equivalence.symm (dform_rel_equivalence.eqvGen_iff.1 h)`. Use `set P := Quot.out d with hP`. Use `set q : DFCls G := Quot.mk _ (DForm.ofDPair P) with hq`.

Express the relevant statement in the definitionally equal form `((Quot.out q).β : G.C) = algebraMap ℚ G.C s * ((y : G.C) * P.β * sh G y) at hβ`. Establish `hsim : ((y * P.γ * y⁻¹ : G.Cˣ) : G.C) * (Quot.out q).β * sh G ((y * P.γ * y⁻¹ : G.Cˣ) : G.C) = algebraMap ℚ G.C (P.c : ℚ) * (Quot.out q).β`. Rewrite using `[hβ]`. Conclude with `transport_sim _ _ _ _ _ P.sim`. Set `w : GlobalTheory.LKCx.grp G (Quot.out q).β` to `⟨(y * P.γ * y⁻¹, P.c), hsim, hpos _ _ _ hsim⟩`.

Establish `hmw : minpoly G.F ((w.1.1 : G.Cˣ) : G.C) = P.pol` using `by show minpoly G.F (((y * P.γ * y⁻¹ : G.Cˣ)) : G.C) = minpoly G.F (P.γ : G.C)`. Rewrite using `[Units.val_mul, Units.val_mul, minpoly_conj]`. Take `⟨z, hz⟩` from `isConj_iff.1 (Quotient.exact (Quotient.out_eq (ConjClasses.mk w)).symm)`. Establish `hmin : minpoly G.F (((Quotient.out (ConjClasses.mk w)).1.1 : G.Cˣ) : G.C) = P.pol`. Rewrite using `[← hz, ← hmw]`.

Use `show minpoly G.F ((((z.1.1 * w.1.1) * z.1.1⁻¹ : G.Cˣ)) : G.C) = _`. Rewrite using `[Units.val_mul, Units.val_mul, minpoly_conj]`. Establish `hreg : RegAt G ⟨q, ConjClasses.mk w⟩`. Unfold `RegAt RegIrr`. Rewrite using `[hmin]`.

Conclude with `⟨P.reg.1, P.reg.2, hd⟩`. Use `⟨⟨⟨q, ConjClasses.mk w⟩, hreg⟩, ?_⟩` and prove the remaining obligations. Establish `hw : (minpoly G.F ((w.1.1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F ((w.1.1 : G.Cˣ) : G.C)).Separable`. Rewrite using `[hmw]`. Conclude with `P.reg`.

Establish `h1 : P.Rel (mkPair (Quot.out q) w hw)` using `⟨y, s, hs, hβ, rfl⟩`. Establish `h2` using `mkPair_rel_conj (Quot.out q) w z _ hz hw ⟨hreg.1, hreg.2.1⟩`. Establish `h3` using `((DPair.rel_equivalence G).trans h1 h2)`. Conclude with `((DPair.mk_eq_iff _ _).2 ((DPair.rel_equivalence G).symm h3)).trans (Quot.out_eq d)`.
-/
theorem mem_range_toCls
    (hpos : ∀ (B : DForm G) (y : G.Cˣ) (s : ℚ), (y : G.C) * B.β * sh G y = algebraMap ℚ G.C s * B.β → 0 < s)
    (d : DCls G) (hd : Irreducible (Quot.out d).pol) : d ∈ Set.range (toCls G) := by
  obtain ⟨y, s, hs, hβ⟩ : DForm.Rel (DForm.ofDPair (Quot.out d)) (Quot.out (Quot.mk _ (DForm.ofDPair (Quot.out d))
      : DFCls G)) := by
    have h := Quot.eq.1 (Quot.out_eq (Quot.mk DForm.Rel (DForm.ofDPair (Quot.out d))))
    exact dform_rel_equivalence.symm (dform_rel_equivalence.eqvGen_iff.1 h)
  set P := Quot.out d with hP
  set q : DFCls G := Quot.mk _ (DForm.ofDPair P) with hq
  change ((Quot.out q).β : G.C) = algebraMap ℚ G.C s * ((y : G.C) * P.β * sh G y) at hβ
  have hsim : ((y * P.γ * y⁻¹ : G.Cˣ) : G.C) * (Quot.out q).β * sh G ((y * P.γ * y⁻¹ : G.Cˣ) : G.C) =
      algebraMap ℚ G.C (P.c : ℚ) * (Quot.out q).β := by
    rw [hβ]; exact transport_sim _ _ _ _ _ P.sim
  let w : GlobalTheory.LKCx.grp G (Quot.out q).β := ⟨(y * P.γ * y⁻¹, P.c), hsim, hpos _ _ _ hsim⟩
  have hmw : minpoly G.F ((w.1.1 : G.Cˣ) : G.C) = P.pol := by
    show minpoly G.F (((y * P.γ * y⁻¹ : G.Cˣ)) : G.C) = minpoly G.F (P.γ : G.C)
    rw [Units.val_mul, Units.val_mul, minpoly_conj]
  obtain ⟨z, hz⟩ := isConj_iff.1 (Quotient.exact (Quotient.out_eq (ConjClasses.mk w)).symm)
  have hmin : minpoly G.F (((Quotient.out (ConjClasses.mk w)).1.1 : G.Cˣ) : G.C) = P.pol := by
    rw [← hz, ← hmw]
    show minpoly G.F ((((z.1.1 * w.1.1) * z.1.1⁻¹ : G.Cˣ)) : G.C) = _
    rw [Units.val_mul, Units.val_mul, minpoly_conj]
  have hreg : RegAt G ⟨q, ConjClasses.mk w⟩ := by
    unfold RegAt RegIrr; rw [hmin]; exact ⟨P.reg.1, P.reg.2, hd⟩
  refine ⟨⟨⟨q, ConjClasses.mk w⟩, hreg⟩, ?_⟩
  have hw : (minpoly G.F ((w.1.1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F ((w.1.1 : G.Cˣ) : G.C)).Separable := by
    rw [hmw]; exact P.reg
  have h1 : P.Rel (mkPair (Quot.out q) w hw) := ⟨y, s, hs, hβ, rfl⟩
  have h2 := mkPair_rel_conj (Quot.out q) w z _ hz hw ⟨hreg.1, hreg.2.1⟩
  have h3 := ((DPair.rel_equivalence G).trans h1 h2)
  exact ((DPair.mk_eq_iff _ _).2 ((DPair.rel_equivalence G).symm h3)).trans (Quot.out_eq d)

variable (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1))
  (f' : Gr G 1 → ℂ)

def summand (d : DCls G) : ℂ :=
  if Irreducible (Quot.out d).pol then wt (Quot.out d).pol * (Quot.out d).term Kf f 1 K' f' else 0

/- English proof (translation)
Use `set M := mkPair (Quot.out x.1) (Quotient.out x.2) ⟨h.1, h.2.1⟩ with hM`. Take `⟨hpol, -, ht⟩` from `DPair.rel_pol_c_term p G _ _ (DPair.rel_out M)`. Establish `hirr : Irreducible (Quot.out (Quot.mk DPair.Rel M : DCls G)).pol`. Rewrite using `[← hpol]`. Conclude with `h.2.2`.

Use `show _ = summand wt Kf f K' f' (Quot.mk _ M)`. Unfold `summand`. Rewrite using `[if_pos hirr, ← hpol, ← ht Kf f 1 K' f' one_pos hf hf', hterm M (Quotient.out x.2).2]`. Both sides reduce to the same expression.
-/
theorem summand_toCls
    (hterm : ∀ (P : DPair G) (hm : (P.γ, P.c) ∈ GlobalTheory.LKCx.grp G P.β),
      P.term Kf f 1 K' f' =
        centSum (GlobalTheory.LKCx.toAfF G P.β P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec)
          (GlobalTheory.LKCx.toP1 G P.β) (MonoidHom.id (Gr G 1)) Kf K' 1 f f' ⟨(P.γ, P.c), hm⟩)
    (hf : ∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) (hf' : ∀ k ∈ K', ∀ g, f' (k⁻¹ * g * sigG G 1 k) = f' g)
    (x : Idx G) (h : RegAt G x) :
    wt (minpoly G.F (((Quotient.out x.2 : GlobalTheory.LKCx.grp G (Quot.out x.1).β).1.1 : G.Cˣ) : G.C)) *
      centSum (GlobalTheory.LKCx.toAfF G (Quot.out x.1).β (Quot.out x.1).trivAf.choose
          (Quot.out x.1).trivAf.choose_spec.choose (Quot.out x.1).trivAf.choose_spec.choose_spec)
        (GlobalTheory.LKCx.toP1 G (Quot.out x.1).β) (MonoidHom.id (Gr G 1)) Kf K' 1 f f' (Quotient.out x.2) =
      summand wt Kf f K' f' (toCls G ⟨x, h⟩) := by
  set M := mkPair (Quot.out x.1) (Quotient.out x.2) ⟨h.1, h.2.1⟩ with hM
  obtain ⟨hpol, -, ht⟩ := DPair.rel_pol_c_term p G _ _ (DPair.rel_out M)
  have hirr : Irreducible (Quot.out (Quot.mk DPair.Rel M : DCls G)).pol := by
    rw [← hpol]; exact h.2.2
  show _ = summand wt Kf f K' f' (Quot.mk _ M)
  unfold summand
  rw [if_pos hirr, ← hpol, ← ht Kf f 1 K' f' one_pos hf hf', hterm M (Quotient.out x.2).2]
  rfl

/- English proof (translation)
Use `set F := summand wt Kf f K' f' with hF`. Establish `hL : GlobalTheory.LKDef.dSumIrr G wt Kf f 1 K' f' = ∑ᶠ d, F d` using `rfl`. Establish `hsuppF : Function.support F ⊆ {q : DCls G | Irreducible (Quot.out q).pol ∧ (Quot.out q).term Kf f 1 K' f' ≠ 0}`. Introduce `d hd`. Rewrite `hd` using `[Function.mem_support, hF, summand]`.

Use `split_ifs at hd with hi`. Conclude with `⟨hi, right_ne_zero_of_mul hd⟩`. Conclude with `absurd rfl hd`. Establish `hfinF` using `hfin.subset hsuppF`. Establish `hrange : Function.support F ⊆ Set.range (toCls G)` using `fun d hd => mem_range_toCls hpos d (hsuppF hd).1`.

Set `H : Idx G → ℂ` to `fun x => if h : RegAt G x then F (toCls G ⟨x, h⟩) else 0`. Establish `hR : ∀ (q : DFCls G) (c : ConjClasses (GlobalTheory.LKCx.grp G (Quot.out q).β)), (if GlobalTheory.LKDef.RegIrr G (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C) then wt (minpoly G.F (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G …`. Introduce `q c`. Distinguish the cases in `h : RegAt G ⟨q, c⟩`. Establish `h' : RegIrr G (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C)` using `h`.

Simplify using `only [H, dif_pos h]`. Rewrite using `[if_pos h']`. Conclude with `summand_toCls wt Kf f K' f' hterm hf hf' ⟨q, c⟩ h`. Establish `h' : ¬ RegIrr G (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C)` using `h`. Simplify using `only [H, dif_neg h]`.

Rewrite using `[if_neg h']`. Establish `hsuppH : (Function.support H).Finite`. Apply `((hfinF.preimage (toCls_injective).injOn).image Subtype.val).subset` to reduce the goal to its premises. Introduce `x hx`. Rewrite `hx` using `[Function.mem_support]`.

Distinguish the cases in `h : RegAt G x`. Simplify using `only [H, dif_pos h] at hx`. Conclude with `⟨⟨x, h⟩, hx, rfl⟩`. Simplify using `only [H, dif_neg h] at hx`. Conclude with `absurd rfl hx`.

Establish `hRHS : (∑ᶠ q : DFCls G, ∑ᶠ c : ConjClasses (GlobalTheory.LKCx.grp G (Quot.out q).β), (if GlobalTheory.LKDef.RegIrr G (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C) then wt (minpoly G.F (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 …` using `finsum_congr fun q => finsum_congr fun c => hR q c`. Rewrite using `[hRHS, ← GlobalTheory.OrbitFibre.finsum_sigma_iter H hsuppH, hL]`. Establish `h1 : ∑ᶠ x, H x = ∑ᶠ x : {x // RegAt G x}, F (toCls G x)`. Rewrite using `[← finsum_eq_mem_of_supp H (Set.range Subtype.val) ?_, finsum_mem_range Subtype.val_injective]`. Apply `finsum_congr` to reduce the goal to its premises.

Introduce `x`. Simplify using `only [H, dif_pos x.2]`. Introduce `x hx`. Rewrite `hx` using `[Function.mem_support]`. Distinguish the cases in `h : RegAt G x`.

Conclude with `⟨⟨x, h⟩, rfl⟩`. Simplify using `only [H, dif_neg h] at hx`. Conclude with `absurd rfl hx`. Rewrite using `[h1, ← finsum_mem_range (toCls_injective (G := G)), finsum_eq_mem_of_supp F _ hrange]`.
-/
theorem regroup_of
    (hpos : ∀ (B : DForm G) (y : G.Cˣ) (s : ℚ), (y : G.C) * B.β * sh G y = algebraMap ℚ G.C s * B.β → 0 < s)
    (hfin : {q : DCls G | Irreducible (Quot.out q).pol ∧ (Quot.out q).term Kf f 1 K' f' ≠ 0}.Finite)
    (hterm : ∀ (P : DPair G) (hm : (P.γ, P.c) ∈ GlobalTheory.LKCx.grp G P.β),
      P.term Kf f 1 K' f' =
        centSum (GlobalTheory.LKCx.toAfF G P.β P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec)
          (GlobalTheory.LKCx.toP1 G P.β) (MonoidHom.id (Gr G 1)) Kf K' 1 f f' ⟨(P.γ, P.c), hm⟩)
    (hf : ∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) (hf' : ∀ k ∈ K', ∀ g, f' (k⁻¹ * g * sigG G 1 k) = f' g) :
    GlobalTheory.LKDef.dSumIrr G wt Kf f 1 K' f' =
      ∑ᶠ q : GlobalTheory.LKDef.DFCls G, ∑ᶠ c : ConjClasses (GlobalTheory.LKCx.grp G (Quot.out q).β),
        if GlobalTheory.LKDef.RegIrr G (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C) then
          wt (minpoly G.F (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C)) *
            centSum (GlobalTheory.LKCx.toAfF G (Quot.out q).β (Quot.out q).trivAf.choose (Quot.out q).trivAf.choose_spec.choose
                (Quot.out q).trivAf.choose_spec.choose_spec)
              (GlobalTheory.LKCx.toP1 G (Quot.out q).β) (MonoidHom.id (Gr G 1)) Kf K' 1 f f' (Quotient.out c)
        else 0 := by
  set F := summand wt Kf f K' f' with hF
  have hL : GlobalTheory.LKDef.dSumIrr G wt Kf f 1 K' f' = ∑ᶠ d, F d := rfl
  have hsuppF : Function.support F ⊆
      {q : DCls G | Irreducible (Quot.out q).pol ∧ (Quot.out q).term Kf f 1 K' f' ≠ 0} := by
    intro d hd
    rw [Function.mem_support, hF, summand] at hd
    split_ifs at hd with hi
    · exact ⟨hi, right_ne_zero_of_mul hd⟩
    · exact absurd rfl hd
  have hfinF := hfin.subset hsuppF
  have hrange : Function.support F ⊆ Set.range (toCls G) := fun d hd => mem_range_toCls hpos d (hsuppF hd).1
  let H : Idx G → ℂ := fun x => if h : RegAt G x then F (toCls G ⟨x, h⟩) else 0
  have hR : ∀ (q : DFCls G) (c : ConjClasses (GlobalTheory.LKCx.grp G (Quot.out q).β)),
      (if GlobalTheory.LKDef.RegIrr G (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C) then
          wt (minpoly G.F (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C)) *
            centSum (GlobalTheory.LKCx.toAfF G (Quot.out q).β (Quot.out q).trivAf.choose (Quot.out q).trivAf.choose_spec.choose
                (Quot.out q).trivAf.choose_spec.choose_spec)
              (GlobalTheory.LKCx.toP1 G (Quot.out q).β) (MonoidHom.id (Gr G 1)) Kf K' 1 f f' (Quotient.out c)
        else 0) = H ⟨q, c⟩ := by
    intro q c
    by_cases h : RegAt G ⟨q, c⟩
    · have h' : RegIrr G (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C) := h
      simp only [H, dif_pos h]
      rw [if_pos h']
      exact summand_toCls wt Kf f K' f' hterm hf hf' ⟨q, c⟩ h
    · have h' : ¬ RegIrr G (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C) := h
      simp only [H, dif_neg h]
      rw [if_neg h']
  have hsuppH : (Function.support H).Finite := by
    apply ((hfinF.preimage (toCls_injective).injOn).image Subtype.val).subset
    intro x hx
    rw [Function.mem_support] at hx
    by_cases h : RegAt G x
    · simp only [H, dif_pos h] at hx
      exact ⟨⟨x, h⟩, hx, rfl⟩
    · simp only [H, dif_neg h] at hx
      exact absurd rfl hx
  have hRHS : (∑ᶠ q : DFCls G, ∑ᶠ c : ConjClasses (GlobalTheory.LKCx.grp G (Quot.out q).β),
      (if GlobalTheory.LKDef.RegIrr G (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C) then
          wt (minpoly G.F (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C)) *
            centSum (GlobalTheory.LKCx.toAfF G (Quot.out q).β (Quot.out q).trivAf.choose (Quot.out q).trivAf.choose_spec.choose
                (Quot.out q).trivAf.choose_spec.choose_spec)
              (GlobalTheory.LKCx.toP1 G (Quot.out q).β) (MonoidHom.id (Gr G 1)) Kf K' 1 f f' (Quotient.out c)
        else 0)) = ∑ᶠ q : DFCls G, ∑ᶠ c : ConjClasses (GlobalTheory.LKCx.grp G (Quot.out q).β), H ⟨q, c⟩ :=
    finsum_congr fun q => finsum_congr fun c => hR q c
  rw [hRHS, ← GlobalTheory.OrbitFibre.finsum_sigma_iter H hsuppH, hL]
  have h1 : ∑ᶠ x, H x = ∑ᶠ x : {x // RegAt G x}, F (toCls G x) := by
    rw [← finsum_eq_mem_of_supp H (Set.range Subtype.val) ?_,
      finsum_mem_range Subtype.val_injective]
    · apply finsum_congr
      intro x
      simp only [H, dif_pos x.2]
    · intro x hx
      rw [Function.mem_support] at hx
      by_cases h : RegAt G x
      · exact ⟨⟨x, h⟩, rfl⟩
      · simp only [H, dif_neg h] at hx
        exact absurd rfl hx
  rw [h1, ← finsum_mem_range (toCls_injective (G := G)), finsum_eq_mem_of_supp F _ hrange]

end Sum

/- English proof (translation)
Introduce `p _ G ha wt L f hf hfb K' f' hf' hfb'`. Conclude with `regroup_of wt L.K.toSubgroup f K' f' (hposT p G) (hfinT p G ha L f hf hfb K' f' hf' hfb') (fun P hm => htermT p G P hm L f hf K' f' hf') (fun k hk g => hf.2.2.1 k hk g) hf'.2.2.1`.
-/
theorem regroup_main
    (hposT : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (B : GlobalTheory.LKDef.DForm G) (y : G.Cˣ) (s : ℚ),
  (y : G.C) * B.β * sh G y = algebraMap ℚ G.C s * B.β → 0 < s)
    (hfinT : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      {q : GlobalTheory.LKDef.DCls G | Irreducible (Quot.out q).pol ∧ (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite)
    (htermT : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : GlobalTheory.LKDef.DPair G) (hm : (P.γ, P.c) ∈ GlobalTheory.LKCx.grp G P.β)
    (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      P.term L.K.toSubgroup f 1 K' f' =
        centSum (GlobalTheory.LKCx.toAfF G P.β P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec)
          (GlobalTheory.LKCx.toP1 G P.β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' ⟨(P.γ, P.c), hm⟩) :
    ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (wt : Polynomial G.F → ℂ)
    (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      GlobalTheory.LKDef.dSumIrr G wt L.K.toSubgroup f 1 K' f' =
        ∑ᶠ q : GlobalTheory.LKDef.DFCls G, ∑ᶠ c : ConjClasses (GlobalTheory.LKCx.grp G (Quot.out q).β),
          if GlobalTheory.LKDef.RegIrr G (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C) then
            wt (minpoly G.F (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C)) *
              centSum (GlobalTheory.LKCx.toAfF G (Quot.out q).β (Quot.out q).trivAf.choose (Quot.out q).trivAf.choose_spec.choose
                  (Quot.out q).trivAf.choose_spec.choose_spec)
                (GlobalTheory.LKCx.toP1 G (Quot.out q).β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' (Quotient.out c)
          else 0 := by
  intro p _ G ha wt L f hf hfb K' f' hf' hfb'
  exact regroup_of wt L.K.toSubgroup f K' f' (hposT p G) (hfinT p G ha L f hf hfb K' f' hf' hfb')
    (fun P hm => htermT p G P hm L f hf K' f' hf') (fun k hk g => hf.2.2.1 k hk g) hf'.2.2.1

end GlobalTheory.LKDef.Regroup
