import Formalism.LocalToGlobal.Columns.TargetChF
import Formalism.LocalToGlobal.Columns.DGamAut

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Gen

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

/- English proof (translation)
Use `⟨fun P => ⟨(p.fr P)⁻¹ * p0.fr P, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show ∀ x, ((p.fr P)⁻¹ * p0.fr P) x ∈ stdAt X.E n P.1 ↔ x ∈ stdAt X.E n P.1`. Introduce `x`. Establish `hx : p.1.2 P (((p.fr P)⁻¹ * p0.fr P) x) = p0.1.2 P x` using `LinearEquiv.apply_symm_apply _ _`. Establish `h' : p.1.1 = p0.1.1` using `h`.

Rewrite using `[← p.2 P, hx, h', p0.2 P]`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [HSMul.hSMul, SMul.smul]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Establish `h1` using `one_smul (UF X.E n × GLG X.E n SG) p0.1.1`.

Simplify using `only [HSMul.hSMul, SMul.smul] at h1`. Conclude with `h.trans h1.symm`. Use function extensionality and compare the values at `P`. Simplify using `only [DecoF.fr, OneMemClass.coe_one, one_mul, InvMemClass.coe_inv, _root_.mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel]`.
-/
theorem frm_exists_c (p p0 : DecoF X.E n ST SG Q) (h : p.deco = p0.deco) :
    ∃ c : GLQ X.E n Q, p = ((1, 1, c) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) • p0 := by
  refine ⟨fun P => ⟨(p.fr P)⁻¹ * p0.fr P, ?_⟩, ?_⟩
  · show ∀ x, ((p.fr P)⁻¹ * p0.fr P) x ∈ stdAt X.E n P.1 ↔ x ∈ stdAt X.E n P.1
    intro x
    have hx : p.1.2 P (((p.fr P)⁻¹ * p0.fr P) x) = p0.1.2 P x := LinearEquiv.apply_symm_apply _ _
    have h' : p.1.1 = p0.1.1 := h
    rw [← p.2 P, hx, h', p0.2 P]
  · apply Subtype.ext
    simp only [HSMul.hSMul, SMul.smul]
    refine Prod.ext ?_ ?_
    · have h1 := one_smul (UF X.E n × GLG X.E n SG) p0.1.1
      simp only [HSMul.hSMul, SMul.smul] at h1
      exact h.trans h1.symm
    · funext P
      simp only [DecoF.fr, OneMemClass.coe_one, one_mul, InvMemClass.coe_inv, _root_.mul_inv_rev, inv_inv,
        ← mul_assoc, mul_inv_cancel]

variable (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q)

/- English proof (translation)
Use `haveI : ∀ w : SG, Finite (𝓞 X.E ⧸ w.1.asIdeal) := fun w => Ideal.finiteQuotientOfFreeOfNeBot _ w.1.ne_bot`. Take `⟨m2, hm2, h2⟩` from `hroot g.2.2`. Establish `hfo : IsOfFinOrder g.2.1` using `isOfFinOrder_of_finite _`. Establish `ha : ((Λ.chr g.2.1 : X.Kˣ) : X.K) ^ orderOf g.2.1 = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]`.

Use `⟨orderOf g.2.1 * m2, Nat.mul_pos hfo.orderOf_pos hm2, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, mul_pow, pow_mul, ha, one_pow, one_mul, mul_comm (orderOf _) m2, pow_mul, h2, one_pow]`.
-/
theorem frm_root (hroot : ∀ c : ↥Θ.grp, ∃ m : ℕ, 0 < m ∧ ((Θ.chr c : X.Kˣ) : X.K) ^ m = 1) (g : FrmG Λ Θ) :
    ∃ m : ℕ, 0 < m ∧ (((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) ^ m = 1 := by
  haveI : ∀ w : SG, Finite (𝓞 X.E ⧸ w.1.asIdeal) := fun w =>
    Ideal.finiteQuotientOfFreeOfNeBot _ w.1.ne_bot
  obtain ⟨m2, hm2, h2⟩ := hroot g.2.2
  have hfo : IsOfFinOrder g.2.1 := isOfFinOrder_of_finite _
  have ha : ((Λ.chr g.2.1 : X.Kˣ) : X.K) ^ orderOf g.2.1 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
  refine ⟨orderOf g.2.1 * m2, Nat.mul_pos hfo.orderOf_pos hm2, ?_⟩
  rw [Units.val_mul, mul_pow, pow_mul, ha, one_pow, one_mul, mul_comm (orderOf _) m2, pow_mul, h2,
    one_pow]

open Classical in

/- English proof (translation)
Take `⟨s, hs, hrep⟩` from `DecoSet.finite_reps (ST := ST) (SG := SG) (n := n) (posStar_of_conj hX.conjE)`. Establish `: Finite s` using `hs`. Set `pt : s → (∀ P : Q, ↥(GLint X.E n P.1) ⧸ (Θ P).H) → Option (DecoF X.E n ST SG Q)` to `fun d cb => if h : ∃ p0 : DecoF X.E n ST SG Q, p0.deco = d.1 then some (((1, 1, fun P => ((cb P).out)⁻¹) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) • h.choose) else none`. Establish `hfin : Finite (Option (s × (∀ P : Q, ↥(GLint X.E n P.1) ⧸ (Θ P).H)))` using `inferInstance`. Distinguish the cases in `hne : Nonempty (frmGSD (C.pull DecoF.deco) Λ Θ).Cl`.

Use `swap`. Use `not_nonempty_iff.1 hne` as an intermediate fact. Conclude with `inferInstance`. Take `⟨c00⟩` from `hne`. Use `Finite.of_surjective (fun a : s × (∀ P : Q, ↥(GLint X.E n P.1) ⧸ (Θ P).H) => match pt a.1 a.2 with` and prove the remaining obligations.

Consider the case `some p => (frmGSD (C.pull DecoF.deco) Λ Θ).cls p`. Consider the case `none => c00) ?_`. Introduce `c`. Proceed by induction on `c using Quotient.inductionOn' with`. Consider the case `h p`.

Take `⟨d0, hd0, g, hg⟩` from `hrep (DecoF.deco p)`. Set `p1 : DecoF X.E n ST SG Q` to `((g, 1, 1) : UF X.E n × GLG X.E n SG × GLQ X.E n Q)⁻¹ • p`. Establish `hp1 : p1.deco = d0` using `by show ((g, (1 : GLG X.E n SG)) : UF X.E n × GLG X.E n SG)⁻¹ • p.deco = d0`. Rewrite using `[hg, inv_smul_smul]`. Establish `hex : ∃ p0 : DecoF X.E n ST SG Q, p0.deco = d0` using `⟨p1, hp1⟩`.

Take `⟨c, hc⟩` from `frm_exists_c p1 hex.choose (hp1.trans hex.choose_spec.symm)`. Set `cb : ∀ P : Q, ↥(GLint X.E n P.1) ⧸ (Θ P).H` to `fun P => QuotientGroup.mk ((c P)⁻¹)`. Establish `hout : ∀ P : Q, ((c P)⁻¹)⁻¹ * (cb P).out ∈ (Θ P).H` using `fun P => QuotientGroup.eq.1 (QuotientGroup.out_eq' (cb P)).symm`. Use `⟨(⟨d0, hd0⟩, cb), ?_⟩` and prove the remaining obligations. Establish `hpt : pt ⟨d0, hd0⟩ cb = some (((1, 1, fun P => ((cb P).out)⁻¹) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) • hex.choose)` using `dif_pos hex`.

Use `show (match pt ⟨d0, hd0⟩ cb with`. Consider the case `some p => (frmGSD (C.pull DecoF.deco) Λ Θ).cls p`. Consider the case `none => c00) = _`. Rewrite using `[hpt]`. Set `θ : ↥Θ.grp` to `⟨fun P => ((c P)⁻¹)⁻¹ * (cb P).out, fun P _ => hout P⟩`.

Use `((frmGSD (C.pull DecoF.deco) Λ Θ).cls_eq_iff _ p).mpr ⟨((g, 1, θ) : FrmG Λ Θ)⁻¹, ?_⟩` and prove the remaining obligations. Use `inv_smul_eq_iff.2 (Eq.symm ?_)` and prove the remaining obligations. Use `show ((g, (1 : GLG X.E n SG), (θ : GLQ X.E n Q)) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) • (((1, 1, fun P => ((cb P).out)⁻¹) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) • hex.choose) = p`. Rewrite using `[← mul_smul]`. Establish `e : ((g, (1 : GLG X.E n SG), (θ : GLQ X.E n Q)) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) * (1, 1, fun P => ((cb P).out)⁻¹) = (g, 1, 1) * (1, 1, c)`.

Use `Prod.ext (by simp) (Prod.ext (by simp) ?_)` and prove the remaining obligations. Use function extensionality and compare the values at `P`. Use `show ((c P)⁻¹)⁻¹ * (cb P).out * ((cb P).out)⁻¹ = 1 * c P`. Use `group`. Rewrite using `[e, mul_smul, ← hc]`.

Conclude with `smul_inv_smul _ p`. Use `fin_stab := by`. Introduce `p`. Use `DecoSet.finite_stabilizer (posStar_of_conj hX.conjE) (DecoF.deco p : DecoSet X.E n ST SG)` as an intermediate fact. Use `Finite.of_injective (fun a : MulAction.stabilizer (frmGSD (C.pull DecoF.deco) Λ Θ).G p => (⟨(a.1.1, (a.1.2.1 : GLG X.E n SG)), congrArg DecoF.deco a.2⟩ : MulAction.stabilizer (UF X.E n × GLG X.E n SG) (DecoF.deco p : DecoSet X.E n ST SG))) ?_` and prove the remaining obligations.

Introduce `a b hab`. Establish `h0 : ((a.1.1, (a.1.2.1 : GLG X.E n SG)) : UF X.E n × GLG X.E n SG) = (b.1.1, (b.1.2.1 : GLG X.E n SG))` using `congrArg Subtype.val hab`. Conclude with `Subtype.ext (dga_frm_stab_inj Λ Θ p a.2 b.2 (Prod.mk.inj h0).1)`. Use `nab_smul := by`. Introduce `g d`.

Take `⟨m, hm, hc⟩` from `frm_root Λ Θ hroot g`. Conclude with `(hC.nab_smul (g.1, (g.2.1 : GLG X.E n SG)) (DecoF.deco d)).trans (map_root_smul _ _ hm hc).symm`. Use `del_smul := by`. Introduce `g d`. Take `⟨m, hm, hc⟩` from `frm_root Λ Θ hroot g`.

Conclude with `(hC.del_smul (g.1, (g.2.1 : GLG X.E n SG)) (DecoF.deco d)).trans (map_root_smul _ _ hm hc).symm`. Use `inv := by`. Introduce `g (x : C.V) (y : C.V)`. Take `⟨m, hm, hc⟩` from `frm_root Λ Θ hroot g`. Use `show C.pair ((((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) • C.rho g.1 x) ((((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) • C.rho g.1 y) = C.pair x y`.

Rewrite using `[LinearMap.map_smulₛₗ₂, map_smul, hC.inv, smul_smul]`. Use `show (star (((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) * _) • _ = _`. Rewrite using `[star_mul_root hX.conjK hm hc, one_smul]`.
-/
theorem frmGSD_ok_of_finIdx (hX : X.Ok) (C : CoefPk X n (DecoSet X.E n ST SG)) (hC : C.Eqv)
    (hfi : ∀ P : Q, Finite (↥(GLint X.E n P.1) ⧸ (Θ P).H))
    (hroot : ∀ c : ↥Θ.grp, ∃ m : ℕ, 0 < m ∧ ((Θ.chr c : X.Kˣ) : X.K) ^ m = 1) : (frmGSD (C.pull DecoF.deco) Λ Θ).Ok where
  fin_orb := by
    obtain ⟨s, hs, hrep⟩ := DecoSet.finite_reps (ST := ST) (SG := SG) (n := n) (posStar_of_conj hX.conjE)
    have : Finite s := hs

    let pt : s → (∀ P : Q, ↥(GLint X.E n P.1) ⧸ (Θ P).H) → Option (DecoF X.E n ST SG Q) := fun d cb =>
      if h : ∃ p0 : DecoF X.E n ST SG Q, p0.deco = d.1 then
        some (((1, 1, fun P => ((cb P).out)⁻¹) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) • h.choose) else none
    have hfin : Finite (Option (s × (∀ P : Q, ↥(GLint X.E n P.1) ⧸ (Θ P).H))) := inferInstance
    by_cases hne : Nonempty (frmGSD (C.pull DecoF.deco) Λ Θ).Cl
    swap
    · have := not_nonempty_iff.1 hne
      exact inferInstance
    obtain ⟨c00⟩ := hne
    refine Finite.of_surjective (fun a : s × (∀ P : Q, ↥(GLint X.E n P.1) ⧸ (Θ P).H) =>
      match pt a.1 a.2 with
      | some p => (frmGSD (C.pull DecoF.deco) Λ Θ).cls p
      | none => c00) ?_
    intro c
    induction c using Quotient.inductionOn' with
    | h p =>
      obtain ⟨d0, hd0, g, hg⟩ := hrep (DecoF.deco p)

      let p1 : DecoF X.E n ST SG Q := ((g, 1, 1) : UF X.E n × GLG X.E n SG × GLQ X.E n Q)⁻¹ • p
      have hp1 : p1.deco = d0 := by
        show ((g, (1 : GLG X.E n SG)) : UF X.E n × GLG X.E n SG)⁻¹ • p.deco = d0
        rw [hg, inv_smul_smul]
      have hex : ∃ p0 : DecoF X.E n ST SG Q, p0.deco = d0 := ⟨p1, hp1⟩
      obtain ⟨c, hc⟩ := frm_exists_c p1 hex.choose (hp1.trans hex.choose_spec.symm)

      let cb : ∀ P : Q, ↥(GLint X.E n P.1) ⧸ (Θ P).H := fun P => QuotientGroup.mk ((c P)⁻¹)
      have hout : ∀ P : Q, ((c P)⁻¹)⁻¹ * (cb P).out ∈ (Θ P).H := fun P => QuotientGroup.eq.1 (QuotientGroup.out_eq' (cb P)).symm
      refine ⟨(⟨d0, hd0⟩, cb), ?_⟩
      have hpt : pt ⟨d0, hd0⟩ cb = some (((1, 1, fun P => ((cb P).out)⁻¹) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) • hex.choose) := dif_pos hex
      show (match pt ⟨d0, hd0⟩ cb with
        | some p => (frmGSD (C.pull DecoF.deco) Λ Θ).cls p
        | none => c00) = _
      rw [hpt]
      let θ : ↥Θ.grp := ⟨fun P => ((c P)⁻¹)⁻¹ * (cb P).out, fun P _ => hout P⟩
      refine ((frmGSD (C.pull DecoF.deco) Λ Θ).cls_eq_iff _ p).mpr ⟨((g, 1, θ) : FrmG Λ Θ)⁻¹, ?_⟩
      refine inv_smul_eq_iff.2 (Eq.symm ?_)
      show ((g, (1 : GLG X.E n SG), (θ : GLQ X.E n Q)) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) •
        (((1, 1, fun P => ((cb P).out)⁻¹) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) • hex.choose) = p
      rw [← mul_smul]
      have e : ((g, (1 : GLG X.E n SG), (θ : GLQ X.E n Q)) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) * (1, 1, fun P => ((cb P).out)⁻¹) =
          (g, 1, 1) * (1, 1, c) := by
        refine Prod.ext (by simp) (Prod.ext (by simp) ?_)
        funext P
        show ((c P)⁻¹)⁻¹ * (cb P).out * ((cb P).out)⁻¹ = 1 * c P
        group
      rw [e, mul_smul, ← hc]
      exact smul_inv_smul _ p
  fin_stab := by
    intro p
    have := DecoSet.finite_stabilizer (posStar_of_conj hX.conjE) (DecoF.deco p : DecoSet X.E n ST SG)
    refine Finite.of_injective
      (fun a : MulAction.stabilizer (frmGSD (C.pull DecoF.deco) Λ Θ).G p =>
        (⟨(a.1.1, (a.1.2.1 : GLG X.E n SG)), congrArg DecoF.deco a.2⟩ :
          MulAction.stabilizer (UF X.E n × GLG X.E n SG) (DecoF.deco p : DecoSet X.E n ST SG))) ?_
    intro a b hab
    have h0 : ((a.1.1, (a.1.2.1 : GLG X.E n SG)) : UF X.E n × GLG X.E n SG) = (b.1.1, (b.1.2.1 : GLG X.E n SG)) :=
      congrArg Subtype.val hab
    exact Subtype.ext (dga_frm_stab_inj Λ Θ p a.2 b.2 (Prod.mk.inj h0).1)
  nab_smul := by
    intro g d
    obtain ⟨m, hm, hc⟩ := frm_root Λ Θ hroot g
    exact (hC.nab_smul (g.1, (g.2.1 : GLG X.E n SG)) (DecoF.deco d)).trans (map_root_smul _ _ hm hc).symm
  del_smul := by
    intro g d
    obtain ⟨m, hm, hc⟩ := frm_root Λ Θ hroot g
    exact (hC.del_smul (g.1, (g.2.1 : GLG X.E n SG)) (DecoF.deco d)).trans (map_root_smul _ _ hm hc).symm
  inv := by
    intro g (x : C.V) (y : C.V)
    obtain ⟨m, hm, hc⟩ := frm_root Λ Θ hroot g
    show C.pair ((((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) • C.rho g.1 x)
      ((((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) • C.rho g.1 y) = C.pair x y
    rw [LinearMap.map_smulₛₗ₂, map_smul, hC.inv, smul_smul]
    show (star (((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) * _) • _ = _
    rw [star_mul_root hX.conjK hm hc, one_smul]

end Gen

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

/- English proof (translation)
Introduce `b` and use `frmGSD_ok_of_finIdx (L.levG j b) (L.levQ j b) hX (colVal W u j (Pr.vT u) Pr.vGs) (colVal_eqv W hX u j _ _) (hfi b) (hroot b)`.
-/
theorem chF_ok_of_finIdx (hX : X.Ok) (u : Pr.Word) (j : ℕ)
    (hfi : ∀ (b : L.β j) (P : QE sel (mu : Chr X.F X.E X.K)), Finite (↥(GLint X.E (R.N j) P.1) ⧸ (L.levQ j b P).H))
    (hroot : ∀ (b : L.β j) (c : ↥(L.levQ j b).grp), ∃ m : ℕ, 0 < m ∧ (((L.levQ j b).chr c : X.Kˣ) : X.K) ^ m = 1) :
    (chF W sel mu L u j).Ok := fun b =>
  frmGSD_ok_of_finIdx (L.levG j b) (L.levQ j b) hX (colVal W u j (Pr.vT u) Pr.vGs)
    (colVal_eqv W hX u j _ _) (hfi b) (hroot b)

end Chain

end Formalism.L2.Col
