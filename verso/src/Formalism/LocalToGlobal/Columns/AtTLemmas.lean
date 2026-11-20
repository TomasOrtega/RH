import Mathlib
import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice
import Formalism.LocalToGlobal.Columns.GSetLemmas
import Formalism.LocalToGlobal.Columns.ColFormsLemmas

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section DiaMoves

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `sup_le le_sup_left ?_` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Establish `e : a • (r • x) = (r • a) • x`.

Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[SetLike.mem_coe, e]`. Conclude with `Submodule.mem_sup_right (Submodule.subset_span ⟨r • a, Submodule.smul_mem _ r ha, rfl⟩)`.

Use `sup_le le_sup_left ?_` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Take `⟨s, p, hp, e⟩` from `P.isMaximal.exists_inv hr`. Establish `e2 : a • x = a • (p • x) + (s • a) • (r • x)`.

Establish `e3 : (s • a) • (r • x) = a • ((s * r) • x)`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e3, ← smul_add, ← add_smul, add_comm, e, one_smul]`.

Rewrite using `[SetLike.mem_coe, e2]`. Conclude with `Submodule.add_mem_sup (inv_smul_mem ha (Submodule.smul_mem_smul hp hx)) (Submodule.subset_span ⟨s • a, Submodule.smul_mem _ s ha, rfl⟩)`.
-/
theorem upA_smul {P : HeightOneSpectrum (𝓞 E)} {N : Submodule (𝓞 E) (Sp E n)} {x : Sp E n} (hx : x ∈ N)
    {r : 𝓞 E} (hr : r ∉ P.asIdeal) : upA P.asIdeal N (r • x) = upA P.asIdeal N x := by
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    have e : a • (r • x) = (r • a) • x := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
      ring
    rw [SetLike.mem_coe, e]
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨r • a, Submodule.smul_mem _ r ha, rfl⟩)
  · refine sup_le le_sup_left ?_
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨s, p, hp, e⟩ := P.isMaximal.exists_inv hr
    have e2 : a • x = a • (p • x) + (s • a) • (r • x) := by
      have e3 : (s • a) • (r • x) = a • ((s * r) • x) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul]
        ring
      rw [e3, ← smul_add, ← add_smul, add_comm, e, one_smul]
    rw [SetLike.mem_coe, e2]
    exact Submodule.add_mem_sup (inv_smul_mem ha (Submodule.smul_mem_smul hp hx))
      (Submodule.subset_span ⟨s • a, Submodule.smul_mem _ s ha, rfl⟩)

/- English proof (translation)
Take `⟨r, hr⟩` from `Ideal.Quotient.mk_surjective c.1`. Use `⟨r, hr, fun h0 => ?_⟩` and prove the remaining obligations. Rewrite `h0` using `[← Ideal.Quotient.eq_zero_iff_mem, hr]`. Conclude with `c.ne_zero h0`.
-/
theorem exists_lift_unit (P : HeightOneSpectrum (𝓞 E)) (c : (𝓞 E ⧸ P.asIdeal)ˣ) :
    ∃ r : 𝓞 E, Ideal.Quotient.mk P.asIdeal r = c.1 ∧ r ∉ P.asIdeal := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective c.1
  refine ⟨r, hr, fun h0 => ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, hr] at h0
  exact c.ne_zero h0

/- English proof (translation)
Take `⟨x, hx, hfx, rfl⟩` from `h`. Take `⟨r, hr, hrP⟩` from `exists_lift_unit P.1 (c P)⁻¹`. Establish `hN : upN P.1.asIdeal d.N (r • x) = upN P.1.asIdeal d.N x`. Unfold `upN`. Rewrite using `[upA_smul hx hrP]`.

Use `⟨r • x, Submodule.smul_mem _ r hx, ?_, ?_⟩` and prove the remaining obligations. Use `show (c P).1 * d.f P (r • x) = 1`. Rewrite using `[hd.f_smul P r x (le_locP _ _ hx), hr, hfx, mul_one, Units.mul_inv]`. Use `ext1`. Conclude with `hN.symm`.

Use function extensionality and compare the values at `Q y`. Simplify using `only [Deco.dia, Deco.up]`. Break down `eq_or_ne Q P with rfl | hQ` into its components or cases. Rewrite using `[Function.update_self, Function.update_self]`. Establish `hiff : y ∈ localization₂ Q.1.asIdeal (upN Q.1.asIdeal d.N (r • x)) ↔ y ∈ localization₂ Q.1.asIdeal (upN Q.1.asIdeal d.N x)` using `by rw [hN]`.

Distinguish the cases in `hy : y ∈ localization₂ Q.1.asIdeal (upN Q.1.asIdeal d.N x)`. Rewrite using `[if_pos hy]`. Conclude with `(if_pos (hiff.2 hy)).symm`. Rewrite using `[if_neg hy, mul_zero]`. Conclude with `(if_neg (fun h' => hy (hiff.1 h'))).symm`.

Rewrite using `[Function.update_of_ne hQ, Function.update_of_ne hQ]`. Both sides reduce to the same expression.
-/
theorem Deco.IsUp.dia {P : ST} {q : 𝓞 E} {d d' : Deco E n ST SG} (hd : d.Ok) (h : Deco.IsUp P q d d')
    (c : DiaG E ST) : Deco.IsUp P q (d.dia c) (d'.dia c) := by
  classical
  obtain ⟨x, hx, hfx, rfl⟩ := h
  obtain ⟨r, hr, hrP⟩ := exists_lift_unit P.1 (c P)⁻¹
  have hN : upN P.1.asIdeal d.N (r • x) = upN P.1.asIdeal d.N x := by
    unfold upN
    rw [upA_smul hx hrP]
  refine ⟨r • x, Submodule.smul_mem _ r hx, ?_, ?_⟩
  · show (c P).1 * d.f P (r • x) = 1
    rw [hd.f_smul P r x (le_locP _ _ hx), hr, hfx, mul_one, Units.mul_inv]
  · ext1
    · exact hN.symm
    · funext Q y
      simp only [Deco.dia, Deco.up]
      rcases eq_or_ne Q P with rfl | hQ
      · rw [Function.update_self, Function.update_self]
        have hiff : y ∈ localization₂ Q.1.asIdeal (upN Q.1.asIdeal d.N (r • x)) ↔
            y ∈ localization₂ Q.1.asIdeal (upN Q.1.asIdeal d.N x) := by rw [hN]
        by_cases hy : y ∈ localization₂ Q.1.asIdeal (upN Q.1.asIdeal d.N x)
        · rw [if_pos hy]
          exact (if_pos (hiff.2 hy)).symm
        · rw [if_neg hy, mul_zero]
          exact (if_neg (fun h' => hy (hiff.1 h'))).symm
      · rw [Function.update_of_ne hQ, Function.update_of_ne hQ]
    · rfl

/- English proof (translation)
Unfold `Deco.kerAt`. Use `congr 1`. Use extensionality with `x`. Use `show (x ∈ d.N ∧ (c P).1 * d.f P x = 0) ↔ (x ∈ d.N ∧ d.f P x = 0)`. Rewrite using `[Units.mul_right_eq_zero]`.
-/
theorem Deco.kerAt_dia (d : Deco E n ST SG) (c : DiaG E ST) (P : ST) : (d.dia c).kerAt P = d.kerAt P := by
  unfold Deco.kerAt
  congr 1
  ext x
  show (x ∈ d.N ∧ (c P).1 * d.f P x = 0) ↔ (x ∈ d.N ∧ d.f P x = 0)
  rw [Units.mul_right_eq_zero]

/- English proof (translation)
Take `⟨h1, h2⟩` from `h`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `ext1`. Use `show d'.N = (d.dia c).dnN P`. Unfold `Deco.dnN`.

Rewrite using `[Deco.kerAt_dia]`. Conclude with `congrArg Deco.N h1`. Use function extensionality and compare the values at `Q y`. Establish `h3 : d'.f Q = (d.dn P (d'.f P)).f Q` using `by rw [← h1]`. Simplify using `only [Deco.dia, Deco.dn] at h3 ⊢`.

Break down `eq_or_ne Q P with rfl | hQ` into its components or cases. Rewrite using `[Function.update_self]`. Rewrite using `[Function.update_of_ne hQ]`. Rewrite `h3` using `[Function.update_of_ne hQ]`. Rewrite using `[h3]`.

Establish `h6` using `congrArg Deco.be h1`. Conclude with `h6`. Introduce `e he hfe`. Take `⟨r, hr, hrP⟩` from `exists_lift_unit P.1 (c P)`. Establish `hfe' : (c P).1 * d.f P e = 1` using `hfe`.

Establish `h4 : d.f P (r • e) = 1` using `by rw [hd.f_smul P r e (le_locP _ _ he), hr, hfe']`. Establish `h5` using `h2 (r • e) (Submodule.smul_mem _ r he) h4`. Use `show (c P).1 * d'.f P (q • e) = a`. Rewrite `h5` using `[smul_comm]`. Distinguish the cases in `hy : q • e ∈ d'.at P.1`.

Rewrite using `[← h5, hd'.f_smul P r _ hy, hr]`. Establish `hy' : r • q • e ∉ d'.at P.1`. Introduce `hm`. Apply `hy` to reduce the goal to its premises. Take `⟨s, hs, hm'⟩` from `(mem_locP P.1 _ _).1 hm`.

Use `(mem_locP P.1 _ _).2 ⟨s * r, fun hsr => ?_, by rw [mul_smul]; exact hm'⟩` and prove the remaining obligations. Break down `P.1.isPrime.mem_or_mem hsr with h' | h'` into its components or cases. Conclude with `hs h'`. Conclude with `hrP h'`. Rewrite using `[← h5, hd'.f_off P _ hy, hd'.f_off P _ hy', mul_zero]`.
-/
theorem Deco.IsDnA.dia {P : ST} {q : 𝓞 E} {a : 𝓞 E ⧸ P.1.asIdeal} {d d' : Deco E n ST SG} (hd : d.Ok)
    (hd' : d'.Ok) (h : Deco.IsDnA P q a d d') (c : DiaG E ST) : Deco.IsDnA P q a (d.dia c) (d'.dia c) := by
  classical
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · ext1
    · show d'.N = (d.dia c).dnN P
      unfold Deco.dnN
      rw [Deco.kerAt_dia]
      exact congrArg Deco.N h1
    · funext Q y
      have h3 : d'.f Q = (d.dn P (d'.f P)).f Q := by rw [← h1]
      simp only [Deco.dia, Deco.dn] at h3 ⊢
      rcases eq_or_ne Q P with rfl | hQ
      · rw [Function.update_self]
      · rw [Function.update_of_ne hQ]
        rw [Function.update_of_ne hQ] at h3
        rw [h3]
    · have h6 := congrArg Deco.be h1
      exact h6
  · intro e he hfe
    obtain ⟨r, hr, hrP⟩ := exists_lift_unit P.1 (c P)
    have hfe' : (c P).1 * d.f P e = 1 := hfe
    have h4 : d.f P (r • e) = 1 := by rw [hd.f_smul P r e (le_locP _ _ he), hr, hfe']
    have h5 := h2 (r • e) (Submodule.smul_mem _ r he) h4
    show (c P).1 * d'.f P (q • e) = a
    rw [smul_comm] at h5
    by_cases hy : q • e ∈ d'.at P.1
    · rw [← h5, hd'.f_smul P r _ hy, hr]
    · have hy' : r • q • e ∉ d'.at P.1 := by
        intro hm
        apply hy
        obtain ⟨s, hs, hm'⟩ := (mem_locP P.1 _ _).1 hm
        refine (mem_locP P.1 _ _).2 ⟨s * r, fun hsr => ?_, by rw [mul_smul]; exact hm'⟩
        rcases P.1.isPrime.mem_or_mem hsr with h' | h'
        · exact hs h'
        · exact hrP h'
      rw [← h5, hd'.f_off P _ hy, hd'.f_off P _ hy', mul_zero]

instance diaAction : MulAction (DiaG E ST) (DecoSet E n ST SG) where
  smul c d := d.dia c
  one_smul := DecoSet.dia_one
  mul_smul c c' d := DecoSet.dia_mul c c' d

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem DecoSet.dia_smul_def (c : DiaG E ST) (d : DecoSet E n ST SG) : c • d = d.dia c := rfl

instance diaComm : SMulCommClass (DiaG E ST) (UF E n × GLG E n SG) (DecoSet E n ST SG) :=
  ⟨fun c a d => (DecoSet.dia_smul c a d)⟩

/- English proof (translation)
The claim follows from `inv_smul_smul c d`.
-/
theorem DecoSet.dia_inv_dia (c : DiaG E ST) (d : DecoSet E n ST SG) : (d.dia c).dia c⁻¹ = d :=
  inv_smul_smul c d

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1 : ((d'.dia c).dia c⁻¹) ∈ ((d.dia c).dia c⁻¹).upSet P q` using `Deco.IsUp.dia (d.dia c).2 h c⁻¹`. Rewrite `h1` using `[DecoSet.dia_inv_dia, DecoSet.dia_inv_dia]`. Then use the resulting hypothesis. Introduce `h`.

Conclude with `Deco.IsUp.dia d.2 h c`.
-/
theorem DecoSet.dia_mem_upSet (c : DiaG E ST) (P : ST) (q : 𝓞 E) (d d' : DecoSet E n ST SG) :
    d'.dia c ∈ (d.dia c).upSet P q ↔ d' ∈ d.upSet P q := by
  constructor
  · intro h
    have h1 : ((d'.dia c).dia c⁻¹) ∈ ((d.dia c).dia c⁻¹).upSet P q := Deco.IsUp.dia (d.dia c).2 h c⁻¹
    rwa [DecoSet.dia_inv_dia, DecoSet.dia_inv_dia] at h1
  · intro h
    exact Deco.IsUp.dia d.2 h c

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1 : ((d'.dia c).dia c⁻¹) ∈ ((d.dia c).dia c⁻¹).dnSetA P q a` using `Deco.IsDnA.dia (d.dia c).2 (d'.dia c).2 h c⁻¹`. Rewrite `h1` using `[DecoSet.dia_inv_dia, DecoSet.dia_inv_dia]`. Then use the resulting hypothesis. Introduce `h`.

Conclude with `Deco.IsDnA.dia d.2 d'.2 h c`.
-/
theorem DecoSet.dia_mem_dnSetA (c : DiaG E ST) (P : ST) (q : 𝓞 E) (a : 𝓞 E ⧸ P.1.asIdeal)
    (d d' : DecoSet E n ST SG) : d'.dia c ∈ (d.dia c).dnSetA P q a ↔ d' ∈ d.dnSetA P q a := by
  constructor
  · intro h
    have h1 : ((d'.dia c).dia c⁻¹) ∈ ((d.dia c).dia c⁻¹).dnSetA P q a :=
      Deco.IsDnA.dia (d.dia c).2 (d'.dia c).2 h c⁻¹
    rwa [DecoSet.dia_inv_dia, DecoSet.dia_inv_dia] at h1
  · intro h
    exact Deco.IsDnA.dia d.2 d'.2 h c

/- English proof (translation)
The claim follows from `Finset.sum_equiv (MulAction.toPerm c) (fun d' => (h d d').symm) (fun _ _ => rfl)`.
-/
theorem DecoSet.sum_dia {M : Type*} [AddCommMonoid M] (nb : DecoSet E n ST SG → Finset (DecoSet E n ST SG))
    (c : DiaG E ST) (h : ∀ d d', d'.dia c ∈ nb (d.dia c) ↔ d' ∈ nb d) (F : DecoSet E n ST SG → M)
    (d : DecoSet E n ST SG) : ∑ d' ∈ nb d, F (d'.dia c) = ∑ d' ∈ nb (d.dia c), F d' :=
  Finset.sum_equiv (MulAction.toPerm c) (fun d' => (h d d').symm) (fun _ _ => rfl)

end DiaMoves

section OpsL

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG)

/- English proof (translation)
Unfold `diaG`. Conclude with `LocOp.ofMap_op_apply (S := formGSD C Λ) (S' := formGSD C Λ) _ _ _ _ _ φ d`.
-/
theorem diaG_apply (c : DiaG X.E ST) (φ : (formGSD C Λ).EqFun) (d : DecoSet X.E n ST SG) :
    ((diaG C Λ c φ : (formGSD C Λ).EqFun) : (formGSD C Λ).D → (formGSD C Λ).V) d =
      (φ : (formGSD C Λ).D → (formGSD C Λ).V) (d.dia c) := by
  unfold diaG
  exact LocOp.ofMap_op_apply (S := formGSD C Λ) (S' := formGSD C Λ) _ _ _ _ _ φ d

/- English proof (translation)
Unfold `diamondOperatorOnForms'`. Conclude with `LocOp.ofMap_op_apply (S := formGSD C Λ) (S' := formGSD C Λ) _ _ _ _ _ φ d`.
-/
theorem diamond_action_apply (P : ST) (c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) (φ : (formGSD C Λ).EqFun) (d : DecoSet X.E n ST SG) :
    ((diamondOperatorOnForms' C Λ P c φ : (formGSD C Λ).EqFun) : (formGSD C Λ).D → (formGSD C Λ).V) d =
      (φ : (formGSD C Λ).D → (formGSD C Λ).V) (d.dia1 P c) := by
  unfold diamondOperatorOnForms'
  exact LocOp.ofMap_op_apply (S := formGSD C Λ) (S' := formGSD C Λ) _ _ _ _ _ φ d

open Classical in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem diamond_single_eq (P : ST) (c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) : diamondOperatorOnForms' C Λ P c = diaG C Λ (Pi.mulSingle P c) := rfl

/- English proof (translation)
Unfold `UG`. Conclude with `LocOp.ofNbr_op_apply (S := formGSD C Λ) (S' := formGSD C Λ) _ _ _ _ _ φ d`.
-/
theorem UG_apply (P : ST) (q : 𝓞 X.E) (φ : (formGSD C Λ).EqFun) (d : DecoSet X.E n ST SG) :
    ((UG C Λ P q φ : (formGSD C Λ).EqFun) : (formGSD C Λ).D → (formGSD C Λ).V) d =
      ∑ d' ∈ (DecoSet.upSet_finite d P q).toFinset, (φ : (formGSD C Λ).D → (formGSD C Λ).V) d' := by
  unfold UG
  exact LocOp.ofNbr_op_apply (S := formGSD C Λ) (S' := formGSD C Λ) _ _ _ _ _ φ d

/- English proof (translation)
Unfold `DaG`. Conclude with `LocOp.ofNbr_op_apply (S := formGSD C Λ) (S' := formGSD C Λ) _ _ _ _ _ φ d`.
-/
theorem DaG_apply (P : ST) (q : 𝓞 X.E) (a : 𝓞 X.E ⧸ P.1.asIdeal) (φ : (formGSD C Λ).EqFun)
    (d : DecoSet X.E n ST SG) :
    ((DaG C Λ P q a φ : (formGSD C Λ).EqFun) : (formGSD C Λ).D → (formGSD C Λ).V) d =
      ∑ d' ∈ (DecoSet.dnSetA_finite d P q a).toFinset, (φ : (formGSD C Λ).D → (formGSD C Λ).V) d' := by
  unfold DaG
  exact LocOp.ofNbr_op_apply (S := formGSD C Λ) (S' := formGSD C Λ) _ _ _ _ _ φ d

/- English proof (translation)
Unfold `NmG`. Conclude with `Finset.sum_congr (by ext; simp) fun _ _ => rfl`.
-/
theorem NmG_eq (P : ST) [Fintype (𝓞 X.E ⧸ P.1.asIdeal)ˣ] : NmG C Λ P = ∑ c, diamondOperatorOnForms' C Λ P c := by
  unfold NmG
  exact Finset.sum_congr (by ext; simp) fun _ _ => rfl

/- English proof (translation)
Unfold `GsG`. Conclude with `Finset.sum_congr (by ext; simp) fun _ _ => rfl`.
-/
theorem GsG_eq (P : ST) (ψ : AddChar (𝓞 X.E ⧸ P.1.asIdeal) X.K) [Fintype (𝓞 X.E ⧸ P.1.asIdeal)ˣ] :
    GsG C Λ P ψ = ∑ c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ, ψ (c : 𝓞 X.E ⧸ P.1.asIdeal) • diamondOperatorOnForms' C Λ P c := by
  unfold GsG
  exact Finset.sum_congr (by ext; simp) fun _ _ => rfl

/- English proof (translation)
Unfold `FFG`. Conclude with `Finset.sum_congr (by ext; simp) fun _ _ => rfl`.
-/
theorem FFG_eq (P : ST) (q : 𝓞 X.E) (ψ : AddChar (𝓞 X.E ⧸ P.1.asIdeal) X.K) [Fintype (𝓞 X.E ⧸ P.1.asIdeal)] :
    FFG C Λ P q ψ = ∑ a : 𝓞 X.E ⧸ P.1.asIdeal, ψ a • DaG C Λ P q a := by
  unfold FFG
  exact Finset.sum_congr (by ext; simp) fun _ _ => rfl

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `φ`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `d`. Rewrite using `[diaG_apply, DecoSet.dia_one]`.

Both sides reduce to the same expression.
-/
theorem diaG_one : diaG C Λ 1 = 1 := by
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  funext d
  rw [diaG_apply, DecoSet.dia_one]
  rfl

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `φ`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `d`. Rewrite using `[Module.End.mul_apply, diaG_apply, diaG_apply, diaG_apply, mul_comm, DecoSet.dia_mul]`.
-/
theorem diaG_mul (c c' : DiaG X.E ST) : diaG C Λ (c * c') = diaG C Λ c * diaG C Λ c' := by
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  funext d
  rw [Module.End.mul_apply, diaG_apply, diaG_apply, diaG_apply, mul_comm, DecoSet.dia_mul]

def diaHom : DiaG X.E ST →* Module.End X.K (formGSD C Λ).EqFun where
  toFun := diaG C Λ
  map_one' := diaG_one C Λ
  map_mul' := diaG_mul C Λ

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun c a d => DecoSet.dia_smul c (FormG.incl Λ a) d⟩ diaG C Λ c = (GSD.Slice.dia (formGSD C Λ) c).op := rfl`.
-/
theorem diaG_eq_dia (c : DiaG X.E ST) :
    haveI : SMulCommClass (DiaG X.E ST) (formGSD C Λ).G (formGSD C Λ).D :=
      ⟨fun c a d => DecoSet.dia_smul c (FormG.incl Λ a) d⟩
    diaG C Λ c = (GSD.Slice.dia (formGSD C Λ) c).op := rfl

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `φ`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `d`. Rewrite using `[Module.End.mul_apply, Module.End.mul_apply, UG_apply, diaG_apply, UG_apply]`.

Use `(Finset.sum_congr rfl fun d' _ => diaG_apply C Λ c φ d').trans ?_` and prove the remaining obligations. Conclude with `DecoSet.sum_dia (fun d => (DecoSet.upSet_finite d P q).toFinset) c (fun d d' => by`. Rewrite using `[Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]`. Conclude with `DecoSet.dia_mem_upSet c P q d d')`. Use the proof step `(fun d' => (φ : (formGSD C Λ).D → (formGSD C Λ).V) d') d`.
-/
theorem UG_diaG (P : ST) (q : 𝓞 X.E) (c : DiaG X.E ST) :
    UG C Λ P q * diaG C Λ c = diaG C Λ c * UG C Λ P q := by
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  funext d
  rw [Module.End.mul_apply, Module.End.mul_apply, UG_apply, diaG_apply, UG_apply]
  refine (Finset.sum_congr rfl fun d' _ => diaG_apply C Λ c φ d').trans ?_
  exact DecoSet.sum_dia (fun d => (DecoSet.upSet_finite d P q).toFinset) c
    (fun d d' => by
      rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      exact DecoSet.dia_mem_upSet c P q d d')
    (fun d' => (φ : (formGSD C Λ).D → (formGSD C Λ).V) d') d

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `φ`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `d`. Rewrite using `[Module.End.mul_apply, Module.End.mul_apply, DaG_apply, diaG_apply, DaG_apply]`.

Use `(Finset.sum_congr rfl fun d' _ => diaG_apply C Λ c φ d').trans ?_` and prove the remaining obligations. Conclude with `DecoSet.sum_dia (fun d => (DecoSet.dnSetA_finite d P q a).toFinset) c (fun d d' => by`. Rewrite using `[Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]`. Conclude with `DecoSet.dia_mem_dnSetA c P q a d d')`. Use the proof step `(fun d' => (φ : (formGSD C Λ).D → (formGSD C Λ).V) d') d`.
-/
theorem DaG_diaG (P : ST) (q : 𝓞 X.E) (a : 𝓞 X.E ⧸ P.1.asIdeal) (c : DiaG X.E ST) :
    DaG C Λ P q a * diaG C Λ c = diaG C Λ c * DaG C Λ P q a := by
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  funext d
  rw [Module.End.mul_apply, Module.End.mul_apply, DaG_apply, diaG_apply, DaG_apply]
  refine (Finset.sum_congr rfl fun d' _ => diaG_apply C Λ c φ d').trans ?_
  exact DecoSet.sum_dia (fun d => (DecoSet.dnSetA_finite d P q a).toFinset) c
    (fun d d' => by
      rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      exact DecoSet.dia_mem_dnSetA c P q a d d')
    (fun d' => (φ : (formGSD C Λ).D → (formGSD C Λ).V) d') d

/- English proof (translation)
Unfold `NmG`. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun c _ => hA _`.
-/
theorem comm_NmG {A : Module.End X.K (formGSD C Λ).EqFun} (hA : ∀ c, A * diaG C Λ c = diaG C Λ c * A) (P : ST) :
    A * NmG C Λ P = NmG C Λ P * A := by
  unfold NmG
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun c _ => hA _

/- English proof (translation)
Rewrite using `[← diaG_mul, ← diaG_mul, mul_comm]`.
-/
theorem diaG_comm (c c' : DiaG X.E ST) : diaG C Λ c * diaG C Λ c' = diaG C Λ c' * diaG C Λ c := by
  rw [← diaG_mul, ← diaG_mul, mul_comm]

end OpsL

section ColsL

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

/- English proof (translation)
Simplify using `only [ColRamV, Submodule.mem_iInf, LinearMap.mem_ker]`.
-/
theorem mem_ColRamV (u : Pr.Word) (j : ℕ) (φ : ColV W Ch u j) :
    φ ∈ ColRamV W Ch u j ↔ ∀ P, NmOp W Ch u j P φ = 0 := by
  simp only [ColRamV, Submodule.mem_iInf, LinearMap.mem_ker]

/- English proof (translation)
Rewrite `hφ`, the goal using `[mem_ColRamV]`. Introduce `P`. Establish `h1 : NmOp W Ch u j P * A = A * NmOp W Ch u j P` using `(comm_NmG _ _ hA P).symm`. Rewrite using `[← Module.End.mul_apply, h1, Module.End.mul_apply, hφ P, map_zero]`.
-/
theorem mem_ColRamV_of_comm (u : Pr.Word) (j : ℕ) {A : Module.End X.K (ColV W Ch u j)}
    (hA : ∀ c, A * diaG (colVal W u j (Pr.vT u) Pr.vGs) (colLev Ch j) c =
      diaG (colVal W u j (Pr.vT u) Pr.vGs) (colLev Ch j) c * A)
    {φ : ColV W Ch u j} (hφ : φ ∈ ColRamV W Ch u j) : A φ ∈ ColRamV W Ch u j := by
  rw [mem_ColRamV] at hφ ⊢
  intro P
  have h1 : NmOp W Ch u j P * A = A * NmOp W Ch u j P := (comm_NmG _ _ hA P).symm
  rw [← Module.End.mul_apply, h1, Module.End.mul_apply, hφ P, map_zero]

/- English proof (translation)
The claim follows from `mem_ColRamV_of_comm W Ch u j (UG_diaG _ _ P _) hφ`.
-/
theorem UOp_mem_ColRamV (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) {φ : ColV W Ch u j}
    (hφ : φ ∈ ColRamV W Ch u j) : UOp W Ch u j P φ ∈ ColRamV W Ch u j :=
  mem_ColRamV_of_comm W Ch u j (UG_diaG _ _ P _) hφ

/- English proof (translation)
The claim follows from `mem_ColRamV_of_comm W Ch u j (DaG_diaG _ _ P _ a) hφ`.
-/
theorem DaOp_mem_ColRamV (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) (a : 𝓞 X.E ⧸ P.1.asIdeal)
    {φ : ColV W Ch u j} (hφ : φ ∈ ColRamV W Ch u j) : DaOp W Ch u j P a φ ∈ ColRamV W Ch u j :=
  mem_ColRamV_of_comm W Ch u j (DaG_diaG _ _ P _ a) hφ

/- English proof (translation)
The claim follows from `DaOp_mem_ColRamV W Ch u j P 1 hφ`.
-/
theorem DOp_mem_ColRamV (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) {φ : ColV W Ch u j}
    (hφ : φ ∈ ColRamV W Ch u j) : DOp W Ch u j P φ ∈ ColRamV W Ch u j :=
  DaOp_mem_ColRamV W Ch u j P 1 hφ

/- English proof (translation)
The claim follows from `mem_ColRamV_of_comm W Ch u j (A := diaOp W Ch u j P c) (fun c' => diaG_comm _ _ _ c') hφ`.
-/
theorem diaOp_mem_ColRamV (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) (c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ)
    {φ : ColV W Ch u j} (hφ : φ ∈ ColRamV W Ch u j) : diaOp W Ch u j P c φ ∈ ColRamV W Ch u j :=
  mem_ColRamV_of_comm W Ch u j (A := diaOp W Ch u j P c) (fun c' => diaG_comm _ _ _ c') hφ

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => intro φ hφ`. Simplify using `using hφ`. Consider the case `cons A l ih`. Introduce `φ hφ`.

Rewrite using `[List.prod_cons, Module.End.mul_apply]`. Conclude with `h A (List.mem_cons_self) _ (ih (fun B hB => h B (List.mem_cons_of_mem _ hB)) φ hφ)`.
-/
theorem list_prod_mem {M : Type*} [AddCommGroup M] [Module X.K M] (p : Submodule X.K M)
    (l : List (Module.End X.K M)) (h : ∀ A ∈ l, ∀ φ ∈ p, A φ ∈ p) : ∀ φ ∈ p, l.prod φ ∈ p := by
  induction l with
  | nil => intro φ hφ; simpa using hφ
  | cons A l ih =>
    intro φ hφ
    rw [List.prod_cons, Module.End.mul_apply]
    exact h A (List.mem_cons_self) _ (ih (fun B hB => h B (List.mem_cons_of_mem _ hB)) φ hφ)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => intro φ hφ`. Simplify using `using hφ`. Consider the case `succ k ih`. Introduce `φ hφ`.

Rewrite using `[pow_succ, Module.End.mul_apply]`. Conclude with `ih _ (h φ hφ)`.
-/
theorem pow_mem {M : Type*} [AddCommGroup M] [Module X.K M] (p : Submodule X.K M)
    (A : Module.End X.K M) (h : ∀ φ ∈ p, A φ ∈ p) (k : ℕ) : ∀ φ ∈ p, (A ^ k) φ ∈ p := by
  induction k with
  | zero => intro φ hφ; simpa using hφ
  | succ k ih =>
    intro φ hφ
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ (h φ hφ)

/- English proof (translation)
Use `list_prod_mem (ColRamV W Ch u j) _ ?_ φ hφ` and prove the remaining obligations. Introduce `A hA ψ hψ`. Take `⟨P, -, rfl⟩` from `List.mem_map.1 hA`. Conclude with `UOp_mem_ColRamV W Ch u j P hψ`.
-/
theorem UprodC_mem_ColRamV (u : Pr.Word) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.K)) {φ : ColV W Ch u j}
    (hφ : φ ∈ ColRamV W Ch u j) : UprodC W Ch u j w φ ∈ ColRamV W Ch u j := by
  refine list_prod_mem (ColRamV W Ch u j) _ ?_ φ hφ
  intro A hA ψ hψ
  obtain ⟨P, -, rfl⟩ := List.mem_map.1 hA
  exact UOp_mem_ColRamV W Ch u j P hψ

/- English proof (translation)
Unfold `TUmC`. Rewrite using `[LinearMap.smul_apply]`. Conclude with `Submodule.smul_mem _ _ (pow_mem (MramV W Ch u) _ (fun ψ hψ => UprodC_mem_ColRamV W Ch u 0 w hψ) R.m φ hφ)`.
-/
theorem TUmC_mem_MramV (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) {φ : MfV W Ch u}
    (hφ : φ ∈ MramV W Ch u) : TUmC W Ch u w φ ∈ MramV W Ch u := by
  unfold TUmC
  rw [LinearMap.smul_apply]
  exact Submodule.smul_mem _ _
    (pow_mem (MramV W Ch u) _ (fun ψ hψ => UprodC_mem_ColRamV W Ch u 0 w hψ) R.m φ hφ)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_ramified_sublattice_iff (u : Pr.Word) (φ : MfV W Ch u) :
    φ ∈ ramifiedSublattice W Ch u ↔ φ ∈ MfL W Ch u ∧ φ ∈ MramV W Ch u := Iff.rfl

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_MramL (u : Pr.Word) (φ : MramV W Ch u) : φ ∈ MramL W Ch u ↔ ramIncl W Ch u φ ∈ MfL W Ch u := Iff.rfl

/- English proof (translation)
The claim follows from `Subtype.val_injective`.
-/
theorem ramIncl_injective (u : Pr.Word) : Function.Injective (ramIncl W Ch u) := Subtype.val_injective

/- English proof (translation)
The claim follows from `Submodule.range_subtype _`.
-/
theorem range_ramIncl (u : Pr.Word) : LinearMap.range (ramIncl W Ch u) = MramV W Ch u :=
  Submodule.range_subtype _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem MramL_eq_comap (u : Pr.Word) :
    MramL W Ch u = (MfL W Ch u).comap ((ramIncl W Ch u).restrictScalars (𝓞 X.K)) := rfl

/- English proof (translation)
Use extensionality with `φ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨ψ, hψ, rfl⟩`. Conclude with `⟨hψ, ψ.2⟩`. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `⟨⟨φ, h2⟩, h1, rfl⟩`.
-/
theorem MramL_map (u : Pr.Word) :
    (MramL W Ch u).map ((ramIncl W Ch u).restrictScalars (𝓞 X.K)) = ramifiedSublattice W Ch u := by
  ext φ
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    exact ⟨hψ, ψ.2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨φ, h2⟩, h1, rfl⟩

/- English proof (translation)
The claim follows from `inf_le_left`.
-/
theorem ramified_sublattice_le_integral (u : Pr.Word) : ramifiedSublattice W Ch u ≤ MfL W Ch u := inf_le_left

/- English proof (translation)
Use `⟨hφ, ?_⟩` and prove the remaining obligations. Establish `h1 : (algebraMap (𝓞 X.K) X.K a) • φ ∈ MramV W Ch u`. Rewrite using `[algebraMap_smul]`. Conclude with `h.2`. Establish `h2 : algebraMap (𝓞 X.K) X.K a ≠ 0`.

Introduce `h0`. Conclude with `ha (RingOfIntegers.coe_injective (by simpa using h0))`. Conclude with `((MramV W Ch u).smul_mem_iff h2).1 h1`.
-/
theorem ramified_sublattice_saturated (u : Pr.Word) {a : 𝓞 X.K} (ha : a ≠ 0) {φ : MfV W Ch u} (hφ : φ ∈ MfL W Ch u)
    (h : a • φ ∈ ramifiedSublattice W Ch u) : φ ∈ ramifiedSublattice W Ch u := by
  refine ⟨hφ, ?_⟩
  have h1 : (algebraMap (𝓞 X.K) X.K a) • φ ∈ MramV W Ch u := by
    rw [algebraMap_smul]
    exact h.2
  have h2 : algebraMap (𝓞 X.K) X.K a ≠ 0 := by
    intro h0
    exact ha (RingOfIntegers.coe_injective (by simpa using h0))
  exact ((MramV W Ch u).smul_mem_iff h2).1 h1

/- English proof (translation)
Introduce and unpack `_ ⟨φ, hφ, rfl⟩`. Conclude with `TUmC_mem_MramV W Ch u w hφ.2`.
-/
theorem scaled_ramified_le_span (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) :
    scaledRamifiedLattice W Ch u w ≤ (MramV W Ch u).restrictScalars (𝓞 X.K) := by
  rintro _ ⟨φ, hφ, rfl⟩
  exact TUmC_mem_MramV W Ch u w hφ.2

/- English proof (translation)
Use extensionality with `φ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨ψ, hψ, rfl⟩`. Conclude with `hψ`. Introduce `h`.

Conclude with `⟨⟨φ, scaled_ramified_le_span W Ch u w h⟩, h, rfl⟩`.
-/
theorem NlamG_map (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) :
    (NlamG W Ch u w).map ((ramIncl W Ch u).restrictScalars (𝓞 X.K)) = scaledRamifiedLattice W Ch u w := by
  ext φ
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    exact hψ
  · intro h
    exact ⟨⟨φ, scaled_ramified_le_span W Ch u w h⟩, h, rfl⟩

def TUmR (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : Module.End X.K (MramV W Ch u) :=
  (TUmC W Ch u w).restrict fun _ h => TUmC_mem_MramV W Ch u w h

/- English proof (translation)
Use extensionality with `φ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨ψ, hψ, e⟩`. Conclude with `⟨⟨ψ, hψ.2⟩, hψ.1, Subtype.ext e⟩`. Introduce and unpack `⟨ψ, hψ, rfl⟩`.

Conclude with `⟨ψ.1, ⟨hψ, ψ.2⟩, rfl⟩`.
-/
theorem NlamG_eq_map (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) :
    NlamG W Ch u w = (MramL W Ch u).map ((TUmR W Ch u w).restrictScalars (𝓞 X.K)) := by
  ext φ
  constructor
  · rintro ⟨ψ, hψ, e⟩
    exact ⟨⟨ψ, hψ.2⟩, hψ.1, Subtype.ext e⟩
  · rintro ⟨ψ, hψ, rfl⟩
    exact ⟨ψ.1, ⟨hψ, ψ.2⟩, rfl⟩

end ColsL

section SeenL

variable {X : Fields} {Pr : Primes X}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_pullW (τ : X.Tau) (w : HeightOneSpectrum (𝓞 X.K)) (x : 𝓞 X.E) :
    x ∈ (pullW τ w).asIdeal ↔ X.embO τ x ∈ w.asIdeal := Iff.rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_embO (τ : X.Tau) (x : 𝓞 X.E) : ((X.embO τ x : 𝓞 X.K) : X.K) = X.emb τ (x : X.E) := rfl

/- English proof (translation)
The claim follows from `mem_divs (hPr.piT_ne_zero u) _`.
-/
theorem pullW_mem_vT (hPr : Pr.Ok) (u : Pr.Word) (τ : X.Tau) (w : HeightOneSpectrum (𝓞 X.K)) :
    pullW τ w ∈ Pr.vT u ↔ X.embO τ (Pr.piT u) ∈ w.asIdeal :=
  mem_divs (hPr.piT_ne_zero u) _

/- English proof (translation)
The claim follows from `RingOfIntegers.ext (hx τ τ')`.
-/
theorem embO_of_Kq {x : 𝓞 X.E} (hx : (x : X.E) ∈ X.Kq) (τ τ' : X.Tau) : X.embO τ x = X.embO τ' x :=
  RingOfIntegers.ext (hx τ τ')

/- English proof (translation)
Introduce `τ τ'`. Use `show X.emb τ (star (x : X.E)) = X.emb τ' (star (x : X.E))`. Rewrite using `[hX.emb_star, hX.emb_star, hx τ τ']`.
-/
theorem conjO_mem_Kq (hX : X.Ok) {x : 𝓞 X.E} (hx : (x : X.E) ∈ X.Kq) : ((X.conjO x : 𝓞 X.E) : X.E) ∈ X.Kq := by
  intro τ τ'
  show X.emb τ (star (x : X.E)) = X.emb τ' (star (x : X.E))
  rw [hX.emb_star, hX.emb_star, hx τ τ']

/- English proof (translation)
The claim follows from `forall_congr' fun τ => (pullW_mem_vT hPr u τ w).symm`.
-/
theorem seenC_iff (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) :
    seenC Pr u w ↔ ∀ τ, pullW τ w ∈ Pr.vT u :=
  forall_congr' fun τ => (pullW_mem_vT hPr u τ w).symm

/- English proof (translation)
Distinguish the cases in `hne : Nonempty X.Tau`. Take `⟨τ₀⟩` from `hne`. Establish `h1 : X.embO τ₀ (Pr.piT u) * X.embO τ₀ (X.conjO (Pr.piT u)) ∈ w.asIdeal`. Rewrite using `[← map_mul, hPr.piT_norm u, map_natCast]`. Conclude with `hw`.

Break down `w.isPrime.mem_or_mem h1 with h | h` into its components or cases. Use `left`. Introduce `τ`. Rewrite using `[embO_of_Kq (hPr.piT_Kq u) τ τ₀]`. Conclude with `h`.

Use `right`. Introduce `τ`. Rewrite using `[embO_of_Kq (conjO_mem_Kq hX (hPr.piT_Kq u)) τ τ₀]`. Conclude with `h`. Use `left`.

Introduce `τ`. Conclude with `absurd ⟨τ⟩ hne`.
-/
theorem seenC_or_seenBarC (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K))
    (hw : (Pr.T u : 𝓞 X.K) ∈ w.asIdeal) : seenC Pr u w ∨ seenBarC Pr u w := by
  by_cases hne : Nonempty X.Tau
  · obtain ⟨τ₀⟩ := hne
    have h1 : X.embO τ₀ (Pr.piT u) * X.embO τ₀ (X.conjO (Pr.piT u)) ∈ w.asIdeal := by
      rw [← map_mul, hPr.piT_norm u, map_natCast]
      exact hw
    rcases w.isPrime.mem_or_mem h1 with h | h
    · left
      intro τ
      rw [embO_of_Kq (hPr.piT_Kq u) τ τ₀]
      exact h
    · right
      intro τ
      rw [embO_of_Kq (conjO_mem_Kq hX (hPr.piT_Kq u)) τ τ₀]
      exact h
  · left
    intro τ
    exact absurd ⟨τ⟩ hne

/- English proof (translation)
Take `⟨a, b, e⟩` from `hPr.piT_cop u`. Apply `w.isPrime.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `e'` using `congrArg (X.embO τ) e`. Rewrite `e'` using `[map_add, map_mul, map_mul, map_one]`.

Rewrite using `[← e']`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)`.
-/
theorem not_seen_both (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (τ : X.Tau)
    (h1 : X.embO τ (Pr.piT u) ∈ w.asIdeal) (h2 : X.embO τ (X.conjO (Pr.piT u)) ∈ w.asIdeal) : False := by
  obtain ⟨a, b, e⟩ := hPr.piT_cop u
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have e' := congrArg (X.embO τ) e
  rw [map_add, map_mul, map_mul, map_one] at e'
  rw [← e']
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

variable {R : Ranks} (W : Wts X Pr.Word R)

/- English proof (translation)
Unfold `topsP`. Conclude with `Finset.filter_true_of_mem fun τ _ => (pullW_mem_vT hPr u τ w).2 (h τ)`.
-/
theorem topsP_of_seenC (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (h : seenC Pr u w) :
    topsP W u w = W.tops := by
  classical
  unfold topsP
  exact Finset.filter_true_of_mem fun τ _ => (pullW_mem_vT hPr u τ w).2 (h τ)

/- English proof (translation)
Unfold `topsP`. Conclude with `Finset.filter_false_of_mem fun τ _ h1 => not_seen_both hPr u w τ ((pullW_mem_vT hPr u τ w).1 h1) (h τ)`.
-/
theorem topsP_of_seenBarC (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (h : seenBarC Pr u w) :
    topsP W u w = ∅ := by
  classical
  unfold topsP
  exact Finset.filter_false_of_mem fun τ _ h1 => not_seen_both hPr u w τ ((pullW_mem_vT hPr u τ w).1 h1) (h τ)

/- English proof (translation)
Unfold `VVTc topsP SeesP`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨τ, hτ, e⟩`. Conclude with `⟨τ, ⟨hτ, by rw [e]; exact P.2⟩, e⟩`.

Introduce and unpack `⟨τ, ⟨hτ, -⟩, e⟩`. Conclude with `⟨τ, hτ, e⟩`.
-/
theorem mem_VVTc (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (P : {P // P ∈ Pr.vT u}) :
    P ∈ VVTc W u w ↔ ∃ τ ∈ topsP W u w, pullW τ w = P.1 := by
  classical
  unfold VVTc topsP SeesP
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨τ, hτ, e⟩
    exact ⟨τ, ⟨hτ, by rw [e]; exact P.2⟩, e⟩
  · rintro ⟨τ, ⟨hτ, -⟩, e⟩
    exact ⟨τ, hτ, e⟩

/- English proof (translation)
Use extensionality with `P`. Rewrite using `[mem_VVTc, topsP_of_seenBarC W hPr u w h]`. Simplify using the standard rewrite rules.
-/
theorem VVTc_of_seenBarC (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (h : seenBarC Pr u w) :
    VVTc W u w = ∅ := by
  classical
  ext P
  rw [mem_VVTc, topsP_of_seenBarC W hPr u w h]
  simp

end SeenL

end Formalism.L2.Col
