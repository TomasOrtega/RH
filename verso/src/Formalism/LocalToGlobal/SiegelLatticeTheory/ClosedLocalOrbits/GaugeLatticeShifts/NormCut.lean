import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOpStmt
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormCore
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormAsm

noncomputable section

open scoped Classical ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NormCut

section HSop

variable {Wq Wp : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

def opOf (x : Formalism.L2.SG.PackageTie.HS Wq Wp) : Wq →L[ℂ] Wp :=
  ∑ i, (innerSL ℂ (stdOrthonormalBasis ℂ Wq i)).smulRight (x i)

/- English proof (translation)
Simplify using `[opOf, ContinuousLinearMap.sum_apply]`.
-/
theorem opOf_apply (x : Formalism.L2.SG.PackageTie.HS Wq Wp) (e : Wq) :
    opOf x e = ∑ i, inner ℂ (stdOrthonormalBasis ℂ Wq i) e • x i := by
  simp [opOf, ContinuousLinearMap.sum_apply]

/- English proof (translation)
Use extensionality with `e`. Simplify using `[opOf_apply, Finset.sum_add_distrib, smul_add]`.
-/
theorem opOf_add (x y : Formalism.L2.SG.PackageTie.HS Wq Wp) : opOf (x + y) = opOf x + opOf y := by
  ext e
  simp [opOf_apply, Finset.sum_add_distrib, smul_add]

/- English proof (translation)
Use extensionality with `e`. Simplify using `[opOf_apply, Finset.smul_sum, smul_smul, mul_comm]`.
-/
theorem opOf_smul (c : ℂ) (x : Formalism.L2.SG.PackageTie.HS Wq Wp) : opOf (c • x) = c • opOf x := by
  ext e
  simp [opOf_apply, Finset.smul_sum, smul_smul, mul_comm]

/- English proof (translation)
Establish `h : ∀ i, (Formalism.L2.SG.PackageTie.hsEmb (opOf x)) i = opOf x (stdOrthonormalBasis ℂ Wq i)` using `fun i => rfl`. Apply `PiLp.ext` to reduce the goal to its premises. Introduce `i`. Rewrite using `[h, opOf_apply]`. Simplify using `[orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ Wq).orthonormal]`.
-/
theorem hsEmb_opOf (x : Formalism.L2.SG.PackageTie.HS Wq Wp) : Formalism.L2.SG.PackageTie.hsEmb (opOf x) = x := by
  have h : ∀ i, (Formalism.L2.SG.PackageTie.hsEmb (opOf x)) i = opOf x (stdOrthonormalBasis ℂ Wq i) := fun i => rfl
  apply PiLp.ext
  intro i
  rw [h, opOf_apply]
  simp [orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ Wq).orthonormal]

/- English proof (translation)
Establish `h : ∀ i, (Formalism.L2.SG.PackageTie.hsEmb A) i = A (stdOrthonormalBasis ℂ Wq i)` using `fun i => rfl`. Use extensionality with `e`. Rewrite using `[opOf_apply]`. Use `conv_rhs => rw [← (stdOrthonormalBasis ℂ Wq).sum_repr' e]`. Rewrite using `[map_sum]`.

Simplify using `only [map_smul, h]`.
-/
theorem opOf_hsEmb (A : Wq →L[ℂ] Wp) : opOf (Formalism.L2.SG.PackageTie.hsEmb A) = A := by
  have h : ∀ i, (Formalism.L2.SG.PackageTie.hsEmb A) i = A (stdOrthonormalBasis ℂ Wq i) := fun i => rfl
  ext e
  rw [opOf_apply]
  conv_rhs => rw [← (stdOrthonormalBasis ℂ Wq).sum_repr' e]
  rw [map_sum]
  simp only [map_smul, h]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hsEmb_eq_hsV (A : Wq →L[ℂ] Wp) : Formalism.L2.SG.PackageTie.hsEmb A = hsV A := rfl

end HSop

section Blocks

variable {C C' V V' : Type} [Fintype C] [Fintype C'] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V] [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

/- English proof (translation)
Use extensionality with `v`. Use `first`. Consider the case `rfl`. Consider the case `simp [blockOf]`.
-/
theorem blockOf_add (A B : PiLp 2 (fun _ : C' => V') →L[ℂ] PiLp 2 (fun _ : C => V)) (ρ : C) (ρ' : C') :
    blockOf (A + B) ρ ρ' = blockOf A ρ ρ' + blockOf B ρ ρ' := by
  ext v
  first
  | rfl
  | simp [blockOf]

/- English proof (translation)
Use extensionality with `v`. Use `first`. Consider the case `rfl`. Consider the case `simp [blockOf]`.
-/
theorem blockOf_smul (c : ℂ) (A : PiLp 2 (fun _ : C' => V') →L[ℂ] PiLp 2 (fun _ : C => V)) (ρ : C) (ρ' : C') :
    blockOf (c • A) ρ ρ' = c • blockOf A ρ ρ' := by
  ext v
  first
  | rfl
  | simp [blockOf]

def BlL (ρ : C) (ρ' : C') :
    Formalism.L2.SG.PackageTie.HS (PiLp 2 (fun _ : C' => V')) (PiLp 2 (fun _ : C => V)) →ₗ[ℂ]
      Formalism.L2.SG.PackageTie.HS V' V where
  toFun x := Formalism.L2.SG.PackageTie.hsEmb (blockOf (opOf x) ρ ρ')
  map_add' x y := by rw [opOf_add, blockOf_add, map_add]
  map_smul' c x := by rw [opOf_smul, blockOf_smul, map_smul]; rfl

def Bl (ρ : C) (ρ' : C') :
    Formalism.L2.SG.PackageTie.HS (PiLp 2 (fun _ : C' => V')) (PiLp 2 (fun _ : C => V)) →L[ℂ]
      Formalism.L2.SG.PackageTie.HS V' V :=
  LinearMap.toContinuousLinearMap (BlL ρ ρ')

/- English proof (translation)
Establish `h : Bl ρ ρ' (Formalism.L2.SG.PackageTie.hsEmb A) = Formalism.L2.SG.PackageTie.hsEmb (blockOf (opOf (Formalism.L2.SG.PackageTie.hsEmb A)) ρ ρ')` using `rfl`. Rewrite using `[h, opOf_hsEmb]`.
-/
theorem Bl_hsEmb (A : PiLp 2 (fun _ : C' => V') →L[ℂ] PiLp 2 (fun _ : C => V)) (ρ : C) (ρ' : C') :
    Bl ρ ρ' (Formalism.L2.SG.PackageTie.hsEmb A) = Formalism.L2.SG.PackageTie.hsEmb (blockOf A ρ ρ') := by
  have h : Bl ρ ρ' (Formalism.L2.SG.PackageTie.hsEmb A) =
      Formalism.L2.SG.PackageTie.hsEmb (blockOf (opOf (Formalism.L2.SG.PackageTie.hsEmb A)) ρ ρ') := rfl
  rw [h, opOf_hsEmb]

/- English proof (translation)
Establish `key` using `hHS C C' V V' (opOf x) (opOf y)`. Simplify using `only [← hsEmb_eq_hsV, hsEmb_opOf] at key`. Conclude with `key`.
-/
theorem inner_Bl (hHS : HSBlocks)
    (x y : Formalism.L2.SG.PackageTie.HS (PiLp 2 (fun _ : C' => V')) (PiLp 2 (fun _ : C => V))) :
    inner ℂ x y = ∑ ρ, ∑ ρ', inner ℂ (Bl ρ ρ' x) (Bl ρ ρ' y) := by
  have key := hHS C C' V V' (opOf x) (opOf y)
  simp only [← hsEmb_eq_hsV, hsEmb_opOf] at key
  exact key

end Blocks

section Conc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (TR : TypedRed X) (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (FdN FdN' : Set X.B.I.Ginf)

def UG : Set (Iof TR) := {x | ∀ v, Formalism.L2.SG.GGMirabolic.IsUni D.R.k (x v)}

def psiG (x : Iof TR) : ℂ := ∏ v, Formalism.L2.SG.GGMirabolic.psiNat (TR.psi0 v) (x v)

variable {TR} in

def lamQ {w : D.what₂.Word} {rs : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (c : ColSys X w rs) (ρ : c.Cl) :
    {Λ // Λ ∈ rs} := ⟨c.lamOf ρ, c.lam_mem ρ⟩

def positionT (t : GTerm X u u' F0 F0' what₂ rows') : {Λ // Λ ∈ what₂} × {Λ' // Λ' ∈ rows'} :=
  (⟨t.lam, t.mem⟩, ⟨t.lam', t.mem'⟩)

def aT (t : GTerm X u u' F0 F0' what₂ rows') : Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u) :=
  Formalism.L2.SG.PackageTie.hsEmb (ampN cs cs' FdN FdN' t)

variable (F0 F0') in

def ColPhase (sc : cs.Cl → Iof TR) (sc' : cs'.Cl → Iof TR) : Prop :=
  ∀ (t : GTerm X u u' F0 F0' what₂ rows') (ρ : cs.Cl) (ρ' : cs'.Cl), cs.lamOf ρ = t.lam → cs'.lamOf ρ' = t.lam' →
    (if kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt ∈ X.K2 then
      chiL X (kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt) else 0) =
    psiG TR ((sc ρ)⁻¹ * iotaOf TR cs cs' t * sc' ρ')

variable (F0) in

def ColFree {w : D.what₂.Word} {rs : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (c : ColSys X w rs)
    (A : {Λ // Λ ∈ rs} → Set (Iof TR)) (sc : c.Cl → Iof TR) : Prop :=
  ∀ q : {Λ // Λ ∈ rs},
    Function.Bijective
        (fun x : A q × {ρ : c.Cl // lamQ c ρ = q} × UG TR => (x.1 : Iof TR) * sc x.2.1.1 * (x.2.2 : Iof TR)) ∧
      wRow D F0 q.1 = ((Nat.card (A q) : ℝ))⁻¹

variable (F0 F0') in

def SatGram (S : Set (GTerm X u u' F0 F0' what₂ rows')) (A : {Λ // Λ ∈ what₂} → Set (Iof TR))
    (A' : {Λ' // Λ' ∈ rows'} → Set (Iof TR)) : Prop :=
  ∀ q : {Λ // Λ ∈ what₂} × {Λ' // Λ' ∈ rows'},
    (∀ b ∈ A q.1, ∀ i j,
      inner ℂ (Zs S positionT (iotaOf TR cs cs') (aT cs cs' FdN FdN') q (b * i))
          (Zs S positionT (iotaOf TR cs cs') (aT cs cs' FdN FdN') q (b * j)) =
        inner ℂ (Zs S positionT (iotaOf TR cs cs') (aT cs cs' FdN FdN') q i)
          (Zs S positionT (iotaOf TR cs cs') (aT cs cs' FdN FdN') q j)) ∧
    (∀ b ∈ A' q.2, ∀ i j,
      inner ℂ (Zs S positionT (iotaOf TR cs cs') (aT cs cs' FdN FdN') q (i * b⁻¹))
          (Zs S positionT (iotaOf TR cs cs') (aT cs cs' FdN FdN') q (j * b⁻¹)) =
        inner ℂ (Zs S positionT (iotaOf TR cs cs') (aT cs cs' FdN FdN') q i)
          (Zs S positionT (iotaOf TR cs cs') (aT cs cs' FdN FdN') q j))

/- English proof (translation)
Establish `key : ∀ x, (blockOf (Formalism.L2.SG.TermOp.aTerm cs cs' FdN FdN' t) ρ ρ') x = ∑ ρ'', blk cs cs' FdN FdN' t ρ ρ'' ((Pi.single ρ' x : cs'.Cl → X.Vpi u') ρ'')` using `fun x => rfl`. Use extensionality with `x`. Rewrite using `[key x, Finset.sum_eq_single ρ']`. Rewrite using `[Pi.single_eq_same]`. Introduce `b _ hb`.

Rewrite using `[Pi.single_eq_of_ne hb, map_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem blockOf_aTerm (t : GTerm X u u' F0 F0' what₂ rows') (ρ : cs.Cl) (ρ' : cs'.Cl) :
    blockOf (aTerm cs cs' FdN FdN' t) ρ ρ' = blk cs cs' FdN FdN' t ρ ρ' := by
  have key : ∀ x, (blockOf (Formalism.L2.SG.TermOp.aTerm cs cs' FdN FdN' t) ρ ρ') x =
      ∑ ρ'', blk cs cs' FdN FdN' t ρ ρ'' ((Pi.single ρ' x : cs'.Cl → X.Vpi u') ρ'') := fun x => rfl
  ext x
  rw [key x, Finset.sum_eq_single ρ']
  · rw [Pi.single_eq_same]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, map_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

variable {TR cs cs' FdN FdN'} in

/- English proof (translation)
Distinguish the cases in `hs : cs.lamOf ρ = t.lam ∧ cs'.lamOf ρ' = t.lam'`. Take `⟨h1, h2⟩` from `hs`. Establish `hposition : positionT t = (lamQ cs ρ, lamQ cs' ρ')` using `Prod.ext (Subtype.ext h1.symm) (Subtype.ext h2.symm)`. Establish `hP` using `hPh t ρ ρ' h1 h2`. Rewrite using `[if_pos hposition]`.

Distinguish the cases in `hk : kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt ∈ X.K2`. Rewrite `hP` using `[if_pos hk]`. Establish `hb : blk cs cs' FdN FdN' t ρ ρ' = chiL X (kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt) • ampN cs cs' FdN FdN' t`. Rewrite using `[blk, if_pos ⟨h1, h2, hk⟩, ampN, level_char_eq_mul, hChi t ρ ρ' h1 h2 hk, smul_smul, smul_smul, smul_smul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hb, map_smul, ← hP]`. Both sides reduce to the same expression. Rewrite `hP` using `[if_neg hk]`. Establish `hb : blk cs cs' FdN FdN' t ρ ρ' = 0`.

Rewrite using `[blk, if_neg (fun h => hk h.2.2)]`. Rewrite using `[hb, map_zero, ← hP, zero_smul]`. Establish `hb : blk cs cs' FdN FdN' t ρ ρ' = 0`. Rewrite using `[blk, if_neg (fun h => hs ⟨h.1, h.2.1⟩)]`. Establish `hposition : ¬ positionT t = (lamQ cs ρ, lamQ cs' ρ')`.

Introduce `he`. Simplify using `only [positionT, lamQ, Prod.mk.injEq, Subtype.mk.injEq] at he`. Conclude with `hs ⟨he.1.symm, he.2.symm⟩`. Rewrite using `[hb, map_zero, if_neg hposition]`.
-/
theorem hsEmb_blk {sc : cs.Cl → Iof TR} {sc' : cs'.Cl → Iof TR} (hChi : ChiNIndep F0 F0' cs cs')
    (hPh : ColPhase F0 F0' TR cs cs' sc sc') (t : GTerm X u u' F0 F0' what₂ rows') (ρ : cs.Cl) (ρ' : cs'.Cl) :
    Formalism.L2.SG.PackageTie.hsEmb (blk cs cs' FdN FdN' t ρ ρ') =
      if positionT t = (lamQ cs ρ, lamQ cs' ρ') then
        psiG TR ((sc ρ)⁻¹ * iotaOf TR cs cs' t * sc' ρ') • aT cs cs' FdN FdN' t else 0 := by
  by_cases hs : cs.lamOf ρ = t.lam ∧ cs'.lamOf ρ' = t.lam'
  · obtain ⟨h1, h2⟩ := hs
    have hposition : positionT t = (lamQ cs ρ, lamQ cs' ρ') := Prod.ext (Subtype.ext h1.symm) (Subtype.ext h2.symm)
    have hP := hPh t ρ ρ' h1 h2
    rw [if_pos hposition]
    by_cases hk : kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt ∈ X.K2
    · rw [if_pos hk] at hP
      have hb : blk cs cs' FdN FdN' t ρ ρ' =
          chiL X (kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt) • ampN cs cs' FdN FdN' t := by
        rw [blk, if_pos ⟨h1, h2, hk⟩, ampN, level_char_eq_mul, hChi t ρ ρ' h1 h2 hk, smul_smul, smul_smul, smul_smul]
        congr 1
        ring
      rw [hb, map_smul, ← hP]
      rfl
    · rw [if_neg hk] at hP
      have hb : blk cs cs' FdN FdN' t ρ ρ' = 0 := by
        rw [blk, if_neg (fun h => hk h.2.2)]
      rw [hb, map_zero, ← hP, zero_smul]
  · have hb : blk cs cs' FdN FdN' t ρ ρ' = 0 := by
      rw [blk, if_neg (fun h => hs ⟨h.1, h.2.1⟩)]
    have hposition : ¬ positionT t = (lamQ cs ρ, lamQ cs' ρ') := by
      intro he
      simp only [positionT, lamQ, Prod.mk.injEq, Subtype.mk.injEq] at he
      exact hs ⟨he.1.symm, he.2.symm⟩
    rw [hb, map_zero, if_neg hposition]

variable (F0 F0') in

/- English proof (translation)
Use `haveI := FiniteDimensional.complete ℂ (X.Vpi u)`. Use `haveI := FiniteDimensional.complete ℂ (X.Vpi u')`. Establish `hpos : ∀ {P Q : Type} (B : Set (Iof TR)) (f : B × P × Q → Iof TR), Function.Bijective f → 0 < Nat.card B`. Introduce `P Q B f hf`. Take `⟨x, -⟩` from `hf.2 1`.

Conclude with `Nat.card_pos_iff.mpr ⟨⟨x.1⟩, inferInstance⟩`. Establish `hU : ∀ y : Iof TR, y ∈ UG TR → ∀ v, Formalism.L2.SG.GGMirabolic.IsUni D.R.k (y v)` using `fun y hy => hy`. Conclude with `normExp_abs (X := tOf F0 F0' TR cs cs' FdN FdN') (S := S) (lamR := lamQ cs) (lamR' := lamQ cs') (Bl := fun ρ ρ' => Bl ρ ρ') (hBl := inner_Bl hHS) (intersection_update_fsHerm_neg_one := positionT) (a := aT cs cs' FdN FdN') (ιt := iotaOf TR cs cs') (p := psiG TR) (sR := sc) (sR' := …`. Rewrite using `[Bl_hsEmb, blockOf_aTerm, hsEmb_blk hChi hPh]`. Apply the tactic sequence `split_ifs <;> rfl)`.

Use the proof step `(w := fun q => Real.sqrt (wRow D F0 q.1.1 * wRow D F0' q.2.1))`. Apply the tactic sequence `(hw0 := fun q => by try dsimp only`. Rewrite using `[(hF q.1).2, (hF' q.2).2]`. Apply `Real.sqrt_pos.mpr` to reduce the goal to its premises. Apply `mul_pos` to reduce the goal to its premises.

Conclude with `inv_pos.mpr (by exact_mod_cast hpos _ _ (hF q.1).1)`. Conclude with `inv_pos.mpr (by exact_mod_cast hpos _ _ (hF' q.2).1))`. Use the proof step `(hvec := fun t => by show Formalism.L2.SG.TermOp.vec cs cs' FdN FdN' t = _`. Simplify using `only [Formalism.L2.SG.TermOp.vec, positionT]`. Use `congr 1`.

Use function extensionality and compare the values at `q`. Distinguish the cases in `h : q = (⟨t.lam, t.mem⟩, ⟨t.lam', t.mem'⟩)`. Substitute `h` using the available equality. Conclude with `Eq.trans (if_pos rfl) (if_pos rfl).symm`. Conclude with `Eq.trans (if_neg h) (if_neg h).symm)`.

Use the proof step `(hio := fun t => rfl) (U := UG TR)`. Use the proof step `(h0 := fun x hx => by`. Simplify using `only [UG, Set.mem_setOf_eq, not_forall] at hx`. Take `⟨v, hv⟩` from `hx`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ v) (by rw [Formalism.L2.SG.GGMirabolic.psiNat, if_neg hv]))`.

Use the proof step `(hr := fun x y hy => by`. Simplify using `only [psiG, Pi.mul_apply, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun v _ => (hPsi _ _ (TR.psi0 v) (x v) (y v) (hU y hy v)).1)`. Use the proof step `(hl := fun x y hy => by`. Simplify using `only [psiG, Pi.mul_apply, ← Finset.prod_mul_distrib]`.

Conclude with `Finset.prod_congr rfl fun v _ => (hPsi _ _ (TR.psi0 v) (x v) (y v) (hU y hy v)).2.1)`. Use the proof step `(hn := fun y hy => by`. Simplify using `only [psiG, map_prod, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_eq_one fun v _ => (hPsi _ _ (TR.psi0 v) 1 (y v) (hU y hy v)).2.2)`. Use the proof step `(hGG := fun i j => by show conj (Formalism.L2.SG.GGMirabolic.gamProd TR.psi0 (j⁻¹ * i)) = _`.

Use `congr 1`. Take `⟨h1, h2⟩` from `hGam TR.Pl TR.Fq D.R.k TR.psi0 (j⁻¹ * i)`. Establish `hc : Nat.card (UG TR) = ∏ v, Formalism.L2.SG.GGMirabolic.cardU (TR.Fq v) D.R.k` using `h2`. Rewrite using `[h1, gamOf, hc, Nat.cast_prod]`. Use the proof step `rfl)`.

Use the proof step `(A := A) (A' := A') (hA := fun q => (hF q).1) (hA' := fun q => (hF' q).1)`. Apply the tactic sequence `(hwA := fun q => by try dsimp only`. Rewrite using `[Real.sq_sqrt (by rw [(hF q.1).2, (hF' q.2).2]; positivity), (hF q.1).2, (hF' q.2).2, mul_inv])`. Use the proof step `(hsatL := fun q => (hSat q).1) (hsatR := fun q => (hSat q).2) (hsum := hAbs.1) (hsumv := hAbs.2.1)`.
-/
theorem normExpansionOn_tOf (hHS : HSBlocks) (hGam : GamProdSum) (hPsi : PsiNatEquiv)
    (S : Set (GTerm X u u' F0 F0' what₂ rows')) (hAbs : (tOf F0 F0' TR cs cs' FdN FdN').AbsConv)
    (hChi : ChiNIndep F0 F0' cs cs') (sc : cs.Cl → Iof TR) (sc' : cs'.Cl → Iof TR)
    (hPh : ColPhase F0 F0' TR cs cs' sc sc') (A : {Λ // Λ ∈ what₂} → Set (Iof TR))
    (A' : {Λ' // Λ' ∈ rows'} → Set (Iof TR)) (hF : ColFree F0 TR cs A sc) (hF' : ColFree F0' TR cs' A' sc')
    (hSat : SatGram F0 F0' TR cs cs' FdN FdN' S A A') :
    (tOf F0 F0' TR cs cs' FdN FdN').NormExpansionOn S := by
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  haveI := FiniteDimensional.complete ℂ (X.Vpi u')
  have hpos : ∀ {P Q : Type} (B : Set (Iof TR)) (f : B × P × Q → Iof TR), Function.Bijective f →
      0 < Nat.card B := by
    intro P Q B f hf
    obtain ⟨x, -⟩ := hf.2 1
    exact Nat.card_pos_iff.mpr ⟨⟨x.1⟩, inferInstance⟩
  have hU : ∀ y : Iof TR, y ∈ UG TR → ∀ v, Formalism.L2.SG.GGMirabolic.IsUni D.R.k (y v) := fun y hy => hy
  exact normExp_abs (X := tOf F0 F0' TR cs cs' FdN FdN') (S := S) (lamR := lamQ cs) (lamR' := lamQ cs')
    (Bl := fun ρ ρ' => Bl ρ ρ') (hBl := inner_Bl hHS) (intersection_update_fsHerm_neg_one := positionT) (a := aT cs cs' FdN FdN')
    (ιt := iotaOf TR cs cs') (p := psiG TR) (sR := sc) (sR' := sc')
    (hop := fun t ρ ρ' => by
      show Bl ρ ρ' (Formalism.L2.SG.PackageTie.hsEmb (Formalism.L2.SG.TermOp.aTerm cs cs' FdN FdN' t)) = _
      rw [Bl_hsEmb, blockOf_aTerm, hsEmb_blk hChi hPh]
      split_ifs <;> rfl)
    (w := fun q => Real.sqrt (wRow D F0 q.1.1 * wRow D F0' q.2.1))
    (hw0 := fun q => by
      try dsimp only
      rw [(hF q.1).2, (hF' q.2).2]
      apply Real.sqrt_pos.mpr
      apply mul_pos
      · exact inv_pos.mpr (by exact_mod_cast hpos _ _ (hF q.1).1)
      · exact inv_pos.mpr (by exact_mod_cast hpos _ _ (hF' q.2).1))
    (hvec := fun t => by
      show Formalism.L2.SG.TermOp.vec cs cs' FdN FdN' t = _
      simp only [Formalism.L2.SG.TermOp.vec, positionT]
      congr 1
      funext q
      by_cases h : q = (⟨t.lam, t.mem⟩, ⟨t.lam', t.mem'⟩)
      · subst h
        exact Eq.trans (if_pos rfl) (if_pos rfl).symm
      · exact Eq.trans (if_neg h) (if_neg h).symm)
    (hio := fun t => rfl) (U := UG TR)
    (h0 := fun x hx => by
      simp only [UG, Set.mem_setOf_eq, not_forall] at hx
      obtain ⟨v, hv⟩ := hx
      exact Finset.prod_eq_zero (Finset.mem_univ v) (by rw [Formalism.L2.SG.GGMirabolic.psiNat, if_neg hv]))
    (hr := fun x y hy => by
      simp only [psiG, Pi.mul_apply, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun v _ => (hPsi _ _ (TR.psi0 v) (x v) (y v) (hU y hy v)).1)
    (hl := fun x y hy => by
      simp only [psiG, Pi.mul_apply, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun v _ => (hPsi _ _ (TR.psi0 v) (x v) (y v) (hU y hy v)).2.1)
    (hn := fun y hy => by
      simp only [psiG, map_prod, ← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun v _ => (hPsi _ _ (TR.psi0 v) 1 (y v) (hU y hy v)).2.2)
    (hGG := fun i j => by
      show conj (Formalism.L2.SG.GGMirabolic.gamProd TR.psi0 (j⁻¹ * i)) = _
      congr 1
      obtain ⟨h1, h2⟩ := hGam TR.Pl TR.Fq D.R.k TR.psi0 (j⁻¹ * i)
      have hc : Nat.card (UG TR) = ∏ v, Formalism.L2.SG.GGMirabolic.cardU (TR.Fq v) D.R.k := h2
      rw [h1, gamOf, hc, Nat.cast_prod]
      rfl)
    (A := A) (A' := A') (hA := fun q => (hF q).1) (hA' := fun q => (hF' q).1)
    (hwA := fun q => by
      try dsimp only
      rw [Real.sq_sqrt (by rw [(hF q.1).2, (hF' q.2).2]; positivity), (hF q.1).2, (hF' q.2).2, mul_inv])
    (hsatL := fun q => (hSat q).1) (hsatR := fun q => (hSat q).2) (hsum := hAbs.1) (hsumv := hAbs.2.1)

variable (F0 F0') in

/- English proof (translation)
Unfold `NormExpSat`. Conclude with `⟨normExpansionOn_tOf (hHS := hHS) (hGam := hGam) (hPsi := hPsi) (hAbs := hAbs) (hChi := hChi) (hPh := hPh) (hF := hF) (hF' := hF') (hSat := hSg), normExpansionOn_tOf (hHS := hHS) (hGam := hGam) (hPsi := hPsi) (hAbs := hAbs) (hChi := hChi) (hPh := hPh) (hF := hF) (hF' := hF') (hSa …`.
-/
theorem normExpSat_of (hHS : HSBlocks) (hGam : GamProdSum) (hPsi : PsiNatEquiv)
    (hAbs : (tOf F0 F0' TR cs cs' FdN FdN').AbsConv)
    (hChi : ChiNIndep F0 F0' cs cs') (sc : cs.Cl → Iof TR) (sc' : cs'.Cl → Iof TR)
    (hPh : ColPhase F0 F0' TR cs cs' sc sc') (A : {Λ // Λ ∈ what₂} → Set (Iof TR))
    (A' : {Λ' // Λ' ∈ rows'} → Set (Iof TR)) (hF : ColFree F0 TR cs A sc) (hF' : ColFree F0' TR cs' A' sc')
    (hSg : SatGram F0 F0' TR cs cs' FdN FdN' (tOf F0 F0' TR cs cs' FdN FdN').genSet A A')
    (hSn : SatGram F0 F0' TR cs cs' FdN FdN' (tOf F0 F0' TR cs cs' FdN FdN').ngSet A A') :
    NormExpSat F0 F0' TR cs cs' FdN FdN' := by
  unfold NormExpSat
  exact ⟨normExpansionOn_tOf (hHS := hHS) (hGam := hGam) (hPsi := hPsi) (hAbs := hAbs) (hChi := hChi) (hPh := hPh)
      (hF := hF) (hF' := hF') (hSat := hSg),
    normExpansionOn_tOf (hHS := hHS) (hGam := hGam) (hPsi := hPsi) (hAbs := hAbs) (hChi := hChi) (hPh := hPh)
      (hF := hF) (hF' := hF') (hSat := hSn)⟩

end Conc

end Formalism.L2.SG.NormCut
