import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.InBlock
import Formalism.LocalToGlobal.IndefiniteReal.CxPassA

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.L2.GlobalTheoryTheory.DivPassage

namespace In3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  (I : In3 K G Pl0 I0 Ty T m)

def rep (h1 : I.ρf 1 = 1) (hm : ∀ g h, I.ρf (g * h) = I.ρf g * I.ρf h) : Representation K G (Fin I.Sg.D → K) where
  toFun g := Matrix.toLin' (I.ρf g)
  map_one' := by rw [h1, Matrix.toLin'_one]; rfl
  map_mul' g h := by rw [hm, Matrix.toLin'_mul]; rfl

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `simp [rep, Matrix.toLin'_apply]`.
-/
theorem rep_apply (h1 : I.ρf 1 = 1) (hm : ∀ g h, I.ρf (g * h) = I.ρf g * I.ρf h) (g : G) (x : Fin I.Sg.D → K) :
    I.rep h1 hm g x = I.ρf g *ᵥ x := by
  first
  | rfl
  | simp [rep, Matrix.toLin'_apply]

/- English proof (translation)
Rewrite using `[← Matrix.toLin'_apply']`. Simplify using `only [epM, Formalism.IndefR.TransferLatticeStatement.epP, map_smul, map_sum, hχ, map_inv]`. Use `congr 1`. Use `Finset.sum_congr (by congr; exact Subsingleton.elim _ _) (fun h _ => ?_)` and prove the remaining obligations. Establish `e` using `hχ h⁻¹`.

Rewrite `e` using `[map_inv χ, map_inv ψ]`. Rewrite using `[e]`. Both sides reduce to the same expression.
-/
theorem epM_eq (h1 : I.ρf 1 = 1) (hm : ∀ g h, I.ρf (g * h) = I.ρf g * I.ρf h) (P : Subgroup G) (ψ : P →* Kˣ)
    (χ : P →* (𝓞 K)ˣ) (hχ : ∀ h, (((χ h : (𝓞 K)ˣ) : 𝓞 K) : K) = ((ψ h : Kˣ) : K)) :
    (I.epM P ψ).mulVecLin = Formalism.IndefR.TransferLatticeStatement.epP P χ (I.rep h1 hm) := by
  rw [← Matrix.toLin'_apply']
  simp only [epM, Formalism.IndefR.TransferLatticeStatement.epP, map_smul, map_sum, hχ, map_inv]
  congr 1
  refine Finset.sum_congr (by congr; exact Subsingleton.elim _ _) (fun h _ => ?_)
  have e := hχ h⁻¹
  rw [map_inv χ, map_inv ψ] at e
  rw [e]
  rfl

/- English proof (translation)
Rewrite using `[← Matrix.toLin'_apply']`. Simplify using `only [eMat, Formalism.IndefR.TransferLatticeStatement.eS, map_smul, map_sum]`. Both sides reduce to the same expression.
-/
theorem eMat_eq (h1 : I.ρf 1 = 1) (hm : ∀ g h, I.ρf (g * h) = I.ρf g * I.ρf h) {W : Type} [AddCommGroup W]
    [Module K W] (τ : Representation K G W) :
    (I.eMat τ).mulVecLin = Formalism.IndefR.TransferLatticeStatement.eS τ (I.rep h1 hm) := by
  rw [← Matrix.toLin'_apply']
  simp only [eMat, Formalism.IndefR.TransferLatticeStatement.eS, map_smul, map_sum]
  rfl

/- English proof (translation)
Take `⟨h1, hm, -⟩` from `hρ s H`. Take `⟨χ0, hχ0⟩` from `Formalism.IndefR.LatticeTransfer.liftChar K I.P0 I.ψ0`. Take `⟨χ1, hχ1⟩` from `Formalism.IndefR.LatticeTransfer.liftChar K I.P1 I.ψ1`. Establish `hFrm : (I.LA τ nbar).FramesG` using `hFr s H`. Establish `hL : (I.LA τ nbar).LatG` using `hLat s H`.

Establish `key0 : (I.LA τ nbar).ep0.mulVecLin = Formalism.IndefR.TransferLatticeStatement.epP I.P0 χ0 (I.rep h1 hm)` using `I.epM_eq h1 hm I.P0 I.ψ0 χ0 hχ0`. Establish `key1 : (I.LA τ nbar).ep1.mulVecLin = Formalism.IndefR.TransferLatticeStatement.epP I.P1 χ1 (I.rep h1 hm)` using `I.epM_eq h1 hm I.P1 I.ψ1 χ1 hχ1`. Establish `hs : ∀ t : S, (I.eMat (τ t)).mulVecLin = Formalism.IndefR.TransferLatticeStatement.eS (τ t) (I.rep h1 hm)` using `fun t => I.eMat_eq h1 hm (τ t)`. Establish `hnS : ∀ t : S, Formalism.IndefR.IndefiniteEpsilonOperator.nOf (τ t) ⟨I.P1, I.ψ1⟩ = Formalism.IndefR.TransferLatticeStatement.nS (τ t) I.P1 χ1` using `fun t => nOf_eq_nS (τ t) I.P1 I.ψ1 χ1 hχ1`. Establish `hM1' : Formalism.IndefR.TransferLatticeStatement.M1 τ I.P0 χ0` using `fun t => by rw [← nOf_eq_nS (τ t) I.P0 I.ψ0 χ0 hχ0]; exact hM1 t`.

Establish `hgood : Formalism.IndefR.TransferLatticeStatement.eGood τ (I.rep h1 hm) = LinearMap.id`. Unfold `Formalism.IndefR.TransferLatticeStatement.eGood`. Rewrite using `[← Finset.sum_congr rfl fun t _ => hs t]`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`.

Establish `hx` using `congrArg (fun M : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K => M *ᵥ x) (hGood s H hτ hX)`. Simplify using `only [Matrix.sum_mulVec, Matrix.one_mulVec] at hx`. Rewrite using `[LinearMap.sum_apply, LinearMap.id_apply]`. Simplify `hx` using `only [Matrix.mulVecLin_apply]`. Establish `hst : ∀ g : G, ∀ a ∈ I.Sg.RR, I.rep h1 hm g a ∈ I.Sg.RR` using `fun g a ha => by`.

Rewrite using `[rep_apply]`. Conclude with `hGL s H g a ha`. Establish `hUn : Formalism.IndefR.TransferLatticeStatement.IsUnitaryRep (Pi.basisFun K (Fin I.Sg.D)) I.Sg.XE (I.rep h1 hm)` using `fun v g x y => by`. Rewrite using `[rep_apply, rep_apply]`. Conclude with `hU s H v g x y`.

Take `⟨hRk, hD0, hD1, hMx⟩` from `Formalism.IndefR.LatticeTransfer.levelAmb_transfer (I.LA τ nbar) τ I.P0 χ0 I.P1 χ1 (I.rep h1 hm) hτ hM1' key0 key1 hs hnS rfl hgood hFrm hL hst hUn`. Establish `hE : ∀ b, (I.LA τ nbar).EmbAt (I.Jm b) (I.epM (I.lvP b) (I.lvψ b)) (Nat.card (I.lvP b)) (I.Sb b).XE` using `fun b => ⟨(hJ s H b).2, hR s H b, hMet s H b⟩`. Establish `hSd : ∀ b, (I.LA τ nbar).SandAt (I.Jm b) (I.epM (I.lvP b) (I.lvψ b)) (Nat.card (I.lvP b)) (I.Sb b).RR`. Introduce `b`. Take `⟨hin, hout⟩` from `hS s H b`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `y ⟨x, hx, rfl⟩`. Use `⟨hin x hx, ?_⟩` and prove the remaining obligations. Use `show (I.Jm b *ᵥ x) ∈ LinearMap.range (I.epM (I.lvP b) (I.lvψ b)).mulVecLin`. Rewrite using `[← hR s H b]`.

Conclude with `⟨x, rfl⟩`. Introduce and unpack `y ⟨hyR, hyE⟩`. Take `⟨x, hx, hxy⟩` from `hout y hyR hyE`. Conclude with `⟨x, hx, hxy⟩`. Establish `hRows : (I.LA τ nbar).RowsG` using `⟨Formalism.L2.GlobalTheoryTheory.DivPassage2.rows_gen (I.LA τ nbar) hL (I.Jm false) _ H.pos0 (hJ s H false).2 (hR s H false), Formalism.L2.GlobalTheoryTheory.DivPassage2.rows_gen (I.LA τ nbar) hL (I.Jm true) _ H.pos1 (hJ s H true).2 (hR s H true)⟩`.

Establish `hSz : (I.LA τ nbar).Sizes N.la`. Use `⟨Nat.card_pos, ?_, Nat.card_pos, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(Subgroup.card_le_card_group I.P0).trans (Nat.card_eq_fintype_card).le`. Conclude with `(Subgroup.card_le_card_group I.P1).trans (Nat.card_eq_fintype_card).le`. Rewrite using `[hla]`.

Conclude with `le_refl _`. Conclude with `passage_from_levels K I.A3.fam3.base3 _ _ N (I.Sb false) (I.Sb true) (I.LA τ nbar) hFrm hL (hE false) (hE true) (hSd false) (hSd true) hSz hRk hD0 hD1 (hMx hRows.2) ⟨hn, hM2⟩ hRows`.
-/
theorem passage_of_steps [IsTotallyComplex K] {s : ℕ} (H : I.Hyp s) {S : Type} [Fintype S] {Ws : S → Type}
    [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)] [∀ s, FiniteDimensional K (Ws s)]
    (τ : ∀ s, Representation K G (Ws s)) (nbar : ℝ) (N : IndefNum I.A3.fam3.base3)
    (hρ : I.PRho) (hJ : I.PJ) (hR : I.PRange) (hMet : I.PMet) (hFr : I.PFrames) (hU : I.PUni)
    (hLat : I.PLat) (hGL : I.PGLat) (hS : I.PSand) (hGood : I.PGood τ)
    (hτ : Formalism.IndefR.TransferLatticeStatement.IsGood τ) (hX : CharsX τ I.A.fam.X) (hM1 : Formalism.IndefR.IndefiniteEpsilonOperator.M1 τ ⟨I.P0, I.ψ0⟩) (hn : 0 < nbar)
    (hM2 : NearConstantMultiplicities τ ⟨I.P1, I.ψ1⟩ nbar N.de) (hla : N.la = Formalism.IndefR.IndefiniteEpsilonOperator.la G) :
    Passage N (I.Sb false) (I.Sb true) := by
  obtain ⟨h1, hm, -⟩ := hρ s H
  obtain ⟨χ0, hχ0⟩ := Formalism.IndefR.LatticeTransfer.liftChar K I.P0 I.ψ0
  obtain ⟨χ1, hχ1⟩ := Formalism.IndefR.LatticeTransfer.liftChar K I.P1 I.ψ1
  have hFrm : (I.LA τ nbar).FramesG := hFr s H
  have hL : (I.LA τ nbar).LatG := hLat s H
  have key0 : (I.LA τ nbar).ep0.mulVecLin = Formalism.IndefR.TransferLatticeStatement.epP I.P0 χ0 (I.rep h1 hm) :=
    I.epM_eq h1 hm I.P0 I.ψ0 χ0 hχ0
  have key1 : (I.LA τ nbar).ep1.mulVecLin = Formalism.IndefR.TransferLatticeStatement.epP I.P1 χ1 (I.rep h1 hm) :=
    I.epM_eq h1 hm I.P1 I.ψ1 χ1 hχ1
  have hs : ∀ t : S, (I.eMat (τ t)).mulVecLin = Formalism.IndefR.TransferLatticeStatement.eS (τ t) (I.rep h1 hm) := fun t =>
    I.eMat_eq h1 hm (τ t)
  have hnS : ∀ t : S, Formalism.IndefR.IndefiniteEpsilonOperator.nOf (τ t) ⟨I.P1, I.ψ1⟩ = Formalism.IndefR.TransferLatticeStatement.nS (τ t) I.P1 χ1 := fun t =>
    nOf_eq_nS (τ t) I.P1 I.ψ1 χ1 hχ1
  have hM1' : Formalism.IndefR.TransferLatticeStatement.M1 τ I.P0 χ0 := fun t => by rw [← nOf_eq_nS (τ t) I.P0 I.ψ0 χ0 hχ0]; exact hM1 t
  have hgood : Formalism.IndefR.TransferLatticeStatement.eGood τ (I.rep h1 hm) = LinearMap.id := by
    unfold Formalism.IndefR.TransferLatticeStatement.eGood
    rw [← Finset.sum_congr rfl fun t _ => hs t]
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun M : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K => M *ᵥ x) (hGood s H hτ hX)
    simp only [Matrix.sum_mulVec, Matrix.one_mulVec] at hx
    rw [LinearMap.sum_apply, LinearMap.id_apply]
    simpa only [Matrix.mulVecLin_apply] using hx
  have hst : ∀ g : G, ∀ a ∈ I.Sg.RR, I.rep h1 hm g a ∈ I.Sg.RR := fun g a ha => by
    rw [rep_apply]; exact hGL s H g a ha
  have hUn : Formalism.IndefR.TransferLatticeStatement.IsUnitaryRep (Pi.basisFun K (Fin I.Sg.D)) I.Sg.XE (I.rep h1 hm) := fun v g x y => by
    rw [rep_apply, rep_apply]; exact hU s H v g x y
  obtain ⟨hRk, hD0, hD1, hMx⟩ := Formalism.IndefR.LatticeTransfer.levelAmb_transfer (I.LA τ nbar) τ I.P0 χ0 I.P1 χ1 (I.rep h1 hm) hτ hM1'
    key0 key1 hs hnS rfl hgood hFrm hL hst hUn
  have hE : ∀ b, (I.LA τ nbar).EmbAt (I.Jm b) (I.epM (I.lvP b) (I.lvψ b)) (Nat.card (I.lvP b)) (I.Sb b).XE := fun b =>
    ⟨(hJ s H b).2, hR s H b, hMet s H b⟩
  have hSd : ∀ b, (I.LA τ nbar).SandAt (I.Jm b) (I.epM (I.lvP b) (I.lvψ b)) (Nat.card (I.lvP b)) (I.Sb b).RR := by
    intro b
    obtain ⟨hin, hout⟩ := hS s H b
    refine ⟨?_, ?_⟩
    · rintro y ⟨x, hx, rfl⟩
      refine ⟨hin x hx, ?_⟩
      show (I.Jm b *ᵥ x) ∈ LinearMap.range (I.epM (I.lvP b) (I.lvψ b)).mulVecLin
      rw [← hR s H b]; exact ⟨x, rfl⟩
    · rintro y ⟨hyR, hyE⟩
      obtain ⟨x, hx, hxy⟩ := hout y hyR hyE
      exact ⟨x, hx, hxy⟩
  have hRows : (I.LA τ nbar).RowsG :=
    ⟨Formalism.L2.GlobalTheoryTheory.DivPassage2.rows_gen (I.LA τ nbar) hL (I.Jm false) _ H.pos0 (hJ s H false).2 (hR s H false),
      Formalism.L2.GlobalTheoryTheory.DivPassage2.rows_gen (I.LA τ nbar) hL (I.Jm true) _ H.pos1 (hJ s H true).2 (hR s H true)⟩
  have hSz : (I.LA τ nbar).Sizes N.la := by
    refine ⟨Nat.card_pos, ?_, Nat.card_pos, ?_, ?_⟩
    · exact (Subgroup.card_le_card_group I.P0).trans (Nat.card_eq_fintype_card).le
    · exact (Subgroup.card_le_card_group I.P1).trans (Nat.card_eq_fintype_card).le
    · rw [hla]; exact le_refl _
  exact passage_from_levels K I.A3.fam3.base3 _ _ N (I.Sb false) (I.Sb true) (I.LA τ nbar) hFrm hL (hE false) (hE true)
    (hSd false) (hSd true) hSz hRk hD0 hD1 (hMx hRows.2) ⟨hn, hM2⟩ hRows

end In3

def Steps3 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 I0 Ty T : Type) (m : ℕ)
    (I : In3 K G Pl0 I0 Ty T m), I.PRho ∧ I.PJ ∧ I.PRange ∧ I.PMet ∧ I.PFrames ∧ I.PUni ∧ I.PLat ∧ I.PGLat ∧ I.PSand ∧
      ∀ (S : Type) [Fintype S] (Ws : S → Type) [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
        [∀ s, FiniteDimensional K (Ws s)] (τ : ∀ s, Representation K G (Ws s)), I.PGood τ

/- English proof (translation)
Introduce `K _ _ _ _ G _ _ Pl0 I0 Ty T m A3 s P0 ψ0 P1 ψ1 Dc Sp Zsc X C CH gE S _ Ws _ _ _ τ nbar hok hsep hst hin h4 hp0 hp1 hh2 hrat hh2g hratg hgu hge hn0 hn1 hτ hX hM1 hn hM2 hla`. Set `I : In3 K G Pl0 I0 Ty T m` to `⟨A3, P0, ψ0, P1, ψ1, Dc, Sp, Zsc, X, gE⟩`. Take `⟨hρ, hJ, hR, hMet, hFr, hU, hLat, hGL, hS, hG⟩` from `h K G Pl0 I0 Ty T m I`. Conclude with `I.passage_of_steps ⟨hok, hsep, hst, hin, h4, hp0, hp1, hh2, hrat, hh2g, hratg, hgu, hge, hn0, hn1⟩ τ nbar _ hρ hJ hR hMet hFr hU hLat hGL hS (hG S Ws τ) hτ hX hM1 hn hM2 hla`.
-/
theorem cutPassage3S_of_steps (h : Steps3) : CutPassage3S := by
  intro K _ _ _ _ G _ _ Pl0 I0 Ty T m A3 s P0 ψ0 P1 ψ1 Dc Sp Zsc X C CH gE S _ Ws _ _ _ τ nbar
    hok hsep hst hin h4 hp0 hp1 hh2 hrat hh2g hratg hgu hge hn0 hn1 hτ hX hM1 hn hM2 hla
  let I : In3 K G Pl0 I0 Ty T m := ⟨A3, P0, ψ0, P1, ψ1, Dc, Sp, Zsc, X, gE⟩
  obtain ⟨hρ, hJ, hR, hMet, hFr, hU, hLat, hGL, hS, hG⟩ := h K G Pl0 I0 Ty T m I
  exact I.passage_of_steps ⟨hok, hsep, hst, hin, h4, hp0, hp1, hh2, hrat, hh2g, hratg, hgu, hge, hn0, hn1⟩
    τ nbar _ hρ hJ hR hMet hFr hU hLat hGL hS (hG S Ws τ) hτ hX hM1 hn hM2 hla

/- English proof (translation)
Introduce `K _ _ _ _ G _ _ Pl0 I0 Ty T m A3 s P0 ψ0 P1 ψ1 Dc Sp Zsc X C CH gE S _ Ws _ _ _ τ nbar a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 _ _ a16 a17 a18 a19 a20 a21 a22 a23`. Conclude with `h K G Pl0 I0 Ty T m A3 s P0 ψ0 P1 ψ1 Dc Sp Zsc X C CH gE S Ws τ nbar a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a16 a17 a18 a19 a20 a21 a22 a23`.
-/
theorem cutPassage3_of_S (h : CutPassage3S) : CutPassage3 := by
  intro K _ _ _ _ G _ _ Pl0 I0 Ty T m A3 s P0 ψ0 P1 ψ1 Dc Sp Zsc X C CH gE S _ Ws _ _ _ τ nbar a1 a2 a3 a4 a5 a6 a7
    a8 a9 a10 a11 a12 a13 _ _ a16 a17 a18 a19 a20 a21 a22 a23
  exact h K G Pl0 I0 Ty T m A3 s P0 ψ0 P1 ψ1 Dc Sp Zsc X C CH gE S Ws τ nbar a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
    a13 a16 a17 a18 a19 a20 a21 a22 a23

end Formalism.IndefR.CxPass
