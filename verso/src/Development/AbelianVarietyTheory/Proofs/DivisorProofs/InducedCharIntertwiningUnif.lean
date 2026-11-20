import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankSB
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatRankDeficientReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedScalarIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreMemInducedSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenStabilizerSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableFullRankFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreZeroMemCoinvariantsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanCharacterTranslatesCoinvariant
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThK.MidJac GlobalTheory.CuspBlock

noncomputable section

namespace GlobalTheory.DetIndScal

open Matrix GlobalTheory.RankFibre

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use `ext`. Simplify using `[e2, blocks, stdSum, finSigmaFinEquiv_apply]`.
-/
theorem blockIndex_zero (a a' : ℕ) (i : Fin a) : e2 a a' ⟨0, i⟩ = blocks a a' ⟨false, i⟩ := by
  ext
  simp [e2, blocks, stdSum, finSigmaFinEquiv_apply]

/- English proof (translation)
Use `ext`. Simplify using `[e2, blocks, stdSum, finSigmaFinEquiv_apply]`.
-/
theorem blockIndex_one (a a' : ℕ) (j : Fin a') : e2 a a' ⟨1, j⟩ = blocks a a' ⟨true, j⟩ := by
  ext
  simp [e2, blocks, stdSum, finSigmaFinEquiv_apply]

/- English proof (translation)
Rewrite using `[mem_parab_iff, mem_parab_two]`. Prove the components needed by the constructor for the conclusion. Introduce `h j i`. Use `h 1 0 j i (by decide)` as an intermediate fact. Rewrite `this` using `[blockIndex_zero, blockIndex_one]`. Then use the resulting hypothesis.

Introduce `h c d i j hdc`. Establish `hc : c = 1` using `Fin.ext (by have := c.isLt; have : d.val < c.val := hdc; omega)`. Establish `hd : d = 0` using `Fin.ext (by have : d.val < c.val := hdc; have := c.isLt; omega)`. Substitute `hc hd` using the available equality. Conclude with `(congrArg₂ (fun x y => (p : Matrix (Fin (a + a')) (Fin (a + a')) k) x y) (blockIndex_one a a' i) (blockIndex_zero a a' j)).trans (h i j)`.
-/
theorem mem_parabolic_two_blocks_iff (a a' : ℕ) (p : GL (Fin (a + a')) k) :
    p ∈ parab k (e2 a a') ↔ p ∈ parab k (blocks a a') := by
  rw [mem_parab_iff, mem_parab_two]
  constructor
  · intro h j i
    have := h 1 0 j i (by decide)
    rwa [blockIndex_zero, blockIndex_one] at this
  · intro h c d i j hdc
    have hc : c = 1 := Fin.ext (by have := c.isLt; have : d.val < c.val := hdc; omega)
    have hd : d = 0 := Fin.ext (by have : d.val < c.val := hdc; have := c.isLt; omega)
    subst hc hd
    exact (congrArg₂ (fun x y => (p : Matrix (Fin (a + a')) (Fin (a + a')) k) x y) (blockIndex_one a a' i)
      (blockIndex_zero a a' j)).trans (h i j)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [leviProj_apply]`. Conclude with `congrArg₂ (fun x y => (p : Matrix (Fin (a + a')) (Fin (a + a')) k) x y) (blockIndex_zero a a' i) (blockIndex_zero a a' j)`.
-/
theorem leviProj_two_blocks_zero (a a' : ℕ) (p : GL (Fin (a + a')) k) (h1 : p ∈ parab k (e2 a a'))
    (h2 : p ∈ parab k (blocks a a')) :
    (leviProj k (e2 a a') ⟨p, h1⟩ 0 : GL (Fin a) k) = leviProj k (blocks a a') ⟨p, h2⟩ false := by
  ext i j
  simp only [leviProj_apply]
  exact congrArg₂ (fun x y => (p : Matrix (Fin (a + a')) (Fin (a + a')) k) x y) (blockIndex_zero a a' i) (blockIndex_zero a a' j)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [leviProj_apply]`. Conclude with `congrArg₂ (fun x y => (p : Matrix (Fin (a + a')) (Fin (a + a')) k) x y) (blockIndex_one a a' i) (blockIndex_one a a' j)`.
-/
theorem leviProj_two_blocks_one (a a' : ℕ) (p : GL (Fin (a + a')) k) (h1 : p ∈ parab k (e2 a a'))
    (h2 : p ∈ parab k (blocks a a')) :
    (leviProj k (e2 a a') ⟨p, h1⟩ 1 : GL (Fin a') k) = leviProj k (blocks a a') ⟨p, h2⟩ true := by
  ext i j
  simp only [leviProj_apply]
  exact congrArg₂ (fun x y => (p : Matrix (Fin (a + a')) (Fin (a + a')) k) x y) (blockIndex_one a a' i) (blockIndex_one a a' j)

/- English proof (translation)
Simplify using `[modExp, Finset.sum_filter, Fin.sum_univ_two]`.
-/
theorem modular_exponent_two_blocks_zero (a a' : ℕ) : modExp (fun c : Fin 2 => Fin (![a, a'] c)) 0 = a' := by
  simp [modExp, Finset.sum_filter, Fin.sum_univ_two]

/- English proof (translation)
Simplify using `[modExp, Finset.sum_filter, Fin.sum_univ_two]`.
-/
theorem modular_exponent_two_blocks_one (a a' : ℕ) : modExp (fun c : Fin 2 => Fin (![a, a'] c)) 1 = -(a : ℤ) := by
  simp [modExp, Finset.sum_filter, Fin.sum_univ_two]

/- English proof (translation)
Establish `h0` using `leviProj_two_blocks_zero a a' p h1 h2`. Establish `h1'` using `leviProj_two_blocks_one a a' p h1 h2`. Use `set l := leviProj k (e2 a a') ⟨p, h1⟩`. Use `set lb := leviProj k (blocks a a') ⟨p, h2⟩`. Establish `hlb : lb = leviTwo k (Fin a) (Fin a') (lb false, lb true)` using `((leviTwo k (Fin a) (Fin a')).apply_symm_apply _).symm`.

Establish `hd : deltaHalf k (fun c : Fin 2 => Fin (![a, a'] c)) l = absPow k ((a' : ℂ) / 2) (GeneralLinearGroup.det (lb false)) * absPow k (-(a : ℂ) / 2) (GeneralLinearGroup.det (lb true))`. Rewrite using `[deltaHalf_apply, Fin.prod_univ_two, modular_exponent_two_blocks_zero, modular_exponent_two_blocks_one]`. Rewrite using `[← h0, ← h1']`. Use `push_cast`. Rewrite using `[neg_div]`.

Both sides reduce to the same expression. Establish `ht : GlobalTheory.ThK.DetProd.twoDet a a' (ν * β) β l = (ν * β) (GeneralLinearGroup.det (lb false)) * β (GeneralLinearGroup.det (lb true))`. Rewrite using `[← h0, ← h1']`. Both sides reduce to the same expression. Establish `hp : parChar ν β a a' ⟨p, h2⟩ = deltaHalf k (Two (Fin a) (Fin a')) lb * (ν * β) (GeneralLinearGroup.det (lb false)) * β (GeneralLinearGroup.det (lb true))` using `rfl`.

Establish `hδ` using `deltaHalf_two (k := k) (lb false, lb true)`. Rewrite `hδ` using `[← hlb]`. Simplify using `only [Fintype.card_fin] at hδ`. Rewrite using `[hd, ht, hp, hδ]`. Simplify using `only [Units.val_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem char_eq (ν β : kˣ →* ℂˣ) (a a' : ℕ) (p : GL (Fin (a + a')) k) (h1 : p ∈ parab k (e2 a a'))
    (h2 : p ∈ parab k (blocks a a')) :
    (deltaHalf k (fun c : Fin 2 => Fin (![a, a'] c)) (leviProj k (e2 a a') ⟨p, h1⟩) : ℂ) *
      (GlobalTheory.ThK.DetProd.twoDet a a' (ν * β) β (leviProj k (e2 a a') ⟨p, h1⟩) : ℂ) =
      (parChar ν β a a' ⟨p, h2⟩ : ℂ) := by
  have h0 := leviProj_two_blocks_zero a a' p h1 h2
  have h1' := leviProj_two_blocks_one a a' p h1 h2
  set l := leviProj k (e2 a a') ⟨p, h1⟩
  set lb := leviProj k (blocks a a') ⟨p, h2⟩
  have hlb : lb = leviTwo k (Fin a) (Fin a') (lb false, lb true) :=
    ((leviTwo k (Fin a) (Fin a')).apply_symm_apply _).symm
  have hd : deltaHalf k (fun c : Fin 2 => Fin (![a, a'] c)) l =
      absPow k ((a' : ℂ) / 2) (GeneralLinearGroup.det (lb false)) *
        absPow k (-(a : ℂ) / 2) (GeneralLinearGroup.det (lb true)) := by
    rw [deltaHalf_apply, Fin.prod_univ_two, modular_exponent_two_blocks_zero, modular_exponent_two_blocks_one]
    rw [← h0, ← h1']
    push_cast
    rw [neg_div]
    rfl
  have ht : GlobalTheory.ThK.DetProd.twoDet a a' (ν * β) β l =
      (ν * β) (GeneralLinearGroup.det (lb false)) * β (GeneralLinearGroup.det (lb true)) := by
    rw [← h0, ← h1']
    rfl
  have hp : parChar ν β a a' ⟨p, h2⟩ = deltaHalf k (Two (Fin a) (Fin a')) lb *
      (ν * β) (GeneralLinearGroup.det (lb false)) * β (GeneralLinearGroup.det (lb true)) := rfl
  have hδ := deltaHalf_two (k := k) (lb false, lb true)
  rw [← hlb] at hδ
  simp only [Fintype.card_fin] at hδ
  rw [hd, ht, hp, hδ]
  simp only [Units.val_mul]
  ring

/- English proof (translation)
Use `⟨?_, fun p g => ?_⟩` and prove the remaining obligations. Establish `hs` using `F.2`. Establish `he : {g : GL (Fin (a + a')) k | rightReg ℂ (GL (Fin (a + a')) k) ℂ g F.1.1 = F.1.1} = {g | ind (parab k (e2 a a')) ((twist (ofChar (GlobalTheory.ThK.DetProd.twoDet a a' (ν * β) β)) (deltaHalf k (fun c : Fin 2 => Fin (![a, a'] c)))).comp (leviProj k (e2 a a'))) g F.1 = F.1}`. Use extensionality with `g`. Conclude with `⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩`.

Use `show IsOpen {g : GL (Fin (a + a')) k | rightReg ℂ (GL (Fin (a + a')) k) ℂ g F.1.1 = F.1.1}`. Rewrite using `[he]`. Conclude with `hs`. Establish `h1` using `(mem_parabolic_two_blocks_iff a a' p.1).2 p.2`. Use `F.1.2 ⟨p.1, h1⟩ g` as an intermediate fact.

Simplify using `only [MonoidHom.coe_comp, Function.comp_apply, twist_apply, ofChar_apply, smul_eq_mul] at this`. Rewrite using `[ofChar_apply, ← char_eq ν β a a' p.1 h1 p.2]`. Use `this.trans ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem val_mem_indScal (ν β : kˣ →* ℂˣ) (a a' : ℕ)
    (F : IndSp (k := k) (e2 a a') (ofChar (GlobalTheory.ThK.DetProd.twoDet a a' (ν * β) β))) :
    F.1.1 ∈ indScal ν β a a' := by
  refine ⟨?_, fun p g => ?_⟩
  · have hs := F.2
    have he : {g : GL (Fin (a + a')) k | rightReg ℂ (GL (Fin (a + a')) k) ℂ g F.1.1 = F.1.1} =
        {g | ind (parab k (e2 a a')) ((twist (ofChar (GlobalTheory.ThK.DetProd.twoDet a a' (ν * β) β))
          (deltaHalf k (fun c : Fin 2 => Fin (![a, a'] c)))).comp (leviProj k (e2 a a'))) g F.1 = F.1} := by
      ext g
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    show IsOpen {g : GL (Fin (a + a')) k | rightReg ℂ (GL (Fin (a + a')) k) ℂ g F.1.1 = F.1.1}
    rw [he]
    exact hs
  · have h1 := (mem_parabolic_two_blocks_iff a a' p.1).2 p.2
    have := F.1.2 ⟨p.1, h1⟩ g
    simp only [MonoidHom.coe_comp, Function.comp_apply, twist_apply, ofChar_apply, smul_eq_mul] at this
    rw [ofChar_apply, ← char_eq ν β a a' p.1 h1 p.2]
    refine this.trans ?_
    ring

/- English proof (translation)
Establish `hlaw : f ∈ indSpace (parab k (e2 a a')) ((twist (ofChar (GlobalTheory.ThK.DetProd.twoDet a a' (ν * β) β)) (deltaHalf k (fun c : Fin 2 => Fin (![a, a'] c)))).comp (leviProj k (e2 a a')))`. Introduce `p g`. Establish `h2` using `(mem_parabolic_two_blocks_iff a a' p.1).1 p.2`. Use `hf.2 ⟨p.1, h2⟩ g` as an intermediate fact. Rewrite `this` using `[ofChar_apply, ← char_eq ν β a a' p.1 p.2 h2]`.

Simplify using `only [MonoidHom.coe_comp, Function.comp_apply, twist_apply, ofChar_apply, smul_eq_mul]`. Use `this.trans ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `⟨⟨⟨f, hlaw⟩, ?_⟩, rfl⟩` and prove the remaining obligations. Establish `hs : IsOpen {g : GL (Fin (a + a')) k | rightReg ℂ (GL (Fin (a + a')) k) ℂ g f = f}` using `hf.1`.

Establish `he : {g : GL (Fin (a + a')) k | rightReg ℂ (GL (Fin (a + a')) k) ℂ g f = f} = {g | ind (parab k (e2 a a')) ((twist (ofChar (GlobalTheory.ThK.DetProd.twoDet a a' (ν * β) β)) (deltaHalf k (fun c : Fin 2 => Fin (![a, a'] c)))).comp (leviProj k (e2 a a'))) g ⟨f, hlaw⟩ = ⟨f, hlaw⟩}`. Use extensionality with `g`. Conclude with `⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩`. Use `show IsOpen {g | ind (parab k (e2 a a')) ((twist (ofChar (GlobalTheory.ThK.DetProd.twoDet a a' (ν * β) β)) (deltaHalf k (fun c : Fin 2 => Fin (![a, a'] c)))).comp (leviProj k (e2 a a'))) g ⟨f, hlaw⟩ = ⟨f, hlaw⟩}`. Rewrite using `[← he]`.

Conclude with `hs`.
-/
theorem exists_of_mem_indScal (ν β : kˣ →* ℂˣ) (a a' : ℕ) {f : GL (Fin (a + a')) k → ℂ}
    (hf : f ∈ indScal ν β a a') :
    ∃ F : IndSp (k := k) (e2 a a') (ofChar (GlobalTheory.ThK.DetProd.twoDet a a' (ν * β) β)), F.1.1 = f := by
  have hlaw : f ∈ indSpace (parab k (e2 a a')) ((twist (ofChar (GlobalTheory.ThK.DetProd.twoDet a a' (ν * β) β))
      (deltaHalf k (fun c : Fin 2 => Fin (![a, a'] c)))).comp (leviProj k (e2 a a'))) := by
    intro p g
    have h2 := (mem_parabolic_two_blocks_iff a a' p.1).1 p.2
    have := hf.2 ⟨p.1, h2⟩ g
    rw [ofChar_apply, ← char_eq ν β a a' p.1 p.2 h2] at this
    simp only [MonoidHom.coe_comp, Function.comp_apply, twist_apply, ofChar_apply, smul_eq_mul]
    refine this.trans ?_
    ring
  refine ⟨⟨⟨f, hlaw⟩, ?_⟩, rfl⟩
  have hs : IsOpen {g : GL (Fin (a + a')) k | rightReg ℂ (GL (Fin (a + a')) k) ℂ g f = f} := hf.1
  have he : {g : GL (Fin (a + a')) k | rightReg ℂ (GL (Fin (a + a')) k) ℂ g f = f} =
      {g | ind (parab k (e2 a a')) ((twist (ofChar (GlobalTheory.ThK.DetProd.twoDet a a' (ν * β) β))
        (deltaHalf k (fun c : Fin 2 => Fin (![a, a'] c)))).comp (leviProj k (e2 a a'))) g ⟨f, hlaw⟩ = ⟨f, hlaw⟩} := by
    ext g
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  show IsOpen {g | ind (parab k (e2 a a')) ((twist (ofChar (GlobalTheory.ThK.DetProd.twoDet a a' (ν * β) β))
        (deltaHalf k (fun c : Fin 2 => Fin (![a, a'] c)))).comp (leviProj k (e2 a a'))) g ⟨f, hlaw⟩ = ⟨f, hlaw⟩}
  rw [← he]
  exact hs

open GlobalTheory.SplitFlip in

/- English proof (translation)
Introduce `HB k _ _ _ _ a a' ν β hνs hνu hβs hβu ϖ hϖ hνϖ W _ _ R L hL1 hL2`. Use `borelize k`. Establish `hLc : ∀ z ∈ coinv ν β a (a + a'), L z = 0`. Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨g, Ψ, hΨ, rfl⟩` from `hx`. Rewrite using `[map_sub, hL1 g Ψ hΨ, sub_self]`. Consider the case `zero => exact map_zero L`. Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]`.

Consider the case `smul c x _ hx => rw [map_smul, hx, smul_zero]`. Establish `hR0 : ∀ h, R h 0 = 0`. Introduce `h`. Establish `h0 : omA ν β 1 h (0 : Matrix (Fin a) (Fin (a + a')) k → ℂ) = 0`. Use function extensionality and compare the values at `Y`.

Simplify using `[omA]`. Use `hL2 h 0 (GlobalTheory.WeilM.SB _).zero_mem` as an intermediate fact. Rewrite `this` using `[h0, map_zero]`. Conclude with `this.symm`. Establish `hS0 : ∀ (h : GL (Fin (a + a')) k) (Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ), Φ ∈ fullRankSB k a (a + a') → omA ν β 1 h Φ ∈ fullRankSB k a (a + a')`.

Introduce `h Φ hΦ`. Use `⟨omA_mem_SB ν β 1 h hΦ.1, fun Y hY => ?_⟩` and prove the remaining obligations. Establish `hr : (((1 : GL (Fin a) k)⁻¹).val * Y * (invT h).val).rank ≠ a`. Rewrite using `[inv_one, Units.val_one, Matrix.one_mul, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units (invT h))]` and apply the resulting hypothesis. Simplify using `only [omA, hΦ.2 _ hr, mul_zero]`.

Establish `hint : ∀ Φ ∈ fullRankSB k a (a + a'), ∀ x : GL (Fin (a + a')) k, MeasureTheory.Integrable (fun g : GL (Fin a) k => omA ν β 1 x Φ (g.val * X0 k finSumFinEquiv) * (ν (gdet g) : ℂ) * apow (gdet g) (((a + a' : ℕ) : ℂ) / 2)) (haarVol (GlobalTheory.SplitWeil.KO k (Fin a)))` using `fun Φ hΦ x => GlobalTheory.T.integrable_full_rank_fibre k a a' ν hνs _ (hS0 x Φ hΦ)`. Establish `hadd : ∀ Φ ∈ fullRankSB k a (a + a'), ∀ Ψ ∈ fullRankSB k a (a + a'), fibre ν β a a' (Φ + Ψ) = fibre ν β a a' Φ + fibre ν β a a' Ψ`. Introduce `Φ hΦ Ψ hΨ`. Use function extensionality and compare the values at `x`. Rewrite using `[Pi.add_apply]`.

Unfold `fibre`. Rewrite using `[← MeasureTheory.integral_add (hint Φ hΦ x) (hint Ψ hΨ x)]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Simplify using `only [omA, Pi.add_apply]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsmul : ∀ (c : ℂ) (Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ), fibre ν β a a' (c • Φ) = c • fibre ν β a a' Φ`. Introduce `c Φ`. Use function extensionality and compare the values at `x`. Rewrite using `[Pi.smul_apply, smul_eq_mul]`.

Unfold `fibre`. Rewrite using `[← MeasureTheory.integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Simplify using `only [omA, Pi.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hind : ∀ Ψ ∈ fullRankSB k a (a + a'), fibre ν β a a' Ψ ∈ indScal ν β a a'`. Introduce `Ψ hΨ`. Use `⟨?_, GlobalTheory.T.fibre_mem_induced_space k a a' ν β Ψ⟩` and prove the remaining obligations. Establish `hle : GlobalTheory.RankFibre.stabSub ((GlobalTheory.SplitFlip.repA ν β).comp (MonoidHom.inr (GL (Fin a) k) (GL (Fin (a + a')) k))) Ψ ≤ GlobalTheory.RankFibre.stabSub (rightReg ℂ (GL (Fin (a + a')) k) ℂ) (fibre ν β a a' Ψ)`.

Introduce `h hh`. Establish `hh' : omA ν β 1 h Ψ = Ψ` using `hh`. Use `show rightReg ℂ (GL (Fin (a + a')) k) ℂ h (fibre ν β a a' Ψ) = fibre ν β a a' Ψ`. Use function extensionality and compare the values at `x`. Use `show fibre ν β a a' Ψ (x * h) = fibre ν β a a' Ψ x`.

Rewrite using `[← fibre_omA, hh']`. Conclude with `Subgroup.isOpen_mono hle (GlobalTheory.T.isOpen_stabilizer_schwartzBruhat k a (a + a') ν β hβs Ψ hΨ.1)`. Set `Z : fullRankSB k a (a + a') →ₗ[ℂ] (GL (Fin (a + a')) k → ℂ)` to `{ toFun := fun Φ => fibre ν β a a' Φ.1 map_add' := fun Φ Ψ => hadd Φ.1 Φ.2 Ψ.1 Ψ.2 map_smul' := fun c Φ => hsmul c Φ.1 }`. Set `Lr : fullRankSB k a (a + a') →ₗ[ℂ] W` to `L ∘ₗ (fullRankSB k a (a + a')).subtype`. Establish `hker : LinearMap.ker Z ≤ LinearMap.ker Lr`.

Introduce `Φ hΦ`. Rewrite `hΦ`, the goal using `[LinearMap.mem_ker]`. Conclude with `hLc _ (GlobalTheory.T.fibre_zero_mem_coinvariants k a a' ν β hνs hβs Φ.1 Φ.2 hΦ)`. Set `Lbar : LinearMap.range Z →ₗ[ℂ] W` to `((LinearMap.ker Z).liftQ Lr hker) ∘ₗ (Z.quotKerEquivRange.symm : LinearMap.range Z →ₗ[ℂ] _)`. Establish `hLbar : ∀ Φ : fullRankSB k a (a + a'), Lbar ⟨Z Φ, LinearMap.mem_range_self Z Φ⟩ = L Φ.1`.

Introduce `Φ`. Establish `e : (⟨Z Φ, LinearMap.mem_range_self Z Φ⟩ : LinearMap.range Z) = Z.quotKerEquivRange (Submodule.Quotient.mk Φ)` using `rfl`. Simplify using `only [Lbar, LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[e, LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]`. Both sides reduce to the same expression.

Establish `hMle : LinearMap.range Z ≤ indScal ν β a a'`. Introduce and unpack `_ ⟨Φ, rfl⟩`. Conclude with `hind Φ.1 Φ.2`. Establish `hMst : ∀ f ∈ LinearMap.range Z, ∀ h : GL (Fin (a + a')) k, (fun x => f (x * h)) ∈ LinearMap.range Z`. Introduce and unpack `_ ⟨Φ, rfl⟩ h`.

Conclude with `⟨⟨omA ν β 1 h Φ.1, hS0 h Φ.1 Φ.2⟩, funext fun x => fibre_omA ν β a a' h Φ.1 x⟩`. Establish `hstep1 : ∀ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) k), ∃ Φ : fullRankSB k a (a + a'), L Ψ = L Φ.1`. Introduce `Ψ hΨ`. Take `⟨Φ₀, hΦ₀, hr, hd⟩` from `GlobalTheory.T.schwartzBruhat_rank_deficient_reduction k a (a + a') (Nat.le_add_right a a') ν β hνs hνu ϖ hϖ hνϖ Ψ hΨ`. Use `⟨⟨Φ₀, hΦ₀, hr⟩, ?_⟩` and prove the remaining obligations.

Use `hLc _ hd` as an intermediate fact. Rewrite `this` using `[map_sub, sub_eq_zero]`. Then use the resulting hypothesis. Break down `GlobalTheory.T.induced_scalar_irreducible HB k a a' ν β hνs hνu hβs hβu (LinearMap.range Z) hMle hMst with h0 | hT` into its components or cases. Use `⟨0, fun h y => by simp [hR0], fun Ψ hΨ => ⟨0, ?_⟩⟩` and prove the remaining obligations. Take `⟨Φ, hΦ⟩` from `hstep1 Ψ hΨ`.

Rewrite using `[hΦ, LinearMap.zero_apply]`. Establish `hm : Z Φ ∈ LinearMap.range Z` using `LinearMap.mem_range_self Z Φ`. Rewrite `hm` using `[h0, Submodule.mem_bot]`. Conclude with `hker (LinearMap.mem_ker.2 hm)`. Set `V : IndSp (k` to `k) (e2 a a') (ofChar (GlobalTheory.ThK.DetProd.twoDet a a' (ν * β) β)) →ₗ[ℂ] (GL (Fin (a + a')) k → ℂ) := Submodule.subtype _ ∘ₗ Submodule.subtype _`.

Set `j` to `LinearMap.codRestrict (LinearMap.range Z) V (fun F => hT (val_mem_indScal ν β a a' F))`. Use `⟨Lbar ∘ₗ j, fun h y => ?_, fun Ψ hΨ => ?_⟩` and prove the remaining obligations. Take `⟨Φ, hΦ⟩` from `(j y).2`. Establish `e1 : j y = ⟨Z Φ, LinearMap.mem_range_self Z Φ⟩` using `Subtype.ext hΦ.symm`. Establish `e2' : j (detInd a a' (ν * β) β h y) = ⟨Z ⟨omA ν β 1 h Φ.1, hS0 h Φ.1 Φ.2⟩, LinearMap.mem_range_self _ _⟩`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Use `show y.1.1 (x * h) = fibre ν β a a' (omA ν β 1 h Φ.1) x`. Rewrite using `[fibre_omA]`. Conclude with `(congrFun hΦ (x * h)).symm`.

Use `show Lbar (j _) = R h (Lbar (j y))`. Rewrite using `[e1, e2', hLbar, hLbar]`. Conclude with `hL2 h Φ.1 Φ.2.1`. Take `⟨Φ, hΦ⟩` from `hstep1 Ψ hΨ`. Take `⟨y, hy⟩` from `exists_of_mem_indScal ν β a a' (hind Φ.1 Φ.2)`.

Use `⟨y, ?_⟩` and prove the remaining obligations. Establish `e1 : j y = ⟨Z Φ, LinearMap.mem_range_self Z Φ⟩` using `Subtype.ext hy`. Use `show L Ψ = Lbar (j y)`. Rewrite using `[e1, hLbar, hΦ]`.
-/
theorem factor_through_detInd : GlobalTheory.Published.BernsteinUnitaryProductIrreducible →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a a' : ℕ)
    (ν β : kˣ →* ℂˣ), IsSmoothChar ν → IsUnitaryChar ν → IsSmoothChar β → IsUnitaryChar β →
    ∀ ϖ : kˣ, GlobalTheory.SplitFlip.IsUnif ϖ → ν ϖ ≠ 1 →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (R : GL (Fin (a + a')) k → W → W)
      (L : (Matrix (Fin a) (Fin (a + a')) k → ℂ) →ₗ[ℂ] W),
      (∀ (g : GL (Fin a) k), ∀ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) k), L (GlobalTheory.SplitFlip.omA ν β g 1 Ψ) = L Ψ) →
      (∀ (h : GL (Fin (a + a')) k), ∀ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) k),
        L (GlobalTheory.SplitFlip.omA ν β 1 h Ψ) = R h (L Ψ)) →
      ∃ T : IndSp (e2 a a') (ofChar (GlobalTheory.ThK.DetProd.twoDet a a' (ν * β) β)) →ₗ[ℂ] W,
        (∀ h y, T (detInd a a' (ν * β) β h y) = R h (T y)) ∧
        ∀ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) k), ∃ y, L Ψ = T y := by
  intro HB k _ _ _ _ a a' ν β hνs hνu hβs hβu ϖ hϖ hνϖ W _ _ R L hL1 hL2
  borelize k

  have hLc : ∀ z ∈ coinv ν β a (a + a'), L z = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, Ψ, hΨ, rfl⟩ := hx
      rw [map_sub, hL1 g Ψ hΨ, sub_self]
    | zero => exact map_zero L
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, hx, smul_zero]
  have hR0 : ∀ h, R h 0 = 0 := by
    intro h
    have h0 : omA ν β 1 h (0 : Matrix (Fin a) (Fin (a + a')) k → ℂ) = 0 := by
      funext Y
      simp [omA]
    have := hL2 h 0 (GlobalTheory.WeilM.SB _).zero_mem
    rw [h0, map_zero] at this
    exact this.symm

  have hS0 : ∀ (h : GL (Fin (a + a')) k) (Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ),
      Φ ∈ fullRankSB k a (a + a') → omA ν β 1 h Φ ∈ fullRankSB k a (a + a') := by
    intro h Φ hΦ
    refine ⟨omA_mem_SB ν β 1 h hΦ.1, fun Y hY => ?_⟩
    have hr : (((1 : GL (Fin a) k)⁻¹).val * Y * (invT h).val).rank ≠ a := by
      rwa [inv_one, Units.val_one, Matrix.one_mul,
        Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units (invT h))]
    simp only [omA, hΦ.2 _ hr, mul_zero]
  have hint : ∀ Φ ∈ fullRankSB k a (a + a'), ∀ x : GL (Fin (a + a')) k,
      MeasureTheory.Integrable (fun g : GL (Fin a) k => omA ν β 1 x Φ (g.val * X0 k finSumFinEquiv) * (ν (gdet g) : ℂ) *
        apow (gdet g) (((a + a' : ℕ) : ℂ) / 2)) (haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) :=
    fun Φ hΦ x => GlobalTheory.T.integrable_full_rank_fibre k a a' ν hνs _ (hS0 x Φ hΦ)
  have hadd : ∀ Φ ∈ fullRankSB k a (a + a'), ∀ Ψ ∈ fullRankSB k a (a + a'),
      fibre ν β a a' (Φ + Ψ) = fibre ν β a a' Φ + fibre ν β a a' Ψ := by
    intro Φ hΦ Ψ hΨ
    funext x
    rw [Pi.add_apply]
    unfold fibre
    rw [← MeasureTheory.integral_add (hint Φ hΦ x) (hint Ψ hΨ x)]
    congr 1
    funext g
    simp only [omA, Pi.add_apply]
    ring
  have hsmul : ∀ (c : ℂ) (Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ),
      fibre ν β a a' (c • Φ) = c • fibre ν β a a' Φ := by
    intro c Φ
    funext x
    rw [Pi.smul_apply, smul_eq_mul]
    unfold fibre
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext g
    simp only [omA, Pi.smul_apply, smul_eq_mul]
    ring

  have hind : ∀ Ψ ∈ fullRankSB k a (a + a'), fibre ν β a a' Ψ ∈ indScal ν β a a' := by
    intro Ψ hΨ
    refine ⟨?_, GlobalTheory.T.fibre_mem_induced_space k a a' ν β Ψ⟩
    have hle : GlobalTheory.RankFibre.stabSub ((GlobalTheory.SplitFlip.repA ν β).comp
        (MonoidHom.inr (GL (Fin a) k) (GL (Fin (a + a')) k))) Ψ ≤
        GlobalTheory.RankFibre.stabSub (rightReg ℂ (GL (Fin (a + a')) k) ℂ) (fibre ν β a a' Ψ) := by
      intro h hh
      have hh' : omA ν β 1 h Ψ = Ψ := hh
      show rightReg ℂ (GL (Fin (a + a')) k) ℂ h (fibre ν β a a' Ψ) = fibre ν β a a' Ψ
      funext x
      show fibre ν β a a' Ψ (x * h) = fibre ν β a a' Ψ x
      rw [← fibre_omA, hh']
    exact Subgroup.isOpen_mono hle (GlobalTheory.T.isOpen_stabilizer_schwartzBruhat k a (a + a') ν β hβs Ψ hΨ.1)

  let Z : fullRankSB k a (a + a') →ₗ[ℂ] (GL (Fin (a + a')) k → ℂ) :=
    { toFun := fun Φ => fibre ν β a a' Φ.1
      map_add' := fun Φ Ψ => hadd Φ.1 Φ.2 Ψ.1 Ψ.2
      map_smul' := fun c Φ => hsmul c Φ.1 }
  let Lr : fullRankSB k a (a + a') →ₗ[ℂ] W := L ∘ₗ (fullRankSB k a (a + a')).subtype
  have hker : LinearMap.ker Z ≤ LinearMap.ker Lr := by
    intro Φ hΦ
    rw [LinearMap.mem_ker] at hΦ ⊢
    exact hLc _ (GlobalTheory.T.fibre_zero_mem_coinvariants k a a' ν β hνs hβs Φ.1 Φ.2 hΦ)
  let Lbar : LinearMap.range Z →ₗ[ℂ] W :=
    ((LinearMap.ker Z).liftQ Lr hker) ∘ₗ (Z.quotKerEquivRange.symm : LinearMap.range Z →ₗ[ℂ] _)
  have hLbar : ∀ Φ : fullRankSB k a (a + a'), Lbar ⟨Z Φ, LinearMap.mem_range_self Z Φ⟩ = L Φ.1 := by
    intro Φ
    have e : (⟨Z Φ, LinearMap.mem_range_self Z Φ⟩ : LinearMap.range Z) =
        Z.quotKerEquivRange (Submodule.Quotient.mk Φ) := rfl
    simp only [Lbar, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [e, LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]
    rfl
  have hMle : LinearMap.range Z ≤ indScal ν β a a' := by
    rintro _ ⟨Φ, rfl⟩
    exact hind Φ.1 Φ.2
  have hMst : ∀ f ∈ LinearMap.range Z, ∀ h : GL (Fin (a + a')) k, (fun x => f (x * h)) ∈ LinearMap.range Z := by
    rintro _ ⟨Φ, rfl⟩ h
    exact ⟨⟨omA ν β 1 h Φ.1, hS0 h Φ.1 Φ.2⟩, funext fun x => fibre_omA ν β a a' h Φ.1 x⟩

  have hstep1 : ∀ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) k),
      ∃ Φ : fullRankSB k a (a + a'), L Ψ = L Φ.1 := by
    intro Ψ hΨ
    obtain ⟨Φ₀, hΦ₀, hr, hd⟩ :=
      GlobalTheory.T.schwartzBruhat_rank_deficient_reduction k a (a + a') (Nat.le_add_right a a') ν β hνs hνu ϖ hϖ hνϖ Ψ hΨ
    refine ⟨⟨Φ₀, hΦ₀, hr⟩, ?_⟩
    have := hLc _ hd
    rwa [map_sub, sub_eq_zero] at this
  rcases GlobalTheory.T.induced_scalar_irreducible HB k a a' ν β hνs hνu hβs hβu (LinearMap.range Z) hMle hMst with h0 | hT
  · refine ⟨0, fun h y => by simp [hR0], fun Ψ hΨ => ⟨0, ?_⟩⟩
    obtain ⟨Φ, hΦ⟩ := hstep1 Ψ hΨ
    rw [hΦ, LinearMap.zero_apply]
    have hm : Z Φ ∈ LinearMap.range Z := LinearMap.mem_range_self Z Φ
    rw [h0, Submodule.mem_bot] at hm
    exact hker (LinearMap.mem_ker.2 hm)
  · let V : IndSp (k := k) (e2 a a') (ofChar (GlobalTheory.ThK.DetProd.twoDet a a' (ν * β) β)) →ₗ[ℂ]
        (GL (Fin (a + a')) k → ℂ) := Submodule.subtype _ ∘ₗ Submodule.subtype _
    let j := LinearMap.codRestrict (LinearMap.range Z) V (fun F => hT (val_mem_indScal ν β a a' F))
    refine ⟨Lbar ∘ₗ j, fun h y => ?_, fun Ψ hΨ => ?_⟩
    · obtain ⟨Φ, hΦ⟩ := (j y).2
      have e1 : j y = ⟨Z Φ, LinearMap.mem_range_self Z Φ⟩ := Subtype.ext hΦ.symm
      have e2' : j (detInd a a' (ν * β) β h y) =
          ⟨Z ⟨omA ν β 1 h Φ.1, hS0 h Φ.1 Φ.2⟩, LinearMap.mem_range_self _ _⟩ := by
        apply Subtype.ext
        funext x
        show y.1.1 (x * h) = fibre ν β a a' (omA ν β 1 h Φ.1) x
        rw [fibre_omA]
        exact (congrFun hΦ (x * h)).symm
      show Lbar (j _) = R h (Lbar (j y))
      rw [e1, e2', hLbar, hLbar]
      exact hL2 h Φ.1 Φ.2.1
    · obtain ⟨Φ, hΦ⟩ := hstep1 Ψ hΨ
      obtain ⟨y, hy⟩ := exists_of_mem_indScal ν β a a' (hind Φ.1 Φ.2)
      refine ⟨y, ?_⟩
      have e1 : j y = ⟨Z Φ, LinearMap.mem_range_self Z Φ⟩ := Subtype.ext hy
      show L Ψ = Lbar (j y)
      rw [e1, hLbar, hΦ]

end GlobalTheory.DetIndScal
