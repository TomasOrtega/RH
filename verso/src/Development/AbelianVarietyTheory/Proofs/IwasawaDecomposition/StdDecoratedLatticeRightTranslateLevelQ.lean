import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemParLevOfQ
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfMulJ0Decoration
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeCongruenceInLevelCharacterOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.ActQ

/- English proof (translation)
Substitute `h` using the available equality. Use extensionality with `i j`. Simplify using `[castGL]`.
-/
theorem castGL_castGL_symm {R : Type} [CommRing R] {a b : ℕ} (h : a = b) (m : GL (Fin b) R) :
    castGL h (castGL h.symm m) = m := by
  subst h
  ext i j
  simp [castGL]

/- English proof (translation)
Substitute `h` using the available equality. Establish `e : castGL (rfl : a = a) m = m`. Use extensionality with `i j`. Simplify using `[castGL]`. Rewrite using `[e]` and apply the resulting hypothesis.
-/
theorem castGL_mem_St_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {a b : ℕ} (h : a = b) (m : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F)) (hm : m ∈ Formalism.L2.DIV.St 1) :
    castGL h m ∈ Formalism.L2.DIV.St 1 := by
  subst h
  have e : castGL (rfl : a = a) m = m := by
    ext i j
    simp [castGL]
  rwa [e]

/- English proof (translation)
Introduce `X px I U L _ _ hL i t A k hF κ x`. Take `⟨-, hASt, hAU, hkU, hkSt, -⟩` from `hF`. Use `set w : Bridge.Gf (Vc X.toD7 i) → GL (Fin X.B.R.nV) (EA X) := fun g => castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) (g : GL (Fin (Vc X.toD7 i).rank) _)) with hw`. Establish `hwmul : w (x * κ) = w x * w κ`. Simplify using `only [hw, Subgroup.coe_mul, map_mul]`.

Establish `hconj : ∀ g : GL (Fin (Vc X.toD7 i).rank) (EA X), g ∈ Formalism.L2.DIV.UA X.toD7.sp.cm (Vc X.toD7 i).gram → A⁻¹ * castGL (rkEq X i).symm g * A ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV`. Introduce `g hg`. Use `(hAU _).2 ?_` and prove the remaining obligations. Establish `e : A * (A⁻¹ * castGL (rkEq X i).symm g * A) * A⁻¹ = castGL (rkEq X i).symm g` using `by group`. Rewrite using `[e, castGL_castGL_symm]`.

Conclude with `hg`. Establish `hxU : Formalism.UG.bc (swapAE X.toD7) ((x : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _) ∈ Formalism.L2.DIV.UA X.toD7.sp.cm (Vc X.toD7 i).gram`. Take `⟨g, hg⟩` from `x.2`. Rewrite using `[← hg]`. Conclude with `GlobalTheory.LevFinCong.finE_mem_UA _ g`.

Establish `hκP` using `mem_parLev_of_Q X I U L i t κ`. Establish `hκU` using `Formalism.L2.DIV.parLev_UA hκP`. Establish `hκS : Formalism.UG.bc (swapAE X.toD7) ((κ : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _) ∈ Formalism.L2.DIV.St (1 : GL (Fin (Vc X.toD7 i).rank) (EA X))`. Establish `h0` using `Formalism.L2.DIV.parLev_St hκP`. Establish `hb : L.βV i = 1` using `hL.beta.1 i`.

Conclude with `hb ▸ h0`. Use `set y := A⁻¹ * w x * A * k with hy`. Use `set z := (A * k)⁻¹ * w κ * (A * k) with hz`. Establish `hyU : y ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV` using `mul_mem (hconj _ hxU) hkU`. Establish `hzU : z ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV`.

Establish `e : z = k⁻¹ * (A⁻¹ * w κ * A) * k` using `by rw [hz]; group`. Rewrite using `[e]`. Conclude with `mul_mem (mul_mem (inv_mem hkU) (hconj _ hκU)) hkU`. Establish `hzS : z ∈ Formalism.L2.DIV.St (1 : GL (Fin X.B.R.nV) (EA X))`. Establish `hwS : w κ ∈ Formalism.L2.DIV.St (1 : GL (Fin X.B.R.nV) (EA X))` using `castGL_mem_St_one _ _ hκS`.

Establish `hAk` using `mul_mem hASt hkSt`. Conclude with `mul_mem (mul_mem (inv_mem hAk) hwS) hAk`. Establish `hzJ : z ∈ Formalism.L2.Col.J0 X.toD7.sp.cm X.B.R.nV (∅ : Finset (Pl X.toD7.host.E))` using `⟨⟨hzU, hzS⟩, Subgroup.mem_iInf.2 fun P => Subgroup.mem_iInf.2 fun hP => absurd hP (Finset.notMem_empty _)⟩`. Establish `hyz : A⁻¹ * w (x * κ) * A * k = y * z`. Rewrite using `[hwmul, hy, hz]`.

Use `group`. Establish `hyzU : y * z ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV` using `mul_mem hyU hzU`. Establish `hred : Formalism.L2.Col.redG X.toD7.sp.cm X.B.R.nV ∅ (sgL X I U t) ⟨z, hzJ⟩ = redZ X I U L i t A k κ`. Use function extensionality and compare the values at `v`. Use `show _ = Formalism.L2.DIV.redFn (1 : GL (Fin X.B.R.nV) (EA X)) v.1 z`.

Unfold `Formalism.L2.DIV.redFn`. Rewrite using `[Formalism.L2.DIV.extendOne_of_mem _ hzS]`. Both sides reduce to the same expression. Establish `hraw` using `GlobalTheory.Mem.Col2.TopCh.decoRaw_mul_levelIwahori_reduction X.toD7.sp.cm ∅ (sgL X I U t) y z hzJ`. Rewrite `hraw` using `[hred]`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show (Formalism.L2.Col.decoOf ∅ (sgL X I U t) (A⁻¹ * w (x * κ) * A * k)).1 = (Formalism.L2.Col.decoOf ∅ (sgL X I U t) y).1.act 1 (redZ X I U L i t A k κ)⁻¹`. Rewrite using `[hyz]`. Unfold `Formalism.L2.Col.decoOf`. Rewrite using `[dif_pos (Formalism.L2.Col.decorated_lattice_exists X.toD7.sp.cm X.B.R.nV ∅ (sgL X I U t) _ hyzU), dif_pos (Formalism.L2.Col.decorated_lattice_exists X.toD7.sp.cm X.B.R.nV ∅ (sgL X I U t) _ hyU)]`.

Conclude with `hraw`.
-/
theorem ptS_mul_Q : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → ValsIn I → LevOf X I U L → ∀ (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k →
    ∀ (κ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) (x : Bridge.Gf (Vc X.toD7 i)),
      LiftBrg.ActQ.ptS X I U i t A k (x * κ) =
        ((1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV), (LiftBrg.ActQ.redZ X I U L i t A k κ)⁻¹) • LiftBrg.ActQ.ptS X I U i t A k x := by
  intro X px I U L _ _ hL i t A k hF κ x
  obtain ⟨-, hASt, hAU, hkU, hkSt, -⟩ := hF
  set w : Bridge.Gf (Vc X.toD7 i) → GL (Fin X.B.R.nV) (EA X) := fun g =>
    castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) (g : GL (Fin (Vc X.toD7 i).rank) _)) with hw
  have hwmul : w (x * κ) = w x * w κ := by
    simp only [hw, Subgroup.coe_mul, map_mul]

  have hconj : ∀ g : GL (Fin (Vc X.toD7 i).rank) (EA X), g ∈ Formalism.L2.DIV.UA X.toD7.sp.cm (Vc X.toD7 i).gram →
      A⁻¹ * castGL (rkEq X i).symm g * A ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV := by
    intro g hg
    refine (hAU _).2 ?_
    have e : A * (A⁻¹ * castGL (rkEq X i).symm g * A) * A⁻¹ = castGL (rkEq X i).symm g := by group
    rw [e, castGL_castGL_symm]
    exact hg
  have hxU : Formalism.UG.bc (swapAE X.toD7) ((x : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _) ∈
      Formalism.L2.DIV.UA X.toD7.sp.cm (Vc X.toD7 i).gram := by
    obtain ⟨g, hg⟩ := x.2
    rw [← hg]
    exact GlobalTheory.LevFinCong.finE_mem_UA _ g
  have hκP := mem_parLev_of_Q X I U L i t κ
  have hκU := Formalism.L2.DIV.parLev_UA hκP
  have hκS : Formalism.UG.bc (swapAE X.toD7) ((κ : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _) ∈
      Formalism.L2.DIV.St (1 : GL (Fin (Vc X.toD7 i).rank) (EA X)) := by
    have h0 := Formalism.L2.DIV.parLev_St hκP
    have hb : L.βV i = 1 := hL.beta.1 i
    exact hb ▸ h0
  set y := A⁻¹ * w x * A * k with hy
  set z := (A * k)⁻¹ * w κ * (A * k) with hz
  have hyU : y ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV := mul_mem (hconj _ hxU) hkU
  have hzU : z ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV := by
    have e : z = k⁻¹ * (A⁻¹ * w κ * A) * k := by rw [hz]; group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hkU) (hconj _ hκU)) hkU
  have hzS : z ∈ Formalism.L2.DIV.St (1 : GL (Fin X.B.R.nV) (EA X)) := by
    have hwS : w κ ∈ Formalism.L2.DIV.St (1 : GL (Fin X.B.R.nV) (EA X)) := castGL_mem_St_one _ _ hκS
    have hAk := mul_mem hASt hkSt
    exact mul_mem (mul_mem (inv_mem hAk) hwS) hAk
  have hzJ : z ∈ Formalism.L2.Col.J0 X.toD7.sp.cm X.B.R.nV (∅ : Finset (Pl X.toD7.host.E)) :=
    ⟨⟨hzU, hzS⟩, Subgroup.mem_iInf.2 fun P => Subgroup.mem_iInf.2 fun hP => absurd hP (Finset.notMem_empty _)⟩
  have hyz : A⁻¹ * w (x * κ) * A * k = y * z := by
    rw [hwmul, hy, hz]; group
  have hyzU : y * z ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV := mul_mem hyU hzU
  have hred : Formalism.L2.Col.redG X.toD7.sp.cm X.B.R.nV ∅ (sgL X I U t) ⟨z, hzJ⟩ = redZ X I U L i t A k κ := by
    funext v
    show _ = Formalism.L2.DIV.redFn (1 : GL (Fin X.B.R.nV) (EA X)) v.1 z
    unfold Formalism.L2.DIV.redFn
    rw [Formalism.L2.DIV.extendOne_of_mem _ hzS]
    rfl
  have hraw := GlobalTheory.Mem.Col2.TopCh.decoRaw_mul_levelIwahori_reduction X.toD7.sp.cm ∅ (sgL X I U t) y z hzJ
  rw [hred] at hraw
  apply Subtype.ext
  show (Formalism.L2.Col.decoOf ∅ (sgL X I U t) (A⁻¹ * w (x * κ) * A * k)).1 =
    (Formalism.L2.Col.decoOf ∅ (sgL X I U t) y).1.act 1 (redZ X I U L i t A k κ)⁻¹
  rw [hyz]
  unfold Formalism.L2.Col.decoOf
  rw [dif_pos (Formalism.L2.Col.decorated_lattice_exists X.toD7.sp.cm X.B.R.nV ∅ (sgL X I U t) _ hyzU),
    dif_pos (Formalism.L2.Col.decorated_lattice_exists X.toD7.sp.cm X.B.R.nV ∅ (sgL X I U t) _ hyU)]
  exact hraw

end GlobalTheory.Mem.R3.LiftBrg.ActQ
