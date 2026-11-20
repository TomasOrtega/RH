import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueChainComplexFormsStabiliserLaw
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Rk.Top

/- English proof (translation)
Establish `key : ∀ P, Formalism.L2.Col.polOf G' (shiftOf lam) o (fnOf G (shiftOf lam) 1 P) = P`. Introduce `P`. Establish `h` using `Formalism.L2.Col.polOf_fnOf G' (shiftOf lam) o P`. Rewrite `h` using `[ho]`. Conclude with `h`.

Establish `hval : ∀ v, ∃ P ∈ Formalism.L2.DIV.VV ℂ lam, j v = fnOf G (shiftOf lam) 1 P`. Introduce `v`. Establish `hv : j v ∈ ValC G lam` using `hr ▸ LinearMap.mem_range_self j v`. Take `⟨P, hP, hPv⟩` from `Submodule.mem_map.mp hv`. Rewrite `hP` using `[GlobalTheory.Pdv.FormsStd.cSpan_eq_VV]`.

Conclude with `⟨P, hP, hPv.symm⟩`. Set `φ : V →ₗ[ℂ] Formalism.L2.DIV.Pol ℂ ι n` to `{ toFun := fun v => Formalism.L2.Col.polOf G' (shiftOf lam) o (j v) map_add' := fun x y => by rw [map_add]; exact (Formalism.L2.Col.polOf G' (shiftOf lam) o).map_add (j x) (j y) map_smul' := fun c x => by rw [map_smul]; exact (Formalism.L2.Col.polOf G' (shiftOf lam) o).map_smul c …`. Establish `hφ : ∀ v, φ v = Formalism.L2.Col.polOf G' (shiftOf lam) o (j v)` using `fun _ => rfl`. Establish `hmem : ∀ v, φ v ∈ Formalism.L2.DIV.VV ℂ lam`. Introduce `v`.

Take `⟨P, hP, e⟩` from `hval v`. Rewrite using `[hφ, e, key]`. Conclude with `hP`. Set `φ' : V →ₗ[ℂ] Formalism.L2.DIV.VV ℂ lam` to `φ.codRestrict _ hmem`. Establish `hφ' : ∀ v, (φ' v : Formalism.L2.DIV.Pol ℂ ι n) = φ v` using `fun _ => rfl`.

Establish `inj : Function.Injective φ'`. Introduce `v v' h`. Establish `h' : φ v = φ v'` using `by rw [← hφ', ← hφ', h]`. Take `⟨P, -, e⟩` from `hval v`. Take `⟨P', -, e'⟩` from `hval v'`.

Rewrite `h'` using `[hφ, hφ, e, e', key, key]`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[e, e', h']`. Establish `surj : Function.Surjective φ'`. Introduce `x`.

Establish `hx : fnOf G (shiftOf lam) 1 x.1 ∈ LinearMap.range j`. Rewrite using `[hr]`. Use `Submodule.mem_map.mpr ⟨x.1, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.Pdv.FormsStd.cSpan_eq_VV]`. Conclude with `x.2`.

Take `⟨v, hv⟩` from `hx`. Use `⟨v, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[hφ', hφ, hv, key]`. Set `e` to `LinearEquiv.ofBijective φ' ⟨inj, surj⟩`. Use `haveI : FiniteDimensional ℂ (Formalism.L2.DIV.VV ℂ lam) := Module.Finite.of_basis (Formalism.L2.DIV.bVV ℂ lam)`.

Set `ψ : Module.Dual ℂ (Formalism.L2.DIV.VV ℂ lam)` to `ℓ ∘ₗ e.symm.toLinearMap`. Establish `hB : (pairBK (K` using `ℂ) lam).flip.Nondegenerate := by`. Use `pairingBNondegenerate_holds ℂ ι n lam` as an intermediate fact. Conclude with `LinearMap.flip_nondegenerate.mpr this`. Set `w` to `(LinearMap.BilinForm.toDual _ hB).symm ψ`.

Establish `hw : ∀ x, ψ x = pairBK lam x w`. Introduce `x`. Establish `h1 : LinearMap.BilinForm.toDual _ hB w = ψ` using `LinearEquiv.apply_symm_apply _ _`. Rewrite using `[← h1, LinearMap.BilinForm.toDual_def, LinearMap.flip_apply]`. Use `⟨w.1, w.2, fun v => ?_⟩` and prove the remaining obligations.

Establish `h2 : ℓ v = ψ (e v)` using `by simp [ψ]`. Rewrite using `[h2, hw, pairBK_apply]`. Both sides reduce to the same expression.
-/
theorem exists_pairB_of_range_eq {ι : Type} [Fintype ι] {n : ℕ} (G G' : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n)
    (o : Frames G') (ho : (fun τ => (o.1 τ)⁻¹) = 1) {V : Type} [AddCommGroup V] [Module ℂ V] (j : V →ₗ[ℂ] (Frames G → ℂ))
    (hinj : Function.Injective j) (hr : LinearMap.range j = ValC G lam) (ℓ : V →ₗ[ℂ] ℂ) :
    ∃ w ∈ Formalism.L2.DIV.VV ℂ lam, ∀ v, ℓ v = Formalism.L2.DIV.pairB lam (Formalism.L2.Col.polOf G' (shiftOf lam) o (j v)) w := by
  have key : ∀ P, Formalism.L2.Col.polOf G' (shiftOf lam) o (fnOf G (shiftOf lam) 1 P) = P := by
    intro P
    have h := Formalism.L2.Col.polOf_fnOf G' (shiftOf lam) o P
    rw [ho] at h
    exact h
  have hval : ∀ v, ∃ P ∈ Formalism.L2.DIV.VV ℂ lam, j v = fnOf G (shiftOf lam) 1 P := by
    intro v
    have hv : j v ∈ ValC G lam := hr ▸ LinearMap.mem_range_self j v
    obtain ⟨P, hP, hPv⟩ := Submodule.mem_map.mp hv
    rw [GlobalTheory.Pdv.FormsStd.cSpan_eq_VV] at hP
    exact ⟨P, hP, hPv.symm⟩
  let φ : V →ₗ[ℂ] Formalism.L2.DIV.Pol ℂ ι n :=
    { toFun := fun v => Formalism.L2.Col.polOf G' (shiftOf lam) o (j v)
      map_add' := fun x y => by rw [map_add]; exact (Formalism.L2.Col.polOf G' (shiftOf lam) o).map_add (j x) (j y)
      map_smul' := fun c x => by rw [map_smul]; exact (Formalism.L2.Col.polOf G' (shiftOf lam) o).map_smul c (j x) }
  have hφ : ∀ v, φ v = Formalism.L2.Col.polOf G' (shiftOf lam) o (j v) := fun _ => rfl
  have hmem : ∀ v, φ v ∈ Formalism.L2.DIV.VV ℂ lam := by
    intro v
    obtain ⟨P, hP, e⟩ := hval v
    rw [hφ, e, key]
    exact hP
  let φ' : V →ₗ[ℂ] Formalism.L2.DIV.VV ℂ lam := φ.codRestrict _ hmem
  have hφ' : ∀ v, (φ' v : Formalism.L2.DIV.Pol ℂ ι n) = φ v := fun _ => rfl
  have inj : Function.Injective φ' := by
    intro v v' h
    have h' : φ v = φ v' := by rw [← hφ', ← hφ', h]
    obtain ⟨P, -, e⟩ := hval v
    obtain ⟨P', -, e'⟩ := hval v'
    rw [hφ, hφ, e, e', key, key] at h'
    apply hinj
    rw [e, e', h']
  have surj : Function.Surjective φ' := by
    intro x
    have hx : fnOf G (shiftOf lam) 1 x.1 ∈ LinearMap.range j := by
      rw [hr]
      refine Submodule.mem_map.mpr ⟨x.1, ?_, rfl⟩
      rw [GlobalTheory.Pdv.FormsStd.cSpan_eq_VV]
      exact x.2
    obtain ⟨v, hv⟩ := hx
    refine ⟨v, Subtype.ext ?_⟩
    rw [hφ', hφ, hv, key]
  let e := LinearEquiv.ofBijective φ' ⟨inj, surj⟩
  haveI : FiniteDimensional ℂ (Formalism.L2.DIV.VV ℂ lam) := Module.Finite.of_basis (Formalism.L2.DIV.bVV ℂ lam)
  let ψ : Module.Dual ℂ (Formalism.L2.DIV.VV ℂ lam) := ℓ ∘ₗ e.symm.toLinearMap
  have hB : (pairBK (K := ℂ) lam).flip.Nondegenerate := by
    have := pairingBNondegenerate_holds ℂ ι n lam
    exact LinearMap.flip_nondegenerate.mpr this
  let w := (LinearMap.BilinForm.toDual _ hB).symm ψ
  have hw : ∀ x, ψ x = pairBK lam x w := by
    intro x
    have h1 : LinearMap.BilinForm.toDual _ hB w = ψ := LinearEquiv.apply_symm_apply _ _
    rw [← h1, LinearMap.BilinForm.toDual_def, LinearMap.flip_apply]
  refine ⟨w.1, w.2, fun v => ?_⟩
  have h2 : ℓ v = ψ (e v) := by simp [ψ]
  rw [h2, hw, pairBK_apply]
  rfl

end GlobalTheory.Core.Rk.Top

namespace GlobalTheory.Core.Rk.Top

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Unfold `Formalism.L2.Forms.sgT PerIn.sgT Formalism.L2.Forms.shW GlobalTheory.Mem.Col2.shW`. Use `congr 1`. Use function extensionality and compare the values at `i`. Establish `h1 : (((I.rec7 l Z).fm u).sg τ).w i = ((I.perIn u a).sg τ).w i` using `rfl`.

Establish `h2 : (I.rec7 l Z).R = B.R` using `rfl`. Rewrite using `[h1, h2]`. Establish `hd : 2 ∣ B.R.t + 1`. Take `⟨k, hk⟩` from `B.R.t_odd`. Conclude with `⟨k + 1, by omega⟩`.

Rewrite using `[Nat.mul_div_assoc _ hd]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sgT_eq_perIn_sgT {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) : Formalism.L2.Forms.sgT (D := I.rec7 l Z) u = (I.perIn u a).sgT := by
  funext τ
  unfold Formalism.L2.Forms.sgT PerIn.sgT Formalism.L2.Forms.shW GlobalTheory.Mem.Col2.shW
  congr 1
  funext i
  have h1 : (((I.rec7 l Z).fm u).sg τ).w i = ((I.perIn u a).sg τ).w i := rfl
  have h2 : (I.rec7 l Z).R = B.R := rfl
  rw [h1, h2]
  have hd : 2 ∣ B.R.t + 1 := by
    obtain ⟨k, hk⟩ := B.R.t_odd
    exact ⟨k + 1, by omega⟩
  rw [Nat.mul_div_assoc _ hd]
  push_cast
  ring

/- English proof (translation)
Introduce `B X I l Z u a S MX j hJ ℓ`. Establish `hr` using `hJ.range`. Rewrite `hr` using `[sgT_eq_perIn_sgT I l Z u a]`. Establish `e : (fun τ => ((GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)).1 τ)⁻¹) = 1` using `funext fun τ => inv_one`. Conclude with `exists_pairB_of_range_eq _ _ _ _ e j hJ.inj hr ℓ`.
-/
theorem exists_pairB_of_isJ : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) {S : (I.rec7 l Z).what₂.Tau → SPar} (MX : DSModel (I.rec7 l Z).sp.X' S) (j : SmT MX →ₗ[ℂ] (Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ)), GlobalTheory.Core.Rk.Top.IsJ u MX j → ∀ ℓ : SmT MX →ₗ[ℂ] ℂ, ∃ w ∈ Formalism.L2.DIV.VV ℂ (I.perIn u a).sgT, ∀ v, ℓ v = Formalism.L2.DIV.pairB (I.perIn u a).sgT (Formalism.L2.Col.polOf (GlobalTheory.Mem.Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (Formalism.L2.Forms.shiftOf (I.perIn u a).sgT) (GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) (j v)) w := by
  intro B X I l Z u a S MX j hJ ℓ
  have hr := hJ.range
  rw [sgT_eq_perIn_sgT I l Z u a] at hr
  have e : (fun τ => ((GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)).1 τ)⁻¹) = 1 := funext fun τ => inv_one
  exact exists_pairB_of_range_eq _ _ _ _ e j hJ.inj hr ℓ

end GlobalTheory.Core.Rk.Top

end
