import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ToTermAct

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.NormCut Formalism.L2.SG.PackageTie2 Matrix

namespace Formalism.L2.SG.Pf.Act

section Row

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D}

/- English proof (translation)
Apply `LinearEquiv.ext` to reduce the goal to its premises. Introduce `y`. Apply `inclCrd_inj` to reduce the goal to its premises. Rewrite using `[isoG_spec]`. Use `show X.B.I.fmat 1 *ᵥ incl X.B.I (X.crd y) = incl X.B.I (X.crd y)`.

Simplify using `[Formalism.MainNotions.S.AutInst.fmat]`.
-/
theorem isoG_one {u : D.what₂.Word} : isoG (1 : Gam X u) = 1 := by
  apply LinearEquiv.ext
  intro y
  apply inclCrd_inj
  rw [isoG_spec]
  show X.B.I.fmat 1 *ᵥ incl X.B.I (X.crd y) = incl X.B.I (X.crd y)
  simp [Formalism.MainNotions.S.AutInst.fmat]

/- English proof (translation)
Establish `e : colD (cs.h (cs.base q.1)) (iotaF X u 1 * cs.h (cs.base q.1)) = (((cs.h (cs.base q.1) : X.B.I.Gf) * X.xu u))⁻¹ * (((cs.h (cs.base q.1) : X.B.I.Gf) * X.xu u))`. Unfold `colD`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `Formalism.L2.SG.Pf.LatDictK.dict_K X _ _ {y | X.B.I.fmat (((cs.h (cs.base q.1) : X.B.I.Gf) * X.xu u))⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf} (fun _ => Iff.rfl) (fun _ => Iff.rfl)`.
-/
theorem one_mem_gamL {u : D.what₂.Word} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂)
    (q : {Λ // Λ ∈ what₂}) : colD (cs.h (cs.base q.1)) (iotaF X u 1 * cs.h (cs.base q.1)) ∈ X.B.I.Kset := by
  have e : colD (cs.h (cs.base q.1)) (iotaF X u 1 * cs.h (cs.base q.1)) =
      (((cs.h (cs.base q.1) : X.B.I.Gf) * X.xu u))⁻¹ * (((cs.h (cs.base q.1) : X.B.I.Gf) * X.xu u)) := by
    unfold colD; simp
  rw [e]
  exact Formalism.L2.SG.Pf.LatDictK.dict_K X _ _ {y | X.B.I.fmat (((cs.h (cs.base q.1) : X.B.I.Gf) * X.xu u))⁻¹ *ᵥ
    incl X.B.I (X.crd y) ∈ X.B.I.Lf} (fun _ => Iff.rfl) (fun _ => Iff.rfl)

/- English proof (translation)
Substitute `hx1 hβ1` using the available equality. Distinguish the cases in `hβ : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ Formalism.L2.SG.Saturated.AutF Λ' (lf D F0')`. Proceed by induction on `c using Quot.ind with`. Consider the case `mk p`. Rewrite using `[SatGramActR.cmap_pos _ _ _ _ hβ]`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (p.1.1 * (1 : X.B.I.GA)⁻¹, p.1.2 * (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V)⁻¹) = p.1`. Simplify using the standard rewrite rules. Conclude with `SatGramActR.cmap_neg _ _ _ _ hβ c`.
-/
theorem cmap_id {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {x : X.B.I.GA} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hN : SatGramActR.AutFConjN) (hx : RatLink X x β) (hx1 : x = 1) (hβ1 : β = 1)
    {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V} (c : GQ X u u' F0 F0' Λ Λ') :
    SatGramActR.cmap x β hN hx c = c := by
  subst hx1 hβ1
  by_cases hβ : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ Formalism.L2.SG.Saturated.AutF Λ' (lf D F0')
  · induction c using Quot.ind with
    | mk p =>
      rw [SatGramActR.cmap_pos _ _ _ _ hβ]
      congr 1
      apply Subtype.ext
      show (p.1.1 * (1 : X.B.I.GA)⁻¹, p.1.2 * (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V)⁻¹) = p.1
      simp
  · exact SatGramActR.cmap_neg _ _ _ _ hβ c

/- English proof (translation)
Take `⟨Λ, hΛ, Λ', hΛ', c⟩` from `t`. Use `show (⟨Λ, hΛ, Λ', hΛ', SatGramActR.cmap x β hN hx c⟩ : GTerm X u u' F0 F0' what₂ rows') = ⟨Λ, hΛ, Λ', hΛ', c⟩`. Rewrite using `[cmap_id hN hx hx1 hβ1]`.
-/
theorem tmap_id {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    {x : X.B.I.GA} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hN : SatGramActR.AutFConjN) (hx : RatLink X x β) (hx1 : x = 1) (hβ1 : β = 1)
    (t : GTerm X u u' F0 F0' what₂ rows') : SatGramActR.tmap x β hN hx t = t := by
  obtain ⟨Λ, hΛ, Λ', hΛ', c⟩ := t
  show (⟨Λ, hΛ, Λ', hΛ', SatGramActR.cmap x β hN hx c⟩ : GTerm X u u' F0 F0' what₂ rows') = ⟨Λ, hΛ, Λ', hΛ', c⟩
  rw [cmap_id hN hx hx1 hβ1]

variable {Y : Full X} {u u' : D.what₂.Word}

/- English proof (translation)
The claim follows from `tmap_id _ _ rfl isoG_one t`.
-/
theorem act_one (q : {Λ // Λ ∈ Y.what₂ u'}) (t : TT Y u u') :
    KernelOfEmbedding.act Y q ⟨1, one_mem_gamL (Y.cs u') q⟩ t = t :=
  tmap_id _ _ rfl isoG_one t

/- English proof (translation)
Introduce `u u' s s' h hrow`. Take `⟨γ, rfl⟩` from `KernelOfEmbedding.fib_gam (hN u') h`. Establish `hι` using `KernelOfEmbedding.iota_act hIR ⟨s.lam', s.mem'⟩ γ s rfl`. Establish `hι2 : iotaOf Y.TR (Y.cs u) (Y.cs u') s = iotaOf Y.TR (Y.cs u) (Y.cs u') (KernelOfEmbedding.act Y ⟨s.lam', s.mem'⟩ γ s)` using `congrArg (fun r => r.2.2) hrow`. Rewrite `hι2` using `[hι]`.

Establish `hl : levi Y.TR (SatGramActL.kB (Y.cs u') s.lam' γ.1) = 1`. Establish `h3 : iotaOf Y.TR (Y.cs u) (Y.cs u') s * (levi Y.TR (SatGramActL.kB (Y.cs u') s.lam' γ.1))⁻¹ = iotaOf Y.TR (Y.cs u) (Y.cs u') s * 1` using `by rw [mul_one]; exact hι2.symm`. Conclude with `inv_eq_one.1 (mul_left_cancel h3)`. Establish `hg : gamL_levi (Y.cs u') Y.TR ⟨s.lam', s.mem'⟩ γ = gamL_levi (Y.cs u') Y.TR ⟨s.lam', s.mem'⟩ ⟨1, one_mem_gamL (Y.cs u') ⟨s.lam', s.mem'⟩⟩`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show levi Y.TR (colD _ _) = levi Y.TR (colD _ _)`. Establish `e1 : colD ((Y.cs u').h ((Y.cs u').base s.lam')) (iotaF X u' γ.1 * (Y.cs u').h ((Y.cs u').base s.lam')) = SatGramActL.kB (Y.cs u') s.lam' γ.1` using `(aK_eq _ _).symm`. Establish `e2 : colD ((Y.cs u').h ((Y.cs u').base s.lam')) (iotaF X u' 1 * (Y.cs u').h ((Y.cs u').base s.lam')) = 1`. Unfold `colD`. Simplify using the standard rewrite rules.

Rewrite using `[e1, e2, hl, levi_one]`. Establish `h1` using `(gamL_levi_bij (Y.cs u') Y.TR Y.hK (hN u') ⟨s.lam', s.mem'⟩).1 hg`. Rewrite using `[h1, act_one]`.
-/
theorem rowFree_of (hN : ∀ u' : D.what₂.Word, Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK)
    (hIR : SatGramRep.IotaRepC) : Formalism.L2.SG.Pf.FibreCounting.RowFree Y := by
  intro u u' s s' h hrow
  obtain ⟨γ, rfl⟩ := KernelOfEmbedding.fib_gam (hN u') h
  have hι := KernelOfEmbedding.iota_act hIR ⟨s.lam', s.mem'⟩ γ s rfl
  have hι2 : iotaOf Y.TR (Y.cs u) (Y.cs u') s =
      iotaOf Y.TR (Y.cs u) (Y.cs u') (KernelOfEmbedding.act Y ⟨s.lam', s.mem'⟩ γ s) := congrArg (fun r => r.2.2) hrow
  rw [hι] at hι2
  have hl : levi Y.TR (SatGramActL.kB (Y.cs u') s.lam' γ.1) = 1 := by
    have h3 : iotaOf Y.TR (Y.cs u) (Y.cs u') s * (levi Y.TR (SatGramActL.kB (Y.cs u') s.lam' γ.1))⁻¹ =
        iotaOf Y.TR (Y.cs u) (Y.cs u') s * 1 := by rw [mul_one]; exact hι2.symm
    exact inv_eq_one.1 (mul_left_cancel h3)
  have hg : gamL_levi (Y.cs u') Y.TR ⟨s.lam', s.mem'⟩ γ =
      gamL_levi (Y.cs u') Y.TR ⟨s.lam', s.mem'⟩ ⟨1, one_mem_gamL (Y.cs u') ⟨s.lam', s.mem'⟩⟩ := by
    apply Subtype.ext
    show levi Y.TR (colD _ _) = levi Y.TR (colD _ _)
    have e1 : colD ((Y.cs u').h ((Y.cs u').base s.lam')) (iotaF X u' γ.1 * (Y.cs u').h ((Y.cs u').base s.lam')) =
        SatGramActL.kB (Y.cs u') s.lam' γ.1 := (aK_eq _ _).symm
    have e2 : colD ((Y.cs u').h ((Y.cs u').base s.lam')) (iotaF X u' 1 * (Y.cs u').h ((Y.cs u').base s.lam')) = 1 := by
      unfold colD; simp
    rw [e1, e2, hl, levi_one]
  have h1 := (gamL_levi_bij (Y.cs u') Y.TR Y.hK (hN u') ⟨s.lam', s.mem'⟩).1 hg
  rw [h1, act_one]

/- English proof (translation)
The claim follows from `rowFree_of hN hIR u u' s₁ s₂ h hr`.
-/
theorem liftIotaFree (hN : ∀ u' : D.what₂.Word, Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK)
    (hIR : SatGramRep.IotaRepC) (u u' : D.what₂.Word) (s₁ s₂ : TT Y u u') (h : s₁.toTerm = s₂.toTerm)
    (hr : rowOf Y.TR (Y.cs u) (Y.cs u') s₁ = rowOf Y.TR (Y.cs u) (Y.cs u') s₂) : s₁ = s₂ :=
  rowFree_of hN hIR u u' s₁ s₂ h hr

end Row

end Formalism.L2.SG.Pf.Act
