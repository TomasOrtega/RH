import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActRRep
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FormHermitianPositive
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LeviColsPf

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp Formalism.L2.SG.NormCut Formalism.L2.SG.Pf.SatGramRep
  Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf.SatGramActR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Steps

def LiftAut : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (w : D.what₂.Word)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), Λ ∈ Y.what₂ w → ∀ γ : Gam X w,
    ((((Y.cs w).h ((Y.cs w).base Λ) : X.B.I.Gf) * X.xu w)⁻¹ * (iotaF X w γ : X.B.I.Gf) *
        (((Y.cs w).h ((Y.cs w).base Λ) : X.B.I.Gf) * X.xu w) ∈ X.B.I.Kset) →
    ∃ β : (VS D).V ≃ₗ[D.host.E] (VS D).V, RatLink X (γ : X.B.I.GA) β ∧
      β ∈ Formalism.L2.SG.Saturated.AutF Λ (lf D (X.Fu w))

def AutFConjN : Prop :=
  ∀ (D : D7) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V), β ∈ Formalism.L2.SG.Saturated.AutF Λ F →
    ∀ n ∈ NLam Λ F, β * n * β⁻¹ ∈ NLam Λ F

def ChiNR : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : D.what₂.Word) (h : Hfin X w) (γ : Gam X w) (κ : X.B.I.Gf),
    κ ∈ X.B.I.Kset →
    ((h : X.B.I.Gf) * X.xu w)⁻¹ * (iotaF X w γ : X.B.I.Gf) * ((h : X.B.I.Gf) * X.xu w) ∈ X.B.I.Kset →
    chiN X (κ * (((h : X.B.I.Gf) * X.xu w)⁻¹ * (iotaF X w γ : X.B.I.Gf) * ((h : X.B.I.Gf) * X.xu w))⁻¹) = chiN X κ

def OOR : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (γ : Gam X u') (Ω : Set X.B.I.Ginf)
    (x : X.B.I.Ginf),
    (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
     OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Ω (X.Wu u) (X.Wu u') (x * ((γ : X.B.I.GA).1)⁻¹) =
       (OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Ω (X.Wu u) (X.Wu u') x).comp (X.piU u' ((γ : X.B.I.GA).1)⁻¹))

def HSR : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (γ : Gam X u'),
    ∃ U : Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u) ≃ₗᵢ[ℂ] Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u),
      ∀ A : X.Vpi u' →L[ℂ] X.Vpi u,
        U (Formalism.L2.SG.PackageTie.hsEmb A) = Formalism.L2.SG.PackageTie.hsEmb (A.comp (X.piU u' ((γ : X.B.I.GA).1)⁻¹))

end Steps

section Map

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

/- English proof (translation)
Take `⟨⟨h1, -⟩, -, -⟩` from `hβ`. Conclude with `h1`.
-/
theorem isom_of_autF {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {F : LFlag (VS D) D.R.rS T}
    {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hβ : β ∈ Formalism.L2.SG.Saturated.AutF Λ F) :
    β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by
  obtain ⟨⟨h1, -⟩, -, -⟩ := hβ
  exact h1

/- English proof (translation)
Take `⟨⟨-, h2⟩, -, -⟩` from `hβ`. Conclude with `h2`.
-/
theorem gmap_of_autF {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {F : LFlag (VS D) D.R.rS T}
    {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hβ : β ∈ Formalism.L2.SG.Saturated.AutF Λ F) :
    Formalism.HermitianLatticesTheory.gmap β Λ = Λ := by
  obtain ⟨⟨-, h2⟩, -, -⟩ := hβ
  exact h2

/- English proof (translation)
Establish `hiso` using `isom_of_autF hβ`. Take `⟨-, hfr, hzt⟩` from `hβ`. Establish `hinv : ∀ v, β v = v → β⁻¹ v = v`. Introduce `v hv`. Combine the equalities or inequalities in the displayed calculation.

Establish `he : ∀ i, β (F.fl.e i) = F.fl.e i`. Introduce `i`. Use `hfr (Fin.castSucc i)` as an intermediate fact. Simplify `this` using `[Formalism.MainNotions.S.Lat.frame, Formalism.MainNotions.S.FlagG.fvec]`. Establish `hz : β F.fl.z = F.fl.z`.

Use `hfr (Fin.last _)` as an intermediate fact. Simplify `this` using `[Formalism.MainNotions.S.Lat.frame, Formalism.MainNotions.S.FlagG.fvec]`. Establish `key : ∀ A B : Formalism.MainNotions.S.FlagG (VS D) D.R.rS T, A.e = B.e → A.z = B.z → A = B`. Introduce and unpack `⟨e1, z1, _, _, _, _⟩ ⟨e2, z2, _, _, _, _⟩ h1 h2`. Consider the cases of `h1`.

Consider the cases of `h2`. Both sides reduce to the same expression. Establish `hγβ : γ * β⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `Subgroup.mul_mem _ hγ (Subgroup.inv_mem _ hiso)`. Unfold `mapLF`. Rewrite using `[dif_pos hγβ, dif_pos hγ]`.

Use `congr 1`. Apply `key` to reduce the goal to its premises. Use function extensionality and compare the values at `a show γ (β⁻¹ (F.fl.e a)) = γ (F.fl.e a)`. Rewrite using `[hinv _ (he a)]`. Use `show γ (β⁻¹ F.fl.z) = γ F.fl.z`.

Rewrite using `[hinv _ hz]`. Use `show γ (β⁻¹ F.zt) = γ F.zt`. Rewrite using `[hinv _ hzt]`.
-/
theorem mapLF_mul_aut {Λ' : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {F : LFlag (VS D) D.R.rS T}
    {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hβ : β ∈ Formalism.L2.SG.Saturated.AutF Λ' F)
    (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) :
    mapLF (γ * β⁻¹) F = mapLF γ F := by
  have hiso := isom_of_autF hβ
  obtain ⟨-, hfr, hzt⟩ := hβ
  have hinv : ∀ v, β v = v → β⁻¹ v = v := by
    intro v hv
    calc β⁻¹ v = β⁻¹ (β v) := by rw [hv]
      _ = v := β.symm_apply_apply v
  have he : ∀ i, β (F.fl.e i) = F.fl.e i := by
    intro i
    have := hfr (Fin.castSucc i)
    simpa [Formalism.MainNotions.S.Lat.frame, Formalism.MainNotions.S.FlagG.fvec] using this
  have hz : β F.fl.z = F.fl.z := by
    have := hfr (Fin.last _)
    simpa [Formalism.MainNotions.S.Lat.frame, Formalism.MainNotions.S.FlagG.fvec] using this
  have key : ∀ A B : Formalism.MainNotions.S.FlagG (VS D) D.R.rS T, A.e = B.e → A.z = B.z → A = B := by
    rintro ⟨e1, z1, _, _, _, _⟩ ⟨e2, z2, _, _, _, _⟩ h1 h2
    cases h1
    cases h2
    rfl
  have hγβ : γ * β⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := Subgroup.mul_mem _ hγ (Subgroup.inv_mem _ hiso)
  unfold mapLF
  rw [dif_pos hγβ, dif_pos hγ]
  congr 1
  · apply key
    · funext a
      show γ (β⁻¹ (F.fl.e a)) = γ (F.fl.e a)
      rw [hinv _ (he a)]
    · show γ (β⁻¹ F.fl.z) = γ F.fl.z
      rw [hinv _ hz]
  · show γ (β⁻¹ F.zt) = γ F.zt
    rw [hinv _ hzt]

variable (x : X.B.I.GA) (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)

def rmul (hx : RatLink X x β) {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}
    (hβ : β ∈ Formalism.L2.SG.Saturated.AutF Λ' (lf D F0')) (p : GCar X u u' F0 F0' Λ Λ') : GCar X u u' F0 F0' Λ Λ' :=
  ⟨(p.1.1 * x⁻¹, p.1.2 * β⁻¹),
    Formalism.L2.SG.Pf.ratLink_mul X p.2.1 (Formalism.L2.SG.Pf.ratLink_inv X hx),
    Subgroup.mul_mem _ p.2.2.1 (Subgroup.inv_mem _ (isom_of_autF hβ)),
    by rw [Formalism.L2.SG.Pf.gmap_mul, Formalism.L2.SG.Pf.gmap_inv (gmap_of_autF hβ), p.2.2.2.1],
    by rw [mapLF_mul_aut hβ p.1.2 p.2.2.1]; exact p.2.2.2.2⟩

/- English proof (translation)
Take `⟨n, hn, n', hn', hq⟩` from `h`. Use `⟨n, hn, β * n' * β⁻¹, hN D Λ' (lf D F0') β hβ n' hn', ?_⟩` and prove the remaining obligations. Use `show q.1.2 * β⁻¹ = n * (p.1.2 * β⁻¹) * (β * n' * β⁻¹)`. Rewrite using `[hq]`. Use `group`.
-/
theorem rmul_rel (hN : AutFConjN) (hx : RatLink X x β) {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}
    (hβ : β ∈ Formalism.L2.SG.Saturated.AutF Λ' (lf D F0')) (p q : GCar X u u' F0 F0' Λ Λ')
    (h : GRel X u u' F0 F0' Λ Λ' p q) : GRel X u u' F0 F0' Λ Λ' (rmul x β hx hβ p) (rmul x β hx hβ q) := by
  obtain ⟨n, hn, n', hn', hq⟩ := h
  refine ⟨n, hn, β * n' * β⁻¹, hN D Λ' (lf D F0') β hβ n' hn', ?_⟩
  show q.1.2 * β⁻¹ = n * (p.1.2 * β⁻¹) * (β * n' * β⁻¹)
  rw [hq]
  group

def cmap (hN : AutFConjN) (hx : RatLink X x β) {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}
    (c : GQ X u u' F0 F0' Λ Λ') : GQ X u u' F0 F0' Λ Λ' :=
  if hβ : β ∈ Formalism.L2.SG.Saturated.AutF Λ' (lf D F0') then Quot.map (rmul x β hx hβ) (rmul_rel x β hN hx hβ) c else c

/- English proof (translation)
Unfold `cmap`. Conclude with `dif_pos hβ`.
-/
theorem cmap_pos (hN : AutFConjN) (hx : RatLink X x β) {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}
    (hβ : β ∈ Formalism.L2.SG.Saturated.AutF Λ' (lf D F0')) (p : GCar X u u' F0 F0' Λ Λ') :
    cmap x β hN hx (Quot.mk _ p) = Quot.mk _ (rmul x β hx hβ p) := by
  unfold cmap
  exact dif_pos hβ

/- English proof (translation)
Unfold `cmap`. Conclude with `dif_neg hβ`.
-/
theorem cmap_neg (hN : AutFConjN) (hx : RatLink X x β) {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}
    (hβ : β ∉ Formalism.L2.SG.Saturated.AutF Λ' (lf D F0')) (c : GQ X u u' F0 F0' Λ Λ') :
    cmap x β hN hx c = c := by
  unfold cmap
  exact dif_neg hβ

/- English proof (translation)
Establish `inv_autF : ∀ {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V}, γ ∈ Formalism.L2.SG.Saturated.AutF Λ' (lf D F0') → γ⁻¹ ∈ Formalism.L2.SG.Saturated.AutF Λ' (lf D F0')`. Introduce `γ hγ`. Establish `hiso` using `isom_of_autF hγ`. Establish `hg` using `gmap_of_autF hγ`. Take `⟨-, hfr, hzt⟩` from `hγ`.

Establish `hinv : ∀ v, γ v = v → γ⁻¹ v = v`. Introduce `v hv`. Combine the equalities or inequalities in the displayed calculation. Conclude with `⟨⟨Subgroup.inv_mem _ hiso, Formalism.L2.SG.Pf.gmap_inv hg⟩, fun a => hinv _ (hfr a), hinv _ hzt⟩`. Distinguish the cases in `hβ : β ∈ Formalism.L2.SG.Saturated.AutF Λ' (lf D F0')`.

Establish `hβ'` using `inv_autF hβ`. Take `⟨p, rfl⟩` from `Quot.exists_rep c`. Rewrite using `[cmap_pos x β hN hx hβ p, cmap_pos x⁻¹ β⁻¹ hN (Formalism.L2.SG.Pf.ratLink_inv X hx) hβ']`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show ((p.1.1 * x⁻¹) * x⁻¹⁻¹, (p.1.2 * β⁻¹) * β⁻¹⁻¹) = p.1`. Simplify using the standard rewrite rules. Establish `hβ' : β⁻¹ ∉ Formalism.L2.SG.Saturated.AutF Λ' (lf D F0')` using `fun h => hβ (by simpa using inv_autF h)`. Rewrite using `[cmap_neg x β hN hx hβ, cmap_neg x⁻¹ β⁻¹ hN (Formalism.L2.SG.Pf.ratLink_inv X hx) hβ']`.
-/
theorem cmap_inv (hN : AutFConjN) (hx : RatLink X x β) {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}
    (c : GQ X u u' F0 F0' Λ Λ') :
    cmap x⁻¹ β⁻¹ hN (Formalism.L2.SG.Pf.ratLink_inv X hx) (cmap x β hN hx c) = c := by
  have inv_autF : ∀ {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V},
      γ ∈ Formalism.L2.SG.Saturated.AutF Λ' (lf D F0') → γ⁻¹ ∈ Formalism.L2.SG.Saturated.AutF Λ' (lf D F0') := by
    intro γ hγ
    have hiso := isom_of_autF hγ
    have hg := gmap_of_autF hγ
    obtain ⟨-, hfr, hzt⟩ := hγ
    have hinv : ∀ v, γ v = v → γ⁻¹ v = v := by
      intro v hv
      calc γ⁻¹ v = γ⁻¹ (γ v) := by rw [hv]
        _ = v := γ.symm_apply_apply v
    exact ⟨⟨Subgroup.inv_mem _ hiso, Formalism.L2.SG.Pf.gmap_inv hg⟩, fun a => hinv _ (hfr a), hinv _ hzt⟩
  by_cases hβ : β ∈ Formalism.L2.SG.Saturated.AutF Λ' (lf D F0')
  · have hβ' := inv_autF hβ
    obtain ⟨p, rfl⟩ := Quot.exists_rep c
    rw [cmap_pos x β hN hx hβ p, cmap_pos x⁻¹ β⁻¹ hN (Formalism.L2.SG.Pf.ratLink_inv X hx) hβ']
    congr 1
    apply Subtype.ext
    show ((p.1.1 * x⁻¹) * x⁻¹⁻¹, (p.1.2 * β⁻¹) * β⁻¹⁻¹) = p.1
    simp
  · have hβ' : β⁻¹ ∉ Formalism.L2.SG.Saturated.AutF Λ' (lf D F0') := fun h => hβ (by simpa using inv_autF h)
    rw [cmap_neg x β hN hx hβ, cmap_neg x⁻¹ β⁻¹ hN (Formalism.L2.SG.Pf.ratLink_inv X hx) hβ']

def tmap (hN : AutFConjN) (hx : RatLink X x β) (t : GTerm X u u' F0 F0' what₂ rows') : GTerm X u u' F0 F0' what₂ rows' :=
  ⟨t.lam, t.mem, t.lam', t.mem', cmap x β hN hx t.cls⟩

/- English proof (translation)
Consider the cases of `t`. Simplify using `only [tmap, cmap_inv]`.
-/
theorem tmap_inv (hN : AutFConjN) (hx : RatLink X x β) (t : GTerm X u u' F0 F0' what₂ rows') :
    tmap x⁻¹ β⁻¹ hN (Formalism.L2.SG.Pf.ratLink_inv X hx) (tmap x β hN hx t) = t := by
  cases t
  simp only [tmap, cmap_inv]

def tequiv (hN : AutFConjN) (hx : RatLink X x β) : GTerm X u u' F0 F0' what₂ rows' ≃ GTerm X u u' F0 F0' what₂ rows' where
  toFun := tmap x β hN hx
  invFun := tmap x⁻¹ β⁻¹ hN (Formalism.L2.SG.Pf.ratLink_inv X hx)
  left_inv t := tmap_inv x β hN hx t
  right_inv t := by
    have := tmap_inv x⁻¹ β⁻¹ hN (Formalism.L2.SG.Pf.ratLink_inv X hx) t
    simp only [inv_inv] at this
    exact this

/- English proof (translation)
Establish `h1 : t.cls = Quot.mk _ t.rep` using `(Quot.out_eq t.cls).symm`. Use `show cmap x β hN hx t.cls = _`. Rewrite using `[h1]`. Conclude with `cmap_pos x β hN hx hβ t.rep`.
-/
theorem tmap_cls (hN : AutFConjN) (hx : RatLink X x β) (t : GTerm X u u' F0 F0' what₂ rows')
    (hβ : β ∈ Formalism.L2.SG.Saturated.AutF t.lam' (lf D F0')) :
    (tmap x β hN hx t).cls = Quot.mk _ (rmul x β hx hβ t.rep) := by
  have h1 : t.cls = Quot.mk _ t.rep := (Quot.out_eq t.cls).symm
  show cmap x β hN hx t.cls = _
  rw [h1]
  exact cmap_pos x β hN hx hβ t.rep

/- English proof (translation)
Distinguish the cases in `hβ : β ∈ Formalism.L2.SG.Saturated.AutF t.lam' (lf D F0')`. Establish `hTR` using `Formalism.L2.SG.Pf.toTermRel_holds X u u' F0 F0'`. Establish `mk_congr : ∀ (A B : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (hA : TermDef.PD D t.lam (lf D F0) u' A) (hB : TermDef.PD D t.lam (lf D F0) u' B), A = B → TermDef.mk t.lam (lf D F0) (TermDef.PD D t.lam (lf D F0) u') ⟨A, hA⟩ = TermDef.mk t.lam (lf D F0) (TermDef.PD D t.lam (lf …`. Introduce and unpack `A B hA hB rfl`. Both sides reduce to the same expression.

Set `f : GCar X u u' F0 F0' t.lam t.lam' → TermDef.TermQ t.lam (lf D F0) (TermDef.PD D t.lam (lf D F0) u')` to `fun p => TermDef.mk _ _ _ ⟨mapLF p.1.2 (lf D F0'), p.2.2.2.2⟩`. Establish `hf : ∀ p q, GRel X u u' F0 F0' t.lam t.lam' p q → f p = f q`. Introduce `p q h`. Conclude with `Quot.sound (hTR _ _ p q h)`. Establish `key : ∀ c : GQ X u u' F0 F0' t.lam t.lam', f (Quot.out c) = Quot.lift f hf c` using `fun c => congrArg (Quot.lift f hf) (Quot.out_eq c)`.

Establish `h1` using `tmap_cls x β hN hx t hβ`. Establish `h2 : f (tmap x β hN hx t).rep = f (rmul x β hx hβ t.rep)` using `(key (tmap x β hN hx t).cls).trans (by rw [h1])`. Establish `h3 : f (rmul x β hx hβ t.rep) = f t.rep` using `mk_congr _ _ _ _ (mapLF_mul_aut hβ t.rep.1.2 t.rep.2.2.1)`. Use `show (⟨t.lam, t.mem, f (tmap x β hN hx t).rep⟩ : TermDef.Term D u u' F0 what₂) = ⟨t.lam, t.mem, f t.rep⟩`. Rewrite using `[h2, h3]`.

Establish `h : tmap x β hN hx t = t` using `by show (⟨t.lam, t.mem, t.lam', t.mem', cmap x β hN hx t.cls⟩ : GTerm X u u' F0 F0' what₂ rows') = t`. Rewrite using `[cmap_neg x β hN hx hβ]`. Rewrite using `[h]`.
-/
theorem toTerm_tmap (hN : AutFConjN) (hx : RatLink X x β) (t : GTerm X u u' F0 F0' what₂ rows') :
    (tmap x β hN hx t).toTerm = t.toTerm := by
  by_cases hβ : β ∈ Formalism.L2.SG.Saturated.AutF t.lam' (lf D F0')
  · have hTR := Formalism.L2.SG.Pf.toTermRel_holds X u u' F0 F0'
    have mk_congr : ∀ (A B : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
        (hA : TermDef.PD D t.lam (lf D F0) u' A) (hB : TermDef.PD D t.lam (lf D F0) u' B), A = B →
        TermDef.mk t.lam (lf D F0) (TermDef.PD D t.lam (lf D F0) u') ⟨A, hA⟩ =
          TermDef.mk t.lam (lf D F0) (TermDef.PD D t.lam (lf D F0) u') ⟨B, hB⟩ := by
      rintro A B hA hB rfl
      rfl
    let f : GCar X u u' F0 F0' t.lam t.lam' → TermDef.TermQ t.lam (lf D F0) (TermDef.PD D t.lam (lf D F0) u') :=
      fun p => TermDef.mk _ _ _ ⟨mapLF p.1.2 (lf D F0'), p.2.2.2.2⟩
    have hf : ∀ p q, GRel X u u' F0 F0' t.lam t.lam' p q → f p = f q := by
      intro p q h
      exact Quot.sound (hTR _ _ p q h)
    have key : ∀ c : GQ X u u' F0 F0' t.lam t.lam', f (Quot.out c) = Quot.lift f hf c :=
      fun c => congrArg (Quot.lift f hf) (Quot.out_eq c)
    have h1 := tmap_cls x β hN hx t hβ
    have h2 : f (tmap x β hN hx t).rep = f (rmul x β hx hβ t.rep) :=
      (key (tmap x β hN hx t).cls).trans (by rw [h1])
    have h3 : f (rmul x β hx hβ t.rep) = f t.rep :=
      mk_congr _ _ _ _ (mapLF_mul_aut hβ t.rep.1.2 t.rep.2.2.1)
    show (⟨t.lam, t.mem, f (tmap x β hN hx t).rep⟩ : TermDef.Term D u u' F0 what₂) = ⟨t.lam, t.mem, f t.rep⟩
    rw [h2, h3]
  · have h : tmap x β hN hx t = t := by
      show (⟨t.lam, t.mem, t.lam', t.mem', cmap x β hN hx t.cls⟩ : GTerm X u u' F0 F0' what₂ rows') = t
      rw [cmap_neg x β hN hx hβ]
    rw [h]

end Map

section Act

open Formalism.L2.SG.Full

def RightActC' : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    AmpWellDef (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') →
    OOFundIndep X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    ∀ S ∈ ({(Y.tO u u').genSet, (Y.tO u u').ngSet, (Y.tO u u').degSet} :
      Set (Set (GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')))),
    Formalism.L2.SG.Pf.SatGram.RightAct (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') S
      (Aset Y.TR (Y.cs u'))

end Act

end Formalism.L2.SG.Pf.SatGramActR
