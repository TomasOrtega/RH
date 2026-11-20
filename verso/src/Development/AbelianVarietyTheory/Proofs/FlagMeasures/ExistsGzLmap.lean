import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HbApply
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitLatticeUnimodularAndPrimitive
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsEqOfStabilizerConjugateLattices
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowsOrb.StabAct

open GlobalTheory.RowsOrb GlobalTheory.RowsOrb.Uniq

variable {D : D7} (X : HidaSetting D)

abbrev Xs : Submodule D.host.E (VS D).V := Submodule.span D.host.E (Set.range X.eX)

/- English proof (translation)
Establish `hdY` using `dual_symm hh X.ef`. Rewrite using `[P_apply, ← coord hdY hx, sub_self]`.
-/
theorem P_X {x : (VS D).V} (hx : x ∈ Xs X) : P (VS D).hT X.eX X.fY x = 0 := by
  have hdY := dual_symm hh X.ef
  rw [P_apply, ← coord hdY hx, sub_self]

/- English proof (translation)
Rewrite using `[P_apply]`. Simplify using `[((mem_Wb X w).1 hw _).2]`.
-/
theorem P_Wb {w : (VS D).V} (hw : w ∈ Wb X) : P (VS D).hT X.eX X.fY w = w := by
  rw [P_apply]; simp [((mem_Wb X w).1 hw _).2]

/- English proof (translation)
Rewrite using `[P_apply, sub_sub_cancel]`. Conclude with `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)`.
-/
theorem sub_proj_mem₂ (v : (VS D).V) : v - P (VS D).hT X.eX X.fY v ∈ Xs X := by
  rw [P_apply, sub_sub_cancel]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

variable {X}

/- English proof (translation)
Rewrite using `[← δ.apply_symm_apply (X.eX a), hδ]`. Conclude with `GlobalTheory.RowsOrb.Basic.hT_span_left X.eX w (fun b => ((mem_Wb X w).1 hw b).1) (hX _ (Submodule.subset_span ⟨a, rfl⟩))`.
-/
theorem orth_e (δ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hδ : ∀ x y, (VS D).hT (δ x) (δ y) = (VS D).hT x y)
    (hX : ∀ x ∈ Xs X, δ.symm x ∈ Xs X) {w : (VS D).V} (hw : w ∈ Wb X) (a : Fin D.R.rS) :
    (VS D).hT (X.eX a) (δ w) = 0 := by
  rw [← δ.apply_symm_apply (X.eX a), hδ]
  exact GlobalTheory.RowsOrb.Basic.hT_span_left X.eX w (fun b => ((mem_Wb X w).1 hw b).1)
    (hX _ (Submodule.subset_span ⟨a, rfl⟩))

variable (X)

def gl (δ : (VS D).V →ₗ[D.host.E] (VS D).V) (hS : ∀ w ∈ Wb X, ∀ a, (VS D).hT (X.eX a) (δ w) = 0) :
    Wb X →ₗ[D.host.E] Wb X :=
  LinearMap.codRestrict (Wb X) (P (VS D).hT X.eX X.fY ∘ₗ δ ∘ₗ (Wb X).subtype)
    (fun w a => P_mem X.ee (dual_symm hh X.ef) (hS _ w.2) a)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gl_coe (δ : (VS D).V →ₗ[D.host.E] (VS D).V) (hS : ∀ w ∈ Wb X, ∀ a, (VS D).hT (X.eX a) (δ w) = 0)
    (w : Wb X) : ((gl X δ hS w : Wb X) : (VS D).V) = P (VS D).hT X.eX X.fY (δ w) := rfl

/- English proof (translation)
Establish `e : P (VS D).hT X.eX X.fY (δ w) = δ w - (δ w - P (VS D).hT X.eX X.fY (δ w))` using `by abel`. Rewrite using `[e, map_sub, hεδ, map_sub, P_X X (hε _ (sub_proj_mem₂ X _)), sub_zero, P_Wb X hw]`.
-/
theorem gl_inv (δ ε : (VS D).V →ₗ[D.host.E] (VS D).V) (hεδ : ∀ v, ε (δ v) = v)
    (hε : ∀ x ∈ Xs X, ε x ∈ Xs X) {w : (VS D).V} (hw : w ∈ Wb X) :
    P (VS D).hT X.eX X.fY (ε (P (VS D).hT X.eX X.fY (δ w))) = w := by
  have e : P (VS D).hT X.eX X.fY (δ w) = δ w - (δ w - P (VS D).hT X.eX X.fY (δ w)) := by abel
  rw [e, map_sub, hεδ, map_sub, P_X X (hε _ (sub_proj_mem₂ X _)), sub_zero, P_Wb X hw]

def ge (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (h1 : ∀ w ∈ Wb X, ∀ a, (VS D).hT (X.eX a) (γ w) = 0)
    (h2 : ∀ w ∈ Wb X, ∀ a, (VS D).hT (X.eX a) (γ.symm w) = 0)
    (hX : ∀ x ∈ Xs X, γ x ∈ Xs X) (hX' : ∀ x ∈ Xs X, γ.symm x ∈ Xs X) : Wb X ≃ₗ[D.host.E] Wb X :=
  LinearEquiv.ofLinear (gl X (γ : (VS D).V →ₗ[D.host.E] (VS D).V) h1)
    (gl X ((γ.symm : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) h2)
    (LinearMap.ext fun w => Subtype.ext (gl_inv X _ _ (fun v => γ.apply_symm_apply v) hX w.2))
    (LinearMap.ext fun w => Subtype.ext (gl_inv X _ _ (fun v => γ.symm_apply_apply v) hX' w.2))

/- English proof (translation)
Take `⟨l, hl, x, hx, rfl⟩` from `Submodule.mem_sup.1 hv`. Rewrite `hx` using `[GlobalTheory.RowsOrb.Basic.mem_XO]`. Use `Submodule.mem_sup.2 ⟨δ l, Submodule.mem_map_of_mem hl, δ x - (δ (l + x) - P (VS D).hT X.eX X.fY (δ (l + x))), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.RowsOrb.Basic.mem_XO]`. Conclude with `Submodule.sub_mem _ (hX x hx) (sub_proj_mem₂ X _)`.

Rewrite using `[map_add]`. Normalize the expressions using the abelian group laws.
-/
theorem transport (u : D.what₂.Word) (δ : (VS D).V →ₗ[D.host.E] (VS D).V) (hX : ∀ x ∈ Xs X, δ x ∈ Xs X)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) {v : (VS D).V}
    (hv : v ∈ Λ ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X) :
    P (VS D).hT X.eX X.fY (δ v) ∈
      Λ.map (δ.restrictScalars (𝓞 D.host.E)) ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X := by
  obtain ⟨l, hl, x, hx, rfl⟩ := Submodule.mem_sup.1 hv
  rw [GlobalTheory.RowsOrb.Basic.mem_XO] at hx
  refine Submodule.mem_sup.2 ⟨δ l, Submodule.mem_map_of_mem hl,
    δ x - (δ (l + x) - P (VS D).hT X.eX X.fY (δ (l + x))), ?_, ?_⟩
  · rw [GlobalTheory.RowsOrb.Basic.mem_XO]
    exact Submodule.sub_mem _ (hX x hx) (sub_proj_mem₂ X _)
  · rw [map_add]; abel

end GlobalTheory.RowsOrb.StabAct

open GlobalTheory.RowsOrb.StabAct GlobalTheory.RowsOrb.Uniq in

/- English proof (translation)
Introduce `D X u γ hγ`. Take `⟨hiso, hXa, hz⟩` from `hγ`. Establish `hδ : ∀ x y, (VS D).hT (γ x) (γ y) = (VS D).hT x y` using `hiso`. Establish `hδ' : ∀ x y, (VS D).hT (γ.symm x) (γ.symm y) = (VS D).hT x y` using `fun x y => by`. Rewrite using `[← hδ, γ.apply_symm_apply, γ.apply_symm_apply]`.

Establish `hXr : (X.Fu u).Xa D.R.rS = Xs X`. Simplify using `only [FlagG.Xa, HidaSetting.Fu_e]`. Use `congr 1`. Use extensionality with `v`. Simplify using the standard rewrite rules.

Establish `hmap` using `hXa D.R.rS`. Rewrite `hmap` using `[hXr]`. Establish `hX : ∀ x ∈ Xs X, γ x ∈ Xs X` using `fun x hx => by`. Rewrite using `[← hmap]`. Conclude with `Submodule.mem_map_of_mem hx`.

Establish `hX' : ∀ x ∈ Xs X, γ.symm x ∈ Xs X` using `fun x hx => by`. Rewrite `hx` using `[← hmap]`. Take `⟨y, hy, rfl⟩` from `hx`. Simplify using `using hy`. Establish `h1` using `fun w (hw : w ∈ GlobalTheory.RowsOrb.Wb X) a => orth_e γ hδ hX' hw a`.

Establish `h2` using `fun w (hw : w ∈ GlobalTheory.RowsOrb.Wb X) a => orth_e γ.symm hδ' (fun x hx => by simpa using hX x hx) hw a`. Establish `hz' : γ (X.zu u) = X.zu u` using `by rw [← HidaSetting.flagZVector]; exact hz`. Set `e` to `ge X γ h1 h2 hX hX'`. Establish `he : ∀ w, ((e w : GlobalTheory.RowsOrb.Wb X) : (VS D).V) = P (VS D).hT X.eX X.fY (γ w)` using `fun w => rfl`. Establish `he' : ∀ w, ((e.symm w : GlobalTheory.RowsOrb.Wb X) : (VS D).V) = P (VS D).hT X.eX X.fY (γ.symm w)` using `fun w => rfl`.

Establish `hi : e ∈ Formalism.HermitianLatticesTheory.isom (GlobalTheory.RowsOrb.hb X)`. Introduce `x y`. Rewrite using `[GlobalTheory.RowsOrb.hb_apply, GlobalTheory.RowsOrb.hb_apply, he, he, P_apply, P_apply, P_iso hh X.ee (orth_e γ hδ hX' x.2) (orth_e γ hδ hX' y.2), hδ]`. Establish `hs : (⟨e, hi⟩ : Formalism.HermitianLatticesTheory.isom (GlobalTheory.RowsOrb.hb X)) ∈ GlobalTheory.RowsOrb.Gz X u`. Rewrite using `[MulAction.mem_stabilizer_iff]`.

Use `show e (GlobalTheory.RowsOrb.zb X u) = GlobalTheory.RowsOrb.zb X u`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[he, GlobalTheory.RowsOrb.zb_coe, hz']`. Conclude with `P_Wb X (GlobalTheory.RowsOrb.zb X u).2`. Use `⟨⟨⟨e, hi⟩, hs⟩, fun Λ => ?_⟩` and prove the remaining obligations.

Establish `hback : (Formalism.HermitianLatticesTheory.gmap γ Λ).map (((γ.symm : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) = Λ`. Use extensionality with `v`. Simplify using `only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨y, hy, rfl⟩, rfl⟩`.

Simplify using `using hy`. Introduce `hv`. Conclude with `⟨γ v, ⟨v, hv, rfl⟩, by simp⟩`. Use `show Formalism.HermitianLatticesTheory.gmap e (GlobalTheory.RowsOrb.Lmap X u Λ) = _`. Use extensionality with `w'`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Establish `h` using `transport X u (γ : (VS D).V →ₗ[D.host.E] (VS D).V) hX Λ ((GlobalTheory.RowsOrb.mem_Lmap X u Λ w).1 hw)`. Conclude with `(GlobalTheory.RowsOrb.mem_Lmap X u _ _).2 h`. Introduce `hw'`.

Use `⟨e.symm w', ?_, e.apply_symm_apply w'⟩` and prove the remaining obligations. Establish `h` using `transport X u ((γ.symm : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) hX' (Formalism.HermitianLatticesTheory.gmap γ Λ) ((GlobalTheory.RowsOrb.mem_Lmap X u _ w').1 hw')`. Rewrite `h` using `[hback]`. Conclude with `(GlobalTheory.RowsOrb.mem_Lmap X u _ _).2 h`.
-/
theorem GlobalTheory.RowsOrb.exists_gz_lmap : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), ∀ γ ∈ stabF D (X.Fu u),
    ∃ g : GlobalTheory.RowsOrb.Gz X u, ∀ Λ : Submodule (𝓞 D.host.E) (VS D).V,
      g • GlobalTheory.RowsOrb.Lmap X u Λ = GlobalTheory.RowsOrb.Lmap X u (Formalism.HermitianLatticesTheory.gmap γ Λ) := by
  intro D X u γ hγ
  obtain ⟨hiso, hXa, hz⟩ := hγ
  have hδ : ∀ x y, (VS D).hT (γ x) (γ y) = (VS D).hT x y := hiso
  have hδ' : ∀ x y, (VS D).hT (γ.symm x) (γ.symm y) = (VS D).hT x y := fun x y => by
    rw [← hδ, γ.apply_symm_apply, γ.apply_symm_apply]
  have hXr : (X.Fu u).Xa D.R.rS = Xs X := by
    simp only [FlagG.Xa, HidaSetting.Fu_e]
    congr 1
    ext v
    simp
  have hmap := hXa D.R.rS
  rw [hXr] at hmap
  have hX : ∀ x ∈ Xs X, γ x ∈ Xs X := fun x hx => by
    rw [← hmap]; exact Submodule.mem_map_of_mem hx
  have hX' : ∀ x ∈ Xs X, γ.symm x ∈ Xs X := fun x hx => by
    rw [← hmap] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  have h1 := fun w (hw : w ∈ GlobalTheory.RowsOrb.Wb X) a => orth_e γ hδ hX' hw a
  have h2 := fun w (hw : w ∈ GlobalTheory.RowsOrb.Wb X) a => orth_e γ.symm hδ' (fun x hx => by simpa using hX x hx) hw a
  have hz' : γ (X.zu u) = X.zu u := by rw [← HidaSetting.flagZVector]; exact hz
  let e := ge X γ h1 h2 hX hX'
  have he : ∀ w, ((e w : GlobalTheory.RowsOrb.Wb X) : (VS D).V) = P (VS D).hT X.eX X.fY (γ w) := fun w => rfl
  have he' : ∀ w, ((e.symm w : GlobalTheory.RowsOrb.Wb X) : (VS D).V) = P (VS D).hT X.eX X.fY (γ.symm w) := fun w => rfl
  have hi : e ∈ Formalism.HermitianLatticesTheory.isom (GlobalTheory.RowsOrb.hb X) := by
    intro x y
    rw [GlobalTheory.RowsOrb.hb_apply, GlobalTheory.RowsOrb.hb_apply, he, he, P_apply, P_apply,
      P_iso hh X.ee (orth_e γ hδ hX' x.2) (orth_e γ hδ hX' y.2), hδ]
  have hs : (⟨e, hi⟩ : Formalism.HermitianLatticesTheory.isom (GlobalTheory.RowsOrb.hb X)) ∈ GlobalTheory.RowsOrb.Gz X u := by
    rw [MulAction.mem_stabilizer_iff]
    show e (GlobalTheory.RowsOrb.zb X u) = GlobalTheory.RowsOrb.zb X u
    apply Subtype.ext
    rw [he, GlobalTheory.RowsOrb.zb_coe, hz']
    exact P_Wb X (GlobalTheory.RowsOrb.zb X u).2
  refine ⟨⟨⟨e, hi⟩, hs⟩, fun Λ => ?_⟩
  have hback : (Formalism.HermitianLatticesTheory.gmap γ Λ).map
      (((γ.symm : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars
        (𝓞 D.host.E)) = Λ := by
    ext v
    simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa using hy
    · intro hv
      exact ⟨γ v, ⟨v, hv, rfl⟩, by simp⟩
  show Formalism.HermitianLatticesTheory.gmap e (GlobalTheory.RowsOrb.Lmap X u Λ) = _
  ext w'
  constructor
  · rintro ⟨w, hw, rfl⟩
    have h := transport X u (γ : (VS D).V →ₗ[D.host.E] (VS D).V) hX Λ ((GlobalTheory.RowsOrb.mem_Lmap X u Λ w).1 hw)
    exact (GlobalTheory.RowsOrb.mem_Lmap X u _ _).2 h
  · intro hw'
    refine ⟨e.symm w', ?_, e.apply_symm_apply w'⟩
    have h := transport X u ((γ.symm : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) hX'
      (Formalism.HermitianLatticesTheory.gmap γ Λ) ((GlobalTheory.RowsOrb.mem_Lmap X u _ w').1 hw')
    rw [hback] at h
    exact (GlobalTheory.RowsOrb.mem_Lmap X u _ _).2 h
