import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowCharacterTimesInverseUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreePointFieldAlgebraicallyClosedStatement
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefEig

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

/- English proof (translation)
Establish `h : ActLev (Xo` using `p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (p.O i).lev2 := (p.pins i).2.act.1`. Conclude with `⟨fun g => h.total g, fun g => h.func g, h.one, fun g g' => h.mul g g', fun g => h.nat g, fun g => h.bor g⟩`.
-/
theorem actLev_levB (p : PtAt ex Csz) (i : Fin D.R.m) :
    ActLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) := by
  have h : ActLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (p.O i).lev2 := (p.pins i).2.act.1
  exact ⟨fun g => h.total g, fun g => h.func g, h.one, fun g g' => h.mul g g', fun g => h.nat g, fun g => h.bor g⟩

/- English proof (translation)
Introduce `g f hf` and use `by obtain ⟨cc, ph, hO⟩ := (hp.oneMap i).1 obtain ⟨k, hk, -⟩ := (p.pins i).2.lift.lev g exact (hO.1 g k hk f hf).1`.
-/
theorem actKeeps (p : PtAt ex Csz) (i : Fin D.R.m) (hp : p.Rows) : ActKeeps (κ := p.κ) p.O i := fun g f hf => by
  obtain ⟨cc, ph, hO⟩ := (hp.oneMap i).1
  obtain ⟨k, hk, -⟩ := (p.pins i).2.lift.lev g
  exact (hO.1 g k hk f hf).1

/- English proof (translation)
Establish `hv` using `chi_mul_psi_inv_mem_core p i hp.1 hp.2`. Use `choose b hb using hv`. Establish `hinj : Function.Injective (algebraMap p.T.Q.c.F D.what₂.LL)` using `(algebraMap p.T.Q.c.F D.what₂.LL).injective`. Establish `hb0 : ∀ u, b u ≠ 0` using `fun u h => by`. Use `hb u` as an intermediate fact.

Rewrite `this` using `[h, map_zero]`. Conclude with `Units.ne_zero _ this.symm`. Use `⟨{ toFun := fun u => Units.mk0 (b u) (hb0 u), map_one' := ?_, map_mul' := ?_ }, fun u => hb u⟩` and prove the remaining obligations. Use `Units.ext (hinj ?_)` and prove the remaining obligations. Simplify using `[hb]`.

Introduce `u v`. Use `Units.ext (hinj ?_)` and prove the remaining obligations. Simplify using `only [Units.val_mk0, Units.val_mul, map_mul, hb, Subgroup.coe_mul, MonoidHom.inv_apply]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_chi (p : PtAt ex Csz) (i : Fin D.R.m) (hp : RowsT p) :
    ∃ χ : (p.F.lv2.lvl false).P →* (p.T.Q.c.F)ˣ, ∀ u, algebraMap p.T.Q.c.F D.what₂.LL (χ u : p.T.Q.c.F) =
      (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) := by
  have hv := chi_mul_psi_inv_mem_core p i hp.1 hp.2
  choose b hb using hv
  have hinj : Function.Injective (algebraMap p.T.Q.c.F D.what₂.LL) := (algebraMap p.T.Q.c.F D.what₂.LL).injective
  have hb0 : ∀ u, b u ≠ 0 := fun u h => by
    have := hb u
    rw [h, map_zero] at this
    exact Units.ne_zero _ this.symm
  refine ⟨{ toFun := fun u => Units.mk0 (b u) (hb0 u), map_one' := ?_, map_mul' := ?_ }, fun u => hb u⟩
  · refine Units.ext (hinj ?_)
    simp [hb]
  · intro u v
    refine Units.ext (hinj ?_)
    simp only [Units.val_mk0, Units.val_mul, map_mul, hb, Subgroup.coe_mul, MonoidHom.inv_apply]
    push_cast
    ring

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Simplify using `only [eigSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]`. Both sides reduce to the same expression.
-/
theorem mem_eigSub_iff (p : PtAt ex Csz) (i : Fin D.R.m) (χ : (p.F.lv2.lvl false).P →* (p.T.Q.c.F)ˣ)
    (f : p.T.R ((i : ℕ) + 1)) :
    f ∈ eigSub (Xo := p.T.Q.Xo ((i : ℕ) + 1)) (c := p.T.Q.c)
        (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) χ ↔
      ∀ u : (p.F.lv2.lvl false).P,
        actLev p.T.Q.c (p.O i).lev2 (u : p.P.Gp) f = ((χ u : (p.T.Q.c.F)ˣ) : p.T.Q.c.F) • f := by
  simp only [eigSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]
  rfl

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M hp hi hG hW hH hF`. Take `⟨χ, hχ⟩` from `exists_chi p i hp`. Establish `hK` using `actKeeps p i hp.1`. Establish `hρ` using `(p.rhoGeo i).1 hK`. Establish `hsm : ∀ (u : (p.F.lv2.lvl false).P) (f : p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n), ((p.fw.e i (((χ u : (p.T.Q.c.F)ˣ) : p.T.Q.c.F) • f) : (p.R.FW i).WK) : Fin (p.R.nW i) → D.what₂.LL) = (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) • …` using `fun u f => by`.

Rewrite using `[LinearEquiv.map_smul, Submodule.coe_smul, ← hχ u, algebraMap_smul]`. Use `⟨(p.F.lv2.lvl false).P, inferInstance, inferInstance, fun g => (p.O i).lev2 (g : p.P.Gp), χ, actLev_levB p i, GlobalTheory.T.free_point_field_algebraically_closed p i PP A M hp hi hG hW hH hF, le_of_eq ?_⟩` and prove the remaining obligations. Establish `hAB : ((eigSub (Xo` using `p.T.Q.Xo ((i : ℕ) + 1)) (c := p.T.Q.c) (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) χ).comap (cuspW (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (p.T.U ((i : ℕ) + 1)) (Gk p i)).subtype).restrictScalars (𝓞 p.T.Q.c.F) = ((Submodule.span p.T.Q.c.F (typeK p.fw p.F.lv2 i)).comap ( …`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `(x : p.T.R ((i : ℕ) + 1)) ∈ eigSub (Xo := p.T.Q.Xo ((i : ℕ) + 1)) (c := p.T.Q.c) (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) χ ↔ (x : p.T.R ((i : ℕ) + 1)) ∈ Submodule.span p.T.Q.c.F (typeK p.fw p.F.lv2 i)`.

Establish `hx : (x : p.T.R ((i : ℕ) + 1)) ∈ p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n`. Conclude with `(cuspW_wtZ (Xo := p.T.Q.Xo ((i : ℕ) + 1)) (c := p.T.Q.c) (U := p.T.U ((i : ℕ) + 1)) (wtA (p.κ i)) (p.κ i).n).le x.2`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite `h` using `[mem_eigSub_iff]`.

Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨hx, fun u => ?_⟩` and prove the remaining obligations. Take `⟨hf', h2⟩` from `hρ (u : p.P.Gp) ⟨x, hx⟩`. Rewrite using `[← h2]`. Establish `h3 : (⟨actLev p.T.Q.c (p.O i).lev2 (u : p.P.Gp) (x : p.T.R ((i : ℕ) + 1)), hf'⟩ : p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n) = ((χ u : (p.T.Q.c.F)ˣ) : p.T.Q.c.F) • ⟨x, hx⟩` using `Subtype.ext (h u)`.

Conclude with `(congrArg (fun y => ((p.fw.e i y : (p.R.FW i).WK) : Fin (p.R.nW i) → D.what₂.LL)) h3).trans (hsm u ⟨x, hx⟩)`. Introduce `h`. Use `Submodule.span_le.2 ?_ h` and prove the remaining obligations. Introduce and unpack `f ⟨hf, hT⟩`. Rewrite using `[SetLike.mem_coe, mem_eigSub_iff]`.

Introduce `u`. Take `⟨hf', h2⟩` from `hρ (u : p.P.Gp) ⟨f, hf⟩`. Establish `h4 : (p.R.FW i).ρ (u : p.P.Gp) ((p.fw.e i ⟨f, hf⟩ : (p.R.FW i).WK) : Fin (p.R.nW i) → D.what₂.LL) = (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) • ((p.fw.e i ⟨f, hf⟩ : (p.R.FW i).WK) : Fin (p.R.nW i) → D.what₂.LL)` using `hT u`. Establish `h5 : (p.fw.e i ⟨actLev p.T.Q.c (p.O i).lev2 (u : p.P.Gp) f, hf'⟩) = p.fw.e i (((χ u : (p.T.Q.c.F)ˣ) : p.T.Q.c.F) • ⟨f, hf⟩)`. Conclude with `Subtype.ext (h2.trans (h4.trans (hsm u ⟨f, hf⟩).symm))`.

Conclude with `congrArg Subtype.val ((p.fw.e i).injective h5)`. Establish `key : eigLat (p.T.U ((i : ℕ) + 1)) (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) χ (Gk p i) = latTypeK p.fw p.F.lv2 i` using `congrArg (latW (p.T.U ((i : ℕ) + 1)) (Gk p i) ⊓ ·) hAB`. Rewrite using `[muCore, ← key]`.
-/
theorem eig_slope_le : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), RowsT p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c → ∃ (G : Type) (_ : Group G) (_ : Finite G) (lev : G → ((dat p i).La →ₗ[𝓞 D.host.E] (dat p i).La) × ((dat p i).La →ₗ[𝓞 D.host.E] (dat p i).La)) (χ : G →* (p.T.Q.c.F)ˣ), ActLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c lev ∧ FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c lev ∧ slope_sq (normW (p.T.U ((i : ℕ) + 1)) (xiR D) (p.T.V ((i : ℕ) + 1)) (p.T.dict ((i : ℕ) + 1)) (Gk p i)) (eigLat (p.T.U ((i : ℕ) + 1)) lev χ (Gk p i)) ≤ muCore p i := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M hp hi hG hW hH hF
  obtain ⟨χ, hχ⟩ := exists_chi p i hp
  have hK := actKeeps p i hp.1
  have hρ := (p.rhoGeo i).1 hK
  have hsm : ∀ (u : (p.F.lv2.lvl false).P) (f : p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n),
      ((p.fw.e i (((χ u : (p.T.Q.c.F)ˣ) : p.T.Q.c.F) • f) : (p.R.FW i).WK) : Fin (p.R.nW i) → D.what₂.LL) =
        (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) •
          ((p.fw.e i f : (p.R.FW i).WK) : Fin (p.R.nW i) → D.what₂.LL) := fun u f => by
    rw [LinearEquiv.map_smul, Submodule.coe_smul, ← hχ u, algebraMap_smul]
  refine ⟨(p.F.lv2.lvl false).P, inferInstance, inferInstance, fun g => (p.O i).lev2 (g : p.P.Gp), χ, actLev_levB p i,
    GlobalTheory.T.free_point_field_algebraically_closed p i PP A M hp hi hG hW hH hF, le_of_eq ?_⟩
  have hAB : ((eigSub (Xo := p.T.Q.Xo ((i : ℕ) + 1)) (c := p.T.Q.c)
        (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) χ).comap
        (cuspW (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (p.T.U ((i : ℕ) + 1)) (Gk p i)).subtype).restrictScalars (𝓞 p.T.Q.c.F) =
      ((Submodule.span p.T.Q.c.F (typeK p.fw p.F.lv2 i)).comap (VK p.fw i).subtype).restrictScalars (𝓞 p.T.Q.c.F) := by
    ext x
    change (x : p.T.R ((i : ℕ) + 1)) ∈ eigSub (Xo := p.T.Q.Xo ((i : ℕ) + 1)) (c := p.T.Q.c)
        (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) χ ↔
      (x : p.T.R ((i : ℕ) + 1)) ∈ Submodule.span p.T.Q.c.F (typeK p.fw p.F.lv2 i)
    have hx : (x : p.T.R ((i : ℕ) + 1)) ∈ p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n := by
      exact (cuspW_wtZ (Xo := p.T.Q.Xo ((i : ℕ) + 1)) (c := p.T.Q.c) (U := p.T.U ((i : ℕ) + 1))
        (wtA (p.κ i)) (p.κ i).n).le x.2
    constructor
    · intro h
      rw [mem_eigSub_iff] at h
      apply Submodule.subset_span
      refine ⟨hx, fun u => ?_⟩
      obtain ⟨hf', h2⟩ := hρ (u : p.P.Gp) ⟨x, hx⟩
      rw [← h2]
      have h3 : (⟨actLev p.T.Q.c (p.O i).lev2 (u : p.P.Gp) (x : p.T.R ((i : ℕ) + 1)), hf'⟩ :
          p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n) = ((χ u : (p.T.Q.c.F)ˣ) : p.T.Q.c.F) • ⟨x, hx⟩ :=
        Subtype.ext (h u)
      exact (congrArg (fun y => ((p.fw.e i y : (p.R.FW i).WK) : Fin (p.R.nW i) → D.what₂.LL)) h3).trans (hsm u ⟨x, hx⟩)
    · intro h
      refine Submodule.span_le.2 ?_ h
      rintro f ⟨hf, hT⟩
      rw [SetLike.mem_coe, mem_eigSub_iff]
      intro u
      obtain ⟨hf', h2⟩ := hρ (u : p.P.Gp) ⟨f, hf⟩
      have h4 : (p.R.FW i).ρ (u : p.P.Gp) ((p.fw.e i ⟨f, hf⟩ : (p.R.FW i).WK) : Fin (p.R.nW i) → D.what₂.LL) =
          (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) •
            ((p.fw.e i ⟨f, hf⟩ : (p.R.FW i).WK) : Fin (p.R.nW i) → D.what₂.LL) := hT u
      have h5 : (p.fw.e i ⟨actLev p.T.Q.c (p.O i).lev2 (u : p.P.Gp) f, hf'⟩) =
          p.fw.e i (((χ u : (p.T.Q.c.F)ˣ) : p.T.Q.c.F) • ⟨f, hf⟩) := by
        exact Subtype.ext (h2.trans (h4.trans (hsm u ⟨f, hf⟩).symm))
      exact congrArg Subtype.val ((p.fw.e i).injective h5)
  have key : eigLat (p.T.U ((i : ℕ) + 1)) (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) χ (Gk p i) =
      latTypeK p.fw p.F.lv2 i :=
    congrArg (latW (p.T.U ((i : ℕ) + 1)) (Gk p i) ⊓ ·) hAB
  rw [muCore, ← key]

end GlobalTheory.DefEig
