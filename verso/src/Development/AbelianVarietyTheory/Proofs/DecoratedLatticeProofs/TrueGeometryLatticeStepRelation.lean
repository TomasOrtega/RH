import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepIndexLeS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsRepsRepresentUnitaryDoubleCosetsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FixLevCompactOpen
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.LevProd

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word} {a : GeoAll W u} {t : W.P.T}

/- English proof (translation)
Set `v : Fin J.r → GlobalTheory.FinPl.Pl (I.rec7 l Z)` to `fun i => (J.G i).q.v`. Set `f : Fin J.r → Fin J.r` to `fun i => (Finset.univ.filter (fun i' => v i' = v i)).min' ⟨i, by simp⟩`. Establish `hf : ∀ i, v (f i) = v i` using `fun i => (Finset.mem_filter.1 (Finset.min'_mem (Finset.univ.filter (fun i' => v i' = v i)) ⟨i, by simp⟩)).2`. Establish `hf2 : ∀ i i', v i = v i' → f i = f i'`. Introduce `i i' h`.

Simplify using `only [f, h]`. Set `R` to `{i : Fin J.r // f i = i}`. Set `e : R ≃ Fin (Fintype.card R)` to `Fintype.equivFin R`. Set `ρ : Fin (Fintype.card R) → Fin J.r` to `fun m => (e.symm m).1`. Establish `hinj : Function.Injective fun m => (J.G (ρ m)).q.v`.

Introduce `m m' h`. Establish `h1 : f (ρ m) = f (ρ m')` using `hf2 _ _ h`. Rewrite `h1` using `[(e.symm m).2, (e.symm m').2]`. Conclude with `e.symm.injective (Subtype.ext h1)`. Take `⟨Ψ, hc, hin, -, huniq⟩` from `GlobalTheory.FixLev.exists_section ((I.rec7 l Z).sp.X j) (fun m => (J.G (ρ m)).k) (fun m => (J.G (ρ m)).q) hinj (fun _ => XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (fun m => (J.G (ρ m)).FX j (by have := step_index_le_s J (ρ m) hj; omega))`.

Establish `hP : (GlobalTheory.FinPl.grpAt ((I.rec7 l Z).sp.X j) fun p => ∃ m, p = (J.G (ρ m)).q.v) = GlobalTheory.FinPl.grpAt _ (twAt J)`. Use `congr 1`. Use function extensionality and compare the values at `p`. Apply `propext` to reduce the goal to its premises. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨m, rfl⟩`. Conclude with `⟨ρ m, rfl⟩`. Introduce and unpack `⟨i, rfl⟩`. Establish `hfix : f (f i) = f i` using `hf2 _ _ (hf i)`. Use `⟨e ⟨f i, hfix⟩, ?_⟩` and prove the remaining obligations.

Use `show v i = v (e.symm (e ⟨f i, hfix⟩)).1`. Rewrite using `[e.symm_apply_apply]`. Conclude with `(hf i).symm`. Use `⟨Fintype.card R, ρ, Ψ, hc, fun x => hP.le (hin x), fun g hg => huniq g (hP.ge hg) _ fun m => ?_⟩` and prove the remaining obligations. Conclude with `(GlobalTheory.LevIdx.eq_locHom_iff _ _ _ g _).2 rfl`.
-/
theorem exists_sec_tw (J : QJ a t) (j : ℕ) (hj : j + 2 ≤ B.R.m) :
    ∃ (n : ℕ) (ρ : Fin n → Fin J.r)
      (Ψ : (∀ m : Fin n, GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G (ρ m)).k) →
        GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)),
      Continuous Ψ ∧ (∀ x, Ψ x ∈ GlobalTheory.FinPl.grpAt _ (twAt J)) ∧
      ∀ g ∈ GlobalTheory.FinPl.grpAt _ (twAt J), Ψ (fun m => phi J j hj g (ρ m)) = g := by
  classical
  let v : Fin J.r → GlobalTheory.FinPl.Pl (I.rec7 l Z) := fun i => (J.G i).q.v
  let f : Fin J.r → Fin J.r := fun i => (Finset.univ.filter (fun i' => v i' = v i)).min' ⟨i, by simp⟩
  have hf : ∀ i, v (f i) = v i := fun i =>
    (Finset.mem_filter.1 (Finset.min'_mem (Finset.univ.filter (fun i' => v i' = v i)) ⟨i, by simp⟩)).2
  have hf2 : ∀ i i', v i = v i' → f i = f i' := by
    intro i i' h
    simp only [f, h]
  let R := {i : Fin J.r // f i = i}
  let e : R ≃ Fin (Fintype.card R) := Fintype.equivFin R
  let ρ : Fin (Fintype.card R) → Fin J.r := fun m => (e.symm m).1
  have hinj : Function.Injective fun m => (J.G (ρ m)).q.v := by
    intro m m' h
    have h1 : f (ρ m) = f (ρ m') := hf2 _ _ h
    rw [(e.symm m).2, (e.symm m').2] at h1
    exact e.symm.injective (Subtype.ext h1)
  obtain ⟨Ψ, hc, hin, -, huniq⟩ := GlobalTheory.FixLev.exists_section ((I.rec7 l Z).sp.X j)
    (fun m => (J.G (ρ m)).k) (fun m => (J.G (ρ m)).q) hinj
    (fun _ => XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j)
    (fun m => (J.G (ρ m)).FX j (by have := step_index_le_s J (ρ m) hj; omega))
  have hP : (GlobalTheory.FinPl.grpAt ((I.rec7 l Z).sp.X j) fun p => ∃ m, p = (J.G (ρ m)).q.v) =
      GlobalTheory.FinPl.grpAt _ (twAt J) := by
    congr 1
    funext p
    apply propext
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨ρ m, rfl⟩
    · rintro ⟨i, rfl⟩
      have hfix : f (f i) = f i := hf2 _ _ (hf i)
      refine ⟨e ⟨f i, hfix⟩, ?_⟩
      show v i = v (e.symm (e ⟨f i, hfix⟩)).1
      rw [e.symm_apply_apply]
      exact (hf i).symm
  refine ⟨Fintype.card R, ρ, Ψ, hc, fun x => hP.le (hin x), fun g hg => huniq g (hP.ge hg) _ fun m => ?_⟩
  exact (GlobalTheory.LevIdx.eq_locHom_iff _ _ _ g _).2 rfl

/- English proof (translation)
Establish `hU` using `(GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hW.tr.ok hW.tr.pins.some l Z u (W.P.I.tup t) J.Ch₀ J.A hR.is j (by omega) (J.ι j α)).1`. Use `haveI hNn : (GlobalTheory.FinPl.grpAt ((I.rec7 l Z).sp.X j) (twAt J)).Normal := by`. Unfold `GlobalTheory.FinPl.grpAt GlobalTheory.FinPl.congGrp`. Use `infer_instance`. Take `⟨n, ρ, Ψ, hc, hin, huniq⟩` from `exists_sec_tw J j hj`.

Set `Kp : Set ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)` to `Set.pi Set.univ fun i => (KO (J.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) : Set _)`. Establish `hKpc : IsCompact Kp` using `isCompact_univ_pi fun i => SplitFlip.isCompact_KO`. Establish `hKpcl : IsClosed Kp` using `isClosed_set_pi fun i _ => Subgroup.isClosed_of_isOpen _ SplitFlip.isOpen_KO`. Establish `hphi : Continuous (phi J j hj)` using `continuous_pi fun i => GlobalTheory.LevIdx.continuous_locHom _ _ _`. Set `C : Set ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)` to `(fun p : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) × ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) => (phi J j hj p.1)⁻¹ * p.2) '' ((J.A.U j (J.ι j α) : Set _) ×ˢ Kp)`.

Establish `hCc : IsCompact C` using `(hU.cpt.prod hKpc).image ((hphi.comp continuous_fst).inv.mul continuous_snd)`. Set `F : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) × ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)` to `fun p => p.1 * Ψ (fun m => p.2 (ρ m))`. Establish `hF : Continuous F` using `continuous_fst.mul (hc.comp (continuous_pi fun m => (continuous_apply (ρ m)).comp continuous_snd))`. Set `S` to `((J.A.U j (J.ι j α) : Set _) ×ˢ C) ∩ F ⁻¹' (phi J j hj ⁻¹' Kp)`. Establish `hSc : IsCompact S` using `(hU.cpt.prod hCc).inter_right ((hKpcl.preimage hphi).preimage hF)`.

Establish `heq : (relax J j hj α : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) = F '' S`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce `hg`. Establish `hg1` using `Subgroup.mem_inf.1 (hg : g ∈ relax J j hj α)`.

Establish `hsup : g ∈ ((J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (twAt J) : Subgroup _) : Set _)` using `(Subgroup.mem_inf.1 hg1.1).1`. Establish `hK : phi J j hj g ∈ Kp` using `Subgroup.mem_comap.1 hg1.2`. Rewrite `hsup` using `[Subgroup.mul_normal]`. Take `⟨x, hx, y, hy, rfl⟩` from `hsup`. Establish `hFy : F (x, phi J j hj y) = x * y` using `by show x * Ψ (fun m => phi J j hj y (ρ m)) = x * y`.

Rewrite using `[huniq y hy]`. Use `⟨(x, phi J j hj y), ⟨⟨hx, ⟨(x, phi J j hj (x * y)), ⟨hx, hK⟩, ?_⟩⟩, ?_⟩, hFy⟩` and prove the remaining obligations. Use `show (phi J j hj x)⁻¹ * phi J j hj (x * y) = phi J j hj y`. Rewrite using `[map_mul, inv_mul_cancel_left]`. Use `show phi J j hj (F (x, phi J j hj y)) ∈ Kp`.

Rewrite using `[hFy]`. Conclude with `hK`. Introduce and unpack `⟨⟨x, z⟩, ⟨⟨hx, -⟩, hK⟩, rfl⟩ show F (x, z) ∈ relax J j hj α`. Use `Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, Subgroup.mem_comap.2 hK⟩` and prove the remaining obligations. Conclude with `Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right (hin _))`.

Conclude with `Subgroup.mul_mem _ (hU.le hx) (GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ (hin _))`. Rewrite using `[heq]`. Conclude with `hSc.image hF`.
-/
theorem isCompact_relax (hW : AllTrue W) (J : QJ a t) (hR : J.Reads) (j : ℕ) (hj : j + 2 ≤ B.R.m) (α : J.Ch j) :
    IsCompact (relax J j hj α : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) := by
  classical
  have hU := (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hW.tr.ok hW.tr.pins.some l Z u (W.P.I.tup t) J.Ch₀ J.A hR.is j (by omega) (J.ι j α)).1
  haveI hNn : (GlobalTheory.FinPl.grpAt ((I.rec7 l Z).sp.X j) (twAt J)).Normal := by
    unfold GlobalTheory.FinPl.grpAt GlobalTheory.FinPl.congGrp
    infer_instance
  obtain ⟨n, ρ, Ψ, hc, hin, huniq⟩ := exists_sec_tw J j hj
  let Kp : Set ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) :=
    Set.pi Set.univ fun i => (KO (J.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) : Set _)
  have hKpc : IsCompact Kp := isCompact_univ_pi fun i => SplitFlip.isCompact_KO
  have hKpcl : IsClosed Kp := isClosed_set_pi fun i _ => Subgroup.isClosed_of_isOpen _ SplitFlip.isOpen_KO
  have hphi : Continuous (phi J j hj) := continuous_pi fun i => GlobalTheory.LevIdx.continuous_locHom _ _ _
  let C : Set ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) :=
    (fun p : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) × ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) =>
      (phi J j hj p.1)⁻¹ * p.2) '' ((J.A.U j (J.ι j α) : Set _) ×ˢ Kp)
  have hCc : IsCompact C := (hU.cpt.prod hKpc).image ((hphi.comp continuous_fst).inv.mul continuous_snd)
  let F : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) × ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) →
      GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) := fun p => p.1 * Ψ (fun m => p.2 (ρ m))
  have hF : Continuous F :=
    continuous_fst.mul (hc.comp (continuous_pi fun m => (continuous_apply (ρ m)).comp continuous_snd))
  let S := ((J.A.U j (J.ι j α) : Set _) ×ˢ C) ∩ F ⁻¹' (phi J j hj ⁻¹' Kp)
  have hSc : IsCompact S := (hU.cpt.prod hCc).inter_right ((hKpcl.preimage hphi).preimage hF)
  have heq : (relax J j hj α : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) = F '' S := by
    ext g
    constructor
    · intro hg
      have hg1 := Subgroup.mem_inf.1 (hg : g ∈ relax J j hj α)
      have hsup : g ∈ ((J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (twAt J) : Subgroup _) : Set _) :=
        (Subgroup.mem_inf.1 hg1.1).1
      have hK : phi J j hj g ∈ Kp := Subgroup.mem_comap.1 hg1.2
      rw [Subgroup.mul_normal] at hsup
      obtain ⟨x, hx, y, hy, rfl⟩ := hsup
      have hFy : F (x, phi J j hj y) = x * y := by
        show x * Ψ (fun m => phi J j hj y (ρ m)) = x * y
        rw [huniq y hy]
      refine ⟨(x, phi J j hj y), ⟨⟨hx, ⟨(x, phi J j hj (x * y)), ⟨hx, hK⟩, ?_⟩⟩, ?_⟩, hFy⟩
      · show (phi J j hj x)⁻¹ * phi J j hj (x * y) = phi J j hj y
        rw [map_mul, inv_mul_cancel_left]
      · show phi J j hj (F (x, phi J j hj y)) ∈ Kp
        rw [hFy]
        exact hK
    · rintro ⟨⟨x, z⟩, ⟨⟨hx, -⟩, hK⟩, rfl⟩
      show F (x, z) ∈ relax J j hj α
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, Subgroup.mem_comap.2 hK⟩
      · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right (hin _))
      · exact Subgroup.mul_mem _ (hU.le hx) (GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ (hin _))
  rw [heq]
  exact hSc.image hF

/- English proof (translation)
Introduce `B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat j hj`. Unfold `Up`. Use `split_ifs with h`. Conclude with `isCompact_relax hW _ h.choose_spec.choose_spec.1 j hj _`. Rewrite using `[Subgroup.coe_bot]`.

Conclude with `isCompact_singleton`.
-/
theorem isCompact_Up : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), IsCompact (GlobalTheory.LevProd.Up a j hj : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat j hj
  unfold Up
  split_ifs with h
  · exact isCompact_relax hW _ h.choose_spec.choose_spec.1 j hj _
  · rw [Subgroup.coe_bot]
    exact isCompact_singleton

end GlobalTheory.LevProd
end
