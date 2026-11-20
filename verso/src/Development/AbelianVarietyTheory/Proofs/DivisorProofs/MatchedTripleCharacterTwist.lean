import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleFiniteWeilIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaVanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLinePolynomialEquivariance
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

open scoped Classical

namespace GlobalTheory.ThKPolStab

open Formalism.BasicNotions.TH GlobalTheory.RealLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Establish `h1 : (1 : UA σ X.J) ∈ UAt σ X (evFin F v)`. Introduce `u _`. Use `show u • (mat (1 : UA σ X.J) - 1) = 0`. Establish `: mat (1 : UA σ X.J) = 1` using `rfl`. Rewrite using `[this, sub_self, smul_zero]`.

Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem Ψ hΨ`. Take `⟨f, hf, φ, hSB, hev, rfl⟩` from `hΨ`. Establish `hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1` using `(hev.and hP.good.std).mono fun w hw => hw.1.trans hw.2`. Take `⟨φ₁, ⟨hφ₁, hact⟩, -⟩` from `(hA F E σ B n d X W M χX χW om r s r' s' hP v).1 1 h1 h hh (φ v) (hSB v)`.

Take `⟨ρ, hρ, hρt⟩` from `GlobalTheory.PureFactor.exists_rest_factor v f φ hstd`. Establish `hpure : tens (evFin F v) (φ v) ρ = pure f φ`. Rewrite using `[hρt, Function.update_eq_self]`. Establish `hRest : Rest (evFin F v) (φ v) ρ` using `⟨hρ, by rw [hpure]; exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩`. Establish `hmap : om (1, h) (pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v φ₁)`.

Rewrite using `[← hpure, hact ρ hRest, hρt]`. Rewrite using `[hmap]`. Use `Submodule.subset_span ⟨f, hf, Function.update φ v φ₁, fun w => ?_, ?_, rfl⟩` and prove the remaining obligations. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality.

Rewrite using `[Function.update_self]`. Conclude with `hφ₁`. Rewrite using `[Function.update_of_ne hw]`. Conclude with `hSB w`. Use `filter_upwards [hev, Filter.eventually_cofinite_ne v] with w hw hne`.

Rewrite using `[Function.update_of_ne hne]`. Conclude with `hw`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem polData_stable_right (hA : ActsEx) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ X W)
    {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s') (v : Pl F)
    (h : UA σ W.J) (hh : h ∈ UAt σ W (evFin F v)) (Φ : Fn F n d) (hΦ : Φ ∈ PolData B M) :
    om (1, h) Φ ∈ PolData B M := by
  have h1 : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := by
    intro u _
    show u • (mat (1 : UA σ X.J) - 1) = 0
    have : mat (1 : UA σ X.J) = 1 := rfl
    rw [this, sub_self, smul_zero]
  induction hΦ using Submodule.span_induction with
  | mem Ψ hΨ =>
    obtain ⟨f, hf, φ, hSB, hev, rfl⟩ := hΨ
    have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
      (hev.and hP.good.std).mono fun w hw => hw.1.trans hw.2
    obtain ⟨φ₁, ⟨hφ₁, hact⟩, -⟩ :=
      (hA F E σ B n d X W M χX χW om r s r' s' hP v).1 1 h1 h hh (φ v) (hSB v)
    obtain ⟨ρ, hρ, hρt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
    have hpure : tens (evFin F v) (φ v) ρ = pure f φ := by
      rw [hρt, Function.update_eq_self]
    have hRest : Rest (evFin F v) (φ v) ρ := ⟨hρ, by rw [hpure]; exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
    have hmap : om (1, h) (pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v φ₁) := by
      rw [← hpure, hact ρ hRest, hρt]
    rw [hmap]
    refine Submodule.subset_span ⟨f, hf, Function.update φ v φ₁, fun w => ?_, ?_, rfl⟩
    · by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact hφ₁
      · rw [Function.update_of_ne hw]; exact hSB w
    · filter_upwards [hev, Filter.eventually_cofinite_ne v] with w hw hne
      rw [Function.update_of_ne hne]; exact hw
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/- English proof (translation)
Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem Ψ hΨ`. Take `⟨f, hf, φ, hSB, hev, rfl⟩` from `hΨ`. Establish `hs : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1` using `(hev.and hstd).mono fun w hw => hw.1.trans hw.2`. Take `⟨f₁, hf₁, hact⟩` from `hT f hf`.

Rewrite using `[GlobalTheory.ThetaFacInf.Fib.acts_pure φ hSB hs hact]`. Conclude with `Submodule.subset_span ⟨f₁, hf₁, φ, hSB, hev, rfl⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem polData_stable_inf {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ X W)
    (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (T : Module.End ℂ (Fn F n d))
    (hT : ∀ f ∈ M.Pol B.ψ B.emb, ∃ f₁ ∈ M.Pol B.ψ B.emb, Acts (evI F) T f f₁) (Φ : Fn F n d) (hΦ : Φ ∈ PolData B M) :
    T Φ ∈ PolData B M := by
  induction hΦ using Submodule.span_induction with
  | mem Ψ hΨ =>
    obtain ⟨f, hf, φ, hSB, hev, rfl⟩ := hΨ
    have hs : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
      (hev.and hstd).mono fun w hw => hw.1.trans hw.2
    obtain ⟨f₁, hf₁, hact⟩ := hT f hf
    rw [GlobalTheory.ThetaFacInf.Fib.acts_pure φ hSB hs hact]
    exact Submodule.subset_span ⟨f₁, hf₁, φ, hSB, hev, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/- English proof (translation)
Introduce `hK F E _ _ _ _ _ σ B a a' G X om om' h`. Take `⟨hb, hg, hc, hw, -⟩` from `h`. Use `choose A hA hAθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists _ _ _ _ _ (hg.hV.sig w) (hg.hV.cartan w)`. Use `choose C hC hCθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists _ _ _ _ _ (hg.hW.sig w) (hg.hW.cartan w)`. Establish `hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w)` using `fun w => by`.

Rewrite using `[GlobalTheory.PolStabInf.incM_map_piInf, one_smul]`. Conclude with `hA w`. Establish `hC1 : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w)` using `fun w => by`. Rewrite using `[GlobalTheory.PolStabInf.incM_map_piInf]`. Conclude with `hC w`.

Establish `fr : Framed B.emb (incM F G.V.J) (incM F G.W.J) 1 Complex.I A C` using `⟨one_mul _, hA1, hC1⟩`. Establish `hD` using `GlobalTheory.T.archHeisenbergDerivatives_exist`. Establish `hvl` using `GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hD`. Establish `hfe` using `GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hD`. Establish `hsec` using `GlobalTheory.T.lieSecond_of_prints_derEx_fockEx_vacLine_lieScalar hK.base hD hfe hvl (GlobalTheory.T.lieScalar_of_prints_derEx_vacLine hK.base hD hvl)`.

Establish `hfst` using `GlobalTheory.T.lieFirst_of_lieSecond' hsec`. Take `⟨Φ, hΦ⟩` from `hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C hb.cm hb.std fr`. Establish `hr` using `GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws GlobalTheory.RealLift.actsLaws hD hvl F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ`. Establish `hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om` using `hw`. Take `⟨d, hd, hB1⟩` from `hwp.2.1`.

Establish `hW1` using `hfst F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co d 1 Complex.I A C Φ _ _ _ hb.cm hb.std fr hΦ hd hB1 (GlobalTheory.PolStabInf.hasExp_div B.emb hc.expβ hc.expα)`. Establish `hadm` using `fun g => (hwp.isUSplitting).adm g`. Establish `hL` using `GlobalTheory.RealLift.actsLaws`. Establish `mem : ∀ T, Φ T ∈ G.M.Pol B.ψ B.emb` using `fun T => hr ▸ LinearMap.mem_range_self Φ T`. Establish `pol : ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ T, f = Φ T` using `fun f hf => by`.

Rewrite `hf` using `[← hr]`. Take `⟨T, rfl⟩` from `hf`. Conclude with `⟨T, rfl⟩`. Introduce `k hk f hf`. Take `⟨T, rfl⟩` from `pol f hf`.

Take `⟨γ, hγ, Yg, hgen, hKC, hγ1⟩` from `GlobalTheory.RealLift.kLine_of_lineEx GlobalTheory.RealLift.exists_line_of_upq F E σ (Fin a) _ _ B.emb (incM F G.V.J) 1 A G.V.θ hb.cm hA1 hAθ k hk.1 hk.2`. Take `⟨U, -, hSA⟩` from `GlobalTheory.ExpAct.expAct_fock F _ _ Φ _ ((om.comp (MonoidHom.inl _ _)).comp γ) (GlobalTheory.RealLift.locFin_sumPl _ _ _ fun w => GlobalTheory.PolStabInf.locFin_fock1 _ _ _ _ (Yg w) (hKC w) _) (fun t l hl => hadm _ l hl) (fun T => hW1 γ hγ Yg hgen T)`. Establish `h2` using `(hL F _ (Φ T) (Φ (U T)) (Φ (U T))).2.1 _ (map_zero _) (hSA T)`. Rewrite `h2` using `[MonoidHom.comp_apply, hγ1]`. Conclude with `⟨_, mem _, h2⟩`.
-/
theorem kInfV_exists : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∀ k ∈ KInf σ G.V B.emb, ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ f₁ ∈ G.M.Pol B.ψ B.emb, Acts (evI F) (om (k, 1)) f f₁ := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' h
  obtain ⟨hb, hg, hc, hw, -⟩ := h
  choose A hA hAθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists _ _ _ _ _ (hg.hV.sig w) (hg.hV.cartan w)
  choose C hC hCθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists _ _ _ _ _ (hg.hW.sig w) (hg.hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [GlobalTheory.PolStabInf.incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [GlobalTheory.PolStabInf.incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F G.V.J) (incM F G.W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have hD := GlobalTheory.T.archHeisenbergDerivatives_exist
  have hvl := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hD
  have hfe := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hD
  have hsec := GlobalTheory.T.lieSecond_of_prints_derEx_fockEx_vacLine_lieScalar hK.base hD hfe hvl (GlobalTheory.T.lieScalar_of_prints_derEx_vacLine hK.base hD hvl)
  have hfst := GlobalTheory.T.lieFirst_of_lieSecond' hsec
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws GlobalTheory.RealLift.actsLaws hD hvl F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr
    hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hw
  obtain ⟨d, hd, hB1⟩ := hwp.2.1
  have hW1 := hfst F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co d 1 Complex.I A C Φ _ _ _ hb.cm hb.std fr hΦ hd hB1
    (GlobalTheory.PolStabInf.hasExp_div B.emb hc.expβ hc.expα)
  have hadm := fun g => (hwp.isUSplitting).adm g
  have hL := GlobalTheory.RealLift.actsLaws
  have mem : ∀ T, Φ T ∈ G.M.Pol B.ψ B.emb := fun T => hr ▸ LinearMap.mem_range_self Φ T
  have pol : ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ T, f = Φ T := fun f hf => by
    rw [← hr] at hf
    obtain ⟨T, rfl⟩ := hf
    exact ⟨T, rfl⟩
  intro k hk f hf
  obtain ⟨T, rfl⟩ := pol f hf
  obtain ⟨γ, hγ, Yg, hgen, hKC, hγ1⟩ := GlobalTheory.RealLift.kLine_of_lineEx GlobalTheory.RealLift.exists_line_of_upq F E σ (Fin a) _ _
    B.emb (incM F G.V.J) 1 A G.V.θ hb.cm hA1 hAθ k hk.1 hk.2
  obtain ⟨U, -, hSA⟩ := GlobalTheory.ExpAct.expAct_fock F _ _ Φ _ ((om.comp (MonoidHom.inl _ _)).comp γ)
    (GlobalTheory.RealLift.locFin_sumPl _ _ _ fun w => GlobalTheory.PolStabInf.locFin_fock1 _ _ _ _ (Yg w) (hKC w) _)
    (fun t l hl => hadm _ l hl) (fun T => hW1 γ hγ Yg hgen T)
  have h2 := (hL F _ (Φ T) (Φ (U T)) (Φ (U T))).2.1 _ (map_zero _) (hSA T)
  rw [MonoidHom.comp_apply, hγ1] at h2
  exact ⟨_, mem _, h2⟩

/- English proof (translation)
Introduce `hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM Φ hΦ`. Establish `hT` using `hM.triple`. Establish `hV : IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q)` using `{ base := hT.base, herm := hT.geo.hV, skew := hT.geo.hW, good := hT.geo.hM, hX := hT.chars.heckeβ, hW := GlobalTheory.ThKRatInv.isHecke_div hT.chars.heckeβ hT.chars.heckeα, resX := hT.chars.resβ, resW := GlobalTheory.ThKRatInv.resEtaPow_div hT.chars.resβ hT.chars.resα, weil := hT …`. Establish `hA` using `GlobalTheory.T.theta_action_exists hK.base`. Establish `hstd` using `hT.geo.hM.std`.

Take `⟨-, -, -, hP4⟩` from `GlobalTheory.T.real_line_polynomial_equivariance hK F E σ B a a' G X om om' hT`. Use `⟨fun v g hg => GlobalTheory.ThKPolFinV.polData_stable_left hA B G.M hV v g hg Φ hΦ, fun k hk => ?_, fun v h hh => polData_stable_right hA B G.M hV v h hh Φ hΦ, fun k hk => ?_⟩` and prove the remaining obligations. Conclude with `polData_stable_inf B G.M hstd (om (k, 1)) (kInfV_exists hK F E σ B a a' G X om om' hT k hk) Φ hΦ`. Use `polData_stable_inf B G.M hstd (om (1, k)) (fun f hf => ?_) Φ hΦ` and prove the remaining obligations. Take `⟨f₁, hf₁, hact, -⟩` from `hP4 k hk f hf`.

Conclude with `⟨f₁, hf₁, hact⟩`.
-/
theorem stab : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, (∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, ∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.V (GlobalTheory.AdelicU.evFin F v), om (g, 1) Φ ∈ GlobalTheory.ThK.PolData B G.M) ∧ (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.V B.emb, om (k, 1) Φ ∈ GlobalTheory.ThK.PolData B G.M) ∧ (∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v), om (1, h) Φ ∈ GlobalTheory.ThK.PolData B G.M) ∧ ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.W B.emb, om (1, k) Φ ∈ GlobalTheory.ThK.PolData B G.M := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM Φ hΦ
  have hT := hM.triple
  have hV : IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
    { base := hT.base, herm := hT.geo.hV, skew := hT.geo.hW, good := hT.geo.hM, hX := hT.chars.heckeβ,
      hW := GlobalTheory.ThKRatInv.isHecke_div hT.chars.heckeβ hT.chars.heckeα,
      resX := hT.chars.resβ, resW := GlobalTheory.ThKRatInv.resEtaPow_div hT.chars.resβ hT.chars.resα, weil := hT.weil }
  have hA := GlobalTheory.T.theta_action_exists hK.base
  have hstd := hT.geo.hM.std
  obtain ⟨-, -, -, hP4⟩ := GlobalTheory.T.real_line_polynomial_equivariance hK F E σ B a a' G X om om' hT
  refine ⟨fun v g hg => GlobalTheory.ThKPolFinV.polData_stable_left hA B G.M hV v g hg Φ hΦ, fun k hk => ?_,
    fun v h hh => polData_stable_right hA B G.M hV v h hh Φ hΦ, fun k hk => ?_⟩
  · exact polData_stable_inf B G.M hstd (om (k, 1)) (kInfV_exists hK F E σ B a a' G X om om' hT k hk) Φ hΦ
  · refine polData_stable_inf B G.M hstd (om (1, k)) (fun f hf => ?_) Φ hΦ
    obtain ⟨f₁, hf₁, hact, -⟩ := hP4 k hk f hf
    exact ⟨f₁, hf₁, hact⟩

end GlobalTheory.ThKPolStab

end
