import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfRationalUnitaryAdelicMulStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousPf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveCompactLevelInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoordsStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownLevelPrimeAdelicFactorisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastAllTranspose
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastGroupEmbeddingRealComponentsBlockForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.AdForm.EvzDecomp

/- English proof (translation)
Establish `h : Formalism.UG.cT s (g : Matrix n n A) * J * (g : Matrix n n A) = J` using `hg`. Use `show Formalism.UG.cT s' ((g : Matrix n n A).map φ) * J.map φ * (g : Matrix n n A).map φ = J.map φ`. Establish `e : Formalism.UG.cT s' ((g : Matrix n n A).map φ) = (Formalism.UG.cT s (g : Matrix n n A)).map φ`. Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, hs]`.

Rewrite using `[e, ← Matrix.map_mul, ← Matrix.map_mul, h]`.
-/
theorem bc_mem_UJ' {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n] (φ : A →+* B) (s : A →+* A)
    (s' : B →+* B) (hs : ∀ a, φ (s a) = s' (φ a)) (J : Matrix n n A) {g : GL n A} (hg : g ∈ Formalism.UG.UJ s J) :
    Formalism.UG.bc φ g ∈ Formalism.UG.UJ s' (J.map φ) := by
  have h : Formalism.UG.cT s (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  show Formalism.UG.cT s' ((g : Matrix n n A).map φ) * J.map φ * (g : Matrix n n A).map φ = J.map φ
  have e : Formalism.UG.cT s' ((g : Matrix n n A).map φ) = (Formalism.UG.cT s (g : Matrix n n A)).map φ := by
    ext i j; simp [Formalism.UG.cT, hs]
  rw [e, ← Matrix.map_mul, ← Matrix.map_mul, h]

/- English proof (translation)
Substitute `hn` using the available equality. Rewrite using `[GlobalTheory.AdForm.RdLaw.finM_rfl]`. Establish `e : Formalism.L2.Theta.mt V (1 : GA D V) = 1`. Use `GlobalTheory.AdForm.RdLaw.mt_mul V 1 1` as an intermediate fact. Simplify using `using this`.

Rewrite using `[e, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem finM_one' {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) : finM V hn (1 : GA D V) = 1 := by
  subst hn
  rw [GlobalTheory.AdForm.RdLaw.finM_rfl]
  have e : Formalism.L2.Theta.mt V (1 : GA D V) = 1 := by
    have := GlobalTheory.AdForm.RdLaw.mt_mul V 1 1
    simpa using this
  rw [e, Matrix.map_one _ (map_zero _) (map_one _)]

/- English proof (translation)
Substitute `hn` using the available equality. Conclude with `GlobalTheory.AdForm.RdLaw.finM_pf V g`.
-/
theorem finM_pf' {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) :
    finM V hn (GlobalTheory.AdForm.RdLaw.pf V g) = finM V hn g := by
  subst hn; exact GlobalTheory.AdForm.RdLaw.finM_pf V g

/- English proof (translation)
Substitute `hn` using the available equality. Conclude with `GlobalTheory.AdForm.RdLaw.infM_mul θ V g h τ`.
-/
theorem infM_mul' {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (g h : GA D V) (τ : D.what₂.Tau) :
    infM θ V hn (g * h) τ = infM θ V hn g τ * infM θ V hn h τ := by
  subst hn; exact GlobalTheory.AdForm.RdLaw.infM_mul θ V g h τ

/- English proof (translation)
Substitute `hn` using the available equality. Rewrite `hk` using `[GlobalTheory.AdForm.RdLaw.finM_rfl]`. Establish `e : (Formalism.L2.Theta.mt V k).map (toEAf D) = (finHom V k).val.map (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E)` using `rfl`. Rewrite `hk` using `[e]`. Use `show finHom V k = 1`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_one]`. Use extensionality with `i j`. Use `congrFun (congrFun hk i) j` as an intermediate fact. Simplify using `only [Matrix.map_apply] at this`.

Establish `h3` using `congrArg (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm this`. Rewrite `h3` using `[AlgEquiv.symm_apply_apply]`. Rewrite using `[h3, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem mem_GinfC_of_finM {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (k : GA D V) (hk : finM V hn k = 1) :
    k ∈ GinfC V := by
  subst hn
  rw [GlobalTheory.AdForm.RdLaw.finM_rfl] at hk
  have e : (Formalism.L2.Theta.mt V k).map (toEAf D) = (finHom V k).val.map
      (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) := rfl
  rw [e] at hk
  show finHom V k = 1
  apply Units.ext
  rw [Units.val_one]
  ext i j
  have := congrFun (congrFun hk i) j
  simp only [Matrix.map_apply] at this
  have h3 := congrArg (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm this
  rw [AlgEquiv.symm_apply_apply] at h3
  rw [h3, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Substitute `hN hA` using the available equality. Use extensionality with `i j`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun a => ?_) i <;> refine Fin.lastCases ?_ (fun b => ?_) j`. Rewrite using `[Matrix.one_apply_eq]`. Conclude with `h.2.2`.

Rewrite using `[Matrix.one_apply_ne (Fin.castSucc_lt_last b).ne']`. Conclude with `(h.2.1 b).2`. Rewrite using `[Matrix.one_apply_ne (Fin.castSucc_lt_last a).ne]`. Conclude with `(h.2.1 a).1`. Establish `e` using `h.1 a b`.

Establish `e2 : G (Fin.castSucc a) (Fin.castSucc b) = (1 : Matrix (Fin n) (Fin n) R) a b` using `e`. Rewrite using `[e2]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[Matrix.one_apply_ne hab, Matrix.one_apply_ne (fun h => hab (Fin.castSucc_injective _ h))]`.
-/
theorem isBlock_one {R : Type} [Zero R] [One R] {N n : ℕ} (hN : N = n + 1) {G : Matrix (Fin N) (Fin N) R}
    {A : Matrix (Fin n) (Fin n) R} (h : GlobalTheory.BranchFormula.IsBlock hN G A 1) (hA : A = 1) : G = 1 := by
  subst hN hA
  ext i j
  refine Fin.lastCases ?_ (fun a => ?_) i <;> refine Fin.lastCases ?_ (fun b => ?_) j
  · rw [Matrix.one_apply_eq]; exact h.2.2
  · rw [Matrix.one_apply_ne (Fin.castSucc_lt_last b).ne']; exact (h.2.1 b).2
  · rw [Matrix.one_apply_ne (Fin.castSucc_lt_last a).ne]; exact (h.2.1 a).1
  · have e := h.1 a b
    have e2 : G (Fin.castSucc a) (Fin.castSucc b) = (1 : Matrix (Fin n) (Fin n) R) a b := e
    rw [e2]
    by_cases hab : a = b
    · subst hab; simp
    · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne (fun h => hab (Fin.castSucc_injective _ h))]

/- English proof (translation)
Substitute `hn` using the available equality. Establish `hG' : V.gram = 1` using `by simpa using hG`. Establish `hmem : Formalism.UG.bc (incA D) γ₀ ∈ HR (AF D.host.F) D.sp.cm.sig V.gram`. Use `bc_mem_UJ' (incA D) (D.sp.cm.sig : D.host.E →+* D.host.E) (sigR (AF D.host.F) D.sp.cm.sig) (fun x => ?_) 1 hγ` as an intermediate fact. Rewrite using `[hG']`.

Establish `e1 : (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D) = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`. Use `show Formalism.UG.bc (incA D) γ₀ ∈ Formalism.UG.UJ _ ((1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map _)`. Conclude with `this`. Use `show sigR (AF D.host.F) D.sp.cm.sig (1 ⊗ₜ x) = _`. Simplify using `[sigR]`.

Both sides reduce to the same expression. Set `γ : GA D V` to `⟨_, hmem⟩`. Establish `hmt : Formalism.L2.Theta.mt V γ = (γ₀ : Matrix _ _ _).map (incA D)` using `rfl`. Establish `hmt' : Formalism.L2.Theta.mt V γ⁻¹ = ((γ₀⁻¹ : GL (Fin V.rank) D.host.E) : Matrix _ _ _).map (incA D)` using `rfl`. Use `⟨γ, ?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `Subgroup.mem_subgroupOf.2 (Subgroup.mem_map_of_mem _ (hG' ▸ hγ))`. Conclude with `GlobalTheory.AdForm.RdLaw.rat_finM V γ₀ γ hmt`. Introduce `τ`. Conclude with `GlobalTheory.AdForm.RdLaw.rat_infM θ hθ V γ₀⁻¹ γ⁻¹ hmt' τ`.
-/
theorem ratPt {D : D7} (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) {n : ℕ} (hn : V.rank = n)
    (hG : V.gram.reindex (finCongr hn) (finCongr hn) = 1) (γ₀ : GL (Fin n) D.host.E)
    (hγ : γ₀ ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) 1) :
    ∃ γ ∈ GQ V, finM V hn γ = (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ₀).1 ∧
      ∀ τ, infM θ V hn γ⁻¹ τ = atInf (Formalism.L2.Forms.embT D) ((γ₀⁻¹ : GL (Fin n) D.host.E) : Matrix _ _ _) τ := by
  subst hn
  have hG' : V.gram = 1 := by simpa using hG
  have hmem : Formalism.UG.bc (incA D) γ₀ ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    have := bc_mem_UJ' (incA D) (D.sp.cm.sig : D.host.E →+* D.host.E) (sigR (AF D.host.F) D.sp.cm.sig) (fun x => ?_) 1 hγ
    · rw [hG']
      have e1 : (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
      show Formalism.UG.bc (incA D) γ₀ ∈ Formalism.UG.UJ _ ((1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map _)
      exact this
    · show sigR (AF D.host.F) D.sp.cm.sig (1 ⊗ₜ x) = _
      simp [sigR]
      rfl
  let γ : GA D V := ⟨_, hmem⟩
  have hmt : Formalism.L2.Theta.mt V γ = (γ₀ : Matrix _ _ _).map (incA D) := rfl
  have hmt' : Formalism.L2.Theta.mt V γ⁻¹ = ((γ₀⁻¹ : GL (Fin V.rank) D.host.E) : Matrix _ _ _).map (incA D) := rfl
  refine ⟨γ, ?_, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_map_of_mem _ (hG' ▸ hγ))
  · exact GlobalTheory.AdForm.RdLaw.rat_finM V γ₀ γ hmt
  · intro τ
    exact GlobalTheory.AdForm.RdLaw.rat_infM θ hθ V γ₀⁻¹ γ⁻¹ hmt' τ

/- English proof (translation)
Substitute `hn` using the available equality. Conclude with `GlobalTheory.AdForm.RdLaw.infM_fin θ V k hk τ`.
-/
theorem infM_fin'' {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (k : GA D V) (hk : k ∈ GfC V)
    (τ : D.what₂.Tau) : infM θ V hn k τ = 1 := by
  subst hn
  exact GlobalTheory.AdForm.RdLaw.infM_fin θ V k hk τ

/- English proof (translation)
Introduce `B X I hOk hPins l Z u emb hEmb h y hM`. Take `⟨e1, e2⟩` from `hEmb h`. Establish `hinc : (toEAf (I.rec7 l Z)).comp (incA (I.rec7 l Z)) = Formalism.UG.inclE (F` using `(I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) := by`. Use extensionality with `x`. Use `show (Algebra.TensorProduct.comm _ _ _) (finPart (I.rec7 l Z) (1 ⊗ₜ x)) = x ⊗ₜ 1`.

Establish `: finPart (I.rec7 l Z) (1 ⊗ₜ x) = (1 : Af (I.rec7 l Z).host.F) ⊗ₜ x` using `by show Algebra.TensorProduct.map _ _ (1 ⊗ₜ x) = _`. Rewrite using `[Algebra.TensorProduct.map_tmul, map_one]`. Both sides reduce to the same expression. Rewrite using `[this]`. Both sides reduce to the same expression.

Establish `hy : y.1 = ((Formalism.L2.Theta.mt _ h).map (toEAf (I.rec7 l Z))).reindex (finCongr (rankP (I.rec7 l Z))) (finCongr (rankP (I.rec7 l Z)))`. Use extensionality with `i j`. Use `hM.2 ((finCongr (rankP (I.rec7 l Z))).symm i) ((finCongr (rankP (I.rec7 l Z))).symm j)` as an intermediate fact. Simplify using `only [Equiv.apply_symm_apply] at this`. Rewrite using `[← this]`.

Both sides reduce to the same expression. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h3` using `congrArg (fun M => Matrix.map M (toEAf (I.rec7 l Z))) e1`. Simplify using `only [Matrix.map_mul, Matrix.map_map] at h3`. Rewrite using `[hy, ← hinc]`.

Conclude with `h3`. Use function extensionality and compare the values at `i`. Establish `h3` using `congrArg (toEAf (I.rec7 l Z)) (congrFun e2 i)`. Rewrite `h3` using `[RingHom.map_mulVec]`. Rewrite using `[← hinc]`.

Conclude with `h3`.
-/
theorem ext_finM_emb : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (emb : GA (I.rec7 l Z) (I.rec7 l Z).sp.X' →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X B.R.m)), IsEmbTop (D := (I.rec7 l Z)) (TC.z0 X u) emb → ∀ (h : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') (y : GL (Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)), GlobalTheory.Core.Rk.Top.HasMat h y → IsExt (I.rec7 l Z) (TC.z0 X u) (Formalism.UG.inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) y.1 (finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) (emb h)) := by
  intro B X I hOk hPins l Z u emb hEmb h y hM
  obtain ⟨e1, e2⟩ := hEmb h
  have hinc : (toEAf (I.rec7 l Z)).comp (incA (I.rec7 l Z)) =
      Formalism.UG.inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) := by
    ext x
    show (Algebra.TensorProduct.comm _ _ _) (finPart (I.rec7 l Z) (1 ⊗ₜ x)) = x ⊗ₜ 1
    have : finPart (I.rec7 l Z) (1 ⊗ₜ x) = (1 : Af (I.rec7 l Z).host.F) ⊗ₜ x := by
      show Algebra.TensorProduct.map _ _ (1 ⊗ₜ x) = _
      rw [Algebra.TensorProduct.map_tmul, map_one]; rfl
    rw [this]; rfl
  have hy : y.1 = ((Formalism.L2.Theta.mt _ h).map (toEAf (I.rec7 l Z))).reindex (finCongr (rankP (I.rec7 l Z)))
      (finCongr (rankP (I.rec7 l Z))) := by
    ext i j
    have := hM.2 ((finCongr (rankP (I.rec7 l Z))).symm i) ((finCongr (rankP (I.rec7 l Z))).symm j)
    simp only [Equiv.apply_symm_apply] at this
    rw [← this]; rfl
  refine ⟨?_, ?_⟩
  · have h3 := congrArg (fun M => Matrix.map M (toEAf (I.rec7 l Z))) e1
    simp only [Matrix.map_mul, Matrix.map_map] at h3
    rw [hy, ← hinc]
    exact h3
  · funext i
    have h3 := congrArg (toEAf (I.rec7 l Z)) (congrFun e2 i)
    rw [RingHom.map_mulVec] at h3
    rw [← hinc]
    exact h3

/- English proof (translation)
Introduce `B X I hOk hPins l Z u a Ch₀ A hA bad K hRP c g hg`. Establish `R` using `hA.reads B.R.m le_rfl`. Establish `hTop` using `hA.top (A.chOf B.R.m ((I.perIn u a).tilC c))`. Establish `h1` using `hTop ((I.stX a).rep c).1.1 (K.y c).1 g (hRP.pt c) hg`. Establish `hmv` using `(I.stp u a B.R.m).mv_smul (I.perIn u a).b0 ((I.perIn u a).tilPt c)`.

Establish `h2` using `GlobalTheory.T.isPointOf_rational_unitary_adelic_mul _ _ B.sp.cm _ _ _ _ ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)).1⁻¹ _ _ h1`. Use `set g₀ := (I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c) with hg₀`. Set `κ' : (I.stp u a B.R.m).G (I.perIn u a).b0` to `((1 : Formalism.L2.Col.UF B.fields.E (B.R.N B.R.m)), g₀.2)`. Establish `hgam1 : (I.stp u a B.R.m).gam (I.perIn u a).b0 κ' = 1` using `by show Formalism.L2.Col.ufGL _ _ (1 : Formalism.L2.Col.UF B.fields.E (B.R.N B.R.m)) = 1`. Simplify using the standard rewrite rules.

Establish `hq : ((g₀.1⁻¹, 1, 1) : Formalism.L2.Col.UF B.fields.E (B.R.N B.R.m) × Formalism.L2.Col.GLG B.fields.E (B.R.N B.R.m) (B.primes X).vGs × Formalism.L2.Col.GLQ B.fields.E (B.R.N B.R.m) (Formalism.L2.Col.QE I.sel ↑(I.tup a))) • (tilF I.sel (I.tup a) u ((I.stX a).rep c).1.1) = ((I.stp …`. Establish `e0 : (tilF I.sel (I.tup a) u ((I.stX a).rep c).1.1) = ((I.perIn u a).tilPt c).1.1` using `rfl`. Rewrite using `[e0, ← hmv]`. Use `show _ = Formalism.L2.Col.FrmG.incl _ _ κ' • _`. Use `show _ • (Formalism.L2.Col.FrmG.incl _ _ g₀ • _) = _`.

Rewrite using `[smul_smul]`. Use `congr 1`. Use `ext1`. Simplify using `[κ', Formalism.L2.Col.FrmG.incl]`. Apply the tactic sequence `ext1 <;> simp [κ', Formalism.L2.Col.FrmG.incl]`.

Establish `hr : ratAd B.host.F g₀.1⁻¹ = (ratAd B.host.F g₀.1)⁻¹` using `by show Formalism.UG.bc _ (Formalism.L2.Col.ufGL _ _ g₀.1⁻¹) = (Formalism.UG.bc _ (Formalism.L2.Col.ufGL _ _ g₀.1))⁻¹`. Rewrite using `[map_inv, map_inv]`. Use `set Y : TC.GA B (B.R.N B.R.m) := (show TC.GA B (B.R.N B.R.m) from ((A.K B.R.m le_rfl (A.chOf B.R.m ((I.perIn u a).tilC c))).y ⟨(I.perIn u a).tilC c, rfl⟩).1) with hY`. Establish `hpt : TC.PtOf (Y * (Y⁻¹ * (ratAd B.host.F g₀.1)⁻¹ * g) * A.kb B.R.m (A.chOf B.R.m ((I.perIn u a).tilC c))) ((I.stp u a B.R.m).act (I.perIn u a).b0 κ' ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c))).1.1`. Rewrite using `[← hq]`.

Establish `e : Y * (Y⁻¹ * (ratAd B.host.F g₀.1)⁻¹ * g) * A.kb B.R.m (A.chOf B.R.m ((I.perIn u a).tilC c)) = ratAd B.host.F g₀.1⁻¹ * (g * A.kb B.R.m (A.chOf B.R.m ((I.perIn u a).tilC c)))`. Rewrite using `[hr]`. Use `group`. Rewrite using `[e]`. Conclude with `h2`.

Establish `hcos` using `GlobalTheory.Mem.Col2.ChEx.cos_of_neT I (u := u) (a := a) (i := B.R.m) (by omega) ((I.stp u a B.R.m).act (I.perIn u a).b0 κ' ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c))) ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c))`. Establish `hxU` using `(R.lev ((I.perIn u a).tilC c) (Y⁻¹ * (ratAd B.host.F g₀.1)⁻¹ * g) _ hpt).2 ⟨κ', hgam1, rfl, hcos⟩`. Use `⟨⟨_, hxU⟩, rfl, ?_⟩` and prove the remaining obligations. Conclude with `R.chr ((I.perIn u a).tilC c) ⟨_, hxU⟩ κ' hgam1 hpt`.
-/
theorem top_lev_chi : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀), A.Is → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∀ c (g : TC.GA B (B.R.N B.R.m)), IsExt (I.rec7 l Z) (TC.z0 X u) (Formalism.UG.inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) (K.y c).1.1 g.1 → ∃ κ : (A.K B.R.m le_rfl (A.chOf B.R.m ((I.perIn u a).tilC c))).lev.U, (show TC.GA B (B.R.N B.R.m) from κ.1) = (show TC.GA B (B.R.N B.R.m) from ((A.K B.R.m le_rfl (A.chOf B.R.m ((I.perIn u a).tilC c))).y ⟨(I.perIn u a).tilC c, rfl⟩).1)⁻¹ * (ratAd B.host.F ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)).1)⁻¹ * g ∧ (((A.K B.R.m le_rfl (A.chOf B.R.m ((I.perIn u a).tilC c))).lev.chi κ : ℂˣ) : ℂ) = B.embLL (((I.stp u a B.R.m).chr (I.perIn u a).b0 ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)) : B.LLˣ) : B.LL) := by
  intro B X I hOk hPins l Z u a Ch₀ A hA bad K hRP c g hg
  have R := hA.reads B.R.m le_rfl
  have hTop := hA.top (A.chOf B.R.m ((I.perIn u a).tilC c))
  have h1 := hTop ((I.stX a).rep c).1.1 (K.y c).1 g (hRP.pt c) hg
  have hmv := (I.stp u a B.R.m).mv_smul (I.perIn u a).b0 ((I.perIn u a).tilPt c)
  have h2 := GlobalTheory.T.isPointOf_rational_unitary_adelic_mul _ _ B.sp.cm _ _ _ _ ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)).1⁻¹ _ _ h1
  set g₀ := (I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c) with hg₀
  let κ' : (I.stp u a B.R.m).G (I.perIn u a).b0 := ((1 : Formalism.L2.Col.UF B.fields.E (B.R.N B.R.m)), g₀.2)
  have hgam1 : (I.stp u a B.R.m).gam (I.perIn u a).b0 κ' = 1 := by
    show Formalism.L2.Col.ufGL _ _ (1 : Formalism.L2.Col.UF B.fields.E (B.R.N B.R.m)) = 1
    simp
  have hq : ((g₀.1⁻¹, 1, 1) : Formalism.L2.Col.UF B.fields.E (B.R.N B.R.m) × Formalism.L2.Col.GLG B.fields.E (B.R.N B.R.m) (B.primes X).vGs × Formalism.L2.Col.GLQ B.fields.E (B.R.N B.R.m) (Formalism.L2.Col.QE I.sel ↑(I.tup a))) • (tilF I.sel (I.tup a) u ((I.stX a).rep c).1.1) =
      ((I.stp u a B.R.m).act (I.perIn u a).b0 κ' ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c))).1.1 := by
    have e0 : (tilF I.sel (I.tup a) u ((I.stX a).rep c).1.1) = ((I.perIn u a).tilPt c).1.1 := rfl
    rw [e0, ← hmv]
    show _ = Formalism.L2.Col.FrmG.incl _ _ κ' • _
    show _ • (Formalism.L2.Col.FrmG.incl _ _ g₀ • _) = _
    rw [smul_smul]
    congr 1
    ext1
    · simp [κ', Formalism.L2.Col.FrmG.incl]
    · ext1 <;> simp [κ', Formalism.L2.Col.FrmG.incl]
  have hr : ratAd B.host.F g₀.1⁻¹ = (ratAd B.host.F g₀.1)⁻¹ := by
    show Formalism.UG.bc _ (Formalism.L2.Col.ufGL _ _ g₀.1⁻¹) = (Formalism.UG.bc _ (Formalism.L2.Col.ufGL _ _ g₀.1))⁻¹
    rw [map_inv, map_inv]
  set Y : TC.GA B (B.R.N B.R.m) := (show TC.GA B (B.R.N B.R.m) from
    ((A.K B.R.m le_rfl (A.chOf B.R.m ((I.perIn u a).tilC c))).y ⟨(I.perIn u a).tilC c, rfl⟩).1) with hY
  have hpt : TC.PtOf (Y * (Y⁻¹ * (ratAd B.host.F g₀.1)⁻¹ * g) * A.kb B.R.m (A.chOf B.R.m ((I.perIn u a).tilC c)))
      ((I.stp u a B.R.m).act (I.perIn u a).b0 κ' ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c))).1.1 := by
    rw [← hq]
    have e : Y * (Y⁻¹ * (ratAd B.host.F g₀.1)⁻¹ * g) * A.kb B.R.m (A.chOf B.R.m ((I.perIn u a).tilC c)) =
        ratAd B.host.F g₀.1⁻¹ * (g * A.kb B.R.m (A.chOf B.R.m ((I.perIn u a).tilC c))) := by
      rw [hr]; group
    rw [e]
    exact h2
  have hcos := GlobalTheory.Mem.Col2.ChEx.cos_of_neT I (u := u) (a := a) (i := B.R.m) (by omega)
    ((I.stp u a B.R.m).act (I.perIn u a).b0 κ' ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c)))
    ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c))
  have hxU := (R.lev ((I.perIn u a).tilC c) (Y⁻¹ * (ratAd B.host.F g₀.1)⁻¹ * g) _ hpt).2 ⟨κ', hgam1, rfl, hcos⟩
  refine ⟨⟨_, hxU⟩, rfl, ?_⟩
  exact R.chr ((I.perIn u a).tilC c) ⟨_, hxU⟩ κ' hgam1 hpt

end GlobalTheory.AdForm.EvzDecomp

open GlobalTheory.AdForm.EvzDecomp in

/- English proof (translation)
Introduce `B X I hOk hPins l Z u a Ch₀ A hA θ hθ emb hEmb bad K hRP c h hM`. Establish `hExt` using `ext_finM_emb I hOk hPins l Z u emb hEmb h (K.y c).1 hM`. Establish `hinvM : ∀ x : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X B.R.m), finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) x * finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) x⁻¹ = 1` using `fun x => by`. Rewrite using `[← GlobalTheory.AdForm.StabMove.finM_mul, mul_inv_cancel, finM_one']`. Establish `hinvM' : ∀ x : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X B.R.m), finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) x⁻¹ * finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) x = 1` using `fun x => by`.

Rewrite using `[← GlobalTheory.AdForm.StabMove.finM_mul, inv_mul_cancel, finM_one']`. Set `gU : TC.GA B (B.R.N B.R.m)` to `⟨finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) (emb h), finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) (emb h)⁻¹, hinvM _, hinvM' _⟩`. Take `⟨κ0, hκ0, hχ0⟩` from `top_lev_chi I hOk hPins l Z u a Ch₀ A hA bad K hRP c gU hExt`. Establish `hG : ((I.rec7 l Z).sp.X B.R.m).gram.reindex (finCongr (rankN (I.rec7 l Z) B.R.m le_rfl)) (finCongr (rankN (I.rec7 l Z) B.R.m le_rfl)) = 1` using `((GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hOk hPins l Z).2.2.2 B.R.m le_rfl).1`. Take `⟨γ, hγQ, hγf, hγi⟩` from `ratPt θ hθ _ (rankN (I.rec7 l Z) B.R.m le_rfl) hG (Formalism.L2.Col.ufGL _ _ ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)).1) (GlobalTheory.Mem.Col2.DnAdel.ufGL_UJ B.sp.cm _ ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)).1)`.

Take `⟨hh₀f, hh₀m⟩` from `hA.h B.R.m le_rfl (A.chOf B.R.m ((I.perIn u a).tilC c)) ⟨(I.perIn u a).tilC c, rfl⟩`. Use `set h₀ := A.h B.R.m (A.chOf B.R.m ((I.perIn u a).tilC c)) ⟨(I.perIn u a).tilC c, rfl⟩ with hh₀`. Use `set Zr := (γ * h₀)⁻¹ * emb h with hZr`. Use `set κA := GlobalTheory.AdForm.RdLaw.pf _ Zr with hκA`. Establish `hκAf : κA ∈ GfC _` using `GlobalTheory.AdForm.RdLaw.pf_fin _ Zr`.

Use `set Y : TC.GA B (B.R.N B.R.m) := (show TC.GA B (B.R.N B.R.m) from ((A.K B.R.m le_rfl (A.chOf B.R.m ((I.perIn u a).tilC c))).y ⟨(I.perIn u a).tilC c, rfl⟩).1) with hY`. Use `set Rr := ratAd B.host.F ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)).1 with hRr`. Establish `e1 : finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) (γ * h₀) * finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) Zr = gU.1`. Rewrite using `[← GlobalTheory.AdForm.StabMove.finM_mul, hZr, mul_inv_cancel_left]`. Establish `e2 : finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) (γ * h₀) = (Rr * Y).1`.

Rewrite using `[GlobalTheory.AdForm.StabMove.finM_mul, hγf, hh₀m]`. Both sides reduce to the same expression. Establish `e3 : (Rr * Y).1 * (show Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) (AfE B.host.F B.host.E) from finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) Zr) = gU.1` using `by rw [← e2]; exact e1`. Establish `hfZ : finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) Zr = ((Rr * Y)⁻¹ * gU).1`. Establish `e4 : ((Rr * Y)⁻¹ * gU).1 = ((Rr * Y)⁻¹).1 * ((Rr * Y).1 * (show Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) (AfE B.host.F B.host.E) from finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) Zr))` using `by rw [Units.val_mul, e3]`.

Rewrite using `[e4, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]`. Establish `hκ0' : (show TC.GA B (B.R.N B.R.m) from κ0.1) = (Rr * Y)⁻¹ * gU` using `by rw [hκ0, _root_.mul_inv_rev]`. Establish `hfκ : κ0.1.1 = finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) κA`. Rewrite using `[finM_pf', hfZ, ← hκ0']`. Establish `hκU : κA ∈ A.U B.R.m (A.chOf B.R.m ((I.perIn u a).tilC c))` using `(hA.U B.R.m le_rfl _ κA).2 ⟨hκAf, κ0, hfκ⟩`.

Set `κ : A.U B.R.m (A.chOf B.R.m ((I.perIn u a).tilC c))` to `⟨κA, hκU⟩`. Establish `hchi` using `hA.chi B.R.m le_rfl _ κ κ0 hfκ`. Use `set k := Zr * κA⁻¹ with hk`. Establish `hkC : k ∈ GinfC _` using `mem_GinfC_of_finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) k (by`. Rewrite using `[hk, GlobalTheory.AdForm.StabMove.finM_mul, ← finM_pf' _ (rankN (I.rec7 l Z) B.R.m le_rfl) Zr, ← hκA, hinvM])`.

Establish `hInf : ∀ τ, infM θ _ (rankN (I.rec7 l Z) B.R.m le_rfl) (emb h) τ = 1` using `fun τ => isBlock_one (Formalism.L2.Col.N_m_succ B.R) (GlobalTheory.EmbTopBlock.isBlock_infM_emb I hOk hPins l Z u θ hθ emb (Formalism.L2.Col.N_m_succ B.R) hEmb h τ) (infM_fin'' θ _ (rankP (I.rec7 l Z)) h hM.1 τ)`. Use `⟨γ, hγQ, k, hkC, κ, ?_, ?_⟩` and prove the remaining obligations. Use `show emb h = γ * (h₀ * (Zr * κA⁻¹)) * κA`. Rewrite using `[hZr]`. Use `group`.

Introduce `φ _ y`. Use `⟨frMul B.fields.emb B.embLL ((I.stp u a B.R.m).gam (I.perIn u a).b0 ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)))⁻¹ y, ?_, ?_⟩` and prove the remaining obligations. Introduce `τ`. Establish `ek : k = h₀⁻¹ * γ⁻¹ * (emb h * κA⁻¹)` using `by rw [hk, hZr]; group`. Establish `hk' : infM θ _ (rankN (I.rec7 l Z) B.R.m le_rfl) k τ = ((((I.stp u a B.R.m).gam (I.perIn u a).b0 ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)))⁻¹ : GL (Fin (B.R.N B.R.m)) B.fields.E) : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) B.fields.E).map (Formalism.L2. …`.

Rewrite using `[ek, infM_mul', infM_mul', infM_mul', infM_fin'' θ _ _ h₀⁻¹ (inv_mem hh₀f), hInf, infM_fin'' θ _ _ κA⁻¹ (inv_mem hκAf), one_mul, mul_one, mul_one, hγi τ, GlobalTheory.Mem.Col2.LowerTie.embT_eq I l Z]`. Both sides reduce to the same expression. Rewrite using `[hk']`. Both sides reduce to the same expression. Rewrite using `[hchi, hχ0]`.

Both sides reduce to the same expression.
-/
theorem GlobalTheory.AdForm.TwDat.Is.evz_decomp : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀), A.Is → ∀ θ, IsInfFam θ → ∀ emb : GA (I.rec7 l Z) (I.rec7 l Z).sp.X' →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X B.R.m), IsEmbTop (D := (I.rec7 l Z)) (TC.z0 X u) emb → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∀ c h, GlobalTheory.Core.Rk.Top.HasMat h (K.y c).1 → ∃ γ ∈ GQ ((I.rec7 l Z).sp.X B.R.m), ∃ k ∈ GinfC ((I.rec7 l Z).sp.X B.R.m), ∃ κ : A.U B.R.m (A.chOf B.R.m ((I.perIn u a).tilC c)), emb h = γ * (A.h B.R.m _ ⟨(I.perIn u a).tilC c, rfl⟩ * k) * κ.1 ∧ ∀ φ ∈ (I.fm l u a).Fi B.R.m, ∀ y : (I.chain l u a).Y B.R.m, ∃ y' : (I.chain l u a).Y B.R.m, IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) B.R.m le_rfl) k) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ ∧ (A.chi B.R.m _ κ : ℂ) * φ ((I.perIn u a).tilC c) y' = (I.per l u a).evz φ c y := by
  intro B X I hOk hPins l Z u a Ch₀ A hA θ hθ emb hEmb bad K hRP c h hM
  have hExt := ext_finM_emb I hOk hPins l Z u emb hEmb h (K.y c).1 hM
  have hinvM : ∀ x : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X B.R.m), finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) x *
      finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) x⁻¹ = 1 := fun x => by
    rw [← GlobalTheory.AdForm.StabMove.finM_mul, mul_inv_cancel, finM_one']
  have hinvM' : ∀ x : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X B.R.m), finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) x⁻¹ *
      finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) x = 1 := fun x => by
    rw [← GlobalTheory.AdForm.StabMove.finM_mul, inv_mul_cancel, finM_one']
  let gU : TC.GA B (B.R.N B.R.m) := ⟨finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) (emb h),
    finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) (emb h)⁻¹, hinvM _, hinvM' _⟩
  obtain ⟨κ0, hκ0, hχ0⟩ := top_lev_chi I hOk hPins l Z u a Ch₀ A hA bad K hRP c gU hExt
  have hG : ((I.rec7 l Z).sp.X B.R.m).gram.reindex (finCongr (rankN (I.rec7 l Z) B.R.m le_rfl))
      (finCongr (rankN (I.rec7 l Z) B.R.m le_rfl)) = 1 := ((GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hOk hPins l Z).2.2.2 B.R.m le_rfl).1
  obtain ⟨γ, hγQ, hγf, hγi⟩ := ratPt θ hθ _ (rankN (I.rec7 l Z) B.R.m le_rfl) hG
    (Formalism.L2.Col.ufGL _ _ ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)).1)
    (GlobalTheory.Mem.Col2.DnAdel.ufGL_UJ B.sp.cm _ ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)).1)
  obtain ⟨hh₀f, hh₀m⟩ := hA.h B.R.m le_rfl (A.chOf B.R.m ((I.perIn u a).tilC c)) ⟨(I.perIn u a).tilC c, rfl⟩
  set h₀ := A.h B.R.m (A.chOf B.R.m ((I.perIn u a).tilC c)) ⟨(I.perIn u a).tilC c, rfl⟩ with hh₀
  set Zr := (γ * h₀)⁻¹ * emb h with hZr
  set κA := GlobalTheory.AdForm.RdLaw.pf _ Zr with hκA
  have hκAf : κA ∈ GfC _ := GlobalTheory.AdForm.RdLaw.pf_fin _ Zr
  set Y : TC.GA B (B.R.N B.R.m) := (show TC.GA B (B.R.N B.R.m) from
    ((A.K B.R.m le_rfl (A.chOf B.R.m ((I.perIn u a).tilC c))).y ⟨(I.perIn u a).tilC c, rfl⟩).1) with hY
  set Rr := ratAd B.host.F ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)).1 with hRr
  have e1 : finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) (γ * h₀) * finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) Zr = gU.1 := by
    rw [← GlobalTheory.AdForm.StabMove.finM_mul, hZr, mul_inv_cancel_left]
  have e2 : finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) (γ * h₀) = (Rr * Y).1 := by
    rw [GlobalTheory.AdForm.StabMove.finM_mul, hγf, hh₀m]; rfl
  have e3 : (Rr * Y).1 * (show Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) (AfE B.host.F B.host.E) from
      finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) Zr) = gU.1 := by rw [← e2]; exact e1
  have hfZ : finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) Zr = ((Rr * Y)⁻¹ * gU).1 := by
    have e4 : ((Rr * Y)⁻¹ * gU).1 = ((Rr * Y)⁻¹).1 * ((Rr * Y).1 * (show Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) (AfE B.host.F B.host.E) from
      finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) Zr)) := by rw [Units.val_mul, e3]
    rw [e4, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  have hκ0' : (show TC.GA B (B.R.N B.R.m) from κ0.1) = (Rr * Y)⁻¹ * gU := by rw [hκ0, _root_.mul_inv_rev]
  have hfκ : κ0.1.1 = finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) κA := by
    rw [finM_pf', hfZ, ← hκ0']
  have hκU : κA ∈ A.U B.R.m (A.chOf B.R.m ((I.perIn u a).tilC c)) :=
    (hA.U B.R.m le_rfl _ κA).2 ⟨hκAf, κ0, hfκ⟩
  let κ : A.U B.R.m (A.chOf B.R.m ((I.perIn u a).tilC c)) := ⟨κA, hκU⟩
  have hchi := hA.chi B.R.m le_rfl _ κ κ0 hfκ
  set k := Zr * κA⁻¹ with hk
  have hkC : k ∈ GinfC _ := mem_GinfC_of_finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) k (by
    rw [hk, GlobalTheory.AdForm.StabMove.finM_mul, ← finM_pf' _ (rankN (I.rec7 l Z) B.R.m le_rfl) Zr, ← hκA, hinvM])
  have hInf : ∀ τ, infM θ _ (rankN (I.rec7 l Z) B.R.m le_rfl) (emb h) τ = 1 := fun τ =>
    isBlock_one (Formalism.L2.Col.N_m_succ B.R)
      (GlobalTheory.EmbTopBlock.isBlock_infM_emb I hOk hPins l Z u θ hθ emb (Formalism.L2.Col.N_m_succ B.R) hEmb h τ)
      (infM_fin'' θ _ (rankP (I.rec7 l Z)) h hM.1 τ)
  refine ⟨γ, hγQ, k, hkC, κ, ?_, ?_⟩
  · show emb h = γ * (h₀ * (Zr * κA⁻¹)) * κA
    rw [hZr]; group
  · intro φ _ y
    refine ⟨frMul B.fields.emb B.embLL ((I.stp u a B.R.m).gam (I.perIn u a).b0
      ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)))⁻¹ y, ?_, ?_⟩
    · intro τ
      have ek : k = h₀⁻¹ * γ⁻¹ * (emb h * κA⁻¹) := by rw [hk, hZr]; group
      have hk' : infM θ _ (rankN (I.rec7 l Z) B.R.m le_rfl) k τ = ((((I.stp u a B.R.m).gam (I.perIn u a).b0
          ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)))⁻¹ : GL (Fin (B.R.N B.R.m)) B.fields.E) :
            Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) B.fields.E).map (Formalism.L2.Col.embAt B.embLL B.fields.emb τ) := by
        rw [ek, infM_mul', infM_mul', infM_mul', infM_fin'' θ _ _ h₀⁻¹ (inv_mem hh₀f), hInf,
          infM_fin'' θ _ _ κA⁻¹ (inv_mem hκAf), one_mul, mul_one, mul_one, hγi τ,
          GlobalTheory.Mem.Col2.LowerTie.embT_eq I l Z]
        rfl
      rw [hk']
      rfl
    · rw [hchi, hχ0]
      rfl
