import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgAtLeAlgD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelInfAlt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieDerivativePolynomialFockArchimedeanUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryPreservesPolynomialFockStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankPolynomialFockSchrodingerModelLeAleph0Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealLieOperatorThetaQuotientLine

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix

noncomputable section

namespace GlobalTheory.HoweGlobalPair.RealPlaceSmall

section Ops

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

/- English proof (translation)
Introduce `r _`. Establish `e : tens (evI F) (⇑(0 : SInf F κ)) r = 0` using `by funext y; simp [tens]`. Rewrite using `[e, map_zero]`.
-/
private theorem acts_zero₀ (T : Module.End ℂ ((κ → AF F) → ℂ)) :
    Acts (evI F) ⇑T ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  rw [e, map_zero]

open scoped Classical in

/- English proof (translation)
Use `set g₀ : (κ → Af F) → ℂ := (GlobalTheory.RealLift.intPts F κ).indicator 1 with hg₀def`. Establish `hg₀ : g₀ ∈ SB (κ → Af F)` using `GlobalTheory.RealLift.indicator_intPts_mem_SB`. Establish `hg₀0 : g₀ 0 = 1` using `by rw [hg₀def, Set.indicator_of_mem GlobalTheory.RealLift.zero_mem_intPts]; rfl`. Use `set r₀ : (κ → AF F) → ℂ := fun x => g₀ (fun i => (x i).2) with hr₀def`. Establish `hr₀inv : ∀ x z, At (evI F) z → r₀ (x + z) = r₀ x`.

Introduce `x z hz`. Express the relevant statement in the definitionally equal form `g₀ (fun i => (x i + z i).2) = g₀ (fun i => (x i).2)`. Use `congr 1`. Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `(x i).2 + (z i).2 = (x i).2`.

Rewrite using `[GlobalTheory.RealLift.fin_eq_zero_of_at hz, add_zero]`. Establish `htens₀ : ∀ φ : (κ → mixedEmbedding.mixedSpace F) → ℂ, tens (evI F) φ r₀ = pureA F φ g₀` using `fun φ => rfl`. Establish `hrest₀ : ∀ φ : SInf F κ, Rest (evI F) ⇑φ r₀` using `fun φ => ⟨hr₀inv, by rw [htens₀]; exact Submodule.subset_span ⟨φ, g₀, hg₀, rfl⟩⟩`. Establish `e : ∀ φ ψ : SInf F κ, tens (evI F) ⇑(c • φ + ψ) r₀ = c • tens (evI F) ⇑φ r₀ + tens (evI F) ⇑ψ r₀`. Introduce `φ ψ`.

Use function extensionality and compare the values at `y`. Simplify using `[tens]`. Expand and normalize the polynomial expressions, which then agree. Establish `key : tens (evI F) ⇑h r₀ = tens (evI F) ⇑(c • f₁ + g₁) r₀`. Rewrite using `[← hh r₀ (hrest₀ _), e, map_add, map_smul, hf r₀ (hrest₀ f), hg r₀ (hrest₀ g), e]`.

Use extensionality with `a`. Use `congrFun key (GlobalTheory.RealLift.ptAt a 0)` as an intermediate fact. Rewrite `this` using `[htens₀, htens₀, GlobalTheory.RealLift.pureA_ptAt, GlobalTheory.RealLift.pureA_ptAt, hg₀0, mul_one, mul_one]`. Conclude with `this`.
-/
theorem acts_comb_eq (T : Module.End ℂ ((κ → AF F) → ℂ)) (c : ℂ) {f f₁ g g₁ h : SInf F κ}
    (hf : Acts (evI F) ⇑T ⇑f ⇑f₁) (hg : Acts (evI F) ⇑T ⇑g ⇑g₁) (hh : Acts (evI F) ⇑T ⇑(c • f + g) ⇑h) :
    h = c • f₁ + g₁ := by
  set g₀ : (κ → Af F) → ℂ := (GlobalTheory.RealLift.intPts F κ).indicator 1 with hg₀def
  have hg₀ : g₀ ∈ SB (κ → Af F) := GlobalTheory.RealLift.indicator_intPts_mem_SB
  have hg₀0 : g₀ 0 = 1 := by rw [hg₀def, Set.indicator_of_mem GlobalTheory.RealLift.zero_mem_intPts]; rfl
  set r₀ : (κ → AF F) → ℂ := fun x => g₀ (fun i => (x i).2) with hr₀def
  have hr₀inv : ∀ x z, At (evI F) z → r₀ (x + z) = r₀ x := by
    intro x z hz
    change g₀ (fun i => (x i + z i).2) = g₀ (fun i => (x i).2)
    congr 1
    funext i
    change (x i).2 + (z i).2 = (x i).2
    rw [GlobalTheory.RealLift.fin_eq_zero_of_at hz, add_zero]
  have htens₀ : ∀ φ : (κ → mixedEmbedding.mixedSpace F) → ℂ, tens (evI F) φ r₀ = pureA F φ g₀ := fun φ => rfl
  have hrest₀ : ∀ φ : SInf F κ, Rest (evI F) ⇑φ r₀ := fun φ =>
    ⟨hr₀inv, by rw [htens₀]; exact Submodule.subset_span ⟨φ, g₀, hg₀, rfl⟩⟩
  have e : ∀ φ ψ : SInf F κ, tens (evI F) ⇑(c • φ + ψ) r₀ = c • tens (evI F) ⇑φ r₀ + tens (evI F) ⇑ψ r₀ := by
    intro φ ψ; funext y; simp [tens]; ring
  have key : tens (evI F) ⇑h r₀ = tens (evI F) ⇑(c • f₁ + g₁) r₀ := by
    rw [← hh r₀ (hrest₀ _), e, map_add, map_smul, hf r₀ (hrest₀ f), hg r₀ (hrest₀ g), e]
  ext a
  have := congrFun key (GlobalTheory.RealLift.ptAt a 0)
  rw [htens₀, htens₀, GlobalTheory.RealLift.pureA_ptAt, GlobalTheory.RealLift.pureA_ptAt, hg₀0, mul_one, mul_one] at this
  exact this

/- English proof (translation)
Use `choose d hdP hd using hex`. Use `⟨{ toFun := fun x => ⟨d x x.2, hdP x x.2⟩, map_add' := ?_, map_smul' := ?_ }, fun x => hd x x.2⟩` and prove the remaining obligations. Introduce `x y`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h` using `hcomb 1 x (d x x.2) y (d y y.2) x.2 y.2 (hd x x.2) (hd y y.2)`.

Simplify using `only [one_smul] at h`. Conclude with `huniq _ _ _ (hd _ (x + y).2) h`. Introduce `c x`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h` using `hcomb c x (d x x.2) 0 0 x.2 P.zero_mem (hd x x.2) hzero`.

Simplify using `only [add_zero] at h`. Conclude with `huniq _ _ _ (hd _ (c • x).2) h`.
-/
theorem exists_op {V : Type} [AddCommGroup V] [Module ℂ V] (P : Submodule ℂ V) (Rel : V → V → Prop)
    (hex : ∀ f ∈ P, ∃ f₁ ∈ P, Rel f f₁) (huniq : ∀ f f₁ f₂, Rel f f₁ → Rel f f₂ → f₁ = f₂) (hzero : Rel 0 0)
    (hcomb : ∀ (c : ℂ) f f₁ g g₁, f ∈ P → g ∈ P → Rel f f₁ → Rel g g₁ → Rel (c • f + g) (c • f₁ + g₁)) :
    ∃ D : Module.End ℂ ↥P, ∀ x : ↥P, Rel x (D x) := by
  choose d hdP hd using hex
  refine ⟨{ toFun := fun x => ⟨d x x.2, hdP x x.2⟩, map_add' := ?_, map_smul' := ?_ }, fun x => hd x x.2⟩
  · intro x y
    apply Subtype.ext
    have h := hcomb 1 x (d x x.2) y (d y y.2) x.2 y.2 (hd x x.2) (hd y y.2)
    simp only [one_smul] at h
    exact huniq _ _ _ (hd _ (x + y).2) h
  · intro c x
    apply Subtype.ext
    have h := hcomb c x (d x x.2) 0 0 x.2 P.zero_mem (hd x x.2) hzero
    simp only [add_zero] at h
    exact huniq _ _ _ (hd _ (c • x).2) h

end Ops

/- English proof (translation)
Take `⟨hrs, A, hA⟩` from `h`. Set `e : Fin r ⊕ Fin s ≃ Fin n` to `finSumFinEquiv.trans (finCongr hrs)`. Set `A' : Matrix (Fin n) (Fin n) ℂ` to `A.submatrix id e.symm`. Establish `h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm`. Rewrite using `[← hA]`.

Use extensionality with `i j`. Simplify using `[A', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply]`. Establish `h2 : (A'ᵀ * M * A'.map star).det ≠ 0`. Rewrite using `[h1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]`. Simplify using `[Matrix.det_neg]`.

Introduce `h0`. Apply `h2` to reduce the goal to its premises. Rewrite using `[Matrix.det_mul, Matrix.det_mul, h0]`. Simplify using the standard rewrite rules.
-/
private theorem det_ne_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply]
  have h2 : (A'ᵀ * M * A'.map star).det ≠ 0 := by
    rw [h1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Matrix.det_neg]
  intro h0
  apply h2
  rw [Matrix.det_mul, Matrix.det_mul, h0]; simp

/- English proof (translation)
Introduce `h0`. Apply `det_ne_hasSig h` to reduce the goal to its premises. Establish `e` using `RingHom.map_det τ J`. Rewrite `e` using `[RingHom.mapMatrix_apply]`. Rewrite using `[Matrix.det_smul, ← e, h0, map_zero, mul_zero]`.
-/
private theorem det_ne_sig_map {E : Type} [Field E] {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (τ : E →+* ℂ) (c : ℂ)
    (h : HasSig (c • J.map τ) r s) : J.det ≠ 0 := by
  intro h0
  apply det_ne_hasSig h
  have e := RingHom.map_det τ J
  rw [RingHom.mapMatrix_apply] at e
  rw [Matrix.det_smul, ← e, h0, map_zero, mul_zero]

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩`.
-/
private theorem hecke_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

/- English proof (translation)
Substitute `hk` using the available equality. Introduce `a`. Establish `e` using `h a`. Establish `e'` using `h' a`. Rewrite using `[MonoidHom.div_apply, Circle.coe_div, e, e']`.

Use `split_ifs`. Simplify using the standard rewrite rules. Rewrite using `[pow_add]`. Apply the tactic sequence `rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring`.
-/
private theorem resEta_div {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) (hk : k = n + m) :
    ResEtaPow K (χ / χ') k := by
  subst hk
  intro a
  have e := h a
  have e' := h' a
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM hreal hLieX hCptX`. Establish `hT` using `hM.triple`. Establish `hg` using `hT.geo`. Establish `hc` using `hT.chars`. Take `⟨w₀⟩` from `(inferInstance : Nonempty (InfinitePlace F))`.

Establish `dV' : G.V'.J.det ≠ 0` using `det_ne_sig_map (Bs.emb w₀).1 1 (by rw [one_smul]; exact hg.hV'.sig w₀)`. Establish `dW : G.W.J.det ≠ 0` using `det_ne_sig_map (Bs.emb w₀).1 Complex.I (hg.hW.sig w₀)`. Establish `hres` using `resEta_div hc.resα hc.resβ (Nat.add_comm a a')`. Establish `hhk` using `hecke_div hc.heckeα hc.heckeβ`. Establish `hLie` using `GlobalTheory.T.lieDerivative_polynomialFock_archimedeanUnitary F E σ hT.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hT.base.std hg.hV'.herm dV' hg.hW.skew dW hc.resα hres hc.heckeα hhk hT.weil' Bs.emb hg.hV'.cartan hg.hW.cartan`.

Establish `hCpt` using `GlobalTheory.T.compactUnitary_preserves_polynomialFock F E σ hT.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hT.base.std hg.hV'.herm dV' hg.hW.skew dW hc.resα hres hc.heckeα hhk hT.weil' Bs.emb hg.hV'.cartan hg.hW.cartan`. Use `set P := G.M'.Pol Bs.ψ Bs.emb with hPdef`. Establish `lieOp : ∀ γ ∈ Lines σ G.W, ∃ D : Module.End ℂ ↥P, ∀ x : ↥P, ActsD (evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) ⇑(x : SInf F (Fin a' × Fin (a + a'))) ⇑((D x : ↥P) : SInf F (Fin a' × Fin (a + a')))`. Introduce `γ hγ`. Use `exists_op P (fun f f₁ => ActsD (evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑f₁) (fun f hf => ?_) (fun f f₁ f₂ h₁ h₂ => (GlobalTheory.RealLift.actsLaws F _ f f₁ f₂).2.2.1 _ h₁ h₂) (GlobalTheory.RealLieOp.actsD_zero' (fun t => om' (1, γ (Multiplicative.ofAdd t)))) (fu …` and prove the remaining obligations.

Take `⟨f₁, h₁⟩` from `(hLie γ hγ f hf).1`. Conclude with `⟨f₁, (hLie γ hγ f hf).2 f₁ h₁, h₁⟩`. Establish `cptOp : ∀ k ∈ KInf σ G.W Bs.emb, ∃ D : Module.End ℂ ↥P, ∀ x : ↥P, Acts (evI F) (om' (1, k)) ⇑(x : SInf F (Fin a' × Fin (a + a'))) ⇑((D x : ↥P) : SInf F (Fin a' × Fin (a + a')))`. Introduce `k hk`. Use `exists_op P (fun f f₁ => Acts (evI F) (om' (1, k)) ⇑f ⇑f₁) (fun f hf => ?_) (fun f f₁ f₂ h₁ h₂ => (GlobalTheory.RealLift.actsLaws F _ f f₁ f₂).2.2.2.1 _ h₁ h₂) (acts_zero₀ _) (fun c f f₁ g g₁ hf hg h₁ h₂ => ?_)` and prove the remaining obligations.

Take `⟨f₁, h₁⟩` from `(hCpt k hk f hf).1`. Conclude with `⟨f₁, (hCpt k hk f hf).2 f₁ h₁, h₁⟩`. Establish `hs : c • f + g ∈ P` using `add_mem (P.smul_mem c hf) hg`. Take `⟨h, hh⟩` from `(hCpt k hk _ hs).1`. Establish `e` using `acts_comb_eq (om' (1, k)) c h₁ h₂ hh`.

Rewrite `hh` using `[e]`. Conclude with `hh`. Establish `key : ∀ N : Submodule ℂ ↥P, relInf G.M' Bs.ψ Bs.emb om' ≤ N → (∀ g ∈ opInf G.M' Bs.ψ Bs.emb om', ∀ x ∈ N, g x ∈ N) → GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' (N.map P.subtype)`. Introduce `N hrel hop`. Use `⟨Submodule.map_subtype_le _ _, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `γ hγ f hf f₁ hA`. Establish `h1 : f₁ ∈ P` using `hLieX γ hγ f hf f₁ hA`. Conclude with `⟨⟨f₁, h1⟩, hrel (Submodule.subset_span (Or.inl ⟨γ, hγ, f, hf, hA⟩)), rfl⟩`. Introduce `k hk f hf f₁ hA`. Establish `h1 : f₁ ∈ P` using `hCptX k hk f hf f₁ hA`.

Conclude with `⟨⟨f₁, h1⟩ - ⟨f, hf⟩, hrel (Submodule.subset_span (Or.inr ⟨k, hk, ⟨f, hf⟩, ⟨f₁, h1⟩, hA, rfl⟩)), rfl⟩`. Introduce `γ hγ f hf f₁ hA`. Take `⟨y, hy, rfl⟩` from `hf`. Take `⟨D, hD⟩` from `lieOp γ hγ`. Establish `hgD : D ∈ opInf G.M' Bs.ψ Bs.emb om'` using `Or.inr ⟨γ, hγ, hD⟩`.

Establish `e : f₁ = ((D y : ↥P) : SInf F _)` using `(GlobalTheory.RealLift.actsLaws F _ _ _ _).2.2.1 _ hA (hD y)`. Conclude with `⟨D y, hop D hgD y hy, e.symm⟩`. Introduce `k hk f hf f₁ hA`. Take `⟨y, hy, rfl⟩` from `hf`. Take `⟨D, hD⟩` from `cptOp k hk`.

Establish `hgD : D ∈ opInf G.M' Bs.ψ Bs.emb om'` using `Or.inl ⟨k, hk, hD⟩`. Establish `e : f₁ = ((D y : ↥P) : SInf F _)` using `(GlobalTheory.RealLift.actsLaws F _ _ _ _).2.2.2.1 _ hA (hD y)`. Conclude with `⟨D y, hop D hgD y hy, e.symm⟩`. Establish `hinj : Function.Injective (Submodule.map P.subtype)` using `Submodule.map_injective_of_injective P.injective_subtype`. Establish `hne : ∀ N : Submodule ℂ ↥P, N ≠ ⊤ → N.map P.subtype ≠ P`.

Introduce `N hN h`. Apply `hN` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises. Rewrite using `[h, Submodule.map_subtype_top]`. Use `⟨GlobalTheory.T.rank_polynomialFock_schrodingerModel_le_aleph0 Bs G.M' hT.base hg.hV' hg.hW hg.hM', ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Take `⟨L, hL⟩` from `hreal.1`. Conclude with `⟨L, fun m N hN hN' => hL m (fun i => (N i).map P.subtype) ((Submodule.map_strictMono_of_injective P.injective_subtype).comp hN) fun i => key _ (hN' i).1 (hN' i).2⟩`. Introduce `N hrel hop hN x hx`. Conclude with `hreal.2 _ (key N hrel hop) (hne N hN) x ⟨x, hx, rfl⟩`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `x (⟨γ, hγ, f, hf, hA⟩ | ⟨k, hk, f, f₁, hA, rfl⟩)`. Conclude with `hM.real.quot'.lie γ hγ f hf _ hA`. Use `show R.p' (((f₁ - f : ↥P)) : SInf F _) = 0`. Rewrite using `[Submodule.coe_sub, map_sub, hM.real.quot'.cpt k hk f f.2 f₁ hA, sub_self]`. Introduce `g hgI x hx`.

Establish `hx' : R.p' (x : SInf F _) = 0` using `hx`. Use `show R.p' ((g x : ↥P) : SInf F _) = 0`. Break down `hgI with ⟨k, hk, hA⟩ | ⟨γ, hγ, hA⟩` into its components or cases. Establish `h` using `hM.real.cpt k hk 0 (G.M.Pol Bs.ψ Bs.emb).zero_mem x x.2 0 _ (acts_zero₀ _) (hA x) (by rw [hx', map_zero])`. Rewrite `h` using `[map_zero]`.

Conclude with `h.symm`. Establish `h` using `hM.real.lie γ hγ 0 (G.M.Pol Bs.ψ Bs.emb).zero_mem x x.2 0 _ (GlobalTheory.RealLieOp.actsD_zero' _) (hA x) (by rw [hx', map_zero])`. Rewrite `h` using `[map_zero]`. Conclude with `h.symm`.
-/
theorem realTransfer' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' N →
        N ≠ G.M'.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p' f = 0) →
    (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.V', ∀ f ∈ G.M'.Pol Bs.ψ Bs.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om' (γ (Multiplicative.ofAdd t), 1)) f f₁ → f₁ ∈ G.M'.Pol Bs.ψ Bs.emb) →
    (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.V' Bs.emb, ∀ f ∈ G.M'.Pol Bs.ψ Bs.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om' (k, 1)) f f₁ → f₁ ∈ G.M'.Pol Bs.ψ Bs.emb) →
    Module.rank ℂ ↥(G.M'.Pol Bs.ψ Bs.emb) ≤ Cardinal.aleph0 ∧
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ↥(G.M'.Pol Bs.ψ Bs.emb)), StrictMono N →
        (∀ j, GlobalTheory.HoweGlobalPair.relInf G.M' Bs.ψ Bs.emb om' ≤ N j ∧ ∀ g ∈ GlobalTheory.HoweGlobalPair.opInf G.M' Bs.ψ Bs.emb om', ∀ x ∈ N j, g x ∈ N j) → m ≤ L) ∧
    (∀ N : Submodule ℂ ↥(G.M'.Pol Bs.ψ Bs.emb), GlobalTheory.HoweGlobalPair.relInf G.M' Bs.ψ Bs.emb om' ≤ N → (∀ g ∈ GlobalTheory.HoweGlobalPair.opInf G.M' Bs.ψ Bs.emb om', ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ → N ≤ LinearMap.ker (R.p' ∘ₗ (G.M'.Pol Bs.ψ Bs.emb).subtype)) ∧
    GlobalTheory.HoweGlobalPair.relInf G.M' Bs.ψ Bs.emb om' ≤ LinearMap.ker (R.p' ∘ₗ (G.M'.Pol Bs.ψ Bs.emb).subtype) ∧
    ∀ g ∈ GlobalTheory.HoweGlobalPair.opInf G.M' Bs.ψ Bs.emb om', ∀ x ∈ LinearMap.ker (R.p' ∘ₗ (G.M'.Pol Bs.ψ Bs.emb).subtype), g x ∈ LinearMap.ker (R.p' ∘ₗ (G.M'.Pol Bs.ψ Bs.emb).subtype) := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM hreal hLieX hCptX
  have hT := hM.triple
  have hg := hT.geo
  have hc := hT.chars
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have dV' : G.V'.J.det ≠ 0 := det_ne_sig_map (Bs.emb w₀).1 1 (by rw [one_smul]; exact hg.hV'.sig w₀)
  have dW : G.W.J.det ≠ 0 := det_ne_sig_map (Bs.emb w₀).1 Complex.I (hg.hW.sig w₀)
  have hres := resEta_div hc.resα hc.resβ (Nat.add_comm a a')
  have hhk := hecke_div hc.heckeα hc.heckeβ
  have hLie := GlobalTheory.T.lieDerivative_polynomialFock_archimedeanUnitary F E σ hT.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hT.base.std
    hg.hV'.herm dV' hg.hW.skew dW hc.resα hres hc.heckeα hhk hT.weil' Bs.emb hg.hV'.cartan hg.hW.cartan
  have hCpt := GlobalTheory.T.compactUnitary_preserves_polynomialFock F E σ hT.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hT.base.std
    hg.hV'.herm dV' hg.hW.skew dW hc.resα hres hc.heckeα hhk hT.weil' Bs.emb hg.hV'.cartan hg.hW.cartan
  set P := G.M'.Pol Bs.ψ Bs.emb with hPdef

  have lieOp : ∀ γ ∈ Lines σ G.W, ∃ D : Module.End ℂ ↥P, ∀ x : ↥P,
      ActsD (evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) ⇑(x : SInf F (Fin a' × Fin (a + a')))
        ⇑((D x : ↥P) : SInf F (Fin a' × Fin (a + a'))) := by
    intro γ hγ
    refine exists_op P (fun f f₁ => ActsD (evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑f₁)
      (fun f hf => ?_) (fun f f₁ f₂ h₁ h₂ => (GlobalTheory.RealLift.actsLaws F _ f f₁ f₂).2.2.1 _ h₁ h₂)
      (GlobalTheory.RealLieOp.actsD_zero' (fun t => om' (1, γ (Multiplicative.ofAdd t))))
      (fun c f f₁ g g₁ _ _ h₁ h₂ => GlobalTheory.RealLieOp.actsD_comb (fun t => om' (1, γ (Multiplicative.ofAdd t))) c h₁ h₂)
    obtain ⟨f₁, h₁⟩ := (hLie γ hγ f hf).1
    exact ⟨f₁, (hLie γ hγ f hf).2 f₁ h₁, h₁⟩
  have cptOp : ∀ k ∈ KInf σ G.W Bs.emb, ∃ D : Module.End ℂ ↥P, ∀ x : ↥P,
      Acts (evI F) (om' (1, k)) ⇑(x : SInf F (Fin a' × Fin (a + a')))
        ⇑((D x : ↥P) : SInf F (Fin a' × Fin (a + a'))) := by
    intro k hk
    refine exists_op P (fun f f₁ => Acts (evI F) (om' (1, k)) ⇑f ⇑f₁)
      (fun f hf => ?_) (fun f f₁ f₂ h₁ h₂ => (GlobalTheory.RealLift.actsLaws F _ f f₁ f₂).2.2.2.1 _ h₁ h₂)
      (acts_zero₀ _) (fun c f f₁ g g₁ hf hg h₁ h₂ => ?_)
    · obtain ⟨f₁, h₁⟩ := (hCpt k hk f hf).1
      exact ⟨f₁, (hCpt k hk f hf).2 f₁ h₁, h₁⟩
    · have hs : c • f + g ∈ P := add_mem (P.smul_mem c hf) hg
      obtain ⟨h, hh⟩ := (hCpt k hk _ hs).1
      have e := acts_comb_eq (om' (1, k)) c h₁ h₂ hh
      rw [e] at hh
      exact hh

  have key : ∀ N : Submodule ℂ ↥P, relInf G.M' Bs.ψ Bs.emb om' ≤ N →
      (∀ g ∈ opInf G.M' Bs.ψ Bs.emb om', ∀ x ∈ N, g x ∈ N) →
      GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' (N.map P.subtype) := by
    intro N hrel hop
    refine ⟨Submodule.map_subtype_le _ _, ?_, ?_, ?_, ?_⟩
    · intro γ hγ f hf f₁ hA
      have h1 : f₁ ∈ P := hLieX γ hγ f hf f₁ hA
      exact ⟨⟨f₁, h1⟩, hrel (Submodule.subset_span (Or.inl ⟨γ, hγ, f, hf, hA⟩)), rfl⟩
    · intro k hk f hf f₁ hA
      have h1 : f₁ ∈ P := hCptX k hk f hf f₁ hA
      exact ⟨⟨f₁, h1⟩ - ⟨f, hf⟩, hrel (Submodule.subset_span (Or.inr ⟨k, hk, ⟨f, hf⟩, ⟨f₁, h1⟩, hA, rfl⟩)), rfl⟩
    · intro γ hγ f hf f₁ hA
      obtain ⟨y, hy, rfl⟩ := hf
      obtain ⟨D, hD⟩ := lieOp γ hγ
      have hgD : D ∈ opInf G.M' Bs.ψ Bs.emb om' := Or.inr ⟨γ, hγ, hD⟩
      have e : f₁ = ((D y : ↥P) : SInf F _) := (GlobalTheory.RealLift.actsLaws F _ _ _ _).2.2.1 _ hA (hD y)
      exact ⟨D y, hop D hgD y hy, e.symm⟩
    · intro k hk f hf f₁ hA
      obtain ⟨y, hy, rfl⟩ := hf
      obtain ⟨D, hD⟩ := cptOp k hk
      have hgD : D ∈ opInf G.M' Bs.ψ Bs.emb om' := Or.inl ⟨k, hk, hD⟩
      have e : f₁ = ((D y : ↥P) : SInf F _) := (GlobalTheory.RealLift.actsLaws F _ _ _ _).2.2.2.1 _ hA (hD y)
      exact ⟨D y, hop D hgD y hy, e.symm⟩
  have hinj : Function.Injective (Submodule.map P.subtype) :=
    Submodule.map_injective_of_injective P.injective_subtype
  have hne : ∀ N : Submodule ℂ ↥P, N ≠ ⊤ → N.map P.subtype ≠ P := by
    intro N hN h
    apply hN
    apply hinj
    rw [h, Submodule.map_subtype_top]
  refine ⟨GlobalTheory.T.rank_polynomialFock_schrodingerModel_le_aleph0 Bs G.M' hT.base hg.hV' hg.hW hg.hM', ?_, ?_, ?_, ?_⟩
  · obtain ⟨L, hL⟩ := hreal.1
    exact ⟨L, fun m N hN hN' => hL m (fun i => (N i).map P.subtype)
      ((Submodule.map_strictMono_of_injective P.injective_subtype).comp hN) fun i => key _ (hN' i).1 (hN' i).2⟩
  · intro N hrel hop hN x hx
    exact hreal.2 _ (key N hrel hop) (hne N hN) x ⟨x, hx, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro x (⟨γ, hγ, f, hf, hA⟩ | ⟨k, hk, f, f₁, hA, rfl⟩)
    · exact hM.real.quot'.lie γ hγ f hf _ hA
    · show R.p' (((f₁ - f : ↥P)) : SInf F _) = 0
      rw [Submodule.coe_sub, map_sub, hM.real.quot'.cpt k hk f f.2 f₁ hA, sub_self]
  · intro g hgI x hx
    have hx' : R.p' (x : SInf F _) = 0 := hx
    show R.p' ((g x : ↥P) : SInf F _) = 0
    rcases hgI with ⟨k, hk, hA⟩ | ⟨γ, hγ, hA⟩
    · have h := hM.real.cpt k hk 0 (G.M.Pol Bs.ψ Bs.emb).zero_mem x x.2 0 _ (acts_zero₀ _) (hA x)
        (by rw [hx', map_zero])
      rw [map_zero] at h
      exact h.symm
    · have h := hM.real.lie γ hγ 0 (G.M.Pol Bs.ψ Bs.emb).zero_mem x x.2 0 _
        (GlobalTheory.RealLieOp.actsD_zero' _) (hA x) (by rw [hx', map_zero])
      rw [map_zero] at h
      exact h.symm

end GlobalTheory.HoweGlobalPair.RealPlaceSmall

end
