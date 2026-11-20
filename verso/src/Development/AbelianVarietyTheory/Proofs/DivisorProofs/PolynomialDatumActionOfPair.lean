import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolActs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDualPairSwapSymmetry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFinitePiTensorSumOfFactorOperators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchrodingerMapExistsOfArchHeisenbergDerivaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivatiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLawsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupGeneratorsExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieScalarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExistsStatement

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PolActsPf

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.RealActs

section Swap

variable {P Q R S : ℕ}

def flipE (P Q R S : ℕ) : Formalism.BasicNotions.TH.Pol R S P Q ≃ₗ[ℂ] Formalism.BasicNotions.TH.Pol P Q R S :=
  (MvPolynomial.renameEquiv ℂ (Equiv.prodComm (Ix R S) (Ix P Q))).toLinearEquiv

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem flipE_apply (f : Formalism.BasicNotions.TH.Pol R S P Q) : flipE P Q R S f = MvPolynomial.rename Prod.swap f := rfl

/- English proof (translation)
Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> rfl`.
-/
theorem lineSign_flip (a : Ix P Q) (b : Ix R S) :
    lineSign (p := R) (q := S) (r := P) (s := Q) b a = lineSign (p := P) (q := Q) (r := R) (s := S) a b := by
  rcases a with a | a <;> rcases b with b | b <;> rfl

/- English proof (translation)
Simplify using `only [heisOp, flipE_apply, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sub_apply, map_smul, map_sum, map_sub, GlobalTheory.FockSwap.rename_raiB, GlobalTheory.FockSwap.rename_lowB]`. Use `congr 1`. Use `Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun l => ?_` and prove the remaining obligations. Simplify using `[lineSign_flip]`.
-/
theorem flipE_heisOp (c : Matrix (Ix R S) (Ix P Q) ℂ) (f : Formalism.BasicNotions.TH.Pol R S P Q) :
    flipE P Q R S (heisOp c f) = heisOp cᵀ (flipE P Q R S f) := by
  simp only [heisOp, flipE_apply, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sub_apply,
    map_smul, map_sum, map_sub, GlobalTheory.FockSwap.rename_raiB, GlobalTheory.FockSwap.rename_lowB]
  congr 1
  refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun l => ?_
  simp [lineSign_flip]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def flipT (ι : Type) (P Q R S : ℕ) :
    (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol R S P Q) ≃ₗ[ℂ] ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S :=
  PiTensorProduct.congr fun _ => flipE P Q R S

/- English proof (translation)
Establish `e : (flipT ι P Q R S).toLinearMap ∘ₗ atPl w L' = atPl w L ∘ₗ (flipT ι P Q R S).toLinearMap`. Use `PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)` and prove the remaining obligations. Simplify using `only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, atPl, flipT, PiTensorProduct.map_tprod, PiTensorProduct.congr_tprod]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Distinguish the cases in `hi : i = w`. Substitute `hi` using the available equality. Simplify using `[h]`. Simplify using `[Function.update_of_ne hi]`. Conclude with `LinearMap.congr_fun e T`.
-/
theorem flipT_atPl (w : ι) (L' : Module.End ℂ (Formalism.BasicNotions.TH.Pol R S P Q)) (L : Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))
    (h : ∀ f, flipE P Q R S (L' f) = L (flipE P Q R S f)) (T : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol R S P Q) :
    flipT ι P Q R S (atPl w L' T) = atPl w L (flipT ι P Q R S T) := by
  have e : (flipT ι P Q R S).toLinearMap ∘ₗ atPl w L' = atPl w L ∘ₗ (flipT ι P Q R S).toLinearMap := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, atPl, flipT,
      PiTensorProduct.map_tprod, PiTensorProduct.congr_tprod]
    congr 1
    funext i
    by_cases hi : i = w
    · subst hi; simp [h]
    · simp [Function.update_of_ne hi]
  exact LinearMap.congr_fun e T

/- English proof (translation)
Simplify using `only [sumPl, LinearMap.sum_apply, map_sum]`. Conclude with `Finset.sum_congr rfl fun w _ => flipT_atPl w (L' w) (L w) (h w) T`.
-/
theorem flipT_sumPl (L' : ι → Module.End ℂ (Formalism.BasicNotions.TH.Pol R S P Q)) (L : ι → Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))
    (h : ∀ w f, flipE P Q R S (L' w f) = L w (flipE P Q R S f)) (T : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol R S P Q) :
    flipT ι P Q R S (sumPl L' T) = sumPl L (flipT ι P Q R S T) := by
  simp only [sumPl, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun w _ => flipT_atPl w (L' w) (L w) (h w) T

end Swap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `⟨hΦ.1.comp (flipT (InfinitePlace F) P Q R S).injective, fun u hu c hc T => ?_⟩` and prove the remaining obligations. Establish `hu' : At (evI F) uᵀ` using `fun x hx => by rw [← Matrix.transpose_smul, hu x hx, Matrix.transpose_zero]`. Establish `hc' : ∀ w, uᵀ.map (piInf (τ w)) = A w * (c w)ᵀ * (C w)ᵀ` using `fun w => by`. Rewrite using `[Matrix.transpose_map, hc w]`. Simplify using `[Matrix.transpose_mul, Matrix.mul_assoc]`.

Establish `key` using `hΦ.2 uᵀ hu' (fun w => (c w)ᵀ) hc' (flipT (InfinitePlace F) P Q R S T)`. Establish `hr : ∀ t : ℝ, d'.rho ψ (realAd F t • u) = d.rho ψ (realAd F t • uᵀ)` using `fun t => by show schr ψ (d'.e _) = schr ψ (d.e _)`. Rewrite using `[← hdd, Matrix.transpose_smul, Matrix.transpose_transpose]`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, hr]`. Rewrite using `[flipT_sumPl (fun w => heisOp (c w)) (fun w => heisOp (c w)ᵀ) (fun w f => flipE_heisOp (c w) f)]` and apply the resulting hypothesis.
-/
theorem isFockMap_flip {σ : E →ₐ[F] E} {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
    {P Q R S : ℕ} {ψ : AddChar (AF F) ℂ} {τ : ∀ w : InfinitePlace F, EmbOver E w} {JA : Matrix α α (AE F E)}
    {JB : Matrix β β (AE F E)} {d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ}
    {d' : Darboux (symp (R := AF F) (cA σ) (-1) JB JA) κ} {A : InfinitePlace F → Matrix α (Ix P Q) ℂ}
    {C : InfinitePlace F → Matrix β (Ix R S) ℂ} {Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ} (hΦ : IsFockMap ψ τ d A C Φ)
    (hdd : ∀ x : Matrix α β (AE F E), d'.e xᵀ = d.e x) :
    IsFockMap ψ τ d' C A (Φ ∘ₗ (flipT (InfinitePlace F) P Q R S).toLinearMap) := by
  refine ⟨hΦ.1.comp (flipT (InfinitePlace F) P Q R S).injective, fun u hu c hc T => ?_⟩
  have hu' : At (evI F) uᵀ := fun x hx => by rw [← Matrix.transpose_smul, hu x hx, Matrix.transpose_zero]
  have hc' : ∀ w, uᵀ.map (piInf (τ w)) = A w * (c w)ᵀ * (C w)ᵀ := fun w => by
    rw [Matrix.transpose_map, hc w]; simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have key := hΦ.2 uᵀ hu' (fun w => (c w)ᵀ) hc' (flipT (InfinitePlace F) P Q R S T)
  have hr : ∀ t : ℝ, d'.rho ψ (realAd F t • u) = d.rho ψ (realAd F t • uᵀ) := fun t => by
    show schr ψ (d'.e _) = schr ψ (d.e _)
    rw [← hdd, Matrix.transpose_smul, Matrix.transpose_transpose]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hr]
  rwa [flipT_sumPl (fun w => heisOp (c w)) (fun w => heisOp (c w)ᵀ) (fun w f => flipE_heisOp (c w) f)]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[incM, piInf, compInf, inclR, infEmb_tmul]`.
-/
theorem incM_map_real {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

/- English proof (translation)
Introduce `v` and use `by obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 v exact ⟨W, hW, hv, fun y hy => W.add_mem (hs Y hY y hy) (W.smul_mem c hy)⟩`.
-/
theorem locFin_compact (P Q R S : ℕ) (Y : Mat R S) (hY : IsKC Y) (c : ℂ) :
    LocFin (fockAct2 P Q R S Y + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs Y hY y hy) (W.smul_mem c hy)⟩

section Graph

variable {κ V : Type} [Fintype κ] [AddCommGroup V] [Module ℂ V] {Φ : V →ₗ[ℂ] SInf F κ}

/- English proof (translation)
Take `⟨Ψ, hΨ⟩` from `LinearMap.exists_leftInverse_of_injective Φ (LinearMap.ker_eq_bot.2 hΦ)`. Use `⟨Φ ∘ₗ L ∘ₗ Ψ, fun f _ => LinearMap.mem_range_self Φ _, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨v, rfl⟩ f₁`. Establish `e : (Φ ∘ₗ L ∘ₗ Ψ) (Φ v) = Φ (L v)`. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, ← LinearMap.comp_apply Ψ Φ, hΨ, LinearMap.id_apply]`.

Rewrite using `[e]`. Conclude with `⟨fun h1 => huniq _ _ _ h1 (h v), fun h1 => h1 ▸ h v⟩`.
-/
theorem graph_of_inj (hΦ : Function.Injective Φ) (L : Module.End ℂ V) (Rel : SInf F κ → SInf F κ → Prop)
    (huniq : ∀ f f₁ f₂, Rel f f₁ → Rel f f₂ → f₁ = f₂) (h : ∀ v, Rel (Φ v) (Φ (L v))) :
    ∃ D : SInf F κ →ₗ[ℂ] SInf F κ, (∀ f ∈ LinearMap.range Φ, D f ∈ LinearMap.range Φ) ∧
      ∀ f ∈ LinearMap.range Φ, ∀ f₁ : SInf F κ, Rel f f₁ ↔ f₁ = D f := by
  obtain ⟨Ψ, hΨ⟩ := LinearMap.exists_leftInverse_of_injective Φ (LinearMap.ker_eq_bot.2 hΦ)
  refine ⟨Φ ∘ₗ L ∘ₗ Ψ, fun f _ => LinearMap.mem_range_self Φ _, ?_⟩
  rintro _ ⟨v, rfl⟩ f₁
  have e : (Φ ∘ₗ L ∘ₗ Ψ) (Φ v) = Φ (L v) := by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← LinearMap.comp_apply Ψ Φ, hΨ, LinearMap.id_apply]
  rw [e]
  exact ⟨fun h1 => huniq _ _ _ h1 (h v), fun h1 => h1 ▸ h v⟩

/- English proof (translation)
The claim follows from `graph_of_inj hΦ L (fun f f₁ => ActsD (evI F) T f f₁) (fun f f₁ f₂ => (actsLaws F κ f f₁ f₂).2.2.1 T) fun v => (actsLaws F κ _ _ (Φ v)).1 T h0 (h v)`.
-/
theorem derOn_of_sd (hΦ : Function.Injective Φ) (L : Module.End ℂ V) (T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ)
    (h0 : ∀ t, T t 0 = 0) (h : ∀ v, SD T (Φ v) (Φ (L v))) : DerOn (LinearMap.range Φ) T :=
  graph_of_inj hΦ L (fun f f₁ => ActsD (evI F) T f f₁) (fun f f₁ f₂ => (actsLaws F κ f f₁ f₂).2.2.1 T)
    fun v => (actsLaws F κ _ _ (Φ v)).1 T h0 (h v)

/- English proof (translation)
The claim follows from `graph_of_inj hΦ L (fun f f₁ => Acts (evI F) T f f₁) (fun f f₁ f₂ => (actsLaws F κ f f₁ f₂).2.2.2.1 T) fun v => (actsLaws F κ _ _ (Φ v)).2.1 T h0 (h v)`.
-/
theorem opOn_of_sa (hΦ : Function.Injective Φ) (L : Module.End ℂ V) (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ)
    (h0 : T 0 = 0) (h : ∀ v, SA T (Φ v) (Φ (L v))) : OpOn (LinearMap.range Φ) T :=
  graph_of_inj hΦ L (fun f f₁ => Acts (evI F) T f f₁) (fun f f₁ f₂ => (actsLaws F κ f f₁ f₂).2.2.2.1 T)
    fun v => (actsLaws F κ _ _ (Φ v)).2.1 T h0 (h v)

end Graph

/- English proof (translation)
Establish `hder : DerEx` using `GlobalTheory.T.archHeisenbergDerivatives_exist`. Establish `hls : LieScalar` using `GlobalTheory.T.lieScalar_of_prints_derEx_vacLine hP hder (GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder)`. Establish `hgen : GenEx` using `GlobalTheory.T.oneParamSubgroup_generators_exist`. Establish `hkl : KLine` using `kLine_of_lineEx exists_line_of_upq`. Take `⟨c, hact⟩` from `hls F E σ _ _ _ _ _ _ _ ψ τ _ _ d a b A C Φ om hcm hψ fr hΦ hs`.

Use `⟨fun γ hγ => ?_, fun k hk hc => ?_⟩` and prove the remaining obligations. Take `⟨Y, -, hY⟩` from `hgen F E σ β R S τ JB b C hcm fr.2.2 γ hγ`. Conclude with `derOn_of_sd hΦ.1 _ _ (fun t => map_zero _) (hact γ hγ Y hY)`. Take `⟨γ, hγ, Y, hY, hKC, hγ1⟩` from `hkl F E σ β R S τ JB b C θ hcm fr.2.2 hθ k hk hc`. Establish `hloc` using `locFin_sumPl _ _ _ (fun w => locFin_compact P Q R S (Y w) (hKC w) (c w * (Y w).trace))`.

Take `⟨U, -, hSA⟩` from `GlobalTheory.ExpAct.expAct_fock F κ _ Φ _ (om.comp γ) hloc (fun t l hl => hs.adm _ l hl) (fun T => hact γ hγ Y hY T)`. Rewrite `hSA` using `[MonoidHom.comp_apply, hγ1]`. Conclude with `opOn_of_sa hΦ.1 U _ (map_zero _) hSA`.
-/
theorem member (hP : GlobalTheory.FunPr.Hypotheses₂) {σ : E →ₐ[F] E} {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype κ] {P Q R S : ℕ} {ψ : AddChar (AF F) ℂ} {τ : ∀ w : InfinitePlace F, EmbOver E w}
    {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} {d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ} {a b : ℂ}
    {A : InfinitePlace F → Matrix α (Ix P Q) ℂ} {C : InfinitePlace F → Matrix β (Ix R S) ℂ}
    {Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ} {om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)}
    {θ : InfinitePlace F → Matrix β β ℂ} (hcm : IsCMExt F E σ) (hψ : IsStd ψ) (fr : Framed τ JA JB a b A C)
    (hΦ : IsFockMap ψ τ d A C Φ) (hs : IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om)
    (hθ : ∀ w, θ w * C w = C w * Jm R S) :
    (∀ γ ∈ RLines σ JB, DerOn (LinearMap.range Φ) (fun t => om (γ (Multiplicative.ofAdd t)))) ∧
    ∀ k : UG (cA σ) JB, At (evI F) ((k.1 : Matrix β β (AE F E)) - 1) →
      (∀ w, Commute ((k.1 : Matrix β β (AE F E)).map (piInf (τ w))) (θ w)) → OpOn (LinearMap.range Φ) (om k) := by
  have hder : DerEx := GlobalTheory.T.archHeisenbergDerivatives_exist
  have hls : LieScalar := GlobalTheory.T.lieScalar_of_prints_derEx_vacLine hP hder (GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder)
  have hgen : GenEx := GlobalTheory.T.oneParamSubgroup_generators_exist
  have hkl : KLine := kLine_of_lineEx exists_line_of_upq
  obtain ⟨c, hact⟩ := hls F E σ _ _ _ _ _ _ _ ψ τ _ _ d a b A C Φ om hcm hψ fr hΦ hs
  refine ⟨fun γ hγ => ?_, fun k hk hc => ?_⟩
  · obtain ⟨Y, -, hY⟩ := hgen F E σ β R S τ JB b C hcm fr.2.2 γ hγ
    exact derOn_of_sd hΦ.1 _ _ (fun t => map_zero _) (hact γ hγ Y hY)
  · obtain ⟨γ, hγ, Y, hY, hKC, hγ1⟩ := hkl F E σ β R S τ JB b C θ hcm fr.2.2 hθ k hk hc
    have hloc := locFin_sumPl _ _ _ (fun w => locFin_compact P Q R S (Y w) (hKC w) (c w * (Y w).trace))
    obtain ⟨U, -, hSA⟩ := GlobalTheory.ExpAct.expAct_fock F κ _ Φ _ (om.comp γ) hloc
      (fun t l hl => hs.adm _ l hl) (fun T => hact γ hγ Y hY T)
    rw [MonoidHom.comp_apply, hγ1] at hSA
    exact opOn_of_sa hΦ.1 U _ (map_zero _) hSA

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' h`. Establish `hb` using `h.base`. Establish `hfr : FrameEx` using `GlobalTheory.T.cartanEigen_orthonormalFrame_exists`. Establish `hder : DerEx` using `GlobalTheory.T.archHeisenbergDerivatives_exist`. Establish `hfe : FockEx` using `GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hder`.

Establish `hpr : PolRange` using `GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws actsLaws hder (GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder)`. Use `choose A hA hAθ using fun w => hfr _ _ _ _ _ (h.herm.sig w) (h.herm.cartan w)`. Use `choose C hC hCθ using fun w => hfr _ _ _ _ _ (h.skew.sig w) (h.skew.cartan w)`. Establish `hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w)` using `fun w => by`. Rewrite using `[incM_map_real, one_smul]`.

Conclude with `hA w`. Establish `hC1 : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w)` using `fun w => by`. Rewrite using `[incM_map_real]`. Conclude with `hC w`. Establish `fr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C` using `⟨one_mul _, hA1, hC1⟩`.

Establish `fr' : Framed B.emb (incM F W.J) (incM F X.J) Complex.I 1 C A` using `⟨mul_one _, hC1, hA1⟩`. Take `⟨Φ, hΦ⟩` from `hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C hb.cm hb.std fr`. Establish `hr` using `hpr F E σ _ _ _ _ _ _ X W M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ`. Establish `hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co χX χW om` using `h.weil`. Take `⟨d', hd', hB⟩` from `hwp.2.1`.

Establish `hr' : LinearMap.range (Φ ∘ₗ (flipT (InfinitePlace F) r s r' s').toLinearMap) = M.Pol B.ψ B.emb`. Rewrite using `[LinearEquiv.range_comp, hr]`. Take `⟨h1, h2⟩` from `member hP hb.cm hb.std fr' (isFockMap_flip hΦ hd') hB.1 hAθ`. Take `⟨h3, h4⟩` from `member hP hb.cm hb.std fr hΦ hwp.1.1 hCθ`. Rewrite `h1`, `h2` using `[hr']`.

Rewrite `h3`, `h4` using `[hr]`. Conclude with `⟨fun γ hγ => h1 γ hγ, fun k hk => h2 k hk.1 hk.2, fun γ hγ => h3 γ hγ, fun k hk => h4 k hk.1 hk.2⟩`.
-/
theorem polActs_of_isPair : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E)
    (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → GlobalTheory.RealActs.PolActs B M om := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' h
  have hb := h.base
  have hfr : FrameEx := GlobalTheory.T.cartanEigen_orthonormalFrame_exists
  have hder : DerEx := GlobalTheory.T.archHeisenbergDerivatives_exist
  have hfe : FockEx := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hder
  have hpr : PolRange := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws actsLaws hder (GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder)
  choose A hA hAθ using fun w => hfr _ _ _ _ _ (h.herm.sig w) (h.herm.cartan w)
  choose C hC hCθ using fun w => hfr _ _ _ _ _ (h.skew.sig w) (h.skew.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_real, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_real]; exact hC w
  have fr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have fr' : Framed B.emb (incM F W.J) (incM F X.J) Complex.I 1 C A := ⟨mul_one _, hC1, hA1⟩
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := hpr F E σ _ _ _ _ _ _ X W M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co χX χW om := h.weil
  obtain ⟨d', hd', hB⟩ := hwp.2.1
  have hr' : LinearMap.range (Φ ∘ₗ (flipT (InfinitePlace F) r s r' s').toLinearMap) = M.Pol B.ψ B.emb := by
    rw [LinearEquiv.range_comp, hr]
  obtain ⟨h1, h2⟩ := member hP hb.cm hb.std fr' (isFockMap_flip hΦ hd') hB.1 hAθ
  obtain ⟨h3, h4⟩ := member hP hb.cm hb.std fr hΦ hwp.1.1 hCθ
  rw [hr'] at h1 h2
  rw [hr] at h3 h4
  exact ⟨fun γ hγ => h1 γ hγ, fun k hk => h2 k hk.1 hk.2, fun γ hγ => h3 γ hγ, fun k hk => h4 k hk.1 hk.2⟩

end GlobalTheory.PolActsPf

end
