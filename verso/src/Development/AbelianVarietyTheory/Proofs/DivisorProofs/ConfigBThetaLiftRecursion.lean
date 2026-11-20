import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockSpaceStableArchimedeanMaximalCompaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartCompactStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartInvariantSubmoduleDenseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBMatchedIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBMatchedIntegralFoldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBMatchedThetaCompareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactLeviLiftStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.BranchIsoB

/- English proof (translation)
Introduce `r _`. Establish `h0 : tens (evI F) (⇑(0 : SInf F κ)) r = 0`. Use function extensionality and compare the values at `x`. Simplify using `[tens]`. Rewrite using `[h0, map_zero]`.
-/
theorem acts_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (T : Module.End ℂ ((κ → AF F) → ℂ)) :
    Acts (evI F) T (⇑(0 : SInf F κ)) (⇑(0 : SInf F κ)) := by
  intro r _
  have h0 : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by
    funext x; simp [tens]
  rw [h0, map_zero]

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁`. Establish `hstab` using `GlobalTheory.T.config_B_matched_integral hKP F E σ B a b G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁`. Establish `hirr` using `GlobalTheory.T.config_B_matched_integral_fold hKP F E σ B a b G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁`. Take `⟨ψ, ⟨y₀, hy₀, hψy₀⟩, hψV, hψeq⟩` from `GlobalTheory.T.config_B_matched_theta_compare hKP F E σ B a b G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁`. Establish `hlift` using `GlobalTheory.T.max_compact_levi_lift F E σ B a b G G₁ H H' hC hM.triple.base hM.triple.geo hM₁.triple.geo`.

Establish `hirr₁` using `GlobalTheory.T.lowPart_invariant_submodule_dense hKP F E σ B a b G₁ X om₁ om₁' R₁ Rf₁ hM₁`. Establish `hstab₁` using `(GlobalTheory.T.low_part_compact_stable hKP F E σ B a b G₁ X om₁ om₁' R₁ Rf₁ hM₁).1`. Use `set Vt := (twPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) (lowPartInf B G.M R.p)) with hVt`. Use `set V₁ := lowPartInf B G₁.M R₁.p with hV₁`. Establish `hker : ∀ y ∈ V₁, ψ y = 0 → y = 0`.

Set `N₁ : Submodule ℂ R₁.Pi` to `V₁ ⊓ LinearMap.ker ψ`. Establish `hN₁ : ∀ k₁ ∈ KInf σ G₁.W B.emb, ∀ g ∈ G₁.M.Pol B.ψ B.emb, ∀ g₁ : SInf F (Fin a × Fin (a + b)), Acts (evI F) (om₁ (1, k₁)) g g₁ → R₁.p g ∈ N₁ → R₁.p g₁ ∈ N₁`. Introduce `k₁ hk₁ g hg g₁ hact hgN`. Take `⟨hgV, hgK⟩` from `Submodule.mem_inf.1 hgN`. Take `⟨k, hk, hL⟩` from `hlift k₁ hk₁`.

Use `Submodule.mem_inf.2 ⟨hstab₁ k₁ hk₁ g hg g₁ hact hgV, ?_⟩` and prove the remaining obligations. Rewrite `hgK`, the goal using `[LinearMap.mem_ker]`. Use `hψeq k hk k₁ hk₁ hL g hg g₁ hact hgV 0 (G.M.Pol B.ψ B.emb).zero_mem 0 (acts_zero _) (by rw [hgK, map_zero])` as an intermediate fact. Rewrite using `[this, map_zero]`. Break down `hirr₁ N₁ inf_le_left hN₁ with h | h` into its components or cases.

Introduce `y hy hψ`. Establish `: y ∈ N₁` using `Submodule.mem_inf.2 ⟨hy, hψ⟩`. Rewrite `this` using `[h, Submodule.mem_bot]`. Then use the resulting hypothesis. It suffices to derive a contradiction. Establish `: y₀ ∈ N₁` using `by rw [h]; exact hy₀`.

Conclude with `hψy₀ (Submodule.mem_inf.1 this).2`. Establish `himg : V₁.map ψ = Vt`. Establish `hle : V₁.map ψ ≤ Vt` using `Submodule.map_le_iff_le_comap.2 fun y hy => hψV y hy`. Establish `hst : KStabL B G.M om R.p G₁.W H' (V₁.map ψ)`. Introduce `k hk k₁ hk₁ hL f hf f₁ hact hfN`.

Take `⟨y, hy, hyf⟩` from `Submodule.mem_map.1 hfN`. Take `⟨g, hg, rfl⟩` from `Submodule.mem_map.1 hy`. Establish `hgP : g ∈ G₁.M.Pol B.ψ B.emb` using `fockDeg_le_pol _ _ _ _ hg`. Take `⟨A₁, hA₁⟩` from `GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B a (a + b) G₁.V G₁.W G₁.M om₁ X.β (X.β / X.α) hM₁.triple.base hM₁.triple.geo.hM hM₁.triple.weil k₁ hk₁`. Establish `hact₁` using `hA₁ g`.

Establish `hyV : R₁.p g ∈ V₁` using `hy`. Use `hψeq k hk k₁ hk₁ hL g hgP (A₁ g) hact₁ hyV f hf f₁ hact hyf` as an intermediate fact. Conclude with `Submodule.mem_map.2 ⟨R₁.p (A₁ g), hstab₁ k₁ hk₁ g hgP (A₁ g) hact₁ hyV, this⟩`. Break down `hirr _ hle hst with h | h` into its components or cases. It suffices to derive a contradiction.

Establish `: ψ y₀ ∈ V₁.map ψ` using `Submodule.mem_map_of_mem hy₀`. Rewrite `this` using `[h, Submodule.mem_bot]`. Conclude with `hψy₀ this`. Conclude with `h`. Establish `hψV' : ∀ y : V₁, ψ y ∈ Vt` using `fun y => hψV y y.2`.

Set `ψ' : V₁ →ₗ[ℂ] Vt` to `(ψ.domRestrict V₁).codRestrict Vt hψV'`. Establish `hinj : Function.Injective ψ'`. Rewrite using `[← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]`. Introduce `y hy`. Rewrite `hy` using `[LinearMap.mem_ker]`.

Establish `h1 : ψ y = 0` using `congrArg Subtype.val hy`. Conclude with `Subtype.ext (hker y y.2 h1)`. Establish `hsurj : Function.Surjective ψ'`. Introduce and unpack `⟨x, hx⟩`. Rewrite `hx` using `[← himg]`.

Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.1 hx`. Conclude with `⟨⟨y, hy⟩, rfl⟩`. Set `e : V₁ ≃ₗ[ℂ] Vt` to `LinearEquiv.ofBijective ψ' ⟨hinj, hsurj⟩`. Take `⟨C, hCc⟩` from `Submodule.exists_isCompl Vt`. Set `π : R.Pi →ₗ[ℂ] Vt` to `Submodule.linearProjOfIsCompl Vt C hCc`.

Establish `hπ : ∀ x (hx : x ∈ Vt), π x = ⟨x, hx⟩` using `fun x hx => Submodule.linearProjOfIsCompl_apply_left hCc ⟨x, hx⟩`. Set `ι : R.Pi →ₗ[ℂ] R₁.Pi` to `V₁.subtype ∘ₗ e.symm.toLinearMap ∘ₗ π`. Establish `hιv : ∀ x (hx : x ∈ Vt), ι x = (e.symm ⟨x, hx⟩ : V₁)` using `fun x hx => by`. Simplify using `only [ι, LinearMap.comp_apply, hπ x hx, Submodule.subtype_apply, LinearEquiv.coe_coe]`. Establish `hιψ : ∀ y (hy : y ∈ V₁), ι (ψ y) = y` using `fun y hy => by`.

Rewrite using `[hιv (ψ y) (hψV y hy)]`. Establish `: (⟨ψ y, hψV y hy⟩ : Vt) = e ⟨y, hy⟩` using `rfl`. Rewrite using `[this, LinearEquiv.symm_apply_apply]`. Establish `hψι : ∀ x (hx : x ∈ Vt), ψ (ι x) = x` using `fun x hx => by`. Rewrite using `[hιv x hx]`.

Use `congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)` as an intermediate fact. Conclude with `this`. Use `⟨ι, ?_, ?_, hstab, ?_⟩` and prove the remaining obligations. Introduce `y hy h0`. Rewrite using `[← hψι y hy, h0, map_zero]`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite using `[hιv x hx]`. Conclude with `(e.symm ⟨x, hx⟩).2`. Introduce `y hy`.

Conclude with `⟨ψ y, hψV y hy, hιψ y hy⟩`. Introduce `k hk k₁ hk₁ hL f hf f₁ hact hfV g hg g₁ hact₁ hιf`. Establish `hgV : R₁.p g ∈ V₁` using `by rw [← hιf, hιv _ hfV]; exact (e.symm _).2`. Establish `h1 : ψ (R₁.p g) = R.p f` using `by rw [← hιf, hψι _ hfV]`. Establish `h2` using `hψeq k hk k₁ hk₁ hL g hg g₁ hact₁ hgV f hf f₁ hact h1`.

Rewrite using `[← h2, hιψ _ (hstab₁ k₁ hk₁ g hg g₁ hact₁ hgV)]`.
-/
theorem twPart_iso_lowPart : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a (b + 2)) (Rf : FinMaps F a (b + 2))
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F a b) (Rf₁ : FinMaps F a b),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∃ ι : R.Pi →ₗ[ℂ] R₁.Pi, (∀ y ∈ twPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) (lowPartInf B G.M R.p), ι y = 0 → y = 0) ∧
        (twPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) (lowPartInf B G.M R.p)).map ι = lowPartInf B G₁.M R₁.p ∧
        KStabL B G.M om R.p G₁.W H' (twPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) (lowPartInf B G.M R.p)) ∧
        ∀ k ∈ KInf σ G.W B.emb, ∀ k₁ ∈ KInf σ G₁.W B.emb, IsLevi H' 1 k₁ k →
          ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + (b + 2))), Acts (evI F) (om (1, k)) f f₁ →
          R.p f ∈ twPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) (lowPartInf B G.M R.p) → ∀ g ∈ G₁.M.Pol B.ψ B.emb, ∀ g₁ : SInf F (Fin a × Fin (a + b)),
          Acts (evI F) (om₁ (1, k₁)) g g₁ → ι (R.p f) = R₁.p g → ι (R.p f₁) = R₁.p g₁ := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁
  have hstab := GlobalTheory.T.config_B_matched_integral hKP F E σ B a b G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁
  have hirr := GlobalTheory.T.config_B_matched_integral_fold hKP F E σ B a b G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁
  obtain ⟨ψ, ⟨y₀, hy₀, hψy₀⟩, hψV, hψeq⟩ := GlobalTheory.T.config_B_matched_theta_compare hKP F E σ B a b G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁
  have hlift := GlobalTheory.T.max_compact_levi_lift F E σ B a b G G₁ H H' hC hM.triple.base hM.triple.geo hM₁.triple.geo
  have hirr₁ := GlobalTheory.T.lowPart_invariant_submodule_dense hKP F E σ B a b G₁ X om₁ om₁' R₁ Rf₁ hM₁
  have hstab₁ := (GlobalTheory.T.low_part_compact_stable hKP F E σ B a b G₁ X om₁ om₁' R₁ Rf₁ hM₁).1
  set Vt := (twPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) (lowPartInf B G.M R.p)) with hVt
  set V₁ := lowPartInf B G₁.M R₁.p with hV₁

  have hker : ∀ y ∈ V₁, ψ y = 0 → y = 0 := by
    let N₁ : Submodule ℂ R₁.Pi := V₁ ⊓ LinearMap.ker ψ
    have hN₁ : ∀ k₁ ∈ KInf σ G₁.W B.emb, ∀ g ∈ G₁.M.Pol B.ψ B.emb, ∀ g₁ : SInf F (Fin a × Fin (a + b)),
        Acts (evI F) (om₁ (1, k₁)) g g₁ → R₁.p g ∈ N₁ → R₁.p g₁ ∈ N₁ := by
      intro k₁ hk₁ g hg g₁ hact hgN
      obtain ⟨hgV, hgK⟩ := Submodule.mem_inf.1 hgN
      obtain ⟨k, hk, hL⟩ := hlift k₁ hk₁
      refine Submodule.mem_inf.2 ⟨hstab₁ k₁ hk₁ g hg g₁ hact hgV, ?_⟩
      rw [LinearMap.mem_ker] at hgK ⊢
      have := hψeq k hk k₁ hk₁ hL g hg g₁ hact hgV 0 (G.M.Pol B.ψ B.emb).zero_mem 0 (acts_zero _)
        (by rw [hgK, map_zero])
      rw [this, map_zero]
    rcases hirr₁ N₁ inf_le_left hN₁ with h | h
    · intro y hy hψ
      have : y ∈ N₁ := Submodule.mem_inf.2 ⟨hy, hψ⟩
      rwa [h, Submodule.mem_bot] at this
    · exfalso
      have : y₀ ∈ N₁ := by rw [h]; exact hy₀
      exact hψy₀ (Submodule.mem_inf.1 this).2

  have himg : V₁.map ψ = Vt := by
    have hle : V₁.map ψ ≤ Vt := Submodule.map_le_iff_le_comap.2 fun y hy => hψV y hy
    have hst : KStabL B G.M om R.p G₁.W H' (V₁.map ψ) := by
      intro k hk k₁ hk₁ hL f hf f₁ hact hfN
      obtain ⟨y, hy, hyf⟩ := Submodule.mem_map.1 hfN
      obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.1 hy
      have hgP : g ∈ G₁.M.Pol B.ψ B.emb := fockDeg_le_pol _ _ _ _ hg
      obtain ⟨A₁, hA₁⟩ := GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B a (a + b) G₁.V G₁.W G₁.M om₁ X.β (X.β / X.α)
        hM₁.triple.base hM₁.triple.geo.hM hM₁.triple.weil k₁ hk₁
      have hact₁ := hA₁ g
      have hyV : R₁.p g ∈ V₁ := hy
      have := hψeq k hk k₁ hk₁ hL g hgP (A₁ g) hact₁ hyV f hf f₁ hact hyf
      exact Submodule.mem_map.2 ⟨R₁.p (A₁ g), hstab₁ k₁ hk₁ g hgP (A₁ g) hact₁ hyV, this⟩
    rcases hirr _ hle hst with h | h
    · exfalso
      have : ψ y₀ ∈ V₁.map ψ := Submodule.mem_map_of_mem hy₀
      rw [h, Submodule.mem_bot] at this
      exact hψy₀ this
    · exact h
  have hψV' : ∀ y : V₁, ψ y ∈ Vt := fun y => hψV y y.2
  let ψ' : V₁ →ₗ[ℂ] Vt := (ψ.domRestrict V₁).codRestrict Vt hψV'
  have hinj : Function.Injective ψ' := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    rw [LinearMap.mem_ker] at hy
    have h1 : ψ y = 0 := congrArg Subtype.val hy
    exact Subtype.ext (hker y y.2 h1)
  have hsurj : Function.Surjective ψ' := by
    rintro ⟨x, hx⟩
    rw [← himg] at hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
    exact ⟨⟨y, hy⟩, rfl⟩
  let e : V₁ ≃ₗ[ℂ] Vt := LinearEquiv.ofBijective ψ' ⟨hinj, hsurj⟩
  obtain ⟨C, hCc⟩ := Submodule.exists_isCompl Vt
  let π : R.Pi →ₗ[ℂ] Vt := Submodule.linearProjOfIsCompl Vt C hCc
  have hπ : ∀ x (hx : x ∈ Vt), π x = ⟨x, hx⟩ := fun x hx =>
    Submodule.linearProjOfIsCompl_apply_left hCc ⟨x, hx⟩
  let ι : R.Pi →ₗ[ℂ] R₁.Pi := V₁.subtype ∘ₗ e.symm.toLinearMap ∘ₗ π
  have hιv : ∀ x (hx : x ∈ Vt), ι x = (e.symm ⟨x, hx⟩ : V₁) := fun x hx => by
    simp only [ι, LinearMap.comp_apply, hπ x hx, Submodule.subtype_apply, LinearEquiv.coe_coe]
  have hιψ : ∀ y (hy : y ∈ V₁), ι (ψ y) = y := fun y hy => by
    rw [hιv (ψ y) (hψV y hy)]
    have : (⟨ψ y, hψV y hy⟩ : Vt) = e ⟨y, hy⟩ := rfl
    rw [this, LinearEquiv.symm_apply_apply]
  have hψι : ∀ x (hx : x ∈ Vt), ψ (ι x) = x := fun x hx => by
    rw [hιv x hx]
    have := congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
    exact this
  refine ⟨ι, ?_, ?_, hstab, ?_⟩
  · intro y hy h0
    rw [← hψι y hy, h0, map_zero]
  · apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [hιv x hx]; exact (e.symm ⟨x, hx⟩).2
    · intro y hy
      exact ⟨ψ y, hψV y hy, hιψ y hy⟩
  · intro k hk k₁ hk₁ hL f hf f₁ hact hfV g hg g₁ hact₁ hιf
    have hgV : R₁.p g ∈ V₁ := by rw [← hιf, hιv _ hfV]; exact (e.symm _).2
    have h1 : ψ (R₁.p g) = R.p f := by rw [← hιf, hψι _ hfV]
    have h2 := hψeq k hk k₁ hk₁ hL g hg g₁ hact₁ hgV f hf f₁ hact h1
    rw [← h2, hιψ _ (hstab₁ k₁ hk₁ g hg g₁ hact₁ hgV)]

end GlobalTheory.BranchIsoB
