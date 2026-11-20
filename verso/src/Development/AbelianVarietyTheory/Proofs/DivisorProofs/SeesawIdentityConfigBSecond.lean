import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairDoubleDescent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingEigenIntertwinerTripleCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermComplement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairDoubleAdaptedRestrictionStatement

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.XTermLevi

/- English proof (translation)
Introduce `x`. Rewrite using `[MonoidHom.div_apply, Circle.coe_div, h₁ x, h₂ x]`. Use `split_ifs`. Simplify using the standard rewrite rules. Establish `h : ((-1 : ℂ) ^ n) * (-1) ^ n = 1` using `by rw [← pow_add, ← two_mul, pow_mul]; norm_num`.

Rewrite using `[div_eq_iff (pow_ne_zero _ (by norm_num)), pow_add, mul_assoc, h, mul_one]`.
-/
theorem resEtaPow_div {R E : Type} [CommRing R] [CommRing E] [Algebra R E] {K : Subgroup Rˣ}
    {χ₁ χ₂ : Eˣ →* Circle} {m n : ℕ} (h₁ : ResEtaPow K χ₁ m) (h₂ : ResEtaPow K χ₂ n) :
    ResEtaPow K (χ₁ / χ₂) (m + n) := by
  intro x
  rw [MonoidHom.div_apply, Circle.coe_div, h₁ x, h₂ x]
  split_ifs
  · simp
  · have h : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
    rw [div_eq_iff (pow_ne_zero _ (by norm_num)), pow_add, mul_assoc, h, mul_one]

/- English proof (translation)
Introduce `x`. Rewrite using `[h x]`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hn`. Use `split_ifs`. Both sides reduce to the same expression.

Rewrite using `[Nat.add_sub_cancel_left, pow_add]`. Evaluate the numerical expressions.
-/
theorem resEtaPow_sub_two {R E : Type} [CommRing R] [CommRing E] [Algebra R E] {K : Subgroup Rˣ}
    {χ : Eˣ →* Circle} {n : ℕ} (h : ResEtaPow K χ n) (hn : 2 ≤ n) : ResEtaPow K χ (n - 2) := by
  intro x
  rw [h x]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  split_ifs
  · rfl
  · rw [Nat.add_sub_cancel_left, pow_add]; norm_num

/- English proof (translation)
Assemble the required witnesses or components as `⟨h₁.1.div' h₂.1, fun x => by rw [MonoidHom.div_apply, h₁.2 x, h₂.2 x]; exact div_self' 1⟩`.
-/
theorem isHecke_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {χ₁ χ₂ : Chr F E}
    (h₁ : IsHecke F E χ₁) (h₂ : IsHecke F E χ₂) : IsHecke F E (χ₁ / χ₂) :=
  ⟨h₁.1.div' h₂.1, fun x => by rw [MonoidHom.div_apply, h₁.2 x, h₂.2 x]; exact div_self' 1⟩

/- English proof (translation)
Simplify using `only [thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]`.
-/
theorem thetaSum_smul {F : Type} [Field F] [NumberField F] {κ : Type} (c : ℂ) (Φ : (κ → AF F) → ℂ) :
    thetaSum F (c • Φ) = c * thetaSum F Φ := by
  simp only [thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mul_vecMulVec' {R : Type} [CommRing R] {n d : ℕ} (A : Matrix (Fin n) (Fin n) R) (x : Fin n → R) (y : Fin d → R) :
    A * Matrix.vecMulVec x y = Matrix.vecMulVec (A *ᵥ x) y := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Establish `e1 : ∀ v : Matrix (Fin n) (Fin d) (AE F E), actAB (cA σ) ((m, 1) : UA σ X.J × UA σ W.J) v = mat m * v`. Introduce `v`. Simplify using `[actAB, mat]`. Rewrite using `[e1]`. Break down `hu with ⟨y, rfl⟩ | ⟨z, rfl⟩` into its components or cases.

Conclude with `Or.inl ⟨mat m *ᵥ y, mul_vecMulVec' _ _ _⟩`. Use `Or.inr ⟨l.1 • z, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_vecMulVec', hL.1, Matrix.mulVec_smul]`. Use extensionality with `i j`. Simplify using `only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem actAB_mem_isoA {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} (H : Plane E n n₁)
    (H' : Plane E d d₁) {l : (AE F E)ˣ} {g₀ : UA σ X₁.J} {m : UA σ X.J} (hL : IsLevi (W₁ := X₁) H l g₀ m)
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : u ∈ isoA H H') :
    actAB (cA σ) ((m, 1) : UA σ X.J × UA σ W.J) u ∈ isoA H H' := by
  have e1 : ∀ v : Matrix (Fin n) (Fin d) (AE F E), actAB (cA σ) ((m, 1) : UA σ X.J × UA σ W.J) v = mat m * v := by
    intro v
    simp [actAB, mat]
  rw [e1]
  rcases hu with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · exact Or.inl ⟨mat m *ᵥ y, mul_vecMulVec' _ _ _⟩
  · refine Or.inr ⟨l.1 • z, ?_⟩
    rw [mul_vecMulVec', hL.1, Matrix.mulVec_smul]
    ext i j
    simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    ring

/- English proof (translation)
Simplify using `only [actAB, shiftA, OneMemClass.coe_one, Units.val_one, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_smul, one_smul]`. Rewrite using `[show ((m : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) = mat m from rfl, mul_vecMulVec', hL.1, Matrix.smul_vecMulVec, smul_smul, Units.inv_mul, one_smul]`.
-/
theorem actAB_shiftA {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} (H : Plane E n n₁)
    (H' : Plane E d d₁) {l : (AE F E)ˣ} {g₀ : UA σ X₁.J} {m : UA σ X.J} (hL : IsLevi (W₁ := X₁) H l g₀ m) :
    actAB (cA σ) ((m, 1) : UA σ X.J × UA σ W.J) (shiftA H H' l⁻¹) = shiftA H H' 1 := by
  simp only [actAB, shiftA, OneMemClass.coe_one, Units.val_one, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_smul,
    one_smul]
  rw [show ((m : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) = mat m from rfl, mul_vecMulVec', hL.1,
    Matrix.smul_vecMulVec, smul_smul, Units.inv_mul, one_smul]

/- English proof (translation)
Establish `hS` using `hpair.weil.isUSplitting`. Establish `hS₁` using `hpair₁.weil.isUSplitting`. Set `f : Fn F n d →ₗ[ℂ] Fn F n₁ d₁` to `om₁ (g₀⁻¹, 1) ∘ₗ e ∘ₗ om (m, 1)`. Establish `hinv : ∀ ψ : Fn F n₁ d₁, om₁ (g₀, 1) (om₁ (g₀⁻¹, 1) ψ) = ψ`. Introduce `ψ`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one, Prod.mk_one_one, map_one, Module.End.one_apply]`. Establish `hact : ∀ z : Matrix (Fin n₁) (Fin d₁) (AE F E), actAB (cA σ) ((m, 1) : UA σ X.J × UA σ W.J) (incM F H.ι * z * (incM F H'.ι)ᵀ) = incM F H.ι * actAB (cA σ) ((g₀, 1) : UA σ X₁.J × UA σ W₁.J) z * (incM F H'.ι)ᵀ`. Introduce `z`. Simplify using `only [actAB, OneMemClass.coe_one, Units.val_one, Matrix.transpose_one, Matrix.mul_one]`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc]`.

Use `congr 2`. Conclude with `hL.2.2`. Establish `hback : ∀ z : Matrix (Fin n₁) (Fin d₁) (AE F E), actAB (cA σ) ((g₀⁻¹, 1) : UA σ X₁.J × UA σ W₁.J) (actAB (cA σ) ((g₀, 1) : UA σ X₁.J × UA σ W₁.J) z) = z`. Introduce `z`. Simplify using `only [actAB, OneMemClass.coe_one, Units.val_one, Matrix.transpose_one, Matrix.mul_one, InvMemClass.coe_inv]`.

Rewrite using `[← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]`. Take `⟨c, hc⟩` from `GlobalTheory.ThK.EvLawUniq.eq_smul_isEv hP F E σ B n d n₁ d₁ X W X₁ W₁ M χX χW om r s r' s' hpair H H' j₀ j₁ i₀ i₁ M₁ hH hH' hpair₁.good e hev f (fun z Φ hΦ => by`. Establish `h1` using `hS.pres (m, 1) Φ hΦ`. Establish `h2` using `hev.maps _ h1`. Use `show om₁ (g₀⁻¹, 1) (e (om (m, 1) (M.co.rho B.ψ _ Φ))) = M₁.co.rho B.ψ z (om₁ (g₀⁻¹, 1) (e (om (m, 1) Φ)))`.

Rewrite using `[hS.impl (m, 1) _ Φ hΦ, hact, hev.Heisenberg₂ _ _ h1, hS₁.impl (g₀⁻¹, 1) _ _ h2, hback])`. Use the proof step `(fun u hu Φ hΦ => by`. Establish `h1` using `hS.pres (m, 1) Φ hΦ`. Use `show om₁ (g₀⁻¹, 1) (e (om (m, 1) (M.co.rho B.ψ u Φ))) = om₁ (g₀⁻¹, 1) (e (om (m, 1) Φ))`. Rewrite using `[hS.impl (m, 1) _ Φ hΦ, hev.inv _ (actAB_mem_isoA H H' hL hu) _ h1])`.

Use `⟨c, fun Φ hΦ => ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (om₁ (g₀, 1)) (hc Φ hΦ)`. Rewrite `h` using `[map_smul]`. Rewrite using `[← h]`. Conclude with `(hinv _).symm`.
-/
theorem exists_levi_const (hP : GlobalTheory.FunPr.Hypotheses₂) {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁}
    {W₁ : Spc F E d₁} {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}
    (hpair : IsPair B M χX χW om r s r' s') {H : Plane E n n₁} {H' : Plane E d d₁} {j₀ j₁ i₀ i₁ : ℕ}
    {M₁ : Model σ X₁ W₁} {om₁ : Rep σ X₁ W₁} {r₁ s₁ r₁' s₁' : ℕ}
    (hH : H.IsAdapted σ B X X₁ j₀ j₁) (hH' : H'.IsAdapted σ B W W₁ i₀ i₁) (hpair₁ : IsPair B M₁ χX χW om₁ r₁ s₁ r₁' s₁')
    {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} (hev : IsEv B M M₁ H.ι H'.ι (isoA H H') e)
    {l : (AE F E)ˣ} {g₀ : UA σ X₁.J} {m : UA σ X.J} (hL : IsLevi (W₁ := X₁) H l g₀ m) :
    ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (m, 1) Φ) = c • om₁ (g₀, 1) (e Φ) := by
  have hS := hpair.weil.isUSplitting
  have hS₁ := hpair₁.weil.isUSplitting
  let f : Fn F n d →ₗ[ℂ] Fn F n₁ d₁ := om₁ (g₀⁻¹, 1) ∘ₗ e ∘ₗ om (m, 1)
  have hinv : ∀ ψ : Fn F n₁ d₁, om₁ (g₀, 1) (om₁ (g₀⁻¹, 1) ψ) = ψ := by
    intro ψ
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one, Prod.mk_one_one, map_one,
      Module.End.one_apply]
  have hact : ∀ z : Matrix (Fin n₁) (Fin d₁) (AE F E),
      actAB (cA σ) ((m, 1) : UA σ X.J × UA σ W.J) (incM F H.ι * z * (incM F H'.ι)ᵀ) =
        incM F H.ι * actAB (cA σ) ((g₀, 1) : UA σ X₁.J × UA σ W₁.J) z * (incM F H'.ι)ᵀ := by
    intro z
    simp only [actAB, OneMemClass.coe_one, Units.val_one, Matrix.transpose_one, Matrix.mul_one]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    congr 2
    exact hL.2.2
  have hback : ∀ z : Matrix (Fin n₁) (Fin d₁) (AE F E),
      actAB (cA σ) ((g₀⁻¹, 1) : UA σ X₁.J × UA σ W₁.J) (actAB (cA σ) ((g₀, 1) : UA σ X₁.J × UA σ W₁.J) z) = z := by
    intro z
    simp only [actAB, OneMemClass.coe_one, Units.val_one, Matrix.transpose_one, Matrix.mul_one, InvMemClass.coe_inv]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  obtain ⟨c, hc⟩ := GlobalTheory.ThK.EvLawUniq.eq_smul_isEv hP F E σ B n d n₁ d₁ X W X₁ W₁ M χX χW om r s r' s' hpair H H'
    j₀ j₁ i₀ i₁ M₁ hH hH' hpair₁.good e hev f
    (fun z Φ hΦ => by
      have h1 := hS.pres (m, 1) Φ hΦ
      have h2 := hev.maps _ h1
      show om₁ (g₀⁻¹, 1) (e (om (m, 1) (M.co.rho B.ψ _ Φ))) = M₁.co.rho B.ψ z (om₁ (g₀⁻¹, 1) (e (om (m, 1) Φ)))
      rw [hS.impl (m, 1) _ Φ hΦ, hact, hev.Heisenberg₂ _ _ h1, hS₁.impl (g₀⁻¹, 1) _ _ h2, hback])
    (fun u hu Φ hΦ => by
      have h1 := hS.pres (m, 1) Φ hΦ
      show om₁ (g₀⁻¹, 1) (e (om (m, 1) (M.co.rho B.ψ u Φ))) = om₁ (g₀⁻¹, 1) (e (om (m, 1) Φ))
      rw [hS.impl (m, 1) _ Φ hΦ, hev.inv _ (actAB_mem_isoA H H' hL hu) _ h1])
  refine ⟨c, fun Φ hΦ => ?_⟩
  have h := congrArg (om₁ (g₀, 1)) (hc Φ hΦ)
  rw [map_smul] at h
  rw [← h]
  exact (hinv _).symm

def reM {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (Y : Spc F E n) : Model σ (reS X Y) W :=
  ⟨M.co, M.vac, M.μ, M.dom⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.rat, h.vac, h.std, h.haar, h.dom⟩`.
-/
theorem reM_isGood {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} (Y : Spc F E n) {ψ : AddChar (AF F) ℂ}
    (h : M.IsGood ψ) : (reM M Y).IsGood ψ :=
  ⟨h.rat, h.vac, h.std, h.haar, h.dom⟩

/- English proof (translation)
The claim follows from `h`.
-/
theorem reM_isWeil {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} (Y : Spc F E n) {ψ : AddChar (AF F) ℂ}
    {χX χW : Chr F E} {om : Rep σ X W} (h : M.IsWeil ψ χX χW om) : (reM M Y).IsWeil ψ χX χW om := h

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.maps, h.Heisenberg₂, h.inv, h.loc⟩`.
-/
theorem reM_isEv {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E}
    {M : Model σ X W} (Y : Spc F E n) {M₁ : Model σ X₁ W₁} {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E}
    {I : Set (Matrix (Fin n) (Fin d) (AE F E))} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} (h : IsEv B M M₁ ι ι' I e) :
    IsEv B (reM M Y) M₁ ι ι' I e :=
  ⟨h.maps, h.Heisenberg₂, h.inv, h.loc⟩

end GlobalTheory.XTermLevi

open GlobalTheory.XTermLevi in

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B a b G G₁ H H' cfg X om om' om₁ om₁' T T₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hev Φ hΦ h`. Take `⟨hs1, hX₁⟩` from `GlobalTheory.HermPlaneComplSig.isHerm_complement F E σ B a n₁ (reS G.V V₂) X₁ H₀ j₀ j₁ (a - G.p) G.p T.base hV₂ hH₀`. Establish `hn : a = n₁ + 2` using `hH₀.rank`. Establish `hresX : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range X.β n₁`. Use `resEtaPow_sub_two T.chars.resβ (by omega)` as an intermediate fact.

Rewrite `this` using `[show a - 2 = n₁ by omega]`. Then use the resulting hypothesis. Take `⟨om₂, hom₂⟩` from `GlobalTheory.WeilExGen.exists_isWeil hKP.base F E σ B T.base n₁ (a + b) X₁ G₁.W _ _ _ _ hX₁ T₁.geo.hW M₂ hM₂ X.β (X.β / X.α) T.chars.heckeβ (isHecke_div T.chars.heckeβ T.chars.heckeα) hresX (resEtaPow_div T₁.chars.resβ T₁.chars.resα)`. Establish `P₂ : IsPair B M₂ X.β (X.β / X.α) om₂ (a - G.p - 1) (G.p - 1) _ _` using `⟨T.base, hX₁, T₁.geo.hW, hM₂, T.chars.heckeβ, isHecke_div T.chars.heckeβ T.chars.heckeα, hresX, resEtaPow_div T₁.chars.resβ T₁.chars.resα, hom₂⟩`. Use `⟨om₂, X.β, X.β / X.α, a - G.p - 1, G.p - 1, _, _, P₂, Or.inl ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `T.geo.eBig`.

Establish `h2` using `cfg.eq`. Establish `h3 : min (a - G.p - 1) (G.p - 1) ≤ G.p - 1` using `min_le_right _ _`. Use linear arithmetic over natural numbers and integers. Establish `P : IsPair B (reM G.M V₂) X.β (X.β / X.α) om (a - G.p) G.p _ _` using `⟨T.base, hV₂, T.geo.hW, reM_isGood V₂ T.geo.hM, T.chars.heckeβ, isHecke_div T.chars.heckeβ T.chars.heckeα, T.chars.resβ, resEtaPow_div T.chars.resβ T.chars.resα, reM_isWeil V₂ T.weil⟩`. Establish `hev' : IsEv B (reM G.M V₂) M₂ H₀.ι H'.ι (isoA H₀ H') e₂` using `reM_isEv V₂ hev`.

Introduce `l g₀ m hL k`. Establish `hS` using `T.weil.isUSplitting`. Take `⟨c, hc0⟩` from `exists_levi_const (X := reS G.V V₂) hKP.base P hH₀ cfg.hH' P₂ hev' (m := m) hL`. Establish `hcn` using `GlobalTheory.T.pair_double_adapted_restriction hKP F E σ B a (a + (b + 2)) n₁ (a + b) (reS G.V V₂) G.W X₁ G₁.W (reM G.M V₂) X.β (X.β / X.α) om _ _ _ _ P H₀ H' j₀ j₁ a (a + b + 1) M₂ om₂ _ _ _ _ hH₀ cfg.hH' P₂ e₂ hev' l g₀ m hL c hc0`. Establish `hc : ∀ Ψ ∈ schA F (Fin a × Fin (a + (b + 2))), e₂ (om (m, 1) Ψ) = c • om₂ (g₀, 1) (e₂ Ψ)` using `fun Ψ hΨ => hc0 Ψ hΨ`.

Establish `hΨ : om (k, h) Φ ∈ schA F (Fin a × Fin (a + (b + 2)))` using `hS.pres _ _ (GlobalTheory.ConeTermCont.polData_le B G.M T.geo.hM hΦ)`. Establish `hΨ'` using `GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ T.base.std (shiftA H₀ H' l⁻¹) _ hΨ`. Establish `h1 : om (m * k, h) Φ = om (m, 1) (om (k, h) Φ)`. Rewrite using `[← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]`. Establish `h2 : G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (m, 1) (om (k, h) Φ)) = om (m, 1) (G.M.co.rho B.ψ (shiftA H₀ H' l⁻¹) (om (k, h) Φ))`.

Rewrite using `[hS.impl (m, 1) _ _ hΨ, actAB_shiftA H₀ H' hL]`. Rewrite using `[h1, h2, hc _ hΨ', thetaSum_smul, enorm_mul, ← ofReal_norm_eq_enorm c, hcn]`.
-/
theorem GlobalTheory.ThK.xTerm_levi_norm : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (V₂ : Spc F E a) (n₁ : ℕ) (X₁ : Spc F E n₁) (H₀ : Plane E a n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ G₁.W) (e₂ : Fn F a (a + (b + 2)) →ₗ[ℂ] Fn F n₁ (a + b)), (reS G.V V₂).IsHerm σ B (a - G.p) G.p → H₀.IsAdapted σ B (reS G.V V₂) X₁ j₀ j₁ → M₂.IsGood B.ψ → IsEv B G.M M₂ H₀.ι H'.ι (isoA H₀ H') e₂ → ∀ Φ ∈ PolData B G.M, ∀ h : UA σ G.W.J, ∃ (om₂ : Rep σ X₁ G₁.W) (χX χW : Chr F E) (r s r' s' : ℕ), IsPair B M₂ χX χW om₂ r s r' s' ∧ (a + b + 2 * min r s < 2 * n₁ ∨ min r s = 0) ∧ ∀ (l : (AE F E)ˣ) (g₀ : UA σ X₁.J) (m : UA σ G.V.J), IsLevi (W₁ := X₁) H₀ l g₀ m → ∀ k : UA σ G.V.J, ‖thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (m * k, h) Φ)))‖ₑ = ENNReal.ofReal ((absE F E l : ℝ) ^ (((a + b : ℕ) : ℝ) / 2)) * ‖thetaSum F (om₂ (g₀, 1) (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' l⁻¹) (om (k, h) Φ))))‖ₑ := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' cfg X om om' om₁ om₁' T T₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hev Φ hΦ h

  obtain ⟨hs1, hX₁⟩ := GlobalTheory.HermPlaneComplSig.isHerm_complement F E σ B a n₁ (reS G.V V₂) X₁ H₀ j₀ j₁ (a - G.p) G.p T.base hV₂ hH₀
  have hn : a = n₁ + 2 := hH₀.rank
  have hresX : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range X.β n₁ := by
    have := resEtaPow_sub_two T.chars.resβ (by omega)
    rwa [show a - 2 = n₁ by omega] at this
  obtain ⟨om₂, hom₂⟩ := GlobalTheory.WeilExGen.exists_isWeil hKP.base F E σ B T.base n₁ (a + b) X₁ G₁.W _ _ _ _ hX₁ T₁.geo.hW M₂ hM₂
    X.β (X.β / X.α) T.chars.heckeβ (isHecke_div T.chars.heckeβ T.chars.heckeα) hresX
    (resEtaPow_div T₁.chars.resβ T₁.chars.resα)
  have P₂ : IsPair B M₂ X.β (X.β / X.α) om₂ (a - G.p - 1) (G.p - 1) _ _ :=
    ⟨T.base, hX₁, T₁.geo.hW, hM₂, T.chars.heckeβ, isHecke_div T.chars.heckeβ T.chars.heckeα, hresX,
      resEtaPow_div T₁.chars.resβ T₁.chars.resα, hom₂⟩
  refine ⟨om₂, X.β, X.β / X.α, a - G.p - 1, G.p - 1, _, _, P₂, Or.inl ?_, ?_⟩
  · have h1 := T.geo.eBig
    have h2 := cfg.eq
    have h3 : min (a - G.p - 1) (G.p - 1) ≤ G.p - 1 := min_le_right _ _
    omega

  have P : IsPair B (reM G.M V₂) X.β (X.β / X.α) om (a - G.p) G.p _ _ :=
    ⟨T.base, hV₂, T.geo.hW, reM_isGood V₂ T.geo.hM, T.chars.heckeβ, isHecke_div T.chars.heckeβ T.chars.heckeα,
      T.chars.resβ, resEtaPow_div T.chars.resβ T.chars.resα, reM_isWeil V₂ T.weil⟩
  have hev' : IsEv B (reM G.M V₂) M₂ H₀.ι H'.ι (isoA H₀ H') e₂ := reM_isEv V₂ hev
  intro l g₀ m hL k
  have hS := T.weil.isUSplitting
  obtain ⟨c, hc0⟩ := exists_levi_const (X := reS G.V V₂) hKP.base P hH₀ cfg.hH' P₂ hev' (m := m) hL
  have hcn := GlobalTheory.T.pair_double_adapted_restriction hKP F E σ B a (a + (b + 2)) n₁ (a + b) (reS G.V V₂) G.W X₁ G₁.W (reM G.M V₂) X.β (X.β / X.α) om _ _ _ _ P H₀ H'
    j₀ j₁ a (a + b + 1) M₂ om₂ _ _ _ _ hH₀ cfg.hH' P₂ e₂ hev' l g₀ m hL c hc0
  have hc : ∀ Ψ ∈ schA F (Fin a × Fin (a + (b + 2))), e₂ (om (m, 1) Ψ) = c • om₂ (g₀, 1) (e₂ Ψ) :=
    fun Ψ hΨ => hc0 Ψ hΨ
  have hΨ : om (k, h) Φ ∈ schA F (Fin a × Fin (a + (b + 2))) :=
    hS.pres _ _ (GlobalTheory.ConeTermCont.polData_le B G.M T.geo.hM hΦ)
  have hΨ' := GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ T.base.std (shiftA H₀ H' l⁻¹) _ hΨ
  have h1 : om (m * k, h) Φ = om (m, 1) (om (k, h) Φ) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  have h2 : G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (m, 1) (om (k, h) Φ)) =
      om (m, 1) (G.M.co.rho B.ψ (shiftA H₀ H' l⁻¹) (om (k, h) Φ)) := by
    rw [hS.impl (m, 1) _ _ hΨ, actAB_shiftA H₀ H' hL]
  rw [h1, h2, hc _ hΨ', thetaSum_smul, enorm_mul, ← ofReal_norm_eq_enorm c, hcn]
