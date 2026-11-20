import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicator
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ParabolicDerivativeFixesSplitVector
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GradientFixesSplitVector
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorStatement

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
noncomputable section
namespace GlobalTheory.SplitScalar
/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B a a' G X om om' hTr v hsp hT hψ h2 hvac k hk c hc`. Take `⟨-, dd, omd, hdc, hws, hres⟩` from `hTr.weil'.1`. Take `⟨R, hR0, hR⟩` from `GlobalTheory.RestWitness.exists_rest (Fin a' × Fin (a + a')) v`. Establish `hV` using `hTr.geo.hM'.vac v`. Establish `hSB : G.M'.vac v ∈ SB _` using `hV.1`.

Establish `hne : G.M'.vac v ≠ 0` using `hV.2.1`. Establish `hRv` using `hR _ hSB`. Use `set Ψ := tens (evFin F v) (G.M'.vac v) R with hΨdef`. Establish `hΨ : Ψ ∈ schA F _` using `hRv.2`. Establish `hΨ' : (fun x => star (Ψ x)) ∈ schA F _` using `GlobalTheory.SchAConj.star_mem_schA F _ Ψ hΨ`.

Set `H : Subgroup (GlobalTheory.InertDbl.UD σ G.W)` to `{ carrier := {g | omd g (GlobalTheory.InertDbl.dblFun Ψ) = GlobalTheory.InertDbl.dblFun Ψ} one_mem' := by simp mul_mem' := fun {x y} hx hy => by`. Simplify using `only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *`. Rewrite using `[hy, hx]`. Use the proof step `inv_mem' := fun {x} hx => by`. Simplify using `only [Set.mem_setOf_eq] at *`.

Use `conv_lhs => rw [← hx]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }`. Establish `hgen` using `(GlobalTheory.T.scalarSq_smul_matrix_supported_at_place) F E σ B a a' G X om om' hTr v hsp hψ h2 k hk`. Establish `hle : Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v) ≤ H`. Rewrite using `[Subgroup.closure_le]`.

Introduce and unpack `g (hg | hg)`. Conclude with `(_root_.GlobalTheory.T.split_double_parabolic_derivative_fixed) hP F E σ B a a' G X om om' hTr v hsp hT hψ h2 hvac dd omd hdc hws R hR0 hRv g hg`. Conclude with `(_root_.GlobalTheory.T.nabla_preserves_split_fixed) hP F E σ B a a' G X om om' hTr v hsp hT hψ h2 hvac dd omd hdc hws R hR0 hRv g hg`. Establish `hfix : omd (GlobalTheory.InertDbl.inlD σ G.W k) (GlobalTheory.InertDbl.dblFun Ψ) = GlobalTheory.InertDbl.dblFun Ψ` using `hle hgen`. Establish `hact : om' (1, k) Ψ = c • Ψ`.

Rewrite using `[hΨdef, hc R hRv]`. Use function extensionality and compare the values at `x`. Simplify using `[tens, mul_assoc]`. Establish `hr` using `hres k (GlobalTheory.InertDbl.inlD σ G.W k) rfl Ψ hΨ (fun x => star (Ψ x)) hΨ'`. Simplify using `only [MonoidHom.comp_apply, MonoidHom.inr_apply] at hr`.

Rewrite `hr` using `[hact]`. Establish `key : c • GlobalTheory.InertDbl.dblFun Ψ = GlobalTheory.InertDbl.dblFun Ψ`. Establish `e1 : omd (GlobalTheory.InertDbl.inlD σ G.W k) (GlobalTheory.InertDbl.dblFun Ψ) = c • GlobalTheory.InertDbl.dblFun Ψ`. Unfold `GlobalTheory.InertDbl.dblFun`. Rewrite using `[hr]`.

Use function extensionality and compare the values at `x`. Simplify using `only [boxFun, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← e1, hfix]`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y, G.M'.vac v y ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hne (funext h)`. Set `x : Fin a' × Fin (a + a') → AF F` to `fun i => GlobalTheory.LatVac.liftV v (y i)`. Establish `hRx : R x = R 0`.

Use `hRv.1 0 x (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)` as an intermediate fact. Simplify using `using this`. Establish `hΨx : Ψ x ≠ 0`. Simplify using `only [hΨdef, tens, x, GlobalTheory.LatVac.evFin_liftV, hRx]`. Conclude with `mul_ne_zero hy hR0`.

Establish `h2'` using `congrFun key (Sum.elim x x)`. Simplify using `only [GlobalTheory.InertDbl.dblFun, boxFun, Pi.smul_apply, smul_eq_mul] at h2'`. Establish `hz : Ψ x * star (Ψ x) ≠ 0` using `mul_ne_zero hΨx (star_ne_zero.mpr hΨx)`. Establish `h3 : (Sum.elim x x ∘ Sum.inl : Fin a' × Fin (a + a') → AF F) = x` using `rfl`. Establish `h4 : (Sum.elim x x ∘ Sum.inr : Fin a' × Fin (a + a') → AF F) = x` using `rfl`.

Rewrite `h2'` using `[h3, h4]`. Conclude with `(mul_eq_right₀ hz).mp h2'`.
-/
theorem weil_scalar_eq_one_of_split : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∀ c : ℂ, Acts (evFin F v) (om' (1, k)) (G.M'.vac v) (c • G.M'.vac v) → c = 1 := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v hsp hT hψ h2 hvac k hk c hc
  obtain ⟨-, dd, omd, hdc, hws, hres⟩ := hTr.weil'.1
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (Fin a' × Fin (a + a')) v
  have hV := hTr.geo.hM'.vac v
  have hSB : G.M'.vac v ∈ SB _ := hV.1
  have hne : G.M'.vac v ≠ 0 := hV.2.1
  have hRv := hR _ hSB
  set Ψ := tens (evFin F v) (G.M'.vac v) R with hΨdef
  have hΨ : Ψ ∈ schA F _ := hRv.2
  have hΨ' : (fun x => star (Ψ x)) ∈ schA F _ := GlobalTheory.SchAConj.star_mem_schA F _ Ψ hΨ
  let H : Subgroup (GlobalTheory.InertDbl.UD σ G.W) :=
    { carrier := {g | omd g (GlobalTheory.InertDbl.dblFun Ψ) = GlobalTheory.InertDbl.dblFun Ψ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hgen := (GlobalTheory.T.scalarSq_smul_matrix_supported_at_place) F E σ B a a' G X om om' hTr v hsp hψ h2 k hk
  have hle : Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v) ≤ H := by
    rw [Subgroup.closure_le]
    rintro g (hg | hg)
    · exact (_root_.GlobalTheory.T.split_double_parabolic_derivative_fixed) hP F E σ B a a' G X om om' hTr v hsp hT hψ h2 hvac dd omd hdc hws R hR0 hRv g hg
    · exact (_root_.GlobalTheory.T.nabla_preserves_split_fixed) hP F E σ B a a' G X om om' hTr v hsp hT hψ h2 hvac dd omd hdc hws R hR0 hRv g hg
  have hfix : omd (GlobalTheory.InertDbl.inlD σ G.W k) (GlobalTheory.InertDbl.dblFun Ψ) = GlobalTheory.InertDbl.dblFun Ψ := hle hgen
  have hact : om' (1, k) Ψ = c • Ψ := by
    rw [hΨdef, hc R hRv]
    funext x
    simp [tens, mul_assoc]
  have hr := hres k (GlobalTheory.InertDbl.inlD σ G.W k) rfl Ψ hΨ (fun x => star (Ψ x)) hΨ'
  simp only [MonoidHom.comp_apply, MonoidHom.inr_apply] at hr
  rw [hact] at hr
  have key : c • GlobalTheory.InertDbl.dblFun Ψ = GlobalTheory.InertDbl.dblFun Ψ := by
    have e1 : omd (GlobalTheory.InertDbl.inlD σ G.W k) (GlobalTheory.InertDbl.dblFun Ψ) = c • GlobalTheory.InertDbl.dblFun Ψ := by
      unfold GlobalTheory.InertDbl.dblFun
      rw [hr]
      funext x
      simp only [boxFun, Pi.smul_apply, smul_eq_mul]
      ring
    rw [← e1, hfix]
  obtain ⟨y, hy⟩ : ∃ y, G.M'.vac v y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  let x : Fin a' × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
  have hRx : R x = R 0 := by
    have := hRv.1 0 x (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
    simpa using this
  have hΨx : Ψ x ≠ 0 := by
    simp only [hΨdef, tens, x, GlobalTheory.LatVac.evFin_liftV, hRx]
    exact mul_ne_zero hy hR0
  have h2' := congrFun key (Sum.elim x x)
  simp only [GlobalTheory.InertDbl.dblFun, boxFun, Pi.smul_apply, smul_eq_mul] at h2'
  have hz : Ψ x * star (Ψ x) ≠ 0 := mul_ne_zero hΨx (star_ne_zero.mpr hΨx)
  have h3 : (Sum.elim x x ∘ Sum.inl : Fin a' × Fin (a + a') → AF F) = x := rfl
  have h4 : (Sum.elim x x ∘ Sum.inr : Fin a' × Fin (a + a') → AF F) = x := rfl
  rw [h3, h4] at h2'
  exact (mul_eq_right₀ hz).mp h2'
end GlobalTheory.SplitScalar
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.SplitScalar.weil_scalar_eq_one_of_split | exact _root_.GlobalTheory.SplitScalar.weil_scalar_eq_one_of_split | (intros; apply _root_.GlobalTheory.SplitScalar.weil_scalar_eq_one_of_split <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.split_place_weil_scalar_trivial : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∀ c : ℂ, Acts (evFin F v) (om' (1, k)) (G.M'.vac v) (c • G.M'.vac v) → c = 1 := by
  first | exact @_root_.GlobalTheory.SplitScalar.weil_scalar_eq_one_of_split | exact _root_.GlobalTheory.SplitScalar.weil_scalar_eq_one_of_split | (intros; apply _root_.GlobalTheory.SplitScalar.weil_scalar_eq_one_of_split <;> assumption)
end
