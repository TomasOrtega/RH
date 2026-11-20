import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypInvLe
import Formalism.LocalToGlobal.GroupLattices.FockModels.SwRowGenMonomial
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf

noncomputable section

namespace Formalism.MainNotions.G.CmpJ.PFormsCl

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms MvPolynomial NumberField IsDedekindDomain

section Tr

variable {ι : Type} [Fintype ι] {n : ℕ}

/- English proof (translation)
Introduce `a b hab`. Use `lam.anti hab` as an intermediate fact. Unfold `DomWeight.natW`. Conclude with `Int.toNat_le_toNat (by omega)`.
-/
theorem foNat_anti (lam : DomWeight n) : Antitone lam.natW := by
  intro a b hab
  have := lam.anti hab
  unfold DomWeight.natW
  exact Int.toNat_le_toNat (by omega)

/- English proof (translation)
Unfold `delSq at hq ⊢`. Rewrite `hq`, the goal using `[Formalism.L2.G.Model.sw_weyl_eq ℂ n n le_rfl _ (foNat_anti lam)]`. Conclude with `Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n _ g q hq`.
-/
theorem foRow_delSq (lam : DomWeight n) (g : Matrix (Fin n) (Fin n) ℂ) {q : MvPolynomial (Fin n × Fin n) ℂ}
    (hq : q ∈ delSq ℂ n lam) : Formalism.GradedWeylDivisibility.rowAct ℂ g q ∈ delSq ℂ n lam := by
  unfold delSq at hq ⊢
  rw [Formalism.L2.G.Model.sw_weyl_eq ℂ n n le_rfl _ (foNat_anti lam)] at hq ⊢
  exact Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n _ g q hq

def foTr {Gm : ι → Matrix (Fin n) (Fin n) ℂ} (g : ι → Matrix (Fin n) (Fin n) ℂ) (hg : ∀ τ, IsUnit (g τ).det)
    (y : Formalism.L2.Forms.Frames Gm) : Formalism.L2.Forms.Frames Gm :=
  (⟨fun τ => g τ * y.1 τ, fun τ => by rw [Matrix.det_mul]; exact (hg τ).mul (y.2 τ)⟩ :
    {y : ι → Matrix (Fin n) (Fin n) ℂ // ∀ τ, IsUnit (y τ).det})

def blockRowSubstitutionAlgHom (g : ι → Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (ι × Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ :=
  aeval fun x => ∑ c : Fin n, C (g x.1 x.2.1 c) * X (x.1, c, x.2.2)

/- English proof (translation)
Simplify using `only [blockRowSubstitutionAlgHom, aeval_X]`.
-/
theorem blockRowSubstitution_X (g : ι → Matrix (Fin n) (Fin n) ℂ) (x : ι × Fin n × Fin n) :
    blockRowSubstitutionAlgHom g (X x) = ∑ c : Fin n, C (g x.1 x.2.1 c) * X (x.1, c, x.2.2) := by
  simp only [blockRowSubstitutionAlgHom, aeval_X]

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on`. Use `next a => simp [blockRowSubstitutionAlgHom]`. Use `next p q hp hq => simp only [map_add, hp, hq]`. Use `next p x hp => simp only [map_mul, hp, blockRowSubstitution_X, eval_X, map_sum, eval_C]`.
-/
theorem eval_blockRowSubstitution (g : ι → Matrix (Fin n) (Fin n) ℂ) (z : ι × Fin n × Fin n → ℂ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    eval z (blockRowSubstitutionAlgHom g P) = eval (fun x => ∑ c, g x.1 x.2.1 c * z (x.1, c, x.2.2)) P := by
  induction P using MvPolynomial.induction_on
  next a => simp [blockRowSubstitutionAlgHom]
  next p q hp hq => simp only [map_add, hp, hq]
  next p x hp => simp only [map_mul, hp, blockRowSubstitution_X, eval_X, map_sum, eval_C]

/- English proof (translation)
Establish `h : (blockRowSubstitutionAlgHom g).comp (rename (Prod.mk τ)) = (rename (Prod.mk τ)).comp (Formalism.GradedWeylDivisibility.rowAct ℂ (r` using `n) (n := n) (g τ)) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `[blockRowSubstitutionAlgHom, Formalism.GradedWeylDivisibility.rowAct, rename_X, map_sum]`. Conclude with `congrArg (fun φ => φ q) h`.
-/
theorem blockRowSubstitution_rename (g : ι → Matrix (Fin n) (Fin n) ℂ) (τ : ι) (q : MvPolynomial (Fin n × Fin n) ℂ) :
    blockRowSubstitutionAlgHom g (rename (Prod.mk τ) q) = rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.rowAct ℂ (g τ) q) := by
  have h : (blockRowSubstitutionAlgHom g).comp (rename (Prod.mk τ)) = (rename (Prod.mk τ)).comp (Formalism.GradedWeylDivisibility.rowAct ℂ (r := n) (n := n) (g τ)) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [blockRowSubstitutionAlgHom, Formalism.GradedWeylDivisibility.rowAct, rename_X, map_sum]
  exact congrArg (fun φ => φ q) h

/- English proof (translation)
Simplify using `only [ten, map_prod, blockRowSubstitution_rename]`.
-/
theorem blockRowSubstitution_tensor (g : ι → Matrix (Fin n) (Fin n) ℂ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    blockRowSubstitutionAlgHom g (ten f) = ten fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (g τ) (f τ) := by
  simp only [ten, map_prod, blockRowSubstitution_rename]

/- English proof (translation)
Establish `h : CSpan lam ≤ (CSpan lam).comap (blockRowSubstitutionAlgHom g).toLinearMap`. Unfold `CSpan`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Conclude with `Submodule.subset_span ⟨fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (g τ) (f τ), fun τ => foRow_delSq _ _ (hf τ), blockRowSubstitution_tensor g f⟩`.

Conclude with `h hP`.
-/
theorem blockRowSubstitution_preserves_complexSpan (lam : ι → DomWeight n) (g : ι → Matrix (Fin n) (Fin n) ℂ) {P : MvPolynomial (ι × Fin n × Fin n) ℂ}
    (hP : P ∈ CSpan lam) : blockRowSubstitutionAlgHom g P ∈ CSpan lam := by
  have h : CSpan lam ≤ (CSpan lam).comap (blockRowSubstitutionAlgHom g).toLinearMap := by
    unfold CSpan
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact Submodule.subset_span ⟨fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (g τ) (f τ), fun τ => foRow_delSq _ _ (hf τ), blockRowSubstitution_tensor g f⟩
  exact h hP

/- English proof (translation)
Take `⟨P, hP, rfl⟩` from `Submodule.mem_map.1 hv`. Establish `h : (fun y => fnOf Gm (shiftOf lam) 1 P (foTr g hg y)) = (∏ τ, (g τ).det ^ shiftOf lam τ) • fnOf Gm (shiftOf lam) 1 (blockRowSubstitutionAlgHom g P)`. Use function extensionality and compare the values at `y`. Simplify using `only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul, foTr, Pi.one_apply, Matrix.one_mul, eval_blockRowSubstitution, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]`. Simplify using `only [Matrix.mul_apply]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (blockRowSubstitution_preserves_complexSpan lam g hP))`.
-/
theorem foValC_tr {Gm : ι → Matrix (Fin n) (Fin n) ℂ} (lam : ι → DomWeight n) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (hg : ∀ τ, IsUnit (g τ).det) {v : Formalism.L2.Forms.Frames Gm → ℂ} (hv : v ∈ ValC Gm lam) :
    (fun y => v (foTr g hg y)) ∈ ValC Gm lam := by
  obtain ⟨P, hP, rfl⟩ := Submodule.mem_map.1 hv
  have h : (fun y => fnOf Gm (shiftOf lam) 1 P (foTr g hg y)) =
      (∏ τ, (g τ).det ^ shiftOf lam τ) • fnOf Gm (shiftOf lam) 1 (blockRowSubstitutionAlgHom g P) := by
    funext y
    simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul, foTr, Pi.one_apply, Matrix.one_mul, eval_blockRowSubstitution,
      Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]
    simp only [Matrix.mul_apply]
    ring
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (blockRowSubstitution_preserves_complexSpan lam g hP))

end Tr

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T fT : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

/- English proof (translation)
Rewrite using `[show a⁻¹ * b * y * (l * k⁻¹) = a⁻¹ * (b * y * l) * k⁻¹ by group, ← h]`. Use `group`.
-/
theorem foGrp {Γ : Type} [Group Γ] (a b y k l : Γ) (h : a * y * k = b * y * l) : y = a⁻¹ * b * y * (l * k⁻¹) := by
  rw [show a⁻¹ * b * y * (l * k⁻¹) = a⁻¹ * (b * y * l) * k⁻¹ by group, ← h]
  group

/- English proof (translation)
Establish `h` using `((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).map (emb τ)`. Rewrite `h` using `[RingHom.map_det]`. Then use the resulting hypothesis.
-/
theorem foInf_unit (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (τ : ι) : IsUnit (atInf emb γ.1 τ).det := by
  have h := ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).map (emb τ)
  rwa [RingHom.map_det] at h

/- English proof (translation)
Simplify using `[atInf, Matrix.map_mul]`.
-/
theorem foInf_mul (emb : ι → E →+* ℂ) (a b : Matrix (Fin n) (Fin n) E) (τ : ι) :
    atInf emb (a * b) τ = atInf emb a τ * atInf emb b τ := by
  simp [atInf, Matrix.map_mul]

/- English proof (translation)
Simplify using `[atInf]`.
-/
theorem foInf_one (emb : ι → E →+* ℂ) (τ : ι) : atInf emb (1 : Matrix (Fin n) (Fin n) E) τ = 1 := by
  simp [atInf]

def foTrR (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (y : Formalism.L2.Forms.Frames (gramC J emb)) : Formalism.L2.Forms.Frames (gramC J emb) :=
  foTr (atInf emb γ.1) (foInf_unit emb γ) y

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem foTrR_val (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (y : Formalism.L2.Forms.Frames (gramC J emb)) (τ : ι) :
    (foTrR emb γ y).1 τ = atInf emb γ.1 τ * y.1 τ := rfl

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `τ`. Use `show (foTrR emb (γ * δ) y).1 τ = (foTrR emb γ (foTrR emb δ y)).1 τ`. Rewrite using `[foTrR_val, foTrR_val, foTrR_val, Units.val_mul, foInf_mul, Matrix.mul_assoc]`.
-/
theorem foTrR_mul (emb : ι → E →+* ℂ) (γ δ : GL (Fin n) E) (y : Formalism.L2.Forms.Frames (gramC J emb)) :
    foTrR emb (γ * δ) y = foTrR emb γ (foTrR emb δ y) := by
  apply Subtype.ext
  funext τ
  show (foTrR emb (γ * δ) y).1 τ = (foTrR emb γ (foTrR emb δ y)).1 τ
  rw [foTrR_val, foTrR_val, foTrR_val, Units.val_mul, foInf_mul, Matrix.mul_assoc]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `τ`. Use `show (foTrR emb 1 y).1 τ = y.1 τ`. Rewrite using `[foTrR_val, Units.val_one, foInf_one, Matrix.one_mul]`.
-/
theorem foTrR_one (emb : ι → E →+* ℂ) (y : Formalism.L2.Forms.Frames (gramC J emb)) : foTrR emb 1 y = y := by
  apply Subtype.ext
  funext τ
  show (foTrR emb 1 y).1 τ = y.1 τ
  rw [foTrR_val, Units.val_one, foInf_one, Matrix.one_mul]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `τ`. Conclude with `h τ`.

Introduce `h τ`. Rewrite using `[h]`. Both sides reduce to the same expression.
-/
theorem foIsTr_iff (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (y' y : Formalism.L2.Forms.Frames (gramC J emb)) :
    IsTr (atInf emb γ) y' y ↔ y = foTrR emb γ y' := by
  constructor
  · intro h
    apply Subtype.ext
    funext τ
    exact h τ
  · intro h τ
    rw [h]
    rfl

def FoInv (S : StepLevel F E σ J T fT bad) (emb : ι → E →+* ℂ) (y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (v : Formalism.L2.Forms.Frames (gramC J emb) → ℂ) : Prop :=
  ∀ γ : GL (Fin n) E, γ ∈ UJ (σ : E →+* E) J → ∀ κ : S.U,
    y0.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y0.1 * κ.1 →
    ∀ y y' : Formalism.L2.Forms.Frames (gramC J emb), IsTr (atInf emb γ) y' y → v y = (S.chi κ : ℂ) * v y'

variable (S : StepLevel F E σ J T fT bad) (emb : ι → E →+* ℂ)

/- English proof (translation)
Establish `hy : y0.1 = bc (inclE (F` using `F) (FiniteAdeleRing (𝓞 F) F)) (γa⁻¹ * γb) * y0.1 * (κb * κa⁻¹).1 := by`. Rewrite using `[map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]`. Conclude with `foGrp _ _ _ _ _ h`. Establish `ht : foTrR emb γa⁻¹ z = foTrR emb (γa⁻¹ * γb) (foTrR emb γb⁻¹ z)`. Rewrite using `[← foTrR_mul]`.

Simplify using `[mul_assoc]`. Use `hv (γa⁻¹ * γb) (Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) hb) (κb * κa⁻¹) hy _ _ ((foIsTr_iff emb _ _ _).2 ht)` as an intermediate fact. Rewrite using `[this, map_mul, map_inv, Units.val_mul]`. Establish `e : (S.chi κa : ℂ) * ((S.chi κa)⁻¹ : ℂˣ) = 1` using `Units.mul_inv _`. Take the linear combination `((S.chi κb : ℂ) * v (foTrR emb γb⁻¹ z)) * e`.
-/
theorem foInv_wd {y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)} {v : Formalism.L2.Forms.Frames (gramC J emb) → ℂ} (hv : FoInv S emb y0 v)
    {γa γb : GL (Fin n) E} (ha : γa ∈ UJ (σ : E →+* E) J) (hb : γb ∈ UJ (σ : E →+* E) J) {κa κb : S.U}
    (h : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γa * y0.1 * κa.1 =
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γb * y0.1 * κb.1)
    (z : Formalism.L2.Forms.Frames (gramC J emb)) :
    (S.chi κa : ℂ) * v (foTrR emb γa⁻¹ z) = (S.chi κb : ℂ) * v (foTrR emb γb⁻¹ z) := by
  have hy : y0.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γa⁻¹ * γb) * y0.1 * (κb * κa⁻¹).1 := by
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    exact foGrp _ _ _ _ _ h
  have ht : foTrR emb γa⁻¹ z = foTrR emb (γa⁻¹ * γb) (foTrR emb γb⁻¹ z) := by
    rw [← foTrR_mul]
    simp [mul_assoc]
  have := hv (γa⁻¹ * γb) (Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) hb) (κb * κa⁻¹) hy _ _
    ((foIsTr_iff emb _ _ _).2 ht)
  rw [this, map_mul, map_inv, Units.val_mul]
  have e : (S.chi κa : ℂ) * ((S.chi κa)⁻¹ : ℂˣ) = 1 := Units.mul_inv _
  linear_combination ((S.chi κb : ℂ) * v (foTrR emb γb⁻¹ z)) * e

open Classical in

def foForm (y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (v : Formalism.L2.Forms.Frames (gramC J emb) → ℂ) :
    UPts σ J (FiniteAdeleRing (𝓞 F) F) → Formalism.L2.Forms.Frames (gramC J emb) → ℂ := fun x =>
  if h : ∃ γ : GL (Fin n) E, γ ∈ UJ (σ : E →+* E) J ∧ ∃ κ : S.U,
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y0.1 * κ.1 then
    fun y => (S.chi h.choose_spec.2.choose : ℂ) * v (foTrR emb h.choose⁻¹ y)
  else 0

variable {S emb}

/- English proof (translation)
Establish `h : ∃ γ : GL (Fin n) E, γ ∈ UJ (σ : E →+* E) J ∧ ∃ κ : S.U, x.1 = bc (inclE (F` using `F) (FiniteAdeleRing (𝓞 F) F)) γ * y0.1 * κ.1 := ⟨γ, hγ, κ, hx⟩`. Simplify using `only [foForm, dif_pos h]`. Conclude with `foInv_wd S emb hv h.choose_spec.1 hγ (h.choose_spec.2.choose_spec.symm.trans hx) y`.
-/
theorem foForm_eq {y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)} {v : Formalism.L2.Forms.Frames (gramC J emb) → ℂ} (hv : FoInv S emb y0 v)
    {x : UPts σ J (FiniteAdeleRing (𝓞 F) F)} {γ : GL (Fin n) E} (hγ : γ ∈ UJ (σ : E →+* E) J) {κ : S.U}
    (hx : x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y0.1 * κ.1) (y : Formalism.L2.Forms.Frames (gramC J emb)) :
    foForm S emb y0 v x y = (S.chi κ : ℂ) * v (foTrR emb γ⁻¹ y) := by
  have h : ∃ γ : GL (Fin n) E, γ ∈ UJ (σ : E →+* E) J ∧ ∃ κ : S.U,
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y0.1 * κ.1 := ⟨γ, hγ, κ, hx⟩
  simp only [foForm, dif_pos h]
  exact foInv_wd S emb hv h.choose_spec.1 hγ (h.choose_spec.2.choose_spec.symm.trans hx) y

/- English proof (translation)
Simplify using `only [foForm, dif_neg hx]`.
-/
theorem foForm_off {y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)} {v : Formalism.L2.Forms.Frames (gramC J emb) → ℂ}
    {x : UPts σ J (FiniteAdeleRing (𝓞 F) F)}
    (hx : ¬ ∃ γ : GL (Fin n) E, γ ∈ UJ (σ : E →+* E) J ∧ ∃ κ : S.U,
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y0.1 * κ.1) :
    foForm S emb y0 v x = 0 := by
  simp only [foForm, dif_neg hx]

/- English proof (translation)
Introduce `γ hγ x x' κ h y y' hy`. Distinguish the cases in `hx : ∃ γ1 : GL (Fin n) E, γ1 ∈ UJ (σ : E →+* E) J ∧ ∃ κ1 : S.U, x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1 * y0.1 * κ1.1`. Take `⟨γ1, hγ1, κ1, hx1⟩` from `hx`. Establish `hx' : x'.1 = bc (inclE (F` using `F) (FiniteAdeleRing (𝓞 F) F)) (γ * γ1) * y0.1 * (κ1 * κ).1 := by`. Rewrite using `[h, hx1, map_mul, Subgroup.coe_mul]`.

Use `group`. Establish `e : (γ * γ1)⁻¹ * γ = γ1⁻¹` using `by group`. Rewrite using `[foForm_eq hv (Subgroup.mul_mem _ hγ hγ1) hx' y, foForm_eq hv hγ1 hx1 y', map_mul, Units.val_mul, (foIsTr_iff emb γ y' y).1 hy, ← foTrR_mul, e]`. Expand and normalize the polynomial expressions, which then agree. Establish `hx' : ¬ ∃ γ1 : GL (Fin n) E, γ1 ∈ UJ (σ : E →+* E) J ∧ ∃ κ1 : S.U, x'.1 = bc (inclE (F` using `F) (FiniteAdeleRing (𝓞 F) F)) γ1 * y0.1 * κ1.1 := by`.

Introduce and unpack `⟨γ1, hγ1, κ1, hx1⟩`. Use `hx ⟨γ⁻¹ * γ1, Subgroup.mul_mem _ (Subgroup.inv_mem _ hγ) hγ1, κ1 * κ⁻¹, ?_⟩` and prove the remaining obligations. Establish `h2 : x.1 = (bc (inclE (F` using `F) (FiniteAdeleRing (𝓞 F) F)) γ)⁻¹ * x'.1 * κ.1⁻¹ := by`. Rewrite using `[h]`. Use `group`.

Rewrite using `[h2, hx1, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]`. Use `group`. Rewrite using `[foForm_off hx, foForm_off hx']`. Simplify using the standard rewrite rules.
-/
theorem foForm_adFun {y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)} {v : Formalism.L2.Forms.Frames (gramC J emb) → ℂ} (hv : FoInv S emb y0 v) :
    foForm S emb y0 v ∈ AdFun S emb := by
  intro γ hγ x x' κ h y y' hy
  by_cases hx : ∃ γ1 : GL (Fin n) E, γ1 ∈ UJ (σ : E →+* E) J ∧ ∃ κ1 : S.U,
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1 * y0.1 * κ1.1
  · obtain ⟨γ1, hγ1, κ1, hx1⟩ := hx
    have hx' : x'.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ * γ1) * y0.1 * (κ1 * κ).1 := by
      rw [h, hx1, map_mul, Subgroup.coe_mul]
      group
    have e : (γ * γ1)⁻¹ * γ = γ1⁻¹ := by group
    rw [foForm_eq hv (Subgroup.mul_mem _ hγ hγ1) hx' y, foForm_eq hv hγ1 hx1 y', map_mul, Units.val_mul,
      (foIsTr_iff emb γ y' y).1 hy, ← foTrR_mul, e]
    ring
  · have hx' : ¬ ∃ γ1 : GL (Fin n) E, γ1 ∈ UJ (σ : E →+* E) J ∧ ∃ κ1 : S.U,
        x'.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1 * y0.1 * κ1.1 := by
      rintro ⟨γ1, hγ1, κ1, hx1⟩
      refine hx ⟨γ⁻¹ * γ1, Subgroup.mul_mem _ (Subgroup.inv_mem _ hγ) hγ1, κ1 * κ⁻¹, ?_⟩
      have h2 : x.1 = (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ)⁻¹ * x'.1 * κ.1⁻¹ := by
        rw [h]
        group
      rw [h2, hx1, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [foForm_off hx, foForm_off hx']
    simp

/- English proof (translation)
Distinguish the cases in `hx : ∃ γ1 : GL (Fin n) E, γ1 ∈ UJ (σ : E →+* E) J ∧ ∃ κ1 : S.U, x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1 * y0.1 * κ1.1`. Take `⟨γ1, hγ1, κ1, hx1⟩` from `hx`. Establish `e : foForm S emb y0 v x = (S.chi κ1 : ℂ) • fun y => v (foTr (atInf emb (γ1⁻¹).1) (foInf_unit emb γ1⁻¹) y)`. Use function extensionality and compare the values at `y`. Rewrite using `[foForm_eq hv hγ1 hx1 y]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ (foValC_tr lam _ _ hV)`. Rewrite using `[foForm_off hx]`. Conclude with `Submodule.zero_mem _`.
-/
theorem foForm_val {y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)} {v : Formalism.L2.Forms.Frames (gramC J emb) → ℂ} (hv : FoInv S emb y0 v)
    {lam : ι → DomWeight n} (hV : v ∈ ValC (gramC J emb) lam) (x : UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    foForm S emb y0 v x ∈ ValC (gramC J emb) lam := by
  by_cases hx : ∃ γ1 : GL (Fin n) E, γ1 ∈ UJ (σ : E →+* E) J ∧ ∃ κ1 : S.U,
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1 * y0.1 * κ1.1
  · obtain ⟨γ1, hγ1, κ1, hx1⟩ := hx
    have e : foForm S emb y0 v x = (S.chi κ1 : ℂ) • fun y => v (foTr (atInf emb (γ1⁻¹).1) (foInf_unit emb γ1⁻¹) y) := by
      funext y
      rw [foForm_eq hv hγ1 hx1 y]
      rfl
    rw [e]
    exact Submodule.smul_mem _ _ (foValC_tr lam _ _ hV)
  · rw [foForm_off hx]
    exact Submodule.zero_mem _

/- English proof (translation)
The claim follows from `Submodule.mem_inf.2 ⟨foForm_adFun hv, Submodule.mem_pi.2 fun x _ => foForm_val hv hV x⟩`.
-/
theorem foForm_mem {y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)} {v : Formalism.L2.Forms.Frames (gramC J emb) → ℂ} (hv : FoInv S emb y0 v)
    {lam : ι → DomWeight n} (hV : v ∈ ValC (gramC J emb) lam) : foForm S emb y0 v ∈ AdForms S emb lam :=
  Submodule.mem_inf.2 ⟨foForm_adFun hv, Submodule.mem_pi.2 fun x _ => foForm_val hv hV x⟩

/- English proof (translation)
Use function extensionality and compare the values at `y`. Rewrite using `[foForm_eq hv (Subgroup.one_mem _) (κ := 1) (by simp) y]`. Simplify using `[foTrR_one]`.
-/
theorem foForm_self {y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)} {v : Formalism.L2.Forms.Frames (gramC J emb) → ℂ} (hv : FoInv S emb y0 v) :
    foForm S emb y0 v y0 = v := by
  funext y
  rw [foForm_eq hv (Subgroup.one_mem _) (κ := 1) (by simp) y]
  simp [foTrR_one]

end Adelic

section Rec

open Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.PCard Formalism.MainNotions.G.CmpJ.PRankGe Formalism.MainNotions.G.CmpJ.PInvLe

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

/- English proof (translation)
Introduce `β c v hv`. Use `Submodule.mem_map.2 ⟨_, Submodule.mem_map.2 ⟨_, foForm_mem hv.2 hv.1, rfl⟩, ?_⟩` and prove the remaining obligations. Conclude with `foForm_self hv.2`.
-/
theorem formsOnClassOf_holds (S : StepIn M i hi G) : FormsOnClassOf S := by
  intro β c v hv
  refine Submodule.mem_map.2 ⟨_, Submodule.mem_map.2 ⟨_, foForm_mem hv.2 hv.1, rfl⟩, ?_⟩
  exact foForm_self hv.2

/- English proof (translation)
The claim follows from `valLiftOf_of S e (formsOnClassOf_holds S) h2`.
-/
theorem valLiftOf_of_cmp (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (h2 : CmpLiftOf S e) : ValLiftOf S e :=
  valLiftOf_of S e (formsOnClassOf_holds S) h2

/- English proof (translation)
The claim follows from `invLeOf_of_two S e (formsOnClassOf_holds S) h2`.
-/
theorem invLeOf_of_cmp (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (h2 : CmpLiftOf S e) : InvLeOf S e :=
  invLeOf_of_two S e (formsOnClassOf_holds S) h2

/- English proof (translation)
The claim follows from `chartRankGe_of_lift S e H hS X (valLiftOf_of_cmp S e h2)`.
-/
theorem chartRankGe_of_cmp [IsFractionRing G.O G.Kf] (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (H : ∀ β, S.Core e β)
    (hS : BlockRationalityField) (X : KAat.ChX S) (h2 : CmpLiftOf S e) : ChartRankGe S :=
  chartRankGe_of_lift S e H hS X (valLiftOf_of_cmp S e h2)

end Rec

section Card

open Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.PCard Formalism.MainNotions.G.CmpJ.PRankGe Formalism.MainNotions.G.CmpJ.PInvLe

variable {D : D7} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

/- English proof (translation)
The claim follows from `cmpJHyp_of_two c Gt hS core ok twUnit valIntN iwF hfin X (fun _ _ => formsOnClassOf_holds _) h2`.
-/
theorem cmpJHyp_of_cmp (c : LatCmp D) {I : CmpJIn Tw u μ w h Lv} (Gt : GatTies D) (hS : BlockRationalityField)
    (core : ∀ j hj β, (I.at' j hj).st.Core (c.embW u w h) β) (ok : ∀ j hj, (I.at' j hj).st.okW w)
    (twUnit : ∀ j hj β, (I.at' j hj).st.TwUnit w β) (valIntN : ∀ j hj, (I.at' j hj).st.ValIntN (c.embW u w h) w)
    (iwF : ∀ j hj β, (I.at' j hj).st.IwF β) (hfin : ∀ j, j + 1 ≤ D.R.m → (gatJ Lv (j + 1)).FinClasses)
    (X : ∀ j hj, KAat.ChX (I.at' j hj).st) (h2 : ∀ j hj, CmpLiftOf (I.at' j hj).st (c.embW u w h)) : CmpJHyp c I :=
  cmpJHyp_of_two c Gt hS core ok twUnit valIntN iwF hfin X (fun _ _ => formsOnClassOf_holds _) h2

end Card

end Formalism.MainNotions.G.CmpJ.PFormsCl
