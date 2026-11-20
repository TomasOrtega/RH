import Formalism.LocalToGlobal.GlobalTheory.BlockActions.StabRestrict
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ClassInjectiveOfDegree

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

def StabFix (Tf : FormsTiedSym D u Ch chOf) : Prop :=
  ∀ (c : (D.fm u).clsP) (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)),
    γ ∈ ((Tf.cls D.R.m le_rfl (Or.inr rfl)).stabI ((D.fm u).til c)).range →
    ((Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1) *ᵥ Tf.til.z0 = Tf.til.z0

/- English proof (translation)
Establish `hTp : ((D.mem u).A.T : ℕ).Prime` using `(D.mem u).A.T_prime`. Take `⟨a, ha⟩` from `Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line`. Establish `hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0` using `by exact_mod_cast hTp.ne_zero`. Establish `ha0 : a ≠ 0`. Introduce `h0`.

Establish `hzz` using `Tf.til.hermitianForm_lastCoordinateUniformizerVector_self`. Rewrite `hzz` using `[ha, h0, zero_smul]`. Apply `hT0` to reduce the goal to its premises. Rewrite using `[← hzz]`. Simplify using `[hform]`.

Introduce `y`. Take `⟨x, s, hy⟩` from `span_iXc_zc D y`. Conclude with `⟨x, s / a, by rw [hy, ha, smul_smul, div_mul_cancel₀ s ha0]⟩`.
-/
theorem span_with_orthogonal_vector (Tf : FormsTiedSym D u Ch chOf) :
    ∀ y, ∃ (x : Fin (D.R.N D.R.m - 1) → D.host.E) (s : D.host.E), y = iXc D x + s • Tf.til.z0 := by
  have hTp : ((D.mem u).A.T : ℕ).Prime := (D.mem u).A.T_prime
  obtain ⟨a, ha⟩ := Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hTp.ne_zero
  have ha0 : a ≠ 0 := by
    intro h0
    have hzz := Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
    rw [ha, h0, zero_smul] at hzz
    apply hT0; rw [← hzz]; simp [hform]
  intro y
  obtain ⟨x, s, hy⟩ := span_iXc_zc D y
  exact ⟨x, s / a, by rw [hy, ha, smul_smul, div_mul_cancel₀ s ha0]⟩

/- English proof (translation)
Establish `hC` using `crdFacts_of Tf`. Establish `hTp : ((D.mem u).A.T : ℕ).Prime` using `(D.mem u).A.T_prime`. Use `set σ : D.host.E →+* D.host.E := (sigD D : D.host.E →+* D.host.E) with hσdef`. Use `set J := gramN D D.R.m le_rfl with hJ`. Use `set z0 := Tf.til.z0 with hz0`.

Take `⟨a, ha⟩` from `Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line`. Rewrite `ha` using `[← hz0]`. Establish `hzz : hform σ J z0 z0 = (((D.mem u).A.T : ℕ) : D.host.E)` using `Tf.til.hermitianForm_lastCoordinateUniformizerVector_self`. Establish `hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0` using `by exact_mod_cast hTp.ne_zero`. Establish `horth : ∀ x, hform σ J (iXc D x) z0 = 0 ∧ hform σ J z0 (iXc D x) = 0` using `fun x => by`.

Rewrite using `[ha, hform_smul_right, hform_smul_left, (hC.orth x).1, (hC.orth x).2]`. Simplify using the standard rewrite rules. Establish `hγ : ∀ x y, hform σ J (Γ *ᵥ x) (Γ *ᵥ y) = hform σ J x y` using `fun x y => hform_UJ σ J Γ hΓ x y`. Take `⟨δ, hδ, hδi⟩` from `fix_restrict σ J (gramP D) (iXc D) (iXc_injective D) z0 hC.iso horth (span_with_orthogonal_vector Tf) (by rw [hzz]; exact hT0) Γ hγ hfix`. Use `⟨δ, ⟨?_, ?_⟩, hδi⟩` and prove the remaining obligations.

Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Simplify using `only [Matrix.toLin'_apply, ← mulVec_mulVec]`. Use `show Γ *ᵥ ((iXm D).map (RingHom.id D.host.E) *ᵥ x) = (iXm D).map (RingHom.id D.host.E) *ᵥ (δ *ᵥ x)`.

Establish `hm : (iXm D).map (RingHom.id D.host.E) = iXm D` using `by ext i j; rfl`. Rewrite using `[hm, iXm, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, hδ]`. Establish `: (fun a => (RingHom.id D.host.E) (z0 a)) = z0` using `rfl`. Rewrite using `[this]`. Conclude with `hfix`.
-/
theorem ext_of_fix (Tf : FormsTiedSym D u Ch chOf) (Γ : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E)
    (hΓ : cT (sigD D : D.host.E →+* D.host.E) Γ * gramN D D.R.m le_rfl * Γ = gramN D D.R.m le_rfl)
    (hfix : Γ *ᵥ Tf.til.z0 = Tf.til.z0) :
    ∃ δ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E,
      IsExt D Tf.til.z0 (RingHom.id D.host.E) δ Γ ∧
      ∀ x y, hform (sigD D : D.host.E →+* D.host.E) (gramP D) (δ *ᵥ x) (δ *ᵥ y) =
        hform (sigD D : D.host.E →+* D.host.E) (gramP D) x y := by
  have hC := crdFacts_of Tf
  have hTp : ((D.mem u).A.T : ℕ).Prime := (D.mem u).A.T_prime
  set σ : D.host.E →+* D.host.E := (sigD D : D.host.E →+* D.host.E) with hσdef
  set J := gramN D D.R.m le_rfl with hJ
  set z0 := Tf.til.z0 with hz0
  obtain ⟨a, ha⟩ := Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line
  rw [← hz0] at ha
  have hzz : hform σ J z0 z0 = (((D.mem u).A.T : ℕ) : D.host.E) := Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hTp.ne_zero
  have horth : ∀ x, hform σ J (iXc D x) z0 = 0 ∧ hform σ J z0 (iXc D x) = 0 := fun x => by
    rw [ha, hform_smul_right, hform_smul_left, (hC.orth x).1, (hC.orth x).2]; simp
  have hγ : ∀ x y, hform σ J (Γ *ᵥ x) (Γ *ᵥ y) = hform σ J x y := fun x y => hform_UJ σ J Γ hΓ x y
  obtain ⟨δ, hδ, hδi⟩ := fix_restrict σ J (gramP D) (iXc D) (iXc_injective D) z0 hC.iso horth (span_with_orthogonal_vector Tf)
    (by rw [hzz]; exact hT0) Γ hγ hfix
  refine ⟨δ, ⟨?_, ?_⟩, hδi⟩
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    simp only [Matrix.toLin'_apply, ← mulVec_mulVec]
    show Γ *ᵥ ((iXm D).map (RingHom.id D.host.E) *ᵥ x) = (iXm D).map (RingHom.id D.host.E) *ᵥ (δ *ᵥ x)
    have hm : (iXm D).map (RingHom.id D.host.E) = iXm D := by ext i j; rfl
    rw [hm, iXm, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, hδ]
  · have : (fun a => (RingHom.id D.host.E) (z0 a)) = z0 := rfl
    rw [this]; exact hfix

/- English proof (translation)
Establish `hm : (iXm D).map (RingHom.id D.host.E) = iXm D` using `by ext i j; rfl`. Establish `hz : (fun a => (RingHom.id D.host.E) (Tf.til.z0 a)) = Tf.til.z0` using `rfl`. Take `⟨a1, b1⟩` from `h1`. Take `⟨a2, b2⟩` from `h2`. Rewrite `a1`, `a2` using `[hm]`.

Rewrite `b1`, `b2` using `[hz]`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `y`. Simplify using `only [Matrix.toLin'_apply]`.

Take `⟨x, s, rfl⟩` from `span_with_orthogonal_vector Tf y`. Establish `hx : iXc D x = iXm D *ᵥ x` using `by simp only [iXm, LinearMap.toMatrix'_mulVec]`. Rewrite using `[hx, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, b1, b2, mulVec_mulVec, mulVec_mulVec, a1, a2]`.
-/
theorem ext_unique (Tf : FormsTiedSym D u Ch chOf) {δ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E}
    {Γ1 Γ2 : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E}
    (h1 : IsExt D Tf.til.z0 (RingHom.id D.host.E) δ Γ1) (h2 : IsExt D Tf.til.z0 (RingHom.id D.host.E) δ Γ2) : Γ1 = Γ2 := by
  have hm : (iXm D).map (RingHom.id D.host.E) = iXm D := by ext i j; rfl
  have hz : (fun a => (RingHom.id D.host.E) (Tf.til.z0 a)) = Tf.til.z0 := rfl
  obtain ⟨a1, b1⟩ := h1
  obtain ⟨a2, b2⟩ := h2
  rw [hm] at a1 a2
  rw [hz] at b1 b2
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro y
  simp only [Matrix.toLin'_apply]
  obtain ⟨x, s, rfl⟩ := span_with_orthogonal_vector Tf y
  have hx : iXc D x = iXm D *ᵥ x := by simp only [iXm, LinearMap.toMatrix'_mulVec]
  rw [hx, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, b1, b2, mulVec_mulVec, mulVec_mulVec, a1, a2]

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Use `set Km := Tf.cls D.R.m le_rfl (Or.inr rfl) with hKm`. Establish `key : ∀ s : (D.mem u).C.stab D.R.m ((D.fm u).til c), ∃ (s' : (D.fm u).stabilizer₂ c) (δ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E), IsExt D Tf.til.z0 (RingHom.id D.host.E) δ ((Tf.til.ga c).1.1 * (Km.stabI ((D.fm u).til c) s).1.1 * ((Tf.til.ga c)⁻¹).1.1) ∧ …`. Introduce `s`. Use `set γ := Km.stabI ((D.fm u).til c) s with hγ`. Establish `hU : cT (sigD D : D.host.E →+* D.host.E) ((Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1) * gramN D D.R.m le_rfl * ((Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1) = gramN D D.R.m le_rfl`.

Establish `h0` using `(Tf.til.ga c * γ * (Tf.til.ga c)⁻¹).2`. Establish `e : (Tf.til.ga c * γ * (Tf.til.ga c)⁻¹).1.1 = (Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1`. Simplify using `only [Subgroup.coe_mul, Units.val_mul]`. Establish `h1 : cT (sigD D : D.host.E →+* D.host.E) (Tf.til.ga c * γ * (Tf.til.ga c)⁻¹).1.1 * gramN D D.R.m le_rfl * (Tf.til.ga c * γ * (Tf.til.ga c)⁻¹).1.1 = gramN D D.R.m le_rfl` using `h0`. Rewrite `h1` using `[e]`. Then use the resulting hypothesis.

Take `⟨δ, hδE, hδi⟩` from `ext_of_fix Tf _ hU (hF c γ ⟨s, rfl⟩)`. Establish `hΓu : IsUnit ((Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1).det`. Rewrite using `[← Units.val_mul, ← Units.val_mul]`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)`. Establish `hδu` using `isUnit_of_extE Tf δ _ hΓu hδE`.

Use `set Δ : GL (Fin (D.R.N D.R.m - 1)) D.host.E := ((Matrix.isUnit_iff_isUnit_det δ).mpr hδu).unit with hΔdef`. Establish `hΔv : Δ.1 = δ` using `IsUnit.unit_spec _`. Establish `hΔ : Δ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramP D)` using `by show cT _ Δ.1 * gramP D * Δ.1 = gramP D`. Rewrite using `[hΔv]`. Conclude with `unitary_of_hform _ _ _ hδi`.

Take `⟨s', hs'⟩` from `stab_restrict Tf c γ ⟨s, rfl⟩ ⟨Δ, hΔ⟩ (by rw [show (⟨Δ, hΔ⟩ : UJ _ _).1.1 = δ from hΔv]; exact hδE)`. Conclude with `⟨s', δ, hδE, by rw [hs']; exact hΔv⟩`. Use `choose g δf hδE hδv using key`. Use `⟨g, fun s1 s2 h12 => ?_⟩` and prove the remaining obligations. Establish `hδ12 : δf s1 = δf s2` using `by rw [← hδv s1, ← hδv s2, h12]`.

Establish `hΓ` using `ext_unique Tf (hδE s1) (hδ12 ▸ hδE s2)`. Apply `Km.stabI_inj ((D.fm u).til c)` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Establish `hi : ((Tf.til.ga c)⁻¹).1.1 * (Tf.til.ga c).1.1 = 1`.

Rewrite using `[← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]`. Both sides reduce to the same expression. Use `congrArg (fun M => ((Tf.til.ga c)⁻¹).1.1 * M * (Tf.til.ga c).1.1) hΓ` as an intermediate fact. Simplify using `only [← Matrix.mul_assoc, hi, Matrix.one_mul] at this`. Simplify using `only [Matrix.mul_assoc, hi, Matrix.mul_one] at this`.

Conclude with `this`.
-/
theorem stab_back (Tf : FormsTiedSym D u Ch chOf) (hF : StabFix Tf) (c : (D.fm u).clsP) :
    ∃ g : (D.mem u).C.stab D.R.m ((D.fm u).til c) → (D.fm u).stabilizer₂ c, Function.Injective g := by
  set Km := Tf.cls D.R.m le_rfl (Or.inr rfl) with hKm
  have key : ∀ s : (D.mem u).C.stab D.R.m ((D.fm u).til c), ∃ (s' : (D.fm u).stabilizer₂ c)
      (δ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E),
      IsExt D Tf.til.z0 (RingHom.id D.host.E) δ
        ((Tf.til.ga c).1.1 * (Km.stabI ((D.fm u).til c) s).1.1 * ((Tf.til.ga c)⁻¹).1.1) ∧
      (Tf.clsP.stabI c s').1.1 = δ := by
    intro s
    set γ := Km.stabI ((D.fm u).til c) s with hγ
    have hU : cT (sigD D : D.host.E →+* D.host.E) ((Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1) *
        gramN D D.R.m le_rfl * ((Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1) = gramN D D.R.m le_rfl := by
      have h0 := (Tf.til.ga c * γ * (Tf.til.ga c)⁻¹).2
      have e : (Tf.til.ga c * γ * (Tf.til.ga c)⁻¹).1.1 =
          (Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1 := by
        simp only [Subgroup.coe_mul, Units.val_mul]
      have h1 : cT (sigD D : D.host.E →+* D.host.E) (Tf.til.ga c * γ * (Tf.til.ga c)⁻¹).1.1 *
          gramN D D.R.m le_rfl * (Tf.til.ga c * γ * (Tf.til.ga c)⁻¹).1.1 = gramN D D.R.m le_rfl := h0
      rwa [e] at h1
    obtain ⟨δ, hδE, hδi⟩ := ext_of_fix Tf _ hU (hF c γ ⟨s, rfl⟩)
    have hΓu : IsUnit ((Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1).det := by
      rw [← Units.val_mul, ← Units.val_mul]
      exact (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
    have hδu := isUnit_of_extE Tf δ _ hΓu hδE
    set Δ : GL (Fin (D.R.N D.R.m - 1)) D.host.E := ((Matrix.isUnit_iff_isUnit_det δ).mpr hδu).unit with hΔdef
    have hΔv : Δ.1 = δ := IsUnit.unit_spec _
    have hΔ : Δ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramP D) := by
      show cT _ Δ.1 * gramP D * Δ.1 = gramP D
      rw [hΔv]; exact unitary_of_hform _ _ _ hδi
    obtain ⟨s', hs'⟩ := stab_restrict Tf c γ ⟨s, rfl⟩ ⟨Δ, hΔ⟩ (by rw [show (⟨Δ, hΔ⟩ : UJ _ _).1.1 = δ from hΔv]; exact hδE)
    exact ⟨s', δ, hδE, by rw [hs']; exact hΔv⟩
  choose g δf hδE hδv using key
  refine ⟨g, fun s1 s2 h12 => ?_⟩
  have hδ12 : δf s1 = δf s2 := by rw [← hδv s1, ← hδv s2, h12]
  have hΓ := ext_unique Tf (hδE s1) (hδ12 ▸ hδE s2)
  apply Km.stabI_inj ((D.fm u).til c)
  apply Subtype.ext
  apply Units.ext
  have hi : ((Tf.til.ga c)⁻¹).1.1 * (Tf.til.ga c).1.1 = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have := congrArg (fun M => ((Tf.til.ga c)⁻¹).1.1 * M * (Tf.til.ga c).1.1) hΓ
  simp only [← Matrix.mul_assoc, hi, Matrix.one_mul] at this
  simp only [Matrix.mul_assoc, hi, Matrix.mul_one] at this
  exact this

/- English proof (translation)
The claim follows from `stabiliser_bijective_of_injection (fun D u Ch chOf Tf c => stab_back Tf (hF D u Ch chOf Tf) c)`.
-/
theorem stabiliser_bijective_of_fixed
    (hF : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
      StabFix Tf) : StabiliserMapBijective :=
  stabiliser_bijective_of_injection (fun D u Ch chOf Tf c => stab_back Tf (hF D u Ch chOf Tf) c)

end Formalism.L2.GlobalTheoryTheory.Br
