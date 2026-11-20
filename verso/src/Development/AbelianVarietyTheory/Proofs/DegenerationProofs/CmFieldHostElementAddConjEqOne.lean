import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch.AbVal

/- English proof (translation)
Establish `h1 : H.bar H.rt ^ 2 = H.rt ^ 2`. Rewrite using `[← map_pow, H.rt_sq, map_neg, map_natCast]`. Establish `h2 : 2 * H.bar H.w0 = 1 + H.bar H.rt`. Use `congrArg H.bar H.two_weight_eq_one_add_root` as an intermediate fact. Simplify `this` using `[map_ofNat]`.

Establish `h3 : H.bar H.rt = -H.rt`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h1 with e | e` into its components or cases. It suffices to derive a contradiction. Establish `e' : IsCMField.complexConj E (H.rt : E) = H.rt` using `by rw [← H.bar_eq, e]`. Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`.

Establish `c` using `IsCMField.complexEmbedding_complexConj E φ (H.rt : E)`. Rewrite `c` using `[e']`. Establish `r : φ (H.rt : E) ^ 2 = -(H.d : ℂ)`. Use `congrArg (fun z : 𝓞 E => φ (z : E)) H.rt_sq` as an intermediate fact. Simplify using `using this`.

Take `⟨x, hx⟩` from `Complex.conj_eq_iff_real.1 c.symm`. Rewrite `r` using `[hx]`. Establish `r' : x ^ 2 = -(H.d : ℝ)` using `by exact_mod_cast r`. Establish `: (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Use polynomial arithmetic with `[sq_nonneg x]`.

Conclude with `e`. Establish `: (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1`. Rewrite using `[mul_add, h2, H.two_weight_eq_one_add_root, h3]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `mul_left_cancel₀ two_ne_zero this`.
-/
theorem cmField_host_element_add_conj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : H.w0 + H.bar H.w0 = 1 := by
  have h1 : H.bar H.rt ^ 2 = H.rt ^ 2 := by
    rw [← map_pow, H.rt_sq, map_neg, map_natCast]
  have h2 : 2 * H.bar H.w0 = 1 + H.bar H.rt := by
    have := congrArg H.bar H.two_weight_eq_one_add_root
    simpa [map_ofNat] using this
  have h3 : H.bar H.rt = -H.rt := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with e | e
    · exfalso
      have e' : IsCMField.complexConj E (H.rt : E) = H.rt := by rw [← H.bar_eq, e]
      obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have c := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
      rw [e'] at c
      have r : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
        have := congrArg (fun z : 𝓞 E => φ (z : E)) H.rt_sq
        simpa using this
      obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 c.symm
      rw [hx] at r
      have r' : x ^ 2 = -(H.d : ℝ) := by exact_mod_cast r
      have : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
      nlinarith [sq_nonneg x]
    · exact e
  have : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by
    rw [mul_add, h2, H.two_weight_eq_one_add_root, h3]; ring
  exact mul_left_cancel₀ two_ne_zero this

/- English proof (translation)
Introduce `h` and use `(((Units.isUnit _).map _).map _).ne_zero ((dif_pos (fun z _ => Good.mem (L := D.P.L) (z := z) (J := ν.J) (fun ψ => ν.good ψ trivial) (fun _ : PUnit => eSec D.P.A) (TF (R := R) F).hom)).symm.trans h)`.
-/
theorem rg_ne_zero {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {N : NumD F} (ν : NumOf D F N) : ν.rg ≠ 0 := fun h =>
  (((Units.isUnit _).map _).map _).ne_zero ((dif_pos (fun z _ =>
    Good.mem (L := D.P.L) (z := z) (J := ν.J) (fun ψ => ν.good ψ trivial) (fun _ : PUnit => eSec D.P.A)
      (TF (R := R) F).hom)).symm.trans h)

/- English proof (translation)
Use `choose F hF hU using fun a => hlift (act.act a) (act.hom a)`. Establish `add : ∀ a b, F (a + b) = F a + F b` using `fun a b => (hU _ _ fun z => by`. Rewrite using `[LinearMap.add_apply, hadd, hF, hF, act.map_add]`. Conclude with `(MonObj.comp_mul _ _ _).symm).symm`. Use `⟨RingHom.mk' ⟨⟨F, (hU _ _ fun z => ?_).symm⟩, fun a b => (hU _ _ fun z => ?_).symm⟩ add, hF⟩` and prove the remaining obligations.

Rewrite using `[act.map_one, Category.comp_id]`. Both sides reduce to the same expression. Rewrite using `[act.map_mul, Module.End.mul_apply, hF, hF, Category.assoc]`.
-/
theorem exists_ringHom_lift {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {O : Type} [CommRing O]
    (act : RingAct A O) {V : Type} [AddCommGroup V] [Module ℂ V] (ex : V → (T ⟶ A))
    (hadd : ∀ z w, ex (z + w) = ex z * ex w)
    (hlift : ∀ f : A ⟶ A, IsMonHom f → ∃! F : V →ₗ[ℂ] V, ∀ z, ex (F z) = ex z ≫ f) :
    ∃ F : O →+* Module.End ℂ V, ∀ a z, ex (F a z) = ex z ≫ act.act a := by
  choose F hF hU using fun a => hlift (act.act a) (act.hom a)
  have add : ∀ a b, F (a + b) = F a + F b := fun a b => (hU _ _ fun z => by
    rw [LinearMap.add_apply, hadd, hF, hF, act.map_add]
    exact (MonObj.comp_mul _ _ _).symm).symm
  refine ⟨RingHom.mk' ⟨⟨F, (hU _ _ fun z => ?_).symm⟩, fun a b => (hU _ _ fun z => ?_).symm⟩ add, hF⟩
  · rw [act.map_one, Category.comp_id]; rfl
  · rw [act.map_mul, Module.End.mul_apply, hF, hF, Category.assoc]

/- English proof (translation)
Introduce `E _ _ _ H D R _ _ _ A`. Use `letI := H.starRing`. Take `⟨g, Λ, Hm, χ, Ef, ex, fr, hf, hEf, hbij⟩` from `hEx R A.D₀.P A.ν.J A.ν.good`. Take `⟨hdisc, hfull, hherm, hpos, hnorm, hχ, hadd, hsurj, hker, hfr, hlift⟩` from `hGrp R A.D₀ _ g Λ Hm χ ex fr hf`. Establish `hcube` using `hCube R A.D₀ _ g Λ Hm χ ex fr hf`.

Take `⟨hsym, hneg⟩` from `hSym R A.D₀ _ g Λ Hm χ ex fr hf`. Establish `hros` using `hRos R A.D₀ _ g Λ Hm χ ex fr hf`. Establish `hprim` using `hPrim R A.D₀ _ g Λ Hm χ ex fr hf`. Take `⟨θ, hθ, hθv⟩` from `hSec R A.D₀ _ g Λ Hm χ ex fr hf A.ν.th`. Establish `hlie` using `hLie R A.D₀ _ g Λ Hm χ ex fr hf`.

Take `⟨F, hF⟩` from `exists_ringHom_lift A.oa.onB.toRingAct ex hadd hlift`. Establish `hmem : ∀ a, ∀ l ∈ Λ, F a l ∈ Λ` using `fun a l hl => by haveI := A.oa.onB.hom a`. Rewrite using `[← hker, hF, (hker l).2 hl, MonObj.one_comp]`. Establish `hadj : ∀ a z w, hermForm Hm (F a z) w = hermForm Hm z (F (star a) w)` using `fun a => by haveI := A.oa.onB.hom a haveI := A.oa.onB.hom (star a)`. Take `⟨r, hr⟩` from `exists_ros hL.globalFns A.D₀.P.isAb A.D₀.P.isLB _ _ (A.oa.onB.rosati a)`.

Conclude with `(hros _ _ (A.oa.onB.hom a) (A.oa.onB.hom (star a)) _ _ (hF a) (hF (star a)) r hr).1`. Set `B : An H` to `{ gB := g, abelian₂ := Λ, discrete := hdisc, full := hfull, Hm := Hm, Hm_herm := hherm, Hm_pos := hpos, Ef := Ef, Ef_eq := hEf, Ef_bij := hbij, chi := χ, chi_norm := hnorm, chi_add := hχ, chi_neg := hneg, F := F, F_mem := hmem, F_adj := hadj, X := PUnit, ct := 0, ct_smul := fun a …`. Establish `hrg` using `rg_ne_zero A.ν`. Establish `h0` using `(fr 0).ne_zero`. Establish `hw : ∀ z w, hermForm Hm z w = hermForm Hm z (F H.w0 w) + hermForm Hm (F H.w0 z) w` using `fun z w => by`.

Rewrite using `[hadj]`. Use `Eq.trans ?_ (B.H_add_right z (F H.w0 w) (F (star H.w0) w))` and prove the remaining obligations. Rewrite using `[← LinearMap.add_apply, ← map_add, show H.w0 + star H.w0 = 1 from cmField_host_element_add_conj_eq_one H, map_one]`. Both sides reduce to the same expression. Establish `hp` using `hprim _ (A.oa.onB.hom H.w0) (F H.w0) (hmem H.w0) (hF H.w0) hw Ef hEf`.

Establish `hth : ∀ z, A.N.th (A.ν.eA.symm (ex z)) = θ z * fr 0 / A.ν.rg * ((fr z / fr 0 : ℂˣ) : ℂ)` using `fun z => by`. Establish `e` using `A.ν.th_eq (A.ν.eA.symm (ex z))`. Rewrite `e` using `[MulEquiv.apply_symm_apply, hθv]`. Express the relevant statement in the definitionally equal form `_ * A.ν.rg = _ at e`. Rewrite using `[Units.val_div_eq_div_val, eq_div_of_mul_eq hrg e]`.

Clear the denominators using the available nonvanishing facts. Use `⟨B, fun z => A.ν.eA.symm (ex z), fun z => fr z / fr 0, fun z => θ z * fr 0 / A.ν.rg, ⟨fun z w => (congrArg A.ν.eA.symm (hadd z w)).trans (map_mul _ _ _), A.ν.eA.symm.surjective.comp hsurj, fun z => (map_eq_one_iff _ A.ν.eA.symm.injective).trans (hker z), div_self' _, fun l z => ? …` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[Units.val_div_eq_div_val, Units.val_div_eq_div_val, hfr l z, mul_div_assoc]`. Both sides reduce to the same expression.

Use `Units.ext ?_` and prove the remaining obligations. Establish `e` using `hcube x y z`. Simplify using `only [Units.val_mul, Units.val_div_eq_div_val, A.ν.θ_eq, MulEquiv.apply_symm_apply]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `e`.

Use `Units.ext ?_` and prove the remaining obligations. Establish `e` using `hsym x`. Simplify using `only [Units.val_mul, Units.val_div_eq_div_val, A.ν.σ_eq, MulEquiv.apply_symm_apply]`. Rewrite using `[← e, mul_div_assoc]`. Establish `e₁` using `hθv (z + l)`.

Rewrite `e₁` using `[hadd, (hker l).2 l.2, _root_.mul_one, hθv, hfr l z, ← _root_.mul_assoc]`. Establish `e₂` using `mul_right_cancel₀ (fr (z + l)).ne_zero e₁`. Express the relevant statement in the definitionally equal form `θ (z + l) * fr 0 / A.ν.rg = (χ l * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l)) ^ 1 * Complex.exp (Real.pi * B.H 0 l) * (θ z * fr 0 / A.ν.rg)`. Rewrite using `[← e₂, B.H_zero_left, mul_zero, Complex.exp_zero]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `hz haveI := A.closed`. Take `⟨-, -, -, ⟨s, f, hs, hf0⟩, hv, -⟩` from `hFam R A.D₀ A.even A.bimult ℂ A.N A.ν 1 le_rfl`. Take `⟨c, rfl⟩` from `hv s f hs`. Use `hf0 (funext fun α => funext fun x => ?_)` and prove the remaining obligations. Take `⟨z, hz'⟩` from `hsurj (A.ν.eA (x * A.N.c α))`.

Establish `e` using `hth z`. Rewrite `e` using `[hz', MulEquiv.symm_apply_apply, congrFun hz z]`. Simplify using `[NumD.vth, e]`. Take `⟨t, h₁, h₂, -⟩` from `A.w0`. Conclude with `(hp t ⟨h₁, h₂⟩).1`.

Take `⟨n, h₁, h₂⟩` from `A.det τ`. Rewrite using `[← h₂]`. Conclude with `congrArg (· + _) (hlie _ (ofRingAct A.oa.onB.toRingAct) (fun a => F a) hF τ n h₁)`. Simplify using `only [MulEquiv.apply_symm_apply]`. Conclude with `hF a z`.

Establish `e` using `(hros _ _ (A.oa.onB.hom a) (A.oa.onB.hom b) _ _ (hF a) (hF b) r hr).2 x z`. Simplify using `only [Units.val_div_eq_div_val, MulEquiv.apply_symm_apply]`. Express the relevant statement in the definitionally equal form `_ * ((fr (F a x) : ℂ) / _) * _ * ((fr (x + F b z) : ℂ) / _) = (fr (F a x + z) : ℂ) / _ * _ * ((fr (F b z) : ℂ) / _)`. Clear the denominators using the available nonvanishing facts. Take the linear combination `e`.

Establish `e` using `(hp t ht).2 z`. Simplify using `only [Units.val_div_eq_div_val, MulEquiv.apply_symm_apply]`. Express the relevant statement in the definitionally equal form `_ * _ * ((fr (F H.w0 z) : ℂ) / _) = (fr (z + F H.w0 z) : ℂ) / _`. Clear the denominators using the available nonvanishing facts. Take the linear combination `e`.
-/
theorem valSt (hL : Laws) (hFam : BrFamSt) (hEx : FibExSt) (hGrp : FibGrpSt) (hCube : FibCubeSt) (hSym : FibSymSt)
    (hRos : FibRosSt) (hPrim : FibPrimSt) (hSec : FibSecSt) (hLie : FibLieSt) : ValSt := by
  intro E _ _ _ H D R _ _ _ A
  letI := H.starRing
  obtain ⟨g, Λ, Hm, χ, Ef, ex, fr, hf, hEf, hbij⟩ := hEx R A.D₀.P A.ν.J A.ν.good
  obtain ⟨hdisc, hfull, hherm, hpos, hnorm, hχ, hadd, hsurj, hker, hfr, hlift⟩ := hGrp R A.D₀ _ g Λ Hm χ ex fr hf
  have hcube := hCube R A.D₀ _ g Λ Hm χ ex fr hf
  obtain ⟨hsym, hneg⟩ := hSym R A.D₀ _ g Λ Hm χ ex fr hf
  have hros := hRos R A.D₀ _ g Λ Hm χ ex fr hf
  have hprim := hPrim R A.D₀ _ g Λ Hm χ ex fr hf
  obtain ⟨θ, hθ, hθv⟩ := hSec R A.D₀ _ g Λ Hm χ ex fr hf A.ν.th
  have hlie := hLie R A.D₀ _ g Λ Hm χ ex fr hf
  obtain ⟨F, hF⟩ := exists_ringHom_lift A.oa.onB.toRingAct ex hadd hlift
  have hmem : ∀ a, ∀ l ∈ Λ, F a l ∈ Λ := fun a l hl => by
    haveI := A.oa.onB.hom a
    rw [← hker, hF, (hker l).2 hl, MonObj.one_comp]
  have hadj : ∀ a z w, hermForm Hm (F a z) w = hermForm Hm z (F (star a) w) := fun a => by
    haveI := A.oa.onB.hom a
    haveI := A.oa.onB.hom (star a)
    obtain ⟨r, hr⟩ := exists_ros hL.globalFns A.D₀.P.isAb A.D₀.P.isLB _ _ (A.oa.onB.rosati a)
    exact (hros _ _ (A.oa.onB.hom a) (A.oa.onB.hom (star a)) _ _ (hF a) (hF (star a)) r hr).1
  let B : An H :=
    { gB := g, abelian₂ := Λ, discrete := hdisc, full := hfull, Hm := Hm, Hm_herm := hherm, Hm_pos := hpos, Ef := Ef,
      Ef_eq := hEf, Ef_bij := hbij, chi := χ, chi_norm := hnorm, chi_add := hχ, chi_neg := hneg, F := F,
      F_mem := hmem, F_adj := hadj, X := PUnit, ct := 0, ct_smul := fun a _ => (map_zero (F a)).symm, T := 0,
      T_symm := fun _ _ => rfl, T_adj := fun _ _ _ => rfl, psi := fun _ => 1, psi_neg := fun _ => rfl,
      psi_add := fun _ _ => by simp, be := 0, be_symm := fun _ _ => rfl, be_pos := fun _ h => (h rfl).elim,
      be_adj := fun _ _ _ => rfl, be_even := fun _ => dvd_zero _ }
  have hrg := rg_ne_zero A.ν
  have h0 := (fr 0).ne_zero
  have hw : ∀ z w, hermForm Hm z w = hermForm Hm z (F H.w0 w) + hermForm Hm (F H.w0 z) w := fun z w => by
    rw [hadj]
    refine Eq.trans ?_ (B.H_add_right z (F H.w0 w) (F (star H.w0) w))
    rw [← LinearMap.add_apply, ← map_add, show H.w0 + star H.w0 = 1 from cmField_host_element_add_conj_eq_one H, map_one]
    rfl
  have hp := hprim _ (A.oa.onB.hom H.w0) (F H.w0) (hmem H.w0) (hF H.w0) hw Ef hEf
  have hth : ∀ z, A.N.th (A.ν.eA.symm (ex z)) = θ z * fr 0 / A.ν.rg * ((fr z / fr 0 : ℂˣ) : ℂ) := fun z => by
    have e := A.ν.th_eq (A.ν.eA.symm (ex z))
    rw [MulEquiv.apply_symm_apply, hθv] at e
    change _ * A.ν.rg = _ at e
    rw [Units.val_div_eq_div_val, eq_div_of_mul_eq hrg e]
    field_simp
  refine ⟨B, fun z => A.ν.eA.symm (ex z), fun z => fr z / fr 0, fun z => θ z * fr 0 / A.ν.rg,
    ⟨fun z w => (congrArg A.ν.eA.symm (hadd z w)).trans (map_mul _ _ _), A.ν.eA.symm.surjective.comp hsurj,
      fun z => (map_eq_one_iff _ A.ν.eA.symm.injective).trans (hker z), div_self' _, fun l z => ?_, fun x y z => ?_,
      fun x => ?_, ⟨by simp only [div_eq_mul_inv]; exact (hθ.mul_const _).mul_const _, fun l z => ?_⟩, hth⟩, ?_, ?_, fun τ => ?_, fun a z => ?_,
      fun a b r hr x z => ?_, fun t ht z => ?_⟩
  · beta_reduce
    rw [Units.val_div_eq_div_val, Units.val_div_eq_div_val, hfr l z, mul_div_assoc]
    rfl
  · refine Units.ext ?_
    have e := hcube x y z
    simp only [Units.val_mul, Units.val_div_eq_div_val, A.ν.θ_eq, MulEquiv.apply_symm_apply]
    field_simp
    linear_combination e
  · refine Units.ext ?_
    have e := hsym x
    simp only [Units.val_mul, Units.val_div_eq_div_val, A.ν.σ_eq, MulEquiv.apply_symm_apply]
    rw [← e, mul_div_assoc]
  · have e₁ := hθv (z + l)
    rw [hadd, (hker l).2 l.2, _root_.mul_one, hθv, hfr l z, ← _root_.mul_assoc] at e₁
    have e₂ := mul_right_cancel₀ (fr (z + l)).ne_zero e₁
    change θ (z + l) * fr 0 / A.ν.rg = (χ l * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l)) ^ 1 *
      Complex.exp (Real.pi * B.H 0 l) * (θ z * fr 0 / A.ν.rg)
    rw [← e₂, B.H_zero_left, mul_zero, Complex.exp_zero]
    ring
  · intro hz
    haveI := A.closed
    obtain ⟨-, -, -, ⟨s, f, hs, hf0⟩, hv, -⟩ := hFam R A.D₀ A.even A.bimult ℂ A.N A.ν 1 le_rfl
    obtain ⟨c, rfl⟩ := hv s f hs
    refine hf0 (funext fun α => funext fun x => ?_)
    obtain ⟨z, hz'⟩ := hsurj (A.ν.eA (x * A.N.c α))
    have e := hth z
    rw [hz', MulEquiv.symm_apply_apply, congrFun hz z] at e
    simp [NumD.vth, e]
  · obtain ⟨t, h₁, h₂, -⟩ := A.w0
    exact (hp t ⟨h₁, h₂⟩).1
  · obtain ⟨n, h₁, h₂⟩ := A.det τ
    rw [← h₂]
    exact congrArg (· + _) (hlie _ (ofRingAct A.oa.onB.toRingAct) (fun a => F a) hF τ n h₁)
  · simp only [MulEquiv.apply_symm_apply]
    exact hF a z
  · have e := (hros _ _ (A.oa.onB.hom a) (A.oa.onB.hom b) _ _ (hF a) (hF b) r hr).2 x z
    simp only [Units.val_div_eq_div_val, MulEquiv.apply_symm_apply]
    change _ * ((fr (F a x) : ℂ) / _) * _ * ((fr (x + F b z) : ℂ) / _) = (fr (F a x + z) : ℂ) / _ * _ * ((fr (F b z) : ℂ) / _)
    field_simp
    linear_combination e
  · have e := (hp t ht).2 z
    simp only [Units.val_div_eq_div_val, MulEquiv.apply_symm_apply]
    change _ * _ * ((fr (F H.w0 z) : ℂ) / _) = (fr (z + F H.w0 z) : ℂ) / _
    field_simp
    linear_combination e

end GlobalTheory.Ex.Arch.AbVal
end
