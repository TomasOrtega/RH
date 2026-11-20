import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox

noncomputable section

namespace GlobalTheory.RowLev

open Formalism.MainNotions.S MeasureTheory NumberField IsDedekindDomain Matrix

structure Red (I : AutInst) (g : ℕ) (Q : Type) [Group Q] where
  toFun : I.Gf → Q
  map_mul : ∀ x ∈ I.Kset, ∀ y ∈ I.Kset, toFun (x * y) = toFun x * toFun y
  ker : ∀ x ∈ I.Kset, toFun x = 1 ↔ x ∈ I.Kg g
  surj : ∀ q : Q, ∃ x ∈ I.Kset, toFun x = q

def Red.lift {I : AutInst} {g : ℕ} {Q : Type} [Group Q] (ρ : Red I g Q) (μf : Measure I.Gf)
    (a : MonoidAlgebra ℂ Q) : I.Gf → ℂ := by
  classical
  exact fun x => if x ∈ I.Kset then a.coeff (ρ.toFun x) / ((μf (I.Kg g)).toReal : ℂ) else 0

def IsSA {Q : Type} [Group Q] (a : MonoidAlgebra ℂ Q) : Prop := ∀ q : Q, a.coeff q⁻¹ = star (a.coeff q)

def tensAlg {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]
    (a : ∀ i, MonoidAlgebra ℂ (G i)) : MonoidAlgebra ℂ (∀ i, G i) :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun h : ∀ i, G i => ∏ i, (a i).coeff (h i))

def zSet {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)] {Lab : ι → Type}
    (z : ∀ i, Lab i → MonoidAlgebra ℂ (G i)) (S : Set (∀ i, Lab i)) : MonoidAlgebra ℂ (∀ i, G i) :=
  ∑ᶠ t ∈ S, tensAlg fun i => z i (t i)

def IsSeries {Q Lab : Type} [Group Q] (z : Lab → MonoidAlgebra ℂ Q) : Prop :=
  (∀ f, z f * z f = z f) ∧ (∀ f a, z f * a = a * z f) ∧ (∀ f f', f ≠ f' → z f * z f' = 0) ∧
    ∃ T : Finset Lab, (∀ f, f ∉ T → z f = 0) ∧ ∑ f ∈ T, z f = 1

def extId (I : AutInst) (𝔞 : Ideal (𝓞 I.E)) : Ideal (IntAf I.F I.E) :=
  Ideal.span {z : IntAf I.F I.E | ∃ a ∈ 𝔞, (z : TensorProduct I.F I.E (Af I.F)) = Formalism.UG.inclE (F := I.F) (Af I.F) (a : I.E)}

def hAf (I : AutInst) (x y : Fin I.n → TensorProduct I.F I.E (Af I.F)) : TensorProduct I.F I.E (Af I.F) :=
  Formalism.UG.hform (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))) x y

structure PlFrame (I : AutInst) (N p : ℕ) (w : HeightOneSpectrum (𝓞 I.E)) where
  r : IntAf I.F I.E →+* ZMod p
  r_ker : ∀ (a : 𝓞 I.E) (h : Formalism.UG.inclE (F := I.F) (Af I.F) (a : I.E) ∈ IntAf I.F I.E),
    r ⟨_, h⟩ = 0 ↔ a ∈ w.asIdeal
  c : I.Lf →ₛₗ[r] (Fin N → ZMod p)
  c_surj : Function.Surjective c
  c_ker : ∀ y : I.Lf, c y = 0 ↔
    (y : Fin I.n → TensorProduct I.F I.E (Af I.F)) ∈ extId I w.asIdeal • I.Lf

abbrev GProd (N : ℕ) (g : Fin 2 → ℕ) (Pl : Fin 2 → Type) : Type :=
  ∀ kv : (Σ k : Fin 2, Pl k), GL (Fin N) (ZMod (g kv.1))

def ActsBy {I : AutInst} {N : ℕ} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type}
    {w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)} (fr : ∀ k v, PlFrame I N (g k) (w k v))
    (ρ : I.Gf → GProd N g Pl) : Prop :=
  ∀ x ∈ I.Kset, ∀ (k : Fin 2) (v : Pl k) (y : I.Lf) (h : I.fmat x *ᵥ (y : Fin I.n → _) ∈ I.Lf),
    (fr k v).c ⟨_, h⟩ = ((ρ x ⟨k, v⟩ : GL (Fin N) (ZMod (g k))) : Matrix (Fin N) (Fin N) (ZMod (g k))) *ᵥ (fr k v).c y

def IsConj (I : AutInst) (w w' : HeightOneSpectrum (𝓞 I.E)) : Prop :=
  ∀ a b : 𝓞 I.E, (b : I.E) = star (a : I.E) → (a ∈ w.asIdeal ↔ b ∈ w'.asIdeal)

def IsChoice (I : AutInst) (g : Fin 2 → ℕ) (Pl : Fin 2 → Type)
    (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)) : Prop :=
  (∀ k, (g k).Prime) ∧ g 0 ≠ g 1 ∧ (∀ k, (Ideal.span {((g k : ℕ) : 𝓞 I.E)}).IsRadical) ∧
    (∀ k v, ((g k : ℕ) : 𝓞 I.E) ∈ (w k v).asIdeal ∧ Ideal.absNorm (w k v).asIdeal = g k) ∧
    (∀ k, Function.Injective (w k)) ∧ (∀ k v v', ¬ IsConj I (w k v) (w k v')) ∧
    ∀ k (u : HeightOneSpectrum (𝓞 I.E)), ((g k : ℕ) : 𝓞 I.E) ∈ u.asIdeal → ∃ v, u = w k v ∨ IsConj I (w k v) u

open Formalism.UG Formalism.UG.P
open scoped TensorProduct

namespace Inhab

def Ksub (I : AutInst) : Subgroup I.Gf :=
  (Formalism.UG.stabGL I.Lf).comap (Formalism.UG.UPts I.cm.sig I.J (Af I.F)).subtype

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_Ksub (I : AutInst) (x : I.Gf) : x ∈ Ksub I ↔ x ∈ I.Kset := Iff.rfl

/- English proof (translation)
The claim follows from `(hx y).1 hy`.
-/
theorem mulVec_mem {I : AutInst} {x : I.Gf} (hx : x ∈ I.Kset) {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    I.fmat x *ᵥ y ∈ I.Lf := (hx y).1 hy

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fmat_mul (I : AutInst) (x y : I.Gf) : I.fmat (x * y) = I.fmat x * I.fmat y := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fmat_one (I : AutInst) : I.fmat 1 = 1 := rfl

def KgSub (I : AutInst) (g : ℕ) : Subgroup (Ksub I) where
  carrier := {x | (x : I.Gf) ∈ I.Kg g}
  one_mem' := ⟨(Ksub I).one_mem, fun y _ => ⟨0, zero_mem _, by
    rw [OneMemClass.coe_one, fmat_one]; simp⟩⟩
  mul_mem' := by
    rintro x w ⟨hx, hx'⟩ ⟨hw, hw'⟩
    refine ⟨(x * w).2, fun y hy => ?_⟩
    obtain ⟨z, hz, e⟩ := hx' _ (mulVec_mem hw hy)
    obtain ⟨z', hz', e'⟩ := hw' y hy
    refine ⟨z + z', add_mem hz hz', ?_⟩
    rw [smul_add, ← e, ← e', Subgroup.coe_mul, fmat_mul]
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, sub_mul, one_mul]
    abel
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨x⁻¹.2, fun y hy => ?_⟩
    obtain ⟨z, hz, e⟩ := hx' _ (mulVec_mem (x⁻¹).2 hy)
    refine ⟨-z, neg_mem hz, ?_⟩
    rw [smul_neg, ← e]
    have h1 : I.fmat x * I.fmat (x⁻¹ : Ksub I) = 1 := by
      rw [← fmat_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, sub_mul, one_mul, h1]
    abel

instance (I : AutInst) (g : ℕ) : (KgSub I g).Normal := ⟨fun x hx k => by
  refine ⟨(k * x * k⁻¹).2, fun y hy => ?_⟩
  obtain ⟨z, hz, e⟩ := hx.2 _ (mulVec_mem (k⁻¹).2 hy)
  refine ⟨I.fmat k *ᵥ z, mulVec_mem k.2 hz, ?_⟩
  have h1 : I.fmat k * I.fmat (k⁻¹ : Ksub I) = 1 := by
    rw [← fmat_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
  rw [← Matrix.mulVec_smul, ← e, Subgroup.coe_mul, Subgroup.coe_mul, fmat_mul, fmat_mul]
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_sub,
    h1, mul_assoc, sub_mul, one_mul, mul_sub]⟩

open Classical in

def quotRed (I : AutInst) (g : ℕ) : Red I g (Ksub I ⧸ KgSub I g) where
  toFun x := if h : x ∈ Ksub I then QuotientGroup.mk ⟨x, h⟩ else 1
  map_mul x hx y hy := by
    have hx' : x ∈ Ksub I := hx
    have hy' : y ∈ Ksub I := hy
    rw [dif_pos hx', dif_pos hy', dif_pos (mul_mem hx' hy')]
    rfl
  ker x hx := by
    have hx' : x ∈ Ksub I := hx
    rw [dif_pos hx', QuotientGroup.eq_one_iff]
    rfl
  surj q := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨x, x.2, dif_pos x.2⟩

end Inhab

open Inhab

namespace Red

variable {I : AutInst} {g : ℕ} {Q : Type} [Group Q] (ρ : Red I g Q)

def toHom : Ksub I →* Q := MonoidHom.mk' (fun x => ρ.toFun x) fun x y => ρ.map_mul x x.2 y y.2

/- English proof (translation)
The claim follows from `ρ.toHom.map_one`.
-/
theorem map_one : ρ.toFun 1 = 1 := ρ.toHom.map_one

/- English proof (translation)
The claim follows from `ρ.toHom.map_inv ⟨x, hx⟩`.
-/
theorem map_inv {x : I.Gf} (hx : x ∈ I.Kset) : ρ.toFun x⁻¹ = (ρ.toFun x)⁻¹ := ρ.toHom.map_inv ⟨x, hx⟩

def quotEquiv : (Ksub I ⧸ KgSub I g) ≃* Q :=
  (QuotientGroup.quotientMulEquivOfEq (M := KgSub I g) (N := ρ.toHom.ker)
    (Subgroup.ext fun x : Ksub I => (ρ.ker x x.2).symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ.toHom fun q => by
      obtain ⟨x, hx, e⟩ := ρ.surj q
      exact ⟨⟨x, hx⟩, e⟩)

/- English proof (translation)
Unfold `Red.lift`. Conclude with `if_pos hx`.
-/
theorem lift_of_mem (μf : Measure I.Gf) (a : MonoidAlgebra ℂ Q) {x : I.Gf} (hx : x ∈ I.Kset) :
    ρ.lift μf a x = a.coeff (ρ.toFun x) / ((μf (I.Kg g)).toReal : ℂ) := by
  unfold Red.lift
  exact if_pos hx

/- English proof (translation)
Unfold `Red.lift`. Conclude with `if_neg hx`.
-/
theorem lift_of_notMem (μf : Measure I.Gf) (a : MonoidAlgebra ℂ Q) {x : I.Gf} (hx : x ∉ I.Kset) :
    ρ.lift μf a x = 0 := by
  unfold Red.lift
  exact if_neg hx

/- English proof (translation)
Distinguish the cases in `hx : x ∈ I.Kset`. Rewrite using `[ρ.lift_of_mem μf _ hx]`. Distinguish the cases in `h : x ∈ I.Kg g`. Rewrite using `[Set.indicator_of_mem h, (ρ.ker x hx).2 h]`. Simplify using `[MonoidAlgebra.one_def]`.

Rewrite using `[Set.indicator_of_notMem h]`. Establish `: ρ.toFun x ≠ 1` using `fun e => h ((ρ.ker x hx).1 e)`. Simplify using `[MonoidAlgebra.one_def, this.symm]`. Rewrite using `[ρ.lift_of_notMem μf _ hx, Set.indicator_of_notMem (fun h => hx h.1)]`.
-/
theorem lift_one (μf : Measure I.Gf) (x : I.Gf) :
    ρ.lift μf 1 x = (I.Kg g).indicator (fun _ => (((μf (I.Kg g)).toReal : ℂ))⁻¹) x := by
  classical
  by_cases hx : x ∈ I.Kset
  · rw [ρ.lift_of_mem μf _ hx]
    by_cases h : x ∈ I.Kg g
    · rw [Set.indicator_of_mem h, (ρ.ker x hx).2 h]
      simp [MonoidAlgebra.one_def]
    · rw [Set.indicator_of_notMem h]
      have : ρ.toFun x ≠ 1 := fun e => h ((ρ.ker x hx).1 e)
      simp [MonoidAlgebra.one_def, this.symm]
  · rw [ρ.lift_of_notMem μf _ hx, Set.indicator_of_notMem (fun h => hx h.1)]

/- English proof (translation)
Distinguish the cases in `hx : x ∈ I.Kset`. Establish `hx' : x⁻¹ ∈ I.Kset` using `(Ksub I).inv_mem hx`. Rewrite using `[ρ.lift_of_mem μf a hx, ρ.lift_of_mem μf a hx', ρ.map_inv hx, ha]`. Simplify using the standard rewrite rules. Establish `hx' : x⁻¹ ∉ I.Kset` using `fun h => hx (by have := (Ksub I).inv_mem h; rwa [inv_inv] at this)`.

Rewrite using `[ρ.lift_of_notMem μf a hx, ρ.lift_of_notMem μf a hx', star_zero]`.
-/
theorem lift_inv (μf : Measure I.Gf) (a : MonoidAlgebra ℂ Q) (ha : IsSA a) (x : I.Gf) :
    ρ.lift μf a x⁻¹ = star (ρ.lift μf a x) := by
  by_cases hx : x ∈ I.Kset
  · have hx' : x⁻¹ ∈ I.Kset := (Ksub I).inv_mem hx
    rw [ρ.lift_of_mem μf a hx, ρ.lift_of_mem μf a hx', ρ.map_inv hx, ha]
    simp
  · have hx' : x⁻¹ ∉ I.Kset := fun h => hx (by have := (Ksub I).inv_mem h; rwa [inv_inv] at this)
    rw [ρ.lift_of_notMem μf a hx, ρ.lift_of_notMem μf a hx', star_zero]

end Red

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tensAlg_coeff {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]
    (a : ∀ i, MonoidAlgebra ℂ (G i)) (h : ∀ i, G i) : (tensAlg a).coeff h = ∏ i, (a i).coeff (h i) := rfl

namespace Inhab

section Reduction
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Rewrite using `[← adelstab_incl_C, map_natCast, map_natCast]`.
-/
theorem levelafC_nat (N : ℕ) : levelafC (F := F) E (N : 𝓞 F) = (N : E ⊗[F] Af F) := by
  rw [← adelstab_incl_C, map_natCast, map_natCast]

def psi (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] : 𝓞 E →+* IntAf F E :=
  ((inclE (F := F) (Af F)).comp (algebraMap (𝓞 E) E)).codRestrict _ fun y => adelstab_incl_int y

/- English proof (translation)
Establish `hfin : Finite (𝓞 E ⧸ w.asIdeal)` using `(Ideal.absNorm_ne_zero_iff _).1 (by rw [hw]; exact hp.ne_zero)`. Use `letI := Fintype.ofFinite (𝓞 E ⧸ w.asIdeal)`. Establish `hc : Fintype.card (𝓞 E ⧸ w.asIdeal) = p`. Rewrite using `[← Nat.card_eq_fintype_card, ← hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Set `e` to `ZMod.ringEquivOfPrime (𝓞 E ⧸ w.asIdeal) hp hc`.

Set `ρ : 𝓞 E →+* ZMod p` to `e.symm.toRingHom.comp (Ideal.Quotient.mk _)`. Establish `hρ : ∀ a, ρ a = 0 ↔ a ∈ w.asIdeal` using `fun a => by show e.symm (Ideal.Quotient.mk _ a) = 0 ↔ _`. Rewrite using `[map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]`. Set `P : Ideal (IntAf F E)` to `Ideal.span {(p : IntAf F E)}`. Set `θ : 𝓞 E →+* IntAf F E ⧸ P` to `(Ideal.Quotient.mk P).comp (psi F E)`.

Establish `hp0 : ((p : ℕ) : 𝓞 F) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `hθ : Function.Surjective θ`. Introduce `q`. Take `⟨s, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Take `⟨b, t, ht, hs⟩` from `csGlob_approx integral_adele_approximation_holds (p : 𝓞 F) hp0 s.1 s.2`.

Use `⟨b, ?_⟩` and prove the remaining obligations. Use `show Ideal.Quotient.mk P _ = _`. Rewrite using `[eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton']`. Use `⟨⟨t, ht⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite `hs` using `[levelafC_nat]`.

Use `show t * ((p : IntAf F E) : E ⊗[F] Af F) = s.1 - inclE (F := F) (Af F) (algebraMap (𝓞 E) E b)`. Rewrite using `[hs]`. Simplify using `[mul_comm]`. Establish `hker : RingHom.ker θ ≤ RingHom.ker ρ`. Introduce `a ha`.

Rewrite `ha`, the goal using `[RingHom.mem_ker]`. Establish `ha' : psi F E a ∈ P` using `Ideal.Quotient.eq_zero_iff_mem.1 ha`. Take `⟨t, ht⟩` from `Ideal.mem_span_singleton'.1 ha'`. Establish `ht' : (t : E ⊗[F] Af F) * (p : E ⊗[F] Af F) = inclE (F` using `F) (Af F) (algebraMap (𝓞 E) E a) := by`. Establish `: (t : E ⊗[F] Af F) * (p : E ⊗[F] Af F) = (psi F E a : E ⊗[F] Af F)`.

Simplify using `using congrArg Subtype.val ht`. Conclude with `this`. Establish `hpE : (p : E) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `h2 : inclE (F` using `F) (Af F) (algebraMap (𝓞 E) E a / p) = t := by`. Rewrite using `[div_eq_mul_inv, map_mul, ← ht', mul_assoc, ← map_natCast (inclE (F := F) (E := E) (Af F)) p, ← map_mul, mul_inv_cancel₀ hpE, map_one, mul_one]`.

Establish `h3` using `csGlob_int (F := F) _ (h2 ▸ t.2)`. Take `⟨b, hb⟩ : ∃ b : 𝓞 E, algebraMap (𝓞 E) E b = algebraMap (𝓞 E) E a / p` from `⟨⟨_, h3⟩, rfl⟩`. Establish `h4 : a = (p : 𝓞 E) * b`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_natCast, hb]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[h4, map_mul, map_natCast, ZMod.natCast_self, zero_mul]`. Use `⟨(RingHom.liftOfSurjective θ hθ ⟨ρ, hker⟩).comp (Ideal.Quotient.mk P), fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[← hρ]`. Use `RingHom.liftOfSurjective_comp_apply θ hθ ⟨ρ, hker⟩ a` as an intermediate fact.

Conclude with `Eq.congr this rfl`.
-/
theorem exists_reduction (p : ℕ) (hp : p.Prime) (w : HeightOneSpectrum (𝓞 E)) (hw : Ideal.absNorm w.asIdeal = p) :
    ∃ r : IntAf F E →+* ZMod p, ∀ a, r (psi F E a) = 0 ↔ a ∈ w.asIdeal := by
  classical
  have hfin : Finite (𝓞 E ⧸ w.asIdeal) := (Ideal.absNorm_ne_zero_iff _).1 (by rw [hw]; exact hp.ne_zero)
  letI := Fintype.ofFinite (𝓞 E ⧸ w.asIdeal)
  have hc : Fintype.card (𝓞 E ⧸ w.asIdeal) = p := by
    rw [← Nat.card_eq_fintype_card, ← hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  let e := ZMod.ringEquivOfPrime (𝓞 E ⧸ w.asIdeal) hp hc
  let ρ : 𝓞 E →+* ZMod p := e.symm.toRingHom.comp (Ideal.Quotient.mk _)
  have hρ : ∀ a, ρ a = 0 ↔ a ∈ w.asIdeal := fun a => by
    show e.symm (Ideal.Quotient.mk _ a) = 0 ↔ _
    rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
  let P : Ideal (IntAf F E) := Ideal.span {(p : IntAf F E)}
  let θ : 𝓞 E →+* IntAf F E ⧸ P := (Ideal.Quotient.mk P).comp (psi F E)
  have hp0 : ((p : ℕ) : 𝓞 F) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hθ : Function.Surjective θ := by
    intro q
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨b, t, ht, hs⟩ := csGlob_approx integral_adele_approximation_holds (p : 𝓞 F) hp0 s.1 s.2
    refine ⟨b, ?_⟩
    show Ideal.Quotient.mk P _ = _
    rw [eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton']
    refine ⟨⟨t, ht⟩, Subtype.ext ?_⟩
    rw [levelafC_nat] at hs
    show t * ((p : IntAf F E) : E ⊗[F] Af F) = s.1 - inclE (F := F) (Af F) (algebraMap (𝓞 E) E b)
    rw [hs]
    simp [mul_comm]
  have hker : RingHom.ker θ ≤ RingHom.ker ρ := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    have ha' : psi F E a ∈ P := Ideal.Quotient.eq_zero_iff_mem.1 ha
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 ha'
    have ht' : (t : E ⊗[F] Af F) * (p : E ⊗[F] Af F) = inclE (F := F) (Af F) (algebraMap (𝓞 E) E a) := by
      have : (t : E ⊗[F] Af F) * (p : E ⊗[F] Af F) = (psi F E a : E ⊗[F] Af F) := by
        simpa using congrArg Subtype.val ht
      exact this
    have hpE : (p : E) ≠ 0 := by exact_mod_cast hp.ne_zero
    have h2 : inclE (F := F) (Af F) (algebraMap (𝓞 E) E a / p) = t := by
      rw [div_eq_mul_inv, map_mul, ← ht', mul_assoc, ← map_natCast (inclE (F := F) (E := E) (Af F)) p, ← map_mul,
        mul_inv_cancel₀ hpE, map_one, mul_one]
    have h3 := csGlob_int (F := F) _ (h2 ▸ t.2)
    obtain ⟨b, hb⟩ : ∃ b : 𝓞 E, algebraMap (𝓞 E) E b = algebraMap (𝓞 E) E a / p := ⟨⟨_, h3⟩, rfl⟩
    have h4 : a = (p : 𝓞 E) * b := by
      apply RingOfIntegers.coe_injective
      rw [map_mul, map_natCast, hb]
      field_simp
    rw [h4, map_mul, map_natCast, ZMod.natCast_self, zero_mul]
  refine ⟨(RingHom.liftOfSurjective θ hθ ⟨ρ, hker⟩).comp (Ideal.Quotient.mk P), fun a => ?_⟩
  rw [← hρ]
  have := RingHom.liftOfSurjective_comp_apply θ hθ ⟨ρ, hker⟩ a
  exact Eq.congr this rfl

/- English proof (translation)
Establish `hp0 : ((p : ℕ) : 𝓞 F) ≠ 0` using `by exact_mod_cast hp`. Take `⟨b, t, ht, hs⟩` from `csGlob_approx integral_adele_approximation_holds (p : 𝓞 F) hp0 s.1 s.2`. Rewrite `hs` using `[levelafC_nat]`. Use `⟨b, ⟨t, ht⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[hs]`.

Simplify using `only [Subring.coe_add, Subring.coe_mul, Subring.coe_natCast]`. Both sides reduce to the same expression.
-/
theorem exists_approx {p : ℕ} (hp : p ≠ 0) (s : IntAf F E) :
    ∃ (b : 𝓞 E) (t : IntAf F E), s = psi F E b + (p : IntAf F E) * t := by
  have hp0 : ((p : ℕ) : 𝓞 F) ≠ 0 := by exact_mod_cast hp
  obtain ⟨b, t, ht, hs⟩ := csGlob_approx integral_adele_approximation_holds (p : 𝓞 F) hp0 s.1 s.2
  rw [levelafC_nat] at hs
  refine ⟨b, ⟨t, ht⟩, Subtype.ext ?_⟩
  rw [hs]
  simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_natCast]
  rfl

end Reduction

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `s h`. Rewrite `h` using `[RingHom.mem_ker]`. Take `⟨b, t, e⟩` from `exists_approx hp s`. Rewrite `e` using `[← map_natCast (psi I.F I.E)]`.

Establish `hpr : r (psi I.F I.E (p : 𝓞 I.E)) = 0` using `by rw [map_natCast, map_natCast, ZMod.natCast_self]`. Establish `hb : r (psi I.F I.E b) = 0`. Rewrite `h` using `[e, map_add, _root_.map_mul, hpr, zero_mul, add_zero]`. Conclude with `h`. Rewrite using `[e]`.

Conclude with `add_mem (Ideal.subset_span ⟨b, (hr b).1 hb, rfl⟩) (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, (hr _).1 hpr, rfl⟩))`. Rewrite using `[extId, Ideal.span_le]`. Introduce and unpack `⟨z, hz⟩ ⟨b, hb, rfl⟩`. Conclude with `(hr b).2 hb`.
-/
theorem ker_eq_extId {I : AutInst} {p : ℕ} (hp : p ≠ 0) {w : HeightOneSpectrum (𝓞 I.E)}
    (r : IntAf I.F I.E →+* ZMod p) (hr : ∀ a, r (psi I.F I.E a) = 0 ↔ a ∈ w.asIdeal) :
    RingHom.ker r = extId I w.asIdeal := by
  apply le_antisymm
  · intro s h
    rw [RingHom.mem_ker] at h
    obtain ⟨b, t, e⟩ := exists_approx hp s
    rw [← map_natCast (psi I.F I.E)] at e
    have hpr : r (psi I.F I.E (p : 𝓞 I.E)) = 0 := by rw [map_natCast, map_natCast, ZMod.natCast_self]
    have hb : r (psi I.F I.E b) = 0 := by
      rw [e, map_add, _root_.map_mul, hpr, zero_mul, add_zero] at h
      exact h
    rw [e]
    exact add_mem (Ideal.subset_span ⟨b, (hr b).1 hb, rfl⟩)
      (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, (hr _).1 hpr, rfl⟩))
  · rw [extId, Ideal.span_le]
    rintro ⟨z, hz⟩ ⟨b, hb, rfl⟩
    exact (hr b).2 hb

def latEnd {I : AutInst} {x : I.Gf} (hx : x ∈ I.Kset) : I.Lf →ₗ[IntAf I.F I.E] I.Lf where
  toFun y := ⟨_, mulVec_mem hx y.2⟩
  map_add' y z := Subtype.ext (Matrix.mulVec_add (I.fmat x) y.1 z.1)
  map_smul' a y := Subtype.ext (Matrix.mulVec_smul (I.fmat x) (a : I.E ⊗[I.F] Af I.F) y.1)

/- English proof (translation)
Establish `hT : ∀ y, c y = 0 → c (T y) = 0` using `fun y hy => by`. Rewrite `hy`, the goal using `[hk]`. Use `Submodule.smul_induction_on hy (fun a ha z _ => ?_) (fun z z' hz hz' => ?_)` and prove the remaining obligations. Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem_smul ha Submodule.mem_top`.

Rewrite using `[map_add]`. Conclude with `add_mem hz hz'`. Use `choose b hb using fun j : Fin N => hc (Pi.single j 1)`. Use `choose s hs using hr`. Use `⟨Matrix.of fun i j => c (T (b j)) i, fun y => ?_⟩` and prove the remaining obligations.

Establish `h0 : c (y - ∑ j, s (c y j) • b j) = 0`. Rewrite using `[map_sub, map_sum, sub_eq_zero]`. Simplify using `only [map_smulₛₗ, hs, hb]`. Conclude with `pi_eq_sum_univ' _`. Establish `h1` using `hT _ h0`.

Rewrite `h1` using `[map_sub, map_sub, map_sum, map_sum, sub_eq_zero]`. Rewrite using `[h1]`. Use function extensionality and compare the values at `i`. Simplify using `only [map_smul, map_smulₛₗ, hs, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.of_apply, mul_comm]`.
-/
theorem exists_matrix {R k L : Type} [CommRing R] [CommRing k] [AddCommGroup L] [Module R L] {N : ℕ}
    (r : R →+* k) (hr : Function.Surjective r) (c : L →ₛₗ[r] (Fin N → k)) (hc : Function.Surjective c)
    (𝔞 : Ideal R) (hk : ∀ y, c y = 0 ↔ y ∈ 𝔞 • (⊤ : Submodule R L)) (T : L →ₗ[R] L) :
    ∃ M : Matrix (Fin N) (Fin N) k, ∀ y, c (T y) = M *ᵥ c y := by
  classical
  have hT : ∀ y, c y = 0 → c (T y) = 0 := fun y hy => by
    rw [hk] at hy ⊢
    refine Submodule.smul_induction_on hy (fun a ha z _ => ?_) (fun z z' hz hz' => ?_)
    · rw [map_smul]; exact Submodule.smul_mem_smul ha Submodule.mem_top
    · rw [map_add]; exact add_mem hz hz'
  choose b hb using fun j : Fin N => hc (Pi.single j 1)
  choose s hs using hr
  refine ⟨Matrix.of fun i j => c (T (b j)) i, fun y => ?_⟩
  have h0 : c (y - ∑ j, s (c y j) • b j) = 0 := by
    rw [map_sub, map_sum, sub_eq_zero]
    simp only [map_smulₛₗ, hs, hb]
    exact pi_eq_sum_univ' _
  have h1 := hT _ h0
  rw [map_sub, map_sub, map_sum, map_sum, sub_eq_zero] at h1
  rw [h1]
  funext i
  simp only [map_smul, map_smulₛₗ, hs, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Matrix.of_apply, mul_comm]

end Inhab

namespace PlFrame

variable {I : AutInst} {N p : ℕ} {w : HeightOneSpectrum (𝓞 I.E)} (fr : PlFrame I N p w)

/- English proof (translation)
The claim follows from `fr.r_ker a _`.
-/
theorem r_psi (a : 𝓞 I.E) : fr.r (psi I.F I.E a) = 0 ↔ a ∈ w.asIdeal := fr.r_ker a _

def residueEquiv : (𝓞 I.E ⧸ w.asIdeal) ≃+* ZMod p :=
  (Ideal.quotEquivOfEq (Ideal.ext fun a => (fr.r_psi a).symm)).trans
    (RingHom.quotientKerEquivOfSurjective (f := fr.r.comp (psi I.F I.E)) (ZMod.ringHom_surjective _))

include fr in

/- English proof (translation)
Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_congr fr.residueEquiv.toEquiv, Nat.card_zmod]`.
-/
theorem absNorm_eq : Ideal.absNorm w.asIdeal = p := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_congr fr.residueEquiv.toEquiv, Nat.card_zmod]

include fr in

/- English proof (translation)
Establish `h0 : p ≠ 0`. Rewrite using `[← fr.absNorm_eq, Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `w.ne_bot`. Use `haveI := w.isPrime`. Use `haveI : IsDomain (ZMod p) := fr.residueEquiv.symm.toMulEquiv.isDomain`.

Conclude with `(CharP.char_is_prime_or_zero (ZMod p) p).resolve_right h0`.
-/
theorem prime : p.Prime := by
  have h0 : p ≠ 0 := by
    rw [← fr.absNorm_eq, Ne, Ideal.absNorm_eq_zero_iff]
    exact w.ne_bot
  haveI := w.isPrime
  haveI : IsDomain (ZMod p) := fr.residueEquiv.symm.toMulEquiv.isDomain
  exact (CharP.char_is_prime_or_zero (ZMod p) p).resolve_right h0

/- English proof (translation)
The claim follows from `ker_eq_extId fr.prime.ne_zero fr.r fr.r_psi`.
-/
theorem ker_r : RingHom.ker fr.r = extId I w.asIdeal := ker_eq_extId fr.prime.ne_zero fr.r fr.r_psi

/- English proof (translation)
The claim follows from `(fr.c_ker y).trans (Submodule.mem_smul_top_iff _ _ y).symm`.
-/
theorem c_eq_zero_iff (y : I.Lf) :
    fr.c y = 0 ↔ y ∈ extId I w.asIdeal • (⊤ : Submodule (IntAf I.F I.E) I.Lf) :=
  (fr.c_ker y).trans (Submodule.mem_smul_top_iff _ _ y).symm

include fr in

/- English proof (translation)
Establish `hk : (extId I w.asIdeal • (⊤ : Submodule (IntAf I.F I.E) I.Lf)).toAddSubgroup = fr.c.toAddMonoidHom.ker` using `AddSubgroup.ext fun y => (fr.c_eq_zero_iff y).symm`. Establish `e : (I.Lf ⧸ (extId I w.asIdeal • (⊤ : Submodule (IntAf I.F I.E) I.Lf)).toAddSubgroup) ≃ (Fin N → ZMod p)` using `((QuotientAddGroup.quotientAddEquivOfEq hk).trans (QuotientAddGroup.quotientKerEquivOfSurjective fr.c.toAddMonoidHom fr.c_surj)).toEquiv`. Use `show Nat.card (I.Lf ⧸ (extId I w.asIdeal • (⊤ : Submodule (IntAf I.F I.E) I.Lf)).toAddSubgroup) = _`. Rewrite using `[Nat.card_congr e, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]`.
-/
theorem card_quot :
    Nat.card (I.Lf ⧸ (extId I w.asIdeal • (⊤ : Submodule (IntAf I.F I.E) I.Lf))) = p ^ N := by
  have hk : (extId I w.asIdeal • (⊤ : Submodule (IntAf I.F I.E) I.Lf)).toAddSubgroup = fr.c.toAddMonoidHom.ker :=
    AddSubgroup.ext fun y => (fr.c_eq_zero_iff y).symm
  have e : (I.Lf ⧸ (extId I w.asIdeal • (⊤ : Submodule (IntAf I.F I.E) I.Lf)).toAddSubgroup) ≃ (Fin N → ZMod p) :=
    ((QuotientAddGroup.quotientAddEquivOfEq hk).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective fr.c.toAddMonoidHom fr.c_surj)).toEquiv
  show Nat.card (I.Lf ⧸ (extId I w.asIdeal • (⊤ : Submodule (IntAf I.F I.E) I.Lf)).toAddSubgroup) = _
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

include fr in

/- English proof (translation)
The claim follows from `Nat.pow_right_injective fr.prime.two_le (fr.card_quot.symm.trans fr'.card_quot)`.
-/
theorem rank_unique {N' : ℕ} (fr' : PlFrame I N' p w) : N = N' :=
  Nat.pow_right_injective fr.prime.two_le (fr.card_quot.symm.trans fr'.card_quot)

def ActsAs (x : I.Gf) (M : Matrix (Fin N) (Fin N) (ZMod p)) : Prop :=
  ∀ (y : I.Lf) (h : I.fmat x *ᵥ (y : Fin I.n → _) ∈ I.Lf), fr.c ⟨_, h⟩ = M *ᵥ fr.c y

/- English proof (translation)
Use `Matrix.toLin'.injective (LinearMap.ext fun t => ?_)` and prove the remaining obligations. Take `⟨y, rfl⟩` from `fr.c_surj t`. Conclude with `(h y (mulVec_mem hx y.2)).symm.trans (h' y _)`.
-/
theorem ActsAs.unique {x : I.Gf} (hx : x ∈ I.Kset) {M M' : Matrix (Fin N) (Fin N) (ZMod p)}
    (h : fr.ActsAs x M) (h' : fr.ActsAs x M') : M = M' := by
  classical
  refine Matrix.toLin'.injective (LinearMap.ext fun t => ?_)
  obtain ⟨y, rfl⟩ := fr.c_surj t
  exact (h y (mulVec_mem hx y.2)).symm.trans (h' y _)

/- English proof (translation)
Introduce `y hy`. Establish `e : I.fmat (x * x') *ᵥ (y : Fin I.n → _) = I.fmat x *ᵥ (I.fmat x' *ᵥ (y : Fin I.n → _))`. Rewrite using `[fmat_mul, Matrix.mulVec_mulVec]`. Rewrite using `[← Matrix.mulVec_mulVec, ← h' y (mulVec_mem hx' y.2), ← h ⟨_, mulVec_mem hx' y.2⟩ (e ▸ hy)]`. Conclude with `congrArg fr.c (Subtype.ext e)`.
-/
theorem ActsAs.mul {x x' : I.Gf} (hx' : x' ∈ I.Kset) {M M' : Matrix (Fin N) (Fin N) (ZMod p)}
    (h : fr.ActsAs x M) (h' : fr.ActsAs x' M') : fr.ActsAs (x * x') (M * M') := by
  intro y hy
  have e : I.fmat (x * x') *ᵥ (y : Fin I.n → _) = I.fmat x *ᵥ (I.fmat x' *ᵥ (y : Fin I.n → _)) := by
    rw [fmat_mul, Matrix.mulVec_mulVec]
  rw [← Matrix.mulVec_mulVec, ← h' y (mulVec_mem hx' y.2), ← h ⟨_, mulVec_mem hx' y.2⟩ (e ▸ hy)]
  exact congrArg fr.c (Subtype.ext e)

/- English proof (translation)
Introduce `y hy`. Rewrite using `[Matrix.one_mulVec]`. Conclude with `congrArg fr.c (Subtype.ext (by show I.fmat 1 *ᵥ (y : Fin I.n → _) = (y : Fin I.n → _)`. Rewrite using `[fmat_one, Matrix.one_mulVec]))`.
-/
theorem actsAs_one : fr.ActsAs 1 1 := by
  intro y hy
  rw [Matrix.one_mulVec]
  exact congrArg fr.c (Subtype.ext (by
    show I.fmat 1 *ᵥ (y : Fin I.n → _) = (y : Fin I.n → _)
    rw [fmat_one, Matrix.one_mulVec]))

/- English proof (translation)
Take `⟨M, hM⟩` from `exists_matrix fr.r (ZMod.ringHom_surjective _) fr.c fr.c_surj (extId I w.asIdeal) fr.c_eq_zero_iff (latEnd hx)`. Conclude with `⟨M, fun y _ => hM y⟩`.
-/
theorem exists_actsAs {x : I.Gf} (hx : x ∈ I.Kset) : ∃ M, fr.ActsAs x M := by
  obtain ⟨M, hM⟩ := exists_matrix fr.r (ZMod.ringHom_surjective _) fr.c fr.c_surj (extId I w.asIdeal)
    fr.c_eq_zero_iff (latEnd hx)
  exact ⟨M, fun y _ => hM y⟩

/- English proof (translation)
Establish `h0 : ∀ x : Ksub I, ∃ M, fr.ActsAs x.1 M` using `fun x => fr.exists_actsAs (x := x.1) x.2`. Use `choose M hM using h0`. Establish `hmul : ∀ x y : Ksub I, M (x * y) = M x * M y` using `fun x y => ActsAs.unique fr (x := x.1 * y.1) (x * y).2 (hM (x * y)) (ActsAs.mul fr (x := x.1) (x' := y.1) y.2 (hM x) (hM y))`. Establish `hone : M 1 = 1` using `ActsAs.unique fr (x := 1) (Ksub I).one_mem (hM 1) fr.actsAs_one`. Take `⟨φ, hφ⟩ : ∃ φ : Ksub I →* GL (Fin N) (ZMod p), ∀ x, (φ x).val = M x` from `⟨(⟨⟨M, hone⟩, hmul⟩ : Ksub I →* Matrix (Fin N) (Fin N) (ZMod p)).toHomUnits, fun _ => rfl⟩`.

Use `⟨fun x => if h : x ∈ Ksub I then φ ⟨x, h⟩ else 1, fun x hx => ?_, fun x hx y hy => ?_⟩` and prove the remaining obligations. Establish `hx' : x ∈ Ksub I` using `hx beta_reduce`. Rewrite using `[dif_pos hx', hφ]`. Conclude with `hM ⟨x, hx'⟩`. Establish `hx' : x ∈ Ksub I` using `hx`.

Establish `hy' : y ∈ Ksub I` using `hy`. Use `beta_reduce`. Rewrite using `[dif_pos hx', dif_pos hy', dif_pos (mul_mem hx' hy'), ← φ.map_mul]`. Both sides reduce to the same expression.
-/
theorem exists_act : ∃ ρ : I.Gf → GL (Fin N) (ZMod p),
    (∀ x ∈ I.Kset, fr.ActsAs x (ρ x : Matrix (Fin N) (Fin N) (ZMod p))) ∧
      ∀ x ∈ I.Kset, ∀ x' ∈ I.Kset, ρ (x * x') = ρ x * ρ x' := by
  classical
  have h0 : ∀ x : Ksub I, ∃ M, fr.ActsAs x.1 M := fun x => fr.exists_actsAs (x := x.1) x.2
  choose M hM using h0
  have hmul : ∀ x y : Ksub I, M (x * y) = M x * M y := fun x y =>
    ActsAs.unique fr (x := x.1 * y.1) (x * y).2 (hM (x * y)) (ActsAs.mul fr (x := x.1) (x' := y.1) y.2 (hM x) (hM y))
  have hone : M 1 = 1 := ActsAs.unique fr (x := 1) (Ksub I).one_mem (hM 1) fr.actsAs_one
  obtain ⟨φ, hφ⟩ : ∃ φ : Ksub I →* GL (Fin N) (ZMod p), ∀ x, (φ x).val = M x :=
    ⟨(⟨⟨M, hone⟩, hmul⟩ : Ksub I →* Matrix (Fin N) (Fin N) (ZMod p)).toHomUnits, fun _ => rfl⟩
  refine ⟨fun x => if h : x ∈ Ksub I then φ ⟨x, h⟩ else 1, fun x hx => ?_, fun x hx y hy => ?_⟩
  · have hx' : x ∈ Ksub I := hx
    beta_reduce
    rw [dif_pos hx', hφ]
    exact hM ⟨x, hx'⟩
  · have hx' : x ∈ Ksub I := hx
    have hy' : y ∈ Ksub I := hy
    beta_reduce
    rw [dif_pos hx', dif_pos hy', dif_pos (mul_mem hx' hy'), ← φ.map_mul]
    rfl

end PlFrame

section Acts

variable {I : AutInst} {N : ℕ} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type}
  {w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)} (fr : ∀ k v, PlFrame I N (g k) (w k v))

/- English proof (translation)
Use `choose ρ h1 h2 using fun k v => (fr k v).exists_act`. Conclude with `⟨fun x kv => ρ kv.1 kv.2 x, fun x hx k v => h1 k v x hx, fun x hx x' hx' => funext fun kv => h2 kv.1 kv.2 x hx x' hx'⟩`.
-/
theorem exists_actsBy : ∃ ρ : I.Gf → GProd N g Pl, ActsBy fr ρ ∧
    ∀ x ∈ I.Kset, ∀ x' ∈ I.Kset, ρ (x * x') = ρ x * ρ x' := by
  choose ρ h1 h2 using fun k v => (fr k v).exists_act
  exact ⟨fun x kv => ρ kv.1 kv.2 x, fun x hx k v => h1 k v x hx,
    fun x hx x' hx' => funext fun kv => h2 kv.1 kv.2 x hx x' hx'⟩

/- English proof (translation)
The claim follows from `funext fun kv => Units.ext (PlFrame.ActsAs.unique (fr kv.1 kv.2) hx (h x hx kv.1 kv.2) (h' x hx kv.1 kv.2))`.
-/
theorem ActsBy.unique {ρ ρ' : I.Gf → GProd N g Pl} (h : ActsBy fr ρ) (h' : ActsBy fr ρ') {x : I.Gf}
    (hx : x ∈ I.Kset) : ρ x = ρ' x :=
  funext fun kv => Units.ext (PlFrame.ActsAs.unique (fr kv.1 kv.2) hx (h x hx kv.1 kv.2) (h' x hx kv.1 kv.2))

end Acts

namespace Inhab

/- English proof (translation)
Take `⟨r, hr⟩` from `exists_reduction (F := I.F) p hp w hw`. Establish `hk` using `ker_eq_extId hp.ne_zero r hr`. Set `c : I.Lf →ₛₗ[r] (Fin I.n → ZMod p)` to `{ toFun := fun y i => r ⟨y.1 i, (hI y.1).1 y.2 i⟩ map_add' := fun x y => funext fun i => by`. Rewrite using `[Pi.add_apply, ← map_add]`. Both sides reduce to the same expression.

Use the proof step `map_smul' := fun a x => funext fun i => by`. Establish `e : (⟨(a • x).1 i, (hI _).1 (a • x).2 i⟩ : IntAf I.F I.E) = a * ⟨x.1 i, (hI x.1).1 x.2 i⟩` using `rfl`. Use `show r _ = r a * r _`. Rewrite using `[e, _root_.map_mul] }`. Use `⟨⟨r, fun a _ => hr a, c, ?_, fun y => ?_⟩, fun _ _ => rfl⟩` and prove the remaining obligations.

Introduce `t choose s hs using ZMod.ringHom_surjective r`. Conclude with `⟨⟨fun i => (s (t i) : I.E ⊗[I.F] Af I.F), (hI _).2 fun i => (s (t i)).2⟩, funext fun i => hs (t i)⟩`. Rewrite using `[← Submodule.mem_smul_top_iff, ← hk]`. Use `⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Establish `he : ∀ k, (Pi.single k 1 : Fin I.n → I.E ⊗[I.F] Af I.F) ∈ I.Lf` using `fun k => (hI _).2 fun i => by`.

Distinguish the cases in `h : i = k`. Substitute `h` using the available equality. Rewrite using `[Pi.single_eq_same]`. Conclude with `one_mem _`. Rewrite using `[Pi.single_eq_of_ne h]`.

Conclude with `zero_mem _`. Establish `e : y = ∑ k, (⟨y.1 k, (hI y.1).1 y.2 k⟩ : IntAf I.F I.E) • (⟨_, he k⟩ : I.Lf)`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_sum]`. Use function extensionality and compare the values at `j`.

Rewrite using `[Finset.sum_apply, Finset.sum_eq_single j]`. Use `show _ = y.1 j * (Pi.single j 1 : Fin I.n → I.E ⊗[I.F] Af I.F) j`. Rewrite using `[Pi.single_eq_same, mul_one]`. Introduce `b _ hb show y.1 b * (Pi.single b 1 : Fin I.n → I.E ⊗[I.F] Af I.F) j = 0`. Rewrite using `[Pi.single_eq_of_ne (Ne.symm hb), mul_zero]`.

Conclude with `fun h => absurd (Finset.mem_univ j) h`. Rewrite using `[e]`. Conclude with `sum_mem fun k _ => Submodule.smul_mem_smul (congrFun h k) Submodule.mem_top`. Use `Submodule.smul_induction_on h (fun a ha x _ => ?_) (fun x y hx hy => ?_)` and prove the remaining obligations. Rewrite using `[map_smulₛₗ, RingHom.mem_ker.1 ha, zero_smul]`.

Rewrite using `[map_add, hx, hy, add_zero]`.
-/
theorem exists_frame (I : AutInst) (hI : ∀ y, y ∈ I.Lf ↔ ∀ i, y i ∈ IntAf I.F I.E) (p : ℕ) (hp : p.Prime)
    (w : HeightOneSpectrum (𝓞 I.E)) (hw : Ideal.absNorm w.asIdeal = p) :
    ∃ fr : PlFrame I I.n p w, ∀ (y : I.Lf) (i : Fin I.n), fr.c y i = fr.r ⟨y.1 i, (hI y.1).1 y.2 i⟩ := by
  classical
  obtain ⟨r, hr⟩ := exists_reduction (F := I.F) p hp w hw
  have hk := ker_eq_extId hp.ne_zero r hr
  let c : I.Lf →ₛₗ[r] (Fin I.n → ZMod p) :=
    { toFun := fun y i => r ⟨y.1 i, (hI y.1).1 y.2 i⟩
      map_add' := fun x y => funext fun i => by
        rw [Pi.add_apply, ← map_add]; rfl
      map_smul' := fun a x => funext fun i => by
        have e : (⟨(a • x).1 i, (hI _).1 (a • x).2 i⟩ : IntAf I.F I.E) =
          a * ⟨x.1 i, (hI x.1).1 x.2 i⟩ := rfl
        show r _ = r a * r _
        rw [e, _root_.map_mul] }
  refine ⟨⟨r, fun a _ => hr a, c, ?_, fun y => ?_⟩, fun _ _ => rfl⟩
  · intro t
    choose s hs using ZMod.ringHom_surjective r
    exact ⟨⟨fun i => (s (t i) : I.E ⊗[I.F] Af I.F), (hI _).2 fun i => (s (t i)).2⟩, funext fun i => hs (t i)⟩
  rw [← Submodule.mem_smul_top_iff, ← hk]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have he : ∀ k, (Pi.single k 1 : Fin I.n → I.E ⊗[I.F] Af I.F) ∈ I.Lf := fun k => (hI _).2 fun i => by
      by_cases h : i = k
      · subst h; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _
    have e : y = ∑ k, (⟨y.1 k, (hI y.1).1 y.2 k⟩ : IntAf I.F I.E) • (⟨_, he k⟩ : I.Lf) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · show _ = y.1 j * (Pi.single j 1 : Fin I.n → I.E ⊗[I.F] Af I.F) j
        rw [Pi.single_eq_same, mul_one]
      · intro b _ hb
        show y.1 b * (Pi.single b 1 : Fin I.n → I.E ⊗[I.F] Af I.F) j = 0
        rw [Pi.single_eq_of_ne (Ne.symm hb), mul_zero]
      · exact fun h => absurd (Finset.mem_univ j) h
    rw [e]
    exact sum_mem fun k _ => Submodule.smul_mem_smul (congrFun h k) Submodule.mem_top
  · refine Submodule.smul_induction_on h (fun a ha x _ => ?_) (fun x y hx hy => ?_)
    · rw [map_smulₛₗ, RingHom.mem_ker.1 ha, zero_smul]
    · rw [map_add, hx, hy, add_zero]

/- English proof (translation)
The claim follows from `fr.rank_unique (exists_frame I hI p fr.prime w fr.absNorm_eq).choose`.
-/
theorem rank_eq_of_std {I : AutInst} (hI : ∀ y, y ∈ I.Lf ↔ ∀ i, y i ∈ IntAf I.F I.E) {N p : ℕ}
    {w : HeightOneSpectrum (𝓞 I.E)} (fr : PlFrame I N p w) : N = I.n :=
  fr.rank_unique (exists_frame I hI p fr.prime w fr.absNorm_eq).choose

/- English proof (translation)
Set `st : 𝓞 I.E →+* 𝓞 I.E` to `RingOfIntegers.mapRingHom (starRingEnd I.E)`. Establish `hst : ∀ a : 𝓞 I.E, (st a : I.E) = star (a : I.E)` using `fun a => rfl`. Establish `hst2 : ∀ a, st (st a) = a` using `fun a => RingOfIntegers.ext (by rw [hst, hst, star_star])`. Establish `hsurj : Function.Surjective st` using `fun a => ⟨st a, hst2 a⟩`. Set `cj : HeightOneSpectrum (𝓞 I.E) → HeightOneSpectrum (𝓞 I.E)` to `fun v => v.comap st hsurj`.

Establish `hcj : ∀ v a, a ∈ (cj v).asIdeal ↔ st a ∈ v.asIdeal` using `fun v a => Iff.rfl`. Establish `hcc : ∀ v, cj (cj v) = v` using `fun v => HeightOneSpectrum.ext (Ideal.ext fun a => by rw [hcj, hcj, hst2])`. Establish `hconj : ∀ v v', IsConj I v v' ↔ v' = cj v` using `fun v v' => by`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use `HeightOneSpectrum.ext (Ideal.ext fun b => ?_)` and prove the remaining obligations. Rewrite using `[hcj]`. Conclude with `(h (st b) b (by rw [hst, star_star])).symm`. Introduce and unpack `rfl a b hab`. Establish `: b = st a` using `RingOfIntegers.ext hab`.

Substitute `this` using the available equality. Rewrite using `[hcj, hst2]`. Establish `hcne : ∀ k (v : HeightOneSpectrum (𝓞 I.E)), ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal → cj v ≠ v` using `fun k v hv h => (hsp k v hv).2.2 ((hconj v v).2 h.symm)`. Establish `hcm : ∀ k (v : HeightOneSpectrum (𝓞 I.E)), ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal → ((g k : ℕ) : 𝓞 I.E) ∈ (cj v).asIdeal` using `fun k v hv => by rw [hcj, map_natCast]; exact hv`. Use `letI : LinearOrder (HeightOneSpectrum (𝓞 I.E)) := linearOrderOfSTO WellOrderingRel`.

Use `⟨fun k => {v : HeightOneSpectrum (𝓞 I.E) // ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal ∧ v < cj v}, fun k v => v.1, ?_, hg, hne, ?_, fun k v => ⟨v.2.1, (hsp k v.1 v.2.1).1⟩, fun k => Subtype.val_injective, ?_, ?_⟩` and prove the remaining obligations. Introduce `k`. Establish `hnu : Ideal.span {((g k : ℕ) : 𝓞 I.E)} ≠ ⊤`. Introduce `h`. Use `congrArg Ideal.absNorm h` as an intermediate fact.

Rewrite `this` using `[Ideal.absNorm_span_natCast, Ideal.absNorm_top]`. Establish `h2` using `(hg k).one_lt`. Establish `h3 : 0 < Module.finrank ℤ (𝓞 I.E)` using `Module.finrank_pos`. Conclude with `(Nat.one_lt_pow h3.ne' h2).ne' this`. Take `⟨P, hP, hle⟩` from `Ideal.exists_le_maximal _ hnu`.

Set `u : HeightOneSpectrum (𝓞 I.E)` to `⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)⟩`. Establish `hu : ((g k : ℕ) : 𝓞 I.E) ∈ u.asIdeal` using `hle (Ideal.mem_span_singleton_self _)`. Break down `lt_or_gt_of_ne (hcne k u hu) with h | h` into its components or cases. Conclude with `⟨⟨cj u, hcm k u hu, by rw [hcc]; exact h⟩⟩`. Conclude with `⟨⟨u, hu, h⟩⟩`.

Introduce `k`. Establish `h0 : Ideal.span {((g k : ℕ) : 𝓞 I.E)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `(hg k).ne_zero` after adjusting the coercions. Establish `hsq : Squarefree (Ideal.span {((g k : ℕ) : 𝓞 I.E)})`.

Rewrite using `[squarefree_iff_irreducible_sq_not_dvd_of_ne_zero h0]`. Introduce `P hP hd`. Establish `hP' : Prime P` using `hP.prime`. Set `u : HeightOneSpectrum (𝓞 I.E)` to `⟨P, Ideal.isPrime_of_prime hP', hP'.ne_zero⟩`. Establish `hm2 : ((g k : ℕ) : 𝓞 I.E) ∈ P ^ 2`.

Rewrite using `[sq]`. Conclude with `Ideal.le_of_dvd hd (Ideal.mem_span_singleton_self _)`. Conclude with `(hsp k u (Ideal.pow_le_self two_ne_zero hm2)).2.1 hm2`. Introduce and unpack `x ⟨m, hm⟩`. Establish `h1 : Ideal.span {((g k : ℕ) : 𝓞 I.E)} ∣ Ideal.span {x} ^ m`.

Rewrite using `[Ideal.span_singleton_pow, Ideal.dvd_span_singleton]`. Conclude with `hm`. Conclude with `Ideal.dvd_span_singleton.1 (hsq.isRadical m _ h1)`. Introduce `k v v' h`. Establish `e : v'.1 = cj v.1` using `(hconj _ _).1 h`.

Establish `h1` using `v.2.2`. Establish `h2` using `v'.2.2`. Rewrite `h2` using `[e, hcc]`. Conclude with `lt_asymm h1 h2`. Introduce `k u hu`.

Break down `lt_or_gt_of_ne (hcne k u hu) with h | h` into its components or cases. Conclude with `⟨⟨cj u, hcm k u hu, by rw [hcc]; exact h⟩, Or.inr ((hconj _ _).2 (hcc u).symm)⟩`. Conclude with `⟨⟨u, hu, h⟩, Or.inl rfl⟩`.
-/
theorem exists_choice (I : AutInst) (g : Fin 2 → ℕ) (hg : ∀ k, (g k).Prime) (hne : g 0 ≠ g 1)
    (hsp : ∀ k (v : HeightOneSpectrum (𝓞 I.E)), ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal →
      Ideal.absNorm v.asIdeal = g k ∧ ((g k : ℕ) : 𝓞 I.E) ∉ v.asIdeal ^ 2 ∧ ¬ IsConj I v v) :
    ∃ (Pl : Fin 2 → Type) (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)), (∀ k, Nonempty (Pl k)) ∧
      IsChoice I g Pl w := by
  classical
  let st : 𝓞 I.E →+* 𝓞 I.E := RingOfIntegers.mapRingHom (starRingEnd I.E)
  have hst : ∀ a : 𝓞 I.E, (st a : I.E) = star (a : I.E) := fun a => rfl
  have hst2 : ∀ a, st (st a) = a := fun a => RingOfIntegers.ext (by rw [hst, hst, star_star])
  have hsurj : Function.Surjective st := fun a => ⟨st a, hst2 a⟩
  let cj : HeightOneSpectrum (𝓞 I.E) → HeightOneSpectrum (𝓞 I.E) := fun v => v.comap st hsurj
  have hcj : ∀ v a, a ∈ (cj v).asIdeal ↔ st a ∈ v.asIdeal := fun v a => Iff.rfl
  have hcc : ∀ v, cj (cj v) = v := fun v => HeightOneSpectrum.ext (Ideal.ext fun a => by rw [hcj, hcj, hst2])
  have hconj : ∀ v v', IsConj I v v' ↔ v' = cj v := fun v v' => by
    constructor
    · intro h
      refine HeightOneSpectrum.ext (Ideal.ext fun b => ?_)
      rw [hcj]
      exact (h (st b) b (by rw [hst, star_star])).symm
    · rintro rfl a b hab
      have : b = st a := RingOfIntegers.ext hab
      subst this
      rw [hcj, hst2]
  have hcne : ∀ k (v : HeightOneSpectrum (𝓞 I.E)), ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal → cj v ≠ v :=
    fun k v hv h => (hsp k v hv).2.2 ((hconj v v).2 h.symm)
  have hcm : ∀ k (v : HeightOneSpectrum (𝓞 I.E)), ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal →
      ((g k : ℕ) : 𝓞 I.E) ∈ (cj v).asIdeal := fun k v hv => by rw [hcj, map_natCast]; exact hv
  letI : LinearOrder (HeightOneSpectrum (𝓞 I.E)) := linearOrderOfSTO WellOrderingRel
  refine ⟨fun k => {v : HeightOneSpectrum (𝓞 I.E) // ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal ∧ v < cj v},
    fun k v => v.1, ?_, hg, hne, ?_, fun k v => ⟨v.2.1, (hsp k v.1 v.2.1).1⟩, fun k => Subtype.val_injective, ?_, ?_⟩
  · intro k
    have hnu : Ideal.span {((g k : ℕ) : 𝓞 I.E)} ≠ ⊤ := by
      intro h
      have := congrArg Ideal.absNorm h
      rw [Ideal.absNorm_span_natCast, Ideal.absNorm_top] at this
      have h2 := (hg k).one_lt
      have h3 : 0 < Module.finrank ℤ (𝓞 I.E) := Module.finrank_pos
      exact (Nat.one_lt_pow h3.ne' h2).ne' this
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hnu
    let u : HeightOneSpectrum (𝓞 I.E) :=
      ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)⟩
    have hu : ((g k : ℕ) : 𝓞 I.E) ∈ u.asIdeal := hle (Ideal.mem_span_singleton_self _)
    rcases lt_or_gt_of_ne (hcne k u hu) with h | h
    · exact ⟨⟨cj u, hcm k u hu, by rw [hcc]; exact h⟩⟩
    · exact ⟨⟨u, hu, h⟩⟩
  · intro k
    have h0 : Ideal.span {((g k : ℕ) : 𝓞 I.E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact_mod_cast (hg k).ne_zero
    have hsq : Squarefree (Ideal.span {((g k : ℕ) : 𝓞 I.E)}) := by
      rw [squarefree_iff_irreducible_sq_not_dvd_of_ne_zero h0]
      intro P hP hd
      have hP' : Prime P := hP.prime
      let u : HeightOneSpectrum (𝓞 I.E) := ⟨P, Ideal.isPrime_of_prime hP', hP'.ne_zero⟩
      have hm2 : ((g k : ℕ) : 𝓞 I.E) ∈ P ^ 2 := by
        rw [sq]; exact Ideal.le_of_dvd hd (Ideal.mem_span_singleton_self _)
      exact (hsp k u (Ideal.pow_le_self two_ne_zero hm2)).2.1 hm2
    rintro x ⟨m, hm⟩
    have h1 : Ideal.span {((g k : ℕ) : 𝓞 I.E)} ∣ Ideal.span {x} ^ m := by
      rw [Ideal.span_singleton_pow, Ideal.dvd_span_singleton]; exact hm
    exact Ideal.dvd_span_singleton.1 (hsq.isRadical m _ h1)
  · intro k v v' h
    have e : v'.1 = cj v.1 := (hconj _ _).1 h
    have h1 := v.2.2
    have h2 := v'.2.2
    rw [e, hcc] at h2
    exact lt_asymm h1 h2
  · intro k u hu
    rcases lt_or_gt_of_ne (hcne k u hu) with h | h
    · exact ⟨⟨cj u, hcm k u hu, by rw [hcc]; exact h⟩, Or.inr ((hconj _ _).2 (hcc u).symm)⟩
    · exact ⟨⟨u, hu, h⟩, Or.inl rfl⟩

def negOne (I : AutInst) : I.Gf := ⟨-1, by
  show cT (sigR I.cm.sig (Af I.F)) (Units.val (-1 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))) * _ *
    Units.val (-1 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) = _
  have : cT (sigR I.cm.sig (Af I.F)) (-1 : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) = -1 := by
    rw [cT, Matrix.map_neg _ (map_neg _), Matrix.transpose_neg]
    exact congrArg Neg.neg (cT_one _)
  rw [Units.val_neg, Units.val_one, this]
  simp⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fmat_negOne (I : AutInst) : I.fmat (negOne I) = -1 := rfl

/- English proof (translation)
Introduce `y` and use `by show _ ↔ I.fmat (negOne I) *ᵥ y ∈ I.Lf rw [fmat_negOne, Matrix.neg_mulVec, Matrix.one_mulVec, neg_mem_iff]`.
-/
theorem negOne_mem (I : AutInst) : negOne I ∈ I.Kset := fun y => by
  show _ ↔ I.fmat (negOne I) *ᵥ y ∈ I.Lf
  rw [fmat_negOne, Matrix.neg_mulVec, Matrix.one_mulVec, neg_mem_iff]

/- English proof (translation)
Introduce `y hy`. Rewrite using `[Matrix.neg_mulVec, Matrix.one_mulVec, ← map_neg]`. Conclude with `congrArg fr.c (Subtype.ext (by show I.fmat (negOne I) *ᵥ (y : Fin I.n → _) = -(y : Fin I.n → _)`. Rewrite using `[fmat_negOne, Matrix.neg_mulVec, Matrix.one_mulVec]))`.
-/
theorem actsAs_negOne {I : AutInst} {N p : ℕ} {w : HeightOneSpectrum (𝓞 I.E)} (fr : PlFrame I N p w) :
    fr.ActsAs (negOne I) (-1) := by
  intro y hy
  rw [Matrix.neg_mulVec, Matrix.one_mulVec, ← map_neg]
  exact congrArg fr.c (Subtype.ext (by
    show I.fmat (negOne I) *ᵥ (y : Fin I.n → _) = -(y : Fin I.n → _)
    rw [fmat_negOne, Matrix.neg_mulVec, Matrix.one_mulVec]))

end Inhab

/- English proof (translation)
Use extensionality with `h`. Simplify using `only [tensAlg_coeff, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]`. Rewrite using `[Finset.prod_ite_zero]`. Simplify using `[funext_iff]`.
-/
example {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)] :
    tensAlg (fun i => (1 : MonoidAlgebra ℂ (G i))) = 1 := by
  classical
  ext h
  simp only [tensAlg_coeff, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ => mul_one _, fun _ a => by simp, fun _ _ h => absurd rfl h, {()}, fun _ h => absurd (by simp) h, by simp⟩`.
-/
example (Q : Type) [Group Q] : IsSeries (fun _ : Unit => (1 : MonoidAlgebra ℂ Q)) :=
  ⟨fun _ => mul_one _, fun _ a => by simp, fun _ _ h => absurd rfl h, {()}, fun _ h => absurd (by simp) h, by simp⟩

/- English proof (translation)
The claim follows from `Units.ext (PlFrame.ActsAs.unique (fr kv.1 kv.2) (negOne_mem I) (h _ (negOne_mem I) kv.1 kv.2) (actsAs_negOne _))`.
-/
example {I : AutInst} {N : ℕ} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type} {w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)}
    (fr : ∀ k v, PlFrame I N (g k) (w k v)) (ρ : I.Gf → GProd N g Pl) (h : ActsBy fr ρ) (kv : Σ k, Pl k) :
    ρ (negOne I) kv = -1 :=
  Units.ext (PlFrame.ActsAs.unique (fr kv.1 kv.2) (negOne_mem I) (h _ (negOne_mem I) kv.1 kv.2) (actsAs_negOne _))

end GlobalTheory.RowLev
