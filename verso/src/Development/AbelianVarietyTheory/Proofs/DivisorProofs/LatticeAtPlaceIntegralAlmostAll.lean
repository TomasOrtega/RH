import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyTwoNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqIntegralSpanGenerato

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.LatIntegral

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [incM, Matrix.map_apply, Matrix.smul_apply, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]`. Rewrite using `[TensorProduct.tmul_smul, algebraMap_smul]`.
-/
theorem incM_smul {n d : ℕ} (c : F) (x : Matrix (Fin n) (Fin d) E) :
    incM F (c • x) = algebraMap F (AF F) c • incM F x := by
  ext i j
  simp only [incM, Matrix.map_apply, Matrix.smul_apply, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply]
  rw [TensorProduct.tmul_smul, algebraMap_smul]

/- English proof (translation)
Repeatedly rewrite using `[Finset.sum_mul, add_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_add_distrib, ← hA j, ← hB j, Finset.mul_sum, Finset.mul_sum]`. Apply the tactic sequence `congr 1 <;> refine Finset.sum_congr rfl fun m _ => by ring`.
-/
theorem combo {K M κ : Type} [CommRing K] [Fintype M] [Fintype κ] (p q : κ → K) (A B : κ → M → K) (R : M → K)
    (α β : κ → K) (hA : ∀ j, ∑ m, A j m * R m = α j) (hB : ∀ j, ∑ m, B j m * R m = β j) :
    ∑ m, (∑ j, (p j * A j m + q j * B j m)) * R m = ∑ j, (p j * α j + q j * β j) := by
  simp_rw [Finset.sum_mul, add_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_add_distrib, ← hA j, ← hB j, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun m _ => by ring

end GlobalTheory.LatIntegral

noncomputable section

namespace GlobalTheory.LatIntegral

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Simplify using `only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_sum, map_smul, hr, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul, GlobalTheory.EmbChart.evFin_atPlace, AlgHom.commutes, and_self]`.
-/
theorem locCo_sum {n d : ℕ} {κ : Type} [Fintype κ]
    {B : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n) (Fin d) (AE F E) → AF F} (co : Darboux B κ) (v : Pl F)
    {M : Type} [Fintype M] (a : M → Fv F v) (g : M → Matrix (Fin n) (Fin d) E) (ry rz : M → κ → F)
    (hr : ∀ m, co.e (incM F (g m)) = (fun i => algebraMap F (AF F) (ry m i), fun i => algebraMap F (AF F) (rz m i)))
    (i : κ) :
    (GlobalTheory.LatVac.locCo co v (∑ m, GlobalTheory.EmbChart.atPlace v (a m) • incM F (g m))).1 i =
                 ∑ m, a m * algebraMap F (Fv F v) (ry m i) ∧
      (GlobalTheory.LatVac.locCo co v (∑ m, GlobalTheory.EmbChart.atPlace v (a m) • incM F (g m))).2 i =
        ∑ m, a m * algebraMap F (Fv F v) (rz m i) := by
  simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_sum, map_smul, hr, Prod.fst_sum, Prod.snd_sum,
    Finset.sum_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul, GlobalTheory.EmbChart.evFin_atPlace,
    AlgHom.commutes, and_self]

/- English proof (translation)
Set `I : Matrix (Fin n) (Fin d) E →+ Matrix (Fin n) (Fin d) (AE F E)` to `(inclR (F := F) (E := E) (AF F)).toAddMonoidHom.mapMatrix`. Establish `hI : ∀ J, incM F J = I J` using `fun J => rfl`. Use `⟨fun h => ?_, ?_⟩` and prove the remaining obligations. Proceed by induction on `h using AddSubgroup.closure_induction with`. Consider the case `mem z hz`.

Take `⟨a, ha, hint, x, hx, y, hy, rfl⟩` from `hz`. Establish `hx' : x ∈ Submodule.span ℤ (Set.range ex)` using `by rw [hex]; exact hx`. Establish `hy' : y ∈ Submodule.span ℤ (Set.range fy)` using `by rw [hfy]; exact hy`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).1 hx'`. Take `⟨c', rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).1 hy'`.

Use `⟨fun m => ⟨(c m.1 * c' m.2) • GlobalTheory.AdelicU.evFin F v a, zsmul_mem hint _⟩, ?_⟩` and prove the remaining obligations. Establish `ha'` using `GlobalTheory.VacAny.eq_atPlace_of_at v a ha`. Simplify using `only [hI, GlobalTheory.LatParam.vecMulVec_sum_zsmul, map_sum, map_zsmul, Finset.smul_sum, map_zsmul]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[← ha', smul_comm, smul_assoc]`.

Consider the case `zero => exact ⟨fun _ => 0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, rfl⟩` from `hx`. Take `⟨b, rfl⟩` from `hy`. Conclude with `⟨a + b, by simp only [Pi.add_apply, AddMemClass.coe_add, map_add, add_smul, Finset.sum_add_distrib]⟩`.

Consider the case `neg x _ hx`. Take `⟨a, rfl⟩` from `hx`. Conclude with `⟨-a, by simp only [Pi.neg_apply, NegMemClass.coe_neg, map_neg, neg_smul, Finset.sum_neg_distrib]⟩`. Introduce and unpack `⟨a, rfl⟩`. Use `AddSubgroup.sum_mem _ fun m _ => AddSubgroup.subset_closure ?_` and prove the remaining obligations.

Use `⟨_, GlobalTheory.VacAny.at_atPlace _, ?_, ex m.1, ?_, fy m.2, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.EmbChart.evFin_atPlace]`. Conclude with `(a m).2`. Establish `: ex m.1 ∈ Submodule.span ℤ (Set.range ex)` using `Submodule.subset_span ⟨m.1, rfl⟩`. Rewrite `this` using `[hex]`.

Conclude with `this`. Establish `: fy m.2 ∈ Submodule.span ℤ (Set.range fy)` using `Submodule.subset_span ⟨m.2, rfl⟩`. Rewrite `this` using `[hfy]`. Conclude with `this`.
-/
theorem param {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl F) {kx ky : ℕ} (ex : Fin kx → Fin n → E)
    (fy : Fin ky → Fin d → E) (hex : Submodule.span ℤ (Set.range ex) = X.L.restrictScalars ℤ)
    (hfy : Submodule.span ℤ (Set.range fy) = Y.L.restrictScalars ℤ) (γ : Matrix (Fin n) (Fin d) (AE F E)) :
    γ ∈ latAtV X Y v ↔ ∃ a : Fin kx × Fin ky → v.adicCompletionIntegers F,
      γ = ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • incM F (Matrix.vecMulVec (ex m.1) (fy m.2)) := by
  let I : Matrix (Fin n) (Fin d) E →+ Matrix (Fin n) (Fin d) (AE F E) :=
    (inclR (F := F) (E := E) (AF F)).toAddMonoidHom.mapMatrix
  have hI : ∀ J, incM F J = I J := fun J => rfl
  refine ⟨fun h => ?_, ?_⟩
  · induction h using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hint, x, hx, y, hy, rfl⟩ := hz
      have hx' : x ∈ Submodule.span ℤ (Set.range ex) := by rw [hex]; exact hx
      have hy' : y ∈ Submodule.span ℤ (Set.range fy) := by rw [hfy]; exact hy
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx'
      obtain ⟨c', rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy'
      refine ⟨fun m => ⟨(c m.1 * c' m.2) • GlobalTheory.AdelicU.evFin F v a, zsmul_mem hint _⟩, ?_⟩
      have ha' := GlobalTheory.VacAny.eq_atPlace_of_at v a ha
      simp only [hI, GlobalTheory.LatParam.vecMulVec_sum_zsmul, map_sum, map_zsmul, Finset.smul_sum, map_zsmul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← ha', smul_comm, smul_assoc]
    | zero => exact ⟨fun _ => 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, by simp only [Pi.add_apply, AddMemClass.coe_add, map_add, add_smul, Finset.sum_add_distrib]⟩
    | neg x _ hx =>
      obtain ⟨a, rfl⟩ := hx
      exact ⟨-a, by simp only [Pi.neg_apply, NegMemClass.coe_neg, map_neg, neg_smul, Finset.sum_neg_distrib]⟩
  · rintro ⟨a, rfl⟩
    refine AddSubgroup.sum_mem _ fun m _ => AddSubgroup.subset_closure ?_
    refine ⟨_, GlobalTheory.VacAny.at_atPlace _, ?_, ex m.1, ?_, fy m.2, ?_, rfl⟩
    · rw [GlobalTheory.EmbChart.evFin_atPlace]; exact (a m).2
    · have : ex m.1 ∈ Submodule.span ℤ (Set.range ex) := Submodule.subset_span ⟨m.1, rfl⟩
      rw [hex] at this; exact this
    · have : fy m.2 ∈ Submodule.span ℤ (Set.range fy) := Submodule.subset_span ⟨m.2, rfl⟩
      rw [hfy] at this; exact this

end GlobalTheory.LatIntegral

namespace GlobalTheory.LatIntegral

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
The claim follows from `map_sum ((inclR (F := F) (E := E) (AF F)).toAddMonoidHom.mapMatrix) f _`.
-/
theorem incM_sum {n d : ℕ} {M : Type} [Fintype M] (f : M → Matrix (Fin n) (Fin d) E) :
    incM F (∑ m, f m) = ∑ m, incM F (f m) :=
  map_sum ((inclR (F := F) (E := E) (AF F)).toAddMonoidHom.mapMatrix) f _

end GlobalTheory.LatIntegral

namespace GlobalTheory.LatIntegral

/- English proof (translation)
Introduce `F E _ _ _ _ _ n d L L' hL hL'`. Use `set S := Submodule.span F {z : Matrix (Fin n) (Fin d) E | ∃ x ∈ L, ∃ y ∈ L', z = Matrix.vecMulVec x y} with hS`. Establish `hden : ∀ c : E, ∃ (t : F) (o : 𝓞 E), c = algebraMap F E t * (o : E)`. Introduce `c`. Take `⟨y, hy0, hy⟩` from `exists_integral_multiples ℤ ℚ (L := E) {c}`.

Establish `hyc` using `hy c (Finset.mem_singleton_self c)`. Use `⟨((y : F))⁻¹, ⟨(y : E) * c, (mem_integralClosure_iff ℤ E).2 (by simpa [zsmul_eq_mul] using hyc)⟩, ?_⟩` and prove the remaining obligations. Use `show c = _ * ((y : E) * c)`. Rewrite using `[map_inv₀, map_intCast, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hy0 : (y : E) ≠ 0), one_mul]`. Establish `hsm : ∀ (c : E) (V : Matrix (Fin n) (Fin d) E), (∀ o : 𝓞 E, (o : E) • V ∈ S) → c • V ∈ S`.

Introduce `c V hV`. Take `⟨t, o, rfl⟩` from `hden c`. Rewrite using `[mul_smul, algebraMap_smul]`. Conclude with `S.smul_mem t (hV o)`. Set `Q : Submodule E (Fin d → E)` to `{ carrier := {w | ∀ x ∈ L, Matrix.vecMulVec x w ∈ S} add_mem' := fun {a b} ha hb x hx => by rw [Matrix.vecMulVec_add]; exact S.add_mem (ha x hx) (hb x hx) zero_mem' := fun x _ => by`.

Use `S.zero_mem` and compare the differences between its conclusion and the goal. Use `ext`. Simplify using `[Matrix.vecMulVec_apply]`. Use the proof step `smul_mem' := fun c w hw x hx => by`. Rewrite using `[Matrix.vecMulVec_smul]`.

Use `hsm c _ fun o => ?_` and prove the remaining obligations. Rewrite using `[← Matrix.smul_vecMulVec]`. Conclude with `hw _ (by simpa [algebraMap_smul] using L.smul_mem o hx) }`. Establish `hQ : Q = ⊤`. Rewrite using `[eq_top_iff, ← hL'.span_eq_top, Submodule.span_le]`.

Introduce `w hw x hx`. Conclude with `Submodule.subset_span ⟨x, hx, w, hw, rfl⟩`. Set `R : Submodule E (Fin n → E)` to `{ carrier := {x | ∀ w, Matrix.vecMulVec x w ∈ S} add_mem' := fun {a b} ha hb w => by rw [Matrix.add_vecMulVec]; exact S.add_mem (ha w) (hb w) zero_mem' := fun w => by`. Use `S.zero_mem` and compare the differences between its conclusion and the goal. Use `ext`.

Simplify using `[Matrix.vecMulVec_apply]`. Use the proof step `smul_mem' := fun c x hx w => by`. Rewrite using `[Matrix.smul_vecMulVec, ← Matrix.vecMulVec_smul]`. Conclude with `hx _ }`. Establish `hR : R = ⊤`.

Rewrite using `[eq_top_iff, ← hL.span_eq_top, Submodule.span_le]`. Introduce `x hx w`. Establish `: w ∈ Q` using `by rw [hQ]; trivial`. Conclude with `this x hx`. Rewrite using `[eq_top_iff]`.

Introduce `z _`. Establish `hz : z = ∑ i, Matrix.vecMulVec (Pi.single i 1) (z i)`. Use extensionality with `a b`. Simplify using `[Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.single_apply]`. Rewrite using `[hz]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `: (Pi.single i 1 : Fin n → E) ∈ R` using `by rw [hR]; trivial`. Conclude with `this _`.
-/
theorem span_vecMulVec_eq_top : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (L' : Submodule (𝓞 E) (Fin d → E)), L.IsLattice E → L'.IsLattice E →
    Submodule.span F {z : Matrix (Fin n) (Fin d) E | ∃ x ∈ L, ∃ y ∈ L', z = Matrix.vecMulVec x y} = ⊤ := by
  intro F E _ _ _ _ _ n d L L' hL hL'
  set S := Submodule.span F {z : Matrix (Fin n) (Fin d) E | ∃ x ∈ L, ∃ y ∈ L', z = Matrix.vecMulVec x y} with hS

  have hden : ∀ c : E, ∃ (t : F) (o : 𝓞 E), c = algebraMap F E t * (o : E) := by
    intro c
    obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {c}
    have hyc := hy c (Finset.mem_singleton_self c)
    refine ⟨((y : F))⁻¹, ⟨(y : E) * c, (mem_integralClosure_iff ℤ E).2 (by simpa [zsmul_eq_mul] using hyc)⟩, ?_⟩
    show c = _ * ((y : E) * c)
    rw [map_inv₀, map_intCast, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hy0 : (y : E) ≠ 0), one_mul]
  have hsm : ∀ (c : E) (V : Matrix (Fin n) (Fin d) E), (∀ o : 𝓞 E, (o : E) • V ∈ S) → c • V ∈ S := by
    intro c V hV
    obtain ⟨t, o, rfl⟩ := hden c
    rw [mul_smul, algebraMap_smul]
    exact S.smul_mem t (hV o)
  let Q : Submodule E (Fin d → E) :=
    { carrier := {w | ∀ x ∈ L, Matrix.vecMulVec x w ∈ S}
      add_mem' := fun {a b} ha hb x hx => by rw [Matrix.vecMulVec_add]; exact S.add_mem (ha x hx) (hb x hx)
      zero_mem' := fun x _ => by
        convert S.zero_mem
        ext; simp [Matrix.vecMulVec_apply]
      smul_mem' := fun c w hw x hx => by
        rw [Matrix.vecMulVec_smul]
        refine hsm c _ fun o => ?_
        rw [← Matrix.smul_vecMulVec]
        exact hw _ (by simpa [algebraMap_smul] using L.smul_mem o hx) }
  have hQ : Q = ⊤ := by
    rw [eq_top_iff, ← hL'.span_eq_top, Submodule.span_le]
    intro w hw x hx
    exact Submodule.subset_span ⟨x, hx, w, hw, rfl⟩
  let R : Submodule E (Fin n → E) :=
    { carrier := {x | ∀ w, Matrix.vecMulVec x w ∈ S}
      add_mem' := fun {a b} ha hb w => by rw [Matrix.add_vecMulVec]; exact S.add_mem (ha w) (hb w)
      zero_mem' := fun w => by
        convert S.zero_mem
        ext; simp [Matrix.vecMulVec_apply]
      smul_mem' := fun c x hx w => by
        rw [Matrix.smul_vecMulVec, ← Matrix.vecMulVec_smul]
        exact hx _ }
  have hR : R = ⊤ := by
    rw [eq_top_iff, ← hL.span_eq_top, Submodule.span_le]
    intro x hx w
    have : w ∈ Q := by rw [hQ]; trivial
    exact this x hx
  rw [eq_top_iff]
  intro z _
  have hz : z = ∑ i, Matrix.vecMulVec (Pi.single i 1) (z i) := by
    ext a b
    simp [Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.single_apply]
  rw [hz]
  refine Submodule.sum_mem _ fun i _ => ?_
  have : (Pi.single i 1 : Fin n → E) ∈ R := by rw [hR]; trivial
  exact this _

end GlobalTheory.LatIntegral

namespace GlobalTheory.LatIntegral

/- English proof (translation)
Use `set N := Submodule.span (AF F) (Set.range (incM F : Matrix (Fin n) (Fin d) E → Matrix (Fin n) (Fin d) (AE F E)))`. Rewrite using `[Matrix.matrix_eq_sum_single w]`. Use `Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Proceed by induction on `w i j using TensorProduct.induction_on with`. Consider the case `zero => rw [Matrix.single_zero]`.

Conclude with `N.zero_mem`. Consider the case `add x y hx hy => rw [Matrix.single_add]`. Conclude with `N.add_mem hx hy`. Consider the case `tmul a e`. Establish `h1 : a ⊗ₜ[F] e = a • ((1 : AF F) ⊗ₜ[F] e)` using `by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]`.

Establish `h2 : Matrix.single i j ((1 : AF F) ⊗ₜ[F] e) = incM F (Matrix.single i j e)`. Use extensionality with `a b`. Simplify using `only [incM, Matrix.map_apply, Matrix.single_apply, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[h1, ← Matrix.smul_single, h2]`.

Conclude with `N.smul_mem a (Submodule.subset_span ⟨_, rfl⟩)`.
-/
theorem mem_span_incM {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (w : Matrix (Fin n) (Fin d) (AE F E)) :
    w ∈ Submodule.span (AF F) (Set.range (incM F : Matrix (Fin n) (Fin d) E → Matrix (Fin n) (Fin d) (AE F E))) := by
  classical
  set N := Submodule.span (AF F) (Set.range (incM F : Matrix (Fin n) (Fin d) E → Matrix (Fin n) (Fin d) (AE F E)))
  rw [Matrix.matrix_eq_sum_single w]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  induction w i j using TensorProduct.induction_on with
  | zero => rw [Matrix.single_zero]; exact N.zero_mem
  | add x y hx hy => rw [Matrix.single_add]; exact N.add_mem hx hy
  | tmul a e =>
    have h1 : a ⊗ₜ[F] e = a • ((1 : AF F) ⊗ₜ[F] e) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h2 : Matrix.single i j ((1 : AF F) ⊗ₜ[F] e) = incM F (Matrix.single i j e) := by
      ext a b
      simp only [incM, Matrix.map_apply, Matrix.single_apply, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.includeRight_apply]
      split_ifs <;> simp
    rw [h1, ← Matrix.smul_single, h2]
    exact N.smul_mem a (Submodule.subset_span ⟨_, rfl⟩)

/- English proof (translation)
Introduce `F E _ _ _ _ _ n d B κ _ co hrat y z`. Establish `hinj : Function.Injective (algebraMap F (AF F))` using `AdeleRing.algebraMap_injective (𝓞 F) F`. Use `choose ry rz hr using hrat`. Establish `hadd : ∀ x x' : Matrix (Fin n) (Fin d) E, ry (x + x') = ry x + ry x' ∧ rz (x + x') = rz x + rz x'`. Introduce `x x'`.

Establish `h` using `congrArg co.e (show incM F (x + x') = incM F x + incM F x' from Matrix.map_add _ (map_add _) _ _)`. Rewrite `h` using `[map_add, hr, hr, hr]`. Use `⟨funext fun i => hinj ?_, funext fun i => hinj ?_⟩` and prove the remaining obligations. Use `congrArg (fun p => p.1 i) h` as an intermediate fact. Simplify using `using this`.

Use `congrArg (fun p => p.2 i) h` as an intermediate fact. Simplify using `using this`. Establish `hsmul : ∀ (c : F) (x : Matrix (Fin n) (Fin d) E), ry (c • x) = c • ry x ∧ rz (c • x) = c • rz x`. Introduce `c x`. Establish `h` using `congrArg co.e (incM_smul c x)`.

Rewrite `h` using `[map_smul, hr, hr]`. Use `⟨funext fun i => hinj ?_, funext fun i => hinj ?_⟩` and prove the remaining obligations. Use `congrArg (fun p => p.1 i) h` as an intermediate fact. Simplify `this` using `[Algebra.smul_def]`. Use `congrArg (fun p => p.2 i) h` as an intermediate fact.

Simplify `this` using `[Algebra.smul_def]`. Set `ρ : Matrix (Fin n) (Fin d) E →ₗ[F] (κ → F) × (κ → F)` to `{ toFun := fun x => (ry x, rz x) map_add' := fun x x' => by rw [(hadd x x').1, (hadd x x').2]; rfl map_smul' := fun c x => by rw [(hsmul c x).1, (hsmul c x).2]; rfl }`. It suffices to establish `hyz : (y, z) ∈ LinearMap.range ρ by`. Take `⟨x, hx⟩` from `hyz`. Use `⟨x, ?_⟩` and prove the remaining obligations.

Rewrite using `[hr x]`. Establish `h1 : ry x = y` using `congrArg Prod.fst hx`. Establish `h2 : rz x = z` using `congrArg Prod.snd hx`. Rewrite using `[h1, h2]`. Assume the negation of the conclusion as `hyz`.

Take `⟨f, hf, hmap⟩` from `Submodule.exists_dual_map_eq_bot_of_notMem hyz inferInstance`. Establish `hf0 : ∀ x, f (ρ x) = 0` using `fun x => by`. Establish `: f (ρ x) ∈ (LinearMap.range ρ).map f` using `Submodule.mem_map_of_mem ⟨x, rfl⟩`. Rewrite `this` using `[hmap, Submodule.mem_bot]`. Then use the resulting hypothesis. Use `set α : κ → F := fun i => f ((fun j => if i = j then 1 else 0), 0)`.

Use `set β : κ → F := fun i => f (0, fun j => if i = j then 1 else 0)`. Establish `hfp : ∀ p : (κ → F) × (κ → F), f p = ∑ i, p.1 i * α i + ∑ i, p.2 i * β i`. Introduce `p`. Apply the tactic sequence `have hp : p = LinearMap.inl F _ _ p.1 + LinearMap.inr F _ _ p.2 := by ext <;> simp`. Rewrite using `[hp, map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.pi_apply_eq_sum_univ (f ∘ₗ _) p.1, LinearMap.pi_apply_eq_sum_univ (f ∘ₗ LinearMap.inr F _ _) p.2]`.

Simplify using `[α, β, smul_eq_mul]`. Set `φA : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] AF F` to `{ toFun := fun q => ∑ i, q.1 i * algebraMap F (AF F) (α i) + ∑ i, q.2 i * algebraMap F (AF F) (β i) map_add' := fun q q' => by`. Simplify using `only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree. Use the proof step `map_smul' := fun c q => by`.

Simplify using `only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, RingHom.id_apply, mul_add] }`. Establish `hφ : ∀ u v : κ → F, φA (fun i => algebraMap F (AF F) (u i), fun i => algebraMap F (AF F) (v i)) = algebraMap F (AF F) (f (u, v))`. Introduce `u v`. Rewrite using `[hfp]`. Simplify using `[φA, map_add, map_sum, map_mul]`.

Set `Φ : Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] AF F` to `φA ∘ₗ co.e.toLinearMap`. Establish `hΦ : Φ = 0`. Establish `hle : Submodule.span (AF F) (Set.range (incM F : Matrix (Fin n) (Fin d) E → Matrix (Fin n) (Fin d) (AE F E))) ≤ LinearMap.ker Φ`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`.

Use `show φA (co.e (incM F x)) = 0`. Rewrite using `[hr, hφ]`. Use `hf0 x` as an intermediate fact. Simplify using `only [ρ, LinearMap.coe_mk, AddHom.coe_mk] at this`. Rewrite using `[this, map_zero]`.

Use extensionality with `w`. Conclude with `hle (mem_span_incM w)`. Apply `hf` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises. Rewrite using `[← hφ, map_zero]`.

Use `congrArg (fun L => L (co.e.symm (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)))) hΦ` as an intermediate fact. Simplify `this` using `[Φ]`.
-/
theorem darboux_rat_surj : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    {B : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n) (Fin d) (AE F E) → AF F} {κ : Type} [Fintype κ]
    (co : Darboux B κ), (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : κ → F,
      co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∀ y z : κ → F, ∃ x : Matrix (Fin n) (Fin d) E,
      co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
  intro F E _ _ _ _ _ n d B κ _ co hrat y z
  classical
  have hinj : Function.Injective (algebraMap F (AF F)) := AdeleRing.algebraMap_injective (𝓞 F) F
  choose ry rz hr using hrat
  have hadd : ∀ x x' : Matrix (Fin n) (Fin d) E, ry (x + x') = ry x + ry x' ∧ rz (x + x') = rz x + rz x' := by
    intro x x'
    have h := congrArg co.e (show incM F (x + x') = incM F x + incM F x' from Matrix.map_add _ (map_add _) _ _)
    rw [map_add, hr, hr, hr] at h
    refine ⟨funext fun i => hinj ?_, funext fun i => hinj ?_⟩
    · have := congrArg (fun p => p.1 i) h; simpa using this
    · have := congrArg (fun p => p.2 i) h; simpa using this
  have hsmul : ∀ (c : F) (x : Matrix (Fin n) (Fin d) E), ry (c • x) = c • ry x ∧ rz (c • x) = c • rz x := by
    intro c x
    have h := congrArg co.e (incM_smul c x)
    rw [map_smul, hr, hr] at h
    refine ⟨funext fun i => hinj ?_, funext fun i => hinj ?_⟩
    · have := congrArg (fun p => p.1 i) h; simpa [Algebra.smul_def] using this
    · have := congrArg (fun p => p.2 i) h; simpa [Algebra.smul_def] using this
  let ρ : Matrix (Fin n) (Fin d) E →ₗ[F] (κ → F) × (κ → F) :=
    { toFun := fun x => (ry x, rz x)
      map_add' := fun x x' => by rw [(hadd x x').1, (hadd x x').2]; rfl
      map_smul' := fun c x => by rw [(hsmul c x).1, (hsmul c x).2]; rfl }
  suffices hyz : (y, z) ∈ LinearMap.range ρ by
    obtain ⟨x, hx⟩ := hyz
    refine ⟨x, ?_⟩
    rw [hr x]
    have h1 : ry x = y := congrArg Prod.fst hx
    have h2 : rz x = z := congrArg Prod.snd hx
    rw [h1, h2]
  by_contra hyz
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hyz inferInstance
  have hf0 : ∀ x, f (ρ x) = 0 := fun x => by
    have : f (ρ x) ∈ (LinearMap.range ρ).map f := Submodule.mem_map_of_mem ⟨x, rfl⟩
    rwa [hmap, Submodule.mem_bot] at this
  set α : κ → F := fun i => f ((fun j => if i = j then 1 else 0), 0)
  set β : κ → F := fun i => f (0, fun j => if i = j then 1 else 0)
  have hfp : ∀ p : (κ → F) × (κ → F), f p = ∑ i, p.1 i * α i + ∑ i, p.2 i * β i := by
    intro p
    have hp : p = LinearMap.inl F _ _ p.1 + LinearMap.inr F _ _ p.2 := by ext <;> simp
    rw [hp, map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.pi_apply_eq_sum_univ (f ∘ₗ _) p.1,
      LinearMap.pi_apply_eq_sum_univ (f ∘ₗ LinearMap.inr F _ _) p.2]
    simp [α, β, smul_eq_mul]
  let φA : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] AF F :=
    { toFun := fun q => ∑ i, q.1 i * algebraMap F (AF F) (α i) + ∑ i, q.2 i * algebraMap F (AF F) (β i)
      map_add' := fun q q' => by
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]; ring
      map_smul' := fun c q => by
        simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum,
          RingHom.id_apply, mul_add] }
  have hφ : ∀ u v : κ → F, φA (fun i => algebraMap F (AF F) (u i), fun i => algebraMap F (AF F) (v i)) =
      algebraMap F (AF F) (f (u, v)) := by
    intro u v
    rw [hfp]
    simp [φA, map_add, map_sum, map_mul]
  let Φ : Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] AF F := φA ∘ₗ co.e.toLinearMap
  have hΦ : Φ = 0 := by
    have hle : Submodule.span (AF F) (Set.range (incM F : Matrix (Fin n) (Fin d) E → Matrix (Fin n) (Fin d) (AE F E)))
        ≤ LinearMap.ker Φ := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      show φA (co.e (incM F x)) = 0
      rw [hr, hφ]
      have := hf0 x
      simp only [ρ, LinearMap.coe_mk, AddHom.coe_mk] at this
      rw [this, map_zero]
    ext w
    exact hle (mem_span_incM w)
  apply hf
  apply hinj
  rw [← hφ, map_zero]
  have := congrArg (fun L => L (co.e.symm (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)))) hΦ
  simpa [Φ] using this

end GlobalTheory.LatIntegral

namespace GlobalTheory.LatIntegral

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP`. Establish `hX` using `hP.herm.lat`. Establish `hW` using `hP.skew.lat`. Take `⟨kx, ex, hex⟩` from `Submodule.fg_iff_exists_fin_generating_family.1 (hX.fg.restrictScalars (R := ℤ))`. Take `⟨ky, fy, hfy⟩` from `Submodule.fg_iff_exists_fin_generating_family.1 (hW.fg.restrictScalars (R := ℤ))`.

Take `⟨g, hg⟩ : ∃ g : Fin kx × Fin ky → Matrix (Fin n) (Fin d) E, g = fun m => Matrix.vecMulVec (ex m.1) (fy m.2)` from `⟨_, rfl⟩`. Establish `hpar : ∀ v γ, γ ∈ latAtV X W v ↔ ∃ a : Fin kx × Fin ky → v.adicCompletionIntegers F, γ = ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • incM F (g m)`. Introduce `v γ`. Substitute `hg` using the available equality. Conclude with `param X W v ex fy hex hfy γ`.

Use `choose ry rz hr using hP.good.rat`. Establish `hspan : ∀ x : Matrix (Fin n) (Fin d) E, x ∈ Submodule.span F (Set.range g)`. Introduce `x`. Establish `h1 : x ∈ Submodule.span F {z : Matrix (Fin n) (Fin d) E | ∃ a ∈ X.L, ∃ b ∈ W.L, z = Matrix.vecMulVec a b}`. Rewrite using `[span_vecMulVec_eq_top X.L W.L hX hW]`.

Discharge the goal by the elementary cases of `trivial`. Use `Submodule.span_le.2 ?_ h1` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, b, hb, rfl⟩`. Establish `ha' : a ∈ Submodule.span ℤ (Set.range ex)` using `by rw [hex]; exact ha`. Establish `hb' : b ∈ Submodule.span ℤ (Set.range fy)` using `by rw [hfy]; exact hb`.

Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).1 ha'`. Take `⟨c', rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).1 hb'`. Rewrite using `[GlobalTheory.LatParam.vecMulVec_sum_zsmul]`. Use `Submodule.sum_mem _ fun m _ => ?_` and prove the remaining obligations. Establish `hm : Matrix.vecMulVec (ex m.1) (fy m.2) ∈ Submodule.span F (Set.range g)` using `Submodule.subset_span ⟨m, by rw [hg]⟩`.

Conclude with `Submodule.smul_of_tower_mem _ _ hm`. Establish `hcoef : ∀ (t : Bool) (j : Fin n × Fin d), ∃ c : Fin kx × Fin ky → F, ∀ i, ∑ m, c m * ry (g m) i = (if t then (if i = j then 1 else 0) else 0) ∧ ∑ m, c m * rz (g m) i = (if t then 0 else (if i = j then 1 else 0))`. Introduce `t j`. Take `⟨x, hx⟩` from `darboux_rat_surj M.co hP.good.rat (fun i => if t then (if i = j then 1 else 0) else 0) (fun i => if t then 0 else (if i = j then 1 else 0))`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun F).1 (hspan x)`.

Use `⟨c, fun i => ?_⟩` and prove the remaining obligations. Establish `key : M.co.e (incM F x) = ∑ m, algebraMap F (AF F) (c m) • M.co.e (incM F (g m))`. Rewrite using `[← hc, incM_sum, map_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[incM_smul, map_smul]`.

Rewrite `key` using `[hx]`. Establish `k1` using `congrArg (fun p => p.1 i) key`. Establish `k2` using `congrArg (fun p => p.2 i) key`. Simplify using `only [hr, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, ← map_mul, ← map_sum] at k1 k2`. Establish `hinj : Function.Injective (algebraMap F (AF F))` using `AdeleRing.algebraMap_injective (𝓞 F) F`.

Conclude with `⟨(hinj k1).symm, (hinj k2).symm⟩`. Use `choose C hC using hcoef`. Establish `hfin : ∀ᶠ v in Filter.cofinite, ∀ m, (∀ i, algebraMap F (Fv F v) (ry (g m) i) ∈ v.adicCompletionIntegers F ∧ algebraMap F (Fv F v) (rz (g m) i) ∈ v.adicCompletionIntegers F) ∧ ∀ t j, algebraMap F (Fv F v) (C t j m) ∈ v.adicCompletionIntegers F`. Use `Filter.eventually_all.2 fun m => Filter.Eventually.and (Filter.eventually_all.2 fun i => (eventually_algebraMap_mem_integers _).and (eventually_algebraMap_mem_integers _)) (Filter.eventually_all.2 fun t => Filter.eventually_all.2 fun j => eventually_algebraMap_mem_integers _)` and prove the remaining obligations. Use `filter_upwards [hfin] with v hv`.

Introduce `l`. Rewrite using `[AddSubgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨γ, hγ, rfl⟩ i`. Take `⟨a, rfl⟩` from `(hpar v γ).1 hγ`.

Take `⟨h1, h2⟩` from `locCo_sum M.co v (fun m => (a m : Fv F v)) g (fun m => ry (g m)) (fun m => rz (g m)) (fun m => hr (g m)) i`. Rewrite using `[h1, h2]`. Conclude with `⟨sum_mem fun m _ => mul_mem (a m).2 ((hv m).1 i).1, sum_mem fun m _ => mul_mem (a m).2 ((hv m).1 i).2⟩`. Introduce `hl set a : Fin kx × Fin ky → Fv F v := fun m => ∑ j, (l.1 j * algebraMap F (Fv F v) (C true j m) + l.2 j * algebraMap F (Fv F v) (C false j m)) with ha`. Establish `haO : ∀ m, a m ∈ v.adicCompletionIntegers F` using `fun m => sum_mem fun j _ => add_mem (mul_mem (hl j).1 ((hv m).2 true j)) (mul_mem (hl j).2 ((hv m).2 false j))`.

Use `⟨∑ m, GlobalTheory.EmbChart.atPlace v (a m) • incM F (g m), (hpar v _).2 ⟨fun m => ⟨a m, haO m⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hA : ∀ (t : Bool) (j i : Fin n × Fin d), ∑ m, algebraMap F (Fv F v) (C t j m) * algebraMap F (Fv F v) (ry (g m) i) = algebraMap F (Fv F v) (if t then (if i = j then 1 else 0) else 0)`. Introduce `t j i`. Rewrite using `[← (hC t j i).1, map_sum]`. Simplify using `only [map_mul]`.

Establish `hB : ∀ (t : Bool) (j i : Fin n × Fin d), ∑ m, algebraMap F (Fv F v) (C t j m) * algebraMap F (Fv F v) (rz (g m) i) = algebraMap F (Fv F v) (if t then 0 else (if i = j then 1 else 0))`. Introduce `t j i`. Rewrite using `[← (hC t j i).2, map_sum]`. Simplify using `only [map_mul]`. Use `Prod.ext (funext fun i => ?_) (funext fun i => ?_)` and prove the remaining obligations.

Rewrite using `[(locCo_sum M.co v a g (fun m => ry (g m)) (fun m => rz (g m)) (fun m => hr (g m)) i).1, ha, combo l.1 l.2 _ _ _ _ _ (fun j => hA true j i) (fun j => hA false j i)]`. Simplify using the standard rewrite rules. Rewrite using `[(locCo_sum M.co v a g (fun m => ry (g m)) (fun m => rz (g m)) (fun m => hr (g m)) i).2, ha, combo l.1 l.2 _ _ _ _ _ (fun j => hB true j i) (fun j => hB false j i)]`. Simplify using the standard rewrite rules.
-/
theorem locCo_latAtV_eventually : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ᶠ v in Filter.cofinite, ∀ l, l ∈ (latAtV X W v).map (GlobalTheory.LatVac.locCo M.co v) ↔
      ∀ i, l.1 i ∈ v.adicCompletionIntegers F ∧ l.2 i ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  classical
  have hX := hP.herm.lat
  have hW := hP.skew.lat
  obtain ⟨kx, ex, hex⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (hX.fg.restrictScalars (R := ℤ))
  obtain ⟨ky, fy, hfy⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (hW.fg.restrictScalars (R := ℤ))
  obtain ⟨g, hg⟩ : ∃ g : Fin kx × Fin ky → Matrix (Fin n) (Fin d) E, g = fun m => Matrix.vecMulVec (ex m.1) (fy m.2) :=
    ⟨_, rfl⟩
  have hpar : ∀ v γ, γ ∈ latAtV X W v ↔ ∃ a : Fin kx × Fin ky → v.adicCompletionIntegers F,
      γ = ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • incM F (g m) := by
    intro v γ; subst hg; exact param X W v ex fy hex hfy γ
  choose ry rz hr using hP.good.rat
  have hspan : ∀ x : Matrix (Fin n) (Fin d) E, x ∈ Submodule.span F (Set.range g) := by
    intro x
    have h1 : x ∈ Submodule.span F {z : Matrix (Fin n) (Fin d) E | ∃ a ∈ X.L, ∃ b ∈ W.L, z = Matrix.vecMulVec a b} := by
      rw [span_vecMulVec_eq_top X.L W.L hX hW]; trivial
    refine Submodule.span_le.2 ?_ h1
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have ha' : a ∈ Submodule.span ℤ (Set.range ex) := by rw [hex]; exact ha
    have hb' : b ∈ Submodule.span ℤ (Set.range fy) := by rw [hfy]; exact hb
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 ha'
    obtain ⟨c', rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hb'
    rw [GlobalTheory.LatParam.vecMulVec_sum_zsmul]
    refine Submodule.sum_mem _ fun m _ => ?_
    have hm : Matrix.vecMulVec (ex m.1) (fy m.2) ∈ Submodule.span F (Set.range g) :=
      Submodule.subset_span ⟨m, by rw [hg]⟩
    exact Submodule.smul_of_tower_mem _ _ hm
  have hcoef : ∀ (t : Bool) (j : Fin n × Fin d), ∃ c : Fin kx × Fin ky → F, ∀ i,
      ∑ m, c m * ry (g m) i = (if t then (if i = j then 1 else 0) else 0) ∧
        ∑ m, c m * rz (g m) i = (if t then 0 else (if i = j then 1 else 0)) := by
    intro t j
    obtain ⟨x, hx⟩ := darboux_rat_surj M.co hP.good.rat (fun i => if t then (if i = j then 1 else 0) else 0)
      (fun i => if t then 0 else (if i = j then 1 else 0))
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 (hspan x)
    refine ⟨c, fun i => ?_⟩
    have key : M.co.e (incM F x) = ∑ m, algebraMap F (AF F) (c m) • M.co.e (incM F (g m)) := by
      rw [← hc, incM_sum, map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [incM_smul, map_smul]
    rw [hx] at key
    have k1 := congrArg (fun p => p.1 i) key
    have k2 := congrArg (fun p => p.2 i) key
    simp only [hr, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
      smul_eq_mul, ← map_mul, ← map_sum] at k1 k2
    have hinj : Function.Injective (algebraMap F (AF F)) := AdeleRing.algebraMap_injective (𝓞 F) F
    exact ⟨(hinj k1).symm, (hinj k2).symm⟩
  choose C hC using hcoef
  have hfin : ∀ᶠ v in Filter.cofinite, ∀ m, (∀ i, algebraMap F (Fv F v) (ry (g m) i) ∈ v.adicCompletionIntegers F ∧
      algebraMap F (Fv F v) (rz (g m) i) ∈ v.adicCompletionIntegers F) ∧
      ∀ t j, algebraMap F (Fv F v) (C t j m) ∈ v.adicCompletionIntegers F := by
    refine Filter.eventually_all.2 fun m => Filter.Eventually.and (Filter.eventually_all.2 fun i =>
      (eventually_algebraMap_mem_integers _).and (eventually_algebraMap_mem_integers _))
      (Filter.eventually_all.2 fun t => Filter.eventually_all.2 fun j => eventually_algebraMap_mem_integers _)
  filter_upwards [hfin] with v hv
  intro l
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨γ, hγ, rfl⟩ i
    obtain ⟨a, rfl⟩ := (hpar v γ).1 hγ
    obtain ⟨h1, h2⟩ := locCo_sum M.co v (fun m => (a m : Fv F v)) g (fun m => ry (g m)) (fun m => rz (g m))
      (fun m => hr (g m)) i
    rw [h1, h2]
    exact ⟨sum_mem fun m _ => mul_mem (a m).2 ((hv m).1 i).1, sum_mem fun m _ => mul_mem (a m).2 ((hv m).1 i).2⟩
  · intro hl
    set a : Fin kx × Fin ky → Fv F v := fun m =>
      ∑ j, (l.1 j * algebraMap F (Fv F v) (C true j m) + l.2 j * algebraMap F (Fv F v) (C false j m)) with ha
    have haO : ∀ m, a m ∈ v.adicCompletionIntegers F := fun m =>
      sum_mem fun j _ => add_mem (mul_mem (hl j).1 ((hv m).2 true j)) (mul_mem (hl j).2 ((hv m).2 false j))
    refine ⟨∑ m, GlobalTheory.EmbChart.atPlace v (a m) • incM F (g m), (hpar v _).2 ⟨fun m => ⟨a m, haO m⟩, rfl⟩, ?_⟩
    have hA : ∀ (t : Bool) (j i : Fin n × Fin d), ∑ m, algebraMap F (Fv F v) (C t j m) * algebraMap F (Fv F v) (ry (g m) i) =
        algebraMap F (Fv F v) (if t then (if i = j then 1 else 0) else 0) := by
      intro t j i; rw [← (hC t j i).1, map_sum]; simp only [map_mul]
    have hB : ∀ (t : Bool) (j i : Fin n × Fin d), ∑ m, algebraMap F (Fv F v) (C t j m) * algebraMap F (Fv F v) (rz (g m) i) =
        algebraMap F (Fv F v) (if t then 0 else (if i = j then 1 else 0)) := by
      intro t j i; rw [← (hC t j i).2, map_sum]; simp only [map_mul]
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · rw [(locCo_sum M.co v a g (fun m => ry (g m)) (fun m => rz (g m)) (fun m => hr (g m)) i).1, ha,
        combo l.1 l.2 _ _ _ _ _ (fun j => hA true j i) (fun j => hA false j i)]
      simp
    · rw [(locCo_sum M.co v a g (fun m => ry (g m)) (fun m => rz (g m)) (fun m => hr (g m)) i).2, ha,
        combo l.1 l.2 _ _ _ _ _ (fun j => hB true j i) (fun j => hB false j i)]
      simp

end GlobalTheory.LatIntegral
