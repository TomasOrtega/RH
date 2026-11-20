import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabilizerInertPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactFixesVacuumNonsplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.XmApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameAdelicLatticeAtFinitePlaceOfInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceUnramifiedSkewSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHomFrameConjugationAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeStabilizerOfFrameConjIntegral
import Formalism.LocalToGlobal.IndefiniteReal.LocalNormSurjectivity.MemMaxVAIff
import Formalism.LocalToGlobal.IndefiniteReal.LocalNormSurjectivity.WittFN
import Formalism.LocalToGlobal.IndefiniteReal.LocalNormSurjectivity.WittHS
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.InertLineTrans

section Local

open Formalism.UG Formalism.IndefR.LocBrg

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

/- English proof (translation)
Take `⟨g0, rfl⟩` from `hg`. Conclude with `((g0 : Matrix (Fin n) (Fin n) (intL L)) i j).2`.
-/
theorem entries_of_GLint {g : GL (Fin n) L} (hg : g ∈ GLint (Fin n) (intL L)) (i j : Fin n) :
    (g : Matrix (Fin n) (Fin n) L) i j ∈ intL L := by
  obtain ⟨g0, rfl⟩ := hg
  exact ((g0 : Matrix (Fin n) (Fin n) (intL L)) i j).2

/- English proof (translation)
Express the relevant statement in the definitionally equal form `∑ j, M i j * y j ∈ intL L`. Conclude with `Subring.sum_mem _ fun j _ => mul_mem (hM i j) (hy j)`.
-/
theorem mulVec_int {M : Matrix (Fin n) (Fin n) L} (hM : ∀ i j, M i j ∈ intL L) {y : Fin n → L}
    (hy : ∀ i, y i ∈ intL L) (i : Fin n) : (M *ᵥ y) i ∈ intL L := by
  change ∑ j, M i j * y j ∈ intL L
  exact Subring.sum_mem _ fun j _ => mul_mem (hM i j) (hy j)

def intCols (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) : Submodule (intL L) (Fin n → L) where
  carrier := {y | ∀ i, y i ∈ intL L}
  zero_mem' := fun _ => zero_mem _
  add_mem' := fun ha hb i => add_mem (ha i) (hb i)
  smul_mem' := fun c _ hy i => mul_mem c.2 (hy i)

/- English proof (translation)
Introduce `i` and use `by by_cases h : i = j · subst h; rw [Pi.single_eq_same]; exact one_mem _ · rw [Pi.single_eq_of_ne h]; exact zero_mem _`.
-/
theorem single_mem (j : Fin n) : (Pi.single j 1 : Fin n → L) ∈ intCols L n := fun i => by
  by_cases h : i = j
  · subst h; rw [Pi.single_eq_same]; exact one_mem _
  · rw [Pi.single_eq_of_ne h]; exact zero_mem _

/- English proof (translation)
Use `(hk _).1 (single_mem j) i` as an intermediate fact. Simplify using `using this`.
-/
theorem entries_of_stab {k : GL (Fin n) L} (hk : k ∈ stabGL (intCols L n)) (i j : Fin n) :
    (k : Matrix (Fin n) (Fin n) L) i j ∈ intL L := by
  have := (hk _).1 (single_mem j) i
  simpa using this

/- English proof (translation)
Establish `hσ : ∀ x ∈ intL L, σ x ∈ intL L` using `fun x hx => by rw [mem_intL, hU.2.1]; exact mem_intL.1 hx`. Take `⟨x, hx, hx1⟩` from `hU.2.2.2.2.1`. Establish `hx0 : σ x - x ≠ 0`. Introduce `h`. Rewrite `hx1` using `[h, map_zero]`.

Conclude with `zero_ne_one hx1`. Establish `hτ : σ x * (σ x - x)⁻¹ ∈ intL L` using `mul_mem (hσ x hx) (by rw [mem_intL, map_inv₀, hx1, inv_one])`. Establish `hτ1 : σ x * (σ x - x)⁻¹ + σ (σ x * (σ x - x)⁻¹) = 1`. Rewrite using `[map_mul, map_inv₀, map_sub, hU.1, ← neg_sub (σ x) x, inv_neg]`. Take the linear combination `mul_inv_cancel₀ hx0`.

Take `⟨i₀, hi₀⟩` from `Function.ne_iff.1 hX0`. Establish `hi₀' : X i₀ ≠ 0` using `hi₀`. Take `⟨k, h1, h2, β, h3⟩` from `GlobalTheory.InertIwasawaIso.exists_stab (r := 1) (intL L) (VA L) (RingEquiv.refl L) (fun y => mem_intL.trans mem_VA.symm) hσ hU.1 hτ hτ1 (fun u hu hsu ⟨b, hb, hub⟩ => by`. Take `⟨t, ht⟩` from `normSurj finNormSurj henselSqrt hU hq ⟨u, mem_VA.2 (mem_intL.1 hu)⟩ (Subtype.ext hsu) (isUnit_iff_exists_inv.2 ⟨⟨b, mem_VA.2 (mem_intL.1 hb)⟩, Subtype.ext hub⟩)`. Conclude with `⟨t, mem_intL.2 (mem_VA.1 t.2), congrArg Subtype.val ht⟩)`.

Use the proof step `(J := (J : Matrix (Fin n) (Fin n) L)) (by ext i j; exact hh j i) J.isUnit (Λ := intCols L n)`. Use the proof step `(fun y => ⟨fun hy z hz => Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => mul_mem (mul_mem (hσ _ (hz i)) (entries_of_GLint hJ i j)) (hy j), fun hy => by`. Establish `h4 : ∀ i, ((J : Matrix (Fin n) (Fin n) L) *ᵥ y) i ∈ intL L` using `fun i => by`. Use `hy _ (single_mem i)` as an intermediate fact. Rewrite `this` using `[hform, Finset.sum_eq_single i]`.

Simplify `this` using `[Matrix.mulVec, dotProduct]`. Introduce `b _ hb`. Simplify using `[Pi.single_eq_of_ne hb]`. Introduce `hb`. Conclude with `absurd (Finset.mem_univ _) hb`.

Establish `h5` using `mulVec_int (entries_of_GLint (inv_mem hJ)) h4`. Rewrite using `[Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h5⟩)` and apply the resulting hypothesis. Use the proof step `(a := 1) (fun y => by rw [Units.val_one, Matrix.one_mulVec]; rfl)`. Use the proof step `(X := Matrix.of fun i (_ : Fin 1) => X i) (P := Matrix.of fun (_ : Fin 1) j => if j = i₀ then (X i₀)⁻¹ else 0)`. Use the proof step `(by`.

Use extensionality with `a b`. Rewrite using `[Subsingleton.elim a b, Matrix.one_apply_eq]`. Simplify using `[Matrix.mul_apply, hi₀'])`. Use the proof step `(by`. Use extensionality with `a b`.

Rewrite using `[Matrix.mul_assoc, Matrix.zero_apply, ← hX]`. Use the proof step `rfl) hg`. Use `⟨k, h1, entries_of_stab h2, entries_of_stab (inv_mem h2), β.1 0 0, ?_, ?_⟩` and prove the remaining obligations. Use `β.det_ne_zero` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_one]`. Then use the resulting hypothesis.

Use function extensionality and compare the values at `i`. Use `congrFun (congrFun h3 i) 0` as an intermediate fact. Simplify using `only [Matrix.mul_apply, Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton] at this`. Rewrite using `[Pi.smul_apply, smul_eq_mul, mul_comm]`. Conclude with `this`.
-/
theorem exists_int [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (hq : Odd q)
    {J : GL (Fin n) L} (hJ : J ∈ GLint (Fin n) (intL L))
    (hh : ∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i)
    {X : Fin n → L} (hX0 : X ≠ 0) (hX : (fun i => σ (X i)) ⬝ᵥ (J : Matrix (Fin n) (Fin n) L) *ᵥ X = 0)
    {g : GL (Fin n) L} (hg : g ∈ UJ σ (J : Matrix (Fin n) (Fin n) L)) :
    ∃ k ∈ UJ σ (J : Matrix (Fin n) (Fin n) L), (∀ i j, (k : Matrix (Fin n) (Fin n) L) i j ∈ intL L) ∧
      (∀ i j, ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ intL L) ∧
      ∃ β : L, β ≠ 0 ∧ ((g * k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ X = β • X := by
  have hσ : ∀ x ∈ intL L, σ x ∈ intL L := fun x hx => by rw [mem_intL, hU.2.1]; exact mem_intL.1 hx
  obtain ⟨x, hx, hx1⟩ := hU.2.2.2.2.1
  have hx0 : σ x - x ≠ 0 := by
    intro h; rw [h, map_zero] at hx1; exact zero_ne_one hx1
  have hτ : σ x * (σ x - x)⁻¹ ∈ intL L :=
    mul_mem (hσ x hx) (by rw [mem_intL, map_inv₀, hx1, inv_one])
  have hτ1 : σ x * (σ x - x)⁻¹ + σ (σ x * (σ x - x)⁻¹) = 1 := by
    rw [map_mul, map_inv₀, map_sub, hU.1, ← neg_sub (σ x) x, inv_neg]
    linear_combination mul_inv_cancel₀ hx0
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hX0
  have hi₀' : X i₀ ≠ 0 := hi₀
  obtain ⟨k, h1, h2, β, h3⟩ := GlobalTheory.InertIwasawaIso.exists_stab (r := 1) (intL L) (VA L) (RingEquiv.refl L)
    (fun y => mem_intL.trans mem_VA.symm) hσ hU.1 hτ hτ1
    (fun u hu hsu ⟨b, hb, hub⟩ => by
      obtain ⟨t, ht⟩ := normSurj finNormSurj henselSqrt hU hq ⟨u, mem_VA.2 (mem_intL.1 hu)⟩ (Subtype.ext hsu)
        (isUnit_iff_exists_inv.2 ⟨⟨b, mem_VA.2 (mem_intL.1 hb)⟩, Subtype.ext hub⟩)
      exact ⟨t, mem_intL.2 (mem_VA.1 t.2), congrArg Subtype.val ht⟩)
    (J := (J : Matrix (Fin n) (Fin n) L)) (by ext i j; exact hh j i) J.isUnit (Λ := intCols L n)
    (fun y => ⟨fun hy z hz => Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ =>
        mul_mem (mul_mem (hσ _ (hz i)) (entries_of_GLint hJ i j)) (hy j), fun hy => by
      have h4 : ∀ i, ((J : Matrix (Fin n) (Fin n) L) *ᵥ y) i ∈ intL L := fun i => by
        have := hy _ (single_mem i)
        rw [hform, Finset.sum_eq_single i] at this
        · simpa [Matrix.mulVec, dotProduct] using this
        · intro b _ hb; simp [Pi.single_eq_of_ne hb]
        · intro hb; exact absurd (Finset.mem_univ _) hb
      have h5 := mulVec_int (entries_of_GLint (inv_mem hJ)) h4
      rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h5⟩)
    (a := 1) (fun y => by rw [Units.val_one, Matrix.one_mulVec]; rfl)
    (X := Matrix.of fun i (_ : Fin 1) => X i) (P := Matrix.of fun (_ : Fin 1) j => if j = i₀ then (X i₀)⁻¹ else 0)
    (by
      ext a b
      rw [Subsingleton.elim a b, Matrix.one_apply_eq]
      simp [Matrix.mul_apply, hi₀'])
    (by
      ext a b
      rw [Matrix.mul_assoc, Matrix.zero_apply, ← hX]
      rfl) hg
  refine ⟨k, h1, entries_of_stab h2, entries_of_stab (inv_mem h2), β.1 0 0, ?_, ?_⟩
  · have := β.det_ne_zero
    rwa [Matrix.det_fin_one] at this
  · funext i
    have := congrFun (congrFun h3 i) 0
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton] at this
    rw [Pi.smul_apply, smul_eq_mul, mul_comm]
    exact this

end Local

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
  {v : Pl F} {ι : L →+ AE F E}

open GlobalTheory.InertLocFrame

/- English proof (translation)
The claim follows from `pre_spec ι ((him _).1 fun u hu => by rw [← smul_mul_assoc, (him _).2 ⟨1, rfl⟩ u hu, zero_mul])`.
-/
theorem iota_pre (him : ∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z) (z : AE F E) :
    ι (pre ι (ι 1 * z)) = ι 1 * z :=
  pre_spec ι ((him _).1 fun u hu => by rw [← smul_mul_assoc, (him _).2 ⟨1, rfl⟩ u hu, zero_mul])

def proj (hinj : Function.Injective ι) (him : ∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z)
    (hmul : ∀ x y, ι (x * y) = ι x * ι y) : AE F E →+* L where
  toFun z := pre ι (ι 1 * z)
  map_one' := hinj (by rw [iota_pre him, mul_one])
  map_zero' := hinj (by rw [iota_pre him, mul_zero, map_zero])
  map_add' a b := hinj (by rw [map_add, iota_pre him, iota_pre him, iota_pre him, mul_add])
  map_mul' a b := hinj (by
    rw [hmul, iota_pre him, iota_pre him, iota_pre him, mul_mul_mul_comm, ← hmul, mul_one])

variable (hinj : Function.Injective ι) (him : ∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z)
  (hmul : ∀ x y, ι (x * y) = ι x * ι y)

/- English proof (translation)
The claim follows from `iota_pre him z`.
-/
theorem iota_proj (z : AE F E) : ι (proj hinj him hmul z) = ι 1 * z := iota_pre him z

/- English proof (translation)
Rewrite using `[hmul, iota_proj, ← mul_assoc, ← hmul, mul_one]`.
-/
theorem iota_mul (a : L) (z : AE F E) : ι a * z = ι (a * proj hinj him hmul z) := by
  rw [hmul, iota_proj, ← mul_assoc, ← hmul, mul_one]

/- English proof (translation)
The claim follows from `hinj (by rw [hσ, iota_proj, iota_proj, map_mul, ← hσ, map_one σL])`.
-/
theorem proj_cA {σ : E →ₐ[F] E} {σL : L →+* L} (hσ : ∀ x, ι (σL x) = cA σ (ι x)) (z : AE F E) :
    proj hinj him hmul (cA σ z) = σL (proj hinj him hmul z) :=
  hinj (by rw [hσ, iota_proj, iota_proj, map_mul, ← hσ, map_one σL])

/- English proof (translation)
Use extensionality with `i j`. Take `⟨y, hy⟩` from `(him ((M - 1) i j)).1 fun u hu => congrFun (congrFun (hM u hu) i) j`. Establish `h : ι 1 * (M - 1) i j = (M - 1) i j` using `by rw [← hy, ← hmul, one_mul]`. Rewrite `h` using `[Matrix.sub_apply]`. Rewrite using `[Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.map_apply, iota_proj, smul_eq_mul]`.

Take the linear combination `-h`.
-/
theorem eq_glue {n : ℕ} {M : Matrix (Fin n) (Fin n) (AE F E)} (hM : At (evFin F v) (M - 1)) :
    M = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (AE F E)) + (M.map (proj hinj him hmul)).map ι := by
  ext i j
  obtain ⟨y, hy⟩ := (him ((M - 1) i j)).1 fun u hu => congrFun (congrFun (hM u hu) i) j
  have h : ι 1 * (M - 1) i j = (M - 1) i j := by rw [← hy, ← hmul, one_mul]
  rw [Matrix.sub_apply] at h
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.map_apply, iota_proj, smul_eq_mul]
  linear_combination -h

/- English proof (translation)
Rewrite using `[Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, add_smul]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Use `congrArg ι (congrFun h i)` as an intermediate fact. Rewrite `this` using `[Pi.smul_apply, smul_eq_mul, ← iota_mul]`.

Rewrite using `[Pi.smul_apply, smul_eq_mul, ← this]`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, ← iota_mul]`.
-/
theorem glue_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) L) (z : Fin n → AE F E) (β : L)
    (h : A *ᵥ (fun i => proj hinj him hmul (z i)) = β • fun i => proj hinj him hmul (z i)) :
    ((1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (AE F E)) + A.map ι) *ᵥ z = (1 - ι 1 + ι β) • z := by
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, add_smul]
  congr 1
  funext i
  have := congrArg ι (congrFun h i)
  rw [Pi.smul_apply, smul_eq_mul, ← iota_mul] at this
  rw [Pi.smul_apply, smul_eq_mul, ← this]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, ← iota_mul]

include hmul in
/- English proof (translation)
Establish `h1 : ι 1 * ι 1 = ι 1` using `by rw [← hmul, one_mul]`. Establish `h2 : ι 1 * ι b = ι b` using `by rw [← hmul, one_mul]`. Establish `h3 : ι 1 * ι a = ι a` using `by rw [← hmul, one_mul]`. Rewrite using `[hmul]`. Take the linear combination `h1 - h2 - h3`.
-/
theorem glue_mul_glue (a b : L) : (1 - ι 1 + ι a) * (1 - ι 1 + ι b) = 1 - ι 1 + ι (a * b) := by
  have h1 : ι 1 * ι 1 = ι 1 := by rw [← hmul, one_mul]
  have h2 : ι 1 * ι b = ι b := by rw [← hmul, one_mul]
  have h3 : ι 1 * ι a = ι a := by rw [← hmul, one_mul]
  rw [hmul]
  linear_combination h1 - h2 - h3

/- English proof (translation)
Establish `h1 : evFin F v (1 - GlobalTheory.VacFixKAt.eAt v) = 0`. Rewrite using `[map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self]`. Establish `h2 : (M - 1) *ᵥ ((1 - GlobalTheory.VacFixKAt.eAt v) • z) = 0`. Rewrite using `[Matrix.mulVec_smul, ← GlobalTheory.VacFixKAt.smul_mulVec', hM _ h1, Matrix.zero_mulVec]`. Rewrite `h2` using `[Matrix.sub_mulVec, Matrix.one_mulVec, sub_smul, one_smul, Matrix.mulVec_sub, sub_eq_zero, sub_eq_iff_eq_add]`.

Establish `h3` using `GlobalTheory.VacFixKAt.eAt_smul_mem W v hz`. Rewrite using `[h2]`. Conclude with `add_mem (sub_mem hz (GlobalTheory.VacFixKAt.latAt_le_latHat W v h3)) (GlobalTheory.VacFixKAt.latAt_le_latHat W v (hL _ h3))`.
-/
theorem mulVec_mem_latHat {d : ℕ} (W : Spc F E d) (v : Pl F) {M : Matrix (Fin d) (Fin d) (AE F E)}
    (hM : At (evFin F v) (M - 1)) (hL : ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v)
    {z : Fin d → AE F E} (hz : z ∈ latHat W) : M *ᵥ z ∈ latHat W := by
  have h1 : evFin F v (1 - GlobalTheory.VacFixKAt.eAt v) = 0 := by
    rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self]
  have h2 : (M - 1) *ᵥ ((1 - GlobalTheory.VacFixKAt.eAt v) • z) = 0 := by
    rw [Matrix.mulVec_smul, ← GlobalTheory.VacFixKAt.smul_mulVec', hM _ h1, Matrix.zero_mulVec]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_smul, one_smul, Matrix.mulVec_sub, sub_eq_zero, sub_eq_iff_eq_add] at h2
  have h3 := GlobalTheory.VacFixKAt.eAt_smul_mem W v hz
  rw [h2]
  exact add_mem (sub_mem hz (GlobalTheory.VacFixKAt.latAt_le_latHat W v h3)) (GlobalTheory.VacFixKAt.latAt_le_latHat W v (hL _ h3))

/- English proof (translation)
Take `⟨hU, hL⟩` from `hk`. Establish `hinv : mat k⁻¹ * mat k = 1` using `Units.inv_mul k.1`. Establish `hU' : At (evFin F v) (mat k⁻¹ - 1)`. Introduce `u hu`. Establish `h0 : u • (mat k - 1) = 0` using `hU u hu`.

Establish `: mat k⁻¹ - 1 = -(mat k⁻¹ * (mat k - 1))`. Rewrite using `[Matrix.mul_sub, hinv, Matrix.mul_one, neg_sub]`. Rewrite using `[this, smul_neg, ← Matrix.mul_smul, h0, Matrix.mul_zero, neg_zero]`. Conclude with `⟨hU, fun z hz => ⟨mulVec_mem_latHat W v hU (fun z hz => (hL z hz).1) hz, mulVec_mem_latHat W v hU' (fun z hz => (hL z hz).2) hz⟩⟩`.
-/
theorem mem_KAt {σ : E →ₐ[F] E} {d : ℕ} (W : Spc F E d) (v : Pl F) {k : UA σ W.J}
    (hk : k ∈ GlobalTheory.InertSph.KAt σ W v) : k ∈ KAt σ W v := by
  obtain ⟨hU, hL⟩ := hk
  have hinv : mat k⁻¹ * mat k = 1 := Units.inv_mul k.1
  have hU' : At (evFin F v) (mat k⁻¹ - 1) := by
    intro u hu
    have h0 : u • (mat k - 1) = 0 := hU u hu
    have : mat k⁻¹ - 1 = -(mat k⁻¹ * (mat k - 1)) := by
      rw [Matrix.mul_sub, hinv, Matrix.mul_one, neg_sub]
    rw [this, smul_neg, ← Matrix.mul_smul, h0, Matrix.mul_zero, neg_zero]
  exact ⟨hU, fun z hz => ⟨mulVec_mem_latHat W v hU (fun z hz => (hL z hz).1) hz,
    mulVec_mem_latHat W v hU' (fun z hz => (hL z hz).2) hz⟩⟩

end Adelic

section Alg

variable {L : Type} [Field L] {n : ℕ} (σ : L →+* L) (c : L) (T : Matrix (Fin n) (Fin n) L) (P : GL (Fin n) L)

/- English proof (translation)
Simplify using `only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]`.
-/
theorem cT_gram (Y : Matrix (Fin n) (Fin n) L) :
    Formalism.UG.cT σ Y * (c • (P.1ᵀ * T * P.1.map σ)ᵀ) * Y = c • ((P.1 * Y)ᵀ * T * (P.1 * Y).map σ)ᵀ := by
  simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_assoc]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Formalism.UG.cT σ (P⁻¹ * G * P).1 * _ * (P⁻¹ * G * P).1 = _`. Rewrite using `[cT_gram, ← Units.val_mul, ← mul_assoc, mul_inv_cancel_left, Units.val_mul, Matrix.map_mul, Matrix.transpose_mul G.1]`. Use `congr 2`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem conj_mem_UJ {G : GL (Fin n) L} (hG : G.1ᵀ * T * G.1.map σ = T) :
    P⁻¹ * G * P ∈ Formalism.UG.UJ σ (c • (P.1ᵀ * T * P.1.map σ)ᵀ) := by
  change Formalism.UG.cT σ (P⁻¹ * G * P).1 * _ * (P⁻¹ * G * P).1 = _
  rw [cT_gram, ← Units.val_mul, ← mul_assoc, mul_inv_cancel_left, Units.val_mul, Matrix.map_mul, Matrix.transpose_mul G.1]
  congr 2
  calc _ = P.1ᵀ * (G.1ᵀ * T * G.1.map σ) * P.1.map σ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hG]

/- English proof (translation)
Establish `e : (fun i => σ ((P.1 *ᵥ Y) i)) = P.1.map σ *ᵥ fun i => σ (Y i)` using `funext fun i => RingHom.map_mulVec σ P.1 Y i`. Rewrite using `[e, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec Y, Matrix.vecMul_transpose, Matrix.mulVec_mulVec _ T]`.
-/
theorem iso_gram (Y : Fin n → L) :
    (fun i => σ (Y i)) ⬝ᵥ (c • (P.1ᵀ * T * P.1.map σ)ᵀ) *ᵥ Y = c * ((P.1 *ᵥ Y) ⬝ᵥ T *ᵥ fun i => σ ((P.1 *ᵥ Y) i)) := by
  have e : (fun i => σ ((P.1 *ᵥ Y) i)) = P.1.map σ *ᵥ fun i => σ (Y i) := funext fun i => RingHom.map_mulVec σ P.1 Y i
  rw [e, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.mulVec_transpose, dotProduct_comm,
    ← Matrix.dotProduct_mulVec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec Y,
    Matrix.vecMul_transpose, Matrix.mulVec_mulVec _ T]

end Alg

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B d W r s hB hW x hx0 hx v hv g hg`. Take `⟨w, hin⟩ : ∃ w : HeightOneSpectrum (𝓞 E), Formalism.UG.IsInertAt F E v w` from `(GlobalTheory.KFinLoc.split_or_inert F E σ B hB v).resolve_left fun ⟨e⟩ => hv.false e`. Take `⟨L, iF, iC, iVl, iCS, ϖ, σL, q, δ, ψL, ι, hunr, hodd, hδ, -, -, hinj, him, hmul, hσ, hint, -⟩` from `GlobalTheory.InertLocField.field_data F E σ B hB v w hin`. Establish `hδne : δ ≠ 0` using `fun h0 => by rw [h0, map_zero] at hδ; exact zero_ne_one hδ.1`. Take `⟨P, hP⟩` from `GlobalTheory.InertLocBasis.exists_basis_at_inert F E v w hin d W hW.lat L ι hinj him hmul hint`.

Take `⟨JT, hJT, hJTg, hJTh⟩` from `GlobalTheory.InertGramSkew.gram_skew_unimodular F E σ B hB v w hin d r s W hW L ϖ σL q δ ι hunr hodd hδ hinj him hmul hσ hint P hP`. Take `⟨iW, hiW⟩` from `GlobalTheory.InertLocFrame.HomW.homW F E σ v d W L σL δ ι hδne him hmul hσ P JT hJTg`. Set `π` to `proj hinj him hmul`. Set `T : Matrix (Fin d) (Fin d) L` to `(incM F W.J).map π`. Establish `hJ : (JT : Matrix (Fin d) (Fin d) L) = -δ⁻¹ • (P.1ᵀ * T * P.1.map σL)ᵀ` using `hJTg`.

Set `G : GL (Fin d) L` to `Matrix.GeneralLinearGroup.map π g.1`. Establish `hGv : G.1 = (mat g).map π` using `rfl`. Establish `hG : G.1ᵀ * T * G.1.map σL = T`. Establish `h0 : (mat g)ᵀ * incM F W.J * (mat g).map (cA σ) = incM F W.J` using `g.2`. Establish `h1 : G.1.map σL = ((mat g).map (cA σ)).map π`.

Use extensionality with `i j`. Conclude with `(proj_cA hinj him hmul hσ _).symm`. Rewrite using `[h1, hGv, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, h0]`. Establish `hh : P⁻¹ * G * P ∈ Formalism.UG.UJ σL (JT : Matrix (Fin d) (Fin d) L)`. Rewrite using `[hJ]`.

Conclude with `conj_mem_UJ σL _ T P hG`. Establish `hgi : iW ⟨_, hh⟩ = g`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `mat _ = mat g`.

Rewrite using `[hiW, eq_glue hinj him hmul hg]`. Express the relevant statement in the definitionally equal form `_ + (P * (P⁻¹ * G * P) * P⁻¹ : GL (Fin d) L).1.map ι = _`. Rewrite using `[show P * (P⁻¹ * G * P) * P⁻¹ = G by group]`. Both sides reduce to the same expression. Set `y : Fin d → L` to `fun i => π (incV F x i)`.

Establish `hPy : P.1 *ᵥ ((P⁻¹).1 *ᵥ y) = y` using `by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Establish `hy0 : (P⁻¹).1 *ᵥ y ≠ 0` using `fun h0 => by`. Rewrite `hPy` using `[h0, Matrix.mulVec_zero]`. Apply `hx0` to reduce the goal to its premises. Use function extensionality and compare the values at `i`.

Conclude with `(π.comp (inclR (F := F) (AF F))).injective ((congrFun hPy i).symm.trans (map_zero _).symm)`. Establish `hiso : (fun i => σL (((P⁻¹).1 *ᵥ y) i)) ⬝ᵥ (JT : Matrix (Fin d) (Fin d) L) *ᵥ ((P⁻¹).1 *ᵥ y) = 0`. Rewrite using `[hJ, iso_gram, hPy]`. Establish `h0` using `congrArg (π.comp (inclR (F := F) (AF F))) hx`. Rewrite `h0` using `[map_zero]`.

Establish `h1 : ∀ i, σL (y i) = π (inclR (F` using `F) (AF F) (σ (x i))) := fun i => (proj_cA hinj him hmul hσ _).symm`. Establish `h2 : (y ⬝ᵥ T *ᵥ fun i => σL (y i)) = (π.comp (inclR (F` using `F) (AF F))) (form σ W.J x x) := by`. Simplify using `only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, h1]`. Both sides reduce to the same expression. Rewrite using `[h2, h0, mul_zero]`.

Take `⟨k, hk, hk1, hk2, β, hβ, hkX⟩` from `exists_int hunr hodd hJT hJTh hy0 hiso hh`. Use `⟨iW ⟨k, hk⟩, mem_KAt W v (GlobalTheory.InertKatFrame.mem_KAt_of_frame F E σ v d W L ι hinj him hmul hint P hP _ k.1 (k⁻¹).1 hk1 hk2 (hiW _) (by rw [← map_inv, hiW]; rfl)), ⟨1 - ι 1 + ι β, 1 - ι 1 + ι β⁻¹, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[glue_mul_glue hmul, mul_inv_cancel₀ hβ, sub_add_cancel]`. Rewrite using `[glue_mul_glue hmul, inv_mul_cancel₀ hβ, sub_add_cancel]`. Rewrite using `[← hgi, ← map_inv, ← map_mul, hiW]`.

Use `glue_mulVec hinj him hmul _ _ β ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(P.1 * (P⁻¹ * G * P * k⁻¹ : GL (Fin d) L).1 * (P⁻¹).1) *ᵥ y = β • y`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hkX, Matrix.mulVec_smul, hPy]`.
-/
theorem exists_stab_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d : ℕ) (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (x : Fin d → E), x ≠ 0 → form σ W.J x x = 0 →
    ∀ (v : Pl F), IsEmpty (E →ₐ[F] Fv F v) → ∀ g ∈ UAt σ W (evFin F v),
      ∃ k ∈ KAt σ W v, ∃ t : (AE F E)ˣ, mat (g * k⁻¹) *ᵥ incV F x = t.1 • incV F x := by
  intro F E _ _ _ _ _ σ B d W r s hB hW x hx0 hx v hv g hg
  obtain ⟨w, hin⟩ : ∃ w : HeightOneSpectrum (𝓞 E), Formalism.UG.IsInertAt F E v w :=
    (GlobalTheory.KFinLoc.split_or_inert F E σ B hB v).resolve_left fun ⟨e⟩ => hv.false e
  obtain ⟨L, iF, iC, iVl, iCS, ϖ, σL, q, δ, ψL, ι, hunr, hodd, hδ, -, -, hinj, him, hmul, hσ, hint, -⟩ :=
    GlobalTheory.InertLocField.field_data F E σ B hB v w hin
  have hδne : δ ≠ 0 := fun h0 => by rw [h0, map_zero] at hδ; exact zero_ne_one hδ.1
  obtain ⟨P, hP⟩ := GlobalTheory.InertLocBasis.exists_basis_at_inert F E v w hin d W hW.lat L ι hinj him hmul hint
  obtain ⟨JT, hJT, hJTg, hJTh⟩ := GlobalTheory.InertGramSkew.gram_skew_unimodular F E σ B hB v w hin d r s W hW L ϖ σL q δ ι hunr hodd hδ hinj
    him hmul hσ hint P hP
  obtain ⟨iW, hiW⟩ := GlobalTheory.InertLocFrame.HomW.homW F E σ v d W L σL δ ι hδne him hmul hσ P JT hJTg
  let π := proj hinj him hmul
  let T : Matrix (Fin d) (Fin d) L := (incM F W.J).map π
  have hJ : (JT : Matrix (Fin d) (Fin d) L) = -δ⁻¹ • (P.1ᵀ * T * P.1.map σL)ᵀ := hJTg
  let G : GL (Fin d) L := Matrix.GeneralLinearGroup.map π g.1
  have hGv : G.1 = (mat g).map π := rfl
  have hG : G.1ᵀ * T * G.1.map σL = T := by
    have h0 : (mat g)ᵀ * incM F W.J * (mat g).map (cA σ) = incM F W.J := g.2
    have h1 : G.1.map σL = ((mat g).map (cA σ)).map π := by
      ext i j; exact (proj_cA hinj him hmul hσ _).symm
    rw [h1, hGv, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, h0]
  have hh : P⁻¹ * G * P ∈ Formalism.UG.UJ σL (JT : Matrix (Fin d) (Fin d) L) := by
    rw [hJ]; exact conj_mem_UJ σL _ T P hG
  have hgi : iW ⟨_, hh⟩ = g := by
    apply Subtype.ext
    apply Units.ext
    change mat _ = mat g
    rw [hiW, eq_glue hinj him hmul hg]
    change _ + (P * (P⁻¹ * G * P) * P⁻¹ : GL (Fin d) L).1.map ι = _
    rw [show P * (P⁻¹ * G * P) * P⁻¹ = G by group]
    rfl
  let y : Fin d → L := fun i => π (incV F x i)
  have hPy : P.1 *ᵥ ((P⁻¹).1 *ᵥ y) = y := by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hy0 : (P⁻¹).1 *ᵥ y ≠ 0 := fun h0 => by
    rw [h0, Matrix.mulVec_zero] at hPy
    apply hx0
    funext i
    exact (π.comp (inclR (F := F) (AF F))).injective ((congrFun hPy i).symm.trans (map_zero _).symm)
  have hiso : (fun i => σL (((P⁻¹).1 *ᵥ y) i)) ⬝ᵥ (JT : Matrix (Fin d) (Fin d) L) *ᵥ ((P⁻¹).1 *ᵥ y) = 0 := by
    rw [hJ, iso_gram, hPy]
    have h0 := congrArg (π.comp (inclR (F := F) (AF F))) hx
    rw [map_zero] at h0
    have h1 : ∀ i, σL (y i) = π (inclR (F := F) (AF F) (σ (x i))) := fun i =>
      (proj_cA hinj him hmul hσ _).symm
    have h2 : (y ⬝ᵥ T *ᵥ fun i => σL (y i)) = (π.comp (inclR (F := F) (AF F))) (form σ W.J x x) := by
      simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, h1]
      rfl
    rw [h2, h0, mul_zero]
  obtain ⟨k, hk, hk1, hk2, β, hβ, hkX⟩ := exists_int hunr hodd hJT hJTh hy0 hiso hh
  refine ⟨iW ⟨k, hk⟩, mem_KAt W v (GlobalTheory.InertKatFrame.mem_KAt_of_frame F E σ v d W L ι hinj him hmul hint P hP _ k.1 (k⁻¹).1 hk1 hk2 (hiW _)
    (by rw [← map_inv, hiW]; rfl)), ⟨1 - ι 1 + ι β, 1 - ι 1 + ι β⁻¹, ?_, ?_⟩, ?_⟩
  · rw [glue_mul_glue hmul, mul_inv_cancel₀ hβ, sub_add_cancel]
  · rw [glue_mul_glue hmul, inv_mul_cancel₀ hβ, sub_add_cancel]
  · rw [← hgi, ← map_inv, ← map_mul, hiW]
    refine glue_mulVec hinj him hmul _ _ β ?_
    change (P.1 * (P⁻¹ * G * P * k⁻¹ : GL (Fin d) L).1 * (P⁻¹).1) *ᵥ y = β • y
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hkX, Matrix.mulVec_smul, hPy]

end GlobalTheory.InertLineTrans
