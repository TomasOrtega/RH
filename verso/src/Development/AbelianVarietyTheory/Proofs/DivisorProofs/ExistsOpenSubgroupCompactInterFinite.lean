import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCompactPreimage
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThetaCplV

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ThetaCplV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F) in

def intFinPart : Subring (AF F) where
  carrier := {a | a.2 ∈ Formalism.UG.intAd F}
  mul_mem' := fun {a b} ha hb => show (a * b).2 ∈ Formalism.UG.intAd F from mul_mem ha hb
  one_mem' := one_mem (Formalism.UG.intAd F)
  add_mem' := fun {a b} ha hb => show (a + b).2 ∈ Formalism.UG.intAd F from add_mem ha hb
  zero_mem' := zero_mem (Formalism.UG.intAd F)
  neg_mem' := fun {a} ha => show (-a).2 ∈ Formalism.UG.intAd F from neg_mem ha

variable (F E) in

def intFinE : Subring (AE F E) :=
  Subring.closure {x | ∃ a ∈ intFinPart F, ∃ β : 𝓞 E, x = a ⊗ₜ[F] (β : E)}

variable (F) in
/- English proof (translation)
Establish `h : IsOpen (Formalism.UG.intAd F : Set (Af F))` using `RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (fun _ => Valued.isOpen_valuationSubring _)`. Establish `e : (intFinPart F : Set (AF F)) = (fun a : AF F => a.2) ⁻¹' (Formalism.UG.intAd F : Set (Af F))` using `rfl`. Establish `hc : Continuous (fun a : AF F => a.2)` using `continuous_snd`. Rewrite using `[e]`. Conclude with `h.preimage hc`.
-/
theorem isOpen_intFinPart : IsOpen (intFinPart F : Set (AF F)) := by
  have h : IsOpen (Formalism.UG.intAd F : Set (Af F)) :=
    RestrictedProduct.isOpen_forall_mem
      (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun _ => Valued.isOpen_valuationSubring _)
  have e : (intFinPart F : Set (AF F)) = (fun a : AF F => a.2) ⁻¹' (Formalism.UG.intAd F : Set (Af F)) := rfl
  have hc : Continuous (fun a : AF F => a.2) := continuous_snd
  rw [e]
  exact h.preimage hc

variable (F E) in
/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _`. Set `b : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → E` to `fun i => (RingOfIntegers.basis E i : E)`. Set `f : (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → AF F) →ₗ[AF F] AE F E` to `Fintype.linearCombination (AF F) fun i => (1 : AF F) ⊗ₜ[F] b i`. Establish `hf : ∀ a, f a = ∑ i, a i ⊗ₜ[F] b i` using `fun a => by`.

Simplify using `[f, Fintype.linearCombination_apply, TensorProduct.smul_tmul']`. Establish `hsurj : Function.Surjective f` using `fun x => by`. Take `⟨a, ha⟩` from `GlobalTheory.AdelicPointsUnimod.exists_sum_tmul (F := F) (E := E) x`. Conclude with `⟨a, by rw [hf, ha]⟩`. Establish `hopen : IsOpenMap f` using `(IsModuleTopology.isOpenQuotientMap_of_surjective hsurj).isOpenMap`.

Establish `hP : IsOpen (Set.univ.pi fun _ : Module.Free.ChooseBasisIndex ℤ (𝓞 E) => (intFinPart F : Set (AF F)))` using `isOpen_set_pi Set.finite_univ fun _ _ => isOpen_intFinPart F`. Establish `hsub : f '' (Set.univ.pi fun _ => (intFinPart F : Set (AF F))) ⊆ intFinE F E`. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Rewrite using `[hf]`. Conclude with `sum_mem fun i _ => Subring.subset_closure ⟨a i, ha i trivial, RingOfIntegers.basis E i, rfl⟩`.

Establish `h0 : (0 : AE F E) ∈ f '' (Set.univ.pi fun _ => (intFinPart F : Set (AF F)))` using `⟨0, fun _ _ => zero_mem (intFinPart F), map_zero f⟩`. Conclude with `AddSubgroup.isOpen_of_mem_nhds (intFinE F E).toAddSubgroup (Filter.mem_of_superset ((hopen _ hP).mem_nhds h0) hsub)`.
-/
theorem isOpen_intFinE : IsOpen (intFinE F E : Set (AE F E)) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  let b : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → E := fun i => (RingOfIntegers.basis E i : E)
  let f : (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → AF F) →ₗ[AF F] AE F E :=
    Fintype.linearCombination (AF F) fun i => (1 : AF F) ⊗ₜ[F] b i
  have hf : ∀ a, f a = ∑ i, a i ⊗ₜ[F] b i := fun a => by
    simp [f, Fintype.linearCombination_apply, TensorProduct.smul_tmul']
  have hsurj : Function.Surjective f := fun x => by
    obtain ⟨a, ha⟩ := GlobalTheory.AdelicPointsUnimod.exists_sum_tmul (F := F) (E := E) x
    exact ⟨a, by rw [hf, ha]⟩
  have hopen : IsOpenMap f := (IsModuleTopology.isOpenQuotientMap_of_surjective hsurj).isOpenMap
  have hP : IsOpen (Set.univ.pi fun _ : Module.Free.ChooseBasisIndex ℤ (𝓞 E) => (intFinPart F : Set (AF F))) :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_intFinPart F
  have hsub : f '' (Set.univ.pi fun _ => (intFinPart F : Set (AF F))) ⊆ intFinE F E := by
    rintro _ ⟨a, ha, rfl⟩
    rw [hf]
    exact sum_mem fun i _ => Subring.subset_closure ⟨a i, ha i trivial, RingOfIntegers.basis E i, rfl⟩
  have h0 : (0 : AE F E) ∈ f '' (Set.univ.pi fun _ => (intFinPart F : Set (AF F))) :=
    ⟨0, fun _ _ => zero_mem (intFinPart F), map_zero f⟩
  exact AddSubgroup.isOpen_of_mem_nhds (intFinE F E).toAddSubgroup
    (Filter.mem_of_superset ((hopen _ hP).mem_nhds h0) hsub)

variable (F) in

def finIdem : AF F := ((0, 1) : Ainf F × Af F)

/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl, one_mem (Formalism.UG.intAd F)⟩`.
-/
theorem finIdem_mem_intFin : finIdem F ∈ GlobalTheory.AdelicPointsUnimod.intFin F :=
  ⟨rfl, one_mem (Formalism.UG.intAd F)⟩

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show (0 : Ainf F) * a.1 = 0`. Rewrite using `[zero_mul]`. Use `show (1 : Af F) * a.2 ∈ Formalism.UG.intAd F`. Rewrite using `[one_mul]`.

Conclude with `ha`.
-/
theorem mul_finIdem_mem_intFin {a : AF F} (ha : a ∈ intFinPart F) :
    finIdem F * a ∈ GlobalTheory.AdelicPointsUnimod.intFin F := by
  refine ⟨?_, ?_⟩
  · show (0 : Ainf F) * a.1 = 0
    rw [zero_mul]
  · show (1 : Af F) * a.2 ∈ Formalism.UG.intAd F
    rw [one_mul]
    exact ha

/- English proof (translation)
Use `show (((0 : Ainf F) * 0, (1 : Af F) * 1) : Ainf F × Af F) = ((0, 1) : Ainf F × Af F)`. Rewrite using `[mul_zero, mul_one]`.
-/
theorem finIdem_mul_self : finIdem F * finIdem F = finIdem F := by
  show (((0 : Ainf F) * 0, (1 : Af F) * 1) : Ainf F × Af F) = ((0, 1) : Ainf F × Af F)
  rw [mul_zero, mul_one]

variable (F E) in

def infPartE : AE F E →ₐ[F] Ainf F ⊗[F] E := Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)

variable (F E) in

def infInclE : Ainf F ⊗[F] E →ₗ[F] AE F E :=
  TensorProduct.map (LinearMap.inl F (Ainf F) (Af F)) LinearMap.id

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem infInclE_tmul (r : Ainf F) (b : E) : infInclE F E (r ⊗ₜ[F] b) = (show AF F from (r, 0)) ⊗ₜ[F] b := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem infPartE_tmul (a : AF F) (b : E) : infPartE F E (a ⊗ₜ[F] b) = (fstA F a) ⊗ₜ[F] b := rfl

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Rewrite using `[infPartE_tmul, infInclE_tmul, ← TensorProduct.add_tmul]`.

Use `congr 1`. Use `show a = (((0 : Ainf F) * a.1 + (fstA F a), (1 : Af F) * a.2 + 0) : Ainf F × Af F)`. Rewrite using `[zero_mul, zero_add, one_mul, add_zero]`. Both sides reduce to the same expression. Consider the case `add x y hx hy => conv_lhs => rw [hx, hy]`.

Rewrite using `[mul_add, map_add, map_add]`. Normalize the expressions using the abelian group laws.
-/
theorem eq_finIdem_mul_add (x : AE F E) :
    x = (finIdem F ⊗ₜ[F] (1 : E)) * x +
      infInclE F E (infPartE F E x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [infPartE_tmul, infInclE_tmul, ← TensorProduct.add_tmul]
    congr 1
    show a = (((0 : Ainf F) * a.1 + (fstA F a), (1 : Af F) * a.2 + 0) : Ainf F × Af F)
    rw [zero_mul, zero_add, one_mul, add_zero]
    rfl
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    rw [mul_add, map_add, map_add]
    abel

/- English proof (translation)
Rewrite using `[map_mul]`. Establish `: infPartE F E (finIdem F ⊗ₜ[F] (1 : E)) = 0`. Simplify using `only [infPartE, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]`. Establish `h0 : fstA F (finIdem F) = 0` using `rfl`. Rewrite using `[h0, TensorProduct.zero_tmul]`.

Rewrite using `[this, zero_mul]`.
-/
theorem infPartE_finIdem_mul (y : AE F E) : infPartE F E ((finIdem F ⊗ₜ[F] (1 : E)) * y) = 0 := by
  rw [map_mul]
  have : infPartE F E (finIdem F ⊗ₜ[F] (1 : E)) = 0 := by
    simp only [infPartE, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    have h0 : fstA F (finIdem F) = 0 := rfl
    rw [h0, TensorProduct.zero_tmul]
  rw [this, zero_mul]

/- English proof (translation)
Establish `hee : (finIdem F ⊗ₜ[F] (1 : E)) * (finIdem F ⊗ₜ[F] (1 : E)) = finIdem F ⊗ₜ[F] (1 : E)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, finIdem_mul_self, one_mul]`. Proceed by induction on `hx using Subring.closure_induction with`. Consider the case `mem x hx`. Take `⟨a, ha, β, rfl⟩` from `hx`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Conclude with `hC _ (mul_finIdem_mem_intFin ha) β`. Consider the case `zero => rw [mul_zero]`. Conclude with `zero_mem C`. Consider the case `one`.

Rewrite using `[mul_one]`. Use `hC _ finIdem_mem_intFin 1` as an intermediate fact. Simplify using `using this`. Consider the case `add x y _ _ hx hy => rw [mul_add]`. Conclude with `add_mem hx hy`.

Consider the case `neg x _ hx => rw [mul_neg]`. Conclude with `neg_mem hx`. Consider the case `mul x y _ _ hx hy`. Establish `e : (finIdem F ⊗ₜ[F] (1 : E)) * (x * y) = ((finIdem F ⊗ₜ[F] (1 : E)) * x) * ((finIdem F ⊗ₜ[F] (1 : E)) * y)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[e]`. Conclude with `mul_mem hx hy`.
-/
theorem finIdem_mul_mem (C : NonUnitalSubring (AE F E))
    (hC : ∀ r ∈ GlobalTheory.AdelicPointsUnimod.intFin F, ∀ β : 𝓞 E, r ⊗ₜ[F] (β : E) ∈ C) {x : AE F E}
    (hx : x ∈ intFinE F E) : (finIdem F ⊗ₜ[F] (1 : E)) * x ∈ C := by
  have hee : (finIdem F ⊗ₜ[F] (1 : E)) * (finIdem F ⊗ₜ[F] (1 : E)) = finIdem F ⊗ₜ[F] (1 : E) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, finIdem_mul_self, one_mul]
  induction hx using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, β, rfl⟩ := hx
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact hC _ (mul_finIdem_mem_intFin ha) β
  | zero => rw [mul_zero]; exact zero_mem C
  | one =>
    rw [mul_one]
    have := hC _ finIdem_mem_intFin 1
    simpa using this
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx
  | mul x y _ _ hx hy =>
    have e : (finIdem F ⊗ₜ[F] (1 : E)) * (x * y) =
        ((finIdem F ⊗ₜ[F] (1 : E)) * x) * ((finIdem F ⊗ₜ[F] (1 : E)) * y) := by
      calc (finIdem F ⊗ₜ[F] (1 : E)) * (x * y)
          = ((finIdem F ⊗ₜ[F] (1 : E)) * (finIdem F ⊗ₜ[F] (1 : E))) * (x * y) := by rw [hee]
        _ = _ := by ring
    rw [e]
    exact mul_mem hx hy

def intLevel (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Subgroup (UA σ J) where
  carrier := {g | ∀ i j, mat g i j ∈ intFinE F E ∧ mat g⁻¹ i j ∈ intFinE F E}
  one_mem' := by
    intro i j
    have h1 : mat (1 : UA σ J) = 1 := rfl
    rw [inv_one, h1]
    have : (1 : Matrix (Fin n) (Fin n) (AE F E)) i j ∈ intFinE F E := by
      rw [Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    exact ⟨this, this⟩
  mul_mem' := by
    intro a b ha hb i j
    have hm : ∀ x y : UA σ J, mat (x * y) = mat x * mat y := fun _ _ => rfl
    refine ⟨?_, ?_⟩
    · rw [hm, Matrix.mul_apply]
      exact sum_mem fun l _ => mul_mem (ha i l).1 (hb l j).1
    · rw [mul_inv_rev, hm, Matrix.mul_apply]
      exact sum_mem fun l _ => mul_mem (hb i l).2 (ha l j).2
  inv_mem' := by
    intro a ha i j
    rw [inv_inv]
    exact ⟨(ha i j).2, (ha i j).1⟩

/- English proof (translation)
Take `⟨hTG, -, -, -⟩` from `GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n J`. Establish `hv : Continuous fun g : UA σ J => ((g : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))` using `Units.continuous_val.comp continuous_subtype_val`. Establish `hmat : ∀ i j, Continuous fun g : UA σ J => mat g i j` using `fun i j => hv.matrix_elem i j`. Establish `e : (intLevel σ J : Set (UA σ J)) = ⋂ i, ⋂ j, ((fun g : UA σ J => mat g i j) ⁻¹' (intFinE F E : Set (AE F E)) ∩ (fun g : UA σ J => mat g⁻¹ i j) ⁻¹' (intFinE F E : Set (AE F E)))`. Use extensionality with `g`.

Simplify using `only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ((isOpen_intFinE F E).preimage (hmat i j)).inter ((isOpen_intFinE F E).preimage ((hmat i j).comp continuous_inv))`.
-/
theorem isOpen_intLevel (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    IsOpen (intLevel σ J : Set (UA σ J)) := by
  obtain ⟨hTG, -, -, -⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n J
  have hv : Continuous fun g : UA σ J => ((g : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) :=
    Units.continuous_val.comp continuous_subtype_val
  have hmat : ∀ i j, Continuous fun g : UA σ J => mat g i j := fun i j => hv.matrix_elem i j
  have e : (intLevel σ J : Set (UA σ J)) =
      ⋂ i, ⋂ j, ((fun g : UA σ J => mat g i j) ⁻¹' (intFinE F E : Set (AE F E)) ∩
        (fun g : UA σ J => mat g⁻¹ i j) ⁻¹' (intFinE F E : Set (AE F E))) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
    rfl
  rw [e]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    ((isOpen_intFinE F E).preimage (hmat i j)).inter ((isOpen_intFinE F E).preimage ((hmat i j).comp continuous_inv))

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J _`. Take `⟨hTG, -, -, -⟩` from `GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n J`. Use `haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F`. Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _`.

Take `⟨hom⟩` from `GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)`. Use `haveI : T2Space (AE F E) := hom.isEmbedding.t2Space`. Take `⟨C, hCc, hC⟩` from `GlobalTheory.AdelicPointsUnimod.exists_compact_subring (F := F) (E := E) (GlobalTheory.AdelicPointsUnimod.intFin F) (GlobalTheory.AdelicPointsUnimod.isCompact_intFin F)`. Use `set eE : AE F E := finIdem F ⊗ₜ[F] (1 : E) with heE`. Set `C₂ : Set (AE F E)` to `(C : Set (AE F E)) ∩ {y | eE * y = y}`.

Establish `hC₂ : IsCompact C₂` using `hCc.inter_right (isClosed_eq (continuous_const.mul continuous_id) continuous_id)`. Establish `hin : ∀ x ∈ intFinE F E, infPartE F E x = 0 → x ∈ C₂`. Introduce `x hx h0`. Establish `hx' : x = eE * x` using `by conv_lhs => rw [eq_finIdem_mul_add x]`. Rewrite using `[h0, map_zero, add_zero]`.

Establish `hm` using `finIdem_mul_mem C hC hx`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hx']`. Conclude with `hm`. Conclude with `hx'.symm`.

Establish `hout : ∀ y ∈ C₂, infPartE F E y = 0`. Introduce and unpack `y ⟨-, hy⟩`. Rewrite using `[← hy]`. Conclude with `infPartE_finIdem_mul y`. Set `Cm : Set (Matrix (Fin n) (Fin n) (AE F E))` to `{M | ∀ i j, (M - 1) i j ∈ C₂}`.

Establish `hCm : IsCompact Cm`. Establish `h1 : IsCompact {X : Matrix (Fin n) (Fin n) (AE F E) | ∀ i j, X i j ∈ C₂}`. Use `isCompact_univ_pi fun _ : Fin n => isCompact_univ_pi fun _ : Fin n => hC₂` as an intermediate fact. Establish `e : {X : Fin n → Fin n → AE F E | ∀ i j, X i j ∈ C₂} = Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => C₂`. Use extensionality with `X`.

Simplify using `[Set.mem_pi]`. Rewrite `this` using `[← e]`. Conclude with `this`. Conclude with `(Homeomorph.subRight (1 : Matrix (Fin n) (Fin n) (AE F E))).isCompact_preimage.2 h1`. Establish `hK` using `GlobalTheory.ThK.UnipDom.isCompact_setOf_mat_mem F E σ n J Cm hCm`.

Set `φ : AE F E →+* Ainf F ⊗[F] E` to `(infPartE F E).toRingHom`. Establish `hφ1 : ∀ i j, φ ((1 : Matrix (Fin n) (Fin n) (AE F E)) i j) = (1 : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j`. Introduce `i j`. Rewrite using `[Matrix.one_apply, Matrix.one_apply]`. Use `split_ifs`.

Conclude with `map_one φ`. Conclude with `map_zero φ`. Establish `hfin : ∀ g : UA σ J, g ∈ finU σ J ↔ ∀ i j, φ ((mat g - 1) i j) = 0`. Introduce `g`. Rewrite using `[mem_finU]`.

Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Use `congrFun (congrFun h i) j` as an intermediate fact. Rewrite using `[Matrix.sub_apply, map_sub]`. Simplify using `only [Matrix.map_apply] at this`.

Rewrite using `[show φ (mat g i j) = _ from this, hφ1, sub_self]`. Introduce `h`. Use extensionality with `i j`. Use `h i j` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, map_sub, sub_eq_zero, hφ1]`.

Conclude with `this`. Use `⟨intLevel σ J, isOpen_intLevel σ J, ?_⟩` and prove the remaining obligations. Establish `hU : IsClosed (intLevel σ J : Set (UA σ J))` using `Subgroup.isClosed_of_isOpen _ (isOpen_intLevel σ J)`. Establish `e : ((intLevel σ J ⊓ finU σ J : Subgroup (UA σ J)) : Set (UA σ J)) = (intLevel σ J : Set (UA σ J)) ∩ {g : UA σ J | mat g ∈ Cm ∧ mat g⁻¹ ∈ Cm}`. Use extensionality with `g`.

Simplify using `only [Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hg, hf⟩`. Establish `hf' : g⁻¹ ∈ finU σ J` using `(finU σ J).inv_mem hf`. Establish `hsub : ∀ (k : UA σ J), (∀ i j, mat k i j ∈ intFinE F E) → k ∈ finU σ J → mat k ∈ Cm`.

Introduce `k hk hkf i j`. Use `hin _ ?_ ((hfin k).1 hkf i j)` and prove the remaining obligations. Rewrite using `[Matrix.sub_apply]`. Use `sub_mem (hk i j) ?_` and prove the remaining obligations. Rewrite using `[Matrix.one_apply]`.

Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`. Conclude with `⟨hg, hsub g (fun i j => (hg i j).1) hf, hsub g⁻¹ (fun i j => (hg i j).2) hf'⟩`. Introduce and unpack `⟨hg, hm, -⟩`.

Conclude with `⟨hg, (hfin g).2 fun i j => hout _ (hm i j)⟩`. Rewrite using `[e]`. Conclude with `hK.inter_left hU`.
-/
theorem exists_isOpen_isCompact_finU : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsCMExt F E σ →
    ∃ U : Subgroup (UA σ J), IsOpen (U : Set (UA σ J)) ∧
      IsCompact ((U ⊓ finU σ J : Subgroup (UA σ J)) : Set (UA σ J)) := by
  intro F E _ _ _ _ _ σ n J _
  obtain ⟨hTG, -, -, -⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n J
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨hom⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := hom.isEmbedding.t2Space
  obtain ⟨C, hCc, hC⟩ := GlobalTheory.AdelicPointsUnimod.exists_compact_subring (F := F) (E := E)
    (GlobalTheory.AdelicPointsUnimod.intFin F) (GlobalTheory.AdelicPointsUnimod.isCompact_intFin F)
  set eE : AE F E := finIdem F ⊗ₜ[F] (1 : E) with heE
  let C₂ : Set (AE F E) := (C : Set (AE F E)) ∩ {y | eE * y = y}
  have hC₂ : IsCompact C₂ := hCc.inter_right (isClosed_eq (continuous_const.mul continuous_id) continuous_id)

  have hin : ∀ x ∈ intFinE F E, infPartE F E x = 0 → x ∈ C₂ := by
    intro x hx h0
    have hx' : x = eE * x := by
      conv_lhs => rw [eq_finIdem_mul_add x]
      rw [h0, map_zero, add_zero]
    have hm := finIdem_mul_mem C hC hx
    refine ⟨?_, ?_⟩
    · rw [hx']; exact hm
    · exact hx'.symm
  have hout : ∀ y ∈ C₂, infPartE F E y = 0 := by
    rintro y ⟨-, hy⟩
    rw [← hy]
    exact infPartE_finIdem_mul y
  let Cm : Set (Matrix (Fin n) (Fin n) (AE F E)) := {M | ∀ i j, (M - 1) i j ∈ C₂}
  have hCm : IsCompact Cm := by
    have h1 : IsCompact {X : Matrix (Fin n) (Fin n) (AE F E) | ∀ i j, X i j ∈ C₂} := by
      have := isCompact_univ_pi fun _ : Fin n => isCompact_univ_pi fun _ : Fin n => hC₂
      have e : {X : Fin n → Fin n → AE F E | ∀ i j, X i j ∈ C₂} = Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => C₂ := by
        ext X
        simp [Set.mem_pi]
      rw [← e] at this
      exact this
    exact (Homeomorph.subRight (1 : Matrix (Fin n) (Fin n) (AE F E))).isCompact_preimage.2 h1
  have hK := GlobalTheory.ThK.UnipDom.isCompact_setOf_mat_mem F E σ n J Cm hCm
  let φ : AE F E →+* Ainf F ⊗[F] E := (infPartE F E).toRingHom
  have hφ1 : ∀ i j, φ ((1 : Matrix (Fin n) (Fin n) (AE F E)) i j) = (1 : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j := by
    intro i j
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact map_one φ
    · exact map_zero φ
  have hfin : ∀ g : UA σ J, g ∈ finU σ J ↔ ∀ i j, φ ((mat g - 1) i j) = 0 := by
    intro g
    rw [mem_finU]
    constructor
    · intro h i j
      have := congrFun (congrFun h i) j
      rw [Matrix.sub_apply, map_sub]
      simp only [Matrix.map_apply] at this
      rw [show φ (mat g i j) = _ from this, hφ1, sub_self]
    · intro h
      ext i j
      have := h i j
      rw [Matrix.sub_apply, map_sub, sub_eq_zero, hφ1] at this
      exact this
  refine ⟨intLevel σ J, isOpen_intLevel σ J, ?_⟩
  have hU : IsClosed (intLevel σ J : Set (UA σ J)) := Subgroup.isClosed_of_isOpen _ (isOpen_intLevel σ J)
  have e : ((intLevel σ J ⊓ finU σ J : Subgroup (UA σ J)) : Set (UA σ J)) =
      (intLevel σ J : Set (UA σ J)) ∩ {g : UA σ J | mat g ∈ Cm ∧ mat g⁻¹ ∈ Cm} := by
    ext g
    simp only [Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hg, hf⟩
      have hf' : g⁻¹ ∈ finU σ J := (finU σ J).inv_mem hf
      have hsub : ∀ (k : UA σ J), (∀ i j, mat k i j ∈ intFinE F E) → k ∈ finU σ J → mat k ∈ Cm := by
        intro k hk hkf i j
        refine hin _ ?_ ((hfin k).1 hkf i j)
        rw [Matrix.sub_apply]
        refine sub_mem (hk i j) ?_
        rw [Matrix.one_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
      exact ⟨hg, hsub g (fun i j => (hg i j).1) hf, hsub g⁻¹ (fun i j => (hg i j).2) hf'⟩
    · rintro ⟨hg, hm, -⟩
      exact ⟨hg, (hfin g).2 fun i j => hout _ (hm i j)⟩
  rw [e]
  exact hK.inter_left hU

end GlobalTheory.ThetaCplV
