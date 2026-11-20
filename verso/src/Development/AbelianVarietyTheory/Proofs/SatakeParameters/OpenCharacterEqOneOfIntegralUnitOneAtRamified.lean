import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfCongSet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubOneMemMapOfEq
open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.UnitCut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open Classical in

def cutA (z : FiniteAdeleRing (𝓞 E) E) (hz : ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (z P) ≤ 1)
    (S : Set (HeightOneSpectrum (𝓞 E))) : FiniteAdeleRing (𝓞 E) E :=
  ⟨fun P => if P ∈ S then z P else 1, Filter.Eventually.of_forall fun P => by
    by_cases h : P ∈ S
    · simp only [h, if_true]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hz P)
    · simp only [h, if_false]
      exact one_mem _⟩

open Classical in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cutA_apply (z : FiniteAdeleRing (𝓞 E) E) (hz : ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (z P) ≤ 1)
    (S : Set (HeightOneSpectrum (𝓞 E))) (P : HeightOneSpectrum (𝓞 E)) :
    cutA z hz S P = if P ∈ S then z P else 1 := by
  rfl

open GlobalTheory.Mem.Col2 (afIso mem_rInt_iff mem_suppAt_iff)

section Cut

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem apply_mul (a b : FiniteAdeleRing (𝓞 E) E) (P : HeightOneSpectrum (𝓞 E)) : (a * b) P = a P * b P := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem apply_one (P : HeightOneSpectrum (𝓞 E)) : (1 : FiniteAdeleRing (𝓞 E) E) P = 1 := rfl

/- English proof (translation)
The claim follows from `(mem_rInt_iff F E _).1 hx.1 P`.
-/
theorem int_val {x : (AfE F E)ˣ} (hx : x ∈ intU F E) (P : HeightOneSpectrum (𝓞 E)) :
    Valued.v (afIso F E (x : AfE F E) P) ≤ 1 :=
  (mem_rInt_iff F E _).1 hx.1 P

/- English proof (translation)
The claim follows from `(mem_rInt_iff F E _).1 hx.2 P`.
-/
theorem int_inv {x : (AfE F E)ˣ} (hx : x ∈ intU F E) (P : HeightOneSpectrum (𝓞 E)) :
    Valued.v (afIso F E ((x⁻¹ : (AfE F E)ˣ) : AfE F E) P) ≤ 1 :=
  (mem_rInt_iff F E _).1 hx.2 P

/- English proof (translation)
Rewrite using `[← apply_mul, ← map_mul, Units.mul_inv, map_one, apply_one]`.
-/
theorem afIso_mul_inv (x : (AfE F E)ˣ) (P : HeightOneSpectrum (𝓞 E)) :
    afIso F E (x : AfE F E) P * afIso F E ((x⁻¹ : (AfE F E)ˣ) : AfE F E) P = 1 := by
  rw [← apply_mul, ← map_mul, Units.mul_inv, map_one, apply_one]

/- English proof (translation)
The claim follows from `Units.ext ((afIso F E).injective (FiniteAdeleRing.ext _ h))`.
-/
theorem eq_of_afIso {y y' : (AfE F E)ˣ} (h : ∀ P, afIso F E (y : AfE F E) P = afIso F E (y' : AfE F E) P) : y = y' :=
  Units.ext ((afIso F E).injective (FiniteAdeleRing.ext _ h))

def cutU (x : (AfE F E)ˣ) (hx : x ∈ intU F E) (S : Set (HeightOneSpectrum (𝓞 E))) : (AfE F E)ˣ where
  val := (afIso F E).symm (cutA (afIso F E (x : AfE F E)) (int_val hx) S)
  inv := (afIso F E).symm (cutA (afIso F E ((x⁻¹ : (AfE F E)ˣ) : AfE F E)) (int_inv hx) S)
  val_inv := by
    rw [← map_mul, (afIso F E).symm_apply_eq, map_one]
    refine FiniteAdeleRing.ext _ fun P => ?_
    rw [apply_mul, cutA_apply, cutA_apply, apply_one]
    split_ifs
    · exact afIso_mul_inv x P
    · exact one_mul 1
  inv_val := by
    rw [← map_mul, (afIso F E).symm_apply_eq, map_one]
    refine FiniteAdeleRing.ext _ fun P => ?_
    rw [apply_mul, cutA_apply, cutA_apply, apply_one]
    split_ifs
    · rw [mul_comm]; exact afIso_mul_inv x P
    · exact one_mul 1

open Classical in
/- English proof (translation)
Use `show afIso F E ((afIso F E).symm _) P = _`. Rewrite using `[RingEquiv.apply_symm_apply, cutA_apply]`.
-/
theorem afIso_cutU (x : (AfE F E)ˣ) (hx : x ∈ intU F E) (S : Set (HeightOneSpectrum (𝓞 E)))
    (P : HeightOneSpectrum (𝓞 E)) :
    afIso F E (cutU x hx S : AfE F E) P = if P ∈ S then afIso F E (x : AfE F E) P else 1 := by
  show afIso F E ((afIso F E).symm _) P = _
  rw [RingEquiv.apply_symm_apply, cutA_apply]

/- English proof (translation)
Use `show Valued.v (afIso F E ((afIso F E).symm _) P) ≤ 1`. Rewrite using `[RingEquiv.apply_symm_apply, cutA_apply]`. Use `split_ifs`. Conclude with `int_inv hx P`. Rewrite using `[map_one]`.
-/
theorem afIso_cutU_inv (x : (AfE F E)ˣ) (hx : x ∈ intU F E) (S : Set (HeightOneSpectrum (𝓞 E)))
    (P : HeightOneSpectrum (𝓞 E)) : Valued.v (afIso F E (((cutU x hx S)⁻¹ : (AfE F E)ˣ) : AfE F E) P) ≤ 1 := by
  show Valued.v (afIso F E ((afIso F E).symm _) P) ≤ 1
  rw [RingEquiv.apply_symm_apply, cutA_apply]
  split_ifs
  · exact int_inv hx P
  · rw [map_one]

/- English proof (translation)
Use `⟨(mem_rInt_iff F E _).2 fun P => ?_, (mem_rInt_iff F E _).2 fun P => afIso_cutU_inv x hx S P⟩` and prove the remaining obligations. Use `show Valued.v (afIso F E (cutU x hx S : AfE F E) P) ≤ 1`. Rewrite using `[afIso_cutU]`. Use `split_ifs`. Conclude with `int_val hx P`.

Rewrite using `[map_one]`.
-/
theorem cutU_mem_intU (x : (AfE F E)ˣ) (hx : x ∈ intU F E) (S : Set (HeightOneSpectrum (𝓞 E))) :
    cutU x hx S ∈ intU F E := by
  refine ⟨(mem_rInt_iff F E _).2 fun P => ?_, (mem_rInt_iff F E _).2 fun P => afIso_cutU_inv x hx S P⟩
  show Valued.v (afIso F E (cutU x hx S : AfE F E) P) ≤ 1
  rw [afIso_cutU]
  split_ifs
  · exact int_val hx P
  · rw [map_one]

/- English proof (translation)
Use `eq_of_afIso fun P => ?_` and prove the remaining obligations. Rewrite using `[Units.val_mul, map_mul, apply_mul, afIso_cutU, afIso_cutU, afIso_cutU]`. Distinguish the cases in `h : P ∈ S`. Establish `h' : P ∉ S'` using `Set.disjoint_left.1 hd h`. Simplify using `[h, h']`.

Apply the tactic sequence `by_cases h' : P ∈ S' <;> simp [h, h']`.
-/
theorem cutU_union (x : (AfE F E)ˣ) (hx : x ∈ intU F E) {S S' : Set (HeightOneSpectrum (𝓞 E))} (hd : Disjoint S S') :
    cutU x hx (S ∪ S') = cutU x hx S * cutU x hx S' := by
  refine eq_of_afIso fun P => ?_
  rw [Units.val_mul, map_mul, apply_mul, afIso_cutU, afIso_cutU, afIso_cutU]
  by_cases h : P ∈ S
  · have h' : P ∉ S' := Set.disjoint_left.1 hd h
    simp [h, h']
  · by_cases h' : P ∈ S' <;> simp [h, h']

/- English proof (translation)
The claim follows from `eq_of_afIso fun P => by rw [afIso_cutU]; simp`.
-/
theorem cutU_univ (x : (AfE F E)ˣ) (hx : x ∈ intU F E) : cutU x hx Set.univ = x :=
  eq_of_afIso fun P => by rw [afIso_cutU]; simp

/- English proof (translation)
The claim follows from `eq_of_afIso fun P => by rw [afIso_cutU, Units.val_one, map_one, apply_one]; simp`.
-/
theorem cutU_empty (x : (AfE F E)ˣ) (hx : x ∈ intU F E) : cutU x hx ∅ = 1 :=
  eq_of_afIso fun P => by rw [afIso_cutU, Units.val_one, map_one, apply_one]; simp

/- English proof (translation)
Assemble the required witnesses or components as `⟨cutU_mem_intU x hx _, (mem_suppAt_iff F E v _).2 fun P hP => by rw [afIso_cutU] simp [hP]⟩`.
-/
theorem cutU_mem_inertAt (x : (AfE F E)ˣ) (hx : x ∈ intU F E) (v : HeightOneSpectrum (𝓞 F)) :
    cutU x hx {P | P.under (𝓞 F) = v} ∈ inertAt E v :=
  ⟨cutU_mem_intU x hx _, (mem_suppAt_iff F E v _).2 fun P hP => by
    rw [afIso_cutU]
    simp [hP]⟩

/- English proof (translation)
Introduce `h'` and use `h (by show (N : 𝓞 F) ∈ P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) rw [Ideal.mem_comap, map_natCast] exact h')`.
-/
theorem natCast_notMem_of_under {P : HeightOneSpectrum (𝓞 E)} {N : ℕ} (h : (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal) :
    (N : 𝓞 E) ∉ P.asIdeal := fun h' => h (by
  show (N : 𝓞 F) ∈ P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
  rw [Ideal.mem_comap, map_natCast]
  exact h')

/- English proof (translation)
Rewrite using `[GlobalTheory.Mem.ReadEx.mem_congN_iff]`. Use `⟨cutU_mem_intU x hx _, (afIso F E).symm (algebraMap E _ (N : E)⁻¹ * (afIso F E (cutU x hx {P | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal} : AfE F E) - 1)), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_rInt_iff, RingEquiv.apply_symm_apply]`. Introduce `P`. Use `show Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) (N : E)⁻¹) P * (afIso F E (cutU x hx {P | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal} : AfE F E) P - 1)) ≤ 1`.

Rewrite using `[afIso_cutU]`. Distinguish the cases in `h : (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal`. Establish `h3 : Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) (N : E)⁻¹) P) = 1`. Express the relevant statement in the definitionally equal form `Valued.v (algebraMap E (P.adicCompletion E) (N : E)⁻¹) = 1`. Rewrite using `[map_inv₀, map_inv₀, ← map_natCast (algebraMap (𝓞 E) E), GlobalTheory.TwistPlaces.valued_int, GlobalTheory.TwistPlaces.intValuation_eq_one P (natCast_notMem_of_under h), inv_one]`.

Establish `h4 : P ∈ {P : HeightOneSpectrum (𝓞 E) | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal}` using `h`. Rewrite using `[if_pos h4, map_mul, h3, one_mul]`. Conclude with `Valuation.map_sub_le _ (int_val hx P) (by rw [map_one])`. Establish `h4 : P ∉ {P : HeightOneSpectrum (𝓞 E) | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal}` using `h`. Rewrite using `[if_neg h4, sub_self, mul_zero, map_zero]`.

Conclude with `zero_le'`. Apply `(afIso F E).injective` to reduce the goal to its premises. Rewrite using `[map_mul, RingEquiv.apply_symm_apply, map_natCast, GlobalTheory.Mem.ReadEx.inv_mul_mul_nat hN, map_sub, map_one]`.
-/
theorem cutU_mem_congN (x : (AfE F E)ˣ) (hx : x ∈ intU F E) {N : ℕ} (hN : 0 < N) :
    cutU x hx {P | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal} ∈ congN F E N := by
  rw [GlobalTheory.Mem.ReadEx.mem_congN_iff]
  refine ⟨cutU_mem_intU x hx _, (afIso F E).symm (algebraMap E _ (N : E)⁻¹ *
    (afIso F E (cutU x hx {P | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal} : AfE F E) - 1)), ?_, ?_⟩
  · rw [mem_rInt_iff, RingEquiv.apply_symm_apply]
    intro P
    show Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) (N : E)⁻¹) P *
      (afIso F E (cutU x hx {P | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal} : AfE F E) P - 1)) ≤ 1
    rw [afIso_cutU]
    by_cases h : (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal
    · have h3 : Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) (N : E)⁻¹) P) = 1 := by
        change Valued.v (algebraMap E (P.adicCompletion E) (N : E)⁻¹) = 1
        rw [map_inv₀, map_inv₀, ← map_natCast (algebraMap (𝓞 E) E), GlobalTheory.TwistPlaces.valued_int,
          GlobalTheory.TwistPlaces.intValuation_eq_one P (natCast_notMem_of_under h), inv_one]
      have h4 : P ∈ {P : HeightOneSpectrum (𝓞 E) | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal} := h
      rw [if_pos h4, map_mul, h3, one_mul]
      exact Valuation.map_sub_le _ (int_val hx P) (by rw [map_one])
    · have h4 : P ∉ {P : HeightOneSpectrum (𝓞 E) | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal} := h
      rw [if_neg h4, sub_self, mul_zero, map_zero]
      exact zero_le'
  · apply (afIso F E).injective
    rw [map_mul, RingEquiv.apply_symm_apply, map_natCast, GlobalTheory.Mem.ReadEx.inv_mul_mul_nat hN, map_sub, map_one]

end Cut

/- English proof (translation)
Introduce `F E L _ _ _ _ _ _ _ ξ hξ _ x hx h1`. Take `⟨N, hN, hk⟩` from `hξ`. Establish `h0 : Ideal.span {(N : 𝓞 F)} ≠ ⊥` using `by simpa using hN.ne'`. Establish `hT : {v : HeightOneSpectrum (𝓞 F) | (N : 𝓞 F) ∈ v.asIdeal}.Finite` using `(Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 hv`. Establish `key : ∀ T : Finset (HeightOneSpectrum (𝓞 F)), ξ (cutU x hx {P | P.under (𝓞 F) ∈ T}) = 1`.

Introduce `T`. Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty`. Establish `e : {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ (∅ : Finset (HeightOneSpectrum (𝓞 F)))} = ∅`. Use extensionality with `P`.

Simplify using the standard rewrite rules. Rewrite using `[e, cutU_empty, map_one]`. Consider the case `insert v T hv ih`. Establish `e : {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ insert v T} = {P | P.under (𝓞 F) = v} ∪ {P | P.under (𝓞 F) ∈ T}`. Use extensionality with `P`.

Simplify using the standard rewrite rules. Establish `hd : Disjoint {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) = v} {P | P.under (𝓞 F) ∈ T}` using `Set.disjoint_left.2 fun P h h' => hv (by`. Establish `h2 : P.under (𝓞 F) = v` using `h`. Establish `h3 : P.under (𝓞 F) ∈ T` using `h'`. Rewrite using `[← h2]`.

Conclude with `h3)`. Rewrite using `[e, cutU_union x hx hd, map_mul, ih, mul_one]`. Distinguish the cases in `hq : v ∈ Qprime ξ`. Establish `e1 : cutU x hx {P | P.under (𝓞 F) = v} = 1` using `eq_of_afIso fun P => by`. Rewrite using `[afIso_cutU, Units.val_one, map_one, apply_one]`.

Use `split_ifs with hP`. Establish `h2 : P.under (𝓞 F) = v` using `hP`. Conclude with `h1 P (by rw [h2]; exact hq)`. Both sides reduce to the same expression. Rewrite using `[e1, map_one]`.

Establish `hle : inertAt E v ≤ ξ.ker`. Assume the negation of the conclusion as `h`. Conclude with `hq h`. Conclude with `MonoidHom.mem_ker.1 (hle (cutU_mem_inertAt x hx v))`. Establish `hd : Disjoint {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ hT.toFinset} {P | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal}` using `Set.disjoint_left.2 fun P h h' => h' (by simpa using h)`.

Establish `eu : {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ hT.toFinset} ∪ {P | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal} = Set.univ`. Use extensionality with `P`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, Set.Finite.mem_toFinset, Set.mem_univ, iff_true]`. Conclude with `em _`. Establish `e : cutU x hx {P | P.under (𝓞 F) ∈ hT.toFinset} * cutU x hx {P | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal} = x`.

Rewrite using `[← cutU_union x hx hd, eu, cutU_univ]`. Establish `e2` using `congrArg ξ e`. Rewrite `e2` using `[map_mul, key, one_mul, MonoidHom.mem_ker.1 (hk (cutU_mem_congN x hx hN))]`. Conclude with `e2.symm`.
-/
theorem map_eq_one_of_one_at_ramified : ∀ (F E L : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Field L] (σ : L →+* ℂ) (ξ : Chr F E L), ξ ∈ openChr F E L → (ratId F E).range ≤ ξ.ker → ∀ x ∈ intU F E,
    (∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) ∈ Qprime ξ → GlobalTheory.Mem.Col2.afIso F E (x : AfE F E) P = 1) → ξ x = 1 := by
  intro F E L _ _ _ _ _ _ _ ξ hξ _ x hx h1
  classical
  obtain ⟨N, hN, hk⟩ := hξ
  have h0 : Ideal.span {(N : 𝓞 F)} ≠ ⊥ := by simpa using hN.ne'
  have hT : {v : HeightOneSpectrum (𝓞 F) | (N : 𝓞 F) ∈ v.asIdeal}.Finite :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 hv
  have key : ∀ T : Finset (HeightOneSpectrum (𝓞 F)), ξ (cutU x hx {P | P.under (𝓞 F) ∈ T}) = 1 := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      have e : {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ (∅ : Finset (HeightOneSpectrum (𝓞 F)))} = ∅ := by
        ext P
        simp
      rw [e, cutU_empty, map_one]
    | insert v T hv ih =>
      have e : {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ insert v T} =
          {P | P.under (𝓞 F) = v} ∪ {P | P.under (𝓞 F) ∈ T} := by
        ext P
        simp
      have hd : Disjoint {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) = v} {P | P.under (𝓞 F) ∈ T} :=
        Set.disjoint_left.2 fun P h h' => hv (by
          have h2 : P.under (𝓞 F) = v := h
          have h3 : P.under (𝓞 F) ∈ T := h'
          rw [← h2]
          exact h3)
      rw [e, cutU_union x hx hd, map_mul, ih, mul_one]
      by_cases hq : v ∈ Qprime ξ
      · have e1 : cutU x hx {P | P.under (𝓞 F) = v} = 1 := eq_of_afIso fun P => by
          rw [afIso_cutU, Units.val_one, map_one, apply_one]
          split_ifs with hP
          · have h2 : P.under (𝓞 F) = v := hP
            exact h1 P (by rw [h2]; exact hq)
          · rfl
        rw [e1, map_one]
      · have hle : inertAt E v ≤ ξ.ker := by
          by_contra h
          exact hq h
        exact MonoidHom.mem_ker.1 (hle (cutU_mem_inertAt x hx v))
  have hd : Disjoint {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ hT.toFinset}
      {P | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal} :=
    Set.disjoint_left.2 fun P h h' => h' (by simpa using h)
  have eu : {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ hT.toFinset} ∪
      {P | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal} = Set.univ := by
    ext P
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.Finite.mem_toFinset, Set.mem_univ, iff_true]
    exact em _
  have e : cutU x hx {P | P.under (𝓞 F) ∈ hT.toFinset} * cutU x hx {P | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal} = x := by
    rw [← cutU_union x hx hd, eu, cutU_univ]
  have e2 := congrArg ξ e
  rw [map_mul, key, one_mul, MonoidHom.mem_ker.1 (hk (cutU_mem_congN x hx hN))] at e2
  exact e2.symm

end GlobalTheory.UnitCut
