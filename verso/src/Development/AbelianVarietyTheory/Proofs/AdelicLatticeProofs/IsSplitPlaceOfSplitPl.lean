import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.SupportedAtSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate

noncomputable section

namespace GlobalTheory.UnRep.Compare

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evalAt_apply (v : HeightOneSpectrum (𝓞 F)) (a : FiniteAdeleRing (𝓞 F) F) : evalAt v a = a v := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem loc_tmul (v : HeightOneSpectrum (𝓞 F)) (a : FiniteAdeleRing (𝓞 F) F) (x : E) :
    loc E v (a ⊗ₜ[F] x) = a v ⊗ₜ[F] x := rfl

/- English proof (translation)
Set `b` to `Module.Basis.ofVectorSpace F E`. Establish `key : ∀ (v : HeightOneSpectrum (𝓞 F)) (i) (y : RA F E), (Algebra.TensorProduct.basis (FiniteAdeleRing (𝓞 F) F) b).repr y i v = (Algebra.TensorProduct.basis (v.adicCompletion F) b).repr (loc E v y) i`. Introduce `v i y`. Rewrite using `[← evalAt_apply]`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a e`. Rewrite using `[loc_tmul, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul]`. Simplify using `only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes, evalAt_apply v a]`. Consider the case `add s t hs ht => simp only [map_add, Finsupp.add_apply, hs, ht]`.

Apply `(Algebra.TensorProduct.basis (FiniteAdeleRing (𝓞 F) F) b).repr.injective` to reduce the goal to its premises. Use extensionality with `i : 1`. Use `DFunLike.ext _ _ fun v => ?_` and prove the remaining obligations. Rewrite using `[key, h, map_zero, map_zero]`. Both sides reduce to the same expression.
-/
theorem eq_zero_of_loc {x : RA F E} (h : ∀ v, loc E v x = 0) : x = 0 := by
  let b := Module.Basis.ofVectorSpace F E
  have key : ∀ (v : HeightOneSpectrum (𝓞 F)) (i) (y : RA F E),
      (Algebra.TensorProduct.basis (FiniteAdeleRing (𝓞 F) F) b).repr y i v =
        (Algebra.TensorProduct.basis (v.adicCompletion F) b).repr (loc E v y) i := by
    intro v i y
    rw [← evalAt_apply]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      rw [loc_tmul, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul]
      simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes,
        evalAt_apply v a]
    | add s t hs ht => simp only [map_add, Finsupp.add_apply, hs, ht]
  apply (Algebra.TensorProduct.basis (FiniteAdeleRing (𝓞 F) F) b).repr.injective
  ext i : 1
  refine DFunLike.ext _ _ fun v => ?_
  rw [key, h, map_zero, map_zero]
  rfl

/- English proof (translation)
The claim follows from `sub_eq_zero.1 (eq_zero_of_loc fun v => by rw [map_sub, h, sub_self])`.
-/
theorem eq_of_loc {x y : RA F E} (h : ∀ v, loc E v x = loc E v y) : x = y :=
  sub_eq_zero.1 (eq_zero_of_loc fun v => by rw [map_sub, h, sub_self])

open Classical in

def ind (S : Set (HeightOneSpectrum (𝓞 F))) : FiniteAdeleRing (𝓞 F) F :=
  ⟨fun w => if w ∈ S then 1 else 0, Filter.Eventually.of_forall fun w => by
    by_cases h : w ∈ S
    · simp only [if_pos h]; exact one_mem _
    · simp only [if_neg h]; exact zero_mem _⟩

/- English proof (translation)
The claim follows from `if_pos h`.
-/
theorem ind_pos {S : Set (HeightOneSpectrum (𝓞 F))} {w} (h : w ∈ S) : ind S w = 1 := if_pos h

/- English proof (translation)
The claim follows from `if_neg h`.
-/
theorem ind_neg {S : Set (HeightOneSpectrum (𝓞 F))} {w} (h : w ∉ S) : ind S w = 0 := if_neg h

/- English proof (translation)
Distinguish the cases in `h : w ∈ S`. Rewrite using `[ind_pos h]`. Conclude with `one_mem _`. Rewrite using `[ind_neg h]`. Conclude with `zero_mem _`.
-/
theorem ind_int (S : Set (HeightOneSpectrum (𝓞 F))) (w) : ind S w ∈ w.adicCompletionIntegers F := by
  by_cases h : w ∈ S
  · rw [ind_pos h]; exact one_mem _
  · rw [ind_neg h]; exact zero_mem _

/- English proof (translation)
Rewrite using `[loc_tmul, ind_pos h]`. Both sides reduce to the same expression.
-/
theorem loc_ind_pos {S : Set (HeightOneSpectrum (𝓞 F))} {w} (h : w ∈ S) :
    loc E w (ind S ⊗ₜ[F] (1 : E)) = 1 := by rw [loc_tmul, ind_pos h]; rfl

/- English proof (translation)
Rewrite using `[loc_tmul, ind_neg h, TensorProduct.zero_tmul]`.
-/
theorem loc_ind_neg {S : Set (HeightOneSpectrum (𝓞 F))} {w} (h : w ∉ S) :
    loc E w (ind S ⊗ₜ[F] (1 : E)) = 0 := by rw [loc_tmul, ind_neg h, TensorProduct.zero_tmul]

/- English proof (translation)
Establish `hm' : (m : F) ≠ 0` using `by exact_mod_cast hm`. Use `⟨ind S * algebraMap F _ (m : F)⁻¹, fun v => ?_, ?_⟩` and prove the remaining obligations. Establish `: (ind S * algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F)⁻¹) v = ind S v * (((m : F)⁻¹ : F) : v.adicCompletion F)` using `rfl`. Rewrite using `[this]`. Distinguish the cases in `hv : v ∈ S`.

Rewrite using `[ind_pos hv, one_mul, HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀]`. Establish `h1` using `(HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) v).2 (hS v hv)`. Rewrite `h1` using `[map_natCast]`. Rewrite using `[h1, inv_one]`. Rewrite using `[ind_neg hv, zero_mul]`.

Conclude with `zero_mem _`. Rewrite using `[← nsmul_eq_mul, TensorProduct.smul_tmul', nsmul_eq_mul, ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) m, mul_left_comm, ← map_mul, mul_inv_cancel₀ hm', map_one, mul_one]`.
-/
theorem exists_inv (m : ℕ) (hm : m ≠ 0) (S : Set (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∈ S, (m : 𝓞 F) ∉ v.asIdeal) :
    ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧
      (m : RA F E) * (a ⊗ₜ[F] (1 : E)) = ind S ⊗ₜ[F] (1 : E) := by
  have hm' : (m : F) ≠ 0 := by exact_mod_cast hm
  refine ⟨ind S * algebraMap F _ (m : F)⁻¹, fun v => ?_, ?_⟩
  · have : (ind S * algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F)⁻¹) v
        = ind S v * (((m : F)⁻¹ : F) : v.adicCompletion F) := rfl
    rw [this]
    by_cases hv : v ∈ S
    · rw [ind_pos hv, one_mul, HeightOneSpectrum.mem_adicCompletionIntegers,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀]
      have h1 := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) v).2 (hS v hv)
      rw [map_natCast] at h1
      rw [h1, inv_one]
    · rw [ind_neg hv, zero_mul]; exact zero_mem _
  · rw [← nsmul_eq_mul, TensorProduct.smul_tmul', nsmul_eq_mul,
      ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) m, mul_left_comm, ← map_mul,
      mul_inv_cancel₀ hm', map_one, mul_one]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem isUnA_iff (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (g : Matrix (Fin n) (Fin n) (RA F E)) : IsUnA c G g ↔ IsUnitaryA c G g := Iff.rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fm_eq_ratM {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) : fm F γ = ratM F γ := rfl

/- English proof (translation)
Take `⟨P, hP, hPv, a, ha, b, hb, hbP⟩` from `h`. Set `σ : 𝓞 E ≃+* 𝓞 E` to `RingOfIntegers.mapRingEquiv c.toRingEquiv`. Establish `hσ : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = c x` using `fun _ => rfl`. Use `⟨P, P.comap σ, fun h => hbP ?_, hP, inferInstance, hPv, ?_⟩` and prove the remaining obligations. Rewrite `ha` using `[h, Ideal.mem_comap]`.

Rewrite using `[show b = σ a from Subtype.ext hb]` and apply the resulting hypothesis. Rewrite using `[← hPv]`. Use extensionality with `x`. Establish `: σ (algebraMap (𝓞 F) (𝓞 E) x) = algebraMap (𝓞 F) (𝓞 E) x` using `Subtype.ext (c.commutes (x : F))`. Simplify using `only [Ideal.mem_comap, this]`.
-/
theorem isSplitPlace_of_splitPl (c : E ≃ₐ[F] E) {v : HeightOneSpectrum (𝓞 F)} (h : SplitPl c v) :
    IsSplitPlace E v := by
  obtain ⟨P, hP, hPv, a, ha, b, hb, hbP⟩ := h
  let σ : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv c.toRingEquiv
  have hσ : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = c x := fun _ => rfl
  refine ⟨P, P.comap σ, fun h => hbP ?_, hP, inferInstance, hPv, ?_⟩
  · rw [h, Ideal.mem_comap] at ha
    rwa [show b = σ a from Subtype.ext hb]
  · rw [← hPv]
    ext x
    have : σ (algebraMap (𝓞 F) (𝓞 E) x) = algebraMap (𝓞 F) (𝓞 E) x :=
      Subtype.ext (c.commutes (x : F))
    simp only [Ideal.mem_comap, this]

/- English proof (translation)
Use `haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩`. Establish `hcard : Nat.card (E ≃ₐ[F] E) = 2` using `by rw [IsGalois.card_aut_eq_finrank, h2]`. Take `⟨y, -, hy⟩` from `(Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard`. Distinguish the cases in `h : σ = 1`. Conclude with `Or.inl h`.

Conclude with `Or.inr ((hy σ h).trans (hy c hc).symm)`.
-/
theorem aut_eq (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (σ : E ≃ₐ[F] E) :
    σ = 1 ∨ σ = c := by
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
  by_cases h : σ = 1
  · exact Or.inl h
  · exact Or.inr ((hy σ h).trans (hy c hc).symm)

/- English proof (translation)
Break down `aut_eq c h2 hc (c * c) with h | h` into its components or cases. Conclude with `DFunLike.congr_fun h x`. Conclude with `absurd (mul_eq_left.1 h) hc`.
-/
theorem conj_conj (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (x : E) : c (c x) = x := by
  rcases aut_eq c h2 hc (c * c) with h | h
  · exact DFunLike.congr_fun h x
  · exact absurd (mul_eq_left.1 h) hc

/- English proof (translation)
Use `haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩`. Take `⟨a, haP, haQ⟩` from `Set.not_subset.1 hPQ`. Set `σ : 𝓞 E ≃+* 𝓞 E` to `RingOfIntegers.mapRingEquiv c.toRingEquiv`. Establish `hσ : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = c x` using `fun _ => rfl`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ((a * σ a : 𝓞 E) : E) ∈ Set.range (algebraMap F E) := by`.

Rewrite using `[IsGalois.mem_range_algebraMap_iff_fixed]`. Introduce `f`. Break down `aut_eq c h2 hc f with rfl | rfl` into its components or cases. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `f ((a : E) * f a) = (a : E) * f a`.

Rewrite using `[map_mul, conj_conj f h2 hc, mul_comm]`. Establish `hint : IsIntegral ℤ m`. Rewrite using `[← isIntegral_algebraMap_iff (B := E) (algebraMap F E).injective, hm]`. Conclude with `(a * σ a).2`. Take `⟨m', hm'⟩ : ∃ m' : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) m' = a * σ a` from `⟨⟨m, hint⟩, Subtype.ext hm⟩`.

Establish `h1 : a * σ a ∈ Q`. Rewrite using `[← hm', ← Ideal.mem_comap, ← h, Ideal.mem_comap, hm']`. Conclude with `P.mul_mem_right _ haP`. Conclude with `⟨σ a, (hQ.mem_or_mem h1).resolve_left haQ, a, (conj_conj c h2 hc _).symm, haQ⟩`.
-/
theorem moved_of_not_le (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    {P Q : Ideal (𝓞 E)} (hQ : Q.IsPrime)
    (h : P.comap (algebraMap (𝓞 F) (𝓞 E)) = Q.comap (algebraMap (𝓞 F) (𝓞 E))) (hPQ : ¬ P ≤ Q) :
    Moved c Q := by
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  obtain ⟨a, haP, haQ⟩ := Set.not_subset.1 hPQ
  let σ : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv c.toRingEquiv
  have hσ : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = c x := fun _ => rfl
  obtain ⟨m, hm⟩ : ((a * σ a : 𝓞 E) : E) ∈ Set.range (algebraMap F E) := by
    rw [IsGalois.mem_range_algebraMap_iff_fixed]
    intro f
    rcases aut_eq c h2 hc f with rfl | rfl
    · rfl
    · change f ((a : E) * f a) = (a : E) * f a
      rw [map_mul, conj_conj f h2 hc, mul_comm]
  have hint : IsIntegral ℤ m := by
    rw [← isIntegral_algebraMap_iff (B := E) (algebraMap F E).injective, hm]
    exact (a * σ a).2
  obtain ⟨m', hm'⟩ : ∃ m' : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) m' = a * σ a := ⟨⟨m, hint⟩, Subtype.ext hm⟩
  have h1 : a * σ a ∈ Q := by
    rw [← hm', ← Ideal.mem_comap, ← h, Ideal.mem_comap, hm']
    exact P.mul_mem_right _ haP
  exact ⟨σ a, (hQ.mem_or_mem h1).resolve_left haQ, a, (conj_conj c h2 hc _).symm, haQ⟩

/- English proof (translation)
Use `⟨isSplitPlace_of_splitPl c, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨w, w', hne, hw, hw', h, h'⟩`. Distinguish the cases in `hle : w ≤ w'`. Conclude with `⟨w, hw, h, moved_of_not_le c h2 hc hw (h'.trans h.symm) fun h => hne (le_antisymm hle h)⟩`. Conclude with `⟨w', hw', h', moved_of_not_le c h2 hc hw' (h.trans h'.symm) hle⟩`.
-/
theorem splitPl_iff (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (v : HeightOneSpectrum (𝓞 F)) : SplitPl c v ↔ IsSplitPlace E v := by
  refine ⟨isSplitPlace_of_splitPl c, ?_⟩
  rintro ⟨w, w', hne, hw, hw', h, h'⟩
  by_cases hle : w ≤ w'
  · exact ⟨w, hw, h, moved_of_not_le c h2 hc hw (h'.trans h.symm) fun h => hne (le_antisymm hle h)⟩
  · exact ⟨w', hw', h', moved_of_not_le c h2 hc hw' (h.trans h'.symm) hle⟩

/- English proof (translation)
Establish `hone : ∀ v : HeightOneSpectrum (𝓞 F), h.map (loc E v) = 1 ↔ ∀ i j, loc E v ((h - 1) i j) = 0`. Introduce `v`. Rewrite using `[← Matrix.map_one (loc E v) (map_zero _) (map_one _), ← Matrix.ext_iff]`. Simplify using `only [Matrix.map_apply, Matrix.sub_apply, map_sub, sub_eq_zero]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨e, -, hfin, hp, he⟩`. Use `⟨hfin.toFinset, fun v hv => hp v (hfin.mem_toFinset.1 hv), fun v hv => (hone v).2 fun i j => ?_⟩` and prove the remaining obligations. Establish `h0 : e v = 0`. Assume the negation of the conclusion as `h0`. Conclude with `hv (hfin.mem_toFinset.2 h0)`.

Rewrite using `[← he, Matrix.smul_apply, smul_eq_mul, map_mul, loc_tmul, h0, TensorProduct.zero_tmul, zero_mul]`. Introduce and unpack `⟨T, hp, hT⟩`. Establish `hs : ∀ v, ind (T : Set (HeightOneSpectrum (𝓞 F))) v ≠ 0 → v ∈ T` using `fun v hv => by`. Assume the negation of the conclusion as `h0`. Conclude with `hv (ind_neg h0)`.

Use `⟨ind T, ?_, T.finite_toSet.subset hs, fun v hv => hp v (hs v hv), ?_⟩` and prove the remaining obligations. Use `DFunLike.ext _ _ fun v => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ind _ v * ind _ v = ind _ v`. Distinguish the cases in `hv : v ∈ (T : Set (HeightOneSpectrum (𝓞 F)))`. Rewrite using `[ind_pos hv, one_mul]`.

Rewrite using `[ind_neg hv, zero_mul]`. Use extensionality with `i j`. Use `eq_of_loc fun v => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_apply, smul_eq_mul, map_mul]`. Distinguish the cases in `hv : v ∈ (T : Set (HeightOneSpectrum (𝓞 F)))`.

Rewrite using `[loc_ind_pos hv, one_mul]`. Rewrite using `[(hone v).1 (hT v hv), mul_zero]`.
-/
theorem support_iff (p : HeightOneSpectrum (𝓞 F) → Prop) {n : ℕ} (h : Matrix (Fin n) (Fin n) (RA F E)) :
    (∃ e : FiniteAdeleRing (𝓞 F) F, e * e = e ∧ {v | e v ≠ 0}.Finite ∧
      (∀ v, e v ≠ 0 → p v) ∧ (e ⊗ₜ[F] (1 : E)) • (h - 1) = h - 1) ↔
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), (∀ v ∈ T, p v) ∧ ∀ v ∉ T, h.map (loc E v) = 1 := by
  have hone : ∀ v : HeightOneSpectrum (𝓞 F), h.map (loc E v) = 1 ↔ ∀ i j, loc E v ((h - 1) i j) = 0 := by
    intro v
    rw [← Matrix.map_one (loc E v) (map_zero _) (map_one _), ← Matrix.ext_iff]
    simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, sub_eq_zero]
  constructor
  · rintro ⟨e, -, hfin, hp, he⟩
    refine ⟨hfin.toFinset, fun v hv => hp v (hfin.mem_toFinset.1 hv), fun v hv => (hone v).2 fun i j => ?_⟩
    have h0 : e v = 0 := by
      by_contra h0
      exact hv (hfin.mem_toFinset.2 h0)
    rw [← he, Matrix.smul_apply, smul_eq_mul, map_mul, loc_tmul, h0, TensorProduct.zero_tmul, zero_mul]
  · rintro ⟨T, hp, hT⟩
    have hs : ∀ v, ind (T : Set (HeightOneSpectrum (𝓞 F))) v ≠ 0 → v ∈ T := fun v hv => by
      by_contra h0
      exact hv (ind_neg h0)
    refine ⟨ind T, ?_, T.finite_toSet.subset hs, fun v hv => hp v (hs v hv), ?_⟩
    · refine DFunLike.ext _ _ fun v => ?_
      change ind _ v * ind _ v = ind _ v
      by_cases hv : v ∈ (T : Set (HeightOneSpectrum (𝓞 F)))
      · rw [ind_pos hv, one_mul]
      · rw [ind_neg hv, zero_mul]
    · ext i j
      refine eq_of_loc fun v => ?_
      rw [Matrix.smul_apply, smul_eq_mul, map_mul]
      by_cases hv : v ∈ (T : Set (HeightOneSpectrum (𝓞 F)))
      · rw [loc_ind_pos hv, one_mul]
      · rw [(hone v).1 (hT v hv), mul_zero]

/- English proof (translation)
Rewrite using `[SuppSplit, support_iff (fun v => SplitPl c v ∧ (N : 𝓞 F) ∉ v.asIdeal), SupportedAtSplit]`. Simplify using `only [splitPl_iff c h2 hc]`.
-/
theorem suppSplit_iff (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) {n : ℕ} (N : ℕ)
    (h : Matrix (Fin n) (Fin n) (RA F E)) : SuppSplit c N h ↔ SupportedAtSplit N h := by
  rw [SuppSplit, support_iff (fun v => SplitPl c v ∧ (N : 𝓞 F) ∉ v.asIdeal), SupportedAtSplit]
  simp only [splitPl_iff c h2 hc]

/- English proof (translation)
Introduce `h` and use `by obtain ⟨p, q, hpq⟩ : IsCoprime (t : 𝓞 F) (N : 𝓞 F) := Nat.Coprime.cast ht exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hpq ▸ add_mem (v.asIdeal.mul_mem_left _ h) (v.asIdeal.mul_mem_left _ hv)))`.
-/
theorem notMem_of_coprime {t N : ℕ} (ht : t.Coprime N) {v : HeightOneSpectrum (𝓞 F)}
    (hv : (N : 𝓞 F) ∈ v.asIdeal) : (t : 𝓞 F) ∉ v.asIdeal := fun h => by
  obtain ⟨p, q, hpq⟩ : IsCoprime (t : 𝓞 F) (N : 𝓞 F) := Nat.Coprime.cast ht
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hpq ▸ add_mem (v.asIdeal.mul_mem_left _ h) (v.asIdeal.mul_mem_left _ hv)))

/- English proof (translation)
Take `⟨t, ht, h⟩` from `h`. Introduce `v hv z hz`. Take `⟨w, hw, e⟩` from `h z hz`. Establish `htv` using `notMem_of_coprime ht hv`. Establish `ht0 : t ≠ 0`.

Introduce and unpack `rfl`. Conclude with `htv (by simp)`. Take `⟨a, ha, hat'⟩` from `exists_inv (E := E) t ht0 {v} (fun u hu => by rw [hu]; exact htv)`. Use `⟨_, Translate.hat_smul_int ha hw, fun i => ?_⟩` and prove the remaining obligations. Establish `e1` using `congrArg (loc E v) (congrFun e i)`.

Establish `e2` using `congrArg (loc E v) hat'`. Rewrite `e2` using `[loc_ind_pos (Set.mem_singleton v)]`. Simplify using `only [Pi.smul_apply, Pi.sub_apply, nsmul_eq_mul, smul_eq_mul, map_mul] at e1 e2 ⊢`. Take the linear combination `(loc E v (a ⊗ₜ[F] (1 : E))) * e1 - (loc E v ((k *ᵥ z) i - z i)) * e2`.
-/
theorem congOneAt_of_congAtA {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (N D : ℕ)
    (k : Matrix (Fin n) (Fin n) (RA F E)) (h : CongAtA F L N D k) :
    CongOneAt N D (L : Set (Fin n → E)) k := by
  obtain ⟨t, ht, h⟩ := h
  intro v hv z hz
  obtain ⟨w, hw, e⟩ := h z hz
  have htv := notMem_of_coprime ht hv
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact htv (by simp)
  obtain ⟨a, ha, hat'⟩ := exists_inv (E := E) t ht0 {v} (fun u hu => by rw [hu]; exact htv)
  refine ⟨_, Translate.hat_smul_int ha hw, fun i => ?_⟩
  have e1 := congrArg (loc E v) (congrFun e i)
  have e2 := congrArg (loc E v) hat'
  rw [loc_ind_pos (Set.mem_singleton v)] at e2
  simp only [Pi.smul_apply, Pi.sub_apply, nsmul_eq_mul, smul_eq_mul, map_mul] at e1 e2 ⊢
  linear_combination (loc E v (a ⊗ₜ[F] (1 : E))) * e1 - (loc E v ((k *ᵥ z) i - z i)) * e2

/- English proof (translation)
Proceed by induction on `m using Nat.recOnMul with`. Consider the case `zero => exact absurd rfl hm`. Consider the case `one => exact ⟨1, 0, Nat.coprime_one_left N, one_dvd _⟩`. Consider the case `prime p hp`. Distinguish the cases in `h : p ∣ N`.

Conclude with `⟨1, 1, Nat.coprime_one_left N, by simpa using h⟩`. Conclude with `⟨p, 0, (Nat.Prime.coprime_iff_not_dvd hp).2 h, by simp⟩`. Consider the case `mul a b ha hb`. Take `⟨t, j, ht, h⟩` from `ha (left_ne_zero_of_mul hm)`. Take `⟨t', j', ht', h'⟩` from `hb (right_ne_zero_of_mul hm)`.

Use `⟨t * t', j + j', Nat.Coprime.mul_left ht ht', ?_⟩` and prove the remaining obligations. Rewrite using `[pow_add, mul_mul_mul_comm]`. Conclude with `mul_dvd_mul h h'`.
-/
theorem exists_coprime_dvd (N m : ℕ) (hm : m ≠ 0) : ∃ t j : ℕ, t.Coprime N ∧ m ∣ t * N ^ j := by
  induction m using Nat.recOnMul with
  | zero => exact absurd rfl hm
  | one => exact ⟨1, 0, Nat.coprime_one_left N, one_dvd _⟩
  | prime p hp =>
    by_cases h : p ∣ N
    · exact ⟨1, 1, Nat.coprime_one_left N, by simpa using h⟩
    · exact ⟨p, 0, (Nat.Prime.coprime_iff_not_dvd hp).2 h, by simp⟩
  | mul a b ha hb =>
    obtain ⟨t, j, ht, h⟩ := ha (left_ne_zero_of_mul hm)
    obtain ⟨t', j', ht', h'⟩ := hb (right_ne_zero_of_mul hm)
    refine ⟨t * t', j + j', Nat.Coprime.mul_left ht ht', ?_⟩
    rw [pow_add, mul_mul_mul_comm]
    exact mul_dvd_mul h h'

/- English proof (translation)
Establish `hfin : {v : HeightOneSpectrum (𝓞 F) | (N : 𝓞 F) ∈ v.asIdeal}.Finite`. Use `(Ideal.finite_factors (I := Ideal.span {(N : 𝓞 F)}) (by simpa using hN)).subset fun v hv => ?_` and prove the remaining obligations. Conclude with `Ideal.dvd_span_singleton.2 hv`. Use `choose! y hy hy' using h`. Use `⟨∑ v ∈ hfin.toFinset, (ind {v} ⊗ₜ[F] (1 : E) : RA F E) • y v, sum_mem fun v hv => Translate.hat_smul_int (ind_int _) (hy v (hfin.mem_toFinset.1 hv)), fun v hv i => ?_⟩` and prove the remaining obligations.

Rewrite using `[hy' v hv i]`. Simplify using `only [Pi.smul_apply, nsmul_eq_mul, map_mul, Finset.sum_apply, map_sum, smul_eq_mul]`. Rewrite using `[Finset.sum_eq_single v, loc_ind_pos (Set.mem_singleton v), one_mul]`. Introduce `w _ hw`. Rewrite using `[loc_ind_neg (fun h => hw (Set.mem_singleton_iff.1 h).symm), zero_mul]`.

Introduce `h`. Conclude with `absurd (hfin.mem_toFinset.2 hv) h`.
-/
theorem exists_glue {n : ℕ} (L : Set (Fin n → E)) {N : ℕ} (hN : N ≠ 0) (D : ℕ) (u : Fin n → RA F E)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∈ v.asIdeal →
      ∃ y ∈ hat F L, ∀ i, loc E v (u i) = loc E v ((D • y) i)) :
    ∃ y ∈ hat F L, ∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∈ v.asIdeal →
      ∀ i, loc E v (u i) = loc E v ((D • y) i) := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | (N : 𝓞 F) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(N : 𝓞 F)}) (by simpa using hN)).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  choose! y hy hy' using h
  refine ⟨∑ v ∈ hfin.toFinset, (ind {v} ⊗ₜ[F] (1 : E) : RA F E) • y v,
    sum_mem fun v hv => Translate.hat_smul_int (ind_int _) (hy v (hfin.mem_toFinset.1 hv)), fun v hv i => ?_⟩
  rw [hy' v hv i]
  simp only [Pi.smul_apply, nsmul_eq_mul, map_mul, Finset.sum_apply, map_sum, smul_eq_mul]
  rw [Finset.sum_eq_single v, loc_ind_pos (Set.mem_singleton v), one_mul]
  · intro w _ hw
    rw [loc_ind_neg (fun h => hw (Set.mem_singleton_iff.1 h).symm), zero_mul]
  · intro h
    exact absurd (hfin.mem_toFinset.2 hv) h

/- English proof (translation)
Introduce `z hz`. Take `⟨r, hr⟩` from `hdvd`. Take `⟨y, hy, hy'⟩` from `exists_glue (L : Set (Fin n → E)) hN D (k *ᵥ z - z) fun v hv => h v hv z hz`. Use `set S : Set (HeightOneSpectrum (𝓞 F)) := {v | (N : 𝓞 F) ∈ v.asIdeal} with hS`. Take `⟨a, ha, ha'⟩` from `exists_inv (E := E) (N ^ j) (pow_ne_zero _ hN) Sᶜ (fun v hv h => by`.

Rewrite `h` using `[Nat.cast_pow]`. Conclude with `hv (v.isPrime.mem_of_pow_mem _ h))`. Establish `hu : d • (k *ᵥ z - z) ∈ hat F (L : Set (Fin n → E))`. Rewrite using `[smul_sub]`. Conclude with `sub_mem (hk z hz) (nsmul_mem hz d)`.

Use `⟨_, add_mem (Translate.hat_smul_int (ind_int S) (nsmul_mem hy t)) (Translate.hat_smul_int ha (nsmul_mem hu r)), funext fun i => eq_of_loc fun v => ?_⟩` and prove the remaining obligations. Establish `e2` using `congrArg (loc E v) ha'`. Establish `e3 : ((t * N ^ j : ℕ) : v.adicCompletion F ⊗[F] E) = (D * d * r : ℕ)` using `by rw [hr]`. Generalize the expression as in `k *ᵥ z - z = u at *`. Distinguish the cases in `hv : v ∈ S`.

Establish `e1` using `hy' v hv i`. Establish `e4 : loc E v (a ⊗ₜ[F] (1 : E)) = 0`. Rewrite `e2` using `[loc_ind_neg (Set.notMem_compl_iff.2 hv), map_mul, map_natCast]`. Establish `hu : IsUnit ((N ^ j : ℕ) : v.adicCompletion F ⊗[F] E)`. Rewrite using `[← map_natCast (algebraMap F _)]`.

Conclude with `(IsUnit.mk0 _ (Nat.cast_ne_zero.2 (pow_ne_zero _ hN))).map _`. Conclude with `(hu.mul_right_eq_zero).1 e2`. Simplify using `only [Pi.smul_apply, Pi.add_apply, nsmul_eq_mul, smul_eq_mul, map_mul, map_add, map_natCast, Pi.mul_apply, Pi.natCast_apply, loc_ind_pos hv, e4] at e1 ⊢`. Take the linear combination `(t : v.adicCompletion F ⊗[F] E) * e1`. Rewrite `e2` using `[loc_ind_pos (Set.mem_compl hv)]`.

Simplify using `only [Pi.smul_apply, Pi.add_apply, nsmul_eq_mul, smul_eq_mul, map_mul, map_add, map_natCast, Pi.mul_apply, Pi.natCast_apply, loc_ind_neg hv] at e2 ⊢`. Move the coercions through the operations in `at e2 e3`. Take the linear combination `(loc E v (a ⊗ₜ[F] (1 : E)) * loc E v (u i)) * e3 - (t : v.adicCompletion F ⊗[F] E) * loc E v (u i) * e2`.
-/
theorem congAtA_of_congOneAt {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) {N D d : ℕ} (hN : N ≠ 0) (hD : D ≠ 0)
    (hd : d ≠ 0) (k : Matrix (Fin n) (Fin n) (RA F E))
    (hk : ∀ z ∈ hat F (L : Set (Fin n → E)), d • k *ᵥ z ∈ hat F (L : Set (Fin n → E)))
    (h : CongOneAt N D (L : Set (Fin n → E)) k) {t j : ℕ} (hdvd : D * d ∣ t * N ^ j) :
    ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)), t • (k *ᵥ z - z) = D • w := by
  intro z hz
  obtain ⟨r, hr⟩ := hdvd
  obtain ⟨y, hy, hy'⟩ := exists_glue (L : Set (Fin n → E)) hN D (k *ᵥ z - z) fun v hv => h v hv z hz
  set S : Set (HeightOneSpectrum (𝓞 F)) := {v | (N : 𝓞 F) ∈ v.asIdeal} with hS
  obtain ⟨a, ha, ha'⟩ := exists_inv (E := E) (N ^ j) (pow_ne_zero _ hN) Sᶜ (fun v hv h => by
    rw [Nat.cast_pow] at h
    exact hv (v.isPrime.mem_of_pow_mem _ h))
  have hu : d • (k *ᵥ z - z) ∈ hat F (L : Set (Fin n → E)) := by
    rw [smul_sub]; exact sub_mem (hk z hz) (nsmul_mem hz d)
  refine ⟨_, add_mem (Translate.hat_smul_int (ind_int S) (nsmul_mem hy t))
    (Translate.hat_smul_int ha (nsmul_mem hu r)), funext fun i => eq_of_loc fun v => ?_⟩
  have e2 := congrArg (loc E v) ha'
  have e3 : ((t * N ^ j : ℕ) : v.adicCompletion F ⊗[F] E) = (D * d * r : ℕ) := by rw [hr]
  generalize k *ᵥ z - z = u at *
  by_cases hv : v ∈ S
  · have e1 := hy' v hv i
    have e4 : loc E v (a ⊗ₜ[F] (1 : E)) = 0 := by
      rw [loc_ind_neg (Set.notMem_compl_iff.2 hv), map_mul, map_natCast] at e2
      have hu : IsUnit ((N ^ j : ℕ) : v.adicCompletion F ⊗[F] E) := by
        rw [← map_natCast (algebraMap F _)]
        exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (pow_ne_zero _ hN))).map _
      exact (hu.mul_right_eq_zero).1 e2
    simp only [Pi.smul_apply, Pi.add_apply, nsmul_eq_mul, smul_eq_mul, map_mul, map_add, map_natCast,
      Pi.mul_apply, Pi.natCast_apply,
      loc_ind_pos hv, e4] at e1 ⊢
    linear_combination (t : v.adicCompletion F ⊗[F] E) * e1
  · rw [loc_ind_pos (Set.mem_compl hv)] at e2
    simp only [Pi.smul_apply, Pi.add_apply, nsmul_eq_mul, smul_eq_mul, map_mul, map_add, map_natCast,
      Pi.mul_apply, Pi.natCast_apply,
      loc_ind_neg hv] at e2 ⊢
    push_cast at e2 e3
    linear_combination (loc E v (a ⊗ₜ[F] (1 : E)) * loc E v (u i)) * e3 -
      (t : v.adicCompletion F ⊗[F] E) * loc E v (u i) * e2

/- English proof (translation)
Use `⟨congOneAt_of_congAtA L N D k, fun h => ?_⟩` and prove the remaining obligations. Take `⟨t, j, ht, hdvd⟩` from `exists_coprime_dvd N (D * d) (mul_ne_zero hD hd)`. Conclude with `⟨t, ht, congAtA_of_congOneAt L hN hD hd k hk h hdvd⟩`.
-/
theorem congAtA_iff_of_bounded {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) {N D d : ℕ} (hN : N ≠ 0) (hD : D ≠ 0)
    (hd : d ≠ 0) (k : Matrix (Fin n) (Fin n) (RA F E))
    (hk : ∀ z ∈ hat F (L : Set (Fin n → E)), d • k *ᵥ z ∈ hat F (L : Set (Fin n → E))) :
    CongAtA F L N D k ↔ CongOneAt N D (L : Set (Fin n → E)) k := by
  refine ⟨congOneAt_of_congAtA L N D k, fun h => ?_⟩
  obtain ⟨t, j, ht, hdvd⟩ := exists_coprime_dvd N (D * d) (mul_ne_zero hD hd)
  exact ⟨t, ht, congAtA_of_congOneAt L hN hD hd k hk h hdvd⟩

/- English proof (translation)
Take `⟨d, hd, hk⟩` from `Translate.exists_bound k hfg (hat_rational_points_and_approx F E n L hfg hsp).2.2.2`. Conclude with `congAtA_iff_of_bounded L hN hD hd.ne' k hk`.
-/
theorem congAtA_iff [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) {N D : ℕ} (hN : N ≠ 0) (hD : D ≠ 0)
    (k : Matrix (Fin n) (Fin n) (RA F E)) :
    CongAtA F L N D k ↔ CongOneAt N D (L : Set (Fin n → E)) k := by
  obtain ⟨d, hd, hk⟩ := Translate.exists_bound k hfg (hat_rational_points_and_approx F E n L hfg hsp).2.2.2
  exact congAtA_iff_of_bounded L hN hD hd.ne' k hk

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨v⟩ : Nonempty (HeightOneSpectrum (𝓞 F)) := by`. Take `⟨P, hP⟩` from `Ideal.exists_maximal (𝓞 F)`. Conclude with `⟨⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩⟩`. Use `haveI : Nontrivial (FiniteAdeleRing (𝓞 F) F) := (evalAt v).toRingHom.domain_nontrivial`. Conclude with `Algebra.TensorProduct.includeRight_injective (algebraMap F _).injective`.
-/
theorem inc_injective : Function.Injective
    (Algebra.TensorProduct.includeRight (R := F) (A := FiniteAdeleRing (𝓞 F) F) (B := E)) := by
  obtain ⟨v⟩ : Nonempty (HeightOneSpectrum (𝓞 F)) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
    exact ⟨⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩⟩
  haveI : Nontrivial (FiniteAdeleRing (𝓞 F) F) := (evalAt v).toRingHom.domain_nontrivial
  exact Algebra.TensorProduct.includeRight_injective (algebraMap F _).injective

/- English proof (translation)
Establish `key : ∀ (M : Matrix (Fin n) (Fin n) R) (x y : Fin n → R), ∑ a, ∑ b, x a * M a b * s (y b) = x ⬝ᵥ (M *ᵥ fun b => s (y b))` using `fun M x y => by`. Simplify using `only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]`. Establish `e : ∀ x y : Fin n → R, ∑ a, ∑ b, (g *ᵥ x) a * G a b * s ((g *ᵥ y) b) = ∑ a, ∑ b, x a * (gᵀ * G * g.map s) a b * s (y b)` using `fun x y => by`. Establish `e : (fun b => s ((g *ᵥ y) b)) = g.map s *ᵥ fun b => s (y b)`. Use function extensionality and compare the values at `b`.

Simplify using `only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]`. Rewrite using `[key, key, e, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, ← Matrix.dotProduct_mulVec, mul_assoc]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `a b`.

Use `(e (Pi.single a 1) (Pi.single b 1)).symm.trans (h _ _)` as an intermediate fact. Simplify `this` using `[Pi.single_apply, apply_ite s]`. Introduce `h x y`. Rewrite using `[e, h]`.
-/
theorem unitary_iff_matrix {R : Type} [CommRing R] {n : ℕ} (s : R →+* R) (G g : Matrix (Fin n) (Fin n) R) :
    (∀ x y : Fin n → R, ∑ a, ∑ b, (g *ᵥ x) a * G a b * s ((g *ᵥ y) b) = ∑ a, ∑ b, x a * G a b * s (y b)) ↔
      gᵀ * G * g.map s = G := by
  have key : ∀ (M : Matrix (Fin n) (Fin n) R) (x y : Fin n → R),
      ∑ a, ∑ b, x a * M a b * s (y b) = x ⬝ᵥ (M *ᵥ fun b => s (y b)) := fun M x y => by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have e : ∀ x y : Fin n → R, ∑ a, ∑ b, (g *ᵥ x) a * G a b * s ((g *ᵥ y) b) =
      ∑ a, ∑ b, x a * (gᵀ * G * g.map s) a b * s (y b) := fun x y => by
    have e : (fun b => s ((g *ᵥ y) b)) = g.map s *ᵥ fun b => s (y b) := by
      funext b
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
    rw [key, key, e, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec,
      ← Matrix.dotProduct_mulVec, mul_assoc]
  constructor
  · intro h
    ext a b
    have := (e (Pi.single a 1) (Pi.single b 1)).symm.trans (h _ _)
    simpa [Pi.single_apply, apply_ite s] using this
  · intro h x y
    rw [e, h]

/- English proof (translation)
The claim follows from `unitary_iff_matrix (sg (FiniteAdeleRing (𝓞 F) F) c).toRingHom (fm F G) g`.
-/
theorem isUnA_iff_matrix (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (g : Matrix (Fin n) (Fin n) (RA F E)) :
    IsUnA c G g ↔ gᵀ * fm F G * g.map (sg (FiniteAdeleRing (𝓞 F) F) c).toRingHom = fm F G :=
  unitary_iff_matrix (sg (FiniteAdeleRing (𝓞 F) F) c).toRingHom (fm F G) g

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fm_eq_map {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) : fm F γ =
    γ.map (Algebra.TensorProduct.includeRight (R := F) (A := FiniteAdeleRing (𝓞 F) F) (B := E)).toRingHom := rfl

/- English proof (translation)
Establish `h1 : IsUnE c G γ ↔ γᵀ * G * γ.map (c : E →+* E) = G` using `unitary_iff_matrix (c : E →+* E) G γ`. Establish `h2 : (fm F γ).map (sg (FiniteAdeleRing (𝓞 F) F) c).toRingHom = fm F (γ.map (c : E →+* E))`. Use extensionality with `a b`. Simplify using `[fm, sg]`. Rewrite using `[← isUnA_iff, ← fm_eq_ratM, isUnA_iff_matrix, h1, h2, fm_eq_map, fm_eq_map, fm_eq_map, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]`.

Conclude with `(Matrix.map_injective inc_injective).eq_iff.symm`.
-/
theorem isUnE_iff (c : E ≃ₐ[F] E) {n : ℕ} (G γ : Matrix (Fin n) (Fin n) E) :
    IsUnE c G γ ↔ IsUnitaryA c G (ratM F γ) := by
  have h1 : IsUnE c G γ ↔ γᵀ * G * γ.map (c : E →+* E) = G := unitary_iff_matrix (c : E →+* E) G γ
  have h2 : (fm F γ).map (sg (FiniteAdeleRing (𝓞 F) F) c).toRingHom = fm F (γ.map (c : E →+* E)) := by
    ext a b
    simp [fm, sg]
  rw [← isUnA_iff, ← fm_eq_ratM, isUnA_iff_matrix, h1, h2, fm_eq_map, fm_eq_map, fm_eq_map,
    ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
  exact (Matrix.map_injective inc_injective).eq_iff.symm

/- English proof (translation)
Establish `h` using `congrArg Matrix.det ((isUnA_iff_matrix c G g).1 hg)`. Establish `hu : IsUnit (fm F G).det`. Rewrite using `[fm_eq_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `(IsUnit.mk0 _ hG).map _`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_assoc]`.

Rewrite using `[Matrix.isUnit_iff_isUnit_det]`. Conclude with `isUnit_of_mul_isUnit_left (h.symm ▸ hu)`.
-/
theorem isUnit_of_isUnA (c : E ≃ₐ[F] E) {n : ℕ} {G : Matrix (Fin n) (Fin n) E} (hG : G.det ≠ 0)
    {g : Matrix (Fin n) (Fin n) (RA F E)} (hg : IsUnA c G g) : IsUnit g := by
  have h := congrArg Matrix.det ((isUnA_iff_matrix c G g).1 hg)
  have hu : IsUnit (fm F G).det := by
    rw [fm_eq_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsUnit.mk0 _ hG).map _
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_assoc] at h
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_of_mul_isUnit_left (h.symm ▸ hu)

omit [NumberField F] in
/- English proof (translation)
Establish `h` using `congrArg Matrix.det ((unitary_iff_matrix (c : E →+* E) G γ).1 hγ)`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_assoc]`. Rewrite using `[Matrix.isUnit_iff_isUnit_det]`. Conclude with `isUnit_of_mul_isUnit_left (h.symm ▸ IsUnit.mk0 _ hG)`.
-/
theorem isUnit_of_isUnE (c : E ≃ₐ[F] E) {n : ℕ} {G : Matrix (Fin n) (Fin n) E} (hG : G.det ≠ 0)
    {γ : Matrix (Fin n) (Fin n) E} (hγ : IsUnE c G γ) : IsUnit γ := by
  have h := congrArg Matrix.det ((unitary_iff_matrix (c : E →+* E) G γ).1 hγ)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_assoc] at h
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_of_mul_isUnit_left (h.symm ▸ IsUnit.mk0 _ hG)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => ⟨h.2.1, fun a b => (h.2.2.1 a b).symm, h.2.2.2⟩, fun h => ⟨conj_conj c h2 h.1, h.1, fun a b => (h.2.1 a b).symm, h.2.2⟩⟩`.
-/
theorem isHermForm_iff (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) :
    IsHermForm c G ↔ c ≠ 1 ∧ (∀ a b, G b a = c (G a b)) ∧ G.det ≠ 0 :=
  ⟨fun h => ⟨h.2.1, fun a b => (h.2.2.1 a b).symm, h.2.2.2⟩,
    fun h => ⟨conj_conj c h2 h.1, h.1, fun a b => (h.2.1 a b).symm, h.2.2⟩⟩

def HasRep (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (N : ℕ) : Prop :=
  ∀ g : GL (Fin n) (RA F E), IsUnA c G g.1 → ∃ (γ : GL (Fin n) E) (h k : GL (Fin n) (RA F E)),
    IsUnE c G γ.1 ∧ IsUnA c G h.1 ∧ IsUnA c G k.1 ∧ g.1 = fm F γ.1 * h.1 * k.1 ∧ SuppSplit c N h.1 ∧
    (∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)), k.1 *ᵥ z - z = N • w) ∧
    ∀ z ∈ hat F (L : Set (Fin n → E)), (k⁻¹).1 *ᵥ z ∈ hat F (L : Set (Fin n → E))

/- English proof (translation)
Introduce `g hg`. Take `⟨γ, h, k, hγ, ⟨hh, hs⟩, ⟨hk, hst, hcong⟩, e⟩` from `H g.1 hg`. Rewrite `hγ` using `[← isUnE_iff]`. Take `⟨γ, rfl⟩` from `isUnit_of_isUnE c hG hγ`. Take `⟨h, rfl⟩` from `isUnit_of_isUnA c hG hh`.

Take `⟨k, rfl⟩` from `isUnit_of_isUnA c hG hk`. Use `⟨γ, h, k, hγ, hh, hk, e, (suppSplit_iff c h2 hc N _).2 hs, ?_, fun z hz => ?_⟩` and prove the remaining obligations. Use `congAtA_of_congOneAt L hN hN one_ne_zero k.1 (fun z hz => by` as an intermediate fact. Rewrite using `[one_smul, ← SetLike.mem_coe, ← hst]; exact ⟨z, hz, rfl⟩) hcong (t := 1) (j := 1) (by simp)`. Simplify `this` using `only [one_smul]`.

Rewrite `hz` using `[← SetLike.mem_coe, ← hst]`. Take `⟨x, hx, rfl⟩` from `hz`. Rewrite using `[Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]` and apply the resulting hypothesis.
-/
theorem hasRep_of (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) {n : ℕ}
    {G : Matrix (Fin n) (Fin n) E} (hG : G.det ≠ 0) (L : Submodule (𝓞 E) (Fin n → E)) {N : ℕ} (hN : N ≠ 0)
    (H : HasSplitRepresentatives c G (L : Set (Fin n → E)) N N) : HasRep c G L N := by
  intro g hg
  obtain ⟨γ, h, k, hγ, ⟨hh, hs⟩, ⟨hk, hst, hcong⟩, e⟩ := H g.1 hg
  rw [← isUnE_iff] at hγ
  obtain ⟨γ, rfl⟩ := isUnit_of_isUnE c hG hγ
  obtain ⟨h, rfl⟩ := isUnit_of_isUnA c hG hh
  obtain ⟨k, rfl⟩ := isUnit_of_isUnA c hG hk
  refine ⟨γ, h, k, hγ, hh, hk, e, (suppSplit_iff c h2 hc N _).2 hs, ?_, fun z hz => ?_⟩
  · have := congAtA_of_congOneAt L hN hN one_ne_zero k.1 (fun z hz => by
      rw [one_smul, ← SetLike.mem_coe, ← hst]; exact ⟨z, hz, rfl⟩) hcong (t := 1) (j := 1) (by simp)
    simpa only [one_smul] using this
  · rw [← SetLike.mem_coe, ← hst] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

/- English proof (translation)
Introduce `g hg`. Take `⟨g, rfl⟩` from `isUnit_of_isUnA c hG hg`. Take `⟨γ, h, k, hγ, hh, hk, e, hs, hcong, hinv⟩` from `H g hg`. Take `⟨T, hT, hT'⟩` from `(suppSplit_iff c h2 hc _ _).1 hs`. Use `⟨γ.1, h.1, k.1, (isUnE_iff c G _).1 hγ, ⟨hh, T, fun v hv => ⟨(hT v hv).1, fun h => (hT v hv).2 ?_⟩, hT'⟩, ⟨hk, ?_, fun v _ z hz => ?_⟩, e⟩` and prove the remaining obligations.

Rewrite using `[Nat.cast_mul]`. Conclude with `v.asIdeal.mul_mem_right _ h`. Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Take `⟨w, hw, e⟩` from `hcong z hz`.

Rewrite using `[sub_eq_iff_eq_add.1 e]`. Conclude with `add_mem (nsmul_mem hw _) hz`. Introduce `z hz`. Conclude with `⟨_, hinv z hz, by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩`. Take `⟨w, hw, e⟩` from `hcong z hz`.

Use `⟨N • w, nsmul_mem hw _, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul, mul_comm D, ← e]`. Both sides reduce to the same expression.
-/
theorem of_hasRep (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) {n : ℕ}
    {G : Matrix (Fin n) (Fin n) E} (hG : G.det ≠ 0) (L : Submodule (𝓞 E) (Fin n → E)) (N D : ℕ)
    (H : HasRep c G L (N * D)) : HasSplitRepresentatives c G (L : Set (Fin n → E)) N D := by
  intro g hg
  obtain ⟨g, rfl⟩ := isUnit_of_isUnA c hG hg
  obtain ⟨γ, h, k, hγ, hh, hk, e, hs, hcong, hinv⟩ := H g hg
  obtain ⟨T, hT, hT'⟩ := (suppSplit_iff c h2 hc _ _).1 hs
  refine ⟨γ.1, h.1, k.1, (isUnE_iff c G _).1 hγ, ⟨hh, T, fun v hv => ⟨(hT v hv).1, fun h => (hT v hv).2 ?_⟩, hT'⟩,
    ⟨hk, ?_, fun v _ z hz => ?_⟩, e⟩
  · rw [Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ h
  · apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨w, hw, e⟩ := hcong z hz
      rw [sub_eq_iff_eq_add.1 e]
      exact add_mem (nsmul_mem hw _) hz
    · intro z hz
      exact ⟨_, hinv z hz, by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩
  · obtain ⟨w, hw, e⟩ := hcong z hz
    refine ⟨N • w, nsmul_mem hw _, fun i => ?_⟩
    rw [smul_smul, mul_comm D, ← e]
    rfl

def RepStatement (n₀ : ℕ) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ),
    n₀ ≤ n → ∀ G : Matrix (Fin n) (Fin n) E, IsHermForm c G → Module.finrank F E = 2 →
    ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ →
    ∀ N : ℕ, 0 < N → HasRep c G L N

/- English proof (translation)
Introduce `F E _ _ _ _ _ c n hn` and use `H F E c n (hab.trans hn)`.
-/
theorem RepStatement.mono {a b : ℕ} (hab : a ≤ b) (H : RepStatement a) : RepStatement b :=
  fun F E _ _ _ _ _ c n hn => H F E c n (hab.trans hn)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `H F E _ _ _ _ _ c h2 hc n hn G hG hdet L hfg hsp N D hN hD`. Conclude with `of_hasRep c h2 hc hdet L N D (H F E c n hn G ((isHermForm_iff c h2 G).2 ⟨hc, hG, hdet⟩) h2 L hfg hsp _ (Nat.pos_of_ne_zero (mul_ne_zero hN hD)))`. Introduce `H F E _ _ _ _ _ c n hn G hG h2 L hfg hsp N hN`. Take `⟨hc, hG, hdet⟩` from `(isHermForm_iff c h2 G).1 hG`.

Conclude with `hasRep_of c h2 hc hdet L hN.ne' (H F E c h2 hc n hn G hG hdet L hfg hsp N N hN.ne' hN.ne')`.
-/
theorem repStatement_iff : RepStatement 2 ↔ SplitRepresentatives := by
  constructor
  · intro H F E _ _ _ _ _ c h2 hc n hn G hG hdet L hfg hsp N D hN hD
    exact of_hasRep c h2 hc hdet L N D (H F E c n hn G ((isHermForm_iff c h2 G).2 ⟨hc, hG, hdet⟩) h2 L hfg hsp
      _ (Nat.pos_of_ne_zero (mul_ne_zero hN hD)))
  · intro H F E _ _ _ _ _ c n hn G hG h2 L hfg hsp N hN
    obtain ⟨hc, hG, hdet⟩ := (isHermForm_iff c h2 G).1 hG
    exact hasRep_of c h2 hc hdet L hN.ne' (H F E c h2 hc n hn G hG hdet L hfg hsp N N hN.ne' hN.ne')

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ _ _ _ _ _ c _ G g => isUnA_iff c G g, fun _ _ _ _ _ _ c h2 hc => ⟨splitPl_iff c h2 hc, fun _ N h => suppSplit_iff c h2 hc N h⟩, fun _ _ _ _ _ _ _ _ L hfg hsp _ _ hN hD k => congAtA_iff L hfg hsp hN hD k, repStatement_iff⟩`.
-/
theorem typings_agree :
    (∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ)
      (G : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (RA F E)), IsUnA c G g ↔ IsUnitaryA c G g) ∧
    (∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E),
      Module.finrank F E = 2 → c ≠ 1 →
      (∀ v : HeightOneSpectrum (𝓞 F), SplitPl c v ↔ IsSplitPlace E v) ∧
      ∀ (n N : ℕ) (h : Matrix (Fin n) (Fin n) (RA F E)), SuppSplit c N h ↔ SupportedAtSplit N h) ∧
    (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
      (L : Submodule (𝓞 E) (Fin n → E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ →
      ∀ N D : ℕ, N ≠ 0 → D ≠ 0 → ∀ k : Matrix (Fin n) (Fin n) (RA F E),
      CongAtA F L N D k ↔ CongOneAt N D (L : Set (Fin n → E)) k) ∧
    (RepStatement 2 ↔ SplitRepresentatives) :=
  ⟨fun _ _ _ _ _ _ c _ G g => isUnA_iff c G g,
    fun _ _ _ _ _ _ c h2 hc => ⟨splitPl_iff c h2 hc, fun _ N h => suppSplit_iff c h2 hc N h⟩,
    fun _ _ _ _ _ _ _ _ L hfg hsp _ _ hN hD k => congAtA_iff L hfg hsp hN hD k, repStatement_iff⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun H F E _ _ _ _ _ c n G hG h2 L hfg hsp g N hg hN => H F E c n (Nat.zero_le n) G hG h2 L hfg hsp N hN g hg, fun H F E _ _ _ _ _ c n _ G hG h2 L hfg hsp N hN g hg => H F E c n G hG h2 L hfg hsp g N hg hN⟩`.
-/
theorem repStatement_zero_iff : RepStatement 0 ↔ (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → Module.finrank F E = 2 → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (g : GL (Fin n) (RA F E)) (N : ℕ), IsUnA c G g.1 → 0 < N → ∃ (γ : GL (Fin n) E) (h k : GL (Fin n) (RA F E)), IsUnE c G γ.1 ∧ IsUnA c G h.1 ∧ IsUnA c G k.1 ∧ g.1 = fm F γ.1 * h.1 * k.1 ∧ SuppSplit c N h.1 ∧ (∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)), k.1 *ᵥ z - z = N • w) ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), (k⁻¹).1 *ᵥ z ∈ hat F (L : Set (Fin n → E))) :=
  ⟨fun H F E _ _ _ _ _ c n G hG h2 L hfg hsp g N hg hN => H F E c n (Nat.zero_le n) G hG h2 L hfg hsp N hN g hg,
    fun H F E _ _ _ _ _ c n _ G hG h2 L hfg hsp N hN g hg => H F E c n G hG h2 L hfg hsp g N hg hN⟩

end GlobalTheory.UnRep.Compare
