import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

section Places

open Classical

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Pi.single v x v = x`. Simplify using the standard rewrite rules.
-/
theorem evalAt_singleF_same (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    evalAt F v (singleF F v x) = x := by
  change Pi.single v x v = x
  simp

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Pi.single v x u = 0`. Simplify using `[h]`.
-/
theorem evalAt_singleF_ne {u v : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) (x : v.adicCompletion F) :
    evalAt F u (singleF F v x) = 0 := by
  change Pi.single v x u = 0
  simp [h]

/- English proof (translation)
Apply `FiniteAdeleRing.ext` to reduce the goal to its premises. Introduce `u`. Express the relevant statement in the definitionally equal form `Pi.single v x u * Pi.single w y u = 0`. Distinguish the cases in `hu : u = v`. Substitute `hu` using the available equality.

Simplify using `[h]`. Simplify using `[hu]`.
-/
theorem singleF_mul_of_ne {v w : HeightOneSpectrum (𝓞 F)} (h : v ≠ w) (x : v.adicCompletion F)
    (y : w.adicCompletion F) : singleF F v x * singleF F w y = 0 := by
  apply FiniteAdeleRing.ext; intro u
  change Pi.single v x u * Pi.single w y u = 0
  by_cases hu : u = v
  · subst hu; simp [h]
  · simp [hu]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a' b'`. Simplify using `[singleV, Algebra.TensorProduct.tmul_mul_tmul, singleF_mul_of_ne h]`. Consider the case `add y y' hy hy' => rw [map_add, mul_add, hy, hy', add_zero]`. Consider the case `add x x' hx hx' => rw [map_add, add_mul, hx, hx', add_zero]`.
-/
theorem singleV_mul_of_ne {v w : HeightOneSpectrum (𝓞 F)} (h : v ≠ w) (x : Kv E v) (y : Kv E w) :
    singleV E v x * singleV E w y = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a' b' =>
      simp [singleV, Algebra.TensorProduct.tmul_mul_tmul, singleF_mul_of_ne h]
    | add y y' hy hy' => rw [map_add, mul_add, hy, hy', add_zero]
  | add x x' hx hx' => rw [map_add, add_mul, hx, hx', add_zero]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [compAt, singleV, evalAt_singleF_same]`. Consider the case `add x x' hx hx' => rw [map_add, map_add, hx, hx']`.
-/
theorem compAt_singleV_same (v : HeightOneSpectrum (𝓞 F)) (x : Kv E v) :
    compAt E v (singleV E v x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [compAt, singleV, evalAt_singleF_same]
  | add x x' hx hx' => rw [map_add, map_add, hx, hx']

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [compAt, singleV, evalAt_singleF_ne h]`. Consider the case `add x x' hx hx' => rw [map_add, map_add, hx, hx', add_zero]`.
-/
theorem compAt_singleV_ne {u v : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) (x : Kv E v) :
    compAt E u (singleV E v x) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [compAt, singleV, evalAt_singleF_ne h]
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', add_zero]

/- English proof (translation)
Rewrite using `[restrictTo, map_sum]`. Use `split_ifs with hv`. Rewrite using `[Finset.sum_eq_single_of_mem v hv (fun w _ hw => compAt_singleV_ne hw.symm _), compAt_singleV_same]`. Conclude with `Finset.sum_eq_zero fun w hw => compAt_singleV_ne (by rintro rfl; exact hv hw) _`.
-/
theorem compAt_restrictTo (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F))
    (a : AE F E) : compAt E v (restrictTo E S a) = if v ∈ S then compAt E v a else 0 := by
  rw [restrictTo, map_sum]
  split_ifs with hv
  · rw [Finset.sum_eq_single_of_mem v hv (fun w _ hw => compAt_singleV_ne hw.symm _),
      compAt_singleV_same]
  · exact Finset.sum_eq_zero fun w hw => compAt_singleV_ne (by rintro rfl; exact hv hw) _

/- English proof (translation)
Simplify using `[compAt, inclA, inclV]`.
-/
theorem compAt_inclA (v : HeightOneSpectrum (𝓞 F)) (y : E) :
    compAt E v (inclA F E y) = inclV E v y := by
  simp [compAt, inclA, inclV]

/- English proof (translation)
Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [compAt, sigA, sigV]`. Consider the case `add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]`.
-/
theorem compAt_sigA (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : AE F E) :
    compAt E v (sigA c a) = sigV c v (compAt E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [compAt, sigA, sigV]
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]

/- English proof (translation)
Take `⟨hdet, hu⟩` from `hx`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one]`. Establish `h` using `congrArg (compAt E v).mapMatrix hu`. Simplify using `only [map_mul, RingHom.mapMatrix_apply] at h`.

Establish `hJ : (J.map (inclA F E)).map (compAt E v) = J.map (inclV E v)`. Use extensionality with `i j`. Simplify using `[compAt_inclA]`. Establish `hs : (x.map (sigA c)).map (compAt E v) = (x.map (compAt E v)).map (sigV c v).toRingHom`. Use extensionality with `i j`.

Simplify using `[compAt_sigA]`. Rewrite `h` using `[hJ, hs, Matrix.transpose_map]`. Conclude with `h`.
-/
theorem map_compAt_mem_SU (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {N : ℕ}
    (J : Matrix (Fin N) (Fin N) E) {x : Matrix (Fin N) (Fin N) (AE F E)}
    (hx : x ∈ SU (sigA c) (J.map (inclA F E))) :
    x.map (compAt E v) ∈ SU (sigV c v).toRingHom (J.map (inclV E v)) := by
  obtain ⟨hdet, hu⟩ := hx
  refine ⟨?_, ?_⟩
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one]
  · have h := congrArg (compAt E v).mapMatrix hu
    simp only [map_mul, RingHom.mapMatrix_apply] at h
    have hJ : (J.map (inclA F E)).map (compAt E v) = J.map (inclV E v) := by
      ext i j; simp [compAt_inclA]
    have hs : (x.map (sigA c)).map (compAt E v) = (x.map (compAt E v)).map (sigV c v).toRingHom := by
      ext i j; simp [compAt_sigA]
    rw [hJ, hs, Matrix.transpose_map] at h
    exact h

end Places

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons v l ih`. Rewrite `hl` using `[List.nodup_cons]`. Simplify using `only [List.map_cons, List.prod_cons, List.sum_cons]`.

Rewrite using `[ih hl.2]`. Establish `h0 : ∀ l' : List ι, v ∉ l' → B v * (l'.map B).sum = 0`. Introduce `l' hv'`. Proceed by induction on `l' with`. Consider the case `nil => simp`.

Consider the case `cons w l' ih'`. Rewrite `hv'` using `[List.mem_cons, not_or]`. Rewrite using `[List.map_cons, List.sum_cons, mul_add, hB v w hv'.1, ih' hv'.2, add_zero]`. Rewrite using `[mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, h0 l hl.1]`. Normalize the expressions using the abelian group laws.
-/
theorem list_prod_one_add {ι R : Type*} [Ring R] (B : ι → R) (hB : ∀ v w, v ≠ w → B v * B w = 0)
    (l : List ι) (hl : l.Nodup) : (l.map fun v => 1 + B v).prod = 1 + (l.map B).sum := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [ih hl.2]
    have h0 : ∀ l' : List ι, v ∉ l' → B v * (l'.map B).sum = 0 := by
      intro l' hv'
      induction l' with
      | nil => simp
      | cons w l' ih' =>
        rw [List.mem_cons, not_or] at hv'
        rw [List.map_cons, List.sum_cons, mul_add, hB v w hv'.1, ih' hv'.2, add_zero]
    rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, h0 l hl.1]
    abel

/- English proof (translation)
Introduce `F E _ _ _ _ _ c hE hc N J hJ hdet hiso _ _ S x`. Establish `part3 : ∀ l : List (HeightOneSpectrum (𝓞 F)), l.Nodup → (∀ v, v ∈ l ↔ v ∈ S) → trunc E S x = (l.map fun v => embed E v (x.map (compAt E v))).prod`. Introduce `l hl hlS`. Establish `hB : ∀ v w : HeightOneSpectrum (𝓞 F), v ≠ w → (x.map (compAt E v) - 1).map (singleV E v) * (x.map (compAt E w) - 1).map (singleV E w) = 0`. Introduce `v w h`.

Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply]`. Conclude with `Finset.sum_eq_zero fun k _ => singleV_mul_of_ne h _ _`. Rewrite using `[show (fun v => embed E v (x.map (compAt E v))) = fun v => 1 + (x.map (compAt E v) - 1).map (singleV E v) from rfl, list_prod_one_add _ hB l hl]`. Establish `hS : l.toFinset = S` using `by ext v; rw [List.mem_toFinset, hlS]`.

Rewrite using `[← List.sum_toFinset _ hl, hS, trunc]`. Use `congr 1`. Use extensionality with `i j`. Rewrite using `[Matrix.sum_apply]`. Simplify using `only [Matrix.map_apply, restrictTo, Matrix.sub_apply]`.

Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[map_sub, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Use `⟨?_, ?_, part3, ?_⟩` and prove the remaining obligations. Introduce `v hv`.

Use extensionality with `i j`. Simplify using `only [trunc, Matrix.map_apply, Matrix.add_apply, map_add, compAt_restrictTo, if_pos hv, Matrix.sub_apply, map_sub]`. Normalize the expressions using the abelian group laws. Introduce `v hv`. Use extensionality with `i j`.

Simplify using `only [trunc, Matrix.map_apply, Matrix.add_apply, map_add, compAt_restrictTo, if_neg hv, add_zero]`. Rewrite using `[Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Introduce `hx`. Establish `: Module.Finite F E` using `Module.finite_of_finrank_eq_succ hE`.

Establish `: IsTopologicalRing (AE F E)` using `IsModuleTopology.isTopologicalRing (FiniteAdeleRing (𝓞 F) F) (AE F E)`. Rewrite using `[part3 S.toList (Finset.nodup_toList S) (fun v => Finset.mem_toList)]`. Establish `hmem : ∀ l : List (HeightOneSpectrum (𝓞 F)), (l.map fun v => embed E v (x.map (compAt E v))).prod ∈ Cl c J`. Introduce `l`. Proceed by induction on `l with`.

Consider the case `nil`. Conclude with `subset_closure ⟨1, one_mem_SU, Matrix.map_one _ (map_zero _) (map_one _)⟩`. Consider the case `cons v l ih`. Rewrite using `[List.map_cons, List.prod_cons]`. Use `map_mem_closure₂ continuous_mul (hLoc F E c hE hc N J hJ hdet hiso v _ (map_compAt_mem_SU c v J hx)) ih ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨γ, hγ, rfl⟩ _ ⟨γ', hγ', rfl⟩`. Conclude with `⟨γ * γ', mul_mem_SU hγ hγ', Matrix.map_mul⟩`. Conclude with `hmem _`.
-/
theorem Truncation.proof (hLoc : LocalInClosure.Statement) : Truncation.Statement := by
  classical
  intro F E _ _ _ _ _ c hE hc N J hJ hdet hiso _ _ S x
  have part3 : ∀ l : List (HeightOneSpectrum (𝓞 F)), l.Nodup → (∀ v, v ∈ l ↔ v ∈ S) →
      trunc E S x = (l.map fun v => embed E v (x.map (compAt E v))).prod := by
    intro l hl hlS
    have hB : ∀ v w : HeightOneSpectrum (𝓞 F), v ≠ w →
        (x.map (compAt E v) - 1).map (singleV E v) * (x.map (compAt E w) - 1).map (singleV E w) = 0 := by
      intro v w h
      ext i j
      rw [Matrix.mul_apply]
      exact Finset.sum_eq_zero fun k _ => singleV_mul_of_ne h _ _
    rw [show (fun v => embed E v (x.map (compAt E v))) =
      fun v => 1 + (x.map (compAt E v) - 1).map (singleV E v) from rfl, list_prod_one_add _ hB l hl]
    have hS : l.toFinset = S := by ext v; rw [List.mem_toFinset, hlS]
    rw [← List.sum_toFinset _ hl, hS, trunc]
    congr 1
    ext i j
    rw [Matrix.sum_apply]
    simp only [Matrix.map_apply, restrictTo, Matrix.sub_apply]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_sub, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨?_, ?_, part3, ?_⟩
  · intro v hv
    ext i j
    simp only [trunc, Matrix.map_apply, Matrix.add_apply, map_add, compAt_restrictTo, if_pos hv,
      Matrix.sub_apply, map_sub]
    abel
  · intro v hv
    ext i j
    simp only [trunc, Matrix.map_apply, Matrix.add_apply, map_add, compAt_restrictTo, if_neg hv,
      add_zero]
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · intro hx
    have : Module.Finite F E := Module.finite_of_finrank_eq_succ hE
    have : IsTopologicalRing (AE F E) :=
      IsModuleTopology.isTopologicalRing (FiniteAdeleRing (𝓞 F) F) (AE F E)
    rw [part3 S.toList (Finset.nodup_toList S) (fun v => Finset.mem_toList)]
    have hmem : ∀ l : List (HeightOneSpectrum (𝓞 F)),
        (l.map fun v => embed E v (x.map (compAt E v))).prod ∈ Cl c J := by
      intro l
      induction l with
      | nil =>
        exact subset_closure ⟨1, one_mem_SU, Matrix.map_one _ (map_zero _) (map_one _)⟩
      | cons v l ih =>
        rw [List.map_cons, List.prod_cons]
        refine map_mem_closure₂ continuous_mul
          (hLoc F E c hE hc N J hJ hdet hiso v _ (map_compAt_mem_SU c v J hx)) ih ?_
        rintro _ ⟨γ, hγ, rfl⟩ _ ⟨γ', hγ', rfl⟩
        exact ⟨γ * γ', mul_mem_SU hγ hγ', Matrix.map_mul⟩
    exact hmem _

end StrongApprox

end GroundTheory.Heights₂.Heights
