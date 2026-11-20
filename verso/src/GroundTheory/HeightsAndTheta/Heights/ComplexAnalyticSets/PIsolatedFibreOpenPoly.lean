import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIsolatedFibreOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIsolatedFibreOpenPoly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology Filter Matrix ComplexSets

noncomputable section

namespace IsolatedFibreOpenPoly

variable {n d : ℕ}

def graphSubst (p : Fin d → MvPolynomial (Fin n) ℂ) :
    MvPolynomial (Fin (n + d)) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  aeval (Fin.append X p)

def graphIdeal (P : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ) :
    Ideal (MvPolynomial (Fin (n + d)) ℂ) :=
  P.comap (graphSubst p)

def graphPt (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) : Fin (n + d) → ℂ :=
  Fin.append x fun i => eval x (p i)

def firstPart (z : Fin (n + d) → ℂ) : Fin n → ℂ :=
  fun j => z (Fin.castAdd d j)

def lastRows (n d : ℕ) : Matrix (Fin d) (Fin (n + d)) ℂ :=
  fun i j => if j = Fin.natAdd n i then 1 else 0

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[lastRows, Matrix.mulVec, dotProduct, ite_mul]`.
-/
theorem lastRows_mulVec (z : Fin (n + d) → ℂ) : lastRows n d *ᵥ z = fun i => z (Fin.natAdd n i) := by
  funext i
  simp [lastRows, Matrix.mulVec, dotProduct, ite_mul]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `[firstPart, graphPt, Fin.append_left]`.
-/
theorem firstPart_graphPt (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) :
    firstPart (graphPt p x) = x := by
  funext j
  simp [firstPart, graphPt, Fin.append_left]

/- English proof (translation)
Simplify using `[graphPt, Fin.append_right]`.
-/
theorem graphPt_natAdd (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) (i : Fin d) :
    graphPt p x (Fin.natAdd n i) = eval x (p i) := by
  simp [graphPt, Fin.append_right]

/- English proof (translation)
The claim follows from `continuous_pi fun _ => continuous_apply _`.
-/
theorem continuous_firstPart : Continuous (firstPart : (Fin (n + d) → ℂ) → Fin n → ℂ) :=
  continuous_pi fun _ => continuous_apply _

/- English proof (translation)
Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C a => simp [graphSubst]`. Consider the case `add q r hq hr => simp only [map_add, hq, hr]`. Consider the case `mul_X q i hq`. Simplify using `only [map_mul, graphSubst, aeval_X, eval_X]`.

Use `congr 1`. Use `Fin.addCases (fun j => ?_) (fun j => ?_) i` and prove the remaining obligations. Simplify using `[graphPt, Fin.append_left]`. Simplify using `[graphPt, Fin.append_right]`.
-/
theorem eval_graphSubst (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ)
    (q : MvPolynomial (Fin (n + d)) ℂ) : eval x (graphSubst p q) = eval (graphPt p x) q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [graphSubst]
  | add q r hq hr => simp only [map_add, hq, hr]
  | mul_X q i hq =>
    simp only [map_mul, graphSubst, aeval_X, eval_X]
    congr 1
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [graphPt, Fin.append_left]
    · simp [graphPt, Fin.append_right]

/- English proof (translation)
Rewrite using `[graphSubst, aeval_rename]`. Establish `h : (Fin.append X p ∘ Fin.castAdd d : Fin n → MvPolynomial (Fin n) ℂ) = X`. Use function extensionality and compare the values at `j`. Simplify using `[Fin.append_left]`. Rewrite using `[h, aeval_X_left_apply]`.
-/
theorem graphSubst_rename (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ) :
    graphSubst p (rename (Fin.castAdd d) q) = q := by
  rw [graphSubst, aeval_rename]
  have h : (Fin.append X p ∘ Fin.castAdd d : Fin n → MvPolynomial (Fin n) ℂ) = X := by
    funext j
    simp [Fin.append_left]
  rw [h, aeval_X_left_apply]

/- English proof (translation)
Introduce `q` and use `⟨rename (Fin.castAdd d) q, graphSubst_rename p q⟩`.
-/
theorem graphSubst_surjective (p : Fin d → MvPolynomial (Fin n) ℂ) :
    Function.Surjective (graphSubst p) :=
  fun q => ⟨rename (Fin.castAdd d) q, graphSubst_rename p q⟩

/- English proof (translation)
Use `hP` as an intermediate fact. Unfold `graphIdeal`. Use `infer_instance`.
-/
theorem isPrime_graphIdeal {P : Ideal (MvPolynomial (Fin n) ℂ)} (hP : P.IsPrime)
    (p : Fin d → MvPolynomial (Fin n) ℂ) : (graphIdeal P p).IsPrime := by
  have := hP
  unfold graphIdeal
  infer_instance

/- English proof (translation)
Use `set f : MvPolynomial (Fin (n + d)) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ P := (Ideal.Quotient.mk P).comp (graphSubst p).toRingHom with hf`. Establish `hsurj : Function.Surjective f` using `Ideal.Quotient.mk_surjective.comp (graphSubst_surjective p)`. Establish `hker : graphIdeal P p = RingHom.ker f`. Rewrite using `[hf, ← RingHom.comap_ker, Ideal.mk_ker]`. Both sides reduce to the same expression.

Conclude with `ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hsurj))`.
-/
theorem ringKrullDim_graphIdeal (P : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ) :
    ringKrullDim (MvPolynomial (Fin (n + d)) ℂ ⧸ graphIdeal P p) =
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) := by
  set f : MvPolynomial (Fin (n + d)) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ P :=
    (Ideal.Quotient.mk P).comp (graphSubst p).toRingHom with hf
  have hsurj : Function.Surjective f :=
    Ideal.Quotient.mk_surjective.comp (graphSubst_surjective p)
  have hker : graphIdeal P p = RingHom.ker f := by
    rw [hf, ← RingHom.comap_ker, Ideal.mk_ker]
    rfl
  exact ringKrullDim_eq_of_ringEquiv
    ((Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hsurj))

/- English proof (translation)
Introduce `q hq`. Rewrite using `[← eval_graphSubst]`. Conclude with `hx _ hq`.
-/
theorem graphPt_mem {P : Ideal (MvPolynomial (Fin n) ℂ)} (p : Fin d → MvPolynomial (Fin n) ℂ)
    {x : Fin n → ℂ} (hx : x ∈ zeroSet P) : graphPt p x ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p) := by
  intro q hq
  rw [← eval_graphSubst]
  exact hx _ hq

/- English proof (translation)
Introduce `q hq`. Establish `h` using `hz (rename (Fin.castAdd d) q) (by show graphSubst p (rename (Fin.castAdd d) q) ∈ P`. Rewrite using `[graphSubst_rename]`. Conclude with `hq)`. Rewrite `h` using `[eval_rename]`.

Conclude with `h`.
-/
theorem firstPart_mem {P : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {z : Fin (n + d) → ℂ} (hz : z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p)) :
    firstPart z ∈ zeroSet P := by
  intro q hq
  have h := hz (rename (Fin.castAdd d) q) (by
    show graphSubst p (rename (Fin.castAdd d) q) ∈ P
    rw [graphSubst_rename]
    exact hq)
  rw [eval_rename] at h
  exact h

/- English proof (translation)
Establish `h` using `hz (X (Fin.natAdd n i) - rename (Fin.castAdd d) (p i)) (by show graphSubst p (X (Fin.natAdd n i) - rename (Fin.castAdd d) (p i)) ∈ P`. Rewrite using `[map_sub, graphSubst_rename, graphSubst, aeval_X, Fin.append_right, sub_self]`. Conclude with `P.zero_mem)`. Rewrite `h` using `[map_sub, eval_X, eval_rename, sub_eq_zero]`. Conclude with `h`.
-/
theorem natAdd_of_mem {P : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {z : Fin (n + d) → ℂ} (hz : z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p)) (i : Fin d) :
    z (Fin.natAdd n i) = eval (firstPart z) (p i) := by
  have h := hz (X (Fin.natAdd n i) - rename (Fin.castAdd d) (p i)) (by
    show graphSubst p (X (Fin.natAdd n i) - rename (Fin.castAdd d) (p i)) ∈ P
    rw [map_sub, graphSubst_rename, graphSubst, aeval_X, Fin.append_right, sub_self]
    exact P.zero_mem)
  rw [map_sub, eval_X, eval_rename, sub_eq_zero] at h
  exact h

/- English proof (translation)
Use function extensionality and compare the values at `k`. Use `Fin.addCases (fun j => ?_) (fun i => ?_) k` and prove the remaining obligations. Simplify using `[graphPt, firstPart, Fin.append_left]`. Rewrite using `[natAdd_of_mem hz i, graphPt_natAdd]`.
-/
theorem eq_graphPt_of_mem {P : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {z : Fin (n + d) → ℂ} (hz : z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p)) :
    z = graphPt p (firstPart z) := by
  funext k
  refine Fin.addCases (fun j => ?_) (fun i => ?_) k
  · simp [graphPt, firstPart, Fin.append_left]
  · rw [natAdd_of_mem hz i, graphPt_natAdd]

/- English proof (translation)
Introduce `n d P p x hP hdim hx ⟨W, hW, hiso⟩ W' hW'`. Establish `hV : IndefiniteRowSideFullHecke.ComplexSets.IsAffVariety (graphIdeal P p) d` using `⟨isPrime_graphIdeal hP p, by rw [ringKrullDim_graphIdeal]; exact hdim⟩`. Establish `hAx : lastRows n d *ᵥ graphPt p x = fun i => eval x (p i)`. Rewrite using `[lastRows_mulVec]`. Use function extensionality and compare the values at `i`.

Conclude with `graphPt_natAdd p x i`. Establish `hN : ∀ U ∈ 𝓝 x, firstPart ⁻¹' U ∈ 𝓝 (graphPt p x)` using `fun U hU => continuous_firstPart.continuousAt.preimage_mem_nhds (by rw [firstPart_graphPt]; exact hU)`. Establish `hisoG : ∀ z ∈ firstPart ⁻¹' W, z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p) → lastRows n d *ᵥ z = lastRows n d *ᵥ graphPt p x → z = graphPt p x`. Introduce `z hzW hz hAz`. Establish `hfz : firstPart z = x`.

Use `hiso _ ⟨firstPart_mem hz, hzW⟩ fun i => ?_` and prove the remaining obligations. Establish `h` using `congrFun hAz i`. Rewrite `h` using `[lastRows_mulVec, lastRows_mulVec]`. Simplify using `only at h`. Rewrite `h` using `[natAdd_of_mem hz, graphPt_natAdd]`.

Conclude with `h`. Rewrite using `[eq_graphPt_of_mem hz, hfz]`. Establish `h` using `hOpen (n + d) d (graphIdeal P p) (lastRows n d) (graphPt p x) hV (graphPt_mem p hx) ⟨firstPart ⁻¹' W, hN W hW, hisoG⟩ (firstPart ⁻¹' W') (hN W' hW')`. Rewrite `h` using `[hAx]`. Use `Filter.mem_of_superset h ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨z, ⟨hz, hzW'⟩, rfl⟩`. Use `⟨firstPart z, ⟨firstPart_mem hz, hzW'⟩, ?_⟩` and prove the remaining obligations. Use `show (fun i => eval (firstPart z) (p i)) = lastRows n d *ᵥ z`. Rewrite using `[lastRows_mulVec]`. Use function extensionality and compare the values at `i`.

Conclude with `(natAdd_of_mem hz i).symm`.
-/
theorem proof (hOpen : IndefiniteRowSideFullHecke.ComplexSets.IsolatedFibreOpen.Statement) : IsolatedFibreOpenPoly.Statement := by
  intro n d P p x hP hdim hx ⟨W, hW, hiso⟩ W' hW'
  have hV : IndefiniteRowSideFullHecke.ComplexSets.IsAffVariety (graphIdeal P p) d :=
    ⟨isPrime_graphIdeal hP p, by rw [ringKrullDim_graphIdeal]; exact hdim⟩
  have hAx : lastRows n d *ᵥ graphPt p x = fun i => eval x (p i) := by
    rw [lastRows_mulVec]
    funext i
    exact graphPt_natAdd p x i
  have hN : ∀ U ∈ 𝓝 x, firstPart ⁻¹' U ∈ 𝓝 (graphPt p x) := fun U hU =>
    continuous_firstPart.continuousAt.preimage_mem_nhds (by rw [firstPart_graphPt]; exact hU)
  have hisoG : ∀ z ∈ firstPart ⁻¹' W, z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p) →
      lastRows n d *ᵥ z = lastRows n d *ᵥ graphPt p x → z = graphPt p x := by
    intro z hzW hz hAz
    have hfz : firstPart z = x := by
      refine hiso _ ⟨firstPart_mem hz, hzW⟩ fun i => ?_
      have h := congrFun hAz i
      rw [lastRows_mulVec, lastRows_mulVec] at h
      simp only at h
      rw [natAdd_of_mem hz, graphPt_natAdd] at h
      exact h
    rw [eq_graphPt_of_mem hz, hfz]
  have h := hOpen (n + d) d (graphIdeal P p) (lastRows n d) (graphPt p x) hV (graphPt_mem p hx)
    ⟨firstPart ⁻¹' W, hN W hW, hisoG⟩ (firstPart ⁻¹' W') (hN W' hW')
  rw [hAx] at h
  refine Filter.mem_of_superset h ?_
  rintro _ ⟨z, ⟨hz, hzW'⟩, rfl⟩
  refine ⟨firstPart z, ⟨firstPart_mem hz, hzW'⟩, ?_⟩
  show (fun i => eval (firstPart z) (p i)) = lastRows n d *ᵥ z
  rw [lastRows_mulVec]
  funext i
  exact (natAdd_of_mem hz i).symm

end IsolatedFibreOpenPoly

end

end GroundTheory.Heights₂.Heights
