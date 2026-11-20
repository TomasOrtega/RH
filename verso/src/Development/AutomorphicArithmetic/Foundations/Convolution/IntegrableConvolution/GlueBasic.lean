import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt

noncomputable section

open PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped Fin.NatCast Fin.CommRing

namespace UpperTheory.ConvolutionTheory.L1

section SlopeTestRemainingChoices

variable {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
  {ι : R →+* S} {s : S →+* S} {m : ℕ} (D : Split ι s m) (n : ℕ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem comp_apply (i : Fin (m + 1)) (x : GL (Fin n) S) (a b : Fin n) :
    (D.comp n i x : Matrix (Fin n) (Fin n) R) a b = D.e ((x : Matrix (Fin n) (Fin n) S) a b) i := rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b`. Rewrite using `[comp_apply]`. Use `show D.e (D.e.symm fun i => (g i : Matrix (Fin n) (Fin n) R) a b) i = _`. Simplify using the standard rewrite rules.
-/
private theorem comp_glue (g : Fin (m + 1) → GL (Fin n) R) (i : Fin (m + 1)) :
    D.comp n i (D.glue n g) = g i := by
  apply Units.ext
  ext a b
  rw [comp_apply]
  show D.e (D.e.symm fun i => (g i : Matrix (Fin n) (Fin n) R) a b) i = _
  simp

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b`. Use `show D.e.symm (fun i => (D.comp n i x : Matrix (Fin n) (Fin n) R) a b) = _`. Simplify using `only [comp_apply]`. Conclude with `D.e.symm_apply_apply _`.
-/
private theorem glue_comp (x : GL (Fin n) S) : D.glue n (fun i => D.comp n i x) = x := by
  apply Units.ext
  ext a b
  show D.e.symm (fun i => (D.comp n i x : Matrix (Fin n) (Fin n) R) a b) = _
  simp only [comp_apply]
  exact D.e.symm_apply_apply _

/- English proof (translation)
Rewrite using `[← glue_comp D n x, ← glue_comp D n y]`. Conclude with `congrArg _ (funext h)`.
-/
private theorem comp_inj {x y : GL (Fin n) S} (h : ∀ i, D.comp n i x = D.comp n i y) : x = y := by
  rw [← glue_comp D n x, ← glue_comp D n y]
  exact congrArg _ (funext h)

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b`. Rewrite using `[comp_apply]`. Conclude with `D.map_diag _ i`.
-/
private theorem comp_diag (t : GL (Fin n) R) (i : Fin (m + 1)) : D.comp n i (mapGL n ι t) = t := by
  apply Units.ext
  ext a b
  rw [comp_apply]
  exact D.map_diag _ i

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b`. Rewrite using `[comp_apply, comp_apply]`. Conclude with `D.map_shift _ i`.
-/
private theorem comp_shift (x : GL (Fin n) S) (i : Fin (m + 1)) :
    D.comp n i (mapGL n s x) = D.comp n (i + 1) x := by
  apply Units.ext
  ext a b
  rw [comp_apply, comp_apply]
  exact D.map_shift _ i

/- English proof (translation)
Proceed by induction on `k generalizing i with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ']`. Use `show D.comp n i (θ ((θ ^ k) x)) = _`.

Rewrite using `[hθ, comp_shift, ih]`. Use `congr 1`. Use `push_cast`. Use `abel_nf`.
-/
private theorem comp_pow (θ : Monoid.End (GL (Fin n) S)) (hθ : ∀ x, θ x = mapGL n s x) (k : ℕ)
    (x : GL (Fin n) S) (i : Fin (m + 1)) :
    D.comp n i ((θ ^ k) x) = D.comp n (i + (k : Fin (m + 1))) x := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    show D.comp n i (θ ((θ ^ k) x)) = _
    rw [hθ, comp_shift, ih]
    congr 1
    push_cast
    abel_nf

/- English proof (translation)
Use `congr 1`. Apply the tactic sequence `apply List.ext_getElem <;> simp`.
-/
private theorem ofFn_range {G : Type} [Monoid G] (k : ℕ) (f : ℕ → G) :
    (List.ofFn fun i : Fin k => f i).prod = ((List.range k).map f).prod := by
  congr 1
  apply List.ext_getElem <;> simp

/- English proof (translation)
Establish `hh : (fun i : Fin (m + 1) => D.comp n (j + i) δ) = fun i : Fin (m + 1) => (fun k : ℕ => D.comp n (j + (k : Fin (m + 1))) δ) i`. Use function extensionality and compare the values at `i`. Simplify using `only [Fin.cast_val_eq_self]`. Rewrite using `[hh, ofFn_range (m + 1) (fun k : ℕ => D.comp n (j + (k : Fin (m + 1))) δ), twNorm, map_list_prod, List.map_map]`. Use `congr 1`.

Apply `List.map_congr_left` to reduce the goal to its premises. Introduce `k _`. Conclude with `comp_pow D n θ hθ k δ j`.
-/
private theorem comp_twNorm (θ : Monoid.End (GL (Fin n) S)) (hθ : ∀ x, θ x = mapGL n s x)
    (δ : GL (Fin n) S) (j : Fin (m + 1)) :
    D.comp n j (twNorm θ (m + 1) δ) = (List.ofFn fun i => D.comp n (j + i) δ).prod := by
  have hh : (fun i : Fin (m + 1) => D.comp n (j + i) δ) =
      fun i : Fin (m + 1) => (fun k : ℕ => D.comp n (j + (k : Fin (m + 1))) δ) i := by
    funext i
    simp only [Fin.cast_val_eq_self]
  rw [hh, ofFn_range (m + 1) (fun k : ℕ => D.comp n (j + (k : Fin (m + 1))) δ), twNorm, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  exact comp_pow D n θ hθ k δ j

/- English proof (translation)
The claim follows from `(Units.continuous_val (M := Matrix (Fin n) (Fin n) T)).matrix_elem a b`.
-/
private theorem entry {T : Type} [CommRing T] [TopologicalSpace T] (a b : Fin n) :
    Continuous fun x : GL (Fin n) T => (x : Matrix (Fin n) (Fin n) T) a b :=
  (Units.continuous_val (M := Matrix (Fin n) (Fin n) T)).matrix_elem a b

/- English proof (translation)
The claim follows from `(Units.continuous_iff.mp (continuous_id (X := GL (Fin n) T))).2.matrix_elem a b`.
-/
private theorem entryInv {T : Type} [CommRing T] [TopologicalSpace T] (a b : Fin n) :
    Continuous fun x : GL (Fin n) T => ((x⁻¹ : GL (Fin n) T) : Matrix (Fin n) (Fin n) T) a b :=
  (Units.continuous_iff.mp (continuous_id (X := GL (Fin n) T))).2.matrix_elem a b

/- English proof (translation)
Rewrite using `[List.ofFn_succ, List.ofFn_succ' (f := fun i => c (j + 1 + i))]`. Simplify using `only [List.prod_cons, List.concat_eq_append, List.prod_append, List.prod_nil, mul_one, List.prod_singleton, add_zero, Fin.zero_eta]`. Establish `h1 : ∀ i : Fin m, j + i.succ = j + 1 + i.castSucc` using `fun i => by`. Rewrite using `[← Fin.coeSucc_eq_succ]`. Normalize the expressions using the abelian group laws.

Establish `h2 : j + 1 + Fin.last m = j`. Rewrite using `[add_assoc, add_comm 1, Fin.last_add_one, add_zero]`. Simplify using `only [h1, h2, mul_assoc]`.
-/
private theorem norm_shift {G : Type} [Group G] (c : Fin (m + 1) → G) (j : Fin (m + 1)) :
    (List.ofFn fun i => c (j + i)).prod * c j = c j * (List.ofFn fun i => c (j + 1 + i)).prod := by
  rw [List.ofFn_succ, List.ofFn_succ' (f := fun i => c (j + 1 + i))]
  simp only [List.prod_cons, List.concat_eq_append, List.prod_append, List.prod_nil, mul_one, List.prod_singleton,
    add_zero, Fin.zero_eta]
  have h1 : ∀ i : Fin m, j + i.succ = j + 1 + i.castSucc := fun i => by
    rw [← Fin.coeSucc_eq_succ]
    abel
  have h2 : j + 1 + Fin.last m = j := by
    rw [add_assoc, add_comm 1, Fin.last_add_one, add_zero]
  simp only [h1, h2, mul_assoc]

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory.L1 in
/- English proof (translation)
Introduce `R S _ _ _ _ _ _ ι s m D n`. Use `⟨comp_glue D n, glue_comp D n, ?_, ?_, ?_, comp_diag D n, comp_shift D n, ?_⟩` and prove the remaining obligations. Introduce `g h`. Apply `comp_inj D n` to reduce the goal to its premises. Introduce `i`.

Rewrite using `[map_mul, comp_glue, comp_glue, comp_glue]`. Both sides reduce to the same expression. Use `Units.continuous_iff.mpr ⟨?_, ?_⟩` and prove the remaining obligations. Use `continuous_matrix fun a b => ?_` and prove the remaining obligations. Apply the tactic sequence `exact D.cont_symm.comp (continuous_pi fun i => (entry n a b).comp (continuous_apply i))`.

Use `continuous_matrix fun a b => ?_` and prove the remaining obligations. Conclude with `D.cont_symm.comp (continuous_pi fun i => (entryInv n a b).comp (continuous_apply i))`. Introduce `i`. Use `Units.continuous_iff.mpr ⟨?_, ?_⟩` and prove the remaining obligations. Use `continuous_matrix fun a b => ?_` and prove the remaining obligations.

Apply the tactic sequence `exact (continuous_apply i).comp (D.cont.comp (entry n a b))`. Use `continuous_matrix fun a b => ?_` and prove the remaining obligations. Establish `: (fun x : GL (Fin n) S => (((D.comp n i x)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b) = fun x => D.e (((x⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) a b) i`. Use function extensionality and compare the values at `x`. Rewrite using `[← map_inv, comp_apply]`.

Use `show Continuous (fun x : GL (Fin n) S => (((D.comp n i x)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b)`. Rewrite using `[this]`. Conclude with `(continuous_apply i).comp (D.cont.comp (entryInv n a b))`. Introduce `δ γ`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `N : ∀ j : Fin (m + 1), (List.ofFn fun i => D.comp n (j + i) δ).prod = γ` using `fun j => by`. Rewrite using `[← comp_twNorm D n (mapGL n s) (fun _ => rfl), h, comp_diag]`. Use `⟨fun i => ?_, ?_, N⟩` and prove the remaining obligations. Establish `e` using `norm_shift (fun i => D.comp n i δ) i`.

Rewrite `e` using `[N, N]`. Rewrite using `[Subgroup.mem_centralizer_singleton_iff]`. Conclude with `e.symm`. Simplify using `using N 0`. Introduce and unpack `⟨-, -, N⟩`.

Apply `comp_inj D n` to reduce the goal to its premises. Introduce `j`. Rewrite using `[comp_twNorm D n (mapGL n s) (fun _ => rfl), N, comp_diag]`.
-/
theorem UpperTheory.ConvolutionTheory.L1.glueBasic :
    UpperTheory.ConvolutionTheory.L1.GlueBasic := by
  intro R S _ _ _ _ _ _ ι s m D n
  refine ⟨comp_glue D n, glue_comp D n, ?_, ?_, ?_, comp_diag D n, comp_shift D n, ?_⟩
  · intro g h
    apply comp_inj D n
    intro i
    rw [map_mul, comp_glue, comp_glue, comp_glue]
    rfl
  · refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · refine continuous_matrix fun a b => ?_
      exact D.cont_symm.comp (continuous_pi fun i => (entry n a b).comp (continuous_apply i))
    · refine continuous_matrix fun a b => ?_
      exact D.cont_symm.comp (continuous_pi fun i => (entryInv n a b).comp (continuous_apply i))
  · intro i
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · refine continuous_matrix fun a b => ?_
      exact (continuous_apply i).comp (D.cont.comp (entry n a b))
    · refine continuous_matrix fun a b => ?_
      have : (fun x : GL (Fin n) S => (((D.comp n i x)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b) =
          fun x => D.e (((x⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) a b) i := by
        funext x
        rw [← map_inv, comp_apply]
      show Continuous (fun x : GL (Fin n) S => (((D.comp n i x)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b)
      rw [this]
      exact (continuous_apply i).comp (D.cont.comp (entryInv n a b))
  · intro δ γ
    constructor
    · intro h
      have N : ∀ j : Fin (m + 1), (List.ofFn fun i => D.comp n (j + i) δ).prod = γ := fun j => by
        rw [← comp_twNorm D n (mapGL n s) (fun _ => rfl), h, comp_diag]
      refine ⟨fun i => ?_, ?_, N⟩
      · have e := norm_shift (fun i => D.comp n i δ) i
        rw [N, N] at e
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact e.symm
      · simpa using N 0
    · rintro ⟨-, -, N⟩
      apply comp_inj D n
      intro j
      rw [comp_twNorm D n (mapGL n s) (fun _ => rfl), N, comp_diag]
