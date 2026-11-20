import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDetGenericSumMemOfCharpolyCoeffMem

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.SpanRing

/- English proof (translation)
Unfold `CharPolyIn at h`. Break down `subsingleton_or_nontrivial O with hO | hO` into its components or cases. Establish `hz : (fun x => (mat (rep x) g).charpoly.coeff j) = 0` using `Subsingleton.elim _ _`. Rewrite using `[hz]`. Conclude with `T.zero_mem`.

Distinguish the cases in `hj : j ≤ n`. Establish `e : (fun x => (mat (rep x) g).charpoly.coeff j) = fun x => (mat (rep x) g).charpolyRev.coeff (n - j)`. Use function extensionality and compare the values at `x`. Rewrite using `[← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, Polynomial.revAt_le (Nat.sub_le n j), Nat.sub_sub_self hj]`. Rewrite using `[e]`.

Conclude with `h g (n - j)`. Establish `hz : (fun x => (mat (rep x) g).charpoly.coeff j) = 0`. Use function extensionality and compare the values at `x`. Apply `Polynomial.coeff_eq_zero_of_natDegree_lt` to reduce the goal to its premises. Rewrite using `[Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hz]`. Conclude with `T.zero_mem`.
-/
theorem charpoly_coeff_mem_of_charPolyIn {Γ X O : Type} [Group Γ] [CommRing O] {n : ℕ}
    (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)) (h : CharPolyIn T rep) (g : Γ) (j : ℕ) :
    (fun x => (mat (rep x) g).charpoly.coeff j) ∈ T := by
  unfold CharPolyIn at h
  rcases subsingleton_or_nontrivial O with hO | hO
  · have hz : (fun x => (mat (rep x) g).charpoly.coeff j) = 0 := Subsingleton.elim _ _
    rw [hz]
    exact T.zero_mem
  · by_cases hj : j ≤ n
    · have e : (fun x => (mat (rep x) g).charpoly.coeff j) =
          fun x => (mat (rep x) g).charpolyRev.coeff (n - j) := by
        funext x
        rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim,
          Fintype.card_fin, Polynomial.revAt_le (Nat.sub_le n j), Nat.sub_sub_self hj]
      rw [e]
      exact h g (n - j)
    · have hz : (fun x => (mat (rep x) g).charpoly.coeff j) = 0 := by
        funext x
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
        omega
      rw [hz]
      exact T.zero_mem

/- English proof (translation)
Use `set φ : MvPolynomial (Fin m) (X → O) →+* MvPolynomial (Fin m) O := MvPolynomial.map (Pi.evalRingHom (fun _ => O) x) with hφ`. Establish `h1 : φ.mapMatrix (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) • Matrix.of (fun i j => MvPolynomial.C (fun y => a k y i j))) = ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations.

Simplify using `[hφ]`. Rewrite using `[← h1, ← RingHom.map_det, hφ, MvPolynomial.coeff_map]`. Both sides reduce to the same expression.
-/
private theorem coeff_det_generic_sum_eval {X O : Type} [CommRing O] {n m : ℕ}
    (a : Fin m → X → Matrix (Fin n) (Fin n) O) (x : X) (d : Fin m →₀ ℕ) :
    MvPolynomial.coeff d (Matrix.det (∑ k,
      (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C)) =
    (MvPolynomial.coeff d (Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) •
      Matrix.of (fun i j => MvPolynomial.C (fun y => a k y i j)))) : X → O) x := by
  set φ : MvPolynomial (Fin m) (X → O) →+* MvPolynomial (Fin m) O :=
    MvPolynomial.map (Pi.evalRingHom (fun _ => O) x) with hφ
  have h1 : φ.mapMatrix (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) •
      Matrix.of (fun i j => MvPolynomial.C (fun y => a k y i j))) =
      ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Matrix.ext fun i j => ?_
    simp [hφ]
  rw [← h1, ← RingHom.map_det, hφ, MvPolynomial.coeff_map]
  rfl

/- English proof (translation)
Introduce `Γ X O _ _ n T rep hT m a ha d`. Set `T' : Subring (MvPolynomial (Fin m) (X → O))` to `(MvPolynomial.map T.val.toRingHom).range`. Establish `hmemT : ∀ p ∈ T', ∀ e, MvPolynomial.coeff e p ∈ T`. Introduce `p hp e`. Take `⟨q, rfl⟩` from `RingHom.mem_range.1 hp`.

Rewrite using `[MvPolynomial.coeff_map]`. Conclude with `(MvPolynomial.coeff e q).2`. Establish `hC : ∀ f ∈ T, (MvPolynomial.C f : MvPolynomial (Fin m) (X → O)) ∈ T'` using `fun f hf => RingHom.mem_range.2 ⟨MvPolynomial.C ⟨f, hf⟩, by simp⟩`. Establish `hX : ∀ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) ∈ T'` using `fun k => RingHom.mem_range.2 ⟨MvPolynomial.X k, by simp⟩`. Set `M : Γ → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O))` to `fun h => Matrix.of fun i j => MvPolynomial.C (fun y => mat (rep y) h i j)`.

Establish `hmul : ∀ A ∈ Set.range M, ∀ B ∈ Set.range M, A * B ∈ Set.range M`. Introduce and unpack `_ ⟨g, rfl⟩ _ ⟨h, rfl⟩`. Use `⟨g * h, ?_⟩` and prove the remaining obligations. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [M, Matrix.mul_apply, Matrix.of_apply, ← map_mul, ← map_sum]`.

Use `congr 1`. Use function extensionality and compare the values at `y`. Simplify using `[mat, Matrix.mul_apply, Finset.sum_apply]`. Establish `hchar : ∀ A ∈ Set.range M, ∀ j, A.charpoly.coeff j ∈ T'`. Introduce and unpack `_ ⟨h, rfl⟩ j`.

Establish `hP : M h = (Matrix.of fun i j => fun y => mat (rep y) h i j).map MvPolynomial.C`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Both sides reduce to the same expression. Rewrite using `[hP, Matrix.charpoly_map, Polynomial.coeff_map]`. Apply `hC` to reduce the goal to its premises.

Establish `e : (Matrix.of fun i j => fun y => mat (rep y) h i j).charpoly.coeff j = fun y => (mat (rep y) h).charpoly.coeff j`. Use function extensionality and compare the values at `y`. Establish `hm : (Matrix.of fun i j => fun y => mat (rep y) h i j).map (Pi.evalRingHom (fun _ => O) y) = mat (rep y) h`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Both sides reduce to the same expression.

Establish `e'` using `congrArg (fun p => Polynomial.coeff p j) (Matrix.charpoly_map (Matrix.of fun i j => fun y => mat (rep y) h i j) (Pi.evalRingHom (fun _ => O) y))`. Rewrite `e'` using `[hm]`. Simplify using `only [Polynomial.coeff_map] at e'`. Conclude with `e'.symm`. Rewrite using `[e]`.

Conclude with `charpoly_coeff_mem_of_charPolyIn T rep hT h j`. Establish `hlift : ∀ b : X → Matrix (Fin n) (Fin n) O, b ∈ Submodule.span O (gens T rep) → (Matrix.of fun i j => MvPolynomial.C (fun y => b y i j) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O))) ∈ Submodule.span T' (Set.range M)`. Introduce `b hb`. Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem b hb`.

Take `⟨f, hf, h, rfl⟩` from `hb`. Establish `e : (Matrix.of fun i j => MvPolynomial.C (fun y => (fun x => f x • mat (rep x) h) y i j) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O))) = (⟨MvPolynomial.C f, hC f hf⟩ : T') • M h`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.of_apply, Subring.smul_def, Matrix.smul_apply, smul_eq_mul, M, ← map_mul]`. Use `congr 1`.

Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, rfl⟩)`. Consider the case `zero`. Establish `e : (Matrix.of fun i j => MvPolynomial.C (fun y => (0 : X → Matrix (Fin n) (Fin n) O) y i j) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O))) = 0`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations.

Simplify using `only [Matrix.of_apply, Pi.zero_apply, Matrix.zero_apply]`. Conclude with `map_zero _`. Rewrite using `[e]`. Conclude with `Submodule.zero_mem _`. Consider the case `add b c _ _ hb hc`.

Establish `e : (Matrix.of fun i j => MvPolynomial.C (fun y => (b + c) y i j) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O))) = Matrix.of (fun i j => MvPolynomial.C (fun y => b y i j)) + Matrix.of (fun i j => MvPolynomial.C (fun y => c y i j))`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.of_apply, Matrix.add_apply, ← map_add]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `Submodule.add_mem _ hb hc`. Consider the case `smul r b _ hb`. Establish `e : (Matrix.of fun i j => MvPolynomial.C (fun y => (r • b) y i j) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O))) = (⟨MvPolynomial.C (algebraMap O (X → O) r), hC _ (T.algebraMap_mem r)⟩ : T') • Matrix.of (fun i j => MvPolynomial.C (fun y => b y i j))`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.of_apply, Subring.smul_def, Matrix.smul_apply, smul_eq_mul, ← map_mul]`.

Use `congr 1`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ hb`. Establish `hB : (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) • Matrix.of (fun i j => MvPolynomial.C (fun y => a k y i j))) ∈ Submodule.span T' (Set.range M)`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations.

Use `Submodule.smul_mem (Submodule.span T' (Set.range M)) (⟨MvPolynomial.X k, hX k⟩ : T') (hlift (a k) ((inRing_iff_mem_span T rep (a k)).1 (ha k)))` as an intermediate fact. Conclude with `this`. Take `⟨N, f, g, hfg⟩` from `Submodule.mem_span_set'.1 hB`. Establish `hdet` using `Amitsur.det_sum_smul_mem T' (Set.range M) hmul hchar Finset.univ (fun i => (f i : MvPolynomial (Fin m) (X → O))) (fun i => (g i).1) (fun i => (f i).2) (fun i => (g i).2)`. Establish `hsum : (∑ i ∈ Finset.univ, (f i : MvPolynomial (Fin m) (X → O)) • (g i).1) = ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) • Matrix.of (fun i j => MvPolynomial.C (fun y => a k y i j))`.

Rewrite using `[← hfg]`. Both sides reduce to the same expression. Rewrite `hdet` using `[hsum]`. Establish `key : (fun x => MvPolynomial.coeff d (Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C))) = MvPolynomial.coeff d (Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) • Matrix.of (fun i j => MvPolynomial.C (fun y => a k y i j …`. Use function extensionality and compare the values at `fun x => coeff_det_generic_sum_eval a x d`.

Rewrite using `[key]`. Conclude with `hmemT _ hdet d`.
-/
theorem coeff_det_generic_sum_mem_of_inRing :
    ∀ {Γ X O : Type} [Group Γ] [CommRing O] {n : ℕ} (T : Subalgebra O (X → O))
      (rep : X → (Γ →* GL (Fin n) O)), CharPolyIn T rep →
      ∀ (m : ℕ) (a : Fin m → X → Matrix (Fin n) (Fin n) O), (∀ k, InRing T rep (a k)) →
      ∀ d : Fin m →₀ ℕ, (fun x => MvPolynomial.coeff d (Matrix.det (∑ k,
        (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C))) ∈ T := by
  intro Γ X O _ _ n T rep hT m a ha d
  classical

  let T' : Subring (MvPolynomial (Fin m) (X → O)) := (MvPolynomial.map T.val.toRingHom).range
  have hmemT : ∀ p ∈ T', ∀ e, MvPolynomial.coeff e p ∈ T := by
    intro p hp e
    obtain ⟨q, rfl⟩ := RingHom.mem_range.1 hp
    rw [MvPolynomial.coeff_map]
    exact (MvPolynomial.coeff e q).2
  have hC : ∀ f ∈ T, (MvPolynomial.C f : MvPolynomial (Fin m) (X → O)) ∈ T' := fun f hf =>
    RingHom.mem_range.2 ⟨MvPolynomial.C ⟨f, hf⟩, by simp⟩
  have hX : ∀ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) ∈ T' := fun k =>
    RingHom.mem_range.2 ⟨MvPolynomial.X k, by simp⟩

  let M : Γ → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O)) :=
    fun h => Matrix.of fun i j => MvPolynomial.C (fun y => mat (rep y) h i j)
  have hmul : ∀ A ∈ Set.range M, ∀ B ∈ Set.range M, A * B ∈ Set.range M := by
    rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
    refine ⟨g * h, ?_⟩
    refine Matrix.ext fun i j => ?_
    simp only [M, Matrix.mul_apply, Matrix.of_apply, ← map_mul, ← map_sum]
    congr 1
    funext y
    simp [mat, Matrix.mul_apply, Finset.sum_apply]
  have hchar : ∀ A ∈ Set.range M, ∀ j, A.charpoly.coeff j ∈ T' := by
    rintro _ ⟨h, rfl⟩ j
    have hP : M h = (Matrix.of fun i j => fun y => mat (rep y) h i j).map MvPolynomial.C := by
      refine Matrix.ext fun i j => ?_
      rfl
    rw [hP, Matrix.charpoly_map, Polynomial.coeff_map]
    apply hC
    have e : (Matrix.of fun i j => fun y => mat (rep y) h i j).charpoly.coeff j =
        fun y => (mat (rep y) h).charpoly.coeff j := by
      funext y
      have hm : (Matrix.of fun i j => fun y => mat (rep y) h i j).map (Pi.evalRingHom (fun _ => O) y) =
          mat (rep y) h := by
        refine Matrix.ext fun i j => ?_
        rfl
      have e' := congrArg (fun p => Polynomial.coeff p j)
        (Matrix.charpoly_map (Matrix.of fun i j => fun y => mat (rep y) h i j) (Pi.evalRingHom (fun _ => O) y))
      rw [hm] at e'
      simp only [Polynomial.coeff_map] at e'
      exact e'.symm
    rw [e]
    exact charpoly_coeff_mem_of_charPolyIn T rep hT h j

  have hlift : ∀ b : X → Matrix (Fin n) (Fin n) O, b ∈ Submodule.span O (gens T rep) →
      (Matrix.of fun i j => MvPolynomial.C (fun y => b y i j) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O)))
        ∈ Submodule.span T' (Set.range M) := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨f, hf, h, rfl⟩ := hb
      have e : (Matrix.of fun i j => MvPolynomial.C (fun y => (fun x => f x • mat (rep x) h) y i j) :
          Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O))) =
          (⟨MvPolynomial.C f, hC f hf⟩ : T') • M h := by
        refine Matrix.ext fun i j => ?_
        simp only [Matrix.of_apply, Subring.smul_def, Matrix.smul_apply, smul_eq_mul, M, ← map_mul]
        congr 1
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, rfl⟩)
    | zero =>
      have e : (Matrix.of fun i j => MvPolynomial.C (fun y => (0 : X → Matrix (Fin n) (Fin n) O) y i j) :
          Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O))) = 0 := by
        refine Matrix.ext fun i j => ?_
        simp only [Matrix.of_apply, Pi.zero_apply, Matrix.zero_apply]
        exact map_zero _
      rw [e]
      exact Submodule.zero_mem _
    | add b c _ _ hb hc =>
      have e : (Matrix.of fun i j => MvPolynomial.C (fun y => (b + c) y i j) :
          Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O))) =
          Matrix.of (fun i j => MvPolynomial.C (fun y => b y i j)) +
            Matrix.of (fun i j => MvPolynomial.C (fun y => c y i j)) := by
        refine Matrix.ext fun i j => ?_
        simp only [Matrix.of_apply, Matrix.add_apply, ← map_add]
        rfl
      rw [e]
      exact Submodule.add_mem _ hb hc
    | smul r b _ hb =>
      have e : (Matrix.of fun i j => MvPolynomial.C (fun y => (r • b) y i j) :
          Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O))) =
          (⟨MvPolynomial.C (algebraMap O (X → O) r), hC _ (T.algebraMap_mem r)⟩ : T') •
            Matrix.of (fun i j => MvPolynomial.C (fun y => b y i j)) := by
        refine Matrix.ext fun i j => ?_
        simp only [Matrix.of_apply, Subring.smul_def, Matrix.smul_apply, smul_eq_mul, ← map_mul]
        congr 1
      rw [e]
      exact Submodule.smul_mem _ _ hb
  have hB : (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) •
      Matrix.of (fun i j => MvPolynomial.C (fun y => a k y i j))) ∈ Submodule.span T' (Set.range M) := by
    refine Submodule.sum_mem _ fun k _ => ?_
    have := Submodule.smul_mem (Submodule.span T' (Set.range M)) (⟨MvPolynomial.X k, hX k⟩ : T')
      (hlift (a k) ((inRing_iff_mem_span T rep (a k)).1 (ha k)))
    exact this
  obtain ⟨N, f, g, hfg⟩ := Submodule.mem_span_set'.1 hB
  have hdet := Amitsur.det_sum_smul_mem T' (Set.range M) hmul hchar Finset.univ
    (fun i => (f i : MvPolynomial (Fin m) (X → O))) (fun i => (g i).1)
    (fun i => (f i).2) (fun i => (g i).2)
  have hsum : (∑ i ∈ Finset.univ, (f i : MvPolynomial (Fin m) (X → O)) • (g i).1) =
      ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) •
        Matrix.of (fun i j => MvPolynomial.C (fun y => a k y i j)) := by
    rw [← hfg]
    rfl
  rw [hsum] at hdet
  have key : (fun x => MvPolynomial.coeff d (Matrix.det (∑ k,
      (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C))) =
      MvPolynomial.coeff d (Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) •
        Matrix.of (fun i j => MvPolynomial.C (fun y => a k y i j)))) :=
    funext fun x => coeff_det_generic_sum_eval a x d
  rw [key]
  exact hmemT _ hdet d

end GlobalTheory.SpanRing
