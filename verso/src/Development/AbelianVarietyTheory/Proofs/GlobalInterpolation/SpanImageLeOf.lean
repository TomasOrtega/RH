import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

noncomputable section

namespace GlobalTheory.IdealTransport

section General

variable {R R' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R' M']
  (φ : R ≃+* R') (f : M ≃+ M') (h : ∀ r m, f (r • m) = φ r • f m)

include h

/- English proof (translation)
Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨m, hm, rfl⟩`. Use `show f m ∈ N'`. Establish `hm' : m ∈ Submodule.span R S` using `hS ▸ hm`. Use `clear hm`.

Proceed by induction on `hm' using Submodule.span_induction with`. Consider the case `mem x hx => exact hN x hx`. Consider the case `zero => rw [map_zero]`. Conclude with `N'.zero_mem`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `N'.add_mem hx hy`. Consider the case `smul r x _ hx => rw [h]`. Conclude with `N'.smul_mem _ hx`.
-/
theorem span_image_le_of (N : Submodule R M) (N' : Submodule R' M') (S : Set M) (hS : N = Submodule.span R S)
    (hN : ∀ m ∈ S, f m ∈ N') : Submodule.span R' (f '' (N : Set M)) ≤ N' := by
  rw [Submodule.span_le]
  rintro _ ⟨m, hm, rfl⟩
  show f m ∈ N'
  have hm' : m ∈ Submodule.span R S := hS ▸ hm
  clear hm
  induction hm' using Submodule.span_induction with
  | mem x hx => exact hN x hx
  | zero => rw [map_zero]; exact N'.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact N'.add_mem hx hy
  | smul r x _ hx => rw [h]; exact N'.smul_mem _ hx

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Conclude with `span_image_le_of φ f h _ _ S rfl fun m hm => Submodule.subset_span ⟨m, hm, rfl⟩`. Conclude with `Submodule.span_mono (Set.image_mono Submodule.subset_span)`.
-/
theorem span_image_span (S : Set M) :
    Submodule.span R' (f '' (Submodule.span R S : Set M)) = Submodule.span R' (f '' S) := by
  apply le_antisymm
  · exact span_image_le_of φ f h _ _ S rfl fun m hm => Submodule.subset_span ⟨m, hm, rfl⟩
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

/- English proof (translation)
Establish `hsm : ∀ (r : R') (y : M'), f.symm (r • y) = φ.symm r • f.symm y`. Introduce `r y`. Apply `f.injective` to reduce the goal to its premises. Rewrite using `[h, AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨m, hm, rfl⟩` from `hy`. Simplify using `using hm`.

Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `N.add_mem hy hz`. Consider the case `smul r y _ hy => rw [hsm]`. Conclude with `N.smul_mem _ hy`.

Introduce `hx`. Conclude with `Submodule.subset_span ⟨f.symm x, hx, by simp⟩`.
-/
theorem mem_span_image (N : Submodule R M) (x : M') :
    x ∈ Submodule.span R' (f '' (N : Set M)) ↔ f.symm x ∈ N := by
  have hsm : ∀ (r : R') (y : M'), f.symm (r • y) = φ.symm r • f.symm y := by
    intro r y
    apply f.injective
    rw [h, AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, hm, rfl⟩ := hy
      simpa using hm
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact N.add_mem hy hz
    | smul r y _ hy => rw [hsm]; exact N.smul_mem _ hy
  · intro hx
    exact Submodule.subset_span ⟨f.symm x, hx, by simp⟩

end General

section Fields

variable {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] (e : E ≃+* E')

/- English proof (translation)
Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul]`. Both sides reduce to the same expression.
-/
theorem map_smul_int (r : 𝓞 E) (x : E) : e (r • x) = RingOfIntegers.mapRingEquiv e r • e x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  rfl

abbrev trI (I : Submodule (𝓞 E) E) : Submodule (𝓞 E') E' := Submodule.span (𝓞 E') (e '' (I : Set E))

abbrev trL {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E') (Fin n → E') :=
  Submodule.span (𝓞 E') ((fun (x : Fin n → E) (i : Fin n) => e (x i)) '' (N : Set (Fin n → E)))

/- English proof (translation)
The claim follows from `mem_span_image (RingOfIntegers.mapRingEquiv e) e.toAddEquiv (map_smul_int e) I x`.
-/
theorem mem_trI (I : Submodule (𝓞 E) E) (x : E') : x ∈ trI e I ↔ e.symm x ∈ I := mem_span_image (RingOfIntegers.mapRingEquiv e) e.toAddEquiv (map_smul_int e) I x

/- English proof (translation)
The claim follows from `span_image_span (RingOfIntegers.mapRingEquiv e) e.toAddEquiv (map_smul_int e) S`.
-/
theorem trI_span (S : Set E) : trI e (Submodule.span (𝓞 E) S) = Submodule.span (𝓞 E') (e '' S) := span_image_span (RingOfIntegers.mapRingEquiv e) e.toAddEquiv (map_smul_int e) S

/- English proof (translation)
The claim follows from `mem_span_image (RingOfIntegers.mapRingEquiv e) (AddEquiv.piCongrRight fun _ : Fin n => e.toAddEquiv) (fun r v => funext fun i => map_smul_int e r (v i)) N x`.
-/
theorem mem_trL {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E') :
    x ∈ trL e N ↔ (fun i => e.symm (x i)) ∈ N := mem_span_image (RingOfIntegers.mapRingEquiv e) (AddEquiv.piCongrRight fun _ : Fin n => e.toAddEquiv)
    (fun r v => funext fun i => map_smul_int e r (v i)) N x

/- English proof (translation)
Rewrite using `[Submodule.mul_eq_span_mul_set I J, trI_span, Set.image_mul]`. Conclude with `(Submodule.span_mul_span _ _ _).symm`.
-/
theorem trI_mul (I J : Submodule (𝓞 E) E) : trI e (I * J) = trI e I * trI e J := by
  rw [Submodule.mul_eq_span_mul_set I J, trI_span, Set.image_mul]
  exact (Submodule.span_mul_span _ _ _).symm

/- English proof (translation)
Rewrite using `[trI_span, Set.image_singleton]`.
-/
theorem trI_singleton (y : E) : trI e (Submodule.span (𝓞 E) {y}) = Submodule.span (𝓞 E') {e y} := by
  rw [trI_span, Set.image_singleton]

/- English proof (translation)
Use `conv_lhs => rw [Submodule.one_eq_span]`. Rewrite using `[trI_singleton, map_one, ← Submodule.one_eq_span]`.
-/
theorem trI_one : trI e 1 = 1 := by
  conv_lhs => rw [Submodule.one_eq_span]
  rw [trI_singleton, map_one, ← Submodule.one_eq_span]

/- English proof (translation)
Use `⟨Submodule.span (𝓞 E) (e.symm '' (J : Set E')), ?_⟩` and prove the remaining obligations. Rewrite using `[trI_span, Set.image_image]`. Simplify using `only [RingEquiv.apply_symm_apply, Set.image_id']`. Conclude with `Submodule.span_eq J`.
-/
theorem trI_surj (J : Submodule (𝓞 E') E') : ∃ I, trI e I = J := by
  refine ⟨Submodule.span (𝓞 E) (e.symm '' (J : Set E')), ?_⟩
  rw [trI_span, Set.image_image]
  simp only [RingEquiv.apply_symm_apply, Set.image_id']
  exact Submodule.span_eq J

/- English proof (translation)
Rewrite using `[← trI_one e, mem_trI]`.
-/
theorem mem_one_iff (x : E') : x ∈ (1 : Submodule (𝓞 E') E') ↔ e.symm x ∈ (1 : Submodule (𝓞 E) E) := by
  rw [← trI_one e, mem_trI]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, map_sum]`.
-/
theorem map_mulVec' {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (v : Fin n → E) :
    (A.map e).mulVec (fun i => e (v i)) = fun i => e (A.mulVec v i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum]

/- English proof (translation)
The claim follows from `(RingHom.map_det (e : E →+* E') A).symm`.
-/
theorem det_map' {n : ℕ} (A : Matrix (Fin n) (Fin n) E) : (A.map e).det = e A.det := (RingHom.map_det (e : E →+* E') A).symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `H v hv`. Establish `hv' : (fun i => e (v i)) ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E') E'))`. Rewrite `hv`, the goal using `[Submodule.mem_pi]`. Introduce `i hi`.

Rewrite using `[mem_one_iff e, RingEquiv.symm_apply_apply]`. Conclude with `hv i hi`. Establish `hA` using `H _ hv'`. Rewrite `hA` using `[map_mulVec' e A v, mem_trL]`. Simplify using `using hA`.

Introduce `H v hv`. Establish `hv' : (fun i => e.symm (v i)) ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E))`. Rewrite `hv`, the goal using `[Submodule.mem_pi]`. Introduce `i hi`. Rewrite using `[← mem_one_iff e]`.

Conclude with `hv i hi`. Establish `hmv : (A.map e).mulVec v = fun i => e (A.mulVec (fun i => e.symm (v i)) i)`. Establish `hk` using `map_mulVec' e A (fun i => e.symm (v i))`. Simplify using `only [RingEquiv.apply_symm_apply] at hk`. Conclude with `hk`.

Rewrite using `[hmv, mem_trL]`. Simplify using `using H _ hv'`.
-/
theorem carries_iff {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E)) (A : Matrix (Fin n) (Fin n) E) :
    (∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E') E')), (A.map e).mulVec v ∈ trL e N) ↔
      ∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)), A.mulVec v ∈ N := by
  constructor
  · intro H v hv
    have hv' : (fun i => e (v i)) ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E') E')) := by
      rw [Submodule.mem_pi] at hv ⊢
      intro i hi
      rw [mem_one_iff e, RingEquiv.symm_apply_apply]
      exact hv i hi
    have hA := H _ hv'
    rw [map_mulVec' e A v, mem_trL] at hA
    simpa using hA
  · intro H v hv
    have hv' : (fun i => e.symm (v i)) ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) := by
      rw [Submodule.mem_pi] at hv ⊢
      intro i hi
      rw [← mem_one_iff e]
      exact hv i hi
    have hmv : (A.map e).mulVec v = fun i => e (A.mulVec (fun i => e.symm (v i)) i) := by
      have hk := map_mulVec' e A (fun i => e.symm (v i))
      simp only [RingEquiv.apply_symm_apply] at hk
      exact hk
    rw [hmv, mem_trL]
    simpa using H _ hv'

/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨A', hA', rfl⟩`. Establish `hmap : (A'.map e.symm).map e = A'`. Use extensionality with `i j`.

Simplify using the standard rewrite rules. Use `⟨(A'.map e.symm).det, ⟨A'.map e.symm, ?_, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← carries_iff e N, hmap]`. Conclude with `hA'`. Rewrite using `[← det_map', hmap]`.

Introduce and unpack `⟨y, ⟨A, hA, rfl⟩, rfl⟩`. Conclude with `⟨A.map e, (carries_iff e N A).mpr hA, (det_map' e A).symm⟩`.
-/
theorem det_set {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E)) :
    {x | ∃ A : Matrix (Fin n) (Fin n) E', (∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E') E')),
        A.mulVec v ∈ trL e N) ∧ x = A.det} =
      e '' {x | ∃ A : Matrix (Fin n) (Fin n) E, (∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)),
        A.mulVec v ∈ N) ∧ x = A.det} := by
  ext x
  constructor
  · rintro ⟨A', hA', rfl⟩
    have hmap : (A'.map e.symm).map e = A' := by
      ext i j
      simp
    refine ⟨(A'.map e.symm).det, ⟨A'.map e.symm, ?_, rfl⟩, ?_⟩
    · rw [← carries_iff e N, hmap]
      exact hA'
    · rw [← det_map', hmap]
  · rintro ⟨y, ⟨A, hA, rfl⟩, rfl⟩
    exact ⟨A.map e, (carries_iff e N A).mpr hA, (det_map' e A).symm⟩

end Fields

/- English proof (translation)
Introduce `D X s`. Use `⟨fun I x => mem_trI s.iE I x, fun I J => trI_mul s.iE I J, trI_one s.iE, fun y => trI_singleton s.iE y, trI_surj s.iE, fun n N => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← det_set s.iE N]`. Both sides reduce to the same expression.

Use `_ = idTo s (detLat N) := (trI_span s.iE _).symm`.
-/
theorem transport : ∀ (D : D7) (X : Fields) (s : Seam D X), (∀ (I : Submodule (𝓞 X.E) X.E) (x : D.host.E), x ∈ idTo s I ↔ s.iE.symm x ∈ I) ∧ (∀ I J : Submodule (𝓞 X.E) X.E, idTo s (I * J) = idTo s I * idTo s J) ∧ idTo s 1 = 1 ∧ (∀ y : X.E, idTo s (Submodule.span (𝓞 X.E) {y}) = Submodule.span (𝓞 D.host.E) {s.iE y}) ∧ (∀ 𝔞 : TaylorLogMetric.IdE D, ∃ I, idTo s I = 𝔞) ∧ ∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)), TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N) = idTo s (detLat N) := by
  intro D X s
  refine ⟨fun I x => mem_trI s.iE I x, fun I J => trI_mul s.iE I J, trI_one s.iE,
    fun y => trI_singleton s.iE y, trI_surj s.iE, fun n N => ?_⟩
  calc TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)
      = Submodule.span (𝓞 D.host.E) (s.iE '' {x | ∃ A : Matrix (Fin n) (Fin n) X.E,
          (∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 X.E) X.E)), A.mulVec v ∈ N) ∧
            x = A.det}) := by
        rw [← det_set s.iE N]
        rfl
    _ = idTo s (detLat N) := (trI_span s.iE _).symm

end GlobalTheory.IdealTransport
