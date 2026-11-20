import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.MemIntOEOfIsIntegral

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI.UnitaryApproxFinWork

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {n : Type} [Fintype n] [DecidableEq n]

def MS (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F))
    (M : Matrix n n (E ⊗[F] v.adicCompletion F)) : Prop :=
  ∀ i j, M i j ∈ Sv E v

def MC (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (d : 𝓞 F)
    (M : Matrix n n (E ⊗[F] v.adicCompletion F)) : Prop :=
  ∃ A, MS E v A ∧ M = dv E v d • A

variable {v : HeightOneSpectrum (𝓞 F)}

/- English proof (translation)
Introduce `i j` and use `by rw [Matrix.mul_apply] exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hM i k) (hN k j)`.
-/
theorem MS_mul {M N : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) (hN : MS E v N) :
    MS E v (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hM i k) (hN k j)

/- English proof (translation)
Introduce `i j` and use `Subring.add_mem _ (hM i j) (hN i j)`.
-/
theorem MS_add {M N : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) (hN : MS E v N) :
    MS E v (M + N) := fun i j => Subring.add_mem _ (hM i j) (hN i j)

/- English proof (translation)
Introduce `i j` and use `Subring.sub_mem _ (hM i j) (hN i j)`.
-/
theorem MS_sub {M N : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) (hN : MS E v N) :
    MS E v (M - N) := fun i j => Subring.sub_mem _ (hM i j) (hN i j)

/- English proof (translation)
Introduce `i j` and use `by rw [Matrix.one_apply] split_ifs · exact Subring.one_mem _ · exact Subring.zero_mem _`.
-/
theorem MS_one : MS E v (1 : Matrix n n (E ⊗[F] v.adicCompletion F)) := fun i j => by
  rw [Matrix.one_apply]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

/- English proof (translation)
Introduce `i j` and use `by rw [Matrix.smul_apply, smul_eq_mul] exact Subring.mul_mem _ ha (hM i j)`.
-/
theorem MS_smul {a : E ⊗[F] v.adicCompletion F} (ha : a ∈ Sv E v)
    {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) : MS E v (a • M) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul]
  exact Subring.mul_mem _ ha (hM i j)

def toS {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) : Matrix n n (Sv E v) :=
  fun i j => ⟨M i j, hM i j⟩

/- English proof (translation)
Use extensionality with `i j`. Both sides reduce to the same expression.
-/
theorem map_toS {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) :
    (Sv E v).subtype.mapMatrix (toS hM) = M := by
  ext i j
  rfl

/- English proof (translation)
Introduce `i j`. Rewrite using `[← map_toS hM, ← RingHom.map_adjugate]`. Conclude with `((toS hM).adjugate i j).2`.
-/
theorem MS_adjugate {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) :
    MS E v M.adjugate := by
  intro i j
  rw [← map_toS hM, ← RingHom.map_adjugate]
  exact ((toS hM).adjugate i j).2

/- English proof (translation)
Rewrite using `[← map_toS hM, ← RingHom.map_det]`. Conclude with `(toS hM).det.2`.
-/
theorem det_mem {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) : M.det ∈ Sv E v := by
  rw [← map_toS hM, ← RingHom.map_det]
  exact (toS hM).det.2

/- English proof (translation)
Apply `Subring.subset_closure` to reduce the goal to its premises. Use `left`. Conclude with `⟨⟨algebraMap F E (d : F), ⟨⟨algebraMap F E (d : F), (RingOfIntegers.isIntegral_coe d).algebraMap⟩, rfl⟩⟩, rfl⟩`.
-/
private lemma dv_mem_Sv' (d : 𝓞 F) : dv E v d ∈ Sv E v := by
  apply Subring.subset_closure
  left
  exact ⟨⟨algebraMap F E (d : F),
    ⟨⟨algebraMap F E (d : F), (RingOfIntegers.isIntegral_coe d).algebraMap⟩, rfl⟩⟩, rfl⟩

/- English proof (translation)
Set `p : Sv E v` to `⟨dv E v π, dv_mem_Sv' π⟩`. Set `B` to `toS hA`. Set `I : Ideal (Sv E v)` to `Ideal.span {p}`. Establish `hp0 : Ideal.Quotient.mk I p = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)`. Establish `h0 : (Ideal.Quotient.mk I).mapMatrix (p • B) = 0`.

Use extensionality with `i j`. Simplify using `[hp0]`. Establish `hmap : (Ideal.Quotient.mk I).mapMatrix (1 + p • B) = 1`. Rewrite using `[map_add, map_one, h0, add_zero]`. Establish `hdet : Ideal.Quotient.mk I ((1 + p • B).det - 1) = 0`.

Rewrite using `[map_sub, RingHom.map_det, hmap, Matrix.det_one, map_one, sub_self]`. Take `⟨t, ht⟩` from `Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hdet)`. Use `⟨(t : E ⊗[F] v.adicCompletion F), t.2, ?_⟩` and prove the remaining obligations. Establish `h2 : (Sv E v).subtype.mapMatrix (1 + p • B) = 1 + dv E v π • A`. Rewrite using `[map_add, map_one]`.

Use `congr 1`. Establish `h4 : (1 + p • B).det = 1 + p * t`. Rewrite using `[mul_comm, ht]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← h2, ← RingHom.map_det, h4]`.

Simplify using `[p]`.
-/
theorem det_one_add (π : 𝓞 F) {A : Matrix n n (E ⊗[F] v.adicCompletion F)} (hA : MS E v A) :
    ∃ s ∈ Sv E v, (1 + dv E v π • A).det = 1 + dv E v π * s := by
  let p : Sv E v := ⟨dv E v π, dv_mem_Sv' π⟩
  let B := toS hA
  let I : Ideal (Sv E v) := Ideal.span {p}
  have hp0 : Ideal.Quotient.mk I p = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  have h0 : (Ideal.Quotient.mk I).mapMatrix (p • B) = 0 := by
    ext i j
    simp [hp0]
  have hmap : (Ideal.Quotient.mk I).mapMatrix (1 + p • B) = 1 := by
    rw [map_add, map_one, h0, add_zero]
  have hdet : Ideal.Quotient.mk I ((1 + p • B).det - 1) = 0 := by
    rw [map_sub, RingHom.map_det, hmap, Matrix.det_one, map_one, sub_self]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hdet)
  refine ⟨(t : E ⊗[F] v.adicCompletion F), t.2, ?_⟩
  have h2 : (Sv E v).subtype.mapMatrix (1 + p • B) = 1 + dv E v π • A := by
    rw [map_add, map_one]
    congr 1
  have h4 : (1 + p • B).det = 1 + p * t := by
    rw [mul_comm, ht]
    ring
  rw [← h2, ← RingHom.map_det, h4]
  simp [p]

/- English proof (translation)
Take `⟨A, hA, rfl⟩` from `h`. Conclude with `⟨A i j, hA i j, by rw [Matrix.smul_apply, smul_eq_mul]⟩`.
-/
theorem MC_entries {d : 𝓞 F} {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (h : MC E v d M) (i j : n) :
    Cong E v d (M i j) := by
  obtain ⟨A, hA, rfl⟩ := h
  exact ⟨A i j, hA i j, by rw [Matrix.smul_apply, smul_eq_mul]⟩

/- English proof (translation)
Use `choose t ht heq using h`. Use `⟨Matrix.of fun i j => t i j, fun i j => ht i j, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Rewrite using `[Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]`. Conclude with `heq i j`.
-/
theorem MC_of_entries {d : 𝓞 F} {M : Matrix n n (E ⊗[F] v.adicCompletion F)}
    (h : ∀ i j, Cong E v d (M i j)) : MC E v d M := by
  choose t ht heq using h
  refine ⟨Matrix.of fun i j => t i j, fun i j => ht i j, ?_⟩
  ext i j
  rw [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  exact heq i j

/- English proof (translation)
Establish `hx : algebraMap F E (c : F) ≠ 0` using `by simpa using hc`. Establish `hu : IsUnit (dv E v c)` using `(IsUnit.mk0 _ hx).map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F))`. Establish `hmul : dv E v (c * e) = dv E v c * dv E v e` using `by simp [dv]`. Rewrite `h` using `[hmul, mul_smul]`. Conclude with `hu.smul_left_cancel.1 h`.
-/
theorem MC_cancel {c e : 𝓞 F} (hc : c ≠ 0) {M A : Matrix n n (E ⊗[F] v.adicCompletion F)}
    (h : dv E v c • M = dv E v (c * e) • A) : M = dv E v e • A := by
  have hx : algebraMap F E (c : F) ≠ 0 := by simpa using hc
  have hu : IsUnit (dv E v c) :=
    (IsUnit.mk0 _ hx).map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F))
  have hmul : dv E v (c * e) = dv E v c * dv E v e := by simp [dv]
  rw [hmul, mul_smul] at h
  exact hu.smul_left_cancel.1 h

/- English proof (translation)
Simplify using `only [PI.UnitaryApproxDefs.intOE, RingHom.mem_range] at hx ⊢`. Take `⟨y, rfl⟩` from `hx`. Conclude with `⟨⟨σ y, (RingOfIntegers.isIntegral_coe y).map σ.toRingHom.toIntAlgHom⟩, rfl⟩`.
-/
theorem sigma_mem_intOE (σ : E →ₐ[F] E) {x : E} (hx : x ∈ PI.UnitaryApproxDefs.intOE E) : σ x ∈ PI.UnitaryApproxDefs.intOE E := by
  simp only [PI.UnitaryApproxDefs.intOE, RingHom.mem_range] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  exact ⟨⟨σ y, (RingOfIntegers.isIntegral_coe y).map σ.toRingHom.toIntAlgHom⟩, rfl⟩

/- English proof (translation)
Establish `h : Sv E v ≤ (Sv E v).comap (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F))`. Use `Subring.closure_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)`. Simplify using `only [Subring.coe_comap, Set.mem_preimage]`. Apply `Subring.subset_closure` to reduce the goal to its premises.

Use `left`. Conclude with `⟨⟨σ x, sigma_mem_intOE σ hx⟩, by simp [PI.UnitaryApproxDefs.sigR]⟩`. Simplify using `only [Subring.coe_comap, Set.mem_preimage]`. Apply `Subring.subset_closure` to reduce the goal to its premises. Use `right`.

Conclude with `⟨⟨y, hy⟩, by simp [PI.UnitaryApproxDefs.sigR]⟩`. Conclude with `h hs`.
-/
theorem sigR_mem_Sv (σ : E →ₐ[F] E) {s : E ⊗[F] v.adicCompletion F} (hs : s ∈ Sv E v) :
    PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) s ∈ Sv E v := by
  have h : Sv E v ≤ (Sv E v).comap (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · simp only [Subring.coe_comap, Set.mem_preimage]
      apply Subring.subset_closure
      left
      exact ⟨⟨σ x, sigma_mem_intOE σ hx⟩, by simp [PI.UnitaryApproxDefs.sigR]⟩
    · simp only [Subring.coe_comap, Set.mem_preimage]
      apply Subring.subset_closure
      right
      exact ⟨⟨y, hy⟩, by simp [PI.UnitaryApproxDefs.sigR]⟩
  exact h hs

/- English proof (translation)
Introduce `i j` and use `sigR_mem_Sv σ (hM j i)`.
-/
theorem MS_cT (σ : E →ₐ[F] E) {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) :
    MS E v (PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)) M) := fun i j => sigR_mem_Sv σ (hM j i)

/- English proof (translation)
Simplify using `[PI.UnitaryApproxDefs.sigR, PI.UnitaryApproxDefs.inclE, dv]`.
-/
theorem sigR_dv (σ : E →ₐ[F] E) (d : 𝓞 F) : PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) (dv E v d) = dv E v d := by
  simp [PI.UnitaryApproxDefs.sigR, PI.UnitaryApproxDefs.inclE, dv]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[PI.UnitaryApproxDefs.cT, PI.UnitaryApproxDefs.sigR, PI.UnitaryApproxDefs.inclE]`.
-/
theorem cT_map (σ : E →ₐ[F] E) (M : Matrix n n E) :
    PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)) (M.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F))) =
      (PI.UnitaryApproxDefs.cT (σ : E →+* E) M).map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) := by
  ext i j
  simp [PI.UnitaryApproxDefs.cT, PI.UnitaryApproxDefs.sigR, PI.UnitaryApproxDefs.inclE]

end PI.UnitaryApproxFinWork

end
