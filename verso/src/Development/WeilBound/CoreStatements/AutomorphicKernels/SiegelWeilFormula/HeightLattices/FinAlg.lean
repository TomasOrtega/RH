import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.InFrameForm

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain

namespace PositivityTheory.SiegelWeilFormula.HeightDict

open PositivityTheory.SiegelWeilFormula.KWhit.Ht

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Take `⟨-, hE, -, h⟩` from `hcm`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[h, h, star_star]`.
-/
theorem sig_sig (hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, hE, -, h⟩ := hcm
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h, h, star_star]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [HeckeCharacterZeroLocus.SiegelWeilU.sigR, sig_sig hcm]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem sgv_sgv (hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) (v : HeightOneSpectrum (𝓞 F)) (z : v.adicCompletion F ⊗[F] E) :
    HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [HeckeCharacterZeroLocus.SiegelWeilU.sigR, sig_sig hcm]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Take `⟨a₀, ha₀, o, rfl⟩` from `ha`. Take `⟨b₀, hb₀, o', rfl⟩` from `hb`. Conclude with `⟨a₀ * b₀, mul_mem ha₀ hb₀, o * o', by simp [Algebra.TensorProduct.tmul_mul_tmul]⟩`.
-/
theorem OE_gen_mul (v : HeightOneSpectrum (𝓞 F)) {a b : v.adicCompletion F ⊗[F] E}
    (ha : ∃ a₀ ∈ v.adicCompletionIntegers F, ∃ o : 𝓞 E, a = a₀ ⊗ₜ[F] (o : E))
    (hb : ∃ b₀ ∈ v.adicCompletionIntegers F, ∃ o : 𝓞 E, b = b₀ ⊗ₜ[F] (o : E)) :
    ∃ c₀ ∈ v.adicCompletionIntegers F, ∃ o : 𝓞 E, a * b = c₀ ⊗ₜ[F] (o : E) := by
  obtain ⟨a₀, ha₀, o, rfl⟩ := ha
  obtain ⟨b₀, hb₀, o', rfl⟩ := hb
  exact ⟨a₀ * b₀, mul_mem ha₀ hb₀, o * o', by simp [Algebra.TensorProduct.tmul_mul_tmul]⟩

/- English proof (translation)
Proceed by induction on `ha using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Proceed by induction on `hb using AddSubgroup.closure_induction with`. Consider the case `mem y hy => exact AddSubgroup.subset_closure (OE_gen_mul v hx hy)`. Consider the case `zero => simp`.

Consider the case `add y y' _ _ h h' => rw [mul_add]`. Conclude with `add_mem h h'`. Consider the case `neg y _ h => rw [mul_neg]`. Conclude with `neg_mem h`. Consider the case `zero => simp`.

Consider the case `add x x' _ _ h h' => rw [add_mul]`. Conclude with `add_mem h h'`. Consider the case `neg x _ h => rw [neg_mul]`. Conclude with `neg_mem h`.
-/
theorem OE_mul (v : HeightOneSpectrum (𝓞 F)) {a b : v.adicCompletion F ⊗[F] E} (ha : a ∈ OE E v) (hb : b ∈ OE E v) :
    a * b ∈ OE E v := by
  induction ha using AddSubgroup.closure_induction with
  | mem x hx =>
    induction hb using AddSubgroup.closure_induction with
    | mem y hy => exact AddSubgroup.subset_closure (OE_gen_mul v hx hy)
    | zero => simp
    | add y y' _ _ h h' => rw [mul_add]; exact add_mem h h'
    | neg y _ h => rw [mul_neg]; exact neg_mem h
  | zero => simp
  | add x x' _ _ h h' => rw [add_mul]; exact add_mem h h'
  | neg x _ h => rw [neg_mul]; exact neg_mem h

/- English proof (translation)
The claim follows from `AddSubgroup.subset_closure ⟨1, one_mem _, 1, by simp [Algebra.TensorProduct.one_def]⟩`.
-/
theorem OE_one (v : HeightOneSpectrum (𝓞 F)) : (1 : v.adicCompletion F ⊗[F] E) ∈ OE E v :=
  AddSubgroup.subset_closure ⟨1, one_mem _, 1, by simp [Algebra.TensorProduct.one_def]⟩

variable (E) in

def OEsub (v : HeightOneSpectrum (𝓞 F)) : Subring (v.adicCompletion F ⊗[F] E) :=
  { OE E v with
    one_mem' := OE_one v
    mul_mem' := fun ha hb => OE_mul v ha hb }

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨a, ha, o, rfl⟩` from `hx`. Use `AddSubgroup.subset_closure ⟨a, ha, ⟨σ o, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `(o.2.map σ)`.

Simplify using `[HeckeCharacterZeroLocus.SiegelWeilU.sigR]`. Both sides reduce to the same expression. Consider the case `zero => simp`. Consider the case `add x x' _ _ h h' => rw [map_add]`. Conclude with `add_mem h h'`.

Consider the case `neg x _ h => rw [map_neg]`. Conclude with `neg_mem h`.
-/
theorem OE_sig (v : HeightOneSpectrum (𝓞 F)) {z : v.adicCompletion F ⊗[F] E} (hz : z ∈ OE E v) :
    HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ z ∈ OE E v := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, o, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨a, ha, ⟨σ o, ?_⟩, ?_⟩
    · exact (o.2.map σ)
    · simp [HeckeCharacterZeroLocus.SiegelWeilU.sigR]
      rfl
  | zero => simp
  | add x x' _ _ h h' => rw [map_add]; exact add_mem h h'
  | neg x _ h => rw [map_neg]; exact neg_mem h

/- English proof (translation)
Simplify using `[lat, AddSubgroup.mem_pi]`.
-/
theorem mem_lat (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (y : Fin n → v.adicCompletion F ⊗[F] E) :
    y ∈ lat E v n ↔ ∀ i, y i ∈ OE E v := by
  simp [lat, AddSubgroup.mem_pi]

end PositivityTheory.SiegelWeilFormula.HeightDict
