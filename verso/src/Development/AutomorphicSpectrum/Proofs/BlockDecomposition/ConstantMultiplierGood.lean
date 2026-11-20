import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
import Development.AutomorphicArithmetic.LocalEmbeddings.OppLagr

noncomputable section

namespace GlobalTheory.CompanionTheory.RgEisCM

open scoped TensorProduct NNReal Matrix NumberField.AdeleRing
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open PositivityTheory.RgEis

section Transport

variable {R R' : Type} [CommRing R] [CommRing R'] {ι : Type} [Fintype ι] [DecidableEq ι]

def glEquiv (e : R ≃+* R') : GL ι R ≃* GL ι R' := Units.mapEquiv (RingEquiv.mapMatrix e).toMulEquiv

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_glEquiv (e : R ≃+* R') (g : GL ι R) :
    ((glEquiv e g : GL ι R') : Matrix ι ι R') = (g : Matrix ι ι R).map e := rfl

/- English proof (translation)
Rewrite using `[← map_inv]`. Both sides reduce to the same expression.
-/
theorem coe_glEquiv_inv (e : R ≃+* R') (g : GL ι R) :
    (((glEquiv e g)⁻¹ : GL ι R') : Matrix ι ι R') = ((g⁻¹ : GL ι R) : Matrix ι ι R).map e := by
  rw [← map_inv]; rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(∀ r ∉ s, ∀ c ∈ s, _ ∧ _) ↔ (∀ r ∉ s, ∀ c ∈ s, _ ∧ _)`. Simplify using `only [coe_glEquiv, coe_glEquiv_inv, Matrix.map_apply, EmbeddingLike.map_eq_zero_iff]`.
-/
theorem mem_stab_iff (e : R ≃+* R') (s : Set ι) (g : GL ι R) :
    g ∈ stab R s ↔ glEquiv e g ∈ stab R' s := by
  change (∀ r ∉ s, ∀ c ∈ s, _ ∧ _) ↔ (∀ r ∉ s, ∀ c ∈ s, _ ∧ _)
  simp only [coe_glEquiv, coe_glEquiv_inv, Matrix.map_apply, EmbeddingLike.map_eq_zero_iff]

variable {E : Type} [Field E]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `((∀ r c, _ ∧ _) ∧ ∀ w, _) ↔ ((∀ r c, _ ∧ _) ∧ ∀ w, _)`. Simplify using `only [coe_glEquiv, coe_glEquiv_inv, Matrix.map_apply, hO]`. Use `and_congr_right fun _ => ⟨fun h w' => ?_, fun h w => ?_⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `hφ' w'`. Establish `: ((g : Matrix ι ι R).map e).map (B.φ w') = (g : Matrix ι ι R).map (A.φ w)`.

Use extensionality with `r c`. Simplify using `[hw]`. Rewrite using `[this]`. Conclude with `h w`. Take `⟨w', hw⟩` from `hφ w`.

Establish `: (g : Matrix ι ι R).map (A.φ w) = ((g : Matrix ι ι R).map e).map (B.φ w')`. Use extensionality with `r c`. Simplify using `[hw]`. Rewrite using `[this]`. Conclude with `h w'`.
-/
theorem mem_kGL_iff (A : Ad E R) (B : Ad E R') (e : R ≃+* R') (hO : ∀ x, x ∈ A.O ↔ e x ∈ B.O)
    (hφ : ∀ w, ∃ w', ∀ x, A.φ w x = B.φ w' (e x)) (hφ' : ∀ w', ∃ w, ∀ x, A.φ w x = B.φ w' (e x)) (g : GL ι R) :
    g ∈ A.kGL ι ↔ glEquiv e g ∈ B.kGL ι := by
  change ((∀ r c, _ ∧ _) ∧ ∀ w, _) ↔ ((∀ r c, _ ∧ _) ∧ ∀ w, _)
  simp only [coe_glEquiv, coe_glEquiv_inv, Matrix.map_apply, hO]
  refine and_congr_right fun _ => ⟨fun h w' => ?_, fun h w => ?_⟩
  · obtain ⟨w, hw⟩ := hφ' w'
    have : ((g : Matrix ι ι R).map e).map (B.φ w') = (g : Matrix ι ι R).map (A.φ w) := by
      ext r c; simp [hw]
    rw [this]; exact h w
  · obtain ⟨w', hw⟩ := hφ w
    have : (g : Matrix ι ι R).map (A.φ w) = ((g : Matrix ι ι R).map e).map (B.φ w') := by
      ext r c; simp [hw]
    rw [this]; exact h w'

/- English proof (translation)
Introduce `g`. Take `⟨p, hp, k, hk', hg⟩` from `h (glEquiv e g)`. Use `⟨(glEquiv e).symm p, ?_, (glEquiv e).symm k, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_stab_iff e]`. Simplify using `using hp`.

Rewrite using `[hk]`. Simplify using `using hk'`. Apply `(glEquiv e).injective` to reduce the goal to its premises. Simplify using `[hg]`.
-/
theorem iwa_transport (A : Ad E R) (B : Ad E R') (e : R ≃+* R') (hk : ∀ g : GL ι R, g ∈ A.kGL ι ↔ glEquiv e g ∈ B.kGL ι)
    (s : Set ι) (h : Iwa (stab R' s) (B.kGL ι)) : Iwa (stab R s) (A.kGL ι) := by
  intro g
  obtain ⟨p, hp, k, hk', hg⟩ := h (glEquiv e g)
  refine ⟨(glEquiv e).symm p, ?_, (glEquiv e).symm k, ?_, ?_⟩
  · rw [mem_stab_iff e]; simpa using hp
  · rw [hk]; simpa using hk'
  · apply (glEquiv e).injective
    simp [hg]

variable [TopologicalSpace R] [TopologicalSpace R']

/- English proof (translation)
The claim follows from `Continuous.units_map _ (Continuous.matrix_map continuous_id h)`.
-/
theorem continuous_glEquiv (e : R ≃+* R') (h : Continuous e) : Continuous (glEquiv (ι := ι) e) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id h)

/- English proof (translation)
Set `H : GL ι R ≃ₜ GL ι R'` to `{ toEquiv := (glEquiv e).toEquiv continuous_toFun := continuous_glEquiv e h1 continuous_invFun := continuous_glEquiv e.symm h2 }`. Establish `: (A.kGL ι : Set (GL ι R)) = H ⁻¹' (B.kGL ι : Set (GL ι R'))`. Use extensionality with `g`. Conclude with `hk g`. Rewrite using `[this]`.

Conclude with `H.isCompact_preimage.2 h`.
-/
theorem kcpt_transport (A : Ad E R) (B : Ad E R') (e : R ≃+* R') (h1 : Continuous e) (h2 : Continuous e.symm)
    (hk : ∀ g : GL ι R, g ∈ A.kGL ι ↔ glEquiv e g ∈ B.kGL ι) (h : IsCompact (B.kGL ι : Set (GL ι R'))) :
    IsCompact (A.kGL ι : Set (GL ι R)) := by
  let H : GL ι R ≃ₜ GL ι R' :=
    { toEquiv := (glEquiv e).toEquiv
      continuous_toFun := continuous_glEquiv e h1
      continuous_invFun := continuous_glEquiv e.symm h2 }
  have : (A.kGL ι : Set (GL ι R)) = H ⁻¹' (B.kGL ι : Set (GL ι R')) := by
    ext g; exact hk g
  rw [this]
  exact H.isCompact_preimage.2 h

end Transport

section CM

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Simplify using `[cA, inclR, Algebra.TensorProduct.map_tmul]`.
-/
theorem cA_inclR (σ : E →ₐ[F] E) (x : E) :
    cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
  simp [cA, inclR, Algebra.TensorProduct.map_tmul]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x => simp [cA, Algebra.TensorProduct.map_tmul, GlobalTheory.OppLagr.conj_conj h]`. Consider the case `add x y hx hy => simp [map_add, hx, hy]`.
-/
theorem cA_cA {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [cA, Algebra.TensorProduct.map_tmul, GlobalTheory.OppLagr.conj_conj h]
  | add x y hx hy => simp [map_add, hx, hy]

/- English proof (translation)
Use `haveI : Module.Finite (AF F) (AE F E) := inferInstance`. Conclude with `IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap`.
-/
theorem continuous_cA (σ : E →ₐ[F] E) : Continuous (cA σ) := by
  haveI : Module.Finite (AF F) (AE F E) := inferInstance
  exact IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, h1, h2, o, rfl⟩` from `hz`. Establish `ho : IsIntegral ℤ (σ (o : E))` using `(RingOfIntegers.isIntegral_coe o).map σ`. Use `AddSubgroup.subset_closure ⟨a, h1, h2, (⟨σ o, ho⟩ : 𝓞 E), ?_⟩` and prove the remaining obligations.

Rewrite using `[map_smul, cA_inclR]`. Both sides reduce to the same expression. Consider the case `zero => simp [zero_mem]`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`.

Consider the case `neg x _ hx => rw [map_neg]`. Conclude with `neg_mem hx`.
-/
theorem cA_mem_intHat (σ : E →ₐ[F] E) {z : AE F E} (hz : z ∈ intHat F E) : cA σ z ∈ intHat F E := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, h1, h2, o, rfl⟩ := hz
    have ho : IsIntegral ℤ (σ (o : E)) := (RingOfIntegers.isIntegral_coe o).map σ
    refine AddSubgroup.subset_closure ⟨a, h1, h2, (⟨σ o, ho⟩ : 𝓞 E), ?_⟩
    rw [map_smul, cA_inclR]
    rfl
  | zero => simp [zero_mem]
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

end CM

/- English proof (translation)
Introduce `hS hD hI F E _ _ _ _ _ σ χ c hcm _ hχ hres`. Establish `hs` using `hS E`. Take `⟨d1, d2, d3, d4, -⟩` from `hD F E`. Establish `hO : ∀ x, x ∈ (adCM σ χ).O ↔ eqv F E x ∈ (adStd E).O` using `fun x => Iff.rfl`. Establish `hk : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : GL ι (AE F E)), g ∈ (adCM σ χ).kGL ι ↔ glEquiv (eqv F E) g ∈ (adStd E).kGL ι` using `fun ι _ _ g => mem_kGL_iff _ _ _ hO (fun w => ⟨w, fun _ => rfl⟩) (fun w => ⟨w, fun _ => rfl⟩) g`.

Establish `hu : Continuous (Units.map (eqv F E).toRingHom.toMonoidHom)` using `Continuous.units_map _ d1`. Establish `hi : ∀ x : Eˣ, Units.map (eqv F E).toRingHom.toMonoidHom (Units.map (inclR (F` using `F) (AF F)).toMonoidHom x) = Units.map (adStd E).i.toMonoidHom x := fun x => Units.ext (d3 x)`. Take `⟨ξ, hξ⟩` from `GlobalTheory.OppLagr.exists_isQuad hcm`. Use `⟨⟨?_, ?_, ?_, ?_, hχ.1, hχ.2, ?_, ?_⟩, cA_cA hcm, continuous_cA σ, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y hxy`.

Apply `hs.iinj` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `algebraMap E 𝔸[E] x = algebraMap E 𝔸[E] y`. Rewrite using `[← d3, ← d3]`. Conclude with `congrArg _ hxy`. Introduce `x y`.

Express the relevant statement in the definitionally equal form `(adStd E).lg (Units.map _ (x * y)) = _`. Rewrite using `[map_mul]`. Conclude with `hs.lgmul _ _`. Conclude with `hs.lgcont.comp hu`. Introduce `x`.

Conclude with `(congrArg (adStd E).lg (hi x)).trans (hs.lgi x)`. Introduce `ι _ _`. Conclude with `kcpt_transport _ _ (eqv F E) d1 d2 (hk ι) (hs.kcpt ι)`. Introduce `ι _ _ s`. Conclude with `iwa_transport _ _ (eqv F E) (hk ι) s (hs.iwa ι s)`.

Introduce `x hx`. Establish `h1 : finOne F • x ∈ intHat F E` using `(d4 x).1 hx`. Use `(d4 _).2 ?_` and prove the remaining obligations. Establish `h2` using `cA_mem_intHat σ h1`. Rewrite `h2` using `[map_smul]`. Then use the resulting hypothesis.

Introduce `w x`. Conclude with `(hI F E σ hcm).1 w x`. Introduce `x`. Conclude with `⟨σ x, cA_inclR σ x⟩`. Introduce `x`.

Conclude with `ResEtaPow.map_conj hξ hres x`.
-/
theorem cmGood : StdGood → Dict → DictInf → CMGood := by
  intro hS hD hI F E _ _ _ _ _ σ χ c hcm _ hχ hres
  have hs := hS E
  obtain ⟨d1, d2, d3, d4, -⟩ := hD F E
  have hO : ∀ x, x ∈ (adCM σ χ).O ↔ eqv F E x ∈ (adStd E).O := fun x => Iff.rfl
  have hk : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : GL ι (AE F E)),
      g ∈ (adCM σ χ).kGL ι ↔ glEquiv (eqv F E) g ∈ (adStd E).kGL ι := fun ι _ _ g =>
    mem_kGL_iff _ _ _ hO (fun w => ⟨w, fun _ => rfl⟩) (fun w => ⟨w, fun _ => rfl⟩) g
  have hu : Continuous (Units.map (eqv F E).toRingHom.toMonoidHom) := Continuous.units_map _ d1
  have hi : ∀ x : Eˣ, Units.map (eqv F E).toRingHom.toMonoidHom (Units.map (inclR (F := F) (AF F)).toMonoidHom x) =
      Units.map (adStd E).i.toMonoidHom x := fun x => Units.ext (d3 x)
  obtain ⟨ξ, hξ⟩ := GlobalTheory.OppLagr.exists_isQuad hcm
  refine ⟨⟨?_, ?_, ?_, ?_, hχ.1, hχ.2, ?_, ?_⟩, cA_cA hcm, continuous_cA σ, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    apply hs.iinj
    change algebraMap E 𝔸[E] x = algebraMap E 𝔸[E] y
    rw [← d3, ← d3]
    exact congrArg _ hxy
  · intro x y
    change (adStd E).lg (Units.map _ (x * y)) = _
    rw [map_mul]
    exact hs.lgmul _ _
  · exact hs.lgcont.comp hu
  · intro x
    exact (congrArg (adStd E).lg (hi x)).trans (hs.lgi x)
  · intro ι _ _
    exact kcpt_transport _ _ (eqv F E) d1 d2 (hk ι) (hs.kcpt ι)
  · intro ι _ _ s
    exact iwa_transport _ _ (eqv F E) (hk ι) s (hs.iwa ι s)
  · intro x hx
    have h1 : finOne F • x ∈ intHat F E := (d4 x).1 hx
    refine (d4 _).2 ?_
    have h2 := cA_mem_intHat σ h1
    rwa [map_smul] at h2
  · intro w x
    exact (hI F E σ hcm).1 w x
  · intro x
    exact ⟨σ x, cA_inclR σ x⟩
  · intro x
    exact ResEtaPow.map_conj hξ hres x

end GlobalTheory.CompanionTheory.RgEisCM
