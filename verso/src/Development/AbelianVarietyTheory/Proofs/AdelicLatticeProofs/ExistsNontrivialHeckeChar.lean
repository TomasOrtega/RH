import Mathlib
import Formalism.UnipotentAdelicQuotients.ThmBInHecke
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsPrimeIdemOfComp
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTensorFiniteAdeleEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom

open HeckeCharacterZeroLocus.ThmBIn NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.HeckeInhabitant

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Use `letI : Algebra F ℂ := w.embedding.toAlgebra`. Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _`. Set `τ : E →ₐ[F] ℂ` to `IsAlgClosed.lift`. Set `g0 : AF F →+* ℂ` to `(InfinitePlace.Completion.extensionEmbedding w).comp ((Pi.evalRingHom (fun u : InfinitePlace F => u.Completion) w).comp (RingHom.fst (Ainf F) (Af F)))`.

Set `g : AF F →ₐ[F] ℂ` to `⟨g0, fun x => InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ x)⟩`. Set `θ : AE F E →+* ℂ` to `(Algebra.TensorProduct.productMap g τ).toRingHom`. Establish `hθ : ∀ a x, θ (a ⊗ₜ[F] x) = g0 a * τ x` using `fun a x => rfl`. Use `haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩`. Use `⟨θ, τ, ?_, fun x => ?_, fun α => ?_⟩` and prove the remaining obligations.

Use `IsModuleTopology.continuous_of_ringHom (R := AF F) θ ?_` and prove the remaining obligations. Establish `: Continuous g0` using `(InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp ((continuous_apply w).comp continuous_fst)`. Use `this.congr fun a => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = θ (a ⊗ₜ[F] 1)`. Rewrite using `[hθ, map_one, mul_one]`.

Express the relevant statement in the definitionally equal form `θ (1 ⊗ₜ[F] x) = _`. Rewrite using `[hθ, map_one, one_mul]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `θ (_ ⊗ₜ[F] 1) = _`. Rewrite using `[hθ, map_one, mul_one]`.

Conclude with `map_zero (InfinitePlace.Completion.extensionEmbedding w)`.
-/
theorem exists_arch : ∃ (θ : AE F E →+* ℂ) (τ : E →+* ℂ), Continuous θ ∧ (∀ x, θ (incA F E x) = τ x) ∧
    ∀ α, θ (algebraMap (AF F) (AE F E) (pairA F 0 α)) = 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  letI : Algebra F ℂ := w.embedding.toAlgebra
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  let τ : E →ₐ[F] ℂ := IsAlgClosed.lift
  let g0 : AF F →+* ℂ := (InfinitePlace.Completion.extensionEmbedding w).comp
    ((Pi.evalRingHom (fun u : InfinitePlace F => u.Completion) w).comp (RingHom.fst (Ainf F) (Af F)))
  let g : AF F →ₐ[F] ℂ := ⟨g0, fun x => InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ x)⟩
  let θ : AE F E →+* ℂ := (Algebra.TensorProduct.productMap g τ).toRingHom
  have hθ : ∀ a x, θ (a ⊗ₜ[F] x) = g0 a * τ x := fun a x => rfl
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  refine ⟨θ, τ, ?_, fun x => ?_, fun α => ?_⟩
  · refine IsModuleTopology.continuous_of_ringHom (R := AF F) θ ?_
    have : Continuous g0 := (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
      ((continuous_apply w).comp continuous_fst)
    refine this.congr fun a => ?_
    change _ = θ (a ⊗ₜ[F] 1)
    rw [hθ, map_one, mul_one]
  · change θ (1 ⊗ₜ[F] x) = _
    rw [hθ, map_one, one_mul]; rfl
  · change θ (_ ⊗ₜ[F] 1) = _
    rw [hθ, map_one, mul_one]
    exact map_zero (InfinitePlace.Completion.extensionEmbedding w)

/- English proof (translation)
Take `⟨ι, h1, h2, -⟩` from `GlobalTheory.AdeleBaseChange.exists_tensor_finiteAdele_equiv F E`. Use `haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩`. Use `⟨ι.toRingHom.comp (finPart F E), ?_, fun x => h1 x, fun y => h2 _⟩` and prove the remaining obligations. Use `IsModuleTopology.continuous_of_ringHom (R := AF F) _ ?_` and prove the remaining obligations. Use `GlobalTheory.HeckeTensorRead.continuous_of_map_integral (ι.toRingHom.comp (algebraMap (Af F) (Af F ⊗[F] E))) (fun a ha P => (h2 (a ⊗ₜ[F] (1 : E))).1 (AddSubgroup.subset_closure ⟨a, ha, 1, rfl⟩) P)` as an intermediate fact.

Conclude with `this.comp continuous_snd`.
-/
theorem exists_fin : ∃ Φ : AE F E →+* FiniteAdeleRing (𝓞 E) E, Continuous Φ ∧
    (∀ x, Φ (incA F E x) = algebraMap E _ x) ∧
    ∀ y, finPart F E y ∈ intAE F E ↔ ∀ P, Valued.v (Φ y P) ≤ 1 := by
  obtain ⟨ι, h1, h2, -⟩ := GlobalTheory.AdeleBaseChange.exists_tensor_finiteAdele_equiv F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  refine ⟨ι.toRingHom.comp (finPart F E), ?_, fun x => h1 x, fun y => h2 _⟩
  refine IsModuleTopology.continuous_of_ringHom (R := AF F) _ ?_
  have := GlobalTheory.HeckeTensorRead.continuous_of_map_integral
    (ι.toRingHom.comp (algebraMap (Af F) (Af F ⊗[F] E))) (fun a ha P =>
      (h2 (a ⊗ₜ[F] (1 : E))).1 (AddSubgroup.subset_closure ⟨a, ha, 1, rfl⟩) P)
  exact this.comp continuous_snd

/- English proof (translation)
Express the relevant statement in the definitionally equal form `a ⊗ₜ[F] σ 1 = a ⊗ₜ[F] (1 : E)`. Rewrite using `[map_one]`.
-/
theorem cA_base (σ : E →ₐ[F] E) (a : AF F) : cA σ (algebraMap (AF F) (AE F E) a) = algebraMap (AF F) (AE F E) a := by
  change a ⊗ₜ[F] σ 1 = a ⊗ₜ[F] (1 : E)
  rw [map_one]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cA_inc (σ : E →ₐ[F] E) (x : E) : cA σ (incA F E x) = incA F E (σ x) := rfl

/- English proof (translation)
Use `haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩`. Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _`. Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _`. Use `IsModuleTopology.continuous_of_ringHom (R := AF F) _ ?_` and prove the remaining obligations. Establish `: Continuous (algebraMap (AF F) (AE F E))` using `IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AE F E))`.

Conclude with `this.congr fun a => (cA_base σ a).symm`.
-/
theorem cA_cont (σ : E →ₐ[F] E) : Continuous (cA σ) := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  refine IsModuleTopology.continuous_of_ringHom (R := AF F) _ ?_
  have : Continuous (algebraMap (AF F) (AE F E)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AE F E))
  exact this.congr fun a => (cA_base σ a).symm

/- English proof (translation)
Establish `e : finPart F E (cA σ y) = sigR (Af F) σ (finPart F E y)` using `by clear h`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp only [RingHom.map_zero]`. Consider the case `add x y hx hy => simp only [RingHom.map_add, hx, hy]`. Consider the case `tmul a x => rfl`.

Rewrite using `[e]`. Generalize the expression as in `finPart F E y = z at h`. Proceed by induction on `h using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨a, ha, x, rfl⟩` from `hy`.

Conclude with `AddSubgroup.subset_closure ⟨a, ha, RingOfIntegers.mapRingHom (σ : E →+* E) x, rfl⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`.

Consider the case `neg x _ hx => rw [map_neg]`. Conclude with `neg_mem hx`.
-/
theorem cA_int (σ : E →ₐ[F] E) (y : AE F E) (h : finPart F E y ∈ intAE F E) :
    finPart F E (cA σ y) ∈ intAE F E := by
  have e : finPart F E (cA σ y) = sigR (Af F) σ (finPart F E y) := by
    clear h
    induction y using TensorProduct.induction_on with
    | zero => simp only [RingHom.map_zero]
    | add x y hx hy => simp only [RingHom.map_add, hx, hy]
    | tmul a x => rfl
  rw [e]
  generalize finPart F E y = z at h
  induction h using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨a, ha, RingOfIntegers.mapRingHom (σ : E →+* E) x, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

/- English proof (translation)
Break down `h with ⟨⟨⟨h1, h2, v, ε, ⟨α, rfl, -⟩, h3⟩, -⟩, -⟩ | ⟨-, ⟨v, ε, ⟨α, rfl, -⟩, rfl⟩, -⟩` into its components or cases. Establish `a1` using `congrArg θ h1`. Establish `a2` using `congrArg θ h2`. Establish `a3` using `congrArg θ h3`. Rewrite `a3` using `[hθ, RingHom.map_add]`.

Rewrite `a1`, `a2` using `[RingHom.map_mul]`. Rewrite `a2` using `[RingHom.map_zero]`. Establish `: θ e = 0` using `by linear_combination θ e * a3 - a1 - a2`. Conclude with `⟨this, by rw [this, zero_add] at a3; exact a3⟩`. Rewrite using `[cA_base]`.

Conclude with `⟨hθ α, hθ α⟩`.
-/
theorem idem_arch {σ : E →ₐ[F] E} {θ : AE F E →+* ℂ} (hθ : ∀ α, θ (algebraMap (AF F) (AE F E) (pairA F 0 α)) = 0)
    {P : HeightOneSpectrum (𝓞 E)} {e f : AE F E} (h : IsPrimeIdem σ P e f) : θ e = 0 ∧ θ (cA σ e) = 0 := by
  rcases h with ⟨⟨⟨h1, h2, v, ε, ⟨α, rfl, -⟩, h3⟩, -⟩, -⟩ | ⟨-, ⟨v, ε, ⟨α, rfl, -⟩, rfl⟩, -⟩
  · have a1 := congrArg θ h1
    have a2 := congrArg θ h2
    have a3 := congrArg θ h3
    rw [hθ, RingHom.map_add] at a3
    rw [RingHom.map_mul] at a1 a2
    rw [RingHom.map_zero] at a2
    have : θ e = 0 := by linear_combination θ e * a3 - a1 - a2
    exact ⟨this, by rw [this, zero_add] at a3; exact a3⟩
  · rw [cA_base]
    exact ⟨hθ α, hθ α⟩

/- English proof (translation)
Establish `h' : e * e = e ∧ ∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ finPart F E (e * incA F E ((x : E)⁻¹)) ∉ intAE F E)`. Break down `h with ⟨⟨⟨h1, -⟩, h2⟩, -⟩ | ⟨-, ⟨v, ε, ⟨α, rfl, a1, a0⟩, rfl⟩, h2⟩` into its components or cases. Conclude with `⟨h1, h2⟩`. Use `⟨?_, h2⟩` and prove the remaining obligations. Rewrite using `[← map_mul]`.

Use `congrArg _ (Prod.ext (mul_zero (0 : Ainf F)) (GlobalTheory.PlaceIdem.adele_ext fun u => ?_))` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `evalV F u α * evalV F u α = evalV F u α`. Distinguish the cases in `hu : u = v`. Substitute `hu` using the available equality. Rewrite using `[a1, mul_one]`.

Rewrite using `[a0 u hu, mul_zero]`. Take `⟨hee, hx⟩` from `h'`. Take `⟨g, hg⟩ : ∃ g, g = Φ e` from `⟨_, rfl⟩`. Establish `hgg : g * g = g` using `by rw [hg, ← RingHom.map_mul, hee]`. Establish `hg01 : ∀ R, g R ≠ 0 → g R = 1`.

Introduce `R hR`. Establish `: g R * g R = g R * 1` using `by rw [← GlobalTheory.PlaceIdem.mul_ap, hgg, mul_one]`. Conclude with `mul_left_cancel₀ hR this`. Establish `key : ∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ ∃ R, g R ≠ 0 ∧ x ∈ R.asIdeal)`. Introduce `x hx0`.

Rewrite using `[hx x hx0, hint, RingHom.map_mul, ← hg, hι, not_forall]`. Use `exists_congr fun R => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.PlaceIdem.mul_ap]`. Distinguish the cases in `hR : g R = 0`. Simplify using `[hR]`.

Rewrite using `[hg01 R hR, one_mul, GlobalTheory.PlaceIdem.val_inv_le_one R hx0]`. Simplify using the standard rewrite rules. Establish `h0 : ∀ Q, Q ≠ P → g Q = 0`. Introduce `Q hQ`. Assume the negation of the conclusion as `hne`.

Use `hQ (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top fun x hxQ => ?_))` and prove the remaining obligations. Distinguish the cases in `hx0 : x = 0`. Rewrite using `[hx0]`. Conclude with `zero_mem _`. Conclude with `(key x hx0).2 ⟨Q, hne, hxQ⟩`.

Rewrite using `[← hg]`. Use `⟨?_, h0⟩` and prove the remaining obligations. Take `⟨x, hxP, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot`. Take `⟨R, hR, -⟩` from `(key x hx0).1 hxP`. Distinguish the cases in `hRP : R = P`.

Substitute `hRP` using the available equality. Conclude with `hg01 _ hR`. Conclude with `absurd (h0 R hRP) hR`.
-/
theorem idem_fin {σ : E →ₐ[F] E} {Φ : AE F E →+* FiniteAdeleRing (𝓞 E) E}
    (hι : ∀ x, Φ (incA F E x) = algebraMap E _ x)
    (hint : ∀ y, finPart F E y ∈ intAE F E ↔ ∀ P, Valued.v (Φ y P) ≤ 1)
    {P : HeightOneSpectrum (𝓞 E)} {e f : AE F E} (h : IsPrimeIdem σ P e f) :
    Φ e P = 1 ∧ ∀ Q, Q ≠ P → Φ e Q = 0 := by
  have h' : e * e = e ∧ ∀ x : 𝓞 E, x ≠ 0 →
      (x ∈ P.asIdeal ↔ finPart F E (e * incA F E ((x : E)⁻¹)) ∉ intAE F E) := by
    rcases h with ⟨⟨⟨h1, -⟩, h2⟩, -⟩ | ⟨-, ⟨v, ε, ⟨α, rfl, a1, a0⟩, rfl⟩, h2⟩
    · exact ⟨h1, h2⟩
    · refine ⟨?_, h2⟩
      rw [← map_mul]
      refine congrArg _ (Prod.ext (mul_zero (0 : Ainf F)) (GlobalTheory.PlaceIdem.adele_ext fun u => ?_))
      change evalV F u α * evalV F u α = evalV F u α
      by_cases hu : u = v
      · subst hu; rw [a1, mul_one]
      · rw [a0 u hu, mul_zero]
  obtain ⟨hee, hx⟩ := h'
  obtain ⟨g, hg⟩ : ∃ g, g = Φ e := ⟨_, rfl⟩
  have hgg : g * g = g := by rw [hg, ← RingHom.map_mul, hee]
  have hg01 : ∀ R, g R ≠ 0 → g R = 1 := by
    intro R hR
    have : g R * g R = g R * 1 := by rw [← GlobalTheory.PlaceIdem.mul_ap, hgg, mul_one]
    exact mul_left_cancel₀ hR this
  have key : ∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ ∃ R, g R ≠ 0 ∧ x ∈ R.asIdeal) := by
    intro x hx0
    rw [hx x hx0, hint, RingHom.map_mul, ← hg, hι, not_forall]
    refine exists_congr fun R => ?_
    rw [GlobalTheory.PlaceIdem.mul_ap]
    by_cases hR : g R = 0
    · simp [hR]
    · rw [hg01 R hR, one_mul, GlobalTheory.PlaceIdem.val_inv_le_one R hx0]
      simp
  have h0 : ∀ Q, Q ≠ P → g Q = 0 := by
    intro Q hQ
    by_contra hne
    refine hQ (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top fun x hxQ => ?_))
    by_cases hx0 : x = 0
    · rw [hx0]; exact zero_mem _
    · exact (key x hx0).2 ⟨Q, hne, hxQ⟩
  rw [← hg]
  refine ⟨?_, h0⟩
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  obtain ⟨R, hR, -⟩ := (key x hx0).1 hxP
  by_cases hRP : R = P
  · subst hRP
    exact hg01 _ hR
  · exact absurd (h0 R hRP) hR

/- English proof (translation)
The claim follows from `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P x`.
-/
theorem val_alg (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    Valued.v (algebraMap E (FiniteAdeleRing (𝓞 E) E) x P) = P.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P x

/- English proof (translation)
Take `⟨e, f, ϖ, he, h1, h2, hx⟩` from `h`. Take `⟨d1, d0⟩` from `idem_fin hι hint he`. Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl`. Conclude with `P.ne_bot (by rw [hπ]; simp)`.

Establish `e1 : Φ (x : AE F E) Q = Φ e Q * algebraMap E (FiniteAdeleRing (𝓞 E) E) (ϖ : E) Q + (1 - Φ e Q)`. Rewrite using `[hx, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hι]`. Both sides reduce to the same expression. Establish `e2 : ∀ y : 𝓞 E, Q.valuation E (y : E) = Q.intValuation y` using `fun y => HeightOneSpectrum.valuation_of_algebraMap Q y`. Rewrite using `[e1, e2]`.

Distinguish the cases in `hQ : Q = P`. Substitute `hQ` using the available equality. Rewrite using `[d1, one_mul, sub_self, add_zero, val_alg, e2, HeightOneSpectrum.intValuation_singleton Q hπ0 hπ]`. Establish `a1` using `(HeightOneSpectrum.intValuation_le_pow_iff_mem Q ϖ 1).2 (by rwa [pow_one])`. Establish `a2` using `mt (HeightOneSpectrum.intValuation_le_pow_iff_mem Q ϖ 2).1 h2`.

Establish `a0 : Q.intValuation ϖ ≠ 0` using `fun h => a2 (by rw [h]; exact zero_le)`. Rewrite `a1`, `a2`, the goal using `[← WithZero.exp_log a0]`. Rewrite `a1`, `a2` using `[WithZero.exp_le_exp]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[d0 Q hQ, zero_mul, zero_add, sub_zero, map_one, eq_comm, HeightOneSpectrum.intValuation_eq_one_iff]`. Introduce `hm`. Use `hQ (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top ?_).symm)` and prove the remaining obligations. Rewrite using `[hπ, Ideal.span_singleton_le_iff_mem]`. Conclude with `hm`.
-/
theorem unif_val {σ : E →ₐ[F] E} {Φ : AE F E →+* FiniteAdeleRing (𝓞 E) E}
    (hι : ∀ x, Φ (incA F E x) = algebraMap E _ x)
    (hint : ∀ y, finPart F E y ∈ intAE F E ↔ ∀ P, Valued.v (Φ y P) ≤ 1)
    {P : HeightOneSpectrum (𝓞 E)} {π : 𝓞 E} (hπ : P.asIdeal = Ideal.span {π}) {x : (AE F E)ˣ}
    (h : IsUnifIdele σ P x) (Q : HeightOneSpectrum (𝓞 E)) :
    Valued.v (Φ (x : AE F E) Q) = Q.valuation E (π : E) := by
  obtain ⟨e, f, ϖ, he, h1, h2, hx⟩ := h
  obtain ⟨d1, d0⟩ := idem_fin hι hint he
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact P.ne_bot (by rw [hπ]; simp)
  have e1 : Φ (x : AE F E) Q = Φ e Q * algebraMap E (FiniteAdeleRing (𝓞 E) E) (ϖ : E) Q + (1 - Φ e Q) := by
    rw [hx, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hι]
    rfl
  have e2 : ∀ y : 𝓞 E, Q.valuation E (y : E) = Q.intValuation y := fun y => HeightOneSpectrum.valuation_of_algebraMap Q y
  rw [e1, e2]
  by_cases hQ : Q = P
  · subst hQ
    rw [d1, one_mul, sub_self, add_zero, val_alg, e2, HeightOneSpectrum.intValuation_singleton Q hπ0 hπ]
    have a1 := (HeightOneSpectrum.intValuation_le_pow_iff_mem Q ϖ 1).2 (by rwa [pow_one])
    have a2 := mt (HeightOneSpectrum.intValuation_le_pow_iff_mem Q ϖ 2).1 h2
    have a0 : Q.intValuation ϖ ≠ 0 := fun h => a2 (by rw [h]; exact zero_le)
    rw [← WithZero.exp_log a0] at a1 a2 ⊢
    rw [WithZero.exp_le_exp] at a1 a2
    congr 1
    omega
  · rw [d0 Q hQ, zero_mul, zero_add, sub_zero, map_one, eq_comm, HeightOneSpectrum.intValuation_eq_one_iff]
    intro hm
    refine hQ (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top ?_).symm)
    rw [hπ, Ideal.span_singleton_le_iff_mem]
    exact hm

/- English proof (translation)
Use `haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩`. Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _`. Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _`. Set `S : Submonoid (AE F E)` to `{ carrier := {z | ∀ P, Valued.v (Φ z P) ≤ 1} one_mem' := fun P => by`. Rewrite using `[RingHom.map_one]`.

Conclude with `(map_one (Valued.v : Valuation (P.adicCompletion E) _)).le`. Use the proof step `mul_mem' := fun {a b} ha hb P => by`. Rewrite using `[RingHom.map_mul, GlobalTheory.PlaceIdem.mul_ap, map_mul]`. Conclude with `mul_le_one' (ha P) (hb P) }`. Establish `hO : IsOpen {a : FiniteAdeleRing (𝓞 E) E | ∀ v, a v ∈ v.adicCompletionIntegers E}` using `RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _`.

Establish `hS : IsOpen (S : Set (AE F E))` using `hO.preimage hΦc`. Set `t : (AE F E)ˣ →* ℂˣ` to `Units.map θ.toMonoidHom`. Set `b : ℂˣ →* ℂˣ` to `Units.map (starRingEnd ℂ).toMonoidHom`. Set `ψ : (AE F E)ˣ →* ℂˣ` to `(t / b.comp t) ^ k`. Establish `hψ : ∀ x, ((ψ x : ℂˣ) : ℂ) = (θ x / star (θ x)) ^ k` using `fun x => by`.

Express the relevant statement in the definitionally equal form `(((t x / b (t x)) ^ k : ℂˣ) : ℂ) = _`. Rewrite using `[Units.val_pow_eq_pow_val, Units.val_div_eq_div_val]`. Both sides reduce to the same expression. Establish `ht : Continuous t` using `Continuous.units_map _ hθc`. Establish `hb : Continuous b` using `Continuous.units_map _ Complex.continuous_conj`.

Establish `hψc : Continuous ψ` using `(ht.div' (hb.comp ht)).pow k`. Set `α : Eˣ →* (AE F E)ˣ` to `Units.map (incA F E).toMonoidHom`. Take `⟨ν, hν, hνu, hνU, hν1⟩` from `GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (AE F E)ˣ Eˣ S.units (Submonoid.isOpen_units hS) α 1 ψ hψc (fun x => by`. Establish `: θ x ≠ 0` using `(t x).ne_zero`. Rewrite using `[hψ, norm_pow, norm_div, norm_star, div_self (norm_ne_zero_iff.2 this), one_pow])`.

Use the proof step `(fun _ => by simp)`. Use the proof step `(fun y hy => by`. Take `⟨h1, h2⟩` from `(Submonoid.mem_units_iff _ _).1 hy`. Take `⟨p, hp⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one E (y : E) (R := 𝓞 E) fun P => by`. Rewrite using `[← val_alg, ← hι]`.

Conclude with `h1 P`. Take `⟨q, hq⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one E ((y⁻¹ : Eˣ) : E) (R := 𝓞 E) fun P => by`. Rewrite using `[← val_alg, ← hι]`. Conclude with `h2 P`. Establish `hpq : p * q = 1`.

Apply `FaithfulSMul.algebraMap_injective (𝓞 E) E` to reduce the goal to its premises. Rewrite using `[map_mul, hp, hq, map_one, Units.mul_inv]`. Establish `h3` using `congrArg (fun u : (𝓞 E)ˣ => τ (algebraMap (𝓞 E) E u)) (hk (Units.mkOfMulEqOne p q hpq))`. Simplify using `only [Units.val_pow_eq_pow_val, Units.val_mkOfMulEqOne, map_pow, hp, Units.val_one, map_one] at h3`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[hψ]`. Express the relevant statement in the definitionally equal form `(1 : ℂ) = (θ (incA F E y) / star (θ (incA F E y))) ^ k`. Rewrite using `[hθ, div_pow, ← star_pow, h3, star_one, div_one])`. Set `C : (AE F E)ˣ →* (AE F E)ˣ` to `Units.map (cA σ).toMonoidHom`. Establish `hC : Continuous C` using `Continuous.units_map _ (cA_cont σ)`.

Set `μ : (AE F E)ˣ →* ℂˣ` to `ν.comp (MonoidHom.id _ / C)`. Establish `hμ : ∀ x, μ x = ν (x / C x)` using `fun x => rfl`. Establish `hμc : Continuous μ` using `hν.comp (continuous_id.div' hC)`. Use `⟨GlobalTheory.unitaryCharToCircle μ fun x => hνu _, ⟨Continuous.subtype_mk (Units.continuous_val.comp hμc) _, fun x => Circle.ext ?_⟩, fun a => Circle.ext ?_, fun x h1 h2 => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((ν (α x / C (α x)) : ℂˣ) : ℂ) = 1`.

Establish `: C (α x) = α (Units.map (σ : E →+* E).toMonoidHom x)` using `Units.ext rfl`. Rewrite using `[this, ← map_div, hν1]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `((ν (idF F E a / C (idF F E a)) : ℂˣ) : ℂ) = 1`. Establish `: C (idF F E a) = idF F E a` using `Units.ext (cA_base σ a)`.

Rewrite using `[this, div_self', map_one]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `((ν (x / C x) : ℂˣ) : ℂ) = _`. Establish `m1 : x ∈ S.units` using `(Submonoid.mem_units_iff _ _).2 ⟨(hint _).1 h1, (hint _).1 h2⟩`. Establish `m2 : C x ∈ S.units` using `(Submonoid.mem_units_iff _ _).2 ⟨(hint _).1 (cA_int σ _ h1), (hint _).1 (cA_int σ _ h2)⟩`.

Establish `e : θ ((x / C x : (AE F E)ˣ) : AE F E) = θ x / θ (cA σ x)`. Express the relevant statement in the definitionally equal form `((t (x / C x) : ℂˣ) : ℂ) = _`. Rewrite using `[map_div, Units.val_div_eq_div_val]`. Both sides reduce to the same expression. Rewrite using `[hνU _ (div_mem m1 m2), hψ, e]`.
-/
theorem exists_char (σ : E →ₐ[F] E) {k : ℕ} (hk : ∀ u : (𝓞 E)ˣ, u ^ k = 1)
    {θ : AE F E →+* ℂ} {τ : E →+* ℂ} (hθc : Continuous θ) (hθ : ∀ x, θ (incA F E x) = τ x)
    {Φ : AE F E →+* FiniteAdeleRing (𝓞 E) E} (hΦc : Continuous Φ)
    (hι : ∀ x, Φ (incA F E x) = algebraMap E _ x)
    (hint : ∀ y, finPart F E y ∈ intAE F E ↔ ∀ P, Valued.v (Φ y P) ≤ 1) :
    ∃ χ : (AE F E)ˣ →* Circle, IsHeckeChar F E χ ∧ (∀ a : (AF F)ˣ, χ (idF F E a) = 1) ∧
      ∀ x : (AE F E)ˣ, finPart F E (x : AE F E) ∈ intAE F E → finPart F E ((x⁻¹ : (AE F E)ˣ) : AE F E) ∈ intAE F E →
        (χ x : ℂ) = (θ x / θ (cA σ x) / star (θ x / θ (cA σ x))) ^ k := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  let S : Submonoid (AE F E) :=
    { carrier := {z | ∀ P, Valued.v (Φ z P) ≤ 1}
      one_mem' := fun P => by
        rw [RingHom.map_one]
        exact (map_one (Valued.v : Valuation (P.adicCompletion E) _)).le
      mul_mem' := fun {a b} ha hb P => by
        rw [RingHom.map_mul, GlobalTheory.PlaceIdem.mul_ap, map_mul]
        exact mul_le_one' (ha P) (hb P) }
  have hO : IsOpen {a : FiniteAdeleRing (𝓞 E) E | ∀ v, a v ∈ v.adicCompletionIntegers E} :=
    RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _
  have hS : IsOpen (S : Set (AE F E)) := hO.preimage hΦc
  let t : (AE F E)ˣ →* ℂˣ := Units.map θ.toMonoidHom
  let b : ℂˣ →* ℂˣ := Units.map (starRingEnd ℂ).toMonoidHom
  let ψ : (AE F E)ˣ →* ℂˣ := (t / b.comp t) ^ k
  have hψ : ∀ x, ((ψ x : ℂˣ) : ℂ) = (θ x / star (θ x)) ^ k := fun x => by
    change (((t x / b (t x)) ^ k : ℂˣ) : ℂ) = _
    rw [Units.val_pow_eq_pow_val, Units.val_div_eq_div_val]
    rfl
  have ht : Continuous t := Continuous.units_map _ hθc
  have hb : Continuous b := Continuous.units_map _ Complex.continuous_conj
  have hψc : Continuous ψ := (ht.div' (hb.comp ht)).pow k
  let α : Eˣ →* (AE F E)ˣ := Units.map (incA F E).toMonoidHom
  obtain ⟨ν, hν, hνu, hνU, hν1⟩ := GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (AE F E)ˣ Eˣ S.units
    (Submonoid.isOpen_units hS) α 1 ψ hψc
    (fun x => by
      have : θ x ≠ 0 := (t x).ne_zero
      rw [hψ, norm_pow, norm_div, norm_star, div_self (norm_ne_zero_iff.2 this), one_pow])
    (fun _ => by simp)
    (fun y hy => by
      obtain ⟨h1, h2⟩ := (Submonoid.mem_units_iff _ _).1 hy
      obtain ⟨p, hp⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E (y : E) (R := 𝓞 E) fun P => by
        rw [← val_alg, ← hι]; exact h1 P
      obtain ⟨q, hq⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E ((y⁻¹ : Eˣ) : E) (R := 𝓞 E) fun P => by
        rw [← val_alg, ← hι]; exact h2 P
      have hpq : p * q = 1 := by
        apply FaithfulSMul.algebraMap_injective (𝓞 E) E
        rw [map_mul, hp, hq, map_one, Units.mul_inv]
      have h3 := congrArg (fun u : (𝓞 E)ˣ => τ (algebraMap (𝓞 E) E u)) (hk (Units.mkOfMulEqOne p q hpq))
      simp only [Units.val_pow_eq_pow_val, Units.val_mkOfMulEqOne, map_pow, hp, Units.val_one, map_one] at h3
      apply Units.ext
      rw [hψ]
      change (1 : ℂ) = (θ (incA F E y) / star (θ (incA F E y))) ^ k
      rw [hθ, div_pow, ← star_pow, h3, star_one, div_one])
  let C : (AE F E)ˣ →* (AE F E)ˣ := Units.map (cA σ).toMonoidHom
  have hC : Continuous C := Continuous.units_map _ (cA_cont σ)
  let μ : (AE F E)ˣ →* ℂˣ := ν.comp (MonoidHom.id _ / C)
  have hμ : ∀ x, μ x = ν (x / C x) := fun x => rfl
  have hμc : Continuous μ := hν.comp (continuous_id.div' hC)
  refine ⟨GlobalTheory.unitaryCharToCircle μ fun x => hνu _,
    ⟨Continuous.subtype_mk (Units.continuous_val.comp hμc) _, fun x => Circle.ext ?_⟩, fun a => Circle.ext ?_,
    fun x h1 h2 => ?_⟩
  · change ((ν (α x / C (α x)) : ℂˣ) : ℂ) = 1
    have : C (α x) = α (Units.map (σ : E →+* E).toMonoidHom x) := Units.ext rfl
    rw [this, ← map_div, hν1]
    rfl
  · change ((ν (idF F E a / C (idF F E a)) : ℂˣ) : ℂ) = 1
    have : C (idF F E a) = idF F E a := Units.ext (cA_base σ a)
    rw [this, div_self', map_one]
    rfl
  · change ((ν (x / C x) : ℂˣ) : ℂ) = _
    have m1 : x ∈ S.units := (Submonoid.mem_units_iff _ _).2 ⟨(hint _).1 h1, (hint _).1 h2⟩
    have m2 : C x ∈ S.units := (Submonoid.mem_units_iff _ _).2 ⟨(hint _).1 (cA_int σ _ h1), (hint _).1 (cA_int σ _ h2)⟩
    have e : θ ((x / C x : (AE F E)ˣ) : AE F E) = θ x / θ (cA σ x) := by
      change ((t (x / C x) : ℂˣ) : ℂ) = _
      rw [map_div, Units.val_div_eq_div_val]
      rfl
    rw [hνU _ (div_mem m1 m2), hψ, e]

/- English proof (translation)
Take `⟨θ, τ, hθc, hθ, hθ0⟩` from `exists_arch (F := F) (E := E)`. Take `⟨Φ, hΦc, hι, hint⟩` from `exists_fin (F := F) (E := E)`. Take `⟨χ, hχ, hχF, hχU⟩` from `exists_char σ hk hθc hθ hΦc hι hint`. Choose the witnesses or unpack the hypotheses as in `⟨π, hπ, hne⟩ : ∃ π : 𝓞 E, Prime π ∧ σ (π : E) ^ (2 * k) ≠ (π : E) ^ (2 * k) := by`. Assume the negation of the conclusion as `hc`.

Use `push Not at hc`. Use `ha (UniqueFactorizationMonoid.induction_on_prime (P := fun b : 𝓞 E => σ (b : E) ^ (2 * k) = (b : E) ^ (2 * k)) a ?_ ?_ ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `σ 0 ^ _ = 0 ^ _`. Rewrite using `[map_zero]`. Introduce and unpack `x ⟨u, rfl⟩`.

Establish `h3` using `congrArg (fun u : (𝓞 E)ˣ => algebraMap (𝓞 E) E u) (hk u)`. Simplify using `only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at h3`. Express the relevant statement in the definitionally equal form `σ (algebraMap (𝓞 E) E u) ^ _ = (algebraMap (𝓞 E) E u) ^ _`. Rewrite using `[← map_pow, pow_mul', h3, one_pow, map_one]`. Introduce `b p _ hp hb`.

Express the relevant statement in the definitionally equal form `σ ((p : E) * b) ^ _ = ((p : E) * b) ^ _`. Rewrite using `[map_mul, mul_pow, mul_pow, hb, hc p hp]`. Set `P : HeightOneSpectrum (𝓞 E)` to `⟨Ideal.span {π}, (Ideal.span_singleton_prime hπ.ne_zero).2 hπ, by simpa using hπ.ne_zero⟩`. Establish `hex : ∃ x, IsUnifIdele σ P x`. Assume the negation of the conclusion as `hc`.

Use `GlobalTheory.CMPrimeIdele.chiAt_one F E σ hσ P` as an intermediate fact. Rewrite `this` using `[chiAt, dif_neg fun h => hc h.2]`. Conclude with `zero_ne_one this`. Establish `harch : ∀ {e f z : AE F E} {x : AE F E}, IsPrimeIdem σ P e f → x = e * z + (1 - e) → θ x = 1 ∧ θ (cA σ x) = 1`. Introduce `e f z x he hx`.

Take `⟨d1, d2⟩` from `idem_arch hθ0 he`. Prove the components needed by the constructor for the conclusion. Rewrite using `[hx, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, d1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hx]`.

Simplify using `only [RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, d2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hunr : IsUnramAt σ χ P`. Take `⟨x, e, f, ϖ, he, -⟩` from `hex`. Use `⟨e, f, he, fun y hy h1 h2 => Circle.ext ?_⟩` and prove the remaining obligations.

Take `⟨d1, d2⟩` from `harch he hy`. Rewrite using `[hχU y h1 h2, d1, d2]`. Simplify using the standard rewrite rules. Establish `hval : ∀ x, IsUnifIdele σ P x → χ x ≠ 1`. Introduce `x hx h1`.

Establish `hπ0 : (π : E) ≠ 0` using `by exact_mod_cast hπ.ne_zero`. Set `p : (AE F E)ˣ` to `Units.map (incA F E).toMonoidHom (Units.mk0 (π : E) hπ0)`. Establish `hv` using `unif_val hι hint (P := P) (π := π) rfl hx`. Take `⟨e, f, ϖ, he, -, -, hx⟩` from `hx`. Take `⟨d1, d2⟩` from `harch he hx`.

Establish `hp : ∀ Q : HeightOneSpectrum (𝓞 E), Valued.v (Φ (p : AE F E) Q) = Q.valuation E (π : E)` using `fun Q => by`. Express the relevant statement in the definitionally equal form `Valued.v (Φ (incA F E (π : E)) Q) = _`. Rewrite using `[hι, val_alg]`. Establish `hq : ∀ y z : (AE F E)ˣ, (∀ Q : HeightOneSpectrum (𝓞 E), Valued.v (Φ (y : AE F E) Q) = Q.valuation E (π : E)) → (∀ Q : HeightOneSpectrum (𝓞 E), Valued.v (Φ (z : AE F E) Q) = Q.valuation E (π : E)) → finPart F E ((y / z : (AE F E)ˣ) : AE F E) ∈ intAE F E`. Introduce `y z hy hz`.

Use `(hint _).2 fun Q => le_of_eq ?_` and prove the remaining obligations. Establish `h2` using `hy Q`. Rewrite `h2` using `[← div_mul_cancel y z, Units.val_mul, RingHom.map_mul, GlobalTheory.PlaceIdem.mul_ap, map_mul, hz]`. Establish `h0 : Q.valuation E (π : E) ≠ 0` using `by simpa using hπ0`. Conclude with `mul_right_cancel₀ h0 (h2.trans (one_mul _).symm)`.

Establish `h2` using `hχU (p / x) (hq _ _ hp hv) (by rw [inv_div]; exact hq _ _ hv hp)`. Establish `h3 : θ ((p / x : (AE F E)ˣ) : AE F E) = τ π`. Use `congrArg (fun y : (AE F E)ˣ => θ (y : AE F E)) (div_mul_cancel p x)` as an intermediate fact. Simplify using `only [Units.val_mul, RingHom.map_mul, d1, mul_one] at this`. Conclude with `this.trans (hθ _)`.

Establish `h4 : θ (cA σ ((p / x : (AE F E)ˣ) : AE F E)) = star (τ π)`. Use `congrArg (fun y : (AE F E)ˣ => θ (cA σ (y : AE F E))) (div_mul_cancel p x)` as an intermediate fact. Simplify using `only [Units.val_mul, RingHom.map_mul, d2, mul_one] at this`. Conclude with `this.trans ((hθ (σ π)).trans (hσ.2.2.2 τ _))`. Establish `h5 : χ p = 1` using `hχ.2 _`.

Rewrite `h2` using `[map_div, h5, h1, div_one, h3, h4]`. Establish `t0 : τ π ≠ 0` using `by simpa using hπ0`. Establish `t1 : star (τ π) ≠ 0` using `by simpa using hπ0`. Apply `hne` to reduce the goal to its premises. Apply `τ.injective` to reduce the goal to its premises.

Rewrite using `[map_pow, map_pow, hσ.2.2.2, eq_comm, ← div_eq_one_iff_eq (pow_ne_zero _ t1), ← div_pow, pow_mul]`. Rewrite `h2` using `[star_div₀, star_star]`. Use `Eq.trans ?_ h2.symm` and prove the remaining obligations. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Establish `hc : chiAt σ χ P = ((χ hex.choose : Circle) : ℂ)`. Rewrite using `[chiAt, dif_pos ⟨hunr, hex⟩]`. Use `⟨χ, hχ, hχF, fun h => hval _ hex.choose_spec (by rw [h]; rfl), P, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hc]`. Conclude with `Circle.coe_ne_zero _`.

Rewrite using `[hc]`. Conclude with `fun h => hval _ hex.choose_spec (Circle.ext h)`.
-/
theorem exists_of_principal (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) [IsPrincipalIdealRing (𝓞 E)] {k : ℕ}
    (hk : ∀ u : (𝓞 E)ˣ, u ^ k = 1) (a : 𝓞 E) (ha : σ (a : E) ^ (2 * k) ≠ (a : E) ^ (2 * k)) :
    ∃ χ : (AE F E)ˣ →* Circle, IsHeckeChar F E χ ∧ (∀ a : (AF F)ˣ, χ (idF F E a) = 1) ∧ χ ≠ 1 ∧
      ∃ P : HeightOneSpectrum (𝓞 E), chiAt σ χ P ≠ 0 ∧ chiAt σ χ P ≠ 1 := by
  obtain ⟨θ, τ, hθc, hθ, hθ0⟩ := exists_arch (F := F) (E := E)
  obtain ⟨Φ, hΦc, hι, hint⟩ := exists_fin (F := F) (E := E)
  obtain ⟨χ, hχ, hχF, hχU⟩ := exists_char σ hk hθc hθ hΦc hι hint
  obtain ⟨π, hπ, hne⟩ : ∃ π : 𝓞 E, Prime π ∧ σ (π : E) ^ (2 * k) ≠ (π : E) ^ (2 * k) := by
    by_contra hc
    push Not at hc
    refine ha (UniqueFactorizationMonoid.induction_on_prime
      (P := fun b : 𝓞 E => σ (b : E) ^ (2 * k) = (b : E) ^ (2 * k)) a ?_ ?_ ?_)
    · change σ 0 ^ _ = 0 ^ _
      rw [map_zero]
    · rintro x ⟨u, rfl⟩
      have h3 := congrArg (fun u : (𝓞 E)ˣ => algebraMap (𝓞 E) E u) (hk u)
      simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at h3
      change σ (algebraMap (𝓞 E) E u) ^ _ = (algebraMap (𝓞 E) E u) ^ _
      rw [← map_pow, pow_mul', h3, one_pow, map_one]
    · intro b p _ hp hb
      change σ ((p : E) * b) ^ _ = ((p : E) * b) ^ _
      rw [map_mul, mul_pow, mul_pow, hb, hc p hp]
  let P : HeightOneSpectrum (𝓞 E) :=
    ⟨Ideal.span {π}, (Ideal.span_singleton_prime hπ.ne_zero).2 hπ, by simpa using hπ.ne_zero⟩
  have hex : ∃ x, IsUnifIdele σ P x := by
    by_contra hc
    have := GlobalTheory.CMPrimeIdele.chiAt_one F E σ hσ P
    rw [chiAt, dif_neg fun h => hc h.2] at this
    exact zero_ne_one this
  have harch : ∀ {e f z : AE F E} {x : AE F E}, IsPrimeIdem σ P e f → x = e * z + (1 - e) →
      θ x = 1 ∧ θ (cA σ x) = 1 := by
    intro e f z x he hx
    obtain ⟨d1, d2⟩ := idem_arch hθ0 he
    constructor
    · rw [hx, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, d1]; ring
    · rw [hx]
      simp only [RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, d2]; ring
  have hunr : IsUnramAt σ χ P := by
    obtain ⟨x, e, f, ϖ, he, -⟩ := hex
    refine ⟨e, f, he, fun y hy h1 h2 => Circle.ext ?_⟩
    obtain ⟨d1, d2⟩ := harch he hy
    rw [hχU y h1 h2, d1, d2]
    simp
  have hval : ∀ x, IsUnifIdele σ P x → χ x ≠ 1 := by
    intro x hx h1
    have hπ0 : (π : E) ≠ 0 := by exact_mod_cast hπ.ne_zero
    let p : (AE F E)ˣ := Units.map (incA F E).toMonoidHom (Units.mk0 (π : E) hπ0)
    have hv := unif_val hι hint (P := P) (π := π) rfl hx
    obtain ⟨e, f, ϖ, he, -, -, hx⟩ := hx
    obtain ⟨d1, d2⟩ := harch he hx
    have hp : ∀ Q : HeightOneSpectrum (𝓞 E), Valued.v (Φ (p : AE F E) Q) = Q.valuation E (π : E) := fun Q => by
      change Valued.v (Φ (incA F E (π : E)) Q) = _
      rw [hι, val_alg]
    have hq : ∀ y z : (AE F E)ˣ, (∀ Q : HeightOneSpectrum (𝓞 E), Valued.v (Φ (y : AE F E) Q) = Q.valuation E (π : E)) →
        (∀ Q : HeightOneSpectrum (𝓞 E), Valued.v (Φ (z : AE F E) Q) = Q.valuation E (π : E)) →
        finPart F E ((y / z : (AE F E)ˣ) : AE F E) ∈ intAE F E := by
      intro y z hy hz
      refine (hint _).2 fun Q => le_of_eq ?_
      have h2 := hy Q
      rw [← div_mul_cancel y z, Units.val_mul, RingHom.map_mul, GlobalTheory.PlaceIdem.mul_ap, map_mul, hz] at h2
      have h0 : Q.valuation E (π : E) ≠ 0 := by simpa using hπ0
      exact mul_right_cancel₀ h0 (h2.trans (one_mul _).symm)
    have h2 := hχU (p / x) (hq _ _ hp hv) (by rw [inv_div]; exact hq _ _ hv hp)
    have h3 : θ ((p / x : (AE F E)ˣ) : AE F E) = τ π := by
      have := congrArg (fun y : (AE F E)ˣ => θ (y : AE F E)) (div_mul_cancel p x)
      simp only [Units.val_mul, RingHom.map_mul, d1, mul_one] at this
      exact this.trans (hθ _)
    have h4 : θ (cA σ ((p / x : (AE F E)ˣ) : AE F E)) = star (τ π) := by
      have := congrArg (fun y : (AE F E)ˣ => θ (cA σ (y : AE F E))) (div_mul_cancel p x)
      simp only [Units.val_mul, RingHom.map_mul, d2, mul_one] at this
      exact this.trans ((hθ (σ π)).trans (hσ.2.2.2 τ _))
    have h5 : χ p = 1 := hχ.2 _
    rw [map_div, h5, h1, div_one, h3, h4] at h2
    have t0 : τ π ≠ 0 := by simpa using hπ0
    have t1 : star (τ π) ≠ 0 := by simpa using hπ0
    apply hne
    apply τ.injective
    rw [map_pow, map_pow, hσ.2.2.2, eq_comm, ← div_eq_one_iff_eq (pow_ne_zero _ t1), ← div_pow, pow_mul]
    rw [star_div₀, star_star] at h2
    refine Eq.trans ?_ h2.symm
    congr 1
    field_simp
  have hc : chiAt σ χ P = ((χ hex.choose : Circle) : ℂ) := by
    rw [chiAt, dif_pos ⟨hunr, hex⟩]
  refine ⟨χ, hχ, hχF, fun h => hval _ hex.choose_spec (by rw [h]; rfl), P, ?_, ?_⟩
  · rw [hc]; exact Circle.coe_ne_zero _
  · rw [hc]; exact fun h => hval _ hex.choose_spec (Circle.ext h)

end General

/- English proof (translation)
Set `K` to `CyclotomicField 3 ℚ`. Use `haveI : IsCMField K := IsCyclotomicExtension.Rat.isCMField K (S := {3}) ⟨3, rfl, by norm_num⟩`. Use `haveI := IsCyclotomicExtension.Rat.three_pid K`. Establish `hζ` using `IsCyclotomicExtension.zeta_spec 3 ℚ K`. Set `σ : K →ₐ[maximalRealSubfield K] K` to `IsCMField.complexConj K`.

Establish `hσ : IsCMExt (maximalRealSubfield K) K σ` using `⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _, fun τ x => IsCMField.complexEmbedding_complexConj K τ x⟩`. Use `⟨maximalRealSubfield K, K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, σ, hσ, exists_of_principal σ hσ (k := 6) (fun u => ?_) (3 + hζ.toInteger) ?_⟩` and prove the remaining obligations. Establish `hu` using `IsCyclotomicExtension.Rat.Three.Units.mem hζ u`. Generalize the expression as in `hη : (IsUnit.unit _ : (𝓞 K)ˣ) = η at hu`. Establish `h3 : η ^ 3 = 1`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[← hη, Units.val_pow_eq_pow_val, IsUnit.unit_spec]`. Conclude with `hζ.toInteger_isPrimitiveRoot.pow_eq_one`. Establish `h6 : η ^ 6 = 1` using `by rw [show 6 = 3 * 2 from rfl, pow_mul, h3, one_pow]`. Establish `ev : Even 6` using `by decide`.

Simplify using `only [List.mem_cons, List.not_mem_nil, or_false] at hu`. Apply the tactic sequence `rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;>`. Simplify using `only [ev.neg_pow, one_pow, h6, pow_right_comm _ 2 6]`. Take `⟨ζ, hz⟩ : ∃ ζ, ζ = IsCyclotomicExtension.zeta 3 ℚ K` from `⟨_, rfl⟩`. Express the relevant statement in the definitionally equal form `σ (3 + IsCyclotomicExtension.zeta 3 ℚ K) ^ _ ≠ (3 + IsCyclotomicExtension.zeta 3 ℚ K) ^ _`.

Rewrite `hζ`, the goal using `[← hz]`. Establish `h1 : ζ ^ 2 = -1 - ζ`. Use `hζ.geom_sum_eq_zero (by norm_num)` as an intermediate fact. Simplify using `only [Finset.sum_range_succ, Finset.sum_range_zero] at this`. Take the linear combination `this`.

Establish `a2 : (3 + ζ) ^ 2 = 8 + 5 * ζ` using `by linear_combination h1`. Establish `a4 : (8 + 5 * ζ) ^ 2 = 39 + 55 * ζ` using `by linear_combination 25 * h1`. Establish `a8 : (39 + 55 * ζ) ^ 2 = -1504 + 1265 * ζ` using `by linear_combination 3025 * h1`. Establish `a12 : (3 + ζ) ^ (2 * 6) = -128231 - 102960 * ζ`. Rewrite using `[show 2 * 6 = 2 * 2 * 3 from rfl, pow_mul, pow_mul, a2, a4, pow_succ, a8]`.

Take the linear combination `69575 * h1`. Introduce `h`. Rewrite `h` using `[← map_pow, a12, map_sub, map_mul, map_neg, map_ofNat, map_ofNat]`. Establish `h2 : σ ζ = ζ` using `by linear_combination (-1 / 102960 : K) * h`. Take `⟨τ⟩ : Nonempty (K →+* ℂ)` from `inferInstance`.

Establish `h3` using `hσ.2.2.2 τ ζ`. Rewrite `h3` using `[h2]`. Establish `h4` using `congrArg τ h1`. Rewrite `h4` using `[map_pow, map_sub, map_neg, map_one]`. Take `⟨r, hr⟩` from `Complex.conj_eq_iff_real.1 h3.symm`.

Rewrite `h4` using `[hr]`. Establish `h5 : r ^ 2 = -1 - r` using `by exact_mod_cast h4`. Use polynomial arithmetic with `[sq_nonneg (2 * r + 1)]`.
-/
theorem exists_nontrivial_heckeChar : ∃ (F E : Type) (_ : Field F) (_ : NumberField F) (_ : Field E) (_ : NumberField E) (_ : Algebra F E) (σ : E →ₐ[F] E), IsCMExt F E σ ∧ ∃ χ : (AE F E)ˣ →* Circle, IsHeckeChar F E χ ∧ (∀ a : (AF F)ˣ, χ (idF F E a) = 1) ∧ χ ≠ 1 ∧ ∃ P : HeightOneSpectrum (𝓞 E), chiAt σ χ P ≠ 0 ∧ chiAt σ χ P ≠ 1 := by
  let K := CyclotomicField 3 ℚ
  haveI : IsCMField K := IsCyclotomicExtension.Rat.isCMField K (S := {3}) ⟨3, rfl, by norm_num⟩
  haveI := IsCyclotomicExtension.Rat.three_pid K
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  let σ : K →ₐ[maximalRealSubfield K] K := IsCMField.complexConj K
  have hσ : IsCMExt (maximalRealSubfield K) K σ :=
    ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _,
      fun τ x => IsCMField.complexEmbedding_complexConj K τ x⟩
  refine ⟨maximalRealSubfield K, K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, σ, hσ,
    exists_of_principal σ hσ (k := 6) (fun u => ?_) (3 + hζ.toInteger) ?_⟩
  · have hu := IsCyclotomicExtension.Rat.Three.Units.mem hζ u
    generalize hη : (IsUnit.unit _ : (𝓞 K)ˣ) = η at hu
    have h3 : η ^ 3 = 1 := by
      apply Units.ext
      rw [← hη, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
      exact hζ.toInteger_isPrimitiveRoot.pow_eq_one
    have h6 : η ^ 6 = 1 := by rw [show 6 = 3 * 2 from rfl, pow_mul, h3, one_pow]
    have ev : Even 6 := by decide
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [ev.neg_pow, one_pow, h6, pow_right_comm _ 2 6]
  · obtain ⟨ζ, hz⟩ : ∃ ζ, ζ = IsCyclotomicExtension.zeta 3 ℚ K := ⟨_, rfl⟩
    change σ (3 + IsCyclotomicExtension.zeta 3 ℚ K) ^ _ ≠ (3 + IsCyclotomicExtension.zeta 3 ℚ K) ^ _
    rw [← hz] at hζ ⊢
    have h1 : ζ ^ 2 = -1 - ζ := by
      have := hζ.geom_sum_eq_zero (by norm_num)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
      linear_combination this
    have a2 : (3 + ζ) ^ 2 = 8 + 5 * ζ := by linear_combination h1
    have a4 : (8 + 5 * ζ) ^ 2 = 39 + 55 * ζ := by linear_combination 25 * h1
    have a8 : (39 + 55 * ζ) ^ 2 = -1504 + 1265 * ζ := by linear_combination 3025 * h1
    have a12 : (3 + ζ) ^ (2 * 6) = -128231 - 102960 * ζ := by
      rw [show 2 * 6 = 2 * 2 * 3 from rfl, pow_mul, pow_mul, a2, a4, pow_succ, a8]
      linear_combination 69575 * h1
    intro h
    rw [← map_pow, a12, map_sub, map_mul, map_neg, map_ofNat, map_ofNat] at h
    have h2 : σ ζ = ζ := by linear_combination (-1 / 102960 : K) * h
    obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have h3 := hσ.2.2.2 τ ζ
    rw [h2] at h3
    have h4 := congrArg τ h1
    rw [map_pow, map_sub, map_neg, map_one] at h4
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h3.symm
    rw [hr] at h4
    have h5 : r ^ 2 = -1 - r := by exact_mod_cast h4
    nlinarith [sq_nonneg (2 * r + 1)]

end GlobalTheory.HeckeInhabitant
