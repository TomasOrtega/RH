import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DifferentIdealEqTop

open NumberField Module Filter Topology
open scoped Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BoxSum

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

def rEmb (w : {w : InfinitePlace F // w.IsReal}) : 𝓞 F →+* ℝ :=
  (InfinitePlace.embedding_of_isReal w.2).comp (algebraMap (𝓞 F) F)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rEmb_apply (w : {w : InfinitePlace F // w.IsReal}) (n : 𝓞 F) :
    rEmb w n = InfinitePlace.embedding_of_isReal w.2 (n : F) := rfl

/- English proof (translation)
Establish `hR : IsTotallyReal F` using `QuadraticExtensionConjugation.isTotallyReal hK hF`. Prove the components needed by the constructor for the conclusion. Introduce `h w`. Set `_ : Algebra F ℂ` to `w.1.embedding.toAlgebra`. Set `φ : K →ₐ[F] ℂ` to `IsAlgClosed.lift`.

Establish `h1 : φ (algebraMap F K (n : F)) = w.1.embedding (n : F)` using `φ.commutes _`. Establish `h2` using `h φ.toRingHom`. Establish `h3 : (φ.toRingHom (algebraMap F K (n : F))).re = rEmb w n` using `by show (φ (algebraMap F K (n : F))).re = _`. Rewrite using `[h1, rEmb_apply, ← InfinitePlace.embedding_of_isReal_apply w.2, Complex.ofReal_re]`. Rewrite `h2` using `[h3]`. Then use the resulting hypothesis.

Introduce `h φ`. Establish `hw : (InfinitePlace.mk (φ.comp (algebraMap F K))).IsReal` using `IsTotallyReal.isReal _`. Establish `h1` using `InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 hw)`. Establish `h3 : (φ (algebraMap F K (n : F))).re = rEmb ⟨_, hw⟩ n`. Rewrite using `[rEmb_apply, ← Complex.ofReal_re (InfinitePlace.embedding_of_isReal _ _), InfinitePlace.embedding_of_isReal_apply hw, h1]`.

Both sides reduce to the same expression. Rewrite using `[h3]`. Conclude with `h _`.
-/
theorem mem_boxSet_iff (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {T : ℝ} {n : 𝓞 F} :
    n ∈ boxSet K F T ↔ ∀ w : {w : InfinitePlace F // w.IsReal}, 0 < rEmb w n ∧ rEmb w n ≤ T := by
  have hR : IsTotallyReal F := QuadraticExtensionConjugation.isTotallyReal hK hF
  constructor
  · intro h w
    let _ : Algebra F ℂ := w.1.embedding.toAlgebra
    let φ : K →ₐ[F] ℂ := IsAlgClosed.lift
    have h1 : φ (algebraMap F K (n : F)) = w.1.embedding (n : F) := φ.commutes _
    have h2 := h φ.toRingHom
    have h3 : (φ.toRingHom (algebraMap F K (n : F))).re = rEmb w n := by
      show (φ (algebraMap F K (n : F))).re = _
      rw [h1, rEmb_apply, ← InfinitePlace.embedding_of_isReal_apply w.2, Complex.ofReal_re]
    rwa [h3] at h2
  · intro h φ
    have hw : (InfinitePlace.mk (φ.comp (algebraMap F K))).IsReal := IsTotallyReal.isReal _
    have h1 := InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 hw)
    have h3 : (φ (algebraMap F K (n : F))).re = rEmb ⟨_, hw⟩ n := by
      rw [rEmb_apply, ← Complex.ofReal_re (InfinitePlace.embedding_of_isReal _ _),
        InfinitePlace.embedding_of_isReal_apply hw, h1]
      rfl
    rw [h3]
    exact h _

/- English proof (translation)
Establish `h1 : (Ideal.absNorm (Ideal.span {n}) : ℝ) = |((Algebra.norm ℚ (n : F) : ℚ) : ℝ)|`. Rewrite using `[Ideal.absNorm_span_singleton, Nat.cast_natAbs, ← Algebra.coe_norm_int]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[h1, ← Rat.cast_abs, ← InfinitePlace.prod_eq_abs_norm]`.

Establish `h2 : ∀ w : InfinitePlace F, w.IsReal` using `fun w => IsTotallyReal.isReal w`. Rewrite using `[Finset.prod_subtype (p := fun w : InfinitePlace F => w.IsReal) Finset.univ (by simp [h2]) (fun w => w (n : F) ^ w.mult)]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[InfinitePlace.mult, if_pos w.2, pow_one, rEmb_apply, ← Real.norm_eq_abs, InfinitePlace.norm_embedding_of_isReal]`.
-/
theorem absNorm_eq_prod [IsTotallyReal F] (n : 𝓞 F) :
    (Ideal.absNorm (Ideal.span {n}) : ℝ) = ∏ w : {w : InfinitePlace F // w.IsReal}, |rEmb w n| := by
  have h1 : (Ideal.absNorm (Ideal.span {n}) : ℝ) = |((Algebra.norm ℚ (n : F) : ℚ) : ℝ)| := by
    rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, ← Algebra.coe_norm_int]
    push_cast
    rfl
  rw [h1, ← Rat.cast_abs, ← InfinitePlace.prod_eq_abs_norm]
  have h2 : ∀ w : InfinitePlace F, w.IsReal := fun w => IsTotallyReal.isReal w
  rw [Finset.prod_subtype (p := fun w : InfinitePlace F => w.IsReal) Finset.univ (by simp [h2])
    (fun w => w (n : F) ^ w.mult)]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [InfinitePlace.mult, if_pos w.2, pow_one, rEmb_apply, ← Real.norm_eq_abs,
    InfinitePlace.norm_embedding_of_isReal]

/- English proof (translation)
Establish `hR : IsTotallyReal F` using `QuadraticExtensionConjugation.isTotallyReal hK hF`. Rewrite using `[absNorm_eq_prod]`. Conclude with `Finset.prod_congr rfl fun w _ => abs_of_pos (((mem_boxSet_iff hK hF).1 hn) w).1`.
-/
theorem absNorm_eq_prod_of_mem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {T : ℝ} {n : 𝓞 F}
    (hn : n ∈ boxSet K F T) :
    (Ideal.absNorm (Ideal.span {n}) : ℝ) = ∏ w : {w : InfinitePlace F // w.IsReal}, rEmb w n := by
  have hR : IsTotallyReal F := QuadraticExtensionConjugation.isTotallyReal hK hF
  rw [absNorm_eq_prod]
  exact Finset.prod_congr rfl fun w _ => abs_of_pos (((mem_boxSet_iff hK hF).1 hn) w).1

/- English proof (translation)
Establish `hR : IsTotallyReal F` using `QuadraticExtensionConjugation.isTotallyReal hK hF`. Establish `h1` using `(discrTower K F hK hF).2.1`. Rewrite using `[← h1, IsTotallyReal.finrank]`.
-/
theorem card_real (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) :
    Fintype.card {w : InfinitePlace F // w.IsReal} = Formalism.HermitianLatticesTheory.fDeg K := by
  have hR : IsTotallyReal F := QuadraticExtensionConjugation.isTotallyReal hK hF
  have h1 := (discrTower K F hK hF).2.1
  rw [← h1, IsTotallyReal.finrank]

/- English proof (translation)
Establish `hR : IsTotallyReal F` using `QuadraticExtensionConjugation.isTotallyReal hK hF`. Establish `h0` using `Embeddings.finite_of_norm_le F ℂ T`. Use `Set.Finite.of_finite_image (f := fun n : 𝓞 F => (n : F)) (h0.subset ?_) (RingOfIntegers.coe_injective.injOn)` and prove the remaining obligations. Introduce and unpack `_ ⟨n, hn, rfl⟩`. Use `⟨n.2, fun ψ => ?_⟩` and prove the remaining obligations.

Establish `hw : (InfinitePlace.mk ψ).IsReal` using `IsTotallyReal.isReal _`. Establish `h1` using `((mem_boxSet_iff hK hF).1 hn) ⟨_, hw⟩`. Establish `h2 : ‖ψ (n : F)‖ = |rEmb ⟨_, hw⟩ n|`. Rewrite using `[rEmb_apply, ← Real.norm_eq_abs, InfinitePlace.norm_embedding_of_isReal]`. Both sides reduce to the same expression.

Rewrite using `[h2, abs_of_pos h1.1]`. Conclude with `h1.2`.
-/
theorem finite_boxSet (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (T : ℝ) :
    (boxSet K F T).Finite := by
  have hR : IsTotallyReal F := QuadraticExtensionConjugation.isTotallyReal hK hF
  have h0 := Embeddings.finite_of_norm_le F ℂ T
  refine Set.Finite.of_finite_image (f := fun n : 𝓞 F => (n : F)) (h0.subset ?_)
    (RingOfIntegers.coe_injective.injOn)
  rintro _ ⟨n, hn, rfl⟩
  refine ⟨n.2, fun ψ => ?_⟩
  have hw : (InfinitePlace.mk ψ).IsReal := IsTotallyReal.isReal _
  have h1 := ((mem_boxSet_iff hK hF).1 hn) ⟨_, hw⟩
  have h2 : ‖ψ (n : F)‖ = |rEmb ⟨_, hw⟩ n| := by
    rw [rEmb_apply, ← Real.norm_eq_abs, InfinitePlace.norm_embedding_of_isReal]
    rfl
  rw [h2, abs_of_pos h1.1]
  exact h1.2

/- English proof (translation)
Introduce and unpack `rfl`. Take `⟨φ⟩ : Nonempty (K →+* ℂ)` from `inferInstance`. Use `(hn φ).1` as an intermediate fact. Simplify using `at this`.
-/
theorem ne_zero_of_mem_boxSet {T : ℝ} {n : 𝓞 F} (hn : n ∈ boxSet K F T) : n ≠ 0 := by
  rintro rfl
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have := (hn φ).1
  simp at this

/- English proof (translation)
Rewrite using `[absNorm_eq_prod_of_mem hK hF hn, ← card_real hK hF, ← Finset.card_univ, ← Finset.prod_const]`. Conclude with `Finset.prod_le_prod (fun w _ => (((mem_boxSet_iff hK hF).1 hn) w).1.le) fun w _ => (((mem_boxSet_iff hK hF).1 hn) w).2`.
-/
theorem absNorm_le_of_mem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {T : ℝ} {n : 𝓞 F}
    (hn : n ∈ boxSet K F T) :
    (Ideal.absNorm (Ideal.span {n}) : ℝ) ≤ T ^ Formalism.HermitianLatticesTheory.fDeg K := by
  rw [absNorm_eq_prod_of_mem hK hF hn, ← card_real hK hF, ← Finset.card_univ, ← Finset.prod_const]
  exact Finset.prod_le_prod (fun w _ => (((mem_boxSet_iff hK hF).1 hn) w).1.le)
    fun w _ => (((mem_boxSet_iff hK hF).1 hn) w).2

end Formalism.HermitianLattices.Ext.L3.BoxSum
