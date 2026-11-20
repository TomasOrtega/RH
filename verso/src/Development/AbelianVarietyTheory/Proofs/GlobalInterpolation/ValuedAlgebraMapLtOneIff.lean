import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SplittingProjection
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.OverPlaceIntegralForm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGlobalUniformizerResidueRepresentatives
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SplitUnitaryGroupIso
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Transport
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stabstd

noncomputable section

namespace GlobalTheory.OverCompare

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

section Unitary

/- English proof (translation)
Take `⟨e, he⟩` from `Formalism.UG.P.split_group_points F E n σ J K φ hφ`. Use `set ρ : E →+* K := ((RingHom.fst _ _).comp φ.toRingHom).comp (inclE (F := F) K) with hρ`. Establish `hsp : J.map ((φ : E ⊗[F] K →+* K × K).comp (inclE (F` using `F) K)) = splitJ (J.map ρ) := by`. Use extensionality with `i j`. Both sides reduce to the same expression.

Establish `h1 : σ (J i j) = J j i` using `congrFun (congrFun hJ j) i`. Establish `h2` using `congrArg Prod.fst (hφ (inclE (F := F) K (J i j)))`. Establish `h3 : sigR σ K (inclE (F` using `F) K (J i j)) = inclE (F := F) K (J j i) := by`. Rewrite using `[← h1]`. Both sides reduce to the same expression.

Rewrite `h2` using `[h3]`. Conclude with `h2.symm`. Establish `hd' : IsUnit (J.map ρ).det`. Use `hd.map ρ` as an intermediate fact. Rewrite `this` using `[RingHom.map_det]`. Then use the resulting hypothesis.

Establish `hbc : ∀ g : GL n (E ⊗[F] K), bc ((RingHom.fst _ _).comp φ.toRingHom) g = bc (RingHom.fst K K) (bc (φ : E ⊗[F] K →+* K × K) g)` using `fun g => by`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Both sides reduce to the same expression. Take `⟨g, hg, hg'⟩` from `Formalism.UG.P.split_surjective (J.map ρ) hd' g'`.

Use `⟨e.symm ⟨g, hsp ▸ hg⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show bc _ _ = _`. Rewrite using `[hbc, ← he, MulEquiv.apply_symm_apply]`. Conclude with `hg'`. Introduce `y hy`.

Apply `e.injective` to reduce the goal to its premises. Rewrite using `[MulEquiv.apply_symm_apply]`. Apply `Subtype.ext` to reduce the goal to its premises. Use `Formalism.UG.P.split_injective (J.map ρ) hd' _ _ (hsp ▸ (e y).2) hg ?_` and prove the remaining obligations. Establish `hy' : bc (RingHom.fst K K) (e y : GL n (K × K)) = bc (RingHom.fst K K) g`.

Rewrite using `[hg', he, ← hbc]`. Conclude with `hy`. Conclude with `congrArg Units.val hy'`.
-/
theorem existsUnique_upts {F E : Type} [Field F] [Field E] [Algebra F E] {n : Type} [Fintype n]
    [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (hJ : IsHerm (σ : E →+* E) J)
    (hd : IsUnit J.det) (K : Type) [CommRing K] [Algebra F K] (φ : E ⊗[F] K ≃+* K × K)
    (hφ : ∀ x, φ (sigR σ K x) = swapR K (φ x)) (g' : GL n K) :
    ∃! g : UPts σ J K, bc ((RingHom.fst _ _).comp φ.toRingHom) g.1 = g' := by
  obtain ⟨e, he⟩ := Formalism.UG.P.split_group_points F E n σ J K φ hφ
  set ρ : E →+* K := ((RingHom.fst _ _).comp φ.toRingHom).comp (inclE (F := F) K) with hρ
  have hsp : J.map ((φ : E ⊗[F] K →+* K × K).comp (inclE (F := F) K)) = splitJ (J.map ρ) := by
    ext i j
    · rfl
    · have h1 : σ (J i j) = J j i := congrFun (congrFun hJ j) i
      have h2 := congrArg Prod.fst (hφ (inclE (F := F) K (J i j)))
      have h3 : sigR σ K (inclE (F := F) K (J i j)) = inclE (F := F) K (J j i) := by
        rw [← h1]; rfl
      rw [h3] at h2
      exact h2.symm
  have hd' : IsUnit (J.map ρ).det := by
    have := hd.map ρ
    rwa [RingHom.map_det] at this
  have hbc : ∀ g : GL n (E ⊗[F] K), bc ((RingHom.fst _ _).comp φ.toRingHom) g =
      bc (RingHom.fst K K) (bc (φ : E ⊗[F] K →+* K × K) g) := fun g => by
    apply Units.ext; ext i j; rfl
  obtain ⟨g, hg, hg'⟩ := Formalism.UG.P.split_surjective (J.map ρ) hd' g'
  refine ⟨e.symm ⟨g, hsp ▸ hg⟩, ?_, ?_⟩
  · show bc _ _ = _
    rw [hbc, ← he, MulEquiv.apply_symm_apply]
    exact hg'
  · intro y hy
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    refine Formalism.UG.P.split_injective (J.map ρ) hd' _ _ (hsp ▸ (e y).2) hg ?_
    have hy' : bc (RingHom.fst K K) (e y : GL n (K × K)) = bc (RingHom.fst K K) g := by
      rw [hg', he, ← hbc]; exact hy
    exact congrArg Units.val hy'

/- English proof (translation)
Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`. Take `⟨y, hy, hy0⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Apply `hy` to reduce the goal to its premises. Establish `: sp.crd0.symm y = 0`.

Use `(sp.X 0).nondeg.2 _ fun x => ?_` and prove the remaining obligations. Rewrite using `[sp.hermitianForm_base_coordinates, LinearEquiv.apply_symm_apply]`. Unfold `hform`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Use `congrFun hy0 i` as an intermediate fact.

Simplify using `only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this`. Simplify using `only [mul_assoc, ← Finset.mul_sum, this, mul_zero]`. Simplify using `using this`.
-/
theorem gram_matrix_det_unit {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] (sp : Spaces R F E) : IsUnit sp.gram0.det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨y, hy, hy0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  apply hy
  have : sp.crd0.symm y = 0 := by
    refine (sp.X 0).nondeg.2 _ fun x => ?_
    rw [sp.hermitianForm_base_coordinates, LinearEquiv.apply_symm_apply]
    unfold hform
    refine Finset.sum_eq_zero fun i _ => ?_
    have := congrFun hy0 i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
    simp only [mul_assoc, ← Finset.mul_sum, this, mul_zero]
  simpa using this

end Unitary

section Primes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)}

/- English proof (translation)
The claim follows from `(GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.toIntV E v a).2`.
-/
theorem tmul_mem_intV (a : 𝓞 E) : ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F)) ∈ intV E v :=
  (GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.toIntV E v a).2

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_toIntV (a : 𝓞 E) :
    ((GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.toIntV E v a : intV E v) : E ⊗[F] v.adicCompletion F) =
      (a : E) ⊗ₜ[F] (1 : v.adicCompletion F) := rfl

/- English proof (translation)
Establish `: ((algebraMap (𝓞 F) (𝓞 E) b : 𝓞 E) : E) = (b : F) • (1 : E)`. Rewrite using `[Algebra.smul_def, mul_one]`. Both sides reduce to the same expression. Rewrite using `[this, TensorProduct.smul_tmul, Algebra.smul_def, mul_one]`.
-/
theorem tmul_algebraMap (b : 𝓞 F) :
    (((algebraMap (𝓞 F) (𝓞 E) b : 𝓞 E) : E) ⊗ₜ[F] (1 : v.adicCompletion F)) =
      (1 : E) ⊗ₜ[F] (algebraMap F (v.adicCompletion F) (b : F)) := by
  have : ((algebraMap (𝓞 F) (𝓞 E) b : 𝓞 E) : E) = (b : F) • (1 : E) := by
    rw [Algebra.smul_def, mul_one]; rfl
  rw [this, TensorProduct.smul_tmul, Algebra.smul_def, mul_one]

/- English proof (translation)
Rewrite using `[(GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives F v).2.1]`. Conclude with `v.valuation_lt_one_iff_mem _`.
-/
theorem valued_algebraMap_lt_one_iff (b : 𝓞 F) :
    Valued.v (algebraMap F (v.adicCompletion F) (b : F)) < 1 ↔ b ∈ v.asIdeal := by
  rw [(GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives F v).2.1]
  exact v.valuation_lt_one_iff_mem _

def primeE (p : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F)
    (hp : ∀ x ∈ intV E v, Valued.v (p x) ≤ 1)
    (h1 : ∀ a : v.adicCompletion F, p ((1 : E) ⊗ₜ[F] a) = a) : HeightOneSpectrum (𝓞 E) where
  asIdeal :=
    { carrier := {a | Valued.v (p ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))) < 1}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        show Valued.v (p (((a + b : 𝓞 E) : E) ⊗ₜ[F] (1 : v.adicCompletion F))) < 1
        rw [show ((a + b : 𝓞 E) : E) = (a : E) + (b : E) from rfl, TensorProduct.add_tmul, map_add]
        exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hb)
      smul_mem' := fun c a ha => by
        show Valued.v (p (((c * a : 𝓞 E) : E) ⊗ₜ[F] (1 : v.adicCompletion F))) < 1
        have : (((c * a : 𝓞 E) : E) ⊗ₜ[F] (1 : v.adicCompletion F)) =
            ((c : E) ⊗ₜ[F] (1 : v.adicCompletion F)) * ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F)) := by
          simp
        rw [this, map_mul, map_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hp _ (tmul_mem_intV c)) zero_le' ha }
  isPrime := by
    refine ⟨?_, fun {a b} hab => ?_⟩
    · rw [Ideal.ne_top_iff_one]
      show ¬ Valued.v (p (((1 : 𝓞 E) : E) ⊗ₜ[F] (1 : v.adicCompletion F))) < 1
      rw [show ((1 : 𝓞 E) : E) = 1 from rfl, h1]; simp
    · have hab' : Valued.v (p (((a * b : 𝓞 E) : E) ⊗ₜ[F] (1 : v.adicCompletion F))) < 1 := hab
      have : (((a * b : 𝓞 E) : E) ⊗ₜ[F] (1 : v.adicCompletion F)) =
          ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F)) * ((b : E) ⊗ₜ[F] (1 : v.adicCompletion F)) := by
        simp
      rw [this, map_mul, map_mul] at hab'
      by_contra hc
      rw [not_or] at hc
      have ha : 1 ≤ Valued.v (p ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))) := not_lt.1 hc.1
      have hb : 1 ≤ Valued.v (p ((b : E) ⊗ₜ[F] (1 : v.adicCompletion F))) := not_lt.1 hc.2
      exact absurd hab' (not_lt.2 (one_le_mul ha hb))
  ne_bot := by
    obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    refine Submodule.ne_bot_iff _ |>.2 ⟨algebraMap (𝓞 F) (𝓞 E) b, ?_, ?_⟩
    · show Valued.v (p (((algebraMap (𝓞 F) (𝓞 E) b : 𝓞 E) : E) ⊗ₜ[F] (1 : v.adicCompletion F))) < 1
      rw [tmul_algebraMap, h1, valued_algebraMap_lt_one_iff]; exact hb
    · simpa using hb0

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_primeE {p : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F} {hp h1} (a : 𝓞 E) :
    a ∈ (primeE p hp h1).asIdeal ↔
      Valued.v (p ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))) < 1 := Iff.rfl

/- English proof (translation)
Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `b hb`. Rewrite using `[Ideal.mem_comap, mem_primeE, tmul_algebraMap, h1, valued_algebraMap_lt_one_iff]`. Conclude with `hb`.
-/
theorem map_le_primeE {p : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F} {hp h1} :
    v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≤ (primeE p hp h1).asIdeal := by
  rw [Ideal.map_le_iff_le_comap]
  intro b hb
  rw [Ideal.mem_comap, mem_primeE, tmul_algebraMap, h1, valued_algebraMap_lt_one_iff]; exact hb

/- English proof (translation)
Use `haveI : Finite (𝓞 E ⧸ P.asIdeal) := P.asIdeal.finiteQuotientOfFreeOfNeBot P.ne_bot`. Establish `hle` using `Ideal.map_le_iff_le_comap.1 h`. Establish `heq : v.asIdeal = P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))` using `v.isMaximal.eq_of_le (Ideal.comap_ne_top _ P.isPrime.ne_top) hle`. Rewrite using `[Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]`. Conclude with `Nat.card_le_card_of_injective _ (Ideal.quotientMap_injective' (H := hle) heq.ge)`.
-/
theorem absNorm_le_of_map_le (P : HeightOneSpectrum (𝓞 E))
    (h : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≤ P.asIdeal) :
    Ideal.absNorm v.asIdeal ≤ Ideal.absNorm P.asIdeal := by
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := P.asIdeal.finiteQuotientOfFreeOfNeBot P.ne_bot
  have hle := Ideal.map_le_iff_le_comap.1 h
  have heq : v.asIdeal = P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) :=
    v.isMaximal.eq_of_le (Ideal.comap_ne_top _ P.isPrime.ne_top) hle
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_le_card_of_injective _ (Ideal.quotientMap_injective' (H := hle) heq.ge)

/- English proof (translation)
Establish `hco : P.asIdeal ⊔ Q.asIdeal = ⊤` using `P.isMaximal.coprime_of_ne Q.isMaximal (fun h => hne (HeightOneSpectrum.ext h))`. Establish `hle : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≤ P.asIdeal * Q.asIdeal`. Rewrite using `[Ideal.mul_eq_inf_of_coprime hco]`. Conclude with `le_inf hP hQ`. Take `⟨J, hJ⟩` from `Ideal.dvd_iff_le.2 hle`.

Establish `hn` using `congrArg Ideal.absNorm hJ`. Establish `hr : Module.finrank (𝓞 F) (𝓞 E) = 2`. Rewrite using `[← hdeg, IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E]`. Rewrite `hn` using `[Ideal.absNorm_algebraMap, hr, map_mul, map_mul]`. Establish `h1` using `absNorm_le_of_map_le P hP`.

Establish `h2` using `absNorm_le_of_map_le Q hQ`. Establish `h0 : 0 < Ideal.absNorm v.asIdeal` using `Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)`. Establish `hJ1 : Ideal.absNorm J = 1`. Establish `h3 : Ideal.absNorm v.asIdeal ^ 2 ≤ Ideal.absNorm P.asIdeal * Ideal.absNorm Q.asIdeal`. Rewrite using `[sq]`.

Conclude with `Nat.mul_le_mul h1 h2`. Establish `h4 : 0 < Ideal.absNorm v.asIdeal ^ 2` using `by positivity`. Generalize the expression as in `Ideal.absNorm P.asIdeal * Ideal.absNorm Q.asIdeal = m at *`. Generalize the expression as in `Ideal.absNorm v.asIdeal ^ 2 = a at *`. Generalize the expression as in `Ideal.absNorm J = j at *`.

Break down `j with _ | _ | j` into its components or cases. Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[hJ, Ideal.absNorm_eq_one_iff.1 hJ1, Ideal.mul_top]`.
-/
theorem map_eq_mul (hdeg : Module.finrank F E = 2) (P Q : HeightOneSpectrum (𝓞 E)) (hne : P ≠ Q)
    (hP : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≤ P.asIdeal)
    (hQ : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≤ Q.asIdeal) :
    v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = P.asIdeal * Q.asIdeal := by
  have hco : P.asIdeal ⊔ Q.asIdeal = ⊤ :=
    P.isMaximal.coprime_of_ne Q.isMaximal (fun h => hne (HeightOneSpectrum.ext h))
  have hle : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≤ P.asIdeal * Q.asIdeal := by
    rw [Ideal.mul_eq_inf_of_coprime hco]; exact le_inf hP hQ
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  have hn := congrArg Ideal.absNorm hJ
  have hr : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← hdeg, IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E]
  rw [Ideal.absNorm_algebraMap, hr, map_mul, map_mul] at hn
  have h1 := absNorm_le_of_map_le P hP
  have h2 := absNorm_le_of_map_le Q hQ
  have h0 : 0 < Ideal.absNorm v.asIdeal :=
    Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  have hJ1 : Ideal.absNorm J = 1 := by
    have h3 : Ideal.absNorm v.asIdeal ^ 2 ≤ Ideal.absNorm P.asIdeal * Ideal.absNorm Q.asIdeal := by
      rw [sq]; exact Nat.mul_le_mul h1 h2
    have h4 : 0 < Ideal.absNorm v.asIdeal ^ 2 := by positivity
    generalize Ideal.absNorm P.asIdeal * Ideal.absNorm Q.asIdeal = m at *
    generalize Ideal.absNorm v.asIdeal ^ 2 = a at *
    generalize Ideal.absNorm J = j at *
    rcases j with _ | _ | j
    · omega
    · rfl
    · nlinarith
  rw [hJ, Ideal.absNorm_eq_one_iff.1 hJ1, Ideal.mul_top]

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hs`. Set `P` to `primeE (GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.prP s) (fun x hx => ((h3 x).1 hx).1) (fun a => congrArg Prod.fst (h1 a))`. Set `Q` to `primeE (GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.prPbar s) (fun x hx => ((h3 x).1 hx).2) (fun a => congrArg Prod.snd (h1 a))`. Establish `hne : P ≠ Q`. Introduce `hPQ`.

Establish `key : ∀ x ∈ intV E v, Valued.v ((s x).1 - (s x).2) < 1`. Introduce `x hx`. Proceed by induction on `hx using Subring.closure_induction with`. Consider the case `mem x hx`. Break down `hx with ⟨⟨_, a, rfl⟩, rfl⟩ | ⟨a, rfl⟩` into its components or cases.

Take `⟨b, hb⟩` from `(GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives F v).2.2.1 (s ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))).1 ((h3 _).1 (tmul_mem_intV a)).1`. Establish `e : s (((a - algebraMap (𝓞 F) (𝓞 E) b : 𝓞 E) : E) ⊗ₜ[F] (1 : v.adicCompletion F)) = s ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F)) - (algebraMap F (v.adicCompletion F) (b : F), algebraMap F (v.adicCompletion F) (b : F))`. Rewrite using `[← h1, ← tmul_algebraMap, ← map_sub, ← TensorProduct.sub_tmul]`. Both sides reduce to the same expression. Establish `hP : a - algebraMap (𝓞 F) (𝓞 E) b ∈ P.asIdeal` using `by show Valued.v (s _).1 < 1`.

Rewrite using `[e]`. Conclude with `hb`. Rewrite `hP` using `[hPQ]`. Establish `hQ : Valued.v (s (((a - algebraMap (𝓞 F) (𝓞 E) b : 𝓞 E) : E) ⊗ₜ[F] (1 : v.adicCompletion F))).2 < 1` using `hP`. Rewrite `hQ` using `[e]`.

Use `show Valued.v ((s ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))).1 - (s ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))).2) < 1`. Rewrite using `[← sub_sub_sub_cancel_right _ _ (algebraMap F (v.adicCompletion F) (b : F))]`. Conclude with `lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hb hQ)`. Use `show Valued.v ((s ((1 : E) ⊗ₜ[F] (a : v.adicCompletion F))).1 - (s ((1 : E) ⊗ₜ[F] (a : v.adicCompletion F))).2) < 1`. Rewrite using `[h1]`.

Simplify using the standard rewrite rules. Consider the case `zero => simp`. Consider the case `one => simp`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add, Prod.fst_add, Prod.snd_add, add_sub_add_comm]`.

Conclude with `lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hy)`. Consider the case `neg x _ hx`. Rewrite using `[map_neg, Prod.fst_neg, Prod.snd_neg, neg_sub_neg, Valuation.map_sub_swap]`. Conclude with `hx`. Consider the case `mul x y hx' hy' hx hy`.

Establish `e : (s (x * y)).1 - (s (x * y)).2 = (s x).1 * ((s y).1 - (s y).2) + (s y).2 * ((s x).1 - (s x).2)`. Rewrite using `[map_mul, Prod.fst_mul, Prod.snd_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)` and prove the remaining obligations.

Rewrite using `[map_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_right ((h3 x).1 hx').1 zero_le' hy`. Rewrite using `[map_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_right ((h3 y).1 hy').2 zero_le' hx`. Use `key (s.symm (1, 0)) ((h3 _).2 (by simp))` as an intermediate fact.

Simplify using `at this`. Conclude with `⟨P, Q, hne, map_eq_mul hdeg P Q hne map_le_primeE map_le_primeE, h1, h2, h3, fun a => Iff.rfl, fun a => Iff.rfl⟩`.
-/
theorem exists_primes (hdeg : Module.finrank F E = 2) {σ : E →ₐ[F] E}
    {s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F}
    (hs : GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.IsSplitting σ v s) :
    ∃ P Pb, GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.IsSplitting σ P Pb s := by
  obtain ⟨h1, h2, h3⟩ := hs
  let P := primeE (GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.prP s) (fun x hx => ((h3 x).1 hx).1)
    (fun a => congrArg Prod.fst (h1 a))
  let Q := primeE (GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.prPbar s) (fun x hx => ((h3 x).1 hx).2)
    (fun a => congrArg Prod.snd (h1 a))
  have hne : P ≠ Q := by
    intro hPQ
    have key : ∀ x ∈ intV E v, Valued.v ((s x).1 - (s x).2) < 1 := by
      intro x hx
      induction hx using Subring.closure_induction with
      | mem x hx =>
        rcases hx with ⟨⟨_, a, rfl⟩, rfl⟩ | ⟨a, rfl⟩
        · obtain ⟨b, hb⟩ := (GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives F v).2.2.1
            (s ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))).1 ((h3 _).1 (tmul_mem_intV a)).1
          have e : s (((a - algebraMap (𝓞 F) (𝓞 E) b : 𝓞 E) : E) ⊗ₜ[F] (1 : v.adicCompletion F)) =
              s ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F)) -
                (algebraMap F (v.adicCompletion F) (b : F), algebraMap F (v.adicCompletion F) (b : F)) := by
            rw [← h1, ← tmul_algebraMap, ← map_sub, ← TensorProduct.sub_tmul]; rfl
          have hP : a - algebraMap (𝓞 F) (𝓞 E) b ∈ P.asIdeal := by
            show Valued.v (s _).1 < 1
            rw [e]; exact hb
          rw [hPQ] at hP
          have hQ : Valued.v (s (((a - algebraMap (𝓞 F) (𝓞 E) b : 𝓞 E) : E) ⊗ₜ[F]
            (1 : v.adicCompletion F))).2 < 1 := hP
          rw [e] at hQ
          show Valued.v ((s ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))).1 -
            (s ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))).2) < 1
          rw [← sub_sub_sub_cancel_right _ _ (algebraMap F (v.adicCompletion F) (b : F))]
          exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hb hQ)
        · show Valued.v ((s ((1 : E) ⊗ₜ[F] (a : v.adicCompletion F))).1 -
            (s ((1 : E) ⊗ₜ[F] (a : v.adicCompletion F))).2) < 1
          rw [h1]; simp
      | zero => simp
      | one => simp
      | add x y _ _ hx hy =>
        rw [map_add, Prod.fst_add, Prod.snd_add, add_sub_add_comm]
        exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hy)
      | neg x _ hx =>
        rw [map_neg, Prod.fst_neg, Prod.snd_neg, neg_sub_neg, Valuation.map_sub_swap]; exact hx
      | mul x y hx' hy' hx hy =>
        have e : (s (x * y)).1 - (s (x * y)).2 =
            (s x).1 * ((s y).1 - (s y).2) + (s y).2 * ((s x).1 - (s x).2) := by
          rw [map_mul, Prod.fst_mul, Prod.snd_mul]; ring
        rw [e]
        refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
        · rw [map_mul]
          exact mul_lt_one_of_nonneg_of_lt_one_right ((h3 x).1 hx').1 zero_le' hy
        · rw [map_mul]
          exact mul_lt_one_of_nonneg_of_lt_one_right ((h3 y).1 hy').2 zero_le' hx
    have := key (s.symm (1, 0)) ((h3 _).2 (by simp))
    simp at this
  exact ⟨P, Q, hne, map_eq_mul hdeg P Q hne map_le_primeE map_le_primeE, h1, h2, h3,
    fun a => Iff.rfl, fun a => Iff.rfl⟩

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Conclude with `Ideal.subset_span ((hP a).1 ha)`. Rewrite using `[GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.primeOf, Ideal.span_le]`.

Introduce `x hx`. Establish `hx' : Valued.v (p x) < 1` using `hx`. Take `⟨π, hπ⟩` from `v.intValuation_exists_uniformizer`. Use `set π' := algebraMap F (v.adicCompletion F) (π : F) with hπ'`. Establish `hv : Valued.v π' = WithZero.exp (-1)`.

Rewrite using `[hπ', (GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives F v).2.1, ← hπ]`. Conclude with `v.valuation_of_algebraMap π`. Establish `hπ0 : π' ≠ 0`. Introduce `h`. Rewrite `hv` using `[h, map_zero]`.

Conclude with `WithZero.exp_ne_zero hv.symm`. Establish `hπP : algebraMap (𝓞 F) (𝓞 E) π ∈ P.asIdeal`. Rewrite using `[hP, tmul_algebraMap, h1, ← hπ', hv, ← WithZero.exp_zero, WithZero.exp_lt_exp]`. Use linear arithmetic over natural numbers and integers. Establish `hnle : ¬ P.asIdeal ≤ Q.asIdeal` using `fun h => hne (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h))`.

Take `⟨a, haP, haQ⟩` from `Set.not_subset.1 hnle`. Establish `hu : Valued.v (q ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))) = 1` using `le_antisymm (hq _ (tmul_mem_intV a)) (not_lt.1 fun h => haQ ((hQ a).2 h))`. Establish `hu0 : q ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F)) ≠ 0`. Introduce `h`. Rewrite `hu` using `[h, map_zero]`.

Conclude with `zero_ne_one hu`. Take `⟨y, hy, hy1, hy2⟩` from `hsur (p x / π') 0 (by`. Rewrite using `[map_div₀, hv, div_le_one₀ (by simp)]`. Conclude with `WithZero.lt_mul_exp_iff_le (by simp) |>.1 (by simpa using hx')) (by simp)`. Take `⟨z, hz, hz1, hz2⟩` from `hsur 0 (q x / q ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))) (by simp) (by`.

Rewrite using `[map_div₀, hu, div_one]`. Conclude with `hq _ x.2)`. Establish `: x = ⟨y, hy⟩ * GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.toIntV E v (algebraMap (𝓞 F) (𝓞 E) π) + ⟨z, hz⟩ * GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.toIntV E v a`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises.

Simplify using `only [Subring.coe_add, Subring.coe_mul, map_add, map_mul, coe_toIntV, hy1, hz1, tmul_algebraMap, h1, ← hπ', zero_mul, add_zero, div_mul_cancel₀ _ hπ0]`. Simplify using `only [Subring.coe_add, Subring.coe_mul, map_add, map_mul, coe_toIntV, hy2, hz2, zero_mul, zero_add, div_mul_cancel₀ _ hu0]`. Rewrite using `[this]`. Conclude with `add_mem (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hπP)) (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ haP))`.
-/
theorem map_eq_primeOf (p : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F)
    (hp : ∀ x ∈ intV E v, Valued.v (p x) ≤ 1)
    (h1 : ∀ a : v.adicCompletion F, p ((1 : E) ⊗ₜ[F] a) = a)
    (q : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F)
    (hq : ∀ x ∈ intV E v, Valued.v (q x) ≤ 1)
    (hsur : ∀ a b, Valued.v a ≤ 1 → Valued.v b ≤ 1 → ∃ x ∈ intV E v, p x = a ∧ q x = b)
    (hinj : ∀ x y, p x = p y → q x = q y → x = y)
    (P Q : HeightOneSpectrum (𝓞 E)) (hne : P ≠ Q)
    (hP : ∀ a : 𝓞 E, a ∈ P.asIdeal ↔ Valued.v (p ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))) < 1)
    (hQ : ∀ a : 𝓞 E, a ∈ Q.asIdeal ↔ Valued.v (q ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))) < 1) :
    P.asIdeal.map (GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.toIntV E v) = GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.primeOf p := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact Ideal.subset_span ((hP a).1 ha)
  · rw [GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.primeOf, Ideal.span_le]
    intro x hx
    have hx' : Valued.v (p x) < 1 := hx
    obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
    set π' := algebraMap F (v.adicCompletion F) (π : F) with hπ'
    have hv : Valued.v π' = WithZero.exp (-1) := by
      rw [hπ', (GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives F v).2.1, ← hπ]
      exact v.valuation_of_algebraMap π
    have hπ0 : π' ≠ 0 := by
      intro h; rw [h, map_zero] at hv; exact WithZero.exp_ne_zero hv.symm
    have hπP : algebraMap (𝓞 F) (𝓞 E) π ∈ P.asIdeal := by
      rw [hP, tmul_algebraMap, h1, ← hπ', hv, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have hnle : ¬ P.asIdeal ≤ Q.asIdeal := fun h =>
      hne (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h))
    obtain ⟨a, haP, haQ⟩ := Set.not_subset.1 hnle
    have hu : Valued.v (q ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))) = 1 :=
      le_antisymm (hq _ (tmul_mem_intV a)) (not_lt.1 fun h => haQ ((hQ a).2 h))
    have hu0 : q ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F)) ≠ 0 := by
      intro h; rw [h, map_zero] at hu; exact zero_ne_one hu
    obtain ⟨y, hy, hy1, hy2⟩ := hsur (p x / π') 0 (by
      rw [map_div₀, hv, div_le_one₀ (by simp)]
      exact WithZero.lt_mul_exp_iff_le (by simp) |>.1 (by simpa using hx')) (by simp)
    obtain ⟨z, hz, hz1, hz2⟩ := hsur 0 (q x / q ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))) (by simp) (by
      rw [map_div₀, hu, div_one]; exact hq _ x.2)
    have : x = ⟨y, hy⟩ * GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.toIntV E v (algebraMap (𝓞 F) (𝓞 E) π) +
        ⟨z, hz⟩ * GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.toIntV E v a := by
      apply Subtype.ext
      apply hinj
      · simp only [Subring.coe_add, Subring.coe_mul, map_add, map_mul, coe_toIntV, hy1, hz1,
          tmul_algebraMap, h1, ← hπ', zero_mul, add_zero, div_mul_cancel₀ _ hπ0]
      · simp only [Subring.coe_add, Subring.coe_mul, map_add, map_mul, coe_toIntV, hy2, hz2,
          zero_mul, zero_add, div_mul_cancel₀ _ hu0]
    rw [this]
    exact add_mem (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hπP))
      (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ haP))

/- English proof (translation)
Take `⟨hne, -, h1, -, h3, hP, hQ⟩` from `hs`. Establish `e1 : ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.prP s x = (s x).1` using `fun _ => rfl`. Establish `e2 : ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.prPbar s x = (s x).2` using `fun _ => rfl`. Establish `hp : ∀ x ∈ intV E v, Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.prP s x) ≤ 1` using `fun x hx => ((h3 x).1 hx).1`. Establish `hq : ∀ x ∈ intV E v, Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.prPbar s x) ≤ 1` using `fun x hx => ((h3 x).1 hx).2`.

Establish `hm : ∀ a b : v.adicCompletion F, Valued.v a ≤ 1 → Valued.v b ≤ 1 → s.symm (a, b) ∈ intV E v` using `fun a b ha hb => (h3 _).2 (by rw [s.apply_symm_apply]; exact ⟨ha, hb⟩)`. Prove the components needed by the constructor for the conclusion. Use `map_eq_primeOf _ hp (fun a => by rw [e1, h1]) (GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.prPbar s) hq (fun a b ha hb => ⟨s.symm (a, b), hm a b ha hb, ?_, ?_⟩) (fun x y h h' => s.injective (Prod.ext h h')) P Pb hne hP hQ` and prove the remaining obligations. Rewrite using `[e1, s.apply_symm_apply]`. Rewrite using `[e2, s.apply_symm_apply]`.

Use `map_eq_primeOf _ hq (fun a => by rw [e2, h1]) (GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.prP s) hp (fun a b ha hb => ⟨s.symm (b, a), hm b a hb ha, ?_, ?_⟩) (fun x y h h' => s.injective (Prod.ext h' h)) Pb P hne.symm hQ hP` and prove the remaining obligations. Rewrite using `[e2, s.apply_symm_apply]`. Rewrite using `[e1, s.apply_symm_apply]`.
-/
theorem map_primes {σ : E →ₐ[F] E} {P Pb : HeightOneSpectrum (𝓞 E)}
    {s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F}
    (hs : GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.IsSplitting σ P Pb s) :
    P.asIdeal.map (GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.toIntV E v) = GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.primeOf (GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.prP s) ∧
    Pb.asIdeal.map (GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.toIntV E v) =
      GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.primeOf (GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.prPbar s) := by
  obtain ⟨hne, -, h1, -, h3, hP, hQ⟩ := hs
  have e1 : ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.prP s x = (s x).1 := fun _ => rfl
  have e2 : ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.prPbar s x = (s x).2 := fun _ => rfl
  have hp : ∀ x ∈ intV E v, Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.prP s x) ≤ 1 := fun x hx => ((h3 x).1 hx).1
  have hq : ∀ x ∈ intV E v, Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.prPbar s x) ≤ 1 := fun x hx => ((h3 x).1 hx).2
  have hm : ∀ a b : v.adicCompletion F, Valued.v a ≤ 1 → Valued.v b ≤ 1 → s.symm (a, b) ∈ intV E v :=
    fun a b ha hb => (h3 _).2 (by rw [s.apply_symm_apply]; exact ⟨ha, hb⟩)
  constructor
  · refine map_eq_primeOf _ hp (fun a => by rw [e1, h1]) (GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.prPbar s) hq
      (fun a b ha hb => ⟨s.symm (a, b), hm a b ha hb, ?_, ?_⟩)
      (fun x y h h' => s.injective (Prod.ext h h')) P Pb hne hP hQ
    · rw [e1, s.apply_symm_apply]
    · rw [e2, s.apply_symm_apply]
  · refine map_eq_primeOf _ hq (fun a => by rw [e2, h1]) (GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.prP s) hp
      (fun a b ha hb => ⟨s.symm (b, a), hm b a hb ha, ?_, ?_⟩)
      (fun x y h h' => s.injective (Prod.ext h' h)) Pb P hne.symm hQ hP
    · rw [e2, s.apply_symm_apply]
    · rw [e1, s.apply_symm_apply]

end Primes

section Frame

variable {K : Type} [Field K] {O : ValuationSubring K} {n : Type} [Fintype n] [DecidableEq n]

def IsFrame (Λ : Submodule O (n → K)) (b : GL n K) : Prop :=
  ∀ y : n → K, (b : Matrix n n K) *ᵥ y ∈ Λ ↔ ∀ i, y i ∈ O

/- English proof (translation)
Rewrite using `[Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`.
-/
theorem mul_inv_mulVec (b : GL n K) (x : n → K) :
    (b : Matrix n n K) *ᵥ (((b⁻¹ : GL n K) : Matrix n n K) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

/- English proof (translation)
Rewrite using `[Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`.
-/
theorem inv_mul_mulVec (b : GL n K) (x : n → K) :
    ((b⁻¹ : GL n K) : Matrix n n K) *ᵥ ((b : Matrix n n K) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Use `(h (((b⁻¹ : GL n K) : Matrix n n K) *ᵥ x)).1 (by rw [mul_inv_mulVec]; exact hx)` as an intermediate fact. Conclude with `⟨fun i => ⟨_, this i⟩, mul_inv_mulVec b x⟩`. Introduce and unpack `⟨y, rfl⟩`. Conclude with `(h _).2 fun i => (y i).2`. Introduce `h y`.

Rewrite using `[← SetLike.mem_coe, h]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz⟩ i`. Use `congrArg (fun w => ((b⁻¹ : GL n K) : Matrix n n K) *ᵥ w) hz` as an intermediate fact. Simplify using `only [inv_mul_mulVec] at this`.

Rewrite using `[← this]`. Conclude with `(z i).2`. Introduce `hy`. Conclude with `⟨fun i => ⟨y i, hy i⟩, rfl⟩`.
-/
theorem isFrame_iff (Λ : Submodule O (n → K)) (b : GL n K) :
    IsFrame Λ b ↔ (Λ : Set (n → K)) =
      Set.range (fun y : n → O => (b : Matrix n n K) *ᵥ fun i => (y i : K)) := by
  constructor
  · intro h
    ext x
    constructor
    · intro hx
      have := (h (((b⁻¹ : GL n K) : Matrix n n K) *ᵥ x)).1 (by rw [mul_inv_mulVec]; exact hx)
      exact ⟨fun i => ⟨_, this i⟩, mul_inv_mulVec b x⟩
    · rintro ⟨y, rfl⟩
      exact (h _).2 fun i => (y i).2
  · intro h y
    rw [← SetLike.mem_coe, h]
    constructor
    · rintro ⟨z, hz⟩ i
      have := congrArg (fun w => ((b⁻¹ : GL n K) : Matrix n n K) *ᵥ w) hz
      simp only [inv_mul_mulVec] at this
      rw [← this]; exact (z i).2
    · intro hy
      exact ⟨fun i => ⟨y i, hy i⟩, rfl⟩

/- English proof (translation)
Establish `: (x : n → K) ∈ (Λ : Set (n → K))` using `x.2`. Rewrite `this` using `[(isFrame_iff Λ b).1 h]`. Take `⟨z, hz⟩` from `this`. Conclude with `⟨z, hz.symm⟩`.
-/
theorem IsFrame.exists_coord {Λ : Submodule O (n → K)} {b : GL n K} (h : IsFrame Λ b) (x : Λ) :
    ∃ z : n → O, (x : n → K) = (b : Matrix n n K) *ᵥ fun i => (z i : K) := by
  have : (x : n → K) ∈ (Λ : Set (n → K)) := x.2
  rw [(isFrame_iff Λ b).1 h] at this
  obtain ⟨z, hz⟩ := this
  exact ⟨z, hz.symm⟩

/- English proof (translation)
Rewrite using `[← Formalism.UG.P.stabilizer_standard_lattice K O n Subtype.val_injective]`. Establish `hs : ∀ y : n → K, y ∈ stdLat (n` using `n) (A := K) O ↔ (b : Matrix n n K) *ᵥ y ∈ Λ := by`. Introduce `y`. Rewrite using `[Formalism.UG.P.mem_stdLat_iff', h y]`. Conclude with `forall_congr' fun i => ⟨fun ⟨z, hz⟩ => hz ▸ z.2, fun hy => ⟨⟨y i, hy⟩, rfl⟩⟩`.

Establish `e : ∀ y : n → K, (b : Matrix n n K) *ᵥ (((b⁻¹ * g * b : GL n K) : Matrix n n K) *ᵥ y) = (g : Matrix n n K) *ᵥ ((b : Matrix n n K) *ᵥ y)`. Introduce `y`. Rewrite using `[Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mul_inv_mulVec]`. Prove the components needed by the constructor for the conclusion. Introduce `hg y`.

Rewrite using `[hs, hs, e]`. Conclude with `hg _`. Introduce `hg x`. Use `hg (((b⁻¹ : GL n K) : Matrix n n K) *ᵥ x)` as an intermediate fact. Rewrite `this` using `[hs, hs, e, mul_inv_mulVec]`. Then use the resulting hypothesis.
-/
theorem IsFrame.mem_stabGL_iff {Λ : Submodule O (n → K)} {b : GL n K} (h : IsFrame Λ b)
    (g : GL n K) : g ∈ stabGL Λ ↔ b⁻¹ * g * b ∈ (bc (n := n) (algebraMap O K)).range := by
  rw [← Formalism.UG.P.stabilizer_standard_lattice K O n Subtype.val_injective]
  have hs : ∀ y : n → K, y ∈ stdLat (n := n) (A := K) O ↔ (b : Matrix n n K) *ᵥ y ∈ Λ := by
    intro y
    rw [Formalism.UG.P.mem_stdLat_iff', h y]
    exact forall_congr' fun i => ⟨fun ⟨z, hz⟩ => hz ▸ z.2, fun hy => ⟨⟨y i, hy⟩, rfl⟩⟩
  have e : ∀ y : n → K, (b : Matrix n n K) *ᵥ (((b⁻¹ * g * b : GL n K) : Matrix n n K) *ᵥ y) =
      (g : Matrix n n K) *ᵥ ((b : Matrix n n K) *ᵥ y) := by
    intro y
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mul_inv_mulVec]
  constructor
  · intro hg y
    rw [hs, hs, e]; exact hg _
  · intro hg x
    have := hg (((b⁻¹ : GL n K) : Matrix n n K) *ᵥ x)
    rwa [hs, hs, e, mul_inv_mulVec] at this

def rowEval (φ : n → O ⧸ IsLocalRing.maximalIdeal O) (z : n → O) : O ⧸ IsLocalRing.maximalIdeal O :=
  ∑ i, φ i * Ideal.Quotient.mk _ (z i)

/- English proof (translation)
Rewrite using `[rowEval, Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[hj]`. Simplify using the standard rewrite rules.
-/
theorem rowEval_single (φ : n → O ⧸ IsLocalRing.maximalIdeal O) (i : n) (a : O) :
    rowEval φ (Pi.single i a) = φ i * Ideal.Quotient.mk _ a := by
  rw [rowEval, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

def IsRow {Λ : Submodule O (n → K)} (b : GL n K) (f : Λ →ₗ[O] IsLocalRing.ResidueField O)
    (φ : n → O ⧸ IsLocalRing.maximalIdeal O) : Prop :=
  ∀ (y : Λ) (z : n → O), (y : n → K) = (b : Matrix n n K) *ᵥ (fun i => (z i : K)) →
    f y = rowEval φ z

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem residue_smul (a : O) (m : O ⧸ IsLocalRing.maximalIdeal O) :
    (a • (show IsLocalRing.ResidueField O from m) : IsLocalRing.ResidueField O) =
      (show IsLocalRing.ResidueField O from Ideal.Quotient.mk _ a * m) := rfl

/- English proof (translation)
Establish `hc : ∀ (x : Λ) i, (((b⁻¹ : GL n K) : Matrix n n K) *ᵥ (x : n → K)) i ∈ O` using `fun x => (h _).1 (by rw [mul_inv_mulVec]; exact x.2)`. Set `c : Λ → n → O` to `fun x i => ⟨_, hc x i⟩`. Establish `cadd : ∀ x y i, c (x + y) i = c x i + c y i` using `fun x y i => by`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[c, Matrix.mulVec_add]`.

Establish `csmul : ∀ (a : O) x i, c (a • x) i = a * c x i` using `fun a x i => by`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `: ((a • x : Λ) : n → K) = (a : K) • (x : n → K)` using `rfl`. Simplify using `[c, this, Matrix.mulVec_smul]`. Set `f0 : Λ → O ⧸ IsLocalRing.maximalIdeal O` to `fun x => ∑ i, φ i * Ideal.Quotient.mk _ (c x i)`.

Use `⟨⟨⟨f0, fun x y => ?_⟩, fun a x => ?_⟩, fun y z hy => ?_⟩` and prove the remaining obligations. Use `show f0 (x + y) = f0 x + f0 y`. Simplify using `only [f0, cadd, map_add, mul_add, Finset.sum_add_distrib]`. Use `show f0 (a • x) = Ideal.Quotient.mk _ a * f0 x`. Simplify using `only [f0, csmul, map_mul, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Use `show f0 y = rowEval φ z`. Establish `: c y = z`. Use function extensionality and compare the values at `i`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show (((b⁻¹ : GL n K) : Matrix n n K) *ᵥ (y : n → K)) i = z i`. Rewrite using `[hy, inv_mul_mulVec]`. Simplify using `only [f0, this, rowEval]`.
-/
theorem IsFrame.exists_fun {Λ : Submodule O (n → K)} {b : GL n K} (h : IsFrame Λ b)
    (φ : n → O ⧸ IsLocalRing.maximalIdeal O) :
    ∃ f : Λ →ₗ[O] IsLocalRing.ResidueField O, IsRow b f φ := by
  have hc : ∀ (x : Λ) i, (((b⁻¹ : GL n K) : Matrix n n K) *ᵥ (x : n → K)) i ∈ O := fun x =>
    (h _).1 (by rw [mul_inv_mulVec]; exact x.2)
  let c : Λ → n → O := fun x i => ⟨_, hc x i⟩
  have cadd : ∀ x y i, c (x + y) i = c x i + c y i := fun x y i => by
    apply Subtype.ext
    simp [c, Matrix.mulVec_add]
  have csmul : ∀ (a : O) x i, c (a • x) i = a * c x i := fun a x i => by
    apply Subtype.ext
    have : ((a • x : Λ) : n → K) = (a : K) • (x : n → K) := rfl
    simp [c, this, Matrix.mulVec_smul]
  let f0 : Λ → O ⧸ IsLocalRing.maximalIdeal O := fun x => ∑ i, φ i * Ideal.Quotient.mk _ (c x i)
  refine ⟨⟨⟨f0, fun x y => ?_⟩, fun a x => ?_⟩, fun y z hy => ?_⟩
  · show f0 (x + y) = f0 x + f0 y
    simp only [f0, cadd, map_add, mul_add, Finset.sum_add_distrib]
  · show f0 (a • x) = Ideal.Quotient.mk _ a * f0 x
    simp only [f0, csmul, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · show f0 y = rowEval φ z
    have : c y = z := by
      funext i; apply Subtype.ext
      show (((b⁻¹ : GL n K) : Matrix n n K) *ᵥ (y : n → K)) i = z i
      rw [hy, inv_mul_mulVec]
    simp only [f0, this, rowEval]

/- English proof (translation)
Establish `hm : ∀ i, (b : Matrix n n K) *ᵥ (Pi.single i 1 : n → K) ∈ Λ` using `fun i => (h _).2 fun j => by`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hj]`.

Use `⟨fun i => f ⟨_, hm i⟩, fun y z hy => ?_⟩` and prove the remaining obligations. Establish `: y = ∑ i, z i • (⟨_, hm i⟩ : Λ)`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hy, Submodule.coe_sum]`. Establish `: ∀ i, ((z i • (⟨_, hm i⟩ : Λ) : Λ) : n → K) = (b : Matrix n n K) *ᵥ ((z i : K) • (Pi.single i 1 : n → K))` using `fun i => by`.

Rewrite using `[Matrix.mulVec_smul]`. Both sides reduce to the same expression. Simplify using `only [this]`. Rewrite using `[← Matrix.mulVec_sum]`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[this, map_sum]`. Use `Finset.sum_congr (M := IsLocalRing.ResidueField O) rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`.

Conclude with `(residue_smul _ _).trans (mul_comm _ _)`.
-/
theorem IsFrame.exists_row {Λ : Submodule O (n → K)} {b : GL n K} (h : IsFrame Λ b)
    (f : Λ →ₗ[O] IsLocalRing.ResidueField O) :
    ∃ φ : n → O ⧸ IsLocalRing.maximalIdeal O, IsRow b f φ := by
  have hm : ∀ i, (b : Matrix n n K) *ᵥ (Pi.single i 1 : n → K) ∈ Λ := fun i => (h _).2 fun j => by
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  refine ⟨fun i => f ⟨_, hm i⟩, fun y z hy => ?_⟩
  have : y = ∑ i, z i • (⟨_, hm i⟩ : Λ) := by
    apply Subtype.ext
    rw [hy, Submodule.coe_sum]
    have : ∀ i, ((z i • (⟨_, hm i⟩ : Λ) : Λ) : n → K) =
        (b : Matrix n n K) *ᵥ ((z i : K) • (Pi.single i 1 : n → K)) := fun i => by
      rw [Matrix.mulVec_smul]; rfl
    simp only [this]
    rw [← Matrix.mulVec_sum]
    congr 1
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [this, map_sum]
  refine Finset.sum_congr (M := IsLocalRing.ResidueField O) rfl fun i _ => ?_
  rw [map_smul]
  exact (residue_smul _ _).trans (mul_comm _ _)

/- English proof (translation)
Use `not_congr ⟨fun h0 => ?_, fun h0 => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Establish `hy` using `hf ⟨_, (h _).2 fun j => ((Pi.single i 1 : n → O) j).2⟩ (Pi.single i 1) rfl`. Establish `h2 : rowEval φ (Pi.single i 1) = φ i` using `by rw [rowEval_single, map_one, mul_one]`. Rewrite `hy` using `[h0, h2]`.

Conclude with `hy.symm`. Use extensionality with `y`. Take `⟨z, hz⟩` from `h.exists_coord y`. Establish `h2 : rowEval (0 : n → O ⧸ IsLocalRing.maximalIdeal O) z = 0` using `by simp [rowEval]`. Rewrite using `[hf y z hz, h0, h2]`.

Both sides reduce to the same expression.
-/
theorem IsRow.ne_zero_iff {Λ : Submodule O (n → K)} {b : GL n K} (h : IsFrame Λ b)
    {f : Λ →ₗ[O] IsLocalRing.ResidueField O} {φ : n → O ⧸ IsLocalRing.maximalIdeal O}
    (hf : IsRow b f φ) : f ≠ 0 ↔ φ ≠ 0 := by
  refine not_congr ⟨fun h0 => ?_, fun h0 => ?_⟩
  · funext i
    have hy := hf ⟨_, (h _).2 fun j => ((Pi.single i 1 : n → O) j).2⟩ (Pi.single i 1) rfl
    have h2 : rowEval φ (Pi.single i 1) = φ i := by rw [rowEval_single, map_one, mul_one]
    rw [h0, h2] at hy
    exact hy.symm
  · ext y
    obtain ⟨z, hz⟩ := h.exists_coord y
    have h2 : rowEval (0 : n → O ⧸ IsLocalRing.maximalIdeal O) z = 0 := by simp [rowEval]
    rw [hf y z hz, h0, h2]
    rfl

/- English proof (translation)
Take `⟨y, hy⟩` from `DFunLike.ne_iff.1 hf`. Introduce `m`. Take `⟨a, ha⟩` from `IsLocalRing.residue_surjective (m / f y)`. Use `⟨a • y, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq, ha]`.

Conclude with `div_mul_cancel₀ _ hy`.
-/
theorem surjective_of_ne_zero {Λ : Submodule O (n → K)}
    {f : Λ →ₗ[O] IsLocalRing.ResidueField O} (hf : f ≠ 0) : Function.Surjective f := by
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.1 hf
  intro m
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (m / f y)
  refine ⟨a • y, ?_⟩
  rw [map_smul, Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq, ha]
  exact div_mul_cancel₀ _ hy

/- English proof (translation)
Establish `key : ∀ (u : GL n O), bc (algebraMap O K) u = b⁻¹ * g * b → ∀ z : n → O, (g : Matrix n n K) *ᵥ ((b : Matrix n n K) *ᵥ fun i => (z i : K)) = (b : Matrix n n K) *ᵥ fun i => (((u : Matrix n n O) *ᵥ z) i : K)`. Introduce `u hu z`. Establish `h1 : (fun i => (((u : Matrix n n O) *ᵥ z) i : K)) = ((bc (algebraMap O K) u : GL n K) : Matrix n n K) *ᵥ fun i => (z i : K)`. Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec (algebraMap O K) _ _ _`.

Rewrite using `[h1, hu, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mul_inv_mulVec]`. Establish `sum : ∀ (u : GL n O) (z : n → O), rowEval φ ((u : Matrix n n O) *ᵥ z) = rowEval (φ ᵥ* ((redGL (IsLocalRing.maximalIdeal O) u : GL n _) : Matrix n n _)) z`. Introduce `u z`. Establish `h1 : ∀ i, Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) (((u : Matrix n n O) *ᵥ z) i) = (((redGL (IsLocalRing.maximalIdeal O) u : GL n _) : Matrix n n _) *ᵥ fun j => Ideal.Quotient.mk _ (z j)) i` using `fun i => RingHom.map_mulVec _ _ _ _`. Simplify using `only [rowEval, h1]`.

Conclude with `Matrix.dotProduct_mulVec φ _ _`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hg, hg'⟩`. Take `⟨u, hu⟩` from `(h.mem_stabGL_iff g).1 hg`. Use `⟨u, ?_, hu⟩` and prove the remaining obligations.

Use `show φ ᵥ* ((redGL (IsLocalRing.maximalIdeal O) u : GL n _) : Matrix n n _) = φ`. Use function extensionality and compare the values at `j`. Establish `h1` using `hg' ⟨_, (h _).2 fun i => ((Pi.single j 1 : n → O) i).2⟩`. Rewrite `h1` using `[hf _ _ (key u hu _), hf _ _ rfl, sum]`. Establish `h2 : ∀ ψ : n → O ⧸ IsLocalRing.maximalIdeal O, rowEval ψ (Pi.single j 1) = ψ j` using `fun ψ => by rw [rowEval_single, map_one, mul_one]`.

Conclude with `(h2 _).symm.trans (h1.trans (h2 _))`. Introduce and unpack `⟨u, hu, hu'⟩`. Establish `hu2 : φ ᵥ* ((redGL (IsLocalRing.maximalIdeal O) u : GL n _) : Matrix n n _) = φ` using `hu`. Use `⟨(h.mem_stabGL_iff g).2 ⟨u, hu'⟩, fun x => ?_⟩` and prove the remaining obligations. Take `⟨z, hz⟩` from `h.exists_coord x`.

Rewrite using `[hf x z hz, hf _ ((u : Matrix n n O) *ᵥ z) (by rw [← key u hu', ← hz]), sum, hu2]`.
-/
theorem IsRow.mem_stabFun_iff {Λ : Submodule O (n → K)} {b : GL n K} (h : IsFrame Λ b)
    {f : Λ →ₗ[O] IsLocalRing.ResidueField O} {φ : n → O ⧸ IsLocalRing.maximalIdeal O}
    (hf : IsRow b f φ) (g : GL n K) :
    g ∈ stabFun Λ f ↔ b⁻¹ * g * b ∈ congPre (algebraMap O K) (IsLocalRing.maximalIdeal O)
      (GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.stabRow φ) := by
  have key : ∀ (u : GL n O), bc (algebraMap O K) u = b⁻¹ * g * b → ∀ z : n → O,
      (g : Matrix n n K) *ᵥ ((b : Matrix n n K) *ᵥ fun i => (z i : K)) =
        (b : Matrix n n K) *ᵥ fun i => (((u : Matrix n n O) *ᵥ z) i : K) := by
    intro u hu z
    have h1 : (fun i => (((u : Matrix n n O) *ᵥ z) i : K)) =
        ((bc (algebraMap O K) u : GL n K) : Matrix n n K) *ᵥ fun i => (z i : K) := by
      funext i
      exact RingHom.map_mulVec (algebraMap O K) _ _ _
    rw [h1, hu, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      mul_inv_mulVec]
  have sum : ∀ (u : GL n O) (z : n → O),
      rowEval φ ((u : Matrix n n O) *ᵥ z) =
        rowEval (φ ᵥ* ((redGL (IsLocalRing.maximalIdeal O) u : GL n _) : Matrix n n _)) z := by
    intro u z
    have h1 : ∀ i, Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) (((u : Matrix n n O) *ᵥ z) i) =
        (((redGL (IsLocalRing.maximalIdeal O) u : GL n _) : Matrix n n _) *ᵥ
          fun j => Ideal.Quotient.mk _ (z j)) i := fun i => RingHom.map_mulVec _ _ _ _
    simp only [rowEval, h1]
    exact Matrix.dotProduct_mulVec φ _ _
  constructor
  · rintro ⟨hg, hg'⟩
    obtain ⟨u, hu⟩ := (h.mem_stabGL_iff g).1 hg
    refine ⟨u, ?_, hu⟩
    show φ ᵥ* ((redGL (IsLocalRing.maximalIdeal O) u : GL n _) : Matrix n n _) = φ
    funext j
    have h1 := hg' ⟨_, (h _).2 fun i => ((Pi.single j 1 : n → O) i).2⟩
    rw [hf _ _ (key u hu _), hf _ _ rfl, sum] at h1
    have h2 : ∀ ψ : n → O ⧸ IsLocalRing.maximalIdeal O, rowEval ψ (Pi.single j 1) = ψ j :=
      fun ψ => by rw [rowEval_single, map_one, mul_one]
    exact (h2 _).symm.trans (h1.trans (h2 _))
  · rintro ⟨u, hu, hu'⟩
    have hu2 : φ ᵥ* ((redGL (IsLocalRing.maximalIdeal O) u : GL n _) : Matrix n n _) = φ := hu
    refine ⟨(h.mem_stabGL_iff g).2 ⟨u, hu'⟩, fun x => ?_⟩
    obtain ⟨z, hz⟩ := h.exists_coord x
    rw [hf x z hz, hf _ ((u : Matrix n n O) *ᵥ z) (by rw [← key u hu', ← hz]), sum, hu2]

end Frame

section Part

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {n : Type}

/- English proof (translation)
Use `⟨fun h => ?_, fun h => Submodule.subset_span h⟩` and prove the remaining obligations. Proceed by induction on `h using Submodule.span_induction with`. Consider the case `mem x hx => exact hx`. Consider the case `zero => exact ⟨0, Λ.zero_mem, by funext i; simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨a, ha, rfl⟩` from `hx`. Take `⟨b, hb, rfl⟩` from `hy`. Conclude with `⟨a + b, Λ.add_mem ha hb, by funext i; simp⟩`. Consider the case `smul c x _ hx`. Take `⟨a, ha, rfl⟩` from `hx`.

Take `⟨d, hd, hdc⟩` from `hsur c c.2`. Use `⟨(⟨d, hd⟩ : intV E v) • a, Λ.smul_mem _ ha, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Use `show p (d * a i) = (c : v.adicCompletion F) * p (a i)`. Rewrite using `[map_mul, hdc]`.
-/
theorem mem_partOf (p : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F)
    (hsur : ∀ a ∈ v.adicCompletionIntegers F, ∃ x ∈ intV E v, p x = a)
    (Λ : Submodule (intV E v) (n → E ⊗[F] v.adicCompletion F)) (y : n → v.adicCompletion F) :
    y ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.partOf p Λ ↔ ∃ x ∈ Λ, (fun i => p (x i)) = y := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, Λ.zero_mem, by funext i; simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, Λ.add_mem ha hb, by funext i; simp⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨d, hd, hdc⟩ := hsur c c.2
    refine ⟨(⟨d, hd⟩ : intV E v) • a, Λ.smul_mem _ ha, ?_⟩
    funext i
    show p (d * a i) = (c : v.adicCompletion F) * p (a i)
    rw [map_mul, hdc]

variable {σ : E →ₐ[F] E}
  {s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F}

/- English proof (translation)
Introduce `a ha`. Use `⟨s.symm (a, a), (hs.2.2 _).2 (by rw [s.apply_symm_apply]; exact ⟨ha, ha⟩), ?_⟩` and prove the remaining obligations. Use `show (s (s.symm (a, a))).1 = a`. Rewrite using `[s.apply_symm_apply]`.
-/
theorem sur_prP (hs : GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.IsSplitting σ v s) :
    ∀ a ∈ v.adicCompletionIntegers F, ∃ x ∈ intV E v, GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.prP s x = a := by
  intro a ha
  refine ⟨s.symm (a, a), (hs.2.2 _).2 (by rw [s.apply_symm_apply]; exact ⟨ha, ha⟩), ?_⟩
  show (s (s.symm (a, a))).1 = a
  rw [s.apply_symm_apply]

/- English proof (translation)
Introduce `a ha`. Use `⟨s.symm (a, a), (hs.2.2 _).2 (by rw [s.apply_symm_apply]; exact ⟨ha, ha⟩), ?_⟩` and prove the remaining obligations. Use `show (s (s.symm (a, a))).2 = a`. Rewrite using `[s.apply_symm_apply]`.
-/
theorem sur_prPbar (hs : GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.IsSplitting σ v s) :
    ∀ a ∈ v.adicCompletionIntegers F, ∃ x ∈ intV E v, GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.prPbar s x = a := by
  intro a ha
  refine ⟨s.symm (a, a), (hs.2.2 _).2 (by rw [s.apply_symm_apply]; exact ⟨ha, ha⟩), ?_⟩
  show (s (s.symm (a, a))).2 = a
  rw [s.apply_symm_apply]

/- English proof (translation)
The claim follows from `Set.ext fun y => mem_partOf _ (sur_prP hs) Λ y`.
-/
theorem coe_partOf_prP (hs : GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.IsSplitting σ v s)
    (Λ : Submodule (intV E v) (n → E ⊗[F] v.adicCompletion F)) :
    (GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.partOf (GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.prP s) Λ : Set (n → v.adicCompletion F)) =
      GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.pr₁ s '' (Λ : Set _) :=
  Set.ext fun y => mem_partOf _ (sur_prP hs) Λ y

/- English proof (translation)
The claim follows from `Set.ext fun y => mem_partOf _ (sur_prPbar hs) Λ y`.
-/
theorem coe_partOf_prPbar (hs : GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.IsSplitting σ v s)
    (Λ : Submodule (intV E v) (n → E ⊗[F] v.adicCompletion F)) :
    (GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.partOf (GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.prPbar s) Λ : Set (n → v.adicCompletion F)) =
      GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.pr₂ s '' (Λ : Set _) :=
  Set.ext fun y => mem_partOf _ (sur_prPbar hs) Λ y

end Part

/- English proof (translation)
Establish `hm : ∀ (x : n → A) i, (((bc p g : GL n K) : Matrix n n K) *ᵥ fun j => p (x j)) i = p (((g : Matrix n n A) *ᵥ x) i)` using `fun x i => (RingHom.map_mulVec p _ _ _).symm`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hg2, h⟩`. Use `⟨hg', fun y => ?_⟩` and prove the remaining obligations. Take `⟨x, hx, hxy⟩` from `(hΛ y).1 y.2`.

Establish `e1` using `hf ⟨x, hx⟩ y (fun i => (congrFun hxy i).symm)`. Establish `e2` using `hf ⟨(g : Matrix n n _) *ᵥ x, (hg2 x).1 hx⟩ ⟨((bc p g : GL n _) : Matrix n n _) *ᵥ (y : n → _), (hg' y).1 y.2⟩ (fun i => by show (((bc p g : GL n _) : Matrix n n _) *ᵥ (y : n → _)) i = p (((g : Matrix n n _) *ᵥ x) i)`. Rewrite using `[← hxy, hm])`. Conclude with `e2.trans ((congrArg ε (h ⟨x, hx⟩)).trans e1.symm)`. Introduce and unpack `⟨hg2, h⟩`.

Use `⟨hg, fun x => ε.injective ?_⟩` and prove the remaining obligations. Establish `hy : (fun i => p (x.1 i)) ∈ Λ'` using `(hΛ _).2 ⟨x, x.2, rfl⟩`. Establish `e1` using `hf x ⟨_, hy⟩ (fun _ => rfl)`. Establish `e2` using `hf ⟨(g : Matrix n n _) *ᵥ x.1, (hg x).1 x.2⟩ ⟨((bc p g : GL n _) : Matrix n n _) *ᵥ (fun i => p (x.1 i)), (hg2 _).1 hy⟩ (fun i => hm _ i)`. Conclude with `e2.symm.trans ((h ⟨_, hy⟩).trans e1)`.
-/
theorem mem_stabFun_iff_part {n A S K O : Type} [Fintype n] [DecidableEq n] [CommRing A] [CommRing S]
    [Algebra S A] [CommRing K] [CommRing O] [Algebra O K] (p : A →+* K)
    (Λ : Submodule S (n → A)) (Λ' : Submodule O (n → K))
    (hΛ : ∀ y, y ∈ Λ' ↔ ∃ x ∈ Λ, (fun i => p (x i)) = y)
    {M M' : Type} [AddCommGroup M] [Module S M] [AddCommGroup M']
    [Module O M'] (f₀ : Λ →ₗ[S] M) (f : Λ' →ₗ[O] M') (ε : M ≃+ M')
    (hf : ∀ (x : Λ) (y : Λ'), (∀ i, y.1 i = p (x.1 i)) → f y = ε (f₀ x))
    (g : GL n A) (hg : g ∈ stabGL Λ) (hg' : bc p g ∈ stabGL Λ') :
    g ∈ stabFun Λ f₀ ↔ bc p g ∈ stabFun Λ' f := by
  have hm : ∀ (x : n → A) i, (((bc p g : GL n K) : Matrix n n K) *ᵥ fun j => p (x j)) i =
        p (((g : Matrix n n A) *ᵥ x) i) := fun x i => (RingHom.map_mulVec p _ _ _).symm
  constructor
  · rintro ⟨hg2, h⟩
    refine ⟨hg', fun y => ?_⟩
    obtain ⟨x, hx, hxy⟩ := (hΛ y).1 y.2
    have e1 := hf ⟨x, hx⟩ y (fun i => (congrFun hxy i).symm)
    have e2 := hf ⟨(g : Matrix n n _) *ᵥ x, (hg2 x).1 hx⟩
      ⟨((bc p g : GL n _) : Matrix n n _) *ᵥ (y : n → _), (hg' y).1 y.2⟩ (fun i => by
        show (((bc p g : GL n _) : Matrix n n _) *ᵥ (y : n → _)) i = p (((g : Matrix n n _) *ᵥ x) i)
        rw [← hxy, hm])
    exact e2.trans ((congrArg ε (h ⟨x, hx⟩)).trans e1.symm)
  · rintro ⟨hg2, h⟩
    refine ⟨hg, fun x => ε.injective ?_⟩
    have hy : (fun i => p (x.1 i)) ∈ Λ' := (hΛ _).2 ⟨x, x.2, rfl⟩
    have e1 := hf x ⟨_, hy⟩ (fun _ => rfl)
    have e2 := hf ⟨(g : Matrix n n _) *ᵥ x.1, (hg x).1 x.2⟩
      ⟨((bc p g : GL n _) : Matrix n n _) *ᵥ (fun i => p (x.1 i)), (hg2 _).1 hy⟩ (fun i => hm _ i)
    exact e2.symm.trans ((h ⟨_, hy⟩).trans e1)

end GlobalTheory.OverCompare

end
