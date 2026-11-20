import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.SpanPowerMembership.RelDetCore
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Development.AutomorphicArithmetic.WeightCongruences.IsRootOfIntegral

open NumberField

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open Formalism.BasicNotions

section RelDet

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Unfold `SDLat.smulLat`. Rewrite using `[Matrix.toLin'_one]`. Conclude with `Submodule.map_id L`.
-/
theorem smulLat_one {N : ℕ} (L : Submodule (𝓞 E) (Fin N → E)) :
    SDLat.smulLat (1 : Matrix (Fin N) (Fin N) E) L = L := by
  unfold SDLat.smulLat
  rw [Matrix.toLin'_one]
  exact Submodule.map_id L

/- English proof (translation)
Unfold `SDLat.smulLat`. Rewrite using `[← Submodule.map_comp, Matrix.toLin'_mul]`. Both sides reduce to the same expression.
-/
theorem smulLat_mul {N : ℕ} (A B : Matrix (Fin N) (Fin N) E) (L : Submodule (𝓞 E) (Fin N → E)) :
    SDLat.smulLat (A * B) L = SDLat.smulLat A (SDLat.smulLat B L) := by
  unfold SDLat.smulLat
  rw [← Submodule.map_comp, Matrix.toLin'_mul]
  rfl

def orbRel (N : ℕ) : Setoid (SDLat E N) where
  r L L' := ∃ γ : Matrix.unitaryGroup (Fin N) E, L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) E) L.1
  iseqv := by
    refine ⟨fun L => ⟨1, ?_⟩, fun {L L'} ⟨γ, h⟩ => ⟨γ⁻¹, ?_⟩, fun {L L' L''} ⟨γ, h⟩ ⟨γ', h'⟩ => ⟨γ' * γ, ?_⟩⟩
    · exact (smulLat_one L.1).symm
    · rw [h, ← smulLat_mul]
      have : ((γ⁻¹ : Matrix.unitaryGroup (Fin N) E) : Matrix (Fin N) (Fin N) E) *
          (γ : Matrix (Fin N) (Fin N) E) = 1 := by
        rw [← Submonoid.coe_mul, inv_mul_cancel]; rfl
      rw [this, smulLat_one]
    · rw [h', h, ← smulLat_mul]; rfl

def orbRep {N : ℕ} (L : SDLat E N) : SDLat E N := (Quotient.mk (orbRel N) L).out

/- English proof (translation)
The claim follows from `Quotient.mk_out (s := orbRel N) L`.
-/
theorem orbRep_rel {N : ℕ} (L : SDLat E N) : (orbRel N) (orbRep L) L := Quotient.mk_out (s := orbRel N) L

/- English proof (translation)
Unfold `orbRep`. Rewrite using `[Quotient.sound h]`.
-/
theorem orbRep_eq {N : ℕ} {L L' : SDLat E N} (h : (orbRel N) L L') : orbRep L = orbRep L' := by
  unfold orbRep
  rw [Quotient.sound h]

def orbGam {N : ℕ} (L : SDLat E N) : Matrix.unitaryGroup (Fin N) E := Classical.choose (orbRep_rel L)

/- English proof (translation)
The claim follows from `Classical.choose_spec (orbRep_rel L)`.
-/
theorem orbGam_spec {N : ℕ} (L : SDLat E N) :
    L.1 = SDLat.smulLat ((orbGam L : Matrix.unitaryGroup (Fin N) E) : Matrix (Fin N) (Fin N) E) (orbRep L).1 :=
  Classical.choose_spec (orbRep_rel L)

def detU {N : ℕ} (γ : Matrix.unitaryGroup (Fin N) E) : unitary E :=
  ⟨(γ : Matrix (Fin N) (Fin N) E).det, Matrix.det_of_mem_unitary γ.2⟩

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use `show ((γ * δ : Matrix.unitaryGroup (Fin N) E) : Matrix (Fin N) (Fin N) E).det = _`. Rewrite using `[Submonoid.coe_mul, Matrix.det_mul]`. Both sides reduce to the same expression.
-/
theorem detU_mul {N : ℕ} (γ δ : Matrix.unitaryGroup (Fin N) E) : detU (γ * δ) = detU γ * detU δ := by
  apply Subtype.ext
  show ((γ * δ : Matrix.unitaryGroup (Fin N) E) : Matrix (Fin N) (Fin N) E).det = _
  rw [Submonoid.coe_mul, Matrix.det_mul]
  rfl

variable {Tau : Type} [Fintype Tau] (emb : Tau → (E →+* ℂ))

def inverseEmbeddingProduct : unitary E →* ℂˣ :=
  (∏ τ : Tau, (Units.map (emb τ).toMonoidHom).comp Unitary.toUnits)⁻¹

/- English proof (translation)
Simplify using `[inverseEmbeddingProduct]`.
-/
theorem inverseEmbeddingProduct_apply (z : unitary E) : ((inverseEmbeddingProduct emb z : ℂˣ) : ℂ) = ∏ τ : Tau, (emb τ (z : E))⁻¹ := by
  simp [inverseEmbeddingProduct]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[inverseEmbeddingProduct_apply, Units.val_one]`. Break down `hz with hz | hz` into its components or cases. Simplify using `[hz]`. Simplify using `[hz, hcard.neg_one_pow]`.
-/
theorem inverseEmbeddingProduct_sign_eq_one (hcard : Even (Fintype.card Tau)) (z : unitary E) (hz : (z : E) = 1 ∨ (z : E) = -1) :
    inverseEmbeddingProduct emb z = 1 := by
  apply Units.ext
  rw [inverseEmbeddingProduct_apply, Units.val_one]
  rcases hz with hz | hz
  · simp [hz]
  · simp [hz, hcard.neg_one_pow]

def potGen {N : ℕ} (L : SDLat E N) : ℂˣ := inverseEmbeddingProduct emb (detU (orbGam L))

def relDetGen (N : ℕ) (L L' : SDLat E N) : ℂˣ := (potGen emb L)⁻¹ * potGen emb L'

/- English proof (translation)
Simplify using `[relDetGen]`.
-/
theorem relDetGen_self (N : ℕ) (L : SDLat E N) : relDetGen emb N L L = 1 := by
  simp [relDetGen]

/- English proof (translation)
Simplify using `only [relDetGen]`. Use `group`.
-/
theorem relDetGen_mul (N : ℕ) (L L' L'' : SDLat E N) :
    relDetGen emb N L L' * relDetGen emb N L' L'' = relDetGen emb N L L'' := by
  simp only [relDetGen]
  group

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[inverseEmbeddingProduct_apply, Units.val_one, Finset.prod_inv_distrib, inv_eq_one]`. Apply `hmu` to reduce the goal to its premises. Use `det_root_of_unity_of_stab hstar (δ : Matrix (Fin N) (Fin N) E) (Matrix.det_of_mem_unitary δ.2) L.1 L.2.1 L.2.2.1 ?_` and prove the remaining obligations. Introduce `x hx`.

Establish `: (δ : Matrix (Fin N) (Fin N) E).mulVec x ∈ SDLat.smulLat (δ : Matrix (Fin N) (Fin N) E) L.1` using `⟨x, hx, by simp [Matrix.toLin'_apply]⟩`. Rewrite `this` using `[hδ]`. Then use the resulting hypothesis.
-/
theorem inverseEmbeddingProduct_stabilizer_det (hstar : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x))
    (hmu : ∀ x : E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → ∏ τ : Tau, emb τ x = 1)
    {N : ℕ} (δ : Matrix.unitaryGroup (Fin N) E) (L : SDLat E N)
    (hδ : SDLat.smulLat (δ : Matrix (Fin N) (Fin N) E) L.1 = L.1) : inverseEmbeddingProduct emb (detU δ) = 1 := by
  apply Units.ext
  rw [inverseEmbeddingProduct_apply, Units.val_one, Finset.prod_inv_distrib, inv_eq_one]
  apply hmu
  refine det_root_of_unity_of_stab hstar (δ : Matrix (Fin N) (Fin N) E) (Matrix.det_of_mem_unitary δ.2)
    L.1 L.2.1 L.2.2.1 ?_
  intro x hx
  have : (δ : Matrix (Fin N) (Fin N) E).mulVec x ∈ SDLat.smulLat (δ : Matrix (Fin N) (Fin N) E) L.1 :=
    ⟨x, hx, by simp [Matrix.toLin'_apply]⟩
  rwa [hδ] at this

/- English proof (translation)
Establish `hrel : (orbRel N) L L'` using `⟨γ, h⟩`. Establish `hrep : orbRep L' = orbRep L` using `(orbRep_eq hrel).symm`. Use `set r := orbRep L with hr`. Use `set gL := orbGam L`. Use `set gL' := orbGam L'`.

Establish `hL : L.1 = SDLat.smulLat (gL : Matrix (Fin N) (Fin N) E) r.1` using `orbGam_spec L`. Establish `hL' : L'.1 = SDLat.smulLat (gL' : Matrix (Fin N) (Fin N) E) r.1`. Use `orbGam_spec L'` as an intermediate fact. Rewrite `this` using `[hrep]`. Then use the resulting hypothesis. Use `set δ : Matrix.unitaryGroup (Fin N) E := (γ * gL)⁻¹ * gL'`.

Establish `hδ : SDLat.smulLat (δ : Matrix (Fin N) (Fin N) E) r.1 = r.1`. Establish `e1 : SDLat.smulLat ((γ * gL : Matrix.unitaryGroup (Fin N) E) : Matrix (Fin N) (Fin N) E) r.1 = SDLat.smulLat (gL' : Matrix (Fin N) (Fin N) E) r.1`. Rewrite using `[Submonoid.coe_mul, smulLat_mul, ← hL, ← h, hL']`. Use `show SDLat.smulLat (((γ * gL)⁻¹ * gL' : Matrix.unitaryGroup (Fin N) E) : Matrix (Fin N) (Fin N) E) r.1 = r.1`. Rewrite using `[Submonoid.coe_mul, smulLat_mul, ← e1, ← smulLat_mul, ← Submonoid.coe_mul, inv_mul_cancel]`.

Conclude with `smulLat_one r.1`. Establish `hs` using `inverseEmbeddingProduct_stabilizer_det emb hstar hmu δ r hδ`. Establish `hg : gL' = (γ * gL) * δ` using `by show gL' = (γ * gL) * ((γ * gL)⁻¹ * gL')`. Rewrite using `[← mul_assoc, mul_inv_cancel, one_mul]`. Establish `: potGen emb L' = inverseEmbeddingProduct emb (detU γ) * potGen emb L`.

Simplify using `only [potGen]`. Rewrite using `[show orbGam L' = gL' from rfl, hg, detU_mul, detU_mul, map_mul, map_mul, hs, mul_one, mul_comm]`. Simplify using `only [relDetGen, this]`. Rewrite using `[mul_comm (inverseEmbeddingProduct emb (detU γ)), ← mul_assoc, inv_mul_cancel, one_mul]`. Both sides reduce to the same expression.
-/
theorem relDetGen_smul (hstar : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x))
    (hmu : ∀ x : E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → ∏ τ : Tau, emb τ x = 1)
    (N : ℕ) (L L' : SDLat E N) (γ : Matrix.unitaryGroup (Fin N) E)
    (h : L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) E) L.1) :
    relDetGen emb N L L' = inverseEmbeddingProduct emb ⟨(γ : Matrix (Fin N) (Fin N) E).det, Matrix.det_of_mem_unitary γ.2⟩ := by
  have hrel : (orbRel N) L L' := ⟨γ, h⟩
  have hrep : orbRep L' = orbRep L := (orbRep_eq hrel).symm
  set r := orbRep L with hr
  set gL := orbGam L
  set gL' := orbGam L'
  have hL : L.1 = SDLat.smulLat (gL : Matrix (Fin N) (Fin N) E) r.1 := orbGam_spec L
  have hL' : L'.1 = SDLat.smulLat (gL' : Matrix (Fin N) (Fin N) E) r.1 := by
    have := orbGam_spec L'; rwa [hrep] at this
  set δ : Matrix.unitaryGroup (Fin N) E := (γ * gL)⁻¹ * gL'
  have hδ : SDLat.smulLat (δ : Matrix (Fin N) (Fin N) E) r.1 = r.1 := by
    have e1 : SDLat.smulLat ((γ * gL : Matrix.unitaryGroup (Fin N) E) : Matrix (Fin N) (Fin N) E) r.1 =
        SDLat.smulLat (gL' : Matrix (Fin N) (Fin N) E) r.1 := by
      rw [Submonoid.coe_mul, smulLat_mul, ← hL, ← h, hL']
    show SDLat.smulLat (((γ * gL)⁻¹ * gL' : Matrix.unitaryGroup (Fin N) E) : Matrix (Fin N) (Fin N) E) r.1 = r.1
    rw [Submonoid.coe_mul, smulLat_mul, ← e1, ← smulLat_mul, ← Submonoid.coe_mul, inv_mul_cancel]
    exact smulLat_one r.1
  have hs := inverseEmbeddingProduct_stabilizer_det emb hstar hmu δ r hδ
  have hg : gL' = (γ * gL) * δ := by
    show gL' = (γ * gL) * ((γ * gL)⁻¹ * gL')
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  have : potGen emb L' = inverseEmbeddingProduct emb (detU γ) * potGen emb L := by
    simp only [potGen]
    rw [show orbGam L' = gL' from rfl, hg, detU_mul, detU_mul, map_mul, map_mul, hs, mul_one, mul_comm]
  simp only [relDetGen, this]
  rw [mul_comm (inverseEmbeddingProduct emb (detU γ)), ← mul_assoc, inv_mul_cancel, one_mul]
  rfl

end RelDet

section Host

variable {R : Ranks} (H : Host R) {Tau : Type} [Fintype Tau] (eTau : Tau ≃ ↥(R.Psi))

def embTau : Tau → (H.E →+* ℂ) := fun τ => H.emb ((eTau τ : R.Psi) : R.GG)

/- English proof (translation)
Introduce `_ hx` and use `UpperTheory.Mu.prod_emb H eTau hx`.
-/
theorem prod_embTau_eq_one_of_torsion : ∀ x : H.E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → ∏ τ : Tau, embTau H eTau τ x = 1 :=
  fun _ hx => UpperTheory.Mu.prod_emb H eTau hx

/- English proof (translation)
Introduce and unpack `x ⟨m, hm, hx⟩`. Establish `hi : IsIntegral ℤ x` using `IsIntegral.of_pow hm (by rw [hx]; exact isIntegral_one)`. Set `y : 𝓞 H.E` to `⟨x, hi⟩`. Establish `hy : y ^ m = 1`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises.

Rewrite using `[map_pow, map_one]`. Conclude with `hx`. Set `u : (𝓞 H.E)ˣ` to `Units.ofPowEqOne y m hy hm.ne'`. Establish `hu : u ∈ Units.torsion H.E`. Rewrite using `[Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]`.

Conclude with `⟨m, hm, Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hy)⟩`. Establish `hc : Nat.card (Units.torsion H.E) = 2`. Rewrite using `[← h2, Units.torsionOrder]`. Apply the tactic sequence `try simp`. Establish `h1 : (⟨u, hu⟩ : Units.torsion H.E) ^ 2 = 1` using `by rw [← hc]; exact pow_card_eq_one'`.

Establish `h3 : u ^ 2 = 1` using `congrArg Subtype.val h1`. Establish `h4 : y ^ 2 = 1` using `congrArg Units.val h3`. Establish `h5 : x ^ 2 = 1`. Use `congrArg (algebraMap (𝓞 H.E) H.E) h4` as an intermediate fact. Rewrite `this` using `[map_pow, map_one]`. Then use the resulting hypothesis.

Conclude with `sq_eq_one_iff.mp h5`.
-/
theorem eq_one_or_neg_one_of_torsionOrder_two (h2 : Units.torsionOrder H.E = 2) :
    ∀ x : H.E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → x = 1 ∨ x = -1 := by
  rintro x ⟨m, hm, hx⟩
  have hi : IsIntegral ℤ x := IsIntegral.of_pow hm (by rw [hx]; exact isIntegral_one)
  let y : 𝓞 H.E := ⟨x, hi⟩
  have hy : y ^ m = 1 := by
    apply RingOfIntegers.coe_injective
    rw [map_pow, map_one]
    exact hx
  let u : (𝓞 H.E)ˣ := Units.ofPowEqOne y m hy hm.ne'
  have hu : u ∈ Units.torsion H.E := by
    rw [Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    exact ⟨m, hm, Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hy)⟩
  have hc : Nat.card (Units.torsion H.E) = 2 := by
    rw [← h2, Units.torsionOrder]
    try simp
  have h1 : (⟨u, hu⟩ : Units.torsion H.E) ^ 2 = 1 := by rw [← hc]; exact pow_card_eq_one'
  have h3 : u ^ 2 = 1 := congrArg Subtype.val h1
  have h4 : y ^ 2 = 1 := congrArg Units.val h3
  have h5 : x ^ 2 = 1 := by
    have := congrArg (algebraMap (𝓞 H.E) H.E) h4
    rwa [map_pow, map_one] at this
  exact sq_eq_one_iff.mp h5

/- English proof (translation)
Rewrite using `[← Nat.card_eq_fintype_card, Nat.card_congr eTau, R.toFrame.natCard_Psi]`. Conclude with `even_two_mul _`.
-/
theorem even_card_Tau {R : Ranks} {Tau : Type} [Fintype Tau] (eTau : Tau ≃ ↥(R.Psi)) :
    Even (Fintype.card Tau) := by
  rw [← Nat.card_eq_fintype_card, Nat.card_congr eTau, R.toFrame.natCard_Psi]
  exact even_two_mul _

def exampleInverseEmbeddingProduct : letI := H.cmStar; unitary H.E →* ℂˣ := letI := H.cmStar; inverseEmbeddingProduct (embTau H eTau)

/- English proof (translation)
Set `_` to `H.cmStar`. Introduce `z`. Conclude with `inverseEmbeddingProduct_apply (embTau H eTau) z`.
-/
theorem exampleCharacter_unitary_product : letI := H.cmStar; ∀ z : unitary H.E,
    (((MonoidHom.id ℂˣ) (exampleInverseEmbeddingProduct H eTau z) : ℂˣ) : ℂ) =
      ∏ τ : Tau, (H.emb ((eTau τ : R.Psi) : R.GG) (z : H.E))⁻¹ := by
  let _ := H.cmStar
  intro z
  exact inverseEmbeddingProduct_apply (embTau H eTau) z

def relDetExample : letI := H.cmStar; ∀ N, SDLat H.E N → SDLat H.E N → ℂˣ :=
  letI := H.cmStar; relDetGen (embTau H eTau)

/- English proof (translation)
Set `_` to `H.cmStar`. Conclude with `relDetGen_self (embTau H eTau)`.
-/
theorem relDetExample_self : letI := H.cmStar; ∀ N L, relDetExample H eTau N L L = 1 := by
  let _ := H.cmStar
  exact relDetGen_self (embTau H eTau)

/- English proof (translation)
Set `_` to `H.cmStar`. Conclude with `relDetGen_mul (embTau H eTau)`.
-/
theorem relDetExample_mul : letI := H.cmStar; ∀ N L L' L'',
    relDetExample H eTau N L L' * relDetExample H eTau N L' L'' = relDetExample H eTau N L L'' := by
  let _ := H.cmStar
  exact relDetGen_mul (embTau H eTau)

/- English proof (translation)
Set `_` to `H.cmStar`. Conclude with `relDetGen_smul (embTau H eTau) (emb_star H) (prod_embTau_eq_one_of_torsion H eTau)`.
-/
theorem relDetExample_smul : letI := H.cmStar; ∀ N (L L' : SDLat H.E N) (γ : Matrix.unitaryGroup (Fin N) H.E),
    L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) H.E) L.1 →
      relDetExample H eTau N L L' = exampleInverseEmbeddingProduct H eTau
        ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩ := by
  let _ := H.cmStar
  exact relDetGen_smul (embTau H eTau) (emb_star H) (prod_embTau_eq_one_of_torsion H eTau)

end Host

end Formalism.BasicNotions.Examples₂
