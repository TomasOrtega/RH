import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjMemSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeFrameEmbedding

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Formalism.UG Sa2 Matrix

namespace GlobalTheory.CompanionTheory.PlaneSA.OfTwo

section Group

variable {S : Type} [CommRing S] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  {c : S →+* S} {J : Matrix m m S} {K : Matrix n n S} {a : S} {V : Matrix m n S} {P : Matrix n m S}

def uHom (h : IsFrame c J K a V P) : UJ c K →* UJ c J where
  toFun g := ⟨Units.map (embHom h.pv) g.1, frame_embedding_unitary h g.2⟩
  map_one' := Subtype.ext (map_one (Units.map (embHom h.pv)))
  map_mul' g g' := Subtype.ext (map_mul (Units.map (embHom h.pv)) g.1 g'.1)

/- English proof (translation)
Use `set G : Matrix m m S := (g.1 : Matrix m m S) with hG`. Use `set H : Matrix m m S := ((g⁻¹).1 : Matrix m m S) with hH`. Establish `hHG : H * G = 1`. Establish `e : ((g⁻¹ * g).1 : GL m S) = 1` using `by rw [inv_mul_cancel]; rfl`. Conclude with `congrArg Units.val e`.

Establish `hGH : G * H = 1`. Establish `e : ((g * g⁻¹).1 : GL m S) = 1` using `by rw [mul_inv_cancel]; rfl`. Conclude with `congrArg Units.val e`. Establish `h1 : (1 - V * P) * G = 1 - V * P` using `fix_left h hL g.2 hq`. Establish `hq' : H * (1 - V * P) = 1 - V * P`.

Combine the equalities or inequalities in the displayed calculation. Establish `h1' : (1 - V * P) * H = 1 - V * P`. Combine the equalities or inequalities in the displayed calculation. Establish `eG : emb0 V P (P * G * V) = G` using `frame_embedding_projection h.pv hq h1`. Establish `eH : emb0 V P (P * H * V) = H` using `frame_embedding_projection h.pv hq' h1'`.

Establish `hxy : (P * G * V) * (P * H * V) = 1`. Use `projection_frame_embedding h.pv ((P * G * V) * (P * H * V))` as an intermediate fact. Rewrite `this` using `[embed_mul h.pv, eG, eH, hGH, Matrix.mul_one, h.pv]`. Conclude with `this.symm`. Establish `hyx : (P * H * V) * (P * G * V) = 1`.

Use `projection_frame_embedding h.pv ((P * H * V) * (P * G * V))` as an intermediate fact. Rewrite `this` using `[embed_mul h.pv, eG, eH, hHG, Matrix.mul_one, h.pv]`. Conclude with `this.symm`. Set `x : GL n S` to `⟨P * G * V, P * H * V, hxy, hyx⟩`. Establish `hb : IsFrame c J K a V P` using `h`.

Establish `hu : cT c (x : Matrix n n S) * K * (x : Matrix n n S) = K`. Use `unitary_of_frame_embedding h hab ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `cT c (emb0 V P (P * G * V)) * J * emb0 V P (P * G * V) = J`. Rewrite using `[eG]`. Conclude with `g.2`.

Use `⟨⟨x, hu⟩, Subtype.ext (Units.ext eG), rfl⟩` and prove the remaining obligations.
-/
theorem exists_preimage (h : IsFrame c J K a V P) {b : S} (hab : b * a = 1) {L : Matrix m m S}
    (hL : L * J = 1) (g : UJ c J) (hq : (g.1 : Matrix m m S) * (1 - V * P) = 1 - V * P) :
    ∃ y : UJ c K, uHom h y = g ∧ (y.1 : Matrix n n S) = P * (g.1 : Matrix m m S) * V := by
  set G : Matrix m m S := (g.1 : Matrix m m S) with hG
  set H : Matrix m m S := ((g⁻¹).1 : Matrix m m S) with hH
  have hHG : H * G = 1 := by
    have e : ((g⁻¹ * g).1 : GL m S) = 1 := by rw [inv_mul_cancel]; rfl
    exact congrArg Units.val e
  have hGH : G * H = 1 := by
    have e : ((g * g⁻¹).1 : GL m S) = 1 := by rw [mul_inv_cancel]; rfl
    exact congrArg Units.val e
  have h1 : (1 - V * P) * G = 1 - V * P := fix_left h hL g.2 hq
  have hq' : H * (1 - V * P) = 1 - V * P := by
    calc H * (1 - V * P) = H * (G * (1 - V * P)) := by rw [hq]
      _ = 1 - V * P := by rw [← Matrix.mul_assoc, hHG, Matrix.one_mul]
  have h1' : (1 - V * P) * H = 1 - V * P := by
    calc (1 - V * P) * H = (1 - V * P) * G * H := by rw [h1]
      _ = 1 - V * P := by rw [Matrix.mul_assoc, hGH, Matrix.mul_one]
  have eG : emb0 V P (P * G * V) = G := frame_embedding_projection h.pv hq h1
  have eH : emb0 V P (P * H * V) = H := frame_embedding_projection h.pv hq' h1'
  have hxy : (P * G * V) * (P * H * V) = 1 := by
    have := projection_frame_embedding h.pv ((P * G * V) * (P * H * V))
    rw [embed_mul h.pv, eG, eH, hGH, Matrix.mul_one, h.pv] at this
    exact this.symm
  have hyx : (P * H * V) * (P * G * V) = 1 := by
    have := projection_frame_embedding h.pv ((P * H * V) * (P * G * V))
    rw [embed_mul h.pv, eG, eH, hHG, Matrix.mul_one, h.pv] at this
    exact this.symm
  let x : GL n S := ⟨P * G * V, P * H * V, hxy, hyx⟩
  have hb : IsFrame c J K a V P := h
  have hu : cT c (x : Matrix n n S) * K * (x : Matrix n n S) = K := by
    refine unitary_of_frame_embedding h hab ?_
    change cT c (emb0 V P (P * G * V)) * J * emb0 V P (P * G * V) = J
    rw [eG]
    exact g.2
  refine ⟨⟨x, hu⟩, Subtype.ext (Units.ext eG), rfl⟩

end Group

section Basis

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[h.2.2.2, h.2.2.2, star_star]`.
-/
theorem conj_conj [NumberField E] {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

/- English proof (translation)
Use `haveI := Subalgebra.isSimpleOrder_of_finrank h.2.2.1`. Use `haveI := h.2.1`. Break down `eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h1 | h1` into its components or cases. Establish `: x ∈ AlgHom.equalizer σ (AlgHom.id F E)` using `hx`. Rewrite `this` using `[h1]`.

Conclude with `Algebra.mem_bot.1 this`. It suffices to derive a contradiction. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `IsTotallyComplex.complexEmbedding_not_isReal τ` to reduce the goal to its premises. Rewrite using `[ComplexEmbedding.isReal_iff]`.

Use extensionality with `y`. Establish `hy : y ∈ AlgHom.equalizer σ (AlgHom.id F E)` using `h1 ▸ Algebra.mem_top`. Establish `hy' : σ y = y` using `hy`. Use `h.2.2.2 τ y` as an intermediate fact. Rewrite `this` using `[hy']`.

Conclude with `this.symm`.
-/
theorem exists_of_conj_eq [NumberField E] {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {x : E} (hx : σ x = x) :
    ∃ t : F, algebraMap F E t = x := by
  haveI := Subalgebra.isSimpleOrder_of_finrank h.2.2.1
  haveI := h.2.1
  rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h1 | h1
  · have : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := hx
    rw [h1] at this
    exact Algebra.mem_bot.1 this
  · exfalso
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [ComplexEmbedding.isReal_iff]
    ext y
    have hy : y ∈ AlgHom.equalizer σ (AlgHom.id F E) := h1 ▸ Algebra.mem_top
    have hy' : σ y = y := hy
    have := h.2.2.2 τ y
    rw [hy'] at this
    exact this.symm

variable {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

/- English proof (translation)
Simplify using `only [hf, Pi.add_apply, mul_add, Finset.sum_add_distrib]`.
-/
theorem hf_add_right (x y z : Fin M → E) : hf σ J x (y + z) = hf σ J x y + hf σ J x z := by
  simp only [hf, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem hf_smul_right (t : E) (x y : Fin M → E) : hf σ J x (t • y) = t * hf σ J x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Simplify using `only [hf, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]`.
-/
theorem hf_add_left (x y z : Fin M → E) : hf σ J (x + y) z = hf σ J x z + hf σ J y z := by
  simp only [hf, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem hf_smul_left (t : E) (x y : Fin M → E) : hf σ J (t • x) y = σ t * hf σ J x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Simplify using `only [hf, map_sum, map_mul, hσ, hJ]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem hf_conj (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → E) :
    σ (hf σ J x y) = hf σ J y x := by
  simp only [hf, map_sum, map_mul, hσ, hJ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Use `set p := hf σ J w₀ w₀ with hpd`. Use `set q := hf σ J w₀ w₁ with hqd`. Use `set t := q / p with ht`. Establish `hσp : σ p = p` using `hf_conj hσ hJ w₀ w₀`. Establish `hσq : σ q = hf σ J w₁ w₀` using `hf_conj hσ hJ w₀ w₁`.

Use `set v₁ : Fin M → E := w₁ + (-t) • w₀ with hv₁`. Establish `h01 : hf σ J w₀ v₁ = 0`. Rewrite using `[hv₁, hf_add_right, hf_smul_right, ← hqd, ← hpd, ht]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `h10 : hf σ J v₁ w₀ = 0`. Rewrite using `[← hf_conj hσ hJ w₀ v₁, h01, map_zero]`. Establish `h11 : hf σ J v₁ v₁ = (p * hf σ J w₁ w₁ - q * σ q) / p`. Establish `e : hf σ J v₁ v₁ = hf σ J w₁ v₁` using `by conv_lhs => rw [hv₁, hf_add_left, hf_smul_left]`. Rewrite using `[← hv₁, h01, mul_zero, add_zero]`.

Rewrite using `[e, hv₁, hf_add_right, hf_smul_right, ← hσq, ht]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hb : hf σ J v₁ v₁ ≠ 0`. Rewrite using `[h11]`.

Use `div_ne_zero ?_ hp` and prove the remaining obligations. Rewrite using `[hσq]`. Conclude with `hd`. Take `⟨a, ha⟩` from `hfix p hσp`. Take `⟨b, hb'⟩` from `hfix _ (hf_conj hσ hJ v₁ v₁)`.

Use `⟨w₀, v₁, a, b, ?_, ?_, ha.symm, hb'.symm, h01, h10, fun x => ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl; exact hp (by rw [← ha, map_zero])`. Introduce and unpack `rfl; exact hb (by rw [← hb', map_zero])`. Establish `e : hf σ J v₁ x = hf σ J w₁ x + σ (-t) * hf σ J w₀ x`. Rewrite using `[hv₁, hf_add_left, hf_smul_left]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h0, h1⟩`. Conclude with `⟨h0, by rw [e, h0, h1]; simp⟩`. Introduce and unpack `⟨h0, h1⟩`. Use `⟨h0, ?_⟩` and prove the remaining obligations.

Rewrite `h1` using `[e, h0]`. Simplify using `using h1`.
-/
theorem orth_of_ne (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j)
    (hfix : ∀ x : E, σ x = x → ∃ t : F, algebraMap F E t = x) {w₀ w₁ : Fin M → E}
    (hp : hf σ J w₀ w₀ ≠ 0) (hd : PlaneND σ J w₀ w₁) :
    ∃ (v₀ v₁ : Fin M → E) (a b : F), a ≠ 0 ∧ b ≠ 0 ∧ hf σ J v₀ v₀ = algebraMap F E a ∧
      hf σ J v₁ v₁ = algebraMap F E b ∧ hf σ J v₀ v₁ = 0 ∧ hf σ J v₁ v₀ = 0 ∧
      ∀ x, (hf σ J w₀ x = 0 ∧ hf σ J w₁ x = 0) ↔ (hf σ J v₀ x = 0 ∧ hf σ J v₁ x = 0) := by
  set p := hf σ J w₀ w₀ with hpd
  set q := hf σ J w₀ w₁ with hqd
  set t := q / p with ht
  have hσp : σ p = p := hf_conj hσ hJ w₀ w₀
  have hσq : σ q = hf σ J w₁ w₀ := hf_conj hσ hJ w₀ w₁
  set v₁ : Fin M → E := w₁ + (-t) • w₀ with hv₁
  have h01 : hf σ J w₀ v₁ = 0 := by
    rw [hv₁, hf_add_right, hf_smul_right, ← hqd, ← hpd, ht]
    field_simp
    ring
  have h10 : hf σ J v₁ w₀ = 0 := by
    rw [← hf_conj hσ hJ w₀ v₁, h01, map_zero]
  have h11 : hf σ J v₁ v₁ = (p * hf σ J w₁ w₁ - q * σ q) / p := by
    have e : hf σ J v₁ v₁ = hf σ J w₁ v₁ := by
      conv_lhs => rw [hv₁, hf_add_left, hf_smul_left]
      rw [← hv₁, h01, mul_zero, add_zero]
    rw [e, hv₁, hf_add_right, hf_smul_right, ← hσq, ht]
    field_simp
    ring
  have hb : hf σ J v₁ v₁ ≠ 0 := by
    rw [h11]
    refine div_ne_zero ?_ hp
    rw [hσq]
    exact hd
  obtain ⟨a, ha⟩ := hfix p hσp
  obtain ⟨b, hb'⟩ := hfix _ (hf_conj hσ hJ v₁ v₁)
  refine ⟨w₀, v₁, a, b, ?_, ?_, ha.symm, hb'.symm, h01, h10, fun x => ?_⟩
  · rintro rfl; exact hp (by rw [← ha, map_zero])
  · rintro rfl; exact hb (by rw [← hb', map_zero])
  · have e : hf σ J v₁ x = hf σ J w₁ x + σ (-t) * hf σ J w₀ x := by
      rw [hv₁, hf_add_left, hf_smul_left]
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨h0, by rw [e, h0, h1]; simp⟩
    · rintro ⟨h0, h1⟩
      refine ⟨h0, ?_⟩
      rw [e, h0] at h1
      simpa using h1

/- English proof (translation)
Distinguish the cases in `hp : hf σ J u₀ u₀ = 0`. Distinguish the cases in `hr : hf σ J u₁ u₁ = 0`. Use `set q := hf σ J u₀ u₁ with hqd`. Establish `hσq : σ q = hf σ J u₁ u₀` using `hf_conj hσ hJ u₀ u₁`. Establish `hq : q * σ q ≠ 0`.

Introduce `h0`. Apply `hd` to reduce the goal to its premises. Rewrite using `[hp, hr, ← hσq, ← hqd, h0]`. Simplify using the standard rewrite rules. Use `set w₀ : Fin M → E := u₀ + σ q • u₁ with hw`.

Establish `e1 : hf σ J w₀ u₁ = q`. Rewrite using `[hw, hf_add_left, hf_smul_left, hr, mul_zero, add_zero]`. Establish `e2 : hf σ J u₁ w₀ = σ q`. Rewrite using `[hw, hf_add_right, hf_smul_right, hr, mul_zero, add_zero, hσq]`. Establish `e3 : hf σ J w₀ w₀ = 2 * (q * σ q)` using `by conv_lhs => rw [hw, hf_add_right, hf_smul_right]`.

Rewrite using `[← hw, e1, hw, hf_add_left, hf_smul_left, hp, ← hσq, hσ, zero_add]`. Expand and normalize the polynomial expressions, which then agree. Establish `hw0 : hf σ J w₀ w₀ ≠ 0` using `by haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective`. Rewrite using `[e3]`. Conclude with `mul_ne_zero two_ne_zero hq`.

Establish `hnd : PlaneND σ J w₀ u₁`. Express the relevant statement in the definitionally equal form `hf σ J w₀ w₀ * hf σ J u₁ u₁ - hf σ J w₀ u₁ * hf σ J u₁ w₀ ≠ 0`. Rewrite using `[hr, e1, e2, mul_zero, zero_sub]`. Conclude with `neg_ne_zero.2 hq`. Take `⟨v₀, v₁, a, b, ha, hb, h1, h2, h3, h4, h5⟩` from `orth_of_ne hσ hJ hfix hw0 hnd`.

Use `⟨v₀, v₁, a, b, ha, hb, h1, h2, h3, h4, fun x => Iff.trans ?_ (h5 x)⟩` and prove the remaining obligations. Establish `e : hf σ J w₀ x = hf σ J u₀ x + σ (σ q) * hf σ J u₁ x`. Rewrite using `[hw, hf_add_left, hf_smul_left]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h0, h1⟩`.

Conclude with `⟨by rw [e, h0, h1]; simp, h1⟩`. Introduce and unpack `⟨h0, h1⟩`. Use `⟨?_, h1⟩` and prove the remaining obligations. Rewrite `h0` using `[e, h1]`. Simplify using `using h0`.

Establish `hnd : PlaneND σ J u₁ u₀`. Establish `: hf σ J u₁ u₁ * hf σ J u₀ u₀ - hf σ J u₁ u₀ * hf σ J u₀ u₁ = hf σ J u₀ u₀ * hf σ J u₁ u₁ - hf σ J u₀ u₁ * hf σ J u₁ u₀` using `by ring`. Express the relevant statement in the definitionally equal form `hf σ J u₁ u₁ * hf σ J u₀ u₀ - hf σ J u₁ u₀ * hf σ J u₀ u₁ ≠ 0`. Rewrite using `[this]`. Conclude with `hd`.

Take `⟨v₀, v₁, a, b, ha, hb, h1, h2, h3, h4, h5⟩` from `orth_of_ne hσ hJ hfix hr hnd`. Conclude with `⟨v₀, v₁, a, b, ha, hb, h1, h2, h3, h4, fun x => Iff.trans and_comm (h5 x)⟩`. Conclude with `orth_of_ne hσ hJ hfix hp hd`.
-/
theorem exists_orth (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j)
    (hfix : ∀ x : E, σ x = x → ∃ t : F, algebraMap F E t = x) {u₀ u₁ : Fin M → E}
    (hd : PlaneND σ J u₀ u₁) :
    ∃ (v₀ v₁ : Fin M → E) (a b : F), a ≠ 0 ∧ b ≠ 0 ∧ hf σ J v₀ v₀ = algebraMap F E a ∧
      hf σ J v₁ v₁ = algebraMap F E b ∧ hf σ J v₀ v₁ = 0 ∧ hf σ J v₁ v₀ = 0 ∧
      ∀ x, (hf σ J u₀ x = 0 ∧ hf σ J u₁ x = 0) ↔ (hf σ J v₀ x = 0 ∧ hf σ J v₁ x = 0) := by
  by_cases hp : hf σ J u₀ u₀ = 0
  · by_cases hr : hf σ J u₁ u₁ = 0
    ·
      set q := hf σ J u₀ u₁ with hqd
      have hσq : σ q = hf σ J u₁ u₀ := hf_conj hσ hJ u₀ u₁
      have hq : q * σ q ≠ 0 := by
        intro h0
        apply hd
        rw [hp, hr, ← hσq, ← hqd, h0]; simp
      set w₀ : Fin M → E := u₀ + σ q • u₁ with hw
      have e1 : hf σ J w₀ u₁ = q := by
        rw [hw, hf_add_left, hf_smul_left, hr, mul_zero, add_zero]
      have e2 : hf σ J u₁ w₀ = σ q := by
        rw [hw, hf_add_right, hf_smul_right, hr, mul_zero, add_zero, hσq]
      have e3 : hf σ J w₀ w₀ = 2 * (q * σ q) := by
        conv_lhs => rw [hw, hf_add_right, hf_smul_right]
        rw [← hw, e1, hw, hf_add_left, hf_smul_left, hp, ← hσq, hσ, zero_add]
        ring
      have hw0 : hf σ J w₀ w₀ ≠ 0 := by
        haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
        rw [e3]; exact mul_ne_zero two_ne_zero hq
      have hnd : PlaneND σ J w₀ u₁ := by
        change hf σ J w₀ w₀ * hf σ J u₁ u₁ - hf σ J w₀ u₁ * hf σ J u₁ w₀ ≠ 0
        rw [hr, e1, e2, mul_zero, zero_sub]
        exact neg_ne_zero.2 hq
      obtain ⟨v₀, v₁, a, b, ha, hb, h1, h2, h3, h4, h5⟩ := orth_of_ne hσ hJ hfix hw0 hnd
      refine ⟨v₀, v₁, a, b, ha, hb, h1, h2, h3, h4, fun x => Iff.trans ?_ (h5 x)⟩
      have e : hf σ J w₀ x = hf σ J u₀ x + σ (σ q) * hf σ J u₁ x := by
        rw [hw, hf_add_left, hf_smul_left]
      constructor
      · rintro ⟨h0, h1⟩
        exact ⟨by rw [e, h0, h1]; simp, h1⟩
      · rintro ⟨h0, h1⟩
        refine ⟨?_, h1⟩
        rw [e, h1] at h0
        simpa using h0
    · have hnd : PlaneND σ J u₁ u₀ := by
        have : hf σ J u₁ u₁ * hf σ J u₀ u₀ - hf σ J u₁ u₀ * hf σ J u₀ u₁ =
            hf σ J u₀ u₀ * hf σ J u₁ u₁ - hf σ J u₀ u₁ * hf σ J u₁ u₀ := by ring
        change hf σ J u₁ u₁ * hf σ J u₀ u₀ - hf σ J u₁ u₀ * hf σ J u₀ u₁ ≠ 0
        rw [this]
        exact hd
      obtain ⟨v₀, v₁, a, b, ha, hb, h1, h2, h3, h4, h5⟩ := orth_of_ne hσ hJ hfix hr hnd
      exact ⟨v₀, v₁, a, b, ha, hb, h1, h2, h3, h4, fun x => Iff.trans and_comm (h5 x)⟩
  · exact orth_of_ne hσ hJ hfix hp hd

end Basis

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

def rowJ (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (v : Fin M → E) (j : Fin M) : E :=
  ∑ i, σ (v i) * J i j

/- English proof (translation)
Simplify using `only [hf, rowJ, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem sum_row (t : E) (x y : Fin M → E) : ∑ j, (t * rowJ σ J x j) * y j = t * hf σ J x y := by
  simp only [hf, rowJ, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Simplify using `only [rowJ, map_sum, map_mul, hσ, hJ]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`.
-/
theorem conj_row (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) (v : Fin M → E) (i : Fin M) :
    σ (rowJ σ J v i) = ∑ j, J i j * v j := by
  simp only [rowJ, map_sum, map_mul, hσ, hJ]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/- English proof (translation)
Establish `hσ` using `conj_conj hcm`. Take `⟨v₀, v₁, a, b, ha, hb, h1, h2, h3, h4, h5⟩` from `exists_orth hσ hJ.1 (fun x hx => exists_of_conj_eq hcm hx) hd`. Use `set A := algebraMap F E a with hAd`. Use `set B := algebraMap F E b with hBd`. Establish `hA : A ≠ 0` using `by rw [hAd]; exact (map_ne_zero _).2 ha`.

Establish `hB : B ≠ 0` using `by rw [hBd]; exact (map_ne_zero _).2 hb`. Establish `hσA : σ A = A` using `σ.commutes a`. Establish `hσB : σ B = B` using `σ.commutes b`. Set `V : Matrix (Fin M) (Fin 2) E` to `fun i k => ![v₀ i, v₁ i] k`. Set `P : Matrix (Fin 2) (Fin M) E` to `fun k j => ![A⁻¹ * rowJ σ J v₀ j, B⁻¹ * rowJ σ J v₁ j] k`.

Establish `hK : J2 E (-b / a) = !![1, 0; 0, B / A]`. Simplify using `[J2, map_div₀, map_neg, hAd, hBd, neg_div]`. Use `⟨-b / a, A, V, P, div_ne_zero (neg_ne_zero.2 hb) ha, hA, ⟨?_, ?_, ?_⟩, fun x => (h5 x).trans ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.one_fin_two]`. Use `Matrix.ext fun k l => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.mul_apply]`. Apply the tactic sequence `fin_cases k <;> fin_cases l`. Express the relevant statement in the definitionally equal form `∑ j, (A⁻¹ * rowJ σ J v₀ j) * v₀ j = 1`. Rewrite using `[sum_row, h1, inv_mul_cancel₀ hA]`. Express the relevant statement in the definitionally equal form `∑ j, (A⁻¹ * rowJ σ J v₀ j) * v₁ j = 0`.

Rewrite using `[sum_row, h3, mul_zero]`. Express the relevant statement in the definitionally equal form `∑ j, (B⁻¹ * rowJ σ J v₁ j) * v₀ j = 0`. Rewrite using `[sum_row, h4, mul_zero]`. Express the relevant statement in the definitionally equal form `∑ j, (B⁻¹ * rowJ σ J v₁ j) * v₁ j = 1`. Rewrite using `[sum_row, h2, inv_mul_cancel₀ hB]`.

Rewrite using `[hK]`. Use `Matrix.ext fun i k => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_apply, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two]`. Use `fin_cases k`. Express the relevant statement in the definitionally equal form `∑ j, J i j * v₀ j = A • (σ (A⁻¹ * rowJ σ J v₀ i) * 1 + σ (B⁻¹ * rowJ σ J v₁ i) * 0)`.

Simplify using `only [map_mul, map_inv₀, RingHom.coe_coe, hσA, conj_row hσ hJ.1, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `∑ j, J i j * v₁ j = A • (σ (A⁻¹ * rowJ σ J v₀ i) * 0 + σ (B⁻¹ * rowJ σ J v₁ i) * (B / A))`. Simplify using `only [map_mul, map_inv₀, hσB, conj_row hσ hJ.1, smul_eq_mul]`.

Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules. Rewrite using `[hK]`. Use `Matrix.ext fun k j => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_apply, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two]`.

Use `fin_cases k`. Express the relevant statement in the definitionally equal form `∑ i, σ (v₀ i) * J i j = A • (1 * (A⁻¹ * rowJ σ J v₀ j) + 0 * (B⁻¹ * rowJ σ J v₁ j))`. Express the relevant statement in the definitionally equal form `rowJ σ J v₀ j = _`. Simplify using `only [smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.

Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `∑ i, σ (v₁ i) * J i j = A • (0 * (A⁻¹ * rowJ σ J v₀ j) + (B / A) * (B⁻¹ * rowJ σ J v₁ j))`. Express the relevant statement in the definitionally equal form `rowJ σ J v₁ j = _`. Simplify using `only [smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.

Simplify using the standard rewrite rules. Establish `e0 : P.mulVec x 0 = A⁻¹ * hf σ J v₀ x` using `sum_row _ _ _`. Establish `e1 : P.mulVec x 1 = B⁻¹ * hf σ J v₁ x` using `sum_row _ _ _`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g0, g1⟩`.

Use function extensionality and compare the values at `k`. Use `fin_cases k`. Express the relevant statement in the definitionally equal form `P.mulVec x 0 = 0`. Rewrite using `[e0, g0, mul_zero]`. Express the relevant statement in the definitionally equal form `P.mulVec x 1 = 0`.

Rewrite using `[e1, g1, mul_zero]`. Introduce `g`. Establish `g0` using `congrFun g 0`. Establish `g1` using `congrFun g 1`. Rewrite `g0` using `[e0]`.

Rewrite `g1` using `[e1]`. Conclude with `⟨by simpa [hA] using g0, by simpa [hB] using g1⟩`.
-/
theorem exists_frame (hcm : IsCMExt F E σ) (hJ : IsHermND σ J) {u₀ u₁ : Fin M → E} (hd : PlaneND σ J u₀ u₁) :
    ∃ (β : F) (a : E) (V : Matrix (Fin M) (Fin 2) E) (P : Matrix (Fin 2) (Fin M) E),
      β ≠ 0 ∧ a ≠ 0 ∧ IsFrame (σ : E →+* E) J (J2 E β) a V P ∧
      ∀ x : Fin M → E, (hf σ J u₀ x = 0 ∧ hf σ J u₁ x = 0) ↔ P.mulVec x = 0 := by
  have hσ := conj_conj hcm
  obtain ⟨v₀, v₁, a, b, ha, hb, h1, h2, h3, h4, h5⟩ :=
    exists_orth hσ hJ.1 (fun x hx => exists_of_conj_eq hcm hx) hd
  set A := algebraMap F E a with hAd
  set B := algebraMap F E b with hBd
  have hA : A ≠ 0 := by rw [hAd]; exact (map_ne_zero _).2 ha
  have hB : B ≠ 0 := by rw [hBd]; exact (map_ne_zero _).2 hb
  have hσA : σ A = A := σ.commutes a
  have hσB : σ B = B := σ.commutes b
  let V : Matrix (Fin M) (Fin 2) E := fun i k => ![v₀ i, v₁ i] k
  let P : Matrix (Fin 2) (Fin M) E := fun k j => ![A⁻¹ * rowJ σ J v₀ j, B⁻¹ * rowJ σ J v₁ j] k
  have hK : J2 E (-b / a) = !![1, 0; 0, B / A] := by
    simp [J2, map_div₀, map_neg, hAd, hBd, neg_div]
  refine ⟨-b / a, A, V, P, div_ne_zero (neg_ne_zero.2 hb) ha, hA, ⟨?_, ?_, ?_⟩, fun x => (h5 x).trans ?_⟩
  · rw [Matrix.one_fin_two]
    refine Matrix.ext fun k l => ?_
    rw [Matrix.mul_apply]
    fin_cases k <;> fin_cases l
    · change ∑ j, (A⁻¹ * rowJ σ J v₀ j) * v₀ j = 1
      rw [sum_row, h1, inv_mul_cancel₀ hA]
    · change ∑ j, (A⁻¹ * rowJ σ J v₀ j) * v₁ j = 0
      rw [sum_row, h3, mul_zero]
    · change ∑ j, (B⁻¹ * rowJ σ J v₁ j) * v₀ j = 0
      rw [sum_row, h4, mul_zero]
    · change ∑ j, (B⁻¹ * rowJ σ J v₁ j) * v₁ j = 1
      rw [sum_row, h2, inv_mul_cancel₀ hB]
  · rw [hK]
    refine Matrix.ext fun i k => ?_
    rw [Matrix.smul_apply, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases k
    · change ∑ j, J i j * v₀ j = A • (σ (A⁻¹ * rowJ σ J v₀ i) * 1 + σ (B⁻¹ * rowJ σ J v₁ i) * 0)
      simp only [map_mul, map_inv₀, RingHom.coe_coe, hσA, conj_row hσ hJ.1, smul_eq_mul]
      field_simp
      simp
    · change ∑ j, J i j * v₁ j = A • (σ (A⁻¹ * rowJ σ J v₀ i) * 0 + σ (B⁻¹ * rowJ σ J v₁ i) * (B / A))
      simp only [map_mul, map_inv₀, hσB, conj_row hσ hJ.1, smul_eq_mul]
      field_simp
      simp
  · rw [hK]
    refine Matrix.ext fun k j => ?_
    rw [Matrix.smul_apply, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases k
    · change ∑ i, σ (v₀ i) * J i j = A • (1 * (A⁻¹ * rowJ σ J v₀ j) + 0 * (B⁻¹ * rowJ σ J v₁ j))
      change rowJ σ J v₀ j = _
      simp only [smul_eq_mul]
      field_simp
      simp
    · change ∑ i, σ (v₁ i) * J i j = A • (0 * (A⁻¹ * rowJ σ J v₀ j) + (B / A) * (B⁻¹ * rowJ σ J v₁ j))
      change rowJ σ J v₁ j = _
      simp only [smul_eq_mul]
      field_simp
      simp
  · have e0 : P.mulVec x 0 = A⁻¹ * hf σ J v₀ x := sum_row _ _ _
    have e1 : P.mulVec x 1 = B⁻¹ * hf σ J v₁ x := sum_row _ _ _
    constructor
    · rintro ⟨g0, g1⟩
      funext k
      fin_cases k
      · change P.mulVec x 0 = 0
        rw [e0, g0, mul_zero]
      · change P.mulVec x 1 = 0
        rw [e1, g1, mul_zero]
    · intro g
      have g0 := congrFun g 0
      have g1 := congrFun g 1
      rw [e0] at g0
      rw [e1] at g1
      exact ⟨by simpa [hA] using g0, by simpa [hB] using g1⟩

end Frame

end GlobalTheory.CompanionTheory.PlaneSA.OfTwo

end
