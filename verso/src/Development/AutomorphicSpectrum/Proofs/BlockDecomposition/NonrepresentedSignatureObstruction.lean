import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBlockNFZeroOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfMulUnimodular
import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongrOfSignatureOfAdelicNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFromBlocks
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAuxiliaryHyperbolicVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignCompatibleNumberingOfWittTowerLower
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMultTOfEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseRangeRealEmbeddings
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCS
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureExists
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Hasse
open Matrix NumberField

/- English proof (translation)
Take `⟨c, Q, hQ⟩` from `Formalism.UG.P.sig_data _ _ _ h`. Use `GlobalTheory.FrameComplement.hasSignature_of_frame c (Q.map (starRingEnd ℂ)) ?_` and prove the remaining obligations. Establish `e1 : (Q.map (starRingEnd ℂ))ᴴ * J.map (starRingEnd ℂ) * Q.map (starRingEnd ℂ) = (Qᴴ * J * Q).map (starRingEnd ℂ)`. Rewrite using `[Matrix.map_mul (f := starRingEnd ℂ), Matrix.map_mul (f := starRingEnd ℂ)]`. Use `congr 2`.

Rewrite using `[e1, hQ]`. Apply the tactic sequence `ext (a | a) (b | b) <;> simp [Formalism.UG.Jpq, Matrix.one_apply, apply_ite (starRingEnd ℂ)]`.
-/
theorem hasSignature_map_conj {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ} {p q : ℕ}
    (h : Formalism.UG.HasSignature J p q) : Formalism.UG.HasSignature (J.map (starRingEnd ℂ)) p q := by
  obtain ⟨c, Q, hQ⟩ := Formalism.UG.P.sig_data _ _ _ h
  refine GlobalTheory.FrameComplement.hasSignature_of_frame c (Q.map (starRingEnd ℂ)) ?_
  have e1 : (Q.map (starRingEnd ℂ))ᴴ * J.map (starRingEnd ℂ) * Q.map (starRingEnd ℂ) =
      (Qᴴ * J * Q).map (starRingEnd ℂ) := by
    rw [Matrix.map_mul (f := starRingEnd ℂ), Matrix.map_mul (f := starRingEnd ℂ)]
    congr 2
  rw [e1, hQ]
  ext (a | a) (b | b) <;> simp [Formalism.UG.Jpq, Matrix.one_apply, apply_ite (starRingEnd ℂ)]

/- English proof (translation)
Set `e : Fin P ⊕ Fin N ≃ Fin n` to `finSumFinEquiv.trans (finCongr h)`. Set `s : Fin n → ℝ` to `fun i => (√|c i|)⁻¹`. Establish `hs : ∀ i, s i * c i * s i = if (i : ℕ) < P then 1 else -1` using `fun i => by`. Establish `h0 : c i ≠ 0`. Break down `lt_or_ge (i : ℕ) P with h | h` into its components or cases.

Conclude with `((hc i).1 h).ne'`. Conclude with `((hc i).2 h).ne`. Establish `hp : 0 < |c i|` using `abs_pos.2 h0`. Establish `hq : √|c i| * √|c i| = |c i|` using `Real.mul_self_sqrt hp.le`. Establish `hq0 : √|c i| ≠ 0` using `(Real.sqrt_pos.2 hp).ne'`.

Use `split_ifs with hi`. Establish `hh` using `(hc i).1 hi`. Rewrite `hq`, `hq0` using `[abs_of_pos hh]`. Simplify using `only [s, abs_of_pos hh]`. Clear the denominators using the available nonvanishing facts.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hh` using `(hc i).2 (not_lt.1 hi)`. Rewrite `hq`, `hq0` using `[abs_of_neg hh]`. Simplify using `only [s, abs_of_neg hh]`. Clear the denominators using the available nonvanishing facts.

Combine the linear equalities and inequalities to obtain the conclusion. Use `GlobalTheory.FrameComplement.hasSignature_of_frame (by simp [h]) ((Matrix.diagonal fun i => (s i : ℂ)).submatrix id e) ?_` and prove the remaining obligations. Establish `e1 : ((Matrix.diagonal fun i => (s i : ℂ)).submatrix id e)ᴴ * (Matrix.diagonal fun i => (c i : ℂ)) * (Matrix.diagonal fun i => (s i : ℂ)).submatrix id e = (Matrix.diagonal fun i : Fin n => (((if (i : ℕ) < P then 1 else -1 : ℝ)) : ℂ)).submatrix e e`. Establish `e2 : ((Matrix.diagonal fun i => (s i : ℂ)).submatrix id e)ᴴ * (Matrix.diagonal fun i => (c i : ℂ)) * (Matrix.diagonal fun i => (s i : ℂ)).submatrix id e = ((Matrix.diagonal fun i => (s i : ℂ))ᴴ * (Matrix.diagonal fun i => (c i : ℂ)) * (Matrix.diagonal fun i => (s i : ℂ))).submatr …`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations.

Simplify using `only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply, id]`. Rewrite using `[e2, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Rewrite using `[← hs i]`.

Simplify using the standard rewrite rules. Rewrite using `[e1]`. Establish `hl : ∀ a : Fin P, ((e (Sum.inl a) : Fin n) : ℕ) = a` using `fun a => by simp [e]`. Establish `hr : ∀ a : Fin N, ((e (Sum.inr a) : Fin n) : ℕ) = P + a` using `fun a => by simp [e]`. Apply the tactic sequence `ext (a | a) (b | b) <;> simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply, hl, hr, Fin.ext_iff] <;> split_ifs <;> simp`.
-/
theorem hasSignature_diagonal {n P N : ℕ} (c : Fin n → ℝ) (h : P + N = n)
    (hc : ∀ i : Fin n, ((i : ℕ) < P → 0 < c i) ∧ (P ≤ (i : ℕ) → c i < 0)) :
    Formalism.UG.HasSignature (Matrix.diagonal fun i => (c i : ℂ)) P N := by
  let e : Fin P ⊕ Fin N ≃ Fin n := finSumFinEquiv.trans (finCongr h)
  let s : Fin n → ℝ := fun i => (√|c i|)⁻¹
  have hs : ∀ i, s i * c i * s i = if (i : ℕ) < P then 1 else -1 := fun i => by
    have h0 : c i ≠ 0 := by
      rcases lt_or_ge (i : ℕ) P with h | h
      · exact ((hc i).1 h).ne'
      · exact ((hc i).2 h).ne
    have hp : 0 < |c i| := abs_pos.2 h0
    have hq : √|c i| * √|c i| = |c i| := Real.mul_self_sqrt hp.le
    have hq0 : √|c i| ≠ 0 := (Real.sqrt_pos.2 hp).ne'
    split_ifs with hi
    · have hh := (hc i).1 hi
      rw [abs_of_pos hh] at hq hq0
      simp only [s, abs_of_pos hh]
      field_simp
      linarith
    · have hh := (hc i).2 (not_lt.1 hi)
      rw [abs_of_neg hh] at hq hq0
      simp only [s, abs_of_neg hh]
      field_simp
      linarith
  refine GlobalTheory.FrameComplement.hasSignature_of_frame (by simp [h])
    ((Matrix.diagonal fun i => (s i : ℂ)).submatrix id e) ?_
  have e1 : ((Matrix.diagonal fun i => (s i : ℂ)).submatrix id e)ᴴ * (Matrix.diagonal fun i => (c i : ℂ)) *
      (Matrix.diagonal fun i => (s i : ℂ)).submatrix id e =
      (Matrix.diagonal fun i : Fin n => (((if (i : ℕ) < P then 1 else -1 : ℝ)) : ℂ)).submatrix e e := by
    have e2 : ((Matrix.diagonal fun i => (s i : ℂ)).submatrix id e)ᴴ * (Matrix.diagonal fun i => (c i : ℂ)) *
        (Matrix.diagonal fun i => (s i : ℂ)).submatrix id e =
        ((Matrix.diagonal fun i => (s i : ℂ))ᴴ * (Matrix.diagonal fun i => (c i : ℂ)) *
        (Matrix.diagonal fun i => (s i : ℂ))).submatrix e e := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply, id]
    rw [e2, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 2
    funext i
    rw [← hs i]
    simp
  rw [e1]
  have hl : ∀ a : Fin P, ((e (Sum.inl a) : Fin n) : ℕ) = a := fun a => by simp [e]
  have hr : ∀ a : Fin N, ((e (Sum.inr a) : Fin n) : ℕ) = P + a := fun a => by simp [e]
  ext (a | a) (b | b) <;> simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply, hl, hr, Fin.ext_iff] <;>
    split_ifs <;> simp

/- English proof (translation)
Use `haveI : Finite (F →+* ℝ) := Finite.of_injective (fun σ => Complex.ofRealHom.comp σ) (fun σ τ h => by`. Use extensionality with `x`. Use `congrArg (fun g : F →+* ℂ => g x) h` as an intermediate fact. Simplify using `using this)`. Establish `hd` using `GlobalTheory.Shintani.denseRange_realEmbeddings F`.

Establish `key : ∀ i : Fin n, ∃ x : F, ∀ σ : F →+* ℝ, ((i : ℕ) < P σ → 0 < σ x) ∧ (P σ ≤ (i : ℕ) → σ x < 0)`. Introduce `i`. Set `U : (F →+* ℝ) → Set ℝ` to `fun σ => if (i : ℕ) < P σ then Set.Ioi 0 else Set.Iio 0`. Establish `hU : IsOpen (Set.pi Set.univ U)` using `isOpen_set_pi Set.finite_univ fun σ _ => by`. Simplify using `only [U]`.

Use `split_ifs`. Conclude with `isOpen_Ioi`. Conclude with `isOpen_Iio`. Establish `hne : (Set.pi Set.univ U).Nonempty` using `⟨fun σ => if (i : ℕ) < P σ then 1 else -1, fun σ _ => by`. Simplify using `only [U]`.

Apply the tactic sequence `split_ifs <;> simp⟩`. Take `⟨x, hx⟩` from `hd.exists_mem_open hU hne`. Use `⟨x, fun σ => ?_⟩` and prove the remaining obligations. Use `hx σ (Set.mem_univ _)` as an intermediate fact. Simplify using `only [U] at this`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Simplify `this` using `[h]`. Introduce `h`. Simplify `this` using `[not_lt.2 h]`.

Use `choose a ha using key`. Conclude with `⟨a, fun σ i => ha i σ⟩`.
-/
theorem exists_signs (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (n : ℕ) (P : (F →+* ℝ) → ℕ) :
    ∃ a : Fin n → F, ∀ (σ : F →+* ℝ) (i : Fin n),
      ((i : ℕ) < P σ → 0 < σ (a i)) ∧ (P σ ≤ (i : ℕ) → σ (a i) < 0) := by
  haveI : Finite (F →+* ℝ) := Finite.of_injective (fun σ => Complex.ofRealHom.comp σ) (fun σ τ h => by
    ext x
    have := congrArg (fun g : F →+* ℂ => g x) h
    simpa using this)
  have hd := GlobalTheory.Shintani.denseRange_realEmbeddings F
  have key : ∀ i : Fin n, ∃ x : F, ∀ σ : F →+* ℝ, ((i : ℕ) < P σ → 0 < σ x) ∧ (P σ ≤ (i : ℕ) → σ x < 0) := by
    intro i
    let U : (F →+* ℝ) → Set ℝ := fun σ => if (i : ℕ) < P σ then Set.Ioi 0 else Set.Iio 0
    have hU : IsOpen (Set.pi Set.univ U) := isOpen_set_pi Set.finite_univ fun σ _ => by
      simp only [U]
      split_ifs
      · exact isOpen_Ioi
      · exact isOpen_Iio
    have hne : (Set.pi Set.univ U).Nonempty := ⟨fun σ => if (i : ℕ) < P σ then 1 else -1, fun σ _ => by
      simp only [U]
      split_ifs <;> simp⟩
    obtain ⟨x, hx⟩ := hd.exists_mem_open hU hne
    refine ⟨x, fun σ => ?_⟩
    have := hx σ (Set.mem_univ _)
    simp only [U] at this
    constructor
    · intro h
      simpa [h] using this
    · intro h
      simpa [not_lt.2 h] using this
  choose a ha using key
  exact ⟨a, fun σ i => ha i σ⟩

/- English proof (translation)
Use `haveI := cm.totReal`. Establish `hr : ComplexEmbedding.IsReal (τ.comp (algebraMap F E))` using `InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)`. Conclude with `⟨hr.embedding, fun x => (hr.coe_embedding_apply x).symm⟩`.
-/
theorem exists_real_restrict {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (cm : CMData F E) (τ : E →+* ℂ) :
    ∃ σ : F →+* ℝ, ∀ x : F, τ (algebraMap F E x) = (σ x : ℂ) := by
  haveI := cm.totReal
  have hr : ComplexEmbedding.IsReal (τ.comp (algebraMap F E)) :=
    InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)
  exact ⟨hr.embedding, fun x => (hr.coe_embedding_apply x).symm⟩

/- English proof (translation)
Use `haveI := cm.totReal`. Use `haveI := cm.cmUnram.1`. Use `haveI : Algebra.IsQuadraticExtension F E := ⟨cm.deg2⟩`. Use `haveI : IsCMField E := IsCMField.ofCMExtension F E`. Establish `hst : ∀ (φ : E →+* ℂ) x, φ (star x) = starRingEnd ℂ (φ x)` using `cm.cmUnram.2.1`.

Establish `hcc : ∀ x : E, ReciprocityTheory.ChartRestriction.G.FD.cc x = star x` using `fun x => by`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Conclude with `τ.injective ((GlobalTheory.Published.embedding_cc τ x).trans (hst τ x).symm)`. Take `⟨θ, h0, hθ⟩` from `GlobalTheory.Published.exists_cc_eq_neg E`. Rewrite `hθ` using `[hcc]`.

Establish `hfix : ∀ x : E, star x = x → τ' x = τ x` using `fun x hx => by`. Take `⟨a, rfl⟩` from `(cm.fixed x).1 hx`. Conclude with `h a`. Establish `h2 : (2 : E) ≠ 0` using `two_ne_zero`. Establish `hdec : ∀ x : E, ∃ u v : E, star u = u ∧ star v = v ∧ x = u + v * θ` using `fun x => by`.

Use `⟨(x + star x) / 2, (x - star x) / (2 * θ), ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[star_div₀, add_comm]`. Rewrite using `[star_div₀, star_sub, star_star, star_mul', hθ]`. Simplify using `only [star_ofNat]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hsq : τ' θ * τ' θ = τ θ * τ θ`. Establish `: star (θ * θ) = θ * θ` using `by rw [star_mul', hθ]; ring`.

Use `hfix _ this` as an intermediate fact. Simplify using `using this`. Establish `hf : (τ' θ - τ θ) * (τ' θ + τ θ) = 0` using `by linear_combination hsq`. Break down `mul_eq_zero.1 hf with h3 | h3` into its components or cases. Use `left`.

Use extensionality with `x`. Take `⟨u, v, hu, hv, rfl⟩` from `hdec x`. Simplify using `only [map_add, map_mul, hfix u hu, hfix v hv, sub_eq_zero.1 h3]`. Use `right`. Establish `hθ' : τ' θ = starRingEnd ℂ (τ θ)`.

Rewrite using `[← hst, hθ, map_neg]`. Take the linear combination `h3`. Establish `hc : ∀ w : E, star w = w → starRingEnd ℂ (τ w) = τ w` using `fun w hw => by rw [← hst, hw]`. Use extensionality with `x`. Take `⟨u, v, hu, hv, rfl⟩` from `hdec x`.

Simplify using `only [RingHom.comp_apply, map_add, map_mul, hfix u hu, hfix v hv, hc u hu, hc v hv, hθ']`.
-/
theorem eq_or_conj_of_restrict {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (cm : CMData F E) (τ τ' : E →+* ℂ)
    (h : ∀ x : F, τ' (algebraMap F E x) = τ (algebraMap F E x)) :
    τ' = τ ∨ τ' = (starRingEnd ℂ).comp τ := by
  haveI := cm.totReal
  haveI := cm.cmUnram.1
  haveI : Algebra.IsQuadraticExtension F E := ⟨cm.deg2⟩
  haveI : IsCMField E := IsCMField.ofCMExtension F E
  have hst : ∀ (φ : E →+* ℂ) x, φ (star x) = starRingEnd ℂ (φ x) := cm.cmUnram.2.1
  have hcc : ∀ x : E, ReciprocityTheory.ChartRestriction.G.FD.cc x = star x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective ((GlobalTheory.Published.embedding_cc τ x).trans (hst τ x).symm)
  obtain ⟨θ, h0, hθ⟩ := GlobalTheory.Published.exists_cc_eq_neg E
  rw [hcc] at hθ
  have hfix : ∀ x : E, star x = x → τ' x = τ x := fun x hx => by
    obtain ⟨a, rfl⟩ := (cm.fixed x).1 hx
    exact h a
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  have hdec : ∀ x : E, ∃ u v : E, star u = u ∧ star v = v ∧ x = u + v * θ := fun x => by
    refine ⟨(x + star x) / 2, (x - star x) / (2 * θ), ?_, ?_, ?_⟩
    · simp [star_div₀, add_comm]
    · rw [star_div₀, star_sub, star_star, star_mul', hθ]
      simp only [star_ofNat]
      field_simp
      ring
    · field_simp
      ring
  have hsq : τ' θ * τ' θ = τ θ * τ θ := by
    have : star (θ * θ) = θ * θ := by rw [star_mul', hθ]; ring
    have := hfix _ this
    simpa using this
  have hf : (τ' θ - τ θ) * (τ' θ + τ θ) = 0 := by linear_combination hsq
  rcases mul_eq_zero.1 hf with h3 | h3
  · left
    ext x
    obtain ⟨u, v, hu, hv, rfl⟩ := hdec x
    simp only [map_add, map_mul, hfix u hu, hfix v hv, sub_eq_zero.1 h3]
  · right
    have hθ' : τ' θ = starRingEnd ℂ (τ θ) := by
      rw [← hst, hθ, map_neg]
      linear_combination h3
    have hc : ∀ w : E, star w = w → starRingEnd ℂ (τ w) = τ w := fun w hw => by rw [← hst, hw]
    ext x
    obtain ⟨u, v, hu, hv, rfl⟩ := hdec x
    simp only [RingHom.comp_apply, map_add, map_mul, hfix u hu, hfix v hv, hc u hu, hc v hv, hθ']

/- English proof (translation)
Set `g : Fin t ⊕ Fin k → Fin t ⊕ ((Fin k ⊕ Fin k) ⊕ Fin n)` to `Sum.elim Sum.inl (fun j => Sum.inr (Sum.inl (Sum.inl j)))`. Establish `hg : Function.Injective g`. Apply the tactic sequence `rintro (a | a) (b | b) hab <;> simp_all [g]`. Set `c : Fin t ⊕ Fin k → Fin m` to `fun i => e.symm (g i)`. Use `⟨P.submatrix id c, le_antisymm ?_ ?_, ?_⟩` and prove the remaining obligations.

Simplify using `using Matrix.rank_le_card_width (P.submatrix id c)`. Establish `hu : IsUnit P.det` using `isUnit_iff_ne_zero.2 hP`. Establish `h1 : (P⁻¹).submatrix c id * P.submatrix id c = 1`. Establish `: (P⁻¹).submatrix c id * P.submatrix id c = (P⁻¹ * P).submatrix c c`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations.

Simplify using `only [Matrix.mul_apply, Matrix.submatrix_apply, id]`. Rewrite using `[this, Matrix.nonsing_inv_mul _ hu]`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Establish `hc : Function.Injective c` using `e.symm.injective.comp hg`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply, hij, hc.ne hij]`. Establish `h2` using `Matrix.rank_mul_le_right ((P⁻¹).submatrix c id) (P.submatrix id c)`. Rewrite `h2` using `[h1, Matrix.rank_one]`.

Simplify using `using h2`. Establish `: (P.submatrix id c)ᴴ * G * P.submatrix id c = (Pᴴ * G * P).submatrix c c`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply, id]`. Rewrite using `[this, h]`.

Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;> simp [c, g]`.
-/
theorem frame_of_congr {E : Type} [Field E] [StarRing E] {m t k n : ℕ} (G P : Matrix (Fin m) (Fin m) E)
    (hP : P.det ≠ 0) (e : Fin m ≃ Fin t ⊕ ((Fin k ⊕ Fin k) ⊕ Fin n)) (B : Matrix (Fin t) (Fin t) E)
    (A : Matrix (Fin n) (Fin n) E)
    (h : Pᴴ * G * P = (fromBlocks B 0 0 (fromBlocks (fromBlocks 0 1 1 0) 0 0 A)).submatrix e e) :
    ∃ x : Matrix (Fin m) (Fin t ⊕ Fin k) E, x.rank = t + k ∧ xᴴ * G * x = fromBlocks B 0 0 0 := by
  let g : Fin t ⊕ Fin k → Fin t ⊕ ((Fin k ⊕ Fin k) ⊕ Fin n) :=
    Sum.elim Sum.inl (fun j => Sum.inr (Sum.inl (Sum.inl j)))
  have hg : Function.Injective g := by
    rintro (a | a) (b | b) hab <;> simp_all [g]
  let c : Fin t ⊕ Fin k → Fin m := fun i => e.symm (g i)
  refine ⟨P.submatrix id c, le_antisymm ?_ ?_, ?_⟩
  · simpa using Matrix.rank_le_card_width (P.submatrix id c)
  · have hu : IsUnit P.det := isUnit_iff_ne_zero.2 hP
    have h1 : (P⁻¹).submatrix c id * P.submatrix id c = 1 := by
      have : (P⁻¹).submatrix c id * P.submatrix id c = (P⁻¹ * P).submatrix c c := by
        refine Matrix.ext fun i j => ?_
        simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
      rw [this, Matrix.nonsing_inv_mul _ hu]
      refine Matrix.ext fun i j => ?_
      have hc : Function.Injective c := e.symm.injective.comp hg
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.one_apply, hij, hc.ne hij]
    have h2 := Matrix.rank_mul_le_right ((P⁻¹).submatrix c id) (P.submatrix id c)
    rw [h1, Matrix.rank_one] at h2
    simpa using h2
  · have : (P.submatrix id c)ᴴ * G * P.submatrix id c = (Pᴴ * G * P).submatrix c c := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply, id]
    rw [this, h]
    refine Matrix.ext fun i j => ?_
    rcases i with i | i <;> rcases j with j | j <;> simp [c, g]

/- English proof (translation)
Use `set f : Fin t ⊕ Fin (r - t) ≃ Fin r := finSumFinEquiv.trans (finCongr htk) with hf`. Establish `h1 : ∀ a : Fin t, f (Sum.inl a) = Fin.castLE ht.le a` using `fun a => by`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `[hf]`. Establish `h2 : ∀ a : Fin (r - t), t ≤ (f (Sum.inr a)).1` using `fun a => by`.

Simplify using `[hf]`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Take `⟨a, rfl⟩` from `f.surjective a`. Take `⟨b, rfl⟩` from `f.surjective b`. Rewrite using `[Matrix.submatrix_apply, f.symm_apply_apply, f.symm_apply_apply]`.

Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b`. Simplify using `[h1]`. Simplify using `[hz _ _ (Or.inr (h2 b))]`. Simplify using `[hz _ _ (Or.inl (h2 a))]`. Simplify using `[hz _ _ (Or.inl (h2 a))]`.
-/
theorem block_submatrix {E : Type} [Field E] {r t : ℕ} (ht : t < r) (β : Matrix (Fin r) (Fin r) E)
    (hz : ∀ i j : Fin r, (t ≤ i.1 ∨ t ≤ j.1) → β i j = 0) (htk : t + (r - t) = r) :
    (fromBlocks (β.submatrix (Fin.castLE ht.le) (Fin.castLE ht.le)) 0 0 0 :
      Matrix (Fin t ⊕ Fin (r - t)) (Fin t ⊕ Fin (r - t)) E).submatrix
        (finSumFinEquiv.trans (finCongr htk)).symm (finSumFinEquiv.trans (finCongr htk)).symm = β := by
  set f : Fin t ⊕ Fin (r - t) ≃ Fin r := finSumFinEquiv.trans (finCongr htk) with hf
  have h1 : ∀ a : Fin t, f (Sum.inl a) = Fin.castLE ht.le a := fun a => by
    apply Fin.ext; simp [hf]
  have h2 : ∀ a : Fin (r - t), t ≤ (f (Sum.inr a)).1 := fun a => by
    simp [hf]
  refine Matrix.ext fun a b => ?_
  obtain ⟨a, rfl⟩ := f.surjective a
  obtain ⟨b, rfl⟩ := f.surjective b
  rw [Matrix.submatrix_apply, f.symm_apply_apply, f.symm_apply_apply]
  rcases a with a | a <;> rcases b with b | b
  · simp [h1]
  · simp [hz _ _ (Or.inr (h2 b))]
  · simp [hz _ _ (Or.inl (h2 a))]
  · simp [hz _ _ (Or.inl (h2 a))]

/- English proof (translation)
Establish `htk : t + (r - t) = r` using `by omega`. Establish `hZe` using `block_submatrix ht Z hZ htk`. Use `set f : Fin t ⊕ Fin (r - t) ≃ Fin r := finSumFinEquiv.trans (finCongr htk) with hf`. Use `set Zs := Z.submatrix (Fin.castLE ht.le) (Fin.castLE ht.le) with hZs`. Take `⟨-, Q, hQ⟩` from `Formalism.UG.P.sig_data _ _ _ hs`.

Set `Q₁ : Matrix (Fin t) (Fin p) ℂ` to `Q.submatrix id Sum.inl`. Establish `hQ1 : Q₁ᴴ * Zs * Q₁ = 1`. Establish `h1 : Q₁ᴴ * Zs * Q₁ = (Qᴴ * Zs * Q).submatrix Sum.inl Sum.inl`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [Q₁, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply, id]`.

Rewrite using `[h1, hQ]`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `[Formalism.UG.Jpq]`. Set `C : Matrix (Fin t ⊕ Fin (r - t)) (Fin p ⊕ Fin (r - t)) ℂ` to `fromBlocks Q₁ 0 0 1`. Set `A : Matrix (Fin r) (Fin p ⊕ Fin (r - t)) ℂ` to `C.submatrix f.symm id`.

Set `Lm : Matrix (Fin p ⊕ Fin (r - t)) (Fin t ⊕ Fin (r - t)) ℂ` to `fromBlocks (Q₁ᴴ * Zs) 0 0 1`. Establish `hLC : Lm * C = 1`. Simplify using `[Lm, C, fromBlocks_multiply, hQ1]`. Establish `hLA : Lm.submatrix id f.symm * A = 1`. Rewrite using `[show A = C.submatrix f.symm id from rfl, Matrix.submatrix_mul_equiv, hLC, Matrix.submatrix_id_id]`.

Establish `hA : Aᴴ * Z * A = fromBlocks 1 0 0 0`. Establish `h1 : Aᴴ * Z * A = Cᴴ * (fromBlocks Zs 0 0 0 : Matrix (Fin t ⊕ Fin (r - t)) (Fin t ⊕ Fin (r - t)) ℂ) * C`. Rewrite using `[← hZe]`. Simplify using `only [A]`. Rewrite using `[Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]`.

Rewrite using `[h1]`. Simplify using `[C, fromBlocks_conjTranspose, fromBlocks_multiply, hQ1]`. Establish `hinj : Function.Injective A.mulVecLin` using `fun v w hvw => by`. Establish `h1 : A *ᵥ v = A *ᵥ w` using `hvw`. Use `congrArg (fun u => (Lm.submatrix id f.symm) *ᵥ u) h1` as an intermediate fact.

Simplify `this` using `[Matrix.mulVec_mulVec, hLA]`. Use `⟨LinearMap.range A.mulVecLin, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨v, rfl⟩`. Establish `e1 : star (A *ᵥ v) ⬝ᵥ (Z *ᵥ (A *ᵥ v)) = star v ⬝ᵥ ((Aᴴ * Z * A) *ᵥ v)`. Rewrite using `[star_mulVec, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec, Matrix.mul_assoc]`.

Establish `e2 : star (A *ᵥ v) ⬝ᵥ (Z *ᵥ (A *ᵥ v)) = ∑ i, star (v (Sum.inl i)) * v (Sum.inl i)`. Rewrite using `[e1, hA]`. Simplify using `[fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type]`. Use `show 0 ≤ 1 * (star (A *ᵥ v) ⬝ᵥ (Z *ᵥ (A *ᵥ v))).re`. Rewrite using `[e2, one_mul, Complex.re_sum]`.

Use `Finset.sum_nonneg fun i _ => ?_` and prove the remaining obligations. Establish `hc : star (v (Sum.inl i)) * v (Sum.inl i) = ((Complex.normSq (v (Sum.inl i)) : ℝ) : ℂ)`. Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Both sides reduce to the same expression. Rewrite using `[hc, Complex.ofReal_re]`.

Conclude with `Complex.normSq_nonneg _`. Rewrite using `[LinearMap.finrank_range_of_inj hinj]`. Simplify using the standard rewrite rules.
-/
theorem exists_nonnegOn {r t : ℕ} (ht : t < r) (Z : Matrix (Fin r) (Fin r) ℂ)
    (hZ : ∀ i j : Fin r, (t ≤ i.1 ∨ t ≤ j.1) → Z i j = 0) {p q : ℕ}
    (hs : Formalism.UG.HasSignature (Z.submatrix (Fin.castLE ht.le) (Fin.castLE ht.le)) p q) :
    ∃ S : Submodule ℂ (Fin r → ℂ), NonnegOn 1 Z S ∧ Module.finrank ℂ S = p + (r - t) := by
  have htk : t + (r - t) = r := by omega
  have hZe := block_submatrix ht Z hZ htk
  set f : Fin t ⊕ Fin (r - t) ≃ Fin r := finSumFinEquiv.trans (finCongr htk) with hf
  set Zs := Z.submatrix (Fin.castLE ht.le) (Fin.castLE ht.le) with hZs
  obtain ⟨-, Q, hQ⟩ := Formalism.UG.P.sig_data _ _ _ hs
  let Q₁ : Matrix (Fin t) (Fin p) ℂ := Q.submatrix id Sum.inl
  have hQ1 : Q₁ᴴ * Zs * Q₁ = 1 := by
    have h1 : Q₁ᴴ * Zs * Q₁ = (Qᴴ * Zs * Q).submatrix Sum.inl Sum.inl := by
      refine Matrix.ext fun i j => ?_
      simp only [Q₁, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply, id]
    rw [h1, hQ]
    refine Matrix.ext fun i j => ?_
    simp [Formalism.UG.Jpq]
  let C : Matrix (Fin t ⊕ Fin (r - t)) (Fin p ⊕ Fin (r - t)) ℂ := fromBlocks Q₁ 0 0 1
  let A : Matrix (Fin r) (Fin p ⊕ Fin (r - t)) ℂ := C.submatrix f.symm id
  let Lm : Matrix (Fin p ⊕ Fin (r - t)) (Fin t ⊕ Fin (r - t)) ℂ := fromBlocks (Q₁ᴴ * Zs) 0 0 1
  have hLC : Lm * C = 1 := by
    simp [Lm, C, fromBlocks_multiply, hQ1]
  have hLA : Lm.submatrix id f.symm * A = 1 := by
    rw [show A = C.submatrix f.symm id from rfl, Matrix.submatrix_mul_equiv, hLC, Matrix.submatrix_id_id]
  have hA : Aᴴ * Z * A = fromBlocks 1 0 0 0 := by
    have h1 : Aᴴ * Z * A = Cᴴ * (fromBlocks Zs 0 0 0 : Matrix (Fin t ⊕ Fin (r - t)) (Fin t ⊕ Fin (r - t)) ℂ) * C := by
      rw [← hZe]
      simp only [A]
      rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
        Matrix.submatrix_id_id]
    rw [h1]
    simp [C, fromBlocks_conjTranspose, fromBlocks_multiply, hQ1]
  have hinj : Function.Injective A.mulVecLin := fun v w hvw => by
    have h1 : A *ᵥ v = A *ᵥ w := hvw
    have := congrArg (fun u => (Lm.submatrix id f.symm) *ᵥ u) h1
    simpa [Matrix.mulVec_mulVec, hLA] using this
  refine ⟨LinearMap.range A.mulVecLin, ?_, ?_⟩
  · rintro _ ⟨v, rfl⟩
    have e1 : star (A *ᵥ v) ⬝ᵥ (Z *ᵥ (A *ᵥ v)) = star v ⬝ᵥ ((Aᴴ * Z * A) *ᵥ v) := by
      rw [star_mulVec, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec, Matrix.mul_assoc]
    have e2 : star (A *ᵥ v) ⬝ᵥ (Z *ᵥ (A *ᵥ v)) = ∑ i, star (v (Sum.inl i)) * v (Sum.inl i) := by
      rw [e1, hA]
      simp [fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type]
    show 0 ≤ 1 * (star (A *ᵥ v) ⬝ᵥ (Z *ᵥ (A *ᵥ v))).re
    rw [e2, one_mul, Complex.re_sum]
    refine Finset.sum_nonneg fun i _ => ?_
    have hc : star (v (Sum.inl i)) * v (Sum.inl i) = ((Complex.normSq (v (Sum.inl i)) : ℝ) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]; rfl
    rw [hc, Complex.ofReal_re]
    exact Complex.normSq_nonneg _
  · rw [LinearMap.finrank_range_of_inj hinj]
    simp

/- English proof (translation)
Take `⟨c, Q, hQ⟩` from `Formalism.UG.P.sig_data _ _ _ hs`. Simplify using `only [Fintype.card_fin] at c`. Set `N : Matrix (Fin m) (Fin q) ℂ` to `Q.submatrix id Sum.inr`. Establish `hN : Nᴴ * G * N = -1`. Establish `h1 : Nᴴ * G * N = (Qᴴ * G * Q).submatrix Sum.inr Sum.inr`.

Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [N, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply, id]`. Rewrite using `[h1, hQ]`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `[Formalism.UG.Jpq]`.

Establish `hL : (-(Nᴴ * G)) * N = 1`. Rewrite using `[Matrix.neg_mul, hN, neg_neg]`. Establish `hinj : Function.Injective N.mulVecLin` using `fun v w hvw => by`. Establish `h1 : N *ᵥ v = N *ᵥ w` using `hvw`. Use `congrArg (fun u => (-(Nᴴ * G)) *ᵥ u) h1` as an intermediate fact.

Simplify `this` using `only [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec]`. Establish `hdis : Disjoint T (LinearMap.range N.mulVecLin)`. Rewrite using `[Submodule.disjoint_def]`. Introduce and unpack `x hx ⟨v, rfl⟩`. Assume the negation of the conclusion as `h0`.

Establish `h1` using `hT _ hx h0`. Establish `e1 : star (N *ᵥ v) ⬝ᵥ (G *ᵥ (N *ᵥ v)) = star v ⬝ᵥ ((Nᴴ * G * N) *ᵥ v)`. Rewrite using `[star_mulVec, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec, Matrix.mul_assoc]`. Establish `h2 : 0 < 1 * (star (N *ᵥ v) ⬝ᵥ (G *ᵥ (N *ᵥ v))).re` using `h1`. Rewrite `h2` using `[e1, hN, one_mul]`.

Simplify using `only [Matrix.neg_mulVec, Matrix.one_mulVec, dotProduct_neg, Complex.neg_re] at h2`. Establish `h3 : 0 ≤ (star v ⬝ᵥ v).re`. Rewrite using `[dotProduct, Complex.re_sum]`. Use `Finset.sum_nonneg fun i _ => ?_` and prove the remaining obligations. Establish `hc : star (v i) * v i = ((Complex.normSq (v i) : ℝ) : ℂ)`.

Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Both sides reduce to the same expression. Simplify using `only [Pi.star_apply]`. Rewrite using `[hc, Complex.ofReal_re]`. Conclude with `Complex.normSq_nonneg _`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `Submodule.finrank_add_finrank_le_of_disjoint hdis`. Rewrite `h1` using `[LinearMap.finrank_range_of_inj hinj]`. Simplify using `at h1`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_le_of_posOn {m p q : ℕ} (G : Matrix (Fin m) (Fin m) ℂ) (hs : Formalism.UG.HasSignature G p q)
    (T : Submodule ℂ (Fin m → ℂ)) (hT : PosOn 1 G T) : Module.finrank ℂ T ≤ p := by
  obtain ⟨c, Q, hQ⟩ := Formalism.UG.P.sig_data _ _ _ hs
  simp only [Fintype.card_fin] at c
  let N : Matrix (Fin m) (Fin q) ℂ := Q.submatrix id Sum.inr
  have hN : Nᴴ * G * N = -1 := by
    have h1 : Nᴴ * G * N = (Qᴴ * G * Q).submatrix Sum.inr Sum.inr := by
      refine Matrix.ext fun i j => ?_
      simp only [N, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply, id]
    rw [h1, hQ]
    refine Matrix.ext fun i j => ?_
    simp [Formalism.UG.Jpq]
  have hL : (-(Nᴴ * G)) * N = 1 := by
    rw [Matrix.neg_mul, hN, neg_neg]
  have hinj : Function.Injective N.mulVecLin := fun v w hvw => by
    have h1 : N *ᵥ v = N *ᵥ w := hvw
    have := congrArg (fun u => (-(Nᴴ * G)) *ᵥ u) h1
    simpa only [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec] using this
  have hdis : Disjoint T (LinearMap.range N.mulVecLin) := by
    rw [Submodule.disjoint_def]
    rintro x hx ⟨v, rfl⟩
    by_contra h0
    have h1 := hT _ hx h0
    have e1 : star (N *ᵥ v) ⬝ᵥ (G *ᵥ (N *ᵥ v)) = star v ⬝ᵥ ((Nᴴ * G * N) *ᵥ v) := by
      rw [star_mulVec, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec, Matrix.mul_assoc]
    have h2 : 0 < 1 * (star (N *ᵥ v) ⬝ᵥ (G *ᵥ (N *ᵥ v))).re := h1
    rw [e1, hN, one_mul] at h2
    simp only [Matrix.neg_mulVec, Matrix.one_mulVec, dotProduct_neg, Complex.neg_re] at h2
    have h3 : 0 ≤ (star v ⬝ᵥ v).re := by
      rw [dotProduct, Complex.re_sum]
      refine Finset.sum_nonneg fun i _ => ?_
      have hc : star (v i) * v i = ((Complex.normSq (v i) : ℝ) : ℂ) := by
        rw [Complex.normSq_eq_conj_mul_self]; rfl
      simp only [Pi.star_apply]
      rw [hc, Complex.ofReal_re]
      exact Complex.normSq_nonneg _
    linarith
  have h1 := Submodule.finrank_add_finrank_le_of_disjoint hdis
  rw [LinearMap.finrank_range_of_inj hinj] at h1
  simp at h1
  omega

/- English proof (translation)
Take `⟨c, Q, hQ⟩` from `Formalism.UG.P.sig_data _ _ _ h`. Set `s` to `Equiv.sumComm (Fin q) (Fin p)`. Use `GlobalTheory.FrameComplement.hasSignature_of_frame (by omega) (Q.submatrix id s) ?_` and prove the remaining obligations. Establish `e1 : (Q.submatrix id s)ᴴ * (-J) * Q.submatrix id s = -((Qᴴ * J * Q).submatrix s s)`. Use extensionality with `a b`.

Simplify using `[Matrix.mul_apply, Matrix.conjTranspose_apply]`. Rewrite using `[e1, hQ]`. Apply the tactic sequence `ext (a | a) (b | b) <;> simp [Formalism.UG.Jpq, s, Matrix.one_apply]`.
-/
theorem hasSig_neg {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ} {p q : ℕ}
    (h : Formalism.UG.HasSignature J p q) : Formalism.UG.HasSignature (-J) q p := by
  obtain ⟨c, Q, hQ⟩ := Formalism.UG.P.sig_data _ _ _ h
  let s := Equiv.sumComm (Fin q) (Fin p)
  refine GlobalTheory.FrameComplement.hasSignature_of_frame (by omega) (Q.submatrix id s) ?_
  have e1 : (Q.submatrix id s)ᴴ * (-J) * Q.submatrix id s = -((Qᴴ * J * Q).submatrix s s) := by
    ext a b
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [e1, hQ]
  ext (a | a) (b | b) <;> simp [Formalism.UG.Jpq, s, Matrix.one_apply]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Take `⟨S, hS, hd⟩` from `exists_nonnegOn ht Z hZ hB`. Take `⟨T, hT, hle⟩` from `hno 1 S (Or.inl rfl) hS`. Use `finrank_le_of_posOn G hG T hT` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Take `⟨S, hS, hd⟩` from `exists_nonnegOn ht (-Z) (fun i j h => by simp [hZ i j h]) (q := p₁) (p := q₁) (hasSig_neg hB)`. Establish `hS' : NonnegOn (-1) Z S` using `fun w hw => by`. Use `hS w hw` as an intermediate fact. Simplify `this` using `[Matrix.neg_mulVec]`. Take `⟨T, hT, hle⟩` from `hno (-1) S (Or.inr rfl) hS'`.

Establish `hT' : PosOn 1 (-G) T` using `fun w hw h0 => by`. Use `hT w hw h0` as an intermediate fact. Simplify `this` using `[Matrix.neg_mulVec]`. Use `finrank_le_of_posOn (-G) (hasSig_neg hG) T hT'` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem sig_bound {m r t : ℕ} (ht : t < r) (Z : Matrix (Fin r) (Fin r) ℂ)
    (hZ : ∀ i j : Fin r, (t ≤ i.1 ∨ t ≤ j.1) → Z i j = 0) (G : Matrix (Fin m) (Fin m) ℂ) {p₁ q₁ p q : ℕ}
    (hB : Formalism.UG.HasSignature (Z.submatrix (Fin.castLE ht.le) (Fin.castLE ht.le)) p₁ q₁)
    (hG : Formalism.UG.HasSignature G p q)
    (hno : ∀ (ε : ℝ) (S : Submodule ℂ (Fin r → ℂ)), (ε = 1 ∨ ε = -1) → NonnegOn ε Z S →
      ∃ T : Submodule ℂ (Fin m → ℂ), PosOn ε G T ∧ Module.finrank ℂ S ≤ Module.finrank ℂ T) :
    p₁ + (r - t) ≤ p ∧ q₁ + (r - t) ≤ q := by
  constructor
  · obtain ⟨S, hS, hd⟩ := exists_nonnegOn ht Z hZ hB
    obtain ⟨T, hT, hle⟩ := hno 1 S (Or.inl rfl) hS
    have := finrank_le_of_posOn G hG T hT
    omega
  · obtain ⟨S, hS, hd⟩ := exists_nonnegOn ht (-Z) (fun i j h => by simp [hZ i j h])
      (q := p₁) (p := q₁) (hasSig_neg hB)
    have hS' : NonnegOn (-1) Z S := fun w hw => by
      have := hS w hw
      simpa [Matrix.neg_mulVec] using this
    obtain ⟨T, hT, hle⟩ := hno (-1) S (Or.inr rfl) hS'
    have hT' : PosOn 1 (-G) T := fun w hw h0 => by
      have := hT w hw h0
      simpa [Matrix.neg_mulVec] using this
    have := finrank_le_of_posOn (-G) (hasSig_neg hG) T hT'
    omega

def blockM {F E : Type} [Field F] [Field E] [Algebra F E] {t k n : ℕ} (B : Matrix (Fin t) (Fin t) E)
    (a : Fin n → F) : Matrix (Fin t ⊕ ((Fin k ⊕ Fin k) ⊕ Fin n)) (Fin t ⊕ ((Fin k ⊕ Fin k) ⊕ Fin n)) E :=
  fromBlocks B 0 0 (fromBlocks (fromBlocks 0 1 1 0) 0 0 (diagonal fun i => algebraMap F E (a i)))

/- English proof (translation)
Apply the tactic sequence `ext (i | (i | i) | i) (j | (j | j) | j) <;>`. Simplify using `[blockM, Matrix.one_apply, Matrix.diagonal_apply, apply_ite τ, hσ]`.
-/
theorem blockM_map {F E : Type} [Field F] [Field E] [Algebra F E] {t k n : ℕ} (B : Matrix (Fin t) (Fin t) E)
    (a : Fin n → F) (τ : E →+* ℂ) (σ : F →+* ℝ) (hσ : ∀ x : F, τ (algebraMap F E x) = (σ x : ℂ)) :
    (blockM (k := k) B a).map τ = fromBlocks (B.map τ) 0 0 (fromBlocks (fromBlocks 0 1 1 0) 0 0
      (diagonal fun i => ((σ (a i) : ℝ) : ℂ))) := by
  ext (i | (i | i) | i) (j | (j | j) | j) <;>
    simp [blockM, Matrix.one_apply, Matrix.diagonal_apply, apply_ite τ, hσ]

/- English proof (translation)
Rewrite using `[blockM, det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁, det_diagonal, mul_assoc]`.
-/
theorem blockM_det {F E : Type} [Field F] [Field E] [Algebra F E] {t k n : ℕ} (B : Matrix (Fin t) (Fin t) E)
    (a : Fin n → F) : (blockM (k := k) B a).det =
      B.det * (fromBlocks 0 1 1 0 : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) E).det * ∏ i, algebraMap F E (a i) := by
  rw [blockM, det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁, det_diagonal, mul_assoc]

/- English proof (translation)
Establish `: (fromBlocks 0 1 1 0 : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) E) * (fromBlocks 0 1 1 0 : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) E) = 1`. Simplify using `[fromBlocks_multiply]`. Conclude with `(Matrix.isUnit_det_of_right_inverse this).ne_zero`.
-/
theorem hyp_det_ne {E : Type} [Field E] (k : ℕ) :
    (fromBlocks 0 1 1 0 : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) E).det ≠ 0 := by
  have : (fromBlocks 0 1 1 0 : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) E) *
      (fromBlocks 0 1 1 0 : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) E) = 1 := by
    simp [fromBlocks_multiply]
  exact (Matrix.isUnit_det_of_right_inverse this).ne_zero

/- English proof (translation)
Establish `hf : ∀ z : F, star (algebraMap F E z) = algebraMap F E z` using `fun z => (cm.fixed _).2 ⟨z, rfl⟩`. Simplify using `[blockM, fromBlocks_conjTranspose, hB, Matrix.diagonal_conjTranspose]`. Conclude with `fun i => hf _`.
-/
theorem blockM_herm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (cm : CMData F E) {t k n : ℕ} (B : Matrix (Fin t) (Fin t) E) (hB : Bᴴ = B) (a : Fin n → F) :
    (blockM (k := k) B a)ᴴ = blockM B a := by
  have hf : ∀ z : F, star (algebraMap F E z) = algebraMap F E z := fun z => (cm.fixed _).2 ⟨z, rfl⟩
  simp [blockM, fromBlocks_conjTranspose, hB, Matrix.diagonal_conjTranspose]
  exact fun i => hf _

/- English proof (translation)
Unfold `Formalism.UG.IsHerm`. Rewrite using `[Formalism.UG.P.cT_conj_eq]`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.conjTranspose_apply, Matrix.map_apply]`. Establish `: G i j = star (G j i)` using `by conv_lhs => rw [← hG]`.

Both sides reduce to the same expression. Rewrite using `[this, hτ]`. Both sides reduce to the same expression.
-/
theorem map_isHerm {E : Type} [Field E] [StarRing E] {n : Type} [Fintype n] [DecidableEq n] (G : Matrix n n E) (hG : Gᴴ = G)
    (τ : E →+* ℂ) (hτ : ∀ x, τ (star x) = starRingEnd ℂ (τ x)) : Formalism.UG.IsHerm (starRingEnd ℂ) (G.map τ) := by
  unfold Formalism.UG.IsHerm
  rw [Formalism.UG.P.cT_conj_eq]
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
  have : G i j = star (G j i) := by
    conv_lhs => rw [← hG]
    rfl
  rw [this, hτ]
  rfl

/- English proof (translation)
Rewrite using `[show (G.map τ).det = τ G.det from (RingHom.map_det τ G).symm]`. Conclude with `(isUnit_iff_ne_zero.2 hG).map _`.
-/
theorem map_isUnit_det {E : Type} [Field E] {n : Type} [Fintype n] [DecidableEq n] (G : Matrix n n E) (hG : G.det ≠ 0)
    (τ : E →+* ℂ) : IsUnit (G.map τ).det := by
  rw [show (G.map τ).det = τ G.det from (RingHom.map_det τ G).symm]
  exact (isUnit_iff_ne_zero.2 hG).map _

/- English proof (translation)
Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply, id]`.
-/
theorem gram_submatrix {E : Type} [Field E] [StarRing E] {m a b : Type} [Fintype m] [Fintype a] [Fintype b] [DecidableEq a]
    (G : Matrix m m E) (x : Matrix m a E) (f : b ≃ a) :
    (x.submatrix id f)ᴴ * G * x.submatrix id f = (xᴴ * G * x).submatrix f f := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply, id]

/- English proof (translation)
Use `haveI : Algebra.IsQuadraticExtension F E := ⟨cm.deg2⟩`. Conclude with `⟨ComplexEmbedding.lift E (Complex.ofRealHom.comp σ), fun x => ComplexEmbedding.lift_algebraMap_apply E _ x⟩`.
-/
theorem exists_lift {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (cm : CMData F E) (σ : F →+* ℝ) : ∃ τ : E →+* ℂ, ∀ x : F, τ (algebraMap F E x) = (σ x : ℂ) := by
  haveI : Algebra.IsQuadraticExtension F E := ⟨cm.deg2⟩
  exact ⟨ComplexEmbedding.lift E (Complex.ofRealHom.comp σ), fun x => ComplexEmbedding.lift_algebraMap_apply E _ x⟩

/- English proof (translation)
Use `haveI := cm.totReal`. Take `⟨n, hn⟩ : ∃ n, n = m - t - 2 * k` from `⟨_, rfl⟩`. Establish `hn0 : 0 < n` using `by omega`. Use `choose L hL using exists_lift cm`. Use `choose p₁ q₁ p q h1 h2 h3 h4 using fun σ => hs (L σ)`.

Establish `c1 : ∀ σ, t = p₁ σ + q₁ σ` using `fun σ => by simpa using (Formalism.UG.P.sig_data _ _ _ (h1 σ)).1`. Establish `c2 : ∀ σ, m = p σ + q σ` using `fun σ => by simpa using (Formalism.UG.P.sig_data _ _ _ (h2 σ)).1`. Set `P : (F →+* ℝ) → ℕ` to `fun σ => p σ - p₁ σ - k`. Establish `sigM : ∀ a : Fin n → F, (∀ (σ : F →+* ℝ) (i : Fin n), ((i : ℕ) < P σ → 0 < σ (a i)) ∧ (P σ ≤ (i : ℕ) → σ (a i) < 0)) → ∀ τ : E →+* ℂ, ∃ u v : ℕ, Formalism.UG.HasSignature (G.map τ) u v ∧ Formalism.UG.HasSignature ((blockM (k` using `k) B a).map τ) u v := by`. Introduce `a ha τ`.

Take `⟨σ, hσ⟩` from `exists_real_restrict cm τ`. Establish `key : Formalism.UG.HasSignature ((blockM (k` using `k) B a).map (L σ)) (p σ) (q σ) := by`. Establish `hc1` using `c1 σ`. Establish `hc2` using `c2 σ`. Establish `h3'` using `h3 σ`.

Establish `h4'` using `h4 σ`. Establish `d` using `hasSignature_diagonal (P := P σ) (N := q σ - q₁ σ - k) (fun i => σ (a i)) (by simp only [P]; omega) (ha σ)`. Use `GlobalTheory.FrameComplement.hasSignature_fromBlocks (h1 σ) (GlobalTheory.FrameComplement.hasSignature_fromBlocks (GlobalTheory.WittSign.hasSignature_hyperbolic k) d)` as an intermediate fact. Rewrite using `[blockM_map B a (L σ) σ (hL σ)]`. Rewrite `this` using `[show p₁ σ + (k + P σ) = p σ by simp only [P]; omega, show q₁ σ + (k + (q σ - q₁ σ - k)) = q σ by omega]`. Then use the resulting hypothesis.

Break down `eq_or_conj_of_restrict cm (L σ) τ (fun x => by rw [hσ, hL]) with rfl | rfl` into its components or cases. Conclude with `⟨_, _, h2 σ, key⟩`. Use `⟨p σ, q σ, ?_, ?_⟩` and prove the remaining obligations. Use `hasSignature_map_conj (h2 σ)` as an intermediate fact. Rewrite `this` using `[Matrix.map_map]`. Then use the resulting hypothesis.

Use `hasSignature_map_conj key` as an intermediate fact. Rewrite `this` using `[Matrix.map_map]`. Then use the resulting hypothesis. Take `⟨a, ha⟩` from `exists_signs F n P`. Take `⟨e⟩ : Nonempty (Fin m ≃ Fin t ⊕ ((Fin k ⊕ Fin k) ⊕ Fin n))` from `Fintype.card_eq.1 (by simp; omega)`. Take `⟨τ₀⟩ : Nonempty (E →+* ℂ)` from `inferInstance`.

Take `⟨σ₀, -⟩` from `exists_real_restrict cm τ₀`. Establish `ha0 : ∀ i, a i ≠ 0` using `fun i h0 => by`. Use `ha σ₀ i` as an intermediate fact. Rewrite `this` using `[h0, map_zero]`. Break down `lt_or_ge (i : ℕ) (P σ₀) with h | h` into its components or cases.

Conclude with `lt_irrefl _ (this.1 h)`. Conclude with `lt_irrefl _ (this.2 h)`. Establish `hMd : ∀ b : Fin n → F, (∀ i, b i ≠ 0) → ((blockM (k` using `k) B b).submatrix e e).det ≠ 0 := fun b hb => by`. Rewrite using `[det_submatrix_equiv_self, blockM_det]`. Use `mul_ne_zero (mul_ne_zero hBd (hyp_det_ne k)) (Finset.prod_ne_zero_iff.2 fun i _ => ?_)` and prove the remaining obligations.

Conclude with `(map_ne_zero _).2 (hb i)`. Establish `hMh : ∀ b : Fin n → F, ((blockM (k` using `k) B b).submatrix e e)ᴴ = (blockM (k := k) B b).submatrix e e := fun b => by rw [conjTranspose_submatrix, blockM_herm cm B hB]`. Establish `hsub : ∀ (b : Fin n → F) (τ : E →+* ℂ), ((blockM (k` using `k) B b).submatrix e e).map τ = ((blockM (k := k) B b).map τ).submatrix e e := fun _ _ => rfl`. Take `⟨c, hc⟩` from `(cm.fixed (G.det / ((blockM (k := k) B a).submatrix e e).det)).1 (by`. Rewrite using `[star_div₀, ← Matrix.det_conjTranspose, ← Matrix.det_conjTranspose, hG, hMh])`.

Establish `hcpos : ∀ σ : F →+* ℝ, 0 < σ c` using `fun σ => by`. Take `⟨u, v, hu, hv⟩` from `sigM a ha (L σ)`. Take `⟨Q, hQ, hQe⟩` from `GlobalTheory.HermAdelicNorm.congr_of_hasSignature hu (GlobalTheory.StandardGramVectors.hasSignature_submatrix hv e)`. Use `GlobalTheory.Published.Landherr.re_det_div_pos (G' := (blockM (k := k) B a).submatrix e e) hGd (L σ) ⟨Q, hQ, hQe⟩` as an intermediate fact. Rewrite `this` using `[← hc, hL]`.

Simplify using `using this`. Establish `hc0 : c ≠ 0` using `fun h => by`. Use `hcpos σ₀` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Conclude with `lt_irrefl _ this`.

Set `i₀ : Fin n` to `⟨0, hn0⟩`. Set `a' : Fin n → F` to `fun i => a i * (if i = i₀ then c else 1)`. Apply the tactic sequence `have ha'0 : ∀ i, a' i ≠ 0 := fun i => mul_ne_zero (ha0 i) (by split_ifs <;> simp [hc0])`. Establish `ha' : ∀ (σ : F →+* ℝ) (i : Fin n), ((i : ℕ) < P σ → 0 < σ (a' i)) ∧ (P σ ≤ (i : ℕ) → σ (a' i) < 0)`. Introduce `σ i`.

Establish `hp : 0 < σ (if i = i₀ then c else 1)` using `by split_ifs`. Conclude with `hcpos σ`. Simplify using the standard rewrite rules. Simplify using `only [a', map_mul]`. Conclude with `⟨fun h => mul_pos ((ha σ i).1 h) hp, fun h => mul_neg_of_neg_of_pos ((ha σ i).2 h) hp⟩`.

Establish `hdet : ((blockM (k` using `k) B a').submatrix e e).det = G.det := by`. Establish `h5` using `hMd a ha0`. Rewrite `h5`, the goal using `[det_submatrix_equiv_self]`. Establish `h6 : ∏ i, algebraMap F E (a' i) = (∏ i, algebraMap F E (a i)) * algebraMap F E c`. Simplify using `only [a', map_mul, Finset.prod_mul_distrib, apply_ite (algebraMap F E), map_one, Finset.prod_ite_eq', Finset.mem_univ, if_true]`.

Rewrite `*` using `[hc, det_submatrix_equiv_self]`. Rewrite using `[blockM_det, h6, ← mul_assoc, ← blockM_det, mul_div_cancel₀ _ h5]`. Take `⟨R, hR, hRe⟩` from `GlobalTheory.HermAdelicNorm.congr_of_signature_of_adelic_norm F E cm m G ((blockM (k := k) B a').submatrix e e) hG (hMh a') hGd (hMd a' ha'0) (fun τ => by`. Take `⟨u, v, hu, hv⟩` from `sigM a' ha' τ`. Conclude with `⟨u, v, hu, GlobalTheory.StandardGramVectors.hasSignature_submatrix hv e⟩)`.

Use the proof step `⟨1, by rw [hdet, div_self hGd]; simp⟩`. Conclude with `frame_of_congr G R hR e B _ hRe`.
-/
theorem exists_frame_of_sig {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (cm : CMData F E) {m t k : ℕ} (G : Matrix (Fin m) (Fin m) E) (B : Matrix (Fin t) (Fin t) E)
    (hG : Gᴴ = G) (hB : Bᴴ = B) (hGd : G.det ≠ 0) (hBd : B.det ≠ 0) (hm : t + 2 * k < m)
    (hs : ∀ τ : E →+* ℂ, ∃ p₁ q₁ p q : ℕ, Formalism.UG.HasSignature (B.map τ) p₁ q₁ ∧
      Formalism.UG.HasSignature (G.map τ) p q ∧ p₁ + k ≤ p ∧ q₁ + k ≤ q) :
    ∃ x : Matrix (Fin m) (Fin t ⊕ Fin k) E, x.rank = t + k ∧ xᴴ * G * x = fromBlocks B 0 0 0 := by
  classical
  haveI := cm.totReal
  obtain ⟨n, hn⟩ : ∃ n, n = m - t - 2 * k := ⟨_, rfl⟩
  have hn0 : 0 < n := by omega
  choose L hL using exists_lift cm
  choose p₁ q₁ p q h1 h2 h3 h4 using fun σ => hs (L σ)
  have c1 : ∀ σ, t = p₁ σ + q₁ σ := fun σ => by simpa using (Formalism.UG.P.sig_data _ _ _ (h1 σ)).1
  have c2 : ∀ σ, m = p σ + q σ := fun σ => by simpa using (Formalism.UG.P.sig_data _ _ _ (h2 σ)).1
  let P : (F →+* ℝ) → ℕ := fun σ => p σ - p₁ σ - k
  have sigM : ∀ a : Fin n → F, (∀ (σ : F →+* ℝ) (i : Fin n), ((i : ℕ) < P σ → 0 < σ (a i)) ∧ (P σ ≤ (i : ℕ) → σ (a i) < 0)) →
      ∀ τ : E →+* ℂ, ∃ u v : ℕ, Formalism.UG.HasSignature (G.map τ) u v ∧
        Formalism.UG.HasSignature ((blockM (k := k) B a).map τ) u v := by
    intro a ha τ
    obtain ⟨σ, hσ⟩ := exists_real_restrict cm τ
    have key : Formalism.UG.HasSignature ((blockM (k := k) B a).map (L σ)) (p σ) (q σ) := by
      have hc1 := c1 σ
      have hc2 := c2 σ
      have h3' := h3 σ
      have h4' := h4 σ
      have d := hasSignature_diagonal (P := P σ) (N := q σ - q₁ σ - k) (fun i => σ (a i))
        (by simp only [P]; omega) (ha σ)
      have := GlobalTheory.FrameComplement.hasSignature_fromBlocks (h1 σ)
        (GlobalTheory.FrameComplement.hasSignature_fromBlocks (GlobalTheory.WittSign.hasSignature_hyperbolic k) d)
      rw [blockM_map B a (L σ) σ (hL σ)]
      rwa [show p₁ σ + (k + P σ) = p σ by simp only [P]; omega,
        show q₁ σ + (k + (q σ - q₁ σ - k)) = q σ by omega] at this
    rcases eq_or_conj_of_restrict cm (L σ) τ (fun x => by rw [hσ, hL]) with rfl | rfl
    · exact ⟨_, _, h2 σ, key⟩
    · refine ⟨p σ, q σ, ?_, ?_⟩
      · have := hasSignature_map_conj (h2 σ)
        rwa [Matrix.map_map] at this
      · have := hasSignature_map_conj key
        rwa [Matrix.map_map] at this
  obtain ⟨a, ha⟩ := exists_signs F n P
  obtain ⟨e⟩ : Nonempty (Fin m ≃ Fin t ⊕ ((Fin k ⊕ Fin k) ⊕ Fin n)) :=
    Fintype.card_eq.1 (by simp; omega)
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨σ₀, -⟩ := exists_real_restrict cm τ₀
  have ha0 : ∀ i, a i ≠ 0 := fun i h0 => by
    have := ha σ₀ i
    rw [h0, map_zero] at this
    rcases lt_or_ge (i : ℕ) (P σ₀) with h | h
    · exact lt_irrefl _ (this.1 h)
    · exact lt_irrefl _ (this.2 h)
  have hMd : ∀ b : Fin n → F, (∀ i, b i ≠ 0) → ((blockM (k := k) B b).submatrix e e).det ≠ 0 := fun b hb => by
    rw [det_submatrix_equiv_self, blockM_det]
    refine mul_ne_zero (mul_ne_zero hBd (hyp_det_ne k)) (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
    exact (map_ne_zero _).2 (hb i)
  have hMh : ∀ b : Fin n → F, ((blockM (k := k) B b).submatrix e e)ᴴ = (blockM (k := k) B b).submatrix e e :=
    fun b => by rw [conjTranspose_submatrix, blockM_herm cm B hB]
  have hsub : ∀ (b : Fin n → F) (τ : E →+* ℂ), ((blockM (k := k) B b).submatrix e e).map τ =
      ((blockM (k := k) B b).map τ).submatrix e e := fun _ _ => rfl
  obtain ⟨c, hc⟩ := (cm.fixed (G.det / ((blockM (k := k) B a).submatrix e e).det)).1 (by
    rw [star_div₀, ← Matrix.det_conjTranspose, ← Matrix.det_conjTranspose, hG, hMh])
  have hcpos : ∀ σ : F →+* ℝ, 0 < σ c := fun σ => by
    obtain ⟨u, v, hu, hv⟩ := sigM a ha (L σ)
    obtain ⟨Q, hQ, hQe⟩ := GlobalTheory.HermAdelicNorm.congr_of_hasSignature hu
      (GlobalTheory.StandardGramVectors.hasSignature_submatrix hv e)
    have := GlobalTheory.Published.Landherr.re_det_div_pos (G' := (blockM (k := k) B a).submatrix e e) hGd (L σ) ⟨Q, hQ, hQe⟩
    rw [← hc, hL] at this
    simpa using this
  have hc0 : c ≠ 0 := fun h => by
    have := hcpos σ₀
    rw [h, map_zero] at this
    exact lt_irrefl _ this
  let i₀ : Fin n := ⟨0, hn0⟩
  let a' : Fin n → F := fun i => a i * (if i = i₀ then c else 1)
  have ha'0 : ∀ i, a' i ≠ 0 := fun i => mul_ne_zero (ha0 i) (by split_ifs <;> simp [hc0])
  have ha' : ∀ (σ : F →+* ℝ) (i : Fin n), ((i : ℕ) < P σ → 0 < σ (a' i)) ∧ (P σ ≤ (i : ℕ) → σ (a' i) < 0) := by
    intro σ i
    have hp : 0 < σ (if i = i₀ then c else 1) := by
      split_ifs
      · exact hcpos σ
      · simp
    simp only [a', map_mul]
    exact ⟨fun h => mul_pos ((ha σ i).1 h) hp, fun h => mul_neg_of_neg_of_pos ((ha σ i).2 h) hp⟩
  have hdet : ((blockM (k := k) B a').submatrix e e).det = G.det := by
    have h5 := hMd a ha0
    rw [det_submatrix_equiv_self] at h5 ⊢
    have h6 : ∏ i, algebraMap F E (a' i) = (∏ i, algebraMap F E (a i)) * algebraMap F E c := by
      simp only [a', map_mul, Finset.prod_mul_distrib, apply_ite (algebraMap F E), map_one,
        Finset.prod_ite_eq', Finset.mem_univ, if_true]
    rw [hc, det_submatrix_equiv_self] at *
    rw [blockM_det, h6, ← mul_assoc, ← blockM_det, mul_div_cancel₀ _ h5]
  obtain ⟨R, hR, hRe⟩ := GlobalTheory.HermAdelicNorm.congr_of_signature_of_adelic_norm F E cm m G
    ((blockM (k := k) B a').submatrix e e) hG (hMh a') hGd (hMd a' ha'0)
    (fun τ => by
      obtain ⟨u, v, hu, hv⟩ := sigM a' ha' τ
      exact ⟨u, v, hu, GlobalTheory.StandardGramVectors.hasSignature_submatrix hv e⟩)
    ⟨1, by rw [hdet, div_self hGd]; simp⟩
  exact frame_of_congr G R hR e B _ hRe

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Hasse

open GlobalTheory.CompanionTheory.WeilSiegel.NoFrame GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Hasse in

/- English proof (translation)
Introduce `D r V h2r t β hNF hno`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨ht, hz, hdet⟩` from `hNF`. Apply `hno` to reduce the goal to its premises.

Establish `hstar : ∀ x : D.host.E, D.sp.cm.sig x = star x` using `fun _ => rfl`. Establish `hβ : ∀ i j, star (β.1 j i) = β.1 i j` using `fun i j => by`. Use `congrFun (congrFun β.2 i) j` as an intermediate fact. Simplify `this` using `[hstar]`. Use `set B : Matrix (Fin t) (Fin t) D.host.E := β.1.submatrix (Fin.castLE ht.le) (Fin.castLE ht.le) with hBdef`.

Establish `hBh : Bᴴ = B` using `Matrix.ext fun i j => hβ _ _`. Establish `hGh : V.gramᴴ = V.gram` using `Matrix.ext fun a b => V.herm.eq _ _`. Establish `hGd : V.gram.det ≠ 0` using `GlobalTheory.FrameComplement.gram_det_ne V`. Establish `hplace : ∀ ρ : D.what₂.Tau, ∃ p₁ q₁ p q : ℕ, Formalism.UG.HasSignature (B.map (tauE D ρ)) p₁ q₁ ∧ Formalism.UG.HasSignature (V.gram.map (tauE D ρ)) p q ∧ p₁ + (r - t) ≤ p ∧ q₁ + (r - t) ≤ q`. Introduce `ρ`.

Establish `hτ : ∀ x, tauE D ρ (star x) = starRingEnd ℂ (tauE D ρ x)` using `fun x => D.sp.cm.cmUnram.2.1 _ x`. Take `⟨p₁, q₁, hB⟩` from `Formalism.UG.P.signature_exists _ (B.map (tauE D ρ)) (map_isHerm B hBh _ hτ) (map_isUnit_det B hdet _)`. Take `⟨p, q, hG⟩` from `Formalism.UG.P.signature_exists _ (V.gram.map (tauE D ρ)) (map_isHerm _ hGh _ hτ) (map_isUnit_det _ hGd _)`. Take `⟨h1, h2⟩` from `sig_bound ht (β.1.map (tauE D ρ)) (fun i j h => by simp [hz i j h]) (V.gram.map (tauE D ρ)) (p₁ := p₁) (q₁ := q₁) hB hG (fun ε S hε hS => by`. Take `⟨T, hT, hle⟩` from `hcon ρ ε S hε hS`.

Conclude with `⟨T, hT, hle⟩)`. Conclude with `⟨p₁, q₁, p, q, hB, hG, h1, h2⟩`. Take `⟨x, hx1, hx2⟩` from `exists_frame_of_sig D.sp.cm (k := r - t) V.gram B hGh hBh hGd hdet (by omega) (fun τ => by`. Take `⟨ρ, rfl | rfl⟩` from `GlobalTheory.DefLiftMult.exists_tauE D τ`. Conclude with `hplace ρ`.

Take `⟨p₁, q₁, p, q, h1, h2, h3, h4⟩` from `hplace ρ`. Use `⟨p₁, q₁, p, q, ?_, ?_, h3, h4⟩` and prove the remaining obligations. Use `hasSignature_map_conj h1` as an intermediate fact. Rewrite `this` using `[Matrix.map_map]`. Then use the resulting hypothesis. Use `hasSignature_map_conj h2` as an intermediate fact.

Rewrite using `[Matrix.map_map] at this)` and apply the resulting hypothesis. Establish `htk : t + (r - t) = r` using `by omega`. Set `f : Fin t ⊕ Fin (r - t) ≃ Fin r` to `finSumFinEquiv.trans (finCongr htk)`. Use `⟨x.submatrix id f.symm, ?_, ?_⟩` and prove the remaining obligations. Use `Matrix.rank_submatrix x (Equiv.refl _) f.symm` as an intermediate fact.

Rewrite `this` using `[hx1, htk]`. Conclude with `this`. Establish `e1 : gramQ V (x.submatrix id f.symm) = (x.submatrix id f.symm)ᴴ * V.gram * x.submatrix id f.symm`. Unfold `gramQ`. Rewrite using `[Matrix.mul_assoc]`.

Both sides reduce to the same expression. Rewrite using `[e1, gram_submatrix, hx2]`. Conclude with `block_submatrix ht β.1 hz htk`.
-/
theorem GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.exists_obstruction : ∀ (D : D7) (r : ℕ) (V : HSp D), 2 * r < V.rank → ∀ (t : ℕ) (β : HermE D r), GlobalTheory.CompanionTheory.WeilSiegel.Deg.IsBlockNF t β → (¬ ∃ x : Matrix (Fin V.rank) (Fin r) D.host.E, x.rank = r ∧ gramQ V x = β.1) → ∃ (ρ : D.what₂.Tau) (ε : ℝ) (S : Submodule ℂ (Fin r → ℂ)), (ε = 1 ∨ ε = -1) ∧ GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.NonnegOn ε (β.1.map (tauE D ρ)) S ∧ ∀ T : Submodule ℂ (Fin V.rank → ℂ), GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.PosOn ε (gramAt D V ρ) T → Module.finrank ℂ T < Module.finrank ℂ S := by
  intro D r V h2r t β hNF hno
  by_contra hcon
  push_neg at hcon
  obtain ⟨ht, hz, hdet⟩ := hNF
  apply hno
  have hstar : ∀ x : D.host.E, D.sp.cm.sig x = star x := fun _ => rfl
  have hβ : ∀ i j, star (β.1 j i) = β.1 i j := fun i j => by
    have := congrFun (congrFun β.2 i) j
    simpa [hstar] using this
  set B : Matrix (Fin t) (Fin t) D.host.E := β.1.submatrix (Fin.castLE ht.le) (Fin.castLE ht.le) with hBdef
  have hBh : Bᴴ = B := Matrix.ext fun i j => hβ _ _
  have hGh : V.gramᴴ = V.gram := Matrix.ext fun a b => V.herm.eq _ _
  have hGd : V.gram.det ≠ 0 := GlobalTheory.FrameComplement.gram_det_ne V
  have hplace : ∀ ρ : D.what₂.Tau, ∃ p₁ q₁ p q : ℕ, Formalism.UG.HasSignature (B.map (tauE D ρ)) p₁ q₁ ∧
      Formalism.UG.HasSignature (V.gram.map (tauE D ρ)) p q ∧ p₁ + (r - t) ≤ p ∧ q₁ + (r - t) ≤ q := by
    intro ρ
    have hτ : ∀ x, tauE D ρ (star x) = starRingEnd ℂ (tauE D ρ x) := fun x => D.sp.cm.cmUnram.2.1 _ x
    obtain ⟨p₁, q₁, hB⟩ := Formalism.UG.P.signature_exists _ (B.map (tauE D ρ))
      (map_isHerm B hBh _ hτ) (map_isUnit_det B hdet _)
    obtain ⟨p, q, hG⟩ := Formalism.UG.P.signature_exists _ (V.gram.map (tauE D ρ))
      (map_isHerm _ hGh _ hτ) (map_isUnit_det _ hGd _)
    obtain ⟨h1, h2⟩ := sig_bound ht (β.1.map (tauE D ρ)) (fun i j h => by simp [hz i j h])
      (V.gram.map (tauE D ρ)) (p₁ := p₁) (q₁ := q₁) hB hG (fun ε S hε hS => by
        obtain ⟨T, hT, hle⟩ := hcon ρ ε S hε hS
        exact ⟨T, hT, hle⟩)
    exact ⟨p₁, q₁, p, q, hB, hG, h1, h2⟩
  obtain ⟨x, hx1, hx2⟩ := exists_frame_of_sig D.sp.cm (k := r - t) V.gram B hGh hBh hGd hdet (by omega)
    (fun τ => by
      obtain ⟨ρ, rfl | rfl⟩ := GlobalTheory.DefLiftMult.exists_tauE D τ
      · exact hplace ρ
      · obtain ⟨p₁, q₁, p, q, h1, h2, h3, h4⟩ := hplace ρ
        refine ⟨p₁, q₁, p, q, ?_, ?_, h3, h4⟩
        · have := hasSignature_map_conj h1
          rwa [Matrix.map_map] at this
        · have := hasSignature_map_conj h2
          rwa [Matrix.map_map] at this)
  have htk : t + (r - t) = r := by omega
  let f : Fin t ⊕ Fin (r - t) ≃ Fin r := finSumFinEquiv.trans (finCongr htk)
  refine ⟨x.submatrix id f.symm, ?_, ?_⟩
  · have := Matrix.rank_submatrix x (Equiv.refl _) f.symm
    rw [hx1, htk] at this
    exact this
  · have e1 : gramQ V (x.submatrix id f.symm) = (x.submatrix id f.symm)ᴴ * V.gram * x.submatrix id f.symm := by
      unfold gramQ
      rw [Matrix.mul_assoc]
      rfl
    rw [e1, gram_submatrix, hx2]
    exact block_submatrix ht β.1 hz htk
