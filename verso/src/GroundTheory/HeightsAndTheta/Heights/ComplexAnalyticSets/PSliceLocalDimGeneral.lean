import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceLocalDimGeneral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceLocalDimUpperZariski
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalDimDomain
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceReducedAway
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

/- English proof (translation)
Set `s : Finset (R ⧸ I)` to `Finset.univ.image fun i => Ideal.Quotient.mk I (t i)`. Establish `hs : Ideal.span (s : Set (R ⧸ I)) = (Ideal.span (Set.range t)).map (Ideal.Quotient.mk I)`. Rewrite using `[Ideal.map_span]`. Use `congr 1`. Use extensionality with `x`.

Simplify using `[s]`. Establish `hjac : (Ideal.span (Set.range t)).map (Ideal.Quotient.mk I) ≤ Ring.jacobson (R ⧸ I)`. Rewrite using `[← Ideal.jacobson_bot, ← Ideal.map_quotient_self I, ← Ideal.map_jacobson_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]), IsLocalRing.jacobson_eq_maximalIdeal I hI]`. Use `Ideal.map_mono ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `ht i`. Establish `hkey` using `ringKrullDim_le_ringKrullDim_quotient_add_card s fun x hx => hjac (hs ▸ Ideal.subset_span hx)`. Rewrite `hkey` using `[hs, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup I _)]`. Use `hkey.trans ?_` and prove the remaining obligations.

Use `gcongr`. Conclude with `Finset.card_image_le.trans (by simp)` after adjusting the coercions.
-/
theorem ringKrullDim_quotient_le_sup_span_add {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R)
    (hI : I ≠ ⊤) {d : ℕ} (t : Fin d → R) (ht : ∀ i, t i ∈ IsLocalRing.maximalIdeal R) :
    ringKrullDim (R ⧸ I) ≤ ringKrullDim (R ⧸ (I ⊔ Ideal.span (Set.range t))) + (d : ℕ) := by
  classical
  let s : Finset (R ⧸ I) := Finset.univ.image fun i => Ideal.Quotient.mk I (t i)
  have hs : Ideal.span (s : Set (R ⧸ I)) = (Ideal.span (Set.range t)).map (Ideal.Quotient.mk I) := by
    rw [Ideal.map_span]
    congr 1
    ext x
    simp [s]
  have hjac : (Ideal.span (Set.range t)).map (Ideal.Quotient.mk I) ≤ Ring.jacobson (R ⧸ I) := by
    rw [← Ideal.jacobson_bot, ← Ideal.map_quotient_self I,
      ← Ideal.map_jacobson_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]),
      IsLocalRing.jacobson_eq_maximalIdeal I hI]
    refine Ideal.map_mono ?_
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact ht i
  have hkey := ringKrullDim_le_ringKrullDim_quotient_add_card s
    fun x hx => hjac (hs ▸ Ideal.subset_span hx)
  rw [hs, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup I _)] at hkey
  refine hkey.trans ?_
  gcongr
  exact_mod_cast Finset.card_image_le.trans (by simp)

/- English proof (translation)
Set `φ` to `algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)))`. Set `t : Fin d → MvPolynomial (Fin n) ℂ` to `fun i => linPoly L i - C ((L *ᵥ q) i)`. Establish `hI : J.map φ ≠ ⊤`. Introduce `h`. Unfold `localRingAt at hdim`.

Establish `: Subsingleton (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)) ⧸ J.map φ)` using `Ideal.Quotient.subsingleton_iff.mpr h`. Rewrite `hdim` using `[ringKrullDim_eq_bot_of_subsingleton]`. Conclude with `WithBot.bot_ne_coe hdim`. Establish `ht : ∀ i, φ (t i) ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)))`. Introduce `i`.

Rewrite using `[← Localization.AtPrime.map_eq_maximalIdeal]`. Use `Ideal.mem_map_of_mem _ ?_` and prove the remaining obligations. Simplify using `[t, RingHom.mem_ker, eval_linPoly]`. Establish `hkey` using `ringKrullDim_quotient_le_sup_span_add (J.map φ) hI (fun i => φ (t i)) ht`. Establish `hsl : (sliceIdeal J L q).map φ = J.map φ ⊔ Ideal.span (Set.range fun i => φ (t i))`.

Rewrite using `[sliceIdeal, Ideal.map_sup, Ideal.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Rewrite `hkey` using `[← hsl]`. Express the relevant statement in the definitionally equal form `ringKrullDim (localRingAt J q) ≤ ringKrullDim (localRingAt (sliceIdeal J L q) q) + (d : ℕ) at hkey`. Rewrite `hkey` using `[hdim]`.

Generalize the expression as in `ringKrullDim (localRingAt (sliceIdeal J L q) q) = D at hkey ⊢`. Proceed by induction on `D using WithBot.recBotCoe with`. Consider the case `bot => simp at hkey`. Consider the case `coe e`. Proceed by induction on `e using ENat.recTopCoe with`.

Consider the case `top => exact WithBot.coe_le_coe.2 le_top`. Consider the case `coe k`. Establish `h2 : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ ((k + d : ℕ) : WithBot ℕ∞)` using `by simpa using hkey`. Establish `h3 : d + 1 ≤ k + d` using `by exact_mod_cast h2`. Conclude with `(show 1 ≤ k by omega)` after adjusting the coercions.
-/
theorem one_le_ringKrullDim_localRingAt_sliceIdeal {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (L : Matrix (Fin d) (Fin n) ℂ) (q : Fin n → ℂ)
    (hdim : ringKrullDim (localRingAt J q) = (d + 1 : ℕ)) :
    ((1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (localRingAt (sliceIdeal J L q) q) := by
  let φ := algebraMap (MvPolynomial (Fin n) ℂ)
    (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)))
  let t : Fin d → MvPolynomial (Fin n) ℂ := fun i => linPoly L i - C ((L *ᵥ q) i)
  have hI : J.map φ ≠ ⊤ := by
    intro h
    unfold localRingAt at hdim
    have : Subsingleton (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)) ⧸
        J.map φ) := Ideal.Quotient.subsingleton_iff.mpr h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact WithBot.bot_ne_coe hdim
  have ht : ∀ i, φ (t i) ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ))) := by
    intro i
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    refine Ideal.mem_map_of_mem _ ?_
    simp [t, RingHom.mem_ker, eval_linPoly]
  have hkey := ringKrullDim_quotient_le_sup_span_add (J.map φ) hI (fun i => φ (t i)) ht
  have hsl : (sliceIdeal J L q).map φ = J.map φ ⊔ Ideal.span (Set.range fun i => φ (t i)) := by
    rw [sliceIdeal, Ideal.map_sup, Ideal.map_span, ← Set.range_comp]
    rfl
  rw [← hsl] at hkey
  change ringKrullDim (localRingAt J q) ≤ ringKrullDim (localRingAt (sliceIdeal J L q) q) + (d : ℕ)
    at hkey
  rw [hdim] at hkey
  generalize ringKrullDim (localRingAt (sliceIdeal J L q) q) = D at hkey ⊢
  induction D using WithBot.recBotCoe with
  | bot => simp at hkey
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact WithBot.coe_le_coe.2 le_top
    | coe k =>
      have h2 : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ ((k + d : ℕ) : WithBot ℕ∞) := by simpa using hkey
      have h3 : d + 1 ≤ k + d := by exact_mod_cast h2
      exact_mod_cast (show 1 ≤ k by omega)

/- English proof (translation)
Introduce `n d J q hJ hdim hq`. Take `⟨F, hF, hgood⟩` from `hU n d J q hJ hdim hq`. Establish `hloc` using `hL n (d + 1) J hJ hdim q hq`. Set `e : Matrix (Fin d) (Fin n) ℂ → (Fin d × Fin n → ℂ)` to `fun L ij => L ij.1 ij.2`. Set `ψ : (Fin d × Fin n → ℂ) → Matrix (Fin d) (Fin n) ℂ` to `fun y => Matrix.of fun i j => y (i, j)`.

Establish `he : Continuous e` using `continuous_pi fun ij => continuous_id.matrix_elem ij.1 ij.2`. Establish `hψ : Continuous ψ` using `continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)`. Use `⟨{L | eval (e L) F ≠ 0}, ?_, ?_, fun L hLF => le_antisymm (hgood L hLF) (one_le_ringKrullDim_localRingAt_sliceIdeal J L q hloc)⟩` and prove the remaining obligations. Conclude with `isOpen_ne_fun ((MvPolynomial.continuous_eval F).comp he) continuous_const`. Rewrite using `[dense_iff_inter_open]`.

Introduce and unpack `U hU ⟨L₀, hL₀⟩`. Take `⟨y, hyU, hyF⟩` from `exists_eval_ne_zero_of_isOpen_pi hF (hU.preimage hψ) ⟨e L₀, hL₀⟩`. Conclude with `⟨ψ y, hyU, hyF⟩`.
-/
theorem SliceLocalDimGeneral.proof (hL : LocalDimDomain.Statement)
    (hU : SliceLocalDimUpperZariski.Statement) : SliceLocalDimGeneral.Statement := by
  intro n d J q hJ hdim hq
  obtain ⟨F, hF, hgood⟩ := hU n d J q hJ hdim hq
  have hloc := hL n (d + 1) J hJ hdim q hq
  let e : Matrix (Fin d) (Fin n) ℂ → (Fin d × Fin n → ℂ) := fun L ij => L ij.1 ij.2
  let ψ : (Fin d × Fin n → ℂ) → Matrix (Fin d) (Fin n) ℂ := fun y => Matrix.of fun i j => y (i, j)
  have he : Continuous e := continuous_pi fun ij => continuous_id.matrix_elem ij.1 ij.2
  have hψ : Continuous ψ :=
    continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)
  refine ⟨{L | eval (e L) F ≠ 0}, ?_, ?_, fun L hLF => le_antisymm (hgood L hLF)
    (one_le_ringKrullDim_localRingAt_sliceIdeal J L q hloc)⟩
  · exact isOpen_ne_fun ((MvPolynomial.continuous_eval F).comp he) continuous_const
  · rw [dense_iff_inter_open]
    rintro U hU ⟨L₀, hL₀⟩
    obtain ⟨y, hyU, hyF⟩ := exists_eval_ne_zero_of_isOpen_pi hF (hU.preimage hψ) ⟨e L₀, hL₀⟩
    exact ⟨ψ y, hyU, hyF⟩

end

end GroundTheory.Heights₂.Heights
