import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartDim
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothMetricOfIsSmoothHerm
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChart
import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDim
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar mcPts segre)

namespace SegreChartDim

/- English proof (translation)
Establish `hJp : J.IsPrime` using `hJ.1.1`. Establish `hIJ : I ≤ J` using `hJ.1.2`. Establish `hfJ : ∀ a ∈ J, f a ∈ J.comap g` using `fun a ha => by`. Rewrite using `[Ideal.mem_comap]`. Use `hIJ (hgf a)` as an intermediate fact.

Simplify using `using J.add_mem this ha`. Use `⟨⟨⟨Ideal.comap_isPrime g J, fun b hb => hIJ (hg hb)⟩, fun Z ⟨hZp, hIZ⟩ hZJ => ?_⟩, ?_⟩` and prove the remaining obligations. Establish `hle : Z.comap f ≤ J` using `fun a ha => by`. Establish `h1 : g (f a) ∈ J` using `hZJ ha`. Use `J.sub_mem h1 (hIJ (hgf a))` as an intermediate fact.

Simplify using `using this`. Establish `hJZ` using `hJ.2 ⟨Ideal.comap_isPrime f Z, fun a ha => hIZ (hf ha)⟩ hle`. Introduce `b hb`. Establish `h1 : f (g b) ∈ Z` using `hJZ hb`. Use `Z.sub_mem h1 (hIZ (hfg b))` as an intermediate fact.

Simplify using `using this`. Set `φ : A ⧸ J →+* B ⧸ J.comap g` to `Ideal.Quotient.lift J ((Ideal.Quotient.mk _).comp f) fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (hfJ a ha)`. Set `ψ : B ⧸ J.comap g →+* A ⧸ J` to `Ideal.Quotient.lift _ ((Ideal.Quotient.mk J).comp g) fun b hb => Ideal.Quotient.eq_zero_iff_mem.mpr hb`. Use `ringKrullDim_eq_of_ringEquiv (RingEquiv.ofRingHom φ ψ ?_ ?_)` and prove the remaining obligations. Use `Ideal.Quotient.ringHom_ext (RingHom.ext fun b => ?_) show Ideal.Quotient.mk (J.comap g) (f (g b)) = Ideal.Quotient.mk (J.comap g) b` and prove the remaining obligations.

Conclude with `Ideal.Quotient.eq.mpr (hIJ (hg (hfg b)))`. Use `Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_) show Ideal.Quotient.mk J (g (f a)) = Ideal.Quotient.mk J a` and prove the remaining obligations. Conclude with `Ideal.Quotient.eq.mpr (hIJ (hgf a))`.
-/
theorem minimalPrimes_transfer {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (g : B →+* A)
    (I : Ideal A) (I' : Ideal B) (hf : I ≤ I'.comap f) (hg : I' ≤ I.comap g)
    (hgf : ∀ a, g (f a) - a ∈ I) (hfg : ∀ b, f (g b) - b ∈ I') (J : Ideal A) (hJ : J ∈ I.minimalPrimes) :
    J.comap g ∈ I'.minimalPrimes ∧ ringKrullDim (A ⧸ J) = ringKrullDim (B ⧸ J.comap g) := by
  have hJp : J.IsPrime := hJ.1.1
  have hIJ : I ≤ J := hJ.1.2
  have hfJ : ∀ a ∈ J, f a ∈ J.comap g := fun a ha => by
    rw [Ideal.mem_comap]
    have := hIJ (hgf a)
    simpa using J.add_mem this ha
  refine ⟨⟨⟨Ideal.comap_isPrime g J, fun b hb => hIJ (hg hb)⟩, fun Z ⟨hZp, hIZ⟩ hZJ => ?_⟩, ?_⟩
  · have hle : Z.comap f ≤ J := fun a ha => by
      have h1 : g (f a) ∈ J := hZJ ha
      have := J.sub_mem h1 (hIJ (hgf a))
      simpa using this
    have hJZ := hJ.2 ⟨Ideal.comap_isPrime f Z, fun a ha => hIZ (hf ha)⟩ hle
    intro b hb
    have h1 : f (g b) ∈ Z := hJZ hb
    have := Z.sub_mem h1 (hIZ (hfg b))
    simpa using this
  · let φ : A ⧸ J →+* B ⧸ J.comap g :=
      Ideal.Quotient.lift J ((Ideal.Quotient.mk _).comp f) fun a ha =>
        Ideal.Quotient.eq_zero_iff_mem.mpr (hfJ a ha)
    let ψ : B ⧸ J.comap g →+* A ⧸ J :=
      Ideal.Quotient.lift _ ((Ideal.Quotient.mk J).comp g) fun b hb =>
        Ideal.Quotient.eq_zero_iff_mem.mpr hb
    refine ringKrullDim_eq_of_ringEquiv (RingEquiv.ofRingHom φ ψ ?_ ?_)
    · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun b => ?_)
      show Ideal.Quotient.mk (J.comap g) (f (g b)) = Ideal.Quotient.mk (J.comap g) b
      exact Ideal.Quotient.eq.mpr (hIJ (hg (hfg b)))
    · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
      show Ideal.Quotient.mk J (g (f a)) = Ideal.Quotient.mk J a
      exact Ideal.Quotient.eq.mpr (hIJ (hgf a))

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `V W hV hW`. Simplify using `only [Finset.coe_empty, Ideal.span_empty, sup_bot_eq] at hW`. Rewrite `hW` using `[Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff]`.

Substitute `hW` using the available equality. Simplify using the standard rewrite rules. Consider the case `insert a s ha ih`. Introduce `V W hV hW`. Establish `hWp : W.IsPrime` using `hW.1.1`.

Establish `hsplit : V ⊔ Ideal.span (↑(insert a s) : Set (MvPolynomial τ F)) = (V ⊔ Ideal.span (s : Set (MvPolynomial τ F))) ⊔ Ideal.span {a}`. Rewrite using `[Finset.coe_insert, Ideal.span_insert, sup_comm (Ideal.span {a}), sup_assoc]`. Rewrite `hW` using `[hsplit]`. Take `⟨W', hW', hW'W⟩` from `Ideal.exists_minimalPrimes_le (le_sup_left.trans hW.1.2)`. Establish `hW'p : W'.IsPrime` using `hW'.1.1`.

Establish `hmin : W ∈ (W' ⊔ Ideal.span {a}).minimalPrimes`. Use `⟨⟨hWp, sup_le hW'W (le_sup_right.trans hW.1.2)⟩, fun Z ⟨hZp, hZ⟩ hZW => ?_⟩` and prove the remaining obligations. Conclude with `hW.2 ⟨hZp, sup_le (hW'.1.2.trans (le_sup_left.trans hZ)) (le_sup_right.trans hZ)⟩ hZW`. Establish `h1` using `ih V W' hV hW'`. Rewrite using `[Finset.card_insert_of_notMem ha, Nat.cast_succ]`.

Distinguish the cases in `haW' : a ∈ W'`. Establish `heq : W' ⊔ Ideal.span {a} = W'` using `sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr haW')`. Rewrite `hmin` using `[heq, Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff]`. Substitute `hmin` using the available equality. Conclude with `h1.trans (add_le_add le_rfl (show (s.card : WithBot ℕ∞) ≤ (s.card : WithBot ℕ∞) + 1 by exact_mod_cast Nat.le_succ s.card))`.

Establish `h2` using `ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.dimPIT F τ W' W a hW'p haW' hmin`. Rewrite `h1` using `[← h2]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ringKrullDim_le_of_mem_minimalPrimes_sup_span {F : Type} [Field F] {τ : Type} [Fintype τ]
    (s : Finset (MvPolynomial τ F)) :
    ∀ (V W : Ideal (MvPolynomial τ F)), V.IsPrime → W ∈ (V ⊔ Ideal.span (s : Set (MvPolynomial τ F))).minimalPrimes →
      ringKrullDim (MvPolynomial τ F ⧸ V) ≤ ringKrullDim (MvPolynomial τ F ⧸ W) + (s.card : WithBot ℕ∞) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro V W hV hW
    simp only [Finset.coe_empty, Ideal.span_empty, sup_bot_eq] at hW
    rw [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff] at hW
    subst hW
    simp
  | insert a s ha ih =>
    intro V W hV hW
    have hWp : W.IsPrime := hW.1.1
    have hsplit : V ⊔ Ideal.span (↑(insert a s) : Set (MvPolynomial τ F)) =
        (V ⊔ Ideal.span (s : Set (MvPolynomial τ F))) ⊔ Ideal.span {a} := by
      rw [Finset.coe_insert, Ideal.span_insert, sup_comm (Ideal.span {a}), sup_assoc]
    rw [hsplit] at hW
    obtain ⟨W', hW', hW'W⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hW.1.2)
    have hW'p : W'.IsPrime := hW'.1.1
    have hmin : W ∈ (W' ⊔ Ideal.span {a}).minimalPrimes := by
      refine ⟨⟨hWp, sup_le hW'W (le_sup_right.trans hW.1.2)⟩, fun Z ⟨hZp, hZ⟩ hZW => ?_⟩
      exact hW.2 ⟨hZp, sup_le (hW'.1.2.trans (le_sup_left.trans hZ)) (le_sup_right.trans hZ)⟩ hZW
    have h1 := ih V W' hV hW'
    rw [Finset.card_insert_of_notMem ha, Nat.cast_succ]
    by_cases haW' : a ∈ W'
    · have heq : W' ⊔ Ideal.span {a} = W' := sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr haW')
      rw [heq, Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff] at hmin
      subst hmin
      exact h1.trans (add_le_add le_rfl
        (show (s.card : WithBot ℕ∞) ≤ (s.card : WithBot ℕ∞) + 1 by exact_mod_cast Nat.le_succ s.card))
    · have h2 := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.dimPIT F τ W' W a hW'p haW' hmin
      rw [← h2] at h1
      calc ringKrullDim (MvPolynomial τ F ⧸ V) ≤ ringKrullDim (MvPolynomial τ F ⧸ W) + 1 + (s.card : WithBot ℕ∞) := h1
        _ = ringKrullDim (MvPolynomial τ F ⧸ W) + ((s.card : WithBot ℕ∞) + 1) := by rw [add_assoc, add_comm 1]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

open ReciprocityTheory.AnForm.R (chartIdeal conePts affCoord) in

/- English proof (translation)
Establish `: 𝔮.IsPrime` using `h𝔮.1.1`. Establish `hup` using `ReciprocityTheory.AnForm.R.ringKrullDim_quotient_le_of_chartIdeal_le hP e hdim p 𝔮 h𝔮.1.2`. Take `⟨Q, hQ, hQ𝔮⟩` from `Ideal.exists_minimalPrimes_le (le_sup_left.trans h𝔮.1.2)`. Establish `hQp : Q.IsPrime` using `hQ.1.1`. Set `s : Finset (MvPolynomial (Σ k, ι k) ℂ)` to `Finset.univ.image fun k => X ⟨k, p k⟩ - 1`.

Establish `hs : (s : Set (MvPolynomial (Σ k, ι k) ℂ)) = Set.range fun k => X ⟨k, p k⟩ - 1`. Simplify using `[s]`. Establish `hmin : 𝔮 ∈ (Q ⊔ Ideal.span (s : Set (MvPolynomial (Σ k, ι k) ℂ))).minimalPrimes`. Rewrite using `[hs]`. Use `⟨⟨‹_›, sup_le hQ𝔮 (le_sup_right.trans h𝔮.1.2)⟩, fun Z ⟨hZp, hZ⟩ hZ𝔮 => ?_⟩` and prove the remaining obligations.

Conclude with `h𝔮.2 ⟨hZp, sup_le (hQ.1.2.trans (le_sup_left.trans hZ)) (le_sup_right.trans hZ)⟩ hZ𝔮`. Establish `hlow` using `ringKrullDim_le_of_mem_minimalPrimes_sup_span s Q 𝔮 hQp hmin`. Rewrite `hlow` using `[hdim Q hQ]`. Establish `hcard : s.card ≤ Fintype.card K` using `Finset.card_image_le.trans (by simp)`. Establish `hne : ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) ≠ ⊥`.

Establish `: Nontrivial (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)` using `Ideal.Quotient.nontrivial_iff.mpr this.ne_top`. Conclude with `ne_bot_of_le_ne_bot (by simp) ringKrullDim_nonneg_of_nontrivial`. Use `le_antisymm hup ?_` and prove the remaining obligations. Generalize the expression as in `ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) = d at hup hlow hne`. Proceed by induction on `d using WithBot.recBotCoe with`.

Consider the case `bot => exact absurd rfl hne`. Consider the case `coe d`. Proceed by induction on `d using ENat.recTopCoe with`. Consider the case `top => exact absurd hup (by exact_mod_cast (show ¬ ((⊤ : ℕ∞) ≤ (e : ℕ∞)) by simp))`. Consider the case `coe d`.

Establish `h1 : e + Fintype.card K ≤ d + s.card` using `by exact_mod_cast hlow`. Conclude with `(show e ≤ d by omega)` after adjusting the coercions.
-/
theorem ringKrullDim_of_mem_minimalPrimes_chartIdeal {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
    (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal P) (e : ℕ)
    (hdim : ∀ Q ∈ P.minimalPrimes,
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞))
    (p : (k : K) → ι k) {𝔮 : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (h𝔮 : 𝔮 ∈ (chartIdeal P p).minimalPrimes) :
    ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) = e := by
  classical
  have : 𝔮.IsPrime := h𝔮.1.1
  have hup := ReciprocityTheory.AnForm.R.ringKrullDim_quotient_le_of_chartIdeal_le hP e hdim p 𝔮 h𝔮.1.2
  obtain ⟨Q, hQ, hQ𝔮⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans h𝔮.1.2)
  have hQp : Q.IsPrime := hQ.1.1
  let s : Finset (MvPolynomial (Σ k, ι k) ℂ) := Finset.univ.image fun k => X ⟨k, p k⟩ - 1
  have hs : (s : Set (MvPolynomial (Σ k, ι k) ℂ)) = Set.range fun k => X ⟨k, p k⟩ - 1 := by
    simp [s]
  have hmin : 𝔮 ∈ (Q ⊔ Ideal.span (s : Set (MvPolynomial (Σ k, ι k) ℂ))).minimalPrimes := by
    rw [hs]
    refine ⟨⟨‹_›, sup_le hQ𝔮 (le_sup_right.trans h𝔮.1.2)⟩, fun Z ⟨hZp, hZ⟩ hZ𝔮 => ?_⟩
    exact h𝔮.2 ⟨hZp, sup_le (hQ.1.2.trans (le_sup_left.trans hZ)) (le_sup_right.trans hZ)⟩ hZ𝔮
  have hlow := ringKrullDim_le_of_mem_minimalPrimes_sup_span s Q 𝔮 hQp hmin
  rw [hdim Q hQ] at hlow
  have hcard : s.card ≤ Fintype.card K := Finset.card_image_le.trans (by simp)
  have hne : ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) ≠ ⊥ := by
    have : Nontrivial (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) := Ideal.Quotient.nontrivial_iff.mpr this.ne_top
    exact ne_bot_of_le_ne_bot (by simp) ringKrullDim_nonneg_of_nontrivial
  refine le_antisymm hup ?_
  generalize ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) = d at hup hlow hne
  induction d using WithBot.recBotCoe with
  | bot => exact absurd rfl hne
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact absurd hup (by exact_mod_cast (show ¬ ((⊤ : ℕ∞) ≤ (e : ℕ∞)) by simp))
    | coe d =>
      have h1 : e + Fintype.card K ≤ d + s.card := by exact_mod_cast hlow
      exact_mod_cast (show e ≤ d by omega)

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Use `and_congr_right fun _ => ⟨fun h f hf => ?_, fun h f hf => h _ (Ideal.mem_map_of_mem _ hf)⟩` and prove the remaining obligations. Establish `hle : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ RingHom.ker (MvPolynomial.eval z)`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `g hg`. Conclude with `h g hg`.

Conclude with `hle hf`.
-/
theorem mem_mcPts_iff {P : Ideal (MRing ι)} (z : (Σ k, ι k) → ℂ) :
    z ∈ mcPts P ↔ z ∈ ReciprocityTheory.AnForm.R.conePts (P.map (MvPolynomial.map (Int.castRingHom ℂ))) := by
  refine and_congr_right fun _ => ⟨fun h f hf => ?_, fun h f hf => h _ (Ideal.mem_map_of_mem _ hf)⟩
  have hle : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ RingHom.ker (MvPolynomial.eval z) := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    exact h g hg
  exact hle hf

end SegreChartDim

open SegreChartDim

/- English proof (translation)
Introduce `K _ ι _ P e m σ i hP J hJ`. Use `set PQ : Ideal (MvPolynomial (Σ k, ι k) ℚ) := P.map (MvPolynomial.map (Int.castRingHom ℚ)) with hPQ`. Establish `hvar` using `GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isProjVarQ_of_isArithVar hP`. Establish `: PQ.IsPrime` using `hvar.1.isPrime`. Use `set PC : Ideal (MvPolynomial (Σ k, ι k) ℂ) := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hPC`.

Establish `hext : ReciprocityTheory.AnForm.R.extC PQ = PC`. Rewrite using `[ReciprocityTheory.AnForm.R.extC, hPQ, hPC, Ideal.map_map]`. Use `congr 1`. Use `MvPolynomial.ringHom_ext (fun c => ?_) (fun q => ?_)` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, MvPolynomial.map_C]`.

Use `congr 1`. Simplify using the standard rewrite rules. Establish `hdim : ∀ Q ∈ PC.minimalPrimes, ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)`. Introduce `Q hQ`. Rewrite `hQ` using `[← hext]`.

Rewrite using `[ReciprocityTheory.AnForm.R.ringKrullDim_of_mem_minimalPrimes_extC PQ Q hQ]`. Conclude with `hvar.2`. Establish `hPCh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal PC`. Take `⟨S, hS, hPS⟩` from `hP.2.1.2.1`. Use `⟨MvPolynomial.map (Int.castRingHom ℂ) '' S, ?_, by rw [hPC, hPS, Ideal.map_span]⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨f, hf, rfl⟩`. Take `⟨a, ha⟩` from `hS f hf`. Conclude with `⟨a, fun d hd k => ha d (MvPolynomial.support_map_subset _ _ hd) k⟩`. Use `set T : Set ((Σ k, ι k) → ℂ) := MvPolynomial.zeroLocus ℂ (ReciprocityTheory.AnForm.R.chartIdeal PC i) with hT`. Use `set S := segreChartSet P σ i with hS`.

Establish `hTmem : ∀ y, y ∈ T ↔ ∀ h ∈ ReciprocityTheory.AnForm.R.chartIdeal PC i, eval y h = 0` using `fun y => by`. Simplify using `[hT, MvPolynomial.mem_zeroLocus_iff]`. Establish `hsegT : ∀ y ∈ T, (fun a => segre y (σ a)) ∈ S`. Introduce `y hy`. Take `⟨hc, h1, -⟩` from `ReciprocityTheory.AnForm.R.conePts_of_chartIdeal hPCh i y ((hTmem y).1 hy)`.

Conclude with `⟨y, (mem_mcPts_iff y).2 hc, by simp [segre, h1], rfl⟩`. Establish `hlift_apply : ∀ z : (Σ k, ι k) → ℂ, segre z i = 1 → chartLift σ i (fun a => segre z (σ a)) = ReciprocityTheory.AnForm.R.affCoord i z`. Introduce `z hz`. Use function extensionality and compare the values at `q`. Rewrite using `[chartLift_segre_apply σ i z hz q.1 q.2]`.

Simplify using `[ReciprocityTheory.AnForm.R.affCoord, div_eq_mul_inv]`. Establish `hliftS : ∀ x ∈ S, chartLift σ i x ∈ T`. Introduce and unpack `_ ⟨z, hz, hzi, rfl⟩`. Establish `hne : ∀ k, z ⟨k, i k⟩ ≠ 0` using `fun k h0 => by`. Establish `: segre z i = 0` using `Finset.prod_eq_zero (Finset.mem_univ k) h0`.

Rewrite `this` using `[hzi]`. Conclude with `one_ne_zero this`. Rewrite using `[hTmem, hlift_apply z hzi]`. Conclude with `(ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal hPCh i z hne).1 ((mem_mcPts_iff z).1 hz)`. Establish `hsegLift : ∀ x ∈ S, (fun a => segre (chartLift σ i x) (σ a)) = x`.

Introduce and unpack `_ ⟨z, -, hzi, rfl⟩`. Rewrite using `[segre_chartLift σ i z hzi]`. Establish `hliftSeg : ∀ y ∈ T, chartLift σ i (fun a => segre y (σ a)) = y`. Introduce `y hy`. Take `⟨-, h1, -⟩` from `ReciprocityTheory.AnForm.R.conePts_of_chartIdeal hPCh i y ((hTmem y).1 hy)`.

Establish `hyi : segre y i = 1` using `by simp [segre, h1]`. Use function extensionality and compare the values at `q`. Rewrite using `[chartLift_segre_apply σ i y hyi q.1 q.2, h1, inv_one, mul_one]`. Set `α : MvPolynomial (Fin m) ℂ →ₐ[ℂ] MvPolynomial (Σ k, ι k) ℂ` to `aeval fun a => ∏ k, X ⟨k, σ a k⟩`. Set `β : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] MvPolynomial (Fin m) ℂ` to `aeval fun q => X (σ.symm (Function.update i q.1 q.2))`.

Establish `hα : ∀ (y : (Σ k, ι k) → ℂ) f, eval y (α f) = eval (fun a => segre y (σ a)) f`. Introduce `y f`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C c => simp [α]`. Consider the case `add f g hf hg => simp [hf, hg]`.

Consider the case `mul_X f a hf`. Rewrite using `[map_mul, map_mul, map_mul, hf]`. Simplify using `[α, segre, map_prod]`. Establish `hβ : ∀ (x : Fin m → ℂ) g, eval x (β g) = eval (chartLift σ i x) g`. Introduce `x g`.

Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C c => simp [β]`. Consider the case `add f g hf hg => simp [hf, hg]`. Consider the case `mul_X f q hf`. Rewrite using `[map_mul, map_mul, map_mul, hf]`.

Simplify using `[β, chartLift]`. Establish `hvanS : ∀ f, f ∈ segreChartIdeal P σ i ↔ ∀ x ∈ S, eval x f = 0` using `fun f => by`. Simplify using `[segreChartIdeal, hS, MvPolynomial.mem_vanishingIdeal_iff]`. Establish `hvanT : ∀ g, g ∈ MvPolynomial.vanishingIdeal ℂ T ↔ ∀ y ∈ T, eval y g = 0` using `fun g => by`. Simplify using `[MvPolynomial.mem_vanishingIdeal_iff]`.

Establish `htr` using `minimalPrimes_transfer α.toRingHom β.toRingHom (segreChartIdeal P σ i) (MvPolynomial.vanishingIdeal ℂ T) (fun f hf => by`. Rewrite using `[Ideal.mem_comap, hvanT]`. Introduce `y hy`. Use `show eval y (α f) = 0`. Rewrite using `[hα]`.

Conclude with `(hvanS f).1 hf _ (hsegT y hy))`. Use the proof step `(fun g hg => by`. Rewrite using `[Ideal.mem_comap, hvanS]`. Introduce `x hx`. Use `show eval x (β g) = 0`.

Rewrite using `[hβ]`. Conclude with `(hvanT g).1 hg _ (hliftS x hx))`. Use the proof step `(fun f => by`. Rewrite using `[hvanS]`. Introduce `x hx`.

Use `show eval x (β (α f) - f) = 0`. Rewrite using `[map_sub, hβ, hα, hsegLift x hx, sub_self])`. Use the proof step `(fun g => by`. Rewrite using `[hvanT]`. Introduce `y hy`.

Use `show eval y (α (β g) - g) = 0`. Rewrite using `[map_sub, hα, hβ, hliftSeg y hy, sub_self])`. Use `J (mem_segreChartComponents.1 hJ)`. Take `⟨hmin, hd⟩` from `htr`. Rewrite using `[hd]`.

Rewrite `hmin` using `[hT, MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, Ideal.radical_minimalPrimes]`. Conclude with `ringKrullDim_of_mem_minimalPrimes_chartIdeal hPCh e hdim i hmin`.
-/
theorem SegreChartDim.proof : SegreChartDim.Statement := by
  classical
  intro K _ ι _ P e m σ i hP J hJ

  set PQ : Ideal (MvPolynomial (Σ k, ι k) ℚ) := P.map (MvPolynomial.map (Int.castRingHom ℚ)) with hPQ
  have hvar := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isProjVarQ_of_isArithVar hP
  have : PQ.IsPrime := hvar.1.isPrime
  set PC : Ideal (MvPolynomial (Σ k, ι k) ℂ) := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hPC
  have hext : ReciprocityTheory.AnForm.R.extC PQ = PC := by
    rw [ReciprocityTheory.AnForm.R.extC, hPQ, hPC, Ideal.map_map]
    congr 1
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun q => ?_)
    · simp only [RingHom.comp_apply, MvPolynomial.map_C]
      congr 1
    · simp
  have hdim : ∀ Q ∈ PC.minimalPrimes,
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    intro Q hQ
    rw [← hext] at hQ
    rw [ReciprocityTheory.AnForm.R.ringKrullDim_of_mem_minimalPrimes_extC PQ Q hQ]
    exact hvar.2
  have hPCh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal PC := by
    obtain ⟨S, hS, hPS⟩ := hP.2.1.2.1
    refine ⟨MvPolynomial.map (Int.castRingHom ℂ) '' S, ?_, by rw [hPC, hPS, Ideal.map_span]⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, fun d hd k => ha d (MvPolynomial.support_map_subset _ _ hd) k⟩

  set T : Set ((Σ k, ι k) → ℂ) := MvPolynomial.zeroLocus ℂ (ReciprocityTheory.AnForm.R.chartIdeal PC i) with hT
  set S := segreChartSet P σ i with hS
  have hTmem : ∀ y, y ∈ T ↔ ∀ h ∈ ReciprocityTheory.AnForm.R.chartIdeal PC i, eval y h = 0 := fun y => by
    simp [hT, MvPolynomial.mem_zeroLocus_iff]
  have hsegT : ∀ y ∈ T, (fun a => segre y (σ a)) ∈ S := by
    intro y hy
    obtain ⟨hc, h1, -⟩ := ReciprocityTheory.AnForm.R.conePts_of_chartIdeal hPCh i y ((hTmem y).1 hy)
    exact ⟨y, (mem_mcPts_iff y).2 hc, by simp [segre, h1], rfl⟩
  have hlift_apply : ∀ z : (Σ k, ι k) → ℂ, segre z i = 1 →
      chartLift σ i (fun a => segre z (σ a)) = ReciprocityTheory.AnForm.R.affCoord i z := by
    intro z hz
    funext q
    rw [chartLift_segre_apply σ i z hz q.1 q.2]
    simp [ReciprocityTheory.AnForm.R.affCoord, div_eq_mul_inv]
  have hliftS : ∀ x ∈ S, chartLift σ i x ∈ T := by
    rintro _ ⟨z, hz, hzi, rfl⟩
    have hne : ∀ k, z ⟨k, i k⟩ ≠ 0 := fun k h0 => by
      have : segre z i = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
      rw [hzi] at this
      exact one_ne_zero this
    rw [hTmem, hlift_apply z hzi]
    exact (ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal hPCh i z hne).1 ((mem_mcPts_iff z).1 hz)
  have hsegLift : ∀ x ∈ S, (fun a => segre (chartLift σ i x) (σ a)) = x := by
    rintro _ ⟨z, -, hzi, rfl⟩
    rw [segre_chartLift σ i z hzi]
  have hliftSeg : ∀ y ∈ T, chartLift σ i (fun a => segre y (σ a)) = y := by
    intro y hy
    obtain ⟨-, h1, -⟩ := ReciprocityTheory.AnForm.R.conePts_of_chartIdeal hPCh i y ((hTmem y).1 hy)
    have hyi : segre y i = 1 := by simp [segre, h1]
    funext q
    rw [chartLift_segre_apply σ i y hyi q.1 q.2, h1, inv_one, mul_one]

  let α : MvPolynomial (Fin m) ℂ →ₐ[ℂ] MvPolynomial (Σ k, ι k) ℂ :=
    aeval fun a => ∏ k, X ⟨k, σ a k⟩
  let β : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] MvPolynomial (Fin m) ℂ :=
    aeval fun q => X (σ.symm (Function.update i q.1 q.2))
  have hα : ∀ (y : (Σ k, ι k) → ℂ) f, eval y (α f) = eval (fun a => segre y (σ a)) f := by
    intro y f
    induction f using MvPolynomial.induction_on with
    | C c => simp [α]
    | add f g hf hg => simp [hf, hg]
    | mul_X f a hf =>
      rw [map_mul, map_mul, map_mul, hf]
      simp [α, segre, map_prod]
  have hβ : ∀ (x : Fin m → ℂ) g, eval x (β g) = eval (chartLift σ i x) g := by
    intro x g
    induction g using MvPolynomial.induction_on with
    | C c => simp [β]
    | add f g hf hg => simp [hf, hg]
    | mul_X f q hf =>
      rw [map_mul, map_mul, map_mul, hf]
      simp [β, chartLift]
  have hvanS : ∀ f, f ∈ segreChartIdeal P σ i ↔ ∀ x ∈ S, eval x f = 0 := fun f => by
    simp [segreChartIdeal, hS, MvPolynomial.mem_vanishingIdeal_iff]
  have hvanT : ∀ g, g ∈ MvPolynomial.vanishingIdeal ℂ T ↔ ∀ y ∈ T, eval y g = 0 := fun g => by
    simp [MvPolynomial.mem_vanishingIdeal_iff]
  have htr := minimalPrimes_transfer α.toRingHom β.toRingHom (segreChartIdeal P σ i)
    (MvPolynomial.vanishingIdeal ℂ T)
    (fun f hf => by
      rw [Ideal.mem_comap, hvanT]
      intro y hy
      show eval y (α f) = 0
      rw [hα]
      exact (hvanS f).1 hf _ (hsegT y hy))
    (fun g hg => by
      rw [Ideal.mem_comap, hvanS]
      intro x hx
      show eval x (β g) = 0
      rw [hβ]
      exact (hvanT g).1 hg _ (hliftS x hx))
    (fun f => by
      rw [hvanS]
      intro x hx
      show eval x (β (α f) - f) = 0
      rw [map_sub, hβ, hα, hsegLift x hx, sub_self])
    (fun g => by
      rw [hvanT]
      intro y hy
      show eval y (α (β g) - g) = 0
      rw [map_sub, hα, hβ, hliftSeg y hy, sub_self])
    J (mem_segreChartComponents.1 hJ)
  obtain ⟨hmin, hd⟩ := htr
  rw [hd]
  rw [hT, MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, Ideal.radical_minimalPrimes] at hmin
  exact ringKrullDim_of_mem_minimalPrimes_chartIdeal hPCh e hdim i hmin

end GroundTheory.Heights₂.Heights
