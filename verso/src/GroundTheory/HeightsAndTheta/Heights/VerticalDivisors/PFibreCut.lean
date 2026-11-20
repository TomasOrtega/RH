import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsFibreCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial IsDedekindDomain

/- English proof (translation)
Introduce `hWQ`. Establish `: Q.IsPrime` using `hQ.isPrime`. Establish `hPQ : P ≤ Q` using `le_sup_left.trans hQ.le`. Establish `h1` using `Ideal.map_height_le_one_of_mem_minimalPrimes hQ`. Establish `hπ : Function.Surjective (Ideal.Quotient.mk P)` using `Ideal.Quotient.mk_surjective`.

Establish `hker : RingHom.ker (Ideal.Quotient.mk P) = P` using `Ideal.mk_ker`. Establish `hWm : (W.map (Ideal.Quotient.mk P)).IsPrime` using `Ideal.map_isPrime_of_surjective hπ (hker.le.trans hPW.le)`. Establish `hQm : (Q.map (Ideal.Quotient.mk P)).IsPrime` using `Ideal.map_isPrime_of_surjective hπ (hker.le.trans hPQ)`. Establish `hinj : ∀ {I J : Ideal R}, P ≤ I → P ≤ J → I.map (Ideal.Quotient.mk P) = J.map (Ideal.Quotient.mk P) → I = J`. Introduce `I J hI hJ h`.

Use `congrArg (Ideal.comap (Ideal.Quotient.mk P)) h` as an intermediate fact. Rewrite `this` using `[Ideal.comap_map_of_surjective' _ hπ, Ideal.comap_map_of_surjective' _ hπ, hker, sup_eq_left.mpr hI, sup_eq_left.mpr hJ]`. Then use the resulting hypothesis. Establish `hlt1 : (⊥ : Ideal (R ⧸ P)) < W.map (Ideal.Quotient.mk P)`. Use `bot_lt_iff_ne_bot.mpr fun h => hPW.ne ?_` and prove the remaining obligations. Conclude with `hinj le_rfl hPW.le (by rw [h, Ideal.map_quotient_self])`.

Establish `hlt2 : W.map (Ideal.Quotient.mk P) < Q.map (Ideal.Quotient.mk P)` using `lt_of_le_of_ne (Ideal.map_mono hWQ.le) fun h => hWQ.ne (hinj hPW.le hPQ h)`. Establish `a` using `Ideal.height_strict_mono_of_isPrime_of_isPrime hlt1`. Establish `b` using `Ideal.height_strict_mono_of_isPrime_of_isPrime hlt2`. Rewrite `a` using `[Ideal.height_bot]`. Establish `c : (W.map (Ideal.Quotient.mk P)).height < 1` using `lt_of_lt_of_le b h1`.

Rewrite `c` using `[Order.lt_one_iff]`. Rewrite `a` using `[c]`. Conclude with `lt_irrefl _ a`.
-/
theorem not_lt_of_mem_minimalPrimes_sup_span {R : Type*} [CommRing R] [IsNoetherianRing R]
    {P W Q : Ideal R} {f : R} [P.IsPrime] [W.IsPrime] (hPW : P < W)
    (hQ : Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes) : ¬ W < Q := by
  intro hWQ
  have : Q.IsPrime := hQ.isPrime
  have hPQ : P ≤ Q := le_sup_left.trans hQ.le
  have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hQ
  have hπ : Function.Surjective (Ideal.Quotient.mk P) := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (Ideal.Quotient.mk P) = P := Ideal.mk_ker
  have hWm : (W.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective hπ (hker.le.trans hPW.le)
  have hQm : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective hπ (hker.le.trans hPQ)
  have hinj : ∀ {I J : Ideal R}, P ≤ I → P ≤ J →
      I.map (Ideal.Quotient.mk P) = J.map (Ideal.Quotient.mk P) → I = J := by
    intro I J hI hJ h
    have := congrArg (Ideal.comap (Ideal.Quotient.mk P)) h
    rwa [Ideal.comap_map_of_surjective' _ hπ, Ideal.comap_map_of_surjective' _ hπ, hker,
      sup_eq_left.mpr hI, sup_eq_left.mpr hJ] at this
  have hlt1 : (⊥ : Ideal (R ⧸ P)) < W.map (Ideal.Quotient.mk P) := by
    refine bot_lt_iff_ne_bot.mpr fun h => hPW.ne ?_
    exact hinj le_rfl hPW.le (by rw [h, Ideal.map_quotient_self])
  have hlt2 : W.map (Ideal.Quotient.mk P) < Q.map (Ideal.Quotient.mk P) :=
    lt_of_le_of_ne (Ideal.map_mono hWQ.le) fun h => hWQ.ne (hinj hPW.le hPQ h)
  have a := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt1
  have b := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt2
  rw [Ideal.height_bot] at a
  have c : (W.map (Ideal.Quotient.mk P)).height < 1 := lt_of_lt_of_le b h1
  rw [Order.lt_one_iff] at c
  rw [c] at a
  exact lt_irrefl _ a

/- English proof (translation)
Introduce `O _ _ n P W v hP hPC hW hWmax`. Use `set vX : Ideal (MvPolynomial (Fin n) O) := Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal with hvX`. Establish `hWp : W.IsPrime` using `hW.isPrime`. Establish `hPW : P ≤ W` using `le_sup_left.trans hW.le`. Establish `hvW : vX ≤ W` using `le_sup_right.trans hW.le`.

Establish `hfin` using `(P ⊔ vX).finite_minimalPrimes_of_isNoetherianRing`. Choose the witnesses or unpack the hypotheses as in `⟨h, hhQ, hhW⟩ : ∃ h, (∀ Q ∈ (P ⊔ vX).minimalPrimes, Q ≠ W → h ∈ Q) ∧ h ∉ W := by`. Establish `hnot : ¬ (hfin.toFinset.erase W).inf id ≤ W`. Rewrite using `[hWp.inf_le']`. Introduce and unpack `⟨Q, hQs, hQW⟩`.

Take `⟨hQW', hQ⟩` from `Finset.mem_erase.mp hQs`. Rewrite `hQ` using `[Set.Finite.mem_toFinset]`. Conclude with `hQW' (le_antisymm hQW (hW.2 ⟨hQ.isPrime, hQ.le⟩ hQW))`. Take `⟨h, hh, hhW⟩` from `SetLike.not_le_iff_exists.mp hnot`. Conclude with `⟨h, fun Q hQ hQW => Finset.inf_le (f := id) (Finset.mem_erase.mpr ⟨hQW, hfin.mem_toFinset.mpr hQ⟩) hh, hhW⟩`.

Establish `hvmax : v.asIdeal.IsMaximal` using `v.isPrime.isMaximal v.ne_bot`. Establish `hWC : W.comap (C : O →+* MvPolynomial (Fin n) O) = v.asIdeal` using `(hvmax.eq_of_le (Ideal.comap_ne_top _ hWp.ne_top) (Ideal.map_le_iff_le_comap.mp hvW)).symm`. Establish `: W.LiesOver v.asIdeal` using `⟨hWC.symm⟩`. Set `_ : Field (O ⧸ v.asIdeal)` to `Ideal.Quotient.field _`. Establish `hBnf : ¬ IsField (MvPolynomial (Fin n) O ⧸ W)` using `fun hf => hWmax (Ideal.Quotient.maximal_of_isField W hf)`.

Take `⟨I, hIbot, hItop⟩` from `Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top.mp hBnf`. Establish `hdim1 : 1 ≤ ringKrullDim (MvPolynomial (Fin n) O ⧸ W)`. Establish `: Nontrivial (_ ⧸ I)` using `Ideal.Quotient.nontrivial_iff.mpr hItop.ne`. Establish `h2` using `GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le I hIbot.ne'`. Establish `h0` using `ringKrullDim_nonneg_of_nontrivial (R := (MvPolynomial (Fin n) O ⧸ W) ⧸ I)`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨N₀, hN₀, hhN₀, hdimN₀⟩` from `hAvoid (O ⧸ v.asIdeal) (MvPolynomial (Fin n) O ⧸ W) (Ideal.Quotient.mk W h) (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]) hdim1`. Use `set φ : MvPolynomial (Fin n) O →+* (MvPolynomial (Fin n) O ⧸ W) ⧸ N₀ := (Ideal.Quotient.mk N₀).comp (Ideal.Quotient.mk W) with hφ`. Establish `hφs : Function.Surjective φ` using `Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective`. Use `set N := RingHom.ker φ with hNdef`.

Establish `hNp : N.IsPrime` using `RingHom.ker_isPrime φ`. Establish `hmemN : ∀ a, a ∈ N ↔ Ideal.Quotient.mk W a ∈ N₀` using `fun a => by`. Simplify using `[N, φ, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]`. Establish `hWN : W ≤ N` using `fun a ha => (hmemN a).mpr (by`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.mpr ha]`.

Conclude with `N₀.zero_mem)`. Establish `hhN : h ∉ N` using `fun hh => hhN₀ ((hmemN h).mp hh)`. Establish `hdimN : ringKrullDim (MvPolynomial (Fin n) O ⧸ N) + 1 = ringKrullDim (MvPolynomial (Fin n) O ⧸ W)`. Rewrite using `[ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hφs)]`. Conclude with `hdimN₀`.

Establish `hNW : ¬ N ≤ W`. Introduce `hle`. Establish `hN₀bot : N₀ = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`.

Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Conclude with `Ideal.mem_bot.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr (hle ((hmemN a).mpr hx)))`. Substitute `hN₀bot` using the available equality. Rewrite `hdimN₀` using `[ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)]`. Take `⟨m, hm, -⟩` from `GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg (k := O ⧸ v.asIdeal) (A := MvPolynomial (Fin n) O ⧸ W)`.

Rewrite `hdimN₀` using `[hm]`. Establish `: ((m + 1 : ℕ) : WithBot ℕ∞) = (m : WithBot ℕ∞)` using `by push_cast; exact hdimN₀`. Establish `: m + 1 = m` using `by exact_mod_cast this`. Use linear arithmetic over natural numbers and integers. Establish `hNQ : ∀ Q ∈ (P ⊔ vX).minimalPrimes, ¬ N ≤ Q` using `fun Q hQ hle => hNW (hle.trans (hQ.2 ⟨hWp, hW.le⟩ (hWN.trans hle)))`.

Choose the witnesses or unpack the hypotheses as in `⟨f, hfN, hfQ⟩ : ∃ f ∈ N, ∀ Q ∈ (P ⊔ vX).minimalPrimes, f ∉ Q := by`. Establish `hns : ¬ ((N : Set (MvPolynomial (Fin n) O)) ⊆ ⋃ Q ∈ (↑hfin.toFinset : Set (Ideal (MvPolynomial (Fin n) O))), ((id Q : Ideal _) : Set _))`. Rewrite using `[Ideal.subset_union_prime (f := id) ⊥ ⊥ (fun Q hQ _ _ => (hfin.mem_toFinset.mp hQ).isPrime)]`. Introduce and unpack `⟨Q, hQ, hle⟩`. Conclude with `hNQ Q (hfin.mem_toFinset.mp hQ) hle`.

Take `⟨f, hfN, hf⟩` from `Set.not_subset.mp hns`. Use `⟨f, hfN, fun Q hQ hfQ => hf ?_⟩` and prove the remaining obligations. Conclude with `Set.mem_biUnion (Finset.mem_coe.mpr (hfin.mem_toFinset.mpr hQ)) hfQ`. Establish `hfW : f ∉ W` using `hfQ W hW`. Establish `hfP : f ∉ P` using `fun hf => hfW (hPW hf)`.

Establish `hPfN : P ⊔ Ideal.span {f} ≤ N` using `sup_le (hPW.trans hWN) ((Ideal.span_singleton_le_iff_mem _).mpr hfN)`. Take `⟨P', hP', hP'N⟩` from `Ideal.exists_minimalPrimes_le hPfN`. Establish `hP'p : P'.IsPrime` using `hP'.isPrime`. Establish `hPP' : P ≤ P'` using `le_sup_left.trans hP'.le`. Establish `hfP' : f ∈ P'` using `hP'.le (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))`.

Establish `hQN : ∀ Q ∈ (P ⊔ vX).minimalPrimes, Q ≤ N → Q = W` using `fun Q hQ hle => by`. Assume the negation of the conclusion as `hne`. Conclude with `hhN (hle (hhQ Q hQ hne))`. Establish `hPltW : P < W` using `lt_of_le_of_ne hPW fun hPW' => v.ne_bot (by`. Rewrite using `[eq_bot_iff, ← hPC, hPW']`.

Conclude with `Ideal.map_le_iff_le_comap.mp hvW)`. Establish `hvP' : ¬ vX ≤ P'`. Introduce `hle`. Take `⟨Q, hQ, hQP'⟩` from `Ideal.exists_minimalPrimes_le (sup_le hPP' hle)`. Rewrite `hQP'` using `[hQN Q hQ (hQP'.trans hP'N)]`.

Break down `hQP'.lt_or_eq with hlt | heq` into its components or cases. Conclude with `not_lt_of_mem_minimalPrimes_sup_span hPltW hP' hlt`. Conclude with `hfW (heq ▸ hfP')`. Establish `hP'C : P'.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥`. Assume the negation of the conclusion as `hne`.

Establish `hmax : (P'.comap (C : O →+* MvPolynomial (Fin n) O)).IsMaximal` using `Ideal.IsPrime.isMaximal inferInstance hne`. Establish `heq : P'.comap (C : O →+* MvPolynomial (Fin n) O) = N.comap C` using `hmax.eq_of_le (Ideal.comap_ne_top _ hNp.ne_top) (Ideal.comap_mono hP'N)`. Apply `hvP'` to reduce the goal to its premises. Rewrite using `[hvX, Ideal.map_le_iff_le_comap, heq]`. Conclude with `Ideal.map_le_iff_le_comap.mp (hvW.trans hWN)`.

Take `⟨W', hW', hW'N⟩` from `Ideal.exists_minimalPrimes_le (sup_le hP'N (hvW.trans hWN) : P' ⊔ vX ≤ N)`. Establish `: W'.IsPrime` using `hW'.isPrime`. Establish `hWW' : W ≤ W'`. Take `⟨Q, hQ, hQW'⟩` from `Ideal.exists_minimalPrimes_le (sup_le (hPP'.trans (le_sup_left.trans hW'.le)) (le_sup_right.trans hW'.le) : P ⊔ vX ≤ W')`. Rewrite using `[← hQN Q hQ (hQW'.trans hW'N)]`.

Conclude with `hQW'`. Establish `hfW' : f ∈ W'` using `hW'.le (Ideal.mem_sup_left hfP')`. Use `⟨P', W', f, hfP, hP', hP'C, hW', le_antisymm ?_ ?_⟩` and prove the remaining obligations. Establish `hne : W'.map (Ideal.Quotient.mk W) ≠ ⊥`. Introduce `hb`.

Apply `hfW` to reduce the goal to its premises. Establish `hm : Ideal.Quotient.mk W f ∈ W'.map (Ideal.Quotient.mk W)` using `Ideal.mem_map_of_mem _ hfW'`. Rewrite `hm` using `[hb, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hm`. Establish `h2` using `GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le _ hne`.

Rewrite `h2` using `[ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hWW')]`. Then use the resulting hypothesis. Rewrite using `[← hdimN]`. Conclude with `add_le_add (ringKrullDim_le_of_surjective (Ideal.Quotient.factor hW'N) (Ideal.Quotient.factor_surjective hW'N)) le_rfl`.
-/
theorem FibreCut.proof (hAvoid : CodimOnePrimeAvoid.Statement) : FibreCut.Statement := by
  intro O _ _ n P W v hP hPC hW hWmax
  classical
  set vX : Ideal (MvPolynomial (Fin n) O) :=
    Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal with hvX
  have hWp : W.IsPrime := hW.isPrime
  have hPW : P ≤ W := le_sup_left.trans hW.le
  have hvW : vX ≤ W := le_sup_right.trans hW.le
  have hfin := (P ⊔ vX).finite_minimalPrimes_of_isNoetherianRing

  obtain ⟨h, hhQ, hhW⟩ : ∃ h, (∀ Q ∈ (P ⊔ vX).minimalPrimes, Q ≠ W → h ∈ Q) ∧ h ∉ W := by
    have hnot : ¬ (hfin.toFinset.erase W).inf id ≤ W := by
      rw [hWp.inf_le']
      rintro ⟨Q, hQs, hQW⟩
      obtain ⟨hQW', hQ⟩ := Finset.mem_erase.mp hQs
      rw [Set.Finite.mem_toFinset] at hQ
      exact hQW' (le_antisymm hQW (hW.2 ⟨hQ.isPrime, hQ.le⟩ hQW))
    obtain ⟨h, hh, hhW⟩ := SetLike.not_le_iff_exists.mp hnot
    exact ⟨h, fun Q hQ hQW => Finset.inf_le (f := id)
      (Finset.mem_erase.mpr ⟨hQW, hfin.mem_toFinset.mpr hQ⟩) hh, hhW⟩

  have hvmax : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  have hWC : W.comap (C : O →+* MvPolynomial (Fin n) O) = v.asIdeal :=
    (hvmax.eq_of_le (Ideal.comap_ne_top _ hWp.ne_top) (Ideal.map_le_iff_le_comap.mp hvW)).symm
  have : W.LiesOver v.asIdeal := ⟨hWC.symm⟩
  let _ : Field (O ⧸ v.asIdeal) := Ideal.Quotient.field _
  have hBnf : ¬ IsField (MvPolynomial (Fin n) O ⧸ W) :=
    fun hf => hWmax (Ideal.Quotient.maximal_of_isField W hf)
  obtain ⟨I, hIbot, hItop⟩ := Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top.mp hBnf
  have hdim1 : 1 ≤ ringKrullDim (MvPolynomial (Fin n) O ⧸ W) := by
    have : Nontrivial (_ ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop.ne
    have h2 := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le I hIbot.ne'
    have h0 := ringKrullDim_nonneg_of_nontrivial (R := (MvPolynomial (Fin n) O ⧸ W) ⧸ I)
    calc (1 : WithBot ℕ∞) = 0 + 1 := by simp
      _ ≤ ringKrullDim ((MvPolynomial (Fin n) O ⧸ W) ⧸ I) + 1 := add_le_add h0 le_rfl
      _ ≤ _ := h2
  obtain ⟨N₀, hN₀, hhN₀, hdimN₀⟩ := hAvoid (O ⧸ v.asIdeal) (MvPolynomial (Fin n) O ⧸ W)
    (Ideal.Quotient.mk W h) (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]) hdim1

  set φ : MvPolynomial (Fin n) O →+* (MvPolynomial (Fin n) O ⧸ W) ⧸ N₀ :=
    (Ideal.Quotient.mk N₀).comp (Ideal.Quotient.mk W) with hφ
  have hφs : Function.Surjective φ :=
    Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  set N := RingHom.ker φ with hNdef
  have hNp : N.IsPrime := RingHom.ker_isPrime φ
  have hmemN : ∀ a, a ∈ N ↔ Ideal.Quotient.mk W a ∈ N₀ := fun a => by
    simp [N, φ, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  have hWN : W ≤ N := fun a ha => (hmemN a).mpr (by
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]; exact N₀.zero_mem)
  have hhN : h ∉ N := fun hh => hhN₀ ((hmemN h).mp hh)
  have hdimN : ringKrullDim (MvPolynomial (Fin n) O ⧸ N) + 1 =
      ringKrullDim (MvPolynomial (Fin n) O ⧸ W) := by
    rw [ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hφs)]
    exact hdimN₀
  have hNW : ¬ N ≤ W := by
    intro hle
    have hN₀bot : N₀ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact Ideal.mem_bot.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr (hle ((hmemN a).mpr hx)))
    subst hN₀bot
    rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)] at hdimN₀
    obtain ⟨m, hm, -⟩ := GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg
      (k := O ⧸ v.asIdeal) (A := MvPolynomial (Fin n) O ⧸ W)
    rw [hm] at hdimN₀
    have : ((m + 1 : ℕ) : WithBot ℕ∞) = (m : WithBot ℕ∞) := by push_cast; exact hdimN₀
    have : m + 1 = m := by exact_mod_cast this
    omega

  have hNQ : ∀ Q ∈ (P ⊔ vX).minimalPrimes, ¬ N ≤ Q := fun Q hQ hle =>
    hNW (hle.trans (hQ.2 ⟨hWp, hW.le⟩ (hWN.trans hle)))
  obtain ⟨f, hfN, hfQ⟩ : ∃ f ∈ N, ∀ Q ∈ (P ⊔ vX).minimalPrimes, f ∉ Q := by
    have hns : ¬ ((N : Set (MvPolynomial (Fin n) O)) ⊆
        ⋃ Q ∈ (↑hfin.toFinset : Set (Ideal (MvPolynomial (Fin n) O))), ((id Q : Ideal _) : Set _)) := by
      rw [Ideal.subset_union_prime (f := id) ⊥ ⊥
        (fun Q hQ _ _ => (hfin.mem_toFinset.mp hQ).isPrime)]
      rintro ⟨Q, hQ, hle⟩
      exact hNQ Q (hfin.mem_toFinset.mp hQ) hle
    obtain ⟨f, hfN, hf⟩ := Set.not_subset.mp hns
    refine ⟨f, hfN, fun Q hQ hfQ => hf ?_⟩
    exact Set.mem_biUnion (Finset.mem_coe.mpr (hfin.mem_toFinset.mpr hQ)) hfQ
  have hfW : f ∉ W := hfQ W hW
  have hfP : f ∉ P := fun hf => hfW (hPW hf)

  have hPfN : P ⊔ Ideal.span {f} ≤ N :=
    sup_le (hPW.trans hWN) ((Ideal.span_singleton_le_iff_mem _).mpr hfN)
  obtain ⟨P', hP', hP'N⟩ := Ideal.exists_minimalPrimes_le hPfN
  have hP'p : P'.IsPrime := hP'.isPrime
  have hPP' : P ≤ P' := le_sup_left.trans hP'.le
  have hfP' : f ∈ P' := hP'.le (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have hQN : ∀ Q ∈ (P ⊔ vX).minimalPrimes, Q ≤ N → Q = W := fun Q hQ hle => by
    by_contra hne
    exact hhN (hle (hhQ Q hQ hne))
  have hPltW : P < W := lt_of_le_of_ne hPW fun hPW' => v.ne_bot (by
    rw [eq_bot_iff, ← hPC, hPW']
    exact Ideal.map_le_iff_le_comap.mp hvW)
  have hvP' : ¬ vX ≤ P' := by
    intro hle
    obtain ⟨Q, hQ, hQP'⟩ := Ideal.exists_minimalPrimes_le (sup_le hPP' hle)
    rw [hQN Q hQ (hQP'.trans hP'N)] at hQP'
    rcases hQP'.lt_or_eq with hlt | heq
    · exact not_lt_of_mem_minimalPrimes_sup_span hPltW hP' hlt
    · exact hfW (heq ▸ hfP')
  have hP'C : P'.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ := by
    by_contra hne
    have hmax : (P'.comap (C : O →+* MvPolynomial (Fin n) O)).IsMaximal :=
      Ideal.IsPrime.isMaximal inferInstance hne
    have heq : P'.comap (C : O →+* MvPolynomial (Fin n) O) = N.comap C :=
      hmax.eq_of_le (Ideal.comap_ne_top _ hNp.ne_top) (Ideal.comap_mono hP'N)
    apply hvP'
    rw [hvX, Ideal.map_le_iff_le_comap, heq]
    exact Ideal.map_le_iff_le_comap.mp (hvW.trans hWN)

  obtain ⟨W', hW', hW'N⟩ := Ideal.exists_minimalPrimes_le
    (sup_le hP'N (hvW.trans hWN) : P' ⊔ vX ≤ N)
  have : W'.IsPrime := hW'.isPrime
  have hWW' : W ≤ W' := by
    obtain ⟨Q, hQ, hQW'⟩ := Ideal.exists_minimalPrimes_le
      (sup_le (hPP'.trans (le_sup_left.trans hW'.le)) (le_sup_right.trans hW'.le) : P ⊔ vX ≤ W')
    rw [← hQN Q hQ (hQW'.trans hW'N)]
    exact hQW'
  have hfW' : f ∈ W' := hW'.le (Ideal.mem_sup_left hfP')
  refine ⟨P', W', f, hfP, hP', hP'C, hW', le_antisymm ?_ ?_⟩
  · have hne : W'.map (Ideal.Quotient.mk W) ≠ ⊥ := by
      intro hb
      apply hfW
      have hm : Ideal.Quotient.mk W f ∈ W'.map (Ideal.Quotient.mk W) := Ideal.mem_map_of_mem _ hfW'
      rw [hb, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hm
      exact hm
    have h2 := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le _ hne
    rwa [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hWW')] at h2
  · rw [← hdimN]
    exact add_le_add (ringKrullDim_le_of_surjective (Ideal.Quotient.factor hW'N)
      (Ideal.Quotient.factor_surjective hW'N)) le_rfl

end GroundTheory.Heights₂.Heights.Vertical
