import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassIntegralLatticesDiscriminantOrderLe
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IdealsOfNormEqIndexSet

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.LineMass

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Establish `e : S ∩ {x | f x ∈ insert a s} = (S ∩ {x | f x = a}) ∪ (S ∩ {x | f x ∈ s})`.

Use extensionality with `x`. Simplify using `only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_insert, Set.mem_union]`. The claim follows by propositional logic. Rewrite using `[e, Set.encard_union_eq]`. Use `gcongr`.

Rewrite using `[Set.disjoint_left]`. Introduce and unpack `x ⟨-, h1⟩ ⟨-, h2⟩`. Conclude with `ha (by rw [← show f x = a from h1]; exact h2)`.
-/
theorem sum_encard_fibre_le {α ι : Type*} (S : Set α) (f : α → ι) (s : Finset ι) :
    ∑ n ∈ s, (S ∩ {a | f a = n}).encard ≤ (S ∩ {a | f a ∈ s}).encard := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have e : S ∩ {x | f x ∈ insert a s} = (S ∩ {x | f x = a}) ∪ (S ∩ {x | f x ∈ s}) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_insert, Set.mem_union]
      tauto
    rw [e, Set.encard_union_eq]
    · gcongr
    · rw [Set.disjoint_left]
      rintro x ⟨-, h1⟩ ⟨-, h2⟩
      exact ha (by rw [← show f x = a from h1]; exact h2)

/- English proof (translation)
Take `⟨-, hconst, -, -, hadd⟩` from `GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive G α`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [hconst]`. Consider the case `insert a s ha ih`. Simplify using `only [Finset.sum_insert ha]`.

Rewrite using `[hadd, ih]`.
-/
theorem orbSum_finsetSum {G α ι : Type} [Group G] [MulAction G α] (X : Set α) (N : ι → α → ℝ≥0∞)
    (s : Finset ι) : ∑ n ∈ s, orbSum G X (N n) = orbSum G X (fun x => ∑ n ∈ s, N n x) := by
  obtain ⟨-, hconst, -, -, hadd⟩ := GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive G α
  induction s using Finset.induction_on with
  | empty => simp [hconst]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [hadd, ih]

/- English proof (translation)
Take `⟨e⟩ : Nonempty (V ≃ₗ[K] K)` from `FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (by simp [h1])`. Set `e' : V →ₗ[𝓞 K] K` to `(e : V →ₗ[K] K).restrictScalars (𝓞 K)`. Take `⟨a, ha, hint⟩ : IsFractional (nonZeroDivisors (𝓞 K)) (M.map e')` from `FractionalIdeal.isFractional_of_fg (hM.fg.map e')`. Establish `ha0 : a ≠ 0` using `nonZeroDivisors.ne_zero ha`. Set `ψ : V →ₗ[𝓞 K] K` to `a • e'`.

Establish `hψ : Function.Injective ψ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Establish `: a • e x = 0` using `hx`. Rewrite `this` using `[smul_eq_zero]`.

Conclude with `e.map_eq_zero_iff.1 (this.resolve_left ha0)`. Set `ι : 𝓞 K →ₗ[𝓞 K] K` to `Algebra.linearMap (𝓞 K) K`. Establish `hι : Function.Injective ι` using `FaithfulSMul.algebraMap_injective (𝓞 K) K`. Set `J : Submodule (𝓞 K) V → Ideal (𝓞 K)` to `fun N => (N.map ψ).comap ι`. Establish `hJ : ∀ N ≤ M, Submodule.map ι (J N) = N.map ψ`.

Introduce `N hN`. Use `Submodule.map_comap_eq_of_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨y, hy⟩` from `hint (e' x) ⟨x, hN hx, rfl⟩`. Conclude with `⟨y, hy⟩`.

Establish `hle : ∀ N ≤ M, J N ≤ J M` using `fun N hN => Submodule.comap_mono (Submodule.map_mono hN)`. Establish `hidx : ∀ N ≤ M, idxN M N * Ideal.absNorm (J M) = Ideal.absNorm (J N)`. Introduce `N hN`. Establish `e1 : idxN M N = (J N).toAddSubgroup.relIndex (J M).toAddSubgroup`. Unfold `idxN`.

Rewrite using `[← AddSubgroup.relIndex_map_map_of_injective (f := ψ.toAddMonoidHom) _ _ hψ, ← AddSubgroup.relIndex_map_map_of_injective (f := ι.toAddMonoidHom) (J N).toAddSubgroup _ hι]`. Express the relevant statement in the definitionally equal form `(N.map ψ).toAddSubgroup.relIndex (M.map ψ).toAddSubgroup = (Submodule.map ι (J N)).toAddSubgroup.relIndex (Submodule.map ι (J M)).toAddSubgroup`. Rewrite using `[hJ N hN, hJ M le_rfl]`. Rewrite using `[e1]`. Conclude with `AddSubgroup.relIndex_mul_index (hle N hN)`.

Establish `hJM : J M ≠ ⊥`. Introduce `h0`. Establish `h2` using `hJ M le_rfl`. Rewrite `h2` using `[h0, Submodule.map_bot]`. Establish `h3 : M = ⊥`.

Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Establish `: ψ x ∈ (⊥ : Submodule (𝓞 K) K)` using `h2 ▸ ⟨x, hx, rfl⟩`. Conclude with `(injective_iff_map_eq_zero ψ).1 hψ x this`. Establish `h4` using `hM.span_eq_top`.

Rewrite `h4` using `[h3]`. Establish `: Nontrivial V` using `Module.nontrivial_of_finrank_pos (R := K) (by omega)`. Simplify using `at h4`. Establish `hq : ∀ N : Submodule (𝓞 K) V, ∃ I : Ideal (𝓞 K), N ≤ M → J N = J M * I`. Introduce `N`.

Distinguish the cases in `hN : N ≤ M`. Take `⟨I, hI⟩` from `Ideal.dvd_iff_le.2 (hle N hN)`. Conclude with `⟨I, fun _ => hI⟩`. Conclude with `⟨⊥, fun h => (hN h).elim⟩`. Use `choose q hq using hq`.

Use `Set.encard_le_encard_of_injOn (f := q) ?_ ?_` and prove the remaining obligations. Introduce and unpack `N ⟨hN, h0, hX⟩`. Establish `h2` using `hidx N hN`. Rewrite `h2` using `[hq N hN, map_mul, mul_comm]`. Establish `h3` using `Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.1 hJM)) h2`.

Use `⟨fun hb => h0 (by rw [h3, hb, Ideal.absNorm_bot]), ?_⟩` and prove the remaining obligations. Rewrite using `[← h3]`. Conclude with `hX` after adjusting the coercions. Introduce and unpack `N ⟨hN, -⟩ N' ⟨hN', -⟩ hqq`. Apply `Submodule.map_injective_of_injective hψ` to reduce the goal to its premises.

Rewrite using `[← hJ N hN, ← hJ N' hN', hq N hN, hq N' hN', hqq]`.
-/
theorem sub_count {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h1 : Module.finrank K V = 1)
    (M : Submodule (𝓞 K) V) (hM : Submodule.IsLattice K M) (X : ℕ) :
    {N : Submodule (𝓞 K) V | N ≤ M ∧ idxN M N ≠ 0 ∧ idxN M N ≤ X}.encard ≤
      {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.encard := by
  obtain ⟨e⟩ : Nonempty (V ≃ₗ[K] K) :=
    FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (by simp [h1])
  let e' : V →ₗ[𝓞 K] K := (e : V →ₗ[K] K).restrictScalars (𝓞 K)
  obtain ⟨a, ha, hint⟩ : IsFractional (nonZeroDivisors (𝓞 K)) (M.map e') :=
    FractionalIdeal.isFractional_of_fg (hM.fg.map e')
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  let ψ : V →ₗ[𝓞 K] K := a • e'
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have : a • e x = 0 := hx
    rw [smul_eq_zero] at this
    exact e.map_eq_zero_iff.1 (this.resolve_left ha0)
  let ι : 𝓞 K →ₗ[𝓞 K] K := Algebra.linearMap (𝓞 K) K
  have hι : Function.Injective ι := FaithfulSMul.algebraMap_injective (𝓞 K) K
  let J : Submodule (𝓞 K) V → Ideal (𝓞 K) := fun N => (N.map ψ).comap ι
  have hJ : ∀ N ≤ M, Submodule.map ι (J N) = N.map ψ := by
    intro N hN
    refine Submodule.map_comap_eq_of_le ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy⟩ := hint (e' x) ⟨x, hN hx, rfl⟩
    exact ⟨y, hy⟩
  have hle : ∀ N ≤ M, J N ≤ J M := fun N hN => Submodule.comap_mono (Submodule.map_mono hN)
  have hidx : ∀ N ≤ M, idxN M N * Ideal.absNorm (J M) = Ideal.absNorm (J N) := by
    intro N hN
    have e1 : idxN M N = (J N).toAddSubgroup.relIndex (J M).toAddSubgroup := by
      unfold idxN
      rw [← AddSubgroup.relIndex_map_map_of_injective (f := ψ.toAddMonoidHom) _ _ hψ,
        ← AddSubgroup.relIndex_map_map_of_injective (f := ι.toAddMonoidHom) (J N).toAddSubgroup _ hι]
      change (N.map ψ).toAddSubgroup.relIndex (M.map ψ).toAddSubgroup =
        (Submodule.map ι (J N)).toAddSubgroup.relIndex (Submodule.map ι (J M)).toAddSubgroup
      rw [hJ N hN, hJ M le_rfl]
    rw [e1]
    exact AddSubgroup.relIndex_mul_index (hle N hN)
  have hJM : J M ≠ ⊥ := by
    intro h0
    have h2 := hJ M le_rfl
    rw [h0, Submodule.map_bot] at h2
    have h3 : M = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : ψ x ∈ (⊥ : Submodule (𝓞 K) K) := h2 ▸ ⟨x, hx, rfl⟩
      exact (injective_iff_map_eq_zero ψ).1 hψ x this
    have h4 := hM.span_eq_top
    rw [h3] at h4
    have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
    simp at h4
  have hq : ∀ N : Submodule (𝓞 K) V, ∃ I : Ideal (𝓞 K), N ≤ M → J N = J M * I := by
    intro N
    by_cases hN : N ≤ M
    · obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.2 (hle N hN)
      exact ⟨I, fun _ => hI⟩
    · exact ⟨⊥, fun h => (hN h).elim⟩
  choose q hq using hq
  refine Set.encard_le_encard_of_injOn (f := q) ?_ ?_
  · rintro N ⟨hN, h0, hX⟩
    have h2 := hidx N hN
    rw [hq N hN, map_mul, mul_comm] at h2
    have h3 := Nat.eq_of_mul_eq_mul_left
      (Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.1 hJM)) h2
    refine ⟨fun hb => h0 (by rw [h3, hb, Ideal.absNorm_bot]), ?_⟩
    rw [← h3]
    exact_mod_cast hX
  · rintro N ⟨hN, -⟩ N' ⟨hN', -⟩ hqq
    apply Submodule.map_injective_of_injective hψ
    rw [← hJ N hN, ← hJ N' hN', hq N hN, hq N' hN', hqq]

/- English proof (translation)
Introduce `hMM K V _ _ _ _ _ _ _ _ h hK hs hp hj V' _ _ _ _ _ h' I hs' hI X hX`. Establish `hnd` using `SpaceMass.nondeg_of_PD h hp`. Establish `hp'` using `SpaceMass.PD_of_ortho h' hK I _ hI`. Establish `hnd'` using `SpaceMass.nondeg_of_PD h' hp'`. Distinguish the cases in `hE : ∃ M₁ : Submodule (𝓞 K) V, IsIntLat h M₁`.

Use `swap`. Use `le_of_eq_of_le (Finset.sum_eq_zero fun n _ => ?_) zero_le` and prove the remaining obligations. Unfold `orbMass orbSum`. Conclude with `ENNReal.tsum_eq_zero.2 fun q => (hE ⟨_, q.2.1⟩).elim`. Take `⟨M₁, hM₁⟩` from `hE`.

Take `⟨hex, -, -⟩` from `GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K V h hK hs hnd`. Take `⟨M₀, hM₀, -⟩` from `hex M₁ hM₁`. Take `⟨c, hc⟩` from `hMM K hK 1 le_rfl`. Take `⟨-, hu', ho'⟩` from `GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K V' h' hK hs' hnd'`. Take `⟨hIl, hIu, hIr⟩` from `ho' I _ hI`.

Take `⟨hImax, -, hIlam⟩` from `hu' I hIl hIu`. Establish `hcI : mass h' I = c` using `by rw [hc V' h' hs' hp' hIr I hImax, hIlam, mul_one]`. Establish `hdisc` using `GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K V h hK hs hnd`. Take `⟨hmass, hmpos, hYst, hfin, -⟩` from `GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp M₀ hM₀.1.1`. Establish `hm₀ : mass h M₀ = c`.

Establish `: lamMax h M₀ = 1`. Unfold `lamMax`. Use `finprod_mem_of_eqOn_one fun P _ => ?_` and prove the remaining obligations. Establish `: (qIn P : ℝ) + 1 ≠ 0` using `by positivity`. Simplify using `only [hj, pow_one, sub_neg_eq_add, Pi.one_apply]`.

Conclude with `div_self this`. Rewrite using `[hc V h hs hp hj M₀ hM₀, this, mul_one]`. Take `⟨mono, hconst, -⟩` from `GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive (isom h) (Submodule (𝓞 K) V)`. Establish `key : ∀ n : ℕ, orbMass (isom h) (latsDisc (R` using `𝓞 K) h n) ≤ orbSum (isom h) (genus h M₀) (fun M' => ((({N : Submodule (𝓞 K) V | IsIntLat h N ∧ N ≤ M'} ∩ {N | discN h N = n}).encard : ℕ∞) : ℝ≥0∞)) := by`. Introduce `n`.

Establish `hDst : Stable (isom h) (latsDisc (R` using `𝓞 K) h n) := by`. Introduce `g M hM`. Establish `h1` using `(GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp M hM.1.1).2.2.1 g M (SpaceMass.mem_genus_self h M hM.1.1)`. Establish `h2` using `(hdisc M hM.1).2.2.2.1 _ h1`. Conclude with `⟨h2.1, h2.2.trans hM.2⟩`.

Set `Y : Set (Submodule (𝓞 K) V × Submodule (𝓞 K) V)` to `{p | p.1 ∈ latsDisc (R := 𝓞 K) h n ∧ p.2 ∈ genus h M₀ ∧ p.1 ≤ p.2}`. Establish `hXst : Stable (isom h) Y`. Introduce and unpack `g p ⟨h1, h2, h3⟩`. Conclude with `⟨hDst g _ h1, hYst g _ h2, Submodule.map_mono h3⟩`. Establish `f1` using `GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (isom h) _ _ Y (latsDisc (R := 𝓞 K) h n) Prod.fst (fun _ _ => rfl) hXst hDst (fun p hp => hp.1) (fun y hy => hfin y hy.1.1)`.

Establish `f2` using `GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (isom h) _ _ Y (genus h M₀) Prod.snd (fun _ _ => rfl) hXst hYst (fun p hp => hp.2.1) (fun y hy => hfin y hy.1)`. Establish `s1 : orbMass (isom h) (latsDisc (R` using `𝓞 K) h n) ≤ orbMass (isom h) Y := by`. Rewrite using `[f1]`. Use `mono _ _ _ _ subset_rfl fun M hM => ?_` and prove the remaining obligations. Take `⟨M', hM', hle⟩` from `hex M hM.1`.

Establish `hne : (Y ∩ Prod.fst ⁻¹' {M}).Nonempty` using `⟨(M, M'), ⟨hM, (GlobalTheory.T.mem_genus_iff_maximalIntegralHermitianLattice K V h hK hs hp M₀ M' hM₀).2 hM', hle⟩, rfl⟩`. Use `Set.one_le_encard_iff_nonempty.2 hne` as an intermediate fact. Conclude with `this` after adjusting the coercions. Use `s1.trans ?_` and prove the remaining obligations. Rewrite using `[f2]`.

Use `mono _ _ _ _ subset_rfl fun M' _ => ?_` and prove the remaining obligations. Establish `: (Y ∩ Prod.snd ⁻¹' {M'}).encard ≤ ({N : Submodule (𝓞 K) V | IsIntLat h N ∧ N ≤ M'} ∩ {N | discN h N = n}).encard`. Use `Set.encard_le_encard_of_injOn (f := Prod.fst) ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨N, N'⟩ ⟨⟨h1, -, h3⟩, h4⟩`. Take `rfl : N' = M'` from `h4`.

Conclude with `⟨⟨h1.1, h3⟩, h1.2⟩`. Introduce and unpack `⟨N, N'⟩ ⟨-, h4⟩ ⟨P, P'⟩ ⟨-, h5⟩ h6`. Take `rfl : N' = M'` from `h4`. Take `rfl : P' = N'` from `h5`. Take `rfl : N = P` from `h6`.

Both sides reduce to the same expression. Conclude with `this` after adjusting the coercions. Use `(Finset.sum_le_sum fun n _ => key n).trans ?_` and prove the remaining obligations. Rewrite using `[orbSum_finsetSum]`. Take `⟨hIfin, hIcard⟩` from `Formalism.HermitianLatticeCounting.P.ideal_norm_le_count K (X : ℝ) (by exact_mod_cast hX)`.

Establish `hexp : 1 + Real.logb 2 (Module.finrank ℚ K) = 2 + Real.logb 2 (fDeg K)`. Use `hK.1` as an intermediate fact. Establish `h2 : Module.finrank ℚ K = 2 * fDeg K`. Unfold `fDeg`. Rewrite using `[InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.finrank, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]`.

Establish `h3 : (fDeg K : ℝ) ≠ 0`. Conclude with `(Fintype.card_pos (α := InfinitePlace K)).ne'` after adjusting the coercions. Rewrite using `[h2]`. Use `push_cast`. Rewrite using `[Real.logb_mul two_ne_zero h3, Real.logb_self_eq_one (by norm_num)]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hIcard` using `[hexp]`. Rewrite using `[hcI, ← hm₀, mul_comm, ENNReal.ofReal_mul (by positivity), hmass, ← hconst]`. Use `mono _ _ _ _ subset_rfl fun M' hM' => ?_` and prove the remaining obligations. Establish `hM''` using `(hdisc M₀ hM₀.1).2.2.2.1 M' hM'`.

Establish `a1` using `sum_encard_fibre_le {N : Submodule (𝓞 K) V | IsIntLat h N ∧ N ≤ M'} (fun N => discN h N) (Finset.Icc 1 (X ^ 2))`. Establish `a2 : ({N : Submodule (𝓞 K) V | IsIntLat h N ∧ N ≤ M'} ∩ {N | discN h N ∈ Finset.Icc 1 (X ^ 2)}).encard ≤ {N : Submodule (𝓞 K) V | N ≤ M' ∧ idxN M' N ≠ 0 ∧ idxN M' N ≤ X}.encard`. Use `Set.encard_le_encard ?_` and prove the remaining obligations. Introduce and unpack `N ⟨⟨h1, h2⟩, h3⟩`. Take `⟨h4, h5⟩` from `(hdisc N h1).2.2.1 M' hM''.1 h2`.

Use `⟨h2, h4, ?_⟩` and prove the remaining obligations. Establish `h6 : discN h N ≤ X ^ 2` using `(Finset.mem_Icc.1 h3).2`. Establish `h7` using `Nat.pos_of_ne_zero (hdisc M' hM''.1).1`. Establish `h8 : idxN M' N ^ 2 ≤ X ^ 2` using `(Nat.le_mul_of_pos_left _ h7).trans (h5 ▸ h6)`. Conclude with `(Nat.pow_le_pow_iff_left two_ne_zero).1 h8`.

Establish `a3` using `(a1.trans a2).trans (sub_count hj M' hM'.1 X)`. Rewrite `a3` using `[← hIfin.cast_ncard_eq]`. Use `le_trans ?_ (ENNReal.ofReal_le_ofReal hIcard)` and prove the remaining obligations. Rewrite using `[ENNReal.ofReal_natCast]`. Establish `a4` using `ENat.toENNReal_le.2 a3`.

Rewrite `a4` using `[ENat.toENNReal_coe]`. Use `le_trans (le_of_eq ?_) a4` and prove the remaining obligations. Conclude with `(map_sum ENat.toENNRealRingHom _ _).symm`.
-/
theorem main : MaxMass → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → Module.finrank K V = 1 → ∀ (V₁ : Type) [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁] [Module (𝓞 K) V₁] [IsScalarTower (𝓞 K) K V₁] (h₁ : V₁ →ₗ⋆[K] V₁ →ₗ[K] K) (I₁ : Submodule (𝓞 K) V₁), h₁.IsSymm → IsOrthoLattice h₁ I₁ 1 → ∀ X : ℕ, 1 ≤ X → ∑ n ∈ Finset.Icc 1 (X ^ 2), orbMass (isom h) (latsDisc (R := 𝓞 K) h n) ≤ ENNReal.ofReal (mass h₁ I₁ * (X : ℝ) ^ (2 + Real.logb 2 (fDeg K))) := by
  intro hMM K V _ _ _ _ _ _ _ _ h hK hs hp hj V' _ _ _ _ _ h' I hs' hI X hX
  have hnd := SpaceMass.nondeg_of_PD h hp
  have hp' := SpaceMass.PD_of_ortho h' hK I _ hI
  have hnd' := SpaceMass.nondeg_of_PD h' hp'
  by_cases hE : ∃ M₁ : Submodule (𝓞 K) V, IsIntLat h M₁
  swap
  · refine le_of_eq_of_le (Finset.sum_eq_zero fun n _ => ?_) zero_le
    unfold orbMass orbSum
    exact ENNReal.tsum_eq_zero.2 fun q => (hE ⟨_, q.2.1⟩).elim
  obtain ⟨M₁, hM₁⟩ := hE
  obtain ⟨hex, -, -⟩ := GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K V h hK hs hnd
  obtain ⟨M₀, hM₀, -⟩ := hex M₁ hM₁
  obtain ⟨c, hc⟩ := hMM K hK 1 le_rfl
  obtain ⟨-, hu', ho'⟩ := GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K V' h' hK hs' hnd'
  obtain ⟨hIl, hIu, hIr⟩ := ho' I _ hI
  obtain ⟨hImax, -, hIlam⟩ := hu' I hIl hIu
  have hcI : mass h' I = c := by rw [hc V' h' hs' hp' hIr I hImax, hIlam, mul_one]
  have hdisc := GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K V h hK hs hnd
  obtain ⟨hmass, hmpos, hYst, hfin, -⟩ := GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp M₀ hM₀.1.1
  have hm₀ : mass h M₀ = c := by
    have : lamMax h M₀ = 1 := by
      unfold lamMax
      refine finprod_mem_of_eqOn_one fun P _ => ?_
      have : (qIn P : ℝ) + 1 ≠ 0 := by positivity
      simp only [hj, pow_one, sub_neg_eq_add, Pi.one_apply]
      exact div_self this
    rw [hc V h hs hp hj M₀ hM₀, this, mul_one]
  obtain ⟨mono, hconst, -⟩ := GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive (isom h) (Submodule (𝓞 K) V)
  have key : ∀ n : ℕ, orbMass (isom h) (latsDisc (R := 𝓞 K) h n) ≤ orbSum (isom h) (genus h M₀)
      (fun M' => ((({N : Submodule (𝓞 K) V | IsIntLat h N ∧ N ≤ M'} ∩ {N | discN h N = n}).encard : ℕ∞) :
        ℝ≥0∞)) := by
    intro n
    have hDst : Stable (isom h) (latsDisc (R := 𝓞 K) h n) := by
      intro g M hM
      have h1 := (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp M hM.1.1).2.2.1 g M
        (SpaceMass.mem_genus_self h M hM.1.1)
      have h2 := (hdisc M hM.1).2.2.2.1 _ h1
      exact ⟨h2.1, h2.2.trans hM.2⟩
    let Y : Set (Submodule (𝓞 K) V × Submodule (𝓞 K) V) :=
      {p | p.1 ∈ latsDisc (R := 𝓞 K) h n ∧ p.2 ∈ genus h M₀ ∧ p.1 ≤ p.2}
    have hXst : Stable (isom h) Y := by
      rintro g p ⟨h1, h2, h3⟩
      exact ⟨hDst g _ h1, hYst g _ h2, Submodule.map_mono h3⟩
    have f1 := GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (isom h) _ _ Y (latsDisc (R := 𝓞 K) h n) Prod.fst (fun _ _ => rfl) hXst hDst
      (fun p hp => hp.1) (fun y hy => hfin y hy.1.1)
    have f2 := GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (isom h) _ _ Y (genus h M₀) Prod.snd (fun _ _ => rfl) hXst hYst
      (fun p hp => hp.2.1) (fun y hy => hfin y hy.1)
    have s1 : orbMass (isom h) (latsDisc (R := 𝓞 K) h n) ≤ orbMass (isom h) Y := by
      rw [f1]
      refine mono _ _ _ _ subset_rfl fun M hM => ?_
      obtain ⟨M', hM', hle⟩ := hex M hM.1
      have hne : (Y ∩ Prod.fst ⁻¹' {M}).Nonempty :=
        ⟨(M, M'), ⟨hM, (GlobalTheory.T.mem_genus_iff_maximalIntegralHermitianLattice K V h hK hs hp M₀ M' hM₀).2 hM', hle⟩, rfl⟩
      have := Set.one_le_encard_iff_nonempty.2 hne
      exact_mod_cast this
    refine s1.trans ?_
    rw [f2]
    refine mono _ _ _ _ subset_rfl fun M' _ => ?_
    have : (Y ∩ Prod.snd ⁻¹' {M'}).encard ≤
        ({N : Submodule (𝓞 K) V | IsIntLat h N ∧ N ≤ M'} ∩ {N | discN h N = n}).encard := by
      refine Set.encard_le_encard_of_injOn (f := Prod.fst) ?_ ?_
      · rintro ⟨N, N'⟩ ⟨⟨h1, -, h3⟩, h4⟩
        obtain rfl : N' = M' := h4
        exact ⟨⟨h1.1, h3⟩, h1.2⟩
      · rintro ⟨N, N'⟩ ⟨-, h4⟩ ⟨P, P'⟩ ⟨-, h5⟩ h6
        obtain rfl : N' = M' := h4
        obtain rfl : P' = N' := h5
        obtain rfl : N = P := h6
        rfl
    exact_mod_cast this
  refine (Finset.sum_le_sum fun n _ => key n).trans ?_
  rw [orbSum_finsetSum]
  obtain ⟨hIfin, hIcard⟩ := Formalism.HermitianLatticeCounting.P.ideal_norm_le_count K (X : ℝ) (by exact_mod_cast hX)
  have hexp : 1 + Real.logb 2 (Module.finrank ℚ K) = 2 + Real.logb 2 (fDeg K) := by
    have := hK.1
    have h2 : Module.finrank ℚ K = 2 * fDeg K := by
      unfold fDeg
      rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.finrank,
        IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
    have h3 : (fDeg K : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos (α := InfinitePlace K)).ne'
    rw [h2]
    push_cast
    rw [Real.logb_mul two_ne_zero h3, Real.logb_self_eq_one (by norm_num)]
    ring
  rw [hexp] at hIcard
  rw [hcI, ← hm₀, mul_comm, ENNReal.ofReal_mul (by positivity), hmass, ← hconst]
  refine mono _ _ _ _ subset_rfl fun M' hM' => ?_
  have hM'' := (hdisc M₀ hM₀.1).2.2.2.1 M' hM'
  have a1 := sum_encard_fibre_le {N : Submodule (𝓞 K) V | IsIntLat h N ∧ N ≤ M'} (fun N => discN h N)
    (Finset.Icc 1 (X ^ 2))
  have a2 : ({N : Submodule (𝓞 K) V | IsIntLat h N ∧ N ≤ M'} ∩
      {N | discN h N ∈ Finset.Icc 1 (X ^ 2)}).encard ≤
      {N : Submodule (𝓞 K) V | N ≤ M' ∧ idxN M' N ≠ 0 ∧ idxN M' N ≤ X}.encard := by
    refine Set.encard_le_encard ?_
    rintro N ⟨⟨h1, h2⟩, h3⟩
    obtain ⟨h4, h5⟩ := (hdisc N h1).2.2.1 M' hM''.1 h2
    refine ⟨h2, h4, ?_⟩
    have h6 : discN h N ≤ X ^ 2 := (Finset.mem_Icc.1 h3).2
    have h7 := Nat.pos_of_ne_zero (hdisc M' hM''.1).1
    have h8 : idxN M' N ^ 2 ≤ X ^ 2 := (Nat.le_mul_of_pos_left _ h7).trans (h5 ▸ h6)
    exact (Nat.pow_le_pow_iff_left two_ne_zero).1 h8
  have a3 := (a1.trans a2).trans (sub_count hj M' hM'.1 X)
  rw [← hIfin.cast_ncard_eq] at a3
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal hIcard)
  rw [ENNReal.ofReal_natCast]
  have a4 := ENat.toENNReal_le.2 a3
  rw [ENat.toENNReal_coe] at a4
  refine le_trans (le_of_eq ?_) a4
  exact (map_sum ENat.toENNRealRingHom _ _).symm

end GlobalTheory.Mass.LineMass
