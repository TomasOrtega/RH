import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleModuleEqNormModuleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleModuleBoundedOnCompactStatement

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Vanish

open GlobalTheory.CompanionTheory.SW.WBox (cK)

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R] {d : ℕ}
  (b : Module.Basis (Fin d) F E)

/- English proof (translation)
Establish `e : (r ⊗ₜ[F] (1 : E)) * y = r • y`. Rewrite using `[Algebra.smul_def]`. Both sides reduce to the same expression. Simplify using `[cK, e]`.
-/
theorem cK_tmul_mul (r : R) (y : R ⊗[F] E) (k : Fin d) :
    cK R b ((r ⊗ₜ[F] (1 : E)) * y) k = r * cK R b y k := by
  have e : (r ⊗ₜ[F] (1 : E)) * y = r • y := by
    rw [Algebra.smul_def]
    rfl
  simp [cK, e]

/- English proof (translation)
Establish `e : (N : R ⊗[F] E) = (N : R) ⊗ₜ[F] (1 : E)`. Conclude with `(map_natCast (algebraMap R (R ⊗[F] E)) N).symm`. Rewrite using `[e, cK_tmul_mul]`.
-/
theorem cK_nat_mul (N : ℕ) (y : R ⊗[F] E) (k : Fin d) :
    cK R b ((N : R ⊗[F] E) * y) k = (N : R) * cK R b y k := by
  have e : (N : R ⊗[F] E) = (N : R) ⊗ₜ[F] (1 : E) := by
    exact (map_natCast (algebraMap R (R ⊗[F] E)) N).symm
  rw [e, cK_tmul_mul]

end Coord

section Scale

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

/- English proof (translation)
Use `set p : ℕ := Ideal.absNorm v.asIdeal with hp`. Establish `hp0 : 0 < p` using `Nat.pos_of_ne_zero fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)`. Establish `hp1 : Valued.v (p : Fv F v) < 1`. Establish `h1 : ((p : 𝓞 F)) ∈ v.asIdeal`. Simplify `Ideal.absNorm_mem v.asIdeal` using `[hp]`.

Establish `h2` using `(v.valuation_lt_one_iff_mem (K := F) (p : 𝓞 F)).2 h1`. Establish `h3 : (p : Fv F v) = algebraMap (𝓞 F) (Fv F v) (p : 𝓞 F)` using `(map_natCast _ p).symm`. Rewrite using `[h3]`. Conclude with `(HeightOneSpectrum.valuedAdicCompletion_eq_valuation v (p : 𝓞 F)).trans_lt h2`. Establish `hO : IsOpen {t : Fv F v | Valued.v t ≤ 1}` using `Valued.isOpen_integer (Fv F v)`.

Establish `hopen : ∀ k : ℕ, IsOpen {t : Fv F v | Valued.v ((p : Fv F v) ^ k * t) ≤ 1}` using `fun k => hO.preimage (continuous_const.mul continuous_id)`. Take `⟨k, hk⟩` from `hQ.elim_directed_cover (fun k : ℕ => {t : Fv F v | Valued.v ((p : Fv F v) ^ k * t) ≤ 1}) hopen (fun t _ => by`. Distinguish the cases in `ht : t = 0`. Conclude with `Set.mem_iUnion.2 ⟨0, by simp [ht]⟩`. Establish `hvt : Valued.v t ≠ 0` using `(Valuation.ne_zero_iff _).2 ht`.

Take `⟨n, hn⟩` from `exists_pow_lt₀ hp1 (Units.mk0 _ (inv_ne_zero hvt))`. Use `Set.mem_iUnion.2 ⟨n, ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq, map_mul, map_pow]`. Conclude with `(mul_le_mul' hn.le le_rfl).trans (inv_mul_cancel₀ hvt).le)`. Use the proof step `(directed_of_isDirected_le fun i j hij t ht => by`.

Simplify using `only [Set.mem_setOf_eq] at ht ⊢`. Rewrite using `[← Nat.sub_add_cancel hij, pow_add, mul_assoc, map_mul, map_pow]`. Conclude with `mul_le_one' (pow_le_one' hp1.le _) ht)`. Conclude with `⟨p ^ k, pow_pos hp0 k, fun t ht => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 (by`. Rewrite using `[Nat.cast_pow]`.

Conclude with `hk ht)⟩`.
-/
theorem scale_one (v : HeightOneSpectrum (𝓞 F)) (Q : Set (Fv F v)) (hQ : IsCompact Q) :
    ∃ N : ℕ, 0 < N ∧ ∀ t ∈ Q, (N : Fv F v) * t ∈ v.adicCompletionIntegers F := by
  set p : ℕ := Ideal.absNorm v.asIdeal with hp
  have hp0 : 0 < p := Nat.pos_of_ne_zero fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hp1 : Valued.v (p : Fv F v) < 1 := by
    have h1 : ((p : 𝓞 F)) ∈ v.asIdeal := by
      simpa [hp] using Ideal.absNorm_mem v.asIdeal
    have h2 := (v.valuation_lt_one_iff_mem (K := F) (p : 𝓞 F)).2 h1
    have h3 : (p : Fv F v) = algebraMap (𝓞 F) (Fv F v) (p : 𝓞 F) := (map_natCast _ p).symm
    rw [h3]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation v (p : 𝓞 F)).trans_lt h2
  have hO : IsOpen {t : Fv F v | Valued.v t ≤ 1} := Valued.isOpen_integer (Fv F v)
  have hopen : ∀ k : ℕ, IsOpen {t : Fv F v | Valued.v ((p : Fv F v) ^ k * t) ≤ 1} := fun k =>
    hO.preimage (continuous_const.mul continuous_id)
  obtain ⟨k, hk⟩ := hQ.elim_directed_cover (fun k : ℕ => {t : Fv F v | Valued.v ((p : Fv F v) ^ k * t) ≤ 1}) hopen
    (fun t _ => by
      by_cases ht : t = 0
      · exact Set.mem_iUnion.2 ⟨0, by simp [ht]⟩
      · have hvt : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).2 ht
        obtain ⟨n, hn⟩ := exists_pow_lt₀ hp1 (Units.mk0 _ (inv_ne_zero hvt))
        refine Set.mem_iUnion.2 ⟨n, ?_⟩
        simp only [Set.mem_setOf_eq, map_mul, map_pow]
        exact (mul_le_mul' hn.le le_rfl).trans (inv_mul_cancel₀ hvt).le)
    (directed_of_isDirected_le fun i j hij t ht => by
      simp only [Set.mem_setOf_eq] at ht ⊢
      rw [← Nat.sub_add_cancel hij, pow_add, mul_assoc, map_mul, map_pow]
      exact mul_le_one' (pow_le_one' hp1.le _) ht)
  exact ⟨p ^ k, pow_pos hp0 k, fun t ht => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 (by
    rw [Nat.cast_pow]
    exact hk ht)⟩

/- English proof (translation)
Take `⟨_, _, _, _, -⟩` from `GlobalTheory.T.completion_is_local_ring F v`. Establish `hh` using `(GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Fv F v)).2.2.2.2.2.2.1 d b`. Establish `hc : ∀ q : Fin 1 × Fin 1 × Fin d, Continuous fun Y : Fin 1 → Fin 1 → Fv F v ⊗[F] E => cK (Fv F v) b (Y q.1 q.2.1) q.2.2` using `fun q => (continuous_apply q.2.2).comp (hh.continuous.comp (continuous_apply_apply q.1 q.2.1))`. Use `choose n hn0 hn using fun q => scale_one v _ (hK.image (hc q))`. Use `⟨∏ q, n q, Finset.prod_pos fun q _ => hn0 q, fun Y hY a i k => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `cK (Fv F v) b (((∏ q, n q : ℕ) : Fv F v ⊗[F] E) * Y a i) k ∈ _`. Rewrite using `[cK_nat_mul]`. Take `⟨c, hc'⟩` from `Finset.dvd_prod_of_mem n (Finset.mem_univ (a, i, k))`. Rewrite using `[hc']`. Establish `h1` using `hn (a, i, k) _ ⟨Y, hY, rfl⟩`.

Establish `e : ((n (a, i, k) * c : ℕ) : Fv F v) * cK (Fv F v) b (Y a i) k = (c : Fv F v) * ((n (a, i, k) : Fv F v) * cK (Fv F v) b (Y a i) k)` using `by push_cast; ring`. Rewrite using `[e]`. Conclude with `mul_mem (natCast_mem _ c) h1`.
-/
theorem scale_lat [NumberField E] (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (K : Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) (hK : IsCompact K) :
    ∃ N : ℕ, 0 < N ∧ ∀ Y ∈ K, (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v := by
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  have hh := (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Fv F v)).2.2.2.2.2.2.1 d b
  have hc : ∀ q : Fin 1 × Fin 1 × Fin d, Continuous fun Y : Fin 1 → Fin 1 → Fv F v ⊗[F] E => cK (Fv F v) b (Y q.1 q.2.1) q.2.2 :=
    fun q => (continuous_apply q.2.2).comp (hh.continuous.comp (continuous_apply_apply q.1 q.2.1))
  choose n hn0 hn using fun q => scale_one v _ (hK.image (hc q))
  refine ⟨∏ q, n q, Finset.prod_pos fun q _ => hn0 q, fun Y hY a i k => ?_⟩
  change cK (Fv F v) b (((∏ q, n q : ℕ) : Fv F v ⊗[F] E) * Y a i) k ∈ _
  rw [cK_nat_mul]
  obtain ⟨c, hc'⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ (a, i, k))
  rw [hc']
  have h1 := hn (a, i, k) _ ⟨Y, hY, rfl⟩
  have e : ((n (a, i, k) * c : ℕ) : Fv F v) * cK (Fv F v) b (Y a i) k =
      (c : Fv F v) * ((n (a, i, k) : Fv F v) * cK (Fv F v) b (Y a i) k) := by
    push_cast; ring
  rw [e]
  exact mul_mem (natCast_mem _ c) h1

/- English proof (translation)
Introduce `a i k` and use `by change cK (Fv F v) b ((N : Fv F v ⊗[F] E) * Y a i) k ∈ _ rw [cK_nat_mul] exact mul_mem (natCast_mem _ N) (hY a i k)`.
-/
theorem nat_mul_latV {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (N : ℕ)
    {Y : Fin 1 → Fin 1 → Fv F v ⊗[F] E} (hY : Y ∈ latV b v) :
    (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v := fun a i k => by
  change cK (Fv F v) b ((N : Fv F v ⊗[F] E) * Y a i) k ∈ _
  rw [cK_nat_mul]
  exact mul_mem (natCast_mem _ N) (hY a i k)

end Scale

/- English proof (translation)
Take `⟨hφc, hφs, hφ0, -, hAS, hAoff⟩` from `hT`. Take `⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩` from `GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 1`. Take `⟨u1, u2⟩` from `GlobalTheory.T.adelic_tuple_compact_sets F E σ hcm d b 1 1`. Establish `hSc : ∀ v, ∃ N : ℕ, 0 < N ∧ (v ∈ S → ∀ Y ∈ A v, (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v)` using `fun v => by`. Distinguish the cases in `hv : v ∈ S`.

Take `⟨N, h0, h1⟩` from `scale_lat σ hcm b v (A v) (hAS v hv).1`. Conclude with `⟨N, h0, fun _ => h1⟩`. Conclude with `⟨1, one_pos, fun h => absurd h hv⟩`. Use `choose n hn0 hn using hSc`. Use `set N1 : ℕ := ∏ v ∈ S, n v with hN1`.

Establish `hN1p : 0 < N1` using `Finset.prod_pos fun v _ => hn0 v`. Establish `hsc : ∀ v, ∀ Y ∈ A v, (fun a i => (N1 : Fv F v ⊗[F] E) * Y a i) ∈ latV b v` using `fun v Y hY => by`. Distinguish the cases in `hv : v ∈ S`. Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem n hv`. Establish `h1` using `nat_mul_latV b v c (hn v hv Y hY)`.

Establish `e : (fun a i => (N1 : Fv F v ⊗[F] E) * Y a i) = fun a i => (c : Fv F v ⊗[F] E) * ((n v : Fv F v ⊗[F] E) * Y a i)`. Use function extensionality and compare the values at `a i`. Rewrite using `[hN1, hc]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `h1`. Rewrite `hY` using `[hAoff v hv]`. Conclude with `nat_mul_latV b v N1 hY`. Take `⟨r1, hr1⟩` from `(IsCompact.image hφs t9).bddAbove`.

Use `⟨_, u1 N1 r1 hN1p, fun Y hY hs => ⟨fun v => hsc v _ (hY v), hr1 ⟨_, hs, rfl⟩⟩⟩` and prove the remaining obligations.
-/
theorem exists_compact {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (J : Matrix (Fin 1) (Fin 1) E) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) (hT : IsTest σ J b S φ A) :
    ∃ K : Set (Fin 1 → Fin 1 → AF F ⊗[F] E), IsCompact K ∧
      ∀ Y : Fin 1 → Fin 1 → AF F ⊗[F] E, (∀ v, projV v (projFin Y) ∈ A v) → projInf Y ∈ tsupport φ → Y ∈ K := by
  obtain ⟨hφc, hφs, hφ0, -, hAS, hAoff⟩ := hT
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 1
  obtain ⟨u1, u2⟩ := GlobalTheory.T.adelic_tuple_compact_sets F E σ hcm d b 1 1
  have hSc : ∀ v, ∃ N : ℕ, 0 < N ∧ (v ∈ S → ∀ Y ∈ A v, (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v) := fun v => by
    by_cases hv : v ∈ S
    · obtain ⟨N, h0, h1⟩ := scale_lat σ hcm b v (A v) (hAS v hv).1
      exact ⟨N, h0, fun _ => h1⟩
    · exact ⟨1, one_pos, fun h => absurd h hv⟩
  choose n hn0 hn using hSc
  set N1 : ℕ := ∏ v ∈ S, n v with hN1
  have hN1p : 0 < N1 := Finset.prod_pos fun v _ => hn0 v
  have hsc : ∀ v, ∀ Y ∈ A v, (fun a i => (N1 : Fv F v ⊗[F] E) * Y a i) ∈ latV b v := fun v Y hY => by
    by_cases hv : v ∈ S
    · obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n hv
      have h1 := nat_mul_latV b v c (hn v hv Y hY)
      have e : (fun a i => (N1 : Fv F v ⊗[F] E) * Y a i) = fun a i => (c : Fv F v ⊗[F] E) * ((n v : Fv F v ⊗[F] E) * Y a i) := by
        funext a i
        rw [hN1, hc]
        push_cast
        ring
      rw [e]
      exact h1
    · rw [hAoff v hv] at hY
      exact nat_mul_latV b v N1 hY
  obtain ⟨r1, hr1⟩ := (IsCompact.image hφs t9).bddAbove
  refine ⟨_, u1 N1 r1 hN1p, fun Y hY hs => ⟨fun v => hsc v _ (hY v), hr1 ⟨_, hs, rfl⟩⟩⟩

/- English proof (translation)
Unfold `Psi at h`. Distinguish the cases in `h1 : ∀ v, projV v (projFin Y) ∈ A v`. Use `⟨h1, subset_tsupport φ ?_⟩` and prove the remaining obligations. Rewrite `h` using `[Set.indicator_of_mem (by exact h1)]`. Introduce `h2`.

Conclude with `h (by simp [h2])`. Rewrite `h` using `[Set.indicator_of_notMem (by exact h1)]`. Conclude with `absurd rfl h`.
-/
theorem mem_of_Psi_ne {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E))
    (Y : Fin 1 → Fin 1 → AF F ⊗[F] E) (h : Psi φ A Y ≠ 0) :
    (∀ v, projV v (projFin Y) ∈ A v) ∧ projInf Y ∈ tsupport φ := by
  unfold Psi at h
  by_cases h1 : ∀ v, projV v (projFin Y) ∈ A v
  · refine ⟨h1, subset_tsupport φ ?_⟩
    rw [Set.indicator_of_mem (by exact h1)] at h
    intro h2
    exact h (by simp [h2])
  · rw [Set.indicator_of_notMem (by exact h1)] at h
    exact absurd rfl h

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
The claim follows from `GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv.comp (continuous_apply_apply 0 0)`.
-/
theorem cont_f : Continuous fun Y : Fin 1 → Fin 1 → AF F ⊗[F] E => GroundTheory.BlockD.ThmBHecke.adeleEquiv F E (Y 0 0) :=
    GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv.comp (continuous_apply_apply 0 0)

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Conclude with `GroundTheory.BlockD.ThmBHecke.adeleEquiv_incA (t : E)`.
-/
theorem hdiag (t : Eˣ) : GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (ofE t) = IdeleGroup.diagonal E t := by
    apply Units.ext
    exact GroundTheory.BlockD.ThmBHecke.adeleEquiv_incA (t : E)

/- English proof (translation)
Rewrite using `[map_mul, map_mul, hdiag, IdeleGroup.ideleModule_diagonal, mul_one]`.
-/
theorem mod_mul (y : (AF F ⊗[F] E)ˣ) (t : Eˣ) : (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (y * ofE t)) : ℝ) = (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E y) : ℝ) := by
  rw [map_mul, map_mul, hdiag, IdeleGroup.ideleModule_diagonal, mul_one]

/- English proof (translation)
Unfold `Th at h`. Take `⟨X, hX⟩` from `not_forall.1 (fun hall => h (ENNReal.tsum_eq_zero.2 hall))`. Conclude with `⟨X.1, X.2, hX⟩`.
-/
theorem exists_term (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) (y : (AF F ⊗[F] E)ˣ)
    (h : Th φ A y ≠ 0) : ∃ X : Fin 1 → Fin 1 → E, X ≠ 0 ∧
      Psi φ A (fun a i => (y : AF F ⊗[F] E) * inclR (AF F) (X a i)) ≠ 0 := by
  unfold Th at h
  obtain ⟨X, hX⟩ := not_forall.1 (fun hall => h (ENNReal.tsum_eq_zero.2 hall))
  exact ⟨X.1, X.2, hX⟩

/- English proof (translation)
Introduce `h0` and use `h (by funext a i rw [Subsingleton.elim a 0, Subsingleton.elim i 0, h0] rfl)`.
-/
theorem entry_ne {X : Fin 1 → Fin 1 → E} (h : X ≠ 0) : X 0 0 ≠ 0 := fun h0 => h (by
  funext a i
  rw [Subsingleton.elim a 0, Subsingleton.elim i 0, h0]
  rfl)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_eq (y : (AF F ⊗[F] E)ˣ) {X : Fin 1 → Fin 1 → E} (h : X 0 0 ≠ 0) :
    ((GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (y * ofE (Units.mk0 _ h)) : IdeleGroup E) : AdeleRing (𝓞 E) E) =
      GroundTheory.BlockD.ThmBHecke.adeleEquiv F E ((y : AF F ⊗[F] E) * inclR (AF F) (X 0 0)) := rfl
end

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm J hJ d b S φ A hT`. Take `⟨K, hK, hmem⟩` from `exists_compact σ hcm J b S φ A hT`. Take `⟨R, hR⟩` from `GlobalTheory.T.idele_module_bounded_on_compact E _ (hK.image (cont_f (F := F) (E := E)))`. Use `⟨R, fun y n hn hlt => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Take `⟨X, hX0, hX⟩` from `exists_term φ A y hne`. Take `⟨h1, h2⟩` from `mem_of_Psi_ne φ A _ hX`. Establish `hYK` using `hmem _ h1 h2`. Establish `ht` using `entry_ne hX0`. Establish `hle` using `hR (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (y * ofE (Units.mk0 _ ht))) (by rw [coe_eq]; exact ⟨_, hYK, rfl⟩)`.

Rewrite `hle` using `[mod_mul, GlobalTheory.T.idele_module_eq_norm_module F E σ hcm y n hn]`. Conclude with `absurd hle (not_le.2 hlt)`.
-/
theorem th_eq_zero_of_large_module : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A → ∃ R : ℝ, ∀ (y : (AF F ⊗[F] E)ˣ) (n : (AF F)ˣ), IsNm σ y n → R < md n → Th φ A y = 0 := by
  intro F E _ _ _ _ _ σ hcm J hJ d b S φ A hT
  obtain ⟨K, hK, hmem⟩ := exists_compact σ hcm J b S φ A hT
  obtain ⟨R, hR⟩ := GlobalTheory.T.idele_module_bounded_on_compact E _ (hK.image (cont_f (F := F) (E := E)))
  refine ⟨R, fun y n hn hlt => ?_⟩
  by_contra hne
  obtain ⟨X, hX0, hX⟩ := exists_term φ A y hne
  obtain ⟨h1, h2⟩ := mem_of_Psi_ne φ A _ hX
  have hYK := hmem _ h1 h2
  have ht := entry_ne hX0
  have hle := hR (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (y * ofE (Units.mk0 _ ht)))
    (by rw [coe_eq]; exact ⟨_, hYK, rfl⟩)
  rw [mod_mul, GlobalTheory.T.idele_module_eq_norm_module F E σ hcm y n hn] at hle
  exact absurd hle (not_le.2 hlt)

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Vanish

end
