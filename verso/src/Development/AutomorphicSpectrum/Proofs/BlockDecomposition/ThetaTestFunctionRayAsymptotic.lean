import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Box

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

/- English proof (translation)
Simplify using `[cK, inclR, Algebra.TensorProduct.basis_repr_tmul, Algebra.algebraMap_eq_smul_one]`.
-/
theorem cK_incl (e : E) (k : Fin d) : cK R b (inclR R e) k = algebraMap F R (b.repr e k) := by
  simp [cK, inclR, Algebra.TensorProduct.basis_repr_tmul, Algebra.algebraMap_eq_smul_one]

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

/- English proof (translation)
Express the relevant statement in the definitionally equal form `((u : AF F) ⊗ₜ[F] (1 : E)) * ((1 : AF F) ⊗ₜ[F] e) = _`. Simplify using `[Algebra.TensorProduct.tmul_mul_tmul]`.
-/
theorem ofF_mul_incl (u : (AF F)ˣ) (e : E) :
    ((ofF u : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * inclR (AF F) e = (u : AF F) ⊗ₜ[F] e := by
  change ((u : AF F) ⊗ₜ[F] (1 : E)) * ((1 : AF F) ⊗ₜ[F] e) = _
  simp [Algebra.TensorProduct.tmul_mul_tmul]

/- English proof (translation)
Use function extensionality and compare the values at `a i`. Establish `h1 : sndA F (u : AF F) = 1` using `hu`. Express the relevant statement in the definitionally equal form `Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (((ofF u : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * inclR (AF F) (X a i))) = (1 : Fv F v) ⊗ₜ[F] X a i`. Rewrite using `[ofF_mul_incl]`. Simplify using `only [Algebra.TensorProduct.map_tmul, h1, map_one, AlgHom.id_apply]`.
-/
theorem projV_ofF (u : (AF F)ˣ) (hu : (u : AF F).2 = 1) (v : HeightOneSpectrum (𝓞 F)) (X : Fin 1 → Fin 1 → E) :
    projV v (projFin fun a i => ((ofF u : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * inclR (AF F) (X a i)) =
      ratTup (Fv F v) X := by
  funext a i
  have h1 : sndA F (u : AF F) = 1 := hu
  change Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)
    (((ofF u : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * inclR (AF F) (X a i))) = (1 : Fv F v) ⊗ₜ[F] X a i
  rw [ofF_mul_incl]
  simp only [Algebra.TensorProduct.map_tmul, h1, map_one, AlgHom.id_apply]

/- English proof (translation)
Use function extensionality and compare the values at `a i`. Establish `h1 : fstA F (u : AF F) = t` using `hu`. Express the relevant statement in the definitionally equal form `Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (((ofF u : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * inclR (AF F) (X a i)) = (t ⊗ₜ[F] (1 : E)) * ((1 : Ainf F) ⊗ₜ[F] X a i)`. Rewrite using `[ofF_mul_incl]`. Simplify using `[Algebra.TensorProduct.map_tmul, h1, Algebra.TensorProduct.tmul_mul_tmul]`.
-/
theorem projInf_ofF (u : (AF F)ˣ) (t : Ainf F) (hu : (u : AF F).1 = t) (X : Fin 1 → Fin 1 → E) :
    projInf (fun a i => ((ofF u : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * inclR (AF F) (X a i)) =
      fun a i => (t ⊗ₜ[F] (1 : E)) * ratTup (Ainf F) X a i := by
  funext a i
  have h1 : fstA F (u : AF F) = t := hu
  change Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)
    (((ofF u : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * inclR (AF F) (X a i)) = (t ⊗ₜ[F] (1 : E)) * ((1 : Ainf F) ⊗ₜ[F] X a i)
  rw [ofF_mul_incl]
  simp [Algebra.TensorProduct.map_tmul, h1, Algebra.TensorProduct.tmul_mul_tmul]

end Scale

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm J hJ d b θ r hray S φ A hT K hK`. Take `⟨hφc, hφs, hφ0, -, hAS, hAoff⟩` from `hT`. Take `⟨⟨_, _, _⟩, -⟩` from `GlobalTheory.T.adeles_locally_compact_second_countable F`. Take `⟨_, _, _, _, -, -, -, hB, -, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)`. Take `⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩` from `GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 1`.

Take `⟨u1, u2⟩` from `GlobalTheory.T.adelic_tuple_compact_sets F E σ hcm d b 1 1`. Establish `hSc : ∀ v, ∃ N : ℕ, 0 < N ∧ (v ∈ S → ∀ Y ∈ A v, (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v)` using `fun v => by`. Distinguish the cases in `hv : v ∈ S`. Take `⟨N, h0, h1⟩` from `scale_lat σ hcm b v (A v) (hAS v hv).1`. Conclude with `⟨N, h0, fun _ => h1⟩`.

Conclude with `⟨1, one_pos, fun h => absurd h hv⟩`. Use `choose n hn0 hn using hSc`. Use `set N1 : ℕ := ∏ v ∈ S, n v with hN1`. Establish `hN1p : 0 < N1` using `Finset.prod_pos fun v _ => hn0 v`. Establish `hsc : ∀ v, ∀ Y ∈ A v, (fun a i => (N1 : Fv F v ⊗[F] E) * Y a i) ∈ latV b v` using `fun v Y hY => by`.

Distinguish the cases in `hv : v ∈ S`. Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem n hv`. Establish `h1` using `nat_mul_latV b v c (hn v hv Y hY)`. Establish `e : (fun a i => (N1 : Fv F v ⊗[F] E) * Y a i) = fun a i => (c : Fv F v ⊗[F] E) * ((n v : Fv F v ⊗[F] E) * Y a i)`. Use function extensionality and compare the values at `a i`.

Rewrite using `[hN1, hc]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `h1`.

Rewrite `hY` using `[hAoff v hv]`. Conclude with `nat_mul_latV b v N1 hY`. Take `⟨r1, hr1⟩` from `(IsCompact.image hφs t9).bddAbove`. Establish `hK1` using `u1 N1 r1 hN1p`. Use `set K1 := {X : Fin 1 → Fin 1 → AF F ⊗[F] E | (∀ v, (fun a i => (N1 : Fv F v ⊗[F] E) * projV v (projFin X) a i) ∈ latV b v) ∧ sizeTup b (projInf X) ≤ r1} with hK1d`.

Establish `hcont : Continuous (fun q : (AF F ⊗[F] E)ˣ × (Fin 1 → Fin 1 → AF F ⊗[F] E) => (fun a i => (q.1 : AF F ⊗[F] E) * q.2 a i : Fin 1 → Fin 1 → AF F ⊗[F] E))` using `continuous_pi fun a => continuous_pi fun i => (Units.continuous_val.comp continuous_fst).mul ((continuous_apply_apply a i).comp continuous_snd)`. Establish `hK2 : IsCompact ((fun q : (AF F ⊗[F] E)ˣ × (Fin 1 → Fin 1 → AF F ⊗[F] E) => (fun a i => (q.1 : AF F ⊗[F] E) * q.2 a i : Fin 1 → Fin 1 → AF F ⊗[F] E)) '' (K⁻¹ ×ˢ K1))` using `(hK.inv.prod hK1).image hcont`. Take `⟨N, ρ, hN, hρ, hsub⟩` from `u2 _ hK2`. Use `⟨N, N * ρ, hN, fun k hk X ε hε hne => ?_⟩` and prove the remaining obligations. Use `set Y : Fin 1 → Fin 1 → AF F ⊗[F] E := fun a i => ((k * ofF (r ε) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * inclR (AF F) (X a i) with hY`.

Establish `hmem : (∀ v, projV v (projFin Y) ∈ A v) ∧ φ (projInf Y) ≠ 0`. Assume the negation of the conclusion as `hcon`. Apply `hne` to reduce the goal to its premises. Unfold `Psi`. Distinguish the cases in `h1 : ∀ v, projV v (projFin Y) ∈ A v`.

Rewrite using `[Set.indicator_of_mem (by exact h1)]`. Establish `h2 : φ (projInf Y) = 0`. Assume the negation of the conclusion as `h2`. Conclude with `hcon ⟨h1, h2⟩`. Simplify using `[h2]`.

Rewrite using `[Set.indicator_of_notMem (by exact h1)]`. Take `⟨hmv, hφne⟩` from `hmem`. Establish `hYK : Y ∈ K1` using `⟨fun v => hsc v _ (hmv v), hr1 ⟨_, subset_tsupport φ hφne, rfl⟩⟩`. Use `set W : Fin 1 → Fin 1 → AF F ⊗[F] E := fun a i => ((ofF (r ε) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * inclR (AF F) (X a i) with hW`. Establish `hWY : (fun a i => ((k⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * Y a i) = W`.

Use function extensionality and compare the values at `a i`. Simplify using `only [hY, hW, Units.val_mul, ← mul_assoc, Units.inv_mul, one_mul]`. Take `⟨hW1, hW2⟩` from `hsub W ⟨(k⁻¹, Y), ⟨Set.inv_mem_inv.2 hk, hYK⟩, hWY⟩`. Take `⟨hr1', hr2'⟩` from `hray ε hε`. Establish `hWv : ∀ v, projV v (projFin W) = ratTup (Fv F v) X` using `fun v => projV_ofF _ hr2' v X`.

Establish `hWinf : projInf W = fun a i => (θ ε ⊗ₜ[F] (1 : E)) * ratTup (Ainf F) X a i` using `projInf_ofF _ _ hr1' X`. Simplify using `only [hWv, hWinf] at hW1 hW2`. Use `⟨fun q v => ?_, fun q w => ?_⟩` and prove the remaining obligations. Establish `h1` using `hW1 v q.1 q.2.1 q.2.2`. Express the relevant statement in the definitionally equal form `cK (Fv F v) b ((N : Fv F v ⊗[F] E) * ratTup (Fv F v) X q.1 q.2.1) q.2.2 ∈ _ at h1`.

Rewrite `h1` using `[cK_nat_mul, ratTup, cK_incl]`. Rewrite using `[map_mul, map_natCast]` and apply the resulting hypothesis. Establish `e1 : θ ε * algebraMap F (Ainf F) ((N : F) * b.repr (X q.1 q.2.1) q.2.2) = N • (θ ε * algebraMap F (Ainf F) (b.repr (X q.1 q.2.1) q.2.2))`. Rewrite using `[map_mul, map_natCast, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Use `set D : Fin 1 → Fin 1 → Ainf F ⊗[F] E := fun a i => (θ ε ⊗ₜ[F] (1 : E)) * ratTup (Ainf F) X a i with hD`. Establish `h2 : ‖(θ ε * algebraMap F (Ainf F) (b.repr (X q.1 q.2.1) q.2.2)) w‖ ≤ ρ`. Use `le_trans ?_ hW2` and prove the remaining obligations. Establish `e2 : (Algebra.TensorProduct.basis (Ainf F) b).repr (D q.1 q.2.1) q.2.2 = θ ε * algebraMap F (Ainf F) (b.repr (X q.1 q.2.1) q.2.2)`. Express the relevant statement in the definitionally equal form `cK (Ainf F) b ((θ ε ⊗ₜ[F] (1 : E)) * ratTup (Ainf F) X q.1 q.2.1) q.2.2 = _`.

Rewrite using `[cK_tmul_mul, ratTup, cK_incl]`. Rewrite using `[← e2, sizeTup]`. Establish `n0 : ∀ (y : Ainf F ⊗[F] E), 0 ≤ sizeInf b y` using `fun y => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e1]`.

Express the relevant statement in the definitionally equal form `‖N • ((θ ε * algebraMap F (Ainf F) (b.repr (X q.1 q.2.1) q.2.2)) w)‖ ≤ _`. Conclude with `(norm_nsmul_le ..).trans (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg N))`.
-/
theorem unit_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (θ : ℝ →+* Ainf F) (r : ℝ → (AF F)ˣ), IsRay θ r → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A → ∀ K : Set (AF F ⊗[F] E)ˣ, IsCompact K → ∃ (N : ℕ) (ρ : ℝ), 0 < N ∧ ∀ k ∈ K, ∀ (X : Fin 1 → Fin 1 → E) (ε : ℝ), 0 < ε → Psi φ A (fun a i => ((k * ofF (r ε) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * inclR (AF F) (X a i)) ≠ 0 → (∀ (p : Fin 1 × Fin 1 × Fin d) (v : HeightOneSpectrum (𝓞 F)), algebraMap F (Fv F v) ((N : F) * b.repr (X p.1 p.2.1) p.2.2) ∈ v.adicCompletionIntegers F) ∧ ∀ (p : Fin 1 × Fin 1 × Fin d) (w : InfinitePlace F), ‖(θ ε * algebraMap F (Ainf F) ((N : F) * b.repr (X p.1 p.2.1) p.2.2)) w‖ ≤ ρ := by
  intro F E _ _ _ _ _ σ hcm J hJ d b θ r hray S φ A hT K hK
  obtain ⟨hφc, hφs, hφ0, -, hAS, hAoff⟩ := hT
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
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
  have hK1 := u1 N1 r1 hN1p
  set K1 := {X : Fin 1 → Fin 1 → AF F ⊗[F] E | (∀ v, (fun a i => (N1 : Fv F v ⊗[F] E) * projV v (projFin X) a i) ∈ latV b v) ∧
    sizeTup b (projInf X) ≤ r1} with hK1d
  have hcont : Continuous (fun q : (AF F ⊗[F] E)ˣ × (Fin 1 → Fin 1 → AF F ⊗[F] E) =>
      (fun a i => (q.1 : AF F ⊗[F] E) * q.2 a i : Fin 1 → Fin 1 → AF F ⊗[F] E)) :=
    continuous_pi fun a => continuous_pi fun i =>
      (Units.continuous_val.comp continuous_fst).mul ((continuous_apply_apply a i).comp continuous_snd)
  have hK2 : IsCompact ((fun q : (AF F ⊗[F] E)ˣ × (Fin 1 → Fin 1 → AF F ⊗[F] E) =>
      (fun a i => (q.1 : AF F ⊗[F] E) * q.2 a i : Fin 1 → Fin 1 → AF F ⊗[F] E)) '' (K⁻¹ ×ˢ K1)) :=
    (hK.inv.prod hK1).image hcont
  obtain ⟨N, ρ, hN, hρ, hsub⟩ := u2 _ hK2
  refine ⟨N, N * ρ, hN, fun k hk X ε hε hne => ?_⟩
  set Y : Fin 1 → Fin 1 → AF F ⊗[F] E := fun a i =>
    ((k * ofF (r ε) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * inclR (AF F) (X a i) with hY
  have hmem : (∀ v, projV v (projFin Y) ∈ A v) ∧ φ (projInf Y) ≠ 0 := by
    by_contra hcon
    apply hne
    unfold Psi
    by_cases h1 : ∀ v, projV v (projFin Y) ∈ A v
    · rw [Set.indicator_of_mem (by exact h1)]
      have h2 : φ (projInf Y) = 0 := by
        by_contra h2
        exact hcon ⟨h1, h2⟩
      simp [h2]
    · rw [Set.indicator_of_notMem (by exact h1)]
  obtain ⟨hmv, hφne⟩ := hmem
  have hYK : Y ∈ K1 := ⟨fun v => hsc v _ (hmv v), hr1 ⟨_, subset_tsupport φ hφne, rfl⟩⟩
  set W : Fin 1 → Fin 1 → AF F ⊗[F] E := fun a i =>
    ((ofF (r ε) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * inclR (AF F) (X a i) with hW
  have hWY : (fun a i => ((k⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * Y a i) = W := by
    funext a i
    simp only [hY, hW, Units.val_mul, ← mul_assoc, Units.inv_mul, one_mul]
  obtain ⟨hW1, hW2⟩ := hsub W ⟨(k⁻¹, Y), ⟨Set.inv_mem_inv.2 hk, hYK⟩, hWY⟩
  obtain ⟨hr1', hr2'⟩ := hray ε hε
  have hWv : ∀ v, projV v (projFin W) = ratTup (Fv F v) X := fun v => projV_ofF _ hr2' v X
  have hWinf : projInf W = fun a i => (θ ε ⊗ₜ[F] (1 : E)) * ratTup (Ainf F) X a i := projInf_ofF _ _ hr1' X
  simp only [hWv, hWinf] at hW1 hW2
  refine ⟨fun q v => ?_, fun q w => ?_⟩
  · have h1 := hW1 v q.1 q.2.1 q.2.2
    change cK (Fv F v) b ((N : Fv F v ⊗[F] E) * ratTup (Fv F v) X q.1 q.2.1) q.2.2 ∈ _ at h1
    rw [cK_nat_mul, ratTup, cK_incl] at h1
    rwa [map_mul, map_natCast]
  · have e1 : θ ε * algebraMap F (Ainf F) ((N : F) * b.repr (X q.1 q.2.1) q.2.2) =
        N • (θ ε * algebraMap F (Ainf F) (b.repr (X q.1 q.2.1) q.2.2)) := by
      rw [map_mul, map_natCast, nsmul_eq_mul]
      ring
    set D : Fin 1 → Fin 1 → Ainf F ⊗[F] E := fun a i => (θ ε ⊗ₜ[F] (1 : E)) * ratTup (Ainf F) X a i with hD
    have h2 : ‖(θ ε * algebraMap F (Ainf F) (b.repr (X q.1 q.2.1) q.2.2)) w‖ ≤ ρ := by
      refine le_trans ?_ hW2
      have e2 : (Algebra.TensorProduct.basis (Ainf F) b).repr (D q.1 q.2.1) q.2.2 =
          θ ε * algebraMap F (Ainf F) (b.repr (X q.1 q.2.1) q.2.2) := by
        change cK (Ainf F) b ((θ ε ⊗ₜ[F] (1 : E)) * ratTup (Ainf F) X q.1 q.2.1) q.2.2 = _
        rw [cK_tmul_mul, ratTup, cK_incl]
      rw [← e2, sizeTup]
      have n0 : ∀ (y : Ainf F ⊗[F] E), 0 ≤ sizeInf b y := fun y =>
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
      calc _ ≤ ∑ v : InfinitePlace F, ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (D q.1 q.2.1) q.2.2 v‖ :=
            Finset.single_le_sum (f := fun v : InfinitePlace F => ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (D q.1 q.2.1) q.2.2 v‖)
              (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
        _ ≤ sizeInf b (D q.1 q.2.1) :=
            Finset.single_le_sum (f := fun k => ∑ v : InfinitePlace F, ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (D q.1 q.2.1) k v‖)
              (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ q.2.2)
        _ ≤ ∑ i, sizeInf b (D q.1 i) :=
            Finset.single_le_sum (f := fun i => sizeInf b (D q.1 i)) (fun _ _ => n0 _) (Finset.mem_univ q.2.1)
        _ ≤ ∑ a, ∑ i, sizeInf b (D a i) :=
            Finset.single_le_sum (f := fun a => ∑ i, sizeInf b (D a i))
              (fun _ _ => Finset.sum_nonneg fun _ _ => n0 _) (Finset.mem_univ q.1)
    rw [e1]
    change ‖N • ((θ ε * algebraMap F (Ainf F) (b.repr (X q.1 q.2.1) q.2.2)) w)‖ ≤ _
    exact (norm_nsmul_le ..).trans (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg N))

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Box

end
