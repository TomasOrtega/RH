import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardEmbeddedHermDataIndexLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscriminantOrderCommonFixedLatticeEmbeddedDataStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardIsometriesFixingSubspaceDefiniteLatticesLeStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.PairNoFix

/- English proof (translation)
Rewrite using `[← ENNReal.tsum_set_one S, ← ENNReal.tsum_set_const, ← ENNReal.tsum_fiberwise (fun _ : S => (1 : ℝ≥0∞)) (fun a : S => (⟨f a, hf a a.2⟩ : T))]`. Use `ENNReal.tsum_le_tsum fun b => ?_` and prove the remaining obligations. Rewrite using `[ENNReal.tsum_set_one]`. Use `le_trans ?_ (hc b b.2)` and prove the remaining obligations. Rewrite using `[← (Subtype.val_injective.encard_image _)]`.

Use `ENat.toENNReal_le.2 (Set.encard_le_encard ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Conclude with `⟨a.2, congrArg Subtype.val ha⟩`.
-/
theorem encard_le_of_fibres {α β : Type} (S : Set α) (T : Set β) (f : α → β) (hf : ∀ a ∈ S, f a ∈ T)
    (c : ℝ≥0∞) (hc : ∀ b ∈ T, ((({a ∈ S | f a = b}).encard : ℕ∞) : ℝ≥0∞) ≤ c) :
    ((S.encard : ℕ∞) : ℝ≥0∞) ≤ ((T.encard : ℕ∞) : ℝ≥0∞) * c := by
  rw [← ENNReal.tsum_set_one S, ← ENNReal.tsum_set_const,
    ← ENNReal.tsum_fiberwise (fun _ : S => (1 : ℝ≥0∞)) (fun a : S => (⟨f a, hf a a.2⟩ : T))]
  refine ENNReal.tsum_le_tsum fun b => ?_
  rw [ENNReal.tsum_set_one]
  refine le_trans ?_ (hc b b.2)
  rw [← (Subtype.val_injective.encard_image _)]
  refine ENat.toENNReal_le.2 (Set.encard_le_encard ?_)
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨a.2, congrArg Subtype.val ha⟩

/- English proof (translation)
Substitute `hm` using the available equality. Establish `x0 : 0 < x` using `by linarith`. Establish `x0' : 0 < x'` using `by linarith`. Establish `D0 : 0 < D` using `by linarith`. Establish `h1 : 1 ≤ (x * x') ^ ((k : ℝ) / 2) * (q ^ (k * f) * D) ^ k`.

Establish `hs : ((x * x') ^ ((k : ℝ) / 2)) ^ 2 = (x * x') ^ k`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2 : 1 ≤ ((x * x') ^ ((k : ℝ) / 2) * (q ^ (k * f) * D) ^ k) ^ 2`. Rewrite using `[mul_pow, hs]`. Establish `: (x * x') ^ k * ((q ^ (k * f) * D) ^ k) ^ 2 = (q ^ (2 * k * f) * D * x * x') ^ k * D ^ k`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `one_le_mul_of_one_le_of_one_le (one_le_pow₀ h) (one_le_pow₀ hD)`. Conclude with `(one_le_sq_iff₀ (by positivity)).1 h2`. Establish `h3 : x ^ c * x' ^ c ≤ (x * x' * D ^ 2) ^ c`. Rewrite using `[← Real.mul_rpow x0.le x0'.le]`. Use `Real.rpow_le_rpow (by positivity) ?_ hc` and prove the remaining obligations.

Conclude with `le_mul_of_one_le_right (by positivity) (one_le_pow₀ hD)`. Rewrite using `[Real.rpow_add x0, Real.rpow_add x0', Real.rpow_add (by positivity : 0 < x * x' * D ^ 2)]`. Simplify using `only [Real.rpow_natCast]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem arith (k f : ℕ) (c e : ℝ) (hc : 0 ≤ c) (x x' D q A : ℝ) (hx : 1 ≤ x) (hx' : 1 ≤ x') (hD : 1 ≤ D)
    (hq : 0 < q) (hA : 0 ≤ A) (h : 1 ≤ q ^ (2 * k * f) * D * x * x') (m : ℕ) (hm : (m : ℝ) = e) :
    (x ^ ((k : ℝ) + c) * (x * D) ^ m) * (x' ^ ((k : ℝ) + c) * (x' * D) ^ m) * A ^ (4 * k * f) ≤
      (x * x') ^ ((k : ℝ) / 2) * (x * x' * D ^ 2) ^ (c + e) * (q ^ (k * f) * A ^ (4 * f) * D * x * x') ^ k := by
  subst hm
  have x0 : 0 < x := by linarith
  have x0' : 0 < x' := by linarith
  have D0 : 0 < D := by linarith
  have h1 : 1 ≤ (x * x') ^ ((k : ℝ) / 2) * (q ^ (k * f) * D) ^ k := by
    have hs : ((x * x') ^ ((k : ℝ) / 2)) ^ 2 = (x * x') ^ k := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast]
      congr 1; push_cast; ring
    have h2 : 1 ≤ ((x * x') ^ ((k : ℝ) / 2) * (q ^ (k * f) * D) ^ k) ^ 2 := by
      rw [mul_pow, hs]
      have : (x * x') ^ k * ((q ^ (k * f) * D) ^ k) ^ 2 = (q ^ (2 * k * f) * D * x * x') ^ k * D ^ k := by
        ring
      rw [this]
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ h) (one_le_pow₀ hD)
    exact (one_le_sq_iff₀ (by positivity)).1 h2
  have h3 : x ^ c * x' ^ c ≤ (x * x' * D ^ 2) ^ c := by
    rw [← Real.mul_rpow x0.le x0'.le]
    refine Real.rpow_le_rpow (by positivity) ?_ hc
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hD)
  rw [Real.rpow_add x0, Real.rpow_add x0', Real.rpow_add (by positivity : 0 < x * x' * D ^ 2)]
  simp only [Real.rpow_natCast]
  calc x ^ k * x ^ c * (x * D) ^ m * (x' ^ k * x' ^ c * (x' * D) ^ m) * A ^ (4 * k * f)
      = 1 * (x ^ c * x' ^ c) * ((x * x' * D ^ 2) ^ m * (A ^ (4 * f) * x * x') ^ k) := by ring
    _ ≤ ((x * x') ^ ((k : ℝ) / 2) * (q ^ (k * f) * D) ^ k) * (x * x' * D ^ 2) ^ c *
        ((x * x' * D ^ 2) ^ m * (A ^ (4 * f) * x * x') ^ k) := by gcongr
    _ = _ := by ring

/- English proof (translation)
Introduce `hM K V _ _ _ _ _ _ _ _ H hK hPD L₀ g j D₀ hL hD hG hg x x' hx hx'`. Break down `Set.eq_empty_or_nonempty {p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = ⊥} with he | ⟨p₀, hp₀, hfix⟩` into its components or cases. Rewrite using `[he]`. Simplify using the standard rewrite rules. Establish `h43` using `GlobalTheory.T.discriminantOrder_common_fixedLattice_embeddedData K V H hK hPD L₀ g j D₀ hL hD hG hg x x' hx hx' p₀ hp₀`.

Rewrite `h43` using `[hfix]`. Establish `hone : GlobalTheory.Mass.discN (GlobalTheory.Mass.hRes H.B.flip (⊥ : Submodule K V)) (GlobalTheory.Mass.latIn ⊥ (fixLat p₀.1.2)) = 1`. Unfold `GlobalTheory.Mass.discN GlobalTheory.Mass.idxN`. Rewrite using `[AddSubgroup.relIndex_eq_one]`. Introduce `y _`.

Rewrite using `[Subsingleton.elim y 0]`. Conclude with `zero_mem _`. Rewrite `h43` using `[hone, finrank_bot, Nat.sub_zero, Nat.cast_one]`. Establish `hD1 : 1 ≤ D₀`. Break down `Nat.eq_zero_or_pos D₀ with h | h` into its components or cases.

Rewrite `h43` using `[h]`. Evaluate the numerical expressions using `at h43`. Conclude with `h`. Establish `hcf : 0 ≤ cf K`. Unfold `cf`.

Establish `: (1 : ℝ) ≤ Module.finrank ℚ K` using `by exact_mod_cast Module.finrank_pos`. Use `Real.logb_nonneg (b := 2) (by norm_num) this` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA` using `GlobalTheory.T.encard_embedded_hermData_index_le K V H hK hPD L₀ g j D₀ hL hD hG hg x hx`. Establish `hB` using `GlobalTheory.T.encard_embedded_hermData_index_le K V H hK hPD L₀ g j D₀ hL hD hG hg x' hx'`.

Establish `hcnt` using `encard_le_of_fibres {p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = ⊥} ({d | IsDat H g L₀ j x d} ×ˢ {d | IsDat H g L₀ j x' d}) (fun p => (p.1, p.2.1)) (fun p hp => ⟨hp.1.1, hp.1.2.1⟩) (((4 * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ≥0∞) ^ (4 * (Module.fin …`. Introduce and unpack `⟨d, d'⟩ ⟨hd, hd'⟩`. Establish `h` using `GlobalTheory.T.card_isometries_fixing_subspace_definite_lattices_le hM K V H hK hPD ⊥ d'.1 d.1 hd'.1.1 hd.1.1`. Rewrite `h` using `[finrank_bot, Nat.sub_zero]`. Use `le_trans (ENat.toENNReal_le.2 ?_) h` and prove the remaining obligations.

Use `Set.encard_le_encard_of_injOn (f := fun p => p.2.2) ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨a, b, η⟩ ⟨⟨hp, -⟩, he⟩`. Take `⟨rfl, rfl⟩` from `Prod.mk.inj he`. Use `⟨hp.2.2.1, hp.2.2.2.1, ?_⟩` and prove the remaining obligations. Introduce `y hy`.

Rewrite using `[(Submodule.mem_bot K).1 hy, map_zero]`. Introduce and unpack `⟨a, b, η⟩ ⟨-, he⟩ ⟨a', b', η'⟩ ⟨-, he'⟩ hη`. Take `⟨rfl, rfl⟩` from `Prod.mk.inj he`. Take `⟨rfl, rfl⟩` from `Prod.mk.inj he'`. Simplify using `only at hη`.

Rewrite using `[hη])`. Rewrite `hcnt` using `[Set.encard_prod, ENat.toENNReal_mul]`. Use `hcnt.trans ((mul_le_mul_left (mul_le_mul' hA hB) _).trans ?_)` and prove the remaining obligations. Rewrite using `[← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations.

Establish `hg0 : (0 : ℝ) < g` using `by exact_mod_cast (by omega : 0 < g)`. Conclude with `arith _ _ _ _ hcf _ _ _ _ _ (by exact_mod_cast hx) (by exact_mod_cast hx') (by exact_mod_cast hD1) (by positivity) (by positivity) h43 _ (by push_cast; ring)`.
-/
theorem main : MinkowskiBound → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (x x' : ℕ), 1 ≤ x → 1 ≤ x' → ((({p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = ⊥}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (((x : ℝ) * x') ^ (((Module.finrank K V) : ℝ) / 2) * ((x : ℝ) * x' * (D₀ : ℝ) ^ 2) ^ (cf K + 3 * (2 * j + 1)) * ((2 / (g : ℝ)) ^ ((Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K)) * ((4 * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ) ^ (4 * (Formalism.HermitianLatticesTheory.fDeg K)) * D₀ * x * x') ^ (Module.finrank K V)) := by
  intro hM K V _ _ _ _ _ _ _ _ H hK hPD L₀ g j D₀ hL hD hG hg x x' hx hx'
  rcases Set.eq_empty_or_nonempty {p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = ⊥} with he | ⟨p₀, hp₀, hfix⟩
  · rw [he]; simp
  have h43 := GlobalTheory.T.discriminantOrder_common_fixedLattice_embeddedData K V H hK hPD L₀ g j D₀ hL hD hG hg x x' hx hx' p₀ hp₀
  rw [hfix] at h43
  have hone : GlobalTheory.Mass.discN (GlobalTheory.Mass.hRes H.B.flip (⊥ : Submodule K V))
      (GlobalTheory.Mass.latIn ⊥ (fixLat p₀.1.2)) = 1 := by
    unfold GlobalTheory.Mass.discN GlobalTheory.Mass.idxN
    rw [AddSubgroup.relIndex_eq_one]
    intro y _
    rw [Subsingleton.elim y 0]
    exact zero_mem _
  rw [hone, finrank_bot, Nat.sub_zero, Nat.cast_one] at h43
  have hD1 : 1 ≤ D₀ := by
    rcases Nat.eq_zero_or_pos D₀ with h | h
    · rw [h] at h43; norm_num at h43
    · exact h
  have hcf : 0 ≤ cf K := by
    unfold cf
    have : (1 : ℝ) ≤ Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    have := Real.logb_nonneg (b := 2) (by norm_num) this
    linarith
  have hA := GlobalTheory.T.encard_embedded_hermData_index_le K V H hK hPD L₀ g j D₀ hL hD hG hg x hx
  have hB := GlobalTheory.T.encard_embedded_hermData_index_le K V H hK hPD L₀ g j D₀ hL hD hG hg x' hx'
  have hcnt := encard_le_of_fibres {p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = ⊥}
    ({d | IsDat H g L₀ j x d} ×ˢ {d | IsDat H g L₀ j x' d}) (fun p => (p.1, p.2.1))
    (fun p hp => ⟨hp.1.1, hp.1.2.1⟩)
    (((4 * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ≥0∞) ^ (4 * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K)))
    (by
      rintro ⟨d, d'⟩ ⟨hd, hd'⟩
      have h := GlobalTheory.T.card_isometries_fixing_subspace_definite_lattices_le hM K V H hK hPD ⊥ d'.1 d.1 hd'.1.1 hd.1.1
      rw [finrank_bot, Nat.sub_zero] at h
      refine le_trans (ENat.toENNReal_le.2 ?_) h
      refine Set.encard_le_encard_of_injOn (f := fun p => p.2.2) ?_ ?_
      · rintro ⟨a, b, η⟩ ⟨⟨hp, -⟩, he⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        refine ⟨hp.2.2.1, hp.2.2.2.1, ?_⟩
        intro y hy
        rw [(Submodule.mem_bot K).1 hy, map_zero]
      · rintro ⟨a, b, η⟩ ⟨-, he⟩ ⟨a', b', η'⟩ ⟨-, he'⟩ hη
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he'
        simp only at hη
        rw [hη])
  rw [Set.encard_prod, ENat.toENNReal_mul] at hcnt
  refine hcnt.trans ((mul_le_mul_left (mul_le_mul' hA hB) _).trans ?_)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  exact arith _ _ _ _ hcf _ _ _ _ _ (by exact_mod_cast hx) (by exact_mod_cast hx') (by exact_mod_cast hD1)
    (by positivity) (by positivity) h43 _ (by push_cast; ring)

end GlobalTheory.PairNoFix
