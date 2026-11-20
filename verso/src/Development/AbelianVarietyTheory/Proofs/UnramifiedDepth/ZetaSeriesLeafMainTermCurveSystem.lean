import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ZetaSeriesCoeffMulLe
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupCoordinatesPullbackLinearTangentBasis
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

noncomputable section

namespace GlobalTheory.MainTerm

open Formalism.BaseCaseIdentities (Data Kn s0)

/- English proof (translation)
Set `φ : I ≃ Fin (Fintype.card I)` to `Fintype.equivFin I`. Establish `hmem : ∀ s c, c ∈ (Gs s).map φ.toEmbedding ↔ φ.symm c ∈ Gs s` using `fun s c => Finset.mem_map_equiv`. Establish `key` using `GlobalTheory.zetaSeries_main_term C v l hl hv h3 (Fintype.card I) M s₀ {c | good (φ.symm c)} (fun s => (Gs s).map φ.toEmbedding) (fun c n e => al (φ.symm c) n (φ.symm e)) (fun s e j => π s (φ.symm e) j) (fun c => t (φ.symm c)) (fun s c hc => h1 s _ ((hmem s c).1 hc)) (fun s s' c …`. Use extensionality with `μ`. Rewrite using `[← h12 (φ.symm e) μ]`.

Express the relevant statement in the definitionally equal form `∑ n ∈ Finset.range (μ.degree + 1), ∑ a, al (φ.symm a) n (φ.symm e) * MvPowerSeries.coeff μ (t (φ.symm a) ^ (l ^ n)) = _`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Conclude with `Equiv.sum_comp φ.symm (fun c => al c n (φ.symm e) * MvPowerSeries.coeff μ (t c ^ (l ^ n))))`. Use `1 (fun c n _ => be (φ.symm c) n) 0`. Use the proof step `(fun c => h13 _) (fun c n => h14 _ n) (fun c hc n hn => h15 _ hc n hn)`.

Use the proof step `(fun s hs c hc => h16 s hs _ ((hmem s c).1 hc)) ζ`. Use the proof step `(fun α => by`. Rewrite using `[h17 α]`. Use `congr 1`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations.

Conclude with `(Equiv.sum_comp φ.symm (fun c => be c n * MvPowerSeries.coeff α (t c ^ (l ^ n)))).symm)`. Simplify `key` using `only [Finset.sum_map, Equiv.coe_toEmbedding, Equiv.symm_apply_apply]`.
-/
theorem zetaSeries_main_term_fintype (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ))
    (l : ℕ) (hl : l.Prime) (hv : v (l : C) = 1) (h3 : 3 ≤ l) (I : Type) [Fintype I] (M s₀ : ℕ)
    (good : I → Prop) (Gs : ℕ → Finset I) (al : I → ℕ → I → C) (π : ℕ → I → Fin M → C)
    (t : I → MvPowerSeries (Fin M) C) (h1 : ∀ s c, c ∈ Gs s → good c)
    (h2 : ∀ s s' c, c ∈ Gs s → c ∈ Gs s' → s = s')
    (h4 : ∀ c e, al c 0 e = if c = e then 1 else 0)
    (h5 : ∀ c (n : ℕ) e, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (al c n e))
    (h6 : ∀ c, good c → ∀ e, al c 1 e = 0)
    (h6' : ∀ c, good c → ∀ (n : ℕ) e, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (al c n e))
    (h7 : ∀ s < s₀, ∀ c ∈ Gs s, ∀ e, e ∉ Gs (s + 1) → 0 ≤ v (al c 2 e))
    (h8 : ∀ c j, 0 ≤ v (π 0 c j)) (h9 : ∀ c, c ∉ Gs 0 → ∀ j, π 0 c j = 0)
    (h10 : ∀ s e j, π (s + 1) e j = ∑ c ∈ Gs s, (l : C) * al c 2 e * π s c j ^ (l ^ 2))
    (h11 : ∀ c, MvPowerSeries.constantCoeff (t c) = 0)
    (h12 : ∀ (e : I) (μ : Fin M →₀ ℕ), ∑ s ∈ Finset.range (μ.degree + 1), ∑ c,
      al c s e * MvPowerSeries.coeff μ (t c ^ (l ^ s)) =
        MvPowerSeries.coeff μ (∑ j, MvPowerSeries.C (R := C) (π 0 e j) *
          (MvPowerSeries.X j : MvPowerSeries (Fin M) C)))
    (be : I → ℕ → C) (h13 : ∀ c, be c 0 = 0)
    (h14 : ∀ c (n : ℕ), ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (be c n))
    (h15 : ∀ c, good c → ∀ n : ℕ, 2 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (be c n))
    (h16 : ∀ s < s₀, ∀ c ∈ Gs s, be c 1 = 0) (ζ : MvPowerSeries (Fin M) C)
    (h17 : ∀ α, MvPowerSeries.coeff α ζ = -∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ c,
      be c n * MvPowerSeries.coeff α (t c ^ (l ^ n))) :
    ReciprocityTheory.PGsh.OrdGe v (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (l : ℝ) ^ (2 * s₀ + 1)))
      (ζ - ∑ j, MvPowerSeries.C (R := C)
        (((l : C) ^ (1 + l * (∑ u ∈ Finset.range s₀, (l ^ 2) ^ u)))⁻¹ *
          ((-1) ^ (s₀ + 1) * ∑ c ∈ Gs s₀, π s₀ c j ^ l * ((l : C) * be c 1))) *
        (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ (l ^ (2 * s₀ + 1))) 0 := by
  let φ : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  have hmem : ∀ s c, c ∈ (Gs s).map φ.toEmbedding ↔ φ.symm c ∈ Gs s := fun s c =>
    Finset.mem_map_equiv
  have key := GlobalTheory.zetaSeries_main_term C v l hl hv h3 (Fintype.card I) M s₀ {c | good (φ.symm c)}
    (fun s => (Gs s).map φ.toEmbedding) (fun c n e => al (φ.symm c) n (φ.symm e))
    (fun s e j => π s (φ.symm e) j) (fun c => t (φ.symm c))
    (fun s c hc => h1 s _ ((hmem s c).1 hc))
    (fun s s' c _ _ hc hc' => h2 s s' _ ((hmem s c).1 hc) ((hmem s' c).1 hc'))
    (fun c e => by simp [h4])
    (fun c n e => h5 _ n _)
    (fun c hc => ⟨funext fun e => h6 _ hc _, fun n e hn => h6' _ hc n _ hn⟩)
    (fun s hs c hc e he => h7 s hs _ ((hmem s c).1 hc) _ (fun h => he ((hmem _ e).2 h)))
    (fun c j => h8 _ j)
    (fun c hc => funext fun j => h9 _ (fun h => hc ((hmem _ c).2 h)) j)
    (fun s e j => by simp [h10, Finset.sum_map])
    (fun c => h11 _)
    (fun e => by
      ext μ
      rw [← h12 (φ.symm e) μ]
      change ∑ n ∈ Finset.range (μ.degree + 1), ∑ a, al (φ.symm a) n (φ.symm e) *
        MvPowerSeries.coeff μ (t (φ.symm a) ^ (l ^ n)) = _
      refine Finset.sum_congr rfl fun n _ => ?_
      exact Equiv.sum_comp φ.symm (fun c => al c n (φ.symm e) * MvPowerSeries.coeff μ (t c ^ (l ^ n))))
    1 (fun c n _ => be (φ.symm c) n) 0
    (fun c => h13 _) (fun c n => h14 _ n) (fun c hc n hn => h15 _ hc n hn)
    (fun s hs c hc => h16 s hs _ ((hmem s c).1 hc)) ζ
    (fun α => by
      rw [h17 α]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      exact (Equiv.sum_comp φ.symm (fun c => be c n * MvPowerSeries.coeff α (t c ^ (l ^ n)))).symm)
  simpa only [Finset.sum_map, Equiv.coe_toEmbedding, Equiv.symm_apply_apply] using key

/- English proof (translation)
Introduce `C _ _ V d _ I J _ _ G S Z D a i h hid t ht N em hem κ hκ`. Establish `hDv : D.v = V.v` using `h.1`. Establish `hDl : D.l = V.l` using `h.2.1`. Establish `hDi : D.i = i` using `h.2.2.1`. Establish `hi : Odd i` using `hDi ▸ D.i_odd`.

Establish `h3 : 3 ≤ V.l` using `hDl ▸ D.l_ge`. Establish `hK : Kn i = s0 i + 1` using `Kn_eq hi`. Establish `hs : 2 * s0 i + 1 = i` using `two_mul_chainStartIndex_add_one_of_odd hi`. Set `al : I → ℕ → I → C` to `fun c k b => if k = 0 then (if c = b then 1 else 0) else D.al c k b`. Establish `hal0 : ∀ c b, al c 0 b = if c = b then 1 else 0` using `fun c b => by simp [al]`.

Establish `halk : ∀ c k b, 1 ≤ k → al c k b = D.al c k b` using `fun c k b hk => by`. Establish `: k ≠ 0` using `by omega`. Simplify using `[al, this]`. Take `⟨hc1, hc2, hc3⟩` from `GlobalTheory.MainTerm.linPull_coords C V d I J G S t ht (Fin N) (fun δ => S.tan (em δ)) (fun b j => chainMat D 0 b (em j)) al (fun j x => by simp [chainMat_zero]) (fun c b => by rw [hal0]) (fun c k x hk => by`. Rewrite using `[h.2.2.2.1 c k x hk]`.

Conclude with `Finset.sum_congr rfl fun b _ => by rw [halk c k b hk])`. Establish `hGs : ∀ s c, c ∈ Finset.univ.filter (fun c => D.lev c = s ∧ s < Kn D.i) ↔ D.lev c = s ∧ s < Kn D.i` using `fun s c => by simp`. Establish `hl0 : (D.l : C) ≠ 0` using `by exact_mod_cast D.l_prime.ne_zero`. Establish `key` using `zetaSeries_main_term_fintype C V.v V.l V.l_prime V.v_l h3 I N (s0 i) D.good (fun s => Finset.univ.filter (fun c => D.lev c = s ∧ s < Kn D.i)) al (fun s e j => chainMat D s e (em j)) (fun c => linPull (fun δ => S.tan (em δ)) (t c)) (fun s c hc => by`. Take `⟨h1, h2⟩` from `(hGs s c).1 hc`.

Conclude with `D.pure_good c (h1 ▸ h2))`. Use the proof step `(fun s s' c hc hc' => ((hGs s c).1 hc).1.symm.trans ((hGs s' c).1 hc').1)`. Use `hal0`. Use the proof step `(fun c n e => by`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases.

Apply the tactic sequence `rw [hal0] split_ifs <;> simp`. Rewrite using `[halk c n e hn, ← hDv]`. Conclude with `D.al_all c n e)`. Use the proof step `(fun c hc e => by rw [halk c 1 e le_rfl, D.al_one c hc])`. Use the proof step `(fun c hc n e hn => by`.

Rewrite using `[halk c n e hn, ← hDv]`. Use `D.al_good c hc n e hn` as an intermediate fact. Rewrite using `[neg_sub] at this)` and apply the resulting hypothesis. Use the proof step `(fun s hs' c hc e he => by`. Take `⟨h1, h2⟩` from `(hGs s c).1 hc`.

Establish `h4 : s + 1 < Kn D.i` using `by rw [hDi, hK]; omega`. Establish `h5 : D.lev e ≠ D.lev c + 1` using `fun h6 => he ((hGs _ e).2 ⟨by rw [h6, h1], h4⟩)`. Rewrite using `[halk c 2 e (by norm_num), D.al_two c (h1 ▸ h2), D.g_supp c (h1 ▸ h4) e h5, zero_add, inv_mul_cancel_left₀ hl0, ← hDv]`. Conclude with `D.lam_int c e)`. Use the proof step `(fun c j => by simpa [VF.Ge] using h.chainMat_int 0 c (em j))`.

Use the proof step `(fun c hc j => by`. Rewrite using `[chainMat_zero, if_neg]`. Introduce and unpack `rfl`. Conclude with `hc ((hGs _ _).2 ⟨hem j, by rw [hDi, hK]; omega⟩))`. Use the proof step `(fun s e j => by`.

Rewrite using `[chainMat_succ, hDl]`. Conclude with `Finset.sum_congr rfl fun c _ => by rw [halk c 2 e (by norm_num)])`. Use `hc1 hc2 (fun c n => S.be c n κ) (fun c => S.be_zero c κ)`. Use the proof step `(fun c n => G.bound0 n _ (S.mem c) (Sum.inr κ))`. Use the proof step `(fun c hc n hn => by`.

Take `⟨m, rfl⟩` from `Nat.exists_eq_add_of_le' hn`. Use `(h.good hc).bound m (Sum.inr κ)` as an intermediate fact. Establish `e : (1 - ((m + 2 : ℕ) : ℝ)) = -((m : ℝ) + 1)` using `by push_cast; ring`. Rewrite using `[e]`. Conclude with `this)`.

Use the proof step `(fun s hs' c hc => by`. Take `⟨h1, h2⟩` from `(hGs s c).1 hc`. Apply `S.pure c 1` to reduce the goal to its premises. Rewrite using `[hκ, h.2.2.2.2 c (by rw [h1, ← hDi]; exact h2), h1, add_assoc, ← Nat.cast_add]`. Introduce `h5`.

Establish `h6` using `(ZMod.natCast_eq_natCast_iff' _ _ _).1 (add_left_cancel h5)`. Rewrite `h6` using `[Nat.mod_eq_of_lt hid, Nat.mod_eq_of_lt (by omega)]`. Use the proof step `omega)`. Use the proof step `(linPull (fun δ => S.tan (em δ)) (S.ze t κ)) (hc3 κ)`. Establish `hE : expE V.l i = 1 + V.l * (∑ u ∈ Finset.range (s0 i), (V.l ^ 2) ^ u)` using `rfl`.

Establish `hmain : ((V.l : C) ^ expE V.l i)⁻¹ • ∑ δ : Fin N, mainVec S D (em δ) κ • (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ (V.l ^ i) = ∑ j, MvPowerSeries.C (R` using `C) (((V.l : C) ^ (1 + V.l * (∑ u ∈ Finset.range (s0 i), (V.l ^ 2) ^ u)))⁻¹ * ((-1) ^ (s0 i + 1) * ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s0 i ∧ s0 i < Kn D.i), chainMat D (s0 i) c (em j) ^ V.l * ((V.l : C) * S.be c 1 κ))) * (MvPowerSeries.X j : MvPowerSeries (Fin N) C) ^ (V …`. Rewrite using `[Finset.smul_sum, hs, hE]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, MvPowerSeries.smul_eq_C_mul, mainVec, hDl, hDi]`. Rewrite using `[hmain]`.

Introduce `μ`. Establish `hk` using `key μ`. Rewrite `hk` using `[hs]`. Establish `hr : ∑ m, (1 / ((V.l : ℝ) ^ 2 - 1) + 3 / (8 * (V.l : ℝ) ^ i)) * (μ m : ℝ) = (μ.degree : ℝ) * (r1 V.l i - del V.l i)`. Rewrite using `[← Finset.mul_sum, Finsupp.degree_eq_sum, Nat.cast_sum, mul_comm]`.

Use `congr 1`. Unfold `r1 del rho`. Establish `: (V.l : ℝ) ≠ 0` using `by exact_mod_cast V.l_prime.ne_zero`. Rewrite using `[add_sub_assoc]`. Use `congr 1`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hr] at hk`. Rewrite using `[hs]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← WithTop.coe_add, sub_add_cancel]`. Use `_ ≤ _ := add_le_add_left hk _`.
-/
theorem zeta_leaf_main_term : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) [NeZero d] (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z I) (a : ZMod d) (i : ℕ), Adapted S D a i → i < d → ∀ t : I → MvPowerSeries I C, S.IsT t → ∀ (N : ℕ) (em : Fin N → I), (∀ δ, D.lev (em δ) = 0) → ∀ κ : J, G.ty (Sum.inr κ) = a + (i : ZMod d) → WtGe1 V i 0 (linPull (fun δ => S.tan (em δ)) (S.ze t κ) - ((V.l : C) ^ expE V.l i)⁻¹ • ∑ δ : Fin N, mainVec S D (em δ) κ • (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ (V.l ^ i)) := by
  intro C _ _ V d _ I J _ _ G S Z D a i h hid t ht N em hem κ hκ
  have hDv : D.v = V.v := h.1
  have hDl : D.l = V.l := h.2.1
  have hDi : D.i = i := h.2.2.1
  have hi : Odd i := hDi ▸ D.i_odd
  have h3 : 3 ≤ V.l := hDl ▸ D.l_ge
  have hK : Kn i = s0 i + 1 := Kn_eq hi
  have hs : 2 * s0 i + 1 = i := two_mul_chainStartIndex_add_one_of_odd hi
  let al : I → ℕ → I → C := fun c k b => if k = 0 then (if c = b then 1 else 0) else D.al c k b
  have hal0 : ∀ c b, al c 0 b = if c = b then 1 else 0 := fun c b => by simp [al]
  have halk : ∀ c k b, 1 ≤ k → al c k b = D.al c k b := fun c k b hk => by
    have : k ≠ 0 := by omega
    simp [al, this]
  obtain ⟨hc1, hc2, hc3⟩ := GlobalTheory.MainTerm.linPull_coords C V d I J G S t ht (Fin N) (fun δ => S.tan (em δ))
    (fun b j => chainMat D 0 b (em j)) al
    (fun j x => by simp [chainMat_zero])
    (fun c b => by rw [hal0])
    (fun c k x hk => by
      rw [h.2.2.2.1 c k x hk]
      exact Finset.sum_congr rfl fun b _ => by rw [halk c k b hk])
  have hGs : ∀ s c, c ∈ Finset.univ.filter (fun c => D.lev c = s ∧ s < Kn D.i) ↔
      D.lev c = s ∧ s < Kn D.i := fun s c => by simp
  have hl0 : (D.l : C) ≠ 0 := by exact_mod_cast D.l_prime.ne_zero
  have key := zetaSeries_main_term_fintype C V.v V.l V.l_prime V.v_l h3 I N (s0 i) D.good
    (fun s => Finset.univ.filter (fun c => D.lev c = s ∧ s < Kn D.i)) al
    (fun s e j => chainMat D s e (em j)) (fun c => linPull (fun δ => S.tan (em δ)) (t c))
    (fun s c hc => by
      obtain ⟨h1, h2⟩ := (hGs s c).1 hc
      exact D.pure_good c (h1 ▸ h2))
    (fun s s' c hc hc' => ((hGs s c).1 hc).1.symm.trans ((hGs s' c).1 hc').1)
    hal0
    (fun c n e => by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [hal0]
        split_ifs <;> simp
      · rw [halk c n e hn, ← hDv]
        exact D.al_all c n e)
    (fun c hc e => by rw [halk c 1 e le_rfl, D.al_one c hc])
    (fun c hc n e hn => by
      rw [halk c n e hn, ← hDv]
      have := D.al_good c hc n e hn
      rwa [neg_sub] at this)
    (fun s hs' c hc e he => by
      obtain ⟨h1, h2⟩ := (hGs s c).1 hc
      have h4 : s + 1 < Kn D.i := by rw [hDi, hK]; omega
      have h5 : D.lev e ≠ D.lev c + 1 := fun h6 => he ((hGs _ e).2 ⟨by rw [h6, h1], h4⟩)
      rw [halk c 2 e (by norm_num), D.al_two c (h1 ▸ h2), D.g_supp c (h1 ▸ h4) e h5, zero_add,
        inv_mul_cancel_left₀ hl0, ← hDv]
      exact D.lam_int c e)
    (fun c j => by simpa [VF.Ge] using h.chainMat_int 0 c (em j))
    (fun c hc j => by
      rw [chainMat_zero, if_neg]
      rintro rfl
      exact hc ((hGs _ _).2 ⟨hem j, by rw [hDi, hK]; omega⟩))
    (fun s e j => by
      rw [chainMat_succ, hDl]
      exact Finset.sum_congr rfl fun c _ => by rw [halk c 2 e (by norm_num)])
    hc1 hc2 (fun c n => S.be c n κ) (fun c => S.be_zero c κ)
    (fun c n => G.bound0 n _ (S.mem c) (Sum.inr κ))
    (fun c hc n hn => by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
      have := (h.good hc).bound m (Sum.inr κ)
      have e : (1 - ((m + 2 : ℕ) : ℝ)) = -((m : ℝ) + 1) := by push_cast; ring
      rw [e]
      exact this)
    (fun s hs' c hc => by
      obtain ⟨h1, h2⟩ := (hGs s c).1 hc
      apply S.pure c 1
      rw [hκ, h.2.2.2.2 c (by rw [h1, ← hDi]; exact h2), h1, add_assoc, ← Nat.cast_add]
      intro h5
      have h6 := (ZMod.natCast_eq_natCast_iff' _ _ _).1 (add_left_cancel h5)
      rw [Nat.mod_eq_of_lt hid, Nat.mod_eq_of_lt (by omega)] at h6
      omega)
    (linPull (fun δ => S.tan (em δ)) (S.ze t κ)) (hc3 κ)
  have hE : expE V.l i = 1 + V.l * (∑ u ∈ Finset.range (s0 i), (V.l ^ 2) ^ u) := rfl
  have hmain : ((V.l : C) ^ expE V.l i)⁻¹ • ∑ δ : Fin N, mainVec S D (em δ) κ •
      (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ (V.l ^ i) =
      ∑ j, MvPowerSeries.C (R := C)
        (((V.l : C) ^ (1 + V.l * (∑ u ∈ Finset.range (s0 i), (V.l ^ 2) ^ u)))⁻¹ *
          ((-1) ^ (s0 i + 1) * ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s0 i ∧ s0 i < Kn D.i),
            chainMat D (s0 i) c (em j) ^ V.l * ((V.l : C) * S.be c 1 κ))) *
        (MvPowerSeries.X j : MvPowerSeries (Fin N) C) ^ (V.l ^ (2 * s0 i + 1)) := by
    rw [Finset.smul_sum, hs, hE]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, MvPowerSeries.smul_eq_C_mul, mainVec, hDl, hDi]
  rw [hmain]
  intro μ
  have hk := key μ
  rw [hs] at hk
  have hr : ∑ m, (1 / ((V.l : ℝ) ^ 2 - 1) + 3 / (8 * (V.l : ℝ) ^ i)) * (μ m : ℝ) =
      (μ.degree : ℝ) * (r1 V.l i - del V.l i) := by
    rw [← Finset.mul_sum, Finsupp.degree_eq_sum, Nat.cast_sum, mul_comm]
    congr 1
    unfold r1 del rho
    have : (V.l : ℝ) ≠ 0 := by exact_mod_cast V.l_prime.ne_zero
    rw [add_sub_assoc]
    congr 1
    field_simp
    ring
  simp only [hr] at hk
  rw [hs]
  calc (((0 : ℝ) : ℝ) : WithTop ℝ)
      = ((0 - (μ.degree : ℝ) * (r1 V.l i - del V.l i) : ℝ) : WithTop ℝ) +
        (((μ.degree : ℝ) * (r1 V.l i - del V.l i) : ℝ) : WithTop ℝ) := by
        rw [← WithTop.coe_add, sub_add_cancel]
    _ ≤ _ := add_le_add_left hk _

end GlobalTheory.MainTerm
