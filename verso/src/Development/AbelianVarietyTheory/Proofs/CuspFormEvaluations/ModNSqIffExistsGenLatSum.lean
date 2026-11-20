import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Establish `hN' : (N : E) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `hfg : L.FG`. Establish `hle : L ≤ Submodule.span (𝓞 E) (Set.range fun b : Fin n => (Pi.single b (N : E)⁻¹ : Fin n → E))`. Introduce `v hv`. Use `choose u hu' using hu v hv`.

Establish `: v = ∑ b, u b • (Pi.single b (N : E)⁻¹ : Fin n → E)`. Use function extensionality and compare the values at `c`. Rewrite using `[Finset.sum_apply, Finset.sum_eq_single c]`. Simplify using `only [Pi.smul_apply, Pi.single_eq_same]`. Rewrite using `[Algebra.smul_def]`.

Express the relevant statement in the definitionally equal form `v c = (u c : E) * _`. Rewrite using `[hu']`. Clear the denominators using the available nonvanishing facts. Introduce `b _ hb`. Simplify using `[Pi.single_eq_of_ne hb.symm]`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)`. Conclude with `Submodule.FG.of_le (Submodule.fg_span (Set.finite_range _)) hle`. Establish `: Module.Finite (𝓞 E) L` using `Module.Finite.iff_fg.2 hfg`.

Establish `: Module.FinitePresentation (𝓞 E) L` using `Module.finitePresentation_of_finite _ _`. Establish `: Module.Projective (𝓞 E) L` using `Module.Flat.projective_of_finitePresentation`. Take `⟨m, f, g, -, -, hfg⟩` from `Module.Finite.exists_comp_eq_id_of_projective (𝓞 E) L`. Use `⟨m, fun i => f (Pi.single i 1), fun i => (LinearMap.proj i) ∘ₗ g, fun v => ?_⟩` and prove the remaining obligations. Establish `h1 : f (g v) = v` using `LinearMap.congr_fun hfg v`.

Use `conv_rhs => rw [← h1, pi_eq_sum_univ' (g v), map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`. Use `congr 2`.
-/
theorem exists_dualFamily_of_nsmul_integral {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) {N : ℕ} (hN : 0 < N)
    (hu : ∀ v ∈ L, ∀ b, ∃ u : 𝓞 E, (u : E) = (N : E) * v b) :
    ∃ (m : ℕ) (w : Fin m → L) (lam : Fin m → (L →ₗ[𝓞 E] 𝓞 E)), ∀ v, ∑ i, lam i v • w i = v := by
  classical
  have hN' : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hfg : L.FG := by
    have hle : L ≤ Submodule.span (𝓞 E)
        (Set.range fun b : Fin n => (Pi.single b (N : E)⁻¹ : Fin n → E)) := by
      intro v hv
      choose u hu' using hu v hv
      have : v = ∑ b, u b • (Pi.single b (N : E)⁻¹ : Fin n → E) := by
        funext c
        rw [Finset.sum_apply, Finset.sum_eq_single c]
        · simp only [Pi.smul_apply, Pi.single_eq_same]
          rw [Algebra.smul_def]
          change v c = (u c : E) * _
          rw [hu']; field_simp
        · intro b _ hb
          simp [Pi.single_eq_of_ne hb.symm]
        · simp
      rw [this]
      exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
    exact Submodule.FG.of_le (Submodule.fg_span (Set.finite_range _)) hle
  have : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hfg
  have : Module.FinitePresentation (𝓞 E) L := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 E) L := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 E) L
  refine ⟨m, fun i => f (Pi.single i 1), fun i => (LinearMap.proj i) ∘ₗ g, fun v => ?_⟩
  have h1 : f (g v) = v := LinearMap.congr_fun hfg v
  conv_rhs => rw [← h1, pi_eq_sum_univ' (g v), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  congr 2

/- English proof (translation)
Simplify using `only [stdLat, Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]`.
-/
theorem mem_stdLat_iff_integral {E : Type} [Field E] [NumberField E] {n : ℕ} (v : Fin n → E) :
    v ∈ stdLat E n ↔ ∀ b, ∃ u : 𝓞 E, (u : E) = v b := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]

/- English proof (translation)
Introduce `E _ _ _ H Dw n Λ N hU hN hle a`. Establish `hN' : (N : E) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `hNO : (N : 𝓞 E) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `inj : Function.Injective (fun x : 𝓞 E => (x : E))` using `RingOfIntegers.coe_injective`. Establish `he : ∀ b : Fin n, (Pi.single b (N : E) : Fin n → E) ∈ Λ.La`.

Introduce `b`. Apply `hle` to reduce the goal to its premises. Establish `h1 : (Pi.single b (1 : E) : Fin n → E) ∈ stdLat E n`. Rewrite using `[mem_stdLat_iff_integral]`. Introduce `c`.

Distinguish the cases in `h : c = b`. Substitute `h; exact ⟨1, by simp⟩` using the available equality. Conclude with `⟨0, by simp [Pi.single_eq_of_ne h]⟩`. Establish `h2` using `Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (N : 𝓞 E)) h1`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `c`. Distinguish the cases in `h : c = b`. Substitute `h` using the available equality. Simplify using `[Algebra.smul_def]`. Simplify using `[Pi.single_eq_of_ne h]`.

Establish `hu : ∀ v ∈ Λ.La, ∀ b, ∃ u : 𝓞 E, (u : E) = (N : E) * v b`. Introduce `v hv b`. Take `⟨y, hy⟩` from `(hU (Pi.single b (N : E))).1 (he b) v hv`. Use `⟨y, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 E) E y = _`.

Rewrite using `[hy, Finset.sum_eq_single b]`. Simplify using the standard rewrite rules. Introduce `c _ hc`. Simplify using `[Pi.single_eq_of_ne hc]`. Simplify using the standard rewrite rules.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Conclude with `⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun b => b.elim0⟩`. Take `⟨m, w, lam, hw⟩` from `exists_dualFamily_of_nsmul_integral Λ.La hN hu`.

Set `e : Fin n → Λ.La` to `fun b => ⟨Pi.single b (N : E), he b⟩`. Establish `hx : ∀ i, ∃ x : Dw.La, ∑ j, lam i (e j) • a j = (N ^ 2) • x`. Introduce `i`. Use `h (Matrix.of fun _ j => (lam i (e j) : E) / N) ?_ (fun _ j => lam i (e j)) ?_ ⟨0, hn⟩` and prove the remaining obligations. Introduce `v hv`.

Rewrite using `[mem_stdLat_iff_integral]`. Introduce `b`. Use `⟨lam i ⟨v, hv⟩, ?_⟩` and prove the remaining obligations. Use `choose u hu' using hu v hv`. Establish `h1 : ((N : 𝓞 E) * N) • (⟨v, hv⟩ : Λ.La) = ∑ j, u j • e j`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `c`. Simplify using `only [e, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]`. Rewrite using `[Finset.sum_eq_single c]`. Simplify using `only [Pi.single_eq_same, Algebra.smul_def]`.

Express the relevant statement in the definitionally equal form `_ = (u c : E) * _`. Rewrite using `[hu']`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Introduce `d _ hd`.

Simplify using `[Pi.single_eq_of_ne hd.symm]`. Simplify using the standard rewrite rules. Establish `h2` using `congrArg (fun z => ((lam i z : 𝓞 E) : E)) h1`. Simplify using `only [map_smul, map_sum, smul_eq_mul] at h2`. Move the coercions through the operations in `at h2`.

Simplify using `only [Matrix.mulVec, dotProduct, Matrix.of_apply]`. Apply `mul_left_cancel₀ (mul_ne_zero hN' hN')` to reduce the goal to its premises. Rewrite using `[Finset.mul_sum]`. Use `h2.trans (Finset.sum_congr rfl fun j _ => ?_)` and prove the remaining obligations. Use `hu' j` as an intermediate fact.

Express the relevant statement in the definitionally equal form `(u j : E) * (lam i (e j) : E) = _`. Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts. Introduce `_ j`. Simplify using `only [Matrix.of_apply]`.

Clear the denominators using the available nonvanishing facts. Use `choose x hx using hx`. Use `choose v hv using fun i => hu (w i) (w i).2`. Use `⟨m, x, v, fun i => ⟨w i, (w i).2, hv i⟩, fun b => ?_⟩` and prove the remaining obligations. Use `Dw.proj` as an intermediate fact.

Establish `hd : ∀ j, ∑ i, v i b * lam i (e j) = if j = b then (N : 𝓞 E) ^ 2 else 0`. Introduce `j`. Apply `inj` to reduce the goal to its premises. Establish `h1` using `congrFun (congrArg Subtype.val (hw (e j))) b`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, Algebra.smul_def] at h1`.

Establish `h2 : (((∑ i, v i b * lam i (e j) : 𝓞 E)) : E) = (N : E) * (e j : Fin n → E) b`. Rewrite using `[← h1, Finset.mul_sum]`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 E) E _ = _`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul]`. Express the relevant statement in the definitionally equal form `(v i b : E) * _ = _`. Rewrite using `[hv]`. Expand and normalize the polynomial expressions, which then agree. Express the relevant statement in the definitionally equal form `(((∑ i, v i b * lam i (e j) : 𝓞 E)) : E) = _`.

Rewrite using `[h2]`. Distinguish the cases in `hj : j = b`. Substitute `hj` using the available equality. Simplify using `[e, sq]`. Simplify using `[e, hj]`.

Apply `smul_right_injective Dw.La (pow_ne_zero 2 hNO)` to reduce the goal to its premises. Establish `hx' : ∀ i, ((N : 𝓞 E) ^ 2) • x i = ∑ j, lam i (e j) • a j`. Introduce `i`. Rewrite using `[hx, ← Nat.cast_smul_eq_nsmul (𝓞 E), Nat.cast_pow]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `[hd]`. Use `_ = ∑ i, v i b • ∑ j, lam i (e j) • a j := by`. Simplify using `only [Finset.sum_smul, Finset.smul_sum, mul_smul]`. Conclude with `Finset.sum_comm`. Use `_ = ((N : 𝓞 E) ^ 2) • ∑ i, v i b • x i := by`.

Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← hx', smul_comm]`. Introduce and unpack `⟨m, x, v, hv, ha⟩ mu hmu cm hcm i choose w hw hvw using hv choose y hy using fun k => (mem_stdLat_iff_integral _).1 (hmu (w k) (hw k)) i`. Establish `hd : ∀ k, ∑ j, cm i j * v k j = (N : 𝓞 E) ^ 2 * y k`.

Introduce `k`. Apply `inj` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 E) E _ = algebraMap (𝓞 E) E _`. Rewrite using `[map_sum, map_mul]`. Express the relevant statement in the definitionally equal form `_ = _ * (y k : E)`.

Rewrite using `[hy]`. Simplify using `only [Matrix.mulVec, dotProduct, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Express the relevant statement in the definitionally equal form `(cm i j : E) * (v k j : E) = _`.

Rewrite using `[hcm, hvw]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Use `⟨∑ k, y k • x k, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [ha, Finset.sum_smul, Finset.smul_sum, mul_smul]`. Conclude with `Finset.sum_comm`. Use `_ = _ := by`. Rewrite using `[← Nat.cast_smul_eq_nsmul (𝓞 E), Nat.cast_pow, Finset.smul_sum]`. Simplify using `only [hd, mul_smul]`.
-/
theorem modN_sq_iff_exists_genLat_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∀ a : Fin n → Dw.La, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • a j)) ↔ ∃ (m : ℕ) (x : Fin m → Dw.La) (v : Fin m → Fin n → 𝓞 E), (∀ i, ∃ w ∈ Λ.La, ∀ b, (v i b : E) = (N : E) * w b) ∧ ∀ b, a b = ∑ i, v i b • x i := by
  classical
  intro E _ _ _ H Dw n Λ N hU hN hle a
  have hN' : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hNO : (N : 𝓞 E) ≠ 0 := by exact_mod_cast hN.ne'
  have inj : Function.Injective (fun x : 𝓞 E => (x : E)) := RingOfIntegers.coe_injective
  have he : ∀ b : Fin n, (Pi.single b (N : E) : Fin n → E) ∈ Λ.La := by
    intro b
    apply hle
    have h1 : (Pi.single b (1 : E) : Fin n → E) ∈ stdLat E n := by
      rw [mem_stdLat_iff_integral]
      intro c
      by_cases h : c = b
      · subst h; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [Pi.single_eq_of_ne h]⟩
    have h2 := Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (N : 𝓞 E)) h1
    convert h2 using 1
    funext c
    by_cases h : c = b
    · subst h; simp [Algebra.smul_def]
    · simp [Pi.single_eq_of_ne h]
  have hu : ∀ v ∈ Λ.La, ∀ b, ∃ u : 𝓞 E, (u : E) = (N : E) * v b := by
    intro v hv b
    obtain ⟨y, hy⟩ := (hU (Pi.single b (N : E))).1 (he b) v hv
    refine ⟨y, ?_⟩
    change algebraMap (𝓞 E) E y = _
    rw [hy, Finset.sum_eq_single b]
    · simp
    · intro c _ hc
      simp [Pi.single_eq_of_ne hc]
    · simp
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun b => b.elim0⟩
    obtain ⟨m, w, lam, hw⟩ := exists_dualFamily_of_nsmul_integral Λ.La hN hu
    let e : Fin n → Λ.La := fun b => ⟨Pi.single b (N : E), he b⟩
    have hx : ∀ i, ∃ x : Dw.La, ∑ j, lam i (e j) • a j = (N ^ 2) • x := by
      intro i
      refine h (Matrix.of fun _ j => (lam i (e j) : E) / N) ?_ (fun _ j => lam i (e j)) ?_ ⟨0, hn⟩
      · intro v hv
        rw [mem_stdLat_iff_integral]
        intro b
        refine ⟨lam i ⟨v, hv⟩, ?_⟩
        choose u hu' using hu v hv
        have h1 : ((N : 𝓞 E) * N) • (⟨v, hv⟩ : Λ.La) = ∑ j, u j • e j := by
          apply Subtype.ext
          funext c
          simp only [e, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
          rw [Finset.sum_eq_single c]
          · simp only [Pi.single_eq_same, Algebra.smul_def]
            change _ = (u c : E) * _
            rw [hu']; simp; ring
          · intro d _ hd
            simp [Pi.single_eq_of_ne hd.symm]
          · simp
        have h2 := congrArg (fun z => ((lam i z : 𝓞 E) : E)) h1
        simp only [map_smul, map_sum, smul_eq_mul] at h2
        push_cast at h2
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
        apply mul_left_cancel₀ (mul_ne_zero hN' hN')
        rw [Finset.mul_sum]
        refine h2.trans (Finset.sum_congr rfl fun j _ => ?_)
        have := hu' j
        change (u j : E) * (lam i (e j) : E) = _
        rw [this]; field_simp
      · intro _ j
        simp only [Matrix.of_apply]; field_simp
    choose x hx using hx
    choose v hv using fun i => hu (w i) (w i).2
    refine ⟨m, x, v, fun i => ⟨w i, (w i).2, hv i⟩, fun b => ?_⟩
    have := Dw.proj
    have hd : ∀ j, ∑ i, v i b * lam i (e j) = if j = b then (N : 𝓞 E) ^ 2 else 0 := by
      intro j
      apply inj
      have h1 := congrFun (congrArg Subtype.val (hw (e j))) b
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        Algebra.smul_def] at h1
      have h2 : (((∑ i, v i b * lam i (e j) : 𝓞 E)) : E) = (N : E) * (e j : Fin n → E) b := by
        rw [← h1, Finset.mul_sum]
        change algebraMap (𝓞 E) E _ = _
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul]
        change (v i b : E) * _ = _
        rw [hv]; ring
      change (((∑ i, v i b * lam i (e j) : 𝓞 E)) : E) = _
      rw [h2]
      by_cases hj : j = b
      · subst hj; simp [e, sq]
      · simp [e, hj]
    apply smul_right_injective Dw.La (pow_ne_zero 2 hNO)
    have hx' : ∀ i, ((N : 𝓞 E) ^ 2) • x i = ∑ j, lam i (e j) • a j := by
      intro i
      rw [hx, ← Nat.cast_smul_eq_nsmul (𝓞 E), Nat.cast_pow]
    calc ((N : 𝓞 E) ^ 2) • a b = ∑ j, (∑ i, v i b * lam i (e j)) • a j := by
          simp [hd]
      _ = ∑ i, v i b • ∑ j, lam i (e j) • a j := by
          simp only [Finset.sum_smul, Finset.smul_sum, mul_smul]
          exact Finset.sum_comm
      _ = ((N : 𝓞 E) ^ 2) • ∑ i, v i b • x i := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← hx', smul_comm]
  · rintro ⟨m, x, v, hv, ha⟩ mu hmu cm hcm i
    choose w hw hvw using hv
    choose y hy using fun k => (mem_stdLat_iff_integral _).1 (hmu (w k) (hw k)) i
    have hd : ∀ k, ∑ j, cm i j * v k j = (N : 𝓞 E) ^ 2 * y k := by
      intro k
      apply inj
      change algebraMap (𝓞 E) E _ = algebraMap (𝓞 E) E _
      rw [map_sum, map_mul]
      change _ = _ * (y k : E)
      rw [hy]
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul]
      change (cm i j : E) * (v k j : E) = _
      rw [hcm, hvw]; simp; ring
    refine ⟨∑ k, y k • x k, ?_⟩
    calc ∑ j, cm i j • a j = ∑ k, (∑ j, cm i j * v k j) • x k := by
          simp only [ha, Finset.sum_smul, Finset.smul_sum, mul_smul]
          exact Finset.sum_comm
      _ = _ := by
          rw [← Nat.cast_smul_eq_nsmul (𝓞 E), Nat.cast_pow, Finset.smul_sum]
          simp only [hd, mul_smul]

end GlobalTheory
