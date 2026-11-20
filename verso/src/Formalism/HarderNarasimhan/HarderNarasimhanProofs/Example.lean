import Formalism.HarderNarasimhan.DegSupermodZ
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNSlopes
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax

open Module Submodule

noncomputable section

namespace Formalism.HN

namespace PolygonExample

abbrev E2 := EuclideanSpace ℝ (Fin 2)

def e₀ : E2 := EuclideanSpace.single 0 1
def e₁ : E2 := EuclideanSpace.single 1 1
def Lx : Submodule ℤ E2 := Submodule.span ℤ {e₀, (2 : ℝ) • e₁}
def Px : Submodule ℤ E2 := Submodule.span ℤ {e₀}

/- English proof (translation)
Use extensionality with `x`. Simplify using `[zl]`.
-/
theorem zl_id (N : Submodule ℤ E2) : zl (AddMonoidHom.id E2) N = N := by
  ext x
  simp [zl]

/- English proof (translation)
Simplify using `[e₀, e₁]`.
-/
theorem coord0 (m n : ℤ) : (m • e₀ + n • ((2 : ℝ) • e₁)) 0 = m := by
  simp [e₀, e₁]

/- English proof (translation)
Simplify using `[e₀, e₁]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coord1 (m n : ℤ) : (m • e₀ + n • ((2 : ℝ) • e₁)) 1 = 2 * n := by
  simp [e₀, e₁]
  ring

/- English proof (translation)
Establish `key : ∀ (y : E2) (i : Fin 2), |y i| ≤ ‖y‖`. Introduce `y i`. Rewrite using `[EuclideanSpace.norm_eq, ← Real.sqrt_sq_eq_abs]`. Apply `Real.sqrt_le_sqrt` to reduce the goal to its premises. Use `Finset.single_le_sum (f := fun j => ‖y j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)` as an intermediate fact.

Simplify `this` using `[Real.norm_eq_abs, sq_abs]`. Rewrite `hx` using `[Lx, Submodule.mem_span_pair]`. Take `⟨m, n, rfl⟩` from `hx`. Distinguish the cases in `hm : m = 0`. Establish `hn : n ≠ 0`.

Introduce and unpack `rfl`. Substitute `hm` using the available equality. Conclude with `h0 (by simp)`. Establish `k1` using `key (m • e₀ + n • ((2 : ℝ) • e₁)) 1`. Rewrite `k1` using `[coord1, abs_mul]`.

Establish `: (1 : ℝ) ≤ |(n : ℝ)|` using `by exact_mod_cast Int.one_le_abs hn`. Evaluate the numerical expressions using `at k1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `k0` using `key (m • e₀ + n • ((2 : ℝ) • e₁)) 0`. Rewrite `k0` using `[coord0]`.

Establish `: (1 : ℝ) ≤ |(m : ℝ)|` using `by exact_mod_cast Int.one_le_abs hm`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_le_norm {x : E2} (hx : x ∈ Lx) (h0 : x ≠ 0) : 1 ≤ ‖x‖ := by
  have key : ∀ (y : E2) (i : Fin 2), |y i| ≤ ‖y‖ := by
    intro y i
    rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    have := Finset.single_le_sum (f := fun j => ‖y j‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ i)
    simpa [Real.norm_eq_abs, sq_abs] using this
  rw [Lx, Submodule.mem_span_pair] at hx
  obtain ⟨m, n, rfl⟩ := hx
  by_cases hm : m = 0
  · have hn : n ≠ 0 := by
      rintro rfl
      subst hm
      exact h0 (by simp)
    have k1 := key (m • e₀ + n • ((2 : ℝ) • e₁)) 1
    rw [coord1, abs_mul] at k1
    have : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
    norm_num at k1
    linarith
  · have k0 := key (m • e₀ + n • ((2 : ℝ) • e₁)) 0
    rw [coord0] at k0
    have : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm
    linarith

/- English proof (translation)
Use `discreteTopology_of_isOpen_singleton_zero (Metric.isOpen_singleton_iff.2 ⟨1, one_pos, fun y hy => ?_⟩)` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hy0 : (y : E2) ≠ 0` using `fun h => hne (Subtype.ext h)`. Use `one_le_norm (hN y.2) hy0` as an intermediate fact. Rewrite `hy` using `[dist_zero_right, Submodule.coe_norm]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem discrete_of_le (N : Submodule ℤ E2) (hN : N ≤ Lx) : DiscreteTopology N := by
  refine discreteTopology_of_isOpen_singleton_zero
    (Metric.isOpen_singleton_iff.2 ⟨1, one_pos, fun y hy => ?_⟩)
  by_contra hne
  have hy0 : (y : E2) ≠ 0 := fun h => hne (Subtype.ext h)
  have := one_le_norm (hN y.2) hy0
  rw [dist_zero_right, Submodule.coe_norm] at hy
  linarith

def vx : Fin 2 → E2 := ![e₀, (2 : ℝ) • e₁]

/- English proof (translation)
Unfold `vx`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`. Establish `h0` using `congrArg (fun v : E2 => v 0) hst`. Establish `h1` using `congrArg (fun v : E2 => v 1) hst`.

Simplify using `only [coord0, coord1] at h0 h1`. Simplify using `only [PiLp.zero_apply] at h0 h1`. Prove the components needed by the constructor for the conclusion. Conclude with `h0` after adjusting the coercions. Establish `: (t : ℝ) = 0` using `by linarith`.

Conclude with `this` after adjusting the coercions.
-/
theorem vx_li : LinearIndependent ℤ vx := by
  unfold vx
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h0 := congrArg (fun v : E2 => v 0) hst
  have h1 := congrArg (fun v : E2 => v 1) hst
  simp only [coord0, coord1] at h0 h1
  simp only [PiLp.zero_apply] at h0 h1
  constructor
  · exact_mod_cast h0
  · have : (t : ℝ) = 0 := by linarith
    exact_mod_cast this

/- English proof (translation)
Rewrite using `[Lx]`. Use `congr 1`. Use extensionality with `x`. Simplify using `[vx, Fin.exists_fin_two, eq_comm]`. The claim follows by propositional logic.
-/
theorem Lx_eq : Lx = Submodule.span ℤ (Set.range vx) := by
  rw [Lx]
  congr 1
  ext x
  simp [vx, Fin.exists_fin_two, eq_comm]
  tauto

/- English proof (translation)
Rewrite using `[Formalism.F.rk, Lx_eq, finrank_span_eq_card vx_li]`. Simplify using the standard rewrite rules.
-/
theorem rk_Lx : Formalism.F.rk Lx = 2 := by
  rw [Formalism.F.rk, Lx_eq, finrank_span_eq_card vx_li]
  simp

/- English proof (translation)
Use `haveI := discrete_of_le Lx le_rfl`. Set `b : Basis (Fin 2) ℤ Lx` to `(Basis.span vx_li).map (LinearEquiv.ofEq _ _ Lx_eq.symm)`. Establish `hb : ∀ i, (b i : E2) = vx i` using `fun i => by simp [b, Basis.span_apply]`. Rewrite using `[Formalism.F.covolEqGram E2 Lx (Fin 2) b]`. Establish `hg : Matrix.gram ℝ (fun i => (b i : E2)) = !![1, 0; 0, 4]`.

Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [Matrix.gram_apply, hb, vx, e₀, e₁, inner_smul_left, inner_smul_right, EuclideanSpace.inner_single_left, norm_smul, EuclideanSpace.norm_single] <;> norm_num`. Rewrite using `[hg, Matrix.det_fin_two_of, show (1 : ℝ) * 4 - 0 * 0 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]`.
-/
theorem covol_Lx : Formalism.F.covol Lx = 2 := by
  haveI := discrete_of_le Lx le_rfl
  let b : Basis (Fin 2) ℤ Lx := (Basis.span vx_li).map (LinearEquiv.ofEq _ _ Lx_eq.symm)
  have hb : ∀ i, (b i : E2) = vx i := fun i => by simp [b, Basis.span_apply]
  rw [Formalism.F.covolEqGram E2 Lx (Fin 2) b]
  have hg : Matrix.gram ℝ (fun i => (b i : E2)) = !![1, 0; 0, 4] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.gram_apply, hb, vx, e₀, e₁, inner_smul_left, inner_smul_right,
        EuclideanSpace.inner_single_left, norm_smul, EuclideanSpace.norm_single] <;> norm_num
  rw [hg, Matrix.det_fin_two_of, show (1 : ℝ) * 4 - 0 * 0 = 2 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _))`.
-/
theorem Px_le : Px ≤ Lx := Submodule.span_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _))

/- English proof (translation)
Introduce `h`. Use `congrArg (fun v : E2 => v 0) h` as an intermediate fact. Simplify using `[e₀] at this`.
-/
theorem e₀_ne : e₀ ≠ 0 := by
  intro h
  have := congrArg (fun v : E2 => v 0) h
  simp [e₀] at this

/- English proof (translation)
Conclude with `(Formalism.F.covolBasic E2).2 e₀ e₀_ne |>.trans (by simp [e₀])`.
-/
theorem covol_Px : Formalism.F.covol Px = 1 := by
  exact (Formalism.F.covolBasic E2).2 e₀ e₀_ne |>.trans (by simp [e₀])

/- English proof (translation)
Establish `hli : LinearIndependent ℤ ![e₀]`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`. Use `fin_cases i`. Use `congrArg (fun v : E2 => v 0) hg` as an intermediate fact.

Simplify `this` using `[e₀]`. Establish `hP : Px = Submodule.span ℤ (Set.range ![e₀])` using `by simp [Px]`. Rewrite using `[Formalism.F.rk, hP, finrank_span_eq_card hli]`. Simplify using the standard rewrite rules.
-/
theorem rk_Px : Formalism.F.rk Px = 1 := by
  have hli : LinearIndependent ℤ ![e₀] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    fin_cases i
    have := congrArg (fun v : E2 => v 0) hg
    simpa [e₀] using this
  have hP : Px = Submodule.span ℤ (Set.range ![e₀]) := by simp [Px]
  rw [Formalism.F.rk, hP, finrank_span_eq_card hli]
  simp

end PolygonExample

section Main

open PolygonExample

local notation "ρx" => AddMonoidHom.id E2

/- English proof (translation)
Simplify using `only [Formalism.HN.deg, zl_id]`.
-/
theorem ex_deg (N : Submodule ℤ E2) : deg ρx N = Formalism.F.deg N := by
  simp only [Formalism.HN.deg, zl_id]
/- English proof (translation)
Simplify using `only [Formalism.HN.rk, zl_id]`.
-/
theorem ex_rk (N : Submodule ℤ E2) : rk ρx N = Formalism.F.rk N := by
  simp only [Formalism.HN.rk, zl_id]
/- English proof (translation)
Simplify using `only [Formalism.HN.slope, zl_id]`.
-/
theorem ex_slope (N : Submodule ℤ E2) : slope ρx N = Formalism.F.slope N := by
  simp only [Formalism.HN.slope, zl_id]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun x _ y _ h => h, by rw [zl_id]; exact discrete_of_le N hN⟩`.
-/
theorem ex_isLat (N : Submodule ℤ E2) (hN : N ≤ Lx) : IsLat ρx N := ⟨fun x _ y _ h => h, by rw [zl_id]; exact discrete_of_le N hN⟩

/- English proof (translation)
Use `haveI hd : DiscreteTopology N := discrete_of_le N hN`. Use `haveI : DiscreteTopology Lx := discrete_of_le Lx le_rfl`. Use `haveI : Module.Finite ℤ Lx := by`. Rewrite using `[Lx]`. Conclude with `Module.Finite.span_of_finite ℤ (Set.toFinite _)`.

Establish `hrk : Formalism.F.rk N ≤ 2`. Conclude with `(Submodule.finrank_mono hN).trans rk_Lx.le`. Establish `h2 : Formalism.F.rk N = 2 → 2 ≤ Formalism.F.covol N`. Introduce `h`. Use `Formalism.F.covolAntiSameRank E2 N Lx inferInstance hN (by rw [h, rk_Lx])` as an intermediate fact.

Rewrite `this` using `[covol_Lx]`. Then use the resulting hypothesis. Establish `h1 : 1 ≤ Formalism.F.covol N`. Distinguish the cases in `hb : N = ⊥`. Substitute `hb` using the available equality. Rewrite using `[(Formalism.F.covolBasic E2).1]`.

Take `⟨v, hv, hv0, hvn⟩` from `Formalism.F.shortVector E2 N hd hb`. Establish `hv1` using `one_le_norm (hN hv) hv0`. Take `h | h | h : Formalism.F.rk N = 0 ∨ Formalism.F.rk N = 1 ∨ Formalism.F.rk N = 2` from `by omega`. Rewrite `hvn` using `[h]`. Simplify using `at hvn`.

Conclude with `absurd hvn hv0`. Rewrite `hvn` using `[h]`. Simplify using `at hvn`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear relations using `[h2 h]`.

Use `⟨hrk, ?_, fun h => ?_⟩` and prove the remaining obligations. Simplify using `only [Formalism.F.deg]`. Combine the linear relations using `[Real.log_nonneg h1]`. Simplify using `only [Formalism.F.deg]`. Combine the linear relations using `[Real.log_le_log (by norm_num) (h2 h)]`.
-/
theorem ex_bounds (N : Submodule ℤ E2) (hN : N ≤ Lx) :
    Formalism.F.rk N ≤ 2 ∧ Formalism.F.deg N ≤ 0 ∧ (Formalism.F.rk N = 2 → Formalism.F.deg N ≤ - Real.log 2) := by
  haveI hd : DiscreteTopology N := discrete_of_le N hN
  haveI : DiscreteTopology Lx := discrete_of_le Lx le_rfl
  haveI : Module.Finite ℤ Lx := by
    rw [Lx]
    exact Module.Finite.span_of_finite ℤ (Set.toFinite _)
  have hrk : Formalism.F.rk N ≤ 2 := by
    exact (Submodule.finrank_mono hN).trans rk_Lx.le
  have h2 : Formalism.F.rk N = 2 → 2 ≤ Formalism.F.covol N := by
    intro h
    have := Formalism.F.covolAntiSameRank E2 N Lx inferInstance hN (by rw [h, rk_Lx])
    rwa [covol_Lx] at this
  have h1 : 1 ≤ Formalism.F.covol N := by
    by_cases hb : N = ⊥
    · subst hb
      rw [(Formalism.F.covolBasic E2).1]
    obtain ⟨v, hv, hv0, hvn⟩ := Formalism.F.shortVector E2 N hd hb
    have hv1 := one_le_norm (hN hv) hv0
    obtain h | h | h : Formalism.F.rk N = 0 ∨ Formalism.F.rk N = 1 ∨ Formalism.F.rk N = 2 := by omega
    · rw [h] at hvn
      simp at hvn
      exact absurd hvn hv0
    · rw [h] at hvn
      simp at hvn
      linarith
    · linarith [h2 h]
  refine ⟨hrk, ?_, fun h => ?_⟩
  · simp only [Formalism.F.deg]
    linarith [Real.log_nonneg h1]
  · simp only [Formalism.F.deg]
    linarith [Real.log_le_log (by norm_num) (h2 h)]

/- English proof (translation)
Use `⟨Px_le, ?_⟩` and prove the remaining obligations. Rewrite using `[zl_id, zl_id]`. Use `⟨Px_le, fun x hx hxs => ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[Lx, Submodule.mem_span_pair]`. Take `⟨m, n, rfl⟩` from `hx`.

Rewrite `hxs` using `[Px, Submodule.span_span_of_tower, Submodule.mem_span_singleton]`. Take `⟨c, hc⟩` from `hxs`. Establish `h2 : (2 : ℝ) * n = 0`. Rewrite using `[← coord1 m n, ← hc]`. Simplify using `[e₀]`.

Establish `hn : n = 0`. Establish `: (n : ℝ) = 0` using `by linarith`. Conclude with `this` after adjusting the coercions. Substitute `hn` using the available equality. Simplify using `only [zero_smul, add_zero]`.

Conclude with `Submodule.smul_mem _ m (Submodule.mem_span_singleton_self e₀)`.
-/
theorem ex_Psat : IsSat ρx Lx Px := by
  refine ⟨Px_le, ?_⟩
  rw [zl_id, zl_id]
  refine ⟨Px_le, fun x hx hxs => ?_⟩
  rw [Lx, Submodule.mem_span_pair] at hx
  obtain ⟨m, n, rfl⟩ := hx
  rw [Px, Submodule.span_span_of_tower, Submodule.mem_span_singleton] at hxs
  obtain ⟨c, hc⟩ := hxs
  have h2 : (2 : ℝ) * n = 0 := by
    rw [← coord1 m n, ← hc]
    simp [e₀]
  have hn : n = 0 := by
    have : (n : ℝ) = 0 := by linarith
    exact_mod_cast this
  subst hn
  simp only [zero_smul, add_zero]
  exact Submodule.smul_mem _ m (Submodule.mem_span_singleton_self e₀)

/- English proof (translation)
Substitute `hn` using the available equality. Establish `hle : ∀ j, s j ≤ 0`. Introduce `j`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Use `hpos (s j) h` as an intermediate fact. Rewrite `this` using `[Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Conclude with `this (Finset.mem_univ j) le_rfl`. Establish `h10 : s 1 ≤ s 0` using `hanti (by decide)`. Establish `hs1 : s 1 < 0`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `hu : (Finset.univ.filter (fun j : Fin 2 => (0 : ℝ) ≤ s j)) = Finset.univ`. Use extensionality with `j`. Apply the tactic sequence `fin_cases j <;> simp <;> linarith`.

Rewrite `h0` using `[hu]`. Simplify using `at h0`. Establish `hs0 : s 0 = 0`. Assume the negation of the conclusion as `h`. Establish `hlt : s 0 < 0` using `lt_of_le_of_ne (hle 0) h`.

Establish `he : (Finset.univ.filter (fun j : Fin 2 => (0 : ℝ) ≤ s j)) = ∅`. Use extensionality with `j`. Apply the tactic sequence `fin_cases j <;> simp <;> linarith`. Rewrite `h0` using `[he]`. Simplify using `at h0`.

Rewrite `hsum` using `[Fin.sum_univ_two, hs0, zero_add]`. Introduce `j`. Apply the tactic sequence `fin_cases j <;> simp [hs0, hsum]`.
-/
theorem ex_slopes (n : ℕ) (s : Fin n → ℝ) (hn : n = 2) (hanti : Antitone s)
    (hpos : ∀ θ : ℝ, 0 < θ → (Finset.univ.filter (fun j => θ ≤ s j)).card = 0)
    (h0 : (Finset.univ.filter (fun j => (0 : ℝ) ≤ s j)).card = 1)
    (hsum : ∑ j, s j = - Real.log 2) :
    ∀ j : Fin n, s j = if (j : ℕ) = 0 then 0 else - Real.log 2 := by
  subst hn
  have hle : ∀ j, s j ≤ 0 := by
    intro j
    by_contra h
    push_neg at h
    have := hpos (s j) h
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at this
    exact this (Finset.mem_univ j) le_rfl
  have h10 : s 1 ≤ s 0 := hanti (by decide)
  have hs1 : s 1 < 0 := by
    by_contra h
    push_neg at h
    have hu : (Finset.univ.filter (fun j : Fin 2 => (0 : ℝ) ≤ s j)) = Finset.univ := by
      ext j
      fin_cases j <;> simp <;> linarith
    rw [hu] at h0
    simp at h0
  have hs0 : s 0 = 0 := by
    by_contra h
    have hlt : s 0 < 0 := lt_of_le_of_ne (hle 0) h
    have he : (Finset.univ.filter (fun j : Fin 2 => (0 : ℝ) ≤ s j)) = ∅ := by
      ext j
      fin_cases j <;> simp <;> linarith
    rw [he] at h0
    simp at h0
  rw [Fin.sum_univ_two, hs0, zero_add] at hsum
  intro j
  fin_cases j <;> simp [hs0, hsum]

/- English proof (translation)
Establish `hlog : 0 < Real.log 2` using `Real.log_pos (by norm_num)`. Establish `hL : IsLat ρx Lx` using `ex_isLat Lx le_rfl`. Establish `he₀L : e₀ ∈ Lx` using `Submodule.subset_span (Set.mem_insert _ _)`. Establish `he₀P : e₀ ∈ Px` using `Submodule.mem_span_singleton_self e₀`. Establish `hLne : Lx ≠ ⊥` using `fun h => e₀_ne (by rw [h] at he₀L; simpa using he₀L)`.

Establish `hPne : Px ≠ ⊥` using `fun h => e₀_ne (by rw [h] at he₀P; simpa using he₀P)`. Establish `rkL : rk ρx Lx = 2` using `by rw [ex_rk, rk_Lx]`. Establish `rkP : rk ρx Px = 1` using `by rw [ex_rk, rk_Px]`. Establish `degL : deg ρx Lx = - Real.log 2` using `by rw [ex_deg, Formalism.F.deg, covol_Lx]`. Establish `degP : deg ρx Px = 0` using `by rw [ex_deg, Formalism.F.deg, covol_Px]; simp`.

Establish `rkbot : rk ρx (⊥ : Submodule ℤ E2) = 0` using `by rw [ex_rk, Formalism.F.rk]; simp`. Establish `bnd : ∀ N, N ≤ Lx → (rk ρx N ≤ 2 ∧ deg ρx N ≤ 0 ∧ (rk ρx N = 2 → deg ρx N ≤ - Real.log 2))`. Introduce `N hN`. Rewrite using `[ex_rk, ex_deg]`. Conclude with `ex_bounds N hN`.

Establish `mc` using `fun N (hN : N ≤ Lx) (hne : N ≠ ⊥) => h1 ℤ E2 E2 ρx N (ex_isLat N hN) hne`. Establish `mumin_le : ∀ N, N ≤ Lx → N ≠ ⊥ → muMin ρx N ≤ deg ρx N / rk ρx N`. Introduce `N hN hne`. Use `(mc N hN hne).2.2.2.1` as an intermediate fact. Rewrite `this` using `[ex_slope, Formalism.F.slope, ← ex_deg, ← ex_rk]`. Then use the resulting hypothesis.

Establish `muMax0 : muMax ρx Lx = 0`. Apply `le_antisymm` to reduce the goal to its premises. Use `((mc Lx le_rfl hLne).1 0).2 (fun N hN => ?_)` and prove the remaining obligations. Rewrite using `[zero_mul]`. Conclude with `(bnd N hN).2.1`.

Use `((mc Lx le_rfl hLne).1 (muMax ρx Lx)).1 le_rfl Px Px_le` as an intermediate fact. Rewrite `this` using `[degP, rkP]`. Simplify using `using this`. Establish `muMinL : muMin ρx Lx = - Real.log 2`. Apply `le_antisymm` to reduce the goal to its premises.

Use `((mc Lx le_rfl hLne).2.1 (muMin ρx Lx)).1 le_rfl Px Px_le` as an intermediate fact. Rewrite `this` using `[degP, rkP, rkL, degL]`. Evaluate the numerical expressions using `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Use `((mc Lx le_rfl hLne).2.1 _).2 (fun N hN => ?_)` and prove the remaining obligations.

Rewrite using `[rkL, degL]`. Take `⟨b1, b2, b3⟩` from `bnd N hN`. Take `h | h | h : rk ρx N = 0 ∨ rk ρx N = 1 ∨ rk ρx N = 2` from `by omega`. Rewrite using `[h]`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[h]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Use `b3 h` as an intermediate fact.

Rewrite using `[h]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs` using `fun θ => h2 ℤ E2 E2 ρx Lx hL θ`. Establish `hpos : ∀ θ : ℝ, 0 < θ → hnStep ρx Lx θ = ⊥`.

Introduce `θ hθ`. Assume the negation of the conclusion as `hne`. Establish `hSL : hnStep ρx Lx θ ≤ Lx` using `(hs θ).1.1`. Establish `h₁` using `(hs θ).2.1 hne`. Establish `h₂` using `mumin_le _ hSL hne`.

Establish `h₃ : deg ρx (hnStep ρx Lx θ) / rk ρx (hnStep ρx Lx θ) ≤ 0` using `div_nonpos_of_nonpos_of_nonneg (bnd _ hSL).2.1 (Nat.cast_nonneg _)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `muMinP : 0 ≤ muMin ρx Px`. Use `((mc Px Px_le hPne).2.1 0).2 (fun N hN => ?_)` and prove the remaining obligations. Rewrite using `[zero_mul, degP]`.

Combine the linear relations using `[(bnd N (hN.trans Px_le)).2.1]`. Establish `step0 : hnStep ρx Lx 0 = Px`. Establish `hPS : Px ≤ hnStep ρx Lx 0` using `(hs 0).2.2.1 Px Px_le hPne muMinP`. Establish `hSL : hnStep ρx Lx 0 ≤ Lx` using `(hs 0).1.1`. Establish `hSne : hnStep ρx Lx 0 ≠ ⊥` using `fun h => hPne (le_bot_iff.1 (h ▸ hPS))`.

Establish `hrkS : rk ρx (hnStep ρx Lx 0) ≠ 2`. Introduce `h`. Establish `h₁` using `(hs 0).2.1 hSne`. Establish `h₂` using `mumin_le _ hSL hSne`. Rewrite `h₂` using `[h]`.

Use `(bnd _ hSL).2.2 h` as an intermediate fact. Move the coercions through the operations in `at h₂`. Combine the linear equalities and inequalities to obtain the conclusion. Use `le_antisymm ?_ hPS` and prove the remaining obligations. Introduce `x hx`.

Establish `hxL` using `hSL hx`. Rewrite `hxL` using `[Lx, Submodule.mem_span_pair]`. Take `⟨m, n, hmn⟩` from `hxL`. Distinguish the cases in `hn : n = 0`. Substitute `hn` using the available equality.

Rewrite using `[← hmn]`. Simplify using `only [zero_smul, add_zero]`. Conclude with `Submodule.smul_mem _ m he₀P`. It suffices to derive a contradiction. Apply `hrkS` to reduce the goal to its premises.

Use `haveI := discrete_of_le _ hSL`. Establish `hli : LinearIndependent ℤ ![(⟨e₀, hPS he₀P⟩ : hnStep ρx Lx 0), (⟨x, hx⟩ : hnStep ρx Lx 0)]`. Apply `LinearIndependent.of_comp (hnStep ρx Lx 0).subtype` to reduce the goal to its premises. Rewrite using `[show (hnStep ρx Lx 0).subtype ∘ ![(⟨e₀, hPS he₀P⟩ : hnStep ρx Lx 0), (⟨x, hx⟩ : hnStep ρx Lx 0)] = ![e₀, x] by`. Use extensionality with `i : 1`.

Apply the tactic sequence `fin_cases i <;> rfl]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`. Establish `key : s • e₀ + t • x = (s + t * m) • e₀ + (t * n) • ((2 : ℝ) • e₁)`. Rewrite using `[← hmn]`.

Use `module`. Rewrite `hst` using `[key]`. Establish `c0` using `congrArg (fun v : E2 => v 0) hst`. Establish `c1` using `congrArg (fun v : E2 => v 1) hst`. Simplify using `only [coord0, coord1, PiLp.zero_apply] at c0 c1`.

Establish `ht : t = 0`. Move the coercions through the operations in `at c1`. Establish `h' : (t : ℝ) * n = 0` using `by linarith`. Establish `h'' : t * n = 0` using `by exact_mod_cast h'`. Conclude with `(mul_eq_zero.1 h'').resolve_right hn`.

Substitute `ht` using the available equality. Use `⟨?_, rfl⟩` and prove the remaining obligations. Simplify using `using c0`. Establish `hc` using `hli.fintype_card_le_finrank`. Simplify using `only [Fintype.card_fin] at hc`.

Establish `hle2` using `(bnd _ hSL).1`. Rewrite `hle2`, the goal using `[ex_rk, Formalism.F.rk]`. Use linear arithmetic over natural numbers and integers. Establish `stepL : hnStep ρx Lx (- Real.log 2) = Lx` using `le_antisymm (hs _).1.1 ((hs _).2.2.1 Lx le_rfl hLne (by rw [muMinL]))`. Establish `hsl` using `h3 ℤ E2 E2 ρx Lx hL`.

Establish `hslopes` using `ex_slopes (rk ρx Lx) (slopeList ρx Lx) rkL hsl.1 (fun θ hθ => by rw [hsl.2.1 θ, hpos θ hθ, rkbot]) (by rw [hsl.2.1 0, step0, rkP]) (by rw [hsl.2.2.1, degL])`. Unfold `Example`. Conclude with `⟨hL, rkL, hslopes, step0, stepL, muMax0, muMinL⟩`.
-/
theorem example_of (h1 : MuChar.{0, 0, 0}) (h2 : HNStep.{0, 0, 0}) (h3 : HNSlopes.{0, 0, 0}) :
    Example := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : IsLat ρx Lx := ex_isLat Lx le_rfl
  have he₀L : e₀ ∈ Lx := Submodule.subset_span (Set.mem_insert _ _)
  have he₀P : e₀ ∈ Px := Submodule.mem_span_singleton_self e₀
  have hLne : Lx ≠ ⊥ := fun h => e₀_ne (by rw [h] at he₀L; simpa using he₀L)
  have hPne : Px ≠ ⊥ := fun h => e₀_ne (by rw [h] at he₀P; simpa using he₀P)
  have rkL : rk ρx Lx = 2 := by rw [ex_rk, rk_Lx]
  have rkP : rk ρx Px = 1 := by rw [ex_rk, rk_Px]
  have degL : deg ρx Lx = - Real.log 2 := by rw [ex_deg, Formalism.F.deg, covol_Lx]
  have degP : deg ρx Px = 0 := by rw [ex_deg, Formalism.F.deg, covol_Px]; simp
  have rkbot : rk ρx (⊥ : Submodule ℤ E2) = 0 := by rw [ex_rk, Formalism.F.rk]; simp
  have bnd : ∀ N, N ≤ Lx →
      (rk ρx N ≤ 2 ∧ deg ρx N ≤ 0 ∧ (rk ρx N = 2 → deg ρx N ≤ - Real.log 2)) := by
    intro N hN
    rw [ex_rk, ex_deg]
    exact ex_bounds N hN
  have mc := fun N (hN : N ≤ Lx) (hne : N ≠ ⊥) => h1 ℤ E2 E2 ρx N (ex_isLat N hN) hne
  have mumin_le : ∀ N, N ≤ Lx → N ≠ ⊥ → muMin ρx N ≤ deg ρx N / rk ρx N := by
    intro N hN hne
    have := (mc N hN hne).2.2.2.1
    rwa [ex_slope, Formalism.F.slope, ← ex_deg, ← ex_rk] at this
  have muMax0 : muMax ρx Lx = 0 := by
    apply le_antisymm
    · refine ((mc Lx le_rfl hLne).1 0).2 (fun N hN => ?_)
      rw [zero_mul]
      exact (bnd N hN).2.1
    · have := ((mc Lx le_rfl hLne).1 (muMax ρx Lx)).1 le_rfl Px Px_le
      rw [degP, rkP] at this
      simpa using this
  have muMinL : muMin ρx Lx = - Real.log 2 := by
    apply le_antisymm
    · have := ((mc Lx le_rfl hLne).2.1 (muMin ρx Lx)).1 le_rfl Px Px_le
      rw [degP, rkP, rkL, degL] at this
      norm_num at this
      linarith
    · refine ((mc Lx le_rfl hLne).2.1 _).2 (fun N hN => ?_)
      rw [rkL, degL]
      obtain ⟨b1, b2, b3⟩ := bnd N hN
      obtain h | h | h : rk ρx N = 0 ∨ rk ρx N = 1 ∨ rk ρx N = 2 := by omega
      · rw [h]; push_cast; linarith
      · rw [h]; push_cast; linarith
      · have := b3 h
        rw [h]; push_cast; linarith
  have hs := fun θ => h2 ℤ E2 E2 ρx Lx hL θ
  have hpos : ∀ θ : ℝ, 0 < θ → hnStep ρx Lx θ = ⊥ := by
    intro θ hθ
    by_contra hne
    have hSL : hnStep ρx Lx θ ≤ Lx := (hs θ).1.1
    have h₁ := (hs θ).2.1 hne
    have h₂ := mumin_le _ hSL hne
    have h₃ : deg ρx (hnStep ρx Lx θ) / rk ρx (hnStep ρx Lx θ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (bnd _ hSL).2.1 (Nat.cast_nonneg _)
    linarith
  have muMinP : 0 ≤ muMin ρx Px := by
    refine ((mc Px Px_le hPne).2.1 0).2 (fun N hN => ?_)
    rw [zero_mul, degP]
    linarith [(bnd N (hN.trans Px_le)).2.1]
  have step0 : hnStep ρx Lx 0 = Px := by
    have hPS : Px ≤ hnStep ρx Lx 0 := (hs 0).2.2.1 Px Px_le hPne muMinP
    have hSL : hnStep ρx Lx 0 ≤ Lx := (hs 0).1.1
    have hSne : hnStep ρx Lx 0 ≠ ⊥ := fun h => hPne (le_bot_iff.1 (h ▸ hPS))
    have hrkS : rk ρx (hnStep ρx Lx 0) ≠ 2 := by
      intro h
      have h₁ := (hs 0).2.1 hSne
      have h₂ := mumin_le _ hSL hSne
      rw [h] at h₂
      have := (bnd _ hSL).2.2 h
      push_cast at h₂
      linarith
    refine le_antisymm ?_ hPS
    intro x hx
    have hxL := hSL hx
    rw [Lx, Submodule.mem_span_pair] at hxL
    obtain ⟨m, n, hmn⟩ := hxL
    by_cases hn : n = 0
    · subst hn
      rw [← hmn]
      simp only [zero_smul, add_zero]
      exact Submodule.smul_mem _ m he₀P
    exfalso
    apply hrkS
    haveI := discrete_of_le _ hSL
    have hli : LinearIndependent ℤ
        ![(⟨e₀, hPS he₀P⟩ : hnStep ρx Lx 0), (⟨x, hx⟩ : hnStep ρx Lx 0)] := by
      apply LinearIndependent.of_comp (hnStep ρx Lx 0).subtype
      rw [show (hnStep ρx Lx 0).subtype ∘
          ![(⟨e₀, hPS he₀P⟩ : hnStep ρx Lx 0), (⟨x, hx⟩ : hnStep ρx Lx 0)] = ![e₀, x] by
        ext i : 1
        fin_cases i <;> rfl]
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have key : s • e₀ + t • x = (s + t * m) • e₀ + (t * n) • ((2 : ℝ) • e₁) := by
        rw [← hmn]
        module
      rw [key] at hst
      have c0 := congrArg (fun v : E2 => v 0) hst
      have c1 := congrArg (fun v : E2 => v 1) hst
      simp only [coord0, coord1, PiLp.zero_apply] at c0 c1
      have ht : t = 0 := by
        push_cast at c1
        have h' : (t : ℝ) * n = 0 := by linarith
        have h'' : t * n = 0 := by exact_mod_cast h'
        exact (mul_eq_zero.1 h'').resolve_right hn
      subst ht
      refine ⟨?_, rfl⟩
      simpa using c0
    have hc := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hc
    have hle2 := (bnd _ hSL).1
    rw [ex_rk, Formalism.F.rk] at hle2 ⊢
    omega
  have stepL : hnStep ρx Lx (- Real.log 2) = Lx :=
    le_antisymm (hs _).1.1 ((hs _).2.2.1 Lx le_rfl hLne (by rw [muMinL]))
  have hsl := h3 ℤ E2 E2 ρx Lx hL
  have hslopes := ex_slopes (rk ρx Lx) (slopeList ρx Lx) rkL hsl.1
    (fun θ hθ => by rw [hsl.2.1 θ, hpos θ hθ, rkbot])
    (by rw [hsl.2.1 0, step0, rkP])
    (by rw [hsl.2.2.1, degL])
  unfold Example
  exact ⟨hL, rkL, hslopes, step0, stepL, muMax0, muMinL⟩

/- English proof (translation)
The claim follows from `example_of slope_characterization (hnStep_of degree_supermodular slope_characterization maximal_slope_ratio finite_supremum_slopes real_saturation_property saturation_basic_properties) polygon_slopes_characterization`.
-/
theorem polygon_worked_example : Example := example_of slope_characterization
  (hnStep_of degree_supermodular slope_characterization maximal_slope_ratio finite_supremum_slopes real_saturation_property saturation_basic_properties)
  polygon_slopes_characterization

end Main

end Formalism.HN
