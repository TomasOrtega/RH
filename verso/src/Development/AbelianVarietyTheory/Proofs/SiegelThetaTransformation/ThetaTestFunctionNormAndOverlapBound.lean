import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructurePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariantStatement

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.PhiNorm

section Product

variable {κ ι α : Type} [Fintype κ] [Fintype ι]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Use `⟨isSB_zero, ?_⟩` and prove the remaining obligations. Use `TensVac.ip_smul_left 0 h' h'` as an intermediate fact. Simplify using `using this`.

Consider the case `insert a s ha ih`. Take `⟨h1, h2⟩` from `ih fun φ hφ => hs φ (Finset.mem_insert_of_mem hφ)`. Establish `h3` using `hs a (Finset.mem_insert_self _ _)`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, TensVac.ip_add_left h3 h1 h', h2]`. Conclude with `⟨(GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι _ _ h3 h1).1, rfl⟩`.
-/
theorem sum_left (s : Finset α) (f : α → Matrix κ ι ℚ → ℂ) {ψ : Matrix κ ι ℚ → ℂ}
    (hs : ∀ a ∈ s, IsSB (f a)) (h' : IsSB ψ) :
    IsSB (∑ a ∈ s, f a) ∧ SW.ip (∑ a ∈ s, f a) ψ = ∑ a ∈ s, SW.ip (f a) ψ := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨isSB_zero, ?_⟩
    have := TensVac.ip_smul_left 0 h' h'
    simpa using this
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih fun φ hφ => hs φ (Finset.mem_insert_of_mem hφ)
    have h3 := hs a (Finset.mem_insert_self _ _)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, TensVac.ip_add_left h3 h1 h', h2]
    exact ⟨(GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι _ _ h3 h1).1, rfl⟩

/- English proof (translation)
Rewrite using `[(sum_left s f hf (sum_left s f' hf' isSB_zero).1).2]`. Use `Finset.sum_congr rfl fun a ha => ?_` and prove the remaining obligations. Rewrite using `[TensVac.ip_conj (sum_left s f' hf' isSB_zero).1 (hf a ha), (sum_left s f' hf' (hf a ha)).2, map_sum, Finset.sum_eq_single_of_mem a ha, ← TensVac.ip_conj (hf' a ha) (hf a ha)]`. Introduce `b hb hba`. Rewrite using `[← TensVac.ip_conj (hf' b hb) (hf a ha)]`.

Assume the negation of the conclusion as `h0`. Conclude with `hba (h a ha b hb h0).symm`.
-/
theorem ip_sum_diag (s : Finset α) (f f' : α → Matrix κ ι ℚ → ℂ) (hf : ∀ a ∈ s, IsSB (f a))
    (hf' : ∀ a ∈ s, IsSB (f' a)) (h : ∀ a ∈ s, ∀ b ∈ s, SW.ip (f a) (f' b) ≠ 0 → a = b) :
    SW.ip (∑ a ∈ s, f a) (∑ a ∈ s, f' a) = ∑ a ∈ s, SW.ip (f a) (f' a) := by
  rw [(sum_left s f hf (sum_left s f' hf' isSB_zero).1).2]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [TensVac.ip_conj (sum_left s f' hf' isSB_zero).1 (hf a ha), (sum_left s f' hf' (hf a ha)).2,
    map_sum, Finset.sum_eq_single_of_mem a ha, ← TensVac.ip_conj (hf' a ha) (hf a ha)]
  intro b hb hba
  rw [← TensVac.ip_conj (hf' b hb) (hf a ha)]
  by_contra h0
  exact hba (h a ha b hb h0).symm

end Product

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

/- English proof (translation)
Establish `H` using `(heisG_laws E r X g bas idx n hs hn).2.2.2`. Establish `key : ∀ (y : Matrix (Fin n) (Fin r) E) (v : TF n g), IsSB v → epsW X w δ • heisG X bas δ v = v → epsW X w δ • heisG X bas δ (heisG X bas y v) = cexp (-(2 * π * I * ((∑ k, EF X (δ k) (y k) : ℚ) : ℂ))) • heisG X bas y v`. Introduce `y v hv h`. Establish `e : heisG X bas δ (heisG X bas y v) = cexp (-(2 * π * I * ((∑ k, EF X (δ k) (y k) : ℚ) : ℂ))) • heisG X bas y (heisG X bas δ v)`. Rewrite using `[(H δ v hv).2.2.1 y, (H y v hv).2.2.1 δ, smul_smul, ← Complex.exp_add, add_comm y, TensVac.sumEF_swap hs δ y]`.

Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, smul_comm, ← TensVac.heisG_smul, h]`. Establish `h1` using `(H y v hv).1`.

Establish `h2` using `(H y' v' hv').1`. Establish `h3` using `(H δ _ h1).2.2.2.1 _ h2`. Establish `h4 : SW.ip (epsW X w δ • heisG X bas δ (heisG X bas y v)) (epsW X w δ • heisG X bas δ (heisG X bas y' v')) = SW.ip (heisG X bas y v) (heisG X bas y' v')`. Rewrite using `[TensVac.ip_smul_left _ (H δ _ h1).1 (TensVac.sb_smul _ (H δ _ h2).1), TensVac.ip_smul_right _ (H δ _ h1).1 (H δ _ h2).1, ← mul_assoc, TensVac.epsW_mul_conj, one_mul, h3]`. Rewrite `h4` using `[key y v hv h, key y' v' hv' h', TensVac.ip_smul_left _ h1 (TensVac.sb_smul _ h2), TensVac.ip_smul_right _ h1 h2, ← mul_assoc, mul_left_eq_self₀, or_iff_left h0, ← Complex.exp_conj, ← Complex.exp_add, Complex.exp_eq_one_iff]`.

Take `⟨k, hk⟩` from `h4`. Use `⟨-k, ?_⟩` and prove the remaining obligations. Establish `e : ∑ i, EF X (δ i) ((y - y') i) = ∑ i, EF X (δ i) (y i) - ∑ i, EF X (δ i) (y' i)`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Establish `: (y - y') i = y i - y' i` using `rfl`. Simplify using `only [TensLat.EF_eq_bilin, this, map_sub]`. Rewrite using `[e]`. Simplify using `only [map_neg, map_mul, conj_ofReal, conj_I, map_ratCast, map_ofNat] at hk`. Establish `hπ : (2 * π * I : ℂ) ≠ 0` using `Complex.two_pi_I_ne_zero`.

Apply `Rat.cast_injective (α := ℂ)` to reduce the goal to its premises. Apply `mul_left_cancel₀ hπ` to reduce the goal to its premises. Move the coercions through the operations in `at hk ⊢`. Take the linear combination `-hk`.
-/
theorem pair_int (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n) {w : E}
    {v v' : TF n g} (hv : IsSB v) (hv' : IsSB v') {δ y y' : Matrix (Fin n) (Fin r) E}
    (h : epsW X w δ • heisG X bas δ v = v) (h' : epsW X w δ • heisG X bas δ v' = v')
    (h0 : SW.ip (heisG X bas y v) (heisG X bas y' v') ≠ 0) :
    ∃ k : ℤ, ∑ i, EF X (δ i) ((y - y') i) = k := by
  have H := (heisG_laws E r X g bas idx n hs hn).2.2.2
  have key : ∀ (y : Matrix (Fin n) (Fin r) E) (v : TF n g), IsSB v →
      epsW X w δ • heisG X bas δ v = v → epsW X w δ • heisG X bas δ (heisG X bas y v) =
        cexp (-(2 * π * I * ((∑ k, EF X (δ k) (y k) : ℚ) : ℂ))) • heisG X bas y v := by
    intro y v hv h
    have e : heisG X bas δ (heisG X bas y v) =
        cexp (-(2 * π * I * ((∑ k, EF X (δ k) (y k) : ℚ) : ℂ))) •
          heisG X bas y (heisG X bas δ v) := by
      rw [(H δ v hv).2.2.1 y, (H y v hv).2.2.1 δ, smul_smul, ← Complex.exp_add, add_comm y,
        TensVac.sumEF_swap hs δ y]
      congr 2
      push_cast
      ring
    rw [e, smul_comm, ← TensVac.heisG_smul, h]
  have h1 := (H y v hv).1
  have h2 := (H y' v' hv').1
  have h3 := (H δ _ h1).2.2.2.1 _ h2
  have h4 : SW.ip (epsW X w δ • heisG X bas δ (heisG X bas y v))
      (epsW X w δ • heisG X bas δ (heisG X bas y' v')) =
      SW.ip (heisG X bas y v) (heisG X bas y' v') := by
    rw [TensVac.ip_smul_left _ (H δ _ h1).1 (TensVac.sb_smul _ (H δ _ h2).1),
      TensVac.ip_smul_right _ (H δ _ h1).1 (H δ _ h2).1, ← mul_assoc, TensVac.epsW_mul_conj,
      one_mul, h3]
  rw [key y v hv h, key y' v' hv' h', TensVac.ip_smul_left _ h1 (TensVac.sb_smul _ h2),
    TensVac.ip_smul_right _ h1 h2, ← mul_assoc, mul_left_eq_self₀, or_iff_left h0,
    ← Complex.exp_conj, ← Complex.exp_add, Complex.exp_eq_one_iff] at h4
  obtain ⟨k, hk⟩ := h4
  refine ⟨-k, ?_⟩
  have e : ∑ i, EF X (δ i) ((y - y') i) = ∑ i, EF X (δ i) (y i) - ∑ i, EF X (δ i) (y' i) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (y - y') i = y i - y' i := rfl
    simp only [TensLat.EF_eq_bilin, this, map_sub]
  rw [e]
  simp only [map_neg, map_mul, conj_ofReal, conj_I, map_ratCast, map_ofNat] at hk
  have hπ : (2 * π * I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  apply Rat.cast_injective (α := ℂ)
  apply mul_left_cancel₀ hπ
  push_cast at hk ⊢
  linear_combination -hk

/- English proof (translation)
Set `c : 𝓞 E → 𝓞 E` to `fun a => ⟨cc (a : E), Base.isIntegral_cc a.isIntegral_coe⟩`. Establish `hc : ∀ a, ((c a : 𝓞 E) : E) = cc (a : E)` using `fun _ => rfl`. Establish `hm : ∀ m ∈ conjI 𝔪, c m ∈ 𝔪`. Introduce `m hm`. Proceed by induction on `hm using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨b, hb, e⟩` from `hx`. Establish `: c x = b` using `by ext; rw [hc, e]; simp [cc]`. Rewrite using `[this]` and apply the resulting hypothesis. Consider the case `zero`.

Establish `: c 0 = 0` using `by ext; rw [hc]; simp [cc]`. Rewrite using `[this]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy`. Establish `: c (x + y) = c x + c y` using `by ext; push_cast; simp [hc, cc]`.

Rewrite using `[this]`. Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx`. Establish `: c (a • x) = c a * c x` using `by ext; push_cast; simp [hc, cc]`. Rewrite using `[this]`.

Conclude with `Ideal.mul_mem_left _ _ hx`. Take `⟨a, ha, b, hb, hab⟩` from `Ideal.isCoprime_iff_exists.1 h`. Take `⟨u, rfl⟩` from `Ideal.mem_span_singleton'.1 ha`. Use `Ideal.isCoprime_iff_exists.2 ⟨c u * t', Ideal.mem_span_singleton'.2 ⟨_, rfl⟩, c b, hm b hb, ?_⟩` and prove the remaining obligations. Use `congrArg (fun a : 𝓞 E => cc (a : E)) hab` as an intermediate fact.

Use `ext`. Move the coercions through the operations in `at this ⊢`. Simplify `this` using `[hc, ht, cc]`.
-/
theorem coprime_cc {𝔪 : Ideal (𝓞 E)} {t t' : 𝓞 E} (ht : (t' : E) = cc (t : E))
    (h : IsCoprime (Ideal.span {t}) (conjI 𝔪)) : IsCoprime (Ideal.span {t'}) 𝔪 := by
  let c : 𝓞 E → 𝓞 E := fun a => ⟨cc (a : E), Base.isIntegral_cc a.isIntegral_coe⟩
  have hc : ∀ a, ((c a : 𝓞 E) : E) = cc (a : E) := fun _ => rfl
  have hm : ∀ m ∈ conjI 𝔪, c m ∈ 𝔪 := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, e⟩ := hx
      have : c x = b := by ext; rw [hc, e]; simp [cc]
      rwa [this]
    | zero =>
      have : c 0 = 0 := by ext; rw [hc]; simp [cc]
      rw [this]; exact zero_mem _
    | add x y _ _ hx hy =>
      have : c (x + y) = c x + c y := by ext; push_cast; simp [hc, cc]
      rw [this]; exact add_mem hx hy
    | smul a x _ hx =>
      have : c (a • x) = c a * c x := by ext; push_cast; simp [hc, cc]
      rw [this]; exact Ideal.mul_mem_left _ _ hx
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 h
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  refine Ideal.isCoprime_iff_exists.2 ⟨c u * t', Ideal.mem_span_singleton'.2 ⟨_, rfl⟩, c b,
    hm b hb, ?_⟩
  have := congrArg (fun a : 𝓞 E => cc (a : E)) hab
  ext
  push_cast at this ⊢
  simpa [hc, ht, cc] using this

omit [IsCMField E] in

/- English proof (translation)
Use `Submodule.smul_induction_on hv (fun a ha u hu => ?_) fun a b ha hb => ?_` and prove the remaining obligations. Rewrite using `[smul_comm]`. Conclude with `Submodule.smul_mem_smul ha (h u hu)`. Rewrite using `[smul_add]`. Conclude with `add_mem ha hb`.
-/
theorem smul_mem_smul {𝔪 : Ideal (𝓞 E)} {L L' : Lt E r} {t : 𝓞 E} (h : ∀ v ∈ L, t • v ∈ L')
    {v : Fin r → E} (hv : v ∈ 𝔪 • L) : t • v ∈ 𝔪 • L' := by
  refine Submodule.smul_induction_on hv (fun a ha u hu => ?_) fun a b ha hb => ?_
  · rw [smul_comm]; exact Submodule.smul_mem_smul ha (h u hu)
  · rw [smul_add]; exact add_mem ha hb

/- English proof (translation)
Take `⟨-, s, hs, hs1, -⟩` from `hL`. Take `⟨-, s', hs', -, hs2⟩` from `hL'`. Take `⟨N, -, hN, -, hN2⟩` from `hΛ.2.2`. Take `⟨a, ha, b, hb, hab⟩` from `Ideal.isCoprime_iff_exists.1 D.cop`. Set `t : 𝓞 E` to `⟨cc ((s' * s : 𝓞 E) : E), Base.isIntegral_cc (s' * s).isIntegral_coe⟩`.

Establish `ht : (t : E) = cc ((s' * s : 𝓞 E) : E)` using `rfl`. Establish `h1 : ∀ v ∈ D.sh L, (s' * s) • v ∈ D.sh L'` using `fun v hv c hc => by`. Rewrite using `[smul_comm]`. Conclude with `smul_mem_smul (fun u hu => by rw [mul_smul]; exact hs2 _ (hs1 u hu)) (hv c hc)`. Establish `hctr : ∀ (c : E) (d : Matrix (Fin n) (Fin r) E) (v : Fin n → E), TensLat.ctr (c • d) v = c • TensLat.ctr d v` using `fun c d v => by`.

Use function extensionality and compare the values at `j`. Simplify using `[TensLat.ctr, Finset.sum_apply, Finset.mul_sum, mul_left_comm]`. Establish `h2 : (t : E) • (y - y') ∈ tens Λ (D.sh L)`. Use `(TensLat.tens_selfDual hΛ hS _).2 fun δ hδ => ?_` and prove the remaining obligations. Take `⟨m, hm⟩` from `h (((s' * s : 𝓞 E) : E) • δ) (TensLat.smul_mem_tens hΛ (s' * s).isIntegral_coe hδ) (by`.

Rewrite `hδ`, the goal using `[TensLat.mem_tens_iff hΛ]`. Introduce `v hv`. Rewrite using `[hctr]`. Conclude with `h1 _ (hδ v hv))`. Use `⟨-m, ?_⟩` and prove the remaining obligations.

Rewrite using `[Int.cast_neg, ← hm, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[TensLat.EF_swap]`. Conclude with `congrArg Neg.neg (TensLat.EF_smul X _ _ _).symm`. Establish `h3` using `(TensLat.mem_tens_iff hΛ _ _).1 h2 _ (hN2 (Pi.single k 1) (Submodule.subset_span ⟨k, rfl⟩))`.

Establish `h4 : TensLat.ctr ((t : E) • (y - y')) ((N : E) • (Pi.single k 1 : Fin n → E)) = ((N : 𝓞 E) * t) • (y k - y' k)`. Rewrite using `[TensLat.ctr, Finset.sum_eq_single k]`. Use function extensionality and compare the values at `j`. Express the relevant statement in the definitionally equal form `_ = (((N : 𝓞 E) * t : 𝓞 E) : E) * (y k j - y' k j)`. Simplify using `[cc, mul_assoc, Algebra.smul_def]`.

Introduce `j _ hj`. Simplify using `[hj, cc]`. Simplify using the standard rewrite rules. Rewrite `h3` using `[h4]`. Use `⟨s * (b * (N * t)), ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [← Ideal.span_singleton_mul_span_singleton]`. Use `hs.of_mul_right_left.mul_left (IsCoprime.mul_left ?_ (IsCoprime.mul_left ?_ ?_))` and prove the remaining obligations. Conclude with `Ideal.isCoprime_iff_exists.2 ⟨b, Ideal.mem_span_singleton_self b, a, ha, (add_comm _ _).trans hab⟩`. Take `⟨p, q, hpq⟩ : IsCoprime (N : ℤ) (M : ℤ)` from `Nat.isCoprime_iff_coprime.2 hN`. Use `Ideal.isCoprime_iff_exists.2 ⟨p * N, Ideal.mem_span_singleton'.2 ⟨_, rfl⟩, q * M, Ideal.mul_mem_left _ _ hM, ?_⟩` and prove the remaining obligations.

Conclude with `congrArg (Int.cast : ℤ → 𝓞 E) hpq` after adjusting the coercions. Use `coprime_cc ht ?_` and prove the remaining obligations. Rewrite using `[← Ideal.span_singleton_mul_span_singleton]`. Conclude with `hs'.of_mul_right_right.mul_left hs.of_mul_right_right`. Rewrite using `[mul_smul, mul_smul]`.

Conclude with `smul_mem_smul hs1 (h3 b hb)`.
-/
theorem cong_of_pair (D : Level X) {M : ℕ} (hM : (M : 𝓞 E) ∈ D.𝔪) {L L' : Lt E r}
    (hL : L ∈ D.lats) (hL' : L' ∈ D.lats) (hS : SelfD X (D.sh L)) {Λ : Lt E n}
    (hΛ : Λ ∈ Vset E n M) {y y' : Matrix (Fin n) (Fin r) E}
    (h : ∀ δ ∈ tens Λ (D.sh L), δ ∈ tens Λ (D.sh L') →
      ∃ k : ℤ, ∑ i, EF X (δ i) ((y - y') i) = k) (k : Fin n) : Cong X D.𝔪 (y k) (y' k) := by
  obtain ⟨-, s, hs, hs1, -⟩ := hL
  obtain ⟨-, s', hs', -, hs2⟩ := hL'
  obtain ⟨N, -, hN, -, hN2⟩ := hΛ.2.2
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 D.cop
  let t : 𝓞 E := ⟨cc ((s' * s : 𝓞 E) : E), Base.isIntegral_cc (s' * s).isIntegral_coe⟩
  have ht : (t : E) = cc ((s' * s : 𝓞 E) : E) := rfl
  have h1 : ∀ v ∈ D.sh L, (s' * s) • v ∈ D.sh L' := fun v hv c hc => by
    rw [smul_comm]
    exact smul_mem_smul (fun u hu => by rw [mul_smul]; exact hs2 _ (hs1 u hu)) (hv c hc)
  have hctr : ∀ (c : E) (d : Matrix (Fin n) (Fin r) E) (v : Fin n → E),
      TensLat.ctr (c • d) v = c • TensLat.ctr d v := fun c d v => by
    funext j
    simp [TensLat.ctr, Finset.sum_apply, Finset.mul_sum, mul_left_comm]
  have h2 : (t : E) • (y - y') ∈ tens Λ (D.sh L) := by
    refine (TensLat.tens_selfDual hΛ hS _).2 fun δ hδ => ?_
    obtain ⟨m, hm⟩ := h (((s' * s : 𝓞 E) : E) • δ)
      (TensLat.smul_mem_tens hΛ (s' * s).isIntegral_coe hδ) (by
        rw [TensLat.mem_tens_iff hΛ] at hδ ⊢
        intro v hv
        rw [hctr]
        exact h1 _ (hδ v hv))
    refine ⟨-m, ?_⟩
    rw [Int.cast_neg, ← hm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensLat.EF_swap]
    exact congrArg Neg.neg (TensLat.EF_smul X _ _ _).symm
  have h3 := (TensLat.mem_tens_iff hΛ _ _).1 h2 _
    (hN2 (Pi.single k 1) (Submodule.subset_span ⟨k, rfl⟩))
  have h4 : TensLat.ctr ((t : E) • (y - y')) ((N : E) • (Pi.single k 1 : Fin n → E)) =
      ((N : 𝓞 E) * t) • (y k - y' k) := by
    rw [TensLat.ctr, Finset.sum_eq_single k]
    · funext j
      change _ = (((N : 𝓞 E) * t : 𝓞 E) : E) * (y k j - y' k j)
      simp [cc, mul_assoc, Algebra.smul_def]
    · intro j _ hj; simp [hj, cc]
    · simp
  rw [h4] at h3
  refine ⟨s * (b * (N * t)), ?_, ?_⟩
  · simp only [← Ideal.span_singleton_mul_span_singleton]
    refine hs.of_mul_right_left.mul_left (IsCoprime.mul_left ?_ (IsCoprime.mul_left ?_ ?_))
    · exact Ideal.isCoprime_iff_exists.2 ⟨b, Ideal.mem_span_singleton_self b, a, ha,
        (add_comm _ _).trans hab⟩
    · obtain ⟨p, q, hpq⟩ : IsCoprime (N : ℤ) (M : ℤ) := Nat.isCoprime_iff_coprime.2 hN
      refine Ideal.isCoprime_iff_exists.2 ⟨p * N, Ideal.mem_span_singleton'.2 ⟨_, rfl⟩, q * M,
        Ideal.mul_mem_left _ _ hM, ?_⟩
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hpq
    · refine coprime_cc ht ?_
      rw [← Ideal.span_singleton_mul_span_singleton]
      exact hs'.of_mul_right_right.mul_left hs.of_mul_right_right
  · rw [mul_smul, mul_smul]
    exact smul_mem_smul hs1 (h3 b hb)

/- English proof (translation)
Establish `hm : (0 : ℝ) ≤ m` using `Nat.cast_nonneg _`. Rewrite using `[← pow_left_inj₀ ha (Real.rpow_nonneg hm _) two_ne_zero, ← Real.rpow_natCast (_ ^ _), ← Real.rpow_mul hm, show -(n : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(n : ℝ) by push_cast; ring, Real.rpow_neg hm, Real.rpow_natCast]`. Conclude with `eq_inv_of_mul_eq_one_right (by exact_mod_cast h)`.
-/
theorem eq_rpow {a : ℝ} {m n : ℕ} (ha : 0 ≤ a) (h : ((m ^ n : ℕ) : ℝ) * a ^ 2 = 1) :
    a = (m : ℝ) ^ (-(n : ℝ) / 2) := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  rw [← pow_left_inj₀ ha (Real.rpow_nonneg hm _) two_ne_zero, ← Real.rpow_natCast (_ ^ _),
    ← Real.rpow_mul hm, show -(n : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(n : ℝ) by push_cast; ring,
    Real.rpow_neg hm, Real.rpow_natCast]
  exact eq_inv_of_mul_eq_one_right (by exact_mod_cast h)

/- English proof (translation)
Introduce `E _ _ _ r X g bas idx n hs hev D hn M hM0 hM v₀ hv₀ L hL Λ hΛ`. Establish `H` using `(heisG_laws E r X g bas idx n hs hev).2.2.2`. Establish `P` using `GlobalTheory.T.levelTestFunction_finite_sum_equivariant E r X g bas idx n hs hev D hn M hM0 hM v₀ hv₀`. Establish `Lv` using `(GlobalTheory.T.level_structure_properties E r X g bas idx n hs hev D hn).2.2.2.1`. Establish `hv` using `(P L hL Λ hΛ).2.1`.

Establish `main : ∀ L' ∈ D.lats, SW.ip (D.phi bas hn v₀ L Λ) (D.phi bas hn v₀ L' Λ) = (Nat.card D.J : ℂ) * SW.ip (unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L))) (unitv (projA X bas D.w (tens Λ (D.sh L')) (v₀ L')))`. Introduce `L' hL'`. Establish `hv'` using `(P L' hL' Λ hΛ).2.1`. Take `⟨s, hcard, hsy, e, e'⟩` from `(P L hL Λ hΛ).2.2.1 L' hL'`. Rewrite using `[e, e', ip_sum_diag s _ _ (fun y _ => TensVac.sb_smul _ (H y _ hv.1).1) (fun y _ => TensVac.sb_smul _ (H y _ hv'.1).1), ← hcard, ← nsmul_eq_mul, ← Finset.sum_const]`.

Use `Finset.sum_congr rfl fun y hy => ?_` and prove the remaining obligations. Rewrite using `[TensVac.ip_smul_left _ (H y _ hv.1).1 (TensVac.sb_smul _ (H y _ hv'.1).1), TensVac.ip_smul_right _ (H y _ hv.1).1 (H y _ hv'.1).1, ← mul_assoc, Complex.mul_conj', (hsy y hy).2.1, (H y _ hv.1).2.2.2.1 _ hv'.1]`. Simplify using the standard rewrite rules. Introduce `y hy y' hy' h0`. Rewrite `h0` using `[TensVac.ip_smul_left _ (H y _ hv.1).1 (TensVac.sb_smul _ (H y' _ hv'.1).1), TensVac.ip_smul_right _ (H y _ hv.1).1 (H y' _ hv'.1).1]`.

Use `(hsy y hy).2.2 y' hy' (cong_of_pair D hM hL hL' (Lv L hL).1 hΛ fun δ hδ hδ' => ?_)` and prove the remaining obligations. Conclude with `pair_int idx hs hev hv.1 hv'.1 (hv.2.2 δ hδ) (hv'.2.2 δ hδ') (right_ne_zero_of_mul (right_ne_zero_of_mul h0))`. Use `⟨by rw [main L hL, hv.2.1, mul_one], fun L' hL' => ?_⟩` and prove the remaining obligations. Establish `hv'` using `(P L' hL' Λ hΛ).2.1`. Establish `h1` using `(TensVac.vacua E r X g bas idx n hs hev D.w D.w_int D.w_tr _ (Lv L hL).1 M Λ hΛ).2.2.2 _ (Lv L' hL').1 Λ hΛ _ _ hv hv'`.

Rewrite `h1` using `[((TensLat.tens_selfDual_semichar_index E r X g bas idx n hs hev D.w D.w_int D.w_tr _ (Lv L hL).1 M Λ hΛ).2.2.2.2.1 _ (Lv L' hL').1).1, (Lv L hL).2.2.1 L' hL']`. Rewrite using `[main L' hL', norm_mul, Complex.norm_natCast]`. Use `mul_le_mul_of_nonneg_left (le_of_eq ?_) (Nat.cast_nonneg _)` and prove the remaining obligations. Conclude with `eq_rpow (norm_nonneg _) h1`.
-/
theorem phi_norm_overlap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : Level X) (hn : r ≤ n) (M : ℕ), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ L ∈ D.lats, ∀ Λ ∈ Vset E n M, SW.ip (D.phi bas hn v₀ L Λ) (D.phi bas hn v₀ L Λ) = (Nat.card D.J : ℂ) ∧ ∀ L' ∈ D.lats, ‖SW.ip (D.phi bas hn v₀ L Λ) (D.phi bas hn v₀ L' Λ)‖ ≤ (Nat.card D.J : ℝ) * (L'.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ^ (-(n : ℝ) / 2) := by
  intro E _ _ _ r X g bas idx n hs hev D hn M hM0 hM v₀ hv₀ L hL Λ hΛ
  have H := (heisG_laws E r X g bas idx n hs hev).2.2.2
  have P := GlobalTheory.T.levelTestFunction_finite_sum_equivariant E r X g bas idx n hs hev D hn M hM0 hM v₀ hv₀
  have Lv := (GlobalTheory.T.level_structure_properties E r X g bas idx n hs hev D hn).2.2.2.1
  have hv := (P L hL Λ hΛ).2.1
  have main : ∀ L' ∈ D.lats, SW.ip (D.phi bas hn v₀ L Λ) (D.phi bas hn v₀ L' Λ) =
      (Nat.card D.J : ℂ) * SW.ip (unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L)))
        (unitv (projA X bas D.w (tens Λ (D.sh L')) (v₀ L'))) := by
    intro L' hL'
    have hv' := (P L' hL' Λ hΛ).2.1
    obtain ⟨s, hcard, hsy, e, e'⟩ := (P L hL Λ hΛ).2.2.1 L' hL'
    rw [e, e', ip_sum_diag s _ _ (fun y _ => TensVac.sb_smul _ (H y _ hv.1).1)
      (fun y _ => TensVac.sb_smul _ (H y _ hv'.1).1), ← hcard, ← nsmul_eq_mul,
      ← Finset.sum_const]
    · refine Finset.sum_congr rfl fun y hy => ?_
      rw [TensVac.ip_smul_left _ (H y _ hv.1).1 (TensVac.sb_smul _ (H y _ hv'.1).1),
        TensVac.ip_smul_right _ (H y _ hv.1).1 (H y _ hv'.1).1, ← mul_assoc, Complex.mul_conj',
        (hsy y hy).2.1, (H y _ hv.1).2.2.2.1 _ hv'.1]
      simp
    · intro y hy y' hy' h0
      rw [TensVac.ip_smul_left _ (H y _ hv.1).1 (TensVac.sb_smul _ (H y' _ hv'.1).1),
        TensVac.ip_smul_right _ (H y _ hv.1).1 (H y' _ hv'.1).1] at h0
      refine (hsy y hy).2.2 y' hy' (cong_of_pair D hM hL hL' (Lv L hL).1 hΛ fun δ hδ hδ' => ?_)
      exact pair_int idx hs hev hv.1 hv'.1 (hv.2.2 δ hδ) (hv'.2.2 δ hδ')
        (right_ne_zero_of_mul (right_ne_zero_of_mul h0))
  refine ⟨by rw [main L hL, hv.2.1, mul_one], fun L' hL' => ?_⟩
  have hv' := (P L' hL' Λ hΛ).2.1
  have h1 := (TensVac.vacua E r X g bas idx n hs hev D.w D.w_int D.w_tr _ (Lv L hL).1 M Λ
    hΛ).2.2.2 _ (Lv L' hL').1 Λ hΛ _ _ hv hv'
  rw [((TensLat.tens_selfDual_semichar_index E r X g bas idx n hs hev D.w D.w_int D.w_tr _
    (Lv L hL).1 M Λ hΛ).2.2.2.2.1 _ (Lv L' hL').1).1, (Lv L hL).2.2.1 L' hL'] at h1
  rw [main L' hL', norm_mul, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (Nat.cast_nonneg _)
  exact eq_rpow (norm_nonneg _) h1

end GlobalTheory.SW.PhiNorm
