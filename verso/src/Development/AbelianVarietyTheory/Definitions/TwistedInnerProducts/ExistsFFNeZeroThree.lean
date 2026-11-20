import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HasConductorMulShift
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField

open ValuativeRel Matrix IsLocalRing
open scoped Pointwise

noncomputable section
namespace GlobalTheory.LatPair.Model

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun P => P.fn_ne (LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero])⟩`.
-/
theorem isEmpty_pair [IsEmpty n] : IsEmpty (Pair k n) :=
  ⟨fun P => P.fn_ne (LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero])⟩

/- English proof (translation)
Introduce `φ φ' h h'`. Unfold `cntIp`. Rewrite using `[finsum_eq_sum_of_support_subset (s := h'.toFinset) _ (fun P hP => by`. Simplify using `only [Function.mem_support, ne_eq, mul_eq_zero, not_or, map_eq_zero] at hP`. Simplify using `using hP.2),`.

Use `finsum_eq_sum_of_support_subset (s := h.toFinset) _ (fun P hP => by`. Simplify using `only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hP`. Simplify using `using hP.1)]`. Establish `e1 : ∀ P, sumOp S w φ P = ∑ Q ∈ h.toFinset, if Q ∈ S P then w P Q * φ Q else 0` using `fun P => by`. Rewrite using `[sumOp_apply, ← Finset.sum_filter]`.

Use `(Finset.sum_subset (fun Q hQ => (Finset.mem_filter.1 hQ).2) fun Q hQ hQ' => ?_).symm` and prove the remaining obligations. Establish `: φ Q = 0` using `by simpa [hQ] using hQ'`. Simplify using `[this]`. Establish `e2 : ∀ Q, sumOp S' w' φ' Q = ∑ P ∈ h'.toFinset, if P ∈ S' Q then w' Q P * φ' P else 0` using `fun P => by`. Rewrite using `[sumOp_apply, ← Finset.sum_filter]`.

Use `(Finset.sum_subset (fun Q hQ => (Finset.mem_filter.1 hQ).2) fun Q hQ hQ' => ?_).symm` and prove the remaining obligations. Establish `: φ' Q = 0` using `by simpa [hQ] using hQ'`. Simplify using `[this]`. Simplify using `only [e1, e2, Finset.sum_mul, map_sum, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun Q _ => Finset.sum_congr rfl fun P _ => ?_` and prove the remaining obligations. Distinguish the cases in `hQ : Q ∈ S P`. Rewrite using `[if_pos hQ, if_pos ((hS P Q).1 hQ), hw P Q hQ, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hQ, if_neg (fun h => hQ ((hS P Q).2 h))]`.

Simplify using the standard rewrite rules.
-/
theorem isAdj_sumOp (S S' : Pair k n → Finset (Pair k n)) (w w' : Pair k n → Pair k n → ℂ)
    (hS : ∀ P Q, Q ∈ S P ↔ P ∈ S' Q) (hw : ∀ P Q, Q ∈ S P → w P Q = (starRingEnd ℂ) (w' Q P)) :
    IsAdj (sumOp S w) (sumOp S' w') := by
  classical
  intro φ φ' h h'
  unfold cntIp
  rw [finsum_eq_sum_of_support_subset (s := h'.toFinset) _ (fun P hP => by
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or, map_eq_zero] at hP
      simpa using hP.2),
    finsum_eq_sum_of_support_subset (s := h.toFinset) _ (fun P hP => by
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hP
      simpa using hP.1)]
  have e1 : ∀ P, sumOp S w φ P = ∑ Q ∈ h.toFinset, if Q ∈ S P then w P Q * φ Q else 0 := fun P => by
    rw [sumOp_apply, ← Finset.sum_filter]
    refine (Finset.sum_subset (fun Q hQ => (Finset.mem_filter.1 hQ).2) fun Q hQ hQ' => ?_).symm
    have : φ Q = 0 := by simpa [hQ] using hQ'
    simp [this]
  have e2 : ∀ Q, sumOp S' w' φ' Q = ∑ P ∈ h'.toFinset, if P ∈ S' Q then w' Q P * φ' P else 0 := fun P => by
    rw [sumOp_apply, ← Finset.sum_filter]
    refine (Finset.sum_subset (fun Q hQ => (Finset.mem_filter.1 hQ).2) fun Q hQ hQ' => ?_).symm
    have : φ' Q = 0 := by simpa [hQ] using hQ'
    simp [this]
  simp only [e1, e2, Finset.sum_mul, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Q _ => Finset.sum_congr rfl fun P _ => ?_
  by_cases hQ : Q ∈ S P
  · rw [if_pos hQ, if_pos ((hS P Q).1 hQ), hw P Q hQ, map_mul]
    ring
  · rw [if_neg hQ, if_neg (fun h => hQ ((hS P Q).2 h))]
    simp

/- English proof (translation)
The claim follows from `isAdj_sumOp _ _ _ _ (fun P Q => by simp [eq_comm]) fun P Q _ => by rw [conj_resChar, neg_neg]`.
-/
theorem isAdj_FF {ψ : AddChar k Circle} (hψ : SplitWeil.HasConductor ψ 1) (q : Unif k) :
    IsAdj (FF q (resChar ψ hψ q) : Module.End ℂ (Form k n ℂ)) (FFStar q (resChar ψ hψ q)) :=
  isAdj_sumOp _ _ _ _ (fun P Q => by simp [eq_comm]) fun P Q _ => by rw [conj_resChar, neg_neg]

/- English proof (translation)
The claim follows from `isAdj_sumOp _ _ _ _ (fun P Q => by simp [eq_comm]) fun P Q _ => by simp`.
-/
theorem isAdj_U (q : Unif k) : IsAdj (U q : Module.End ℂ (Form k n ℂ)) (D q) :=
  isAdj_sumOp _ _ _ _ (fun P Q => by simp [eq_comm]) fun P Q _ => by simp

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/- English proof (translation)
The claim follows from `Finset.sum_equiv (MulAction.toPerm c) (fun P => by simp) fun _ _ => rfl`.
-/
theorem sum_withLat_dia {A : Type*} [AddCommMonoid A] (c : 𝓀[k]ˣ) (L : Submodule 𝒪[k] (n → k)) (F : Pair k n → A) :
    ∑ P ∈ withLat L, F (c • P) = ∑ P ∈ withLat L, F P :=
  Finset.sum_equiv (MulAction.toPerm c) (fun P => by simp) fun _ _ => rfl

/- English proof (translation)
Use extensionality with `P₁`. Simplify using `only [FF_apply, dia_apply, Pair.dia_ker]`. Rewrite using `[← sum_withLat_dia c _ fun P => χ (cross q (c • P₁) P) • φ P]`. Use `Finset.sum_congr rfl fun P hP => ?_` and prove the remaining obligations. Establish `h` using `mem_withLat.1 hP`.

Rewrite using `[cross_dia_left q (P := c • P) h, cross_dia_right q h, Units.inv_mul_cancel_left]`.
-/
theorem FF_dia (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (c : 𝓀[k]ˣ) (φ : Form k n M) :
    FF q χ (dia c φ) = dia c (FF q χ φ) := by
  ext P₁
  simp only [FF_apply, dia_apply, Pair.dia_ker]
  rw [← sum_withLat_dia c _ fun P => χ (cross q (c • P₁) P) • φ P]
  refine Finset.sum_congr rfl fun P hP => ?_
  have h := mem_withLat.1 hP
  rw [cross_dia_left q (P := c • P) h, cross_dia_right q h, Units.inv_mul_cancel_left]

/- English proof (translation)
Use `split_ifs with hg`. Simplify using `[hg]`. Use `(AddChar.sum_eq_zero_iff_ne_zero (ψ := χ.compAddMonoidHom g.toAddMonoidHom)).2 fun h => hχ ?_` and prove the remaining obligations. Use extensionality with `a`. Take `⟨x, rfl⟩` from `LinearMap.surjective hg a`.

Conclude with `DFunLike.congr_fun h x`.
-/
theorem sum_char {V : Type*} [AddCommGroup V] [Module 𝓀[k] V] [Fintype V] {χ : AddChar 𝓀[k] ℂ} (hχ : χ ≠ 1)
    (g : Module.Dual 𝓀[k] V) [Decidable (g = 0)] : ∑ x, χ (g x) = if g = 0 then (Fintype.card V : ℂ) else 0 := by
  split_ifs with hg
  · simp [hg]
  · refine (AddChar.sum_eq_zero_iff_ne_zero (ψ := χ.compAddMonoidHom g.toAddMonoidHom)).2 fun h => hχ ?_
    ext a
    obtain ⟨x, rfl⟩ := LinearMap.surjective hg a
    exact DFunLike.congr_fun h x

/- English proof (translation)
Use extensionality with `P`. Take `⟨L, hL, f, rfl⟩ : ∃ (L : Submodule 𝒪[k] (n → k)) (_ : L.IsLattice k) (f : _), P = ofDual L f` from `⟨P.lat, P.isLat, _, P.ofDual_red.symm⟩`. Use `letI := Fintype.ofFinite (Red L)`. Use `letI := Fintype.ofFinite (Module.Dual 𝓀[k] (Red L))`. Establish `hc : (Fintype.card (Red L) : ℂ) = SplitWeil.resCard k ^ Fintype.card n`.

Rewrite using `[← Nat.card_eq_fintype_card, Red.card_eq]`. Use `push_cast`. Both sides reduce to the same expression. Simplify using `only [FFStar_ofDual, FF_up, Finset.smul_sum, smul_smul, Pi.sub_apply, Pi.smul_apply, tr_apply, ofDual_lat, sum_withLat]`. Rewrite using `[Finset.sum_comm]`.

Establish `key : ∀ g : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}, ∑ x : {x : Red L // x ≠ 0}, χ (-f.1 x.1) * χ (g.1 x.1) = (if g = f then (Fintype.card (Red L) : ℂ) else 0) - 1` using `fun g => by`. Establish `h1` using `sum_char hχ (g.1 - f.1)`. Rewrite `h1` using `[Fintype.sum_eq_add_sum_subtype_ne _ 0]`. Simplify using `only [map_zero, AddChar.map_zero_eq_one, sub_eq_zero, Subtype.val_inj] at h1`. Rewrite using `[← h1, add_sub_cancel_left]`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[← AddChar.map_add_eq_mul, LinearMap.sub_apply, neg_add_eq_sub]`. Simplify using `only [← Finset.sum_smul, key, sub_smul, one_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, hc]`.
-/
theorem FFStar_FF [Fintype n] (q : Unif k) {χ : AddChar 𝓀[k] ℂ} (hχ : χ ≠ 1) (φ : Form k n M) :
    FFStar q χ (FF q χ φ) = (SplitWeil.resCard k ^ Fintype.card n : ℂ) • φ - tr φ := by
  classical
  ext P
  obtain ⟨L, hL, f, rfl⟩ : ∃ (L : Submodule 𝒪[k] (n → k)) (_ : L.IsLattice k) (f : _), P = ofDual L f :=
    ⟨P.lat, P.isLat, _, P.ofDual_red.symm⟩
  letI := Fintype.ofFinite (Red L)
  letI := Fintype.ofFinite (Module.Dual 𝓀[k] (Red L))
  have hc : (Fintype.card (Red L) : ℂ) = SplitWeil.resCard k ^ Fintype.card n := by
    rw [← Nat.card_eq_fintype_card, Red.card_eq]; push_cast; rfl
  simp only [FFStar_ofDual, FF_up, Finset.smul_sum, smul_smul, Pi.sub_apply, Pi.smul_apply, tr_apply, ofDual_lat,
    sum_withLat]
  rw [Finset.sum_comm]
  have key : ∀ g : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0},
      ∑ x : {x : Red L // x ≠ 0}, χ (-f.1 x.1) * χ (g.1 x.1) =
        (if g = f then (Fintype.card (Red L) : ℂ) else 0) - 1 := fun g => by
    have h1 := sum_char hχ (g.1 - f.1)
    rw [Fintype.sum_eq_add_sum_subtype_ne _ 0] at h1
    simp only [map_zero, AddChar.map_zero_eq_one, sub_eq_zero, Subtype.val_inj] at h1
    rw [← h1, add_sub_cancel_left]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← AddChar.map_add_eq_mul, LinearMap.sub_apply, neg_add_eq_sub]
  simp only [← Finset.sum_smul, key, sub_smul, one_smul, Finset.sum_sub_distrib, ite_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, hc]

/- English proof (translation)
Use `letI := Fintype.ofFinite 𝓀[k]ˣ`. Establish `h1 : ∑ P ∈ s, ∑ c : 𝓀[k]ˣ, φ (c • P) = 0` using `Finset.sum_eq_zero fun P _ => (mem_Mram φ).1 h P`. Rewrite `h1` using `[Finset.sum_comm]`. Establish `h2 : ∀ c : 𝓀[k]ˣ, ∑ P ∈ s, φ (c • P) = ∑ P ∈ s, φ P` using `fun c => Finset.sum_equiv (MulAction.toPerm c) (fun P => (hs c P).symm) fun _ _ => rfl`. Simplify using `only [h2, Finset.sum_const, Finset.card_univ] at h1`.

Rewrite `h1` using `[← Nat.cast_smul_eq_nsmul ℂ]`. Conclude with `(smul_eq_zero.1 h1).resolve_left (by exact_mod_cast Fintype.card_ne_zero)`.
-/
theorem sum_stable_eq_zero {φ : Form k n M} (h : φ ∈ Mram k n M) (s : Finset (Pair k n))
    (hs : ∀ (c : 𝓀[k]ˣ) P, c • P ∈ s ↔ P ∈ s) : ∑ P ∈ s, φ P = 0 := by
  letI := Fintype.ofFinite 𝓀[k]ˣ
  have h1 : ∑ P ∈ s, ∑ c : 𝓀[k]ˣ, φ (c • P) = 0 := Finset.sum_eq_zero fun P _ => (mem_Mram φ).1 h P
  rw [Finset.sum_comm] at h1
  have h2 : ∀ c : 𝓀[k]ˣ, ∑ P ∈ s, φ (c • P) = ∑ P ∈ s, φ P := fun c =>
    Finset.sum_equiv (MulAction.toPerm c) (fun P => (hs c P).symm) fun _ _ => rfl
  simp only [h2, Finset.sum_const, Finset.card_univ] at h1
  rw [← Nat.cast_smul_eq_nsmul ℂ] at h1
  exact (smul_eq_zero.1 h1).resolve_left (by exact_mod_cast Fintype.card_ne_zero)

/- English proof (translation)
Assemble the required witnesses or components as `⟨funext fun P => (tr_apply φ P).trans (sum_stable_eq_zero h _ (by simp)), funext fun P => (tr'_apply φ P).trans (sum_stable_eq_zero h _ (by simp))⟩`.
-/
theorem tr_eq_zero {φ : Form k n M} (h : φ ∈ Mram k n M) : tr φ = 0 ∧ tr' φ = 0 :=
  ⟨funext fun P => (tr_apply φ P).trans (sum_stable_eq_zero h _ (by simp)),
    funext fun P => (tr'_apply φ P).trans (sum_stable_eq_zero h _ (by simp))⟩

/- English proof (translation)
Use `letI := Fintype.ofFinite 𝓀[k]ˣ`. Use extensionality with `P₁`. Rewrite using `[FF_apply, D_apply, ← Finset.sum_filter_add_sum_filter_not _ (fun P => cross q P₁ P = 0)]`. Establish `h0 : ∑ P ∈ withLat P₁.ker with cross q P₁ P = 0, χ (cross q P₁ P) • φ P = 0`. Rewrite using `[Finset.sum_congr rfl (g := φ) fun P hP => by simp [(Finset.mem_filter.1 hP).2]]`.

Use `sum_stable_eq_zero h _ fun c P => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, mem_withLat, Pair.dia_lat]`. Conclude with `and_congr_right fun hP => by simp [cross_dia_right q hP]`. Rewrite using `[h0, zero_add]`. Simplify using `only [Gs_apply]`.

Rewrite using `[← Finset.sum_product']`. Use `symm`. Use `Finset.sum_bij (fun z _ => z.2 • z.1) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨P, c⟩ hz`. Simplify using `only [Finset.mem_product, Finset.mem_filter, mem_withLat, Finset.mem_univ, and_true] at hz`.

Simplify using `[hz.1, cross_dia_right q hz.1, hz.2]`. Introduce and unpack `⟨P, c⟩ hz ⟨P', c'⟩ hz' e`. Simplify using `only [Finset.mem_product, Finset.mem_filter, mem_withLat, Finset.mem_univ, and_true] at hz hz' e`. Use `congrArg (cross q P₁) e` as an intermediate fact. Rewrite `this` using `[cross_dia_right q hz.1, cross_dia_right q hz'.1, hz.2, hz'.2, mul_one, mul_one, Units.val_inj]`.

Substitute `this` using the available equality. Rewrite using `[MulAction.injective c e]`. Introduce `P hP`. Simplify using `only [Finset.mem_filter, mem_withLat] at hP`. Use `⟨((Units.mk0 _ hP.2)⁻¹ • P, Units.mk0 _ hP.2), ?_, smul_inv_smul _ _⟩` and prove the remaining obligations.

Simplify using `[hP.1, cross_dia_right q hP.1, hP.2]`. Introduce and unpack `⟨P, c⟩ hz`. Simplify using `only [Finset.mem_product, Finset.mem_filter, mem_withLat, Finset.mem_univ, and_true] at hz`. Simplify using `[cross_dia_right q hz.1, hz.2]`.
-/
theorem FF_eq_D_Gs (q : Unif k) (χ : AddChar 𝓀[k] ℂ) {φ : Form k n M} (h : φ ∈ Mram k n M) :
    FF q χ φ = D q (Gs χ φ) := by
  classical
  letI := Fintype.ofFinite 𝓀[k]ˣ
  ext P₁
  rw [FF_apply, D_apply, ← Finset.sum_filter_add_sum_filter_not _ (fun P => cross q P₁ P = 0)]
  have h0 : ∑ P ∈ withLat P₁.ker with cross q P₁ P = 0, χ (cross q P₁ P) • φ P = 0 := by
    rw [Finset.sum_congr rfl (g := φ) fun P hP => by simp [(Finset.mem_filter.1 hP).2]]
    refine sum_stable_eq_zero h _ fun c P => ?_
    simp only [Finset.mem_filter, mem_withLat, Pair.dia_lat]
    exact and_congr_right fun hP => by simp [cross_dia_right q hP]
  rw [h0, zero_add]
  simp only [Gs_apply]
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun z _ => z.2 • z.1) ?_ ?_ ?_ ?_
  · rintro ⟨P, c⟩ hz
    simp only [Finset.mem_product, Finset.mem_filter, mem_withLat, Finset.mem_univ, and_true] at hz
    simp [hz.1, cross_dia_right q hz.1, hz.2]
  · rintro ⟨P, c⟩ hz ⟨P', c'⟩ hz' e
    simp only [Finset.mem_product, Finset.mem_filter, mem_withLat, Finset.mem_univ, and_true] at hz hz' e
    have := congrArg (cross q P₁) e
    rw [cross_dia_right q hz.1, cross_dia_right q hz'.1, hz.2, hz'.2, mul_one, mul_one, Units.val_inj] at this
    subst this
    rw [MulAction.injective c e]
  · intro P hP
    simp only [Finset.mem_filter, mem_withLat] at hP
    refine ⟨((Units.mk0 _ hP.2)⁻¹ • P, Units.mk0 _ hP.2), ?_, smul_inv_smul _ _⟩
    simp [hP.1, cross_dia_right q hP.1, hP.2]
  · rintro ⟨P, c⟩ hz
    simp only [Finset.mem_product, Finset.mem_filter, mem_withLat, Finset.mem_univ, and_true] at hz
    simp [cross_dia_right q hz.1, hz.2]

/- English proof (translation)
Use `FFStar_FF q hχ φ` as an intermediate fact. Rewrite `this` using `[h0, map_zero, (tr_eq_zero h).1, sub_zero]`. Use `(smul_eq_zero.1 this.symm).resolve_left (pow_ne_zero _ ?_)` and prove the remaining obligations. Conclude with `(Nat.card_pos (α := 𝓀[k])).ne'` after adjusting the coercions.
-/
theorem FF_ne_zero [Fintype n] (q : Unif k) {χ : AddChar 𝓀[k] ℂ} (hχ : χ ≠ 1) {φ : Form k n M}
    (h : φ ∈ Mram k n M) (h0 : FF q χ φ = 0) : φ = 0 := by
  have := FFStar_FF q hχ φ
  rw [h0, map_zero, (tr_eq_zero h).1, sub_zero] at this
  refine (smul_eq_zero.1 this.symm).resolve_left (pow_ne_zero _ ?_)
  exact_mod_cast (Nat.card_pos (α := 𝓀[k])).ne'

/- English proof (translation)
Use `letI := Fintype.ofFinite 𝓀[k]ˣ`. Use `eq_bot_iff.2 fun φ h => funext fun P => ?_` and prove the remaining obligations. Use `(mem_Mram φ).1 h P` as an intermediate fact. Rewrite `this` using `[Fintype.sum_subsingleton _ 1, one_smul]`. Then use the resulting hypothesis.
-/
theorem Mram_eq_bot [Subsingleton 𝓀[k]ˣ] : Mram k n M = ⊥ := by
  letI := Fintype.ofFinite 𝓀[k]ˣ
  refine eq_bot_iff.2 fun φ h => funext fun P => ?_
  have := (mem_Mram φ).1 h P
  rwa [Fintype.sum_subsingleton _ 1, one_smul] at this

/- English proof (translation)
Use extensionality with `y`. Set `i₀ : Fin c` to `⟨p - 1, by omega⟩`. Establish `hi : ∀ i : Fin c, i.val + 1 = p ↔ i = i₀` using `fun i => by rw [Fin.ext_iff]; simp only [i₀]; omega`. Establish `h : (RootEx.colE c p (-((q.1 : k) • f)))⁻¹ • y = Sum.elim (y ∘ Sum.inl + ((q.1 : k) * y (Sum.inr i₀)) • f) (y ∘ Sum.inr)`. Express the relevant statement in the definitionally equal form `fromBlocks 1 (-Matrix.of fun r (i : Fin c) => if i.val + 1 = p then (-((q.1 : k) • f)) r else 0) 0 1 *ᵥ y = _`.

Rewrite using `[fromBlocks_mulVec]`. Simplify using `only [zero_mulVec, one_mulVec, zero_add]`. Use `congr 2`. Use extensionality with `r`. Simplify using `[mulVec, dotProduct, hi]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [mem_smul_iff, h, mem_gluedLat, Sum.elim_comp_inl, Sum.elim_inr, Function.comp_apply, smul_zero, sub_zero]`. Use `exists_congr fun s => and_congr_left fun H => ?_` and prove the remaining obligations. Use `(H i₀).2.1 ((hi _).2 rfl)` as an intermediate fact. Rewrite using `[this, Unif.inv, mul_inv_cancel_left₀ q.ne_zero]`.

Express the relevant statement in the definitionally equal form `y ∘ Sum.inl + s • f - s • f ∈ L ↔ _`. Rewrite using `[add_sub_cancel_right]`.
-/
theorem colE_smul_gluedLat [Fintype n] [DecidableEq n] (q : Unif k) {c p : ℕ} (h1 : 1 ≤ p) (hp : p ≤ c)
    (L : Submodule 𝒪[k] (n → k)) (f : n → k) :
    RootEx.colE c p (-((q.1 : k) • f)) • gluedLat q c p L f = gluedLat q c p L 0 := by
  ext y
  let i₀ : Fin c := ⟨p - 1, by omega⟩
  have hi : ∀ i : Fin c, i.val + 1 = p ↔ i = i₀ := fun i => by rw [Fin.ext_iff]; simp only [i₀]; omega
  have h : (RootEx.colE c p (-((q.1 : k) • f)))⁻¹ • y =
      Sum.elim (y ∘ Sum.inl + ((q.1 : k) * y (Sum.inr i₀)) • f) (y ∘ Sum.inr) := by
    change fromBlocks 1 (-Matrix.of fun r (i : Fin c) => if i.val + 1 = p then (-((q.1 : k) • f)) r else 0) 0 1 *ᵥ y = _
    rw [fromBlocks_mulVec]
    simp only [zero_mulVec, one_mulVec, zero_add]
    congr 2
    ext r
    simp [mulVec, dotProduct, hi]
    ring
  simp only [mem_smul_iff, h, mem_gluedLat, Sum.elim_comp_inl, Sum.elim_inr, Function.comp_apply, smul_zero, sub_zero]
  refine exists_congr fun s => and_congr_left fun H => ?_
  have := (H i₀).2.1 ((hi _).2 rfl)
  rw [this, Unif.inv, mul_inv_cancel_left₀ q.ne_zero]
  change y ∘ Sum.inl + s • f - s • f ∈ L ↔ _
  rw [add_sub_cancel_right]

/- English proof (translation)
Introduce `P Q h`. Establish `h' : gluedLat q c p P.ker P.vec = gluedLat q c p Q.ker Q.vec` using `h`. Establish `hk : P.ker = Q.ker`. Use extensionality with `x`. Rewrite using `[← inX_mem_gluedLat (q := q) h1 hp (f := P.vec), h', inX_mem_gluedLat h1 hp]`.

Establish `hm : q.inv • avec k n c p + inX k n c P.vec ∈ gluedLat q c p Q.ker Q.vec` using `h' ▸ Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))`. Take `⟨s, hs, H⟩` from `mem_gluedLat.1 hm`. Establish `h2` using `(H ⟨p - 1, by omega⟩).2.1 (by simp; omega)`. Establish `h3 : (s : k) = 1`. Establish `hq : q.inv ≠ 0` using `inv_ne_zero q.ne_zero`.

Simplify `h2.symm` using `[avec, inX, show p - 1 + 1 = p by omega, hq]`. Establish `h4 : s = 1` using `Subtype.ext h3`. Substitute `h4` using the available equality. Use `Pair.ext_ker hk P.hasVal_vec ((Pair.hasVal_one_iff Q.hasVal_vec).2 ?_)` and prove the remaining obligations. Use `hs using 2` and compare the differences between its conclusion and the goal.

Use extensionality with `j`. Simplify using `[avec, inX]`. Simplify using the standard rewrite rules.
-/
theorem glued_injective (q : Unif k) {c p : ℕ} (h1 : 1 ≤ p) (hp : p ≤ c) :
    Function.Injective fun P : Pair k n => P.glued q c p := by
  intro P Q h
  have h' : gluedLat q c p P.ker P.vec = gluedLat q c p Q.ker Q.vec := h
  have hk : P.ker = Q.ker := by
    ext x
    rw [← inX_mem_gluedLat (q := q) h1 hp (f := P.vec), h', inX_mem_gluedLat h1 hp]
  have hm : q.inv • avec k n c p + inX k n c P.vec ∈ gluedLat q c p Q.ker Q.vec := h' ▸ Submodule.mem_sup_left
    (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
  obtain ⟨s, hs, H⟩ := mem_gluedLat.1 hm
  have h2 := (H ⟨p - 1, by omega⟩).2.1 (by simp; omega)
  have h3 : (s : k) = 1 := by
    have hq : q.inv ≠ 0 := inv_ne_zero q.ne_zero
    simpa [avec, inX, show p - 1 + 1 = p by omega, hq] using h2.symm
  have h4 : s = 1 := Subtype.ext h3
  subst h4
  refine Pair.ext_ker hk P.hasVal_vec ((Pair.hasVal_one_iff Q.hasVal_vec).2 ?_)
  convert hs using 2
  · ext j; simp [avec, inX]
  · simp

/- English proof (translation)
The claim follows from `if_neg fun h => hc (by have h1 := maps_iff_hasVal.1 h _ _ P.hasVal_vec rw [one_mulVec, Pair.dia_hasVal] at h1 simpa using h1.unique P.hasVal_vec)`.
-/
theorem phiOne_one_dia [Fintype n] [DecidableEq n] (P : Pair k n) {c : 𝓀[k]ˣ} (hc : c ≠ 1) :
    phiOne P (c • P) 1 = 0 :=
  if_neg fun h => hc (by
    have h1 := maps_iff_hasVal.1 h _ _ P.hasVal_vec
    rw [one_mulVec, Pair.dia_hasVal] at h1
    simpa using h1.unique P.hasVal_vec)

/- English proof (translation)
Take `⟨q⟩ : Nonempty (Unif k)` from `inferInstance`. Take `⟨ψ, hψ⟩` from `SplitWeil.Model.exists_hasConductor (k := k)`. Take `⟨φ, h, h0⟩` from `(Submodule.ne_bot_iff _).1 (Mram_ne_bot (n := n) hc)`. Conclude with `⟨q, ψ, hψ, φ, h, fun e => h0 (FF_ne_zero q (resChar_ne_one hψ q) h e)⟩`.
-/
theorem exists_FF_ne_zero [Fintype n] [Nonempty n] {c : 𝓀[k]ˣ} (hc : c ≠ 1) :
    ∃ (q : Unif k) (ψ : AddChar k Circle) (hψ : SplitWeil.HasConductor ψ 1) (φ : Form k n ℂ),
      φ ∈ Mram k n ℂ ∧ FF q (resChar ψ hψ q) φ ≠ 0 := by
  obtain ⟨q⟩ : Nonempty (Unif k) := inferInstance
  obtain ⟨ψ, hψ⟩ := SplitWeil.Model.exists_hasConductor (k := k)
  obtain ⟨φ, h, h0⟩ := (Submodule.ne_bot_iff _).1 (Mram_ne_bot (n := n) hc)
  exact ⟨q, ψ, hψ, φ, h, fun e => h0 (FF_ne_zero q (resChar_ne_one hψ q) h e)⟩

instance factThree : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/- English proof (translation)
Use `letI := SplitWeil.Model.padic_localField 3`. Use `exists_FF_ne_zero (c := -1) fun h => ?_` and prove the remaining obligations. Establish `h1 : (-1 : 𝓀[ℚ_[3]]) = 1` using `by simpa using congrArg Units.val h`. Establish `h3 : residue 𝒪[ℚ_[3]] 3 = 0`. Rewrite using `[residue_eq_zero_iff, ← not_not (a := _ ∈ _), notMem_maximalIdeal]`.

Introduce `hu`. Take `⟨v, hv⟩` from `hu.exists_right_inv`. Establish `hv' : (3 : ℚ_[3]) * v = 1` using `congrArg Subtype.val hv`. Establish `hle : ¬ valuation ℚ_[3] 1 < valuation ℚ_[3] v`. Simplify using `using (Valuation.mem_integer_iff _ _).1 v.2`.

Rewrite `hle` using `[SplitWeil.Model.padic_lt]`. Establish `hn` using `congrArg norm hv'`. Establish `h3 : ‖(3 : ℚ_[3])‖ < 1` using `by simpa using Padic.norm_p_lt_one (p := 3)`. Rewrite `hn` using `[norm_mul, norm_one]`. Rewrite `hle` using `[norm_one, not_lt]`.

Use polynomial arithmetic with `[norm_nonneg (3 : ℚ_[3]), norm_nonneg (v : ℚ_[3])]`. Rewrite `h3` using `[map_ofNat]`. Conclude with `one_ne_zero (α := 𝓀[ℚ_[3]]) (by linear_combination h3 + h1)`.
-/
theorem exists_FF_ne_zero_three :
    letI := SplitWeil.Model.padic_localField 3
    ∃ (q : Unif ℚ_[3]) (ψ : AddChar ℚ_[3] Circle) (hψ : SplitWeil.HasConductor ψ 1) (φ : Form ℚ_[3] (Fin 2) ℂ),
      φ ∈ Mram ℚ_[3] (Fin 2) ℂ ∧ FF q (resChar ψ hψ q) φ ≠ 0 := by
  letI := SplitWeil.Model.padic_localField 3
  refine exists_FF_ne_zero (c := -1) fun h => ?_
  have h1 : (-1 : 𝓀[ℚ_[3]]) = 1 := by simpa using congrArg Units.val h
  have h3 : residue 𝒪[ℚ_[3]] 3 = 0 := by
    rw [residue_eq_zero_iff, ← not_not (a := _ ∈ _), notMem_maximalIdeal]
    intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    have hv' : (3 : ℚ_[3]) * v = 1 := congrArg Subtype.val hv
    have hle : ¬ valuation ℚ_[3] 1 < valuation ℚ_[3] v := by
      simpa using (Valuation.mem_integer_iff _ _).1 v.2
    rw [SplitWeil.Model.padic_lt] at hle
    have hn := congrArg norm hv'
    have h3 : ‖(3 : ℚ_[3])‖ < 1 := by simpa using Padic.norm_p_lt_one (p := 3)
    rw [norm_mul, norm_one] at hn
    rw [norm_one, not_lt] at hle
    nlinarith [norm_nonneg (3 : ℚ_[3]), norm_nonneg (v : ℚ_[3])]
  rw [map_ofNat] at h3
  exact one_ne_zero (α := 𝓀[ℚ_[3]]) (by linear_combination h3 + h1)

end GlobalTheory.LatPair.Model
