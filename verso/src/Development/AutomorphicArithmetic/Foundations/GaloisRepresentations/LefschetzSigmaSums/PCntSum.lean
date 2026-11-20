import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.SigmaSplit

open UpperTheory.Gal.LocalSmoothExtension

/- English proof (translation)
Introduce `Γ _ K K' M h hMK hKK' hnorm hconj _ Δ _ r hrK hr V _ _ P hP`. Establish `hPM : ∀ c ∈ K', ∀ u ∈ M, P (h * c * u) = P (h * c)`. Introduce `c hc u hu`. Establish `e` using `hP _ (hconj c hc u hu) c hc`. Rewrite using `[← e]`.

Use `congr 1`. Use `group`. Set `φ : (K' ⧸ K.subgroupOf K') × Δ → K' ⧸ M.subgroupOf K'` to `fun z => QuotientGroup.mk (Quotient.out z.1 * ⟨r z.2, hKK' (hrK z.2)⟩)`. Establish `hφ : Function.Bijective φ`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨a, x⟩ ⟨a', x'⟩ he`. Simplify using `only [φ, QuotientGroup.eq, Subgroup.mem_subgroupOf] at he`. Move the coercions through the operations in `at he`. Establish `hK : (↑(Quotient.out a) : Γ)⁻¹ * ↑(Quotient.out a') ∈ K`. Establish `e` using `K.mul_mem (K.mul_mem (hrK x) (hMK he)) (K.inv_mem (hrK x'))`.

Use `e using 1` and compare the differences between its conclusion and the goal. Use `group`. Establish `ha : a = a'`. Rewrite using `[← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' a', QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Use `push_cast`.

Conclude with `hK`. Substitute `ha` using the available equality. Establish `hx1 : r x' * (r x')⁻¹ ∈ M` using `by simpa using M.one_mem`. Establish `hx2 : r x' * (r x)⁻¹ ∈ M`. Establish `e` using `hnorm (r x) (hKK' (hrK x)) _ he`.

Use `e using 1` and compare the differences between its conclusion and the goal. Use `group`. Take `⟨x0, _, hu⟩` from `hr (r x') (hrK x')`. Rewrite using `[hu x hx2, hu x' hx1]`. Introduce `b`.

Take `⟨c, rfl⟩` from `QuotientGroup.mk_surjective b`. Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul (K.subgroupOf K') c`. Establish `hκ : (↑(Quotient.out (QuotientGroup.mk c : K' ⧸ K.subgroupOf K')) : Γ)⁻¹ * ↑c ∈ K`. Rewrite using `[hk]`. Use `push_cast`.

Establish `e` using `K.inv_mem (Subgroup.mem_subgroupOf.1 k.2)`. Use `e using 1` and compare the differences between its conclusion and the goal. Use `group`. Take `⟨x, hx, -⟩` from `hr _ hκ`. Use `⟨(QuotientGroup.mk c, x), ?_⟩` and prove the remaining obligations.

Simplify using `only [φ]`. Rewrite using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Use `push_cast`. Establish `e` using `hnorm (r x)⁻¹ (K'.inv_mem (hKK' (hrK x))) _ hx`. Use `e using 1` and compare the differences between its conclusion and the goal.

Use `group`. Use `haveI : Finite (K' ⧸ M.subgroupOf K') := Finite.of_surjective φ hφ.2`. Use `letI : Fintype (K' ⧸ M.subgroupOf K') := Fintype.ofFinite _`. Establish `hL : ∑ z : (K' ⧸ K.subgroupOf K') × Δ, P (h * ↑(Quotient.out z.1) * r z.2) = ∑ z : (K' ⧸ K.subgroupOf K') × Δ, P (h * ↑(Quotient.out (φ z)))`. Use `Finset.sum_congr rfl fun z _ => ?_` and prove the remaining obligations.

Take `⟨u, hu⟩` from `QuotientGroup.mk_out_eq_mul (M.subgroupOf K') (Quotient.out z.1 * ⟨r z.2, hKK' (hrK z.2)⟩)`. Simplify using `only [φ]`. Rewrite using `[hu]`. Use `push_cast`. Establish `hc : (↑(Quotient.out z.1) : Γ) * r z.2 ∈ K'` using `K'.mul_mem (Quotient.out z.1).2 (hKK' (hrK z.2))`.

Establish `e` using `hPM _ hc _ (Subgroup.mem_subgroupOf.1 u.2)`. Rewrite using `[mul_assoc h, ← e]`. Use `congr 1`. Use `group`. Set `g : K' ⧸ M.subgroupOf K' → Γ ⧸ K` to `fun b => QuotientGroup.mk (h * ↑(Quotient.out b))⁻¹`.

Establish `hcnt : ∀ y : Γ ⧸ K, cntFn K K' M h (Quotient.out y) = ((Finset.univ.filter (fun b => g b = y)).card : ℂ)`. Introduce `y`. Establish `hset : (Finset.univ.filter fun b : K' ⧸ M.subgroupOf K' => h * ↑(Quotient.out b) * Quotient.out y ∈ K) = Finset.univ.filter fun b => g b = y`. Use `Finset.filter_congr fun b _ => ?_` and prove the remaining obligations. Simplify using `only [g]`.

Use `conv_rhs => rw [← QuotientGroup.out_eq' y]`. Rewrite using `[QuotientGroup.eq, inv_inv]`. Unfold `cntFn`. Rewrite using `[Nat.card_eq_fintype_card, Fintype.card_subtype, hset]`. Establish `hsupp : (Function.support fun y : Γ ⧸ K => cntFn K K' M h (Quotient.out y) • P (Quotient.out y)⁻¹) ⊆ ↑(Finset.univ.image g)`.

Introduce `y hy`. Rewrite `hy` using `[Function.mem_support, hcnt]`. Assume the negation of the conclusion as `hyn`. Apply `hy` to reduce the goal to its premises. Establish `e : Finset.univ.filter (fun b => g b = y) = ∅`.

Rewrite using `[Finset.filter_eq_empty_iff]`. Introduce `b _ hb`. Conclude with `hyn (Finset.mem_coe.2 (Finset.mem_image.2 ⟨b, Finset.mem_univ _, hb⟩))`. Simplify using `[e]`. Establish `hR : ∑ y ∈ Finset.univ.image g, cntFn K K' M h (Quotient.out y) • P (Quotient.out y)⁻¹ = ∑ b, P (Quotient.out (g b))⁻¹`.

Rewrite using `[Finset.sum_comp (fun y => P (Quotient.out y)⁻¹) g]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[hcnt, Nat.cast_smul_eq_nsmul]`. Establish `hR4 : ∑ b, P (Quotient.out (g b))⁻¹ = ∑ b : K' ⧸ M.subgroupOf K', P (h * ↑(Quotient.out b))`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul K (h * ↑(Quotient.out b))⁻¹`. Simplify using `only [g]`. Rewrite using `[hk, show ((h * ↑(Quotient.out b))⁻¹ * (↑k : Γ))⁻¹ = (↑k)⁻¹ * (h * ↑(Quotient.out b)) by group]`. Conclude with `hP _ (K.inv_mem k.2) _ (Quotient.out b).2`. Rewrite using `[hL, Fintype.sum_bijective φ hφ (fun z => P (h * ↑(Quotient.out (φ z)))) (fun b => P (h * ↑(Quotient.out b))) (fun _ => rfl), finsum_eq_sum_of_support_subset _ hsupp, hR, hR4]`.
-/
theorem UpperTheory.Gal.LocalSmoothExtension.cntSum_of :
    CntSum := by
  classical
  intro Γ _ K K' M h hMK hKK' hnorm hconj _ Δ _ r hrK hr V _ _ P hP
  have hPM : ∀ c ∈ K', ∀ u ∈ M, P (h * c * u) = P (h * c) := by
    intro c hc u hu
    have e := hP _ (hconj c hc u hu) c hc
    rw [← e]
    congr 1
    group
  let φ : (K' ⧸ K.subgroupOf K') × Δ → K' ⧸ M.subgroupOf K' := fun z =>
    QuotientGroup.mk (Quotient.out z.1 * ⟨r z.2, hKK' (hrK z.2)⟩)
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨a, x⟩ ⟨a', x'⟩ he
      simp only [φ, QuotientGroup.eq, Subgroup.mem_subgroupOf] at he
      push_cast at he
      have hK : (↑(Quotient.out a) : Γ)⁻¹ * ↑(Quotient.out a') ∈ K := by
        have e := K.mul_mem (K.mul_mem (hrK x) (hMK he)) (K.inv_mem (hrK x'))
        convert e using 1
        group
      have ha : a = a' := by
        rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' a', QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        push_cast
        exact hK
      subst ha
      have hx1 : r x' * (r x')⁻¹ ∈ M := by simpa using M.one_mem
      have hx2 : r x' * (r x)⁻¹ ∈ M := by
        have e := hnorm (r x) (hKK' (hrK x)) _ he
        convert e using 1
        group
      obtain ⟨x0, _, hu⟩ := hr (r x') (hrK x')
      rw [hu x hx2, hu x' hx1]
    · intro b
      obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective b
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (K.subgroupOf K') c
      have hκ : (↑(Quotient.out (QuotientGroup.mk c : K' ⧸ K.subgroupOf K')) : Γ)⁻¹ * ↑c ∈ K := by
        rw [hk]
        push_cast
        have e := K.inv_mem (Subgroup.mem_subgroupOf.1 k.2)
        convert e using 1
        group
      obtain ⟨x, hx, -⟩ := hr _ hκ
      refine ⟨(QuotientGroup.mk c, x), ?_⟩
      simp only [φ]
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      push_cast
      have e := hnorm (r x)⁻¹ (K'.inv_mem (hKK' (hrK x))) _ hx
      convert e using 1
      group
  haveI : Finite (K' ⧸ M.subgroupOf K') := Finite.of_surjective φ hφ.2
  letI : Fintype (K' ⧸ M.subgroupOf K') := Fintype.ofFinite _
  have hL : ∑ z : (K' ⧸ K.subgroupOf K') × Δ, P (h * ↑(Quotient.out z.1) * r z.2)
      = ∑ z : (K' ⧸ K.subgroupOf K') × Δ, P (h * ↑(Quotient.out (φ z))) := by
    refine Finset.sum_congr rfl fun z _ => ?_
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (M.subgroupOf K')
      (Quotient.out z.1 * ⟨r z.2, hKK' (hrK z.2)⟩)
    simp only [φ]
    rw [hu]
    push_cast
    have hc : (↑(Quotient.out z.1) : Γ) * r z.2 ∈ K' :=
      K'.mul_mem (Quotient.out z.1).2 (hKK' (hrK z.2))
    have e := hPM _ hc _ (Subgroup.mem_subgroupOf.1 u.2)
    rw [mul_assoc h, ← e]
    congr 1
    group
  let g : K' ⧸ M.subgroupOf K' → Γ ⧸ K := fun b => QuotientGroup.mk (h * ↑(Quotient.out b))⁻¹
  have hcnt : ∀ y : Γ ⧸ K, cntFn K K' M h (Quotient.out y)
      = ((Finset.univ.filter (fun b => g b = y)).card : ℂ) := by
    intro y
    have hset : (Finset.univ.filter fun b : K' ⧸ M.subgroupOf K' =>
        h * ↑(Quotient.out b) * Quotient.out y ∈ K) = Finset.univ.filter fun b => g b = y := by
      refine Finset.filter_congr fun b _ => ?_
      simp only [g]
      conv_rhs => rw [← QuotientGroup.out_eq' y]
      rw [QuotientGroup.eq, inv_inv]
    unfold cntFn
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hset]
  have hsupp : (Function.support fun y : Γ ⧸ K =>
      cntFn K K' M h (Quotient.out y) • P (Quotient.out y)⁻¹) ⊆ ↑(Finset.univ.image g) := by
    intro y hy
    rw [Function.mem_support, hcnt] at hy
    by_contra hyn
    apply hy
    have e : Finset.univ.filter (fun b => g b = y) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro b _ hb
      exact hyn (Finset.mem_coe.2 (Finset.mem_image.2 ⟨b, Finset.mem_univ _, hb⟩))
    simp [e]
  have hR : ∑ y ∈ Finset.univ.image g, cntFn K K' M h (Quotient.out y) • P (Quotient.out y)⁻¹
      = ∑ b, P (Quotient.out (g b))⁻¹ := by
    rw [Finset.sum_comp (fun y => P (Quotient.out y)⁻¹) g]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hcnt, Nat.cast_smul_eq_nsmul]
  have hR4 : ∑ b, P (Quotient.out (g b))⁻¹ = ∑ b : K' ⧸ M.subgroupOf K', P (h * ↑(Quotient.out b)) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (h * ↑(Quotient.out b))⁻¹
    simp only [g]
    rw [hk, show ((h * ↑(Quotient.out b))⁻¹ * (↑k : Γ))⁻¹ = (↑k)⁻¹ * (h * ↑(Quotient.out b)) by group]
    exact hP _ (K.inv_mem k.2) _ (Quotient.out b).2
  rw [hL, Fintype.sum_bijective φ hφ (fun z => P (h * ↑(Quotient.out (φ z))))
    (fun b => P (h * ↑(Quotient.out b))) (fun _ => rfl), finsum_eq_sum_of_support_subset _ hsupp, hR, hR4]
