import Mathlib
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe

open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal

namespace GlobalTheory

/- English proof (translation)
Establish `hle : Ideal.span {a} ≤ J` using `by rw [h]; exact Ideal.mul_le_right`. Establish `hJ : J ≠ ⊥`. Introduce and unpack `rfl`. Rewrite `h` using `[Ideal.mul_bot, Ideal.span_singleton_eq_bot]`. Conclude with `ha h`.

Establish `hNJ : Ideal.absNorm J ≠ 0` using `fun h0 => hJ (Ideal.absNorm_eq_zero_iff.mp h0)`. Establish `key` using `AddSubgroup.relIndex_mul_index (H := (Ideal.span {a}).toAddSubgroup) (K := J.toAddSubgroup) hle`. Establish `e1 : J.toAddSubgroup.index = Ideal.absNorm J` using `rfl`. Establish `e2 : (Ideal.span {a}).toAddSubgroup.index = Ideal.absNorm I * Ideal.absNorm J`. Rewrite using `[← map_mul, ← h]`.

Both sides reduce to the same expression. Rewrite `key` using `[e1, e2]`. Conclude with `Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hNJ) key`.
-/
theorem xClasses_index {K : Type} [Field K] [NumberField K] (I J : Ideal (𝓞 K)) (a : 𝓞 K)
    (ha : a ≠ 0) (h : Ideal.span {a} = I * J) :
    ((Ideal.span {a}).toAddSubgroup.addSubgroupOf J.toAddSubgroup).index = Ideal.absNorm I := by
  have hle : Ideal.span {a} ≤ J := by rw [h]; exact Ideal.mul_le_right
  have hJ : J ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at h
    exact ha h
  have hNJ : Ideal.absNorm J ≠ 0 := fun h0 => hJ (Ideal.absNorm_eq_zero_iff.mp h0)
  have key := AddSubgroup.relIndex_mul_index
    (H := (Ideal.span {a}).toAddSubgroup) (K := J.toAddSubgroup) hle
  have e1 : J.toAddSubgroup.index = Ideal.absNorm J := rfl
  have e2 : (Ideal.span {a}).toAddSubgroup.index = Ideal.absNorm I * Ideal.absNorm J := by
    rw [← map_mul, ← h]; rfl
  rw [e1, e2] at key
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hNJ) key

/- English proof (translation)
Take `⟨o, ho⟩` from `hz a haI`. Establish `hmem : o ∈ J`. Establish `hle : Ideal.span {o} * I ≤ J * I`. Rewrite using `[Ideal.span_singleton_mul_le_iff]`. Introduce `α hα`.

Take `⟨p, hp⟩` from `hz α hα`. Establish `hop : o * α = a * p`. Apply `IsFractionRing.injective (𝓞 K) K` to reduce the goal to its premises. Simplify using `only [map_mul]`. Express the relevant statement in the definitionally equal form `(o : K) * (α : K) = (a : K) * (p : K)`.

Rewrite using `[ho, hp]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hop, mul_comm J I, ← h]`. Conclude with `Ideal.mul_mem_right p _ (Ideal.mem_span_singleton_self a)`. Establish `hdvd : J * I ∣ Ideal.span {o} * I` using `Ideal.dvd_iff_le.mpr hle`.

Rewrite `hdvd` using `[mul_dvd_mul_iff_right hI]`. Conclude with `Ideal.dvd_span_singleton.mp hdvd`. Conclude with `⟨⟨o, hmem⟩, ho⟩`.
-/
theorem xClasses_mem {K : Type} [Field K] [NumberField K] (I J : Ideal (𝓞 K)) (a : 𝓞 K)
    (hI : I ≠ ⊥) (haI : a ∈ I) (h : Ideal.span {a} = I * J) (z : K)
    (hz : ∀ α ∈ I, ∃ o : 𝓞 K, (o : K) = (α : K) * z) :
    ∃ o : J.toAddSubgroup, ((o : 𝓞 K) : K) = (a : K) * z := by
  obtain ⟨o, ho⟩ := hz a haI
  have hmem : o ∈ J := by
    have hle : Ideal.span {o} * I ≤ J * I := by
      rw [Ideal.span_singleton_mul_le_iff]
      intro α hα
      obtain ⟨p, hp⟩ := hz α hα
      have hop : o * α = a * p := by
        apply IsFractionRing.injective (𝓞 K) K
        simp only [map_mul]
        change (o : K) * (α : K) = (a : K) * (p : K)
        rw [ho, hp]; ring
      rw [hop, mul_comm J I, ← h]
      exact Ideal.mul_mem_right p _ (Ideal.mem_span_singleton_self a)
    have hdvd : J * I ∣ Ideal.span {o} * I := Ideal.dvd_iff_le.mpr hle
    rw [mul_dvd_mul_iff_right hI] at hdvd
    exact Ideal.dvd_span_singleton.mp hdvd
  exact ⟨⟨o, hmem⟩, ho⟩

/- English proof (translation)
Introduce `α hα`. Take `⟨β, hβ, rfl⟩` from `Ideal.mem_span_singleton_mul.mp hα`. Use `set φ := algebraMap (𝓞 K) K with hφ`. Use `set B := Y.submatrix id f with hB`. Establish `hM : B.map φ * (B.map φ).adjugate = (φ B.det) • (1 : Matrix (Fin r) (Fin r) K)`.

Rewrite using `[Matrix.mul_adjugate, RingHom.map_det]`. Both sides reduce to the same expression. Establish `e1 : ∀ k, (S * Y.map φ) i (f k) = (S * B.map φ) i k`. Introduce `k`. Simplify using `[Matrix.mul_apply, B]`.

Establish `e2 : ∀ k, φ (B.adjugate k j) = (B.map φ).adjugate k j`. Introduce `k`. Conclude with `congrFun (congrFun (RingHom.map_adjugate φ B) k) j`. Establish `hkey : ∑ k, (S * Y.map φ) i (f k) * φ (B.adjugate k j) = φ B.det * S i j`. Repeatedly rewrite using `[e1, e2]`.

Rewrite using `[← Matrix.mul_apply, Matrix.mul_assoc, hM]`. Simplify using `[Matrix.mul_apply, Matrix.one_apply, mul_comm]`. Use `choose g hg using fun k => hx i (f k) β hβ`. Use `⟨∑ k, g k * B.adjugate k j, ?_⟩` and prove the remaining obligations. Establish `hc : ∀ u : 𝓞 K, (u : K) = φ u` using `fun u => rfl`.

Simplify using `only [hc, map_sum, map_mul] at hg ⊢`. Repeatedly rewrite using `[hg]`. Rewrite using `[mul_comm (φ B.det) (φ β), mul_assoc, ← hkey, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem xClasses_denom {K : Type} [Field K] [NumberField K] (A : Ideal (𝓞 K)) {r : ℕ}
    (Y : Matrix (Fin r) (Fin (r + 1)) (𝓞 K)) (f : Fin r → Fin (r + 1))
    (S : Matrix (Fin r) (Fin r) K)
    (hx : ∀ a b, ∀ α ∈ A, ∃ o : 𝓞 K,
      (o : K) = (α : K) * (S * Y.map (algebraMap (𝓞 K) K)) a b) (i j : Fin r) :
    ∀ α ∈ Ideal.span {(Y.submatrix id f).det} * A, ∃ o : 𝓞 K, (o : K) = (α : K) * S i j := by
  classical
  intro α hα
  obtain ⟨β, hβ, rfl⟩ := Ideal.mem_span_singleton_mul.mp hα
  set φ := algebraMap (𝓞 K) K with hφ
  set B := Y.submatrix id f with hB
  have hM : B.map φ * (B.map φ).adjugate = (φ B.det) • (1 : Matrix (Fin r) (Fin r) K) := by
    rw [Matrix.mul_adjugate, RingHom.map_det]; rfl
  have e1 : ∀ k, (S * Y.map φ) i (f k) = (S * B.map φ) i k := by
    intro k; simp [Matrix.mul_apply, B]
  have e2 : ∀ k, φ (B.adjugate k j) = (B.map φ).adjugate k j := by
    intro k; exact congrFun (congrFun (RingHom.map_adjugate φ B) k) j
  have hkey : ∑ k, (S * Y.map φ) i (f k) * φ (B.adjugate k j) = φ B.det * S i j := by
    simp_rw [e1, e2]
    rw [← Matrix.mul_apply, Matrix.mul_assoc, hM]
    simp [Matrix.mul_apply, Matrix.one_apply, mul_comm]
  choose g hg using fun k => hx i (f k) β hβ
  refine ⟨∑ k, g k * B.adjugate k j, ?_⟩
  have hc : ∀ u : 𝓞 K, (u : K) = φ u := fun u => rfl
  simp only [hc, map_sum, map_mul] at hg ⊢
  simp_rw [hg]
  rw [mul_comm (φ B.det) (φ β), mul_assoc, ← hkey, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/- English proof (translation)
Introduce `K _ _ _ A r Y b₀ hA hdet`. Use `set f := b₀.succAbove with hf`. Use `set φ := algebraMap (𝓞 K) K with hφ`. Use `set D := (Y.submatrix id f).det with hD`. Use `set I := Ideal.span {D} * A with hI`.

Use `set YK := Y.map φ with hYK`. Establish `hφinj : Function.Injective φ` using `IsFractionRing.injective (𝓞 K) K`. Establish `hc : ∀ u : 𝓞 K, (u : K) = φ u` using `fun u => rfl`. Establish `hI0 : I ≠ ⊥`. Introduce `h0`.

Break down `mul_eq_zero.mp (show Ideal.span {D} * A = 0 from h0) with h1 | h1` into its components or cases. Conclude with `hdet (Ideal.span_singleton_eq_bot.mp h1)`. Conclude with `hA h1`. Take `⟨a, haI, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hI0`. Take `⟨J, hJ⟩ : I ∣ Ideal.span {a}` from `Ideal.dvd_span_singleton.mpr haI`.

Establish `haK : φ a ≠ 0` using `fun h0 => ha0 (hφinj (h0.trans (map_zero φ).symm))`. Set `C : Matrix (Fin (r + 1)) (Fin r) K` to `(1 : Matrix (Fin (r + 1)) (Fin (r + 1)) K).submatrix id f`. Establish `hC : ∀ M : Matrix (Fin r) (Fin (r + 1)) K, M * C = M.submatrix id f` using `fun M => by`. Simplify `Matrix.mul_submatrix_one (Equiv.refl (Fin (r + 1))) f M` using `[C]`. Establish `hYf : YK * C = (Y.submatrix id f).map φ`.

Rewrite using `[hC, hYK, Matrix.submatrix_map]`. Establish `hdetYf : IsUnit (YK * C).det`. Rewrite using `[hYf, show ((Y.submatrix id f).map φ).det = φ D from (RingHom.map_det φ _).symm]`. Conclude with `isUnit_iff_ne_zero.mpr (fun h0 => hdet (hφinj (h0.trans (map_zero φ).symm)))`. Establish `hdetYfH : IsUnit (YK * C)ᴴ.det`.

Rewrite using `[Matrix.det_conjTranspose]`. Conclude with `isUnit_iff_ne_zero.mpr (star_ne_zero.mpr (isUnit_iff_ne_zero.mp hdetYf))`. Take `⟨Good, hGood⟩ : ∃ G : Matrix (Fin r) (Fin (r + 1)) K → Prop, ∀ x, G x ↔ (∀ p q, ∀ α ∈ A, ∃ o : 𝓞 K, (o : K) = (α : K) * x p q) ∧ xᴴ * YK + YKᴴ * x = 0` from `⟨_, fun _ => Iff.rfl⟩`. Choose the witnesses or unpack the hypotheses as in `⟨Sx, hSx⟩ : ∃ Sx : Matrix (Fin r) (Fin (r + 1)) K → Matrix (Fin r) (Fin r) K, ∀ x, Good x → x = Sx x * YK ∧ (Sx x)ᴴ = -Sx x := by`. Use `⟨fun x => x * C * (YK * C)⁻¹, fun x hG => ?_⟩` and prove the remaining obligations.

Establish `hxY` using `((hGood x).mp hG).2`. Use `set Yf := YK * C with hYfdef`. Use `set S := x * C * Yf⁻¹ with hS`. Establish `hSYf : S * Yf = x * C` using `Matrix.nonsing_inv_mul_cancel_right _ _ hdetYf`. Use `set P := x - S * YK with hP`.

Establish `hxP : x = S * YK + P` using `by rw [hP]; abel`. Establish `hPC : P * C = 0`. Rewrite using `[hP, Matrix.sub_mul, Matrix.mul_assoc, ← hYfdef, hSYf, sub_self]`. Establish `h1 : Cᴴ * xᴴ = Yfᴴ * Sᴴ`. Rewrite using `[← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul, hSYf]`.

Establish `h2 : Cᴴ * YKᴴ = Yfᴴ` using `by rw [← Matrix.conjTranspose_mul]`. Establish `h3 : Yfᴴ * Sᴴ * YK + Yfᴴ * x = 0`. Establish `h0 : Cᴴ * (xᴴ * YK + YKᴴ * x) = 0` using `by rw [hxY, Matrix.mul_zero]`. Rewrite `h0` using `[Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, h2]`. Then use the resulting hypothesis. Establish `h4 : Yfᴴ * ((Sᴴ + S) * YK + P) = 0`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws. Use `_ = 0 := by rw [← hxP]; exact h3`. Establish `h5 : (Sᴴ + S) * YK + P = 0`.

Establish `h0` using `congrArg (fun M => Yfᴴ⁻¹ * M) h4`. Rewrite `h0` using `[Matrix.nonsing_inv_mul_cancel_left _ _ hdetYfH, Matrix.mul_zero]`. Then use the resulting hypothesis. Establish `h6 : Sᴴ + S = 0`. Establish `h0` using `congrArg (fun M => M * C * Yf⁻¹) h5`. Rewrite `h0` using `[Matrix.add_mul, hPC, add_zero, Matrix.mul_assoc ((Sᴴ + S)) YK C, ← hYfdef, Matrix.mul_nonsing_inv_cancel_right _ _ hdetYf, Matrix.zero_mul, Matrix.zero_mul]`. Then use the resulting hypothesis.

Establish `h7 : P = 0` using `by rwa [h6, Matrix.zero_mul, zero_add] at h5`. Rewrite `hxP` using `[h7, add_zero]`. Conclude with `⟨hxP, eq_neg_of_add_eq_zero_left h6⟩`. Establish `hent : ∀ x, Good x → ∀ i j, ∃ o : J.toAddSubgroup, ((o : 𝓞 K) : K) = (a : K) * Sx x i j`. Introduce `x hG i j`.

Establish `hx` using `((hGood x).mp hG).1`. Establish `h1` using `(hSx x hG).1`. Apply `xClasses_mem I J a hI0 haI hJ` to reduce the goal to its premises. Establish `hx' : ∀ p q, ∀ α ∈ A, ∃ o : 𝓞 K, (o : K) = (α : K) * (Sx x * Y.map φ) p q`. Introduce `p q α hα`.

Rewrite using `[← hYK, ← h1]`. Conclude with `hx p q α hα`. Conclude with `xClasses_denom A Y f (Sx x) hx' i j`. Use `set Q := ↥J.toAddSubgroup ⧸ (Ideal.span {a}).toAddSubgroup.addSubgroupOf J.toAddSubgroup`. Establish `hcardQ : Nat.card Q = Ideal.absNorm I` using `xClasses_index I J a ha0 hJ`.

Establish `: Finite Q` using `Nat.finite_of_card_ne_zero (by`. Rewrite using `[hcardQ]`. Conclude with `fun h0 => hI0 (Ideal.absNorm_eq_zero_iff.mp h0))`. Set `_ : Fintype Q` to `Fintype.ofFinite Q`. Choose the witnesses or unpack the hypotheses as in `⟨key, hkey⟩ : ∃ key : Matrix (Fin r) (Fin (r + 1)) K → (Fin r → Fin r → Q), ∀ x, Good x → ∀ i j, ∃ o : J.toAddSubgroup, ((o : 𝓞 K) : K) = (a : K) * Sx x i j ∧ key x i j = (o : Q) := by`.

Use `⟨fun x i j => if h : ∃ o : J.toAddSubgroup, ((o : 𝓞 K) : K) = (a : K) * Sx x i j then ((Classical.choose h : J.toAddSubgroup) : Q) else 0, fun x hG i j => ?_⟩` and prove the remaining obligations. Establish `h` using `hent x hG i j`. Conclude with `⟨Classical.choose h, Classical.choose_spec h, by simp only [dif_pos h]⟩`. Choose the witnesses or unpack the hypotheses as in `⟨g, hg⟩ : ∃ g : (Fin r → Fin r → Q) → Matrix (Fin r) (Fin (r + 1)) K, ∀ q, (∃ x, Good x ∧ key x = q) → Good (g q) ∧ key (g q) = q := by`. Use `⟨fun q => if h : ∃ x, Good x ∧ key x = q then Classical.choose h else 0, fun q h => ?_⟩` and prove the remaining obligations.

Simplify using `only [dif_pos h]`. Conclude with `Classical.choose_spec h`. Use `⟨Finset.univ.image g, ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.card_univ, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, ← pow_mul, sq]`.

Use `_ = Ideal.absNorm I ^ (r ^ 2) := by rw [← Nat.card_eq_fintype_card, hcardQ]`. Introduce `x hx hxY`. Establish `hG : Good x` using `(hGood x).mpr ⟨hx, hxY⟩`. Take `⟨hG', hk⟩` from `hg (key x) ⟨x, hG, rfl⟩`. Use `set x' := g (key x) with hx'`.

Establish `hdiff : ∀ i j, ∃ t : 𝓞 K, φ t = Sx x i j - Sx x' i j`. Introduce `i j`. Take `⟨o, ho, hko⟩` from `hkey x hG i j`. Take `⟨o', ho', hko'⟩` from `hkey x' hG' i j`. Establish `e : ((o' : J.toAddSubgroup) : Q) = (o : Q)`.

Rewrite using `[← hko, ← hko', hk]`. Establish `hm` using `QuotientAddGroup.eq.mp e`. Rewrite `hm` using `[AddSubgroup.mem_addSubgroupOf]`. Take `⟨t, ht⟩` from `Ideal.mem_span_singleton'.mp hm`. Use `⟨t, ?_⟩` and prove the remaining obligations.

Establish `ht' : φ t * φ a = φ a * (Sx x i j - Sx x' i j)`. Rewrite using `[← map_mul, ht]`. Simplify using `only [AddSubgroup.coe_add, AddSubgroup.coe_neg, map_add, map_neg]`. Rewrite using `[← hc, ← hc, ho, ho']`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `mul_left_cancel₀ haK (by rw [mul_comm]; exact ht')`. Take `⟨c, hcc⟩ : ∃ c : Matrix (Fin r) (Fin r) (𝓞 K), ∀ i j, φ (c i j) = Sx x i j - Sx x' i j` from `⟨fun i j => Classical.choose (hdiff i j), fun i j => Classical.choose_spec (hdiff i j)⟩`. Establish `hcm : c.map φ = Sx x - Sx x'`. Use extensionality with `i j`. Simplify using `[hcc]`.

Use `⟨x', Finset.mem_image_of_mem _ (Finset.mem_univ _), c, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hcm, Matrix.conjTranspose_sub, (hSx x hG).2, (hSx x' hG').2]`. Normalize the expressions using the abelian group laws. Rewrite using `[hcm, Matrix.sub_mul, ← (hSx x hG).1, ← (hSx x' hG').1]`. Normalize the expressions using the abelian group laws.
-/
theorem xClasses : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (A : Ideal (𝓞 K)) (r : ℕ) (Y : Matrix (Fin r) (Fin (r + 1)) (𝓞 K)) (b₀ : Fin (r + 1)), A ≠ ⊥ → (Y.submatrix id b₀.succAbove).det ≠ 0 → ∃ reps : Finset (Matrix (Fin r) (Fin (r + 1)) K), reps.card ≤ Ideal.absNorm (Ideal.span {(Y.submatrix id b₀.succAbove).det} * A) ^ (r ^ 2) ∧ ∀ x : Matrix (Fin r) (Fin (r + 1)) K, (∀ a b, ∀ α ∈ A, ∃ o : 𝓞 K, (o : K) = (α : K) * x a b) → xᴴ * Y.map (algebraMap (𝓞 K) K) + (Y.map (algebraMap (𝓞 K) K))ᴴ * x = 0 → ∃ x₀ ∈ reps, ∃ c : Matrix (Fin r) (Fin r) (𝓞 K), (c.map (algebraMap (𝓞 K) K))ᴴ = -c.map (algebraMap (𝓞 K) K) ∧ x = x₀ + c.map (algebraMap (𝓞 K) K) * Y.map (algebraMap (𝓞 K) K) := by
  classical
  intro K _ _ _ A r Y b₀ hA hdet
  set f := b₀.succAbove with hf
  set φ := algebraMap (𝓞 K) K with hφ
  set D := (Y.submatrix id f).det with hD
  set I := Ideal.span {D} * A with hI
  set YK := Y.map φ with hYK
  have hφinj : Function.Injective φ := IsFractionRing.injective (𝓞 K) K
  have hc : ∀ u : 𝓞 K, (u : K) = φ u := fun u => rfl
  have hI0 : I ≠ ⊥ := by
    intro h0
    rcases mul_eq_zero.mp (show Ideal.span {D} * A = 0 from h0) with h1 | h1
    · exact hdet (Ideal.span_singleton_eq_bot.mp h1)
    · exact hA h1
  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
  obtain ⟨J, hJ⟩ : I ∣ Ideal.span {a} := Ideal.dvd_span_singleton.mpr haI
  have haK : φ a ≠ 0 := fun h0 => ha0 (hφinj (h0.trans (map_zero φ).symm))

  let C : Matrix (Fin (r + 1)) (Fin r) K :=
    (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) K).submatrix id f
  have hC : ∀ M : Matrix (Fin r) (Fin (r + 1)) K, M * C = M.submatrix id f := fun M => by
    simpa [C] using Matrix.mul_submatrix_one (Equiv.refl (Fin (r + 1))) f M
  have hYf : YK * C = (Y.submatrix id f).map φ := by
    rw [hC, hYK, Matrix.submatrix_map]
  have hdetYf : IsUnit (YK * C).det := by
    rw [hYf, show ((Y.submatrix id f).map φ).det = φ D from (RingHom.map_det φ _).symm]
    exact isUnit_iff_ne_zero.mpr (fun h0 => hdet (hφinj (h0.trans (map_zero φ).symm)))
  have hdetYfH : IsUnit (YK * C)ᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr (isUnit_iff_ne_zero.mp hdetYf))
  obtain ⟨Good, hGood⟩ : ∃ G : Matrix (Fin r) (Fin (r + 1)) K → Prop, ∀ x, G x ↔
      (∀ p q, ∀ α ∈ A, ∃ o : 𝓞 K, (o : K) = (α : K) * x p q) ∧ xᴴ * YK + YKᴴ * x = 0 :=
    ⟨_, fun _ => Iff.rfl⟩

  obtain ⟨Sx, hSx⟩ : ∃ Sx : Matrix (Fin r) (Fin (r + 1)) K → Matrix (Fin r) (Fin r) K,
      ∀ x, Good x → x = Sx x * YK ∧ (Sx x)ᴴ = -Sx x := by
    refine ⟨fun x => x * C * (YK * C)⁻¹, fun x hG => ?_⟩
    have hxY := ((hGood x).mp hG).2
    set Yf := YK * C with hYfdef
    set S := x * C * Yf⁻¹ with hS
    have hSYf : S * Yf = x * C := Matrix.nonsing_inv_mul_cancel_right _ _ hdetYf
    set P := x - S * YK with hP
    have hxP : x = S * YK + P := by rw [hP]; abel
    have hPC : P * C = 0 := by
      rw [hP, Matrix.sub_mul, Matrix.mul_assoc, ← hYfdef, hSYf, sub_self]
    have h1 : Cᴴ * xᴴ = Yfᴴ * Sᴴ := by
      rw [← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul, hSYf]
    have h2 : Cᴴ * YKᴴ = Yfᴴ := by rw [← Matrix.conjTranspose_mul]
    have h3 : Yfᴴ * Sᴴ * YK + Yfᴴ * x = 0 := by
      have h0 : Cᴴ * (xᴴ * YK + YKᴴ * x) = 0 := by rw [hxY, Matrix.mul_zero]
      rwa [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, h2] at h0
    have h4 : Yfᴴ * ((Sᴴ + S) * YK + P) = 0 := by
      calc Yfᴴ * ((Sᴴ + S) * YK + P) = Yfᴴ * Sᴴ * YK + Yfᴴ * (S * YK + P) := by
            simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]; abel
        _ = 0 := by rw [← hxP]; exact h3
    have h5 : (Sᴴ + S) * YK + P = 0 := by
      have h0 := congrArg (fun M => Yfᴴ⁻¹ * M) h4
      rwa [Matrix.nonsing_inv_mul_cancel_left _ _ hdetYfH, Matrix.mul_zero] at h0
    have h6 : Sᴴ + S = 0 := by
      have h0 := congrArg (fun M => M * C * Yf⁻¹) h5
      rwa [Matrix.add_mul, hPC, add_zero, Matrix.mul_assoc ((Sᴴ + S)) YK C, ← hYfdef,
        Matrix.mul_nonsing_inv_cancel_right _ _ hdetYf, Matrix.zero_mul, Matrix.zero_mul] at h0
    have h7 : P = 0 := by rwa [h6, Matrix.zero_mul, zero_add] at h5
    rw [h7, add_zero] at hxP
    exact ⟨hxP, eq_neg_of_add_eq_zero_left h6⟩

  have hent : ∀ x, Good x → ∀ i j, ∃ o : J.toAddSubgroup, ((o : 𝓞 K) : K) = (a : K) * Sx x i j := by
    intro x hG i j
    have hx := ((hGood x).mp hG).1
    have h1 := (hSx x hG).1
    apply xClasses_mem I J a hI0 haI hJ
    have hx' : ∀ p q, ∀ α ∈ A, ∃ o : 𝓞 K, (o : K) = (α : K) * (Sx x * Y.map φ) p q := by
      intro p q α hα; rw [← hYK, ← h1]; exact hx p q α hα
    exact xClasses_denom A Y f (Sx x) hx' i j
  set Q := ↥J.toAddSubgroup ⧸ (Ideal.span {a}).toAddSubgroup.addSubgroupOf J.toAddSubgroup
  have hcardQ : Nat.card Q = Ideal.absNorm I := xClasses_index I J a ha0 hJ
  have : Finite Q := Nat.finite_of_card_ne_zero (by
    rw [hcardQ]; exact fun h0 => hI0 (Ideal.absNorm_eq_zero_iff.mp h0))
  let _ : Fintype Q := Fintype.ofFinite Q
  obtain ⟨key, hkey⟩ : ∃ key : Matrix (Fin r) (Fin (r + 1)) K → (Fin r → Fin r → Q),
      ∀ x, Good x → ∀ i j, ∃ o : J.toAddSubgroup,
        ((o : 𝓞 K) : K) = (a : K) * Sx x i j ∧ key x i j = (o : Q) := by
    refine ⟨fun x i j => if h : ∃ o : J.toAddSubgroup, ((o : 𝓞 K) : K) = (a : K) * Sx x i j
      then ((Classical.choose h : J.toAddSubgroup) : Q) else 0, fun x hG i j => ?_⟩
    have h := hent x hG i j
    exact ⟨Classical.choose h, Classical.choose_spec h, by simp only [dif_pos h]⟩
  obtain ⟨g, hg⟩ : ∃ g : (Fin r → Fin r → Q) → Matrix (Fin r) (Fin (r + 1)) K,
      ∀ q, (∃ x, Good x ∧ key x = q) → Good (g q) ∧ key (g q) = q := by
    refine ⟨fun q => if h : ∃ x, Good x ∧ key x = q then Classical.choose h else 0,
      fun q h => ?_⟩
    simp only [dif_pos h]
    exact Classical.choose_spec h
  refine ⟨Finset.univ.image g, ?_, ?_⟩
  · calc (Finset.univ.image g).card ≤ (Finset.univ : Finset (Fin r → Fin r → Q)).card :=
          Finset.card_image_le
      _ = Fintype.card Q ^ (r ^ 2) := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, ← pow_mul, sq]
      _ = Ideal.absNorm I ^ (r ^ 2) := by rw [← Nat.card_eq_fintype_card, hcardQ]
  · intro x hx hxY
    have hG : Good x := (hGood x).mpr ⟨hx, hxY⟩
    obtain ⟨hG', hk⟩ := hg (key x) ⟨x, hG, rfl⟩
    set x' := g (key x) with hx'
    have hdiff : ∀ i j, ∃ t : 𝓞 K, φ t = Sx x i j - Sx x' i j := by
      intro i j
      obtain ⟨o, ho, hko⟩ := hkey x hG i j
      obtain ⟨o', ho', hko'⟩ := hkey x' hG' i j
      have e : ((o' : J.toAddSubgroup) : Q) = (o : Q) := by
        rw [← hko, ← hko', hk]
      have hm := QuotientAddGroup.eq.mp e
      rw [AddSubgroup.mem_addSubgroupOf] at hm
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hm
      refine ⟨t, ?_⟩
      have ht' : φ t * φ a = φ a * (Sx x i j - Sx x' i j) := by
        rw [← map_mul, ht]
        simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, map_add, map_neg]
        rw [← hc, ← hc, ho, ho']; ring
      exact mul_left_cancel₀ haK (by rw [mul_comm]; exact ht')
    obtain ⟨c, hcc⟩ : ∃ c : Matrix (Fin r) (Fin r) (𝓞 K), ∀ i j, φ (c i j) = Sx x i j - Sx x' i j :=
      ⟨fun i j => Classical.choose (hdiff i j), fun i j => Classical.choose_spec (hdiff i j)⟩
    have hcm : c.map φ = Sx x - Sx x' := by
      ext i j; simp [hcc]
    refine ⟨x', Finset.mem_image_of_mem _ (Finset.mem_univ _), c, ?_, ?_⟩
    · rw [hcm, Matrix.conjTranspose_sub, (hSx x hG).2, (hSx x' hG').2]; abel
    · rw [hcm, Matrix.sub_mul, ← (hSx x hG).1, ← (hSx x' hG').1]; abel

end GlobalTheory
