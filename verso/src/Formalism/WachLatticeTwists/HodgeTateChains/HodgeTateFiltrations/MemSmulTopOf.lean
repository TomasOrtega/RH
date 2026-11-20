import Formalism.WachLatticeTwists.HodgeTateChains.GammaIterateMatrixCongruence
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.FrobeniusPowerCongruenceHolds
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.UnitCongruenceGivesPerturbation

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

open Matrix

section ovr

variable {AA WC : Type} [CommRing AA] [CommRing WC] (ι : AA →+* WC) {r : ℕ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, Matrix.map_one ι (map_zero ι) (map_one ι)⟩`.
-/
lemma over_one : OverSub ι (1 : Matrix (Fin r) (Fin r) WC) :=
  ⟨1, Matrix.map_one ι (map_zero ι) (map_one ι)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, Matrix.map_zero ι (map_zero ι)⟩`.
-/
lemma over_zero : OverSub ι (0 : Matrix (Fin r) (Fin r) WC) :=
  ⟨0, Matrix.map_zero ι (map_zero ι)⟩

/- English proof (translation)
Take `⟨a, rfl⟩` from `hA`. Take `⟨b, rfl⟩` from `hB`. Conclude with `⟨a + b, Matrix.map_add ι (map_add ι) a b⟩`.
-/
lemma over_add {A B : Matrix (Fin r) (Fin r) WC} (hA : OverSub ι A) (hB : OverSub ι B) :
    OverSub ι (A + B) := by
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨b, rfl⟩ := hB
  exact ⟨a + b, Matrix.map_add ι (map_add ι) a b⟩

/- English proof (translation)
Take `⟨a, rfl⟩` from `hA`. Conclude with `⟨-a, by ext i j; simp⟩`.
-/
lemma over_neg {A : Matrix (Fin r) (Fin r) WC} (hA : OverSub ι A) : OverSub ι (-A) := by
  obtain ⟨a, rfl⟩ := hA
  exact ⟨-a, by ext i j; simp⟩

/- English proof (translation)
Take `⟨a, rfl⟩` from `hA`. Take `⟨b, rfl⟩` from `hB`. Conclude with `⟨a * b, Matrix.map_mul⟩`.
-/
lemma over_mul {A B : Matrix (Fin r) (Fin r) WC} (hA : OverSub ι A) (hB : OverSub ι B) :
    OverSub ι (A * B) := by
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨b, rfl⟩ := hB
  exact ⟨a * b, Matrix.map_mul⟩

def overGrp : AddSubgroup (Matrix (Fin r) (Fin r) WC) where
  carrier := {M | OverSub ι M}
  zero_mem' := over_zero ι
  add_mem' := fun ha hb => over_add ι ha hb
  neg_mem' := fun ha => over_neg ι ha

end ovr

/- English proof (translation)
Introduce `ℓ AA WC _ _ ι φ r hsat hcl hφ hstep Z S S' Y hS hS' hY hZ`. Set `T : Matrix (Fin r) (Fin r) WC →+ Matrix (Fin r) (Fin r) WC` to `AddMonoidHom.mk' (fun M => M.map φ - S * M * S') (by`. Introduce `a b`. Rewrite using `[Matrix.map_add φ (map_add φ), Matrix.mul_add, Matrix.add_mul]`. Use the proof step `abel)`.

Use `lemmaA ℓ (Matrix (Fin r) (Fin r) WC) (overGrp ι) T hsat ?_ ?_ ?_ Z ?_` and prove the remaining obligations. Introduce `x hx`. Apply `hcl` to reduce the goal to its premises. Introduce `n`. Take `⟨a, ha, b, hab⟩` from `hx n`.

Conclude with `⟨a, b, ha, hab⟩`. Introduce `a ha`. Conclude with `(overGrp ι).sub_mem (hφ a ha) (over_mul ι (over_mul ι hS ha) hS')`. Introduce and unpack `x ⟨a, ha, b, hab⟩`. Take `⟨A, B, hA, hAB⟩` from `hstep x S S' hS hS' ⟨a, b, ha, hab⟩`.

Conclude with `⟨A, hA, B, hAB⟩`. Use `show OverSub ι (Z.map φ - S * Z * S')`. Rewrite using `[hZ, add_sub_cancel_left]`. Conclude with `hY`.
-/
theorem lemmaAMat : StatLemmaAMat := by
  intro ℓ AA WC _ _ ι φ r hsat hcl hφ hstep Z S S' Y hS hS' hY hZ
  let T : Matrix (Fin r) (Fin r) WC →+ Matrix (Fin r) (Fin r) WC :=
    AddMonoidHom.mk' (fun M => M.map φ - S * M * S') (by
      intro a b
      rw [Matrix.map_add φ (map_add φ), Matrix.mul_add, Matrix.add_mul]
      abel)
  refine lemmaA ℓ (Matrix (Fin r) (Fin r) WC) (overGrp ι) T hsat ?_ ?_ ?_ Z ?_
  · intro x hx
    apply hcl
    intro n
    obtain ⟨a, ha, b, hab⟩ := hx n
    exact ⟨a, b, ha, hab⟩
  · intro a ha
    exact (overGrp ι).sub_mem (hφ a ha) (over_mul ι (over_mul ι hS ha) hS')
  · rintro x ⟨a, ha, b, hab⟩
    obtain ⟨A, B, hA, hAB⟩ := hstep x S S' hS hS' ⟨a, b, ha, hab⟩
    exact ⟨A, hA, B, hAB⟩
  · show OverSub ι (Z.map φ - S * Z * S')
    rw [hZ, add_sub_cancel_left]
    exact hY

/- English proof (translation)
Establish `hp : ∀ (n : ℕ) (a : WC), t ^ n * a = 0 → a = 0`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro a ha`. Simplify using `using ha`.

Consider the case `succ n ih => intro a ha; exact ht a (ih _ (by rw [← mul_assoc, ← pow_succ]; exact ha))`. Use extensionality with `i j`. Establish `h1` using `congrFun (congrFun h i) j`. Simplify using `only [Matrix.smul_apply, smul_eq_mul] at h1`. Conclude with `sub_eq_zero.1 (hp n _ (by rw [mul_sub, h1, sub_self]))`.
-/
lemma cancel_pow {WC : Type} [CommRing WC] (t : WC) (ht : ∀ a : WC, t * a = 0 → a = 0) (n : ℕ) {r : ℕ}
    (M M' : Matrix (Fin r) (Fin r) WC) (h : t ^ n • M = t ^ n • M') : M = M' := by
  have hp : ∀ (n : ℕ) (a : WC), t ^ n * a = 0 → a = 0 := by
    intro n
    induction n with
    | zero => intro a ha; simpa using ha
    | succ n ih => intro a ha; exact ht a (ih _ (by rw [← mul_assoc, ← pow_succ]; exact ha))
  ext i j
  have h1 := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h1
  exact sub_eq_zero.1 (hp n _ (by rw [mul_sub, h1, sub_self]))

/- English proof (translation)
Introduce `AA WC _ _ ι φ x ξ r M0 h0 Xx Xi P P1 Q1 hL hx hξ h1 h2 hW1 hP1 hPQ`. Prove the components needed by the constructor for the conclusion. Apply `hL _ (P1.map ι) 1 0 ⟨P1, rfl⟩ (over_one ι) (over_zero ι)` to reduce the goal to its premises. Rewrite using `[Matrix.map_smul' φ _ _ (map_mul φ), map_pow, hx, hW1, hP1, map_mul, mul_pow, add_zero, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm]`. Apply `hL _ 1 (Q1.map ι) 0 (over_one ι) ⟨Q1, rfl⟩ (over_zero ι)` to reduce the goal to its premises.

Establish `e1 : Xi.map φ * P = Xi`. Establish `e0 : Xi.map φ * Xx.map φ = 1`. Rewrite using `[← Matrix.map_mul, h2, Matrix.map_one φ (map_zero φ) (map_one φ)]`. Rewrite `e0` using `[hW1, ← Matrix.mul_assoc]`. Combine the equalities or inequalities in the displayed calculation.

Establish `e3 : (ι ξ) ^ h0 • Xi.map φ = Xi * Q1.map ι`. Apply `cancel_pow (ι ξ) hξ M0` to reduce the goal to its premises. Establish `a1 : Xi.map φ * (P1.map ι * Q1.map ι) = (ι ξ) ^ (M0 + h0) • Xi.map φ`. Rewrite using `[← Matrix.map_mul, hPQ, Matrix.map_smul' ι _ _ (map_mul ι), Matrix.map_one ι (map_zero ι) (map_one ι), Matrix.mul_smul, Matrix.mul_one, map_pow]`. Rewrite `a1` using `[← Matrix.mul_assoc, hP1, Matrix.mul_smul, e1, Matrix.smul_mul]`.

Rewrite using `[smul_smul, ← pow_add, ← a1]`. Rewrite using `[Matrix.map_smul' φ _ _ (map_mul φ), map_pow, hx, map_mul, mul_pow, ← smul_smul, e3, add_zero, Matrix.one_mul, Matrix.smul_mul]`.
-/
theorem sandwichAA : StatSandwichAA := by
  intro AA WC _ _ ι φ x ξ r M0 h0 Xx Xi P P1 Q1 hL hx hξ h1 h2 hW1 hP1 hPQ
  constructor
  · apply hL _ (P1.map ι) 1 0 ⟨P1, rfl⟩ (over_one ι) (over_zero ι)
    rw [Matrix.map_smul' φ _ _ (map_mul φ), map_pow, hx, hW1, hP1, map_mul, mul_pow, add_zero,
      Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm]
  · apply hL _ 1 (Q1.map ι) 0 (over_one ι) ⟨Q1, rfl⟩ (over_zero ι)
    have e1 : Xi.map φ * P = Xi := by
      have e0 : Xi.map φ * Xx.map φ = 1 := by
        rw [← Matrix.map_mul, h2, Matrix.map_one φ (map_zero φ) (map_one φ)]
      rw [hW1, ← Matrix.mul_assoc] at e0
      calc Xi.map φ * P = Xi.map φ * P * (Xx * Xi) := by rw [h1, Matrix.mul_one]
        _ = (Xi.map φ * P * Xx) * Xi := by rw [← Matrix.mul_assoc]
        _ = Xi := by rw [e0, Matrix.one_mul]
    have e3 : (ι ξ) ^ h0 • Xi.map φ = Xi * Q1.map ι := by
      apply cancel_pow (ι ξ) hξ M0
      have a1 : Xi.map φ * (P1.map ι * Q1.map ι) = (ι ξ) ^ (M0 + h0) • Xi.map φ := by
        rw [← Matrix.map_mul, hPQ, Matrix.map_smul' ι _ _ (map_mul ι),
          Matrix.map_one ι (map_zero ι) (map_one ι), Matrix.mul_smul, Matrix.mul_one, map_pow]
      rw [← Matrix.mul_assoc, hP1, Matrix.mul_smul, e1, Matrix.smul_mul] at a1
      rw [smul_smul, ← pow_add, ← a1]
    rw [Matrix.map_smul' φ _ _ (map_mul φ), map_pow, hx, map_mul, mul_pow, ← smul_smul, e3, add_zero,
      Matrix.one_mul, Matrix.smul_mul]

/- English proof (translation)
Introduce `ℓ hℓ AA OC _ _ ϑ x c r M0 h0 A A' hc hAA' hA'A`. Establish `hle` using `(minimal_exponent_attained ℓ hℓ (M0 + h0)).1`. Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le hle`. Establish `hmap : ∀ B B' : Matrix (Fin r) (Fin r) AA, B * B' = (x ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) AA) → B.map ϑ * B'.map ϑ = ((ϑ x) ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) OC)`. Introduce `B B' h`.

Rewrite using `[← Matrix.map_mul, h, Matrix.map_smul' ϑ _ _ (map_mul ϑ), Matrix.map_one ϑ (map_zero ϑ) (map_one ϑ), map_pow]`. Establish `hs : ((ϑ x) ^ k * c) * (ϑ x) ^ (M0 + h0) = (ℓ : OC)`. Rewrite using `[← hc, hk, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨((ϑ x) ^ k * c) • A'.map ϑ, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.mul_smul, hmap A A' hAA', smul_smul, hs]`. Rewrite using `[Matrix.smul_mul, hmap A' A hA'A, smul_smul, hs]`.
-/
theorem sandwichOC : StatSandwichOC := by
  intro ℓ hℓ AA OC _ _ ϑ x c r M0 h0 A A' hc hAA' hA'A
  have hle := (minimal_exponent_attained ℓ hℓ (M0 + h0)).1
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  have hmap : ∀ B B' : Matrix (Fin r) (Fin r) AA,
      B * B' = (x ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) AA) →
      B.map ϑ * B'.map ϑ = ((ϑ x) ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) OC) := by
    intro B B' h
    rw [← Matrix.map_mul, h, Matrix.map_smul' ϑ _ _ (map_mul ϑ),
      Matrix.map_one ϑ (map_zero ϑ) (map_one ϑ), map_pow]
  have hs : ((ϑ x) ^ k * c) * (ϑ x) ^ (M0 + h0) = (ℓ : OC) := by
    rw [← hc, hk, pow_add]; ring
  refine ⟨((ϑ x) ^ k * c) • A'.map ϑ, ?_, ?_⟩
  · rw [Matrix.mul_smul, hmap A A' hAA', smul_smul, hs]
  · rw [Matrix.smul_mul, hmap A' A hA'A, smul_smul, hs]

section vec

variable {As : Type} [CommRing As] {r : ℕ}

/- English proof (translation)
Establish `hv : v = ∑ j, v j • (Pi.single j (1 : As) : Fin r → As)`. Use extensionality with `k`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[hv]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (h j) trivial`.
-/
lemma mem_smul_top_of (J : Ideal As) (v : Fin r → As) (h : ∀ j, v j ∈ J) :
    v ∈ J • (⊤ : Submodule As (Fin r → As)) := by
  have hv : v = ∑ j, v j • (Pi.single j (1 : As) : Fin r → As) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (h j) trivial

/- English proof (translation)
Use `Submodule.smul_induction_on h ?_ ?_` and prove the remaining obligations. Introduce `a ha n _`. Conclude with `J.mul_mem_right _ ha`. Introduce `a b ha hb`. Conclude with `J.add_mem ha hb`.
-/
lemma coord_of_mem (J : Ideal As) (v : Fin r → As)
    (h : v ∈ J • (⊤ : Submodule As (Fin r → As))) (j : Fin r) : v j ∈ J := by
  refine Submodule.smul_induction_on h ?_ ?_
  · intro a ha n _
    exact J.mul_mem_right _ ha
  · intro a b ha hb
    exact J.add_mem ha hb

end vec

/- English proof (translation)
Introduce `ℓ hℓ As R _ _ σ πs ϑ z ϖ ϖ' r s n G h0 h1 hG hπ hϖ' hz hϖ hdiv i j`. Use `set I : Ideal As := Ideal.span {(ℓ : As), πs} with hI`. Establish `hsl : ∀ (a : As) (v : Fin r → As), gamN σ G (a • v) = σ a • gamN σ G v`. Introduce `a v`. Use extensionality with `k`.

Simplify using `[gamN, Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc]`. Establish `hW3 : ∀ v : Fin r → As, gamN σ G v - v ∈ I • (⊤ : Submodule As (Fin r → As))`. Introduce `v`. Apply `mem_smul_top_of` to reduce the goal to its premises. Introduce `k`.

Establish `e : (gamN σ G v - v) k = ∑ t, ((σ (v t) - v t) * G t k + v t * (G - 1) t k)`. Establish `e1 : v k = ∑ t, v t * (1 : Matrix (Fin r) (Fin r) As) t k`. Simplify using `[Matrix.one_apply]`. Establish `e2 : (gamN σ G v - v) k = ∑ t, σ (v t) * G t k - v k` using `rfl`. Rewrite using `[e2]`.

Use `conv_lhs => rw [e1]`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.sub_apply]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `I.sum_mem fun t _ => I.add_mem (I.mul_mem_right _ (h0 _)) (I.mul_mem_left _ (hG t k))`. Take `⟨y, z', hz', hyz⟩` from `frobenius_power_congruence_holds ℓ hℓ As I σ (Fin r → As) (gamN σ G) hsl h0 h1 hW3 (s + n + 1) (by omega) (Pi.single i 1)`. Establish `hone : (1 : Matrix (Fin r) (Fin r) As) i j = (Pi.single i (1 : As) : Fin r → As) j`. Rewrite using `[Matrix.one_apply, Pi.single_apply]`.

Distinguish the cases in `h : i = j`. Simplify using `[h]`. Simplify using `[h, Ne.symm h]`. Establish `hc : ((⇑(gamN σ G))^[ℓ ^ (s + n + 1)] (Pi.single i 1)) j - (1 : Matrix (Fin r) (Fin r) As) i j = (ℓ : As) ^ 2 * y j + z' j`. Rewrite using `[hone]`.

Use `congrFun hyz j` as an intermediate fact. Simplify using `only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply] at this`. Rewrite using `[this, nsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hc, map_add, map_mul, map_pow, map_natCast]`. Apply `dvd_add` to reduce the goal to its premises. Apply `Dvd.dvd.mul_right` to reduce the goal to its premises. Rewrite using `[pow_two]`. Conclude with `mul_dvd_mul hz hϖ`.

Establish `e : s + n + 1 - 1 = s + n` using `rfl`. Rewrite `hz'` using `[e]`. Establish `hm : ϑ (z' j) ∈ Ideal.map ϑ (I ^ (ℓ ^ (s + n)))` using `Ideal.mem_map_of_mem ϑ (coord_of_mem _ z' hz' j)`. Establish `hle : Ideal.map ϑ I ≤ Ideal.span {ϖ'}`. Rewrite using `[hI, Ideal.map_span, Ideal.span_le]`.

Introduce and unpack `_ ⟨a, ha, rfl⟩`. Break down `ha with rfl | rfl` into its components or cases. Rewrite using `[map_natCast]`. Conclude with `Ideal.mem_span_singleton.2 hϖ'`. Rewrite using `[hπ]`.

Conclude with `Ideal.mem_span_singleton_self _`. Rewrite `hm` using `[Ideal.map_pow]`. Establish `hm2` using `Ideal.pow_right_mono hle (ℓ ^ (s + n)) hm`. Rewrite `hm2` using `[Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Conclude with `dvd_trans hdiv hm2`.
-/
theorem w3Um : GammaIterateMatrixCongruence := by
  intro ℓ hℓ As R _ _ σ πs ϑ z ϖ ϖ' r s n G h0 h1 hG hπ hϖ' hz hϖ hdiv i j
  set I : Ideal As := Ideal.span {(ℓ : As), πs} with hI
  have hsl : ∀ (a : As) (v : Fin r → As), gamN σ G (a • v) = σ a • gamN σ G v := by
    intro a v
    ext k
    simp [gamN, Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc]
  have hW3 : ∀ v : Fin r → As, gamN σ G v - v ∈ I • (⊤ : Submodule As (Fin r → As)) := by
    intro v
    apply mem_smul_top_of
    intro k
    have e : (gamN σ G v - v) k = ∑ t, ((σ (v t) - v t) * G t k + v t * (G - 1) t k) := by
      have e1 : v k = ∑ t, v t * (1 : Matrix (Fin r) (Fin r) As) t k := by
        simp [Matrix.one_apply]
      have e2 : (gamN σ G v - v) k = ∑ t, σ (v t) * G t k - v k := rfl
      rw [e2]
      conv_lhs => rw [e1]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Matrix.sub_apply]; ring
    rw [e]
    exact I.sum_mem fun t _ => I.add_mem (I.mul_mem_right _ (h0 _)) (I.mul_mem_left _ (hG t k))
  obtain ⟨y, z', hz', hyz⟩ := frobenius_power_congruence_holds ℓ hℓ As I σ (Fin r → As) (gamN σ G) hsl h0 h1 hW3 (s + n + 1)
    (by omega) (Pi.single i 1)
  have hone : (1 : Matrix (Fin r) (Fin r) As) i j = (Pi.single i (1 : As) : Fin r → As) j := by
    rw [Matrix.one_apply, Pi.single_apply]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  have hc : ((⇑(gamN σ G))^[ℓ ^ (s + n + 1)] (Pi.single i 1)) j
      - (1 : Matrix (Fin r) (Fin r) As) i j = (ℓ : As) ^ 2 * y j + z' j := by
    rw [hone]
    have := congrFun hyz j
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply] at this
    rw [this, nsmul_eq_mul]; push_cast; ring
  rw [hc, map_add, map_mul, map_pow, map_natCast]
  apply dvd_add
  · apply Dvd.dvd.mul_right
    rw [pow_two]
    exact mul_dvd_mul hz hϖ
  · have e : s + n + 1 - 1 = s + n := rfl
    rw [e] at hz'
    have hm : ϑ (z' j) ∈ Ideal.map ϑ (I ^ (ℓ ^ (s + n))) :=
      Ideal.mem_map_of_mem ϑ (coord_of_mem _ z' hz' j)
    have hle : Ideal.map ϑ I ≤ Ideal.span {ϖ'} := by
      rw [hI, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨a, ha, rfl⟩
      rcases ha with rfl | rfl
      · rw [map_natCast]; exact Ideal.mem_span_singleton.2 hϖ'
      · rw [hπ]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.map_pow] at hm
    have hm2 := Ideal.pow_right_mono hle (ℓ ^ (s + n)) hm
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hm2
    exact dvd_trans hdiv hm2

/- English proof (translation)
Introduce `R _ t c r Um hc hU i j`. Establish `e : (c • Um - 1) i j = (c - 1) * Um i j + (Um - 1) i j`. Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `dvd_add (Dvd.dvd.mul_right hc _) (hU i j)`.
-/
theorem twistUm : StatTwistUm := by
  intro R _ t c r Um hc hU i j
  have e : (c • Um - 1) i j = (c - 1) * Um i j + (Um - 1) i j := by
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
  rw [e]
  exact dvd_add (Dvd.dvd.mul_right hc _) (hU i j)

/- English proof (translation)
Introduce `ℓ _ u s H0 hs h2 hu`. Establish `hℓ : ℓ.Prime` using `Fact.out`. Take `⟨_, hval⟩` from `Formalism.WindowSums.valuation_zpow_sub_one ℓ u s hs h2 hu ((ℓ ^ (s + n0 ℓ H0 + 1) : ℕ) : ℤ) (by exact_mod_cast pow_ne_zero _ hℓ.ne_zero)`. Use `⟨?_, by unfold mOf; omega, by unfold mOf; omega, by unfold mOf; omega⟩` and prove the remaining obligations. Rewrite `hval` using `[zpow_natCast]`.

Rewrite using `[hval]`. Establish `hv : padicValInt ℓ ((ℓ ^ (s + n0 ℓ H0 + 1) : ℕ) : ℤ) = s + n0 ℓ H0 + 1`. Rewrite using `[padicValInt.of_nat, padicValNat.prime_pow]`. Rewrite using `[hv]`. Unfold `mOf`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem genM : StatGenM := by
  intro ℓ _ u s H0 hs h2 hu
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨_, hval⟩ := Formalism.WindowSums.valuation_zpow_sub_one ℓ u s hs h2 hu ((ℓ ^ (s + n0 ℓ H0 + 1) : ℕ) : ℤ)
    (by exact_mod_cast pow_ne_zero _ hℓ.ne_zero)
  refine ⟨?_, by unfold mOf; omega, by unfold mOf; omega, by unfold mOf; omega⟩
  rw [zpow_natCast] at hval
  rw [hval]
  have hv : padicValInt ℓ ((ℓ ^ (s + n0 ℓ H0 + 1) : ℕ) : ℤ) = s + n0 ℓ H0 + 1 := by
    rw [padicValInt.of_nat, padicValNat.prime_pow]
  rw [hv]
  unfold mOf
  ring

/- English proof (translation)
Introduce `ℓ _ u s H0 hs h2 hu`. Take `⟨hv, h1, h22, hsm⟩` from `genM ℓ u s H0 hs h2 hu`. Use `⟨fun U a n d D hd => ll ℓ _ _ h1 (fun _ => h22) hv U a n d D hd, fun U h0U hne D => h0 ℓ _ _ h1 (fun _ => h22) hv U h0U hne D, fun e d U D L K T φ ψ hd => tbFull ℓ u _ s _ e d hs h2 hsm hu hv U D L K T φ ψ hd⟩` and prove the remaining obligations.
-/
theorem topsAtM : StatTopsAtM := by
  intro ℓ _ u s H0 hs h2 hu
  obtain ⟨hv, h1, h22, hsm⟩ := genM ℓ u s H0 hs h2 hu
  refine ⟨fun U a n d D hd => ll ℓ _ _ h1 (fun _ => h22) hv U a n d D hd,
    fun U h0U hne D => h0 ℓ _ _ h1 (fun _ => h22) hv U h0U hne D,
    fun e d U D L K T φ ψ hd => tbFull ℓ u _ s _ e d hs h2 hsm hu hv U D L K T φ ψ hd⟩

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
