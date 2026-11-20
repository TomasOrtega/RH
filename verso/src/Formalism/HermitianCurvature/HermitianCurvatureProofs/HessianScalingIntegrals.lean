import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces

noncomputable section

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology

namespace Formalism.FourierDecayAlt.P.HessianScalingIntegrals

variable {K : Type} [CommRing K]

/- English proof (translation)
Take `⟨h, hh⟩` from `QuotientAddGroup.mk_out_eq_add Λ x`. Rewrite using `[hh]`. Simplify using the standard rewrite rules.
-/
theorem out_mk_sub (Λ : AddSubgroup K) (x : K) :
    (Quotient.out (x : K ⧸ Λ) : K) - x ∈ Λ := by
  obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add Λ x
  rw [hh]; simp

/- English proof (translation)
Establish `: DiscreteTopology (K ⧸ Λ)` using `QuotientAddGroup.discreteTopology hΛ`. Establish `h1 : ((QuotientAddGroup.mk : K → K ⧸ Λ) '' (L : Set K)).Finite` using `(hL.image QuotientAddGroup.continuous_mk).finite_of_discrete`. Use `(Set.Finite.pi' (fun _ : Fin d => h1)).subset ?_` and prove the remaining obligations. Introduce `y hy i`. Conclude with `⟨_, hy i, QuotientAddGroup.out_eq' _⟩`.
-/
theorem fin_supp [TopologicalSpace K] [IsTopologicalRing K] (Λ L : AddSubgroup K)
    (hΛ : IsOpen (Λ : Set K)) (hL : IsCompact (L : Set K)) (d : ℕ) :
    {y : Fin d → K ⧸ Λ | ∀ i, (Quotient.out (y i) : K) ∈ L}.Finite := by
  have : DiscreteTopology (K ⧸ Λ) := QuotientAddGroup.discreteTopology hΛ
  have h1 : ((QuotientAddGroup.mk : K → K ⧸ Λ) '' (L : Set K)).Finite :=
    (hL.image QuotientAddGroup.continuous_mk).finite_of_discrete
  refine (Set.Finite.pi' (fun _ : Fin d => h1)).subset ?_
  intro y hy i
  exact ⟨_, hy i, QuotientAddGroup.out_eq' _⟩

/- English proof (translation)
Unfold `intK`. Use `congr 1`. Apply `finsum_eq_sum_of_support_subset` to reduce the goal to its premises. Introduce `y hy`. Simplify using `only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]`.

Conclude with `hg _ hy`.
-/
theorem intK_eq_sum (R : Subring K) (Λ L : AddSubgroup K) (d : ℕ)
    (hfin : {y : Fin d → K ⧸ Λ | ∀ i, (Quotient.out (y i) : K) ∈ L}.Finite)
    (g : (Fin d → K) → ℂ) (hg : ∀ x, g x ≠ 0 → ∀ i, x i ∈ L) :
    intK R Λ d g = (volL R Λ : ℂ) ^ d * ∑ y ∈ hfin.toFinset, g (fun i => Quotient.out (y i)) := by
  unfold intK
  congr 1
  apply finsum_eq_sum_of_support_subset
  intro y hy
  simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
  exact hg _ hy

/- English proof (translation)
Establish `hinv : ∀ x x' : Fin m → K, (∀ k, x k - x' k ∈ Λ) → G x = G x'`. Introduce `x x' h`. Use `hG x' (fun k => x k - x' k) h` as an intermediate fact. Rewrite using `[← this]`. Use `congr 1`.

Use extensionality with `k`. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Introduce `ξ l hl`. Distinguish the cases in `hξ : ∀ k, ξ k ∈ B`.

Establish `hξl : ∀ k, (ξ + l) k ∈ B` using `fun k => B.add_mem (hξ k) (hΛB (hl k))`. Rewrite using `[← hGG' _ hξl, ← hGG' _ hξ]`. Apply `hinv` to reduce the goal to its premises. Introduce `k`. Use `(hcos (ξ + l) ξ hξl hξ).2 (fun k => by simpa using hl k) k` as an intermediate fact.

Simplify using `using this`. Establish `hξl : ¬ ∀ k, (ξ + l) k ∈ B` using `fun h => hξ fun k => by`. Use `B.sub_mem (h k) (hΛB (hl k))` as an intermediate fact. Simplify using `using this`. Rewrite using `[hG'0 _ hξl, hG'0 _ hξ]`.

Unfold `intK`. Use `congr 1`. Set `o : (Fin m → K ⧸ Λ) → (Fin m → K)` to `fun y i => Quotient.out (y i)`. Set `e : (Fin m → K ⧸ Λ) → (Fin m → K ⧸ Λ)` to `fun y k => ((z + φ (o y) k : K) : K ⧸ Λ)`. Establish `hoe : ∀ y k, o (e y) k - (z + φ (o y) k) ∈ Λ` using `fun y k => out_mk_sub Λ _`.

Establish `h1 : ∑ᶠ y, G (o y) = ∑ᶠ y ∈ {y | ∀ k, o y k - z ∈ B}, G (o y)`. Use `finsum_congr fun y => ?_` and prove the remaining obligations. Rewrite using `[finsum_eq_if]`. Use `split_ifs with h`. Both sides reduce to the same expression.

Conclude with `hG0 _ h`. Establish `h2 : ∑ᶠ y, G' (o y) = ∑ᶠ y ∈ {y | ∀ k, o y k ∈ B}, G' (o y)`. Use `finsum_congr fun y => ?_` and prove the remaining obligations. Rewrite using `[finsum_eq_if]`. Use `split_ifs with h`.

Both sides reduce to the same expression. Conclude with `hG'0 _ h`. Express the relevant statement in the definitionally equal form `∑ᶠ y, G (o y) = ∑ᶠ y, G' (o y)`. Rewrite using `[h1, h2]`. Use `symm`.

Use `finsum_mem_eq_of_bijOn e ⟨?_, ?_, ?_⟩ ?_` and prove the remaining obligations. Introduce `y hy k`. Establish `h3 : φ (o y) k ∈ B` using `hbij.mapsTo hy k`. Establish `h4` using `B.add_mem (hΛB (hoe y k)) h3`. Establish `: o (e y) k - z = o (e y) k - (z + φ (o y) k) + φ (o y) k` using `by ring`.

Rewrite using `[this]`. Conclude with `h4`. Introduce `y hy y' hy' hyy`. Establish `h3 : ∀ k, φ (o y) k - φ (o y') k ∈ Λ`. Introduce `k`.

Use `congrFun hyy k` as an intermediate fact. Establish `h5 : ((z + φ (o y) k : K) : K ⧸ Λ) = ((z + φ (o y') k : K) : K ⧸ Λ)` using `this`. Rewrite `h5` using `[QuotientAddGroup.eq]`. Establish `h6` using `Λ.neg_mem h5`. Establish `: φ (o y) k - φ (o y') k = -(-(z + φ (o y) k) + (z + φ (o y') k))` using `by ring`.

Rewrite using `[this]`. Conclude with `h6`. Establish `h4` using `(hcos _ _ hy hy').1 h3`. Use function extensionality and compare the values at `k`. Establish `h5 : ((o y k : K) : K ⧸ Λ) = ((o y' k : K) : K ⧸ Λ)`.

Rewrite using `[QuotientAddGroup.eq]`. Establish `h6` using `Λ.neg_mem (h4 k)`. Establish `: -o y k + o y' k = -(o y k - o y' k)` using `by ring`. Rewrite using `[this]`. Conclude with `h6`.

Simplify `h5` using `[o]`. Introduce `y hy`. Establish `hmem : (fun k => o y k - z) ∈ {ξ : Fin m → K | ∀ k, ξ k ∈ B}` using `hy`. Take `⟨ξ, hξ, hξy⟩` from `hbij.surjOn hmem`. Set `y' : Fin m → K ⧸ Λ` to `fun k => ((ξ k : K) : K ⧸ Λ)`.

Establish `h3 : ∀ k, o y' k - ξ k ∈ Λ` using `fun k => out_mk_sub Λ _`. Establish `h4 : ∀ k, o y' k ∈ B` using `fun k => by`. Use `B.add_mem (hΛB (h3 k)) (hξ k)` as an intermediate fact. Simplify using `using this`. Use `⟨y', h4, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `k`. Establish `h5` using `(hcos _ _ h4 hξ).2 h3 k`. Establish `h6 : ((z + φ (o y') k : K) : K ⧸ Λ) = ((o y k : K) : K ⧸ Λ)`. Rewrite using `[QuotientAddGroup.eq]`. Establish `h7 : φ ξ k = o y k - z` using `congrFun hξy k`.

Establish `: -(z + φ (o y') k) + o y k = -(φ (o y') k - φ ξ k)` using `by rw [h7]; ring`. Rewrite using `[this]`. Conclude with `Λ.neg_mem h5`. Establish `h8 : ((o y k : K) : K ⧸ Λ) = y k` using `QuotientAddGroup.out_eq' _`. Conclude with `h6.trans h8`.

Introduce `y hy`. Rewrite using `[← hGG' _ hy]`. Use `symm`. Conclude with `hinv _ _ (hoe y)`.
-/
theorem ball_piece (R : Subring K) (m : ℕ) (B Λ : AddSubgroup K) (hΛB : Λ ≤ B) (z : K)
    (φ : (Fin m → K) → (Fin m → K))
    (hbij : Set.BijOn φ {ξ | ∀ k, ξ k ∈ B} {ξ | ∀ k, ξ k ∈ B})
    (hcos : ∀ ξ η : Fin m → K, (∀ k, ξ k ∈ B) → (∀ k, η k ∈ B) →
      ((∀ k, φ ξ k - φ η k ∈ Λ) ↔ ∀ k, ξ k - η k ∈ Λ))
    (G G' : (Fin m → K) → ℂ) (hG : LatInvN Λ G)
    (hG0 : ∀ x, (¬ ∀ k, x k - z ∈ B) → G x = 0)
    (hG'0 : ∀ ξ, (¬ ∀ k, ξ k ∈ B) → G' ξ = 0)
    (hGG' : ∀ ξ, (∀ k, ξ k ∈ B) → G (fun k => z + φ ξ k) = G' ξ) :
    LatInvN Λ G' ∧ intK R Λ m G = intK R Λ m G' := by
  classical
  have hinv : ∀ x x' : Fin m → K, (∀ k, x k - x' k ∈ Λ) → G x = G x' := by
    intro x x' h
    have := hG x' (fun k => x k - x' k) h
    rw [← this]; congr 1; ext k; simp
  constructor
  · intro ξ l hl
    by_cases hξ : ∀ k, ξ k ∈ B
    · have hξl : ∀ k, (ξ + l) k ∈ B := fun k => B.add_mem (hξ k) (hΛB (hl k))
      rw [← hGG' _ hξl, ← hGG' _ hξ]
      apply hinv
      intro k
      have := (hcos (ξ + l) ξ hξl hξ).2 (fun k => by simpa using hl k) k
      simpa using this
    · have hξl : ¬ ∀ k, (ξ + l) k ∈ B := fun h => hξ fun k => by
        have := B.sub_mem (h k) (hΛB (hl k)); simpa using this
      rw [hG'0 _ hξl, hG'0 _ hξ]
  · unfold intK
    congr 1
    let o : (Fin m → K ⧸ Λ) → (Fin m → K) := fun y i => Quotient.out (y i)
    let e : (Fin m → K ⧸ Λ) → (Fin m → K ⧸ Λ) := fun y k => ((z + φ (o y) k : K) : K ⧸ Λ)
    have hoe : ∀ y k, o (e y) k - (z + φ (o y) k) ∈ Λ := fun y k => out_mk_sub Λ _
    have h1 : ∑ᶠ y, G (o y) = ∑ᶠ y ∈ {y | ∀ k, o y k - z ∈ B}, G (o y) := by
      refine finsum_congr fun y => ?_
      rw [finsum_eq_if]
      split_ifs with h
      · rfl
      · exact hG0 _ h
    have h2 : ∑ᶠ y, G' (o y) = ∑ᶠ y ∈ {y | ∀ k, o y k ∈ B}, G' (o y) := by
      refine finsum_congr fun y => ?_
      rw [finsum_eq_if]
      split_ifs with h
      · rfl
      · exact hG'0 _ h
    change ∑ᶠ y, G (o y) = ∑ᶠ y, G' (o y)
    rw [h1, h2]
    symm
    refine finsum_mem_eq_of_bijOn e ⟨?_, ?_, ?_⟩ ?_
    · intro y hy k
      have h3 : φ (o y) k ∈ B := hbij.mapsTo hy k
      have h4 := B.add_mem (hΛB (hoe y k)) h3
      have : o (e y) k - z = o (e y) k - (z + φ (o y) k) + φ (o y) k := by ring
      rw [this]; exact h4
    · intro y hy y' hy' hyy
      have h3 : ∀ k, φ (o y) k - φ (o y') k ∈ Λ := by
        intro k
        have := congrFun hyy k
        have h5 : ((z + φ (o y) k : K) : K ⧸ Λ) = ((z + φ (o y') k : K) : K ⧸ Λ) := this
        rw [QuotientAddGroup.eq] at h5
        have h6 := Λ.neg_mem h5
        have : φ (o y) k - φ (o y') k = -(-(z + φ (o y) k) + (z + φ (o y') k)) := by ring
        rw [this]; exact h6
      have h4 := (hcos _ _ hy hy').1 h3
      funext k
      have h5 : ((o y k : K) : K ⧸ Λ) = ((o y' k : K) : K ⧸ Λ) := by
        rw [QuotientAddGroup.eq]
        have h6 := Λ.neg_mem (h4 k)
        have : -o y k + o y' k = -(o y k - o y' k) := by ring
        rw [this]; exact h6
      simpa [o] using h5
    · intro y hy
      have hmem : (fun k => o y k - z) ∈ {ξ : Fin m → K | ∀ k, ξ k ∈ B} := hy
      obtain ⟨ξ, hξ, hξy⟩ := hbij.surjOn hmem
      let y' : Fin m → K ⧸ Λ := fun k => ((ξ k : K) : K ⧸ Λ)
      have h3 : ∀ k, o y' k - ξ k ∈ Λ := fun k => out_mk_sub Λ _
      have h4 : ∀ k, o y' k ∈ B := fun k => by
        have := B.add_mem (hΛB (h3 k)) (hξ k); simpa using this
      refine ⟨y', h4, ?_⟩
      funext k
      have h5 := (hcos _ _ h4 hξ).2 h3 k
      have h6 : ((z + φ (o y') k : K) : K ⧸ Λ) = ((o y k : K) : K ⧸ Λ) := by
        rw [QuotientAddGroup.eq]
        have h7 : φ ξ k = o y k - z := congrFun hξy k
        have : -(z + φ (o y') k) + o y k = -(φ (o y') k - φ ξ k) := by rw [h7]; ring
        rw [this]; exact Λ.neg_mem h5
      have h8 : ((o y k : K) : K ⧸ Λ) = y k := QuotientAddGroup.out_eq' _
      exact h6.trans h8
    · intro y hy
      rw [← hGG' _ hy]
      symm
      exact hinv _ _ (hoe y)

/- English proof (translation)
Unfold `hessM`. Rewrite using `[smul_smul, mul_inv, Units.val_mul, mul_comm]`.
-/
theorem hess_scale (m : ℕ) (z t : Kˣ) :
    hessM m (z * t) = ((t⁻¹ : Kˣ) : K) • hessM m z := by
  unfold hessM
  rw [smul_smul, mul_inv, Units.val_mul, mul_comm]

/- English proof (translation)
Introduce `h`. Establish `h1 : ψ (a + -a) = 1` using `by simp`. Rewrite `h1` using `[AddChar.map_add_eq_mul, h, zero_mul]`. Conclude with `zero_ne_one h1`.
-/
theorem psi_ne_zero (ψ : AddChar K ℂ) (a : K) : ψ a ≠ 0 := by
  intro h
  have h1 : ψ (a + -a) = 1 := by simp
  rw [AddChar.map_add_eq_mul, h, zero_mul] at h1
  exact zero_ne_one h1

/- English proof (translation)
Use `hA (fun _ => z) (fun k => x k - z) hx` as an intermediate fact. Rewrite using `[← this]`. Use `congr 1`. Use extensionality with `k`. Simplify using the standard rewrite rules.
-/
theorem amp_const (Λ₁ : AddSubgroup K) {m : ℕ} (A : (Fin m → K) → ℂ) (hA : LatInvN Λ₁ A) (z : K)
    (x : Fin m → K) (hx : ∀ k, x k - z ∈ Λ₁) : A x = A (fun _ => z) := by
  have := hA (fun _ => z) (fun k => x k - z) hx
  rw [← this]; congr 1; ext k; simp

open Classical in

/- English proof (translation)
Substitute `hD` using the available equality. Distinguish the cases in `hA0 : A (fun _ => (z : K)) = 0`. Establish `h0 : (fun x : Fin m → K => if ∀ k, x k - (z : K) ∈ B then A x * ψ (g0 ((z : K) ^ (m + 1)) x * ((t⁻¹ : Kˣ) : K)) else 0) = fun _ => 0`. Use function extensionality and compare the values at `x`. Use `split_ifs with h`.

Rewrite using `[amp_const Λ₁ A hA z x (fun k => hBΛ₁ _ (h k)), hA0, zero_mul]`. Both sides reduce to the same expression. Rewrite using `[h0, hA0]`. Simplify using `[intK]`. Take `⟨φ, hbij, hcos, hval⟩` from `hmorse set c : ℂ := A (fun _ => (z : K)) * ψ (((m + 1 : ℕ) : K) * (z : K) * ((t⁻¹ : Kˣ) : K)) with hc`.

Establish `hc0 : c ≠ 0` using `mul_ne_zero hA0 (psi_ne_zero ψ _)`. Take `⟨hi, he⟩` from `ball_piece R m B.toAddSubgroup Λ.toAddSubgroup hΛB (z : K) φ hbij (hcos Λ hΛB) _ (fun ξ => c * gaussF ψ B.toAddSubgroup (hessM m (z * t)) ξ) hinv (fun x hx => if_neg hx) (fun ξ hξ => by`. Establish `: gaussF ψ B.toAddSubgroup (hessM m (z * t)) ξ = 0` using `if_neg hξ`. Rewrite using `[this, mul_zero])`. Use the proof step `(fun ξ hξ => by`.

Establish `h1 : ∀ k, (z : K) + φ ξ k - (z : K) ∈ B` using `fun k => by`. Establish `: φ ξ k ∈ B` using `hbij.mapsTo hξ k`. Simplify using `using this`. Establish `h2 : gaussF ψ B.toAddSubgroup (hessM m (z * t)) ξ = ψ (Ring.inverse 2 * (ξ ⬝ᵥ (hessM m (z * t) *ᵥ ξ)))` using `if_pos hξ`. Rewrite using `[h2]`.

Simplify using `only []`. Rewrite using `[if_pos h1, amp_const Λ₁ A hA z _ (fun k => hBΛ₁ _ (h1 k)), (hval ξ hξ).2, hc, mul_assoc, ← AddChar.map_add_eq_mul, hess_scale, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]`. Use `congr 2`. Use the proof step `ring)`. Establish `hi' : LatInvN Λ.toAddSubgroup (gaussF ψ B.toAddSubgroup (hessM m (z * t)))`.

Introduce `ξ l hl`. Conclude with `mul_left_cancel₀ hc0 (hi ξ l hl)`. Rewrite using `[he]`. Establish `h3 : intK R Λ.toAddSubgroup m (fun ξ => c * gaussF ψ B.toAddSubgroup (hessM m (z * t)) ξ) = c * intK R Λ.toAddSubgroup m (gaussF ψ B.toAddSubgroup (hessM m (z * t)))`. Unfold `intK`.

Rewrite using `[mul_left_comm]`. Use `congr 1`. Use `smul_finsum c (fun y : Fin m → K ⧸ Λ.toAddSubgroup => gaussF ψ B.toAddSubgroup (hessM m (z * t)) (fun i => Quotient.out (y i)))` as an intermediate fact. Simplify `this.symm` using `[smul_eq_mul]`. Rewrite using `[h3, hγ.2.2 (z * t) _ _ hB hΛ hadm hi', Units.val_mul, hmod.2.2, Real.mul_rpow hmod.1.le hmod.2.1.le, hc]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem root_piece [TopologicalSpace K] (R : Subring K) (ψ : AddChar K ℂ) (m : ℕ) (γ : Kˣ → ℂ)
    (hγ : IsGamma R ψ m γ) (Λ₁ : AddSubgroup K) (B Λ : Submodule R K)
    (hB : IsLat B.toAddSubgroup) (hΛ : IsLat Λ.toAddSubgroup) (hΛB : Λ ≤ B)
    (hBΛ₁ : ∀ b ∈ B, b ∈ Λ₁)
    (A : (Fin m → K) → ℂ) (hA : LatInvN Λ₁ A) (t z : Kˣ) (D : K) (hD : (z : K) ^ (m + 1) = D)
    (hmod : 0 < modK R (z : K) ∧ 0 < modK R (t : K) ∧
      modK R ((z : K) * (t : K)) = modK R (z : K) * modK R (t : K))
    (hadm : GaussAdm ψ B.toAddSubgroup (hessM m (z * t)))
    (hmorse : ∃ φ : (Fin m → K) → (Fin m → K),
        Set.BijOn φ {ξ | ∀ k, ξ k ∈ B} {ξ | ∀ k, ξ k ∈ B} ∧
        (∀ Λ : Submodule R K, Λ ≤ B → ∀ ξ η : Fin m → K, (∀ k, ξ k ∈ B) → (∀ k, η k ∈ B) →
          ((∀ k, φ ξ k - φ η k ∈ Λ) ↔ ∀ k, ξ k - η k ∈ Λ)) ∧
        ∀ ξ : Fin m → K, (∀ k, ξ k ∈ B) →
          (∀ k, IsUnit ((z : K) + φ ξ k)) ∧
          g0 ((z : K) ^ (m + 1)) (fun k => (z : K) + φ ξ k) =
            ((m + 1 : ℕ) : K) * (z : K) + Ring.inverse 2 * (ξ ⬝ᵥ (hessM m z *ᵥ ξ)))
    (hinv : LatInvN Λ.toAddSubgroup (fun x : Fin m → K => if ∀ k, x k - (z : K) ∈ B then
      A x * ψ (g0 D x * ((t⁻¹ : Kˣ) : K)) else 0)) :
    intK R Λ.toAddSubgroup m (fun x : Fin m → K => if ∀ k, x k - (z : K) ∈ B then
      A x * ψ (g0 D x * ((t⁻¹ : Kˣ) : K)) else 0) =
      ((modK R (t : K) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
        (γ (z * t) * ((modK R ((m + 1 : ℕ) : K) ^ (-(1 : ℝ) / 2) *
            modK R (z : K) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
          ψ (((m + 1 : ℕ) : K) * (z : K) * ((t⁻¹ : Kˣ) : K)) * A (fun _ => (z : K))) := by
  subst hD
  by_cases hA0 : A (fun _ => (z : K)) = 0
  · have h0 : (fun x : Fin m → K => if ∀ k, x k - (z : K) ∈ B then
        A x * ψ (g0 ((z : K) ^ (m + 1)) x * ((t⁻¹ : Kˣ) : K)) else 0) = fun _ => 0 := by
      funext x
      split_ifs with h
      · rw [amp_const Λ₁ A hA z x (fun k => hBΛ₁ _ (h k)), hA0, zero_mul]
      · rfl
    rw [h0, hA0]
    simp [intK]
  · obtain ⟨φ, hbij, hcos, hval⟩ := hmorse
    set c : ℂ := A (fun _ => (z : K)) * ψ (((m + 1 : ℕ) : K) * (z : K) * ((t⁻¹ : Kˣ) : K)) with hc
    have hc0 : c ≠ 0 := mul_ne_zero hA0 (psi_ne_zero ψ _)
    obtain ⟨hi, he⟩ := ball_piece R m B.toAddSubgroup Λ.toAddSubgroup hΛB (z : K) φ hbij
      (hcos Λ hΛB) _ (fun ξ => c * gaussF ψ B.toAddSubgroup (hessM m (z * t)) ξ) hinv
      (fun x hx => if_neg hx)
      (fun ξ hξ => by
        have : gaussF ψ B.toAddSubgroup (hessM m (z * t)) ξ = 0 := if_neg hξ
        rw [this, mul_zero])
      (fun ξ hξ => by
        have h1 : ∀ k, (z : K) + φ ξ k - (z : K) ∈ B := fun k => by
          have : φ ξ k ∈ B := hbij.mapsTo hξ k
          simpa using this
        have h2 : gaussF ψ B.toAddSubgroup (hessM m (z * t)) ξ =
            ψ (Ring.inverse 2 * (ξ ⬝ᵥ (hessM m (z * t) *ᵥ ξ))) := if_pos hξ
        rw [h2]
        simp only []
        rw [if_pos h1, amp_const Λ₁ A hA z _ (fun k => hBΛ₁ _ (h1 k)), (hval ξ hξ).2, hc, mul_assoc,
          ← AddChar.map_add_eq_mul, hess_scale, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
        congr 2
        ring)
    have hi' : LatInvN Λ.toAddSubgroup (gaussF ψ B.toAddSubgroup (hessM m (z * t))) := by
      intro ξ l hl
      exact mul_left_cancel₀ hc0 (hi ξ l hl)
    rw [he]
    have h3 : intK R Λ.toAddSubgroup m (fun ξ => c * gaussF ψ B.toAddSubgroup (hessM m (z * t)) ξ) =
        c * intK R Λ.toAddSubgroup m (gaussF ψ B.toAddSubgroup (hessM m (z * t))) := by
      unfold intK
      rw [mul_left_comm]
      congr 1
      have := smul_finsum c (fun y : Fin m → K ⧸ Λ.toAddSubgroup =>
        gaussF ψ B.toAddSubgroup (hessM m (z * t)) (fun i => Quotient.out (y i)))
      simpa [smul_eq_mul] using this.symm
    rw [h3, hγ.2.2 (z * t) _ _ hB hΛ hadm hi', Units.val_mul, hmod.2.2,
      Real.mul_rpow hmod.1.le hmod.2.1.le, hc]
    push_cast
    ring

/- English proof (translation)
Use `forall_congr' fun k => ?_` and prove the remaining obligations. Establish `h1 : (x + l) k - z = x k - z + l k` using `by simp only [Pi.add_apply]; ring`. Rewrite using `[h1]`. Conclude with `B.add_mem_cancel_right (hl k)`.
-/
theorem ball_iff (B : AddSubgroup K) {m : ℕ} (x l : Fin m → K) (z : K) (hl : ∀ k, l k ∈ B) :
    (∀ k, (x + l) k - z ∈ B) ↔ ∀ k, x k - z ∈ B := by
  refine forall_congr' fun k => ?_
  have h1 : (x + l) k - z = x k - z + l k := by simp only [Pi.add_apply]; ring
  rw [h1]
  exact B.add_mem_cancel_right (hl k)

end Formalism.FourierDecayAlt.P.HessianScalingIntegrals

open Formalism.FourierDecayAlt.P.HessianScalingIntegrals in
open Classical in

/- English proof (translation)
Introduce `hNS hMorse hRef hMod hRF _ _ _ _ _ hRS hSM hGA _ K _ _ _ R ψ hD hn m hm γ hγ L₀ Λ₁ Q hL₀ hΛ₁ hQ hQu`. Take `⟨VM, hVM, hM⟩` from `hMorse K R ψ hD hn m hm Q hQ hQu`. Take `⟨VS, hVS, hS⟩` from `hRS K R ψ hD hn (m + 1) (by omega) Q hQ hQu`. Establish `hΛ₁n : (Λ₁ : Set K) ∈ 𝓝 (0 : K)` using `hΛ₁.1.mem_nhds Λ₁.zero_mem`. Take `⟨B, hB, hBV⟩` from `hSM K R ψ hD hn (VM ∩ VS ∩ (Λ₁ : Set K)) (inter_mem (inter_mem hVM hVS) hΛ₁n)`.

Take `⟨VN, hVN, hN⟩` from `hNS K R ψ hD hn m hm L₀ Λ₁ B.toAddSubgroup Q hL₀ hΛ₁ hB hQ hQu`. Take `⟨VG, hVG, hG⟩` from `hGA K R ψ hD hn m B.toAddSubgroup Q hB hQ hQu`. Use `⟨VN ∩ VG, inter_mem hVN hVG, ?_⟩` and prove the remaining obligations. Introduce `t D' A ht hD' hA Λ hΛ hF`. Establish `hΛn : (Λ : Set K) ∈ 𝓝 (0 : K)` using `hΛ.1.mem_nhds Λ.zero_mem`.

Establish `hBn : (B : Set K) ∈ 𝓝 (0 : K)` using `hB.1.mem_nhds B.zero_mem`. Take `⟨Λ', hΛ', hΛ'V⟩` from `hSM K R ψ hD hn ((Λ : Set K) ∩ (B : Set K)) (inter_mem hΛn hBn)`. Establish `hΛ'Λ : Λ'.toAddSubgroup ≤ Λ` using `fun x hx => (hΛ'V hx).1`. Establish `hΛ'B : Λ' ≤ B` using `fun x hx => (hΛ'V hx).2`. Use `set F : (Fin m → K) → ℂ := fun x => A x * ψ (g0 (D' : K) x * ((t⁻¹ : Kˣ) : K)) with hFdef`.

Establish `hFsupp : ∀ x, F x ≠ 0 → ∀ i, x i ∈ L₀` using `fun x hx i => (hA.1 x (left_ne_zero_of_mul hx) i).1`. Establish `hF' : LatInvN Λ'.toAddSubgroup F` using `fun x l hl => hF x l fun i => hΛ'Λ (hl i)`. Rewrite using `[← hRef K R ψ hD Λ Λ'.toAddSubgroup L₀ m F hΛ hΛ' hL₀ hΛ'Λ hFsupp hF]`. Establish `hfin : {z : Kˣ | z ^ (m + 1) = D'}.Finite` using `@hRF K _ hD.artin hD.red (m + 1) (by omega) D'`. Establish `hzQ : ∀ z : Kˣ, z ^ (m + 1) = D' → (z : K) ^ (m + 1) = (D' : K)` using `fun z hz => by`.

Rewrite using `[← hz, Units.val_pow_eq_pow_val]`. Establish `hsep : ∀ z z' : Kˣ, z ^ (m + 1) = D' → z' ^ (m + 1) = D' → ∀ x : Fin m → K, (∀ k, x k - (z : K) ∈ B) → (∀ k, x k - (z' : K) ∈ B) → z = z'`. Introduce `z z' hz hz' x hx hx'`. Use `hS z z' (by rw [hzQ z hz]; exact hD') (hz.trans hz'.symm) ?_` and prove the remaining obligations. Establish `h1` using `B.sub_mem (hx' ⟨0, hm⟩) (hx ⟨0, hm⟩)`.

Establish `h2 : (z : K) - (z' : K) = x ⟨0, hm⟩ - (z' : K) - (x ⟨0, hm⟩ - (z : K))` using `by ring`. Rewrite using `[h2]`. Conclude with `(hBV h1).1.2`. Use `set Foff : (Fin m → K) → ℂ := fun x => if ∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, x k - (z : K) ∈ B.toAddSubgroup then 0 else F x with hFoff`. Use `set Fz : Kˣ → (Fin m → K) → ℂ := fun z x => if ∀ k, x k - (z : K) ∈ B then F x else 0 with hFz`.

Establish `hdec : ∀ x, F x = Foff x + ∑ z ∈ hfin.toFinset, Fz z x`. Introduce `x`. Distinguish the cases in `h : ∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, x k - (z : K) ∈ B.toAddSubgroup`. Take `⟨z0, hz0, hx0⟩` from `h`. Establish `h1 : Foff x = 0` using `if_pos ⟨z0, hz0, hx0⟩`.

Rewrite using `[h1, zero_add, Finset.sum_eq_single z0]`. Conclude with `(if_pos hx0).symm`. Introduce `z hz hne`. Use `if_neg fun hx => hne ?_` and prove the remaining obligations. Conclude with `hsep z z0 (by simpa using hz) hz0 x hx hx0`.

Introduce `hz`. Conclude with `absurd (by simpa using hz0) hz`. Establish `h1 : Foff x = F x` using `if_neg h`. Rewrite using `[h1, Finset.sum_eq_zero, add_zero]`. Introduce `z hz`.

Conclude with `if_neg fun hx => h ⟨z, by simpa using hz, hx⟩`. Establish `hFoffInv : LatInvN Λ'.toAddSubgroup Foff`. Introduce `x l hl`. Establish `h1 : (∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, (x + l) k - (z : K) ∈ B.toAddSubgroup) ↔ ∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, x k - (z : K) ∈ B.toAddSubgroup` using `exists_congr fun z => and_congr_right fun _ => ball_iff B.toAddSubgroup x l z fun k => hΛ'B (hl k)`. Simplify using `only [hFoff]`.

Rewrite using `[if_congr h1 rfl (hF' x l hl)]`. Establish `hFzInv : ∀ z : Kˣ, LatInvN Λ'.toAddSubgroup (Fz z)`. Introduce `z x l hl`. Establish `h1 : (∀ k, (x + l) k - (z : K) ∈ B) ↔ ∀ k, x k - (z : K) ∈ B` using `ball_iff B.toAddSubgroup x l z fun k => hΛ'B (hl k)`. Simplify using `only [hFz]`.

Rewrite using `[if_congr h1 (hF' x l hl) rfl]`. Establish `hFoffSupp : ∀ x, Foff x ≠ 0 → ∀ i, x i ∈ L₀`. Introduce `x hx`. Apply `hFsupp` to reduce the goal to its premises. Introduce `h0`.

Apply `hx` to reduce the goal to its premises. Simplify using `only [hFoff, h0, ite_self]`. Establish `hFzSupp : ∀ z x, Fz z x ≠ 0 → ∀ i, x i ∈ L₀`. Introduce `z x hx`. Apply `hFsupp` to reduce the goal to its premises.

Introduce `h0`. Apply `hx` to reduce the goal to its premises. Simplify using `only [hFz, h0, ite_self]`. Establish `hS0` using `fin_supp Λ'.toAddSubgroup L₀ hΛ'.1 hL₀.2 m`. Establish `hsplit : intK R Λ'.toAddSubgroup m F = intK R Λ'.toAddSubgroup m Foff + ∑ z ∈ hfin.toFinset, intK R Λ'.toAddSubgroup m (Fz z)`.

Rewrite using `[intK_eq_sum R _ L₀ m hS0 F hFsupp, intK_eq_sum R _ L₀ m hS0 Foff hFoffSupp]`. Repeatedly rewrite using `[fun z => intK_eq_sum R _ L₀ m hS0 (Fz z) (hFzSupp z)]`. Rewrite using `[← Finset.mul_sum, ← mul_add, Finset.sum_comm, ← Finset.sum_add_distrib]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun y _ => hdec _`.

Establish `hoff : intK R Λ'.toAddSubgroup m Foff = 0` using `hN t D' A ht.1 hD' hA Λ'.toAddSubgroup hΛ' hFoffInv`. Rewrite using `[hsplit, hoff, zero_add]`. Establish `hrhs : (∑ᶠ z : Kˣ, if z ^ (m + 1) = D' then γ (z * t) * ((modK R ((m + 1 : ℕ) : K) ^ (-(1 : ℝ) / 2) * modK R (z : K) ^ ((m : ℝ) / 2) : ℝ) : ℂ) * ψ (((m + 1 : ℕ) : K) * (z : K) * ((t⁻¹ : Kˣ) : K)) * A (fun _ => (z : K)) else 0) = ∑ z ∈ hfin.toFinset, γ (z * t) * ((modK R ((m + 1 : …`. Rewrite using `[finsum_eq_sum_of_support_subset (s := hfin.toFinset)]`. Use `Finset.sum_congr rfl fun z hz => if_pos (by simpa using hz)` and prove the remaining obligations.

Introduce `z hz`. Simplify using `only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]`. Assume the negation of the conclusion as `h`. Conclude with `hz (if_neg h)`. Rewrite using `[hrhs, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun z hz => ?_` and prove the remaining obligations. Establish `hz' : z ^ (m + 1) = D'` using `by simpa using hz`. Establish `hzq : (z : K) ^ (m + 1) ∈ Q` using `by rw [hzQ z hz']; exact hD'`. Conclude with `root_piece R ψ m γ hγ Λ₁ B Λ' hB hΛ' hΛ'B (fun b hb => (hBV hb).2) A hA.2 t z (D' : K) (hzQ z hz') ⟨(hMod K R ψ hD z t).1, (hMod K R ψ hD t z).1, (hMod K R ψ hD z t).2⟩ (hG t z ht.2 hzq) (hM B hB (fun b hb => (hBV hb).1.1) z hzq) (hFzInv z)`.
-/
theorem Formalism.FourierDecayAlt.P.stationaryPhaseOfSteps : Formalism.FourierDecayAlt.A6.StationaryAssemble := by
  intro hNS hMorse hRef hMod hRF _ _ _ _ _ hRS hSM hGA _ K _ _ _ R ψ hD hn m hm γ hγ L₀ Λ₁ Q hL₀ hΛ₁
    hQ hQu
  obtain ⟨VM, hVM, hM⟩ := hMorse K R ψ hD hn m hm Q hQ hQu
  obtain ⟨VS, hVS, hS⟩ := hRS K R ψ hD hn (m + 1) (by omega) Q hQ hQu
  have hΛ₁n : (Λ₁ : Set K) ∈ 𝓝 (0 : K) := hΛ₁.1.mem_nhds Λ₁.zero_mem
  obtain ⟨B, hB, hBV⟩ := hSM K R ψ hD hn (VM ∩ VS ∩ (Λ₁ : Set K))
    (inter_mem (inter_mem hVM hVS) hΛ₁n)
  obtain ⟨VN, hVN, hN⟩ := hNS K R ψ hD hn m hm L₀ Λ₁ B.toAddSubgroup Q hL₀ hΛ₁ hB hQ hQu
  obtain ⟨VG, hVG, hG⟩ := hGA K R ψ hD hn m B.toAddSubgroup Q hB hQ hQu
  refine ⟨VN ∩ VG, inter_mem hVN hVG, ?_⟩
  intro t D' A ht hD' hA Λ hΛ hF

  have hΛn : (Λ : Set K) ∈ 𝓝 (0 : K) := hΛ.1.mem_nhds Λ.zero_mem
  have hBn : (B : Set K) ∈ 𝓝 (0 : K) := hB.1.mem_nhds B.zero_mem
  obtain ⟨Λ', hΛ', hΛ'V⟩ := hSM K R ψ hD hn ((Λ : Set K) ∩ (B : Set K)) (inter_mem hΛn hBn)
  have hΛ'Λ : Λ'.toAddSubgroup ≤ Λ := fun x hx => (hΛ'V hx).1
  have hΛ'B : Λ' ≤ B := fun x hx => (hΛ'V hx).2
  set F : (Fin m → K) → ℂ := fun x => A x * ψ (g0 (D' : K) x * ((t⁻¹ : Kˣ) : K)) with hFdef
  have hFsupp : ∀ x, F x ≠ 0 → ∀ i, x i ∈ L₀ := fun x hx i =>
    (hA.1 x (left_ne_zero_of_mul hx) i).1
  have hF' : LatInvN Λ'.toAddSubgroup F := fun x l hl => hF x l fun i => hΛ'Λ (hl i)
  rw [← hRef K R ψ hD Λ Λ'.toAddSubgroup L₀ m F hΛ hΛ' hL₀ hΛ'Λ hFsupp hF]

  have hfin : {z : Kˣ | z ^ (m + 1) = D'}.Finite :=
    @hRF K _ hD.artin hD.red (m + 1) (by omega) D'
  have hzQ : ∀ z : Kˣ, z ^ (m + 1) = D' → (z : K) ^ (m + 1) = (D' : K) := fun z hz => by
    rw [← hz, Units.val_pow_eq_pow_val]
  have hsep : ∀ z z' : Kˣ, z ^ (m + 1) = D' → z' ^ (m + 1) = D' → ∀ x : Fin m → K,
      (∀ k, x k - (z : K) ∈ B) → (∀ k, x k - (z' : K) ∈ B) → z = z' := by
    intro z z' hz hz' x hx hx'
    refine hS z z' (by rw [hzQ z hz]; exact hD') (hz.trans hz'.symm) ?_
    have h1 := B.sub_mem (hx' ⟨0, hm⟩) (hx ⟨0, hm⟩)
    have h2 : (z : K) - (z' : K) = x ⟨0, hm⟩ - (z' : K) - (x ⟨0, hm⟩ - (z : K)) := by ring
    rw [h2]
    exact (hBV h1).1.2
  set Foff : (Fin m → K) → ℂ := fun x =>
    if ∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, x k - (z : K) ∈ B.toAddSubgroup then 0 else F x with hFoff
  set Fz : Kˣ → (Fin m → K) → ℂ := fun z x => if ∀ k, x k - (z : K) ∈ B then F x else 0 with hFz
  have hdec : ∀ x, F x = Foff x + ∑ z ∈ hfin.toFinset, Fz z x := by
    intro x
    by_cases h : ∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, x k - (z : K) ∈ B.toAddSubgroup
    · obtain ⟨z0, hz0, hx0⟩ := h
      have h1 : Foff x = 0 := if_pos ⟨z0, hz0, hx0⟩
      rw [h1, zero_add, Finset.sum_eq_single z0]
      · exact (if_pos hx0).symm
      · intro z hz hne
        refine if_neg fun hx => hne ?_
        exact hsep z z0 (by simpa using hz) hz0 x hx hx0
      · intro hz
        exact absurd (by simpa using hz0) hz
    · have h1 : Foff x = F x := if_neg h
      rw [h1, Finset.sum_eq_zero, add_zero]
      intro z hz
      exact if_neg fun hx => h ⟨z, by simpa using hz, hx⟩
  have hFoffInv : LatInvN Λ'.toAddSubgroup Foff := by
    intro x l hl
    have h1 : (∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, (x + l) k - (z : K) ∈ B.toAddSubgroup) ↔
        ∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, x k - (z : K) ∈ B.toAddSubgroup :=
      exists_congr fun z => and_congr_right fun _ =>
        ball_iff B.toAddSubgroup x l z fun k => hΛ'B (hl k)
    simp only [hFoff]
    rw [if_congr h1 rfl (hF' x l hl)]
  have hFzInv : ∀ z : Kˣ, LatInvN Λ'.toAddSubgroup (Fz z) := by
    intro z x l hl
    have h1 : (∀ k, (x + l) k - (z : K) ∈ B) ↔ ∀ k, x k - (z : K) ∈ B :=
      ball_iff B.toAddSubgroup x l z fun k => hΛ'B (hl k)
    simp only [hFz]
    rw [if_congr h1 (hF' x l hl) rfl]
  have hFoffSupp : ∀ x, Foff x ≠ 0 → ∀ i, x i ∈ L₀ := by
    intro x hx
    apply hFsupp
    intro h0
    apply hx
    simp only [hFoff, h0, ite_self]
  have hFzSupp : ∀ z x, Fz z x ≠ 0 → ∀ i, x i ∈ L₀ := by
    intro z x hx
    apply hFsupp
    intro h0
    apply hx
    simp only [hFz, h0, ite_self]
  have hS0 := fin_supp Λ'.toAddSubgroup L₀ hΛ'.1 hL₀.2 m
  have hsplit : intK R Λ'.toAddSubgroup m F = intK R Λ'.toAddSubgroup m Foff +
      ∑ z ∈ hfin.toFinset, intK R Λ'.toAddSubgroup m (Fz z) := by
    rw [intK_eq_sum R _ L₀ m hS0 F hFsupp, intK_eq_sum R _ L₀ m hS0 Foff hFoffSupp]
    simp_rw [fun z => intK_eq_sum R _ L₀ m hS0 (Fz z) (hFzSupp z)]
    rw [← Finset.mul_sum, ← mul_add, Finset.sum_comm, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun y _ => hdec _
  have hoff : intK R Λ'.toAddSubgroup m Foff = 0 :=
    hN t D' A ht.1 hD' hA Λ'.toAddSubgroup hΛ' hFoffInv
  rw [hsplit, hoff, zero_add]
  have hrhs : (∑ᶠ z : Kˣ, if z ^ (m + 1) = D' then
          γ (z * t) * ((modK R ((m + 1 : ℕ) : K) ^ (-(1 : ℝ) / 2) *
            modK R (z : K) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
          ψ (((m + 1 : ℕ) : K) * (z : K) * ((t⁻¹ : Kˣ) : K)) * A (fun _ => (z : K)) else 0) =
      ∑ z ∈ hfin.toFinset, γ (z * t) * ((modK R ((m + 1 : ℕ) : K) ^ (-(1 : ℝ) / 2) *
            modK R (z : K) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
          ψ (((m + 1 : ℕ) : K) * (z : K) * ((t⁻¹ : Kˣ) : K)) * A (fun _ => (z : K)) := by
    rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
    · refine Finset.sum_congr rfl fun z hz => if_pos (by simpa using hz)
    · intro z hz
      simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
      by_contra h
      exact hz (if_neg h)
  rw [hrhs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hz' : z ^ (m + 1) = D' := by simpa using hz
  have hzq : (z : K) ^ (m + 1) ∈ Q := by rw [hzQ z hz']; exact hD'
  exact root_piece R ψ m γ hγ Λ₁ B Λ' hB hΛ' hΛ'B (fun b hb => (hBV hb).2) A hA.2 t z (D' : K)
    (hzQ z hz') ⟨(hMod K R ψ hD z t).1, (hMod K R ψ hD t z).1, (hMod K R ψ hD z t).2⟩
    (hG t z ht.2 hzq) (hM B hB (fun b hb => (hBV hb).1.1) z hzq) (hFzInv z)
