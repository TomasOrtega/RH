import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.MemInvariantSectionsTwoWeightIff

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

def dPsi (K : Type) [Field K] (m : ℕ) : PolXY K (m + 1) →ₗ[K] MvPolynomial (Fin (m + 1) × Fin (m + 1)) K :=
  (deltaB K m).toLinearMap ∘ₗ (PsiXY K m).toLinearMap

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dPsi_apply (K : Type) [Field K] (m : ℕ) (f : PolXY K (m + 1)) : dPsi K m f = deltaB K m (PsiXY K m f) := rfl

/- English proof (translation)
Use `R.std.1.frac_O` as an intermediate fact. Establish `hΛ : IsLattice R.O (colSpan R.O g)` using `⟨g, hg, rfl⟩`. Rewrite using `[mem_invariant_sections_two_weight_iff hCO m a b hm _ hΛ y]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`.

Take `⟨f, hf, rfl⟩` from `(h2 R.Kf m hm a b x).1 (twoLat_le_twoSp m a b _ hΛ x hx)`. Conclude with `⟨f, hf, (h5 p n' R m hm g hg g' hg' a b f hf).1 hx, rfl⟩`. Introduce and unpack `⟨f, hf, hl, rfl⟩`. Conclude with `⟨_, (h5 p n' R m hm g hg g' hg' a b f hf).2 hl, rfl⟩`.
-/
theorem tie5b (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hCO : CartanOnto) {p n' : ℕ} (R : RS p n') (m : ℕ) (hm : 1 ≤ m)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf) (hg : IsUnit g.det) (g' : GL (Fin (m + 1)) R.Kf)
    (hg' : (g' : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf) = g⁻¹) (a b : ℕ)
    (y : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) :
    y ∈ H0 R.O m (wtPQ m a b) (colSpan R.O g) ↔
      ∃ f ∈ PolAB R.Kf (m + 1) a b, f ∈ latOf g' (GaussLat R.Ov.toSubring) ∧ deltaB R.Kf m (PsiXY R.Kf m f) = y := by
  have := R.std.1.frac_O
  have hΛ : IsLattice R.O (colSpan R.O g) := ⟨g, hg, rfl⟩
  rw [mem_invariant_sections_two_weight_iff hCO m a b hm _ hΛ y]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨f, hf, rfl⟩ := (h2 R.Kf m hm a b x).1 (twoLat_le_twoSp m a b _ hΛ x hx)
    exact ⟨f, hf, (h5 p n' R m hm g hg g' hg' a b f hf).1 hx, rfl⟩
  · rintro ⟨f, hf, hl, rfl⟩
    exact ⟨_, (h5 p n' R m hm g hg g' hg' a b f hf).2 hl, rfl⟩

/- English proof (translation)
Use `R.std.1.frac_O` as an intermediate fact. Establish `hinj : Function.Injective (algebraMap R.O R.Kf)` using `IsFractionRing.injective R.O R.Kf`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Conclude with `delta_twoSp R.Kf m a b hm _ ((h2 R.Kf m hm a b _).2 ⟨f, hf, rfl⟩)`.

Establish `h1 : IsUnit (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf).det` using `by rw [Matrix.det_one]; exact isUnit_one`. Take `⟨B, -, hB1, -, hB2⟩` from `la_basis hinj m (wtPQ m a b) 1 h1`. Rewrite using `[← hB2, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Establish `hi : B i ∈ H0 R.O m (wtPQ m a b) (colSpan R.O (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf))`.

Rewrite using `[H0_eq_twisted_nabla (la_indep hinj) m _ (wtPQ_anti m a b hm) 1 h1, ← hB1]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Take `⟨f, hf, -, hfe⟩` from `(tie5b h2 h5 hCO R m hm 1 h1 1 (by simp) a b (B i)).1 hi`. Conclude with `⟨f, hf, hfe⟩`.
-/
theorem tie3 (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hCO : CartanOnto) {p n' : ℕ} (R : RS p n') (m : ℕ) (hm : 1 ≤ m) (a b : ℕ) :
    (PolAB R.Kf (m + 1) a b).map (dPsi R.Kf m) = dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m a b)) := by
  have := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  apply le_antisymm
  · rintro _ ⟨f, hf, rfl⟩
    exact delta_twoSp R.Kf m a b hm _ ((h2 R.Kf m hm a b _).2 ⟨f, hf, rfl⟩)
  · have h1 : IsUnit (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf).det := by rw [Matrix.det_one]; exact isUnit_one
    obtain ⟨B, -, hB1, -, hB2⟩ := la_basis hinj m (wtPQ m a b) 1 h1
    rw [← hB2, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hi : B i ∈ H0 R.O m (wtPQ m a b) (colSpan R.O (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf)) := by
      rw [H0_eq_twisted_nabla (la_indep hinj) m _ (wtPQ_anti m a b hm) 1 h1, ← hB1]
      exact Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨f, hf, -, hfe⟩ := (tie5b h2 h5 hCO R m hm 1 h1 1 (by simp) a b (B i)).1 hi
    exact ⟨f, hf, hfe⟩

/- English proof (translation)
Establish `h0 : (0 : Fin (m + 1 + 1)) ≠ Fin.last (m + 1)` using `(last_ne_zero' m).symm`. Rewrite using `[hwt_apply]`. Distinguish the cases in `hi : i = 0`. Substitute `hi` using the available equality. Simplify using `[nuOf, wtPQ, h0.symm]`.

Use linear arithmetic over natural numbers and integers. Distinguish the cases in `hl : i = Fin.last (m + 1)`. Simplify using `[nuOf, wtPQ, hl, h0.symm]`. Simplify using `[nuOf, wtPQ, hi, hl, h0.symm]`.
-/
theorem nuOf_wtPQ_cast (m a b : ℕ) (i : Fin (m + 2)) :
    ((nuOf (wtPQ (m + 1) a b) i : ℕ) : ℤ) = hwt m a b i + b := by
  have h0 : (0 : Fin (m + 1 + 1)) ≠ Fin.last (m + 1) := (last_ne_zero' m).symm
  rw [hwt_apply]
  by_cases hi : i = 0
  · subst hi
    simp [nuOf, wtPQ, h0.symm]
    omega
  · by_cases hl : i = Fin.last (m + 1)
    · simp [nuOf, wtPQ, hl, h0.symm]
    · simp [nuOf, wtPQ, hi, hl, h0.symm]

/- English proof (translation)
Unfold `weylDim`. Use `Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[add_sub_add_right_eq_sub]`.
-/
theorem weylDim_shift (n : ℕ) (lam : Fin n → ℤ) (c : ℤ) : weylDim n (fun i => lam i + c) = weylDim n lam := by
  unfold weylDim
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  rw [add_sub_add_right_eq_sub]

/- English proof (translation)
Establish `hanti : Antitone (nuOf (wtPQ (m + 1) a b))`. Introduce `i j hij`. Use `wtPQ_anti (m + 1) a b (by omega) hij` as an intermediate fact. Unfold `nuOf`. Use linear arithmetic over natural numbers and integers.

Establish `hq : (Module.finrank K (dualWeyl K (m + 1 + 1) (m + 1 + 1) (nuOf (wtPQ (m + 1) a b))) : ℚ) = (dimHar (m + 1) a b : ℚ)`. Rewrite using `[finrank_weyl D h3 K _ _ hanti, ← weylDim_hwt_eq, ← weylDim_shift (m + 2) (hwt m a b) b]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `nuOf_wtPQ_cast m a b i`.

Conclude with `hq` after adjusting the coercions.
-/
theorem finrank_wtPQ (D : Formalism.BasicNotions.D7) (h3 : Formalism.MainNotions.ColumnSystems.adm3 D) (K : Type) [Field K] [CharZero K] (m a b : ℕ) :
    Module.finrank K (dualWeyl K (m + 1 + 1) (m + 1 + 1) (nuOf (wtPQ (m + 1) a b))) = dimHar (m + 1) a b := by
  have hanti : Antitone (nuOf (wtPQ (m + 1) a b)) := by
    intro i j hij
    have := wtPQ_anti (m + 1) a b (by omega) hij
    unfold nuOf
    omega
  have hq : (Module.finrank K (dualWeyl K (m + 1 + 1) (m + 1 + 1) (nuOf (wtPQ (m + 1) a b))) : ℚ) =
      (dimHar (m + 1) a b : ℚ) := by
    rw [finrank_weyl D h3 K _ _ hanti, ← weylDim_hwt_eq, ← weylDim_shift (m + 2) (hwt m a b) b]
    congr 1
    funext i
    exact nuOf_wtPQ_cast m a b i
  exact_mod_cast hq

/- English proof (translation)
Take `⟨m, rfl⟩ : ∃ m', m = m' + 1` from `⟨m - 1, by omega⟩`. Establish `: CharZero R.Kf` using `R.charZero`. Establish `hfin : Module.Finite R.Kf (PolAB R.Kf (m + 1 + 1) a b)` using `Har2.finite_polAB (m + 1) a b`. Use `set T := (dPsi R.Kf (m + 1)).domRestrict (PolAB R.Kf (m + 1 + 1) a b) with hT`. Establish `hrange : LinearMap.range T = dualWeyl R.Kf (m + 1 + 1) (m + 1 + 1) (nuOf (wtPQ (m + 1) a b))`.

Rewrite using `[hT, LinearMap.range_domRestrict]`. Conclude with `tie3 h2 h5 hCO R (m + 1) hm a b`. Establish `hrn` using `LinearMap.finrank_range_add_finrank_ker T`. Rewrite `hrn` using `[hrange, finrank_wtPQ D h3 R.Kf m a b, Har2.finrank_polAB]`. Introduce `f hf hf0`.

Establish `hfk : (⟨f, hf⟩ : PolAB R.Kf (m + 1 + 1) a b) ∈ LinearMap.ker T` using `hf0`. Distinguish the cases in `hab : a = 0 ∨ b = 0`. Establish `hk0 : Module.finrank R.Kf (LinearMap.ker T) = 0`. Unfold `dimHar dimPol at hrn`. Rewrite `hrn` using `[if_pos hab]`.

Use linear arithmetic over natural numbers and integers. Establish `hbot : LinearMap.ker T = ⊥` using `Submodule.finrank_eq_zero.1 hk0`. Rewrite `hfk` using `[hbot, Submodule.mem_bot]`. Establish `hf00 : f = 0` using `congrArg Subtype.val hfk`. Conclude with `⟨0, Submodule.zero_mem _, by rw [hf00, mul_zero]⟩`.

Rewrite `hab` using `[not_or]`. Take `⟨a, rfl⟩ : ∃ a', a = a' + 1` from `⟨a - 1, by omega⟩`. Take `⟨b, rfl⟩ : ∃ b', b = b' + 1` from `⟨b - 1, by omega⟩`. Set `μ : PolAB R.Kf (m + 1 + 1) a b →ₗ[R.Kf] PolAB R.Kf (m + 1 + 1) (a + 1) (b + 1)` to `LinearMap.codRestrict _ ((LinearMap.mulLeft R.Kf (hXY R.Kf (m + 1 + 1))) ∘ₗ (PolAB R.Kf (m + 1 + 1) a b).subtype) (fun G => Har2.h_mul_mem G.2)`. Establish `hμinj : Function.Injective μ`.

Introduce `G G' h`. Establish `h' : hXY R.Kf (m + 1 + 1) * (G : PolXY R.Kf (m + 1 + 1)) = hXY R.Kf (m + 1 + 1) * G'` using `congrArg Subtype.val h`. Conclude with `Subtype.ext (mul_left_cancel₀ (hXY_ne_zero R.Kf (m + 1)) h')`. Establish `hle : LinearMap.range μ ≤ LinearMap.ker T`. Introduce and unpack `_ ⟨G, rfl⟩`.

Use `show deltaB R.Kf (m + 1) (PsiXY R.Kf (m + 1) (hXY R.Kf (m + 1 + 1) * (G : PolXY R.Kf (m + 1 + 1)))) = 0`. Rewrite using `[map_mul, map_mul, delta_Psi_h R.Kf (m + 1) hm, zero_mul]`. Establish `hr : Module.finrank R.Kf (LinearMap.range μ) = (a + (m + 1)).choose (m + 1) * (b + (m + 1)).choose (m + 1)`. Rewrite using `[LinearMap.finrank_range_of_inj hμinj, Har2.finrank_polAB]`. Establish `hle2` using `Submodule.finrank_mono hle`.

Establish `heq : LinearMap.range μ = LinearMap.ker T`. Apply `Submodule.eq_of_le_of_finrank_eq hle` to reduce the goal to its premises. Unfold `dimHar dimPol at hrn`. Rewrite `hrn` using `[if_neg (by omega)]`. Simplify using `only [Nat.add_sub_cancel] at hrn`.

Establish `hkle : Module.finrank R.Kf (LinearMap.ker T) ≤ (a + 1 + (m + 1)).choose (m + 1) * (b + 1 + (m + 1)).choose (m + 1)` using `by omega`. Use linear arithmetic over natural numbers and integers. Rewrite `hfk` using `[← heq]`. Take `⟨G, hG⟩` from `hfk`. Conclude with `⟨G, G.2, (congrArg Subtype.val hG).symm⟩`.
-/
theorem tie4 (D : Formalism.BasicNotions.D7) (h3 : Formalism.MainNotions.ColumnSystems.adm3 D) (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hCO : CartanOnto) {p n' : ℕ}
    (R : RS p n') (m : ℕ) (hm : 1 ≤ m) (a b : ℕ) :
    ∀ f ∈ PolAB R.Kf (m + 1) a b, deltaB R.Kf m (PsiXY R.Kf m f) = 0 →
      ∃ G ∈ PolAB R.Kf (m + 1) (a - 1) (b - 1), f = hXY R.Kf (m + 1) * G := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have : CharZero R.Kf := R.charZero
  have hfin : Module.Finite R.Kf (PolAB R.Kf (m + 1 + 1) a b) := Har2.finite_polAB (m + 1) a b
  set T := (dPsi R.Kf (m + 1)).domRestrict (PolAB R.Kf (m + 1 + 1) a b) with hT
  have hrange : LinearMap.range T = dualWeyl R.Kf (m + 1 + 1) (m + 1 + 1) (nuOf (wtPQ (m + 1) a b)) := by
    rw [hT, LinearMap.range_domRestrict]
    exact tie3 h2 h5 hCO R (m + 1) hm a b
  have hrn := LinearMap.finrank_range_add_finrank_ker T
  rw [hrange, finrank_wtPQ D h3 R.Kf m a b, Har2.finrank_polAB] at hrn
  intro f hf hf0
  have hfk : (⟨f, hf⟩ : PolAB R.Kf (m + 1 + 1) a b) ∈ LinearMap.ker T := hf0
  by_cases hab : a = 0 ∨ b = 0
  · have hk0 : Module.finrank R.Kf (LinearMap.ker T) = 0 := by
      unfold dimHar dimPol at hrn
      rw [if_pos hab] at hrn
      omega
    have hbot : LinearMap.ker T = ⊥ := Submodule.finrank_eq_zero.1 hk0
    rw [hbot, Submodule.mem_bot] at hfk
    have hf00 : f = 0 := congrArg Subtype.val hfk
    exact ⟨0, Submodule.zero_mem _, by rw [hf00, mul_zero]⟩
  · rw [not_or] at hab
    obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    let μ : PolAB R.Kf (m + 1 + 1) a b →ₗ[R.Kf] PolAB R.Kf (m + 1 + 1) (a + 1) (b + 1) :=
      LinearMap.codRestrict _ ((LinearMap.mulLeft R.Kf (hXY R.Kf (m + 1 + 1))) ∘ₗ (PolAB R.Kf (m + 1 + 1) a b).subtype)
        (fun G => Har2.h_mul_mem G.2)
    have hμinj : Function.Injective μ := by
      intro G G' h
      have h' : hXY R.Kf (m + 1 + 1) * (G : PolXY R.Kf (m + 1 + 1)) = hXY R.Kf (m + 1 + 1) * G' :=
        congrArg Subtype.val h
      exact Subtype.ext (mul_left_cancel₀ (hXY_ne_zero R.Kf (m + 1)) h')
    have hle : LinearMap.range μ ≤ LinearMap.ker T := by
      rintro _ ⟨G, rfl⟩
      show deltaB R.Kf (m + 1) (PsiXY R.Kf (m + 1) (hXY R.Kf (m + 1 + 1) * (G : PolXY R.Kf (m + 1 + 1)))) = 0
      rw [map_mul, map_mul, delta_Psi_h R.Kf (m + 1) hm, zero_mul]
    have hr : Module.finrank R.Kf (LinearMap.range μ) = (a + (m + 1)).choose (m + 1) * (b + (m + 1)).choose (m + 1) := by
      rw [LinearMap.finrank_range_of_inj hμinj, Har2.finrank_polAB]
    have hle2 := Submodule.finrank_mono hle
    have heq : LinearMap.range μ = LinearMap.ker T := by
      apply Submodule.eq_of_le_of_finrank_eq hle
      unfold dimHar dimPol at hrn
      rw [if_neg (by omega)] at hrn
      simp only [Nat.add_sub_cancel] at hrn
      have hkle : Module.finrank R.Kf (LinearMap.ker T) ≤
          (a + 1 + (m + 1)).choose (m + 1) * (b + 1 + (m + 1)).choose (m + 1) := by omega
      omega
    rw [← heq] at hfk
    obtain ⟨G, hG⟩ := hfk
    exact ⟨G, G.2, (congrArg Subtype.val hG).symm⟩

/- English proof (translation)
Introduce `p n' R m hm`. Establish `hm1 : 1 ≤ m` using `by omega`. Use `⟨h1 R.Kf m hm1, h2 R.Kf m hm1, ?_, tie4 D h3 h2 h5 hCO R m hm1, ?_⟩` and prove the remaining obligations. Introduce `a b y`. Rewrite using `[← tie3 h2 h5 hCO R m hm1 a b]`.

Conclude with `Submodule.mem_map`. Introduce and unpack `Λ ⟨g, hg, rfl⟩`. Establish `hgi : IsUnit (g⁻¹).det` using `Matrix.isUnit_nonsing_inv_det g hg`. Use `⟨Matrix.GeneralLinearGroup.mk'' g⁻¹ hgi, ?_, ?_⟩` and prove the remaining obligations. Introduce `P Q f hf`.

Conclude with `h5 p n' R m hm1 g hg _ rfl P Q f hf`. Introduce `a b y`. Conclude with `tie5b h2 h5 hCO R m hm1 g hg _ rfl a b y`.
-/
theorem tiePsi_of (D : Formalism.BasicNotions.D7) (h1 : ExplicitMapInjective) (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hCO : CartanOnto)
    (h3 : Formalism.MainNotions.ColumnSystems.adm3 D) : TiePsi := by
  intro p n' R m hm
  have hm1 : 1 ≤ m := by omega
  refine ⟨h1 R.Kf m hm1, h2 R.Kf m hm1, ?_, tie4 D h3 h2 h5 hCO R m hm1, ?_⟩
  · intro a b y
    rw [← tie3 h2 h5 hCO R m hm1 a b]
    exact Submodule.mem_map
  · rintro Λ ⟨g, hg, rfl⟩
    have hgi : IsUnit (g⁻¹).det := Matrix.isUnit_nonsing_inv_det g hg
    refine ⟨Matrix.GeneralLinearGroup.mk'' g⁻¹ hgi, ?_, ?_⟩
    · intro P Q f hf
      exact h5 p n' R m hm1 g hg _ rfl P Q f hf
    · intro a b y
      exact tie5b h2 h5 hCO R m hm1 g hg _ rfl a b y

end Formalism.MainNotions.flipOneThree.Pf

end
