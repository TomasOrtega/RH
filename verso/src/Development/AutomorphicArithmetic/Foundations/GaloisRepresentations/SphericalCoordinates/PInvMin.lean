import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

/- English proof (translation)
Set `S : Subalgebra K A` to `Algebra.adjoin K {(u : A), ↑u⁻¹}`. Use `letI : CommRing S := Algebra.adjoinCommRingOfComm K (by`. Introduce `a ha b hb`. Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb`. Apply the tactic sequence `rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp)`.

Set `x : S` to `⟨u, Algebra.subset_adjoin (by simp)⟩`. Set `y : S` to `⟨↑u⁻¹, Algebra.subset_adjoin (by simp)⟩`. Use `letI : Invertible x := ⟨y, Subtype.ext (by simp [x, y]), Subtype.ext (by simp [x, y])⟩`. Establish `key` using `Polynomial.eval₂_reverse_eq_zero_iff (algebraMap K S) x f`. Establish `h1 : Polynomial.aeval (↑u⁻¹ : A) f.reverse = S.val (Polynomial.aeval y f.reverse)` using `Polynomial.aeval_algHom_apply S.val y f.reverse`.

Establish `h2 : Polynomial.aeval (u : A) f = S.val (Polynomial.aeval x f)` using `Polynomial.aeval_algHom_apply S.val x f`. Rewrite using `[h1, h2, map_eq_zero_iff S.val Subtype.val_injective, map_eq_zero_iff S.val Subtype.val_injective, Polynomial.aeval_def, Polynomial.aeval_def]`. Conclude with `key`.
-/
private theorem aeval_inv_reverse_eq_zero_iff {K A : Type} [Field K] [Ring A] [Algebra K A] (u : Aˣ) (f : K[X]) :
    Polynomial.aeval (↑u⁻¹ : A) f.reverse = 0 ↔ Polynomial.aeval (u : A) f = 0 := by
  let S : Subalgebra K A := Algebra.adjoin K {(u : A), ↑u⁻¹}
  letI : CommRing S := Algebra.adjoinCommRingOfComm K (by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp)
  let x : S := ⟨u, Algebra.subset_adjoin (by simp)⟩
  let y : S := ⟨↑u⁻¹, Algebra.subset_adjoin (by simp)⟩
  letI : Invertible x := ⟨y, Subtype.ext (by simp [x, y]), Subtype.ext (by simp [x, y])⟩
  have key := Polynomial.eval₂_reverse_eq_zero_iff (algebraMap K S) x f
  have h1 : Polynomial.aeval (↑u⁻¹ : A) f.reverse = S.val (Polynomial.aeval y f.reverse) :=
    Polynomial.aeval_algHom_apply S.val y f.reverse
  have h2 : Polynomial.aeval (u : A) f = S.val (Polynomial.aeval x f) :=
    Polynomial.aeval_algHom_apply S.val x f
  rw [h1, h2, map_eq_zero_iff S.val Subtype.val_injective, map_eq_zero_iff S.val Subtype.val_injective,
    Polynomial.aeval_def, Polynomial.aeval_def]
  exact key

/- English proof (translation)
Introduce `r hr`. Take `⟨s, hs⟩` from `hr`. Establish `hf : f = r.mirror * r.mirror * s.mirror`. Rewrite using `[← Polynomial.mirror_mul_of_domain, ← Polynomial.mirror_mul_of_domain, ← hs, Polynomial.mirror_mirror]`. Establish `hu : IsUnit r.mirror` using `h _ ⟨_, hf⟩`.

Establish `hr0 : r ≠ 0`. Introduce and unpack `rfl`. Rewrite `hu` using `[Polynomial.mirror_zero]`. Conclude with `not_isUnit_zero hu`. Rewrite `hu`, the goal using `[Polynomial.isUnit_iff_degree_eq_zero]`.

Rewrite using `[Polynomial.degree_eq_natDegree hr0]`. Rewrite `hu` using `[Polynomial.degree_eq_natDegree (Polynomial.mirror_eq_zero.not.mpr hr0), Polynomial.mirror_natDegree]`. Conclude with `hu`.
-/
private theorem squarefree_mirror {F : Type} [Field F] (f : F[X]) (h : Squarefree f) :
    Squarefree f.mirror := by
  intro r hr
  obtain ⟨s, hs⟩ := hr
  have hf : f = r.mirror * r.mirror * s.mirror := by
    rw [← Polynomial.mirror_mul_of_domain, ← Polynomial.mirror_mul_of_domain, ← hs,
      Polynomial.mirror_mirror]
  have hu : IsUnit r.mirror := h _ ⟨_, hf⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Polynomial.mirror_zero] at hu
    exact not_isUnit_zero hu
  rw [Polynomial.isUnit_iff_degree_eq_zero] at hu ⊢
  rw [Polynomial.degree_eq_natDegree hr0]
  rw [Polynomial.degree_eq_natDegree (Polynomial.mirror_eq_zero.not.mpr hr0),
    Polynomial.mirror_natDegree] at hu
  exact hu

/- English proof (translation)
Rewrite using `[← Polynomial.separable_map (algebraMap K (AlgebraicClosure K))]`. Establish `hm : (f.reverse).map (algebraMap K (AlgebraicClosure K)) = (f.map (algebraMap K (AlgebraicClosure K))).mirror`. Establish `htd : (f.map (algebraMap K (AlgebraicClosure K))).natTrailingDegree = 0` using `Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr (by rw [Polynomial.coeff_map]; exact (_root_.map_ne_zero _).mpr h0))`. Rewrite using `[Polynomial.mirror, htd, pow_zero, _root_.mul_one]`. Simplify using `only [Polynomial.reverse, Polynomial.natDegree_map, Polynomial.reflect_map]`.

Rewrite using `[hm, PerfectField.separable_iff_squarefree]`. Conclude with `squarefree_mirror _ ((Polynomial.separable_map _).mpr hs).squarefree`.
-/
private theorem separable_reverse_of_coeff_zero_ne_zero {K : Type} [Field K] (f : K[X]) (h0 : f.coeff 0 ≠ 0)
    (hs : f.Separable) : f.reverse.Separable := by
  rw [← Polynomial.separable_map (algebraMap K (AlgebraicClosure K))]
  have hm : (f.reverse).map (algebraMap K (AlgebraicClosure K)) =
      (f.map (algebraMap K (AlgebraicClosure K))).mirror := by
    have htd : (f.map (algebraMap K (AlgebraicClosure K))).natTrailingDegree = 0 :=
      Polynomial.natTrailingDegree_eq_zero.mpr
        (Or.inr (by rw [Polynomial.coeff_map]; exact (_root_.map_ne_zero _).mpr h0))
    rw [Polynomial.mirror, htd, pow_zero, _root_.mul_one]
    simp only [Polynomial.reverse, Polynomial.natDegree_map, Polynomial.reflect_map]
  rw [hm, PerfectField.separable_iff_squarefree]
  exact squarefree_mirror _ ((Polynomial.separable_map _).mpr hs).squarefree

/- English proof (translation)
Introduce `K A _ _ _ _ _ u`. Establish `hint : ∀ v : Aˣ, IsIntegral K (v : A)` using `fun v => .of_finite K _`. Establish `hc : ∀ v : Aˣ, (minpoly K (v : A)).coeff 0 ≠ 0`. Introduce `v h0`. Take `⟨q, hq⟩` from `Polynomial.X_dvd_iff.mpr h0`.

Establish `hne` using `minpoly.ne_zero (hint v)`. Establish `hq0 : q ≠ 0`. Introduce and unpack `rfl`. Rewrite `hq` using `[mul_zero]`. Conclude with `hne hq`.

Establish `hev : Polynomial.aeval (v : A) q = 0`. Use `minpoly.aeval K (v : A)` as an intermediate fact. Rewrite `this` using `[hq, map_mul, Polynomial.aeval_X]`. Simplify using `using congrArg (fun z => (↑v⁻¹ : A) * z) this`. Establish `hdeg` using `minpoly.degree_le_of_ne_zero K (v : A) hq0 hev`.

Establish `h2` using `Polynomial.natDegree_le_natDegree hdeg`. Rewrite `h2` using `[hq, Polynomial.natDegree_X_mul hq0]`. Use linear arithmetic over natural numbers and integers. Use `set p := minpoly K (u : A) with hp`. Establish `htd : p.natTrailingDegree = 0` using `Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr (hc u))`.

Establish `hdegrev : p.reverse.natDegree = p.natDegree`. Rewrite using `[Polynomial.reverse_natDegree, htd, Nat.sub_zero]`. Establish `hinvMonic : (invPoly p).Monic` using `by show (Polynomial.C (p.coeff 0)⁻¹ * p.reverse).leadingCoeff = 1`. Rewrite using `[Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, Polynomial.reverse_leadingCoeff, Polynomial.trailingCoeff_eq_coeff_zero (hc u), inv_mul_cancel₀ (hc u)]`. Establish `hinvDeg : (invPoly p).natDegree = p.natDegree` using `by show (Polynomial.C (p.coeff 0)⁻¹ * p.reverse).natDegree = _`.

Rewrite using `[Polynomial.natDegree_C_mul (inv_ne_zero (hc u)), hdegrev]`. Establish `hinvEval : Polynomial.aeval (↑u⁻¹ : A) (invPoly p) = 0` using `by show Polynomial.aeval (↑u⁻¹ : A) (Polynomial.C (p.coeff 0)⁻¹ * p.reverse) = 0`. Rewrite using `[map_mul, (aeval_inv_reverse_eq_zero_iff u p).mpr (minpoly.aeval K _), mul_zero]`. Establish `heq : minpoly K (↑u⁻¹ : A) = invPoly p`. Use `(minpoly.unique K _ hinvMonic hinvEval ?_).symm` and prove the remaining obligations.

Introduce `q hqm hqe`. Establish `hq0 : q ≠ 0` using `hqm.ne_zero`. Establish `h1 : Polynomial.aeval (u : A) q.reverse = 0`. Use `(aeval_inv_reverse_eq_zero_iff u⁻¹ q).mpr hqe` as an intermediate fact. Simplify using `using this`.

Establish `h2` using `minpoly.degree_le_of_ne_zero K (u : A) (mt Polynomial.reverse_eq_zero.mp hq0) h1`. Establish `h3` using `Polynomial.natDegree_le_natDegree h2`. Establish `h4` using `Polynomial.reverse_natDegree_le q`. Rewrite using `[Polynomial.degree_eq_natDegree hinvMonic.ne_zero, Polynomial.degree_eq_natDegree hq0, hinvDeg]`. Conclude with `h3.trans h4` after adjusting the coercions.

Use `⟨heq, by rw [heq, hinvDeg], fun hs => ?_⟩` and prove the remaining obligations. Rewrite using `[heq]`. Establish `hrev : p.reverse.Separable` using `separable_reverse_of_coeff_zero_ne_zero p (hc u) hs`. Use `hrev.of_dvd ⟨Polynomial.C (p.coeff 0), ?_⟩` and prove the remaining obligations. Use `show p.reverse = Polynomial.C (p.coeff 0)⁻¹ * p.reverse * Polynomial.C (p.coeff 0)`.

Rewrite using `[_root_.mul_comm, ← _root_.mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ (hc u), Polynomial.C_1, _root_.one_mul]`.
-/
theorem UpperTheory.Gal.W2.invMin_of :
    UpperTheory.Gal.W2.InvMin := by
  intro K A _ _ _ _ _ u
  have hint : ∀ v : Aˣ, IsIntegral K (v : A) := fun v => .of_finite K _
  have hc : ∀ v : Aˣ, (minpoly K (v : A)).coeff 0 ≠ 0 := by
    intro v h0
    obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr h0
    have hne := minpoly.ne_zero (hint v)
    have hq0 : q ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hq
      exact hne hq
    have hev : Polynomial.aeval (v : A) q = 0 := by
      have := minpoly.aeval K (v : A)
      rw [hq, map_mul, Polynomial.aeval_X] at this
      simpa using congrArg (fun z => (↑v⁻¹ : A) * z) this
    have hdeg := minpoly.degree_le_of_ne_zero K (v : A) hq0 hev
    have h2 := Polynomial.natDegree_le_natDegree hdeg
    rw [hq, Polynomial.natDegree_X_mul hq0] at h2
    omega
  set p := minpoly K (u : A) with hp
  have htd : p.natTrailingDegree = 0 := Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr (hc u))
  have hdegrev : p.reverse.natDegree = p.natDegree := by
    rw [Polynomial.reverse_natDegree, htd, Nat.sub_zero]
  have hinvMonic : (invPoly p).Monic := by
    show (Polynomial.C (p.coeff 0)⁻¹ * p.reverse).leadingCoeff = 1
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, Polynomial.reverse_leadingCoeff,
      Polynomial.trailingCoeff_eq_coeff_zero (hc u), inv_mul_cancel₀ (hc u)]
  have hinvDeg : (invPoly p).natDegree = p.natDegree := by
    show (Polynomial.C (p.coeff 0)⁻¹ * p.reverse).natDegree = _
    rw [Polynomial.natDegree_C_mul (inv_ne_zero (hc u)), hdegrev]
  have hinvEval : Polynomial.aeval (↑u⁻¹ : A) (invPoly p) = 0 := by
    show Polynomial.aeval (↑u⁻¹ : A) (Polynomial.C (p.coeff 0)⁻¹ * p.reverse) = 0
    rw [map_mul, (aeval_inv_reverse_eq_zero_iff u p).mpr (minpoly.aeval K _), mul_zero]
  have heq : minpoly K (↑u⁻¹ : A) = invPoly p := by
    refine (minpoly.unique K _ hinvMonic hinvEval ?_).symm
    intro q hqm hqe
    have hq0 : q ≠ 0 := hqm.ne_zero
    have h1 : Polynomial.aeval (u : A) q.reverse = 0 := by
      have := (aeval_inv_reverse_eq_zero_iff u⁻¹ q).mpr hqe
      simpa using this
    have h2 := minpoly.degree_le_of_ne_zero K (u : A) (mt Polynomial.reverse_eq_zero.mp hq0) h1
    have h3 := Polynomial.natDegree_le_natDegree h2
    have h4 := Polynomial.reverse_natDegree_le q
    rw [Polynomial.degree_eq_natDegree hinvMonic.ne_zero, Polynomial.degree_eq_natDegree hq0, hinvDeg]
    exact_mod_cast h3.trans h4
  refine ⟨heq, by rw [heq, hinvDeg], fun hs => ?_⟩
  rw [heq]
  have hrev : p.reverse.Separable := separable_reverse_of_coeff_zero_ne_zero p (hc u) hs
  refine hrev.of_dvd ⟨Polynomial.C (p.coeff 0), ?_⟩
  show p.reverse = Polynomial.C (p.coeff 0)⁻¹ * p.reverse * Polynomial.C (p.coeff 0)
  rw [_root_.mul_comm, ← _root_.mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ (hc u),
    Polynomial.C_1, _root_.one_mul]
