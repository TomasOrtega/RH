import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompactPreimageNormCentralizerHermitianStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology Polynomial

noncomputable section
namespace GlobalTheory.OrbCpt

variable {k : Type} [NontriviallyNormedField k] {r : ℕ}

noncomputable def gsum (X Y : Matrix (Fin r) (Fin r) k) : ℕ → Matrix (Fin r) (Fin r) k
  | 0 => 0
  | m + 1 => X ^ m + gsum X Y m * Y

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [gsum]`. Consider the case `succ m ih`. Establish `h : X * gsum X Y m = gsum X Y m * Y + (X ^ m - Y ^ m)` using `by rw [← ih]; abel`. Simplify using `only [gsum, mul_add, add_mul, ← mul_assoc, h]`.

Rewrite using `[pow_succ' X m, pow_succ Y m]`. Use `noncomm_ring`.
-/
theorem gsum_inter (X Y : Matrix (Fin r) (Fin r) k) (m : ℕ) :
    X * gsum X Y m - gsum X Y m * Y = X ^ m - Y ^ m := by
  induction m with
  | zero => simp [gsum]
  | succ m ih =>
    have h : X * gsum X Y m = gsum X Y m * Y + (X ^ m - Y ^ m) := by rw [← ih]; abel
    simp only [gsum, mul_add, add_mul, ← mul_assoc, h]
    rw [pow_succ' X m, pow_succ Y m]
    noncomm_ring

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [gsum]`. Consider the case `succ m ih`. Rewrite using `[gsum, ih, smul_mul_assoc, ← pow_succ, Nat.cast_succ (m + 1), add_smul, one_smul, add_comm]`.
-/
theorem gsum_self (X : Matrix (Fin r) (Fin r) k) (m : ℕ) :
    gsum X X (m + 1) = ((m + 1 : ℕ) : k) • X ^ m := by
  induction m with
  | zero => simp [gsum]
  | succ m ih =>
    rw [gsum, ih, smul_mul_assoc, ← pow_succ, Nat.cast_succ (m + 1), add_smul, one_smul, add_comm]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa [gsum] using continuous_const`. Consider the case `succ m ih => simp only [gsum]`. Use `fun_prop`.
-/
theorem continuous_gsum (m : ℕ) :
    Continuous fun q : Matrix (Fin r) (Fin r) k × Matrix (Fin r) (Fin r) k => gsum q.1 q.2 m := by
  induction m with
  | zero => simpa [gsum] using continuous_const
  | succ m ih => simp only [gsum]; fun_prop

def hm (p : k[X]) (X Y : Matrix (Fin r) (Fin r) k) : Matrix (Fin r) (Fin r) k :=
  ∑ m ∈ Finset.range (p.natDegree + 2), p.coeff m • gsum X Y m

/- English proof (translation)
Establish `h1 : p.natDegree < p.natDegree + 2` using `by omega`. Rewrite using `[aeval_eq_sum_range' h1, aeval_eq_sum_range' h1, hm, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, smul_mul_assoc, ← smul_sub, gsum_inter, smul_sub]`.
-/
theorem hm_inter (p : k[X]) (X Y : Matrix (Fin r) (Fin r) k) :
    X * hm p X Y - hm p X Y * Y = aeval X p - aeval Y p := by
  have h1 : p.natDegree < p.natDegree + 2 := by omega
  rw [aeval_eq_sum_range' h1, aeval_eq_sum_range' h1, hm, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, gsum_inter, smul_sub]

/- English proof (translation)
Establish `h1 : (derivative p).natDegree < p.natDegree + 1` using `lt_of_le_of_lt (natDegree_derivative_le p) (by omega)`. Rewrite using `[aeval_eq_sum_range' h1, hm, Finset.sum_range_succ', show gsum X X 0 = 0 from rfl, smul_zero, add_zero]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[gsum_self, coeff_derivative, smul_smul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hm_self (p : k[X]) (X : Matrix (Fin r) (Fin r) k) :
    hm p X X = aeval X (derivative p) := by
  have h1 : (derivative p).natDegree < p.natDegree + 1 :=
    lt_of_le_of_lt (natDegree_derivative_le p) (by omega)
  rw [aeval_eq_sum_range' h1, hm, Finset.sum_range_succ', show gsum X X 0 = 0 from rfl, smul_zero,
    add_zero]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [gsum_self, coeff_derivative, smul_smul]
  congr 1; push_cast; ring

/- English proof (translation)
Unfold `hm`. Conclude with `continuous_finsetSum _ fun m _ => (continuous_const_smul (p.coeff m)).comp (continuous_gsum m)`.
-/
theorem continuous_hm (p : k[X]) :
    Continuous fun q : Matrix (Fin r) (Fin r) k × Matrix (Fin r) (Fin r) k => hm p q.1 q.2 := by
  unfold hm
  exact continuous_finsetSum _ fun m _ =>
    (continuous_const_smul (p.coeff m)).comp (continuous_gsum m)

/- English proof (translation)
Take `⟨u, v, huv⟩` from `hp`. Establish `h` using `congrArg (aeval X) huv`. Rewrite `h` using `[map_add, map_mul, map_mul, hX, mul_zero, zero_add, map_one]`. Rewrite using `[hm_self]`. Conclude with `(Matrix.isUnit_det_of_left_inverse h).ne_zero`.
-/
theorem det_hm_self_ne_zero {p : k[X]} (hp : p.Separable) {X : Matrix (Fin r) (Fin r) k}
    (hX : aeval X p = 0) : (hm p X X).det ≠ 0 := by
  obtain ⟨u, v, huv⟩ := hp
  have h := congrArg (aeval X) huv
  rw [map_add, map_mul, map_mul, hX, mul_zero, zero_add, map_one] at h
  rw [hm_self]
  exact (Matrix.isUnit_det_of_left_inverse h).ne_zero

end GlobalTheory.OrbCpt

noncomputable section
namespace GlobalTheory.OrbCpt

variable {k : Type} [NontriviallyNormedField k] {r : ℕ}

/- English proof (translation)
Use `haveI : CompactSpace P := isCompact_iff_compactSpace.mp hP`. Set `φ : P → GL (Fin r) k` to `fun x => ⟨f x, (f x)⁻¹, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hdet x x.2)), Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet x x.2))⟩`. Establish `hφ : Continuous φ`. Rewrite using `[Units.continuous_iff]`. Use `⟨hf.comp continuous_subtype_val, ?_⟩` and prove the remaining obligations.

Use `show Continuous fun x : P => (f x)⁻¹`. Establish `: (fun x : P => (f x)⁻¹) = fun x : P => ((f x).det)⁻¹ • (f x).adjugate`. Use function extensionality and compare the values at `x`. Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv']`. Rewrite using `[this]`.

Conclude with `((hf.comp continuous_subtype_val).matrix_det.inv₀ fun x => hdet x.1 x.2).smul (hf.comp continuous_subtype_val).matrix_adjugate`. Conclude with `⟨Set.range φ, isCompact_range hφ, fun x hx => ⟨φ ⟨x, hx⟩, ⟨_, rfl⟩, rfl⟩⟩`.
-/
theorem isCompact_units_image {X : Type} [TopologicalSpace X] {P : Set X} (hP : IsCompact P)
    {f : X → Matrix (Fin r) (Fin r) k} (hf : Continuous f) (hdet : ∀ x ∈ P, (f x).det ≠ 0) :
    ∃ C : Set (GL (Fin r) k), IsCompact C ∧
      ∀ x ∈ P, ∃ c ∈ C, (c : Matrix (Fin r) (Fin r) k) = f x := by
  classical
  haveI : CompactSpace P := isCompact_iff_compactSpace.mp hP
  let φ : P → GL (Fin r) k := fun x =>
    ⟨f x, (f x)⁻¹, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hdet x x.2)),
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet x x.2))⟩
  have hφ : Continuous φ := by
    rw [Units.continuous_iff]
    refine ⟨hf.comp continuous_subtype_val, ?_⟩
    show Continuous fun x : P => (f x)⁻¹
    have : (fun x : P => (f x)⁻¹) = fun x : P => ((f x).det)⁻¹ • (f x).adjugate := by
      funext x; rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [this]
    exact ((hf.comp continuous_subtype_val).matrix_det.inv₀ fun x => hdet x.1 x.2).smul
      (hf.comp continuous_subtype_val).matrix_adjugate
  exact ⟨Set.range φ, isCompact_range hφ, fun x hx => ⟨φ ⟨x, hx⟩, ⟨_, rfl⟩, rfl⟩⟩

/- English proof (translation)
Take `⟨p, hp⟩ : ∃ p, p = A₀.charpoly` from `⟨_, rfl⟩`. Rewrite `hs` using `[← hp]`. Take `⟨cj, hcjdef⟩ : ∃ cj : GL (Fin r) k → Matrix (Fin r) (Fin r) k, ∀ g, cj g = (g : Matrix (Fin r) (Fin r) k) * A₀ * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k)` from `⟨_, fun _ => rfl⟩`. Simplify using `only [← hcjdef]`. Establish `hcj : ∀ g, aeval (cj g) p = 0`.

Introduce `g`. Establish `: (cj g).charpoly = p`. Rewrite using `[hcjdef, Matrix.coe_units_inv, Matrix.charpoly_units_conj, hp]`. Rewrite using `[← this]`. Conclude with `Matrix.aeval_self_charpoly _`.

Establish `hint : ∀ g h : GL (Fin r) k, cj g * (hm p (cj g) (cj h) * (h : Matrix (Fin r) (Fin r) k)) = (hm p (cj g) (cj h) * (h : Matrix (Fin r) (Fin r) k)) * A₀`. Introduce `g h`. Establish `e` using `hm_inter p (cj g) (cj h)`. Rewrite `e` using `[hcj, hcj, sub_zero, sub_eq_zero]`. Establish `e2 : cj h * (h : Matrix (Fin r) (Fin r) k) = h * A₀`.

Rewrite using `[hcjdef]`. Simplify using `only [mul_assoc, Units.inv_mul, mul_one]`. Rewrite using `[← mul_assoc, e, mul_assoc, e2, mul_assoc]`. Take `⟨D, hDdef⟩ : ∃ D : Matrix (Fin r) (Fin r) k → Matrix (Fin r) (Fin r) k → k, ∀ X Y, D X Y = (hm p X Y).det` from `⟨_, fun _ _ => rfl⟩`. Establish `hD : Continuous fun q : Matrix (Fin r) (Fin r) k × Matrix (Fin r) (Fin r) k => D q.1 q.2`.

Simplify using `only [hDdef]`. Conclude with `(continuous_hm p).matrix_det`. Establish `hD1 : ∀ Y, Continuous fun X => D X Y` using `fun Y => hD.comp (continuous_id.prodMk continuous_const)`. Establish `hD2 : ∀ X, Continuous fun Y => D X Y` using `fun X => hD.comp (continuous_const.prodMk continuous_id)`. Use `set K := closure (Z ∩ Set.range cj) with hKdef`.

Establish `hK : IsCompact K` using `hZ.closure_of_subset Set.inter_subset_left`. Establish `hKp : ∀ X ∈ K, aeval X p = 0`. Establish `hc : IsClosed {X : Matrix (Fin r) (Fin r) k | aeval X p = 0}` using `isClosed_eq (Polynomial.continuous_aeval p) continuous_const`. Introduce `X hX`. Conclude with `(closure_minimal (fun Y hY => by obtain ⟨g, rfl⟩ := hY.2; exact hcj g) hc) hX`.

Establish `hcover : K ⊆ ⋃ g : {g : GL (Fin r) k // cj g ∈ Z}, {X | D X (cj g.1) ≠ 0}`. Introduce `X hX`. Establish `h0 : D X X ≠ 0` using `by rw [hDdef]; exact det_hm_self_ne_zero hs (hKp X hX)`. Establish `hnb : {Y | D X Y ≠ 0} ∈ 𝓝 X` using `(isOpen_ne_fun (hD2 X) continuous_const).mem_nhds h0`. Take `⟨Y, hY1, hY2, ⟨g, rfl⟩⟩` from `mem_closure_iff_nhds.mp hX _ hnb`.

Conclude with `Set.mem_iUnion.mpr ⟨⟨g, hY2⟩, hY1⟩`. Take `⟨s, hs'⟩` from `hK.elim_finite_subcover _ (fun g => isOpen_ne_fun (hD1 _) continuous_const) hcover`. Take `⟨ψ, hψdef⟩ : ∃ ψ : Matrix (Fin r) (Fin r) k → ℝ, ∀ X, ψ X = ∑ g ∈ s, ‖D X (cj g.1)‖` from `⟨_, fun _ => rfl⟩`. Establish `hψ : Continuous ψ`. Establish `: ψ = fun X => ∑ g ∈ s, ‖D X (cj g.1)‖` using `funext hψdef`.

Rewrite using `[this]`. Conclude with `continuous_finsetSum _ fun g _ => (hD1 _).norm`. Establish `hψpos : ∀ X ∈ K, 0 < ψ X`. Introduce `X hX`. Take `⟨g, hg, hgX⟩` from `Set.mem_iUnion₂.mp (hs' hX)`.

Establish `hgX' : D X (cj g.1) ≠ 0` using `hgX`. Establish `h1 : 0 < ‖D X (cj g.1)‖` using `norm_pos_iff.mpr hgX'`. Establish `h2 : ‖D X (cj g.1)‖ ≤ ∑ g ∈ s, ‖D X (cj g.1)‖` using `Finset.single_le_sum (f := fun i : {g : GL (Fin r) k // cj g ∈ Z} => ‖D X (cj i.1)‖) (fun (i : {g : GL (Fin r) k // cj g ∈ Z}) _ => norm_nonneg (D X (cj i.1))) hg`. Rewrite using `[hψdef]`. Conclude with `lt_of_lt_of_le h1 h2`.

Break down `K.eq_empty_or_nonempty with hKe | hKne` into its components or cases. Use `⟨∅, isCompact_empty, fun g hg => ?_⟩` and prove the remaining obligations. Establish `: cj g ∈ K` using `subset_closure ⟨hg, g, rfl⟩`. Rewrite `this` using `[hKe]`. Conclude with `absurd this (Set.notMem_empty _)`.

Take `⟨x0, hx0, hmin⟩` from `hK.exists_isMinOn hKne hψ.continuousOn`. Use `set δ := ψ x0 / ((s.card : ℝ) + 1) with hδdef`. Establish `hδ : 0 < δ` using `div_pos (hψpos x0 hx0) (by positivity)`. Establish `hpiece : ∀ X ∈ K, ∃ g ∈ s, δ ≤ ‖D X (cj g.1)‖`. Introduce `X hX`.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `h1 : ψ X ≤ ∑ g ∈ s, δ` using `by rw [hψdef]; exact Finset.sum_le_sum fun g hg => (hcon g hg).le`. Rewrite `h1` using `[Finset.sum_const, nsmul_eq_mul]`. Establish `h2 : ψ x0 ≤ ψ X` using `hmin hX`.

Establish `hq` using `hψpos x0 hx0`. Establish `h3 : (s.card : ℝ) * δ < ψ x0`. Rewrite using `[hδdef, mul_div_assoc', div_lt_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hC : ∀ g ∈ s, ∃ C : Set (GL (Fin r) k), IsCompact C ∧ ∀ X ∈ K ∩ {X | δ ≤ ‖D X (cj g.1)‖}, ∃ c ∈ C, (c : Matrix (Fin r) (Fin r) k) = hm p X (cj g.1) * (g.1 : Matrix (Fin r) (Fin r) k)`. Introduce `g _`. Apply `isCompact_units_image (hK.inter_right (isClosed_le continuous_const (hD1 _).norm)) (((continuous_hm p).comp (continuous_id.prodMk continuous_const)).mul continuous_const)` to reduce the goal to its premises. Introduce and unpack `X ⟨_, hX⟩`. Use `show (hm p X (cj g.1) * (g.1 : Matrix (Fin r) (Fin r) k)).det ≠ 0`.

Rewrite using `[Matrix.det_mul, ← hDdef]`. Conclude with `mul_ne_zero (norm_pos_iff.mp (lt_of_lt_of_le hδ hX)) (Matrix.isUnit_det_of_left_inverse (Units.inv_mul g.1)).ne_zero`. Use `choose! Cg hCg hCgm using hC`. Use `⟨⋃ g ∈ s, Cg g, s.isCompact_biUnion hCg, fun g hg => ?_⟩` and prove the remaining obligations. Establish `hgK : cj g ∈ K` using `subset_closure ⟨hg, g, rfl⟩`.

Take `⟨g', hg's, hδg⟩` from `hpiece _ hgK`. Take `⟨c, hcC, hc⟩` from `hCgm g' hg's (cj g) ⟨hgK, hδg⟩`. Use `⟨c, Set.mem_iUnion₂.mpr ⟨g', hg's, hcC⟩, c⁻¹ * g, ?_, by rw [mul_inv_cancel_left]⟩` and prove the remaining obligations. Establish `hi` using `hint g g'.1`. Rewrite `hi` using `[← hc]`.

Establish `hA : A₀ * ((c⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) = ((c⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) * cj g`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc, Units.mul_inv, mul_one]`. Rewrite using `[Units.val_mul, ← mul_assoc, hA]`. Rewrite using `[hcjdef]`.

Simplify using `only [mul_assoc, Units.inv_mul, mul_one]`.
-/
theorem gl_orbit_cpt (A₀ : Matrix (Fin r) (Fin r) k) (hs : A₀.charpoly.Separable)
    (Z : Set (Matrix (Fin r) (Fin r) k)) (hZ : IsCompact Z) :
    ∃ C : Set (GL (Fin r) k), IsCompact C ∧ ∀ g : GL (Fin r) k,
      (g : Matrix (Fin r) (Fin r) k) * A₀ * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) ∈ Z →
      ∃ c ∈ C, ∃ t : GL (Fin r) k,
        (t : Matrix (Fin r) (Fin r) k) * A₀ = A₀ * (t : Matrix (Fin r) (Fin r) k) ∧ g = c * t := by
  classical
  obtain ⟨p, hp⟩ : ∃ p, p = A₀.charpoly := ⟨_, rfl⟩
  rw [← hp] at hs
  obtain ⟨cj, hcjdef⟩ : ∃ cj : GL (Fin r) k → Matrix (Fin r) (Fin r) k, ∀ g, cj g =
      (g : Matrix (Fin r) (Fin r) k) * A₀ * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) :=
    ⟨_, fun _ => rfl⟩
  simp only [← hcjdef]
  have hcj : ∀ g, aeval (cj g) p = 0 := by
    intro g
    have : (cj g).charpoly = p := by
      rw [hcjdef, Matrix.coe_units_inv, Matrix.charpoly_units_conj, hp]
    rw [← this]; exact Matrix.aeval_self_charpoly _
  have hint : ∀ g h : GL (Fin r) k, cj g * (hm p (cj g) (cj h) * (h : Matrix (Fin r) (Fin r) k)) =
      (hm p (cj g) (cj h) * (h : Matrix (Fin r) (Fin r) k)) * A₀ := by
    intro g h
    have e := hm_inter p (cj g) (cj h)
    rw [hcj, hcj, sub_zero, sub_eq_zero] at e
    have e2 : cj h * (h : Matrix (Fin r) (Fin r) k) = h * A₀ := by
      rw [hcjdef]; simp only [mul_assoc, Units.inv_mul, mul_one]
    rw [← mul_assoc, e, mul_assoc, e2, mul_assoc]
  obtain ⟨D, hDdef⟩ : ∃ D : Matrix (Fin r) (Fin r) k → Matrix (Fin r) (Fin r) k → k,
      ∀ X Y, D X Y = (hm p X Y).det := ⟨_, fun _ _ => rfl⟩
  have hD : Continuous fun q : Matrix (Fin r) (Fin r) k × Matrix (Fin r) (Fin r) k => D q.1 q.2 := by
    simp only [hDdef]; exact (continuous_hm p).matrix_det
  have hD1 : ∀ Y, Continuous fun X => D X Y := fun Y =>
    hD.comp (continuous_id.prodMk continuous_const)
  have hD2 : ∀ X, Continuous fun Y => D X Y := fun X =>
    hD.comp (continuous_const.prodMk continuous_id)
  set K := closure (Z ∩ Set.range cj) with hKdef
  have hK : IsCompact K := hZ.closure_of_subset Set.inter_subset_left
  have hKp : ∀ X ∈ K, aeval X p = 0 := by
    have hc : IsClosed {X : Matrix (Fin r) (Fin r) k | aeval X p = 0} :=
      isClosed_eq (Polynomial.continuous_aeval p) continuous_const
    intro X hX
    exact (closure_minimal (fun Y hY => by obtain ⟨g, rfl⟩ := hY.2; exact hcj g) hc) hX
  have hcover : K ⊆ ⋃ g : {g : GL (Fin r) k // cj g ∈ Z}, {X | D X (cj g.1) ≠ 0} := by
    intro X hX
    have h0 : D X X ≠ 0 := by rw [hDdef]; exact det_hm_self_ne_zero hs (hKp X hX)
    have hnb : {Y | D X Y ≠ 0} ∈ 𝓝 X := (isOpen_ne_fun (hD2 X) continuous_const).mem_nhds h0
    obtain ⟨Y, hY1, hY2, ⟨g, rfl⟩⟩ := mem_closure_iff_nhds.mp hX _ hnb
    exact Set.mem_iUnion.mpr ⟨⟨g, hY2⟩, hY1⟩
  obtain ⟨s, hs'⟩ := hK.elim_finite_subcover _
    (fun g => isOpen_ne_fun (hD1 _) continuous_const) hcover
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : Matrix (Fin r) (Fin r) k → ℝ, ∀ X, ψ X = ∑ g ∈ s, ‖D X (cj g.1)‖ :=
    ⟨_, fun _ => rfl⟩
  have hψ : Continuous ψ := by
    have : ψ = fun X => ∑ g ∈ s, ‖D X (cj g.1)‖ := funext hψdef
    rw [this]; exact continuous_finsetSum _ fun g _ => (hD1 _).norm
  have hψpos : ∀ X ∈ K, 0 < ψ X := by
    intro X hX
    obtain ⟨g, hg, hgX⟩ := Set.mem_iUnion₂.mp (hs' hX)
    have hgX' : D X (cj g.1) ≠ 0 := hgX
    have h1 : 0 < ‖D X (cj g.1)‖ := norm_pos_iff.mpr hgX'
    have h2 : ‖D X (cj g.1)‖ ≤ ∑ g ∈ s, ‖D X (cj g.1)‖ :=
      Finset.single_le_sum (f := fun i : {g : GL (Fin r) k // cj g ∈ Z} => ‖D X (cj i.1)‖)
        (fun (i : {g : GL (Fin r) k // cj g ∈ Z}) _ => norm_nonneg (D X (cj i.1))) hg
    rw [hψdef]; exact lt_of_lt_of_le h1 h2
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨∅, isCompact_empty, fun g hg => ?_⟩
    have : cj g ∈ K := subset_closure ⟨hg, g, rfl⟩
    rw [hKe] at this; exact absurd this (Set.notMem_empty _)
  obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn hKne hψ.continuousOn
  set δ := ψ x0 / ((s.card : ℝ) + 1) with hδdef
  have hδ : 0 < δ := div_pos (hψpos x0 hx0) (by positivity)
  have hpiece : ∀ X ∈ K, ∃ g ∈ s, δ ≤ ‖D X (cj g.1)‖ := by
    intro X hX
    by_contra hcon
    push_neg at hcon
    have h1 : ψ X ≤ ∑ g ∈ s, δ := by rw [hψdef]; exact Finset.sum_le_sum fun g hg => (hcon g hg).le
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    have h2 : ψ x0 ≤ ψ X := hmin hX
    have hq := hψpos x0 hx0
    have h3 : (s.card : ℝ) * δ < ψ x0 := by
      rw [hδdef, mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have hC : ∀ g ∈ s, ∃ C : Set (GL (Fin r) k), IsCompact C ∧
      ∀ X ∈ K ∩ {X | δ ≤ ‖D X (cj g.1)‖},
        ∃ c ∈ C, (c : Matrix (Fin r) (Fin r) k) = hm p X (cj g.1) * (g.1 : Matrix (Fin r) (Fin r) k) := by
    intro g _
    apply isCompact_units_image (hK.inter_right (isClosed_le continuous_const (hD1 _).norm))
      (((continuous_hm p).comp (continuous_id.prodMk continuous_const)).mul continuous_const)
    rintro X ⟨_, hX⟩
    show (hm p X (cj g.1) * (g.1 : Matrix (Fin r) (Fin r) k)).det ≠ 0
    rw [Matrix.det_mul, ← hDdef]
    exact mul_ne_zero (norm_pos_iff.mp (lt_of_lt_of_le hδ hX))
      (Matrix.isUnit_det_of_left_inverse (Units.inv_mul g.1)).ne_zero
  choose! Cg hCg hCgm using hC
  refine ⟨⋃ g ∈ s, Cg g, s.isCompact_biUnion hCg, fun g hg => ?_⟩
  have hgK : cj g ∈ K := subset_closure ⟨hg, g, rfl⟩
  obtain ⟨g', hg's, hδg⟩ := hpiece _ hgK
  obtain ⟨c, hcC, hc⟩ := hCgm g' hg's (cj g) ⟨hgK, hδg⟩
  refine ⟨c, Set.mem_iUnion₂.mpr ⟨g', hg's, hcC⟩, c⁻¹ * g, ?_, by rw [mul_inv_cancel_left]⟩
  have hi := hint g g'.1
  rw [← hc] at hi
  have hA : A₀ * ((c⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) =
      ((c⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) * cj g := by
    calc A₀ * ((c⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k)
        = (((c⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) * c) * A₀ *
            ((c⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by rw [Units.inv_mul, one_mul]
      _ = ((c⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) * ((c : Matrix (Fin r) (Fin r) k) * A₀) *
            ((c⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by simp only [mul_assoc]
      _ = ((c⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) * (cj g * c) *
            ((c⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by rw [hi]
      _ = ((c⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) * cj g := by
            simp only [mul_assoc, Units.mul_inv, mul_one]
  rw [Units.val_mul, ← mul_assoc, hA]
  rw [hcjdef]; simp only [mul_assoc, Units.inv_mul, mul_one]

end GlobalTheory.OrbCpt

noncomputable section
namespace GlobalTheory.OrbCpt

/- English proof (translation)
Use `haveI : ContinuousStar E := ⟨by`. Establish `h` using `AddMonoidHomClass.isometry_of_norm (starAddEquiv (R := E)) (fun x => Unram.norm_star (F := F) x)`. Conclude with `h.continuous⟩`. Take `⟨CE, hCE, hCEg⟩` from `gl_orbit_cpt A₀ hs Z hZ`. Set `sU : GL (Fin r) E → GL (Fin r) E` to `fun c => ⟨star (c : Matrix (Fin r) (Fin r) E), star ((c⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E), by rw [← star_mul, Units.inv_mul, star_one], by rw [← star_mul, Units.mul_inv, star_one]⟩`.

Establish `hsU : Continuous sU`. Rewrite using `[Units.continuous_iff]`. Conclude with `⟨continuous_star.comp Units.continuous_val, continuous_star.comp Units.continuous_coe_inv⟩`. Set `M : Set (GL (Fin r) E)` to `(fun c => (sU c * c)⁻¹) '' CE`. Establish `hM : IsCompact M` using `hCE.image ((hsU.mul continuous_id).inv)`.

Take `⟨S, hS, hSt⟩` from `hN F E r A₀ hH hs M hM`. Set `KM : Set (Matrix (Fin r) (Fin r) E)` to `(fun q : GL (Fin r) E × GL (Fin r) E => ((q.1 * q.2 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)) '' (CE ×ˢ S)`. Establish `hKM : IsCompact KM` using `(hCE.prod hS).image (Units.continuous_val.comp continuous_mul)`. Establish `hcl : IsClosed (Matrix.unitaryGroup (Fin r) E : Set (Matrix (Fin r) (Fin r) E))`. Establish `: (Matrix.unitaryGroup (Fin r) E : Set (Matrix (Fin r) (Fin r) E)) = {A | star A * A = 1} ∩ {A | A * star A = 1}`.

Use extensionality with `A`. Conclude with `Unitary.mem_iff`. Rewrite using `[this]`. Conclude with `(isClosed_eq (continuous_star.mul continuous_id) continuous_const).inter (isClosed_eq (continuous_id.mul continuous_star) continuous_const)`. Use `⟨Subtype.val ⁻¹' KM, hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hKM, ?_⟩` and prove the remaining obligations.

Introduce `g hg`. Establish `hg1 : g.1 * star g.1 = 1` using `Matrix.mem_unitaryGroup_iff.mp g.2`. Establish `hg2 : star g.1 * g.1 = 1` using `(Unitary.mem_iff.mp g.2).1`. Set `gU : GL (Fin r) E` to `⟨g.1, star g.1, hg1, hg2⟩`. Take `⟨c, hc, t, ht, hgct⟩` from `hCEg gU hg`.

Use `set cm : Matrix (Fin r) (Fin r) E := (c : Matrix (Fin r) (Fin r) E)`. Use `set ci : Matrix (Fin r) (Fin r) E := ((c⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)`. Establish `htv : (t : Matrix (Fin r) (Fin r) E) = ci * g.1`. Establish `: t = c⁻¹ * gU` using `by rw [hgct, inv_mul_cancel_left]`. Rewrite using `[this, Units.val_mul]`.

Establish `htt : (t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E) = ci * star ci`. Rewrite using `[htv, star_mul, mul_assoc, ← mul_assoc g.1, hg1, one_mul]`. Establish `hmM : (sU c * c)⁻¹ ∈ M` using `⟨c, hc, rfl⟩`. Establish `hmv : (((sU c * c)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) = ci * star ci`. Rewrite using `[_root_.mul_inv_rev, Units.val_mul]`.

Both sides reduce to the same expression. Take `⟨s, hsS, hsA, hss⟩` from `hSt t ht ⟨_, hmM, by rw [htt, hmv]⟩`. Rewrite `hss` using `[htt]`. Use `set sm : Matrix (Fin r) (Fin r) E := (s : Matrix (Fin r) (Fin r) E)`. Use `set si : Matrix (Fin r) (Fin r) E := ((s⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)`.

Establish `hcs : ((c * s : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) ∈ Matrix.unitaryGroup (Fin r) E`. Rewrite using `[Matrix.mem_unitaryGroup_iff, Units.val_mul, star_mul, show cm * sm * (star sm * star cm) = cm * (sm * star sm) * star cm by noncomm_ring, hss, show cm * (ci * star ci) * star cm = (cm * ci) * star (cm * ci) by rw [star_mul]; noncomm_ring, Units.mul_inv, star_one, one_mul]`. Establish `hsi : si * A₀ = A₀ * si`. Combine the equalities or inequalities in the displayed calculation. Establish `hst : ((s⁻¹ * t : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) ∈ Matrix.unitaryGroup (Fin r) E`.

Rewrite using `[Matrix.mem_unitaryGroup_iff, Units.val_mul, star_mul, show si * (t : Matrix (Fin r) (Fin r) E) * (star (t : Matrix (Fin r) (Fin r) E) * star si) = si * ((t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E)) * star si by noncomm_ring, htt, ← hss, show si * (sm * s …`. Use `⟨⟨_, hcs⟩, ⟨(c, s), ⟨hc, hsS⟩, rfl⟩, ⟨_, hst⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show ((s⁻¹ * t : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * A₀ = A₀ * ((s⁻¹ * t : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)`. Rewrite using `[Units.val_mul, mul_assoc, ht, ← mul_assoc, hsi, mul_assoc]`. Apply `Subtype.ext show g.1 = ((c * s : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * ((s⁻¹ * t : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)` to reduce the goal to its premises.

Rewrite using `[← Units.val_mul, mul_assoc, mul_inv_cancel_left, ← hgct]`.
-/
theorem unitary_orbit_cpt (hN : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (A₀ : Matrix (Fin r) (Fin r) E), A₀.IsHermitian → A₀.charpoly.Separable → ∀ M : Set (GL (Fin r) E), IsCompact M → ∃ S : Set (GL (Fin r) E), IsCompact S ∧ ∀ t : GL (Fin r) E, (t : Matrix (Fin r) (Fin r) E) * A₀ = A₀ * (t : Matrix (Fin r) (Fin r) E) → (∃ m ∈ M, (t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E) = (m : Matrix (Fin r) (Fin r) E)) → ∃ s ∈ S, (s : Matrix (Fin r) (Fin r) E) * A₀ = A₀ * (s : Matrix (Fin r) (Fin r) E) ∧ (s : Matrix (Fin r) (Fin r) E) * star (s : Matrix (Fin r) (Fin r) E) = (t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E))
    (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (A₀ : Matrix (Fin r) (Fin r) E) (hH : A₀.IsHermitian)
    (hs : A₀.charpoly.Separable) (Z : Set (Matrix (Fin r) (Fin r) E)) (hZ : IsCompact Z) :
    ∃ C : Set (Matrix.unitaryGroup (Fin r) E), IsCompact C ∧ ∀ g : Matrix.unitaryGroup (Fin r) E,
      g.1 * A₀ * star g.1 ∈ Z → ∃ c ∈ C, ∃ t : Matrix.unitaryGroup (Fin r) E,
        t.1 * A₀ = A₀ * t.1 ∧ g = c * t := by
  classical
  haveI : ContinuousStar E := ⟨by
    have h := AddMonoidHomClass.isometry_of_norm (starAddEquiv (R := E))
      (fun x => Unram.norm_star (F := F) x)
    exact h.continuous⟩
  obtain ⟨CE, hCE, hCEg⟩ := gl_orbit_cpt A₀ hs Z hZ

  let sU : GL (Fin r) E → GL (Fin r) E := fun c =>
    ⟨star (c : Matrix (Fin r) (Fin r) E), star ((c⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E),
      by rw [← star_mul, Units.inv_mul, star_one], by rw [← star_mul, Units.mul_inv, star_one]⟩
  have hsU : Continuous sU := by
    rw [Units.continuous_iff]
    exact ⟨continuous_star.comp Units.continuous_val, continuous_star.comp Units.continuous_coe_inv⟩
  let M : Set (GL (Fin r) E) := (fun c => (sU c * c)⁻¹) '' CE
  have hM : IsCompact M := hCE.image ((hsU.mul continuous_id).inv)
  obtain ⟨S, hS, hSt⟩ := hN F E r A₀ hH hs M hM
  let KM : Set (Matrix (Fin r) (Fin r) E) :=
    (fun q : GL (Fin r) E × GL (Fin r) E => ((q.1 * q.2 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)) ''
      (CE ×ˢ S)
  have hKM : IsCompact KM := (hCE.prod hS).image (Units.continuous_val.comp continuous_mul)
  have hcl : IsClosed (Matrix.unitaryGroup (Fin r) E : Set (Matrix (Fin r) (Fin r) E)) := by
    have : (Matrix.unitaryGroup (Fin r) E : Set (Matrix (Fin r) (Fin r) E)) =
        {A | star A * A = 1} ∩ {A | A * star A = 1} := by
      ext A; exact Unitary.mem_iff
    rw [this]
    exact (isClosed_eq (continuous_star.mul continuous_id) continuous_const).inter
      (isClosed_eq (continuous_id.mul continuous_star) continuous_const)
  refine ⟨Subtype.val ⁻¹' KM, hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hKM, ?_⟩
  intro g hg
  have hg1 : g.1 * star g.1 = 1 := Matrix.mem_unitaryGroup_iff.mp g.2
  have hg2 : star g.1 * g.1 = 1 := (Unitary.mem_iff.mp g.2).1
  let gU : GL (Fin r) E := ⟨g.1, star g.1, hg1, hg2⟩
  obtain ⟨c, hc, t, ht, hgct⟩ := hCEg gU hg
  set cm : Matrix (Fin r) (Fin r) E := (c : Matrix (Fin r) (Fin r) E)
  set ci : Matrix (Fin r) (Fin r) E := ((c⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)
  have htv : (t : Matrix (Fin r) (Fin r) E) = ci * g.1 := by
    have : t = c⁻¹ * gU := by rw [hgct, inv_mul_cancel_left]
    rw [this, Units.val_mul]
  have htt : (t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E) = ci * star ci := by
    rw [htv, star_mul, mul_assoc, ← mul_assoc g.1, hg1, one_mul]
  have hmM : (sU c * c)⁻¹ ∈ M := ⟨c, hc, rfl⟩
  have hmv : (((sU c * c)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) = ci * star ci := by
    rw [_root_.mul_inv_rev, Units.val_mul]; rfl
  obtain ⟨s, hsS, hsA, hss⟩ := hSt t ht ⟨_, hmM, by rw [htt, hmv]⟩
  rw [htt] at hss
  set sm : Matrix (Fin r) (Fin r) E := (s : Matrix (Fin r) (Fin r) E)
  set si : Matrix (Fin r) (Fin r) E := ((s⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)
  have hcs : ((c * s : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) ∈ Matrix.unitaryGroup (Fin r) E := by
    rw [Matrix.mem_unitaryGroup_iff, Units.val_mul, star_mul,
      show cm * sm * (star sm * star cm) = cm * (sm * star sm) * star cm by noncomm_ring, hss,
      show cm * (ci * star ci) * star cm = (cm * ci) * star (cm * ci) by rw [star_mul]; noncomm_ring,
      Units.mul_inv, star_one, one_mul]
  have hsi : si * A₀ = A₀ * si := by
    calc si * A₀ = si * A₀ * (sm * si) := by rw [Units.mul_inv, mul_one]
      _ = si * (sm * A₀) * si := by rw [hsA]; noncomm_ring
      _ = A₀ * si := by rw [← mul_assoc si, Units.inv_mul, one_mul]
  have hst : ((s⁻¹ * t : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) ∈ Matrix.unitaryGroup (Fin r) E := by
    rw [Matrix.mem_unitaryGroup_iff, Units.val_mul, star_mul,
      show si * (t : Matrix (Fin r) (Fin r) E) * (star (t : Matrix (Fin r) (Fin r) E) * star si) =
        si * ((t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E)) * star si by noncomm_ring,
      htt, ← hss,
      show si * (sm * star sm) * star si = (si * sm) * star (si * sm) by rw [star_mul]; noncomm_ring,
      Units.inv_mul, star_one, one_mul]
  refine ⟨⟨_, hcs⟩, ⟨(c, s), ⟨hc, hsS⟩, rfl⟩, ⟨_, hst⟩, ?_, ?_⟩
  · show ((s⁻¹ * t : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * A₀ =
      A₀ * ((s⁻¹ * t : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)
    rw [Units.val_mul, mul_assoc, ht, ← mul_assoc, hsi, mul_assoc]
  · apply Subtype.ext
    show g.1 = ((c * s : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *
      ((s⁻¹ * t : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)
    rw [← Units.val_mul, mul_assoc, mul_inv_cancel_left, ← hgct]

end GlobalTheory.OrbCpt

namespace GlobalTheory.OrbCpt

/- English proof (translation)
Introduce `F E _ _ _ _ _ r` and use `⟨fun A₀ hs Z hZ => gl_orbit_cpt A₀ hs Z hZ, fun A₀ hH hs Z hZ => unitary_orbit_cpt GlobalTheory.T.exists_compact_preimage_norm_centralizer_hermitian F E r A₀ hH hs Z hZ⟩`.
-/
theorem orbit_cpt : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), (∀ (A₀ : Matrix (Fin r) (Fin r) F), A₀.charpoly.Separable → ∀ Z : Set (Matrix (Fin r) (Fin r) F), IsCompact Z → ∃ C : Set (GL (Fin r) F), IsCompact C ∧ ∀ g : GL (Fin r) F, (g : Matrix (Fin r) (Fin r) F) * A₀ * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) ∈ Z → ∃ c ∈ C, ∃ t : GL (Fin r) F, (t : Matrix (Fin r) (Fin r) F) * A₀ = A₀ * (t : Matrix (Fin r) (Fin r) F) ∧ g = c * t) ∧ ∀ (A₀ : Matrix (Fin r) (Fin r) E), A₀.IsHermitian → A₀.charpoly.Separable → ∀ Z : Set (Matrix (Fin r) (Fin r) E), IsCompact Z → ∃ C : Set (Matrix.unitaryGroup (Fin r) E), IsCompact C ∧ ∀ g : Matrix.unitaryGroup (Fin r) E, g.1 * A₀ * star g.1 ∈ Z → ∃ c ∈ C, ∃ t : Matrix.unitaryGroup (Fin r) E, t.1 * A₀ = A₀ * t.1 ∧ g = c * t := fun F E _ _ _ _ _ r =>
  ⟨fun A₀ hs Z hZ => gl_orbit_cpt A₀ hs Z hZ,
    fun A₀ hH hs Z hZ => unitary_orbit_cpt GlobalTheory.T.exists_compact_preimage_norm_centralizer_hermitian F E r A₀ hH hs Z hZ⟩

end GlobalTheory.OrbCpt
