import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVan
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRestSide

noncomputable section

open Matrix Polynomial ValuativeRel

namespace PositivityTheory.RgUd.T.Desc.Asm

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

/- English proof (translation)
Apply `IsTopologicalAddGroup.t2Space_of_zero_sep` to reduce the goal to its premises. Introduce `x hx`. Use `⟨{y | valuation k y < valuation k x}, (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem ((valuation k).ne_zero_iff.2 hx), ?_⟩` and prove the remaining obligations. Conclude with `fun h => lt_irrefl (valuation k x) h`.
-/
theorem t2 : T2Space k := by
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro x hx
  refine ⟨{y | valuation k y < valuation k x},
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem ((valuation k).ne_zero_iff.2 hx), ?_⟩
  exact fun h => lt_irrefl (valuation k x) h

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Yhc6.main g x m`.
-/
theorem conj_pow (g : GL (Fin n) k) (x : Matrix (Fin n) (Fin n) k) (m : ℕ) :
    (g.val * x * g⁻¹.val) ^ m = g.val * x ^ m * g⁻¹.val :=
  _root_.UpperTheory.Reformulated.B.Yhc6.main g x m

/- English proof (translation)
Rewrite using `[aeval_eq_sum_range, aeval_eq_sum_range, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[conj_pow, Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem aeval_conj (g : GL (Fin n) k) (x : Matrix (Fin n) (Fin n) k) (P : k[X]) :
    aeval (g.val * x * g⁻¹.val) P = g.val * aeval x P * g⁻¹.val := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conj_pow, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Establish `h1 : g⁻¹.val * g.val = 1` using `by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `h2 : g.val * g⁻¹.val = 1` using `by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `e` using `hg a ha`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem comm_inv {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {g : GL (Fin n) k} (hg : g ∈ Gz Z) {a} (ha : a ∈ Z) :
    a * g⁻¹.val = g⁻¹.val * a := by
  have h1 : g⁻¹.val * g.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : g.val * g⁻¹.val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e := hg a ha
  calc a * g⁻¹.val = g⁻¹.val * (g.val * a) * g⁻¹.val := by rw [← mul_assoc, h1, one_mul]
    _ = g⁻¹.val * (a * g.val) * g⁻¹.val := by rw [e]
    _ = g⁻¹.val * a := by rw [mul_assoc, mul_assoc, h2, mul_one]

/- English proof (translation)
Introduce `a ha`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem conj_mem_Bz {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {g : GL (Fin n) k} (hg : g ∈ Gz Z)
    {x} (hx : x ∈ Bz Z) : g.val * x * g⁻¹.val ∈ Bz Z := by
  intro a ha
  calc a * (g.val * x * g⁻¹.val) = (a * g.val) * x * g⁻¹.val := by noncomm_ring
    _ = g.val * (a * x) * g⁻¹.val := by rw [hg a ha]; noncomm_ring
    _ = g.val * x * (a * g⁻¹.val) := by rw [hx a ha]; noncomm_ring
    _ = g.val * x * g⁻¹.val * a := by rw [comm_inv hg ha]; noncomm_ring

/- English proof (translation)
Use function extensionality and compare the values at `ij`. Simplify using `only [pZ]`. Use `set b : Matrix (Fin n) (Fin n) k := ((Module.finBasis k Z ij.2 : Z) : Matrix (Fin n) (Fin n) k)`. Establish `hb : b ∈ Z` using `(Module.finBasis k Z ij.2 : Z).2`. Establish `h1 : g⁻¹.val * g.val = 1` using `by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]`.

Rewrite using `[conj_pow]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc b, mul_assoc b]`. Use `_ = trace (g.val * (b * x ^ (ij.1 : ℕ) * g⁻¹.val)) := by rw [hg b hb]; simp only [mul_assoc]`. Use `_ = trace ((b * x ^ (ij.1 : ℕ) * g⁻¹.val) * g.val) := trace_mul_comm _ _`.

Use `_ = trace (b * x ^ (ij.1 : ℕ)) := by rw [mul_assoc, h1, mul_one]`.
-/
theorem pZ_conj {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {g : GL (Fin n) k} (hg : g ∈ Gz Z)
    (x : Matrix (Fin n) (Fin n) k) : pZ Z (g.val * x * g⁻¹.val) = pZ Z x := by
  funext ij
  simp only [pZ]
  set b : Matrix (Fin n) (Fin n) k := ((Module.finBasis k Z ij.2 : Z) : Matrix (Fin n) (Fin n) k)
  have hb : b ∈ Z := (Module.finBasis k Z ij.2 : Z).2
  have h1 : g⁻¹.val * g.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [conj_pow]
  calc trace (b * (g.val * x ^ (ij.1 : ℕ) * g⁻¹.val)) = trace ((b * g.val) * x ^ (ij.1 : ℕ) * g⁻¹.val) := by
        rw [mul_assoc b, mul_assoc b]
    _ = trace (g.val * (b * x ^ (ij.1 : ℕ) * g⁻¹.val)) := by rw [hg b hb]; simp only [mul_assoc]
    _ = trace ((b * x ^ (ij.1 : ℕ) * g⁻¹.val) * g.val) := trace_mul_comm _ _
    _ = trace (b * x ^ (ij.1 : ℕ)) := by rw [mul_assoc, h1, mul_one]

/- English proof (translation)
Use `continuous_pi fun ij => ?_` and prove the remaining obligations. Conclude with `(continuous_const.matrix_mul (continuous_id.pow _)).matrix_trace`.
-/
theorem continuous_pZ (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Continuous (pZ Z) := by
  refine continuous_pi fun ij => ?_
  exact (continuous_const.matrix_mul (continuous_id.pow _)).matrix_trace

/- English proof (translation)
Use `haveI := t2 (k := k)`. Establish `: Bz Z = ⋂ a ∈ Z, {x : Matrix (Fin n) (Fin n) k | a * x = x * a}`. Use extensionality with `x`. Simplify using `[Bz]`. Rewrite using `[this]`.

Conclude with `isClosed_biInter fun a _ => isClosed_eq (continuous_const.matrix_mul continuous_id) (continuous_id.matrix_mul continuous_const)`.
-/
theorem isClosed_Bz (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : IsClosed (Bz Z) := by
  haveI := t2 (k := k)
  have : Bz Z = ⋂ a ∈ Z, {x : Matrix (Fin n) (Fin n) k | a * x = x * a} := by
    ext x; simp [Bz]
  rw [this]
  exact isClosed_biInter fun a _ =>
    isClosed_eq (continuous_const.matrix_mul continuous_id) (continuous_id.matrix_mul continuous_const)

/- English proof (translation)
Use `set S := ∑ i ∈ Finset.range j, x ^ i * y ^ (j - 1 - i) with hS`. Establish `e : S * (x - y) = x ^ j - y ^ j` using `hc.geom_sum₂_mul j`. Establish `hx : Commute S x` using `Commute.sum_left _ _ _ fun i _ => ((Commute.refl x).pow_left i).mul_left (hc.symm.pow_left _)`. Establish `hy : Commute S y` using `Commute.sum_left _ _ _ fun i _ => (hc.pow_left i).mul_left ((Commute.refl y).pow_left _)`. Rewrite using `[← e]`.

Conclude with `Commute.isNilpotent_mul_left (hx.sub_right hy) h`.
-/
theorem isNilpotent_pow_sub {x y : Matrix (Fin n) (Fin n) k} (hc : Commute x y) (h : IsNilpotent (x - y)) (j : ℕ) :
    IsNilpotent (x ^ j - y ^ j) := by
  set S := ∑ i ∈ Finset.range j, x ^ i * y ^ (j - 1 - i) with hS
  have e : S * (x - y) = x ^ j - y ^ j := hc.geom_sum₂_mul j
  have hx : Commute S x := Commute.sum_left _ _ _ fun i _ =>
    ((Commute.refl x).pow_left i).mul_left (hc.symm.pow_left _)
  have hy : Commute S y := Commute.sum_left _ _ _ fun i _ =>
    (hc.pow_left i).mul_left ((Commute.refl y).pow_left _)
  rw [← e]
  exact Commute.isNilpotent_mul_left (hx.sub_right hy) h

/- English proof (translation)
Establish `hx : x ∈ Subalgebra.centralizer k ({a} : Set (Matrix (Fin n) (Fin n) k))`. Rewrite using `[Subalgebra.mem_centralizer_iff]`. Introduce `g hg`. Rewrite using `[Set.mem_singleton_iff.1 hg]`. Conclude with `h`.

Establish `h2 : aeval x P ∈ Subalgebra.centralizer k ({a} : Set (Matrix (Fin n) (Fin n) k))` using `Algebra.adjoin_le (Set.singleton_subset_iff.2 hx) (Polynomial.aeval_mem_adjoin_singleton k x (p := P))`. Rewrite `h2` using `[Subalgebra.mem_centralizer_iff]`. Conclude with `h2 a rfl`.
-/
theorem comm_aeval {a x : Matrix (Fin n) (Fin n) k} (h : a * x = x * a) (P : k[X]) :
    a * aeval x P = aeval x P * a := by
  have hx : x ∈ Subalgebra.centralizer k ({a} : Set (Matrix (Fin n) (Fin n) k)) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg]
    exact h
  have h2 : aeval x P ∈ Subalgebra.centralizer k ({a} : Set (Matrix (Fin n) (Fin n) k)) :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 hx) (Polynomial.aeval_mem_adjoin_singleton k x (p := P))
  rw [Subalgebra.mem_centralizer_iff] at h2
  exact h2 a rfl

/- English proof (translation)
Introduce `a ha` and use `comm_aeval (hx a ha) P`.
-/
theorem P_mem_Bz {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {x} (hx : x ∈ Bz Z) (P : k[X]) :
    aeval x P ∈ Bz Z := fun a ha => comm_aeval (hx a ha) P

/- English proof (translation)
Use function extensionality and compare the values at `ij`. Simplify using `only [pZ]`. Use `set b : Matrix (Fin n) (Fin n) k := ((Module.finBasis k Z ij.2 : Z) : Matrix (Fin n) (Fin n) k)`. Establish `hb : b ∈ Z` using `(Module.finBasis k Z ij.2 : Z).2`. Use `set j : ℕ := (ij.1 : ℕ)`.

Establish `hxP : Commute x (aeval x P)` using `comm_aeval rfl P`. Establish `hN` using `isNilpotent_pow_sub hxP hn j`. Establish `hbx : Commute b x` using `hx b hb`. Establish `hbP : Commute b (aeval x P)` using `comm_aeval (hx b hb) P`. Establish `hbN : Commute b (x ^ j - aeval x P ^ j)` using `(hbx.pow_right j).sub_right (hbP.pow_right j)`.

Establish `h0` using `(Matrix.isNilpotent_trace_of_isNilpotent (Commute.isNilpotent_mul_left hbN hN)).eq_zero`. Rewrite `h0` using `[mul_sub, trace_sub, sub_eq_zero]`. Conclude with `h0.symm`.
-/
theorem pZ_P {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {x} (hx : x ∈ Bz Z) (P : k[X])
    (hn : IsNilpotent (x - aeval x P)) : pZ Z (aeval x P) = pZ Z x := by
  funext ij
  simp only [pZ]
  set b : Matrix (Fin n) (Fin n) k := ((Module.finBasis k Z ij.2 : Z) : Matrix (Fin n) (Fin n) k)
  have hb : b ∈ Z := (Module.finBasis k Z ij.2 : Z).2
  set j : ℕ := (ij.1 : ℕ)
  have hxP : Commute x (aeval x P) := comm_aeval rfl P
  have hN := isNilpotent_pow_sub hxP hn j
  have hbx : Commute b x := hx b hb
  have hbP : Commute b (aeval x P) := comm_aeval (hx b hb) P
  have hbN : Commute b (x ^ j - aeval x P ^ j) := (hbx.pow_right j).sub_right (hbP.pow_right j)
  have h0 := (Matrix.isNilpotent_trace_of_isNilpotent (Commute.isNilpotent_mul_left hbN hN)).eq_zero
  rw [mul_sub, trace_sub, sub_eq_zero] at h0
  exact h0.symm

/- English proof (translation)
Establish `hsP : Commute s (aeval w P)` using `comm_aeval hc.symm.eq P`. Establish `hwP : Commute w (aeval w P)` using `comm_aeval rfl P`. Establish `hcomm : Commute (w - aeval w P) (w - s)` using `((Commute.refl w).sub_left hwP.symm).sub_right (hc.sub_left hsP.symm)`. Establish `hD : IsNilpotent (s - aeval w P)`. Establish `e : (w - aeval w P) - (w - s) = s - aeval w P` using `by abel`.

Rewrite using `[← e]`. Conclude with `Commute.isNilpotent_sub hcomm hPn hn`. Establish `e1 : ∀ M : Matrix (Fin n) (Fin n) k, Matrix.toLinAlgEquiv' M = Matrix.toLin' M` using `fun _ => rfl`. Establish `hcl : Commute (Matrix.toLin' s) (Matrix.toLin' (aeval w P))`. Rewrite using `[← e1, ← e1]`.

Conclude with `hsP.map _`. Establish `hss : Module.End.IsSemisimple (Matrix.toLin' (s - aeval w P))`. Rewrite using `[map_sub]`. Conclude with `Module.End.IsSemisimple.sub_of_commute hcl hs hPs`. Establish `hnl : IsNilpotent (Matrix.toLin' (s - aeval w P))`.

Rewrite using `[← e1]`. Conclude with `hD.map _`. Establish `h0` using `Module.End.eq_zero_of_isNilpotent_isSemisimple hnl hss`. Rewrite `h0` using `[LinearEquiv.map_eq_zero_iff, sub_eq_zero]`. Conclude with `h0.symm`.
-/
theorem jc_unique [CharZero k] {s w : Matrix (Fin n) (Fin n) k} (P : k[X])
    (hs : Module.End.IsSemisimple (Matrix.toLin' s)) (hc : Commute w s) (hn : IsNilpotent (w - s))
    (hPs : Module.End.IsSemisimple (Matrix.toLin' (aeval w P))) (hPn : IsNilpotent (w - aeval w P)) :
    aeval w P = s := by
  have hsP : Commute s (aeval w P) := comm_aeval hc.symm.eq P
  have hwP : Commute w (aeval w P) := comm_aeval rfl P
  have hcomm : Commute (w - aeval w P) (w - s) :=
    ((Commute.refl w).sub_left hwP.symm).sub_right (hc.sub_left hsP.symm)
  have hD : IsNilpotent (s - aeval w P) := by
    have e : (w - aeval w P) - (w - s) = s - aeval w P := by abel
    rw [← e]
    exact Commute.isNilpotent_sub hcomm hPn hn
  have e1 : ∀ M : Matrix (Fin n) (Fin n) k, Matrix.toLinAlgEquiv' M = Matrix.toLin' M := fun _ => rfl
  have hcl : Commute (Matrix.toLin' s) (Matrix.toLin' (aeval w P)) := by
    rw [← e1, ← e1]; exact hsP.map _
  have hss : Module.End.IsSemisimple (Matrix.toLin' (s - aeval w P)) := by
    rw [map_sub]; exact Module.End.IsSemisimple.sub_of_commute hcl hs hPs
  have hnl : IsNilpotent (Matrix.toLin' (s - aeval w P)) := by
    rw [← e1]; exact hD.map _
  have h0 := Module.End.eq_zero_of_isNilpotent_isSemisimple hnl hss
  rw [LinearEquiv.map_eq_zero_iff, sub_eq_zero] at h0
  exact h0.symm

/- English proof (translation)
Introduce `hJ hS n Z hZ s hs _hsZ hss hvan y hy ξ hsupp hinv`. Take `⟨P, hP⟩` from `hJ n Z hZ y`. Establish `: T2Space k` using `t2`. Use `hS n Z hZ s hs hss hvan (Bz Z ∩ pZ Z ⁻¹' {y}) P ((isClosed_Bz Z).inter (isClosed_singleton.preimage (continuous_pZ Z))) Set.inter_subset_left ?_ ?_ ξ hsupp hinv` and prove the remaining obligations. Introduce `g hg x hx`.

Use `⟨conj_mem_Bz hg hx.1, ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_preimage, pZ_conj hg]`. Conclude with `hx.2`. Introduce `x hx`. Establish `hxy : pZ Z x = y` using `hx.2`.

Take `⟨hss', hnil⟩` from `hP x hx.1 hxy`. Use `⟨⟨P_mem_Bz hx.1 P, ?_⟩, hss', hnil, ?_⟩` and prove the remaining obligations. Use `show pZ Z (aeval x P) ∈ ({y} : Set _)`. Rewrite using `[pZ_P hx.1 P hnil]`. Conclude with `hx.2`.

Take `⟨g, hg, hn, hc⟩` from `hy x hx.1 hxy`. Use `⟨g, hg, ?_⟩` and prove the remaining obligations. Rewrite using `[← aeval_conj]`. Establish `hw : pZ Z (g.val * x * g⁻¹.val) = y` using `by rw [pZ_conj hg]; exact hxy`. Take `⟨h1, h2⟩` from `hP _ (conj_mem_Bz hg hx.1) hw`.

Conclude with `jc_unique P hss hc hn h1 h2`.
-/
theorem descA_of [CharZero k] : JCPoly (k := k) → SliceVan (k := k) → DescA (k := k) := by
  intro hJ hS n Z hZ s hs _hsZ hss hvan y hy ξ hsupp hinv
  obtain ⟨P, hP⟩ := hJ n Z hZ y
  have : T2Space k := t2
  refine hS n Z hZ s hs hss hvan (Bz Z ∩ pZ Z ⁻¹' {y}) P
    ((isClosed_Bz Z).inter (isClosed_singleton.preimage (continuous_pZ Z))) Set.inter_subset_left ?_ ?_ ξ hsupp hinv
  · intro g hg x hx
    refine ⟨conj_mem_Bz hg hx.1, ?_⟩
    simp only [Set.mem_preimage, pZ_conj hg]
    exact hx.2
  · intro x hx
    have hxy : pZ Z x = y := hx.2
    obtain ⟨hss', hnil⟩ := hP x hx.1 hxy
    refine ⟨⟨P_mem_Bz hx.1 P, ?_⟩, hss', hnil, ?_⟩
    · show pZ Z (aeval x P) ∈ ({y} : Set _)
      rw [pZ_P hx.1 P hnil]
      exact hx.2
    · obtain ⟨g, hg, hn, hc⟩ := hy x hx.1 hxy
      refine ⟨g, hg, ?_⟩
      rw [← aeval_conj]
      have hw : pZ Z (g.val * x * g⁻¹.val) = y := by rw [pZ_conj hg]; exact hxy
      obtain ⟨h1, h2⟩ := hP _ (conj_mem_Bz hg hx.1) hw
      exact jc_unique P hss hc hn h1 h2

end PositivityTheory.RgUd.T.Desc.Asm
