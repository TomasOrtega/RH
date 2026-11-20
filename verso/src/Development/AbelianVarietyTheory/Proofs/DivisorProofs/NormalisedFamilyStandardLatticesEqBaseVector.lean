import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.NatAtStd

/- English proof (translation)
Establish `hr : ∀ x : E, x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x` using `fun x => ⟨by rintro ⟨a, rfl⟩; exact a.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩`. Establish `hm : ∀ x : Fin N → E, x ∈ (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) ↔ ∀ k, IsIntegral ℤ (x k)` using `fun x => by`. Simplify using `only [Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]`. Conclude with `forall_congr' fun k => hr (x k)`. Establish `hs : ∀ k : Fin N, (Pi.single k 1 : Fin N → E) ∈ (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E))` using `fun k => by`.

Rewrite using `[hm]`. Introduce `j`. Rewrite using `[Pi.single_apply]`. Use `split_ifs`. Conclude with `isIntegral_one`.

Conclude with `isIntegral_zero`. Use `⟨Submodule.fg_pi fun _ => ?_, ?_, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Submodule.one_eq_span]`. Conclude with `Submodule.fg_span_singleton _`. Rewrite using `[eq_top_iff, ← (Pi.basisFun E (Fin N)).span_eq]`.

Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Simplify using `using hs k`. Rewrite using `[hr]`. Rewrite `hx`, `hy` using `[hm]`.

Conclude with `IsIntegral.sum _ fun i _ => ((hx i).map (starRingEnd E).toIntAlgHom).mul (hy i)`. Rewrite using `[hm]`. Introduce `k`. Use `h _ (hs k)` as an intermediate fact. Rewrite `this` using `[hr]`.

Simplify `this` using `[stdH, Pi.single_apply, apply_ite]`.
-/
theorem isSD_pi (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ) :
    IsSDLat E N (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) := by
  have hr : ∀ x : E, x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x := fun x =>
    ⟨by rintro ⟨a, rfl⟩; exact a.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  have hm : ∀ x : Fin N → E, x ∈ (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) ↔
      ∀ k, IsIntegral ℤ (x k) := fun x => by
    simp only [Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]
    exact forall_congr' fun k => hr (x k)
  have hs : ∀ k : Fin N, (Pi.single k 1 : Fin N → E) ∈
      (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) := fun k => by
    rw [hm]
    intro j
    rw [Pi.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  refine ⟨Submodule.fg_pi fun _ => ?_, ?_, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin N)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨k, rfl⟩
    simpa using hs k
  · rw [hr]
    rw [hm] at hx hy
    exact IsIntegral.sum _ fun i _ => ((hx i).map (starRingEnd E).toIntAlgHom).mul (hy i)
  · rw [hm]
    intro k
    have := h _ (hs k)
    rw [hr] at this
    simpa [stdH, Pi.single_apply, apply_ite] using this

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨A, hA, rfl⟩`. Establish `h : ∀ i j, ∃ b : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E b = A i j` using `fun i j => by`. Establish `h1 : (Pi.single j 1 : Fin N → D.host.E) ∈ StandardLatticesGL3.stdL D N` using `fun k _ => by`.

Distinguish the cases in `e : k = j`. Substitute `e` using the available equality. Rewrite using `[Pi.single_eq_same]`. Conclude with `Submodule.one_le.1 le_rfl`. Rewrite using `[Pi.single_eq_of_ne e]`.

Conclude with `Submodule.zero_mem _`. Establish `h2` using `Submodule.mem_one.1 (hA _ h1 i trivial)`. Simplify using `using h2`. Use `choose b hb using h`. Establish `e : A = (algebraMap (𝓞 D.host.E) D.host.E).mapMatrix (Matrix.of b)` using `Matrix.ext fun i j => (hb i j).symm`.

Rewrite using `[e, ← RingHom.map_det]`. Conclude with `Submodule.mem_one.2 ⟨_, rfl⟩`. Conclude with `Submodule.one_le.2 (Submodule.subset_span ⟨1, fun v hv => by simpa using hv, Matrix.det_one.symm⟩)`.
-/
theorem detId_std (D : D7) (N : ℕ) : TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N) = 1 := by
  classical
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨A, hA, rfl⟩
    have h : ∀ i j, ∃ b : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E b = A i j := fun i j => by
      have h1 : (Pi.single j 1 : Fin N → D.host.E) ∈ StandardLatticesGL3.stdL D N := fun k _ => by
        by_cases e : k = j
        · subst e
          rw [Pi.single_eq_same]
          exact Submodule.one_le.1 le_rfl
        · rw [Pi.single_eq_of_ne e]
          exact Submodule.zero_mem _
      have h2 := Submodule.mem_one.1 (hA _ h1 i trivial)
      simpa using h2
    choose b hb using h
    have e : A = (algebraMap (𝓞 D.host.E) D.host.E).mapMatrix (Matrix.of b) :=
      Matrix.ext fun i j => (hb i j).symm
    rw [e, ← RingHom.map_det]
    exact Submodule.mem_one.2 ⟨_, rfl⟩
  · exact Submodule.one_le.2 (Submodule.subset_span ⟨1, fun v hv => by simpa using hv, Matrix.det_one.symm⟩)

/- English proof (translation)
Use `letI := D.host.cmStar`. Establish `h1` using `h.2 1`. Rewrite using `[Submodule.one_eq_span]`. Simplify using `using h1`.
-/
theorem chi_one (D : D7) (χ : TaylorLogMetric.IdE D → ℂ) (h : TaylorLogMetric.IsChi D χ) : χ 1 = 1 := by
  letI := D.host.cmStar
  have h1 := h.2 1
  rw [Submodule.one_eq_span]
  simpa using h1

/- English proof (translation)
Simplify using `[Base.chiFac, detId_std, chi_one D χ h]`.
-/
theorem chiFac_std (D : D7) (χ : TaylorLogMetric.IdE D → ℂ) (h : TaylorLogMetric.IsChi D χ) (a b : ℕ) :
    Base.chiFac χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) = 1 := by
  simp [Base.chiFac, detId_std, chi_one D χ h]

variable (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ}

/- English proof (translation)
Establish `htop : A.addSubgroupOf A = ⊤` using `AddSubgroup.addSubgroupOf_self A`. Use `haveI hsub : Subsingleton (A ⧸ A.addSubgroupOf A) := by`. Rewrite using `[htop]`. Conclude with `QuotientAddGroup.subsingleton_quotient_top`. Set `q0 : A ⧸ A.addSubgroupOf A` to `QuotientAddGroup.mk 0`.

Use `⟨((Quotient.out q0 : A) : TaylorLogMetric.VC D N N'), Subtype.property _, fun G => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `z`. Establish `hi : (A.addSubgroupOf A).index = 1` using `by rw [htop]; exact AddSubgroup.index_top`. Unfold `TaylorLogMetric.Iop`. Rewrite using `[finsum_eq_single _ q0 (fun q hq => absurd (Subsingleton.elim q q0) hq), hi]`.

Simplify using the standard rewrite rules.
-/
theorem Iop_self (A : AddSubgroup (TaylorLogMetric.VC D N N')) :
    ∃ x ∈ A, ∀ G : TaylorLogMetric.VC D N N' → ℂ, TaylorLogMetric.Iop D T A A G = fun z => TaylorLogMetric.al D T x * TaylorLogMetric.U D T x G z := by
  have htop : A.addSubgroupOf A = ⊤ := AddSubgroup.addSubgroupOf_self A
  haveI hsub : Subsingleton (A ⧸ A.addSubgroupOf A) := by
    rw [htop]; exact QuotientAddGroup.subsingleton_quotient_top
  let q0 : A ⧸ A.addSubgroupOf A := QuotientAddGroup.mk 0
  refine ⟨((Quotient.out q0 : A) : TaylorLogMetric.VC D N N'), Subtype.property _, fun G => ?_⟩
  funext z
  have hi : (A.addSubgroupOf A).index = 1 := by rw [htop]; exact AddSubgroup.index_top
  unfold TaylorLogMetric.Iop
  rw [finsum_eq_single _ q0 (fun q hq => absurd (Subsingleton.elim q q0) hq), hi]
  simp

/- English proof (translation)
Simplify using `[TaylorLogMetric.Hf, neg_div]`.
-/
theorem Hf_neg_right (z x : TaylorLogMetric.VC D N N') : TaylorLogMetric.Hf D T z (-x) = -TaylorLogMetric.Hf D T z x := by
  simp [TaylorLogMetric.Hf, neg_div]

/- English proof (translation)
Simplify using `[TaylorLogMetric.Hf, neg_div]`.
-/
theorem Hf_neg_left (z x : TaylorLogMetric.VC D N N') : TaylorLogMetric.Hf D T (-z) x = -TaylorLogMetric.Hf D T z x := by
  simp [TaylorLogMetric.Hf, neg_div]

/- English proof (translation)
Simplify using `[TaylorLogMetric.Hf, add_mul, Finset.sum_add_distrib, add_div]`.
-/
theorem Hf_add_left (z w x : TaylorLogMetric.VC D N N') : TaylorLogMetric.Hf D T (z + w) x = TaylorLogMetric.Hf D T z x + TaylorLogMetric.Hf D T w x := by
  simp [TaylorLogMetric.Hf, add_mul, Finset.sum_add_distrib, add_div]

/- English proof (translation)
Unfold `TaylorLogMetric.al`. Rewrite using `[Hf_neg_left, Hf_neg_right, neg_neg, ← mul_zpow]`. Simplify using the standard rewrite rules.
-/
theorem al_neg_mul (x : TaylorLogMetric.VC D N N') : TaylorLogMetric.al D T (-x) * TaylorLogMetric.al D T x = 1 := by
  unfold TaylorLogMetric.al
  rw [Hf_neg_left, Hf_neg_right, neg_neg, ← mul_zpow]
  simp

/- English proof (translation)
Establish `h` using `al_neg_mul D T x`. Unfold `TaylorLogMetric.U`. Simplify using `only [Hf_add_left, Hf_neg_left, Hf_neg_right, neg_add_cancel_right]`. Establish `he : Complex.exp (-(Real.pi : ℂ) * (TaylorLogMetric.Hf D T z x + -TaylorLogMetric.Hf D T x x) - (Real.pi : ℂ) * TaylorLogMetric.Hf D T x x / 2) * Complex.exp (-(Real.pi : ℂ) * -TaylorLogMetric.Hf D T z x - (Real.pi : ℂ) * - -TaylorLogMetric.Hf D T x x / 2) = 1`. Rewrite using `[← Complex.exp_add, ← Complex.exp_zero]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `(G z) * he * (TaylorLogMetric.al D T (-x) * TaylorLogMetric.al D T x) + G z * h`.
-/
theorem inv_op (x : TaylorLogMetric.VC D N N') (G : TaylorLogMetric.VC D N N' → ℂ) (z : TaylorLogMetric.VC D N N') :
    TaylorLogMetric.al D T (-x) * TaylorLogMetric.U D T (-x) (fun w => TaylorLogMetric.al D T x * TaylorLogMetric.U D T x G w) z = G z := by
  have h := al_neg_mul D T x
  unfold TaylorLogMetric.U
  simp only [Hf_add_left, Hf_neg_left, Hf_neg_right, neg_add_cancel_right]
  have he : Complex.exp (-(Real.pi : ℂ) * (TaylorLogMetric.Hf D T z x + -TaylorLogMetric.Hf D T x x) - (Real.pi : ℂ) * TaylorLogMetric.Hf D T x x / 2) *
      Complex.exp (-(Real.pi : ℂ) * -TaylorLogMetric.Hf D T z x - (Real.pi : ℂ) * - -TaylorLogMetric.Hf D T x x / 2) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    ring
  linear_combination (G z) * he * (TaylorLogMetric.al D T (-x) * TaylorLogMetric.al D T x) + G z * h

/- English proof (translation)
Introduce `D cc dl B χ hχ hV a b ha hb`. Establish `hA : TaylorLogMetric.admitted D a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b)`. Use `letI := D.host.cmStar`. Conclude with `⟨ha, hb, isSD_pi _ a, isSD_pi _ b⟩`. Use `⟨hA, ?_⟩` and prove the remaining obligations.

Take `⟨x, hx, hI⟩` from `Iop_self D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b))`. Establish `hTh : B.eNat χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) ∈ TaylorLogMetric.Th D B.tor (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b)` using `(hV a b _ _ hA).1`. Establish `hfix` using `hTh.2 (-x) (neg_mem hx)`. Establish `he : B.eNat χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) = fun z => TaylorLogMetric.al D B.tor x * TaylorLogMetric.U D B.tor x (fun w => TaylorLogMetric.al D B.tor x * TaylorLogMetric.U D B.tor x (B.thZero a b) w) z`. Use function extensionality and compare the values at `z`.

Unfold `Base.eNat Base.thMoved Base.thHalf`. Rewrite using `[chiFac_std D χ hχ, one_mul, hI, hI]`. Establish `h1 : B.eNat χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) = fun w => TaylorLogMetric.al D B.tor x * TaylorLogMetric.U D B.tor x (B.thZero a b) w`. Use function extensionality and compare the values at `z`. Rewrite using `[← hfix z]`.

Use `conv_lhs => rw [he]`. Conclude with `inv_op D B.tor x _ z`. Use function extensionality and compare the values at `z`. Rewrite using `[← hfix z]`. Use `conv_lhs => rw [h1]`.

Conclude with `inv_op D B.tor x _ z`.
-/
theorem eNat_std : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (B : Base D cc dl) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → B.VecP χ → ∀ a b : ℕ, Even a → Even b → TaylorLogMetric.admitted D a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) ∧ B.eNat χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) = B.thZero a b := by
  intro D cc dl B χ hχ hV a b ha hb
  have hA : TaylorLogMetric.admitted D a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) := by
    letI := D.host.cmStar
    exact ⟨ha, hb, isSD_pi _ a, isSD_pi _ b⟩
  refine ⟨hA, ?_⟩
  obtain ⟨x, hx, hI⟩ := Iop_self D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b))
  have hTh : B.eNat χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) ∈ TaylorLogMetric.Th D B.tor (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) :=
    (hV a b _ _ hA).1
  have hfix := hTh.2 (-x) (neg_mem hx)
  have he : B.eNat χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) = fun z => TaylorLogMetric.al D B.tor x * TaylorLogMetric.U D B.tor x
      (fun w => TaylorLogMetric.al D B.tor x * TaylorLogMetric.U D B.tor x (B.thZero a b) w) z := by
    funext z
    unfold Base.eNat Base.thMoved Base.thHalf
    rw [chiFac_std D χ hχ, one_mul, hI, hI]
  have h1 : B.eNat χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) =
      fun w => TaylorLogMetric.al D B.tor x * TaylorLogMetric.U D B.tor x (B.thZero a b) w := by
    funext z
    rw [← hfix z]
    conv_lhs => rw [he]
    exact inv_op D B.tor x _ z
  funext z
  rw [← hfix z]
  conv_lhs => rw [h1]
  exact inv_op D B.tor x _ z

end GlobalTheory.NatAtStd
