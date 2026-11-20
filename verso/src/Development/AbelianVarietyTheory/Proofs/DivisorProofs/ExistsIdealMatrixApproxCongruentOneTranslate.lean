import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorRationalTranslateMemThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPrincipalCongruenceLevelSubgroupIffIntegralCo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleStrongApproxModAdelicIdeal
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlobApprox
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.LevelSubgroupFiniteAdelicStandard
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.CongApprox

/- English proof (translation)
The claim follows from `Formalism.UG.P.easyc_inclE_mem _ _ _ (RingHom.mem_range.2 ⟨x, rfl⟩)`.
-/
theorem inc_mem_OhE (D : D7) (x : 𝓞 D.host.E) : inc D (x : D.host.E) ∈ OhE D :=
  Formalism.UG.P.easyc_inclE_mem _ _ _ (RingHom.mem_range.2 ⟨x, rfl⟩)

/- English proof (translation)
Rewrite using `[← GlobalTheory.AdelicApprox.levelC_natCast]`. Take `⟨b, t, ht, h⟩` from `Formalism.UG.P.csGlob_approx Formalism.UG.P.csGlob_intAdApprox (n : 𝓞 ℚ) (Nat.cast_ne_zero.2 hn.ne') s hs`. Conclude with `⟨b, t, ht, h⟩`.
-/
theorem exists_int_approx (D : D7) (n : ℕ) (hn : 0 < n) (s : AE D) (hs : s ∈ OhE D) :
    ∃ b : 𝓞 D.host.E, ∃ w ∈ OhE D, s = inc D (b : D.host.E) + (n : AE D) * w := by
  rw [← GlobalTheory.AdelicApprox.levelC_natCast]
  obtain ⟨b, t, ht, h⟩ := Formalism.UG.P.csGlob_approx Formalism.UG.P.csGlob_intAdApprox (n : 𝓞 ℚ)
    (Nat.cast_ne_zero.2 hn.ne') s hs
  exact ⟨b, t, ht, h⟩

/- English proof (translation)
Establish `h` using `GlobalTheory.AdelicApprox.absNorm_mul_mem_IhE D ⊤ s hs`. Simplify `h` using `[Ideal.absNorm_top]`.
-/
theorem OhE_le_IhE_top (D : D7) (s : AE D) (hs : s ∈ OhE D) : s ∈ IhE D ⊤ := by
  have h := GlobalTheory.AdelicApprox.absNorm_mul_mem_IhE D ⊤ s hs
  simpa [Ideal.absNorm_top] using h

/- English proof (translation)
Unfold `hatId at ht ⊢`. Proceed by induction on `ht using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨b, hb, s, hs, rfl⟩` from `hy`. Conclude with `AddSubgroup.subset_closure ⟨b, hb, x * s, mul_mem hx hs, by ring⟩`.

Consider the case `zero => rw [mul_zero]`. Conclude with `zero_mem _`. Consider the case `add y y' _ _ hy hy' => rw [mul_add]`. Conclude with `add_mem hy hy'`. Consider the case `neg y _ hy => rw [mul_neg]`.

Conclude with `neg_mem hy`.
-/
theorem mul_mem_hatId (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (x : AE D) (hx : x ∈ OhE D)
    (t : AE D) (ht : t ∈ hatId D 𝔪) : x * t ∈ hatId D 𝔪 := by
  unfold hatId at ht ⊢
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, x * s, mul_mem hx hs, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add y y' _ _ hy hy' => rw [mul_add]; exact add_mem hy hy'
  | neg y _ hy => rw [mul_neg]; exact neg_mem hy

/- English proof (translation)
Unfold `hatId at ht`. Proceed by induction on `ht using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨b, hb, s, hs, rfl⟩` from `hy`. Take `⟨c, w, hw, hsw⟩` from `exists_int_approx D m hm s hs`.

Use `⟨b * c, Ideal.mul_mem_right c 𝔪 hb, -(inc D (b : D.host.E) * w), OhE_le_IhE_top D _ (neg_mem (mul_mem (inc_mem_OhE D b) hw)), ?_⟩` and prove the remaining obligations. Rewrite using `[hsw]`. Use `push_cast`. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩`. Consider the case `add y y' _ _ hy hy'`. Take `⟨b, hb, u, hu, h⟩` from `hy`. Take `⟨b', hb', u', hu', h'⟩` from `hy'`. Use `⟨b + b', add_mem hb hb', u + u', add_mem hu hu', ?_⟩` and prove the remaining obligations.

Use `push_cast`. Rewrite using `[map_add]`. Take the linear combination `h + h'`. Consider the case `neg y _ hy`. Take `⟨b, hb, u, hu, h⟩` from `hy`.

Use `⟨-b, neg_mem hb, -u, neg_mem hu, ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[map_neg]`. Take the linear combination `-h`.
-/
theorem exists_mem_approx (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (m : ℕ) (hm : 0 < m) (t : AE D)
    (ht : t ∈ hatId D 𝔪) :
    ∃ b ∈ 𝔪, ∃ y ∈ IhE D ⊤, inc D (b : D.host.E) - t = (m : AE D) * y := by
  unfold hatId at ht
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    obtain ⟨c, w, hw, hsw⟩ := exists_int_approx D m hm s hs
    refine ⟨b * c, Ideal.mul_mem_right c 𝔪 hb, -(inc D (b : D.host.E) * w),
      OhE_le_IhE_top D _ (neg_mem (mul_mem (inc_mem_OhE D b) hw)), ?_⟩
    rw [hsw]
    push_cast
    rw [map_mul]
    ring
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | add y y' _ _ hy hy' =>
    obtain ⟨b, hb, u, hu, h⟩ := hy
    obtain ⟨b', hb', u', hu', h'⟩ := hy'
    refine ⟨b + b', add_mem hb hb', u + u', add_mem hu hu', ?_⟩
    push_cast
    rw [map_add]
    linear_combination h + h'
  | neg y _ hy =>
    obtain ⟨b, hb, u, hu, h⟩ := hy
    refine ⟨-b, neg_mem hb, -u, neg_mem hu, ?_⟩
    push_cast
    rw [map_neg]
    linear_combination -h

end GlobalTheory.CongApprox

namespace GlobalTheory.CongApprox

/- English proof (translation)
Introduce `D 𝔪 _ a d k hk hcong z _ m hm`. Establish `hinv : CongOne D 𝔪 k⁻¹` using `congOne_inv hk hcong`. Use `set K : Matrix (Fin a) (Fin a) (AE D) := (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) with hK`. Use `set T : Matrix (Fin d) (Fin a) (AE D) := z.map (inc D) * (K - 1) with hT`. Establish `hTmem : ∀ i j, T i j ∈ hatId D 𝔪`.

Introduce `i j`. Rewrite using `[hT, Matrix.mul_apply]`. Use `sum_mem fun l _ => ?_` and prove the remaining obligations. Take `⟨b, hb⟩` from `‹∀ i j, ∃ b : 𝓞 D.host.E, z i j = (b : D.host.E)› i l`. Rewrite using `[Matrix.map_apply, hb]`.

Conclude with `mul_mem_hatId D 𝔪 _ (inc_mem_OhE D b) _ (hinv l j)`. Use `choose b hb y hy hby using fun i j => exists_mem_approx D 𝔪 m hm (T i j) (hTmem i j)`. Use `⟨Matrix.of fun i j => (b i j : D.host.E), fun i j => ⟨b i j, hb i j, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hKinv : (((k : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) = K`. Rewrite using `[hK, Subgroup.coe_inv]`.

Establish `e1 : (((1 : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) = 1` using `by simp`. Establish `hzK : z.map (inc D) * K = z.map (inc D) + T`. Rewrite using `[hT, Matrix.mul_sub, Matrix.mul_one]`. Normalize the expressions using the abelian group laws. Establish `key : ∀ i j, ((z + Matrix.of fun i j => (b i j : D.host.E)).map (inc D) - (((1 : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * z.map (inc D) * (((k : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j = inc D (b i j : D.host.E) - T i …`.

Introduce `i j`. Rewrite using `[e1, Matrix.one_mul, hKinv, hzK, Matrix.map_add _ (map_add (inc D))]`. Simplify using `[Matrix.map_apply]`. Unfold `CloseTo`. Conclude with `fun i j => ⟨y i j, hy i j, (key i j).trans (hby i j)⟩`.
-/
theorem exists_closeTo_congOne : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ {a d : ℕ} (k : GA D a), k ∈ intG D a → CongOne D 𝔪 k → ∀ (z : Matrix (Fin d) (Fin a) D.host.E), (∀ i j, ∃ b : 𝓞 D.host.E, z i j = (b : D.host.E)) → ∀ m : ℕ, 0 < m → ∃ w : Matrix (Fin d) (Fin a) D.host.E, (∀ i j, ∃ b ∈ 𝔪, w i j = (b : D.host.E)) ∧ CloseTo D ⊤ m (k : GL (Fin a) (AE D)) ((1 : GA D d) : GL (Fin d) (AE D)) z (z + w) := by
  intro D 𝔪 _ a d k hk hcong z _ m hm
  have hinv : CongOne D 𝔪 k⁻¹ := congOne_inv hk hcong
  set K : Matrix (Fin a) (Fin a) (AE D) := (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) with hK
  set T : Matrix (Fin d) (Fin a) (AE D) := z.map (inc D) * (K - 1) with hT
  have hTmem : ∀ i j, T i j ∈ hatId D 𝔪 := by
    intro i j
    rw [hT, Matrix.mul_apply]
    refine sum_mem fun l _ => ?_
    obtain ⟨b, hb⟩ := ‹∀ i j, ∃ b : 𝓞 D.host.E, z i j = (b : D.host.E)› i l
    rw [Matrix.map_apply, hb]
    exact mul_mem_hatId D 𝔪 _ (inc_mem_OhE D b) _ (hinv l j)
  choose b hb y hy hby using fun i j => exists_mem_approx D 𝔪 m hm (T i j) (hTmem i j)
  refine ⟨Matrix.of fun i j => (b i j : D.host.E), fun i j => ⟨b i j, hb i j, rfl⟩, ?_⟩
  have hKinv : (((k : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) = K := by
    rw [hK, Subgroup.coe_inv]
  have e1 : (((1 : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) = 1 := by simp
  have hzK : z.map (inc D) * K = z.map (inc D) + T := by
    rw [hT, Matrix.mul_sub, Matrix.mul_one]; abel
  have key : ∀ i j, ((z + Matrix.of fun i j => (b i j : D.host.E)).map (inc D) -
      (((1 : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * z.map (inc D) *
        (((k : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j =
      inc D (b i j : D.host.E) - T i j := by
    intro i j
    rw [e1, Matrix.one_mul, hKinv, hzK, Matrix.map_add _ (map_add (inc D))]
    simp [Matrix.map_apply]
  unfold CloseTo
  exact fun i j => ⟨y i j, hy i j, (key i j).trans (hby i j)⟩

end GlobalTheory.CongApprox
