import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FinsumQuotientOfLe
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsZeroOrPosMulRootOfUnityFiniteGaussSumStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ComplexPhaseCalculusRootOfUnityStatement
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase

/- English proof (translation)
Establish `h` using `QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' (x : G ⧸ N)).symm`. Rewrite `h` using `[neg_add_eq_sub]`. Then use the resulting hypothesis.
-/
private theorem quotient_out_sub_mem' {G : Type} [AddCommGroup G] (N : AddSubgroup G) (x : G) :
    (x : G ⧸ N).out - x ∈ N := by
  have h := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' (x : G ⧸ N)).symm
  rwa [neg_add_eq_sub] at h

open Classical in

/- English proof (translation)
Distinguish the cases in `hc0 : c = 0`. Apply the tactic sequence `have h0 : ∀ x, φ x = 0 := fun x => by rw [hφ x]; split_ifs <;> simp [hc0]`. Simplify using `only [h0, finsum_zero]`. Conclude with `ph_zero`. Establish `hfper : ∀ s ∈ S, ∀ t ∈ S, t ∈ P → f (s + t) = f s`.

Introduce `s hs t htS htP`. Establish `h1` using `hφ (a + (s + t))`. Establish `h2` using `hφ (a + s)`. Rewrite `h1` using `[add_sub_cancel_left, if_pos (S.add_mem hs htS)]`. Rewrite `h2` using `[add_sub_cancel_left, if_pos hs]`.

Establish `h3 : φ (a + (s + t)) = φ (a + s)` using `by rw [← add_assoc]; exact hper _ t htP`. Conclude with `mul_left_cancel₀ hc0 (h1.symm.trans (h3.trans h2))`. Set `ψ : S →+ A ⧸ P` to `(QuotientAddGroup.mk' P).comp S.subtype`. Establish `hker : ∀ u : S, u ∈ ψ.ker ↔ (u : A) ∈ P` using `fun u => by`. Simplify using `[ψ, AddMonoidHom.mem_ker, QuotientAddGroup.eq_zero_iff]`.

Set `ι' : S ⧸ ψ.ker →+ A ⧸ P` to `QuotientAddGroup.kerLift ψ`. Establish `hι : Function.Injective ι'` using `QuotientAddGroup.kerLift_injective ψ`. Set `j : S ⧸ ψ.ker → A ⧸ P` to `fun m => (a : A ⧸ P) + ι' m`. Establish `hj : Function.Injective j` using `fun m m' h => hι (add_left_cancel h)`. Establish `hjmk : ∀ u : S, j (u : S ⧸ ψ.ker) = ((a + u : A) : A ⧸ P)` using `fun u => by`.

Simplify using `[j, ι', ψ]`. Set `fb : S ⧸ ψ.ker → ℂ` to `fun m => f (m.out : A)`. Establish `hfb : ∀ u : S, fb (u : S ⧸ ψ.ker) = f u`. Introduce `u`. Establish `hk` using `(hker _).mp (quotient_out_sub_mem' ψ.ker u)`.

Establish `e : (((u : S ⧸ ψ.ker).out : S) : A) = u + (((u : S ⧸ ψ.ker).out - u : S) : A)` using `by simp`. Use `show f (((u : S ⧸ ψ.ker).out : S) : A) = f u`. Rewrite using `[e]`. Conclude with `hfper _ u.2 _ ((u : S ⧸ ψ.ker).out - u).2 hk`. Establish `hval : ∀ m, φ (j m).out = c * fb m`.

Introduce `m`. Take `⟨u, rfl⟩` from `QuotientAddGroup.mk_surjective m`. Rewrite using `[hjmk, hfb]`. Establish `hk` using `quotient_out_sub_mem' P (a + (u : A))`. Establish `e : ((a + (u : A) : A) : A ⧸ P).out = (a + u) + (((a + (u : A) : A) : A ⧸ P).out - (a + u))` using `by abel`.

Rewrite using `[e, hper _ _ hk, hφ, add_sub_cancel_left, if_pos u.2]`. Establish `hfbne : ∀ m, fb m ≠ 0` using `fun m h => by`. Establish `h1` using `(hf.1 _ (m.out).2).norm_eq_one`. Simplify using `[fb] at h`. Rewrite `h1` using `[h, norm_zero]`.

Conclude with `zero_ne_one h1`. Establish `hrange : Set.range j ⊆ Function.support (fun q : A ⧸ P => φ q.out)`. Introduce and unpack `_ ⟨m, rfl⟩`. Rewrite using `[Function.mem_support, hval]`. Conclude with `mul_ne_zero hc0 (hfbne m)`.

Establish `: Finite (S ⧸ ψ.ker)`. Use `hfin.to_subtype` as an intermediate fact. Conclude with `Finite.of_injective (fun m => (⟨j m, hrange ⟨m, rfl⟩⟩ : Function.support (fun q : A ⧸ P => φ q.out))) (fun m m' h => hj (congrArg Subtype.val h))`. Use `haveI := Fintype.ofFinite (S ⧸ ψ.ker)`. Establish `hsupp : Function.support (fun q : A ⧸ P => φ q.out) ⊆ Set.range j`.

Introduce `q hq`. Rewrite `hq` using `[Function.mem_support, hφ]`. Use `split_ifs at hq with hmem`. Use `⟨((⟨q.out - a, hmem⟩ : S) : S ⧸ ψ.ker), ?_⟩` and prove the remaining obligations. Rewrite using `[hjmk]`.

Simplify using the standard rewrite rules. Conclude with `absurd rfl hq`. Establish `hsum : ∑ᶠ q : A ⧸ P, φ q.out = c * ∑ m : S ⧸ ψ.ker, fb m`. Rewrite using `[← finsum_mem_univ, finsum_mem_inter_support_eq' _ Set.univ (Set.range j) (fun q hq => ⟨fun _ => hsupp hq, fun _ => Set.mem_univ q⟩), finsum_mem_range hj, finsum_eq_sum_of_fintype, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun m _ => hval m`.

Rewrite using `[hsum]`. Use `Ph.mul hc (GlobalTheory.T.isZeroOrPosMulRootOfUnity_finite_gaussSum (S ⧸ ψ.ker) fb ⟨fun x _ => hf.1 _ (x.out).2, fun x _ y _ z _ => ?_⟩)` and prove the remaining obligations. Take `⟨u, rfl⟩` from `QuotientAddGroup.mk_surjective x`. Take `⟨v, rfl⟩` from `QuotientAddGroup.mk_surjective y`. Take `⟨w, rfl⟩` from `QuotientAddGroup.mk_surjective z`.

Establish `h0 : fb 0 = f 0` using `by simpa using hfb 0`. Establish `e2 : ∀ x y : S, ((x : S ⧸ ψ.ker) + y) = ((x + y : S) : S ⧸ ψ.ker)` using `fun x y => rfl`. Rewrite using `[e2 u v, e2 (u + v) w, e2 v w, e2 u w, h0]`. Simplify using `only [hfb]`. Simplify using `using hf.2 _ u.2 _ v.2 _ w.2`.
-/
theorem ph_finsum_quotient {A : Type} [AddCommGroup A] (P S : AddSubgroup A) (φ f : A → ℂ) (c : ℂ) (a : A)
    (hper : ∀ x, ∀ y ∈ P, φ (x + y) = φ x)
    (hfin : (Function.support fun q : A ⧸ P => φ q.out).Finite)
    (hc : Ph c) (hf : Quad S f) (hφ : ∀ x, φ x = if x - a ∈ S then c * f (x - a) else 0) :
    Ph (∑ᶠ q : A ⧸ P, φ q.out) := by
  by_cases hc0 : c = 0
  · have h0 : ∀ x, φ x = 0 := fun x => by rw [hφ x]; split_ifs <;> simp [hc0]
    simp only [h0, finsum_zero]
    exact ph_zero

  have hfper : ∀ s ∈ S, ∀ t ∈ S, t ∈ P → f (s + t) = f s := by
    intro s hs t htS htP
    have h1 := hφ (a + (s + t))
    have h2 := hφ (a + s)
    rw [add_sub_cancel_left, if_pos (S.add_mem hs htS)] at h1
    rw [add_sub_cancel_left, if_pos hs] at h2
    have h3 : φ (a + (s + t)) = φ (a + s) := by rw [← add_assoc]; exact hper _ t htP
    exact mul_left_cancel₀ hc0 (h1.symm.trans (h3.trans h2))

  let ψ : S →+ A ⧸ P := (QuotientAddGroup.mk' P).comp S.subtype
  have hker : ∀ u : S, u ∈ ψ.ker ↔ (u : A) ∈ P := fun u => by
    simp [ψ, AddMonoidHom.mem_ker, QuotientAddGroup.eq_zero_iff]
  let ι' : S ⧸ ψ.ker →+ A ⧸ P := QuotientAddGroup.kerLift ψ
  have hι : Function.Injective ι' := QuotientAddGroup.kerLift_injective ψ
  let j : S ⧸ ψ.ker → A ⧸ P := fun m => (a : A ⧸ P) + ι' m
  have hj : Function.Injective j := fun m m' h => hι (add_left_cancel h)
  have hjmk : ∀ u : S, j (u : S ⧸ ψ.ker) = ((a + u : A) : A ⧸ P) := fun u => by
    simp [j, ι', ψ]
  let fb : S ⧸ ψ.ker → ℂ := fun m => f (m.out : A)
  have hfb : ∀ u : S, fb (u : S ⧸ ψ.ker) = f u := by
    intro u
    have hk := (hker _).mp (quotient_out_sub_mem' ψ.ker u)
    have e : (((u : S ⧸ ψ.ker).out : S) : A) = u + (((u : S ⧸ ψ.ker).out - u : S) : A) := by simp
    show f (((u : S ⧸ ψ.ker).out : S) : A) = f u
    rw [e]
    exact hfper _ u.2 _ ((u : S ⧸ ψ.ker).out - u).2 hk
  have hval : ∀ m, φ (j m).out = c * fb m := by
    intro m
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective m
    rw [hjmk, hfb]
    have hk := quotient_out_sub_mem' P (a + (u : A))
    have e : ((a + (u : A) : A) : A ⧸ P).out =
        (a + u) + (((a + (u : A) : A) : A ⧸ P).out - (a + u)) := by abel
    rw [e, hper _ _ hk, hφ, add_sub_cancel_left, if_pos u.2]
  have hfbne : ∀ m, fb m ≠ 0 := fun m h => by
    have h1 := (hf.1 _ (m.out).2).norm_eq_one
    simp [fb] at h
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hrange : Set.range j ⊆ Function.support (fun q : A ⧸ P => φ q.out) := by
    rintro _ ⟨m, rfl⟩
    rw [Function.mem_support, hval]
    exact mul_ne_zero hc0 (hfbne m)
  have : Finite (S ⧸ ψ.ker) := by
    have := hfin.to_subtype
    exact Finite.of_injective
      (fun m => (⟨j m, hrange ⟨m, rfl⟩⟩ : Function.support (fun q : A ⧸ P => φ q.out)))
      (fun m m' h => hj (congrArg Subtype.val h))
  haveI := Fintype.ofFinite (S ⧸ ψ.ker)

  have hsupp : Function.support (fun q : A ⧸ P => φ q.out) ⊆ Set.range j := by
    intro q hq
    rw [Function.mem_support, hφ] at hq
    split_ifs at hq with hmem
    · refine ⟨((⟨q.out - a, hmem⟩ : S) : S ⧸ ψ.ker), ?_⟩
      rw [hjmk]
      simp
    · exact absurd rfl hq
  have hsum : ∑ᶠ q : A ⧸ P, φ q.out = c * ∑ m : S ⧸ ψ.ker, fb m := by
    rw [← finsum_mem_univ, finsum_mem_inter_support_eq' _ Set.univ (Set.range j)
        (fun q hq => ⟨fun _ => hsupp hq, fun _ => Set.mem_univ q⟩), finsum_mem_range hj,
      finsum_eq_sum_of_fintype, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => hval m
  rw [hsum]
  refine Ph.mul hc (GlobalTheory.T.isZeroOrPosMulRootOfUnity_finite_gaussSum (S ⧸ ψ.ker) fb ⟨fun x _ => hf.1 _ (x.out).2, fun x _ y _ z _ => ?_⟩)
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective y
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective z
  have h0 : fb 0 = f 0 := by simpa using hfb 0
  have e2 : ∀ x y : S, ((x : S ⧸ ψ.ker) + y) = ((x + y : S) : S ⧸ ψ.ker) := fun x y => rfl
  rw [e2 u v, e2 (u + v) w, e2 v w, e2 u w, h0]
  simp only [hfb]
  simpa using hf.2 _ u.2 _ v.2 _ w.2

/- English proof (translation)
Introduce `κ ι _ _ _ φ hφ`. Take `⟨hsb, c, a, S, f, hc, hf, hφx⟩` from `hφ`. Establish `hR` using `hsb.choose_spec`. Unfold `haar`. Rewrite using `[dif_pos hsb]`.

Unfold `haarAt`. Use `Ph.mul ?_ (ph_finsum_quotient (perSub ℚ κ ι hsb.choose) S φ f c a (GlobalTheory.SW.HaarLevel.periodic hR.2) (GlobalTheory.SW.HaarLevel.finite_support hR.1 hR.2) hc hf hφx)` and prove the remaining obligations. Establish `h` using `GlobalTheory.T.complex_phase_calculus_rootOfUnity.2.2.1 (((hsb.choose : ℝ) ^ (Module.finrank ℚ ℚ * (Fintype.card κ * Fintype.card ι)))⁻¹)`. Use `h using 1` and compare the differences between its conclusion and the goal. Use `push_cast`.

Both sides reduce to the same expression.
-/
theorem ph_haar_of_shape : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι],
    ∀ φ : Matrix κ ι ℚ → ℂ, Shape φ → Ph (haar φ) := by
  intro κ ι _ _ _ φ hφ
  obtain ⟨hsb, c, a, S, f, hc, hf, hφx⟩ := hφ
  have hR := hsb.choose_spec
  unfold haar
  rw [dif_pos hsb]
  unfold haarAt
  refine Ph.mul ?_ (ph_finsum_quotient (perSub ℚ κ ι hsb.choose) S φ f c a
    (GlobalTheory.SW.HaarLevel.periodic hR.2) (GlobalTheory.SW.HaarLevel.finite_support hR.1 hR.2) hc hf hφx)

  have h := GlobalTheory.T.complex_phase_calculus_rootOfUnity.2.2.1
    (((hsb.choose : ℝ) ^ (Module.finrank ℚ ℚ * (Fintype.card κ * Fintype.card ι)))⁻¹)
  convert h using 1
  push_cast
  rfl

end GlobalTheory.Phase
