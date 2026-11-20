import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPrimitiveTiltedRootOfUnityLocalPeriodRingsData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRFiltrationLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisLogTeichmullerUniqueGaloisFrobeniusBdR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusFontaineTEqMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineTIsUnitBcrisAndUniformizerBdRPlus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalPeriodRingsDataUnramifiedLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcrisFrobeniusFixedFilZeroEqQp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.EigenDegree

/- English proof (translation)
Use `haveI : IsDomain B := hι.isDomain ι`. Establish `hprod : ∀ (d : ℕ → ℤ) (f : ℕ → D) (s : Finset ℕ), (∀ i ∈ s, F (d i) (f i)) → F (∑ i ∈ s, d i) (∏ i ∈ s, f i)`. Introduce `d f s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro _`.

Simplify using `using h1`. Consider the case `insert a s ha ih`. Introduce `h`. Rewrite using `[Finset.sum_insert ha, Finset.prod_insert ha]`. Conclude with `hmul _ _ _ _ (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.

Establish `hne : ∀ j, j < n → (⇑φ)^[j] x ≠ 0`. Introduce `j hj h`. Establish `e : (⇑φ)^[n] x = 0`. Rewrite using `[← Nat.sub_add_cancel hj.le, Function.iterate_add_apply, h, iterate_map_zero]`. Rewrite `e` using `[hx]`.

Conclude with `mul_ne_zero hp.ne_zero hx0 e`. Take `⟨N, hN⟩ : ∃ N, N = ∏ j ∈ Finset.range n, (⇑φ)^[j] x` from `⟨_, rfl⟩`. Establish `hN0 : N ≠ 0`. Rewrite using `[hN]`. Conclude with `Finset.prod_ne_zero_iff.2 fun j hj => hne j (Finset.mem_range.1 hj)`.

Establish `hφN : φ N = p * N`. Apply `mul_right_cancel₀ hx0` to reduce the goal to its premises. Establish `e1` using `Finset.prod_range_succ (fun j => (⇑φ)^[j] x) n`. Establish `e2` using `Finset.prod_range_succ' (fun j => (⇑φ)^[j] x) n`. Simplify using `only [Function.iterate_succ_apply', Function.iterate_zero_apply] at e2`.

Rewrite `e2` using `[← map_prod, ← hN, e1, ← hN, hx]`. Rewrite using `[← e2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hN1 : F 1 (ι N)`. Use `hprod (fun i => if i = 0 then 1 else 0) (fun i => ι ((⇑φ)^[i] x)) (Finset.range n) (by` as an intermediate fact.

Introduce `i hi`. Use `split_ifs with h`. Substitute `h` using the available equality. Conclude with `hx1`. Conclude with `hj0 i (Finset.mem_range.1 hi))`.

Rewrite `this` using `[← map_prod, ← hN]`. Simplify `this` using `[hn]`. Take `⟨s, hs⟩` from `ht.exists_right_inv`. Take `⟨z, hz, hz'⟩` from `hsucc _ hN1`. Establish `hb : t * (s * N) = N` using `by rw [← mul_assoc, hs, one_mul]`.

Establish `hφb : φ (s * N) = s * N`. Apply `(hp.mul ht).mul_left_cancel` to reduce the goal to its premises. Rewrite using `[← hφt, ← map_mul, hb, hφN, hφt, mul_assoc, hb]`. Establish `hbz : ι (s * N) = z`. Rewrite using `[map_mul, hz', ← mul_assoc, ← map_mul, mul_comm s, hs, map_one, one_mul]`.

Take `⟨c, hc, hc0⟩` from `hfund _ hφb (hbz ▸ hz) (fun h => hN0 (by rw [← hb, h, mul_zero]))`. Establish `htc : t = c * N`. Combine the equalities or inequalities in the displayed calculation. Establish `hNu : IsUnit N` using `isUnit_of_mul_isUnit_right (htc ▸ ht)`. Establish `hN2 : ¬ F 2 (ι N)`.

Introduce `h`. Apply `ht2` to reduce the goal to its premises. Use `hmul _ _ _ _ hc0 h` as an intermediate fact. Rewrite `this` using `[zero_add, ← map_mul, ← htc]`. Then use the resulting hypothesis. Establish `key : ∀ j, j < n → ¬ F ((if j = 0 then 1 else 0) + 1) (ι ((⇑φ)^[j] x))`.

Introduce `j hj h`. Apply `hN2` to reduce the goal to its premises. Use `hprod (fun i => (if i = 0 then 1 else 0) + (if i = j then 1 else 0)) (fun i => ι ((⇑φ)^[i] x)) (Finset.range n) (by` as an intermediate fact. Introduce `i hi`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using `using h`. Distinguish the cases in `h0 : i = 0`. Substitute `h0` using the available equality. Simplify `hx1` using `[hij]`.

Simplify `hj0 i (Finset.mem_range.1 hi))` using `[hij, h0]`. Rewrite `this` using `[← map_prod, ← hN, Finset.sum_add_distrib]`. Simplify `this` using `[hn, hj, one_add_one_eq_two]`. Use `⟨?_, ?_, fun j h0 hj => ?_⟩` and prove the remaining obligations. Use `isUnit_of_dvd_unit ?_ hNu` and prove the remaining obligations.

Rewrite using `[hN]`. Conclude with `Finset.dvd_prod_of_mem (fun j => (⇑φ)^[j] x) (Finset.mem_range.2 hn)`. Simplify `key 0 hn` using `[one_add_one_eq_two]`. Simplify `key j hj` using `[h0.ne']`.
-/
theorem abstract {B D : Type} [CommRing B] [CommRing D] [IsDomain D] (ι : B →+* D)
    (hι : Function.Injective ι) (φ : B →+* B) (F : ℤ → D → Prop) (h1 : F 0 1)
    (hmul : ∀ a b x y, F a x → F b y → F (a + b) (x * y)) (p t : B) (hp : IsUnit p) (ht : IsUnit t)
    (hφt : φ t = p * t) (ht2 : ¬ F 2 (ι t)) (hsucc : ∀ y, F 1 y → ∃ z, F 0 z ∧ y = ι t * z)
    (hfund : ∀ b, φ b = b → F 0 (ι b) → b ≠ 0 → ∃ c, c * b = 1 ∧ F 0 (ι c))
    (n : ℕ) (hn : 0 < n) (x : B) (hx : (⇑φ)^[n] x = p * x) (hx0 : x ≠ 0) (hx1 : F 1 (ι x))
    (hj0 : ∀ j, j < n → F 0 (ι ((⇑φ)^[j] x))) :
    IsUnit x ∧ ¬ F 2 (ι x) ∧ ∀ j, 0 < j → j < n → ¬ F 1 (ι ((⇑φ)^[j] x)) := by
  haveI : IsDomain B := hι.isDomain ι
  have hprod : ∀ (d : ℕ → ℤ) (f : ℕ → D) (s : Finset ℕ), (∀ i ∈ s, F (d i) (f i)) →
      F (∑ i ∈ s, d i) (∏ i ∈ s, f i) := by
    intro d f s
    induction s using Finset.induction_on with
    | empty => intro _; simpa using h1
    | insert a s ha ih =>
      intro h
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      exact hmul _ _ _ _ (h a (Finset.mem_insert_self _ _))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
  have hne : ∀ j, j < n → (⇑φ)^[j] x ≠ 0 := by
    intro j hj h
    have e : (⇑φ)^[n] x = 0 := by
      rw [← Nat.sub_add_cancel hj.le, Function.iterate_add_apply, h, iterate_map_zero]
    rw [hx] at e
    exact mul_ne_zero hp.ne_zero hx0 e
  obtain ⟨N, hN⟩ : ∃ N, N = ∏ j ∈ Finset.range n, (⇑φ)^[j] x := ⟨_, rfl⟩
  have hN0 : N ≠ 0 := by
    rw [hN]
    exact Finset.prod_ne_zero_iff.2 fun j hj => hne j (Finset.mem_range.1 hj)
  have hφN : φ N = p * N := by
    apply mul_right_cancel₀ hx0
    have e1 := Finset.prod_range_succ (fun j => (⇑φ)^[j] x) n
    have e2 := Finset.prod_range_succ' (fun j => (⇑φ)^[j] x) n
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply] at e2
    rw [← map_prod, ← hN, e1, ← hN, hx] at e2
    rw [← e2]
    ring
  have hN1 : F 1 (ι N) := by
    have := hprod (fun i => if i = 0 then 1 else 0) (fun i => ι ((⇑φ)^[i] x)) (Finset.range n) (by
      intro i hi
      split_ifs with h
      · subst h; exact hx1
      · exact hj0 i (Finset.mem_range.1 hi))
    rw [← map_prod, ← hN] at this
    simpa [hn] using this
  obtain ⟨s, hs⟩ := ht.exists_right_inv
  obtain ⟨z, hz, hz'⟩ := hsucc _ hN1
  have hb : t * (s * N) = N := by rw [← mul_assoc, hs, one_mul]
  have hφb : φ (s * N) = s * N := by
    apply (hp.mul ht).mul_left_cancel
    rw [← hφt, ← map_mul, hb, hφN, hφt, mul_assoc, hb]
  have hbz : ι (s * N) = z := by
    rw [map_mul, hz', ← mul_assoc, ← map_mul, mul_comm s, hs, map_one, one_mul]
  obtain ⟨c, hc, hc0⟩ := hfund _ hφb (hbz ▸ hz) (fun h => hN0 (by rw [← hb, h, mul_zero]))
  have htc : t = c * N := by
    calc t = t * (c * (s * N)) := by rw [hc, mul_one]
      _ = c * (t * (s * N)) := by ring
      _ = c * N := by rw [hb]
  have hNu : IsUnit N := isUnit_of_mul_isUnit_right (htc ▸ ht)
  have hN2 : ¬ F 2 (ι N) := by
    intro h
    apply ht2
    have := hmul _ _ _ _ hc0 h
    rwa [zero_add, ← map_mul, ← htc] at this
  have key : ∀ j, j < n → ¬ F ((if j = 0 then 1 else 0) + 1) (ι ((⇑φ)^[j] x)) := by
    intro j hj h
    apply hN2
    have := hprod (fun i => (if i = 0 then 1 else 0) + (if i = j then 1 else 0))
      (fun i => ι ((⇑φ)^[i] x)) (Finset.range n) (by
      intro i hi
      by_cases hij : i = j
      · subst hij
        simpa using h
      · by_cases h0 : i = 0
        · subst h0
          simpa [hij] using hx1
        · simpa [hij, h0] using hj0 i (Finset.mem_range.1 hi))
    rw [← map_prod, ← hN, Finset.sum_add_distrib] at this
    simpa [hn, hj, one_add_one_eq_two] using this
  refine ⟨?_, ?_, fun j h0 hj => ?_⟩
  · refine isUnit_of_dvd_unit ?_ hNu
    rw [hN]
    exact Finset.dvd_prod_of_mem (fun j => (⇑φ)^[j] x) (Finset.mem_range.2 hn)
  · simpa [one_add_one_eq_two] using key 0 hn
  · simpa [h0.ne'] using key j hj

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

/- English proof (translation)
Introduce `l _ C n hn x hx hx0 hx1 hj0`. Take `⟨-, h1, hmul, -, -, -, hP⟩` from `filD_laws l`. Take `⟨htu, -, ht2, hlu⟩` from `core_t_unit_fil l C`. Establish `he` using `core_isEps l C`. Establish `hlog` using `(LogFun.log_fun l C.ε C.t he.1 C.t_log).2.2.2 C.j C.j_cris`.

Use `haveI : IsDomain (Per.BdR l) := (BdRField.bdR_isField l).2.2.1.isDomain`. Use `abstract C.ι (ULaws.u_laws l C).2.2.2.1 (Per.φB l) (fun a y => y ∈ Per.FilD l a) h1 hmul (l : Per.Bcris l) (algebraMap (Per.Acris l) (Per.Bcris l) C.t) hlu htu ?_ ?_ ?_ ?_ n hn x hx hx0 hx1 hj0` and prove the remaining obligations. Rewrite using `[fund_phiB_alg, TPhi.t_phi l C, map_mul, map_natCast]`. Introduce `h`. Rewrite `h` using `[C.ι_j]`.

Conclude with `ht2 ((hP 2 _).1 h)`. Introduce `y hy`. Take `⟨z, hz, e⟩` from `(TiedUnif.filD_succ he hlog 0 y).1 (by rwa [zero_add])`. Conclude with `⟨z, hz, by rw [C.ι_j]; exact e⟩`. Introduce `b hb hb0 hne`.

Take `⟨c, rfl⟩` from `fundamental_exact l C b hb hb0`. Establish `hc : c ≠ 0`. Introduce and unpack `rfl`. Conclude with `hne (by rw [map_zero, map_zero])`. Use `⟨C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c⁻¹), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_mul, ← map_mul, inv_mul_cancel₀ hc, map_one, map_one]`. Use `show C.ι _ ∈ _`. Rewrite using `[C.ι_u]`. Conclude with `TiedUnif.alg_mem_FilD_zero _`.
-/
theorem main : ∀ (l : ℕ) [Fact l.Prime] (C : GlobalTheory.MemLoc.Core l) (n : ℕ), 0 < n → ∀ x : Per.Bcris l,
    (⇑(Per.φB l))^[n] x = (l : Per.Bcris l) * x → x ≠ 0 → C.ι x ∈ Per.FilD l 1 →
    (∀ j : ℕ, j < n → C.ι ((⇑(Per.φB l))^[j] x) ∈ Per.FilD l 0) →
    IsUnit x ∧ C.ι x ∉ Per.FilD l 2 ∧
      ∀ j : ℕ, 0 < j → j < n → C.ι ((⇑(Per.φB l))^[j] x) ∉ Per.FilD l 1 := by
  intro l _ C n hn x hx hx0 hx1 hj0
  obtain ⟨-, h1, hmul, -, -, -, hP⟩ := filD_laws l
  obtain ⟨htu, -, ht2, hlu⟩ := core_t_unit_fil l C
  have he := core_isEps l C
  have hlog := (LogFun.log_fun l C.ε C.t he.1 C.t_log).2.2.2 C.j C.j_cris
  haveI : IsDomain (Per.BdR l) := (BdRField.bdR_isField l).2.2.1.isDomain
  refine abstract C.ι (ULaws.u_laws l C).2.2.2.1 (Per.φB l) (fun a y => y ∈ Per.FilD l a) h1 hmul
    (l : Per.Bcris l) (algebraMap (Per.Acris l) (Per.Bcris l) C.t) hlu htu ?_ ?_ ?_ ?_ n hn x hx hx0 hx1 hj0
  · rw [fund_phiB_alg, TPhi.t_phi l C, map_mul, map_natCast]
  · intro h
    rw [C.ι_j] at h
    exact ht2 ((hP 2 _).1 h)
  · intro y hy
    obtain ⟨z, hz, e⟩ := (TiedUnif.filD_succ he hlog 0 y).1 (by rwa [zero_add])
    exact ⟨z, hz, by rw [C.ι_j]; exact e⟩
  · intro b hb hb0 hne
    obtain ⟨c, rfl⟩ := fundamental_exact l C b hb hb0
    have hc : c ≠ 0 := by
      rintro rfl
      exact hne (by rw [map_zero, map_zero])
    refine ⟨C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c⁻¹), ?_, ?_⟩
    · rw [← map_mul, ← map_mul, inv_mul_cancel₀ hc, map_one, map_one]
    · show C.ι _ ∈ _
      rw [C.ι_u]
      exact TiedUnif.alg_mem_FilD_zero _

end GlobalTheory.MemLoc.EigenDegree
