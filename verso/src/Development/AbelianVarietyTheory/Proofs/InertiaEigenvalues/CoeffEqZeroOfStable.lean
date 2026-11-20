import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.UnramDisjoint

/- English proof (translation)
It suffices to establish `H : ∀ n : ℕ, ∀ c : ι → Ω, (Finset.univ.filter (fun i => c i ≠ 0)).card = n → (∀ i, c i ∈ N) → ∑ i, c i * x i = 0 → ∀ i, c i = 0 from H _ c rfl hc h`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `c hcard hc h`.

Assume the negation of the conclusion as `hne`. Take `⟨j, hj⟩` from `not_forall.mp hne`. Use `set d : ι → Ω := fun i => c i * (c j)⁻¹ with hd`. Establish `hdN : ∀ i, d i ∈ N` using `fun i => N.mul_mem (hc i) (N.inv_mem (hc j))`. Establish `hdj : d j = 1` using `mul_inv_cancel₀ hj`.

Establish `hdsum : ∑ i, d i * x i = 0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl (fun i _ => by simp only [hd]; ring)`. Use `_ = 0 := by rw [h, zero_mul]`.

Establish `hfix : ∀ g ∈ K.fixingSubgroup, ∀ i, g (d i) = d i`. Introduce `g hg`. Establish `hgx : ∀ i, g (x i) = x i` using `fun i => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _ (hx i)`. Use `set e : ι → Ω := fun i => g (d i) - d i with he`. Establish `heN : ∀ i, e i ∈ N` using `fun i => N.sub_mem (hN g _ (hdN i)) (hdN i)`.

Establish `h2 : ∑ i, g (d i) * x i = 0`. Use `congrArg g hdsum` as an intermediate fact. Rewrite `this` using `[map_sum, map_zero]`. Simplify `this` using `only [map_mul, hgx]`. Establish `hesum : ∑ i, e i * x i = 0`.

Simplify using `only [he, sub_mul, Finset.sum_sub_distrib, h2, hdsum, sub_zero]`. Establish `hej : e j = 0` using `by simp only [he, hdj, map_one, sub_self]`. Establish `hlt : (Finset.univ.filter (fun i => e i ≠ 0)).card < n`. Rewrite using `[← hcard]`. Apply `Finset.card_lt_card` to reduce the goal to its premises.

Use `(Finset.ssubset_iff_of_subset ?_).mpr ⟨j, ?_, ?_⟩` and prove the remaining obligations. Introduce `i hi`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢`. Introduce `hci`. Apply `hi` to reduce the goal to its premises.

Establish `hdi : d i = 0` using `by simp only [hd, hci, zero_mul]`. Simplify using `only [he, hdi, map_zero, sub_zero]`. Simplify using `[hj]`. Simplify using `[hej]`. Introduce `i`.

Conclude with `sub_eq_zero.mp (ih _ hlt e rfl heN hesum i)`. Establish `hdK : ∀ i, d i ∈ K`. Introduce `i`. Rewrite using `[← InfiniteGalois.fixedField_fixingSubgroup K, IntermediateField.mem_fixedField_iff]`. Conclude with `fun g hg => hfix g hg i`.

Establish `h0` using `hind d (fun i => ⟨hdK i, hdN i⟩) hdsum j`. Rewrite `h0` using `[hdj]`. Conclude with `one_ne_zero h0`.
-/
theorem coeff_eq_zero_of_stable {F Ω ι : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
    [Fintype ι] (K N : IntermediateField F Ω)
    (hN : ∀ (g : Ω ≃ₐ[F] Ω) (y : Ω), y ∈ N → g y ∈ N) (x : ι → Ω) (hx : ∀ i, x i ∈ K)
    (hind : ∀ c : ι → Ω, (∀ i, c i ∈ K ⊓ N) → ∑ i, c i * x i = 0 → ∀ i, c i = 0)
    (c : ι → Ω) (hc : ∀ i, c i ∈ N) (h : ∑ i, c i * x i = 0) : ∀ i, c i = 0 := by
  classical
  suffices H : ∀ n : ℕ, ∀ c : ι → Ω, (Finset.univ.filter (fun i => c i ≠ 0)).card = n →
      (∀ i, c i ∈ N) → ∑ i, c i * x i = 0 → ∀ i, c i = 0 from H _ c rfl hc h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c hcard hc h
  by_contra hne
  obtain ⟨j, hj⟩ := not_forall.mp hne

  set d : ι → Ω := fun i => c i * (c j)⁻¹ with hd
  have hdN : ∀ i, d i ∈ N := fun i => N.mul_mem (hc i) (N.inv_mem (hc j))
  have hdj : d j = 1 := mul_inv_cancel₀ hj
  have hdsum : ∑ i, d i * x i = 0 := by
    calc ∑ i, d i * x i = (∑ i, c i * x i) * (c j)⁻¹ := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun i _ => by simp only [hd]; ring)
      _ = 0 := by rw [h, zero_mul]

  have hfix : ∀ g ∈ K.fixingSubgroup, ∀ i, g (d i) = d i := by
    intro g hg
    have hgx : ∀ i, g (x i) = x i := fun i => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _ (hx i)
    set e : ι → Ω := fun i => g (d i) - d i with he
    have heN : ∀ i, e i ∈ N := fun i => N.sub_mem (hN g _ (hdN i)) (hdN i)
    have h2 : ∑ i, g (d i) * x i = 0 := by
      have := congrArg g hdsum
      rw [map_sum, map_zero] at this
      simpa only [map_mul, hgx] using this
    have hesum : ∑ i, e i * x i = 0 := by
      simp only [he, sub_mul, Finset.sum_sub_distrib, h2, hdsum, sub_zero]
    have hej : e j = 0 := by simp only [he, hdj, map_one, sub_self]
    have hlt : (Finset.univ.filter (fun i => e i ≠ 0)).card < n := by
      rw [← hcard]
      apply Finset.card_lt_card
      refine (Finset.ssubset_iff_of_subset ?_).mpr ⟨j, ?_, ?_⟩
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        intro hci
        apply hi
        have hdi : d i = 0 := by simp only [hd, hci, zero_mul]
        simp only [he, hdi, map_zero, sub_zero]
      · simp [hj]
      · simp [hej]
    intro i
    exact sub_eq_zero.mp (ih _ hlt e rfl heN hesum i)

  have hdK : ∀ i, d i ∈ K := by
    intro i
    rw [← InfiniteGalois.fixedField_fixingSubgroup K, IntermediateField.mem_fixedField_iff]
    exact fun g hg => hfix g hg i
  have h0 := hind d (fun i => ⟨hdK i, hdN i⟩) hdsum j
  rw [hdj] at h0
  exact one_ne_zero h0

/- English proof (translation)
Use `delta MaximalUnramifiedExtension at hy ⊢`. Establish `hmap : (IntermediateField.adjoin ℚ_[l] {x : PadicAlgCl l | ∃ m, 0 < m ∧ ¬l ∣ m ∧ x ^ m = 1}).map (g : PadicAlgCl l →ₐ[ℚ_[l]] PadicAlgCl l) ≤ IntermediateField.adjoin ℚ_[l] {x : PadicAlgCl l | ∃ m, 0 < m ∧ ¬l ∣ m ∧ x ^ m = 1}`. Rewrite using `[IntermediateField.adjoin_map]`. Apply `IntermediateField.adjoin.mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨z, ⟨m, hm, hl, hz⟩, rfl⟩`.

Conclude with `⟨m, hm, hl, by rw [← map_pow, hz, map_one]⟩`. Conclude with `hmap ⟨y, hy, rfl⟩`.
-/
theorem apply_mem_Kur {l : ℕ} [Fact l.Prime] (g : GQ l) (y : Om l) (hy : y ∈ MaximalUnramifiedExtension l) :
    g y ∈ MaximalUnramifiedExtension l := by
  delta MaximalUnramifiedExtension at hy ⊢
  have hmap : (IntermediateField.adjoin ℚ_[l] {x : PadicAlgCl l | ∃ m, 0 < m ∧ ¬l ∣ m ∧ x ^ m = 1}).map
      (g : PadicAlgCl l →ₐ[ℚ_[l]] PadicAlgCl l) ≤
      IntermediateField.adjoin ℚ_[l] {x : PadicAlgCl l | ∃ m, 0 < m ∧ ¬l ∣ m ∧ x ^ m = 1} := by
    rw [IntermediateField.adjoin_map]
    apply IntermediateField.adjoin.mono
    rintro _ ⟨z, ⟨m, hm, hl, hz⟩, rfl⟩
    exact ⟨m, hm, hl, by rw [← map_pow, hz, map_one]⟩
  exact hmap ⟨y, hy, rfl⟩

/- English proof (translation)
Rewrite `hx`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `a ha`. Establish `hcoe : ∀ z : ↥(K0 K), ((algebraMap ↥(K0 K) ↥K.1 z : ↥K.1) : Om l) = z` using `fun z => rfl`. Establish `hzero` using `coeff_eq_zero_of_stable (F := ℚ_[l]) K.1 (MaximalUnramifiedExtension l) (fun g y hy => apply_mem_Kur g y hy) (fun i => (x i : Om l)) (fun i => (x i).2) (fun c hc hsum => by`. Establish `hc0` using `hx (fun i => ⟨c i, hc i⟩) (by`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify `hsum)` using `[Algebra.smul_def, hcoe]`. Introduce `i`. Simplify using `using congrArg Subtype.val (hc0 i))`. Use the proof step `(fun i => (a i : Om l)) (fun i => (a i).2)`.

Use the proof step `(by simpa [Algebra.smul_def] using ha)`. Introduce `i`. Conclude with `Subtype.ext (hzero i)`.
-/
theorem linearIndependent_Kur (l : ℕ) [Fact l.Prime] (K : FinExt l) (m : ℕ) (x : Fin m → ↥K.1)
    (hx : LinearIndependent ↥(K0 K) x) :
    LinearIndependent ↥(MaximalUnramifiedExtension l) (fun i => (x i : Om l)) := by
  rw [Fintype.linearIndependent_iff] at hx ⊢
  intro a ha
  have hcoe : ∀ z : ↥(K0 K), ((algebraMap ↥(K0 K) ↥K.1 z : ↥K.1) : Om l) = z := fun z => rfl
  have hzero := coeff_eq_zero_of_stable (F := ℚ_[l]) K.1 (MaximalUnramifiedExtension l) (fun g y hy => apply_mem_Kur g y hy)
    (fun i => (x i : Om l)) (fun i => (x i).2)
    (fun c hc hsum => by
      have hc0 := hx (fun i => ⟨c i, hc i⟩) (by
        apply Subtype.ext
        simpa [Algebra.smul_def, hcoe] using hsum)
      intro i
      simpa using congrArg Subtype.val (hc0 i))
    (fun i => (a i : Om l)) (fun i => (a i).2)
    (by simpa [Algebra.smul_def] using ha)
  intro i
  exact Subtype.ext (hzero i)

end GlobalTheory.UnramDisjoint
