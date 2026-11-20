import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.FinInterNil

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Set `M : Submonoid E` to `{ carrier := {z | ∃ t : D, t ≠ 0 ∧ ∃ n : ℕ, z = algebraMap D E t * y ^ n} mul_mem' := by`. Introduce and unpack `a b ⟨t, ht, n, rfl⟩ ⟨t', ht', m, rfl⟩`. Conclude with `⟨t * t', mul_ne_zero ht ht', n + m, by rw [map_mul, pow_add]; ring⟩`.

Use the proof step `one_mem' := ⟨1, one_ne_zero, 0, by simp⟩ }`. Establish `h0 : (0 : E) ∉ M`. Introduce and unpack `⟨t, ht, n, hz⟩`. Apply `hcon t ht` to reduce the goal to its premises. Use `⟨n + 1, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Establish `hdisj : Disjoint ((⊥ : Ideal E) : Set E) (M : Set E)`. Rewrite using `[Set.disjoint_left]`. Introduce `z hz hzM`. Establish `hz0 : z = 0` using `by simpa using hz`.

Conclude with `h0 (hz0 ▸ hzM)`. Take `⟨Q, hQ, -, hQM⟩` from `Ideal.exists_le_prime_disjoint ⊥ M hdisj`. Establish `hcomap : Q.comap (algebraMap D E) = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `t ht`.

Rewrite using `[Ideal.mem_bot]`. Assume the negation of the conclusion as `htne`. Establish `hm : algebraMap D E t ∈ M` using `⟨t, htne, 0, by simp⟩`. Conclude with `Set.disjoint_left.mp hQM (Ideal.mem_comap.mp ht) hm`. Establish `hyQ` using `hy Q hQ hcomap`.

Establish `hm : y ∈ M` using `⟨1, one_ne_zero, 1, by simp⟩`. Conclude with `Set.disjoint_left.mp hQM hyQ hm`.
-/
theorem exists_ne_zero_isNilpotent_mul {D E : Type} [CommRing D] [IsDomain D] [CommRing E]
    [Algebra D E] (y : E)
    (hy : ∀ Q : Ideal E, Q.IsPrime → Q.comap (algebraMap D E) = ⊥ → y ∈ Q) :
    ∃ t : D, t ≠ 0 ∧ IsNilpotent (algebraMap D E t * y) := by
  by_contra hcon
  push_neg at hcon
  let M : Submonoid E :=
    { carrier := {z | ∃ t : D, t ≠ 0 ∧ ∃ n : ℕ, z = algebraMap D E t * y ^ n}
      mul_mem' := by
        rintro a b ⟨t, ht, n, rfl⟩ ⟨t', ht', m, rfl⟩
        exact ⟨t * t', mul_ne_zero ht ht', n + m, by rw [map_mul, pow_add]; ring⟩
      one_mem' := ⟨1, one_ne_zero, 0, by simp⟩ }
  have h0 : (0 : E) ∉ M := by
    rintro ⟨t, ht, n, hz⟩
    apply hcon t ht
    refine ⟨n + 1, ?_⟩
    calc (algebraMap D E t * y) ^ (n + 1)
        = algebraMap D E t ^ n * y * (algebraMap D E t * y ^ n) := by ring
      _ = 0 := by rw [← hz, mul_zero]
  have hdisj : Disjoint ((⊥ : Ideal E) : Set E) (M : Set E) := by
    rw [Set.disjoint_left]
    intro z hz hzM
    have hz0 : z = 0 := by simpa using hz
    exact h0 (hz0 ▸ hzM)
  obtain ⟨Q, hQ, -, hQM⟩ := Ideal.exists_le_prime_disjoint ⊥ M hdisj
  have hcomap : Q.comap (algebraMap D E) = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    rw [Ideal.mem_bot]
    by_contra htne
    have hm : algebraMap D E t ∈ M := ⟨t, htne, 0, by simp⟩
    exact Set.disjoint_left.mp hQM (Ideal.mem_comap.mp ht) hm
  have hyQ := hy Q hQ hcomap
  have hm : y ∈ M := ⟨1, one_ne_zero, 1, by simp⟩
  exact Set.disjoint_left.mp hQM hyQ hm

/- English proof (translation)
Introduce `D E _ _ _ _ ι X P hFG hQ`. Establish `hstep : ∀ y ∈ (⨅ i ∈ X, P i), ∃ t : D, t ≠ 0 ∧ IsNilpotent (algebraMap D E t * y)` using `fun y hy => exists_ne_zero_isNilpotent_mul y (fun Q hQp hQc => hQ Q hQp hQc hy)`. Establish `hJfg : (∏ i ∈ X, P i).FG`. Use `Finset.prod_induction P (fun J : Ideal E => J.FG) (fun a b ha hb => ha.mul hb) ?_ hFG` and prove the remaining obligations. Conclude with `⟨{1}, by simp⟩`.

Establish `hJI : ∀ g ∈ ∏ i ∈ X, P i, g ∈ (⨅ i ∈ X, P i)`. Introduce `g hg`. Simplify using `only [Submodule.mem_iInf]`. Introduce `i hi`. Conclude with `(Ideal.prod_le_inf.trans (Finset.inf_le hi)) hg`.

Take `⟨S, hS⟩` from `hJfg`. Establish `hSI : ∀ g : S, (g : E) ∈ (⨅ i ∈ X, P i)` using `fun g => hJI g (hS ▸ Submodule.subset_span g.2)`. Use `choose t ht using fun g : S => hstep g.1 (hSI g)`. Use `⟨∏ g : S, t g, Finset.prod_ne_zero_iff.mpr (fun g _ => (ht g).1), ?_⟩` and prove the remaining obligations. Use `set s := ∏ g : S, t g with hs`.

Set `K : Ideal E` to `Submodule.comap (LinearMap.mulLeft E (algebraMap D E s)) (nilradical E)`. Establish `hK : ∀ z, z ∈ K ↔ IsNilpotent (algebraMap D E s * z)`. Introduce `z`. Simplify using `[K, mem_nilradical]`. Establish `hJK : (∏ i ∈ X, P i) ≤ K`.

Rewrite using `[← hS, Submodule.span_le]`. Introduce `g hg`. Rewrite using `[SetLike.mem_coe, hK]`. Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem t (Finset.mem_univ (⟨g, hg⟩ : S))`. Establish `he : algebraMap D E s * g = algebraMap D E c * (algebraMap D E (t ⟨g, hg⟩) * g)`.

Rewrite using `[hs, hc, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he]`. Conclude with `(Commute.all _ _).isNilpotent_mul_left (ht ⟨g, hg⟩).2`. Introduce `y hy`.

Establish `hyN : y ^ X.card ∈ ∏ i ∈ X, P i`. Use `Ideal.prod_mem_prod (s := X) (I := P) (x := fun _ => y) (fun i hi => by` as an intermediate fact. Use `hy` as an intermediate fact. Simplify using `only [Submodule.mem_iInf] at this`. Conclude with `this i hi)`.

Simplify `this` using `[Finset.prod_const]`. Establish `hn` using `(hK _).mp (hJK hyN)`. Establish `hpow : IsNilpotent ((algebraMap D E s * y) ^ (X.card + 1))`. Establish `he : (algebraMap D E s * y) ^ (X.card + 1) = (algebraMap D E s ^ X.card * y) * (algebraMap D E s * y ^ X.card)` using `by ring`. Rewrite using `[he]`.

Conclude with `(Commute.all _ _).isNilpotent_mul_left hn`. Take `⟨k, hk⟩` from `hpow`. Conclude with `⟨(X.card + 1) * k, by rw [pow_mul, hk]⟩`.
-/
theorem main : ∀ (D E : Type) [CommRing D] [IsDomain D] [CommRing E] [Algebra D E] (ι : Type)
    (X : Finset ι) (P : ι → Ideal E), (∀ i ∈ X, (P i).FG) →
    (∀ Q : Ideal E, Q.IsPrime → Q.comap (algebraMap D E) = ⊥ → (⨅ i ∈ X, P i) ≤ Q) →
    ∃ s : D, s ≠ 0 ∧ ∀ y ∈ (⨅ i ∈ X, P i), IsNilpotent (algebraMap D E s * y) := by
  intro D E _ _ _ _ ι X P hFG hQ
  classical
  have hstep : ∀ y ∈ (⨅ i ∈ X, P i), ∃ t : D, t ≠ 0 ∧ IsNilpotent (algebraMap D E t * y) :=
    fun y hy => exists_ne_zero_isNilpotent_mul y (fun Q hQp hQc => hQ Q hQp hQc hy)
  have hJfg : (∏ i ∈ X, P i).FG := by
    refine Finset.prod_induction P (fun J : Ideal E => J.FG) (fun a b ha hb => ha.mul hb) ?_ hFG
    exact ⟨{1}, by simp⟩
  have hJI : ∀ g ∈ ∏ i ∈ X, P i, g ∈ (⨅ i ∈ X, P i) := by
    intro g hg
    simp only [Submodule.mem_iInf]
    intro i hi
    exact (Ideal.prod_le_inf.trans (Finset.inf_le hi)) hg
  obtain ⟨S, hS⟩ := hJfg
  have hSI : ∀ g : S, (g : E) ∈ (⨅ i ∈ X, P i) := fun g =>
    hJI g (hS ▸ Submodule.subset_span g.2)
  choose t ht using fun g : S => hstep g.1 (hSI g)
  refine ⟨∏ g : S, t g, Finset.prod_ne_zero_iff.mpr (fun g _ => (ht g).1), ?_⟩
  set s := ∏ g : S, t g with hs
  let K : Ideal E := Submodule.comap (LinearMap.mulLeft E (algebraMap D E s)) (nilradical E)
  have hK : ∀ z, z ∈ K ↔ IsNilpotent (algebraMap D E s * z) := by
    intro z
    simp [K, mem_nilradical]
  have hJK : (∏ i ∈ X, P i) ≤ K := by
    rw [← hS, Submodule.span_le]
    intro g hg
    rw [SetLike.mem_coe, hK]
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem t (Finset.mem_univ (⟨g, hg⟩ : S))
    have he : algebraMap D E s * g = algebraMap D E c * (algebraMap D E (t ⟨g, hg⟩) * g) := by
      rw [hs, hc, map_mul]; ring
    rw [he]
    exact (Commute.all _ _).isNilpotent_mul_left (ht ⟨g, hg⟩).2
  intro y hy
  have hyN : y ^ X.card ∈ ∏ i ∈ X, P i := by
    have := Ideal.prod_mem_prod (s := X) (I := P) (x := fun _ => y) (fun i hi => by
      have := hy
      simp only [Submodule.mem_iInf] at this
      exact this i hi)
    simpa [Finset.prod_const] using this
  have hn := (hK _).mp (hJK hyN)
  have hpow : IsNilpotent ((algebraMap D E s * y) ^ (X.card + 1)) := by
    have he : (algebraMap D E s * y) ^ (X.card + 1)
        = (algebraMap D E s ^ X.card * y) * (algebraMap D E s * y ^ X.card) := by ring
    rw [he]
    exact (Commute.all _ _).isNilpotent_mul_left hn
  obtain ⟨k, hk⟩ := hpow
  exact ⟨(X.card + 1) * k, by rw [pow_mul, hk]⟩

end GlobalTheory.FinInterNil
