import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

namespace GlobalTheory.CompanionTheory.Ar.Tw

/- English proof (translation)
Set `F` to `FractionRing D`. Set `g : Polynomial F` to `Polynomial.X ^ 2 + Polynomial.C (p : F)`. Establish `hmonic : g.Monic` using `Polynomial.monic_X_pow_add_C _ (by norm_num)`. Establish `hdeg : g.natDegree = 2` using `Polynomial.natDegree_X_pow_add_C`. Establish `hinjF : Function.Injective (algebraMap D F)` using `IsFractionRing.injective D F`.

Establish `hnr : ∀ r : F, r ^ 2 + (p : F) ≠ 0`. Introduce `r hr`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := D) r`. Establish `hb0 : algebraMap D F b ≠ 0`. Introduce `h0`.

Conclude with `nonZeroDivisors.ne_zero hb (hinjF (by simpa using h0))`. Establish `h1 : algebraMap D F (a ^ 2 + (p : D) * b ^ 2) = 0`. Simplify using `only [map_add, map_mul, map_pow, map_natCast]`. Establish `e : algebraMap D F a ^ 2 + (p : F) * algebraMap D F b ^ 2 = ((algebraMap D F a / algebraMap D F b) ^ 2 + (p : F)) * algebraMap D F b ^ 2`. Rewrite using `[div_pow, add_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hb0)]`.

Rewrite using `[e, hr, zero_mul]`. Establish `h2 : a ^ 2 + (p : D) * b ^ 2 = 0` using `hinjF (by simpa using h1)`. Conclude with `hb0 (by rw [h a b h2, map_zero])`. Establish `hirr : Irreducible g`. Rewrite using `[hmonic.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]`.

Use `Multiset.eq_zero_of_forall_notMem fun r hr => ?_` and prove the remaining obligations. Use `(Polynomial.mem_roots'.mp hr).2` as an intermediate fact. Simplify using `[g, Polynomial.IsRoot] at this`. Conclude with `hnr r this`. Use `haveI : Fact (Irreducible g) := ⟨hirr⟩`.

Use `⟨AdjoinRoot g, inferInstance, (AdjoinRoot.of g).comp (algebraMap D F), AdjoinRoot.root g, ?_, ?_⟩` and prove the remaining obligations. Establish `h0 : AdjoinRoot.mk g (Polynomial.X ^ 2 + Polynomial.C (p : F)) = 0` using `AdjoinRoot.mk_self`. Rewrite `h0` using `[map_add, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, map_natCast]`. Take the linear combination `h0`. Introduce `u v huv`.

Establish `h1 : AdjoinRoot.mk g (Polynomial.C (algebraMap D F u) + Polynomial.C (algebraMap D F v) * Polynomial.X) = 0`. Simplify using `using huv`. Rewrite `h1` using `[AdjoinRoot.mk_eq_zero]`. Establish `h2` using `Polynomial.eq_zero_of_dvd_of_degree_lt h1 (by`. Rewrite using `[Polynomial.degree_eq_natDegree hmonic.ne_zero, hdeg]`.

Use `compute_degree`. Conclude with `(by norm_num : 1 < 2))` after adjusting the coercions. Establish `hu` using `congrArg (fun t => Polynomial.coeff t 0) h2`. Establish `hv` using `congrArg (fun t => Polynomial.coeff t 1) h2`. Simplify using `at hu hv`.

Conclude with `⟨hu, hv⟩`.
-/
theorem exists_root_field {D : Type} [CommRing D] [IsDomain D] (p : ℕ)
    (h : ∀ a b : D, a ^ 2 + (p : D) * b ^ 2 = 0 → b = 0) :
    ∃ (E : Type) (_ : Field E) (i : D →+* E) (s : E), s ^ 2 = -(p : E) ∧
      ∀ u v : D, i u + i v * s = 0 → u = 0 ∧ v = 0 := by
  classical
  let F := FractionRing D
  let g : Polynomial F := Polynomial.X ^ 2 + Polynomial.C (p : F)
  have hmonic : g.Monic := Polynomial.monic_X_pow_add_C _ (by norm_num)
  have hdeg : g.natDegree = 2 := Polynomial.natDegree_X_pow_add_C
  have hinjF : Function.Injective (algebraMap D F) := IsFractionRing.injective D F
  have hnr : ∀ r : F, r ^ 2 + (p : F) ≠ 0 := by
    intro r hr
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := D) r
    have hb0 : algebraMap D F b ≠ 0 := by
      intro h0
      exact nonZeroDivisors.ne_zero hb (hinjF (by simpa using h0))
    have h1 : algebraMap D F (a ^ 2 + (p : D) * b ^ 2) = 0 := by
      simp only [map_add, map_mul, map_pow, map_natCast]
      have e : algebraMap D F a ^ 2 + (p : F) * algebraMap D F b ^ 2 =
          ((algebraMap D F a / algebraMap D F b) ^ 2 + (p : F)) * algebraMap D F b ^ 2 := by
        rw [div_pow, add_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hb0)]
      rw [e, hr, zero_mul]
    have h2 : a ^ 2 + (p : D) * b ^ 2 = 0 := hinjF (by simpa using h1)
    exact hb0 (by rw [h a b h2, map_zero])
  have hirr : Irreducible g := by
    rw [hmonic.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
    refine Multiset.eq_zero_of_forall_notMem fun r hr => ?_
    have := (Polynomial.mem_roots'.mp hr).2
    simp [g, Polynomial.IsRoot] at this
    exact hnr r this
  haveI : Fact (Irreducible g) := ⟨hirr⟩
  refine ⟨AdjoinRoot g, inferInstance, (AdjoinRoot.of g).comp (algebraMap D F), AdjoinRoot.root g, ?_, ?_⟩
  · have h0 : AdjoinRoot.mk g (Polynomial.X ^ 2 + Polynomial.C (p : F)) = 0 := AdjoinRoot.mk_self
    rw [map_add, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, map_natCast] at h0
    linear_combination h0
  · intro u v huv
    have h1 : AdjoinRoot.mk g (Polynomial.C (algebraMap D F u) +
        Polynomial.C (algebraMap D F v) * Polynomial.X) = 0 := by
      simpa using huv
    rw [AdjoinRoot.mk_eq_zero] at h1
    have h2 := Polynomial.eq_zero_of_dvd_of_degree_lt h1 (by
      rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, hdeg]
      compute_degree
      exact_mod_cast (by norm_num : 1 < 2))
    have hu := congrArg (fun t => Polynomial.coeff t 0) h2
    have hv := congrArg (fun t => Polynomial.coeff t 1) h2
    simp at hu hv
    exact ⟨hu, hv⟩

/- English proof (translation)
Use `haveI : IsDomain (MRing ι ⧸ W) := Ideal.Quotient.isDomain W`. Establish `hD : ∀ a b : MRing ι ⧸ W, a ^ 2 + (p : MRing ι ⧸ W) * b ^ 2 = 0 → b = 0`. Introduce `a b h`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective b`.

Rewrite using `[Ideal.Quotient.eq_zero_iff_mem]`. Apply `hN a` to reduce the goal to its premises. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Simplify using `using h`. Take `⟨E, _, i, s, hs, hind⟩` from `exists_root_field p hD`.

Set `φ : MRing (Tb ι) →+* Polynomial E` to `(aeval (fun q : Σ o, Tb ι o => match q with`. Consider the case `⟨none, j⟩ => if j = (0 : Fin 2) then Polynomial.C s * Polynomial.X else Polynomial.X`. Consider the case `⟨some k, l⟩ => Polynomial.C (i (Ideal.Quotient.mk W (X ⟨k, l⟩)))) : MRing (Tb ι) →ₐ[ℤ] Polynomial E).toRingHom`. Establish `hinc : ∀ f : MRing ι, φ (inc f) = Polynomial.C (i (Ideal.Quotient.mk W f))`. Introduce `f`.

Establish `: (φ.comp inc) = (Polynomial.C.comp (i.comp (Ideal.Quotient.mk W)))`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using `[φ, inc]`. Introduce `l`.

Simplify using `[φ, inc, oldIdx]`. Conclude with `congrArg (fun g => g f) this`. Establish `hx : φ xN = Polynomial.C s * Polynomial.X`. Simplify using `only [φ, xN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]`. Conclude with `if_pos rfl`.

Establish `hy : φ yN = Polynomial.X`. Simplify using `only [φ, yN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]`. Conclude with `if_neg (show ¬ ((1 : Fin 2) = 0) by decide)`. Establish `hCp : φ (C (p : ℤ)) = (p : Polynomial E)`. Simplify using `[φ]`.

Establish `hle : twist p W ≤ RingHom.ker φ`. Use `sup_le (Ideal.map_le_iff_le_comap.mpr fun f hf => ?_) ?_` and prove the remaining obligations. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, hinc, Ideal.Quotient.eq_zero_iff_mem.mpr hf]`. Simplify using the standard rewrite rules. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff] show quad p ∈ RingHom.ker φ`.

Rewrite using `[RingHom.mem_ker]`. Simplify using `only [quad, map_add, map_mul, map_pow, hx, hy, hCp]`. Establish `hs' : (Polynomial.C s) ^ 2 = -(p : Polynomial E)`. Rewrite using `[← map_pow, hs]`. Simplify using the standard rewrite rules.

Take the linear combination `(Polynomial.X ^ 2 : Polynomial E) * hs'`. Set `φ' : (MRing (Tb ι) ⧸ twist p W) →+* Polynomial E` to `Ideal.Quotient.lift _ φ (fun a ha => hle ha)`. Set `mk'` to `Ideal.Quotient.mk (twist p W)`. Establish `hWle : ∀ a ∈ W, (mk'.comp inc) a = 0`. Introduce `a ha`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha))`. Set `τ : (MRing ι ⧸ W) →+* (MRing (Tb ι) ⧸ twist p W)` to `Ideal.Quotient.lift W (mk'.comp inc) hWle`. Set `σ : Polynomial (MRing ι ⧸ W) →+* (MRing (Tb ι) ⧸ twist p W)` to `Polynomial.eval₂RingHom τ (mk' yN)`. Establish `hσC : ∀ d, σ (Polynomial.C d) = τ d` using `fun d => by simp [σ]`. Establish `hσX : σ Polynomial.X = mk' yN` using `by simp [σ]`.

Establish `hxx : mk' xN * mk' xN = σ (-(p : Polynomial (MRing ι ⧸ W)) * Polynomial.X ^ 2)`. Establish `hq : mk' (quad p) = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))`. Simplify using `only [quad, map_add, map_mul, map_pow] at hq`. Establish `hc : mk' (C (p : ℤ)) = (p : MRing (Tb ι) ⧸ twist p W)` using `by simp [mk']`. Rewrite `hq` using `[hc]`.

Simplify using `only [map_mul, map_neg, map_natCast, map_pow, hσX]`. Take the linear combination `hq`. Establish `hform : ∀ f : MRing (Tb ι), ∃ a b : Polynomial (MRing ι ⧸ W), mk' f = σ a + σ b * mk' xN`. Introduce `f`. Proceed by induction on `f using MvPolynomial.induction_on with`.

Consider the case `C n`. Use `⟨(n : Polynomial (MRing ι ⧸ W)), 0, ?_⟩` and prove the remaining obligations. Simplify using `[mk']`. Consider the case `add f g hf hg`. Take `⟨a, b, h1⟩` from `hf`.

Take `⟨a', b', h2⟩` from `hg`. Conclude with `⟨a + a', b + b', by rw [map_add, h1, h2, map_add, map_add]; ring⟩`. Consider the case `mul_X f q hf`. Take `⟨a, b, h1⟩` from `hf`. Rewrite using `[map_mul, h1]`.

Take `⟨o, l⟩` from `q`. Consider the cases of `o with`. Consider the case `none`. Establish `aux : ∀ l : Fin 2, (X (⟨none, l⟩ : Σ o, Tb ι o) : MRing (Tb ι)) = xN ∨ (X (⟨none, l⟩ : Σ o, Tb ι o) : MRing (Tb ι)) = yN`. Introduce `l`.

Use `fin_cases l`. Conclude with `Or.inl rfl`. Conclude with `Or.inr rfl`. Break down `aux l with hl | hl` into its components or cases. Rewrite using `[hl]`.

Use `⟨b * (-(p : Polynomial (MRing ι ⧸ W)) * Polynomial.X ^ 2), a, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul σ b, ← hxx]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hl]`. Use `⟨a * Polynomial.X, b * Polynomial.X, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, map_mul, hσX]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `some k`. Use `⟨a * Polynomial.C (Ideal.Quotient.mk W (X ⟨k, l⟩)), b * Polynomial.C (Ideal.Quotient.mk W (X ⟨k, l⟩)), ?_⟩` and prove the remaining obligations. Establish `hτ : τ (Ideal.Quotient.mk W (X ⟨k, l⟩)) = mk' (X ⟨some k, l⟩)`.

Rewrite using `[show τ (Ideal.Quotient.mk W (X ⟨k, l⟩)) = mk' (inc (X ⟨k, l⟩)) from Ideal.Quotient.lift_mk _ _ _]`. Simplify using `[inc, oldIdx]`. Rewrite using `[map_mul, map_mul, hσC, hτ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hφ' : ∀ f, φ' (mk' f) = φ f` using `fun f => Ideal.Quotient.lift_mk _ _ _`.

Establish `hτ' : ∀ d, τ (Ideal.Quotient.mk W d) = mk' (inc d)` using `fun d => Ideal.Quotient.lift_mk _ _ _`. Establish `hσ : ∀ a, φ' (σ a) = a.map (i : (MRing ι ⧸ W) →+* E)`. Establish `: (φ'.comp σ) = Polynomial.mapRingHom i`. Apply `Polynomial.ringHom_ext` to reduce the goal to its premises. Introduce `d`.

Take `⟨d, rfl⟩` from `Ideal.Quotient.mk_surjective d`. Use `show φ' (σ (Polynomial.C _)) = (Polynomial.C _).map i`. Rewrite using `[hσC, hτ', hφ', hinc, Polynomial.map_C]`. Use `show φ' (σ Polynomial.X) = Polynomial.X.map i`. Rewrite using `[hσX, hφ', hy, Polynomial.map_X]`.

Conclude with `fun a => congrArg (fun g => g a) this`. Establish `hφx : φ' (mk' xN) = Polynomial.C s * Polynomial.X`. Rewrite using `[hφ', hx]`. Establish `hinj : Function.Injective φ'`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `q hq`. Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Take `⟨a, b, h1⟩` from `hform f`. Express the relevant statement in the definitionally equal form `φ' (mk' f) = 0 at hq`. Express the relevant statement in the definitionally equal form `mk' f = 0`.

Rewrite `hq`, the goal using `[h1]`. Rewrite `hq` using `[map_add, map_mul, hσ, hσ, hφx]`. Establish `hcoef : ∀ n, (a.coeff (n + 1) = 0 ∧ b.coeff n = 0)`. Introduce `n`. Use `congrArg (fun t => Polynomial.coeff t (n + 1)) hq` as an intermediate fact.

Simplify using `only [Polynomial.coeff_add, Polynomial.coeff_map, Polynomial.coeff_zero] at this`. Establish `e : (Polynomial.map i b * (Polynomial.C s * Polynomial.X)).coeff (n + 1) = i (b.coeff n) * s`. Rewrite using `[← mul_assoc, Polynomial.coeff_mul_X, mul_comm, Polynomial.coeff_C_mul, Polynomial.coeff_map, mul_comm]`. Rewrite `this` using `[e]`. Conclude with `hind _ _ this`.

Establish `ha0 : a.coeff 0 = 0`. Use `congrArg (fun t => Polynomial.coeff t 0) hq` as an intermediate fact. Simplify using `only [Polynomial.coeff_add, Polynomial.coeff_map, Polynomial.coeff_zero] at this`. Establish `e : (Polynomial.map i b * (Polynomial.C s * Polynomial.X)).coeff 0 = 0`. Rewrite using `[← mul_assoc, Polynomial.coeff_mul_X_zero]`.

Rewrite `this` using `[e, add_zero]`. Establish `h3` using `hind (a.coeff 0) 0 (by simpa using this)`. Conclude with `h3.1`. Establish `ha : a = 0`. Use extensionality with `n`.

Consider the cases of `n with`. Consider the case `zero => simpa using ha0`. Consider the case `succ n => simpa using (hcoef n).1`. Establish `hb : b = 0`. Use extensionality with `n`.

Simplify using `using (hcoef n).2`. Rewrite using `[ha, hb]`. Simplify using the standard rewrite rules. Use `haveI : IsDomain (MRing (Tb ι) ⧸ twist p W) := hinj.isDomain φ'`. Conclude with `(Ideal.Quotient.isDomain_iff_prime _).mp inferInstance`.
-/
theorem twist_isPrime (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (W : Ideal (MRing ι)) (hW : W.IsPrime) (hN : NoRoot p W) : (twist p W).IsPrime := by
  classical
  haveI : IsDomain (MRing ι ⧸ W) := Ideal.Quotient.isDomain W
  have hD : ∀ a b : MRing ι ⧸ W, a ^ 2 + (p : MRing ι ⧸ W) * b ^ 2 = 0 → b = 0 := by
    intro a b h
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [Ideal.Quotient.eq_zero_iff_mem]
    apply hN a
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa using h
  obtain ⟨E, _, i, s, hs, hind⟩ := exists_root_field p hD
  let φ : MRing (Tb ι) →+* Polynomial E :=
    (aeval (fun q : Σ o, Tb ι o => match q with
      | ⟨none, j⟩ => if j = (0 : Fin 2) then Polynomial.C s * Polynomial.X else Polynomial.X
      | ⟨some k, l⟩ => Polynomial.C (i (Ideal.Quotient.mk W (X ⟨k, l⟩)))) :
        MRing (Tb ι) →ₐ[ℤ] Polynomial E).toRingHom
  have hinc : ∀ f : MRing ι, φ (inc f) = Polynomial.C (i (Ideal.Quotient.mk W f)) := by
    intro f
    have : (φ.comp inc) = (Polynomial.C.comp (i.comp (Ideal.Quotient.mk W))) := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp [φ, inc]
      · intro l; simp [φ, inc, oldIdx]
    exact congrArg (fun g => g f) this
  have hx : φ xN = Polynomial.C s * Polynomial.X := by
    simp only [φ, xN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
    exact if_pos rfl
  have hy : φ yN = Polynomial.X := by
    simp only [φ, yN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
    exact if_neg (show ¬ ((1 : Fin 2) = 0) by decide)
  have hCp : φ (C (p : ℤ)) = (p : Polynomial E) := by
    simp [φ]
  have hle : twist p W ≤ RingHom.ker φ := by
    refine sup_le (Ideal.map_le_iff_le_comap.mpr fun f hf => ?_) ?_
    · rw [Ideal.mem_comap, RingHom.mem_ker, hinc, Ideal.Quotient.eq_zero_iff_mem.mpr hf]
      simp
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      show quad p ∈ RingHom.ker φ
      rw [RingHom.mem_ker]
      simp only [quad, map_add, map_mul, map_pow, hx, hy, hCp]
      have hs' : (Polynomial.C s) ^ 2 = -(p : Polynomial E) := by
        rw [← map_pow, hs]; simp
      linear_combination (Polynomial.X ^ 2 : Polynomial E) * hs'
  let φ' : (MRing (Tb ι) ⧸ twist p W) →+* Polynomial E :=
    Ideal.Quotient.lift _ φ (fun a ha => hle ha)
  let mk' := Ideal.Quotient.mk (twist p W)
  have hWle : ∀ a ∈ W, (mk'.comp inc) a = 0 := by
    intro a ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha))
  let τ : (MRing ι ⧸ W) →+* (MRing (Tb ι) ⧸ twist p W) :=
    Ideal.Quotient.lift W (mk'.comp inc) hWle
  let σ : Polynomial (MRing ι ⧸ W) →+* (MRing (Tb ι) ⧸ twist p W) :=
    Polynomial.eval₂RingHom τ (mk' yN)
  have hσC : ∀ d, σ (Polynomial.C d) = τ d := fun d => by simp [σ]
  have hσX : σ Polynomial.X = mk' yN := by simp [σ]
  have hxx : mk' xN * mk' xN = σ (-(p : Polynomial (MRing ι ⧸ W)) * Polynomial.X ^ 2) := by
    have hq : mk' (quad p) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    simp only [quad, map_add, map_mul, map_pow] at hq
    have hc : mk' (C (p : ℤ)) = (p : MRing (Tb ι) ⧸ twist p W) := by simp [mk']
    rw [hc] at hq
    simp only [map_mul, map_neg, map_natCast, map_pow, hσX]
    linear_combination hq
  have hform : ∀ f : MRing (Tb ι), ∃ a b : Polynomial (MRing ι ⧸ W),
      mk' f = σ a + σ b * mk' xN := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C n =>
      refine ⟨(n : Polynomial (MRing ι ⧸ W)), 0, ?_⟩
      simp [mk']
    | add f g hf hg =>
      obtain ⟨a, b, h1⟩ := hf
      obtain ⟨a', b', h2⟩ := hg
      exact ⟨a + a', b + b', by rw [map_add, h1, h2, map_add, map_add]; ring⟩
    | mul_X f q hf =>
      obtain ⟨a, b, h1⟩ := hf
      rw [map_mul, h1]
      obtain ⟨o, l⟩ := q
      cases o with
      | none =>
        have aux : ∀ l : Fin 2, (X (⟨none, l⟩ : Σ o, Tb ι o) : MRing (Tb ι)) = xN ∨
            (X (⟨none, l⟩ : Σ o, Tb ι o) : MRing (Tb ι)) = yN := by
          intro l
          fin_cases l
          · exact Or.inl rfl
          · exact Or.inr rfl
        rcases aux l with hl | hl
        · rw [hl]
          refine ⟨b * (-(p : Polynomial (MRing ι ⧸ W)) * Polynomial.X ^ 2), a, ?_⟩
          rw [map_mul σ b, ← hxx]
          ring
        · rw [hl]
          refine ⟨a * Polynomial.X, b * Polynomial.X, ?_⟩
          rw [map_mul, map_mul, hσX]
          ring
      | some k =>
        refine ⟨a * Polynomial.C (Ideal.Quotient.mk W (X ⟨k, l⟩)),
          b * Polynomial.C (Ideal.Quotient.mk W (X ⟨k, l⟩)), ?_⟩
        have hτ : τ (Ideal.Quotient.mk W (X ⟨k, l⟩)) = mk' (X ⟨some k, l⟩) := by
          rw [show τ (Ideal.Quotient.mk W (X ⟨k, l⟩)) = mk' (inc (X ⟨k, l⟩)) from Ideal.Quotient.lift_mk _ _ _]
          simp [inc, oldIdx]
        rw [map_mul, map_mul, hσC, hτ]
        ring
  have hφ' : ∀ f, φ' (mk' f) = φ f := fun f => Ideal.Quotient.lift_mk _ _ _
  have hτ' : ∀ d, τ (Ideal.Quotient.mk W d) = mk' (inc d) := fun d => Ideal.Quotient.lift_mk _ _ _
  have hσ : ∀ a, φ' (σ a) = a.map (i : (MRing ι ⧸ W) →+* E) := by
    have : (φ'.comp σ) = Polynomial.mapRingHom i := by
      apply Polynomial.ringHom_ext
      · intro d
        obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d
        show φ' (σ (Polynomial.C _)) = (Polynomial.C _).map i
        rw [hσC, hτ', hφ', hinc, Polynomial.map_C]
      · show φ' (σ Polynomial.X) = Polynomial.X.map i
        rw [hσX, hφ', hy, Polynomial.map_X]
    exact fun a => congrArg (fun g => g a) this
  have hφx : φ' (mk' xN) = Polynomial.C s * Polynomial.X := by
    rw [hφ', hx]
  have hinj : Function.Injective φ' := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨a, b, h1⟩ := hform f
    change φ' (mk' f) = 0 at hq
    change mk' f = 0
    rw [h1] at hq ⊢
    rw [map_add, map_mul, hσ, hσ, hφx] at hq
    have hcoef : ∀ n, (a.coeff (n + 1) = 0 ∧ b.coeff n = 0) := by
      intro n
      have := congrArg (fun t => Polynomial.coeff t (n + 1)) hq
      simp only [Polynomial.coeff_add, Polynomial.coeff_map, Polynomial.coeff_zero] at this
      have e : (Polynomial.map i b * (Polynomial.C s * Polynomial.X)).coeff (n + 1) =
          i (b.coeff n) * s := by
        rw [← mul_assoc, Polynomial.coeff_mul_X, mul_comm, Polynomial.coeff_C_mul,
          Polynomial.coeff_map, mul_comm]
      rw [e] at this
      exact hind _ _ this
    have ha0 : a.coeff 0 = 0 := by
      have := congrArg (fun t => Polynomial.coeff t 0) hq
      simp only [Polynomial.coeff_add, Polynomial.coeff_map, Polynomial.coeff_zero] at this
      have e : (Polynomial.map i b * (Polynomial.C s * Polynomial.X)).coeff 0 = 0 := by
        rw [← mul_assoc, Polynomial.coeff_mul_X_zero]
      rw [e, add_zero] at this
      have h3 := hind (a.coeff 0) 0 (by simpa using this)
      exact h3.1
    have ha : a = 0 := by
      ext n
      cases n with
      | zero => simpa using ha0
      | succ n => simpa using (hcoef n).1
    have hb : b = 0 := by
      ext n
      simpa using (hcoef n).2
    rw [ha, hb]; simp
  haveI : IsDomain (MRing (Tb ι) ⧸ twist p W) := hinj.isDomain φ'
  exact (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance

end GlobalTheory.CompanionTheory.Ar.Tw
