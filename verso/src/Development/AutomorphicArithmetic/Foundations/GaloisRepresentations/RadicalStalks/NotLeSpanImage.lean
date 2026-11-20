import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord

/- English proof (translation)
Introduce `hle`. Choose the witnesses or unpack the hypotheses as in `⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual k P, ℓ v ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hv0 ((Module.forall_dual_apply_eq_zero_iff k v).1 h)`.

Set `K : Submodule k P` to `G ⊓ LinearMap.ker ℓ`. Establish `hKG : K < G`. Use `lt_of_le_of_ne inf_le_left fun h => hℓ ?_` and prove the remaining obligations. Establish `: v ∈ K` using `h ▸ hv`. Conclude with `this.2`.

Set `b` to `Module.finBasis k K`. Set `t : Fin (Module.finrank k K) → P` to `fun i => A (b i : P)`. Establish `hAK : ∀ y ∈ K, A y ∈ Submodule.span k (Set.range t)`. Introduce `y hy`. Establish `e : y = ∑ i, b.repr ⟨y, hy⟩ i • (b i : P)`.

Establish `h : ((∑ i, b.repr ⟨y, hy⟩ i • b i : K) : P) = y` using `by rw [b.sum_repr]`. Rewrite `h` using `[Submodule.coe_sum]`. Simplify `h.symm` using `only [Submodule.coe_smul]`. Rewrite using `[e, map_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hA]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Establish `hspan : Submodule.span k (A '' G) ≤ Submodule.span k (Set.range t)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, hg, rfl⟩`.

Set `l : k` to `ℓ g / ℓ v`. Establish `hy : g - l • v ∈ K`. Use `⟨G.sub_mem hg (G.smul_mem _ hv), ?_⟩` and prove the remaining obligations. Simplify using `[l, hℓ]`. Establish `e : A g = A (g - l • v)`.

Rewrite using `[map_sub, hA, hAv, smul_zero, sub_zero]`. Rewrite using `[SetLike.mem_coe, e]`. Conclude with `hAK _ hy`. Establish `h1 : Module.finrank k G ≤ Module.finrank k (Submodule.span k (Set.range t))` using `Submodule.finrank_mono (hle.trans hspan)`. Establish `h2 : Module.finrank k (Submodule.span k (Set.range t)) ≤ Module.finrank k K`.

Use `finrank_range_le_card (R := k) t` as an intermediate fact. Simplify `this` using `[Set.finrank]`. Establish `h3` using `Submodule.finrank_lt_finrank_of_lt hKG`. Use linear arithmetic over natural numbers and integers.
-/
private lemma not_le_span_image {k P : Type*} [Field k] [AddCommGroup P] [Module k P] [FiniteDimensional k P]
    (G : Submodule k P) (A : P →+ P) (q : ℕ) (hq : 0 < q) (hA : ∀ (l : k) x, A (l • x) = l ^ q • A x)
    (v : P) (hv : v ∈ G) (hv0 : v ≠ 0) (hAv : A v = 0) :
    ¬ G ≤ Submodule.span k (A '' G) := by
  intro hle
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual k P, ℓ v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv0 ((Module.forall_dual_apply_eq_zero_iff k v).1 h)
  let K : Submodule k P := G ⊓ LinearMap.ker ℓ
  have hKG : K < G := by
    refine lt_of_le_of_ne inf_le_left fun h => hℓ ?_
    have : v ∈ K := h ▸ hv
    exact this.2
  let b := Module.finBasis k K
  let t : Fin (Module.finrank k K) → P := fun i => A (b i : P)
  have hAK : ∀ y ∈ K, A y ∈ Submodule.span k (Set.range t) := by
    intro y hy
    have e : y = ∑ i, b.repr ⟨y, hy⟩ i • (b i : P) := by
      have h : ((∑ i, b.repr ⟨y, hy⟩ i • b i : K) : P) = y := by rw [b.sum_repr]
      rw [Submodule.coe_sum] at h
      simpa only [Submodule.coe_smul] using h.symm
    rw [e, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hA]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspan : Submodule.span k (A '' G) ≤ Submodule.span k (Set.range t) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    let l : k := ℓ g / ℓ v
    have hy : g - l • v ∈ K := by
      refine ⟨G.sub_mem hg (G.smul_mem _ hv), ?_⟩
      simp [l, hℓ]
    have e : A g = A (g - l • v) := by
      rw [map_sub, hA, hAv, smul_zero, sub_zero]
    rw [SetLike.mem_coe, e]
    exact hAK _ hy
  have h1 : Module.finrank k G ≤ Module.finrank k (Submodule.span k (Set.range t)) :=
    Submodule.finrank_mono (hle.trans hspan)
  have h2 : Module.finrank k (Submodule.span k (Set.range t)) ≤ Module.finrank k K := by
    have := finrank_range_le_card (R := k) t
    simpa [Set.finrank] using this
  have h3 := Submodule.finrank_lt_finrank_of_lt hKG
  omega

/- English proof (translation)
Establish `h : ((Polynomial.X - Polynomial.C l) ^ (p ^ n) : Polynomial k) = Polynomial.X ^ (p ^ n) - Polynomial.C (l ^ (p ^ n))`. Rewrite using `[sub_pow_char_pow, Polynomial.C_pow]`. Use `congrArg (Polynomial.aeval T) h` as an intermediate fact. Simplify `this` using `[Algebra.algebraMap_eq_smul_one, smul_pow]`.
-/
private lemma sub_smul_pow (p : ℕ) [Fact p.Prime] {k P : Type*} [Field k] [CharP k p] [AddCommGroup P] [Module k P]
    (T : Module.End k P) (l : k) (n : ℕ) : (T - l • 1) ^ (p ^ n) = T ^ (p ^ n) - (l ^ (p ^ n)) • 1 := by
  have h : ((Polynomial.X - Polynomial.C l) ^ (p ^ n) : Polynomial k) =
      Polynomial.X ^ (p ^ n) - Polynomial.C (l ^ (p ^ n)) := by
    rw [sub_pow_char_pow, Polynomial.C_pow]
  have := congrArg (Polynomial.aeval T) h
  simpa [Algebra.algebraMap_eq_smul_one, smul_pow] using this

/- English proof (translation)
Use `letI := Fintype.ofFinite R`. Use `letI : Field R := Fintype.fieldOfDomain R`. Rewrite using `[Nat.card_eq_fintype_card]`. Conclude with `FiniteField.pow_card x`.
-/
private lemma pow_card_subring {k : Type*} [Field k] (R : Subring k) [Finite R] (x : R) : x ^ Nat.card R = x := by
  classical
  letI := Fintype.ofFinite R
  letI : Field R := Fintype.fieldOfDomain R
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

/- English proof (translation)
Take `⟨n, hn⟩` from `Module.End.mem_maxGenEigenspace _ _ _ |>.1 hy`. Use `set N : Module.End k P := T - l • 1 with hN`. Establish `hq : 2 ≤ p ^ f`. Combine the equalities or inequalities in the displayed calculation. Establish `hNq : (N ^ (p ^ f)) y = N y`.

Rewrite using `[hN, sub_smul_pow p, hl]`. Simplify using `[hT]`. Establish `hit : ∀ j : ℕ, (N ^ (j * (p ^ f - 1) + 1)) y = N y`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero => simp`. Consider the case `succ j ih`. Establish `e : (j + 1) * (p ^ f - 1) + 1 = j * (p ^ f - 1) + p ^ f`. Establish `: p ^ f - 1 + 1 = p ^ f` using `by omega`. Rewrite using `[Nat.add_mul, Nat.one_mul, Nat.add_assoc, this]`.

Rewrite using `[e, pow_add, Module.End.mul_apply, hNq, ← Module.End.mul_apply, ← pow_succ, ih]`. Establish `hz : N y = 0`. Rewrite using `[← hit n]`. Establish `e : n * (p ^ f - 1) + 1 = (n * (p ^ f - 1) + 1 - n) + n`. Establish `: n ≤ n * (p ^ f - 1)` using `Nat.le_mul_of_pos_right n (by omega)`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[e, pow_add, Module.End.mul_apply, hn, map_zero]`. Establish `: T y - l • y = 0` using `by simpa [hN] using hz`. Conclude with `sub_eq_zero.1 this`.
-/
private lemma eig_of_gen (p : ℕ) [Fact p.Prime] {k P : Type*} [Field k] [CharP k p] [AddCommGroup P] [Module k P]
    (T : Module.End k P) (l : k) (f : ℕ) (hf : 0 < f) (hl : l ^ (p ^ f) = l) (y : P)
    (hy : y ∈ T.maxGenEigenspace l) (hT : (T ^ (p ^ f)) y = T y) : T y = l • y := by
  obtain ⟨n, hn⟩ := Module.End.mem_maxGenEigenspace _ _ _ |>.1 hy
  set N : Module.End k P := T - l • 1 with hN
  have hq : 2 ≤ p ^ f := by
    calc 2 ≤ p := (Fact.out : p.Prime).two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hf
  have hNq : (N ^ (p ^ f)) y = N y := by
    rw [hN, sub_smul_pow p, hl]
    simp [hT]
  have hit : ∀ j : ℕ, (N ^ (j * (p ^ f - 1) + 1)) y = N y := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : (j + 1) * (p ^ f - 1) + 1 = j * (p ^ f - 1) + p ^ f := by
        have : p ^ f - 1 + 1 = p ^ f := by omega
        rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc, this]
      rw [e, pow_add, Module.End.mul_apply, hNq, ← Module.End.mul_apply, ← pow_succ, ih]
  have hz : N y = 0 := by
    rw [← hit n]
    have e : n * (p ^ f - 1) + 1 = (n * (p ^ f - 1) + 1 - n) + n := by
      have : n ≤ n * (p ^ f - 1) := Nat.le_mul_of_pos_right n (by omega)
      omega
    rw [e, pow_add, Module.End.mul_apply, hn, map_zero]
  have : T y - l • y = 0 := by simpa [hN] using hz
  exact sub_eq_zero.1 this

/- English proof (translation)
Set `U : (C → k) → Submodule k P` to `fun ψ => ⨅ d, (ρ d).maxGenEigenspace (ψ d)`. Set `G : Submodule k P` to `U χ`. Set `H : Submodule k P` to `⨆ ψ : {ψ : C → k // ψ ≠ χ}, U ψ`. Establish `hc : ∀ x y, Commute (ρ x) (ρ y)` using `fun x y => by show ρ x * ρ y = ρ y * ρ x`. Rewrite using `[← map_mul, ← map_mul, mul_comm]`.

Establish `hmaps : ∀ i j m0, Set.MapsTo (ρ i) ((ρ j).maxGenEigenspace m0) ((ρ j).maxGenEigenspace m0)` using `fun i j m0 => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) m0`. Establish `hind : iSupIndep U` using `Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun x => ρ x) hmaps`. Establish `htop : ⨆ ψ, U ψ = ⊤` using `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo (fun x => ρ x) hmaps (fun i => Module.End.iSup_maxGenEigenspace_eq_top (ρ i))`. Establish `hUH : ∀ ψ : C → k, ψ ≠ χ → U ψ ≤ H` using `fun ψ h => le_iSup (fun ψ : {ψ : C → k // ψ ≠ χ} => U ψ) ⟨ψ, h⟩`. Establish `hsup : G ⊔ H = ⊤`.

Rewrite using `[eq_top_iff, ← htop]`. Use `iSup_le fun ψ => ?_` and prove the remaining obligations. Distinguish the cases in `h : ψ = χ`. Substitute `h` using the available equality. Conclude with `le_sup_left`.

Conclude with `le_sup_of_le_right (hUH ψ h)`. Establish `hdisj : Disjoint G H` using `(hind χ).mono_right (iSup_le fun ψ => le_iSup₂_of_le (f := fun j (_ : j ≠ ⇑χ) => U j) ψ.1 ψ.2 le_rfl)`. Establish `hρU : ∀ c ψ, ∀ x ∈ U ψ, ρ c x ∈ U ψ`. Introduce `c ψ x hx`. Simplify using `only [U, Submodule.mem_iInf] at hx ⊢`.

Conclude with `fun d => hmaps c d _ (hx d)`. Establish `hρH : ∀ c, ∀ x ∈ H, ρ c x ∈ H`. Introduce `c x hx`. Establish `hle : H ≤ H.comap (ρ c)` using `iSup_le fun ψ y hy => hUH ψ.1 ψ.2 (hρU c ψ.1 y hy)`. Conclude with `hle hx`.

Establish `hAU : ∀ ψ : C → k, ∀ x ∈ U ψ, A x ∈ U (fun c => ψ c ^ q)`. Introduce `ψ x hx`. Simplify using `only [U, Submodule.mem_iInf, Module.End.mem_maxGenEigenspace] at hx ⊢`. Introduce `d`. Take `⟨n, hn⟩` from `hx d`.

Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `step : ∀ (n : ℕ) y, ((ρ d - (ψ d ^ q) • 1) ^ n) (A y) = A (((ρ d - ψ d • 1) ^ n) y)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro y`.

Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `y`. Establish `e : (ρ d - (ψ d ^ q) • 1) (A y) = A ((ρ d - ψ d • 1) y)`. Simplify using `[hcomm, hsemi, map_sub]`.

Rewrite using `[pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, e, ih]`. Rewrite using `[step, hn, map_zero]`. Establish `hAG : ∀ x ∈ G, A x ∈ G`. Introduce `x hx`. Use `hAU χ x hx` as an intermediate fact.

Establish `e : (fun c => χ c ^ q) = ⇑χ` using `funext hfix`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Establish `hAH : ∀ x ∈ H, A x ∈ H`. Introduce `x hx`. Use `Submodule.iSup_induction (fun ψ : {ψ : C → k // ψ ≠ χ} => U ψ) (motive := fun x => A x ∈ H) hx ?_ ?_ ?_` and prove the remaining obligations.

Introduce `ψ y hy`. Use `hUH _ ?_ (hAU ψ.1 y hy)` and prove the remaining obligations. Introduce `h`. Use `ψ.2 (funext fun c => hinj ?_)` and prove the remaining obligations. Use `show ψ.1 c ^ q = χ c ^ q`.

Rewrite using `[hfix, ← congrFun h c]`. Simplify using the standard rewrite rules. Introduce `y z hy hz`. Rewrite using `[map_add]`. Conclude with `H.add_mem hy hz`.

Establish `hεG : ∀ x ∈ G, ρ ε x = x`. Establish `aux : ∀ (n : ℕ) (x : P), ((ρ ε - (1 : k) • 1) ^ n) x = 0 → ρ ε x = x`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro x hx`.

Simplify using `at hx`. Simplify using `[hx]`. Consider the case `succ n ih`. Introduce `x hx`. Rewrite `hx` using `[pow_succ, Module.End.mul_apply]`.

Establish `h1` using `ih _ hx`. Establish `h2 : ρ ε (ρ ε x) = ρ ε x` using `by rw [← Module.End.mul_apply, hε]`. Simplify using `only [one_smul, LinearMap.sub_apply, Module.End.one_apply, map_sub, h2, sub_self] at h1`. Conclude with `sub_eq_zero.1 h1.symm`. Introduce `x hx`.

Establish `h` using `(Submodule.mem_iInf _).1 hx ε`. Rewrite `h` using `[hε1]`. Take `⟨n, hn⟩` from `(Module.End.mem_maxGenEigenspace _ _ _).1 h`. Conclude with `aux n x hn`. Establish `h1εG : ∀ x ∈ G, ρ (1 - ε) x = 0`.

Introduce `x hx`. Simplify using `[map_sub, hεG x hx]`. Set `Wd : Submodule k P` to `Submodule.span k (A '' G)`. Establish `hWG : Wd ≤ G` using `Submodule.span_le.2 (by rintro _ ⟨x, hx, rfl⟩; exact hAG x hx)`. Establish `haW : ∀ x ∈ Wd, ρ a x ∈ Wd`.

Introduce `x hx`. Establish `hle : Wd ≤ Wd.comap (ρ a)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Use `show ρ a (A y) ∈ Wd`.

Rewrite using `[← hcomm]`. Conclude with `Submodule.subset_span ⟨_, hρU a χ y hy, rfl⟩`. Conclude with `hle hx`. Establish `hvG : v ∈ G`. Use `(Submodule.mem_iInf _).2 fun c => (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, ?_⟩` and prove the remaining obligations.

Simplify using `[hv]`. Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Establish `hS : Submodule.span k (Set.range A) ≤ Wd ⊔ H`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨z, rfl⟩`. Establish `hz : z ∈ G ⊔ H` using `hsup ▸ Submodule.mem_top`. Take `⟨z1, h1, z2, h2, rfl⟩` from `Submodule.mem_sup.1 hz`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem_sup (Submodule.subset_span ⟨z1, h1, rfl⟩) (hAH z2 h2)`.

Establish `hstep : ∀ u ∈ G, ∃ w ∈ Wd, ∃ u' ∈ G, u = w + ρ a u'`. Introduce `u hu`. Take `⟨s, hs, hsu⟩` from `(Submodule.mem_map).1 (hno u hu)`. Take `⟨u', v', hx⟩` from `annG (u - s) (by rw [map_sub, hsu, sub_self])`. Take `⟨w, hw, h, hh, rfl⟩` from `Submodule.mem_sup.1 (hS hs)`.

Establish `d : ∀ z : P, z ∈ G ⊔ H` using `fun z => hsup ▸ Submodule.mem_top`. Take `⟨u1, hu1, u2, hu2, rfl⟩` from `Submodule.mem_sup.1 (d u')`. Take `⟨v1, hv1, v2, hv2, rfl⟩` from `Submodule.mem_sup.1 (d v')`. Establish `e0 : ρ (1 - ε) v1 = 0` using `h1εG v1 hv1`. Establish `e1 : u - w - ρ a u1 = h + ρ a u2 + ρ (1 - ε) v2`.

Simplify using `only [map_add, e0] at hx`. Establish `h'` using `sub_eq_iff_eq_add.1 hx`. Rewrite using `[h']`. Normalize the expressions using the abelian group laws. Establish `hd0 : u - w - ρ a u1 = 0`.

Use `Submodule.disjoint_def.1 hdisj _ (G.sub_mem (G.sub_mem hu (hWG hw)) (hρU a _ u1 hu1)) ?_` and prove the remaining obligations. Rewrite using `[e1]`. Conclude with `H.add_mem (H.add_mem hh (hρH a _ hu2)) (hρH _ _ hv2)`. Use `⟨w, hw, u1, hu1, ?_⟩` and prove the remaining obligations. Establish `h'` using `sub_eq_zero.1 hd0`.

Conclude with `sub_eq_iff_eq_add'.1 h'`. Establish `hpow : ∀ (n : ℕ), ∀ x ∈ Wd, (ρ a ^ n) x ∈ Wd`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro x hx`.

Simplify using `using hx`. Consider the case `succ n ih`. Introduce `x hx`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Conclude with `haW _ (ih x hx)`.

Establish `hiter : ∀ (n : ℕ), ∀ u ∈ G, ∃ w ∈ Wd, ∃ u' ∈ G, u = w + (ρ a ^ n) u'`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro u hu; exact ⟨0, Wd.zero_mem, u, hu, by simp⟩`. Consider the case `succ n ih`.

Introduce `u hu`. Take `⟨w, hw, u', hu', e⟩` from `ih u hu`. Take `⟨w2, hw2, u'', hu'', e2⟩` from `hstep u' hu'`. Use `⟨w + (ρ a ^ n) w2, Wd.add_mem hw (hpow n _ hw2), u'', hu'', ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ, Module.End.mul_apply, e, e2, map_add, add_assoc]`.

Take `⟨e, he⟩` from `hnil`. Establish `hGW : G ≤ Wd`. Introduce `u hu`. Take `⟨w, hw, u', hu', eq⟩` from `hiter e u hu`. Establish `h0 : (ρ a ^ e) u' = 0`.

Establish `h1 : (ρ a ^ e * ρ ε) u' = 0` using `by rw [he]; rfl`. Rewrite `h1` using `[Module.End.mul_apply, hεG u' hu']`. Then use the resulting hypothesis. Rewrite using `[eq, h0, add_zero]`. Conclude with `hw`. Conclude with `not_le_span_image G A q hq hsemi v hvG hv0 hAv hGW`.
-/
private lemma exists_not_mem {k C P : Type*} [Field k] [IsAlgClosed k] [CommRing C] [AddCommGroup P] [Module k P]
    [FiniteDimensional k P] (ρ : C →+* Module.End k P) (χ : C →+* k) (q : ℕ) (hq : 0 < q) (A : P →+ P)
    (hsemi : ∀ (l : k) x, A (l • x) = l ^ q • A x) (hcomm : ∀ c x, A (ρ c x) = ρ c (A x))
    (hfix : ∀ c, χ c ^ q = χ c) (hinj : Function.Injective fun x : k => x ^ q) (ε a g : C)
    (hε : ρ ε * ρ ε = ρ ε) (hε1 : χ ε = 1) (hnil : ∃ e : ℕ, ρ a ^ e * ρ ε = 0)
    (annG : ∀ x, ρ g x = 0 → ∃ u v, x = ρ a u + ρ (1 - ε) v)
    (v : P) (hv0 : v ≠ 0) (hv : ∀ c, ρ c v = χ c • v) (hAv : A v = 0) :
    ∃ u ∈ ⨅ c, (ρ c).maxGenEigenspace (χ c), ρ g u ∉ (Submodule.span k (Set.range A)).map (ρ g) := by
  classical
  let U : (C → k) → Submodule k P := fun ψ => ⨅ d, (ρ d).maxGenEigenspace (ψ d)
  let G : Submodule k P := U χ
  let H : Submodule k P := ⨆ ψ : {ψ : C → k // ψ ≠ χ}, U ψ
  have hc : ∀ x y, Commute (ρ x) (ρ y) := fun x y => by
    show ρ x * ρ y = ρ y * ρ x
    rw [← map_mul, ← map_mul, mul_comm]
  have hmaps : ∀ i j m0, Set.MapsTo (ρ i) ((ρ j).maxGenEigenspace m0) ((ρ j).maxGenEigenspace m0) :=
    fun i j m0 => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) m0
  have hind : iSupIndep U :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun x => ρ x) hmaps
  have htop : ⨆ ψ, U ψ = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo (fun x => ρ x) hmaps
      (fun i => Module.End.iSup_maxGenEigenspace_eq_top (ρ i))
  have hUH : ∀ ψ : C → k, ψ ≠ χ → U ψ ≤ H := fun ψ h =>
    le_iSup (fun ψ : {ψ : C → k // ψ ≠ χ} => U ψ) ⟨ψ, h⟩
  have hsup : G ⊔ H = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun ψ => ?_
    by_cases h : ψ = χ
    · subst h; exact le_sup_left
    · exact le_sup_of_le_right (hUH ψ h)
  have hdisj : Disjoint G H :=
    (hind χ).mono_right (iSup_le fun ψ => le_iSup₂_of_le (f := fun j (_ : j ≠ ⇑χ) => U j) ψ.1 ψ.2 le_rfl)
  have hρU : ∀ c ψ, ∀ x ∈ U ψ, ρ c x ∈ U ψ := by
    intro c ψ x hx
    simp only [U, Submodule.mem_iInf] at hx ⊢
    exact fun d => hmaps c d _ (hx d)
  have hρH : ∀ c, ∀ x ∈ H, ρ c x ∈ H := by
    intro c x hx
    have hle : H ≤ H.comap (ρ c) := iSup_le fun ψ y hy => hUH ψ.1 ψ.2 (hρU c ψ.1 y hy)
    exact hle hx
  have hAU : ∀ ψ : C → k, ∀ x ∈ U ψ, A x ∈ U (fun c => ψ c ^ q) := by
    intro ψ x hx
    simp only [U, Submodule.mem_iInf, Module.End.mem_maxGenEigenspace] at hx ⊢
    intro d
    obtain ⟨n, hn⟩ := hx d
    refine ⟨n, ?_⟩
    have step : ∀ (n : ℕ) y, ((ρ d - (ψ d ^ q) • 1) ^ n) (A y) = A (((ρ d - ψ d • 1) ^ n) y) := by
      intro n
      induction n with
      | zero => intro y; simp
      | succ n ih =>
        intro y
        have e : (ρ d - (ψ d ^ q) • 1) (A y) = A ((ρ d - ψ d • 1) y) := by
          simp [hcomm, hsemi, map_sub]
        rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, e, ih]
    rw [step, hn, map_zero]
  have hAG : ∀ x ∈ G, A x ∈ G := by
    intro x hx
    have := hAU χ x hx
    have e : (fun c => χ c ^ q) = ⇑χ := funext hfix
    rwa [e] at this
  have hAH : ∀ x ∈ H, A x ∈ H := by
    intro x hx
    refine Submodule.iSup_induction (fun ψ : {ψ : C → k // ψ ≠ χ} => U ψ) (motive := fun x => A x ∈ H) hx ?_ ?_ ?_
    · intro ψ y hy
      refine hUH _ ?_ (hAU ψ.1 y hy)
      intro h
      refine ψ.2 (funext fun c => hinj ?_)
      show ψ.1 c ^ q = χ c ^ q
      rw [hfix, ← congrFun h c]
    · simp
    · intro y z hy hz
      rw [map_add]
      exact H.add_mem hy hz
  have hεG : ∀ x ∈ G, ρ ε x = x := by
    have aux : ∀ (n : ℕ) (x : P), ((ρ ε - (1 : k) • 1) ^ n) x = 0 → ρ ε x = x := by
      intro n
      induction n with
      | zero => intro x hx; simp at hx; simp [hx]
      | succ n ih =>
        intro x hx
        rw [pow_succ, Module.End.mul_apply] at hx
        have h1 := ih _ hx
        have h2 : ρ ε (ρ ε x) = ρ ε x := by rw [← Module.End.mul_apply, hε]
        simp only [one_smul, LinearMap.sub_apply, Module.End.one_apply, map_sub, h2, sub_self] at h1
        exact sub_eq_zero.1 h1.symm
    intro x hx
    have h := (Submodule.mem_iInf _).1 hx ε
    rw [hε1] at h
    obtain ⟨n, hn⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 h
    exact aux n x hn
  have h1εG : ∀ x ∈ G, ρ (1 - ε) x = 0 := by
    intro x hx
    simp [map_sub, hεG x hx]
  let Wd : Submodule k P := Submodule.span k (A '' G)
  have hWG : Wd ≤ G := Submodule.span_le.2 (by rintro _ ⟨x, hx, rfl⟩; exact hAG x hx)
  have haW : ∀ x ∈ Wd, ρ a x ∈ Wd := by
    intro x hx
    have hle : Wd ≤ Wd.comap (ρ a) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨y, hy, rfl⟩
      show ρ a (A y) ∈ Wd
      rw [← hcomm]
      exact Submodule.subset_span ⟨_, hρU a χ y hy, rfl⟩
    exact hle hx
  have hvG : v ∈ G := by
    refine (Submodule.mem_iInf _).2 fun c => (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, ?_⟩
    simp [hv]
  by_contra hno
  push_neg at hno
  have hS : Submodule.span k (Set.range A) ≤ Wd ⊔ H := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨z, rfl⟩
    have hz : z ∈ G ⊔ H := hsup ▸ Submodule.mem_top
    obtain ⟨z1, h1, z2, h2, rfl⟩ := Submodule.mem_sup.1 hz
    rw [map_add]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨z1, h1, rfl⟩) (hAH z2 h2)
  have hstep : ∀ u ∈ G, ∃ w ∈ Wd, ∃ u' ∈ G, u = w + ρ a u' := by
    intro u hu
    obtain ⟨s, hs, hsu⟩ := (Submodule.mem_map).1 (hno u hu)
    obtain ⟨u', v', hx⟩ := annG (u - s) (by rw [map_sub, hsu, sub_self])
    obtain ⟨w, hw, h, hh, rfl⟩ := Submodule.mem_sup.1 (hS hs)
    have d : ∀ z : P, z ∈ G ⊔ H := fun z => hsup ▸ Submodule.mem_top
    obtain ⟨u1, hu1, u2, hu2, rfl⟩ := Submodule.mem_sup.1 (d u')
    obtain ⟨v1, hv1, v2, hv2, rfl⟩ := Submodule.mem_sup.1 (d v')
    have e0 : ρ (1 - ε) v1 = 0 := h1εG v1 hv1
    have e1 : u - w - ρ a u1 = h + ρ a u2 + ρ (1 - ε) v2 := by
      simp only [map_add, e0] at hx
      have h' := sub_eq_iff_eq_add.1 hx
      rw [h']
      abel
    have hd0 : u - w - ρ a u1 = 0 := by
      refine Submodule.disjoint_def.1 hdisj _ (G.sub_mem (G.sub_mem hu (hWG hw)) (hρU a _ u1 hu1)) ?_
      rw [e1]
      exact H.add_mem (H.add_mem hh (hρH a _ hu2)) (hρH _ _ hv2)
    refine ⟨w, hw, u1, hu1, ?_⟩
    have h' := sub_eq_zero.1 hd0
    exact sub_eq_iff_eq_add'.1 h'
  have hpow : ∀ (n : ℕ), ∀ x ∈ Wd, (ρ a ^ n) x ∈ Wd := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      rw [pow_succ', Module.End.mul_apply]
      exact haW _ (ih x hx)
  have hiter : ∀ (n : ℕ), ∀ u ∈ G, ∃ w ∈ Wd, ∃ u' ∈ G, u = w + (ρ a ^ n) u' := by
    intro n
    induction n with
    | zero => intro u hu; exact ⟨0, Wd.zero_mem, u, hu, by simp⟩
    | succ n ih =>
      intro u hu
      obtain ⟨w, hw, u', hu', e⟩ := ih u hu
      obtain ⟨w2, hw2, u'', hu'', e2⟩ := hstep u' hu'
      refine ⟨w + (ρ a ^ n) w2, Wd.add_mem hw (hpow n _ hw2), u'', hu'', ?_⟩
      rw [pow_succ, Module.End.mul_apply, e, e2, map_add, add_assoc]
  obtain ⟨e, he⟩ := hnil
  have hGW : G ≤ Wd := by
    intro u hu
    obtain ⟨w, hw, u', hu', eq⟩ := hiter e u hu
    have h0 : (ρ a ^ e) u' = 0 := by
      have h1 : (ρ a ^ e * ρ ε) u' = 0 := by rw [he]; rfl
      rwa [Module.End.mul_apply, hεG u' hu'] at h1
    rw [eq, h0, add_zero]
    exact hw
  exact not_le_span_image G A q hq hsemi v hvG hv0 hAv hGW

end UpperTheory.Gal.Ord

/- English proof (translation)
Introduce `p _ k _ _ _ C _ w f hf hcard π χ P _ _ ρ F Φ L`. Use `haveI := L.fin`. Set `ρh : C →+* Module.End k P` to `{ toFun := ρ, map_one' := L.one, map_mul' := L.mul, map_add' := L.add map_zero' := by`. Establish `h` using `L.add 0 0`. Simplify using `using h }`.

Establish `hp : ρh (p : C) = 0`. Rewrite using `[map_natCast, ← map_natCast (algebraMap k (Module.End k P)), CharP.cast_eq_zero k p, map_zero]`. Establish `hdvd : ∀ x : C, (p : C) ∣ x → ρh x = 0`. Introduce and unpack `_ ⟨d, rfl⟩`. Rewrite using `[map_mul, hp, zero_mul]`.

Establish `hfix : ∀ c, χ c ^ (p ^ f) = χ c`. Establish `e : (C ⧸ w) ≃ χ.range` using `((Ideal.quotEquivOfEq L.ker.symm).trans (RingHom.quotientKerEquivRange χ)).toEquiv`. Establish `hcard' : Nat.card χ.range = p ^ f` using `(Nat.card_congr e).symm.trans hcard`. Use `haveI : Finite χ.range := Nat.finite_of_card_ne_zero (by`. Rewrite using `[hcard']`.

Conclude with `pow_ne_zero _ (Fact.out : p.Prime).ne_zero)`. Introduce `c`. Establish `h` using `pow_card_subring χ.range ⟨χ c, c, rfl⟩`. Rewrite `h` using `[hcard']`. Conclude with `congrArg Subtype.val h`.

Establish `hinj : Function.Injective fun x : k => x ^ (p ^ f)`. Introduce `x y h`. Conclude with `(iterateFrobenius k p f).injective (by simpa [iterateFrobenius_def] using h)`. Set `A : P →+ P` to `{ toFun := (⇑Φ)^[f], map_zero' := iterate_map_zero Φ f, map_add' := iterate_map_add Φ f }`. Establish `hsemiN : ∀ (n : ℕ) (l : k) x, (⇑Φ)^[n] (l • x) = l ^ (p ^ n) • (⇑Φ)^[n] x`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro l x`. Simplify using the standard rewrite rules. Consider the case `succ n ih`.

Introduce `l x`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply', ih, L.semi, ← pow_mul, pow_succ]`. Establish `hcommN : ∀ (n : ℕ) c x, (⇑Φ)^[n] (ρ c x) = ρ c ((⇑Φ)^[n] x)`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => intro c x`. Both sides reduce to the same expression. Consider the case `succ n ih`. Introduce `c x`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply', ih, L.comm]`.

Take `⟨x0, hx0F, hx0, -⟩` from `L.line`. Establish `hAv : A (ρ π.ε x0) = 0` using `by show (⇑Φ)^[f] (ρ π.ε x0) = 0`. Establish `e : (⇑Φ)^[f] (ρ π.ε x0) = (⇑Φ)^[f - 1] (Φ (ρ π.ε x0))`. Rewrite using `[← Function.iterate_succ_apply]`. Use `congr 2`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[e, L.comm, (L.kerΦ x0).2 hx0F, map_zero, iterate_map_zero]`. Establish `hε : ρh π.ε * ρh π.ε = ρh π.ε`. Establish `h` using `hdvd _ π.idem`. Rewrite `h` using `[map_sub, map_mul, sub_eq_zero]`. Then use the resulting hypothesis.

Establish `hε1 : χ π.ε = 1`. Establish `h : π.ε - 1 ∈ RingHom.ker χ` using `L.ker ▸ π.one`. Rewrite `h` using `[RingHom.mem_ker, map_sub, map_one, sub_eq_zero]`. Then use the resulting hypothesis. Establish `hnil : ∃ e : ℕ, ρh π.a ^ e * ρh π.ε = 0`. Take `⟨e, he⟩` from `π.nil`.

Use `⟨e, ?_⟩` and prove the remaining obligations. Establish `h` using `hdvd _ he`. Rewrite `h` using `[map_mul, map_pow]`. Then use the resulting hypothesis. Take `⟨u, hu, hnot⟩` from `exists_not_mem ρh χ (p ^ f) (pow_pos (Fact.out : p.Prime).pos f) A (fun l x => hsemiN f l x) (fun c x => hcommN f c x) hfix hinj π.ε π.a π.g hε hε1 hnil (fun x h => by`. Take `⟨u, v, e⟩` from `L.annG x h`.

Conclude with `⟨u, v, e⟩)`. Use the proof step `(ρ π.ε x0) hx0 (fun c => L.eig c x0 hx0F) hAv`. Establish `kills : ∀ x, χ x = 0 → ρh x (ρh π.g u) = 0`. Introduce `x hx`. Establish `hxw : x ∈ w` using `L.ker ▸ (RingHom.mem_ker.2 hx)`.

Take `⟨u0, d1⟩` from `π.gen x hxw`. Establish `hd : (p : C) ∣ x * π.g`. Establish `e : x * π.g = (π.ε * x - π.a * u0) * π.g - x * (π.ε * π.g - π.g) + u0 * (π.a * π.g)` using `by ring`. Rewrite using `[e]`. Conclude with `dvd_add (dvd_sub (d1.mul_right _) (π.geps.mul_left _)) ((Dvd.intro _ π.prod.symm).mul_left _)`.

Establish `h` using `hdvd _ hd`. Rewrite `h` using `[map_mul]`. Rewrite using `[← Module.End.mul_apply, h]`. Both sides reduce to the same expression. Establish `eig : ∀ c, ρ c (ρ π.g u) = χ c • ρ π.g u`.

Introduce `c`. Establish `hyG : ρh π.g u ∈ (ρh c).maxGenEigenspace (χ c)`. Establish `hcm : Commute (ρh c) (ρh π.g)` using `by show ρh c * ρh π.g = ρh π.g * ρh c`. Rewrite using `[← map_mul, ← map_mul, mul_comm]`. Conclude with `Module.End.mapsTo_maxGenEigenspace_of_comm hcm _ ((Submodule.mem_iInf _).1 hu c)`.

Use `eig_of_gen p (ρh c) (χ c) f hf (hfix c) _ hyG ?_` and prove the remaining obligations. Establish `hw : χ (c ^ (p ^ f) - c) = 0` using `by rw [map_sub, map_pow, hfix, sub_self]`. Establish `h` using `kills _ hw`. Rewrite `h` using `[map_sub, map_pow, LinearMap.sub_apply, sub_eq_zero]`. Then use the resulting hypothesis. Take `⟨ξ, hξ1, hξ2⟩` from `Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance`.

Establish `hεε : ∀ y, ρ π.ε (ρ π.ε y) = ρ π.ε y` using `fun y => by`. Establish `h` using `congrArg (fun T : Module.End k P => T y) hε`. Conclude with `h`. Establish `hεg : ∀ y, ρ π.ε (ρ π.g y) = ρ π.g y` using `fun y => by`. Establish `h` using `hdvd _ π.geps`.

Rewrite `h` using `[map_sub, map_mul, sub_eq_zero]`. Conclude with `congrArg (fun T : Module.End k P => T y) h`. Use `⟨ξ ∘ₗ ρ π.ε, fun y => ?_, fun z => ?_, ρ π.g u, eig, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, hεε]`. Simplify using `only [LinearMap.comp_apply, hεg]`.

Establish `hm : ρh π.g (A z) ∈ (Submodule.span k (Set.range A)).map (ρh π.g)` using `Submodule.mem_map_of_mem (Submodule.subset_span ⟨z, rfl⟩)`. Establish `h` using `Submodule.mem_map_of_mem (f := ξ) hm`. Rewrite `h` using `[hξ2, Submodule.mem_bot]`. Conclude with `h`. Simplify using `only [LinearMap.comp_apply, hεg]`.

Conclude with `hξ1`.
-/
theorem UpperTheory.Gal.Ord.alg2 :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k p] (C : Type) [CommRing C] (w : Ideal C) (f : ℕ), 0 < f →
      Nat.card (C ⧸ w) = p ^ f → ∀ (π : Par p w f) (χ : C →+* k) (P : Type 1) [AddCommGroup P] [Module k P] (ρ : C → Module.End k P) (F : Submodule k P)
      (Φ : P →+ P), Lin p π χ ρ F Φ →
      ∃ x : Module.Dual k P, (∀ y, x (ρ π.ε y) = x y) ∧ (∀ z, x (ρ π.g (Φ^[f] z)) = 0) ∧ ∃ y, (∀ c, ρ c y = χ c • y) ∧ x y ≠ 0 := by
  intro p _ k _ _ _ C _ w f hf hcard π χ P _ _ ρ F Φ L
  haveI := L.fin
  let ρh : C →+* Module.End k P :=
    { toFun := ρ, map_one' := L.one, map_mul' := L.mul, map_add' := L.add
      map_zero' := by
        have h := L.add 0 0
        simpa using h }
  have hp : ρh (p : C) = 0 := by
    rw [map_natCast, ← map_natCast (algebraMap k (Module.End k P)), CharP.cast_eq_zero k p, map_zero]
  have hdvd : ∀ x : C, (p : C) ∣ x → ρh x = 0 := by
    rintro _ ⟨d, rfl⟩
    rw [map_mul, hp, zero_mul]
  have hfix : ∀ c, χ c ^ (p ^ f) = χ c := by
    have e : (C ⧸ w) ≃ χ.range :=
      ((Ideal.quotEquivOfEq L.ker.symm).trans (RingHom.quotientKerEquivRange χ)).toEquiv
    have hcard' : Nat.card χ.range = p ^ f := (Nat.card_congr e).symm.trans hcard
    haveI : Finite χ.range := Nat.finite_of_card_ne_zero (by
      rw [hcard']; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    intro c
    have h := pow_card_subring χ.range ⟨χ c, c, rfl⟩
    rw [hcard'] at h
    exact congrArg Subtype.val h
  have hinj : Function.Injective fun x : k => x ^ (p ^ f) := by
    intro x y h
    exact (iterateFrobenius k p f).injective (by simpa [iterateFrobenius_def] using h)
  let A : P →+ P :=
    { toFun := (⇑Φ)^[f], map_zero' := iterate_map_zero Φ f, map_add' := iterate_map_add Φ f }
  have hsemiN : ∀ (n : ℕ) (l : k) x, (⇑Φ)^[n] (l • x) = l ^ (p ^ n) • (⇑Φ)^[n] x := by
    intro n
    induction n with
    | zero => intro l x; simp
    | succ n ih =>
      intro l x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, L.semi, ← pow_mul, pow_succ]
  have hcommN : ∀ (n : ℕ) c x, (⇑Φ)^[n] (ρ c x) = ρ c ((⇑Φ)^[n] x) := by
    intro n
    induction n with
    | zero => intro c x; rfl
    | succ n ih =>
      intro c x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, L.comm]
  obtain ⟨x0, hx0F, hx0, -⟩ := L.line
  have hAv : A (ρ π.ε x0) = 0 := by
    show (⇑Φ)^[f] (ρ π.ε x0) = 0
    have e : (⇑Φ)^[f] (ρ π.ε x0) = (⇑Φ)^[f - 1] (Φ (ρ π.ε x0)) := by
      rw [← Function.iterate_succ_apply]
      congr 2
      omega
    rw [e, L.comm, (L.kerΦ x0).2 hx0F, map_zero, iterate_map_zero]
  have hε : ρh π.ε * ρh π.ε = ρh π.ε := by
    have h := hdvd _ π.idem
    rwa [map_sub, map_mul, sub_eq_zero] at h
  have hε1 : χ π.ε = 1 := by
    have h : π.ε - 1 ∈ RingHom.ker χ := L.ker ▸ π.one
    rwa [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at h
  have hnil : ∃ e : ℕ, ρh π.a ^ e * ρh π.ε = 0 := by
    obtain ⟨e, he⟩ := π.nil
    refine ⟨e, ?_⟩
    have h := hdvd _ he
    rwa [map_mul, map_pow] at h
  obtain ⟨u, hu, hnot⟩ := exists_not_mem ρh χ (p ^ f) (pow_pos (Fact.out : p.Prime).pos f) A
    (fun l x => hsemiN f l x) (fun c x => hcommN f c x) hfix hinj π.ε π.a π.g hε hε1 hnil
    (fun x h => by
      obtain ⟨u, v, e⟩ := L.annG x h
      exact ⟨u, v, e⟩)
    (ρ π.ε x0) hx0 (fun c => L.eig c x0 hx0F) hAv
  have kills : ∀ x, χ x = 0 → ρh x (ρh π.g u) = 0 := by
    intro x hx
    have hxw : x ∈ w := L.ker ▸ (RingHom.mem_ker.2 hx)
    obtain ⟨u0, d1⟩ := π.gen x hxw
    have hd : (p : C) ∣ x * π.g := by
      have e : x * π.g = (π.ε * x - π.a * u0) * π.g - x * (π.ε * π.g - π.g) + u0 * (π.a * π.g) := by ring
      rw [e]
      exact dvd_add (dvd_sub (d1.mul_right _) (π.geps.mul_left _)) ((Dvd.intro _ π.prod.symm).mul_left _)
    have h := hdvd _ hd
    rw [map_mul] at h
    rw [← Module.End.mul_apply, h]
    rfl
  have eig : ∀ c, ρ c (ρ π.g u) = χ c • ρ π.g u := by
    intro c
    have hyG : ρh π.g u ∈ (ρh c).maxGenEigenspace (χ c) := by
      have hcm : Commute (ρh c) (ρh π.g) := by
        show ρh c * ρh π.g = ρh π.g * ρh c
        rw [← map_mul, ← map_mul, mul_comm]
      exact Module.End.mapsTo_maxGenEigenspace_of_comm hcm _ ((Submodule.mem_iInf _).1 hu c)
    refine eig_of_gen p (ρh c) (χ c) f hf (hfix c) _ hyG ?_
    have hw : χ (c ^ (p ^ f) - c) = 0 := by rw [map_sub, map_pow, hfix, sub_self]
    have h := kills _ hw
    rwa [map_sub, map_pow, LinearMap.sub_apply, sub_eq_zero] at h
  obtain ⟨ξ, hξ1, hξ2⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hεε : ∀ y, ρ π.ε (ρ π.ε y) = ρ π.ε y := fun y => by
    have h := congrArg (fun T : Module.End k P => T y) hε
    exact h
  have hεg : ∀ y, ρ π.ε (ρ π.g y) = ρ π.g y := fun y => by
    have h := hdvd _ π.geps
    rw [map_sub, map_mul, sub_eq_zero] at h
    exact congrArg (fun T : Module.End k P => T y) h
  refine ⟨ξ ∘ₗ ρ π.ε, fun y => ?_, fun z => ?_, ρ π.g u, eig, ?_⟩
  · simp only [LinearMap.comp_apply, hεε]
  · simp only [LinearMap.comp_apply, hεg]
    have hm : ρh π.g (A z) ∈ (Submodule.span k (Set.range A)).map (ρh π.g) :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨z, rfl⟩)
    have h := Submodule.mem_map_of_mem (f := ξ) hm
    rw [hξ2, Submodule.mem_bot] at h
    exact h
  · simp only [LinearMap.comp_apply, hεg]
    exact hξ1
