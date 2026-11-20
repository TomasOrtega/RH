import Formalism.PadicSubsetSums.CentralIdempotents.SchurOrthogonalityCompact

open Polynomial
open scoped TensorProduct

namespace Formalism.IrreducibleCountingLemmas.Z

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Establish `hinj : Function.Injective (aeval g p)`. Use `(injective_iff_map_eq_zero (aeval g p)).2 fun w hw => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hw0`. Conclude with `hcon ⟨w, hw0, hw⟩`.

Use `haveI : Fact (Irreducible p) := ⟨hp⟩`. Establish `hunit : IsUnit (aeval g p)` using `by first`. Consider the case `exact (Module.End.isUnit_iff _).2 ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩`. Consider the case `exact (LinearMap.isUnit_iff_ker_eq_bot _).2 (LinearMap.ker_eq_bot.2 hinj)`. Establish `hunitL` using `hunit.map (Module.End.baseChangeHom K (AdjoinRoot p) V)`.

Establish `hE : Module.End.baseChangeHom K (AdjoinRoot p) V (aeval g p) = aeval (g.baseChange (AdjoinRoot p)) (p.map (algebraMap K (AdjoinRoot p)))`. Rewrite using `[Polynomial.aeval_map_algebraMap, ← Polynomial.aeval_algHom_apply]`. Both sides reduce to the same expression. Establish `hpr : Polynomial.eval (AdjoinRoot.root p) (p.map (algebraMap K (AdjoinRoot p))) = 0`. Rewrite using `[Polynomial.eval_map, AdjoinRoot.algebraMap_eq]`.

Conclude with `AdjoinRoot.eval₂_root p`. Establish `hev : Module.End.HasEigenvalue (g.baseChange (AdjoinRoot p)) (AdjoinRoot.root p)`. Rewrite using `[Module.End.hasEigenvalue_iff_isRoot_charpoly, LinearMap.charpoly_baseChange]`. Conclude with `Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (Polynomial.map_dvd _ hdvd) hpr`. Take `⟨v, hv⟩` from `hev.exists_hasEigenvector`.

Establish `h0 : aeval (g.baseChange (AdjoinRoot p)) (p.map (algebraMap K (AdjoinRoot p))) v = 0`. Rewrite using `[Module.End.aeval_apply_of_hasEigenvector hv, hpr, zero_smul]`. Rewrite `h0` using `[← hE]`. Establish `hbij : Function.Injective (Module.End.baseChangeHom K (AdjoinRoot p) V (aeval g p))` using `by first`. Consider the case `exact ((Module.End.isUnit_iff _).1 hunitL).1`.

Consider the case `exact LinearMap.ker_eq_bot.1 ((LinearMap.isUnit_iff_ker_eq_bot _).1 hunitL)`. Conclude with `hv.2 (hbij (h0.trans (map_zero _).symm))`.
-/
theorem exists_ne_zero_aeval_eq_zero {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : Module.End K V) (p : K[X]) (hp : Irreducible p)
    (hdvd : p ∣ g.charpoly) : ∃ w : V, w ≠ 0 ∧ aeval g p w = 0 := by
  classical
  by_contra hcon
  have hinj : Function.Injective (aeval g p) := by
    refine (injective_iff_map_eq_zero (aeval g p)).2 fun w hw => ?_
    by_contra hw0
    exact hcon ⟨w, hw0, hw⟩
  haveI : Fact (Irreducible p) := ⟨hp⟩
  have hunit : IsUnit (aeval g p) := by
    first
      | exact (Module.End.isUnit_iff _).2 ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
      | exact (LinearMap.isUnit_iff_ker_eq_bot _).2 (LinearMap.ker_eq_bot.2 hinj)
  have hunitL := hunit.map (Module.End.baseChangeHom K (AdjoinRoot p) V)
  have hE : Module.End.baseChangeHom K (AdjoinRoot p) V (aeval g p)
      = aeval (g.baseChange (AdjoinRoot p)) (p.map (algebraMap K (AdjoinRoot p))) := by
    rw [Polynomial.aeval_map_algebraMap, ← Polynomial.aeval_algHom_apply]
    rfl
  have hpr : Polynomial.eval (AdjoinRoot.root p) (p.map (algebraMap K (AdjoinRoot p))) = 0 := by
    rw [Polynomial.eval_map, AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.eval₂_root p
  have hev : Module.End.HasEigenvalue (g.baseChange (AdjoinRoot p)) (AdjoinRoot.root p) := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, LinearMap.charpoly_baseChange]
    exact Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (Polynomial.map_dvd _ hdvd) hpr
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  have h0 : aeval (g.baseChange (AdjoinRoot p)) (p.map (algebraMap K (AdjoinRoot p))) v = 0 := by
    rw [Module.End.aeval_apply_of_hasEigenvector hv, hpr, zero_smul]
  rw [← hE] at h0
  have hbij : Function.Injective (Module.End.baseChangeHom K (AdjoinRoot p) V (aeval g p)) := by
    first
      | exact ((Module.End.isUnit_iff _).1 hunitL).1
      | exact LinearMap.ker_eq_bot.1 ((LinearMap.isUnit_iff_ker_eq_bot _).1 hunitL)
  exact hv.2 (hbij (h0.trans (map_zero _).symm))

/- English proof (translation)
Establish `hm : ∀ (f h : Module.End K V) (x : V), (f * h) x = f (h x)` using `fun _ _ _ => rfl`. Establish `hadd : ∀ (f h : Module.End K V) (x : V), (f + h) x = f x + h x` using `fun _ _ _ => rfl`. Establish `hone : ∀ x : V, (1 : Module.End K V) x = x` using `fun _ => rfl`. Establish `hkill : ∀ (s t : K[X]) (x : V), aeval g s x = 0 → aeval g (t * s) x = 0`. Introduce `s t x hx`.

Rewrite using `[map_mul, hm, hx, map_zero]`. Establish `hsq : Squarefree g.charpoly` using `hs.squarefree`. Use `WfDvdMonoid.induction_on_irreducible d ?_ ?_ ?_` and prove the remaining obligations. Introduce `h0`. Conclude with `absurd (zero_dvd_iff.1 h0) (LinearMap.charpoly_monic g).ne_zero`.

Introduce `u hu _`. Conclude with `⟨0, map_zero _, fun q _ => hu.dvd⟩`. Introduce `a i _ hi ih hdvd`. Establish `ha : a ∣ g.charpoly` using `dvd_of_mul_left_dvd hdvd`. Establish `hid : i ∣ g.charpoly` using `dvd_of_mul_right_dvd hdvd`.

Take `⟨ea, hea0, hea⟩` from `ih ha`. Take `⟨w, hw0, hw⟩` from `exists_ne_zero_aeval_eq_zero g i hi hid`. Establish `hcopOf : ∀ n : K[X], ¬ i ∣ n → IsCoprime i n` using `fun n h => by first`. Consider the case `exact (Irreducible.coprime_iff_not_dvd hi).2 h`. Consider the case `exact (Irreducible.isCoprime_iff_not_dvd hi).2 h`.

Establish `hcop : IsCoprime i a` using `hcopOf a fun hia => hi.1 (hsq i (dvd_trans (mul_dvd_mul_left i hia) hdvd))`. Use `⟨ea + w, ?_, fun q hq => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, hkill a i ea hea0, mul_comm, hkill i a w hw, add_zero]`. Establish `hw' : aeval g (i * q) w = 0`. Rewrite using `[mul_comm]`.

Conclude with `hkill i q w hw`. Establish `hqi : aeval g (i * q) ea = 0`. Establish `h1` using `hkill q i _ hq`. Rewrite `h1` using `[map_add, hw', add_zero]`. Then use the resulting hypothesis. Establish `haq : a ∣ q`.

Establish `h2 : a ∣ i * q` using `hea _ hqi`. Use `first`. Consider the case `exact hcop.symm.dvd_of_dvd_mul_left h2`. Consider the case `exact hcop.symm.dvd_of_dvd_mul_right (by rwa [mul_comm] at h2)`. Establish `hea' : aeval g (a * q) ea = 0`.

Rewrite using `[mul_comm]`. Conclude with `hkill a q ea hea0`. Establish `hwq : aeval g (a * q) w = 0`. Establish `h1` using `hkill q a _ hq`. Rewrite `h1` using `[map_add, hea', zero_add]`. Then use the resulting hypothesis.

Establish `hiaq : i ∣ a * q`. Assume the negation of the conclusion as `hn`. Take `⟨u, t, hut⟩` from `hcopOf _ hn`. Apply `hw0` to reduce the goal to its premises. Establish `h2 : aeval g (u * i + t * (a * q)) w = 0`.

Rewrite using `[map_add, hadd, hkill i u w hw, hkill (a * q) t w hwq, add_zero]`. Rewrite `h2` using `[hut, map_one, hone]`. Then use the resulting hypothesis. Establish `hiq : i ∣ q` using `by first`. Consider the case `exact hcop.dvd_of_dvd_mul_left hiaq`. Consider the case `exact hcop.dvd_of_dvd_mul_right (by rwa [mul_comm] at hiaq)`.

Conclude with `hcop.mul_dvd hiq haq`.
-/
theorem exists_annihilator_eq {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : Module.End K V) (hs : g.charpoly.Separable) (d : K[X]) :
    d ∣ g.charpoly → ∃ e : V, aeval g d e = 0 ∧ ∀ q : K[X], aeval g q e = 0 → d ∣ q := by
  classical
  have hm : ∀ (f h : Module.End K V) (x : V), (f * h) x = f (h x) := fun _ _ _ => rfl
  have hadd : ∀ (f h : Module.End K V) (x : V), (f + h) x = f x + h x := fun _ _ _ => rfl
  have hone : ∀ x : V, (1 : Module.End K V) x = x := fun _ => rfl
  have hkill : ∀ (s t : K[X]) (x : V), aeval g s x = 0 → aeval g (t * s) x = 0 := by
    intro s t x hx
    rw [map_mul, hm, hx, map_zero]
  have hsq : Squarefree g.charpoly := hs.squarefree
  refine WfDvdMonoid.induction_on_irreducible d ?_ ?_ ?_
  · intro h0
    exact absurd (zero_dvd_iff.1 h0) (LinearMap.charpoly_monic g).ne_zero
  · intro u hu _
    exact ⟨0, map_zero _, fun q _ => hu.dvd⟩
  · intro a i _ hi ih hdvd
    have ha : a ∣ g.charpoly := dvd_of_mul_left_dvd hdvd
    have hid : i ∣ g.charpoly := dvd_of_mul_right_dvd hdvd
    obtain ⟨ea, hea0, hea⟩ := ih ha
    obtain ⟨w, hw0, hw⟩ := exists_ne_zero_aeval_eq_zero g i hi hid
    have hcopOf : ∀ n : K[X], ¬ i ∣ n → IsCoprime i n := fun n h => by
      first
        | exact (Irreducible.coprime_iff_not_dvd hi).2 h
        | exact (Irreducible.isCoprime_iff_not_dvd hi).2 h
    have hcop : IsCoprime i a := hcopOf a fun hia =>
      hi.1 (hsq i (dvd_trans (mul_dvd_mul_left i hia) hdvd))
    refine ⟨ea + w, ?_, fun q hq => ?_⟩
    · rw [map_add, hkill a i ea hea0, mul_comm, hkill i a w hw, add_zero]
    · have hw' : aeval g (i * q) w = 0 := by
        rw [mul_comm]
        exact hkill i q w hw
      have hqi : aeval g (i * q) ea = 0 := by
        have h1 := hkill q i _ hq
        rwa [map_add, hw', add_zero] at h1
      have haq : a ∣ q := by
        have h2 : a ∣ i * q := hea _ hqi
        first
          | exact hcop.symm.dvd_of_dvd_mul_left h2
          | exact hcop.symm.dvd_of_dvd_mul_right (by rwa [mul_comm] at h2)
      have hea' : aeval g (a * q) ea = 0 := by
        rw [mul_comm]
        exact hkill a q ea hea0
      have hwq : aeval g (a * q) w = 0 := by
        have h1 := hkill q a _ hq
        rwa [map_add, hea', zero_add] at h1
      have hiaq : i ∣ a * q := by
        by_contra hn
        obtain ⟨u, t, hut⟩ := hcopOf _ hn
        apply hw0
        have h2 : aeval g (u * i + t * (a * q)) w = 0 := by
          rw [map_add, hadd, hkill i u w hw, hkill (a * q) t w hwq, add_zero]
        rwa [hut, map_one, hone] at h2
      have hiq : i ∣ q := by
        first
          | exact hcop.dvd_of_dvd_mul_left hiaq
          | exact hcop.dvd_of_dvd_mul_right (by rwa [mul_comm] at hiaq)
      exact hcop.mul_dvd hiq haq

/- English proof (translation)
Unfold `BCCyclicVector`. Introduce `K V _ _ _ _ g hs`. Take `⟨e, -, he⟩` from `exists_annihilator_eq g hs g.charpoly dvd_rfl`. Set `φ : K[X] →ₗ[K] V` to `{ toFun := fun q => aeval g q e map_add' := fun a b => by simp map_smul' := fun c a => by simp }`. Set `ψ : Polynomial.degreeLT K (Module.finrank K V) →ₗ[K] V` to `φ.comp (Polynomial.degreeLT K (Module.finrank K V)).subtype`.

Establish `hdeg : g.charpoly.degree = (Module.finrank K V : WithBot ℕ)`. Rewrite using `[Polynomial.degree_eq_natDegree (LinearMap.charpoly_monic g).ne_zero, LinearMap.charpoly_natDegree]`. Establish `hinj : Function.Injective ψ`. Use `(injective_iff_map_eq_zero ψ).2 fun x hx => ?_` and prove the remaining obligations. Establish `hmem` using `Polynomial.mem_degreeLT.1 x.2`.

Establish `hd : g.charpoly ∣ x.1` using `he x.1 hx`. Conclude with `Subtype.ext (Polynomial.eq_zero_of_dvd_of_degree_lt hd (by rw [hdeg]; exact hmem))`. Use `haveI : FiniteDimensional K (Polynomial.degreeLT K (Module.finrank K V)) := LinearEquiv.finiteDimensional (Polynomial.degreeLTEquiv K (Module.finrank K V)).symm`. Establish `hfr : Module.finrank K (Polynomial.degreeLT K (Module.finrank K V)) = Module.finrank K V`. Rewrite using `[(Polynomial.degreeLTEquiv K (Module.finrank K V)).finrank_eq]`.

Simplify using the standard rewrite rules. Establish `hsurj` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hinj`. Use `⟨e, fun v => ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `hsurj v`. Conclude with `⟨x.1, hx⟩`.
-/
theorem base_change_cyclic_vector : BCCyclicVector := by
  unfold BCCyclicVector
  intro K V _ _ _ _ g hs
  classical
  obtain ⟨e, -, he⟩ := exists_annihilator_eq g hs g.charpoly dvd_rfl
  let φ : K[X] →ₗ[K] V :=
    { toFun := fun q => aeval g q e
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
  let ψ : Polynomial.degreeLT K (Module.finrank K V) →ₗ[K] V :=
    φ.comp (Polynomial.degreeLT K (Module.finrank K V)).subtype
  have hdeg : g.charpoly.degree = (Module.finrank K V : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree (LinearMap.charpoly_monic g).ne_zero,
      LinearMap.charpoly_natDegree]
  have hinj : Function.Injective ψ := by
    refine (injective_iff_map_eq_zero ψ).2 fun x hx => ?_
    have hmem := Polynomial.mem_degreeLT.1 x.2
    have hd : g.charpoly ∣ x.1 := he x.1 hx
    exact Subtype.ext (Polynomial.eq_zero_of_dvd_of_degree_lt hd (by rw [hdeg]; exact hmem))
  haveI : FiniteDimensional K (Polynomial.degreeLT K (Module.finrank K V)) :=
    LinearEquiv.finiteDimensional (Polynomial.degreeLTEquiv K (Module.finrank K V)).symm
  have hfr : Module.finrank K (Polynomial.degreeLT K (Module.finrank K V)) = Module.finrank K V := by
    rw [(Polynomial.degreeLTEquiv K (Module.finrank K V)).finrank_eq]
    simp
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hinj
  refine ⟨e, fun v => ?_⟩
  obtain ⟨x, hx⟩ := hsurj v
  exact ⟨x.1, hx⟩

end Formalism.IrreducibleCountingLemmas.Z
