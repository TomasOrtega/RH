import Mathlib

open Polynomial
open scoped TensorProduct

namespace GlobalTheory.SepCentralizer

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hinj : Function.Injective (aeval g p)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `w hw`.

Assume the negation of the conclusion as `hw0`. Conclude with `hcon w hw0 hw`. Establish `hunit : IsUnit (aeval g p)` using `(Module.End.isUnit_iff _).2 ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩`. Establish `: Fact (Irreducible p)` using `⟨hp⟩`. Set `L` to `AdjoinRoot p`.

Set `gL : Module.End L (L ⊗[K] V)` to `Module.End.baseChangeHom K L V g`. Establish `hgL : gL = g.baseChange L` using `rfl`. Establish `hroot : gL.charpoly.IsRoot (AdjoinRoot.root p)`. Rewrite using `[hgL, LinearMap.charpoly_baseChange, IsRoot.def, eval_map_algebraMap]`. Take `⟨r, hr⟩` from `hdvd`.

Rewrite using `[hr, map_mul, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_mul]`. Take `⟨v, hv⟩` from `((Module.End.hasEigenvalue_iff_isRoot_charpoly gL _).2 hroot).exists_hasEigenvector`. Establish `h1 : aeval gL (p.map (algebraMap K L)) v = 0`. Rewrite using `[Module.End.aeval_apply_of_hasEigenvector hv, eval_map_algebraMap, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_smul]`. Establish `h2 : aeval gL (p.map (algebraMap K L)) = Module.End.baseChangeHom K L V (aeval g p)`.

Rewrite using `[aeval_map_algebraMap, ← aeval_algHom_apply]`. Establish `h3 : IsUnit (Module.End.baseChangeHom K L V (aeval g p))` using `hunit.map _`. Rewrite `h1` using `[h2]`. Establish `h4` using `((Module.End.isUnit_iff _).1 h3).1`. Conclude with `hv.2 (h4 (by rw [h1, map_zero]))`.
-/
theorem exists_ne_zero_aeval_eq_zero {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : Module.End K V) (p : K[X]) (hp : Irreducible p)
    (hdvd : p ∣ g.charpoly) : ∃ w : V, w ≠ 0 ∧ aeval g p w = 0 := by
  by_contra hcon
  push_neg at hcon
  have hinj : Function.Injective (aeval g p) := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    by_contra hw0
    exact hcon w hw0 hw
  have hunit : IsUnit (aeval g p) :=
    (Module.End.isUnit_iff _).2 ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  have : Fact (Irreducible p) := ⟨hp⟩
  let L := AdjoinRoot p
  let gL : Module.End L (L ⊗[K] V) := Module.End.baseChangeHom K L V g
  have hgL : gL = g.baseChange L := rfl
  have hroot : gL.charpoly.IsRoot (AdjoinRoot.root p) := by
    rw [hgL, LinearMap.charpoly_baseChange, IsRoot.def, eval_map_algebraMap]
    obtain ⟨r, hr⟩ := hdvd
    rw [hr, map_mul, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_mul]
  obtain ⟨v, hv⟩ :=
    ((Module.End.hasEigenvalue_iff_isRoot_charpoly gL _).2 hroot).exists_hasEigenvector
  have h1 : aeval gL (p.map (algebraMap K L)) v = 0 := by
    rw [Module.End.aeval_apply_of_hasEigenvector hv, eval_map_algebraMap, AdjoinRoot.aeval_eq,
      AdjoinRoot.mk_self, zero_smul]
  have h2 : aeval gL (p.map (algebraMap K L)) = Module.End.baseChangeHom K L V (aeval g p) := by
    rw [aeval_map_algebraMap, ← aeval_algHom_apply]
  have h3 : IsUnit (Module.End.baseChangeHom K L V (aeval g p)) := hunit.map _
  rw [h2] at h1
  have h4 := ((Module.End.isUnit_iff _).1 h3).1
  exact hv.2 (h4 (by rw [h1, map_zero]))

/- English proof (translation)
Proceed by induction on `d using UniqueFactorizationMonoid.induction_on_coprime with`. Consider the case `h0`. Introduce `h`. Conclude with `absurd (zero_dvd_iff.1 h) g.charpoly_monic.ne_zero`. Consider the case `h1 hx`.

Introduce `_`. Conclude with `⟨0, map_zero _, fun q _ => hx.dvd⟩`. Consider the case `hpr i hp`. Name the introduced variables `p`. Introduce `h`.

Break down `i with _ | _ | i` into its components or cases. Conclude with `⟨0, map_zero _, fun q _ => by simp⟩`. Rewrite `h`, the goal using `[zero_add, pow_one]`. Take `⟨w, hw0, hw⟩` from `exists_ne_zero_aeval_eq_zero g p hp.irreducible h`. Use `⟨w, hw, fun q hq => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hnd`. Take `⟨a, b, hab⟩` from `(hp.irreducible.coprime_iff_not_dvd).2 hnd`. Apply `hw0` to reduce the goal to its premises. Use `congrArg (fun r => aeval g r w) hab` as an intermediate fact. Simplify using `only [map_add, map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply, hw, hq, map_zero, add_zero, Module.End.one_apply] at this`.

Conclude with `this.symm`. It suffices to derive a contradiction. Establish `h2 : p * p ∣ g.charpoly`. Use `dvd_trans ?_ h` and prove the remaining obligations. Conclude with `⟨p ^ i, by ring⟩`.

Conclude with `hp.not_isUnit (hs.squarefree p h2)`. Consider the case `hcp hxy hx hy`. Name the introduced variables `x y`. Introduce `h`. Establish `hco : IsCoprime x y` using `hxy.isCoprime`.

Take `⟨e₁, h1, h1'⟩` from `hx (dvd_trans (dvd_mul_right x y) h)`. Take `⟨e₂, h2, h2'⟩` from `hy (dvd_trans (dvd_mul_left y x) h)`. Use `⟨e₁ + e₂, ?_, fun q hq => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add]`. Establish `a1 : aeval g (x * y) e₁ = 0`.

Rewrite using `[mul_comm, map_mul, Module.End.mul_apply, h1, map_zero]`. Establish `a2 : aeval g (x * y) e₂ = 0`. Rewrite using `[map_mul, Module.End.mul_apply, h2, map_zero]`. Rewrite using `[a1, a2, add_zero]`. Rewrite `hq` using `[map_add]`.

Establish `b1 : x ∣ q`. Establish `: aeval g (q * y) e₁ = 0`. Establish `c` using `congrArg (aeval g y) hq`. Rewrite `c` using `[map_add, map_zero, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, mul_comm y q]`. Establish `c2 : aeval g (q * y) e₂ = 0`.

Rewrite using `[map_mul, Module.End.mul_apply, h2, map_zero]`. Rewrite `c` using `[c2, add_zero]`. Then use the resulting hypothesis. Conclude with `hco.dvd_of_dvd_mul_right (h1' _ this)`. Establish `b2 : y ∣ q`. Establish `: aeval g (q * x) e₂ = 0`.

Establish `c` using `congrArg (aeval g x) hq`. Rewrite `c` using `[map_add, map_zero, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, mul_comm x q]`. Establish `c2 : aeval g (q * x) e₁ = 0`. Rewrite using `[map_mul, Module.End.mul_apply, h1, map_zero]`. Rewrite `c` using `[c2, zero_add]`. Then use the resulting hypothesis.

Conclude with `hco.symm.dvd_of_dvd_mul_right (h2' _ this)`. Conclude with `hco.mul_dvd b1 b2`.
-/
theorem exists_annihilator_eq {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : Module.End K V) (hs : g.charpoly.Separable) (d : K[X]) :
    d ∣ g.charpoly → ∃ e : V, aeval g d e = 0 ∧ ∀ q : K[X], aeval g q e = 0 → d ∣ q := by
  induction d using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 =>
    intro h
    exact absurd (zero_dvd_iff.1 h) g.charpoly_monic.ne_zero
  | h1 hx =>
    intro _
    exact ⟨0, map_zero _, fun q _ => hx.dvd⟩
  | hpr i hp =>
    rename_i p
    intro h
    rcases i with _ | _ | i
    · exact ⟨0, map_zero _, fun q _ => by simp⟩
    · rw [zero_add, pow_one] at h ⊢
      obtain ⟨w, hw0, hw⟩ := exists_ne_zero_aeval_eq_zero g p hp.irreducible h
      refine ⟨w, hw, fun q hq => ?_⟩
      by_contra hnd
      obtain ⟨a, b, hab⟩ := (hp.irreducible.coprime_iff_not_dvd).2 hnd
      apply hw0
      have := congrArg (fun r => aeval g r w) hab
      simp only [map_add, map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply, hw, hq,
        map_zero, add_zero, Module.End.one_apply] at this
      exact this.symm
    · exfalso
      have h2 : p * p ∣ g.charpoly := by
        refine dvd_trans ?_ h
        exact ⟨p ^ i, by ring⟩
      exact hp.not_isUnit (hs.squarefree p h2)
  | hcp hxy hx hy =>
    rename_i x y
    intro h
    have hco : IsCoprime x y := hxy.isCoprime
    obtain ⟨e₁, h1, h1'⟩ := hx (dvd_trans (dvd_mul_right x y) h)
    obtain ⟨e₂, h2, h2'⟩ := hy (dvd_trans (dvd_mul_left y x) h)
    refine ⟨e₁ + e₂, ?_, fun q hq => ?_⟩
    · rw [map_add]
      have a1 : aeval g (x * y) e₁ = 0 := by
        rw [mul_comm, map_mul, Module.End.mul_apply, h1, map_zero]
      have a2 : aeval g (x * y) e₂ = 0 := by
        rw [map_mul, Module.End.mul_apply, h2, map_zero]
      rw [a1, a2, add_zero]
    · rw [map_add] at hq
      have b1 : x ∣ q := by
        have : aeval g (q * y) e₁ = 0 := by
          have c := congrArg (aeval g y) hq
          rw [map_add, map_zero, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul,
            mul_comm y q] at c
          have c2 : aeval g (q * y) e₂ = 0 := by
            rw [map_mul, Module.End.mul_apply, h2, map_zero]
          rwa [c2, add_zero] at c
        exact hco.dvd_of_dvd_mul_right (h1' _ this)
      have b2 : y ∣ q := by
        have : aeval g (q * x) e₂ = 0 := by
          have c := congrArg (aeval g x) hq
          rw [map_add, map_zero, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul,
            mul_comm x q] at c
          have c2 : aeval g (q * x) e₁ = 0 := by
            rw [map_mul, Module.End.mul_apply, h1, map_zero]
          rwa [c2, zero_add] at c
        exact hco.symm.dvd_of_dvd_mul_right (h2' _ this)
      exact hco.mul_dvd b1 b2

/- English proof (translation)
Take `⟨e, -, he⟩` from `exists_annihilator_eq g hs g.charpoly dvd_rfl`. Use `⟨e, ?_⟩` and prove the remaining obligations. Set `φ : K[X] →ₗ[K] V` to `(LinearMap.applyₗ e) ∘ₗ (aeval g).toLinearMap`. Establish `hφ : ∀ p, φ p = aeval g p e` using `fun p => rfl`. Set `ψ : degreeLT K (Module.finrank K V) →ₗ[K] V` to `φ ∘ₗ (degreeLT K (Module.finrank K V)).subtype`.

Establish `hinj : Function.Injective ψ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `q hq`. Establish `h1 : g.charpoly ∣ (q : K[X])` using `he _ hq`. Establish `h2 : (q : K[X]).degree < g.charpoly.degree`.

Rewrite using `[degree_eq_natDegree g.charpoly_monic.ne_zero, LinearMap.charpoly_natDegree]`. Conclude with `mem_degreeLT.1 q.2`. Conclude with `Subtype.ext (eq_zero_of_dvd_of_degree_lt h1 h2)`. Establish `hfin : Module.finrank K (degreeLT K (Module.finrank K V)) = Module.finrank K V`. Rewrite using `[(degreeLTEquiv K (Module.finrank K V)).finrank_eq, Module.finrank_fin_fun]`.

Establish `: FiniteDimensional K (degreeLT K (Module.finrank K V))` using `(degreeLTEquiv K (Module.finrank K V)).symm.finiteDimensional`. Establish `hsurj` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).1 hinj`. Introduce `v`. Take `⟨q, hq⟩` from `hsurj v`. Conclude with `⟨q, hq⟩`.
-/
theorem exists_cyclic {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : Module.End K V) (hs : g.charpoly.Separable) :
    ∃ e : V, ∀ v : V, ∃ q : K[X], aeval g q e = v := by
  obtain ⟨e, -, he⟩ := exists_annihilator_eq g hs g.charpoly dvd_rfl
  refine ⟨e, ?_⟩
  let φ : K[X] →ₗ[K] V := (LinearMap.applyₗ e) ∘ₗ (aeval g).toLinearMap
  have hφ : ∀ p, φ p = aeval g p e := fun p => rfl
  let ψ : degreeLT K (Module.finrank K V) →ₗ[K] V := φ ∘ₗ (degreeLT K (Module.finrank K V)).subtype
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    have h1 : g.charpoly ∣ (q : K[X]) := he _ hq
    have h2 : (q : K[X]).degree < g.charpoly.degree := by
      rw [degree_eq_natDegree g.charpoly_monic.ne_zero, LinearMap.charpoly_natDegree]
      exact mem_degreeLT.1 q.2
    exact Subtype.ext (eq_zero_of_dvd_of_degree_lt h1 h2)
  have hfin : Module.finrank K (degreeLT K (Module.finrank K V)) = Module.finrank K V := by
    rw [(degreeLTEquiv K (Module.finrank K V)).finrank_eq, Module.finrank_fin_fun]
  have : FiniteDimensional K (degreeLT K (Module.finrank K V)) :=
    (degreeLTEquiv K (Module.finrank K V)).symm.finiteDimensional
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).1 hinj
  intro v
  obtain ⟨q, hq⟩ := hsurj v
  exact ⟨q, hq⟩

/- English proof (translation)
Take `⟨e, he⟩` from `exists_cyclic g hs`. Take `⟨p, hp⟩` from `he (c e)`. Use `⟨p, LinearMap.ext fun v => ?_⟩` and prove the remaining obligations. Take `⟨q, rfl⟩` from `he v`. Establish `hcq : Commute (aeval g q) c` using `(Algebra.commute_of_mem_adjoin_singleton_of_commute (aeval_mem_adjoin_singleton K g) hc).symm`.

Rewrite using `[← Module.End.mul_apply, ← hcq.eq, Module.End.mul_apply, ← hp, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]`.
-/
theorem exists_eq_aeval_of_commute {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g c : Module.End K V) (hs : g.charpoly.Separable)
    (hc : c * g = g * c) : ∃ p : K[X], c = aeval g p := by
  obtain ⟨e, he⟩ := exists_cyclic g hs
  obtain ⟨p, hp⟩ := he (c e)
  refine ⟨p, LinearMap.ext fun v => ?_⟩
  obtain ⟨q, rfl⟩ := he v
  have hcq : Commute (aeval g q) c :=
    (Algebra.commute_of_mem_adjoin_singleton_of_commute (aeval_mem_adjoin_singleton K g) hc).symm
  rw [← Module.End.mul_apply, ← hcq.eq, Module.End.mul_apply, ← hp, ← Module.End.mul_apply,
    ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]

/- English proof (translation)
Introduce `k _ n Γ C u r h hC`. Set `e` to `(Matrix.toLinAlgEquiv' (R := k) (n := Fin n))`. Establish `hs : (e Γ).charpoly.Separable`. Rewrite using `[show e Γ = Matrix.toLin' Γ from rfl, Matrix.charpoly_toLin']`. Conclude with `⟨u, r, h⟩`.

Establish `hc : e C * e Γ = e Γ * e C`. Rewrite using `[← map_mul, ← map_mul, hC]`. Take `⟨p, hp⟩` from `exists_eq_aeval_of_commute _ _ hs hc`. Use `⟨p, e.injective ?_⟩` and prove the remaining obligations. Rewrite using `[hp]`.

Conclude with `aeval_algHom_apply e.toAlgHom Γ p`.
-/
theorem eq_aeval_of_commute_of_separable : ∀ (k : Type) [Field k] (n : ℕ)
    (Γ C : Matrix (Fin n) (Fin n) k) (u r : k[X]),
    u * Γ.charpoly + r * derivative Γ.charpoly = 1 → C * Γ = Γ * C →
    ∃ g : k[X], C = aeval Γ g := by
  intro k _ n Γ C u r h hC
  let e := (Matrix.toLinAlgEquiv' (R := k) (n := Fin n))
  have hs : (e Γ).charpoly.Separable := by
    rw [show e Γ = Matrix.toLin' Γ from rfl, Matrix.charpoly_toLin']
    exact ⟨u, r, h⟩
  have hc : e C * e Γ = e Γ * e C := by
    rw [← map_mul, ← map_mul, hC]
  obtain ⟨p, hp⟩ := exists_eq_aeval_of_commute _ _ hs hc
  refine ⟨p, e.injective ?_⟩
  rw [hp]
  exact aeval_algHom_apply e.toAlgHom Γ p

end GlobalTheory.SepCentralizer
