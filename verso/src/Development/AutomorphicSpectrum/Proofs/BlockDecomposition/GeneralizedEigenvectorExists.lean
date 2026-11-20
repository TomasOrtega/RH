import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.GenericPrincipalSeries.GenericPrincipalSeries
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant

noncomputable section

namespace GlobalTheory.CompanionTheory.TorusQuot

open Module Polynomial

/- English proof (translation)
Set `S : Set (Submodule ℂ V)` to `{K | K ≠ ⊤ ∧ ∀ i, ∀ x ∈ K, A i x ∈ K}`. Establish `hS : S.Nonempty` using `⟨⊥, bot_ne_top, fun i x hx => by`. Rewrite `hx`, the goal using `[Submodule.mem_bot]`. Rewrite using `[hx, map_zero]⟩`. Take `⟨K, ⟨hK, hKs⟩, hmax⟩` from `(wellFounded_gt (α := Submodule ℂ V)).has_min S hS`.

Establish `hrange : ∀ i, LinearMap.range (A i) ≤ K`. Introduce `i`. Establish `hstable : ∀ j, ∀ x ∈ K ⊔ LinearMap.range (A i), A j x ∈ K ⊔ LinearMap.range (A i)`. Introduce `j x hx`. Take `⟨k, hk, y, ⟨z, rfl⟩, rfl⟩` from `Submodule.mem_sup.1 hx`.

Rewrite using `[map_add]`. Use `Submodule.add_mem _ (Submodule.mem_sup_left (hKs j k hk)) (Submodule.mem_sup_right ⟨A j z, ?_⟩)` and prove the remaining obligations. Use `LinearMap.congr_fun (hc i j) z` as an intermediate fact. Simplify `this` using `[Module.End.mul_apply]`. Distinguish the cases in `htop : K ⊔ LinearMap.range (A i) = ⊤`.

It suffices to derive a contradiction. Establish `hpow : ∀ n : ℕ, ∀ x ∈ K, (A i ^ n) x ∈ K`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro x hx`.

Simplify using `using hx`. Consider the case `succ n ih`. Introduce `x hx`. Rewrite using `[pow_succ, Module.End.mul_apply]`. Conclude with `ih _ (hKs i x hx)`.

Establish `hall : ∀ n : ℕ, K ⊔ LinearMap.range (A i ^ n) = ⊤`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[pow_zero, eq_top_iff]`.

Introduce `x _`. Conclude with `Submodule.mem_sup_right ⟨x, rfl⟩`. Consider the case `succ n ih`. Rewrite using `[eq_top_iff]`. Introduce `x _`.

Establish `hx : x ∈ K ⊔ LinearMap.range (A i ^ n)` using `by rw [ih]; trivial`. Take `⟨k, hk, y, ⟨z, rfl⟩, rfl⟩` from `Submodule.mem_sup.1 hx`. Establish `hz : z ∈ K ⊔ LinearMap.range (A i)` using `by rw [htop]; trivial`. Take `⟨k', hk', y', ⟨a, rfl⟩, rfl⟩` from `Submodule.mem_sup.1 hz`. Rewrite using `[map_add, ← add_assoc]`.

Use `Submodule.add_mem _ (Submodule.mem_sup_left (K.add_mem hk (hpow n _ hk'))) (Submodule.mem_sup_right ⟨a, ?_⟩)` and prove the remaining obligations. Rewrite using `[pow_succ, Module.End.mul_apply]`. Establish `hnil : IsNilpotent (A i)` using `Module.End.isNilpotent_iff_of_finite.2 (hn i)`. Take `⟨n, hn0⟩` from `hnil`. Use `hall n` as an intermediate fact.

Rewrite `this` using `[hn0, LinearMap.range_zero, sup_bot_eq]`. Conclude with `hK this`. Establish `hle : K ≤ K ⊔ LinearMap.range (A i)` using `le_sup_left`. Establish `hnot` using `hmax _ ⟨htop, hstable⟩`. Establish `heq : K = K ⊔ LinearMap.range (A i)`.

Assume the negation of the conclusion as `hne`. Conclude with `hnot (lt_of_le_of_ne hle hne)`. Rewrite using `[heq]`. Conclude with `le_sup_right`. Take `⟨φ, hφ0, hφ⟩` from `Submodule.exists_le_ker_of_lt_top K (lt_top_iff_ne_top.2 hK)`.

Conclude with `⟨φ, hφ0, fun i x => hφ (hrange i ⟨x, rfl⟩)⟩`.
-/
theorem exists_functional_of_commuting_nilpotent {ι V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] (A : ι → End ℂ V)
    (hc : ∀ i j, A i * A j = A j * A i) (hn : ∀ i x, ∃ k : ℕ, (A i ^ k) x = 0) :
    ∃ φ : V →ₗ[ℂ] ℂ, φ ≠ 0 ∧ ∀ i x, φ (A i x) = 0 := by
  let S : Set (Submodule ℂ V) := {K | K ≠ ⊤ ∧ ∀ i, ∀ x ∈ K, A i x ∈ K}
  have hS : S.Nonempty := ⟨⊥, bot_ne_top, fun i x hx => by
    rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]⟩
  obtain ⟨K, ⟨hK, hKs⟩, hmax⟩ :=
    (wellFounded_gt (α := Submodule ℂ V)).has_min S hS
  have hrange : ∀ i, LinearMap.range (A i) ≤ K := by
    intro i
    have hstable : ∀ j, ∀ x ∈ K ⊔ LinearMap.range (A i), A j x ∈ K ⊔ LinearMap.range (A i) := by
      intro j x hx
      obtain ⟨k, hk, y, ⟨z, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
      rw [map_add]
      refine Submodule.add_mem _ (Submodule.mem_sup_left (hKs j k hk))
        (Submodule.mem_sup_right ⟨A j z, ?_⟩)
      have := LinearMap.congr_fun (hc i j) z
      simpa [Module.End.mul_apply] using this
    by_cases htop : K ⊔ LinearMap.range (A i) = ⊤
    · exfalso
      have hpow : ∀ n : ℕ, ∀ x ∈ K, (A i ^ n) x ∈ K := by
        intro n
        induction n with
        | zero => intro x hx; simpa using hx
        | succ n ih =>
          intro x hx
          rw [pow_succ, Module.End.mul_apply]
          exact ih _ (hKs i x hx)
      have hall : ∀ n : ℕ, K ⊔ LinearMap.range (A i ^ n) = ⊤ := by
        intro n
        induction n with
        | zero =>
          rw [pow_zero, eq_top_iff]
          intro x _
          exact Submodule.mem_sup_right ⟨x, rfl⟩
        | succ n ih =>
          rw [eq_top_iff]
          intro x _
          have hx : x ∈ K ⊔ LinearMap.range (A i ^ n) := by rw [ih]; trivial
          obtain ⟨k, hk, y, ⟨z, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
          have hz : z ∈ K ⊔ LinearMap.range (A i) := by rw [htop]; trivial
          obtain ⟨k', hk', y', ⟨a, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hz
          rw [map_add, ← add_assoc]
          refine Submodule.add_mem _
            (Submodule.mem_sup_left (K.add_mem hk (hpow n _ hk')))
            (Submodule.mem_sup_right ⟨a, ?_⟩)
          rw [pow_succ, Module.End.mul_apply]
      have hnil : IsNilpotent (A i) := Module.End.isNilpotent_iff_of_finite.2 (hn i)
      obtain ⟨n, hn0⟩ := hnil
      have := hall n
      rw [hn0, LinearMap.range_zero, sup_bot_eq] at this
      exact hK this
    · have hle : K ≤ K ⊔ LinearMap.range (A i) := le_sup_left
      have hnot := hmax _ ⟨htop, hstable⟩
      have heq : K = K ⊔ LinearMap.range (A i) := by
        by_contra hne
        exact hnot (lt_of_le_of_ne hle hne)
      rw [heq]
      exact le_sup_right
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top K (lt_top_iff_ne_top.2 hK)
  exact ⟨φ, hφ0, fun i x => hφ (hrange i ⟨x, rfl⟩)⟩

/- English proof (translation)
Set `g : ℂ[X]` to `∑ i ∈ Finset.range K, X ^ i`. Establish `hg : (X - 1 : ℂ[X]) * g = X ^ K - 1`. Rewrite using `[mul_comm]`. Conclude with `geom_sum_mul X K`. Establish `hirr : Irreducible (X - 1 : ℂ[X])`.

Simplify using `using irreducible_X_sub_C (1 : ℂ)`. Establish `hnd : ¬ (X - 1 : ℂ[X]) ∣ g`. Introduce `hd`. Establish `hroot : IsRoot g 1`. Establish `: (X - C 1 : ℂ[X]) ∣ g` using `by simpa using hd`.

Conclude with `dvd_iff_isRoot.1 this`. Establish `hev : g.eval 1 = (K : ℂ)` using `by simp [g, eval_finset_sum]`. Rewrite `hroot` using `[IsRoot.def, hev]`. Conclude with `(Nat.cast_ne_zero.2 hK.ne') hroot`. Take `⟨a, b, hab⟩` from `((hirr.coprime_iff_not_dvd).2 hnd).pow_left (m := r)`.

Establish `hpoly : a * (X - 1) * (X - 1) ^ r + b * (X ^ K - 1) = (X - 1 : ℂ[X])`. Rewrite using `[← hg]`. Take the linear combination `(X - 1 : ℂ[X]) * hab`. Establish `hkey` using `congrArg (aeval T) hpoly`. Simplify using `only [map_add, map_mul, map_pow, map_sub, aeval_X, map_one] at hkey`.

Establish `happ` using `LinearMap.congr_fun hkey w`. Simplify using `only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, h1, h2, map_zero, sub_self, zero_add] at happ`. Use `sub_eq_zero.1 happ.symm` as an intermediate fact. Conclude with `this`.
-/
theorem fixed_of_pow_fixed_of_gen {V : Type} [AddCommGroup V] [Module ℂ V] (T : End ℂ V) (w : V)
    (K r : ℕ) (hK : 0 < K) (h1 : (T ^ K) w = w) (h2 : ((T - 1) ^ r) w = 0) : T w = w := by
  let g : ℂ[X] := ∑ i ∈ Finset.range K, X ^ i
  have hg : (X - 1 : ℂ[X]) * g = X ^ K - 1 := by
    rw [mul_comm]
    exact geom_sum_mul X K
  have hirr : Irreducible (X - 1 : ℂ[X]) := by
    simpa using irreducible_X_sub_C (1 : ℂ)
  have hnd : ¬ (X - 1 : ℂ[X]) ∣ g := by
    intro hd
    have hroot : IsRoot g 1 := by
      have : (X - C 1 : ℂ[X]) ∣ g := by simpa using hd
      exact dvd_iff_isRoot.1 this
    have hev : g.eval 1 = (K : ℂ) := by simp [g, eval_finset_sum]
    rw [IsRoot.def, hev] at hroot
    exact (Nat.cast_ne_zero.2 hK.ne') hroot
  obtain ⟨a, b, hab⟩ := ((hirr.coprime_iff_not_dvd).2 hnd).pow_left (m := r)
  have hpoly : a * (X - 1) * (X - 1) ^ r + b * (X ^ K - 1) = (X - 1 : ℂ[X]) := by
    rw [← hg]
    linear_combination (X - 1 : ℂ[X]) * hab
  have hkey := congrArg (aeval T) hpoly
  simp only [map_add, map_mul, map_pow, map_sub, aeval_X, map_one] at hkey
  have happ := LinearMap.congr_fun hkey w
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply,
    Module.End.one_apply, h1, h2, map_zero, sub_self, zero_add] at happ
  have := sub_eq_zero.1 happ.symm
  exact this

/- English proof (translation)
Proceed by induction on `k generalizing y with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]`. Use `congr 1`.
-/
theorem coe_restrict_sub_pow {V : Type} [AddCommGroup V] [Module ℂ V] (p : Submodule ℂ V)
    (f : End ℂ V) (hf : ∀ x ∈ p, f x ∈ p) (μ : ℂ) (k : ℕ) (y : p) :
    (((f.restrict hf - μ • (1 : End ℂ p)) ^ k) y : V) = ((f - μ • (1 : End ℂ V)) ^ k) (y : V) := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
    congr 1

/- English proof (translation)
Set `T : Λ → End ℂ E` to `fun l => (ρ l : End ℂ M).restrict (hE l)`. Establish `hT : ∀ i j, Commute (T i) (T j)`. Introduce `i j`. Use extensionality with `x`. Use `LinearMap.congr_fun (hc i j) (x : M)` as an intermediate fact.

Simplify `this` using `[T, Module.End.mul_apply]`. Establish `hmaps : ∀ i j φ, Set.MapsTo (T i) (End.maxGenEigenspace (T j) φ) (End.maxGenEigenspace (T j) φ)` using `fun i j φ => End.mapsTo_maxGenEigenspace_of_comm (hT j i) φ`. Establish `htop` using `End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo T hmaps (fun i => End.iSup_maxGenEigenspace_eq_top (T i))`. Establish `hle : (⊤ : Submodule ℂ E).map E.subtype ≤ ⨆ χ : Λ → ℂ, ⨅ l, End.maxGenEigenspace (ρ l : End ℂ M) (χ l)`. Rewrite using `[← htop, Submodule.map_iSup]`.

Use `iSup_mono fun χ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.map_le_iff_le_comap]`. Introduce `y hy`. Rewrite using `[Submodule.mem_comap, Submodule.mem_iInf]`. Introduce `l`.

Establish `hl` using `(Submodule.mem_iInf _).1 hy l`. Take `⟨k, hk⟩` from `(End.mem_maxGenEigenspace _ _ _).1 hl`. Use `(End.mem_maxGenEigenspace _ _ _).2 ⟨k, ?_⟩` and prove the remaining obligations. Use `coe_restrict_sub_pow E (ρ l) (hE l) (χ l) k y` as an intermediate fact. Rewrite `this` using `[hk]`.

Conclude with `this.symm`. Conclude with `hle ⟨⟨w, hw⟩, trivial, rfl⟩`.
-/
theorem mem_iSup_iInf_of_finite {Λ M : Type} [Group Λ] [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ Λ M) (hc : ∀ l l', ρ l * ρ l' = ρ l' * ρ l)
    (E : Submodule ℂ M) [FiniteDimensional ℂ E] (hE : ∀ l, ∀ x ∈ E, ρ l x ∈ E) (w : M)
    (hw : w ∈ E) :
    w ∈ ⨆ χ : Λ → ℂ, ⨅ l, End.maxGenEigenspace (ρ l : End ℂ M) (χ l) := by
  let T : Λ → End ℂ E := fun l => (ρ l : End ℂ M).restrict (hE l)
  have hT : ∀ i j, Commute (T i) (T j) := by
    intro i j
    ext x
    have := LinearMap.congr_fun (hc i j) (x : M)
    simpa [T, Module.End.mul_apply] using this
  have hmaps : ∀ i j φ, Set.MapsTo (T i) (End.maxGenEigenspace (T j) φ)
      (End.maxGenEigenspace (T j) φ) :=
    fun i j φ => End.mapsTo_maxGenEigenspace_of_comm (hT j i) φ
  have htop := End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo T hmaps
    (fun i => End.iSup_maxGenEigenspace_eq_top (T i))
  have hle : (⊤ : Submodule ℂ E).map E.subtype ≤
      ⨆ χ : Λ → ℂ, ⨅ l, End.maxGenEigenspace (ρ l : End ℂ M) (χ l) := by
    rw [← htop, Submodule.map_iSup]
    refine iSup_mono fun χ => ?_
    rw [Submodule.map_le_iff_le_comap]
    intro y hy
    rw [Submodule.mem_comap, Submodule.mem_iInf]
    intro l
    have hl := (Submodule.mem_iInf _).1 hy l
    obtain ⟨k, hk⟩ := (End.mem_maxGenEigenspace _ _ _).1 hl
    refine (End.mem_maxGenEigenspace _ _ _).2 ⟨k, ?_⟩
    have := coe_restrict_sub_pow E (ρ l) (hE l) (χ l) k y
    rw [hk] at this
    exact this.symm
  exact hle ⟨⟨w, hw⟩, trivial, rfl⟩

/- English proof (translation)
Introduce `Λ _ M _ _ ρ hc U hU hpow hex hfd ξ v hv0 hv`. Establish `hmem : ∀ (m : ℕ) (w : M), w ∈ (⨅ u : U m, LinearMap.ker (ρ (u : Λ) - 1)) ↔ ∀ u ∈ U m, ρ u w = w`. Introduce `m w`. Rewrite using `[Submodule.mem_iInf]`. Prove the components needed by the constructor for the conclusion.

Introduce `h u hu`. Use `h ⟨u, hu⟩` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]`. Conclude with `this`. Introduce `h u`.

Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]`. Conclude with `h u u.2`. Establish `hcomm : ∀ l l' (x : M), ρ l (ρ l' x) = ρ l' (ρ l x)` using `fun l l' x => by`. Use `LinearMap.congr_fun (hc l l') x` as an intermediate fact. Simplify `this` using `[Module.End.mul_apply]`.

Set `t : (Λ → ℂ) → Submodule ℂ M` to `fun χ => ⨅ l, End.maxGenEigenspace (ρ l : End ℂ M) (χ l)`. Establish `htS : ∀ χ l, ∀ x ∈ t χ, ρ l x ∈ t χ`. Introduce `χ l x hx`. Use `(Submodule.mem_iInf _).2 fun j => ?_` and prove the remaining obligations. Establish `hcj : Commute (ρ j : End ℂ M) (ρ l)` using `hc j l`.

Conclude with `End.mapsTo_maxGenEigenspace_of_comm hcj (χ j) ((Submodule.mem_iInf _).1 hx j)`. Set `ξ' : Λ → ℂ` to `ξ`. Set `N : Submodule ℂ M` to `t ξ'`. Set `C : Submodule ℂ M` to `⨆ χ, ⨆ (_ : χ ≠ ξ'), t χ`. Establish `hind : iSupIndep t` using `End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun l => (ρ l : End ℂ M)) (fun i j φ => End.mapsTo_maxGenEigenspace_of_comm (show Commute (ρ j : End ℂ M) (ρ i) from hc j i) φ)`.

Establish `hsup : N ⊔ C = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `w _`. Take `⟨m, hm⟩` from `hex w`. Use `haveI := hfd m`.

Establish `hst : ∀ l, ∀ x ∈ (⨅ u : U m, LinearMap.ker (ρ (u : Λ) - 1)), ρ l x ∈ (⨅ u : U m, LinearMap.ker (ρ (u : Λ) - 1))`. Introduce `l x hx`. Use `(hmem m _).2 fun u hu => ?_` and prove the remaining obligations. Rewrite using `[hcomm, (hmem m x).1 hx u hu]`. Establish `hw` using `mem_iSup_iInf_of_finite ρ hc _ hst w ((hmem m w).2 hm)`.

Establish `hle : (⨆ χ : Λ → ℂ, t χ) ≤ N ⊔ C`. Use `iSup_le fun χ => ?_` and prove the remaining obligations. Distinguish the cases in `h : χ = ξ'`. Rewrite using `[h]`. Conclude with `le_sup_left`.

Conclude with `le_trans (le_iSup₂ (f := fun χ (_ : χ ≠ ξ') => t χ) χ h) le_sup_right`. Conclude with `hle hw`. Establish `hIC : IsCompl N C` using `⟨hind ξ', codisjoint_iff.2 hsup⟩`. Establish `hCS : ∀ l, ∀ x ∈ C, ρ l x ∈ C`. Introduce `l`.

Establish `: C ≤ C.comap (ρ l : End ℂ M)`. Use `iSup₂_le fun χ h x hx => ?_` and prove the remaining obligations. Conclude with `(le_iSup₂ (f := fun χ (_ : χ ≠ ξ') => t χ) χ h) (htS χ l x hx)`. Conclude with `fun x hx => this hx`. Establish `hvN : v ∈ N` using `(Submodule.mem_iInf _).2 hv`.

Take `⟨m0, hm0⟩` from `hex v`. Establish `hξ1 : ∀ u ∈ U m0, ξ u = 1`. Introduce `u hu`. Take `⟨r, hr⟩` from `(End.mem_maxGenEigenspace _ _ _).1 (hv u)`. Assume the negation of the conclusion as `hne`.

Establish `hact : ∀ k : ℕ, (((ρ u : End ℂ M) - ξ u • (1 : End ℂ M)) ^ k) v = (1 - ξ u) ^ k • v`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`.

Establish `hstep : ((ρ u : End ℂ M) - ξ u • (1 : End ℂ M)) v = (1 - ξ u) • v`. Rewrite using `[LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hm0 u hu, sub_smul, one_smul]`. Rewrite using `[pow_succ, Module.End.mul_apply, hstep, map_smul, ih, smul_smul, pow_succ, mul_comm]`. Rewrite `hr` using `[hact r]`. Break down `smul_eq_zero.1 hr with h | h` into its components or cases.

Conclude with `pow_ne_zero r (sub_ne_zero.2 (Ne.symm hne)) h`. Conclude with `hv0 h`. Establish `hNfix : ∀ w ∈ N, ∀ u ∈ U m0, ρ u w = w`. Introduce `w hw u hu`. Take `⟨m1, hm1⟩` from `hex w`.

Take `⟨K, hK, huK⟩` from `hpow m0 (max m0 m1) (le_max_left _ _) u hu`. Take `⟨r, hr⟩` from `(End.mem_maxGenEigenspace _ _ _).1 ((Submodule.mem_iInf _).1 hw u)`. Use `fixed_of_pow_fixed_of_gen (ρ u) w K r hK ?_ ?_` and prove the remaining obligations. Rewrite using `[← map_pow]`. Conclude with `hm1 _ (hU (le_max_right m0 m1) huK)`.

Establish `h1 : ξ' u = 1` using `hξ1 u hu`. Rewrite `hr` using `[h1, one_smul]`. Conclude with `hr`. Use `haveI : FiniteDimensional ℂ N := by haveI := hfd m0`. Conclude with `Submodule.finiteDimensional_of_le (S₂ := ⨅ u : U m0, LinearMap.ker (ρ (u : Λ) - 1)) fun w hw => (hmem m0 w).2 (hNfix w hw)`.

Use `haveI : Nontrivial N := ⟨⟨⟨v, hvN⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩`. Establish `hNS : ∀ l, ∀ x ∈ N, ρ l x ∈ N` using `htS ξ'`. Set `T : Λ → End ℂ N` to `fun l => (ρ l : End ℂ M).restrict (hNS l)`. Set `A : Λ → End ℂ N` to `fun l => T l - ξ l • (1 : End ℂ N)`. Establish `hT : ∀ i j, Commute (T i) (T j)`.

Introduce `i j`. Use extensionality with `x`. Simplify `hcomm i j (x : M)` using `[T, Module.End.mul_apply]`. Establish `hs : ∀ (a : ℂ) (B : End ℂ N), Commute (a • (1 : End ℂ N)) B` using `fun a B => (Commute.one_left B).smul_left a`. Establish `hAc : ∀ i j, A i * A j = A j * A i` using `fun i j => Commute.sub_left (Commute.sub_right (hT i j) (hs _ _).symm) (hs _ _)`.

Establish `hAn : ∀ i x, ∃ k : ℕ, (A i ^ k) x = 0`. Introduce `i x`. Take `⟨k, hk⟩` from `(End.mem_maxGenEigenspace _ _ _).1 ((Submodule.mem_iInf _).1 x.2 i)`. Use `⟨k, Subtype.ext ?_⟩` and prove the remaining obligations. Use `coe_restrict_sub_pow N (ρ i) (hNS i) (ξ i) k x` as an intermediate fact.

Rewrite `hk` using `[show (ξ' i) = ξ i from rfl]`. Rewrite `this` using `[hk]`. Conclude with `this`. Take `⟨φ, hφ0, hφ⟩` from `exists_functional_of_commuting_nilpotent A hAc hAn`. Set `P : M →ₗ[ℂ] N` to `Submodule.linearProjOfIsCompl N C hIC`.

Establish `hPN : ∀ x : N, P x = x` using `fun x => Submodule.linearProjOfIsCompl_apply_left hIC x`. Establish `hPC : ∀ x ∈ C, P x = 0` using `fun x hx => (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hIC).2 hx`. Use `⟨φ ∘ₗ P, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Apply `hφ0` to reduce the goal to its premises.

Use extensionality with `x`. Use `LinearMap.congr_fun h (x : M)` as an intermediate fact. Simplify `this` using `[hPN]`. Introduce `l w`. Establish `hw : w ∈ N ⊔ C` using `by rw [hsup]; trivial`.

Take `⟨n, hn, c, hc', rfl⟩` from `Submodule.mem_sup.1 hw`. Establish `hφT : φ (T l ⟨n, hn⟩) = ξ l * φ ⟨n, hn⟩`. Establish `h0` using `hφ l ⟨n, hn⟩`. Establish `hx : A l ⟨n, hn⟩ = T l ⟨n, hn⟩ - ξ l • (⟨n, hn⟩ : N)` using `rfl`. Rewrite `h0` using `[hx, map_sub, map_smul, smul_eq_mul, sub_eq_zero]`.

Conclude with `h0`. Establish `h1 : P (ρ l n) = T l ⟨n, hn⟩` using `hPN ⟨ρ l n, hNS l n hn⟩`. Establish `h2 : P n = ⟨n, hn⟩` using `hPN ⟨n, hn⟩`. Simplify using `only [LinearMap.comp_apply, map_add, hPC c hc', hPC _ (hCS l c hc'), h1, h2, add_zero, map_zero, hφT]`.
-/
theorem exists_quotient_character : ∀ (Λ : Type) [Group Λ] (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ Λ M), (∀ l l', ρ l * ρ l' = ρ l' * ρ l) → ∀ (U : ℕ → Subgroup Λ), Antitone U → (∀ m m', m ≤ m' → ∀ u ∈ U m, ∃ N : ℕ, 0 < N ∧ u ^ N ∈ U m') → (∀ w : M, ∃ m, ∀ u ∈ U m, ρ u w = w) → (∀ m, FiniteDimensional ℂ ↥(⨅ u : U m, LinearMap.ker (ρ (u : Λ) - 1))) → ∀ (ξ : Λ →* ℂ) (v : M), v ≠ 0 → (∀ l, v ∈ Module.End.maxGenEigenspace (ρ l) (ξ l)) → ∃ f : M →ₗ[ℂ] ℂ, f ≠ 0 ∧ ∀ l w, f (ρ l w) = ξ l * f w := by
  classical
  intro Λ _ M _ _ ρ hc U hU hpow hex hfd ξ v hv0 hv
  have hmem : ∀ (m : ℕ) (w : M), w ∈ (⨅ u : U m, LinearMap.ker (ρ (u : Λ) - 1)) ↔
      ∀ u ∈ U m, ρ u w = w := by
    intro m w
    rw [Submodule.mem_iInf]
    constructor
    · intro h u hu
      have := h ⟨u, hu⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
      exact this
    · intro h u
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      exact h u u.2
  have hcomm : ∀ l l' (x : M), ρ l (ρ l' x) = ρ l' (ρ l x) := fun l l' x => by
    have := LinearMap.congr_fun (hc l l') x
    simpa [Module.End.mul_apply] using this
  let t : (Λ → ℂ) → Submodule ℂ M := fun χ => ⨅ l, End.maxGenEigenspace (ρ l : End ℂ M) (χ l)
  have htS : ∀ χ l, ∀ x ∈ t χ, ρ l x ∈ t χ := by
    intro χ l x hx
    refine (Submodule.mem_iInf _).2 fun j => ?_
    have hcj : Commute (ρ j : End ℂ M) (ρ l) := hc j l
    exact End.mapsTo_maxGenEigenspace_of_comm hcj (χ j) ((Submodule.mem_iInf _).1 hx j)
  let ξ' : Λ → ℂ := ξ
  let N : Submodule ℂ M := t ξ'
  let C : Submodule ℂ M := ⨆ χ, ⨆ (_ : χ ≠ ξ'), t χ
  have hind : iSupIndep t := End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (fun l => (ρ l : End ℂ M))
    (fun i j φ => End.mapsTo_maxGenEigenspace_of_comm (show Commute (ρ j : End ℂ M) (ρ i) from hc j i) φ)
  have hsup : N ⊔ C = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨m, hm⟩ := hex w
    haveI := hfd m
    have hst : ∀ l, ∀ x ∈ (⨅ u : U m, LinearMap.ker (ρ (u : Λ) - 1)), ρ l x ∈
        (⨅ u : U m, LinearMap.ker (ρ (u : Λ) - 1)) := by
      intro l x hx
      refine (hmem m _).2 fun u hu => ?_
      rw [hcomm, (hmem m x).1 hx u hu]
    have hw := mem_iSup_iInf_of_finite ρ hc _ hst w ((hmem m w).2 hm)
    have hle : (⨆ χ : Λ → ℂ, t χ) ≤ N ⊔ C := by
      refine iSup_le fun χ => ?_
      by_cases h : χ = ξ'
      · rw [h]; exact le_sup_left
      · exact le_trans (le_iSup₂ (f := fun χ (_ : χ ≠ ξ') => t χ) χ h) le_sup_right
    exact hle hw
  have hIC : IsCompl N C := ⟨hind ξ', codisjoint_iff.2 hsup⟩
  have hCS : ∀ l, ∀ x ∈ C, ρ l x ∈ C := by
    intro l
    have : C ≤ C.comap (ρ l : End ℂ M) := by
      refine iSup₂_le fun χ h x hx => ?_
      exact (le_iSup₂ (f := fun χ (_ : χ ≠ ξ') => t χ) χ h) (htS χ l x hx)
    exact fun x hx => this hx
  have hvN : v ∈ N := (Submodule.mem_iInf _).2 hv
  obtain ⟨m0, hm0⟩ := hex v
  have hξ1 : ∀ u ∈ U m0, ξ u = 1 := by
    intro u hu
    obtain ⟨r, hr⟩ := (End.mem_maxGenEigenspace _ _ _).1 (hv u)
    by_contra hne
    have hact : ∀ k : ℕ, (((ρ u : End ℂ M) - ξ u • (1 : End ℂ M)) ^ k) v = (1 - ξ u) ^ k • v := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hstep : ((ρ u : End ℂ M) - ξ u • (1 : End ℂ M)) v = (1 - ξ u) • v := by
          rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hm0 u hu, sub_smul,
            one_smul]
        rw [pow_succ, Module.End.mul_apply, hstep, map_smul, ih, smul_smul, pow_succ, mul_comm]
    rw [hact r] at hr
    rcases smul_eq_zero.1 hr with h | h
    · exact pow_ne_zero r (sub_ne_zero.2 (Ne.symm hne)) h
    · exact hv0 h
  have hNfix : ∀ w ∈ N, ∀ u ∈ U m0, ρ u w = w := by
    intro w hw u hu
    obtain ⟨m1, hm1⟩ := hex w
    obtain ⟨K, hK, huK⟩ := hpow m0 (max m0 m1) (le_max_left _ _) u hu
    obtain ⟨r, hr⟩ := (End.mem_maxGenEigenspace _ _ _).1 ((Submodule.mem_iInf _).1 hw u)
    refine fixed_of_pow_fixed_of_gen (ρ u) w K r hK ?_ ?_
    · rw [← map_pow]
      exact hm1 _ (hU (le_max_right m0 m1) huK)
    · have h1 : ξ' u = 1 := hξ1 u hu
      rw [h1, one_smul] at hr
      exact hr
  haveI : FiniteDimensional ℂ N := by
    haveI := hfd m0
    exact Submodule.finiteDimensional_of_le (S₂ := ⨅ u : U m0, LinearMap.ker (ρ (u : Λ) - 1))
      fun w hw => (hmem m0 w).2 (hNfix w hw)
  haveI : Nontrivial N := ⟨⟨⟨v, hvN⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩
  have hNS : ∀ l, ∀ x ∈ N, ρ l x ∈ N := htS ξ'
  let T : Λ → End ℂ N := fun l => (ρ l : End ℂ M).restrict (hNS l)
  let A : Λ → End ℂ N := fun l => T l - ξ l • (1 : End ℂ N)
  have hT : ∀ i j, Commute (T i) (T j) := by
    intro i j
    ext x
    simpa [T, Module.End.mul_apply] using hcomm i j (x : M)
  have hs : ∀ (a : ℂ) (B : End ℂ N), Commute (a • (1 : End ℂ N)) B :=
    fun a B => (Commute.one_left B).smul_left a
  have hAc : ∀ i j, A i * A j = A j * A i := fun i j =>
    Commute.sub_left (Commute.sub_right (hT i j) (hs _ _).symm) (hs _ _)
  have hAn : ∀ i x, ∃ k : ℕ, (A i ^ k) x = 0 := by
    intro i x
    obtain ⟨k, hk⟩ := (End.mem_maxGenEigenspace _ _ _).1 ((Submodule.mem_iInf _).1 x.2 i)
    refine ⟨k, Subtype.ext ?_⟩
    have := coe_restrict_sub_pow N (ρ i) (hNS i) (ξ i) k x
    rw [show (ξ' i) = ξ i from rfl] at hk
    rw [hk] at this
    exact this
  obtain ⟨φ, hφ0, hφ⟩ := exists_functional_of_commuting_nilpotent A hAc hAn
  let P : M →ₗ[ℂ] N := Submodule.linearProjOfIsCompl N C hIC
  have hPN : ∀ x : N, P x = x := fun x => Submodule.linearProjOfIsCompl_apply_left hIC x
  have hPC : ∀ x ∈ C, P x = 0 := fun x hx =>
    (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hIC).2 hx
  refine ⟨φ ∘ₗ P, ?_, ?_⟩
  · intro h
    apply hφ0
    ext x
    have := LinearMap.congr_fun h (x : M)
    simpa [hPN] using this
  · intro l w
    have hw : w ∈ N ⊔ C := by rw [hsup]; trivial
    obtain ⟨n, hn, c, hc', rfl⟩ := Submodule.mem_sup.1 hw
    have hφT : φ (T l ⟨n, hn⟩) = ξ l * φ ⟨n, hn⟩ := by
      have h0 := hφ l ⟨n, hn⟩
      have hx : A l ⟨n, hn⟩ = T l ⟨n, hn⟩ - ξ l • (⟨n, hn⟩ : N) := rfl
      rw [hx, map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h0
      exact h0
    have h1 : P (ρ l n) = T l ⟨n, hn⟩ := hPN ⟨ρ l n, hNS l n hn⟩
    have h2 : P n = ⟨n, hn⟩ := hPN ⟨n, hn⟩
    simp only [LinearMap.comp_apply, map_add, hPC c hc', hPC _ (hCS l c hc'), h1, h2, add_zero,
      map_zero, hφT]

end GlobalTheory.CompanionTheory.TorusQuot
